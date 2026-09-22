import LeanToLambdaBox.ErasesCorrect.Close
import LeanToLambdaBox.FirstOrderInd
import LeanToLambdaBox.SubjectReduction
import LeanToLambdaBox.VisitExprRefines
import LeanToLambdaBox.VisitExprRefines.Step.Env
import LeanToLambdaBox.VisitExprRefines.Step.Mechanical
import LeanToLambdaBox.VisitExprRefines.Step.Passes

/-!
# The capstone — the shipping erasure, at a first-order answer

`shipping_erase_correct_firstorder` is the applied form of the correctness statement: for a
source term the erasure ran on, the emitted program `(Γ, t)` is the lowered image of a
specification environment that erases the **prepared** term, it satisfies what peregrine's
first pass needs, and every first-order answer the source evaluation produces is reproduced —
uniquely and box-free — by the emitted program under λ□'s own semantics.

The syntactic conjuncts read the prepared term `pe` and the observable conjunct reads the
source subject `e`: `Erasure.visitExpr`'s input is post-`prepare_erasure`, and the two terms
cannot be identified, since `Lean.Compiler.LCNF.macroInline` replaces a constant by its body.
`prepare_sound` carries the source evaluation from `e` to `pe`, at the spine the observable is
read under. `hprep` fixes `pe`; at a rung it is the subject itself, checked by
`lake exe reify --prepared`.

The conclusion is `LBWfPeregrine`, and since F-ETA (the emitted body of a registered
fixpoint is the η-expansion `LBTerm.etaFix`, not the bare `tFix` node) `LBWfPeregrine`'s
`expandedFix` clause carries all three term-level conjuncts of MetaRocq's `expanded_tFix`
(§4.7 of `doc/rework/10-MERGE-FIXES.md`); `PeregrinePre`, the separate predicate the earlier
gap needed, is deleted.

Three hypotheses are stated in the form this module can express. `hsup` is the fragment
predicate `Supported`, which a rung discharges by computation through `supportedB_sound`.
The first-order side condition is `FirstOrderInd env I`, the closed predicate of
`FirstOrderInd.lean`. The spine premises are `ErasesLB` unfolded with the argument's
`ErasesEnv` conjunct, the length equation `Lower.mkApps` consumes, and the spine's translation.

`hnb : NoBodylessRefs Γ t` is `erase_correct_firstorder`'s `axiom_free` analogue, decided per
rung: without it a run reaching a body-less declaration would satisfy the conclusion
vacuously, its source evaluation having no derivation. `hwf : LBWfPeregrine Γ t` is decided
per rung the same way, by kernel computation on the emitted program.

The erasure half of the composition is `erasure_bridge_of_run`, a proved term; the simulation
half is `erases_correct`, applied once at the spine the observable is read under. What remains
is one named binder, `hbridge`, whose two fields wait on the specification environment the
run's final state admits. `bridgeEnv_of_regInv` derives both from a registration invariant
there, `doc/rework/08-REPAIRS-W5.md` §2 states what would produce that invariant and the three
obstructions in the way, and `doc/trust.md`'s rows are the accounting.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean Erasure Witness

/-! ## The erasure half, discharged -/

set_option linter.unusedVariables false in
/--
**The erasure half of the capstone's bundle, discharged.** The entry reader carries no fixvar
map and the entry state is empty, so `BridgeInv` holds there by construction, and T8 puts the
emitted term in the composite at every specification environment of the final state. All
eighteen member steps are supplied here, `step6` among them, so the composition takes no
further obligation. `hblk` is the standing block binder, consumed at the install site rather
than here.
-/
theorem erasure_bridge_of_run
    {lenv : Lean.Environment} {env : VEnv} {gw : Void IO.RealWorld → NameGenerator}
    {tbl : SourceTable} {cfg : ErasureConfig} {e pe : Expr} {ve : VExpr}
    {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
    {w wp wt : Void IO.RealWorld} {sp sf : ErasureState} {t : LBTerm}
    (P : ErasureSpec lenv env [] gw) (E : EraserAsks lenv env gw)
    (A : UpstreamAsks env)
    (htbl : SourceTableAdequate lenv tbl) (hsafe : TableSafe lenv tbl)
    (hblk : TableBlocks lenv env tbl)
    (hcfg : ConfigPinned cfg) (hcb : CompilerBodies lenv env tbl.body?)
    (hsup : Supported env tbl pe) (hwt : TrExprS env [] [] pe ve)
    (hprep : Erasure.prepare_erasure e {} { «config» := cfg } cctx ref w = .ok (pe, sp) wp)
    (hvis : Erasure.visitExpr pe sp { «config» := cfg } cctx ref wp = .ok (t, sf) wt)
    {Γspec : GlobalDeclarations} (hspec : SpecEnv env tbl.body? tbl.levels? sf Γspec) :
    ∃ t₀, Erases env [] [] pe t₀ ∧ Lower Γspec t₀ t := by
  obtain rfl : sp = ({} : ErasureState) := run_prepare_erasure_state hcfg.1 hprep
  have hinv : BridgeInv env [] tbl cfg (gw wp) { «config» := cfg } {} [] := by
    refine ⟨⟨.nil, trivial, rfl, rfl⟩, rfl, rfl, ?_, ?_, Or.inl rfl, ?_,
      indRegistryModelled_empty⟩
    · intro fv hfv; simp at hfv
    · intro fv hfv; simp at hfv
    · intro n k h; simp at h
  exact (visitExpr_refines_erasesLB
    (step_visitExpr E) step_visitLiteral (step_visitConstructor A) (step_visitConst A) step5
    (step6 E hsafe) step_visitAppArgs step_visitLet step_visitLambda step_visitProj
    step_visitApp (step_visitConstApp hsafe) step_visitCtorEta step_visitCtorEtaGo
    step_visitCasesEta step_visitCasesEtaGo (step_visitCases A E) step_visitAlt
    P htbl hcfg hcb hwt hsup rfl hvis hinv Γspec hspec).1

/-! ## The residual, as one named binder -/

/--
What the capstone assumes beyond the erasure half, as one named binder: the two environment
results the specification environment of the run's final state carries. Both are derived by
`bridgeEnv_of_regInv` from `RegInvShape'` and `RegSaturated` at that state, and no theorem
produces that invariant for a run of the shipping eraser — `doc/rework/08-REPAIRS-W5.md` §2 is
the statement that would, and §2.3 the three measured obstructions in the way.
-/
structure ErasureBridge (env : VEnv) (bo : Name → Option Expr) (lp : Name → List Name)
    (Γspec Γ : GlobalDeclarations) (t₀ : LBTerm) : Prop where
  /-- The specification environment erases the source environment. `RegInvShape'.erasesEnv`
      derives it from the registration invariant at the run's final state, at the two
      side conditions `bridgeEnv_of_regInv` names. -/
  erasesEnv : ErasesEnv env bo lp Γspec t₀
  /-- The emitted environment is the lowered, pruned specification environment.
      `RegInvShape'.lowerEnv` derives it from the same invariant at a saturated registry. -/
  lowerEnv : LowerEnv Γspec Γ

/-! ## The bridge's environment fields, from the registration invariant -/

/--
**The bridge's two environment fields, derived.** `RegInvShape'` — the invariant the
registration path maintains — carries the specification environment's content, the emitted
environment's shape and the relation between them; `RegSaturated` says the run registered
everything that environment declares. `hdeps` is decidable at a concrete program, and `htab`
is the one clause `ErasesEnv` reads off the compiler table rather than off any environment.
The `SpecEnv` is what `erasure_bridge_of_run` consumes; `LBWfSpec` is what the pass metatheory
reads of `Γspec`.
-/
theorem bridgeEnv_of_regInv {env : VEnv} {bo : Name → Option Expr} {lp : Name → List Name}
    {Γspec : GlobalDeclarations} {sf : ErasureState} {t₀ : LBTerm}
    (hreg : RegInvShape' env bo lp Γspec sf) (hsat : RegSaturated env Γspec sf)
    (hdeps : ∀ kn, ReachableFrom Γspec t₀ kn → (LBTerm.envLookup Γspec kn).isSome)
    (htab : ∀ c b, bo c = some b → ConstOrigin env c) :
    SpecEnv env bo lp sf Γspec ∧ LBWfSpec Γspec ∧
      ErasesEnv env bo lp Γspec t₀ ∧ LowerEnv Γspec sf.gdecls :=
  ⟨hreg.specEnv, ⟨hreg.spec.keys, hreg.specClosed⟩,
    hreg.erasesEnv hdeps htab, hreg.lowerEnv hsat⟩

/-! ## The capstone -/

set_option linter.unusedVariables false in
/--
**The shipping erasure is correct at a first-order answer.** For a term the erasure ran on
under a pinned configuration, whose prepared form is inside the fragment and whose emitted
program declares a body for every constant it reaches: `(Γ, t)` is the lowered image of a
specification environment that erases the prepared term, it satisfies `LBWfPeregrine` —
`expandedFix` included, since F-ETA's registered fixpoints are η-expanded — and every
first-order answer the **source** evaluation produces is reproduced by it, uniquely and
box-free. The binders' classes are `doc/trust.md`'s
rows; the erasure half is `erasure_bridge_of_run`, the simulation `erases_correct` at the
spine, the answer's shape and uniqueness `firstorder_erases_core`, and the rest `hbridge`.
-/
theorem shipping_erase_correct_firstorder
    {lenv : Lean.Environment} {env : VEnv} {gw : Void IO.RealWorld → NameGenerator}
    {tbl : SourceTable} {cfg : ErasureConfig} {e pe : Expr} {ve : VExpr}
    {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
    {w wp w' : Void IO.RealWorld}
    {Γ : GlobalDeclarations} {t : LBTerm} {inls : List Kername}
    (P : ErasureSpec lenv env [] gw)
    (E : EraserAsks lenv env gw)
    (A : UpstreamAsks env)
    (htbl : SourceTableAdequate lenv tbl)
    (hsafe : TableSafe lenv tbl)
    (hblk : TableBlocks lenv env tbl)
    (hcfg : ConfigPinned cfg)
    (hcb : CompilerBodies lenv env tbl.body?)
    (hwt : TrExprS env [] [] pe ve)
    (hsup : Supported env tbl pe)
    (hprep : Erasure.prepare_erasure e {} { «config» := cfg } cctx ref w = .ok (pe, {}) wp)
    (hrun : Erasure.erase e cfg cctx ref w = .ok (.untyped Γ (some t), inls) w')
    (hnb : NoBodylessRefs Γ t)
    (hwf : LBWfPeregrine Γ t)
    (hbridge : ∀ (sf : ErasureState) (wt : Void IO.RealWorld),
      Erasure.visitExpr pe {} { «config» := cfg } cctx ref wp = .ok (t, sf) wt →
      ∃ Γspec : GlobalDeclarations, SpecEnv env tbl.body? tbl.levels? sf Γspec ∧
        ∀ t₀ : LBTerm, Erases env [] [] pe t₀ → Lower Γspec t₀ t →
          ErasureBridge env tbl.body? tbl.levels? Γspec Γ t₀) :
    ∃ (Γspec : GlobalDeclarations) (t₀ : LBTerm),
      Erasure.prepare_erasure e {} { «config» := cfg } cctx ref w = .ok (pe, {}) wp
      ∧ Erases env [] [] pe t₀
      ∧ ErasesEnv env tbl.body? tbl.levels? Γspec t₀
      ∧ Lower Γspec t₀ t
      ∧ LowerEnv Γspec Γ
      ∧ LBWfPeregrine Γ t
      ∧ ∀ (args : List Expr) (targs : List LBTerm) (I : Name) (us : List VLevel)
          (idx : List VExpr) (v : Expr) (vv vs : VExpr),
          targs.length = args.length →
          (∀ i, i < args.length → ∃ a₀, Erases env [] [] args[i]! a₀ ∧
            Lower Γspec a₀ targs[i]! ∧ ErasesEnv env tbl.body? tbl.levels? Γspec a₀) →
          TrExprS env [] [] (mkApps pe args) vs →
          SEval env tbl.body? [] fullFlags [] (mkApps e args) v →
          TrExprS env [] [] v vv →
          env.HasType 0 [] vv (VExpr.mkApps (.const I us) idx) →
          FirstOrderInd env I →
          ∃ tv₀ tv, Erases env [] [] v tv₀ ∧ Lower Γspec tv₀ tv ∧ NoBox tv
            ∧ (∀ tv', Erases env [] [] v tv' → tv' = tv₀)
            ∧ WcbvEval Γ eraseFlags (LBTerm.mkApps t targs) tv := by
  obtain ⟨pe', t', sp, sf, wp', wt, hpr, hvis, hp, -⟩ := erase_run_ok hrun
  obtain ⟨rfl, rfl, rfl⟩ : pe = pe' ∧ sp = ({} : ErasureState) ∧ wp = wp' := by
    injection hprep.symm.trans hpr with h1 h2
    injection h1 with h3 h4
    exact ⟨h3, h4.symm, h2⟩
  obtain rfl : t = t' := by injection hp with _ h; exact Option.some.inj h
  obtain ⟨Γspec, hspec, hrest⟩ := hbridge sf wt hvis
  obtain ⟨t₀, her, hlow⟩ :=
    erasure_bridge_of_run P E A htbl hsafe hblk hcfg hcb hsup hwt hprep hvis hspec
  have B := hrest t₀ her hlow
  refine ⟨Γspec, t₀, hprep, her, B.erasesEnv, hlow, B.lowerEnv, hwf, ?_⟩
  intro args targs I us idx v vv vs hlen hargs hwtsp hev hvwt hty hfo
  obtain ⟨a₀s, hlen₀, ha₀⟩ :=
    exists_list_of_index args.length
      (fun i a₀ => Erases env [] [] args[i]! a₀ ∧ Lower Γspec a₀ targs[i]! ∧
        ErasesEnv env tbl.body? tbl.levels? Γspec a₀) hargs
  have hevp : SEval env tbl.body? [] fullFlags [] (mkApps pe args) v :=
    prepare_sound E hcfg.1 hprep args tbl.body? [] fullFlags [] v hev
  have hspine : Erases env [] [] (mkApps pe args) (LBTerm.mkApps t₀ a₀s) :=
    Erases.mkApps args a₀s her hlen₀ (fun i hi => (ha₀ i hi).1)
  have hlowspine : Lower Γspec (LBTerm.mkApps t₀ a₀s) (LBTerm.mkApps t targs) :=
    Lower.mkApps hlow (by rw [hlen, hlen₀]) (fun i hi => (ha₀ i (by omega)).2.1)
  have hspecspine : ErasesEnv env tbl.body? tbl.levels? Γspec (LBTerm.mkApps t₀ a₀s) :=
    B.erasesEnv.mkApps (fun x hx => by
      obtain ⟨i, hi, rfl⟩ := Lower.mem_getElem! hx
      exact (ha₀ i (by omega)).2.2)
  obtain ⟨tv₀, tv, herv, hlowv, hevtgt⟩ :=
    erases_correct P.envWF hwtsp hevp hspine hlowspine hspecspine B.lowerEnv
      (tabledLevels_of_table htbl hsafe hcb) A
  obtain ⟨hfos, huniq⟩ :=
    firstorder_erases_core (Us := []) P.envWF A hev.svalue hfo hvwt hty herv
  exact ⟨tv₀, tv, herv, hlowv, noBox_lower_of_foSpine hfos hlowv, huniq, hevtgt⟩

end LeanToLambdaBox
