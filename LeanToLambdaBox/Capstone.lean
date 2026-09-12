import LeanToLambdaBox.ErasesLB
import LeanToLambdaBox.FirstOrderInd
import LeanToLambdaBox.SpecEnv
import LeanToLambdaBox.SubjectReduction
import LeanToLambdaBox.Supported

/-!
# The capstone — the shipping erasure, at a first-order answer

`shipping_erase_correct_firstorder` is the applied form of the correctness statement: for a
source term the erasure ran on, the emitted program `(Γ, t)` is the lowered image of a
specification environment that erases `e`, it satisfies what peregrine's first pass needs,
and every first-order answer the source evaluation produces is reproduced — uniquely and
box-free — by the emitted program under λ□'s own semantics.

`LBExpandedFix` is **not** concluded: the erasure emits bare `tFix` constant bodies, so
`PeregrinePre` does not hold of its output (finding F-ETA). The conclusion is
`LBWfPeregrine`, which is what the emitted program does satisfy.

Three hypotheses are stated in the form this module can express. `hsup` is the fragment
predicate `Supported`, which a rung discharges by computation through `supportedB_sound`.
The first-order side condition is `FirstOrderInd env I`, the closed predicate of
`FirstOrderInd.lean`. The spine premise is the composite `ErasesLB`, together with the length
equation `Lower.mkApps` consumes.

`hnb : NoBodylessRefs Γ t` is `erase_correct_firstorder`'s `axiom_free` analogue, decided per
rung: without it a run reaching a body-less declaration would satisfy the conclusion
vacuously, its source evaluation having no derivation.

At this wave the composition is proved and the results it composes are the fields of one
named binder, `hbridge : ErasureBridge …` — each field named after the theorem that
discharges it and the wave that lands it.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean Erasure Witness

/-! ## The configuration the statement is made at -/

/-- The five configuration restrictions the correctness statement is made under: no
`@[csimp]` replacement, no `@[extern]` axiomatisation, peano `Nat`, no constructor argmask
pruning, no typeclass-dispatch auto-inlining. Each is a scope restriction stated as a
hypothesis rather than an omission. -/
def ConfigPinned (cfg : ErasureConfig) : Prop :=
  cfg.csimp = false ∧ cfg.extern = .preferLogical ∧ cfg.nat = .peano ∧
    cfg.remove_irrel_constr_args = false ∧ cfg.auto_inline_typeclass_dispatch = false

/-! ## The pending results -/

/--
What the capstone composes, as one named binder: the bridge's own conclusion together with
the results the later waves prove. Every field names the theorem that discharges it, and the
shapes are the ones the composition consumes; where a field is *stronger* than the theorem
named — a premise that theorem takes and the capstone's clause cannot supply — the field's
docstring says so.
-/
structure ErasureBridge (env : VEnv) (bo : Name → Option Expr)
    (e : Expr) (Γspec Γ : GlobalDeclarations) (t t₀ : LBTerm) : Prop where
  /-- The subject's own erasure. Discharged by `visitExpr_refines_erasesLB` (T8, W4). -/
  erases : Erases env [] [] e t₀
  /-- The specification environment erases the source environment. Discharged by
      `SpecEnv.erasesEnv` on the `SpecEnv` that W3 constructs from the run's final state. -/
  erasesEnv : ErasesEnv env bo Γspec t₀
  /-- The emitted term is the lowered erasure. Discharged by `visitExpr_refines_erasesLB`. -/
  lower : Lower Γspec t₀ t
  /-- The emitted environment is the lowered, pruned specification environment. Discharged
      by W3's environment instantiation. -/
  lowerEnv : LowerEnv Γspec Γ
  /-- The specification environment is well formed. Its `Nodup` half is `ErasesEnv.keys`;
      the `ClosedBodies` half is W3's. -/
  wfSpec : LBWfSpec Γspec
  /-- What peregrine's first pass needs of the emitted program. Discharged by W4's output
      lemmas; `LBExpandedFix` is deliberately absent (F-ETA). -/
  wf : LBWfPeregrine Γ t
  /-- `erases_correct` (T5, W3): one simulation, on the composite, at the **emitted**
      environment. Stronger than T5 by three premises T9's clause cannot supply at an
      applied subject — `env.WF`, `TrExprS env [] [] s ve` and `ErasesEnv env bo Γspec t₀s`
      hold of the subject `e` and its erasure `t₀`, not of the spine `mkApps e args` — and
      by `LowerEnv Γspec Γ`, which is the field `lowerEnv`. At `args = []` they coincide. -/
  simulate : ∀ {s t₀s ts v : _}, Erases env [] [] s t₀s → Lower Γspec t₀s ts →
      SEval env bo [] fullFlags [] s v →
      ∃ v₀ v', Erases env [] [] v v₀ ∧ Lower Γspec v₀ v' ∧ WcbvEval Γ eraseFlags ts v'
  /-- `firstorder_erases_deterministic` and `firstorder_no_box` (T7, W3). Stronger than T7
      by the value premise `SEval env bo [] fullFlags [] v v`, and by asking box-freedom of
      the *lowered* value: T7 proves it of the erasure, and the transport along `Lower` is
      false without a guard (`noBox_lower_needs_noFix`). -/
  firstorder : ∀ {I : Name} {us : List VLevel} {idx : List VExpr} {v : Expr} {vv : VExpr}
      {tv₀ tv : LBTerm}, FirstOrderInd env I → TrExprS env [] [] v vv →
      env.HasType 0 [] vv (VExpr.mkApps (.const I us) idx) →
      Erases env [] [] v tv₀ → Lower Γspec tv₀ tv →
      NoBox tv ∧ ∀ tv', Erases env [] [] v tv' → tv' = tv₀

/-! ## The capstone -/

set_option linter.unusedVariables false in
/--
**The shipping erasure is correct at a first-order answer.** For a term the erasure ran on
under a pinned configuration, inside the fragment, whose emitted program declares
a body for every constant it reaches: `(Γ, t)` is the lowered image of a specification
environment that erases `e`, it satisfies `LBWfPeregrine` — not `LBExpandedFix`, finding
F-ETA — and every first-order answer the source evaluation produces is reproduced by it,
uniquely and box-free. The binders' classes are `doc/trust.md`'s rows; the proof is
`hbridge`'s fields, composed.
-/
theorem shipping_erase_correct_firstorder
    {lenv : Lean.Environment} {env : VEnv} {gw : Void IO.RealWorld → NameGenerator}
    {tbl : SourceTable} {cfg : ErasureConfig} {e : Expr} {ve : VExpr}
    {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {Γ : GlobalDeclarations} {t : LBTerm} {inls : List Kername}
    (P : ErasureSpec lenv env [] gw)
    (htbl : SourceTableAdequate lenv tbl)
    (hcfg : ConfigPinned cfg)
    (hcb : CompilerBodies lenv env tbl.body?)
    (hwt : TrExprS env [] [] e ve)
    (hsup : Supported env tbl e)
    (hrun : Erasure.erase e cfg cctx ref w = .ok (.untyped Γ (some t), inls) w')
    (hnb : NoBodylessRefs Γ t)
    (hbridge : ∃ Γspec t₀, ErasureBridge env tbl.body? e Γspec Γ t t₀) :
    ∃ (Γspec : GlobalDeclarations) (t₀ : LBTerm),
      Erases env [] [] e t₀
      ∧ ErasesEnv env tbl.body? Γspec t₀
      ∧ Lower Γspec t₀ t
      ∧ LowerEnv Γspec Γ
      ∧ LBWfPeregrine Γ t
      ∧ ∀ (args : List Expr) (targs : List LBTerm) (I : Name) (us : List VLevel)
          (idx : List VExpr) (v : Expr) (vv : VExpr),
          targs.length = args.length →
          (∀ i, i < args.length → ErasesLB env [] Γspec [] args[i]! targs[i]!) →
          SEval env tbl.body? [] fullFlags [] (mkApps e args) v →
          TrExprS env [] [] v vv →
          env.HasType 0 [] vv (VExpr.mkApps (.const I us) idx) →
          FirstOrderInd env I →
          ∃ tv₀ tv, Erases env [] [] v tv₀ ∧ Lower Γspec tv₀ tv ∧ NoBox tv
            ∧ (∀ tv', Erases env [] [] v tv' → tv' = tv₀)
            ∧ WcbvEval Γ eraseFlags (LBTerm.mkApps t targs) tv := by
  obtain ⟨Γspec, t₀, B⟩ := hbridge
  refine ⟨Γspec, t₀, B.erases, B.erasesEnv, B.lower, B.lowerEnv, B.wf, ?_⟩
  intro args targs I us idx v vv hlen hargs hev hvwt hty hfo
  obtain ⟨a₀s, hlen₀, ha₀⟩ :=
    exists_list_of_index args.length
      (fun i a₀ => Erases env [] [] args[i]! a₀ ∧ Lower Γspec a₀ targs[i]!) hargs
  have hspine : Erases env [] [] (mkApps e args) (LBTerm.mkApps t₀ a₀s) :=
    Erases.mkApps args a₀s B.erases hlen₀ (fun i hi => (ha₀ i hi).1)
  have hlowspine : Lower Γspec (LBTerm.mkApps t₀ a₀s) (LBTerm.mkApps t targs) :=
    Lower.mkApps B.lower (by rw [hlen, hlen₀]) (fun i hi => (ha₀ i (by omega)).2)
  obtain ⟨tv₀, tv, herv, hlowv, hevtgt⟩ := B.simulate hspine hlowspine hev
  obtain ⟨hnobox, huniq⟩ := B.firstorder hfo hvwt hty herv hlowv
  exact ⟨tv₀, tv, herv, hlowv, hnobox, huniq, hevtgt⟩

end LeanToLambdaBox
