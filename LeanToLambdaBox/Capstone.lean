import LeanToLambdaBox.LowerCorrect
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

Three hypotheses are stated in the form this module can express. `hsup` is the `supportedB`
verdict on the reified table — the decidable form, which a rung discharges by computation;
the fragment predicate it certifies is `Supported.lean`'s to state. The first-order side
condition is the parameter `fo : Name → Prop` with the premise `fo I`, so the statement is a
schema a first-order predicate instantiates. The spine premise is `Erases` composed with
`Lower`, written out, together with the length equation `Lower.mkApps` consumes.

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

/-! ## Erasure over an application spine -/

/-- `Erases` is a congruence over an application spine: the source spine erases to the λ□
spine of the erased head and the erased arguments. -/
theorem erases_mkApps {env : VEnv} {Us : List Name} {Δ : VLCtx} {f : Expr} {f' : LBTerm} :
    ∀ (args : List Expr) (args' : List LBTerm), Erases env Us Δ f f' →
      args'.length = args.length →
      (∀ i, i < args.length → Erases env Us Δ args[i]! args'[i]!) →
      Erases env Us Δ (mkApps f args) (LBTerm.mkApps f' args') := by
  intro args
  induction args generalizing f f' with
  | nil =>
      intro args' hf hlen _
      have : args' = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst this; exact hf
  | cons a as ih =>
      intro args' hf hlen h
      obtain ⟨b, bs, rfl⟩ : ∃ b bs, args' = b :: bs := by
        cases args' with
        | nil => simp at hlen
        | cons b bs => exact ⟨b, bs, rfl⟩
      have hlen' : bs.length = as.length := by simpa using hlen
      have ha : Erases env Us Δ a b := by
        have h0 := h 0 (by simp)
        rwa [getElem!_pos (a :: as) 0 (by simp), getElem!_pos (b :: bs) 0 (by simp)] at h0
      refine ih bs (.app hf ha) hlen' ?_
      intro i hi
      have hi' := h (i + 1) (by simp only [List.length_cons]; omega)
      rwa [getElem!_pos (a :: as) (i + 1) (by simp only [List.length_cons]; omega),
        getElem!_pos (b :: bs) (i + 1) (by simp only [List.length_cons]; omega),
        List.getElem_cons_succ, List.getElem_cons_succ,
        ← getElem!_pos as i hi, ← getElem!_pos bs i (by omega)] at hi'

/-! ## The pending results -/

/--
What the capstone composes, as one named binder: the bridge's own conclusion together with
the three simulation results the later waves prove. Every field names the theorem that
discharges it; none is an axiom, and the capstone's proof is exactly the composition.

The shapes are the ones the composition consumes. Where a field is *stronger* than the
theorem named — a premise that theorem takes and the capstone's clause cannot supply — the
field's docstring says so.
-/
structure ErasureBridge (env : VEnv) (bo : Name → Option Expr) (fo : Name → Prop)
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
  /-- `erases_correct` (T5, W2-W3). Stronger than T5 by two premises T9's clause cannot
      supply at an applied subject: `TrExprS env [] [] s ve` and `ErasesEnv env bo Γspec ts`
      hold of the subject `e` and its erasure `t₀`, not of the spine `mkApps e args`. At
      `args = []` the two coincide. -/
  simulate : ∀ {s ts v : _}, Erases env [] [] s ts → SEval env bo [] fullFlags [] s v →
      ∃ v', Erases env [] [] v v' ∧ WcbvEval Γspec eraseFlags ts v'
  /-- `lower_correct` (T6, W2), whose δ / constructor / fix fragment is
      `lower_correct_deltaChain`. Stronger than T6 by its `LBClosed ts 0` premise, which
      T9's clause does not carry for the spine. -/
  lowerCorrect : ∀ {s ts v : LBTerm}, Lower Γspec s ts → WcbvEval Γspec eraseFlags s v →
      ∃ v', Lower Γspec v v' ∧ WcbvEval Γ eraseFlags ts v'
  /-- `firstorder_erases_deterministic` and `firstorder_no_box` (T7, W3). Stronger than T7
      by the value premise `SEval env bo [] fullFlags [] v v`, and by asking box-freedom of
      the *lowered* value: T7 proves it of the erasure, and the transport along `Lower` is
      false without a guard (`noBox_lower_needs_noFix`). -/
  firstorder : ∀ {I : Name} {us : List VLevel} {idx : List VExpr} {v : Expr} {vv : VExpr}
      {tv₀ tv : LBTerm}, fo I → TrExprS env [] [] v vv →
      env.HasType 0 [] vv (VExpr.mkApps (.const I us) idx) →
      Erases env [] [] v tv₀ → Lower Γspec tv₀ tv →
      NoBox tv ∧ ∀ tv', Erases env [] [] v tv' → tv' = tv₀

/-! ## The capstone -/

set_option linter.unusedVariables false in
/--
**The shipping erasure is correct at a first-order answer.** For a source term `e` the
erasure ran on under a pinned configuration, inside the supported fragment, whose emitted
program's reachable axioms have realizers: there is a specification environment `Γspec` and
a specification term `t₀` such that `e` erases to `t₀` over `Γspec`, the emitted program is
their lowered image, the emitted program satisfies `LBWfPeregrine`, and for every
first-order answer the source evaluation produces, the emitted program evaluates to the
answer's erasure — uniquely, and with no `□` in it.

`P`, `htbl`, `hrun` and `hwt` are the named class-**D** binders: each is about a primitive
no term denotes (the elaboration environment, a monadic run, a table copied out of it) or
awaits the translation witness. `hcfg`, `hsup` and `hax` are decidable per program.
`hbridge` carries the results the later waves prove; the proof here is the composition.

`LBExpandedFix` is not concluded — finding F-ETA.
-/
theorem shipping_erase_correct_firstorder
    {lenv : Lean.Environment} {env : VEnv} {gw : Void IO.RealWorld → NameGenerator}
    {tbl : SourceTable} {cfg : ErasureConfig} {fuel : Nat} {e : Expr} {ve : VExpr}
    {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {Γ : GlobalDeclarations} {t : LBTerm} {inls : List Kername} {fo : Name → Prop}
    (P : ErasureSpec lenv env [] gw)
    (htbl : SourceTableAdequate lenv tbl)
    (hcfg : ConfigPinned cfg)
    (hcb : CompilerBodies lenv env tbl.body?)
    (hwt : TrExprS env [] [] e ve)
    (hsup : supportedB tbl fuel e = .ok ())
    (hrun : Erasure.erase e cfg cctx ref w = .ok (.untyped Γ (some t), inls) w')
    (hax : ErasableAxioms Γ t)
    (hbridge : ∃ Γspec t₀, ErasureBridge env tbl.body? fo e Γspec Γ t t₀) :
    ∃ (Γspec : GlobalDeclarations) (t₀ : LBTerm),
      Erases env [] [] e t₀
      ∧ ErasesEnv env tbl.body? Γspec t₀
      ∧ Lower Γspec t₀ t
      ∧ LowerEnv Γspec Γ
      ∧ LBWfPeregrine Γ t
      ∧ ∀ (args : List Expr) (targs : List LBTerm) (I : Name) (us : List VLevel)
          (idx : List VExpr) (v : Expr) (vv : VExpr),
          targs.length = args.length →
          (∀ i, i < args.length →
            ∃ a₀, Erases env [] [] args[i]! a₀ ∧ Lower Γspec a₀ targs[i]!) →
          SEval env tbl.body? [] fullFlags [] (mkApps e args) v →
          TrExprS env [] [] v vv →
          env.HasType 0 [] vv (VExpr.mkApps (.const I us) idx) →
          fo I →
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
    erases_mkApps args a₀s B.erases hlen₀ (fun i hi => (ha₀ i hi).1)
  have hlowspine : Lower Γspec (LBTerm.mkApps t₀ a₀s) (LBTerm.mkApps t targs) :=
    Lower.mkApps B.lower (by rw [hlen, hlen₀]) (fun i hi => (ha₀ i (by omega)).2)
  obtain ⟨tv₀, herv, hevspec⟩ := B.simulate hspine hev
  obtain ⟨tv, hlowv, hevtgt⟩ := B.lowerCorrect hlowspine hevspec
  obtain ⟨hnb, huniq⟩ := B.firstorder hfo hvwt hty herv hlowv
  exact ⟨tv₀, tv, herv, hlowv, hnb, huniq, hevtgt⟩

end LeanToLambdaBox
