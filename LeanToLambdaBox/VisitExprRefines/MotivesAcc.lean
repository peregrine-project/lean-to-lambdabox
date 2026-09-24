import LeanToLambdaBox.VisitExprRefines.Motives
-- `TableRecPrefixed` and `no_realizer_exit_compiler`: the table column `AccAsks` carries for
-- the two realizer exits.
import LeanToLambdaBox.VisitExprRefines.Step.Env

/-!
# The accumulator conjunct, in its own bundle of motives

`doc/rework/12-REPAIRS-W9.md` §2.5. The clause the registration path owes — "from the
accumulator at the entry state, an extension of the specification environment and the
accumulator at the exit state" — mentions no term, no `Lower` and no `SpecEnv`, so it does not
belong in `RunRefines`. It goes in a bundle of its own, proved by a second instance of
`Erasure.visitExpr.mutual_fixpoint_induct` that *consumes* the first bundle's conclusion at
the shipping family. `RunRefines`, `RunRefinesAlt`, `HeadRefines` and `Motive1`…`Motive18` are
therefore unchanged, and so are the eighteen step lemmas that prove them.

Each `MotiveAccᵢ` carries the premises of `Motiveᵢ` — the same `BridgeInv`, `Supported`,
translation and head premises — and replaces the conclusion by `AccGrows`. Keeping the premise
lists identical is what makes each `StepAccᵢ` route its sub-runs exactly as `Stepᵢ` does.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean Erasure Witness Lean.Order

-- The approximation conjunct is `⊑` on a five-argument member of the erasure family, whose
-- `PartialOrder` instance is five transformer layers deep under five binders.
set_option synthInstance.maxSize 4000

/-! ## The accumulator along a run -/

/-- **The accumulator at one state.** `RegAcc` — the triple a registration run carries — with
the facts a registration *step* reads of the pair besides it: the two clauses
`SpecKeysEmitted` exempts (`ColdStartShape.lean`'s `RuntimeKeysModelled` and
`EmittedNotRuntime`), and the three state invariants `regInv_registerInd_run` asks for at its
entry state. Each is re-established at the grown pair, which is why they travel with the
accumulator rather than beside it. -/
structure AccState (lenv : Environment) (env : VEnv) (tbl : SourceTable)
    (Γ : GlobalDeclarations) (s : ErasureState) : Prop where
  /-- The accumulator proper. -/
  acc : RegAcc env tbl.body? tbl.levels? Γ s
  /-- Every runtime key of the specification environment answers to a modelled `casesOn`. -/
  rkm : RuntimeKeysModelled env Γ
  /-- No emitted key is a runtime key of the specification environment. -/
  enr : EmittedNotRuntime Γ s
  /-- Every emitted key is a registered constant's kername or a registered block's key. -/
  keyed : RegKeyed env s
  /-- The constant registry holds canonical kernames. -/
  canon : CanonicalConstants s
  /-- The block table mirrors the emitted blocks. -/
  cover : IndBlocksCover lenv s

/-- The accumulator is blind to the `@[inline]` bookkeeping list: no clause reads it, so
every field is its own at the consed state. -/
theorem AccState.inlinings {lenv : Environment} {env : VEnv} {tbl : SourceTable}
    {Γ : GlobalDeclarations} {s : ErasureState} {kn : Kername}
    (h : AccState lenv env tbl Γ s) :
    AccState lenv env tbl Γ { s with inlinings := kn :: s.inlinings } where
  acc :=
    let H := h.acc.shape
    let C := h.acc.content
    let K := h.acc.keysEmitted
    ⟨⟨H.spec, H.specClosed, H.specFVarFree, H.consts, H.inds, H.keys, H.defs, H.defsTotal,
        H.axioms, H.indsEmitted, H.sub, H.closed⟩,
      ⟨C.defns, C.declEnv⟩, ⟨K.consts, K.inds⟩⟩
  rkm := h.rkm
  enr := h.enr
  keyed := ConstExt.regKeyed (s := s) (s' := { s with inlinings := kn :: s.inlinings })
    (ConstExt.of_same rfl rfl) (fun _ hn => hn) h.keyed
  canon := (ConstExt.of_same (s := s) (s' := { s with inlinings := kn :: s.inlinings })
    rfl rfl).canon h.canon
  cover := ConstExt.indBlocksCover (s := s) (s' := { s with inlinings := kn :: s.inlinings })
    (ConstExt.of_same rfl rfl) rfl (fun _ hn => hn) h.cover

/-- **The accumulator along a sub-run**: an extension of the specification environment carrying
the state column from the entry state to the exit state. No term occurs, which is what keeps
the relation out of `RunRefines`. -/
def AccGrows (lenv : Environment) (env : VEnv) (tbl : SourceTable)
    (s s' : ErasureState) : Prop :=
  ∀ Γ₀, AccState lenv env tbl Γ₀ s →
    ∃ Γ₁, SpecGrow Γ₀ Γ₁ ∧ AccState lenv env tbl Γ₁ s'

/-- A run that left the state alone grows nothing. -/
theorem AccGrows.rfl' {lenv : Environment} {env : VEnv} {tbl : SourceTable}
    (s : ErasureState) : AccGrows lenv env tbl s s :=
  fun Γ₀ h => ⟨Γ₀, SpecGrow.refl _, h⟩

/-- The same at a state equation, which is the shape a primitive's run lemma hands over. -/
theorem AccGrows.of_eq {lenv : Environment} {env : VEnv} {tbl : SourceTable}
    {s s' : ErasureState} (h : s' = s) : AccGrows lenv env tbl s s' := by
  subst h; exact AccGrows.rfl' _

/-- Composition of the conjunct is `SpecGrow.trans` and nothing else. -/
theorem AccGrows.trans {lenv : Environment} {env : VEnv} {tbl : SourceTable}
    {s s' s₂ : ErasureState} (h : AccGrows lenv env tbl s s')
    (h' : AccGrows lenv env tbl s' s₂) : AccGrows lenv env tbl s s₂ := by
  intro Γ₀ hA
  obtain ⟨Γ₁, hg₁, hA₁⟩ := h Γ₀ hA
  obtain ⟨Γ₂, hg₂, hA₂⟩ := h' Γ₁ hA₁
  exact ⟨Γ₂, hg₁.trans hg₂, hA₂⟩

/-- The `@[inline]` bookkeeping cons grows nothing. -/
theorem AccGrows.inl {lenv : Environment} {env : VEnv} {tbl : SourceTable}
    (s : ErasureState) (kn : Kername) :
    AccGrows lenv env tbl s { s with inlinings := kn :: s.inlinings } :=
  fun Γ₀ h => ⟨Γ₀, SpecGrow.refl _, h.inlinings⟩

/-! ## The eighteen motives -/

section Motives

variable (lenv : Environment) (env : VEnv) (tbl : SourceTable) (cfg : ErasureConfig)
  (gw : Void IO.RealWorld → NameGenerator)

/-- Motive 1 — `Erasure.visitExpr`. -/
def MotiveAcc1 (f : Expr → EraseM LBTerm) : Prop :=
  (∀ e s ctx cctx ref w t s' w', f e s ctx cctx ref w = .ok (t, s') w' →
    ∀ Us Δ, BridgeInv env Us tbl cfg (gw w) ctx s Δ → Supported env tbl e →
      (∃ ve, TrExprS env Us Δ e ve) → AccGrows lenv env tbl s s') ∧
  f ⊑ Erasure.visitExpr

/-- Motive 2 — `Erasure.visitLiteral`. -/
def MotiveAcc2 (f : Literal → EraseM LBTerm) : Prop :=
  (∀ l s ctx cctx ref w t s' w', f l s ctx cctx ref w = .ok (t, s') w' →
    ∀ Us Δ n, BridgeInv env Us tbl cfg (gw w) ctx s Δ → l = .natVal n →
      PeanoReady env → peanoReadyB tbl = true → Supported env tbl (.lit l) →
      (∃ ve, TrExprS env Us Δ (.lit l) ve) → AccGrows lenv env tbl s s') ∧
  f ⊑ Erasure.visitLiteral

/-- Motive 3 — `Erasure.visitConstructor`, one of the three members that register a block. -/
def MotiveAcc3 (f : Name → Array Expr → EraseM LBTerm) : Prop :=
  (∀ cn args s ctx cctx ref w t s' w', f cn args s ctx cctx ref w = .ok (t, s') w' →
    ∀ Us Δ, BridgeInv env Us tbl cfg (gw w) ctx s Δ →
      (∃ I k, CtorOf env cn I k) → ArgsOk env Us tbl Δ args →
      AccGrows lenv env tbl s s') ∧
  f ⊑ Erasure.visitConstructor

/-- Motive 4 — `Erasure.visitConst`. -/
def MotiveAcc4 (f : Expr → EraseM LBTerm) : Prop :=
  (∀ e s ctx cctx ref w t s' w', f e s ctx cctx ref w = .ok (t, s') w' →
    ∀ Us Δ n us, BridgeInv env Us tbl cfg (gw w) ctx s Δ → e = .const n us →
      PlainHead n → isCasesOnName n = false → KnownHead env tbl n → Supported env tbl e →
      (∀ (I : Name) (k : Nat), ¬ CtorOf env n I k) →
      (∀ (iid : InductiveId) (np : Nat) (nfs : List Nat), ¬ IndInfo env n iid np nfs) →
      AccGrows lenv env tbl s s') ∧
  f ⊑ Erasure.visitConst

/-- Motive 5 — `Erasure.get_constant_kername`. -/
def MotiveAcc5 (f : Name → EraseM Kername) : Prop :=
  (∀ n s ctx cctx ref w kn s' w', f n s ctx cctx ref w = .ok (kn, s') w' →
    ∀ Us Δ, BridgeInv env Us tbl cfg (gw w) ctx s Δ → Supported env tbl (.const n []) →
      (tbl.decl? n).isSome → AccGrows lenv env tbl s s') ∧
  f ⊑ Erasure.get_constant_kername

/-- Motive 6 — `Erasure.visitMutual`, the member with the registering exits. -/
def MotiveAcc6 (f : Name → EraseM Unit) : Prop :=
  (∀ n s ctx cctx ref w u s' w', f n s ctx cctx ref w = .ok (u, s') w' →
    ∀ Us Δ, BridgeInv env Us tbl cfg (gw w) ctx s Δ → Supported env tbl (.const n []) →
      (tbl.decl? n).isSome → AccGrows lenv env tbl s s') ∧
  f ⊑ Erasure.visitMutual

/-- Motive 7 — `Erasure.visitAppArgs`. -/
def MotiveAcc7 (f : LBTerm → Array Expr → EraseM LBTerm) : Prop :=
  (∀ hd args s ctx cctx ref w t s' w', f hd args s ctx cctx ref w = .ok (t, s') w' →
    ∀ Us Δ (e : Expr), BridgeInv env Us tbl cfg (gw w) ctx s Δ →
      HeadRefines env Us tbl ctx Δ s e hd → ArgsOk env Us tbl Δ args →
      AccGrows lenv env tbl s s') ∧
  f ⊑ Erasure.visitAppArgs

/-- Motive 8 — `Erasure.visitLet`. -/
def MotiveAcc8 (f : Expr → EraseM LBTerm) : Prop :=
  (∀ e s ctx cctx ref w t s' w', f e s ctx cctx ref w = .ok (t, s') w' →
    ∀ Us Δ n ty v b nd, BridgeInv env Us tbl cfg (gw w) ctx s Δ → e = .letE n ty v b nd →
      Supported env tbl e → (∃ ve, TrExprS env Us Δ e ve) →
      AccGrows lenv env tbl s s') ∧
  f ⊑ Erasure.visitLet

/-- Motive 9 — `Erasure.visitLambda`. -/
def MotiveAcc9 (f : Expr → EraseM LBTerm) : Prop :=
  (∀ e s ctx cctx ref w t s' w', f e s ctx cctx ref w = .ok (t, s') w' →
    ∀ Us Δ n ty b bi, BridgeInv env Us tbl cfg (gw w) ctx s Δ → e = .lam n ty b bi →
      Supported env tbl e → (∃ ve, TrExprS env Us Δ e ve) →
      AccGrows lenv env tbl s s') ∧
  f ⊑ Erasure.visitLambda

/-- Motive 10 — `Erasure.visitProj`, one of the three members that register a block. -/
def MotiveAcc10 (f : Name → Nat → Expr → EraseM LBTerm) : Prop :=
  (∀ tn i e s ctx cctx ref w t s' w', f tn i e s ctx cctx ref w = .ok (t, s') w' →
    ∀ Us Δ (I : ReifiedInduct) (np nf : Nat), BridgeInv env Us tbl cfg (gw w) ctx s Δ →
      tbl.ind? tn = some I → InformativeInd env tn → IndArity env tn np [nf] → i < nf →
      Supported env tbl e → (∃ ve, TrExprS env Us Δ e ve) →
      AccGrows lenv env tbl s s') ∧
  f ⊑ Erasure.visitProj

/-- Motive 11 — `Erasure.visitApp`. -/
def MotiveAcc11 (f : Expr → EraseM LBTerm) : Prop :=
  (∀ e s ctx cctx ref w t s' w', f e s ctx cctx ref w = .ok (t, s') w' →
    ∀ Us Δ, BridgeInv env Us tbl cfg (gw w) ctx s Δ → Supported env tbl e →
      (∃ ve, TrExprS env Us Δ e ve) →
      (∀ (c : Name) (us : List Level), e.getAppFn = .const c us →
        ∀ (iid : InductiveId) (np : Nat) (nfs : List Nat), ¬ IndInfo env c iid np nfs) →
      AccGrows lenv env tbl s s') ∧
  f ⊑ Erasure.visitApp

/-- Motive 12 — `Erasure.visitConstApp`. -/
def MotiveAcc12 (f : Expr → EraseM LBTerm) : Prop :=
  (∀ e s ctx cctx ref w t s' w', f e s ctx cctx ref w = .ok (t, s') w' →
    ∀ Us Δ cn us, BridgeInv env Us tbl cfg (gw w) ctx s Δ → e.getAppFn = .const cn us →
      Supported env tbl e → (∃ ve, TrExprS env Us Δ e ve) →
      (∀ (iid : InductiveId) (np : Nat) (nfs : List Nat), ¬ IndInfo env cn iid np nfs) →
      AccGrows lenv env tbl s s') ∧
  f ⊑ Erasure.visitConstApp

/-- Motive 13 — `Erasure.visitCtorEta`. -/
def MotiveAcc13 (f : Name → Nat → Expr → EraseM LBTerm) : Prop :=
  (∀ cn ar e s ctx cctx ref w t s' w', f cn ar e s ctx cctx ref w = .ok (t, s') w' →
    ∀ Us Δ us, BridgeInv env Us tbl cfg (gw w) ctx s Δ → e.getAppFn = .const cn us →
      (∃ I k, CtorOf env cn I k) → ar ≤ e.getAppArgs.size →
      ArgsOk env Us tbl Δ e.getAppArgs → AccGrows lenv env tbl s s') ∧
  f ⊑ Erasure.visitCtorEta

/-- Motive 14 — `Erasure.visitCtorEtaGo`. -/
def MotiveAcc14 (f : Name → Nat → Expr → Expr → Array Expr → EraseM LBTerm) : Prop :=
  (∀ cn ar ty fe args s ctx cctx ref w t s' w',
    f cn ar ty fe args s ctx cctx ref w = .ok (t, s') w' →
    ∀ Us Δ, BridgeInv env Us tbl cfg (gw w) ctx s Δ →
      (∃ I k, CtorOf env cn I k) → ar ≤ args.size → ArgsOk env Us tbl Δ args →
      AccGrows lenv env tbl s s') ∧
  f ⊑ Erasure.visitCtorEtaGo

/-- Motive 15 — `Erasure.visitCasesEta`. -/
def MotiveAcc15 (f : Lean.CasesInfo → Expr → EraseM LBTerm) : Prop :=
  (∀ ci e s ctx cctx ref w t s' w', f ci e s ctx cctx ref w = .ok (t, s') w' →
    ∀ Us Δ con us I, BridgeInv env Us tbl cfg (gw w) ctx s Δ → e.getAppFn = .const con us →
      CasesHead env tbl ci con I → ci.arity ≤ e.getAppArgs.size →
      Supported env tbl e → ArgsOk env Us tbl Δ e.getAppArgs →
      (∃ ve, TrExprS env Us Δ e ve) → AccGrows lenv env tbl s s') ∧
  f ⊑ Erasure.visitCasesEta

/-- Motive 16 — `Erasure.visitCasesEtaGo`. -/
def MotiveAcc16 (f : Lean.CasesInfo → Expr → Expr → Array Expr → EraseM LBTerm) : Prop :=
  (∀ ci ty fe args s ctx cctx ref w t s' w', f ci ty fe args s ctx cctx ref w = .ok (t, s') w' →
    ∀ Us Δ con us I, BridgeInv env Us tbl cfg (gw w) ctx s Δ →
      CasesHead env tbl ci con I → ci.arity ≤ args.size →
      Supported env tbl (srcSpine (.const con us) args) → ArgsOk env Us tbl Δ args →
      (∃ ve, TrExprS env Us Δ (srcSpine (.const con us) args) ve) →
      AccGrows lenv env tbl s s') ∧
  f ⊑ Erasure.visitCasesEtaGo

/-- Motive 17 — `Erasure.visitCases`, one of the three members that register a block. -/
def MotiveAcc17 (f : Lean.CasesInfo → Array Expr → EraseM LBTerm) : Prop :=
  (∀ ci args s ctx cctx ref w t s' w', f ci args s ctx cctx ref w = .ok (t, s') w' →
    ∀ Us Δ con us I, BridgeInv env Us tbl cfg (gw w) ctx s Δ →
      CasesHead env tbl ci con I → ci.arity ≤ args.size →
      Supported env tbl (srcSpine (.const con us) args) → ArgsOk env Us tbl Δ args →
      (∃ ve, TrExprS env Us Δ (srcSpine (.const con us) args) ve) →
      AccGrows lenv env tbl s s') ∧
  f ⊑ Erasure.visitCases

/-- Motive 18 — `Erasure.visitAlt`. -/
def MotiveAcc18 (f : Nat → ConstructorArgMask → Expr → EraseM (List BinderName × LBTerm)) :
    Prop :=
  (∀ nf mask e s ctx cctx ref w r s' w', f nf mask e s ctx cctx ref w = .ok (r, s') w' →
    ∀ Us Δ, BridgeInv env Us tbl cfg (gw w) ctx s Δ → mask = Array.replicate nf .keep →
      IsLamTelescope nf e → Supported env tbl e → (∃ ve, TrExprS env Us Δ e ve) →
      AccGrows lenv env tbl s s') ∧
  f ⊑ Erasure.visitAlt

end Motives

/-! ## The bundle -/

/-- The eighteen accumulator motives at one eraser family. -/
structure MotivesAcc (lenv : Environment) (env : VEnv) (tbl : SourceTable)
    (cfg : ErasureConfig) (gw : Void IO.RealWorld → NameGenerator)
    (f₁ : Expr → EraseM LBTerm) (f₂ : Literal → EraseM LBTerm)
    (f₃ : Name → Array Expr → EraseM LBTerm) (f₄ : Expr → EraseM LBTerm)
    (f₅ : Name → EraseM Kername) (f₆ : Name → EraseM Unit)
    (f₇ : LBTerm → Array Expr → EraseM LBTerm) (f₈ f₉ : Expr → EraseM LBTerm)
    (f₁₀ : Name → Nat → Expr → EraseM LBTerm) (f₁₁ f₁₂ : Expr → EraseM LBTerm)
    (f₁₃ : Name → Nat → Expr → EraseM LBTerm)
    (f₁₄ : Name → Nat → Expr → Expr → Array Expr → EraseM LBTerm)
    (f₁₅ : Lean.CasesInfo → Expr → EraseM LBTerm)
    (f₁₆ : Lean.CasesInfo → Expr → Expr → Array Expr → EraseM LBTerm)
    (f₁₇ : Lean.CasesInfo → Array Expr → EraseM LBTerm)
    (f₁₈ : Nat → ConstructorArgMask → Expr → EraseM (List BinderName × LBTerm)) : Prop where
  /-- `Erasure.visitExpr`. -/
  motive1 : MotiveAcc1 lenv env tbl cfg gw f₁
  /-- `Erasure.visitLiteral`. -/
  motive2 : MotiveAcc2 lenv env tbl cfg gw f₂
  /-- `Erasure.visitConstructor`. -/
  motive3 : MotiveAcc3 lenv env tbl cfg gw f₃
  /-- `Erasure.visitConst`. -/
  motive4 : MotiveAcc4 lenv env tbl cfg gw f₄
  /-- `Erasure.get_constant_kername`. -/
  motive5 : MotiveAcc5 lenv env tbl cfg gw f₅
  /-- `Erasure.visitMutual`. -/
  motive6 : MotiveAcc6 lenv env tbl cfg gw f₆
  /-- `Erasure.visitAppArgs`. -/
  motive7 : MotiveAcc7 lenv env tbl cfg gw f₇
  /-- `Erasure.visitLet`. -/
  motive8 : MotiveAcc8 lenv env tbl cfg gw f₈
  /-- `Erasure.visitLambda`. -/
  motive9 : MotiveAcc9 lenv env tbl cfg gw f₉
  /-- `Erasure.visitProj`. -/
  motive10 : MotiveAcc10 lenv env tbl cfg gw f₁₀
  /-- `Erasure.visitApp`. -/
  motive11 : MotiveAcc11 lenv env tbl cfg gw f₁₁
  /-- `Erasure.visitConstApp`. -/
  motive12 : MotiveAcc12 lenv env tbl cfg gw f₁₂
  /-- `Erasure.visitCtorEta`. -/
  motive13 : MotiveAcc13 lenv env tbl cfg gw f₁₃
  /-- `Erasure.visitCtorEtaGo`. -/
  motive14 : MotiveAcc14 lenv env tbl cfg gw f₁₄
  /-- `Erasure.visitCasesEta`. -/
  motive15 : MotiveAcc15 lenv env tbl cfg gw f₁₅
  /-- `Erasure.visitCasesEtaGo`. -/
  motive16 : MotiveAcc16 lenv env tbl cfg gw f₁₆
  /-- `Erasure.visitCases`. -/
  motive17 : MotiveAcc17 lenv env tbl cfg gw f₁₇
  /-- `Erasure.visitAlt`. -/
  motive18 : MotiveAcc18 lenv env tbl cfg gw f₁₈

/-! ## The eighteen step interfaces

Each is the second induction's obligation at one member. The ambient premises are the first
bundle's, plus the asks the registering exits read (`AccAsks`), plus the first bundle's
conclusion at the shipping family.

That last premise is what a step reads a *sub-run's* state, registry and generator facts off:
`MotiveAccᵢ` concludes `AccGrows` alone, and a step that sequences two sub-runs needs
`BridgeInv` at the second one's entry state, which is `RunConcl`, `IndRegistryModelled` and
the generator bound at the first one's exit. Each is `RunRefines`' own, read at the shipping
member the approximation conjunct transports the sub-run to. `doc/rework/12-REPAIRS-W9.md`
§2.5 gives the premise to `StepAcc6` alone; it is here at every step because every step but
the four leaf ones has that sequencing, and it costs nothing — the two bundles stay separate
and T8's footprint is untouched.
-/

/-- The first bundle at the shipping family. -/
abbrev ShippingMotives (env : VEnv) (tbl : SourceTable) (cfg : ErasureConfig)
    (gw : Void IO.RealWorld → NameGenerator) : Prop :=
  Motives env tbl cfg gw
    Erasure.visitExpr Erasure.visitLiteral Erasure.visitConstructor Erasure.visitConst
    Erasure.get_constant_kername Erasure.visitMutual Erasure.visitAppArgs Erasure.visitLet
    Erasure.visitLambda Erasure.visitProj Erasure.visitApp Erasure.visitConstApp
    Erasure.visitCtorEta Erasure.visitCtorEtaGo Erasure.visitCasesEta Erasure.visitCasesEtaGo
    Erasure.visitCases Erasure.visitAlt

/-- The ambient premises every accumulator step is stated under: the first bundle's four, the
two asks, the safety column `Erasure.register_inductive`'s step spends at each member of a
block, the block-key freshness the specification environment owes at every registered block,
and the three table columns that close the realizer exits. -/
structure AccAsks (lenv : Environment) (env : VEnv) (tbl : SourceTable)
    (gw : Void IO.RealWorld → NameGenerator) : Prop where
  /-- The eraser's own obligations. -/
  eraser : EraserAsks lenv env gw
  /-- The upstream model's. -/
  upstream : UpstreamAsks env
  /-- Every tabled head's compiler declaration is safe and is no `_unsafe_rec` companion. -/
  safe : TableSafe lenv tbl
  /-- The table's blocks. -/
  blocks : TableBlocks lenv env tbl
  /-- Every declared inductive is safe, which is what `propositionalInd_of_arity` spends at a
      block's members. -/
  indSafe : ∀ (I : Name) (iv : InductiveVal), lenv.find? I = some (.inductInfo iv) →
    DefinitionSafety.safe ≤ (ConstantInfo.inductInfo iv).safety
  /-- No tabled body's key collides with a block's or an eliminator's. -/
  fresh : ∀ indinfo : InductiveVal, BodiedKeysFresh env tbl.body? indinfo
  /-- Lean's quotient and recursor name schemes. -/
  scheme : SchemeNames lenv
  /-- A tabled recursor's inductive type is tabled. -/
  recPrefixed : TableRecPrefixed tbl

section Steps

variable (lenv : Environment) (env : VEnv) (tbl : SourceTable) (cfg : ErasureConfig)
  (gw : Void IO.RealWorld → NameGenerator)

/-- Step 1 — the obligation at `Erasure.visitExpr`. -/
abbrev StepAcc1 : Prop :=
  (∀ Us, ErasureSpec lenv env Us gw) → AccAsks lenv env tbl gw →
  SourceTableAdequate lenv tbl → ConfigPinned cfg → CompilerBodies lenv env tbl.body? →
  ShippingMotives env tbl cfg gw →
  ∀ (vExpr : Expr → EraseM LBTerm) (vLit : Literal → EraseM LBTerm) (vLet : Expr → EraseM LBTerm)
    (vLam : Expr → EraseM LBTerm) (vProj : Name → Nat → Expr → EraseM LBTerm)
    (vApp : Expr → EraseM LBTerm),
    MotiveAcc1 lenv env tbl cfg gw vExpr →
    MotiveAcc2 lenv env tbl cfg gw vLit →
    MotiveAcc8 lenv env tbl cfg gw vLet →
    MotiveAcc9 lenv env tbl cfg gw vLam →
    MotiveAcc10 lenv env tbl cfg gw vProj →
    MotiveAcc11 lenv env tbl cfg gw vApp →
    MotiveAcc1 lenv env tbl cfg gw (visitExprBody vExpr vLit vLet vLam vProj vApp)

/-- Step 2 — the obligation at `Erasure.visitLiteral`. -/
abbrev StepAcc2 : Prop :=
  (∀ Us, ErasureSpec lenv env Us gw) → AccAsks lenv env tbl gw →
  SourceTableAdequate lenv tbl → ConfigPinned cfg → CompilerBodies lenv env tbl.body? →
  ShippingMotives env tbl cfg gw →
  ∀ (vCtor : Name → Array Expr → EraseM LBTerm),
    MotiveAcc3 lenv env tbl cfg gw vCtor →
    MotiveAcc2 lenv env tbl cfg gw (visitLiteralBody vCtor)

/-- Step 3 — the obligation at `Erasure.visitConstructor`. -/
abbrev StepAcc3 : Prop :=
  (∀ Us, ErasureSpec lenv env Us gw) → AccAsks lenv env tbl gw →
  SourceTableAdequate lenv tbl → ConfigPinned cfg → CompilerBodies lenv env tbl.body? →
  ShippingMotives env tbl cfg gw →
  ∀ (vLit : Literal → EraseM LBTerm) (vConst : Expr → EraseM LBTerm)
    (vArgs : LBTerm → Array Expr → EraseM LBTerm),
    MotiveAcc2 lenv env tbl cfg gw vLit →
    MotiveAcc4 lenv env tbl cfg gw vConst →
    MotiveAcc7 lenv env tbl cfg gw vArgs →
    MotiveAcc3 lenv env tbl cfg gw (visitConstructorBody vLit vConst vArgs)

/-- Step 4 — the obligation at `Erasure.visitConst`. -/
abbrev StepAcc4 : Prop :=
  (∀ Us, ErasureSpec lenv env Us gw) → AccAsks lenv env tbl gw →
  SourceTableAdequate lenv tbl → ConfigPinned cfg → CompilerBodies lenv env tbl.body? →
  ShippingMotives env tbl cfg gw →
  ∀ (vGck : Name → EraseM Kername),
    MotiveAcc5 lenv env tbl cfg gw vGck →
    MotiveAcc4 lenv env tbl cfg gw (visitConstBody vGck)

/-- Step 5 — the obligation at `Erasure.get_constant_kername`. -/
abbrev StepAcc5 : Prop :=
  (∀ Us, ErasureSpec lenv env Us gw) → AccAsks lenv env tbl gw →
  SourceTableAdequate lenv tbl → ConfigPinned cfg → CompilerBodies lenv env tbl.body? →
  ShippingMotives env tbl cfg gw →
  ∀ (vMut : Name → EraseM Unit),
    MotiveAcc6 lenv env tbl cfg gw vMut →
    MotiveAcc5 lenv env tbl cfg gw (getConstantKernameBody vMut)

/-- Step 6 — the obligation at `Erasure.visitMutual`, the one step that reads the first
bundle: its two term exits register the erasure of a member body, and the witness is
`Motive1`'s at the shipping `Erasure.visitExpr`. -/
abbrev StepAcc6 : Prop :=
  (∀ Us, ErasureSpec lenv env Us gw) → AccAsks lenv env tbl gw →
  SourceTableAdequate lenv tbl → ConfigPinned cfg → CompilerBodies lenv env tbl.body? →
  ShippingMotives env tbl cfg gw →
  ∀ (vExpr : Expr → EraseM LBTerm),
    MotiveAcc1 lenv env tbl cfg gw vExpr →
    MotiveAcc6 lenv env tbl cfg gw (visitMutualBody vExpr)

/-- Step 7 — the obligation at `Erasure.visitAppArgs`. -/
abbrev StepAcc7 : Prop :=
  (∀ Us, ErasureSpec lenv env Us gw) → AccAsks lenv env tbl gw →
  SourceTableAdequate lenv tbl → ConfigPinned cfg → CompilerBodies lenv env tbl.body? →
  ShippingMotives env tbl cfg gw →
  ∀ (vExpr : Expr → EraseM LBTerm),
    MotiveAcc1 lenv env tbl cfg gw vExpr →
    MotiveAcc7 lenv env tbl cfg gw (visitAppArgsBody vExpr)

/-- Step 8 — the obligation at `Erasure.visitLet`. -/
abbrev StepAcc8 : Prop :=
  (∀ Us, ErasureSpec lenv env Us gw) → AccAsks lenv env tbl gw →
  SourceTableAdequate lenv tbl → ConfigPinned cfg → CompilerBodies lenv env tbl.body? →
  ShippingMotives env tbl cfg gw →
  ∀ (vExpr : Expr → EraseM LBTerm),
    MotiveAcc1 lenv env tbl cfg gw vExpr →
    MotiveAcc8 lenv env tbl cfg gw (visitLetBody vExpr)

/-- Step 9 — the obligation at `Erasure.visitLambda`. -/
abbrev StepAcc9 : Prop :=
  (∀ Us, ErasureSpec lenv env Us gw) → AccAsks lenv env tbl gw →
  SourceTableAdequate lenv tbl → ConfigPinned cfg → CompilerBodies lenv env tbl.body? →
  ShippingMotives env tbl cfg gw →
  ∀ (vExpr : Expr → EraseM LBTerm),
    MotiveAcc1 lenv env tbl cfg gw vExpr →
    MotiveAcc9 lenv env tbl cfg gw (visitLambdaBody vExpr)

/-- Step 10 — the obligation at `Erasure.visitProj`. -/
abbrev StepAcc10 : Prop :=
  (∀ Us, ErasureSpec lenv env Us gw) → AccAsks lenv env tbl gw →
  SourceTableAdequate lenv tbl → ConfigPinned cfg → CompilerBodies lenv env tbl.body? →
  ShippingMotives env tbl cfg gw →
  ∀ (vExpr : Expr → EraseM LBTerm),
    MotiveAcc1 lenv env tbl cfg gw vExpr →
    MotiveAcc10 lenv env tbl cfg gw (visitProjBody vExpr)

/-- Step 11 — the obligation at `Erasure.visitApp`. -/
abbrev StepAcc11 : Prop :=
  (∀ Us, ErasureSpec lenv env Us gw) → AccAsks lenv env tbl gw →
  SourceTableAdequate lenv tbl → ConfigPinned cfg → CompilerBodies lenv env tbl.body? →
  ShippingMotives env tbl cfg gw →
  ∀ (vExpr : Expr → EraseM LBTerm) (vArgs : LBTerm → Array Expr → EraseM LBTerm)
    (vConstApp : Expr → EraseM LBTerm),
    MotiveAcc1 lenv env tbl cfg gw vExpr →
    MotiveAcc7 lenv env tbl cfg gw vArgs →
    MotiveAcc12 lenv env tbl cfg gw vConstApp →
    MotiveAcc11 lenv env tbl cfg gw (visitAppBody vExpr vArgs vConstApp)

/-- Step 12 — the obligation at `Erasure.visitConstApp`. -/
abbrev StepAcc12 : Prop :=
  (∀ Us, ErasureSpec lenv env Us gw) → AccAsks lenv env tbl gw →
  SourceTableAdequate lenv tbl → ConfigPinned cfg → CompilerBodies lenv env tbl.body? →
  ShippingMotives env tbl cfg gw →
  ∀ (vConst : Expr → EraseM LBTerm) (vArgs : LBTerm → Array Expr → EraseM LBTerm)
    (vCtorEta : Name → Nat → Expr → EraseM LBTerm)
    (vCasesEta : CasesInfo → Expr → EraseM LBTerm),
    MotiveAcc4 lenv env tbl cfg gw vConst →
    MotiveAcc7 lenv env tbl cfg gw vArgs →
    MotiveAcc13 lenv env tbl cfg gw vCtorEta →
    MotiveAcc15 lenv env tbl cfg gw vCasesEta →
    MotiveAcc12 lenv env tbl cfg gw (visitConstAppBody vConst vArgs vCtorEta vCasesEta)

/-- Step 13 — the obligation at `Erasure.visitCtorEta`. -/
abbrev StepAcc13 : Prop :=
  (∀ Us, ErasureSpec lenv env Us gw) → AccAsks lenv env tbl gw →
  SourceTableAdequate lenv tbl → ConfigPinned cfg → CompilerBodies lenv env tbl.body? →
  ShippingMotives env tbl cfg gw →
  ∀ (vCtorEtaGo : Name → Nat → Expr → Expr → Array Expr → EraseM LBTerm),
    MotiveAcc14 lenv env tbl cfg gw vCtorEtaGo →
    MotiveAcc13 lenv env tbl cfg gw (visitCtorEtaBody vCtorEtaGo)

/-- Step 14 — the obligation at `Erasure.visitCtorEtaGo`. -/
abbrev StepAcc14 : Prop :=
  (∀ Us, ErasureSpec lenv env Us gw) → AccAsks lenv env tbl gw →
  SourceTableAdequate lenv tbl → ConfigPinned cfg → CompilerBodies lenv env tbl.body? →
  ShippingMotives env tbl cfg gw →
  ∀ (vExpr : Expr → EraseM LBTerm) (vCtor : Name → Array Expr → EraseM LBTerm)
    (vCtorEtaGo : Name → Nat → Expr → Expr → Array Expr → EraseM LBTerm),
    MotiveAcc1 lenv env tbl cfg gw vExpr →
    MotiveAcc3 lenv env tbl cfg gw vCtor →
    MotiveAcc14 lenv env tbl cfg gw vCtorEtaGo →
    MotiveAcc14 lenv env tbl cfg gw (visitCtorEtaGoBody vExpr vCtor vCtorEtaGo)

/-- Step 15 — the obligation at `Erasure.visitCasesEta`. -/
abbrev StepAcc15 : Prop :=
  (∀ Us, ErasureSpec lenv env Us gw) → AccAsks lenv env tbl gw →
  SourceTableAdequate lenv tbl → ConfigPinned cfg → CompilerBodies lenv env tbl.body? →
  ShippingMotives env tbl cfg gw →
  ∀ (vCasesEtaGo : CasesInfo → Expr → Expr → Array Expr → EraseM LBTerm),
    MotiveAcc16 lenv env tbl cfg gw vCasesEtaGo →
    MotiveAcc15 lenv env tbl cfg gw (visitCasesEtaBody vCasesEtaGo)

/-- Step 16 — the obligation at `Erasure.visitCasesEtaGo`. -/
abbrev StepAcc16 : Prop :=
  (∀ Us, ErasureSpec lenv env Us gw) → AccAsks lenv env tbl gw →
  SourceTableAdequate lenv tbl → ConfigPinned cfg → CompilerBodies lenv env tbl.body? →
  ShippingMotives env tbl cfg gw →
  ∀ (vExpr : Expr → EraseM LBTerm)
    (vCasesEtaGo : CasesInfo → Expr → Expr → Array Expr → EraseM LBTerm)
    (vCases : CasesInfo → Array Expr → EraseM LBTerm),
    MotiveAcc1 lenv env tbl cfg gw vExpr →
    MotiveAcc16 lenv env tbl cfg gw vCasesEtaGo →
    MotiveAcc17 lenv env tbl cfg gw vCases →
    MotiveAcc16 lenv env tbl cfg gw (visitCasesEtaGoBody vExpr vCasesEtaGo vCases)

/-- Step 17 — the obligation at `Erasure.visitCases`. -/
abbrev StepAcc17 : Prop :=
  (∀ Us, ErasureSpec lenv env Us gw) → AccAsks lenv env tbl gw →
  SourceTableAdequate lenv tbl → ConfigPinned cfg → CompilerBodies lenv env tbl.body? →
  ShippingMotives env tbl cfg gw →
  ∀ (vExpr : Expr → EraseM LBTerm)
    (vAlt : Nat → ConstructorArgMask → Expr → EraseM (List BinderName × LBTerm)),
    MotiveAcc1 lenv env tbl cfg gw vExpr →
    MotiveAcc18 lenv env tbl cfg gw vAlt →
    MotiveAcc17 lenv env tbl cfg gw (visitCasesBody vExpr vAlt)

/-- Step 18 — the obligation at `Erasure.visitAlt`. -/
abbrev StepAcc18 : Prop :=
  (∀ Us, ErasureSpec lenv env Us gw) → AccAsks lenv env tbl gw →
  SourceTableAdequate lenv tbl → ConfigPinned cfg → CompilerBodies lenv env tbl.body? →
  ShippingMotives env tbl cfg gw →
  ∀ (vExpr : Expr → EraseM LBTerm),
    MotiveAcc1 lenv env tbl cfg gw vExpr →
    MotiveAcc18 lenv env tbl cfg gw (visitAltBody vExpr)

end Steps

end LeanToLambdaBox
