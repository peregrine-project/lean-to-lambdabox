import LeanToLambdaBox.Bridge
import LeanToLambdaBox.ErasesCorrect.Steps

/-!
# The eighteen motives of the bridge induction

`Erasure.visitExpr` is one member of an eighteen-function `partial_fixpoint` family, so the
bridge is proved by fixpoint induction with one motive per member. This module states the
eighteen motives, the bundle `Motives` of all of them at the shipping family — which is the
induction's conclusion — and the eighteen step interfaces `Step1`–`Step18`, each stating "given
the motives of the members this one calls, the motive holds of its body".

Every motive is a conjunction: the refinement statement, and `f ⊑ Erasure.visitXxx`, the
approximation in `partial_fixpoint`'s own order. The second conjunct is a tautology at the
fixpoint and is what lets a step speak about *the* block the shipping eraser builds rather than
about whichever one an arbitrary point of the CCPO happens to produce.

Each `Stepᵢ` names the abstract body of one member: the shipping definition with its recursive
calls replaced by the induction's abstract functions. Elaborating the body here is what makes
the step provable in a file of its own — the induction's own step goal is that statement, and
the aggregator discharges it by `exact`.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean Erasure Witness Lean.Order

-- The approximation conjunct is `⊑` on a five-argument member of the erasure family, whose
-- `PartialOrder` instance is five transformer layers deep under five binders.
set_option synthInstance.maxSize 4000

/-! ## The shared conclusions -/

/-- What a successful sub-run of a term-producing member concludes: the state grew canonically,
the inductive registry is still the model's, the generator only advanced, and at every
specification environment of the final state the emitted term is the source term's image in the
reader's fixvar mode. -/
def RunRefines (env : VEnv) (Us : List Name) (tbl : SourceTable) (ctx : ErasureContext)
    (Δ : VLCtx) (s s' : ErasureState) (gen gen' : NameGenerator) (e : Expr) (t : LBTerm) : Prop :=
  RunConcl s s' ∧ IndRegistryModelled env s' ∧ gen ≤ gen' ∧
    ∀ Γspec, SpecEnv env tbl.body? tbl.levels? s' Γspec → ErasesLBMode tbl ctx env Us Γspec Δ e t

/-- `RunRefines` for `Erasure.visitAlt`, whose result is a `case` alternative rather than a
term. -/
def RunRefinesAlt (env : VEnv) (Us : List Name) (tbl : SourceTable) (ctx : ErasureContext)
    (Δ : VLCtx) (s s' : ErasureState) (gen gen' : NameGenerator) (nf : Nat) (m : Expr)
    (alt : List BinderName × LBTerm) : Prop :=
  RunConcl s s' ∧ IndRegistryModelled env s' ∧ gen ≤ gen' ∧
    ∀ Γspec, SpecEnv env tbl.body? tbl.levels? s' Γspec →
      ErasesLBAltMode tbl ctx env Us Γspec Δ nf m alt

/-- The head premise of `Erasure.visitAppArgs`' motive, read at the *initial* state: the caller
holds the head's refinement there, and `SpecEnv.mono` re-reads a final-state environment at it. -/
def HeadRefines (env : VEnv) (Us : List Name) (tbl : SourceTable) (ctx : ErasureContext)
    (Δ : VLCtx) (s : ErasureState) (e : Expr) (t : LBTerm) : Prop :=
  ∀ Γspec, SpecEnv env tbl.body? tbl.levels? s Γspec → ErasesLBMode tbl ctx env Us Γspec Δ e t

/-- The fragment and translation conditions on the arguments of a spine, at the array the run
carries them in. -/
def ArgsOk (env : VEnv) (Us : List Name) (tbl : SourceTable) (Δ : VLCtx)
    (args : Array Expr) : Prop :=
  ∀ (i : Nat) (hi : i < args.size),
    Supported env tbl args[i] ∧ ∃ ve, TrExprS env Us Δ args[i] ve

/-- The source spine a run over `args` at head `hd` is about. -/
def srcSpine (hd : Expr) (args : Array Expr) : Expr := args.toList.foldl Expr.app hd

/-! ## The `casesOn` head the run dispatches on -/

/-- The `casesOn` head data a `casesOn`-eliminating motive reads: the fragment's own conditions
on the head, and the run's agreement with the table. -/
structure CasesHead (env : VEnv) (tbl : SourceTable) (ci : Lean.CasesInfo) (con : Name)
    (I : ReifiedInduct) : Prop where
  /-- The head is not one of the four excluded name classes. -/
  plain : PlainHead con
  /-- The head is a `casesOn` constant. -/
  cases : isCasesOnName con = true
  /-- Its inductive type is tabled, at the name the erasure recovers from the head's prefix. -/
  ind : tbl.ind? con.getPrefix = some I
  /-- Its inductive type is informative, without which the emitted `.case` is stuck. -/
  informative : InformativeInd env con.getPrefix
  /-- The elaborator's own metadata agrees with the table's. -/
  agrees : CasesInfoAgrees ci con I

/-! ## The eighteen motives -/

section Motives

variable (env : VEnv) (Us : List Name) (tbl : SourceTable) (cfg : ErasureConfig)
  (gw : Void IO.RealWorld → NameGenerator)

/-- Motive 1 — `Erasure.visitExpr`: a supported, translatable term erases to a term of the
composite, in whichever fixvar mode the reader is in. -/
def Motive1 (f : Expr → EraseM LBTerm) : Prop :=
  (∀ e s ctx cctx ref w t s' w', f e s ctx cctx ref w = .ok (t, s') w' →
    ∀ Δ, BridgeInv env Us tbl cfg (gw w) ctx s Δ → Supported env tbl e →
      (∃ ve, TrExprS env Us Δ e ve) →
      RunRefines env Us tbl ctx Δ s s' (gw w) (gw w') e t) ∧
  f ⊑ Erasure.visitExpr

/-- Motive 2 — `Erasure.visitLiteral`: a `Nat` literal erases to its peano tower. The premises
beyond the invariant are the fragment's own `natLit` rule and the verdict at the literal, whose
kername clause the recursive constructor call needs. -/
def Motive2 (f : Literal → EraseM LBTerm) : Prop :=
  (∀ l s ctx cctx ref w t s' w', f l s ctx cctx ref w = .ok (t, s') w' →
    ∀ Δ n, BridgeInv env Us tbl cfg (gw w) ctx s Δ → l = .natVal n →
      PeanoReady env → peanoReadyB tbl = true → Supported env tbl (.lit l) →
      (∃ ve, TrExprS env Us Δ (.lit l) ve) →
      RunRefines env Us tbl ctx Δ s s' (gw w) (gw w') (.lit l) t) ∧
  f ⊑ Erasure.visitLiteral

/-- Motive 3 — `Erasure.visitConstructor`: a constructor applied to a supported argument array
erases to the applied constructor node. -/
def Motive3 (f : Name → Array Expr → EraseM LBTerm) : Prop :=
  (∀ cn args s ctx cctx ref w t s' w', f cn args s ctx cctx ref w = .ok (t, s') w' →
    ∀ Δ (us : List Level), BridgeInv env Us tbl cfg (gw w) ctx s Δ →
      (∃ I k, CtorOf env cn I k) → ArgsOk env Us tbl Δ args →
      RunRefines env Us tbl ctx Δ s s' (gw w) (gw w') (srcSpine (.const cn us) args) t) ∧
  f ⊑ Erasure.visitConstructor

/-- Motive 4 — `Erasure.visitConst`: a plain known constant becomes its kername, or, inside a
mutual block that defines it, that member's fix variable. The two exclusions are what
`Erases.const` needs and `KnownHead` does not settle: `KnownHead` has a constructor column and
a type-former column, and the run emits a `.const` node, which no rule of the composite relates
to either head. Both are read off the run at the call sites — the constructor column from
`Erasure.visitConstApp`'s `Lean.Compiler.LCNF.getCtorArity?` miss, the type-former column from
the relevance oracle's `false` verdict through `EraserAsks.oracle_informative`. -/
def Motive4 (f : Expr → EraseM LBTerm) : Prop :=
  (∀ e s ctx cctx ref w t s' w', f e s ctx cctx ref w = .ok (t, s') w' →
    ∀ Δ n us, BridgeInv env Us tbl cfg (gw w) ctx s Δ → e = .const n us →
      PlainHead n → isCasesOnName n = false → KnownHead env tbl n → Supported env tbl e →
      (∀ (I : Name) (k : Nat), ¬ CtorOf env n I k) →
      (∀ (iid : InductiveId) (np : Nat) (nfs : List Nat), ¬ IndInfo env n iid np nfs) →
      RunRefines env Us tbl ctx Δ s s' (gw w) (gw w') e t) ∧
  f ⊑ Erasure.visitConst

/-- Motive 5 — `Erasure.get_constant_kername`: the kername returned is the canonical one, and
the constant is registered afterwards. The name is in the table's constant column, which is
where `Erasure.visitConst` has already put it and what the registration below needs to know the
name is not an `_unsafe_rec` companion. -/
def Motive5 (f : Name → EraseM Kername) : Prop :=
  (∀ n s ctx cctx ref w kn s' w', f n s ctx cctx ref w = .ok (kn, s') w' →
    ∀ Δ, BridgeInv env Us tbl cfg (gw w) ctx s Δ → Supported env tbl (.const n []) →
      (tbl.decl? n).isSome →
      kn = toKername n ∧ (s'.constants.get? n).isSome ∧
        RunConcl s s' ∧ IndRegistryModelled env s' ∧ gw w ≤ gw w') ∧
  f ⊑ Erasure.get_constant_kername

/-- Motive 6 — `Erasure.visitMutual`: the declaration is registered. Its two branches erase the
member bodies, the block branch under the reader that carries the block's fix variables, which
is where the sub-runs conclude `ErasesLBFix` rather than `ErasesLB`; the content of what is
registered is read off the final state by `SpecEnv`, not concluded here. -/
def Motive6 (f : Name → EraseM Unit) : Prop :=
  (∀ n s ctx cctx ref w u s' w', f n s ctx cctx ref w = .ok (u, s') w' →
    ∀ Δ, BridgeInv env Us tbl cfg (gw w) ctx s Δ → Supported env tbl (.const n []) →
      (tbl.decl? n).isSome →
      (s'.constants.get? n).isSome ∧ RunConcl s s' ∧ IndRegistryModelled env s' ∧
        gw w ≤ gw w') ∧
  f ⊑ Erasure.visitMutual

/-- Motive 7 — `Erasure.visitAppArgs`: a head already related to a source term, applied to a
supported argument array, is the spine. -/
def Motive7 (f : LBTerm → Array Expr → EraseM LBTerm) : Prop :=
  (∀ hd args s ctx cctx ref w t s' w', f hd args s ctx cctx ref w = .ok (t, s') w' →
    ∀ Δ (e : Expr), BridgeInv env Us tbl cfg (gw w) ctx s Δ →
      HeadRefines env Us tbl ctx Δ s e hd → ArgsOk env Us tbl Δ args →
      RunRefines env Us tbl ctx Δ s s' (gw w) (gw w') (srcSpine e args) t) ∧
  f ⊑ Erasure.visitAppArgs

/-- Motive 8 — `Erasure.visitLet`. -/
def Motive8 (f : Expr → EraseM LBTerm) : Prop :=
  (∀ e s ctx cctx ref w t s' w', f e s ctx cctx ref w = .ok (t, s') w' →
    ∀ Δ n ty v b nd, BridgeInv env Us tbl cfg (gw w) ctx s Δ → e = .letE n ty v b nd →
      Supported env tbl e → (∃ ve, TrExprS env Us Δ e ve) →
      RunRefines env Us tbl ctx Δ s s' (gw w) (gw w') e t) ∧
  f ⊑ Erasure.visitLet

/-- Motive 9 — `Erasure.visitLambda`. -/
def Motive9 (f : Expr → EraseM LBTerm) : Prop :=
  (∀ e s ctx cctx ref w t s' w', f e s ctx cctx ref w = .ok (t, s') w' →
    ∀ Δ n ty b bi, BridgeInv env Us tbl cfg (gw w) ctx s Δ → e = .lam n ty b bi →
      Supported env tbl e → (∃ ve, TrExprS env Us Δ e ve) →
      RunRefines env Us tbl ctx Δ s s' (gw w) (gw w') e t) ∧
  f ⊑ Erasure.visitLambda

/-- Motive 10 — `Erasure.visitProj`: a projection of a tabled, informative structure. -/
def Motive10 (f : Name → Nat → Expr → EraseM LBTerm) : Prop :=
  (∀ tn i e s ctx cctx ref w t s' w', f tn i e s ctx cctx ref w = .ok (t, s') w' →
    ∀ Δ (I : ReifiedInduct) (np nf : Nat), BridgeInv env Us tbl cfg (gw w) ctx s Δ →
      tbl.ind? tn = some I → InformativeInd env tn → IndArity env tn np [nf] → i < nf →
      Supported env tbl e → (∃ ve, TrExprS env Us Δ e ve) →
      RunRefines env Us tbl ctx Δ s s' (gw w) (gw w') (.proj tn i e) t) ∧
  f ⊑ Erasure.visitProj

/-- Motive 11 — `Erasure.visitApp`, the spine dispatcher. The head exclusion travels with the
subject: `Erasure.visitExpr` reaches this member only past a `false` relevance verdict, which
by `EraserAsks.oracle_informative` rules out a type former at the spine's head, and the
constant arm below spends it at `Motive4`. -/
def Motive11 (f : Expr → EraseM LBTerm) : Prop :=
  (∀ e s ctx cctx ref w t s' w', f e s ctx cctx ref w = .ok (t, s') w' →
    ∀ Δ, BridgeInv env Us tbl cfg (gw w) ctx s Δ → Supported env tbl e →
      (∃ ve, TrExprS env Us Δ e ve) →
      (∀ (c : Name) (us : List Level), e.getAppFn = .const c us →
        ∀ (iid : InductiveId) (np : Nat) (nfs : List Nat), ¬ IndInfo env c iid np nfs) →
      RunRefines env Us tbl ctx Δ s s' (gw w) (gw w') e t) ∧
  f ⊑ Erasure.visitApp

/-- Motive 12 — `Erasure.visitConstApp`, the constant-headed spine. The head is not a type
former: the exclusion is `Motive11`'s, read at the head this member has already matched. -/
def Motive12 (f : Expr → EraseM LBTerm) : Prop :=
  (∀ e s ctx cctx ref w t s' w', f e s ctx cctx ref w = .ok (t, s') w' →
    ∀ Δ cn us, BridgeInv env Us tbl cfg (gw w) ctx s Δ → e.getAppFn = .const cn us →
      Supported env tbl e → (∃ ve, TrExprS env Us Δ e ve) →
      (∀ (iid : InductiveId) (np : Nat) (nfs : List Nat), ¬ IndInfo env cn iid np nfs) →
      RunRefines env Us tbl ctx Δ s s' (gw w) (gw w') e t) ∧
  f ⊑ Erasure.visitConstApp

/-- Motive 13 — `Erasure.visitCtorEta`, entered at a saturated constructor spine. -/
def Motive13 (f : Name → Nat → Expr → EraseM LBTerm) : Prop :=
  (∀ cn ar e s ctx cctx ref w t s' w', f cn ar e s ctx cctx ref w = .ok (t, s') w' →
    ∀ Δ us, BridgeInv env Us tbl cfg (gw w) ctx s Δ → e.getAppFn = .const cn us →
      (∃ I k, CtorOf env cn I k) → ar ≤ e.getAppArgs.size →
      ArgsOk env Us tbl Δ e.getAppArgs →
      RunRefines env Us tbl ctx Δ s s' (gw w) (gw w') e t) ∧
  f ⊑ Erasure.visitCtorEta

/-- Motive 14 — `Erasure.visitCtorEtaGo`, its saturated loop. -/
def Motive14 (f : Name → Nat → Expr → Expr → Array Expr → EraseM LBTerm) : Prop :=
  (∀ cn ar ty fe args s ctx cctx ref w t s' w',
    f cn ar ty fe args s ctx cctx ref w = .ok (t, s') w' →
    ∀ Δ us, BridgeInv env Us tbl cfg (gw w) ctx s Δ →
      (∃ I k, CtorOf env cn I k) → ar ≤ args.size → ArgsOk env Us tbl Δ args →
      RunRefines env Us tbl ctx Δ s s' (gw w) (gw w') (srcSpine (.const cn us) args) t) ∧
  f ⊑ Erasure.visitCtorEtaGo

/-- Motive 15 — `Erasure.visitCasesEta`, entered at a saturated `casesOn` spine. -/
def Motive15 (f : Lean.CasesInfo → Expr → EraseM LBTerm) : Prop :=
  (∀ ci e s ctx cctx ref w t s' w', f ci e s ctx cctx ref w = .ok (t, s') w' →
    ∀ Δ con us I, BridgeInv env Us tbl cfg (gw w) ctx s Δ → e.getAppFn = .const con us →
      CasesHead env tbl ci con I → ci.arity ≤ e.getAppArgs.size →
      Supported env tbl e → ArgsOk env Us tbl Δ e.getAppArgs →
      (∃ ve, TrExprS env Us Δ e ve) →
      RunRefines env Us tbl ctx Δ s s' (gw w) (gw w') e t) ∧
  f ⊑ Erasure.visitCasesEta

/-- Motive 16 — `Erasure.visitCasesEtaGo`, its saturated loop. -/
def Motive16 (f : Lean.CasesInfo → Expr → Expr → Array Expr → EraseM LBTerm) : Prop :=
  (∀ ci ty fe args s ctx cctx ref w t s' w', f ci ty fe args s ctx cctx ref w = .ok (t, s') w' →
    ∀ Δ con us I, BridgeInv env Us tbl cfg (gw w) ctx s Δ →
      CasesHead env tbl ci con I → ci.arity ≤ args.size →
      Supported env tbl (srcSpine (.const con us) args) → ArgsOk env Us tbl Δ args →
      (∃ ve, TrExprS env Us Δ (srcSpine (.const con us) args) ve) →
      RunRefines env Us tbl ctx Δ s s' (gw w) (gw w') (srcSpine (.const con us) args) t) ∧
  f ⊑ Erasure.visitCasesEtaGo

/-- Motive 17 — `Erasure.visitCases`, the `case` node itself. -/
def Motive17 (f : Lean.CasesInfo → Array Expr → EraseM LBTerm) : Prop :=
  (∀ ci args s ctx cctx ref w t s' w', f ci args s ctx cctx ref w = .ok (t, s') w' →
    ∀ Δ con us I, BridgeInv env Us tbl cfg (gw w) ctx s Δ →
      CasesHead env tbl ci con I → ci.arity ≤ args.size →
      Supported env tbl (srcSpine (.const con us) args) → ArgsOk env Us tbl Δ args →
      (∃ ve, TrExprS env Us Δ (srcSpine (.const con us) args) ve) →
      RunRefines env Us tbl ctx Δ s s' (gw w) (gw w') (srcSpine (.const con us) args) t) ∧
  f ⊑ Erasure.visitCases

/-- Motive 18 — `Erasure.visitAlt`: a minor premise that is a manifest λ-telescope becomes an
alternative with that many binders. -/
def Motive18 (f : Nat → ConstructorArgMask → Expr → EraseM (List BinderName × LBTerm)) : Prop :=
  (∀ nf mask e s ctx cctx ref w r s' w', f nf mask e s ctx cctx ref w = .ok (r, s') w' →
    ∀ Δ, BridgeInv env Us tbl cfg (gw w) ctx s Δ → mask = Array.replicate nf .keep →
      IsLamTelescope nf e → Supported env tbl e → (∃ ve, TrExprS env Us Δ e ve) →
      RunRefinesAlt env Us tbl ctx Δ s s' (gw w) (gw w') nf e r) ∧
  f ⊑ Erasure.visitAlt

end Motives

/-! ## The bundle -/

/-- The eighteen motives at one eraser family. Read at the shipping family it is the bridge
induction's conclusion; read at an abstract one it is what a step lemma is given. -/
structure Motives (env : VEnv) (Us : List Name) (tbl : SourceTable) (cfg : ErasureConfig)
    (gw : Void IO.RealWorld → NameGenerator)
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
  motive1 : Motive1 env Us tbl cfg gw f₁
  /-- `Erasure.visitLiteral`. -/
  motive2 : Motive2 env Us tbl cfg gw f₂
  /-- `Erasure.visitConstructor`. -/
  motive3 : Motive3 env Us tbl cfg gw f₃
  /-- `Erasure.visitConst`. -/
  motive4 : Motive4 env Us tbl cfg gw f₄
  /-- `Erasure.get_constant_kername`. -/
  motive5 : Motive5 env Us tbl cfg gw f₅
  /-- `Erasure.visitMutual`. -/
  motive6 : Motive6 env Us tbl cfg gw f₆
  /-- `Erasure.visitAppArgs`. -/
  motive7 : Motive7 env Us tbl cfg gw f₇
  /-- `Erasure.visitLet`. -/
  motive8 : Motive8 env Us tbl cfg gw f₈
  /-- `Erasure.visitLambda`. -/
  motive9 : Motive9 env Us tbl cfg gw f₉
  /-- `Erasure.visitProj`. -/
  motive10 : Motive10 env Us tbl cfg gw f₁₀
  /-- `Erasure.visitApp`. -/
  motive11 : Motive11 env Us tbl cfg gw f₁₁
  /-- `Erasure.visitConstApp`. -/
  motive12 : Motive12 env Us tbl cfg gw f₁₂
  /-- `Erasure.visitCtorEta`. -/
  motive13 : Motive13 env Us tbl cfg gw f₁₃
  /-- `Erasure.visitCtorEtaGo`. -/
  motive14 : Motive14 env Us tbl cfg gw f₁₄
  /-- `Erasure.visitCasesEta`. -/
  motive15 : Motive15 env Us tbl cfg gw f₁₅
  /-- `Erasure.visitCasesEtaGo`. -/
  motive16 : Motive16 env Us tbl cfg gw f₁₆
  /-- `Erasure.visitCases`. -/
  motive17 : Motive17 env Us tbl cfg gw f₁₇
  /-- `Erasure.visitAlt`. -/
  motive18 : Motive18 env Us tbl cfg gw f₁₈

/-! ## The abstract bodies

Each member's body, with its calls into the family replaced by parameters. These are the
`partial_fixpoint` step goals of `Erasure.visitExpr.mutual_fixpoint_induct`, named so that a
step lemma can be stated — and proved — in a file that does not carry the induction.
-/

/-- The abstract body of `Erasure.visitExpr`: the shipping definition, with its calls into the
erasure family replaced by the induction's own functions. -/
def visitExprBody (vExpr : Expr → EraseM LBTerm) (vLit : Literal → EraseM LBTerm)
   (vLet : Expr → EraseM LBTerm) (vLam : Expr → EraseM LBTerm)
   (vProj : Name → Nat → Expr → EraseM LBTerm) (vApp : Expr → EraseM LBTerm) (e : Expr) : EraseM LBTerm := do
  if (← liftMetaM <| Erasure.isErasable (← read).lparams e) then
    return .box
  match e with
  | .app ..      => vApp e
  | .const ..    => vApp e
  | .proj s i e  => vProj s i e
  | .mdata _ e   => vExpr e
  | .lam ..      => vLam e
  | .letE ..     => vLet e
  | .lit l     => vLit l
  | .fvar fvarId => pure (.fvar fvarId)
  | .forallE .. | .mvar .. | .bvar .. | .sort ..  => unreachable!

/-- The abstract body of `Erasure.visitLiteral`: the shipping definition, with its calls into the
erasure family replaced by the induction's own functions. -/
def visitLiteralBody (vCtor : Name → Array Expr → EraseM LBTerm) (l: Literal) : EraseM LBTerm := do
  match (← read).config.nat, l with
  | .peano, .natVal 0 => vCtor ``Nat.zero #[]
  | .peano, .natVal (n+1) => vCtor ``Nat.succ #[.lit (.natVal n)]
  | .machine, .natVal n =>
    if n <= BitVec.intMax 63 then
      pure <| .prim ⟨.primInt, n⟩
    else
      panic! "Nat literal not representable as a 63-bit signed integer."
  | _, .strVal _ => panic! "String literals not supported."

/-- The abstract body of `Erasure.visitConstructor`: the shipping definition, with its calls into the
erasure family replaced by the induction's own functions. -/
def visitConstructorBody (vLit : Literal → EraseM LBTerm) (vConst : Expr → EraseM LBTerm)
   (vArgs : LBTerm → Array Expr → EraseM LBTerm) (ctorname: Name) (args: Array Expr) : EraseM LBTerm := do
  let .ctorInfo info ← getConstInfo ctorname | unreachable!
  let cidx := info.cidx
  let .inductInfo indinfo ← getConstInfo info.induct | unreachable!
  let (indid, argmasks) ← register_inductive indinfo
  let argmask := argmasks[cidx]!

  if isExtern (← getEnv) ctorname && (← read).config.extern == .preferAxiom then
    return ← vArgs (.const <| toKername ctorname) args

  match (← read).config.nat, ctorname with
  | .machine, ``Nat.zero =>
    unless args.size == 0 do
      panic s!"Nat.zero applied to {args.size} arguments."
    return ← vLit (.natVal 0)
  | .machine, ``Nat.succ =>
    unless args.size == 1 do
      panic s!"Nat.succ applied to {args.size} arguments."
    let nat_add ← vConst (.const ``Nat.add [])
    return ← vArgs nat_add #[args[0]!, .lit (.natVal 1)]
  | .machine, _
  | .peano, _ => pure ()

  let param_args := args[:info.numParams]
  let field_args := args[info.numParams:info.numParams + info.numFields]
  let extra_args := args[info.numParams + info.numFields:]
  let filtered_args := param_args.toArray ++ (filter argmask field_args) ++ extra_args.toArray
  vArgs (.construct indid cidx []) filtered_args

/-- The abstract body of `Erasure.visitConst`: the shipping definition, with its calls into the
erasure family replaced by the induction's own functions. -/
def visitConstBody (vGck : Name → EraseM Kername) (e: Expr) : EraseM LBTerm := do
  let .const declName _ := e | unreachable!
  if let .some id := (← read).fixvars.bind (fun hmap => hmap[declName]?) then
    return .fvar id
  return .const (← vGck declName)

/-- The abstract body of `Erasure.get_constant_kername`: the shipping definition, with its calls into the
erasure family replaced by the induction's own functions. -/
def getConstantKernameBody (vMut : Name → EraseM Unit) (n: Name) : EraseM Kername := do
  if let .some kn := (← get).constants.get? n then
    return kn
  else
   vMut n
   return (← get).constants[n]!

/-- The abstract body of `Erasure.visitMutual`: the shipping definition, with its calls into the
erasure family replaced by the induction's own functions. -/
def visitMutualBody (vExpr : Expr → EraseM LBTerm) (name: Name) : EraseM Unit := do
  let ci := (← Compiler.LCNF.getDeclInfo? name).get!
  let names := ci.all
  let single_decl := names.length == 1
  let leanInline := single_decl && match Compiler.getInlineAttribute? (← getEnv) name with
    | .some .inline | .some .alwaysInline => true
    | _ => false
  if single_decl then
    if leanInline then
      logInfo s!"Name {name} is marked as inline."
      modify (fun s => { s with inlinings := s.inlinings.cons (toKername name) })
    match ci.value? (allowOpaque := true), isExtern (← getEnv) name, (← read).config.extern with
    | .none, _, _ =>
      logInfo s!"No value found for name {name}, emitting axiom."
      return ← addAxiom name
    | .some _, false, _ => pure ()
    | .some _, true, .preferAxiom =>
      logInfo s!"Name {name} has a value but is tagged @[extern], emitting axiom."
      return ← addAxiom name
    | .some _, true, .preferLogical =>
      logInfo s!"Name {name} is tagged @[extern] but has a value, using value."
      pure ()

  let nonrecursive: Bool := single_decl && !(name_occurs name (ci.value! (allowOpaque := true)))
  if nonrecursive
  then
    let e: Expr := ci.value! (allowOpaque := true)
    let t ← withReader (fun env => { env with fixvars := .none, lparams := ci.levelParams }) do
      pure (← vExpr (← prepare_erasure e))
    let kn := toKername name
    modify (fun s => { s with constants := s.constants.insert name kn, gdecls := s.gdecls.cons (kn, .constantDecl <| ⟨.some t⟩) })
    if (← read).config.auto_inline_typeclass_dispatch && !leanInline && !t.containsFix then
      let isInst ← Lean.Meta.isInstance name
      if isInst then
        logInfo s!"Auto-inlining typeclass instance {name}."
        modify (fun s => { s with inlinings := s.inlinings.cons kn })
      else if t.isTrivialAlias then
        logInfo s!"Auto-inlining trivial alias {name}."
        modify (fun s => { s with inlinings := s.inlinings.cons kn })
  else
    let ids ← names.mapM (fun _ => mkFreshFVarId)
    let fixvarnames := names.map remove_unsafe_rec
    withReader (fun env => { env with fixvars := fixvarnames |>.zip ids |> Std.HashMap.ofList |> .some }) do
      let defs: List FixDef ← names.mapM (fun n => do
        let ci ← getConstInfo n
        let e: Expr := ci.value! (allowOpaque := true)
        let t: LBTerm ← withReader (fun env => { env with lparams := ci.levelParams }) do
          vExpr (← prepare_erasure e)
        mkDef (remove_unsafe_rec n) fixvarnames t
      )
      for (n, i) in fixvarnames.zipIdx do
        let kn := toKername n
        modify (fun s => { s with constants := s.constants.insert n kn, gdecls := s.gdecls.cons (kn, .constantDecl ⟨.some <| .fix defs i⟩) })

/-- The abstract body of `Erasure.visitAppArgs`: the shipping definition, with its calls into the
erasure family replaced by the induction's own functions. -/
def visitAppArgsBody (vExpr : Expr → EraseM LBTerm) (f : LBTerm) (args : Array Expr) : EraseM LBTerm := do
    args.foldlM (fun e arg => do return LBTerm.app e (← vExpr arg)) f

/-- The abstract body of `Erasure.visitLet`: the shipping definition, with its calls into the
erasure family replaced by the induction's own functions. -/
def visitLetBody (vExpr : Expr → EraseM LBTerm) (e : Expr) : EraseM LBTerm :=
  letMonocular e (fun fvarid val body => do mkLetIn fvarid (← vExpr val) (← vExpr body))

/-- The abstract body of `Erasure.visitLambda`: the shipping definition, with its calls into the
erasure family replaced by the induction's own functions. -/
def visitLambdaBody (vExpr : Expr → EraseM LBTerm) (e : Expr) : EraseM LBTerm :=
  lambdaMonocular e (fun fvarid body => do mkLambda fvarid (← vExpr body))

/-- The abstract body of `Erasure.visitProj`: the shipping definition, with its calls into the
erasure family replaced by the induction's own functions. -/
def visitProjBody (vExpr : Expr → EraseM LBTerm) (s : Name) (i : Nat) (e : Expr) : EraseM LBTerm := do
  let .inductInfo indinfo ← getConstInfo s | unreachable!
  let (indid, argmasks) ← register_inductive indinfo
  let fieldIdx := argmasks[0]![:i].toArray.count .keep
  let projinfo: ProjectionInfo := { indType := indid, paramCount := indinfo.numParams, fieldIdx }
  return .proj projinfo (← vExpr e)

/-- The abstract body of `Erasure.visitApp`: the shipping definition, with its calls into the
erasure family replaced by the induction's own functions. -/
def visitAppBody (vExpr : Expr → EraseM LBTerm) (vArgs : LBTerm → Array Expr → EraseM LBTerm)
   (vConstApp : Expr → EraseM LBTerm) (e : Expr) : EraseM LBTerm :=
  if let .const .. := e.getAppFn then
    vConstApp e
  else
    e.withApp fun f args => do vArgs (← vExpr f) args

/-- The abstract body of `Erasure.visitConstApp`: the shipping definition, with its calls into the
erasure family replaced by the induction's own functions. -/
def visitConstAppBody (vConst : Expr → EraseM LBTerm) (vArgs : LBTerm → Array Expr → EraseM LBTerm)
   (vCtorEta : Name → Nat → Expr → EraseM LBTerm)
   (vCasesEta : CasesInfo → Expr → EraseM LBTerm) (e: Expr) : EraseM LBTerm :=
  e.withApp fun f args => do
    let .const declName _ := f | unreachable!
    if let some casesInfo ← getCasesInfo? declName then
      vCasesEta casesInfo e
    else if let some arity ← Compiler.LCNF.getCtorArity? declName then
      vCtorEta declName arity e
    else
      vArgs (← vConst f) args

/-- The abstract body of `Erasure.visitCtorEta`: the shipping definition, with its calls into the
erasure family replaced by the induction's own functions. -/
def visitCtorEtaBody (vCtorEtaGo : Name → Nat → Expr → Expr → Array Expr → EraseM LBTerm)
   (ctorname : Name) (arity : Nat) (e : Expr) : EraseM LBTerm := do
  let type ← liftMetaM do Meta.inferType e
  e.withApp (fun f args => vCtorEtaGo ctorname arity type f args)

/-- The abstract body of `Erasure.visitCtorEtaGo`: the shipping definition, with its calls into the
erasure family replaced by the induction's own functions. -/
def visitCtorEtaGoBody (vCtor : Name → Array Expr → EraseM LBTerm)
   (vCtorEtaGo : Name → Nat → Expr → Expr → Array Expr → EraseM LBTerm)
   (ctorname : Name) (arity : Nat) (type f : Expr) (args : Array Expr) : EraseM LBTerm :=
  if args.size >= arity then
    vCtor ctorname args
  else
    forallMonocular type fun fvarid bodytype => do
      let res ← vCtorEtaGo ctorname arity bodytype f (args.push (.fvar fvarid))
      mkLambda fvarid res

/-- The abstract body of `Erasure.visitCasesEta`: the shipping definition, with its calls into the
erasure family replaced by the induction's own functions. -/
def visitCasesEtaBody (vCasesEtaGo : CasesInfo → Expr → Expr → Array Expr → EraseM LBTerm)
   (casesInfo : CasesInfo) (e : Expr) : EraseM LBTerm := do
  let type ← liftMetaM do Meta.inferType e
  e.withApp (fun f args => vCasesEtaGo casesInfo type f args)

/-- The abstract body of `Erasure.visitCasesEtaGo`: the shipping definition, with its calls into the
erasure family replaced by the induction's own functions. -/
def visitCasesEtaGoBody (vCasesEtaGo : CasesInfo → Expr → Expr → Array Expr → EraseM LBTerm)
   (vCases : CasesInfo → Array Expr → EraseM LBTerm)
   (casesInfo : CasesInfo) (type f : Expr) (args : Array Expr) : EraseM LBTerm :=
  if args.size >= casesInfo.arity then
    vCases casesInfo args
  else
    forallMonocular type fun fvarid bodytype => do
      let res ← vCasesEtaGo casesInfo bodytype f (args.push (.fvar fvarid))
      mkLambda fvarid res

/-- The abstract body of `Erasure.visitCases`: the shipping definition, with its calls into the
erasure family replaced by the induction's own functions. -/
def visitCasesBody (vExpr : Expr → EraseM LBTerm)
   (vAlt : Nat → ConstructorArgMask → Expr → EraseM (List BinderName × LBTerm))
   (casesInfo : CasesInfo) (args: Array Expr) : EraseM LBTerm := do
  let discr_nt ← vExpr args[casesInfo.discrPos]!
  let typeName := casesInfo.declName.getPrefix

  let mut ret: LBTerm ← (match typeName, (← read).config.nat with
  | ``Nat, .machine => do
    let zero_arm := args[casesInfo.altsRange.lower]!
    let zero_nt ← vExpr zero_arm
    let succ_arm := args[casesInfo.altsRange.lower + 1]!
    let bool_indval := (← getConstInfo ``Bool).inductiveVal!
    let (bool_indid, _) ← register_inductive bool_indval
    withLocalDecl `n (.const ``Nat []) .default (fun n_fvar => do
      let gtz_arm := Expr.app succ_arm <| mkAppN (.const ``Nat.sub []) #[.fvar n_fvar, .lit (.natVal 1)]
      let gtz_nt: LBTerm ← vExpr gtz_arm
      let condition: LBTerm ← vExpr <| mkAppN (.const ``Nat.beq []) #[.fvar n_fvar, .lit (.natVal 0)]
      let case_nt: LBTerm := .case (bool_indid, 0) condition [← mkAlt [] gtz_nt, ← mkAlt [] zero_nt]
      mkLetIn n_fvar discr_nt case_nt
    )
  | ``Int, .machine => do
    let ofnat_fun := args[casesInfo.altsRange.lower]!
    let negsucc_fun := args[casesInfo.altsRange.lower + 1]!
    let bool_indval := (← getConstInfo ``Bool).inductiveVal!
    let (bool_indid, _) ← register_inductive bool_indval
    withLocalDecl `n (.const ``Nat []) .default (fun n_fvar => do
      let ofnat_nt: LBTerm := .app (← vExpr ofnat_fun) (.fvar n_fvar)
      let negsucc_nt: LBTerm :=
        .app (← vExpr negsucc_fun)
        <| .app (← vExpr (.const ``Int.neg []))
        <| .app (← vExpr (.const ``Nat.succ [])) (.fvar n_fvar)
      let condition: LBTerm ← vExpr <| mkAppN (.const ``Nat.ble []) #[.lit (.natVal 0), .fvar n_fvar]
      let case_nt: LBTerm := .case (bool_indid, 0) condition [← mkAlt [] negsucc_nt, ← mkAlt [] ofnat_nt]
      mkLetIn n_fvar discr_nt case_nt
    )
  | _, _ => do
    let .inductInfo indVal ← getConstInfo typeName | unreachable!
    let (indid, argmasks) ← register_inductive indVal
    let mut alts := #[]
    for i in casesInfo.altsRange.toArray, altInfo in casesInfo.altNumParams, argmask in argmasks do
      let numFields := match altInfo with | .ctor _ n => n | .default n => n
      let alt ← vAlt numFields argmask args[i]!
      alts := alts.push alt
    pure <| LBTerm.case (indid, indVal.numParams) discr_nt alts.toList
  )

  for arg in (args[casesInfo.arity:]).toArray do
    ret := .app ret (← vExpr arg)
  return ret

/-- The abstract body of `Erasure.visitAlt`: the shipping definition, with its calls into the
erasure family replaced by the induction's own functions. -/
def visitAltBody (vExpr : Expr → EraseM LBTerm) (numFields : Nat) (argmask: ConstructorArgMask) (e : Expr) : EraseM (List BinderName × LBTerm) := do
  lambdaOrIntroToArity e (← liftMetaM <| Meta.inferType e) numFields fun e fvarids => do
    mkAlt (filter argmask fvarids.toArray).toList (← vExpr e)

/-! ## The approximation conjunct, discharged

Every motive's second conjunct is free: a step of the erasure functional stays below its
fixpoint (`fix_step_le`), the eighteen slots pack into one tuple (`mutual_le_of`), and one
projection lands the member. These are the eighteen instances, so a step lemma spends no
proof on them.
-/

/-- The approximation conjunct at `Erasure.visitExpr`: one step of the erasure functional
stays below its fixpoint, and the family's own monotonicity proof is what says so. -/
theorem bodyLe1 {vExpr : Expr → EraseM LBTerm} {vLit : Literal → EraseM LBTerm}
    {vLet : Expr → EraseM LBTerm} {vLam : Expr → EraseM LBTerm}
    {vProj : Name → Nat → Expr → EraseM LBTerm} {vApp : Expr → EraseM LBTerm}
    (h1 : vExpr ⊑ Erasure.visitExpr) (h2 : vLit ⊑ Erasure.visitLiteral)
    (h8 : vLet ⊑ Erasure.visitLet) (h9 : vLam ⊑ Erasure.visitLambda)
    (h10 : vProj ⊑ Erasure.visitProj) (h11 : vApp ⊑ Erasure.visitApp) :
    visitExprBody vExpr vLit vLet vLam vProj vApp ⊑ Erasure.visitExpr :=
  visitExpr_eq_mutual ▸ (fix_step_le Erasure.visitExpr.mutual._proof_1
    (mutual_le_of h1 h2 approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl h8 h9 h10 h11
      approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl)).1

/-- The approximation conjunct at `Erasure.visitLiteral`: one step of the erasure functional
stays below its fixpoint, and the family's own monotonicity proof is what says so. -/
theorem bodyLe2 {vCtor : Name → Array Expr → EraseM LBTerm}
    (h3 : vCtor ⊑ Erasure.visitConstructor) :
    visitLiteralBody vCtor ⊑ Erasure.visitLiteral :=
  visitLiteral_eq_mutual ▸ (fix_step_le Erasure.visitExpr.mutual._proof_1
    (mutual_le_of approx_rfl approx_rfl h3 approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl
      approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl
      approx_rfl approx_rfl)).2.1

/-- The approximation conjunct at `Erasure.visitConstructor`: one step of the erasure functional
stays below its fixpoint, and the family's own monotonicity proof is what says so. -/
theorem bodyLe3 {vLit : Literal → EraseM LBTerm} {vConst : Expr → EraseM LBTerm}
    {vArgs : LBTerm → Array Expr → EraseM LBTerm} (h2 : vLit ⊑ Erasure.visitLiteral)
    (h4 : vConst ⊑ Erasure.visitConst) (h7 : vArgs ⊑ Erasure.visitAppArgs) :
    visitConstructorBody vLit vConst vArgs ⊑ Erasure.visitConstructor :=
  visitConstructor_eq_mutual ▸ (fix_step_le Erasure.visitExpr.mutual._proof_1
    (mutual_le_of approx_rfl h2 approx_rfl h4 approx_rfl approx_rfl h7 approx_rfl approx_rfl
      approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl
      approx_rfl)).2.2.1

/-- The approximation conjunct at `Erasure.visitConst`: one step of the erasure functional
stays below its fixpoint, and the family's own monotonicity proof is what says so. -/
theorem bodyLe4 {vGck : Name → EraseM Kername} (h5 : vGck ⊑ Erasure.get_constant_kername) :
    visitConstBody vGck ⊑ Erasure.visitConst :=
  visitConst_eq_mutual ▸ (fix_step_le Erasure.visitExpr.mutual._proof_1
    (mutual_le_of approx_rfl approx_rfl approx_rfl approx_rfl h5 approx_rfl approx_rfl approx_rfl
      approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl
      approx_rfl approx_rfl)).2.2.2.1

/-- The approximation conjunct at `Erasure.get_constant_kername`: one step of the erasure functional
stays below its fixpoint, and the family's own monotonicity proof is what says so. -/
theorem bodyLe5 {vMut : Name → EraseM Unit} (h6 : vMut ⊑ Erasure.visitMutual) :
    getConstantKernameBody vMut ⊑ Erasure.get_constant_kername :=
  get_constant_kername_eq_mutual ▸ (fix_step_le Erasure.visitExpr.mutual._proof_1
    (mutual_le_of approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl h6 approx_rfl approx_rfl
      approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl
      approx_rfl approx_rfl)).2.2.2.2.1

/-- The approximation conjunct at `Erasure.visitMutual`: one step of the erasure functional
stays below its fixpoint, and the family's own monotonicity proof is what says so. -/
theorem bodyLe6 {vExpr : Expr → EraseM LBTerm} (h1 : vExpr ⊑ Erasure.visitExpr) :
    visitMutualBody vExpr ⊑ Erasure.visitMutual :=
  visitMutual_eq_mutual ▸ (fix_step_le Erasure.visitExpr.mutual._proof_1
    (mutual_le_of h1 approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl
      approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl
      approx_rfl approx_rfl)).2.2.2.2.2.1

/-- The approximation conjunct at `Erasure.visitAppArgs`: one step of the erasure functional
stays below its fixpoint, and the family's own monotonicity proof is what says so. -/
theorem bodyLe7 {vExpr : Expr → EraseM LBTerm} (h1 : vExpr ⊑ Erasure.visitExpr) :
    visitAppArgsBody vExpr ⊑ Erasure.visitAppArgs :=
  visitAppArgs_eq_mutual ▸ (fix_step_le Erasure.visitExpr.mutual._proof_1
    (mutual_le_of h1 approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl
      approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl
      approx_rfl approx_rfl)).2.2.2.2.2.2.1

/-- The approximation conjunct at `Erasure.visitLet`: one step of the erasure functional
stays below its fixpoint, and the family's own monotonicity proof is what says so. -/
theorem bodyLe8 {vExpr : Expr → EraseM LBTerm} (h1 : vExpr ⊑ Erasure.visitExpr) :
    visitLetBody vExpr ⊑ Erasure.visitLet :=
  visitLet_eq_mutual ▸ (fix_step_le Erasure.visitExpr.mutual._proof_1
    (mutual_le_of h1 approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl
      approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl
      approx_rfl approx_rfl)).2.2.2.2.2.2.2.1

/-- The approximation conjunct at `Erasure.visitLambda`: one step of the erasure functional
stays below its fixpoint, and the family's own monotonicity proof is what says so. -/
theorem bodyLe9 {vExpr : Expr → EraseM LBTerm} (h1 : vExpr ⊑ Erasure.visitExpr) :
    visitLambdaBody vExpr ⊑ Erasure.visitLambda :=
  visitLambda_eq_mutual ▸ (fix_step_le Erasure.visitExpr.mutual._proof_1
    (mutual_le_of h1 approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl
      approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl
      approx_rfl approx_rfl)).2.2.2.2.2.2.2.2.1

/-- The approximation conjunct at `Erasure.visitProj`: one step of the erasure functional
stays below its fixpoint, and the family's own monotonicity proof is what says so. -/
theorem bodyLe10 {vExpr : Expr → EraseM LBTerm} (h1 : vExpr ⊑ Erasure.visitExpr) :
    visitProjBody vExpr ⊑ Erasure.visitProj :=
  visitProj_eq_mutual ▸ (fix_step_le Erasure.visitExpr.mutual._proof_1
    (mutual_le_of h1 approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl
      approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl
      approx_rfl approx_rfl)).2.2.2.2.2.2.2.2.2.1

/-- The approximation conjunct at `Erasure.visitApp`: one step of the erasure functional
stays below its fixpoint, and the family's own monotonicity proof is what says so. -/
theorem bodyLe11 {vExpr : Expr → EraseM LBTerm} {vArgs : LBTerm → Array Expr → EraseM LBTerm}
    {vConstApp : Expr → EraseM LBTerm} (h1 : vExpr ⊑ Erasure.visitExpr)
    (h7 : vArgs ⊑ Erasure.visitAppArgs) (h12 : vConstApp ⊑ Erasure.visitConstApp) :
    visitAppBody vExpr vArgs vConstApp ⊑ Erasure.visitApp :=
  visitApp_eq_mutual ▸ (fix_step_le Erasure.visitExpr.mutual._proof_1
    (mutual_le_of h1 approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl h7 approx_rfl
      approx_rfl approx_rfl approx_rfl h12 approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl
      approx_rfl)).2.2.2.2.2.2.2.2.2.2.1

/-- The approximation conjunct at `Erasure.visitConstApp`: one step of the erasure functional
stays below its fixpoint, and the family's own monotonicity proof is what says so. -/
theorem bodyLe12 {vConst : Expr → EraseM LBTerm} {vArgs : LBTerm → Array Expr → EraseM LBTerm}
    {vCtorEta : Name → Nat → Expr → EraseM LBTerm} {vCasesEta : CasesInfo → Expr → EraseM LBTerm}
    (h4 : vConst ⊑ Erasure.visitConst) (h7 : vArgs ⊑ Erasure.visitAppArgs)
    (h13 : vCtorEta ⊑ Erasure.visitCtorEta) (h15 : vCasesEta ⊑ Erasure.visitCasesEta) :
    visitConstAppBody vConst vArgs vCtorEta vCasesEta ⊑ Erasure.visitConstApp :=
  visitConstApp_eq_mutual ▸ (fix_step_le Erasure.visitExpr.mutual._proof_1
    (mutual_le_of approx_rfl approx_rfl approx_rfl h4 approx_rfl approx_rfl h7 approx_rfl
      approx_rfl approx_rfl approx_rfl approx_rfl h13 approx_rfl h15 approx_rfl approx_rfl
      approx_rfl)).2.2.2.2.2.2.2.2.2.2.2.1

/-- The approximation conjunct at `Erasure.visitCtorEta`: one step of the erasure functional
stays below its fixpoint, and the family's own monotonicity proof is what says so. -/
theorem bodyLe13 {vCtorEtaGo : Name → Nat → Expr → Expr → Array Expr → EraseM LBTerm}
    (h14 : vCtorEtaGo ⊑ Erasure.visitCtorEtaGo) :
    visitCtorEtaBody vCtorEtaGo ⊑ Erasure.visitCtorEta :=
  visitCtorEta_eq_mutual ▸ (fix_step_le Erasure.visitExpr.mutual._proof_1
    (mutual_le_of approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl
      approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl h14 approx_rfl approx_rfl
      approx_rfl approx_rfl)).2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The approximation conjunct at `Erasure.visitCtorEtaGo`: one step of the erasure functional
stays below its fixpoint, and the family's own monotonicity proof is what says so. -/
theorem bodyLe14 {vCtor : Name → Array Expr → EraseM LBTerm}
    {vCtorEtaGo : Name → Nat → Expr → Expr → Array Expr → EraseM LBTerm}
    (h3 : vCtor ⊑ Erasure.visitConstructor) (h14 : vCtorEtaGo ⊑ Erasure.visitCtorEtaGo) :
    visitCtorEtaGoBody vCtor vCtorEtaGo ⊑ Erasure.visitCtorEtaGo :=
  visitCtorEtaGo_eq_mutual ▸ (fix_step_le Erasure.visitExpr.mutual._proof_1
    (mutual_le_of approx_rfl approx_rfl h3 approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl
      approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl h14 approx_rfl approx_rfl approx_rfl
      approx_rfl)).2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The approximation conjunct at `Erasure.visitCasesEta`: one step of the erasure functional
stays below its fixpoint, and the family's own monotonicity proof is what says so. -/
theorem bodyLe15 {vCasesEtaGo : CasesInfo → Expr → Expr → Array Expr → EraseM LBTerm}
    (h16 : vCasesEtaGo ⊑ Erasure.visitCasesEtaGo) :
    visitCasesEtaBody vCasesEtaGo ⊑ Erasure.visitCasesEta :=
  visitCasesEta_eq_mutual ▸ (fix_step_le Erasure.visitExpr.mutual._proof_1
    (mutual_le_of approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl
      approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl h16
      approx_rfl approx_rfl)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The approximation conjunct at `Erasure.visitCasesEtaGo`: one step of the erasure functional
stays below its fixpoint, and the family's own monotonicity proof is what says so. -/
theorem bodyLe16 {vCasesEtaGo : CasesInfo → Expr → Expr → Array Expr → EraseM LBTerm}
    {vCases : CasesInfo → Array Expr → EraseM LBTerm}
    (h16 : vCasesEtaGo ⊑ Erasure.visitCasesEtaGo) (h17 : vCases ⊑ Erasure.visitCases) :
    visitCasesEtaGoBody vCasesEtaGo vCases ⊑ Erasure.visitCasesEtaGo :=
  visitCasesEtaGo_eq_mutual ▸ (fix_step_le Erasure.visitExpr.mutual._proof_1
    (mutual_le_of approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl
      approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl h16
      h17 approx_rfl)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The approximation conjunct at `Erasure.visitCases`: one step of the erasure functional
stays below its fixpoint, and the family's own monotonicity proof is what says so. -/
theorem bodyLe17 {vExpr : Expr → EraseM LBTerm}
    {vAlt : Nat → ConstructorArgMask → Expr → EraseM (List BinderName × LBTerm)}
    (h1 : vExpr ⊑ Erasure.visitExpr) (h18 : vAlt ⊑ Erasure.visitAlt) :
    visitCasesBody vExpr vAlt ⊑ Erasure.visitCases :=
  visitCases_eq_mutual ▸ (fix_step_le Erasure.visitExpr.mutual._proof_1
    (mutual_le_of h1 approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl
      approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl
      approx_rfl h18)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The approximation conjunct at `Erasure.visitAlt`: one step of the erasure functional
stays below its fixpoint, and the family's own monotonicity proof is what says so. -/
theorem bodyLe18 {vExpr : Expr → EraseM LBTerm} (h1 : vExpr ⊑ Erasure.visitExpr) :
    visitAltBody vExpr ⊑ Erasure.visitAlt :=
  visitAlt_eq_mutual ▸ (fix_step_le Erasure.visitExpr.mutual._proof_1
    (mutual_le_of h1 approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl
      approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl approx_rfl
      approx_rfl approx_rfl)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-! ## The eighteen step interfaces

Each is the induction's obligation at one member, with the ambient specification premises the
bridge is stated under. `visitExpr_refines_of_steps` takes all eighteen and produces `Motives`.
-/

/-- Step 1 — the induction's obligation at `Erasure.visitExpr`: given the motives of the
members it calls, the motive holds of its body. -/
abbrev Step1 (lenv : Environment) (env : VEnv) (Us : List Name) (tbl : SourceTable)
    (cfg : ErasureConfig) (gw : Void IO.RealWorld → NameGenerator) : Prop :=
  ErasureSpec lenv env Us gw → SourceTableAdequate lenv tbl → ConfigPinned cfg →
  CompilerBodies lenv env tbl.body? →
  ∀ (vExpr : Expr → EraseM LBTerm) (vLit : Literal → EraseM LBTerm) (vLet : Expr → EraseM LBTerm)
    (vLam : Expr → EraseM LBTerm) (vProj : Name → Nat → Expr → EraseM LBTerm)
    (vApp : Expr → EraseM LBTerm),
    Motive1 env Us tbl cfg gw vExpr →
    Motive2 env Us tbl cfg gw vLit →
    Motive8 env Us tbl cfg gw vLet →
    Motive9 env Us tbl cfg gw vLam →
    Motive10 env Us tbl cfg gw vProj →
    Motive11 env Us tbl cfg gw vApp →
    Motive1 env Us tbl cfg gw (visitExprBody vExpr vLit vLet vLam vProj vApp)

/-- Step 2 — the induction's obligation at `Erasure.visitLiteral`: given the motives of the
members it calls, the motive holds of its body. -/
abbrev Step2 (lenv : Environment) (env : VEnv) (Us : List Name) (tbl : SourceTable)
    (cfg : ErasureConfig) (gw : Void IO.RealWorld → NameGenerator) : Prop :=
  ErasureSpec lenv env Us gw → SourceTableAdequate lenv tbl → ConfigPinned cfg →
  CompilerBodies lenv env tbl.body? →
  ∀ (vCtor : Name → Array Expr → EraseM LBTerm),
    Motive3 env Us tbl cfg gw vCtor →
    Motive2 env Us tbl cfg gw (visitLiteralBody vCtor)

/-- Step 3 — the induction's obligation at `Erasure.visitConstructor`: given the motives of the
members it calls, the motive holds of its body. -/
abbrev Step3 (lenv : Environment) (env : VEnv) (Us : List Name) (tbl : SourceTable)
    (cfg : ErasureConfig) (gw : Void IO.RealWorld → NameGenerator) : Prop :=
  ErasureSpec lenv env Us gw → SourceTableAdequate lenv tbl → ConfigPinned cfg →
  CompilerBodies lenv env tbl.body? →
  ∀ (vLit : Literal → EraseM LBTerm) (vConst : Expr → EraseM LBTerm)
    (vArgs : LBTerm → Array Expr → EraseM LBTerm),
    Motive2 env Us tbl cfg gw vLit →
    Motive4 env Us tbl cfg gw vConst →
    Motive7 env Us tbl cfg gw vArgs →
    Motive3 env Us tbl cfg gw (visitConstructorBody vLit vConst vArgs)

/-- Step 4 — the induction's obligation at `Erasure.visitConst`: given the motives of the
members it calls, the motive holds of its body. -/
abbrev Step4 (lenv : Environment) (env : VEnv) (Us : List Name) (tbl : SourceTable)
    (cfg : ErasureConfig) (gw : Void IO.RealWorld → NameGenerator) : Prop :=
  ErasureSpec lenv env Us gw → SourceTableAdequate lenv tbl → ConfigPinned cfg →
  CompilerBodies lenv env tbl.body? →
  ∀ (vGck : Name → EraseM Kername),
    Motive5 env Us tbl cfg gw vGck →
    Motive4 env Us tbl cfg gw (visitConstBody vGck)

/-- Step 5 — the induction's obligation at `Erasure.get_constant_kername`: given the motives of the
members it calls, the motive holds of its body. -/
abbrev Step5 (lenv : Environment) (env : VEnv) (Us : List Name) (tbl : SourceTable)
    (cfg : ErasureConfig) (gw : Void IO.RealWorld → NameGenerator) : Prop :=
  ErasureSpec lenv env Us gw → SourceTableAdequate lenv tbl → ConfigPinned cfg →
  CompilerBodies lenv env tbl.body? →
  ∀ (vMut : Name → EraseM Unit),
    Motive6 env Us tbl cfg gw vMut →
    Motive5 env Us tbl cfg gw (getConstantKernameBody vMut)

/-- Step 6 — the induction's obligation at `Erasure.visitMutual`: given the motives of the
members it calls, the motive holds of its body. -/
abbrev Step6 (lenv : Environment) (env : VEnv) (Us : List Name) (tbl : SourceTable)
    (cfg : ErasureConfig) (gw : Void IO.RealWorld → NameGenerator) : Prop :=
  ErasureSpec lenv env Us gw → SourceTableAdequate lenv tbl → ConfigPinned cfg →
  CompilerBodies lenv env tbl.body? →
  ∀ (vExpr : Expr → EraseM LBTerm),
    Motive1 env Us tbl cfg gw vExpr →
    Motive6 env Us tbl cfg gw (visitMutualBody vExpr)

/-- Step 7 — the induction's obligation at `Erasure.visitAppArgs`: given the motives of the
members it calls, the motive holds of its body. -/
abbrev Step7 (lenv : Environment) (env : VEnv) (Us : List Name) (tbl : SourceTable)
    (cfg : ErasureConfig) (gw : Void IO.RealWorld → NameGenerator) : Prop :=
  ErasureSpec lenv env Us gw → SourceTableAdequate lenv tbl → ConfigPinned cfg →
  CompilerBodies lenv env tbl.body? →
  ∀ (vExpr : Expr → EraseM LBTerm),
    Motive1 env Us tbl cfg gw vExpr →
    Motive7 env Us tbl cfg gw (visitAppArgsBody vExpr)

/-- Step 8 — the induction's obligation at `Erasure.visitLet`: given the motives of the
members it calls, the motive holds of its body. -/
abbrev Step8 (lenv : Environment) (env : VEnv) (Us : List Name) (tbl : SourceTable)
    (cfg : ErasureConfig) (gw : Void IO.RealWorld → NameGenerator) : Prop :=
  ErasureSpec lenv env Us gw → SourceTableAdequate lenv tbl → ConfigPinned cfg →
  CompilerBodies lenv env tbl.body? →
  ∀ (vExpr : Expr → EraseM LBTerm),
    Motive1 env Us tbl cfg gw vExpr →
    Motive8 env Us tbl cfg gw (visitLetBody vExpr)

/-- Step 9 — the induction's obligation at `Erasure.visitLambda`: given the motives of the
members it calls, the motive holds of its body. -/
abbrev Step9 (lenv : Environment) (env : VEnv) (Us : List Name) (tbl : SourceTable)
    (cfg : ErasureConfig) (gw : Void IO.RealWorld → NameGenerator) : Prop :=
  ErasureSpec lenv env Us gw → SourceTableAdequate lenv tbl → ConfigPinned cfg →
  CompilerBodies lenv env tbl.body? →
  ∀ (vExpr : Expr → EraseM LBTerm),
    Motive1 env Us tbl cfg gw vExpr →
    Motive9 env Us tbl cfg gw (visitLambdaBody vExpr)

/-- Step 10 — the induction's obligation at `Erasure.visitProj`: given the motives of the
members it calls, the motive holds of its body. -/
abbrev Step10 (lenv : Environment) (env : VEnv) (Us : List Name) (tbl : SourceTable)
    (cfg : ErasureConfig) (gw : Void IO.RealWorld → NameGenerator) : Prop :=
  ErasureSpec lenv env Us gw → SourceTableAdequate lenv tbl → ConfigPinned cfg →
  CompilerBodies lenv env tbl.body? →
  ∀ (vExpr : Expr → EraseM LBTerm),
    Motive1 env Us tbl cfg gw vExpr →
    Motive10 env Us tbl cfg gw (visitProjBody vExpr)

/-- Step 11 — the induction's obligation at `Erasure.visitApp`: given the motives of the
members it calls, the motive holds of its body. -/
abbrev Step11 (lenv : Environment) (env : VEnv) (Us : List Name) (tbl : SourceTable)
    (cfg : ErasureConfig) (gw : Void IO.RealWorld → NameGenerator) : Prop :=
  ErasureSpec lenv env Us gw → SourceTableAdequate lenv tbl → ConfigPinned cfg →
  CompilerBodies lenv env tbl.body? →
  ∀ (vExpr : Expr → EraseM LBTerm) (vArgs : LBTerm → Array Expr → EraseM LBTerm)
    (vConstApp : Expr → EraseM LBTerm),
    Motive1 env Us tbl cfg gw vExpr →
    Motive7 env Us tbl cfg gw vArgs →
    Motive12 env Us tbl cfg gw vConstApp →
    Motive11 env Us tbl cfg gw (visitAppBody vExpr vArgs vConstApp)

/-- Step 12 — the induction's obligation at `Erasure.visitConstApp`: given the motives of the
members it calls, the motive holds of its body. -/
abbrev Step12 (lenv : Environment) (env : VEnv) (Us : List Name) (tbl : SourceTable)
    (cfg : ErasureConfig) (gw : Void IO.RealWorld → NameGenerator) : Prop :=
  ErasureSpec lenv env Us gw → SourceTableAdequate lenv tbl → ConfigPinned cfg →
  CompilerBodies lenv env tbl.body? →
  ∀ (vConst : Expr → EraseM LBTerm) (vArgs : LBTerm → Array Expr → EraseM LBTerm)
    (vCtorEta : Name → Nat → Expr → EraseM LBTerm) (vCasesEta : CasesInfo → Expr → EraseM LBTerm),
    Motive4 env Us tbl cfg gw vConst →
    Motive7 env Us tbl cfg gw vArgs →
    Motive13 env Us tbl cfg gw vCtorEta →
    Motive15 env Us tbl cfg gw vCasesEta →
    Motive12 env Us tbl cfg gw (visitConstAppBody vConst vArgs vCtorEta vCasesEta)

/-- Step 13 — the induction's obligation at `Erasure.visitCtorEta`: given the motives of the
members it calls, the motive holds of its body. -/
abbrev Step13 (lenv : Environment) (env : VEnv) (Us : List Name) (tbl : SourceTable)
    (cfg : ErasureConfig) (gw : Void IO.RealWorld → NameGenerator) : Prop :=
  ErasureSpec lenv env Us gw → SourceTableAdequate lenv tbl → ConfigPinned cfg →
  CompilerBodies lenv env tbl.body? →
  ∀ (vCtorEtaGo : Name → Nat → Expr → Expr → Array Expr → EraseM LBTerm),
    Motive14 env Us tbl cfg gw vCtorEtaGo →
    Motive13 env Us tbl cfg gw (visitCtorEtaBody vCtorEtaGo)

/-- Step 14 — the induction's obligation at `Erasure.visitCtorEtaGo`: given the motives of the
members it calls, the motive holds of its body. -/
abbrev Step14 (lenv : Environment) (env : VEnv) (Us : List Name) (tbl : SourceTable)
    (cfg : ErasureConfig) (gw : Void IO.RealWorld → NameGenerator) : Prop :=
  ErasureSpec lenv env Us gw → SourceTableAdequate lenv tbl → ConfigPinned cfg →
  CompilerBodies lenv env tbl.body? →
  ∀ (vCtor : Name → Array Expr → EraseM LBTerm)
    (vCtorEtaGo : Name → Nat → Expr → Expr → Array Expr → EraseM LBTerm),
    Motive3 env Us tbl cfg gw vCtor →
    Motive14 env Us tbl cfg gw vCtorEtaGo →
    Motive14 env Us tbl cfg gw (visitCtorEtaGoBody vCtor vCtorEtaGo)

/-- Step 15 — the induction's obligation at `Erasure.visitCasesEta`: given the motives of the
members it calls, the motive holds of its body. -/
abbrev Step15 (lenv : Environment) (env : VEnv) (Us : List Name) (tbl : SourceTable)
    (cfg : ErasureConfig) (gw : Void IO.RealWorld → NameGenerator) : Prop :=
  ErasureSpec lenv env Us gw → SourceTableAdequate lenv tbl → ConfigPinned cfg →
  CompilerBodies lenv env tbl.body? →
  ∀ (vCasesEtaGo : CasesInfo → Expr → Expr → Array Expr → EraseM LBTerm),
    Motive16 env Us tbl cfg gw vCasesEtaGo →
    Motive15 env Us tbl cfg gw (visitCasesEtaBody vCasesEtaGo)

/-- Step 16 — the induction's obligation at `Erasure.visitCasesEtaGo`: given the motives of the
members it calls, the motive holds of its body. -/
abbrev Step16 (lenv : Environment) (env : VEnv) (Us : List Name) (tbl : SourceTable)
    (cfg : ErasureConfig) (gw : Void IO.RealWorld → NameGenerator) : Prop :=
  ErasureSpec lenv env Us gw → SourceTableAdequate lenv tbl → ConfigPinned cfg →
  CompilerBodies lenv env tbl.body? →
  ∀ (vCasesEtaGo : CasesInfo → Expr → Expr → Array Expr → EraseM LBTerm)
    (vCases : CasesInfo → Array Expr → EraseM LBTerm),
    Motive16 env Us tbl cfg gw vCasesEtaGo →
    Motive17 env Us tbl cfg gw vCases →
    Motive16 env Us tbl cfg gw (visitCasesEtaGoBody vCasesEtaGo vCases)

/-- Step 17 — the induction's obligation at `Erasure.visitCases`: given the motives of the
members it calls, the motive holds of its body. -/
abbrev Step17 (lenv : Environment) (env : VEnv) (Us : List Name) (tbl : SourceTable)
    (cfg : ErasureConfig) (gw : Void IO.RealWorld → NameGenerator) : Prop :=
  ErasureSpec lenv env Us gw → SourceTableAdequate lenv tbl → ConfigPinned cfg →
  CompilerBodies lenv env tbl.body? →
  ∀ (vExpr : Expr → EraseM LBTerm)
    (vAlt : Nat → ConstructorArgMask → Expr → EraseM (List BinderName × LBTerm)),
    Motive1 env Us tbl cfg gw vExpr →
    Motive18 env Us tbl cfg gw vAlt →
    Motive17 env Us tbl cfg gw (visitCasesBody vExpr vAlt)

/-- Step 18 — the induction's obligation at `Erasure.visitAlt`: given the motives of the
members it calls, the motive holds of its body. -/
abbrev Step18 (lenv : Environment) (env : VEnv) (Us : List Name) (tbl : SourceTable)
    (cfg : ErasureConfig) (gw : Void IO.RealWorld → NameGenerator) : Prop :=
  ErasureSpec lenv env Us gw → SourceTableAdequate lenv tbl → ConfigPinned cfg →
  CompilerBodies lenv env tbl.body? →
  ∀ (vExpr : Expr → EraseM LBTerm),
    Motive1 env Us tbl cfg gw vExpr →
    Motive18 env Us tbl cfg gw (visitAltBody vExpr)

end LeanToLambdaBox
