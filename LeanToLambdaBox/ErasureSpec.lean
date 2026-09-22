import LeanToLambdaBox.CheckerAdequacy
import LeanToLambdaBox.ErasureRun
import LeanToLambdaBox.Closed
import LeanToLambdaBox.Semantics.Eval
import LeanToLambdaBox.SourceEval

/-!
# The two specification bundles

`ErasureSpec` collects what the correctness statement assumes about the **impure primitives**
the shipping erasure calls: `lenv` is modelled by the `VEnv` `env`, the environment lookups
report what `lenv` holds, the `CoreM`/`MetaM` calls only advance the name generator,
`mkFreshFVarId` is fresh, and the relevance oracle is sound. Every clause names a
`Lean.*` primitive or the `lenv`↔`env` connection, so every clause is class **D** — a fact
about an object no term denotes.

`EraserAsks` collects what it assumes about **this repository's own** preprocessing and
relevance oracle: `Erasure.prepare_erasure`'s three passes and `Erasure.isErasable`. Those
are ordinary Lean definitions, so its four fields are class **C**: obligations with an owner,
whose honest end state is a proof. `EraserAsks.oracle_informative` is the first instalment —
the type-former exclusion, derived from two weaker oracle clauses rather than assumed. No
field of it mentions a reader's level scope: each is a statement about a run of the eraser's
own code at the scope that run is made at, so the bundle takes no `Us`.

`ConfigPinned` is the third input restriction, and it lives here because this is the module
below every consumer of it.

`SourceTable` adequacy is deliberately **not** a field of either: a `Prop`-valued structure
cannot hold a table as data, and an unbound table in a field auto-binds to a universal
quantifier that no table satisfies. It is the separate named hypothesis
`Witness.SourceTableAdequate`.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean Erasure
open Lean4Lean.TypeChecker (MLCtx kernelNGen M RecM)

/-! ## The configuration the statement is made at -/

/-- The five configuration restrictions the correctness statement is made under: no
`@[csimp]` replacement, no `@[extern]` axiomatisation, peano `Nat`, no constructor argmask
pruning, no typeclass-dispatch auto-inlining. Each is a scope restriction stated as a
hypothesis rather than an omission. -/
def ConfigPinned (cfg : ErasureConfig) : Prop :=
  cfg.csimp = false ∧ cfg.extern = .preferLogical ∧ cfg.nat = .peano ∧
    cfg.remove_irrel_constr_args = false ∧ cfg.auto_inline_typeclass_dispatch = false

/-! ## The oracle's assumed arm -/

/-- Soundness of a `true` relevance verdict on `e`, read at the ambient level scope `Us` and
at any modelled local context whose `LocalContext` is `lctx`: every translation of `e` there
is `Erasable`. This is the conclusion `Erasure.isErasableMeta` is assumed to deliver — it has
no verified counterpart — and the conclusion the kernel arm *proves*
(`Oracle.kernel_isErasable_sound`). -/
def Oracle.MetaSound (env : VEnv) (Us : List Name) (lctx : LocalContext) (e : Expr) : Prop :=
  ∀ (m : MLCtx) (ve : VExpr), m.WF env Us → m.lctx = lctx →
    (∀ fv ∈ m.vlctx.fvars, kernelNGen.Reserves fv) →
    TrExprS env Us m.vlctx e ve → Erasable env Us.length m.vlctx.toCtx ve

/-! ## The shapes the primitive clauses read

Three `Expr`/`CasesInfo` predicates that no clause below could be stated without. Their home
is here because here is where they are read.
-/

/-- The field count of one `casesOn` alternative, as `Erasure.visitCases` reads it. -/
def altNumFields : Lean.CasesAltInfo → Nat
  | .ctor _ n => n
  | .default n => n

/-- The inferred type's `∀`-telescope agrees with a term's λ-telescope binder for binder.
Vacuous unless the term side is a λ, which is what makes it discharge on a non-λ minor. -/
def ForallMatchesLam : Expr → Expr → Prop
  | .forallE n d c _, .lam m a b _ => n = m ∧ d = a ∧ ForallMatchesLam c b
  | _,                .lam _ _ _ _ => False
  | _,                _            => True

/-- The kernel-side field-count list of a declared inductive: one entry per constructor, read
off its `ConstructorVal`, which is where the block's arithmetic lives. -/
def KernelFields (lenv : Environment) (iv : InductiveVal) (nfs : List Nat) : Prop :=
  nfs.length = iv.ctors.length ∧
    ∀ (j : Nat) (cn : Name), iv.ctors[j]? = some cn →
      ∃ cv : ConstructorVal, lenv.find? cn = some (.ctorInfo cv) ∧ nfs[j]? = some cv.numFields ∧
        cv.induct = iv.name ∧ cv.cidx = j ∧ cv.numParams = iv.numParams

/-- **A block's constructor names determine their positions.** `KernelFields` reads each
constructor's own `ConstructorVal`, whose `cidx` is its position, and `lenv` answers one
`ConstructorVal` per name; so a name occurring at two positions forces them equal. This is what
`Erasure.visitCases`' per-constructor `findIdx?` over the alternatives
(`Erasure.lean:1122-1124`) needs to land on the slot `CasesInfoAgreesK.altCtor` describes:
`findIdx?` returns the *first* match, and only distinctness makes that the constructor's own. -/
theorem KernelFields.ctors_inj {lenv : Environment} {iv : InductiveVal} {nfs : List Nat}
    (h : KernelFields lenv iv nfs) {j k : Nat} {cn : Name}
    (hj : iv.ctors[j]? = some cn) (hk : iv.ctors[k]? = some cn) : j = k := by
  obtain ⟨cv, hcv, -, -, hj', -⟩ := h.2 j cn hj
  obtain ⟨cv', hcv', -, -, hk', -⟩ := h.2 k cn hk
  have hcc : cv = cv' := by injection Option.some.inj (hcv.symm.trans hcv')
  subst hcc
  exact hj'.symm.trans hk'

/-- The elaborator's `Lean.CasesInfo` against the block `lenv` declares. The table-side twin
is `CasesInfoAgrees`, which reads the same arithmetic off a `ReifiedInduct`. -/
structure CasesInfoAgreesK (lenv : Environment) (ci : Lean.CasesInfo)
    (iv : InductiveVal) : Prop where
  /-- The discriminant follows the parameters, the motive and the indices. -/
  discrPos : ci.discrPos = iv.numParams + 1 + iv.numIndices
  /-- The eliminator is saturated by one minor premise per constructor. -/
  arity : ci.arity = iv.numParams + 1 + iv.numIndices + 1 + iv.ctors.length
  /-- The alternatives begin one past the discriminant and end at the arity. -/
  altsRange : ci.altsRange.lower = ci.discrPos + 1 ∧ ci.altsRange.upper = ci.arity
  /-- There is one alternative per constructor. -/
  numAlts : ci.altNumParams.size = iv.ctors.length
  /-- Each alternative binds its constructor's fields. -/
  numFields : ∀ (j : Nat) (a : Lean.CasesAltInfo) (cn : Name) (cv : ConstructorVal),
    ci.altNumParams[j]? = some a → iv.ctors[j]? = some cn →
    lenv.find? cn = some (.ctorInfo cv) → altNumFields a = cv.numFields
  /-- The information names the inductive type the major premise is typed at, which is the
      block `Erasure.visitCases` reads the alternatives against (`Erasure.lean:1098`) and which
      for a `casesOn` auxiliary is not the head's name prefix. `Lean.getCasesInfo?` reads it off
      the discriminant's inferred type (`Lean/Meta/CasesInfo.lean:66`). -/
  indName : ci.indName = iv.name
  /-- Every alternative slot is its constructor's, in constructor order: `Lean.getCasesInfo?`
      builds slot `j` from the constructor its minor premise's motive argument is headed by
      (`Lean/Meta/CasesInfo.lean:71-84`), and a plain `casesOn` has one minor premise per
      constructor in that order, never the catch-all shape `.default` a sparse `casesOn`
      carries. The slot's field count is `numFields` and is not restated here. -/
  altCtor : ∀ (j : Nat) (a : Lean.CasesAltInfo) (cn : Name),
    ci.altNumParams[j]? = some a → iv.ctors[j]? = some cn → ∃ nf, a = .ctor cn nf

/-! ## Lookup adequacy -/

/-- The four environment queries the erasure makes — `Lean.getConstInfo`,
`Lean.Compiler.LCNF.getDeclInfo?`, `Lean.Compiler.LCNF.getCtorArity?` and
`Lean.getCasesInfo?` — report what `lenv` holds, and none of them advances the name
generator. Class **D**: `Lean.Environment` is an opaque primitive with a private
constructor, so no term denotes it and no statement about `getConstInfo` can be discharged
inside Lean. -/
structure LookupAdequate (lenv : Environment) (gw : Void IO.RealWorld → NameGenerator) : Prop where
  /-- `getConstInfo n` returns `lenv`'s own declaration for `n`. -/
  constInfo : ∀ (n : Name) (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State)
    (w : Void IO.RealWorld) (ci : ConstantInfo) (w₁ : Void IO.RealWorld),
    (getConstInfo n : CoreM ConstantInfo) cctx ref w = .ok ci w₁ →
    gw w ≤ gw w₁ ∧ lenv.find? n = some ci
  /-- `getDeclInfo?` answers for a name `lenv` knows, at the compiler block that name belongs
      to, and answers `none` only for a name `lenv` does not know. `getDeclInfo?` reads
      `lenv.find? (Compiler.mkUnsafeRecName n) <|> lenv.find? n`, so both arms are conditions
      on `lenv`. The membership is **guarded**: the query prefers the `_unsafe_rec` twin, so at
      `n = f._unsafe_rec` the answer's block is `f`'s and does not contain `n`. The guard is
      `TableSafe.notUnsafeRec`, a condition on the table's own constant column. -/
  declInfo : ∀ (n : Name) (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State)
    (w : Void IO.RealWorld) (r : Option ConstantInfo) (w₁ : Void IO.RealWorld),
    Lean.Compiler.LCNF.getDeclInfo? n cctx ref w = .ok r w₁ →
    gw w ≤ gw w₁ ∧
    (∀ ci, r = some ci → lenv.find? n ≠ none ∧
      (Lean.Compiler.isUnsafeRecName? n = none → n ∈ ci.all.map Erasure.remove_unsafe_rec)) ∧
    (r = none → lenv.find? n = none)
  /-- `getCtorArity?` answers exactly for the constructors `lenv` declares, at their
      parameter-plus-field arity, and for no other name. -/
  ctorArity : ∀ (n : Name) (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State)
    (w : Void IO.RealWorld) (r : Option Nat) (w₁ : Void IO.RealWorld),
    Lean.Compiler.LCNF.getCtorArity? n cctx ref w = .ok r w₁ →
    gw w ≤ gw w₁ ∧
    (∀ a, r = some a → ∃ cv : ConstructorVal, lenv.find? n = some (.ctorInfo cv) ∧
      a = cv.numParams + cv.numFields) ∧
    (r = none → ∀ cv : ConstructorVal, lenv.find? n ≠ some (.ctorInfo cv))
  /-- `getCasesInfo?` answers exactly for the `casesOn` constants, at metadata that agrees
      with the block `lenv` declares. -/
  casesInfo : ∀ (n : Name) (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State)
    (w : Void IO.RealWorld) (r : Option Lean.CasesInfo) (w₁ : Void IO.RealWorld),
    Lean.getCasesInfo? n cctx ref w = .ok r w₁ →
    gw w ≤ gw w₁ ∧
    (∀ ci, r = some ci → isCasesOnName n = true ∧ ci.declName = n ∧
      ∀ iv : InductiveVal, lenv.find? n.getPrefix = some (.inductInfo iv) →
        CasesInfoAgreesK lenv ci iv) ∧
    (r = none → isCasesOnName n = false)

/-! ## The primitive calls made for their effect, and the kernel's blocks -/

/-- A `Lean.MetaM` computation only advances the name generator, stated at the shape such a
computation is *applied* in: `Lean.MetaM` is `ReaderT Meta.Context (StateRefT Meta.State
CoreM)`, so a run takes a `Meta.Context`, a state reference, a `Core.Context`, a core state
reference and a world token.

The shape matters. At it, `>>=` is the underlying `EST.bind` definitionally, so the property
composes through a `do` block (`MetaGenMono.bind`); at the `Erasure.liftMetaM` shape the other
clauses use it does not, because `Lean.Meta.MetaM.run'` allocates a fresh `Meta.State`
reference per call and therefore does not distribute over `>>=`. `PrimMonotone.liftMetaM` is
the one clause that crosses between the two. -/
def MetaGenMono (gw : Void IO.RealWorld → NameGenerator) {α : Type} (x : Lean.MetaM α) : Prop :=
  ∀ (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) (a : α)
    (w₁ : Void IO.RealWorld),
    x mctx mref cctx ref w = .ok a w₁ → gw w ≤ gw w₁

/-- Running a bind at the applied `Lean.MetaM` shape: `Erasure.run_bind` one monad layer up. -/
theorem meta_run_bind {α β : Type} (x : Lean.MetaM α) (f : α → Lean.MetaM β)
    (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) :
    (x >>= f) mctx mref cctx ref w =
      match x mctx mref cctx ref w with
      | .ok a w₁ => f a mctx mref cctx ref w₁
      | .error e w₁ => .error e w₁ := by
  cases hx : x mctx mref cctx ref w with
  | ok a w₁ => show EST.bind (x mctx mref cctx ref) _ w = _; unfold EST.bind; rw [hx]
  | error e w₁ => show EST.bind (x mctx mref cctx ref) _ w = _; unfold EST.bind; rw [hx]

section MetaGenMono

variable {gw : Void IO.RealWorld → NameGenerator} {α β γ : Type}

/-- `pure` leaves the world where it found it. -/
theorem MetaGenMono.pure (a : α) : MetaGenMono gw (Pure.pure a : Lean.MetaM α) := by
  intro _ _ _ _ _ _ _ h
  cases h
  exact NameGenerator.LE.rfl

/-- A bind advances the generator exactly as far as its two halves do. -/
theorem MetaGenMono.bind {x : Lean.MetaM α} {f : α → Lean.MetaM β}
    (hx : MetaGenMono gw x) (hf : ∀ a, MetaGenMono gw (f a)) : MetaGenMono gw (x >>= f) := by
  intro mctx mref cctx ref w b w₁ h
  rw [meta_run_bind] at h
  cases hx' : x mctx mref cctx ref w with
  | ok a w' =>
    rw [hx'] at h
    exact NameGenerator.LE.trans (hx _ _ _ _ _ _ _ hx') (hf a _ _ _ _ _ _ _ h)
  | error e w' => rw [hx'] at h; exact nomatch h

/-- A `for` loop over a `List` advances the generator exactly as far as its body does. -/
theorem MetaGenMono.forIn_list {f : γ → β → Lean.MetaM (ForInStep β)}
    (hf : ∀ a b, MetaGenMono gw (f a b)) :
    ∀ (l : List γ) (b : β), MetaGenMono gw (forIn l b f)
  | [], _ => by rw [List.forIn_nil]; exact MetaGenMono.pure _
  | a :: as, b => by
      rw [List.forIn_cons]
      refine MetaGenMono.bind (hf a b) (fun r => ?_)
      cases r with
      | done _ => exact MetaGenMono.pure _
      | yield b' => exact MetaGenMono.forIn_list hf as b'

/-- The same over an `Array`, which is the shape the two proof scans take. -/
theorem MetaGenMono.forIn_array {f : γ → β → Lean.MetaM (ForInStep β)}
    (hf : ∀ a b, MetaGenMono gw (f a b)) (as : Array γ) (b : β) :
    MetaGenMono gw (forIn as b f) := by
  rw [← Array.forIn_toList]
  exact MetaGenMono.forIn_list hf _ _

end MetaGenMono

/-- The `CoreM`/`MetaM` calls the erasure makes for their effect alone: each only advances
the name generator, and `Lean.Meta.inferType` additionally reports a Π-telescope matching the
subject's λ-telescope, which is what `Erasure.lambdaOrIntroToArity` peels. Class **D**.

Every clause names one primitive. The two bounded telescopes name it *compositionally* —
each advances the generator no further than the continuation it is called with — which is
what keeps the two anonymous continuations the erasure passes them out of the bundle: they
are covered by `PrimGenMono`, a derived predicate, not by a clause quantifying over
arbitrary `Lean.MetaM` computations. -/
structure PrimMonotone (gw : Void IO.RealWorld → NameGenerator) : Prop where
  /-- `Lean.getEnv`. -/
  getEnv : ∀ (s : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) (le : Environment)
    (s₁ : ErasureState) (w₁ : Void IO.RealWorld),
    (Lean.getEnv : EraseM Environment) s ctx cctx ref w = .ok (le, s₁) w₁ → gw w ≤ gw w₁
  /-- `Lean.logInfo`. -/
  logInfo : ∀ (msg : MessageData) (s : ErasureState) (ctx : ErasureContext)
    (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld)
    (u : Unit) (s₁ : ErasureState) (w₁ : Void IO.RealWorld),
    (Lean.logInfo msg : EraseM Unit) s ctx cctx ref w = .ok (u, s₁) w₁ → gw w ≤ gw w₁
  /-- `Lean.Meta.isInstance`. -/
  isInstance : ∀ (nm : Name) (s : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) (b : Bool)
    (s₁ : ErasureState) (w₁ : Void IO.RealWorld),
    (liftM (Lean.Meta.isInstance nm) : EraseM Bool) s ctx cctx ref w = .ok (b, s₁) w₁ →
    gw w ≤ gw w₁
  /-- `Lean.Meta.inferType`: the generator bound, and the agreement between the inferred
      Π-telescope and the subject's λ-telescope. -/
  inferType : ∀ (e : Expr) (s : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) (ty : Expr)
    (s₁ : ErasureState) (w₁ : Void IO.RealWorld),
    Erasure.liftMetaM (Lean.Meta.inferType e) s ctx cctx ref w = .ok (ty, s₁) w₁ →
    gw w ≤ gw w₁ ∧ ForallMatchesLam ty e
  /-- `Lean.Meta.isProof`, the test `Erasure.firstNonProofField` runs on a constructor's
      fields (`Erasure.lean:308`) and `Erasure.visitCases` on the catch-all's hypotheses
      (`Erasure.lean:1152`). -/
  isProof : ∀ e : Expr, MetaGenMono gw (Lean.Meta.isProof e)
  /-- `Lean.Meta.forallBoundedTelescope`, the telescope `Erasure.firstNonProofField` opens
      over a constructor's type (`Erasure.lean:306`). It binds fresh variables of its own, so
      it advances the generator, and it advances it no further than its continuation does. -/
  forallBoundedTelescope : ∀ {α : Type} (type : Expr) (maxFVars? : Option Nat)
    (k : Array Expr → Expr → Lean.MetaM α) (cleanupAnnotations binderInfoForInstImplicit : Bool),
    (∀ vs b, MetaGenMono gw (k vs b)) →
    MetaGenMono gw (Lean.Meta.forallBoundedTelescope type maxFVars? k cleanupAnnotations
      binderInfoForInstImplicit)
  /-- `Lean.Meta.lambdaBoundedTelescope`, the telescope `Erasure.visitCases` opens over the
      catch-all alternative (`Erasure.lean:1150`), at the same reading. -/
  lambdaBoundedTelescope : ∀ {α : Type} (e : Expr) (maxFVars : Nat)
    (k : Array Expr → Expr → Lean.MetaM α) (cleanupAnnotations : Bool),
    (∀ vs b, MetaGenMono gw (k vs b)) →
    MetaGenMono gw (Lean.Meta.lambdaBoundedTelescope e maxFVars k cleanupAnnotations)
  /-- `Erasure.liftMetaM` (`Erasure.lean:174`), the family's only way of running a `MetaM`
      computation: a generator bound at the applied shape survives the
      `Lean.Meta.MetaM.run'` the lift goes through. This is the clause that carries the three
      `MetaGenMono` ones above to the shape the run lemmas read, and the reason none of them
      has to be restated at it. -/
  liftMetaM : ∀ {α : Type} {x : Lean.MetaM α}, MetaGenMono gw x →
    ∀ {a : α} {s s₁ : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
      {ref : ST.Ref IO.RealWorld Core.State} {w w₁ : Void IO.RealWorld},
    Erasure.liftMetaM x s ctx cctx ref w = .ok (a, s₁) w₁ → gw w ≤ gw w₁

/-- The `Lean.MetaM` computations whose generator bound is a *consequence* of
`PrimMonotone`'s clauses for the named primitives: those built from `Lean.Meta.isProof` and
the two bounded telescopes with `pure` and `>>=`. It carries no assumption of its own — every
occurrence below is discharged by the combinators — and it is what lets the run interface
demand a generator bound without quantifying over arbitrary `MetaM` computations. -/
def PrimGenMono {α : Type} (x : Lean.MetaM α) : Prop :=
  ∀ gw : Void IO.RealWorld → NameGenerator, PrimMonotone gw → MetaGenMono gw x

section PrimGenMono

variable {α β γ : Type}

/-- `pure`. -/
theorem PrimGenMono.pure (a : α) : PrimGenMono (Pure.pure a : Lean.MetaM α) :=
  fun _ _ => MetaGenMono.pure a

/-- A bind of two covered computations. -/
theorem PrimGenMono.bind {x : Lean.MetaM α} {f : α → Lean.MetaM β}
    (hx : PrimGenMono x) (hf : ∀ a, PrimGenMono (f a)) : PrimGenMono (x >>= f) :=
  fun gw hpm => MetaGenMono.bind (hx gw hpm) (fun a => hf a gw hpm)

/-- A `for` loop over an `Array` with a covered body. -/
theorem PrimGenMono.forIn_array {f : γ → β → Lean.MetaM (ForInStep β)}
    (hf : ∀ a b, PrimGenMono (f a b)) (as : Array γ) (b : β) : PrimGenMono (forIn as b f) :=
  fun gw hpm => MetaGenMono.forIn_array (fun a b => hf a b gw hpm) as b

/-- `Lean.Meta.isProof`. -/
theorem PrimGenMono.isProof (e : Expr) : PrimGenMono (Lean.Meta.isProof e) :=
  fun _ hpm => hpm.isProof e

/-- `Lean.Meta.forallBoundedTelescope` at a covered continuation. -/
theorem PrimGenMono.forallBoundedTelescope (type : Expr) (maxFVars? : Option Nat)
    (k : Array Expr → Expr → Lean.MetaM α) (cleanupAnnotations binderInfoForInstImplicit : Bool)
    (hk : ∀ vs b, PrimGenMono (k vs b)) :
    PrimGenMono (Lean.Meta.forallBoundedTelescope type maxFVars? k cleanupAnnotations
      binderInfoForInstImplicit) :=
  fun gw hpm => hpm.forallBoundedTelescope type maxFVars? k cleanupAnnotations
    binderInfoForInstImplicit (fun vs b => hk vs b gw hpm)

/-- `Lean.Meta.lambdaBoundedTelescope` at a covered continuation. -/
theorem PrimGenMono.lambdaBoundedTelescope (e : Expr) (maxFVars : Nat)
    (k : Array Expr → Expr → Lean.MetaM α) (cleanupAnnotations : Bool)
    (hk : ∀ vs b, PrimGenMono (k vs b)) :
    PrimGenMono (Lean.Meta.lambdaBoundedTelescope e maxFVars k cleanupAnnotations) :=
  fun gw hpm => hpm.lambdaBoundedTelescope e maxFVars k cleanupAnnotations
    (fun vs b => hk vs b gw hpm)

end PrimGenMono

/-- **The proof scan both bounded telescopes are called with.** `Erasure.firstNonProofField`
runs it on a constructor's fields (`Erasure.lean:307-309`) and `Erasure.visitCases` on the
catch-all's hypotheses (`Erasure.lean:1151-1153`): one `Lean.Meta.isProof` per binder, stopping
at the first that is not a proof. Stated once, at the array the caller scans, so that neither
anonymous continuation has to be transcribed at its call site. -/
theorem primGenMono_proofScan (xs : Array (Expr × Nat)) :
    PrimGenMono (show Lean.MetaM (Option Nat) from do
      for (v, i) in xs do
        unless ← Lean.Meta.isProof v do return some i
      return none) := by
  refine PrimGenMono.bind (PrimGenMono.forIn_array (fun p _ => ?_) _ _) (fun r => ?_)
  · obtain ⟨v, -⟩ := p
    exact PrimGenMono.bind (PrimGenMono.isProof v)
      (fun _ => by split <;> exact PrimGenMono.pure _)
  · obtain ⟨o, -⟩ := r
    cases o <;> exact PrimGenMono.pure _

/-- The kernel's inductive blocks and the model's agree: `ErasureSpec.decl_adequate`'s
block-level sibling, at the identifier `Erasure.register_inductive` mints. Class **D**. -/
structure BlockAdequate (lenv : Environment) (env : VEnv) : Prop where
  /-- A member of a declared block is the model's type former at that block's identifier. -/
  fwd : ∀ (n m : Name) (iv ivm : InductiveVal) (i : Nat) (nfs : List Nat),
    lenv.find? n = some (.inductInfo iv) → iv.all[i]? = some m →
    lenv.find? m = some (.inductInfo ivm) → KernelFields lenv ivm nfs →
    IndInfo env m ⟨indBlockKername iv.all, i⟩ iv.numParams nfs
  /-- A model type former is declared, at the same arithmetic. -/
  bwd : ∀ (I : Name) (np : Nat) (nfs : List Nat), IndArity env I np nfs →
    ∃ iv : InductiveVal, lenv.find? I = some (.inductInfo iv) ∧ iv.name = I ∧
      iv.numParams = np ∧ KernelFields lenv iv nfs
  /-- A declared constructor is the model's constructor of its type, at its index. -/
  ctor : ∀ (c : Name) (cv : ConstructorVal), lenv.find? c = some (.ctorInfo cv) →
    CtorOf env c cv.induct cv.cidx
  /-- And conversely. -/
  ctorBwd : ∀ (c I : Name) (k : Nat), CtorOf env c I k →
    ∃ cv : ConstructorVal, lenv.find? c = some (.ctorInfo cv) ∧ cv.induct = I ∧ cv.cidx = k
  /-- The `casesOn` constant of a declared inductive is declared in the model, at the
      segmentation the block fixes: the discriminant sits after the parameters, the motive and
      the indices, which is the same arithmetic `CasesInfoAgreesK.discrPos` reads off the
      elaborator's own metadata. Named `casesOnDecl` because a structure may not carry a
      field called `casesOn`. -/
  casesOnDecl : ∀ (c I : Name) (iv : InductiveVal), isCasesOnName c = true → c.getPrefix = I →
    lenv.find? I = some (.inductInfo iv) →
    ∃ nm vc, env.constants c = some vc ∧ ConstOrigin env c ∧
      CasesOnShape env c I (iv.numParams + 1 + iv.numIndices) nm
  /-- A declared inductive is a member of its own block. Class **D** like the five beside it:
      `Lean.InductiveVal.all` is the elaborator's own record of the mutual block, and the
      registration loop of `Erasure.register_inductive` is indexed by membership in it. -/
  selfMem : ∀ (I : Name) (iv : InductiveVal), lenv.find? I = some (.inductInfo iv) →
    iv.name ∈ iv.all

/-! ## The bundle -/

/-- The specification of the erasure's ambient primitives, at the elaboration environment
`lenv`, its model `env`, the ambient level scope `Us` and the name-generator reading `gw`.

`Us` occurs in one field, `oracle_refl`, and there under the premise `ctx.lparams = Us`, so the
bundle says nothing about a call made at any other scope. The bridge therefore takes it at every
scope — `∀ Us, ErasureSpec lenv env Us gw` — which is MetaRocq's per-constant
`abstract_make_wf_env_ext` (`../metarocq/erasure/theories/ErasureFunction.v`) and is what lets a
sub-run below `Erasure.visitMutual`'s `withReader (… lparams := ci.levelParams)` spend the
kernel arm at the scope its verdict was taken under. -/
structure ErasureSpec (lenv : Environment) (env : VEnv) (Us : List Name)
    (gw : Void IO.RealWorld → NameGenerator) : Prop where
  /-- `lenv` is modelled by `env` at safety `.safe`. `Lean4Lean.VEnvs.WF` is stated at
      `Lean.Kernel.Environment`, so the conversion is named here: `lenv.toKernelEnv` is the
      same conversion the shipping oracle makes (`Erasure.isErasable`). Class **D**. -/
  env_connect : ∃ ves : VEnvs, ves.WF lenv.toKernelEnv ∧ env = ves.venv .safe
  /-- The environment queries report what `lenv` holds. Class **D**; see `LookupAdequate`. -/
  lookup_adequate : LookupAdequate lenv gw
  /-- `Lean.mkFreshFVarId` returns an identifier the ambient generator has not handed out,
      reserves it afterwards, and only advances the generator. Class **D**: the generator is
      read out of `IO.RealWorld`, which is opaque. -/
  fresh_names : ∀ (s : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) (x : FVarId)
    (s₁ : ErasureState) (w₁ : Void IO.RealWorld),
    (mkFreshFVarId : EraseM FVarId) s ctx cctx ref w = .ok (x, s₁) w₁ →
    ¬ (gw w).Reserves x ∧ (gw w₁).Reserves x ∧ gw w ≤ gw w₁ ∧ kernelNGen.Reserves x
  /-- A `true` verdict of the relevance oracle at the **ambient** level scope either reflects
      a successful run of the pure verified checker at the same local context and scope, or
      came from the `Erasure.isErasableMeta` fallback, which is assumed sound. The kernel
      disjunct is discharged by `Oracle.kernel_isErasable_sound` — that is what
      `ErasureSpec.oracle_sound_of_run` composes. Class **D** with a class-**B** arm: what is
      irreducible is that the impure `MetaM` plumbing of `Erasure.isErasable` reflects the pure
      `Lean4Lean.TypeChecker.M.run` it calls; no term denotes a `MetaM` run. -/
  oracle_refl : ∀ (e : Expr) (s : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) (b : Bool)
    (s₁ : ErasureState) (w₁ : Void IO.RealWorld),
    Erasure.liftMetaM (Erasure.isErasable ctx.lparams e) s ctx cctx ref w = .ok (b, s₁) w₁ →
    gw w ≤ gw w₁ ∧ (b = true → ctx.lparams = Us →
      M.run lenv.toKernelEnv .safe ctx.lctx ctx.lparams {}
          (RecM.run (LeanToLambdaBox.isErasable e)) = .ok true
      ∨ Oracle.MetaSound env Us ctx.lctx e)
  /-- A declaration `lenv` makes visible at `.safe` is visible in `env` with a translated
      type — in particular an `Lean.InductiveVal` and its model constant.

      This is the field's **amended** shape, and the amendment is the outcome of the derivation
      attempt the design asks for. `ErasureSpec.decl_adequate_of_kernelFind` *proves* the
      statement from `env_connect` alone, for the kernel environment's own lookup; what it
      cannot cross is `Lean.Environment.find?` versus `Lean.Kernel.Environment.find?` — two
      opaque primitives whose agreement is not a theorem of this development. The inductive-only
      form is the `.inductInfo` instance of the same clause, and the fragment predicate
      (`Supported`) needs the other instances too, so the clause is stated uniformly. Class
      **D**, for the same reason `env_connect` is. -/
  decl_adequate : ∀ (n : Name) (ci : ConstantInfo), lenv.find? n = some ci →
    DefinitionSafety.safe ≤ ci.safety →
    ∃ vc, env.constants n = some vc ∧ TrConstant .safe env ci vc
  /-- The `CoreM`/`MetaM` calls the erasure makes for their effect alone. Class **D**. -/
  prim_monotone : PrimMonotone gw
  /-- The kernel's blocks, constructors and eliminators, in the model. Class **D**. -/
  block_adequate : BlockAdequate lenv env

/-! ## What the bundle proves -/

/-- The modelled environment is well formed. A genuine reduction: `env.WF` is what the
target-side metatheory needs, and it follows from the model connection rather than being
assumed. -/
theorem ErasureSpec.envWF {lenv : Environment} {env : VEnv} {Us : List Name}
    {gw : Void IO.RealWorld → NameGenerator} (P : ErasureSpec lenv env Us gw) : env.WF := by
  obtain ⟨ves, hwf, rfl⟩ := P.env_connect
  exact TrEnv'.wf (safety := .safe) hwf.tr

/-- **The kernel arm, discharged.** A `true` verdict of the shipping relevance oracle at the
ambient level scope makes every translation of the subject `Erasable`: the kernel disjunct of
`oracle_refl` is composed with `Oracle.kernel_isErasable_sound`, the assumed disjunct is
`Oracle.MetaSound` itself. -/
theorem ErasureSpec.oracle_sound_of_run {lenv : Environment} {env : VEnv} {Us : List Name}
    {gw : Void IO.RealWorld → NameGenerator} (P : ErasureSpec lenv env Us gw)
    {e : Expr} {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
    {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
    {s₁ : ErasureState} {w₁ : Void IO.RealWorld}
    (hrun : Erasure.liftMetaM (Erasure.isErasable ctx.lparams e) s ctx cctx ref w
      = .ok (true, s₁) w₁)
    (hlp : ctx.lparams = Us)
    {m : MLCtx} {ve : VExpr} (mwf : m.WF env Us) (hlctx : m.lctx = ctx.lctx)
    (hfresh : ∀ fv ∈ m.vlctx.fvars, kernelNGen.Reserves fv)
    (htr : TrExprS env Us m.vlctx e ve) :
    Erasable env Us.length m.vlctx.toCtx ve := by
  obtain ⟨ves, hwf, rfl⟩ := P.env_connect
  rcases (P.oracle_refl e s ctx cctx ref w true s₁ w₁ hrun).2 rfl hlp with hker | hmeta
  · subst hlp
    exact Oracle.kernel_isErasable_sound hwf mwf hfresh htr (by rw [hlctx]; exact hker)
  · exact hmeta m ve mwf hlctx hfresh htr

/-- The declaration-adequacy clause of `ErasureSpec`, **proved** for the kernel environment's
own lookup. This is the derivation `decl_adequate` records: `env_connect` gives
`Lean4Lean.TrEnv`, and `Lean4Lean.TrEnv.find?` reads a visible declaration off it. -/
theorem ErasureSpec.decl_adequate_of_kernelFind {lenv : Environment} {env : VEnv}
    {Us : List Name} {gw : Void IO.RealWorld → NameGenerator} (P : ErasureSpec lenv env Us gw)
    {n : Name} {ci : ConstantInfo} (h : lenv.toKernelEnv.find? n = some ci)
    (hs : DefinitionSafety.safe ≤ ci.safety) :
    ∃ vc, env.constants n = some vc ∧ TrConstant .safe env ci vc := by
  obtain ⟨ves, hwf, rfl⟩ := P.env_connect
  exact TrEnv.find? hwf.tr h hs

/-- **The arity walk commutes with translation.** A Π-telescope ending in a sort translates to
a Π-telescope ending in the translated sort: `Erasure.arityResultSort` (`Erasure.lean:281`) and
`vResultSort` (`Erasability.lean:240`) read the same two arms, and `TrExprS` is structural on
both. The converse fails — see `ErasureSpec.propositionalInd_of_arity`. -/
theorem vResultSort_of_arityResultSort {env : VEnv} {Us : List Name} {u : Level} :
    ∀ {Δ : VLCtx} {e : Expr} {ve : VExpr}, TrExprS env Us Δ e ve →
      Erasure.arityResultSort e = some u →
      ∃ u', vResultSort ve = some u' ∧ VLevel.ofLevel Us u = some u' := by
  intro Δ e
  induction e generalizing Δ with
  | forallE _ _ _ _ _ ihb =>
    intro ve htr har
    cases htr with
    | forallE _ _ _ htrb =>
      obtain ⟨u', hu', hofl⟩ := ihb htrb har
      exact ⟨u', hu', hofl⟩
  | sort l =>
    intro ve htr har
    cases htr with
    | sort hofl =>
      cases Option.some.inj har
      exact ⟨_, rfl, hofl⟩
  | _ => intro ve htr har; simp [Erasure.arityResultSort] at har

/-- **The emitted propositional flag is sound against the model.** An inductive type whose
declared arity `Erasure.isPropositionalArity` accepts is `PropositionalInd` in `env`: the arity
walk commutes with the translation `decl_adequate` supplies, `Lean.Level.isAlwaysZero` and
`alwaysZeroB` agree across `VLevel.ofLevel` (`ofLevel_alwaysZeroB`), and `alwaysZeroB_sound`
reads the valuation-wide equation off the decision. This is the half of MetaRocq's equation
`isPropositionalArity ind_type = ind_propositional`
(`../metarocq/erasure/theories/Extract.v:276`) that a consumer of the flag spends —
`propositional_false_of_informative` contradicts a `true` flag against `InformativeInd`.

The converse implication is **false**, and no clause of `ErasureSpec` assumes it:
`Erasure.arityResultSort` walks `.forallE` alone, where MetaRocq's `destArity`
(`../metarocq/pcuic/theories/PCUICAst.v:486-490`) walks `tLetIn` as well, so at
`inductive FooLet : (let _x := Nat; Prop)` — which elaborates, and whose `InductiveVal.type`
keeps the `letE` — `isPropositionalArity` answers `false` while the translated type is
`.sort .zero` and `PropositionalInd` holds. Recorded against the shipping eraser in
`doc/rework/03-DEV-FIX.md`, F-ARITYLET. -/
theorem ErasureSpec.propositionalInd_of_arity {lenv : Environment} {env : VEnv} {Us : List Name}
    {gw : Void IO.RealWorld → NameGenerator} (P : ErasureSpec lenv env Us gw)
    {I : Name} {iv : InductiveVal} (hfind : lenv.find? I = some (.inductInfo iv))
    (hsafe : DefinitionSafety.safe ≤ (ConstantInfo.inductInfo iv).safety)
    (hprop : Erasure.isPropositionalArity iv.type = true) : PropositionalInd env I := by
  obtain ⟨vc, hvc, -, -, htr⟩ := P.decl_adequate I (.inductInfo iv) hfind hsafe
  rw [Erasure.isPropositionalArity] at hprop
  cases har : Erasure.arityResultSort iv.type with
  | none => rw [har] at hprop; exact absurd hprop (by simp)
  | some u =>
    rw [har] at hprop
    obtain ⟨u', hu', hofl⟩ := vResultSort_of_arityResultSort htr har
    exact ⟨vc, hvc, u', hu', alwaysZeroB_sound ((ofLevel_alwaysZeroB hofl).trans hprop)⟩


/-! ## The eraser's own asks

`Erasure.prepare_erasure`'s passes and `Erasure.isErasable` are defined in this repository,
so a hypothesis about them is an obligation with an owner, not a specification of an input.
They get their own bundle for that reason. The symmetric bundle for lean4lean is
`UpstreamAsks`.
-/

/-- The three `CoreM` passes `Erasure.prepare_erasure` runs. It calls them four times —
`Lean.Compiler.LCNF.macroInline` runs twice — and its `@[csimp]` walk is out of scope by
`ConfigPinned`. -/
def preparePasses : List (Expr → CoreM Expr) :=
  [Erasure.replaceUnsafeRecNames, Lean.Compiler.LCNF.macroInline,
    Lean.Compiler.LCNF.inlineMatchers]

/-- What the correctness statement assumes about the eraser's **own** preprocessing and
relevance oracle. Class **C**: each field is an obligation with an owner, and the honest end
state of each is a proof. -/
structure EraserAsks (lenv : Environment) (env : VEnv)
    (gw : Void IO.RealWorld → NameGenerator) : Prop where
  /-- The four `Erasure.prepare_erasure` calls only advance the generator. Owner: this
      repository, wave W5; discharged by unfolding `Lean.Core.transform`'s generator discipline
      at the three passes. -/
  passes_monotone : ∀ (f : Expr → CoreM Expr), f ∈ preparePasses →
    ∀ (e e' : Expr) (s : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
      (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) (s₁ : ErasureState)
      (w₁ : Void IO.RealWorld),
      (liftM (f e) : EraseM Expr) s ctx cctx ref w = .ok (e', s₁) w₁ → gw w ≤ gw w₁
  /-- Each pass preserves the source evaluation of the subject **under an arbitrary
      application spine**: the capstone reads the observable at `mkApps e args` while the pass
      is a whole-tree walk, so a clause stated at the subject alone does not reach the spine.
      Owner: this repository, wave W5; the δ-expansion half is about
      `Lean.Compiler.LCNF.macroInline`, the `_unsafe_rec` half about
      `Erasure.replaceUnsafeRecNames`. -/
  passes_sound : ∀ (f : Expr → CoreM Expr), f ∈ preparePasses →
    ∀ (e e' : Expr) (s : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
      (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) (s₁ : ErasureState)
      (w₁ : Void IO.RealWorld),
      (liftM (f e) : EraseM Expr) s ctx cctx ref w = .ok (e', s₁) w₁ →
      ∀ (args : List Expr) (bo : Name → Option Expr) (Us' : List Name) (fl : SEvalFlags)
        (Δ : VLCtx) (v : Expr),
        SEval env bo Us' fl Δ (mkApps e args) v → SEval env bo Us' fl Δ (mkApps e' args) v
  /-- A `false` verdict of `Erasure.isErasable` means the **pure kernel run** did not answer
      `true`. Near-definitional — the `| .ok b => return b` arm, modulo the `getEnv`/`getLCtx`
      reads — and so a statement about the two runs at the one scope both are made at,
      `ctx.lparams`, with no reader's scope in it. Owner: this repository, wave W5; discharged
      by a `MetaM` reflection lemma. -/
  oracle_false_refl : ∀ (e : Expr) (s : ErasureState) (ctx : ErasureContext)
    (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld)
    (s₁ : ErasureState) (w₁ : Void IO.RealWorld),
    Erasure.liftMetaM (Erasure.isErasable ctx.lparams e) s ctx cctx ref w = .ok (false, s₁) w₁ →
    M.run lenv.toKernelEnv .safe ctx.lctx ctx.lparams {}
      (RecM.run (LeanToLambdaBox.isErasable e)) ≠ .ok true
  /-- At an inductive-type head the pure kernel run answers `true`: the oracle's completeness
      at the one shape the fragment cannot exclude, reduced to the kernel arm. **Not a
      theorem.** `Erasure.isArityCheck` walks the head's type under a fixed budget
      (`Relevance.lean:49-50`), so a type whose *reduced* telescope is longer than that budget —
      and any other kernel error raised inside `isArityCheck` — leaves the walk short of the
      closing sort and routes the verdict to `Erasure.isErasableMeta`, of which only soundness
      is assumed (`ErasureSpec.oracle_refl`'s second disjunct). The scope `lps` is the run's
      own — the one
      `Erasure.isErasable` is called at, which `Erasure.visitMutual` installs from the
      declaration being entered — and not a reader's: at a fixed `[]` the premises are
      uninhabited below a universe-polymorphic declaration, which is where the shipping
      oracle's `casesOn` verdicts are taken. Owner: this repository, wave W5; discharged by
      three executable-shape lemmas lean4lean does not have, together with a bound on the
      reduced telescope, which a constant budget does not supply. -/
  kernel_ind_head_true : ∀ (lps : List Name) (lctx : LocalContext) (m : MLCtx) (e : Expr)
      (c : Name) (us : List Level) (ve : VExpr) (iid : InductiveId) (np : Nat)
      (nfs : List Nat),
    m.WF env lps → m.lctx = lctx → (∀ fv ∈ m.vlctx.fvars, kernelNGen.Reserves fv) →
    e.getAppFn = .const c us → IndInfo env c iid np nfs → TrExprS env lps m.vlctx e ve →
    M.run lenv.toKernelEnv .safe lctx lps {}
      (RecM.run (LeanToLambdaBox.isErasable e)) = .ok true

/-! ## What the second bundle proves -/

/-- An inductive-type-name spine is erasable: the head's type is an arity, so the head is
`Erasable`, and `Erasable.app` carries that along the spine. -/
theorem erasable_indSpine {env : VEnv} {Us : List Name} {Δ : VLCtx} (henv : env.WF)
    (hΔ : VLCtx.WF env Us.length Δ) {c : Name} {us : List Level} {iid : InductiveId}
    {np : Nat} {nfs : List Nat} (hi : IndInfo env c iid np nfs) :
    ∀ (args : List Expr) {ve : VExpr},
      TrExprS env Us Δ (mkApps (.const c us) args) ve → Erasable env Us.length Δ.toCtx ve := by
  have key : ∀ (n : Nat) (args : List Expr), args.length = n → ∀ {ve : VExpr},
      TrExprS env Us Δ (mkApps (.const c us) args) ve → Erasable env Us.length Δ.toCtx ve := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro args hlen ve htr
      rcases List.eq_nil_or_concat args with rfl | ⟨l', b, rfl⟩
      · exact Erases.indInfo_erasable henv hΔ hi htr
      · rw [List.concat_eq_append, mkApps_append, mkApps_cons, mkApps_nil] at htr
        cases htr with
        | app hTf hTa htrf htra =>
          refine Erasable.app henv hΔ.toCtx (ih l'.length ?_ l' rfl htrf) hTf hTa
          simp only [List.length_concat] at hlen
          omega
  exact fun args => key args.length args rfl

/-- **The type-former exclusion, derived.** A `false` verdict of `Erasure.isErasable` rules
out an inductive-type head: the two oracle clauses contradict each other at the scope the
verdict was taken under, `ctx.lparams`, which is the scope both clauses now read. Stated at
the `MLCtx`, so the three facts a bridge invariant supplies are explicit arguments. -/
theorem EraserAsks.oracle_informative {lenv : Environment} {env : VEnv}
    {gw : Void IO.RealWorld → NameGenerator} (E : EraserAsks lenv env gw)
    {m : MLCtx} {ctx : ErasureContext} {e : Expr} {ve : VExpr} {s s₁ : ErasureState}
    {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State} {w w₁ : Void IO.RealWorld}
    (hm : m.WF env ctx.lparams) (hlctx : m.lctx = ctx.lctx)
    (hfresh : ∀ fv ∈ m.vlctx.fvars, kernelNGen.Reserves fv)
    (hor : Erasure.liftMetaM (Erasure.isErasable ctx.lparams e) s ctx cctx ref w
      = .ok (false, s₁) w₁)
    (htr : TrExprS env ctx.lparams m.vlctx e ve) :
    ∀ c us, e.getAppFn = .const c us → ∀ iid np nfs, ¬ IndInfo env c iid np nfs := by
  intro c us hfn iid np nfs hind
  refine E.oracle_false_refl e s ctx cctx ref w s₁ w₁ hor ?_
  exact E.kernel_ind_head_true ctx.lparams ctx.lctx m e c us ve iid np nfs hm hlctx hfresh
    hfn hind htr

/-! ## The relational pass interface -/

/-- A λ□→λ□ pass, as a relation between two terms read at the specification environment, with
its source and target evaluation points. `wfSpec` and `envRel` are the environment-side
predicates the pass's correctness is relative to: the specification environment is well formed,
and the emitted environment is its image. They are parameters here because the two predicates
`LBWfSpec` and `LowerEnv` are introduced with the environment-erasure relation; instantiating
them is what turns this interface into the statement of `lower_correct`.

Every binder of `correct` is explicit at the field, so no variable of the statement is captured
by the structure's own telescope. -/
structure LBPassR (wfSpec : GlobalDeclarations → Prop)
    (envRel : GlobalDeclarations → GlobalDeclarations → Prop) where
  /-- The pass, at a specification environment. -/
  rel : GlobalDeclarations → LBTerm → LBTerm → Prop
  /-- The evaluation point of the source term. -/
  flIn : WcbvFlags
  /-- The evaluation point of the target term. -/
  flOut : WcbvFlags
  /-- Forward simulation, in `optimize_correct`'s shape with the value existentially bound. -/
  correct : ∀ (Γspec Γ : GlobalDeclarations) (t t' v : LBTerm), wfSpec Γspec → LBClosed t 0 →
    envRel Γspec Γ → rel Γspec t t' → WcbvEval Γspec flIn t v →
    ∃ v', rel Γspec v v' ∧ WcbvEval Γ flOut t' v'

end LeanToLambdaBox
