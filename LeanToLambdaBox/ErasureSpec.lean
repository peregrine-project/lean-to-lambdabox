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
are ordinary Lean definitions, so its five fields are class **C**: obligations with an owner,
whose honest end state is a proof. `EraserAsks.oracle_informative` is the first instalment —
the type-former exclusion, derived from two weaker oracle clauses rather than assumed.

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
      to. The membership is **guarded**: `getDeclInfo?` prefers the `_unsafe_rec` twin, so at
      `n = f._unsafe_rec` the answer's block is `f`'s and does not contain `n`. The guard is
      discharged at the call site, where the visited name comes out of a term
      `Erasure.replaceUnsafeRecNames` has already stripped. -/
  declInfo : ∀ (n : Name) (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State)
    (w : Void IO.RealWorld) (r : Option ConstantInfo) (w₁ : Void IO.RealWorld),
    Lean.Compiler.LCNF.getDeclInfo? n cctx ref w = .ok r w₁ →
    gw w ≤ gw w₁ ∧ ∀ ci, r = some ci → lenv.find? n ≠ none ∧
      (Lean.Compiler.isUnsafeRecName? n = none → n ∈ ci.all.map Erasure.remove_unsafe_rec)
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

/-- The `CoreM`/`MetaM` calls the erasure makes for their effect alone: each only advances
the name generator, and `Lean.Meta.inferType` additionally reports a Π-telescope matching the
subject's λ-telescope, which is what `Erasure.lambdaOrIntroToArity` peels. Class **D**. -/
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
      segmentation the block fixes. Named `casesOnDecl` because a structure may not carry a
      field called `casesOn`. -/
  casesOnDecl : ∀ (c I : Name) (iv : InductiveVal), isCasesOnName c = true → c.getPrefix = I →
    lenv.find? I = some (.inductInfo iv) →
    ∃ dp nm vc, env.constants c = some vc ∧ ConstOrigin env c ∧ CasesOnShape env c I dp nm
/-! ## The bundle -/

/-- The specification of the erasure's ambient primitives, at the elaboration environment
`lenv`, its model `env`, the ambient level scope `Us` and the name-generator reading `gw`. -/
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
  /-- A `true` verdict at a level scope **other** than the ambient one is sound. Class **D**
      with no proved arm, and a real scope limit rather than a formality: the verified checker
      concludes at the scope it ran in, while the consumer holds its translation witness at
      `Us`, and a term that translates at `Us` need not translate at a different scope. A
      dependency erased at its own `levelParams` therefore lands here. At `Us = []` — the
      capstone's scope — the field covers exactly the runs made below a polymorphic
      declaration. -/
  oracle_meta : ∀ (e : Expr) (s : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld)
    (s₁ : ErasureState) (w₁ : Void IO.RealWorld),
    Erasure.liftMetaM (Erasure.isErasable ctx.lparams e) s ctx cctx ref w = .ok (true, s₁) w₁ →
    ctx.lparams ≠ Us → Oracle.MetaSound env Us ctx.lctx e
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
structure EraserAsks (lenv : Environment) (env : VEnv) (Us : List Name)
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
      reads. Owner: this repository, wave W5; discharged by a `MetaM` reflection lemma. -/
  oracle_false_refl : ∀ (e : Expr) (s : ErasureState) (ctx : ErasureContext)
    (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld)
    (s₁ : ErasureState) (w₁ : Void IO.RealWorld),
    Erasure.liftMetaM (Erasure.isErasable ctx.lparams e) s ctx cctx ref w = .ok (false, s₁) w₁ →
    ctx.lparams = Us →
    M.run lenv.toKernelEnv .safe ctx.lctx ctx.lparams {}
      (RecM.run (LeanToLambdaBox.isErasable e)) ≠ .ok true
  /-- At an inductive-type head the pure kernel run answers `true`: the oracle's completeness
      at the one shape the fragment cannot exclude, reduced to the kernel arm. **Refuted in
      general** at a telescope of ≥ 256 binders — `Lean.Expr.Data.approxDepth` is 8 bits, so
      `isArityCheck`'s fuel is capped (`doc/rework/03-DEV-FIX.md`, F-DEPTH). Owner: this
      repository, wave W5; discharged by three executable-shape lemmas lean4lean does not have,
      plus a fuel that counts the reduced telescope. -/
  kernel_ind_head_true : ∀ (lctx : LocalContext) (m : MLCtx) (e : Expr) (c : Name)
      (us : List Level) (ve : VExpr) (iid : InductiveId) (np : Nat) (nfs : List Nat),
    m.WF env Us → m.lctx = lctx → (∀ fv ∈ m.vlctx.fvars, kernelNGen.Reserves fv) →
    e.getAppFn = .const c us → IndInfo env c iid np nfs → TrExprS env Us m.vlctx e ve →
    M.run lenv.toKernelEnv .safe lctx Us {} (RecM.run (LeanToLambdaBox.isErasable e)) = .ok true
  /-- The λ□ keys of a block's members are distinct. `Erasure.visitMutual` builds
      `fixvarMap (ci.all.map Erasure.remove_unsafe_rec) ids` and `Erasure.mkDef` reads it back
      by name, so a collapse here is a miscompilation, not a proof gap. **Refuted in general**
      by a legal `mutual unsafe def u / u._unsafe_rec` block
      (`doc/rework/03-DEV-FIX.md`, F-UNSAFEREC). Owner: this repository, wave W5; discharged by
      the one-line `Nodup` guard that finding proposes. -/
  block_keys_distinct : ∀ (n : Name) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) (ci : ConstantInfo)
    (w₁ : Void IO.RealWorld),
    Lean.Compiler.LCNF.getDeclInfo? n cctx ref w = .ok (some ci) w₁ →
    ((ci.all.map Erasure.remove_unsafe_rec).map toKername).Nodup

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

/-- **The type-former exclusion, derived.** A `false` verdict of `Erasure.isErasable` at the
ambient level scope rules out an inductive-type head: the two oracle clauses contradict each
other there. Stated at the `MLCtx`, so the three facts a bridge invariant supplies are
explicit arguments. -/
theorem EraserAsks.oracle_informative {lenv : Environment} {env : VEnv} {Us : List Name}
    {gw : Void IO.RealWorld → NameGenerator} (E : EraserAsks lenv env Us gw)
    {m : MLCtx} {ctx : ErasureContext} {e : Expr} {ve : VExpr} {s s₁ : ErasureState}
    {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State} {w w₁ : Void IO.RealWorld}
    (hm : m.WF env Us) (hlctx : m.lctx = ctx.lctx)
    (hfresh : ∀ fv ∈ m.vlctx.fvars, kernelNGen.Reserves fv)
    (hor : Erasure.liftMetaM (Erasure.isErasable ctx.lparams e) s ctx cctx ref w
      = .ok (false, s₁) w₁)
    (hlp : ctx.lparams = Us) (htr : TrExprS env Us m.vlctx e ve) :
    ∀ c us, e.getAppFn = .const c us → ∀ iid np nfs, ¬ IndInfo env c iid np nfs := by
  intro c us hfn iid np nfs hind
  refine E.oracle_false_refl e s ctx cctx ref w s₁ w₁ hor hlp ?_
  rw [hlp]
  exact E.kernel_ind_head_true ctx.lctx m e c us ve iid np nfs hm hlctx hfresh hfn hind htr

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
