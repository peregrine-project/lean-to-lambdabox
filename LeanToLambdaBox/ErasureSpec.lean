import LeanToLambdaBox.CheckerAdequacy
import LeanToLambdaBox.ErasureRun
import LeanToLambdaBox.Closed
import LeanToLambdaBox.Semantics.Eval

/-!
# `ErasureSpec` — the one specification bundle

Everything the verification assumes about the *impure* primitives the shipping erasure calls:
the elaboration environment `lenv` is modelled by the `VEnv` `env`, the environment lookups
report what `lenv` holds, `mkFreshFVarId` is fresh, and the relevance oracle is sound.

Four of the six fields are about primitives no term denotes (`Lean.Environment`, `CoreM`,
`MetaM`, `Void IO.RealWorld`); each says so in its own docstring. The two oracle fields are the
only ones with a *proved* branch: `ErasureSpec.oracle_sound_of_run` discharges the kernel arm
through `Oracle.kernel_isErasable_sound`, so what stays assumed there is the reflection of the
impure `MetaM` run onto the pure `M.run`, the `Erasure.isErasableMeta` fallback, and runs at a
level scope other than the ambient one.

`SourceTable` adequacy is deliberately **not** a field: a `Prop`-valued structure cannot hold a
table as data, and an unbound table in a field auto-binds to a universal quantifier that no
table satisfies. It is the separate named hypothesis `Witness.SourceTableAdequate`.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean Erasure
open Lean4Lean.TypeChecker (MLCtx kernelNGen M RecM)

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

/-! ## Lookup adequacy -/

/-- The environment queries the erasure makes report what `lenv` holds, and none of them
advances the name generator. Class **D**: `Lean.Environment` is an opaque primitive with a
private constructor, so no term denotes it and no statement about `getConstInfo` can be
discharged inside Lean.

The four queries are the four the erasure uses: `Lean.getConstInfo` (every constant),
`Lean.Compiler.LCNF.getDeclInfo?` (the compiler-facing declaration `Erasure.visitMutual`
erases), `Lean.Compiler.LCNF.getCtorArity?` and `Lean.Meta.getCasesInfo?` (the constructor and
`casesOn` recognisers `Erasure.visitConstApp` consults). -/
structure LookupAdequate (lenv : Environment) (gw : Void IO.RealWorld → NameGenerator) : Prop where
  /-- `getConstInfo n` returns `lenv`'s own declaration for `n`. -/
  constInfo : ∀ (n : Name) (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State)
    (w : Void IO.RealWorld) (ci : ConstantInfo) (w₁ : Void IO.RealWorld),
    (getConstInfo n : CoreM ConstantInfo) cctx ref w = .ok ci w₁ →
    gw w ≤ gw w₁ ∧ lenv.find? n = some ci
  /-- `getDeclInfo?` answers for a name `lenv` knows, and only for such a name. -/
  declInfo : ∀ (n : Name) (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State)
    (w : Void IO.RealWorld) (r : Option ConstantInfo) (w₁ : Void IO.RealWorld),
    Lean.Compiler.LCNF.getDeclInfo? n cctx ref w = .ok r w₁ →
    gw w ≤ gw w₁ ∧ (r ≠ none → lenv.find? n ≠ none)
  /-- `getCtorArity?` answers exactly for the constructors `lenv` declares, at their
      parameter-plus-field arity. -/
  ctorArity : ∀ (n : Name) (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State)
    (w : Void IO.RealWorld) (r : Option Nat) (w₁ : Void IO.RealWorld),
    Lean.Compiler.LCNF.getCtorArity? n cctx ref w = .ok r w₁ →
    gw w ≤ gw w₁ ∧ ∀ a, r = some a →
      ∃ cv : ConstructorVal, lenv.find? n = some (.ctorInfo cv) ∧ a = cv.numParams + cv.numFields
  /-- `getCasesInfo?` answers only for names `lenv` knows. -/
  casesInfo : ∀ (n : Name) (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State)
    (w : Void IO.RealWorld) (r : Option Lean.CasesInfo) (w₁ : Void IO.RealWorld),
    Lean.getCasesInfo? n cctx ref w = .ok r w₁ →
    gw w ≤ gw w₁ ∧ (r ≠ none → lenv.find? n ≠ none)

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
