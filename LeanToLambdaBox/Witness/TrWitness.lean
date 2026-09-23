import LeanToLambdaBox.Supported

/-!
# `TrExprS` witnesses for the ladder

The capstone binds the source term's translation, `hwt : TrExprS env [] [] e ve`, and the
value's typing, `hty`. This module inhabits them rather than assuming them.

Two routes, in decreasing strength:

* **From the reified table.** A rung's subject is `#erase c`, i.e. the source term
  `Expr.const c []`. `ErasureSpec.decl_adequate` sends the pinned declaration to a model
  constant, so `TrExprS env Us Δ (.const c []) (.const c [])` and — when the declared type is
  itself a constant — `env.HasType Us.length Δ.toCtx (.const c []) (.const T [])` follow from
  the hypotheses a rung already carries (`P`, `htbl`, `hsafe`), costing no binder. Feeding the
  first to `SEval.defeq` carries both to the value of a source evaluation; that composition
  belongs above `SubjectReduction.lean`, which this module deliberately does not import.
* **From the checker.** For a subject that is not a constant, `Lean4Lean.TypeChecker.checkType`
  reports a translation and its type: `checkType.WF` composed with lean4lean's own
  `M.WF.run'` (ambient-`MLCtx` run-adequacy, landed round 4) turns a successful pure run into
  `TrExprS` plus `HasType`. The run equation is then the binder, of the same executable kind as
  the rungs' `hrun`.

`natAdd_trExprS` instantiates the table route on a `reify%`d table, so the route is exercised
by a checked term and not only stated.
-/

namespace LeanToLambdaBox.Witness

open Lean Lean4Lean
open Lean4Lean.TypeChecker (MLCtx M checkType)

/-! ## The table route -/

/-- A constant `lenv` declares translates to the model constant of the same name, at any
modelled local context. The level arguments are translated by `hls`, and `hlen` is the arity
condition read at the declaration's own level parameters. -/
theorem trExprS_const {lenv : Environment} {env : VEnv} {Us : List Name}
    {gw : Void IO.RealWorld → NameGenerator} (P : ErasureSpec lenv env Us gw)
    {n : Name} {ci : ConstantInfo} {Δ : VLCtx} {ls : List Level} {ls' : List VLevel}
    (hfind : lenv.find? n = some ci) (hsf : DefinitionSafety.safe ≤ ci.safety)
    (hls : ls.mapM (VLevel.ofLevel Us) = some ls')
    (hlen : ls.length = ci.levelParams.length) :
    TrExprS env Us Δ (.const n ls) (.const n ls') := by
  obtain ⟨vc, hvc, -, huv, -⟩ := P.decl_adequate n ci hfind hsf
  exact .const hvc hls (hlen.trans huv)

/-- The monomorphic instance of `trExprS_const`: a constant with no level parameters, applied
to no level arguments, is its own translation. -/
theorem trExprS_const_nil {lenv : Environment} {env : VEnv} {Us : List Name}
    {gw : Void IO.RealWorld → NameGenerator} (P : ErasureSpec lenv env Us gw)
    {n : Name} {ci : ConstantInfo} {Δ : VLCtx}
    (hfind : lenv.find? n = some ci) (hsf : DefinitionSafety.safe ≤ ci.safety)
    (hlp : ci.levelParams = []) :
    TrExprS env Us Δ (.const n []) (.const n []) :=
  trExprS_const P hfind hsf rfl (by simp [hlp])

/-- The declared type of a monomorphic constant, read in the model. Inverting the translation
of the declaration's type identifies it with the source type when that type is a constant, so
the model types the subject at the same constant. -/
theorem hasType_const_nil {lenv : Environment} {env : VEnv} {Us : List Name}
    {gw : Void IO.RealWorld → NameGenerator} (P : ErasureSpec lenv env Us gw)
    {n T : Name} {ci : ConstantInfo} {Γ : List VExpr}
    (hfind : lenv.find? n = some ci) (hsf : DefinitionSafety.safe ≤ ci.safety)
    (hlp : ci.levelParams = []) (hty : ci.type = .const T []) :
    env.HasType Us.length Γ (.const n []) (.const T []) := by
  obtain ⟨⟨uv, vty⟩, hvc, -, huv, htr⟩ := P.decl_adequate n ci hfind hsf
  rw [hty] at htr
  cases htr with
  | const _h1 h2 _h3 =>
    rename_i us'
    cases (by simpa using h2.symm : us' = ([] : List VLevel))
    have hlen : ([] : List Level).length
        = ({ uvars := uv, type := VExpr.const T [] } : VConstant).uvars := by
      rw [← huv, hlp]; rfl
    simpa [VExpr.instL] using
      VEnv.HasType.const (env := env) (U := Us.length) (Γ := Γ) hvc (by simp) hlen

/-! ### At a rung's reified table -/

/-- A tabled constant is pinned in `lenv`: the environment knows it, at a safety the
specification bundle accepts, with the level parameters and the type the table records. -/
theorem tableDeclPin {lenv : Environment} {tbl : SourceTable} {n : Name} {d : ReifiedDecl}
    (htbl : SourceTableAdequate lenv tbl) (hsafe : TableSafe lenv tbl)
    (hd : tbl.decl? n = some d) :
    ∃ ci : ConstantInfo, lenv.find? n = some ci ∧ DefinitionSafety.safe ≤ ci.safety
      ∧ ci.levelParams = d.levelParams ∧ ci.type = d.type := by
  obtain ⟨ci, hfind, hlp, hty⟩ := (htbl.decls n d (mem_of_lookup hd)).1
  exact ⟨ci, hfind, hsafe.decls n ci (by rw [hd]; rfl) hfind, hlp, hty⟩

/-- The subject of a rung whose `#erase` names a tabled monomorphic constant translates to the
model constant of that name. `hlp` is `by rfl` on the reified table, and `P`, `htbl`, `hsafe`
are hypotheses the rung already carries, so the translation costs no binder. -/
theorem trExprS_const_of_table {lenv : Environment} {env : VEnv} {Us : List Name}
    {gw : Void IO.RealWorld → NameGenerator} (P : ErasureSpec lenv env Us gw)
    {tbl : SourceTable} (htbl : SourceTableAdequate lenv tbl) (hsafe : TableSafe lenv tbl)
    {n : Name} {Δ : VLCtx}
    (hlp : (tbl.decl? n).map ReifiedDecl.levelParams = some []) :
    TrExprS env Us Δ (.const n []) (.const n []) := by
  cases hdn : tbl.decl? n with
  | none => rw [hdn] at hlp; exact absurd hlp (by simp)
  | some d =>
    rw [hdn] at hlp
    obtain ⟨ci, hfind, hs, hlpci, -⟩ := tableDeclPin htbl hsafe hdn
    exact trExprS_const_nil P hfind hs (hlpci.trans (by simpa using hlp))

/-- The same subject, typed in the model at the constant the table records as its type. Rungs
whose subject is function-typed fall outside this lemma; their translation still comes from
`trExprS_const_of_table`. -/
theorem hasType_const_of_table {lenv : Environment} {env : VEnv} {Us : List Name}
    {gw : Void IO.RealWorld → NameGenerator} (P : ErasureSpec lenv env Us gw)
    {tbl : SourceTable} (htbl : SourceTableAdequate lenv tbl) (hsafe : TableSafe lenv tbl)
    {n T : Name} {Γ : List VExpr}
    (hlp : (tbl.decl? n).map ReifiedDecl.levelParams = some [])
    (hty : (tbl.decl? n).map ReifiedDecl.type = some (.const T [])) :
    env.HasType Us.length Γ (.const n []) (.const T []) := by
  cases hdn : tbl.decl? n with
  | none => rw [hdn] at hlp; exact absurd hlp (by simp)
  | some d =>
    rw [hdn] at hlp hty
    obtain ⟨ci, hfind, hs, hlpci, htyci⟩ := tableDeclPin htbl hsafe hdn
    exact hasType_const_nil P hfind hs (hlpci.trans (by simpa using hlp))
      (htyci.trans (by simpa using hty))

/-! ## The checker route -/

/-- **A successful pure run of the checker reports a translation.** `checkType.WF` states the
translation and its typing at an abstract `VContext`; lean4lean's `M.WF.run'` supplies the
initial state at an ambient `MLCtx`, so an `M.run` returning `.ok ty` witnesses that the subject
and the reported type both translate, at that ambient context. -/
theorem trTyping_of_checkType_run {kenv : Kernel.Environment} {ves : VEnvs} (wf : ves.WF kenv)
    {safety : DefinitionSafety} {lparams : List Name} {fuel : FuelConfig}
    {m : MLCtx} (mwf : m.WF (ves.venv safety) lparams)
    (hfresh : ∀ fv ∈ m.vlctx.fvars, kernelNGen.Reserves fv)
    {e ty : Expr} (hfv : e.FVarsIn (· ∈ m.vlctx.fvars))
    (hrun : M.run kenv safety m.lctx lparams fuel (checkType e) = .ok ty) :
    ∃ ve vty, TrExprS (ves.venv safety) lparams m.vlctx e ve
      ∧ TrExprS (ves.venv safety) lparams m.vlctx ty vty
      ∧ (ves.venv safety).HasType lparams.length m.vlctx.toCtx ve vty := by
  obtain ⟨ve, vty, -, h1, h2, h3⟩ :=
    Lean4Lean.TypeChecker.M.WF.run' wf mwf hfresh
      (Lean4Lean.TypeChecker.checkType.WF
        (c := .ofMLCtx wf safety lparams m mwf (fuel := fuel)) hfv)
      ty hrun
  exact ⟨ve, vty, h1, h2, h3⟩

/-- The closed instance of `trTyping_of_checkType_run`, at the specification bundle's own model
connection: a closed source term the checker accepts at the empty local context translates, with
its reported type, in `env`. The run equation is the binder — executable, unlike the translation
it replaces. -/
theorem trTyping_of_checkType_run_closed {lenv : Environment} {env : VEnv} {Us : List Name}
    {gw : Void IO.RealWorld → NameGenerator} (P : ErasureSpec lenv env Us gw)
    {fuel : FuelConfig} {e ty : Expr} (hfv : e.FVarsIn fun _ => False)
    (hrun : M.run lenv.toKernelEnv .safe {} Us fuel (checkType e) = .ok ty) :
    ∃ ve vty, TrExprS env Us [] e ve ∧ TrExprS env Us [] ty vty
      ∧ env.HasType Us.length [] ve vty := by
  obtain ⟨ves, hwf, rfl⟩ := P.env_connect
  exact trTyping_of_checkType_run hwf (m := .nil) trivial nofun (hfv.mono nofun) hrun

/-! ## The route, exercised -/

/-- A reified table of a real monomorphic constant, standing outside the ladder so that the
table route is checked here rather than only at a rung. -/
def natAddTable : SourceTable := reify% Nat.add

/-- `Nat.add` translates to the model constant of the same name, its one side condition
computed by the kernel off the reified table. This is the shape every rung's `hwt` has. -/
theorem natAdd_trExprS {lenv : Environment} {env : VEnv} {Us : List Name}
    {gw : Void IO.RealWorld → NameGenerator} (P : ErasureSpec lenv env Us gw)
    (htbl : SourceTableAdequate lenv natAddTable) (hsafe : TableSafe lenv natAddTable)
    {Δ : VLCtx} :
    TrExprS env Us Δ (.const ``Nat.add []) (.const ``Nat.add []) :=
  trExprS_const_of_table P htbl hsafe rfl

end LeanToLambdaBox.Witness
