/-
The vacuity regression, in both directions, at the shape that made the finding: a body whose
λ-domain mentions a level parameter.

Erasure of such a body has no derivation at the **empty** level scope. That is what made
`ErasesEnv.defns`' old level quantifier — `∀ Us' ups us, Erases env Us' [] (b.instantiateLevelParams
ups us) b₀`, read at `Us' = ups = us = []` — unsatisfiable at every tabled constant with such a
body, and so made the rungs carrying it vacuous.

The clause is stated at the declaration's own level scope instead (`erases_constant_body (Σ,
cst_universes cb)`, `../metarocq/erasure/theories/Extract.v:264`), and the instantiated reading
is derived where it is spent, by `Erases.instantiateLevelParams`. The second half of this file
is the positive counterpart: at that scope the same body does erase, and its erasure transports
to any reading scope, so the refutation pattern no longer applies to the clause.

The clause-level refutation itself is deliberately absent: after the restatement the
universally quantified clause does not exist, so a theorem refuting it would not elaborate.

Run with `lake env lean test/Vacuity.lean`; not wired into the battery.
-/
import LeanToLambdaBox

open Lean Lean4Lean

namespace LeanToLambdaBox.Vacuity

/-! ## What no level scope can give -/

/-- A sort mentioning a level parameter has no translation at the empty level scope:
`TrExprS.sort` requires `VLevel.ofLevel [] (.succ (.param u))` to be `some`, and it is
`none`. -/
theorem no_trExprS_sort_param {env : VEnv} {Δ : VLCtx} {u : Name} {v : VExpr} :
    ¬ TrExprS env [] Δ (.sort (.succ (.param u))) v := by
  intro h
  cases h with | sort hl => simp [Lean4Lean.VLevel.ofLevel] at hl

/-- **No erasure at the empty level scope of a λ over a parameter-carrying sort.** `Erases`
has two arms at a λ source: `lam`, whose `hty` is the domain's translation, and `box`, whose
`htr` carries it through `TrExprS.lam`. Both need the domain's level in scope. -/
theorem no_erases_lam_sort_param {env : VEnv} {n u : Name} {b : Expr} {bi : BinderInfo}
    {t : LBTerm} :
    ¬ Erases env [] [] (.lam n (.sort (.succ (.param u))) b bi) t := by
  intro h
  cases h with
  | box htr _ => cases htr with | lam _ hd _ => exact no_trExprS_sort_param hd
  | lam hd _ => exact no_trExprS_sort_param hd

/-! ## What the declaration's own level scope does give -/

/-- **The same body erases at its own level scope.** This is the shape of every polymorphic
tabled body of the rungs — `OfNat.ofNat`, `HAdd.hAdd`, `Prod.fst` — and the shape
`no_erases_lam_sort_param` refutes one scope below. -/
theorem erases_lam_sort_param_own_scope (env : VEnv) (n : Name) (bi : BinderInfo) :
    Erases env [`u] [] (.lam n (.sort (.succ (.param `u))) (.bvar 0) bi)
      (.lambda (.named n.toString) (.bvar 0)) :=
  .lam (ty' := .sort (.succ (.param 0))) (.sort rfl)
    (.bvar (e' := (VLocalDecl.vlam (.sort (.succ (.param 0)))).value)
      (A := (VLocalDecl.vlam (.sort (.succ (.param 0)))).type) rfl)

/-- **The restated `defns` clause is inhabited there.** With the level column answering the
declaration's own parameters, the erasure the clause demands exists at a body the old clause
demanded one at the empty scope for. -/
theorem defns_clause_inhabited (env : VEnv) (n c : Name) (bi : BinderInfo)
    (lp : Name → List Name) (hlp : lp c = [`u]) :
    ∃ b₀ : LBTerm, Erases env (lp c) [] (.lam n (.sort (.succ (.param `u))) (.bvar 0) bi) b₀ :=
  ⟨_, hlp ▸ erases_lam_sort_param_own_scope env n bi⟩

/-- **And it transports to the scope the δ arm reads it at.** `Erases.instantiateLevelParams`
at the instance `[0]`, whose `consistent_instance_ext` content holds at every reading scope.
The λ□ image is the same term, so the δ arm is served without the environment being asked for
an erasure at a scope the body's own parameter is not in. -/
theorem erases_lam_sort_param_instantiated (env : VEnv) (Us : List Name) (n : Name)
    (bi : BinderInfo) :
    Erases env Us []
      ((Expr.lam n (.sort (.succ (.param `u))) (.bvar 0) bi).instantiateLevelParams
        [`u] [.zero])
      (.lambda (.named n.toString) (.bvar 0)) :=
  Erases.instantiateLevelParams (us' := [.zero]) rfl rfl
    (erases_lam_sort_param_own_scope env n bi) ⟨trivial, trivial⟩

end LeanToLambdaBox.Vacuity

#print axioms LeanToLambdaBox.Vacuity.no_trExprS_sort_param
#print axioms LeanToLambdaBox.Vacuity.no_erases_lam_sort_param
#print axioms LeanToLambdaBox.Vacuity.erases_lam_sort_param_own_scope
#print axioms LeanToLambdaBox.Vacuity.defns_clause_inhabited
#print axioms LeanToLambdaBox.Vacuity.erases_lam_sort_param_instantiated
