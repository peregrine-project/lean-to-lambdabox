/-
The vacuity regression: erasure has no derivation at the **empty** level scope for a body
whose λ-domain mentions a level parameter.

This is the fact that made `ErasesEnv.defns`' level quantifier — `∀ Us' ups us, Erases env
Us' [] (b.instantiateLevelParams ups us) b₀`, read at `Us' = ups = us = []` — unsatisfiable at
every tabled constant with such a body, and so made the rungs carrying it vacuous. The clause
is stated at the declaration's own level scope instead (`erases_constant_body (Σ, cst_universes
cb)`, `../metarocq/erasure/theories/Extract.v:264`), and the instantiated reading is derived
where it is needed, by `Erases.instL`.

Only the general lemma is kept. The clause-level refutation is deliberately absent: after the
restatement the universally quantified clause no longer exists, so a theorem refuting it would
not elaborate. What a future level-scope clause must respect is the lemma below — a clause
demanding an erasure at a scope the body's own parameters are not in is unsatisfiable.

Run with `lake env lean test/Vacuity.lean`; not wired into the battery.
-/
import LeanToLambdaBox

open Lean Lean4Lean

namespace LeanToLambdaBox.Vacuity

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

end LeanToLambdaBox.Vacuity

#print axioms LeanToLambdaBox.Vacuity.no_trExprS_sort_param
#print axioms LeanToLambdaBox.Vacuity.no_erases_lam_sort_param
