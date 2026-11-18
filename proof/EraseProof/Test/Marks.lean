import EraseProof.Statements

/-!
# Checks of the marks

By `rfl`: `unmark` strips `erase`/`reduced` marks and η-contracts the `eta`-marked expansion
`MarkOf` writes for an under-applied spine; marks are transparent to `toCL?`; `MarksCert` asks
`CLCert` of a mark in the context of its enclosing binders, and `lamTele` closes a context.
-/

open Lean Erasure

namespace EraseProof.Test

/-- `c` with two missing arguments, η-expanded as `MarkEta.intro` writes it (the second argument
marked erased), unmarks to `c`. -/
example : unmark (markEta (.lam `x (.sort 1) (markEta (.lam `y (.bvar 0)
    (mkAppN (.const `c []) #[.bvar 1, markErase (.bvar 0)]) .default)) .default)) =
    .const `c [] := rfl

/-- An η-expansion whose variable occurs in the head is not contracted. -/
example : unmark (markEta (.lam `x (.sort 1) (.app (.bvar 0) (.bvar 0)) .default)) =
    .lam `x (.sort 1) (.app (.bvar 0) (.bvar 0)) .default := rfl

/-- The reduced form's discriminant is unmarked; other metadata is kept. -/
example : unmark (.app (markReduced (.const `d [])) (.mdata {} (markErase (.const `a [])))) =
    .app (.const `d []) (.mdata {} (.const `a [])) := rfl

/-- Marks are transparent to `toCL?`. -/
example : toCL? (markErase (.app (markEta (.const `f [])) (markReduced (.bvar 0)))) =
    toCL? (.app (.const `f []) (.bvar 0)) := rfl

/-- A mark under an `eta`-marked λ and a λ is certified in the context of both binders, innermost
first. -/
example (env : ConLeche.Env) (A B s : Expr) :
    MarksCert env [] (markEta (.lam `x A (.lam `y B (.app (.const `f []) (markErase s)) .default) .default)) =
      (True ∧ CLCert env [(B, none), (A, none)] s) := rfl

/-- A `let` body's marks are certified with the `let`'s value in the context, and the discriminant
of a reduced `casesOn` is certified. -/
example (env : ConLeche.Env) (T s d : Expr) :
    MarksCert env [] (.letE `x T (.const `v []) (.app (markErase s) (markReduced d)) false) =
      (True ∧ CLCert env [(T, some (.const `v []))] s ∧ CLCert env [(T, some (.const `v []))] d) :=
  rfl

/-- The context of a mark closes it by λs and `let`s, outermost binder first. -/
example (A T v s : Expr) :
    lamTele [(T, some v), (A, none)] s =
      .lam .anonymous A (.letE .anonymous T v s false) .default := rfl

end EraseProof.Test
