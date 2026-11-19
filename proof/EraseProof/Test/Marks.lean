import EraseProof.Statements

/-!
# Checks of the marks

By `rfl`: substitution keeps marks in place, and `unmark_instantiate1'` needs `EtaLams`; `unmark`
strips `erase`/`reduced` marks and η-contracts the `eta`-marked expansion `MarkOf` writes for an
under-applied spine; marks are transparent to `toCL?`; `MarksCert` asks
`CLCert` of a mark (`CLCertProof` of a reduced discriminant) in the context of its enclosing
binders, and `lamTele` closes a context.
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

/-- Substitution and universe instantiation keep the marks in place (marks are metadata). -/
example (s a : Expr) (d k : Nat) (ps : List Name) (us : List Level) :
    (markErase s).instantiate1' a d = markErase (s.instantiate1' a d) ∧
    (markEta s).liftLooseBVars' d k = markEta (s.liftLooseBVars' d k) ∧
    Pure.instLevels ps us (markReduced s) = markReduced (Pure.instLevels ps us s) :=
  ⟨rfl, rfl, rfl⟩

/-- An `eta` mark on the substituted variable is contracted after the substitution of `λ x. f x`
… -/
example : unmark ((markEta (.bvar 0)).instantiate1'
    (.lam `x (.sort 0) (.app (.const `f []) (.bvar 0)) .default)) = .const `f [] := rfl

/-- … and not before it: `unmark_instantiate1'` asks that `eta` marks sit on λs (`EtaLams`). -/
example : (unmark (markEta (.bvar 0))).instantiate1'
    (unmark (.lam `x (.sort 0) (.app (.const `f []) (.bvar 0)) .default)) =
    .lam `x (.sort 0) (.app (.const `f []) (.bvar 0)) .default := rfl

/-- A mark under an `eta`-marked λ and a λ is certified in the context of both binders, innermost
first. -/
example (env : ConLeche.Env) (A B s : Expr) :
    MarksCert env [] (markEta (.lam `x A (.lam `y B (.app (.const `f []) (markErase s)) .default) .default)) =
      (True ∧ CLCert env [(B, none), (A, none)] s) := rfl

/-- A `let` body's marks are certified with the `let`'s value in the context, and the discriminant
of a reduced `casesOn` is certified as a proof. -/
example (env : ConLeche.Env) (T s d : Expr) :
    MarksCert env [] (.letE `x T (.const `v []) (.app (markErase s) (markReduced d)) false) =
      (True ∧ CLCert env [(T, some (.const `v []))] s ∧ CLCertProof env [(T, some (.const `v []))] d) :=
  rfl

/-- The context of a mark closes it by λs and `let`s, outermost binder first. -/
example (A T v s : Expr) :
    lamTele [(T, some v), (A, none)] s =
      .lam .anonymous A (.letE .anonymous T v s false) .default := rfl

end EraseProof.Test
