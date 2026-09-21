import Lean4Lean.TypeChecker

/-!
# The erasure relevance check on lean4lean's verified checker (executable)

The *executable* relevance decision the erasure uses: is a term irrelevant (a
proof, or a type-former)? decided by lean4lean's kernel `inferType` followed by
its `isProp` (proof) or a `∀`-telescope arity check (type-former) on the inferred
type — the direct analogue of the shipping `Meta.isProp ∨ Meta.isTypeFormerType`.

This module deliberately imports **only** lean4lean's executable `TypeChecker`
(not its `Verify` metatheory), so the shipping erasure can call it without pulling
in the (heavy, partly-`sorry`) verification layer. The **soundness** of these
checks against lean4lean's `HasType` judgment (`isErasable.WF`) lives separately in
`RelevanceCheck.lean`, which imports `Verify` and refers back to these definitions.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean
open Lean4Lean.TypeChecker.Inner

/-- Proof branch: infer the type of `e`, then ask lean4lean's `isProp` whether that
    type is a `Prop`. -/
def isErasableProp (e : Expr) : Lean4Lean.TypeChecker.RecM Bool := do
  let ty ← inferType e
  isProp ty

/-- Peel the `∀`-telescope of `ty` (whnf at each step): succeed iff it ends in a
    sort. `fuel` bounds the depth; running out throws, so the caller's `.error`
    arm (the elaborator fallback) decides instead of a spurious `false`. -/
def isArityCheck.loop (fuel : Nat) (ty : Expr) : Lean4Lean.TypeChecker.RecM Bool := do
  match fuel with
  | 0 => throw <| .other "isArityCheck: fuel exhausted"
  | fuel + 1 =>
    match ← whnf ty with
    | .forallE name dom body bi =>
        withLocalDecl name bi dom fun x => isArityCheck.loop fuel (body.instantiate1 x)
    | .sort _ => return true
    | _ => return false

/-- Type-former branch: whnf-reduce and peel the whole `∀`-telescope of `ty`,
    succeeding iff it ends in a sort (faithful to `Meta.isTypeFormerType`). Fuelled
    by a fixed budget, not by `ty`'s own (unreduced, 8-bit-saturating) syntactic
    depth: the loop's binder count is the *reduced* telescope's, which a definitional
    alias can hide entirely behind a zero-depth `.const` head, so no bound on the
    unreduced subject bounds it. If the reduced telescope still exceeds the budget,
    the loop throws and `Erasure.isErasable` falls back to `isErasableMeta`. -/
def isArityCheck (ty : Expr) : Lean4Lean.TypeChecker.RecM Bool :=
  isArityCheck.loop 100000 ty

/-- The full erasure relevance oracle on lean4lean's verified checker: infer the
    type of `e`, then succeed if that type is a `Prop` (proof) *or* passes the arity
    check (type-former). -/
def isErasable (e : Expr) : Lean4Lean.TypeChecker.RecM Bool := do
  let ty ← inferType e
  if (← isProp ty) then return true else isArityCheck ty

end LeanToLambdaBox
