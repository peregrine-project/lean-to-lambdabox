import LeanToLambdaBox

/-!
A quotient that identifies distinct values: unordered pairs of `B`, as `B × B` modulo
`(a, b) ~ (b, a)`, and `orU : Quot swapR → B`, the lift of `orB` along its commutativity.
The other quotient tests use `Eq` as the relation, so none of them identifies two values.

Here `(B.t, B.f)` and `(B.f, B.t)` are distinct pairs (`ne_tf`) with equal classes (`sound_tf`, by
`Quot.sound`), and the respect proof of `orU` is the theorem `orB_comm` (by cases), erased to □.
The lifted function reads both projections of the pair, through `Prod`'s projections, and
matches on `B` (`orB.match_1`, a `casesOn`).

The test checks, under `nat := .peano`, the oracle's answers on the quotient type, on a class
and on `orU`, that the three programs take the pure path, and `#erase` writes them:
- `useTF`: `orU` on the class of `(B.t, B.f)`;
- `useFT`: `orU` on the class of `(B.f, B.t)`, the same class, with the other representative;
- `useFF`: `orU` on the class of `(B.f, B.f)`.
peregrine evaluates them to `QP.B.t`, `QP.B.t` and `QP.B.f`: the erased programs give one value
on the two representatives of one class.
-/

-- peregrine: validate useTF.ast
-- peregrine: eval useTF.ast
-- peregrine: validate useFT.ast
-- peregrine: eval useFT.ast
-- peregrine: validate useFF.ast
-- peregrine: eval useFF.ast

open Lean Erasure

set_option linter.defProp false

namespace QP

inductive B | f | t

def orB : B → B → B
  | .f, b => b
  | .t, _ => .t

/-- `(a, b)` is related to `(b, a)`, so `Quot swapR` is the type of unordered pairs. -/
def swapR (p q : B × B) : Prop := q = (p.2, p.1)

theorem orB_comm (a b : B) : orB a b = orB b a := by
  cases a <;> cases b <;> rfl

/-- `orB` on unordered pairs, well defined because `orB` is commutative. -/
def orU : Quot swapR → B :=
  Quot.lift (fun p => orB p.1 p.2) (fun p q h => by subst h; exact orB_comm p.1 p.2)

def useTF : B := orU (Quot.mk swapR (B.t, B.f))
def useFT : B := orU (Quot.mk swapR (B.f, B.t))
def useFF : B := orU (Quot.mk swapR (B.f, B.f))

theorem ne_tf : (B.t, B.f) ≠ (B.f, B.t) := by intro h; cases h
theorem sound_tf : Quot.mk swapR (B.t, B.f) = Quot.mk swapR (B.f, B.t) := Quot.sound rfl

example : useTF = B.t := rfl
example : useFT = B.t := rfl
example : useFF = B.f := rfl

end QP

/-- The oracle's answer on `e` over the closure of the constant `n`, under `nat := .peano`. -/
def oracle (n : Name) (e : Expr) : CoreM Unit := do
  match collectDeps (EnvView.ofEnvironment (← getEnv)) { nat := .peano } (.const n []) with
  | .error err => logInfo s!"collectDeps error ({err.describe})"
  | .ok ds => match Pure.isErasable ⟨ds⟩ oracleFuel [] e with
    | .ok b => logInfo s!"ok {b}"
    | .error err => logInfo s!"error ({err.describe})"

/-- The route of the constant `n` under `nat := .peano`. -/
def check (n : Name) : CoreM Unit := do
  let view := EnvView.ofEnvironment (← getEnv)
  match route view { nat := .peano } (.const n []) with
  | .viaPure (.ok _) => logInfo "viaPure ok"
  | .viaPure (.error err) => logInfo s!"viaPure error ({err.describe})"
  | .viaMeta => logInfo "viaMeta"

/-- `B × B` at universe 0, `Quot.{1} (B × B) QP.swapR` and `@Quot.mk.{1} (B × B) QP.swapR`. -/
def pairB : Expr := mkApp2 (.const ``Prod [0, 0]) (.const ``QP.B []) (.const ``QP.B [])
def quotP : Expr := mkApp2 (.const ``Quot [1]) pairB (.const ``QP.swapR [])
def mkP : Expr := mkApp2 (.const ``Quot.mk [1]) pairB (.const ``QP.swapR [])
def tf : Expr :=
  mkApp4 (.const ``Prod.mk [0, 0]) (.const ``QP.B []) (.const ``QP.B [])
    (.const ``QP.B.t []) (.const ``QP.B.f [])

/-- info: ok true -/
#guard_msgs in
#eval oracle ``QP.useTF quotP
/-- info: ok false -/
#guard_msgs in
#eval oracle ``QP.useTF (.app mkP tf)
/-- info: ok false -/
#guard_msgs in
#eval oracle ``QP.useTF (.const ``QP.orU [])

/-- info: viaPure ok -/
#guard_msgs in
#eval check ``QP.useTF
/-- info: viaPure ok -/
#guard_msgs in
#eval check ``QP.useFT
/-- info: viaPure ok -/
#guard_msgs in
#eval check ``QP.useFF

#guard_msgs (drop warning, drop info) in
#erase QP.useTF config {nat := .peano} to "useTF.ast"
#guard_msgs (drop warning, drop info) in
#erase QP.useFT config {nat := .peano} to "useFT.ast"
#guard_msgs (drop warning, drop info) in
#erase QP.useFF config {nat := .peano} to "useFF.ast"
