import LeanToLambdaBox

/-!
A `casesOn` on an inductive that eliminates only into `Prop` (`Or`, `Exists`: its `casesOn` has no
universe parameter besides the inductive's) gives a proof, and `visitCases` erases it to □ (register
entry S-32). The traversal normally boxes such an application before it reaches `visitCases`. Here
the type `Y` has the sort `Sel true`, which is `Prop` only after `Bool.rec` reduces: the test
checks, under `nat := .peano`, that `test2` (an `Or.casesOn` with two alternatives) and `test` (an
`Exists.casesOn`) take the pure path, and `#erase` writes them to `or.ast` and `ex.ast`. The pure
oracle reduces the recursor (ι, register entry S-43) and boxes each constant itself, as the `Meta`
path's oracle does, so the program is □, which peregrine evaluates to □. Without the recursor
ι-rule, the oracle does not box the constants, `visitCases` erases their bodies to □, and the
program is a constant whose body is □; without that rule either, the pure path emits a λ□ `case` on
□ with two branches for `test2`, on which peregrine's evaluation is stuck, and `□ □ □` for `test`.
-/

-- peregrine: validate or.ast
-- peregrine: eval or.ast --anf=false
-- peregrine: validate ex.ast
-- peregrine: eval ex.ast --anf=false

open Lean Erasure
set_option linter.defProp false

namespace PEP
def Sel (b : Bool) : Type := Bool.casesOn (motive := fun _ => Type) b Prop Prop
def Y : Sel true := True
def w2 : True ∨ True := Or.inl trivial
def test2 : Y := Or.casesOn (motive := fun _ => Y) w2 (fun _ => trivial) (fun _ => trivial)
def wit : Exists (fun _ : Nat => True) := ⟨Nat.zero, trivial⟩
def test : Y := Exists.casesOn (motive := fun _ => Y) wit (fun _ _ => trivial)
end PEP

/-- The route of the constant `n` under `nat := .peano`. -/
def check (n : Name) : CoreM Unit := do
  let view := EnvView.ofEnvironment (← getEnv)
  match route view { nat := .peano } (.const n []) with
  | .viaPure (.ok _) => logInfo "viaPure ok"
  | .viaPure (.error err) => logInfo s!"viaPure error ({err.describe})"
  | .viaMeta => logInfo "viaMeta"

/-- info: viaPure ok -/
#guard_msgs in
#eval check ``PEP.test2
/-- info: viaPure ok -/
#guard_msgs in
#eval check ``PEP.test

#guard_msgs (drop warning, drop info) in
#erase PEP.test2 config {nat := .peano} to "or.ast"
#guard_msgs (drop warning, drop info) in
#erase PEP.test config {nat := .peano} to "ex.ast"
