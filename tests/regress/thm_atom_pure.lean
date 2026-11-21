import LeanToLambdaBox

/-!
The pure oracle `Erasure.Pure.isErasable` answers "erasable" on an application spine headed by a
theorem, whose statement Lean's kernel requires to be a proposition (register entry S-34). Here the
statement `Y` has the type `Sel true`, which is `Prop` only after `Bool.rec` reduces. The test
checks, under `nat := .peano`, over the declarations that `collectDeps` collects, that the oracle
erases `thm`, `thmF Nat.zero` and `use` (a definition whose type is `Y`: the oracle reduces
`Bool.rec`, ι, register entry S-43), that `use` and `useF` take the pure path, and `#erase` writes
them to `use.ast` and `useF.ast`: the program □ (the oracle boxes `use` and `useF`, as the `Meta`
path's oracle does), which peregrine evaluates to □ (printed `(FIX 0)`). Without the recursor
ι-rule the oracle keeps `use`, and the program is a constant whose body is □; without both rules
it answers `false` on both theorem spines, and the pure path stops with
`outside the fragment: unknown constant`.
-/

-- peregrine: validate use.ast
-- peregrine: eval use.ast --anf=false
-- peregrine: validate useF.ast
-- peregrine: eval useF.ast --anf=false

open Lean Erasure
set_option linter.defProp false

namespace TAP
def Sel (b : Bool) : Type := Bool.casesOn (motive := fun _ => Type) b Prop Prop
def Y : Sel true := True
theorem thm : Y := trivial
theorem thmF (_ : Nat) : Y := trivial
def use : Y := thm
def useF : Y := thmF Nat.zero
end TAP

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

/-- info: ok true -/
#guard_msgs in
#eval oracle ``TAP.use (.const ``TAP.thm [])
/-- info: ok true -/
#guard_msgs in
#eval oracle ``TAP.useF (.app (.const ``TAP.thmF []) (.const ``Nat.zero []))
/-- info: ok true -/
#guard_msgs in
#eval oracle ``TAP.use (.const ``TAP.use [])
/-- info: viaPure ok -/
#guard_msgs in
#eval check ``TAP.use
/-- info: viaPure ok -/
#guard_msgs in
#eval check ``TAP.useF

#guard_msgs (drop warning, drop info) in
#erase TAP.use config {nat := .peano} to "use.ast"
#guard_msgs (drop warning, drop info) in
#erase TAP.useF config {nat := .peano} to "useF.ast"
