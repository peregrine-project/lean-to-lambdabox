import LeanToLambdaBox

/-!
The pure oracle `Erasure.Pure.isErasable` answers "erasable" on an application spine headed by a
theorem, whose statement Lean's kernel requires to be a proposition (register entry S-34). Without
that rule the oracle misses such a proof when the sort of its statement is `Prop` only through a
recursor's ι, which `Pure.whnf` lacks: here the statement `Y` has the type `Sel true`, which is
`Prop` only after `Bool.rec` reduces. The test checks, under `nat := .peano`, over the declarations
that `collectDeps` collects, that the oracle erases `thm` and `thmF Nat.zero` and keeps `use`, that
`use` and `useF` take the pure path, and `#erase` writes them to `use.ast` and `useF.ast`: a
constant whose body is □, which peregrine evaluates to □ (printed `(FIX 0)`). Without the rule the
oracle answers `false` on both theorem spines, and the pure path stops with
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
/-- info: ok false -/
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
