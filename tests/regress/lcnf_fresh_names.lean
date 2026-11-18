import LeanToLambdaBox

/-!
`#erase_lcnf` must not depend on the name generator of the context it runs in. The variables that
stand for the members of a recursive component (`addFix`) are abstracted into de Bruijn indices; if
one of them coincides with a variable of the stored LCNF code, the code is abstracted at the wrong
binder. The LCNF code of a declaration keeps the `_uniq.N` names of the context that compiled it,
so a later run in a context whose name generator is at the same numbers drew colliding names.

`#check_lcnf_fresh_names n` erases the recursive declaration `n` once as it is, and once with the
name generator set to each of the numbers that the compilation of `n` drew, and requires the same
program every time.
-/

open Lean Elab Command

/-- Elaborate `d`, which defines `n`, then erase `n` with the name generator set to every number
that the elaboration and compilation of `d` drew; all programs must equal the first one. -/
elab "#check_lcnf_fresh_names " n:ident d:command : command => do
  let before := (← get).ngen
  elabCommand d
  let after := (← get).ngen
  let name ← liftCoreM <| realizeGlobalConstNoOverload n
  let erase : CommandElabM String := do
    let p ← liftCoreM <| Erasure.FromLCNF.eraseDecl name .base {}
    return p |> Serialize.to_sexpr |>.toString
  let reference ← erase
  let mut differ : Array Nat := #[]
  for i in [before.idx:after.idx + 1] do
    modify fun s => { s with ngen := { after with idx := i } }
    if (← erase) != reference then differ := differ.push i
  modify fun s => { s with ngen := after }
  if differ.isEmpty then
    IO.FS.writeFile s!"{name}.result" "same program\n"
    logInfo m!"{name}: the same program for every state of the name generator that its compilation drew"
  else
    throwError m!"{name}: the program depends on the name generator ({differ.size} of {after.idx + 1 - before.idx} states differ, first at _uniq.{differ[0]!})"

/-- info: LcnfFreshNames.tri: the same program for every state of the name generator that its compilation drew -/
#guard_msgs (info, drop warning) in
#check_lcnf_fresh_names LcnfFreshNames.tri
def LcnfFreshNames.tri : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + LcnfFreshNames.tri n
