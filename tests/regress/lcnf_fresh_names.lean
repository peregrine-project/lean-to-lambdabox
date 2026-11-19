import LeanToLambdaBox

/-!
`#erase_lcnf` must not depend on the name generator of the context it runs in. The variables that
stand for the members of a recursive component (`addFix`) are abstracted into de Bruijn indices; if
one of them coincides with a variable of the stored LCNF code, the code is abstracted at the wrong
binder. The LCNF code of a declaration keeps the names of the context that compiled it, so a run in
a context whose name generator is at the same name drew a colliding variable.

`#check_lcnf_fresh_names n` erases the recursive declaration `n` once as it is, and once with the
name generator set to each variable of `n`'s stored base-phase code, so that the first fresh name
is that variable, and requires the same program every time.
-/

open Lean Elab Command Lean.Compiler.LCNF

/-- The variables bound in a code: let declarations, local functions, join points, their parameters
and the parameters of the alternatives. -/
partial def lcnfFreshNamesVars : Code .pure → Array FVarId → Array FVarId
  | .let d k, acc => lcnfFreshNamesVars k (acc.push d.fvarId)
  | .fun d k _, acc =>
    lcnfFreshNamesVars k (lcnfFreshNamesVars d.value (acc.push d.fvarId ++ d.params.map (·.fvarId)))
  | .jp d k, acc =>
    lcnfFreshNamesVars k (lcnfFreshNamesVars d.value (acc.push d.fvarId ++ d.params.map (·.fvarId)))
  | .cases c, acc => c.alts.foldl (init := acc) fun acc alt => match alt with
    | .alt _ ps k _ => lcnfFreshNamesVars k (acc ++ ps.map (·.fvarId))
    | .default k => lcnfFreshNamesVars k acc
  | _, acc => acc

elab "#check_lcnf_fresh_names " n:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverload n
  let some (d : Decl .pure) ← liftCoreM <| getBaseDecl? name
    | throwError "{name} has no base-phase LCNF code"
  let ps : Array FVarId := d.params.map (fun (p : Param .pure) => p.fvarId)
  let vars : Array FVarId := match d.value with
    | .code c => lcnfFreshNamesVars c ps
    | .extern _ => ps
  let erase : CommandElabM String := do
    let p ← liftCoreM <| Erasure.FromLCNF.eraseDecl name .base {}
    return p |> Serialize.to_sexpr |>.toString
  let saved : NameGenerator := (← get).ngen
  let reference ← erase
  let mut differ : Array Name := #[]
  for x in vars do
    let .num pre i := x.name | continue
    let g : NameGenerator := { namePrefix := pre, idx := i }
    modify fun s => { s with ngen := g }
    if (← erase) != reference then differ := differ.push x.name
  modify fun s => { s with ngen := saved }
  unless differ.isEmpty do
    throwError m!"{name}: the program depends on the name generator ({differ.size} of {vars.size} variables give another program, first {toString differ[0]!})"
  IO.FS.writeFile s!"{name}.result" "same program\n"

def LcnfFreshNames.tri : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + LcnfFreshNames.tri n

#guard_msgs (drop info, drop warning) in
#check_lcnf_fresh_names LcnfFreshNames.tri
