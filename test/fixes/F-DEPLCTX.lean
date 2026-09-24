/-
Regression test for F-DEPLCTX.

`Erasure.visitMutual` re-enters a dependency under `withReader`, moving the fixvar map and the
level column. It used to leave `ErasureContext.lctx` alone, so a dependency's body — a *closed*
term — was erased under whatever local context the caller's term walk had open when it reached
the `.const` node, and every relevance verdict taken below ran lean4lean's checker at the pair

    (lctx := the caller's local context, lparams := the dependency's level column)

whose declarations may mention level parameters that column does not have. MetaRocq has no such
step: `erase_constant_body` (`../metarocq/erasure/theories/Extract.v:264`) erases `cst_body cb`
in the **empty** context at `cst_universes cb`.

The test asserts the invariant the fix installs, directly rather than through the emitted bytes:
*the registry a dependency is registered into does not depend on the caller's local context.*
`Erasure.get_constant_kername` is called twice at the same dependency — once from the empty
context, once from under two binders, the first of them typed `Sort (u+1)`, i.e. mentioning a
level parameter `u` that the dependency's column (`[]`) does not have, which is the finding's own
shape — and the two `gdecls` registries are compared byte for byte.

The second half is end-to-end: the `dep` entry of a program erased from a *caller* (a function
whose body references it, so the walk reaches the `.const` node under an open binder) is compared
with the entry the same constant gets erased standalone, and the caller's program is written to
`FIXES_AST_DIR` so that `scripts/fixes.sh` runs it through `peregrine validate` and
`peregrine eval`.

The edit is behaviour-preserving by construction — a closed body mentions no `fvar` of the
caller's context, and the `Meta` calls made on it are context-independent there — so this test
passes on both sides of it. It is a guard: the invariant is what the bridge needs in order to
rebuild `BridgeInv` at a member sub-run (`scratch/round7/U5-report.md` §5), and nothing else in
the suite would notice it being broken again.
-/
import LeanToLambdaBox.Erasure

open Lean Erasure

namespace FDepLctx

/-- The dependency: a closed, universe-monomorphic constant, level column `[]`. -/
def dep (n : Nat) : Nat := n + n

/-- The caller: a function whose body references `dep`, so the eraser holds the caller's own
binder in `lctx` when it reaches the `.const dep` node and registers the dependency. -/
def caller (n : Nat) : Nat := dep n + 1

/-- The erased subject: a closed term, so `peregrine eval` has a value to print (3). -/
def callerTest : Nat := caller 1

def cfg : ErasureConfig := { extern := .preferLogical, nat := .peano, csimp := false }

/-- Register `dep` and return the number of binders the caller's context held at the call
together with the serialized registry the run produced. With `underBinders`, the context holds
two: `x : Sort (u+1)`, mentioning a level parameter the dependency's column does not have, and
`y : Nat`. -/
def registryAt (underBinders : Bool) : CoreM (Nat × String) := do
  let body : EraseM (Nat × String) := do
    let n := (← read).lctx.getFVarIds.size
    let _ ← get_constant_kername ``dep
    return (n, (Serialize.to_sexpr (← get).gdecls).toString)
  let act : EraseM (Nat × String) :=
    if underBinders then
      withLocalDecl `x (.sort (.succ (.param `u))) .default fun _ =>
        withLocalDecl `y (.const ``Nat []) .default fun _ => body
    else body
  return (← run act cfg).1

/-- Erase the counter of every hygienic binder name (`…._hygCtx._hyg.93`). Those counters come
from the `CoreM` name generator, which advances globally: *two standalone runs* of the same
erasure disagree on them, whatever context they run in, so they are not a difference this test
can be about. Everything else — kernames, term structure, de Bruijn indices, argmasks — is
compared as it stands. -/
def normalizeHyg (s : String) : String :=
  match s.splitOn "_hyg." with
  | [] => s
  | p :: rest =>
    p ++ String.join (rest.map fun t => "_hyg.N" ++ String.ofList (t.toList.dropWhile Char.isDigit))

/-- The serialized entry `kn` has in the registry of `p`, `none` when it has none. -/
def entryOf (p : Program) (kn : Kername) : Option String :=
  let .untyped gdecls _ := p
  gdecls.find? (fun e => e.1 == kn) |>.map (fun e => (Serialize.to_sexpr e).toString)

#eval show CoreM Unit from do
  let (n0, reg0) ← registryAt false
  let (n1, reg1) ← registryAt true
  IO.println s!"F-DEPLCTX caller binders open at the call: standalone {n0}, under binders {n1}"
  IO.println s!"F-DEPLCTX registry identical: {normalizeHyg reg0 == normalizeHyg reg1} \
({(normalizeHyg reg0).length} bytes)"

  -- End to end: `callerTest` reaches `.const dep` inside `caller`'s body, i.e. under
  -- `caller`'s own binder, where erasing `dep` standalone reaches it at no binder at all.
  let (pCaller, _) ← erase (.const ``callerTest []) cfg
  let (pDep, _) ← erase (.const ``dep []) cfg
  let kn := toKername ``dep
  match entryOf pCaller kn, entryOf pDep kn with
  | some ec, some ed =>
    IO.println s!"F-DEPLCTX dep entry identical: {ec == ed} ({ed.length} bytes)"
  | _, _ => IO.println "F-DEPLCTX dep entry identical: MISSING"

  if let some dir ← IO.getEnv "FIXES_AST_DIR" then
    IO.FS.writeFile s!"{dir}/caller.ast" (Serialize.to_sexpr pCaller).toString

end FDepLctx
