import LeanToLambdaBox
import EraseProof.Test.NV1Run

/-!
# NV-1's emitted program, for check C11

Run from `proof/` as `lake env lean --run tools/NV1Emit.lean FILE`. It adds the declarations of
the non-vacuity instance NV-1 (`EraseProof.Test.NV1.decls0`: `A`, `CN`, `one`) to an environment
by the kernel, runs `#erase`'s entry point `Erasure.eraseEntry` on NV-1's term
`EraseProof.Test.NV1.e0` (`one (fun a : A => a)`) over that environment, and writes the program to
`FILE` and its attributes to `FILE.inlinings`, printed as `#erase` prints them
(`LeanToLambdaBox/Erasure/Command.lean`). It fails unless the printed program is byte-identical to
the printing of `EraseProof.Test.NV1.p0`, the program that `EraseProof.Test.NV1.hrun` computes and
`EraseProof.Test.NV1.final` is about, and the list of constants to inline is empty, as `hrun`
states. `proof/scripts/c11.sh` then runs `peregrine validate` and `peregrine eval` on `FILE`.
-/

open Lean Erasure EraseProof.Test.NV1

namespace EraseProofNV1Emit

/-- `#erase`'s printing of a program. -/
def printProgram (p : Program) : String := p |> Serialize.to_sexpr |>.toString

/-- `#erase`'s printing of the attributes of a program with the constants `inls` to inline. -/
def printAttributes (inls : List Kername) : String :=
  let c : AttributesConfig :=
    { inlinings := inls, constRemappings := [], indRemappings := [], cstrReorders := [],
      customAttributes := [] }
  c |> Serialize.to_sexpr |>.toString

/-- NV-1's declarations as kernel declarations, oldest first. -/
def declarations : List Declaration :=
  decls0.reverse.map fun
    | .axiomInfo v => .axiomDecl v
    | .defnInfo v => .defnDecl v
    | ci => .axiomDecl { name := ci.name, levelParams := ci.levelParams, type := ci.type,
                         isUnsafe := false }

def main (args : List String) : IO UInt32 := do
  let [file] := args
    | IO.eprintln "usage: lake env lean --run tools/NV1Emit.lean FILE"; return 2
  if decls0.any fun | .defnInfo _ | .axiomInfo _ => false | _ => true then
    IO.eprintln "NV-1: decls0 has a declaration that is neither a definition nor an axiom"
    return 1
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Init }] {}
  let run : CoreM (Program × List Kername) := do
    for d in declarations do addDecl d
    eraseEntry (EnvView.ofEnvironment (← getEnv)) {} e0
  let r : Except Exception (Program × List Kername) ←
    (run.run' { fileName := "<NV-1>", fileMap := default } { env }).toBaseIO
  let (p, inls) ← match r with
    | .ok r => pure r
    | .error e =>
      IO.eprintln s!"NV-1: eraseEntry failed: {← e.toMessageData.toString}"
      return 1
  let s := printProgram p
  IO.FS.writeFile file s
  IO.FS.writeFile (file ++ ".inlinings") (printAttributes inls)
  let expected := printProgram p0
  if s != expected then
    IO.eprintln s!"NV-1: #erase emits\n  {s}\nbut Test.NV1.p0 prints as\n  {expected}"
    return 1
  if !inls.isEmpty then
    IO.eprintln s!"NV-1: #erase asks to inline {inls.length} constant(s); Test.NV1.hrun says none"
    return 1
  IO.println s!"NV-1: #erase emits Test.NV1.p0: {s}"
  return 0

end EraseProofNV1Emit

def main (args : List String) : IO UInt32 := EraseProofNV1Emit.main args
