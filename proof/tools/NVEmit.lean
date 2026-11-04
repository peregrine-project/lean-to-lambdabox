import LeanToLambdaBox
import EraseProof.Test.NV1Run

/-!
# NV-1's emitted program, for check C11

Run from `proof/` as `lake env lean --run tools/NVEmit.lean FILE`. It declares the non-vacuity
instance NV-1 (`inductive B | f | t` and `B.neg`, `EraseProof.Test.NV1`) as the `inductive` command
does (the kernel's inductive declaration, then `mkCasesOn`), checks that the environment's
declarations are the written-out `EraseProof.Test.NV1.P` (every field; `B.neg`'s value up to
binder names), runs `#erase`'s entry point `Erasure.eraseEntry` on `EraseProof.Test.NV1.e`
(`B.neg B.f`) over that environment, and writes the program to `FILE` and its attributes to `FILE.inlinings`,
printed as `#erase` prints them (`LeanToLambdaBox/Erasure/Command.lean`). It fails unless the
printed program is byte-identical to the printing of `EraseProof.Test.NV1.p0`, the program that
`EraseProof.Test.NV1.hrun` computes, and the list of constants to inline is empty, as `hrun`
states. `proof/scripts/c11.sh` then runs `peregrine validate` and `peregrine eval` on `FILE`.
-/

open Lean Elab Erasure EraseProof.Test.NV1

namespace EraseProofNVEmit

/-- `#erase`'s printing of a program. -/
def printProgram (p : Program) : String := p |> Serialize.to_sexpr |>.toString

/-- `#erase`'s printing of the attributes of a program with the constants `inls` to inline. -/
def printAttributes (inls : List Kername) : String :=
  let c : AttributesConfig :=
    { inlinings := inls, constRemappings := [], indRemappings := [], cstrReorders := [],
      customAttributes := [] }
  c |> Serialize.to_sexpr |>.toString

/-- Binder names replaced by `_`. -/
def eraseNames : Expr → Expr
  | .lam _ t b bi => .lam `_ (eraseNames t) (eraseNames b) bi
  | .forallE _ t b bi => .forallE `_ (eraseNames t) (eraseNames b) bi
  | .app f a => .app (eraseNames f) (eraseNames a)
  | e => e

/-- The written-out declaration `ci` is the elaborated `ci'` (every field; a definition's value up
to binder names). -/
def sameDecl (ci ci' : ConstantInfo) : Bool :=
  match ci, ci' with
  | .defnInfo a, .defnInfo b =>
    a.name == b.name && a.levelParams == b.levelParams && a.type == b.type && a.all == b.all &&
      eraseNames a.value == eraseNames b.value && a.safety == b.safety &&
      (match a.hints, b.hints with
        | .abbrev, .abbrev | .«opaque», .«opaque» => true
        | .regular x, .regular y => x == y
        | _, _ => false)
  | .inductInfo a, .inductInfo b =>
    a.name == b.name && a.levelParams == b.levelParams && a.type == b.type &&
      a.numParams == b.numParams && a.numIndices == b.numIndices && a.all == b.all &&
      a.ctors == b.ctors && a.numNested == b.numNested && a.isRec == b.isRec &&
      a.isUnsafe == b.isUnsafe && a.isReflexive == b.isReflexive
  | .ctorInfo a, .ctorInfo b =>
    a.name == b.name && a.levelParams == b.levelParams && a.type == b.type &&
      a.induct == b.induct && a.cidx == b.cidx && a.numParams == b.numParams &&
      a.numFields == b.numFields && a.isUnsafe == b.isUnsafe
  | .recInfo a, .recInfo b =>
    a.name == b.name && a.levelParams == b.levelParams && a.type == b.type && a.all == b.all &&
      a.numParams == b.numParams && a.numIndices == b.numIndices &&
      a.numMotives == b.numMotives && a.numMinors == b.numMinors && a.k == b.k &&
      a.isUnsafe == b.isUnsafe && a.rules.length == b.rules.length &&
      (a.rules.zip b.rules).all fun (r, s) =>
        r.ctor == s.ctor && r.nfields == s.nfields && r.rhs == s.rhs
  | _, _ => false

def main (args : List String) : IO UInt32 := do
  let [file] := args
    | IO.eprintln "usage: lake env lean --run tools/NVEmit.lean FILE"; return 2
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Init }] {}
  let run : CoreM (Program × List Kername) := do
    -- `inductive B | f | t`: the kernel adds `B`, `B.f`, `B.t`, `B.rec`; `B.casesOn` as the
    -- `inductive` command builds it; then `B.neg`.
    addDecl (.inductDecl [] 0 [⟨`B, B_ind.type, [⟨`B.f, tB⟩, ⟨`B.t, tB⟩]⟩] false)
    Meta.MetaM.run' (mkCasesOn `B)
    addDecl (.defnDecl neg_def)
    for ci in P do
      match (← getEnv).find? ci.name with
      | some ci' =>
        unless sameDecl ci ci' do throwError "the declaration {ci.name} differs from the kernel's"
      | none => throwError "{ci.name} is not declared"
    eraseEntry (EnvView.ofEnvironment (← getEnv)) {} e
  let r ← (run.run' { fileName := "<NV-1>", fileMap := default } { env }).toBaseIO
  let (p, inls) ← match r with
    | .ok r => pure r
    | .error err =>
      IO.eprintln s!"NV-1: {← err.toMessageData.toString}"
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

end EraseProofNVEmit

def main (args : List String) : IO UInt32 := EraseProofNVEmit.main args
