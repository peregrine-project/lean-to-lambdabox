import LeanToLambdaBox
import EraseProof.Test.NV1Run
import EraseProof.Test.NV0Premises
import EraseProof.Test.NV2Premises
import EraseProof.Test.NV3Premises
import EraseProof.Test.NV4Premises
import EraseProof.Test.NV5Premises

/-!
# The emitted programs of the non-vacuity instances NV-0 to NV-5, for check C11

Run from `proof/` as `lake env lean --run tools/NVEmit.lean DIR`. For the non-vacuity instance NV-1
(`inductive B | f | t` and `B.neg`, `EraseProof.Test.NV1`) it declares the program as the
`inductive` command does (the kernel's inductive declaration, then `mkCasesOn`), checks that the
environment's declarations are the written-out `P` (every field; a definition's or theorem's value
up to binder names), runs `#erase`'s entry point `Erasure.eraseEntry` on the term `e` over that
environment, and writes the program to `DIR/NV1.ast` and its attributes to `DIR/NV1.ast.inlinings`,
printed as `#erase` prints them (`LeanToLambdaBox/Erasure/Command.lean`). It fails unless the
printed program is byte-identical to the printing of `p0`, the program that `hrun` computes, and
the list of constants to inline is the one `hrun` states (empty). NV-0, NV-2, NV-3, NV-4 and NV-5
are emitted the same way (`Init` declares `Nat`, `Eq`, `False` and the quotient).
-/

open Lean Elab Erasure EraseProof.Test

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
  | .quotInfo a, .quotInfo b =>
    a.name == b.name && a.levelParams == b.levelParams && a.type == b.type &&
      a.kind.ctorIdx == b.kind.ctorIdx
  | .thmInfo a, .thmInfo b =>
    a.name == b.name && a.levelParams == b.levelParams && a.type == b.type && a.all == b.all &&
      eraseNames a.value == eraseNames b.value
  | .axiomInfo a, .axiomInfo b =>
    a.name == b.name && a.levelParams == b.levelParams && a.type == b.type &&
      a.isUnsafe == b.isUnsafe
  | .recInfo a, .recInfo b =>
    a.name == b.name && a.levelParams == b.levelParams && a.type == b.type && a.all == b.all &&
      a.numParams == b.numParams && a.numIndices == b.numIndices &&
      a.numMotives == b.numMotives && a.numMinors == b.numMinors && a.k == b.k &&
      a.isUnsafe == b.isUnsafe && a.rules.length == b.rules.length &&
      (a.rules.zip b.rules).all fun (r, s) =>
        r.ctor == s.ctor && r.nfields == s.nfields && r.rhs == s.rhs
  | _, _ => false

/-- Declare a program with `decl`, check its declarations against `P`, run `#erase`'s entry point
on `e` with the configuration `cfg` and compare the printed program with `p0` and the constants to
inline with `inl0`; write it to `file`. -/
def emit (name file : String) (decl : CoreM Unit) (P : List ConstantInfo) (e : Expr)
    (p0 : Program) (cfg : ErasureConfig := {}) (inl0 : List Kername := []) : IO UInt32 := do
  let env ← importModules #[{ module := `Init }] {}
  let run : CoreM (Program × List Kername) := do
    decl
    for ci in P do
      match (← getEnv).find? ci.name with
      | some ci' =>
        unless sameDecl ci ci' do throwError "the declaration {ci.name} differs from the kernel's"
      | none => throwError "{ci.name} is not declared"
    eraseEntry (EnvView.ofEnvironment (← getEnv)) cfg e
  let r ← (run.run' { fileName := s!"<{name}>", fileMap := default } { env }).toBaseIO
  let (p, inls) ← match r with
    | .ok r => pure r
    | .error err =>
      IO.eprintln s!"{name}: {← err.toMessageData.toString}"
      return 1
  let s := printProgram p
  IO.FS.writeFile file s
  IO.FS.writeFile (file ++ ".inlinings") (printAttributes inls)
  let expected := printProgram p0
  if s != expected then
    IO.eprintln s!"{name}: #erase emits\n  {s}\nbut its p0 prints as\n  {expected}"
    return 1
  if printAttributes inls != printAttributes inl0 then
    IO.eprintln s!"{name}: #erase asks to inline\n  {printAttributes inls}\nbut its hrun says\n  {printAttributes inl0}"
    return 1
  IO.println s!"{name}: #erase emits its p0: {s}"
  return 0

/-- `inductive B | f | t`. -/
def declB : CoreM Unit := do
  addDecl (.inductDecl [] 0 [⟨`B, NV1.B_ind.type, [⟨`B.f, NV1.tB⟩, ⟨`B.t, NV1.tB⟩]⟩] false)
  Meta.MetaM.run' (mkCasesOn `B)

def main (args : List String) : IO UInt32 := do
  let [dir] := args
    | IO.eprintln "usage: lake env lean --run tools/NVEmit.lean DIR"
      return 2
  initSearchPath (← findSysroot)
  IO.FS.createDirAll dir
  -- NV-1: `B` (the kernel adds `B`, `B.f`, `B.t`, `B.rec`; `B.casesOn` as the `inductive`
  -- command builds it), then `B.neg`.
  let r1 ← emit "NV-1" s!"{dir}/NV1.ast" (do declB; addDecl (.defnDecl NV1.neg_def)) NV1.P NV1.e NV1.p0
  let r0 ← emit "NV-0" s!"{dir}/NV0.ast"
    (do addDecl (.defnDecl NV0.id_def); addDecl (.defnDecl NV0.main_def)) NV0.P NV0.e NV0.p0
  let r2 ← emit "NV-2" s!"{dir}/NV2.ast"
    (do declB
        addDecl (.inductDecl [] 1 [⟨`Box, NV2.Box_ind.type, [⟨`Box.mk, NV2.mkTy⟩]⟩] false))
    NV2.P NV2.e NV2.p0
  let r3 ← emit "NV-3" s!"{dir}/NV3.ast" (pure ()) NV3.P NV3.e NV3.p0 NV3.cfg
  let r4 ← emit "NV-4" s!"{dir}/NV4.ast"
    (do declB
        addDecl (.inductDecl [] 0 [⟨`P, .sort .zero, [⟨`P.mk, NV4.P_mk.type⟩]⟩] false)
        Meta.MetaM.run' (mkCasesOn `P))
    NV4.P NV4.e NV4.p0
  let r5 ← emit "NV-5" s!"{dir}/NV5.ast"
    (do declB
        addDecl (.inductDecl [`u] 1 [⟨`W, NV5.W_ind.type, [⟨`W.mk, NV5.mkTy⟩]⟩] false)
        addDecl (.defnDecl NV5.wrap_def))
    NV5.P NV5.e NV5.p0
  return r1 ||| r0 ||| r2 ||| r3 ||| r4 ||| r5

end EraseProofNVEmit

def main (args : List String) : IO UInt32 := EraseProofNVEmit.main args
