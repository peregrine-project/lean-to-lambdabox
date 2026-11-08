import LeanToLambdaBox
import EraseProof.Test.NV1Run
import EraseProof.Test.NV2Run
import EraseProof.Test.NVPData
import EraseProof.Test.NVQRun
import EraseProof.Test.NVRRun
import EraseProof.Test.NVSRun
import EraseProof.Test.NVQPRun

/-!
# NV-1's, NV-2's, NV-Q's, NV-R's, NV-S's and NV-QP's emitted programs, for check C11

Run from `proof/` as `lake env lean --run tools/NVEmit.lean FILE1 FILE2 FILE3 FILE4 FILE5 FILE6
FILE7`. For each of the non-vacuity instances NV-1 (`inductive B | f | t` and `B.neg`,
`EraseProof.Test.NV1`), NV-2 (`B`, `inductive T : Prop | i`, `inductive W | n | s (b : B) (h : T)`,
`EraseProof.Test.NV2`), NV-Q (`B`, the axioms `R` and `hR`, and `Init`'s quotients,
`EraseProof.Test.NVQ`), NV-R (`B` and `inductive N | z | s (n : N)`, `EraseProof.Test.NVR`), NV-S
(`N` and `add`, defined by structural recursion, `EraseProof.Test.NVS`) and NV-QP (`orU` on the
unordered pairs of `B`, `Quot swapR`, `EraseProof.Test.NVQP`, on its two terms `useTF` and `useFT`),
it declares the program as the `inductive` command does (the kernel's inductive declaration, then
`mkCasesOn`; NV-S's and NV-QP's sources are elaborated as a file is), checks that the environment's
declarations are the written-out `P` (for NV-S, `P` and the compiled companion `add._unsafe_rec` of
its view; every field; a definition's or theorem's value up to binder names), runs `#erase`'s entry
point `Erasure.eraseEntry` on the term `e` over that environment, with the instance's
configuration, and writes the program to `FILE1` (resp. `FILE2`, …, `FILE7`) and its attributes to
`FILE1.inlinings`, printed as `#erase` prints them (`LeanToLambdaBox/Erasure/Command.lean`). It
fails unless the printed program is byte-identical to the printing of the instance's `p0`, the
program that its `hrun` computes (for `useFT`, `pFT`: NV-QP's `p0` with `useFT` for `useTF`), and
the list of constants to inline is the one `hrun` states (empty, NV-S's and NV-QP's `inl0`). `proof/scripts/c11.sh` then runs
`peregrine validate` and `peregrine eval` on the seven files. It also checks NV-P's declarations
(`EraseProof.Test.NVP.P`, shared by NV-K up to its lemma `hEq`) against the kernel's: `Eq` and its
`Eq.rec`, `Eq.casesOn` from `Init`, and `B` as declared above.
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

/-- NV-S's source, elaborated as a file is: `N`, then `add` by structural recursion. The
environment of `importModules` does not hold `Init`'s instances, which the `SizeOf` instance of `N`
needs; it is not generated (no declaration of `P` refers to it). -/
def srcNVS : String := "set_option genSizeOf false
inductive N | z | s (n : N)
def add (n m : N) : N :=
  match m with
  | .z => n
  | .s k => .s (add n k)
"

/-- NV-QP's source: the program of `tests/regress/quotient_pair.lean` outside its namespace, with
`Prod B B` for `B × B`, `Eq a b` for `a = b` and term proofs (the environment of `importModules`
has the built-in parsers only, none of `Init`'s notations or tactics); the proof of `orU`'s respect
obligation is the term the regression test's `by subst h; exact orB_comm p.1 p.2` elaborates to. -/
def srcNVQP : String := "set_option genSizeOf false
inductive B | f | t
def orB : B → B → B
  | .f, b => b
  | .t, _ => .t
def swapR (p q : Prod B B) : Prop := Eq q (p.2, p.1)
theorem orB_comm (a b : B) : Eq (orB a b) (orB b a) :=
  B.casesOn (motive := fun a => Eq (orB a b) (orB b a)) a
    (B.casesOn (motive := fun b => Eq (orB B.f b) (orB b B.f)) b rfl rfl)
    (B.casesOn (motive := fun b => Eq (orB B.t b) (orB b B.t)) b rfl rfl)
def orU : Quot swapR → B :=
  Quot.lift (fun p => orB p.1 p.2) (fun p q h =>
    @Eq.ndrec (Prod B B) (p.2, p.1) (fun (q : Prod B B) => Eq (orB p.1 p.2) (orB q.1 q.2))
      (orB_comm p.1 p.2) q (Eq.symm h))
def useTF : B := orU (Quot.mk swapR (B.t, B.f))
def useFT : B := orU (Quot.mk swapR (B.f, B.t))
"

/-- The program `#erase` emits for NV-QP's second term `useFT`: NV-QP's `p0` with the constant
`useFT`, `orU` on the class of `(B.f, B.t)`, in place of `useTF`. -/
def pFT : Program :=
  .untyped ((toKername `useFT, .constantDecl ⟨some (NVQP.useL NVQP.fL NVQP.tL)⟩) :: NVQP.lenv0)
    (some (.const (toKername `useFT)))

/-- Elaborate `src` in the current environment; fail on an error message. -/
def elabSource (name src : String) : CoreM Unit := do
  let (env, msgs) ← Lean.Elab.process src (← getEnv) {} (some s!"<{name}>")
  if msgs.hasErrors then
    throwError "{name}: the source does not elaborate: {← msgs.toList.mapM (·.toString)}"
  setEnv env

/-- NV-P's declarations are the kernel's (`Init`'s `Eq` family, and `B` declared by `declB`). -/
def checkNVP : IO UInt32 := do
  let env ← importModules #[{ module := `Init }] {}
  let run : CoreM Unit := do
    declB
    for ci in NVP.P do
      match (← getEnv).find? ci.name with
      | some ci' =>
        unless sameDecl ci ci' do throwError "the declaration {ci.name} differs from the kernel's"
      | none => throwError "{ci.name} is not declared"
  match ← (run.run' { fileName := "<NV-P>", fileMap := default } { env }).toBaseIO with
  | .ok () => IO.println "NV-P: its declarations are the kernel's"; return 0
  | .error err => IO.eprintln s!"NV-P: {← err.toMessageData.toString}"; return 1

def main (args : List String) : IO UInt32 := do
  let [file1, file2, file3, file4, file5, file6, file7] := args
    | IO.eprintln
        "usage: lake env lean --run tools/NVEmit.lean FILE1 FILE2 FILE3 FILE4 FILE5 FILE6 FILE7"
      return 2
  initSearchPath (← findSysroot)
  -- NV-1: `B` (the kernel adds `B`, `B.f`, `B.t`, `B.rec`; `B.casesOn` as the `inductive`
  -- command builds it), then `B.neg`.
  let r1 ← emit "NV-1" file1 (do declB; addDecl (.defnDecl NV1.neg_def)) NV1.P NV1.e NV1.p0
  -- NV-2: `B`, `T`, `W` and `W.casesOn`.
  let r2 ← emit "NV-2" file2 (do
      declB
      addDecl (.inductDecl [] 0 [⟨`T, NV2.T_ind.type, [⟨`T.i, NV2.tT⟩]⟩] false)
      Meta.MetaM.run' (mkCasesOn `T)
      addDecl (.inductDecl [] 0
        [⟨`W, NV2.W_ind.type, [⟨`W.n, NV2.tW⟩, ⟨`W.s, NV2.sTy⟩]⟩] false)
      Meta.MetaM.run' (mkCasesOn `W))
    NV2.P NV2.e NV2.p0
  let r3 ← checkNVP
  -- NV-Q: `B`, then the axioms `R` and `hR`; the quotients are `Init`'s.
  let r4 ← emit "NV-Q" file3 (do
      declB
      addDecl (.axiomDecl NVQ.R_ax)
      addDecl (.axiomDecl NVQ.hR_ax))
    NVQ.P NVQ.e NVQ.p0
  -- NV-R: `B`, then `N` and `N.casesOn`.
  let r5 ← emit "NV-R" file4 (do
      declB
      addDecl (.inductDecl [] 0 [⟨`N, NVR.N_ind.type, [⟨`N.z, NVR.tN⟩, ⟨`N.s, NVR.sTy⟩]⟩] false)
      Meta.MetaM.run' (mkCasesOn `N))
    NVR.P NVR.e NVR.p0
  -- NV-S: the source of `N` and `add`, elaborated; the declarations of its view, `P` and `add`'s
  -- compiled companion `add._unsafe_rec`, which `structural := .kernel` lets the fragment test
  -- admit.
  let r6 ← emit "NV-S" file5 (elabSource "NV-S" srcNVS) NVS.PV NVS.e NVS.p0 NVS.cfg
    NVS.inl0
  -- NV-QP: the source of the unordered pairs, elaborated; its two terms `useTF` and `useFT`.
  let r7 ← emit "NV-QP" file6 (elabSource "NV-QP" srcNVQP) NVQP.P NVQP.e NVQP.p0 NVQP.cfg
    NVQP.inl0
  let r8 ← emit "NV-QP (useFT)" file7 (elabSource "NV-QP" srcNVQP) NVQP.P NVQP.eFT pFT NVQP.cfg
    NVQP.inl0
  return max (max (max (max r1 r2) (max r3 r4)) (max r5 r6)) (max r7 r8)

end EraseProofNVEmit

def main (args : List String) : IO UInt32 := EraseProofNVEmit.main args
