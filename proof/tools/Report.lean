import Lean

/-!
# The Lean side of `proof/scripts/check.sh`

Run from `proof/` as `lake env lean --run tools/Report.lean [OPTION...]`. It imports the library
and the shipping code (by default the modules `EraseProof` and `LeanToLambdaBox`) and checks, over every declaration of the library's modules
(module `EraseProof` or `EraseProof.*`):

* C3/C4 `axioms`: the footprint of every declaration, computed as `#print axioms` computes it
  (`Lean.collectAxioms`: types and values, an inductive together with its constructors), lies in
  `propext`, `Classical.choice`, `Quot.sound`; so neither `sorryAx`, nor Metalean's axiom
  `Cardinal.exists_inaccessibles`, nor a `._native.` axiom occurs. The footprints are
  cross-checked against `Lean.collectAxioms` itself.
* C5 `sorry`: no declaration reaches a constant whose type or value mentions `sorryAx`.
* C6 `hygiene`: no non-test declaration reaches, through the bodies of the library, the shipping
  code and Metalean, a constant declared in a module `Metalean.Frontend*`, `Metalean.Checker*`,
  `Metalean.Export*`, `Metalean.SetSemantics*` or `Metalean.SetTheory*` (`forbiddenModules`), or
  named with one of these prefixes, or a declaration of the test namespace `EraseProof.Test`.
  The check is on the constants reached, not on the modules imported (Metalean's own modules
  import `Metalean.Frontend.Lookup`), and on modules as well as names (`Metalean.Expr.natLit` is
  declared in the module `Metalean.Checker.Acceleration.Literal`). Exempt are exactly the
  constants that the translator's total term builders `allowRoots` (and the declarations of the
  inductive `Metalean.Export.QuotKind`) reach (`allowList`), which the bridge relation uses for the
  η-terms of constructors, recursors, inductive types and quotients; each exempt constant is a safe
  definition or an inductive (with its constructors and recursor), neither `partial`, `opaque`,
  `unsafe` nor `implemented_by`. Also exempt are the declarations Lean generates for an exempt
  constant when a proof unfolds or rewrites it (`isGeneratedComponent`: `eq_<n>`, `eq_def`,
  `else_eq`, `congr_simp`, `match_<n>`, and so on recursively); their bodies are walked like any other.
* C7 `leaves`: every declaration outside `EraseProof.Test` is reachable from a root of `ROOTS.txt`,
  from a statement definition, from a proved theorem of `statements` or from a corollary of
  `corollaries` (through types and values;
  a mutual block, an inductive with its constructors, recursors, structure projections and the
  declarations `inductive` generates for it, those of its nested occurrences included, is one
  node; generated auxiliaries, `isAux`, are not checked); every root of `ROOTS.txt` is a theorem
  of the library whose consumer does not exist yet; no root is reachable from another root; every
  test that is not a theorem is reachable from a test theorem. The proved theorems of `statements`
  are results of their own, not lemmas of the final theorem: `collectDeps_ok_of` characterizes the
  programs that pass the fragment test, which `erase_correct` takes as its hypothesis `hfrag` and
  so does not use; reachability starts from each of them.
* `expected`: the footprints of the roots and of the test theorems equal `axioms.expected`.
* `modules`: every `.lean` file of the library's source tree is imported.
* C9 `divergences`: every entry `### DV-<n>` of the divergence register has exactly the fields
  `dvFields`, in order, and its artifact field cites a declaration of the library; every code span
  of an entry that is a name `EraseProof.*`, `Metalean.*` or `Erasure.*` is a declaration; a path
  `proof/*.lean` is a file of this package, a Metalean path `Metalean/*.lean[:lines]` a file of
  the Metalean checkout with those lines, a shipping path `LeanToLambdaBox/*.lean[:lines]` a file
  of the root package with those lines, and, with `--metarocq DIR`, a MetaRocq path
  `<dir>/theories/*.v[:lines]` a file of `DIR` with those lines; a span `:<lines>` cites lines of
  the file the field cited last; a single MetaRocq line cited right after an identifier (the two
  spans separated by nothing, `(` or `,`) is one of the four lines from it that mention the
  identifier; every id `DV-<n>` that the register, the library's source files or the shipping
  sources (`LeanToLambdaBox/`) cite is an entry of the register.
* C12 `statements`, always: every statement definition of `statements` is a definition of the
  library of type `Prop`; each theorem of `statements` that exists is a theorem of the library
  whose type is definitionally equal (kernel `isDefEq`) to its statement definition; a theorem
  that does not exist must be listed in `unproved`, which is reported as not yet proved, and a
  theorem listed there must not exist.
* C12 `final`: the final form. The only line of `ROOTS.txt` with consumer `FINAL` is
  `EraseProof.erase_correct FINAL`; every other line names a root whose consumer has not landed
  (C7), so C7 checks reachability from the final theorem `erase_correct`, the statements and those
  roots (tests are roots by themselves); `unproved` is empty. `erase_correct` is a theorem whose
  footprint is exactly `propext`, `Classical.choice`, `Quot.sound`, as is that of each of its
  instances on the non-vacuity programs NV-1, NV-P, NV-K, NV-2, NV-Q, NV-R and NV-S
  (`finalInstances`: `EraseProof.Test.NV1.final`, `NVP.final`, `NVK.final`, `NV2.final`,
  `NVQ.final`, `NVR.final`, `NVS.final`),
  each of which applies `erase_correct` to its program's eight hypothesis terms, theorems within
  the same three axioms; each corollary of `corollaries` (`erase_correct_firstorder`) has the same
  footprint, and its instances (`NV1.firstorder`, `NV2.firstorder`, `NVR.firstorder`,
  `NVS.firstorder`) are
  theorems within those axioms that mention it. Skipped with `--no-final`.
* C12b `pin`, always: the statement definitions and the definitions they are about are those of
  `spec.pin`. The pin of the statement definitions `pinRoots` is computed (`specPin`): for each
  root and every constant reached from it through types, values and constructors, a SHA-256 digest
  of a serialization (`pinText`) of its kind and flags and of its type and value (definitions,
  opaques), its type (theorems, axioms, recursors) or its type and its constructors' names and
  types (inductives), followed further, if it is declared in the library or in the shipping code;
  its name only if it is one of the three shipping functions under verification
  (`underVerification`: `Erasure.collectDeps`, `Erasure.erasePure`, `Erasure.eraseEntry`, whose
  changes the pin does not follow, so the constants reached only through them are not pinned) or
  if it is declared in a dependency (`depPrefixes`, pinned by version). The pin also holds the
  toolchain and the revision of every git dependency (`depPin`: `lean-toolchain` and
  `lake-manifest.json`). `spec.pin` (written by `--write-pin`) must equal the computed pin; every
  constant it names must exist; the toolchain and dependency lines must be those of the root
  package (`--shipping`) and of this package (`--src`), and the running Lean the pinned
  toolchain.

Options: `--import M` (repeatable; replaces the default `EraseProof`, `LeanToLambdaBox`), `--roots FILE`
(`ROOTS.txt`), `--expected FILE` (`axioms.expected`), `--out DIR` (`.check`), `--src DIR` (`.`),
`--divergences FILE` (`../doc/DIVERGENCES.md`), `--metalean DIR` (`../.lake/packages/metalean`),
`--shipping DIR` (`..`, the root package, whose `LeanToLambdaBox.lean` and `LeanToLambdaBox/` are
scanned for `DV-<n>` citations), `--metarocq DIR` (a MetaRocq checkout; without it, MetaRocq
citations are not checked), `--no-final` (skips C12 and the final form of C12b), `--pin FILE`
(`spec.pin`), `--write-pin FILE` (computes the pin of the imported modules, writes it to `FILE`
and runs no check), `--pin-root NAME` (repeatable; replaces `pinRoots` for `--write-pin`).
It writes `DIR/footprints.txt` (every declaration) and `DIR/axioms.actual` (the file
`axioms.expected` should be), prints one line per check, and exits with 1 if a check fails.
-/

open Lean

namespace EraseProofReport

/-- The library's name: its modules are `lib` and `lib.*`, its tests live in namespace
`lib.Test`. -/
def lib : Name := `EraseProof

/-- The axioms a declaration of the library may depend on, in the order footprints print them. -/
def allowedAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- Metalean's own axiom (`Metalean/SetTheory/Cardinal/Inaccessible.lean:16`), which only its
set-theoretic model uses; named in failure messages. -/
def metaleanAxiom : Name := `Cardinal.exists_inaccessibles

/-- Metalean's unverified or model-only modules: its frontend and checkers (`partial` code), its
export format, and its set-theoretic semantics (which reach `metaleanAxiom`) (C6). -/
def forbiddenModules : Array Name := #[`Metalean.Frontend, `Metalean.Checker, `Metalean.Export,
  `Metalean.SetSemantics, `Metalean.SetTheory]

/-- A module or a name under one of `forbiddenModules` (C6). -/
def isForbidden (n : Name) : Bool := forbiddenModules.any (·.isPrefixOf n)

/-- The total term builders of Metalean's translator (`Metalean/Frontend/Translate.lean`) that the
bridge relation uses for the η-terms of saturating names, and the quotient kinds of its export
format; with what they reach, they are exempt from C6 (`allowList`). The η-terms enter the
hypotheses (`TrM` in `he`, `henv`) and, through `ErasableS` in the `box` rule of `Erases`, the
conclusion of the final theorem: a wrong builder could make premises unsatisfiable or change which
terms count as erasable. They are total, non-`partial` definitions of the pinned Metalean. -/
def allowRoots : Array Name := #[`Metalean.Frontend.indTerm, `Metalean.Frontend.ctorTerm,
  `Metalean.Frontend.recrTerm, `Metalean.Frontend.wrapCase, `Metalean.Frontend.quotTerm,
  `Metalean.Export.QuotKind]

/-- The theorems with a statement definition (`EraseProof/Statements.lean`), each with that
definition: the final theorem, the lower bound of its fragment hypothesis, and the theorems
`erases_correct` (relation-level simulation) and `erasePure_erases` (the pure traversal) (C12). -/
def statements : Array (Name × Name) := #[
  (`EraseProof.erase_correct, `EraseProof.erase_correct_statement),
  (`EraseProof.collectDeps_ok_of, `EraseProof.collectDeps_ok_of_statement),
  (`EraseProof.erases_correct, `EraseProof.erases_correct_statement),
  (`EraseProof.erasePure_erases, `EraseProof.erasePure_erases_statement)]

/-- The theorems of `statements` that are not proved yet; C12 reports them and compares the others
with their statements. -/
def unproved : Array Name := #[]

/-- The statement definitions, whose definitions C12b pins. -/
def pinRoots : Array Name := statements.map (·.2)

/-- Module prefixes of the toolchain and the dependencies, whose constants C12b pins by name. -/
def depPrefixes : Array Name := #[`Init, `Std, `Lean, `Mathlib, `Batteries, `Metalean, `Aesop,
  `Qq, `Plausible, `ProofWidgets, `ImportGraph, `LeanSearchClient, `Cli]

/-- The final theorem, the only root of `ROOTS.txt` with consumer `FINAL` in the final form
(C12). -/
def finalTheorem : Name := `EraseProof.erase_correct

/-- The instances of the final theorem on the non-vacuity programs, each with the terms of the
hypotheses that it passes to the final theorem (C12). -/
def finalInstances : Array (Name × Array Name) :=
  #[`EraseProof.Test.NV1, `EraseProof.Test.NVP, `EraseProof.Test.NVK, `EraseProof.Test.NV2,
    `EraseProof.Test.NVQ, `EraseProof.Test.NVR, `EraseProof.Test.NVS].map fun ns =>
    (ns ++ `final, #[`henv, `hwf, `hview, `he, `hty, `hfrag, `hrun, `hev].map (ns ++ ·))

/-- The corollaries of the final theorem, each with its instances on the non-vacuity programs:
proved theorems that derive a more specific conclusion from `erase_correct`. Like the theorems of
`statements`, they are roots of C7; their statements are not pinned (C12b). The final form checks
that each is a theorem whose footprint is exactly `propext`, `Classical.choice`, `Quot.sound`, and
that each instance is a theorem within them that mentions its corollary (C12). -/
def corollaries : Array (Name × Array Name) := #[
  (`EraseProof.erase_correct_firstorder,
    #[`EraseProof.Test.NV1.firstorder, `EraseProof.Test.NV2.firstorder,
      `EraseProof.Test.NVR.firstorder, `EraseProof.Test.NVS.firstorder])]

structure Config where
  imports : Array Name := #[]
  roots : System.FilePath := "ROOTS.txt"
  expected : System.FilePath := "axioms.expected"
  out : System.FilePath := ".check"
  src : System.FilePath := "."
  divergences : System.FilePath := "../doc/DIVERGENCES.md"
  metalean : System.FilePath := "../.lake/packages/metalean"
  shipping : System.FilePath := ".."
  metarocq : Option System.FilePath := none
  final : Bool := true
  pin : System.FilePath := "spec.pin"
  writePin : Option System.FilePath := none
  pinRoots : Array Name := #[]

partial def parseArgs (cfg : Config) : List String → Except String Config
  | [] => .ok cfg
  | "--import" :: m :: rest => parseArgs { cfg with imports := cfg.imports.push m.toName } rest
  | "--roots" :: f :: rest => parseArgs { cfg with roots := f } rest
  | "--expected" :: f :: rest => parseArgs { cfg with expected := f } rest
  | "--out" :: f :: rest => parseArgs { cfg with out := f } rest
  | "--src" :: f :: rest => parseArgs { cfg with src := f } rest
  | "--divergences" :: f :: rest => parseArgs { cfg with divergences := f } rest
  | "--metalean" :: f :: rest => parseArgs { cfg with metalean := f } rest
  | "--shipping" :: f :: rest => parseArgs { cfg with shipping := f } rest
  | "--metarocq" :: d :: rest => parseArgs { cfg with metarocq := some d } rest
  | "--no-final" :: rest => parseArgs { cfg with final := false } rest
  | "--pin" :: f :: rest => parseArgs { cfg with pin := f } rest
  | "--write-pin" :: f :: rest => parseArgs { cfg with writePin := some f } rest
  | "--pin-root" :: n :: rest => parseArgs { cfg with pinRoots := cfg.pinRoots.push n.toName } rest
  | a :: _ => .error s!"unknown or incomplete option {a}"

/-! ## Names -/

def isNumbered (pre s : String) : Bool :=
  s.length > pre.length && s.startsWith pre && (s.toList.drop pre.length).all Char.isDigit

/-- A name component that marks a compiler- or elaborator-generated auxiliary. -/
def isAuxComponent (s : String) : Bool :=
  s.startsWith "_" || isNumbered "match_" s || isNumbered "proof_" s || isNumbered "eq_" s

/-- The last component of a declaration Lean generates on demand for the declaration it is named
under: an equation lemma (`eq_<n>`, `eq_def`, and `else_eq` of a `_sparseCasesOn_<n>` matcher
auxiliary), a `simp` congruence lemma (`congr_simp`) or a matcher (`match_<n>`). -/
def isGeneratedComponent (s : String) : Bool :=
  isNumbered "eq_" s || s == "eq_def" || s == "else_eq" || s == "congr_simp" ||
    isNumbered "match_" s

/-- Exempt from C6: an allow-listed constant, or a declaration generated for an exempt one
(`isGeneratedComponent`; e.g. `Metalean.Frontend.wrapCase.eq_1`,
`Metalean.Frontend.quotTerm._sparseCasesOn_1.else_eq`). What
a generated declaration mentions is checked like any other reach. -/
def isExempt (allowed : Std.HashSet Name) : Name → Bool
  | c@(.str p s) => allowed.contains c || (isGeneratedComponent s && isExempt allowed p)
  | c => allowed.contains c

/-- Last components of generated declarations: auxiliary recursors, `noConfusion`, equation and
induction principles, injectivity lemmas, `sizeOf` lemmas. -/
def auxLast : List String :=
  ["rec", "below", "ibelow", "brecOn", "binductionOn", "casesOn", "recOn", "noConfusion",
   "noConfusionType", "eq_def", "congr_simp", "induct", "mutual_induct", "inj", "injEq", "ctorIdx",
   "sizeOf_spec"]

/-- The name a user wrote: private names without their `_private` prefix. -/
def userName (n : Name) : Name := (privateToUserName? n).getD n

/-- A compiler- or elaborator-generated auxiliary declaration; the no-leaves check skips these. -/
def isAux (n : Name) : Bool :=
  let u := userName n
  anyComponent u || match u with
    | .str _ s => auxLast.contains s
    | _ => false
where
  anyComponent : Name → Bool
    | .anonymous => false
    | .num _ _ => true
    | .str p s => isAuxComponent s || anyComponent p

/-- The declaration a generated auxiliary belongs to. -/
partial def ownerOf (n : Name) : Name :=
  if isAux n then
    match n with
    | .str p _ | .num p _ => if p.isAnonymous then n else ownerOf p
    | .anonymous => n
  else n

def isTest (n : Name) : Bool := (lib ++ `Test).isPrefixOf (userName n)

/-! ## The environment -/

def moduleOf? (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).bind fun idx => env.header.moduleNames[idx.toNat]?

def isOurModule (m : Name) : Bool := lib.isPrefixOf m

def isOurs (env : Environment) (n : Name) : Bool :=
  match moduleOf? env n with
  | some m => isOurModule m
  | none => false

/-- Constants whose bodies are followed by the hygiene walk: ours, the shipping code, Metalean.
Nothing outside these can mention a Metalean constant. -/
def isWalkedModule (m : Name) : Bool :=
  isOurModule m || (`LeanToLambdaBox).isPrefixOf m || (`Metalean).isPrefixOf m

/-- The constants a declaration mentions, as `Lean.collectAxioms` follows them (an inductive's
constructors are handled by `fpMembers`). -/
def uses (env : Environment) (c : Name) : Array Name :=
  match env.find? c with
  | some (.axiomInfo v) => v.type.getUsedConstants
  | some (.defnInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
  | some (.thmInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
  | some (.opaqueInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
  | some (.quotInfo _) => #[]
  | some (.ctorInfo v) => v.type.getUsedConstants
  | some (.recInfo v) => v.type.getUsedConstants
  | some (.inductInfo v) => v.type.getUsedConstants
  | none => #[]

def inductKey (env : Environment) (i : Name) : Name :=
  match env.find? i with
  | some (.inductInfo v) => v.all.headD i
  | _ => i

/-- Footprint node: an inductive block with its constructors is one node. -/
def fpKey (env : Environment) (c : Name) : Name :=
  match env.find? c with
  | some (.ctorInfo v) => inductKey env v.induct
  | some (.inductInfo v) => v.all.headD c
  | _ => c

def fpMembers (env : Environment) (k : Name) : Array Name :=
  match env.find? k with
  | some (.inductInfo v) =>
    v.all.foldl (init := #[]) fun acc i =>
      match env.find? i with
      | some (.inductInfo w) => (acc.push i) ++ w.ctors.toArray
      | _ => acc.push i
  | _ => #[k]

/-- Declarations `I.s` that `inductive` and `structure` generate for an inductive `I`. -/
def inductiveGenerated : List String :=
  ["rec", "below", "ibelow", "brecOn", "binductionOn", "casesOn", "recOn", "noConfusion",
   "noConfusionType", "ctorIdx", "toCtorIdx", "ctorElim", "ctorElimType", "ofNat",
   "ofNat_ctorIdx", "sizeOf_spec"]

/-- A suffix `s` of a declaration `I.s` that `inductive` generates for an inductive `I`: one of
`inductiveGenerated`, or one of them followed by `_<n>`, the auxiliary of the `n`-th nested
occurrence of a nested inductive (`rec_1`, `below_1`, `brecOn_1`). -/
def isInductiveGenerated (s : String) : Bool :=
  inductiveGenerated.contains s || inductiveGenerated.any fun g => isNumbered (g ++ "_") s

/-- Declarations `C.s` that `inductive` and `structure` generate for a constructor `C`. -/
def ctorGenerated : List String := ["inj", "injEq", "sizeOf_spec", "elim", "noConfusion", "hinj"]

/-- No-leaves node: a mutual block; an inductive block with its constructors, recursors,
structure projections and the declarations `inductiveGenerated`, `ctorGenerated`. -/
def leafKey (env : Environment) (c : Name) : Name :=
  let generated? : Option Name := match c with
    | .str p s =>
      match env.find? p with
      | some (.inductInfo _) => if isInductiveGenerated s then some (inductKey env p) else none
      | some (.ctorInfo v) => if ctorGenerated.contains s then some (inductKey env v.induct) else none
      | _ => none
    | _ => none
  match generated?, env.getProjectionFnInfo? c with
  | some k, _ => k
  | none, some info =>
    match env.find? info.ctorName with
    | some (.ctorInfo v) => inductKey env v.induct
    | _ => c
  | none, none =>
    match env.find? c with
    | some (.inductInfo v) => v.all.headD c
    | some (.ctorInfo v) => inductKey env v.induct
    | some (.recInfo v) => v.all.headD c
    | some (.defnInfo v) => v.all.headD c
    | some (.thmInfo v) => v.all.headD c
    | some (.opaqueInfo v) => v.all.headD c
    | _ => c

/-! ## Footprints -/

structure Footprint where
  axioms : NameSet := {}
  /-- The constants reached whose own type or value mentions `sorryAx`. -/
  sorries : NameSet := {}

def Footprint.union (a b : Footprint) : Footprint :=
  { axioms := b.axioms.foldl (·.insert ·) a.axioms
    sorries := b.sorries.foldl (·.insert ·) a.sorries }

/-- Footprints of the nodes reachable from `starts`, memoised in `memo`, by an explicit-stack
post-order walk. A node met again while it is still open (a cycle, possible only through partial
or unsafe declarations) contributes nothing; such nodes are returned in the second component. -/
def footprints (env : Environment) (starts : Array Name)
    (memo : Std.HashMap Name Footprint) : Std.HashMap Name Footprint × Array Name := Id.run do
  let mut memo := memo
  let mut cycles : Array Name := #[]
  let mut open_ : Std.HashSet Name := {}
  let mut stack : Array (Name × Bool) := starts.map fun c => (fpKey env c, false)
  while h : stack.size > 0 do
    let (k, expanded) := stack[stack.size - 1]
    stack := stack.pop
    if memo.contains k then continue
    let members := fpMembers env k
    let deps := members.foldl (init := #[]) fun acc m => acc ++ (uses env m).map (fpKey env)
    if !expanded then
      if open_.contains k then continue
      open_ := open_.insert k
      stack := stack.push (k, true)
      for d in deps do
        if d != k && !memo.contains d && !open_.contains d then
          stack := stack.push (d, false)
    else
      let mut fp : Footprint := {}
      for m in members do
        if let some (.axiomInfo _) := env.find? m then
          fp := { fp with axioms := fp.axioms.insert m }
        if (uses env m).contains ``sorryAx then
          fp := { fp with sorries := fp.sorries.insert m }
      for d in deps do
        if d == k then continue
        match memo[d]? with
        | some f => fp := fp.union f
        | none => cycles := cycles.push d
      memo := memo.insert k fp
      open_ := open_.erase k
  return (memo, cycles)

abbrev EnvM := StateM Environment

instance : MonadEnv EnvM where
  getEnv := get
  modifyEnv := modify

/-- `#print axioms` of `c`, computed by Lean itself. -/
def leanAxioms (env : Environment) (c : Name) : Array Name :=
  (collectAxioms c : EnvM (Array Name)).run' env

def sortAxioms (s : NameSet) : Array Name :=
  let known := allowedAxioms.filter s.contains
  let other := (s.toArray.filter fun a => !allowedAxioms.contains a).qsort Name.lt
  known ++ other

def showList (xs : Array String) : String := if xs.isEmpty then "-" else ",".intercalate xs.toList

def axiomsField (fp : Footprint) : String := showList ((sortAxioms fp.axioms).map toString)

/-! ## Reachability among the library's declarations -/

/-- Leaf keys reachable from `starts` (whose keys are included), following only constants of the
library. Returns the reached keys and, for each reached key, a declaration that mentions it. -/
def reach (env : Environment) (members : Std.HashMap Name (Array Name)) (starts : Array Name) :
    Std.HashSet Name × Std.HashMap Name Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut via : Std.HashMap Name Name := {}
  let mut stack := starts.map (leafKey env)
  while h : stack.size > 0 do
    let k := stack[stack.size - 1]
    stack := stack.pop
    if seen.contains k then continue
    seen := seen.insert k
    for m in members.getD k #[k] do
      for u in uses env m do
        if isOurs env u then
          let ku := leafKey env u
          if !seen.contains ku then
            if !via.contains ku then via := via.insert ku m
            stack := stack.push ku
  return (seen, via)

/-! ## Files -/

def lines (s : String) : List String := (s.splitOn "\n").map fun l => l.trimAscii.toString

def fields (l : String) : List String :=
  ((l.splitOn " ").filter (· ≠ "")).flatMap fun w => (w.splitOn "\t").filter (· ≠ "")

def isComment (l : String) : Bool := l.isEmpty || l.startsWith "#"

partial def leanFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  if !(← dir.isDir) then return #[]
  let mut out := #[]
  for e in ← dir.readDir do
    if ← e.path.isDir then out := out ++ (← leanFiles e.path)
    else if e.path.extension == some "lean" then out := out.push e.path
  return out

def expectedHeader : String :=
"# Axiom footprints of the roots (ROOTS.txt) and of the test theorems (namespace EraseProof.Test).
# One line per declaration: <declaration> <axioms>
#   <axioms>: its `#print axioms`, comma-separated in the order propext, Classical.choice,
#             Quot.sound; `-` for none. sorryAx and Cardinal.exists_inaccessibles never occur.
# proof/scripts/check.sh compares this file with the computed .check/axioms.actual.
"

/-! ## The divergence register (C9) -/

/-- The fields of a register entry, in order (the preamble of `doc/DIVERGENCES.md`). -/
def dvFields : List String :=
  ["Our artifact", "Reference artifact", "What differs", "Why it is forced",
   "What was considered instead"]

/-- An entry `### DV-<n>` of the register: its fields `- **<name>:** <text>` (continuation lines
appended) and any other text. -/
structure DvEntry where
  id : String
  fields : Array (String × String) := #[]
  stray : Array String := #[]

/-- The entries of the register: a line `### <id> ...` opens an entry, any other heading closes
it. -/
def parseRegister (text : String) : Array DvEntry := Id.run do
  let mut out : Array DvEntry := #[]
  let mut cur : Option DvEntry := none
  for l in lines text do
    if l.startsWith "#" then
      if let some e := cur then out := out.push e
      cur := none
      if l.startsWith "### " then
        cur := some { id := (fields (l.drop 4).toString).headD "" }
    else if let some e := cur then
      if l.startsWith "- **" then
        match (l.drop 4).toString.splitOn ":**" with
        | name :: body@(_ :: _) =>
          let text := (":**".intercalate body).trimAscii.toString
          cur := some { e with fields := e.fields.push (name, text) }
        | _ => cur := some { e with stray := e.stray.push l }
      else if !l.isEmpty then
        match e.fields.back? with
        | some (n, b) => cur := some { e with fields := e.fields.pop.push (n, b ++ " " ++ l) }
        | none => cur := some { e with stray := e.stray.push l }
  if let some e := cur then out := out.push e
  return out

/-- The code spans (text between backquotes) of `s`. -/
def codeSpans (s : String) : List String :=
  go (s.splitOn "`") false
where
  go : List String → Bool → List String
    | [], _ => []
    | x :: xs, inside => if inside then x :: go xs false else go xs true

def isDvId (s : String) : Bool :=
  s.startsWith "DV-" && (s.drop 3).toString.length > 0 && (s.drop 3).toString.all Char.isDigit

/-- The register ids `DV-<n>` that `s` cites, in order, with repetitions. -/
def dvCitations (s : String) : List String :=
  ((s.splitOn "DV-").drop 1).filterMap fun part =>
    let ds := (part.takeWhile Char.isDigit).toString
    if ds.isEmpty then none else some s!"DV-{ds}"

/-- The line numbers of a citation suffix such as `642,723,768–835`. -/
def citedLines (s : String) : Option (List Nat) :=
  ((s.replace "–" "-").splitOn ",").foldr (init := some []) fun part acc => do
    let ns ← (part.splitOn "-").mapM String.toNat?
    return ns ++ (← acc)

/-- The code spans of `s` (text between backquotes), each with the text between it and the
previous span (or the start of `s`). -/
def codeSpansGaps (s : String) : List (String × String) :=
  go (s.splitOn "`")
where
  go : List String → List (String × String)
    | gap :: span :: rest => (gap, span) :: go rest
    | _ => []

/-- A MetaRocq source path `<dir>/theories/<F>.v`, with an optional `:<lines>` suffix. -/
def isMetaRocqCite (c : String) : Bool :=
  let path := (c.splitOn ":").headD c
  path.endsWith ".v" && (path.splitOn "/theories/").length == 2 && !path.startsWith "/"

/-- A citation of lines of the file cited last: `:<lines>`. -/
def isRelativeCite (c : String) : Bool :=
  c.startsWith ":" && c.length > 1 &&
    (c.drop 1).toString.all fun ch => ch.isDigit || ch == ',' || ch == '-' || ch == '–'

/-- A span that cites a file: a path of the library, of Metalean, of the shipping code or of
MetaRocq, or lines of the file cited last. -/
def isFileCite (c : String) : Bool :=
  c.startsWith "proof/" || c.startsWith "Metalean/" || c.startsWith "LeanToLambdaBox/" ||
    c == "LeanToLambdaBox.lean" || isMetaRocqCite c || isRelativeCite c

/-- The identifier a span names, for the check that a cited line shows it: the first word, and of
a dotted name its last component; none if that is not an identifier. -/
def citedIdent? (span : String) : Option String :=
  let w := (span.splitOn " ").headD ""
  let w := (w.splitOn ".").getLastD w
  if !w.isEmpty && !w.front.isDigit &&
      w.all (fun ch => ch.isAlphanum || ch == '_' || ch == '\'') then some w else none

/-- The parts of a line citation such as `642,723,768–835`: each a single line or a range. -/
def citedParts (s : String) : Option (List (Nat × Option Nat)) :=
  ((s.replace "–" "-").splitOn ",").mapM fun part =>
    match part.splitOn "-" with
    | [a] => a.toNat?.map (·, none)
    | [a, b] => do pure (← a.toNat?, some (← b.toNat?))
    | _ => none

/-! ## The C6 allow-list -/

/-- The constants of Metalean's modules reachable from `allowRoots` and from the declarations of
the inductive `Metalean.Export.QuotKind` (its constructors, recursor, `casesOn`, `noConfusion`,
...), through types, values and constructors. -/
def allowList (env : Environment) : Std.HashSet Name := Id.run do
  let quotKind := env.constants.fold (init := #[]) fun acc n _ =>
    if (`Metalean.Export.QuotKind).isPrefixOf n then acc.push n else acc
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array Name := allowRoots ++ quotKind
  while h : stack.size > 0 do
    let c := stack[stack.size - 1]
    stack := stack.pop
    if seen.contains c then continue
    let inMetalean := (moduleOf? env c).any (`Metalean).isPrefixOf
    if !inMetalean then continue
    seen := seen.insert c
    let block := match env.find? c with
      | some (.inductInfo v) => #[c] ++ v.ctors.toArray
      | _ => #[c]
    for m in block do
      for u in uses env m do
        if !seen.contains u then stack := stack.push u
  return seen

/-- Why an allow-listed constant may not be exempt: it is `partial`, `opaque`, an axiom, `unsafe`
or `implemented_by`. -/
def allowProblem? (env : Environment) (c : Name) : Option String :=
  match env.find? c with
  | none => some "not a declaration"
  | some ci =>
    if ci.isUnsafe then some "unsafe"
    else if (Compiler.getImplementedBy? env c).isSome then some "implemented_by"
    else match ci with
      | .opaqueInfo _ => some "opaque (or partial)"
      | .axiomInfo _ => some "an axiom"
      | .defnInfo v => if v.safety != .safe then some "partial" else none
      | _ => none

/-! ## The pin of the statements (C12b) -/

def isDep (env : Environment) (c : Name) : Bool :=
  match moduleOf? env c with
  | some m => depPrefixes.any (·.isPrefixOf m)
  | none => true

/-- The shipping functions under verification: the fragment test, the pure traversal and the entry
point behind `#erase`, which the statements are about. C12b pins their names, not their definitions,
and does not follow them, so a change to the code they run leaves the pin unchanged. Every other
shipping constant the statements reach (the λ□ syntax, the configuration, the view, the `casesOn`
recognizer and the other helpers through which the source semantics, the relation and the bridge
are defined) is hashed and followed like a constant of the library. -/
def underVerification : Array Name := #[`Erasure.collectDeps, `Erasure.erasePure,
  `Erasure.eraseEntry]

/-- A serialization of a level: full parameter names, no sharing. -/
def levelText : Level → String
  | .zero => "0"
  | .succ l => s!"(s {levelText l})"
  | .max a b => s!"(max {levelText a} {levelText b})"
  | .imax a b => s!"(imax {levelText a} {levelText b})"
  | .param n => s!"(p {n})"
  | .mvar m => s!"(?u {m.name})"

def binderText : BinderInfo → String
  | .default => "d"
  | .implicit => "i"
  | .strictImplicit => "s"
  | .instImplicit => "c"

/-- A serialization of an expression, appended to `acc`: full constant names and universe levels,
binder infos, literals; binder names and metadata are left out (alpha-equivalent expressions have
the same serialization). -/
partial def exprText (e : Expr) (acc : String) : String :=
  match e with
  | .bvar i => acc ++ s!" #{i}"
  | .fvar x => acc ++ s!" (fvar {x.name})"
  | .mvar m => acc ++ s!" (?m {m.name})"
  | .sort l => acc ++ s!" (sort {levelText l})"
  | .const c us => (us.foldl (fun a u => a ++ " " ++ levelText u) (acc ++ s!" (c {c}")) ++ ")"
  | .app f a => exprText a (exprText f (acc ++ " (a")) ++ ")"
  | .lam _ t b bi => exprText b (exprText t (acc ++ s!" (l {binderText bi}")) ++ ")"
  | .forallE _ t b bi => exprText b (exprText t (acc ++ s!" (f {binderText bi}")) ++ ")"
  | .letE _ t v b nd => exprText b (exprText v (exprText t (acc ++ s!" (let {nd}"))) ++ ")"
  | .lit (.natVal n) => acc ++ s!" (n {n})"
  | .lit (.strVal s) => acc ++ s!" (str {s.quote})"
  | .mdata _ b => exprText b acc
  | .proj S i b => exprText b (acc ++ s!" (proj {S} {i}") ++ ")"

def safetyText : DefinitionSafety → String
  | .safe => "safe"
  | .partial => "partial"
  | _ => "unsafe"

/-- What C12b hashes for a constant whose definition it follows, and the constants it follows: its
kind and flags (safety, `unsafe`; for inductives also `isRec`, `isReflexive`, the counts and `all`),
level parameters, type, the value of definitions and opaques, the constructors' names and types of
inductives. -/
def pinText (env : Environment) (c : Name) : Option (String × Array Name) :=
  match env.find? c with
  | none => none
  | some ci =>
    let head := s!"{c} {ci.levelParams}"
    let ty := exprText ci.type ""
    match ci with
    | .defnInfo v =>
      some (s!"defn {safetyText v.safety} {head} :{ty} :={exprText v.value ""}",
        v.type.getUsedConstants ++ v.value.getUsedConstants)
    | .opaqueInfo v =>
      some (s!"opaque {v.isUnsafe} {head} :{ty} :={exprText v.value ""}",
        v.type.getUsedConstants ++ v.value.getUsedConstants)
    | .thmInfo v => some (s!"thm {head} :{ty}", v.type.getUsedConstants)
    | .axiomInfo v => some (s!"axiom {v.isUnsafe} {head} :{ty}", v.type.getUsedConstants)
    | .recInfo v => some (s!"rec {v.isUnsafe} {v.k} {head} :{ty}", v.type.getUsedConstants)
    | .quotInfo _ => some (s!"quot {head} :{ty}", ci.type.getUsedConstants)
    | .ctorInfo v => some (s!"ctor {v.isUnsafe} {head} :{ty}", #[v.induct])
    | .inductInfo v =>
      let ctors := v.ctors.map fun n => match env.find? n with
        | some cc => s!" | {n} :{exprText cc.type ""}"
        | none => s!" | {n}"
      let deps := v.ctors.foldl (init := v.type.getUsedConstants) fun acc n =>
        match env.find? n with
        | some cc => acc ++ cc.type.getUsedConstants
        | none => acc
      some (s!"induct {v.isUnsafe} {v.isRec} {v.isReflexive} {v.numParams} {v.numIndices} " ++
        s!"{v.numNested} {v.all} {head} :{ty}" ++ String.join ctors, deps)

/-- The SHA-256 digests of `texts`, in order, computed by `python3`'s `hashlib` over the UTF-8 bytes
of each text; `tmp` is a scratch file. -/
def sha256s (tmp : System.FilePath) (texts : Array String) : IO (Array String) := do
  IO.FS.writeFile tmp ("\n".intercalate texts.toList ++ "\n")
  let out ← IO.Process.output { cmd := "python3", args := #["-c",
    "import hashlib, sys\nfor l in open(sys.argv[1], 'rb'):\n  print(hashlib.sha256(l.rstrip(b'\\n')).hexdigest())",
    tmp.toString] }
  if out.exitCode != 0 then throw <| .userError s!"python3 failed: {out.stderr}"
  let ds := ((out.stdout.splitOn "\n").filter (· ≠ "")).toArray
  if ds.size != texts.size then throw <| .userError "python3 returned the wrong number of digests"
  return ds

/-- The toolchain and dependency revisions C12b pins: `toolchain <lean-toolchain>` of the package
`dir`, and `dep <package> <rev>` for every git package of its `lake-manifest.json`. -/
def depPin (dir : System.FilePath) : IO (Array String) := do
  let tc := (← IO.FS.readFile (dir / "lean-toolchain")).trimAscii.toString
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile (dir / "lake-manifest.json")))
  let pkgs ← IO.ofExcept (json.getObjValAs? (Array Json) "packages")
  let mut out := #[s!"toolchain {tc}"]
  for p in pkgs do
    if let .ok "git" := p.getObjValAs? String "type" then
      let name ← IO.ofExcept (p.getObjValAs? String "name")
      let rev ← IO.ofExcept (p.getObjValAs? String "rev")
      out := out.push s!"dep {name} {rev}"
  return out.qsort (· < ·)

/-- The pin of the statement definitions `roots`: `root <name> <digest>` for each root, then, for
every other constant reached from them, `body <name> <digest>` (`pinText`, followed) if it is
declared in the library or in the shipping code, `name <name>` if it is one of
`underVerification` or a constant of a dependency; sorted. -/
def specPin (env : Environment) (roots : Array Name) (tmp : System.FilePath) :
    IO (Array String) := do
  let mut names : Array String := #[]
  let mut hashed : Array (String × String) := #[]
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array Name := roots.reverse
  while h : stack.size > 0 do
    let c := stack[stack.size - 1]
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    let isRoot := roots.contains c
    if !isRoot && (underVerification.contains c || isDep env c) then
      names := names.push s!"name {c}"
    else match pinText env c with
      | some (t, deps) =>
        hashed := hashed.push (s!"{if isRoot then "root" else "body"} {c}", t)
        for d in deps do
          if !seen.contains d then stack := stack.push d
      | none => names := names.push s!"name {c}"
  let ds ← sha256s tmp (hashed.map (·.2))
  let out := names ++ (hashed.zip ds).map fun ((k, _), d) => s!"{k} {d}"
  return out.qsort (· < ·)

def pinHeader : String :=
"# The pin of the statements (tools/Report.lean, C12b): `root <statement definition> <digest>`,
# `body <constant> <digest>` (SHA-256 of the serialized declaration), `name <constant>` (a shipping
# function under verification or a constant of a dependency, pinned by name), `toolchain <name>` and
# `dep <package> <rev>` (the root package's lean-toolchain and lake-manifest.json). Written by
# `tools/Report.lean --write-pin`; proof/scripts/check.sh compares it.
"

/-! ## Main -/

def main (args : List String) : IO UInt32 := do
  let cfg ← match parseArgs {} args with
    | .ok c => pure c
    | .error e => IO.eprintln s!"error: {e}"; return 2
  let imports := if cfg.imports.isEmpty then #[lib, `LeanToLambdaBox] else cfg.imports
  let failures ← IO.mkRef (#[] : Array String)
  let fail (check msg : String) : IO Unit := do
    IO.println s!"FAIL {check}: {msg}"
    failures.modify (·.push check)
  initSearchPath (← findSysroot)
  let env ← importModules (imports.map fun m => { module := m }) {}
  IO.FS.createDirAll cfg.out
  let pinTmp := cfg.out / "pin-texts.txt"
  if let some f := cfg.writePin then
    let roots := if cfg.pinRoots.isEmpty then pinRoots else cfg.pinRoots
    for r in roots do
      if !env.contains r then IO.eprintln s!"error: {r} is not a declaration"; return 1
    let pin := ((← specPin env roots pinTmp) ++ (← depPin cfg.shipping)).qsort (· < ·)
    IO.FS.writeFile f (pinHeader ++ "\n".intercalate pin.toList ++ "\n")
    IO.println s!"pin: {pin.size} lines written to {f}"
    return 0

  -- The library's modules and declarations.
  let ourMods := env.header.moduleNames.filter isOurModule
  let mut ours : Array Name := #[]
  for h : i in [0:env.header.moduleNames.size] do
    if isOurModule env.header.moduleNames[i] then
      ours := ours ++ (env.header.moduleData[i]!.constNames)
  ours := ours.qsort Name.lt
  let checked := ours.filter fun c => !isAux c
  let tests := checked.filter isTest
  let testThms := tests.filter fun c => match env.find? c with
    | some (.thmInfo _) => true
    | _ => false

  -- modules: every source file of the library is imported.
  let files := (← leanFiles (cfg.src / lib.toString)).push (cfg.src / s!"{lib}.lean")
  for f in files do
    if ← f.pathExists then
      let rel := (f.toString.drop (cfg.src.toString.length + 1)).toString
      let mod := ((rel.dropEnd ".lean".length).toString.replace "/" ".").toName
      if !ourMods.contains mod then
        fail "modules" s!"{f} (module {mod}) is not imported by {imports.toList}"

  -- C9 divergences: the register's entries and what they cite.
  if !(← cfg.divergences.pathExists) then
    fail "divergences" s!"{cfg.divergences} does not exist"
  else
    let entries := parseRegister (← IO.FS.readFile cfg.divergences)
    let mut ids : Array String := #[]
    for e in entries do
      if !isDvId e.id then fail "divergences" s!"entry `{e.id}`: the id is not DV-<n>"
      if ids.contains e.id then fail "divergences" s!"entry {e.id} occurs twice"
      ids := ids.push e.id
      for l in e.stray do fail "divergences" s!"{e.id}: text outside the fields: {l}"
      let names := e.fields.toList.map (·.1)
      if names != dvFields then
        fail "divergences" s!"{e.id}: fields {names}, expected {dvFields}"
      let artifact := (e.fields.find? (·.1 == "Our artifact")).map (·.2) |>.getD ""
      if !(codeSpans artifact).any (fun c => c.startsWith s!"{lib}." && env.contains c.toName) then
        fail "divergences" s!"{e.id}: the artifact field cites no declaration of {lib}"
      for (_, body) in e.fields do
        -- `last`: the file that a span `:<lines>` cites lines of, and whether it is MetaRocq's.
        let mut last : Option (System.FilePath × Bool) := none
        -- Set when the file cited last is MetaRocq's and no checkout is given.
        let mut lastUnchecked := false
        let mut prev : Option String := none
        for (gap, c) in codeSpansGaps body do
          let thisPrev := prev
          prev := some c
          if c.any Char.isWhitespace then continue
          if c.startsWith s!"{lib}." || c.startsWith "Metalean." || c.startsWith "Erasure." then
            if !env.contains c.toName then
              fail "divergences" s!"{e.id} cites `{c}`, which is not a declaration"
            continue
          if !isFileCite c then continue
          -- A file citation: the file, and the lines it cites.
          let (path, sfx) := match c.splitOn ":" with
            | [p] => (p, none)
            | p :: rest => (p, some (":".intercalate rest))
            | [] => (c, none)
          let target? : Option (System.FilePath × Bool) :=
            if isRelativeCite c then last
            else if c.startsWith "proof/" then some (cfg.src / (path.drop "proof/".length).toString, false)
            else if c.startsWith "Metalean/" then some (cfg.metalean / path, false)
            else if c.startsWith "LeanToLambdaBox" then some (cfg.shipping / path, false)
            else cfg.metarocq.map fun d => (d / path, true)
          let some (f, mr) := target?
            | if !isRelativeCite c then
                lastUnchecked := true
              else if !lastUnchecked then
                fail "divergences" s!"{e.id} cites `{c}` with no file cited before it in the field"
              continue
          if !isRelativeCite c then
            last := some (f, mr)
            lastUnchecked := false
          if !(← f.pathExists) then
            fail "divergences" s!"{e.id} cites `{c}`: {f} does not exist"
            continue
          let some spec := (if isRelativeCite c then some (c.drop 1).toString else sfx) | continue
          let src := (← IO.FS.readFile f).splitOn "\n"
          let n := src.length - (if src.getLastD "" == "" then 1 else 0)
          match citedParts spec with
          | none => fail "divergences" s!"{e.id} cites `{c}`: malformed line numbers"
          | some parts =>
            for (a, b?) in parts do
              if a == 0 || a > n || b?.any (fun b => b < a || b > n) then
                fail "divergences" s!"{e.id} cites `{c}`: {f} has {n} lines"
              -- A MetaRocq line cited right after an identifier shows that identifier.
              else if mr && b?.isNone then
                let g := gap.trimAscii.toString
                if g == "" || g == "(" || g == "," then
                  if let some p := thisPrev then
                    if !isFileCite p then
                      if let some name := citedIdent? p then
                        let window := " ".intercalate ((src.drop (a - 1)).take 4)
                        if !((window.splitOn name).length > 1) then
                          fail "divergences" s!"{e.id} cites `{p}` at `{c}`, but {f}:{a}-{a + 3} does not mention {name}"
    if cfg.metarocq.isNone then
      IO.println "note: divergences: MetaRocq citations not checked (no --metarocq)"
    -- Every id that the register, the library or the shipping sources cite is an entry.
    let shippingFiles := (← leanFiles (cfg.shipping / "LeanToLambdaBox")).push
      (cfg.shipping / "LeanToLambdaBox.lean")
    for f in #[cfg.divergences] ++ files ++ shippingFiles do
      if !(← f.pathExists) then continue
      let cited := (dvCitations (← IO.FS.readFile f)).eraseDups
      for d in cited do
        if !ids.contains d then
          fail "divergences" s!"{f} cites {d}, which is not an entry of {cfg.divergences}"

  -- Footprints of every declaration of the library.
  -- Compiler implementations of recursive definitions (`f._unsafe_rec`) are partial or unsafe
  -- and may be mutually recursive; they are not part of the logic and are skipped. Any other
  -- partial or unsafe declaration fails.
  let isUnsafeDecl (c : Name) : Bool := match env.find? c with
    | some (.defnInfo v) => v.safety != .safe
    | some ci => ci.isUnsafe
    | none => false
  for c in ours do
    if isUnsafeDecl c && !isAux c then fail "axioms" s!"{c} is partial or unsafe"
  let logical := ours.filter fun c => !isUnsafeDecl c
  let (memo, cycles) := footprints env logical {}
  for c in cycles do IO.println s!"note: dependency cycle through {c} (footprints may be partial)"
  let fpOf (c : Name) : Footprint := memo.getD (fpKey env c) {}
  let mut footLines : Array String := #[]
  for c in logical do
    let fp := fpOf c
    let own := sortAxioms fp.axioms
    -- C3/C4
    for a in own do
      if !allowedAxioms.contains a then
        let why :=
          if a == ``sorryAx then "a sorry"
          else if a == metaleanAxiom then "Metalean's set-theoretic axiom"
          else if a.components.contains `_native then "a native-code axiom"
          else "not allowed"
        fail "axioms" s!"{c} depends on {a} ({why})"
    if !isAux c then
      let lean := leanAxioms env c
      if lean.qsort Name.lt != (fp.axioms.toArray.qsort Name.lt) then
        fail "axioms" s!"{c}: computed footprint {own.toList} differs from #print axioms {lean.toList}"
    -- C5
    for s in fp.sorries do
      fail "sorry" s!"{c} reaches sorryAx through {s}"
    if !isAux c then
      let holders := fp.sorries.toArray.qsort Name.lt
      footLines := footLines.push
        s!"{c} {axiomsField fp} {showList (holders.map toString)}"
  IO.FS.writeFile (cfg.out / "footprints.txt")
    ("# <declaration> <axioms> <sorry declarations reached>\n" ++
      "\n".intercalate footLines.toList ++ (if footLines.isEmpty then "" else "\n"))

  -- ROOTS.txt
  let mut roots : Array Name := #[]
  let rootsText ← IO.FS.readFile cfg.roots
  for l in lines rootsText do
    if isComment l then continue
    match fields l with
    | r :: consumer :: rest =>
      if !rest.isEmpty then fail "leaves" s!"ROOTS.txt: too many fields: {l}"
      let r := r.toName
      let c := consumer.toName
      if roots.contains r then fail "leaves" s!"ROOTS.txt: {r} is listed twice"
      roots := roots.push r
      match env.find? r with
      | none => fail "leaves" s!"ROOTS.txt: {r} is not a declaration"
      | some info =>
        if !isOurs env r then fail "leaves" s!"ROOTS.txt: {r} is not a declaration of {lib}"
        else if isTest r || isAux r then fail "leaves" s!"ROOTS.txt: {r} is a test or an auxiliary"
        else if !info.isTheorem then fail "leaves" s!"ROOTS.txt: {r} is not a theorem"
      if consumer != "FINAL" && env.contains c then
        fail "leaves" s!"ROOTS.txt: the consumer {c} of {r} has landed; remove the line"
    | _ => fail "leaves" s!"ROOTS.txt: expected `<declaration> <consumer or FINAL>`: {l}"

  -- C7 no leaves, C6 tests, from the roots.
  let mut members : Std.HashMap Name (Array Name) := {}
  for c in ours do
    let k := leafKey env c
    members := members.insert k ((members.getD k #[]).push c)
  let (reached, via) := reach env members
    (roots ++ pinRoots.filter env.contains ++ (statements.map (·.1)).filter env.contains ++
      (corollaries.map (·.1)).filter env.contains)
  let mut leafKeys : Array Name := #[]
  for c in checked do
    if isTest c then
      if reached.contains (leafKey env c) then
        fail "hygiene" s!"test declaration {c} is used by {via.getD (leafKey env c) c}"
    else
      let k := leafKey env c
      if !reached.contains k && !leafKeys.contains k then
        leafKeys := leafKeys.push k
        let n := (members.getD k #[]).size
        let block := if n > 1 then s!" (a node of {n} declarations)" else ""
        fail "leaves" s!"{k}{block} is not reachable from a root of ROOTS.txt or a statement"
  -- Test definitions are used by test theorems.
  let (testReached, _) := reach env members testThms
  for c in tests do
    if !testThms.contains c && !testReached.contains (leafKey env c) then
      fail "leaves" s!"test {c} is not a theorem and no test theorem uses it"
  for r in roots do
    for r' in roots do
      if r != r' && env.contains r && env.contains r' then
        let (seen, _) := reach env members #[r']
        if seen.contains (leafKey env r) then
          fail "leaves" s!"root {r} is reachable from root {r'}; remove it from ROOTS.txt"

  -- C6 Metalean's frontend, checkers, export and set-theoretic model are unreachable from
  -- non-test declarations, except the allow-listed term builders.
  let allowed := allowList env
  let mut exempt := 0
  for c in allowed do
    if isForbidden c || (moduleOf? env c).any isForbidden then
      exempt := exempt + 1
      if let some why := allowProblem? env c then
        fail "hygiene" s!"allow-listed {c} is {why}"
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array (Name × Name) := #[]
  for c in ours do
    if !isTest c then stack := stack.push (c, c)
  while h : stack.size > 0 do
    let (c, origin) := stack[stack.size - 1]
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    let mod? := moduleOf? env c
    if (isForbidden c || mod?.any isForbidden) && !isExempt allowed c then
      fail "hygiene" s!"{origin} reaches {c} (module {(mod?.map toString).getD "?"})"
    let walk := match mod? with
      | some m => isWalkedModule m
      | none => false
    if walk then
      let block := match env.find? c with
        | some (.inductInfo v) => #[c] ++ v.ctors.toArray
        | _ => #[c]
      for m in block do
        for u in uses env m do
          if !seen.contains u then stack := stack.push (u, origin)

  -- axioms.expected: roots and test theorems.
  let mut actual : Array String := #[]
  let mut want : Array Name := roots.filter env.contains
  for t in testThms do
    if !want.contains t then want := want.push t
  want := want.qsort Name.lt
  let mut report : Array String := #[]
  for d in want do
    let fp := fpOf d
    actual := actual.push s!"{d} {axiomsField fp}"
    report := report.push s!"  {if isTest d then "test" else "root"} {d}: {axiomsField fp}"
  IO.FS.writeFile (cfg.out / "axioms.actual")
    (expectedHeader ++ "\n".intercalate actual.toList ++ (if actual.isEmpty then "" else "\n"))
  let expText ← IO.FS.readFile cfg.expected
  let mut expected : Std.HashMap Name String := {}
  for l in lines expText do
    if isComment l then continue
    match fields l with
    | [d, a] =>
      if expected.contains d.toName then fail "expected" s!"{cfg.expected}: {d} is listed twice"
      expected := expected.insert d.toName a
    | _ => fail "expected" s!"{cfg.expected}: expected `<declaration> <axioms>`: {l}"
  for d in want do
    let got := axiomsField (fpOf d)
    match expected[d]? with
    | none => fail "expected" s!"{d} has no line in {cfg.expected} (computed: {got})"
    | some e =>
      if e != got then fail "expected" s!"{d}: {cfg.expected} says {e}, computed {got}"
  for (d, _) in expected.toList do
    if !want.contains d then
      fail "expected" s!"{cfg.expected} lists {d}, which is neither a root nor a test theorem"

  -- C12 the statements: each proved theorem against its statement definition.
  for (thm, stmt) in statements do
    match env.find? stmt with
    | some (.defnInfo v) =>
      if !isOurs env stmt then fail "statements" s!"{stmt} is not a declaration of {lib}"
      else if v.type != .sort .zero then fail "statements" s!"{stmt} is not of type Prop"
    | _ => fail "statements" s!"{stmt} is not a definition"
    match env.find? thm with
    | none =>
      if unproved.contains thm then IO.println s!"statements: {thm}: not yet proved"
      else fail "statements" s!"{thm} does not exist and is not listed in `unproved`"
    | some ci =>
      if unproved.contains thm then
        fail "statements" s!"{thm} exists; remove it from `unproved`"
      if !ci.isTheorem || !isOurs env thm then
        fail "statements" s!"{thm} is not a theorem of {lib}"
      else if !Kernel.isDefEqGuarded env {} ci.type (mkConst stmt) then
        fail "statements" s!"the type of {thm} is not its statement {stmt}"

  -- C12 the final form.
  if cfg.final then
    if !unproved.isEmpty then
      fail "final" s!"theorems not yet proved: {unproved.toList}"
    let rootLines := ((lines rootsText).filter (!isComment ·)).map fields
    if rootLines.filter (·.getLast? == some "FINAL") != [[finalTheorem.toString, "FINAL"]] then
      fail "final" s!"{cfg.roots}: `{finalTheorem} FINAL` is not the only line with consumer FINAL"
    let theoremFp? (d : Name) : Option Footprint :=
      match env.find? d with
      | some (.thmInfo _) => if isOurs env d then some (fpOf d) else none
      | _ => none
    let std3 := showList (allowedAxioms.map toString)
    for (inst, hyps) in finalInstances do
      for d in #[finalTheorem, inst] ++ hyps do
        match theoremFp? d with
        | none => fail "final" s!"{d} is not a theorem of {lib}"
        | some fp =>
          let exact := d == finalTheorem || d == inst
          if (exact && axiomsField fp != std3) || !fp.sorries.isEmpty ||
              fp.axioms.toArray.any (!allowedAxioms.contains ·) then
            fail "final" s!"{d}: footprint {axiomsField fp}, expected {if exact then "exactly" else "within"} {std3}"
      if env.contains inst then
        let used := uses env inst
        for h in #[finalTheorem] ++ hyps do
          if !used.contains h then fail "final" s!"{inst} does not mention {h}"
    for (cor, insts) in corollaries do
      for d in #[cor] ++ insts do
        match theoremFp? d with
        | none => fail "final" s!"{d} is not a theorem of {lib}"
        | some fp =>
          if (d == cor && axiomsField fp != std3) || !fp.sorries.isEmpty ||
              fp.axioms.toArray.any (!allowedAxioms.contains ·) then
            fail "final" s!"{d}: footprint {axiomsField fp}, expected {if d == cor then "exactly" else "within"} {std3}"
      for inst in insts do
        if env.contains inst && !(uses env inst).contains cor then
          fail "final" s!"{inst} does not mention {cor}"

  -- C12b the pin of the statements.
  if !(← cfg.pin.pathExists) then
    fail "pin" s!"{cfg.pin} does not exist"
  else
    let pinned := (lines (← IO.FS.readFile cfg.pin)).filter (!isComment ·) |>.toArray
    -- Every pinned constant exists.
    for l in pinned do
      match fields l with
      | ["root", c, _] | ["body", c, _] | ["name", c] =>
        if !env.contains c.toName then
          fail "pin" s!"{cfg.pin} pins {c}, which is not a declaration"
      | ["toolchain", _] | ["dep", _, _] => pure ()
      | _ => fail "pin" s!"{cfg.pin}: malformed line: {l}"
    for r in pinRoots do
      if !pinned.any (·.startsWith s!"root {r} ") then
        fail "pin" s!"{cfg.pin} has no line `root {r} ...`"
    -- The toolchain and the dependency revisions, of the root package and of proof/.
    let pinnedDeps := pinned.filter fun l => l.startsWith "toolchain " || l.startsWith "dep "
    let vers := s!"v{Lean.versionString}"
    for (what, dir) in [("root package", cfg.shipping), ("proof package", cfg.src)] do
      let got ← depPin dir
      if got != pinnedDeps.qsort (· < ·) then
        let extra := got.filter (!pinnedDeps.contains ·)
        let missing := pinnedDeps.filter (!got.contains ·)
        fail "pin" s!"the {what}'s toolchain or dependency revisions differ from {cfg.pin}: actual only {extra.toList}, pinned only {missing.toList}"
    for l in pinnedDeps do
      if let ["toolchain", tc] := fields l then
        if !tc.endsWith vers then
          fail "pin" s!"the running Lean {Lean.versionString} is not the pinned toolchain {tc}"
    -- The pin computed from the statement definitions is the pinned one.
    if pinRoots.all env.contains then
      let computed := ((← specPin env pinRoots pinTmp) ++ (← depPin cfg.shipping)).qsort (· < ·)
      let sorted := pinned.qsort (· < ·)
      if computed != sorted then
        let extra := computed.filter (!sorted.contains ·)
        let missing := sorted.filter (!computed.contains ·)
        fail "pin" s!"the pin differs from {cfg.pin}: computed only {(extra.toList.take 5)}, pinned only {(missing.toList.take 5)}"
      IO.println s!"note: pin: {pinned.size} pinned lines compared"
  IO.println s!"hygiene: {exempt} constant(s) of Metalean's frontend and export allow-listed"

  IO.println s!"report: {ours.size} declarations ({checked.size} checked, {tests.size} tests) in {ourMods.size} module(s); {roots.size} root(s)"
  for l in report do IO.println l
  let fs ← failures.get
  for check in ["axioms", "sorry", "hygiene", "leaves", "expected", "modules", "divergences",
      "statements", "pin", "final"] do
    let n := (fs.filter (· == check)).size
    if check == "final" && !cfg.final then IO.println "final: skipped (--no-final)"
    else IO.println s!"{check}: {if n == 0 then "ok" else s!"{n} failure(s)"}"
  return if fs.isEmpty then 0 else 1

end EraseProofReport

def main (args : List String) : IO UInt32 := EraseProofReport.main args
