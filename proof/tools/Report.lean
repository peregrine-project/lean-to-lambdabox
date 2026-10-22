import Lean

/-!
# The Lean side of `proof/scripts/check.sh`

Run from `proof/` as `lake env lean --run tools/Report.lean [OPTION...]`. It imports the library
(by default the module `EraseProof`) and checks, over every declaration of the library's modules
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
  declared in the module `Metalean.Checker.Acceleration.Literal`).
* C7 `leaves`: every declaration outside `EraseProof.Test` is reachable from a root of `ROOTS.txt`
  (through types and values; a mutual block, an inductive with its constructors, recursors,
  structure projections and the declarations `inductive` generates for it, those of its nested
  occurrences included, is one node; generated auxiliaries, `isAux`, are not checked); every root
  is a theorem of the library whose planned consumer has not landed; no root is reachable from
  another root; every test that is not a theorem is reachable from a test theorem.
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
* C12 `final`: the final form. `ROOTS.txt` is the single line `EraseProof.erase_correct FINAL`, so
  C7 checks reachability from the final theorem `erase_correct` (tests are roots by themselves).
  `erase_correct` is a theorem whose footprint is exactly `propext`, `Classical.choice`,
  `Quot.sound`, as is that of its instance on NV-1, `EraseProof.Test.NV1.final`, which applies
  `erase_correct` to NV-1's hypothesis terms (`finalHypotheses`), theorems within the same three
  axioms. The test `EraseProof.Test.Stub.erase_correct` (`finalStatement`), the approved
  statement written out, is a theorem that mentions `erase_correct` and whose type is that of
  `erase_correct` (`Expr.eqv`, binder order included). Skipped with `--no-final`.

Options: `--import M` (repeatable; replaces the default `EraseProof`), `--roots FILE`
(`ROOTS.txt`), `--expected FILE` (`axioms.expected`), `--out DIR` (`.check`), `--src DIR` (`.`),
`--divergences FILE` (`../doc/DIVERGENCES.md`), `--metalean DIR` (`../.lake/packages/metalean`),
`--shipping DIR` (`..`, the root package, whose `LeanToLambdaBox.lean` and `LeanToLambdaBox/` are
scanned for `DV-<n>` citations), `--metarocq DIR` (a MetaRocq checkout; without it, MetaRocq
citations are not checked), `--no-final` (skips C12).
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

/-- Divergence ids that the shipping sources (`LeanToLambdaBox/`) cite from the l4l register they
were ported with, and that this register does not contain yet. C9 lists them instead of failing;
C12 fails while any is cited and missing. -/
def pendingShippingDv : Array String := #["DV-3", "DV-4", "DV-7", "DV-12", "DV-13", "DV-14", "DV-17"]

/-- The final theorem, the only root of `ROOTS.txt` in the final form (C12). -/
def finalTheorem : Name := `EraseProof.erase_correct

/-- The approved statement of the final theorem, written out as a test proved by it (C12). -/
def finalStatement : Name := `EraseProof.Test.Stub.erase_correct

/-- The instance of the final theorem on NV-1 (C12). -/
def finalInstance : Name := `EraseProof.Test.NV1.final

/-- NV-1's terms for the hypotheses of the final theorem, which `finalInstance` passes to it
(C12). -/
def finalHypotheses : Array Name := #[
  `EraseProof.Test.NV1.henv, `EraseProof.Test.NV1.hwf, `EraseProof.Test.NV1.hview,
  `EraseProof.Test.NV1.he, `EraseProof.Test.NV1.hty, `EraseProof.Test.NV1.hfrag,
  `EraseProof.Test.NV1.hrun, `EraseProof.Test.NV1.hev]

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
  | a :: _ => .error s!"unknown or incomplete option {a}"

/-! ## Names -/

def isNumbered (pre s : String) : Bool :=
  s.length > pre.length && s.startsWith pre && (s.toList.drop pre.length).all Char.isDigit

/-- A name component that marks a compiler- or elaborator-generated auxiliary. -/
def isAuxComponent (s : String) : Bool :=
  s.startsWith "_" || isNumbered "match_" s || isNumbered "proof_" s || isNumbered "eq_" s

/-- Last components of generated declarations: auxiliary recursors, `noConfusion`, equation and
induction principles, injectivity lemmas, `sizeOf` lemmas. -/
def auxLast : List String :=
  ["rec", "below", "ibelow", "brecOn", "binductionOn", "casesOn", "recOn", "noConfusion",
   "noConfusionType", "eq_def", "induct", "mutual_induct", "inj", "injEq", "ctorIdx",
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

/-- The fields of a register entry, in order (`doc/DIVERGENCES.md`, spec §3.5). -/
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

/-! ## Main -/

def main (args : List String) : IO UInt32 := do
  let cfg ← match parseArgs {} args with
    | .ok c => pure c
    | .error e => IO.eprintln s!"error: {e}"; return 2
  let imports := if cfg.imports.isEmpty then #[lib] else cfg.imports
  let failures ← IO.mkRef (#[] : Array String)
  let pending ← IO.mkRef (#[] : Array String)
  let fail (check msg : String) : IO Unit := do
    IO.println s!"FAIL {check}: {msg}"
    failures.modify (·.push check)
  initSearchPath (← findSysroot)
  let env ← importModules (imports.map fun m => { module := m }) {}
  IO.FS.createDirAll cfg.out

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
          if shippingFiles.contains f && pendingShippingDv.contains d then
            pending.modify (·.push s!"{f}: {d}")
          else
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
      if rest.length > 1 then fail "leaves" s!"ROOTS.txt: too many fields: {l}"
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
    | _ => fail "leaves" s!"ROOTS.txt: expected `<declaration> <consumer or FINAL> [<task>]`: {l}"

  -- C7 no leaves, C6 tests, from the roots.
  let mut members : Std.HashMap Name (Array Name) := {}
  for c in ours do
    let k := leafKey env c
    members := members.insert k ((members.getD k #[]).push c)
  let (reached, via) := reach env members roots
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
        fail "leaves" s!"{k}{block} is not reachable from a root of ROOTS.txt"
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
  -- non-test declarations.
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
    if isForbidden c || mod?.any isForbidden then
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

  let pendingDv ← pending.get
  if !pendingDv.isEmpty then
    IO.println s!"note: divergences: {pendingDv.size} shipping citation(s) of l4l ids without an entry yet (pendingShippingDv): {", ".intercalate pendingDv.toList}"

  -- C12 the final form.
  if cfg.final then
    for p in pendingDv do
      fail "final" s!"the shipping source cites a divergence id without an entry: {p}"
    let rootLines := ((lines rootsText).filter (!isComment ·)).map fields
    if rootLines != [[finalTheorem.toString, "FINAL"]] then
      fail "final" s!"{cfg.roots} is not the single line `{finalTheorem} FINAL`"
    let theoremFp? (d : Name) : Option Footprint :=
      match env.find? d with
      | some (.thmInfo _) => if isOurs env d then some (fpOf d) else none
      | _ => none
    let std3 := showList (allowedAxioms.map toString)
    for d in #[finalTheorem, finalInstance] ++ finalHypotheses do
      match theoremFp? d with
      | none => fail "final" s!"{d} is not a theorem of {lib}"
      | some fp =>
        let exact := d == finalTheorem || d == finalInstance
        if (exact && axiomsField fp != std3) || !fp.sorries.isEmpty ||
            fp.axioms.toArray.any (!allowedAxioms.contains ·) then
          fail "final" s!"{d}: footprint {axiomsField fp}, expected {if exact then "exactly" else "within"} {std3}"
    if env.contains finalInstance then
      let used := uses env finalInstance
      for h in #[finalTheorem] ++ finalHypotheses do
        if !used.contains h then fail "final" s!"{finalInstance} does not mention {h}"
    match env.find? finalTheorem, env.find? finalStatement with
    | some ci, some (.thmInfo st) =>
      if !isOurs env finalStatement then
        fail "final" s!"{finalStatement} is not a declaration of {lib}"
      if !(uses env finalStatement).contains finalTheorem then
        fail "final" s!"{finalStatement} does not mention {finalTheorem}"
      if !ci.type.eqv st.type then
        fail "final" s!"the type of {finalTheorem} is not that of {finalStatement}"
    | _, _ => fail "final" s!"{finalStatement} is not a theorem of {lib}"

  IO.println s!"report: {ours.size} declarations ({checked.size} checked, {tests.size} tests) in {ourMods.size} module(s); {roots.size} root(s)"
  for l in report do IO.println l
  let fs ← failures.get
  for check in ["axioms", "sorry", "hygiene", "leaves", "expected", "modules", "divergences",
      "final"] do
    let n := (fs.filter (· == check)).size
    if check == "final" && !cfg.final then IO.println "final: skipped (--no-final)"
    else IO.println s!"{check}: {if n == 0 then "ok" else s!"{n} failure(s)"}"
  return if fs.isEmpty then 0 else 1

end EraseProofReport

def main (args : List String) : IO UInt32 := EraseProofReport.main args
