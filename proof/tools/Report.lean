import Lean

/-!
# The Lean side of `proof/scripts/check.sh`

Run from `proof/` as `lake env lean --run tools/Report.lean [OPTION...]`. It imports the library
(by default the module `EraseProof`) together with the lean4lean modules that declare the
`sorry`s L1–L8, and checks, over every declaration of the library's modules (module `EraseProof`
or `EraseProof.*`):

* C3/C4 `axioms`: the footprint of every declaration, computed as `#print axioms` computes it
  (`Lean.collectAxioms`: types and values, an inductive together with its constructors), lies in
  `propext`, `Classical.choice`, `Quot.sound`, `sorryAx`; so no `Verify/Axioms.lean` axiom of
  lean4lean and no `._native.` axiom occurs. The footprints are cross-checked against
  `Lean.collectAxioms` itself.
* C5 `sorry`: every `sorryAx` a declaration reaches comes from one of lean4lean's `sorry`
  declarations L1–L8 (`sorryLabels`), or, for a test, also `TrProj` (`testOnlySorryLabels`). The
  report lists the labels each root and test reaches.
* C6 `hygiene`: no non-test declaration reaches a constant named `Lean4Lean.TrExprS*`,
  `Lean4Lean.TrExpr`, `Lean4Lean.TrExpr.*` or `Lean4Lean.TrProj*`, or a declaration of the test
  namespace `EraseProof.Test`.
* C7 `leaves`: every declaration outside `EraseProof.Test` is reachable from a root of `ROOTS.txt`
  (through types and values; a mutual block, an inductive with its constructors, recursors and
  structure projections, is one node; generated auxiliaries, `isAux`, are not checked); every root
  is a theorem of the library whose planned consumer has not landed; no root is reachable from
  another root.
* `expected`: the footprints of the roots and of the test theorems equal `axioms.expected`.
* `modules`: every `.lean` file of the library's source tree is imported.
* C9 `divergences`: every entry `### DV-<n>` of the divergence register has exactly the fields
  `dvFields`, in order, and its artifact field cites a declaration of the library; every code span
  of an entry that is a name `EraseProof.*` or `Lean4Lean.*` is a declaration, a path
  `proof/*.lean` is a file of this package, and a lean4lean path `Lean4Lean/*.lean[:lines]` is a
  file of the lean4lean checkout with those lines.

Options: `--import M` (repeatable; replaces the default `EraseProof`), `--roots FILE`
(`ROOTS.txt`), `--expected FILE` (`axioms.expected`), `--out DIR` (`.check`), `--src DIR` (`.`),
`--divergences FILE` (`../doc/DIVERGENCES.md`), `--lean4lean DIR` (`../.lake/packages/lean4lean`).
It writes `DIR/footprints.txt` (every declaration) and `DIR/axioms.actual` (the file
`axioms.expected` should be), prints one line per check, and exits with 1 if a check fails.
-/

open Lean

namespace EraseProofReport

/-- The library's name: its modules are `lib` and `lib.*`, its tests live in namespace
`lib.Test`. -/
def lib : Name := `EraseProof

/-- The axioms a declaration of the library may depend on, in the order footprints print them. -/
def allowedAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound, ``sorryAx]

/-- lean4lean's `sorry` declarations (`master` 8223d223) that the library may reach, with labels. -/
def sorryLabels : Array (String × Name) := #[
  ("L1", `Lean4Lean.VInductDecl.WF),
  ("L2", `Lean4Lean.VEnv.addInduct),
  ("L3", `Lean4Lean.VEnv.addInduct_WF),
  ("L4", `Lean4Lean.VEnv.IsDefEqU.sort_inv),
  ("L5", `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified),
  ("L6", `Lean4Lean.VEnv.IsDefEqU.sort_forallE_inv),
  ("L7", `Lean4Lean.VEnv.IsDefEqU.weakN_iff),
  ("L8", `Lean4Lean.VEnv.NormalEq.parRed)]

/-- Further `sorry` declarations that only test declarations may reach, with labels: lean4lean's
`TrProj` (`Lean4Lean/Verify/Typing/Expr.lean:68`), which the bridge tests reach through `TrExprS`
and `TrEnv'` (exception E-1). -/
def testOnlySorryLabels : Array (String × Name) := #[("TrProj", `Lean4Lean.TrProj)]

/-- The modules declaring `sorryLabels` and `testOnlySorryLabels`; imported so that the names are
checked. -/
def labelModules : Array Name := #[
  `Lean4Lean.Theory.Inductive,
  `Lean4Lean.Theory.Typing.InductiveLemmas,
  `Lean4Lean.Theory.Typing.Injectivity,
  `Lean4Lean.Theory.Typing.UniqueTyping,
  `Lean4Lean.Theory.Typing.ChurchRosser,
  `Lean4Lean.Verify.Typing.Expr]

/-- lean4lean's bridge to Lean expressions, which the library ports instead of using (C6). -/
def isForbiddenBridge (n : Name) : Bool :=
  let s := n.toString
  n == `Lean4Lean.TrExpr || s.startsWith "Lean4Lean.TrExprS" ||
    s.startsWith "Lean4Lean.TrExpr." || s.startsWith "Lean4Lean.TrProj"

structure Config where
  imports : Array Name := #[]
  roots : System.FilePath := "ROOTS.txt"
  expected : System.FilePath := "axioms.expected"
  out : System.FilePath := ".check"
  src : System.FilePath := "."
  divergences : System.FilePath := "../doc/DIVERGENCES.md"
  lean4lean : System.FilePath := "../.lake/packages/lean4lean"

partial def parseArgs (cfg : Config) : List String → Except String Config
  | [] => .ok cfg
  | "--import" :: m :: rest => parseArgs { cfg with imports := cfg.imports.push m.toName } rest
  | "--roots" :: f :: rest => parseArgs { cfg with roots := f } rest
  | "--expected" :: f :: rest => parseArgs { cfg with expected := f } rest
  | "--out" :: f :: rest => parseArgs { cfg with out := f } rest
  | "--src" :: f :: rest => parseArgs { cfg with src := f } rest
  | "--divergences" :: f :: rest => parseArgs { cfg with divergences := f } rest
  | "--lean4lean" :: f :: rest => parseArgs { cfg with lean4lean := f } rest
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

/-- Constants whose bodies are followed by the hygiene walk: ours, the shipping code, lean4lean.
Nothing outside these can mention a lean4lean constant. -/
def isWalkedModule (m : Name) : Bool :=
  isOurModule m || (`LeanToLambdaBox).isPrefixOf m || (`Lean4Lean).isPrefixOf m

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

/-- Declarations `C.s` that `inductive` and `structure` generate for a constructor `C`. -/
def ctorGenerated : List String := ["inj", "injEq", "sizeOf_spec", "elim", "noConfusion", "hinj"]

/-- No-leaves node: a mutual block; an inductive block with its constructors, recursors,
structure projections and the declarations `inductiveGenerated`, `ctorGenerated`. -/
def leafKey (env : Environment) (c : Name) : Name :=
  let generated? : Option Name := match c with
    | .str p s =>
      match env.find? p with
      | some (.inductInfo _) => if inductiveGenerated.contains s then some (inductKey env p) else none
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

def labelOf? (tables : Array (String × Name)) (n : Name) : Option String :=
  (tables.find? fun (_, m) => m == ownerOf n).map (·.1)

def labelOrder (l : String) : Nat :=
  match (sorryLabels ++ testOnlySorryLabels).findIdx? (·.1 == l) with
  | some i => i
  | none => 1000

def labelsOf (tables : Array (String × Name)) (fp : Footprint) : Array String :=
  let ls := fp.sorries.foldl (init := #[]) fun acc s =>
    match labelOf? tables s with
    | some l => if acc.contains l then acc else acc.push l
    | none => acc
  ls.qsort fun a b => labelOrder a < labelOrder b

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
# One line per declaration: <declaration> <axioms> <sorry labels>
#   <axioms>: its `#print axioms`, comma-separated in the order propext, Classical.choice,
#             Quot.sound, sorryAx; `-` for none.
#   <sorry labels>: the lean4lean `sorry` declarations it reaches (L1-L8, and TrProj for tests;
#             see tools/Report.lean `sorryLabels`, `testOnlySorryLabels`), comma-separated;
#             `-` for none.
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

/-- The line numbers of a citation suffix such as `642,723,768–835`. -/
def citedLines (s : String) : Option (List Nat) :=
  ((s.replace "–" "-").splitOn ",").foldr (init := some []) fun part acc => do
    let ns ← (part.splitOn "-").mapM String.toNat?
    return ns ++ (← acc)

/-! ## Main -/

def main (args : List String) : IO UInt32 := do
  let cfg ← match parseArgs {} args with
    | .ok c => pure c
    | .error e => IO.eprintln s!"error: {e}"; return 2
  let imports := if cfg.imports.isEmpty then #[lib] else cfg.imports
  let failures ← IO.mkRef (#[] : Array String)
  let fail (check msg : String) : IO Unit := do
    IO.println s!"FAIL {check}: {msg}"
    failures.modify (·.push check)
  initSearchPath (← findSysroot)
  let env ← importModules ((imports ++ labelModules).map fun m => { module := m }) {}
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
        for c in codeSpans body do
          if c.any Char.isWhitespace then continue
          if c.startsWith s!"{lib}." || c.startsWith "Lean4Lean." then
            if !env.contains c.toName then
              fail "divergences" s!"{e.id} cites `{c}`, which is not a declaration"
          else if c.startsWith "proof/" then
            let f := cfg.src / (c.drop "proof/".length).toString
            if !(← f.pathExists) then
              fail "divergences" s!"{e.id} cites `{c}`, which does not exist"
          else if c.startsWith "Lean4Lean/" then
            let (path, sfx) := match c.splitOn ":" with
              | [p] => (p, none)
              | p :: rest => (p, some (":".intercalate rest))
              | [] => (c, none)
            let f := cfg.lean4lean / path
            if !(← f.pathExists) then
              fail "divergences" s!"{e.id} cites `{c}`: {f} does not exist"
            else if let some sfx := sfx then
              let t ← IO.FS.readFile f
              let n := (t.splitOn "\n").length - (if t.endsWith "\n" then 1 else 0)
              match citedLines sfx with
              | none => fail "divergences" s!"{e.id} cites `{c}`: malformed line numbers"
              | some ls =>
                if ls.any (fun k => k == 0 || k > n) then
                  fail "divergences" s!"{e.id} cites `{c}`: {path} has {n} lines"

  -- The labels name `sorry` declarations of lean4lean.
  for (l, n) in sorryLabels ++ testOnlySorryLabels do
    if !(env.contains n) then fail "sorry" s!"label {l}: {n} is not a declaration"
    else if !(uses env n).contains ``sorryAx then
      fail "sorry" s!"label {l}: {n} does not mention sorryAx"

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
          if moduleOf? env a == some `Lean4Lean.Verify.Axioms then "a Verify/Axioms.lean axiom"
          else if a.components.contains `_native then "a native-code axiom"
          else "not allowed"
        fail "axioms" s!"{c} depends on {a} ({why})"
    if !isAux c then
      let lean := leanAxioms env c
      if lean.qsort Name.lt != (fp.axioms.toArray.qsort Name.lt) then
        fail "axioms" s!"{c}: computed footprint {own.toList} differs from #print axioms {lean.toList}"
    -- C5
    let tables := if isTest c then sorryLabels ++ testOnlySorryLabels else sorryLabels
    for s in fp.sorries do
      if (labelOf? tables s).isNone then
        fail "sorry" s!"{c} reaches sorryAx through {s}, which is not among {showList (tables.map (·.1))}"
    if !isAux c then
      let holders := fp.sorries.toArray.qsort Name.lt
      footLines := footLines.push
        s!"{c} {axiomsField fp} {showList (labelsOf tables fp)} {showList (holders.map toString)}"
  IO.FS.writeFile (cfg.out / "footprints.txt")
    ("# <declaration> <axioms> <sorry labels> <sorry declarations reached>\n" ++
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
  for r in roots do
    for r' in roots do
      if r != r' && env.contains r && env.contains r' then
        let (seen, _) := reach env members #[r']
        if seen.contains (leafKey env r) then
          fail "leaves" s!"root {r} is reachable from root {r'}; remove it from ROOTS.txt"

  -- C6 lean4lean's bridge is unreachable from non-test declarations.
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array (Name × Name) := #[]
  for c in ours do
    if !isTest c then stack := stack.push (c, c)
  while h : stack.size > 0 do
    let (c, origin) := stack[stack.size - 1]
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    if isForbiddenBridge c then
      fail "hygiene" s!"{origin} reaches {c}"
    let walk := match moduleOf? env c with
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
    let tables := if isTest d then sorryLabels ++ testOnlySorryLabels else sorryLabels
    let labels := labelsOf tables fp
    actual := actual.push s!"{d} {axiomsField fp} {showList labels}"
    let detail := labels.map fun l =>
      let n := ((sorryLabels ++ testOnlySorryLabels).find? (·.1 == l)).map (·.2)
      s!"{l} ({(n.map toString).getD "?"})"
    let unlabelled := (fp.sorries.toArray.filter fun h => (labelOf? tables h).isNone).map
      fun h => s!"unlabelled {h}"
    let detail := detail ++ unlabelled
    report := report.push
      s!"  {if isTest d then "test" else "root"} {d}: {if detail.isEmpty then "no sorry" else ", ".intercalate detail.toList}"
  IO.FS.writeFile (cfg.out / "axioms.actual")
    (expectedHeader ++ "\n".intercalate actual.toList ++ (if actual.isEmpty then "" else "\n"))
  let expText ← IO.FS.readFile cfg.expected
  let mut expected : Std.HashMap Name (String × String) := {}
  for l in lines expText do
    if isComment l then continue
    match fields l with
    | [d, a, s] =>
      if expected.contains d.toName then fail "expected" s!"{cfg.expected}: {d} is listed twice"
      expected := expected.insert d.toName (a, s)
    | _ => fail "expected" s!"{cfg.expected}: expected `<declaration> <axioms> <labels>`: {l}"
  for d in want do
    let fp := fpOf d
    let tables := if isTest d then sorryLabels ++ testOnlySorryLabels else sorryLabels
    let got := (axiomsField fp, showList (labelsOf tables fp))
    match expected[d]? with
    | none => fail "expected" s!"{d} has no line in {cfg.expected} (computed: {got.1} {got.2})"
    | some e =>
      if e != got then
        fail "expected" s!"{d}: {cfg.expected} says {e.1} {e.2}, computed {got.1} {got.2}"
  for (d, _) in expected.toList do
    if !want.contains d then
      fail "expected" s!"{cfg.expected} lists {d}, which is neither a root nor a test theorem"

  IO.println s!"report: {ours.size} declarations ({checked.size} checked, {tests.size} tests) in {ourMods.size} module(s); {roots.size} root(s)"
  for l in report do IO.println l
  let fs ← failures.get
  for check in ["axioms", "sorry", "hygiene", "leaves", "expected", "modules", "divergences"] do
    let n := (fs.filter (· == check)).size
    IO.println s!"{check}: {if n == 0 then "ok" else s!"{n} failure(s)"}"
  return if fs.isEmpty then 0 else 1

end EraseProofReport

def main (args : List String) : IO UInt32 := EraseProofReport.main args
