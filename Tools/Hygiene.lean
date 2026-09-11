/-!
# `hygiene` — the mechanical half of the documentation and code-quality policy

`01-DESIGN.md` §9 and `02-PLAN.md` §0 state the policy; this executable runs it. With no
argument it spawns `scripts/hygiene.sh`, which owns the comment checks (slice tags, git
hashes, ISO dates, memory and handoff references, history narration, comment fraction) and
whose exit code becomes this tool's; `--wave N` scopes those to the files wave `N` owns. The
subcommands add what needs the module graph, the plan's tables or the declaration inventory:
`--dup` (N1), `--schedule` (N2), `--anti-epicycle FILE` (§4.4), `--tables`, `--dead` and
`--cites`. None needs a built environment; resolution of backticked *identifiers* is not
checked, as that needs the elaborated one.
-/

namespace Hygiene
/-- Directories walked for Lean sources; `topDirs` adds those a citation may name. -/
def scanRoots : List String := ["LeanToLambdaBox", "VerifyBench", "Tools", "test"]
/-- Files `02-PLAN.md` N3a hands to the wave gate, hence always allowed to import a module
    the wave deletes; `ownedByWave` adds those the plan's own rows name. -/
def standingFiles : List String :=
  ["LeanToLambdaBox.lean", "lakefile.toml", "lake-manifest.json", "test/ledger.expected"]
def topDirs : List String :=
  ["LeanToLambdaBox", "VerifyBench", "Tools", "test", "doc", "scripts", "rocq", "benchmarks"]
/-- The names a `lake exe` driver defines at the root namespace: `main`, which it must, and
    `usage`, which `Tools/GreenCheck.lean` and `Tools/Reify.lean` do. -/
def dupExempt : List String := ["main", "usage"]
/-- The five benchmark duplicates are separate library roots (`lakefile.toml`'s `VerifyBench`
    stanza) never imported together, copied from frozen sources: `Sieve` and `Quicksort` both
    declare `divmod`. N1 governs modules that can meet in one environment: scanned, unpaired. -/
def dupExemptFiles : List String :=
  ["VerifyBench/Arith.lean", "VerifyBench/Sieve.lean", "VerifyBench/Quicksort.lean",
   "VerifyBench/BinaryTrees.lean", "VerifyBench/Fannkuch.lean"]
/-- Tokens `01-DESIGN.md` §4.4 forbids in the pass layer: `Lower` is indexed by λ□ terms and
    the specification environment alone. `FVarId` is λ□'s own fvar syntax, so it is not here. -/
def epicycleTokens : List String := ["Expr", "VEnv", "Erasable", "ErasureState", "NameGenerator"]
def declKeywords : List String :=
  ["theorem", "lemma", "def", "abbrev", "structure", "inductive", "class", "instance", "opaque"]
def declModifiers : List String :=
  ["private", "protected", "noncomputable", "partial", "unsafe", "nonrec", "scoped", "local"]
-- String helpers; the core operations return slices at this toolchain.
def trimS (s : String) : String :=
  String.ofList ((s.toList.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse
def dropS (s : String) (n : Nat) : String := String.ofList (s.toList.drop n)
/-- Split off the first whitespace-delimited token. -/
def firstToken (s : String) : String × String :=
  let cs := s.toList.dropWhile Char.isWhitespace
  let tok := cs.takeWhile (fun c => !c.isWhitespace)
  (String.ofList tok, String.ofList (cs.drop tok.length))
/-- Identifier atoms: maximal runs of identifier characters, dotted names split. -/
def atoms (line : String) : List String :=
  (line.toList.map (fun c => if c.isAlphanum || c == '_' || c == '\'' then c else ' ')
    |> String.ofList).splitOn " " |>.flatMap (·.splitOn ".") |>.filter (!·.isEmpty)
/-- Every `.lean` file under `scanRoots`, plus the library root, sorted. -/
def leanFiles : IO (Array String) := do
  let mut out := #["LeanToLambdaBox.lean"]
  for r in scanRoots do
    if ← System.FilePath.isDir r then
      for p in ← System.FilePath.walkDir r do
        if p.toString.endsWith ".lean" then out := out.push p.toString
  return out.qsort (fun a b => decide (a < b))
/-- Strip one line of comments, carrying the block-comment depth in and out. String
    literals are kept: they are code. Mirrors `scripts/hygiene.sh`'s comment view. -/
partial def stripLine : List Char → Nat → Bool → List Char → List Char × Nat
  | [], d, _, acc => (acc.reverse, d)
  | c :: c' :: cs, d, inStr, acc =>
    if d > 0 then
      if c == '-' && c' == '/' then stripLine cs (d - 1) false acc
      else if c == '/' && c' == '-' then stripLine cs (d + 1) false acc
      else stripLine (c' :: cs) d false acc
    else if inStr then
      if c == '\\' then stripLine cs d true acc
      else stripLine (c' :: cs) d (c != '"') (c :: acc)
    else if c == '-' && c' == '-' then (acc.reverse, d)
    else if c == '/' && c' == '-' then stripLine cs (d + 1) false acc
    else stripLine (c' :: cs) d (c == '"') (c :: acc)
  | [c], d, inStr, acc =>
    if d > 0 || inStr then (acc.reverse, d) else (List.reverse (c :: acc), d)
/-- The comment-stripped code of a text, and of a file, one entry per line. -/
def stripText (text : String) : Array String := Id.run do
  let mut depth := 0; let mut out := #[]
  for l in text.splitOn "\n" do
    let (cs, d) := stripLine l.toList depth false []
    depth := d; out := out.push (String.ofList cs)
  return out
def codeLines (path : String) : IO (Array String) := do return stripText (← IO.FS.readFile path)
/-- Drop a leading `@[…]` attribute group, brackets balanced. -/
partial def dropAttr (s : String) : String :=
  let s := String.ofList (s.toList.dropWhile Char.isWhitespace)
  if s.startsWith "@[" then
    let rec go (cs : List Char) (d : Nat) : List Char :=
      match cs with
      | [] => []
      | '[' :: rest => go rest (d + 1)
      | ']' :: rest => if d ≤ 1 then rest else go rest (d - 1)
      | _ :: rest => go rest d
    dropAttr (String.ofList (go (dropS s 1).toList 0))
  else s
/-- The declared name on a comment-stripped line, without its namespaces; `none` if the line
    declares nothing. Attributes, modifiers, `.{u}`, `_root_.` and anonymity are handled. -/
def declOnLine (line : String) : Option String :=
  let rec peel (s : String) (fuel : Nat) : String :=
    match fuel with
    | 0 => s
    | fuel + 1 =>
      let s' := dropAttr s
      let (tok, rest) := firstToken s'
      if declModifiers.contains tok then peel rest fuel else s'
  let (kw, rest) := firstToken (peel line 8)
  if !declKeywords.contains kw then none else
  let (tok, rest') := firstToken rest
  let tok := if declKeywords.contains tok then (firstToken rest').1 else tok
  let name := ((String.ofList (tok.toList.takeWhile (!" (){}[]:,".toList.contains ·))).splitOn
    ".{").headD ""
  if name.isEmpty then none
  else if name.startsWith "_root_." then some (dropS name 7) else some name
/-- Every declaration head in one file as `(qualified name, line)`. -/
def fileDecls (path : String) : IO (Array (String × Nat)) := do
  let mut ns : List (Option String) := []; let mut out := #[]
  for (line, i) in (← codeLines path).zipIdx do
    let t := trimS line
    let (kw, rest) := firstToken t
    if kw == "namespace" then ns := some (firstToken rest).1 :: ns
    else if kw == "section" || kw == "mutual" then ns := none :: ns
    else if kw == "end" then ns := ns.tail
    else match declOnLine t with
      | none => pure ()
      | some n =>
        let p := String.intercalate "." (ns.filterMap id).reverse
        out := out.push (if t.startsWith "_root_." || p.isEmpty then n else p ++ "." ++ n, i + 1)
  return out
/-- Module name of a path: `Tools/Hygiene.lean` is `Tools.Hygiene`. -/
def moduleOf (path : String) : String :=
  (((String.ofList (path.toList.reverse.drop 5).reverse).splitOn "/")).foldl
    (fun a s => if a.isEmpty then s else a ++ "." ++ s) ""
/-- The import graph as `(file, imported modules)` pairs. -/
def importGraph : IO (Array (String × List String)) := do
  let mut out := #[]
  for f in ← leanFiles do
    out := out.push (f, (← codeLines f).toList.filterMap fun l =>
      let (kw, rest) := firstToken l
      if kw == "import" then some (firstToken rest).1 else none)
  return out
/-- Backticked tokens of a line. A possessive (`` `X.lean` ``'s something) is a citation of
    part of a file and still names the file, so it is not distinguished here. -/
def backticked (line : String) : List String :=
  let rec go : List String → Nat → List String
    | [], _ => []
    | p :: rest, i => if i % 2 == 1 then p :: go rest (i + 1) else go rest (i + 1)
  go (line.splitOn "`") 0
/-- Expand one `{a,b}` group: `E{,X}.lean` gives `E.lean` and `EX.lean`. -/
partial def expandBraces (s : String) : List String :=
  match s.splitOn "{" with
  | pre :: rest@(_ :: _) =>
    match (String.intercalate "{" rest).splitOn "}" with
    | mid :: tail@(_ :: _) =>
      let post := String.intercalate "}" tail
      (mid.splitOn ",").flatMap fun alt => expandBraces (pre ++ alt ++ post)
    | _ => [s]
  | _ => [s]
/-- The `.lean` paths in a table cell: braces expanded, a bare module name resolved under
    `LeanToLambdaBox/`. A cell naming a file possessively yields that file, so a row deleting
    part of a file is checked like any other. -/
def cellFiles (cell : String) : List String :=
  (backticked cell).flatMap fun t =>
    (expandBraces t).filter (·.endsWith ".lean") |>.map fun t =>
      if topDirs.contains ((t.splitOn "/").headD t) then t else "LeanToLambdaBox/" ++ t
/-- The cells of a markdown table row. -/ def rowCells (line : String) : List String :=
  let t := trimS line
  ((if t.startsWith "|" then dropS t 1 else t).splitOn "|").map trimS
/-- Wave number of a `W3`-shaped label. -/ def waveNum (s : String) : Option Nat :=
  if (trimS s).startsWith "W" then (dropS (trimS s) 1).toNat? else none
/-- One row of `02-PLAN.md` §4. `covered` records the row's own statement that the deleted
    files' importers are co-owned by the deleting unit. -/
structure DelRow where
  wave : Nat
  unit : String
  files : List String
  covered : Bool
  deriving Inhabited
/-- `02-PLAN.md` §4's deletion schedule. -/
def deletionRows (plan : Array String) : Array DelRow := Id.run do
  let mut inSec := false; let mut out := #[]
  for l in plan do
    if l.startsWith "## " then inSec := l.startsWith "## 4. Deletion schedule"
    else if inSec && (trimS l).startsWith "| W" then
      let cs := rowCells l
      match waveNum (cs.headD ""), cs[1]?, cs[2]? with
      | some w, some unit, some cell =>
        out := out.push ⟨w, (backticked unit).headD unit, cellFiles cell,
          (cell.splitOn "importers' import lines").length > 1⟩
      | _, _, _ => pure ()
  return out
/-- The files each wave's units own, from `02-PLAN.md` §2's per-wave tables, together with
    those handed to gate ownership in every wave: N3a's four, plus every file a row marks as
    passing to the gate. -/
def ownedByWave (plan : Array String) : Array (Nat × String) × List String := Id.run do
  let mut wave : Option Nat := none; let mut out := #[]; let mut standing := standingFiles
  for l in plan do
    if l.startsWith "### W" then wave := waveNum (firstToken (dropS l 4)).1
    else if (trimS l).startsWith "| **U" || (trimS l).startsWith "| **G" then
      match wave, (rowCells l)[1]? with
      | some w, some cell =>
        for f in cellFiles cell do out := out.push (w, f)
        if (cell.splitOn "N3a").length > 1 then standing := standing ++ cellFiles cell
      | _, _ => pure ()
  return (out, standing)
/-- Print a check's summary, and its finding count as an exit code. -/ def verdict (msg : String) (bad : Nat) : IO UInt32 := do IO.println msg; return (if bad == 0 then 0 else 1)
/-- N1, by a comment-stripped textual scan of declaration heads. The scan is the robust
    half: two modules defining one name are a finding even when nothing imports both — the
    case an elaborated environment cannot exhibit, since it holds each name once. -/
def checkDup : IO UInt32 := do
  let mut all := #[]
  for f in ← leanFiles do
    for (n, line) in ← fileDecls f do all := all.push (n, f, line)
  let ds := all.qsort (fun a b => decide (a.1 < b.1))
  let mut bad := 0; let mut i := 0
  while i < ds.size do
    let n := ds[i]!.1
    let mut j := i; let mut files : List String := []
    while j < ds.size && ds[j]!.1 == n do
      if !files.contains ds[j]!.2.1 then files := ds[j]!.2.1 :: files
      j := j + 1
    let paired := files.filter (!dupExemptFiles.contains ·)
    if paired.length > 1 && !dupExempt.contains n then
      bad := bad + 1
      IO.println s!"dup: {n} defined in {String.intercalate ", " paired.reverse}"
    i := j
  verdict s!"--dup: {ds.size} declarations, {bad} names in two or more files" bad
/-- N2. A file deleted in wave *n* may only be imported by a file deleted in wave ≤ *n*,
    owned by a unit of wave *n*, gate-owned (N3a), or covered by the deletion row's own
    co-ownership of its importers' import lines. -/
def checkSchedule : IO UInt32 := do
  let plan ← codeLines "doc/rework/02-PLAN.md"
  let rows := deletionRows plan
  let (owned, standing) := ownedByWave plan
  let graph ← importGraph
  let delWave : String → Option Nat := fun f =>
    rows.foldl (fun acc r => if r.files.contains f then some (min (acc.getD r.wave) r.wave)
      else acc) none
  let mut bad := 0; let mut nfiles := 0; let mut nedges := 0
  for r in rows do
    for f in r.files do
      nfiles := nfiles + 1
      for (p, imps) in graph do  -- one pass per deleted file; the graph is ~60 files
        if p != f && imps.contains (moduleOf f) then
          nedges := nedges + 1
          let ok := (delWave p).any (· ≤ r.wave) || standing.contains p || r.covered
            || owned.any (fun (w, g) => w == r.wave && g == p)
          if !ok then
            bad := bad + 1
            IO.println s!"schedule: {f} is deleted in W{r.wave} ({r.unit}) but {p} imports \
              it and is neither deleted by then nor owned in W{r.wave}"
  verdict s!"--schedule: {rows.size} deletion rows, {nfiles} deleted files, \
    {nedges} live imports of them, {bad} inversions" bad
/-- The pass layer names no source-side object, comments excluded. -/
def checkAntiEpicycle (file : String) : IO UInt32 := do
  let mut bad := 0
  for (l, i) in (← codeLines file).zipIdx do
    for a in atoms l do
      if epicycleTokens.contains a then
        bad := bad + 1
        IO.println s!"anti-epicycle: {file}:{i + 1}: {a}"
  verdict s!"--anti-epicycle {file}: {bad} forbidden tokens" bad
/-- The constructor names of one inductive in a file, guillemets removed. -/
def inductiveArms (path : String) (ind : String) : IO (List String) := do
  let mut cur : Option String := none; let mut out := #[]
  for l in ← codeLines path do
    let t := trimS l
    let (kw, rest) := firstToken t
    if kw == "inductive" then cur := some (firstToken rest).1
    else if t.startsWith "|" then
      if cur == some ind then
        out := out.push ((firstToken (dropS t 1)).1.replace "«" "" |>.replace "»" "")
    else if !l.startsWith " " && !t.isEmpty then cur := none
  return out.toList
/-- Every arm of `Erases` and `Lower` is named in its rule table; an absent relation is
    reported and skipped, since the tables are written before the relations land. -/
def checkTables : IO UInt32 := do
  let mut bad := 0; let mut checked := 0
  for (src, ind, doc) in [("LeanToLambdaBox/Erases.lean", "Erases", "doc/rules-Erases.md"),
                          ("LeanToLambdaBox/Lower.lean", "Lower", "doc/rules-Lower.md")] do
    if !(← System.FilePath.pathExists src) then
      IO.println s!"tables: {src} absent, its table's coverage is not checked"
    else if !(← System.FilePath.pathExists doc) then
      IO.println s!"tables: {doc} does not exist"; bad := bad + 1
    else
      let names := atoms (← IO.FS.readFile doc)
      for a in ← inductiveArms src ind do
        checked := checked + 1
        if !names.contains a then
          bad := bad + 1; IO.println s!"tables: {doc} does not name {ind}.{a}"
  verdict s!"--tables: {checked} arms checked, {bad} unnamed" bad
/-- The files `doc/coverage.md`'s exception section allows outside the closure. -/
def coverageExceptions : IO (List String) := do
  let mut inSec := false; let mut out := []
  if !(← System.FilePath.pathExists "doc/coverage.md") then return out
  for l in (← IO.FS.readFile "doc/coverage.md").splitOn "\n" do
    if l.startsWith "#" then inSec := (l.splitOn "xception").length > 1
    else if inSec then out := out ++ cellFiles l
  return out
/-- The transitive import closure of a set of files, as paths. -/ partial def closure (graph : Array (String × List String)) (seen : List String)
    : List String → List String
  | [] => seen
  | f :: rest =>
    if seen.contains f then closure graph seen rest
    else
      let imps := (graph.find? (·.1 == f)).map (·.2) |>.getD []
      closure graph (f :: seen) ((graph.toList.filterMap fun (p, _) =>
        if imps.contains (moduleOf p) then some p else none) ++ rest)
/-- Policy 6: every declaration is in `Green.lean` ∪ `Capstone.lean`'s closure or excepted. -/
def checkDead : IO UInt32 := do
  let mut present := []
  for r in ["LeanToLambdaBox/Green.lean", "LeanToLambdaBox/Capstone.lean"] do
    if ← System.FilePath.pathExists r then present := r :: present
  if present.isEmpty then  -- the ladder and the capstone land in W1 and W4
    IO.println "--dead: Green.lean and Capstone.lean absent, closure not checked"
    return 0
  let live := closure (← importGraph) [] present
  let exc ← coverageExceptions
  let mut bad := 0
  for f in ← leanFiles do
    if !live.contains f && !exc.contains f && !standingFiles.contains f then
      for (n, line) in ← fileDecls f do
        bad := bad + 1
        IO.println s!"dead: {f}:{line}: {n}"
  verdict s!"--dead: {bad} declarations outside the closure" bad
/-- Whether a cited path exists, allowing one `*` in the final segment. -/
def citeExists (p : String) : IO Bool := do
  if (p.splitOn "*").length == 1 then System.FilePath.pathExists p
  else
    let dir := String.intercalate "/" ((p.splitOn "/").dropLast)
    let base := ((p.splitOn "/").getLastD "").splitOn "*"
    if !(← System.FilePath.isDir dir) then return false
    return (← System.FilePath.readDir dir).any fun e =>
      e.fileName.startsWith (base.headD "") && e.fileName.endsWith (base.getLastD "")
/-- Policy 4's "every cited document exists", over backticked paths, a `:line` suffix
    stripped. `all` widens it to every cited path, which also reports the design's forward
    references to files a later wave creates. -/
def checkCites (files : List String) (all : Bool) : IO UInt32 := do
  let mut files := files
  if files.isEmpty then
    files := (← leanFiles).toList
    for p in ← System.FilePath.walkDir "doc" do
      if p.toString.endsWith ".md" then files := p.toString :: files
  let mut bad := 0; let mut n := 0
  for f in files do
    for (l, i) in ((← IO.FS.readFile f).splitOn "\n").zipIdx do
      for t in backticked l do
        for t in expandBraces t do
          let t := (t.splitOn ":").headD t
          if (t.splitOn "/").length > 1 && topDirs.contains ((t.splitOn "/").headD "")
              && (all || t.endsWith ".md") then
            n := n + 1
            if !(← citeExists t) then
              bad := bad + 1
              IO.println s!"cite: {f}:{i + 1}: {t} does not exist"
  verdict s!"--cites{if all then " --all" else ""}: {n} cited paths in \
    {files.length} files, {bad} missing" bad
/-- Run `scripts/hygiene.sh`, the comment-hygiene half, and return its exit code. -/
def runShell (args : List String) : IO UInt32 := do
  let child ← IO.Process.spawn { cmd := "scripts/hygiene.sh", args := args.toArray }
  child.wait
/-- Comment hygiene scoped to one wave: every scanned file that wave does not own goes on
    `scripts/hygiene.sh`'s allow list, so findings there are printed without failing the run.
    Shipping code is owned by no wave and N5 forbids editing it, so before W5 this is the
    only form that can pass. -/
def checkWave (n : Nat) : IO UInt32 := do
  let owned := (ownedByWave (← codeLines "doc/rework/02-PLAN.md")).1.filterMap
    fun (w, f) => if w == n then some f else none
  let (h, tmp) ← IO.FS.createTempFile
  for f in ← leanFiles do if !owned.contains f then h.putStrLn f
  h.flush
  let rc ← runShell ["--allow", tmp.toString]
  IO.FS.removeFile tmp
  return rc

def usage : String :=
  "hygiene — the mechanical checks of the documentation and code-quality policy\n\
   usage: hygiene [--allow FILE] | --wave N | --dup | --schedule | --anti-epicycle FILE\n  \
          | --tables | --dead | --cites [--all] [FILE…]\n\
   Run from the repository root; no argument runs scripts/hygiene.sh. Exit 1 on a finding."

end Hygiene

/-- Entry point of the `hygiene` executable: one check per invocation, exit `0` on a clean
    run and `1` on a finding. -/
def main (args : List String) : IO UInt32 := do
  match args.filter (· != "--") with
  | [] => Hygiene.runShell []
  | ["--allow", f] => Hygiene.runShell ["--allow", f]
  | ["--wave", n] => Hygiene.checkWave (n.toNat?.getD 0)
  | ["--dup"] => Hygiene.checkDup
  | ["--schedule"] => Hygiene.checkSchedule
  | ["--anti-epicycle", f] => Hygiene.checkAntiEpicycle f
  | ["--tables"] => Hygiene.checkTables
  | ["--dead"] => Hygiene.checkDead
  | "--cites" :: fs => Hygiene.checkCites (fs.filter (· != "--all")) (fs.contains "--all")
  | ["--help"] | ["-h"] => IO.println Hygiene.usage; return 0
  | _ => IO.eprintln Hygiene.usage; return 1
