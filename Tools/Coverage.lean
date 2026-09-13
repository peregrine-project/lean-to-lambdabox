import LeanToLambdaBox.Supported

/-!
# `coverage` — the measured half of `doc/coverage.md`

`lake exe coverage` writes `doc/coverage.md`; `--stdout` prints it and `--check` diffs the
generated text against the committed file and exits 1 on a difference. Run from the
repository root.

The document is prose with measurements in it, and this executable performs the
measurements rather than transcribing them: it reifies each benchmark program's
`SourceTable` out of the environment its module elaborates in, runs `supportedTerm` at the
entry constant and at every tabled body, reads the emitted `.ast` files, reads the eight
committed rung tables and the eight rung theorems out of `LeanToLambdaBox.Green`, and reads
the `hrun`/`htbl`/`hsafe` rows out of `doc/trust.md`, whose rows they are. The generated
document's own "How this file is measured" section is the list of what is live; every other
figure in it is carried prose.
-/

open Lean LeanToLambdaBox LeanToLambdaBox.Witness

namespace Coverage

/-! ## Text helpers -/

/-- A decimal with thousands separators, the form the document's byte counts use. -/
def comma (n : Nat) : String :=
  let ds := (toString n).toList.reverse
  let gs := ds.toChunks 3 |>.map (fun g => String.ofList g.reverse)
  String.intercalate "," gs.reverse

/-- How many times `pat` occurs in `hay`. -/
def countSub (hay pat : String) : Nat := (hay.splitOn pat).length - 1

/-- The parenthesised group ending at the head of a reversed character list, forward. -/
partial def groupBack : List Char → Nat → List Char → List Char
  | [], _, acc => acc
  | c :: cs, d, acc =>
    if c == ')' then groupBack cs (d + 1) (c :: acc)
    else if c == '(' then (if d ≤ 1 then '(' :: acc else groupBack cs (d - 1) (c :: acc))
    else groupBack cs d (c :: acc)

/-- The quoted components of a printed kername, joined as a dotted name. -/
def kernameOf (s : String) : String :=
  let parts := (s.splitOn "\"").zipIdx.filterMap
    (fun (p, i) => if i % 2 == 1 then some p else none)
  String.intercalate "." parts

/-- Every kername an emitted program declares without a body, in the order the file prints
them. The marker is the printed form of `ConstantDecl (constant_body None)`. -/
def bodylessNames (text : String) : List String :=
  let marker := "(ConstantDecl (constant_body None"
  match text.splitOn marker with
  | [] | [_] => []
  | pres => pres.dropLast.map fun pre =>
      kernameOf (String.ofList (groupBack (pre.toList.reverse.dropWhile (· == ' ')) 0 []))

/-! ## What is measured, per program and per rung -/

/-- A tracked benchmark program: the module holding its definitions, the constant its
`#erase` line names, the emitted file, and the two cells of the program table that state a
judgement rather than a measurement. -/
structure Prog where
  /-- The program's name, as both tables spell it. -/
  name : String
  /-- The library module holding its definitions. -/
  module : Name
  /-- The constant the program's `#erase` line erases. -/
  entry : Name
  /-- The emitted program on disk. -/
  ast : String
  /-- What the erase run does, beyond exiting 0. -/
  eraseRun : String
  /-- Why the program is outside the fragment, when it is. -/
  why : String
  /-- What the capstone says about it. -/
  capstone : String

/-- The five programs of the sibling `benchmarks` repository, as this repository duplicates
them with `csimp := false`. -/
def progs : List Prog :=
  [ { name := "Arith", module := `VerifyBench.Src.Arith, entry := `benchArith
      ast := "VerifyBench/ast/Arith.ast", eraseRun := "exit 0, no panic"
      why := "", capstone := "the applied capstone's subject, G7/G8" },
    { name := "Sieve", module := `VerifyBench.Src.Sieve, entry := `countPrimes
      ast := "VerifyBench/ast/Sieve.ast", eraseRun := "exit 0, no panic"
      why := "`recursorHead` at `Eq.rec`, through `Bool.noConfusion` (`F-EQREC`)"
      capstone := "not a rung; reached only by the general statement" },
    { name := "BinaryTrees", module := `VerifyBench.Src.BinaryTrees, entry := `binaryTreesSimple
      ast := "VerifyBench/ast/BinaryTrees.ast", eraseRun := "exit 0, no panic"
      why := "`F-EQREC`"
      capstone := "not a rung; its `Tree` is one of the first-order witnesses" },
    { name := "Quicksort", module := `VerifyBench.Src.Quicksort, entry := `quicksortBench
      ast := "VerifyBench/ast/Quicksort.ast", eraseRun := "exit 0, **one panic**"
      why := "`F-EQREC`, the well-founded `Nat.div.go`/`Nat.modCore.go` route, and \
              `sparseCasesOn`"
      capstone := "none: the emitted program is wrong (`F-SPARSE`, \
                   `doc/rework/03-DEV-FIX.md`)" },
    { name := "Fannkuch", module := `VerifyBench.Src.Fannkuch, entry := `runBenchmark
      ast := "VerifyBench/ast/Fannkuch.ast", eraseRun := "exit 0, no panic"
      why := "`F-EQREC` and `etaContractedMinor` at `Decidable.casesOn`"
      capstone := "**fails `NoBodylessRefs`** and is outside the capstone's domain: it \
                   reaches the body-less `Eq.rec` (`F-EQREC`)" } ]

/-- What one reified table measures: its size, the fix blocks the environment installs for
it, its `.proj` heads and their two informativeness verdicts, its metadata-headed spines,
and the `supportedTerm` verdict at every tabled body. -/
structure TableFacts where
  /-- Tabled constants. -/
  decls : Nat
  /-- Tabled inductive types. -/
  inds : Nat
  /-- Blocks `fixBlock?` installs, of which singletons, with untabled members and non-λ
  bodies. -/
  blocks : Nat × Nat × Nat × Nat
  /-- `.proj` nodes over the tabled bodies. -/
  projs : Nat
  /-- Each distinct `.proj` head with its `informativeB` and `succSortB` verdicts. -/
  heads : List (Name × Bool × Bool)
  /-- Application spines whose head is a metadata node. -/
  mdataHeads : Nat
  /-- Every tabled body outside the fragment, with the error the checker reports. -/
  errs : List (Name × SupportError)
  /-- Whether no two tabled names share a λ□ key. -/
  kernameSep : Bool

/-- Add one term's `.proj` nodes, `.proj` heads and metadata-headed spines to a running
count. -/
partial def scanTm : Expr → Nat × List Name × Nat → Nat × List Name × Nat
  | .app f a, (p, hs, m) =>
    let acc := if f.isMData then (p, hs, m + 1) else (p, hs, m)
    scanTm a (scanTm f acc)
  | .proj S _ e, (p, hs, m) =>
    scanTm e (p + 1, if hs.contains S then hs else hs ++ [S], m)
  | .lam _ t b _, acc | .forallE _ t b _, acc => scanTm b (scanTm t acc)
  | .letE _ t v b _, acc => scanTm b (scanTm v (scanTm t acc))
  | .mdata _ e, acc => scanTm e acc
  | _, acc => acc

/-- Measure one table against the environment it was reified out of. -/
def measureTable (env : Environment) (tbl : SourceTable) : TableFacts := Id.run do
  let mut blocks := 0; let mut singles := 0; let mut untabled := 0; let mut nonLam := 0
  let mut acc := (0, ([] : List Name), 0)
  let mut errs := #[]
  for (n, d) in tbl.decls do
    if let some nms := fixBlock? env n then
      blocks := blocks + 1
      if nms.length == 1 then singles := singles + 1
      for m in nms do
        match tbl.body? m with
        | none => untabled := untabled + 1
        | some b => unless b.isLambda do nonLam := nonLam + 1
    if let some b := d.body? then
      acc := scanTm b acc
      if let .error e := supportedTerm tbl b then errs := errs.push (n, e)
  let heads := acc.2.1.map fun S => match tbl.ind? S with
    | some I => (S, informativeB I, succSortB I)
    | none => (S, false, false)
  return { decls := tbl.decls.length, inds := tbl.inds.length
           blocks := (blocks, singles, untabled, nonLam)
           projs := acc.1, heads := heads, mdataHeads := acc.2.2
           errs := errs.toList, kernameSep := kernameSepB tbl }

/-- What one program measures: its table, its emitted file and the entry-term verdict. -/
structure ProgFacts where
  /-- The program this measures. -/
  prog : Prog
  /-- The emitted file's size in bytes. -/
  bytes : Nat
  /-- Emitted `tProj`, `tCase` and `tFix` nodes. -/
  nodes : Nat × Nat × Nat
  /-- Every kername the emitted program declares without a body. -/
  bodyless : List String
  /-- Whether `supportedTerm` accepts the entry constant. -/
  entryOk : Bool
  /-- Its reified table's measurements. -/
  tbl : TableFacts

/-- Read an emitted program, with the command that writes it if it is absent: the `.ast`
files are build artifacts, and `lake build VerifyBench` is what produces them. -/
def readAst (path : String) : IO String := do
  if ← System.FilePath.pathExists path then IO.FS.readFile path
  else throw (IO.userError s!"{path} is absent; run `lake build VerifyBench` first")

/-- Reify one program's table out of its own module's environment and measure it. The
modules cannot share an environment: two of the five declare the same name. -/
unsafe def measureProg (p : Prog) : IO ProgFacts := do
  enableInitializersExecution
  let env ← importModules #[{ module := p.module }] {} (trustLevel := 1024) (loadExts := true)
  let ctx : Core.Context := { fileName := "<coverage>", fileMap := default, maxHeartbeats := 0 }
  let (tbl, _) ← (Reify.table [p.entry]).toIO ctx { env }
  let text ← readAst p.ast
  return { prog := p, bytes := text.utf8ByteSize
           nodes := (countSub text "tProj", countSub text "tCase", countSub text "tFix")
           bodyless := bodylessNames text
           entryOk := (supportedTerm tbl (.const p.entry [])).toOption.isSome
           tbl := measureTable env tbl }

/-- What one rung measures: whether its theorem is in the environment, which hypotheses it
still binds, its committed table's measurements and its emitted file's size. -/
structure RungFacts where
  /-- The rung's name. -/
  name : String
  /-- Whether `LeanToLambdaBox.Green` declares the rung's theorem. -/
  present : Bool
  /-- The names the theorem binds. -/
  binders : List String
  /-- Its committed table's measurements. -/
  tbl : Option TableFacts
  /-- Its committed `.ast`'s size in bytes. -/
  bytes : Nat

/-- The hypotheses whose presence or absence at a rung the ladder section reports. -/
def audited : List String := ["hcb", "hev", "hbridge", "hve"]

/-- The binder names of a `∀`-telescope. -/
partial def binderNames : Expr → List String
  | .forallE n _ b _ => n.toString :: binderNames b
  | _ => []

/-- Measure the eight rungs against `LeanToLambdaBox.Green`'s environment, and the
constant and λ□-key counts of that environment. -/
unsafe def measureRungs : IO (List RungFacts × Nat × Nat) := do
  enableInitializersExecution
  let env ← importModules #[{ module := `LeanToLambdaBox.Green }] {}
    (trustLevel := 1024) (loadExts := true)
  let mut out := #[]
  for i in [1, 2, 3, 4, 5, 6, 7, 8] do
    let thm := Name.mkStr3 "LeanToLambdaBox" "Green" s!"green_G{i}"
    let tblName := Name.mkStr3 "LeanToLambdaBox" "Green" s!"g{i}Table"
    let tbl := (env.evalConstCheck SourceTable {} ``SourceTable tblName).toOption.map
      (measureTable env)
    let ast := s!"VerifyBench/ast/Spikes/G{i}.ast"
    let bytes := (← readAst ast).utf8ByteSize
    out := out.push { name := s!"G{i}", present := (env.find? thm).isSome
                      binders := (env.find? thm).map (binderNames ·.type) |>.getD []
                      tbl := tbl, bytes := bytes }
  let mut keys : Std.HashSet String := {}
  let mut n := 0
  for (c, _) in env.constants.toList do
    n := n + 1
    keys := keys.insert (reprStr (toKername c))
  return (out.toList, n, keys.size)

/-! ## The document -/

/-- The rows of `doc/trust.md` the document carries, read out of that file so that
"verbatim" is a fact rather than a claim. -/
def trustRows : IO (List String) := do
  let text ← IO.FS.readFile "doc/trust.md"
  let mut out := []
  for h in ["hrun", "htbl", "hsafe"] do
    match text.splitOn "\n" |>.find? (·.startsWith s!"| `{h}` |") with
    | some l => out := out ++ [l]
    | none => throw (IO.userError s!"doc/trust.md has no `{h}` row")
  return out

/-- One program's row of the program table. -/
def progRow (f : ProgFacts) : String :=
  let verdict :=
    if f.entryOk && f.tbl.errs.isEmpty then
      "**yes** — no `SupportError` at the entry term or at any tabled body"
    else s!"**no** — {f.prog.why}"
  s!"| {f.prog.name} | {comma f.bytes} | {f.prog.eraseRun} | {verdict} | {f.prog.capstone} |"

/-- One program's row of the fragment table: the table it was measured on, the entry
verdict, and every tabled body outside the fragment. -/
def fragmentRow (f : ProgFacts) : String :=
  let errs := f.tbl.errs.map fun (n, e) => s!"`{n}` ({errName e})"
  let what := if errs.isEmpty then "—" else String.intercalate ", " errs
  let nbr := match f.bodyless with
    | [] => "holds"
    | ns => s!"**fails**: {String.intercalate ", " (ns.map (s!"`{·}`"))}"
  s!"| {f.prog.name} | {f.tbl.decls} | {f.tbl.inds} | {if f.entryOk then "`ok`" else "**error**"} \
     | {f.tbl.errs.length} | {what} | {nbr} |"
where
  /-- The checker's own name for an error, with the constant it names. -/
  errName : SupportError → String
    | .recursorHead c => s!"recursorHead {c}"
    | .sparseCasesOn c => s!"sparseCasesOn {c}"
    | .etaContractedMinor c => s!"etaContractedMinor {c}"
    | .underAppliedCtor c => s!"underAppliedCtor {c}"
    | .underAppliedElim c => s!"underAppliedElim {c}"
    | .propElimIntoData I => s!"propElimIntoData {I}"
    | .projField S => s!"projField {S}"
    | .unknownConst c => s!"unknownConst {c}"
    | e => (reprStr e).replace "LeanToLambdaBox.SupportError." ""

/-- One program's row of the emitted-node table. -/
def nodeRow (f : ProgFacts) : String :=
  s!"| {f.prog.name} | {f.nodes.1} | {f.nodes.2.1} | {f.nodes.2.2} | {f.tbl.projs} | \
     {f.tbl.heads.length} | {f.tbl.heads.countP (!·.2.1)} | {f.tbl.heads.countP (!·.2.2)} |"

/-- One rung's row of the standing-hypothesis table. -/
def rungRow (r : RungFacts) : String :=
  let cells := audited.map fun h => if r.binders.contains h then "binder" else "—"
  s!"| {r.name} | {if r.present then "elaborates" else "**absent**"} | {comma r.bytes} | \
     {String.intercalate " | " cells} |"

/-- How many of a table's errors are of a given shape. -/
def countErrs (fs : List TableFacts) (p : SupportError → Bool) : Nat :=
  (fs.map (·.errs.countP (fun e => p e.2))).foldl (· + ·) 0

/-- The sum of a projection over a list of table measurements. -/
def sumOver (fs : List TableFacts) (g : TableFacts → Nat) : Nat := (fs.map g).foldl (· + ·) 0

end Coverage

namespace Coverage

/-- The document's opening, and the list of what the tool measures rather than carries. -/
def header : String :=
"# Coverage — what the theorems reach, and what they do not

Two tables: the five benchmark programs, and the eight rungs of the green ladder. Together
they are the answer to \"on what does this development actually say something?\", and the rule
is that an uncovered program is named with the reason it is uncovered.

`lake exe coverage` writes this file, `--stdout` prints it and `--check` diffs the two, so a
figure below drifts only if the tree does. The `hrun`, `htbl` and `hsafe` rows are read out of
`doc/trust.md`, whose rows they are.

## What is measured on each run

Every number in this file that a command can produce is produced by one: each emitted `.ast`'s
size and its `tProj`/`tCase`/`tFix` and body-less-declaration counts; each program's reified
`SourceTable`, with the `supportedTerm` verdict at its entry constant and at every tabled
body, the `SupportError` of each erroring body, the fix blocks `Witness.fixBlock?` installs,
the `.proj` heads with their `informativeB` and `succSortB` verdicts, the metadata-headed
spines and `kernameSepB`; the same measurements on the eight committed rung tables; each rung
theorem's presence and the hypotheses it still binds; and the constant and λ□-key counts of
the environment `LeanToLambdaBox/Green.lean` elaborates in.

Four things here are prose a reader maintains: the panic reproduction and the erase-run
column (`doc/rework/03-DEV-FIX.md` holds the commands), the wave a rung went green in, N20's
per-program minor counts, and the dead-declaration budget. Each is attributed where it
appears."

/-- The program table and the paragraphs that read it. -/
def programsSection (fs : List ProgFacts) (rungTbls : List TableFacts) : String :=
  let bl := String.intercalate " and " (fs.filter (!·.bodyless.isEmpty) |>.map (·.prog.name))
  let ok := String.intercalate " and " (fs.filter (fun f => f.entryOk && f.tbl.errs.isEmpty)
    |>.map (·.prog.name))
  let allTbls := fs.map (·.tbl) ++ rungTbls
  let blocks := sumOver allTbls (·.blocks.1)
  let singles := sumOver allTbls (·.blocks.2.1)
  let untabled := sumOver allTbls (·.blocks.2.2.1)
  let nonLam := sumOver allTbls (·.blocks.2.2.2)
  let mdata := sumOver allTbls (·.mdataHeads)
  let srcProjs := sumOver allTbls (·.projs)
  let sep := allTbls.countP (·.kernameSep)
  let under := countErrs allTbls fun e => match e with
    | .underAppliedCtor _ | .underAppliedElim _ => true
    | _ => false
  let projErrs := countErrs allTbls fun e => match e with | .projField _ => true | _ => false
s!"## The five programs

The definitions are the frozen copies `VerifyBench/Src/Arith.lean`, `VerifyBench/Src/Sieve.lean`,
`VerifyBench/Src/Quicksort.lean`, `VerifyBench/Src/BinaryTrees.lean` and
`VerifyBench/Src/Fannkuch.lean`, held against the sibling `benchmarks` repository's originals by
`scripts/frozen.sh`; the roots `VerifyBench/*.lean` add the `#erase` line, which sets
`csimp := false` — every correctness statement needs it, and the frozen originals do not set
it. Sizes are of the `.ast` those runs write.

| Program | `.ast` bytes | Erase run | In the fragment? | Capstone |
|---|---|---|---|---|
{String.intercalate "\n" (fs.map progRow)}

The verdict column is the checker's, not a judgement: it is what `supportedTerm` returns over a
`Witness.reify%` table built on the program's entry constant, at the entry term and at every
tabled body. Inside the fragment: **{ok}**. The fragment table below gives the erroring bodies
of the others, one row per program.

The panic is `PANIC at Erasure.visitCases LeanToLambdaBox.Erasure:817:55`, and the run still
exits 0 and still writes the file; both commands are in `doc/rework/03-DEV-FIX.md`. Emitted
programs carrying a body-less constant: **{bl}**, and no other.

`NoBodylessRefs Σ t` — no constant the emitted program reaches is declared without a body — is
the capstone's premise and is decidable. The closure `ReachableFrom` computes reaches every
declared kername of all five, so the body-less count of the emitted file decides it: four of
the five satisfy it, and the exception is **{bl}**, whose reachable `Eq.rec` is declared
body-less: a rung there would have an uninhabitable evaluation hypothesis and would be
vacuously green. The closure includes the
inductive block of every `tConstruct`, `tCase` and `tProj` node, which is what
`constructorArity` and `isPropositionalInductive` are answered from.

### The per-program restrictions

N19, N21 and the three fragment restrictions at the end of the list are conjuncts of
`Supported` and are decided by `supportedB` (`LeanToLambdaBox/Supported.lean`). **N20 is not a
conjunct** — it constrains `hev`, T9's evaluation hypothesis, not the eraser's output — so its
entry records a decidable *sufficient* condition, and says what the semantic obligation costs
when that condition fails. **N22 is not a conjunct either**: it is a condition on the *input*,
one clause of the class-**D** binder `TableBlocks`, read at the blocks the run installs a fixvar
map for. `NoBodylessRefs` is the capstone's own premise, decided on the emitted environment.

* **N19** — no under-applied constructor and no under-applied eliminator occurrence: a tabled
  constructor head is applied to at least `numParams + numFields`, a `casesOn` head to at least
  `dp + 1 + nm`. Reported as `SupportError.underAppliedCtor` / `.underAppliedElim`, and reported
  **{under} times** over the thirteen tables measured here — so the deletion of the two η arms
  costs the tracked programs nothing, the R15 contingency is not triggered, and F-ETA2's
  containment claim is measured rather than assumed. Its constructor half disappears entirely
  once F-ETA2 is repaired: applied-form λ□ evaluates a partially applied constructor spine natively
  (`Value.construct_app_val`, `LeanToLambdaBox/Semantics/Values.lean:105`).
* **N20** — every ι spine's dropped prefix, every unselected minor and every extra argument has
  a source value. Sufficient condition: each is already a syntactic value. It **fails on all
  five**, and the counts are the carried W3R measurement: non-value minors per total ι spine are
  3/3 at Arith, 25/26 at Sieve, 16/19 at BinaryTrees, 28/40 at Quicksort and 2/2 at Fannkuch,
  with 0 bad prefix arguments everywhere, so `hpres` stays cheap and `hmins` is discharged
  semantically — one `SEval` derivation per unselected branch per ι step. Lean's match compiler
  thunks a nullary branch into an *application*, not a λ: no nullary alternative of any emitted
  program has a `tLambda` head, and `Arith.ast`'s `Nat` zero-branch is
  `(tApp (tRel 1) (tConst Unit.unit))`. That is a cost, not a vacuity — Lean is total, so every
  well-typed closed term normalises and each unselected branch has a value, while partial and
  `unsafe` bodies are outside the fragment through N8.
* **N21** — a recursor head is outside the fragment: it is tabled body-less, so δ cannot fire at
  it; it is neither a constructor nor a type former, so no `SEval` value arm applies; and ι is
  keyed on `casesOn` names. A spine headed by one has no source evaluation at all, so a program
  reaching one would be **vacuously** covered. Reported as `SupportError.recursorHead`.
* **N22** — every definition of an emitted mutual fixpoint block is λ-headed. The emitted reading
  is `LBWfPeregrine.fixLambda` (`LeanToLambdaBox/Output.lean`), carried by the pass relation as
  `LowerBlock.hfl` (`doc/rules-Lower.md`). What supplies it is read on the **input** side, in two
  halves, as clauses of `TableBlocks` (`LeanToLambdaBox/Supported.lean`) at the blocks
  `Witness.fixBlock?` names: `lamHeaded`, the tabled body of every member is λ-headed, and
  `informative`, no member is erasable. The second is a conjunct and not a formality —
  `run_mkDef_box_not_lambda` registers an erasable member with a non-λ body — and it is
  model-side, so no computation reaches it. Measured over the thirteen tables — the eight
  committed rung tables and the five reified on the corpus entry constants: **{blocks} blocks**
  install a fixvar map, **{singles}** of them are singletons, and every member is tabled with a
  λ-headed body ({untabled} untabled members, {nonLam} non-λ bodies). A blanket clause would be
  false on every table: the non-λ tabled bodies are the non-recursive instance constants and the
  rung subjects themselves. `lake exe reify --blocks` is the CI mechanism.
* **`NoBodylessRefs`** — no constant the *emitted* program reaches is declared without a body.
  Measured on the emitted environment, not on the source closure.
* **N18, projection half** — the head of a `.proj` node is a tabled inductive type whose declared
  result sort never evaluates to `Prop`. Without it the emitted `.proj` is stuck on the target at
  every flag point, for the same reason the `casesOn` half covers, and `Erases.proj`'s `hinf` has
  no source. Reported as `SupportError.propElimIntoData` at a non-informative head and
  `.unknownConst` at an untabled one.
* **Metadata heads** — `SupportedTm.mdata` reads a metadata node at the empty spine only, so a
  metadata-wrapped application head is outside the fragment. The restriction is what makes
  `Supported.head` a theorem: `Lean.Expr.getAppFn` does not see through `.mdata`, so at a
  non-empty spine the head the checker approved and the head the run dispatches on are different
  terms. Reported as `SupportError.mdataSpine`. Measured over the thirteen tables: **{mdata}**
  application heads are metadata nodes — the restriction excludes nothing on the corpus.
* **Projection shape** — `SupportedTm.proj` carries the block's arity and the field bound: the
  structure's tabled block has exactly one constructor, of `nf` fields, and the field index is
  below `nf`. That is what retires the separate `ProjSupported` premise and what supplies step
  17's dropped-prefix `ProjInfo` through `Supported.projInfo`. Reported as
  `SupportError.projField`, and reported {projErrs} times on the {srcProjs} `.proj` nodes of the
  thirteen tables: every head has one reified constructor and every index is in range.
* **Kername separation** — no two tabled names share a λ□ key. `toKername` is not injective
  (`toKername_not_injective`), so two tabled constants can print as one kername and the second
  shadows the first in the emitted environment; the fragment excludes that input, and the block
  conjunct `BlockKeyed` spends the exclusion at the one name step 4 visits. Decided table-wide by
  `kernameSepB` and reported as `SupportError.kernameCollision`. Measured `true` on
  {sep} of the thirteen tables. The shipping half of the finding — that the eraser emits the
  collision rather than rejecting it — is `F-KERNAME` in `doc/rework/03-DEV-FIX.md`."

end Coverage

namespace Coverage

/-- The node counts, the fragment table, and the paragraphs that read them. -/
def fragmentSection (fs : List ProgFacts) (envCounts : Nat × Nat) : String :=
  let heads := ((fs.map (·.tbl.heads)).flatten.eraseDups).mergeSort
    (fun a b => a.1.toString ≤ b.1.toString)
  let nonInf := heads.countP (!·.2.1)
  let nonSucc := heads.countP (!·.2.2)
  let headList := String.intercalate ", " (heads.map (fun h => s!"`{h.1}`"))
s!"Over the whole elaboration environment of `LeanToLambdaBox/Green.lean` the same check is
{comma envCounts.1} constants against {comma envCounts.2} distinct keys, so no collision is
excluded by the fragment that the environment does not already avoid.

### The nodes each program emits, and the projection heads behind them

The first three columns are the emitted program's; the last four are read on the tabled bodies
the eraser walks, so the `.proj` counts differ — a source projection can be erased away, and a
head is counted once per table.

| Program | `tProj` | `tCase` | `tFix` | source `.proj` | distinct heads | non-informative | non-successor |
|---|---|---|---|---|---|---|---|
{String.intercalate "\n" (fs.map nodeRow)}

The {heads.length} distinct heads across the five programs are typeclass structures and `PProd`:

{headList}

The two verdict columns are what makes N18's projection half free on the corpus. The semantic
criterion `informativeB` — the declared result sort never evaluates to `Prop` — rejects
{nonInf} of them. The syntactic criterion rejects {nonSucc}: the heterogeneous
classes, whose declared result sort is a `max` of successors rather than a successor. Every
tracked program carries at least two such nodes, so the successor form would have emptied the
projection machinery on all five, which is the same false exclusion it makes at `Prod`.

### The fragment table

`Witness.Reify.visit` reads `compilerInfo?` — the `_unsafe_rec` companion first — and tables no
body for a `casesOn`-like head, so the reified table *is* built on compiler bodies and the
\"table closure\" and the \"eraser closure\" coincide. The measurement is `supportedTerm` on the
entry constant together with `supportedTerm` on **every** tabled body of `reify% <entry>` — a
superset of `Supported.Reaches`' closure, so a zero here is stronger than the fragment check:

| Program | tabled decls | inds | entry term | erroring bodies | what they are | `NoBodylessRefs` |
|---|---|---|---|---|---|---|
{String.intercalate "\n" (fs.map fragmentRow)}

N8's claim — that the compiler bodies the eraser reads carry direct structural recursion rather
than `brecOn` — holds of the tables as they now stand; the `brecOn` verdicts an earlier body
column produced survive only on Quicksort, through the well-founded `Nat.div.go` and
`Nat.modCore.go`. No program is excluded at `Prod`: `informativeB` tests the result sort for
never-zero rather than for a syntactic `Level.succ`, so `Prod`'s `Sort (max (u+1) (v+1))` is
accepted and `Prod.casesOn` is reported `propElimIntoData` nowhere.

Not exercised by any of the five, and recorded so that the gap is visible rather than inferred:
a genuinely **mutual** fixpoint block — every block the run installs a fixvar map for across the
thirteen tables is a singleton, so the fix layer's two-member case is covered only by a
hand-built fixture, and the block machinery is correct by construction over the compiler's SCC
but measured only at self-recursive singletons; `Acc`, `WellFounded` and `Quot` occur in none of
the five; and every emitted inductive is declared non-propositional, so no `Prop`-discriminee
elimination is covered at all (`F-PROP`, and the fragment excludes them through
`Supported.propElimIntoData`)."

end Coverage

namespace Coverage

/-- The ladder table, the measured standing hypotheses, and what a rung does and does not
settle. -/
def ladderSection (rs : List RungFacts) : String :=
  let carried := fun h => String.intercalate ", " (rs.filter (·.binders.contains h)
    |>.map (·.name))
  let free := fun h => String.intercalate ", " (rs.filter (!·.binders.contains h) |>.map (·.name))
  let cbFree := free "hcb"; let cbCarried := carried "hcb"; let evFree := free "hev"
s!"## The green ladder

Eight rungs under `VerifyBench/Spikes/`, each a real `#erase` run with a committed `.ast` and a
committed `SourceTable`. G1-G7 are closed nullary definitions, following the closed-normal-term
posture of Letouzey's Theorem 15; G8 is the tracked `benchArith` applied to its argument. Each
rung's conclusion ends in a **literal** peano numeral, so it cannot be satisfied by `□` or by a
stuck term.

| Rung | Program | What it adds | Green in |
|---|---|---|---|
| G1 | `spikeZero : Nat := Nat.zero` | constructor constants, inductive declarations, δ | **W1** |
| G2 | `spikeLit : Nat := Nat.succ 3` | the literal rule, the peano tower, the `OfNat` class tower | **W2** |
| G3 | `spikeLet : Nat := let x := 2; Nat.succ x` | ζ in both semantics | **W2** |
| G4 | `spikeProj : Nat := (Prod.mk 1 2).1` | the projection rule, boxed type parameters, polymorphic dependencies | **W2** |
| G5 | `spikeCase : Nat := Nat.casesOn 2 (thunk) (fun n => n)` | `casesOn`, `.case`, ι, and the first constructed `SEval` derivation | **W3** |
| G6 | `spikeFix : Nat := spikeRec 2` | a recursive constant: the compiler-body table, `.fix`, two guarded unfoldings | **W3** |
| G7 | `arithClosed : Nat := benchArith 0` | the typeclass tower: 10 projections, 4 fix blocks, 5 `.case`, a 19-node peano tower | **W5** |
| G8 | `benchArith : Nat → Nat` | a function-typed subject; the applied capstone | **W5** |

Each rung's theorem and the hypotheses it still binds, read off `LeanToLambdaBox.Green`:

| Rung | Theorem | `.ast` bytes | `hcb` | `hev` | `hbridge` | `hve` |
|---|---|---|---|---|---|---|
{String.intercalate "\n" (rs.map rungRow)}

`lenv` and `env` are universally quantified in every rung, so the ladder delivers
**conditional** non-vacuity. No computation can make it unconditional, and this sentence is
where that is said.

What every rung settles by computation is `hcfg`, `hsup` (through `supportedB`'s kernel
verdict), `hnb` and the target-side evaluation, which is what pins the answer to the literal
numeral; at G8 the evaluated term is the emitted term applied to its argument. `hwt` is settled
too, by a checked term rather than a computation: each subject is `#erase <constant>`, so
`Witness.trExprS_const_of_table` builds its `TrExprS` witness from `P`, `htbl` and `hsafe` —
including at G8, whose subject is function-typed, since that lemma reads only the table's level
parameters.

Two class-**C** hypotheses are binders at most rungs, and `doc/trust.md` carries the rows. `hcb`
is discharged at {cbFree} and binds at every other rung — {cbCarried}. Arith's table has ten
class projections among its tabled bodies, whose typing routes through lean4lean's unproven
`TrProj`, and twenty-eight of its declarations are polymorphic, which G1's monomorphic route
does not reach. `hev` — the source evaluation — is discharged at {evFree}, by `Green.g5_seval`:
δ at the subject, then ι at `Nat.casesOn`, with the discriminant a constructor value, the
selected branch applied to its field, and the *unselected* nullary branch evaluated through its
thunk and the δ step at `Unit.unit` the thunk's argument needs. That is N20's
per-branch obligation, paid.

**No `SEval` witness is constructed at Arith**, and that is a recorded fallback rather than an
oversight: `benchArith 0` runs 45 recursive calls through `Nat.pow`, `Nat.mul`, `Nat.add` and
`Nat.sub`, each a δ on a `.fix`-carrying constant and an ι on its compiled match, and N20 owes
an `SEval` derivation for every unselected minor of every one of them — against a 45-line,
three-`StepDefeq`-binder precedent at G5 for a single δ and ι. The obligation is volume, not
vacuity: Arith is total, so every unselected branch has a value. So `hev` binds at G7 and G8 as
it does at G1-G4 and G6, and T10, non-vacuity, stays demonstrated at G5. The value-side typings
`hvwt` and `hty` are binders at every rung: a rung's value is a constructor spine, not a
constant.

`hbridge` is a binder at every rung too, and it is the largest one, but it does not carry the
erasure itself: `erasure_bridge_of_run` proves `Erases env [] [] pe t₀ ∧ Lower Γspec t₀ t` from
the run, supplying all eighteen member steps, and `ErasureBridge` is the five remaining fields —
the environment, the simulation and the box-freedom of the lowered value. Those wait on the
registration invariant at the run's final state, which no theorem produces for an actual run,
and `doc/trust.md` names a supplier per field. One obligation of the bridge itself survives
beside them, `hve : VisitExprRunConcl`: the term walk's unconditional state, generator and
registry conclusion, which `step6` spends at the dependency bodies `Erasure.visitMutual` erases.
So what a rung says about the shipping erasure is conditional on that obligation and on the
environment half, and `doc/trust.md` carries both rows.

**What a matcher-bearing subject costs the ladder.** `ReifiedDecl.Prepared` — the run clause of
`SourceTableAdequate` — pins the compiler body **up to α**: `Expr.AlphaEq`, an inductive relation
blind to binder names and binder info and to nothing else. `Lean.Compiler.LCNF.inlineMatchers`
draws the `let` binder names it introduces from the name generator, so a declaration whose
preparation inlines a matcher has prepared bodies that agree across runs only up to those names —
which the clause allows. `lake exe reify --check` passes on all eight rung tables; at G7 and G8
it reports five bodies matching up to binder names — `Nat.add`, `Nat.mul`, `Nat.pow`, `Nat.pred`
and `Nat.sub`, the five whose preparation inlines a matcher — and no mismatch, while G1-G6 pass
with no note at all. The λ□ side of the same phenomenon is `LeanToLambdaBox/Alpha.lean`; the
emitted binder names are the frontend generator's choice and embed the spike module's own name,
so a rung's `.ast` is pinned to that module's name and import line, and `green-check` reports a
rename as a byte diff rather than absorbing it.

A measured note on what a source literal costs. Under `nat := .peano` a `Nat` literal is emitted
as a peano tower, but the source syntax `3` is `@OfNat.ofNat Nat 3 (instOfNatNat 3)`, so `OfNat`,
`OfNat.ofNat` and `instOfNatNat` come with it: G2's emitted environment has five declarations for
a one-line subject, and reaches all five. G4 adds `Prod` and `Prod.fst`, for seven. Every kername
those closures reach is declared with a body, so all four rungs satisfy `NoBodylessRefs` by
`decide +kernel`."

/-- The three rows a rung can neither discharge nor expect to, carried from `doc/trust.md`. -/
def bindersSection (rows : List String) : String :=
s!"## The permanent binders every rung keeps

Nine binders stand at every rung of the ladder: `P : ErasureSpec`, `htbl :
SourceTableAdequate`, `hsafe : TableSafe`, `E : EraserAsks`, `A : UpstreamAsks`, `hblk :
TableBlocks`, `hcb : CompilerBodies`, `hprep` and `hve : VisitExprRunConcl`. `hcb` is
discharged at G1, `hve` is the bridge's one residual obligation, and `doc/trust.md` carries a
row per binder and per field. The three below are the ones a rung can neither discharge nor
ever expect to; `lake exe coverage` reads them out of `doc/trust.md` rather than copying them.

| Binder | What it assumes | External mechanism |
|---|---|---|
{String.intercalate "\n" rows}"

/-- The dead-declaration budget, and the exception list it must stay outside of. -/
def tailSection : String :=
"## The dead-declaration budget

`lake exe hygiene --dead` reports **315** declarations outside the import closure of
`LeanToLambdaBox/Green.lean` and `LeanToLambdaBox/Capstone.lean`, and the workflow fails above
that budget: a module falling out of the closure is caught, while the standing residue is not
re-litigated at every push. The residue is four things and nothing else: the tooling (101 — 44 in
`Tools/Hygiene.lean`, 35 in `Tools/Coverage.lean`, 11 each in `Tools/Reify.lean` and
`Tools/GreenCheck.lean`), the frozen benchmark sources under `VerifyBench/Src/` (43), the
`ErasesCorrect/` arms with `ErasesUniform.lean` and `IotaBridge.lean` (72), which only the
aggregator reaches, and `LeanToLambdaBox/Alpha.lean`'s λ□ α-relation with its transports (99),
which no rung reads yet. The count is a measurement of the tree rather than of this file, and is
the one figure here a reader re-runs by hand.

This paragraph is deliberately outside the section below: `--dead` reads every backticked
`.lean` token in the exception section as an exemption, prose included.

## Exceptions to the no-dead-code rule

Every declaration must sit in the import closure of `LeanToLambdaBox/Green.lean` or
`LeanToLambdaBox/Capstone.lean`; `lake exe hygiene --dead` checks it against this list. A row
is admissible only if it names a **scheduled W6 unit as its consumer**, and its trigger is
that the file is deleted if that unit is not executed this cycle. An import into the closure
is not a consumer, and no module gets a standing exemption. An open proof obligation — a
hypothesis a theorem still binds — is not a dead declaration and does not belong here.

| File | Consumer | Trigger |
|---|---|---|
| `LeanToLambdaBox/Optimize.lean` | U6.2, the pass corollary over the non-block constructor regimes | deleted if U6.2 is not executed this cycle |"

/-- The whole document, measured against the tree. -/
unsafe def render : IO String := do
  let fs ← progs.mapM measureProg
  let (rs, consts, keys) ← measureRungs
  let rungTbls := rs.filterMap (·.tbl)
  let rows ← trustRows
  return String.intercalate "\n\n"
    [header, programsSection fs rungTbls, fragmentSection fs (consts, keys),
     ladderSection rs, bindersSection rows, tailSection] ++ "\n"

end Coverage

/-- What this tool does and how to call it. -/
def usage : String :=
  "coverage — regenerate doc/coverage.md from the tree\n\n\
   usage:\n  \
     coverage            write doc/coverage.md\n  \
     coverage --stdout   print the document\n  \
     coverage --check    exit 1 if the committed file differs from the generated one\n\n\
   Run from the repository root."

/-- Entry point of the `coverage` executable. -/
unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  match args with
  | [] => IO.FS.writeFile "doc/coverage.md" (← Coverage.render); return 0
  | ["--stdout"] => IO.print (← Coverage.render); return 0
  | ["--check"] =>
    let want ← Coverage.render
    let got ← IO.FS.readFile "doc/coverage.md"
    if want == got then IO.println "coverage: doc/coverage.md is current"; return 0
    else IO.eprintln "coverage: doc/coverage.md differs from the generated document"; return 1
  | _ => IO.eprintln usage; return 1
