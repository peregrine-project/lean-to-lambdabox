import LeanToLambdaBox.Green

/-!
# `green-check` — the external half of the green ladder

The lane that mechanises outside Lean what the kernel cannot: re-running the frontend on a
green rung and byte-diffing its committed `.ast`, checking that the literal program
`LeanToLambdaBox/Green.lean` states the rung's theorem about is the same bytes, and running
the certified evaluator on it. `--self-test` exercises `lbEval` on the fixtures of
`Semantics/Compute.lean`, so the executable and its evaluator are checked in CI from the
start.

Run from the repository root: the rung paths are relative to it.
-/

open LeanToLambdaBox LeanToLambdaBox.Green

/-- The self-test cases: name, the `lbEval` run, and the value expected of it.
    They cover δ, both constructor regimes, ι and `fix` unfolding — the same
    fixtures the kernel-checked `example`s in `Semantics/Compute.lean` use. -/
def selfTests : List (String × Option LBTerm × Option LBTerm) :=
  [ ("delta-applied", lbEval nvEnv eraseFlags 1000 (.const nvTwoAKn), some (nvPeanoA 2)),
    ("delta-block",   lbEval nvEnv blockFlags 1000 (.const nvTwoBKn),     some (nvPeanoB 2)),
    ("iota-applied",  lbEval nvEnv eraseFlags 1000 (nvPredA (nvPeanoA 3)), some (nvPeanoA 2)),
    ("iota-block",    lbEval nvEnv blockFlags 1000 (nvPredB (nvPeanoB 3)), some (nvPeanoB 2)),
    ("fix-applied",   lbEval nvEnv eraseFlags 1000 (.app (.fix [nvAddTwoA] 0) (nvPeanoA 2)),
      some (nvPeanoA 4)),
    ("fix-block",     lbEval nvEnv blockFlags 1000 (.app (.fix [nvAddTwoB] 0) (nvPeanoB 2)),
      some (nvPeanoB 4)) ]

/-- Run one self-test case, print its verdict, and report whether it passed.
    `LBTerm` has no `DecidableEq`, so the comparison goes through `Repr`. -/
def runCase (c : String × Option LBTerm × Option LBTerm) : IO Bool := do
  let ok := reprStr c.2.1 == reprStr c.2.2
  IO.println s!"{if ok then "PASS" else "FAIL"} {c.1}"
  if !ok then IO.println s!"  got:  {reprStr c.2.1}\n  want: {reprStr c.2.2}"
  return ok

/-- A rung of the ladder: the module whose elaboration re-runs the frontend, the committed
`.ast` that run writes, and the literal program `Green.lean` states the rung about. -/
structure Rung where
  /-- The rung's name, as the command line spells it. -/
  name : String
  /-- The module that re-runs `#erase` and rewrites the committed `.ast`. -/
  spike : System.FilePath
  /-- The committed emitted program, on disk. -/
  ast : System.FilePath
  /-- The committed emitted program, as a Lean literal. -/
  program : ASTType
  /-- The committed emitted term, and the answer `Green.lean` pins it to. -/
  term : LBTerm
  /-- The literal answer the rung's theorem ends in. -/
  answer : LBTerm

/-- The rungs reached so far. -/
def rungs : List Rung :=
  [ { name := "G1"
      spike := "VerifyBench/Spikes/G1.lean"
      ast := "VerifyBench/ast/Spikes/G1.ast"
      program := .untyped g1Env (some g1Term)
      term := g1Term
      answer := g1Answer },
    { name := "G2"
      spike := "VerifyBench/Spikes/G2.lean"
      ast := "VerifyBench/ast/Spikes/G2.ast"
      program := .untyped g2Env (some g2Term)
      term := g2Term
      answer := g2Answer },
    { name := "G3"
      spike := "VerifyBench/Spikes/G3.lean"
      ast := "VerifyBench/ast/Spikes/G3.ast"
      program := .untyped g3Env (some g3Term)
      term := g3Term
      answer := g3Answer },
    { name := "G4"
      spike := "VerifyBench/Spikes/G4.lean"
      ast := "VerifyBench/ast/Spikes/G4.ast"
      program := .untyped g4Env (some g4Term)
      term := g4Term
      answer := g4Answer },
    { name := "G5"
      spike := "VerifyBench/Spikes/G5.lean"
      ast := "VerifyBench/ast/Spikes/G5.ast"
      program := .untyped g5Env (some g5Term)
      term := g5Term
      answer := g5Answer },
    { name := "G6"
      spike := "VerifyBench/Spikes/G6.lean"
      ast := "VerifyBench/ast/Spikes/G6.ast"
      program := .untyped g6Env (some g6Term)
      term := g6Term
      answer := g6Answer } ]

/-- Print a verdict line and return it. -/
def report (ok : Bool) (what : String) : IO Bool := do
  IO.println s!"{if ok then "PASS" else "FAIL"} {what}"
  return ok

/-- Drop one trailing newline, so a committed `.ast` an editor has terminated still
compares equal to the printer's output. -/
def chomp (s : String) : String :=
  if s.endsWith "\n" then (s.take (s.length - 1)).toString else s

/-- The committed literal program, serialised by the shipping printer. -/
def Rung.printed (r : Rung) : String := Serialize.to_sexpr r.program |> sexpr.toString

/-- Re-elaborate the rung's spike module, which rewrites the committed `.ast`. `lean` is
run directly rather than through `lake`, so the `LEAN_PATH` this process was started with
is the one the child sees. -/
def rerun (r : Rung) : IO (Except String Unit) := do
  try
    let out ← IO.Process.output { cmd := "lean", args := #[r.spike.toString] }
    if out.exitCode == 0 then return .ok ()
    else return .error s!"lean exited with {out.exitCode}: {chomp out.stderr}"
  catch e => return .error s!"could not run lean: {e}"

/-- Check one rung: the `.ast` on disk is the literal program `Green.lean` states the rung
about, re-running the frontend writes those same bytes, and the certified evaluator takes
the committed term to the committed answer. The `.ast` is a build artifact, so an absent
one is a note rather than a failure: the re-run writes it and the diff is made against it.
-/
def checkRung (r : Rung) : IO Bool := do
  IO.println s!"rung {r.name}"
  let mut ok := true
  if ← r.ast.pathExists then
    let committed ← IO.FS.readFile r.ast
    ok ← report (chomp committed == chomp r.printed)
      s!"{r.name}: .ast on disk is the literal program of Green.lean"
  else
    IO.println s!"note {r.name}: no {r.ast} on disk; the re-run writes it"
  match ← rerun r with
  | .error msg =>
      ok ← report false s!"{r.name}: re-running {r.spike} ({msg})"
  | .ok () =>
      let regenerated ← IO.FS.readFile r.ast
      ok := (← report (chomp regenerated == chomp r.printed)
        s!"{r.name}: re-run .ast is the literal program of Green.lean") && ok
  let ev := lbEval (match r.program with | .untyped env _ => env) eraseFlags 1000 r.term
  ok := (← report (reprStr ev == reprStr (some r.answer))
    s!"{r.name}: lbEval takes the emitted term to the committed answer") && ok
  return ok

/-- What this tool does and how to call it. -/
def usage : String :=
  "green-check — external checks for the green ladder\n\n\
   usage:\n  \
     green-check --self-test    run lbEval on the built-in fixtures\n  \
     green-check RUNG...        check the named rungs (G1 … G6)\n  \
     green-check --all          check every rung reached so far\n\n\
   Run from the repository root. A rung check byte-diffs the committed .ast against the\n\
   literal program Green.lean states its theorem about, re-runs the frontend and diffs\n\
   again, and evaluates the emitted term with lbEval."

/-- Entry point of the `green-check` executable. -/
def main (args : List String) : IO UInt32 := do
  match args.filter (· != "--") with
  | ["--self-test"] =>
    let results ← selfTests.mapM runCase
    let failed := results.filter (· == false) |>.length
    IO.println s!"{results.length - failed}/{results.length} passed"
    return if failed == 0 then 0 else 1
  | [] | ["--help"] | ["-h"] => IO.println usage; return 0
  | names =>
    let selected := if names == ["--all"] then rungs else rungs.filter (names.contains ·.name)
    if selected.isEmpty then IO.eprintln usage; return 1
    let results ← selected.mapM checkRung
    let failed := results.filter (· == false) |>.length
    IO.println s!"{results.length - failed}/{results.length} rungs green"
    return if failed == 0 then 0 else 1
