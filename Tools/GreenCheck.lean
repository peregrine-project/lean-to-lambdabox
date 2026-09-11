import LeanToLambdaBox.Semantics.Compute

/-!
# `green-check` — the external half of the green ladder

The lane that mechanises outside Lean what the kernel cannot: re-running the
frontend on a green rung, byte-diffing its committed `.ast` and reified table,
and cross-checking the target-side answer against `peregrine eval`. This first
cut carries only `--self-test`, which runs `lbEval` (`Semantics/Compute.lean`)
on the non-vacuity fixtures and reports one line per case, so the executable
and its evaluator are wired up and exercised in CI from the start.
-/

open LeanToLambdaBox

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

/-- What this tool does and how to call it. -/
def usage : String :=
  "green-check — external checks for the green ladder\n\n\
   usage:\n  \
     green-check --self-test    run lbEval on the built-in fixtures\n\n\
   The rung verbs (re-run #erase, byte-diff the .ast and the reified table,\n\
   differential-check lbEval against `peregrine eval`) are not implemented yet."

/-- Entry point of the `green-check` executable: `--self-test` runs the `lbEval`
    fixtures and exits `0` only if every case passes; anything else prints the
    usage text. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["--self-test"] =>
    let results ← selfTests.mapM runCase
    let failed := results.filter (· == false) |>.length
    IO.println s!"{results.length - failed}/{results.length} passed"
    return if failed == 0 then 0 else 1
  | [] | ["--help"] | ["-h"] => IO.println usage; return 0
  | _ => IO.eprintln usage; return 1
