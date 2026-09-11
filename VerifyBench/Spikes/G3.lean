import LeanToLambdaBox.Green

/-!
# Rung G3 — the `#erase` run

The frontend run behind `LeanToLambdaBox.Green.green_G3`: `spikeLet : Nat := let x := 2; Nat.succ x`, erased under the
pinned configuration to `VerifyBench/ast/Spikes/G3.ast`.

Elaborating this module **writes** that file, so it is not a default build target; it is
built by `lake build VerifyBench` and re-run by `lake exe green-check G3`, which byte-diffs
the result against the committed `.ast`. The rung's theorem and the literal transcription of
the emitted program live in `LeanToLambdaBox/Green.lean`, which no `#erase` runs in, so
`lake build` writes nothing.

The `example`s below pin the committed data against the reified table and the certified
evaluator, in the kernel.
-/

open LeanToLambdaBox LeanToLambdaBox.Green

#erase spikeLet config { extern := .preferLogical, nat := .peano, csimp := false }
  to "VerifyBench/ast/Spikes/G3.ast"

/-- The tabled body of the subject is the `let`, which the emitted constant body keeps as
a `tLetIn`. -/
example : (g3Table.body? ``spikeLet).isSome = true := by rfl

/-- The table knows `Nat` at the two constructor indices the emitted inductive body
records. -/
example : (g3Table.ind? ``Nat).map (fun I => (I.numParams, I.ctors.map (·.numFields)))
    = some (0, [0, 1]) := by rfl

/-- The committed emitted program runs to the committed answer. -/
example : lbEval g3Env eraseFlags 16 g3Term = some g3Answer := by rfl
