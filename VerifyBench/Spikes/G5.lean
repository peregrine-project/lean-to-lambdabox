import LeanToLambdaBox.Green

/-!
# Rung G5 — the `#erase` run

The frontend run behind `LeanToLambdaBox.Green.green_G5`: `spikeCase`, a `casesOn` applied
to a constructor value, erased under the pinned configuration to
`VerifyBench/ast/Spikes/G5.ast`.

Elaborating this module **writes** that file, so it is not a default build target; it is
built by `lake build VerifyBench` and re-run by `lake exe green-check G5`, which byte-diffs
the result against the committed `.ast`. The rung's theorem and the literal transcription of
the emitted program live in `LeanToLambdaBox/Green.lean`, which no `#erase` runs in, so
`lake build` writes nothing.

The `example`s below pin the committed data against the reified table and the certified
evaluator, in the kernel.
-/

open LeanToLambdaBox LeanToLambdaBox.Green

#erase spikeCase config { extern := .preferLogical, nat := .peano, csimp := false }
  to "VerifyBench/ast/Spikes/G5.ast"

/-- The table knows `Nat` at the two constructor indices the emitted inductive body
records. -/
example : (g5Table.ind? ``Nat).map (fun I => (I.numParams, I.ctors.map (·.numFields)))
    = some (0, [0, 1]) := by rfl

/-- The table knows `PUnit` at the one constructor index the thunk's argument needs. -/
example : (g5Table.ind? ``PUnit).map (fun I => (I.numParams, I.ctors.map (·.numFields)))
    = some (0, [0]) := by rfl

/-- The tabled body of the thunk's argument is the constructor constant the emitted
declaration is the erasure of. -/
example : g5Table.body? ``Unit.unit = some (.const ``PUnit.unit [.succ .zero]) := by rfl

/-- The committed emitted program runs to the committed answer. -/
example : lbEval g5Env eraseFlags 16 g5Term = some g5Answer := by rfl
