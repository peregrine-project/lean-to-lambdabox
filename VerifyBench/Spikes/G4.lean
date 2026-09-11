import LeanToLambdaBox.Green

/-!
# Rung G4 — the `#erase` run

The frontend run behind `LeanToLambdaBox.Green.green_G4`: `spikeProj : Nat := (Prod.mk 1 2).1`, erased under the
pinned configuration to `VerifyBench/ast/Spikes/G4.ast`.

Elaborating this module **writes** that file, so it is not a default build target; it is
built by `lake build VerifyBench` and re-run by `lake exe green-check G4`, which byte-diffs
the result against the committed `.ast`. The rung's theorem and the literal transcription of
the emitted program live in `LeanToLambdaBox/Green.lean`, which no `#erase` runs in, so
`lake build` writes nothing.

The `example`s below pin the committed data against the reified table and the certified
evaluator, in the kernel.
-/

open LeanToLambdaBox LeanToLambdaBox.Green

#erase spikeProj config { extern := .preferLogical, nat := .peano, csimp := false }
  to "VerifyBench/ast/Spikes/G4.ast"

/-- The table knows `Prod` at the one constructor index the emitted inductive body
records. -/
example : (g4Table.ind? ``Prod).map (fun I => (I.numParams, I.ctors.map (·.numFields)))
    = some (2, [2]) := by rfl

/-- The table knows `Nat` at the two constructor indices the emitted inductive body
records. -/
example : (g4Table.ind? ``Nat).map (fun I => (I.numParams, I.ctors.map (·.numFields)))
    = some (0, [0, 1]) := by rfl

/-- The committed emitted program runs to the committed answer. -/
example : lbEval g4Env eraseFlags 16 g4Term = some g4Answer := by rfl
