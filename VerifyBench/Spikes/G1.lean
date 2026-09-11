import LeanToLambdaBox.Green

/-!
# Rung G1 — the `#erase` run

The frontend run behind `LeanToLambdaBox.Green.green_G1`: `spikeZero : Nat := Nat.zero`,
erased under the pinned configuration to `VerifyBench/ast/Spikes/G1.ast`.

Elaborating this module **writes** that file, so it is not a default build target; it is
built by `lake build VerifyBench` and re-run by `lake exe green-check G1`, which byte-diffs
the result against the committed `.ast`. The rung's theorem and the literal transcription of
the emitted program live in `LeanToLambdaBox/Green.lean`, which no `#erase` runs in, so
`lake build` writes nothing.

The `example`s below pin the committed data against the reified table and the certified
evaluator, in the kernel.
-/

open LeanToLambdaBox LeanToLambdaBox.Green

#erase spikeZero config { extern := .preferLogical, nat := .peano, csimp := false }
  to "VerifyBench/ast/Spikes/G1.ast"

/-- The tabled body of the subject is the constructor constant, which is what the emitted
constant body `.construct natIid 0 []` is the erasure of. -/
example : g1Table.body? ``spikeZero = some (.const ``Nat.zero []) := by rfl

/-- The table knows `Nat` at the two constructor indices the emitted inductive body
records. -/
example : (g1Table.ind? ``Nat).map (fun I => (I.numParams, I.ctors.map (·.numFields)))
    = some (0, [0, 1]) := by rfl

/-- The committed emitted program runs to the committed answer. -/
example : lbEval g1Env eraseFlags 8 g1Term = some g1Answer := by rfl
