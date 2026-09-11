import LeanToLambdaBox.Green

/-!
# Rung G2 — the `#erase` run

The frontend run behind `LeanToLambdaBox.Green.green_G2`: `spikeLit : Nat := Nat.succ 3`, erased under the
pinned configuration to `VerifyBench/ast/Spikes/G2.ast`.

Elaborating this module **writes** that file, so it is not a default build target; it is
built by `lake build VerifyBench` and re-run by `lake exe green-check G2`, which byte-diffs
the result against the committed `.ast`. The rung's theorem and the literal transcription of
the emitted program live in `LeanToLambdaBox/Green.lean`, which no `#erase` runs in, so
`lake build` writes nothing.

The `example`s below pin the committed data against the reified table and the certified
evaluator, in the kernel.
-/

open LeanToLambdaBox LeanToLambdaBox.Green

#erase spikeLit config { extern := .preferLogical, nat := .peano, csimp := false }
  to "VerifyBench/ast/Spikes/G2.ast"

/-- The tabled body of the subject is the literal under the constructor, whose `OfNat`
tower the emitted environment carries. -/
example : (g2Table.body? ``spikeLit).isSome = true := by rfl

/-- The table knows `Nat` at the two constructor indices the emitted inductive body
records. -/
example : (g2Table.ind? ``Nat).map (fun I => (I.numParams, I.ctors.map (·.numFields)))
    = some (0, [0, 1]) := by rfl

/-- The committed emitted program runs to the committed answer. -/
example : lbEval g2Env eraseFlags 16 g2Term = some g2Answer := by rfl
