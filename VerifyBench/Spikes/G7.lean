import LeanToLambdaBox.Green

/-!
# Rung G7 — the `#erase` run

The frontend run behind `LeanToLambdaBox.Green.green_G7`: `arithClosed`, the tracked
benchmark program `benchArith` at `0`, erased under the pinned configuration to
`VerifyBench/ast/Spikes/G7.ast`.

Elaborating this module **writes** that file, so it is not a default build target; it is
built by `lake build VerifyBench` and re-run by `lake exe green-check G7`, which byte-diffs
the result against the committed `.ast`. The rung's theorem and the literal transcription of
the emitted program live in `LeanToLambdaBox/Green.lean`, which no `#erase` runs in, so
`lake build` writes nothing.

The module's own name is load-bearing: the matcher inliner writes it, with the macro scope
derived from it, into the ten emitted `let` binders that `Green.g7Tag` records.

The `example`s below pin the committed data against the reified table and the certified
evaluator, in the kernel.
-/

open LeanToLambdaBox LeanToLambdaBox.Green

#erase arithClosed config { extern := .preferLogical, nat := .peano, csimp := false }
  to "VerifyBench/ast/Spikes/G7.ast"

/-- The table knows `Nat` at the two constructor indices the emitted inductive body
records. -/
example : (g7Table.ind? ``Nat).map (fun I => (I.numParams, I.ctors.map (·.numFields)))
    = some (0, [0, 1]) := by rfl

/-- The subject is tabled with a body, which is what the emitted constant body is the
erasure of. -/
example : (g7Table.body? ``arithClosed).isSome = true := by rfl

/-- The four recursive `Nat` operations the emitted `.fix` blocks come from are all tabled
with bodies. -/
example : ((g7Table.body? ``Nat.pow).isSome, (g7Table.body? ``Nat.mul).isSome,
    (g7Table.body? ``Nat.add).isSome, (g7Table.body? ``Nat.sub).isSome)
    = (true, true, true, true) := by rfl

/-- The committed emitted program runs to the committed answer. -/
example : lbEval g7Env eraseFlags 64 g7Term = some g7Answer := by rfl
