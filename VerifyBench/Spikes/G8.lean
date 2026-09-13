import LeanToLambdaBox.Green

/-!
# Rung G8 — the `#erase` run

The frontend run behind `LeanToLambdaBox.Green.green_G8`: `benchArith`, the tracked
benchmark program itself, erased under the pinned configuration to
`VerifyBench/ast/Spikes/G8.ast`. The subject is function-typed, so the rung's observation is
made at a spine — the emitted term applied to the λ□ numeral `0`.

Elaborating this module **writes** that file, so it is not a default build target; it is
built by `lake build VerifyBench` and re-run by `lake exe green-check G8`, which byte-diffs
the result against the committed `.ast`. The rung's theorem and the literal transcription of
the emitted program live in `LeanToLambdaBox/Green.lean`, which no `#erase` runs in, so
`lake build` writes nothing.

The module's own name is load-bearing: the matcher inliner writes it, with the macro scope
derived from it, into the ten emitted `let` binders that `Green.g8Tag` records — which is
why G7's and G8's environments are transcribed at two different tags.

The `example`s below pin the committed data against the reified table and the certified
evaluator, in the kernel.
-/

open LeanToLambdaBox LeanToLambdaBox.Green

#erase benchArith config { extern := .preferLogical, nat := .peano, csimp := false }
  to "VerifyBench/ast/Spikes/G8.ast"

/-- The table knows `Nat` at the two constructor indices the emitted inductive body
records. -/
example : (g8Table.ind? ``Nat).map (fun I => (I.numParams, I.ctors.map (·.numFields)))
    = some (0, [0, 1]) := by rfl

/-- The subject is tabled with a body, and it is function-typed — the shape that makes this
the applied rung. -/
example : (g8Table.decl? ``benchArith).map (fun d => (d.body?.isSome, d.type.isForall))
    = some (true, true) := by rfl

/-- The committed emitted program, applied to the λ□ numeral `0`, runs to the committed
answer. -/
example : lbEval g8Env eraseFlags 64 (.app g8Term (peanoLB 0)) = some g8Answer := by rfl
