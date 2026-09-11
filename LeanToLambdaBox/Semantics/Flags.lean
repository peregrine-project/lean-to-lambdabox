import LeanToLambdaBox.Basic

/-!
# `WcbvFlags` — evaluation flags for λ□

Faithful translation of MetaRocq's `EWcbvEval.WcbvFlags`. The weak call-by-value
evaluation of λ□ is parameterised by three booleans:

* `with_prop_case` — enable the propositional-case reduction rules (`WcbvEval.iota_sing`,
  `WcbvEval.proj_prop`): a case or projection on an erased proof reduces by substituting
  `□`. Both rules additionally require the inductive to be marked propositional.
* `with_guarded_fix` — a `fix` unfolds only once its principal argument is a constructor
  value (the guarded recursion of Rocq and Lean). With the flag off, a `fix` unfolds on
  any value argument.
* `with_constructor_as_block` — whether constructors carry their arguments *inside* the
  node (`true`, block form) or accumulate them by application (`false`, applied form).

**Both constructor regimes are modelled.** `WcbvEval` carries the block rules
(`construct`, `iota_block`, `proj_block`) and the applied rules (`construct_atom`,
`construct_app`, `iota`, `proj`), each gated on this bit. The shipping erasure emits
applied form, so its evaluation point is `eraseFlags`; `blockFlags` and `propBlockFlags`
are the block-form points `LBOptimize_correct` relates.

**The prop-case bit is inert on emitted output.** The erasure never marks an
`OneInductiveBody` propositional — all 683 inductive entries of the benchmark suite's
emitted environments carry `propositional := false` — and both prop-gated rules require
that mark, so on every emitted environment `eraseFlags` and `entryFlags` agree.
`WcbvEval.propcase_weaken` (`Semantics/Metatheory.lean`) is the direction the consumer
needs: peregrine's `untyped_transform_pipeline` declares its input at `entryFlags`, while
the erasure correctness statement is made at the stronger point `eraseFlags`.
-/

namespace LeanToLambdaBox

/-- Evaluation flags — MetaRocq `EWcbvEval.WcbvFlags`. -/
structure WcbvFlags where
  with_prop_case            : Bool
  with_guarded_fix          : Bool
  with_constructor_as_block : Bool
  deriving Repr, DecidableEq

/-- The point the erasure correctness statement is made at: applied-form constructors,
    prop-case off, guarded fix. MetaRocq's `opt_wcbv_flags`. -/
def eraseFlags : WcbvFlags := ⟨false, true, false⟩

/-- The point peregrine's `untyped_transform_pipeline` declares for its input:
    applied-form constructors, prop-case on, guarded fix. MetaRocq's
    `default_wcbv_flags`. Reached from `eraseFlags` by `WcbvEval.propcase_weaken`. -/
def entryFlags : WcbvFlags := ⟨true, true, false⟩

/-- Block-form constructors, prop-case off, guarded fix: the conclusion point of
    `LBOptimize_correct`. -/
def blockFlags : WcbvFlags := ⟨false, true, true⟩

/-- Block-form constructors, prop-case on, guarded fix: the source point of
    `LBOptimize_correct`, which is what the pass removes the prop-cases from. -/
def propBlockFlags : WcbvFlags := ⟨true, true, true⟩

end LeanToLambdaBox
