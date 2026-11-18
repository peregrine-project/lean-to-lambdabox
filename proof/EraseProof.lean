import EraseProof.Bridge.CLAccept
import EraseProof.Bridge.CLRead
import EraseProof.Statements
import EraseProof.Source.Marks
import EraseProof.Test.Marks
import EraseProof.Test.NV1Run
/-!
# Verification of the eraser

The library root of the proof package: the correctness of the erasure behind `#erase`
(`LeanToLambdaBox`) against con-leche's set-theoretic model of Lean's kernel. The checks are in
`scripts/check.sh`.

* `EraseProof.Target`: λ□ and its evaluation.
* `EraseProof.Spec`: the definitions the statements are about (the bridge to con-leche, the
  con-leche checks, the marks, the source semantics, the erasure relation, `Sound`).
* `EraseProof.Source.Marks`: marks under substitution; `unmark` commutes with lifting, universe
  instantiation and instantiation.
* `EraseProof.Bridge.CLRead`: con-leche's reading of the source semantics' operations on terms.
* `EraseProof.Bridge.CLAccept`: what con-leche's acceptance of the program gives.
* `EraseProof.Statements`: the statements, as definitions of type `Prop`, that `spec.pin` pins.
-/
