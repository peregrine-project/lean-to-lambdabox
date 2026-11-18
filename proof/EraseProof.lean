import EraseProof.Bridge.CLAccept
import EraseProof.Bridge.CLRead
import EraseProof.Statements
import EraseProof.Relation.Inst
import EraseProof.Source.Marks
import EraseProof.Source.Restrict
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
* `EraseProof.TargetLift`: closedness, lifting and closed substitution of λ□ terms.
* `EraseProof.Relation.Basic`, `EraseProof.Relation.Inst`: closedness, congruence, inversion,
  substitution and universe instantiation of the erasure relation.
* `EraseProof.Source.Marks`: marks under substitution; `unmark` commutes with lifting, universe
  instantiation and instantiation.
* `EraseProof.Source.Restrict`: source evaluation in the program restricts to a
  dependency-closed sub-environment.
* `EraseProof.Bridge.CLRead`: con-leche's reading of the source semantics' operations on terms.
* `EraseProof.Bridge.CLAccept`: what con-leche's acceptance of the program gives.
* `EraseProof.Statements`: the statements, as definitions of type `Prop`, that `spec.pin` pins.
-/
