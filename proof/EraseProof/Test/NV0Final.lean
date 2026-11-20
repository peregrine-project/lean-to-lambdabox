import EraseProof.FirstOrder
import EraseProof.Test.NV0Premises


/-!
# NV-0: the final theorem on its program

`final` applies `erase_correct` to the named premises of `Test/NV0Premises.lean`: `p0`, the program
the shipping code emits, is an untyped λ□ program whose main term evaluates to an erasure of the
source value, with the `Erases` relations and `Sound`. The facts that a compiled `#guard` checks
(DV-40) are hypotheses of the instance theorem.
-/

open Lean Erasure EraseProof EraseProof.Test EraseProof.Test.NV0

namespace EraseProof.Test.NV0

theorem final.{w}  :
    ∃ lenv tb vb, p0 = .untyped lenv (some tb) ∧
      Erases (CLCert envNV0) (evalEnvOf view cfg D) [] e tb ∧
      ErasesDeps (CLCert envNV0) (evalEnvOf view cfg D) lenv tb ∧
      Erases noCert (evalEnvOf view cfg D) [] idT vb ∧
      LBEval defaultFlags lenv tb vb ∧ Sound.{w} envNV0 e idT :=
  erase_correct.{w} (hacc) (hty) hclean hview hfrag hnopre hrun hmark (hcert) (hev)

end EraseProof.Test.NV0
