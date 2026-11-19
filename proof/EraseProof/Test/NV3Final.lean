import EraseProof.FirstOrder
import EraseProof.Test.NV3Premises


/-!
# NV-3: the final theorem on its program

`final` applies `erase_correct` to the named premises of `Test/NV3Premises.lean`: `p0`, the program
the shipping code emits, is an untyped λ□ program whose main term evaluates to an erasure of the
source value, with the `Erases` relations and `Sound`. The facts that a compiled `#guard` checks
(DV-40) are hypotheses of the instance theorem.
-/

open Lean Erasure EraseProof EraseProof.Test EraseProof.Test.NV3

namespace EraseProof.Test.NV3

theorem final.{w} (hfold : ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified ConLeche.checkFuel) [] full = .ok envNV3) (hg : guardTerms.all (inferOk envNV3 ConLeche.checkFuel) = true) :
    ∃ lenv tb vb, p0 = .untyped lenv (some tb) ∧
      Erases (CLCert envNV3) (evalEnvOf view cfg D) [] e tb ∧
      ErasesDeps (CLCert envNV3) (evalEnvOf view cfg D) lenv tb ∧
      Erases noCert (evalEnvOf view cfg D) [] (lit 0) vb ∧
      LBEval defaultFlags lenv tb vb ∧ Sound.{w} envNV3 e (lit 0) :=
  erase_correct.{w} (hacc hfold) (hty hg) hclean hview hfrag hnopre hrun hmark (hcert hg) (hev hg)

/-- The value is first-order. -/
theorem fo : FirstOrderValue (evalEnvOf view cfg D) (lit 0) := by
  exact FirstOrderValue.lit

/-- The final theorem on first-order values: the main term evaluates to the structural erasure of
the source value. -/
theorem firstorder.{w} (hfold : ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified ConLeche.checkFuel) [] full = .ok envNV3) (hg : guardTerms.all (inferOk envNV3 ConLeche.checkFuel) = true) :
    ∃ lenv tb, p0 = .untyped lenv (some tb) ∧
      LBEval defaultFlags lenv tb (foErase (evalEnvOf view cfg D) (lit 0) []) ∧
      CLTyped envNV3 (lit 0) ∧ (∀ s, FrozenLeaf (lit 0) s → CLErasable envNV3 s) ∧
      Sound.{w} envNV3 e (lit 0) :=
  erase_correct_firstorder.{w} (hacc hfold) (hty hg) hclean (by krfl) hview hfrag hnopre hrun hmark
    (fun ci hci he v hv => let ⟨vM, h, _⟩ := (hcert hg).2.2 ci hci he v hv; ⟨vM, h⟩) (hev hg) fo

end EraseProof.Test.NV3
