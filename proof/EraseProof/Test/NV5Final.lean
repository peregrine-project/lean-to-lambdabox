import EraseProof.FirstOrder
import EraseProof.Test.NV5Premises


/-!
# NV-5: the final theorem on its program

`final` applies `erase_correct` to the named premises of `Test/NV5Premises.lean`: `p0`, the program
the shipping code emits, is an untyped λ□ program whose main term evaluates to an erasure of the
source value, with the `Erases` relations and `Sound`. The fold equation, which a compiled `#guard`
checks (DV-40), is a hypothesis of the instance theorem.
-/

open Lean Erasure EraseProof EraseProof.Test EraseProof.Test.NV5

namespace EraseProof.Test.NV5

theorem final.{w} (hfold : ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified ConLeche.checkFuel) [] full = .ok envNV5) :
    ∃ lenv tb vb, p0 = .untyped lenv (some tb) ∧
      Erases (CLCert envNV5) (evalEnvOf view cfg D) [] eM tb ∧
      ErasesDeps (CLCert envNV5) (evalEnvOf view cfg D) lenv tb ∧
      Erases noCert (evalEnvOf view cfg D) [] NV1.cT vb ∧
      LBEval defaultFlags lenv tb vb ∧ Sound.{w} envNV5 e NV1.cT :=
  erase_correct.{w} (hacc hfold) hty hclean hview hfrag hnopre hrun hmark hcert hev

/-- The value is first-order. -/
theorem fo : FirstOrderValue (evalEnvOf view cfg D) NV1.cT := by
  exact FirstOrderValue.ctor (c := `B.t) (cv := NV1.Bt_ctor) (us := []) (as := []) (by krfl) rfl (fun _ h => nomatch h)

/-- The final theorem on first-order values: the main term evaluates to the structural erasure of
the source value. -/
theorem firstorder.{w} (hfold : ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified ConLeche.checkFuel) [] full = .ok envNV5) :
    ∃ lenv tb, p0 = .untyped lenv (some tb) ∧
      LBEval defaultFlags lenv tb (foErase (evalEnvOf view cfg D) NV1.cT []) ∧
      CLTyped envNV5 NV1.cT ∧ (∀ s, FrozenLeaf NV1.cT s → CLErasable envNV5 s) ∧
      Sound.{w} envNV5 e NV1.cT :=
  erase_correct_firstorder.{w} (hacc hfold) hty hclean (by krfl) hview hfrag hnopre hrun hmark
    (fun ci hci he v hv => let ⟨vM, h, _⟩ := hcert.2.2 ci hci he v hv; ⟨vM, h⟩) hev fo

end EraseProof.Test.NV5
