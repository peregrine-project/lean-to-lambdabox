import EraseProof.FirstOrder
import EraseProof.Test.NV1Premises


/-!
# NV-1: the final theorem on its program

`final` applies `erase_correct` to the named premises of `Test/NV1Premises.lean`: `p0`, the program
the shipping code emits, is an untyped λ□ program whose main term evaluates to an erasure of the
source value, with the `Erases` relations and `Sound`. The facts that a compiled `#guard` checks
(DV-40) are hypotheses of the instance theorem.
-/

open Lean Erasure EraseProof EraseProof.Test EraseProof.Test.NV1

namespace EraseProof.Test.NV1

theorem final.{w} (hfold : ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified ConLeche.checkFuel) [] nv1full = .ok envNV1) :
    ∃ lenv tb vb, p0 = .untyped lenv (some tb) ∧
      Erases (CLCert envNV1) (evalEnvOf view cfg D) [] e tb ∧
      ErasesDeps (CLCert envNV1) (evalEnvOf view cfg D) lenv tb ∧
      Erases noCert (evalEnvOf view cfg D) [] cT vb ∧
      LBEval defaultFlags lenv tb vb ∧ Sound.{w} envNV1 e cT :=
  erase_correct.{w} (hacc hfold) (hty) hclean hview hfrag hnopre hrun hmark (hcert) (hev)

/-- The value is first-order. -/
theorem fo : FirstOrderValue (evalEnvOf view cfg D) cT := by
  exact FirstOrderValue.ctor (c := `B.t) (cv := NV1.Bt_ctor) (us := []) (as := []) rfl rfl (fun _ h => nomatch h)

/-- The final theorem on first-order values: the main term evaluates to the structural erasure of
the source value. -/
theorem firstorder.{w} (hfold : ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified ConLeche.checkFuel) [] nv1full = .ok envNV1) :
    ∃ lenv tb, p0 = .untyped lenv (some tb) ∧
      LBEval defaultFlags lenv tb (foErase (evalEnvOf view cfg D) cT []) ∧
      CLTyped envNV1 cT ∧ (∀ s, FrozenLeaf cT s → CLErasable envNV1 s) ∧
      Sound.{w} envNV1 e cT :=
  erase_correct_firstorder.{w} (hacc hfold) (hty) hclean (by krfl) hview hfrag hnopre hrun hmark
    (fun ci hci v hv => let ⟨vM, h, _⟩ := (hcert).2.2 ci hci v hv; ⟨vM, h⟩) (hev) fo

end EraseProof.Test.NV1
