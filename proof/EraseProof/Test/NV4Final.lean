import EraseProof.FirstOrder
import EraseProof.Test.NV4Premises


/-!
# NV-4: the final theorem on its program

`final` applies `erase_correct` to the named premises of `Test/NV4Premises.lean`: `p0`, the program
the shipping code emits, is an untyped λ□ program whose main term evaluates to an erasure of the
source value, with the `Erases` relations and `Sound`. The facts that a compiled `#guard` checks
(DV-40) are hypotheses of the instance theorem.
-/

open Lean Erasure EraseProof EraseProof.Test EraseProof.Test.NV4

namespace EraseProof.Test.NV4

theorem final.{w} (hfold : ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified ConLeche.checkFuel) [] full = .ok envNV4) (hg : guards = true) :
    ∃ lenv tb vb, p0 = .untyped lenv (some tb) ∧
      Erases (CLCert envNV4) (evalEnvOf view cfg D) [] eM tb ∧
      ErasesDeps (CLCert envNV4) (evalEnvOf view cfg D) lenv tb ∧
      Erases noCert (evalEnvOf view cfg D) [] NV1.cT vb ∧
      LBEval defaultFlags lenv tb vb ∧ Sound.{w} envNV4 e NV1.cT :=
  erase_correct.{w} (hacc hfold) (hty hg) hclean hview hfrag hnopre hrun hmark (hcert hg) (hev hg)

/-- The value is first-order. -/
theorem fo : FirstOrderValue (evalEnvOf view cfg D) NV1.cT := by
  exact FirstOrderValue.ctor (c := `B.t) (cv := NV1.Bt_ctor) (us := []) (as := []) (by krfl) rfl (fun _ h => nomatch h)

/-- The final theorem on first-order values: the main term evaluates to the structural erasure of
the source value. -/
theorem firstorder.{w} (hfold : ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified ConLeche.checkFuel) [] full = .ok envNV4) (hg : guards = true) :
    ∃ lenv tb, p0 = .untyped lenv (some tb) ∧
      LBEval defaultFlags lenv tb (foErase (evalEnvOf view cfg D) NV1.cT []) ∧
      CLTyped envNV4 NV1.cT ∧ (∀ s, FrozenLeaf NV1.cT s → CLErasable envNV4 s) ∧
      Sound.{w} envNV4 e NV1.cT :=
  erase_correct_firstorder.{w} (hacc hfold) (hty hg) hclean (by krfl) hview hfrag hnopre hrun hmark
    (fun ci hci v hv => let ⟨vM, h, _⟩ := (hcert hg).2.2 ci hci v hv; ⟨vM, h⟩) (hev hg) fo

end EraseProof.Test.NV4
