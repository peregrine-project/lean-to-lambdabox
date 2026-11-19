import EraseProof.FirstOrder
import EraseProof.Test.NV2Premises


/-!
# NV-2: the final theorem on its program

`final` applies `erase_correct` to the named premises of `Test/NV2Premises.lean`: `p0`, the program
the shipping code emits, is an untyped λ□ program whose main term evaluates to an erasure of the
source value, with the `Erases` relations and `Sound`. The facts that a compiled `#guard` checks
(DV-40) are hypotheses of the instance theorem.
-/

open Lean Erasure EraseProof EraseProof.Test EraseProof.Test.NV2

namespace EraseProof.Test.NV2

theorem final.{w} (hfold : ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified ConLeche.checkFuel) [] nv2full = .ok envNV2) :
    ∃ lenv tb vb, p0 = .untyped lenv (some tb) ∧
      Erases (CLCert envNV2) (evalEnvOf view cfg D) [] eM tb ∧
      ErasesDeps (CLCert envNV2) (evalEnvOf view cfg D) lenv tb ∧
      Erases noCert (evalEnvOf view cfg D) [] vM vb ∧
      LBEval defaultFlags lenv tb vb ∧ Sound.{w} envNV2 e vM :=
  erase_correct.{w} (hacc hfold) (hty) hclean hview hfrag hnopre hrun hmark (hcert) (hev)

/-- The value is first-order. -/
theorem fo : FirstOrderValue (evalEnvOf view cfg D) vM := by
  refine FirstOrderValue.ctor (c := `Box.mk) (cv := Boxmk_ctor) (us := []) (as := [markErase (markErase NV1.tB), NV1.cF]) (by krfl) rfl ?_
  intro a ha
  simp at ha
  rcases ha with rfl | rfl
  · exact FirstOrderValue.frozen
  · exact FirstOrderValue.ctor (c := `B.f) (cv := NV1.Bf_ctor) (us := []) (as := []) (by krfl) rfl (fun _ h => nomatch h)

/-- The final theorem on first-order values: the main term evaluates to the structural erasure of
the source value. -/
theorem firstorder.{w} (hfold : ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified ConLeche.checkFuel) [] nv2full = .ok envNV2) :
    ∃ lenv tb, p0 = .untyped lenv (some tb) ∧
      LBEval defaultFlags lenv tb (foErase (evalEnvOf view cfg D) vM []) ∧
      CLTyped envNV2 vM ∧ (∀ s, FrozenLeaf vM s → CLErasable envNV2 s) ∧
      Sound.{w} envNV2 e vM :=
  erase_correct_firstorder.{w} (hacc hfold) (hty) hclean (by krfl) hview hfrag hnopre hrun hmark
    (fun ci hci v hv => let ⟨vM, h, _⟩ := (hcert).2.2 ci hci v hv; ⟨vM, h⟩) (hev) fo

end EraseProof.Test.NV2
