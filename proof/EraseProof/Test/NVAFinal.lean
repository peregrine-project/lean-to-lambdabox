import EraseProof.FirstOrder
import EraseProof.Test.NVAModel
import EraseProof.Test.NVAEval

/-!
# NV-A end to end

The remaining hypotheses of the final theorem on NV-A (`Test/NVAData.lean`): the view agrees with
the program (`hview`), the fragment test accepts `e` (`hfrag`, the closure `D` of `hcollect`), and
`e` evaluates to `Nat.succ (Nat.succ (Nat.succ 2))` (`hev`, `Test/NVAEval.lean`). `final` applies the
final theorem `erase_correct` to all eight hypotheses (`henv`, `hwf`, `he`, `hty` from
`Test/NVAModel.lean`, `hrun` from `Test/NVARun.lean`). The corollary on first-order values
(`erase_correct_firstorder`) does not apply: the value keeps the literal `2` of the first argument
under its constructors, and a literal is not a first-order value (`FirstOrderValue` has
constructor, proof and atom leaves only); `final` states the value's erasure through `Erases`.
-/

open Lean Erasure Metalean

namespace EraseProof.Test.NVA

open EraseProof.Test.NVL (Nat_ind Zero_ctor Succ_ctor Nat_rec)
open EraseProof.Test.NVS (PUnit_ind PUnit_unit PUnit_rec PProd_ind PProd_mk PProd_rec)

theorem mem_P {ci : ConstantInfo} (h : ci ∈ P) :
    ci = .defnInfo inst_def ∨
      ci = .defnInfo ofNat_def ∨
      ci = .recInfo OfNat_rec ∨
      ci = .ctorInfo OfNat_mk ∨
      ci = .inductInfo OfNat_ind ∨
      ci = .defnInfo add_def ∨
      ci = .defnInfo add_f ∨
      ci = .defnInfo match_def ∨
      ci = .defnInfo Nat_brecOn ∨
      ci = .defnInfo Nat_brecOn_go ∨
      ci = .defnInfo Nat_below ∨
      ci = .defnInfo Nat_casesOn ∨
      ci = .recInfo Nat_rec ∨
      ci = .ctorInfo Zero_ctor ∨
      ci = .ctorInfo Succ_ctor ∨
      ci = .inductInfo Nat_ind ∨
      ci = .recInfo PProd_rec ∨
      ci = .ctorInfo PProd_mk ∨
      ci = .inductInfo PProd_ind ∨
      ci = .recInfo PUnit_rec ∨
      ci = .ctorInfo PUnit_unit ∨
      ci = .inductInfo PUnit_ind := by
  simpa [P] using h

/-- `hview`: the view `#erase` reads agrees with the program. -/
theorem hview : ViewAgrees view P := by
  intro ci h
  rcases mem_P h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- `hfrag`: the fragment test accepts `e`, with the closure `D`. -/
theorem hfrag : collectDeps view cfg e = .ok D := hcollect

/-- The final theorem on NV-A: the program `#erase` emits for `Nat.add 2 3` under
`extern := .preferLogical, structural := .kernel, nat := .peano` is an untyped λ□ program whose
main term evaluates to an erasure of `Nat.succ (Nat.succ (Nat.succ 2))`, and that value translates to
a term definitionally equal to the input's at each of its types. -/
theorem final :
    ∃ lenv tb vb, p0 = .untyped lenv (some tb) ∧
      Erases E B [] (evalEnvOf view cfg P) .nil [] v5 vb ∧ LBEval defaultFlags lenv tb vb ∧
      ∀ T, E[.nil] ⊢ tE : T → ∃ t', TrM E B [] .nil [] v5 t' ∧ E[.nil] ⊢ tE ≡ t' : T :=
  erase_correct henv hwf hview he hty hfrag hrun hev

end EraseProof.Test.NVA
