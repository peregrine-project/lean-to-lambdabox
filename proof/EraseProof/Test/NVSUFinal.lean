import EraseProof.Test.NVSUEval
import EraseProof.Test.NVSURun

/-!
# NV-SU end to end

The remaining hypotheses of the final theorem on NV-SU (`Test/NVSUData.lean`): NV-S's model,
program and term (`henv`, `hwf`, `he`, `hty`, `Test/NVSModel.lean`) and view (`hview`,
`Test/NVSFinal.lean`), and the fragment test's acceptance of `e` (`hfrag`, the closure `D` of
`hcollect`, `Test/NVSUCollect.lean`). `final` applies the final theorem `erase_correct` to all nine
hypotheses, with `hpre` from `Test/NVSUModel.lean`, `hrun` from `Test/NVSURun.lean` and `hev` from
`Test/NVSUEval.lean`; the program `pSU` declares `add` as a λ□ fixpoint (`addFixL`). `firstorder`
applies `erase_correct_firstorder`: the main term of the program evaluates in λ□ to
`N.s (N.s N.z)`'s structural erasure.
-/

open Lean Erasure Metalean

namespace EraseProof.Test.NVSU

open EraseProof.Test.NVR (cZ mj iidN)
open EraseProof.Test.NVS (P e view D E B tE ssz ζ12)

/-- `henv`: the program is the Lean form of NV-S's model `E` with table `B`. -/
theorem henv : ProgEnv P ζ12 E B := NVS.henv

/-- `hwf`: `E` is well formed. -/
theorem hwf : EnvWF E := NVS.hwf

/-- `hview`: the view `#erase` reads agrees with the program. -/
theorem hview : ViewAgrees view P := NVS.hview

/-- `he`: the erased term is the Lean form of `tE`. -/
theorem he : TrM E B [] .nil [] e tE := NVS.he

/-- `hty`: `tE` is typed. -/
theorem hty : ∃ T, E[.nil] ⊢ tE : T := NVS.hty

/-- `hfrag`: the fragment test accepts `e`, with the closure `D`. -/
theorem hfrag : collectDeps view cfgSU e = .ok D := hcollect

/-- The final theorem on NV-SU: the program `#erase` emits for `add (N.s N.z) (N.s N.z)` under
`{nat := .peano}`, `add` defined by structural recursion and erased through its compiled
pre-definition, is an untyped λ□ program whose main term evaluates to an erasure of
`N.s (N.s N.z)`, and `N.s (N.s N.z)` translates to a term definitionally equal to the input's at
each of its types. -/
theorem final :
    ∃ lenv tb vb, pSU = .untyped lenv (some tb) ∧
      Erases E B [] (evalEnvOf view cfgSU P) .nil [] ssz vb ∧ LBEval defaultFlags lenv tb vb ∧
      ∀ T, E[.nil] ⊢ tE : T → ∃ t', TrM E B [] .nil [] ssz t' ∧ E[.nil] ⊢ tE ≡ t' : T :=
  erase_correct henv hwf hview hpre he hty hfrag hrun hev

/-- `N.s (N.s N.z)` is a first-order value at `σSU`: constructors of `N : Type` applied to
first-order values. -/
theorem fo_ssz : FirstOrderValue σSU ssz := by
  have hz : FirstOrderValue σSU cZ :=
    FirstOrderValue.ctor (c := `N.z) (us := []) (as := []) (n := 0) (u := .succ .zero) rfl rfl rfl
      rfl rfl (fun _ h => nomatch h)
  have hs : FirstOrderValue σSU mj :=
    FirstOrderValue.ctor (c := `N.s) (us := []) (as := [cZ]) (n := 0) (u := .succ .zero) rfl rfl
      rfl rfl rfl (fun a h => by simp at h; subst h; exact hz)
  exact FirstOrderValue.ctor (c := `N.s) (us := []) (as := [mj]) (n := 0) (u := .succ .zero) rfl
    rfl rfl rfl rfl (fun a h => by simp at h; subst h; exact hs)

/-- The final theorem on first-order values on NV-SU: the main term of the program `#erase` emits
evaluates in λ□ to `N.s (N.s N.z)`'s structural erasure, the constructor `1` of `N`'s block
applied to the constructor `1` applied to the constructor `0`. -/
theorem firstorder :
    ∃ lenv tb, pSU = .untyped lenv (some tb) ∧ LBEval defaultFlags lenv tb
      (.app (.construct iidN 1 []) (.app (.construct iidN 1 []) (.construct iidN 0 []))) :=
  erase_correct_firstorder henv hwf hview hpre he hty hfrag hrun hev fo_ssz

end EraseProof.Test.NVSU
