import EraseProof.Final
import EraseProof.Test.NVKModel
import EraseProof.Test.NVPRun

/-!
# NV-P and NV-K end to end

The remaining hypotheses of the final theorem on NV-P and NV-K (`Test/NVPData.lean`): the views
agree with the programs (`hview`), the fragment test accepts the terms (`hfrag`, from
`Test/NVPRun.lean`), and both terms evaluate to `fun y => y` (`hev`). On NV-P the major
`@Eq.refl B B.t` evaluates to itself and ι continues with the alternative (`SrcEval.casesIota`); on
NV-K the major is the theorem `hEq`, an atom whose statement is the type of `@Eq.refl B B.t`, and the
`casesOn` continues with the alternative (`SrcEval.casesProof`). `final` applies the final theorem
`erase_correct` to all eight hypotheses (`henv`, `hwf`, `he`, `hty` from `Test/NVPModel.lean` and
`Test/NVKModel.lean`, `hrun` from `Test/NVPRun.lean`): the program `pP` that `#erase` emits is an
untyped λ□ program whose main term evaluates to an erasure of `fun y => y`.
-/

open Lean Erasure Metalean

namespace EraseProof.Test.NVP

open EraseProof.Test.NV1 (tB cT B_ind Bf_ctor Bt_ctor B_rec)

theorem mem_P {ci : ConstantInfo} (h : ci ∈ P) :
    ci = .defnInfo Eq_casesOn ∨ ci = .recInfo Eq_rec ∨ ci = .ctorInfo Eq_refl ∨
      ci = .inductInfo Eq_ind ∨ ci = .recInfo B_rec ∨ ci = .ctorInfo Bf_ctor ∨
      ci = .ctorInfo Bt_ctor ∨ ci = .inductInfo B_ind := by
  simpa [P] using h

/-- `hview`: the view `#erase` reads agrees with the program. -/
theorem hview : ViewAgrees view P := by
  intro ci h
  rcases mem_P h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- `hfrag`: the fragment test accepts `e`. -/
theorem hfrag : collectDeps view cfg e = .ok (NVPK.DD false) := NVPK.hcollectP

/-- `hrun`: the entry point returns `pP`. -/
theorem hrun : eraseEntry view cfg e = pure (NVPK.pP, []) := NVPK.hrunP

theorem casesOn_Eq : (evalEnvOf view cfg P).casesOn? `Eq.casesOn = some Eq_ind := by rfl

/-- `@Eq.refl.{1} B B.t`. -/
def reflE : Expr := mkAppN (.const `Eq.refl [l1]) #[tB, cT]

theorem ev_refl : SrcEval (evalEnvOf view cfg P) reflE reflE := by
  have hT : SrcEval (evalEnvOf view cfg P) (mkAppN cT ([] : List Expr).toArray)
      (mkAppN cT ([] : List Expr).toArray) :=
    SrcEval.ctor (as := []) (vs := []) rfl rfl rfl (fun _ _ _ h => nomatch h)
  refine SrcEval.ctor (as := [tB, cT]) (vs := [tB, cT]) rfl rfl rfl ?_
  intro i a v h1 h2
  rcases i with _ | _ | i <;> simp at h1 h2 <;> subst h1 h2
  · exact SrcEval.constAtom (us := []) rfl
  · exact hT

/-- `hev`: `e` evaluates to `fun y => y` (ι on `Eq.refl`). -/
theorem hev : SrcEval (evalEnvOf view cfg P) e idB :=
  SrcEval.casesIota (as := [tB, cT, motE, cT, reflE, idB]) (i := 0) (fs := []) casesOn_Eq rfl rfl
    ev_refl ⟨`Eq.refl, [l1], Eq_refl, [tB, cT], rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl
    (SrcEval.atom trivial)

/-- The final theorem on NV-P: the program `#erase` emits for the `Eq.casesOn` on `Eq.refl` is an
untyped λ□ program whose main term evaluates to an erasure of `fun y => y`, and `fun y => y`
translates to a term definitionally equal to the input's at each of its types. -/
theorem final :
    ∃ lenv tb vb, NVPK.pP = .untyped lenv (some tb) ∧
      Erases EB BB [] (evalEnvOf view cfg P) .nil [] idB vb ∧ LBEval defaultFlags lenv tb vb ∧
      ∀ T, EB[.nil] ⊢ tE : T → ∃ t', TrM EB BB [] .nil [] idB t' ∧ EB[.nil] ⊢ tE ≡ t' : T :=
  erase_correct henv hwf hview he hty hfrag hrun hev

end EraseProof.Test.NVP

namespace EraseProof.Test.NVK

open EraseProof.Test.NV1 (tB cT B_ind Bf_ctor Bt_ctor B_rec)
open EraseProof.Test.NVP (Eq_casesOn Eq_rec Eq_refl Eq_ind l1 motE idB cfg)

theorem mem_P {ci : ConstantInfo} (h : ci ∈ P) :
    ci = .thmInfo hEq_thm ∨ ci = .defnInfo Eq_casesOn ∨ ci = .recInfo Eq_rec ∨
      ci = .ctorInfo Eq_refl ∨ ci = .inductInfo Eq_ind ∨ ci = .recInfo B_rec ∨
      ci = .ctorInfo Bf_ctor ∨ ci = .ctorInfo Bt_ctor ∨ ci = .inductInfo B_ind := by
  simpa [P, NVP.P] using h

/-- `hview`: the view `#erase` reads agrees with the program. -/
theorem hview : ViewAgrees view P := by
  intro ci h
  rcases mem_P h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- `hfrag`: the fragment test accepts `e`. -/
theorem hfrag : collectDeps view cfg e = .ok (NVPK.DD true) := NVPK.hcollectK

/-- `hrun`: the entry point returns `pP`. -/
theorem hrun : eraseEntry view cfg e = pure (NVPK.pP, []) := NVPK.hrunK

theorem casesOn_Eq : (evalEnvOf view cfg P).casesOn? `Eq.casesOn = some Eq_ind := by rfl

/-- `hev`: `e` evaluates to `fun y => y`: the major `hEq` is an atom whose statement is the type of
`@Eq.refl B B.t`, so the `casesOn` continues with the alternative. -/
theorem hev : SrcEval (evalEnvOf view cfg P) e idB :=
  SrcEval.casesProof (as := [tB, cT, motE, cT, .const `hEq [], idB]) (ps := [tB, cT]) (vs := [l1])
    casesOn_Eq rfl rfl (SrcEval.constAtom rfl) (AtomSpine.const rfl) rfl rfl rfl rfl rfl rfl rfl
    rfl rfl (SrcEval.atom trivial)

/-- The final theorem on NV-K: the program `#erase` emits for the `Eq.casesOn` on the theorem `hEq`
is an untyped λ□ program whose main term evaluates to an erasure of `fun y => y`, and
`fun y => y` translates to a term definitionally equal to the input's at each of its types. -/
theorem final :
    ∃ lenv tb vb, NVPK.pP = .untyped lenv (some tb) ∧
      Erases EK BK [] (evalEnvOf view cfg P) .nil [] idB vb ∧ LBEval defaultFlags lenv tb vb ∧
      ∀ T, EK[.nil] ⊢ tE : T → ∃ t', TrM EK BK [] .nil [] idB t' ∧ EK[.nil] ⊢ tE ≡ t' : T :=
  erase_correct henv hwf hview he hty hfrag hrun hev

end EraseProof.Test.NVK
