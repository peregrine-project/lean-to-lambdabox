import EraseProof.Final
import EraseProof.Test.NV1Model
import EraseProof.Test.NV1Run

/-!
# NV-1 end to end

The remaining hypotheses of the final theorem on NV-1 (`Test/NV1Data.lean`): the view agrees with
the program (`hview`), the fragment test accepts `e` (`hfrag`, the closure `D` of `hcollect`), and
`e = B.neg B.f` evaluates to `B.t` (`hev`: δ on `B.neg`, β, then ι on the saturated `B.casesOn`).
`final` applies `erase_correct_of_pure` to all eight hypotheses (`henv`, `hwf`, `he`, `hty` from
`Test/NV1Model.lean`, `hrun` from `Test/NV1Run.lean`): the program `p0` that `#erase` emits is an
untyped λ□ program whose main term evaluates to an erasure of `B.t`, given the correctness of the
pure traversal.
-/

open Lean Erasure Metalean

namespace EraseProof.Test.NV1

theorem mem_P {ci : ConstantInfo} (h : ci ∈ P) :
    ci = .defnInfo neg_def ∨ ci = .defnInfo B_casesOn ∨ ci = .recInfo B_rec ∨
      ci = .ctorInfo Bf_ctor ∨ ci = .ctorInfo Bt_ctor ∨ ci = .inductInfo B_ind := by
  simpa [P] using h

/-- `hview`: the view `#erase` reads agrees with the program. -/
theorem hview : ViewAgrees view P := by
  intro ci h
  rcases mem_P h with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- `hfrag`: the fragment test accepts `e`, with the closure `D`. -/
theorem hfrag : collectDeps view cfg e = .ok D := hcollect

theorem casesOn_B : (evalEnvOf view cfg P).casesOn? `B.casesOn = some B_ind := by rfl

/-- A field-less constructor of `B` evaluates to itself (`eval_construct` with no argument). -/
theorem ev_ctor0 {c : Name} {cv : ConstructorVal}
    (hc : findDecl P c = some (.ctorInfo cv)) (hn : cv.numParams + cv.numFields = 0) :
    SrcEval (evalEnvOf view cfg P) (.const c []) (.const c []) :=
  SrcEval.ctor (as := []) (vs := []) hc hn.symm rfl (fun _ _ _ h => nomatch h)

/-- `hev`: `B.neg B.f` evaluates to `B.t`. -/
theorem hev : SrcEval (evalEnvOf view cfg P) e cT := by
  have hF : SrcEval (evalEnvOf view cfg P) cF cF := ev_ctor0 rfl rfl
  have hT : SrcEval (evalEnvOf view cfg P) cT cT := ev_ctor0 rfl rfl
  have hcases : SrcEval (evalEnvOf view cfg P)
      (mkAppN (.const `B.casesOn [.succ .zero]) [.lam `x tB tB .default, cF, cT, cF].toArray) cT :=
    SrcEval.casesIota (i := 0) (fs := []) casesOn_B rfl rfl hF
      ⟨`B.f, [], Bf_ctor, [], rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl hT
  refine SrcEval.beta ?_ (SrcEval.delta rfl (SrcEval.atom trivial)) hF hcases
  rintro ⟨c, us, ar, h, h', -⟩
  cases h
  cases h'

/-- The final theorem on NV-1: the program `#erase` emits for `B.neg B.f` is an untyped λ□ program
whose main term evaluates to an erasure of `B.t`, and `B.t` translates to a term definitionally
equal to `B.neg B.f`'s at each of its types. -/
theorem final (h : erasePure_erases_statement) :
    ∃ lenv tb vb, p0 = .untyped lenv (some tb) ∧
      Erases E B [] (evalEnvOf view cfg P) .nil [] cT vb ∧ LBEval defaultFlags lenv tb vb ∧
      ∀ T, E[.nil] ⊢ tE : T → ∃ t', TrM E B [] .nil [] cT t' ∧ E[.nil] ⊢ tE ≡ t' : T :=
  erase_correct_of_pure h henv hwf hview he hty hfrag hrun hev

end EraseProof.Test.NV1
