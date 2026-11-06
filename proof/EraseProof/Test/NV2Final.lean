import EraseProof.Final
import EraseProof.Test.NV2Model
import EraseProof.Test.NV2Run

/-!
# NV-2 end to end

The remaining hypotheses of the final theorem on NV-2 (`Test/NV2Data.lean`): the view agrees with
the program (`hview`), the fragment test accepts `e` (`hfrag`, the closure `D` of `hcollect`), and
`e` evaluates to `B.t` (`hev`: the major `W.s B.t T.i` evaluates to itself, its fields `B.t` and the
proof `T.i` being constructors, then ι on the saturated `W.casesOn` applies the alternative
`fun b h => b` to the fields, and two β-steps give `B.t`). `final` applies the final theorem
`erase_correct` to all eight hypotheses (`henv`, `hwf`, `he`, `hty` from `Test/NV2Model.lean`,
`hrun` from `Test/NV2Run.lean`): the program `p0` that `#erase` emits is an untyped λ□ program
whose main term evaluates to an erasure of `B.t`.
-/

open Lean Erasure Metalean

namespace EraseProof.Test.NV2

open EraseProof.Test.NV1 (tB cF cT B_ind Bf_ctor Bt_ctor B_rec)

theorem mem_P {ci : ConstantInfo} (h : ci ∈ P) :
    ci = .defnInfo W_casesOn ∨ ci = .recInfo W_rec ∨ ci = .ctorInfo Wn_ctor ∨
      ci = .ctorInfo Ws_ctor ∨ ci = .inductInfo W_ind ∨ ci = .recInfo T_rec ∨
      ci = .ctorInfo Ti_ctor ∨ ci = .inductInfo T_ind ∨ ci = .recInfo B_rec ∨
      ci = .ctorInfo Bf_ctor ∨ ci = .ctorInfo Bt_ctor ∨ ci = .inductInfo B_ind := by
  simpa [P] using h

/-- `hview`: the view `#erase` reads agrees with the program. -/
theorem hview : ViewAgrees view P := by
  intro ci h
  rcases mem_P h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- `hfrag`: the fragment test accepts `e`, with the closure `D`. -/
theorem hfrag : collectDeps view cfg e = .ok D := hcollect

theorem casesOn_W : (evalEnvOf view cfg P).casesOn? `W.casesOn = some W_ind := by rfl

/-- A field-less constructor evaluates to itself (`eval_construct` with no argument). -/
theorem ev_ctor0 {c : Name} {cv : ConstructorVal}
    (hc : findDecl P c = some (.ctorInfo cv)) (hn : cv.numParams + cv.numFields = 0) :
    SrcEval (evalEnvOf view cfg P) (.const c []) (.const c []) :=
  SrcEval.ctor (as := []) (vs := []) hc hn.symm rfl (fun _ _ _ h => nomatch h)

/-- The major `W.s B.t T.i` evaluates to itself. -/
theorem ev_mj : SrcEval (evalEnvOf view cfg P) mj mj := by
  refine SrcEval.ctor (c := `W.s) (us := []) (as := [cT, cI]) (vs := [cT, cI]) rfl rfl rfl ?_
  intro i a v h1 h2
  rcases i with _ | _ | i <;> simp at h1 h2 <;> subst h1 h2
  · exact ev_ctor0 rfl rfl
  · exact ev_ctor0 rfl rfl

/-- `(fun b h => b) B.t T.i` evaluates to `B.t`. -/
theorem ev_alt : SrcEval (evalEnvOf view cfg P) (mkAppN altS #[cT, cI]) cT := by
  have hT : SrcEval (evalEnvOf view cfg P) cT cT := ev_ctor0 rfl rfl
  have h1 : SrcEval (evalEnvOf view cfg P) (.app altS cT) (.lam `h tT cT .default) :=
    SrcEval.beta (by rintro ⟨c, us, ar, h, -⟩; cases h) (SrcEval.atom trivial) hT
      (SrcEval.atom trivial)
  exact SrcEval.beta (by rintro ⟨c, us, ar, h, -⟩; cases h) h1 (ev_ctor0 rfl rfl) hT

/-- `hev`: `e` evaluates to `B.t`. -/
theorem hev : SrcEval (evalEnvOf view cfg P) e cT :=
  SrcEval.casesIota (as := [motB, mj, cF, altS]) (i := 1) (fs := [cT, cI]) casesOn_W rfl rfl ev_mj
    ⟨`W.s, [], Ws_ctor, [], rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl ev_alt

/-- The final theorem on NV-2: the program `#erase` emits for
`W.casesOn (motive := fun _ => B) (W.s B.t T.i) B.f (fun b h => b)` is an untyped λ□ program whose
main term evaluates to an erasure of `B.t`, and `B.t` translates to a term definitionally equal to
the input's at each of its types. -/
theorem final :
    ∃ lenv tb vb, p0 = .untyped lenv (some tb) ∧
      Erases E B [] (evalEnvOf view cfg P) .nil [] cT vb ∧ LBEval defaultFlags lenv tb vb ∧
      ∀ T, E[.nil] ⊢ tE : T → ∃ t', TrM E B [] .nil [] cT t' ∧ E[.nil] ⊢ tE ≡ t' : T :=
  erase_correct henv hwf hview he hty hfrag hrun hev

end EraseProof.Test.NV2
