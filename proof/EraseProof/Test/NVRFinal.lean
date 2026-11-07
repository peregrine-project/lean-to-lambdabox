import EraseProof.FirstOrder
import EraseProof.Test.NVRModel
import EraseProof.Test.NVRRun

/-!
# NV-R end to end

The remaining hypotheses of the final theorem on NV-R (`Test/NVRData.lean`): the view agrees with
the program (`hview`), the fragment test accepts `e` (`hfrag`, the closure `D` of `hcollect`), and
`e` evaluates to `B.t` (`hev`: the recursor ι, `SrcEval.recIota`, evaluates the minor premises
`B.t` and `fun n ih => ih` and the major `N.s N.z`, a constructor value of `N`; the induction
hypothesis about the field `N.z` is the recursor's ι once more, on `N.z`, whose minor `B.t` has no
field; the minor of `N.s` applied to the field `N.z` and to the induction hypothesis's value `B.t`
gives `B.t` by two β-steps). `final` applies the final theorem `erase_correct` to all eight
hypotheses (`henv`, `hwf`, `he`, `hty` from `Test/NVRModel.lean`, `hrun` from `Test/NVRRun.lean`):
the program `p0` that `#erase` emits is an untyped λ□ program whose main term evaluates to an
erasure of `B.t`. `firstorder` applies `erase_correct_firstorder` to the same hypotheses: that
erasure is `B.t`'s structural erasure, the λ□ constructor `1` of `B`'s block.
-/

open Lean Erasure Metalean

namespace EraseProof.Test.NVR

open EraseProof.Test.NV1 (tB cT B_ind Bf_ctor Bt_ctor B_rec iidB)

theorem mem_P {ci : ConstantInfo} (h : ci ∈ P) :
    ci = .recInfo N_rec ∨ ci = .ctorInfo Nz_ctor ∨ ci = .ctorInfo Ns_ctor ∨
      ci = .inductInfo N_ind ∨ ci = .recInfo B_rec ∨ ci = .ctorInfo Bf_ctor ∨
      ci = .ctorInfo Bt_ctor ∨ ci = .inductInfo B_ind := by
  simpa [P] using h

/-- `hview`: the view `#erase` reads agrees with the program. -/
theorem hview : ViewAgrees view P := by
  intro ci h
  rcases mem_P h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- `hfrag`: the fragment test accepts `e`, with the closure `D`. -/
theorem hfrag : collectDeps view cfg e = .ok D := hcollect

/-- A field-less constructor evaluates to itself (`eval_construct` with no argument). -/
theorem ev_ctor0 {c : Name} {cv : ConstructorVal}
    (hc : findDecl P c = some (.ctorInfo cv)) (hn : cv.numParams + cv.numFields = 0) :
    SrcEval (evalEnvOf view cfg P) (.const c []) (.const c []) :=
  SrcEval.ctor (as := []) (vs := []) hc hn.symm rfl (fun _ _ _ h => nomatch h)

/-- The major `N.s N.z` evaluates to itself. -/
theorem ev_mj : SrcEval (evalEnvOf view cfg P) mj mj := by
  refine SrcEval.ctor (c := `N.s) (us := []) (as := [cZ]) (vs := [cZ]) rfl rfl rfl ?_
  intro i a v h1 h2
  rcases i with _ | i <;> simp at h1 h2
  subst h1 h2
  exact ev_ctor0 rfl rfl

/-- The minor premises evaluate to themselves: `B.t` is a constructor, `fun n ih => ih` a λ. -/
theorem ev_mins : ∀ (i : Nat) m mv, [cT, minS][i]? = some m → [cT, minS][i]? = some mv →
    SrcEval (evalEnvOf view cfg P) m mv := by
  intro i m mv h1 h2
  rcases i with _ | _ | i <;> simp at h1 h2 <;> subst h1 h2
  · exact ev_ctor0 rfl rfl
  · exact SrcEval.atom trivial

/-- The minor premises of `N.rec` have the shape of `recIota`: the induction hypothesis of `s` is
about its last field, and takes no argument. -/
theorem minors_shape : ∀ mi ∈ minorsN, mi.ihs.map (fun h => (h.field, h.binders)) =
    (List.range' (mi.fields.length - mi.ihs.length) mi.ihs.length).map fun f => (f, []) := by
  intro mi h
  simp only [minorsN, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> rfl

/-- `@N.rec (fun _ => B) B.t (fun n ih => ih) N.z` evaluates to `B.t`: the recursor ι on `N.z`,
whose minor `B.t` has no field and no induction hypothesis. -/
theorem ev_ih : SrcEval (evalEnvOf view cfg P)
    (mkAppN (.const `N.rec [.succ .zero]) ([] ++ [motB] ++ [cT, minS] ++ [cZ]).toArray) cT :=
  SrcEval.recIota (ps := []) (ms := [motB]) (mins := [cT, minS]) (mvs := [cT, minS]) (fs := [])
    (rfs := []) (ihvs := []) (T := `N) (iv := N_ind) (cvs := [Nz_ctor, Ns_ctor]) rfl rfl rfl rfl
    rfl recShape_N minors_shape rfl rfl rfl rfl ev_mins (ev_ctor0 rfl rfl)
    ⟨`N.z, [], Nz_ctor, [], rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl
    (fun _ _ _ h => nomatch h) (ev_ctor0 rfl rfl)

/-- `(fun n ih => ih) N.z B.t` evaluates to `B.t`. -/
theorem ev_minS : SrcEval (evalEnvOf view cfg P) (mkAppN minS ([cZ] ++ [cT]).toArray) cT := by
  have hT : SrcEval (evalEnvOf view cfg P) cT cT := ev_ctor0 rfl rfl
  have h1 : SrcEval (evalEnvOf view cfg P) (.app minS cZ) (.lam `ih tB (.bvar 0) .default) :=
    SrcEval.beta (by rintro ⟨c, us, ar, h, -⟩; cases h) (SrcEval.atom trivial) (ev_ctor0 rfl rfl)
      (SrcEval.atom trivial)
  exact SrcEval.beta (by rintro ⟨c, us, ar, h, -⟩; cases h) h1 hT hT

/-- `hev`: `e` evaluates to `B.t`. -/
theorem hev : SrcEval (evalEnvOf view cfg P) e cT :=
  SrcEval.recIota (ps := []) (ms := [motB]) (mins := [cT, minS]) (mvs := [cT, minS]) (fs := [cZ])
    (rfs := [cZ]) (ihvs := [cT]) (T := `N) (iv := N_ind) (cvs := [Nz_ctor, Ns_ctor]) rfl rfl rfl
    rfl rfl recShape_N minors_shape rfl rfl rfl rfl ev_mins ev_mj
    ⟨`N.s, [], Ns_ctor, [], rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl
    (fun i f w h1 h2 => by
      rcases i with _ | i <;> simp at h1 h2
      subst h1 h2
      exact ev_ih)
    ev_minS

/-- The final theorem on NV-R: the program `#erase` emits for
`@N.rec (fun _ => B) B.t (fun _ (ih : B) => ih) (N.s N.z)` is an untyped λ□ program whose main
term evaluates to an erasure of `B.t`, and `B.t` translates to a term definitionally equal to the
input's at each of its types. -/
theorem final :
    ∃ lenv tb vb, p0 = .untyped lenv (some tb) ∧
      Erases E B [] (evalEnvOf view cfg P) .nil [] cT vb ∧ LBEval defaultFlags lenv tb vb ∧
      ∀ T, E[.nil] ⊢ tE : T → ∃ t', TrM E B [] .nil [] cT t' ∧ E[.nil] ⊢ tE ≡ t' : T :=
  erase_correct henv hwf hview he hty hfrag hrun hev

/-- `B.t` is a first-order value: a constructor of `B : Type` with no parameter and no field. -/
theorem fo_cT : FirstOrderValue (evalEnvOf view cfg P) cT :=
  FirstOrderValue.ctor (c := `B.t) (us := []) (as := []) (n := 0) (u := .succ .zero) rfl rfl rfl
    rfl rfl (fun _ h => nomatch h)

/-- The final theorem on first-order values on NV-R: the main term of the program `#erase` emits
evaluates in λ□ to `B.t`'s structural erasure, the constructor `1` of `B`'s block. -/
theorem firstorder :
    ∃ lenv tb, p0 = .untyped lenv (some tb) ∧ LBEval defaultFlags lenv tb (.construct iidB 1 []) :=
  erase_correct_firstorder henv hwf hview he hty hfrag hrun hev fo_cT

end EraseProof.Test.NVR
