import EraseProof.FirstOrder
import EraseProof.Test.NVLModel
import EraseProof.Test.NVLRun

/-!
# NV-L end to end

The remaining hypotheses of the final theorem on NV-L (`Test/NVLData.lean`): the view agrees with
the program (`hview`), the fragment test accepts `e` (`hfrag`, the closure `D` of `hcollect`), and
`e` evaluates to `B.t` (`hev`: the recursor ι, `SrcEval.recIota`, evaluates the minor premises
`B.t` and `fun n ih => ih` and the major, the literal `2`, a value whose constructor form
(`natLitCtor`) is `Nat.succ` applied to the literal `1`, a constructor value of `Nat`; the induction
hypothesis about the field `1` is the recursor's ι on `1`, read as `Nat.succ` applied to `0`, whose
hypothesis is the ι on `0`, read as `Nat.zero`, whose minor `B.t` has no field; each minor of
`Nat.succ` applied to a literal and to the hypothesis's value `B.t` gives `B.t` by two β-steps).
`final` applies the final theorem `erase_correct` to all eight hypotheses (`henv`, `hwf`, `he`,
`hty` from `Test/NVLModel.lean`, `hrun` from `Test/NVLRun.lean`): the program `p0` that `#erase`
emits is an untyped λ□ program whose main term evaluates to an erasure of `B.t`. `firstorder`
applies `erase_correct_firstorder` to the same hypotheses: that erasure is `B.t`'s structural
erasure, the λ□ constructor `1` of `B`'s block.
-/

open Lean Erasure Metalean

namespace EraseProof.Test.NVL

open EraseProof.Test.NV1 (tB cT B_ind Bf_ctor Bt_ctor B_rec iidB)

theorem mem_P {ci : ConstantInfo} (h : ci ∈ P) :
    ci = .recInfo Nat_rec ∨ ci = .ctorInfo Zero_ctor ∨ ci = .ctorInfo Succ_ctor ∨
      ci = .inductInfo Nat_ind ∨ ci = .recInfo B_rec ∨ ci = .ctorInfo Bf_ctor ∨
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

/-- The minor premises evaluate to themselves: `B.t` is a constructor, `fun n ih => ih` a λ. -/
theorem ev_mins : ∀ (i : Nat) m mv, [cT, minS][i]? = some m → [cT, minS][i]? = some mv →
    SrcEval (evalEnvOf view cfg P) m mv := by
  intro i m mv h1 h2
  rcases i with _ | _ | i <;> simp at h1 h2 <;> subst h1 h2
  · exact ev_ctor0 rfl rfl
  · exact SrcEval.atom trivial

/-- The minor premises of `Nat.rec` have the shape of `recIota`: the induction hypothesis of `s` is
about its last field, and takes no argument. -/
theorem minors_shape : ∀ mi ∈ minorsN, mi.ihs.map (fun h => (h.field, h.binders)) =
    (List.range' (mi.fields.length - mi.ihs.length) mi.ihs.length).map fun f => (f, []) := by
  intro mi h
  simp only [minorsN, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> rfl

/-- A literal major evaluates to itself. -/
theorem ev_lit (k : Nat) : SrcEval (evalEnvOf view cfg P) (.lit (.natVal k)) (.lit (.natVal k)) :=
  SrcEval.lit

/-- `@Nat.rec (fun _ => B) B.t (fun n ih => ih) 0` evaluates to `B.t`: the recursor ι on `0`,
read as `Nat.zero`, whose minor `B.t` has no field and no induction hypothesis. -/
theorem ev_ih0 : SrcEval (evalEnvOf view cfg P)
    (mkAppN (.const `Nat.rec [.succ .zero]) ([] ++ [motB] ++ [cT, minS] ++
      [Expr.lit (.natVal 0)]).toArray) cT :=
  SrcEval.recIota (ps := []) (ms := [motB]) (mins := [cT, minS]) (mvs := [cT, minS]) (fs := [])
    (rfs := []) (ihvs := []) (T := `Nat) (iv := Nat_ind) (cvs := [Zero_ctor, Succ_ctor]) rfl rfl rfl
    rfl rfl recShape_N minors_shape rfl rfl rfl rfl ev_mins (ev_lit 0)
    ⟨`Nat.zero, [], Zero_ctor, [], rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl
    (fun _ _ _ h => nomatch h) (ev_ctor0 rfl rfl)

/-- `(fun n ih => ih) k B.t` evaluates to `B.t`. -/
theorem ev_minS (k : Nat) :
    SrcEval (evalEnvOf view cfg P) (mkAppN minS ([Expr.lit (.natVal k)] ++ [cT]).toArray) cT := by
  have hT : SrcEval (evalEnvOf view cfg P) cT cT := ev_ctor0 rfl rfl
  have h1 : SrcEval (evalEnvOf view cfg P) (.app minS (.lit (.natVal k)))
      (.lam `ih tB (.bvar 0) .default) :=
    SrcEval.beta (by rintro ⟨c, us, ar, h, -⟩; cases h) (SrcEval.atom trivial) (ev_lit k)
      (SrcEval.atom trivial)
  exact SrcEval.beta (by rintro ⟨c, us, ar, h, -⟩; cases h) h1 hT hT

/-- The recursor on `k + 1` evaluates to `B.t` when it does on `k`: the ι on `k + 1`, read as
`Nat.succ` applied to `k`, with the induction hypothesis the recursor on `k`. -/
theorem ev_succ {k : Nat} (ih : SrcEval (evalEnvOf view cfg P)
      (mkAppN (.const `Nat.rec [.succ .zero]) ([] ++ [motB] ++ [cT, minS] ++
        [Expr.lit (.natVal k)]).toArray) cT) :
    SrcEval (evalEnvOf view cfg P)
      (mkAppN (.const `Nat.rec [.succ .zero]) ([] ++ [motB] ++ [cT, minS] ++
        [Expr.lit (.natVal (k + 1))]).toArray) cT :=
  SrcEval.recIota (ps := []) (ms := [motB]) (mins := [cT, minS]) (mvs := [cT, minS])
    (fs := [Expr.lit (.natVal k)]) (rfs := [Expr.lit (.natVal k)]) (ihvs := [cT]) (T := `Nat)
    (iv := Nat_ind) (cvs := [Zero_ctor, Succ_ctor]) rfl rfl rfl rfl rfl recShape_N minors_shape rfl
    rfl rfl rfl ev_mins (ev_lit (k + 1))
    ⟨`Nat.succ, [], Succ_ctor, [], rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl
    (fun i f w h1 h2 => by
      rcases i with _ | i <;> simp at h1 h2
      subst h1 h2
      exact ih)
    (ev_minS k)

/-- `hev`: `e` evaluates to `B.t`. -/
theorem hev : SrcEval (evalEnvOf view cfg P) e cT := ev_succ (ev_succ ev_ih0)

/-- The final theorem on NV-L: the program `#erase` emits for
`@Nat.rec (fun _ => B) B.t (fun _ (ih : B) => ih) 2` under `nat := .peano` is an untyped λ□
program whose main term evaluates to an erasure of `B.t`, and `B.t` translates to a term
definitionally equal to the input's at each of its types. -/
theorem final :
    ∃ lenv tb vb, p0 = .untyped lenv (some tb) ∧
      Erases E B [] (evalEnvOf view cfg P) .nil [] cT vb ∧ LBEval defaultFlags lenv tb vb ∧
      ∀ T, E[.nil] ⊢ tE : T → ∃ t', TrM E B [] .nil [] cT t' ∧ E[.nil] ⊢ tE ≡ t' : T :=
  erase_correct henv hwf hview he hty hfrag hrun hev

/-- `B.t` is a first-order value: a constructor of `B : Type` with no parameter and no field. -/
theorem fo_cT : FirstOrderValue (evalEnvOf view cfg P) cT :=
  FirstOrderValue.ctor (c := `B.t) (us := []) (as := []) (n := 0) (u := .succ .zero) rfl rfl rfl
    rfl rfl (fun _ h => nomatch h)

/-- The final theorem on first-order values on NV-L: the main term of the program `#erase` emits
evaluates in λ□ to `B.t`'s structural erasure, the constructor `1` of `B`'s block. -/
theorem firstorder :
    ∃ lenv tb, p0 = .untyped lenv (some tb) ∧ LBEval defaultFlags lenv tb (.construct iidB 1 []) :=
  erase_correct_firstorder henv hwf hview he hty hfrag hrun hev fo_cT

end EraseProof.Test.NVL
