import EraseProof.FirstOrder
import EraseProof.Test.NVQPModel
import EraseProof.Test.NVQPRun

/-!
# NV-QP end to end

The remaining hypotheses of the final theorem on NV-QP (`Test/NVQPData.lean`): the view agrees with
the program (`hview`), the fragment test accepts `e` (`hfrag`, the closure `D` of `hcollect`), and
`e` evaluates to `B.t` (`hev`). The evaluation unfolds `useTF` (δ) to `orU` applied to the class
`Quot.mk swapR (B.t, B.f)`; `orU` unfolds to `Quot.lift (fun p => orB p.1 p.2) orU._proof_1`, a
spine with five of `Quot.lift`'s six arguments, which is its η-expansion (`SrcEval.eta`); the β-step
on the class gives the saturated spine, whose quotient ι (`SrcEval.quotLift`) continues with
`orB p.1 p.2` at the element `(B.t, B.f)`. The projections unfold (δ, β) to primitive projections of
the pair (`SrcEval.proj`); `orB` unfolds (δ, β) to its matcher, the matcher (δ, β) to `B.casesOn`
on `B.t`, whose ι (`SrcEval.casesIota`) takes the second alternative `fun _ => B.t`. `hevFT` is the
evaluation of the second term `useFT`, on the other representative `(B.f, B.t)` of the class: the
same steps, with the ι of `B.casesOn` on `B.f` taking the first alternative `fun b => b` at `B.t`.
Both representatives give `B.t`. `final` applies the final theorem `erase_correct` to all eight
hypotheses (`henv`, `hwf`, `he`, `hty` from `Test/NVQPModel.lean`, `hrun` from
`Test/NVQPRun.lean`); `firstorder` applies `erase_correct_firstorder`.
-/

open Lean Erasure Metalean

namespace EraseProof.Test.NVQP

open EraseProof.Test.NV1 (tB cF cT B_ind Bf_ctor Bt_ctor B_rec B_casesOn iidB)
open EraseProof.Test.NVP (l1)
open EraseProof.Test.NVQ (Quot_val QuotMk_val QuotLift_val QuotInd_val)

theorem mem_P {ci : ConstantInfo} (h : ci ∈ P) :
    ci = .defnInfo useFT_def ∨ ci = .defnInfo useTF_def ∨ ci = .defnInfo orU_def ∨
      ci = .thmInfo resp_thm ∨ ci = .defnInfo swapR_def ∨ ci = .defnInfo orB_def ∨
      ci = .defnInfo orB_match_1 ∨ ci = .defnInfo B_casesOn ∨ ci = .defnInfo Prod_snd ∨
      ci = .defnInfo Prod_fst ∨ ci = .recInfo Prod_rec ∨ ci = .ctorInfo Prod_mk ∨
      ci = .inductInfo Prod_ind ∨ ci = .quotInfo QuotInd_val ∨ ci = .quotInfo QuotLift_val ∨
      ci = .quotInfo QuotMk_val ∨ ci = .quotInfo Quot_val ∨ ci ∈ NVP.P := by
  simpa [P, NVQ.qs] using h

/-- `hview`: the view `#erase` reads agrees with the program. -/
theorem hview : ViewAgrees view P := by
  intro ci h
  rcases mem_P h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | h
  all_goals try rfl
  simp only [NVP.P, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- `hfrag`: the fragment test accepts `e`, with the closure `D`. -/
theorem hfrag : collectDeps view cfg e = .ok D := hcollect

/-! ## The source evaluation -/

/-- The evaluation environment. -/
abbrev σ : EvalEnv := evalEnvOf view cfg P

theorem ns_const {f a : Lean.Expr} {c : Name} {us : List Lean.Level} (h : f.getAppFn = .const c us)
    (hc : specialArity σ c = none) : ¬ ShortSpine σ (.app f a) := by
  rintro ⟨c', us', ar, h1, h2, -⟩
  have h1' : f.getAppFn = .const c' us' := h1
  rw [h] at h1'
  cases h1'
  rw [hc] at h2
  cases h2

theorem ns_lam {f a : Lean.Expr} {n : Name} {A b : Lean.Expr} {bi : BinderInfo}
    (h : f.getAppFn = .lam n A b bi) : ¬ ShortSpine σ (.app f a) := by
  rintro ⟨c, us, ar, h1, -⟩
  have h1' : f.getAppFn = .const c us := h1
  rw [h] at h1'
  cases h1'

theorem ev_atom {x : Lean.Expr} (h : SrcAtom x) : SrcEval σ x x := .atom h

theorem ev_cT : SrcEval σ cT cT :=
  SrcEval.ctor (c := `B.t) (us := []) (as := []) (vs := []) rfl rfl rfl (fun _ _ _ h => nomatch h)
theorem ev_cF : SrcEval σ cF cF :=
  SrcEval.ctor (c := `B.f) (us := []) (as := []) (vs := []) rfl rfl rfl (fun _ _ _ h => nomatch h)
theorem ev_tB : SrcEval σ tB tB := .constAtom (by krfl)

/-- A pair of values is a value. -/
theorem ev_pair {ca cb : Name} (ha : SrcEval σ (.const ca []) (.const ca []))
    (hb : SrcEval σ (.const cb []) (.const cb [])) :
    SrcEval σ (pairB (.const ca []) (.const cb [])) (pairB (.const ca []) (.const cb [])) := by
  refine SrcEval.ctor (c := `Prod.mk) (us := [.zero, .zero]) (as := [tB, tB, .const ca [], .const cb []])
    (vs := [tB, tB, .const ca [], .const cb []]) rfl rfl rfl ?_
  intro i x v h1 h2
  rcases i with _ | _ | _ | _ | i <;> simp at h1 h2 <;> subst h1 h2
  · exact ev_tB
  · exact ev_tB
  · exact ha
  · exact hb

/-- The class of a pair of values is a value. -/
theorem ev_class {ca cb : Name} (ha : SrcEval σ (.const ca []) (.const ca []))
    (hb : SrcEval σ (.const cb []) (.const cb [])) :
    SrcEval σ (mkAppN (.const `Quot.mk [l1]) #[tP, .const `swapR [], pairB (.const ca []) (.const cb [])])
      (mkAppN (.const `Quot.mk [l1]) #[tP, .const `swapR [], pairB (.const ca []) (.const cb [])]) :=
  SrcEval.quotMk (qv := QuotMk_val) (α := tP) (r := .const `swapR []) rfl rfl (ev_pair ha hb)

theorem ev_delta {c : Name} {us : List Lean.Level} {v : DefinitionVal} {r : Lean.Expr}
    (h : σ.unfold? c = some (.defnInfo v, v.value))
    (hr : SrcEval σ (Pure.instLevels v.levelParams us v.value) r) : SrcEval σ (.const c us) r :=
  .delta h hr

/-- `(a, b).1 ⇓ a`: δ of `Prod.fst`, three β, the primitive projection. -/
theorem ev_fst {ca cb : Name} (ha : SrcEval σ (.const ca []) (.const ca []))
    (hb : SrcEval σ (.const cb []) (.const cb [])) :
    SrcEval σ (fstB (pairB (.const ca []) (.const cb []))) (.const ca []) := by
  have hns : specialArity σ `Prod.fst = none := by krfl
  have h0 := ev_delta (c := `Prod.fst) (us := [.zero, .zero]) (v := Prod_fst) (by krfl)
    (ev_atom trivial)
  have h1 := SrcEval.beta (ns_const rfl hns) h0 ev_tB (ev_atom trivial)
  have h2 := SrcEval.beta (ns_const rfl hns) h1 ev_tB (ev_atom trivial)
  refine SrcEval.beta (ns_const rfl hns) h2 (ev_pair ha hb) ?_
  exact SrcEval.proj (fs := [.const ca [], .const cb []]) (ev_pair ha hb) ⟨`Prod.mk, [.zero, .zero], Prod_mk, [tB, tB], rfl, rfl, rfl,
    rfl, rfl, rfl⟩ rfl

/-- `(a, b).2 ⇓ b`. -/
theorem ev_snd {ca cb : Name} (ha : SrcEval σ (.const ca []) (.const ca []))
    (hb : SrcEval σ (.const cb []) (.const cb [])) :
    SrcEval σ (sndB (pairB (.const ca []) (.const cb []))) (.const cb []) := by
  have hns : specialArity σ `Prod.snd = none := by krfl
  have h0 := ev_delta (c := `Prod.snd) (us := [.zero, .zero]) (v := Prod_snd) (by krfl)
    (ev_atom trivial)
  have h1 := SrcEval.beta (ns_const rfl hns) h0 ev_tB (ev_atom trivial)
  have h2 := SrcEval.beta (ns_const rfl hns) h1 ev_tB (ev_atom trivial)
  refine SrcEval.beta (ns_const rfl hns) h2 (ev_pair ha hb) ?_
  exact SrcEval.proj (fs := [.const ca [], .const cb []]) (ev_pair ha hb) ⟨`Prod.mk, [.zero, .zero], Prod_mk, [tB, tB], rfl, rfl, rfl,
    rfl, rfl, rfl⟩ rfl

theorem casesOn_B : σ.casesOn? `B.casesOn = some B_ind := by krfl

/-- `orB.match_1 motO a b altB altT` after δ and β: `B.casesOn (fun x => motO x b) a (altB b)
(altT b)`. -/
def casesO (a b : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.const `B.casesOn [l1]) (.lam `x tB (.app (.app motO (.bvar 0)) b)
    .default)) a) (.app altB b)) (.app altT b)

/-- `orB X Y ⇓ v` from the values `a`, `b` of `X`, `Y` and the evaluation of the matcher's
`B.casesOn`: δ of `orB`, two β, δ of `orB.match_1`, five β. -/
theorem ev_orB {X Y v : Lean.Expr} {ca cb : Name} (hX : SrcEval σ X (.const ca []))
    (hY : SrcEval σ Y (.const cb [])) (ha : SrcEval σ (.const ca []) (.const ca []))
    (hb : SrcEval σ (.const cb []) (.const cb []))
    (hcases : SrcEval σ (casesO (.const ca []) (.const cb [])) v) :
    SrcEval σ (orBC X Y) v := by
  have hno : specialArity σ `orB = none := by krfl
  have hnm : specialArity σ `orB.match_1 = none := by krfl
  have h0 := ev_delta (c := `orB) (us := []) (v := orB_def) (by krfl) (ev_atom trivial)
  have h1 := SrcEval.beta (ns_const rfl hno) h0 hX (ev_atom trivial)
  refine SrcEval.beta (ns_const rfl hno) h1 hY ?_
  have m0 := ev_delta (c := `orB.match_1) (us := [l1]) (v := orB_match_1) (by krfl)
    (ev_atom trivial)
  have m1 := SrcEval.beta (ns_const rfl hnm) m0 (ev_atom (x := motO) trivial) (ev_atom trivial)
  have m2 := SrcEval.beta (ns_const rfl hnm) m1 ha (ev_atom trivial)
  have m3 := SrcEval.beta (ns_const rfl hnm) m2 hb (ev_atom trivial)
  have m4 := SrcEval.beta (ns_const rfl hnm) m3 (ev_atom (x := altB) trivial) (ev_atom trivial)
  exact SrcEval.beta (ns_const rfl hnm) m4 (ev_atom (x := altT) trivial) hcases

/-- The ι of `B.casesOn` on `B.t`: the second alternative `fun _ => B.t`. -/
theorem ev_casesT {cb : Name} (hb : SrcEval σ (.const cb []) (.const cb [])) :
    SrcEval σ (casesO cT (.const cb [])) cT := by
  refine SrcEval.casesIota (c := `B.casesOn) (us := [l1])
    (as := [.lam `x tB (.app (.app motO (.bvar 0)) (.const cb [])) .default, cT,
      .app altB (.const cb []), .app altT (.const cb [])])
    (i := 1) (fs := []) casesOn_B rfl rfl ev_cT ⟨`B.t, [], Bt_ctor, [], rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl ?_
  exact .beta (ns_lam rfl) (ev_atom trivial) hb ev_cT

/-- The ι of `B.casesOn` on `B.f`: the first alternative `fun b => b`. -/
theorem ev_casesF {cb : Name} (hb : SrcEval σ (.const cb []) (.const cb [])) :
    SrcEval σ (casesO cF (.const cb [])) (.const cb []) := by
  refine SrcEval.casesIota (c := `B.casesOn) (us := [l1])
    (as := [.lam `x tB (.app (.app motO (.bvar 0)) (.const cb [])) .default, cF,
      .app altB (.const cb []), .app altT (.const cb [])])
    (i := 0) (fs := []) casesOn_B rfl rfl ev_cF ⟨`B.f, [], Bf_ctor, [], rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl ?_
  exact .beta (ns_lam rfl) (ev_atom trivial) hb hb

/-- `Quot (Prod B B) swapR` -/
def tQL : Lean.Expr := .app (.app (.const `Quot [l1]) tP) (.const `swapR [])

/-- `orU`'s value, a spine of `Quot.lift` with five arguments, is its η-expansion
`fun a => Quot.lift (fun p => orB p.1 p.2) orU._proof_1 a`. -/
def etaU : Lean.Expr :=
  .lam `a tQL (mkAppN (.const `Quot.lift [l1, l1])
    #[tP, .const `swapR [], tB, liftF, .const `orU._proof_1 [], .bvar 0]) .default

theorem ev_orU : SrcEval σ (.const `orU []) etaU :=
  ev_delta (v := orU_def) (by krfl)
    (SrcEval.eta (c := `Quot.lift) (us := [l1, l1])
      (as := [tP, .const `swapR [], tB, liftF, .const `orU._proof_1 []]) (by krfl))

/-- `orU (Quot.mk swapR (a, b)) ⇓ v` from the evaluation of `orB (a, b).1 (a, b).2`: the β-step on
the class gives the saturated spine of `Quot.lift`, and the quotient ι continues with the lifted
function's body at the element. -/
theorem ev_use {ca cb : Name} {v : Lean.Expr} (ha : SrcEval σ (.const ca []) (.const ca []))
    (hb : SrcEval σ (.const cb []) (.const cb []))
    (hbody : SrcEval σ (orBC (fstB (pairB (.const ca []) (.const cb [])))
      (sndB (pairB (.const ca []) (.const cb [])))) v) :
    SrcEval σ (useVal (.const ca []) (.const cb [])) v := by
  refine SrcEval.beta (ns_const rfl (by krfl)) ev_orU (ev_class ha hb) ?_
  show SrcEval σ (mkAppN (.const `Quot.lift [l1, l1]) #[tP, .const `swapR [], tB, liftF,
    .const `orU._proof_1 [], mkAppN (.const `Quot.mk [l1])
      #[tP, .const `swapR [], pairB (.const ca []) (.const cb [])]]) v
  exact SrcEval.quotLift (qv := QuotLift_val) (qv' := QuotMk_val) rfl rfl (ev_atom trivial)
    (ev_class ha hb) rfl rfl hbody

/-- `hev`: `e` evaluates to `B.t`. -/
theorem hev : SrcEval σ e cT :=
  ev_delta (v := useTF_def) (by krfl)
    (ev_use ev_cT ev_cF (ev_orB (ev_fst ev_cT ev_cF) (ev_snd ev_cT ev_cF) ev_cT ev_cF
      (ev_casesT ev_cF)))

/-- `hevFT`: the second term `useFT`, `orU` on the other representative `(B.f, B.t)` of the class,
evaluates to `B.t` too. -/
theorem hevFT : SrcEval σ eFT cT :=
  ev_delta (v := useFT_def) (by krfl)
    (ev_use ev_cF ev_cT (ev_orB (ev_fst ev_cF ev_cT) (ev_snd ev_cF ev_cT) ev_cF ev_cT
      (ev_casesF ev_cT)))

/-! ## The final theorem on NV-QP -/

/-- The final theorem on NV-QP: the program `#erase` emits for `useTF`, a function on unordered
pairs of `B` (a quotient of `Prod B B` whose relation identifies distinct pairs) at the class of
`(B.t, B.f)`, is an untyped λ□ program whose main term evaluates to an erasure of `B.t`, and `B.t`
translates to a term definitionally equal to the input's at each of its types. -/
theorem final :
    ∃ lenv tb vb, p0 = .untyped lenv (some tb) ∧
      Erases E B [] σ .nil [] cT vb ∧ LBEval defaultFlags lenv tb vb ∧
      ∀ T, E[.nil] ⊢ tE : T → ∃ t', TrM E B [] .nil [] cT t' ∧ E[.nil] ⊢ tE ≡ t' : T :=
  erase_correct henv hwf hview he hty hfrag hrun hev

/-- `B.t` is a first-order value: a constructor of `B : Type` with no parameter and no field. -/
theorem fo_cT : FirstOrderValue σ cT :=
  FirstOrderValue.ctor (c := `B.t) (us := []) (as := []) (n := 0) (u := .succ .zero) rfl rfl rfl
    rfl rfl (fun _ h => nomatch h)

/-- The final theorem on first-order values on NV-QP: the main term of the program `#erase` emits
evaluates in λ□ to `B.t`'s structural erasure, the constructor `1` of `B`'s block. -/
theorem firstorder :
    ∃ lenv tb, p0 = .untyped lenv (some tb) ∧ LBEval defaultFlags lenv tb (.construct iidB 1 []) :=
  erase_correct_firstorder henv hwf hview he hty hfrag hrun hev fo_cT

end EraseProof.Test.NVQP
