import EraseProof.FirstOrder
import EraseProof.Test.NVSModel
import EraseProof.Test.NVSRun
import EraseProof.Test.NVRFinal

/-!
# NV-S end to end

The remaining hypotheses of the final theorem on NV-S (`Test/NVSData.lean`): the view agrees with
the program (`hview`), the fragment test accepts `e` (`hfrag`, the closure `D` of `hcollect`), and
`e` evaluates to `N.s (N.s N.z)` (`hev`). The evaluation unfolds `add`, then `N.brecOn` and
`N.brecOn.go` (δ, β): the recursor `N.rec` into the pairs `PProd (motive t) (N.below motive t)` takes
its ι on `N.s N.z` (`SrcEval.recIota`), with the induction hypothesis its ι on `N.z`; each step
applies `add._f n` to the table built so far, which matches with `add.match_1`, a `N.casesOn` (δ,
then `SrcEval.casesIota`); the recursive call is the first projection of the table
(`SrcEval.proj`), and the result is the first projection of the pair. `final` applies the final
theorem `erase_correct` to all eight hypotheses (`henv`, `hwf`, `he`, `hty` from
`Test/NVSModel.lean`, `hrun` from `Test/NVSRun.lean`); `firstorder` applies
`erase_correct_firstorder`: the main term of the program `#erase` emits evaluates in λ□ to
`N.s (N.s N.z)`'s structural erasure.
-/

open Lean Erasure Metalean

namespace EraseProof.Test.NVS

open EraseProof.Test.NVR (tN cZ cS N_ind Nz_ctor Ns_ctor N_rec mj recShape_N minorsN minors_shape
  iidN)

theorem mem_P {ci : ConstantInfo} (h : ci ∈ P) :
    ci = .defnInfo add_def ∨
      ci = .defnInfo add_f ∨
      ci = .defnInfo add_match_1 ∨
      ci = .defnInfo N_brecOn ∨
      ci = .defnInfo N_brecOn_go ∨
      ci = .defnInfo N_below ∨
      ci = .defnInfo N_casesOn ∨
      ci = .recInfo N_rec ∨
      ci = .ctorInfo Nz_ctor ∨
      ci = .ctorInfo Ns_ctor ∨
      ci = .inductInfo N_ind ∨
      ci = .recInfo PProd_rec ∨
      ci = .ctorInfo PProd_mk ∨
      ci = .inductInfo PProd_ind ∨
      ci = .defnInfo Unit_unit ∨
      ci = .defnInfo Unit_def ∨
      ci = .recInfo PUnit_rec ∨
      ci = .ctorInfo PUnit_unit ∨
      ci = .inductInfo PUnit_ind := by
  simpa [P] using h

/-- `hview`: the view `#erase` reads agrees with the program. -/
theorem hview : ViewAgrees view P := by
  intro ci h
  rcases mem_P h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- `hfrag`: the fragment test accepts `e`, with the closure `D`. -/
theorem hfrag : collectDeps view cfg e = .ok D := hcollect

/-! ## The source evaluation -/

/-- The evaluation environment. -/
abbrev σ : EvalEnv := evalEnvOf view cfg P

/-- `max 1 1`, `max 1 u` at `u := 1`. -/
def ml : Lean.Level := .max l1 l1
/-- `N.s (N.s N.z)`. -/
def ssz : Lean.Expr := .app cS mj

theorem ns_lam {f a : Lean.Expr} {n : Name} {A b : Lean.Expr} {bi : BinderInfo}
    (h : f.getAppFn = .lam n A b bi) : ¬ ShortSpine σ (.app f a) := by
  rintro ⟨c, us, ar, h1, -⟩
  have h1' : f.getAppFn = .const c us := h1
  rw [h] at h1'
  cases h1'

theorem ns_const {f a : Lean.Expr} {c : Name} {us : List Lean.Level} (h : f.getAppFn = .const c us)
    (hc : specialArity σ c = none) : ¬ ShortSpine σ (.app f a) := by
  rintro ⟨c', us', ar, h1, h2, -⟩
  have h1' : f.getAppFn = .const c' us' := h1
  rw [h] at h1'
  cases h1'
  rw [hc] at h2
  cases h2

theorem ev_atom {e : Lean.Expr} (h : SrcAtom e) : SrcEval σ e e := .atom h

theorem ev_delta {c : Name} {us : List Lean.Level} {v : DefinitionVal} {r : Lean.Expr}
    (h : σ.unfold? c = some (.defnInfo v, v.value))
    (hr : SrcEval σ (Pure.instLevels v.levelParams us v.value) r) : SrcEval σ (.const c us) r :=
  .delta h hr

theorem ev_cZ : SrcEval σ cZ cZ :=
  SrcEval.ctor (c := `N.z) (us := []) (as := []) (vs := []) rfl rfl rfl (fun _ _ _ h => nomatch h)

theorem ev_mj : SrcEval σ mj mj := by
  refine SrcEval.ctor (c := `N.s) (us := []) (as := [cZ]) (vs := [cZ]) rfl rfl rfl ?_
  intro i a v h1 h2
  rcases i with _ | i <;> simp at h1 h2
  subst h1 h2
  exact ev_cZ

theorem ev_cPU (l : Lean.Level) : SrcEval σ (cPU l) (cPU l) :=
  SrcEval.ctor (c := `PUnit.unit) (us := [l]) (as := []) (vs := []) rfl rfl rfl
    (fun _ _ _ h => nomatch h)

theorem ev_tN : SrcEval σ tN tN := .constAtom (by krfl)
theorem ev_tPU (l : Lean.Level) : SrcEval σ (tPU l) (tPU l) := .constAtom (by krfl)
theorem ev_tPP (a b : Lean.Level) : SrcEval σ (tPP a b) (tPP a b) := .constAtom (by krfl)

/-- `(fun m => N) a ⇓ N`. -/
theorem ev_motN {a : Lean.Expr} (ha : SrcEval σ a a) : SrcEval σ (.app motN a) tN :=
  .beta (ns_lam rfl) (ev_atom trivial) ha ev_tN

/-- `Unit.unit ⇓ PUnit.unit.{1}` (δ). -/
theorem ev_unitU : SrcEval σ (.const `Unit.unit []) (cPU l1) :=
  ev_delta (v := Unit_unit) (by krfl) (ev_cPU l1)

/-! ### `add._f n`, applied: the match on `N.z` and on `N.s N.z` -/

/-- The motive and the alternatives of `add._f`'s match, `n := N.s N.z`. -/
def MF : Lean.Expr :=
  .lam (hyg "m" 8) tN (.forallE (hyg "x" 23) (belowN (.bvar 0)) tN .default) .default
def H1 : Lean.Expr := .lam `_ tUnit (.lam (hyg "x" 23) (belowN cZ) mj .default) .default
def H2 : Lean.Expr :=
  .lam `k tN (.lam (hyg "x" 23) (belowN (.app cS (.bvar 0))) (.app cS (.proj `PProd 0 (.bvar 0)))
    .default) .default

/-- `add.match_1 MF a H1 H2`. -/
def matchApp (a : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.const `add.match_1 [l1]) MF) a) H1) H2

/-- `add._f (N.s N.z)`'s value `fun m f => add.match_1 MF m H1 H2 f`. -/
def Fm : Lean.Expr :=
  .lam `m tN (.lam `f (belowN (.bvar 0)) (.app (matchApp (.bvar 1)) (.bvar 0)) .default) .default

/-- `add.match_1 MF a H1 H2` after δ and β: `N.casesOn (fun x => MF x) a (H1 Unit.unit)
(fun n => H2 n)`. -/
def casesApp (a : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.const `N.casesOn [l1]) (.lam `x tN (.app MF (.bvar 0)) .default)) a)
    (.app H1 (.const `Unit.unit []))) (.lam (hyg "n" 22) tN (.app H2 (.bvar 0)) .default)

theorem ev_addf : SrcEval σ (.app (.const `add._f []) mj) Fm :=
  .beta (ns_const (c := `add._f) (us := []) rfl (by krfl))
    (ev_delta (v := add_f) (by krfl) (ev_atom trivial)) ev_mj (ev_atom trivial)

/-- δ and β of `add.match_1` on the arguments `MF a H1 H2`. -/
syntax (name := _matchBeta) "match_beta" term : tactic
macro_rules
  | `(tactic| match_beta $ha:term) => `(tactic| (
  have hns : specialArity σ `add.match_1 = none := by krfl
  have h0 := ev_delta (c := `add.match_1) (us := [l1]) (v := add_match_1) (by krfl) (ev_atom trivial)
  have h1 := SrcEval.beta (ns_const rfl hns) h0 (ev_atom (e := MF) trivial) (ev_atom trivial)
  have h2 := SrcEval.beta (ns_const rfl hns) h1 $ha (ev_atom trivial)
  have h3 := SrcEval.beta (ns_const rfl hns) h2 (ev_atom (e := H1) trivial) (ev_atom trivial)
  refine SrcEval.beta (ns_const rfl hns) h3 (ev_atom (e := H2) trivial) ?_))

theorem casesOn_N : σ.casesOn? `N.casesOn = some N_ind := by krfl

theorem ev_casesZ : SrcEval σ (casesApp cZ) (.lam (hyg "x" 23) (belowN cZ) mj .default) := by
  refine SrcEval.casesIota (c := `N.casesOn) (us := [l1])
    (as := [.lam `x tN (.app MF (.bvar 0)) .default, cZ, .app H1 (.const `Unit.unit []),
      .lam (hyg "n" 22) tN (.app H2 (.bvar 0)) .default]) (i := 0) (fs := [])
    casesOn_N rfl rfl ev_cZ ⟨`N.z, [], Nz_ctor, [], rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl ?_
  exact .beta (ns_lam rfl) (ev_atom trivial) ev_unitU (ev_atom trivial)

theorem ev_casesS : SrcEval σ (casesApp mj)
    (.lam (hyg "x" 23) (belowN mj) (.app cS (.proj `PProd 0 (.bvar 0))) .default) := by
  refine SrcEval.casesIota (c := `N.casesOn) (us := [l1])
    (as := [.lam `x tN (.app MF (.bvar 0)) .default, mj, .app H1 (.const `Unit.unit []),
      .lam (hyg "n" 22) tN (.app H2 (.bvar 0)) .default]) (i := 1) (fs := [cZ])
    casesOn_N rfl rfl ev_mj ⟨`N.s, [], Ns_ctor, [], rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl ?_
  have h := SrcEval.beta (ns_lam rfl) (ev_atom (e := H2) trivial) ev_cZ (ev_atom trivial)
  exact .beta (ns_lam rfl) (ev_atom trivial) ev_cZ h

theorem ev_matchZ : SrcEval σ (matchApp cZ) (.lam (hyg "x" 23) (belowN cZ) mj .default) := by
  match_beta ev_cZ
  exact ev_casesZ

theorem ev_matchS : SrcEval σ (matchApp mj)
    (.lam (hyg "x" 23) (belowN mj) (.app cS (.proj `PProd 0 (.bvar 0))) .default) := by
  match_beta ev_mj
  exact ev_casesS

/-- `add._f (N.s N.z) N.z PUnit.unit ⇓ N.s N.z`. -/
theorem ev_FmZ : SrcEval σ (.app (.app Fm cZ) (cPU ml)) mj := by
  have h1 := SrcEval.beta (ns_lam rfl) (ev_atom (e := Fm) trivial) ev_cZ (ev_atom trivial)
  have h2 := SrcEval.beta (ns_const (c := `add.match_1) (us := [l1]) rfl (by krfl)) ev_matchZ
    (ev_cPU ml) ev_mj
  exact .beta (ns_lam rfl) h1 (ev_cPU ml) h2

/-! ### `N.below (fun m => N) N.z ⇓ PUnit` -/

/-- `PProd.{1, max 1 1} A B`, `PProd.mk.{1, max 1 1} A B a b`, `N.below.{1} (fun m => N) a`. -/
def PPl (A B : Lean.Expr) : Lean.Expr := .app (.app (tPP l1 ml) A) B
def PPmkl (A B a b : Lean.Expr) : Lean.Expr := .app (.app (.app (.app (cPP l1 ml) A) B) a) b
def belowL (a : Lean.Expr) : Lean.Expr := .app (.app (below l1) motN) a

/-- The minor of `N.s` in `N.below.{1} (fun m => N)`'s recursor. -/
def blMinL : Lean.Expr :=
  .lam `n tN (.lam `n_ih (.sort ml) (PPl (.app motN (.bvar 1)) (.bvar 0)) .default) .default

theorem ev_recBlock : σ.recBlock? N_rec = some ([N_ind], [Nz_ctor, Ns_ctor]) := by krfl

theorem ev_belowZ : SrcEval σ (belowL cZ) (tPU ml) := by
  have hns : specialArity σ `N.below = none := by krfl
  have h0 := ev_delta (c := `N.below) (us := [l1]) (v := N_below) (by krfl) (ev_atom trivial)
  have h1 := SrcEval.beta (ns_const rfl hns) h0 (ev_atom (e := motN) trivial) (ev_atom trivial)
  refine SrcEval.beta (ns_const rfl hns) h1 ev_cZ ?_
  exact SrcEval.recIota (c := `N.rec) (us := [.succ ml]) (ps := []) (ms := [.lam `t tN (.sort ml) .default])
    (mins := [tPU ml, blMinL]) (mvs := [tPU ml, blMinL]) (fs := []) (rfs := []) (ihvs := [])
    (T := `N) (iv := N_ind) (cvs := [Nz_ctor, Ns_ctor]) rfl rfl rfl ev_recBlock rfl recShape_N
    minors_shape rfl rfl rfl rfl
    (fun i m mv h1 h2 => by
      rcases i with _ | _ | i <;> simp at h1 h2 <;> subst h1 h2
      · exact ev_tPU ml
      · exact ev_atom trivial)
    ev_cZ ⟨`N.z, [], Nz_ctor, [], rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl
    (fun _ _ _ h => nomatch h) (ev_tPU ml)

theorem findDecl_PProd : findDecl σ.decls `PProd = some (.inductInfo PProd_ind) := by krfl
theorem casesOn_PProd : σ.casesOn? `PProd = none := by krfl
theorem arity_PProd : specialArity σ `PProd = none := by krfl

theorem nb_PP : ¬ BlocksCong σ (tPP l1 ml) := by
  rintro (⟨c, us, cv, h1, h2⟩ | ⟨c, us, iv, h1, h2⟩ | ⟨c, us, qv, h1, h2⟩) <;> cases h1 <;>
    simp [findDecl_PProd, casesOn_PProd] at h2

theorem nb_PP1 : ¬ BlocksCong σ (.app (tPP l1 ml) tN) := by
  rintro (⟨c, us, cv, h1, h2⟩ | ⟨c, us, iv, h1, h2⟩ | ⟨c, us, qv, h1, h2⟩) <;> cases h1 <;>
    simp [findDecl_PProd, casesOn_PProd] at h2

/-- `PProd ((fun m => N) N.z) (N.below (fun m => N) N.z) ⇓ PProd N PUnit`. -/
theorem ev_PPlZ : SrcEval σ (PPl (.app motN cZ) (belowL cZ)) (PPl tN (tPU ml)) :=
  .appCong (ns_const (c := `PProd) (us := [l1, ml]) rfl arity_PProd)
    (.appCong (ns_const (c := `PProd) (us := [l1, ml]) rfl arity_PProd) (ev_tPP l1 ml) nb_PP
      (ev_motN ev_cZ)) nb_PP1 ev_belowZ

/-! ### `N.brecOn.go (fun m => N) (N.s N.z) (add._f (N.s N.z))` -/

/-- The table on `N.z`: `⟨N.s N.z, PUnit.unit⟩ : PProd N PUnit`. -/
def zV : Lean.Expr := PPmkl tN (tPU ml) mj (cPU ml)

theorem ev_zV : SrcEval σ zV zV := by
  refine SrcEval.ctor (c := `PProd.mk) (us := [l1, ml]) (as := [tN, tPU ml, mj, cPU ml])
    (vs := [tN, tPU ml, mj, cPU ml]) rfl rfl rfl ?_
  intro i a v h1 h2
  rcases i with _ | _ | _ | _ | i <;> simp at h1 h2 <;> subst h1 h2
  · exact ev_tN
  · exact ev_tPU ml
  · exact ev_mj
  · exact ev_cPU ml

/-- `add._f (N.s N.z) (N.s N.z) ⟨N.s N.z, PUnit.unit⟩ ⇓ N.s (N.s N.z)`: the recursive call is the
first projection of the table. -/
theorem ev_FmS : SrcEval σ (.app (.app Fm mj) zV) ssz := by
  have h1 := SrcEval.beta (ns_lam rfl) (ev_atom (e := Fm) trivial) ev_mj (ev_atom trivial)
  have hp : SrcEval σ (.proj `PProd 0 zV) mj :=
    SrcEval.proj ev_zV ⟨`PProd.mk, [l1, ml], PProd_mk, [tN, tPU ml], rfl, rfl, rfl, rfl, rfl, rfl⟩
      (fs := [mj, cPU ml]) rfl
  have hs : SrcEval σ (.app cS (.proj `PProd 0 zV)) ssz := by
    refine SrcEval.ctor (c := `N.s) (us := []) (as := [.proj `PProd 0 zV]) (vs := [mj]) rfl rfl rfl
      ?_
    intro i a v h1 h2
    rcases i with _ | i <;> simp at h1 h2
    subst h1 h2
    exact hp
  have h2 := SrcEval.beta (ns_const (c := `add.match_1) (us := [l1]) rfl (by krfl)) ev_matchS
    ev_zV hs
  exact .beta (ns_lam rfl) h1 ev_zV h2

/-- The motive and minor premises of `N.brecOn.go (fun m => N) (N.s N.z) (add._f (N.s N.z))`'s
recursor. -/
def Mg : Lean.Expr := .lam `t tN (PPl (.app motN (.bvar 0)) (belowL (.bvar 0))) .default
def zMing : Lean.Expr := PPmkl (.app motN cZ) (tPU ml) (.app (.app Fm cZ) (cPU ml)) (cPU ml)
def sMing : Lean.Expr :=
  .lam `n tN (.lam `n_ih (PPl (.app motN (.bvar 0)) (belowL (.bvar 0)))
    (PPmkl (.app motN (.app cS (.bvar 1))) (PPl (.app motN (.bvar 1)) (belowL (.bvar 1)))
      (.app (.app Fm (.app cS (.bvar 1))) (.bvar 0)) (.bvar 0)) .default) .default

/-- The pair on `N.s N.z`: `⟨N.s (N.s N.z), ⟨N.s N.z, PUnit.unit⟩⟩`. -/
def sV : Lean.Expr := PPmkl tN (PPl tN (tPU ml)) ssz zV

theorem ev_zMin : SrcEval σ zMing zV := by
  refine SrcEval.ctor (c := `PProd.mk) (us := [l1, ml])
    (as := [.app motN cZ, tPU ml, .app (.app Fm cZ) (cPU ml), cPU ml])
    (vs := [tN, tPU ml, mj, cPU ml]) rfl rfl rfl ?_
  intro i a v h1 h2
  rcases i with _ | _ | _ | _ | i <;> simp at h1 h2 <;> subst h1 h2
  · exact ev_motN ev_cZ
  · exact ev_tPU ml
  · exact ev_FmZ
  · exact ev_cPU ml

theorem ev_minsGo : ∀ (i : Nat) m mv, [zMing, sMing][i]? = some m → [zV, sMing][i]? = some mv →
    SrcEval σ m mv := by
  intro i m mv h1 h2
  rcases i with _ | _ | i <;> simp at h1 h2 <;> subst h1 h2
  · exact ev_zMin
  · exact ev_atom trivial

theorem ev_minsGo' : ∀ (i : Nat) m mv, [zV, sMing][i]? = some m → [zV, sMing][i]? = some mv →
    SrcEval σ m mv := by
  intro i m mv h1 h2
  rcases i with _ | _ | i <;> simp at h1 h2 <;> subst h1 h2
  · exact ev_zV
  · exact ev_atom trivial

/-- The induction hypothesis: the recursor's ι on `N.z`. -/
theorem ev_ihGo : SrcEval σ (mkAppN (.const `N.rec [ml]) ([] ++ [Mg] ++ [zV, sMing] ++ [cZ]).toArray)
    zV :=
  SrcEval.recIota (ps := []) (ms := [Mg]) (mins := [zV, sMing]) (mvs := [zV, sMing]) (fs := [])
    (rfs := []) (ihvs := []) (T := `N) (iv := N_ind) (cvs := [Nz_ctor, Ns_ctor]) rfl rfl rfl
    ev_recBlock rfl recShape_N minors_shape rfl rfl rfl rfl ev_minsGo' ev_cZ
    ⟨`N.z, [], Nz_ctor, [], rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl
    (fun _ _ _ h => nomatch h) ev_zV

/-- The minor of `N.s` on the field `N.z` and the table `⟨N.s N.z, PUnit.unit⟩`. -/
theorem ev_sMin : SrcEval σ (mkAppN sMing ([cZ] ++ [zV]).toArray) sV := by
  have h1 := SrcEval.beta (ns_lam rfl) (ev_atom (e := sMing) trivial) ev_cZ (ev_atom trivial)
  refine SrcEval.beta (ns_lam rfl) h1 ev_zV ?_
  refine SrcEval.ctor (c := `PProd.mk) (us := [l1, ml])
    (as := [.app motN mj, PPl (.app motN cZ) (belowL cZ), .app (.app Fm mj) zV, zV])
    (vs := [tN, PPl tN (tPU ml), ssz, zV]) rfl rfl rfl ?_
  intro i a v h1 h2
  rcases i with _ | _ | _ | _ | i <;> simp at h1 h2 <;> subst h1 h2
  · exact ev_motN ev_mj
  · exact ev_PPlZ
  · exact ev_FmS
  · exact ev_zV

/-- The recursor's ι on `N.s N.z`. -/
theorem ev_goRec : SrcEval σ (mkAppN (.const `N.rec [ml]) ([] ++ [Mg] ++ [zMing, sMing] ++ [mj]).toArray)
    sV :=
  SrcEval.recIota (ps := []) (ms := [Mg]) (mins := [zMing, sMing]) (mvs := [zV, sMing])
    (fs := [cZ]) (rfs := [cZ]) (ihvs := [zV]) (T := `N) (iv := N_ind) (cvs := [Nz_ctor, Ns_ctor])
    rfl rfl rfl ev_recBlock rfl recShape_N minors_shape rfl rfl rfl rfl ev_minsGo ev_mj
    ⟨`N.s, [], Ns_ctor, [], rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl
    (fun i f w h1 h2 => by
      rcases i with _ | i <;> simp at h1 h2
      subst h1 h2
      exact ev_ihGo)
    ev_sMin

theorem ev_go : SrcEval σ (.app (.app (.app (.const `N.brecOn.go [l1]) motN) mj) Fm) sV := by
  have hns : specialArity σ `N.brecOn.go = none := by krfl
  have h0 := ev_delta (c := `N.brecOn.go) (us := [l1]) (v := N_brecOn_go) (by krfl) (ev_atom trivial)
  have h1 := SrcEval.beta (ns_const rfl hns) h0 (ev_atom (e := motN) trivial) (ev_atom trivial)
  have h2 := SrcEval.beta (ns_const rfl hns) h1 ev_mj (ev_atom trivial)
  exact SrcEval.beta (ns_const rfl hns) h2 (ev_atom (e := Fm) trivial) ev_goRec

/-! ### `add (N.s N.z) (N.s N.z) ⇓ N.s (N.s N.z)` -/

theorem ev_brecOn : SrcEval σ (.app (.app (.app (.const `N.brecOn [l1]) motN) mj)
    (.app (.const `add._f []) mj)) ssz := by
  have hns : specialArity σ `N.brecOn = none := by krfl
  have h0 := ev_delta (c := `N.brecOn) (us := [l1]) (v := N_brecOn) (by krfl) (ev_atom trivial)
  have h1 := SrcEval.beta (ns_const rfl hns) h0 (ev_atom (e := motN) trivial) (ev_atom trivial)
  have h2 := SrcEval.beta (ns_const rfl hns) h1 ev_mj (ev_atom trivial)
  exact SrcEval.beta (ns_const rfl hns) h2 ev_addf
    (SrcEval.proj ev_go ⟨`PProd.mk, [l1, ml], PProd_mk, [tN, PPl tN (tPU ml)], rfl, rfl, rfl, rfl,
      rfl, rfl⟩ (fs := [ssz, zV]) rfl)

/-- `hev`: `e` evaluates to `N.s (N.s N.z)`. -/
theorem hev : SrcEval σ e ssz := by
  have hns : specialArity σ `add = none := by krfl
  have h0 := ev_delta (c := `add) (us := []) (v := add_def) (by krfl) (ev_atom trivial)
  have h1 := SrcEval.beta (ns_const rfl hns) h0 ev_mj (ev_atom trivial)
  exact SrcEval.beta (ns_const rfl hns) h1 ev_mj ev_brecOn

/-! ## The final theorem on NV-S -/

/-- The final theorem on NV-S: the program `#erase` emits for `add (N.s N.z) (N.s N.z)`, `add`
defined by structural recursion and erased under `structural := .kernel`, is an untyped λ□ program
whose main term evaluates to an erasure of `N.s (N.s N.z)`, and `N.s (N.s N.z)` translates to a
term definitionally equal to the input's at each of its types. -/
theorem final :
    ∃ lenv tb vb, p0 = .untyped lenv (some tb) ∧
      Erases E B [] (evalEnvOf view cfg P) .nil [] ssz vb ∧ LBEval defaultFlags lenv tb vb ∧
      ∀ T, E[.nil] ⊢ tE : T → ∃ t', TrM E B [] .nil [] ssz t' ∧ E[.nil] ⊢ tE ≡ t' : T :=
  erase_correct henv hwf hview he hty hfrag hrun hev

/-- `N.s (N.s N.z)` is a first-order value: constructors of `N : Type` applied to first-order
values. -/
theorem fo_ssz : FirstOrderValue σ ssz := by
  have hz : FirstOrderValue σ cZ :=
    FirstOrderValue.ctor (c := `N.z) (us := []) (as := []) (n := 0) (u := .succ .zero) rfl rfl rfl
      rfl rfl (fun _ h => nomatch h)
  have hs : FirstOrderValue σ mj :=
    FirstOrderValue.ctor (c := `N.s) (us := []) (as := [cZ]) (n := 0) (u := .succ .zero) rfl rfl
      rfl rfl rfl (fun a h => by simp at h; subst h; exact hz)
  exact FirstOrderValue.ctor (c := `N.s) (us := []) (as := [mj]) (n := 0) (u := .succ .zero) rfl
    rfl rfl rfl rfl (fun a h => by simp at h; subst h; exact hs)

/-- The final theorem on first-order values on NV-S: the main term of the program `#erase` emits
evaluates in λ□ to `N.s (N.s N.z)`'s structural erasure, the constructor `1` of `N`'s block applied
to the constructor `1` applied to the constructor `0`. -/
theorem firstorder :
    ∃ lenv tb, p0 = .untyped lenv (some tb) ∧ LBEval defaultFlags lenv tb
      (.app (.construct iidN 1 []) (.app (.construct iidN 1 []) (.construct iidN 0 []))) :=
  erase_correct_firstorder henv hwf hview he hty hfrag hrun hev fo_ssz

end EraseProof.Test.NVS
