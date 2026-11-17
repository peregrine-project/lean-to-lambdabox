import EraseProof.Test.NVSUModel
import EraseProof.Test.NVSFinal

/-!
# NV-SU: the source evaluation

`hev`: the term `e = add (N.s N.z) (N.s N.z)` of NV-SU (`Test/NVSUData.lean`) evaluates to
`N.s (N.s N.z)` at `σSU := evalEnvOf view cfgSU P`, under the conversion premise `SrcConv E B []`
of the statements. Under `cfgSU`, `add` has no δ: `SrcEval.deltaRec` evaluates `add a b` by
evaluating `a`, `b` to `va`, `vb` and then `preVal va vb`, given `add va vb ≡ preVal va vb`
(`deltaRec_add`). `preVal (N.s N.z) b` (`evU_pre_of`) is the match `add.match_1` (δ, four β), a
`N.casesOn` on `b` (`SrcEval.casesIota`): on `N.z` the first alternative returns `N.s N.z`, its
argument `Unit.unit` evaluated (δ); on `N.s N.z` the second applies `N.s` to the recursive call
`add (N.s N.z) N.z`, again by `deltaRec`. The conversion at each of the two calls (`conv_add`) is
subject reduction (`SrcEval.defeq`) on two evaluations to the same value: NV-S's, at the kernel
definition of `add` (`structural := .kernel`; `NVS.hev` and `ev_kernelZ`), and the pre-definition's;
the two translations of the value are congruent (`TrM.dcong`).
-/

open Lean Erasure Metalean

namespace EraseProof.Test.NVSU

open EraseProof.Test.NVR (tN cZ cS N_ind Nz_ctor Ns_ctor mj recShape_N minors_shape mZ mS mN
  mZ_typed mS_typed tr_Z tr_S)
open EraseProof.Test.NVS (P e view add_def add_match_1 Unit_unit N_brecOn N_brecOn_go PProd_mk
  hyg tUnit l1 u1 cPU tPU motN σ ml ssz zV Fm Mg zMing sMing ev_delta ev_atom ev_cZ ev_mj ns_const
  ev_addf ev_recBlock ev_minsGo ev_zV E B henv hwf hview n12 ζ12 B12_z B12_s mjM t_n12 addTyM)
open EraseProof.Test.NV1 (typed_of_eq)
open EraseProof.Test.NVS (app_typed')

/-- The evaluation environment of NV-SU. -/
abbrev σSU : EvalEnv := evalEnvOf view cfgSU P

/-- The conversion premise of the statements. -/
abbrev CU : Lean.Expr → Lean.Expr → Prop := SrcConv E B []

/-! ## The kernel definition of `add` at NV-S's environment, on `N.z` -/

/-- The recursor of `N.brecOn.go` on `N.z`. -/
theorem ev_recZ {C : Lean.Expr → Lean.Expr → Prop} :
    SrcEval σ C (mkAppN (.const `N.rec [ml]) ([] ++ [Mg] ++ [zMing, sMing] ++ [cZ]).toArray) zV :=
  SrcEval.recIota (ps := []) (ms := [Mg]) (mins := [zMing, sMing]) (mvs := [zV, sMing]) (fs := [])
    (rfs := []) (ihvs := []) (T := `N) (iv := N_ind) (cvs := [Nz_ctor, Ns_ctor]) rfl rfl rfl
    ev_recBlock rfl recShape_N minors_shape rfl rfl rfl rfl ev_minsGo ev_cZ
    ⟨`N.z, [], Nz_ctor, [], rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl
    (fun _ _ _ h => nomatch h) ev_zV

theorem ev_goZ {C : Lean.Expr → Lean.Expr → Prop} :
    SrcEval σ C (.app (.app (.app (.const `N.brecOn.go [l1]) motN) cZ) Fm) zV := by
  have hns : specialArity σ `N.brecOn.go = none := by krfl
  have h0 := ev_delta (C := C) (c := `N.brecOn.go) (us := [l1]) (v := N_brecOn_go) (by krfl)
    (ev_atom trivial)
  have h1 := SrcEval.beta (ns_const rfl hns) h0 (ev_atom (e := motN) trivial) (ev_atom trivial)
  have h2 := SrcEval.beta (ns_const rfl hns) h1 ev_cZ (ev_atom trivial)
  exact SrcEval.beta (ns_const rfl hns) h2 (ev_atom (e := Fm) trivial) ev_recZ

theorem ev_brecOnZ {C : Lean.Expr → Lean.Expr → Prop} :
    SrcEval σ C (.app (.app (.app (.const `N.brecOn [l1]) motN) cZ)
      (.app (.const `add._f []) mj)) mj := by
  have hns : specialArity σ `N.brecOn = none := by krfl
  have h0 := ev_delta (C := C) (c := `N.brecOn) (us := [l1]) (v := N_brecOn) (by krfl)
    (ev_atom trivial)
  have h1 := SrcEval.beta (ns_const rfl hns) h0 (ev_atom (e := motN) trivial) (ev_atom trivial)
  have h2 := SrcEval.beta (ns_const rfl hns) h1 ev_cZ (ev_atom trivial)
  exact SrcEval.beta (ns_const rfl hns) h2 ev_addf
    (SrcEval.proj ev_goZ ⟨`PProd.mk, [l1, ml], PProd_mk, [tN, tPU ml], rfl, rfl, rfl, rfl, rfl,
      rfl⟩ (fs := [mj, cPU ml]) rfl)

/-- `add (N.s N.z) N.z ⇓ N.s N.z` at NV-S's environment, through `add`'s kernel definition (δ). -/
theorem ev_kernelZ {C : Lean.Expr → Lean.Expr → Prop} :
    SrcEval σ C (.app (.app (.const `add []) mj) cZ) mj := by
  have hns : specialArity σ `add = none := by krfl
  have h0 := ev_delta (C := C) (c := `add) (us := []) (v := add_def) (by krfl) (ev_atom trivial)
  have h1 := SrcEval.beta (ns_const rfl hns) h0 ev_mj (ev_atom trivial)
  exact SrcEval.beta (ns_const rfl hns) h1 ev_cZ ev_brecOnZ

/-! ## Steps at `σSU` -/

theorem nsU_lam {f a : Lean.Expr} {n : Name} {A b : Lean.Expr} {bi : BinderInfo}
    (h : f.getAppFn = .lam n A b bi) : ¬ ShortSpine σSU (.app f a) := by
  rintro ⟨c, us, ar, h1, -⟩
  have h1' : f.getAppFn = .const c us := h1
  rw [h] at h1'
  cases h1'

theorem nsU_const {f a : Lean.Expr} {c : Name} {us : List Level} (h : f.getAppFn = .const c us)
    (hc : specialArity σSU c = none) : ¬ ShortSpine σSU (.app f a) := by
  rintro ⟨c', us', ar, h1, h2, -⟩
  have h1' : f.getAppFn = .const c' us' := h1
  rw [h] at h1'
  cases h1'
  rw [hc] at h2
  cases h2

theorem evU_delta {c : Name} {us : List Level} {v : DefinitionVal} {r : Lean.Expr}
    (h : σSU.unfold? c = some (.defnInfo v, v.value))
    (hr : SrcEval σSU CU (Pure.instLevels v.levelParams us v.value) r) :
    SrcEval σSU CU (.const c us) r :=
  .delta h hr

theorem evU_cZ : SrcEval σSU CU cZ cZ :=
  SrcEval.ctor (c := `N.z) (us := []) (as := []) (vs := []) rfl rfl rfl (fun _ _ _ h => nomatch h)

/-- `N.s a ⇓ N.s v` when `a ⇓ v`. -/
theorem evU_succ {a v : Lean.Expr} (h : SrcEval σSU CU a v) :
    SrcEval σSU CU (.app cS a) (.app cS v) := by
  refine SrcEval.ctor (c := `N.s) (us := []) (as := [a]) (vs := [v]) rfl rfl rfl ?_
  intro i x y h1 h2
  rcases i with _ | i <;> simp at h1 h2
  subst h1 h2
  exact h

theorem evU_mj : SrcEval σSU CU mj mj := evU_succ evU_cZ

/-- `Unit.unit ⇓ PUnit.unit.{1}` (δ). -/
theorem evU_unitU : SrcEval σSU CU (.const `Unit.unit []) (cPU l1) :=
  evU_delta (v := Unit_unit) (by krfl)
    (SrcEval.ctor (c := `PUnit.unit) (us := [l1]) (as := []) (vs := []) rfl rfl rfl
      (fun _ _ _ h => nomatch h))

/-! ## `deltaRec` on `add` -/

theorem find_add : findDecl σSU.decls `add = some (.defnInfo add_def) := by krfl
theorem casesOn_add : σSU.casesOn? `add = none := by krfl
theorem atom_add : σSU.isAtom `add = false := by krfl
theorem ax_add : σSU.axiomatized (.defnInfo add_def) = false := by krfl
theorem pre_add : σSU.recPre? (.defnInfo add_def) = some preVal := preDef_add
theorem arity_pre : lamArity preVal = 2 := by krfl
theorem inst_pre : Pure.instLevels [] [] preVal = preVal := by krfl

theorem mkAppN_two (f a b : Lean.Expr) : mkAppN f [a, b].toArray = .app (.app f a) b := rfl

/-- `add a b ⇓ v` at `σSU` (`SrcEval.deltaRec`): `a ⇓ va`, `b ⇓ vb`, the conversion
`add va vb ≡ preVal va vb`, and `preVal va vb ⇓ v`. Reference: none (DV-7). -/
theorem deltaRec_add {a b va vb v : Lean.Expr} (ha : SrcEval σSU CU a va)
    (hb : SrcEval σSU CU b vb)
    (hc : CU (.app (.app (.const `add []) va) vb) (.app (.app preVal va) vb))
    (hp : SrcEval σSU CU (.app (.app preVal va) vb) v) :
    SrcEval σSU CU (.app (.app (.const `add []) a) b) v := by
  have hlp : (ConstantInfo.defnInfo add_def).levelParams = [] := rfl
  have hc' : CU (mkAppN (.const `add []) [va, vb].toArray)
      (mkAppN (Pure.instLevels (ConstantInfo.defnInfo add_def).levelParams [] preVal)
        [va, vb].toArray) := by
    rw [hlp, inst_pre, mkAppN_two, mkAppN_two]; exact hc
  have hp' : SrcEval σSU CU (mkAppN (Pure.instLevels (ConstantInfo.defnInfo add_def).levelParams []
      preVal) [va, vb].toArray) v := by
    rw [hlp, inst_pre, mkAppN_two]; exact hp
  have hargs : ∀ (i : Nat) x y, [a, b][i]? = some x → [va, vb][i]? = some y →
      SrcEval σSU CU x y := by
    intro i x y h1 h2
    rcases i with _ | _ | i <;> simp at h1 h2 <;> subst h1 h2
    · exact ha
    · exact hb
  have h := SrcEval.deltaRec (σ := σSU) (C := CU) (c := `add) (us := [])
    (ci := .defnInfo add_def) (pre := preVal) (as := [a, b]) (vs := [va, vb]) find_add rfl
    casesOn_add atom_add ax_add pre_add (by rw [arity_pre]; decide) (by rw [arity_pre]; rfl) rfl
    hargs hc' hp'
  rwa [mkAppN_two] at h

/-! ## The pre-definition at `σSU`, on the first argument `N.s N.z` -/

/-- The second alternative of the pre-definition's match at `n := N.s N.z`. -/
def altM2 : Lean.Expr :=
  .lam `k tN (.app cS (.app (.app (.const `add []) mj) (.bvar 0))) .default

/-- `add.match_1.{1} (fun m => N) b (fun _ => N.s N.z) (fun k => N.s (add (N.s N.z) k))` -/
def m4 (b : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.const `add.match_1 [l1]) motPre) b) (.lam `_ tUnit mj .default)) altM2

/-- The arguments of `N.casesOn` in `m4 b` after δ and β. -/
def casesArgsP (b : Lean.Expr) : List Lean.Expr :=
  [.lam `x tN (.app motPre (.bvar 0)) .default, b,
    .app (.lam `_ tUnit mj .default) (.const `Unit.unit []),
    .lam (hyg "n" 22) tN (.app altM2 (.bvar 0)) .default]

theorem casesOn_N : σSU.casesOn? `N.casesOn = some N_ind := by krfl

/-- δ and the four β of `add.match_1` on `motPre b (fun _ => N.s N.z) altM2`, `b` a value. -/
theorem evU_m4 {b v : Lean.Expr} (hb : SrcEval σSU CU b b)
    (hl : ∀ s d, b.liftLooseBVars' s d = b) (hi : ∀ a d, b.instantiate1' a d = b)
    (h : SrcEval σSU CU (mkAppN (.const `N.casesOn [l1]) (casesArgsP b).toArray) v) :
    SrcEval σSU CU (m4 b) v := by
  have hns : specialArity σSU `add.match_1 = none := by krfl
  have h0 := evU_delta (c := `add.match_1) (us := [l1]) (v := add_match_1) (by krfl)
    (.atom trivial)
  have h1 := SrcEval.beta (nsU_const rfl hns) h0 (.atom (e := motPre) trivial) (.atom trivial)
  have h2 := SrcEval.beta (nsU_const rfl hns) h1 hb (.atom trivial)
  have h3 := SrcEval.beta (nsU_const rfl hns) h2 (.atom (e := .lam `_ tUnit mj .default) trivial)
    (.atom trivial)
  refine SrcEval.beta (nsU_const rfl hns) h3 (.atom (e := altM2) trivial) ?_
  convert h using 1
  simp +decide only [Pure.instLevels, Lean.Expr.instantiate1', Lean.Expr.liftLooseBVars', motPre,
    altM2, casesArgsP, mkAppN, tN, cS, mj, cZ, tUnit, ↓reduceIte, add_match_1,
    EraseProof.Test.NVS.matchVal, hl, hi]
  rfl

/-- The match on `N.z`: the first alternative, `N.s N.z`. -/
theorem evU_m4Z : SrcEval σSU CU (m4 cZ) mj := by
  refine evU_m4 evU_cZ (fun _ _ => rfl) (fun _ _ => rfl) (SrcEval.casesIota (c := `N.casesOn) (us := [l1])
    (as := casesArgsP cZ) (i := 0) (fs := []) casesOn_N rfl rfl evU_cZ
    ⟨`N.z, [], Nz_ctor, [], rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl ?_)
  exact .beta (nsU_lam rfl) (.atom trivial) evU_unitU evU_mj

/-- The match on `N.s N.z`: the second alternative, `N.s (add (N.s N.z) N.z)`. -/
theorem evU_m4S {w : Lean.Expr} (hrec : SrcEval σSU CU (.app (.app (.const `add []) mj) cZ) w) :
    SrcEval σSU CU (m4 mj) (.app cS w) := by
  refine evU_m4 evU_mj (fun _ _ => rfl) (fun _ _ => rfl) (SrcEval.casesIota (c := `N.casesOn) (us := [l1])
    (as := casesArgsP mj) (i := 1) (fs := [cZ]) casesOn_N rfl rfl evU_mj
    ⟨`N.s, [], Ns_ctor, [], rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl ?_)
  have h1 : SrcEval σSU CU (.app altM2 cZ) (.app cS w) :=
    .beta (nsU_lam rfl) (.atom trivial) evU_cZ (by
      convert evU_succ hrec using 1
      simp [Lean.Expr.instantiate1', Lean.Expr.liftLooseBVars', cS, mj, cZ])
  exact .beta (nsU_lam rfl) (.atom trivial) evU_cZ (by
    convert h1 using 1
    simp [Lean.Expr.instantiate1', Lean.Expr.liftLooseBVars', altM2, tN, cS, mj, cZ])

/-- `preVal (N.s N.z) b ⇓ v` when its match on the value `b` evaluates to `v`: two β. -/
theorem evU_pre_of {b v : Lean.Expr} (hb : SrcEval σSU CU b b)
    (hl : ∀ s d, b.liftLooseBVars' s d = b) (hm : SrcEval σSU CU (m4 b) v) :
    SrcEval σSU CU (.app (.app preVal mj) b) v := by
  have h1 : SrcEval σSU CU (.app preVal mj) (.lam `m tN
      (.app (.app (.app (.app (.const `add.match_1 [l1]) motPre) (.bvar 0))
        (.lam `_ tUnit mj .default)) altM2) .default) :=
    .beta (nsU_lam rfl) (.atom trivial) evU_mj (by
      convert SrcEval.atom (σ := σSU) (C := CU) (e := .lam `m tN
        (.app (.app (.app (.app (.const `add.match_1 [l1]) motPre) (.bvar 0))
          (.lam `_ tUnit mj .default)) altM2) .default) trivial using 1
      simp +decide [Lean.Expr.instantiate1', Lean.Expr.liftLooseBVars', motPre, altPre1, altPre2,
        altM2, tN, cS, mj, cZ, tUnit])
  refine .beta (nsU_lam rfl) h1 hb ?_
  convert hm using 1
  simp +decide [Lean.Expr.instantiate1', motPre, altM2, m4, tN, cS, mj, cZ, tUnit, hl]

/-! ## The conversion premises -/

theorem subU : SubEnv σSU.decls P := fun _ => CollectSub.findDecl_of_view hview
theorem subS : SubEnv σ.decls P := fun _ => CollectSub.findDecl_of_view hview

/-- The conversion premise of `deltaRec` at a call `add a b`, `a` and `b` with typed translations
`aM`, `bM`, given the kernel evaluation `hk` of `add a b` at NV-S's environment and the evaluation
`hp` of `preVal a b` at `σSU`, to the same value: every typed translation of `add a b` is
definitionally equal, at its type, to `preValM aM bM`. Subject reduction (`SrcEval.defeq`) on `hk`
and `hp` gives two translations of the value, which are congruent (`TrM.dcong`,
`DCong.defeq₂`). Reference: the conclusion of `subject_reduction_eval`
(`MR P/PCUICWcbvEval.v`). -/
theorem conv_add {a b v : Lean.Expr} {aM bM : Metalean.Expr ζ12 0 0}
    (ha : TrM E B [] .nil [] a aM) (hb : TrM E B [] .nil [] b bM)
    (haT : E[.nil] ⊢ aM : mN n12) (hbT : E[.nil] ⊢ bM : mN n12)
    (hk : SrcEval σ CU (.app (.app (.const `add []) a) b) v)
    (hp : SrcEval σSU CU (.app (.app preVal a) b) v) :
    CU (.app (.app (.const `add []) a) b) (.app (.app preVal a) b) := by
  intro t T ht hT
  have htp : TrM E B [] .nil [] (.app (.app preVal a) b) (.app (.app preValM aM) bM) :=
    TrM.app (by rintro ⟨c, us, b, h, -⟩; cases h)
      (TrM.app (by rintro ⟨c, us, b, h, -⟩; cases h) tr_preVal ha) hb
  have hTp : E[.nil] ⊢ .app (.app preValM aM) bM : mN n12 := by
    have h1 := app_typed' preValM_typed haT (by rsx [addTyM])
    rsx at h1
    exact typed_of_eq (app_typed' h1 hbT (by rsx)) (by rsx)
  obtain ⟨w, hw, hd⟩ := SrcEval.defeq henv hwf subS ht hT hk
  obtain ⟨w', hw', hd'⟩ := SrcEval.defeq henv hwf subU htp hTp hp
  have hww := (TrM.dcong hw hw' (LocCong.refl [])).defeq₂ hwf SrcDefeq.nil_ok SrcDefeq.nil_ok
    (DCong.CtxConv.refl SrcDefeq.nil_ok) ⟨_, hd'.right⟩ hd.right
  exact ⟨_, htp, SrcDefeq.dtrans hwf hd (SrcDefeq.dtrans hwf hww hd'.symm)⟩

theorem tr_mj : TrM E B [] .nil [] mj mjM := tr_S B12_s (tr_Z B12_z)
theorem tr_z : TrM E B [] .nil [] cZ (mZ n12) := tr_Z B12_z
theorem mjM_typed : E[.nil] ⊢ (mjM : Metalean.Expr ζ12 0 0) : mN n12 :=
  mS_typed t_n12 (mZ_typed t_n12)

/-! ## The calls and the term -/

/-- `preVal (N.s N.z) N.z ⇓ N.s N.z` at `σSU`. -/
theorem ev_preZ : SrcEval σSU CU (.app (.app preVal mj) cZ) mj := evU_pre_of evU_cZ (fun _ _ => rfl) evU_m4Z

/-- The inner call `add (N.s N.z) N.z ⇓ N.s N.z` at `σSU`, through `deltaRec`. -/
theorem ev_addZ : SrcEval σSU CU (.app (.app (.const `add []) mj) cZ) mj :=
  deltaRec_add evU_mj evU_cZ
    (conv_add tr_mj tr_z mjM_typed (mZ_typed t_n12) ev_kernelZ ev_preZ) ev_preZ

/-- `preVal (N.s N.z) (N.s N.z) ⇓ N.s (N.s N.z)` at `σSU`. -/
theorem ev_preS : SrcEval σSU CU (.app (.app preVal mj) mj) ssz := evU_pre_of evU_mj (fun _ _ => rfl) (evU_m4S ev_addZ)

/-- `hev`: `e = add (N.s N.z) (N.s N.z)` evaluates to `N.s (N.s N.z)` at `σSU`, through
`deltaRec`. -/
theorem hev : SrcEval σSU CU e ssz :=
  deltaRec_add evU_mj evU_mj (conv_add tr_mj tr_mj mjM_typed mjM_typed EraseProof.Test.NVS.hev ev_preS)
    ev_preS

end EraseProof.Test.NVSU
