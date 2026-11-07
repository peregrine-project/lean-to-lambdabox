import EraseProof.Test.NVSFuns

/-!
# NV-S: the Metalean model of the program

The premises of the final theorem about the program and its model, for NV-S (`Test/NVSData.lean`):
the program `P` is the Lean form of the well-formed Metalean environment `E12` with name table
`B12` (`henv`, `hwf`), and the erased term `e` is the Lean form of the closed Metalean term `tE`,
which is typed (`he`, `hty`). The environment holds, oldest first, the blocks of `PUnit`, the
definitions `Unit` and `Unit.unit`, the blocks of `PProd` and `N`, and the definitions
`N.casesOn`, `N.below`, `N.brecOn.go`, `N.brecOn`, `add.match_1`, `add._f` and `add`, whose values
are typed by `Test/NVSDefs.lean` and `Test/NVSFuns.lean`.
-/

open Lean Metalean

namespace EraseProof.Test.NVS

open EraseProof.Test.NV1 (typed_of_eq var_of_get app_typed const_typed fin0_eq lu notSpecial_bvar
  notSpecial_const trLevels_nil)
open EraseProof.Test.NVP (trLevels_one trLevels_two)
open EraseProof.Test.NVR (nSig nBlock mN mZ mS mN_typed mZ_typed mS_typed indN_typed recAllowedN
  appMotN_typed motN_typed nBlock_wf tN cZ cS N_ind Nz_ctor Ns_ctor N_rec mj tr_N tr_Z tr_S sTy recTy
  sTyM sTermM recTyM recTermM ordersN ctorTerm_eqN recrTerm_eqN sTermM_typed largeElimN
  recTermM_typed IsN CsN RsN PN_eq)

/-! ## The environments -/

abbrev ζ1 : Sigs := Sigs.nil.snoc (.inductive puSig)
abbrev ζ2 : Sigs := ζ1.snoc (.const .def 0)
abbrev ζ3 : Sigs := ζ2.snoc (.const .def 0)
abbrev ζ4 : Sigs := ζ3.snoc (.inductive ppSig)
abbrev ζ5 : Sigs := ζ4.snoc (.inductive nSig)
abbrev ζ6 : Sigs := ζ5.snoc (.const .def 1)
abbrev ζ7 : Sigs := ζ6.snoc (.const .def 1)
abbrev ζ8 : Sigs := ζ7.snoc (.const .def 1)
abbrev ζ9 : Sigs := ζ8.snoc (.const .def 1)
abbrev ζ10 : Sigs := ζ9.snoc (.const .def 1)
abbrev ζ11 : Sigs := ζ10.snoc (.const .def 0)
abbrev ζ12 : Sigs := ζ11.snoc (.const .def 0)

abbrev pu1 : Head ζ1 (.inductive puSig) := .here

abbrev pu2 : Head ζ2 (.inductive puSig) := .there .here
abbrev u2 : Head ζ2 (.const .def 0) := .here


abbrev pp4 : Head ζ4 (.inductive ppSig) := .here

abbrev n5 : Head ζ5 (.inductive nSig) := .here

abbrev pu6 : Head ζ6 (.inductive puSig) := .there (.there (.there (.there (.there .here))))
abbrev pp6 : Head ζ6 (.inductive ppSig) := .there (.there .here)
abbrev n6 : Head ζ6 (.inductive nSig) := .there .here

abbrev pu7 : Head ζ7 (.inductive puSig) := .there (.there (.there (.there (.there (.there .here)))))
abbrev pp7 : Head ζ7 (.inductive ppSig) := .there (.there (.there .here))
abbrev n7 : Head ζ7 (.inductive nSig) := .there (.there .here)
abbrev bl7 : Head ζ7 (.const .def 1) := .here

abbrev pp8 : Head ζ8 (.inductive ppSig) := .there (.there (.there (.there .here)))
abbrev n8 : Head ζ8 (.inductive nSig) := .there (.there (.there .here))
abbrev bl8 : Head ζ8 (.const .def 1) := .there .here
abbrev go8 : Head ζ8 (.const .def 1) := .here

abbrev u9 : Head ζ9 (.const .def 0) := .there (.there (.there (.there (.there (.there (.there .here))))))
abbrev uu9 : Head ζ9 (.const .def 0) := .there (.there (.there (.there (.there (.there .here)))))
abbrev n9 : Head ζ9 (.inductive nSig) := .there (.there (.there (.there .here)))
abbrev c9 : Head ζ9 (.const .def 1) := .there (.there (.there .here))

abbrev pu10 : Head ζ10 (.inductive puSig) := .there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
abbrev u10 : Head ζ10 (.const .def 0) := .there (.there (.there (.there (.there (.there (.there (.there .here)))))))
abbrev pp10 : Head ζ10 (.inductive ppSig) := .there (.there (.there (.there (.there (.there .here)))))
abbrev n10 : Head ζ10 (.inductive nSig) := .there (.there (.there (.there (.there .here))))
abbrev bl10 : Head ζ10 (.const .def 1) := .there (.there (.there .here))
abbrev m10 : Head ζ10 (.const .def 1) := .here

abbrev n11 : Head ζ11 (.inductive nSig) := .there (.there (.there (.there (.there (.there .here)))))
abbrev bl11 : Head ζ11 (.const .def 1) := .there (.there (.there (.there .here)))
abbrev br11 : Head ζ11 (.const .def 1) := .there (.there .here)
abbrev f11 : Head ζ11 (.const .def 0) := .here

abbrev n12 : Head ζ12 (.inductive nSig) := .there (.there (.there (.there (.there (.there (.there .here))))))
abbrev a12 : Head ζ12 (.const .def 0) := .here
def E1 : Env ζ1 := Env.nil.snoc (.inductive puBlock)
def E2 : Env ζ2 := E1.snoc (.def (.sort one) (mPU pu1 one))
def E3 : Env ζ3 := E2.snoc (.def (unitM u2) (mPUu pu2 one))
def E4 : Env ζ4 := E3.snoc (.inductive ppBlock)
def E5 : Env ζ5 := E4.snoc (.inductive nBlock)
def E6 : Env ζ6 := E5.snoc (.def (casesOnTyM n5) (casesOnValM n5))
def E7 : Env ζ7 := E6.snoc (.def (belowTyM n6) (belowValM pu6 pp6 n6))
def E8 : Env ζ8 := E7.snoc (.def (goTyM pp7 n7 bl7) (goValM pu7 pp7 n7 bl7))
def E9 : Env ζ9 := E8.snoc (.def (brecOnTyM n8 bl8) (brecOnValM pp8 n8 bl8 go8))
def E10 : Env ζ10 := E9.snoc (.def (matchTyM n9 u9) (matchValM n9 u9 uu9 c9))
def E11 : Env ζ11 := E10.snoc (.def (fTyM n10 bl10) (fValM pp10 n10 u10 bl10 m10))
def E12 : Env ζ12 := E11.snoc (.def (addTyM n11) (addValM n11 br11 f11))

/-- Read a head's entry of the environments. -/
syntax (name := _envs) "envs" : tactic
macro_rules
  | `(tactic| envs) => `(tactic| simp! [E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11, E12,
  Env.get, Entry.block, Entry.constType, Entry.defValue, belowTyM, belowValM, minsBl, casesOnTyM,
  goTyM, F1TyM, pairM, belowM, brecOnTyM, matchTyM, unitM, fTyM, addTyM, motNM,
  EraseProof.Test.NVR.motN, mN, mZ, mS, mPU, mPP, motNL, funext_iff, Fin.forall_fin_one,
  Fin.forall_fin_two, fin0_eq])

theorem t_pu1 : (E1.get pu1).block = puBlock := by envs
theorem t_pu2 : (E2.get pu2).block = puBlock := by envs
theorem t_ut2 : (E2.get u2).constType = .sort one := by envs
theorem t_uv2 : (E2.get u2).defValue = mPU pu2 one := by envs
theorem t_pp4 : (E4.get pp4).block = ppBlock := by envs
theorem t_n5 : (E5.get n5).block = nBlock := by envs
theorem t_n6 : (E6.get n6).block = nBlock := by envs
theorem t_pu6 : (E6.get pu6).block = puBlock := by envs
theorem t_pp6 : (E6.get pp6).block = ppBlock := by envs
theorem t_n7 : (E7.get n7).block = nBlock := by envs
theorem t_pu7 : (E7.get pu7).block = puBlock := by envs
theorem t_pp7 : (E7.get pp7).block = ppBlock := by envs
theorem t_bt7 : (E7.get bl7).constType = belowTyM n7 := by envs
theorem t_bv7 : (E7.get bl7).defValue = belowValM pu7 pp7 n7 := by envs
theorem t_n8 : (E8.get n8).block = nBlock := by envs
theorem t_pp8 : (E8.get pp8).block = ppBlock := by envs
theorem t_bt8 : (E8.get bl8).constType = belowTyM n8 := by envs
theorem t_gt8 : (E8.get go8).constType = goTyM pp8 n8 bl8 := by envs
theorem t_n9 : (E9.get n9).block = nBlock := by envs
theorem t_ut9 : (E9.get u9).constType = .sort one := by envs
theorem t_uut9 : (E9.get uu9).constType = unitM u9 := by envs
theorem t_ct9 : (E9.get c9).constType = casesOnTyM n9 := by envs
theorem t_n10 : (E10.get n10).block = nBlock := by envs
theorem t_pp10 : (E10.get pp10).block = ppBlock := by envs
theorem t_bt10 : (E10.get bl10).constType = belowTyM n10 := by envs
theorem t_bv10 : (E10.get bl10).defValue = belowValM pu10 pp10 n10 := by envs
theorem t_ut10 : (E10.get u10).constType = .sort one := by envs
theorem t_mt10 : (E10.get m10).constType = matchTyM n10 u10 := by envs
theorem t_n11 : (E11.get n11).block = nBlock := by envs
theorem t_brt11 : (E11.get br11).constType = brecOnTyM n11 bl11 := by envs
theorem t_ft11 : (E11.get f11).constType = fTyM n11 bl11 := by envs
theorem t_bt11 : (E11.get bl11).constType = belowTyM n11 := by envs
theorem t_n12 : (E12.get n12).block = nBlock := by envs
theorem t_at12 : (E12.get a12).constType = addTyM n12 := by envs

/-! ## Well-formedness -/

theorem wf1 : EnvWF E1 := .snoc .nil (.inductive (puBlock_wf _))
theorem wf2 : EnvWF E2 := .snoc wf1 (.def ⟨_, .sortDF⟩ (unitVal_typed t_pu1))
theorem wf3 : EnvWF E3 :=
  .snoc wf2 (.def ⟨one, const_typed wf2 u2 Fin.elim0 (by rw [t_ut2]; rsx)⟩
    (unitUVal_typed wf2 t_pu2 t_ut2 t_uv2))
theorem wf4 : EnvWF E4 := .snoc wf3 (.inductive (ppBlock_wf _))
theorem wf5 : EnvWF E5 := .snoc wf4 (.inductive (nBlock_wf _))
theorem wf6 : EnvWF E6 := .snoc wf5 (.def (casesOnTyM_isType t_n5) (casesOnValM_typed t_n5))
theorem wf7 : EnvWF E7 :=
  .snoc wf6 (.def (belowTyM_isType t_n6 t_pu6 t_pp6) (belowValM_typed t_n6 t_pu6 t_pp6))
theorem wf8 : EnvWF E8 :=
  .snoc wf7 (.def (goTyM_isType wf7 t_n7 t_pu7 t_pp7 t_bt7 t_bv7)
    (goValM_typed wf7 t_n7 t_pu7 t_pp7 t_bt7 t_bv7))
theorem wf9 : EnvWF E9 :=
  .snoc wf8 (.def (brecOnTyM_isType wf8 t_n8 t_pp8 t_bt8 t_gt8)
    (brecOnValM_typed wf8 t_n8 t_pp8 t_bt8 t_gt8))
theorem wf10 : EnvWF E10 :=
  .snoc wf9 (.def (matchValM_typed wf9 t_n9 t_ut9 t_uut9 t_ct9).regular
    (matchValM_typed wf9 t_n9 t_ut9 t_uut9 t_ct9))
theorem wf11 : EnvWF E11 :=
  .snoc wf10 (.def (fValM_typed wf10 t_n10 t_pp10 t_bt10 t_bv10 t_ut10 t_mt10).regular
    (fValM_typed wf10 t_n10 t_pp10 t_bt10 t_bv10 t_ut10 t_mt10))
theorem wf12 : EnvWF E12 :=
  .snoc wf11 (.def (addValM_typed wf11 t_n11 t_brt11 t_ft11 t_bt11).regular
    (addValM_typed wf11 t_n11 t_brt11 t_ft11 t_bt11))

/-! ## Name tables -/

def B1 : Binds ζ1 := fun n =>
  if n = `PUnit then some (.ind pu1 0)
  else if n = `PUnit.unit then some (.ctor pu1 0 0 [])
  else if n = `PUnit.rec then some (.recr pu1 0 [[[]]])
  else none
def B2 : Binds ζ2 := (Binds.wk B1).set `Unit (.const .here)
def B3 : Binds ζ3 := (Binds.wk B2).set `Unit.unit (.const .here)
def B4 : Binds ζ4 := fun n =>
  if n = `PProd then some (.ind pp4 0)
  else if n = `PProd.mk then some (.ctor pp4 0 0 [0, 1])
  else if n = `PProd.rec then some (.recr pp4 0 [[[0, 1]]])
  else Binds.wk B3 n
def B5 : Binds ζ5 := fun n =>
  if n = `N then some (.ind n5 0)
  else if n = `N.z then some (.ctor n5 0 0 [])
  else if n = `N.s then some (.ctor n5 0 1 [0])
  else if n = `N.rec then some (.recr n5 0 [[[], [0]]])
  else Binds.wk B4 n
def B6 : Binds ζ6 := (Binds.wk B5).set `N.casesOn (.const .here)
def B7 : Binds ζ7 := (Binds.wk B6).set `N.below (.const .here)
def B8 : Binds ζ8 := (Binds.wk B7).set `N.brecOn.go (.const .here)
def B9 : Binds ζ9 := (Binds.wk B8).set `N.brecOn (.const .here)
def B10 : Binds ζ10 := (Binds.wk B9).set `add.match_1 (.const .here)
def B11 : Binds ζ11 := (Binds.wk B10).set `add._f (.const .here)
def B12 : Binds ζ12 := (Binds.wk B11).set `add (.const .here)

/-! ## Generic `TrM` facts for `PUnit`'s, `PProd`'s and the definitions' constants -/

section TrGeneric
variable {ζ : Sigs} {E : Env ζ} {B : Binds ζ} {lps : List Name} {n : Nat}
  {Γ : Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}

theorem tr_PU {η : Head ζ (.inductive puSig)} (h : B `PUnit = some (.ind η 0)) {u : Lean.Level}
    {l : Metalean.Level lps.length} (hl : TrLevel lps u = some l) :
    TrM E B lps Γ Δ (tPU u) (mPU η l) :=
  TrM.special (as := []) (as' := []) h rfl rfl (fun _ _ _ h => nomatch h)
    (SatTr.indSat (E := E) (lps := lps) (η := η) (s := 0) (us := [u]) (ls := ![l])
      (ps := Fin.elim0) (is := Fin.elim0) (rest := []) (trLevels_one hl))

theorem tr_PUu {η : Head ζ (.inductive puSig)} (h : B `PUnit.unit = some (.ctor η 0 0 []))
    {u : Lean.Level} {l : Metalean.Level lps.length} (hl : TrLevel lps u = some l) :
    TrM E B lps Γ Δ (cPU u) (mPUu η l) :=
  TrM.special (as := []) (as' := []) h rfl rfl (fun _ _ _ h => nomatch h)
    (SatTr.ctorSat (E := E) (lps := lps) (η := η) (s := 0) (c := 0) (us := [u]) (order := [])
      (ls := ![l]) (fs := []) (rest := []) (ps := Fin.elim0) (fds := Fin.elim0)
      (recFds := Fin.elim0) (trLevels_one hl) rfl rfl (fun o => Fin.elim0 o))

theorem tr_PP {η : Head ζ (.inductive ppSig)} (h : B `PProd = some (.ind η 0)) {u v : Lean.Level}
    {l m : Metalean.Level lps.length} (hu : TrLevel lps u = some l) (hv : TrLevel lps v = some m)
    {α β : Lean.Expr} {α' β' : Metalean.Expr ζ lps.length n} (hα : TrM E B lps Γ Δ α α')
    (hβ : TrM E B lps Γ Δ β β') :
    TrM E B lps Γ Δ (.app (.app (tPP u v) α) β) (mPP η l m α' β') :=
  TrM.special (as := [α, β]) (as' := [α', β']) h rfl rfl
    (by
      intro i x x' h1 h2
      rcases i with _ | _ | i <;> simp at h1 h2 <;> subst h1 h2
      · exact hα
      · exact hβ)
    (SatTr.indSat (E := E) (lps := lps) (η := η) (s := 0) (us := [u, v]) (ls := ![l, m])
      (ps := ![α', β']) (is := Fin.elim0) (rest := []) (trLevels_two hu hv))

theorem tr_PPmk {η : Head ζ (.inductive ppSig)} (h : B `PProd.mk = some (.ctor η 0 0 [0, 1]))
    {u v : Lean.Level} {l m : Metalean.Level lps.length} (hu : TrLevel lps u = some l)
    (hv : TrLevel lps v = some m) {α β a b : Lean.Expr} {α' β' a' b' : Metalean.Expr ζ lps.length n}
    (hα : TrM E B lps Γ Δ α α') (hβ : TrM E B lps Γ Δ β β') (ha : TrM E B lps Γ Δ a a')
    (hb : TrM E B lps Γ Δ b b') :
    TrM E B lps Γ Δ (.app (.app (.app (.app (cPP u v) α) β) a) b) (mPPmk η l m α' β' a' b') :=
  TrM.special (as := [α, β, a, b]) (as' := [α', β', a', b']) h rfl rfl
    (by
      intro i x x' h1 h2
      rcases i with _ | _ | _ | _ | i <;> simp at h1 h2 <;> subst h1 h2
      · exact hα
      · exact hβ
      · exact ha
      · exact hb)
    (SatTr.ctorSat (E := E) (lps := lps) (η := η) (s := 0) (c := 0) (us := [u, v]) (order := [0, 1])
      (ls := ![l, m]) (fs := [a', b']) (rest := []) (ps := ![α', β']) (fds := ![a', b'])
      (recFds := Fin.elim0) (trLevels_two hu hv) rfl rfl
      (by intro o; fin_cases o <;> exact ⟨_, _, rfl, rfl, rfl⟩))

theorem tr_const0 {kind : ConstKind} {η : Head ζ (.const kind 0)} {c : Name}
    (h : B c = some (.const η)) : TrM E B lps Γ Δ (.const c []) (.const η Fin.elim0) :=
  TrM.const h trLevels_nil

theorem tr_const1 {kind : ConstKind} {η : Head ζ (.const kind 1)} {c : Name}
    (h : B c = some (.const η)) {u : Lean.Level} {l : Metalean.Level lps.length}
    (hl : TrLevel lps u = some l) : TrM E B lps Γ Δ (.const c [u]) (.const η ![l]) :=
  TrM.const h (trLevels_one hl)

theorem tr_below {η : Head ζ (.const .def 1)} (h : B `N.below = some (.const η)) {u : Lean.Level}
    {l : Metalean.Level lps.length} (hl : TrLevel lps u = some l) {mo a : Lean.Expr}
    {mo' a' : Metalean.Expr ζ lps.length n} (hmo : TrM E B lps Γ Δ mo mo')
    (ha : TrM E B lps Γ Δ a a') :
    TrM E B lps Γ Δ (.app (.app (below u) mo) a) (belowM η l mo' a') :=
  TrM.app (notSpecial_const h ⟨_, rfl⟩) (TrM.app (notSpecial_const h ⟨_, rfl⟩) (tr_const1 h hl) hmo)
    ha

end TrGeneric

theorem trL_u : TrLevel [`u] uu = some lu := rfl
theorem trL_m1u : TrLevel [`u] m1u = some m1M := rfl
theorem trL_sm1u : TrLevel [`u] (.succ m1u) = some (.succ m1M) := rfl
theorem trL_u1 : TrLevel [`u_1] u1 = some lu := rfl
theorem trL_one {lps : List Name} : TrLevel lps l1 = some one := rfl

/-! ## The block of `PUnit` in `E1`/`B1` -/

theorem B1_PU : B1 `PUnit = some (.ind pu1 0) := rfl
theorem B1_PUu : B1 `PUnit.unit = some (.ctor pu1 0 0 []) := rfl
theorem B1_PUrec : B1 `PUnit.rec = some (.recr pu1 0 [[[]]]) := rfl

theorem tr_puRecTy : TrM E1 B1 [`u_1, `u] .nil [] PUnit_rec.type (puRecTyM pu1) :=
  TrM.forallE (TrM.forallE (tr_PU B1_PU rfl) (TrM.sort rfl))
    (TrM.forallE (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_PUu B1_PUu rfl))
      (TrM.forallE (tr_PU B1_PU rfl) (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl))))

theorem tr_puRec :
    TrM E1 B1 [`u_1, `u] .nil [] (.const `PUnit.rec [.param `u_1, .param `u]) (puRecTermM pu1) :=
  TrM.special (as := []) (as' := []) B1_PUrec rfl rfl (fun _ _ _ h => nomatch h)
    (SatTr.recrEta (E := E1) (lps := [`u_1, `u]) (args := []) (η := pu1) (s := 0)
      (us := [.param `u_1, .param `u]) (us' := [.param `u]) (l := q0) (ls := ![q1])
      (fun _ _ => []) (Or.inl ⟨by rw [t_pu1]; exact largeElimPU, _, rfl, rfl⟩)
      (trLevels_one rfl) (by intro t c; fin_cases t; fin_cases c; rfl) (by decide)
      (recrTerm_eqPU t_pu1))

def IsPU : Fin puSig.nsorts → InductiveVal := fun _ => PUnit_ind
def CsPU : (s : Fin puSig.nsorts) → Fin (puSig.nctors s) → ConstructorVal := fun _ _ => PUnit_unit
def RsPU : Fin puSig.nsorts → RecursorVal := fun _ => PUnit_rec
def ordersPU : (s : Fin puSig.nsorts) → Fin (puSig.nctors s) → List Nat := fun _ _ => []

theorem PPU_eq : IndBlock.decls IsPU CsPU RsPU =
    [.recInfo PUnit_rec, .ctorInfo PUnit_unit, .inductInfo PUnit_ind] := rfl

theorem indBlockPU : IndBlock E1 B1 pu1 [`u] IsPU CsPU RsPU ordersPU where
  levels := rfl
  ind s := by fin_cases s; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  ctor s c := by
    fin_cases s; fin_cases c
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, [], [], rfl, rfl, rfl, .nil, .nil, .nil⟩
  ctorType s c := by fin_cases s; fin_cases c; exact ⟨_, [], rfl, rfl, rfl⟩
  recr s := by
    fin_cases s
    exact ⟨rfl, rfl, fun _ => ⟨`u_1, rfl⟩, fun h => absurd (by rw [t_pu1]; exact largeElimPU) h,
      rfl, rfl, rfl, rfl, rfl, rfl⟩
  recrType s := by fin_cases s; rfl
  recMajor s := by fin_cases s; exact ⟨_, _, _, _, _, rfl, rfl⟩
  minors s t c := by fin_cases s; fin_cases t; fin_cases c; rfl
  recIHs s := by
    fin_cases s
    exact ⟨_, _, rfl, rfl, fun t c => by fin_cases t; fin_cases c; rfl⟩
  indexVars s _ h := by fin_cases s; exact h.elim fun i _ => i.elim0

theorem constTypedPU : ∀ ci ∈ IndBlock.decls IsPU CsPU RsPU, ConstTyped E1 B1 ci := by
  rw [PPU_eq]
  intro ci hci
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hci
  rcases hci with rfl | rfl | rfl
  · exact ⟨_, _, tr_puRecTy, tr_puRec, puRecTermM_typed t_pu1⟩
  · exact ⟨_, _, tr_PU B1_PU rfl, tr_PUu B1_PUu rfl, mPUu_typed t_pu1⟩
  · exact ⟨_, _, TrM.sort rfl, tr_PU B1_PU rfl, mPU_typed t_pu1⟩

theorem henv1 : ProgEnv (IndBlock.decls IsPU CsPU RsPU) ζ1 E1 B1 := by
  have h := ProgEnv.induct (P := []) (I := puBlock) (B' := B1) (lps := [`u]) (Is := IsPU)
    (Cs := CsPU) (Rs := RsPU) (orders := ordersPU) .nil (by decide) (by simp [findDecl])
    (by decide)
    (fun n hn => by
      have hl : (IndBlock.decls IsPU CsPU RsPU).map (·.name) = [`PUnit.rec, `PUnit.unit, `PUnit] :=
        rfl
      rw [hl] at hn
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
      obtain ⟨h1, h2, h3⟩ := hn
      simp [B1, Binds.wk, h1, h2, h3])
    indBlockPU constTypedPU
  rw [List.append_nil] at h
  exact h

/-! ## `Unit`, `Unit.unit` -/

theorem B2_PU : B2 `PUnit = some (.ind pu2 0) := rfl
theorem B2_PUu : B2 `PUnit.unit = some (.ctor pu2 0 0 []) := rfl
theorem B2_Unit : B2 `Unit = some (.const u2) := rfl

theorem henv2 : ProgEnv (.defnInfo Unit_def :: IndBlock.decls IsPU CsPU RsPU) ζ2 E2 B2 :=
  ProgEnv.defn henv1 (by decide) (by decide) rfl rfl (TrM.sort rfl) (tr_PU B1_PU rfl)

theorem henv3 : ProgEnv (.defnInfo Unit_unit :: .defnInfo Unit_def ::
    IndBlock.decls IsPU CsPU RsPU) ζ3 E3 B3 :=
  ProgEnv.defn henv2 (by decide) (by decide) rfl rfl (tr_const0 B2_Unit) (tr_PUu B2_PUu rfl)

/-! ## The block of `PProd` in `E4`/`B4` -/

theorem B4_PP : B4 `PProd = some (.ind pp4 0) := rfl
theorem B4_PPmk : B4 `PProd.mk = some (.ctor pp4 0 0 [0, 1]) := rfl
theorem B4_PPrec : B4 `PProd.rec = some (.recr pp4 0 [[[0, 1]]]) := rfl

def P3 : List ConstantInfo :=
  .defnInfo Unit_unit :: .defnInfo Unit_def :: IndBlock.decls IsPU CsPU RsPU

theorem tr_ppTy : TrM E4 B4 [`u, `v] .nil [] PProd_ind.type ppTyM :=
  TrM.forallE (TrM.sort rfl) (TrM.forallE (TrM.sort rfl) (TrM.sort rfl))

theorem tr_ppConst : TrM E4 B4 [`u, `v] .nil [] (.const `PProd [.param `u, .param `v])
    (ppTermM pp4) := by
  have h := TrM.special (E := E4) (B := B4) (lps := [`u, `v]) (Γ := .nil) (Δ := [])
    (c := `PProd) (us := [.param `u, .param `v]) (as := []) (as' := []) B4_PP rfl rfl
    (fun _ _ _ h => nomatch h)
    (SatTr.indEta (E := E4) (lps := [`u, `v]) (args := []) (η := pp4) (s := 0)
      (us := [.param `u, .param `v]) (ls := ![q0, q1]) (trLevels_two rfl rfl) (by decide))
  rw [indTerm_eqPP t_pp4] at h
  exact h

theorem tr_ppMkTy : TrM E4 B4 [`u, `v] .nil [] PProd_mk.type (ppMkTyM pp4) :=
  TrM.forallE (TrM.sort rfl) (TrM.forallE (TrM.sort rfl) (TrM.forallE (TrM.bvar rfl)
    (TrM.forallE (TrM.bvar rfl) (tr_PP B4_PP rfl rfl (TrM.bvar rfl) (TrM.bvar rfl)))))

theorem tr_ppMk : TrM E4 B4 [`u, `v] .nil [] (.const `PProd.mk [.param `u, .param `v])
    (ppMkTermM pp4) :=
  TrM.special (as := []) (as' := []) B4_PPmk rfl rfl (fun _ _ _ h => nomatch h)
    (SatTr.ctorEta (args := []) (η := pp4) (s := 0) (c := 0) (order := [0, 1])
      (trLevels_two rfl rfl) (by decide) (ctorTerm_eqPP t_pp4))

theorem tr_ppRecTy : TrM E4 B4 [`u_1, `u, `v] .nil [] PProd_rec.type (ppRecTyM pp4) :=
  TrM.forallE (TrM.sort rfl) (TrM.forallE (TrM.sort rfl)
    (TrM.forallE (TrM.forallE (tr_PP B4_PP rfl rfl (TrM.bvar rfl) (TrM.bvar rfl)) (TrM.sort rfl))
      (TrM.forallE (TrM.forallE (TrM.bvar rfl) (TrM.forallE (TrM.bvar rfl)
          (TrM.app notSpecial_bvar (TrM.bvar rfl)
            (tr_PPmk B4_PPmk rfl rfl (TrM.bvar rfl) (TrM.bvar rfl) (TrM.bvar rfl) (TrM.bvar rfl)))))
        (TrM.forallE (tr_PP B4_PP rfl rfl (TrM.bvar rfl) (TrM.bvar rfl))
          (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl))))))

theorem tr_ppRec : TrM E4 B4 [`u_1, `u, `v] .nil []
    (.const `PProd.rec [.param `u_1, .param `u, .param `v]) (ppRecTermM pp4) :=
  TrM.special (as := []) (as' := []) B4_PPrec rfl rfl (fun _ _ _ h => nomatch h)
    (SatTr.recrEta (E := E4) (lps := [`u_1, `u, `v]) (args := []) (η := pp4) (s := 0)
      (us := [.param `u_1, .param `u, .param `v]) (us' := [.param `u, .param `v]) (l := r0)
      (ls := ![r1, r2]) (fun _ _ => [0, 1]) (Or.inl ⟨by rw [t_pp4]; exact largeElimPP, _, rfl, rfl⟩)
      (trLevels_two rfl rfl) (by intro t c; fin_cases t; fin_cases c; rfl) (by decide)
      (recrTerm_eqPP t_pp4))

def IsPP : Fin ppSig.nsorts → InductiveVal := fun _ => PProd_ind
def CsPP : (s : Fin ppSig.nsorts) → Fin (ppSig.nctors s) → ConstructorVal := fun _ _ => PProd_mk
def RsPP : Fin ppSig.nsorts → RecursorVal := fun _ => PProd_rec
def ordersPP : (s : Fin ppSig.nsorts) → Fin (ppSig.nctors s) → List Nat := fun _ _ => [0, 1]

theorem PPP_eq : IndBlock.decls IsPP CsPP RsPP =
    [.recInfo PProd_rec, .ctorInfo PProd_mk, .inductInfo PProd_ind] := rfl

theorem indBlockPP : IndBlock E4 B4 pp4 [`u, `v] IsPP CsPP RsPP ordersPP where
  levels := rfl
  ind s := by fin_cases s; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  ctor s c := by
    fin_cases s; fin_cases c
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, [0, 1], [], rfl, rfl, rfl, by decide, .nil,
      List.Perm.refl _⟩
  ctorType s c := by fin_cases s; fin_cases c; exact ⟨_, [], rfl, rfl, rfl⟩
  recr s := by
    fin_cases s
    exact ⟨rfl, rfl, fun _ => ⟨`u_1, rfl⟩, fun h => absurd (by rw [t_pp4]; exact largeElimPP) h,
      rfl, rfl, rfl, rfl, rfl, rfl⟩
  recrType s := by fin_cases s; rfl
  recMajor s := by fin_cases s; exact ⟨_, _, _, _, _, rfl, rfl⟩
  minors s t c := by fin_cases s; fin_cases t; fin_cases c; rfl
  recIHs s := by
    fin_cases s
    exact ⟨_, _, rfl, rfl, fun t c => by fin_cases t; fin_cases c; rfl⟩
  indexVars s _ h := by fin_cases s; exact h.elim fun i _ => i.elim0

theorem constTypedPP : ∀ ci ∈ IndBlock.decls IsPP CsPP RsPP, ConstTyped E4 B4 ci := by
  rw [PPP_eq]
  intro ci hci
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hci
  rcases hci with rfl | rfl | rfl
  · exact ⟨_, _, tr_ppRecTy, tr_ppRec, ppRecTermM_typed t_pp4⟩
  · exact ⟨_, _, tr_ppMkTy, tr_ppMk, ppMkTermM_typed t_pp4⟩
  · exact ⟨_, _, tr_ppTy, tr_ppConst, ppTermM_typed t_pp4⟩

theorem henv4 : ProgEnv (IndBlock.decls IsPP CsPP RsPP ++ P3) ζ4 E4 B4 :=
  ProgEnv.induct (I := ppBlock) (lps := [`u, `v]) (orders := ordersPP) henv3 (by decide)
    (by rw [PPP_eq]; decide) (by decide)
    (fun n hn => by
      rw [PPP_eq] at hn
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
        not_or] at hn
      obtain ⟨h1, h2, h3⟩ := hn
      have h1' : n ≠ `PProd.rec := h1
      have h2' : n ≠ `PProd.mk := h2
      have h3' : n ≠ `PProd := h3
      simp [B4, h1', h2', h3'])
    indBlockPP constTypedPP

/-! ## The block of `N` in `E5`/`B5` -/

theorem B5_N : B5 `N = some (.ind n5 0) := rfl
theorem B5_z : B5 `N.z = some (.ctor n5 0 0 []) := rfl
theorem B5_s : B5 `N.s = some (.ctor n5 0 1 [0]) := rfl
theorem B5_rec : B5 `N.rec = some (.recr n5 0 [[[], [0]]]) := rfl

def P4 : List ConstantInfo := IndBlock.decls IsPP CsPP RsPP ++ P3

theorem tr_recTy5 : TrM E5 B5 [`u] .nil [] recTy (recTyM n5) :=
  TrM.forallE (TrM.forallE (tr_N B5_N) (TrM.sort rfl))
    (TrM.forallE (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_Z B5_z))
      (TrM.forallE (TrM.forallE (tr_N B5_N) (TrM.forallE
          (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl))
          (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_S B5_s (TrM.bvar rfl)))))
        (TrM.forallE (tr_N B5_N) (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl)))))

theorem tr_rec5 : TrM E5 B5 [`u] .nil [] (.const `N.rec [.param `u]) (recTermM n5) := by
  refine TrM.special (as := []) (as' := []) B5_rec rfl rfl (fun _ _ _ h => nomatch h) ?_
  refine SatTr.recrEta (E := E5) (lps := [`u]) (η := n5) (s := 0) (us := [.param `u]) (us' := [])
    (ls := Fin.elim0) (l := lu) (args := []) ordersN ?_ trLevels_nil ?_ (by decide) ?_
  · exact Or.inl ⟨by rw [t_n5]; exact largeElimN, _, rfl, rfl⟩
  · intro t c; fin_cases t; fin_cases c <;> rfl
  · exact recrTerm_eqN t_n5

theorem tr_sConst5 : TrM E5 B5 [] .nil [] cS (sTermM n5) :=
  TrM.special (as := []) (as' := []) B5_s rfl rfl (fun _ _ _ h => nomatch h)
    (SatTr.ctorEta (args := []) (η := n5) (s := 0) (c := 1) (order := [0]) trLevels_nil
      (by decide) (ctorTerm_eqN t_n5))

theorem indBlockN5 : IndBlock E5 B5 n5 [] IsN CsN RsN ordersN where
  levels := rfl
  ind s := by fin_cases s; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  ctor s c := by
    fin_cases s; fin_cases c
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, [], [], rfl, rfl, rfl, .nil, .nil, .nil⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, [], [0], rfl, rfl, rfl, .nil, by decide,
        List.Perm.refl _⟩
  ctorType s c := by fin_cases s; fin_cases c <;> exact ⟨_, [], rfl, rfl, rfl⟩
  recr s := by
    fin_cases s
    exact ⟨rfl, rfl, fun _ => ⟨`u, rfl⟩, fun h => absurd (by rw [t_n5]; exact largeElimN) h, rfl,
      rfl, rfl, rfl, rfl, rfl⟩
  recrType s := by fin_cases s; rfl
  recMajor s := by fin_cases s; exact ⟨_, _, _, _, _, rfl, rfl⟩
  minors s t c := by fin_cases s; fin_cases t; fin_cases c <;> rfl
  recIHs s := by
    fin_cases s
    exact ⟨_, _, rfl, rfl, fun t c => by fin_cases t; fin_cases c <;> rfl⟩
  indexVars s _ h := by fin_cases s; exact h.elim fun i _ => i.elim0

theorem constTypedN5 : ∀ ci ∈ IndBlock.decls IsN CsN RsN, ConstTyped E5 B5 ci := by
  rw [PN_eq]
  intro ci hci
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hci
  rcases hci with rfl | rfl | rfl | rfl
  · exact ⟨_, _, tr_recTy5, tr_rec5, recTermM_typed t_n5⟩
  · exact ⟨_, _, tr_N B5_N, tr_Z B5_z, mZ_typed t_n5⟩
  · exact ⟨_, _, TrM.forallE (tr_N B5_N) (tr_N B5_N), tr_sConst5, sTermM_typed t_n5⟩
  · exact ⟨_, _, TrM.sort rfl, tr_N B5_N, indN_typed t_n5⟩

theorem henv5 : ProgEnv (IndBlock.decls IsN CsN RsN ++ P4) ζ5 E5 B5 :=
  ProgEnv.induct (I := nBlock) (lps := []) (orders := ordersN) henv4 (by decide)
    (by rw [PN_eq]; decide) (by decide)
    (fun n hn => by
      rw [PN_eq] at hn
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
        not_or] at hn
      obtain ⟨h1, h2, h3, h4⟩ := hn
      have h1' : n ≠ `N.rec := h1
      have h2' : n ≠ `N.z := h2
      have h3' : n ≠ `N.s := h3
      have h4' : n ≠ `N := h4
      simp [B5, h1', h2', h3', h4'])
    indBlockN5 constTypedN5

/-! ## The definitions on `N` -/

theorem trM_eq {ζ : Sigs} {E : Env ζ} {B : Binds ζ} {lps : List Name} {n : Nat}
    {Γ : Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n} {e : Lean.Expr}
    {t t' : Metalean.Expr ζ lps.length n} (h : TrM E B lps Γ Δ e t) (ht : t = t') :
    TrM E B lps Γ Δ e t' := ht ▸ h

def P5 : List ConstantInfo := IndBlock.decls IsN CsN RsN ++ P4

/-! ### `N.casesOn` in `E5`/`B5` -/

theorem tr_casesOnTy : TrM E5 B5 [`u] .nil [] casesOnTy (casesOnTyM n5) :=
  TrM.forallE (TrM.forallE (tr_N B5_N) (TrM.sort rfl)) (TrM.forallE (tr_N B5_N)
    (TrM.forallE (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_Z B5_z))
      (TrM.forallE (TrM.forallE (tr_N B5_N)
          (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_S B5_s (TrM.bvar rfl))))
        (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl)))))

theorem tr_casesOnVal : TrM E5 B5 [`u] .nil [] casesOnVal (casesOnValM n5) := by
  have h : TrM E5 B5 [`u] .nil [] casesOnVal _ :=
    TrM.lam (TrM.forallE (tr_N B5_N) (TrM.sort rfl)) (TrM.lam (tr_N B5_N)
      (TrM.lam (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_Z B5_z))
        (TrM.lam (TrM.forallE (tr_N B5_N)
            (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_S B5_s (TrM.bvar rfl))))
          (TrM.special (c := `N.rec) (us := [.param `u])
            (as := [.bvar 3, .bvar 1, .lam `n tN (.lam `n_ih (.app (.bvar 4) (.bvar 0))
              (.app (.bvar 2) (.bvar 1)) .default) .default, .bvar 2])
            (as' := [#0, #2, .lam (mN n5) (.lam (.app #0 #4) (.app #3 #4)), #1]) B5_rec rfl rfl
            (by
              intro i a a' h1 h2
              rcases i with _ | _ | _ | _ | i <;> simp at h1 h2 <;> subst h1 h2
              · exact TrM.bvar rfl
              · exact TrM.bvar rfl
              · exact TrM.lam (tr_N B5_N) (TrM.lam
                  (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl))
                  (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl)))
              · exact TrM.bvar rfl)
            (SatTr.recrSat (E := E5) (lps := [`u]) (η := n5) (s := 0) (orders := [[[], [0]]])
              (us := [.param `u]) (us' := []) (ls := Fin.elim0) (l := lu) ordersN
              ![#0, #2, .lam (mN n5) (.lam (.app #0 #4) (.app #3 #4)), #1] [] (minsCO n5)
              (Or.inl ⟨by rw [t_n5]; exact largeElimN, _, rfl, rfl⟩) trLevels_nil
              (by intro t c; fin_cases t; fin_cases c <;> rfl)
              (by
                intro t c; fin_cases t; fin_cases c <;>
                  simp [Frontend.wrapCase, Frontend.isIdentityOrder] <;> rfl))))))
  exact trM_eq h (by simp only [casesOnValM]; rsx [minsCO, MLDecl.wk, MLDecl.denote]; all_goals (refine ⟨?_, ?_⟩ <;> rfl))

theorem henv6 : ProgEnv (.defnInfo N_casesOn :: P5) ζ6 E6 B6 :=
  ProgEnv.defn henv5 (by decide) (by decide) rfl rfl tr_casesOnTy tr_casesOnVal

/-! ### `N.below` in `E6`/`B6` -/

theorem B6_N : B6 `N = some (.ind n6 0) := rfl
theorem B6_rec : B6 `N.rec = some (.recr n6 0 [[[], [0]]]) := rfl
theorem B6_PU : B6 `PUnit = some (.ind pu6 0) := rfl
theorem B6_PP : B6 `PProd = some (.ind pp6 0) := rfl

theorem tr_belowTy : TrM E6 B6 [`u] .nil [] belowTy (belowTyM n6) :=
  TrM.forallE (TrM.forallE (tr_N B6_N) (TrM.sort rfl)) (TrM.forallE (tr_N B6_N) (TrM.sort rfl))

/-- The minor of `N.s` in `N.below`'s value. -/
def blMinS : Metalean.Expr ζ6 1 2 :=
  .lam (mN n6) (.lam (.sort m1M) (mPP pp6 lu m1M (.app #0 #2) #3))

theorem tr_belowVal : TrM E6 B6 [`u] .nil [] belowVal (belowValM pu6 pp6 n6) := by
  have h : TrM E6 B6 [`u] .nil [] belowVal _ :=
    TrM.lam (TrM.forallE (tr_N B6_N) (TrM.sort rfl)) (TrM.lam (tr_N B6_N)
      (TrM.special (E := E6) (B := B6) (lps := [`u]) (c := `N.rec) (us := [.succ m1u])
        (as := [.lam `t tN (.sort m1u) .default, tPU m1u,
          .lam `n tN (.lam `n_ih (.sort m1u) (.app (.app (tPP uu m1u) (.app (.bvar 3) (.bvar 1)))
            (.bvar 0)) .default) .default, .bvar 0])
        (as' := [.lam (mN n6) (.sort m1M), mPU pu6 m1M, blMinS, #1]) B6_rec rfl rfl
        (by
          intro i a a' h1 h2
          rcases i with _ | _ | _ | _ | i <;> simp at h1 h2 <;> subst h1 h2
          · exact TrM.lam (tr_N B6_N) (TrM.sort rfl)
          · exact tr_PU B6_PU rfl
          · exact TrM.lam (tr_N B6_N) (TrM.lam (TrM.sort rfl)
              (tr_PP B6_PP rfl rfl (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl))
                (TrM.bvar rfl)))
          · exact TrM.bvar rfl)
        (SatTr.recrSat (E := E6) (lps := [`u]) (η := n6) (s := 0) (orders := [[[], [0]]])
          (us := [.succ m1u]) (us' := []) (ls := Fin.elim0) (l := .succ m1M) ordersN
          ![.lam (mN n6) (.sort m1M), mPU pu6 m1M, blMinS, #1] [] (minsBl pu6 pp6 n6)
          (Or.inl ⟨by rw [t_n6]; exact largeElimN, _, rfl, rfl⟩) trLevels_nil
          (by intro t c; fin_cases t; fin_cases c <;> rfl)
          (by
            intro t c; fin_cases t; fin_cases c <;>
              simp [Frontend.wrapCase, Frontend.isIdentityOrder] <;> rfl))))
  exact trM_eq h (by simp only [belowValM]; rsx [blMinS, MLDecl.wk, MLDecl.denote]; all_goals (refine ⟨?_, ?_⟩ <;> rfl))

theorem henv7 : ProgEnv (.defnInfo N_below :: .defnInfo N_casesOn :: P5) ζ7 E7 B7 :=
  ProgEnv.defn henv6 (by decide) (by decide) rfl rfl tr_belowTy tr_belowVal

/-! ### `N.brecOn.go` in `E7`/`B7` -/

theorem B7_N : B7 `N = some (.ind n7 0) := rfl
theorem B7_z : B7 `N.z = some (.ctor n7 0 0 []) := rfl
theorem B7_s : B7 `N.s = some (.ctor n7 0 1 [0]) := rfl
theorem B7_rec : B7 `N.rec = some (.recr n7 0 [[[], [0]]]) := rfl
theorem B7_PU : B7 `PUnit = some (.ind pu7 0) := rfl
theorem B7_PUu : B7 `PUnit.unit = some (.ctor pu7 0 0 []) := rfl
theorem B7_PP : B7 `PProd = some (.ind pp7 0) := rfl
theorem B7_PPmk : B7 `PProd.mk = some (.ctor pp7 0 0 [0, 1]) := rfl
theorem B7_below : B7 `N.below = some (.const bl7) := rfl

section TrGo
variable {n : Nat} {Γ : Ctx ζ7 [`u].length 0 n} {Δ : MLCtx ζ7 [`u].length n}

theorem tr_F1Ty {Γ : Ctx ζ7 [`u].length 0 2} :
    TrM E7 B7 [`u] Γ ((MLCtx.pushLam [] none).pushLam none) F1Ty (F1TyM n7 bl7) :=
  TrM.forallE (tr_N B7_N) (TrM.forallE (tr_below B7_below rfl (TrM.bvar rfl) (TrM.bvar rfl))
    (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl)))

theorem tr_pair {mo t : Nat} {mo' t' : Metalean.Expr ζ7 1 n} (hmo : Δ.findB mo = some mo')
    (ht : Δ.findB t = some t') :
    TrM E7 B7 [`u] Γ Δ (pairTy mo t) (pairM pp7 bl7 mo' t') :=
  tr_PP B7_PP rfl rfl (TrM.app notSpecial_bvar (TrM.bvar hmo) (TrM.bvar ht))
    (tr_below B7_below rfl (TrM.bvar hmo) (TrM.bvar ht))

end TrGo

theorem tr_goTy : TrM E7 B7 [`u] .nil [] goTy (goTyM pp7 n7 bl7) :=
  TrM.forallE (TrM.forallE (tr_N B7_N) (TrM.sort rfl)) (TrM.forallE (tr_N B7_N)
    (TrM.forallE tr_F1Ty (tr_pair rfl rfl)))

/-- The minors of `N.brecOn.go`'s recursor, as the translation gives them. -/
def goMinZ : Metalean.Expr ζ7 1 3 :=
  mPPmk pp7 lu m1M (.app #0 (mZ n7)) (mPU pu7 m1M) (.app (.app #2 (mZ n7)) (mPUu pu7 m1M))
    (mPUu pu7 m1M)
def goMinS : Metalean.Expr ζ7 1 3 :=
  .lam (mN n7) (.lam (pairM pp7 bl7 #0 #3)
    (mPPmk pp7 lu m1M (.app #0 (mS n7 #3)) (pairM pp7 bl7 #0 #3) (.app (.app #2 (mS n7 #3)) #4) #4))

theorem tr_goVal : TrM E7 B7 [`u] .nil [] goVal (goValM pu7 pp7 n7 bl7) := by
  have h : TrM E7 B7 [`u] .nil [] goVal _ :=
    TrM.lam (TrM.forallE (tr_N B7_N) (TrM.sort rfl)) (TrM.lam (tr_N B7_N) (TrM.lam tr_F1Ty
      (TrM.special (E := E7) (B := B7) (lps := [`u]) (c := `N.rec) (us := [m1u])
        (as := [.lam `t tN (pairTy 3 0) .default,
          .app (.app (.app (.app (cPP uu m1u) (.app (.bvar 2) cZ)) (tPU m1u))
            (.app (.app (.bvar 0) cZ) (cPU m1u))) (cPU m1u),
          .lam `n tN (.lam `n_ih (pairTy 3 0)
            (.app (.app (.app (.app (cPP uu m1u) (.app (.bvar 4) (.app cS (.bvar 1)))) (pairTy 4 1))
              (.app (.app (.bvar 2) (.app cS (.bvar 1))) (.bvar 0))) (.bvar 0)) .default) .default,
          .bvar 1])
        (as' := [motGo pp7 n7 bl7, goMinZ, goMinS, #1]) B7_rec rfl rfl
        (by
          intro i a a' h1 h2
          rcases i with _ | _ | _ | _ | i <;> simp at h1 h2 <;> subst h1 h2
          · exact TrM.lam (tr_N B7_N) (tr_pair rfl rfl)
          · exact tr_PPmk B7_PPmk rfl rfl
              (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_Z B7_z)) (tr_PU B7_PU rfl)
              (TrM.app notSpecial_bvar (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_Z B7_z))
                (tr_PUu B7_PUu rfl)) (tr_PUu B7_PUu rfl)
          · exact TrM.lam (tr_N B7_N) (TrM.lam (tr_pair rfl rfl)
              (tr_PPmk B7_PPmk rfl rfl
                (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_S B7_s (TrM.bvar rfl)))
                (tr_pair rfl rfl)
                (TrM.app notSpecial_bvar (TrM.app notSpecial_bvar (TrM.bvar rfl)
                  (tr_S B7_s (TrM.bvar rfl))) (TrM.bvar rfl))
                (TrM.bvar rfl)))
          · exact TrM.bvar rfl)
        (SatTr.recrSat (E := E7) (lps := [`u]) (η := n7) (s := 0) (orders := [[[], [0]]])
          (us := [m1u]) (us' := []) (ls := Fin.elim0) (l := m1M) ordersN
          ![motGo pp7 n7 bl7, goMinZ, goMinS, #1] [] (minsGo pu7 pp7 n7 bl7)
          (Or.inl ⟨by rw [t_n7]; exact largeElimN, _, rfl, rfl⟩) trLevels_nil
          (by intro t c; fin_cases t; fin_cases c <;> rfl)
          (by
            intro t c; fin_cases t; fin_cases c <;>
              simp [Frontend.wrapCase, Frontend.isIdentityOrder] <;> rfl)))))
  exact trM_eq h (by
    simp only [goValM]
    rsx [goMinZ, goMinS, motGo, pairM, minsGo, F1TyM, MLDecl.wk, MLDecl.denote]
    all_goals (refine ⟨?_, ?_⟩ <;> rfl))

theorem henv8 : ProgEnv (.defnInfo N_brecOn_go :: .defnInfo N_below :: .defnInfo N_casesOn :: P5)
    ζ8 E8 B8 :=
  ProgEnv.defn henv7 (by decide) (by decide) rfl rfl tr_goTy tr_goVal

/-- `TypedExt` in the context itself (the identity renaming). -/
theorem typedExt_self {ζ : Sigs} {E : Env ζ} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} {e T : Expr ζ ℓ n}
    (h : E[Γ] ⊢ e : T) : TypedExt E Γ e T :=
  ⟨n, Γ, Ren.id, Function.injective_id, fun v => by rw [Expr.rename_id]; rfl, by simpa using h⟩

/-! ### `N.brecOn` in `E8`/`B8` -/

theorem B8_N : B8 `N = some (.ind n8 0) := rfl
theorem B8_PP : B8 `PProd = some (.ind pp8 0) := rfl
theorem B8_below : B8 `N.below = some (.const bl8) := rfl
theorem B8_go : B8 `N.brecOn.go = some (.const go8) := rfl

theorem tr_F1Ty8 {Γ : Ctx ζ8 [`u].length 0 2} :
    TrM E8 B8 [`u] Γ ((MLCtx.pushLam [] none).pushLam none) F1Ty (F1TyM n8 bl8) :=
  TrM.forallE (tr_N B8_N) (TrM.forallE (tr_below B8_below rfl (TrM.bvar rfl) (TrM.bvar rfl))
    (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl)))

theorem tr_brecOnTy : TrM E8 B8 [`u] .nil [] brecOnTy (brecOnTyM n8 bl8) :=
  TrM.forallE (TrM.forallE (tr_N B8_N) (TrM.sort rfl)) (TrM.forallE (tr_N B8_N)
    (TrM.forallE tr_F1Ty8 (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl))))

theorem tr_brecOnVal : TrM E8 B8 [`u] .nil [] brecOnVal (brecOnValM pp8 n8 bl8 go8) := by
  have hst : (E8.get pp8).block.IsStructure 0 0 := t_pp8 ▸ ppStruct
  have hgo : TrM E8 B8 [`u] (ΓG n8 bl8)
      (((MLCtx.pushLam [] none).pushLam none).pushLam none)
      (.app (.app (.app (.const `N.brecOn.go [uu]) (.bvar 2)) (.bvar 1)) (.bvar 0)) (goAppM go8) :=
    TrM.app (notSpecial_const B8_go ⟨_, rfl⟩) (TrM.app (notSpecial_const B8_go ⟨_, rfl⟩)
      (TrM.app (notSpecial_const B8_go ⟨_, rfl⟩) (tr_const1 B8_go rfl) (TrM.bvar rfl))
      (TrM.bvar rfl)) (TrM.bvar rfl)
  have hty : E8[ΓG n8 bl8] ⊢ goAppM go8 : .ind pp8 0 ![lu, m1M]
      ![.app #0 #1, belowM bl8 lu #0 #1] Fin.elim0 :=
    goAppM_typed wf8 t_n8 t_pp8 t_bt8 t_gt8
  have hp := TrM.projStruct (S := `PProd) (i := 0) hst (by decide) B8_PP hgo (typedExt_self hty)
  rw [projTerm_eqFst hst t_pp8] at hp
  exact TrM.lam (TrM.forallE (tr_N B8_N) (TrM.sort rfl)) (TrM.lam (tr_N B8_N) (TrM.lam tr_F1Ty8 hp))

theorem henv9 : ProgEnv (.defnInfo N_brecOn :: .defnInfo N_brecOn_go :: .defnInfo N_below ::
    .defnInfo N_casesOn :: P5) ζ9 E9 B9 :=
  ProgEnv.defn henv8 (by decide) (by decide) rfl rfl tr_brecOnTy tr_brecOnVal

/-! ### `add.match_1` in `E9`/`B9` -/

theorem B9_N : B9 `N = some (.ind n9 0) := rfl
theorem B9_z : B9 `N.z = some (.ctor n9 0 0 []) := rfl
theorem B9_s : B9 `N.s = some (.ctor n9 0 1 [0]) := rfl
theorem B9_Unit : B9 `Unit = some (.const u9) := rfl
theorem B9_UnitU : B9 `Unit.unit = some (.const uu9) := rfl
theorem B9_casesOn : B9 `N.casesOn = some (.const c9) := rfl

theorem tr_matchTy : TrM E9 B9 [`u_1] .nil [] matchTy (matchTyM n9 u9) :=
  TrM.forallE (TrM.forallE (tr_N B9_N) (TrM.sort rfl)) (TrM.forallE (tr_N B9_N)
    (TrM.forallE (TrM.forallE (tr_const0 B9_Unit)
        (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_Z B9_z)))
      (TrM.forallE (TrM.forallE (tr_N B9_N)
          (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_S B9_s (TrM.bvar rfl))))
        (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl)))))

theorem tr_matchVal : TrM E9 B9 [`u_1] .nil [] matchVal (matchValM n9 u9 uu9 c9) :=
  TrM.lam (TrM.forallE (tr_N B9_N) (TrM.sort rfl)) (TrM.lam (tr_N B9_N)
    (TrM.lam (TrM.forallE (tr_const0 B9_Unit) (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_Z B9_z)))
      (TrM.lam (TrM.forallE (tr_N B9_N)
          (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_S B9_s (TrM.bvar rfl))))
        (TrM.app (notSpecial_const B9_casesOn ⟨_, rfl⟩)
          (TrM.app (notSpecial_const B9_casesOn ⟨_, rfl⟩)
            (TrM.app (notSpecial_const B9_casesOn ⟨_, rfl⟩)
              (TrM.app (notSpecial_const B9_casesOn ⟨_, rfl⟩) (tr_const1 B9_casesOn rfl)
                (TrM.lam (tr_N B9_N) (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl))))
              (TrM.bvar rfl))
            (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_const0 B9_UnitU)))
          (TrM.lam (tr_N B9_N) (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl)))))))

theorem henv10 : ProgEnv (.defnInfo add_match_1 :: .defnInfo N_brecOn :: .defnInfo N_brecOn_go ::
    .defnInfo N_below :: .defnInfo N_casesOn :: P5) ζ10 E10 B10 :=
  ProgEnv.defn henv9 (by decide) (by decide) rfl rfl tr_matchTy tr_matchVal

/-! ### `add._f` in `E10`/`B10` -/

theorem B10_N : B10 `N = some (.ind n10 0) := rfl
theorem B10_z : B10 `N.z = some (.ctor n10 0 0 []) := rfl
theorem B10_s : B10 `N.s = some (.ctor n10 0 1 [0]) := rfl
theorem B10_PP : B10 `PProd = some (.ind pp10 0) := rfl
theorem B10_Unit : B10 `Unit = some (.const u10) := rfl
theorem B10_below : B10 `N.below = some (.const bl10) := rfl
theorem B10_match : B10 `add.match_1 = some (.const m10) := rfl

section TrF
variable {n : Nat} {Γ : Ctx ζ10 ([] : List Name).length 0 n} {Δ : MLCtx ζ10 ([] : List Name).length n}

theorem tr_motN : TrM E10 B10 [] Γ Δ motN (motNL n10) := TrM.lam (tr_N B10_N) (tr_N B10_N)

theorem tr_belowN {a : Lean.Expr} {a' : Metalean.Expr ζ10 0 n} (ha : TrM E10 B10 [] Γ Δ a a') :
    TrM E10 B10 [] Γ Δ (belowN a) (belowM bl10 one (motNL n10) a') :=
  tr_below B10_below rfl tr_motN ha

end TrF

theorem tr_fTy : TrM E10 B10 [] .nil [] fTy (fTyM n10 bl10) :=
  TrM.forallE (tr_N B10_N) (TrM.forallE (tr_N B10_N)
    (TrM.forallE (tr_belowN (TrM.bvar rfl)) (tr_N B10_N)))

/-- The context of `add._f`'s second minor premise's body: `n m f k x`. -/
def Γ5F : Ctx ζ10 0 0 5 :=
  ((ΓF n10 bl10).snoc (mN n10)).snoc (belowM bl10 one (motNL n10) (mS n10 #3))

theorem Γ5F_wf : E10[Γ5F] ⊢ ok := by
  have hb : ∀ {n : Nat} {Γ : Ctx ζ10 0 0 n} {a : Expr ζ10 0 n}, E10[Γ] ⊢ a : mN n10 →
      E10[Γ] ⊢ belowM bl10 one (motNL n10) a : .sort (m1 one) := fun ha =>
    belowM_typed wf10 t_bt10 (motNL_typed t_n10) ha
  have h1 : E10[(#t[mN n10] : Ctx ζ10 0 0 1)] ⊢ ok := .snoc .nil ⟨_, mN_typed t_n10⟩
  have h2 : E10[(#t[mN n10, mN n10] : Ctx ζ10 0 0 2)] ⊢ ok := .snoc h1 ⟨_, mN_typed t_n10⟩
  have hΓ : E10[ΓF n10 bl10] ⊢ ok := .snoc h2 ⟨_, hb (var_of_get h2 ⟨1, by decide⟩ (by rsx))⟩
  have h4 : E10[(ΓF n10 bl10).snoc (mN n10)] ⊢ ok := .snoc hΓ ⟨_, mN_typed t_n10⟩
  exact .snoc h4 ⟨_, hb (mS_typed t_n10 (var_of_get h4 ⟨3, by decide⟩ (by rsx)))⟩

theorem x_typed : E10[Γ5F] ⊢ #4 : .ind pp10 0 ![one, m1 one]
    ![.app (motNL n10) #3, belowM bl10 one (motNL n10) #3] Fin.elim0 := by
  have hΓ := Γ5F_wf
  have hk : E10[Γ5F] ⊢ #3 : mN n10 := var_of_get hΓ ⟨3, by decide⟩ (by rsx [Γ5F])
  have hx : E10[Γ5F] ⊢ #4 : belowM bl10 one (motNL n10) (mS n10 #3) :=
    var_of_get hΓ ⟨4, by decide⟩ (by rsx [Γ5F])
  exact .defeqDF (belowS_defeq_motNL wf10 t_n10 t_pp10 t_bt10 t_bv10 hΓ (motNL_typed t_n10) hk) hx

theorem tr_fVal : TrM E10 B10 [] .nil [] fVal (fValM pp10 n10 u10 bl10 m10) := by
  have hst : (E10.get pp10).block.IsStructure 0 0 := t_pp10 ▸ ppStruct
  have hp := TrM.projStruct (E := E10) (B := B10) (lps := []) (Γ := Γ5F)
    (Δ := MLCtx.pushLam (MLCtx.pushLam (MLCtx.pushLam (MLCtx.pushLam (MLCtx.pushLam
      ([] : MLCtx ζ10 0 0) none) none) none) none) none) (S := `PProd) (i := 0) (e := .bvar 0)
    (e' := #4) hst (by decide) B10_PP (TrM.bvar rfl)
    (typedExt_self x_typed)
  rw [projTerm_eqFstF hst t_pp10] at hp
  exact TrM.lam (tr_N B10_N) (TrM.lam (tr_N B10_N) (TrM.lam (tr_belowN (TrM.bvar rfl))
    (TrM.app (notSpecial_const B10_match ⟨_, rfl⟩)
      (TrM.app (notSpecial_const B10_match ⟨_, rfl⟩)
        (TrM.app (notSpecial_const B10_match ⟨_, rfl⟩)
          (TrM.app (notSpecial_const B10_match ⟨_, rfl⟩)
            (TrM.app (notSpecial_const B10_match ⟨_, rfl⟩) (tr_const1 B10_match rfl)
              (TrM.lam (tr_N B10_N) (TrM.forallE (tr_belowN (TrM.bvar rfl)) (tr_N B10_N))))
            (TrM.bvar rfl))
          (TrM.lam (tr_const0 B10_Unit) (TrM.lam (tr_belowN (tr_Z B10_z)) (TrM.bvar rfl))))
        (TrM.lam (tr_N B10_N) (TrM.lam (tr_belowN (tr_S B10_s (TrM.bvar rfl)))
          (tr_S B10_s hp))))
      (TrM.bvar rfl))))

theorem henv11 : ProgEnv (.defnInfo add_f :: .defnInfo add_match_1 :: .defnInfo N_brecOn ::
    .defnInfo N_brecOn_go :: .defnInfo N_below :: .defnInfo N_casesOn :: P5) ζ11 E11 B11 :=
  ProgEnv.defn henv10 (by decide) (by decide) rfl rfl tr_fTy tr_fVal

/-! ### `add` in `E11`/`B11` -/

theorem B11_N : B11 `N = some (.ind n11 0) := rfl
theorem B11_brecOn : B11 `N.brecOn = some (.const br11) := rfl
theorem B11_f : B11 `add._f = some (.const f11) := rfl

theorem tr_addTy : TrM E11 B11 [] .nil [] addTy (addTyM n11) :=
  TrM.forallE (tr_N B11_N) (TrM.forallE (tr_N B11_N) (tr_N B11_N))

theorem tr_addVal : TrM E11 B11 [] .nil [] addVal (addValM n11 br11 f11) :=
  TrM.lam (tr_N B11_N) (TrM.lam (tr_N B11_N)
    (TrM.app (notSpecial_const B11_brecOn ⟨_, rfl⟩)
      (TrM.app (notSpecial_const B11_brecOn ⟨_, rfl⟩)
        (TrM.app (notSpecial_const B11_brecOn ⟨_, rfl⟩) (tr_const1 B11_brecOn rfl)
          (TrM.lam (tr_N B11_N) (tr_N B11_N)))
        (TrM.bvar rfl))
      (TrM.app (notSpecial_const B11_f ⟨_, rfl⟩) (tr_const0 B11_f) (TrM.bvar rfl))))

theorem henv12 : ProgEnv P ζ12 E12 B12 :=
  ProgEnv.defn henv11 (by decide) (by decide) rfl rfl tr_addTy tr_addVal

/-! ## The erased term `add (N.s N.z) (N.s N.z)` in `E12`/`B12` -/

theorem B12_add : B12 `add = some (.const a12) := rfl
theorem B12_z : B12 `N.z = some (.ctor n12 0 0 []) := rfl
theorem B12_s : B12 `N.s = some (.ctor n12 0 1 [0]) := rfl

/-- `N.s N.z`. -/
def mjM {n : Nat} : Expr ζ12 0 n := mS n12 (mZ n12)

/-- The erased term in Metalean. -/
def tE : Expr ζ12 0 0 := .app (.app (.const a12 Fin.elim0) mjM) mjM

theorem tr_e : TrM E12 B12 [] .nil [] e tE :=
  TrM.app (notSpecial_const B12_add ⟨_, rfl⟩)
    (TrM.app (notSpecial_const B12_add ⟨_, rfl⟩) (tr_const0 B12_add) (tr_S B12_s (tr_Z B12_z)))
    (tr_S B12_s (tr_Z B12_z))

theorem tE_typed : E12[.nil] ⊢ tE : mN n12 := by
  have hmj : E12[(.nil : Ctx ζ12 0 0 0)] ⊢ mjM : mN n12 := mS_typed t_n12 (mZ_typed t_n12)
  have h0 : E12[(.nil : Ctx ζ12 0 0 0)] ⊢ .const a12 Fin.elim0 :
      .forallE (mN n12) (.forallE (mN n12) (mN n12)) :=
    const_typed wf12 a12 Fin.elim0 (by rw [t_at12]; rsx [addTyM])
  have h1 := app_typed' h0 hmj (by rsx)
  rsx at h1
  exact typed_of_eq (app_typed' h1 hmj (by rsx)) (by rsx)

/-! ## The premises -/

/-- The Metalean environment of NV-S. -/
abbrev E : Env ζ12 := E12
/-- The name table of NV-S. -/
abbrev B : Binds ζ12 := B12

/-- `henv`: the program is the Lean form of `E` with table `B`. -/
theorem henv : ProgEnv P ζ12 E B := henv12

/-- `hwf`: `E` is well formed. -/
theorem hwf : EnvWF E := wf12

/-- `he`: the erased term is the Lean form of `tE`. -/
theorem he : TrM E B [] .nil [] e tE := tr_e

/-- `hty`: `tE` is typed. -/
theorem hty : ∃ T, E[.nil] ⊢ tE : T := ⟨_, tE_typed⟩

end EraseProof.Test.NVS
