import EraseProof.Test.NVAOfNat
import EraseProof.Test.NVAData
import EraseProof.Test.NVSModel

/-!
# NV-A: the Metalean model of the program

The premises of the final theorem about the program and its model, for NV-A
(`Test/NVAData.lean`): the program `P` is the Lean form of the well-formed Metalean environment
`E13` with name table `B13` (`henv`, `hwf`), and the erased term `e` is the Lean form of the closed
Metalean term `tE`, which is typed (`he`, `hty`). The environment holds, oldest first, the blocks
of `PUnit`, `PProd` and `Nat` (at the signature `natSig` of the literals' translation, `TrM.lit`),
the definitions `Nat.casesOn`, `Nat.below`, `Nat.brecOn.go`, `Nat.brecOn`, `Nat.add.match_1`,
`Nat.add._f` and `Nat.add`, the block of `OfNat`, and the definitions `OfNat.ofNat` and
`instOfNatNat`, whose values are typed by `Test/NVADefs.lean`, `Test/NVAFuns.lean` and
`Test/NVAOfNat.lean`. The inductive types of the program have no indices.
-/

open Lean Metalean

namespace EraseProof.Test.NVA

open EraseProof.Test.NV1 (typed_of_eq var_of_get app_typed const_typed fin0_eq lu notSpecial_bvar
  notSpecial_const trLevels_nil)
open EraseProof.Test.NVP (trLevels_one trLevels_two)
open EraseProof.Test.NVS (puSig ppSig puBlock ppBlock mPU mPUu mPP mPPmk ppLevel ppStruct
  ppParams mPP_defeq mPP_typed mPPmk_typed mPU_typed mPUu_typed one puBlock_wf ppBlock_wf
  largeElimPU largeElimPP ζ1 pu1 E1 B1 henv1 IsPU CsPU RsPU wf1 tr_PU tr_PUu tr_PP tr_PPmk
  tr_const0 tr_const1 trM_eq typedExt_self indTerm_eqPP ctorTerm_eqPP recrTerm_eqPP ppTermM
  ppMkTermM ppRecTermM ppTyM ppMkTyM ppRecTyM ppTermM_typed ppMkTermM_typed ppRecTermM_typed
  IsPP CsPP RsPP ordersPP PPP_eq r0 r1 r2 q0 q1 PProd_ind PProd_mk PProd_rec PUnit_ind PUnit_unit
  PUnit_rec uu u1 l1 m1u tPU cPU tPP cPP trL_u trL_m1u trL_sm1u trL_u1 trL_one app_typed')
open EraseProof.Test.NVL (nSig nBlock mN mZ mS mN_typed mZ_typed mS_typed indN_typed recAllowedN
  appMotN_typed motN_typed nBlock_wf tN cZ cS Nat_ind Zero_ctor Succ_ctor Nat_rec sTy recTy
  sTyM sTermM recTyM recTermM ordersN ctorTerm_eqN recrTerm_eqN sTermM_typed largeElimN
  recTermM_typed IsN CsN RsN PN_eq tr_N tr_Z tr_S)

/-! ## The environments -/

abbrev ζ2 : Sigs := ζ1.snoc (.inductive ppSig)
abbrev ζ3 : Sigs := ζ2.snoc (.inductive nSig)
abbrev ζ4 : Sigs := ζ3.snoc (.const .def 1)
abbrev ζ5 : Sigs := ζ4.snoc (.const .def 1)
abbrev ζ6 : Sigs := ζ5.snoc (.const .def 1)
abbrev ζ7 : Sigs := ζ6.snoc (.const .def 1)
abbrev ζ8 : Sigs := ζ7.snoc (.const .def 1)
abbrev ζ9 : Sigs := ζ8.snoc (.const .def 0)
abbrev ζ10 : Sigs := ζ9.snoc (.const .def 0)
abbrev ζ11 : Sigs := ζ10.snoc (.inductive ofSig)
abbrev ζ12 : Sigs := ζ11.snoc (.const .def 1)
abbrev ζ13 : Sigs := ζ12.snoc (.const .def 0)

abbrev pp2 : Head ζ2 (.inductive ppSig) := .here
abbrev n3 : Head ζ3 (.inductive nSig) := .here
abbrev pu4 : Head ζ4 (.inductive puSig) := .there (.there (.there .here))
abbrev pp4 : Head ζ4 (.inductive ppSig) := .there (.there .here)
abbrev n4 : Head ζ4 (.inductive nSig) := .there .here
abbrev pu5 : Head ζ5 (.inductive puSig) := .there (.there (.there (.there .here)))
abbrev pp5 : Head ζ5 (.inductive ppSig) := .there (.there (.there .here))
abbrev n5 : Head ζ5 (.inductive nSig) := .there (.there .here)
abbrev bl5 : Head ζ5 (.const .def 1) := .here
abbrev pp6 : Head ζ6 (.inductive ppSig) := .there (.there (.there (.there .here)))
abbrev n6 : Head ζ6 (.inductive nSig) := .there (.there (.there .here))
abbrev bl6 : Head ζ6 (.const .def 1) := .there .here
abbrev go6 : Head ζ6 (.const .def 1) := .here
abbrev n7 : Head ζ7 (.inductive nSig) := .there (.there (.there (.there .here)))
abbrev c7 : Head ζ7 (.const .def 1) := .there (.there (.there .here))
abbrev pu8 : Head ζ8 (.inductive puSig) :=
  .there (.there (.there (.there (.there (.there (.there .here))))))
abbrev pp8 : Head ζ8 (.inductive ppSig) := .there (.there (.there (.there (.there (.there .here)))))
abbrev n8 : Head ζ8 (.inductive nSig) := .there (.there (.there (.there (.there .here))))
abbrev bl8 : Head ζ8 (.const .def 1) := .there (.there (.there .here))
abbrev m8 : Head ζ8 (.const .def 1) := .here
abbrev n9 : Head ζ9 (.inductive nSig) := .there (.there (.there (.there (.there (.there .here)))))
abbrev bl9 : Head ζ9 (.const .def 1) := .there (.there (.there (.there .here)))
abbrev br9 : Head ζ9 (.const .def 1) := .there (.there .here)
abbrev f9 : Head ζ9 (.const .def 0) := .here
abbrev n10 : Head ζ10 (.inductive nSig) :=
  .there (.there (.there (.there (.there (.there (.there .here))))))
abbrev n11 : Head ζ11 (.inductive nSig) :=
  .there (.there (.there (.there (.there (.there (.there (.there .here)))))))
abbrev o11 : Head ζ11 (.inductive ofSig) := .here
abbrev n12 : Head ζ12 (.inductive nSig) :=
  .there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
abbrev o12 : Head ζ12 (.inductive ofSig) := .there .here
abbrev n13 : Head ζ13 (.inductive nSig) :=
  .there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
abbrev a13 : Head ζ13 (.const .def 0) := .there (.there (.there .here))
abbrev on13 : Head ζ13 (.const .def 1) := .there .here
abbrev i13 : Head ζ13 (.const .def 0) := .here

def E2 : Env ζ2 := E1.snoc (.inductive ppBlock)
def E3 : Env ζ3 := E2.snoc (.inductive nBlock)
def E4 : Env ζ4 := E3.snoc (.def (casesOnTyM n3) (casesOnValM n3))
def E5 : Env ζ5 := E4.snoc (.def (belowTyM n4) (belowValM pu4 pp4 n4))
def E6 : Env ζ6 := E5.snoc (.def (goTyM pp5 n5 bl5) (goValM pu5 pp5 n5 bl5))
def E7 : Env ζ7 := E6.snoc (.def (brecOnTyM n6 bl6) (brecOnValM pp6 n6 bl6 go6))
def E8 : Env ζ8 := E7.snoc (.def (matchTyM n7) (matchValM n7 c7))
def E9 : Env ζ9 := E8.snoc (.def (fTyM n8 bl8) (fValM pp8 n8 bl8 m8))
def E10 : Env ζ10 := E9.snoc (.def (addTyM n9) (addValM n9 br9 f9))
def E11 : Env ζ11 := E10.snoc (.inductive (ofBlock n10))
def E12 : Env ζ12 := E11.snoc (.def (ofNatTyM n11 o11) (ofNatValM n11 o11))
def E13 : Env ζ13 := E12.snoc (.def (instTyM n12 o12) (instValM n12 o12))

/-- Read a head's entry of the environments. -/
syntax (name := _envsA) "aenvs" : tactic
macro_rules
  | `(tactic| aenvs) => `(tactic| simp! [E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11, E12, E13,
  Env.get, Entry.block, Entry.constType, Entry.defValue, belowTyM, belowValM, minsBl, casesOnTyM,
  goTyM, F1TyM, pairM, belowM, brecOnTyM, matchTyM, motMM, H1M, H2M, fTyM, nnM, addTyM, motNM,
  EraseProof.Test.NVL.motN, mN, mZ, mS, mPU, mPP, motNL, ofNatTyM, instTyM, mOf, funext_iff,
  Fin.forall_fin_one, Fin.forall_fin_two, fin0_eq])

theorem t_pp2 : (E2.get pp2).block = ppBlock := by aenvs
theorem t_n3 : (E3.get n3).block = nBlock := by aenvs
theorem t_n4 : (E4.get n4).block = nBlock := by aenvs
theorem t_pu4 : (E4.get pu4).block = puBlock := by aenvs
theorem t_pp4 : (E4.get pp4).block = ppBlock := by aenvs
theorem t_n5 : (E5.get n5).block = nBlock := by aenvs
theorem t_pu5 : (E5.get pu5).block = puBlock := by aenvs
theorem t_pp5 : (E5.get pp5).block = ppBlock := by aenvs
theorem t_bt5 : (E5.get bl5).constType = belowTyM n5 := by aenvs
theorem t_bv5 : (E5.get bl5).defValue = belowValM pu5 pp5 n5 := by aenvs
theorem t_n6 : (E6.get n6).block = nBlock := by aenvs
theorem t_pp6 : (E6.get pp6).block = ppBlock := by aenvs
theorem t_bt6 : (E6.get bl6).constType = belowTyM n6 := by aenvs
theorem t_gt6 : (E6.get go6).constType = goTyM pp6 n6 bl6 := by aenvs
theorem t_n7 : (E7.get n7).block = nBlock := by aenvs
theorem t_ct7 : (E7.get c7).constType = casesOnTyM n7 := by aenvs
theorem t_n8 : (E8.get n8).block = nBlock := by aenvs
theorem t_pp8 : (E8.get pp8).block = ppBlock := by aenvs
theorem t_bt8 : (E8.get bl8).constType = belowTyM n8 := by aenvs
theorem t_bv8 : (E8.get bl8).defValue = belowValM pu8 pp8 n8 := by aenvs
theorem t_mt8 : (E8.get m8).constType = matchTyM n8 := by aenvs
theorem t_n9 : (E9.get n9).block = nBlock := by aenvs
theorem t_brt9 : (E9.get br9).constType = brecOnTyM n9 bl9 := by aenvs
theorem t_ft9 : (E9.get f9).constType = fTyM n9 bl9 := by aenvs
theorem t_bt9 : (E9.get bl9).constType = belowTyM n9 := by aenvs
theorem t_n10 : (E10.get n10).block = nBlock := by aenvs
theorem t_n11 : (E11.get n11).block = nBlock := by aenvs
theorem t_o11 : (E11.get o11).block = ofBlock n11 := by aenvs
theorem t_n12 : (E12.get n12).block = nBlock := by aenvs
theorem t_o12 : (E12.get o12).block = ofBlock n12 := by aenvs
theorem t_n13 : (E13.get n13).block = nBlock := by aenvs
theorem t_at13 : (E13.get a13).constType = addTyM n13 := by aenvs
theorem t_ont13 : (E13.get on13).constType = ofNatTyM n13 (.there (.there .here)) := by aenvs
theorem t_it13 : (E13.get i13).constType = instTyM n13 (.there (.there .here)) := by aenvs
theorem t_o13 : (E13.get (.there (.there .here) : Head ζ13 (.inductive ofSig))).block =
    ofBlock n13 := by aenvs

/-! ## Well-formedness -/

theorem wf2 : EnvWF E2 := .snoc wf1 (.inductive (ppBlock_wf _))
theorem wf3 : EnvWF E3 := .snoc wf2 (.inductive (nBlock_wf _))
theorem wf4 : EnvWF E4 := .snoc wf3 (.def (casesOnTyM_isType t_n3) (casesOnValM_typed t_n3))
theorem wf5 : EnvWF E5 :=
  .snoc wf4 (.def (belowTyM_isType t_n4 t_pu4 t_pp4) (belowValM_typed t_n4 t_pu4 t_pp4))
theorem wf6 : EnvWF E6 :=
  .snoc wf5 (.def (goTyM_isType wf5 t_n5 t_pu5 t_pp5 t_bt5 t_bv5)
    (goValM_typed wf5 t_n5 t_pu5 t_pp5 t_bt5 t_bv5))
theorem wf7 : EnvWF E7 :=
  .snoc wf6 (.def (brecOnTyM_isType wf6 t_n6 t_pp6 t_bt6 t_gt6)
    (brecOnValM_typed wf6 t_n6 t_pp6 t_bt6 t_gt6))
theorem wf8 : EnvWF E8 :=
  .snoc wf7 (.def (matchValM_typed wf7 t_n7 t_ct7).regular (matchValM_typed wf7 t_n7 t_ct7))
theorem wf9 : EnvWF E9 :=
  .snoc wf8 (.def (fValM_typed wf8 t_n8 t_pp8 t_bt8 t_bv8 t_mt8).regular
    (fValM_typed wf8 t_n8 t_pp8 t_bt8 t_bv8 t_mt8))
theorem wf10 : EnvWF E10 :=
  .snoc wf9 (.def (addValM_typed wf9 t_n9 t_brt9 t_ft9 t_bt9).regular
    (addValM_typed wf9 t_n9 t_brt9 t_ft9 t_bt9))
theorem wf11 : EnvWF E11 := .snoc wf10 (.inductive (ofBlock_wf t_n10))
theorem wf12 : EnvWF E12 :=
  .snoc wf11 (.def (ofNatValM_typed wf11 t_n11 t_o11).regular (ofNatValM_typed wf11 t_n11 t_o11))
theorem wf13 : EnvWF E13 :=
  .snoc wf12 (.def (instValM_typed t_n12 t_o12).regular (instValM_typed t_n12 t_o12))

/-! ## Name tables -/

def B2 : Binds ζ2 := fun n =>
  if n = `PProd then some (.ind pp2 0)
  else if n = `PProd.mk then some (.ctor pp2 0 0 [0, 1])
  else if n = `PProd.rec then some (.recr pp2 0 [[[0, 1]]])
  else Binds.wk B1 n
def B3 : Binds ζ3 := fun n =>
  if n = `Nat then some (.ind n3 0)
  else if n = `Nat.zero then some (.ctor n3 0 0 [])
  else if n = `Nat.succ then some (.ctor n3 0 1 [0])
  else if n = `Nat.rec then some (.recr n3 0 [[[], [0]]])
  else Binds.wk B2 n
def B4 : Binds ζ4 := (Binds.wk B3).set `Nat.casesOn (.const .here)
def B5 : Binds ζ5 := (Binds.wk B4).set `Nat.below (.const .here)
def B6 : Binds ζ6 := (Binds.wk B5).set `Nat.brecOn.go (.const .here)
def B7 : Binds ζ7 := (Binds.wk B6).set `Nat.brecOn (.const .here)
def B8 : Binds ζ8 := (Binds.wk B7).set `Nat.add.match_1 (.const .here)
def B9 : Binds ζ9 := (Binds.wk B8).set `Nat.add._f (.const .here)
def B10 : Binds ζ10 := (Binds.wk B9).set `Nat.add (.const .here)
def B11 : Binds ζ11 := fun n =>
  if n = `OfNat then some (.ind o11 0)
  else if n = `OfNat.mk then some (.ctor o11 0 0 [0])
  else if n = `OfNat.rec then some (.recr o11 0 [[[0]]])
  else Binds.wk B10 n
def B12 : Binds ζ12 := (Binds.wk B11).set `OfNat.ofNat (.const .here)
def B13 : Binds ζ13 := (Binds.wk B12).set `instOfNatNat (.const .here)

/-! ## The block of `PProd` in `E2`/`B2` -/

theorem B2_PP : B2 `PProd = some (.ind pp2 0) := rfl
theorem B2_PPmk : B2 `PProd.mk = some (.ctor pp2 0 0 [0, 1]) := rfl
theorem B2_PPrec : B2 `PProd.rec = some (.recr pp2 0 [[[0, 1]]]) := rfl

theorem tr_ppTy : TrM E2 B2 [`u, `v] .nil [] PProd_ind.type ppTyM :=
  TrM.forallE (TrM.sort rfl) (TrM.forallE (TrM.sort rfl) (TrM.sort rfl))

theorem tr_ppConst : TrM E2 B2 [`u, `v] .nil [] (.const `PProd [.param `u, .param `v])
    (ppTermM pp2) := by
  have h := TrM.special (E := E2) (B := B2) (lps := [`u, `v]) (Γ := .nil) (Δ := [])
    (c := `PProd) (us := [.param `u, .param `v]) (as := []) (as' := []) B2_PP rfl rfl
    (fun _ _ _ h => nomatch h)
    (SatTr.indEta (E := E2) (lps := [`u, `v]) (args := []) (η := pp2) (s := 0)
      (us := [.param `u, .param `v]) (ls := ![q0, q1]) (trLevels_two rfl rfl) (by decide))
  rw [indTerm_eqPP t_pp2] at h
  exact h

theorem tr_ppMkTy : TrM E2 B2 [`u, `v] .nil [] PProd_mk.type (ppMkTyM pp2) :=
  TrM.forallE (TrM.sort rfl) (TrM.forallE (TrM.sort rfl) (TrM.forallE (TrM.bvar rfl)
    (TrM.forallE (TrM.bvar rfl) (tr_PP B2_PP rfl rfl (TrM.bvar rfl) (TrM.bvar rfl)))))

theorem tr_ppMk : TrM E2 B2 [`u, `v] .nil [] (.const `PProd.mk [.param `u, .param `v])
    (ppMkTermM pp2) :=
  TrM.special (as := []) (as' := []) B2_PPmk rfl rfl (fun _ _ _ h => nomatch h)
    (SatTr.ctorEta (args := []) (η := pp2) (s := 0) (c := 0) (order := [0, 1])
      (trLevels_two rfl rfl) (by decide) (ctorTerm_eqPP t_pp2))

theorem tr_ppRecTy : TrM E2 B2 [`u_1, `u, `v] .nil [] PProd_rec.type (ppRecTyM pp2) :=
  TrM.forallE (TrM.sort rfl) (TrM.forallE (TrM.sort rfl)
    (TrM.forallE (TrM.forallE (tr_PP B2_PP rfl rfl (TrM.bvar rfl) (TrM.bvar rfl)) (TrM.sort rfl))
      (TrM.forallE (TrM.forallE (TrM.bvar rfl) (TrM.forallE (TrM.bvar rfl)
          (TrM.app notSpecial_bvar (TrM.bvar rfl)
            (tr_PPmk B2_PPmk rfl rfl (TrM.bvar rfl) (TrM.bvar rfl) (TrM.bvar rfl) (TrM.bvar rfl)))))
        (TrM.forallE (tr_PP B2_PP rfl rfl (TrM.bvar rfl) (TrM.bvar rfl))
          (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl))))))

theorem tr_ppRec : TrM E2 B2 [`u_1, `u, `v] .nil []
    (.const `PProd.rec [.param `u_1, .param `u, .param `v]) (ppRecTermM pp2) :=
  TrM.special (as := []) (as' := []) B2_PPrec rfl rfl (fun _ _ _ h => nomatch h)
    (SatTr.recrEta (E := E2) (lps := [`u_1, `u, `v]) (args := []) (η := pp2) (s := 0)
      (us := [.param `u_1, .param `u, .param `v]) (us' := [.param `u, .param `v]) (l := r0)
      (ls := ![r1, r2]) (fun _ _ => [0, 1]) (Or.inl ⟨by rw [t_pp2]; exact largeElimPP, _, rfl, rfl⟩)
      (trLevels_two rfl rfl) (by intro t c; fin_cases t; fin_cases c; rfl) (by decide)
      (recrTerm_eqPP t_pp2))

theorem indBlockPP : IndBlock E2 B2 pp2 [`u, `v] IsPP CsPP RsPP ordersPP where
  levels := rfl
  ind s := by fin_cases s; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  ctor s c := by
    fin_cases s; fin_cases c
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, [0, 1], [], rfl, rfl, rfl, by decide, .nil,
      List.Perm.refl _⟩
  ctorType s c := by fin_cases s; fin_cases c; exact ⟨_, [], rfl, rfl, rfl⟩
  recr s := by
    fin_cases s
    exact ⟨rfl, rfl, fun _ => ⟨`u_1, rfl⟩, fun h => absurd (by rw [t_pp2]; exact largeElimPP) h,
      rfl, rfl, rfl, rfl, rfl, rfl⟩
  recrType s := by fin_cases s; rfl
  recMajor s := by fin_cases s; exact ⟨_, _, _, _, _, rfl, rfl⟩
  minors s t c := by fin_cases s; fin_cases t; fin_cases c; rfl
  recIHs s := by
    fin_cases s
    exact ⟨_, _, rfl, rfl, fun t c => by fin_cases t; fin_cases c; rfl⟩
  indexVars s _ h := by fin_cases s; exact h.elim fun i _ => i.elim0

theorem constTypedPP : ∀ ci ∈ IndBlock.decls IsPP CsPP RsPP, ConstTyped E2 B2 ci := by
  rw [PPP_eq]
  intro ci hci
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hci
  rcases hci with rfl | rfl | rfl
  · exact ⟨_, _, tr_ppRecTy, tr_ppRec, ppRecTermM_typed t_pp2⟩
  · exact ⟨_, _, tr_ppMkTy, tr_ppMk, ppMkTermM_typed t_pp2⟩
  · exact ⟨_, _, tr_ppTy, tr_ppConst, ppTermM_typed t_pp2⟩

def P1 : List ConstantInfo := IndBlock.decls IsPU CsPU RsPU

theorem henv2 : ProgEnv (IndBlock.decls IsPP CsPP RsPP ++ P1) ζ2 E2 B2 :=
  ProgEnv.induct (I := ppBlock) (lps := [`u, `v]) (orders := ordersPP) henv1 (by decide)
    (by rw [PPP_eq]; decide) (by decide)
    (fun n hn => by
      rw [PPP_eq] at hn
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
        not_or] at hn
      obtain ⟨h1, h2, h3⟩ := hn
      have h1' : n ≠ `PProd.rec := h1
      have h2' : n ≠ `PProd.mk := h2
      have h3' : n ≠ `PProd := h3
      simp [B2, h1', h2', h3'])
    indBlockPP constTypedPP

/-! ## The block of `Nat` in `E3`/`B3` -/

theorem B3_N : B3 `Nat = some (.ind n3 0) := rfl
theorem B3_z : B3 `Nat.zero = some (.ctor n3 0 0 []) := rfl
theorem B3_s : B3 `Nat.succ = some (.ctor n3 0 1 [0]) := rfl
theorem B3_rec : B3 `Nat.rec = some (.recr n3 0 [[[], [0]]]) := rfl

def P2 : List ConstantInfo := IndBlock.decls IsPP CsPP RsPP ++ P1

theorem tr_recTy3 : TrM E3 B3 [`u] .nil [] recTy (recTyM n3) :=
  TrM.forallE (TrM.forallE (tr_N B3_N) (TrM.sort rfl))
    (TrM.forallE (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_Z B3_z))
      (TrM.forallE (TrM.forallE (tr_N B3_N) (TrM.forallE
          (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl))
          (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_S B3_s (TrM.bvar rfl)))))
        (TrM.forallE (tr_N B3_N) (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl)))))

theorem tr_rec3 : TrM E3 B3 [`u] .nil [] (.const `Nat.rec [.param `u]) (recTermM n3) := by
  refine TrM.special (as := []) (as' := []) B3_rec rfl rfl (fun _ _ _ h => nomatch h) ?_
  refine SatTr.recrEta (E := E3) (lps := [`u]) (η := n3) (s := 0) (us := [.param `u]) (us' := [])
    (ls := Fin.elim0) (l := lu) (args := []) ordersN ?_ trLevels_nil ?_ (by decide) ?_
  · exact Or.inl ⟨by rw [t_n3]; exact largeElimN, _, rfl, rfl⟩
  · intro t c; fin_cases t; fin_cases c <;> rfl
  · exact recrTerm_eqN t_n3

theorem tr_sConst3 : TrM E3 B3 [] .nil [] cS (sTermM n3) :=
  TrM.special (as := []) (as' := []) B3_s rfl rfl (fun _ _ _ h => nomatch h)
    (SatTr.ctorEta (args := []) (η := n3) (s := 0) (c := 1) (order := [0]) trLevels_nil
      (by decide) (ctorTerm_eqN t_n3))

theorem indBlockN3 : IndBlock E3 B3 n3 [] IsN CsN RsN ordersN where
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
    exact ⟨rfl, rfl, fun _ => ⟨`u, rfl⟩, fun h => absurd (by rw [t_n3]; exact largeElimN) h, rfl,
      rfl, rfl, rfl, rfl, rfl⟩
  recrType s := by fin_cases s; rfl
  recMajor s := by fin_cases s; exact ⟨_, _, _, _, _, rfl, rfl⟩
  minors s t c := by fin_cases s; fin_cases t; fin_cases c <;> rfl
  recIHs s := by
    fin_cases s
    exact ⟨_, _, rfl, rfl, fun t c => by fin_cases t; fin_cases c <;> rfl⟩
  indexVars s _ h := by fin_cases s; exact h.elim fun i _ => i.elim0

theorem constTypedN3 : ∀ ci ∈ IndBlock.decls IsN CsN RsN, ConstTyped E3 B3 ci := by
  rw [PN_eq]
  intro ci hci
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hci
  rcases hci with rfl | rfl | rfl | rfl
  · exact ⟨_, _, tr_recTy3, tr_rec3, recTermM_typed t_n3⟩
  · exact ⟨_, _, tr_N B3_N, tr_Z B3_z, mZ_typed t_n3⟩
  · exact ⟨_, _, TrM.forallE (tr_N B3_N) (tr_N B3_N), tr_sConst3, sTermM_typed t_n3⟩
  · exact ⟨_, _, TrM.sort rfl, tr_N B3_N, indN_typed t_n3⟩

theorem henv3 : ProgEnv (IndBlock.decls IsN CsN RsN ++ P2) ζ3 E3 B3 :=
  ProgEnv.induct (I := nBlock) (lps := []) (orders := ordersN) henv2 (by decide)
    (by rw [PN_eq]; decide) (by decide)
    (fun n hn => by
      rw [PN_eq] at hn
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
        not_or] at hn
      obtain ⟨h1, h2, h3, h4⟩ := hn
      have h1' : n ≠ `Nat.rec := h1
      have h2' : n ≠ `Nat.zero := h2
      have h3' : n ≠ `Nat.succ := h3
      have h4' : n ≠ `Nat := h4
      simp [B3, h1', h2', h3', h4'])
    indBlockN3 constTypedN3

/-! ## The definitions on `Nat` -/

theorem tr_below {ζ : Sigs} {E : Env ζ} {B : Binds ζ} {lps : List Name} {n : Nat}
    {Γ : Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n} {η : Head ζ (.const .def 1)}
    (h : B `Nat.below = some (.const η)) {u : Lean.Level}
    {l : Metalean.Level lps.length} (hl : TrLevel lps u = some l) {mo a : Lean.Expr}
    {mo' a' : Metalean.Expr ζ lps.length n} (hmo : TrM E B lps Γ Δ mo mo')
    (ha : TrM E B lps Γ Δ a a') :
    TrM E B lps Γ Δ (.app (.app (below u) mo) a) (belowM η l mo' a') :=
  TrM.app (notSpecial_const h ⟨_, rfl⟩) (TrM.app (notSpecial_const h ⟨_, rfl⟩) (tr_const1 h hl) hmo)
    ha

def P3 : List ConstantInfo := IndBlock.decls IsN CsN RsN ++ P2

/-! ### `Nat.casesOn` in `E3`/`B3` -/

theorem tr_casesOnTy : TrM E3 B3 [`u] .nil [] casesOnTy (casesOnTyM n3) :=
  TrM.forallE (TrM.forallE (tr_N B3_N) (TrM.sort rfl)) (TrM.forallE (tr_N B3_N)
    (TrM.forallE (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_Z B3_z))
      (TrM.forallE (TrM.forallE (tr_N B3_N)
          (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_S B3_s (TrM.bvar rfl))))
        (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl)))))

theorem tr_casesOnVal : TrM E3 B3 [`u] .nil [] casesOnVal (casesOnValM n3) := by
  have h : TrM E3 B3 [`u] .nil [] casesOnVal _ :=
    TrM.lam (TrM.forallE (tr_N B3_N) (TrM.sort rfl)) (TrM.lam (tr_N B3_N)
      (TrM.lam (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_Z B3_z))
        (TrM.lam (TrM.forallE (tr_N B3_N)
            (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_S B3_s (TrM.bvar rfl))))
          (TrM.special (c := `Nat.rec) (us := [.param `u])
            (as := [.bvar 3, .bvar 1, .lam `n tN (.lam `n_ih (.app (.bvar 4) (.bvar 0))
              (.app (.bvar 2) (.bvar 1)) .default) .default, .bvar 2])
            (as' := [#0, #2, .lam (mN n3) (.lam (.app #0 #4) (.app #3 #4)), #1]) B3_rec rfl rfl
            (by
              intro i a a' h1 h2
              rcases i with _ | _ | _ | _ | i <;> simp at h1 h2 <;> subst h1 h2
              · exact TrM.bvar rfl
              · exact TrM.bvar rfl
              · exact TrM.lam (tr_N B3_N) (TrM.lam
                  (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl))
                  (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl)))
              · exact TrM.bvar rfl)
            (SatTr.recrSat (E := E3) (lps := [`u]) (η := n3) (s := 0) (orders := [[[], [0]]])
              (us := [.param `u]) (us' := []) (ls := Fin.elim0) (l := lu) ordersN
              ![#0, #2, .lam (mN n3) (.lam (.app #0 #4) (.app #3 #4)), #1] [] (minsCO n3)
              (Or.inl ⟨by rw [t_n3]; exact largeElimN, _, rfl, rfl⟩) trLevels_nil
              (by intro t c; fin_cases t; fin_cases c <;> rfl)
              (by
                intro t c; fin_cases t; fin_cases c <;>
                  simp [Frontend.wrapCase, Frontend.isIdentityOrder] <;> rfl))))))
  exact trM_eq h (by simp only [casesOnValM]; arsx [minsCO, MLDecl.wk, MLDecl.denote]; all_goals (refine ⟨?_, ?_⟩ <;> rfl))

theorem henv4 : ProgEnv (.defnInfo Nat_casesOn :: P3) ζ4 E4 B4 :=
  ProgEnv.defn henv3 (by decide) (by decide) rfl rfl tr_casesOnTy tr_casesOnVal

/-! ### `Nat.below` in `E4`/`B4` -/

theorem B4_N : B4 `Nat = some (.ind n4 0) := rfl
theorem B4_rec : B4 `Nat.rec = some (.recr n4 0 [[[], [0]]]) := rfl
theorem B4_PU : B4 `PUnit = some (.ind pu4 0) := rfl
theorem B4_PP : B4 `PProd = some (.ind pp4 0) := rfl

theorem tr_belowTy : TrM E4 B4 [`u] .nil [] belowTy (belowTyM n4) :=
  TrM.forallE (TrM.forallE (tr_N B4_N) (TrM.sort rfl)) (TrM.forallE (tr_N B4_N) (TrM.sort rfl))

/-- The minor of `Nat.succ` in `Nat.below`'s value. -/
def blMinS : Metalean.Expr ζ4 1 2 :=
  .lam (mN n4) (.lam (.sort m1M) (mPP pp4 lu m1M (.app #0 #2) #3))

theorem tr_belowVal : TrM E4 B4 [`u] .nil [] belowVal (belowValM pu4 pp4 n4) := by
  have h : TrM E4 B4 [`u] .nil [] belowVal _ :=
    TrM.lam (TrM.forallE (tr_N B4_N) (TrM.sort rfl)) (TrM.lam (tr_N B4_N)
      (TrM.special (E := E4) (B := B4) (lps := [`u]) (c := `Nat.rec) (us := [.succ m1u])
        (as := [.lam `t tN (.sort m1u) .default, tPU m1u,
          .lam `n tN (.lam `n_ih (.sort m1u) (.app (.app (tPP uu m1u) (.app (.bvar 3) (.bvar 1)))
            (.bvar 0)) .default) .default, .bvar 0])
        (as' := [.lam (mN n4) (.sort m1M), mPU pu4 m1M, blMinS, #1]) B4_rec rfl rfl
        (by
          intro i a a' h1 h2
          rcases i with _ | _ | _ | _ | i <;> simp at h1 h2 <;> subst h1 h2
          · exact TrM.lam (tr_N B4_N) (TrM.sort rfl)
          · exact tr_PU B4_PU rfl
          · exact TrM.lam (tr_N B4_N) (TrM.lam (TrM.sort rfl)
              (tr_PP B4_PP rfl rfl (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl))
                (TrM.bvar rfl)))
          · exact TrM.bvar rfl)
        (SatTr.recrSat (E := E4) (lps := [`u]) (η := n4) (s := 0) (orders := [[[], [0]]])
          (us := [.succ m1u]) (us' := []) (ls := Fin.elim0) (l := .succ m1M) ordersN
          ![.lam (mN n4) (.sort m1M), mPU pu4 m1M, blMinS, #1] [] (minsBl pu4 pp4 n4)
          (Or.inl ⟨by rw [t_n4]; exact largeElimN, _, rfl, rfl⟩) trLevels_nil
          (by intro t c; fin_cases t; fin_cases c <;> rfl)
          (by
            intro t c; fin_cases t; fin_cases c <;>
              simp [Frontend.wrapCase, Frontend.isIdentityOrder] <;> rfl))))
  exact trM_eq h (by simp only [belowValM]; arsx [blMinS, MLDecl.wk, MLDecl.denote]; all_goals (refine ⟨?_, ?_⟩ <;> rfl))

theorem henv5 : ProgEnv (.defnInfo Nat_below :: .defnInfo Nat_casesOn :: P3) ζ5 E5 B5 :=
  ProgEnv.defn henv4 (by decide) (by decide) rfl rfl tr_belowTy tr_belowVal

/-! ### `Nat.brecOn.go` in `E5`/`B5` -/

theorem B5_N : B5 `Nat = some (.ind n5 0) := rfl
theorem B5_z : B5 `Nat.zero = some (.ctor n5 0 0 []) := rfl
theorem B5_s : B5 `Nat.succ = some (.ctor n5 0 1 [0]) := rfl
theorem B5_rec : B5 `Nat.rec = some (.recr n5 0 [[[], [0]]]) := rfl
theorem B5_PU : B5 `PUnit = some (.ind pu5 0) := rfl
theorem B5_PUu : B5 `PUnit.unit = some (.ctor pu5 0 0 []) := rfl
theorem B5_PP : B5 `PProd = some (.ind pp5 0) := rfl
theorem B5_PPmk : B5 `PProd.mk = some (.ctor pp5 0 0 [0, 1]) := rfl
theorem B5_below : B5 `Nat.below = some (.const bl5) := rfl

section TrGo
variable {n : Nat} {Γ : Ctx ζ5 [`u].length 0 n} {Δ : MLCtx ζ5 [`u].length n}

theorem tr_F1Ty {Γ : Ctx ζ5 [`u].length 0 2} :
    TrM E5 B5 [`u] Γ ((MLCtx.pushLam [] none).pushLam none) F1Ty (F1TyM n5 bl5) :=
  TrM.forallE (tr_N B5_N) (TrM.forallE (tr_below B5_below rfl (TrM.bvar rfl) (TrM.bvar rfl))
    (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl)))

theorem tr_pair {mo t : Nat} {mo' t' : Metalean.Expr ζ5 1 n} (hmo : Δ.findB mo = some mo')
    (ht : Δ.findB t = some t') :
    TrM E5 B5 [`u] Γ Δ (pairTy mo t) (pairM pp5 bl5 mo' t') :=
  tr_PP B5_PP rfl rfl (TrM.app notSpecial_bvar (TrM.bvar hmo) (TrM.bvar ht))
    (tr_below B5_below rfl (TrM.bvar hmo) (TrM.bvar ht))

end TrGo

theorem tr_goTy : TrM E5 B5 [`u] .nil [] goTy (goTyM pp5 n5 bl5) :=
  TrM.forallE (TrM.forallE (tr_N B5_N) (TrM.sort rfl)) (TrM.forallE (tr_N B5_N)
    (TrM.forallE tr_F1Ty (tr_pair rfl rfl)))

/-- The minors of `Nat.brecOn.go`'s recursor, as the translation gives them. -/
def goMinZ : Metalean.Expr ζ5 1 3 :=
  mPPmk pp5 lu m1M (.app #0 (mZ n5)) (mPU pu5 m1M) (.app (.app #2 (mZ n5)) (mPUu pu5 m1M))
    (mPUu pu5 m1M)
def goMinS : Metalean.Expr ζ5 1 3 :=
  .lam (mN n5) (.lam (pairM pp5 bl5 #0 #3)
    (mPPmk pp5 lu m1M (.app #0 (mS n5 #3)) (pairM pp5 bl5 #0 #3) (.app (.app #2 (mS n5 #3)) #4) #4))

theorem tr_goVal : TrM E5 B5 [`u] .nil [] goVal (goValM pu5 pp5 n5 bl5) := by
  have h : TrM E5 B5 [`u] .nil [] goVal _ :=
    TrM.lam (TrM.forallE (tr_N B5_N) (TrM.sort rfl)) (TrM.lam (tr_N B5_N) (TrM.lam tr_F1Ty
      (TrM.special (E := E5) (B := B5) (lps := [`u]) (c := `Nat.rec) (us := [m1u])
        (as := [.lam `t tN (pairTy 3 0) .default,
          .app (.app (.app (.app (cPP uu m1u) (.app (.bvar 2) cZ)) (tPU m1u))
            (.app (.app (.bvar 0) cZ) (cPU m1u))) (cPU m1u),
          .lam `n tN (.lam `n_ih (pairTy 3 0)
            (.app (.app (.app (.app (cPP uu m1u) (.app (.bvar 4) (.app cS (.bvar 1)))) (pairTy 4 1))
              (.app (.app (.bvar 2) (.app cS (.bvar 1))) (.bvar 0))) (.bvar 0)) .default) .default,
          .bvar 1])
        (as' := [motGo pp5 n5 bl5, goMinZ, goMinS, #1]) B5_rec rfl rfl
        (by
          intro i a a' h1 h2
          rcases i with _ | _ | _ | _ | i <;> simp at h1 h2 <;> subst h1 h2
          · exact TrM.lam (tr_N B5_N) (tr_pair rfl rfl)
          · exact tr_PPmk B5_PPmk rfl rfl
              (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_Z B5_z)) (tr_PU B5_PU rfl)
              (TrM.app notSpecial_bvar (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_Z B5_z))
                (tr_PUu B5_PUu rfl)) (tr_PUu B5_PUu rfl)
          · exact TrM.lam (tr_N B5_N) (TrM.lam (tr_pair rfl rfl)
              (tr_PPmk B5_PPmk rfl rfl
                (TrM.app notSpecial_bvar (TrM.bvar rfl) (tr_S B5_s (TrM.bvar rfl)))
                (tr_pair rfl rfl)
                (TrM.app notSpecial_bvar (TrM.app notSpecial_bvar (TrM.bvar rfl)
                  (tr_S B5_s (TrM.bvar rfl))) (TrM.bvar rfl))
                (TrM.bvar rfl)))
          · exact TrM.bvar rfl)
        (SatTr.recrSat (E := E5) (lps := [`u]) (η := n5) (s := 0) (orders := [[[], [0]]])
          (us := [m1u]) (us' := []) (ls := Fin.elim0) (l := m1M) ordersN
          ![motGo pp5 n5 bl5, goMinZ, goMinS, #1] [] (minsGo pu5 pp5 n5 bl5)
          (Or.inl ⟨by rw [t_n5]; exact largeElimN, _, rfl, rfl⟩) trLevels_nil
          (by intro t c; fin_cases t; fin_cases c <;> rfl)
          (by
            intro t c; fin_cases t; fin_cases c <;>
              simp [Frontend.wrapCase, Frontend.isIdentityOrder] <;> rfl)))))
  exact trM_eq h (by
    simp only [goValM]
    arsx [goMinZ, goMinS, motGo, pairM, minsGo, F1TyM, MLDecl.wk, MLDecl.denote]
    all_goals (refine ⟨?_, ?_⟩ <;> rfl))

theorem henv6 : ProgEnv (.defnInfo Nat_brecOn_go :: .defnInfo Nat_below :: .defnInfo Nat_casesOn :: P3)
    ζ6 E6 B6 :=
  ProgEnv.defn henv5 (by decide) (by decide) rfl rfl tr_goTy tr_goVal

/-! ### `Nat.brecOn` in `E6`/`B6` -/

theorem B6_N : B6 `Nat = some (.ind n6 0) := rfl
theorem B6_PP : B6 `PProd = some (.ind pp6 0) := rfl
theorem B6_below : B6 `Nat.below = some (.const bl6) := rfl
theorem B6_go : B6 `Nat.brecOn.go = some (.const go6) := rfl

theorem tr_F1Ty6 {Γ : Ctx ζ6 [`u].length 0 2} :
    TrM E6 B6 [`u] Γ ((MLCtx.pushLam [] none).pushLam none) F1Ty (F1TyM n6 bl6) :=
  TrM.forallE (tr_N B6_N) (TrM.forallE (tr_below B6_below rfl (TrM.bvar rfl) (TrM.bvar rfl))
    (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl)))

theorem tr_brecOnTy : TrM E6 B6 [`u] .nil [] brecOnTy (brecOnTyM n6 bl6) :=
  TrM.forallE (TrM.forallE (tr_N B6_N) (TrM.sort rfl)) (TrM.forallE (tr_N B6_N)
    (TrM.forallE tr_F1Ty6 (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl))))

theorem tr_brecOnVal : TrM E6 B6 [`u] .nil [] brecOnVal (brecOnValM pp6 n6 bl6 go6) := by
  have hst : (E6.get pp6).block.IsStructure 0 0 := t_pp6 ▸ ppStruct
  have hgo : TrM E6 B6 [`u] (ΓG n6 bl6)
      (((MLCtx.pushLam [] none).pushLam none).pushLam none)
      (.app (.app (.app (.const `Nat.brecOn.go [uu]) (.bvar 2)) (.bvar 1)) (.bvar 0)) (goAppM go6) :=
    TrM.app (notSpecial_const B6_go ⟨_, rfl⟩) (TrM.app (notSpecial_const B6_go ⟨_, rfl⟩)
      (TrM.app (notSpecial_const B6_go ⟨_, rfl⟩) (tr_const1 B6_go rfl) (TrM.bvar rfl))
      (TrM.bvar rfl)) (TrM.bvar rfl)
  have hty : E6[ΓG n6 bl6] ⊢ goAppM go6 : .ind pp6 0 ![lu, m1M]
      ![.app #0 #1, belowM bl6 lu #0 #1] Fin.elim0 :=
    goAppM_typed wf6 t_n6 t_pp6 t_bt6 t_gt6
  have hp := TrM.projStruct (S := `PProd) (i := 0) hst (by decide) B6_PP hgo (typedExt_self hty)
  rw [projTerm_eqFst hst t_pp6] at hp
  exact TrM.lam (TrM.forallE (tr_N B6_N) (TrM.sort rfl)) (TrM.lam (tr_N B6_N) (TrM.lam tr_F1Ty6 hp))

theorem henv7 : ProgEnv (.defnInfo Nat_brecOn :: .defnInfo Nat_brecOn_go :: .defnInfo Nat_below ::
    .defnInfo Nat_casesOn :: P3) ζ7 E7 B7 :=
  ProgEnv.defn henv6 (by decide) (by decide) rfl rfl tr_brecOnTy tr_brecOnVal


/-! ### `Nat.add.match_1` in `E7`/`B7` -/

theorem B7_N : B7 `Nat = some (.ind n7 0) := rfl
theorem B7_z : B7 `Nat.zero = some (.ctor n7 0 0 []) := rfl
theorem B7_s : B7 `Nat.succ = some (.ctor n7 0 1 [0]) := rfl
theorem B7_casesOn : B7 `Nat.casesOn = some (.const c7) := rfl

theorem tr_matchTy : TrM E7 B7 [`u_1] .nil [] matchTy (matchTyM n7) :=
  TrM.forallE (TrM.forallE (tr_N B7_N) (TrM.forallE (tr_N B7_N) (TrM.sort rfl)))
    (TrM.forallE (tr_N B7_N) (TrM.forallE (tr_N B7_N)
      (TrM.forallE (TrM.forallE (tr_N B7_N) (TrM.app notSpecial_bvar
          (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl)) (tr_Z B7_z)))
        (TrM.forallE (TrM.forallE (tr_N B7_N) (TrM.forallE (tr_N B7_N) (TrM.app notSpecial_bvar
            (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl)) (tr_S B7_s (TrM.bvar rfl)))))
          (TrM.app notSpecial_bvar (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl))
            (TrM.bvar rfl))))))

theorem tr_matchVal : TrM E7 B7 [`u_1] .nil [] matchVal (matchValM n7 c7) :=
  TrM.lam (TrM.forallE (tr_N B7_N) (TrM.forallE (tr_N B7_N) (TrM.sort rfl)))
    (TrM.lam (tr_N B7_N) (TrM.lam (tr_N B7_N)
      (TrM.lam (TrM.forallE (tr_N B7_N) (TrM.app notSpecial_bvar
          (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl)) (tr_Z B7_z)))
        (TrM.lam (TrM.forallE (tr_N B7_N) (TrM.forallE (tr_N B7_N) (TrM.app notSpecial_bvar
            (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl)) (tr_S B7_s (TrM.bvar rfl)))))
          (TrM.app (notSpecial_const B7_casesOn ⟨_, rfl⟩)
            (TrM.app (notSpecial_const B7_casesOn ⟨_, rfl⟩)
              (TrM.app (notSpecial_const B7_casesOn ⟨_, rfl⟩)
                (TrM.app (notSpecial_const B7_casesOn ⟨_, rfl⟩) (tr_const1 B7_casesOn rfl)
                  (TrM.lam (tr_N B7_N) (TrM.app notSpecial_bvar
                    (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl)) (TrM.bvar rfl))))
                (TrM.bvar rfl))
              (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl)))
            (TrM.lam (tr_N B7_N) (TrM.app notSpecial_bvar
              (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl)) (TrM.bvar rfl))))))))

theorem henv8 : ProgEnv (.defnInfo match_def :: .defnInfo Nat_brecOn :: .defnInfo Nat_brecOn_go ::
    .defnInfo Nat_below :: .defnInfo Nat_casesOn :: P3) ζ8 E8 B8 :=
  ProgEnv.defn henv7 (by decide) (by decide) rfl rfl tr_matchTy tr_matchVal

/-! ### `Nat.add._f` in `E8`/`B8` -/

theorem B8_N : B8 `Nat = some (.ind n8 0) := rfl
theorem B8_z : B8 `Nat.zero = some (.ctor n8 0 0 []) := rfl
theorem B8_s : B8 `Nat.succ = some (.ctor n8 0 1 [0]) := rfl
theorem B8_PP : B8 `PProd = some (.ind pp8 0) := rfl
theorem B8_below : B8 `Nat.below = some (.const bl8) := rfl
theorem B8_match : B8 `Nat.add.match_1 = some (.const m8) := rfl

section TrF
variable {n : Nat} {Γ : Ctx ζ8 ([] : List Name).length 0 n} {Δ : MLCtx ζ8 ([] : List Name).length n}

theorem tr_motA : TrM E8 B8 [] Γ Δ motA (motNL n8) :=
  TrM.lam (tr_N B8_N) (TrM.forallE (tr_N B8_N) (tr_N B8_N))

theorem tr_belowA {a : Lean.Expr} {a' : Metalean.Expr ζ8 0 n} (ha : TrM E8 B8 [] Γ Δ a a') :
    TrM E8 B8 [] Γ Δ (belowA a) (belowM bl8 one (motNL n8) a') :=
  tr_below B8_below rfl tr_motA ha

end TrF

theorem tr_fTy : TrM E8 B8 [] .nil [] fTy (fTyM n8 bl8) :=
  TrM.forallE (tr_N B8_N) (TrM.forallE (tr_belowA (TrM.bvar rfl))
    (TrM.forallE (tr_N B8_N) (tr_N B8_N)))

/-- The context of `Nat.add._f`'s second alternative's body: `y f x a b x`. -/
def Γ6F : Ctx ζ8 0 0 6 :=
  (((ΓF n8 bl8).snoc (mN n8)).snoc (mN n8)).snoc (belowM bl8 one (motNL n8) (mS n8 #4))

theorem Γ6F_wf : E8[Γ6F] ⊢ ok := by
  have hb : ∀ {n : Nat} {Γ : Ctx ζ8 0 0 n} {a : Expr ζ8 0 n}, E8[Γ] ⊢ a : mN n8 →
      E8[Γ] ⊢ belowM bl8 one (motNL n8) a : .sort (m1 one) := fun ha =>
    belowM_typed wf8 t_bt8 (motNL_typed t_n8) ha
  have h1 : E8[(#t[mN n8] : Ctx ζ8 0 0 1)] ⊢ ok := .snoc .nil ⟨_, mN_typed t_n8⟩
  have h2 : E8[(#t[mN n8, belowM bl8 one (motNL n8) #0] : Ctx ζ8 0 0 2)] ⊢ ok :=
    .snoc h1 ⟨_, hb (var_of_get h1 ⟨0, by decide⟩ (by arsx))⟩
  have hΓ : E8[ΓF n8 bl8] ⊢ ok := .snoc h2 ⟨_, mN_typed t_n8⟩
  have h4 : E8[(ΓF n8 bl8).snoc (mN n8)] ⊢ ok := .snoc hΓ ⟨_, mN_typed t_n8⟩
  have h5 : E8[((ΓF n8 bl8).snoc (mN n8)).snoc (mN n8)] ⊢ ok := .snoc h4 ⟨_, mN_typed t_n8⟩
  exact .snoc h5 ⟨_, hb (mS_typed t_n8 (var_of_get h5 ⟨4, by decide⟩ (by arsx)))⟩

theorem x_typed : E8[Γ6F] ⊢ #5 : .ind pp8 0 ![one, m1 one]
    ![.app (motNL n8) #4, belowM bl8 one (motNL n8) #4] Fin.elim0 := by
  have hΓ := Γ6F_wf
  have hb : E8[Γ6F] ⊢ #4 : mN n8 := var_of_get hΓ ⟨4, by decide⟩ (by arsx [Γ6F])
  have hx : E8[Γ6F] ⊢ #5 : belowM bl8 one (motNL n8) (mS n8 #4) :=
    var_of_get hΓ ⟨5, by decide⟩ (by arsx [Γ6F])
  exact .defeqDF (belowS_defeq_motNL wf8 t_n8 t_pp8 t_bt8 t_bv8 hΓ (motNL_typed t_n8) hb) hx

theorem tr_fVal : TrM E8 B8 [] .nil [] fVal (fValM pp8 n8 bl8 m8) := by
  have hst : (E8.get pp8).block.IsStructure 0 0 := t_pp8 ▸ ppStruct
  have hp := TrM.projStruct (E := E8) (B := B8) (lps := []) (Γ := Γ6F)
    (Δ := MLCtx.pushLam (MLCtx.pushLam (MLCtx.pushLam (MLCtx.pushLam (MLCtx.pushLam
      (MLCtx.pushLam ([] : MLCtx ζ8 0 0) none) none) none) none) none) none) (S := `PProd) (i := 0)
    (e := .bvar 0) (e' := #5) hst (by decide) B8_PP (TrM.bvar rfl) (typedExt_self x_typed)
  rw [projTerm_eqFstA hst t_pp8] at hp
  exact TrM.lam (tr_N B8_N) (TrM.lam (tr_belowA (TrM.bvar rfl)) (TrM.lam (tr_N B8_N)
    (TrM.app (notSpecial_const B8_match ⟨_, rfl⟩)
      (TrM.app (notSpecial_const B8_match ⟨_, rfl⟩)
        (TrM.app (notSpecial_const B8_match ⟨_, rfl⟩)
          (TrM.app (notSpecial_const B8_match ⟨_, rfl⟩)
            (TrM.app (notSpecial_const B8_match ⟨_, rfl⟩)
              (TrM.app (notSpecial_const B8_match ⟨_, rfl⟩) (tr_const1 B8_match rfl)
                (TrM.lam (tr_N B8_N) (TrM.lam (tr_N B8_N)
                  (TrM.forallE (tr_belowA (TrM.bvar rfl)) (tr_N B8_N)))))
              (TrM.bvar rfl))
            (TrM.bvar rfl))
          (TrM.lam (tr_N B8_N) (TrM.lam (tr_belowA (tr_Z B8_z)) (TrM.bvar rfl))))
        (TrM.lam (tr_N B8_N) (TrM.lam (tr_N B8_N) (TrM.lam (tr_belowA (tr_S B8_s (TrM.bvar rfl)))
          (tr_S B8_s (TrM.app (by rintro ⟨c, us, b, h, -⟩; cases h) hp (TrM.bvar rfl)))))))
      (TrM.bvar rfl))))

theorem henv9 : ProgEnv (.defnInfo add_f :: .defnInfo match_def :: .defnInfo Nat_brecOn ::
    .defnInfo Nat_brecOn_go :: .defnInfo Nat_below :: .defnInfo Nat_casesOn :: P3) ζ9 E9 B9 :=
  ProgEnv.defn henv8 (by decide) (by decide) rfl rfl tr_fTy tr_fVal

/-! ### `Nat.add` in `E9`/`B9` -/

theorem B9_N : B9 `Nat = some (.ind n9 0) := rfl
theorem B9_brecOn : B9 `Nat.brecOn = some (.const br9) := rfl
theorem B9_f : B9 `Nat.add._f = some (.const f9) := rfl

theorem tr_addTy : TrM E9 B9 [] .nil [] addTy (addTyM n9) :=
  TrM.forallE (TrM.mdata (tr_N B9_N)) (TrM.forallE (TrM.mdata (tr_N B9_N)) (tr_N B9_N))

theorem tr_addVal : TrM E9 B9 [] .nil [] addVal (addValM n9 br9 f9) :=
  TrM.lam (tr_N B9_N) (TrM.lam (tr_N B9_N)
    (TrM.app (notSpecial_const B9_brecOn ⟨_, rfl⟩)
      (TrM.app (notSpecial_const B9_brecOn ⟨_, rfl⟩)
        (TrM.app (notSpecial_const B9_brecOn ⟨_, rfl⟩)
          (TrM.app (notSpecial_const B9_brecOn ⟨_, rfl⟩) (tr_const1 B9_brecOn rfl)
            (TrM.lam (tr_N B9_N) (TrM.forallE (tr_N B9_N) (tr_N B9_N))))
          (TrM.bvar rfl))
        (tr_const0 B9_f))
      (TrM.bvar rfl)))

theorem henv10 : ProgEnv (.defnInfo add_def :: .defnInfo add_f :: .defnInfo match_def ::
    .defnInfo Nat_brecOn :: .defnInfo Nat_brecOn_go :: .defnInfo Nat_below ::
    .defnInfo Nat_casesOn :: P3) ζ10 E10 B10 :=
  ProgEnv.defn henv9 (by decide) (by decide) rfl rfl tr_addTy tr_addVal

/-! ## The block of `OfNat` in `E11`/`B11` -/

theorem B11_N : B11 `Nat = some (.ind n11 0) := rfl
theorem B11_O : B11 `OfNat = some (.ind o11 0) := rfl
theorem B11_Omk : B11 `OfNat.mk = some (.ctor o11 0 0 [0]) := rfl
theorem B11_Orec : B11 `OfNat.rec = some (.recr o11 0 [[[0]]]) := rfl

section TrOf
variable {ζ : Sigs} {E : Env ζ} {B : Binds ζ} {lps : List Name} {n : Nat}
  {Γ : Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}

theorem tr_Of {η : Head ζ (.inductive ofSig)} (h : B `OfNat = some (.ind η 0)) {u : Lean.Level}
    {l : Metalean.Level lps.length} (hu : TrLevel lps u = some l) {α x : Lean.Expr}
    {α' x' : Metalean.Expr ζ lps.length n} (hα : TrM E B lps Γ Δ α α') (hx : TrM E B lps Γ Δ x x') :
    TrM E B lps Γ Δ (.app (.app (tOf u) α) x) (mOf η l α' x') :=
  TrM.special (as := [α, x]) (as' := [α', x']) h rfl rfl
    (by
      intro i y y' h1 h2
      rcases i with _ | _ | i <;> simp at h1 h2 <;> subst h1 h2
      · exact hα
      · exact hx)
    (SatTr.indSat (E := E) (lps := lps) (η := η) (s := 0) (us := [u]) (ls := ![l])
      (ps := ![α', x']) (is := Fin.elim0) (rest := []) (trLevels_one hu))

theorem tr_OfMk {η : Head ζ (.inductive ofSig)} (h : B `OfNat.mk = some (.ctor η 0 0 [0]))
    {u : Lean.Level} {l : Metalean.Level lps.length} (hu : TrLevel lps u = some l)
    {α x a : Lean.Expr} {α' x' a' : Metalean.Expr ζ lps.length n} (hα : TrM E B lps Γ Δ α α')
    (hx : TrM E B lps Γ Δ x x') (ha : TrM E B lps Γ Δ a a') :
    TrM E B lps Γ Δ (.app (.app (.app (cOf u) α) x) a) (mOfMk η l α' x' a') :=
  TrM.special (as := [α, x, a]) (as' := [α', x', a']) h rfl rfl
    (by
      intro i y y' h1 h2
      rcases i with _ | _ | _ | i <;> simp at h1 h2 <;> subst h1 h2
      · exact hα
      · exact hx
      · exact ha)
    (SatTr.ctorSat (E := E) (lps := lps) (η := η) (s := 0) (c := 0) (us := [u]) (order := [0])
      (ls := ![l]) (fs := [a']) (rest := []) (ps := ![α', x']) (fds := ![a'])
      (recFds := Fin.elim0) (trLevels_one hu) rfl rfl
      (by intro o; fin_cases o; exact ⟨_, _, rfl, rfl, rfl⟩))

end TrOf

theorem tr_ofTy : TrM E11 B11 [`u] .nil [] OfNat_ind.type (ofTyM n11) :=
  TrM.forallE (TrM.sort rfl) (TrM.forallE (tr_N B11_N) (TrM.sort rfl))

theorem tr_ofConst : TrM E11 B11 [`u] .nil [] (.const `OfNat [.param `u]) (ofTermM n11 o11) := by
  have h := TrM.special (E := E11) (B := B11) (lps := [`u]) (Γ := .nil) (Δ := [])
    (c := `OfNat) (us := [.param `u]) (as := []) (as' := []) B11_O rfl rfl
    (fun _ _ _ h => nomatch h)
    (SatTr.indEta (E := E11) (lps := [`u]) (args := []) (η := o11) (s := 0)
      (us := [.param `u]) (ls := ![lu]) (trLevels_one rfl) (by decide))
  rw [indTerm_eqOf t_o11] at h
  exact h

theorem tr_ofMkTy : TrM E11 B11 [`u] .nil [] OfNat_mk.type (ofMkTyM n11 o11) :=
  TrM.forallE (TrM.sort rfl) (TrM.forallE (tr_N B11_N) (TrM.forallE (TrM.bvar rfl)
    (tr_Of B11_O rfl (TrM.bvar rfl) (TrM.bvar rfl))))

theorem tr_ofMk : TrM E11 B11 [`u] .nil [] (.const `OfNat.mk [.param `u]) (ofMkTermM n11 o11) :=
  TrM.special (as := []) (as' := []) B11_Omk rfl rfl (fun _ _ _ h => nomatch h)
    (SatTr.ctorEta (args := []) (η := o11) (s := 0) (c := 0) (order := [0])
      (trLevels_one rfl) (by decide) (ctorTerm_eqOf t_o11))

theorem tr_ofRecTy : TrM E11 B11 [`u_1, `u] .nil [] OfNat_rec.type (ofRecTyM n11 o11) :=
  TrM.forallE (TrM.sort rfl) (TrM.forallE (tr_N B11_N)
    (TrM.forallE (TrM.forallE (tr_Of B11_O rfl (TrM.bvar rfl) (TrM.bvar rfl)) (TrM.sort rfl))
      (TrM.forallE (TrM.forallE (TrM.bvar rfl)
          (TrM.app notSpecial_bvar (TrM.bvar rfl)
            (tr_OfMk B11_Omk rfl (TrM.bvar rfl) (TrM.bvar rfl) (TrM.bvar rfl))))
        (TrM.forallE (tr_Of B11_O rfl (TrM.bvar rfl) (TrM.bvar rfl))
          (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl))))))

theorem tr_ofRec : TrM E11 B11 [`u_1, `u] .nil [] (.const `OfNat.rec [.param `u_1, .param `u])
    (ofRecTermM n11 o11) :=
  TrM.special (as := []) (as' := []) B11_Orec rfl rfl (fun _ _ _ h => nomatch h)
    (SatTr.recrEta (E := E11) (lps := [`u_1, `u]) (args := []) (η := o11) (s := 0)
      (us := [.param `u_1, .param `u]) (us' := [.param `u]) (l := q0) (ls := ![q1])
      (fun _ _ => [0]) (Or.inl ⟨by rw [t_o11]; exact largeElimOf, _, rfl, rfl⟩)
      (trLevels_one rfl) (by intro t c; fin_cases t; fin_cases c; rfl) (by decide)
      (recrTerm_eqOf t_o11))

def IsOf : Fin ofSig.nsorts → InductiveVal := fun _ => OfNat_ind
def CsOf : (s : Fin ofSig.nsorts) → Fin (ofSig.nctors s) → ConstructorVal := fun _ _ => OfNat_mk
def RsOf : Fin ofSig.nsorts → RecursorVal := fun _ => OfNat_rec
def ordersOf : (s : Fin ofSig.nsorts) → Fin (ofSig.nctors s) → List Nat := fun _ _ => [0]

theorem POf_eq : IndBlock.decls IsOf CsOf RsOf =
    [.recInfo OfNat_rec, .ctorInfo OfNat_mk, .inductInfo OfNat_ind] := rfl

theorem indBlockOf : IndBlock E11 B11 o11 [`u] IsOf CsOf RsOf ordersOf where
  levels := rfl
  ind s := by fin_cases s; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  ctor s c := by
    fin_cases s; fin_cases c
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, [0], [], rfl, rfl, rfl, by decide, .nil,
      List.Perm.refl _⟩
  ctorType s c := by fin_cases s; fin_cases c; exact ⟨_, [], rfl, rfl, rfl⟩
  recr s := by
    fin_cases s
    exact ⟨rfl, rfl, fun _ => ⟨`u_1, rfl⟩, fun h => absurd (by rw [t_o11]; exact largeElimOf) h,
      rfl, rfl, rfl, rfl, rfl, rfl⟩
  recrType s := by fin_cases s; rfl
  recMajor s := by fin_cases s; exact ⟨_, _, _, _, _, rfl, rfl⟩
  minors s t c := by fin_cases s; fin_cases t; fin_cases c; rfl
  recIHs s := by
    fin_cases s
    exact ⟨_, _, rfl, rfl, fun t c => by fin_cases t; fin_cases c; rfl⟩
  indexVars s _ h := by fin_cases s; exact h.elim fun i _ => i.elim0

theorem constTypedOf : ∀ ci ∈ IndBlock.decls IsOf CsOf RsOf, ConstTyped E11 B11 ci := by
  rw [POf_eq]
  intro ci hci
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hci
  rcases hci with rfl | rfl | rfl
  · exact ⟨_, _, tr_ofRecTy, tr_ofRec, ofRecTermM_typed t_n11 t_o11⟩
  · exact ⟨_, _, tr_ofMkTy, tr_ofMk, ofMkTermM_typed t_n11 t_o11⟩
  · exact ⟨_, _, tr_ofTy, tr_ofConst, ofTermM_typed t_n11 t_o11⟩

def P10 : List ConstantInfo :=
  .defnInfo add_def :: .defnInfo add_f :: .defnInfo match_def :: .defnInfo Nat_brecOn ::
    .defnInfo Nat_brecOn_go :: .defnInfo Nat_below :: .defnInfo Nat_casesOn :: P3

theorem henv11 : ProgEnv (IndBlock.decls IsOf CsOf RsOf ++ P10) ζ11 E11 B11 :=
  ProgEnv.induct (I := ofBlock n10) (lps := [`u]) (orders := ordersOf) henv10 (by decide)
    (by rw [POf_eq]; decide) (by decide)
    (fun n hn => by
      rw [POf_eq] at hn
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
        not_or] at hn
      obtain ⟨h1, h2, h3⟩ := hn
      have h1' : n ≠ `OfNat.rec := h1
      have h2' : n ≠ `OfNat.mk := h2
      have h3' : n ≠ `OfNat := h3
      simp [B11, h1', h2', h3'])
    indBlockOf constTypedOf

/-! ## `OfNat.ofNat` in `E11`/`B11` -/

theorem tr_ofNatTy : TrM E11 B11 [`u] .nil [] ofNatTy (ofNatTyM n11 o11) :=
  TrM.forallE (TrM.sort rfl) (TrM.forallE (tr_N B11_N)
    (TrM.forallE (tr_Of B11_O rfl (TrM.bvar rfl) (TrM.bvar rfl)) (TrM.bvar rfl)))

theorem self_typed : E11[ΓO n11 o11] ⊢ #2 : .ind o11 0 ![lu] ![#0, #1] Fin.elim0 := by
  have h1 : E11[(#t[.sort (.succ lu)] : Ctx ζ11 1 0 1)] ⊢ ok := .snoc .nil ⟨_, .sortDF⟩
  have h2 : E11[(#t[.sort (.succ lu), mN n11] : Ctx ζ11 1 0 2)] ⊢ ok :=
    .snoc h1 ⟨_, mN_typed t_n11⟩
  have hO := mOf_typed (η := o11) t_o11 (var_of_get h2 ⟨0, by decide⟩ (by ofs))
    (var_of_get h2 ⟨1, by decide⟩ (by ofs))
  have hΓ : E11[ΓO n11 o11] ⊢ ok := .snoc h2 ⟨_, hO⟩
  exact var_of_get hΓ ⟨2, by decide⟩ (by ofs [ΓO])

theorem tr_ofNatVal : TrM E11 B11 [`u] .nil [] ofNatVal (ofNatValM n11 o11) := by
  have hst : (E11.get o11).block.IsStructure 0 0 := t_o11 ▸ ofStruct
  have hp := TrM.projStruct (E := E11) (B := B11) (lps := [`u]) (Γ := ΓO n11 o11)
    (Δ := MLCtx.pushLam (MLCtx.pushLam (MLCtx.pushLam ([] : MLCtx ζ11 1 0) none) none) none)
    (S := `OfNat) (i := 0) (e := .bvar 0) (e' := #2) hst (by decide) B11_O (TrM.bvar rfl)
    (typedExt_self self_typed)
  rw [projTerm_eqOf hst t_o11] at hp
  exact TrM.lam (TrM.sort rfl) (TrM.lam (tr_N B11_N)
    (TrM.lam (tr_Of B11_O rfl (TrM.bvar rfl) (TrM.bvar rfl)) hp))

theorem henv12 : ProgEnv (.defnInfo ofNat_def :: IndBlock.decls IsOf CsOf RsOf ++ P10) ζ12 E12
    B12 :=
  ProgEnv.defn henv11 (by decide) (by decide) rfl rfl tr_ofNatTy tr_ofNatVal

/-! ## `instOfNatNat` in `E12`/`B12` -/

theorem B12_N : B12 `Nat = some (.ind n12 0) := rfl
theorem B12_O : B12 `OfNat = some (.ind o12 0) := rfl
theorem B12_Omk : B12 `OfNat.mk = some (.ctor o12 0 0 [0]) := rfl

theorem tr_instTy : TrM E12 B12 [] .nil [] instTy (instTyM n12 o12) :=
  TrM.forallE (tr_N B12_N) (tr_Of B12_O rfl (tr_N B12_N) (TrM.bvar rfl))

theorem tr_instVal : TrM E12 B12 [] .nil [] instVal (instValM n12 o12) :=
  TrM.lam (tr_N B12_N) (tr_OfMk B12_Omk rfl (tr_N B12_N) (TrM.bvar rfl) (TrM.bvar rfl))

theorem henv13 : ProgEnv P ζ13 E13 B13 :=
  ProgEnv.defn henv12 (by decide) (by decide) rfl rfl tr_instTy tr_instVal

/-! ## The erased term `Nat.add 2 3` in `E13`/`B13` -/

theorem B13_N : B13 `Nat = some (.ind n13 0) := rfl
theorem B13_z : B13 `Nat.zero = some (.ctor n13 0 0 []) := rfl
theorem B13_s : B13 `Nat.succ = some (.ctor n13 0 1 [0]) := rfl
theorem B13_add : B13 `Nat.add = some (.const a13) := rfl
theorem B13_ofNat : B13 `OfNat.ofNat = some (.const on13) := rfl
theorem B13_inst : B13 `instOfNatNat = some (.const i13) := rfl

/-- The numeral `k` in Metalean: `OfNat.ofNat.{0} Nat k (instOfNatNat k)`, the literal the unary
constructor chain `natLitM`. -/
def numM (k : Nat) : Expr ζ13 0 0 :=
  .app (.app (.app (.const on13 ![.zero]) (mN n13)) (natLitM n13 k))
    (.app (.const i13 Fin.elim0) (natLitM n13 k))

/-- The erased term in Metalean. -/
def tE : Expr ζ13 0 0 := .app (.app (.const a13 Fin.elim0) (numM 2)) (numM 3)

theorem tr_num (k : Nat) : TrM E13 B13 [] .nil [] (numK k) (numM k) :=
  TrM.app (notSpecial_const B13_ofNat ⟨_, rfl⟩)
    (TrM.app (notSpecial_const B13_ofNat ⟨_, rfl⟩)
      (TrM.app (notSpecial_const B13_ofNat ⟨_, rfl⟩) (tr_const1 B13_ofNat rfl)
        (TrM.mdata (tr_N B13_N)))
      (TrM.lit B13_N B13_z B13_s))
    (TrM.app (notSpecial_const B13_inst ⟨_, rfl⟩) (tr_const0 B13_inst)
      (TrM.lit B13_N B13_z B13_s))

theorem tr_e : TrM E13 B13 [] .nil [] e tE :=
  TrM.app (notSpecial_const B13_add ⟨_, rfl⟩)
    (TrM.app (notSpecial_const B13_add ⟨_, rfl⟩) (tr_const0 B13_add) (tr_num 2)) (tr_num 3)

theorem natLitM_typed : ∀ k, E13[(.nil : Ctx ζ13 0 0 0)] ⊢ natLitM n13 k : mN n13
  | 0 => mZ_typed t_n13
  | k + 1 => mS_typed t_n13 (natLitM_typed k)

theorem numM_typed (k : Nat) : E13[.nil] ⊢ numM k : mN n13 := by
  have hl := natLitM_typed k
  have h0 : E13[(.nil : Ctx ζ13 0 0 0)] ⊢ .const on13 ![(.zero : Metalean.Level 0)] :
      (E13.get on13).constType{![(.zero : Metalean.Level 0)]}.wkClosed :=
    const_typed wf13 on13 ![.zero] rfl
  rw [t_ont13] at h0
  arsx [ofNatTyM, mOf] at h0
  have hc1 := app_typed' h0 (mN_typed t_n13) (by arsx)
  arsx at hc1
  have hc2 := app_typed' hc1 hl (by arsx)
  arsx at hc2
  have hi0 : E13[(.nil : Ctx ζ13 0 0 0)] ⊢ .const i13 Fin.elim0 :
      (E13.get i13).constType{(Fin.elim0 : Fin 0 → Metalean.Level 0)}.wkClosed :=
    const_typed wf13 i13 Fin.elim0 rfl
  rw [t_it13] at hi0
  arsx [instTyM, mOf] at hi0
  have hi1 := app_typed' hi0 hl (by arsx)
  arsx at hi1
  exact typed_of_eq (app_typed' hc2 hi1 (by arsx)) (by arsx)

theorem tE_typed : E13[.nil] ⊢ tE : mN n13 := by
  have h0 : E13[(.nil : Ctx ζ13 0 0 0)] ⊢ .const a13 Fin.elim0 :
      .forallE (mN n13) (.forallE (mN n13) (mN n13)) :=
    const_typed wf13 a13 Fin.elim0 (by rw [t_at13]; arsx [addTyM])
  have h1 := app_typed' h0 (numM_typed 2) (by arsx)
  arsx at h1
  exact typed_of_eq (app_typed' h1 (numM_typed 3) (by arsx)) (by arsx)

/-! ## The premises -/

/-- The Metalean environment of NV-A. -/
abbrev E : Env ζ13 := E13
/-- The name table of NV-A. -/
abbrev B : Binds ζ13 := B13

/-- `henv`: the program is the Lean form of `E` with table `B`. -/
theorem henv : ProgEnv P ζ13 E B := henv13

/-- `hwf`: `E` is well formed. -/
theorem hwf : EnvWF E := wf13

/-- `he`: the erased term is the Lean form of `tE`. -/
theorem he : TrM E B [] .nil [] e tE := tr_e

/-- `hty`: `tE` is typed. -/
theorem hty : ∃ T, E[.nil] ⊢ tE : T := ⟨_, tE_typed⟩

end EraseProof.Test.NVA
