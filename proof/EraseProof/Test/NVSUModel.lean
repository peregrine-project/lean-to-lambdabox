import EraseProof.Test.NVSUData
import EraseProof.Test.NVSModel

/-!
# NV-SU: the compiled pre-definition in NV-S's model

The premise `hpre` of the final theorem on NV-SU (`Test/NVSUData.lean`): in NV-S's model `E`, `B`
(`Test/NVSModel.lean`), the compiled pre-definition `preVal` of `add` is the Lean form of the
closed Metalean term `preValM` (`tr_preVal`), typed at `add`'s type (`preValM_typed`): the match
`add.match_1` at the motive `fun m => N`, whose alternatives are typed at the motive applied, by a
β-step (`motNL_beta`), the recursive call `add n k` through the constant `add` of `E`. `preVal`
names only `add` and the declarations after it in the newest-first `P`, `add` at its own (empty)
level parameters, and `add` is the only declaration of `P` with a pre-definition under `cfgSU`.
-/

open Lean Metalean

namespace EraseProof.Test.NVSU

open EraseProof.Test.NV1 (typed_of_eq var_of_get app_typed const_typed notSpecial_const)
open EraseProof.Test.NVS (P view add_def addTy ζ12 n12 a12 E12 B12 E B wf12 t_n12 t_at12 B12_s
  B12_add matchTyM addTyM unitM motNL motNM motNL_typed motNL_beta one app_typed' tr_const0
  tr_const1)
open EraseProof.Test.NVR (mN mZ mS mN_typed mZ_typed mS_typed tr_N tr_S)

/-! ## The Metalean term -/

/-- The heads of `add.match_1` and `Unit` in `E12`. -/
abbrev m12 : Head ζ12 (.const .def 1) := .there (.there .here)
abbrev u12 : Head ζ12 (.const .def 0) :=
  .there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))

theorem B12_N : B12 `N = some (.ind n12 0) := rfl
theorem B12_match : B12 `add.match_1 = some (.const m12) := rfl
theorem B12_Unit : B12 `Unit = some (.const u12) := rfl

theorem t_mt12 : (E12.get m12).constType = matchTyM n12 u12 := by envs

theorem t_ut12 : (E12.get u12).constType = .sort one := by envs

/-- The alternatives `fun _ => n` and `fun k => N.s (add n k)`, under `n m`. -/
def alt1PM : Metalean.Expr ζ12 0 2 := .lam (unitM u12) #0
def alt2PM : Metalean.Expr ζ12 0 2 :=
  .lam (mN n12) (mS n12 (.app (.app (.const a12 Fin.elim0) #0) #2))

/-- `pre[add]` in Metalean: `fun n m => add.match_1.{1} (fun m => N) m (fun _ => n)
(fun k => N.s (add n k))`. -/
def preValM : Metalean.Expr ζ12 0 0 :=
  .lam (mN n12) (.lam (mN n12)
    (.app (.app (.app (.app (.const m12 ![one]) (motNL n12)) #1) alt1PM) alt2PM))

/-- `preVal` is the Lean form of `preValM`. -/
theorem tr_preVal : TrM E12 B12 [] .nil [] preVal preValM :=
  TrM.lam (tr_N B12_N) (TrM.lam (tr_N B12_N)
    (TrM.app (notSpecial_const B12_match ⟨_, rfl⟩)
      (TrM.app (notSpecial_const B12_match ⟨_, rfl⟩)
        (TrM.app (notSpecial_const B12_match ⟨_, rfl⟩)
          (TrM.app (notSpecial_const B12_match ⟨_, rfl⟩) (tr_const1 B12_match rfl)
            (TrM.lam (tr_N B12_N) (tr_N B12_N)))
          (TrM.bvar rfl))
        (TrM.lam (tr_const0 B12_Unit) (TrM.bvar rfl)))
      (TrM.lam (tr_N B12_N)
        (tr_S B12_s (TrM.app (notSpecial_const B12_add ⟨_, rfl⟩)
          (TrM.app (notSpecial_const B12_add ⟨_, rfl⟩) (tr_const0 B12_add) (TrM.bvar rfl))
          (TrM.bvar rfl))))))

/-- `add`'s type is the Lean form of `addTyM`. -/
theorem tr_addTy : TrM E12 B12 [] .nil [] addTy (addTyM n12) :=
  TrM.forallE (tr_N B12_N) (TrM.forallE (tr_N B12_N) (tr_N B12_N))

/-! ## Typing -/

/-- `preValM` is typed at `add`'s type. -/
theorem preValM_typed : E12[.nil] ⊢ preValM : addTyM n12 := by
  have h1 : E12[(#t[mN n12] : Ctx ζ12 0 0 1)] ⊢ ok := .snoc .nil ⟨_, mN_typed t_n12⟩
  have hΓ : E12[(#t[mN n12, mN n12] : Ctx ζ12 0 0 2)] ⊢ ok := .snoc h1 ⟨_, mN_typed t_n12⟩
  have hy : E12[(#t[mN n12, mN n12] : Ctx ζ12 0 0 2)] ⊢ #1 : mN n12 :=
    var_of_get hΓ ⟨1, by decide⟩ (by rsx)
  -- `add.match_1.{1} (fun m => N) m`
  have h0 : E12[(#t[mN n12, mN n12] : Ctx ζ12 0 0 2)] ⊢ .const m12 ![one] :
      (E12.get m12).constType{![one]}.wkClosed := const_typed wf12 m12 ![one] rfl
  rw [t_mt12] at h0
  rsx [matchTyM, motNM, unitM] at h0
  have hc1 := app_typed' h0 (motNL_typed t_n12) (by rsx [motNM])
  rsx at hc1
  have hc2 := app_typed' hc1 hy (by rsx)
  rsx at hc2
  -- `fun _ => n`
  have hunit : E12[(#t[mN n12, mN n12] : Ctx ζ12 0 0 2)] ⊢ unitM u12 : .sort one :=
    const_typed wf12 u12 Fin.elim0 (by rw [t_ut12]; rsx)
  have h3 : E12[(#t[mN n12, mN n12, unitM u12] : Ctx ζ12 0 0 3)] ⊢ ok := .snoc hΓ ⟨_, hunit⟩
  have hx3 : E12[(#t[mN n12, mN n12, unitM u12] : Ctx ζ12 0 0 3)] ⊢ #0 : mN n12 :=
    var_of_get h3 ⟨0, by decide⟩ (by rsx)
  have hβz := motNL_beta t_n12 (Γ := (#t[mN n12, mN n12, unitM u12] : Ctx ζ12 0 0 3))
    (mZ_typed t_n12)
  have hH1 : E12[(#t[mN n12, mN n12] : Ctx ζ12 0 0 2)] ⊢ alt1PM :
      .forallE (unitM u12) (.app (motNL n12) (mZ n12)) :=
    .lamDF hunit hβz.left hβz.left (.defeqDF hβz.symm hx3) (.defeqDF hβz.symm hx3)
  have hc3 := app_typed' hc2 hH1 (by rsx [motNL, unitM])
  rsx at hc3
  -- `fun k => N.s (add n k)`
  have h3' : E12[(#t[mN n12, mN n12, mN n12] : Ctx ζ12 0 0 3)] ⊢ ok := .snoc hΓ ⟨_, mN_typed t_n12⟩
  have hn3 : E12[(#t[mN n12, mN n12, mN n12] : Ctx ζ12 0 0 3)] ⊢ #0 : mN n12 :=
    var_of_get h3' ⟨0, by decide⟩ (by rsx)
  have hk3 : E12[(#t[mN n12, mN n12, mN n12] : Ctx ζ12 0 0 3)] ⊢ #2 : mN n12 :=
    var_of_get h3' ⟨2, by decide⟩ (by rsx)
  have hadd : E12[(#t[mN n12, mN n12, mN n12] : Ctx ζ12 0 0 3)] ⊢
      .const a12 Fin.elim0 : .forallE (mN n12) (.forallE (mN n12) (mN n12)) :=
    const_typed wf12 a12 Fin.elim0 (by rw [t_at12]; rsx [addTyM])
  have hcall := typed_of_eq (app_typed' (typed_of_eq (app_typed' hadd hn3 (by rsx))
    (T' := .forallE (mN n12) (mN n12)) (by rsx)) hk3 (by rsx)) (T' := mN n12) (by rsx)
  have hsx := mS_typed t_n12 hcall
  have hβs := motNL_beta t_n12 (mS_typed t_n12 hk3)
  have hH2 : E12[(#t[mN n12, mN n12] : Ctx ζ12 0 0 2)] ⊢ alt2PM :
      .forallE (mN n12) (.app (motNL n12) (mS n12 #2)) :=
    .lamDF (mN_typed t_n12) hβs.left hβs.left (.defeqDF hβs.symm hsx) (.defeqDF hβs.symm hsx)
  have hc4 := app_typed' hc3 hH2 (by rsx [motNL])
  rsx at hc4
  -- the match's type, the motive applied to `m`
  have hbody := Defeq.defeqDF (motNL_beta t_n12 hy) (typed_of_eq hc4 (by rsx [motNL]))
  exact Ctx.lam_congr (Γ := .nil) (Δ := #t[mN n12, mN n12]) hΓ hbody

/-! ## The premise -/

/-- Under `cfgSU` the declaration of `P` with a compiled pre-definition is `add`, its first. -/
theorem preDef_P : (List.range P.length).all (fun k =>
    k == 0 || !((P[k]?).bind (Erasure.preDef? view cfgSU)).isSome) = true := by krfl

/-- `hpre`: the compiled pre-definition of `add`, the only one of `P` (`preDef_P`), names only
`add` and declarations after it in `P`, names `add` at its own (empty) level parameters, and it is
the Lean form of `preValM`, typed at the translation of `add`'s type. Reference: none (DV-31). -/
theorem hpre : PreDefsOK E B view cfgSU P := by
  intro P₁ ci P₀ pre hP hpd
  have hk : P₁.length < P.length := by rw [hP]; simp
  have hci : P[P₁.length]? = some ci := by rw [hP]; simp
  have hP₀ : P.drop (P₁.length + 1) = P₀ := by rw [hP]; simp
  have h0 := List.all_eq_true.mp preDef_P _ (List.mem_range.mpr hk)
  rw [hci, Option.bind_some, hpd] at h0
  have h0' : P₁.length = 0 := by simpa using h0
  rw [h0'] at hci hP₀
  obtain rfl : ci = .defnInfo add_def := Option.some.inj (hci.symm.trans rfl)
  subst hP₀
  obtain rfl : pre = preVal := Option.some.inj (hpd.symm.trans preDef_add)
  refine ⟨?_, ?_, preValM, addTyM n12, tr_preVal, tr_addTy, preValM_typed⟩
  · simp only [ConstsIn, preVal, motPre, altPre1, altPre2, EraseProof.Test.NVR.tN,
      EraseProof.Test.NVR.cS, EraseProof.Test.NVS.tUnit, and_true]
    and_intros
    all_goals first | exact .inl rfl | exact .inr (by krfl)
  · simp only [ConstAt, preVal, motPre, altPre1, altPre2, EraseProof.Test.NVR.tN,
      EraseProof.Test.NVR.cS, EraseProof.Test.NVS.tUnit, and_true]
    and_intros
    all_goals intro h; first | rfl | exact absurd h (by decide)

end EraseProof.Test.NVSU
