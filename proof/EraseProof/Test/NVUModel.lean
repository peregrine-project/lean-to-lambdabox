import EraseProof.Test.NVUData
import EraseProof.Test.NVAModel

/-!
# NV-U: the compiled pre-definition in NV-A's model

The premise `hpre` of the final theorem on NV-U (`Test/NVUData.lean`): in NV-A's model `E`, `B`
(`Test/NVAModel.lean`), the compiled pre-definition `preVal` of `Nat.add` is the Lean form of the
closed Metalean term `preValM` (`tr_preVal`), typed at `Nat.add`'s type (`preValM_typed`): the
match `Nat.add.match_1` at the motive `fun x y => Nat`, whose alternatives are typed at the motive
applied, by two β-steps (`motPM_beta`), the recursive call `Nat.add a b` through the constant
`Nat.add` of `E`. `preVal` names only `Nat.add` and the declarations after it in the newest-first
`P`, and `Nat.add` is the only declaration of `P` with a pre-definition under `cfgU`.
-/

open Lean Metalean

namespace EraseProof.Test.NVU

open EraseProof.Test.NV1 (typed_of_eq var_of_get app_typed const_typed notSpecial_bvar
  notSpecial_const)
open EraseProof.Test.NVS (one app_typed' tr_const0 tr_const1)
open EraseProof.Test.NVL (mN mZ mS mN_typed mZ_typed mS_typed tr_N tr_S)
open EraseProof.Test.NVA (P view add_def addTy ζ13 n13 a13 E13 B13 E B hwf t_n13 t_at13 B13_N
  B13_s B13_add matchTyM motMM H1M H2M addTyM whredS_step defeq_rw)

/-! ## The Metalean term -/

/-- The head of `Nat.add.match_1` in `E13`. -/
abbrev m13 : Head ζ13 (.const .def 1) := .there (.there (.there (.there (.there .here))))

theorem B13_match : B13 `Nat.add.match_1 = some (.const m13) := rfl

theorem t_mt13 : (E13.get m13).constType = matchTyM n13 := by aenvs

/-- The motive `fun x y => Nat`, at any depth. -/
def motPM (n : Nat) : Metalean.Expr ζ13 0 n := .lam (mN n13) (.lam (mN n13) (mN n13))

/-- The alternatives `fun a => a` and `fun a b => Nat.succ (Nat.add a b)`, under `x y`. -/
def alt1PM : Metalean.Expr ζ13 0 2 := .lam (mN n13) #2
def alt2PM : Metalean.Expr ζ13 0 2 :=
  .lam (mN n13) (.lam (mN n13) (mS n13 (.app (.app (.const a13 Fin.elim0) #2) #3)))

/-- `pre[Nat.add]` in Metalean: `fun x y => Nat.add.match_1.{1} (fun x y => Nat) x y (fun a => a)
(fun a b => Nat.succ (Nat.add a b))`. -/
def preValM : Metalean.Expr ζ13 0 0 :=
  .lam (mN n13) (.lam (mN n13)
    (.app (.app (.app (.app (.app (.const m13 ![one]) (motPM 2)) #0) #1) alt1PM) alt2PM))

/-- `preVal` is the Lean form of `preValM`. -/
theorem tr_preVal : TrM E13 B13 [] .nil [] preVal preValM :=
  TrM.lam (tr_N B13_N) (TrM.lam (tr_N B13_N)
    (TrM.app (notSpecial_const B13_match ⟨_, rfl⟩)
      (TrM.app (notSpecial_const B13_match ⟨_, rfl⟩)
        (TrM.app (notSpecial_const B13_match ⟨_, rfl⟩)
          (TrM.app (notSpecial_const B13_match ⟨_, rfl⟩)
            (TrM.app (notSpecial_const B13_match ⟨_, rfl⟩) (tr_const1 B13_match rfl)
              (TrM.lam (tr_N B13_N) (TrM.lam (tr_N B13_N) (tr_N B13_N))))
            (TrM.bvar rfl))
          (TrM.bvar rfl))
        (TrM.lam (tr_N B13_N) (TrM.bvar rfl)))
      (TrM.lam (tr_N B13_N) (TrM.lam (tr_N B13_N)
        (tr_S B13_s (TrM.app (notSpecial_const B13_add ⟨_, rfl⟩)
          (TrM.app (notSpecial_const B13_add ⟨_, rfl⟩) (tr_const0 B13_add) (TrM.bvar rfl))
          (TrM.bvar rfl)))))))

/-- `Nat.add`'s type is the Lean form of `addTyM`. -/
theorem tr_addTy : TrM E13 B13 [] .nil [] addTy (addTyM n13) :=
  TrM.forallE (TrM.mdata (tr_N B13_N)) (TrM.forallE (TrM.mdata (tr_N B13_N)) (tr_N B13_N))

/-! ## Typing -/

theorem motPM_typed {n : Nat} {Γ : Ctx ζ13 0 0 n} :
    E13[Γ] ⊢ motPM n : .forallE (mN n13) (.forallE (mN n13) (.sort one)) :=
  .lamDF (mN_typed t_n13) (.forallEDF (mN_typed t_n13) .sortDF .sortDF)
    (.forallEDF (mN_typed t_n13) .sortDF .sortDF)
    (.lamDF (mN_typed t_n13) .sortDF .sortDF (mN_typed t_n13) (mN_typed t_n13))
    (.lamDF (mN_typed t_n13) .sortDF .sortDF (mN_typed t_n13) (mN_typed t_n13))

/-- The motive applied, by two β-steps. -/
theorem motPM_beta {n : Nat} {Γ : Ctx ζ13 0 0 n} {a b : Metalean.Expr ζ13 0 n} (hΓ : E13[Γ] ⊢ ok)
    (ha : E13[Γ] ⊢ a : mN n13) (hb : E13[Γ] ⊢ b : mN n13) :
    E13[Γ] ⊢ .app (.app (motPM n) a) b ≡ mN n13 : .sort one := by
  have hty := typed_of_eq (app_typed (typed_of_eq (app_typed motPM_typed ha)
    (T' := .forallE (mN n13) (.sort one)) (by arsx)) hb) (T' := .sort one) (by arsx)
  have h1 : E13 ⊢ .app (.app (motPM n) a) b ⤳*
      .app ((Metalean.Expr.lam (mN n13) (mN n13)).inst a) b :=
    .single (.frame (K := .app _) .beta)
  have h2 := whredS_step h1 .beta
  arsx at h2
  exact defeq_rw (WHRedS.defeq hwf hΓ h2 hty) rfl (by arsx [mN]) rfl

/-- `preValM` is typed at `Nat.add`'s type. -/
theorem preValM_typed : E13[.nil] ⊢ preValM : addTyM n13 := by
  have h1 : E13[(#t[mN n13] : Ctx ζ13 0 0 1)] ⊢ ok := .snoc .nil ⟨_, mN_typed t_n13⟩
  have hΓ : E13[(#t[mN n13, mN n13] : Ctx ζ13 0 0 2)] ⊢ ok := .snoc h1 ⟨_, mN_typed t_n13⟩
  have hx : E13[(#t[mN n13, mN n13] : Ctx ζ13 0 0 2)] ⊢ #0 : mN n13 :=
    var_of_get hΓ ⟨0, by decide⟩ (by arsx)
  have hy : E13[(#t[mN n13, mN n13] : Ctx ζ13 0 0 2)] ⊢ #1 : mN n13 :=
    var_of_get hΓ ⟨1, by decide⟩ (by arsx)
  -- `Nat.add.match_1.{1} motive x y`
  have h0 : E13[(#t[mN n13, mN n13] : Ctx ζ13 0 0 2)] ⊢ .const m13 ![one] :
      (E13.get m13).constType{![one]}.wkClosed := const_typed hwf m13 ![one] rfl
  rw [t_mt13] at h0
  arsx [matchTyM, motMM, H1M, H2M] at h0
  have hc1 := app_typed' h0 motPM_typed (by arsx [motPM])
  arsx at hc1
  have hc2 := app_typed' hc1 hx (by arsx)
  arsx at hc2
  have hc3 := app_typed' hc2 hy (by arsx)
  arsx at hc3
  -- `fun a => a`
  have h3 : E13[(#t[mN n13, mN n13, mN n13] : Ctx ζ13 0 0 3)] ⊢ ok := .snoc hΓ ⟨_, mN_typed t_n13⟩
  have ha3 : E13[(#t[mN n13, mN n13, mN n13] : Ctx ζ13 0 0 3)] ⊢ #2 : mN n13 :=
    var_of_get h3 ⟨2, by decide⟩ (by arsx)
  have hβz := motPM_beta h3 ha3 (mZ_typed t_n13)
  have hH1 : E13[(#t[mN n13, mN n13] : Ctx ζ13 0 0 2)] ⊢ alt1PM :
      .forallE (mN n13) (.app (.app (motPM 3) #2) (mZ n13)) :=
    .lamDF (mN_typed t_n13) hβz.left hβz.left (.defeqDF hβz.symm ha3) (.defeqDF hβz.symm ha3)
  have hc4 := app_typed' hc3 hH1 (by arsx [motPM])
  arsx at hc4
  -- `fun a b => Nat.succ (Nat.add a b)`
  have h4 : E13[(#t[mN n13, mN n13, mN n13, mN n13] : Ctx ζ13 0 0 4)] ⊢ ok :=
    .snoc h3 ⟨_, mN_typed t_n13⟩
  have ha4 : E13[(#t[mN n13, mN n13, mN n13, mN n13] : Ctx ζ13 0 0 4)] ⊢ #2 : mN n13 :=
    var_of_get h4 ⟨2, by decide⟩ (by arsx)
  have hb4 : E13[(#t[mN n13, mN n13, mN n13, mN n13] : Ctx ζ13 0 0 4)] ⊢ #3 : mN n13 :=
    var_of_get h4 ⟨3, by decide⟩ (by arsx)
  have hadd : E13[(#t[mN n13, mN n13, mN n13, mN n13] : Ctx ζ13 0 0 4)] ⊢
      .const a13 Fin.elim0 : .forallE (mN n13) (.forallE (mN n13) (mN n13)) :=
    const_typed hwf a13 Fin.elim0 (by rw [t_at13]; arsx [addTyM])
  have hcall := typed_of_eq (app_typed' (typed_of_eq (app_typed' hadd ha4 (by arsx))
    (T' := .forallE (mN n13) (mN n13)) (by arsx)) hb4 (by arsx)) (T' := mN n13) (by arsx)
  have hsx := mS_typed t_n13 hcall
  have hβs := motPM_beta h4 ha4 (mS_typed t_n13 hb4)
  have hH2b : E13[(#t[mN n13, mN n13, mN n13] : Ctx ζ13 0 0 3)] ⊢
      .lam (mN n13) (mS n13 (.app (.app (.const a13 Fin.elim0) #2) #3)) :
      .forallE (mN n13) (.app (.app (motPM 4) #2) (mS n13 #3)) :=
    .lamDF (mN_typed t_n13) hβs.left hβs.left (.defeqDF hβs.symm hsx) (.defeqDF hβs.symm hsx)
  have hH2ty : E13[(#t[mN n13, mN n13, mN n13] : Ctx ζ13 0 0 3)] ⊢
      .forallE (mN n13) (.app (.app (motPM 4) #2) (mS n13 #3)) : _ :=
    .forallEDF (mN_typed t_n13) hβs.left hβs.left
  have hH2 : E13[(#t[mN n13, mN n13] : Ctx ζ13 0 0 2)] ⊢ alt2PM :
      .forallE (mN n13) (.forallE (mN n13) (.app (.app (motPM 4) #2) (mS n13 #3))) :=
    .lamDF (mN_typed t_n13) hH2ty hH2ty hH2b hH2b
  have hc5 := app_typed' hc4 hH2 (by arsx [motPM])
  arsx at hc5
  -- the match's type, the motive applied to `x y`
  have hbody := Defeq.defeqDF (motPM_beta hΓ hx hy) (typed_of_eq hc5 (by arsx [motPM]))
  exact Ctx.lam_congr (Γ := .nil) (Δ := #t[mN n13, mN n13]) hΓ hbody

/-! ## The premise -/

/-- Under `cfgU` the declaration of `P` with a compiled pre-definition is `Nat.add`, its sixth. -/
theorem preDef_P : (List.range P.length).all (fun k =>
    k == 5 || !((P[k]?).bind (Erasure.preDef? view cfgU)).isSome) = true := by krfl

/-- `hpre`: the compiled pre-definition of `Nat.add`, the only one of `P` (`preDef_P`), names only
`Nat.add` and declarations after it in `P`, names `Nat.add` at its own (empty) level parameters,
and it is the Lean form of `preValM`, typed at the translation of `Nat.add`'s type. Reference: none (DV-31). -/
theorem hpre : PreDefsOK E B view cfgU P := by
  intro P₁ ci P₀ pre hP hpd
  have hk : P₁.length < P.length := by rw [hP]; simp
  have hci : P[P₁.length]? = some ci := by rw [hP]; simp
  have hP₀ : P.drop (P₁.length + 1) = P₀ := by rw [hP]; simp
  have h5 := List.all_eq_true.mp preDef_P _ (List.mem_range.mpr hk)
  rw [hci, Option.bind_some, hpd] at h5
  have h5' : P₁.length = 5 := by simpa using h5
  rw [h5'] at hci hP₀
  obtain rfl : ci = .defnInfo add_def := Option.some.inj (hci.symm.trans rfl)
  subst hP₀
  obtain rfl : pre = preVal := Option.some.inj (hpd.symm.trans preDef_add)
  refine ⟨?_, ?_, preValM, addTyM n13, tr_preVal, tr_addTy, preValM_typed⟩
  · simp only [ConstsIn, preVal, motPre, altPre1, altPre2, EraseProof.Test.NVL.tN,
      EraseProof.Test.NVL.cS, and_true]
    and_intros
    all_goals first | exact .inl rfl | exact .inr (by krfl)
  · simp only [ConstAt, preVal, motPre, altPre1, altPre2, EraseProof.Test.NVL.tN,
      EraseProof.Test.NVL.cS, and_true]
    and_intros
    all_goals intro h; first | rfl | exact absurd h (by decide)

end EraseProof.Test.NVU
