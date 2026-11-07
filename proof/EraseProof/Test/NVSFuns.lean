import EraseProof.Test.NVSDefs

/-!
# NV-S: the Metalean definitions `Unit`, `Unit.unit`, `add.match_1`, `add._f`, `add`

Their Metalean forms (`Test/NVSData.lean`) and the typing of their values at their types, in any
well-formed environment whose heads hold the blocks and the earlier definitions (the hypotheses on
the heads' types and values). `add._f`'s second minor premise reads the recursive call as the
first projection `x.1` of the table `x : N.below (fun m => N) (N.s k)`, typed through the
unfolding of the table to `PProd N (N.below (fun m => N) k)` (`belowS_defeq_motNL`). For
`Test/NVSModel.lean`.
-/

open Lean Metalean

namespace EraseProof.Test.NVS

open EraseProof.Test.NV1 (typed_of_eq var_of_get app_typed const_typed fin0_eq lu)
open EraseProof.Test.NVR (nSig nBlock mN mZ mS mN_typed mZ_typed mS_typed indN_typed recAllowedN
  appMotN_typed motN_typed)

/-- Application at a Π-type whose domain equals the argument's type. -/
theorem app_typed' {ζ : Sigs} {E : Env ζ} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} {f a t t₀ : Expr ζ ℓ n}
    {t' : Expr ζ ℓ (n + 1)} (hf : E[Γ] ⊢ f : .forallE t t') (ha : E[Γ] ⊢ a : t₀) (h : t₀ = t) :
    E[Γ] ⊢ .app f a : t'.inst a :=
  app_typed hf (h ▸ ha)

/-- `1` -/
abbrev one {ℓ : Nat} : Level ℓ := .succ .zero

section Defs
variable {ζ : Sigs} (ηPU : Head ζ (.inductive puSig)) (ηPP : Head ζ (.inductive ppSig))
  (ηN : Head ζ (.inductive nSig)) (ηU ηUU : Head ζ (.const .def 0))
  (ηC ηBl ηBr ηM : Head ζ (.const .def 1)) (ηF : Head ζ (.const .def 0))

/-- `Unit`, `Unit.unit` as constants. -/
def unitM {ℓ n : Nat} : Expr ζ ℓ n := .const ηU Fin.elim0
def unitUM {ℓ n : Nat} : Expr ζ ℓ n := .const ηUU Fin.elim0

/-- `add.match_1`'s type `(motive : N → Sort u_1) → (m : N) → (Unit → motive N.z) →
((k : N) → motive (N.s k)) → motive m`. -/
def matchTyM : Expr ζ 1 0 :=
  .forallE (motNM ηN lu) (.forallE (mN ηN) (.forallE (.forallE (unitM ηU) (.app #0 (mZ ηN)))
    (.forallE (.forallE (mN ηN) (.app #0 (mS ηN #3))) (.app #0 #1))))

/-- `fun motive m h_1 h_2 => N.casesOn (fun x => motive x) m (h_1 Unit.unit) (fun n => h_2 n)` -/
def matchValM : Expr ζ 1 0 :=
  .lam (motNM ηN lu) (.lam (mN ηN) (.lam (.forallE (unitM ηU) (.app #0 (mZ ηN)))
    (.lam (.forallE (mN ηN) (.app #0 (mS ηN #3)))
      (.app (.app (.app (.app (.const ηC ![lu]) (.lam (mN ηN) (.app #0 #4))) #1)
        (.app #2 (unitUM ηUU))) (.lam (mN ηN) (.app #3 #4))))))

/-- `(n m : N) → N.below (fun m => N) m → N` -/
def fTyM : Expr ζ 0 0 :=
  .forallE (mN ηN) (.forallE (mN ηN) (.forallE (belowM ηBl one (motNL ηN) #1) (mN ηN)))

/-- `x.1` for `x : N.below (fun m => N) (N.s k)` under `n m f k x`, as Metalean's structure
projection computes it at the parameters `(fun m => N) k` and `N.below (fun m => N) k`. -/
def projFstF : Expr ζ 0 5 :=
  .recr ηPP 0 ![one, m1 one] one ![.app (motNL ηN) #3, belowM ηBl one (motNL ηN) #3]
    (fun _ => .lam (mPP ηPP one (m1 one) (.app (motNL ηN) #3) (belowM ηBl one (motNL ηN) #3))
      (.app (motNL ηN) #3))
    (fun _ _ => .lam (.app (motNL ηN) #3) (.lam (belowM ηBl one (motNL ηN) #3) #5)) Fin.elim0 #4

/-- `fun n m f => add.match_1 (fun m => N.below (fun m => N) m → N) m (fun _ x => n)
(fun k x => N.s x.1) f` -/
def fValM : Expr ζ 0 0 :=
  .lam (mN ηN) (.lam (mN ηN) (.lam (belowM ηBl one (motNL ηN) #1)
    (.app (.app (.app (.app (.app (.const ηM ![one])
      (.lam (mN ηN) (.forallE (belowM ηBl one (motNL ηN) #3) (mN ηN)))) #1)
      (.lam (unitM ηU) (.lam (belowM ηBl one (motNL ηN) (mZ ηN)) #0)))
      (.lam (mN ηN) (.lam (belowM ηBl one (motNL ηN) (mS ηN #3))
        (mS ηN (projFstF ηPP ηN ηBl))))) #2)))

/-- `(n m : N) → N` -/
def addTyM : Expr ζ 0 0 := .forallE (mN ηN) (.forallE (mN ηN) (mN ηN))

/-- `fun n m => N.brecOn (fun m => N) m (add._f n)` -/
def addValM : Expr ζ 0 0 :=
  .lam (mN ηN) (.lam (mN ηN) (.app (.app (.app (.const ηBr ![one]) (motNL ηN)) #1)
    (.app (.const ηF Fin.elim0) #0)))

end Defs

theorem projTerm_eqFstF {ζ : Sigs} {ηPP : Head ζ (.inductive ppSig)} {ηN : Head ζ (.inductive nSig)}
    {ηBl : Head ζ (.const .def 1)} {I : Inductive ζ ppSig} (h : I.IsStructure 0 0)
    (hI : I = ppBlock) :
    h.projTerm ηPP ![one, m1 one] ![.app (motNL ηN) #3, belowM ηBl one (motNL ηN) #3]
      ⟨0, by decide⟩ (#4 : Expr ζ 0 5) = projFstF ηPP ηN ηBl := by
  subst hI
  rw [Inductive.IsStructure.projTerm_eq_recr]
  simp only [projFstF]
  congr 1
  case e_ms =>
    funext t; fin_cases t
    delta Inductive.IsStructure.projectionMotives
    rsx [Inductive.IsStructure.projTypeWith, Inductive.motiveTele, Inductive.indexTele, Ctx.substN]
  case e_mins =>
    funext t c; fin_cases t; fin_cases c
    delta Inductive.IsStructure.projectionCases
    rsx [Inductive.caseTele, CtorSig.caseOrdinary,
      CtorSig.fieldOrdinary, Ctor.fieldTele, Ctor.ordinaryFieldTele, Ctor.ordinaryTeleAux,
      Ctor.ihTele, Ctx.ofTypes, Ctor.recursiveFieldTeleAux, Expr.boundVars,
      Ctor.ordinaryFieldTeleAux, Tele.foldr, Ctx.substN, Subst.liftN]

theorem projType_eqFstF {ζ : Sigs} {ηPP : Head ζ (.inductive ppSig)} {ηN : Head ζ (.inductive nSig)}
    {ηBl : Head ζ (.const .def 1)} {I : Inductive ζ ppSig} (h : I.IsStructure 0 0)
    (hI : I = ppBlock) :
    h.projType ηPP ![one, m1 one] ![.app (motNL ηN) #3, belowM ηBl one (motNL ηN) #3]
      ⟨0, by decide⟩ (#4 : Expr ζ 0 5) = .app (motNL ηN) #3 := by
  subst hI
  rw [Inductive.IsStructure.projType, Inductive.IsStructure.projection]
  simp only [Inductive.IsStructure.projTypeWith]
  rsx

section Typed
variable {ζ : Sigs} {E : Env ζ} {ηPU : Head ζ (.inductive puSig)} {ηPP : Head ζ (.inductive ppSig)}
  {ηN : Head ζ (.inductive nSig)} {ηU ηUU : Head ζ (.const .def 0)}
  {ηC ηBl ηBr ηM : Head ζ (.const .def 1)} {ηF : Head ζ (.const .def 0)}
  (hE : EnvWF E) (hn : (E.get ηN).block = nBlock) (hpu : (E.get ηPU).block = puBlock)
  (hpp : (E.get ηPP).block = ppBlock)

/-! ### `Unit`, `Unit.unit` -/

include hpu in
theorem unitVal_typed : E[.nil] ⊢ (mPU ηPU one : Expr ζ 0 0) : .sort one := mPU_typed hpu

include hE hpu in
/-- `Unit.unit`'s value `PUnit.unit.{1}` at its type `Unit`, by δ of `Unit`. -/
theorem unitUVal_typed (hut : (E.get ηU).constType = .sort one)
    (huv : (E.get ηU).defValue = mPU ηPU one) :
    E[.nil] ⊢ (mPUu ηPU one : Expr ζ 0 0) : unitM ηU := by
  have hc : E[(.nil : Ctx ζ 0 0 0)] ⊢ unitM ηU : .sort one :=
    const_typed hE ηU Fin.elim0 (by rw [hut]; rsx)
  have hd := WHRed.delta_defeq (Γ := .nil) hE hc
  rw [huv] at hd
  exact .defeqDF (defeq_rw hd rfl (by rsx) rfl).symm (mPUu_typed hpu)

/-! ### `add.match_1` -/

/-- `add.match_1`'s binder context `motive m h_1 h_2`. -/
def ΓM (ηN : Head ζ (.inductive nSig)) (ηU : Head ζ (.const .def 0)) : Ctx ζ 1 0 4 :=
  #t[motNM ηN lu, mN ηN, .forallE (unitM ηU) (.app #0 (mZ ηN)),
    .forallE (mN ηN) (.app #0 (mS ηN #3))]

include hE hn in
theorem matchValM_typed (hut : (E.get ηU).constType = .sort one)
    (huut : (E.get ηUU).constType = unitM ηU) (hct : (E.get ηC).constType = casesOnTyM ηN) :
    E[.nil] ⊢ matchValM ηN ηU ηUU ηC : matchTyM ηN ηU := by
  have hU : ∀ {n : Nat} {Γ : Ctx ζ 1 0 n}, E[Γ] ⊢ unitM ηU : .sort one := fun {_ _} =>
    const_typed hE ηU Fin.elim0 (by rw [hut]; rsx)
  have h1 : E[(#t[motNM ηN lu] : Ctx ζ 1 0 1)] ⊢ ok := .snoc .nil ⟨_, motN_typed hn⟩
  have h2 : E[(#t[motNM ηN lu, mN ηN] : Ctx ζ 1 0 2)] ⊢ ok := .snoc h1 ⟨_, mN_typed hn⟩
  have h2u : E[(#t[motNM ηN lu, mN ηN, unitM ηU] : Ctx ζ 1 0 3)] ⊢ ok := .snoc h2 ⟨_, hU⟩
  have hz2 := appMotN_typed hn (var_of_get (T := motNM ηN lu) h2u ⟨0, by decide⟩ (by rsx))
    (mZ_typed hn)
  have hH1 : E[(#t[motNM ηN lu, mN ηN] : Ctx ζ 1 0 2)] ⊢ .forallE (unitM ηU) (.app #0 (mZ ηN)) :
      _ := .forallEDF hU hz2 hz2
  have h3 : E[(#t[motNM ηN lu, mN ηN, .forallE (unitM ηU) (.app #0 (mZ ηN))] : Ctx ζ 1 0 3)] ⊢
      ok := .snoc h2 ⟨_, hH1⟩
  have h3n : E[(#t[motNM ηN lu, mN ηN, .forallE (unitM ηU) (.app #0 (mZ ηN)), mN ηN] :
      Ctx ζ 1 0 4)] ⊢ ok := .snoc h3 ⟨_, mN_typed hn⟩
  have hs3 := appMotN_typed hn (var_of_get (T := motNM ηN lu) h3n ⟨0, by decide⟩ (by rsx))
    (mS_typed hn (var_of_get h3n ⟨3, by decide⟩ (by rsx)))
  have hΓ : E[ΓM ηN ηU] ⊢ ok := .snoc h3 ⟨_, .forallEDF (mN_typed hn) hs3 hs3⟩
  have hm : E[ΓM ηN ηU] ⊢ #0 : motNM ηN lu := var_of_get hΓ ⟨0, by decide⟩ (by rsx [ΓM])
  have hmv : E[ΓM ηN ηU] ⊢ #1 : mN ηN := var_of_get hΓ ⟨1, by decide⟩ (by rsx [ΓM])
  have hh1 : E[ΓM ηN ηU] ⊢ #2 : .forallE (unitM ηU) (.app #0 (mZ ηN)) :=
    var_of_get hΓ ⟨2, by decide⟩ (by rsx [ΓM, unitM])
  have hh2 : E[ΓM ηN ηU] ⊢ #3 : .forallE (mN ηN) (.app #0 (mS ηN #4)) :=
    var_of_get hΓ ⟨3, by decide⟩ (by rsx [ΓM])
  -- the motive `fun x => motive x`
  have h5 : E[(ΓM ηN ηU).snoc (mN ηN)] ⊢ ok := .snoc hΓ ⟨_, mN_typed hn⟩
  have hm5 : E[(ΓM ηN ηU).snoc (mN ηN)] ⊢ #0 : motNM ηN lu :=
    var_of_get h5 ⟨0, by decide⟩ (by rsx [ΓM])
  have hv5 : E[(ΓM ηN ηU).snoc (mN ηN)] ⊢ #4 : mN ηN := var_of_get h5 ⟨4, by decide⟩ (by rsx)
  have hb5 := appMotN_typed hn hm5 hv5
  have hmot : E[ΓM ηN ηU] ⊢ .lam (mN ηN) (.app #0 #4) : motNM ηN lu :=
    .lamDF (mN_typed hn) .sortDF .sortDF hb5 hb5
  have hβ : ∀ {k : Nat} {Γ : Ctx ζ 1 0 (k + 4)} {a : Expr ζ 1 (k + 4)}, E[Γ] ⊢ ok →
      E[Γ] ⊢ .var ⟨0, by omega⟩ : motNM ηN lu → E[Γ] ⊢ a : mN ηN →
      E[Γ] ⊢ .app (.lam (mN ηN) (.app (.var ⟨0, by omega⟩) (.var (Fin.last (k + 4))))) a ≡
        .app (.var ⟨0, by omega⟩) a : .sort lu := by
    intro k Γ a hΓk hmk ha
    have hΓk' : E[Γ.snoc (mN ηN)] ⊢ ok := .snoc hΓk ⟨_, mN_typed hn⟩
    have hmk' : E[Γ.snoc (mN ηN)] ⊢ .var ⟨0, by omega⟩ : motNM ηN lu :=
      defeq_rw (hmk.wk (mN ηN)) (by rsx) (by rsx) (by rsx)
    have hl : E[Γ.snoc (mN ηN)] ⊢ .var (Fin.last (k + 4)) : mN ηN :=
      var_of_get hΓk' _ (by rw [Ctx.get_last]; rsx)
    exact defeq_rw (beta_defeq (mN_typed hn) .sortDF (appMotN_typed hn hmk' hl) ha) rfl
      (by rsx) (by rsx)
  -- `N.casesOn (fun x => motive x) m`
  have h0 : E[ΓM ηN ηU] ⊢ .const ηC ![lu] : (E.get ηC).constType{![lu]}.wkClosed :=
    const_typed hE ηC ![lu] rfl
  rw [hct] at h0
  rsx [casesOnTyM] at h0
  have hc1 := app_typed' h0 hmot (by rsx)
  rsx at hc1
  have hc2 := app_typed' hc1 hmv (by rsx)
  rsx at hc2
  -- `h_1 Unit.unit`
  have huu : E[ΓM ηN ηU] ⊢ unitUM ηUU : unitM ηU :=
    const_typed hE ηUU Fin.elim0 (by rw [huut]; rsx [unitM])
  have hz := typed_of_eq (app_typed hh1 huu) (T' := .app #0 (mZ ηN)) (by rsx)
  have hz' := Defeq.defeqDF (hβ (k := 0) hΓ hm (mZ_typed hn)).symm hz
  have hc3 := app_typed' hc2 hz' (by rsx)
  rsx at hc3
  -- `fun n => h_2 n`
  have hb5' := typed_of_eq (app_typed (defeq_rw (hh2.wk (mN ηN)) (by rsx) (by rsx) (by rsx) :
      E[(ΓM ηN ηU).snoc (mN ηN)] ⊢ #3 : .forallE (mN ηN) (.app #0 (mS ηN #5))) hv5)
    (T' := .app #0 (mS ηN #4)) (by rsx)
  have hr5 := appMotN_typed hn hm5 (mS_typed hn hv5)
  have hβ5 := hβ (k := 1) h5 hm5 (mS_typed hn hv5)
  have hs : E[ΓM ηN ηU] ⊢ .lam (mN ηN) (.app #3 #4) :
      .forallE (mN ηN) (.app (.lam (mN ηN) (.app #0 #5)) (mS ηN #4)) :=
    .lamDF (mN_typed hn) hβ5.left hβ5.left (.defeqDF hβ5.symm hb5') (.defeqDF hβ5.symm hb5')
  have hc4 := app_typed' hc3 hs (by rsx)
  rsx at hc4
  have hbody := Defeq.defeqDF (hβ (k := 0) hΓ hm hmv) (typed_of_eq hc4 (by rsx))
  exact Ctx.lam_congr (Γ := .nil) (Δ := ΓM ηN ηU) hΓ hbody

/-! ### `add._f`, `add` -/

include hn in
theorem motNL_typed {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} : E[Γ] ⊢ motNL ηN : motNM ηN one :=
  .lamDF (mN_typed hn) .sortDF .sortDF (mN_typed hn) (mN_typed hn)

include hn in
/-- `(fun m => N) a ≡ N`. -/
theorem motNL_beta {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} {a : Expr ζ ℓ n} (ha : E[Γ] ⊢ a : mN ηN) :
    E[Γ] ⊢ .app (motNL ηN) a ≡ mN ηN : .sort one :=
  defeq_rw (beta_defeq (mN_typed hn) .sortDF (mN_typed hn) ha) rfl (by rsx) (by rsx)

/-- `add._f`'s binder context `n m f`. -/
def ΓF (ηN : Head ζ (.inductive nSig)) (ηBl : Head ζ (.const .def 1)) : Ctx ζ 0 0 3 :=
  #t[mN ηN, mN ηN, belowM ηBl one (motNL ηN) #1]

theorem imax_m1_one {ℓ : Nat} : (Level.imax (m1 one) one : Level ℓ) = one :=
  Level.ext fun ν => by simp [Nat.imax]

include hE hn hpp in
theorem fValM_typed (ht : (E.get ηBl).constType = belowTyM ηN)
    (hv : (E.get ηBl).defValue = belowValM ηPU ηPP ηN) (hut : (E.get ηU).constType = .sort one)
    (hmt : (E.get ηM).constType = matchTyM ηN ηU) :
    E[.nil] ⊢ fValM ηPP ηN ηU ηBl ηM : fTyM ηN ηBl := by
  have hU : ∀ {n : Nat} {Γ : Ctx ζ 0 0 n}, E[Γ] ⊢ unitM ηU : .sort one := fun {_ _} =>
    const_typed hE ηU Fin.elim0 (by rw [hut]; rsx)
  have hb : ∀ {n : Nat} {Γ : Ctx ζ 0 0 n} {a : Expr ζ 0 n}, E[Γ] ⊢ a : mN ηN →
      E[Γ] ⊢ belowM ηBl one (motNL ηN) a : .sort (m1 one) := fun ha =>
    belowM_typed hE ht (motNL_typed hn) ha
  have h1 : E[(#t[mN ηN] : Ctx ζ 0 0 1)] ⊢ ok := .snoc .nil ⟨_, mN_typed hn⟩
  have h2 : E[(#t[mN ηN, mN ηN] : Ctx ζ 0 0 2)] ⊢ ok := .snoc h1 ⟨_, mN_typed hn⟩
  have hΓ : E[ΓF ηN ηBl] ⊢ ok :=
    .snoc h2 ⟨_, hb (var_of_get h2 ⟨1, by decide⟩ (by rsx))⟩
  have hn0 : E[ΓF ηN ηBl] ⊢ #0 : mN ηN := var_of_get hΓ ⟨0, by decide⟩ (by rsx [ΓF])
  have hmv : E[ΓF ηN ηBl] ⊢ #1 : mN ηN := var_of_get hΓ ⟨1, by decide⟩ (by rsx [ΓF])
  have hf : E[ΓF ηN ηBl] ⊢ #2 : belowM ηBl one (motNL ηN) #1 :=
    var_of_get hΓ ⟨2, by decide⟩ (by rsx [ΓF])
  -- the motive `fun m => N.below (fun m => N) m → N`
  have h4 : E[(ΓF ηN ηBl).snoc (mN ηN)] ⊢ ok := .snoc hΓ ⟨_, mN_typed hn⟩
  have hbm := hb (var_of_get (T := mN ηN) h4 ⟨3, by decide⟩ (by rsx))
  have h5 : E[((ΓF ηN ηBl).snoc (mN ηN)).snoc (belowM ηBl one (motNL ηN) #3)] ⊢ ok :=
    .snoc h4 ⟨_, hbm⟩
  have hpi : E[(ΓF ηN ηBl).snoc (mN ηN)] ⊢ .forallE (belowM ηBl one (motNL ηN) #3) (mN ηN) :
      .sort one := by
    have h := Defeq.forallEDF hbm (mN_typed hn (Γ := ((ΓF ηN ηBl).snoc (mN ηN)).snoc
      (belowM ηBl one (motNL ηN) #3))) (mN_typed hn)
    rwa [imax_m1_one] at h
  have hMF : E[ΓF ηN ηBl] ⊢ .lam (mN ηN) (.forallE (belowM ηBl one (motNL ηN) #3) (mN ηN)) :
      motNM ηN one := .lamDF (mN_typed hn) .sortDF .sortDF hpi hpi
  -- `fun m => …` applied: β
  have hβF : ∀ {n : Nat} {Γ : Ctx ζ 0 0 n} {a : Expr ζ 0 n}, E[Γ] ⊢ ok → E[Γ] ⊢ a : mN ηN →
      E[Γ] ⊢ .app (.lam (mN ηN) (.forallE (belowM ηBl one (motNL ηN) (.var (Fin.last n)))
        (mN ηN))) a ≡ .forallE (belowM ηBl one (motNL ηN) a) (mN ηN) : .sort one := by
    intro n Γ a hΓn ha
    have hΓ1 : E[Γ.snoc (mN ηN)] ⊢ ok := .snoc hΓn ⟨_, mN_typed hn⟩
    have hl : E[Γ.snoc (mN ηN)] ⊢ .var (Fin.last n) : mN ηN :=
      var_of_get hΓ1 _ (by rw [Ctx.get_last]; rsx)
    have hpi' : E[Γ.snoc (mN ηN)] ⊢ .forallE (belowM ηBl one (motNL ηN) (.var (Fin.last n)))
        (mN ηN) : .sort one := by
      have h := Defeq.forallEDF (hb hl) (mN_typed hn (Γ := (Γ.snoc (mN ηN)).snoc
        (belowM ηBl one (motNL ηN) (.var (Fin.last n))))) (mN_typed hn)
      rwa [imax_m1_one] at h
    exact defeq_rw (beta_defeq (mN_typed hn) .sortDF hpi' ha) rfl (by rsx) (by rsx)
  have h0 : E[ΓF ηN ηBl] ⊢ .const ηM ![one] : (E.get ηM).constType{![one]}.wkClosed :=
    const_typed hE ηM ![one] rfl
  rw [hmt] at h0
  rsx [matchTyM, unitM] at h0
  have hc1 := app_typed' h0 hMF (by rsx)
  rsx at hc1
  have hc2 := app_typed' hc1 hmv (by rsx)
  rsx at hc2
  -- `fun _ x => n`
  have hu4 : E[(ΓF ηN ηBl).snoc (unitM ηU)] ⊢ ok := .snoc hΓ ⟨_, hU⟩
  have hbz := hb (Γ := (ΓF ηN ηBl).snoc (unitM ηU)) (mZ_typed hn)
  have hu5 : E[((ΓF ηN ηBl).snoc (unitM ηU)).snoc (belowM ηBl one (motNL ηN) (mZ ηN))] ⊢ ok :=
    .snoc hu4 ⟨_, hbz⟩
  have hn5 : E[((ΓF ηN ηBl).snoc (unitM ηU)).snoc (belowM ηBl one (motNL ηN) (mZ ηN))] ⊢ #0 :
      mN ηN := var_of_get hu5 ⟨0, by decide⟩ (by rsx [ΓF])
  have hβz := hβF (n := 4) hu4 (mZ_typed hn)
  have hpiz := hβz.right
  have hH1in : E[(ΓF ηN ηBl).snoc (unitM ηU)] ⊢ .lam (belowM ηBl one (motNL ηN) (mZ ηN)) #0 :
      .app (.lam (mN ηN) (.forallE (belowM ηBl one (motNL ηN) #4) (mN ηN))) (mZ ηN) :=
    .defeqDF hβz.symm (.lamDF hbz (mN_typed hn) (mN_typed hn) hn5 hn5)
  have hH1 : E[ΓF ηN ηBl] ⊢ .lam (unitM ηU) (.lam (belowM ηBl one (motNL ηN) (mZ ηN)) #0) :
      .forallE (unitM ηU) (.app (.lam (mN ηN) (.forallE (belowM ηBl one (motNL ηN) #4) (mN ηN)))
        (mZ ηN)) := .lamDF hU hβz.left hβz.left hH1in hH1in
  have hc3 := app_typed' hc2 hH1 (by rsx [unitM])
  rsx at hc3
  -- `fun k x => N.s x.1`
  have hk4 : E[(ΓF ηN ηBl).snoc (mN ηN)] ⊢ #3 : mN ηN := var_of_get h4 ⟨3, by decide⟩ (by rsx)
  have hbs := hb (Γ := (ΓF ηN ηBl).snoc (mN ηN)) (mS_typed hn hk4)
  have hk5 : E[((ΓF ηN ηBl).snoc (mN ηN)).snoc (belowM ηBl one (motNL ηN) (mS ηN #3))] ⊢ ok :=
    .snoc h4 ⟨_, hbs⟩
  have hk : E[((ΓF ηN ηBl).snoc (mN ηN)).snoc (belowM ηBl one (motNL ηN) (mS ηN #3))] ⊢ #3 :
      mN ηN := var_of_get hk5 ⟨3, by decide⟩ (by rsx)
  have hx : E[((ΓF ηN ηBl).snoc (mN ηN)).snoc (belowM ηBl one (motNL ηN) (mS ηN #3))] ⊢ #4 :
      belowM ηBl one (motNL ηN) (mS ηN #3) := var_of_get hk5 ⟨4, by decide⟩ (by rsx)
  have hS := belowS_defeq_motNL hE hn hpp ht hv hk5 (motNL_typed hn) hk
  have hst : (E.get ηPP).block.IsStructure 0 0 := hpp ▸ ppStruct
  have hB : InductiveWF E (E.get ηPP).block := (hE.entryWF ηPP).block
  have hps := ppParams hpp (appMotN_typed hn (motNL_typed hn) hk) (hb hk)
  have hmaj : E[((ΓF ηN ηBl).snoc (mN ηN)).snoc (belowM ηBl one (motNL ηN) (mS ηN #3))] ⊢ #4 :
      .ind ηPP 0 ![one, m1 one] ![.app (motNL ηN) #3, belowM ηBl one (motNL ηN) #3]
        hst.indices := by
    rw [← hst.indices_eq Fin.elim0]
    exact .defeqDF hS hx
  have hp := hst.projTerm_hasType hB ⟨0, by decide⟩ hk5 hps hmaj
  rw [projTerm_eqFstF hst hpp, projType_eqFstF hst hpp] at hp
  have hsx := mS_typed hn (.defeqDF (motNL_beta hn hk) hp)
  have hβs := hβF (n := 4) h4 (mS_typed hn hk4)
  have hH2in : E[(ΓF ηN ηBl).snoc (mN ηN)] ⊢ .lam (belowM ηBl one (motNL ηN) (mS ηN #3))
      (mS ηN (projFstF ηPP ηN ηBl)) :
      .app (.lam (mN ηN) (.forallE (belowM ηBl one (motNL ηN) #4) (mN ηN))) (mS ηN #3) :=
    .defeqDF hβs.symm (.lamDF hbs (mN_typed hn) (mN_typed hn) hsx hsx)
  have hH2 : E[ΓF ηN ηBl] ⊢ .lam (mN ηN) (.lam (belowM ηBl one (motNL ηN) (mS ηN #3))
      (mS ηN (projFstF ηPP ηN ηBl))) :
      .forallE (mN ηN) (.app (.lam (mN ηN) (.forallE (belowM ηBl one (motNL ηN) #4) (mN ηN)))
        (mS ηN #3)) := .lamDF (mN_typed hn) hβs.left hβs.left hH2in hH2in
  have hc4 := app_typed' hc3 hH2 (by rsx)
  rsx at hc4
  have hβm := hβF (n := 3) hΓ hmv
  have hc4' := Defeq.defeqDF hβm (typed_of_eq hc4 (by rsx))
  have hbody := typed_of_eq (app_typed hc4' hf) (T' := mN ηN) (by rsx)
  exact Ctx.lam_congr (Γ := .nil) (Δ := ΓF ηN ηBl) hΓ hbody

include hE hn in
theorem addValM_typed (hbt : (E.get ηBr).constType = brecOnTyM ηN ηBl)
    (hft : (E.get ηF).constType = fTyM ηN ηBl)
    (ht : (E.get ηBl).constType = belowTyM ηN) :
    E[.nil] ⊢ addValM ηN ηBr ηF : addTyM ηN := by
  have h1 : E[(#t[mN ηN] : Ctx ζ 0 0 1)] ⊢ ok := .snoc .nil ⟨_, mN_typed hn⟩
  have hΓ : E[(#t[mN ηN, mN ηN] : Ctx ζ 0 0 2)] ⊢ ok := .snoc h1 ⟨_, mN_typed hn⟩
  have hn0 : E[(#t[mN ηN, mN ηN] : Ctx ζ 0 0 2)] ⊢ #0 : mN ηN :=
    var_of_get hΓ ⟨0, by decide⟩ (by rsx)
  have hmv : E[(#t[mN ηN, mN ηN] : Ctx ζ 0 0 2)] ⊢ #1 : mN ηN :=
    var_of_get hΓ ⟨1, by decide⟩ (by rsx)
  have h0 : E[(#t[mN ηN, mN ηN] : Ctx ζ 0 0 2)] ⊢ .const ηBr ![one] :
      (E.get ηBr).constType{![one]}.wkClosed := const_typed hE ηBr ![one] rfl
  rw [hbt] at h0
  rsx [brecOnTyM, F1TyM] at h0
  have hc1 := app_typed' h0 (motNL_typed hn) (by rsx)
  rsx at hc1
  have hc2 := app_typed' hc1 hmv (by rsx)
  rsx at hc2
  have hf0 : E[(#t[mN ηN, mN ηN] : Ctx ζ 0 0 2)] ⊢ .const ηF Fin.elim0 :
      (E.get ηF).constType{(Fin.elim0 : Fin 0 → Level 0)}.wkClosed := const_typed hE ηF Fin.elim0 rfl
  rw [hft] at hf0
  rsx [fTyM] at hf0
  have hf1 := app_typed' hf0 hn0 (by rsx)
  rsx at hf1
  -- `add._f n : (m : N) → N.below (fun m => N) m → N` at `(t : N) → N.below _ t → (fun m => N) t`
  have h3 : E[(#t[mN ηN, mN ηN, mN ηN] : Ctx ζ 0 0 3)] ⊢ ok := .snoc hΓ ⟨_, mN_typed hn⟩
  have hv3 : E[(#t[mN ηN, mN ηN, mN ηN] : Ctx ζ 0 0 3)] ⊢ #2 : mN ηN :=
    var_of_get h3 ⟨2, by decide⟩ (by rsx)
  have hb3 := belowM_typed hE ht (motNL_typed hn) hv3
  have hTy : ∀ {A : Expr ζ 0 3}, E[(#t[mN ηN, mN ηN, mN ηN] : Ctx ζ 0 0 3)] ⊢ A : .sort (m1 one) →
      E[(#t[mN ηN, mN ηN, mN ηN] : Ctx ζ 0 0 3).snoc A] ⊢ .app (motNL ηN) #2 ≡ mN ηN :
        .sort one := by
    intro A hA
    have h4 : E[(#t[mN ηN, mN ηN, mN ηN] : Ctx ζ 0 0 3).snoc A] ⊢ ok := .snoc h3 ⟨_, hA⟩
    exact motNL_beta hn (var_of_get h4 ⟨2, by decide⟩ (by rsx))
  have hin : E[(#t[mN ηN, mN ηN, mN ηN] : Ctx ζ 0 0 3)] ⊢
      .forallE (belowM ηBl one (motNL ηN) #2) (.app (motNL ηN) #2) ≡
      .forallE (belowM ηBl one (motNL ηN) #2) (mN ηN) : .sort (.imax (m1 one) one) :=
    .forallEDF hb3 (hTy hb3) (hTy hb3)
  have hFt : E[(#t[mN ηN, mN ηN] : Ctx ζ 0 0 2)] ⊢
      .forallE (mN ηN) (.forallE (belowM ηBl one (motNL ηN) #2) (.app (motNL ηN) #2)) ≡
      .forallE (mN ηN) (.forallE (belowM ηBl one (motNL ηN) #2) (mN ηN)) : _ :=
    .forallEDF (mN_typed hn) hin hin
  have hF := Defeq.defeqDF hFt.symm (typed_of_eq hf1 (by rsx))
  have hc3 := app_typed' hc2 hF (by rsx)
  rsx at hc3
  have hbody := Defeq.defeqDF (motNL_beta hn hmv) (typed_of_eq hc3 (by rsx))
  exact Ctx.lam_congr (Γ := .nil) (Δ := #t[mN ηN, mN ηN]) hΓ hbody

end Typed

end EraseProof.Test.NVS
