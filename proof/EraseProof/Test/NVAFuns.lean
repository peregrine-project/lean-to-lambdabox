import EraseProof.Test.NVADefs
import EraseProof.Test.NVSFuns

/-!
# NV-A: the Metalean definitions `Nat.add.match_1`, `Nat.add._f`, `Nat.add`

Their Metalean forms (`Test/NVAData.lean`) and the typing of their values at their types, in any
well-formed environment whose heads hold the blocks and the earlier definitions (the hypotheses on
the heads' types and values). `Nat.add.match_1` is a `Nat.casesOn` on the second of its two
discriminants, at the motive `fun z => motive x z`. `Nat.add._f`'s second alternative reads the
recursive call as the first projection `x.1` of the table `x : Nat.below (fun y => Nat → Nat)
(Nat.succ b)`, typed through the unfolding of the table to `PProd (Nat → Nat)
(Nat.below (fun y => Nat → Nat) b)` (`belowS_defeq_motNL`), and applies it to the first argument.
For `Test/NVAModel.lean`.
-/

open Lean Metalean

namespace EraseProof.Test.NVA

open EraseProof.Test.NV1 (typed_of_eq var_of_get app_typed const_typed fin0_eq lu)
open EraseProof.Test.NVS (puSig ppSig puBlock ppBlock mPU mPUu mPP mPPmk ppLevel ppStruct
  ppParams mPP_defeq mPP_typed mPPmk_typed mPU_typed mPUu_typed app_typed' one imax_m1_one)
open EraseProof.Test.NVL (nSig nBlock mN mZ mS mN_typed mZ_typed mS_typed indN_typed recAllowedN
  appMotN_typed motN_typed)

section Defs
variable {ζ : Sigs} (ηPP : Head ζ (.inductive ppSig)) (ηN : Head ζ (.inductive nSig))
  (ηC ηBl ηBr ηM : Head ζ (.const .def 1)) (ηF : Head ζ (.const .def 0))

/-- `Nat → Nat → Sort u_1` -/
def motMM {n : Nat} : Expr ζ 1 n := .forallE (mN ηN) (.forallE (mN ηN) (.sort lu))

/-- `(a : Nat) → motive a Nat.zero`, under `motive x y`. -/
def H1M : Expr ζ 1 3 := .forallE (mN ηN) (.app (.app #0 #3) (mZ ηN))

/-- `(a b : Nat) → motive a (Nat.succ b)`, under `motive x y h_1`. -/
def H2M : Expr ζ 1 4 := .forallE (mN ηN) (.forallE (mN ηN) (.app (.app #0 #4) (mS ηN #5)))

/-- `Nat.add.match_1`'s type `(motive : Nat → Nat → Sort u_1) → (x y : Nat) →
((a : Nat) → motive a Nat.zero) → ((a b : Nat) → motive a (Nat.succ b)) → motive x y`. -/
def matchTyM : Expr ζ 1 0 :=
  .forallE (motMM ηN) (.forallE (mN ηN) (.forallE (mN ηN) (.forallE (H1M ηN)
    (.forallE (H2M ηN) (.app (.app #0 #1) #2)))))

/-- `fun motive x y h_1 h_2 => Nat.casesOn (fun z => motive x z) y (h_1 x) (fun n => h_2 x n)` -/
def matchValM : Expr ζ 1 0 :=
  .lam (motMM ηN) (.lam (mN ηN) (.lam (mN ηN) (.lam (H1M ηN) (.lam (H2M ηN)
    (.app (.app (.app (.app (.const ηC ![lu]) (.lam (mN ηN) (.app (.app #0 #1) #5))) #2)
      (.app #3 #1)) (.lam (mN ηN) (.app (.app #4 #1) #5)))))))

/-- `Nat → Nat` -/
def nnM {ℓ n : Nat} : Expr ζ ℓ n := .forallE (mN ηN) (mN ηN)

/-- `(y : Nat) → Nat.below (fun y => Nat → Nat) y → Nat → Nat` -/
def fTyM : Expr ζ 0 0 :=
  .forallE (mN ηN) (.forallE (belowM ηBl one (motNL ηN) #0) (nnM ηN))

/-- The motive `fun x y => Nat.below (fun y => Nat → Nat) y → Nat` of `Nat.add._f`'s match, under
`y f x`. -/
def motFM : Expr ζ 0 3 :=
  .lam (mN ηN) (.lam (mN ηN) (.forallE (belowM ηBl one (motNL ηN) #4) (mN ηN)))

/-- `x.1` for `x : Nat.below (fun y => Nat → Nat) (Nat.succ b)` under `y f x a b x`, as Metalean's
structure projection computes it at the parameters `(fun y => Nat → Nat) b` and
`Nat.below (fun y => Nat → Nat) b`. -/
def projFstA : Expr ζ 0 6 :=
  .recr ηPP 0 ![one, m1 one] one ![.app (motNL ηN) #4, belowM ηBl one (motNL ηN) #4]
    (fun _ => .lam (mPP ηPP one (m1 one) (.app (motNL ηN) #4) (belowM ηBl one (motNL ηN) #4))
      (.app (motNL ηN) #4))
    (fun _ _ => .lam (.app (motNL ηN) #4) (.lam (belowM ηBl one (motNL ηN) #4) #6)) Fin.elim0 #5

/-- The alternatives `fun a x => a` and `fun a b x => Nat.succ (x.1 a)` of `Nat.add._f`'s match,
under `y f x`. -/
def h1FM : Expr ζ 0 3 := .lam (mN ηN) (.lam (belowM ηBl one (motNL ηN) (mZ ηN)) #3)
def h2FM : Expr ζ 0 3 :=
  .lam (mN ηN) (.lam (mN ηN) (.lam (belowM ηBl one (motNL ηN) (mS ηN #4))
    (mS ηN (.app (projFstA ηPP ηN ηBl) #3))))

/-- `fun y f x => Nat.add.match_1 motF x y h1F h2F f` -/
def fValM : Expr ζ 0 0 :=
  .lam (mN ηN) (.lam (belowM ηBl one (motNL ηN) #0) (.lam (mN ηN)
    (.app (.app (.app (.app (.app (.app (.const ηM ![one]) (motFM ηN ηBl)) #2) #0)
      (h1FM ηN ηBl)) (h2FM ηPP ηN ηBl)) #1)))

/-- `(x y : Nat) → Nat` -/
def addTyM : Expr ζ 0 0 := .forallE (mN ηN) (.forallE (mN ηN) (mN ηN))

/-- `fun x y => Nat.brecOn (fun y => Nat → Nat) y Nat.add._f x` -/
def addValM : Expr ζ 0 0 :=
  .lam (mN ηN) (.lam (mN ηN) (.app (.app (.app (.app (.const ηBr ![one]) (motNL ηN)) #1)
    (.const ηF Fin.elim0)) #0))

end Defs

section Typed
variable {ζ : Sigs} {E : Env ζ} {ηPU : Head ζ (.inductive puSig)} {ηPP : Head ζ (.inductive ppSig)}
  {ηN : Head ζ (.inductive nSig)} {ηC ηBl ηBr ηM : Head ζ (.const .def 1)} {ηF : Head ζ (.const .def 0)}
  (hE : EnvWF E) (hn : (E.get ηN).block = nBlock) (hpp : (E.get ηPP).block = ppBlock)

include hn in
theorem motMM_typed {n : Nat} {Γ : Ctx ζ 1 0 n} :
    E[Γ] ⊢ motMM ηN : .sort (.imax (.succ .zero) (.imax (.succ .zero) (.succ lu))) :=
  .forallEDF (mN_typed hn) (.forallEDF (mN_typed hn) .sortDF .sortDF)
    (.forallEDF (mN_typed hn) .sortDF .sortDF)

omit hn in
/-- A motive `f : Nat → Nat → Sort u_1` applied to two numbers. -/
theorem appMot2_typed {n : Nat} {Γ : Ctx ζ 1 0 n} {f a b : Expr ζ 1 n}
    (hf : E[Γ] ⊢ f : motMM ηN) (ha : E[Γ] ⊢ a : mN ηN) (hb : E[Γ] ⊢ b : mN ηN) :
    E[Γ] ⊢ .app (.app f a) b : .sort lu := by
  have h1 := typed_of_eq (app_typed hf ha) (T' := .forallE (mN ηN) (.sort lu)) (by arsx [motMM])
  exact typed_of_eq (app_typed h1 hb) (by arsx)

/-- `Nat.add.match_1`'s binder context `motive x y h_1 h_2`. -/
def ΓM (ηN : Head ζ (.inductive nSig)) : Ctx ζ 1 0 5 :=
  #t[motMM ηN, mN ηN, mN ηN, H1M ηN, H2M ηN]

include hE hn in
theorem matchValM_typed (hct : (E.get ηC).constType = casesOnTyM ηN) :
    E[.nil] ⊢ matchValM ηN ηC : matchTyM ηN := by
  have h1 : E[(#t[motMM ηN] : Ctx ζ 1 0 1)] ⊢ ok := .snoc .nil ⟨_, motMM_typed hn⟩
  have h2 : E[(#t[motMM ηN, mN ηN] : Ctx ζ 1 0 2)] ⊢ ok := .snoc h1 ⟨_, mN_typed hn⟩
  have h3 : E[(#t[motMM ηN, mN ηN, mN ηN] : Ctx ζ 1 0 3)] ⊢ ok := .snoc h2 ⟨_, mN_typed hn⟩
  have h3a : E[(#t[motMM ηN, mN ηN, mN ηN, mN ηN] : Ctx ζ 1 0 4)] ⊢ ok := .snoc h3 ⟨_, mN_typed hn⟩
  have hz3 := appMot2_typed (var_of_get (T := motMM ηN) h3a ⟨0, by decide⟩ (by arsx [motMM]))
    (var_of_get h3a ⟨3, by decide⟩ (by arsx)) (mZ_typed hn)
  have hH1 : E[(#t[motMM ηN, mN ηN, mN ηN] : Ctx ζ 1 0 3)] ⊢ H1M ηN : _ :=
    .forallEDF (mN_typed hn) hz3 hz3
  have h4 : E[(#t[motMM ηN, mN ηN, mN ηN, H1M ηN] : Ctx ζ 1 0 4)] ⊢ ok := .snoc h3 ⟨_, hH1⟩
  have h4a : E[(#t[motMM ηN, mN ηN, mN ηN, H1M ηN, mN ηN] : Ctx ζ 1 0 5)] ⊢ ok :=
    .snoc h4 ⟨_, mN_typed hn⟩
  have h4b : E[(#t[motMM ηN, mN ηN, mN ηN, H1M ηN, mN ηN, mN ηN] : Ctx ζ 1 0 6)] ⊢ ok :=
    .snoc h4a ⟨_, mN_typed hn⟩
  have hs4 := appMot2_typed (var_of_get (T := motMM ηN) h4b ⟨0, by decide⟩ (by arsx [motMM]))
    (var_of_get h4b ⟨4, by decide⟩ (by arsx)) (mS_typed hn (var_of_get h4b ⟨5, by decide⟩ (by arsx)))
  have hH2 : E[(#t[motMM ηN, mN ηN, mN ηN, H1M ηN] : Ctx ζ 1 0 4)] ⊢ H2M ηN : _ :=
    .forallEDF (mN_typed hn) (.forallEDF (mN_typed hn) hs4 hs4) (.forallEDF (mN_typed hn) hs4 hs4)
  have hΓ : E[ΓM ηN] ⊢ ok := .snoc h4 ⟨_, hH2⟩
  have hm : E[ΓM ηN] ⊢ #0 : motMM ηN := var_of_get hΓ ⟨0, by decide⟩ (by arsx [ΓM, motMM])
  have hx : E[ΓM ηN] ⊢ #1 : mN ηN := var_of_get hΓ ⟨1, by decide⟩ (by arsx [ΓM])
  have hy : E[ΓM ηN] ⊢ #2 : mN ηN := var_of_get hΓ ⟨2, by decide⟩ (by arsx [ΓM])
  have hh1 : E[ΓM ηN] ⊢ #3 : .forallE (mN ηN) (.app (.app #0 #5) (mZ ηN)) :=
    var_of_get hΓ ⟨3, by decide⟩ (by arsx [ΓM, H1M])
  have hh2 : E[ΓM ηN] ⊢ #4 : .forallE (mN ηN) (.forallE (mN ηN) (.app (.app #0 #5) (mS ηN #6))) :=
    var_of_get hΓ ⟨4, by decide⟩ (by arsx [ΓM, H2M])
  -- the motive `fun z => motive x z`
  have h5 : E[(ΓM ηN).snoc (mN ηN)] ⊢ ok := .snoc hΓ ⟨_, mN_typed hn⟩
  have hb5 := appMot2_typed (var_of_get (T := motMM ηN) h5 ⟨0, by decide⟩ (by arsx [ΓM, motMM]))
    (var_of_get h5 ⟨1, by decide⟩ (by arsx [ΓM])) (var_of_get h5 ⟨5, by decide⟩ (by arsx))
  have hmot : E[ΓM ηN] ⊢ .lam (mN ηN) (.app (.app #0 #1) #5) : motNM ηN lu :=
    .lamDF (mN_typed hn) .sortDF .sortDF hb5 hb5
  have hβ : ∀ {k : Nat} {Γ : Ctx ζ 1 0 (k + 5)} {a : Expr ζ 1 (k + 5)}, E[Γ] ⊢ ok →
      E[Γ] ⊢ .var ⟨0, by omega⟩ : motMM ηN → E[Γ] ⊢ .var ⟨1, by omega⟩ : mN ηN →
      E[Γ] ⊢ a : mN ηN →
      E[Γ] ⊢ .app (.lam (mN ηN) (.app (.app (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩))
          (.var (Fin.last (k + 5))))) a ≡
        .app (.app (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩)) a : .sort lu := by
    intro k Γ a hΓk hmk hxk ha
    have hΓk' : E[Γ.snoc (mN ηN)] ⊢ ok := .snoc hΓk ⟨_, mN_typed hn⟩
    have hmk' : E[Γ.snoc (mN ηN)] ⊢ .var ⟨0, by omega⟩ : motMM ηN :=
      defeq_rw (hmk.wk (mN ηN)) (by arsx) (by arsx) (by arsx [motMM])
    have hxk' : E[Γ.snoc (mN ηN)] ⊢ .var ⟨1, by omega⟩ : mN ηN :=
      defeq_rw (hxk.wk (mN ηN)) (by arsx) (by arsx) (by arsx)
    have hl : E[Γ.snoc (mN ηN)] ⊢ .var (Fin.last (k + 5)) : mN ηN :=
      var_of_get hΓk' _ (by rw [Ctx.get_last]; arsx)
    exact defeq_rw (beta_defeq (mN_typed hn) .sortDF (appMot2_typed hmk' hxk' hl) ha) rfl
      (by arsx) (by arsx)
  -- `Nat.casesOn (fun z => motive x z) y`
  have h0 : E[ΓM ηN] ⊢ .const ηC ![lu] : (E.get ηC).constType{![lu]}.wkClosed :=
    const_typed hE ηC ![lu] rfl
  rw [hct] at h0
  arsx [casesOnTyM] at h0
  have hc1 := app_typed' h0 hmot (by arsx)
  arsx at hc1
  have hc2 := app_typed' hc1 hy (by arsx)
  arsx at hc2
  -- `h_1 x`
  have hz := typed_of_eq (app_typed hh1 hx) (T' := .app (.app #0 #1) (mZ ηN)) (by arsx)
  have hz' := Defeq.defeqDF (hβ (k := 0) hΓ hm hx (mZ_typed hn)).symm hz
  have hc3 := app_typed' hc2 hz' (by arsx)
  arsx at hc3
  -- `fun n => h_2 x n`
  have hh2' : E[(ΓM ηN).snoc (mN ηN)] ⊢ #4 :
      .forallE (mN ηN) (.forallE (mN ηN) (.app (.app #0 #6) (mS ηN #7))) :=
    defeq_rw (hh2.wk (mN ηN)) (by arsx) (by arsx) (by arsx)
  have hx5 : E[(ΓM ηN).snoc (mN ηN)] ⊢ #1 : mN ηN := var_of_get h5 ⟨1, by decide⟩ (by arsx [ΓM])
  have hv5 : E[(ΓM ηN).snoc (mN ηN)] ⊢ #5 : mN ηN := var_of_get h5 ⟨5, by decide⟩ (by arsx)
  have hm5 : E[(ΓM ηN).snoc (mN ηN)] ⊢ #0 : motMM ηN :=
    var_of_get h5 ⟨0, by decide⟩ (by arsx [ΓM, motMM])
  have hb5' := typed_of_eq (app_typed (typed_of_eq (app_typed hh2' hx5)
      (T' := .forallE (mN ηN) (.app (.app #0 #1) (mS ηN #6))) (by arsx)) hv5)
    (T' := .app (.app #0 #1) (mS ηN #5)) (by arsx)
  have hβ5 := hβ (k := 1) h5 hm5 hx5 (mS_typed hn hv5)
  have hs : E[ΓM ηN] ⊢ .lam (mN ηN) (.app (.app #4 #1) #5) :
      .forallE (mN ηN) (.app (.lam (mN ηN) (.app (.app #0 #1) #6)) (mS ηN #5)) :=
    .lamDF (mN_typed hn) hβ5.left hβ5.left (.defeqDF hβ5.symm hb5') (.defeqDF hβ5.symm hb5')
  have hc4 := app_typed' hc3 hs (by arsx)
  arsx at hc4
  have hbody := Defeq.defeqDF (hβ (k := 0) hΓ hm hx hy) (typed_of_eq hc4 (by arsx))
  exact Ctx.lam_congr (Γ := .nil) (Δ := ΓM ηN) hΓ hbody

/-! ### `Nat.add._f`, `Nat.add` -/

theorem imax_one_one {ℓ : Nat} : (Level.imax one one : Level ℓ) = one :=
  Level.ext fun ν => by simp [Nat.imax]

include hn in
theorem nnM_typed {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} : E[Γ] ⊢ nnM ηN : .sort one := by
  have h := Defeq.forallEDF (mN_typed hn (Γ := Γ)) (mN_typed hn) (mN_typed hn)
  rwa [imax_one_one] at h

include hn in
theorem motNL_typed {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} : E[Γ] ⊢ motNL ηN : motNM ηN one :=
  .lamDF (mN_typed hn) .sortDF .sortDF (nnM_typed hn) (nnM_typed hn)

include hn in
/-- `(fun y => Nat → Nat) a ≡ Nat → Nat`. -/
theorem motNL_beta {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} {a : Expr ζ ℓ n} (ha : E[Γ] ⊢ a : mN ηN) :
    E[Γ] ⊢ .app (motNL ηN) a ≡ nnM ηN : .sort one :=
  defeq_rw (beta_defeq (mN_typed hn) .sortDF (nnM_typed hn) ha) rfl (by arsx [nnM]) (by arsx)

theorem projTerm_eqFstA {I : Inductive ζ ppSig} (h : I.IsStructure 0 0) (hI : I = ppBlock) :
    h.projTerm ηPP ![one, m1 one] ![.app (motNL ηN) #4, belowM ηBl one (motNL ηN) #4]
      ⟨0, by decide⟩ (#5 : Expr ζ 0 6) = projFstA ηPP ηN ηBl := by
  subst hI
  rw [Inductive.IsStructure.projTerm_eq_recr]
  simp only [projFstA]
  congr 1
  case e_ms =>
    funext t; fin_cases t
    delta Inductive.IsStructure.projectionMotives
    arsx [Inductive.IsStructure.projTypeWith, Inductive.motiveTele, Inductive.indexTele, Ctx.substN]
  case e_mins =>
    funext t c; fin_cases t; fin_cases c
    delta Inductive.IsStructure.projectionCases
    arsx [Inductive.caseTele, CtorSig.caseOrdinary,
      CtorSig.fieldOrdinary, Ctor.fieldTele, Ctor.ordinaryFieldTele, Ctor.ordinaryTeleAux,
      Ctor.ihTele, Ctx.ofTypes, Ctor.recursiveFieldTeleAux, Expr.boundVars,
      Ctor.ordinaryFieldTeleAux, Tele.foldr, Ctx.substN, Subst.liftN]

theorem projType_eqFstA {I : Inductive ζ ppSig} (h : I.IsStructure 0 0) (hI : I = ppBlock) :
    h.projType ηPP ![one, m1 one] ![.app (motNL ηN) #4, belowM ηBl one (motNL ηN) #4]
      ⟨0, by decide⟩ (#5 : Expr ζ 0 6) = .app (motNL ηN) #4 := by
  subst hI
  rw [Inductive.IsStructure.projType, Inductive.IsStructure.projection]
  simp only [Inductive.IsStructure.projTypeWith]
  arsx

/-- `Nat.add._f`'s binder context `y f x`. -/
def ΓF (ηN : Head ζ (.inductive nSig)) (ηBl : Head ζ (.const .def 1)) : Ctx ζ 0 0 3 :=
  #t[mN ηN, belowM ηBl one (motNL ηN) #0, mN ηN]

/-- The match's motive `fun x y => Nat.below (fun y => Nat → Nat) y → Nat` at depth `n`. -/
def motFd (ηN : Head ζ (.inductive nSig)) (ηBl : Head ζ (.const .def 1)) (n : Nat) :
    Expr ζ 0 n :=
  .lam (mN ηN) (.lam (mN ηN) (.forallE (belowM ηBl one (motNL ηN) (.var (Fin.last (n + 1))))
    (mN ηN)))

include hE hn hpp in
theorem fValM_typed (ht : (E.get ηBl).constType = belowTyM ηN)
    (hv : (E.get ηBl).defValue = belowValM ηPU ηPP ηN)
    (hmt : (E.get ηM).constType = matchTyM ηN) :
    E[.nil] ⊢ fValM ηPP ηN ηBl ηM : fTyM ηN ηBl := by
  have hb : ∀ {n : Nat} {Γ : Ctx ζ 0 0 n} {a : Expr ζ 0 n}, E[Γ] ⊢ a : mN ηN →
      E[Γ] ⊢ belowM ηBl one (motNL ηN) a : .sort (m1 one) := fun ha =>
    belowM_typed hE ht (motNL_typed hn) ha
  -- the motive at any depth
  have hpiF : ∀ {n : Nat} {Γ : Ctx ζ 0 0 n} {a : Expr ζ 0 n}, E[Γ] ⊢ a : mN ηN →
      E[Γ] ⊢ .forallE (belowM ηBl one (motNL ηN) a) (mN ηN) : .sort one := by
    intro n Γ a ha
    have h := Defeq.forallEDF (hb ha) (mN_typed hn (Γ := Γ.snoc (belowM ηBl one (motNL ηN) a)))
      (mN_typed hn)
    rwa [imax_m1_one] at h
  have hmotF : ∀ {n : Nat} {Γ : Ctx ζ 0 0 n}, E[Γ] ⊢ ok →
      E[Γ] ⊢ motFd ηN ηBl n : .forallE (mN ηN) (.forallE (mN ηN) (.sort one)) := by
    intro n Γ hΓn
    have hΓ1 : E[Γ.snoc (mN ηN)] ⊢ ok := .snoc hΓn ⟨_, mN_typed hn⟩
    have hΓ2 : E[(Γ.snoc (mN ηN)).snoc (mN ηN)] ⊢ ok := .snoc hΓ1 ⟨_, mN_typed hn⟩
    have hl : E[(Γ.snoc (mN ηN)).snoc (mN ηN)] ⊢ .var (Fin.last (n + 1)) : mN ηN :=
      var_of_get hΓ2 _ (by rw [Ctx.get_last]; arsx)
    have hp := hpiF hl
    have hin : E[Γ.snoc (mN ηN)] ⊢ .lam (mN ηN) (.forallE (belowM ηBl one (motNL ηN)
        (.var (Fin.last (n + 1)))) (mN ηN)) : .forallE (mN ηN) (.sort one) :=
      .lamDF (mN_typed hn) .sortDF .sortDF hp hp
    exact .lamDF (mN_typed hn) (.forallEDF (mN_typed hn) .sortDF .sortDF)
      (.forallEDF (mN_typed hn) .sortDF .sortDF) hin hin
  -- the motive applied, by two β
  have hβF : ∀ {n : Nat} {Γ : Ctx ζ 0 0 n} {a b : Expr ζ 0 n}, E[Γ] ⊢ ok → E[Γ] ⊢ a : mN ηN →
      E[Γ] ⊢ b : mN ηN →
      E[Γ] ⊢ .app (.app (motFd ηN ηBl n) a) b ≡ .forallE (belowM ηBl one (motNL ηN) b) (mN ηN) :
        .sort one := by
    intro n Γ a b hΓn ha hb'
    have hty := typed_of_eq (app_typed (typed_of_eq (app_typed (hmotF hΓn) ha)
      (T' := .forallE (mN ηN) (.sort one)) (by arsx)) hb') (T' := .sort one) (by arsx)
    have h1 : E ⊢ .app (.app (motFd ηN ηBl n) a) b ⤳* .app ((Expr.lam (mN ηN)
        (.forallE (belowM ηBl one (motNL ηN) (.var (Fin.last (n + 1)))) (mN ηN))).inst a) b :=
      .single (.frame (K := .app _) .beta)
    have h2 := whredS_step h1 .beta
    arsx at h2
    exact defeq_rw (WHRedS.defeq hE hΓn h2 hty) rfl (by arsx) rfl
  -- the context `y f x`
  have h1 : E[(#t[mN ηN] : Ctx ζ 0 0 1)] ⊢ ok := .snoc .nil ⟨_, mN_typed hn⟩
  have h2 : E[(#t[mN ηN, belowM ηBl one (motNL ηN) #0] : Ctx ζ 0 0 2)] ⊢ ok :=
    .snoc h1 ⟨_, hb (var_of_get h1 ⟨0, by decide⟩ (by arsx))⟩
  have hΓ : E[ΓF ηN ηBl] ⊢ ok := .snoc h2 ⟨_, mN_typed hn⟩
  have hy : E[ΓF ηN ηBl] ⊢ #0 : mN ηN := var_of_get hΓ ⟨0, by decide⟩ (by arsx [ΓF])
  have hf : E[ΓF ηN ηBl] ⊢ #1 : belowM ηBl one (motNL ηN) #0 :=
    var_of_get hΓ ⟨1, by decide⟩ (by arsx [ΓF])
  have hx : E[ΓF ηN ηBl] ⊢ #2 : mN ηN := var_of_get hΓ ⟨2, by decide⟩ (by arsx [ΓF])
  -- `Nat.add.match_1 motF x y`
  have h0 : E[ΓF ηN ηBl] ⊢ .const ηM ![one] : (E.get ηM).constType{![one]}.wkClosed :=
    const_typed hE ηM ![one] rfl
  rw [hmt] at h0
  arsx [matchTyM, motMM, H1M, H2M] at h0
  have hc1 := app_typed' h0 (hmotF (n := 3) hΓ) (by arsx [motFd])
  arsx at hc1
  have hc2 := app_typed' hc1 hx (by arsx)
  arsx at hc2
  have hc3 := app_typed' hc2 hy (by arsx)
  arsx at hc3
  -- `fun a x => a`
  have h4 : E[(ΓF ηN ηBl).snoc (mN ηN)] ⊢ ok := .snoc hΓ ⟨_, mN_typed hn⟩
  have hbz := hb (Γ := (ΓF ηN ηBl).snoc (mN ηN)) (mZ_typed hn)
  have h5z : E[((ΓF ηN ηBl).snoc (mN ηN)).snoc (belowM ηBl one (motNL ηN) (mZ ηN))] ⊢ ok :=
    .snoc h4 ⟨_, hbz⟩
  have ha5 : E[((ΓF ηN ηBl).snoc (mN ηN)).snoc (belowM ηBl one (motNL ηN) (mZ ηN))] ⊢ #3 :
      mN ηN := var_of_get h5z ⟨3, by decide⟩ (by arsx)
  have hβz := hβF (n := 4) h4 (var_of_get h4 ⟨3, by decide⟩ (by arsx)) (mZ_typed hn)
  have hH1in : E[(ΓF ηN ηBl).snoc (mN ηN)] ⊢ .lam (belowM ηBl one (motNL ηN) (mZ ηN)) #3 :
      .app (.app (motFd ηN ηBl 4) #3) (mZ ηN) :=
    .defeqDF hβz.symm (.lamDF hbz (mN_typed hn) (mN_typed hn) ha5 ha5)
  have hH1 : E[ΓF ηN ηBl] ⊢ h1FM ηN ηBl :
      .forallE (mN ηN) (.app (.app (motFd ηN ηBl 4) #3) (mZ ηN)) :=
    .lamDF (mN_typed hn) hβz.left hβz.left hH1in hH1in
  have hc4 := app_typed' hc3 hH1 (by arsx [motFd])
  arsx at hc4
  -- `fun a b x => Nat.succ (x.1 a)`
  have h5 : E[((ΓF ηN ηBl).snoc (mN ηN)).snoc (mN ηN)] ⊢ ok := .snoc h4 ⟨_, mN_typed hn⟩
  have hb4 : E[((ΓF ηN ηBl).snoc (mN ηN)).snoc (mN ηN)] ⊢ #4 : mN ηN :=
    var_of_get h5 ⟨4, by decide⟩ (by arsx)
  have hbs := hb (mS_typed hn hb4)
  have h6 : E[(((ΓF ηN ηBl).snoc (mN ηN)).snoc (mN ηN)).snoc
      (belowM ηBl one (motNL ηN) (mS ηN #4))] ⊢ ok := .snoc h5 ⟨_, hbs⟩
  have hb6 : E[(((ΓF ηN ηBl).snoc (mN ηN)).snoc (mN ηN)).snoc
      (belowM ηBl one (motNL ηN) (mS ηN #4))] ⊢ #4 : mN ηN := var_of_get h6 ⟨4, by decide⟩ (by arsx)
  have ha6 : E[(((ΓF ηN ηBl).snoc (mN ηN)).snoc (mN ηN)).snoc
      (belowM ηBl one (motNL ηN) (mS ηN #4))] ⊢ #3 : mN ηN := var_of_get h6 ⟨3, by decide⟩ (by arsx)
  have hx6 : E[(((ΓF ηN ηBl).snoc (mN ηN)).snoc (mN ηN)).snoc
      (belowM ηBl one (motNL ηN) (mS ηN #4))] ⊢ #5 : belowM ηBl one (motNL ηN) (mS ηN #4) :=
    var_of_get h6 ⟨5, by decide⟩ (by arsx)
  have hS := belowS_defeq_motNL hE hn hpp ht hv h6 (motNL_typed hn) hb6
  have hst : (E.get ηPP).block.IsStructure 0 0 := hpp ▸ ppStruct
  have hB : InductiveWF E (E.get ηPP).block := (hE.entryWF ηPP).block
  have hps := ppParams hpp (appMotN_typed hn (motNL_typed hn) hb6) (hb hb6)
  have hmaj : E[(((ΓF ηN ηBl).snoc (mN ηN)).snoc (mN ηN)).snoc
      (belowM ηBl one (motNL ηN) (mS ηN #4))] ⊢ #5 :
      .ind ηPP 0 ![one, m1 one] ![.app (motNL ηN) #4, belowM ηBl one (motNL ηN) #4]
        hst.indices := by
    rw [← hst.indices_eq Fin.elim0]
    exact .defeqDF hS hx6
  have hp := hst.projTerm_hasType hB ⟨0, by decide⟩ h6 hps hmaj
  rw [projTerm_eqFstA hst hpp, projType_eqFstA hst hpp] at hp
  have hpa := typed_of_eq (app_typed (.defeqDF (motNL_beta hn hb6) hp) ha6) (T' := mN ηN)
    (by arsx [nnM])
  have hsx := mS_typed hn hpa
  have hβs := hβF (n := 5) h5 (var_of_get h5 ⟨3, by decide⟩ (by arsx)) (mS_typed hn hb4)
  have hH2in : E[((ΓF ηN ηBl).snoc (mN ηN)).snoc (mN ηN)] ⊢
      .lam (belowM ηBl one (motNL ηN) (mS ηN #4)) (mS ηN (.app (projFstA ηPP ηN ηBl) #3)) :
      .app (.app (motFd ηN ηBl 5) #3) (mS ηN #4) :=
    .defeqDF hβs.symm (.lamDF hbs (mN_typed hn) (mN_typed hn) hsx hsx)
  have hH2b : E[(ΓF ηN ηBl).snoc (mN ηN)] ⊢ .lam (mN ηN)
      (.lam (belowM ηBl one (motNL ηN) (mS ηN #4)) (mS ηN (.app (projFstA ηPP ηN ηBl) #3))) :
      .forallE (mN ηN) (.app (.app (motFd ηN ηBl 5) #3) (mS ηN #4)) :=
    .lamDF (mN_typed hn) hβs.left hβs.left hH2in hH2in
  have hH2ty : E[(ΓF ηN ηBl).snoc (mN ηN)] ⊢
      .forallE (mN ηN) (.app (.app (motFd ηN ηBl 5) #3) (mS ηN #4)) : _ :=
    .forallEDF (mN_typed hn) hβs.left hβs.left
  have hH2 : E[ΓF ηN ηBl] ⊢ h2FM ηPP ηN ηBl :
      .forallE (mN ηN) (.forallE (mN ηN) (.app (.app (motFd ηN ηBl 5) #3) (mS ηN #4))) :=
    .lamDF (mN_typed hn) hH2ty hH2ty hH2b hH2b
  have hc5 := app_typed' hc4 hH2 (by arsx [motFd])
  arsx at hc5
  -- the match applied to the table `f`
  have hβm := hβF (n := 3) hΓ hx hy
  have hc5' := Defeq.defeqDF hβm (typed_of_eq hc5 (by arsx [motFd]))
  have hbody := typed_of_eq (app_typed hc5' hf) (T' := mN ηN) (by arsx)
  exact Ctx.lam_congr (Γ := .nil) (Δ := ΓF ηN ηBl) hΓ hbody

include hE hn in
theorem addValM_typed (hbt : (E.get ηBr).constType = brecOnTyM ηN ηBl)
    (hft : (E.get ηF).constType = fTyM ηN ηBl) (ht : (E.get ηBl).constType = belowTyM ηN) :
    E[.nil] ⊢ addValM ηN ηBr ηF : addTyM ηN := by
  have h1 : E[(#t[mN ηN] : Ctx ζ 0 0 1)] ⊢ ok := .snoc .nil ⟨_, mN_typed hn⟩
  have hΓ : E[(#t[mN ηN, mN ηN] : Ctx ζ 0 0 2)] ⊢ ok := .snoc h1 ⟨_, mN_typed hn⟩
  have hx : E[(#t[mN ηN, mN ηN] : Ctx ζ 0 0 2)] ⊢ #0 : mN ηN := var_of_get hΓ ⟨0, by decide⟩ (by arsx)
  have hy : E[(#t[mN ηN, mN ηN] : Ctx ζ 0 0 2)] ⊢ #1 : mN ηN := var_of_get hΓ ⟨1, by decide⟩ (by arsx)
  have h0 : E[(#t[mN ηN, mN ηN] : Ctx ζ 0 0 2)] ⊢ .const ηBr ![one] :
      (E.get ηBr).constType{![one]}.wkClosed := const_typed hE ηBr ![one] rfl
  rw [hbt] at h0
  arsx [brecOnTyM, F1TyM] at h0
  have hc1 := app_typed' h0 (motNL_typed hn) (by arsx)
  arsx at hc1
  have hc2 := app_typed' hc1 hy (by arsx)
  arsx at hc2
  have hf0 : E[(#t[mN ηN, mN ηN] : Ctx ζ 0 0 2)] ⊢ .const ηF Fin.elim0 :
      (E.get ηF).constType{(Fin.elim0 : Fin 0 → Level 0)}.wkClosed := const_typed hE ηF Fin.elim0 rfl
  rw [hft] at hf0
  arsx [fTyM, nnM] at hf0
  -- `Nat.add._f : (y : Nat) → Nat.below _ y → Nat → Nat` at `(t : Nat) → Nat.below _ t → (fun y => Nat → Nat) t`
  have h3 : E[(#t[mN ηN, mN ηN, mN ηN] : Ctx ζ 0 0 3)] ⊢ ok := .snoc hΓ ⟨_, mN_typed hn⟩
  have hv3 : E[(#t[mN ηN, mN ηN, mN ηN] : Ctx ζ 0 0 3)] ⊢ #2 : mN ηN :=
    var_of_get h3 ⟨2, by decide⟩ (by arsx)
  have hb3 := belowM_typed hE ht (motNL_typed hn) hv3
  have hTy : ∀ {A : Expr ζ 0 3}, E[(#t[mN ηN, mN ηN, mN ηN] : Ctx ζ 0 0 3)] ⊢ A : .sort (m1 one) →
      E[(#t[mN ηN, mN ηN, mN ηN] : Ctx ζ 0 0 3).snoc A] ⊢ .app (motNL ηN) #2 ≡ nnM ηN :
        .sort one := by
    intro A hA
    have h4 : E[(#t[mN ηN, mN ηN, mN ηN] : Ctx ζ 0 0 3).snoc A] ⊢ ok := .snoc h3 ⟨_, hA⟩
    exact motNL_beta hn (var_of_get h4 ⟨2, by decide⟩ (by arsx))
  have hin : E[(#t[mN ηN, mN ηN, mN ηN] : Ctx ζ 0 0 3)] ⊢
      .forallE (belowM ηBl one (motNL ηN) #2) (.app (motNL ηN) #2) ≡
      .forallE (belowM ηBl one (motNL ηN) #2) (nnM ηN) : .sort (.imax (m1 one) one) :=
    .forallEDF hb3 (hTy hb3) (hTy hb3)
  have hFt : E[(#t[mN ηN, mN ηN] : Ctx ζ 0 0 2)] ⊢
      .forallE (mN ηN) (.forallE (belowM ηBl one (motNL ηN) #2) (.app (motNL ηN) #2)) ≡
      .forallE (mN ηN) (.forallE (belowM ηBl one (motNL ηN) #2) (nnM ηN)) : _ :=
    .forallEDF (mN_typed hn) hin hin
  have hF := Defeq.defeqDF hFt.symm (typed_of_eq hf0 (by arsx [nnM]))
  have hc3 := app_typed' hc2 hF (by arsx)
  arsx at hc3
  have hc3' := Defeq.defeqDF (motNL_beta hn hy) (typed_of_eq hc3 (by arsx))
  have hbody := typed_of_eq (app_typed hc3' hx) (T' := mN ηN) (by arsx [nnM])
  exact Ctx.lam_congr (Γ := .nil) (Δ := #t[mN ηN, mN ηN]) hΓ hbody

end Typed


end EraseProof.Test.NVA
