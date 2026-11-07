import EraseProof.Test.NVQData
import EraseProof.Test.NVPModel

/-!
# NV-Q: the Metalean model of the program

The premises of the final theorem about the program and its model, for NV-Q (`Test/NVQData.lean`):
the program `P` is the Lean form of the well-formed Metalean environment `EH` with name table `BH`
(`henv`, `hwf`), and the erased term `e` is the Lean form of the closed Metalean term `tE`, which is
typed (`he`, `hty`). `EH` extends NV-P's environment `EB` by the quotient entry (over `Eq`'s head)
and the axioms `R` and `hR`. The quotient constants' η-terms (`Metalean.Frontend.quotTerm`) are
typed at the translations of their Lean types in any environment whose quotient entry is over a
head holding `Eq.block` (`quotTyTerm_typed`).
-/

open Lean Metalean

namespace EraseProof.Test.NVQ

open EraseProof.Test.NV1 (tB cT mB mT bSig bBlock indB_typed ctorB_typed typed_of_eq var_of_get
  app_typed const_typed tr_B tr_T notSpecial_bvar notSpecial_const trLevels_nil)
open EraseProof.Test.NVP (ζB ηEB ηBB ηCB EB BB hqB hbB wfB BB_Eq BB_B BB_t eqA eqA_typed l1M
  trLevel_l1 tr_eqC trLevels_one trLevels_two imax_one typed_of_eq' mB_typed mT_typed BB_typed idM l1)

/-! ## The quotient constants' η-terms -/

section Generic
variable {ζ : Sigs} {E : Env ζ} {η : Head ζ .quot} {ηE : Head ζ (.inductive Eq.sig)}

abbrev pu : Level 1 := .param 0
abbrev qu : Level 2 := .param 0
abbrev qv : Level 2 := .param 1

/-- The binders of `Quot`'s η-term: `{α : Sort u} (r : α → α → Prop)`. -/
def ΔT : Ctx ζ 1 0 2 := #t[.sort pu, Quot.relType #0]
/-- The binders of `Quot.mk`'s η-term: `{α : Sort u} (r : α → α → Prop) (a : α)`. -/
def ΔM : Ctx ζ 1 0 3 := #t[.sort pu, Quot.relType #0, #0]
/-- The binders of `Quot.lift`'s η-term. -/
def ΔL (η : Head ζ .quot) (ηE : Head ζ (.inductive Eq.sig)) : Ctx ζ 2 0 6 :=
  #t[.sort qu, Quot.relType #0, .sort qv, .forallE #0 #2, Quot.compatType ηE qv #0 #1 #2 #3,
    .quot η qu #0 #1]
/-- The binders of `Quot.ind`'s η-term. -/
def ΔI (η : Head ζ .quot) : Ctx ζ 1 0 5 :=
  #t[.sort pu, Quot.relType #0, Quot.motiveType η pu #0 #1, Quot.minorType η pu #0 #1 #2,
    .quot η pu #0 #1]

theorem ΔT_wf : E[(ΔT : Ctx ζ 1 0 2)] ⊢ ok := by
  have h1 : E[(#t[.sort pu] : Ctx ζ 1 0 1)] ⊢ ok := .snoc .nil ⟨_, .sortDF⟩
  exact .snoc h1 ⟨_, Quot.relType_congr (var_of_get h1 ⟨0, by decide⟩ (by eqsimp))⟩

theorem ΔM_wf : E[(ΔM : Ctx ζ 1 0 3)] ⊢ ok := by
  have h2 := ΔT_wf (E := E) (ζ := ζ)
  exact .snoc h2 ⟨pu, var_of_get h2 ⟨0, by decide⟩ (by eqsimp [ΔT])⟩

theorem quotT_typed :
    E[.nil] ⊢ (ΔT : Ctx ζ 1 0 2).lam (.quot η pu #0 #1) : (ΔT : Ctx ζ 1 0 2).pi (.sort pu) := by
  have hΓ := ΔT_wf (E := E) (ζ := ζ)
  exact Ctx.lam_congr (Γ := .nil) (Δ := ΔT) hΓ
    (.quotDF (var_of_get hΓ ⟨0, by decide⟩ (by eqsimp [ΔT]))
      (var_of_get hΓ ⟨1, by decide⟩ (by eqsimp [ΔT])))

theorem quotM_typed :
    E[.nil] ⊢ (ΔM : Ctx ζ 1 0 3).lam (.quotMk η pu #0 #1 #2) :
      (ΔM : Ctx ζ 1 0 3).pi (.quot η pu #0 #1) := by
  have hΓ := ΔM_wf (E := E) (ζ := ζ)
  exact Ctx.lam_congr (Γ := .nil) (Δ := ΔM) hΓ
    (.quotMkDF (var_of_get hΓ ⟨0, by decide⟩ (by eqsimp [ΔM]))
      (var_of_get hΓ ⟨1, by decide⟩ (by eqsimp [ΔM])) (var_of_get hΓ ⟨2, by decide⟩ (by eqsimp [ΔM])))

theorem ΔL_wf (hq : (E.get ηE).block = Eq.block) : E[ΔL η ηE] ⊢ ok := by
  have h1 : E[(#t[.sort qu] : Ctx ζ 2 0 1)] ⊢ ok := .snoc .nil ⟨_, .sortDF⟩
  have h2 : E[(#t[.sort qu, Quot.relType #0] : Ctx ζ 2 0 2)] ⊢ ok :=
    .snoc h1 ⟨_, Quot.relType_congr (var_of_get h1 ⟨0, by decide⟩ (by eqsimp))⟩
  have h3 : E[(#t[.sort qu, Quot.relType #0, .sort qv] : Ctx ζ 2 0 3)] ⊢ ok :=
    .snoc h2 ⟨_, .sortDF⟩
  have h3' : E[(#t[.sort qu, Quot.relType #0, .sort qv, #0] : Ctx ζ 2 0 4)] ⊢ ok :=
    .snoc h3 ⟨_, var_of_get h3 ⟨0, by decide⟩ (by eqsimp)⟩
  have hf3 : E[(#t[.sort qu, Quot.relType #0, .sort qv] : Ctx ζ 2 0 3)] ⊢
      .forallE #0 #2 : .sort (.imax qu qv) :=
    .forallEDF (var_of_get h3 ⟨0, by decide⟩ (by eqsimp)) (var_of_get h3' ⟨2, by decide⟩ (by eqsimp))
      (var_of_get h3' ⟨2, by decide⟩ (by eqsimp))
  have h4 : E[(#t[.sort qu, Quot.relType #0, .sort qv, .forallE #0 #2] : Ctx ζ 2 0 4)] ⊢ ok :=
    .snoc h3 ⟨_, hf3⟩
  have h5 : E[(#t[.sort qu, Quot.relType #0, .sort qv, .forallE #0 #2,
      Quot.compatType ηE qv #0 #1 #2 #3] : Ctx ζ 2 0 5)] ⊢ ok :=
    .snoc h4 (Quot.compatType_isType hq (var_of_get h4 ⟨0, by decide⟩ (by eqsimp))
      (var_of_get h4 ⟨1, by decide⟩ (by eqsimp)) (var_of_get h4 ⟨2, by decide⟩ (by eqsimp))
      (var_of_get h4 ⟨3, by decide⟩ (by eqsimp)))
  exact .snoc h5 ⟨_, .quotDF (var_of_get h5 ⟨0, by decide⟩ (by eqsimp))
    (var_of_get h5 ⟨1, by decide⟩ (by eqsimp))⟩

theorem quotL_typed (hq : (E.get (E.get η).eqHead).block = Eq.block) :
    E[.nil] ⊢ (ΔL η (E.get η).eqHead).lam (.quotLift η qu qv #0 #1 #2 #3 #4 #5) :
      (ΔL η (E.get η).eqHead).pi #2 := by
  have hΓ := ΔL_wf (η := η) hq
  exact Ctx.lam_congr (Γ := .nil) (Δ := ΔL η (E.get η).eqHead) hΓ
    (.quotLiftDF (var_of_get hΓ ⟨0, by decide⟩ (by eqsimp [ΔL]))
      (var_of_get hΓ ⟨1, by decide⟩ (by eqsimp [ΔL])) (var_of_get hΓ ⟨2, by decide⟩ (by eqsimp [ΔL]))
      (var_of_get hΓ ⟨3, by decide⟩ (by eqsimp [ΔL])) (var_of_get hΓ ⟨4, by decide⟩ (by eqsimp [ΔL]))
      (var_of_get hΓ ⟨5, by decide⟩ (by eqsimp [ΔL])))

theorem ΔI_wf : E[(ΔI η : Ctx ζ 1 0 5)] ⊢ ok := by
  have h2 := ΔT_wf (E := E) (ζ := ζ)
  have h3 : E[(#t[.sort pu, Quot.relType #0, Quot.motiveType η pu #0 #1] : Ctx ζ 1 0 3)] ⊢ ok :=
    .snoc h2 (Quot.motiveType_isType (var_of_get h2 ⟨0, by decide⟩ (by eqsimp [ΔT]))
      (var_of_get h2 ⟨1, by decide⟩ (by eqsimp [ΔT])))
  have h4 : E[(#t[.sort pu, Quot.relType #0, Quot.motiveType η pu #0 #1,
      Quot.minorType η pu #0 #1 #2] : Ctx ζ 1 0 4)] ⊢ ok :=
    .snoc h3 (Quot.minorType_isType (var_of_get h3 ⟨0, by decide⟩ (by eqsimp))
      (var_of_get h3 ⟨1, by decide⟩ (by eqsimp)) (var_of_get h3 ⟨2, by decide⟩ (by eqsimp)))
  exact .snoc h4 ⟨_, .quotDF (var_of_get h4 ⟨0, by decide⟩ (by eqsimp))
    (var_of_get h4 ⟨1, by decide⟩ (by eqsimp))⟩

theorem quotI_typed :
    E[.nil] ⊢ (ΔI η : Ctx ζ 1 0 5).lam (.quotInd η pu #0 #1 #2 #3 #4) :
      (ΔI η : Ctx ζ 1 0 5).pi (.app #2 #4) := by
  have hΓ := ΔI_wf (E := E) (η := η)
  have hβ : E[ΔI η] ⊢ #2 : Quot.motiveType η pu #0 #1 := var_of_get hΓ ⟨2, by decide⟩ (by eqsimp [ΔI])
  have ha : E[ΔI η] ⊢ #4 : .quot η pu #0 #1 := var_of_get hΓ ⟨4, by decide⟩ (by eqsimp [ΔI])
  exact Ctx.lam_congr (Γ := .nil) (Δ := ΔI η) hΓ
    (.quotIndDF (var_of_get hΓ ⟨0, by decide⟩ (by eqsimp [ΔI]))
      (var_of_get hΓ ⟨1, by decide⟩ (by eqsimp [ΔI])) hβ
      (var_of_get hΓ ⟨3, by decide⟩ (by eqsimp [ΔI])) ha (app_typed hβ ha))

end Generic

/-! ## The quotient entry over `EB` -/

abbrev ζQ : Sigs := ζB.snoc .quot
abbrev ηQ : Head ζQ .quot := .here
abbrev ηEQ : Head ζQ (.inductive Eq.sig) := .there ηEB
abbrev ηBQ : Head ζQ (.inductive bSig) := .there ηBB

/-- NV-P's environment with the quotient entry over `Eq`. -/
def EQ : Env ζQ := EB.snoc (.quot ηEB)

theorem hqQ : (EQ.get ηEQ).block = Eq.block := by simp! [EQ, EB, NVP.EA, Env.get, Entry.block]
theorem heqQ : (EQ.get ηQ).eqHead = ηEQ := by simp! [EQ, Env.get, Entry.eqHead]
theorem wfQ : EnvWF EQ := .snoc wfB (.quot hqB)

/-- The name table of `EQ`: the four quotient constants at the quotient entry. -/
def BQ : Binds ζQ :=
  ((((Binds.wk BB).set `Quot (.quot .here .type)).set `Quot.mk (.quot .here .ctor)).set
    `Quot.lift (.quot .here .lift)).set `Quot.ind (.quot .here .ind)

theorem BQ_Quot : BQ `Quot = some (.quot ηQ .type) := rfl
theorem BQ_mk : BQ `Quot.mk = some (.quot ηQ .ctor) := rfl
theorem BQ_lift : BQ `Quot.lift = some (.quot ηQ .lift) := rfl
theorem BQ_ind : BQ `Quot.ind = some (.quot ηQ .ind) := rfl
theorem BQ_Eq : BQ `Eq = some (.ind ηEQ 0) := rfl
theorem BQ_B : BQ `B = some (.ind ηBQ 0) := rfl

theorem trLevel_u : TrLevel [`u] (.param `u) = some pu := rfl
theorem trLevel_uv : TrLevel [`u, `v] (.param `u) = some qu := rfl
theorem trLevel_v : TrLevel [`u, `v] (.param `v) = some qv := rfl

/-- `@Quot.{u} α r` with `α`, `r` translated. -/
theorem tr_quotC {lps : List Name} {n : Nat} {Γ : Ctx ζQ lps.length 0 n} {Δ : MLCtx ζQ lps.length n}
    {u : Lean.Level} {l : Metalean.Level lps.length} {α r : Lean.Expr} {α' r' : Metalean.Expr ζQ lps.length n}
    (hl : TrLevel lps u = some l) (hα : TrM EQ BQ lps Γ Δ α α') (hr : TrM EQ BQ lps Γ Δ r r') :
    TrM EQ BQ lps Γ Δ (.app (.app (.const `Quot [u]) α) r) (.quot ηQ l α' r') :=
  TrM.special (c := `Quot) (us := [u]) (as := [α, r]) (as' := [α', r']) BQ_Quot rfl rfl
    (by
      intro i x x' h1 h2
      rcases i with _ | _ | i <;> simp at h1 h2 <;> subst h1 h2 <;> assumption)
    (SatTr.quotType (rest := []) (by simp [hl]))

theorem tr_QuotTy : TrM EQ BQ [`u] .nil [] Quot_val.type ((ΔT : Ctx ζQ 1 0 2).pi (.sort pu)) :=
  TrM.forallE (TrM.sort trLevel_u) (TrM.forallE (TrM.forallE (TrM.bvar rfl)
    (TrM.forallE (TrM.bvar rfl) (TrM.sort rfl))) (TrM.sort trLevel_u))

theorem tr_QuotC : TrM EQ BQ [`u] .nil [] (.const `Quot [.param `u])
    ((ΔT : Ctx ζQ 1 0 2).lam (.quot ηQ pu #0 #1)) :=
  TrM.special (as := []) (as' := []) BQ_Quot rfl rfl (fun _ _ _ h => nomatch h)
    (SatTr.quotEta (args := []) rfl (by decide) rfl)

theorem tr_MkTy : TrM EQ BQ [`u] .nil [] QuotMk_val.type
    ((ΔM : Ctx ζQ 1 0 3).pi (.quot ηQ pu #0 #1)) :=
  TrM.forallE (TrM.sort trLevel_u) (TrM.forallE (TrM.forallE (TrM.bvar rfl)
    (TrM.forallE (TrM.bvar rfl) (TrM.sort rfl))) (TrM.forallE (TrM.bvar rfl)
      (tr_quotC trLevel_u (TrM.bvar rfl) (TrM.bvar rfl))))

theorem tr_MkC : TrM EQ BQ [`u] .nil [] (.const `Quot.mk [.param `u])
    ((ΔM : Ctx ζQ 1 0 3).lam (.quotMk ηQ pu #0 #1 #2)) :=
  TrM.special (as := []) (as' := []) BQ_mk rfl rfl (fun _ _ _ h => nomatch h)
    (SatTr.quotEta (args := []) rfl (by decide) rfl)

theorem tr_LiftTy : TrM EQ BQ [`u, `v] .nil [] QuotLift_val.type ((ΔL ηQ ηEQ).pi #2) :=
  TrM.forallE (TrM.sort trLevel_uv) (TrM.forallE (TrM.forallE (TrM.bvar rfl)
    (TrM.forallE (TrM.bvar rfl) (TrM.sort rfl))) (TrM.forallE (TrM.sort trLevel_v)
      (TrM.forallE (TrM.forallE (TrM.bvar rfl) (TrM.bvar rfl))
        (TrM.forallE (TrM.forallE (TrM.bvar rfl) (TrM.forallE (TrM.bvar rfl)
          (TrM.forallE (TrM.app notSpecial_bvar (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl))
            (TrM.bvar rfl))
            (tr_eqC BQ_Eq trLevel_v (TrM.bvar rfl) (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl))
              (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl))))))
          (TrM.forallE (tr_quotC trLevel_uv (TrM.bvar rfl) (TrM.bvar rfl)) (TrM.bvar rfl))))))

theorem tr_LiftC : TrM EQ BQ [`u, `v] .nil [] (.const `Quot.lift [.param `u, .param `v])
    ((ΔL ηQ ηEQ).lam (.quotLift ηQ qu qv #0 #1 #2 #3 #4 #5)) :=
  TrM.special (as := []) (as' := []) BQ_lift rfl rfl (fun _ _ _ h => nomatch h)
    (SatTr.quotEta (args := []) rfl (by decide) rfl)

theorem tr_IndTy : TrM EQ BQ [`u] .nil [] QuotInd_val.type ((ΔI ηQ).pi (.app #2 #4)) :=
  TrM.forallE (TrM.sort trLevel_u) (TrM.forallE (TrM.forallE (TrM.bvar rfl)
    (TrM.forallE (TrM.bvar rfl) (TrM.sort rfl)))
    (TrM.forallE (TrM.forallE (tr_quotC trLevel_u (TrM.bvar rfl) (TrM.bvar rfl)) (TrM.sort rfl))
      (TrM.forallE (TrM.forallE (TrM.bvar rfl) (TrM.app notSpecial_bvar (TrM.bvar rfl)
        (TrM.special (c := `Quot.mk) (us := [.param `u]) (as := [.bvar 3, .bvar 2, .bvar 0])
          (as' := [#0, #1, #3]) BQ_mk rfl rfl
          (by
            intro i x x' h1 h2
            rcases i with _ | _ | _ | i <;> simp at h1 h2 <;> subst h1 h2 <;> exact TrM.bvar rfl)
          (SatTr.quotMk (rest := []) rfl))))
        (TrM.forallE (tr_quotC trLevel_u (TrM.bvar rfl) (TrM.bvar rfl))
          (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl))))))

theorem tr_IndC : TrM EQ BQ [`u] .nil [] (.const `Quot.ind [.param `u])
    ((ΔI ηQ).lam (.quotInd ηQ pu #0 #1 #2 #3 #4)) :=
  TrM.special (as := []) (as' := []) BQ_ind rfl rfl (fun _ _ _ h => nomatch h)
    (SatTr.quotEta (args := []) rfl (by decide) rfl)

theorem constTypedQ : ∀ q ∈ qs, BQ q.name = some (.quot .here (quotKindOf q.kind)) ∧
    ConstTyped EQ BQ (.quotInfo q) ∧ QuotShape q := by
  intro q hq
  simp only [qs, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨rfl, ⟨_, _, tr_QuotTy, tr_QuotC, quotT_typed⟩, .inl ⟨rfl, rfl, _, rfl⟩⟩
  · exact ⟨rfl, ⟨_, _, tr_MkTy, tr_MkC, quotM_typed⟩, .inr (.inl ⟨rfl, rfl, rfl⟩)⟩
  · exact ⟨rfl, ⟨_, _, tr_LiftTy, tr_LiftC, quotL_typed (η := ηQ) (by rw [heqQ]; exact hqQ)⟩,
      .inr (.inr (.inl ⟨rfl, rfl, rfl⟩))⟩
  · exact ⟨rfl, ⟨_, _, tr_IndTy, tr_IndC, quotI_typed⟩, .inr (.inr (.inr ⟨rfl, rfl⟩))⟩

/-- The quotient constants and NV-P's program are the Lean form of `EQ` with table `BQ`. -/
theorem henvQ : ProgEnv (qs.reverse.map .quotInfo ++ NVP.P) ζQ EQ BQ :=
  ProgEnv.quot NVP.henv BB_Eq rfl (by decide) (by decide)
    (fun n hn => by
      simp only [qs, Quot_val, QuotMk_val, QuotLift_val, QuotInd_val, List.map_cons, List.map_nil,
        List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
      obtain ⟨h1, h2, h3, h4⟩ := hn
      simp [BQ, Binds.set, h1, h2, h3, h4])
    constTypedQ

/-! ## The axioms `R` and `hR` -/

abbrev ζR : Sigs := ζQ.snoc (.const .«axiom» 0)
abbrev ζH : Sigs := ζR.snoc (.const .«axiom» 0)
abbrev ηRH : Head ζH (.const .«axiom» 0) := .there .here
abbrev ηHH : Head ζH (.const .«axiom» 0) := .here
abbrev ηQH : Head ζH .quot := .there (.there ηQ)
abbrev ηEH : Head ζH (.inductive Eq.sig) := .there (.there ηEQ)
abbrev ηBH : Head ζH (.inductive bSig) := .there (.there ηBQ)
abbrev ηBR : Head ζR (.inductive bSig) := .there ηBQ
abbrev ηER : Head ζR (.inductive Eq.sig) := .there ηEQ
abbrev ηRR : Head ζR (.const .«axiom» 0) := .here

section Terms
variable {ζ : Sigs} (ηB : Head ζ (.inductive bSig)) {n : Nat}

/-- `B → B`. -/
abbrev bbM : Expr ζ 0 n := .forallE (mB ηB) (mB ηB)
/-- `fun x => x : (B → B) → B → B`. -/
def idFM : Expr ζ 0 n := .lam (bbM ηB) (.var (Fin.last n))

end Terms

/-- `R`'s type `(B → B) → (B → B) → Prop`. -/
def RTyM : Expr ζQ 0 0 := .forallE (bbM ηBQ) (.forallE (bbM ηBQ) .prop)

theorem RTyM_eq : RTyM = Quot.relType (bbM ηBQ) := by eqsimp [RTyM]

theorem tr_RTy : TrM EQ BQ [] .nil [] R_ax.type RTyM :=
  TrM.forallE (TrM.forallE (tr_B BQ_B) (tr_B BQ_B))
    (TrM.forallE (TrM.forallE (tr_B BQ_B) (tr_B BQ_B)) (TrM.sort rfl))

def ER : Env ζR := EQ.snoc (.«axiom» RTyM)
def BR : Binds ζR := (Binds.wk BQ).set `R (.const .here)

theorem BR_R : BR `R = some (.const ηRR) := rfl
theorem BR_Eq : BR `Eq = some (.ind ηER 0) := rfl
theorem BR_B : BR `B = some (.ind ηBR 0) := rfl
theorem hbR : (ER.get ηBR).block = bBlock := by
  simp! [ER, EQ, EB, NVP.EA, NV1.E1, Env.get, Entry.block]
theorem hqR : (ER.get ηER).block = Eq.block := by
  simp! [ER, EQ, EB, NVP.EA, Env.get, Entry.block]

theorem hbQ : (EQ.get ηBQ).block = bBlock := by simp! [EQ, EB, NVP.EA, NV1.E1, Env.get, Entry.block]

theorem RTy_isType : EQ[.nil] ⊢ RTyM typ := by
  rw [RTyM_eq]; exact ⟨_, Quot.relType_congr (BB_typed hbQ)⟩

theorem henvR : ProgEnv (.axiomInfo R_ax :: (qs.reverse.map .quotInfo ++ NVP.P)) ζR ER BR :=
  ProgEnv.«axiom» henvQ (by decide) (by decide) rfl tr_RTy

theorem wfR : EnvWF ER := .snoc wfQ (.«axiom» RTy_isType)

/-- `R` in `ER`. -/
abbrev RM {ζ : Sigs} {n : Nat} (η : Head ζ (.const .«axiom» 0)) : Expr ζ 0 n := .const η Fin.elim0

/-- `hR`'s type `∀ a b : B → B, R a b → (fun x => x) a = (fun x => x) b`. -/
def hRTyM : Expr ζR 0 0 :=
  .forallE (bbM ηBR) (.forallE (bbM ηBR) (.forallE (.app (.app (RM ηRR) #0) #1)
    (eqA ηER l1M (bbM ηBR) (.app (idFM ηBR) #0) (.app (idFM ηBR) #1))))

/-- `hR`'s type is `Quot.compatType` at `B → B`, `R`, `B → B` and `fun x => x`. -/
theorem hRTyM_eq : hRTyM = Quot.compatType ηER l1M (bbM ηBR) (RM ηRR) (bbM ηBR) (idFM ηBR) := by
  eqsimp [hRTyM, idFM, RM, Quot.compatType]

theorem notSpecial_idF {ζ : Sigs} {B : Binds ζ} : ¬ SpecialHead B idF := by
  rintro ⟨c, us, b, h, -⟩; cases h

theorem tr_hRTy : TrM ER BR [] .nil [] hRTy hRTyM :=
  TrM.forallE (TrM.forallE (tr_B BR_B) (tr_B BR_B)) (TrM.forallE (TrM.forallE (tr_B BR_B) (tr_B BR_B))
    (TrM.forallE (TrM.app (notSpecial_const BR_R ⟨_, rfl⟩) (TrM.app (notSpecial_const BR_R ⟨_, rfl⟩)
      (TrM.const BR_R trLevels_nil) (TrM.bvar rfl)) (TrM.bvar rfl))
      (tr_eqC BR_Eq trLevel_l1 (TrM.forallE (tr_B BR_B) (tr_B BR_B))
        (TrM.app notSpecial_idF (TrM.lam (TrM.forallE (tr_B BR_B) (tr_B BR_B)) (TrM.bvar rfl))
          (TrM.bvar rfl))
        (TrM.app notSpecial_idF (TrM.lam (TrM.forallE (tr_B BR_B) (tr_B BR_B)) (TrM.bvar rfl))
          (TrM.bvar rfl)))))

section Typing
variable {ζ : Sigs} {E : Env ζ} {ηB : Head ζ (.inductive bSig)}

/-- `fun x => x : (B → B) → B → B`. -/
theorem idFM_typed (hb : (E.get ηB).block = bBlock) :
    E[(.nil : Ctx ζ 0 0 0)] ⊢ idFM ηB : .forallE (bbM ηB) (bbM ηB).wk := by
  have h1 : E[(#t[bbM ηB] : Ctx ζ 0 0 1)] ⊢ ok := .snoc .nil ⟨_, BB_typed hb⟩
  have hv := var_of_get h1 ⟨0, by decide⟩ (T := bbM ηB) (by nvsimp [bbM])
  exact typed_of_eq (.lamDF (BB_typed hb) (BB_typed hb) (BB_typed hb) hv hv) (by nvsimp [bbM])

/-- `fun y => y : B → B`. -/
theorem idM_typed' (hb : (E.get ηB).block = bBlock) :
    E[(.nil : Ctx ζ 0 0 0)] ⊢ idM ηB : bbM ηB := by
  have h1 : E[(#t[mB ηB] : Ctx ζ 0 0 1)] ⊢ ok := .snoc .nil ⟨_, indB_typed hb⟩
  have hv := var_of_get h1 ⟨0, by decide⟩ (T := mB ηB) (by nvsimp)
  exact .lamDF (mB_typed hb) (mB_typed hb) (mB_typed hb) hv hv

end Typing

theorem hcR : (ER.get ηRR).constType = Quot.relType (bbM ηBR) := by
  simp! [ER, Env.get, Entry.constType, RTyM]
  eqsimp [bbM]

theorem RR_typed : ER[.nil] ⊢ RM ηRR : Quot.relType (bbM ηBR) :=
  const_typed wfR ηRR Fin.elim0 (by rw [hcR]; eqsimp [Expr.wkClosed, bbM])

theorem hRTy_isType : ER[.nil] ⊢ hRTyM typ := by
  rw [hRTyM_eq]
  exact Quot.compatType_isType hqR (BB_typed hbR) RR_typed (BB_typed hbR) (idFM_typed hbR)

/-- The Metalean environment of NV-Q. -/
def EH : Env ζH := ER.snoc (.«axiom» hRTyM)

/-- The name table of NV-Q. -/
def BH : Binds ζH := (Binds.wk BR).set `hR (.const .here)

theorem BH_lift : BH `Quot.lift = some (.quot ηQH .lift) := rfl
theorem BH_mk : BH `Quot.mk = some (.quot ηQH .ctor) := rfl
theorem BH_R : BH `R = some (.const ηRH) := rfl
theorem BH_hR : BH `hR = some (.const ηHH) := rfl
theorem BH_B : BH `B = some (.ind ηBH 0) := rfl
theorem BH_t : BH `B.t = some (.ctor ηBH 0 1 []) := rfl

/-- `henv`: the program is the Lean form of `EH` with table `BH`. -/
theorem henv : ProgEnv P ζH EH BH :=
  ProgEnv.«axiom» henvR (by decide) (by decide) rfl tr_hRTy

/-- `hwf`: `EH` is well formed. -/
theorem hwf : EnvWF EH := .snoc wfR (.«axiom» hRTy_isType)

theorem hbH : (EH.get ηBH).block = bBlock := by
  simp! [EH, ER, EQ, EB, NVP.EA, NV1.E1, Env.get, Entry.block]
theorem hqH : (EH.get ηEH).block = Eq.block := by
  simp! [EH, ER, EQ, EB, NVP.EA, Env.get, Entry.block]
theorem heqH : (EH.get ηQH).eqHead = ηEH := by simp! [EH, ER, EQ, Env.get, Entry.eqHead]

/-- The erased term in Metalean. -/
def tE : Metalean.Expr ζH 0 0 :=
  .app (.quotLift ηQH l1M l1M (bbM ηBH) (RM ηRH) (bbM ηBH) (idFM ηBH) (RM ηHH)
    (.quotMk ηQH l1M (bbM ηBH) (RM ηRH) (idM ηBH))) (mT ηBH)

/-- `he`: the erased term is the Lean form of `tE`. -/
theorem he : TrM EH BH [] .nil [] e tE :=
  TrM.special (lps := []) (c := `Quot.lift) (us := [l1, l1])
    (as := [tBB, cR, tBB, idF, .const `hR [], qm, cT])
    (as' := [bbM ηBH, RM ηRH, bbM ηBH, idFM ηBH, RM ηHH,
      .quotMk ηQH l1M (bbM ηBH) (RM ηRH) (idM ηBH), mT ηBH]) BH_lift rfl rfl
    (by
      intro i x x' h1 h2
      rcases i with _ | _ | _ | _ | _ | _ | _ | i <;> simp at h1 h2 <;> subst h1 h2
      · exact TrM.forallE (tr_B BH_B) (tr_B BH_B)
      · exact TrM.const BH_R trLevels_nil
      · exact TrM.forallE (tr_B BH_B) (tr_B BH_B)
      · exact TrM.lam (TrM.forallE (tr_B BH_B) (tr_B BH_B)) (TrM.bvar rfl)
      · exact TrM.const BH_hR trLevels_nil
      · refine TrM.special (lps := []) (c := `Quot.mk) (us := [l1]) (as := [tBB, cR, idB])
          (as' := [bbM ηBH, RM ηRH, idM ηBH]) BH_mk rfl rfl ?_ (SatTr.quotMk (rest := []) rfl)
        intro j y y' g1 g2
        rcases j with _ | _ | _ | j <;> simp at g1 g2 <;> subst g1 g2
        · exact TrM.forallE (tr_B BH_B) (tr_B BH_B)
        · exact TrM.const BH_R trLevels_nil
        · exact TrM.lam (tr_B BH_B) (TrM.bvar rfl)
      · exact tr_T BH_t)
    (SatTr.quotLift (rest := [mT ηBH]) rfl)

theorem hcRH : (EH.get ηRH).constType = Quot.relType (bbM ηBH) := by
  simp! [EH, ER, Env.get, Entry.constType, RTyM]
  eqsimp [bbM]

theorem hcHH : (EH.get ηHH).constType =
    Quot.compatType ηEH l1M (bbM ηBH) (RM ηRH) (bbM ηBH) (idFM ηBH) := by
  simp! [EH, Env.get, Entry.constType, hRTyM]
  eqsimp [bbM, idFM, RM]

/-- `hty`: `tE` is typed. -/
theorem hty : ∃ T, EH[.nil] ⊢ tE : T := by
  have hα : EH[(.nil : Ctx ζH 0 0 0)] ⊢ bbM ηBH : .sort l1M := BB_typed hbH
  have hr : EH[(.nil : Ctx ζH 0 0 0)] ⊢ RM ηRH : Quot.relType (bbM ηBH) :=
    const_typed hwf ηRH Fin.elim0 (by rw [hcRH]; eqsimp [Expr.wkClosed, bbM])
  have hh : EH[(.nil : Ctx ζH 0 0 0)] ⊢ RM ηHH :
      Quot.compatType (EH.get ηQH).eqHead l1M (bbM ηBH) (RM ηRH) (bbM ηBH) (idFM ηBH) := by
    rw [heqH]
    exact const_typed hwf ηHH Fin.elim0 (by rw [hcHH]; eqsimp [Expr.wkClosed, bbM, idFM, RM])
  have hlift : EH[(.nil : Ctx ζH 0 0 0)] ⊢ .quotLift ηQH l1M l1M (bbM ηBH) (RM ηRH) (bbM ηBH)
      (idFM ηBH) (RM ηHH) (.quotMk ηQH l1M (bbM ηBH) (RM ηRH) (idM ηBH)) : bbM ηBH :=
    .quotLiftDF hα hr hα (idFM_typed hbH) hh (.quotMkDF hα hr (idM_typed' hbH))
  exact ⟨_, app_typed hlift (mT_typed hbH)⟩

end EraseProof.Test.NVQ
