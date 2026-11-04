import Metalean.Typing.Substitution

/-!
# Substitution under binders whose types need not be typed

Metalean's public `Defeq.substitution` asks every variable of the source context to be sent to a
typed term, so substituting under binders asks their types to be typed. Its private lemma
`Defeq.substRen` also accepts variables that are renamed to a variable of the same type, and so
substitutes a typed term for a variable under any telescope of binders (`Defeq.inst_tele`).

The definitions `SubstImage`, `SubstRen` and the lemmas `SubstRen.lift`, `SubstRen.liftN`,
`SubstRen.inst`, `Defeq.substRen` are copied from Metalean (`https://github.com/intgrah/metalean`,
commit `9407ba4407374a05e90777a068c2dc520e4ac0e7`, file `Metalean/Typing/Substitution.lean`,
Copyright (c) 2026 Jeremy Chen), which is distributed under the Apache License 2.0. The generic
`Defeq.substOf` there is specialised here to `SubstRen`; the proof is the same.
-/

namespace EraseProof
open Metalean

variable {ζ : Sigs} {E : Env ζ} {ℓ n m : Nat}

/-- How a substitution treats one variable: sent to a typed term, or renamed to a variable of the
substituted type. Copied from `ML Typing/Substitution.lean:20` (`SubstImage`). -/
private inductive SubstImage (E : Env ζ) (Γ₁ : Ctx ζ ℓ 0 n) (Γ₂ : Ctx ζ ℓ 0 m)
    (σ : Subst ζ ℓ n m) (v : Var n) : Prop where
  | typed (h : E[Γ₂] ⊢ σ v : (Γ₁.get v).subst σ)
  | renamed (w : Var m) (hσ : σ v = .var w) (htype : Γ₂.get w = (Γ₁.get v).subst σ)

/-- Every variable is sent to a typed term or renamed. Copied from
`ML Typing/Substitution.lean:25` (`SubstRen`). -/
private def SubstRen (E : Env ζ) (Γ₁ : Ctx ζ ℓ 0 n) (Γ₂ : Ctx ζ ℓ 0 m) (σ : Subst ζ ℓ n m) :
    Prop :=
  ∀ v : Var n, SubstImage E Γ₁ Γ₂ σ v

/-- Copied from `ML Typing/Substitution.lean:138` (`SubstRen.lift`). -/
private theorem SubstRen.lift {Γ₁ : Ctx ζ ℓ 0 n} {Γ₂ : Ctx ζ ℓ 0 m} {σ : Subst ζ ℓ n m}
    {t : Expr ζ ℓ n} (h : SubstRen E Γ₁ Γ₂ σ) :
    SubstRen E (Γ₁.snoc t) (Γ₂.snoc (t.subst σ)) σ.lift := fun v => by
  cases v using Fin.lastCases with
  | last =>
    exact .renamed (Fin.last m) (Subst.lift_last σ)
      (by simp)
  | cast v =>
    cases h v with
    | typed d =>
      refine .typed ?_
      simpa using d.wk (t.subst σ)
    | renamed w hw htype =>
      refine .renamed w.castSucc ?_ ?_
      · simp [hw, Expr.wk]
      · simp
        exact congrArg Expr.wk htype

/-- Copied from `ML Typing/Substitution.lean:155` (`SubstRen.liftN`). -/
private theorem SubstRen.liftN {Γ₁ : Ctx ζ ℓ 0 n} {Γ₂ : Ctx ζ ℓ 0 m} {σ : Subst ζ ℓ n m}
    (h : SubstRen E Γ₁ Γ₂ σ) (k : Nat) (Δ : Ctx ζ ℓ n (n + k)) :
    SubstRen E (Γ₁ ++ Δ) (Γ₂ ++ Ctx.substN σ k Δ) (σ.liftN k) := by
  induction Δ using Tele.addInduction with
  | nil => exact h
  | snoc k Δ t ih => simpa! [Ctx.substN] using ih.lift

/-- Copied from `ML Typing/Substitution.lean:162` (`SubstRen.inst`). -/
private theorem SubstRen.inst {Γ : Ctx ζ ℓ 0 m} {t e : Expr ζ ℓ m} (he : E[Γ] ⊢ e : t) :
    SubstRen E (Γ.snoc t) Γ (Subst.id.extend e) := fun v => by
  cases v using Fin.lastCases with
  | last =>
    exact .typed (by simpa [Expr.wk_subst_extend] using he)
  | cast v =>
    refine .renamed v (Subst.extend_castSucc _ _ _) ?_
    simp
    change _ = (Γ.get v).wk.inst e
    simp

/-- Substitution by a substitution that types or renames every variable. Copied from
`ML Typing/Substitution.lean:32` (`Defeq.substOf`, instantiated at `SubstRen`) and `:176`
(`Defeq.substRen`). -/
private theorem Defeq.substRen {Γ₁ : Ctx ζ ℓ 0 n} {Γ₂ : Ctx ζ ℓ 0 m} {e₁ e₂ t : Expr ζ ℓ n}
    {σ : Subst ζ ℓ n m} (hσ : SubstRen E Γ₁ Γ₂ σ) :
    E[Γ₁] ⊢ e₁ ≡ e₂ : t →
    E[Γ₂] ⊢ e₁.subst σ ≡ e₂.subst σ : t.subst σ := by
  intro h
  induction h generalizing m Γ₂ with
    try simp! [Expr.inst_subst, Fin.fun_vecCons, Fin.fun_vecEmpty,
      Fin.const_fin_one] at *
  | var _ ih =>
    cases hσ _ with
    | typed d => exact d
    | renamed w hw htype =>
      simpa [hw, ← htype] using .var
        (by simpa [htype] using ih hσ)
  | symm _ ih => exact .symm (ih hσ)
  | trans _ _ ih₁ ih₂ => exact .trans (ih₁ hσ) (ih₂ hσ)
  | sortDF => exact .sortDF
  | constDF _ ihtype =>
    exact .constDF (ihtype hσ)
  | indDF _ _ ihps ihis =>
    exact .indDF (ihps · hσ) (ihis · hσ)
  | ctorDF _ _ _ _ _ _ ihps ihfields ihrecFields ihfieldTypes ihrecFieldTypes ihtype =>
    exact .ctorDF (ihps · hσ) (ihfields · hσ) (ihrecFields · hσ)
      (ihfieldTypes · hσ) (ihrecFieldTypes · hσ) (ihtype hσ)
  | @recrDF _ _ ι head target ls u ps _ ms₁ ms₂ mins₁ mins₂
      is _ maj _ hallowed _ _ _ _ _ _ ihps ihms ihmins
      ihis ihmaj ihresult =>
    exact .recrDF hallowed (ihps · hσ) (ihms · hσ)
      (ihmins · · hσ) (ihis · hσ) (ihmaj hσ) (ihresult hσ)
  | appDF _ _ _ _ _ iht iht' ihf ihe ihres =>
    exact .appDF
      (iht hσ) (iht' hσ.lift) (ihf hσ) (ihe hσ) (ihres hσ)
  | lamDF _ _ _ _ _ iht iht' iht₂' ihbody ihbody' =>
    exact .lamDF (iht hσ) (iht' hσ.lift) (iht₂' hσ.lift)
      (ihbody hσ.lift) (ihbody' hσ.lift)
  | forallEDF _ _ _ iht ihbody ihbody' =>
    exact .forallEDF (iht hσ) (ihbody hσ.lift) (ihbody' hσ.lift)
  | defeqDF _ _ iht ihe => exact .defeqDF (iht hσ) (ihe hσ)
  | beta _ _ _ _ _ _ iht iht' ihbody ihe ihres ihresult =>
    exact .beta (iht hσ) (iht' hσ.lift) (ihbody hσ.lift)
      (ihe hσ) (ihres hσ) (ihresult hσ)
  | zeta _ _ _ _ iht ihv ihr ihbody =>
    exact .zeta (iht hσ) (ihv hσ) (ihr hσ) (ihbody hσ)
  | @eta n Γ₁ l₁ l₂ e t t' _ _ _ _ _ iht iht' ihtwk ihewk ihe =>
    have hlift : ((fun w => σ.lift.lift (Ren.wkFrom n w)) :
        Subst ζ ℓ (n + 1) (m + 2)) = fun v => (σ.lift v).wkFrom m := by
      funext w
      cases w using Fin.lastCases with
      | last => simp
      | cast w =>
        simp
        rfl
    exact .eta
      (iht hσ) (iht' hσ.lift)
      (by simpa using ihtwk hσ.lift)
      (by
        have dewk := ihewk hσ.lift
        simp! [Expr.wkFrom_subst σ.lift.lift] at dewk
        rwa [hlift, ← Expr.subst_wkFrom σ.lift] at dewk)
      (ihe hσ)
  | etaStruct h _ _ _ ihps ihmaj ihrebuild =>
    exact .etaStruct h
      (fun p => ihps p hσ)
      (ihmaj hσ)
      (ihrebuild hσ)
  | proofIrrel _ _ _ ihp ihh ihh' =>
    exact .proofIrrel (ihp hσ) (ihh hσ) (ihh' hσ)
  | iota hallowed _ _ _ _ _ _ _ _ ihps ihms ihmins ihfields ihrecFields ihtype ihlhs ihrhs =>
    exact .iota hallowed (ihps · hσ) (ihms · hσ) (ihmins · · hσ)
      (ihfields · hσ) (ihrecFields · hσ) (ihtype hσ) (ihlhs hσ) (ihrhs hσ)
  | quotDF _ _ iht ihr =>
    exact .quotDF (iht hσ) (ihr hσ)
  | quotMkDF _ _ _ ihα ihr iha =>
    exact .quotMkDF (ihα hσ) (ihr hσ) (iha hσ)
  | quotLiftDF _ _ _ _ _ _ ihα ihr ihβ ihf ihh iha =>
    exact .quotLiftDF (ihα hσ) (ihr hσ) (ihβ hσ) (ihf hσ) (ihh hσ) (iha hσ)
  | quotIndDF _ _ _ _ _ _ ihα ihr ihβ ihf iha ihresult =>
    exact .quotIndDF (ihα hσ) (ihr hσ) (ihβ hσ) (ihf hσ) (iha hσ) (ihresult hσ)
  | quotIota _ _ _ _ _ _ _ _ ihα ihr ihβ ihf ihh iha ihlhs ihrhs =>
    exact .quotIota (ihα hσ) (ihr hσ) (ihβ hσ) (ihf hσ) (ihh hσ)
      (iha hσ) (ihlhs hσ) (ihrhs hσ)
  | delta _ _ ihtype ihvalue =>
    exact .delta (ihtype hσ) (ihvalue hσ)

/-- Substituting a typed term for a variable under a telescope `Θ` of binders, whose types need
not be typed: a judgement in `Γ.snoc A ++ Θ` holds in `Γ ++ Θ[a]` for the substituted terms.
Reference: `Defeq.substRen` with `SubstRen.inst` and `SubstRen.liftN`
(`ML Typing/Substitution.lean:162,155,176`); MR pcuic/theories/PCUICSubstitution.v:1774
`substitution`. -/
theorem Defeq.inst_tele {Γ : Ctx ζ ℓ 0 n} {A a : Expr ζ ℓ n} (ha : E[Γ] ⊢ a : A) {k : Nat}
    {Θ : Ctx ζ ℓ (n + 1) (n + 1 + k)} {e₁ e₂ T : Expr ζ ℓ (n + 1 + k)}
    (h : E[Γ.snoc A ++ Θ] ⊢ e₁ ≡ e₂ : T) :
    E[Γ ++ Ctx.substN (Subst.id.extend a) k Θ] ⊢ e₁.subst ((Subst.id.extend a).liftN k) ≡
      e₂.subst ((Subst.id.extend a).liftN k) : T.subst ((Subst.id.extend a).liftN k) :=
  Defeq.substRen ((SubstRen.inst ha).liftN k Θ) h

end EraseProof
