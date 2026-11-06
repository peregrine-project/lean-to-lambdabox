import EraseProof.Spec
import EraseProof.Metatheory.NoConf
import Metalean.Metatheory.Unique
import Metalean.Metatheory.Injectivity
import Metalean.Typing.Inversion

/-!
# Inversion of erasability

An application of a type former or a proof is one (`IsErasable.app`); the body of an erasable λ is
erasable (`IsErasable.lam_inv`); a constructor application of an inductive whose sort is not
`Prop` is not erasable (`IsErasable.ctor_not`). The arity half goes through the shape of an arity
(`ErasableInv.Shape`: a sort under Π-binders, outermost binder first) and the injectivity of Π-types
(`TypeEq.forallE_inj`, `ML Metatheory/Injectivity.lean:24`); the proof half through uniqueness of
types (`Defeq.uniqTy`, `ML Metatheory/Unique.lean:149`) and the inversion of Π-typing
(`Defeq.forallE_ty_inv`, `ML Typing/Inversion.lean:56`).
-/

open Metalean (Defeq TypeEq EnvWF)

namespace EraseProof

variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {ℓ n : Nat} {Γ : Metalean.Ctx ζ ℓ 0 n}

namespace ErasableInv

/-- A sort under Π-binders, read from the outermost binder. -/
private inductive Shape : {n : Nat} → Metalean.Expr ζ ℓ n → Prop
  | sort : Shape (.sort u)
  | forallE : Shape B → Shape (.forallE A B)

private theorem Shape.pi {X : Metalean.Expr ζ ℓ b} (hX : Shape X) :
    ∀ Δ : Metalean.Ctx ζ ℓ a b, Shape (Metalean.Ctx.pi X Δ) := by
  intro Δ
  induction Δ with
  | nil => exact hX
  | snoc Δ A ih => exact ih (.forallE hX)

private theorem Shape.exists_pi {T : Metalean.Expr ζ ℓ n} (h : Shape T) :
    ∃ (b : Nat) (Δ : Metalean.Ctx ζ ℓ n b) (u : Metalean.Level ℓ), T = Metalean.Ctx.pi (.sort u) Δ := by
  induction h with
  | sort => exact ⟨_, .nil, _, rfl⟩
  | @forallE m B A _ ih =>
    obtain ⟨b, Δ, u, rfl⟩ := ih
    refine ⟨b, (Metalean.Ctx.nil.snoc A) ++ Δ, u, ?_⟩
    exact (Tele.foldr_append (S := Metalean.Expr ζ ℓ) Metalean.Expr.forallE (.sort u)
      (Metalean.Ctx.nil.snoc A) Δ).symm

private theorem Shape.subst {T : Metalean.Expr ζ ℓ m} (h : Shape T) :
    ∀ {n} (σ : Metalean.Subst ζ ℓ m n), Shape (T.subst σ) := by
  induction h with
  | sort => intro _ _; exact .sort
  | forallE _ ih => intro _ σ; exact .forallE (ih _)

private theorem isArity_iff {T : Metalean.Expr ζ ℓ n} :
    IsArity E Γ T ↔ ∃ X, Shape X ∧ E[Γ] ⊢ T ≡ X typ := by
  constructor
  · rintro ⟨k, Δ, u, h⟩
    exact ⟨_, Shape.pi .sort Δ, h⟩
  · rintro ⟨X, hX, h⟩
    obtain ⟨b, Δ, u, rfl⟩ := hX.exists_pi
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le Δ.le
    exact ⟨k, Δ, u, h⟩

/-- A Π-type equal to an arity has an arity as codomain. -/
private theorem arity_cod (hE : EnvWF E) (hΓ : E[Γ] ⊢ ok) {A : Metalean.Expr ζ ℓ n}
    {B : Metalean.Expr ζ ℓ (n + 1)} {X : Metalean.Expr ζ ℓ n} (hX : Shape X)
    (h : E[Γ] ⊢ .forallE A B ≡ X typ) : ∃ Y, Shape Y ∧ E[Γ.snoc A] ⊢ B ≡ Y typ := by
  cases hX with
  | sort => exact absurd h.symm (TypeEq.sort_ne_forallE hE hΓ)
  | forallE hY => exact ⟨_, hY, (TypeEq.forallE_inj hE hΓ h).2⟩

private theorem imax_eq_zero {l₁ l₂ : Metalean.Level ℓ} (h : l₁.imax l₂ = .zero) : l₂ = .zero := by
  apply Metalean.Level.ext
  intro ν
  have := congrArg (Metalean.Level.eval ν) h
  simp only [Metalean.Level.eval_imax, Metalean.Level.eval_zero] at this
  have := Nat.le_imax_right (n := Metalean.Level.eval ν l₁) (m := Metalean.Level.eval ν l₂)
  simp only [Metalean.Level.eval_zero]
  omega

/-- A type equal to a proposition is a proposition. -/
private theorem prop_of_typeEq (hE : EnvWF E) (hΓ : E[Γ] ⊢ ok) {T U : Metalean.Expr ζ ℓ n}
    (hT : E[Γ] ⊢ T : .prop) (h : E[Γ] ⊢ T ≡ U typ) : E[Γ] ⊢ U : .prop := by
  obtain ⟨l, hl⟩ := TypeEq.sort_uniq hE hΓ h
  obtain rfl := TypeEq.sort_inj hE hΓ (Defeq.uniqTy hE hΓ hl.left hT)
  exact hl.right

/-- The codomain of a proposition `Π A, B` is a proposition. -/
private theorem prop_cod {A : Metalean.Expr ζ ℓ n} {B : Metalean.Expr ζ ℓ (n + 1)} (hE : EnvWF E)
    (hΓ : E[Γ] ⊢ ok) (h : E[Γ] ⊢ .forallE A B : .prop) : E[Γ.snoc A] ⊢ B : .prop := by
  obtain ⟨_, _, -, hB, hs⟩ := Defeq.forallE_ty_inv h
  have := TypeEq.sort_inj hE hΓ hs
  rw [imax_eq_zero this.symm] at hB
  exact hB

end ErasableInv

open ErasableInv

/-- An application of a type former or a proof is one. Reference: `MR E/EArities.v` (`Is_type_app`,
`Is_proof` of applications). -/
theorem IsErasable.app {f a T : Metalean.Expr ζ ℓ n} (hE : EnvWF E) (hΓ : E[Γ] ⊢ ok)
    (h : IsErasable E Γ f) (ht : E[Γ] ⊢ .app f a : T) : IsErasable E Γ (.app f a) := by
  obtain ⟨Tf, hf, hTf⟩ := h
  obtain ⟨A, B, hf', ha, hT⟩ := Defeq.app_inv ht
  have hpi : E[Γ] ⊢ Tf ≡ .forallE A B typ := Defeq.uniqTy hE hΓ hf hf'
  refine ⟨T, ht, ?_⟩
  rcases hTf with hTf | hTf
  · obtain ⟨X, hX, hTX⟩ := isArity_iff.1 hTf
    obtain ⟨Y, hY, hBY⟩ := arity_cod hE hΓ hX (hpi.symm.trans hTX)
    exact .inl (isArity_iff.2 ⟨_, hY.subst _, hT.trans (TypeEq.instCongr hΓ ha hBY)⟩)
  · have hB := prop_cod hE hΓ (prop_of_typeEq hE hΓ hTf hpi)
    have hBa : E[Γ] ⊢ B.inst a : .prop := Defeq.substitution (Metalean.SubstWF.inst hΓ ha) hB
    exact .inr (prop_of_typeEq hE hΓ hBa hT.symm)

/-- The body of an erasable λ is erasable. Reference: `MR E/EArities.v` (`Is_type_lambda`). -/
theorem IsErasable.lam_inv {A : Metalean.Expr ζ ℓ n} {b : Metalean.Expr ζ ℓ (n + 1)}
    (hE : EnvWF E) (hΓ : E[Γ] ⊢ ok) (h : IsErasable E Γ (.lam A b)) :
    IsErasable E (Γ.snoc A) b := by
  obtain ⟨T, ht, hT⟩ := h
  obtain ⟨B, hb, hTB⟩ := Defeq.lam_inv ht hΓ
  refine ⟨B, hb, ?_⟩
  rcases hT with hT | hT
  · obtain ⟨X, hX, hTX⟩ := isArity_iff.1 hT
    obtain ⟨Y, hY, hBY⟩ := arity_cod hE hΓ hX (hTB.symm.trans hTX)
    exact .inl (isArity_iff.2 ⟨Y, hY, hBY⟩)
  · exact .inr (prop_cod hE hΓ (prop_of_typeEq hE hΓ hT hTB))

/-- A constructor application of an inductive whose sort is not `Prop` is not erasable. Reference:
`MR E/EArities.v` (`Is_proof` of constructors of non-propositional inductives). -/
theorem IsErasable.ctor_not {ι : Metalean.IndSig} {η : Metalean.Head ζ (.inductive ι)}
    {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} {ls : Fin ι.nlevels → Metalean.Level ℓ}
    {ps : Fin ι.nparams → Metalean.Expr ζ ℓ n}
    {fds : Fin (ι.ctors s c).nfields → Metalean.Expr ζ ℓ n}
    {recFds : Fin (ι.ctors s c).nrecFields → Metalean.Expr ζ ℓ n} {T : Metalean.Expr ζ ℓ n}
    (hE : EnvWF E) (hΓ : E[Γ] ⊢ ok) (hl : (E.get η).block.level{ls} ≠ .zero)
    (_ht : E[Γ] ⊢ .ctor η s c ls ps fds recFds : T) :
    ¬ IsErasable E Γ (.ctor η s c ls ps fds recFds) := by
  rintro ⟨T', ht', hT'⟩
  obtain ⟨_, _, _, -, -, -, -, hind⟩ := Defeq.ctor_inv ht'
  rcases hT' with hT' | hT'
  · obtain ⟨X, hX, hTX⟩ := isArity_iff.1 hT'
    have h := hind.symm.trans hTX
    cases hX with
    | sort => exact TypeEq.sort_ne_ind hE hΓ h.symm
    | forallE => exact TypeEq.forallE_ne_ind hE hΓ h.symm
  · have hI := prop_of_typeEq hE hΓ hT' hind
    obtain ⟨_, _, -, -, hs⟩ := Defeq.ind_inv hI
    exact hl (TypeEq.sort_inj hE hΓ hs).symm

/-- The element of an erasable `Quot.mk` is erasable: the type of a `Quot.mk` is a quotient type,
which is no arity (`TypeEq.sort_ne_quot`, `TypeEq.forallE_ne_quot`), so the `Quot.mk` is a proof,
the quotient a proposition, and the element a proof. Reference: none (PCUIC has no quotients;
DV-27). -/
theorem IsErasable.quotMk_inv {η : Metalean.Head ζ .quot} {l : Metalean.Level ℓ}
    {α r a : Metalean.Expr ζ ℓ n} (hE : EnvWF E) (hΓ : E[Γ] ⊢ ok)
    (h : IsErasable E Γ (.quotMk η l α r a)) : IsErasable E Γ a := by
  obtain ⟨T', ht', hT'⟩ := h
  have hq := Defeq.quotMk_inv ht'
  obtain ⟨α₁, r₁, a₁, hα, -, ha, -⟩ := Defeq.quotMk_prem ht'
  rcases hT' with hT' | hT'
  · obtain ⟨X, hX, hTX⟩ := isArity_iff.1 hT'
    have h := hq.symm.trans hTX
    cases hX with
    | sort => exact (TypeEq.sort_ne_quot hE hΓ h.symm).elim
    | forallE => exact (TypeEq.forallE_ne_quot hE hΓ h.symm).elim
  · have hQ := prop_of_typeEq hE hΓ hT' hq
    obtain rfl := TypeEq.sort_inj hE hΓ (Defeq.quot_inv hQ).symm
    exact ⟨_, ha.right, .inr hα.left⟩

end EraseProof
