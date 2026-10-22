import Metalean.Semantics.Inversion

/-!
# No-confusion of type formers

Two type formers with different heads (sort, Π, inductive, quotient) are never equal as types.
Metalean states the injectivity of each type former (`ML Semantics/Inversion.lean:56`
`TypeEq.sort_model_inj`, `:66` `TypeEq.forallE_model_inj`, `:86` `TypeEq.quot_model_inj`, and
`:20` `Defeq.ind_model_inv`) but no disequality between them. The proofs follow the same route:
a type equality equates the interpretations of both sides in Metalean's domain model
(`ML Semantics/Inversion.lean:42` `TypeEq.rawInterpret_eq`); the interpretation of one side
contains its head's atom (`sortAtom`, `piAtom`, `indAtom`, `quotAtom`), and the interpretation of
the other side contains only shapes below its own head's atom, which no other head's atom is
(`ML Semantics/Basis/Order.lean:41` `Basis.Le`).
-/

namespace EraseProof
open Metalean CategoryTheory CoherentShape CodeAssignment Presheaf

variable {ζ : Sigs} {E : Env ζ} {ℓ n : Nat} {Δ : Ctx ζ ℓ 0 n} {l u : Level ℓ}
  {t₁ α r : Expr ζ ℓ n} {t₁' : Expr ζ ℓ (n + 1)} {ι : IndSig}
  {η : Head ζ (.inductive ι)} {s : Fin ι.nsorts} {ls : Fin ι.nlevels → Level ℓ}
  {ps : Fin ι.nparams → Expr ζ ℓ n} {is : Fin (ι.nindices s) → Expr ζ ℓ n} {θ : Head ζ .quot}

/-- A sort is not equal, as a type, to a Π-type.
MR pcuic/theories/PCUICConversion.v:326 ws_cumul_pb_Sort_Prod_inv. -/
theorem TypeEq.sort_ne_forallE (hE : EnvWF E) (hΔ : E[Δ] ⊢ ok) :
    ¬ E[Δ] ⊢ .sort l ≡ .forallE t₁ t₁' typ := by
  intro h
  have ⟨_, hr⟩ := h.right
  have ⟨⟨_, ht₁⟩, ⟨_, ht₁'⟩⟩ := hr.forallE_inv
  have hp : ((rawInterpret (piLimit E ℓ) (⟨Δ, hΔ⟩ : CtxCat E ℓ) (.forallE t₁ t₁')).app _ (𝟙 _).op
      fun _ ↦ ⊥).mem (𝟙 _) (piAtom (Ty.pairOfTyping (⟨Δ, hΔ⟩ : CtxCat E ℓ).as ht₁ ht₁')) := by
    rw [rawInterpret_forallE _ ht₁ ht₁', RawFamily.mem_piAtom_pi_value_iff]
    simp
  rw [← h.rawInterpret_eq hΔ hE, rawInterpret_sort, RawFamily.sort_value] at hp
  cases (ΩLower.mem_principal_id (R := pointedOrder E ℓ) _ _).mp hp with
  | collapse h => nomatch h

/-- A sort is not equal, as a type, to an inductive type.
MR pcuic/theories/PCUICConversion.v:1726 invert_cumul_sort_ind. -/
theorem TypeEq.sort_ne_ind (hE : EnvWF E) (hΔ : E[Δ] ⊢ ok) :
    ¬ E[Δ] ⊢ .sort l ≡ .ind η s ls ps is typ := by
  intro h
  have ⟨_, hr⟩ := h.right
  have hB := (hE.entryWF η).block
  have heq := h.rawInterpret_eq hΔ hE
  rw [rawInterpret_sort, RawFamily.sort_value,
    rawInterpret_ind_typed _ (IndTyping.ofTyping (Γ₁ := ⟨Δ, hΔ⟩) hB hr) hB,
    RawFamily.ind_value] at heq
  have hmem : (principalIdeal (sortAtom l : CoherentShape (⟨Δ, hΔ⟩ : CtxCat E ℓ))).mem
      (𝟙 _) (sortAtom l) := by
    rw [← ΩIdeal.val_mem]
    exact (ΩLower.mem_principal_id _ _).mpr le_rfl
  rw [← ΩIdeal.val_mem, heq] at hmem
  obtain ⟨_, _, hle⟩ := hmem
  cases hle with
  | collapse h => nomatch h

/-- A Π-type is not equal, as a type, to an inductive type.
MR pcuic/theories/PCUICConversion.v:1700 invert_cumul_prod_ind. -/
theorem TypeEq.forallE_ne_ind (hE : EnvWF E) (hΔ : E[Δ] ⊢ ok) :
    ¬ E[Δ] ⊢ .forallE t₁ t₁' ≡ .ind η s ls ps is typ := by
  intro h
  have ⟨_, hl⟩ := h.left
  have ⟨_, hr⟩ := h.right
  have ⟨⟨_, ht₁⟩, ⟨_, ht₁'⟩⟩ := hl.forallE_inv
  have hB := (hE.entryWF η).block
  have hp : ((rawInterpret (piLimit E ℓ) (⟨Δ, hΔ⟩ : CtxCat E ℓ) (.forallE t₁ t₁')).app _ (𝟙 _).op
      fun _ ↦ ⊥).mem (𝟙 _) (piAtom (Ty.pairOfTyping (⟨Δ, hΔ⟩ : CtxCat E ℓ).as ht₁ ht₁')) := by
    rw [rawInterpret_forallE _ ht₁ ht₁', RawFamily.mem_piAtom_pi_value_iff]
    simp
  rw [h.rawInterpret_eq hΔ hE,
    rawInterpret_ind_typed _ (IndTyping.ofTyping (Γ₁ := ⟨Δ, hΔ⟩) hB hr) hB,
    RawFamily.ind_value] at hp
  obtain ⟨_, _, hle⟩ := hp
  cases hle with
  | collapse h => nomatch h

/-- A sort is not equal, as a type, to a quotient type (`ML Syntax/Expr.lean:95` `Expr.quot`).
PCUIC has no primitive quotients; analogue of `sort_ne_ind`. -/
theorem TypeEq.sort_ne_quot (hE : EnvWF E) (hΔ : E[Δ] ⊢ ok) :
    ¬ E[Δ] ⊢ .sort l ≡ .quot θ u α r typ := by
  intro h
  have ⟨_, hr⟩ := h.right
  have heq := h.rawInterpret_eq hΔ hE
  rw [rawInterpret_sort, RawFamily.sort_value,
    rawInterpret_quot _ (QuotTyping.ofTyping ⟨Δ, hΔ⟩ hr), RawFamily.quot_value,
    QuotCode.map_hom_id] at heq
  have hmem : (principalIdeal (sortAtom l : CoherentShape (⟨Δ, hΔ⟩ : CtxCat E ℓ))).mem
      (𝟙 _) (sortAtom l) := by
    rw [← ΩIdeal.val_mem]
    exact (ΩLower.mem_principal_id _ _).mpr le_rfl
  rw [← ΩIdeal.val_mem, heq] at hmem
  cases (ΩLower.mem_principal_id (R := pointedOrder E ℓ) _ _).mp hmem with
  | collapse h => nomatch h

/-- A Π-type is not equal, as a type, to a quotient type.
PCUIC has no primitive quotients; analogue of `forallE_ne_ind`. -/
theorem TypeEq.forallE_ne_quot (hE : EnvWF E) (hΔ : E[Δ] ⊢ ok) :
    ¬ E[Δ] ⊢ .forallE t₁ t₁' ≡ .quot θ u α r typ := by
  intro h
  have ⟨_, hl⟩ := h.left
  have ⟨_, hr⟩ := h.right
  have ⟨⟨_, ht₁⟩, ⟨_, ht₁'⟩⟩ := hl.forallE_inv
  have hp : ((rawInterpret (piLimit E ℓ) (⟨Δ, hΔ⟩ : CtxCat E ℓ) (.forallE t₁ t₁')).app _ (𝟙 _).op
      fun _ ↦ ⊥).mem (𝟙 _) (piAtom (Ty.pairOfTyping (⟨Δ, hΔ⟩ : CtxCat E ℓ).as ht₁ ht₁')) := by
    rw [rawInterpret_forallE _ ht₁ ht₁', RawFamily.mem_piAtom_pi_value_iff]
    simp
  rw [h.rawInterpret_eq hΔ hE, rawInterpret_quot _ (QuotTyping.ofTyping ⟨Δ, hΔ⟩ hr),
    RawFamily.quot_value, QuotCode.map_hom_id] at hp
  cases (ΩLower.mem_principal_id (R := pointedOrder E ℓ) _ _).mp hp with
  | collapse h => nomatch h

/-- An inductive type is not equal, as a type, to a quotient type.
PCUIC has no primitive quotients; analogue of `forallE_ne_ind`. -/
theorem TypeEq.ind_ne_quot (hE : EnvWF E) (hΔ : E[Δ] ⊢ ok) :
    ¬ E[Δ] ⊢ .ind η s ls ps is ≡ .quot θ u α r typ := by
  intro h
  have ⟨_, hl⟩ := h.left
  have ⟨_, hr⟩ := h.right
  have hB := (hE.entryWF η).block
  have hq := QuotTyping.ofTyping ⟨Δ, hΔ⟩ hr
  have heq := h.rawInterpret_eq hΔ hE
  rw [rawInterpret_ind_typed _ (IndTyping.ofTyping (Γ₁ := ⟨Δ, hΔ⟩) hB hl) hB,
    RawFamily.ind_value, rawInterpret_quot _ hq, RawFamily.quot_value,
    QuotCode.map_hom_id] at heq
  have hmem : (principalIdeal (quotAtom (hq.code θ))).mem (𝟙 _) (quotAtom (hq.code θ)) := by
    rw [← ΩIdeal.val_mem]
    exact (ΩLower.mem_principal_id _ _).mpr le_rfl
  rw [← ΩIdeal.val_mem, ← heq] at hmem
  obtain ⟨_, _, hle⟩ := hmem
  cases hle with
  | collapse h => nomatch h

end EraseProof
