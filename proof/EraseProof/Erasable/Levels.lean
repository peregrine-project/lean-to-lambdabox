import EraseProof.Spec
import Metalean.Typing.InstLevel

/-!
# Erasability under universe instantiation

A type former or a proof stays one when its universe parameters are instantiated
(`IsErasable.instL`): typing, type equality and the shapes `Π Δ, Sort u` and `Prop` commute with
Metalean's universe instantiation `Expr.instL` (`Defeq.instLevel`, `ML Typing/InstLevel.lean:19`).
-/

open Metalean (Defeq TypeEq)

namespace EraseProof

variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {ℓ ℓ' n : Nat}

/-- Universe instantiation of a type equality. -/
private theorem TypeEq.instL (ls : Fin ℓ → Metalean.Level ℓ') {Γ : Metalean.Ctx ζ ℓ 0 n}
    {T U : Metalean.Expr ζ ℓ n} (h : E[Γ] ⊢ T ≡ U typ) : E[Γ{ls}] ⊢ T{ls} ≡ U{ls} typ := by
  induction h with
  | single h =>
    obtain ⟨u, h⟩ := h
    exact .single ⟨u{ls}, by simpa using h.instLevel ls⟩
  | tail _ h ih =>
    obtain ⟨u, h⟩ := h
    exact .tail ih ⟨u{ls}, by simpa using h.instLevel ls⟩

/-- Universe instantiation of an erasable term in a context. Reference: `isErasable_subst_instance`
(`MR E/ErasureProperties.v:262`); `Defeq.instLevel` (`ML Typing/InstLevel.lean:19`). -/
theorem IsErasable.instL_ctx (ls : Fin ℓ → Metalean.Level ℓ') {Γ : Metalean.Ctx ζ ℓ 0 n}
    {t : Metalean.Expr ζ ℓ n} (h : IsErasable E Γ t) : IsErasable E (Γ{ls}) t{ls} := by
  obtain ⟨T, hT, hA | hP⟩ := h
  · obtain ⟨k, Δ, u, hA⟩ := hA
    exact ⟨T{ls}, hT.instLevel ls, .inl ⟨k, Δ{ls}, u{ls}, by simpa using TypeEq.instL ls hA⟩⟩
  · exact ⟨T{ls}, hT.instLevel ls, .inr (by simpa using hP.instLevel ls)⟩

/-- Universe instantiation of closed erasable terms. Reference: `isErasable_subst_instance`
(`MR E/ErasureProperties.v:262`); `Defeq.instLevel` (`ML Typing/InstLevel.lean:19`). -/
theorem IsErasable.instL {lps lps' : List Name} {t : Metalean.Expr ζ lps'.length 0}
    {ls : Fin lps'.length → Metalean.Level lps.length} (_hE : Metalean.EnvWF E)
    (h : IsErasable E .nil t) : IsErasable E .nil t{ls} := by
  simpa using IsErasable.instL_ctx ls h

end EraseProof
