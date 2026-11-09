import EraseProof.Spec
import Metalean.Typing.Substitution

/-!
# Erasability under substitution

A type former or a proof stays one when a typed term is substituted for its innermost variable
(`IsErasable.inst`): typing and type equality are stable under instantiation (`Defeq.inst_congr`,
`TypeEq.inst_congr₂`, `ML Typing/Substitution.lean:188`, `ML Typing/TypeEq.lean:106`), and the
shapes `Π Δ, Sort u` and `Prop` commute with substitution (`Ctx.pi_subst`,
`ML Syntax/Substitution.lean:271`).
-/

open Metalean (Defeq TypeEq EnvWF)

namespace EraseProof

/-- Substituting a typed term for the innermost variable of an erasable term. Reference:
`is_type_subst` (`MR E/ESubstitution.v:346`); `Defeq.inst_congr`
(`ML Typing/Substitution.lean:188`). -/
theorem IsErasable.inst {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {lps : List Name} {n : Nat}
    {Γ : Metalean.Ctx ζ lps.length 0 n} {a : Metalean.Expr ζ lps.length n}
    {b : Metalean.Expr ζ lps.length (n + 1)} (_hE : EnvWF E) {A : Metalean.Expr ζ lps.length n}
    (ha : E[Γ] ⊢ a : A) (h : IsErasable E (Γ.snoc A) b) : IsErasable E Γ (b.inst a) := by
  obtain ⟨T, hT, hA | hP⟩ := h
  · obtain ⟨k, Δ, u, hA⟩ := hA
    refine ⟨T.inst a, (Defeq.inst_congr hT ha).left,
      .inl ⟨k, Metalean.Ctx.substN (Metalean.Subst.id.extend a) k Δ, u, ?_⟩⟩
    have := TypeEq.inst_congr₂ hA ha
    simpa [Metalean.Expr.inst, Metalean.Ctx.pi_subst] using this
  · refine ⟨T.inst a, (Defeq.inst_congr hT ha).left, .inr ?_⟩
    simpa [Metalean.Expr.inst, Metalean.Expr.subst] using Defeq.inst_congr hP ha

end EraseProof
