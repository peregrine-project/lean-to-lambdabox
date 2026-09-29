import Lean4Lean.Theory.Typing.Lemmas

/-!
# Erasability

`IsErasable` is MetaRocq's `isErasable` over lean4lean's model: some type of the term is an arity
or a proposition. This module proves that erasability is stable under substitution of a variable
and under universe instantiation (Letouzey, Lemma 2).
-/

open Lean Lean4Lean

namespace EraseProof

/-- Syntactic arities `Π x₁…xₙ, Sort u` of the model. Reference: `isArity`
(`MR P/PCUICTyping.v:29`); Let. Def. 1 (type schemes). -/
def IsArity : VExpr → Prop
  | .sort _ => True
  | .forallE _ B => IsArity B
  | _ => False

/-- Some type of `e` is an arity or a proposition (Lean: sort `≈ 0`, no SProp; DV-4). Reference:
`MR E/Extract.v:18 isErasable`; MC §7.3; Let. Def. 1 and the (□) clause of Def. 3. -/
def IsErasable (venv : VEnv) (U : Nat) (Γ : List VExpr) (e : VExpr) : Prop :=
  ∃ T, venv.HasType U Γ e T ∧ (IsArity T ∨ ∃ u, venv.HasType U Γ T (.sort u) ∧ u ≈ .zero)

/-- Arities are stable under substitution at any depth. Reference: `isArity_subst`
(`MR P/PCUICClassification.v:33`), the arity case of `is_type_subst`
(`MR E/ESubstitution.v:346`). -/
theorem IsArity.inst : ∀ {T : VExpr} {k : Nat}, IsArity T → IsArity (T.inst a k)
  | .sort _, _, _ => trivial
  | .forallE _ B, _, h => IsArity.inst (T := B) h
  | .bvar _, _, h | .const .., _, h | .app .., _, h | .lam .., _, h => h.elim

/-- Arities are stable under universe instantiation. Reference: `isArity_subst_instance`
(`MR P/Typing/PCUICUnivSubstitutionTyp.v:537`), the arity case of `isErasable_subst_instance`
(`MR E/ErasureProperties.v:262`). -/
theorem IsArity.instL : ∀ {T : VExpr}, IsArity T → IsArity (T.instL ls)
  | .sort _, _ => trivial
  | .forallE _ B, h => IsArity.instL (T := B) h
  | .bvar _, h | .const .., h | .app .., h | .lam .., h => h.elim

section
variable {venv : VEnv}

/-- Erasability is stable under substitution of one variable. Reference: `is_type_subst`
(`MR E/ESubstitution.v:346`); Let. Lemma 2 (substitution clauses). -/
theorem IsErasable.inst (henv : venv.Ordered) (h₀ : venv.HasType U Γ a A)
    (h : IsErasable venv U (A :: Γ) b) : IsErasable venv U Γ (b.inst a) := by
  obtain ⟨T, hT, hT'⟩ := h
  refine ⟨T.inst a, hT.instN henv .zero h₀, ?_⟩
  obtain hT' | ⟨u, hu, hu0⟩ := hT'
  · exact .inl hT'.inst
  · exact .inr ⟨u, hu.instN henv .zero h₀, hu0⟩

/-- Erasability is stable under universe instantiation. Reference: `isErasable_subst_instance`
(`MR E/ErasureProperties.v:262`). -/
theorem IsErasable.instL (hls : ∀ l ∈ ls, l.WF U') (h : IsErasable venv U Γ e) :
    IsErasable venv U' (Γ.map (VExpr.instL ls)) (e.instL ls) := by
  obtain ⟨T, hT, hT'⟩ := h
  refine ⟨T.instL ls, hT.instL hls, ?_⟩
  obtain hT' | ⟨u, hu, hu0⟩ := hT'
  · exact .inl hT'.instL
  · exact .inr ⟨u.inst ls, hu.instL hls, VLevel.inst_congr_l hu0⟩

end

end EraseProof
