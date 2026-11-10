import EraseProof.Erasability
import EraseProof.Env
import Lean4Lean.Theory.Typing.UniqueTyping

/-!
# Inversion of erasability

`IsErasable.app`: an application of an erasable function is erasable. `IsErasable.lam_inv`: the
body of an erasable λ is erasable. Both identify the erasable type of the term with a Π-type by
lean4lean's unique typing (`IsDefEq.uniq`), then read the codomain off it
(`IsErasable.forallE_cod`): Π-injectivity (`IsDefEqU.forallE_inv`) and `Sort ≢ Π`
(`IsDefEqU.sort_forallE_inv`) in the arity case, Sort-injectivity (`IsDefEqU.sort_inv`) and
`imax u v ≈ 0 ↔ v ≈ 0` in the propositional case. lean4lean states these for `VEnv.WF` only, which
`ProgEnv.wf` provides.
-/

open Lean Lean4Lean

namespace EraseProof

section
variable {venv : VEnv} {P : List ConstantInfo}

/-- A type that is an arity or a proposition and is convertible to `Π A, B` has a codomain
convertible to `B` that is an arity or a proposition. Reference: the step shared by `Is_type_app`
(`MR E/EArities.v:480`) and `Is_type_lambda` (`MR E/EArities.v:535`): `invert_cumul_arity_r`
(`MR P/PCUICConversion.v:1182`) for arities, `cumul_prop1'` (`MR E/EArities.v:430`) and
`is_propositional_sort_prod` (`MR E/EArities.v:529`) for propositions. -/
theorem IsErasable.forallE_cod (henv : ProgEnv P venv) (hΓ : OnCtx Γ (venv.IsType U))
    (hT : IsArity T ∨ ∃ u, venv.HasType U Γ T (.sort u) ∧ u ≈ .zero)
    (hTF : venv.IsDefEqU U Γ T (.forallE A B)) :
    ∃ B', (∃ w, venv.IsDefEq U (A :: Γ) B B' (.sort w)) ∧
      (IsArity B' ∨ ∃ u, venv.HasType U (A :: Γ) B' (.sort u) ∧ u ≈ .zero) := by
  have hwf := henv.wf
  obtain hT | ⟨u, hu, hu0⟩ := hT
  · cases T with
    | sort => exact (VEnv.IsDefEqU.sort_forallE_inv hwf hΓ hTF).elim
    | forallE A' B' =>
      obtain ⟨-, w, hB⟩ := VEnv.IsDefEqU.forallE_inv hwf hΓ hTF.symm
      exact ⟨B', ⟨w, hB⟩, .inl hT⟩
    | bvar | const | app | lam => exact hT.elim
  · obtain ⟨_, hX⟩ := hTF
    obtain ⟨⟨uA, hA⟩, uB, hB⟩ := hX.hasType.2.forallE_inv henv.ordered
    have hPi : venv.HasType U Γ T (.sort (.imax uA uB)) :=
      VEnv.HasType.defeqU_l hwf hΓ hX.symm.toU (hA.forallE hB)
    obtain ⟨_, hs⟩ := VEnv.IsDefEq.uniq hwf hΓ hu hPi
    have hu' := VEnv.IsDefEqU.sort_inv hwf hΓ hs.toU
    exact ⟨B, ⟨uB, hB⟩, .inr ⟨uB, hB, VLevel.imax_eq_zero.1 (hu'.symm.trans hu0)⟩⟩

/-- An application of an erasable function is erasable. Reference: `Is_type_app`
(`MR E/EArities.v:480`); Let. Lemma 2 (application clause). -/
theorem IsErasable.app (henv : ProgEnv P venv) (hΓ : OnCtx Γ (venv.IsType U))
    (hfa : venv.HasType U Γ (.app f a) T) (hf : IsErasable venv U Γ f) :
    IsErasable venv U Γ (.app f a) := by
  have hord := henv.ordered
  obtain ⟨A, B, hfAB, ha⟩ := hfa.app_inv hord hΓ
  obtain ⟨Tf, hTf, hT⟩ := hf
  obtain ⟨_, hTF⟩ := VEnv.IsDefEq.uniq henv.wf hΓ hTf hfAB
  obtain ⟨B', ⟨w, hBB'⟩, hB'⟩ := IsErasable.forallE_cod henv hΓ hT hTF.toU
  obtain ⟨uA, hA⟩ := ha.isType hord hΓ
  refine ⟨B'.inst a, ((VEnv.IsDefEq.forallEDF hA hBB').defeq hfAB).app ha, ?_⟩
  obtain hB' | ⟨u, hu, hu0⟩ := hB'
  · exact .inl hB'.inst
  · exact .inr ⟨u, hu.instN hord .zero ha, hu0⟩

/-- The body of an erasable λ is erasable. Reference: `Is_type_lambda` (`MR E/EArities.v:535`). -/
theorem IsErasable.lam_inv (henv : ProgEnv P venv) (hΓ : OnCtx Γ (venv.IsType U))
    (h : IsErasable venv U Γ (.lam A b)) : IsErasable venv U (A :: Γ) b := by
  obtain ⟨T, hT, hTe⟩ := h
  obtain ⟨⟨_, hA⟩, B, hb⟩ := hT.lam_inv henv.ordered hΓ
  obtain ⟨_, hTF⟩ := VEnv.IsDefEq.uniq henv.wf hΓ hT (hA.lam hb)
  obtain ⟨B', ⟨_, hBB'⟩, hB'⟩ := IsErasable.forallE_cod henv hΓ hTe hTF.toU
  exact ⟨B', hBB'.defeq hb, hB'⟩

end

end EraseProof
