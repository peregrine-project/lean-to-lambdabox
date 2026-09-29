import EraseProof.Source.EvalEnv

/-!
# Unfolding a constant in the model

Every constant that evaluation unfolds (`EvalEnv.unfold?`) over a sub-environment of a program
has, in the program's model, a translated definition: for a definition its defining equation is a
definitional equality of the model, and for a theorem its type is a proposition, so that proof
irrelevance relates it to its value.
-/

open Lean Lean4Lean

namespace EraseProof

/-- `decls` is a sub-environment of `P`. Reference: `extends_decls` (the closure `Σ'` of
`MR E/ErasureFunction.v:1602 erase_global_deps` is a sub-environment), DV-3. -/
def SubEnv (decls P : List ConstantInfo) : Prop :=
  ∀ ci ∈ decls, findDecl P ci.name = some ci

section
variable {venv : VEnv} {P : List ConstantInfo} {σ : EvalEnv}

/-- `TrDef` is monotone in both environments (by `TrS.mono`). Reference: global weakening
(`MR pcuic/theories/PCUICWeakeningEnv.v:295 weakening_env_declared_constant`). -/
theorem TrDef.mono {venv₁ venvV₁ venv₂ venvV₂ : VEnv} (hle : venv₁ ≤ venv₂)
    (hleV : venvV₁ ≤ venvV₂) (h : TrDef venv₁ venvV₁ ci ci') : TrDef venv₂ venvV₂ ci ci' :=
  ⟨h.1.mono hle, h.2.1, h.2.2.mono hleV⟩

/-- A definition or theorem of `P` has a translated definition in the model, with its defining
equation (definitions) or a proof that its type is a proposition (theorems). Reference:
`declared_constant_inv` (`MR P/Typing/PCUICWeakeningEnvTyp.v:252`). -/
theorem ProgEnv.lookupDef (h : ProgEnv P venv) (hc : findDecl P c = some ci)
    (hk : (∃ v, ci = .defnInfo v) ∨ ∃ v, ci = .thmInfo v) :
    ∃ ci' : VDefVal, TrDef venv venv ci ci' ∧ venv.constants c = some ci'.toVConstant ∧
      (venv.defeqs ci'.toDefEq ∨ venv.HasType ci'.uvars [] ci'.type (.sort .zero)) := by
  induction h generalizing ci with
  | nil => simp [findDecl] at hc
  | «axiom» _ _ _ h2 ih =>
    have hle := VEnv.addConst_le h2
    rw [findDecl_cons] at hc
    split at hc
    · cases hc; obtain ⟨_, h⟩ | ⟨_, h⟩ := hk <;> cases h
    · have ⟨ci', h1, h2, h3⟩ := ih hc hk
      exact ⟨ci', h1.mono hle hle, hle.constants h2, h3.imp hle.defeqs (·.mono hle)⟩
  | @defn _ _ _ venv' ci' _ _ htr _ h2 ih =>
    have hle : _ ≤ venv'.addDefEq ci'.toDefEq := (VEnv.addConst_le h2).trans VEnv.addDefEq_le
    rw [findDecl_cons] at hc
    split at hc
    · cases hc; subst c
      exact ⟨ci', htr.mono hle hle, VEnv.addDefEq_le.constants (VEnv.addConst_self h2),
        .inl VEnv.addDefEq_self⟩
    · have ⟨ci', h1, h2, h3⟩ := ih hc hk
      exact ⟨ci', h1.mono hle hle, hle.constants h2, h3.imp hle.defeqs (·.mono hle)⟩
  | thm _ _ htr _ hp h2 ih =>
    have hle := VEnv.addConst_le h2
    rw [findDecl_cons] at hc
    split at hc
    · cases hc; subst c
      exact ⟨_, htr.mono hle hle, VEnv.addConst_self h2, .inr (hp.mono hle)⟩
    · have ⟨ci', h1, h2, h3⟩ := ih hc hk
      exact ⟨ci', h1.mono hle hle, hle.constants h2, h3.imp hle.defeqs (·.mono hle)⟩
  | «opaque» _ _ _ _ h2 ih =>
    have hle := VEnv.addConst_le h2
    rw [findDecl_cons] at hc
    split at hc
    · cases hc; obtain ⟨_, h⟩ | ⟨_, h⟩ := hk <;> cases h
    · have ⟨ci', h1, h2, h3⟩ := ih hc hk
      exact ⟨ci', h1.mono hle hle, hle.constants h2, h3.imp hle.defeqs (·.mono hle)⟩
  | @block _ _ venv' vs cis' _ _ _ htr _ h2 _ ih =>
    have hleV : venv' ≤ venv'.addDefEqs cis' := VEnv.addDefEqs_le
    have hle : _ ≤ venv'.addDefEqs cis' := (VEnv.addConsts_le h2).trans hleV
    simp only [findDecl, List.find?_append] at hc
    cases hb : (vs.reverse.map ConstantInfo.defnInfo).find? (·.name == c) with
    | none =>
      rw [hb, Option.none_or] at hc
      have ⟨ci', h1, h2, h3⟩ := ih hc hk
      exact ⟨ci', h1.mono hle hle, hle.constants h2, h3.imp hle.defeqs (·.mono hle)⟩
    | some d =>
      rw [hb, Option.some_or] at hc
      injection hc with hc
      subst hc
      have hn : d.name = c :=
        beq_iff_eq.1 (List.find?_some (p := fun x : ConstantInfo => x.name == c) hb)
      have ⟨v, hv, hd⟩ : ∃ v ∈ vs, ConstantInfo.defnInfo v = d := by
        simpa using List.mem_of_find?_eq_some hb
      subst hd hn
      have ⟨ci', hci', htr'⟩ := forall₂_exists_of_mem_left htr hv
      have hname : v.name = ci'.name := htr'.2.1
      refine ⟨ci', htr'.mono hle hleV, ?_, .inl (VEnv.addDefEqs_self hci')⟩
      rw [show (ConstantInfo.defnInfo v).name = ci'.name from hname]
      exact hleV.constants (VEnv.addConsts_constants h2 _ hci')

/-- An unfoldable constant of a sub-environment of `P`: its value translates, and it is δ-equal
(definitions) or a proof (theorems, justified by proof irrelevance as `TrEnv'.thm` is). Reference:
`declared_constant_inv` (`MR P/Typing/PCUICWeakeningEnvTyp.v:252`), the δ case of
`subject_reduction_eval` (`MR P/PCUICClassification.v:1093`). -/
theorem ProgEnv.unfold (h : ProgEnv P venv) (hsub : SubEnv σ.decls P)
    (hu : σ.unfold? c = some (ci, b)) :
    ∃ ci' : VDefVal, TrDef venv venv ci ci' ∧ venv.constants c = some ci'.toVConstant ∧
      (venv.defeqs ci'.toDefEq ∨ venv.HasType ci'.uvars [] ci'.type (.sort .zero)) := by
  have ⟨hc, hk⟩ := EvalEnv.unfold?_some hu
  have hn : ci.name = c :=
    beq_iff_eq.1 (List.find?_some (p := fun x : ConstantInfo => x.name == c) hc)
  have hP := hsub ci (List.mem_of_find?_eq_some hc)
  rw [hn] at hP
  exact h.lookupDef hP hk
end

end EraseProof
