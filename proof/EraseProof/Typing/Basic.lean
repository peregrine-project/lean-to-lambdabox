import Lean4Lean.Verify.Typing.Lemmas

/-!
# The translation of Lean terms into lean4lean's model

`TrS` relates a Lean `Expr` to its image in lean4lean's `VExpr` model of Lean's kernel, and this
module proves its structural lemmas: determinism, scoping, monotonicity in the environment and
well-formedness of the image.
-/

open Lean Lean4Lean

namespace EraseProof

/-- The translation of Lean terms into master's model: lean4lean `TrExprS`
(`l4l Verify/Typing/Expr.lean:75`) without the `lit` and `proj` rules (DV-2). Reference: the role of
MetaRocq's Template→PCUIC translation (`trans`, `MR template-pcuic/theories/TemplateToPCUIC.v:63`),
which is a function. -/
inductive TrS (venv : VEnv) (Us : List Name) : VLCtx → Expr → VExpr → Prop
  | bvar : Δ.find? (.inl i) = some (e, A) → TrS venv Us Δ (.bvar i) e
  | fvar : Δ.find? (.inr fv) = some (e, A) → TrS venv Us Δ (.fvar fv) e
  | sort : VLevel.ofLevel Us u = some u' → TrS venv Us Δ (.sort u) (.sort u')
  | const : venv.constants c = some ci → us.mapM (VLevel.ofLevel Us) = some us' →
      us.length = ci.uvars → TrS venv Us Δ (.const c us) (.const c us')
  | app : venv.HasType Us.length Δ.toCtx f' (.forallE A B) →
      venv.HasType Us.length Δ.toCtx a' A →
      TrS venv Us Δ f f' → TrS venv Us Δ a a' → TrS venv Us Δ (.app f a) (.app f' a')
  | lam : venv.IsType Us.length Δ.toCtx ty' → TrS venv Us Δ ty ty' →
      TrS venv Us ((none, .vlam ty') :: Δ) body body' →
      TrS venv Us Δ (.lam n ty body bi) (.lam ty' body')
  | forallE : venv.IsType Us.length Δ.toCtx ty' → venv.IsType Us.length (ty' :: Δ.toCtx) body' →
      TrS venv Us Δ ty ty' → TrS venv Us ((none, .vlam ty') :: Δ) body body' →
      TrS venv Us Δ (.forallE n ty body bi) (.forallE ty' body')
  | letE : venv.HasType Us.length Δ.toCtx val' ty' → TrS venv Us Δ ty ty' →
      TrS venv Us Δ val val' → TrS venv Us ((none, .vlet ty' val') :: Δ) body body' →
      TrS venv Us Δ (.letE n ty val body nd) body'
  | mdata : TrS venv Us Δ e e' → TrS venv Us Δ (.mdata d e) e'

section
variable {venv : VEnv}

/-- The translation is a function of the source term in a fixed context (no typing, no lean4lean
lemma). Reference: definitional for MetaRocq, whose Template→PCUIC `trans`
(`MR template-pcuic/theories/TemplateToPCUIC.v:63`) is a function. -/
theorem TrS.det (H1 : TrS venv Us Δ e e₁) (H2 : TrS venv Us Δ e e₂) : e₁ = e₂ := by
  induction H1 generalizing e₂ with
  | bvar h1 => cases H2 with | bvar h2 => rw [h1] at h2; cases h2; rfl
  | fvar h1 => cases H2 with | fvar h2 => rw [h1] at h2; cases h2; rfl
  | sort h1 => cases H2 with | sort h2 => rw [h1] at h2; cases h2; rfl
  | const _ h2 _ => cases H2 with | const _ h2' _ => rw [h2] at h2'; cases h2'; rfl
  | app _ _ _ _ ih1 ih2 => cases H2 with | app _ _ r1 r2 => rw [ih1 r1, ih2 r2]
  | lam _ _ _ ih1 ih2 => cases H2 with | lam _ r1 r2 => cases ih1 r1; rw [ih2 r2]
  | forallE _ _ _ _ ih1 ih2 => cases H2 with | forallE _ _ r1 r2 => cases ih1 r1; rw [ih2 r2]
  | letE _ _ _ _ ih1 ih2 ih3 =>
    cases H2 with | letE _ r1 r2 r3 => cases ih1 r1; cases ih2 r2; exact ih3 r3
  | mdata _ ih => cases H2 with | mdata r => exact ih r

/-- Scoping: the free variables of a translated term are in the context. Port of lean4lean
`TrExprS.fvarsIn` (`l4l Verify/Typing/Lemmas.lean:865`) without the `lit` and `proj` cases.
Reference: `subject_closed` (`MR pcuic/theories/Typing/PCUICClosedTyp.v:351`). -/
theorem TrS.fvarsIn (h : TrS venv Us Δ e e') : FVarsIn (· ∈ Δ.fvars) e := by
  induction h with
  | fvar h1 => exact VLCtx.find?_eq_some.1 ⟨_, h1⟩
  | sort h => exact ofLevel_hasMVar h
  | const _ h =>
    rw [List.mapM_eq_some] at h
    intro _ hl
    have ⟨_, _, h⟩ := h.forall_exists_l _ hl
    exact ofLevel_hasMVar h
  | bvar | mdata => trivial
  | app _ _ _ _ ih1 ih2
  | lam _ _ _ ih1 ih2
  | forallE _ _ _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | letE _ _ _ _ ih1 ih2 ih3 => exact ⟨ih1, ih2, ih3⟩

/-- The translation is monotone in the environment. Port of lean4lean `TrExprS.mono`
(`l4l Verify/Typing/Lemmas.lean:735`) without the `lit` and `proj` cases. Reference: global
weakening (`MR pcuic/theories/PCUICWeakeningEnv.v:295 weakening_env_declared_constant`). -/
theorem TrS.mono {venv' : VEnv} (hle : venv ≤ venv') (h : TrS venv Us Δ e e') :
    TrS venv' Us Δ e e' := by
  induction h with
  | bvar h1 => exact .bvar h1
  | fvar h1 => exact .fvar h1
  | sort h1 => exact .sort h1
  | const h1 h2 h3 => exact .const (hle.1 h1) h2 h3
  | app h1 h2 _ _ ih1 ih2 => exact .app (h1.mono hle) (h2.mono hle) ih1 ih2
  | lam h1 _ _ ih1 ih2 => exact .lam (h1.mono hle) ih1 ih2
  | forallE h1 h2 _ _ ih1 ih2 => exact .forallE (h1.mono hle) (h2.mono hle) ih1 ih2
  | letE h1 _ _ _ ih1 ih2 ih3 => exact .letE (h1.mono hle) ih1 ih2 ih3
  | mdata _ ih => exact .mdata ih

/-- In an ordered environment and a well-formed context, the image of a translation is
well-typed. Port of lean4lean `TrExprS.wf` (`l4l Verify/Typing/Lemmas.lean:899`) without the `lit`
and `proj` cases. Reference: none in MetaRocq (PCUIC typing is native). -/
theorem TrS.wf {Δ : VLCtx} (henv : venv.Ordered) (hΔ : VLCtx.WF venv Us.length Δ)
    (h : TrS venv Us Δ e e') : VExpr.WF venv Us.length Δ.toCtx e' := by
  induction h with
  | bvar h1 | fvar h1 => exact ⟨_, hΔ.find?_wf henv h1⟩
  | sort h1 => exact ⟨_, VEnv.HasType.sort (.of_ofLevel h1)⟩
  | const h1 h2 h3 =>
    exact ⟨_, VEnv.HasType.const h1 (.of_mapM_ofLevel h2)
      ((List.mapM_eq_some.1 h2).length_eq.symm.trans h3)⟩
  | app h1 h2 => exact ⟨_, h1.app h2⟩
  | lam h1 _ _ _ ih2 =>
    have ⟨_, h1'⟩ := h1
    have ⟨_, h2'⟩ := ih2 ⟨hΔ, nofun, h1⟩
    exact ⟨_, h1'.lam h2'⟩
  | forallE h1 h2 => have ⟨_, h1'⟩ := h1; have ⟨_, h2'⟩ := h2; exact ⟨_, h1'.forallE h2'⟩
  | letE h1 _ _ _ _ _ ih3 => exact ih3 ⟨hΔ, nofun, h1⟩
  | mdata _ ih => exact ih hΔ

end

end EraseProof
