import EraseProof.Typing.Basic

/-!
# Uniqueness of the translation up to definitional equality

In a well-formed environment, two translations of one source term in definitionally equal contexts
are definitionally equal (`TrS.uniq`), and a translation in one context gives a translation in any
definitionally equal context (`TrS.defeqDFC`).
-/

open Lean Lean4Lean

namespace EraseProof

section
variable {venv : VEnv}

/-- Port of lean4lean `TrExprS.uniq` (`l4l Verify/Typing/Lemmas.lean:941`) without the `lit` and
`proj` cases: translations in definitionally equal contexts are definitionally equal. Reference:
none in MetaRocq (its translation is a function). -/
theorem TrS.uniq (henv : venv.WF) (hΔ : VLCtx.IsDefEq venv Us.length Δ₁ Δ₂)
    (H1 : TrS venv Us Δ₁ e e₁) (H2 : TrS venv Us Δ₂ e e₂) :
    venv.IsDefEqU Us.length Δ₁.toCtx e₁ e₂ := by
  induction H1 generalizing Δ₂ e₂ with
  | bvar l1 => let .bvar r1 := H2; exact ⟨_, (hΔ.find?_uniq henv l1 r1).2⟩
  | fvar l1 => let .fvar r1 := H2; exact ⟨_, (hΔ.find?_uniq henv l1 r1).2⟩
  | sort l1 =>
    let .sort r1 := H2; cases l1.symm.trans r1; exact ⟨_, VEnv.HasType.sort (.of_ofLevel l1)⟩
  | const l1 l2 l3 =>
    let .const r1 r2 r3 := H2; cases l1.symm.trans r1; cases l2.symm.trans r2
    exact (TrS.const l1 l2 l3).wf henv hΔ.wf
  | app l1 l2 _ _ ih3 ih4 =>
    let .app _ _ r3 r4 := H2
    exact ⟨_, .appDF
      (ih3 hΔ r3 |>.of_l henv hΔ.wf.toCtx l1)
      (ih4 hΔ r4 |>.of_l henv hΔ.wf.toCtx l2)⟩
  | lam l1 _ _ ih2 ih3 =>
    let ⟨_, l1⟩ := l1; let .lam _ r2 r3 := H2
    have hA := ih2 hΔ r2 |>.of_l henv hΔ.wf.toCtx l1
    have ⟨_, hb⟩ := ih3 (hΔ.cons nofun <| .vlam hA) r3
    exact ⟨_, .lamDF hA hb⟩
  | forallE l1 l2 _ _ ih3 ih4 =>
    let ⟨_, l1'⟩ := l1; let ⟨_, l2⟩ := l2; let .forallE _ _ r3 r4 := H2
    have hA := ih3 hΔ r3 |>.of_l henv hΔ.wf.toCtx l1'
    have hB := ih4 (hΔ.cons nofun <| .vlam hA) r4 |>.of_l (Γ := _::_) henv ⟨hΔ.wf.toCtx, l1⟩ l2
    exact ⟨_, .forallEDF hA hB⟩
  | letE l1 _ _ _ ih2 ih3 ih4 =>
    have hΓ := hΔ.wf.toCtx
    let .letE _ r2 r3 r4 := H2
    have ⟨_, hb⟩ := l1.isType henv hΓ
    refine ih4 (hΔ.cons nofun ?_) r4
    exact .vlet (ih3 hΔ r3 |>.of_l henv hΓ l1) (ih2 hΔ r2 |>.of_l henv hΓ hb)
  | mdata _ ih1 => let .mdata r1 := H2; exact ih1 hΔ r1

/-- Port of lean4lean `TrExprS.defeqDFC` (`l4l Verify/Typing/Lemmas.lean:985`, under `VEnv.WF`),
calling `TrS.uniq` where lean4lean calls `TrExprS.uniq`. Reference: none in MetaRocq (its
translation is a function); the PCUIC analogue is context conversion (MC p. 8:43). -/
theorem TrS.defeqDFC (henv : venv.WF) (hΔ : VLCtx.IsDefEq venv Us.length Δ₁ Δ₂)
    (H : TrS venv Us Δ₁ e e₁) : ∃ e₂, TrS venv Us Δ₂ e e₂ := by
  induction H generalizing Δ₂ with
  | bvar h1 => have ⟨_, _, h1⟩ := hΔ.find?_defeqDFC h1; exact ⟨_, .bvar h1⟩
  | fvar h1 => have ⟨_, _, h1⟩ := hΔ.find?_defeqDFC h1; exact ⟨_, .fvar h1⟩
  | sort h1 => exact ⟨_, .sort h1⟩
  | const h1 h2 h3 => exact ⟨_, .const h1 h2 h3⟩
  | app h1 h2 h3 h4 ih3 ih4 =>
    let ⟨_, h3'⟩ := ih3 hΔ
    let ⟨_, h4'⟩ := ih4 hΔ
    have h1 := h1.defeqDFC henv hΔ.defeqCtx
    have h2 := h2.defeqDFC henv hΔ.defeqCtx
    have h1 := h1.defeqU_l henv (hΔ.symm henv).wf (h3'.uniq henv (hΔ.symm henv) h3).symm
    have h2 := h2.defeqU_l henv (hΔ.symm henv).wf (h4'.uniq henv (hΔ.symm henv) h4).symm
    exact ⟨_, .app h1 h2 h3' h4'⟩
  | lam h1 h2 h3 ih2 ih3 =>
    let ⟨_, h1'⟩ := h1
    let ⟨_, h2'⟩ := ih2 hΔ
    have h1 := h1.defeqDFC henv hΔ.defeqCtx
    have h1 := h1.defeqU_l henv (hΔ.symm henv).wf (h2'.uniq henv (hΔ.symm henv) h2).symm
    have ht := (h2.uniq henv hΔ h2').of_l henv hΔ.wf h1'
    let ⟨_, h3'⟩ := ih3 (hΔ.cons nofun <| .vlam ht)
    exact ⟨_, .lam h1 h2' h3'⟩
  | forallE h1 h2 h3 h4 ih3 ih4 =>
    let ⟨_, h1'⟩ := h1
    let ⟨_, h2'⟩ := h2
    let ⟨_, h3'⟩ := ih3 hΔ
    have ht := (h3.uniq henv hΔ h3').of_l henv hΔ.wf h1'
    have hΔ' := hΔ.cons (ofv := none) nofun (.vlam ht)
    let ⟨_, h4'⟩ := ih4 hΔ'
    have h1 := h1.defeqDFC henv hΔ.defeqCtx
    have h2 := h2.defeqDFC henv (hΔ.defeqCtx.succ ht)
    have h1 := h1.defeqU_l henv (hΔ.symm henv).wf (h3'.uniq henv (hΔ.symm henv) h3).symm
    have h2 := h2.defeqU_l henv (hΔ'.symm henv).wf (h4'.uniq henv (hΔ'.symm henv) h4).symm
    exact ⟨_, .forallE h1 h2 h3' h4'⟩
  | letE h1 h2 h3 h4 ih2 ih3 ih4 =>
    let ⟨_, h2'⟩ := ih2 hΔ
    let ⟨_, h3'⟩ := ih3 hΔ
    have ⟨_, h0⟩ := h1.isType henv hΔ.wf
    have t0 := (h2.uniq henv hΔ h2').of_l henv hΔ.wf h0
    have t1 := (h3.uniq henv hΔ h3').of_l henv hΔ.wf h1
    have t2 := (h2'.uniq henv (hΔ.symm henv) h2).symm
    have t3 := (h3'.uniq henv (hΔ.symm henv) h3).symm
    have hΔ' := hΔ.cons (ofv := none) nofun (.vlet t1 t0)
    let ⟨_, h4'⟩ := ih4 hΔ'
    have h0 := h0.defeqDFC henv hΔ.defeqCtx
    have h0 := h0.defeqU_l henv (hΔ.symm henv).wf t2
    have h1 := h1.defeqDFC henv hΔ.defeqCtx
    have h1 := h1.defeqU_l henv (hΔ.symm henv).wf t3
    have h1 := h1.defeqU_r henv (hΔ.symm henv).wf t2
    exact ⟨_, .letE h1 h2' h3' h4'⟩
  | mdata _ ih1 => let ⟨_, h1⟩ := ih1 hΔ; exact ⟨_, .mdata h1⟩

end

end EraseProof
