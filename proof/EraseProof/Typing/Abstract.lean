import EraseProof.Typing.Inst

/-!
# Abstraction and instantiation of free-variable entries

Closing a free variable of the source term into a de Bruijn variable turns its free-variable entry
of the context into a de Bruijn entry (`TrS.abstract`, `TrS.uninstantiateN`, over lean4lean's
`VLCtx.Abstract`, `l4l Verify/Typing/Lemmas.lean:562`), and conversely opening a de Bruijn entry
with a fresh free variable keeps the image (`TrS.inst_fvar`).
-/

open Lean Lean4Lean

namespace EraseProof

section
variable {venv : VEnv}

/-- Abstraction: abstracting the free variable `x` of an entry at depth `dk` into a de Bruijn
variable keeps the image. Port of lean4lean `TrExprS.abstract`
(`l4l Verify/Typing/Lemmas.lean:1627`) without the `lit` and `proj` cases. Reference: none in
MetaRocq, whose PCUIC contexts have no free-variable entries. -/
theorem TrS.abstract (W : VLCtx.Abstract Δ₀ x d₀ dk k Δ₁ Δ) (H : TrS venv Us Δ₁ e e') :
    TrS venv Us Δ (e.abstract1 x dk) e' := by
  induction H generalizing dk k Δ with
  | bvar h1 =>
    exact .bvar <| (W.find? (by nofun)).trans <| by
      simp; split <;> [skip; rw [if_neg (by omega), if_neg (by omega)]] <;> exact h1
  | @fvar _ _ _ fv h1 =>
    if h : fv = x then
      rw [h, W.find?_self] at h1; cases h1
      rw [Expr.abstract1, if_pos (by simp [h])]
      exact .bvar <| (W.find? (by nofun)).trans (by simpa using W.find?_self)
    else
      have := W.find? (v := .inr fv) (by rintro ⟨⟩; trivial)
      simp at this
      rw [Expr.abstract1, if_neg]
      · exact .fvar (this.trans h1)
      · simp; rintro rfl; trivial
  | sort h1 => exact .sort h1
  | const h1 h2 h3 => exact .const h1 h2 h3
  | app h1 h2 _ _ ih1 ih2 => exact .app (W.toCtx ▸ h1) (W.toCtx ▸ h2) (ih1 W) (ih2 W)
  | lam h1 _ _ ih1 ih2 => exact .lam (W.toCtx ▸ h1) (ih1 W) (ih2 W.succ)
  | forallE h1 h2 _ _ ih1 ih2 =>
    exact .forallE (W.toCtx ▸ h1) (W.toCtx ▸ h2) (ih1 W) (ih2 W.succ)
  | letE h1 _ _ _ ih1 ih2 ih3 =>
    exact .letE (W.toCtx ▸ h1) (ih1 W) (ih2 W) (ih3 W.succ)
  | mdata _ ih => exact .mdata (ih W)

/-- Uninstantiation: if `e` opened at depth `dk` with a free variable `x` it does not mention
translates under the free-variable entry of `x`, then `e` translates to the same image under the
de Bruijn entry that `VLCtx.Abstract` puts in its place. Port of lean4lean
`TrExprS.uninstantiateN` (`l4l Verify/Typing/Lemmas.lean:2132`). Reference: none in MetaRocq,
whose PCUIC contexts have no free-variable entries. -/
theorem TrS.uninstantiateN (W : VLCtx.Abstract Δ₀ x d₀ dk k Δ₁ Δ)
    (H : TrS venv Us Δ₁ (e.instantiate1' (.fvar x) dk) e') (sc : FVarsIn (· ≠ x) e) :
    TrS venv Us Δ e e' := by
  have := H.abstract W
  rwa [sc.abstract_instantiate1] at this

/-- Instantiation with a free variable: if `e` translates under the de Bruijn entry `d`, then `e`
opened with the free variable `x` translates to the same image under the free-variable entry of
`x` with the same declaration `d`. Port of lean4lean `TrExprS.inst_fvar`
(`l4l Verify/Typing/Lemmas.lean:2157`). Reference: none in MetaRocq, whose PCUIC contexts have no
free-variable entries. -/
theorem TrS.inst_fvar {Δ : VLCtx} (henv : venv.Ordered)
    (hΔ : VLCtx.WF venv Us.length ((some (x, deps), d) :: Δ))
    (H : TrS venv Us ((none, d) :: Δ) e e') :
    TrS venv Us ((some (x, deps), d) :: Δ) (e.instantiate1' (.fvar x)) e' := by
  refine
    have W := .skip_fvar (x, deps) d .refl
    have := H.weakFV henv (.cons_bvar _ W) ⟨hΔ, nofun, hΔ.2.2.weakN henv W.toCtx⟩
    ?_
  have hf := TrS.fvar (venv := venv) (Us := Us) (fv := x) (Δ := (some (x, deps), d) :: Δ) <| by
    simp [VLCtx.find?, VLCtx.next]; exact ⟨rfl, rfl⟩
  match d with
  | .vlam A₀ =>
    have := this.inst henv (.bvar .zero) (Δ := (some (x, deps), .vlam _) :: Δ) hf
    rwa [VLocalDecl.depth, VExpr.instN_bvar0] at this
  | .vlet A₀ e₀ =>
    simp [VLocalDecl.depth, VLocalDecl.liftN] at this
    exact this.inst_let henv hf

end

end EraseProof
