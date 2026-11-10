import EraseProof.Typing.Basic

/-!
# Weakening of the translation

Inserting entries into the context of a `TrS` derivation lifts the image: free-variable entries
(`VLCtx.FVLift'`, `VLCtx.FVLift`) and de Bruijn entries (`VLCtx.BVLift`).
-/

open Lean Lean4Lean

namespace EraseProof

section
variable {venv : VEnv}

/-- Weakening over free-variable entries with a general lift: the image is lifted by
`n.consN k`. Port of lean4lean `TrExprS.weakFV'` (`l4l Verify/Typing/Lemmas.lean:649`) without
the `lit` and `proj` cases. Reference: none in MetaRocq, whose PCUIC contexts have no free-variable
entries. -/
theorem TrS.weakFV' (henv : venv.Ordered) (W : VLCtx.FVLift' Δ Δ' dk n k)
    (hΔ' : Δ'.WF venv Us.length) (H : TrS venv Us Δ e e') :
    TrS venv Us Δ' e (e'.lift' (n.consN k)) := by
  induction H generalizing Δ' dk k with
  | bvar h1 => exact .bvar (W.find? hΔ' h1)
  | fvar h1 => exact .fvar (W.find? hΔ' h1)
  | sort h1 => exact .sort h1
  | const h1 h2 h3 => exact .const h1 h2 h3
  | app h1 h2 _ _ ih1 ih2 =>
    exact .app (h1.weak' henv W.toCtx) (h2.weak' henv W.toCtx) (ih1 W hΔ') (ih2 W hΔ')
  | lam h1 _ _ ih1 ih2 =>
    have h1 := h1.weak' henv W.toCtx
    exact .lam h1 (ih1 W hΔ') (ih2 (W.cons_bvar _) ⟨hΔ', nofun, h1⟩)
  | forallE h1 h2 _ _ ih1 ih2 =>
    have h1 := h1.weak' henv W.toCtx
    have h2 := h2.weak' henv W.toCtx.cons
    exact .forallE h1 h2 (ih1 W hΔ') (ih2 (W.cons_bvar _) ⟨hΔ', nofun, h1⟩)
  | letE h1 _ _ _ ih1 ih2 ih3 =>
    have h1 := h1.weak' henv W.toCtx
    exact .letE h1 (ih1 W hΔ') (ih2 W hΔ') (ih3 (W.cons_bvar _) ⟨hΔ', nofun, h1⟩)
  | mdata _ ih => exact .mdata (ih W hΔ')

/-- Weakening over free-variable entries: inserting free-variable entries of total depth `n`
below the `k` innermost de Bruijn levels lifts the image by `liftN n k`, the source term
unchanged. Port of lean4lean `TrExprS.weakFV` (`l4l Verify/Typing/Lemmas.lean:679`) without the
`lit` and `proj` cases. Reference: none in MetaRocq, whose PCUIC contexts have no free-variable
entries. -/
theorem TrS.weakFV (henv : venv.Ordered) (W : VLCtx.FVLift Δ Δ' dk n k)
    (hΔ' : Δ'.WF venv Us.length) (h : TrS venv Us Δ e e') : TrS venv Us Δ' e (e'.liftN n k) := by
  simpa [VExpr.lift'_consN_skipN] using h.weakFV' henv W.toFVLift' hΔ'

/-- Weakening over de Bruijn entries: inserting `dn` de Bruijn entries (of total depth `n`) below
the `dk` innermost ones lifts the source by `liftLooseBVars' dk dn` and the image by `liftN n k`.
Port of lean4lean `TrExprS.weakBV` (`l4l Verify/Typing/Lemmas.lean:690`) without the `lit` and
`proj` cases. Reference: none in MetaRocq (PCUIC typing is native). -/
theorem TrS.weakBV (henv : venv.Ordered) (W : VLCtx.BVLift Δ Δ' dn dk n k)
    (h : TrS venv Us Δ e e') : TrS venv Us Δ' (e.liftLooseBVars' dk dn) (e'.liftN n k) := by
  induction h generalizing Δ' dk k with
  | bvar h1 => exact .bvar (W.find? h1)
  | fvar h1 => exact .fvar (W.find? h1)
  | sort h1 => exact .sort h1
  | const h1 h2 h3 => exact .const h1 h2 h3
  | app h1 h2 _ _ ih1 ih2 =>
    exact .app (h1.weakN henv W.toCtx) (h2.weakN henv W.toCtx) (ih1 W) (ih2 W)
  | lam h1 _ _ ih1 ih2 =>
    exact .lam (h1.weakN henv W.toCtx) (ih1 W) (ih2 (W.cons _))
  | forallE h1 h2 _ _ ih1 ih2 =>
    exact .forallE (h1.weakN henv W.toCtx) (h2.weakN henv W.toCtx.succ) (ih1 W) (ih2 (W.cons _))
  | letE h1 _ _ _ ih1 ih2 ih3 =>
    exact .letE (h1.weakN henv W.toCtx) (ih1 W) (ih2 W) (ih3 (W.cons _))
  | mdata _ ih => exact .mdata (ih W)

end

end EraseProof
