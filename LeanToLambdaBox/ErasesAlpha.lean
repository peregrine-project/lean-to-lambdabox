import LeanToLambdaBox.Erases
import LeanToLambdaBox.Witness.SourceTable

/-!
# Erasure up to source α

`ReifiedDecl.Prepared` (`LeanToLambdaBox/Witness/SourceTable.lean:201`) pins a tabled body to
the value the code generator reads only up to `Witness.Expr.AlphaEq`: on equality the clause is
uninhabited wherever `Lean.Compiler.LCNF.inlineMatchers` fires. Every theorem that reads a
tabled body therefore owes a transport between the body a run of `Erasure.prepare_erasure`
produced and the body the table records.

MetaRocq owes none — `erases_constant_body` reads `cst_body cb`, the very term the global
environment holds (`../metarocq/erasure/theories/Extract.v:264`). The debt is this
development's, and it is what a reified table costs: no term denotes `Lean.Environment`.

Translation absorbs a source renaming outright, since `VExpr` carries no binder name, and so
does erasure, whose `lam` and `letE` arms bind the target name independently of the source's.
The λ□ image of an α-variant is the **same** term, so no α relation on `LBTerm` enters.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean Witness

/-! ## The source relation -/

/-- `Witness.Expr.AlphaEq` is reflexive. -/
theorem Witness.Expr.AlphaEq.refl : ∀ e : Expr, Expr.AlphaEq e e
  | .bvar _ => .bvar
  | .fvar _ => .fvar
  | .mvar _ => .mvar
  | .sort _ => .sort
  | .const _ _ => .const
  | .lit _ => .lit
  | .app f a => .app (Expr.AlphaEq.refl f) (Expr.AlphaEq.refl a)
  | .lam _ ty b _ => .lam (Expr.AlphaEq.refl ty) (Expr.AlphaEq.refl b)
  | .forallE _ ty b _ => .forallE (Expr.AlphaEq.refl ty) (Expr.AlphaEq.refl b)
  | .letE _ ty v b _ => .letE (Expr.AlphaEq.refl ty) (Expr.AlphaEq.refl v) (Expr.AlphaEq.refl b)
  | .proj _ _ e => .proj (Expr.AlphaEq.refl e)
  | .mdata _ e => .mdata (Expr.AlphaEq.refl e)

/-- `Witness.Expr.AlphaEq` is symmetric: each arm relates two nodes of one constructor, with
the binder names and the binder info free on both sides. -/
theorem Witness.Expr.AlphaEq.symm : ∀ {e e' : Expr}, Expr.AlphaEq e e' → Expr.AlphaEq e' e
  | _, _, .bvar => .bvar
  | _, _, .fvar => .fvar
  | _, _, .mvar => .mvar
  | _, _, .sort => .sort
  | _, _, .const => .const
  | _, _, .lit => .lit
  | _, _, .app h₁ h₂ => .app h₁.symm h₂.symm
  | _, _, .lam h₁ h₂ => .lam h₁.symm h₂.symm
  | _, _, .forallE h₁ h₂ => .forallE h₁.symm h₂.symm
  | _, _, .letE h₁ h₂ h₃ => .letE h₁.symm h₂.symm h₃.symm
  | _, _, .proj h => .proj h.symm
  | _, _, .mdata h => .mdata h.symm

/-! ## The two transports -/

/-- Translation to `VExpr` is α-blind: `VExpr` has no binder names, so an α-variant of the
source translates to the **same** target in the same local context. -/
theorem TrExprS.alpha {env : VEnv} {Us : List Name} {Δ : VLCtx} {e e' : Expr} {ve : VExpr}
    (h : TrExprS env Us Δ e ve) (hα : Expr.AlphaEq e e') : TrExprS env Us Δ e' ve := by
  induction h generalizing e' with
  | bvar hf => cases hα; exact .bvar hf
  | fvar hf => cases hα; exact .fvar hf
  | sort hu => cases hα; exact .sort hu
  | const hc hus hlen => cases hα; exact .const hc hus hlen
  | app hf' ha' _ _ ihf iha =>
    cases hα with | app h₁ h₂ => exact .app hf' ha' (ihf h₁) (iha h₂)
  | lam hty' _ _ ihty ihb =>
    cases hα with | lam h₁ h₂ => exact .lam hty' (ihty h₁) (ihb h₂)
  | forallE hty' hb' _ _ ihty ihb =>
    cases hα with | forallE h₁ h₂ => exact .forallE hty' hb' (ihty h₁) (ihb h₂)
  | letE hval' _ _ _ ihty ihv ihb =>
    cases hα with | letE h₁ h₂ h₃ => exact .letE hval' (ihty h₁) (ihv h₂) (ihb h₃)
  | lit hcl _ ih => cases hα; exact .lit hcl (ih (Expr.AlphaEq.refl _))
  | mdata _ ih => cases hα with | mdata h₁ => exact .mdata (ih h₁)
  | proj _ hpr ih => cases hα with | proj h₁ => exact .proj (ih h₁) hpr

/-- Erasure is α-blind on its source and lands in the same λ□ term. `lam` and `letE` bind the
target name independently of the source's and no other arm reads a binder name, so the image
needs no renaming; `box`, `lam` and `letE` carry their `TrExprS` premises across by
`TrExprS.alpha`. -/
theorem Erases.alpha {env : VEnv} {Us : List Name} {Δ : VLCtx} {e e' : Expr} {t : LBTerm}
    (h : Erases env Us Δ e t) (hα : Expr.AlphaEq e e') : Erases env Us Δ e' t := by
  induction h generalizing e' with
  | box htr her => exact .box (TrExprS.alpha htr hα) her
  | bvar hf => cases hα; exact .bvar hf
  | fvar hf => cases hα; exact .fvar hf
  | ctor hc hi => cases hα; exact .ctor hc hi
  | const hc ho => cases hα; exact .const hc ho
  | app _ _ ihf iha => cases hα with | app h₁ h₂ => exact .app (ihf h₁) (iha h₂)
  | lam hty _ ihb => cases hα with | lam h₁ h₂ => exact .lam (TrExprS.alpha hty h₁) (ihb h₂)
  | letE hty hval _ _ ihv ihb =>
    cases hα with
    | letE h₁ h₂ h₃ =>
      exact .letE (TrExprS.alpha hty h₁) (TrExprS.alpha hval h₂) (ihv h₂) (ihb h₃)
  | proj hs hinf hi _ ih => cases hα with | proj h₁ => exact .proj hs hinf hi (ih h₁)
  | lit hcl _ ih => cases hα; exact .lit hcl (ih (Expr.AlphaEq.refl _))
  | mdata _ ih => cases hα with | mdata h₁ => exact .mdata (ih h₁)

/-! ## The consumer -/

/-- A tabled body has exactly the erasures of the body the run visited: for the value the code
generator reads for `n`, every successful `Erasure.prepare_erasure` run under a configuration
with `csimp` off returns a body with the same λ□ images as `tbl.body? n`.

`SourceTableAdequate.body?_prepared`'s α clause spent through `Erases.alpha`. It is what lets
an environment clause — `ErasesEnv.defns`, `SpecContent.defns` — read the tabled body while the
run erased the prepared one. -/
theorem Witness.SourceTableAdequate.erases_prepared {lenv : Environment} {tbl : SourceTable}
    {n : Name} {b : Expr} (h : SourceTableAdequate lenv tbl) (hb : tbl.body? n = some b) :
    ∃ ci v, compilerInfo? lenv n = some ci ∧ ci.value? (allowOpaque := true) = some v ∧
      ∀ (s s' : Erasure.ErasureState) (ctx : Erasure.ErasureContext) (cctx : Core.Context)
        (ref : ST.Ref IO.RealWorld Core.State) (w w' : Void IO.RealWorld) (b' : Expr),
        ctx.config.csimp = false →
        Erasure.prepare_erasure v s ctx cctx ref w = .ok (b', s') w' →
        ∀ (env : VEnv) (Us : List Name) (Δ : VLCtx) (t : LBTerm),
          Erases env Us Δ b' t ↔ Erases env Us Δ b t := by
  obtain ⟨ci, v, hci, hv, hp⟩ := h.body?_prepared hb
  refine ⟨ci, v, hci, hv, fun s s' ctx cctx ref w w' b' hcs hrun _ _ _ _ => ?_⟩
  exact ⟨fun he => Erases.alpha he (hp s s' ctx cctx ref w w' b' hcs hrun),
    fun he => Erases.alpha he (hp s s' ctx cctx ref w w' b' hcs hrun).symm⟩

end LeanToLambdaBox
