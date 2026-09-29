import EraseProof.Typing.Weak

/-!
# Substitution into the translation

Instantiating the de Bruijn variable of a `λ`-bound entry by a translated term substitutes its
image into the image (`TrS.instN`, `TrS.inst`), and instantiating the variable of a `let`-bound
entry by the translation of its value leaves the image unchanged (`TrS.instN_let`,
`TrS.inst_let`). The context shapes are lean4lean's `VLCtx.InstN` and `VLCtx.InstLet`
(`l4l Verify/Typing/Lemmas.lean:511,540`).
-/

open Lean Lean4Lean

namespace EraseProof

section
variable {venv : VEnv}

/-- The variable case of `TrS.instN`: a variable found in `Δ₁` translates, after instantiation,
to its image instantiated at depth `k`. Port of lean4lean `TrExprS.instN_var`
(`l4l Verify/Typing/Lemmas.lean:1194`). Reference: none in MetaRocq (PCUIC typing is native). -/
theorem TrS.instN_var (henv : venv.Ordered) (h₀ : TrS venv Us Δ₀ e₀ e₀')
    (W : VLCtx.InstN Δ₀ e₀' A₀ dk k Δ₁ Δ) (H : Δ₁.find? v = some (e', A)) :
    TrS venv Us Δ (Expr.instantiate1' (VLCtx.varToExpr v) e₀ dk) (e'.inst e₀' k) := by
  induction W generalizing v e' A with
  | zero =>
    obtain (_|i)|fv := v <;> simp [VLCtx.varToExpr, Expr.instantiate1', Expr.liftLooseBVars_zero]
    · cases H; simp [VLocalDecl.value, VExpr.inst]; exact h₀
    · simp [VLCtx.find?, VLCtx.next] at H
      obtain ⟨e, A, H, rfl, rfl⟩ := H
      simp [VLocalDecl.depth, VExpr.inst_liftN]
      exact .bvar H
    · simp [VLCtx.find?, VLCtx.next] at H
      obtain ⟨e, A, H, rfl, rfl⟩ := H
      simp [VLocalDecl.depth, VExpr.inst_liftN]
      exact .fvar H
  | @succ _ k _ _ d _ ih =>
    obtain (_|i)|fv := v <;> simp [VLCtx.varToExpr, Expr.instantiate1']
    · cases H
      cases d <;> exact .bvar <| by simp [VLocalDecl.value, VExpr.inst, VLocalDecl.depth]; rfl
    · simp [VLCtx.find?, VLCtx.next] at H
      obtain ⟨e, A, H, rfl, rfl⟩ := H
      have := ih H; revert this
      simp [VLCtx.varToExpr, Expr.instantiate1']; split <;> [skip; split]
      · intro | .bvar h => ?_
        exact .bvar <| by
          simp [VLCtx.find?, VLCtx.next]
          refine ⟨_, _, h, ?_, rfl⟩
          cases d <;> simp [VLocalDecl.depth, VLocalDecl.inst, VExpr.lift_instN_lo]
      · intro H
        have := Expr.liftLooseBVars_add ▸ H.weakBV henv (.skip (d.inst e₀' k) .refl)
        cases d <;> simpa [← VExpr.lift_instN_lo, VExpr.liftN_zero,
          VLocalDecl.inst, VLocalDecl.depth] using this
      · obtain _|i := i; · omega
        intro | .bvar h => ?_
        exact .bvar <| by
          simp [VLCtx.find?, VLCtx.next]
          refine ⟨_, _, h, ?_, rfl⟩
          cases d <;> simp [VLocalDecl.depth, VLocalDecl.inst, VExpr.lift_instN_lo]
    · simp [VLCtx.find?, VLCtx.next] at H
      obtain ⟨e, A, H, rfl, rfl⟩ := H
      have .fvar h := ih H
      exact .fvar <| by
        simp [VLCtx.find?, VLCtx.next]
        refine ⟨_, _, h, ?_, rfl⟩
        cases d <;> simp [VLocalDecl.depth, VLocalDecl.inst, VExpr.lift_instN_lo]

/-- Substitution under binders: instantiating the de Bruijn variable at depth `dk` of a `λ`-bound
entry (`VLCtx.InstN`) by a translated term `e₀` translates to the image instantiated by `e₀'` at
depth `k`. Port of lean4lean `TrExprS.instN` (`l4l Verify/Typing/Lemmas.lean:1244`) without the
`lit` and `proj` cases. Reference: none in MetaRocq (PCUIC typing is native). -/
theorem TrS.instN (henv : venv.Ordered) (h₀ : TrS venv Us Δ₀ e₀ e₀')
    (t₀ : venv.HasType Us.length Δ₀.toCtx e₀' A₀)
    (W : VLCtx.InstN Δ₀ e₀' A₀ dk k Δ₁ Δ) (H : TrS venv Us Δ₁ e e') :
    TrS venv Us Δ (Expr.instantiate1' e e₀ dk) (e'.inst e₀' k) := by
  induction H generalizing Δ dk k with
  | bvar h1 | fvar h1 => exact instN_var henv h₀ W h1
  | sort h1 => exact .sort h1
  | const h1 h2 h3 => exact .const h1 h2 h3
  | app h1 h2 _ _ ih1 ih2 =>
    exact .app (h1.instN henv W.toCtx t₀) (h2.instN henv W.toCtx t₀) (ih1 W) (ih2 W)
  | lam h1 _ _ ih1 ih2 =>
    exact .lam (h1.instN henv W.toCtx t₀) (ih1 W) (ih2 (W.succ (d := .vlam _)))
  | forallE h1 h2 _ _ ih1 ih2 =>
    exact .forallE (h1.instN henv W.toCtx t₀) (h2.instN henv W.toCtx.succ t₀)
      (ih1 W) (ih2 (W.succ (d := .vlam _)))
  | letE h1 _ _ _ ih1 ih2 ih3 =>
    exact .letE (h1.instN henv W.toCtx t₀) (ih1 W) (ih2 W) (ih3 (W.succ (d := .vlet ..)))
  | mdata _ ih => exact .mdata (ih W)

/-- Substitution for the innermost `λ`-bound entry: if `b` translates to `b'` under a `λ`-entry of
type `A` and `a` translates to `a'` of type `A`, then `b.instantiate1' a` translates to
`b'.inst a'`. Port of lean4lean `TrExprS.inst` (`l4l Verify/Typing/Lemmas.lean:1265`). Reference:
none in MetaRocq (PCUIC typing is native). -/
theorem TrS.inst {Δ : VLCtx} (henv : venv.Ordered) (t₀ : venv.HasType Us.length Δ.toCtx a' A)
    (H : TrS venv Us ((none, .vlam A) :: Δ) b b') (h₀ : TrS venv Us Δ a a') :
    TrS venv Us Δ (b.instantiate1' a) (b'.inst a') :=
  h₀.instN henv t₀ .zero H

/-- The variable case of `TrS.instN_let`: a variable found in `Δ₁` translates, after
instantiation, to its unchanged image. Port of lean4lean `TrExprS.instN_let_var`
(`l4l Verify/Typing/Lemmas.lean:1288`). Reference: none in MetaRocq (PCUIC typing is native). -/
theorem TrS.instN_let_var (henv : venv.Ordered) (h₀ : TrS venv Us Δ₀ e₀ e₀')
    (W : VLCtx.InstLet Δ₀ e₀' A₀ dk k Δ₁ Δ) (H : Δ₁.find? v = some (e', A)) :
    TrS venv Us Δ (Expr.instantiate1' (VLCtx.varToExpr v) e₀ dk) e' := by
  induction W generalizing v e' A with
  | zero =>
    obtain (_|i)|fv := v <;> simp [VLCtx.varToExpr, Expr.instantiate1', Expr.liftLooseBVars_zero]
    · cases H; simp [VLocalDecl.value]; exact h₀
    · simp [VLCtx.find?, VLCtx.next] at H
      obtain ⟨e, A, H, rfl, rfl⟩ := H
      simp [VLocalDecl.depth]
      exact .bvar H
    · simp [VLCtx.find?, VLCtx.next] at H
      obtain ⟨e, A, H, rfl, rfl⟩ := H
      simp [VLocalDecl.depth]
      exact .fvar H
  | @succ _ k _ _ d _ ih =>
    obtain (_|i)|fv := v <;> simp [VLCtx.varToExpr, Expr.instantiate1']
    · cases H
      cases d <;> exact .bvar <| by simp [VLocalDecl.value]; rfl
    · simp [VLCtx.find?, VLCtx.next] at H
      obtain ⟨e, A, H, rfl, rfl⟩ := H
      have := ih H; revert this
      simp [VLCtx.varToExpr, Expr.instantiate1']; split <;> [skip; split]
      · intro | .bvar h => ?_
        exact .bvar <| by
          simp [VLCtx.find?, VLCtx.next]
          refine ⟨_, _, h, ?_, rfl⟩
          cases d <;> simp [VLocalDecl.depth]
      · intro H
        have := Expr.liftLooseBVars_add ▸ H.weakBV henv (.skip d .refl)
        cases d <;> simpa [VLocalDecl.depth] using this
      · obtain _|i := i; · omega
        intro | .bvar h => ?_
        exact .bvar <| by
          simp [VLCtx.find?, VLCtx.next]
          refine ⟨_, _, h, ?_, rfl⟩
          cases d <;> simp [VLocalDecl.depth]
    · simp [VLCtx.find?, VLCtx.next] at H
      obtain ⟨e, A, H, rfl, rfl⟩ := H
      have .fvar h := ih H
      exact .fvar <| by
        simp [VLCtx.find?, VLCtx.next]
        refine ⟨_, _, h, ?_, rfl⟩
        cases d <;> simp [VLocalDecl.depth]

/-- Substitution of a `let` value under binders: instantiating the de Bruijn variable at depth
`dk` of a `let`-bound entry (`VLCtx.InstLet`) by the translated value leaves the image unchanged.
Port of lean4lean `TrExprS.instN_let` (`l4l Verify/Typing/Lemmas.lean:1334`) without the `lit`
and `proj` cases. Reference: none in MetaRocq (PCUIC typing is native). -/
theorem TrS.instN_let (henv : venv.Ordered) (h₀ : TrS venv Us Δ₀ e₀ e₀')
    (W : VLCtx.InstLet Δ₀ e₀' A₀ dk k Δ₁ Δ) (H : TrS venv Us Δ₁ e e') :
    TrS venv Us Δ (Expr.instantiate1' e e₀ dk) e' := by
  induction H generalizing Δ dk k with
  | bvar h1 | fvar h1 => exact instN_let_var henv h₀ W h1
  | sort h1 => exact .sort h1
  | const h1 h2 h3 => exact .const h1 h2 h3
  | app h1 h2 _ _ ih1 ih2 =>
    exact .app (W.toCtx ▸ h1) (W.toCtx ▸ h2) (ih1 W) (ih2 W)
  | lam h1 _ _ ih1 ih2 =>
    exact .lam (W.toCtx ▸ h1) (ih1 W) (ih2 (W.succ (d := .vlam _)))
  | forallE h1 h2 _ _ ih1 ih2 =>
    exact .forallE (W.toCtx ▸ h1) (W.toCtx ▸ h2)
      (ih1 W) (ih2 (W.succ (d := .vlam _)))
  | letE h1 _ _ _ ih1 ih2 ih3 =>
    exact .letE (W.toCtx ▸ h1) (ih1 W) (ih2 W) (ih3 (W.succ (d := .vlet ..)))
  | mdata _ ih => exact .mdata (ih W)

/-- ζ-substitution for the innermost `let`-bound entry: if `b` translates to `b'` under a
`let`-entry of value `v'` and `v` translates to `v'`, then `b.instantiate1' v` translates to the
same `b'`. Port of lean4lean `TrExprS.inst_let` (`l4l Verify/Typing/Lemmas.lean:1355`).
Reference: none in MetaRocq (PCUIC typing is native). -/
theorem TrS.inst_let (henv : venv.Ordered)
    (H : TrS venv Us ((none, .vlet A v') :: Δ) b b') (h₀ : TrS venv Us Δ v v') :
    TrS venv Us Δ (b.instantiate1' v) b' :=
  h₀.instN_let henv .zero H

end

end EraseProof
