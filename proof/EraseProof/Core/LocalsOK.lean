import EraseProof.Oracle.Sound
import EraseProof.Source.Defeq

/-!
# The traversal's locals under its binders

The traversal opens binders with fresh free variables (`withLocalDecl`, `withLocalDef`,
`LeanToLambdaBox/Erasure.lean:539,545`) and pushes a local for each. `LocalsOK` (the locals are
the Lean form of the Metalean context) survives both pushes: a λ/Π-bound local denotes the new
last Metalean variable, of the translated domain (`LocalsOK.pushFVar`); a `let`-bound local
denotes the translated value, in the same Metalean context (`LocalsOK.pushLet`). The binders that
the traversal opens through a type in weak-head normal form (`forallMonocular`) have a
translated domain that is a type, and a translated body under it (`Pure.whnf_forallE`).
-/

open Lean Erasure
open Metalean (Defeq TypeEq)

namespace EraseProof

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {lps : List Name}

/-- A free variable that the locals do not know is not the variable of a local they know. -/
theorem MLCtx.findF_ne {ℓ n : Nat} {Δ : MLCtx ζ ℓ n} {x y : FVarId}
    {t : Metalean.Expr ζ ℓ n} (hx : Δ.findF x = none) (hy : Δ.findF y = some t) :
    (x == y) = false := by
  rcases Bool.eq_false_or_eq_true (x == y) with h | h
  · cases (fvarId_beq_iff x y).mp h; rw [hx] at hy; cases hy
  · exact h

/-- Pushing the local of a λ/Π binder (`withLocalDecl`): its free variable `x`, fresh for the
locals, denotes the new last variable of the context, whose type `A'` translates the local's
type. Reference: the extension of `wf_local` by a `vass` (`MR P/PCUICTyping.v`); DV-13. -/
theorem LocalsOK.pushFVar {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
    {Δ : MLCtx ζ lps.length n} {ls : List Local} {x : FVarId} {nm : Name} {A : Expr}
    {A' : Metalean.Expr ζ lps.length n} (hloc : LocalsOK E B lps Γ Δ ls)
    (hx : Δ.findF x = none) (hA : TrM E B lps Γ Δ A A') (hA' : E[Γ] ⊢ A' typ)
    (hΓ : E[Γ] ⊢ ok) :
    LocalsOK E B lps (Γ.snoc A') (Δ.pushLam (some x)) (⟨x, nm, A, none⟩ :: ls) := by
  have hΓ' : E[Γ.snoc A'] ⊢ ok := .snoc hΓ hA'
  intro l hl
  rcases List.mem_cons.1 hl with rfl | hl
  · refine ⟨A'.wk, .var (Fin.last n), TrM.weakFV hx hA, ?_, ?_, fun v hv => nomatch hv⟩
    · simp [MLCtx.pushLam, MLCtx.findF, (fvarId_beq_iff x x).mpr rfl, MLDecl.denote]
    · simpa using hΓ'.var (Fin.last n)
  · obtain ⟨T, t, hT, hF, ht, hv⟩ := hloc l hl
    refine ⟨T.wk, t.wk, TrM.weakFV hx hT, ?_, ht.wk A', fun v h => TrM.weakFV hx (hv v h)⟩
    simp [MLCtx.pushLam, MLCtx.findF, MLCtx.findF_map_wk, MLCtx.findF_ne hx hF, hF]

/-- Pushing the local of a `let` binder (`withLocalDef`): its free variable `x`, fresh for the
locals, denotes the translated value `v'`, which has the translated type `T'`; the context does
not grow. Reference: the extension of `wf_local` by a `vdef` (`MR P/PCUICTyping.v`); DV-13. -/
theorem LocalsOK.pushLet {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
    {Δ : MLCtx ζ lps.length n} {ls : List Local} {x : FVarId} {nm : Name} {T v : Expr}
    {T' v' : Metalean.Expr ζ lps.length n} (hloc : LocalsOK E B lps Γ Δ ls)
    (hx : Δ.findF x = none) (hT : TrM E B lps Γ Δ T T') (hv : TrM E B lps Γ Δ v v')
    (hvT : E[Γ] ⊢ v' : T') :
    LocalsOK E B lps Γ ((some x, .vlet v') :: Δ) (⟨x, nm, T, some v⟩ :: ls) := by
  intro l hl
  rcases List.mem_cons.1 hl with rfl | hl
  · refine ⟨T', v', TrM.weakFV_let hx hT, ?_, hvT, fun w hw => ?_⟩
    · simp [MLCtx.findF, (fvarId_beq_iff x x).mpr rfl, MLDecl.denote]
    · cases hw; exact TrM.weakFV_let hx hv
  · obtain ⟨T₀, t, hT₀, hF, ht, hv₀⟩ := hloc l hl
    refine ⟨T₀, t, TrM.weakFV_let hx hT₀, ?_, ht, fun w h => TrM.weakFV_let hx (hv₀ w h)⟩
    simp [MLCtx.findF, MLCtx.findF_ne hx hF, hF]

end

open OracleWhnf in
/-- The oracle's weak-head reduction of a translated type onto a `Π` (`forallMonocular`,
`LeanToLambdaBox/Erasure.lean:578`): the domain translates to a type `A'`, the body translates
under the binder, and the type is convertible to the translated `Π`. Reference: `hnf_sound`
(`MR S/PCUICSafeReduce.v:1841`) with the inversion of `tProd` (`MR P/PCUICInversion.v`). -/
theorem Pure.whnf_forallE {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ}
    {P : List ConstantInfo} {lps : List Name} {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
    {Δ : MLCtx ζ lps.length n} {cx : Pure.Ctx} {fuel : Nat} {ls : List Local} {T A b : Expr}
    {x : Name} {bi : BinderInfo} {T' : Metalean.Expr ζ lps.length n}
    (henv : ProgEnv P ζ E B) (hE : Metalean.EnvWF E) (hsub : SubEnv cx.decls P)
    (hΓ : E[Γ] ⊢ ok) (hloc : LocalsOK E B lps Γ Δ ls) (hT : TrM E B lps Γ Δ T T')
    (hty : E[Γ] ⊢ T' typ) (h : Pure.whnf cx fuel ls T = .ok (.forallE x A b bi)) :
    ∃ A' B', TrM E B lps Γ Δ A A' ∧ TrM E B lps (Γ.snoc A') (Δ.pushLam none) b B' ∧
      E[Γ] ⊢ A' typ ∧ E[Γ] ⊢ T' ≡ .forallE A' B' typ := by
  obtain ⟨l, hl⟩ := hty
  obtain ⟨w', hw, hd⟩ := Pure.whnf_sound henv hE hsub hΓ hloc hT hl h
  obtain ⟨A', B', rfl, hA, hB⟩ := SrcDefeq.trM_forallE_inv hw
  have hpi : E[Γ] ⊢ T' ≡ .forallE A' B' typ := .ofDefEq hd
  obtain ⟨_, hpt⟩ := hpi.right
  exact ⟨A', B', hA, hB, (Metalean.Defeq.forallE_inv hpt).1, hpi⟩

end EraseProof
