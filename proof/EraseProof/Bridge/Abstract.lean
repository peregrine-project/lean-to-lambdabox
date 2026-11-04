import EraseProof.Bridge.Basic

/-!
# Closing a binder in the translation

`TrM.uninstantiateN`: the converse of `TrM.inst_fvar`. A body opened with a fresh free variable `x`
translates under the locals where `x` denotes the binder's variable; the body itself translates
to the same Metalean term under the locals where the binder is a bound variable. The proof goes
through the abstraction `AbsFV.absFV x d` (`x` becomes the bound variable `d`), which inverts the
instantiation by `x` on terms that do not mention `x`, and through the relation `AbsFV.Rel` of
the two lists of locals. Reference: lean4lean `TrExprS.uninstantiateN`
(`L4 Typing/Abstract.lean:55`), DV-13.
-/

open Lean Erasure

namespace EraseProof

namespace AbsFV

/-- `x` becomes the bound variable `d` (under binders, `d` plus their number); loose indices from
`d` on move up by one. The inverse of `instantiate1' (.fvar x) d` (`absFV_inst`). -/
def absFV (x : FVarId) : Nat → Expr → Expr
  | d, .bvar i => .bvar (if i < d then i else i + 1)
  | d, .fvar y => if y == x then .bvar d else .fvar y
  | d, .app f a => .app (absFV x d f) (absFV x d a)
  | d, .lam n t b bi => .lam n (absFV x d t) (absFV x (d + 1) b) bi
  | d, .forallE n t b bi => .forallE n (absFV x d t) (absFV x (d + 1) b) bi
  | d, .letE n t v b nd => .letE n (absFV x d t) (absFV x d v) (absFV x (d + 1) b) nd
  | d, .mdata m e => .mdata m (absFV x d e)
  | d, .proj s i e => .proj s i (absFV x d e)
  | _, e => e

theorem absFV_inst {x : FVarId} : ∀ {b : Expr} {d : Nat}, FVarsIn (· ≠ x) b →
    absFV x d (b.instantiate1' (.fvar x) d) = b
  | .bvar i, d, _ => by
    simp only [Expr.instantiate1']
    split_ifs with h₁ h₂
    · simp [absFV, h₁]
    · subst h₂; simp [Expr.liftLooseBVars', absFV, (fvarId_beq_iff x x).mpr rfl]
    · simp only [absFV]; congr 1; split_ifs <;> omega
  | .fvar y, d, h => by
    have hy : (y == x) = false := by
      rcases Bool.eq_false_or_eq_true (y == x) with h' | h'
      · exact absurd ((fvarId_beq_iff y x).mp h') h
      · exact h'
    simp [Expr.instantiate1', absFV, hy]
  | .app f a, d, h => by simp [Expr.instantiate1', absFV, absFV_inst h.1, absFV_inst h.2]
  | .lam _ t b _, d, h => by simp [Expr.instantiate1', absFV, absFV_inst h.1, absFV_inst h.2]
  | .forallE _ t b _, d, h => by simp [Expr.instantiate1', absFV, absFV_inst h.1, absFV_inst h.2]
  | .letE _ t v b _, d, h => by
    simp [Expr.instantiate1', absFV, absFV_inst h.1, absFV_inst h.2.1, absFV_inst h.2.2]
  | .mdata _ e, d, h => by simp [Expr.instantiate1', absFV, absFV_inst (b := e) h]
  | .proj _ _ e, d, h => by simp [Expr.instantiate1', absFV, absFV_inst (b := e) h]
  | .sort _, _, _ | .const .., _, _ | .lit _, _, _ | .mvar _, _, _ => rfl

theorem absFV_foldl (x : FVarId) (d : Nat) (f : Expr) (as : List Expr) :
    absFV x d (as.foldl .app f) = (as.map (absFV x d)).foldl .app (absFV x d f) := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih => simp [ih, absFV]

theorem absFV_getAppFn (x : FVarId) (d : Nat) (f : Expr) :
    (absFV x d f).getAppFn = absFV x d f.getAppFn := by
  induction f generalizing d with
  | app f a ih => simpa [absFV, Expr.getAppFn] using ih d
  | bvar i => simp [absFV, Expr.getAppFn]
  | fvar y => simp only [absFV, Expr.getAppFn]; split <;> rfl
  | _ => simp [absFV, Expr.getAppFn]

theorem absFV_eq_const {x : FVarId} {d : Nat} {g : Expr} {c : Name} {us : List Level}
    (h : absFV x d g = .const c us) : g = .const c us := by
  cases g with
  | fvar y => simp only [absFV] at h; split at h <;> cases h
  | _ => simp only [absFV] at h; first | exact h | cases h

section
variable {ζ : Metalean.Sigs} {ℓ n : Nat}

/-- The locals with `x` (`Δ₂`) and with the bound variable `d` in its place (`Δ₁`). -/
def Rel (x : FVarId) (d : Nat) (Δ₂ Δ₁ : MLCtx ζ ℓ n) : Prop :=
  (∀ i t, Δ₂.findB i = some t → Δ₁.findB (if i < d then i else i + 1) = some t) ∧
  ∀ y t, Δ₂.findF y = some t →
    (if y == x then Δ₁.findB d = some t else Δ₁.findF y = some t)

theorem Rel.zero (x : FVarId) (Δ : MLCtx ζ ℓ n) :
    Rel x 0 (Δ.pushLam (some x)) (Δ.pushLam none) := by
  constructor
  · intro i t ht
    simpa [MLCtx.pushLam, MLCtx.findB] using ht
  · intro y t ht
    simp only [MLCtx.pushLam, MLCtx.findF] at ht
    by_cases hy : (y == x) = true
    · have hxy : (x == y) = true := (fvarId_beq_iff x y).mpr ((fvarId_beq_iff y x).mp hy).symm
      simp only [hxy, ↓reduceIte, Option.some.injEq] at ht
      subst ht
      simp only [hy, ↓reduceIte]
      rfl
    · have hxy : (x == y) = false := by
        rcases Bool.eq_false_or_eq_true (x == y) with h' | h'
        · exact absurd ((fvarId_beq_iff y x).mpr ((fvarId_beq_iff x y).mp h').symm) hy
        · exact h'
      simp only [hxy, Bool.false_eq_true, ↓reduceIte] at ht
      simp only [hy, MLCtx.pushLam, MLCtx.findF]
      exact ht

theorem Rel.pushLam {x : FVarId} {d : Nat} {Δ₂ Δ₁ : MLCtx ζ ℓ n} (h : Rel x d Δ₂ Δ₁) :
    Rel x (d + 1) (Δ₂.pushLam none) (Δ₁.pushLam none) := by
  constructor
  · intro i t ht
    cases i with
    | zero => simpa [MLCtx.pushLam, MLCtx.findB] using ht
    | succ i =>
      simp only [MLCtx.pushLam, MLCtx.findB, MLCtx.findB_map_wk, Option.map_eq_some_iff] at ht
      obtain ⟨u, hu, rfl⟩ := ht
      have hu' := h.1 i u hu
      have hidx : (if i + 1 < d + 1 then i + 1 else i + 1 + 1) =
          (if i < d then i else i + 1) + 1 := by split_ifs <;> omega
      rw [hidx]
      simp [MLCtx.pushLam, MLCtx.findB, MLCtx.findB_map_wk, hu']
  · intro y t ht
    simp only [MLCtx.pushLam, MLCtx.findF, MLCtx.findF_map_wk, Option.map_eq_some_iff] at ht
    obtain ⟨u, hu, rfl⟩ := ht
    have hu' := h.2 y u hu
    split at hu' <;> rename_i hy
    · simp only [hy, ↓reduceIte]; simp [MLCtx.pushLam, MLCtx.findB, MLCtx.findB_map_wk, hu']
    · simp only [hy]; simp [MLCtx.pushLam, MLCtx.findF, MLCtx.findF_map_wk, hu']

theorem Rel.cons {x : FVarId} {d : Nat} {Δ₂ Δ₁ : MLCtx ζ ℓ n} (h : Rel x d Δ₂ Δ₁)
    (v : MLDecl ζ ℓ n) : Rel x (d + 1) ((none, v) :: Δ₂) ((none, v) :: Δ₁) := by
  constructor
  · intro i t ht
    cases i with
    | zero => simpa [MLCtx.findB] using ht
    | succ i =>
      simp only [MLCtx.findB] at ht
      have hidx : (if i + 1 < d + 1 then i + 1 else i + 1 + 1) =
          (if i < d then i else i + 1) + 1 := by split_ifs <;> omega
      rw [hidx]
      simpa [MLCtx.findB] using h.1 i t ht
  · intro y t ht
    have hu' := h.2 y t (by simpa [MLCtx.findF] using ht)
    split at hu' <;> rename_i hy
    · simp only [hy, ↓reduceIte]; simpa [MLCtx.findB] using hu'
    · simp only [hy]; simpa [MLCtx.findF] using hu'

end

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {lps : List Name}

/-- Abstracting `x` into the bound variable `d` keeps the translation. -/
theorem TrM.absN {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ₂ Δ₁ : MLCtx ζ lps.length n}
    {x : FVarId} {d : Nat} {e : Expr} {t : Metalean.Expr ζ lps.length n}
    (h : TrM E B lps Γ Δ₂ e t) (W : Rel x d Δ₂ Δ₁) : TrM E B lps Γ Δ₁ (absFV x d e) t := by
  induction h generalizing d with
  | bvar h => exact .bvar (W.1 _ _ h)
  | fvar h =>
    have h' := W.2 _ _ h
    simp only [absFV]
    split at h' <;> rename_i hy
    · simp only [hy, ↓reduceIte]; exact .bvar h'
    · simp only [hy]; exact .fvar h'
  | sort h => exact .sort h
  | const h₁ h₂ => exact .const h₁ h₂
  | @special _ _ _ _ _ as as' _ _ hb hs hlen _ hsat ih =>
    rw [mkAppN_toArray, absFV_foldl, ← mkAppN_toArray]
    refine .special hb hs (by simpa using hlen) (fun i a a' ha ha' => ?_) hsat
    simp only [List.getElem?_map, Option.map_eq_some_iff] at ha
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    exact ih i a₀ a' ha₀ ha' W
  | app hns _ _ ih₁ ih₂ =>
    refine .app (fun ⟨c, us, b, hc, hB, hs⟩ => hns ⟨c, us, b, ?_, hB, hs⟩) (ih₁ W) (ih₂ W)
    rw [absFV_getAppFn] at hc
    exact absFV_eq_const hc
  | lam _ _ ih₁ ih₂ => exact .lam (ih₁ W) (ih₂ W.pushLam)
  | forallE _ _ ih₁ ih₂ => exact .forallE (ih₁ W) (ih₂ W.pushLam)
  | letE _ _ _ ih₁ ih₂ ih₃ => exact .letE (ih₁ W) (ih₂ W) (ih₃ (W.cons _))
  | mdata _ ih => exact .mdata (ih W)
  | lit h => exact .lit h
  | projStruct hst hi hS _ hty ih => exact .projStruct hst hi hS (ih W) hty
  | projProof hi hS hs hc hr hf hns _ hty ih => exact .projProof hi hS hs hc hr hf hns (ih W) hty

end

end AbsFV

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {lps : List Name}

/-- Closing a binder that was opened with a fresh free variable (`mkLambda`,
`LeanToLambdaBox/Erasure.lean:508`): a body that does not mention `x`, opened with `x`, translates
under the locals where `x` denotes the binder's variable to the term the body translates to under
the locals where the binder is a bound variable. The converse of `TrM.inst_fvar`. Reference:
`TrS.uninstantiateN` (`L4 Typing/Abstract.lean:55`), lean4lean `TrExprS.uninstantiateN`, DV-13. -/
theorem TrM.uninstantiateN {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
    {Δ : MLCtx ζ lps.length n} {A : Metalean.Expr ζ lps.length n} {x : FVarId} {b : Expr}
    {b' : Metalean.Expr ζ lps.length (n + 1)} (hfv : FVarsIn (· ≠ x) b)
    (h : TrM E B lps (Γ.snoc A) (Δ.pushLam (some x)) (b.instantiate1' (.fvar x)) b') :
    TrM E B lps (Γ.snoc A) (Δ.pushLam none) b b' := by
  have := AbsFV.TrM.absN h (AbsFV.Rel.zero x Δ)
  rwa [AbsFV.absFV_inst hfv] at this

end

end EraseProof
