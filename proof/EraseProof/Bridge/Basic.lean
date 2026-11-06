import EraseProof.Spec

/-!
# The translation `TrM` under changes of the locals

Lemmas about `TrM` that keep the Metalean context and image fixed and change only the Lean locals:
free variables of translated terms (`TrM.fvarsIn`), adding a `let`-bound free variable
(`TrM.weakFV_let`), and opening a binder with a fresh free variable (`TrM.inst_fvar`). They rest
on two facts: the translation of a term reads its locals only through `MLCtx.findB` and
`MLCtx.findF` (`TrM.mono`), and substituting a free variable never creates a new saturating
spine (`instantiate1'_fvar_getAppFn`).
-/

open Lean Erasure

namespace EraseProof

/-- Every free variable of `e` satisfies `p`. Reference: lean4lean `FVarsIn`
(`L4 Typing/Basic.lean`), DV-13. -/
def FVarsIn (p : FVarId → Prop) : Expr → Prop
  | .fvar x => p x
  | .app f a => FVarsIn p f ∧ FVarsIn p a
  | .lam _ t b _ | .forallE _ t b _ => FVarsIn p t ∧ FVarsIn p b
  | .letE _ t v b _ => FVarsIn p t ∧ FVarsIn p v ∧ FVarsIn p b
  | .mdata _ e | .proj _ _ e => FVarsIn p e
  | _ => True

section
variable {ζ : Metalean.Sigs} {ℓ n : Nat}

/-- `mkAppN` over a list is a left fold of `Expr.app`. -/
theorem mkAppN_toArray (f : Expr) (as : List Expr) : mkAppN f as.toArray = as.foldl .app f := by
  simp only [mkAppN, List.foldl_toArray]; rfl

/-- The derived `BEq` of free variables is equality. -/
theorem fvarId_beq_iff (x y : FVarId) : (x == y) = true ↔ x = y := by
  cases x; cases y
  show instBEqFVarId.beq _ _ = true ↔ _
  simp [instBEqFVarId.beq]

/-- The free variables of an application spine. -/
theorem FVarsIn_foldl (p : FVarId → Prop) (f : Expr) (as : List Expr) :
    FVarsIn p (as.foldl .app f) ↔ FVarsIn p f ∧ ∀ a ∈ as, FVarsIn p a := by
  induction as generalizing f with
  | nil => simp
  | cons a as ih => simp [ih, FVarsIn, and_assoc]

/-- Instantiating with a free variable commutes with taking the head of a spine. -/
theorem instantiate1'_fvar_getAppFn (x : FVarId) (f : Expr) (d : Nat) :
    (f.instantiate1' (.fvar x) d).getAppFn = f.getAppFn.instantiate1' (.fvar x) d := by
  induction f generalizing d with
  | app f a ih => simpa [Expr.instantiate1', Expr.getAppFn] using ih d
  | bvar i =>
    simp only [Expr.instantiate1', Expr.getAppFn]
    split_ifs <;> simp [Expr.liftLooseBVars', Expr.getAppFn]
  | _ => simp [Expr.instantiate1', Expr.getAppFn]

/-- A term that becomes a constant by instantiation with a free variable is that constant. -/
theorem instantiate1'_fvar_eq_const {x : FVarId} {g : Expr} {d : Nat} {c : Name} {us : List Level}
    (h : g.instantiate1' (.fvar x) d = .const c us) : g = .const c us := by
  cases g with
  | bvar i =>
    simp only [Expr.instantiate1'] at h
    split_ifs at h
    simp [Expr.liftLooseBVars'] at h
  | _ => simp only [Expr.instantiate1'] at h; first | exact h | cases h

/-- Instantiation of an application spine. -/
theorem instantiate1'_foldl (s f : Expr) (as : List Expr) (d : Nat) :
    (as.foldl .app f).instantiate1' s d =
      (as.map (·.instantiate1' s d)).foldl .app (f.instantiate1' s d) := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih => simp [ih, Expr.instantiate1']

/-- The denotation of a weakened local. -/
theorem MLDecl.denote_wk (d : MLDecl ζ ℓ n) : d.wk.denote = d.denote.wk := by
  cases d <;> simp [MLDecl.wk, MLDecl.denote]

/-- `findB` after weakening every entry. -/
theorem MLCtx.findB_map_wk (Δ : MLCtx ζ ℓ n) (i : Nat) :
    MLCtx.findB (Δ.map fun (y, d) => (y, d.wk)) i = (Δ.findB i).map Metalean.Expr.wk := by
  induction Δ generalizing i with
  | nil => rfl
  | cons p Δ ih =>
    obtain ⟨_ | y, d⟩ := p
    · cases i <;> simp [MLCtx.findB, MLDecl.denote_wk, ih]
    · simp [MLCtx.findB, ih]

/-- `findF` after weakening every entry. -/
theorem MLCtx.findF_map_wk (Δ : MLCtx ζ ℓ n) (x : FVarId) :
    MLCtx.findF (Δ.map fun (y, d) => (y, d.wk)) x = (Δ.findF x).map Metalean.Expr.wk := by
  induction Δ with
  | nil => rfl
  | cons p Δ ih =>
    obtain ⟨_ | y, d⟩ := p
    · simp [MLCtx.findF, ih]
    · simp only [List.map_cons, MLCtx.findF]
      split <;> simp [MLDecl.denote_wk, ih]

/-- `Δ'` answers every lookup `Δ` answers, with the same term. -/
def MLCtx.Sub (Δ Δ' : MLCtx ζ ℓ n) : Prop :=
  (∀ i t, Δ.findB i = some t → Δ'.findB i = some t) ∧
  ∀ x t, Δ.findF x = some t → Δ'.findF x = some t

/-- `MLCtx.Sub` is preserved by entering a binder. -/
theorem MLCtx.Sub.pushLam {Δ Δ' : MLCtx ζ ℓ n} (h : Δ.Sub Δ') :
    (Δ.pushLam none).Sub (Δ'.pushLam none) := by
  constructor
  · intro i t ht
    cases i with
    | zero => simpa [MLCtx.pushLam, MLCtx.findB] using ht
    | succ i =>
      simp only [MLCtx.pushLam, MLCtx.findB, MLCtx.findB_map_wk, Option.map_eq_some_iff] at ht ⊢
      obtain ⟨u, hu, rfl⟩ := ht
      exact ⟨u, h.1 _ _ hu, rfl⟩
  · intro x t ht
    simp only [MLCtx.pushLam, MLCtx.findF, MLCtx.findF_map_wk, Option.map_eq_some_iff] at ht ⊢
    obtain ⟨u, hu, rfl⟩ := ht
    exact ⟨u, h.2 _ _ hu, rfl⟩

/-- `MLCtx.Sub` is preserved by pushing the same bound local on both sides. -/
theorem MLCtx.Sub.cons {Δ Δ' : MLCtx ζ ℓ n} (h : Δ.Sub Δ') (d : MLDecl ζ ℓ n) :
    MLCtx.Sub ((none, d) :: Δ) ((none, d) :: Δ') := by
  constructor
  · intro i t ht
    cases i with
    | zero => simpa [MLCtx.findB] using ht
    | succ i => simpa [MLCtx.findB] using h.1 i t (by simpa [MLCtx.findB] using ht)
  · intro x t ht
    simpa [MLCtx.findF] using h.2 x t (by simpa [MLCtx.findF] using ht)

/-- The locals before (`Δ₁`) and after (`Δ₂`) replacing the bound variable `d` by the free
variable `x`: bound variables below `d` keep their denotation, `d` is now `x`, the ones above move
down by one, and free variables keep theirs. -/
def MLCtx.InstFV (x : FVarId) (d : Nat) (Δ₁ Δ₂ : MLCtx ζ ℓ n) : Prop :=
  (∀ i t, Δ₁.findB i = some t →
    (i < d → Δ₂.findB i = some t) ∧ (i = d → Δ₂.findF x = some t) ∧
      (d < i → Δ₂.findB (i - 1) = some t)) ∧
  ∀ y t, Δ₁.findF y = some t → Δ₂.findF y = some t

/-- `MLCtx.InstFV` is preserved by entering a binder (the variable moves to `d + 1`). -/
theorem MLCtx.InstFV.pushLam {x : FVarId} {d : Nat} {Δ₁ Δ₂ : MLCtx ζ ℓ n}
    (h : MLCtx.InstFV x d Δ₁ Δ₂) :
    MLCtx.InstFV x (d + 1) (Δ₁.pushLam none) (Δ₂.pushLam none) := by
  constructor
  · intro i t ht
    cases i with
    | zero =>
      simp only [MLCtx.pushLam, MLCtx.findB] at ht ⊢
      exact ⟨fun _ => ht, by omega, by omega⟩
    | succ i =>
      simp only [MLCtx.pushLam, MLCtx.findB, MLCtx.findB_map_wk, MLCtx.findF,
        MLCtx.findF_map_wk, Option.map_eq_some_iff] at ht ⊢
      obtain ⟨u, hu, rfl⟩ := ht
      obtain ⟨h₁, h₂, h₃⟩ := h.1 i u hu
      refine ⟨fun hi => ⟨u, h₁ (by omega), rfl⟩, fun hi => ⟨u, h₂ (by omega), rfl⟩, fun hi => ?_⟩
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have h₃' := h₃ (by omega)
      simp only [show j + 1 + 1 - 1 = j + 1 from rfl, show j + 1 - 1 = j from rfl] at h₃' ⊢
      simp [MLCtx.findB, MLCtx.findB_map_wk, h₃']
  · intro y t ht
    simp only [MLCtx.pushLam, MLCtx.findF, MLCtx.findF_map_wk, Option.map_eq_some_iff] at ht ⊢
    obtain ⟨u, hu, rfl⟩ := ht
    exact ⟨u, h.2 y u hu, rfl⟩

/-- `MLCtx.InstFV` is preserved by pushing the same bound local on both sides. -/
theorem MLCtx.InstFV.cons {x : FVarId} {d : Nat} {Δ₁ Δ₂ : MLCtx ζ ℓ n}
    (h : MLCtx.InstFV x d Δ₁ Δ₂) (v : MLDecl ζ ℓ n) :
    MLCtx.InstFV x (d + 1) ((none, v) :: Δ₁) ((none, v) :: Δ₂) := by
  constructor
  · intro i t ht
    cases i with
    | zero =>
      simp only [MLCtx.findB] at ht ⊢
      exact ⟨fun _ => ht, by omega, by omega⟩
    | succ i =>
      simp only [MLCtx.findB, MLCtx.findF] at ht ⊢
      obtain ⟨h₁, h₂, h₃⟩ := h.1 i t ht
      refine ⟨fun hi => h₁ (by omega), fun hi => h₂ (by omega), fun hi => ?_⟩
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      simpa [MLCtx.findB] using h₃ (by omega)
  · intro y t ht
    simpa [MLCtx.findF] using h.2 y t (by simpa [MLCtx.findF] using ht)

/-- Opening the innermost binder of `Δ.pushLam none` with a fresh `x` is an `MLCtx.InstFV` at `0`. -/
theorem MLCtx.InstFV.zero {x : FVarId} {Δ : MLCtx ζ ℓ n} (hx : Δ.findF x = none) :
    MLCtx.InstFV x 0 (Δ.pushLam none) (Δ.pushLam (some x)) := by
  have hxx : (x == x) = true := (fvarId_beq_iff x x).mpr rfl
  constructor
  · intro i t ht
    cases i with
    | zero =>
      simp only [MLCtx.pushLam, MLCtx.findB, MLDecl.denote] at ht
      simp [MLCtx.pushLam, MLCtx.findF, hxx, MLDecl.denote, ← ht]
    | succ i =>
      refine ⟨by omega, by omega, fun _ => ?_⟩
      simpa [MLCtx.pushLam, MLCtx.findB] using ht
  · intro y t ht
    simp only [MLCtx.pushLam, MLCtx.findF, MLCtx.findF_map_wk, Option.map_eq_some_iff] at ht ⊢
    obtain ⟨u, hu, rfl⟩ := ht
    have hy : (x == y) = false := by
      rcases Bool.eq_false_or_eq_true (x == y) with h | h
      · cases (fvarId_beq_iff x y).mp h; simp [hx] at hu
      · exact h
    simp [hy, hu]

end

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {lps : List Name}

/-- A translation stays one in a context of locals that answers at least the same lookups. -/
theorem TrM.mono {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ Δ' : MLCtx ζ lps.length n}
    {e : Expr} {t : Metalean.Expr ζ lps.length n} (h : TrM E B lps Γ Δ e t) (hΔ : Δ.Sub Δ') :
    TrM E B lps Γ Δ' e t := by
  induction h with
  | bvar h => exact .bvar (hΔ.1 _ _ h)
  | fvar h => exact .fvar (hΔ.2 _ _ h)
  | sort h => exact .sort h
  | const h₁ h₂ => exact .const h₁ h₂
  | special hb hs hlen _ hsat ih => exact .special hb hs hlen (fun i a a' h₁ h₂ => ih i a a' h₁ h₂ hΔ) hsat
  | app hns _ _ ih₁ ih₂ => exact .app hns (ih₁ hΔ) (ih₂ hΔ)
  | lam _ _ ih₁ ih₂ => exact .lam (ih₁ hΔ) (ih₂ hΔ.pushLam)
  | forallE _ _ ih₁ ih₂ => exact .forallE (ih₁ hΔ) (ih₂ hΔ.pushLam)
  | letE _ _ _ ih₁ ih₂ ih₃ => exact .letE (ih₁ hΔ) (ih₂ hΔ) (ih₃ (hΔ.cons _))
  | mdata _ ih => exact .mdata (ih hΔ)
  | lit h h₀ h₁ => exact .lit h h₀ h₁
  | projStruct hst hi hS _ hty ih => exact .projStruct hst hi hS (ih hΔ) hty
  | projProof hi hS hs hc hr hf hns _ hty ih => exact .projProof hi hS hs hc hr hf hns (ih hΔ) hty

/-- A translated term mentions only the locals' free variables. Reference: `TrS.fvarsIn`
(`L4 Typing/Basic.lean:61`), DV-13. -/
theorem TrM.fvarsIn {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    {e : Expr} {t : Metalean.Expr ζ lps.length n} (h : TrM E B lps Γ Δ e t) :
    FVarsIn (fun x => (Δ.findF x).isSome) e := by
  induction h with
  | bvar | sort | const | lit => trivial
  | fvar h => simp [FVarsIn, h]
  | @special _ _ _ _ _ as as' _ _ _ _ hlen _ _ ih =>
    rw [mkAppN_toArray, FVarsIn_foldl]
    refine ⟨trivial, fun a ha => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    exact ih i _ as'[i] (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem (hlen ▸ hi))
  | app _ _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | lam _ _ ih₁ ih₂ | forallE _ _ ih₁ ih₂ =>
    refine ⟨ih₁, ?_⟩
    simpa [MLCtx.pushLam, MLCtx.findF, MLCtx.findF_map_wk] using ih₂
  | letE _ _ _ ih₁ ih₂ ih₃ =>
    exact ⟨ih₁, ih₂, by simpa [MLCtx.findF] using ih₃⟩
  | mdata _ ih | projStruct _ _ _ _ _ ih | projProof _ _ _ _ _ _ _ _ _ ih => exact ih

/-- Weakening by a new `let`-bound free variable that the locals do not mention. Reference:
`TrS.weakFV` (`L4 Typing/Weak.lean:48`), DV-13. -/
theorem TrM.weakFV_let {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    {e : Expr} {t v : Metalean.Expr ζ lps.length n} {x : FVarId} (hx : Δ.findF x = none)
    (h : TrM E B lps Γ Δ e t) : TrM E B lps Γ ((some x, .vlet v) :: Δ) e t := by
  refine h.mono ⟨fun i t ht => by simpa [MLCtx.findB] using ht, fun y t ht => ?_⟩
  have hy : (x == y) = false := by
    rcases Bool.eq_false_or_eq_true (x == y) with h | h
    · cases (fvarId_beq_iff x y).mp h; simp [hx] at ht
    · exact h
  simp [MLCtx.findF, hy, ht]

/-- Instantiating the bound variable `d` by a free variable that denotes the same term
(`MLCtx.InstFV`) keeps the translation. -/
theorem TrM.instN_fvar {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
    {Δ₁ Δ₂ : MLCtx ζ lps.length n} {x : FVarId} {d : Nat} {b : Expr}
    {b' : Metalean.Expr ζ lps.length n} (hb : TrM E B lps Γ Δ₁ b b') (W : MLCtx.InstFV x d Δ₁ Δ₂) :
    TrM E B lps Γ Δ₂ (b.instantiate1' (.fvar x) d) b' := by
  induction hb generalizing d with
  | @bvar _ _ _ i _ h =>
    obtain ⟨h₁, h₂, h₃⟩ := W.1 _ _ h
    simp only [Expr.instantiate1']
    split_ifs with hlt heq
    · exact .bvar (h₁ hlt)
    · exact .fvar (by simpa [Expr.liftLooseBVars'] using h₂ heq)
    · exact .bvar (h₃ (by omega))
  | fvar h => exact .fvar (W.2 _ _ h)
  | sort h => exact .sort h
  | const h₁ h₂ => exact .const h₁ h₂
  | @special _ _ _ _ _ as as' _ _ hb hs hlen _ hsat ih =>
    rw [mkAppN_toArray, instantiate1'_foldl, ← mkAppN_toArray]
    refine .special hb hs (by simpa using hlen) (fun i a a' ha ha' => ?_) hsat
    simp only [List.getElem?_map, Option.map_eq_some_iff] at ha
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    exact ih i a₀ a' ha₀ ha' W
  | app hns _ _ ih₁ ih₂ =>
    refine .app (fun ⟨c, us, b, hc, hB, hs⟩ => hns ⟨c, us, b, ?_, hB, hs⟩) (ih₁ W) (ih₂ W)
    rw [instantiate1'_fvar_getAppFn] at hc
    exact instantiate1'_fvar_eq_const hc
  | lam _ _ ih₁ ih₂ => exact .lam (ih₁ W) (ih₂ W.pushLam)
  | forallE _ _ ih₁ ih₂ => exact .forallE (ih₁ W) (ih₂ W.pushLam)
  | letE _ _ _ ih₁ ih₂ ih₃ => exact .letE (ih₁ W) (ih₂ W) (ih₃ (W.cons _))
  | mdata _ ih => exact .mdata (ih W)
  | lit h h₀ h₁ => exact .lit h h₀ h₁
  | projStruct hst hi hS _ hty ih => exact .projStruct hst hi hS (ih W) hty
  | projProof hi hS hs hc hr hf hns _ hty ih => exact .projProof hi hS hs hc hr hf hns (ih W) hty

/-- Opening a binder with a fresh free variable (`lambdaMonocular`): the body, with its bound
variable replaced by `x`, translates to the same Metalean term under the locals where `x` denotes
the binder's variable. Reference: `TrS.inst_fvar` (`L4 Typing/Abstract.lean:66`), DV-13. -/
theorem TrM.inst_fvar {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    {A : Metalean.Expr ζ lps.length n} {x : FVarId} {b : Expr}
    {b' : Metalean.Expr ζ lps.length (n + 1)} (hx : Δ.findF x = none)
    (hb : TrM E B lps (Γ.snoc A) (Δ.pushLam none) b b') :
    TrM E B lps (Γ.snoc A) (Δ.pushLam (some x)) (b.instantiate1' (.fvar x)) b' :=
  hb.instN_fvar (MLCtx.InstFV.zero hx)

end

end EraseProof
