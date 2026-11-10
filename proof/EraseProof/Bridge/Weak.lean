import EraseProof.Bridge.Basic
import EraseProof.Bridge.Subst
import Metalean.Typing.Substitution

/-!
# Weakening of the translation

Inserting a Metalean variable at level `cut` (`Expr.wkFrom`, `Ctx.insert`, `ML Syntax/Weakening.lean`)
together with a Lean local, bound (the source's loose bound variables are lifted) or free (the
source is unchanged), keeps a translation (`TrM.wkFrom`). The two instances the development uses
are `TrM.weakBV` and `TrM.weakFV`.
-/

open Lean Erasure

namespace EraseProof

/-- Lifting by zero is the identity. -/
theorem liftLooseBVars'_zero (e : Expr) (s : Nat) : e.liftLooseBVars' s 0 = e := by
  induction e generalizing s with
  | bvar i => simp only [Expr.liftLooseBVars']; split <;> rfl
  | app f a ihf iha => simp [Expr.liftLooseBVars', ihf, iha]
  | lam _ t b _ iht ihb | forallE _ t b _ iht ihb => simp [Expr.liftLooseBVars', iht, ihb]
  | letE _ t v b _ iht ihv ihb => simp [Expr.liftLooseBVars', iht, ihv, ihb]
  | mdata _ e ih | proj _ _ e ih => simp [Expr.liftLooseBVars', ih]
  | _ => rfl

/-- Lifting of an application spine. -/
theorem liftLooseBVars'_foldl (f : Expr) (as : List Expr) (s d : Nat) :
    (as.foldl .app f).liftLooseBVars' s d =
      (as.map (·.liftLooseBVars' s d)).foldl .app (f.liftLooseBVars' s d) := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih => simp [ih, Expr.liftLooseBVars']

/-- Lifting commutes with taking the head of a spine. -/
theorem liftLooseBVars'_getAppFn (f : Expr) (s d : Nat) :
    (f.liftLooseBVars' s d).getAppFn = f.getAppFn.liftLooseBVars' s d := by
  induction f generalizing s with
  | app f a ih => simpa [Expr.liftLooseBVars', Expr.getAppFn] using ih s
  | _ => simp [Expr.liftLooseBVars', Expr.getAppFn]

/-- A term whose lift is a constant is that constant. -/
theorem liftLooseBVars'_eq_const {g : Expr} {s d : Nat} {c : Name} {us : List Level}
    (h : g.liftLooseBVars' s d = .const c us) : g = .const c us := by
  cases g <;> simp only [Expr.liftLooseBVars'] at h <;> first | exact h | cases h

section
variable {ζ : Metalean.Sigs} {ℓ n : Nat}

/-- The locals before (`Δ`) and after (`Δ'`) inserting a Metalean variable at level `cut` and a Lean
local below the `dk` innermost bound variables: `d = 1` for a bound local (the bound variables
from `dk` on move up by one), `d = 0` for a free one. Every lookup of `Δ` is answered by `Δ'`
with the weakened term. -/
def MLCtx.Lift (dk d cut : Nat) (Δ : MLCtx ζ ℓ n) (Δ' : MLCtx ζ ℓ (n + 1)) : Prop :=
  (∀ i t, Δ.findB i = some t → Δ'.findB (if i < dk then i else i + d) = some (t.wkFrom cut)) ∧
  ∀ x t, Δ.findF x = some t → Δ'.findF x = some (t.wkFrom cut)

/-- `MLCtx.Lift` is preserved by entering a binder above the insertion point. -/
theorem MLCtx.Lift.pushLam {dk d cut : Nat} {Δ : MLCtx ζ ℓ n} {Δ' : MLCtx ζ ℓ (n + 1)}
    (h : MLCtx.Lift dk d cut Δ Δ') (hcut : cut ≤ n) :
    MLCtx.Lift (dk + 1) d cut (Δ.pushLam none) (Δ'.pushLam none) := by
  constructor
  · intro i t ht
    cases i with
    | zero =>
      simp only [MLCtx.pushLam, MLCtx.findB, MLDecl.denote] at ht ⊢
      cases ht
      simp [MLCtx.findB, MLDecl.denote, ML.Expr.last_wkFrom hcut]
    | succ i =>
      simp only [MLCtx.pushLam, MLCtx.findB, MLCtx.findB_map_wk, Option.map_eq_some_iff] at ht
      obtain ⟨u, hu, rfl⟩ := ht
      have hu' := h.1 i u hu
      have hidx : (if i + 1 < dk + 1 then i + 1 else i + 1 + d) =
          (if i < dk then i else i + d) + 1 := by split_ifs <;> omega
      rw [hidx]
      simp [MLCtx.pushLam, MLCtx.findB, MLCtx.findB_map_wk, hu', Metalean.Expr.wk_wkFrom hcut]
  · intro x t ht
    simp only [MLCtx.pushLam, MLCtx.findF, MLCtx.findF_map_wk, Option.map_eq_some_iff] at ht
    obtain ⟨u, hu, rfl⟩ := ht
    simp [MLCtx.pushLam, MLCtx.findF, MLCtx.findF_map_wk, h.2 x u hu, Metalean.Expr.wk_wkFrom hcut]

/-- `MLCtx.Lift` is preserved by pushing a `let` above the insertion point. -/
theorem MLCtx.Lift.cons {dk d cut : Nat} {Δ : MLCtx ζ ℓ n} {Δ' : MLCtx ζ ℓ (n + 1)}
    (h : MLCtx.Lift dk d cut Δ Δ') (v : Metalean.Expr ζ ℓ n) :
    MLCtx.Lift (dk + 1) d cut ((none, .vlet v) :: Δ) ((none, .vlet (v.wkFrom cut)) :: Δ') := by
  constructor
  · intro i t ht
    cases i with
    | zero =>
      simp only [MLCtx.findB, MLDecl.denote] at ht ⊢
      cases ht
      simp [MLCtx.findB, MLDecl.denote]
    | succ i =>
      simp only [MLCtx.findB] at ht
      have hidx : (if i + 1 < dk + 1 then i + 1 else i + 1 + d) =
          (if i < dk then i else i + d) + 1 := by split_ifs <;> omega
      rw [hidx]
      simpa [MLCtx.findB] using h.1 i t ht
  · intro x t ht
    simpa [MLCtx.findF] using h.2 x t (by simpa [MLCtx.findF] using ht)

/-- Inserting a bound local below every local is a `MLCtx.Lift` at `0` by one. -/
theorem MLCtx.Lift.bv (Δ : MLCtx ζ ℓ n) : MLCtx.Lift 0 1 n Δ (Δ.pushLam none) := by
  constructor
  · intro i t ht
    simp [MLCtx.pushLam, MLCtx.findB, MLCtx.findB_map_wk, ht, Metalean.Expr.wk]
  · intro x t ht
    simp [MLCtx.pushLam, MLCtx.findF, MLCtx.findF_map_wk, ht, Metalean.Expr.wk]

/-- Inserting a fresh free local below every local is a `MLCtx.Lift` at `0` by zero. -/
theorem MLCtx.Lift.fv {Δ : MLCtx ζ ℓ n} {x : FVarId} (hx : Δ.findF x = none) :
    MLCtx.Lift 0 0 n Δ (Δ.pushLam (some x)) := by
  constructor
  · intro i t ht
    simp [MLCtx.pushLam, MLCtx.findB, MLCtx.findB_map_wk, ht, Metalean.Expr.wk]
  · intro y t ht
    have hy : (x == y) = false := by
      rcases Bool.eq_false_or_eq_true (x == y) with h | h
      · cases (fvarId_beq_iff x y).mp h; simp [hx] at ht
      · exact h
    simp [MLCtx.pushLam, MLCtx.findF, MLCtx.findF_map_wk, hy, ht, Metalean.Expr.wk]

end

namespace WeakExt
open Metalean

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat}

/-- The renaming of `Γ₀.insert A Γ₁` into `Γ'.snoc _` that follows `ρ` off the inserted variable
`cut` and sends `cut` to the new last variable. -/
def insRen {cut n m : Nat} (hcut : cut ≤ n) (ρ : Ren n m) : Ren (n + 1) (m + 1) := fun v =>
  if h : v.val < cut then (ρ ⟨v.val, Nat.lt_of_lt_of_le h hcut⟩).castSucc
  else if h' : v.val = cut then Fin.last m
  else (ρ ⟨v.val - 1, by have := v.isLt; omega⟩).castSucc

theorem insRen_wkFrom {cut n m : Nat} (hcut : cut ≤ n) (ρ : Ren n m) (w : Var n) :
    insRen hcut ρ (Ren.wkFrom cut w) = (ρ w).castSucc := by
  by_cases hw : w.val < cut
  · rw [Ren.wkFrom_of_lt w hw]
    simp [insRen, hw]
  · rw [Ren.wkFrom_of_ge w (by omega)]
    have h₁ : ¬ (w.succ.val < cut) := by simp; omega
    have h₂ : w.succ.val ≠ cut := by simp; omega
    simp only [insRen, h₁, h₂, dite_false]
    simp

theorem insRen_cut {cut n m : Nat} (hcut : cut ≤ n) (ρ : Ren n m) :
    insRen hcut ρ ⟨cut, Nat.lt_succ_of_le hcut⟩ = Fin.last m := by
  simp [insRen]

theorem insRen_inj {cut n m : Nat} (hcut : cut ≤ n) {ρ : Ren n m} (hρ : Function.Injective ρ) :
    Function.Injective (insRen hcut ρ) := by
  intro v w h
  have key : ∀ x y : Var n, (ρ x).val = (ρ y).val → x.val = y.val :=
    fun x y hxy => by rw [hρ (Fin.ext hxy)]
  have ne₁ : ∀ x : Var n, (ρ x).val ≠ m := fun x => (ρ x).isLt.ne
  have ne₂ : ∀ x : Var n, m ≠ (ρ x).val := fun x => (ρ x).isLt.ne'
  have hv := congrArg Fin.val h
  have := v.isLt
  have := w.isLt
  unfold insRen at hv
  ext
  split_ifs at hv <;> simp only [Fin.val_castSucc, Fin.val_last] at hv <;>
    first
    | omega
    | exact absurd hv (ne₁ _)
    | exact absurd hv (ne₂ _)
    | (have := key _ _ hv; simp only at this; omega)

/-- Every variable of `Γ₀.insert A Γ₁` is the inserted one or a weakened old one. -/
theorem var_cases {cut n : Nat} (hcut : cut ≤ n) (v : Var (n + 1)) :
    v.val = cut ∨ ∃ w : Var n, v = Ren.wkFrom cut w := by
  by_cases h : v.val = cut
  · exact .inl h
  · refine .inr ?_
    by_cases hv : v.val < cut
    · exact ⟨⟨v.val, by omega⟩, by rw [Ren.wkFrom_of_lt (⟨v.val, by omega⟩ : Var n) hv]; rfl⟩
    · have := v.isLt
      refine ⟨⟨v.val - 1, by omega⟩, ?_⟩
      rw [Ren.wkFrom_of_ge (⟨v.val - 1, by omega⟩ : Var n) (by simp; omega)]
      ext; simp; omega

/-- The type of the inserted variable. -/
theorem get_insert_cut {cut : Nat} (Γ₀ : Ctx ζ ℓ 0 cut) (A : Expr ζ ℓ cut) {n : Nat}
    (Γ₁ : Ctx ζ ℓ cut n) (h : cut < n + 1) :
    Ctx.get ⟨cut, h⟩ (Γ₀.insert A Γ₁) = A.rename (fun v => ⟨v.val, by omega⟩) := by
  induction Γ₁ with
  | nil =>
    rw [ML.Ctx.insert_nil]
    change (Γ₀.snoc A).get (Fin.last cut) = _
    rw [Ctx.get_last, Expr.wk, Expr.wkFrom]
    congr 1
    funext v
    rw [Ren.wkFrom_of_lt v v.isLt]
    rfl
  | @snoc m Δ t₁ ih =>
    have hcm : cut ≤ m := Tele.le Δ
    rw [ML.Ctx.insert_snoc, Ctx.get_snoc _ _ _ (by simp; omega)]
    change (Ctx.get ⟨cut, by omega⟩ (Γ₀.insert A Δ)).wk = _
    rw [ih (by omega), Expr.wk, Expr.wkFrom, Expr.rename_rename]
    congr 1
    funext v
    simp only [Ren.comp]
    rw [Ren.wkFrom_of_lt _ (by simp; omega)]
    rfl

/-- `TypedExt` is stable under weakening at level `cut`. -/
theorem TypedExt.wkFrom {cut : Nat} {Γ₀ : Ctx ζ ℓ 0 cut} (A : Expr ζ ℓ cut) {n : Nat}
    {Γ₁ : Ctx ζ ℓ cut n} {e T : Expr ζ ℓ n} (h : TypedExt E (Γ₀ ++ Γ₁) e T) :
    TypedExt E (Γ₀.insert A Γ₁) (e.wkFrom cut) (T.wkFrom cut) := by
  obtain ⟨m, Γ', ρ, hρ, hget, hty⟩ := h
  have hcut : cut ≤ n := Tele.le Γ₁
  let ρ₀ : Ren cut m := fun v => ρ ⟨v.val, by omega⟩
  have key (x : Expr ζ ℓ n) : (x.wkFrom cut).rename (insRen hcut ρ) = (x.rename ρ).wk := by
    rw [Expr.wkFrom, Expr.rename_rename, Expr.wk, Expr.wkFrom, Expr.rename_rename]
    congr 1
    funext w
    simp only [Ren.comp, insRen_wkFrom]
    rw [Ren.wkFrom_of_lt _ (ρ w).isLt]
  refine ⟨m + 1, Γ'.snoc (A.rename ρ₀), insRen hcut ρ, insRen_inj hcut hρ, fun v => ?_, ?_⟩
  · rcases var_cases hcut v with hv | ⟨w, rfl⟩
    · obtain rfl : v = ⟨cut, Nat.lt_succ_of_le hcut⟩ := Fin.ext hv
      rw [insRen_cut, Ctx.get_last, get_insert_cut, Expr.rename_rename, Expr.wk, Expr.wkFrom,
        Expr.rename_rename]
      congr 1
      funext w
      simp only [Ren.comp]
      rw [Ren.wkFrom_of_lt _ (ρ₀ w).isLt]
      simp [insRen, ρ₀]
    · rw [insRen_wkFrom, Ctx.get_castSucc, Ctx.get_insert, key, hget]
  · rw [key, key]
    exact hty.wk _

end WeakExt

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {lps : List Name}

/-- Weakening: inserting a Metalean variable of type `A` at level `cut` of the context, with a Lean
local below the `dk` innermost bound variables (`MLCtx.Lift`), lifts the source by
`liftLooseBVars' dk d` and the image by `wkFrom cut`. Reference: `TrS.weakBV`, `TrS.weakFV'`
(`L4 Typing/Weak.lean:21,56`); `Defeq.wkFrom` (`ML Typing/Substitution.lean:122`). -/
theorem TrM.wkFrom {cut : Nat} {Γ₀ : Metalean.Ctx ζ lps.length 0 cut}
    (A : Metalean.Expr ζ lps.length cut) {n : Nat} {Γ₁ : Metalean.Ctx ζ lps.length cut n}
    {Δ : MLCtx ζ lps.length n} {Δ' : MLCtx ζ lps.length (n + 1)} {dk d : Nat} {e : Expr}
    {t : Metalean.Expr ζ lps.length n} (h : TrM E B lps (Γ₀ ++ Γ₁) Δ e t)
    (W : MLCtx.Lift dk d cut Δ Δ') :
    TrM E B lps (Γ₀.insert A Γ₁) Δ' (e.liftLooseBVars' dk d) (t.wkFrom cut) := by
  generalize hΓ : Γ₀ ++ Γ₁ = Γ at h
  induction h generalizing dk with
  | @bvar _ _ _ i _ hb =>
    have := W.1 _ _ hb
    simp only [Expr.liftLooseBVars']
    exact .bvar this
  | fvar hf => exact .fvar (W.2 _ _ hf)
  | sort hl => exact .sort hl
  | const h₁ h₂ => exact .const h₁ h₂
  | @special _ _ _ _ _ as as' _ _ hb hs hlen _ hsat ih =>
    rw [mkAppN_toArray, liftLooseBVars'_foldl, ← mkAppN_toArray]
    have hsat' := hsat.subst (Metalean.Subst.wkFrom cut)
    simp only [← Metalean.Expr.wkFrom_eq_subst] at hsat'
    refine .special hb hs (by simpa using hlen) (fun i a a' ha ha' => ?_) hsat'
    simp only [List.getElem?_map, Option.map_eq_some_iff] at ha ha'
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    obtain ⟨a₀', ha₀', rfl⟩ := ha'
    exact ih i a₀ a₀' ha₀ ha₀' W hΓ
  | app hns _ _ ih₁ ih₂ =>
    refine .app (fun ⟨c, us, b, hc, hB, hs⟩ => hns ⟨c, us, b, ?_, hB, hs⟩) (ih₁ W hΓ) (ih₂ W hΓ)
    rw [liftLooseBVars'_getAppFn] at hc
    exact liftLooseBVars'_eq_const hc
  | @lam _ _ _ _ A' _ _ _ _ _ _ ih₁ ih₂ =>
    rw [Metalean.Expr.wkFrom_lam Γ₁.le]
    exact .lam (ih₁ W hΓ) (ih₂ (Γ₁ := Γ₁.snoc A') (W.pushLam Γ₁.le) (by rw [← hΓ]; rfl))
  | @forallE _ _ _ _ A' _ _ _ _ _ _ ih₁ ih₂ =>
    rw [Metalean.Expr.wkFrom_forallE Γ₁.le]
    exact .forallE (ih₁ W hΓ) (ih₂ (Γ₁ := Γ₁.snoc A') (W.pushLam Γ₁.le) (by rw [← hΓ]; rfl))
  | letE _ _ _ ih₁ ih₂ ih₃ =>
    rw [ML.Expr.wkFrom_letE Γ₁.le, Metalean.Expr.wk_wkFrom Γ₁.le]
    exact .letE (ih₁ W hΓ) (ih₂ W hΓ) (ih₃ (W.cons _) hΓ)
  | mdata _ ih => exact .mdata (ih W hΓ)
  | lit hB h₀ h₁ =>
    rw [Metalean.Expr.wkFrom_eq_subst, natLitM_subst]
    exact .lit hB h₀ h₁
  | projStruct hst hi hS _ hty ih =>
    subst hΓ
    rw [ML.Inductive.IsStructure.projTerm_wkFrom]
    exact .projStruct hst hi hS (ih W rfl) (by simpa using WeakExt.TypedExt.wkFrom A hty)
  | projProof hi hS hs hc hr hf hns _ hty ih =>
    subst hΓ
    rw [Metalean.Expr.wkFrom_eq_subst, projProofTerm_subst]
    simp only [← Metalean.Expr.wkFrom_eq_subst]
    exact .projProof hi hS hs hc hr hf hns (ih W rfl)
      (by simpa using WeakExt.TypedExt.wkFrom A hty)

/-- Weakening by a new bound variable, innermost. Reference: `TrS.weakBV`
(`L4 Typing/Weak.lean:56`); `Defeq.wk` (`ML Typing/Substitution.lean:131`). -/
theorem TrM.weakBV {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    {e : Expr} {t A : Metalean.Expr ζ lps.length n} (h : TrM E B lps Γ Δ e t) :
    TrM E B lps (Γ.snoc A) (Δ.pushLam none) (e.liftLooseBVars' 0 1) t.wk :=
  TrM.wkFrom (Γ₁ := .nil) A h (MLCtx.Lift.bv Δ)

/-- Weakening by a new free variable (λ-bound) that the locals do not mention. Reference:
`TrS.weakFV` (`L4 Typing/Weak.lean:48`); `Defeq.wk` (`ML Typing/Substitution.lean:131`). -/
theorem TrM.weakFV {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    {e : Expr} {t A : Metalean.Expr ζ lps.length n} {x : FVarId} (hx : Δ.findF x = none)
    (h : TrM E B lps Γ Δ e t) : TrM E B lps (Γ.snoc A) (Δ.pushLam (some x)) e t.wk := by
  have h' := TrM.wkFrom (Γ₁ := .nil) A h (MLCtx.Lift.fv hx)
  rw [liftLooseBVars'_zero] at h'
  exact h'

end

end EraseProof
