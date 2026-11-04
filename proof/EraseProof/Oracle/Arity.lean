import EraseProof.Oracle.Whnf

/-!
# Soundness of the oracle's arity test

`Pure.isArity_sound`: when `Erasure.Pure.isArity` answers `true` on a translated type, the type's
image is convertible to an arity (`IsArity`). The test reduces with `whnf` (`Pure.whnf_sound`) and
enters Π-binders. Under a new binder the traversal's locals still translate (`LocalsOK.weakBV`),
because their types and values mention no bound variable: the locals `Δ` of the traversal have no
bound entry, and a translation over such locals has no loose bound variable (`TrM.lift_eq`).
-/

open Lean Erasure
open Metalean (Defeq TypeEq EnvWF)

namespace EraseProof

namespace OracleArity

variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {lps : List Name}

/-- A sort under Π-binders, read from the outermost binder. -/
inductive Shape {ℓ : Nat} : {n : Nat} → Metalean.Expr ζ ℓ n → Prop
  | sort {n : Nat} {u : Metalean.Level ℓ} : Shape (n := n) (.sort u)
  | forallE {n : Nat} {A : Metalean.Expr ζ ℓ n} {C : Metalean.Expr ζ ℓ (n + 1)} :
      Shape C → Shape (.forallE A C)

/-- A shape is `Ctx.pi` of a sort over a telescope. -/
theorem Shape.exists_pi {ℓ n : Nat} {T : Metalean.Expr ζ ℓ n} (h : Shape T) :
    ∃ (b : Nat) (Θ : Metalean.Ctx ζ ℓ n b) (u : Metalean.Level ℓ),
      T = Metalean.Ctx.pi (.sort u) Θ := by
  induction h with
  | sort => exact ⟨_, .nil, _, rfl⟩
  | @forallE m A C _ ih =>
    obtain ⟨b, Θ, u, rfl⟩ := ih
    refine ⟨b, (Metalean.Ctx.nil.snoc A) ++ Θ, u, ?_⟩
    exact (Tele.foldr_append (S := Metalean.Expr ζ ℓ) Metalean.Expr.forallE (.sort u)
      (Metalean.Ctx.nil.snoc A) Θ).symm

/-- A type equal to a shape is an arity. -/
theorem Shape.isArity {ℓ n : Nat} {Γ : Metalean.Ctx ζ ℓ 0 n} {T X : Metalean.Expr ζ ℓ n}
    (hX : Shape X) (h : E[Γ] ⊢ T ≡ X typ) : IsArity E Γ T := by
  obtain ⟨b, Θ, u, rfl⟩ := hX.exists_pi
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le Θ.le
  exact ⟨k, Θ, u, h⟩

/-- Π-types with equal codomains are equal. -/
theorem forallE_cod {ℓ n : Nat} {Γ : Metalean.Ctx ζ ℓ 0 n} {A : Metalean.Expr ζ ℓ n}
    {C₁ C₂ : Metalean.Expr ζ ℓ (n + 1)} (hA : E[Γ] ⊢ A typ) (h : E[Γ.snoc A] ⊢ C₁ ≡ C₂ typ) :
    E[Γ] ⊢ .forallE A C₁ ≡ .forallE A C₂ typ := by
  obtain ⟨l, hA⟩ := hA
  induction h using Relation.TransGen.trans_induction_on with
  | single h => obtain ⟨u, h⟩ := h; exact .ofDefEq (.forallEDF hA h h)
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A translation over locals without bound entries from `k` on is not changed by lifting its
loose bound variables from `k`. -/
theorem TrM.lift_eq {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    {e : Expr} {t : Metalean.Expr ζ lps.length n} (h : TrM E B lps Γ Δ e t) :
    ∀ {k d : Nat}, (∀ i, k ≤ i → Δ.findB i = none) → e.liftLooseBVars' k d = e := by
  induction h with
  | bvar hb =>
    intro k d hk
    simp only [Expr.liftLooseBVars']
    split_ifs with hi
    · rfl
    · rw [hk _ (Nat.le_of_not_lt hi)] at hb
      cases hb
  | fvar | sort | const | lit => intros; rfl
  | @special _ _ _ _ _ as as' _ _ _ _ hlen _ _ ih =>
    intro k d hk
    rw [mkAppN_toArray, liftLooseBVars'_foldl]
    congr 1
    apply List.ext_getElem?
    intro i
    rw [List.getElem?_map]
    rcases ha : as[i]? with _ | a
    · rfl
    · have hi : i < as'.length := by
        rw [← hlen]; exact (List.getElem?_eq_some_iff.mp ha).1
      rcases ha' : as'[i]? with _ | a'
      · rw [List.getElem?_eq_none_iff] at ha'; omega
      · simp only [Option.map_some]
        rw [ih i a a' ha ha' hk]
  | app _ _ _ ih₁ ih₂ =>
    intro k d hk
    simp only [Expr.liftLooseBVars']
    rw [ih₁ hk, ih₂ hk]
  | lam _ _ ih₁ ih₂ | forallE _ _ ih₁ ih₂ =>
    intro k d hk
    simp only [Expr.liftLooseBVars']
    rw [ih₁ hk, ih₂ (k := k + 1) fun i hi => ?_]
    cases i with
    | zero => omega
    | succ i =>
      simp [MLCtx.pushLam, MLCtx.findB, MLCtx.findB_map_wk, hk i (by omega)]
  | letE _ _ _ ih₁ ih₂ ih₃ =>
    intro k d hk
    simp only [Expr.liftLooseBVars']
    rw [ih₁ hk, ih₂ hk, ih₃ (k := k + 1) fun i hi => ?_]
    cases i with
    | zero => omega
    | succ i => simpa [MLCtx.findB] using hk i (by omega)
  | mdata _ ih =>
    intro k d hk
    simp only [Expr.liftLooseBVars']
    rw [ih hk]
  | projStruct _ _ _ _ _ ih | projProof _ _ _ _ _ _ _ _ _ ih =>
    intro k d hk
    simp only [Expr.liftLooseBVars']
    rw [ih hk]

/-- The traversal's locals translate under a new bound variable when their types and values have
no loose bound variable. -/
theorem LocalsOK.weakBV {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    {ls : List Local} (A : Metalean.Expr ζ lps.length n) (hloc : LocalsOK E B lps Γ Δ ls)
    (hcl : ∀ l ∈ ls, l.type.liftLooseBVars' 0 1 = l.type ∧
      ∀ v, l.value? = some v → v.liftLooseBVars' 0 1 = v) :
    LocalsOK E B lps (Γ.snoc A) (Δ.pushLam none) ls := by
  intro l hl
  obtain ⟨T, t, hT, hF, ht, hv⟩ := hloc l hl
  refine ⟨T.wk, t.wk, ?_, ?_, ht.wk A, fun v hv' => ?_⟩
  · have h := TrM.weakBV (A := A) hT
    rwa [(hcl l hl).1] at h
  · simp [MLCtx.pushLam, MLCtx.findF, MLCtx.findF_map_wk, hF]
  · have h := TrM.weakBV (A := A) (hv v hv')
    rwa [(hcl l hl).2 v hv'] at h

/-- `isArity`'s `true` is sound, at every context the oracle enters. -/
theorem isArity_shape {cx : Pure.Ctx} {P : List ConstantInfo} (henv : ProgEnv P ζ E B)
    (hE : EnvWF E) (hsub : SubEnv cx.decls P) {ls : List Local}
    (hcl : ∀ l ∈ ls, l.type.liftLooseBVars' 0 1 = l.type ∧
      ∀ v, l.value? = some v → v.liftLooseBVars' 0 1 = v) :
    ∀ {fuel n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n} {A : Expr}
      {A' : Metalean.Expr ζ lps.length n},
      E[Γ] ⊢ ok → LocalsOK E B lps Γ Δ ls → TrM E B lps Γ Δ A A' → E[Γ] ⊢ A' typ →
      Pure.isArity cx fuel ls A = .ok true → ∃ X, Shape X ∧ E[Γ] ⊢ A' ≡ X typ
  | 0, _, _, _, _, _, _, _, _, _, h => by
    simp [Pure.isArity, throw, throwThe, MonadExceptOf.throw] at h
  | f + 1, n, Γ, Δ, A, A', hΓ, hloc, he, ⟨u, hA⟩, h => by
    simp only [Pure.isArity] at h
    obtain ⟨W, h1, h2⟩ := OracleWhnf.ok_of_bind h
    obtain ⟨W', hW, hd⟩ := Pure.whnf_sound henv hE hsub hΓ hloc he hA h1
    split at h2
    · rename_i l
      generalize hx : Expr.sort l = x at hW
      cases hW with
      | sort _ => exact ⟨_, .sort, .ofDefEq hd⟩
      | special => exact absurd hx (ne_mkAppN_const fun _ _ h => by cases h)
      | _ => cases hx
    · rename_i nm C D bi
      generalize hx : Expr.forallE nm C D bi = x at hW
      cases hW with
      | forallE hC hD =>
        cases hx
        obtain ⟨⟨_, hC'⟩, ⟨_, hD'⟩⟩ := hd.right.forallE_inv
        obtain ⟨Y, hY, hDY⟩ := isArity_shape henv hE hsub hcl (.snoc hΓ ⟨_, hC'⟩)
          (LocalsOK.weakBV _ hloc hcl) hD ⟨_, hD'⟩ h2
        exact ⟨_, .forallE hY, (TypeEq.ofDefEq hd).trans (forallE_cod ⟨_, hC'⟩ hDY)⟩
      | special => exact absurd hx (ne_mkAppN_const fun _ _ h => by cases h)
      | _ => cases hx
    · cases h2

end OracleArity

open OracleArity in
/-- `isArity` answers `true` only on types convertible to an arity. The traversal's locals have no
bound entry (`hnb`): the test enters Π-binders, under which the locals' types must keep their
meaning. Reference: `is_arityP` (`MR E/ErasureFunction.v:826`), `true` direction; port of
`L4 Oracle.lean:22`. -/
theorem Pure.isArity_sound {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ}
    {P : List ConstantInfo} {lps : List Name} {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
    {Δ : MLCtx ζ lps.length n} {cx : Pure.Ctx} {fuel : Nat} {ls : List Local} {A : Expr}
    {A' : Metalean.Expr ζ lps.length n}
    (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv cx.decls P)
    (hΓ : E[Γ] ⊢ ok) (hloc : LocalsOK E B lps Γ Δ ls) (hnb : ∀ i, Δ.findB i = none)
    (he : TrM E B lps Γ Δ A A') (hA : E[Γ] ⊢ A' typ) (h : Pure.isArity cx fuel ls A = .ok true) :
    IsArity E Γ A' := by
  have hcl : ∀ l ∈ ls, l.type.liftLooseBVars' 0 1 = l.type ∧
      ∀ v, l.value? = some v → v.liftLooseBVars' 0 1 = v := by
    intro l hl
    obtain ⟨T, t, hT, -, -, hv⟩ := hloc l hl
    exact ⟨TrM.lift_eq hT fun i _ => hnb i, fun v h' => TrM.lift_eq (hv v h') fun i _ => hnb i⟩
  obtain ⟨X, hX, hd⟩ := isArity_shape henv hE hsub hcl hΓ hloc he hA h
  exact hX.isArity hd

end EraseProof
