import EraseProof.Relation.Basic
import EraseProof.Typing.Inst
import EraseProof.Oracle.Whnf
import EraseProof.Env

/-!
# Substitution into the erasure relation

Letouzey's Lemma 16, as MetaRocq's `erases_subst0` (`MR E/ESubstitution.v:612`): substituting a
closed, erased argument for the variable of an erased `λ` body gives an erasure of the
instantiated body, the λ□ side substituted by `csubst` (`Erases.inst`). A body erased to `□` as a
whole stays erasable by Letouzey's Lemma 2 (`IsErasable.inst`); every other body goes through the
substitution lemma under binders (`Erases.instN`, MetaRocq's `erases_subst`), which uses
erasability under substitution and weakening at any depth (`IsErasable.instN`,
`IsErasable.weakN`) and the relation's weakening for closed terms (`Erases.weakBV`), at the
substituted variable.
-/

open Lean Lean4Lean Erasure

namespace EraseProof

/-! ## Arities, erasability and the λ□ side -/

/-- Arities are stable under lifting. Reference: the arity case of `Is_type_weakening`
(`MR E/ESubstitution.v:138`). -/
theorem IsArity.liftN : ∀ {T : VExpr} {k : Nat}, IsArity T → IsArity (T.liftN n k)
  | .sort _, _, _ => trivial
  | .forallE _ B, _, h => IsArity.liftN (T := B) h
  | .bvar _, _, h | .const .., _, h | .app .., _, h | .lam .., _, h => h.elim

section
variable {venv : VEnv}

/-- Erasability is stable under weakening at any depth. Reference: `Is_type_weakening`
(`MR E/ESubstitution.v:138`). -/
theorem IsErasable.weakN (henv : venv.Ordered) (W : Ctx.LiftN n k Γ Γ')
    (h : IsErasable venv U Γ e) : IsErasable venv U Γ' (e.liftN n k) := by
  obtain ⟨T, hT, hT'⟩ := h
  refine ⟨T.liftN n k, hT.weakN henv W, ?_⟩
  obtain hT' | ⟨u, hu, hu0⟩ := hT'
  · exact .inl hT'.liftN
  · exact .inr ⟨u, hu.weakN henv W, hu0⟩

/-- Erasability is stable under substitution of a variable at any depth. Reference:
`is_type_subst` (`MR E/ESubstitution.v:346`), whose context `Γ ,,, Γ' ,,, Δ` has the substituted
variables below `Δ`; `IsErasable.inst` is the case `Δ = []`. -/
theorem IsErasable.instN (henv : venv.Ordered) (W : Ctx.InstN Γ₀ a A k Γ₁ Γ)
    (h₀ : venv.HasType U Γ₀ a A) (h : IsErasable venv U Γ₁ b) :
    IsErasable venv U Γ (b.inst a k) := by
  obtain ⟨T, hT, hT'⟩ := h
  refine ⟨T.inst a k, hT.instN henv W h₀, ?_⟩
  obtain hT' | ⟨u, hu, hu0⟩ := hT'
  · exact .inl hT'.inst
  · exact .inr ⟨u, hu.instN henv W h₀, hu0⟩

end

mutual
/-- Substitution for an index at or above every loose index is the identity. Reference:
`csubst_closed` (`MR E/ECSubst.v:165`). -/
theorem csubst_closed (t : LBTerm) : ∀ (b : LBTerm) {k : Nat}, closedn k b = true →
    csubst t k b = b
  | .box, _, _ | .fvar _, _, _ | .const _, _, _ | .prim _, _, _ => rfl
  | .bvar n, k, h => by
    simp only [closedn, decide_eq_true_eq] at h
    simp only [csubst]
    rw [if_neg (by omega), if_neg (by omega)]
  | .lambda _ b, _, h => by simp only [csubst, csubst_closed t b h]
  | .letIn _ b b', _, h => by
    simp only [closedn, Bool.and_eq_true] at h
    simp only [csubst, csubst_closed t b h.1, csubst_closed t b' h.2]
  | .app u v, _, h => by
    simp only [closedn, Bool.and_eq_true] at h
    simp only [csubst, csubst_closed t u h.1, csubst_closed t v h.2]
  | .construct _ _ args, _, h => by simp only [csubst, csubstL_closed t args h]
  | .case _ c brs, _, h => by
    simp only [closedn, Bool.and_eq_true] at h
    simp only [csubst, csubst_closed t c h.1, csubstB_closed t brs h.2]
  | .proj _ c, _, h => by simp only [csubst, csubst_closed t c h]
  | .fix defs _, _, h => by simp only [csubst, csubstD_closed t defs h]
/-- `csubst_closed` on argument lists. -/
theorem csubstL_closed (t : LBTerm) : ∀ (as : List LBTerm) {k : Nat}, closednL k as = true →
    csubstL t k as = as
  | [], _, _ => rfl
  | a :: as, _, h => by
    simp only [closednL, Bool.and_eq_true] at h
    simp only [csubstL, csubst_closed t a h.1, csubstL_closed t as h.2]
/-- `csubst_closed` on case branches. -/
theorem csubstB_closed (t : LBTerm) : ∀ (bs : List (List BinderName × LBTerm)) {k : Nat},
    closednB k bs = true → csubstB t k bs = bs
  | [], _, _ => rfl
  | (_, b) :: bs, _, h => by
    simp only [closednB, Bool.and_eq_true] at h
    simp only [csubstB, csubst_closed t b h.1, csubstB_closed t bs h.2]
/-- `csubst_closed` on fixpoint bodies. -/
theorem csubstD_closed (t : LBTerm) : ∀ (ds : List (@FixDef LBTerm)) {k : Nat},
    closednD k ds = true → csubstD t k ds = ds
  | [], _, _ => rfl
  | ⟨_, b, _⟩ :: ds, _, h => by
    simp only [closednD, Bool.and_eq_true] at h
    simp only [csubstD, csubst_closed t b h.1, csubstD_closed t ds h.2]
end

/-! ## Contexts -/

/-- Instantiating the innermost entry of `Δ₀`'s extension leaves `Δ₀` under `dk` de Bruijn
entries: the result context is a de Bruijn lift of `Δ₀` (`VLCtx.BVLift`,
`l4l Verify/Typing/Lemmas.lean:451`). Reference: none (lean4lean's contexts). -/
theorem VLCtx.InstN.bvLift (W : VLCtx.InstN Δ₀ e₀ A₀ dk k Δ₁ Δ) :
    VLCtx.BVLift Δ₀ Δ dk 0 k 0 := by
  induction W with
  | zero => exact .refl
  | @succ _ k _ _ d _ ih =>
    have := VLCtx.BVLift.skip (d.inst e₀ k) ih
    cases d <;> exact this

section
variable {venv : VEnv} {P : List ConstantInfo}

/-! ## Weakening -/

/-- The relation is stable under inserting de Bruijn entries (`VLCtx.BVLift`) below every loose
index of the source term, which the insertion leaves unchanged, and so is the λ□ side. Reference:
`erases_weakening'` (`MR E/ESubstitution.v:187`), for terms closed below the inserted entries. -/
theorem Erases.weakBV (henv : venv.Ordered) (W : VLCtx.BVLift Δ Δ' dn dk n k)
    (hc : Closed e dk) (h : Erases venv Us ac rc Δ e t) : Erases venv Us ac rc Δ' e t := by
  induction h generalizing Δ' dk k with
  | bvar => exact .bvar
  | fvar => exact .fvar
  | lam hA _ ih =>
    have hA' := hA.weakBV henv W
    rw [Expr.liftLooseBVars_eq_self hc.1.looseBVarRange_le] at hA'
    exact .lam hA' (ih (W.cons _) hc.2)
  | letE hT hv _ _ ihv ihb =>
    have hT' := hT.weakBV henv W
    have hv' := hv.weakBV henv W
    rw [Expr.liftLooseBVars_eq_self hc.1.looseBVarRange_le] at hT'
    rw [Expr.liftLooseBVars_eq_self hc.2.1.looseBVarRange_le] at hv'
    exact .letE hT' hv' (ihv W hc.2.1) (ihb (W.cons _) hc.2.2)
  | app _ _ ihf iha => exact .app (ihf W hc.1) (iha W hc.2)
  | const hc' => exact .const hc'
  | constRec hc' hr => exact .constRec hc' hr
  | mdata _ ih => exact .mdata (ih W hc)
  | box hb =>
    obtain ⟨e', he', hE⟩ := hb
    have he'' := he'.weakBV henv W
    rw [Expr.liftLooseBVars_eq_self hc.looseBVarRange_le] at he''
    exact .box ⟨_, he'', hE.weakN henv W.toCtx⟩

/-! ## Substitution -/

/-- Substitution under binders: instantiating the de Bruijn variable at depth `dk` of a `λ`-bound
entry (`VLCtx.InstN`) by a closed term `a` whose erasure is `ta` gives an erasure of the
instantiated term, the λ□ side substituted by `csubst ta dk`. Reference: `erases_subst`
(`MR E/ESubstitution.v:403`), for one closed substituted term. -/
theorem Erases.instN (henv : venv.Ordered) (hrc : RcClosed rc)
    (ha : Erases venv Us ac rc [] a ta) (hta : TrS venv Us [] a a'')
    (hA : venv.HasType Us.length [] a'' A') (W : VLCtx.InstN [] a'' A' dk k Δ₁ Δ)
    (hb : Erases venv Us ac rc Δ₁ b t) :
    Erases venv Us ac rc Δ (b.instantiate1' a dk) (csubst ta dk t) := by
  induction hb generalizing Δ dk k with
  | @bvar _ i =>
    simp only [Expr.instantiate1', csubst]
    by_cases h1 : i < dk
    · rw [if_pos h1, if_neg (by omega), if_neg (by omega)]
      exact .bvar
    · rw [if_neg h1]
      by_cases h2 : i = dk
      · subst h2
        rw [if_pos rfl, if_pos rfl]
        have hc : Closed a 0 := hta.closed
        rw [Expr.liftLooseBVars_eq_self hc.looseBVarRange_le]
        exact ha.weakBV henv (VLCtx.InstN.bvLift W) hc
      · rw [if_neg h2, if_neg (by omega), if_pos (by omega)]
        exact .bvar
  | fvar => exact .fvar
  | lam hA₁ _ ih =>
    exact .lam (hta.instN henv hA W hA₁) (ih (W.succ (d := .vlam _)))
  | letE hT hv _ _ ihv ihb =>
    exact .letE (hta.instN henv hA W hT) (hta.instN henv hA W hv) (ihv W)
      (ihb (W.succ (d := .vlet ..)))
  | app _ _ ihf iha => exact .app (ihf W) (iha W)
  | const hc => exact .const hc
  | constRec hc hr =>
    rw [csubst_closed ta _ (closedn_mono _ (Nat.zero_le _) (hrc _ _ hr))]
    exact .constRec hc hr
  | mdata _ ih => exact .mdata (ih W)
  | box hb =>
    obtain ⟨e', he', hE⟩ := hb
    exact .box ⟨_, hta.instN henv hA W he', hE.instN henv W.toCtx hA⟩

/-- Substituting an erased argument into an erased λ body. Reference: `erases_subst0`
(`MR E/ESubstitution.v:612`); Let. Lemma 16; MC p. 8:62 (closure under substitution). -/
theorem Erases.inst (henv : ProgEnv P venv) (hrc : RcClosed rc)
    (hb : Erases venv Us ac rc [(none, .vlam A')] b t) (ha : Erases venv Us ac rc [] a ta)
    (hta : TrS venv Us [] a a'') (hA : venv.HasType Us.length [] a'' A') :
    Erases venv Us ac rc [] (b.instantiate1' a) (csubst ta 0 t) :=
  match hb with
  | .box ⟨_, hb', hE⟩ =>
    .box ⟨_, hb'.inst henv.ordered hA hta, IsErasable.inst henv.ordered hA hE⟩
  | hb => Erases.instN henv.ordered hrc ha hta hA .zero hb

end

end EraseProof
