import EraseProof.Relation.Basic
import EraseProof.Typing.Abstract

/-!
# Closing a binder and substituting fix variables on the λ□ side

The shipping traversal is locally nameless: it opens a binder with a fresh free variable, erases
the body, and closes the result again, and it erases the members of a recursive block with one
free variable per member, which the block's `tFix` then replaces (DV-13). This module gives the
two λ□ operations and the two facts about the relation that these steps need:

- `abstract1`, the shifting abstraction of lean4lean's `Expr.abstract1` on `LBTerm`, and
  `Erases.uninstantiateN`: closing a binder on both sides keeps the relation;
- `substFVars`, a simultaneous substitution of free variables, and `Erases.substRc`: substituting
  the λ□ side turns the admissible targets `rc` of recursive constants into `rc'`.
-/

open Lean Lean4Lean Erasure

namespace EraseProof

mutual
/-- `x` becomes `bvar k`, loose indices `≥ k` are shifted up. Reference: lean4lean `Expr.abstract1`
(`l4l Verify/Axioms.lean:443`, a definition) on `LBTerm`; no MetaRocq counterpart (DV-13). -/
def abstract1 (x : FVarId) (k : Nat) : LBTerm → LBTerm
  | .box => .box
  | .bvar n => .bvar (if n < k then n else n + 1)
  | .fvar y => if x == y then .bvar k else .fvar y
  | .lambda na b => .lambda na (abstract1 x (k + 1) b)
  | .letIn na b b' => .letIn na (abstract1 x k b) (abstract1 x (k + 1) b')
  | .app u v => .app (abstract1 x k u) (abstract1 x k v)
  | .const kn => .const kn
  | .construct i n args => .construct i n (abstract1L x k args)
  | .case ip c brs => .case ip (abstract1 x k c) (abstract1B x k brs)
  | .proj p c => .proj p (abstract1 x k c)
  | .fix defs i => .fix (abstract1D x (k + defs.length) defs) i
  | .prim p => .prim p
/-- `abstract1` on argument lists (part of `abstract1`; no MetaRocq counterpart). -/
def abstract1L (x : FVarId) (k : Nat) : List LBTerm → List LBTerm
  | [] => []
  | a :: as => abstract1 x k a :: abstract1L x k as
/-- `abstract1` on case branches (part of `abstract1`; no MetaRocq counterpart). -/
def abstract1B (x : FVarId) (k : Nat) :
    List (List BinderName × LBTerm) → List (List BinderName × LBTerm)
  | [] => []
  | (ns, b) :: bs => (ns, abstract1 x (k + ns.length) b) :: abstract1B x k bs
/-- `abstract1` on fixpoint bodies (part of `abstract1`; no MetaRocq counterpart). -/
def abstract1D (x : FVarId) (k : Nat) : List (@FixDef LBTerm) → List (@FixDef LBTerm)
  | [] => []
  | ⟨nm, b, r⟩ :: ds => ⟨nm, abstract1 x k b, r⟩ :: abstract1D x k ds
end

mutual
/-- Simultaneous substitution of free variables (no shifting under binders): closes a block's fix
variables. Reference: none (DV-13). -/
def substFVars (s : FVarId → Option LBTerm) : LBTerm → LBTerm
  | .box => .box
  | .bvar n => .bvar n
  | .fvar y => (s y).getD (.fvar y)
  | .lambda na b => .lambda na (substFVars s b)
  | .letIn na b b' => .letIn na (substFVars s b) (substFVars s b')
  | .app u v => .app (substFVars s u) (substFVars s v)
  | .const kn => .const kn
  | .construct i n args => .construct i n (substFVarsL s args)
  | .case ip c brs => .case ip (substFVars s c) (substFVarsB s brs)
  | .proj p c => .proj p (substFVars s c)
  | .fix defs i => .fix (substFVarsD s defs) i
  | .prim p => .prim p
/-- `substFVars` on argument lists (part of `substFVars`; no MetaRocq counterpart). -/
def substFVarsL (s : FVarId → Option LBTerm) : List LBTerm → List LBTerm
  | [] => []
  | a :: as => substFVars s a :: substFVarsL s as
/-- `substFVars` on case branches (part of `substFVars`; no MetaRocq counterpart). -/
def substFVarsB (s : FVarId → Option LBTerm) :
    List (List BinderName × LBTerm) → List (List BinderName × LBTerm)
  | [] => []
  | (ns, b) :: bs => (ns, substFVars s b) :: substFVarsB s bs
/-- `substFVars` on fixpoint bodies (part of `substFVars`; no MetaRocq counterpart). -/
def substFVarsD (s : FVarId → Option LBTerm) : List (@FixDef LBTerm) → List (@FixDef LBTerm)
  | [] => []
  | ⟨nm, b, r⟩ :: ds => ⟨nm, substFVars s b, r⟩ :: substFVarsD s ds
end

/-- The targets of `rc` are closed and do not mention `x` (so abstraction leaves them unchanged).
Reference: none (DV-13). -/
def RcFresh (rc : Name → LBTerm → Prop) (x : FVarId) : Prop :=
  ∀ c t, rc c t → closedn 0 t = true ∧ hasFVar x t = false

mutual
/-- Abstraction leaves a term unchanged when its loose indices are below the depth and it does not
mention the variable. Reference: lean4lean `FVarsIn.abstract_eq_self`
(`l4l Verify/Typing/Lemmas.lean:105`) on `LBTerm`. -/
theorem abstract1_eq_self (x : FVarId) : ∀ (t : LBTerm) {k : Nat}, closedn k t = true →
    hasFVar x t = false → abstract1 x k t = t
  | .box, _, _, _ | .const _, _, _, _ | .prim _, _, _, _ => rfl
  | .bvar _, _, h, _ => by
    simp only [closedn, decide_eq_true_eq] at h
    simp only [abstract1, if_pos h]
  | .fvar _, _, _, h => by
    simp only [hasFVar] at h
    simp only [abstract1, h, Bool.false_eq_true, if_false]
  | .lambda _ b, _, h, h' => by
    simp only [closedn] at h
    simp only [hasFVar] at h'
    simp only [abstract1, abstract1_eq_self x b h h']
  | .letIn _ b b', _, h, h' => by
    simp only [closedn, Bool.and_eq_true] at h
    simp only [hasFVar, Bool.or_eq_false_iff] at h'
    simp only [abstract1, abstract1_eq_self x b h.1 h'.1, abstract1_eq_self x b' h.2 h'.2]
  | .app u v, _, h, h' => by
    simp only [closedn, Bool.and_eq_true] at h
    simp only [hasFVar, Bool.or_eq_false_iff] at h'
    simp only [abstract1, abstract1_eq_self x u h.1 h'.1, abstract1_eq_self x v h.2 h'.2]
  | .construct _ _ args, _, h, h' => by
    simp only [closedn] at h
    simp only [hasFVar] at h'
    simp only [abstract1, abstract1L_eq_self x args h h']
  | .case _ c brs, _, h, h' => by
    simp only [closedn, Bool.and_eq_true] at h
    simp only [hasFVar, Bool.or_eq_false_iff] at h'
    simp only [abstract1, abstract1_eq_self x c h.1 h'.1, abstract1B_eq_self x brs h.2 h'.2]
  | .proj _ c, _, h, h' => by
    simp only [closedn] at h
    simp only [hasFVar] at h'
    simp only [abstract1, abstract1_eq_self x c h h']
  | .fix defs _, _, h, h' => by
    simp only [closedn] at h
    simp only [hasFVar] at h'
    simp only [abstract1, abstract1D_eq_self x defs h h']
/-- `abstract1_eq_self` on argument lists. -/
theorem abstract1L_eq_self (x : FVarId) : ∀ (as : List LBTerm) {k : Nat},
    closednL k as = true → hasFVarL x as = false → abstract1L x k as = as
  | [], _, _, _ => rfl
  | a :: as, _, h, h' => by
    simp only [closednL, Bool.and_eq_true] at h
    simp only [hasFVarL, Bool.or_eq_false_iff] at h'
    simp only [abstract1L, abstract1_eq_self x a h.1 h'.1, abstract1L_eq_self x as h.2 h'.2]
/-- `abstract1_eq_self` on case branches. -/
theorem abstract1B_eq_self (x : FVarId) : ∀ (bs : List (List BinderName × LBTerm)) {k : Nat},
    closednB k bs = true → hasFVarB x bs = false → abstract1B x k bs = bs
  | [], _, _, _ => rfl
  | (_, b) :: bs, _, h, h' => by
    simp only [closednB, Bool.and_eq_true] at h
    simp only [hasFVarB, Bool.or_eq_false_iff] at h'
    simp only [abstract1B, abstract1_eq_self x b h.1 h'.1, abstract1B_eq_self x bs h.2 h'.2]
/-- `abstract1_eq_self` on fixpoint bodies. -/
theorem abstract1D_eq_self (x : FVarId) : ∀ (ds : List (@FixDef LBTerm)) {k : Nat},
    closednD k ds = true → hasFVarD x ds = false → abstract1D x k ds = ds
  | [], _, _, _ => rfl
  | ⟨_, b, _⟩ :: ds, _, h, h' => by
    simp only [closednD, Bool.and_eq_true] at h
    simp only [hasFVarD, Bool.or_eq_false_iff] at h'
    simp only [abstract1D, abstract1_eq_self x b h.1 h'.1, abstract1D_eq_self x ds h.2 h'.2]
end

section
variable {venv : VEnv}

/-- If `e` opened at depth `dk` with the free variable `x` is erasable under the free-variable entry
of `x`, then `e` is erasable under the de Bruijn entry that `VLCtx.Abstract` puts in its place:
the image by `TrS.uninstantiateN`, the typing context by lean4lean `VLCtx.Abstract.toCtx`
(`l4l Verify/Typing/Lemmas.lean:566`). Reference: none in MetaRocq (DV-13). -/
theorem ErasableS.uninstantiateN (W : VLCtx.Abstract Δ₀ x d₀ dk k Δ₁ Δ) (sc : FVarsIn (· ≠ x) e)
    (H : ErasableS venv Us Δ₁ (e.instantiate1' (.fvar x) dk)) : ErasableS venv Us Δ e :=
  let ⟨e', h1, h2⟩ := H
  ⟨e', h1.uninstantiateN W sc, W.toCtx ▸ h2⟩

/-- Closing a binder: the λ□ side is abstracted by the shifting `abstract1`. Reference: lean4lean
`TrExprS.uninstantiateN` (`l4l Verify/Typing/Lemmas.lean:2132`); none in MetaRocq (DV-13). -/
theorem Erases.uninstantiateN (W : VLCtx.Abstract Δ₀ x d₀ dk k Δ₁ Δ) (hrc : RcFresh rc x)
    (sc : FVarsIn (· ≠ x) e)
    (H : Erases venv Us ac rc Δ₁ (e.instantiate1' (.fvar x) dk) r) :
    Erases venv Us ac rc Δ e (abstract1 x dk r) := by
  induction e generalizing dk k Δ₁ Δ r with
  | bvar i =>
    have hbox (e₁ : Expr) (he : (Expr.bvar i).instantiate1' (.fvar x) dk = e₁)
        (hb : ErasableS venv Us Δ₁ e₁) : Erases venv Us ac rc Δ (.bvar i) (abstract1 x dk .box) :=
      .box (ErasableS.uninstantiateN W sc (he ▸ hb))
    by_cases h1 : i < dk
    · have he : (Expr.bvar i).instantiate1' (.fvar x) dk = .bvar i := by
        simp only [Expr.instantiate1', if_pos h1]
      rw [he] at H
      cases H with
      | bvar => simp only [abstract1, if_pos h1]; exact .bvar
      | box hb => exact hbox _ he hb
    · by_cases h2 : i = dk
      · have he : (Expr.bvar i).instantiate1' (.fvar x) dk = .fvar x := by
          simp only [Expr.instantiate1', if_neg h1, if_pos h2, Expr.liftLooseBVars']
        rw [he] at H
        cases H with
        | fvar => simp only [abstract1, beq_self_eq_true, if_true, h2]; exact .bvar
        | box hb => exact hbox _ he hb
      · have he : (Expr.bvar i).instantiate1' (.fvar x) dk = .bvar (i - 1) := by
          simp only [Expr.instantiate1', if_neg h1, if_neg h2]
        rw [he] at H
        cases H with
        | bvar =>
          simp only [abstract1, if_neg (show ¬ i - 1 < dk by omega),
            show i - 1 + 1 = i by omega]
          exact .bvar
        | box hb => exact hbox _ he hb
  | fvar y =>
    simp only [Expr.instantiate1'] at H
    cases H with
    | fvar =>
      have hxy : (x == y) = false := by simpa using (Ne.symm sc : x ≠ y)
      simp only [abstract1, hxy, Bool.false_eq_true, if_false]
      exact .fvar
    | box hb => exact .box (hb.uninstantiateN W sc)
  | mvar | sort | forallE | lit | proj =>
    simp only [Expr.instantiate1'] at H
    cases H with
    | box hb => exact .box (hb.uninstantiateN W sc)
  | const c us =>
    simp only [Expr.instantiate1'] at H
    cases H with
    | const hc => exact .const hc
    | constRec hc ht =>
      have ⟨h1, h2⟩ := hrc _ _ ht
      rw [abstract1_eq_self x _ (closedn_mono _ (Nat.zero_le _) h1) h2]
      exact .constRec hc ht
    | box hb => exact .box (hb.uninstantiateN W sc)
  | app f a ihf iha =>
    simp only [Expr.instantiate1'] at H
    cases H with
    | app hf ha => exact .app (ihf W sc.1 hf) (iha W sc.2 ha)
    | box hb => exact .box (hb.uninstantiateN W sc)
  | lam n A b bi _ ihb =>
    simp only [Expr.instantiate1'] at H
    cases H with
    | lam hA hb => exact .lam (hA.uninstantiateN W sc.1) (ihb W.succ sc.2 hb)
    | box hb => exact .box (hb.uninstantiateN W sc)
  | letE n T v b nd _ ihv ihb =>
    simp only [Expr.instantiate1'] at H
    cases H with
    | letE hT hv hv' hb =>
      exact .letE (hT.uninstantiateN W sc.1) (hv.uninstantiateN W sc.2.1) (ihv W sc.2.1 hv')
        (ihb W.succ sc.2.2 hb)
    | box hb => exact .box (hb.uninstantiateN W sc)
  | mdata d e ih =>
    simp only [Expr.instantiate1'] at H
    cases H with
    | mdata h => exact .mdata (ih W sc h)
    | box hb => exact .box (hb.uninstantiateN W sc)

/-- Target substitution: replacing free variables of the λ□ side turns the admissible targets `rc`
into `rc'`, provided no free variable of the source is replaced. Closes a block: inside it
`rc c t := t = .fvar (fixvar c)`, and `s := fixTargets xs defs`. Reference: none (DV-13). -/
theorem Erases.substRc {s : FVarId → Option LBTerm} (hsrc : FVarsIn (fun x => s x = none) e)
    (hrc : ∀ c t, rc c t → rc' c (substFVars s t)) (h : Erases venv Us ac rc Δ e r) :
    Erases venv Us ac rc' Δ e (substFVars s r) := by
  induction h with
  | bvar => exact .bvar
  | fvar =>
    rename_i x
    have hx : s x = none := hsrc
    simp only [substFVars, hx, Option.getD_none]
    exact .fvar
  | lam hA _ ih => exact .lam hA (ih hsrc.2)
  | letE hT hv _ _ ihv ihb => exact .letE hT hv (ihv hsrc.2.1) (ihb hsrc.2.2)
  | app _ _ ihf iha => exact .app (ihf hsrc.1) (iha hsrc.2)
  | const hc => exact .const hc
  | constRec hc hr => exact .constRec hc (hrc _ _ hr)
  | mdata _ ih => exact .mdata (ih hsrc)
  | box hb => exact .box hb

end

end EraseProof
