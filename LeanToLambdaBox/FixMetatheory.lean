import LeanToLambdaBox.Abstract

/-!
# `closeFix`: the `n`-way fvar → de Bruijn abstraction of a mutual `fix` block

Pure-`LBTerm` metatheory of the closing step the shipping `Erasure.mkDef`
(`LeanToLambdaBox/Erasure.lean:273`) performs. It imports only `Abstract`, the single-fvar
`toBvar` metatheory, and mentions no source-side notion.

## What the shipping code does

For a recursive mutual block `names = [n₀ … n₍ₘ₋₁₎]`, `Erasure.visitMutual` picks `m` fresh
fvars `ids = [x₀ … x₍ₘ₋₁₎]`, erases each def body with the sibling references `.const nₖ` mapped
to `.fvar xₖ` (`Erasure.visitConst`), then closes every body with `mkDef`, whose loop folds
`toBvar (fixvars[n]) i` over `fixvarnames.reverse.zipIdx`.

Because the block names zip with `ids` in order, that fold is `closeFix ids 0`: it sends the
**last** sibling `x₍ₘ₋₁₎ ↦ .bvar 0` and the **first** `x₀ ↦ .bvar (m-1)`, the de Bruijn
convention of the `.fix` node (`LBTerm.fix`), whose bodies live under `m` binders and refer to
sibling `k` by `.bvar (m-1-k)` — the convention `Semantics.Substitution`'s `fixSubst` inverts.

## What is proved

* `closeFixFold_eq_foldl`: the structural fold equals the `List.foldl` that `mkDef`'s `for`
  elaborates to. The `fixvars` lookup layer (`fixvars[nₖ] = xₖ`) is not proved here; it is a
  fact about the run, and `ErasureRun`/`LowerFix` carry it.
* `closeFix_not_hasFVar` and `hasFVar_closeFix_of`: closing removes exactly the block fvars and
  introduces none.
* `closeFixFold_fvar_head`, `closeFixFold_fvar_of_not_mem`, `closeFixFold_bvar`,
  `closeFixFold_app`: the per-constructor characterisation the index arithmetic rests on.
* `closeFix_2block_last`, `closeFix_2block_first`, `closeFix_2block_unfold` and the two
  `example`s beside them: the two-member block worked out concretely, so the sibling-index
  convention is witnessed rather than only asserted.
-/

namespace LeanToLambdaBox

open Lean

/-- Fold `toBvar` over a list of `(fvar, level)` closing instructions, innermost
(head) first — the pure form of the `mkDef` `for` loop (Erasure.lean:275). -/
def closeFixFold : List (FVarId × Nat) → LBTerm → LBTerm
  | [], t => t
  | (x, lvl) :: rest, t => closeFixFold rest (toBvar x lvl t)

/-- Simultaneously abstract the block fvars `ids = [x₀ … x₍ₘ₋₁₎]` at base level `base`,
sending the **last** sibling to `.bvar base` and the **first** to `.bvar (base+m-1)` —
the `n`-way generalisation of `abstract` and the exact closing performed by `mkDef`
(with `base = 0`). The `reverse.zipIdx` mirrors `mkDef`'s `fixvarnames.reverse.zipIdx`;
`base` shifts every target level (used when closing under further binders). -/
def closeFix (ids : List FVarId) (base : Nat) (t : LBTerm) : LBTerm :=
  closeFixFold (ids.reverse.zipIdx base) t

@[simp] theorem closeFixFold_nil (t : LBTerm) : closeFixFold [] t = t := rfl

theorem closeFixFold_cons (x : FVarId) (lvl : Nat) (rest : List (FVarId × Nat)) (t : LBTerm) :
    closeFixFold ((x, lvl) :: rest) t = closeFixFold rest (toBvar x lvl t) := rfl

/-! ### `closeFix` = the shipping `mkDef` fold

`mkDef`'s loop is `List.forIn … (fun (n,i) body => toBvar (fixvars[n]) i body)` over
`fixvarnames.reverse.zipIdx`. Modulo the `fixvars` lookup (`fixvars[nₖ] = xₖ` by
construction), that is `closeFixFold (ids.reverse.zipIdx)` — i.e. `closeFix ids 0`. We
record the fold-shape correspondence at the pure `(fvar, level)`-list level; the
`fixvars`-lookup layer is discharged in the (deferred) `visitMutual` reconciliation. -/

/-- A left fold of `toBvar` over an explicit pair list equals `closeFixFold`.  This is
the bridge from `mkDef`'s imperative `for` (which elaborates to `List.foldl` over
`reverse.zipIdx`) to the structural `closeFixFold`. -/
theorem closeFixFold_eq_foldl (pairs : List (FVarId × Nat)) (t : LBTerm) :
    closeFixFold pairs t = pairs.foldl (fun body p => toBvar p.1 p.2 body) t := by
  induction pairs generalizing t with
  | nil => rfl
  | cons p rest ih => obtain ⟨x, lvl⟩ := p; simp [closeFixFold, ih]

/-! ### `closeFix` is the identity on terms free of the block fvars

If none of the block fvars occur in `t`, closing is a no-op (each `toBvar` step is,
by `toBvar_eq_of_not_hasFVar`). Used to show that a def body already closed below the
fix binders is untouched, and for the base cases of the per-sibling characterisation. -/

theorem closeFixFold_eq_self_of_not_hasFVar (t : LBTerm) :
    ∀ (pairs : List (FVarId × Nat)), (∀ p ∈ pairs, ¬ hasFVar p.1 t) →
      closeFixFold pairs t = t := by
  intro pairs
  induction pairs generalizing t with
  | nil => intro _; rfl
  | cons p rest ih =>
    intro h
    obtain ⟨x, lvl⟩ := p
    have hx : ¬ hasFVar x t := h (x, lvl) (List.mem_cons_self ..)
    rw [closeFixFold_cons, toBvar_eq_of_not_hasFVar x lvl t hx]
    exact ih t (fun q hq => h q (List.mem_cons_of_mem _ hq))
/-! ### `closeFix` removes the block fvars and introduces none

The dual of the previous section, and the reason a `.fix` node the pass builds is closed at
**every** free variable: a closing step can only delete occurrences, and it deletes exactly
those of the variable it abstracts. The reflection form comes first — it is what keeps the
consumers free of a membership decision on `FVarId`. -/

/-- **Occurrence reflection for the fold.** A variable occurring in a closed term occurred in
the term before closing, and is none of the abstracted ones. -/
theorem hasFVar_closeFixFold_of {x : FVarId} :
    ∀ (pairs : List (FVarId × Nat)) (t : LBTerm),
      hasFVar x (closeFixFold pairs t) → x ∉ pairs.map Prod.fst ∧ hasFVar x t
  | [], t, h => ⟨by simp, h⟩
  | (y, lvl) :: rest, t, h => by
      rw [closeFixFold_cons] at h
      obtain ⟨hn, ht⟩ := hasFVar_closeFixFold_of rest _ h
      obtain ⟨hxy, ht'⟩ := hasFVar_toBvar_of x y lvl t ht
      refine ⟨?_, ht'⟩
      simp only [List.map_cons, List.mem_cons]
      rintro (rfl | hm)
      · exact hxy rfl
      · exact hn hm

/-- **Occurrence reflection for `closeFix`.** -/
theorem hasFVar_closeFix_of {x : FVarId} {ids : List FVarId} {base : Nat} {t : LBTerm}
    (h : hasFVar x (closeFix ids base t)) : x ∉ ids ∧ hasFVar x t := by
  rw [closeFix] at h
  obtain ⟨hn, ht⟩ := hasFVar_closeFixFold_of _ t h
  refine ⟨fun hm => hn ?_, ht⟩
  simp only [List.zipIdx_map_fst, List.mem_reverse]
  exact hm

/-- `closeFixFold` removes every variable of its pair list and introduces none. -/
theorem closeFixFold_not_hasFVar {x : FVarId} :
    ∀ (pairs : List (FVarId × Nat)) (t : LBTerm),
      (¬ hasFVar x t ∨ x ∈ pairs.map Prod.fst) → ¬ hasFVar x (closeFixFold pairs t) := by
  intro pairs t h hc
  obtain ⟨hn, ht⟩ := hasFVar_closeFixFold_of pairs t hc
  exact h.elim (fun h => h ht) hn

/-- `closeFix` removes every block identifier and introduces nothing. -/
theorem closeFix_not_hasFVar {x : FVarId} {ids : List FVarId} {base : Nat} {t : LBTerm}
    (h : ¬ hasFVar x t ∨ x ∈ ids) : ¬ hasFVar x (closeFix ids base t) := by
  intro hc
  obtain ⟨hn, ht⟩ := hasFVar_closeFix_of hc
  exact h.elim (fun h => h ht) hn

/-! ### Distinct-fvar bookkeeping for the per-sibling result

`toBvar y lvl` leaves `.fvar x` (`x ≠ y`) unchanged, and leaves any `.bvar` unchanged;
so once a fvar has been sent to its `.bvar`, the remaining closing steps do not touch
it, and steps for *other* fvars do not touch it beforehand. -/

theorem closeFixFold_bvar (i : Nat) :
    ∀ (pairs : List (FVarId × Nat)), closeFixFold pairs (.bvar i) = .bvar i := by
  intro pairs
  induction pairs with
  | nil => rfl
  | cons p rest ih => obtain ⟨x, lvl⟩ := p; rw [closeFixFold_cons]; simpa [toBvar] using ih

theorem closeFixFold_fvar_of_not_mem (x : FVarId) :
    ∀ (pairs : List (FVarId × Nat)), (∀ p ∈ pairs, p.1 ≠ x) →
      closeFixFold pairs (.fvar x) = .fvar x := by
  intro pairs h
  refine closeFixFold_eq_self_of_not_hasFVar (.fvar x) pairs (fun p hp => ?_)
  simp only [hasFVar_fvar]
  exact fun hxeq => h p hp hxeq.symm

/-- **Per-sibling abstraction.** If `x` is closed at level `lvl` by the *first* pair,
then `x ↦ .bvar lvl`, regardless of the remaining pairs (once `x` is a `.bvar`, every
subsequent `toBvar` is a no-op, `closeFixFold_bvar`). This is the single-step core; it
instantiates at the position of each block fvar in the `reverse.zipIdx` (`closeFix`). -/
theorem closeFixFold_fvar_head (x : FVarId) (lvl : Nat) (rest : List (FVarId × Nat)) :
    closeFixFold ((x, lvl) :: rest) (.fvar x) = .bvar lvl := by
  rw [closeFixFold_cons]
  have hxx : (x == x) = true := fvarId_beq_iff_eq.mpr rfl
  have : toBvar x lvl (.fvar x) = .bvar lvl := by simp only [toBvar, if_pos hxx]
  rw [this, closeFixFold_bvar]

/-! ### Non-vacuity: a concrete 2-def block closes to the `mkDef` convention

`ids = [x₀, x₁]` (block of 2), base 0. `closeFix` folds `[(x₁,0),(x₀,1)]`:
* the last sibling `x₁ ↦ .bvar 0`,
* the first sibling `x₀ ↦ .bvar 1`.
So a body `x₀ x₁` (def 0 calling itself then its sibling) closes to `.bvar 1 .bvar 0`
— exactly what the `.fix` node expects (sibling `k ↦ .bvar (m-1-k)`, here m = 2). -/

/-- `closeFixFold` distributes over application (each `toBvar` does). -/
theorem closeFixFold_app (a b : LBTerm) :
    ∀ (pairs : List (FVarId × Nat)),
      closeFixFold pairs (.app a b) = .app (closeFixFold pairs a) (closeFixFold pairs b) := by
  intro pairs
  induction pairs generalizing a b with
  | nil => rfl
  | cons p rest ih => obtain ⟨x, lvl⟩ := p; rw [closeFixFold_cons, closeFixFold_cons,
      closeFixFold_cons, toBvar]; exact ih _ _

/-- The closing instruction list for a 2-block: `[(x₁, 0), (x₀, 1)]`. -/
example (x₀ x₁ : FVarId) :
    [x₀, x₁].reverse.zipIdx 0 = [(x₁, 0), (x₀, 1)] := rfl

/-- Last sibling `x₁ ↦ .bvar 0`. -/
theorem closeFix_2block_last (x₀ x₁ : FVarId) :
    closeFixFold [(x₁, 0), (x₀, 1)] (.fvar x₁) = .bvar 0 :=
  closeFixFold_fvar_head x₁ 0 [(x₀, 1)]

/-- First sibling `x₀ ↦ .bvar 1`. -/
theorem closeFix_2block_first (x₀ x₁ : FVarId) (h : x₀ ≠ x₁) :
    closeFixFold [(x₁, 0), (x₀, 1)] (.fvar x₀) = .bvar 1 := by
  rw [closeFixFold_cons,
    toBvar_eq_of_not_hasFVar x₁ 0 (.fvar x₀) (by simp only [hasFVar_fvar]; exact h)]
  exact closeFixFold_fvar_head x₀ 1 []

/-- The `closeFix` closing list unfolds to `[(x₁, 0), (x₀, 1)]` for a 2-block. -/
theorem closeFix_2block_unfold (x₀ x₁ : FVarId) (t : LBTerm) :
    closeFix [x₀, x₁] 0 t = closeFixFold [(x₁, 0), (x₀, 1)] t := rfl

/-- A whole def body `x₀ x₁` (self-call applied to sibling-call) closes to the
`.fix`-ready `.bvar 1 .bvar 0`. Concrete witness that `closeFix` produces exactly the
sibling-index convention the semantics' `fixSubst` inverts (sibling `k ↦ .bvar (m-1-k)`,
m = 2). -/
example (x₀ x₁ : FVarId) (h : x₀ ≠ x₁) :
    closeFix [x₀, x₁] 0 (.app (.fvar x₀) (.fvar x₁)) = .app (.bvar 1) (.bvar 0) := by
  rw [closeFix_2block_unfold, closeFixFold_app, closeFix_2block_first x₀ x₁ h,
    closeFix_2block_last x₀ x₁]

end LeanToLambdaBox
