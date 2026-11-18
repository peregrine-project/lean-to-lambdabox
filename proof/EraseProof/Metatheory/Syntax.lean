import Metalean.Syntax.Substitution
import Metalean.Syntax.Structure.Projection

/-!
# Syntactic facts about Metalean's terms

Lemmas about Metalean's application spines, weakening, level instantiation, recursor binders,
structure projections and large elimination that the proofs use. Metalean
(`https://github.com/intgrah/metalean`, distributed under the Apache License 2.0) stated most of
them up to commit `9407ba4407374a05e90777a068c2dc520e4ac0e7` and no longer does at the pinned
revision. Each docstring names the file of `9407ba4` that stated it and says whether the proof is
the one there, adapted from there, or new.
-/

namespace EraseProof.ML

open Metalean

variable {ζ ζ₁ ζ₂ : Sigs} {ℓ ℓ' n m k : Nat}

/-- Peeling the first argument off an application spine. Stated and proved as here in Metalean
`9407ba4`, `Metalean/Syntax/Expr/Application.lean:50` (`Expr.apps_succ`). -/
theorem Expr.apps_succ (η : Metalean.Expr ζ ℓ n) (args : Fin (k + 1) → Metalean.Expr ζ ℓ n) :
    η.apps args = (η.app (args 0)).apps fun i => args i.succ :=
  Fin.foldl_succ ..

/-- A signature morphism commutes with application to a list. Metalean `9407ba4`,
`Metalean/Syntax/Expr/Application.lean:74` (`Expr.map_appList`); the proof, by induction on the
list, is new. -/
@[simp] theorem Expr.map_appList (pre : ζ₁ ⟶ ζ₂) (η : Metalean.Expr ζ₁ ℓ n)
    (args : List (Metalean.Expr ζ₁ ℓ n)) :
    (η.appList args).map pre = (η.map pre).appList (args.map (Metalean.Expr.map pre)) := by
  induction args generalizing η with
  | nil => rfl
  | cons a as ih => exact ih (η.app a)

/-- Level instantiation commutes with application to a list. Metalean `9407ba4`,
`Metalean/Syntax/Expr/Application.lean:80` (`Expr.instL_appList`); the proof, by induction on the
list, is new. -/
@[simp] theorem Expr.instL_appList (ls : Param ℓ → Metalean.Level ℓ') (η : Metalean.Expr ζ ℓ n)
    (args : List (Metalean.Expr ζ ℓ n)) :
    (η.appList args){ls} = η{ls}.appList args{ls} := by
  induction args generalizing η with
  | nil => rfl
  | cons a as ih => exact ih (η.app a)

/-- Substitution commutes with application to a list. Metalean `9407ba4`,
`Metalean/Syntax/Substitution.lean:28` (`Expr.subst_appList`); the proof, by induction on the
list, is new. -/
@[simp] theorem Expr.subst_appList (σ : Subst ζ ℓ m n) (e : Metalean.Expr ζ ℓ m)
    (args : List (Metalean.Expr ζ ℓ m)) :
    (e.appList args).subst σ = (e.subst σ).appList (args.map fun arg => arg.subst σ) := by
  induction args generalizing e with
  | nil => rfl
  | cons a as ih => exact ih (e.app a)

/-- Weakening at `cut ≤ n` sends the last variable to the last variable. Metalean `9407ba4`,
`Metalean/Syntax/Weakening.lean:102` (`Expr.last_wkFrom`); the proof, by unfolding the renaming,
is new. -/
@[simp] theorem Expr.last_wkFrom {cut : Nat} (h : cut ≤ n) :
    (Metalean.Expr.var (Fin.last n) : Metalean.Expr ζ ℓ (n + 1)).wkFrom cut =
      .var (Fin.last (n + 1)) := by
  simp only [Metalean.Expr.wkFrom, Metalean.Expr.rename, Ren.wkFrom]
  rw [dite_eq_right (by simp; omega)]
  rfl

/-- Weakening commutes with `let`. Stated and proved as here in Metalean `9407ba4`,
`Metalean/Syntax/Weakening.lean:130` (`Expr.wkFrom_letE`). -/
@[simp] theorem Expr.wkFrom_letE {cut : Nat} (h : cut ≤ n) (t v : Metalean.Expr ζ ℓ n)
    (e' : Metalean.Expr ζ ℓ (n + 1)) :
    (Metalean.Expr.letE t v e').wkFrom cut =
      Metalean.Expr.letE (t.wkFrom cut) (v.wkFrom cut) (e'.wkFrom cut) := by
  simp [Metalean.Expr.wkFrom, Ren.wkFrom_lift cut h]

/-- Weakening commutes with instantiating the last variable. Metalean `9407ba4`,
`Metalean/Syntax/Weakening.lean:150` (`Expr.inst_wkFrom`); the proof is adapted from there. -/
@[simp] theorem Expr.inst_wkFrom {cut : Nat} (h : cut ≤ n) (t' : Metalean.Expr ζ ℓ (n + 1))
    (e : Metalean.Expr ζ ℓ n) :
    (t'.inst e).wkFrom cut = (t'.wkFrom cut).inst (e.wkFrom cut) := by
  change (t'.subst _).wkFrom cut = (t'.wkFrom cut).subst _
  rw [Metalean.Expr.subst_wkFrom, Metalean.Expr.wkFrom_subst]
  congr 1
  funext v
  change Metalean.Expr.wkFrom cut (dite _ _ _) = dite _ _ _
  by_cases hv : v.val < n
  · have hs : (Ren.wkFrom cut v).val < n + 1 := by
      by_cases hc : v.val < cut
      · simp [hc]
      · simpa [Ren.wkFrom, hc] using hv
    rw [dite_eq_left hv, dite_eq_left hs]
    simp [Subst.id]
    by_cases hc : v.val < cut
    · rw [ite_eq_left hc]
      apply congrArg Metalean.Expr.var
      apply Fin.ext
      simp [hc]
    · rw [ite_eq_right hc]
      apply congrArg Metalean.Expr.var
      apply Fin.ext
      simp [Ren.wkFrom, hc]
  · have hs : ¬(Ren.wkFrom cut v).val < n + 1 := by
      have hvn : v.val = n := by omega
      rw [Ren.wkFrom_of_ge v (by omega)]
      simp [hvn]
    rw [dite_eq_right hv, dite_eq_right hs]
    simp

/-- Inserting a type below an extended context. Stated and proved as here in Metalean `9407ba4`,
`Metalean/Syntax/Weakening.lean:297` (`Ctx.insert_snoc`). -/
@[simp] theorem Ctx.insert_snoc {cutPos : Nat} (Γ : Metalean.Ctx ζ ℓ 0 cutPos)
    (t : Metalean.Expr ζ ℓ cutPos) (Δ : Metalean.Ctx ζ ℓ cutPos n) (t₁ : Metalean.Expr ζ ℓ n) :
    Γ.insert t (Δ.snoc t₁) = (Γ.insert t Δ).snoc (t₁.wkFrom cutPos) := rfl

/-- Inserting a type below the empty telescope extends the context. Stated and proved as here in
Metalean `9407ba4`, `Metalean/Syntax/Weakening.lean:301` (`Ctx.insert_nil`). -/
@[simp] theorem Ctx.insert_nil (Γ : Metalean.Ctx ζ ℓ 0 n) (t : Metalean.Expr ζ ℓ n) :
    Γ.insert t (.nil : Metalean.Ctx ζ ℓ n n) = Γ.snoc t := rfl

/-- Level instantiation commutes with `max`. Stated and proved as here in Metalean `9407ba4`,
`Metalean/Level/Quot/Basic.lean:127` (`Level.inst_max`). -/
@[simp] theorem Level.inst_max {ℓ₁ : Nat} (σ : Param ℓ → Metalean.Level ℓ₁)
    (u v : Metalean.Level ℓ) : (u.max v){σ} = u{σ}.max v{σ} := by
  rcases u
  rcases v
  rfl

/-- Level instantiation commutes with the motive binders of a recursor. Stated and proved as here
in Metalean `9407ba4`, `Metalean/Syntax/Inductive/Recursor.lean:346`
(`Inductive.motiveBinders_instL`). -/
@[simp] theorem Inductive.motiveBinders_instL {ι : IndSig} {I : Metalean.Inductive ζ ι}
    {η : Head ζ (.inductive ι)} {ls : Fin ι.nlevels → Metalean.Level ℓ} {l : Metalean.Level ℓ}
    {ls' : Param ℓ → Metalean.Level ℓ'} :
    (I.motiveBinders η ls l){ls'} = I.motiveBinders η ls{ls'} l{ls'} := by
  simp! [Metalean.Inductive.motiveBinders, InstLevel.inst_tuple]

/-- A signature morphism commutes with the motive binders of a recursor. Stated and proved as here
in Metalean `9407ba4`, `Metalean/Syntax/Inductive/Recursor.lean:316` (`Inductive.motiveBinders_map`,
private there). -/
@[simp] theorem Inductive.motiveBinders_map {ι : IndSig} (I : Metalean.Inductive ζ₁ ι)
    (pre : ζ₁ ⟶ ζ₂) (η : Head ζ₁ (.inductive ι)) (ls : Fin ι.nlevels → Metalean.Level ℓ)
    (l : Metalean.Level ℓ) :
    (I.motiveBinders η ls l).map pre = (I.map pre).motiveBinders (η.map pre) ls l :=
  (Metalean.Ctx.ofTypes_map _ pre).trans <| by simp! [Metalean.Inductive.motiveBinders]

/-- Weakening commutes with a structure projection. Metalean `9407ba4`,
`Metalean/Syntax/Structure/Projection.lean:243` (`Inductive.IsStructure.projTerm_wkFrom`); here
the proof, from the substitution lemma `IsStructure.projTerm_subst`, is new. -/
@[simp] theorem Inductive.IsStructure.projTerm_wkFrom {ι : IndSig} {s : Fin ι.nsorts}
    {c : Fin (ι.nctors s)} {I : Metalean.Inductive ζ ι} (h : I.IsStructure s c)
    (η : Head ζ (.inductive ι)) (ls : Fin ι.nlevels → Metalean.Level ℓ)
    (ps : Fin ι.nparams → Metalean.Expr ζ ℓ n) (f : Fin (ι.ctors s c).nfields)
    (maj : Metalean.Expr ζ ℓ n) (cut : Nat) :
    (h.projTerm η ls ps f maj).wkFrom cut =
      h.projTerm η ls (fun param => (ps param).wkFrom cut) f (maj.wkFrom cut) := by
  simp only [Metalean.Expr.wkFrom_eq_subst]
  exact h.projTerm_subst η ls ps f maj _

/-- A large-eliminating block whose level is zero at some assignment is a subsingleton: it is not
of level `≥ 1`. Metalean `0146928` proves this inline in
`IsStructure.ordinaryLevel_eq_zero_of_eval_zero` (`Metalean/Syntax/Structure.lean:290`), and the
proof is adapted from there; Metalean `9407ba4` stated it per sort as
`SortLargeElim.singleton_of_eval_zero` (`Metalean/Syntax/Inductive/LargeElimination.lean:154`). -/
theorem Inductive.LargeElim.subsingleton_of_eval_zero {ι : IndSig} {I : Metalean.Inductive ζ ι}
    (h : I.LargeElim) (ls : Fin ι.nlevels → Metalean.Level ℓ) {ν : Param ℓ → Nat}
    (hzero : (I.level{ls}).eval ν = 0) : I.Subsingleton := by
  rcases h with h | hlevel
  · exact h
  · have hpositive : 1 ≤ (I.level{ls}).eval ν := by
      rw [Metalean.Level.eval_inst]
      exact hlevel fun p => (ls p).eval ν
    omega

/-- A large-eliminating block whose level is zero at some assignment has exactly one constructor
per sort, whose fields are eligible (`Ctor.Eligible`). Metalean `9407ba4`,
`Metalean/Syntax/Inductive/LargeElimination.lean:154` (`SortLargeElim.singleton_of_eval_zero`),
there for one sort. -/
theorem Inductive.LargeElim.singleton_of_eval_zero {ι : IndSig} {I : Metalean.Inductive ζ ι}
    (h : I.LargeElim) (ls : Fin ι.nlevels → Metalean.Level ℓ) {ν : Param ℓ → Nat}
    (hzero : (I.level{ls}).eval ν = 0) {s : Fin ι.nsorts} (c : Fin (ι.nctors s)) :
    ι.nctors s = 1 ∧ (I.ctors s c).Eligible I.level :=
  have hsub := subsingleton_of_eval_zero h ls hzero
  ⟨hsub.nctors_eq_one c, hsub.eligible s c⟩

end EraseProof.ML
