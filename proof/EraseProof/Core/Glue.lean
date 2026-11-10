import EraseProof.Core.Scope
import EraseProof.Relation.Abstract
import LeanToLambdaBox.Erasure.Entry

/-!
# Glue between the shipping code and the specification

Three facts that tie shipping functions to the definitions the proof reasons about:

- `eraseEntry_pure`: on an in-scope input, a result of the `#erase` entry point
  `Erasure.eraseEntry` is a result of the pure path (`Erasure.collectDeps`, then
  `Erasure.erasePure`). The `CoreM` lemmas it needs (`CoreM.pure_inj`, `CoreM.throwError_ne_pure`,
  `EIO.bind_err`) run a `CoreM` action at an arbitrary context, state reference and world token
  (`someCtx`, `someRef`, `someW`).
- `isRecursiveDecl_eq`: the pure backend's recursion test `Erasure.isRecursiveDecl` is
  `RecursiveDecl` (DV-7).
- `abstract_eq_abstract1`: on a term without loose indices, the traversal's non-shifting
  `abstract` (`toBvar` at depth `0`) is the shifting `abstract1` (DV-13).
-/

open Lean Lean4Lean Erasure

namespace EraseProof

/-! ## `#erase` and the pure path -/

/-- An arbitrary `CoreM` context (glue for the `CoreM` lemmas). -/
noncomputable def someCtx : Core.Context := Classical.choice inferInstance
/-- An arbitrary `CoreM` state reference (glue). -/
noncomputable def someRef : ST.Ref IO.RealWorld Core.State := Classical.choice inferInstance
/-- An arbitrary world token (glue). -/
noncomputable def someW : Void IO.RealWorld := Classical.choice inferInstance

/-- `pure` is injective in `CoreM` (proved). Reference: none (glue). -/
theorem CoreM.pure_inj {α} {a b : α} (h : (pure a : CoreM α) = pure b) : a = b := by
  have h' := congrFun (congrFun (congrFun h someCtx) someRef) someW
  injection h'

/-- An `EIO` bind whose continuation always fails always fails (proved). Reference: none (glue). -/
theorem EIO.bind_err {ε α β : Type} (x : EIO ε β) (f : β → EIO ε α)
    (hf : ∀ b s, ∃ e s', f b s = .error e s') (s : Void IO.RealWorld) :
    ∃ e s', (x >>= f) s = .error e s' := by
  show ∃ e s', (EST.bind x f) s = _
  simp only [EST.bind]
  split
  · exact hf _ _
  · exact ⟨_, _, rfl⟩

/-- An error is not a result in `CoreM` (proved). Reference: none (glue). -/
theorem CoreM.throwError_ne_pure {α} {a : α} {m : MessageData} :
    (Lean.throwError m : CoreM α) ≠ pure a := by
  intro h
  have h' := congrFun (congrFun (congrFun h someCtx) someRef) someW
  have : ∃ e s', (Lean.throwError m : CoreM α) someCtx someRef someW = .error e s' := by
    simp only [Lean.throwError, bind, ReaderT.bind, getRef, MonadRef.getRef]
    apply EIO.bind_err
    intro r s
    apply EIO.bind_err
    intro r s
    exact ⟨_, _, rfl⟩
  obtain ⟨e, s', he⟩ := this
  rw [h'] at he
  cases he

/-- `#erase` glue (proved from the routing lemma): on an in-scope input, a result of the entry
point is a result of the pure path. Reference: none. -/
theorem eraseEntry_pure {view : EnvView} {cfg : ErasureConfig} {r}
    (hin : InScope view e) (hrun : eraseEntry view cfg e = pure r) :
    ∃ decls, collectDeps view e = .ok decls ∧ erasePure view cfg decls e = .ok r := by
  match hc : collectDeps view e with
  | .ok decls =>
    refine ⟨decls, rfl, ?_⟩
    match hp : erasePure view cfg decls e with
    | .ok r' =>
      simp only [eraseEntry, route, hc, hp] at hrun
      exact congrArg _ (CoreM.pure_inj hrun)
    | .error _ =>
      simp only [eraseEntry, route, hc, hp] at hrun
      exact absurd hrun CoreM.throwError_ne_pure
  | .error err =>
    exfalso
    cases err with
    | outOfFragment w => exact collectDeps_not_outOfFragment hin w hc
    | _ => simp [eraseEntry, route, hc] at hrun; exact CoreM.throwError_ne_pure hrun

/-! ## The recursion test -/

/-- The pure backend's occurrence test `Erasure.nameOccurs` is `OccursV`: the two have the same
equations. Reference: none (DV-7). -/
theorem nameOccurs_eq_OccursV (n : Name) : ∀ e, nameOccurs n e = OccursV n e := by
  intro e
  induction e <;> simp_all [nameOccurs, OccursV]

/-- The traversal's recursion test is the specification's `RecursiveDecl`. Reference: none
(DV-7). -/
theorem isRecursiveDecl_eq : Erasure.isRecursiveDecl ci = RecursiveDecl ci := by
  simp only [isRecursiveDecl, RecursiveDecl, nameOccurs_eq_OccursV]

/-! ## Closing a binder -/

mutual
/-- On a term whose loose indices are below `k`, the traversal's `toBvar x k` is `abstract1 x k`:
neither changes those indices, and both send `x` to `bvar k`. Reference: none (DV-13). -/
theorem toBvar_eq_abstract1 (x : FVarId) : ∀ (t : LBTerm) {k : Nat}, closedn k t = true →
    toBvar x k t = abstract1 x k t
  | .box, _, _ | .const _, _, _ | .prim _, _, _ => by simp only [toBvar, abstract1]
  | .bvar _, _, h => by
    simp only [closedn, decide_eq_true_eq] at h
    simp only [toBvar, abstract1, if_pos h]
  | .fvar y, _, _ => by
    simp only [toBvar, abstract1]
    by_cases hxy : x = y
    · subst hxy; simp
    · have hyx : ¬y = x := fun h => hxy h.symm
      simp [hxy, hyx]
  | .lambda _ b, _, h => by
    simp only [closedn] at h
    simp only [toBvar, abstract1, toBvar_eq_abstract1 x b h]
  | .letIn _ b b', _, h => by
    simp only [closedn, Bool.and_eq_true] at h
    simp only [toBvar, abstract1, toBvar_eq_abstract1 x b h.1, toBvar_eq_abstract1 x b' h.2]
  | .app u v, _, h => by
    simp only [closedn, Bool.and_eq_true] at h
    simp only [toBvar, abstract1, toBvar_eq_abstract1 x u h.1, toBvar_eq_abstract1 x v h.2]
  | .construct _ _ args, _, h => by
    simp only [closedn] at h
    simp only [toBvar, abstract1, toBvarList_eq_abstract1L x args h]
  | .case (_, _) c brs, _, h => by
    simp only [closedn, Bool.and_eq_true] at h
    simp only [toBvar, abstract1, toBvar_eq_abstract1 x c h.1, toBvarAlts_eq_abstract1B x brs h.2]
  | .proj _ c, _, h => by
    simp only [closedn] at h
    simp only [toBvar, abstract1, toBvar_eq_abstract1 x c h]
  | .fix defs _, _, h => by
    simp only [closedn] at h
    simp only [toBvar, abstract1, toBvarDefs_eq_abstract1D x defs h]
/-- `toBvar_eq_abstract1` on argument lists. -/
theorem toBvarList_eq_abstract1L (x : FVarId) : ∀ (as : List LBTerm) {k : Nat},
    closednL k as = true → toBvarList x k as = abstract1L x k as
  | [], _, _ => rfl
  | a :: as, _, h => by
    simp only [closednL, Bool.and_eq_true] at h
    simp only [toBvarList, abstract1L, toBvar_eq_abstract1 x a h.1,
      toBvarList_eq_abstract1L x as h.2]
/-- `toBvar_eq_abstract1` on case branches. -/
theorem toBvarAlts_eq_abstract1B (x : FVarId) : ∀ (bs : List (List BinderName × LBTerm)) {k : Nat},
    closednB k bs = true → toBvarAlts x k bs = abstract1B x k bs
  | [], _, _ => rfl
  | (_, b) :: bs, _, h => by
    simp only [closednB, Bool.and_eq_true] at h
    simp only [toBvarAlts, abstract1B, toBvar_eq_abstract1 x b h.1,
      toBvarAlts_eq_abstract1B x bs h.2]
/-- `toBvar_eq_abstract1` on fixpoint bodies. -/
theorem toBvarDefs_eq_abstract1D (x : FVarId) : ∀ (ds : List (@FixDef LBTerm)) {k : Nat},
    closednD k ds = true → toBvarDefs x k ds = abstract1D x k ds
  | [], _, _ => rfl
  | ⟨_, b, _⟩ :: ds, _, h => by
    simp only [closednD, Bool.and_eq_true] at h
    simp only [toBvarDefs, abstract1D, toBvar_eq_abstract1 x b h.1,
      toBvarDefs_eq_abstract1D x ds h.2]
end

/-- The traversal's non-shifting abstraction (shipping `abstract` and `toBvar`) agrees with
`abstract1` on closed terms. Reference: none (DV-13). -/
theorem abstract_eq_abstract1 (h : closedn 0 r = true) : _root_.abstract x r = abstract1 x 0 r :=
  toBvar_eq_abstract1 x r h

end EraseProof
