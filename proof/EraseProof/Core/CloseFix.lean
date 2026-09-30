import EraseProof.Relation.Abstract

/-!
# Closing a recursive block: `mkDef`'s loop

The traversal erases the members of a recursive block with one free variable per member and then
closes each erased body with `mkDef`'s loop of the shipping non-shifting `toBvar`
(`LeanToLambdaBox/Basic.lean`), which sends the fix variable of member `j` of an `m`-member block
to `bvar (m-1-j)` (DV-13). This module states the loop as `closeFix` and proves the two facts the
block step of the traversal's correctness proof needs:

- `closeFix_closed`: a closed body, closed by the loop, has no loose index beyond the block's
  binders;
- `closeFix_substl`: instantiating the loop's result as `cunfold_fix` does
  (`substl (fixSubst defs)`) replaces fix variable `xs[j]` by `tFix defs j` (`fixTargets`).

The loop is stated as a whole: its later steps abstract at indices above `0`, which
`abstract_eq_abstract1` (the traversal's `abstract`, at index `0`) does not cover. The proof goes
through two simultaneous operations: `toBvars`, which abstracts all fix variables at once (the
loop computes it, `closeFix_eq_toBvars`), and `psubst`, MetaRocq's parallel substitution `subst`,
which `substl` computes on closed terms (`substl_eq_psubst`, MetaRocq `substl_subst`);
`psubst_toBvars` relates the two to `substFVars`.
-/

open Lean Erasure

namespace EraseProof

/-- `mkDef`'s closing loop (shipping `Erasure.lean` `mkDef`): the fix variable of member `j` of an
`m`-member block becomes `bvar (m-1-j)`, by the shipping non-shifting `toBvar` (made total by S-A).
Reference: none; MetaRocq's `erase` builds `tFix` bodies de Bruijn (DV-13). -/
def closeFix (xs : List FVarId) (r : LBTerm) : LBTerm :=
  (xs.reverse.zipIdx).foldl (fun b (x, i) => toBvar x i b) r

/-- The fixpoint targets of a block's fix variables: `xs[j] ↦ tFix defs j`. Reference: none
(DV-13). -/
def fixTargets (xs : List FVarId) (defs : List (@FixDef LBTerm)) : FVarId → Option LBTerm :=
  fun x => (xs.idxOf? x).map (.fix defs ·)

/-! ## Simultaneous non-shifting abstraction -/

mutual
/-- Simultaneous non-shifting abstraction: at binder depth `d`, `fvar y` with `f y = some k`
becomes `bvar (k + d)`; other free variables and all loose indices are unchanged. `closeFix`
computes it (`closeFix_eq_toBvars`). Reference: none; the shipping `toBvar`
(`LeanToLambdaBox/Basic.lean`) for several variables at once (DV-13). -/
def toBvars (f : FVarId → Option Nat) (d : Nat) : LBTerm → LBTerm
  | .box => .box
  | .bvar n => .bvar n
  | .fvar y => match f y with | some k => .bvar (k + d) | none => .fvar y
  | .lambda na b => .lambda na (toBvars f (d + 1) b)
  | .letIn na b b' => .letIn na (toBvars f d b) (toBvars f (d + 1) b')
  | .app u v => .app (toBvars f d u) (toBvars f d v)
  | .const kn => .const kn
  | .construct i n args => .construct i n (toBvarsL f d args)
  | .case ip c brs => .case ip (toBvars f d c) (toBvarsB f d brs)
  | .proj p c => .proj p (toBvars f d c)
  | .fix defs i => .fix (toBvarsD f (d + defs.length) defs) i
  | .prim p => .prim p
/-- `toBvars` on argument lists (part of `toBvars`). -/
def toBvarsL (f : FVarId → Option Nat) (d : Nat) : List LBTerm → List LBTerm
  | [] => []
  | a :: as => toBvars f d a :: toBvarsL f d as
/-- `toBvars` on case branches, under each branch's binders (part of `toBvars`). -/
def toBvarsB (f : FVarId → Option Nat) (d : Nat) :
    List (List BinderName × LBTerm) → List (List BinderName × LBTerm)
  | [] => []
  | (ns, b) :: bs => (ns, toBvars f (d + ns.length) b) :: toBvarsB f d bs
/-- `toBvars` on fixpoint bodies (part of `toBvars`). -/
def toBvarsD (f : FVarId → Option Nat) (d : Nat) : List (@FixDef LBTerm) → List (@FixDef LBTerm)
  | [] => []
  | ⟨nm, b, r⟩ :: ds => ⟨nm, toBvars f d b, r⟩ :: toBvarsD f d ds
end

/-- `toBvarsD` keeps the number of fixpoint bodies. -/
theorem toBvarsD_length (f : FVarId → Option Nat) (d : Nat) :
    ∀ ds : List (@FixDef LBTerm), (toBvarsD f d ds).length = ds.length
  | [] => rfl
  | ⟨_, _, _⟩ :: ds => by simp only [toBvarsD, List.length_cons, toBvarsD_length f d ds]

mutual
/-- `toBvars` with the empty map is the identity. -/
theorem toBvars_none : ∀ (t : LBTerm) (d : Nat), toBvars (fun _ => none) d t = t
  | .box, _ | .const _, _ | .prim _, _ | .bvar _, _ | .fvar _, _ => rfl
  | .lambda _ b, d => by simp only [toBvars, toBvars_none b]
  | .letIn _ b b', d => by simp only [toBvars, toBvars_none b, toBvars_none b']
  | .app u v, d => by simp only [toBvars, toBvars_none u, toBvars_none v]
  | .construct _ _ args, d => by simp only [toBvars, toBvarsL_none args]
  | .case _ c brs, d => by simp only [toBvars, toBvars_none c, toBvarsB_none brs]
  | .proj _ c, d => by simp only [toBvars, toBvars_none c]
  | .fix defs _, d => by simp only [toBvars, toBvarsD_none defs]
/-- `toBvars_none` on argument lists. -/
theorem toBvarsL_none : ∀ (as : List LBTerm) (d : Nat), toBvarsL (fun _ => none) d as = as
  | [], _ => rfl
  | a :: as, d => by simp only [toBvarsL, toBvars_none a, toBvarsL_none as]
/-- `toBvars_none` on case branches. -/
theorem toBvarsB_none : ∀ (bs : List (List BinderName × LBTerm)) (d : Nat),
    toBvarsB (fun _ => none) d bs = bs
  | [], _ => rfl
  | (_, b) :: bs, d => by simp only [toBvarsB, toBvars_none b, toBvarsB_none bs]
/-- `toBvars_none` on fixpoint bodies. -/
theorem toBvarsD_none : ∀ (ds : List (@FixDef LBTerm)) (d : Nat),
    toBvarsD (fun _ => none) d ds = ds
  | [], _ => rfl
  | ⟨_, b, _⟩ :: ds, d => by simp only [toBvarsD, toBvars_none b, toBvarsD_none ds]
end

/-- `f` extended by `x ↦ i` where `f` does not map `x` (a variable already abstracted keeps its
index, since a later `toBvar` on it finds no occurrence). -/
def addIdx (f : FVarId → Option Nat) (x : FVarId) (i : Nat) : FVarId → Option Nat :=
  fun y => match f y with | some k => some k | none => if y == x then some i else none

mutual
/-- One more `toBvar` step after a simultaneous abstraction is a simultaneous abstraction. -/
theorem toBvar_toBvars (x : FVarId) (i : Nat) (f : FVarId → Option Nat) :
    ∀ (t : LBTerm) (d : Nat), toBvar x (i + d) (toBvars f d t) = toBvars (addIdx f x i) d t
  | .box, _ | .const _, _ | .prim _, _ | .bvar _, _ => rfl
  | .fvar y, d => by
    simp only [toBvars, addIdx]
    cases f y with
    | some k => rfl
    | none =>
      simp only [toBvar]
      by_cases h : (y == x) = true
      · simp [h]
      · simp [h]
  | .lambda _ b, d => by
    simp only [toBvars, toBvar]
    rw [show i + d + 1 = i + (d + 1) by omega, toBvar_toBvars x i f b]
  | .letIn _ b b', d => by
    simp only [toBvars, toBvar]
    rw [show i + d + 1 = i + (d + 1) by omega, toBvar_toBvars x i f b, toBvar_toBvars x i f b']
  | .app u v, d => by
    simp only [toBvars, toBvar, toBvar_toBvars x i f u, toBvar_toBvars x i f v]
  | .construct _ _ args, d => by
    simp only [toBvars, toBvar, toBvarList_toBvarsL x i f args]
  | .case (_, _) c brs, d => by
    simp only [toBvars, toBvar, toBvar_toBvars x i f c, toBvarAlts_toBvarsB x i f brs]
  | .proj _ c, d => by
    simp only [toBvars, toBvar, toBvar_toBvars x i f c]
  | .fix defs _, d => by
    simp only [toBvars, toBvar, toBvarsD_length]
    rw [show i + d + defs.length = i + (d + defs.length) by omega,
      toBvarDefs_toBvarsD x i f defs]
/-- `toBvar_toBvars` on argument lists. -/
theorem toBvarList_toBvarsL (x : FVarId) (i : Nat) (f : FVarId → Option Nat) :
    ∀ (as : List LBTerm) (d : Nat),
      toBvarList x (i + d) (toBvarsL f d as) = toBvarsL (addIdx f x i) d as
  | [], _ => rfl
  | a :: as, d => by
    simp only [toBvarsL, toBvarList, toBvar_toBvars x i f a, toBvarList_toBvarsL x i f as]
/-- `toBvar_toBvars` on case branches. -/
theorem toBvarAlts_toBvarsB (x : FVarId) (i : Nat) (f : FVarId → Option Nat) :
    ∀ (bs : List (List BinderName × LBTerm)) (d : Nat),
      toBvarAlts x (i + d) (toBvarsB f d bs) = toBvarsB (addIdx f x i) d bs
  | [], _ => rfl
  | (ns, b) :: bs, d => by
    simp only [toBvarsB, toBvarAlts]
    rw [show i + d + ns.length = i + (d + ns.length) by omega, toBvar_toBvars x i f b,
      toBvarAlts_toBvarsB x i f bs]
/-- `toBvar_toBvars` on fixpoint bodies. -/
theorem toBvarDefs_toBvarsD (x : FVarId) (i : Nat) (f : FVarId → Option Nat) :
    ∀ (ds : List (@FixDef LBTerm)) (d : Nat),
      toBvarDefs x (i + d) (toBvarsD f d ds) = toBvarsD (addIdx f x i) d ds
  | [], _ => rfl
  | ⟨_, b, _⟩ :: ds, d => by
    simp only [toBvarsD, toBvarDefs, toBvar_toBvars x i f b, toBvarDefs_toBvarsD x i f ds]
end

/-- The indices `closeFix xs` gives: `xs[j] ↦ m-1-j` (for the last occurrence of a repeated
variable). -/
def closeFixIdx : List FVarId → FVarId → Option Nat
  | [] => fun _ => none
  | x :: xs => addIdx (closeFixIdx xs) x xs.length

/-- The loop's last step closes the head variable. -/
theorem closeFix_cons (x : FVarId) (xs : List FVarId) (r : LBTerm) :
    closeFix (x :: xs) r = toBvar x xs.length (closeFix xs r) := by
  simp only [closeFix, List.reverse_cons, List.zipIdx_append, List.foldl_append,
    List.length_reverse, Nat.zero_add, List.zipIdx_singleton, List.foldl_cons, List.foldl_nil]

/-- `closeFix` is a simultaneous abstraction. -/
theorem closeFix_eq_toBvars :
    ∀ (xs : List FVarId) (r : LBTerm), closeFix xs r = toBvars (closeFixIdx xs) 0 r
  | [], r => by
    simp only [closeFix, List.reverse_nil, List.zipIdx_nil, List.foldl_nil, closeFixIdx,
      toBvars_none]
  | x :: xs, r => by
    rw [closeFix_cons, closeFix_eq_toBvars xs r, closeFixIdx]
    exact toBvar_toBvars x xs.length (closeFixIdx xs) r 0

/-- The indices of `closeFix xs` are below the block's size. -/
theorem closeFixIdx_lt :
    ∀ {xs : List FVarId} {y : FVarId} {k : Nat}, closeFixIdx xs y = some k → k < xs.length
  | [], _, _, h => by simp [closeFixIdx] at h
  | x :: xs, y, k, h => by
    simp only [closeFixIdx, addIdx] at h
    split at h
    · rename_i k' hk'
      cases h
      have := closeFixIdx_lt hk'
      simp only [List.length_cons]; omega
    · split at h
      · cases h; simp
      · cases h

/-- Without repeated variables, `closeFix xs` sends `xs[j]` to `m-1-j`. -/
theorem closeFixIdx_eq : ∀ {xs : List FVarId}, xs.Nodup → ∀ y,
    closeFixIdx xs y = (xs.idxOf? y).map (xs.length - 1 - ·)
  | [], _, y => by simp [closeFixIdx]
  | x :: xs, hnd, y => by
    have ⟨hx, hnd'⟩ := List.nodup_cons.1 hnd
    simp only [closeFixIdx, addIdx, closeFixIdx_eq hnd' y, List.idxOf?_cons, List.length_cons]
    by_cases hyx : y = x
    · subst hyx
      have : xs.idxOf? y = none := List.idxOf?_eq_none_iff.2 hx
      simp [this]
    · have hxy : ¬ (x == y) = true := by simpa using fun h => hyx h.symm
      have hyx' : ¬ (y == x) = true := by simpa using hyx
      cases h : xs.idxOf? y with
      | none => simp [hxy, hyx']
      | some j =>
        simp only [hxy, Option.map_some]
        congr 1
        dsimp only
        omega

/-! ## Parallel substitution of loose indices -/

mutual
/-- Parallel substitution: at binder depth `d`, `bvar (n + d)` becomes `ts[n]`, and the indices
beyond `ts` move down by `ts.length`. Reference: `subst` (`MR E/ELiftSubst.v:50`) without the
`lift0 d` of the substituted terms, which leaves closed terms unchanged. -/
def psubst (ts : List LBTerm) (d : Nat) : LBTerm → LBTerm
  | .box => .box
  | .bvar n => if n < d then .bvar n else
      match ts[n - d]? with | some t => t | none => .bvar (n - ts.length)
  | .fvar y => .fvar y
  | .lambda na b => .lambda na (psubst ts (d + 1) b)
  | .letIn na b b' => .letIn na (psubst ts d b) (psubst ts (d + 1) b')
  | .app u v => .app (psubst ts d u) (psubst ts d v)
  | .const kn => .const kn
  | .construct i n args => .construct i n (psubstL ts d args)
  | .case ip c brs => .case ip (psubst ts d c) (psubstB ts d brs)
  | .proj p c => .proj p (psubst ts d c)
  | .fix defs i => .fix (psubstD ts (d + defs.length) defs) i
  | .prim p => .prim p
/-- `psubst` on argument lists (part of `psubst`). -/
def psubstL (ts : List LBTerm) (d : Nat) : List LBTerm → List LBTerm
  | [] => []
  | a :: as => psubst ts d a :: psubstL ts d as
/-- `psubst` on case branches, under each branch's binders (part of `psubst`). -/
def psubstB (ts : List LBTerm) (d : Nat) :
    List (List BinderName × LBTerm) → List (List BinderName × LBTerm)
  | [] => []
  | (ns, b) :: bs => (ns, psubst ts (d + ns.length) b) :: psubstB ts d bs
/-- `psubst` on fixpoint bodies (part of `psubst`). -/
def psubstD (ts : List LBTerm) (d : Nat) : List (@FixDef LBTerm) → List (@FixDef LBTerm)
  | [] => []
  | ⟨nm, b, r⟩ :: ds => ⟨nm, psubst ts d b, r⟩ :: psubstD ts d ds
end

mutual
/-- Parallel substitution leaves a term without loose indices beyond the depth unchanged.
Reference: `subst_closed` (`MR E/ELiftSubst.v:511`). -/
theorem psubst_closed (ts : List LBTerm) :
    ∀ (t : LBTerm) (d : Nat), closedn d t = true → psubst ts d t = t
  | .box, _, _ | .const _, _, _ | .prim _, _, _ | .fvar _, _, _ => rfl
  | .bvar n, d, h => by
    simp only [closedn, decide_eq_true_eq] at h
    simp only [psubst, if_pos h]
  | .lambda _ b, d, h => by
    simp only [closedn] at h
    simp only [psubst, psubst_closed ts b _ h]
  | .letIn _ b b', d, h => by
    simp only [closedn, Bool.and_eq_true] at h
    simp only [psubst, psubst_closed ts b _ h.1, psubst_closed ts b' _ h.2]
  | .app u v, d, h => by
    simp only [closedn, Bool.and_eq_true] at h
    simp only [psubst, psubst_closed ts u _ h.1, psubst_closed ts v _ h.2]
  | .construct _ _ args, d, h => by
    simp only [closedn] at h
    simp only [psubst, psubstL_closed ts args _ h]
  | .case _ c brs, d, h => by
    simp only [closedn, Bool.and_eq_true] at h
    simp only [psubst, psubst_closed ts c _ h.1, psubstB_closed ts brs _ h.2]
  | .proj _ c, d, h => by
    simp only [closedn] at h
    simp only [psubst, psubst_closed ts c _ h]
  | .fix defs _, d, h => by
    simp only [closedn] at h
    simp only [psubst, psubstD_closed ts defs _ h]
/-- `psubst_closed` on argument lists. -/
theorem psubstL_closed (ts : List LBTerm) : ∀ (as : List LBTerm) (d : Nat),
    closednL d as = true → psubstL ts d as = as
  | [], _, _ => rfl
  | a :: as, d, h => by
    simp only [closednL, Bool.and_eq_true] at h
    simp only [psubstL, psubst_closed ts a _ h.1, psubstL_closed ts as _ h.2]
/-- `psubst_closed` on case branches. -/
theorem psubstB_closed (ts : List LBTerm) : ∀ (bs : List (List BinderName × LBTerm)) (d : Nat),
    closednB d bs = true → psubstB ts d bs = bs
  | [], _, _ => rfl
  | (_, b) :: bs, d, h => by
    simp only [closednB, Bool.and_eq_true] at h
    simp only [psubstB, psubst_closed ts b _ h.1, psubstB_closed ts bs _ h.2]
/-- `psubst_closed` on fixpoint bodies. -/
theorem psubstD_closed (ts : List LBTerm) : ∀ (ds : List (@FixDef LBTerm)) (d : Nat),
    closednD d ds = true → psubstD ts d ds = ds
  | [], _, _ => rfl
  | ⟨_, b, _⟩ :: ds, d, h => by
    simp only [closednD, Bool.and_eq_true] at h
    simp only [psubstD, psubst_closed ts b _ h.1, psubstD_closed ts ds _ h.2]
end

mutual
/-- The empty parallel substitution is the identity. Reference: `subst_empty`
(`MR E/ELiftSubst.v:499`). -/
theorem psubst_nil : ∀ (t : LBTerm) (d : Nat), psubst [] d t = t
  | .box, _ | .const _, _ | .prim _, _ | .fvar _, _ => rfl
  | .bvar n, d => by
    simp only [psubst, List.getElem?_nil, List.length_nil, Nat.sub_zero]
    split <;> rfl
  | .lambda _ b, d => by simp only [psubst, psubst_nil b]
  | .letIn _ b b', d => by simp only [psubst, psubst_nil b, psubst_nil b']
  | .app u v, d => by simp only [psubst, psubst_nil u, psubst_nil v]
  | .construct _ _ args, d => by simp only [psubst, psubstL_nil args]
  | .case _ c brs, d => by simp only [psubst, psubst_nil c, psubstB_nil brs]
  | .proj _ c, d => by simp only [psubst, psubst_nil c]
  | .fix defs _, d => by simp only [psubst, psubstD_nil defs]
/-- `psubst_nil` on argument lists. -/
theorem psubstL_nil : ∀ (as : List LBTerm) (d : Nat), psubstL [] d as = as
  | [], _ => rfl
  | a :: as, d => by simp only [psubstL, psubst_nil a, psubstL_nil as]
/-- `psubst_nil` on case branches. -/
theorem psubstB_nil : ∀ (bs : List (List BinderName × LBTerm)) (d : Nat), psubstB [] d bs = bs
  | [], _ => rfl
  | (_, b) :: bs, d => by simp only [psubstB, psubst_nil b, psubstB_nil bs]
/-- `psubst_nil` on fixpoint bodies. -/
theorem psubstD_nil : ∀ (ds : List (@FixDef LBTerm)) (d : Nat), psubstD [] d ds = ds
  | [], _ => rfl
  | ⟨_, b, _⟩ :: ds, d => by simp only [psubstD, psubst_nil b, psubstD_nil ds]
end

mutual
/-- Substituting a closed `a` for index `d`, then `as` in parallel, is substituting `a :: as` in
parallel. Reference: `closed_subst` (`MR E/ECSubst.v:51`) with `subst_app_decomp`
(`MR E/ELiftSubst.v:541`). -/
theorem psubst_csubst (a : LBTerm) (ha : closedn 0 a = true) (as : List LBTerm) :
    ∀ (t : LBTerm) (d : Nat), psubst as d (csubst a d t) = psubst (a :: as) d t
  | .box, _ | .const _, _ | .prim _, _ | .fvar _, _ => rfl
  | .bvar n, d => by
    simp only [csubst]
    by_cases h1 : d = n
    · subst h1
      simp only [if_true, psubst, Nat.lt_irrefl, if_false, Nat.sub_self, List.getElem?_cons_zero]
      exact psubst_closed as a d (closedn_mono a (Nat.zero_le d) ha)
    · simp only [h1, if_false]
      by_cases h2 : d < n
      · simp only [h2, if_true, psubst]
        rw [if_neg (by omega), if_neg (by omega),
          show n - d = (n - 1 - d) + 1 by omega, List.getElem?_cons_succ]
        cases as[n - 1 - d]? with
        | some _ => rfl
        | none => simp only [List.length_cons]; congr 1; omega
      · simp only [h2, if_false, psubst]
        rw [if_pos (by omega), if_pos (by omega)]
  | .lambda _ b, d => by simp only [csubst, psubst, psubst_csubst a ha as b]
  | .letIn _ b b', d => by
    simp only [csubst, psubst, psubst_csubst a ha as b, psubst_csubst a ha as b']
  | .app u v, d => by
    simp only [csubst, psubst, psubst_csubst a ha as u, psubst_csubst a ha as v]
  | .construct _ _ args, d => by simp only [csubst, psubst, psubstL_csubst a ha as args]
  | .case _ c brs, d => by
    simp only [csubst, psubst, psubst_csubst a ha as c, psubstB_csubst a ha as brs]
  | .proj _ c, d => by simp only [csubst, psubst, psubst_csubst a ha as c]
  | .fix defs _, d => by
    simp only [csubst, psubst, csubstD_length, psubstD_csubst a ha as defs]
/-- `psubst_csubst` on argument lists. -/
theorem psubstL_csubst (a : LBTerm) (ha : closedn 0 a = true) (as : List LBTerm) :
    ∀ (xs : List LBTerm) (d : Nat), psubstL as d (csubstL a d xs) = psubstL (a :: as) d xs
  | [], _ => rfl
  | x :: xs, d => by
    simp only [csubstL, psubstL, psubst_csubst a ha as x, psubstL_csubst a ha as xs]
/-- `psubst_csubst` on case branches. -/
theorem psubstB_csubst (a : LBTerm) (ha : closedn 0 a = true) (as : List LBTerm) :
    ∀ (bs : List (List BinderName × LBTerm)) (d : Nat),
      psubstB as d (csubstB a d bs) = psubstB (a :: as) d bs
  | [], _ => rfl
  | (ns, b) :: bs, d => by
    simp only [csubstB, psubstB, psubst_csubst a ha as b, psubstB_csubst a ha as bs]
/-- `psubst_csubst` on fixpoint bodies. -/
theorem psubstD_csubst (a : LBTerm) (ha : closedn 0 a = true) (as : List LBTerm) :
    ∀ (ds : List (@FixDef LBTerm)) (d : Nat),
      psubstD as d (csubstD a d ds) = psubstD (a :: as) d ds
  | [], _ => rfl
  | ⟨_, b, _⟩ :: ds, d => by
    simp only [csubstD, psubstD, psubst_csubst a ha as b, psubstD_csubst a ha as ds]
end

/-- `substl` of closed terms is parallel substitution at depth `0`. Reference: `substl_subst`
(`MR E/ECSubst.v:67`). -/
theorem substl_eq_psubst : ∀ (ts : List LBTerm), (∀ t ∈ ts, closedn 0 t = true) →
    ∀ b, substl ts b = psubst ts 0 b
  | [], _, b => by simp only [substl, List.foldl_nil, psubst_nil]
  | a :: as, h, b => by
    have e1 : substl (a :: as) b = substl as (csubst a 0 b) := rfl
    rw [e1, substl_eq_psubst as (fun t ht => h t (.tail _ ht)),
      psubst_csubst a (h a (.head _)) as b 0]

/-! ## Abstraction then substitution -/

mutual
/-- On a term without loose indices beyond the depth, abstracting by `F` and substituting `ts` in
parallel substitutes the free variables by `s`, when `F` and `s` agree through `ts`. Reference:
none (DV-13). -/
theorem psubst_toBvars {F : FVarId → Option Nat} {s : FVarId → Option LBTerm} {ts : List LBTerm}
    (H : ∀ y, (F y = none ∧ s y = none) ∨ ∃ k t, F y = some k ∧ ts[k]? = some t ∧ s y = some t) :
    ∀ (t : LBTerm) (d : Nat), closedn d t = true →
    psubst ts d (toBvars F d t) = substFVars s t
  | .box, _, _ | .const _, _, _ | .prim _, _, _ => rfl
  | .bvar n, d, h => by
    simp only [closedn, decide_eq_true_eq] at h
    simp only [toBvars, psubst, if_pos h, substFVars]
  | .fvar y, d, _ => by
    rcases H y with ⟨hF, hs⟩ | ⟨k, t, hF, ht, hs⟩
    · simp only [toBvars, hF, psubst, substFVars, hs, Option.getD_none]
    · simp only [toBvars, hF, psubst, substFVars, hs, Option.getD_some]
      rw [if_neg (by omega), show k + d - d = k by omega, ht]
  | .lambda _ b, d, h => by
    simp only [closedn] at h
    simp only [toBvars, psubst, substFVars, psubst_toBvars H b _ h]
  | .letIn _ b b', d, h => by
    simp only [closedn, Bool.and_eq_true] at h
    simp only [toBvars, psubst, substFVars, psubst_toBvars H b _ h.1, psubst_toBvars H b' _ h.2]
  | .app u v, d, h => by
    simp only [closedn, Bool.and_eq_true] at h
    simp only [toBvars, psubst, substFVars, psubst_toBvars H u _ h.1, psubst_toBvars H v _ h.2]
  | .construct _ _ args, d, h => by
    simp only [closedn] at h
    simp only [toBvars, psubst, substFVars, psubstL_toBvarsL H args _ h]
  | .case _ c brs, d, h => by
    simp only [closedn, Bool.and_eq_true] at h
    simp only [toBvars, psubst, substFVars, psubst_toBvars H c _ h.1, psubstB_toBvarsB H brs _ h.2]
  | .proj _ c, d, h => by
    simp only [closedn] at h
    simp only [toBvars, psubst, substFVars, psubst_toBvars H c _ h]
  | .fix defs _, d, h => by
    simp only [closedn] at h
    simp only [toBvars, psubst, substFVars, toBvarsD_length, psubstD_toBvarsD H defs _ h]
/-- `psubst_toBvars` on argument lists. -/
theorem psubstL_toBvarsL {F : FVarId → Option Nat} {s : FVarId → Option LBTerm} {ts : List LBTerm}
    (H : ∀ y, (F y = none ∧ s y = none) ∨ ∃ k t, F y = some k ∧ ts[k]? = some t ∧ s y = some t) :
    ∀ (as : List LBTerm) (d : Nat), closednL d as = true →
    psubstL ts d (toBvarsL F d as) = substFVarsL s as
  | [], _, _ => rfl
  | a :: as, d, h => by
    simp only [closednL, Bool.and_eq_true] at h
    simp only [toBvarsL, psubstL, substFVarsL, psubst_toBvars H a _ h.1,
      psubstL_toBvarsL H as _ h.2]
/-- `psubst_toBvars` on case branches. -/
theorem psubstB_toBvarsB {F : FVarId → Option Nat} {s : FVarId → Option LBTerm} {ts : List LBTerm}
    (H : ∀ y, (F y = none ∧ s y = none) ∨ ∃ k t, F y = some k ∧ ts[k]? = some t ∧ s y = some t) :
    ∀ (bs : List (List BinderName × LBTerm)) (d : Nat),
    closednB d bs = true → psubstB ts d (toBvarsB F d bs) = substFVarsB s bs
  | [], _, _ => rfl
  | (_, b) :: bs, d, h => by
    simp only [closednB, Bool.and_eq_true] at h
    simp only [toBvarsB, psubstB, substFVarsB, psubst_toBvars H b _ h.1,
      psubstB_toBvarsB H bs _ h.2]
/-- `psubst_toBvars` on fixpoint bodies. -/
theorem psubstD_toBvarsD {F : FVarId → Option Nat} {s : FVarId → Option LBTerm} {ts : List LBTerm}
    (H : ∀ y, (F y = none ∧ s y = none) ∨ ∃ k t, F y = some k ∧ ts[k]? = some t ∧ s y = some t) :
    ∀ (ds : List (@FixDef LBTerm)) (d : Nat), closednD d ds = true →
    psubstD ts d (toBvarsD F d ds) = substFVarsD s ds
  | [], _, _ => rfl
  | ⟨_, b, _⟩ :: ds, d, h => by
    simp only [closednD, Bool.and_eq_true] at h
    simp only [toBvarsD, psubstD, substFVarsD, psubst_toBvars H b _ h.1,
      psubstD_toBvarsD H ds _ h.2]
end

/-! ## Closedness of the abstraction -/

mutual
/-- Abstracting by indices below `K` raises the closedness bound by `K`. -/
theorem closedn_toBvars {F : FVarId → Option Nat} {K : Nat} (hF : ∀ y k, F y = some k → k < K) :
    ∀ (t : LBTerm) (d : Nat), closedn d t = true →
    closedn (d + K) (toBvars F d t) = true
  | .box, _, _ | .const _, _, _ | .prim _, _, _ => rfl
  | .bvar n, d, h => by
    simp only [closedn, decide_eq_true_eq] at h
    simp only [toBvars, closedn, decide_eq_true_eq]; omega
  | .fvar y, d, _ => by
    simp only [toBvars]
    cases h : F y with
    | none => rfl
    | some k =>
      have := hF y k h
      simp only [closedn, decide_eq_true_eq]; omega
  | .lambda _ b, d, h => by
    simp only [closedn] at h
    simp only [toBvars, closedn]
    rw [show d + K + 1 = d + 1 + K by omega]; exact closedn_toBvars hF b _ h
  | .letIn _ b b', d, h => by
    simp only [closedn, Bool.and_eq_true] at h
    simp only [toBvars, closedn, Bool.and_eq_true]
    rw [show d + K + 1 = d + 1 + K by omega]
    exact ⟨closedn_toBvars hF b _ h.1, closedn_toBvars hF b' _ h.2⟩
  | .app u v, d, h => by
    simp only [closedn, Bool.and_eq_true] at h
    simp only [toBvars, closedn, Bool.and_eq_true]
    exact ⟨closedn_toBvars hF u _ h.1, closedn_toBvars hF v _ h.2⟩
  | .construct _ _ args, d, h => by
    simp only [closedn] at h
    simp only [toBvars, closedn]; exact closednL_toBvarsL hF args _ h
  | .case _ c brs, d, h => by
    simp only [closedn, Bool.and_eq_true] at h
    simp only [toBvars, closedn, Bool.and_eq_true]
    exact ⟨closedn_toBvars hF c _ h.1, closednB_toBvarsB hF brs _ h.2⟩
  | .proj _ c, d, h => by
    simp only [closedn] at h
    simp only [toBvars, closedn]; exact closedn_toBvars hF c _ h
  | .fix defs _, d, h => by
    simp only [closedn] at h
    simp only [toBvars, closedn, toBvarsD_length]
    rw [show d + K + defs.length = d + defs.length + K by omega]
    exact closednD_toBvarsD hF defs _ h
/-- `closedn_toBvars` on argument lists. -/
theorem closednL_toBvarsL {F : FVarId → Option Nat} {K : Nat} (hF : ∀ y k, F y = some k → k < K) :
    ∀ (as : List LBTerm) (d : Nat), closednL d as = true →
    closednL (d + K) (toBvarsL F d as) = true
  | [], _, _ => rfl
  | a :: as, d, h => by
    simp only [closednL, Bool.and_eq_true] at h
    simp only [toBvarsL, closednL, Bool.and_eq_true]
    exact ⟨closedn_toBvars hF a _ h.1, closednL_toBvarsL hF as _ h.2⟩
/-- `closedn_toBvars` on case branches. -/
theorem closednB_toBvarsB {F : FVarId → Option Nat} {K : Nat} (hF : ∀ y k, F y = some k → k < K) :
    ∀ (bs : List (List BinderName × LBTerm)) (d : Nat),
    closednB d bs = true → closednB (d + K) (toBvarsB F d bs) = true
  | [], _, _ => rfl
  | (ns, b) :: bs, d, h => by
    simp only [closednB, Bool.and_eq_true] at h
    simp only [toBvarsB, closednB, Bool.and_eq_true]
    rw [show d + K + ns.length = d + ns.length + K by omega]
    exact ⟨closedn_toBvars hF b _ h.1, closednB_toBvarsB hF bs _ h.2⟩
/-- `closedn_toBvars` on fixpoint bodies. -/
theorem closednD_toBvarsD {F : FVarId → Option Nat} {K : Nat} (hF : ∀ y k, F y = some k → k < K) :
    ∀ (ds : List (@FixDef LBTerm)) (d : Nat), closednD d ds = true →
    closednD (d + K) (toBvarsD F d ds) = true
  | [], _, _ => rfl
  | ⟨_, b, _⟩ :: ds, d, h => by
    simp only [closednD, Bool.and_eq_true] at h
    simp only [toBvarsD, closednD, Bool.and_eq_true]
    exact ⟨closedn_toBvars hF b _ h.1, closednD_toBvarsD hF ds _ h.2⟩
end

/-! ## The block's fixpoints -/

/-- The fixpoints of a block whose bodies are closed under the block's binders are closed.
Reference: `closed_fix_subst` (`MR E/EWcbvEval.v:1562`). -/
theorem closedn_fixSubst {defs : List (@FixDef LBTerm)}
    (hdefs : ∀ d ∈ defs, closedn defs.length d.body = true) :
    ∀ t ∈ fixSubst defs, closedn 0 t = true := by
  intro t ht
  simp only [fixSubst, List.mem_map] at ht
  obtain ⟨i, -, rfl⟩ := ht
  simp only [closedn, Nat.zero_add]
  have : ∀ ds : List (@FixDef LBTerm), (∀ d ∈ ds, closedn defs.length d.body = true) →
      closednD defs.length ds = true := by
    intro ds h
    induction ds with
    | nil => rfl
    | cons d ds ih =>
      obtain ⟨_, b, _⟩ := d
      simp only [closednD, Bool.and_eq_true]
      exact ⟨h _ (.head _), ih fun d hd => h d (.tail _ hd)⟩
  exact this defs hdefs

/-- Index `m-1-j` of `fix_subst defs` is `tFix defs j`. Reference: `fix_subst`
(`MR E/EGlobalEnv.v:210`). -/
theorem fixSubst_getElem? (defs : List (@FixDef LBTerm)) {j : Nat} (hj : j < defs.length) :
    (fixSubst defs)[defs.length - 1 - j]? = some (.fix defs j) := by
  have hlt : defs.length - 1 - j < (List.range defs.length).length := by
    simp only [List.length_range]; omega
  simp only [fixSubst, List.getElem?_map]
  rw [List.getElem?_reverse hlt, List.length_range,
    show defs.length - 1 - (defs.length - 1 - j) = j by omega, List.getElem?_range hj]
  rfl

/-! ## The two statements -/

/-- `mkDef`'s abstraction of a closed body is closed under the block's binders. Reference: none
(DV-13); the target-side fact `closed_fix_subst` (`MR E/EWcbvEval.v:1562`) is its use. -/
theorem closeFix_closed (hr : closedn 0 r = true) : closedn xs.length (closeFix xs r) = true := by
  rw [closeFix_eq_toBvars]
  have := closedn_toBvars (F := closeFixIdx xs) (K := xs.length)
    (fun _ _ h => closeFixIdx_lt h) r 0 hr
  rwa [Nat.zero_add] at this

/-- `mkDef`'s multi-variable abstraction: after `substl (fix_subst defs)` (as `cunfold_fix` does),
fix variable `xs[j]` has become `tFix defs j`. Reference: none (DV-13); `cunfold_fix`
(`MR E/EGlobalEnv.v:238`). -/
theorem closeFix_substl (hr : closedn 0 r = true) (hxs : xs.Nodup)
    (hlen : xs.length = defs.length) (hdefs : ∀ d ∈ defs, closedn defs.length d.body = true) :
    substl (fixSubst defs) (closeFix xs r) = substFVars (fixTargets xs defs) r := by
  rw [closeFix_eq_toBvars, substl_eq_psubst _ (closedn_fixSubst hdefs)]
  refine psubst_toBvars (F := closeFixIdx xs) (s := fixTargets xs defs) (ts := fixSubst defs)
    ?_ r 0 hr
  intro y
  rw [closeFixIdx_eq hxs y]
  simp only [fixTargets]
  cases h : xs.idxOf? y with
  | none => exact .inl ⟨rfl, rfl⟩
  | some j =>
    have hj : j < xs.length := (List.idxOf?_eq_some_iff.1 h).1
    refine .inr ⟨xs.length - 1 - j, .fix defs j, rfl, ?_, rfl⟩
    rw [hlen]
    exact fixSubst_getElem? defs (hlen ▸ hj)

end EraseProof
