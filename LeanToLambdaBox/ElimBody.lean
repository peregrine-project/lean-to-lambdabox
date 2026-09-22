import LeanToLambdaBox.Closed
import LeanToLambdaBox.Semantics.Compute

/-!
# Eliminator bodies, as constructions

The λ□ body a runtime library must give an eliminator constant, as a *construction*,
together with its closedness:

* `mkElimBody` — the case-dispatching eliminator at the `casesOn` calling convention:
  `dp` dropped arguments (parameters and motive), the discriminant, then one minor per
  constructor;
* `mkElimBodyRec` — the same dispatch under a guarded `fix` whose principal argument is
  the discriminant;
* `ElimBody` — the two-shape syntactic predicate `Lower` keys its eliminator arms on,
  with `ElimBody.closed`, what `Lower`'s `ElimBodyClosed` asks for.

`Γspec` is never evaluated, so the file carries no evaluation theory: everything here is
target-side syntax — `LBTerm` and the de Bruijn operations — with no `Expr`, no `VEnv`
and no run state.
-/

namespace LeanToLambdaBox

open Lean (Name FVarId)

/-! ## Telescope helpers -/

/-- The arguments an alternative applies to its minor: `fieldArgs m = [.bvar (m-1), …,
.bvar 0]`, the `m` field binders of a `case` alternative in *source* order. -/
def fieldArgs : Nat → List LBTerm
  | 0 => []
  | m + 1 => .bvar m :: fieldArgs m

@[simp] theorem fieldArgs_length (m : Nat) : (fieldArgs m).length = m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [fieldArgs, ih]

/-- `fieldArgs` is `Lower`'s `bvarsDesc`: the descending run of de Bruijn indices. -/
theorem fieldArgs_eq (m : Nat) : fieldArgs m = (List.range m).reverse.map LBTerm.bvar := by
  induction m with
  | zero => rfl
  | succ m ih => rw [List.range_succ]; simp [fieldArgs, ih]

theorem fieldArgs_lt {m : Nat} {t : LBTerm} (h : t ∈ fieldArgs m) : ∃ i, i < m ∧ t = .bvar i := by
  induction m with
  | zero => exact absurd h (by simp [fieldArgs])
  | succ m ih =>
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨m, Nat.lt_succ_self m, rfl⟩
      · obtain ⟨i, hi, rfl⟩ := ih h
        exact ⟨i, Nat.lt_succ_of_lt hi, rfl⟩

/-- The alternatives of `mkElimBody`: alternative `k` binds its `nfs[k]` fields and
applies the `k`-th minor — which sits `nfs[k] + (nfs.length - 1 - k)` binders out — to
them, in order. Written by recursion on the *remaining* field-count list, whose length is
exactly that distance. -/
def elimAlts : List Nat → List (List BinderName × LBTerm)
  | [] => []
  | m :: ms =>
      (List.replicate m .anon, LBTerm.mkApps (.bvar (m + ms.length)) (fieldArgs m))
        :: elimAlts ms

@[simp] theorem elimAlts_length (ms : List Nat) : (elimAlts ms).length = ms.length := by
  induction ms with
  | nil => rfl
  | cons m ms ih => simp [elimAlts, ih]

/-! ## The bodies -/

/-- The λ□ body of a non-recursive eliminator constant at the `casesOn` calling
convention: `dp` dropped arguments (parameters and motive), the discriminant, then one
minor per constructor, dispatched by a `case` node on the discriminant. -/
def mkElimBody (iid : InductiveId) (np dp : Nat) (nfs : List Nat) : LBTerm :=
  mkLambdas (List.replicate (dp + 1 + nfs.length) .anon)
    (.case (iid, np) (.bvar nfs.length) (elimAlts nfs))

/-- The λ□ body of a recursive eliminator constant: `mkElimBody`'s dispatch under a
guarded `fix` whose principal argument is the discriminant. The body is closed, so the
fix variable is unused: which fields carry a recursive call is not a function of the
field *counts* `nfs`, so no recursive call can be written at this signature. -/
def mkElimBodyRec (iid : InductiveId) (np dp : Nat) (nfs : List Nat) : LBTerm :=
  .fix [{ name := .anon, body := mkElimBody iid np dp nfs, principalArgIdx := dp }] 0

/-- The λ□ body of an eliminator constant, as a *syntactic* shape: one constructor per
shape, no semantic side condition. There is no propositional-singleton shape — the
emitted environment marks every inductive non-propositional, so a `□`-discriminant
`.case` is stuck at every flag point. -/
inductive ElimBody : InductiveId → Nat → Nat → List Nat → LBTerm → Prop
  | cases {iid : InductiveId} {np dp : Nat} {nfs : List Nat} :
      ElimBody iid np dp nfs (mkElimBody iid np dp nfs)
  /-- The recursive shape. Named `recur` because `ElimBody.rec` is the recursor. -/
  | recur {iid : InductiveId} {np dp : Nat} {nfs : List Nat} :
      ElimBody iid np dp nfs (mkElimBodyRec iid np dp nfs)

/-! ## Closedness -/

/-- Every field index is below the telescope it is read under. -/
theorem fieldArgs_closed {m k : Nat} (h : m ≤ k) : ∀ t ∈ fieldArgs m, LBClosed t k := by
  intro t ht
  obtain ⟨i, hi, rfl⟩ := fieldArgs_lt ht
  exact Nat.lt_of_lt_of_le hi h

/-- The alternatives are closed under `ms.length` binders: the `k`-th minor's index is
`nfs[k] + (nfs.length - 1 - k)`, the largest of which is `nfs[k] + nfs.length - 1`. -/
theorem elimAlts_closed : ∀ (ms : List Nat) {k : Nat}, ms.length ≤ k → LBClosedAlts (elimAlts ms) k
  | [], _, _ => trivial
  | m :: ms, k, h => by
      refine ⟨?_, elimAlts_closed ms (by simp only [List.length_cons] at h; omega)⟩
      simp only [List.length_replicate]
      refine LBClosed.mkApps ?_ (fun a ha => fieldArgs_closed (Nat.le_add_left m k) a ha)
      simp only [List.length_cons] at h
      show m + ms.length < k + m
      omega

theorem mkElimBody_closed (iid : InductiveId) (np dp : Nat) (nfs : List Nat) :
    LBClosed (mkElimBody iid np dp nfs) 0 := by
  refine LBClosed.mkLambdas ⟨?_, ?_⟩
  · show nfs.length < 0 + (List.replicate (dp + 1 + nfs.length) BinderName.anon).length
    simp only [List.length_replicate]
    omega
  · refine elimAlts_closed nfs ?_
    simp only [List.length_replicate]
    omega

theorem mkElimBodyRec_closed (iid : InductiveId) (np dp : Nat) (nfs : List Nat) :
    LBClosed (mkElimBodyRec iid np dp nfs) 0 :=
  ⟨(mkElimBody_closed iid np dp nfs).mono (Nat.zero_le 1), trivial⟩

/-- Both eliminator shapes are closed: what `Lower`'s `ElimBodyClosed` asks for. -/
theorem ElimBody.closed {iid : InductiveId} {np dp : Nat} {nfs : List Nat} {h : LBTerm} :
    ElimBody iid np dp nfs h → LBClosed h 0
  | .cases => mkElimBody_closed iid np dp nfs
  | .recur => mkElimBodyRec_closed iid np dp nfs

/-- An eliminator body is one of the two shapes: the inductive has no other constructor,
which is what refutes `ElimBody` at a body of any other shape. -/
theorem ElimBody.shape {iid : InductiveId} {np dp : Nat} {nfs : List Nat} {b : LBTerm}
    (h : ElimBody iid np dp nfs b) :
    b = mkElimBody iid np dp nfs ∨ b = mkElimBodyRec iid np dp nfs := by
  cases h with
  | cases => exact .inl rfl
  | recur => exact .inr rfl

/-! ## Checked instances

Three eliminators of the shipping fragment, at the `(np, dp, nfs)` their Lean
declarations have, each with its `ElimBody` shape. `Decidable.casesOn` carries a
parameter, which its `np` records.
-/

/-- `Nat`: no parameters, `zero` with no fields, `succ` with one. -/
def natIid : InductiveId := { mutualBlockName := rootKername "Nat", idx := 0 }

/-- `Nat.casesOn`: one dropped argument (the motive), two minors of `0` and `1` fields. -/
theorem natCasesOn_elimBody : ElimBody natIid 0 1 [0, 1] (mkElimBody natIid 0 1 [0, 1]) := .cases

/-- `Bool`: no parameters, two field-free constructors. -/
def boolIid : InductiveId := { mutualBlockName := rootKername "Bool", idx := 0 }

/-- `Bool.casesOn`: one dropped argument, two field-free minors. -/
theorem boolCasesOn_elimBody : ElimBody boolIid 0 1 [0, 0] (mkElimBody boolIid 0 1 [0, 0]) :=
  .cases

/-- `Decidable`: one parameter, `isFalse` and `isTrue`, each with one field. -/
def decIid : InductiveId := { mutualBlockName := rootKername "Decidable", idx := 0 }

/-- `Decidable.casesOn`: two dropped arguments (the parameter and the motive), two minors
of one field each. -/
theorem decCasesOn_elimBody : ElimBody decIid 1 2 [1, 1] (mkElimBody decIid 1 2 [1, 1]) := .cases

end LeanToLambdaBox
