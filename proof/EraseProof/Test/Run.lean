import LeanToLambdaBox

/-!
# Runs of the traversal at the pure backend, for the non-vacuity tests

The tools with which `Test/NV1Run.lean` evaluates `#erase`'s pure path on a concrete program,
one traversal call at a time. The traversal state holds `Std.HashMap`s keyed by `Name`, whose
hashing (`mixHash`) the kernel does not evaluate, so a run is cut at every map access:
`bind_ok` replaces the first action of a bind by its result, and the map accesses are rewritten
with the `Std.HashMap` lemmas. What remains is evaluated by the kernel: the tactic `krfl` closes an
equation `a = b` by a theorem `a = b` whose proof is `Eq.refl a`, which only the kernel checks
(the elaborator's definitional unfolding does not complete on these runs, e.g. on `Name.toString`).
The iterators of `Subarray` and `Std.Rco` are well-founded loops that neither reduces; they are
rewritten into lists first (`toArray_toSubarray`, `forIn_toSubarray_size`, and the range lemmas
of the standard library). Reference: none.
-/

open Lean Erasure

namespace EraseProof.Test

/-- `krfl` closes `a = b` by kernel evaluation: it adds the auxiliary theorem `a = b` with proof
`Eq.refl a`, which the kernel checks. -/
syntax (name := _krfl) "krfl" : tactic

macro_rules
  | `(tactic| krfl) => `(tactic| run_tac do
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
      let t ← Lean.instantiateMVars (← g.getType)
      let some (_, a, _) := t.eq? | throwError "krfl: not an equation"
      g.assign (← Lean.Meta.mkAuxTheorem t (← Lean.Meta.mkEqRefl a))
    Lean.Elab.Tactic.replaceMainGoal [])

variable {α β : Type} {pc : PureCtx} {st : ErasureState} {ps : PureState} {tc : TravCtx}

/-- A run of a bind runs the continuation from the state the first action leaves. Reference:
none. -/
theorem runPure_bind (x : EraseT PureM α) (k : α → EraseT PureM β) :
    (x >>= k).runPure st tc pc ps =
      x.runPure st tc pc ps >>= fun r => (k r.1.1).runPure r.1.2 tc pc r.2 := rfl

/-- A run of `withReader f x` runs `x` under the reader context `f tc`. Reference: none. -/
theorem runPure_withReader (f : TravCtx → TravCtx) (x : EraseT PureM α) :
    (withReader f x).runPure st tc pc ps = x.runPure st (f tc) pc ps := rfl

/-- A run of a bind whose first action returns `a`: the run of the continuation on `a`.
Reference: none. -/
theorem bind_ok {x : EraseT PureM α} {k : α → EraseT PureM β} {a : α} {st' : ErasureState}
    {ps' : PureState} {r : Except EraseError ((β × ErasureState) × PureState)}
    (hx : x.runPure st tc pc ps = .ok ((a, st'), ps')) (hk : (k a).runPure st' tc pc ps' = r) :
    (x >>= k).runPure st tc pc ps = r := by
  rw [runPure_bind, hx]; exact hk

/-- `withApp` on a constant. Reference: none. -/
theorem withApp_const {γ : Sort _} (c : Name) (us : List Level) (k : Expr → Array Expr → γ) :
    (Expr.const c us).withApp k = k (.const c us) #[] := rfl

/-- `withApp` on an application of a head that is not an application. Reference: none. -/
theorem withApp_app1 {γ : Sort _} (f a : Expr) (k : Expr → Array Expr → γ) (hf : f.isApp = false) :
    (Expr.app f a).withApp k = k f #[a] := by
  cases f <;> first | (cases hf; done) | krfl

/-- The elements of a subarray built by `toSubarray`, as `extract`. Reference: none. -/
theorem toArray_toSubarray (xs : Array α) (lo hi : Nat) :
    Std.Slice.toArray (xs.toSubarray lo hi) = xs.extract lo hi :=
  Array.toArray_mkSlice_rco

/-- A loop over the empty suffix of an array returns its initial value. Reference: none. -/
theorem forIn_toSubarray_size (xs : Array Expr) (init : β)
    (f : Expr → β → EraseT PureM (ForInStep β)) :
    forIn (xs.toSubarray xs.size) init f = pure init := by
  rw [Subarray.forIn_eq_forIn_toList]
  have : (xs.toSubarray xs.size).toList = [] := by
    simp [Subarray.toList_eq_drop_take]
  rw [this]; rfl

end EraseProof.Test
