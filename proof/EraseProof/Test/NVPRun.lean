import EraseProof.Test.NVPData
import EraseProof.Test.Run

/-!
# NV-P and NV-K through the entry point of `#erase`

The hypotheses `hfrag` and `hrun` of the final theorem (`MR E/ErasureFunctionProperties.v:657
erase_correct`) on NV-P and NV-K (`Test/NVPData.lean`), which differ only in the major premise of
the `Eq.casesOn` (`mj`). `hcollect` computes the fragment test's closures by kernel evaluation.
The pure path's run is evaluated one traversal call at a time (`Test/Run.lean`): the major is a
proof (its sort is `Prop`) and `Eq` has one constructor, so `visitCases` reduces the `casesOn` to
its alternative `fun y => y` (`idB_run`, `visitCases_run`), without a λ□ `case` and without
registering an inductive; the program is `pP`, with no declaration.
-/
open Lean Erasure EraseProof.Test
open EraseProof.Test.NV1 (tB cT)
open EraseProof.Test.NVP (l1 motE idB Eq_ind Eq_refl Eq_rec Eq_casesOn)

namespace EraseProof.Test.NVPK

/-- The major premise: `@Eq.refl.{1} B B.t` (NV-P) or `hEq` (NV-K). -/
def mj : Bool → Expr
  | false => mkAppN (.const `Eq.refl [l1]) #[tB, cT]
  | true => .const `hEq []

/-- The arguments of the `Eq.casesOn`. -/
def args (k : Bool) : Array Expr := #[tB, cT, motE, cT, mj k, idB]

/-- The term: NV-P's `e` (`k = false`), NV-K's `e` (`k = true`). -/
def ee (k : Bool) : Expr := mkAppN (.const `Eq.casesOn [l1, l1]) (args k)

/-- The closures, in the order the fragment test returns them. -/
def DD : Bool → List ConstantInfo
  | false => [.ctorInfo NV1.Bt_ctor, .ctorInfo NV1.Bf_ctor, .inductInfo NV1.B_ind, .ctorInfo Eq_refl,
      .inductInfo Eq_ind, .recInfo Eq_rec, .defnInfo Eq_casesOn]
  | true => [.thmInfo NVK.hEq_thm, .ctorInfo NV1.Bt_ctor, .ctorInfo NV1.Bf_ctor, .inductInfo NV1.B_ind,
      .ctorInfo Eq_refl, .inductInfo Eq_ind, .recInfo Eq_rec, .defnInfo Eq_casesOn]

/-- The views. -/
def vw : Bool → EnvView
  | false => NVP.view
  | true => NVK.view

/-- The pure backend's context over the closure. -/
def pcK (k : Bool) : PureCtx := ⟨DD k, vw k⟩

/-- The fragment test accepts the term and returns its closure, by kernel evaluation.
Reference: the environment `Σ'` of `erase_global_deps` (`MR E/ErasureFunction.v:1602`). -/
theorem hcollect {k : Bool} : collectDeps (vw k) {} (ee k) = .ok (DD k) := by
  cases k <;> rfl

/-- The free variable of the traversal's first fresh local. -/
def xy : FVarId := ⟨.num `_pure 0⟩
/-- The erasure of `fun y => y`. -/
def idL : LBTerm := .lambda (binderNameOf `y) (_root_.abstract xy (.fvar xy))

variable {st : ErasureState}

/-- `visitExpr` on the alternative `fun y => y`. Reference: the `tLambda` case of `erase`
(`MR E/ErasureFunction.v:1003`). -/
theorem idB_run {k : Bool} {n : Nat} {L : LocalContext} :
    (visitExpr (m := PureM) (n + 4) idB).runPure st ⟨L, [], none, {}⟩ (pcK k) ⟨0⟩ =
      .ok ((idL, st), ⟨1⟩) := by
  rw [idB, visitExpr, ← idB]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ⟨0⟩) (by cases k <;> krfl) ?_
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [visitLambda]
  refine bind_ok (a := xy) (st' := st) (ps' := ⟨1⟩) rfl ?_
  refine bind_ok (a := .fvar xy) (st' := st) (ps' := ⟨1⟩) ?_ ?_
  · cases k <;> krfl
  rfl

/-- The recognizer's answer on `Eq.casesOn`. -/
def ciEq : CasesInfo :=
  { declName := `Eq.casesOn, indName := `Eq, arity := 6, discrPos := 4, motivePos := 2,
    altsRange := 5...6, altNumParams := #[.ctor `Eq.refl 0] }

/-- The shipping recognizer recognizes `Eq.casesOn` over the closures. Reference: none. -/
theorem casesInfo_Eq {k : Bool} : casesInfo? (DD k) `Eq.casesOn = some ciEq := by cases k <;> krfl

/-- `visitCases`'s alternative of the `Eq.casesOn`: `Eq.refl ↦ fun y => y`. -/
def altsEq : Std.HashMap Name (Nat × Expr) := (∅ : Std.HashMap Name (Nat × Expr)).insert `Eq.refl (0, idB)

theorem altsEq_refl : altsEq[`Eq.refl]? = some (0, idB) := by
  simp only [altsEq, Std.HashMap.getElem?_insert_self]

/-- `visitCases` on the `Eq.casesOn`: the major's sort is `Prop` and `Eq` has one constructor,
so the result is the erased alternative. Reference: `iotaSing` of λ□ (`MR E/EWcbvEval.v`), applied
at erasure time (the `tCase` case of `erase`, `MR E/ErasureFunction.v:1016`). -/
theorem visitCases_run {k : Bool} {n : Nat} {L : LocalContext} :
    (visitCases (m := PureM) (n + 6) ciEq (args k)).runPure st ⟨L, [], none, {}⟩ (pcK k) ⟨0⟩ =
      .ok ((idL, st), ⟨1⟩) := by
  have hr : (ciEq.altsRange.toList) = [5] := by simp [ciEq]
  cases k <;>
  · rw [visitCases]
    apply bind_ok rfl
    apply bind_ok rfl
    apply bind_ok rfl
    refine bind_ok (a := .zero) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
    simp only [← forIn'_eq_forIn, Std.Rco.forIn'_eq_forIn'_toList, hr, List.forIn'_cons,
      List.forIn'_nil]
    refine bind_ok (a := (altsEq, none, ?sEnd)) (st' := st) (ps' := ⟨0⟩) ?_ ?_
    case sEnd => exact (ciEq.altNumParams.toSubarray 1 1)
    · rfl
    refine bind_ok (a := ∅) (st' := st) (ps' := ⟨0⟩) rfl ?_
    simp only [show Eq_ind.ctors[0]! = `Eq.refl from rfl, altsEq_refl, Std.HashMap.getElem?_empty,
      show (!Level.zero.isNeverZero && Eq_ind.numCtors == 1) = true from rfl, ite_true]
    apply bind_ok idB_run
    simp only [toArray_toSubarray]
    krfl

theorem withApp_ee {γ : Sort _} {k : Bool} (f : Expr → Array Expr → γ) :
    (ee k).withApp f = f (.const `Eq.casesOn [l1, l1]) (args k) := by
  cases k <;> krfl

/-- The term as an application to its last argument. -/
theorem ee_app {k : Bool} :
    ee k = .app (mkAppN (.const `Eq.casesOn [l1, l1]) #[tB, cT, motE, cT, mj k]) idB := by
  cases k <;> rfl

/-- `visitExpr` on the term. Reference: the `tApp` and `tCase` cases of `erase`
(`MR E/ErasureFunction.v:1009`, `:1016`). -/
theorem e_run {k : Bool} {n : Nat} {L : LocalContext} :
    (visitExpr (m := PureM) (n + 9) (ee k)).runPure st ⟨L, [], none, {}⟩ (pcK k) ⟨0⟩ =
      .ok ((idL, st), ⟨1⟩) := by
  rw [ee_app, visitExpr, ← ee_app]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ⟨0⟩) (by cases k <;> krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 7) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_ee]
  refine bind_ok (a := some ciEq) (st' := st) (ps' := ⟨0⟩) (by cases k <;> krfl) ?_
  change (withAppEtaToMinArity (m := PureM) (n + 6) _ 6 _).runPure _ _ _ _ = _
  rw [withAppEtaToMinArity]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := .app (.app motE cT) (mj k)) (st' := st) (ps' := ⟨0⟩) (by cases k <;> krfl) ?_
  rw [withApp_ee, withAppEtaToMinArity.go]
  exact visitCases_run

/-- The program `#erase` emits for NV-P and NV-K. -/
def pP : Program := .untyped [] (some idL)

/-- The pure path returns `pP` and no constant to inline. Reference: `erase`
(`MR E/ErasureFunction.v:989`). -/
theorem hpure {k : Bool} : erasePure (vw k) {} (DD k) (ee k) = .ok (pP, []) := by
  rw [erasePure, show travFuel = (travFuel - 9) + 9 by decide]
  rw [show ((visitExpr (m := PureM) (travFuel - 9 + 9) (ee k)).runPure {} { «config» := {} }
    ⟨DD k, vw k⟩ {}) = .ok ((idL, {}), ⟨1⟩) from e_run]
  rfl

/-- `#erase`'s entry point returns `pP` and no constant to inline. Reference: the hypotheses
`erase … = t'`, `erase_global_deps … = Σ'` of `erase_correct`
(`MR E/ErasureFunctionProperties.v:657`). -/
theorem hrun {k : Bool} : eraseEntry (vw k) {} (ee k) = pure (pP, []) := by
  simp only [eraseEntry, route, hcollect, hpure]

/-- `hfrag` on NV-P. -/
theorem hcollectP : collectDeps NVP.view NVP.cfg NVP.e = .ok (DD false) := rfl

/-- `hfrag` on NV-K. -/
theorem hcollectK : collectDeps NVK.view NVP.cfg NVK.e = .ok (DD true) := rfl

/-- `hrun` on NV-P. -/
theorem hrunP : eraseEntry NVP.view NVP.cfg NVP.e = pure (pP, []) := hrun (k := false)

/-- `hrun` on NV-K. -/
theorem hrunK : eraseEntry NVK.view NVP.cfg NVK.e = pure (pP, []) := hrun (k := true)

end EraseProof.Test.NVPK
