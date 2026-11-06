import EraseProof.Test.NVQData
import EraseProof.Test.NV1Run

/-!
# NV-Q through the entry point of `#erase`

The hypotheses `hfrag` and `hrun` of the final theorem (`MR E/ErasureFunctionProperties.v:657
erase_correct`) on NV-Q (`Test/NVQData.lean`). `hcollect` computes the fragment test's closure `D`
by kernel evaluation: it holds the quotient constants `Quot.lift`, `Quot.mk` and `Quot` (from
`Quot.lift`'s type), with `Eq`. `hrun` is the run of the entry point, evaluated one traversal call
at a time (`Test/Run.lean`): `Quot.lift` with seven arguments takes `visitConstApp`'s `Quot.lift`
branch, which erases the function `fun x => x` (`idF_run`) and applies it to the erasures of the
quotient and of the argument beyond the arity; `Quot.mk` erases as its element `fun y => y`
(`qm_run`, `idB_run`) and `B.t` as the constructor of `B`'s block, which it registers.
-/

open Lean Erasure EraseProof.Test

namespace EraseProof.Test.NVQ

open EraseProof.Test.NV1 (tB cT B_ind Bf_ctor Bt_ctor iidB masksB bodyB stB)
open EraseProof.Test.NVP (l1 Eq_ind Eq_refl Eq_rec)

/-- The closure of `e`, in the order the fragment test returns it. -/
def D : List ConstantInfo :=
  [.quotInfo QuotMk_val, .axiomInfo hR_ax, .axiomInfo R_ax, .ctorInfo Bt_ctor, .ctorInfo Bf_ctor,
    .inductInfo B_ind, .quotInfo Quot_val, .ctorInfo Eq_refl, .recInfo Eq_rec, .inductInfo Eq_ind,
    .quotInfo QuotLift_val]

/-- The fragment test accepts `e` and returns the closure `D`, by kernel evaluation. Reference: the
environment `Σ'` of `erase_global_deps` (`MR E/ErasureFunction.v:1602`). -/
theorem hcollect : collectDeps view cfg e = .ok D := rfl

/-- The pure backend's context over the closure. -/
def pc : PureCtx := ⟨D, view⟩

variable {st : ErasureState} {ps : PureState} {dc : Name}

/-- `register_inductive` on `B` when it is not registered. Reference: the `InductiveDecl` of
`erase_global_deps` (`MR E/ErasureFunction.v:1602`). -/
theorem register_B_new {L : LocalContext} {ls : List Local} {F : Option (Std.HashMap Name FVarId)}
    (h : st.inductives[`B]? = none) :
    (register_inductive (m := PureM) B_ind).runPure st ⟨L, ls, F, {}, dc⟩ pc ps =
      .ok (((iidB, masksB), stB st), ps) := by
  rw [register_inductive]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, show B_ind.name = `B from rfl, h]
  apply bind_ok (a := [bodyB]) (st' := { st with inductives := st.inductives.insert `B (iidB, masksB) })
    (ps' := ps) rfl
  apply bind_ok rfl
  apply bind_ok rfl
  simp only [Std.HashMap.getElem?_insert_self]
  rfl

/-- `visitExpr` on `B.t` outside any binder, `B` not registered. Reference: the `tConstruct` case
of `erase` (`MR E/ErasureFunction.v:1014`). -/
theorem cT_run {n : Nat} {L : LocalContext} (h : st.inductives[`B]? = none) :
    (visitExpr (m := PureM) (n + 6) cT).runPure st ⟨L, [], none, {}, dc⟩ pc ps =
      .ok ((.construct iidB 1 [], stB st), ps) := by
  rw [cT, visitExpr]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ps) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 4) _).runPure _ _ _ _ = _
  rw [visitConstApp]
  refine bind_ok (a := none) (st' := st) (ps' := ps) (by krfl) ?_
  refine bind_ok (a := some 0) (st' := st) (ps' := ps) (by krfl) ?_
  change (withAppEtaToMinArity (m := PureM) (n + 3) _ 0 _).runPure _ _ _ _ = _
  rw [withAppEtaToMinArity]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := tB) (st' := st) (ps' := ps) (by krfl) ?_
  rw [withApp_const, withAppEtaToMinArity.go]
  rw [visitConstructor]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok (register_B_new h)
  simp only [toArray_toSubarray]
  krfl

/-- The traversal's first two fresh locals. -/
def x0 : FVarId := ⟨.num `_pure 0⟩
def x1 : FVarId := ⟨.num `_pure 1⟩
/-- The erasures of `fun x => x` and `fun y => y`. -/
def idFL : LBTerm := .lambda (binderNameOf `x) (_root_.abstract x0 (.fvar x0))
def idBL : LBTerm := .lambda (binderNameOf `y) (_root_.abstract x1 (.fvar x1))

/-- `visitExpr` on the function `fun x => x`, the first fresh local. Reference: the `tLambda` case
of `erase` (`MR E/ErasureFunction.v:1003`). -/
theorem idF_run {n : Nat} {L : LocalContext} :
    (visitExpr (m := PureM) (n + 4) idF).runPure st ⟨L, [], none, {}, dc⟩ pc ⟨0⟩ =
      .ok ((idFL, st), ⟨1⟩) := by
  rw [idF, visitExpr, ← idF]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [visitLambda]
  refine bind_ok (a := x0) (st' := st) (ps' := ⟨1⟩) rfl ?_
  refine bind_ok (a := .fvar x0) (st' := st) (ps' := ⟨1⟩) (by krfl) ?_
  rfl

/-- `visitExpr` on the element `fun y => y`, the second fresh local. Reference: the `tLambda` case
of `erase` (`MR E/ErasureFunction.v:1003`). -/
theorem idB_run {n : Nat} {L : LocalContext} :
    (visitExpr (m := PureM) (n + 4) idB).runPure st ⟨L, [], none, {}, dc⟩ pc ⟨1⟩ =
      .ok ((idBL, st), ⟨2⟩) := by
  rw [idB, visitExpr, ← idB]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ⟨1⟩) (by krfl) ?_
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [visitLambda]
  refine bind_ok (a := x1) (st' := st) (ps' := ⟨2⟩) rfl ?_
  refine bind_ok (a := .fvar x1) (st' := st) (ps' := ⟨2⟩) (by krfl) ?_
  rfl

theorem qm_app : qm = .app (mkAppN (.const `Quot.mk [l1]) #[tBB, cR]) idB := rfl

theorem withApp_qm {γ : Sort _} (k : Expr → Array Expr → γ) :
    qm.withApp k = k (.const `Quot.mk [l1]) #[tBB, cR, idB] := by
  krfl

/-- `visitExpr` on the quotient `Quot.mk R (fun y => y)`: `visitConstApp`'s `Quot.mk` branch
erases it as its element. Reference: DV-29. -/
theorem qm_run {n : Nat} {L : LocalContext} :
    (visitExpr (m := PureM) (n + 7) qm).runPure st ⟨L, [], none, {}, dc⟩ pc ⟨1⟩ =
      .ok ((idBL, st), ⟨2⟩) := by
  rw [qm_app, visitExpr, ← qm_app]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ⟨1⟩) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 5) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_qm]
  refine bind_ok (a := none) (st' := st) (ps' := ⟨1⟩) (by krfl) ?_
  refine bind_ok (a := none) (st' := st) (ps' := ⟨1⟩) (by krfl) ?_
  refine bind_ok (a := some (.quotInfo QuotMk_val)) (st' := st) (ps' := ⟨1⟩) (by krfl) ?_
  change (withAppEtaToMinArity (m := PureM) (n + 4) _ 3 _).runPure _ _ _ _ = _
  rw [withAppEtaToMinArity]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := .app (.app (.const `Quot [l1]) tBB) cR) (st' := st) (ps' := ⟨1⟩) (by krfl) ?_
  rw [withApp_qm, withAppEtaToMinArity.go]
  refine bind_ok (a := idB) (st' := st) (ps' := ⟨1⟩) rfl ?_
  refine bind_ok (a := idBL) (st' := st) (ps' := ⟨2⟩) idB_run ?_
  rw [visitAppArgs]
  rfl

theorem e_app :
    e = .app (mkAppN (.const `Quot.lift [l1, l1]) #[tBB, cR, tBB, idF, .const `hR [], qm]) cT := rfl

theorem withApp_e {γ : Sort _} (k : Expr → Array Expr → γ) :
    e.withApp k = k (.const `Quot.lift [l1, l1]) #[tBB, cR, tBB, idF, .const `hR [], qm, cT] := by
  krfl

/-- The erasure of `e`: `(fun x => x) (fun y => y) B.t` in λ□. -/
def eL : LBTerm := .app (.app idFL idBL) (.construct iidB 1 [])

/-- `visitExpr` on `e`: `visitConstApp`'s `Quot.lift` branch on seven arguments. Reference:
DV-29. -/
theorem e_run {n : Nat} {L : LocalContext} (h : st.inductives[`B]? = none) :
    (visitExpr (m := PureM) (n + 11) e).runPure st ⟨L, [], none, {}, dc⟩ pc ⟨0⟩ =
      .ok ((eL, stB st), ⟨2⟩) := by
  rw [e_app, visitExpr, ← e_app]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 9) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_e]
  refine bind_ok (a := none) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  refine bind_ok (a := none) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  refine bind_ok (a := some (.quotInfo QuotLift_val)) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  change (withAppEtaToMinArity (m := PureM) (n + 8) _ 6 _).runPure _ _ _ _ = _
  rw [withAppEtaToMinArity]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := tB) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  rw [withApp_e, withAppEtaToMinArity.go]
  refine bind_ok (a := idF) (st' := st) (ps' := ⟨0⟩) rfl ?_
  refine bind_ok (a := idFL) (st' := st) (ps' := ⟨1⟩) idF_run ?_
  rw [visitAppArgs, show (#[tBB, cR, tBB, idF, .const `hR [], qm, cT] : Array Expr).extract 5 =
    #[qm, cT] from rfl, ← Array.foldlM_toList]
  simp only [List.foldlM_cons, List.foldlM_nil]
  refine bind_ok (a := .app idFL idBL) (st' := st) (ps' := ⟨2⟩) ?_ ?_
  · apply bind_ok qm_run
    rfl
  refine bind_ok (a := eL) (st' := stB st) (ps' := ⟨2⟩) ?_ ?_
  · apply bind_ok (cT_run h)
    rfl
  rfl

/-- The program `#erase` emits for NV-Q. -/
def p0 : Program :=
  .untyped [(mutualBlockKername [`B], .inductiveDecl ⟨.finite, 0, [bodyB]⟩)] (some eL)

/-- The pure path on NV-Q's closure returns `p0` and no constant to inline. Reference: `erase`
(`MR E/ErasureFunction.v:989`) and `erase_global_deps` (`MR E/ErasureFunction.v:1602`). -/
theorem hpure : erasePure view cfg D e = .ok (p0, []) := by
  rw [erasePure, show travFuel = (travFuel - 11) + 11 by decide]
  rw [show ((visitExpr (m := PureM) (travFuel - 11 + 11) e).runPure {} { «config» := cfg }
    ⟨D, view⟩ {}) = .ok ((eL, stB {}), ⟨2⟩) from e_run Std.HashMap.getElem?_empty]
  rfl

/-- `#erase`'s entry point on NV-Q returns `p0` and no constant to inline. Reference: the
hypotheses `erase … = t'` and `erase_global_deps … = Σ'` of `erase_correct`
(`MR E/ErasureFunctionProperties.v:657`). -/
theorem hrun : eraseEntry view cfg e = pure (p0, []) := by
  simp only [eraseEntry, route, hcollect, hpure]

end EraseProof.Test.NVQ
