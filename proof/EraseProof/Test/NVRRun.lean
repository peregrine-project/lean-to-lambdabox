import EraseProof.Test.NVRData
import EraseProof.Test.NV1Run

/-!
# NV-R through the entry point of `#erase`

The hypotheses `hfrag` and `hrun` of the final theorem (`MR E/ErasureFunctionProperties.v:657
erase_correct`) on NV-R (`Test/NVRData.lean`). `hcollect` computes the fragment test's closure `D`
by kernel evaluation. `hrun` is the run of the entry point, evaluated one traversal call at a time
(`Test/Run.lean`): `N.rec` with four arguments takes `visitConstApp`'s recursor branch, `visitRec`,
which registers `N`, erases the minor premises `B.t` (registering `B`) and `fun n ih => ih`
(`minS_run`) and the major `N.s N.z` (`mj_run`), and returns the minors let-bound around the λ□
fixpoint of `N`'s block (`recFix`) applied to the major (`e_run`).
-/

open Lean Erasure EraseProof.Test

namespace EraseProof.Test.NVR

open EraseProof.Test.NV1 (tB cT B_ind Bf_ctor Bt_ctor iidB masksB bodyB stB)

/-- The closure of `e`, in the order the fragment test returns it. -/
def D : List ConstantInfo :=
  [.ctorInfo Bt_ctor, .ctorInfo Bf_ctor, .inductInfo B_ind, .ctorInfo Ns_ctor, .ctorInfo Nz_ctor,
    .inductInfo N_ind, .recInfo N_rec]

/-- The fragment test accepts `e` and returns the closure `D`, by kernel evaluation. Reference: the
environment `Σ'` of `erase_global_deps` (`MR E/ErasureFunction.v:1602`). -/
theorem hcollect : collectDeps view cfg e = .ok D := rfl

/-- The pure backend's context over the closure. -/
def pc : PureCtx := ⟨D, view⟩

variable {st : ErasureState} {ps : PureState} {dc : Name}

/-! ## The inductives `N` and `B` -/

/-- The λ□ inductive of `N`. -/
def iidN : InductiveId := ⟨mutualBlockKername [`N], 0⟩

/-- The argument masks of `N`'s constructors: the field of `N.s` is kept. -/
def masksN : InductiveArgMasks := [#[], #[.keep]]

/-- The λ□ body of `N`. -/
def bodyN : OneInductiveBody :=
  { name := toString `N, propositional := false,
    ctors := [⟨toString `N.z, 0⟩, ⟨toString `N.s, 1⟩], projs := [] }

/-- The state after registering `N`. -/
def stN (st : ErasureState) : ErasureState :=
  { st with
    inductives := st.inductives.insert `N (iidN, masksN)
    gdecls := (mutualBlockKername [`N], .inductiveDecl ⟨.finite, 0, [bodyN]⟩) :: st.gdecls }

/-- `register_inductive` on `N` when it is not registered. Reference: the `InductiveDecl` of
`erase_global_deps` (`MR E/ErasureFunction.v:1602`). -/
theorem register_N_new {L : LocalContext} {ls : List Local} {F : Option (Std.HashMap Name FVarId)}
    (h : st.inductives[`N]? = none) :
    (register_inductive (m := PureM) N_ind).runPure st ⟨L, ls, F, {}, dc⟩ pc ps =
      .ok (((iidN, masksN), stN st), ps) := by
  rw [register_inductive]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, show N_ind.name = `N from rfl, h]
  apply bind_ok (a := [bodyN]) (st' := { st with inductives := st.inductives.insert `N (iidN, masksN) })
    (ps' := ps) rfl
  apply bind_ok rfl
  apply bind_ok rfl
  simp only [Std.HashMap.getElem?_insert_self]
  rfl

/-- `register_inductive` on `N` when it is registered. Reference: none. -/
theorem register_N_found {tc : TravCtx} (h : st.inductives[`N]? = some (iidN, masksN)) :
    (register_inductive (m := PureM) N_ind).runPure st tc pc ps = .ok (((iidN, masksN), st), ps) := by
  rw [register_inductive]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, show N_ind.name = `N from rfl, h]
  rfl

/-- `register_inductive` on `B` when it is not registered. Reference: as `register_N_new`. -/
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

theorem stN_N : (stN st).inductives[`N]? = some (iidN, masksN) := by
  simp only [stN, Std.HashMap.getElem?_insert_self]

/-- The state after the minor premises: `N`, then `B` registered. -/
abbrev stM (st : ErasureState) : ErasureState := stB (stN st)

theorem stM_N : (stM st).inductives[`N]? = some (iidN, masksN) := by
  simp only [stM, NV1.stB, stN, Std.HashMap.getElem?_insert]
  rfl

/-! ## The minor premises -/

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

/-- The erasure of the minor premise `fun n ih => ih`. -/
def minSL : LBTerm :=
  .lambda (binderNameOf `n) (_root_.abstract x0
    (.lambda (binderNameOf `ih) (_root_.abstract x1 (.fvar x1))))

/-- `visitExpr` on the minor premise `fun n ih => ih`, from the counter's first variable: two λs
whose body, the variable `ih` of type `B`, is not erasable. Reference: the `tLambda` case of `erase`
(`MR E/ErasureFunction.v:1003`). -/
theorem minS_run {n : Nat} {L : LocalContext} :
    (visitExpr (m := PureM) (n + 8) minS).runPure st ⟨L, [], none, {}, dc⟩ pc ⟨0⟩ =
      .ok ((minSL, st), ⟨2⟩) := by
  krfl

/-! ## The major premise -/

/-- `visitConstructor` on `N.z` without arguments, `N` registered. Reference: the `tConstruct`
case of `erase` (`MR E/ErasureFunction.v:1014`). -/
theorem cZ_run {n : Nat} {L : LocalContext} (h : st.inductives[`N]? = some (iidN, masksN)) :
    (visitExpr (m := PureM) (n + 6) cZ).runPure st ⟨L, [], none, {}, dc⟩ pc ps =
      .ok ((.construct iidN 0 [], st), ps) := by
  rw [cZ, visitExpr]
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
  refine bind_ok (a := tN) (st' := st) (ps' := ps) (by krfl) ?_
  rw [withApp_const, withAppEtaToMinArity.go]
  rw [visitConstructor]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok (register_N_found h)
  simp only [toArray_toSubarray]
  krfl

theorem withApp_mj {γ : Sort _} (k : Expr → Array Expr → γ) : mj.withApp k = k cS #[cZ] := by
  krfl

/-- The arguments `visitConstructor` passes on for `N.s N.z`: no parameter, the field kept. -/
theorem args_s : #[cZ].extract 0 0 ++
    filter #[ConstructorArgRelevance.keep]
      (↑(#[cZ].toSubarray 0 (0 + 1)) : Array Expr) ++ #[cZ].extract (0 + 1) = #[cZ] := by
  apply Array.toList_inj.mp
  simp [filter, toArray_toSubarray]

/-- The erasure of the major `N.s N.z`. -/
def mjL : LBTerm := .app (.construct iidN 1 []) (.construct iidN 0 [])

/-- `visitExpr` on the major `N.s N.z`, `N` registered. Reference: the `tConstruct` case of
`erase` (`MR E/ErasureFunction.v:1014`). -/
theorem mj_run {n : Nat} {L : LocalContext} (h : st.inductives[`N]? = some (iidN, masksN)) :
    (visitExpr (m := PureM) (n + 12) mj).runPure st ⟨L, [], none, {}, dc⟩ pc ps =
      .ok ((mjL, st), ps) := by
  rw [mj, visitExpr, ← mj]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ps) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 10) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_mj]
  refine bind_ok (a := none) (st' := st) (ps' := ps) (by krfl) ?_
  refine bind_ok (a := some 1) (st' := st) (ps' := ps) (by krfl) ?_
  change (withAppEtaToMinArity (m := PureM) (n + 9) _ 1 _).runPure _ _ _ _ = _
  rw [withAppEtaToMinArity]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := tN) (st' := st) (ps' := ps) (by krfl) ?_
  rw [withApp_mj, withAppEtaToMinArity.go]
  rw [visitConstructor]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok (register_N_found h)
  dsimp only
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  simp only
  apply bind_ok rfl
  simp only [toArray_toSubarray, show Ns_ctor.numParams = 0 from rfl,
    show Ns_ctor.numFields = 1 from rfl, show Ns_ctor.cidx = 1 from rfl]
  rw [args_s]
  refine (congrArg (fun x : EraseT PureM LBTerm => x.runPure st ⟨L, [], none, {}, dc⟩ pc ps)
    (?_ : _ = visitAppArgs (m := PureM) (n + 8) (.construct iidN 1 []) #[cZ])).trans ?_
  · krfl
  rw [visitAppArgs, ← Array.foldlM_toList]
  simp only [List.foldlM_cons, List.foldlM_nil]
  refine bind_ok (a := mjL) (st' := st) (ps' := ps) ?_ ?_
  · apply bind_ok (cZ_run (n := n + 1) h)
    rfl
  rfl

/-! ## The run on NV-R -/

/-- The minor premises of `N.rec`, as `recShape` reads them from its type: `z` without fields, `s`
with the field `n` and one induction hypothesis about it. -/
def minorsN : List RecMinor := [⟨`z, [], []⟩, ⟨`s, [`n], [⟨0, 0, []⟩]⟩]

/-- `recShape` on `N.rec`'s type. Reference: none. -/
theorem recShape_N : recShape N_rec.numParams N_rec.numMotives N_rec.type
    ([Nz_ctor, Ns_ctor].map (·.numFields)) = some ([[`t]], minorsN) := by krfl

/-- `N`'s member of the recursor's block, as `recFix` erases it. -/
def memberN : RecMember :=
  ⟨`N, [`t], iidN, [(0, ⟨`z, [], []⟩, #[]), (1, ⟨`s, [`n], [⟨0, 0, []⟩]⟩, #[.keep])]⟩

/-- The λ□ fixpoint of `N`'s block, as `recFix` builds it for `N.rec`. -/
def fixL : LBTerm := recFix 2 0 false [memberN] 0

/-- The erasure of `e`: the minors let-bound around the fixpoint applied to the major. -/
def eL : LBTerm :=
  .letIn (binderNameOf `z) (.construct iidB 1 [])
    (.letIn (binderNameOf `s) minSL (.app fixL mjL))

theorem e_app : e = .app (mkAppN (.const `N.rec [.succ .zero]) #[motB, cT, minS]) mj := rfl

theorem withApp_e {γ : Sort _} (k : Expr → Array Expr → γ) :
    e.withApp k = k (.const `N.rec [.succ .zero]) #[motB, cT, minS, mj] := by
  krfl

/-- `visitExpr` on `e`: `visitConstApp`'s recursor branch, `visitRec`, on a saturated spine; `N` is
registered by the loop over the block, `B` by the first minor premise. Reference: none (DV-30). -/
theorem e_run {n : Nat} {L : LocalContext}
    (hN : st.inductives[`N]? = none) (hB : st.inductives[`B]? = none) :
    (visitExpr (m := PureM) (n + 20) e).runPure st ⟨L, [], none, {}, dc⟩ pc ⟨0⟩ =
      .ok ((eL, stM st), ⟨2⟩) := by
  rw [e_app, visitExpr, ← e_app]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 18) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_e]
  refine bind_ok (a := none) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  refine bind_ok (a := none) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  refine bind_ok (a := some (.recInfo N_rec)) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  change (visitRec (m := PureM) (n + 17) _ _).runPure _ _ _ _ = _
  rw [visitRec]
  refine bind_ok (a := [N_ind]) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  refine bind_ok (a := [Nz_ctor, Ns_ctor]) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  apply bind_ok rfl
  have hnsc : ∀ x, recStaysConstant x N_rec [N_ind] [Nz_ctor, Ns_ctor] = false := by
    intro x; cases x <;> krfl
  simp only [hnsc, Bool.false_eq_true, ↓reduceIte]
  rw [recShape_N]
  dsimp only
  rw [List.forIn_cons]
  simp only [List.forIn_nil, Std.toStream, Std.Stream.next?]
  refine bind_ok (a := (#[memberN], 2, [])) (st' := stN st) (ps' := ⟨0⟩) ?_ ?_
  · refine bind_ok (a := ForInStep.yield (#[memberN], 2, [])) (st' := stN st) (ps' := ⟨0⟩) ?_ ?_
    · apply bind_ok (register_N_new hN)
      rfl
    rfl
  apply bind_ok rfl
  rw [show N_rec.numParams + N_rec.numMotives + N_rec.numMinors + N_rec.numIndices + 1 = 4 from rfl,
    show N_rec.numParams + N_rec.numMotives = 1 from rfl,
    show N_rec.numMinors = 2 from rfl, show N_rec.numParams = 0 from rfl]
  rw [withAppEtaToMinArity]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := .app motB mj) (st' := stN st) (ps' := ⟨0⟩) (by krfl) ?_
  rw [withApp_e, withAppEtaToMinArity.go]
  simp only [show (#[motB, cT, minS, mj] : Array Expr).size = 4 from rfl, ge_iff_le, Nat.le_refl,
    ↓reduceIte]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := Level.succ .zero) (st' := stN st) (ps' := ⟨0⟩) (by krfl) ?_
  rw [show (#[motB, cT, minS, mj].extract 1 (1 + 2)).toList = [cT, minS] from rfl]
  simp only [List.mapM_cons, List.mapM_nil]
  refine bind_ok (a := [.construct iidB 1 [], minSL]) (st' := stM st) (ps' := ⟨2⟩) ?_ ?_
  · apply bind_ok (cT_run (n := n + 10) (by simp [stN, Std.HashMap.getElem?_insert, hB]))
    refine bind_ok (a := [minSL]) (st' := stM st) (ps' := ⟨2⟩) ?_ ?_
    · apply bind_ok (minS_run (n := n + 8))
      rfl
    rfl
  rw [visitAppArgs, show (#[motB, cT, minS, mj].extract (1 + 2) 4) = #[mj] from rfl,
    ← Array.foldlM_toList]
  simp only [List.foldlM_cons, List.foldlM_nil]
  refine bind_ok (a := .app fixL mjL) (st' := stM st) (ps' := ⟨2⟩) ?_ ?_
  · refine bind_ok (a := .app fixL mjL) (st' := stM st) (ps' := ⟨2⟩) ?_ ?_
    · apply bind_ok (mj_run (n := n + 3) stM_N)
      rfl
    rfl
  rw [visitAppArgs]
  rfl

/-- The program `#erase` emits for NV-R. -/
def p0 : Program :=
  .untyped [(mutualBlockKername [`B], .inductiveDecl ⟨.finite, 0, [bodyB]⟩),
    (mutualBlockKername [`N], .inductiveDecl ⟨.finite, 0, [bodyN]⟩)] (some eL)

/-- The pure path on NV-R's closure returns `p0` and no constant to inline. Reference: `erase`
(`MR E/ErasureFunction.v:989`) and `erase_global_deps` (`MR E/ErasureFunction.v:1602`). -/
theorem hpure : erasePure view cfg D e = .ok (p0, []) := by
  rw [erasePure, show travFuel = (travFuel - 20) + 20 by decide]
  rw [show ((visitExpr (m := PureM) (travFuel - 20 + 20) e).runPure {} { «config» := cfg }
    ⟨D, view⟩ {}) = .ok ((eL, stM {}), ⟨2⟩) from
      e_run Std.HashMap.getElem?_empty Std.HashMap.getElem?_empty]
  rfl

/-- `#erase`'s entry point on NV-R returns `p0` and no constant to inline. Reference: the
hypotheses `erase … = t'` and `erase_global_deps … = Σ'` of `erase_correct`
(`MR E/ErasureFunctionProperties.v:657`). -/
theorem hrun : eraseEntry view cfg e = pure (p0, []) := by
  simp only [eraseEntry, route, hcollect, hpure]
end EraseProof.Test.NVR
