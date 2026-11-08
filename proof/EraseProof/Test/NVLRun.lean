import EraseProof.Test.NVLData
import EraseProof.Test.NV1Run

/-!
# NV-R through the entry point of `#erase`

The hypotheses `hfrag` and `hrun` of the final theorem (`MR E/ErasureFunctionProperties.v:657
erase_correct`) on NV-R (`Test/NVRData.lean`). `hcollect` computes the fragment test's closure `D`
by kernel evaluation. `hrun` is the run of the entry point, evaluated one traversal call at a time
(`Test/Run.lean`): `Nat.rec` with four arguments takes `visitConstApp`'s recursor branch, `visitRec`,
which registers `Nat`, erases the minor premises `B.t` (registering `B`) and `fun n ih => ih`
(`minS_run`) and the major `Nat.succ N.z` (`mj_run`), and returns the minors let-bound around the λ□
fixpoint of `Nat`'s block (`recFix`) applied to the major (`e_run`).
-/

open Lean Erasure EraseProof.Test

namespace EraseProof.Test.NVL

open EraseProof.Test.NV1 (tB cT B_ind Bf_ctor Bt_ctor iidB masksB bodyB stB)

/-- The closure of `e`, in the order the fragment test returns it. -/
def D : List ConstantInfo :=
  [.ctorInfo Bt_ctor, .ctorInfo Bf_ctor, .inductInfo B_ind, .ctorInfo Succ_ctor, .ctorInfo Zero_ctor,
    .inductInfo Nat_ind, .recInfo Nat_rec]

/-- The fragment test accepts `e` and returns the closure `D`, by kernel evaluation. Reference: the
environment `Σ'` of `erase_global_deps` (`MR E/ErasureFunction.v:1602`). -/
theorem hcollect : collectDeps view cfg e = .ok D := rfl

/-- The pure backend's context over the closure. -/
def pc : PureCtx := ⟨D, view⟩

variable {st : ErasureState} {ps : PureState} {dc : Name}

/-! ## The inductives `Nat` and `B` -/

/-- The λ□ inductive of `Nat`. -/
def iidN : InductiveId := ⟨mutualBlockKername [`Nat], 0⟩

/-- The argument masks of `Nat`'s constructors: the field of `Nat.succ` is kept. -/
def masksN : InductiveArgMasks := [#[], #[.keep]]

/-- The λ□ body of `Nat`. -/
def bodyN : OneInductiveBody :=
  { name := toString `Nat, propositional := false,
    ctors := [⟨toString `Nat.zero, 0⟩, ⟨toString `Nat.succ, 1⟩], projs := [] }

/-- The state after registering `Nat`. -/
def stN (st : ErasureState) : ErasureState :=
  { st with
    inductives := st.inductives.insert `Nat (iidN, masksN)
    gdecls := (mutualBlockKername [`Nat], .inductiveDecl ⟨.finite, 0, [bodyN]⟩) :: st.gdecls }

/-- `register_inductive` on `Nat` when it is not registered. Reference: the `InductiveDecl` of
`erase_global_deps` (`MR E/ErasureFunction.v:1602`). -/
theorem register_Nat_new {L : LocalContext} {ls : List Local} {F : Option (Std.HashMap Name FVarId)}
    (h : st.inductives[`Nat]? = none) :
    (register_inductive (m := PureM) Nat_ind).runPure st ⟨L, ls, F, cfg, dc⟩ pc ps =
      .ok (((iidN, masksN), stN st), ps) := by
  rw [register_inductive]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, show Nat_ind.name = `Nat from rfl, h]
  apply bind_ok (a := [bodyN]) (st' := { st with inductives := st.inductives.insert `Nat (iidN, masksN) })
    (ps' := ps) rfl
  apply bind_ok rfl
  apply bind_ok rfl
  simp only [Std.HashMap.getElem?_insert_self]
  rfl

/-- `register_inductive` on `Nat` when it is registered. Reference: none. -/
theorem register_Nat_found {tc : TravCtx} (h : st.inductives[`Nat]? = some (iidN, masksN)) :
    (register_inductive (m := PureM) Nat_ind).runPure st tc pc ps = .ok (((iidN, masksN), st), ps) := by
  rw [register_inductive]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, show Nat_ind.name = `Nat from rfl, h]
  rfl

/-- `register_inductive` on `B` when it is not registered. Reference: as `register_Nat_new`. -/
theorem register_B_new {L : LocalContext} {ls : List Local} {F : Option (Std.HashMap Name FVarId)}
    (h : st.inductives[`B]? = none) :
    (register_inductive (m := PureM) B_ind).runPure st ⟨L, ls, F, cfg, dc⟩ pc ps =
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

theorem stN_Nat : (stN st).inductives[`Nat]? = some (iidN, masksN) := by
  simp only [stN, Std.HashMap.getElem?_insert_self]

/-- The state after the minor premises: `Nat`, then `B` registered. -/
abbrev stM (st : ErasureState) : ErasureState := stB (stN st)

theorem stM_Nat : (stM st).inductives[`Nat]? = some (iidN, masksN) := by
  simp only [stM, NV1.stB, stN, Std.HashMap.getElem?_insert]
  rfl

/-! ## The minor premises -/

/-- `visitExpr` on `B.t` outside any binder, `B` not registered. Reference: the `tConstruct` case
of `erase` (`MR E/ErasureFunction.v:1014`). -/
theorem cT_run {n : Nat} {L : LocalContext} (h : st.inductives[`B]? = none) :
    (visitExpr (m := PureM) (n + 6) cT).runPure st ⟨L, [], none, cfg, dc⟩ pc ps =
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
    (visitExpr (m := PureM) (n + 8) minS).runPure st ⟨L, [], none, cfg, dc⟩ pc ⟨0⟩ =
      .ok ((minSL, st), ⟨2⟩) := by
  krfl

/-! ## The major premise -/

/-- The erasure of a Nat literal under `nat := .peano`: λ□'s constructor chain of `Nat`. -/
def natL : Nat → LBTerm
  | 0 => .construct iidN 0 []
  | k + 1 => .app (.construct iidN 1 []) (natL k)

/-- `visitExpr` on the literal `0`, `Nat` registered: `visitLiteral` erases it as `Nat.zero`.
Reference: none (Lean's literals; `Erases.litZero`). -/
theorem lit0_run {n : Nat} {L : LocalContext} (h : st.inductives[`Nat]? = some (iidN, masksN)) :
    (visitExpr (m := PureM) (n + 4) (.lit (.natVal 0))).runPure st ⟨L, [], none, cfg, dc⟩ pc ps =
      .ok ((natL 0, st), ps) := by
  rw [visitExpr]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ps) (by krfl) ?_
  change (visitLiteral (m := PureM) (n + 3) _).runPure _ _ _ _ = _
  rw [visitLiteral]
  apply bind_ok rfl
  change (visitConstructor (m := PureM) (n + 2) `Nat.zero #[]).runPure _ _ _ _ = _
  rw [visitConstructor]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok (register_Nat_found h)
  simp only [toArray_toSubarray]
  krfl

/-- The arguments `visitConstructor` passes on for `Nat.succ a`: no parameter, the field kept. -/
theorem args_s (a : Expr) : #[a].extract 0 0 ++
    filter #[ConstructorArgRelevance.keep]
      (↑(#[a].toSubarray 0 (0 + 1)) : Array Expr) ++ #[a].extract (0 + 1) = #[a] := by
  apply Array.toList_inj.mp
  simp [filter, toArray_toSubarray]

/-- `visitExpr` on the literal `k + 1`, `Nat` registered: `visitLiteral` erases it as `Nat.succ`
applied to the literal `k`. Reference: none (Lean's literals; `Erases.litSucc`). -/
theorem litS_run {n k : Nat} {L : LocalContext} (hk : k + 1 ≤ peanoMaxLiteral)
    (h : st.inductives[`Nat]? = some (iidN, masksN))
    (ih : (visitExpr (m := PureM) (n + 1) (.lit (.natVal k))).runPure st ⟨L, [], none, cfg, dc⟩ pc
      ps = .ok ((natL k, st), ps)) :
    (visitExpr (m := PureM) (n + 5) (.lit (.natVal (k + 1)))).runPure st ⟨L, [], none, cfg, dc⟩ pc
      ps = .ok ((natL (k + 1), st), ps) := by
  rw [visitExpr]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ps) (by krfl) ?_
  change (visitLiteral (m := PureM) (n + 4) _).runPure _ _ _ _ = _
  rw [visitLiteral]
  apply bind_ok rfl
  simp only [show cfg.nat = .peano from rfl, show ¬ (k + 1 > peanoMaxLiteral) by omega,
    Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
  change (visitConstructor (m := PureM) (n + 3) `Nat.succ #[.lit (.natVal k)]).runPure _ _ _ _ = _
  rw [visitConstructor]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok (register_Nat_found h)
  dsimp only
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  simp only
  apply bind_ok rfl
  simp only [toArray_toSubarray, show Succ_ctor.numParams = 0 from rfl,
    show Succ_ctor.numFields = 1 from rfl, show Succ_ctor.cidx = 1 from rfl]
  rw [args_s]
  refine (congrArg (fun x : EraseT PureM LBTerm => x.runPure st ⟨L, [], none, cfg, dc⟩ pc ps)
    (?_ : _ = visitAppArgs (m := PureM) (n + 2) (.construct iidN 1 []) #[.lit (.natVal k)])).trans ?_
  · krfl
  rw [visitAppArgs, ← Array.foldlM_toList]
  simp only [List.foldlM_cons, List.foldlM_nil]
  refine bind_ok (a := natL (k + 1)) (st' := st) (ps' := ps) ?_ ?_
  · apply bind_ok ih
    rfl
  rfl

/-- The erasure of the major `2`. -/
def mjL : LBTerm := natL 2

/-- `visitExpr` on the major `2`, `Nat` registered. -/
theorem mj_run {n : Nat} {L : LocalContext} (h : st.inductives[`Nat]? = some (iidN, masksN)) :
    (visitExpr (m := PureM) (n + 12) mj).runPure st ⟨L, [], none, cfg, dc⟩ pc ps =
      .ok ((mjL, st), ps) :=
  litS_run (n := n + 7) (by decide) h (litS_run (n := n + 3) (by decide) h (lit0_run h))

/-! ## The run on NV-L -/

/-- The minor premises of `Nat.rec`, as `recShape` reads them from its type: `z` without fields, `s`
with the field `n` and one induction hypothesis about it. -/
def minorsN : List RecMinor := [⟨`zero, [], []⟩, ⟨`succ, [`n], [⟨0, 0, []⟩]⟩]

/-- `recShape` on `Nat.rec`'s type. Reference: none. -/
theorem recShape_N : recShape Nat_rec.numParams Nat_rec.numMotives Nat_rec.type
    ([Zero_ctor, Succ_ctor].map (·.numFields)) = some ([[`t]], minorsN) := by krfl

/-- `Nat`'s member of the recursor's block, as `recFix` erases it. -/
def memberN : RecMember :=
  ⟨`Nat, [`t], iidN, [(0, ⟨`zero, [], []⟩, #[]), (1, ⟨`succ, [`n], [⟨0, 0, []⟩]⟩, #[.keep])]⟩

/-- The λ□ fixpoint of `Nat`'s block, as `recFix` builds it for `Nat.rec`. -/
def fixL : LBTerm := recFix 2 0 false [memberN] 0

/-- The erasure of `e`: the minors let-bound around the fixpoint applied to the major. -/
def eL : LBTerm :=
  .letIn (binderNameOf `zero) (.construct iidB 1 [])
    (.letIn (binderNameOf `succ) minSL (.app fixL mjL))

theorem e_app : e = .app (mkAppN (.const `Nat.rec [.succ .zero]) #[motB, cT, minS]) mj := rfl

theorem withApp_e {γ : Sort _} (k : Expr → Array Expr → γ) :
    e.withApp k = k (.const `Nat.rec [.succ .zero]) #[motB, cT, minS, mj] := by
  krfl

/-- `visitExpr` on `e`: `visitConstApp`'s recursor branch, `visitRec`, on a saturated spine; `Nat` is
registered by the loop over the block, `B` by the first minor premise. Reference: none (DV-30). -/
theorem e_run {n : Nat} {L : LocalContext}
    (hN : st.inductives[`Nat]? = none) (hB : st.inductives[`B]? = none) :
    (visitExpr (m := PureM) (n + 20) e).runPure st ⟨L, [], none, cfg, dc⟩ pc ⟨0⟩ =
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
  refine bind_ok (a := some (.recInfo Nat_rec)) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  change (visitRec (m := PureM) (n + 17) _ _).runPure _ _ _ _ = _
  rw [visitRec]
  refine bind_ok (a := [Nat_ind]) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  refine bind_ok (a := [Zero_ctor, Succ_ctor]) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  apply bind_ok rfl
  have hnsc : recStaysConstant .peano Nat_rec [Nat_ind] [Zero_ctor, Succ_ctor] = false := by krfl
  simp only [show cfg.nat = .peano from rfl, hnsc, Bool.false_eq_true, ↓reduceIte]
  rw [recShape_N]
  dsimp only
  rw [List.forIn_cons]
  simp only [List.forIn_nil, Std.toStream, Std.Stream.next?]
  refine bind_ok (a := (#[memberN], 2, [])) (st' := stN st) (ps' := ⟨0⟩) ?_ ?_
  · refine bind_ok (a := ForInStep.yield (#[memberN], 2, [])) (st' := stN st) (ps' := ⟨0⟩) ?_ ?_
    · apply bind_ok (register_Nat_new hN)
      rfl
    rfl
  apply bind_ok rfl
  rw [show Nat_rec.numParams + Nat_rec.numMotives + Nat_rec.numMinors + Nat_rec.numIndices + 1 = 4 from rfl,
    show Nat_rec.numParams + Nat_rec.numMotives = 1 from rfl,
    show Nat_rec.numMinors = 2 from rfl, show Nat_rec.numParams = 0 from rfl]
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
    · apply bind_ok (mj_run (n := n + 3) stM_Nat)
      rfl
    rfl
  rw [visitAppArgs]
  rfl

/-- The program `#erase` emits for NV-R. -/
def p0 : Program :=
  .untyped [(mutualBlockKername [`B], .inductiveDecl ⟨.finite, 0, [bodyB]⟩),
    (mutualBlockKername [`Nat], .inductiveDecl ⟨.finite, 0, [bodyN]⟩)] (some eL)

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
end EraseProof.Test.NVL
