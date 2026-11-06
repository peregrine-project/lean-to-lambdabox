import EraseProof.Test.NV2Data
import EraseProof.Test.NV1Run

/-!
# NV-2 through the entry point of `#erase`

The hypotheses `hfrag` and `hrun` of the final theorem (`MR E/ErasureFunctionProperties.v:657
erase_correct`) on NV-2 (`Test/NV2Data.lean`). `hcollect` computes the fragment test's closure `D`
by kernel evaluation. `hrun` is the run of the entry point, evaluated one traversal call at a time
(`Test/Run.lean`): the major `W.s B.t T.i` is erased to the constructor applied to `B.t` and to □ for
the proof `T.i` (`mj_run`), registering `W` and then `B`; the alternatives are `B.f` and, under the
two fields `b` and `h`, the variable `b` (`visitAlt_s_run`); the result is the λ□ `case` on `W`
(`visitCases_run`, `e_run`).
-/

open Lean Erasure EraseProof.Test

namespace EraseProof.Test.NV2

open EraseProof.Test.NV1 (tB cF cT B_ind Bf_ctor Bt_ctor B_rec iidB masksB bodyB stB)

/-- The closure of `e`, in the order the fragment test returns it. -/
def D : List ConstantInfo :=
  [.ctorInfo Ti_ctor, .recInfo T_rec, .inductInfo T_ind, .ctorInfo Bt_ctor, .ctorInfo Bf_ctor,
    .inductInfo B_ind, .ctorInfo Ws_ctor, .ctorInfo Wn_ctor, .inductInfo W_ind, .recInfo W_rec,
    .defnInfo W_casesOn]

/-- The fragment test accepts `e` and returns the closure `D`, by kernel evaluation. Reference: the
environment `Σ'` of `erase_global_deps` (`MR E/ErasureFunction.v:1602`). -/
theorem hcollect : collectDeps view cfg e = .ok D := rfl

/-- The pure backend's context over the closure. -/
def pc : PureCtx := ⟨D, view⟩

variable {st : ErasureState} {ps : PureState}

/-! ## The inductives `W` and `B` -/

/-- The λ□ inductive of `W`. -/
def iidW : InductiveId := ⟨mutualBlockKername [`W], 0⟩

/-- The argument masks of `W`'s constructors: both fields of `W.s` are kept. -/
def masksW : InductiveArgMasks := [#[], #[.keep, .keep]]

/-- The λ□ body of `W`. -/
def bodyW : OneInductiveBody :=
  { name := toString `W, propositional := false,
    ctors := [⟨toString `W.n, 0⟩, ⟨toString `W.s, 2⟩], projs := [] }

/-- The state after registering `W`. -/
def stW (st : ErasureState) : ErasureState :=
  { st with
    inductives := st.inductives.insert `W (iidW, masksW)
    gdecls := (mutualBlockKername [`W], .inductiveDecl ⟨.finite, 0, [bodyW]⟩) :: st.gdecls }

/-- `register_inductive` on `W` when it is not registered. Reference: the `InductiveDecl` of
`erase_global_deps` (`MR E/ErasureFunction.v:1602`). -/
theorem register_W_new {L : LocalContext} {ls : List Local} {F : Option (Std.HashMap Name FVarId)}
    (h : st.inductives[`W]? = none) :
    (register_inductive (m := PureM) W_ind).runPure st ⟨L, ls, F, {}⟩ pc ps =
      .ok (((iidW, masksW), stW st), ps) := by
  rw [register_inductive]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, show W_ind.name = `W from rfl, h]
  apply bind_ok (a := [bodyW]) (st' := { st with inductives := st.inductives.insert `W (iidW, masksW) })
    (ps' := ps) rfl
  apply bind_ok rfl
  apply bind_ok rfl
  simp only [Std.HashMap.getElem?_insert_self]
  rfl

/-- `register_inductive` on `W` when it is registered. Reference: none. -/
theorem register_W_found {tc : TravCtx} (h : st.inductives[`W]? = some (iidW, masksW)) :
    (register_inductive (m := PureM) W_ind).runPure st tc pc ps = .ok (((iidW, masksW), st), ps) := by
  rw [register_inductive]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, show W_ind.name = `W from rfl, h]
  rfl

/-- `register_inductive` on `B` when it is not registered. Reference: as `register_W_new`. -/
theorem register_B_new {L : LocalContext} {ls : List Local} {F : Option (Std.HashMap Name FVarId)}
    (h : st.inductives[`B]? = none) :
    (register_inductive (m := PureM) B_ind).runPure st ⟨L, ls, F, {}⟩ pc ps =
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

/-- `register_inductive` on `B` when it is registered. Reference: none. -/
theorem register_B_found {tc : TravCtx} (h : st.inductives[`B]? = some (iidB, masksB)) :
    (register_inductive (m := PureM) B_ind).runPure st tc pc ps = .ok (((iidB, masksB), st), ps) := by
  rw [register_inductive]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, show B_ind.name = `B from rfl, h]
  rfl

theorem stW_W : (stW st).inductives[`W]? = some (iidW, masksW) := by
  simp only [stW, Std.HashMap.getElem?_insert_self]

/-! ## Constructors -/

/-- `visitConstructor` on `B.f` (index 0) or `B.t` (index 1) without arguments, outside any
binder, given the registration of `B`. Reference: the `tConstruct` case of `erase`
(`MR E/ErasureFunction.v:1014`). -/
theorem visitConstructorB_run {n k : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)}
    {c : Name} {st' : ErasureState} (hc : c = `B.f ∧ k = 0 ∨ c = `B.t ∧ k = 1)
    (hreg : (register_inductive (m := PureM) B_ind).runPure st ⟨L, [], F, {}⟩ pc ps =
      .ok (((iidB, masksB), st'), ps)) :
    (visitConstructor (m := PureM) (n + 2) c #[]).runPure st ⟨L, [], F, {}⟩ pc ps =
      .ok ((.construct iidB k [], st'), ps) := by
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · rw [visitConstructor]
    apply bind_ok rfl
    apply bind_ok rfl
    apply bind_ok hreg
    simp only [toArray_toSubarray]
    krfl

/-- `visitExpr` on `B.f` or `B.t` outside any binder, given the registration of `B`. Reference:
the `tConstruct` case of `erase` (`MR E/ErasureFunction.v:1014`). -/
theorem visitExpr_ctorB_run {n k : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)}
    {c : Name} {st' : ErasureState} (hc : c = `B.f ∧ k = 0 ∨ c = `B.t ∧ k = 1)
    (hreg : (register_inductive (m := PureM) B_ind).runPure st ⟨L, [], F, {}⟩ pc ps =
      .ok (((iidB, masksB), st'), ps)) :
    (visitExpr (m := PureM) (n + 6) (.const c [])).runPure st ⟨L, [], F, {}⟩ pc ps =
      .ok ((.construct iidB k [], st'), ps) := by
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · rw [visitExpr]
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
    exact visitConstructorB_run (by simp) hreg

/-- `visitExpr` on the proof `T.i`: erasable, so □. Reference: the erasable case of `erase`
(`MR E/ErasureFunction.v:989`). -/
theorem visitExpr_I_run {n : Nat} {tc : TravCtx} :
    (visitExpr (m := PureM) (n + 1) cI).runPure st tc pc ps = .ok ((.box, st), ps) := by
  rw [cI, visitExpr]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := true) (st' := st) (ps' := ps) (by krfl) ?_
  rfl

/-- The arguments `visitConstructor` passes on for `W.s B.t T.i`: no parameter, both fields kept. -/
theorem args_s : #[cT, cI].extract 0 0 ++
    filter #[ConstructorArgRelevance.keep, ConstructorArgRelevance.keep]
      (↑(#[cT, cI].toSubarray 0 (0 + 2)) : Array Expr) ++ #[cT, cI].extract (0 + 2) = #[cT, cI] := by
  apply Array.toList_inj.mp
  simp [filter, toArray_toSubarray]

/-- The erasure of the major `W.s B.t T.i`. -/
def mjL : LBTerm := .app (.app (.construct iidW 1 []) (.construct iidB 1 [])) .box

/-- `visitConstructor` on `W.s B.t T.i`, neither `W` nor `B` registered: registers `W`, then `B`
(at `B.t`); `T.i` is erased to □. Reference: the `tConstruct` case of `erase`
(`MR E/ErasureFunction.v:1014`). -/
theorem visitConstructor_s_run {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)}
    (hW : st.inductives[`W]? = none) (hB : st.inductives[`B]? = none) :
    (visitConstructor (m := PureM) (n + 9) `W.s #[cT, cI]).runPure st ⟨L, [], F, {}⟩ pc ps =
      .ok ((mjL, stB (stW st)), ps) := by
  rw [visitConstructor]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok (register_W_new hW)
  dsimp only
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  simp only
  apply bind_ok rfl
  simp only [toArray_toSubarray, show Ws_ctor.numParams = 0 from rfl,
    show Ws_ctor.numFields = 2 from rfl, show Ws_ctor.cidx = 1 from rfl]
  rw [args_s]
  refine (congrArg (fun x : EraseT PureM LBTerm => x.runPure (stW st) ⟨L, [], F, {}⟩ pc ps)
    (?_ : _ = visitAppArgs (m := PureM) (n + 8) (.construct iidW 1 []) #[cT, cI])).trans ?_
  · krfl
  rw [visitAppArgs, ← Array.foldlM_toList]
  simp only [List.foldlM_cons, List.foldlM_nil]
  refine bind_ok (a := .app (.construct iidW 1 []) (.construct iidB 1 [])) (st' := stB (stW st))
    (ps' := ps) ?_ ?_
  · apply bind_ok (visitExpr_ctorB_run (n := n + 1) (.inr ⟨rfl, rfl⟩)
      (register_B_new (by simp [stW, Std.HashMap.getElem?_insert, hB])))
    rfl
  refine bind_ok (a := mjL) (st' := stB (stW st)) (ps' := ps) ?_ ?_
  · apply bind_ok (visitExpr_I_run (n := n + 6))
    rfl
  rfl

theorem withApp_mj {γ : Sort _} (k : Expr → Array Expr → γ) : mj.withApp k = k cS #[cT, cI] := by
  krfl

/-- `visitExpr` on the major `W.s B.t T.i`, neither `W` nor `B` registered. Reference: the
`tConstruct` case of `erase` (`MR E/ErasureFunction.v:1014`). -/
theorem mj_run {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)}
    (hW : st.inductives[`W]? = none) (hB : st.inductives[`B]? = none) :
    (visitExpr (m := PureM) (n + 12) mj).runPure st ⟨L, [], F, {}⟩ pc ps =
      .ok ((mjL, stB (stW st)), ps) := by
  rw [mj, visitExpr, ← mj]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ps) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 10) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_mj]
  refine bind_ok (a := none) (st' := st) (ps' := ps) (by krfl) ?_
  refine bind_ok (a := some 2) (st' := st) (ps' := ps) (by krfl) ?_
  change (withAppEtaToMinArity (m := PureM) (n + 9) _ 2 _).runPure _ _ _ _ = _
  rw [withAppEtaToMinArity]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := tW) (st' := st) (ps' := ps) (by krfl) ?_
  rw [withApp_mj, withAppEtaToMinArity.go]
  exact visitConstructor_s_run hW hB

/-! ## The alternatives -/

/-- `visitAlt` on the alternative `B.f` of `W.n`, `B` registered. Reference: the branches of the
`tCase` case of `erase` (`MR E/ErasureFunction.v:1016`). -/
theorem visitAlt_n_run {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)}
    (h : st.inductives[`B]? = some (iidB, masksB)) :
    (visitAlt (m := PureM) (n + 7) 0 #[] [] cF).runPure st ⟨L, [], F, {}⟩ pc ps =
      .ok ((([], .construct iidB 0 []), st), ps) := by
  rw [visitAlt]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := tB) (st' := st) (ps' := ps) (by krfl) ?_
  rw [lambdaOrIntroToArity]
  apply bind_ok (visitExpr_ctorB_run (.inl ⟨rfl, rfl⟩) (register_B_found h))
  krfl

/-- `visitAlt` on the alternative `fun b h => b` of `W.s`, from the counter's first variable: the
fields are bound, and the body is the variable `b`, not erasable. Reference: the branches of the
`tCase` case of `erase` (`MR E/ErasureFunction.v:1016`). -/
theorem visitAlt_s_run {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)} :
    (visitAlt (m := PureM) (n + 7) 2 #[.keep, .keep] [] altS).runPure st ⟨L, [], F, {}⟩ pc ⟨0⟩ =
      .ok (((([binderNameOf `b, binderNameOf `h], .bvar 1)), st), ⟨2⟩) := by
  krfl

/-! ## The `case` on `W` -/

/-- `visitCases`'s alternatives: `W.n ↦ B.f`, `W.s ↦ fun b h => b`. -/
def altsW : Std.HashMap Name (Nat × Expr) :=
  ((∅ : Std.HashMap Name (Nat × Expr)).insert `W.n (0, cF)).insert `W.s (2, altS)

theorem altsW_n : altsW[`W.n]? = some (0, cF) := by
  simp only [altsW, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]; rfl

theorem altsW_s : altsW[`W.s]? = some (2, altS) := by
  simp only [altsW, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]; rfl

theorem altsW_all : ([`W.n, `W.s].all fun x => altsW.contains x) = true := by
  simp only [altsW, Std.HashMap.contains_insert, Std.HashMap.contains_empty]; rfl

/-- The state after the major: `W`, then `B` registered. -/
abbrev stM (st : ErasureState) : ErasureState := stB (stW st)

theorem stM_W : (stM st).inductives[`W]? = some (iidW, masksW) := by
  simp only [stM, NV1.stB, stW, Std.HashMap.getElem?_insert]
  rfl

theorem stM_B : (stM st).inductives[`B]? = some (iidB, masksB) := NV1.stB_B

/-- The erasure of the term: the λ□ `case` on `W`. -/
def caseL : LBTerm :=
  .case (iidW, 0) mjL
    [([], .construct iidB 0 []), ([binderNameOf `b, binderNameOf `h], .bvar 1)]

/-- `visitCasesOn` on the alternatives and the erased major, `W` and `B` registered. Reference:
the `tCase` case of `erase` (`MR E/ErasureFunction.v:1016`). -/
theorem visitCasesOn_run {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)} :
    (visitCasesOn (m := PureM) (n + 9) W_ind altsW ∅ none mjL).runPure (stM st)
      ⟨L, [], F, {}⟩ pc ⟨0⟩ = .ok ((caseL, stM st), ⟨2⟩) := by
  rw [visitCasesOn]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok (register_W_found stM_W)
  simp only [show W_ind.ctors = [`W.n, `W.s] from rfl, List.forIn_cons, List.forIn_nil, bind_assoc,
    altsW_n, altsW_s, Std.HashMap.getD_empty]
  refine bind_ok (a := .yield (#[([], .construct iidB 0 [])], ([#[.keep, .keep]] : List ConstructorArgMask)))
    (st' := stM st) (ps' := ⟨0⟩) ?_ ?_
  · apply bind_ok (visitAlt_n_run stM_B)
    rfl
  refine bind_ok (a := (#[([], .construct iidB 0 []), ([binderNameOf `b, binderNameOf `h], .bvar 1)],
    ([] : List ConstructorArgMask))) (st' := stM st) (ps' := ⟨2⟩) ?_ ?_
  · refine bind_ok (a := .yield (#[([], .construct iidB 0 []),
      ([binderNameOf `b, binderNameOf `h], .bvar 1)], ([] : List ConstructorArgMask)))
      (st' := stM st) (ps' := ⟨2⟩) ?_ ?_
    · apply bind_ok visitAlt_s_run
      rfl
    · rfl
  rfl

/-- The recognizer's answer on `W.casesOn`. -/
def ciW : CasesInfo :=
  { declName := `W.casesOn, indName := `W, arity := 4, discrPos := 1, motivePos := 0,
    altsRange := 2...4, altNumParams := #[.ctor `W.n 0, .ctor `W.s 2] }

/-- The shipping recognizer recognizes `W.casesOn` over the closure. Reference: none. -/
theorem casesInfo_W : casesInfo? D `W.casesOn = some ciW := by krfl

/-- `visitCases` on the term's `casesOn`: `W.casesOn` has one universe parameter more than `W`, so
it eliminates into data, and the major's sort is never `Prop`, so the result is the λ□ `case`.
Reference: the `tCase` case of `erase` (`MR E/ErasureFunction.v:1016`). -/
theorem visitCases_run {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)}
    (hW : st.inductives[`W]? = none) (hB : st.inductives[`B]? = none) :
    (visitCases (m := PureM) (n + 13) ciW #[motB, mj, cF, altS]).runPure st
      ⟨L, [], F, {}⟩ pc ⟨0⟩ = .ok ((caseL, stM st), ⟨2⟩) := by
  rw [visitCases]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := Level.succ .zero) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  have hr : (ciW.altsRange.toList) = [2, 3] := by simp [ciW, Nat.toList_rco_eq_ite]
  simp only [← forIn'_eq_forIn, Std.Rco.forIn'_eq_forIn'_toList, hr, List.forIn'_cons,
    List.forIn'_nil]
  refine bind_ok (a := (altsW, none, ?sEnd)) (st' := st) (ps' := ⟨0⟩) ?_ ?_
  case sEnd => exact (ciW.altNumParams.toSubarray 2 2)
  · rfl
  apply bind_ok (mj_run hW hB)
  simp only [show W_ind.ctors = [`W.n, `W.s] from rfl, altsW_all, ite_true]
  apply bind_ok visitCasesOn_run
  rw [show ciW.arity = (#[motB, mj, cF, altS] : Array Expr).size from rfl, forIn_toSubarray_size]
  rfl

/-! ## The run on NV-2 -/

theorem withApp_e {γ : Sort _} (k : Expr → Array Expr → γ) :
    e.withApp k = k (.const `W.casesOn [.succ .zero]) #[motB, mj, cF, altS] := by
  krfl

/-- `visitExpr` on `e`: a saturated recognized `casesOn`. Reference: the `tCase` case of `erase`
(`MR E/ErasureFunction.v:1016`). -/
theorem e_run {n : Nat} {L : LocalContext}
    (hW : st.inductives[`W]? = none) (hB : st.inductives[`B]? = none) :
    (visitExpr (m := PureM) (n + 16) e).runPure st ⟨L, [], none, {}⟩ pc ⟨0⟩ =
      .ok ((caseL, stM st), ⟨2⟩) := by
  rw [e, visitExpr, ← e]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 14) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_e]
  refine bind_ok (a := some ciW) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  change (withAppEtaToMinArity (m := PureM) (n + 13) _ 4 _).runPure _ _ _ _ = _
  rw [withAppEtaToMinArity]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := .app motB mj) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  rw [withApp_e, withAppEtaToMinArity.go]
  exact visitCases_run hW hB

/-- The program `#erase` emits for NV-2. -/
def p0 : Program :=
  .untyped [(mutualBlockKername [`B], .inductiveDecl ⟨.finite, 0, [bodyB]⟩),
    (mutualBlockKername [`W], .inductiveDecl ⟨.finite, 0, [bodyW]⟩)] (some caseL)

/-- The pure path on NV-2's closure returns `p0` and no constant to inline. Reference: `erase`
(`MR E/ErasureFunction.v:989`) and `erase_global_deps` (`MR E/ErasureFunction.v:1602`). -/
theorem hpure : erasePure view cfg D e = .ok (p0, []) := by
  rw [erasePure, show travFuel = (travFuel - 16) + 16 by decide]
  rw [show ((visitExpr (m := PureM) (travFuel - 16 + 16) e).runPure {} { «config» := cfg }
    ⟨D, view⟩ {}) = .ok ((caseL, stM {}), ⟨2⟩) from
      e_run Std.HashMap.getElem?_empty Std.HashMap.getElem?_empty]
  rfl

/-- `#erase`'s entry point on NV-2 returns `p0` and no constant to inline. Reference: the
hypotheses `erase … = t'` and `erase_global_deps … = Σ'` of `erase_correct`
(`MR E/ErasureFunctionProperties.v:657`). -/
theorem hrun : eraseEntry view cfg e = pure (p0, []) := by
  simp only [eraseEntry, route, hcollect, hpure]

end EraseProof.Test.NV2
