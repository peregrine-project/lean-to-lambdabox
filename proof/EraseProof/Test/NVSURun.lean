import EraseProof.Test.NVSUCollect

/-!
# NV-SU through the entry point of `#erase`

The hypothesis `hrun` of the final theorem (`MR E/ErasureFunctionProperties.v:657
erase_correct`) on NV-SU (`Test/NVSUData.lean`) and on NV-SUD (`Test/NVSUDFinal.lean`): the run
of the entry point on NV-S's closure `D` (`hcollect`, `Test/NVSUCollect.lean`, and
`hcollect_default`, `Test/NVSRun.lean`) under `cfgOf nat`, for either `nat` (`hpure`). The
traversal reads `nat` only to treat `Nat`'s constructors, `casesOn`, recursor and literals apart,
and the program has none, so the steps on constructors (`cZ_run`, `cPU_run_of`, `sArg_run`) close
at both values. The run is evaluated one traversal call at a time (`Test/Run.lean`), cut at every
read of the traversal's maps, with NV-S's steps on any closure
(`lam_run`, `appArgs_cons`, `register_found`, `kername_found`). `e` erases `add` (`kername_add`):
`PureM.declInfo?` gives it with its compiled pre-definition `preVal` as value, which mentions
`add`, so `visitMutual` takes its fixpoint branch: it binds `add` to a fresh local (the fix
variable) while it erases the value, then abstracts it (`mkDef`) and declares `add` as the λ□
fixpoint `addFixL`. In the value, `add.match_1`, `@[inline]`, is marked for inlining and erased on
the way to a λ□ constant (`kername_match`): its `casesOn` is a λ□ `case`, which registers `N`, and
its first alternative erases `Unit.unit`, `@[inline]` as well, to the constructor of `PUnit`, which
registers `PUnit`; the recursive call `add n k` erases to the fix variable applied to `n` and `k`.
The program is NV-S's (`Test/NVSRun.lean`) with `add` the fixpoint and without `add._f`,
`N.brecOn`, `N.brecOn.go` and `PProd`, and the same constants to inline. The fresh locals are
numbered in the order the traversal opens them: the fix variable (0), `add`'s `n m` (1, 2),
`add.match_1`'s (3–6) and its alternative's (7), the alternatives of the pre-definition's match
(8, 9). The locals of a body are those of its binders on top of those of the body that refers to
the definition first (`visitMutual` erases a definition under the caller's locals).
-/

open Lean Erasure EraseProof.Test

namespace EraseProof.Test.NVSU

open EraseProof.Test.NVS (P e view D pc add_def add_match_1 matchVal mMotTy Unit_unit PUnit_ind
  hyg tUnit l1 u1 cPU iidPU masksPU bodyPU unitL sL stPU stDef stInl stDefI ciN withApp_sx args_s
  xf xv loc erasable_step infer_step lam_run appArgs_nil appArgs_cons register_found
  kername_found)
open EraseProof.Test.NVR (tN cZ cS N_ind Ns_ctor iidN masksN bodyN stN mj mjL)

variable {ps : PureState} {dc : Name} {nat : Config.Nat}

/-! ## The inductives `N` and `PUnit` -/

/-- `register_inductive` on `N` when it is not registered. Reference: the `InductiveDecl` of
`erase_global_deps` (`MR E/ErasureFunction.v:1602`). -/
theorem register_N_new {st : ErasureState} {L : LocalContext} {ls : List Local}
    {F : Option (Std.HashMap Name FVarId)} (h : st.inductives[`N]? = none) :
    (register_inductive (m := PureM) N_ind).runPure st ⟨L, ls, F, cfgOf nat, dc⟩ pc ps =
      .ok (((iidN, masksN), stN st), ps) := by
  rw [register_inductive]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, show N_ind.name = `N from rfl, h]
  apply bind_ok (a := [bodyN])
    (st' := { st with inductives := st.inductives.insert `N (iidN, masksN) }) (ps' := ps) rfl
  apply bind_ok rfl
  apply bind_ok rfl
  simp only [Std.HashMap.getElem?_insert_self]
  rfl

theorem register_PU_new {st : ErasureState} {L : LocalContext} {ls : List Local}
    {F : Option (Std.HashMap Name FVarId)} (h : st.inductives[`PUnit]? = none) :
    (register_inductive (m := PureM) PUnit_ind).runPure st ⟨L, ls, F, cfgOf nat, dc⟩ pc ps =
      .ok (((iidPU, masksPU), stPU st), ps) := by
  rw [register_inductive]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, show PUnit_ind.name = `PUnit from rfl, h]
  apply bind_ok (a := [bodyPU])
    (st' := { st with inductives := st.inductives.insert `PUnit (iidPU, masksPU) }) (ps' := ps) rfl
  apply bind_ok rfl
  apply bind_ok rfl
  simp only [Std.HashMap.getElem?_insert_self]
  rfl

/-! ## Constructors and locals -/

/-- `visitExpr` on `N.z`, `N` registered. Reference: the `tConstruct` case of `erase`
(`MR E/ErasureFunction.v:1014`). -/
theorem cZ_run {st : ErasureState} {n : Nat} {L : LocalContext} {ls : List Local}
    {F : Option (Std.HashMap Name FVarId)} (h : st.inductives[`N]? = some (iidN, masksN)) :
    (visitExpr (m := PureM) (n + 6) cZ).runPure st ⟨L, ls, F, cfgOf nat, dc⟩ pc ps =
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
  apply bind_ok (register_found h)
  simp only [toArray_toSubarray]
  cases nat <;> krfl

/-- `visitExpr` on `PUnit.unit.{1}`, with the registration step `hreg` on `PUnit`. Reference: the
`tConstruct` case of `erase` (`MR E/ErasureFunction.v:1014`). -/
theorem cPU_run_of {st : ErasureState} {n : Nat} {L : LocalContext} {ls : List Local}
    {F : Option (Std.HashMap Name FVarId)} {st' : ErasureState}
    (hreg : (register_inductive (m := PureM) PUnit_ind).runPure st ⟨L, ls, F, cfgOf nat, dc⟩ pc ps =
      .ok (((iidPU, masksPU), st'), ps)) :
    (visitExpr (m := PureM) (n + 6) (cPU l1)).runPure st ⟨L, ls, F, cfgOf nat, dc⟩ pc ps =
      .ok ((unitL, st'), ps) := by
  rw [cPU, visitExpr]
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
  refine bind_ok (a := EraseProof.Test.NVS.tPU l1) (st' := st) (ps' := ps) (by krfl) ?_
  rw [withApp_const, withAppEtaToMinArity.go]
  rw [visitConstructor]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok hreg
  simp only [toArray_toSubarray]
  cases nat <;> krfl

/-- `visitExpr` on a local of `ls` that the oracle keeps. Reference: the `tRel` case of `erase`
(`MR E/ErasureFunction.v:997`). -/
theorem fvar_run {st : ErasureState} {n k : Nat} {L : LocalContext} {ls : List Local}
    {F : Option (Std.HashMap Name FVarId)}
    (hE : Pure.isErasable ⟨D⟩ oracleFuel ls (xv k) = .ok false) :
    (visitExpr (m := PureM) (n + 1) (xv k)).runPure st ⟨L, ls, F, cfgOf nat, dc⟩ pc ps =
      .ok ((.fvar (xf k), st), ps) := by
  rw [xv, visitExpr]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ps)
    (erasable_step (pc := pc) (tc := ⟨L, ls, F, cfgOf nat, dc⟩) hE) ?_
  rfl

/-- `visitExpr` on `N.s a`, `a` erased to `ra` with the state unchanged, `N` registered.
Reference: the `tConstruct` case of `erase` (`MR E/ErasureFunction.v:1014`). -/
theorem sArg_run {st : ErasureState} {n : Nat} {a : Expr} {ra : LBTerm} {L : LocalContext}
    {ls : List Local} {F : Option (Std.HashMap Name FVarId)}
    (hE : Pure.isErasable ⟨D⟩ oracleFuel ls (.app cS a) = .ok false)
    (hT : Pure.inferType ⟨D⟩ oracleFuel ls [] (.app cS a) = .ok tN)
    (ha : (visitExpr (m := PureM) (n + 7) a).runPure st ⟨L, ls, F, cfgOf nat, dc⟩ pc ps =
      .ok ((ra, st), ps))
    (h : st.inductives[`N]? = some (iidN, masksN)) :
    (visitExpr (m := PureM) (n + 12) (.app cS a)).runPure st ⟨L, ls, F, cfgOf nat, dc⟩ pc ps =
      .ok ((.app sL ra, st), ps) := by
  rw [visitExpr]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ps)
    (erasable_step (pc := pc) (tc := ⟨L, ls, F, cfgOf nat, dc⟩) hE) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 10) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_sx _ _]
  refine bind_ok (a := none) (st' := st) (ps' := ps) (by krfl) ?_
  refine bind_ok (a := some 1) (st' := st) (ps' := ps) (by krfl) ?_
  change (withAppEtaToMinArity (m := PureM) (n + 9) _ 1 _).runPure _ _ _ _ = _
  rw [withAppEtaToMinArity]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := tN) (st' := st) (ps' := ps)
    (infer_step (pc := pc) (tc := ⟨L, ls, F, cfgOf nat, dc⟩) hT) ?_
  rw [withApp_sx _ _, withAppEtaToMinArity.go]
  rw [visitConstructor]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok (register_found (iv := N_ind) h)
  dsimp only
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  simp only
  apply bind_ok rfl
  simp only [toArray_toSubarray, show Ns_ctor.numParams = 0 from rfl,
    show Ns_ctor.numFields = 1 from rfl, show Ns_ctor.cidx = 1 from rfl]
  rw [args_s]
  refine (congrArg (fun x : EraseT PureM LBTerm => x.runPure st ⟨L, ls, F, cfgOf nat, dc⟩ pc ps)
    (?_ : _ = visitAppArgs (m := PureM) (n + 8) sL #[a])).trans ?_
  · cases nat <;> krfl
  exact appArgs_cons (as := []) ha appArgs_nil

/-! ## `Unit.unit` and `add.match_1` -/

/-- The state after `add.match_1` is marked for inlining. -/
abbrev st1 : ErasureState := stInl {} `add.match_1
/-- The state after its `casesOn` registers `N`. -/
abbrev st2 : ErasureState := stN st1
/-- The state after `Unit.unit`: marked for inlining, `PUnit` registered, erased. -/
abbrev stU : ErasureState := stDefI (stPU (stInl st2 `Unit.unit)) `Unit.unit unitL

/-- Facts about the traversal's maps in the states of the run. -/
macro (name := _sufact) "sufact" : tactic =>
  `(tactic| (simp only [stU, st2, st1, stDefI, stInl, stDef, stPU, stN,
    Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]; try rfl))

/-- `visitMutual` on `Unit.unit`, `PUnit` not registered: an `@[inline]` definition, marked for
inlining and erased to the λ□ constructor of `PUnit`, which registers `PUnit`. Reference:
`erase_constant_body` (`MR E/ErasureFunction.v:1309`); the marking: none. -/
theorem visitMutual_unit {n : Nat} {L : LocalContext} {o : List Local}
    {F : Option (Std.HashMap Name FVarId)} :
    (visitMutual (m := PureM) (n + 8) `Unit.unit).runPure st2 ⟨L, o, F, cfgOf nat, dc⟩ pc ps =
      .ok (((), stU), ps) := by
  rw [visitMutual]
  iterate 10 apply bind_ok rfl
  refine bind_ok (a := unitL) (st' := stPU (stInl st2 `Unit.unit)) (ps' := ps) ?_ ?_
  · rw [runPure_withReader]
    apply bind_ok rfl
    refine bind_ok (a := cPU l1) (st' := stInl st2 `Unit.unit) (ps' := ps) rfl ?_
    exact cPU_run_of (n := n + 1) (register_PU_new (by sufact))
  rfl

/-- `get_constant_kername` on `Unit.unit`, not yet erased. Reference: `erase_global_deps`
(`MR E/ErasureFunction.v:1602`). -/
theorem kername_unit {n : Nat} {L : LocalContext} {o : List Local}
    {F : Option (Std.HashMap Name FVarId)} :
    (get_constant_kername (m := PureM) (n + 9) `Unit.unit).runPure st2 ⟨L, o, F, cfgOf nat, dc⟩ pc ps =
      .ok ((toKername `Unit.unit, stU), ps) := by
  rw [get_constant_kername]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, show st2.constants[`Unit.unit]? = none by sufact]
  apply bind_ok visitMutual_unit
  apply bind_ok rfl
  simp only [stU, stDefI, stDef, Std.HashMap.getElem?_insert_self]
  rfl

/-- The locals of the pre-definition's body: `n`, `m`. -/
def lsA : List Local := [loc 2 `m tN, loc 1 `n tN]

/-- The locals of `add.match_1`'s body: `motive`, `m`, `h_1`, `h_2`. -/
def lsM : List Local :=
  loc 6 `h_2 (.forallE `k tN (.app (xv 3) (.app cS (.bvar 0))) .default) ::
    loc 5 `h_1 (.forallE `_ tUnit (.app (xv 3) cZ) .default) :: loc 4 (hyg "m" 8) tN ::
    loc 3 `motive mMotTy :: lsA

/-- The alternatives and the motive of `add.match_1`'s `casesOn`. -/
def alt1 : Expr := .app (xv 5) (.const `Unit.unit [])
def alt2 : Expr := .lam (hyg "n" 22) tN (.app (xv 6) (.bvar 0)) .default
def motM : Expr := .lam `x tN (.app (xv 3) (.bvar 0)) .default

/-- `add.match_1`'s body. -/
def mB : Expr := .app (.app (.app (.app (.const `N.casesOn [u1]) motM) (xv 4)) alt1) alt2

theorem withApp_mB {γ : Sort _} (k : Expr → Array Expr → γ) :
    mB.withApp k = k (.const `N.casesOn [u1]) #[motM, xv 4, alt1, alt2] := by krfl

theorem withApp_alt1 {γ : Sort _} (k : Expr → Array Expr → γ) :
    alt1.withApp k = k (xv 5) #[.const `Unit.unit []] := by krfl

/-- The erasure of the first alternative, `h_1 Unit.unit`. -/
def alt1L : LBTerm := .app (.fvar (xf 5)) (.const (toKername `Unit.unit))

/-- `visitExpr` on `Unit.unit` under `add.match_1`'s binders, not yet erased: the λ□ constant.
Reference: the `tConst` case of `erase` (`MR E/ErasureFunction.v:999`). -/
theorem unitC_run {n : Nat} {L : LocalContext} :
    (visitExpr (m := PureM) (n + 14) (.const `Unit.unit [])).runPure st2 ⟨L, lsM, none, cfgOf nat, dc⟩
      pc ps = .ok ((.const (toKername `Unit.unit), stU), ps) := by
  rw [visitExpr]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st2) (ps' := ps) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 12) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_const]
  refine bind_ok (a := none) (st' := st2) (ps' := ps) (by krfl) ?_
  refine bind_ok (a := none) (st' := st2) (ps' := ps) (by krfl) ?_
  refine bind_ok (a := some (.defnInfo Unit_unit)) (st' := st2) (ps' := ps) (by krfl) ?_
  refine bind_ok (a := .const (toKername `Unit.unit)) (st' := stU) (ps' := ps) ?_ ?_
  · rw [visitConst]
    apply bind_ok rfl
    refine bind_ok (kername_unit (n := n + 1)) ?_
    rfl
  exact appArgs_nil

/-- `visitAlt` on the first alternative `h_1 Unit.unit` (no field). Reference: the branches of the
`tCase` case of `erase` (`MR E/ErasureFunction.v:1016`). -/
theorem alt1_run {n : Nat} {L : LocalContext} :
    (visitAlt (m := PureM) (n + 18) 0 #[] [] alt1).runPure st2 ⟨L, lsM, none, cfgOf nat, dc⟩ pc ps =
      .ok ((([], alt1L), stU), ps) := by
  rw [visitAlt]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := .app (xv 3) cZ) (st' := st2) (ps' := ps) (by krfl) ?_
  rw [lambdaOrIntroToArity]
  refine bind_ok (a := alt1L) (st' := stU) (ps' := ps) ?_ ?_
  · show (visitExpr (m := PureM) (n + 17) alt1).runPure _ _ _ _ = _
    rw [alt1, visitExpr, ← alt1]
    apply bind_ok rfl
    apply bind_ok rfl
    refine bind_ok (a := false) (st' := st2) (ps' := ps) (by krfl) ?_
    rw [visitApp]
    change (alt1.withApp fun f args => do
      visitAppArgs (m := PureM) (n + 15) (← visitExpr (m := PureM) (n + 15) f) args).runPure _ _ _ _ = _
    rw [withApp_alt1]
    refine bind_ok (a := .fvar (xf 5)) (st' := st2) (ps' := ps) (by krfl) ?_
    refine appArgs_cons (as := []) (unitC_run (n := n)) ?_
    exact appArgs_nil
  krfl

/-- The erasure of the second alternative, `fun n => h_2 n`, under its field. -/
def alt2L : LBTerm := .app (.fvar (xf 6)) (.bvar 0)

/-- `visitAlt` on the second alternative `fun n => h_2 n` (one field), from the counter's eighth
variable. Reference: the branches of the `tCase` case of `erase` (`MR E/ErasureFunction.v:1016`). -/
theorem alt2_run {st : ErasureState} {n : Nat} {L : LocalContext} :
    (visitAlt (m := PureM) (n + 10) 1 #[.keep] [] alt2).runPure st ⟨L, lsM, none, cfgOf nat, dc⟩ pc ⟨7⟩ =
      .ok ((([binderNameOf (hyg "n" 22)], alt2L), st), ⟨8⟩) := by
  krfl

/-- `visitCases`'s alternatives of `add.match_1`'s `casesOn`. -/
def altsM : Std.HashMap Name (Nat × Expr) :=
  ((∅ : Std.HashMap Name (Nat × Expr)).insert `N.z (0, alt1)).insert `N.s (1, alt2)

theorem altsM_z : altsM[`N.z]? = some (0, alt1) := by
  simp only [altsM, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]; rfl

theorem altsM_s : altsM[`N.s]? = some (1, alt2) := by
  simp only [altsM, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]; rfl

theorem altsM_all : ([`N.z, `N.s].all fun x => altsM.contains x) = true := by
  simp only [altsM, Std.HashMap.contains_insert, Std.HashMap.contains_empty]; rfl

/-- The erasure of `add.match_1`'s body: the λ□ `case` on `m`. -/
def caseM : LBTerm :=
  .case (iidN, 0) (.fvar (xf 4)) [([], alt1L), ([binderNameOf (hyg "n" 22)], alt2L)]

/-- `visitCasesOn` on `add.match_1`'s alternatives and the discriminant `m`: it registers `N`.
Reference: the `tCase` case of `erase` (`MR E/ErasureFunction.v:1016`). -/
theorem visitCasesOn_run {n : Nat} {L : LocalContext} :
    (visitCasesOn (m := PureM) (n + 19) N_ind altsM ∅ none (.fvar (xf 4))).runPure st1
      ⟨L, lsM, none, cfgOf nat, dc⟩ pc ⟨7⟩ = .ok ((caseM, stU), ⟨8⟩) := by
  rw [visitCasesOn]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok (register_N_new (by sufact))
  simp only [show N_ind.ctors = [`N.z, `N.s] from rfl, List.forIn_cons, List.forIn_nil, bind_assoc,
    altsM_z, altsM_s, Std.HashMap.getD_empty]
  refine bind_ok (a := .yield (#[([], alt1L)], ([#[.keep]] : List ConstructorArgMask)))
    (st' := stU) (ps' := ⟨7⟩) ?_ ?_
  · apply bind_ok (alt1_run (n := n))
    rfl
  refine bind_ok (a := (#[([], alt1L), ([binderNameOf (hyg "n" 22)], alt2L)],
    ([] : List ConstructorArgMask))) (st' := stU) (ps' := ⟨8⟩) ?_ ?_
  · refine bind_ok (a := .yield (#[([], alt1L), ([binderNameOf (hyg "n" 22)], alt2L)],
      ([] : List ConstructorArgMask))) (st' := stU) (ps' := ⟨8⟩) ?_ ?_
    · apply bind_ok (alt2_run (n := n + 8))
      rfl
    · rfl
  rfl

/-- `visitCases` on `add.match_1`'s `casesOn`: the λ□ `case`. Reference: the `tCase` case of
`erase` (`MR E/ErasureFunction.v:1016`). -/
theorem visitCases_run {n : Nat} {L : LocalContext} :
    (visitCases (m := PureM) (n + 22) ciN #[motM, xv 4, alt1, alt2]).runPure st1
      ⟨L, lsM, none, cfgOf nat, dc⟩ pc ⟨7⟩ = .ok ((caseM, stU), ⟨8⟩) := by
  rw [visitCases]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := Level.succ .zero) (st' := st1) (ps' := ⟨7⟩) (by krfl) ?_
  have hr : (ciN.altsRange.toList) = [2, 3] := by simp [ciN, Nat.toList_rco_eq_ite]
  simp only [← forIn'_eq_forIn, Std.Rco.forIn'_eq_forIn'_toList, hr, List.forIn'_cons,
    List.forIn'_nil]
  refine bind_ok (a := (altsM, none, ?sEnd)) (st' := st1) (ps' := ⟨7⟩) ?_ ?_
  case sEnd => exact (ciN.altNumParams.toSubarray 2 2)
  · rfl
  refine bind_ok (a := .fvar (xf 4)) (st' := st1) (ps' := ⟨7⟩) (by krfl) ?_
  simp only [show N_ind.ctors = [`N.z, `N.s] from rfl, altsM_all, ite_true]
  apply bind_ok (visitCasesOn_run (n := n + 2))
  rw [show ciN.arity = (#[motM, xv 4, alt1, alt2] : Array Expr).size from rfl,
    forIn_toSubarray_size]
  rfl

/-- `visitExpr` on `add.match_1`'s body: a saturated recognized `casesOn`. Reference: the `tCase`
case of `erase` (`MR E/ErasureFunction.v:1016`). -/
theorem mB_run {n : Nat} {L : LocalContext} :
    (visitExpr (m := PureM) (n + 26) mB).runPure st1 ⟨L, lsM, none, cfgOf nat, dc⟩ pc ⟨7⟩ =
      .ok ((caseM, stU), ⟨8⟩) := by
  rw [mB, visitExpr, ← mB]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st1) (ps' := ⟨7⟩) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 24) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_mB]
  refine bind_ok (a := some ciN) (st' := st1) (ps' := ⟨7⟩) (by krfl) ?_
  change (withAppEtaToMinArity (m := PureM) (n + 23) _ 4 _).runPure _ _ _ _ = _
  rw [withAppEtaToMinArity]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := .app motM (xv 4)) (st' := st1) (ps' := ⟨7⟩)
    (infer_step (pc := pc) (tc := ⟨L, lsM, none, cfgOf nat, dc⟩) (by krfl)) ?_
  rw [withApp_mB, withAppEtaToMinArity.go]
  simp only [show (#[motM, xv 4, alt1, alt2] : Array Expr).size = 4 from rfl, ge_iff_le,
    Nat.le_refl, ↓reduceIte]
  exact visitCases_run (n := n + 1)

/-- The erasure of `add.match_1`'s value. -/
def matchVLU : LBTerm :=
  .lambda (binderNameOf `motive) (_root_.abstract (xf 3) (.lambda (binderNameOf (hyg "m" 8))
    (_root_.abstract (xf 4) (.lambda (binderNameOf `h_1) (_root_.abstract (xf 5)
      (.lambda (binderNameOf `h_2) (_root_.abstract (xf 6) caseM)))))))

/-- `visitExpr` on `add.match_1`'s value, from the counter's fourth variable. Reference: the
`tLambda` case of `erase` (`MR E/ErasureFunction.v:1003`). -/
theorem matchV_run {n : Nat} {L : LocalContext} :
    (visitExpr (m := PureM) (n + 34) matchVal).runPure st1 ⟨L, lsA, none, cfgOf nat, dc⟩ pc ⟨3⟩ =
      .ok ((matchVLU, stU), ⟨8⟩) :=
  lam_run (by krfl) fun _ => lam_run (by krfl) fun _ => lam_run (by krfl) fun _ =>
    lam_run (by krfl) fun _ => mB_run (n := n)

/-- The state after `add.match_1`. -/
abbrev stMt : ErasureState := stDefI stU `add.match_1 matchVLU

/-- `visitMutual` on `add.match_1` from the empty state: an `@[inline]` definition, marked for
inlining and erased to a λ□ constant. Reference: as `visitMutual_unit`. -/
theorem visitMutual_match {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)} :
    (visitMutual (m := PureM) (n + 35) `add.match_1).runPure {} ⟨L, lsA, F, cfgOf nat, dc⟩ pc ⟨3⟩ =
      .ok (((), stMt), ⟨8⟩) := by
  rw [visitMutual]
  iterate 10 apply bind_ok rfl
  refine bind_ok (a := matchVLU) (st' := stU) (ps' := ⟨8⟩) ?_ ?_
  · rw [runPure_withReader]
    apply bind_ok rfl
    refine bind_ok (a := matchVal) (st' := st1) (ps' := ⟨3⟩) rfl ?_
    exact matchV_run (n := n)
  rfl

/-- `get_constant_kername` on `add.match_1` from the empty state. Reference: `erase_global_deps`
(`MR E/ErasureFunction.v:1602`). -/
theorem kername_match {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)} :
    (get_constant_kername (m := PureM) (n + 36) `add.match_1).runPure {} ⟨L, lsA, F, cfgOf nat, dc⟩
      pc ⟨3⟩ = .ok ((toKername `add.match_1, stMt), ⟨8⟩) := by
  rw [get_constant_kername]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty]
  apply bind_ok visitMutual_match
  apply bind_ok rfl
  simp only [stMt, stDefI, stDef, Std.HashMap.getElem?_insert_self]
  rfl

/-! ## `add`: the fixpoint -/

/-- The fix variables of `add`'s block: `add` bound to the local 0. -/
def fixM : Std.HashMap Name FVarId := Std.HashMap.ofList [(`add, xf 0)]

theorem fixM_add : fixM[`add]? = some (xf 0) := by
  simp only [fixM, Std.HashMap.ofList_singleton, Std.HashMap.getElem?_insert_self]

theorem fixM_add' : fixM[`add]! = xf 0 := by
  simp only [fixM, Std.HashMap.ofList_singleton, Std.HashMap.getElem!_insert_self]

theorem fixM_match : fixM[`add.match_1]? = none := by
  simp only [fixM, Std.HashMap.ofList_singleton, Std.HashMap.getElem?_insert,
    Std.HashMap.getElem?_empty]
  rfl

/-- The locals of the second alternative's body: `k`. -/
def lsB : List Local := loc 9 `k tN :: lsA

/-- The recursive call `add n k` in the second alternative. -/
def callB : Expr := .app (.app (.const `add []) (xv 1)) (xv 9)

theorem withApp_callB {γ : Sort _} (k : Expr → Array Expr → γ) :
    callB.withApp k = k (.const `add []) #[xv 1, xv 9] := by krfl

/-- The erasure of the recursive call: the fix variable applied to `n` and `k`. -/
def callBL : LBTerm := .app (.app (.fvar (xf 0)) (.fvar (xf 1))) (.fvar (xf 9))

/-- `visitExpr` on the recursive call `add n k` in the fixpoint body: `visitConst` finds `add`
among the fix variables. Reference: the `tRel` case of `erase` for the fixpoint's variable
(`MR E/ErasureFunction.v:997`); DV-7. -/
theorem callB_run {st : ErasureState} {n : Nat} {L : LocalContext} :
    (visitExpr (m := PureM) (n + 5) callB).runPure st ⟨L, lsB, some fixM, cfgOf nat, dc⟩ pc ps =
      .ok ((callBL, st), ps) := by
  rw [callB, visitExpr, ← callB]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ps) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 3) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_callB]
  refine bind_ok (a := none) (st' := st) (ps' := ps) (by krfl) ?_
  refine bind_ok (a := none) (st' := st) (ps' := ps) (by krfl) ?_
  refine bind_ok (a := some (.defnInfo add_def)) (st' := st) (ps' := ps) (by krfl) ?_
  refine bind_ok (a := .fvar (xf 0)) (st' := st) (ps' := ps) ?_ ?_
  · rw [visitConst]
    apply bind_ok rfl
    simp only [Option.bind_some, fixM_add]
    rfl
  refine appArgs_cons (as := [xv 9]) (fvar_run (n := n) (by krfl)) ?_
  refine appArgs_cons (as := []) (fvar_run (n := n) (by krfl)) ?_
  exact appArgs_nil

/-- The alternatives of the pre-definition's match under its locals `n m`: `fun _ => n` and
`fun k => N.s (add n k)`. -/
def altQ1 : Expr := .lam `_ tUnit (xv 1) .default
def altQ2 : Expr := .lam `k tN (.app cS (.app (.app (.const `add []) (xv 1)) (.bvar 0))) .default

/-- The pre-definition's body `add.match_1 (fun m => N) m (fun _ => n) (fun k => N.s (add n k))`
under its locals. -/
def preB : Expr :=
  .app (.app (.app (.app (.const `add.match_1 [l1]) motPre) (xv 2)) altQ1) altQ2

theorem withApp_preB {γ : Sort _} (k : Expr → Array Expr → γ) :
    preB.withApp k = k (.const `add.match_1 [l1]) #[motPre, xv 2, altQ1, altQ2] := by krfl

/-- The erasures of the alternatives of the pre-definition's match. -/
def altP1L : LBTerm := .lambda (binderNameOf `_) (_root_.abstract (xf 8) (.fvar (xf 1)))
def altP2L : LBTerm := .lambda (binderNameOf `k) (_root_.abstract (xf 9) (.app sL callBL))

/-- The erasure of the pre-definition's body. -/
def preBL : LBTerm :=
  .app (.app (.app (.app (.const (toKername `add.match_1)) .box) (.fvar (xf 2))) altP1L) altP2L

/-- `visitExpr` on the pre-definition's body from the empty state, in the fixpoint branch: the λ□
constant of `add.match_1`, erased on the way, applied to □ and the erased arguments, the recursive
call under the second alternative erased to the fix variable. Reference: the `tConst` and `tApp`
cases of `erase` (`MR E/ErasureFunction.v:999`, `:1006`). -/
theorem preB_run {n : Nat} {L : LocalContext} :
    (visitExpr (m := PureM) (n + 42) preB).runPure {} ⟨L, lsA, some fixM, cfgOf nat, dc⟩ pc ⟨3⟩ =
      .ok ((preBL, stMt), ⟨10⟩) := by
  have hN : stMt.inductives[`N]? = some (iidN, masksN) := by sufact
  rw [preB, visitExpr, ← preB]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := {}) (ps' := ⟨3⟩) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 40) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_preB]
  refine bind_ok (a := none) (st' := {}) (ps' := ⟨3⟩) (by krfl) ?_
  refine bind_ok (a := none) (st' := {}) (ps' := ⟨3⟩) (by krfl) ?_
  refine bind_ok (a := some (.defnInfo add_match_1)) (st' := {}) (ps' := ⟨3⟩) (by krfl) ?_
  refine bind_ok (a := .const (toKername `add.match_1)) (st' := stMt) (ps' := ⟨8⟩) ?_ ?_
  · rw [visitConst]
    apply bind_ok rfl
    simp only [Option.bind_some, fixM_match]
    refine bind_ok (kername_match (n := n + 2)) ?_
    rfl
  refine appArgs_cons (as := [xv 2, altQ1, altQ2]) (r := .box) (st' := stMt) (ps' := ⟨8⟩)
    (by krfl) ?_
  refine appArgs_cons (as := [altQ1, altQ2]) (r := .fvar (xf 2)) (st' := stMt) (ps' := ⟨8⟩)
    (by krfl) ?_
  refine appArgs_cons (as := [altQ2]) (r := altP1L) (st' := stMt) (ps' := ⟨9⟩)
    (lam_run (by krfl) fun _ => by krfl) ?_
  refine appArgs_cons (as := []) (r := altP2L) (st' := stMt) (ps' := ⟨10⟩)
    (lam_run (by krfl) fun _ =>
      sArg_run (n := n + 24) (by krfl) (by krfl) (callB_run (n := n + 26)) hN) ?_
  exact appArgs_nil

/-- The erasure of the pre-definition, with the fix variable free. -/
def preVL : LBTerm :=
  .lambda (binderNameOf `n) (_root_.abstract (xf 1) (.lambda (binderNameOf `m)
    (_root_.abstract (xf 2) preBL)))

/-- `visitExpr` on the pre-definition from the empty state, from the counter's second variable.
Reference: the `tLambda` case of `erase` (`MR E/ErasureFunction.v:1003`). -/
theorem preV_run {n : Nat} {L : LocalContext} :
    (visitExpr (m := PureM) (n + 46) preVal).runPure {} ⟨L, [], some fixM, cfgOf nat, dc⟩ pc ⟨1⟩ =
      .ok ((preVL, stMt), ⟨10⟩) :=
  lam_run (by krfl) fun _ => lam_run (by krfl) fun _ => preB_run (n := n)

/-- `add`'s declaration as `PureM.declInfo?` gives it under `cfgOf nat`: `add_def` with the value
`preVal` (`preDef_add`). -/
def addU : DefinitionVal := { add_def with value := preVal }

/-- `add`'s λ□ fixpoint: one definition named after `add`, whose body abstracts the fix variable
from the pre-definition's erasure, recursive-argument index 0 (`mkDef`). -/
def addDefL : @FixDef LBTerm := { name := fixDefName `add, body := toBvar (xf 0) 0 preVL }
def addFixL : LBTerm := .fix [addDefL] 0

/-- `addFixL` in closed form: `tFix [⟨add, λ n m. add.match_1 □ m (λ _. n)
(λ k. N.s (add n k)), 0⟩] 0`, the recursive call the fixpoint's variable `tRel 3`. -/
theorem addFixL_eq : addFixL = .fix [⟨fixDefName `add, .lambda (binderNameOf `n)
    (.lambda (binderNameOf `m) (.app (.app (.app (.app
      (.const (toKername `add.match_1)) .box) (.bvar 0))
      (.lambda (binderNameOf `_) (.bvar 2)))
      (.lambda (binderNameOf `k)
        (.app sL (.app (.app (.bvar 3) (.bvar 2)) (.bvar 0)))))), 0⟩] 0 := by
  krfl

/-- `mkDef` on `add`'s erased pre-definition: the fix variable abstracted at index 0. Reference:
the bodies of `tFix` in `erase` (`MR E/ErasureFunction.v:1022`); DV-7. -/
theorem mkDef_run {st : ErasureState} {L : LocalContext} {ls : List Local} :
    (mkDef (m := PureM) `add [`add] preVL).runPure st ⟨L, ls, some fixM, cfgOf nat, dc⟩ pc ps =
      .ok ((addDefL, st), ps) := by
  rw [mkDef]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.zipIdx_cons,
    List.zipIdx_nil, List.forIn_cons, List.forIn_nil]
  refine bind_ok (a := toBvar (xf 0) 0 preVL) (st' := st) (ps' := ps) ?_ rfl
  refine bind_ok (a := .yield (toBvar (xf 0) 0 preVL)) (st' := st) (ps' := ps) ?_ rfl
  apply bind_ok rfl
  dsimp only
  rw [Option.get!_some, fixM_add']
  rfl

/-- The state after `add`. -/
abbrev stAdd : ErasureState := stDef stMt `add addFixL

/-- `visitMutual` on `add` from the empty state: `PureM.declInfo?` gives `add` with its compiled
pre-definition as value, which mentions `add`, so the fixpoint branch: one fresh fix variable, the
value erased under it, `mkDef`, and `add` declared as the fixpoint. Reference: the `tFix` case of
`erase` (`MR E/ErasureFunction.v:1022`) and `erase_constant_body` (`MR E/ErasureFunction.v:1309`);
DV-7. -/
theorem visitMutual_add {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)} :
    (visitMutual (m := PureM) (n + 48) `add).runPure {} ⟨L, [], F, cfgOf nat, dc⟩ pc ⟨0⟩ =
      .ok (((), stAdd), ⟨10⟩) := by
  rw [visitMutual]
  apply bind_ok rfl
  refine bind_ok (a := some (.defnInfo addU)) (st' := {}) (ps' := ⟨0⟩) (by krfl) ?_
  iterate 6 apply bind_ok rfl
  rw [runPure_withReader]
  refine bind_ok (a := [addDefL]) (st' := stMt) (ps' := ⟨10⟩) ?_ ?_
  · rw [show (ConstantInfo.defnInfo addU).all = [`add] from rfl, List.mapM_cons, List.mapM_nil]
    simp only [show ((`add : Name) == (ConstantInfo.defnInfo addU).name) = true by krfl,
      ↓reduceIte]
    refine bind_ok (a := addDefL) (st' := stMt) (ps' := ⟨10⟩) ?_ rfl
    apply bind_ok rfl
    refine bind_ok (a := preVL) (st' := stMt) (ps' := ⟨10⟩) ?_ mkDef_run
    rw [runPure_withReader]
    apply bind_ok rfl
    refine bind_ok (a := preVal) (st' := {}) (ps' := ⟨1⟩) rfl ?_
    exact preV_run (n := n + 1)
  rfl

/-- `get_constant_kername` on `add` from the empty state. Reference: `erase_global_deps`
(`MR E/ErasureFunction.v:1602`). -/
theorem kername_add {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)} :
    (get_constant_kername (m := PureM) (n + 49) `add).runPure {} ⟨L, [], F, cfgOf nat, dc⟩ pc ⟨0⟩ =
      .ok ((toKername `add, stAdd), ⟨10⟩) := by
  rw [get_constant_kername]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty]
  apply bind_ok visitMutual_add
  apply bind_ok rfl
  simp only [stAdd, stDef, Std.HashMap.getElem?_insert_self]
  rfl

/-! ## The term -/

theorem withApp_e {γ : Sort _} (k : Expr → Array Expr → γ) :
    e.withApp k = k (.const `add []) #[mj, mj] := by krfl

/-- The erasure of the major `N.s N.z`, `N` registered. -/
theorem mj_run {st : ErasureState} {n : Nat} {L : LocalContext}
    (h : st.inductives[`N]? = some (iidN, masksN)) :
    (visitExpr (m := PureM) (n + 12) mj).runPure st ⟨L, [], none, cfgOf nat, .anonymous⟩ pc ps =
      .ok ((mjL, st), ps) :=
  sArg_run (by krfl) (by krfl) (cZ_run (n := n + 1) h) h

/-- `visitExpr` on `e = add (N.s N.z) (N.s N.z)`: the λ□ constant of `add`, erased on the way as a
fixpoint with its dependencies, applied to the erased arguments. Reference: the `tConst` and `tApp`
cases of `erase` (`MR E/ErasureFunction.v:999`, `:1006`), with `erase_global_deps`
(`MR E/ErasureFunction.v:1602`). -/
theorem e_run {n : Nat} {L : LocalContext} :
    (visitExpr (m := PureM) (n + 68) e).runPure {} ⟨L, [], none, cfgOf nat, .anonymous⟩ pc ⟨0⟩ =
      .ok ((EraseProof.Test.NVS.eL, stAdd), ⟨10⟩) := by
  have hN : stAdd.inductives[`N]? = some (iidN, masksN) := by sufact
  rw [e, visitExpr, ← e]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := {}) (ps' := ⟨0⟩) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 66) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_e]
  refine bind_ok (a := none) (st' := {}) (ps' := ⟨0⟩) (by krfl) ?_
  refine bind_ok (a := none) (st' := {}) (ps' := ⟨0⟩) (by krfl) ?_
  refine bind_ok (a := some (.defnInfo add_def)) (st' := {}) (ps' := ⟨0⟩) (by krfl) ?_
  refine bind_ok (a := .const (toKername `add)) (st' := stAdd) (ps' := ⟨10⟩) ?_ ?_
  · rw [visitConst]
    apply bind_ok rfl
    refine bind_ok (kername_add (n := n + 15)) ?_
    rfl
  refine appArgs_cons (as := [mj]) (mj_run (n := n + 52) hN) ?_
  refine appArgs_cons (as := []) (mj_run (n := n + 52) hN) ?_
  exact appArgs_nil

/-! ## The run on NV-SU -/

/-- The program `#erase` emits for NV-SU: `add` as the fixpoint `addFixL`, NV-S's declarations of
`add.match_1`, `Unit.unit`, `PUnit` and `N`, and NV-S's term. -/
def pSU : Program :=
  .untyped [(toKername `add, .constantDecl ⟨some addFixL⟩),
    (toKername `add.match_1, .constantDecl ⟨some EraseProof.Test.NVS.matchVL⟩),
    (toKername `Unit.unit, .constantDecl ⟨some unitL⟩),
    (mutualBlockKername [`PUnit], .inductiveDecl ⟨.finite, 0, [bodyPU]⟩),
    (mutualBlockKername [`N], .inductiveDecl ⟨.finite, 0, [bodyN]⟩)] (some EraseProof.Test.NVS.eL)

/-- The pure path on NV-S's closure under `cfgOf nat` returns `pSU` and NV-S's constants to inline,
`Unit.unit` and `add.match_1`. Reference: `erase` (`MR E/ErasureFunction.v:989`) and
`erase_global_deps` (`MR E/ErasureFunction.v:1602`). -/
theorem hpure : erasePure view (cfgOf nat) D e = .ok (pSU, EraseProof.Test.NVS.inl0) := by
  rw [erasePure, show travFuel = (travFuel - 68) + 68 by decide]
  rw [show ((visitExpr (m := PureM) (travFuel - 68 + 68) e).runPure {} { «config» := cfgOf nat }
    ⟨D, view⟩ {}) = .ok ((EraseProof.Test.NVS.eL, stAdd), ⟨10⟩) from e_run]
  krfl

/-- `#erase`'s entry point on NV-SU returns `pSU` and NV-S's constants to inline. Reference: the
hypotheses `erase … = t'` and `erase_global_deps … = Σ'` of `erase_correct`
(`MR E/ErasureFunctionProperties.v:657`). -/
theorem hrun : eraseEntry view cfgSU e = pure (pSU, EraseProof.Test.NVS.inl0) := by
  simp only [eraseEntry, route, hcollect, show erasePure view cfgSU D e = _ from hpure]

end EraseProof.Test.NVSU
