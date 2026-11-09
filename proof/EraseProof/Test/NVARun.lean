import EraseProof.Test.NVAData
import EraseProof.Test.NVSRun
import EraseProof.Test.NVLRun

/-!
# NV-A through the entry point of `#erase`

The hypotheses `hfrag` and `hrun` of the final theorem (`MR E/ErasureFunctionProperties.v:657
erase_correct`) on NV-A (`Test/NVAData.lean`). `hcollect` computes the fragment test's closure `D`
by kernel evaluation (and `hcollect_default` shows that under the default configuration it rejects
`e`: `Nat.add` has a compiled companion in the view). `hrun` is the run of the entry point,
evaluated one traversal call at a time (`Test/Run.lean`), cut at every read of the traversal's
maps, with NV-S's steps on any closure (`lam_run`, `appArgs_cons`, `register_found`,
`kername_found`). `e` erases `Nat.add` (`kername_add`: its `@[extern]` attribute is read and, under
`extern := .preferLogical`, its kernel definition erased), whose body erases `Nat.brecOn` with
`Nat.brecOn.go` (`kername_brecOn`: the projection of `Nat.brecOn`'s value registers `PProd`,
`visitRec` on the `Nat.rec` of `Nat.brecOn.go` registers `Nat`, the minor premise of `Nat.zero`
registers `PUnit`) and `Nat.add._f` with `Nat.add.match_1` (`kername_f`: the `casesOn` of
`Nat.add.match_1` is a λ□ `case`, the projection `x.1` of the table `Nat.below` is a λ□ projection
of `PProd`); `Nat.below` occurs only in types and is not erased. The numerals erase
`OfNat.ofNat` (`kername_ofNat`: its projection registers `OfNat`) and `instOfNatNat`
(`kername_inst`), and their literals the constructor chains of `Nat` (`nat := .peano`). The fresh
locals are numbered in the order the traversal opens them: `Nat.add`'s `x y` (0, 1),
`Nat.brecOn`'s (2–4), `Nat.brecOn.go`'s (5–7) and its minor premise's (8, 9), `Nat.add._f`'s
(10–12), `Nat.add.match_1`'s (13–17) and its alternative's (18), the alternatives of
`Nat.add._f` (19–23), `OfNat.ofNat`'s (24–26) and `instOfNatNat`'s (27). The locals of a body
are those of its binders on top of those of the body that refers to the definition first
(`visitMutual` erases a definition under the caller's locals).
-/

open Lean Erasure EraseProof.Test

namespace EraseProof.Test.NVA

open EraseProof.Test.NVL (tN cZ cS Nat_ind Zero_ctor Succ_ctor Nat_rec motTy iidN masksN bodyN
  stN natL memberN fixL recShape_N)
open EraseProof.Test.NVS (uu u1 l1 m1u tPU cPU tPP cPP PUnit_ind PUnit_unit PUnit_rec PProd_ind
  PProd_mk PProd_rec iidPP iidPU masksPP masksPU bodyPP bodyPU projPP mkL unitL xf xv loc
  erasable_step infer_step lam_run appArgs_nil appArgs_cons register_found kername_found stPP stPU
  stDef args_PP)

/-- The closure of `e`, in the order the fragment test returns it. -/
def D : List ConstantInfo :=
  [.defnInfo inst_def, .ctorInfo OfNat_mk, .recInfo OfNat_rec, .inductInfo OfNat_ind,
    .defnInfo ofNat_def, .defnInfo Nat_casesOn, .defnInfo match_def, .defnInfo add_f,
    .defnInfo Nat_brecOn_go, .ctorInfo PProd_mk, .recInfo PProd_rec, .inductInfo PProd_ind,
    .ctorInfo PUnit_unit, .recInfo PUnit_rec, .inductInfo PUnit_ind, .recInfo Nat_rec,
    .defnInfo Nat_below, .defnInfo Nat_brecOn, .ctorInfo Succ_ctor, .ctorInfo Zero_ctor,
    .inductInfo Nat_ind, .defnInfo add_def]

/-- The fragment test accepts `e` and returns the closure `D`, by kernel evaluation. Reference: the
environment `Σ'` of `erase_global_deps` (`MR E/ErasureFunction.v:1602`). -/
theorem hcollect : collectDeps view cfg e = .ok D := rfl

/-- Under the default structural configuration (`structural := .unsafeRec`) the fragment test
rejects `e` as outside the fragment (`#erase` reports "recursive definition Nat.add"): the view
has `Nat.add`'s compiled companion `Nat.add._unsafe_rec`. -/
theorem hcollect_default :
    (match collectDeps view { cfg with structural := .unsafeRec } e with
      | .error (.outOfFragment _) => true | _ => false) = true := by
  krfl

/-- The pure backend's context over the closure. -/
def pc : PureCtx := ⟨D, view⟩

variable {st : ErasureState} {ps : PureState} {dc : Name}

/-! ## The inductives `PProd`, `Nat`, `PUnit` and `OfNat` -/

/-- The λ□ inductive of `OfNat`, the argument mask of `OfNat.mk` (its field kept) and the λ□ body of
`OfNat` (a structure: one projection). -/
def iidOf : InductiveId := ⟨mutualBlockKername [`OfNat], 0⟩
def masksOf : InductiveArgMasks := [#[.keep]]
def bodyOf : OneInductiveBody :=
  { name := toString `OfNat, propositional := false, ctors := [⟨toString `OfNat.mk, 1⟩],
    projs := [⟨"0"⟩] }

/-- The state after registering `OfNat`. -/
def stOf (st : ErasureState) : ErasureState :=
  { st with
    inductives := st.inductives.insert `OfNat (iidOf, masksOf)
    gdecls := (mutualBlockKername [`OfNat], .inductiveDecl ⟨.finite, 2, [bodyOf]⟩) :: st.gdecls }

/-- `register_inductive` on `PProd` when it is not registered. Reference: the `InductiveDecl` of
`erase_global_deps` (`MR E/ErasureFunction.v:1602`). -/
theorem register_PP_new {L : LocalContext} {ls : List Local} {F : Option (Std.HashMap Name FVarId)}
    (h : st.inductives[`PProd]? = none) :
    (register_inductive (m := PureM) PProd_ind).runPure st ⟨L, ls, F, cfg, dc⟩ pc ps =
      .ok (((iidPP, masksPP), stPP st), ps) := by
  rw [register_inductive]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, show PProd_ind.name = `PProd from rfl, h]
  apply bind_ok (a := [bodyPP])
    (st' := { st with inductives := st.inductives.insert `PProd (iidPP, masksPP) }) (ps' := ps) rfl
  apply bind_ok rfl
  apply bind_ok rfl
  simp only [Std.HashMap.getElem?_insert_self]
  rfl

theorem register_PU_new {L : LocalContext} {ls : List Local} {F : Option (Std.HashMap Name FVarId)}
    (h : st.inductives[`PUnit]? = none) :
    (register_inductive (m := PureM) PUnit_ind).runPure st ⟨L, ls, F, cfg, dc⟩ pc ps =
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

theorem register_Nat_new {L : LocalContext} {ls : List Local} {F : Option (Std.HashMap Name FVarId)}
    (h : st.inductives[`Nat]? = none) :
    (register_inductive (m := PureM) Nat_ind).runPure st ⟨L, ls, F, cfg, dc⟩ pc ps =
      .ok (((iidN, masksN), stN st), ps) := by
  rw [register_inductive]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, show Nat_ind.name = `Nat from rfl, h]
  apply bind_ok (a := [bodyN])
    (st' := { st with inductives := st.inductives.insert `Nat (iidN, masksN) }) (ps' := ps) rfl
  apply bind_ok rfl
  apply bind_ok rfl
  simp only [Std.HashMap.getElem?_insert_self]
  rfl

theorem register_Of_new {L : LocalContext} {ls : List Local} {F : Option (Std.HashMap Name FVarId)}
    (h : st.inductives[`OfNat]? = none) :
    (register_inductive (m := PureM) OfNat_ind).runPure st ⟨L, ls, F, cfg, dc⟩ pc ps =
      .ok (((iidOf, masksOf), stOf st), ps) := by
  rw [register_inductive]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, show OfNat_ind.name = `OfNat from rfl, h]
  apply bind_ok (a := [bodyOf])
    (st' := { st with inductives := st.inductives.insert `OfNat (iidOf, masksOf) }) (ps' := ps) rfl
  apply bind_ok rfl
  apply bind_ok rfl
  simp only [Std.HashMap.getElem?_insert_self]
  rfl

theorem stPU_PU : (stPU st).inductives[`PUnit]? = some (iidPU, masksPU) := by
  simp only [stPU, Std.HashMap.getElem?_insert_self]

theorem stN_N : (stN st).inductives[`Nat]? = some (iidN, masksN) := by
  simp only [stN, Std.HashMap.getElem?_insert_self]

/-! ## Constructors -/

/-- `visitExpr` on `Nat.zero`, `Nat` registered. Reference: the `tConstruct` case of `erase`
(`MR E/ErasureFunction.v:1014`). -/
theorem cZ_run {n : Nat} {L : LocalContext} {ls : List Local} {F : Option (Std.HashMap Name FVarId)}
    (h : st.inductives[`Nat]? = some (iidN, masksN)) :
    (visitExpr (m := PureM) (n + 6) cZ).runPure st ⟨L, ls, F, cfg, dc⟩ pc ps =
      .ok ((natL 0, st), ps) := by
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
  krfl

/-- `visitExpr` on `PUnit.unit.{max 1 u}`, with the registration step `hreg` on `PUnit`.
Reference: the `tConstruct` case of `erase` (`MR E/ErasureFunction.v:1014`). -/
theorem cPU_run_of {n : Nat} {L : LocalContext} {ls : List Local}
    {F : Option (Std.HashMap Name FVarId)} {st' : ErasureState}
    (hreg : (register_inductive (m := PureM) PUnit_ind).runPure st ⟨L, ls, F, cfg, dc⟩ pc ps =
      .ok (((iidPU, masksPU), st'), ps)) :
    (visitExpr (m := PureM) (n + 6) (cPU m1u)).runPure st ⟨L, ls, F, cfg, dc⟩ pc ps =
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
  refine bind_ok (a := tPU m1u) (st' := st) (ps' := ps) (by krfl) ?_
  rw [withApp_const, withAppEtaToMinArity.go]
  rw [visitConstructor]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok hreg
  simp only [toArray_toSubarray]
  krfl

/-! ## `Nat.brecOn.go` -/

/-- The type of `F_1` under the motive `x_k`. -/
def F1T (k : Nat) : Expr :=
  .forallE `t tN (.forallE `f (.app (.app (below uu) (xv k)) (.bvar 0)) (.app (xv k) (.bvar 1))
    .default) .default

/-- The locals of `Nat.brecOn.go`'s body: `motive`, `t`, `F_1`. -/
def lsGo (o : List Local) : List Local := loc 7 `F_1 (F1T 5) :: loc 6 `t tN :: loc 5 `motive motTy :: o

/-- `PProd (x_k t) (Nat.below x_k t)` -/
def pairF (k : Nat) (t : Expr) : Expr :=
  .app (.app (tPP uu m1u) (.app (xv k) t)) (.app (.app (below uu) (xv k)) t)

/-- `@PProd.mk.{u, max 1 u} a b c d` -/
def mk4 (a b c d : Expr) : Expr := .app (.app (.app (.app (cPP uu m1u) a) b) c) d

/-- The arguments of `Nat.rec` in `Nat.brecOn.go`'s body. -/
def goMot : Expr := .lam `t tN (pairF 5 (.bvar 0)) .default
def fZ : Expr := .app (.app (xv 7) cZ) (cPU m1u)
def goMz : Expr := mk4 (.app (xv 5) cZ) (tPU m1u) fZ (cPU m1u)
def goMsBody (n ih : Expr) : Expr :=
  mk4 (.app (xv 5) (.app cS n)) (pairF 5 n) (.app (.app (xv 7) (.app cS n)) ih) ih
def goMs : Expr :=
  .lam `n tN (.lam `n_ih (pairF 5 (.bvar 0)) (goMsBody (.bvar 1) (.bvar 0)) .default) .default
def goB : Expr := .app (.app (.app (.app (.const `Nat.rec [m1u]) goMot) goMz) goMs) (xv 6)

theorem withApp_fZ {γ : Sort _} (k : Expr → Array Expr → γ) :
    fZ.withApp k = k (xv 7) #[cZ, cPU m1u] := by krfl

/-- `visitExpr` on `F_1 Nat.zero PUnit.unit`, `Nat` registered and `PUnit` not: `PUnit` is
registered by its constructor. Reference: the `tApp` case of `erase`
(`MR E/ErasureFunction.v:1006`). -/
theorem fZ_run {n : Nat} {L : LocalContext} {o : List Local}
    (hN : st.inductives[`Nat]? = some (iidN, masksN)) (hPU : st.inductives[`PUnit]? = none) :
    (visitExpr (m := PureM) (n + 10) fZ).runPure st ⟨L, lsGo o, none, cfg, dc⟩ pc ps =
      .ok ((.app (.app (.fvar (xf 7)) (natL 0)) unitL, stPU st), ps) := by
  rw [fZ, visitExpr, ← fZ]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ps) (by krfl) ?_
  rw [visitApp]
  change (fZ.withApp fun f args => do
    visitAppArgs (m := PureM) (n + 8) (← visitExpr (m := PureM) (n + 8) f) args).runPure _ _ _ _ = _
  rw [withApp_fZ]
  refine bind_ok (a := .fvar (xf 7)) (st' := st) (ps' := ps) (by krfl) ?_
  refine appArgs_cons (as := [cPU m1u]) (cZ_run (n := n + 1) hN) ?_
  refine appArgs_cons (as := []) (cPU_run_of (n := n + 1) (register_PU_new hPU)) ?_
  exact appArgs_nil

theorem withApp_goMz {γ : Sort _} (k : Expr → Array Expr → γ) :
    goMz.withApp k = k (cPP uu m1u) #[.app (xv 5) cZ, tPU m1u, fZ, cPU m1u] := by krfl

/-- The erasure of the minor premise of `Nat.zero` in `Nat.brecOn.go`. -/
def mzL : LBTerm :=
  .app (.app (.app (.app mkL .box) .box) (.app (.app (.fvar (xf 7)) (natL 0)) unitL)) unitL

/-- `visitExpr` on the minor premise `⟨F_1 Nat.zero PUnit.unit, PUnit.unit⟩` of `Nat.zero`,
`PProd` and `Nat` registered: the type arguments are erased. Reference: the `tConstruct` case of
`erase` (`MR E/ErasureFunction.v:1014`). -/
theorem mz_run {n : Nat} {L : LocalContext} {o : List Local}
    (hPP : st.inductives[`PProd]? = some (iidPP, masksPP))
    (hN : st.inductives[`Nat]? = some (iidN, masksN)) (hPU : st.inductives[`PUnit]? = none) :
    (visitExpr (m := PureM) (n + 15) goMz).runPure st ⟨L, lsGo o, none, cfg, dc⟩ pc ps =
      .ok ((mzL, stPU st), ps) := by
  rw [goMz, mk4, visitExpr, ← mk4, ← goMz]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ps) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 13) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_goMz]
  refine bind_ok (a := none) (st' := st) (ps' := ps) (by krfl) ?_
  refine bind_ok (a := some 4) (st' := st) (ps' := ps) (by krfl) ?_
  change (withAppEtaToMinArity (m := PureM) (n + 12) _ 4 _).runPure _ _ _ _ = _
  rw [withAppEtaToMinArity]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := .app (.app (tPP uu m1u) (.app (xv 5) cZ)) (tPU m1u)) (st' := st) (ps' := ps)
    (by krfl) ?_
  rw [withApp_goMz, withAppEtaToMinArity.go]
  rw [visitConstructor]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok (register_found hPP)
  dsimp only
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  simp only
  apply bind_ok rfl
  simp only [toArray_toSubarray, show PProd_mk.numParams = 2 from rfl,
    show PProd_mk.numFields = 2 from rfl, show PProd_mk.cidx = 0 from rfl]
  rw [args_PP]
  refine (congrArg (fun x : EraseT PureM LBTerm => x.runPure st ⟨L, lsGo o, none, cfg, dc⟩ pc ps)
    (?_ : _ = visitAppArgs (m := PureM) (n + 11) mkL #[.app (xv 5) cZ, tPU m1u, fZ, cPU m1u])).trans ?_
  · krfl
  refine appArgs_cons (as := [tPU m1u, fZ, cPU m1u]) (r := .box) (st' := st) (ps' := ps) (by krfl) ?_
  refine appArgs_cons (as := [fZ, cPU m1u]) (r := .box) (st' := st) (ps' := ps) (by krfl) ?_
  refine appArgs_cons (as := [cPU m1u]) (fZ_run (n := n) hN hPU) ?_
  refine appArgs_cons (as := []) (cPU_run_of (n := n + 4)
    (register_found (iv := PUnit_ind) stPU_PU)) ?_
  exact appArgs_nil

/-- The locals of the minor premise of `Nat.succ` in `Nat.brecOn.go`: `n`, `n_ih`. -/
def lsS (o : List Local) : List Local := loc 9 `n_ih (pairF 5 (xv 8)) :: loc 8 `n tN :: lsGo o

theorem withApp_sx {γ : Sort _} (k : Expr → Array Expr → γ) (x : Expr) :
    (Expr.app cS x).withApp k = k cS #[x] := withApp_app1 cS x k rfl

/-- The arguments `visitConstructor` passes on for `Nat.succ x`: the field, kept. -/
theorem args_s (x : Expr) : #[x].extract 0 0 ++
    filter #[ConstructorArgRelevance.keep]
      (↑(#[x].toSubarray 0 (0 + 1)) : Array Expr) ++ #[x].extract (0 + 1) = #[x] := by
  apply Array.toList_inj.mp
  simp [filter, toArray_toSubarray]

/-- `visitExpr` on `Nat.succ a`, `a` erased to `ra` with the state unchanged, `Nat` registered.
Reference: the `tConstruct` case of `erase` (`MR E/ErasureFunction.v:1014`). -/
theorem sArg_run {n : Nat} {a : Expr} {ra : LBTerm} {L : LocalContext} {ls : List Local}
    {F : Option (Std.HashMap Name FVarId)}
    (hE : Pure.isErasable ⟨D⟩ oracleFuel ls (.app cS a) = .ok false)
    (hT : Pure.inferType ⟨D⟩ oracleFuel ls [] (.app cS a) = .ok tN)
    (ha : (visitExpr (m := PureM) (n + 7) a).runPure st ⟨L, ls, F, cfg, dc⟩ pc ps = .ok ((ra, st), ps))
    (h : st.inductives[`Nat]? = some (iidN, masksN)) :
    (visitExpr (m := PureM) (n + 12) (.app cS a)).runPure st ⟨L, ls, F, cfg, dc⟩ pc ps =
      .ok ((.app (.construct iidN 1 []) ra, st), ps) := by
  rw [visitExpr]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ps)
    (erasable_step (pc := pc) (tc := ⟨L, ls, F, cfg, dc⟩) hE) ?_
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
    (infer_step (pc := pc) (tc := ⟨L, ls, F, cfg, dc⟩) hT) ?_
  rw [withApp_sx _ _, withAppEtaToMinArity.go]
  rw [visitConstructor]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok (register_found (iv := Nat_ind) h)
  dsimp only
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  simp only
  apply bind_ok rfl
  simp only [toArray_toSubarray, show Succ_ctor.numParams = 0 from rfl,
    show Succ_ctor.numFields = 1 from rfl, show Succ_ctor.cidx = 1 from rfl]
  rw [args_s]
  refine (congrArg (fun x : EraseT PureM LBTerm => x.runPure st ⟨L, ls, F, cfg, dc⟩ pc ps)
    (?_ : _ = visitAppArgs (m := PureM) (n + 8) (.construct iidN 1 []) #[a])).trans ?_
  · krfl
  exact appArgs_cons (as := []) ha appArgs_nil

/-- `visitExpr` on a local of `ls` that the oracle keeps. Reference: the `tRel` case of `erase`
(`MR E/ErasureFunction.v:997`). -/
theorem fvar_run {n k : Nat} {L : LocalContext} {ls : List Local}
    {F : Option (Std.HashMap Name FVarId)}
    (hE : Pure.isErasable ⟨D⟩ oracleFuel ls (xv k) = .ok false) :
    (visitExpr (m := PureM) (n + 1) (xv k)).runPure st ⟨L, ls, F, cfg, dc⟩ pc ps =
      .ok ((.fvar (xf k), st), ps) := by
  rw [xv, visitExpr]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ps)
    (erasable_step (pc := pc) (tc := ⟨L, ls, F, cfg, dc⟩) hE) ?_
  rfl

/-- `F_1 (Nat.succ n) n_ih` in the minor premise of `Nat.succ`. -/
def fS : Expr := .app (.app (xv 7) (.app cS (xv 8))) (xv 9)

theorem withApp_fS {γ : Sort _} (k : Expr → Array Expr → γ) :
    fS.withApp k = k (xv 7) #[.app cS (xv 8), xv 9] := by krfl

/-- `visitExpr` on `F_1 (Nat.succ n) n_ih`, `Nat` registered. Reference: the `tApp` case of
`erase` (`MR E/ErasureFunction.v:1006`). -/
theorem fS_run {n : Nat} {L : LocalContext} {o : List Local}
    (hN : st.inductives[`Nat]? = some (iidN, masksN)) :
    (visitExpr (m := PureM) (n + 15) fS).runPure st ⟨L, lsS o, none, cfg, dc⟩ pc ps =
      .ok ((.app (.app (.fvar (xf 7)) (.app (.construct iidN 1 []) (.fvar (xf 8)))) (.fvar (xf 9)),
        st), ps) := by
  rw [fS, visitExpr, ← fS]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ps) (by krfl) ?_
  rw [visitApp]
  change (fS.withApp fun f args => do
    visitAppArgs (m := PureM) (n + 13) (← visitExpr (m := PureM) (n + 13) f) args).runPure _ _ _ _ = _
  rw [withApp_fS]
  refine bind_ok (a := .fvar (xf 7)) (st' := st) (ps' := ps) (by krfl) ?_
  refine appArgs_cons (as := [xv 9])
    (sArg_run (n := n) (by krfl) (by krfl) (fvar_run (n := n + 6) (by krfl)) hN) ?_
  refine appArgs_cons (as := []) (r := .fvar (xf 9)) (st' := st) (ps' := ps) (by krfl) ?_
  exact appArgs_nil

def msB : Expr := goMsBody (xv 8) (xv 9)

theorem withApp_msB {γ : Sort _} (k : Expr → Array Expr → γ) :
    msB.withApp k = k (cPP uu m1u) #[.app (xv 5) (.app cS (xv 8)), pairF 5 (xv 8), fS, xv 9] := by
  krfl

/-- The erasure of the body of the minor premise of `Nat.succ`. -/
def msBL : LBTerm :=
  .app (.app (.app (.app mkL .box) .box)
    (.app (.app (.fvar (xf 7)) (.app (.construct iidN 1 []) (.fvar (xf 8)))) (.fvar (xf 9))))
    (.fvar (xf 9))

/-- `visitExpr` on `⟨F_1 (Nat.succ n) n_ih, n_ih⟩`, `PProd` and `Nat` registered. Reference: the
`tConstruct` case of `erase` (`MR E/ErasureFunction.v:1014`). -/
theorem msB_run {n : Nat} {L : LocalContext} {o : List Local}
    (hPP : st.inductives[`PProd]? = some (iidPP, masksPP))
    (hN : st.inductives[`Nat]? = some (iidN, masksN)) :
    (visitExpr (m := PureM) (n + 20) msB).runPure st ⟨L, lsS o, none, cfg, dc⟩ pc ps =
      .ok ((msBL, st), ps) := by
  rw [msB, goMsBody, mk4, visitExpr, ← mk4, ← goMsBody, ← msB]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ps) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 18) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_msB]
  refine bind_ok (a := none) (st' := st) (ps' := ps) (by krfl) ?_
  refine bind_ok (a := some 4) (st' := st) (ps' := ps) (by krfl) ?_
  change (withAppEtaToMinArity (m := PureM) (n + 17) _ 4 _).runPure _ _ _ _ = _
  rw [withAppEtaToMinArity]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := .app (.app (tPP uu m1u) (.app (xv 5) (.app cS (xv 8)))) (pairF 5 (xv 8)))
    (st' := st) (ps' := ps) (by krfl) ?_
  rw [withApp_msB, withAppEtaToMinArity.go]
  rw [visitConstructor]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok (register_found hPP)
  dsimp only
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  simp only
  apply bind_ok rfl
  simp only [toArray_toSubarray, show PProd_mk.numParams = 2 from rfl,
    show PProd_mk.numFields = 2 from rfl, show PProd_mk.cidx = 0 from rfl]
  rw [args_PP]
  refine (congrArg (fun x : EraseT PureM LBTerm => x.runPure st ⟨L, lsS o, none, cfg, dc⟩ pc ps)
    (?_ : _ = visitAppArgs (m := PureM) (n + 16) mkL
      #[.app (xv 5) (.app cS (xv 8)), pairF 5 (xv 8), fS, xv 9])).trans ?_
  · krfl
  refine appArgs_cons (as := [pairF 5 (xv 8), fS, xv 9]) (r := .box) (st' := st) (ps' := ps)
    (by krfl) ?_
  refine appArgs_cons (as := [fS, xv 9]) (r := .box) (st' := st) (ps' := ps) (by krfl) ?_
  refine appArgs_cons (as := [xv 9]) (fS_run (n := n) hN) ?_
  refine appArgs_cons (as := []) (r := .fvar (xf 9)) (st' := st) (ps' := ps) (by krfl) ?_
  exact appArgs_nil

/-- The erasure of the minor premise of `Nat.succ` in `Nat.brecOn.go`. -/
def msL : LBTerm :=
  .lambda (binderNameOf `n) (_root_.abstract (xf 8)
    (.lambda (binderNameOf `n_ih) (_root_.abstract (xf 9) msBL)))

/-- `visitExpr` on the minor premise `fun n n_ih => ⟨F_1 (Nat.succ n) n_ih, n_ih⟩` of
`Nat.succ`, `PProd` and `Nat` registered, from the counter's ninth variable. Reference: the
`tLambda` case of `erase` (`MR E/ErasureFunction.v:1003`). -/
theorem ms_run {n : Nat} {L : LocalContext} {o : List Local}
    (hPP : st.inductives[`PProd]? = some (iidPP, masksPP))
    (hN : st.inductives[`Nat]? = some (iidN, masksN)) :
    (visitExpr (m := PureM) (n + 24) goMs).runPure st ⟨L, lsGo o, none, cfg, dc⟩ pc ⟨8⟩ =
      .ok ((msL, st), ⟨10⟩) :=
  lam_run (by krfl) fun _ => lam_run (by krfl) fun _ => msB_run (n := n) hPP hN

/-- The erasure of `Nat.brecOn.go`'s body: the minor premises let-bound around NV-L's fixpoint of
`Nat`'s block, applied to `t`. -/
def goBL : LBTerm :=
  .letIn (binderNameOf `zero) mzL (.letIn (binderNameOf `succ) msL (.app fixL (.fvar (xf 6))))

theorem withApp_goB {γ : Sort _} (k : Expr → Array Expr → γ) :
    goB.withApp k = k (.const `Nat.rec [m1u]) #[goMot, goMz, goMs, xv 6] := by krfl

theorem goB_app : goB = .app (mkAppN (.const `Nat.rec [m1u]) #[goMot, goMz, goMs]) (xv 6) := rfl

/-- `visitExpr` on `Nat.brecOn.go`'s body `Nat.rec (fun t => PProd (motive t) (Nat.below motive t))
mz ms t`: `visitConstApp`'s recursor branch, `visitRec`; `Nat` is registered by the loop over the
block, `PUnit` by the first minor premise. Reference: none (DV-30). -/
theorem goB_run {n : Nat} {L : LocalContext} {o : List Local}
    (hPP : st.inductives[`PProd]? = some (iidPP, masksPP))
    (hN : st.inductives[`Nat]? = none) (hPU : st.inductives[`PUnit]? = none) :
    (visitExpr (m := PureM) (n + 30) goB).runPure st ⟨L, lsGo o, none, cfg, dc⟩ pc ⟨8⟩ =
      .ok ((goBL, stPU (stN st)), ⟨10⟩) := by
  have hPP' : (stN st).inductives[`PProd]? = some (iidPP, masksPP) := by
    simp only [stN, Std.HashMap.getElem?_insert, hPP]; rfl
  have hPU' : (stN st).inductives[`PUnit]? = none := by
    simp only [stN, Std.HashMap.getElem?_insert, hPU]; rfl
  have hN' : (stPU (stN st)).inductives[`Nat]? = some (iidN, masksN) := by
    simp only [stPU, stN, Std.HashMap.getElem?_insert]; rfl
  have hPP'' : (stPU (stN st)).inductives[`PProd]? = some (iidPP, masksPP) := by
    simp only [stPU, Std.HashMap.getElem?_insert, hPP']; rfl
  rw [goB_app, visitExpr, ← goB_app]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ⟨8⟩) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 28) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_goB]
  refine bind_ok (a := none) (st' := st) (ps' := ⟨8⟩) (by krfl) ?_
  refine bind_ok (a := none) (st' := st) (ps' := ⟨8⟩) (by krfl) ?_
  refine bind_ok (a := some (.recInfo Nat_rec)) (st' := st) (ps' := ⟨8⟩) (by krfl) ?_
  change (visitRec (m := PureM) (n + 27) _ _).runPure _ _ _ _ = _
  rw [visitRec]
  refine bind_ok (a := [Nat_ind]) (st' := st) (ps' := ⟨8⟩) (by krfl) ?_
  refine bind_ok (a := [Zero_ctor, Succ_ctor]) (st' := st) (ps' := ⟨8⟩) (by krfl) ?_
  apply bind_ok rfl
  have hnsc : recStaysConstant .peano Nat_rec [Nat_ind] [Zero_ctor, Succ_ctor] = false := by krfl
  simp only [show cfg.nat = .peano from rfl, hnsc, Bool.false_eq_true, ↓reduceIte]
  rw [recShape_N]
  dsimp only
  rw [List.forIn_cons]
  simp only [List.forIn_nil, Std.toStream, Std.Stream.next?]
  refine bind_ok (a := (#[memberN], 2, [])) (st' := stN st) (ps' := ⟨8⟩) ?_ ?_
  · refine bind_ok (a := ForInStep.yield (#[memberN], 2, [])) (st' := stN st) (ps' := ⟨8⟩) ?_ ?_
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
  refine bind_ok (a := .app goMot (xv 6)) (st' := stN st) (ps' := ⟨8⟩) (by krfl) ?_
  rw [withApp_goB, withAppEtaToMinArity.go]
  simp only [show (#[goMot, goMz, goMs, xv 6] : Array Expr).size = 4 from rfl, ge_iff_le,
    Nat.le_refl, ↓reduceIte]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := Level.succ .zero) (st' := stN st) (ps' := ⟨8⟩) (by krfl) ?_
  rw [show (#[goMot, goMz, goMs, xv 6].extract 1 (1 + 2)).toList = [goMz, goMs] from rfl]
  simp only [List.mapM_cons, List.mapM_nil]
  refine bind_ok (a := [mzL, msL]) (st' := stPU (stN st)) (ps' := ⟨10⟩) ?_ ?_
  · apply bind_ok (mz_run (n := n + 11) hPP' stN_N hPU')
    refine bind_ok (a := [msL]) (st' := stPU (stN st)) (ps' := ⟨10⟩) ?_ ?_
    · apply bind_ok (ms_run (n := n + 2) hPP'' hN')
      rfl
    rfl
  rw [visitAppArgs, show (#[goMot, goMz, goMs, xv 6].extract (1 + 2) 4) = #[xv 6] from rfl,
    ← Array.foldlM_toList]
  simp only [List.foldlM_cons, List.foldlM_nil]
  refine bind_ok (a := .app fixL (.fvar (xf 6))) (st' := stPU (stN st)) (ps' := ⟨10⟩) ?_ ?_
  · refine bind_ok (a := .app fixL (.fvar (xf 6))) (st' := stPU (stN st)) (ps' := ⟨10⟩) ?_ ?_
    · refine bind_ok (a := LBTerm.fvar (xf 6)) (st' := stPU (stN st)) (ps' := ⟨10⟩) (by krfl) ?_
      rfl
    rfl
  rw [visitAppArgs]
  rfl

/-- The erasure of `Nat.brecOn.go`'s value. -/
def goVL : LBTerm :=
  .lambda (binderNameOf `motive) (_root_.abstract (xf 5) (.lambda (binderNameOf `t)
    (_root_.abstract (xf 6) (.lambda (binderNameOf `F_1) (_root_.abstract (xf 7) goBL)))))

/-- `visitExpr` on `Nat.brecOn.go`'s value, from the counter's sixth variable. Reference: the
`tLambda` case of `erase` (`MR E/ErasureFunction.v:1003`). -/
theorem goV_run {n : Nat} {L : LocalContext} {o : List Local}
    (hPP : st.inductives[`PProd]? = some (iidPP, masksPP))
    (hN : st.inductives[`Nat]? = none) (hPU : st.inductives[`PUnit]? = none) :
    (visitExpr (m := PureM) (n + 36) goVal).runPure st ⟨L, o, none, cfg, dc⟩ pc ⟨5⟩ =
      .ok ((goVL, stPU (stN st)), ⟨10⟩) :=
  lam_run (by krfl) fun _ => lam_run (by krfl) fun _ => lam_run (by krfl) fun _ =>
    goB_run (n := n) hPP hN hPU

/-- `visitMutual` on `Nat.brecOn.go`: a single, non-recursive definition without attributes,
erased to a λ□ constant. Reference: `erase_constant_body` (`MR E/ErasureFunction.v:1309`) in
`erase_global_deps` (`MR E/ErasureFunction.v:1602`). -/
theorem visitMutual_go {n : Nat} {L : LocalContext} {o : List Local}
    {F : Option (Std.HashMap Name FVarId)}
    (hPP : st.inductives[`PProd]? = some (iidPP, masksPP))
    (hN : st.inductives[`Nat]? = none) (hPU : st.inductives[`PUnit]? = none) :
    (visitMutual (m := PureM) (n + 37) `Nat.brecOn.go).runPure st ⟨L, o, F, cfg, dc⟩ pc ⟨5⟩ =
      .ok (((), stDef (stPU (stN st)) `Nat.brecOn.go goVL), ⟨10⟩) := by
  rw [visitMutual]
  iterate 8 apply bind_ok rfl
  refine bind_ok (a := goVL) (st' := stPU (stN st)) (ps' := ⟨10⟩) ?_ ?_
  · rw [runPure_withReader]
    apply bind_ok rfl
    refine bind_ok (a := goVal) (st' := st) (ps' := ⟨5⟩) rfl ?_
    exact goV_run (n := n) hPP hN hPU
  rfl

/-- `get_constant_kername` on `Nat.brecOn.go`, not yet erased. Reference: `erase_global_deps`
(`MR E/ErasureFunction.v:1602`). -/
theorem kername_go {n : Nat} {L : LocalContext} {o : List Local}
    {F : Option (Std.HashMap Name FVarId)} (hc : st.constants[`Nat.brecOn.go]? = none)
    (hPP : st.inductives[`PProd]? = some (iidPP, masksPP))
    (hN : st.inductives[`Nat]? = none) (hPU : st.inductives[`PUnit]? = none) :
    (get_constant_kername (m := PureM) (n + 38) `Nat.brecOn.go).runPure st ⟨L, o, F, cfg, dc⟩ pc
      ⟨5⟩ = .ok ((toKername `Nat.brecOn.go, stDef (stPU (stN st)) `Nat.brecOn.go goVL), ⟨10⟩) := by
  rw [get_constant_kername]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, hc]
  apply bind_ok (visitMutual_go hPP hN hPU)
  apply bind_ok rfl
  simp only [stDef, Std.HashMap.getElem?_insert_self]
  rfl

/-! ## `Nat.brecOn` -/

/-- The locals of `Nat.brecOn`'s body: `motive`, `t`, `F_1`. -/
def lsB (o : List Local) : List Local :=
  loc 4 `F_1 (F1T 2) :: loc 3 `t tN :: loc 2 `motive motTy :: o

/-- `Nat.brecOn.go motive t F_1` in `Nat.brecOn`'s body. -/
def goApp : Expr := .app (.app (.app (.const `Nat.brecOn.go [uu]) (xv 2)) (xv 3)) (xv 4)

theorem withApp_goApp {γ : Sort _} (k : Expr → Array Expr → γ) :
    goApp.withApp k = k (.const `Nat.brecOn.go [uu]) #[xv 2, xv 3, xv 4] := by krfl

/-- The state after `Nat.brecOn.go`. -/
abbrev stGo (st : ErasureState) : ErasureState := stDef (stPU (stN st)) `Nat.brecOn.go goVL

/-- `visitExpr` on `Nat.brecOn.go motive t F_1`, `Nat.brecOn.go` not erased, `PProd` registered:
the λ□ constant of `Nat.brecOn.go`, erased on the way, applied to □ for the motive. Reference: the
`tConst` and `tApp` cases of `erase` (`MR E/ErasureFunction.v:999`, `:1006`). -/
theorem goApp_run {n : Nat} {L : LocalContext} {o : List Local}
    (hc : st.constants[`Nat.brecOn.go]? = none)
    (hPP : st.inductives[`PProd]? = some (iidPP, masksPP))
    (hN : st.inductives[`Nat]? = none) (hPU : st.inductives[`PUnit]? = none) :
    (visitExpr (m := PureM) (n + 44) goApp).runPure st ⟨L, lsB o, none, cfg, dc⟩ pc ⟨5⟩ =
      .ok ((.app (.app (.app (.const (toKername `Nat.brecOn.go)) .box) (.fvar (xf 3)))
        (.fvar (xf 4)), stGo st), ⟨10⟩) := by
  rw [goApp, visitExpr, ← goApp]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ⟨5⟩) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 42) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_goApp]
  refine bind_ok (a := none) (st' := st) (ps' := ⟨5⟩) (by krfl) ?_
  refine bind_ok (a := none) (st' := st) (ps' := ⟨5⟩) (by krfl) ?_
  refine bind_ok (a := some (.defnInfo Nat_brecOn_go)) (st' := st) (ps' := ⟨5⟩) (by krfl) ?_
  refine bind_ok (a := .const (toKername `Nat.brecOn.go)) (st' := stGo st) (ps' := ⟨10⟩) ?_ ?_
  · rw [visitConst]
    apply bind_ok rfl
    refine bind_ok (kername_go (n := n + 2) hc hPP hN hPU) ?_
    rfl
  refine appArgs_cons (as := [xv 3, xv 4]) (r := .box) (st' := stGo st) (ps' := ⟨10⟩) (by krfl) ?_
  refine appArgs_cons (as := [xv 4]) (r := .fvar (xf 3)) (st' := stGo st) (ps' := ⟨10⟩) (by krfl) ?_
  refine appArgs_cons (as := []) (r := .fvar (xf 4)) (st' := stGo st) (ps' := ⟨10⟩) (by krfl) ?_
  exact appArgs_nil

/-- The erasure of `Nat.brecOn`'s value. -/
def brecOnVL : LBTerm :=
  .lambda (binderNameOf `motive) (_root_.abstract (xf 2) (.lambda (binderNameOf `t)
    (_root_.abstract (xf 3) (.lambda (binderNameOf `F_1) (_root_.abstract (xf 4)
      (.proj projPP
        (.app (.app (.app (.const (toKername `Nat.brecOn.go)) .box) (.fvar (xf 3)))
          (.fvar (xf 4)))))))))

/-- `visitExpr` on `Nat.brecOn`'s value, `PProd` not registered: the first projection of
`Nat.brecOn.go`'s pair, where the projection registers `PProd`. Reference: the `tLambda` and
`tProj` cases of `erase` (`MR E/ErasureFunction.v:1003`, `:1020`). -/
theorem brecOnV_run {n : Nat} {L : LocalContext} {o : List Local}
    (hc : st.constants[`Nat.brecOn.go]? = none) (hPP : st.inductives[`PProd]? = none)
    (hN : st.inductives[`Nat]? = none) (hPU : st.inductives[`PUnit]? = none) :
    (visitExpr (m := PureM) (n + 52) brecOnVal).runPure st ⟨L, o, none, cfg, dc⟩ pc ⟨2⟩ =
      .ok ((brecOnVL, stGo (stPP st)), ⟨10⟩) := by
  refine lam_run (by krfl) fun _ => lam_run (by krfl) fun _ => lam_run (by krfl) fun L' => ?_
  show (visitExpr (m := PureM) (n + 46) (.proj `PProd 0 goApp)).runPure st
    ⟨L', lsB o, none, cfg, dc⟩ pc ⟨5⟩ = _
  rw [visitExpr]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ⟨5⟩) (by krfl) ?_
  change (visitProj (m := PureM) (n + 45) `PProd 0 goApp).runPure _ _ _ _ = _
  rw [visitProj]
  apply bind_ok rfl
  apply bind_ok (register_PP_new hPP)
  apply bind_ok rfl
  refine bind_ok (goApp_run (n := n) hc (by simp only [stPP, Std.HashMap.getElem?_insert_self])
    (by simp only [stPP, Std.HashMap.getElem?_insert, hN]; rfl)
    (by simp only [stPP, Std.HashMap.getElem?_insert, hPU]; rfl)) ?_
  simp only [toArray_toSubarray]
  rfl

/-- The state after `Nat.brecOn`. -/
abbrev stBr (st : ErasureState) : ErasureState := stDef (stGo (stPP st)) `Nat.brecOn brecOnVL

/-- `visitMutual` on `Nat.brecOn`. Reference: as `visitMutual_go`. -/
theorem visitMutual_brecOn {n : Nat} {L : LocalContext} {o : List Local}
    {F : Option (Std.HashMap Name FVarId)}
    (hc : st.constants[`Nat.brecOn.go]? = none) (hPP : st.inductives[`PProd]? = none)
    (hN : st.inductives[`Nat]? = none) (hPU : st.inductives[`PUnit]? = none) :
    (visitMutual (m := PureM) (n + 53) `Nat.brecOn).runPure st ⟨L, o, F, cfg, dc⟩ pc ⟨2⟩ =
      .ok (((), stBr st), ⟨10⟩) := by
  rw [visitMutual]
  iterate 8 apply bind_ok rfl
  refine bind_ok (a := brecOnVL) (st' := stGo (stPP st)) (ps' := ⟨10⟩) ?_ ?_
  · rw [runPure_withReader]
    apply bind_ok rfl
    refine bind_ok (a := brecOnVal) (st' := st) (ps' := ⟨2⟩) rfl ?_
    exact brecOnV_run (n := n) hc hPP hN hPU
  rfl

/-- `get_constant_kername` on `Nat.brecOn`, not yet erased. Reference: `erase_global_deps`
(`MR E/ErasureFunction.v:1602`). -/
theorem kername_brecOn {n : Nat} {L : LocalContext} {o : List Local}
    {F : Option (Std.HashMap Name FVarId)} (hb : st.constants[`Nat.brecOn]? = none)
    (hc : st.constants[`Nat.brecOn.go]? = none) (hPP : st.inductives[`PProd]? = none)
    (hN : st.inductives[`Nat]? = none) (hPU : st.inductives[`PUnit]? = none) :
    (get_constant_kername (m := PureM) (n + 54) `Nat.brecOn).runPure st ⟨L, o, F, cfg, dc⟩ pc ⟨2⟩ =
      .ok ((toKername `Nat.brecOn, stBr st), ⟨10⟩) := by
  rw [get_constant_kername]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, hb]
  apply bind_ok (visitMutual_brecOn hc hPP hN hPU)
  apply bind_ok rfl
  simp only [stBr, stDef, Std.HashMap.getElem?_insert_self]
  rfl


/-! ## `Nat.add.match_1` -/

/-- The locals of `Nat.add`'s body: `x`, `y`. -/
def lsA : List Local := [loc 1 x14 tN, loc 0 x13 tN]

/-- The locals of `Nat.add._f`'s body: `y`, `f`, `x`. -/
def lsF : List Local := loc 12 x13 tN :: loc 11 `f (belowA (xv 10)) :: loc 10 x14 tN :: lsA

/-- The locals of `Nat.add.match_1`'s body: `motive`, `x`, `y`, `h_1`, `h_2`. -/
def lsM : List Local :=
  loc 17 `h_2 (.forallE `a tN (.forallE `b tN (.app (.app (xv 13) (.bvar 1)) (.app cS (.bvar 0)))
      .default) .default) ::
    loc 16 `h_1 (.forallE `a tN (.app (.app (xv 13) (.bvar 0)) cZ) .default) ::
    loc 15 x35 tN :: loc 14 x32 tN :: loc 13 `motive mMotTy :: lsF

/-- The motive and the alternatives of `Nat.add.match_1`'s `casesOn`. -/
def motM : Expr := .lam `x tN (.app (.app (xv 13) (xv 14)) (.bvar 0)) .default
def alt1 : Expr := .app (xv 16) (xv 14)
def alt2 : Expr := .lam n58 tN (.app (.app (xv 17) (xv 14)) (.bvar 0)) .default

/-- `Nat.add.match_1`'s body. -/
def mB : Expr := .app (.app (.app (.app (.const `Nat.casesOn [u1]) motM) (xv 15)) alt1) alt2

theorem withApp_mB {γ : Sort _} (k : Expr → Array Expr → γ) :
    mB.withApp k = k (.const `Nat.casesOn [u1]) #[motM, xv 15, alt1, alt2] := by krfl

/-- The erasures of the alternatives, `h_1 x` and, under its field, `h_2 x n`. -/
def alt1L : LBTerm := .app (.fvar (xf 16)) (.fvar (xf 14))
def alt2L : LBTerm := .app (.app (.fvar (xf 17)) (.fvar (xf 14))) (.bvar 0)

/-- `visitAlt` on the first alternative `h_1 x` (no field). Reference: the branches of the
`tCase` case of `erase` (`MR E/ErasureFunction.v:1016`). -/
theorem alt1_run {n : Nat} {L : LocalContext} :
    (visitAlt (m := PureM) (n + 10) 0 #[] [] alt1).runPure st ⟨L, lsM, none, cfg, dc⟩ pc ⟨18⟩ =
      .ok ((([], alt1L), st), ⟨18⟩) := by
  krfl

/-- `visitAlt` on the second alternative `fun n => h_2 x n` (one field), from the counter's
nineteenth variable. Reference: the branches of the `tCase` case of `erase`
(`MR E/ErasureFunction.v:1016`). -/
theorem alt2_run {n : Nat} {L : LocalContext} :
    (visitAlt (m := PureM) (n + 10) 1 #[.keep] [] alt2).runPure st ⟨L, lsM, none, cfg, dc⟩ pc ⟨18⟩ =
      .ok ((([binderNameOf n58], alt2L), st), ⟨19⟩) := by
  krfl

/-- `visitCases`'s alternatives of `Nat.add.match_1`'s `casesOn`. -/
def altsM : Std.HashMap Name (Nat × Expr) :=
  ((∅ : Std.HashMap Name (Nat × Expr)).insert `Nat.zero (0, alt1)).insert `Nat.succ (1, alt2)

theorem altsM_z : altsM[`Nat.zero]? = some (0, alt1) := by
  simp only [altsM, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]; rfl

theorem altsM_s : altsM[`Nat.succ]? = some (1, alt2) := by
  simp only [altsM, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]; rfl

theorem altsM_all : ([`Nat.zero, `Nat.succ].all fun x => altsM.contains x) = true := by
  simp only [altsM, Std.HashMap.contains_insert, Std.HashMap.contains_empty]; rfl

/-- The erasure of `Nat.add.match_1`'s body: the λ□ `case` on `y`. -/
def caseM : LBTerm :=
  .case (iidN, 0) (.fvar (xf 15)) [([], alt1L), ([binderNameOf n58], alt2L)]

/-- `visitCasesOn` on `Nat.add.match_1`'s alternatives and the discriminant `y`, `Nat` registered.
Reference: the `tCase` case of `erase` (`MR E/ErasureFunction.v:1016`). -/
theorem visitCasesOn_run {n : Nat} {L : LocalContext}
    (hN : st.inductives[`Nat]? = some (iidN, masksN)) :
    (visitCasesOn (m := PureM) (n + 19) Nat_ind altsM ∅ none (.fvar (xf 15))).runPure st
      ⟨L, lsM, none, cfg, dc⟩ pc ⟨18⟩ = .ok ((caseM, st), ⟨19⟩) := by
  rw [visitCasesOn]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok (register_found (iv := Nat_ind) hN)
  simp only [show Nat_ind.ctors = [`Nat.zero, `Nat.succ] from rfl, List.forIn_cons, List.forIn_nil,
    bind_assoc, altsM_z, altsM_s, Std.HashMap.getD_empty]
  refine bind_ok (a := .yield (#[([], alt1L)], ([#[.keep]] : List ConstructorArgMask)))
    (st' := st) (ps' := ⟨18⟩) ?_ ?_
  · apply bind_ok (alt1_run (n := n + 8))
    rfl
  refine bind_ok (a := (#[([], alt1L), ([binderNameOf n58], alt2L)],
    ([] : List ConstructorArgMask))) (st' := st) (ps' := ⟨19⟩) ?_ ?_
  · refine bind_ok (a := .yield (#[([], alt1L), ([binderNameOf n58], alt2L)],
      ([] : List ConstructorArgMask))) (st' := st) (ps' := ⟨19⟩) ?_ ?_
    · apply bind_ok (alt2_run (n := n + 8))
      rfl
    · rfl
  rfl

/-- The recognizer's answer on `Nat.casesOn`. -/
def ciN : CasesInfo :=
  { declName := `Nat.casesOn, indName := `Nat, arity := 4, discrPos := 1, motivePos := 0,
    altsRange := 2...4, altNumParams := #[.ctor `Nat.zero 0, .ctor `Nat.succ 1] }

/-- `visitCases` on `Nat.add.match_1`'s `casesOn`: `Nat.casesOn` has one universe parameter more
than `Nat`, and the discriminant's sort is never `Prop`, so the result is the λ□ `case`.
Reference: the `tCase` case of `erase` (`MR E/ErasureFunction.v:1016`). -/
theorem visitCases_run {n : Nat} {L : LocalContext}
    (hN : st.inductives[`Nat]? = some (iidN, masksN)) :
    (visitCases (m := PureM) (n + 22) ciN #[motM, xv 15, alt1, alt2]).runPure st
      ⟨L, lsM, none, cfg, dc⟩ pc ⟨18⟩ = .ok ((caseM, st), ⟨19⟩) := by
  rw [visitCases]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := Level.succ .zero) (st' := st) (ps' := ⟨18⟩) (by krfl) ?_
  have hr : (ciN.altsRange.toList) = [2, 3] := by simp [ciN, Nat.toList_rco_eq_ite]
  simp only [← forIn'_eq_forIn, Std.Rco.forIn'_eq_forIn'_toList, hr, List.forIn'_cons,
    List.forIn'_nil]
  refine bind_ok (a := (altsM, none, ?sEnd)) (st' := st) (ps' := ⟨18⟩) ?_ ?_
  case sEnd => exact (ciN.altNumParams.toSubarray 2 2)
  · rfl
  refine bind_ok (a := .fvar (xf 15)) (st' := st) (ps' := ⟨18⟩) (by krfl) ?_
  simp only [show Nat_ind.ctors = [`Nat.zero, `Nat.succ] from rfl, altsM_all, ite_true]
  apply bind_ok (visitCasesOn_run (n := n + 2) hN)
  rw [show ciN.arity = (#[motM, xv 15, alt1, alt2] : Array Expr).size from rfl,
    forIn_toSubarray_size]
  rfl

/-- `visitExpr` on `Nat.add.match_1`'s body: a saturated recognized `casesOn`. Reference: the
`tCase` case of `erase` (`MR E/ErasureFunction.v:1016`). -/
theorem mB_run {n : Nat} {L : LocalContext} (hN : st.inductives[`Nat]? = some (iidN, masksN)) :
    (visitExpr (m := PureM) (n + 26) mB).runPure st ⟨L, lsM, none, cfg, dc⟩ pc ⟨18⟩ =
      .ok ((caseM, st), ⟨19⟩) := by
  rw [mB, visitExpr, ← mB]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ⟨18⟩) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 24) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_mB]
  refine bind_ok (a := some ciN) (st' := st) (ps' := ⟨18⟩) (by krfl) ?_
  change (withAppEtaToMinArity (m := PureM) (n + 23) _ 4 _).runPure _ _ _ _ = _
  rw [withAppEtaToMinArity]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := .app motM (xv 15)) (st' := st) (ps' := ⟨18⟩)
    (infer_step (pc := pc) (tc := ⟨L, lsM, none, cfg, dc⟩) (by krfl)) ?_
  rw [withApp_mB, withAppEtaToMinArity.go]
  simp only [show (#[motM, xv 15, alt1, alt2] : Array Expr).size = 4 from rfl, ge_iff_le,
    Nat.le_refl, ↓reduceIte]
  exact visitCases_run (n := n + 1) hN

/-- The erasure of `Nat.add.match_1`'s value. -/
def matchVL : LBTerm :=
  .lambda (binderNameOf `motive) (_root_.abstract (xf 13) (.lambda (binderNameOf x32)
    (_root_.abstract (xf 14) (.lambda (binderNameOf x35) (_root_.abstract (xf 15)
      (.lambda (binderNameOf `h_1) (_root_.abstract (xf 16)
        (.lambda (binderNameOf `h_2) (_root_.abstract (xf 17) caseM)))))))))

/-- `visitExpr` on `Nat.add.match_1`'s value, from the counter's fourteenth variable. Reference: the
`tLambda` case of `erase` (`MR E/ErasureFunction.v:1003`). -/
theorem matchV_run {n : Nat} {L : LocalContext} (hN : st.inductives[`Nat]? = some (iidN, masksN)) :
    (visitExpr (m := PureM) (n + 36) matchVal).runPure st ⟨L, lsF, none, cfg, dc⟩ pc ⟨13⟩ =
      .ok ((matchVL, st), ⟨19⟩) :=
  lam_run (by krfl) fun _ => lam_run (by krfl) fun _ => lam_run (by krfl) fun _ =>
    lam_run (by krfl) fun _ => lam_run (by krfl) fun _ => mB_run (n := n) hN

/-- The state after `Nat.add.match_1`. -/
abbrev stMt (st : ErasureState) : ErasureState := stDef st `Nat.add.match_1 matchVL

/-- `visitMutual` on `Nat.add.match_1`: a single, non-recursive definition without attributes (a
matcher of `Init.Prelude`, which has no `@[inline]` attribute), erased to a λ□ constant.
Reference: as `visitMutual_go`. -/
theorem visitMutual_match {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)}
    (hN : st.inductives[`Nat]? = some (iidN, masksN)) :
    (visitMutual (m := PureM) (n + 37) `Nat.add.match_1).runPure st ⟨L, lsF, F, cfg, dc⟩ pc ⟨13⟩ =
      .ok (((), stMt st), ⟨19⟩) := by
  rw [visitMutual]
  iterate 8 apply bind_ok rfl
  refine bind_ok (a := matchVL) (st' := st) (ps' := ⟨19⟩) ?_ ?_
  · rw [runPure_withReader]
    apply bind_ok rfl
    refine bind_ok (a := matchVal) (st' := st) (ps' := ⟨13⟩) rfl ?_
    exact matchV_run (n := n) hN
  rfl

/-- `get_constant_kername` on `Nat.add.match_1`, not yet erased. Reference: `erase_global_deps`
(`MR E/ErasureFunction.v:1602`). -/
theorem kername_match {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)}
    (hm : st.constants[`Nat.add.match_1]? = none) (hN : st.inductives[`Nat]? = some (iidN, masksN)) :
    (get_constant_kername (m := PureM) (n + 38) `Nat.add.match_1).runPure st ⟨L, lsF, F, cfg, dc⟩
      pc ⟨13⟩ = .ok ((toKername `Nat.add.match_1, stMt st), ⟨19⟩) := by
  rw [get_constant_kername]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, hm]
  apply bind_ok (visitMutual_match hN)
  apply bind_ok rfl
  simp only [stMt, stDef, Std.HashMap.getElem?_insert_self]
  rfl


/-! ## `Nat.add._f` -/

/-- Facts about the traversal's maps in the states of the run. -/
macro (name := _stfactA) "astfact" : tactic =>
  `(tactic| (simp only [stMt, stBr, stGo, stDef, stPU, stN, stPP, stOf,
    Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]; try rfl))

/-- `visitExpr` on the projection `x.1` of `PProd`, `x` the `k`-th local, `PProd` registered.
Reference: the `tProj` case of `erase` (`MR E/ErasureFunction.v:1020`). -/
theorem projX_run {n k : Nat} {L : LocalContext} {ls : List Local}
    {F : Option (Std.HashMap Name FVarId)}
    (hE : Pure.isErasable ⟨D⟩ oracleFuel ls (.proj `PProd 0 (xv k)) = .ok false)
    (hEx : Pure.isErasable ⟨D⟩ oracleFuel ls (xv k) = .ok false)
    (hPP : st.inductives[`PProd]? = some (iidPP, masksPP)) :
    (visitExpr (m := PureM) (n + 4) (.proj `PProd 0 (xv k))).runPure st ⟨L, ls, F, cfg, dc⟩ pc ps =
      .ok ((.proj projPP (.fvar (xf k)), st), ps) := by
  rw [visitExpr]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ps)
    (erasable_step (pc := pc) (tc := ⟨L, ls, F, cfg, dc⟩) hE) ?_
  change (visitProj (m := PureM) (n + 3) `PProd 0 (xv k)).runPure _ _ _ _ = _
  rw [visitProj]
  apply bind_ok rfl
  apply bind_ok (register_found (iv := PProd_ind) hPP)
  apply bind_ok rfl
  refine bind_ok (a := .fvar (xf k)) (st' := st) (ps' := ps) (fvar_run (n := n + 2) hEx) ?_
  simp only [toArray_toSubarray]
  rfl

/-- `x.1 a` in the second alternative of `Nat.add._f`'s match, `x` and `a` the locals 23 and 21. -/
def recCall : Expr := .app (.proj `PProd 0 (xv 23)) (xv 21)

theorem withApp_recCall {γ : Sort _} (k : Expr → Array Expr → γ) :
    recCall.withApp k = k (.proj `PProd 0 (xv 23)) #[xv 21] := by krfl

/-- `visitExpr` on the recursive call `x.1 a`, `PProd` registered: the projection of the table
applied to the first argument. Reference: the `tApp` case of `erase`
(`MR E/ErasureFunction.v:1006`). -/
theorem recCall_run {n : Nat} {L : LocalContext} {ls : List Local}
    {F : Option (Std.HashMap Name FVarId)}
    (hE : Pure.isErasable ⟨D⟩ oracleFuel ls recCall = .ok false)
    (hE1 : Pure.isErasable ⟨D⟩ oracleFuel ls (.proj `PProd 0 (xv 23)) = .ok false)
    (hE2 : Pure.isErasable ⟨D⟩ oracleFuel ls (xv 23) = .ok false)
    (hE3 : Pure.isErasable ⟨D⟩ oracleFuel ls (xv 21) = .ok false)
    (hPP : st.inductives[`PProd]? = some (iidPP, masksPP)) :
    (visitExpr (m := PureM) (n + 7) recCall).runPure st ⟨L, ls, F, cfg, dc⟩ pc ps =
      .ok ((.app (.proj projPP (.fvar (xf 23))) (.fvar (xf 21)), st), ps) := by
  rw [recCall, visitExpr, ← recCall]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ps)
    (erasable_step (pc := pc) (tc := ⟨L, ls, F, cfg, dc⟩) hE) ?_
  rw [visitApp]
  change (recCall.withApp fun f args => do
    visitAppArgs (m := PureM) (n + 5) (← visitExpr (m := PureM) (n + 5) f) args).runPure _ _ _ _ = _
  rw [withApp_recCall]
  refine bind_ok (projX_run (n := n + 1) hE1 hE2 hPP) ?_
  refine appArgs_cons (as := []) (fvar_run (n := n + 3) hE3) ?_
  exact appArgs_nil

/-- `Nat.add._f`'s body. -/
def fB : Expr :=
  .app (.app (.app (.app (.app (.app (.const `Nat.add.match_1 [l1]) motF) (xv 12)) (xv 10)) h1F) h2F)
    (xv 11)

theorem withApp_fB {γ : Sort _} (k : Expr → Array Expr → γ) :
    fB.withApp k = k (.const `Nat.add.match_1 [l1]) #[motF, xv 12, xv 10, h1F, h2F, xv 11] := by
  krfl

/-- The erasures of the alternatives. -/
def h1L : LBTerm :=
  .lambda (binderNameOf `a) (_root_.abstract (xf 19)
    (.lambda (binderNameOf x61) (_root_.abstract (xf 20) (.fvar (xf 19)))))
def h2L : LBTerm :=
  .lambda (binderNameOf `a) (_root_.abstract (xf 21)
    (.lambda (binderNameOf `b) (_root_.abstract (xf 22)
      (.lambda (binderNameOf x61) (_root_.abstract (xf 23)
        (.app (.construct iidN 1 []) (.app (.proj projPP (.fvar (xf 23))) (.fvar (xf 21)))))))))

/-- The erasure of `Nat.add._f`'s body. -/
def fBL : LBTerm :=
  .app (.app (.app (.app (.app (.app (.const (toKername `Nat.add.match_1)) .box) (.fvar (xf 12)))
    (.fvar (xf 10))) h1L) h2L) (.fvar (xf 11))

/-- The inductives `PProd`, `Nat` and `PUnit`, registered. -/
structure Reg (st : ErasureState) : Prop where
  pp : st.inductives[`PProd]? = some (iidPP, masksPP)
  n : st.inductives[`Nat]? = some (iidN, masksN)

/-- `visitExpr` on `Nat.add._f`'s body `Nat.add.match_1 motive x y (fun a _ => a)
(fun a b x => Nat.succ (x.1 a)) f`, `Nat.add.match_1` not erased, `PProd` and `Nat` registered:
the λ□ constant of `Nat.add.match_1`, erased on the way, applied to □ and the erased arguments.
Reference: the `tConst` and `tApp` cases of `erase` (`MR E/ErasureFunction.v:999`, `:1006`). -/
theorem fB_run {n : Nat} {L : LocalContext}
    (hm : st.constants[`Nat.add.match_1]? = none) (hR : Reg st) :
    (visitExpr (m := PureM) (n + 42) fB).runPure st ⟨L, lsF, none, cfg, dc⟩ pc ⟨13⟩ =
      .ok ((fBL, stMt st), ⟨24⟩) := by
  have hR' : Reg (stMt st) := ⟨by astfact; exact hR.pp, by astfact; exact hR.n⟩
  rw [fB, visitExpr, ← fB]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ⟨13⟩) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 40) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_fB]
  refine bind_ok (a := none) (st' := st) (ps' := ⟨13⟩) (by krfl) ?_
  refine bind_ok (a := none) (st' := st) (ps' := ⟨13⟩) (by krfl) ?_
  refine bind_ok (a := some (.defnInfo match_def)) (st' := st) (ps' := ⟨13⟩) (by krfl) ?_
  refine bind_ok (a := .const (toKername `Nat.add.match_1)) (st' := stMt st) (ps' := ⟨19⟩) ?_ ?_
  · rw [visitConst]
    apply bind_ok rfl
    refine bind_ok (kername_match (n := n) hm hR.n) ?_
    rfl
  refine appArgs_cons (as := [xv 12, xv 10, h1F, h2F, xv 11]) (r := .box) (st' := stMt st)
    (ps' := ⟨19⟩) (by krfl) ?_
  refine appArgs_cons (as := [xv 10, h1F, h2F, xv 11]) (r := .fvar (xf 12)) (st' := stMt st)
    (ps' := ⟨19⟩) (by krfl) ?_
  refine appArgs_cons (as := [h1F, h2F, xv 11]) (r := .fvar (xf 10)) (st' := stMt st)
    (ps' := ⟨19⟩) (by krfl) ?_
  refine appArgs_cons (as := [h2F, xv 11]) (r := h1L) (st' := stMt st) (ps' := ⟨21⟩)
    (lam_run (by krfl) fun _ => lam_run (by krfl) fun _ => by krfl) ?_
  refine appArgs_cons (as := [xv 11]) (r := h2L) (st' := stMt st) (ps' := ⟨24⟩)
    (lam_run (by krfl) fun _ => lam_run (by krfl) fun _ => lam_run (by krfl) fun _ =>
      sArg_run (n := n + 20) (by krfl) (by krfl)
        (recCall_run (n := n + 20) (by krfl) (by krfl) (by krfl) (by krfl) hR'.pp) hR'.n) ?_
  refine appArgs_cons (as := []) (r := .fvar (xf 11)) (st' := stMt st) (ps' := ⟨24⟩) (by krfl) ?_
  exact appArgs_nil

/-- The erasure of `Nat.add._f`'s value. -/
def fVL : LBTerm :=
  .lambda (binderNameOf x14) (_root_.abstract (xf 10) (.lambda (binderNameOf `f)
    (_root_.abstract (xf 11) (.lambda (binderNameOf x13) (_root_.abstract (xf 12) fBL)))))

/-- `visitExpr` on `Nat.add._f`'s value, from the counter's eleventh variable. Reference: the
`tLambda` case of `erase` (`MR E/ErasureFunction.v:1003`). -/
theorem fV_run {n : Nat} {L : LocalContext}
    (hm : st.constants[`Nat.add.match_1]? = none) (hR : Reg st) :
    (visitExpr (m := PureM) (n + 48) fVal).runPure st ⟨L, lsA, none, cfg, dc⟩ pc ⟨10⟩ =
      .ok ((fVL, stMt st), ⟨24⟩) :=
  lam_run (by krfl) fun _ => lam_run (by krfl) fun _ => lam_run (by krfl) fun _ =>
    fB_run (n := n) hm hR

/-- The state after `Nat.add._f`. -/
abbrev stF (st : ErasureState) : ErasureState := stDef (stMt st) `Nat.add._f fVL

/-- `visitMutual` on `Nat.add._f`. Reference: as `visitMutual_go`. -/
theorem visitMutual_f {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)}
    (hm : st.constants[`Nat.add.match_1]? = none) (hR : Reg st) :
    (visitMutual (m := PureM) (n + 49) `Nat.add._f).runPure st ⟨L, lsA, F, cfg, dc⟩ pc ⟨10⟩ =
      .ok (((), stF st), ⟨24⟩) := by
  rw [visitMutual]
  iterate 8 apply bind_ok rfl
  refine bind_ok (a := fVL) (st' := stMt st) (ps' := ⟨24⟩) ?_ ?_
  · rw [runPure_withReader]
    apply bind_ok rfl
    refine bind_ok (a := fVal) (st' := st) (ps' := ⟨10⟩) rfl ?_
    exact fV_run (n := n) hm hR
  rfl

/-- `get_constant_kername` on `Nat.add._f`, not yet erased. Reference: `erase_global_deps`
(`MR E/ErasureFunction.v:1602`). -/
theorem kername_f {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)}
    (hf : st.constants[`Nat.add._f]? = none) (hm : st.constants[`Nat.add.match_1]? = none)
    (hR : Reg st) :
    (get_constant_kername (m := PureM) (n + 50) `Nat.add._f).runPure st ⟨L, lsA, F, cfg, dc⟩ pc
      ⟨10⟩ = .ok ((toKername `Nat.add._f, stF st), ⟨24⟩) := by
  rw [get_constant_kername]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, hf]
  apply bind_ok (visitMutual_f hm hR)
  apply bind_ok rfl
  simp only [stF, stDef, Std.HashMap.getElem?_insert_self]
  rfl


/-! ## `Nat.add` -/

/-- `Nat.add`'s body. -/
def aB : Expr :=
  .app (.app (.app (.app (.const `Nat.brecOn [l1]) motA) (xv 1)) (.const `Nat.add._f [])) (xv 0)

theorem withApp_aB {γ : Sort _} (k : Expr → Array Expr → γ) :
    aB.withApp k = k (.const `Nat.brecOn [l1]) #[motA, xv 1, .const `Nat.add._f [], xv 0] := by
  krfl

/-- `visitExpr` on the constant `Nat.add._f` as an argument, not yet erased. Reference: the
`tConst` case of `erase` (`MR E/ErasureFunction.v:999`). -/
theorem fC_run {n : Nat} {L : LocalContext} (hf : st.constants[`Nat.add._f]? = none)
    (hm : st.constants[`Nat.add.match_1]? = none) (hR : Reg st) :
    (visitExpr (m := PureM) (n + 54) (.const `Nat.add._f [])).runPure st ⟨L, lsA, none, cfg, dc⟩ pc
      ⟨10⟩ = .ok ((.const (toKername `Nat.add._f), stF st), ⟨24⟩) := by
  rw [visitExpr]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ⟨10⟩) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 52) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_const]
  refine bind_ok (a := none) (st' := st) (ps' := ⟨10⟩) (by krfl) ?_
  refine bind_ok (a := none) (st' := st) (ps' := ⟨10⟩) (by krfl) ?_
  refine bind_ok (a := some (.defnInfo add_f)) (st' := st) (ps' := ⟨10⟩) (by krfl) ?_
  refine bind_ok (a := .const (toKername `Nat.add._f)) (st' := stF st) (ps' := ⟨24⟩) ?_ ?_
  · rw [visitConst]
    apply bind_ok rfl
    refine bind_ok (kername_f (n := n) hf hm hR) ?_
    rfl
  exact appArgs_nil

/-- The state after `Nat.add`'s body, from the empty state. -/
abbrev stAB : ErasureState := stF (stBr {})

/-- The erasure of `Nat.add`'s body. -/
def aBL : LBTerm :=
  .app (.app (.app (.app (.const (toKername `Nat.brecOn)) .box) (.fvar (xf 1)))
    (.const (toKername `Nat.add._f))) (.fvar (xf 0))

/-- `visitExpr` on `Nat.add`'s body `Nat.brecOn (fun y => Nat → Nat) y Nat.add._f x` from the empty
state: the λ□ constants of `Nat.brecOn` (erased with `Nat.brecOn.go`, registering `PProd`, `Nat` and
`PUnit`) and of `Nat.add._f` (erased with `Nat.add.match_1`). Reference: the `tConst` and `tApp`
cases of `erase` (`MR E/ErasureFunction.v:999`, `:1006`). -/
theorem aB_run {n : Nat} {L : LocalContext} :
    (visitExpr (m := PureM) (n + 60) aB).runPure {} ⟨L, lsA, none, cfg, dc⟩ pc ⟨2⟩ =
      .ok ((aBL, stAB), ⟨24⟩) := by
  have hR : Reg (stBr {}) := ⟨by astfact, by astfact⟩
  rw [aB, visitExpr, ← aB]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := {}) (ps' := ⟨2⟩) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 58) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_aB]
  refine bind_ok (a := none) (st' := {}) (ps' := ⟨2⟩) (by krfl) ?_
  refine bind_ok (a := none) (st' := {}) (ps' := ⟨2⟩) (by krfl) ?_
  refine bind_ok (a := some (.defnInfo Nat_brecOn)) (st' := {}) (ps' := ⟨2⟩) (by krfl) ?_
  refine bind_ok (a := .const (toKername `Nat.brecOn)) (st' := stBr {}) (ps' := ⟨10⟩) ?_ ?_
  · rw [visitConst]
    apply bind_ok rfl
    refine bind_ok (kername_brecOn (n := n + 2) Std.HashMap.getElem?_empty Std.HashMap.getElem?_empty
      Std.HashMap.getElem?_empty Std.HashMap.getElem?_empty Std.HashMap.getElem?_empty) ?_
    rfl
  refine appArgs_cons (as := [xv 1, .const `Nat.add._f [], xv 0]) (r := .box) (st' := stBr {})
    (ps' := ⟨10⟩) (by krfl) ?_
  refine appArgs_cons (as := [.const `Nat.add._f [], xv 0]) (r := .fvar (xf 1)) (st' := stBr {})
    (ps' := ⟨10⟩) (by krfl) ?_
  refine appArgs_cons (as := [xv 0]) (fC_run (n := n + 2) (by astfact) (by astfact) hR) ?_
  refine appArgs_cons (as := []) (r := .fvar (xf 0)) (st' := stAB) (ps' := ⟨24⟩) (by krfl) ?_
  exact appArgs_nil

/-- The erasure of `Nat.add`'s value. -/
def addVL : LBTerm :=
  .lambda (binderNameOf x13) (_root_.abstract (xf 0) (.lambda (binderNameOf x14)
    (_root_.abstract (xf 1) aBL)))

/-- `visitExpr` on `Nat.add`'s value from the empty state. Reference: the `tLambda` case of `erase`
(`MR E/ErasureFunction.v:1003`). -/
theorem addV_run {n : Nat} {L : LocalContext} :
    (visitExpr (m := PureM) (n + 64) addVal).runPure {} ⟨L, [], none, cfg, dc⟩ pc ⟨0⟩ =
      .ok ((addVL, stAB), ⟨24⟩) :=
  lam_run (by krfl) fun _ => lam_run (by krfl) fun _ => aB_run (n := n)

/-- The state after `Nat.add`. -/
abbrev stAdd : ErasureState := stDef stAB `Nat.add addVL

/-- `visitMutual` on `Nat.add`: an `@[extern]` definition, which `extern := .preferLogical` erases
by its value. Reference: as `visitMutual_go`; the `@[extern]` test: none (DV-12). -/
theorem visitMutual_add {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)} :
    (visitMutual (m := PureM) (n + 65) `Nat.add).runPure {} ⟨L, [], F, cfg, dc⟩ pc ⟨0⟩ =
      .ok (((), stAdd), ⟨24⟩) := by
  rw [visitMutual]
  iterate 7 apply bind_ok rfl
  simp only [show pc.view.isExtern `Nat.add = true from rfl,
    show (ConstantInfo.defnInfo add_def).value? true = some addVal from rfl,
    show cfg.1 = .preferLogical from rfl]
  apply bind_ok rfl
  have hnr : ((ConstantInfo.defnInfo add_def).all.length == 1 &&
      !name_occurs (m := PureM) `Nat.add ((some addVal).getD default)) = true := rfl
  simp only [hnr, ↓reduceIte]
  apply bind_ok rfl
  refine bind_ok (a := addVL) (st' := stAB) (ps' := ⟨24⟩) ?_ ?_
  · rw [runPure_withReader]
    apply bind_ok rfl
    refine bind_ok (a := addVal) (st' := {}) (ps' := ⟨0⟩) rfl ?_
    exact addV_run (n := n)
  rfl


/-- `get_constant_kername` on `Nat.add` from the empty state. Reference: `erase_global_deps`
(`MR E/ErasureFunction.v:1602`). -/
theorem kername_add {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)} :
    (get_constant_kername (m := PureM) (n + 66) `Nat.add).runPure {} ⟨L, [], F, cfg, dc⟩ pc ⟨0⟩ =
      .ok ((toKername `Nat.add, stAdd), ⟨24⟩) := by
  rw [get_constant_kername]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty]
  apply bind_ok visitMutual_add
  apply bind_ok rfl
  simp only [stAdd, stDef, Std.HashMap.getElem?_insert_self]
  rfl

/-! ## The literals -/

/-- `visitExpr` on the literal `0` outside any binder, `Nat` registered: `visitLiteral` erases it as
`Nat.zero`. Reference: none (Lean's literals; `Erases.litZero`). -/
theorem lit0_run {n : Nat} {L : LocalContext} (h : st.inductives[`Nat]? = some (iidN, masksN)) :
    (visitExpr (m := PureM) (n + 4) (lit 0)).runPure st ⟨L, [], none, cfg, dc⟩ pc ps =
      .ok ((natL 0, st), ps) := by
  rw [lit, visitExpr]
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
  apply bind_ok (register_found h)
  simp only [toArray_toSubarray]
  krfl

/-- `visitExpr` on the literal `k + 1` outside any binder, `Nat` registered: `visitLiteral` erases
it as `Nat.succ` applied to the literal `k`. Reference: none (Lean's literals; `Erases.litSucc`). -/
theorem litS_run {n k : Nat} {L : LocalContext} (hk : k + 1 ≤ peanoMaxLiteral)
    (h : st.inductives[`Nat]? = some (iidN, masksN))
    (ih : (visitExpr (m := PureM) (n + 1) (lit k)).runPure st ⟨L, [], none, cfg, dc⟩ pc ps =
      .ok ((natL k, st), ps)) :
    (visitExpr (m := PureM) (n + 5) (lit (k + 1))).runPure st ⟨L, [], none, cfg, dc⟩ pc ps =
      .ok ((natL (k + 1), st), ps) := by
  rw [lit, visitExpr]
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
  apply bind_ok (register_found h)
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

/-- `visitExpr` on the literals `2` and `3`, `Nat` registered. -/
theorem lit2_run {n : Nat} {L : LocalContext} (h : st.inductives[`Nat]? = some (iidN, masksN)) :
    (visitExpr (m := PureM) (n + 12) (lit 2)).runPure st ⟨L, [], none, cfg, dc⟩ pc ps =
      .ok ((natL 2, st), ps) :=
  litS_run (n := n + 7) (by decide) h (litS_run (n := n + 3) (by decide) h (lit0_run h))

theorem lit3_run {n : Nat} {L : LocalContext} (h : st.inductives[`Nat]? = some (iidN, masksN)) :
    (visitExpr (m := PureM) (n + 16) (lit 3)).runPure st ⟨L, [], none, cfg, dc⟩ pc ps =
      .ok ((natL 3, st), ps) :=
  litS_run (n := n + 11) (by decide) h (lit2_run h)


/-! ## `OfNat.ofNat` and `instOfNatNat` -/

/-- The λ□ projection of `OfNat`'s field. -/
def projOf : ProjectionInfo := { indType := iidOf, paramCount := 2, fieldIdx := 0 }

/-- The locals of `OfNat.ofNat`'s body: `α`, `x`, `self`. -/
def lsO : List Local :=
  [loc 26 `self (.app (.app (tOf lv) (xv 24)) (xv 25)), loc 25 xo tN, loc 24 `α tyU]

/-- `visitExpr` on `OfNat.ofNat`'s body `self.1`, `OfNat` not registered: the projection registers
it. Reference: the `tProj` case of `erase` (`MR E/ErasureFunction.v:1020`). -/
theorem projOf_run {n : Nat} {L : LocalContext} (h : st.inductives[`OfNat]? = none) :
    (visitExpr (m := PureM) (n + 4) (.proj `OfNat 0 (xv 26))).runPure st ⟨L, lsO, none, cfg, dc⟩ pc
      ps = .ok ((.proj projOf (.fvar (xf 26)), stOf st), ps) := by
  rw [visitExpr]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ps) (by krfl) ?_
  change (visitProj (m := PureM) (n + 3) `OfNat 0 (xv 26)).runPure _ _ _ _ = _
  rw [visitProj]
  apply bind_ok rfl
  apply bind_ok (register_Of_new h)
  apply bind_ok rfl
  refine bind_ok (a := .fvar (xf 26)) (st' := stOf st) (ps' := ps) (fvar_run (n := n + 2) (by krfl)) ?_
  simp only [toArray_toSubarray]
  rfl

/-- The erasure of `OfNat.ofNat`'s value. -/
def ofNatVL : LBTerm :=
  .lambda (binderNameOf `α) (_root_.abstract (xf 24) (.lambda (binderNameOf xo)
    (_root_.abstract (xf 25) (.lambda (binderNameOf `self) (_root_.abstract (xf 26)
      (.proj projOf (.fvar (xf 26))))))))

/-- The state after `OfNat.ofNat`. -/
abbrev stON (st : ErasureState) : ErasureState := stDef (stOf st) `OfNat.ofNat ofNatVL

/-- `visitMutual` on `OfNat.ofNat`. Reference: as `visitMutual_go`. -/
theorem visitMutual_ofNat {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)}
    (h : st.inductives[`OfNat]? = none) :
    (visitMutual (m := PureM) (n + 19) `OfNat.ofNat).runPure st ⟨L, [], F, cfg, dc⟩ pc ⟨24⟩ =
      .ok (((), stON st), ⟨27⟩) := by
  rw [visitMutual]
  iterate 8 apply bind_ok rfl
  refine bind_ok (a := ofNatVL) (st' := stOf st) (ps' := ⟨27⟩) ?_ ?_
  · rw [runPure_withReader]
    apply bind_ok rfl
    refine bind_ok (a := ofNatVal) (st' := st) (ps' := ⟨24⟩) rfl ?_
    exact lam_run (by krfl) fun _ => lam_run (by krfl) fun _ => lam_run (by krfl) fun _ =>
      projOf_run (n := n + 8) h
  rfl

/-- `get_constant_kername` on `OfNat.ofNat`, not yet erased. Reference: `erase_global_deps`
(`MR E/ErasureFunction.v:1602`). -/
theorem kername_ofNat {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)}
    (hc : st.constants[`OfNat.ofNat]? = none) (h : st.inductives[`OfNat]? = none) :
    (get_constant_kername (m := PureM) (n + 20) `OfNat.ofNat).runPure st ⟨L, [], F, cfg, dc⟩ pc
      ⟨24⟩ = .ok ((toKername `OfNat.ofNat, stON st), ⟨27⟩) := by
  rw [get_constant_kername]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, hc]
  apply bind_ok (visitMutual_ofNat h)
  apply bind_ok rfl
  simp only [stON, stDef, Std.HashMap.getElem?_insert_self]
  rfl

/-- `instOfNatNat`'s body `OfNat.mk Nat n n` under its local `n`. -/
def mkB : Expr := .app (.app (.app (cOf .zero) tN) (xv 27)) (xv 27)

theorem withApp_mkB {γ : Sort _} (k : Expr → Array Expr → γ) :
    mkB.withApp k = k (cOf .zero) #[tN, xv 27, xv 27] := by krfl

/-- The arguments `visitConstructor` passes on for `OfNat.mk α x a`: the parameters and the field. -/
theorem args_Of (a b c : Expr) : #[a, b, c].extract 0 2 ++
    filter #[ConstructorArgRelevance.keep] (↑(#[a, b, c].toSubarray 2 (2 + 1)) : Array Expr) ++
      #[a, b, c].extract (2 + 1) = #[a, b, c] := by
  apply Array.toList_inj.mp
  simp [filter, toArray_toSubarray]

/-- The erasure of `instOfNatNat`'s body. -/
def mkBL : LBTerm := .app (.app (.app (.construct iidOf 0 []) .box) (.fvar (xf 27))) (.fvar (xf 27))

/-- `visitExpr` on `OfNat.mk Nat n n`, `OfNat` registered: the type parameter is erased.
Reference: the `tConstruct` case of `erase` (`MR E/ErasureFunction.v:1014`). -/
theorem mkB_run {n : Nat} {L : LocalContext} (h : st.inductives[`OfNat]? = some (iidOf, masksOf)) :
    (visitExpr (m := PureM) (n + 12) mkB).runPure st ⟨L, [loc 27 `n tN], none, cfg, dc⟩ pc ps =
      .ok ((mkBL, st), ps) := by
  rw [mkB, visitExpr, ← mkB]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ps) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 10) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_mkB]
  refine bind_ok (a := none) (st' := st) (ps' := ps) (by krfl) ?_
  refine bind_ok (a := some 3) (st' := st) (ps' := ps) (by krfl) ?_
  change (withAppEtaToMinArity (m := PureM) (n + 9) _ 3 _).runPure _ _ _ _ = _
  rw [withAppEtaToMinArity]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := .app (.app (tOf .zero) tN) (xv 27)) (st' := st) (ps' := ps) (by krfl) ?_
  rw [withApp_mkB, withAppEtaToMinArity.go]
  rw [visitConstructor]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok (register_found (iv := OfNat_ind) h)
  dsimp only
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  simp only
  apply bind_ok rfl
  simp only [toArray_toSubarray, show OfNat_mk.numParams = 2 from rfl,
    show OfNat_mk.numFields = 1 from rfl, show OfNat_mk.cidx = 0 from rfl]
  rw [args_Of]
  refine (congrArg (fun x : EraseT PureM LBTerm =>
      x.runPure st ⟨L, [loc 27 `n tN], none, cfg, dc⟩ pc ps)
    (?_ : _ = visitAppArgs (m := PureM) (n + 8) (.construct iidOf 0 []) #[tN, xv 27, xv 27])).trans ?_
  · krfl
  refine appArgs_cons (as := [xv 27, xv 27]) (r := .box) (st' := st) (ps' := ps) (by krfl) ?_
  refine appArgs_cons (as := [xv 27]) (fvar_run (n := n + 6) (by krfl)) ?_
  refine appArgs_cons (as := []) (fvar_run (n := n + 6) (by krfl)) ?_
  exact appArgs_nil

/-- The erasure of `instOfNatNat`'s value. -/
def instVL : LBTerm := .lambda (binderNameOf `n) (_root_.abstract (xf 27) mkBL)

/-- The state after `instOfNatNat`. -/
abbrev stIn (st : ErasureState) : ErasureState := stDef st `instOfNatNat instVL

/-- `visitMutual` on `instOfNatNat`. Reference: as `visitMutual_go`. -/
theorem visitMutual_inst {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)}
    (h : st.inductives[`OfNat]? = some (iidOf, masksOf)) :
    (visitMutual (m := PureM) (n + 15) `instOfNatNat).runPure st ⟨L, [], F, cfg, dc⟩ pc ⟨27⟩ =
      .ok (((), stIn st), ⟨28⟩) := by
  rw [visitMutual]
  iterate 8 apply bind_ok rfl
  refine bind_ok (a := instVL) (st' := st) (ps' := ⟨28⟩) ?_ ?_
  · rw [runPure_withReader]
    apply bind_ok rfl
    refine bind_ok (a := instVal) (st' := st) (ps' := ⟨27⟩) rfl ?_
    exact lam_run (by krfl) fun _ => mkB_run (n := n) h
  rfl

/-- `get_constant_kername` on `instOfNatNat`, not yet erased. Reference: `erase_global_deps`
(`MR E/ErasureFunction.v:1602`). -/
theorem kername_inst {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)}
    (hc : st.constants[`instOfNatNat]? = none) (h : st.inductives[`OfNat]? = some (iidOf, masksOf)) :
    (get_constant_kername (m := PureM) (n + 16) `instOfNatNat).runPure st ⟨L, [], F, cfg, dc⟩ pc
      ⟨27⟩ = .ok ((toKername `instOfNatNat, stIn st), ⟨28⟩) := by
  rw [get_constant_kername]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, hc]
  apply bind_ok (visitMutual_inst h)
  apply bind_ok rfl
  simp only [stIn, stDef, Std.HashMap.getElem?_insert_self]
  rfl

/-! ## The numerals and the term -/


theorem withApp_instK {γ : Sort _} (k : Nat) (f : Expr → Array Expr → γ) :
    (instK k).withApp f = f (.const `instOfNatNat []) #[lit k] := withApp_app1 _ _ f rfl

theorem withApp_numK {γ : Sort _} (k : Nat) (f : Expr → Array Expr → γ) :
    (numK k).withApp f = f (.const `OfNat.ofNat [.zero]) #[tNb, lit k, instK k] := by
  krfl

/-- `visitExpr` on `instOfNatNat k` outside any binder, with the step `hk` on `instOfNatNat` and
the literal's erasure `hl`. Reference: the `tConst` and `tApp` cases of `erase`
(`MR E/ErasureFunction.v:999`, `:1006`). -/
theorem instK_run {n k : Nat} {L : LocalContext} {st' : ErasureState} {ps' : PureState}
    {t : LBTerm}
    (hk : (get_constant_kername (m := PureM) (n + 16) `instOfNatNat).runPure st
      ⟨L, [], none, cfg, dc⟩ pc ps = .ok ((toKername `instOfNatNat, st'), ps'))
    (hl : (visitExpr (m := PureM) (n + 16) (lit k)).runPure st' ⟨L, [], none, cfg, dc⟩ pc ps' =
      .ok ((t, st'), ps')) :
    (visitExpr (m := PureM) (n + 20) (instK k)).runPure st ⟨L, [], none, cfg, dc⟩ pc ps =
      .ok ((.app (.const (toKername `instOfNatNat)) t, st'), ps') := by
  rw [instK, visitExpr, ← instK]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ps) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 18) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_instK]
  refine bind_ok (a := none) (st' := st) (ps' := ps) (by krfl) ?_
  refine bind_ok (a := none) (st' := st) (ps' := ps) (by krfl) ?_
  refine bind_ok (a := some (.defnInfo inst_def)) (st' := st) (ps' := ps) (by krfl) ?_
  refine bind_ok (a := .const (toKername `instOfNatNat)) (st' := st') (ps' := ps') ?_ ?_
  · rw [visitConst]
    apply bind_ok rfl
    refine bind_ok hk ?_
    rfl
  refine appArgs_cons (as := []) hl ?_
  exact appArgs_nil

/-- `visitExpr` on the numeral `numK k` outside any binder, with the step `ho` on `OfNat.ofNat`, the
literal's erasure `hl` and the instance's `hi`. Reference: the `tConst` and `tApp` cases of `erase`
(`MR E/ErasureFunction.v:999`, `:1006`). -/
theorem numK_run {n k : Nat} {L : LocalContext} {st₁ st₂ : ErasureState} {ps₁ ps₂ : PureState}
    {t i : LBTerm}
    (ho : (get_constant_kername (m := PureM) (n + 20) `OfNat.ofNat).runPure st
      ⟨L, [], none, cfg, dc⟩ pc ps = .ok ((toKername `OfNat.ofNat, st₁), ps₁))
    (hl : (visitExpr (m := PureM) (n + 20) (lit k)).runPure st₁ ⟨L, [], none, cfg, dc⟩ pc ps₁ =
      .ok ((t, st₁), ps₁))
    (hi : (visitExpr (m := PureM) (n + 20) (instK k)).runPure st₁ ⟨L, [], none, cfg, dc⟩ pc ps₁ =
      .ok ((i, st₂), ps₂)) :
    (visitExpr (m := PureM) (n + 24) (numK k)).runPure st ⟨L, [], none, cfg, dc⟩ pc ps =
      .ok ((.app (.app (.app (.const (toKername `OfNat.ofNat)) .box) t) i, st₂), ps₂) := by
  rw [numK, visitExpr, ← numK]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ps) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 22) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_numK]
  refine bind_ok (a := none) (st' := st) (ps' := ps) (by krfl) ?_
  refine bind_ok (a := none) (st' := st) (ps' := ps) (by krfl) ?_
  refine bind_ok (a := some (.defnInfo ofNat_def)) (st' := st) (ps' := ps) (by krfl) ?_
  refine bind_ok (a := .const (toKername `OfNat.ofNat)) (st' := st₁) (ps' := ps₁) ?_ ?_
  · rw [visitConst]
    apply bind_ok rfl
    refine bind_ok ho ?_
    rfl
  refine appArgs_cons (as := [lit k, instK k]) (r := .box) (st' := st₁) (ps' := ps₁) (by krfl) ?_
  refine appArgs_cons (as := [instK k]) hl ?_
  refine appArgs_cons (as := []) hi ?_
  exact appArgs_nil

/-- The erasure of the numeral `k`, the instance and its literal at the erasure of `k`. -/
def numL (k : Nat) : LBTerm :=
  .app (.app (.app (.const (toKername `OfNat.ofNat)) .box) (natL k))
    (.app (.const (toKername `instOfNatNat)) (natL k))

/-- The erasure of `e`. -/
def eL : LBTerm := .app (.app (.const (toKername `Nat.add)) (numL 2)) (numL 3)

/-- The state at the end of the run. -/
abbrev stE : ErasureState := stIn (stON stAdd)

/-- Facts about the traversal's maps in the states of the run's end. -/
macro (name := _stfactE) "stfactE" : tactic =>
  `(tactic| (simp only [stE, stIn, stON, stAdd, stAB, stF]; astfact))

theorem withApp_e {γ : Sort _} (k : Expr → Array Expr → γ) :
    e.withApp k = k (.const `Nat.add []) #[numK 2, numK 3] := by krfl

/-- `visitExpr` on `e = Nat.add 2 3`: the λ□ constant of `Nat.add`, erased on the way with its
dependencies, applied to the erased numerals, the first of which erases `OfNat.ofNat` and
`instOfNatNat`. Reference: the `tConst` and `tApp` cases of `erase`
(`MR E/ErasureFunction.v:999`, `:1006`), with `erase_global_deps` (`MR E/ErasureFunction.v:1602`). -/
theorem e_run {n : Nat} {L : LocalContext} :
    (visitExpr (m := PureM) (n + 80) e).runPure {} ⟨L, [], none, cfg, .anonymous⟩ pc ⟨0⟩ =
      .ok ((eL, stE), ⟨28⟩) := by
  have hN1 : (stAdd).inductives[`Nat]? = some (iidN, masksN) := by stfactE
  have hN2 : (stON stAdd).inductives[`Nat]? = some (iidN, masksN) := by stfactE
  have hN3 : stE.inductives[`Nat]? = some (iidN, masksN) := by stfactE
  rw [e, visitExpr, ← e]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := {}) (ps' := ⟨0⟩) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 78) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_e]
  refine bind_ok (a := none) (st' := {}) (ps' := ⟨0⟩) (by krfl) ?_
  refine bind_ok (a := none) (st' := {}) (ps' := ⟨0⟩) (by krfl) ?_
  refine bind_ok (a := some (.defnInfo add_def)) (st' := {}) (ps' := ⟨0⟩) (by krfl) ?_
  refine bind_ok (a := .const (toKername `Nat.add)) (st' := stAdd) (ps' := ⟨24⟩) ?_ ?_
  · rw [visitConst]
    apply bind_ok rfl
    refine bind_ok (kername_add (n := n + 10)) ?_
    rfl
  refine appArgs_cons (as := [numK 3])
    (numK_run (n := n + 52) (kername_ofNat (n := n + 52) (by stfactE) (by stfactE))
      (lit2_run (n := n + 60) hN2)
      (instK_run (n := n + 52) (kername_inst (n := n + 52) (by stfactE)
        (by stfactE)) (lit2_run (n := n + 56) hN3))) ?_
  refine appArgs_cons (as := [])
    (numK_run (n := n + 52) (kername_found (n := n + 71) (by stfactE))
      (lit3_run (n := n + 56) hN3)
      (instK_run (n := n + 52) (kername_found (n := n + 67) (by stfactE))
        (lit3_run (n := n + 52) hN3))) ?_
  exact appArgs_nil


/-! ## The run on NV-A -/

/-- The program `#erase` emits for NV-A. -/
def p0 : Program :=
  .untyped [(toKername `instOfNatNat, .constantDecl ⟨some instVL⟩),
    (toKername `OfNat.ofNat, .constantDecl ⟨some ofNatVL⟩),
    (mutualBlockKername [`OfNat], .inductiveDecl ⟨.finite, 2, [bodyOf]⟩),
    (toKername `Nat.add, .constantDecl ⟨some addVL⟩),
    (toKername `Nat.add._f, .constantDecl ⟨some fVL⟩),
    (toKername `Nat.add.match_1, .constantDecl ⟨some matchVL⟩),
    (toKername `Nat.brecOn, .constantDecl ⟨some brecOnVL⟩),
    (toKername `Nat.brecOn.go, .constantDecl ⟨some goVL⟩),
    (mutualBlockKername [`PUnit], .inductiveDecl ⟨.finite, 0, [bodyPU]⟩),
    (mutualBlockKername [`Nat], .inductiveDecl ⟨.finite, 0, [bodyN]⟩),
    (mutualBlockKername [`PProd], .inductiveDecl ⟨.finite, 2, [bodyPP]⟩)] (some eL)

/-- The pure path on NV-A's closure returns `p0` and no constant to inline. Reference: `erase`
(`MR E/ErasureFunction.v:989`) and `erase_global_deps` (`MR E/ErasureFunction.v:1602`). -/
theorem hpure : erasePure view cfg D e = .ok (p0, []) := by
  rw [erasePure, show travFuel = (travFuel - 80) + 80 by decide]
  rw [show ((visitExpr (m := PureM) (travFuel - 80 + 80) e).runPure {} { «config» := cfg }
    ⟨D, view⟩ {}) = .ok ((eL, stE), ⟨28⟩) from e_run]
  krfl

/-- `#erase`'s entry point on NV-A returns `p0` and no constant to inline. Reference: the
hypotheses `erase … = t'` and `erase_global_deps … = Σ'` of `erase_correct`
(`MR E/ErasureFunctionProperties.v:657`). -/
theorem hrun : eraseEntry view cfg e = pure (p0, []) := by
  simp only [eraseEntry, route, hcollect, hpure]


end EraseProof.Test.NVA
