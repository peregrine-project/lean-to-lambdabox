import EraseProof.Test.NVSData
import EraseProof.Test.NVRRun

/-!
# NV-S through the entry point of `#erase`

The hypotheses `hfrag` and `hrun` of the final theorem (`MR E/ErasureFunctionProperties.v:657
erase_correct`) on NV-S (`Test/NVSData.lean`). `hcollect` computes the fragment test's closure `D`
by kernel evaluation. `hrun` is the run of the entry point, evaluated one traversal call at a time
(`Test/Run.lean`), cut at every read of the traversal's maps, with the steps on any closure of
`Tools` (`lam_run`: a λ and its body, `appArgs_cons`: the arguments of an application,
`register_found`, `kername_found`). `e` erases `add` (`kername_add`), whose body erases
`N.brecOn` with `N.brecOn.go` (`kername_brecOn`: the projection of `N.brecOn`'s value registers
`PProd`, `visitRec` on the `N.rec` of `N.brecOn.go` registers `N`, the minor premise of `N.z`
registers `PUnit`) and `add._f` with `add.match_1` and `Unit.unit` (`kername_f`: the `casesOn` of
`add.match_1` is a λ□ `case`, both `@[inline]` definitions are marked for inlining, the projection
`x.1` of the table `N.below` is a λ□ projection of `PProd`); `N.below` occurs only in types and is
not erased. The fresh locals are numbered in the order the traversal opens them: `add`'s `n m`
(0, 1), `N.brecOn`'s (2–4), `N.brecOn.go`'s (5–7) and its minor premise's (8, 9), `add._f`'s
(10–12), `add.match_1`'s (13–16) and its alternative's (17), the alternatives of `add._f` (18–21).
The locals of a body are those of its binders on top of those of the body that refers to the
definition first (`visitMutual` erases a definition under the caller's locals).
-/

open Lean Erasure EraseProof.Test

namespace EraseProof.Test.NVS

open EraseProof.Test.NVR (tN cZ cS N_ind Nz_ctor Ns_ctor N_rec motTy mj iidN masksN bodyN)

/-- The closure of `e`, in the order the fragment test returns it. -/
def D : List ConstantInfo :=
  [.defnInfo Unit_unit, .defnInfo N_casesOn, .defnInfo Unit_def, .defnInfo add_match_1,
    .defnInfo add_f, .defnInfo N_brecOn_go, .ctorInfo PProd_mk, .recInfo PProd_rec,
    .inductInfo PProd_ind, .ctorInfo PUnit_unit, .recInfo PUnit_rec, .inductInfo PUnit_ind,
    .recInfo N_rec, .defnInfo N_below, .defnInfo N_brecOn, .ctorInfo Ns_ctor, .ctorInfo Nz_ctor,
    .inductInfo N_ind, .defnInfo add_def]

/-- The fragment test accepts `e` and returns the closure `D`, by kernel evaluation. Reference: the
environment `Σ'` of `erase_global_deps` (`MR E/ErasureFunction.v:1602`). -/
theorem hcollect : collectDeps view cfg e = .ok D := rfl

/-- The pure backend's context over the closure. -/
def pc : PureCtx := ⟨D, view⟩

/-! ## The emitted program -/

/-- The λ□ inductives of `PProd` and `PUnit`. -/
def iidPP : InductiveId := ⟨mutualBlockKername [`PProd], 0⟩
def iidPU : InductiveId := ⟨mutualBlockKername [`PUnit], 0⟩

/-- The argument masks of `PProd.mk` (both fields kept) and `PUnit.unit` (no field). -/
def masksPP : InductiveArgMasks := [#[.keep, .keep]]
def masksPU : InductiveArgMasks := [#[]]

/-- The λ□ bodies of `PProd` (a structure: one projection per kept field) and `PUnit`. -/
def bodyPP : OneInductiveBody :=
  { name := toString `PProd, propositional := false, ctors := [⟨toString `PProd.mk, 2⟩],
    projs := [⟨"0"⟩, ⟨"1"⟩] }
def bodyPU : OneInductiveBody :=
  { name := toString `PUnit, propositional := false, ctors := [⟨toString `PUnit.unit, 0⟩],
    projs := [] }

/-- The first projection of `PProd`. -/
def projPP : ProjectionInfo := { indType := iidPP, paramCount := 2, fieldIdx := 0 }

/-- `N.z`, `N.s`, `PProd.mk`, `PUnit.unit` in λ□. -/
def zL : LBTerm := .construct iidN 0 []
def sL : LBTerm := .construct iidN 1 []
def mkL : LBTerm := .construct iidPP 0 []
def unitL : LBTerm := .construct iidPU 0 []

/-- The erasure of `e`. -/
def eL : LBTerm := .app (.app (.const (toKername `add)) NVR.mjL) NVR.mjL

/-! ## Tools: steps of the traversal on any closure -/

section Tools

variable {pc : PureCtx} {st st' : ErasureState} {ps ps' : PureState} {dc : Name}
  {c : ErasureConfig} {L : LocalContext} {ls : List Local} {F : Option (Std.HashMap Name FVarId)}

/-- The traversal's `k`-th fresh local. -/
def xf (k : Nat) : FVarId := ⟨.num `_pure k⟩
def xv (k : Nat) : Expr := .fvar (xf k)
def loc (k : Nat) (x : Name) (t : Expr) : Local := ⟨xf k, x, t, none⟩

/-- The oracle's erasability test, as the traversal runs it. Reference: none. -/
theorem erasable_step {e : Expr} {b : Bool} {tc : TravCtx}
    (hE : Pure.isErasable ⟨pc.decls⟩ oracleFuel tc.locals e = .ok b) :
    EraseT.runPure (liftM (Backend.isErasable (m := PureM) tc.lctx tc.locals e) :
      EraseT PureM Bool) st tc pc ps = .ok ((b, st), ps) := by
  simp only [EraseT.runPure, Backend.isErasable, PureM.isErasable]
  simp [liftM, monadLift, MonadLift.monadLift, StateT.lift, ReaderT.run, StateT.run, read, MonadReader.read,
    ReaderT.read, MonadReaderOf.read, bind, ReaderT.bind, StateT.bind, readThe, Except.bind, pure, ReaderT.pure, StateT.pure, Except.pure, hE]

/-- The oracle's type inference, as the traversal runs it. Reference: none. -/
theorem infer_step {e T : Expr} {tc : TravCtx}
    (hT : Pure.inferType ⟨pc.decls⟩ oracleFuel tc.locals [] e = .ok T) :
    EraseT.runPure (liftM (Backend.inferType (m := PureM) tc.lctx tc.locals e) :
      EraseT PureM Expr) st tc pc ps = .ok ((T, st), ps) := by
  simp only [EraseT.runPure, Backend.inferType]
  simp [liftM, monadLift, MonadLift.monadLift, StateT.lift, ReaderT.run, StateT.run, read, MonadReader.read,
    ReaderT.read, MonadReaderOf.read, bind, ReaderT.bind, StateT.bind, readThe, Except.bind, pure, ReaderT.pure, StateT.pure, Except.pure, hT]

/-- `visitExpr` on a λ that the oracle keeps: the λ□ λ over the erasure of its body, opened with
the next fresh local. Reference: the `tLambda` case of `erase` (`MR E/ErasureFunction.v:1003`). -/
theorem lam_run {n k : Nat} {x : Name} {t b : Expr} {bi : BinderInfo} {r : LBTerm}
    (hE : Pure.isErasable ⟨pc.decls⟩ oracleFuel ls (.lam x t b bi) = .ok false)
    (hb : ∀ L', (visitExpr (m := PureM) n (b.instantiate1' (xv k))).runPure st
      ⟨L', loc k x t :: ls, F, c, dc⟩ pc ⟨k + 1⟩ = .ok ((r, st'), ps')) :
    (visitExpr (m := PureM) (n + 2) (.lam x t b bi)).runPure st ⟨L, ls, F, c, dc⟩ pc ⟨k⟩ =
      .ok ((.lambda (binderNameOf x) (_root_.abstract (xf k) r), st'), ps') := by
  rw [visitExpr]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ⟨k⟩) (erasable_step (tc := ⟨L, ls, F, c, dc⟩) hE) ?_
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [visitLambda]
  refine bind_ok (a := xf k) (st' := st) (ps' := ⟨k + 1⟩) rfl ?_
  refine bind_ok (a := r) (st' := st') (ps' := ps') (hb _) ?_
  have h : (xf k == xf k) = true := by
    show (Name.num `_pure k).beq (Name.num `_pure k) = true
    simp [Name.beq]
  refine bind_ok (a := binderNameOf x) (st' := st') (ps' := ps') ?_ rfl
  refine bind_ok rfl ?_
  refine bind_ok (a := loc k x t) (st' := st') (ps' := ps') ?_ rfl
  rw [List.find?_cons_of_pos (by exact h)]
  rfl

/-- `visitAppArgs` on no argument. Reference: none. -/
theorem appArgs_nil {n : Nat} {f : LBTerm} {tc : TravCtx} :
    (visitAppArgs (m := PureM) (n + 1) f #[]).runPure st tc pc ps = .ok ((f, st), ps) := by
  rw [visitAppArgs]; rfl

/-- `visitAppArgs` on a first argument and the others. Reference: the `tApp` case of `erase`
(`MR E/ErasureFunction.v:1006`). -/
theorem appArgs_cons {n : Nat} {f r : LBTerm} {a : Expr} {as : List Expr} {tc : TravCtx}
    {res : Except EraseError ((LBTerm × ErasureState) × PureState)}
    (ha : (visitExpr (m := PureM) n a).runPure st tc pc ps = .ok ((r, st'), ps'))
    (hr : (visitAppArgs (m := PureM) (n + 1) (.app f r) as.toArray).runPure st' tc pc ps' = res) :
    (visitAppArgs (m := PureM) (n + 1) f (a :: as).toArray).runPure st tc pc ps = res := by
  rw [visitAppArgs] at hr ⊢
  rw [← Array.foldlM_toList] at hr ⊢
  simp only [List.foldlM_cons] at hr ⊢
  refine bind_ok (a := .app f r) (st' := st') (ps' := ps') ?_ hr
  exact bind_ok ha rfl

/-- `register_inductive` on a registered inductive. Reference: none. -/
theorem register_found {iv : InductiveVal} {r : InductiveId × InductiveArgMasks} {tc : TravCtx}
    (h : st.inductives[iv.name]? = some r) :
    (register_inductive (m := PureM) iv).runPure st tc pc ps = .ok ((r, st), ps) := by
  rw [register_inductive]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, h]
  rfl

/-- `get_constant_kername` on an erased constant. Reference: none. -/
theorem kername_found {n : Nat} {cn : Name} {kn : Kername} {tc : TravCtx}
    (h : st.constants[cn]? = some kn) :
    (get_constant_kername (m := PureM) (n + 1) cn).runPure st tc pc ps = .ok ((kn, st), ps) := by
  rw [get_constant_kername]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, h]
  rfl

end Tools

/-! ## The inductives `PProd`, `N` and `PUnit` -/

variable {st : ErasureState} {ps : PureState} {dc : Name}

/-- The state after registering `PProd`, resp. `PUnit`. -/
def stPP (st : ErasureState) : ErasureState :=
  { st with
    inductives := st.inductives.insert `PProd (iidPP, masksPP)
    gdecls := (mutualBlockKername [`PProd], .inductiveDecl ⟨.finite, 2, [bodyPP]⟩) :: st.gdecls }
def stPU (st : ErasureState) : ErasureState :=
  { st with
    inductives := st.inductives.insert `PUnit (iidPU, masksPU)
    gdecls := (mutualBlockKername [`PUnit], .inductiveDecl ⟨.finite, 0, [bodyPU]⟩) :: st.gdecls }

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

theorem register_N_new {L : LocalContext} {ls : List Local} {F : Option (Std.HashMap Name FVarId)}
    (h : st.inductives[`N]? = none) :
    (register_inductive (m := PureM) N_ind).runPure st ⟨L, ls, F, cfg, dc⟩ pc ps =
      .ok (((iidN, masksN), NVR.stN st), ps) := by
  rw [register_inductive]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, show N_ind.name = `N from rfl, h]
  apply bind_ok (a := [bodyN])
    (st' := { st with inductives := st.inductives.insert `N (iidN, masksN) }) (ps' := ps) rfl
  apply bind_ok rfl
  apply bind_ok rfl
  simp only [Std.HashMap.getElem?_insert_self]
  rfl

theorem stPU_PU : (stPU st).inductives[`PUnit]? = some (iidPU, masksPU) := by
  simp only [stPU, Std.HashMap.getElem?_insert_self]

/-- The inductives once `PProd`, `N` and `PUnit` are registered, in this order. -/
abbrev stI (st : ErasureState) : ErasureState := stPU (NVR.stN (stPP st))

/-- The three registered inductives, as the traversal reads them. -/
structure Reg (st : ErasureState) : Prop where
  pp : st.inductives[`PProd]? = some (iidPP, masksPP)
  n : st.inductives[`N]? = some (iidN, masksN)
  pu : st.inductives[`PUnit]? = some (iidPU, masksPU)

theorem reg_stI : Reg (stI st) where
  pp := by simp only [stI, stPU, NVR.stN, stPP, Std.HashMap.getElem?_insert]; rfl
  n := by simp only [stI, stPU, NVR.stN, stPP, Std.HashMap.getElem?_insert]; rfl
  pu := by simp only [stI, stPU, NVR.stN, stPP, Std.HashMap.getElem?_insert]; rfl

/-! ## Constructors -/

/-- `visitExpr` on `N.z`, `N` registered. Reference: the `tConstruct` case of `erase`
(`MR E/ErasureFunction.v:1014`). -/
theorem cZ_run {n : Nat} {L : LocalContext} {ls : List Local} {F : Option (Std.HashMap Name FVarId)}
    (h : st.inductives[`N]? = some (iidN, masksN)) :
    (visitExpr (m := PureM) (n + 6) cZ).runPure st ⟨L, ls, F, cfg, dc⟩ pc ps =
      .ok ((zL, st), ps) := by
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

/-- `visitExpr` on `PUnit.unit.{l}` at the levels `max 1 u` and `1`, with the registration step
`hreg` on `PUnit`. Reference: the `tConstruct` case of `erase` (`MR E/ErasureFunction.v:1014`). -/
theorem cPU_run_of {n : Nat} {l : Level} {L : LocalContext} {ls : List Local}
    {F : Option (Std.HashMap Name FVarId)} {st' : ErasureState} (hl : l = m1u ∨ l = l1)
    (hreg : (register_inductive (m := PureM) PUnit_ind).runPure st ⟨L, ls, F, cfg, dc⟩ pc ps =
      .ok (((iidPU, masksPU), st'), ps)) :
    (visitExpr (m := PureM) (n + 6) (cPU l)).runPure st ⟨L, ls, F, cfg, dc⟩ pc ps =
      .ok ((unitL, st'), ps) := by
  rw [cPU, visitExpr]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ps) ?_ ?_
  · rcases hl with rfl | rfl <;> krfl
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 4) _).runPure _ _ _ _ = _
  rw [visitConstApp]
  refine bind_ok (a := none) (st' := st) (ps' := ps) ?_ ?_
  · rcases hl with rfl | rfl <;> krfl
  refine bind_ok (a := some 0) (st' := st) (ps' := ps) ?_ ?_
  · rcases hl with rfl | rfl <;> krfl
  change (withAppEtaToMinArity (m := PureM) (n + 3) _ 0 _).runPure _ _ _ _ = _
  rw [withAppEtaToMinArity]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := tPU l) (st' := st) (ps' := ps) ?_ ?_
  · rcases hl with rfl | rfl <;> krfl
  rw [withApp_const, withAppEtaToMinArity.go]
  rw [visitConstructor]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok hreg
  simp only [toArray_toSubarray]
  krfl

/-! ## `N.brecOn.go` -/

/-- The type of `F_1` under the motive `x_k`. -/
def F1T (k : Nat) : Expr :=
  .forallE `t tN (.forallE `f (.app (.app (below uu) (xv k)) (.bvar 0)) (.app (xv k) (.bvar 1))
    .default) .default

/-- The locals of `N.brecOn.go`'s body: `motive`, `t`, `F_1`. -/
def lsGo (o : List Local) : List Local := loc 7 `F_1 (F1T 5) :: loc 6 `t tN :: loc 5 `motive motTy :: o

/-- `PProd (x_k t) (N.below x_k t)` -/
def pairF (k : Nat) (t : Expr) : Expr :=
  .app (.app (tPP uu m1u) (.app (xv k) t)) (.app (.app (below uu) (xv k)) t)

/-- `@PProd.mk.{u, max 1 u} a b c d` -/
def mk4 (a b c d : Expr) : Expr := .app (.app (.app (.app (cPP uu m1u) a) b) c) d

/-- The arguments of `N.rec` in `N.brecOn.go`'s body. -/
def goMot : Expr := .lam `t tN (pairF 5 (.bvar 0)) .default
def fZ : Expr := .app (.app (xv 7) cZ) (cPU m1u)
def goMz : Expr := mk4 (.app (xv 5) cZ) (tPU m1u) fZ (cPU m1u)
def goMsBody (n ih : Expr) : Expr :=
  mk4 (.app (xv 5) (.app cS n)) (pairF 5 n) (.app (.app (xv 7) (.app cS n)) ih) ih
def goMs : Expr :=
  .lam `n tN (.lam `n_ih (pairF 5 (.bvar 0)) (goMsBody (.bvar 1) (.bvar 0)) .default) .default
def goB : Expr := .app (.app (.app (.app (.const `N.rec [m1u]) goMot) goMz) goMs) (xv 6)

theorem withApp_fZ {γ : Sort _} (k : Expr → Array Expr → γ) :
    fZ.withApp k = k (xv 7) #[cZ, cPU m1u] := by krfl

/-- `visitExpr` on `F_1 N.z PUnit.unit`, `N` registered and `PUnit` not: `PUnit` is registered by
its constructor. Reference: the `tApp` case of `erase` (`MR E/ErasureFunction.v:1006`). -/
theorem fZ_run {n : Nat} {L : LocalContext} {o : List Local} (hN : st.inductives[`N]? = some (iidN, masksN))
    (hPU : st.inductives[`PUnit]? = none) :
    (visitExpr (m := PureM) (n + 10) fZ).runPure st ⟨L, lsGo o, none, cfg, dc⟩ pc ps =
      .ok ((.app (.app (.fvar (xf 7)) zL) unitL, stPU st), ps) := by
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
  refine appArgs_cons (as := []) (cPU_run_of (n := n + 1) (.inl rfl) (register_PU_new hPU)) ?_
  exact appArgs_nil

/-- The arguments `visitConstructor` passes on for `PProd.mk`: the parameters and both fields. -/
theorem args_PP (a b c d : Expr) : #[a, b, c, d].extract 0 2 ++
    filter #[ConstructorArgRelevance.keep, .keep]
      (↑(#[a, b, c, d].toSubarray 2 (2 + 2)) : Array Expr) ++ #[a, b, c, d].extract (2 + 2) =
      #[a, b, c, d] := by
  apply Array.toList_inj.mp
  simp [filter, toArray_toSubarray]

theorem withApp_goMz {γ : Sort _} (k : Expr → Array Expr → γ) :
    goMz.withApp k = k (cPP uu m1u) #[.app (xv 5) cZ, tPU m1u, fZ, cPU m1u] := by krfl

/-- The erasure of the minor premise of `N.z` in `N.brecOn.go`. -/
def mzL : LBTerm := .app (.app (.app (.app mkL .box) .box) (.app (.app (.fvar (xf 7)) zL) unitL)) unitL

/-- `visitExpr` on the minor premise `⟨F_1 N.z PUnit.unit, PUnit.unit⟩` of `N.z`, `PProd` and `N`
registered: the type arguments are erased. Reference: the `tConstruct` case of `erase`
(`MR E/ErasureFunction.v:1014`). -/
theorem mz_run {n : Nat} {L : LocalContext} {o : List Local} (hPP : st.inductives[`PProd]? = some (iidPP, masksPP))
    (hN : st.inductives[`N]? = some (iidN, masksN)) (hPU : st.inductives[`PUnit]? = none) :
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
  refine appArgs_cons (as := []) (cPU_run_of (n := n + 4) (.inl rfl)
    (register_found (iv := PUnit_ind) stPU_PU)) ?_
  exact appArgs_nil

/-- The locals of the minor premise of `N.s` in `N.brecOn.go`: `n`, `n_ih`. -/
def lsS (o : List Local) : List Local := loc 9 `n_ih (pairF 5 (xv 8)) :: loc 8 `n tN :: lsGo o

theorem withApp_sx {γ : Sort _} (k : Expr → Array Expr → γ) (x : Expr) :
    (Expr.app cS x).withApp k = k cS #[x] := withApp_app1 cS x k rfl

/-- The arguments `visitConstructor` passes on for `N.s x`: the field, kept. -/
theorem args_s (x : Expr) : #[x].extract 0 0 ++
    filter #[ConstructorArgRelevance.keep]
      (↑(#[x].toSubarray 0 (0 + 1)) : Array Expr) ++ #[x].extract (0 + 1) = #[x] := by
  apply Array.toList_inj.mp
  simp [filter, toArray_toSubarray]

/-- `visitExpr` on `N.s x`, `x` the `k`-th local (of type `N`) of `ls`, `N` registered.
Reference: the `tConstruct` case of `erase` (`MR E/ErasureFunction.v:1014`). -/
theorem sx_run {n k : Nat} {L : LocalContext} {ls : List Local} {F : Option (Std.HashMap Name FVarId)}
    (hE : Pure.isErasable ⟨D⟩ oracleFuel ls (.app cS (xv k)) = .ok false)
    (hEx : Pure.isErasable ⟨D⟩ oracleFuel ls (xv k) = .ok false)
    (hT : Pure.inferType ⟨D⟩ oracleFuel ls [] (.app cS (xv k)) = .ok tN)
    (h : st.inductives[`N]? = some (iidN, masksN)) :
    (visitExpr (m := PureM) (n + 12) (.app cS (xv k))).runPure st ⟨L, ls, F, cfg, dc⟩ pc ps =
      .ok ((.app sL (.fvar (xf k)), st), ps) := by
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
  refine (congrArg (fun x : EraseT PureM LBTerm => x.runPure st ⟨L, ls, F, cfg, dc⟩ pc ps)
    (?_ : _ = visitAppArgs (m := PureM) (n + 8) sL #[xv k])).trans ?_
  · krfl
  refine appArgs_cons (as := []) (r := .fvar (xf k)) (st' := st) (ps' := ps) ?_ appArgs_nil
  rw [xv, visitExpr]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ps)
    (erasable_step (pc := pc) (tc := ⟨L, ls, F, cfg, dc⟩) hEx) ?_
  rfl

/-- `F_1 (N.s n) n_ih` in the minor premise of `N.s`. -/
def fS : Expr := .app (.app (xv 7) (.app cS (xv 8))) (xv 9)

theorem withApp_fS {γ : Sort _} (k : Expr → Array Expr → γ) :
    fS.withApp k = k (xv 7) #[.app cS (xv 8), xv 9] := by krfl

/-- `visitExpr` on `F_1 (N.s n) n_ih`, `N` registered. Reference: the `tApp` case of `erase`
(`MR E/ErasureFunction.v:1006`). -/
theorem fS_run {n : Nat} {L : LocalContext} {o : List Local} (hN : st.inductives[`N]? = some (iidN, masksN)) :
    (visitExpr (m := PureM) (n + 15) fS).runPure st ⟨L, lsS o, none, cfg, dc⟩ pc ps =
      .ok ((.app (.app (.fvar (xf 7)) (.app sL (.fvar (xf 8)))) (.fvar (xf 9)), st), ps) := by
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
    (sx_run (n := n) (k := 8) (by krfl) (by krfl) (by krfl) hN) ?_
  refine appArgs_cons (as := []) (r := .fvar (xf 9)) (st' := st) (ps' := ps) (by krfl) ?_
  exact appArgs_nil

def msB : Expr := goMsBody (xv 8) (xv 9)

theorem withApp_msB {γ : Sort _} (k : Expr → Array Expr → γ) :
    msB.withApp k = k (cPP uu m1u) #[.app (xv 5) (.app cS (xv 8)), pairF 5 (xv 8), fS, xv 9] := by
  krfl

/-- The erasure of the body of the minor premise of `N.s`. -/
def msBL : LBTerm :=
  .app (.app (.app (.app mkL .box) .box)
    (.app (.app (.fvar (xf 7)) (.app sL (.fvar (xf 8)))) (.fvar (xf 9)))) (.fvar (xf 9))

/-- `visitExpr` on `⟨F_1 (N.s n) n_ih, n_ih⟩`, `PProd` and `N` registered. Reference: the
`tConstruct` case of `erase` (`MR E/ErasureFunction.v:1014`). -/
theorem msB_run {n : Nat} {L : LocalContext} {o : List Local} (hPP : st.inductives[`PProd]? = some (iidPP, masksPP))
    (hN : st.inductives[`N]? = some (iidN, masksN)) :
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

/-- The erasure of the minor premise of `N.s` in `N.brecOn.go`. -/
def msL : LBTerm :=
  .lambda (binderNameOf `n) (_root_.abstract (xf 8)
    (.lambda (binderNameOf `n_ih) (_root_.abstract (xf 9) msBL)))

/-- `visitExpr` on the minor premise `fun n n_ih => ⟨F_1 (N.s n) n_ih, n_ih⟩` of `N.s`, `PProd`
and `N` registered, from the counter's ninth variable. Reference: the `tLambda` case of `erase`
(`MR E/ErasureFunction.v:1003`). -/
theorem ms_run {n : Nat} {L : LocalContext} {o : List Local} (hPP : st.inductives[`PProd]? = some (iidPP, masksPP))
    (hN : st.inductives[`N]? = some (iidN, masksN)) :
    (visitExpr (m := PureM) (n + 24) goMs).runPure st ⟨L, lsGo o, none, cfg, dc⟩ pc ⟨8⟩ =
      .ok ((msL, st), ⟨10⟩) :=
  lam_run (by krfl) fun _ => lam_run (by krfl) fun _ => msB_run (n := n) hPP hN

/-- The erasure of `N.brecOn.go`'s body: the minor premises let-bound around NV-R's fixpoint of
`N`'s block, applied to `t`. -/
def goBL : LBTerm :=
  .letIn (binderNameOf `z) mzL (.letIn (binderNameOf `s) msL (.app NVR.fixL (.fvar (xf 6))))

theorem withApp_goB {γ : Sort _} (k : Expr → Array Expr → γ) :
    goB.withApp k = k (.const `N.rec [m1u]) #[goMot, goMz, goMs, xv 6] := by krfl

theorem goB_app : goB = .app (mkAppN (.const `N.rec [m1u]) #[goMot, goMz, goMs]) (xv 6) := rfl

/-- `visitExpr` on `N.brecOn.go`'s body `N.rec (fun t => PProd (motive t) (N.below motive t)) mz ms
t`: `visitConstApp`'s recursor branch, `visitRec`; `N` is registered by the loop over the block,
`PUnit` by the first minor premise. Reference: none (DV-30). -/
theorem goB_run {n : Nat} {L : LocalContext} {o : List Local} (hPP : st.inductives[`PProd]? = some (iidPP, masksPP))
    (hN : st.inductives[`N]? = none) (hPU : st.inductives[`PUnit]? = none) :
    (visitExpr (m := PureM) (n + 30) goB).runPure st ⟨L, lsGo o, none, cfg, dc⟩ pc ⟨8⟩ =
      .ok ((goBL, stPU (NVR.stN st)), ⟨10⟩) := by
  have hPP' : (NVR.stN st).inductives[`PProd]? = some (iidPP, masksPP) := by
    simp only [NVR.stN, Std.HashMap.getElem?_insert, hPP]; rfl
  have hPU' : (NVR.stN st).inductives[`PUnit]? = none := by
    simp only [NVR.stN, Std.HashMap.getElem?_insert, hPU]; rfl
  have hN' : (stPU (NVR.stN st)).inductives[`N]? = some (iidN, masksN) := by
    simp only [stPU, NVR.stN, Std.HashMap.getElem?_insert]; rfl
  have hPP'' : (stPU (NVR.stN st)).inductives[`PProd]? = some (iidPP, masksPP) := by
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
  refine bind_ok (a := some (.recInfo N_rec)) (st' := st) (ps' := ⟨8⟩) (by krfl) ?_
  change (visitRec (m := PureM) (n + 27) _ _).runPure _ _ _ _ = _
  rw [visitRec]
  refine bind_ok (a := [N_ind]) (st' := st) (ps' := ⟨8⟩) (by krfl) ?_
  refine bind_ok (a := [Nz_ctor, Ns_ctor]) (st' := st) (ps' := ⟨8⟩) (by krfl) ?_
  apply bind_ok rfl
  have hnsc : ∀ x, recStaysConstant x N_rec [N_ind] [Nz_ctor, Ns_ctor] = false := by
    intro x; cases x <;> krfl
  simp only [hnsc, Bool.false_eq_true, ↓reduceIte]
  rw [NVR.recShape_N]
  dsimp only
  rw [List.forIn_cons]
  simp only [List.forIn_nil, Std.toStream, Std.Stream.next?]
  refine bind_ok (a := (#[NVR.memberN], 2, [])) (st' := NVR.stN st) (ps' := ⟨8⟩) ?_ ?_
  · refine bind_ok (a := ForInStep.yield (#[NVR.memberN], 2, [])) (st' := NVR.stN st) (ps' := ⟨8⟩) ?_ ?_
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
  refine bind_ok (a := .app goMot (xv 6)) (st' := NVR.stN st) (ps' := ⟨8⟩) (by krfl) ?_
  rw [withApp_goB, withAppEtaToMinArity.go]
  simp only [show (#[goMot, goMz, goMs, xv 6] : Array Expr).size = 4 from rfl, ge_iff_le,
    Nat.le_refl, ↓reduceIte]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := Level.succ .zero) (st' := NVR.stN st) (ps' := ⟨8⟩) (by krfl) ?_
  rw [show (#[goMot, goMz, goMs, xv 6].extract 1 (1 + 2)).toList = [goMz, goMs] from rfl]
  simp only [List.mapM_cons, List.mapM_nil]
  refine bind_ok (a := [mzL, msL]) (st' := stPU (NVR.stN st)) (ps' := ⟨10⟩) ?_ ?_
  · apply bind_ok (mz_run (n := n + 11) hPP' NVR.stN_N hPU')
    refine bind_ok (a := [msL]) (st' := stPU (NVR.stN st)) (ps' := ⟨10⟩) ?_ ?_
    · apply bind_ok (ms_run (n := n + 2) hPP'' hN')
      rfl
    rfl
  rw [visitAppArgs, show (#[goMot, goMz, goMs, xv 6].extract (1 + 2) 4) = #[xv 6] from rfl,
    ← Array.foldlM_toList]
  simp only [List.foldlM_cons, List.foldlM_nil]
  refine bind_ok (a := .app NVR.fixL (.fvar (xf 6))) (st' := stPU (NVR.stN st)) (ps' := ⟨10⟩) ?_ ?_
  · refine bind_ok (a := .app NVR.fixL (.fvar (xf 6))) (st' := stPU (NVR.stN st)) (ps' := ⟨10⟩) ?_ ?_
    · refine bind_ok (a := LBTerm.fvar (xf 6)) (st' := stPU (NVR.stN st)) (ps' := ⟨10⟩) (by krfl) ?_
      rfl
    rfl
  rw [visitAppArgs]
  rfl

/-- The state after erasing the definition `c` to the λ□ constant `t`. -/
def stDef (st : ErasureState) (c : Name) (t : LBTerm) : ErasureState :=
  { st with
    constants := st.constants.insert c (toKername c)
    gdecls := (toKername c, .constantDecl ⟨some t⟩) :: st.gdecls }

/-- The erasure of `N.brecOn.go`'s value. -/
def goVL : LBTerm :=
  .lambda (binderNameOf `motive) (_root_.abstract (xf 5) (.lambda (binderNameOf `t)
    (_root_.abstract (xf 6) (.lambda (binderNameOf `F_1) (_root_.abstract (xf 7) goBL)))))

/-- `visitExpr` on `N.brecOn.go`'s value, from the counter's sixth variable. Reference: the
`tLambda` case of `erase` (`MR E/ErasureFunction.v:1003`). -/
theorem goV_run {n : Nat} {L : LocalContext} {o : List Local}
    (hPP : st.inductives[`PProd]? = some (iidPP, masksPP))
    (hN : st.inductives[`N]? = none) (hPU : st.inductives[`PUnit]? = none) :
    (visitExpr (m := PureM) (n + 36) goVal).runPure st ⟨L, o, none, cfg, dc⟩ pc ⟨5⟩ =
      .ok ((goVL, stPU (NVR.stN st)), ⟨10⟩) :=
  lam_run (by krfl) fun _ => lam_run (by krfl) fun _ => lam_run (by krfl) fun _ =>
    goB_run (n := n) hPP hN hPU

/-- `visitMutual` on `N.brecOn.go`: a single, non-recursive definition without attributes, erased
to a λ□ constant. Reference: `erase_constant_body` (`MR E/ErasureFunction.v:1309`) in
`erase_global_deps` (`MR E/ErasureFunction.v:1602`). -/
theorem visitMutual_go {n : Nat} {L : LocalContext} {o : List Local}
    {F : Option (Std.HashMap Name FVarId)}
    (hPP : st.inductives[`PProd]? = some (iidPP, masksPP))
    (hN : st.inductives[`N]? = none) (hPU : st.inductives[`PUnit]? = none) :
    (visitMutual (m := PureM) (n + 37) `N.brecOn.go).runPure st ⟨L, o, F, cfg, dc⟩ pc ⟨5⟩ =
      .ok (((), stDef (stPU (NVR.stN st)) `N.brecOn.go goVL), ⟨10⟩) := by
  rw [visitMutual]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := goVL) (st' := stPU (NVR.stN st)) (ps' := ⟨10⟩) ?_ ?_
  · rw [runPure_withReader]
    apply bind_ok rfl
    refine bind_ok (a := goVal) (st' := st) (ps' := ⟨5⟩) rfl ?_
    exact goV_run (n := n) hPP hN hPU
  rfl

/-- `get_constant_kername` on `N.brecOn.go`, not yet erased. Reference: `erase_global_deps`
(`MR E/ErasureFunction.v:1602`). -/
theorem kername_go {n : Nat} {L : LocalContext} {o : List Local}
    {F : Option (Std.HashMap Name FVarId)} (hc : st.constants[`N.brecOn.go]? = none)
    (hPP : st.inductives[`PProd]? = some (iidPP, masksPP))
    (hN : st.inductives[`N]? = none) (hPU : st.inductives[`PUnit]? = none) :
    (get_constant_kername (m := PureM) (n + 38) `N.brecOn.go).runPure st ⟨L, o, F, cfg, dc⟩ pc ⟨5⟩ =
      .ok ((toKername `N.brecOn.go, stDef (stPU (NVR.stN st)) `N.brecOn.go goVL), ⟨10⟩) := by
  rw [get_constant_kername]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, hc]
  apply bind_ok (visitMutual_go hPP hN hPU)
  apply bind_ok rfl
  simp only [stDef, Std.HashMap.getElem?_insert_self]
  rfl

/-! ## `N.brecOn` -/

/-- The locals of `N.brecOn`'s body: `motive`, `t`, `F_1`. -/
def lsB (o : List Local) : List Local :=
  loc 4 `F_1 (F1T 2) :: loc 3 `t tN :: loc 2 `motive motTy :: o

/-- `N.brecOn.go motive t F_1` in `N.brecOn`'s body. -/
def goApp : Expr := .app (.app (.app (.const `N.brecOn.go [uu]) (xv 2)) (xv 3)) (xv 4)

theorem withApp_goApp {γ : Sort _} (k : Expr → Array Expr → γ) :
    goApp.withApp k = k (.const `N.brecOn.go [uu]) #[xv 2, xv 3, xv 4] := by krfl

/-- The state after `N.brecOn.go`. -/
abbrev stGo (st : ErasureState) : ErasureState := stDef (stPU (NVR.stN st)) `N.brecOn.go goVL

/-- `visitExpr` on `N.brecOn.go motive t F_1`, `N.brecOn.go` not erased, `PProd` registered: the
λ□ constant of `N.brecOn.go`, erased on the way, applied to □ for the motive. Reference: the
`tConst` and `tApp` cases of `erase` (`MR E/ErasureFunction.v:999`, `:1006`). -/
theorem goApp_run {n : Nat} {L : LocalContext} {o : List Local}
    (hc : st.constants[`N.brecOn.go]? = none)
    (hPP : st.inductives[`PProd]? = some (iidPP, masksPP))
    (hN : st.inductives[`N]? = none) (hPU : st.inductives[`PUnit]? = none) :
    (visitExpr (m := PureM) (n + 44) goApp).runPure st ⟨L, lsB o, none, cfg, dc⟩ pc ⟨5⟩ =
      .ok ((.app (.app (.app (.const (toKername `N.brecOn.go)) .box) (.fvar (xf 3))) (.fvar (xf 4)),
        stGo st), ⟨10⟩) := by
  rw [goApp, visitExpr, ← goApp]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ⟨5⟩) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 42) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_goApp]
  refine bind_ok (a := none) (st' := st) (ps' := ⟨5⟩) (by krfl) ?_
  refine bind_ok (a := none) (st' := st) (ps' := ⟨5⟩) (by krfl) ?_
  refine bind_ok (a := some (.defnInfo N_brecOn_go)) (st' := st) (ps' := ⟨5⟩) (by krfl) ?_
  refine bind_ok (a := .const (toKername `N.brecOn.go)) (st' := stGo st) (ps' := ⟨10⟩) ?_ ?_
  · rw [visitConst]
    apply bind_ok rfl
    refine bind_ok (kername_go (n := n + 2) hc hPP hN hPU) ?_
    rfl
  refine appArgs_cons (as := [xv 3, xv 4]) (r := .box) (st' := stGo st) (ps' := ⟨10⟩) (by krfl) ?_
  refine appArgs_cons (as := [xv 4]) (r := .fvar (xf 3)) (st' := stGo st) (ps' := ⟨10⟩) (by krfl) ?_
  refine appArgs_cons (as := []) (r := .fvar (xf 4)) (st' := stGo st) (ps' := ⟨10⟩) (by krfl) ?_
  exact appArgs_nil

/-- The erasure of `N.brecOn`'s value. -/
def brecOnVL : LBTerm :=
  .lambda (binderNameOf `motive) (_root_.abstract (xf 2) (.lambda (binderNameOf `t)
    (_root_.abstract (xf 3) (.lambda (binderNameOf `F_1) (_root_.abstract (xf 4)
      (.proj projPP
        (.app (.app (.app (.const (toKername `N.brecOn.go)) .box) (.fvar (xf 3))) (.fvar (xf 4)))))))))

/-- `visitExpr` on `N.brecOn`'s value, `PProd` not registered: the first projection of
`N.brecOn.go`'s pair, where the projection registers `PProd`. Reference: the `tLambda` and `tProj`
cases of `erase` (`MR E/ErasureFunction.v:1003`, `:1020`). -/
theorem brecOnV_run {n : Nat} {L : LocalContext} {o : List Local}
    (hc : st.constants[`N.brecOn.go]? = none) (hPP : st.inductives[`PProd]? = none)
    (hN : st.inductives[`N]? = none) (hPU : st.inductives[`PUnit]? = none) :
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

/-- The state after `N.brecOn`. -/
abbrev stBr (st : ErasureState) : ErasureState := stDef (stGo (stPP st)) `N.brecOn brecOnVL

/-- `visitMutual` on `N.brecOn`. Reference: as `visitMutual_go`. -/
theorem visitMutual_brecOn {n : Nat} {L : LocalContext} {o : List Local}
    {F : Option (Std.HashMap Name FVarId)}
    (hc : st.constants[`N.brecOn.go]? = none) (hPP : st.inductives[`PProd]? = none)
    (hN : st.inductives[`N]? = none) (hPU : st.inductives[`PUnit]? = none) :
    (visitMutual (m := PureM) (n + 53) `N.brecOn).runPure st ⟨L, o, F, cfg, dc⟩ pc ⟨2⟩ =
      .ok (((), stBr st), ⟨10⟩) := by
  rw [visitMutual]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := brecOnVL) (st' := stGo (stPP st)) (ps' := ⟨10⟩) ?_ ?_
  · rw [runPure_withReader]
    apply bind_ok rfl
    refine bind_ok (a := brecOnVal) (st' := st) (ps' := ⟨2⟩) rfl ?_
    exact brecOnV_run (n := n) hc hPP hN hPU
  rfl

/-- `get_constant_kername` on `N.brecOn`, not yet erased. Reference: `erase_global_deps`
(`MR E/ErasureFunction.v:1602`). -/
theorem kername_brecOn {n : Nat} {L : LocalContext} {o : List Local}
    {F : Option (Std.HashMap Name FVarId)} (hb : st.constants[`N.brecOn]? = none)
    (hc : st.constants[`N.brecOn.go]? = none) (hPP : st.inductives[`PProd]? = none)
    (hN : st.inductives[`N]? = none) (hPU : st.inductives[`PUnit]? = none) :
    (get_constant_kername (m := PureM) (n + 54) `N.brecOn).runPure st ⟨L, o, F, cfg, dc⟩ pc ⟨2⟩ =
      .ok ((toKername `N.brecOn, stBr st), ⟨10⟩) := by
  rw [get_constant_kername]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, hb]
  apply bind_ok (visitMutual_brecOn hc hPP hN hPU)
  apply bind_ok rfl
  simp only [stBr, stDef, Std.HashMap.getElem?_insert_self]
  rfl

/-! ## `Unit.unit` and `add.match_1` -/

/-- The state after marking the `@[inline]` definition `c` for inlining. -/
def stInl (st : ErasureState) (c : Name) : ErasureState :=
  { st with inlinings := toKername c :: st.inlinings }

/-- The state after erasing the `@[inline]` definition `c` to the λ□ constant `t`, with its
inlined size. -/
def stDefI (st : ErasureState) (c : Name) (t : LBTerm) : ErasureState :=
  { stDef st c t with
    inlinedSizes := (stDef st c t).inlinedSizes.insert (toKername c)
      (t.inlinedSize (stDef st c t).inlinedSizes) }


/-- `visitMutual` on `Unit.unit`, `PUnit` registered: an `@[inline]` definition, marked for
inlining and erased to the λ□ constant `PUnit.unit`. Reference: `erase_constant_body`
(`MR E/ErasureFunction.v:1309`); the marking: none. -/
theorem visitMutual_unit {n : Nat} {L : LocalContext} {o : List Local}
    {F : Option (Std.HashMap Name FVarId)} (hPU : st.inductives[`PUnit]? = some (iidPU, masksPU)) :
    (visitMutual (m := PureM) (n + 8) `Unit.unit).runPure st ⟨L, o, F, cfg, dc⟩ pc ps =
      .ok (((), stDefI (stInl st `Unit.unit) `Unit.unit unitL), ps) := by
  rw [visitMutual]
  iterate 10 apply bind_ok rfl
  refine bind_ok (a := unitL) (st' := stInl st `Unit.unit) (ps' := ps) ?_ ?_
  · rw [runPure_withReader]
    apply bind_ok rfl
    refine bind_ok (a := cPU l1) (st' := stInl st `Unit.unit) (ps' := ps) rfl ?_
    exact cPU_run_of (n := n + 1) (.inr rfl) (register_found (iv := PUnit_ind) hPU)
  rfl

/-- `get_constant_kername` on `Unit.unit`, not yet erased. Reference: `erase_global_deps`
(`MR E/ErasureFunction.v:1602`). -/
theorem kername_unit {n : Nat} {L : LocalContext} {o : List Local}
    {F : Option (Std.HashMap Name FVarId)} (hc : st.constants[`Unit.unit]? = none)
    (hPU : st.inductives[`PUnit]? = some (iidPU, masksPU)) :
    (get_constant_kername (m := PureM) (n + 9) `Unit.unit).runPure st ⟨L, o, F, cfg, dc⟩ pc ps =
      .ok ((toKername `Unit.unit, stDefI (stInl st `Unit.unit) `Unit.unit unitL), ps) := by
  rw [get_constant_kername]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, hc]
  apply bind_ok (visitMutual_unit hPU)
  apply bind_ok rfl
  simp only [stDefI, stDef, Std.HashMap.getElem?_insert_self]
  rfl

/-- The locals of `add.match_1`'s body: `motive`, `m`, `h_1`, `h_2`. -/
def lsM (o : List Local) : List Local :=
  loc 16 `h_2 (.forallE `k tN (.app (xv 13) (.app cS (.bvar 0))) .default) ::
    loc 15 `h_1 (.forallE `_ tUnit (.app (xv 13) cZ) .default) :: loc 14 (hyg "m" 8) tN ::
    loc 13 `motive mMotTy :: o

/-- The alternatives of `add.match_1`'s `casesOn`. -/
def alt1 : Expr := .app (xv 15) (.const `Unit.unit [])
def alt2 : Expr := .lam (hyg "n" 22) tN (.app (xv 16) (.bvar 0)) .default
def motM : Expr := .lam `x tN (.app (xv 13) (.bvar 0)) .default

/-- `add.match_1`'s body. -/
def mB : Expr := .app (.app (.app (.app (.const `N.casesOn [u1]) motM) (xv 14)) alt1) alt2

theorem withApp_mB {γ : Sort _} (k : Expr → Array Expr → γ) :
    mB.withApp k = k (.const `N.casesOn [u1]) #[motM, xv 14, alt1, alt2] := by krfl

theorem withApp_alt1 {γ : Sort _} (k : Expr → Array Expr → γ) :
    alt1.withApp k = k (xv 15) #[.const `Unit.unit []] := by krfl

/-- The erasure of the first alternative, `h_1 Unit.unit`. -/
def alt1L : LBTerm := .app (.fvar (xf 15)) (.const (toKername `Unit.unit))

/-- `visitExpr` on `Unit.unit` under `add.match_1`'s binders, not yet erased: the λ□ constant.
Reference: the `tConst` case of `erase` (`MR E/ErasureFunction.v:999`). -/
theorem unitC_run {n : Nat} {L : LocalContext} {o : List Local}
    (hc : st.constants[`Unit.unit]? = none) (hPU : st.inductives[`PUnit]? = some (iidPU, masksPU)) :
    (visitExpr (m := PureM) (n + 14) (.const `Unit.unit [])).runPure st ⟨L, lsM o, none, cfg, dc⟩ pc
      ps = .ok ((.const (toKername `Unit.unit), stDefI (stInl st `Unit.unit) `Unit.unit unitL), ps) := by
  rw [visitExpr]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ps) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 12) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_const]
  refine bind_ok (a := none) (st' := st) (ps' := ps) (by krfl) ?_
  refine bind_ok (a := none) (st' := st) (ps' := ps) (by krfl) ?_
  refine bind_ok (a := some (.defnInfo Unit_unit)) (st' := st) (ps' := ps) (by krfl) ?_
  refine bind_ok (a := .const (toKername `Unit.unit))
    (st' := stDefI (stInl st `Unit.unit) `Unit.unit unitL) (ps' := ps) ?_ ?_
  · rw [visitConst]
    apply bind_ok rfl
    refine bind_ok (kername_unit (n := n + 1) hc hPU) ?_
    rfl
  exact appArgs_nil

/-- `visitAlt` on the first alternative `h_1 Unit.unit` (no field). Reference: the branches of the
`tCase` case of `erase` (`MR E/ErasureFunction.v:1016`). -/
theorem alt1_run {n : Nat} {L : LocalContext} {o : List Local}
    (hc : st.constants[`Unit.unit]? = none) (hPU : st.inductives[`PUnit]? = some (iidPU, masksPU)) :
    (visitAlt (m := PureM) (n + 18) 0 #[] [] alt1).runPure st ⟨L, lsM o, none, cfg, dc⟩ pc ps =
      .ok ((([], alt1L), stDefI (stInl st `Unit.unit) `Unit.unit unitL), ps) := by
  rw [visitAlt]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := .app (xv 13) cZ) (st' := st) (ps' := ps) (by krfl) ?_
  rw [lambdaOrIntroToArity]
  refine bind_ok (a := alt1L) (st' := stDefI (stInl st `Unit.unit) `Unit.unit unitL) (ps' := ps) ?_ ?_
  · show (visitExpr (m := PureM) (n + 17) alt1).runPure _ _ _ _ = _
    rw [alt1, visitExpr, ← alt1]
    apply bind_ok rfl
    apply bind_ok rfl
    refine bind_ok (a := false) (st' := st) (ps' := ps) (by krfl) ?_
    rw [visitApp]
    change (alt1.withApp fun f args => do
      visitAppArgs (m := PureM) (n + 15) (← visitExpr (m := PureM) (n + 15) f) args).runPure _ _ _ _ = _
    rw [withApp_alt1]
    refine bind_ok (a := .fvar (xf 15)) (st' := st) (ps' := ps) (by krfl) ?_
    refine appArgs_cons (as := []) (unitC_run (n := n) hc hPU) ?_
    exact appArgs_nil
  krfl

/-- The erasure of the second alternative, `fun n => h_2 n`, under its field. -/
def alt2L : LBTerm := .app (.fvar (xf 16)) (.bvar 0)

/-- `visitAlt` on the second alternative `fun n => h_2 n` (one field), from the counter's
eighteenth variable. Reference: the branches of the `tCase` case of `erase`
(`MR E/ErasureFunction.v:1016`). -/
theorem alt2_run {n : Nat} {L : LocalContext} {o : List Local} :
    (visitAlt (m := PureM) (n + 10) 1 #[.keep] [] alt2).runPure st ⟨L, lsM o, none, cfg, dc⟩ pc ⟨17⟩ =
      .ok ((([binderNameOf (hyg "n" 22)], alt2L), st), ⟨18⟩) := by
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
  .case (iidN, 0) (.fvar (xf 14)) [([], alt1L), ([binderNameOf (hyg "n" 22)], alt2L)]

/-- The state after `Unit.unit`. -/
abbrev stU (st : ErasureState) : ErasureState := stDefI (stInl st `Unit.unit) `Unit.unit unitL

/-- `visitCasesOn` on `add.match_1`'s alternatives and the discriminant `m`, `N` registered.
Reference: the `tCase` case of `erase` (`MR E/ErasureFunction.v:1016`). -/
theorem visitCasesOn_run {n : Nat} {L : LocalContext} {o : List Local}
    (hc : st.constants[`Unit.unit]? = none) (hPU : st.inductives[`PUnit]? = some (iidPU, masksPU))
    (hN : st.inductives[`N]? = some (iidN, masksN)) :
    (visitCasesOn (m := PureM) (n + 19) N_ind altsM ∅ none (.fvar (xf 14))).runPure st
      ⟨L, lsM o, none, cfg, dc⟩ pc ⟨17⟩ = .ok ((caseM, stU st), ⟨18⟩) := by
  rw [visitCasesOn]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok (register_found (iv := N_ind) hN)
  simp only [show N_ind.ctors = [`N.z, `N.s] from rfl, List.forIn_cons, List.forIn_nil, bind_assoc,
    altsM_z, altsM_s, Std.HashMap.getD_empty]
  refine bind_ok (a := .yield (#[([], alt1L)], ([#[.keep]] : List ConstructorArgMask)))
    (st' := stU st) (ps' := ⟨17⟩) ?_ ?_
  · apply bind_ok (alt1_run (n := n) hc hPU)
    rfl
  refine bind_ok (a := (#[([], alt1L), ([binderNameOf (hyg "n" 22)], alt2L)],
    ([] : List ConstructorArgMask))) (st' := stU st) (ps' := ⟨18⟩) ?_ ?_
  · refine bind_ok (a := .yield (#[([], alt1L), ([binderNameOf (hyg "n" 22)], alt2L)],
      ([] : List ConstructorArgMask))) (st' := stU st) (ps' := ⟨18⟩) ?_ ?_
    · apply bind_ok (alt2_run (n := n + 8))
      rfl
    · rfl
  rfl

/-- The recognizer's answer on `N.casesOn`. -/
def ciN : CasesInfo :=
  { declName := `N.casesOn, indName := `N, arity := 4, discrPos := 1, motivePos := 0,
    altsRange := 2...4, altNumParams := #[.ctor `N.z 0, .ctor `N.s 1] }

/-- `visitCases` on `add.match_1`'s `casesOn`: `N.casesOn` has one universe parameter more than `N`,
and the discriminant's sort is never `Prop`, so the result is the λ□ `case`. Reference: the `tCase`
case of `erase` (`MR E/ErasureFunction.v:1016`). -/
theorem visitCases_run {n : Nat} {L : LocalContext} {o : List Local}
    (hc : st.constants[`Unit.unit]? = none) (hPU : st.inductives[`PUnit]? = some (iidPU, masksPU))
    (hN : st.inductives[`N]? = some (iidN, masksN)) :
    (visitCases (m := PureM) (n + 22) ciN #[motM, xv 14, alt1, alt2]).runPure st
      ⟨L, lsM o, none, cfg, dc⟩ pc ⟨17⟩ = .ok ((caseM, stU st), ⟨18⟩) := by
  rw [visitCases]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := Level.succ .zero) (st' := st) (ps' := ⟨17⟩) (by krfl) ?_
  have hr : (ciN.altsRange.toList) = [2, 3] := by simp [ciN, Nat.toList_rco_eq_ite]
  simp only [← forIn'_eq_forIn, Std.Rco.forIn'_eq_forIn'_toList, hr, List.forIn'_cons,
    List.forIn'_nil]
  refine bind_ok (a := (altsM, none, ?sEnd)) (st' := st) (ps' := ⟨17⟩) ?_ ?_
  case sEnd => exact (ciN.altNumParams.toSubarray 2 2)
  · rfl
  refine bind_ok (a := .fvar (xf 14)) (st' := st) (ps' := ⟨17⟩) (by krfl) ?_
  simp only [show N_ind.ctors = [`N.z, `N.s] from rfl, altsM_all, ite_true]
  apply bind_ok (visitCasesOn_run (n := n + 2) hc hPU hN)
  rw [show ciN.arity = (#[motM, xv 14, alt1, alt2] : Array Expr).size from rfl,
    forIn_toSubarray_size]
  rfl


/-- The locals of `add`'s body: `n`, `m`. -/
def lsA : List Local := [loc 1 `m tN, loc 0 `n tN]

/-- The locals of `add._f`'s body: `n`, `m`, `f`. -/
def lsF (o : List Local) : List Local :=
  loc 12 `f (belowN (xv 11)) :: loc 11 `m tN :: loc 10 `n tN :: o

/-- `visitExpr` on `add.match_1`'s body: a saturated recognized `casesOn`. Reference: the `tCase`
case of `erase` (`MR E/ErasureFunction.v:1016`). -/
theorem mB_run {n : Nat} {L : LocalContext} 
    (hc : st.constants[`Unit.unit]? = none) (hPU : st.inductives[`PUnit]? = some (iidPU, masksPU))
    (hN : st.inductives[`N]? = some (iidN, masksN)) :
    (visitExpr (m := PureM) (n + 26) mB).runPure st ⟨L, lsM (lsF lsA), none, cfg, dc⟩ pc ⟨17⟩ =
      .ok ((caseM, stU st), ⟨18⟩) := by
  rw [mB, visitExpr, ← mB]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ⟨17⟩) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 24) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_mB]
  refine bind_ok (a := some ciN) (st' := st) (ps' := ⟨17⟩) (by krfl) ?_
  change (withAppEtaToMinArity (m := PureM) (n + 23) _ 4 _).runPure _ _ _ _ = _
  rw [withAppEtaToMinArity]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := .app motM (xv 14)) (st' := st) (ps' := ⟨17⟩)
    (infer_step (pc := pc) (tc := ⟨L, lsM (lsF lsA), none, cfg, dc⟩) (by krfl)) ?_
  rw [withApp_mB, withAppEtaToMinArity.go]
  simp only [show (#[motM, xv 14, alt1, alt2] : Array Expr).size = 4 from rfl, ge_iff_le,
    Nat.le_refl, ↓reduceIte]
  exact visitCases_run (n := n + 1) hc hPU hN

/-- The erasure of `add.match_1`'s value. -/
def matchVL : LBTerm :=
  .lambda (binderNameOf `motive) (_root_.abstract (xf 13) (.lambda (binderNameOf (hyg "m" 8))
    (_root_.abstract (xf 14) (.lambda (binderNameOf `h_1) (_root_.abstract (xf 15)
      (.lambda (binderNameOf `h_2) (_root_.abstract (xf 16) caseM)))))))

/-- `visitExpr` on `add.match_1`'s value, from the counter's fourteenth variable. Reference: the
`tLambda` case of `erase` (`MR E/ErasureFunction.v:1003`). -/
theorem matchV_run {n : Nat} {L : LocalContext} 
    (hc : st.constants[`Unit.unit]? = none) (hPU : st.inductives[`PUnit]? = some (iidPU, masksPU))
    (hN : st.inductives[`N]? = some (iidN, masksN)) :
    (visitExpr (m := PureM) (n + 34) matchVal).runPure st ⟨L, lsF lsA, none, cfg, dc⟩ pc ⟨13⟩ =
      .ok ((matchVL, stU st), ⟨18⟩) :=
  lam_run (by krfl) fun _ => lam_run (by krfl) fun _ => lam_run (by krfl) fun _ =>
    lam_run (by krfl) fun _ => mB_run (n := n) hc hPU hN

/-- The state after `add.match_1`. -/
abbrev stMt (st : ErasureState) : ErasureState :=
  stDefI (stU (stInl st `add.match_1)) `add.match_1 matchVL

/-- `visitMutual` on `add.match_1`: an `@[inline]` definition, marked for inlining and erased to a
λ□ constant. Reference: as `visitMutual_unit`. -/
theorem visitMutual_match {n : Nat} {L : LocalContext} 
    {F : Option (Std.HashMap Name FVarId)}
    (hc : st.constants[`Unit.unit]? = none) (hPU : st.inductives[`PUnit]? = some (iidPU, masksPU))
    (hN : st.inductives[`N]? = some (iidN, masksN)) :
    (visitMutual (m := PureM) (n + 35) `add.match_1).runPure st ⟨L, lsF lsA, F, cfg, dc⟩ pc ⟨13⟩ =
      .ok (((), stMt st), ⟨18⟩) := by
  rw [visitMutual]
  iterate 10 apply bind_ok rfl
  refine bind_ok (a := matchVL) (st' := stU (stInl st `add.match_1)) (ps' := ⟨18⟩) ?_ ?_
  · rw [runPure_withReader]
    apply bind_ok rfl
    refine bind_ok (a := matchVal) (st' := stInl st `add.match_1) (ps' := ⟨13⟩) rfl ?_
    exact matchV_run (n := n) hc hPU hN
  rfl

/-- `get_constant_kername` on `add.match_1`, not yet erased. Reference: `erase_global_deps`
(`MR E/ErasureFunction.v:1602`). -/
theorem kername_match {n : Nat} {L : LocalContext} 
    {F : Option (Std.HashMap Name FVarId)} (hm : st.constants[`add.match_1]? = none)
    (hc : st.constants[`Unit.unit]? = none) (hPU : st.inductives[`PUnit]? = some (iidPU, masksPU))
    (hN : st.inductives[`N]? = some (iidN, masksN)) :
    (get_constant_kername (m := PureM) (n + 36) `add.match_1).runPure st ⟨L, lsF lsA, F, cfg, dc⟩ pc ⟨13⟩ =
      .ok ((toKername `add.match_1, stMt st), ⟨18⟩) := by
  rw [get_constant_kername]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, hm]
  apply bind_ok (visitMutual_match hc hPU hN)
  apply bind_ok rfl
  simp only [stMt, stDefI, stDef, Std.HashMap.getElem?_insert_self]
  rfl

/-! ## `add._f` -/

/-- Facts about the traversal's maps in the states of the run. -/
macro (name := _stfact) "stfact" : tactic => `(tactic| (simp only [stMt, stDefI, stU, stInl, stBr, stGo, stDef, stPU,
  NVR.stN, stPP, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]; try rfl))

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
  refine bind_ok (a := .fvar (xf k)) (st' := st) (ps' := ps) ?_ ?_
  · rw [xv, visitExpr]
    apply bind_ok rfl
    apply bind_ok rfl
    refine bind_ok (a := false) (st' := st) (ps' := ps)
      (erasable_step (pc := pc) (tc := ⟨L, ls, F, cfg, dc⟩) hEx) ?_
    rfl
  simp only [toArray_toSubarray]
  rfl

/-- `visitExpr` on `N.s a`, `a` erased to `ra` with the state unchanged, `N` registered. Reference: the `tConstruct` case of `erase` (`MR E/ErasureFunction.v:1014`). -/
theorem sArg_run {n : Nat} {a : Expr} {ra : LBTerm} {L : LocalContext} {ls : List Local}
    {F : Option (Std.HashMap Name FVarId)}
    (hE : Pure.isErasable ⟨D⟩ oracleFuel ls (.app cS a) = .ok false)
    (hT : Pure.inferType ⟨D⟩ oracleFuel ls [] (.app cS a) = .ok tN)
    (ha : (visitExpr (m := PureM) (n + 7) a).runPure st ⟨L, ls, F, cfg, dc⟩ pc ps = .ok ((ra, st), ps))
    (h : st.inductives[`N]? = some (iidN, masksN)) :
    (visitExpr (m := PureM) (n + 12) (.app cS a)).runPure st ⟨L, ls, F, cfg, dc⟩ pc ps =
      .ok ((.app sL ra, st), ps) := by
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
  refine (congrArg (fun x : EraseT PureM LBTerm => x.runPure st ⟨L, ls, F, cfg, dc⟩ pc ps)
    (?_ : _ = visitAppArgs (m := PureM) (n + 8) sL #[a])).trans ?_
  · krfl
  exact appArgs_cons (as := []) ha appArgs_nil

/-- The alternatives of `add._f`'s match and its motive. -/
def motF : Expr :=
  .lam (hyg "m" 8) tN (.forallE (hyg "x" 23) (belowN (.bvar 0)) tN .default) .default
def h1F : Expr := .lam `_ tUnit (.lam (hyg "x" 23) (belowN cZ) (xv 10) .default) .default
def h2F : Expr :=
  .lam `k tN (.lam (hyg "x" 23) (belowN (.app cS (.bvar 0))) (.app cS (.proj `PProd 0 (.bvar 0)))
    .default) .default

/-- `add._f`'s body. -/
def fB : Expr :=
  .app (.app (.app (.app (.app (.const `add.match_1 [l1]) motF) (xv 11)) h1F) h2F) (xv 12)

theorem withApp_fB {γ : Sort _} (k : Expr → Array Expr → γ) :
    fB.withApp k = k (.const `add.match_1 [l1]) #[motF, xv 11, h1F, h2F, xv 12] := by krfl

/-- The erasures of the alternatives. -/
def h1L : LBTerm :=
  .lambda (binderNameOf `_) (_root_.abstract (xf 18)
    (.lambda (binderNameOf (hyg "x" 23)) (_root_.abstract (xf 19) (.fvar (xf 10)))))
def h2L : LBTerm :=
  .lambda (binderNameOf `k) (_root_.abstract (xf 20)
    (.lambda (binderNameOf (hyg "x" 23)) (_root_.abstract (xf 21)
      (.app sL (.proj projPP (.fvar (xf 21)))))))

/-- The erasure of `add._f`'s body. -/
def fBL : LBTerm :=
  .app (.app (.app (.app (.app (.const (toKername `add.match_1)) .box) (.fvar (xf 11))) h1L) h2L)
    (.fvar (xf 12))

/-- `visitExpr` on `add._f`'s body `add.match_1 motive m (fun _ x => n) (fun k x => N.s x.1) f`,
`add.match_1` not erased, `N`, `PProd` and `PUnit` registered: the λ□ constant of `add.match_1`,
erased on the way, applied to □ and the erased alternatives. Reference: the `tConst` and `tApp`
cases of `erase` (`MR E/ErasureFunction.v:999`, `:1006`). -/
theorem fB_run {n : Nat} {L : LocalContext}
    (hm : st.constants[`add.match_1]? = none) (hc : st.constants[`Unit.unit]? = none)
    (hR : Reg st) :
    (visitExpr (m := PureM) (n + 40) fB).runPure st ⟨L, lsF lsA, none, cfg, dc⟩ pc ⟨13⟩ =
      .ok ((fBL, stMt st), ⟨22⟩) := by
  have hR' : Reg (stMt st) := ⟨by stfact; exact hR.pp, by stfact; exact hR.n, by stfact; exact hR.pu⟩
  rw [fB, visitExpr, ← fB]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ⟨13⟩) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 38) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_fB]
  refine bind_ok (a := none) (st' := st) (ps' := ⟨13⟩) (by krfl) ?_
  refine bind_ok (a := none) (st' := st) (ps' := ⟨13⟩) (by krfl) ?_
  refine bind_ok (a := some (.defnInfo add_match_1)) (st' := st) (ps' := ⟨13⟩) (by krfl) ?_
  refine bind_ok (a := .const (toKername `add.match_1)) (st' := stMt st) (ps' := ⟨18⟩) ?_ ?_
  · rw [visitConst]
    apply bind_ok rfl
    refine bind_ok (kername_match (n := n) hm hc hR.pu hR.n) ?_
    rfl
  refine appArgs_cons (as := [xv 11, h1F, h2F, xv 12]) (r := .box) (st' := stMt st) (ps' := ⟨18⟩)
    (by krfl) ?_
  refine appArgs_cons (as := [h1F, h2F, xv 12]) (r := .fvar (xf 11)) (st' := stMt st)
    (ps' := ⟨18⟩) (by krfl) ?_
  refine appArgs_cons (as := [h2F, xv 12]) (r := h1L) (st' := stMt st) (ps' := ⟨20⟩)
    (lam_run (by krfl) fun _ => lam_run (by krfl) fun _ => by krfl) ?_
  refine appArgs_cons (as := [xv 12]) (r := h2L) (st' := stMt st) (ps' := ⟨22⟩)
    (lam_run (by krfl) fun _ => lam_run (by krfl) fun _ =>
      sArg_run (n := n + 20) (by krfl) (by krfl)
        (projX_run (n := n + 23) (by krfl) (by krfl) hR'.pp) hR'.n) ?_
  refine appArgs_cons (as := []) (r := .fvar (xf 12)) (st' := stMt st) (ps' := ⟨22⟩) (by krfl) ?_
  exact appArgs_nil

/-- The erasure of `add._f`'s value. -/
def fVL : LBTerm :=
  .lambda (binderNameOf `n) (_root_.abstract (xf 10) (.lambda (binderNameOf `m)
    (_root_.abstract (xf 11) (.lambda (binderNameOf `f) (_root_.abstract (xf 12) fBL)))))

/-- `visitExpr` on `add._f`'s value, from the counter's eleventh variable. Reference: the
`tLambda` case of `erase` (`MR E/ErasureFunction.v:1003`). -/
theorem fV_run {n : Nat} {L : LocalContext}
    (hm : st.constants[`add.match_1]? = none) (hc : st.constants[`Unit.unit]? = none)
    (hR : Reg st) :
    (visitExpr (m := PureM) (n + 46) fVal).runPure st ⟨L, lsA, none, cfg, dc⟩ pc ⟨10⟩ =
      .ok ((fVL, stMt st), ⟨22⟩) :=
  lam_run (by krfl) fun _ => lam_run (by krfl) fun _ => lam_run (by krfl) fun _ =>
    fB_run (n := n) hm hc hR

/-- The state after `add._f`. -/
abbrev stF (st : ErasureState) : ErasureState := stDef (stMt st) `add._f fVL

/-- `visitMutual` on `add._f`. Reference: as `visitMutual_go`. -/
theorem visitMutual_f {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)}
    (hm : st.constants[`add.match_1]? = none) (hc : st.constants[`Unit.unit]? = none)
    (hR : Reg st) :
    (visitMutual (m := PureM) (n + 47) `add._f).runPure st ⟨L, lsA, F, cfg, dc⟩ pc ⟨10⟩ =
      .ok (((), stF st), ⟨22⟩) := by
  rw [visitMutual]
  iterate 8 apply bind_ok rfl
  refine bind_ok (a := fVL) (st' := stMt st) (ps' := ⟨22⟩) ?_ ?_
  · rw [runPure_withReader]
    apply bind_ok rfl
    refine bind_ok (a := fVal) (st' := st) (ps' := ⟨10⟩) rfl ?_
    exact fV_run (n := n) hm hc hR
  rfl

/-- `get_constant_kername` on `add._f`, not yet erased. Reference: `erase_global_deps`
(`MR E/ErasureFunction.v:1602`). -/
theorem kername_f {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)}
    (hf : st.constants[`add._f]? = none)
    (hm : st.constants[`add.match_1]? = none) (hc : st.constants[`Unit.unit]? = none)
    (hR : Reg st) :
    (get_constant_kername (m := PureM) (n + 48) `add._f).runPure st ⟨L, lsA, F, cfg, dc⟩ pc ⟨10⟩ =
      .ok ((toKername `add._f, stF st), ⟨22⟩) := by
  rw [get_constant_kername]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, hf]
  apply bind_ok (visitMutual_f hm hc hR)
  apply bind_ok rfl
  simp only [stF, stDef, Std.HashMap.getElem?_insert_self]
  rfl

/-! ## `add` and the term -/

/-- `add._f n` in `add`'s body. -/
def fApp : Expr := .app (.const `add._f []) (xv 0)

theorem withApp_fApp {γ : Sort _} (k : Expr → Array Expr → γ) :
    fApp.withApp k = k (.const `add._f []) #[xv 0] := by krfl

/-- `visitExpr` on `add._f n`, `add._f` not erased. Reference: the `tConst` and `tApp` cases of
`erase` (`MR E/ErasureFunction.v:999`, `:1006`). -/
theorem fApp_run {n : Nat} {L : LocalContext} (hf : st.constants[`add._f]? = none)
    (hm : st.constants[`add.match_1]? = none) (hc : st.constants[`Unit.unit]? = none)
    (hR : Reg st) :
    (visitExpr (m := PureM) (n + 52) fApp).runPure st ⟨L, lsA, none, cfg, dc⟩ pc ⟨10⟩ =
      .ok ((.app (.const (toKername `add._f)) (.fvar (xf 0)), stF st), ⟨22⟩) := by
  rw [fApp, visitExpr, ← fApp]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ⟨10⟩) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 50) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_fApp]
  refine bind_ok (a := none) (st' := st) (ps' := ⟨10⟩) (by krfl) ?_
  refine bind_ok (a := none) (st' := st) (ps' := ⟨10⟩) (by krfl) ?_
  refine bind_ok (a := some (.defnInfo add_f)) (st' := st) (ps' := ⟨10⟩) (by krfl) ?_
  refine bind_ok (a := .const (toKername `add._f)) (st' := stF st) (ps' := ⟨22⟩) ?_ ?_
  · rw [visitConst]
    apply bind_ok rfl
    refine bind_ok (kername_f (n := n) hf hm hc hR) ?_
    rfl
  refine appArgs_cons (as := []) (r := .fvar (xf 0)) (st' := stF st) (ps' := ⟨22⟩) (by krfl) ?_
  exact appArgs_nil

/-- `add`'s body. -/
def aB : Expr := .app (.app (.app (.const `N.brecOn [l1]) motN) (xv 1)) fApp

theorem withApp_aB {γ : Sort _} (k : Expr → Array Expr → γ) :
    aB.withApp k = k (.const `N.brecOn [l1]) #[motN, xv 1, fApp] := by krfl

/-- The state after `add`'s body, from the empty state. -/
abbrev stAB : ErasureState := stF (stBr {})

/-- The erasure of `add`'s body. -/
def aBL : LBTerm :=
  .app (.app (.app (.const (toKername `N.brecOn)) .box) (.fvar (xf 1)))
    (.app (.const (toKername `add._f)) (.fvar (xf 0)))

/-- `visitExpr` on `add`'s body `N.brecOn (fun m => N) m (add._f n)` from the empty state: the λ□
constants of `N.brecOn` (erased with `N.brecOn.go`, registering `PProd`, `N` and `PUnit`) and of
`add._f` (erased with `add.match_1` and `Unit.unit`). Reference: the `tConst` and `tApp` cases of
`erase` (`MR E/ErasureFunction.v:999`, `:1006`). -/
theorem aB_run {n : Nat} {L : LocalContext} :
    (visitExpr (m := PureM) (n + 58) aB).runPure {} ⟨L, lsA, none, cfg, dc⟩ pc ⟨2⟩ =
      .ok ((aBL, stAB), ⟨22⟩) := by
  have hR : Reg (stBr {}) := ⟨by stfact, by stfact, by stfact⟩
  rw [aB, visitExpr, ← aB]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := {}) (ps' := ⟨2⟩) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 56) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_aB]
  refine bind_ok (a := none) (st' := {}) (ps' := ⟨2⟩) (by krfl) ?_
  refine bind_ok (a := none) (st' := {}) (ps' := ⟨2⟩) (by krfl) ?_
  refine bind_ok (a := some (.defnInfo N_brecOn)) (st' := {}) (ps' := ⟨2⟩) (by krfl) ?_
  refine bind_ok (a := .const (toKername `N.brecOn)) (st' := stBr {}) (ps' := ⟨10⟩) ?_ ?_
  · rw [visitConst]
    apply bind_ok rfl
    refine bind_ok (kername_brecOn (n := n) Std.HashMap.getElem?_empty Std.HashMap.getElem?_empty
      Std.HashMap.getElem?_empty Std.HashMap.getElem?_empty Std.HashMap.getElem?_empty) ?_
    rfl
  refine appArgs_cons (as := [xv 1, fApp]) (r := .box) (st' := stBr {}) (ps' := ⟨10⟩) (by krfl) ?_
  refine appArgs_cons (as := [fApp]) (r := .fvar (xf 1)) (st' := stBr {}) (ps' := ⟨10⟩) (by krfl) ?_
  refine appArgs_cons (as := []) (fApp_run (n := n + 2) (by stfact) (by stfact) (by stfact) hR) ?_
  exact appArgs_nil

/-- The erasure of `add`'s value. -/
def addVL : LBTerm :=
  .lambda (binderNameOf `n) (_root_.abstract (xf 0) (.lambda (binderNameOf `m)
    (_root_.abstract (xf 1) aBL)))

/-- `visitExpr` on `add`'s value from the empty state. Reference: the `tLambda` case of `erase`
(`MR E/ErasureFunction.v:1003`). -/
theorem addV_run {n : Nat} {L : LocalContext} :
    (visitExpr (m := PureM) (n + 62) addVal).runPure {} ⟨L, [], none, cfg, dc⟩ pc ⟨0⟩ =
      .ok ((addVL, stAB), ⟨22⟩) :=
  lam_run (by krfl) fun _ => lam_run (by krfl) fun _ => aB_run (n := n)

/-- The state after `add`. -/
abbrev stAdd : ErasureState := stDef stAB `add addVL

/-- `visitMutual` on `add`. Reference: as `visitMutual_go`. -/
theorem visitMutual_add {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)} :
    (visitMutual (m := PureM) (n + 63) `add).runPure {} ⟨L, [], F, cfg, dc⟩ pc ⟨0⟩ =
      .ok (((), stAdd), ⟨22⟩) := by
  rw [visitMutual]
  iterate 8 apply bind_ok rfl
  refine bind_ok (a := addVL) (st' := stAB) (ps' := ⟨22⟩) ?_ ?_
  · rw [runPure_withReader]
    apply bind_ok rfl
    refine bind_ok (a := addVal) (st' := {}) (ps' := ⟨0⟩) rfl ?_
    exact addV_run (n := n)
  rfl

/-- `get_constant_kername` on `add` from the empty state. Reference: `erase_global_deps`
(`MR E/ErasureFunction.v:1602`). -/
theorem kername_add {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)} :
    (get_constant_kername (m := PureM) (n + 64) `add).runPure {} ⟨L, [], F, cfg, dc⟩ pc ⟨0⟩ =
      .ok ((toKername `add, stAdd), ⟨22⟩) := by
  rw [get_constant_kername]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty]
  apply bind_ok visitMutual_add
  apply bind_ok rfl
  simp only [stAdd, stDef, Std.HashMap.getElem?_insert_self]
  rfl

theorem withApp_e {γ : Sort _} (k : Expr → Array Expr → γ) :
    e.withApp k = k (.const `add []) #[mj, mj] := by krfl

/-- The erasure of the major `N.s N.z`. -/
theorem mj_run {n : Nat} {L : LocalContext} {st : ErasureState}
    (h : st.inductives[`N]? = some (iidN, masksN)) :
    (visitExpr (m := PureM) (n + 12) mj).runPure st ⟨L, [], none, cfg, .anonymous⟩ pc ⟨22⟩ =
      .ok ((NVR.mjL, st), ⟨22⟩) :=
  sArg_run (by krfl) (by krfl) (cZ_run (n := n + 1) h) h

/-- `visitExpr` on `e = add (N.s N.z) (N.s N.z)`: the λ□ constant of `add`, erased on the way with
its dependencies, applied to the erased arguments. Reference: the `tConst` and `tApp` cases of
`erase` (`MR E/ErasureFunction.v:999`, `:1006`), with `erase_global_deps`
(`MR E/ErasureFunction.v:1602`). -/
theorem e_run {n : Nat} {L : LocalContext} :
    (visitExpr (m := PureM) (n + 68) e).runPure {} ⟨L, [], none, cfg, .anonymous⟩ pc ⟨0⟩ =
      .ok ((eL, stAdd), ⟨22⟩) := by
  have hN : stAdd.inductives[`N]? = some (iidN, masksN) := by stfact
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
  refine bind_ok (a := .const (toKername `add)) (st' := stAdd) (ps' := ⟨22⟩) ?_ ?_
  · rw [visitConst]
    apply bind_ok rfl
    refine bind_ok (kername_add (n := n)) ?_
    rfl
  refine appArgs_cons (as := [mj]) (mj_run (n := n + 52) hN) ?_
  refine appArgs_cons (as := []) (mj_run (n := n + 52) hN) ?_
  exact appArgs_nil

/-! ## The run on NV-S -/

/-- The constants `#erase` marks for inlining on NV-S: the `@[inline]` definitions it erases,
the last first. -/
def inl0 : List Kername := [toKername `Unit.unit, toKername `add.match_1]

/-- The program `#erase` emits for NV-S. -/
def p0 : Program :=
  .untyped [(toKername `add, .constantDecl ⟨some addVL⟩),
    (toKername `add._f, .constantDecl ⟨some fVL⟩),
    (toKername `add.match_1, .constantDecl ⟨some matchVL⟩),
    (toKername `Unit.unit, .constantDecl ⟨some unitL⟩),
    (toKername `N.brecOn, .constantDecl ⟨some brecOnVL⟩),
    (toKername `N.brecOn.go, .constantDecl ⟨some goVL⟩),
    (mutualBlockKername [`PUnit], .inductiveDecl ⟨.finite, 0, [bodyPU]⟩),
    (mutualBlockKername [`N], .inductiveDecl ⟨.finite, 0, [bodyN]⟩),
    (mutualBlockKername [`PProd], .inductiveDecl ⟨.finite, 2, [bodyPP]⟩)] (some eL)

/-- The pure path on NV-S's closure returns `p0` and `inl0`. Reference: `erase`
(`MR E/ErasureFunction.v:989`) and `erase_global_deps` (`MR E/ErasureFunction.v:1602`). -/
theorem hpure : erasePure view cfg D e = .ok (p0, inl0) := by
  rw [erasePure, show travFuel = (travFuel - 68) + 68 by decide]
  rw [show ((visitExpr (m := PureM) (travFuel - 68 + 68) e).runPure {} { «config» := cfg }
    ⟨D, view⟩ {}) = .ok ((eL, stAdd), ⟨22⟩) from e_run]
  krfl

/-- `#erase`'s entry point on NV-S returns `p0` and `inl0`. Reference: the hypotheses
`erase … = t'` and `erase_global_deps … = Σ'` of `erase_correct`
(`MR E/ErasureFunctionProperties.v:657`). -/
theorem hrun : eraseEntry view cfg e = pure (p0, inl0) := by
  simp only [eraseEntry, route, hcollect, hpure]

end EraseProof.Test.NVS
