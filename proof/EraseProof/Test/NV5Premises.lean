import EraseProof.Statements
import EraseProof.Test.NV5Data
import EraseProof.Test.NV1Premises
import EraseProof.Test.NVKit

/-!
# NV-5: the hypotheses of the final theorem

Each hypothesis of `erase_correct_statement` holds on the program of `Test/NV5Data.lean`, each
stated as the theorem of that name; `hev` goes through `SrcEval.zeta` (the `let`),
`SrcEval.proj` (`p.1` of the structure value), `SrcEval.frozenApp` (`wrap`'s `f B.t` with `f`
erased), `SrcEval.delta`, `SrcEval.beta` and `SrcEval.ctor`. `hfrag` and `hrun` are the shipping
`collectDeps`/`eraseEntry` evaluated one traversal call at a time (`Test/Run.lean`). The kernel
checks everything but the equation of the pure fold inside `hacc`, its premise `hfold`, which a
`#guard` checks by compiled evaluation (DV-40): every con-leche run on the terms is evaluated by
the kernel (`krfl`).
-/

open Lean Erasure EraseProof EraseProof.Test EraseProof.Test.NV5

namespace EraseProof.Test.NV5

open EraseProof.Test.NV1 (tB cT B_ind Bf_ctor Bt_ctor B_rec kRecType kRule kB nm nm2 iidB masksB bodyB stB)

/-! ## con-leche's environment -/

def full : List ConLeche.Declaration := (DeclsOf? P).getD []

def envNV5 : ConLeche.Env :=
  ⟨[ .defnInfo (cvC (.defnInfo wrap_def)) (cl wrapVal) (.regular 1)
   , .recInfo (cvC (.recInfo W_rec)) 3 3 false [⟨Name.toCL `W.mk, 2, .plain, cl W_rec.rules[0]!.rhs⟩]
   , .ctorInfo (cvC (.ctorInfo W_mk)) 1 2 (Name.toCL `W)
   , .indInfo (cvC (.inductInfo W_ind))
       { eta := true, all := [Name.toCL `W], nparams := 1, ctors := [Name.toCL `W.mk], neverZero := true }
   , .recInfo ⟨nm2 "B" "rec", [nm "u"], kRecType⟩ 3 3 false [kRule "f" 1, kRule "t" 0]
   , .ctorInfo ⟨nm2 "B" "t", [], kB⟩ 0 0 (nm "B")
   , .ctorInfo ⟨nm2 "B" "f", [], kB⟩ 0 0 (nm "B")
   , .indInfo ⟨nm "B", [], .sort (.succ .zero)⟩
       { all := [nm "B"], ctors := [nm2 "B" "f", nm2 "B" "t"], neverZero := true } ],
   [{ structName := Name.toCL `W, levelParams := [Name.toCL `u], numParams := 1, ctor := Name.toCL `W.mk,
      numFields := 2, bodies := #[cl tB, .bvar 1] }]⟩

#guard match ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified ConLeche.checkFuel) []
    full with
  | .ok env => decide (env.consts = envNV5.consts) && decide (env.tables = envNV5.tables)
  | .error _ => false

/-! ## `hacc`, `hty`, `hclean`, `hview`, `hfrag`, `hnopre` -/

theorem decls : DeclsOf? P = some full := by krfl

theorem hacc (hfold : ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified ConLeche.checkFuel)
    [] full = .ok envNV5) : ConLecheAccepts P envNV5 :=
  ⟨full, decls, hfold, by krfl, by krfl⟩

theorem hty : CLTyped envNV5 e := typed_of 100 (by krfl)

theorem hclean : NoMarkKeys e = true := by krfl

theorem hview : ViewAgrees view P := by
  intro ci h
  simp only [P, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> refine ⟨rfl, fun cfg pre hp => ?_⟩ <;>
    rw [preDef_none' (by krfl)] at hp <;> cases hp

theorem hfrag : collectDeps view cfg e = .ok D := by krfl

theorem hnopre : NoPreDefs view cfg D := by unfold NoPreDefs; decide

/-! ## `hrun`: the traversal, one call at a time -/

def pc : PureCtx := ⟨D, view⟩

variable {st : ErasureState} {ps : PureState} {dc : Name} {L : LocalContext}

def fx (i : Nat) : FVarId := ⟨.num `_pure i⟩
/-- The let-local `p`, and `Y`, `f` under it while `wrap`'s value is erased. -/
def lp : Local := ⟨fx 0, `p, tW l2 tyT, some (valOf tyT famF)⟩
def lsW : List Local := [⟨fx 2, `f, .forallE `x tB (.fvar (fx 1)) .default, none⟩, ⟨fx 1, `Y, .sort lu, none⟩, lp]

theorem register_B_new (h : st.inductives[`B]? = none) :
    (register_inductive (m := PureM) B_ind).runPure st ⟨L, lsW, none, cfg, dc⟩ pc ps =
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

def iidW : InductiveId := ⟨mutualBlockKername [`W], 0⟩
def masksW : InductiveArgMasks := [#[.keep, .keep]]
def bodyW : OneInductiveBody :=
  { name := toString `W, propositional := false, ctors := [⟨toString `W.mk, 2⟩], projs := [⟨"0"⟩, ⟨"1"⟩] }

def stW (st : ErasureState) : ErasureState :=
  { st with
    inductives := st.inductives.insert `W (iidW, masksW)
    gdecls := (mutualBlockKername [`W], .inductiveDecl ⟨.finite, 1, [bodyW]⟩) :: st.gdecls }

theorem register_W_new (h : st.inductives[`W]? = none) :
    (register_inductive (m := PureM) W_ind).runPure st ⟨L, lsW, none, cfg, dc⟩ pc ps =
      .ok (((iidW, masksW), stW st), ps) := by
  rw [register_inductive]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, show W_ind.name = `W from rfl, h]
  apply bind_ok (a := [bodyW]) (st' := { st with inductives := st.inductives.insert `W (iidW, masksW) })
    (ps' := ps) (by krfl)
  apply bind_ok rfl
  apply bind_ok rfl
  simp only [Std.HashMap.getElem?_insert_self]
  rfl

/-- `register_inductive` on a registered inductive. -/
theorem register_found {iv : InductiveVal} {r : InductiveId × InductiveArgMasks} {tc : TravCtx}
    (h : st.inductives[iv.name]? = some r) :
    (register_inductive (m := PureM) iv).runPure st tc pc ps = .ok ((r, st), ps) := by
  rw [register_inductive]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, h]
  rfl

/-- `B.t` under `Y`, `f`, with `B` registered by `hr`. -/
theorem cT_run {n : Nat} {st' : ErasureState}
    (hr : (register_inductive (m := PureM) B_ind).runPure st ⟨L, lsW, none, cfg, dc⟩ pc ps =
      .ok (((iidB, masksB), st'), ps)) :
    (visitExpr (m := PureM) (n + 6) cT).runPure st ⟨L, lsW, none, cfg, dc⟩ pc ps =
      .ok ((.construct iidB 1 [], st'), ps) := by
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
  apply bind_ok hr
  simp only [toArray_toSubarray]
  krfl

/-- `f B.t` under `Y`, `f`, `B` registered. -/
def appL : LBTerm := .app (.fvar (fx 2)) (.construct iidB 1 [])

theorem app_run {n : Nat} (h : st.inductives[`B]? = some (iidB, masksB)) :
    (visitExpr (m := PureM) (n + 9) (.app (.fvar (fx 2)) cT)).runPure st ⟨L, lsW, none, cfg, dc⟩ pc ps =
      .ok ((appL, st), ps) := by
  rw [visitExpr]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ps) (by krfl) ?_
  rw [visitApp, ite_eq_right_of_eq_false _ _ (eq_false (by simp)), withApp_app1 _ _ _ rfl]
  refine bind_ok (a := .fvar (fx 2)) (st' := st) (ps' := ps) (by krfl) ?_
  rw [visitAppArgs, ← Array.foldlM_toList]
  simp only [List.foldlM_cons, List.foldlM_nil]
  refine bind_ok (a := appL) (st' := st) (ps' := ps) ?_ rfl
  apply bind_ok (cT_run (n := n) (register_found h))
  rfl

/-- `W.mk Y B.t (f B.t)`: `W.mk □ B.t (f B.t)`, registering `W`, then `B`. -/
def mkWL : LBTerm := .app (.app (.app (.construct iidW 0 []) .box) (.construct iidB 1 [])) appL

theorem stW_B (h : st.inductives[`B]? = none) : (stW st).inductives[`B]? = none := by
  simp only [stW, Std.HashMap.getElem?_insert]; simpa using h

theorem mkW_run {n : Nat} (hW : st.inductives[`W]? = none) (hB : st.inductives[`B]? = none) :
    (visitConstructor (m := PureM) (n + 11) `W.mk #[.fvar (fx 1), cT, .app (.fvar (fx 2)) cT]).runPure st
      ⟨L, lsW, none, cfg, dc⟩ pc ps = .ok ((mkWL, stB (stW st)), ps) := by
  rw [visitConstructor]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok (register_W_new hW)
  simp only [Subarray.copy_eq_toArray, toArray_toSubarray]
  refine bind_ok (a := #[.keep, .keep]) (st' := stW st) (ps' := ps) rfl ?_
  refine bind_ok (a := false) (st' := stW st) (ps' := ps) rfl ?_
  apply bind_ok rfl
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  apply bind_ok rfl
  split
  · rename_i h; simp at h
  · rename_i h; simp at h
  all_goals
    rw [show #[.fvar (fx 1), cT, .app (.fvar (fx 2)) cT].extract 0 W_mk.numParams ++
        filter #[ConstructorArgRelevance.keep, .keep]
        (#[.fvar (fx 1), cT, .app (.fvar (fx 2)) cT].extract W_mk.numParams (W_mk.numParams + W_mk.numFields)) ++
        #[.fvar (fx 1), cT, .app (.fvar (fx 2)) cT].extract (W_mk.numParams + W_mk.numFields) =
        #[.fvar (fx 1), cT, .app (.fvar (fx 2)) cT] by krfl,
      show W_mk.cidx = 0 from rfl, visitAppArgs, ← Array.foldlM_toList]
    simp only [List.foldlM_cons, List.foldlM_nil]
    refine bind_ok (a := .app (.construct iidW 0 []) .box) (st' := stW st) (ps' := ps) (by krfl) ?_
    refine bind_ok (a := .app (.app (.construct iidW 0 []) .box) (.construct iidB 1 []))
      (st' := stB (stW st)) (ps' := ps) ?_ ?_
    · apply bind_ok (cT_run (n := n + 3) (register_B_new (stW_B hB)))
      rfl
    refine bind_ok (a := mkWL) (st' := stB (stW st)) (ps' := ps) ?_ rfl
    apply bind_ok (app_run (n := n) (by simp [stB]))
    rfl

theorem withApp_mkW {γ : Sort _} (k : Expr → Array Expr → γ) :
    (mkW lu (.fvar (fx 1)) cT (.app (.fvar (fx 2)) cT)).withApp k =
      k (.const `W.mk [lu]) #[.fvar (fx 1), cT, .app (.fvar (fx 2)) cT] := by krfl

theorem body_run {n : Nat} (hW : st.inductives[`W]? = none) (hB : st.inductives[`B]? = none) :
    (visitExpr (m := PureM) (n + 15) (mkW lu (.fvar (fx 1)) cT (.app (.fvar (fx 2)) cT))).runPure st
      ⟨L, lsW, none, cfg, dc⟩ pc ps = .ok ((mkWL, stB (stW st)), ps) := by
  have he : mkW lu (.fvar (fx 1)) cT (.app (.fvar (fx 2)) cT) =
    .app (mkAppN (.const `W.mk [lu]) #[.fvar (fx 1), cT]) (.app (.fvar (fx 2)) cT) := rfl
  rw [he, visitExpr, ← he]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ps) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 13) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_mkW]
  refine bind_ok (a := none) (st' := st) (ps' := ps) (by krfl) ?_
  refine bind_ok (a := some 3) (st' := st) (ps' := ps) (by krfl) ?_
  change (withAppEtaToMinArity (m := PureM) (n + 12) _ 3 _).runPure _ _ _ _ = _
  rw [withAppEtaToMinArity]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := tW lu (.fvar (fx 1))) (st' := st) (ps' := ps) (by krfl) ?_
  rw [withApp_mkW, withAppEtaToMinArity.go, ite_eq_left_of_eq_true _ _ (by decide)]
  exact mkW_run (n := n + 1) hW hB

/-- `wrap`'s value: `fun Y f => W.mk □ B.t (f B.t)`. -/
def wrapL : LBTerm :=
  .lambda (binderNameOf `Y) (_root_.abstract (fx 1) (.lambda (binderNameOf `f) (_root_.abstract (fx 2) mkWL)))

theorem wrapVal_run {n : Nat} (hW : st.inductives[`W]? = none) (hB : st.inductives[`B]? = none) :
    (visitExpr (m := PureM) (n + 19) wrapVal).runPure st ⟨L, [lp], none, cfg, dc⟩ pc ⟨1⟩ =
      .ok ((wrapL, stB (stW st)), ⟨3⟩) := by
  rw [wrapVal, visitExpr, ← wrapVal]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ⟨1⟩) (by krfl) ?_
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [visitLambda]
  refine bind_ok (a := fx 1) (st' := st) (ps' := ⟨2⟩) rfl ?_
  refine bind_ok (a := .lambda (binderNameOf `f) (_root_.abstract (fx 2) mkWL)) (st' := stB (stW st))
    (ps' := ⟨3⟩) ?_ (by krfl)
  rw [show Backend.instantiate1 PureM (.lam `f fTy (mkW lu (.bvar 1) cT (.app (.bvar 0) cT)) .default)
    (.fvar (fx 1)) = .lam `f (.forallE `x tB (.fvar (fx 1)) .default)
      (mkW lu (.fvar (fx 1)) cT (.app (.bvar 0) cT)) .default by krfl, visitExpr]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ⟨2⟩) (by krfl) ?_
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [visitLambda]
  refine bind_ok (a := fx 2) (st' := st) (ps' := ⟨3⟩) rfl ?_
  refine bind_ok (a := mkWL) (st' := stB (stW st)) (ps' := ⟨3⟩) ?_ (by krfl)
  rw [show Backend.instantiate1 PureM (mkW lu (.fvar (fx 1)) cT (.app (.bvar 0) cT)) (.fvar (fx 2)) =
    mkW lu (.fvar (fx 1)) cT (.app (.fvar (fx 2)) cT) by krfl]
  exact body_run (n := n) hW hB

def knWrap : Kername := toKername `wrap

/-- The state after erasing `wrap`. -/
def stWrap (st : ErasureState) : ErasureState :=
  { stB (stW st) with
    constants := (stB (stW st)).constants.insert `wrap knWrap
    gdecls := (knWrap, .constantDecl ⟨some wrapL⟩) :: (stB (stW st)).gdecls }

theorem kername_wrap_run {n : Nat} (hc : st.constants[`wrap]? = none) (hW : st.inductives[`W]? = none)
    (hB : st.inductives[`B]? = none) :
    (get_constant_kername (m := PureM) (n + 21) `wrap).runPure st ⟨L, [lp], none, cfg, dc⟩ pc ⟨1⟩ =
      .ok ((knWrap, stWrap st), ⟨3⟩) := by
  rw [get_constant_kername]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, hc]
  refine bind_ok (a := ()) (st' := stWrap st) (ps' := ⟨3⟩) ?_ ?_
  · rw [visitMutual]
    apply bind_ok rfl
    apply bind_ok rfl
    apply bind_ok rfl
    apply bind_ok rfl
    apply bind_ok rfl
    apply bind_ok rfl
    apply bind_ok rfl
    apply bind_ok rfl
    refine bind_ok (a := wrapL) (st' := stB (stW st)) (ps' := ⟨3⟩) ?_ ?_
    · rw [runPure_withReader]
      apply bind_ok rfl
      refine bind_ok (a := wrapVal) (st' := st) (ps' := ⟨1⟩) rfl ?_
      exact wrapVal_run (L := L) hW hB
    rfl
  apply bind_ok rfl
  simp only [stWrap, Std.HashMap.getElem?_insert_self]
  rfl

theorem withApp_val {γ : Sort _} (k : Expr → Array Expr → γ) :
    (valOf tyT famF).withApp k = k (.const `wrap [l2]) #[tyT, famF] := by krfl

/-- The value of `p`: `wrap □ □`. -/
def valL : LBTerm := .app (.app (.const knWrap) .box) .box

theorem val_run {n : Nat} (hc : st.constants[`wrap]? = none) (hW : st.inductives[`W]? = none)
    (hB : st.inductives[`B]? = none) :
    (visitExpr (m := PureM) (n + 25) (valOf tyT famF)).runPure st ⟨L, [lp], none, cfg, dc⟩ pc ⟨1⟩ =
      .ok ((valL, stWrap st), ⟨3⟩) := by
  have he : valOf tyT famF = .app (.app (.const `wrap [l2]) tyT) famF := rfl
  rw [he, visitExpr, ← he]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ⟨1⟩) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 23) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_val]
  refine bind_ok (a := none) (st' := st) (ps' := ⟨1⟩) (by krfl) ?_
  refine bind_ok (a := none) (st' := st) (ps' := ⟨1⟩) (by krfl) ?_
  refine bind_ok (a := some (.defnInfo wrap_def)) (st' := st) (ps' := ⟨1⟩) (by krfl) ?_
  refine bind_ok (a := .const knWrap) (st' := stWrap st) (ps' := ⟨3⟩) ?_ (by krfl)
  rw [visitConst]
  apply bind_ok rfl
  apply bind_ok (kername_wrap_run hc hW hB)
  rfl

theorem stWrap_W : (stWrap st).inductives[`W]? = some (iidW, masksW) := by
  rw [show (stWrap st).inductives = (st.inductives.insert `W (iidW, masksW)).insert `B (iidB, masksB)
    from rfl, Std.HashMap.getElem?_insert]
  exact Std.HashMap.getElem?_insert_self

/-- `p.1`: the projection of the first relevant field. -/
def projL : LBTerm := .proj ⟨iidW, 1, 0⟩ (.fvar (fx 0))

theorem proj_run {n : Nat} (h : st.inductives[`W]? = some (iidW, masksW)) :
    (visitExpr (m := PureM) (n + 3) (.proj `W 0 (.fvar (fx 0)))).runPure st ⟨L, [lp], none, cfg, dc⟩ pc ps =
      .ok ((projL, st), ps) := by
  rw [visitExpr]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ps) (by krfl) ?_
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [visitProj]
  apply bind_ok rfl
  apply bind_ok (register_found (iv := W_ind) h)
  simp only [toArray_toSubarray]
  krfl

/-- The erasure of `e`: `let p := wrap □ □ in p.1`. -/
def eL : LBTerm := .letIn (binderNameOf `p) valL (_root_.abstract (fx 0) projL)

theorem e_run {n : Nat} (hc : st.constants[`wrap]? = none) (hW : st.inductives[`W]? = none)
    (hB : st.inductives[`B]? = none) :
    (visitExpr (m := PureM) (n + 30) e).runPure st ⟨L, [], none, cfg, dc⟩ pc ⟨0⟩ =
      .ok ((eL, stWrap st), ⟨3⟩) := by
  rw [e, letOf, visitExpr, ← letOf, ← e]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [visitLet]
  refine bind_ok (a := fx 0) (st' := st) (ps' := ⟨1⟩) rfl ?_
  rw [runPure_withReader]
  refine bind_ok (a := valL) (st' := stWrap st) (ps' := ⟨3⟩) (val_run (n := n + 3) hc hW hB) ?_
  rw [show Backend.instantiate1 PureM (.proj `W 0 (.bvar 0)) (.fvar (fx 0)) = .proj `W 0 (.fvar (fx 0))
    by krfl]
  refine bind_ok (a := projL) (st' := stWrap st) (ps' := ⟨3⟩) (proj_run (n := n + 25) stWrap_W) ?_
  krfl

def p0 : Program :=
  .untyped [(knWrap, .constantDecl ⟨some wrapL⟩),
    (mutualBlockKername [`B], .inductiveDecl ⟨.finite, 0, [bodyB]⟩),
    (mutualBlockKername [`W], .inductiveDecl ⟨.finite, 1, [bodyW]⟩)] (some eL)

theorem hpure : erasePure view cfg D e = .ok (p0, []) := by
  rw [erasePure, show travFuel = (travFuel - 30) + 30 by decide]
  rw [show ((visitExpr (m := PureM) (travFuel - 30 + 30) e).runPure {} { «config» := cfg }
    ⟨D, view⟩ {}) = .ok ((eL, stWrap {}), ⟨3⟩) from
      e_run Std.HashMap.getElem?_empty Std.HashMap.getElem?_empty Std.HashMap.getElem?_empty]
  rfl

theorem hrun : eraseEntry view cfg e = pure (p0, []) := by
  simp only [eraseEntry, route, hfrag, hpure]

/-! ## `hmark`: the input marked; `wrap`'s value marked at its own level -/

/-- `let p := wrap □Type □(fun _ => B); p.1` -/
def valM : Expr := valOf (markErase tyT) (markErase famF)
def eM : Expr := letOf valM

theorem mark_cT {ls : List Local} (ho : oracle D ls cT = .ok false)
    (hi : Pure.inferType ⟨D⟩ oracleFuel ls [] cT = .ok tB) : MarkOf D cfg ls cT cT :=
  MarkOf.special (c := `B.t) (us := []) (as := []) ho (by krfl) hi
    (MarkEta.sat (Nat.le_refl 0) (MarkSat.ctor (ar := 0) (as := []) (âs := []) (by krfl) (by krfl) rfl
      (by simp)))

theorem hmark : MarkOf D cfg [] e eM := by
  have h : MarkOf D cfg [] e (.letE `p (tW l2 tyT) valM (absFV (fx 0) 0 (.proj `W 0 (.fvar (fx 0)))) false) :=
    MarkOf.letE (x := fx 0) (by krfl) (fresh_of (by krfl))
    (MarkOf.constApp (c := `wrap) (us := [l2]) (as := [tyT, famF]) (âs := [markErase tyT, markErase famF])
      (by krfl) (by krfl) rfl (by
        intro i a â ha hâ
        rcases i with _ | _ | i <;> simp at ha hâ <;> subst ha hâ <;> exact MarkOf.erase (by krfl)))
    (MarkOf.proj (S := `W) (i := 0) (iv := W_ind) (by krfl) (by krfl) (MarkOf.fvar (x := fx 0) (by krfl)))
  rwa [show absFV (fx 0) 0 (.proj `W 0 (.fvar (fx 0))) = .proj `W 0 (.bvar 0) by krfl] at h

/-- `wrap`'s value marked: `fun Y f => W.mk □Y B.t (f B.t)`. -/
def wrapM (u : Level) : Expr :=
  .lam `Y (.sort u) (.lam `f fTy (mkW u (markErase (.bvar 1)) cT (.app (.bvar 0) cT)) .default) .default

theorem mark_wrap : MarkOf D cfg [] wrapVal (wrapM lu) := by
  refine mark_lam (x := fx 1) (by krfl) (fresh_of (by krfl)) (by krfl) ?_
  refine mark_lam (x := fx 2) (by krfl) (fresh_of (by krfl)) (by krfl) ?_
  refine MarkOf.special (c := `W.mk) (us := [lu]) (as := [.fvar (fx 1), cT, .app (.fvar (fx 2)) cT])
    (ar := 3) (T := tW lu (.fvar (fx 1))) (by krfl) (by krfl) (by krfl) (MarkEta.sat (by decide) ?_)
  refine MarkSat.ctor (ar := 3) (âs := [markErase (.fvar (fx 1)), cT, .app (.fvar (fx 2)) cT]) (by krfl)
    (by krfl) rfl ?_
  intro i a â ha hâ
  rcases i with _ | _ | _ | i <;> simp at ha hâ <;> subst ha hâ
  · exact MarkOf.erase (by krfl)
  · exact mark_cT (by krfl) (by krfl)
  · exact MarkOf.app (f := .fvar (fx 2)) (as := [cT]) (âs := [cT]) (by krfl) (by simp) rfl (by simp)
      (MarkOf.fvar (by krfl)) rfl (by
        intro i a â ha hâ
        rcases i with _ | i <;> simp at ha hâ <;> subst ha hâ
        exact mark_cT (by krfl) (by krfl))

/-! ## `hcert`: the input's two marks; `wrap`'s value, the closure's only erased value, and its
mark `□Y` under `Y` and `f` -/

theorem hcert : ProgCert envNV5 D cfg eM := by
  refine ⟨typedAt_of (by krfl), ⟨⟨⟨trivial, cert_of (by krfl)⟩, cert_of (by krfl)⟩, trivial⟩, ?_⟩
  intro ci hci _ v hv
  simp only [D, List.mem_cons, List.not_mem_nil, or_false] at hci
  rcases hci with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases hv
  exact ⟨_, mark_wrap, typedAt_of (by krfl), ⟨⟨⟨trivial, cert_of (by krfl)⟩, trivial⟩, trivial, trivial⟩⟩

/-! ## `hev`: `eM ⇓ B.t`, through `zeta`, `delta`, `beta` (twice), `frozenApp`, `ctor` and `proj` -/

abbrev σD : EvalEnv := evalEnvOf view cfg D

theorem not_short {x : Expr} (h : ∀ c us, x.getAppFn = .const c us → specialArity σD c = none) :
    ¬ ShortSpine σD x := by
  rintro ⟨c, us, ar, h1, h2, -⟩
  rw [h c us h1] at h2
  cases h2

theorem ev_cT : SrcEval envNV5 σD cT cT :=
  SrcEval.ctor (c := `B.t) (us := []) (cv := Bt_ctor) (as := []) (vs := []) (by krfl) rfl rfl (by simp)
    (ok_clean (F := 100) (by krfl) rfl)

/-- `wrap.{2}`'s value, marked at `u` and instantiated -/
theorem ev_wrap : SrcEval envNV5 σD (.const `wrap [l2]) (wrapM l2) :=
  SrcEval.delta (ci := .defnInfo wrap_def) (body := wrapVal) (by krfl) mark_wrap (SrcEval.atom trivial)

/-- the contractum of the first β-redex: `fun (f : B → □Type) => W.mk □□Type B.t (f B.t)` -/
def lamF : Expr :=
  .lam `f (.forallE `x tB (markErase tyT) .default) (mkW l2 (markErase (markErase tyT)) cT (.app (.bvar 0) cT))
    .default

theorem ev_beta1 : SrcEval envNV5 σD (.app (.const `wrap [l2]) (markErase tyT)) lamF :=
  SrcEval.beta (n := `Y) (A := .sort l2) (b := .lam `f fTy (mkW l2 (markErase (.bvar 1)) cT (.app (.bvar 0) cT))
    .default) (bi := .default) (not_short fun _ _ h => by cases h; krfl) ev_wrap
    (SrcEval.frozen (erasable_of (F := 100) (by krfl))) (ok_of (F := 100) (by krfl) (by krfl))
    (SrcEval.atom trivial)

/-- `p`'s value: `W.mk □□Type B.t □((fun _ => B) B.t)` -/
def valV : Expr := mkW l2 (markErase (markErase tyT)) cT (markErase (.app famF cT))

theorem ev_mk {a : Expr} (ha : SrcEval envNV5 σD a (markErase (.app famF cT))) :
    SrcEval envNV5 σD (mkW l2 (markErase (markErase tyT)) cT a) valV :=
  SrcEval.ctor (env := envNV5) (σ := σD) (c := `W.mk) (us := [l2]) (cv := W_mk) (as := [markErase (markErase tyT), cT, a])
    (vs := [markErase (markErase tyT), cT, markErase (.app famF cT)]) (by krfl) rfl rfl (by
      intro i x v hx hv
      rcases i with _ | _ | _ | i <;> simp at hx hv <;> subst hx hv
      · exact SrcEval.frozen (erasable_of (F := 100) (by krfl))
      · exact ev_cT
      · exact ha)
    (ok_of (F := 100) (by krfl) (by krfl))

/-- `□(fun _ => B) B.t ⇓ □((fun _ => B) B.t)`: an erased function applied -/
theorem ev_frozenApp : SrcEval envNV5 σD (.app (markErase famF) cT) (markErase (.app famF cT)) :=
  SrcEval.frozenApp (not_short fun _ _ h => by cases h) (SrcEval.frozen (erasable_of (F := 100) (by krfl)))
    ev_cT (erasable_of (F := 100) (by krfl)) (typed_of 100 (by krfl))

theorem ev_val : SrcEval envNV5 σD valM valV :=
  SrcEval.beta (n := `f) (A := .forallE `x tB (markErase tyT) .default)
    (b := mkW l2 (markErase (markErase tyT)) cT (.app (.bvar 0) cT)) (bi := .default)
    (not_short fun _ _ h => by cases h; krfl) ev_beta1 (SrcEval.frozen (erasable_of (F := 100) (by krfl)))
    (ok_of (F := 100) (by krfl) (by krfl)) (ev_mk ev_frozenApp)

theorem hev : SrcEval envNV5 σD eM cT :=
  SrcEval.zeta (val' := valV) ev_val (ok_of (F := 100) (by krfl) (by krfl)) (ok_of (F := 100) (by krfl) (by krfl))
    (SrcEval.proj (S := `W) (i := 0) (fs := [cT, markErase (.app famF cT)])
      (ev_mk (SrcEval.frozen (erasable_of (F := 100) (by krfl))))
      ⟨`W.mk, [l2], W_mk, [markErase (markErase tyT)], by krfl, rfl, rfl, rfl, rfl, rfl⟩ rfl
      (ok_of (F := 100) (by krfl) (by krfl)))

end EraseProof.Test.NV5
