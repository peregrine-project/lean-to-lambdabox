import EraseProof.Test.NVUCollect

/-!
# NV-U through the entry point of `#erase`

The hypothesis `hrun` of the final theorem (`MR E/ErasureFunctionProperties.v:657
erase_correct`) on NV-U (`Test/NVUData.lean`): the run of the entry point on NV-A's closure `D`
(`hcollect`, `Test/NVUCollect.lean`) under `cfgU`, evaluated one traversal call at a time
(`Test/Run.lean`), cut at every read of the traversal's maps, with NV-S's steps on any closure
(`lam_run`, `appArgs_cons`, `register_found`, `kername_found`). `e` erases `Nat.add`
(`kername_add`): `PureM.declInfo?` gives it with its compiled pre-definition `preVal` as value, its
`@[extern]` attribute is read and, under `extern := .preferLogical`, the value erased; the value
mentions `Nat.add`, so `visitMutual` takes its fixpoint branch, which binds `Nat.add` to a fresh
local (the fix variable) while it erases the value, then abstracts it (`mkDef`) and declares
`Nat.add` as the λ□ fixpoint `addFixL`. In the value, `Nat.add.match_1` is erased on the way to a
λ□ constant (`kername_match`: its `casesOn` is a λ□ `case`, which registers `Nat`), and the
recursive call `Nat.add a b` erases to the fix variable applied to `a` and `b`. The numerals erase
`OfNat.ofNat` (`kername_ofNat`: its projection registers `OfNat`) and `instOfNatNat`
(`kername_inst`), and their literals the constructor chains of `Nat` (`nat := .peano`). The program
is NV-A's (`Test/NVARun.lean`) with `Nat.add` the fixpoint and without `Nat.add._f`,
`Nat.brecOn`, `Nat.brecOn.go`, `PUnit` and `PProd`; it is the program of the regression test
`tests/regress/pure_unsafe_rec.lean` (`add.ast`). The fresh locals are numbered in the order the
traversal opens them: the fix variable (0), `Nat.add`'s `x y` (1, 2), `Nat.add.match_1`'s
(3–7) and its alternative's (8), the alternatives of the pre-definition's match (9–11),
`OfNat.ofNat`'s (12–14) and `instOfNatNat`'s (15). The locals of a body are those of its binders
on top of those of the body that refers to the definition first (`visitMutual` erases a definition
under the caller's locals).
-/

open Lean Erasure EraseProof.Test

namespace EraseProof.Test.NVU

open EraseProof.Test.NVA (P e view D pc add_def match_def matchVal mMotTy inst_def ofNat_def
  OfNat_ind OfNat_mk x13 x14 x32 x35 n58 xo lv tyU tOf cOf lit instK numK instVal ofNatVal iidOf
  masksOf bodyOf stOf projOf matchVL ofNatVL instVL eL numL withApp_sx args_s args_Of withApp_instK
  withApp_numK)
open EraseProof.Test.NVL (tN cZ cS Nat_ind iidN masksN bodyN stN natL)
open EraseProof.Test.NVS (l1 u1 xf xv loc erasable_step infer_step lam_run appArgs_nil appArgs_cons
  register_found kername_found stDef)

variable {st : ErasureState} {ps : PureState} {dc : Name}

/-! ## The inductives `Nat` and `OfNat` -/

/-- `register_inductive` on `Nat` when it is not registered. Reference: the `InductiveDecl` of
`erase_global_deps` (`MR E/ErasureFunction.v:1602`). -/
theorem register_Nat_new {L : LocalContext} {ls : List Local} {F : Option (Std.HashMap Name FVarId)}
    (h : st.inductives[`Nat]? = none) :
    (register_inductive (m := PureM) Nat_ind).runPure st ⟨L, ls, F, cfgU, dc⟩ pc ps =
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
    (register_inductive (m := PureM) OfNat_ind).runPure st ⟨L, ls, F, cfgU, dc⟩ pc ps =
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

/-! ## Locals, `Nat.succ` and the literals -/

/-- `visitExpr` on a local of `ls` that the oracle keeps. Reference: the `tRel` case of `erase`
(`MR E/ErasureFunction.v:997`). -/
theorem fvar_run {n k : Nat} {L : LocalContext} {ls : List Local}
    {F : Option (Std.HashMap Name FVarId)}
    (hE : Pure.isErasable ⟨D⟩ oracleFuel ls (xv k) = .ok false) :
    (visitExpr (m := PureM) (n + 1) (xv k)).runPure st ⟨L, ls, F, cfgU, dc⟩ pc ps =
      .ok ((.fvar (xf k), st), ps) := by
  rw [xv, visitExpr]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ps)
    (erasable_step (pc := pc) (tc := ⟨L, ls, F, cfgU, dc⟩) hE) ?_
  rfl

/-- `visitExpr` on `Nat.succ a`, `a` erased to `ra` with the state unchanged, `Nat` registered.
Reference: the `tConstruct` case of `erase` (`MR E/ErasureFunction.v:1014`). -/
theorem sArg_run {n : Nat} {a : Expr} {ra : LBTerm} {L : LocalContext} {ls : List Local}
    {F : Option (Std.HashMap Name FVarId)}
    (hE : Pure.isErasable ⟨D⟩ oracleFuel ls (.app cS a) = .ok false)
    (hT : Pure.inferType ⟨D⟩ oracleFuel ls [] (.app cS a) = .ok tN)
    (ha : (visitExpr (m := PureM) (n + 7) a).runPure st ⟨L, ls, F, cfgU, dc⟩ pc ps =
      .ok ((ra, st), ps))
    (h : st.inductives[`Nat]? = some (iidN, masksN)) :
    (visitExpr (m := PureM) (n + 12) (.app cS a)).runPure st ⟨L, ls, F, cfgU, dc⟩ pc ps =
      .ok ((.app (.construct iidN 1 []) ra, st), ps) := by
  rw [visitExpr]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ps)
    (erasable_step (pc := pc) (tc := ⟨L, ls, F, cfgU, dc⟩) hE) ?_
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
    (infer_step (pc := pc) (tc := ⟨L, ls, F, cfgU, dc⟩) hT) ?_
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
  simp only [toArray_toSubarray, show (EraseProof.Test.NVL.Succ_ctor).numParams = 0 from rfl,
    show (EraseProof.Test.NVL.Succ_ctor).numFields = 1 from rfl,
    show (EraseProof.Test.NVL.Succ_ctor).cidx = 1 from rfl]
  rw [args_s]
  refine (congrArg (fun x : EraseT PureM LBTerm => x.runPure st ⟨L, ls, F, cfgU, dc⟩ pc ps)
    (?_ : _ = visitAppArgs (m := PureM) (n + 8) (.construct iidN 1 []) #[a])).trans ?_
  · krfl
  exact appArgs_cons (as := []) ha appArgs_nil

/-- `visitExpr` on the literal `0` outside any binder, `Nat` registered: `visitLiteral` erases it as
`Nat.zero`. Reference: none (Lean's literals; `Erases.litZero`). -/
theorem lit0_run {n : Nat} {L : LocalContext} (h : st.inductives[`Nat]? = some (iidN, masksN)) :
    (visitExpr (m := PureM) (n + 4) (lit 0)).runPure st ⟨L, [], none, cfgU, dc⟩ pc ps =
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
    (ih : (visitExpr (m := PureM) (n + 1) (lit k)).runPure st ⟨L, [], none, cfgU, dc⟩ pc ps =
      .ok ((natL k, st), ps)) :
    (visitExpr (m := PureM) (n + 5) (lit (k + 1))).runPure st ⟨L, [], none, cfgU, dc⟩ pc ps =
      .ok ((natL (k + 1), st), ps) := by
  rw [lit, visitExpr]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ps) (by krfl) ?_
  change (visitLiteral (m := PureM) (n + 4) _).runPure _ _ _ _ = _
  rw [visitLiteral]
  apply bind_ok rfl
  simp only [show cfgU.nat = .peano from rfl, show ¬ (k + 1 > peanoMaxLiteral) by omega,
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
  simp only [toArray_toSubarray, show (EraseProof.Test.NVL.Succ_ctor).numParams = 0 from rfl,
    show (EraseProof.Test.NVL.Succ_ctor).numFields = 1 from rfl,
    show (EraseProof.Test.NVL.Succ_ctor).cidx = 1 from rfl]
  rw [args_s]
  refine (congrArg (fun x : EraseT PureM LBTerm => x.runPure st ⟨L, [], none, cfgU, dc⟩ pc ps)
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
    (visitExpr (m := PureM) (n + 12) (lit 2)).runPure st ⟨L, [], none, cfgU, dc⟩ pc ps =
      .ok ((natL 2, st), ps) :=
  litS_run (n := n + 7) (by decide) h (litS_run (n := n + 3) (by decide) h (lit0_run h))

theorem lit3_run {n : Nat} {L : LocalContext} (h : st.inductives[`Nat]? = some (iidN, masksN)) :
    (visitExpr (m := PureM) (n + 16) (lit 3)).runPure st ⟨L, [], none, cfgU, dc⟩ pc ps =
      .ok ((natL 3, st), ps) :=
  litS_run (n := n + 11) (by decide) h (lit2_run h)

/-! ## `Nat.add.match_1` -/

/-- The locals of the pre-definition's body: `x`, `y`. -/
def lsA : List Local := [loc 2 x14 tN, loc 1 x13 tN]

/-- The locals of `Nat.add.match_1`'s body: `motive`, `x`, `y`, `h_1`, `h_2`. -/
def lsM : List Local :=
  loc 7 `h_2 (.forallE `a tN (.forallE `b tN (.app (.app (xv 3) (.bvar 1)) (.app cS (.bvar 0)))
      .default) .default) ::
    loc 6 `h_1 (.forallE `a tN (.app (.app (xv 3) (.bvar 0)) cZ) .default) ::
    loc 5 x35 tN :: loc 4 x32 tN :: loc 3 `motive mMotTy :: lsA

/-- The motive and the alternatives of `Nat.add.match_1`'s `casesOn`. -/
def motM : Expr := .lam `x tN (.app (.app (xv 3) (xv 4)) (.bvar 0)) .default
def alt1 : Expr := .app (xv 6) (xv 4)
def alt2 : Expr := .lam n58 tN (.app (.app (xv 7) (xv 4)) (.bvar 0)) .default

/-- `Nat.add.match_1`'s body. -/
def mB : Expr := .app (.app (.app (.app (.const `Nat.casesOn [u1]) motM) (xv 5)) alt1) alt2

theorem withApp_mB {γ : Sort _} (k : Expr → Array Expr → γ) :
    mB.withApp k = k (.const `Nat.casesOn [u1]) #[motM, xv 5, alt1, alt2] := by krfl

/-- The erasures of the alternatives, `h_1 x` and, under its field, `h_2 x n`. -/
def alt1L : LBTerm := .app (.fvar (xf 6)) (.fvar (xf 4))
def alt2L : LBTerm := .app (.app (.fvar (xf 7)) (.fvar (xf 4))) (.bvar 0)

/-- `visitAlt` on the first alternative `h_1 x` (no field). Reference: the branches of the
`tCase` case of `erase` (`MR E/ErasureFunction.v:1016`). -/
theorem alt1_run {n : Nat} {L : LocalContext} :
    (visitAlt (m := PureM) (n + 10) 0 #[] [] alt1).runPure st ⟨L, lsM, none, cfgU, dc⟩ pc ⟨8⟩ =
      .ok ((([], alt1L), st), ⟨8⟩) := by
  krfl

/-- `visitAlt` on the second alternative `fun n => h_2 x n` (one field), from the counter's ninth
variable. Reference: the branches of the `tCase` case of `erase` (`MR E/ErasureFunction.v:1016`). -/
theorem alt2_run {n : Nat} {L : LocalContext} :
    (visitAlt (m := PureM) (n + 10) 1 #[.keep] [] alt2).runPure st ⟨L, lsM, none, cfgU, dc⟩ pc ⟨8⟩ =
      .ok ((([binderNameOf n58], alt2L), st), ⟨9⟩) := by
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
  .case (iidN, 0) (.fvar (xf 5)) [([], alt1L), ([binderNameOf n58], alt2L)]

/-- `visitCasesOn` on `Nat.add.match_1`'s alternatives and the discriminant `y`, `Nat` not
registered: the `casesOn` registers it. Reference: the `tCase` case of `erase`
(`MR E/ErasureFunction.v:1016`). -/
theorem visitCasesOn_run {n : Nat} {L : LocalContext} (hN : st.inductives[`Nat]? = none) :
    (visitCasesOn (m := PureM) (n + 19) Nat_ind altsM ∅ none (.fvar (xf 5))).runPure st
      ⟨L, lsM, none, cfgU, dc⟩ pc ⟨8⟩ = .ok ((caseM, stN st), ⟨9⟩) := by
  rw [visitCasesOn]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok (register_Nat_new hN)
  simp only [show Nat_ind.ctors = [`Nat.zero, `Nat.succ] from rfl, List.forIn_cons, List.forIn_nil,
    bind_assoc, altsM_z, altsM_s, Std.HashMap.getD_empty]
  refine bind_ok (a := .yield (#[([], alt1L)], ([#[.keep]] : List ConstructorArgMask)))
    (st' := stN st) (ps' := ⟨8⟩) ?_ ?_
  · apply bind_ok (alt1_run (n := n + 8))
    rfl
  refine bind_ok (a := (#[([], alt1L), ([binderNameOf n58], alt2L)],
    ([] : List ConstructorArgMask))) (st' := stN st) (ps' := ⟨9⟩) ?_ ?_
  · refine bind_ok (a := .yield (#[([], alt1L), ([binderNameOf n58], alt2L)],
      ([] : List ConstructorArgMask))) (st' := stN st) (ps' := ⟨9⟩) ?_ ?_
    · apply bind_ok (alt2_run (n := n + 8))
      rfl
    · rfl
  rfl

/-- `visitCases` on `Nat.add.match_1`'s `casesOn`: `Nat.casesOn` has one universe parameter more
than `Nat`, and the discriminant's sort is never `Prop`, so the result is the λ□ `case`.
Reference: the `tCase` case of `erase` (`MR E/ErasureFunction.v:1016`). -/
theorem visitCases_run {n : Nat} {L : LocalContext} (hN : st.inductives[`Nat]? = none) :
    (visitCases (m := PureM) (n + 22) EraseProof.Test.NVA.ciN #[motM, xv 5, alt1, alt2]).runPure st
      ⟨L, lsM, none, cfgU, dc⟩ pc ⟨8⟩ = .ok ((caseM, stN st), ⟨9⟩) := by
  rw [visitCases]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := Level.succ .zero) (st' := st) (ps' := ⟨8⟩) (by krfl) ?_
  have hr : (EraseProof.Test.NVA.ciN.altsRange.toList) = [2, 3] := by
    simp [EraseProof.Test.NVA.ciN, Nat.toList_rco_eq_ite]
  simp only [← forIn'_eq_forIn, Std.Rco.forIn'_eq_forIn'_toList, hr, List.forIn'_cons,
    List.forIn'_nil]
  refine bind_ok (a := (altsM, none, ?sEnd)) (st' := st) (ps' := ⟨8⟩) ?_ ?_
  case sEnd => exact (EraseProof.Test.NVA.ciN.altNumParams.toSubarray 2 2)
  · rfl
  refine bind_ok (a := .fvar (xf 5)) (st' := st) (ps' := ⟨8⟩) (by krfl) ?_
  simp only [show Nat_ind.ctors = [`Nat.zero, `Nat.succ] from rfl, altsM_all, ite_true]
  apply bind_ok (visitCasesOn_run (n := n + 2) hN)
  rw [show EraseProof.Test.NVA.ciN.arity = (#[motM, xv 5, alt1, alt2] : Array Expr).size from rfl,
    forIn_toSubarray_size]
  rfl

/-- `visitExpr` on `Nat.add.match_1`'s body: a saturated recognized `casesOn`. Reference: the
`tCase` case of `erase` (`MR E/ErasureFunction.v:1016`). -/
theorem mB_run {n : Nat} {L : LocalContext} (hN : st.inductives[`Nat]? = none) :
    (visitExpr (m := PureM) (n + 26) mB).runPure st ⟨L, lsM, none, cfgU, dc⟩ pc ⟨8⟩ =
      .ok ((caseM, stN st), ⟨9⟩) := by
  rw [mB, visitExpr, ← mB]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ⟨8⟩) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 24) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_mB]
  refine bind_ok (a := some EraseProof.Test.NVA.ciN) (st' := st) (ps' := ⟨8⟩) (by krfl) ?_
  change (withAppEtaToMinArity (m := PureM) (n + 23) _ 4 _).runPure _ _ _ _ = _
  rw [withAppEtaToMinArity]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := .app motM (xv 5)) (st' := st) (ps' := ⟨8⟩)
    (infer_step (pc := pc) (tc := ⟨L, lsM, none, cfgU, dc⟩) (by krfl)) ?_
  rw [withApp_mB, withAppEtaToMinArity.go]
  simp only [show (#[motM, xv 5, alt1, alt2] : Array Expr).size = 4 from rfl, ge_iff_le,
    Nat.le_refl, ↓reduceIte]
  exact visitCases_run (n := n + 1) hN

/-- The erasure of `Nat.add.match_1`'s value. -/
def matchVLU : LBTerm :=
  .lambda (binderNameOf `motive) (_root_.abstract (xf 3) (.lambda (binderNameOf x32)
    (_root_.abstract (xf 4) (.lambda (binderNameOf x35) (_root_.abstract (xf 5)
      (.lambda (binderNameOf `h_1) (_root_.abstract (xf 6)
        (.lambda (binderNameOf `h_2) (_root_.abstract (xf 7) caseM)))))))))

/-- `visitExpr` on `Nat.add.match_1`'s value, from the counter's fourth variable. Reference: the
`tLambda` case of `erase` (`MR E/ErasureFunction.v:1003`). -/
theorem matchV_run {n : Nat} {L : LocalContext} (hN : st.inductives[`Nat]? = none) :
    (visitExpr (m := PureM) (n + 36) matchVal).runPure st ⟨L, lsA, none, cfgU, dc⟩ pc ⟨3⟩ =
      .ok ((matchVLU, stN st), ⟨9⟩) :=
  lam_run (by krfl) fun _ => lam_run (by krfl) fun _ => lam_run (by krfl) fun _ =>
    lam_run (by krfl) fun _ => lam_run (by krfl) fun _ => mB_run (n := n) hN

/-- The state after `Nat.add.match_1`. -/
abbrev stMt (st : ErasureState) : ErasureState := stDef (stN st) `Nat.add.match_1 matchVLU

/-- `visitMutual` on `Nat.add.match_1`: a single, non-recursive definition without attributes,
erased to a λ□ constant, `Nat` not registered. Reference: as `visitMutual_go`
(`Test/NVSRun.lean`). -/
theorem visitMutual_match {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)}
    (hN : st.inductives[`Nat]? = none) :
    (visitMutual (m := PureM) (n + 37) `Nat.add.match_1).runPure st ⟨L, lsA, F, cfgU, dc⟩ pc ⟨3⟩ =
      .ok (((), stMt st), ⟨9⟩) := by
  rw [visitMutual]
  iterate 8 apply bind_ok rfl
  refine bind_ok (a := matchVLU) (st' := stN st) (ps' := ⟨9⟩) ?_ ?_
  · rw [runPure_withReader]
    apply bind_ok rfl
    refine bind_ok (a := matchVal) (st' := st) (ps' := ⟨3⟩) rfl ?_
    exact matchV_run (n := n) hN
  rfl

/-- `get_constant_kername` on `Nat.add.match_1`, not yet erased. Reference: `erase_global_deps`
(`MR E/ErasureFunction.v:1602`). -/
theorem kername_match {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)}
    (hm : st.constants[`Nat.add.match_1]? = none) (hN : st.inductives[`Nat]? = none) :
    (get_constant_kername (m := PureM) (n + 38) `Nat.add.match_1).runPure st ⟨L, lsA, F, cfgU, dc⟩
      pc ⟨3⟩ = .ok ((toKername `Nat.add.match_1, stMt st), ⟨9⟩) := by
  rw [get_constant_kername]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, hm]
  apply bind_ok (visitMutual_match hN)
  apply bind_ok rfl
  simp only [stMt, stDef, Std.HashMap.getElem?_insert_self]
  rfl

/-! ## `Nat.add`: the fixpoint -/

/-- The fix variables of `Nat.add`'s block: `Nat.add` bound to the local 0. -/
def fixM : Std.HashMap Name FVarId := Std.HashMap.ofList [(`Nat.add, xf 0)]

theorem fixM_add : fixM[`Nat.add]? = some (xf 0) := by
  simp only [fixM, Std.HashMap.ofList_singleton, Std.HashMap.getElem?_insert_self]

theorem fixM_add' : fixM[`Nat.add]! = xf 0 := by
  simp only [fixM, Std.HashMap.ofList_singleton, Std.HashMap.getElem!_insert_self]

theorem fixM_match : fixM[`Nat.add.match_1]? = none := by
  simp only [fixM, Std.HashMap.ofList_singleton, Std.HashMap.getElem?_insert,
    Std.HashMap.getElem?_empty]
  rfl

/-- The locals of the second alternative's body: `a`, `b`. -/
def lsB : List Local := loc 11 `b tN :: loc 10 `a tN :: lsA

/-- The recursive call `Nat.add a b` in the second alternative. -/
def callB : Expr := .app (.app (.const `Nat.add []) (xv 10)) (xv 11)

theorem withApp_callB {γ : Sort _} (k : Expr → Array Expr → γ) :
    callB.withApp k = k (.const `Nat.add []) #[xv 10, xv 11] := by krfl

/-- The erasure of the recursive call: the fix variable applied to `a` and `b`. -/
def callBL : LBTerm := .app (.app (.fvar (xf 0)) (.fvar (xf 10))) (.fvar (xf 11))

/-- `visitExpr` on the recursive call `Nat.add a b` in the fixpoint body: `visitConst` finds
`Nat.add` among the fix variables. Reference: the `tRel` case of `erase` for the fixpoint's
variable (`MR E/ErasureFunction.v:997`); DV-7. -/
theorem callB_run {n : Nat} {L : LocalContext} :
    (visitExpr (m := PureM) (n + 5) callB).runPure st ⟨L, lsB, some fixM, cfgU, dc⟩ pc ps =
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
  refine appArgs_cons (as := [xv 11]) (fvar_run (n := n) (by krfl)) ?_
  refine appArgs_cons (as := []) (fvar_run (n := n) (by krfl)) ?_
  exact appArgs_nil

/-- The pre-definition's body `Nat.add.match_1 (fun x y => Nat) x y (fun a => a)
(fun a b => Nat.succ (Nat.add a b))` under its locals. -/
def preB : Expr :=
  .app (.app (.app (.app (.app (.const `Nat.add.match_1 [l1]) motPre) (xv 1)) (xv 2)) altPre1)
    altPre2

theorem withApp_preB {γ : Sort _} (k : Expr → Array Expr → γ) :
    preB.withApp k = k (.const `Nat.add.match_1 [l1]) #[motPre, xv 1, xv 2, altPre1, altPre2] := by
  krfl

/-- The erasures of the alternatives of the pre-definition's match. -/
def altP1L : LBTerm := .lambda (binderNameOf `a) (_root_.abstract (xf 9) (.fvar (xf 9)))
def altP2L : LBTerm :=
  .lambda (binderNameOf `a) (_root_.abstract (xf 10)
    (.lambda (binderNameOf `b) (_root_.abstract (xf 11) (.app (.construct iidN 1 []) callBL))))

/-- The erasure of the pre-definition's body. -/
def preBL : LBTerm :=
  .app (.app (.app (.app (.app (.const (toKername `Nat.add.match_1)) .box) (.fvar (xf 1)))
    (.fvar (xf 2))) altP1L) altP2L

/-- `visitExpr` on the pre-definition's body from the empty state, in the fixpoint branch: the λ□
constant of `Nat.add.match_1`, erased on the way (which registers `Nat`), applied to □ and the
erased arguments, the recursive call under the second alternative erased to the fix variable.
Reference: the `tConst` and `tApp` cases of `erase` (`MR E/ErasureFunction.v:999`, `:1006`). -/
theorem preB_run {n : Nat} {L : LocalContext} :
    (visitExpr (m := PureM) (n + 42) preB).runPure {} ⟨L, lsA, some fixM, cfgU, dc⟩ pc ⟨3⟩ =
      .ok ((preBL, stMt {}), ⟨12⟩) := by
  have hN : (stMt {}).inductives[`Nat]? = some (iidN, masksN) := by
    simp only [stMt, stDef, stN, Std.HashMap.getElem?_insert_self]
  rw [preB, visitExpr, ← preB]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := {}) (ps' := ⟨3⟩) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 40) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_preB]
  refine bind_ok (a := none) (st' := {}) (ps' := ⟨3⟩) (by krfl) ?_
  refine bind_ok (a := none) (st' := {}) (ps' := ⟨3⟩) (by krfl) ?_
  refine bind_ok (a := some (.defnInfo match_def)) (st' := {}) (ps' := ⟨3⟩) (by krfl) ?_
  refine bind_ok (a := .const (toKername `Nat.add.match_1)) (st' := stMt {}) (ps' := ⟨9⟩) ?_ ?_
  · rw [visitConst]
    apply bind_ok rfl
    simp only [Option.bind_some, fixM_match]
    refine bind_ok (kername_match (n := n) Std.HashMap.getElem?_empty
      Std.HashMap.getElem?_empty) ?_
    rfl
  refine appArgs_cons (as := [xv 1, xv 2, altPre1, altPre2]) (r := .box) (st' := stMt {})
    (ps' := ⟨9⟩) (by krfl) ?_
  refine appArgs_cons (as := [xv 2, altPre1, altPre2]) (r := .fvar (xf 1)) (st' := stMt {})
    (ps' := ⟨9⟩) (by krfl) ?_
  refine appArgs_cons (as := [altPre1, altPre2]) (r := .fvar (xf 2)) (st' := stMt {})
    (ps' := ⟨9⟩) (by krfl) ?_
  refine appArgs_cons (as := [altPre2]) (r := altP1L) (st' := stMt {}) (ps' := ⟨10⟩)
    (lam_run (by krfl) fun _ => by krfl) ?_
  refine appArgs_cons (as := []) (r := altP2L) (st' := stMt {}) (ps' := ⟨12⟩)
    (lam_run (by krfl) fun _ => lam_run (by krfl) fun _ =>
      sArg_run (n := n + 22) (by krfl) (by krfl) (callB_run (n := n + 24)) hN) ?_
  exact appArgs_nil

/-- The erasure of the pre-definition, with the fix variable free. -/
def preVL : LBTerm :=
  .lambda (binderNameOf x13) (_root_.abstract (xf 1) (.lambda (binderNameOf x14)
    (_root_.abstract (xf 2) preBL)))

/-- `visitExpr` on the pre-definition from the empty state, from the counter's second variable.
Reference: the `tLambda` case of `erase` (`MR E/ErasureFunction.v:1003`). -/
theorem preV_run {n : Nat} {L : LocalContext} :
    (visitExpr (m := PureM) (n + 46) preVal).runPure {} ⟨L, [], some fixM, cfgU, dc⟩ pc ⟨1⟩ =
      .ok ((preVL, stMt {}), ⟨12⟩) :=
  lam_run (by krfl) fun _ => lam_run (by krfl) fun _ => preB_run (n := n)

/-- `Nat.add`'s declaration as `PureM.declInfo?` gives it under `cfgU`: `add_def` with the value
`preVal` (`preDef_add`). -/
def addU : DefinitionVal := { add_def with value := preVal }

/-- `Nat.add`'s λ□ fixpoint: one definition named after `Nat.add`, whose body abstracts the fix
variable from the pre-definition's erasure, recursive-argument index 0 (`mkDef`). -/
def addDefL : @FixDef LBTerm := { name := fixDefName `Nat.add, body := toBvar (xf 0) 0 preVL }
def addFixL : LBTerm := .fix [addDefL] 0

/-- `addFixL` in closed form: `tFix [⟨Nat.add, λ x y. Nat.add.match_1 □ x y (λ a. a)
(λ a b. Nat.succ (Nat.add a b)), 0⟩] 0`, the recursive call the fixpoint's variable `tRel 4`. -/
theorem addFixL_eq : addFixL = .fix [⟨fixDefName `Nat.add, .lambda (binderNameOf x13)
    (.lambda (binderNameOf x14) (.app (.app (.app (.app (.app
      (.const (toKername `Nat.add.match_1)) .box) (.bvar 1)) (.bvar 0))
      (.lambda (binderNameOf `a) (.bvar 0)))
      (.lambda (binderNameOf `a) (.lambda (binderNameOf `b)
        (.app (.construct iidN 1 []) (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))))))), 0⟩] 0 := by
  krfl

/-- `mkDef` on `Nat.add`'s erased pre-definition: the fix variable abstracted at index 0.
Reference: the bodies of `tFix` in `erase` (`MR E/ErasureFunction.v:1022`); DV-7. -/
theorem mkDef_run {L : LocalContext} {ls : List Local} :
    (mkDef (m := PureM) `Nat.add [`Nat.add] preVL).runPure st ⟨L, ls, some fixM, cfgU, dc⟩ pc ps =
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

/-- The state after `Nat.add`. -/
abbrev stAdd : ErasureState := stDef (stMt {}) `Nat.add addFixL

/-- `visitMutual` on `Nat.add` from the empty state: `PureM.declInfo?` gives `Nat.add` with its
compiled pre-definition as value; an `@[extern]` definition, which `extern := .preferLogical`
erases by that value; the value mentions `Nat.add`, so the fixpoint branch: one fresh fix variable,
the value erased under it, `mkDef`, and `Nat.add` declared as the fixpoint. Reference: the `tFix`
case of `erase` (`MR E/ErasureFunction.v:1022`) and `erase_constant_body`
(`MR E/ErasureFunction.v:1309`); the `@[extern]` test: none (DV-12); DV-7. -/
theorem visitMutual_add {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)} :
    (visitMutual (m := PureM) (n + 48) `Nat.add).runPure {} ⟨L, [], F, cfgU, dc⟩ pc ⟨0⟩ =
      .ok (((), stAdd), ⟨12⟩) := by
  rw [visitMutual]
  apply bind_ok rfl
  refine bind_ok (a := some (.defnInfo addU)) (st' := {}) (ps' := ⟨0⟩) (by krfl) ?_
  iterate 5 apply bind_ok rfl
  simp only [show pc.view.isExtern `Nat.add = true from rfl,
    show (ConstantInfo.defnInfo addU).value? true = some preVal from rfl,
    show cfgU.1 = .preferLogical from rfl]
  apply bind_ok rfl
  have hnr : ((ConstantInfo.defnInfo addU).all.length == 1 &&
      !name_occurs (m := PureM) `Nat.add ((some preVal).getD default)) = false := by krfl
  simp only [hnr, Bool.false_eq_true, ↓reduceIte]
  refine bind_ok (a := [xf 0]) (st' := {}) (ps' := ⟨1⟩) (by krfl) ?_
  rw [runPure_withReader]
  refine bind_ok (a := [addDefL]) (st' := stMt {}) (ps' := ⟨12⟩) ?_ ?_
  · rw [show (ConstantInfo.defnInfo addU).all = [`Nat.add] from rfl, List.mapM_cons, List.mapM_nil]
    simp only [show ((`Nat.add : Name) == (ConstantInfo.defnInfo addU).name) = true by krfl,
      ↓reduceIte]
    refine bind_ok (a := addDefL) (st' := stMt {}) (ps' := ⟨12⟩) ?_ rfl
    apply bind_ok rfl
    refine bind_ok (a := preVL) (st' := stMt {}) (ps' := ⟨12⟩) ?_ mkDef_run
    rw [runPure_withReader]
    apply bind_ok rfl
    refine bind_ok (a := preVal) (st' := {}) (ps' := ⟨1⟩) rfl ?_
    exact preV_run (n := n + 1)
  rfl

/-- `get_constant_kername` on `Nat.add` from the empty state. Reference: `erase_global_deps`
(`MR E/ErasureFunction.v:1602`). -/
theorem kername_add {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)} :
    (get_constant_kername (m := PureM) (n + 49) `Nat.add).runPure {} ⟨L, [], F, cfgU, dc⟩ pc ⟨0⟩ =
      .ok ((toKername `Nat.add, stAdd), ⟨12⟩) := by
  rw [get_constant_kername]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty]
  apply bind_ok visitMutual_add
  apply bind_ok rfl
  simp only [stAdd, stDef, Std.HashMap.getElem?_insert_self]
  rfl

/-! ## `OfNat.ofNat` and `instOfNatNat` -/

/-- The locals of `OfNat.ofNat`'s body: `α`, `x`, `self`. -/
def lsO : List Local :=
  [loc 14 `self (.app (.app (tOf lv) (xv 12)) (xv 13)), loc 13 xo tN, loc 12 `α tyU]

/-- `visitExpr` on `OfNat.ofNat`'s body `self.1`, `OfNat` not registered: the projection registers
it. Reference: the `tProj` case of `erase` (`MR E/ErasureFunction.v:1020`). -/
theorem projOf_run {n : Nat} {L : LocalContext} (h : st.inductives[`OfNat]? = none) :
    (visitExpr (m := PureM) (n + 4) (.proj `OfNat 0 (xv 14))).runPure st ⟨L, lsO, none, cfgU, dc⟩
      pc ps = .ok ((.proj projOf (.fvar (xf 14)), stOf st), ps) := by
  rw [visitExpr]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ps) (by krfl) ?_
  change (visitProj (m := PureM) (n + 3) `OfNat 0 (xv 14)).runPure _ _ _ _ = _
  rw [visitProj]
  apply bind_ok rfl
  apply bind_ok (register_Of_new h)
  apply bind_ok rfl
  refine bind_ok (a := .fvar (xf 14)) (st' := stOf st) (ps' := ps)
    (fvar_run (n := n + 2) (by krfl)) ?_
  simp only [toArray_toSubarray]
  rfl

/-- The erasure of `OfNat.ofNat`'s value. -/
def ofNatVLU : LBTerm :=
  .lambda (binderNameOf `α) (_root_.abstract (xf 12) (.lambda (binderNameOf xo)
    (_root_.abstract (xf 13) (.lambda (binderNameOf `self) (_root_.abstract (xf 14)
      (.proj projOf (.fvar (xf 14))))))))

/-- The state after `OfNat.ofNat`. -/
abbrev stON (st : ErasureState) : ErasureState := stDef (stOf st) `OfNat.ofNat ofNatVLU

/-- `visitMutual` on `OfNat.ofNat`. Reference: as `visitMutual_go` (`Test/NVSRun.lean`). -/
theorem visitMutual_ofNat {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)}
    (h : st.inductives[`OfNat]? = none) :
    (visitMutual (m := PureM) (n + 19) `OfNat.ofNat).runPure st ⟨L, [], F, cfgU, dc⟩ pc ⟨12⟩ =
      .ok (((), stON st), ⟨15⟩) := by
  rw [visitMutual]
  iterate 8 apply bind_ok rfl
  refine bind_ok (a := ofNatVLU) (st' := stOf st) (ps' := ⟨15⟩) ?_ ?_
  · rw [runPure_withReader]
    apply bind_ok rfl
    refine bind_ok (a := ofNatVal) (st' := st) (ps' := ⟨12⟩) rfl ?_
    exact lam_run (by krfl) fun _ => lam_run (by krfl) fun _ => lam_run (by krfl) fun _ =>
      projOf_run (n := n + 8) h
  rfl

/-- `get_constant_kername` on `OfNat.ofNat`, not yet erased. Reference: `erase_global_deps`
(`MR E/ErasureFunction.v:1602`). -/
theorem kername_ofNat {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)}
    (hc : st.constants[`OfNat.ofNat]? = none) (h : st.inductives[`OfNat]? = none) :
    (get_constant_kername (m := PureM) (n + 20) `OfNat.ofNat).runPure st ⟨L, [], F, cfgU, dc⟩ pc
      ⟨12⟩ = .ok ((toKername `OfNat.ofNat, stON st), ⟨15⟩) := by
  rw [get_constant_kername]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, hc]
  apply bind_ok (visitMutual_ofNat h)
  apply bind_ok rfl
  simp only [stON, stDef, Std.HashMap.getElem?_insert_self]
  rfl

/-- `instOfNatNat`'s body `OfNat.mk Nat n n` under its local `n`. -/
def mkB : Expr := .app (.app (.app (cOf .zero) tN) (xv 15)) (xv 15)

theorem withApp_mkB {γ : Sort _} (k : Expr → Array Expr → γ) :
    mkB.withApp k = k (cOf .zero) #[tN, xv 15, xv 15] := by krfl

/-- The erasure of `instOfNatNat`'s body. -/
def mkBL : LBTerm := .app (.app (.app (.construct iidOf 0 []) .box) (.fvar (xf 15))) (.fvar (xf 15))

/-- `visitExpr` on `OfNat.mk Nat n n`, `OfNat` registered: the type parameter is erased.
Reference: the `tConstruct` case of `erase` (`MR E/ErasureFunction.v:1014`). -/
theorem mkB_run {n : Nat} {L : LocalContext} (h : st.inductives[`OfNat]? = some (iidOf, masksOf)) :
    (visitExpr (m := PureM) (n + 12) mkB).runPure st ⟨L, [loc 15 `n tN], none, cfgU, dc⟩ pc ps =
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
  refine bind_ok (a := .app (.app (tOf .zero) tN) (xv 15)) (st' := st) (ps' := ps) (by krfl) ?_
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
      x.runPure st ⟨L, [loc 15 `n tN], none, cfgU, dc⟩ pc ps)
    (?_ : _ = visitAppArgs (m := PureM) (n + 8) (.construct iidOf 0 []) #[tN, xv 15, xv 15])).trans ?_
  · krfl
  refine appArgs_cons (as := [xv 15, xv 15]) (r := .box) (st' := st) (ps' := ps) (by krfl) ?_
  refine appArgs_cons (as := [xv 15]) (fvar_run (n := n + 6) (by krfl)) ?_
  refine appArgs_cons (as := []) (fvar_run (n := n + 6) (by krfl)) ?_
  exact appArgs_nil

/-- The erasure of `instOfNatNat`'s value. -/
def instVLU : LBTerm := .lambda (binderNameOf `n) (_root_.abstract (xf 15) mkBL)

/-- The state after `instOfNatNat`. -/
abbrev stIn (st : ErasureState) : ErasureState := stDef st `instOfNatNat instVLU

/-- `visitMutual` on `instOfNatNat`. Reference: as `visitMutual_go` (`Test/NVSRun.lean`). -/
theorem visitMutual_inst {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)}
    (h : st.inductives[`OfNat]? = some (iidOf, masksOf)) :
    (visitMutual (m := PureM) (n + 15) `instOfNatNat).runPure st ⟨L, [], F, cfgU, dc⟩ pc ⟨15⟩ =
      .ok (((), stIn st), ⟨16⟩) := by
  rw [visitMutual]
  iterate 8 apply bind_ok rfl
  refine bind_ok (a := instVLU) (st' := st) (ps' := ⟨16⟩) ?_ ?_
  · rw [runPure_withReader]
    apply bind_ok rfl
    refine bind_ok (a := instVal) (st' := st) (ps' := ⟨15⟩) rfl ?_
    exact lam_run (by krfl) fun _ => mkB_run (n := n) h
  rfl

/-- `get_constant_kername` on `instOfNatNat`, not yet erased. Reference: `erase_global_deps`
(`MR E/ErasureFunction.v:1602`). -/
theorem kername_inst {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)}
    (hc : st.constants[`instOfNatNat]? = none) (h : st.inductives[`OfNat]? = some (iidOf, masksOf)) :
    (get_constant_kername (m := PureM) (n + 16) `instOfNatNat).runPure st ⟨L, [], F, cfgU, dc⟩ pc
      ⟨15⟩ = .ok ((toKername `instOfNatNat, stIn st), ⟨16⟩) := by
  rw [get_constant_kername]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, hc]
  apply bind_ok (visitMutual_inst h)
  apply bind_ok rfl
  simp only [stIn, stDef, Std.HashMap.getElem?_insert_self]
  rfl

/-! ## The numerals and the term -/

/-- `visitExpr` on `instOfNatNat k` outside any binder, with the step `hk` on `instOfNatNat` and
the literal's erasure `hl`. Reference: the `tConst` and `tApp` cases of `erase`
(`MR E/ErasureFunction.v:999`, `:1006`). -/
theorem instK_run {n k : Nat} {L : LocalContext} {st' : ErasureState} {ps' : PureState}
    {t : LBTerm}
    (hk : (get_constant_kername (m := PureM) (n + 16) `instOfNatNat).runPure st
      ⟨L, [], none, cfgU, dc⟩ pc ps = .ok ((toKername `instOfNatNat, st'), ps'))
    (hl : (visitExpr (m := PureM) (n + 16) (lit k)).runPure st' ⟨L, [], none, cfgU, dc⟩ pc ps' =
      .ok ((t, st'), ps')) :
    (visitExpr (m := PureM) (n + 20) (instK k)).runPure st ⟨L, [], none, cfgU, dc⟩ pc ps =
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
      ⟨L, [], none, cfgU, dc⟩ pc ps = .ok ((toKername `OfNat.ofNat, st₁), ps₁))
    (hl : (visitExpr (m := PureM) (n + 20) (lit k)).runPure st₁ ⟨L, [], none, cfgU, dc⟩ pc ps₁ =
      .ok ((t, st₁), ps₁))
    (hi : (visitExpr (m := PureM) (n + 20) (instK k)).runPure st₁ ⟨L, [], none, cfgU, dc⟩ pc ps₁ =
      .ok ((i, st₂), ps₂)) :
    (visitExpr (m := PureM) (n + 24) (numK k)).runPure st ⟨L, [], none, cfgU, dc⟩ pc ps =
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

/-- The state at the end of the run. -/
abbrev stE : ErasureState := stIn (stON stAdd)

/-- Facts about the traversal's maps in the states of the run. -/
macro (name := _stfactU) "ufact" : tactic =>
  `(tactic| (simp only [stE, stIn, stON, stAdd, stMt, stDef, stN, stOf,
    Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]; try rfl))

theorem withApp_e {γ : Sort _} (k : Expr → Array Expr → γ) :
    e.withApp k = k (.const `Nat.add []) #[numK 2, numK 3] := by krfl

/-- `visitExpr` on `e = Nat.add 2 3`: the λ□ constant of `Nat.add`, erased on the way as a
fixpoint with its dependencies, applied to the erased numerals, the first of which erases
`OfNat.ofNat` and `instOfNatNat`. Reference: the `tConst` and `tApp` cases of `erase`
(`MR E/ErasureFunction.v:999`, `:1006`), with `erase_global_deps`
(`MR E/ErasureFunction.v:1602`). -/
theorem e_run {n : Nat} {L : LocalContext} :
    (visitExpr (m := PureM) (n + 80) e).runPure {} ⟨L, [], none, cfgU, .anonymous⟩ pc ⟨0⟩ =
      .ok ((eL, stE), ⟨16⟩) := by
  have hN2 : (stON stAdd).inductives[`Nat]? = some (iidN, masksN) := by ufact
  have hN3 : stE.inductives[`Nat]? = some (iidN, masksN) := by ufact
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
  refine bind_ok (a := .const (toKername `Nat.add)) (st' := stAdd) (ps' := ⟨12⟩) ?_ ?_
  · rw [visitConst]
    apply bind_ok rfl
    refine bind_ok (kername_add (n := n + 27)) ?_
    rfl
  refine appArgs_cons (as := [numK 3])
    (numK_run (n := n + 52) (kername_ofNat (n := n + 52) (by ufact) (by ufact))
      (lit2_run (n := n + 60) hN2)
      (instK_run (n := n + 52) (kername_inst (n := n + 52) (by ufact)
        (by ufact)) (lit2_run (n := n + 56) hN3))) ?_
  refine appArgs_cons (as := [])
    (numK_run (n := n + 52) (kername_found (n := n + 71) (by ufact))
      (lit3_run (n := n + 56) hN3)
      (instK_run (n := n + 52) (kername_found (n := n + 67) (by ufact))
        (lit3_run (n := n + 52) hN3))) ?_
  exact appArgs_nil

/-! ## The run on NV-U -/

/-- The program `#erase` emits for NV-U: NV-A's declarations of `instOfNatNat`, `OfNat.ofNat`,
`OfNat`, `Nat.add.match_1` and `Nat`, and `Nat.add` as the fixpoint `addFixL`. -/
def pU : Program :=
  .untyped [(toKername `instOfNatNat, .constantDecl ⟨some instVL⟩),
    (toKername `OfNat.ofNat, .constantDecl ⟨some ofNatVL⟩),
    (mutualBlockKername [`OfNat], .inductiveDecl ⟨.finite, 2, [bodyOf]⟩),
    (toKername `Nat.add, .constantDecl ⟨some addFixL⟩),
    (toKername `Nat.add.match_1, .constantDecl ⟨some matchVL⟩),
    (mutualBlockKername [`Nat], .inductiveDecl ⟨.finite, 0, [bodyN]⟩)] (some eL)

/-- The pure path on NV-A's closure under `cfgU` returns `pU` and no constant to inline.
Reference: `erase` (`MR E/ErasureFunction.v:989`) and `erase_global_deps`
(`MR E/ErasureFunction.v:1602`). -/
theorem hpure : erasePure view cfgU D e = .ok (pU, []) := by
  rw [erasePure, show travFuel = (travFuel - 80) + 80 by decide]
  rw [show ((visitExpr (m := PureM) (travFuel - 80 + 80) e).runPure {} { «config» := cfgU }
    ⟨D, view⟩ {}) = .ok ((eL, stE), ⟨16⟩) from e_run]
  krfl

/-- `#erase`'s entry point on NV-U returns `pU` and no constant to inline. Reference: the
hypotheses `erase … = t'` and `erase_global_deps … = Σ'` of `erase_correct`
(`MR E/ErasureFunctionProperties.v:657`). -/
theorem hrun : eraseEntry view cfgU e = pure (pU, []) := by
  simp only [eraseEntry, route, hcollect, hpure]

end EraseProof.Test.NVU
