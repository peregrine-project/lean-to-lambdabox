import EraseProof.Statements
import EraseProof.Test.NV4Data
import EraseProof.Test.NV1Premises
import EraseProof.Test.NVKit

/-!
# NV-4: the hypotheses of the final theorem

Each hypothesis of `erase_correct_statement` holds on the program of `Test/NV4Data.lean`, each
stated as the theorem of that name; `hev` goes through `SrcEval.quotLift`, `SrcEval.quotMk` and
`SrcEval.casesFrozen` twice (on `Eq.refl`, no field; on a proof of `P`, one field). `hfrag` and
`hrun` are the shipping `collectDeps`/`eraseEntry` evaluated one traversal call at a time
(`Test/Run.lean`). The kernel checks all but two facts: the equation of the pure fold inside `hacc`,
its premise `hfold`, and the con-leche runs of `guards`, the premise `hg`, which infer a type for
the alternative `fun _ => B.t` of `P.casesOn` against `(a : False → P) → motive (P.mk a)`, for
`fun a b h => h` against `Quot.lift`'s `∀ a b, r a b → f a = f b`, or for the proof of `P`; each
compares two `Π`s with different bodies, whose opening the kernel does not reduce (DV-40). A
`#guard` checks each by compiled evaluation.
-/

open Lean Erasure EraseProof EraseProof.Test EraseProof.Test.NV4

namespace EraseProof.Test.NV4

open EraseProof.Test.NV1 (tB cT B_ind Bf_ctor Bt_ctor B_rec kRecType kRule kB nm nm2 iidB masksB bodyB stB)

/-! ## con-leche's environment -/

def full : List ConLeche.Declaration := (DeclsOf? P).getD []

/-- `fun α r β f h a => f a`, `fun α r β mk a => mk a`: con-leche's rules of the quotient -/
def liftRhs : Expr :=
  .lam `α (.sort lu) (.lam `r (relTy 0) (.lam `β (.sort (.param `v)) (.lam `f (.forallE `a (.bvar 2)
    (.bvar 1) .default) (.lam `h compatTy (.lam `a (.bvar 4) (.app (.bvar 2) (.bvar 0)) .default)
    .default) .default) .default) .default) .default
def indRhs : Expr :=
  .lam `α (.sort lu) (.lam `r (relTy 0) (.lam `β (.forallE `a (quotC (.bvar 1) (.bvar 0)) (.sort .zero)
    .default) (.lam `mk (.forallE `a (.bvar 2) (.app (.bvar 1) (mkAppN (.const `Quot.mk [lu])
    #[.bvar 3, .bvar 2, .bvar 0])) .default) (.lam `a (.bvar 3) (.app (.bvar 1) (.bvar 0)) .default)
    .default) .default) .default) .default

def qRule (rhs : Expr) : ConLeche.RecRule :=
  ⟨Name.toCL `Quot.mk, 1, .levels [.param (Name.toCL `u)], cl rhs⟩

def envNV4 : ConLeche.Env :=
  ⟨[ .defnInfo (cvC (.defnInfo P_casesOn)) (cl pCasesOnVal) .abbrev
   , .recInfo (cvC (.recInfo P_rec)) 2 2 false [⟨Name.toCL `P.mk, 1, .plain, cl P_rec.rules[0]!.rhs⟩]
   , .ctorInfo (cvC (.ctorInfo P_mk)) 0 1 (Name.toCL `P)
   , .indInfo (cvC (.inductInfo P_ind)) { all := [Name.toCL `P], ctors := [Name.toCL `P.mk] }
   , .recInfo (cvC (.recInfo False_rec)) 1 1 false []
   , .indInfo (cvC (.inductInfo False_ind)) { all := [Name.toCL `False] }
   , .defnInfo (cvC (.defnInfo Eq_casesOn)) (cl eqCasesOnVal) .abbrev
   , .recInfo (cvC (.quotInfo QuotInd_val)) 4 4 false [qRule indRhs]
   , .recInfo (cvC (.quotInfo QuotLift_val)) 5 5 false [qRule liftRhs]
   , .ctorInfo (cvC (.quotInfo QuotMk_val)) 2 1 (Name.toCL `Quot)
   , .indInfo (cvC (.quotInfo Quot_val)) {}
   , .recInfo (cvC (.recInfo Eq_rec)) 5 4 true [⟨Name.toCL `Eq.refl, 0, .plain, cl eqRecRhs⟩]
   , .ctorInfo (cvC (.ctorInfo Eq_refl)) 2 0 (Name.toCL `Eq)
   , .indInfo (cvC (.inductInfo Eq_ind))
       { all := [Name.toCL `Eq], nparams := 2, nIdx := 1, ctors := [Name.toCL `Eq.refl] }
   , .recInfo ⟨nm2 "B" "rec", [nm "u"], kRecType⟩ 3 3 false [kRule "f" 1, kRule "t" 0]
   , .ctorInfo ⟨nm2 "B" "t", [], kB⟩ 0 0 (nm "B")
   , .ctorInfo ⟨nm2 "B" "f", [], kB⟩ 0 0 (nm "B")
   , .indInfo ⟨nm "B", [], .sort (.succ .zero)⟩
       { all := [nm "B"], ctors := [nm2 "B" "f", nm2 "B" "t"], neverZero := true } ],
   [{ structName := Name.toCL `P, levelParams := [], numParams := 0, ctor := Name.toCL `P.mk,
      numFields := 1, bodies := #[cl fP] }]⟩

#guard match ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified ConLeche.checkFuel) []
    full with
  | .ok env => decide (env.consts = envNV4.consts) && decide (env.tables = envNV4.tables)
  | .error _ => false

/-! ## The compiled checks -/

def pj : Expr := .proj `P 0 dP
/-- `@Quot.{1} α r` -/
def quotC' (α r : Expr) : Expr := .app (.app (.const `Quot [l1]) α) r

/-- The con-leche runs the kernel does not reduce (see the header): inference of `e`, of the
`Quot.lift` redex and of the β-redex of `P.casesOn`'s alternative, `dP` as a proof (unmarked and
as a reduced mark), the projection of `dP` as a proof, and the ι certificate of `P.casesOn`. -/
def guards : Bool :=
  [e, liftOf (qmOf cT), .app altP pj].all (inferOk envNV4 ConLeche.checkFuel) &&
    erasableOk true envNV4 ConLeche.checkFuel dP && erasableOk false envNV4 ConLeche.checkFuel pj &&
    certOk true envNV4 [] dP && frozenOk envNV4 ConLeche.checkFuel `P `P.mk [l1] [] dP

#guard guards

variable (hg : guards = true)

include hg in
theorem guard {t : Expr} (ht : t ∈ [e, liftOf (qmOf cT), .app altP pj]) :
    inferOk envNV4 ConLeche.checkFuel t = true := by
  simp only [guards, Bool.and_eq_true, List.all_eq_true] at hg
  exact hg.1.1.1.1 t ht

include hg in
theorem guard' : erasableOk true envNV4 ConLeche.checkFuel dP = true ∧
    erasableOk false envNV4 ConLeche.checkFuel pj = true ∧ certOk true envNV4 [] dP = true ∧
    frozenOk envNV4 ConLeche.checkFuel `P `P.mk [l1] [] dP = true := by
  simp only [guards, Bool.and_eq_true] at hg
  exact ⟨hg.1.1.1.2, hg.1.1.2, hg.1.2, hg.2⟩

/-! ## `hacc`, `hty`, `hclean`, `hview`, `hfrag`, `hnopre` -/

theorem decls : DeclsOf? P = some full := by krfl

theorem hacc (hfold : ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified ConLeche.checkFuel)
    [] full = .ok envNV4) : ConLecheAccepts P envNV4 :=
  ⟨full, decls, hfold, by krfl, by krfl⟩

include hg in
theorem hty : CLTyped envNV4 e := typed_of _ (guard hg (by simp))

theorem hclean : NoMarkKeys e = true := by krfl

theorem hview : ViewAgrees view P := by
  intro ci h
  simp only [P, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;> refine ⟨rfl, fun cfg pre hp => ?_⟩ <;>
    rw [preDef_none' (by krfl)] at hp <;> cases hp

def D : List ConstantInfo :=
  [.recInfo False_rec, .inductInfo False_ind, .ctorInfo P_mk, .inductInfo P_ind, .recInfo P_rec,
    .defnInfo P_casesOn, .defnInfo Eq_casesOn, .quotInfo QuotMk_val, .ctorInfo Bt_ctor,
    .ctorInfo Bf_ctor, .inductInfo B_ind, .quotInfo Quot_val, .ctorInfo Eq_refl, .recInfo Eq_rec,
    .inductInfo Eq_ind, .quotInfo QuotLift_val]

theorem hfrag : collectDeps view cfg e = .ok D := by krfl

theorem hnopre : NoPreDefs view cfg D := by unfold NoPreDefs; decide

/-! ## `hrun`: the traversal, one call at a time -/

def pc : PureCtx := ⟨D, view⟩

variable {st : ErasureState} {ps : PureState} {dc : Name} {L : LocalContext}

theorem register_B_new {ls : List Local} (h : st.inductives[`B]? = none) :
    (register_inductive (m := PureM) B_ind).runPure st ⟨L, ls, none, {}, dc⟩ pc ps =
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

def fx (i : Nat) : FVarId := ⟨.num `_pure i⟩
def la : Local := ⟨fx 1, `a, fP, none⟩

theorem cT_run {n : Nat} (h : st.inductives[`B]? = none) :
    (visitExpr (m := PureM) (n + 6) cT).runPure st ⟨L, [la], none, cfg, dc⟩ pc ps =
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

def altPL : LBTerm := .lambda (binderNameOf `a) (.construct iidB 1 [])

theorem altP_run {n : Nat} (h : st.inductives[`B]? = none) :
    (visitExpr (m := PureM) (n + 9) altP).runPure st ⟨L, [], none, cfg, dc⟩ pc ⟨1⟩ =
      .ok ((altPL, stB st), ⟨2⟩) := by
  rw [altP, visitExpr, ← altP]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ⟨1⟩) (by krfl) ?_
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [visitLambda]
  refine bind_ok (a := fx 1) (st' := st) (ps' := ⟨2⟩) rfl ?_
  refine bind_ok (a := .construct iidB 1 []) (st' := stB st) (ps' := ⟨2⟩) ?_ ?_
  · exact cT_run (L := L.mkLocalDecl (fx 1) `a fP) (n := n + 1) h
  krfl

def altsP : Std.HashMap Name (Nat × Expr) := (∅ : Std.HashMap Name (Nat × Expr)).insert `P.mk (1, altP)

def ciP : CasesInfo :=
  { declName := `P.casesOn, indName := `P, arity := 3, discrPos := 1, motivePos := 0,
    altsRange := 2...3, altNumParams := #[.ctor `P.mk 1] }

theorem casesP_run {n : Nat} (h : st.inductives[`B]? = none) :
    (visitCases (m := PureM) (n + 11) ciP #[motP, dP, altP]).runPure st ⟨L, [], none, cfg, dc⟩ pc ⟨1⟩ =
      .ok ((.app altPL .box, stB st), ⟨2⟩) := by
  rw [visitCases]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := .zero) (st' := st) (ps' := ⟨1⟩) (by krfl) ?_
  have hr : (ciP.altsRange.toList) = [2] := by simp [ciP]
  simp only [← forIn'_eq_forIn, Std.Rco.forIn'_eq_forIn'_toList, hr, List.forIn'_cons,
    List.forIn'_nil]
  refine bind_ok (a := (altsP, none, ?sEnd)) (st' := st) (ps' := ⟨1⟩) ?_ ?_
  case sEnd => exact (ciP.altNumParams.toSubarray 1 1)
  · rfl
  simp only [show (!Level.zero.isNeverZero && decide (P_ind.numIndices > 0)) = false by decide,
    show (!Level.zero.isNeverZero && P_ind.numCtors == 1) = true by decide, Bool.false_eq_true,
    ↓reduceIte, altsP]
  apply bind_ok rfl
  simp only [Std.HashMap.getElem?_insert_self, Std.HashMap.getElem?_empty]
  apply bind_ok (altP_run (n := n + 1) h)
  apply bind_ok rfl
  rw [toArray_toSubarray, visitAppArgs]
  rfl

theorem withApp_frzP {γ : Sort _} (k : Expr → Array Expr → γ) :
    (frzPOf dP).withApp k = k (.const `P.casesOn [l1]) #[motP, dP, altP] := by krfl

theorem frzP_run {n : Nat} (h : st.inductives[`B]? = none) :
    (visitExpr (m := PureM) (n + 15) (frzPOf dP)).runPure st ⟨L, [], none, cfg, dc⟩ pc ⟨1⟩ =
      .ok ((.app altPL .box, stB st), ⟨2⟩) := by
  have he : frzPOf dP = .app (.app (.app (.const `P.casesOn [l1]) motP) dP) altP := rfl
  rw [he, visitExpr, ← he]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ⟨1⟩) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 13) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_frzP]
  refine bind_ok (a := some ciP) (st' := st) (ps' := ⟨1⟩) (by krfl) ?_
  change (withAppEtaToMinArity (m := PureM) (n + 12) _ 3 _).runPure _ _ _ _ = _
  rw [withAppEtaToMinArity]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := .app motP dP) (st' := st) (ps' := ⟨1⟩) (by krfl) ?_
  rw [withApp_frzP, withAppEtaToMinArity.go, ite_eq_left (by simp)]
  exact casesP_run (n := n + 1) h

def altsE : Std.HashMap Name (Nat × Expr) :=
  (∅ : Std.HashMap Name (Nat × Expr)).insert `Eq.refl (0, frzPOf dP)

def ciEq : CasesInfo :=
  { declName := `Eq.casesOn, indName := `Eq, arity := 6, discrPos := 4, motivePos := 2,
    altsRange := 5...6, altNumParams := #[.ctor `Eq.refl 0] }

theorem casesEq_run {n : Nat} (h : st.inductives[`B]? = none) :
    (visitCases (m := PureM) (n + 16) ciEq #[tB, cT, motE, cT, reflB, frzPOf dP]).runPure st
      ⟨L, [], none, cfg, dc⟩ pc ⟨1⟩ = .ok ((.app altPL .box, stB st), ⟨2⟩) := by
  rw [visitCases]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := .zero) (st' := st) (ps' := ⟨1⟩) (by krfl) ?_
  have hr : (ciEq.altsRange.toList) = [5] := by simp [ciEq]
  simp only [← forIn'_eq_forIn, Std.Rco.forIn'_eq_forIn'_toList, hr, List.forIn'_cons,
    List.forIn'_nil]
  refine bind_ok (a := (altsE, none, ?sEnd)) (st' := st) (ps' := ⟨1⟩) ?_ ?_
  case sEnd => exact (ciEq.altNumParams.toSubarray 1 1)
  · rfl
  simp only [show (!Level.zero.isNeverZero && decide (Eq_ind.numIndices > 0)) = true by decide,
    show (!Level.zero.isNeverZero && Eq_ind.numCtors == 1) = true by decide, ↓reduceIte, altsE]
  refine bind_ok (a := (∅ : Std.HashMap Name (List (Option Expr)))) (st' := st) (ps' := ⟨1⟩)
    (by krfl) ?_
  apply bind_ok rfl
  simp only [Std.HashMap.getElem?_insert_self, Std.HashMap.getElem?_empty]
  apply bind_ok (frzP_run h)
  apply bind_ok rfl
  rw [toArray_toSubarray, visitAppArgs]
  rfl

theorem withApp_frz {γ : Sort _} (k : Expr → Array Expr → γ) :
    (frzOf reflB (frzPOf dP)).withApp k =
      k (.const `Eq.casesOn [l1, l1]) #[tB, cT, motE, cT, reflB, frzPOf dP] := by krfl

theorem frz_run {n : Nat} (h : st.inductives[`B]? = none) :
    (visitExpr (m := PureM) (n + 20) (frzOf reflB (frzPOf dP))).runPure st ⟨L, [], none, cfg, dc⟩ pc
      ⟨1⟩ = .ok ((.app altPL .box, stB st), ⟨2⟩) := by
  have he : frzOf reflB (frzPOf dP) = .app (mkAppN (.const `Eq.casesOn [l1, l1]) #[tB, cT, motE, cT, reflB])
    (frzPOf dP) := rfl
  rw [he, visitExpr, ← he]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ⟨1⟩) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 18) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_frz]
  refine bind_ok (a := some ciEq) (st' := st) (ps' := ⟨1⟩) (by krfl) ?_
  change (withAppEtaToMinArity (m := PureM) (n + 17) _ 6 _).runPure _ _ _ _ = _
  rw [withAppEtaToMinArity]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := .app (.app motE cT) reflB) (st' := st) (ps' := ⟨1⟩) (by krfl) ?_
  rw [withApp_frz, withAppEtaToMinArity.go, ite_eq_left (by simp)]
  exact casesEq_run (n := n + 1) h

theorem withApp_qm {γ : Sort _} (k : Expr → Array Expr → γ) :
    (qmOf (frzOf reflB (frzPOf dP))).withApp k =
      k (.const `Quot.mk [l1]) #[tB, cR, frzOf reflB (frzPOf dP)] := by krfl

theorem qm_run {n : Nat} (h : st.inductives[`B]? = none) :
    (visitExpr (m := PureM) (n + 23) (qmOf (frzOf reflB (frzPOf dP)))).runPure st
      ⟨L, [], none, cfg, dc⟩ pc ⟨1⟩ = .ok ((.app altPL .box, stB st), ⟨2⟩) := by
  have he : qmOf (frzOf reflB (frzPOf dP)) =
    .app (mkAppN (.const `Quot.mk [l1]) #[tB, cR]) (frzOf reflB (frzPOf dP)) := rfl
  rw [he, visitExpr, ← he]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ⟨1⟩) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 21) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_qm]
  refine bind_ok (a := none) (st' := st) (ps' := ⟨1⟩) (by krfl) ?_
  refine bind_ok (a := none) (st' := st) (ps' := ⟨1⟩) (by krfl) ?_
  refine bind_ok (a := some (.quotInfo QuotMk_val)) (st' := st) (ps' := ⟨1⟩) (by krfl) ?_
  change (withAppEtaToMinArity (m := PureM) (n + 20) _ 3 _).runPure _ _ _ _ = _
  rw [withAppEtaToMinArity]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := quotC' tB cR) (st' := st) (ps' := ⟨1⟩) (by krfl) ?_
  rw [withApp_qm, withAppEtaToMinArity.go]
  refine bind_ok (a := frzOf reflB (frzPOf dP)) (st' := st) (ps' := ⟨1⟩) rfl ?_
  refine bind_ok (frz_run h) ?_
  rw [visitAppArgs]
  rfl

def idFL : LBTerm := .lambda (binderNameOf `x) (.bvar 0)

theorem idF_run {n : Nat} :
    (visitExpr (m := PureM) (n + 4) idF).runPure st ⟨L, [], none, cfg, dc⟩ pc ⟨0⟩ =
      .ok ((idFL, st), ⟨1⟩) := by
  krfl

theorem withApp_e {γ : Sort _} (k : Expr → Array Expr → γ) :
    e.withApp k = k (.const `Quot.lift [l1, l1]) #[tB, cR, tB, idF, hL, qmOf (frzOf reflB (frzPOf dP))] := by
  krfl

/-- The erasure of `e`: `(fun x => x) ((fun a => B.t) □)`. -/
def eL : LBTerm := .app idFL (.app altPL .box)

theorem e_run {n : Nat} (h : st.inductives[`B]? = none) :
    (visitExpr (m := PureM) (n + 27) e).runPure st ⟨L, [], none, cfg, dc⟩ pc ⟨0⟩ =
      .ok ((eL, stB st), ⟨2⟩) := by
  have he : e = .app (mkAppN (.const `Quot.lift [l1, l1]) #[tB, cR, tB, idF, hL])
    (qmOf (frzOf reflB (frzPOf dP))) := rfl
  rw [he, visitExpr, ← he]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 25) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_e]
  refine bind_ok (a := none) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  refine bind_ok (a := none) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  refine bind_ok (a := some (.quotInfo QuotLift_val)) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  change (withAppEtaToMinArity (m := PureM) (n + 24) _ 6 _).runPure _ _ _ _ = _
  rw [withAppEtaToMinArity]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := tB) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  rw [withApp_e, withAppEtaToMinArity.go]
  refine bind_ok (a := idF) (st' := st) (ps' := ⟨0⟩) rfl ?_
  refine bind_ok (a := idFL) (st' := st) (ps' := ⟨1⟩) (idF_run (n := n + 20)) ?_
  rw [visitAppArgs, show (#[tB, cR, tB, idF, hL, qmOf (frzOf reflB (frzPOf dP))] : Array Expr).extract 5 =
    #[qmOf (frzOf reflB (frzPOf dP))] from rfl, ← Array.foldlM_toList]
  simp only [List.foldlM_cons, List.foldlM_nil]
  refine bind_ok (a := eL) (st' := stB st) (ps' := ⟨2⟩) ?_ rfl
  apply bind_ok (qm_run (n := n) h)
  rfl

def p0 : Program :=
  .untyped [(mutualBlockKername [`B], .inductiveDecl ⟨.finite, 0, [bodyB]⟩)] (some eL)

theorem hpure : erasePure view cfg D e = .ok (p0, []) := by
  rw [erasePure, show travFuel = (travFuel - 27) + 27 by decide]
  rw [show ((visitExpr (m := PureM) (travFuel - 27 + 27) e).runPure {} { «config» := cfg }
    ⟨D, view⟩ {}) = .ok ((eL, stB {}), ⟨2⟩) from e_run Std.HashMap.getElem?_empty]
  rfl

theorem hrun : eraseEntry view cfg e = pure (p0, []) := by
  simp only [eraseEntry, route, hfrag, hpure]

/-! ## `hmark`: the marks are the two reduced discriminants -/

def frzPM : Expr := frzPOf (markReduced dP)
def frzM : Expr := frzOf (markReduced reflB) frzPM
/-- The marking of `e`. -/
def eM : Expr := liftOf (qmOf frzM)

theorem mark_cT {ls : List Local} (ho : oracle D ls cT = .ok false)
    (hi : Pure.inferType ⟨D⟩ oracleFuel ls [] cT = .ok tB) : MarkOf D cfg ls cT cT :=
  MarkOf.special (c := `B.t) (us := []) (as := []) ho (by krfl) hi
    (MarkEta.sat (Nat.le_refl 0) (MarkSat.ctor (ar := 0) (as := []) (âs := []) (by krfl) (by krfl) rfl
      (by simp)))

theorem mark_frzP : MarkOf D cfg [] (frzPOf dP) frzPM := by
  refine MarkOf.special (c := `P.casesOn) (us := [l1]) (as := [motP, dP, altP]) (ar := 3)
    (T := .app motP dP) (by krfl) (by krfl) (by krfl) (MarkEta.sat (by decide) ?_)
  exact MarkSat.casesReduced (iv := P_ind) (cd := P_casesOn) (pre := [motP]) (d := dP) (alt := altP)
    (âlt := altP) (extra := []) (êxtra := []) (u := .zero) (cn := `P.mk) (cv := P_mk) (by krfl)
    (by krfl) (by decide) rfl (by krfl) rfl rfl (by krfl) (by krfl)
    (mark_lam (x := fx 1) (by krfl) (fresh_of (by krfl)) (by krfl) (mark_cT (by krfl) (by krfl)))
    rfl (by simp)

theorem mark_frz : MarkOf D cfg [] (frzOf reflB (frzPOf dP)) frzM := by
  refine MarkOf.special (c := `Eq.casesOn) (us := [l1, l1]) (as := [tB, cT, motE, cT, reflB, frzPOf dP])
    (ar := 6) (T := .app (.app motE cT) reflB) (by krfl) (by krfl) (by krfl) (MarkEta.sat (by decide) ?_)
  exact MarkSat.casesReduced (iv := Eq_ind) (cd := Eq_casesOn) (pre := [tB, cT, motE, cT]) (d := reflB)
    (alt := frzPOf dP) (âlt := frzPM) (extra := []) (êxtra := []) (u := .zero) (cn := `Eq.refl)
    (cv := Eq_refl) (by krfl) (by krfl) (by decide) rfl (by krfl) rfl rfl (by krfl) (by krfl) mark_frzP
    rfl (by simp)

theorem hmark : MarkOf D cfg [] e eM := by
  refine MarkOf.special (c := `Quot.lift) (us := [l1, l1])
    (as := [tB, cR, tB, idF, hL, qmOf (frzOf reflB (frzPOf dP))]) (ar := 6) (T := tB) (by krfl) (by krfl)
    (by krfl) (MarkEta.sat (by decide) ?_)
  refine MarkSat.quotLift (qv := QuotLift_val) (α := tB) (r := cR) (β := tB) (f := idF) (h := hL)
    (fM := idF) (qM := qmOf frzM) (extra := []) (êxtra := []) (by krfl) (by krfl) (by krfl) rfl
    (mark_lam (x := fx 0) (by krfl) (fresh_of (by krfl)) (by krfl) (MarkOf.fvar (by krfl))) ?_ rfl (by simp)
  refine MarkOf.special (c := `Quot.mk) (us := [l1]) (as := [tB, cR, frzOf reflB (frzPOf dP)]) (ar := 3)
    (T := quotC' tB cR) (by krfl) (by krfl) (by krfl) (MarkEta.sat (by decide) ?_)
  exact MarkSat.quotMk (qv := QuotMk_val) (α := tB) (r := cR) (extra := []) (êxtra := []) (by krfl)
    (by krfl) (by krfl) rfl mark_frz rfl (by simp)

/-! ## `hcert`: the input, its two marks, and the markings of the closure's two values,
`Eq.casesOn`'s (its major marked) and `P.casesOn`'s (its field and its major marked) -/

/-- `Eq.casesOn`'s value with its major marked -/
def eqCasesOnValM : Expr :=
  .lam `α (.sort u1) (.lam an (.bvar 0) (.lam `motive eqMotTy
    (.lam an (.bvar 2) (.lam `t (eqC (.bvar 3) (.bvar 2) (.bvar 0)) (.lam `refl eqReflTy
      (mkAppN (.const `Eq.rec [lu, u1]) #[.bvar 5, .bvar 4, .bvar 3, .bvar 0, .bvar 2, markErase (.bvar 1)])
      .default) .default) .implicit) .implicit) .implicit) .implicit

/-- `P.casesOn`'s value with the field and the major marked -/
def pCasesOnValM : Expr :=
  .lam `motive pMotTy (.lam `t tP (.lam `mk pAltTy (mkAppN (.const `P.rec [lu]) #[.bvar 2,
    .lam `a fP (.lam `a_ih (.forallE `x tF (.app (.bvar 4) (.app (.bvar 1) (.bvar 0))) .default)
      (.app (.bvar 2) (markErase (.bvar 1))) .default) .default, markErase (.bvar 1)]) .default) .default)
    .implicit

theorem mark_eqCasesOn : MarkOf D cfg [] eqCasesOnVal eqCasesOnValM := by
  refine mark_lam (x := fx 0) (by krfl) (fresh_of (by krfl)) (by krfl) ?_
  refine mark_lam (x := fx 1) (by krfl) (fresh_of (by krfl)) (by krfl) ?_
  refine mark_lam (x := fx 2) (by krfl) (fresh_of (by krfl)) (by krfl) ?_
  refine mark_lam (x := fx 3) (by krfl) (fresh_of (by krfl)) (by krfl) ?_
  refine mark_lam (x := fx 4) (by krfl) (fresh_of (by krfl)) (by krfl) ?_
  refine mark_lam (x := fx 5) (by krfl) (fresh_of (by krfl)) (by krfl) ?_
  refine MarkOf.special (c := `Eq.rec) (us := [lu, u1])
    (as := [.fvar (fx 0), .fvar (fx 1), .fvar (fx 2), .fvar (fx 5), .fvar (fx 3), .fvar (fx 4)]) (ar := 6)
    (T := .app (.app (.fvar (fx 2)) (.fvar (fx 3))) (.fvar (fx 4))) (by krfl) (by krfl) (by krfl)
    (MarkEta.sat (by decide) ?_)
  refine MarkSat.recr (r := Eq_rec) (ivs := [Eq_ind]) (cvs := [Eq_refl]) (ps := [.fvar (fx 0), .fvar (fx 1)])
    (ms := [.fvar (fx 2)]) (mins := [.fvar (fx 5)]) (minsM := [.fvar (fx 5)]) (is := [.fvar (fx 3)])
    (îs := [.fvar (fx 3)]) (maj := .fvar (fx 4)) (majM := markErase (.fvar (fx 4))) (extra := [])
    (êxtra := []) (by krfl) (by krfl) (by krfl) (by krfl) (by krfl) (by krfl) rfl rfl rfl rfl
    ⟨.zero, by krfl⟩ rfl ?_ rfl ?_ (MarkOf.erase (by krfl)) rfl (by simp)
  all_goals
    intro i x xM h1 h2
    rcases i with _ | i <;> simp at h1 h2 <;> subst h1 h2
    exact MarkOf.fvar (by krfl)

theorem mark_pCasesOn : MarkOf D cfg [] pCasesOnVal pCasesOnValM := by
  refine mark_lam (x := fx 0) (by krfl) (fresh_of (by krfl)) (by krfl) ?_
  refine mark_lam (x := fx 1) (by krfl) (fresh_of (by krfl)) (by krfl) ?_
  refine mark_lam (x := fx 2) (by krfl) (fresh_of (by krfl)) (by krfl) ?_
  refine MarkOf.special (c := `P.rec) (us := [lu])
    (as := [.fvar (fx 0), .lam `a fP (.lam `a_ih (.forallE `x tF (.app (.fvar (fx 0)) (.app (.bvar 1)
      (.bvar 0))) .default) (.app (.fvar (fx 2)) (.bvar 1)) .default) .default, .fvar (fx 1)]) (ar := 3)
    (T := .app (.fvar (fx 0)) (.fvar (fx 1))) (by krfl) (by krfl) (by krfl) (MarkEta.sat (by decide) ?_)
  refine MarkSat.recr (r := P_rec) (ivs := [P_ind]) (cvs := [P_mk]) (ps := []) (ms := [.fvar (fx 0)])
    (mins := [.lam `a fP (.lam `a_ih (.forallE `x tF (.app (.fvar (fx 0)) (.app (.bvar 1) (.bvar 0)))
      .default) (.app (.fvar (fx 2)) (.bvar 1)) .default) .default])
    (minsM := [.lam `a fP (.lam `a_ih (.forallE `x tF (.app (.fvar (fx 0)) (.app (.bvar 1) (.bvar 0)))
      .default) (.app (.fvar (fx 2)) (markErase (.bvar 1))) .default) .default]) (is := []) (îs := [])
    (maj := .fvar (fx 1)) (majM := markErase (.fvar (fx 1))) (extra := []) (êxtra := []) (by krfl)
    (by krfl) (by krfl) (by krfl) (by krfl) (by krfl) rfl rfl rfl rfl ⟨.zero, by krfl⟩ rfl ?_ rfl
    (by simp) (MarkOf.erase (by krfl)) rfl (by simp)
  intro i x xM h1 h2
  rcases i with _ | i <;> simp at h1 h2 <;> subst h1 h2
  refine mark_lam (x := fx 3) (by krfl) (fresh_of (by krfl)) (by krfl) ?_
  refine mark_lam (x := fx 4) (by krfl) (fresh_of (by krfl)) (by krfl) ?_
  refine MarkOf.app (f := .fvar (fx 2)) (as := [.fvar (fx 3)]) (âs := [markErase (.fvar (fx 3))])
    (by krfl) (by simp) rfl (by intro c us h; cases h) (MarkOf.fvar (by krfl)) rfl ?_
  intro i a â h1 h2
  rcases i with _ | i <;> simp at h1 h2 <;> subst h1 h2
  exact MarkOf.erase (by krfl)

include hg in
theorem hcert : ProgCert envNV4 D cfg eM := by
  refine ⟨typedAt_of ((inferOk_congr (t' := e) (by krfl)).trans (guard hg (by simp))), ?_, ?_⟩
  · have h1 : CLCertProof envNV4 [] reflB := certProof_of (by krfl)
    have h2 : CLCertProof envNV4 [] dP := certProof_of (guard' hg).2.2.1
    simp [MarksCert, eM, liftOf, qmOf, frzM, frzOf, frzPM, frzPOf, mkAppN, h1, h2, cR, idF, hL, motE,
      motP, altP, eqB, tB, cT]
  intro ci hci v hv
  simp only [D, List.mem_cons, List.not_mem_nil, or_false] at hci
  rcases hci with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> cases hv
  · refine ⟨_, mark_pCasesOn, typedAt_of (by krfl), ?_⟩
    simp [MarksCert, pCasesOnValM, mkAppN]
    exact ⟨cert_of (by krfl), cert_of (by krfl)⟩
  · refine ⟨_, mark_eqCasesOn, typedAt_of (by krfl), ?_⟩
    simp [MarksCert, eqCasesOnValM, mkAppN]
    exact cert_of (by krfl)

/-! ## `hev`: `eM ⇓ B.t`, through `quotLift`, `quotMk` and `casesFrozen` (twice) -/

abbrev σD : EvalEnv := evalEnvOf view cfg D

theorem ev_cT : SrcEval envNV4 σD cT cT :=
  SrcEval.ctor (c := `B.t) (us := []) (cv := Bt_ctor) (as := []) (vs := []) (by krfl) rfl rfl (by simp)
    (ok_clean (F := 100) (by krfl) rfl)

theorem not_short {x : Expr} (h : ∀ c us, x.getAppFn ≠ .const c us) : ¬ ShortSpine σD x := by
  rintro ⟨c, us, ar, h1, -⟩
  exact h c us h1

include hg in
/-- `P.casesOn (fun _ => B) dP (fun _ => B.t) ⇓ B.t`: the alternative at the frozen field of `dP` -/
theorem ev_frzP : SrcEval envNV4 σD frzPM cT :=
  SrcEval.casesFrozen (c := `P.casesOn) (us := [l1]) (iv := P_ind) (cn := `P.mk) (cv := P_mk) (d := dP)
    (as := [motP, markReduced dP, altP]) (alt := altP) (by krfl) rfl rfl (by krfl) rfl
    (proofTerm_of (guard' hg).1) (fun h => nomatch h) (fun _ => ⟨rfl, frozen_of (guard' hg).2.2.2⟩) rfl
    (SrcEval.beta (n := `a) (A := fP) (b := cT) (bi := .default) (not_short (by intro c us h; cases h))
      (SrcEval.atom trivial) (SrcEval.frozen (erasable_of (guard' hg).2.1))
      (ok_of ((inferOk_congr (t' := .app altP pj) (by krfl)).trans (guard hg (by simp)))
        ((inferOk_congr (t' := .app altP pj) (by krfl)).trans (guard hg (by simp)))) ev_cT)

include hg in
theorem ev_frz : SrcEval envNV4 σD frzM cT :=
  SrcEval.casesFrozen (c := `Eq.casesOn) (us := [l1, l1]) (iv := Eq_ind) (cn := `Eq.refl) (cv := Eq_refl)
    (d := reflB) (as := [tB, cT, motE, cT, markReduced reflB, frzPM]) (alt := frzPM) (by krfl) rfl rfl
    (by krfl) rfl (proofTerm_of (F := 100) (by krfl)) (fun _ => iota_of (by krfl)) (fun h => nomatch h)
    rfl (ev_frzP hg)

include hg in
theorem hev : SrcEval envNV4 σD eM cT :=
  SrcEval.quotLift (c := `Quot.lift) (us := [l1, l1]) (qv := QuotLift_val) (α := tB) (r := cR) (β := tB)
    (f := idF) (x := `x) (A := tB) (b := .bvar 0) (bi := .default) (h := hL) (q := qmOf frzM)
    (c' := `Quot.mk) (us' := [l1]) (α' := tB) (r' := cR) (a := cT) (qv' := QuotMk_val) (by krfl) rfl
    (SrcEval.atom trivial)
    (SrcEval.quotMk (c := `Quot.mk) (us := [l1]) (qv := QuotMk_val) (α := tB) (r := cR) (by krfl) rfl
      (ev_frz hg) (ok_clean (F := 100) (by krfl) rfl))
    (by krfl) rfl (ok_clean (guard hg (t := liftOf (qmOf cT)) (by simp)) (by krfl))
    ⟨.succ .zero, 100, rfl, by krfl⟩ ev_cT

end EraseProof.Test.NV4
