import EraseProof.Test.NV1Data
import EraseProof.Test.Run

/-!
# NV-1 through the entry point of `#erase`

The hypotheses `hfrag` and `hrun` of the final theorem (`MR E/ErasureFunctionProperties.v:657
erase_correct`: the program is in the fragment, and `erase … = t'`, `erase_global_deps … = Σ'`)
on NV-1 (`Test/NV1Data.lean`). `hcollect` computes the fragment test's closure `D` of `e` by
kernel evaluation of the shipping `collectDeps`. `hrun` is the run of the entry point: `route`
takes the pure path over `D`, and the pure path's run (`hpure`) is evaluated one traversal call
at a time (`Test/Run.lean`), from the constructors (`visitConstructor_run`) and the alternatives
(`visitAlt_run`) up through the `case` on `B` (`visitCasesOn_run`, `visitCases_run`), `B.neg`'s
value (`negVal_run`), its registration (`visitMutual_neg_run`, `kername_neg_run`) and the term
(`e_run`), with the traversal's maps read through the `Std.HashMap` lemmas.
-/

open Lean Erasure EraseProof.Test

namespace EraseProof.Test.NV1

/-- The closure of `e`, in the order the fragment test returns it. -/
def D : List ConstantInfo :=
  [.recInfo B_rec, .defnInfo B_casesOn, .ctorInfo Bt_ctor, .ctorInfo Bf_ctor, .inductInfo B_ind,
    .defnInfo neg_def]

/-- The fragment test accepts `B.neg B.f` and returns the closure `D`, by kernel evaluation: the
hypothesis `hfrag` of the final theorem on NV-1. Reference: the environment `Σ'` of
`erase_global_deps` (`MR E/ErasureFunction.v:1602`). -/
theorem hcollect : collectDeps view cfg e = .ok D := rfl

/-- The pure backend's context over the closure. -/
def pc : PureCtx := ⟨D, view⟩

variable {st : ErasureState} {ps : PureState}

/-! ## The inductive `B` -/

/-- The λ□ inductive of `B`. -/
def iidB : InductiveId := ⟨mutualBlockKername [`B], 0⟩

/-- The argument masks of `B`'s constructors (no field). -/
def masksB : InductiveArgMasks := [#[], #[]]

/-- The λ□ body of `B`. -/
def bodyB : OneInductiveBody :=
  { name := toString `B, propositional := false,
    ctors := [⟨toString `B.f, 0⟩, ⟨toString `B.t, 0⟩], projs := [] }

/-- The state after registering `B`. -/
def stB (st : ErasureState) : ErasureState :=
  { st with
    inductives := st.inductives.insert `B (iidB, masksB)
    gdecls := (mutualBlockKername [`B], .inductiveDecl ⟨.finite, 0, [bodyB]⟩) :: st.gdecls }

/-- `register_inductive` on `B` when it is not registered: registers its λ□ block. Reference: the
`InductiveDecl` of `erase_global_deps` (`MR E/ErasureFunction.v:1602`). -/
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
  simp only [Std.HashMap.getElem!_insert_self]
  rfl

/-- `register_inductive` on `B` when it is registered. Reference: none. -/
theorem register_B_found {tc : TravCtx} (h : st.inductives[`B]? = some (iidB, masksB)) :
    (register_inductive (m := PureM) B_ind).runPure st tc pc ps = .ok (((iidB, masksB), st), ps) := by
  rw [register_inductive]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, show B_ind.name = `B from rfl, h]
  rfl

theorem stB_B : (stB st).inductives[`B]? = some (iidB, masksB) := by
  simp only [stB, Std.HashMap.getElem?_insert_self]

/-! ## Constructors and alternatives -/

/-- `visitConstructor` on `B.f` (index 0) or `B.t` (index 1) without arguments, `B` registered.
Reference: the `tConstruct` case of `erase` (`MR E/ErasureFunction.v:1014`). -/
theorem visitConstructor_run {n k : Nat} {L : LocalContext} {ls : List Local}
    {F : Option (Std.HashMap Name FVarId)} {c : Name}
    (hc : c = `B.f ∧ k = 0 ∨ c = `B.t ∧ k = 1)
    (h : st.inductives[`B]? = some (iidB, masksB)) :
    (visitConstructor (m := PureM) (n + 2) c #[]).runPure st ⟨L, ls, F, {}⟩ pc ps =
      .ok ((.construct iidB k [], st), ps) := by
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · rw [visitConstructor]
    apply bind_ok rfl
    apply bind_ok rfl
    apply bind_ok (register_B_found h)
    simp only [toArray_toSubarray]
    krfl

/-- The free variable of the traversal's first fresh local. -/
def xb : FVarId := ⟨.num `_pure 0⟩

/-- The local of `B.neg`'s binder `b`. -/
def lb : Local := ⟨xb, `b, tB, none⟩

/-- `visitExpr` on `B.f` or `B.t`, at the top or under `b`: the oracle keeps it and it is a
constructor. Reference: the `tConstruct` case of `erase` (`MR E/ErasureFunction.v:1014`). -/
theorem visitExpr_ctor_run {n k : Nat} {L : LocalContext} {ls : List Local}
    {F : Option (Std.HashMap Name FVarId)}
    {c : Name} (hc : c = `B.f ∧ k = 0 ∨ c = `B.t ∧ k = 1) (hls : ls = [] ∨ ls = [lb])
    (h : st.inductives[`B]? = some (iidB, masksB)) :
    (visitExpr (m := PureM) (n + 6) (.const c [])).runPure st ⟨L, ls, F, {}⟩ pc ps =
      .ok ((.construct iidB k [], st), ps) := by
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hls with rfl | rfl <;>
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
    exact visitConstructor_run (by simp) h

/-- `visitAlt` on an alternative `B.f` or `B.t` without fields, under `b`. Reference: the branches
of the `tCase` case of `erase` (`MR E/ErasureFunction.v:1016`). -/
theorem visitAlt_run {n k : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)}
    {c : Name} (hc : c = `B.f ∧ k = 0 ∨ c = `B.t ∧ k = 1)
    (h : st.inductives[`B]? = some (iidB, masksB)) :
    (visitAlt (m := PureM) (n + 7) 0 #[] [] (.const c [])).runPure st ⟨L, [lb], F, {}⟩ pc ps =
      .ok ((([], .construct iidB k []), st), ps) := by
  rw [visitAlt]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := tB) (st' := st) (ps' := ps) ?_ ?_
  · rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> krfl
  rw [lambdaOrIntroToArity]
  apply bind_ok (visitExpr_ctor_run hc (.inr rfl) h)
  krfl

/-! ## The `case` on `B` -/

/-- `visitCases`'s alternatives of `B.neg`'s `casesOn`: `B.f ↦ B.t`, `B.t ↦ B.f`. -/
def altsNeg : Std.HashMap Name (Nat × Expr) :=
  ((∅ : Std.HashMap Name (Nat × Expr)).insert `B.f (0, cT)).insert `B.t (0, cF)

theorem altsNeg_f : altsNeg[`B.f]? = some (0, cT) := by
  simp only [altsNeg, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]; rfl

theorem altsNeg_t : altsNeg[`B.t]? = some (0, cF) := by
  simp only [altsNeg, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]; rfl

theorem altsNeg_all : ([`B.f, `B.t].all fun x => altsNeg.contains x) = true := by
  simp only [altsNeg, Std.HashMap.contains_insert, Std.HashMap.contains_empty]; rfl

/-- The erasure of `B.neg`'s body: the λ□ `case` on `b`. -/
def caseNeg : LBTerm :=
  .case (iidB, 0) (.fvar xb) [([], .construct iidB 1 []), ([], .construct iidB 0 [])]

/-- `visitCasesOn` on `B.neg`'s alternatives and the discriminant `b`, `B` not registered: the
λ□ `case`, with `B` registered. Reference: the `tCase` case of `erase`
(`MR E/ErasureFunction.v:1016`). -/
theorem visitCasesOn_run {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)}
    (h : st.inductives[`B]? = none) :
    (visitCasesOn (m := PureM) (n + 9) B_ind altsNeg ∅ none (.fvar xb)).runPure st
      ⟨L, [lb], F, {}⟩ pc ps = .ok ((caseNeg, stB st), ps) := by
  rw [visitCasesOn]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok (register_B_new h)
  simp only [show B_ind.ctors = [`B.f, `B.t] from rfl, List.forIn_cons, List.forIn_nil, bind_assoc,
    altsNeg_f, altsNeg_t, Std.HashMap.getD_empty]
  refine bind_ok (a := .yield (#[([], .construct iidB 1 [])], ([#[]] : List ConstructorArgMask)))
    (st' := stB st) (ps' := ps) ?_ ?_
  · apply bind_ok (visitAlt_run (.inr ⟨rfl, rfl⟩) stB_B)
    rfl
  refine bind_ok (a := (#[([], .construct iidB 1 []), ([], .construct iidB 0 [])],
    ([] : List ConstructorArgMask))) (st' := stB st) (ps' := ps) ?_ ?_
  · refine bind_ok (a := .yield (#[([], .construct iidB 1 []), ([], .construct iidB 0 [])],
      ([] : List ConstructorArgMask))) (st' := stB st) (ps' := ps) ?_ ?_
    · apply bind_ok (visitAlt_run (.inl ⟨rfl, rfl⟩) stB_B)
      rfl
    · rfl
  rfl

/-- The recognizer's answer on `B.casesOn`. -/
def ciB : CasesInfo :=
  { declName := `B.casesOn, indName := `B, arity := 4, discrPos := 1, motivePos := 0,
    altsRange := 2...4, altNumParams := #[.ctor `B.f 0, .ctor `B.t 0] }

/-- The shipping recognizer recognizes `B.casesOn` over the closure. Reference: none. -/
theorem casesInfo_B : casesInfo? D `B.casesOn = some ciB := by krfl

/-- The motive `fun x => B` of `B.neg`'s `casesOn`. -/
def motNeg : Expr := .lam `x tB tB .default

/-- `visitCases` on `B.neg`'s `casesOn` under `b`: the discriminant's sort is never `Prop`, so
the result is the λ□ `case`. Reference: the `tCase` case of `erase`
(`MR E/ErasureFunction.v:1016`). -/
theorem visitCases_run {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)}
    (h : st.inductives[`B]? = none) :
    (visitCases (m := PureM) (n + 12) ciB #[motNeg, .fvar xb, cT, cF]).runPure st
      ⟨L, [lb], F, {}⟩ pc ps = .ok ((caseNeg, stB st), ps) := by
  rw [visitCases]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := .succ .zero) (st' := st) (ps' := ps) (by krfl) ?_
  have hr : (ciB.altsRange.toList) = [2, 3] := by simp [ciB, Nat.toList_rco_eq_ite]
  simp only [← forIn'_eq_forIn, Std.Rco.forIn'_eq_forIn'_toList, hr, List.forIn'_cons,
    List.forIn'_nil]
  refine bind_ok (a := (altsNeg, none, ?sEnd)) (st' := st) (ps' := ps) ?_ ?_
  case sEnd => exact (ciB.altNumParams.toSubarray 2 2)
  · rfl
  refine bind_ok (a := .fvar xb) (st' := st) (ps' := ps) (by krfl) ?_
  simp only [show B_ind.ctors = [`B.f, `B.t] from rfl, altsNeg_all, ite_true]
  apply bind_ok (visitCasesOn_run h)
  rw [show ciB.arity = (#[motNeg, Expr.fvar xb, cT, cF] : Array Expr).size from rfl,
    forIn_toSubarray_size]
  rfl

/-! ## `B.neg` -/

/-- `B.neg`'s body under its binder: `B.casesOn.{1} (fun x => B) b B.t B.f`. -/
def bodyNeg : Expr :=
  .app (.app (.app (.app (.const `B.casesOn [.succ .zero]) motNeg) (.fvar xb)) cT) cF

theorem withApp_bodyNeg {γ : Sort _} (k : Expr → Array Expr → γ) :
    bodyNeg.withApp k = k (.const `B.casesOn [.succ .zero]) #[motNeg, .fvar xb, cT, cF] := by
  krfl

/-- `visitExpr` on `B.neg`'s body under `b`: a saturated recognized `casesOn`. Reference: the
`tCase` case of `erase` (`MR E/ErasureFunction.v:1016`). -/
theorem bodyNeg_run {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)}
    (h : st.inductives[`B]? = none) :
    (visitExpr (m := PureM) (n + 15) bodyNeg).runPure st ⟨L, [lb], F, {}⟩ pc ps =
      .ok ((caseNeg, stB st), ps) := by
  rw [bodyNeg, visitExpr, ← bodyNeg]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ps) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 13) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_bodyNeg]
  refine bind_ok (a := some ciB) (st' := st) (ps' := ps) (by krfl) ?_
  change (withAppEtaToMinArity (m := PureM) (n + 12) _ 4 _).runPure _ _ _ _ = _
  rw [withAppEtaToMinArity]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := .app motNeg (.fvar xb)) (st' := st) (ps' := ps) (by krfl) ?_
  rw [withApp_bodyNeg, withAppEtaToMinArity.go]
  exact visitCases_run h

/-- The erasure of `B.neg`'s value. -/
def negL : LBTerm := .lambda (binderNameOf `b) (_root_.abstract xb caseNeg)

/-- `visitExpr` on `B.neg`'s value, from the counter's first variable. Reference: the `tLambda`
case of `erase` (`MR E/ErasureFunction.v:1003`). -/
theorem negVal_run {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)}
    (h : st.inductives[`B]? = none) :
    (visitExpr (m := PureM) (n + 17) negVal).runPure st ⟨L, [], F, {}⟩ pc ⟨0⟩ =
      .ok ((negL, stB st), ⟨1⟩) := by
  rw [negVal, visitExpr, ← negVal]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [visitLambda]
  refine bind_ok (a := xb) (st' := st) (ps' := ⟨1⟩) rfl ?_
  refine bind_ok (a := caseNeg) (st' := stB st) (ps' := ⟨1⟩) (bodyNeg_run h) ?_
  rfl

/-- The state after erasing `B.neg`. -/
def stNeg (st : ErasureState) : ErasureState :=
  { stB st with
    constants := (stB st).constants.insert `B.neg (toKername `B.neg)
    gdecls := (toKername `B.neg, .constantDecl ⟨some negL⟩) :: (stB st).gdecls }

/-- `visitMutual` on `B.neg`: a single, non-recursive definition without attributes, erased to
a λ□ constant. Reference: `erase_constant_body` (`MR E/ErasureFunction.v:1309`) in
`erase_global_deps` (`MR E/ErasureFunction.v:1602`). -/
theorem visitMutual_neg_run {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)}
    (h : st.inductives[`B]? = none) :
    (visitMutual (m := PureM) (n + 18) `B.neg).runPure st ⟨L, [], F, {}⟩ pc ⟨0⟩ =
      .ok (((), stNeg st), ⟨1⟩) := by
  rw [visitMutual]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := negL) (st' := stB st) (ps' := ⟨1⟩) ?_ ?_
  · rw [runPure_withReader]
    apply bind_ok rfl
    refine bind_ok (a := negVal) (st' := st) (ps' := ⟨0⟩) rfl ?_
    exact negVal_run (L := L) (F := none) h
  rfl

/-- `get_constant_kername` on `B.neg`, not yet erased. Reference: `erase_global_deps`
(`MR E/ErasureFunction.v:1602`). -/
theorem kername_neg_run {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)}
    (hc : st.constants[`B.neg]? = none) (h : st.inductives[`B]? = none) :
    (get_constant_kername (m := PureM) (n + 19) `B.neg).runPure st ⟨L, [], F, {}⟩ pc ⟨0⟩ =
      .ok ((toKername `B.neg, stNeg st), ⟨1⟩) := by
  rw [get_constant_kername]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, hc]
  apply bind_ok (visitMutual_neg_run h)
  apply bind_ok rfl
  simp only [stNeg, Std.HashMap.getElem!_insert_self]
  rfl

/-- `visitConst` on `B.neg` outside a recursive block. Reference: the `tConst` case of `erase`
(`MR E/ErasureFunction.v:999`). -/
theorem visitConst_neg_run {n : Nat} {L : LocalContext}
    (hc : st.constants[`B.neg]? = none) (h : st.inductives[`B]? = none) :
    (visitConst (m := PureM) (n + 20) (.const `B.neg [])).runPure st ⟨L, [], none, {}⟩ pc ⟨0⟩ =
      .ok ((.const (toKername `B.neg), stNeg st), ⟨1⟩) := by
  rw [visitConst]
  apply bind_ok rfl
  apply bind_ok (kername_neg_run hc h)
  rfl

theorem stNeg_B : (stNeg st).inductives[`B]? = some (iidB, masksB) := by
  simp only [stNeg, stB, Std.HashMap.getElem?_insert_self]

/-! ## The run on NV-1 -/

/-- The erasure of `e`. -/
def t0 : LBTerm := .app (.const (toKername `B.neg)) (.construct iidB 0 [])

/-- `visitExpr` on `e`. Reference: the `tApp` case of `erase` (`MR E/ErasureFunction.v:1009`). -/
theorem e_run {n : Nat} {L : LocalContext}
    (hc : st.constants[`B.neg]? = none) (h : st.inductives[`B]? = none) :
    (visitExpr (m := PureM) (n + 23) e).runPure st ⟨L, [], none, {}⟩ pc ⟨0⟩ =
      .ok ((t0, stNeg st), ⟨1⟩) := by
  rw [e, visitExpr, ← e]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 21) _).runPure _ _ _ _ = _
  rw [visitConstApp, e, withApp_app1 _ _ _ rfl]
  refine bind_ok (a := none) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  refine bind_ok (a := none) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  apply bind_ok (visitConst_neg_run hc h)
  rw [visitAppArgs, ← Array.foldlM_toList]
  simp only [List.foldlM_cons, List.foldlM_nil]
  refine bind_ok (a := t0) (st' := stNeg st) (ps' := ⟨1⟩) ?_ ?_
  · apply bind_ok (visitExpr_ctor_run (k := 0) (.inl ⟨rfl, rfl⟩) (.inl rfl) stNeg_B)
    rfl
  rfl

/-- The program `#erase` emits for NV-1. -/
def p0 : Program :=
  .untyped [(toKername `B.neg, .constantDecl ⟨some negL⟩),
    (mutualBlockKername [`B], .inductiveDecl ⟨.finite, 0, [bodyB]⟩)] (some t0)

/-- The pure path on NV-1's closure returns `p0` and no constant to inline. Reference: `erase`
(`MR E/ErasureFunction.v:989`) and `erase_global_deps` (`MR E/ErasureFunction.v:1602`). -/
theorem hpure : erasePure view cfg D e = .ok (p0, []) := by
  rw [erasePure, show travFuel = (travFuel - 23) + 23 by decide]
  rw [show ((visitExpr (m := PureM) (travFuel - 23 + 23) e).runPure {} { «config» := cfg }
    ⟨D, view⟩ {}) = .ok ((t0, stNeg {}), ⟨1⟩) from
      e_run Std.HashMap.getElem?_empty Std.HashMap.getElem?_empty]
  rfl

/-- `#erase`'s entry point on NV-1 returns `p0` and no constant to inline: the hypothesis `hrun`
of the final theorem on NV-1. Reference: the hypotheses `erase … = t'` and
`erase_global_deps … = Σ'` of `erase_correct` (`MR E/ErasureFunctionProperties.v:657`). -/
theorem hrun : eraseEntry view cfg e = pure (p0, []) := by
  simp only [eraseEntry, route, hcollect, hpure]

end EraseProof.Test.NV1
