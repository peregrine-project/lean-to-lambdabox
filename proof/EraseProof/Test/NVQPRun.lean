import EraseProof.Test.NVQPData
import EraseProof.Test.NVSRun

/-!
# NV-QP through the entry point of `#erase`

The hypotheses `hfrag` and `hrun` of the final theorem (`MR E/ErasureFunctionProperties.v:657
erase_correct`) on NV-QP (`Test/NVQPData.lean`). `hcollect` computes the fragment test's closure `D`
by kernel evaluation: the definitions the term reaches, the theorem `orU._proof_1` (its type only),
the quotient constants `Quot.mk`, `Quot.lift` and `Quot`, `Eq` (from `Quot.lift`'s type), `Prod` and
`B` with their recursors. `hrun` is the run of the entry point, evaluated one traversal call at a
time (`Test/Run.lean`, with the steps on any closure of `Test/NVSRun.lean`), cut at every read of
the traversal's maps. `e` erases `useTF` (`kername_use`), whose value erases `orU` (`kername_orU`)
applied to the class `Quot.mk swapR (Prod.mk B.t B.f)`, which `visitConstApp`'s `Quot.mk` branch
erases as its element, the pair (`qm_run`). `orU`'s value `Quot.lift (fun p => orB p.1 p.2)
orU._proof_1` has five arguments: `visitConstApp`'s `Quot.lift` branch η-expands it to the sixth,
`a`, and erases the lifted function applied to `a`, without the respect proof (`orUV_run`). The
lifted function erases `orB` (`kername_orB`), whose body erases the `@[inline]` matcher
`orB.match_1`, marked for inlining, whose `B.casesOn` is a λ□ `case` and registers `B`
(`kername_match`), and the projections `Prod.fst` and `Prod.snd`, whose primitive projections are
λ□ projections of `Prod` (registered by the first, `kername_fst`, `kername_snd`). The fresh locals
are numbered in the order the traversal opens them (`lsA`, …, `lsF`); the states of the run are
`s0`, …, `s9`. `p0` and `inl0` are the program `#erase` emits and the constants it marks for
inlining. `hcollectFT` is the fragment test on the second term `useFT`, whose emitted program
`tools/NVEmit.lean` checks.
-/

open Lean Erasure EraseProof.Test

namespace EraseProof.Test.NVQP

open EraseProof.Test.NV1 (tB cF cT B_ind Bf_ctor Bt_ctor B_rec B_casesOn iidB masksB bodyB stB)
open EraseProof.Test.NVP (Eq_ind Eq_refl Eq_rec l1)
open EraseProof.Test.NVQ (Quot_val QuotMk_val QuotLift_val)

/-- The closure of `e`, in the order the fragment test returns it. -/
def D : List ConstantInfo :=
  [.quotInfo QuotMk_val, .thmInfo resp_thm, .recInfo B_rec, .defnInfo B_casesOn,
    .defnInfo orB_match_1, .defnInfo orB_def, .quotInfo QuotLift_val, .defnInfo Prod_fst,
    .defnInfo Prod_snd, .ctorInfo Eq_refl, .recInfo Eq_rec, .inductInfo Eq_ind, .defnInfo swapR_def,
    .ctorInfo Prod_mk, .recInfo Prod_rec, .inductInfo Prod_ind, .quotInfo Quot_val, .defnInfo orU_def,
    .ctorInfo Bt_ctor, .ctorInfo Bf_ctor, .inductInfo B_ind, .defnInfo useTF_def]

/-- The fragment test accepts `e` and returns the closure `D`, by kernel evaluation. Reference: the
environment `Σ'` of `erase_global_deps` (`MR E/ErasureFunction.v:1602`). -/
theorem hcollect : collectDeps view cfg e = .ok D := rfl

/-- The closure of the second term `eFT`: `D` with `useFT` in place of `useTF`. -/
def DFT : List ConstantInfo := D.dropLast ++ [.defnInfo useFT_def]

/-- The fragment test accepts `eFT`, the same function on the other representative of the class,
and returns the closure `DFT`, by kernel evaluation. -/
theorem hcollectFT : collectDeps view cfg eFT = .ok DFT := rfl

/-- The pure backend's context over the closure. -/
def pc : PureCtx := ⟨D, view⟩

/-! ## The emitted program -/

/-- The λ□ inductive of `Prod`, the argument masks of `Prod.mk` (both fields kept), and its body (a
structure: one projection per kept field). -/
def iidPr : InductiveId := ⟨mutualBlockKername [`Prod], 0⟩
def masksPr : InductiveArgMasks := [#[.keep, .keep]]
def bodyPr : OneInductiveBody :=
  { name := toString `Prod, propositional := false, ctors := [⟨toString `Prod.mk, 2⟩],
    projs := [⟨"0"⟩, ⟨"1"⟩] }

/-- The projection `i` of `Prod`. -/
def projPr (i : Nat) : ProjectionInfo := { indType := iidPr, paramCount := 2, fieldIdx := i }

/-- `B.f`, `B.t` and `Prod.mk` in λ□. -/
def fL : LBTerm := .construct iidB 0 []
def tL : LBTerm := .construct iidB 1 []
def mkL : LBTerm := .construct iidPr 0 []

/-- `Prod.mk □ □ a b` in λ□. -/
def pairL (a b : LBTerm) : LBTerm := .app (.app (.app (.app mkL .box) .box) a) b

/-- The erasure of `orU (Quot.mk swapR (Prod.mk a b))`: `orU (Prod.mk □ □ a b)`. -/
def useL (a b : LBTerm) : LBTerm := .app (.const (toKername `orU)) (pairL a b)

/-- `fun α β self => self.i`: `Prod.fst` and `Prod.snd` in λ□ (the binder names `α` and `β`
print as anonymous). -/
def projVL (i : Nat) : LBTerm :=
  .lambda (binderNameOf `α) (.lambda (binderNameOf `β)
    (.lambda (binderNameOf `self) (.proj (projPr i) (.bvar 0))))

/-- `c □ □ x` for the projection function `c`. -/
def projAppL (c : Name) (x : LBTerm) : LBTerm := .app (.app (.app (.const (toKername c)) .box) .box) x

/-- `fun a => (fun p => orB p.1 p.2) a`: `orU`, η-expanded to the arity of `Quot.lift`. -/
def orUVL : LBTerm :=
  .lambda (binderNameOf `a) (.app (.lambda (binderNameOf `p)
    (.app (.app (.const (toKername `orB)) (projAppL `Prod.fst (.bvar 0)))
      (projAppL `Prod.snd (.bvar 0)))) (.bvar 0))

/-- `fun x y => orB.match_1 □ x y (fun b => b) (fun _ => B.t)` -/
def orBVL : LBTerm :=
  .lambda (binderNameOf (hyg 7)) (.lambda (binderNameOf (hyg 8))
    (.app (.app (.app (.app (.app (.const (toKername `orB.match_1)) .box) (.bvar 1)) (.bvar 0))
      (.lambda (binderNameOf `b) (.bvar 0))) (.lambda (binderNameOf (hyg 42)) tL)))

/-- `fun motive x y h_1 h_2 => match x with | B.f => h_1 y | B.t => h_2 y` -/
def matchVL : LBTerm :=
  .lambda (binderNameOf `motive) (.lambda (binderNameOf (hyg2 7 26))
    (.lambda (binderNameOf (hyg2 8 29)) (.lambda (binderNameOf `h_1) (.lambda (binderNameOf `h_2)
      (.case (iidB, 0) (.bvar 3) [([], .app (.bvar 1) (.bvar 2)), ([], .app (.bvar 0) (.bvar 2))])))))

/-- The constants `#erase` marks for inlining: the matcher. -/
def inl0 : List Kername := [toKername `orB.match_1]

/-- The λ□ environment `#erase` emits for `useTF` and `useFT` below the term's own constant. -/
def lenv0 : List (Kername × GlobalDecl) :=
  [(toKername `orU, .constantDecl ⟨some orUVL⟩),
    (toKername `Prod.snd, .constantDecl ⟨some (projVL 1)⟩),
    (toKername `Prod.fst, .constantDecl ⟨some (projVL 0)⟩),
    (mutualBlockKername [`Prod], .inductiveDecl ⟨.finite, 2, [bodyPr]⟩),
    (toKername `orB, .constantDecl ⟨some orBVL⟩),
    (toKername `orB.match_1, .constantDecl ⟨some matchVL⟩),
    (mutualBlockKername [`B], .inductiveDecl ⟨.finite, 0, [bodyB]⟩)]

/-- The program `#erase` emits for NV-QP. -/
def p0 : Program :=
  .untyped ((toKername `useTF, .constantDecl ⟨some (useL tL fL)⟩) :: lenv0)
    (some (.const (toKername `useTF)))

/-! ## The run: tools, states, locals -/

open EraseProof.Test.NVS (xf xv loc lam_run appArgs_nil appArgs_cons register_found stDef stInl
  stDefI)

/-- The state after registering `Prod`. -/
def stPr (st : ErasureState) : ErasureState :=
  { st with
    inductives := st.inductives.insert `Prod (iidPr, masksPr)
    gdecls := (mutualBlockKername [`Prod], .inductiveDecl ⟨.finite, 2, [bodyPr]⟩) :: st.gdecls }

variable {st : ErasureState} {ps : PureState} {dc : Name}

/-- `register_inductive` on `B` when it is not registered. Reference: the `InductiveDecl` of
`erase_global_deps` (`MR E/ErasureFunction.v:1602`). -/
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

/-- `register_inductive` on `Prod` when it is not registered. Reference: as `register_B_new`. -/
theorem register_Pr_new {L : LocalContext} {ls : List Local} {F : Option (Std.HashMap Name FVarId)}
    (h : st.inductives[`Prod]? = none) :
    (register_inductive (m := PureM) Prod_ind).runPure st ⟨L, ls, F, cfg, dc⟩ pc ps =
      .ok (((iidPr, masksPr), stPr st), ps) := by
  rw [register_inductive]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, show Prod_ind.name = `Prod from rfl, h]
  apply bind_ok (a := [bodyPr])
    (st' := { st with inductives := st.inductives.insert `Prod (iidPr, masksPr) }) (ps' := ps) rfl
  apply bind_ok rfl
  apply bind_ok rfl
  simp only [Std.HashMap.getElem?_insert_self]
  rfl

/-- The binder types of the matcher's alternatives, under its motive (the fourth local). -/
def h1T : Expr := .forallE `b tB (.app (.app (xv 4) cF) (.bvar 0)) .default
def h2T : Expr := .forallE (hyg 42) tB (.app (.app (xv 4) cT) (.bvar 0)) .default

/-- The locals, in the order the traversal opens them: `orU`'s η-expansion `a` (0), `fun p` (1),
`orB`'s two binders (2, 3), `orB.match_1`'s five (4–8), `orB`'s alternatives (9, 10), the binders
of `Prod.fst` (11–13) and of `Prod.snd` (14–16). -/
def lsA : List Local := [loc 0 `a tQ]
def lsP : List Local := loc 1 `p tP :: lsA
def lsO : List Local := loc 3 (hyg 8) tB :: loc 2 (hyg 7) tB :: lsP
def lsM : List Local :=
  loc 8 `h_2 h2T :: loc 7 `h_1 h1T :: loc 6 (hyg2 8 29) tB :: loc 5 (hyg2 7 26) tB ::
    loc 4 `motive motMTy :: lsO
def lsT : List Local := loc 10 (hyg 42) tB :: lsO

/-! ## `B.casesOn` in `orB.match_1` -/

/-- `visitExpr` on `B.f` or `B.t`, `B` registered. Reference: the `tConstruct` case of `erase`
(`MR E/ErasureFunction.v:1014`). -/
theorem cB_run {n k : Nat} {L : LocalContext} {ls : List Local} {c : Name}
    (hc : c = `B.f ∧ k = 0 ∨ c = `B.t ∧ k = 1) (hls : ls = [] ∨ ls = lsT)
    (h : st.inductives[`B]? = some (iidB, masksB)) :
    (visitExpr (m := PureM) (n + 6) (.const c [])).runPure st ⟨L, ls, none, cfg, dc⟩ pc ps =
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
    rw [visitConstructor]
    apply bind_ok rfl
    apply bind_ok rfl
    apply bind_ok (register_found (iv := B_ind) h)
    simp only [toArray_toSubarray]
    krfl

/-- The alternatives `h_1 y` and `h_2 y` of the matcher's `casesOn`. -/
def alt1 : Expr := .app (xv 7) (xv 6)
def alt2 : Expr := .app (xv 8) (xv 6)
def alt1L : LBTerm := .app (.fvar (xf 7)) (.fvar (xf 6))
def alt2L : LBTerm := .app (.fvar (xf 8)) (.fvar (xf 6))

/-- `visitCasesOn`'s alternatives: `B.f ↦ h_1 y`, `B.t ↦ h_2 y`. -/
def altsM : Std.HashMap Name (Nat × Expr) :=
  ((∅ : Std.HashMap Name (Nat × Expr)).insert `B.f (0, alt1)).insert `B.t (0, alt2)

theorem altsM_f : altsM[`B.f]? = some (0, alt1) := by
  simp only [altsM, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]; rfl

theorem altsM_t : altsM[`B.t]? = some (0, alt2) := by
  simp only [altsM, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]; rfl

theorem altsM_all : ([`B.f, `B.t].all fun x => altsM.contains x) = true := by
  simp only [altsM, Std.HashMap.contains_insert, Std.HashMap.contains_empty]; rfl

/-- The erasure of the matcher's body: the λ□ `case` on its first discriminant. -/
def caseRL : LBTerm := .case (iidB, 0) (.fvar (xf 5)) [([], alt1L), ([], alt2L)]

/-- `visitCasesOn` on the matcher's alternatives and its first discriminant, `B` not registered.
Reference: the `tCase` case of `erase` (`MR E/ErasureFunction.v:1016`). -/
theorem visitCasesOn_run {n : Nat} {L : LocalContext} (h : st.inductives[`B]? = none) :
    (visitCasesOn (m := PureM) (n + 9) B_ind altsM ∅ none (.fvar (xf 5))).runPure st
      ⟨L, lsM, none, cfg, dc⟩ pc ps = .ok ((caseRL, stB st), ps) := by
  rw [visitCasesOn]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok (register_B_new h)
  simp only [show B_ind.ctors = [`B.f, `B.t] from rfl, List.forIn_cons, List.forIn_nil, bind_assoc,
    altsM_f, altsM_t, Std.HashMap.getD_empty]
  refine bind_ok (a := .yield (#[([], alt1L)], ([#[]] : List ConstructorArgMask)))
    (st' := stB st) (ps' := ps) ?_ ?_
  · refine bind_ok (a := (([] : List BinderName), alt1L)) (st' := stB st) (ps' := ps) (by krfl) ?_
    rfl
  refine bind_ok (a := (#[([], alt1L), ([], alt2L)], ([] : List ConstructorArgMask)))
    (st' := stB st) (ps' := ps) ?_ ?_
  · refine bind_ok (a := .yield (#[([], alt1L), ([], alt2L)], ([] : List ConstructorArgMask)))
      (st' := stB st) (ps' := ps) ?_ ?_
    · refine bind_ok (a := (([] : List BinderName), alt2L)) (st' := stB st) (ps' := ps) (by krfl) ?_
      rfl
    · rfl
  rfl

/-- The motive `fun x => motive x y` of the matcher's `casesOn`. -/
def motM : Expr := .lam `x tB (.app (.app (xv 4) (.bvar 0)) (xv 6)) .default

/-- The recognizer's answer on `B.casesOn`. -/
def ciB : CasesInfo :=
  { declName := `B.casesOn, indName := `B, arity := 4, discrPos := 1, motivePos := 0,
    altsRange := 2...4, altNumParams := #[.ctor `B.f 0, .ctor `B.t 0] }

/-- `visitCases` on the matcher's `casesOn`. Reference: the `tCase` case of `erase`
(`MR E/ErasureFunction.v:1016`). -/
theorem visitCases_run {n : Nat} {L : LocalContext} (h : st.inductives[`B]? = none) :
    (visitCases (m := PureM) (n + 12) ciB #[motM, xv 5, alt1, alt2]).runPure st
      ⟨L, lsM, none, cfg, dc⟩ pc ps = .ok ((caseRL, stB st), ps) := by
  rw [visitCases]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := Level.succ .zero) (st' := st) (ps' := ps) (by krfl) ?_
  have hr : (ciB.altsRange.toList) = [2, 3] := by simp [ciB, Nat.toList_rco_eq_ite]
  simp only [← forIn'_eq_forIn, Std.Rco.forIn'_eq_forIn'_toList, hr, List.forIn'_cons,
    List.forIn'_nil]
  refine bind_ok (a := (altsM, none, ?sEnd)) (st' := st) (ps' := ps) ?_ ?_
  case sEnd => exact (ciB.altNumParams.toSubarray 2 2)
  · rfl
  refine bind_ok (a := .fvar (xf 5)) (st' := st) (ps' := ps) (by krfl) ?_
  simp only [show B_ind.ctors = [`B.f, `B.t] from rfl, altsM_all, ite_true]
  apply bind_ok (visitCasesOn_run h)
  rw [show ciB.arity = (#[motM, xv 5, alt1, alt2] : Array Expr).size from rfl,
    forIn_toSubarray_size]
  rfl

/-- The matcher's body. -/
def mbE : Expr := mkAppN (.const `B.casesOn [u1]) #[motM, xv 5, alt1, alt2]

theorem withApp_mbE {γ : Sort _} (k : Expr → Array Expr → γ) :
    mbE.withApp k = k (.const `B.casesOn [u1]) #[motM, xv 5, alt1, alt2] := by krfl

/-- `visitExpr` on the matcher's body: a saturated recognized `casesOn`. Reference: the `tCase`
case of `erase` (`MR E/ErasureFunction.v:1016`). -/
theorem mb_run {n : Nat} {L : LocalContext} (h : st.inductives[`B]? = none) :
    (visitExpr (m := PureM) (n + 15) mbE).runPure st ⟨L, lsM, none, cfg, dc⟩ pc ps =
      .ok ((caseRL, stB st), ps) := by
  rw [show mbE = .app (mkAppN (.const `B.casesOn [u1]) #[motM, xv 5, alt1]) alt2 from rfl,
    visitExpr, ← show mbE = .app (mkAppN (.const `B.casesOn [u1]) #[motM, xv 5, alt1]) alt2 from rfl]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ps) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 13) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_mbE]
  refine bind_ok (a := some ciB) (st' := st) (ps' := ps) (by krfl) ?_
  change (withAppEtaToMinArity (m := PureM) (n + 12) _ 4 _).runPure _ _ _ _ = _
  rw [withAppEtaToMinArity]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := .app motM (xv 5)) (st' := st) (ps' := ps) (by krfl) ?_
  rw [withApp_mbE, withAppEtaToMinArity.go]
  exact visitCases_run h

/-! ## `orB.match_1` and `orB` -/

/-- The erasure of the matcher's value. -/
def matchRL : LBTerm :=
  .lambda (binderNameOf `motive) (_root_.abstract (xf 4) (.lambda (binderNameOf (hyg2 7 26))
    (_root_.abstract (xf 5) (.lambda (binderNameOf (hyg2 8 29)) (_root_.abstract (xf 6)
      (.lambda (binderNameOf `h_1) (_root_.abstract (xf 7)
        (.lambda (binderNameOf `h_2) (_root_.abstract (xf 8) caseRL)))))))))

/-- The erasure of `orB`'s body: the matcher applied to □, the discriminants and the
alternatives. -/
def obRL : LBTerm :=
  .app (.app (.app (.app (.app (.const (toKername `orB.match_1)) .box) (.fvar (xf 2))) (.fvar (xf 3)))
    (.lambda (binderNameOf `b) (_root_.abstract (xf 9) (.fvar (xf 9)))))
    (.lambda (binderNameOf (hyg 42)) (_root_.abstract (xf 10) tL))

/-- The erasure of `orB`'s value. -/
def orBRL : LBTerm :=
  .lambda (binderNameOf (hyg 7)) (_root_.abstract (xf 2)
    (.lambda (binderNameOf (hyg 8)) (_root_.abstract (xf 3) obRL)))

/-- The states of the run, in order: the matcher marked for inlining (`s1`), `B` registered by its
`casesOn` (`s2`), the matcher erased (`s3`), `orB` (`s4`), `Prod` registered by the projection of
`Prod.fst` (`s5`), `Prod.fst` (`s6`), `Prod.snd` (`s7`), `orU` (`s8`), `useTF` (`s9`). -/
def s0 : ErasureState := {}
def s1 : ErasureState := stInl s0 `orB.match_1
def s2 : ErasureState := stB s1
def s3 : ErasureState := stDefI s2 `orB.match_1 matchRL
def s4 : ErasureState := stDef s3 `orB orBRL

/-- The erasure of `Prod.fst` (`i = 0`) and `Prod.snd` (`i = 1`), whose binders are the `k`-th to
`k + 2`-th locals. -/
def projRL (i k : Nat) : LBTerm :=
  .lambda (binderNameOf `α) (_root_.abstract (xf k) (.lambda (binderNameOf `β)
    (_root_.abstract (xf (k + 1)) (.lambda (binderNameOf `self) (_root_.abstract (xf (k + 2))
      (.proj (projPr i) (.fvar (xf (k + 2)))))))))

/-- The erasure of `orB p.1 p.2`, `p` the second local. -/
def lbRL : LBTerm :=
  .app (.app (.const (toKername `orB)) (projAppL `Prod.fst (.fvar (xf 1))))
    (projAppL `Prod.snd (.fvar (xf 1)))

/-- The erasure of the lifted function `fun p => orB p.1 p.2`. -/
def liftRL : LBTerm := .lambda (binderNameOf `p) (_root_.abstract (xf 1) lbRL)

/-- The erasure of `orU`'s value: `Quot.lift`'s η-expansion `fun a => (fun p => orB p.1 p.2) a`. -/
def orURL : LBTerm := .lambda (binderNameOf `a) (_root_.abstract (xf 0) (.app liftRL (.fvar (xf 0))))

def s5 : ErasureState := stPr s4
def s6 : ErasureState := stDef s5 `Prod.fst (projRL 0 11)
def s7 : ErasureState := stDef s6 `Prod.snd (projRL 1 14)
def s8 : ErasureState := stDef s7 `orU orURL
def s9 : ErasureState := stDef s8 `useTF (useL tL fL)

theorem s0_inductives : s0.inductives = ∅ := rfl
theorem s0_constants : s0.constants = ∅ := rfl

/-- Facts about the traversal's maps in the states of the run. -/
macro (name := _qpfact) "qpfact" : tactic => `(tactic| (simp only [s1, s2, s3, s4, s5, s6, s7, s8,
  s9, stDefI, stInl, stDef, stB, stPr, s0_inductives, s0_constants, Std.HashMap.getElem?_insert,
  Std.HashMap.getElem?_empty] <;> try rfl))

/-- `visitExpr` on the matcher's value, from the counter's fifth variable. Reference: the
`tLambda` case of `erase` (`MR E/ErasureFunction.v:1003`). -/
theorem matchV_run {n : Nat} {L : LocalContext} :
    (visitExpr (m := PureM) (n + 25) matchVal).runPure s1 ⟨L, lsO, none, cfg, dc⟩ pc ⟨4⟩ =
      .ok ((matchRL, s2), ⟨9⟩) :=
  lam_run (by krfl) fun _ => lam_run (by krfl) fun _ => lam_run (by krfl) fun _ =>
    lam_run (by krfl) fun _ => lam_run (by krfl) fun _ =>
      mb_run (n := n) (by simp only [s1, stInl, s0_inductives, Std.HashMap.getElem?_empty])

/-- `visitMutual` on `orB.match_1`: an `@[inline]` definition, marked for inlining and erased to a
λ□ constant. Reference: `erase_constant_body` (`MR E/ErasureFunction.v:1309`); the marking: none. -/
theorem visitMutual_match {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)} :
    (visitMutual (m := PureM) (n + 26) `orB.match_1).runPure s0 ⟨L, lsO, F, cfg, dc⟩ pc ⟨4⟩ =
      .ok (((), s3), ⟨9⟩) := by
  rw [visitMutual]
  iterate 10 apply bind_ok rfl
  refine bind_ok (a := matchRL) (st' := s2) (ps' := ⟨9⟩) ?_ ?_
  · rw [runPure_withReader]
    apply bind_ok rfl
    refine bind_ok (a := matchVal) (st' := s1) (ps' := ⟨4⟩) rfl ?_
    exact matchV_run (n := n)
  rfl

/-- `get_constant_kername` on `orB.match_1`, not yet erased. Reference: `erase_global_deps`
(`MR E/ErasureFunction.v:1602`). -/
theorem kername_match {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)} :
    (get_constant_kername (m := PureM) (n + 27) `orB.match_1).runPure s0 ⟨L, lsO, F, cfg, dc⟩ pc
      ⟨4⟩ = .ok ((toKername `orB.match_1, s3), ⟨9⟩) := by
  rw [get_constant_kername]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, s0_constants, Std.HashMap.getElem?_empty]
  apply bind_ok visitMutual_match
  apply bind_ok rfl
  simp only [s3, stDefI, stDef, Std.HashMap.getElem?_insert_self]
  rfl

/-- `orB`'s motive and alternatives. -/
def motO : Expr := .lam (hyg2 7 26) tB (.lam (hyg2 8 29) tB tB .default) .default
def altB : Expr := .lam `b tB (.bvar 0) .default
def altT : Expr := .lam (hyg 42) tB cT .default

/-- `orB`'s body under its two binders. -/
def obE : Expr := mkAppN (.const `orB.match_1 [l1]) #[motO, xv 2, xv 3, altB, altT]

theorem withApp_obE {γ : Sort _} (k : Expr → Array Expr → γ) :
    obE.withApp k = k (.const `orB.match_1 [l1]) #[motO, xv 2, xv 3, altB, altT] := by krfl

/-- `visitExpr` on the alternative `fun _ => B.t`, `B` registered. Reference: the `tLambda` and
`tConstruct` cases of `erase` (`MR E/ErasureFunction.v:1003`, `:1014`). -/
theorem altT_run {n : Nat} {L : LocalContext} :
    (visitExpr (m := PureM) (n + 8) altT).runPure s3 ⟨L, lsO, none, cfg, dc⟩ pc ⟨10⟩ =
      .ok ((.lambda (binderNameOf (hyg 42)) (_root_.abstract (xf 10) tL), s3), ⟨11⟩) :=
  lam_run (by krfl) fun _ => cB_run (.inr ⟨rfl, rfl⟩) (.inr rfl) (by qpfact)

/-- `visitExpr` on `orB`'s body: the λ□ constant of the matcher, erased on the way, applied to □
for the motive, to the discriminants and to the alternatives. Reference: the `tConst` and `tApp`
cases of `erase` (`MR E/ErasureFunction.v:999`, `:1006`). -/
theorem ob_run {n : Nat} {L : LocalContext} :
    (visitExpr (m := PureM) (n + 31) obE).runPure s0 ⟨L, lsO, none, cfg, dc⟩ pc ⟨4⟩ =
      .ok ((obRL, s3), ⟨11⟩) := by
  rw [show obE = .app (mkAppN (.const `orB.match_1 [l1]) #[motO, xv 2, xv 3, altB]) altT from rfl,
    visitExpr,
    ← show obE = .app (mkAppN (.const `orB.match_1 [l1]) #[motO, xv 2, xv 3, altB]) altT from rfl]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := s0) (ps' := ⟨4⟩) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 29) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_obE]
  refine bind_ok (a := none) (st' := s0) (ps' := ⟨4⟩) (by krfl) ?_
  refine bind_ok (a := none) (st' := s0) (ps' := ⟨4⟩) (by krfl) ?_
  refine bind_ok (a := some (.defnInfo orB_match_1)) (st' := s0) (ps' := ⟨4⟩) (by krfl) ?_
  refine bind_ok (a := .const (toKername `orB.match_1)) (st' := s3) (ps' := ⟨9⟩) ?_ ?_
  · rw [visitConst]
    apply bind_ok rfl
    refine bind_ok kername_match ?_
    rfl
  refine appArgs_cons (as := [xv 2, xv 3, altB, altT]) (r := .box) (st' := s3) (ps' := ⟨9⟩)
    (by krfl) ?_
  refine appArgs_cons (as := [xv 3, altB, altT]) (r := .fvar (xf 2)) (st' := s3) (ps' := ⟨9⟩)
    (by krfl) ?_
  refine appArgs_cons (as := [altB, altT]) (r := .fvar (xf 3)) (st' := s3) (ps' := ⟨9⟩)
    (by krfl) ?_
  refine appArgs_cons (as := [altT])
    (r := .lambda (binderNameOf `b) (_root_.abstract (xf 9) (.fvar (xf 9)))) (st' := s3)
    (ps' := ⟨10⟩) (by krfl) ?_
  refine appArgs_cons (as := []) (altT_run (n := n + 19)) ?_
  exact appArgs_nil

/-- `visitExpr` on `orB`'s value, from the counter's third variable. Reference: the `tLambda` case
of `erase` (`MR E/ErasureFunction.v:1003`). -/
theorem orBV_run {n : Nat} {L : LocalContext} :
    (visitExpr (m := PureM) (n + 35) orBVal).runPure s0 ⟨L, lsP, none, cfg, dc⟩ pc ⟨2⟩ =
      .ok ((orBRL, s3), ⟨11⟩) :=
  lam_run (by krfl) fun _ => lam_run (by krfl) fun _ => ob_run (n := n)

/-- `visitMutual` on `orB`: a single, non-recursive definition without attributes, erased to a λ□
constant. Reference: `erase_constant_body` (`MR E/ErasureFunction.v:1309`) in `erase_global_deps`
(`MR E/ErasureFunction.v:1602`). -/
theorem visitMutual_orB {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)} :
    (visitMutual (m := PureM) (n + 36) `orB).runPure s0 ⟨L, lsP, F, cfg, dc⟩ pc ⟨2⟩ =
      .ok (((), s4), ⟨11⟩) := by
  rw [visitMutual]
  iterate 8 apply bind_ok rfl
  refine bind_ok (a := orBRL) (st' := s3) (ps' := ⟨11⟩) ?_ ?_
  · rw [runPure_withReader]
    apply bind_ok rfl
    refine bind_ok (a := orBVal) (st' := s0) (ps' := ⟨2⟩) rfl ?_
    exact orBV_run (n := n)
  rfl

/-- `get_constant_kername` on `orB`, not yet erased. Reference: `erase_global_deps`
(`MR E/ErasureFunction.v:1602`). -/
theorem kername_orB {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)} :
    (get_constant_kername (m := PureM) (n + 37) `orB).runPure s0 ⟨L, lsP, F, cfg, dc⟩ pc ⟨2⟩ =
      .ok ((toKername `orB, s4), ⟨11⟩) := by
  rw [get_constant_kername]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, s0_constants, Std.HashMap.getElem?_empty]
  apply bind_ok visitMutual_orB
  apply bind_ok rfl
  simp only [s4, stDef, Std.HashMap.getElem?_insert_self]
  rfl

/-! ## `Prod.fst` and `Prod.snd` -/

/-- The locals of a projection's body: `α`, `β`, `self`, from the `k`-th local, under `p`. -/
def lsF (k : Nat) : List Local :=
  loc (k + 2) `self (prodC (xv k) (xv (k + 1))) :: loc (k + 1) `β (.sort (.succ uv)) ::
    loc k `α (.sort (.succ uu)) :: lsP

/-- `visitExpr` on `Prod.fst`'s value, `Prod` not registered: the projection registers it.
Reference: the `tLambda` and `tProj` cases of `erase` (`MR E/ErasureFunction.v:1003`, `:1020`). -/
theorem fstV_run {n : Nat} {L : LocalContext} :
    (visitExpr (m := PureM) (n + 9) (projVal 0)).runPure s4 ⟨L, lsP, none, cfg, dc⟩ pc ⟨11⟩ =
      .ok ((projRL 0 11, s5), ⟨14⟩) := by
  refine lam_run (by krfl) fun _ => lam_run (by krfl) fun _ => lam_run (by krfl) fun L' => ?_
  show (visitExpr (m := PureM) (n + 3) (.proj `Prod 0 (xv 13))).runPure s4
    ⟨L', lsF 11, none, cfg, dc⟩ pc ⟨14⟩ = _
  rw [visitExpr]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := s4) (ps' := ⟨14⟩) (by krfl) ?_
  change (visitProj (m := PureM) (n + 2) `Prod 0 (xv 13)).runPure _ _ _ _ = _
  rw [visitProj]
  apply bind_ok rfl
  apply bind_ok (register_Pr_new (by qpfact))
  apply bind_ok rfl
  refine bind_ok (a := .fvar (xf 13)) (st' := s5) (ps' := ⟨14⟩) (by krfl) ?_
  simp only [toArray_toSubarray]
  rfl

/-- `visitExpr` on `Prod.snd`'s value, `Prod` registered. Reference: as `fstV_run`. -/
theorem sndV_run {n : Nat} {L : LocalContext} :
    (visitExpr (m := PureM) (n + 9) (projVal 1)).runPure s6 ⟨L, lsP, none, cfg, dc⟩ pc ⟨14⟩ =
      .ok ((projRL 1 14, s6), ⟨17⟩) := by
  refine lam_run (by krfl) fun _ => lam_run (by krfl) fun _ => lam_run (by krfl) fun L' => ?_
  show (visitExpr (m := PureM) (n + 3) (.proj `Prod 1 (xv 16))).runPure s6
    ⟨L', lsF 14, none, cfg, dc⟩ pc ⟨17⟩ = _
  rw [visitExpr]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := s6) (ps' := ⟨17⟩) (by krfl) ?_
  change (visitProj (m := PureM) (n + 2) `Prod 1 (xv 16)).runPure _ _ _ _ = _
  rw [visitProj]
  apply bind_ok rfl
  apply bind_ok (register_found (iv := Prod_ind) (by qpfact))
  apply bind_ok rfl
  refine bind_ok (a := .fvar (xf 16)) (st' := s6) (ps' := ⟨17⟩) (by krfl) ?_
  simp only [toArray_toSubarray]
  rfl

/-- `visitMutual` on `Prod.fst`, resp. `Prod.snd`. Reference: as `visitMutual_orB`. -/
theorem visitMutual_fst {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)} :
    (visitMutual (m := PureM) (n + 10) `Prod.fst).runPure s4 ⟨L, lsP, F, cfg, dc⟩ pc ⟨11⟩ =
      .ok (((), s6), ⟨14⟩) := by
  rw [visitMutual]
  iterate 8 apply bind_ok rfl
  refine bind_ok (a := projRL 0 11) (st' := s5) (ps' := ⟨14⟩) ?_ ?_
  · rw [runPure_withReader]
    apply bind_ok rfl
    refine bind_ok (a := projVal 0) (st' := s4) (ps' := ⟨11⟩) rfl ?_
    exact fstV_run (n := n)
  rfl

theorem visitMutual_snd {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)} :
    (visitMutual (m := PureM) (n + 10) `Prod.snd).runPure s6 ⟨L, lsP, F, cfg, dc⟩ pc ⟨14⟩ =
      .ok (((), s7), ⟨17⟩) := by
  rw [visitMutual]
  iterate 8 apply bind_ok rfl
  refine bind_ok (a := projRL 1 14) (st' := s6) (ps' := ⟨17⟩) ?_ ?_
  · rw [runPure_withReader]
    apply bind_ok rfl
    refine bind_ok (a := projVal 1) (st' := s6) (ps' := ⟨14⟩) rfl ?_
    exact sndV_run (n := n)
  rfl

/-- `get_constant_kername` on `Prod.fst`, resp. `Prod.snd`, not yet erased. Reference:
`erase_global_deps` (`MR E/ErasureFunction.v:1602`). -/
theorem kername_fst {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)} :
    (get_constant_kername (m := PureM) (n + 11) `Prod.fst).runPure s4 ⟨L, lsP, F, cfg, dc⟩ pc ⟨11⟩ =
      .ok ((toKername `Prod.fst, s6), ⟨14⟩) := by
  rw [get_constant_kername]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, show s4.constants[`Prod.fst]? = none by qpfact]
  apply bind_ok visitMutual_fst
  apply bind_ok rfl
  simp only [s6, stDef, Std.HashMap.getElem?_insert_self]
  rfl

theorem kername_snd {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)} :
    (get_constant_kername (m := PureM) (n + 11) `Prod.snd).runPure s6 ⟨L, lsP, F, cfg, dc⟩ pc ⟨14⟩ =
      .ok ((toKername `Prod.snd, s7), ⟨17⟩) := by
  rw [get_constant_kername]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, show s6.constants[`Prod.snd]? = none by qpfact]
  apply bind_ok visitMutual_snd
  apply bind_ok rfl
  simp only [s7, stDef, Std.HashMap.getElem?_insert_self]
  rfl

/-- `visitExpr` on `p.1`, resp. `p.2`: the λ□ constant of the projection, erased on the way,
applied to □ for the two types. Reference: the `tConst` and `tApp` cases of `erase`
(`MR E/ErasureFunction.v:999`, `:1006`). -/
theorem fstA_run {n : Nat} {L : LocalContext} :
    (visitExpr (m := PureM) (n + 15) (fstB (xv 1))).runPure s4 ⟨L, lsP, none, cfg, dc⟩ pc ⟨11⟩ =
      .ok ((projAppL `Prod.fst (.fvar (xf 1)), s6), ⟨14⟩) := by
  rw [fstB, visitExpr, ← fstB]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := s4) (ps' := ⟨11⟩) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 13) _).runPure _ _ _ _ = _
  rw [visitConstApp, show (fstB (xv 1)).withApp = fun k => k (.const `Prod.fst [.zero, .zero])
    #[tB, tB, xv 1] by funext k; krfl]
  refine bind_ok (a := none) (st' := s4) (ps' := ⟨11⟩) (by krfl) ?_
  refine bind_ok (a := none) (st' := s4) (ps' := ⟨11⟩) (by krfl) ?_
  refine bind_ok (a := some (.defnInfo Prod_fst)) (st' := s4) (ps' := ⟨11⟩) (by krfl) ?_
  refine bind_ok (a := .const (toKername `Prod.fst)) (st' := s6) (ps' := ⟨14⟩) ?_ ?_
  · rw [visitConst]
    apply bind_ok rfl
    refine bind_ok kername_fst ?_
    rfl
  refine appArgs_cons (as := [tB, xv 1]) (r := .box) (st' := s6) (ps' := ⟨14⟩) (by krfl) ?_
  refine appArgs_cons (as := [xv 1]) (r := .box) (st' := s6) (ps' := ⟨14⟩) (by krfl) ?_
  refine appArgs_cons (as := []) (r := .fvar (xf 1)) (st' := s6) (ps' := ⟨14⟩) (by krfl) ?_
  exact appArgs_nil

theorem sndA_run {n : Nat} {L : LocalContext} :
    (visitExpr (m := PureM) (n + 15) (sndB (xv 1))).runPure s6 ⟨L, lsP, none, cfg, dc⟩ pc ⟨14⟩ =
      .ok ((projAppL `Prod.snd (.fvar (xf 1)), s7), ⟨17⟩) := by
  rw [sndB, visitExpr, ← sndB]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := s6) (ps' := ⟨14⟩) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 13) _).runPure _ _ _ _ = _
  rw [visitConstApp, show (sndB (xv 1)).withApp = fun k => k (.const `Prod.snd [.zero, .zero])
    #[tB, tB, xv 1] by funext k; krfl]
  refine bind_ok (a := none) (st' := s6) (ps' := ⟨14⟩) (by krfl) ?_
  refine bind_ok (a := none) (st' := s6) (ps' := ⟨14⟩) (by krfl) ?_
  refine bind_ok (a := some (.defnInfo Prod_snd)) (st' := s6) (ps' := ⟨14⟩) (by krfl) ?_
  refine bind_ok (a := .const (toKername `Prod.snd)) (st' := s7) (ps' := ⟨17⟩) ?_ ?_
  · rw [visitConst]
    apply bind_ok rfl
    refine bind_ok kername_snd ?_
    rfl
  refine appArgs_cons (as := [tB, xv 1]) (r := .box) (st' := s7) (ps' := ⟨17⟩) (by krfl) ?_
  refine appArgs_cons (as := [xv 1]) (r := .box) (st' := s7) (ps' := ⟨17⟩) (by krfl) ?_
  refine appArgs_cons (as := []) (r := .fvar (xf 1)) (st' := s7) (ps' := ⟨17⟩) (by krfl) ?_
  exact appArgs_nil

/-! ## The lifted function and `orU` -/

/-- The lifted function's body `orB p.1 p.2`, `p` the second local. -/
def lbE : Expr := orBC (fstB (xv 1)) (sndB (xv 1))

/-- `visitExpr` on `orB p.1 p.2`: `orB`, erased on the way with its matcher, applied to the
erased projections. Reference: the `tConst` and `tApp` cases of `erase`
(`MR E/ErasureFunction.v:999`, `:1006`). -/
theorem lb_run {n : Nat} {L : LocalContext} :
    (visitExpr (m := PureM) (n + 41) lbE).runPure s0 ⟨L, lsP, none, cfg, dc⟩ pc ⟨2⟩ =
      .ok ((lbRL, s7), ⟨17⟩) := by
  rw [lbE, orBC, visitExpr, ← orBC, ← lbE]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := s0) (ps' := ⟨2⟩) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 39) _).runPure _ _ _ _ = _
  rw [visitConstApp, show lbE.withApp = fun k => k (.const `orB []) #[fstB (xv 1), sndB (xv 1)] by
    funext k; krfl]
  refine bind_ok (a := none) (st' := s0) (ps' := ⟨2⟩) (by krfl) ?_
  refine bind_ok (a := none) (st' := s0) (ps' := ⟨2⟩) (by krfl) ?_
  refine bind_ok (a := some (.defnInfo orB_def)) (st' := s0) (ps' := ⟨2⟩) (by krfl) ?_
  refine bind_ok (a := .const (toKername `orB)) (st' := s4) (ps' := ⟨11⟩) ?_ ?_
  · rw [visitConst]
    apply bind_ok rfl
    refine bind_ok kername_orB ?_
    rfl
  refine appArgs_cons (as := [sndB (xv 1)]) (fstA_run (n := n + 22)) ?_
  refine appArgs_cons (as := []) (sndA_run (n := n + 22)) ?_
  exact appArgs_nil

/-- `visitExpr` on the lifted function `fun p => orB p.1 p.2`, from the counter's second
variable. Reference: the `tLambda` case of `erase` (`MR E/ErasureFunction.v:1003`). -/
theorem liftF_run {n : Nat} {L : LocalContext} :
    (visitExpr (m := PureM) (n + 43) liftF).runPure s0 ⟨L, lsA, none, cfg, dc⟩ pc ⟨1⟩ =
      .ok ((liftRL, s7), ⟨17⟩) :=
  lam_run (by krfl) fun _ => lb_run (n := n)

theorem withApp_orUVal {γ : Sort _} (k : Expr → Array Expr → γ) :
    orUVal.withApp k =
      k (.const `Quot.lift [l1, l1]) #[tP, .const `swapR [], tB, liftF, .const `orU._proof_1 []] := by
  krfl

/-- `visitExpr` on `orU`'s value `Quot.lift (fun p => orB p.1 p.2) orU._proof_1`:
`visitConstApp`'s `Quot.lift` branch on five arguments η-expands it with the counter's first
variable `a` and erases the function applied to `a`. Reference: DV-29, and the η-expansion
of `withAppEtaToMinArity` (DV-25). -/
theorem orUV_run {n : Nat} {L : LocalContext} :
    (visitExpr (m := PureM) (n + 46) orUVal).runPure s0 ⟨L, [], none, cfg, dc⟩ pc ⟨0⟩ =
      .ok ((orURL, s7), ⟨17⟩) := by
  rw [show orUVal = .app (mkAppN (.const `Quot.lift [l1, l1]) #[tP, .const `swapR [], tB, liftF])
      (.const `orU._proof_1 []) from rfl, visitExpr,
    ← show orUVal = .app (mkAppN (.const `Quot.lift [l1, l1]) #[tP, .const `swapR [], tB, liftF])
      (.const `orU._proof_1 []) from rfl]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := s0) (ps' := ⟨0⟩) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 44) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_orUVal]
  refine bind_ok (a := none) (st' := s0) (ps' := ⟨0⟩) (by krfl) ?_
  refine bind_ok (a := none) (st' := s0) (ps' := ⟨0⟩) (by krfl) ?_
  refine bind_ok (a := some (.quotInfo QuotLift_val)) (st' := s0) (ps' := ⟨0⟩) (by krfl) ?_
  change (withAppEtaToMinArity (m := PureM) (n + 43) _ 6 _).runPure _ _ _ _ = _
  rw [withAppEtaToMinArity]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := .forallE `a tQ tB .default) (st' := s0) (ps' := ⟨0⟩) (by krfl) ?_
  rw [withApp_orUVal, withAppEtaToMinArity.go, ite_eq_right (by decide)]
  refine bind_ok (a := .forallE `a tQ tB .default) (st' := s0) (ps' := ⟨0⟩) rfl ?_
  refine bind_ok (a := xf 0) (st' := s0) (ps' := ⟨1⟩) rfl ?_
  rw [runPure_withReader]
  refine bind_ok (a := .app liftRL (.fvar (xf 0))) (st' := s7) (ps' := ⟨17⟩) ?_ (by krfl)
  rw [withAppEtaToMinArity.go, ite_eq_left (by decide)]
  refine bind_ok (a := liftF) (st' := s0) (ps' := ⟨1⟩) rfl ?_
  refine bind_ok (a := liftRL) (st' := s7) (ps' := ⟨17⟩) liftF_run ?_
  change (visitAppArgs (m := PureM) (n + 43) liftRL [xv 0].toArray).runPure _ _ _ _ = _
  refine appArgs_cons (as := []) (r := .fvar (xf 0)) (st' := s7) (ps' := ⟨17⟩) (by krfl) ?_
  exact appArgs_nil

/-- `visitMutual` on `orU`. Reference: as `visitMutual_orB`. -/
theorem visitMutual_orU {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)} :
    (visitMutual (m := PureM) (n + 47) `orU).runPure s0 ⟨L, [], F, cfg, dc⟩ pc ⟨0⟩ =
      .ok (((), s8), ⟨17⟩) := by
  rw [visitMutual]
  iterate 8 apply bind_ok rfl
  refine bind_ok (a := orURL) (st' := s7) (ps' := ⟨17⟩) ?_ ?_
  · rw [runPure_withReader]
    apply bind_ok rfl
    refine bind_ok (a := orUVal) (st' := s0) (ps' := ⟨0⟩) rfl ?_
    exact orUV_run (n := n)
  rfl

/-- `get_constant_kername` on `orU`, not yet erased. Reference: `erase_global_deps`
(`MR E/ErasureFunction.v:1602`). -/
theorem kername_orU {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)} :
    (get_constant_kername (m := PureM) (n + 48) `orU).runPure s0 ⟨L, [], F, cfg, dc⟩ pc ⟨0⟩ =
      .ok ((toKername `orU, s8), ⟨17⟩) := by
  rw [get_constant_kername]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, s0_constants, Std.HashMap.getElem?_empty]
  apply bind_ok visitMutual_orU
  apply bind_ok rfl
  simp only [s8, stDef, Std.HashMap.getElem?_insert_self]
  rfl

/-! ## `useTF` -/

theorem withApp_pr {γ : Sort _} (k : Expr → Array Expr → γ) :
    (pairB cT cF).withApp k = k (.const `Prod.mk [.zero, .zero]) #[tB, tB, cT, cF] := by krfl

/-- `visitExpr` on the pair `Prod.mk B.t B.f`, `Prod` and `B` registered: the type arguments are
erased. Reference: the `tConstruct` case of `erase` (`MR E/ErasureFunction.v:1014`). -/
theorem pr_run {n : Nat} {L : LocalContext} :
    (visitExpr (m := PureM) (n + 11) (pairB cT cF)).runPure s8 ⟨L, [], none, cfg, dc⟩ pc ps =
      .ok ((pairL tL fL, s8), ps) := by
  have hB : s8.inductives[`B]? = some (iidB, masksB) := by qpfact
  rw [pairB, visitExpr, ← pairB]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := s8) (ps' := ps) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 9) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_pr]
  refine bind_ok (a := none) (st' := s8) (ps' := ps) (by krfl) ?_
  refine bind_ok (a := some 4) (st' := s8) (ps' := ps) (by krfl) ?_
  change (withAppEtaToMinArity (m := PureM) (n + 8) _ 4 _).runPure _ _ _ _ = _
  rw [withAppEtaToMinArity]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := tP) (st' := s8) (ps' := ps) (by krfl) ?_
  rw [withApp_pr, withAppEtaToMinArity.go]
  rw [visitConstructor]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok (register_found (iv := Prod_ind) (by qpfact))
  dsimp only
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  simp only
  apply bind_ok rfl
  simp only [toArray_toSubarray, show Prod_mk.numParams = 2 from rfl,
    show Prod_mk.numFields = 2 from rfl, show Prod_mk.cidx = 0 from rfl]
  rw [NVS.args_PP]
  refine (congrArg (fun x : EraseT PureM LBTerm => x.runPure s8 ⟨L, [], none, cfg, dc⟩ pc ps)
    (?_ : _ = visitAppArgs (m := PureM) (n + 7) mkL #[tB, tB, cT, cF])).trans ?_
  · krfl
  refine appArgs_cons (as := [tB, cT, cF]) (r := .box) (st' := s8) (ps' := ps) (by krfl) ?_
  refine appArgs_cons (as := [cT, cF]) (r := .box) (st' := s8) (ps' := ps) (by krfl) ?_
  refine appArgs_cons (as := [cF]) (cB_run (n := n) (.inr ⟨rfl, rfl⟩) (.inl rfl) hB) ?_
  refine appArgs_cons (as := []) (cB_run (n := n) (.inl ⟨rfl, rfl⟩) (.inl rfl) hB) ?_
  exact appArgs_nil

/-- The class `Quot.mk swapR (Prod.mk B.t B.f)`. -/
def qmE : Expr := mkAppN (.const `Quot.mk [l1]) #[tP, .const `swapR [], pairB cT cF]

theorem withApp_qmE {γ : Sort _} (k : Expr → Array Expr → γ) :
    qmE.withApp k = k (.const `Quot.mk [l1]) #[tP, .const `swapR [], pairB cT cF] := by krfl

/-- `visitExpr` on the class `Quot.mk swapR (Prod.mk B.t B.f)`: `visitConstApp`'s `Quot.mk` branch
erases it as its element. Reference: DV-29. -/
theorem qm_run {n : Nat} {L : LocalContext} :
    (visitExpr (m := PureM) (n + 14) qmE).runPure s8 ⟨L, [], none, cfg, dc⟩ pc ps =
      .ok ((pairL tL fL, s8), ps) := by
  rw [show qmE = .app (mkAppN (.const `Quot.mk [l1]) #[tP, .const `swapR []]) (pairB cT cF) from rfl,
    visitExpr,
    ← show qmE = .app (mkAppN (.const `Quot.mk [l1]) #[tP, .const `swapR []]) (pairB cT cF) from rfl]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := s8) (ps' := ps) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 12) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_qmE]
  refine bind_ok (a := none) (st' := s8) (ps' := ps) (by krfl) ?_
  refine bind_ok (a := none) (st' := s8) (ps' := ps) (by krfl) ?_
  refine bind_ok (a := some (.quotInfo QuotMk_val)) (st' := s8) (ps' := ps) (by krfl) ?_
  change (withAppEtaToMinArity (m := PureM) (n + 11) _ 3 _).runPure _ _ _ _ = _
  rw [withAppEtaToMinArity]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := tQ) (st' := s8) (ps' := ps) (by krfl) ?_
  rw [withApp_qmE, withAppEtaToMinArity.go]
  refine bind_ok (a := pairB cT cF) (st' := s8) (ps' := ps) rfl ?_
  refine bind_ok (a := pairL tL fL) (st' := s8) (ps' := ps) (pr_run (n := n)) ?_
  rw [visitAppArgs]
  rfl

/-- `visitExpr` on `useTF`'s value: the λ□ constant of `orU`, erased on the way with its
dependencies, applied to the erased class. Reference: the `tConst` and `tApp` cases of `erase`
(`MR E/ErasureFunction.v:999`, `:1006`). -/
theorem use_run {n : Nat} {L : LocalContext} :
    (visitExpr (m := PureM) (n + 52) (useVal cT cF)).runPure s0 ⟨L, [], none, cfg, dc⟩ pc ⟨0⟩ =
      .ok ((useL tL fL, s8), ⟨17⟩) := by
  rw [useVal, visitExpr, ← useVal]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := s0) (ps' := ⟨0⟩) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 50) _).runPure _ _ _ _ = _
  rw [visitConstApp, show (useVal cT cF).withApp = fun k => k (.const `orU []) #[qmE] by
    funext k; krfl]
  refine bind_ok (a := none) (st' := s0) (ps' := ⟨0⟩) (by krfl) ?_
  refine bind_ok (a := none) (st' := s0) (ps' := ⟨0⟩) (by krfl) ?_
  refine bind_ok (a := some (.defnInfo orU_def)) (st' := s0) (ps' := ⟨0⟩) (by krfl) ?_
  refine bind_ok (a := .const (toKername `orU)) (st' := s8) (ps' := ⟨17⟩) ?_ ?_
  · rw [visitConst]
    apply bind_ok rfl
    refine bind_ok kername_orU ?_
    rfl
  refine appArgs_cons (as := []) (qm_run (n := n + 34)) ?_
  exact appArgs_nil

/-- `visitMutual` on `useTF`. Reference: as `visitMutual_orB`. -/
theorem visitMutual_use {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)} :
    (visitMutual (m := PureM) (n + 53) `useTF).runPure s0 ⟨L, [], F, cfg, dc⟩ pc ⟨0⟩ =
      .ok (((), s9), ⟨17⟩) := by
  rw [visitMutual]
  iterate 8 apply bind_ok rfl
  refine bind_ok (a := useL tL fL) (st' := s8) (ps' := ⟨17⟩) ?_ ?_
  · rw [runPure_withReader]
    apply bind_ok rfl
    refine bind_ok (a := useVal cT cF) (st' := s0) (ps' := ⟨0⟩) rfl ?_
    exact use_run (n := n)
  rfl

/-- `get_constant_kername` on `useTF`, not yet erased. Reference: `erase_global_deps`
(`MR E/ErasureFunction.v:1602`). -/
theorem kername_use {n : Nat} {L : LocalContext} {F : Option (Std.HashMap Name FVarId)} :
    (get_constant_kername (m := PureM) (n + 54) `useTF).runPure s0 ⟨L, [], F, cfg, dc⟩ pc ⟨0⟩ =
      .ok ((toKername `useTF, s9), ⟨17⟩) := by
  rw [get_constant_kername]
  apply bind_ok rfl
  simp only [Std.HashMap.get?_eq_getElem?, s0_constants, Std.HashMap.getElem?_empty]
  apply bind_ok visitMutual_use
  apply bind_ok rfl
  simp only [s9, stDef, Std.HashMap.getElem?_insert_self]
  rfl

/-- `visitExpr` on `e = useTF`: its λ□ constant, erased on the way with its dependencies.
Reference: the `tConst` case of `erase` (`MR E/ErasureFunction.v:999`), with `erase_global_deps`
(`MR E/ErasureFunction.v:1602`). -/
theorem e_run {n : Nat} {L : LocalContext} :
    (visitExpr (m := PureM) (n + 58) e).runPure {} ⟨L, [], none, cfg, .anonymous⟩ pc ⟨0⟩ =
      .ok ((.const (toKername `useTF), s9), ⟨17⟩) := by
  rw [e, visitExpr]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := {}) (ps' := ⟨0⟩) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 56) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_const]
  refine bind_ok (a := none) (st' := {}) (ps' := ⟨0⟩) (by krfl) ?_
  refine bind_ok (a := none) (st' := {}) (ps' := ⟨0⟩) (by krfl) ?_
  refine bind_ok (a := some (.defnInfo useTF_def)) (st' := {}) (ps' := ⟨0⟩) (by krfl) ?_
  refine bind_ok (a := .const (toKername `useTF)) (st' := s9) (ps' := ⟨17⟩) ?_ ?_
  · rw [visitConst]
    apply bind_ok rfl
    refine bind_ok kername_use ?_
    rfl
  exact appArgs_nil

/-! ## The run on NV-QP -/

/-- The pure path on NV-QP's closure returns `p0` and `inl0`. Reference: `erase`
(`MR E/ErasureFunction.v:989`) and `erase_global_deps` (`MR E/ErasureFunction.v:1602`). -/
theorem hpure : erasePure view cfg D e = .ok (p0, inl0) := by
  rw [erasePure, show travFuel = (travFuel - 58) + 58 by decide]
  rw [show ((visitExpr (m := PureM) (travFuel - 58 + 58) e).runPure {} { «config» := cfg }
    ⟨D, view⟩ {}) = .ok ((.const (toKername `useTF), s9), ⟨17⟩) from e_run]
  krfl

/-- `#erase`'s entry point on NV-QP returns `p0` and `inl0`. Reference: the hypotheses
`erase … = t'` and `erase_global_deps … = Σ'` of `erase_correct`
(`MR E/ErasureFunctionProperties.v:657`). -/
theorem hrun : eraseEntry view cfg e = pure (p0, inl0) := by
  simp only [eraseEntry, route, hcollect, hpure]
end EraseProof.Test.NVQP
