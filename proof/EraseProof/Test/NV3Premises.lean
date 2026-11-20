import EraseProof.Statements
import EraseProof.Test.NV3Data
import EraseProof.Test.NVKit

/-!
# NV-3: the hypotheses of the final theorem

Each hypothesis of `erase_correct_statement` holds on the program of `Test/NV3Data.lean`, each
stated as the theorem of that name; `hev` goes through `SrcEval.recIota` (twice: the major `1`
and its induction hypothesis on `0`), `SrcEval.casesLitZero` and `SrcEval.casesLitSucc`.
`hfrag` and `hrun` are the shipping `collectDeps`/`eraseEntry` evaluated one traversal call at a
time (`Test/Run.lean`). The kernel checks all but two facts, each a premise checked by a `#guard`
(compiled evaluation, DV-40): the equation of the pure fold inside `hacc` (`hfold`), and con-leche's
inference of the five terms of `guardTerms` (`hg`), each with a λ minor premise. No con-leche run
needs ι or compares two distinct levels (the motive is constant).
-/

open Lean Erasure EraseProof EraseProof.Test EraseProof.Test.NV3

namespace EraseProof.Test.NV3

/-! ## con-leche's environment -/

def nmN : ConLeche.Name := Name.toCL `Nat

/-- con-leche's input for NV-3 (`DeclsOf? P`). -/
def full : List ConLeche.Declaration := (DeclsOf? P).getD []

def kRules : List ConLeche.RecRule :=
  [⟨Name.toCL `Nat.zero, 0, .plain, cl (recRhs (.bvar 1))⟩,
   ⟨Name.toCL `Nat.succ, 1, .plain, cl (Nat_rec.rules[1]!.rhs)⟩]

/-- NV-3's accepted environment, newest first (the fold's result, `#guard` below). -/
def envNV3 : ConLeche.Env :=
  ⟨[ .defnInfo (cv `Nat.casesOn [`u] casesOnTy) (cl casesOnVal) .abbrev
   , .recInfo (cv `Nat.rec [`u] recTy) 3 3 false kRules
   , .ctorInfo (cv `Nat.succ [] Succ_ctor.type) 0 1 nmN
   , .ctorInfo (cv `Nat.zero [] tN) 0 0 nmN
   , .indInfo (cv `Nat [] (.sort l1))
       { all := [nmN], ctors := [Name.toCL `Nat.zero, Name.toCL `Nat.succ], neverZero := true } ],
   []⟩

#guard match ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified ConLeche.checkFuel) []
    full with
  | .ok env => decide (env.consts = envNV3.consts) && decide (env.tables = envNV3.tables)
  | .error _ => false

/-! ## `hacc`, `hty`, `hclean`, `hview`, `hfrag`, `hnopre` -/

theorem decls : DeclsOf? P = some full := by krfl

theorem hacc (hfold : ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified ConLeche.checkFuel)
    [] full = .ok envNV3) : ConLecheAccepts P envNV3 :=
  ⟨full, decls, hfold, by krfl, by krfl⟩

/-- `Nat.rec` on the minor premises' values -/
def rec4 (zv : Expr) (m : Expr) : Expr := mkAppN (.const `Nat.rec [l1]) #[motN, zv, minS, m]

/-- The terms whose con-leche inference compares a λ minor premise with the binder it fills under a
`Π` whose body differs (`fun n ih => ih` against `(n : Nat) → motive n → motive (n + 1)`): con-leche's
binder congruence opens the bodies with the well-founded `instantiateList`, which the kernel does not
reduce (DV-40), so a `#guard` checks their inference by compiled evaluation and the theorems that
need it take it as the premise `hg`. -/
def guardTerms : List Expr := [e, z, cas 1 (lit 0), rec4 (lit 0) (lit 1), rec4 (lit 0) (lit 0)]

#guard guardTerms.all (inferOk envNV3 ConLeche.checkFuel)

variable (hg : guardTerms.all (inferOk envNV3 ConLeche.checkFuel) = true)
include hg in
theorem guard {t : Expr} (ht : t ∈ guardTerms) : inferOk envNV3 ConLeche.checkFuel t = true :=
  List.all_eq_true.mp hg t ht

include hg in
theorem hty : CLTyped envNV3 e := typed_of _ (guard hg (by simp [guardTerms]))

include hg in
theorem okG {t : Expr} (ht : t ∈ guardTerms) (hu : unmark t = t) : CLOk envNV3 t :=
  ok_clean (guard hg ht) hu

theorem hclean : NoMarkKeys e = true := by krfl

theorem hview : ViewAgrees view P := by
  intro ci h
  simp only [P, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> refine ⟨rfl, fun cfg pre hp => ?_⟩ <;>
    rw [preDef_none' (by krfl)] at hp <;> cases hp

theorem hfrag : collectDeps view cfg e = .ok D := by krfl

theorem hnopre : NoPreDefs view cfg D := by unfold NoPreDefs; decide

/-! ## `hrun`: the traversal, one call at a time -/

omit hg

def pc : PureCtx := ⟨D, view⟩

variable {st : ErasureState} {ps : PureState} {dc : Name}

def iidN : InductiveId := ⟨mutualBlockKername [`Nat], 0⟩
def masksN : InductiveArgMasks := [#[], #[.keep]]
def bodyN : OneInductiveBody :=
  { name := toString `Nat, propositional := false,
    ctors := [⟨toString `Nat.zero, 0⟩, ⟨toString `Nat.succ, 1⟩], projs := [] }

/-- The state after registering `Nat`. -/
def stN (st : ErasureState) : ErasureState :=
  { st with
    inductives := st.inductives.insert `Nat (iidN, masksN)
    gdecls := (mutualBlockKername [`Nat], .inductiveDecl ⟨.finite, 0, [bodyN]⟩) :: st.gdecls }

theorem stN_Nat : (stN st).inductives[`Nat]? = some (iidN, masksN) := by
  simp only [stN, Std.HashMap.getElem?_insert_self]

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

/-- The erasure of a Nat literal under `nat := .peano`: λ□'s constructor chain of `Nat`. -/
def natL : Nat → LBTerm
  | 0 => .construct iidN 0 []
  | k + 1 => .app (.construct iidN 1 []) (natL k)

theorem lit0_run {n : Nat} {L : LocalContext} :
    (visitExpr (m := PureM) (n + 4) (lit 0)).runPure (stN st) ⟨L, [], none, cfg, dc⟩ pc ps =
      .ok ((natL 0, stN st), ps) := by
  rw [lit, visitExpr]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := stN st) (ps' := ps) (by krfl) ?_
  change (visitLiteral (m := PureM) (n + 3) _).runPure _ _ _ _ = _
  rw [visitLiteral]
  apply bind_ok rfl
  change (visitConstructor (m := PureM) (n + 2) `Nat.zero #[]).runPure _ _ _ _ = _
  rw [visitConstructor]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok (register_found stN_Nat)
  simp only [toArray_toSubarray]
  krfl

theorem args_s (a : Expr) : #[a].extract 0 0 ++
    filter #[ConstructorArgRelevance.keep]
      (↑(#[a].toSubarray 0 (0 + 1)) : Array Expr) ++ #[a].extract (0 + 1) = #[a] := by
  apply Array.toList_inj.mp
  simp [filter, toArray_toSubarray]

theorem lit1_run {n : Nat} {L : LocalContext} :
    (visitExpr (m := PureM) (n + 9) (lit 1)).runPure (stN st) ⟨L, [], none, cfg, dc⟩ pc ps =
      .ok ((natL 1, stN st), ps) := by
  rw [lit, visitExpr]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := stN st) (ps' := ps) (by krfl) ?_
  change (visitLiteral (m := PureM) (n + 8) _).runPure _ _ _ _ = _
  rw [visitLiteral]
  apply bind_ok rfl
  simp only [show cfg.nat = .peano from rfl, show ¬ (1 > peanoMaxLiteral) by decide,
    Nat.add_one_ne_zero, ↓reduceIte, Nat.sub_self]
  change (visitConstructor (m := PureM) (n + 7) `Nat.succ #[.lit (.natVal 0)]).runPure _ _ _ _ = _
  rw [visitConstructor]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok (register_found stN_Nat)
  dsimp only
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  simp only
  apply bind_ok rfl
  simp only [toArray_toSubarray, show Succ_ctor.numParams = 0 from rfl,
    show Succ_ctor.numFields = 1 from rfl, show Succ_ctor.cidx = 1 from rfl]
  rw [args_s]
  refine (congrArg (fun x : EraseT PureM LBTerm => x.runPure (stN st) ⟨L, [], none, cfg, dc⟩ pc ps)
    (?_ : _ = visitAppArgs (m := PureM) (n + 6) (.construct iidN 1 []) #[lit 0])).trans ?_
  · krfl
  rw [visitAppArgs, ← Array.foldlM_toList]
  simp only [List.foldlM_cons, List.foldlM_nil]
  refine bind_ok (a := natL 1) (st' := stN st) (ps' := ps) ?_ ?_
  · apply bind_ok (lit0_run (n := n + 1))
    rfl
  rfl

/-! ### The `casesOn` spines -/

def ciN : CasesInfo :=
  { declName := `Nat.casesOn, indName := `Nat, arity := 4, discrPos := 1, motivePos := 0,
    altsRange := 2...4, altNumParams := #[.ctor `Nat.zero 0, .ctor `Nat.succ 1] }

def altsMap (a : Expr) : Std.HashMap Name (Nat × Expr) :=
  ((∅ : Std.HashMap Name (Nat × Expr)).insert `Nat.zero (0, a)).insert `Nat.succ (1, idN)

/-- The erasure of `cas k a`, `aL` that of `a`. -/
def casL (k : Nat) (aL : LBTerm) : LBTerm :=
  .case (iidN, 0) (natL k) [([], aL), ([binderNameOf `n], .bvar 0)]

theorem idN_alt {n j : Nat} {L : LocalContext} (hj : j = 0 ∨ j = 1) :
    (visitAlt (m := PureM) (n + 3) 1 #[.keep] [] idN).runPure (stN st) ⟨L, [], none, cfg, dc⟩ pc ⟨j⟩ =
      .ok ((([binderNameOf `n], .bvar 0), stN st), ⟨j + 1⟩) := by
  rcases hj with rfl | rfl <;> krfl

variable {a : Expr} {aL : LBTerm} {k i j : Nat} {L : LocalContext}

theorem casesOn_run {n : Nat} (hj : j = 0 ∨ j = 1)
    (ha : (visitAlt (m := PureM) (n + 3) 0 #[] [] a).runPure (stN st) ⟨L, [], none, cfg, dc⟩ pc ⟨i⟩ =
      .ok ((([], aL), stN st), ⟨j⟩)) :
    (visitCasesOn (m := PureM) (n + 4) Nat_ind (altsMap a) ∅ none (natL k)).runPure (stN st)
      ⟨L, [], none, cfg, dc⟩ pc ⟨i⟩ = .ok ((casL k aL, stN st), ⟨j + 1⟩) := by
  rw [visitCasesOn]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok (register_found stN_Nat)
  simp only [show Nat_ind.ctors = [`Nat.zero, `Nat.succ] from rfl, List.forIn_cons, List.forIn_nil,
    bind_assoc, Std.HashMap.getD_empty, altsMap, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]
  refine bind_ok (a := .yield (#[([], aL)], ([#[.keep]] : List ConstructorArgMask)))
    (st' := stN st) (ps' := ⟨j⟩) ?_ ?_
  · apply bind_ok ha
    rfl
  refine bind_ok (a := (#[([], aL), ([binderNameOf `n], .bvar 0)], ([] : List ConstructorArgMask)))
    (st' := stN st) (ps' := ⟨j + 1⟩) ?_ ?_
  · refine bind_ok (a := .yield (#[([], aL), ([binderNameOf `n], .bvar 0)], ([] : List ConstructorArgMask)))
      (st' := stN st) (ps' := ⟨j + 1⟩) ?_ ?_
    · apply bind_ok (idN_alt hj)
      rfl
    · rfl
  rfl

theorem cases_run {n : Nat} (hj : j = 0 ∨ j = 1)
    (hk : (visitExpr (m := PureM) (n + 4) (lit k)).runPure (stN st) ⟨L, [], none, cfg, dc⟩ pc ⟨i⟩ =
      .ok ((natL k, stN st), ⟨i⟩))
    (ha : (visitAlt (m := PureM) (n + 3) 0 #[] [] a).runPure (stN st) ⟨L, [], none, cfg, dc⟩ pc ⟨i⟩ =
      .ok ((([], aL), stN st), ⟨j⟩)) :
    (visitCases (m := PureM) (n + 5) ciN #[motN, lit k, a, idN]).runPure (stN st)
      ⟨L, [], none, cfg, dc⟩ pc ⟨i⟩ = .ok ((casL k aL, stN st), ⟨j + 1⟩) := by
  rw [visitCases]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := l1) (st' := stN st) (ps' := ⟨i⟩) (by krfl) ?_
  have hr : (ciN.altsRange.toList) = [2, 3] := by simp [ciN, Nat.toList_rco_eq_ite]
  simp only [← forIn'_eq_forIn, Std.Rco.forIn'_eq_forIn'_toList, hr, List.forIn'_cons,
    List.forIn'_nil]
  refine bind_ok (a := (altsMap a, none, ?sEnd)) (st' := stN st) (ps' := ⟨i⟩) ?_ ?_
  case sEnd => exact (ciN.altNumParams.toSubarray 2 2)
  · rfl
  apply bind_ok hk
  simp only [show Nat_ind.ctors = [`Nat.zero, `Nat.succ] from rfl, altsMap,
    Std.HashMap.contains_insert, Std.HashMap.contains_empty]
  apply bind_ok (casesOn_run hj ha)
  rw [show ciN.arity = (#[motN, lit k, a, idN] : Array Expr).size from rfl, forIn_toSubarray_size]
  rfl

theorem withApp_cas {γ : Sort _} (f : Expr → Array Expr → γ) :
    (cas k a).withApp f = f (.const `Nat.casesOn [l1]) #[motN, lit k, a, idN] := by
  simp only [cas, mkAppN, Array.foldl, Array.foldlM, Id.run]
  krfl

theorem cas_run {n : Nat} (hj : j = 0 ∨ j = 1)
    (hnot : (liftM (Backend.isErasable (m := PureM) L [] (cas k a)) : EraseT PureM Bool).runPure
      (stN st) ⟨L, [], none, cfg, dc⟩ pc ⟨i⟩ = .ok ((false, stN st), ⟨i⟩))
    (hty : (liftM (Backend.inferType (m := PureM) L [] (cas k a)) : EraseT PureM Expr).runPure
      (stN st) ⟨L, [], none, cfg, dc⟩ pc ⟨i⟩ = .ok ((.app motN (lit k), stN st), ⟨i⟩))
    (hk : (visitExpr (m := PureM) (n + 7) (lit k)).runPure (stN st) ⟨L, [], none, cfg, dc⟩ pc ⟨i⟩ =
      .ok ((natL k, stN st), ⟨i⟩))
    (ha : (visitAlt (m := PureM) (n + 6) 0 #[] [] a).runPure (stN st) ⟨L, [], none, cfg, dc⟩ pc ⟨i⟩ =
      .ok ((([], aL), stN st), ⟨j⟩)) :
    (visitExpr (m := PureM) (n + 11) (cas k a)).runPure (stN st) ⟨L, [], none, cfg, dc⟩ pc ⟨i⟩ =
      .ok ((casL k aL, stN st), ⟨j + 1⟩) := by
  have he : cas k a = .app (.app (.app (.app (.const `Nat.casesOn [l1]) motN) (lit k)) a) idN := rfl
  rw [he, visitExpr, ← he]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok hnot ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 9) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_cas]
  refine bind_ok (a := some ciN) (st' := stN st) (ps' := ⟨i⟩) (by krfl) ?_
  change (withAppEtaToMinArity (m := PureM) (n + 8) _ 4 _).runPure _ _ _ _ = _
  rw [withAppEtaToMinArity]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok hty ?_
  rw [withApp_cas, withAppEtaToMinArity.go, ite_eq_left (by simp)]
  exact cases_run (n := n + 3) hj hk ha

/-- the erasures of the two `casesOn` of `z` -/
def innerL : LBTerm := casL 1 (natL 0)
def zL : LBTerm := casL 0 innerL

theorem inner_run {n : Nat} :
    (visitExpr (m := PureM) (n + 13) (cas 1 (lit 0))).runPure (stN st) ⟨L, [], none, cfg, dc⟩ pc ⟨0⟩ =
      .ok ((innerL, stN st), ⟨1⟩) :=
  cas_run (n := n + 2) (.inl rfl) (by krfl) (by krfl) lit1_run (by
    rw [visitAlt]
    apply bind_ok rfl
    apply bind_ok rfl
    refine bind_ok (a := tN) (st' := stN st) (ps' := ⟨0⟩) (by krfl) ?_
    rw [lambdaOrIntroToArity]
    apply bind_ok lit0_run
    krfl)

theorem z_run {n : Nat} :
    (visitExpr (m := PureM) (n + 19) z).runPure (stN st) ⟨L, [], none, cfg, dc⟩ pc ⟨0⟩ =
      .ok ((zL, stN st), ⟨2⟩) :=
  cas_run (n := n + 8) (.inr rfl) (by krfl) (by krfl) lit0_run (by
    rw [visitAlt]
    apply bind_ok rfl
    apply bind_ok rfl
    refine bind_ok (a := .app motN (lit 1)) (st' := stN st) (ps' := ⟨0⟩) (by krfl) ?_
    rw [lambdaOrIntroToArity]
    apply bind_ok inner_run
    krfl)

/-! ### The recursor spine -/

def minSL : LBTerm := .lambda (binderNameOf `n) (.lambda (binderNameOf `ih) (.bvar 0))

theorem minS_run {n : Nat} :
    (visitExpr (m := PureM) (n + 8) minS).runPure st ⟨L, [], none, cfg, dc⟩ pc ⟨2⟩ =
      .ok ((minSL, st), ⟨4⟩) := by
  krfl

def minorsN : List RecMinor := [⟨`zero, [], []⟩, ⟨`succ, [`n], [⟨0, 0, []⟩]⟩]

theorem recShape_N : recShape Nat_rec.numParams Nat_rec.numMotives Nat_rec.type
    ([Zero_ctor, Succ_ctor].map (·.numFields)) = some ([[`t]], minorsN) := by krfl

def memberN : RecMember :=
  ⟨`Nat, [`t], iidN, [(0, ⟨`zero, [], []⟩, #[]), (1, ⟨`succ, [`n], [⟨0, 0, []⟩]⟩, #[.keep])]⟩

def fixL : LBTerm := recFix 2 0 false [memberN] 0

/-- The erasure of `e`: the minors let-bound around the fixpoint applied to the major. -/
def eL : LBTerm :=
  .letIn (binderNameOf `zero) zL (.letIn (binderNameOf `succ) minSL (.app fixL (natL 1)))

theorem e_app : e = .app (mkAppN (.const `Nat.rec [l1]) #[motN, z, minS]) (lit 1) := rfl

theorem withApp_e {γ : Sort _} (k : Expr → Array Expr → γ) :
    e.withApp k = k (.const `Nat.rec [l1]) #[motN, z, minS, lit 1] := by
  krfl

theorem e_run {n : Nat} (hN : st.inductives[`Nat]? = none) :
    (visitExpr (m := PureM) (n + 24) e).runPure st ⟨L, [], none, cfg, dc⟩ pc ⟨0⟩ =
      .ok ((eL, stN st), ⟨4⟩) := by
  rw [e_app, visitExpr, ← e_app]
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := false) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  rw [visitApp]
  change (visitConstApp (m := PureM) (n + 22) _).runPure _ _ _ _ = _
  rw [visitConstApp, withApp_e]
  refine bind_ok (a := none) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  refine bind_ok (a := none) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  refine bind_ok (a := some (.recInfo Nat_rec)) (st' := st) (ps' := ⟨0⟩) (by krfl) ?_
  change (visitRec (m := PureM) (n + 21) _ _).runPure _ _ _ _ = _
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
  refine bind_ok (a := .app motN (lit 1)) (st' := stN st) (ps' := ⟨0⟩) (by krfl) ?_
  rw [withApp_e, withAppEtaToMinArity.go]
  simp only [show (#[motN, z, minS, lit 1] : Array Expr).size = 4 from rfl, ge_iff_le, Nat.le_refl,
    ↓reduceIte]
  apply bind_ok rfl
  apply bind_ok rfl
  apply bind_ok rfl
  refine bind_ok (a := l1) (st' := stN st) (ps' := ⟨0⟩) (by krfl) ?_
  rw [show (#[motN, z, minS, lit 1].extract 1 (1 + 2)).toList = [z, minS] from rfl]
  simp only [List.mapM_cons, List.mapM_nil]
  refine bind_ok (a := [zL, minSL]) (st' := stN st) (ps' := ⟨4⟩) ?_ ?_
  · apply bind_ok (z_run (n := n + 1))
    refine bind_ok (a := [minSL]) (st' := stN st) (ps' := ⟨4⟩) ?_ ?_
    · apply bind_ok (minS_run (n := n + 12))
      rfl
    rfl
  rw [visitAppArgs, show (#[motN, z, minS, lit 1].extract (1 + 2) 4) = #[lit 1] from rfl,
    ← Array.foldlM_toList]
  simp only [List.foldlM_cons, List.foldlM_nil]
  refine bind_ok (a := .app fixL (natL 1)) (st' := stN st) (ps' := ⟨4⟩) ?_ ?_
  · refine bind_ok (a := .app fixL (natL 1)) (st' := stN st) (ps' := ⟨4⟩) ?_ ?_
    · apply bind_ok (lit1_run (n := n + 10))
      rfl
    rfl
  rw [visitAppArgs]
  rfl

/-- The program `#erase` emits for NV-3. -/
def p0 : Program :=
  .untyped [(mutualBlockKername [`Nat], .inductiveDecl ⟨.finite, 0, [bodyN]⟩)] (some eL)

theorem hpure : erasePure view cfg D e = .ok (p0, []) := by
  rw [erasePure, show travFuel = (travFuel - 24) + 24 by decide]
  rw [show ((visitExpr (m := PureM) (travFuel - 24 + 24) e).runPure {} { «config» := cfg }
    ⟨D, view⟩ {}) = .ok ((eL, stN {}), ⟨4⟩) from e_run Std.HashMap.getElem?_empty]
  rfl

theorem hrun : eraseEntry view cfg e = pure (p0, []) := by
  simp only [eraseEntry, route, hfrag, hpure]

/-! ## `hmark`: the oracle keeps every node the traversal visits; NV-3 has no mark -/

def fx (i : Nat) : FVarId := ⟨.num `_pure i⟩

theorem mark_lit0 {ls : List Local} (h : oracle D ls (lit 0) = .ok false) :
    MarkOf D cfg ls (lit 0) (lit 0) := MarkOf.litZero h rfl

theorem mark_lit1 : MarkOf D cfg [] (lit 1) (lit 1) :=
  MarkOf.litSucc (k := 0) (by krfl) rfl (by decide) (mark_lit0 (by krfl))

theorem mark_idN : MarkAlt D cfg [] 1 idN (.forallE `n tN tN .default) idN :=
  MarkAlt.lam (n := `n) (A := tN) (b := .bvar 0) (bi := .default) (y := `n) (D := tN) (C := tN)
    (bi' := .default) (x := fx 0) (bM := .fvar (fx 0)) (by krfl) (fresh_of (by krfl))
    (MarkAlt.done (MarkOf.fvar (by krfl)))

theorem mark_cas {k : Nat} {a Ta : Expr} (hk : MarkOf D cfg [] (lit k) (lit k))
    (ha : MarkOf D cfg [] a a) (ho : oracle D [] (cas k a) = .ok false)
    (hT : Pure.inferType ⟨D⟩ oracleFuel [] [] (cas k a) = .ok (.app motN (lit k)))
    (hl : Pure.typeLevel ⟨D⟩ oracleFuel [] (lit k) = .ok l1)
    (hTa : Pure.inferType ⟨D⟩ oracleFuel [] [] a = .ok Ta) :
    MarkOf D cfg [] (cas k a) (cas k a) := by
  refine MarkOf.special (c := `Nat.casesOn) (us := [l1]) (as := [motN, lit k, a, idN]) (ar := 4)
    ho (by krfl) hT (MarkEta.sat (by simp) ?_)
  refine MarkSat.cases (iv := Nat_ind) (cd := Nat_casesOn) (pre := [motN]) (d := lit k)
    (alts := [a, idN]) (âlts := [a, idN]) (extra := []) (êxtra := []) (by krfl) (by krfl)
    (by decide) rfl rfl hl (fun h => by cases h) hk rfl ?_ ?_ ?_ rfl (by simp)
  · intro i cn h
    rcases i with _ | _ | i <;> simp [Nat_ind] at h <;> subst h
    · exact ⟨_, (by krfl : findDecl D `Nat.zero = some (.ctorInfo Zero_ctor))⟩
    · exact ⟨_, (by krfl : findDecl D `Nat.succ = some (.ctorInfo Succ_ctor))⟩
  · intro i alt h
    rcases i with _ | _ | i <;> simp at h <;> subst h
    · exact ⟨_, hTa⟩
    · exact ⟨_, (by krfl : Pure.inferType ⟨D⟩ oracleFuel [] [] idN = .ok (.forallE `n tN tN .default))⟩
  · intro i cn cv alt âlt T h1 h2 h3 h4 h5
    rcases i with _ | _ | i <;> simp [Nat_ind] at h1 h3 h4 <;> subst h1 h3 h4
    · rw [(by krfl : findDecl D `Nat.zero = some (.ctorInfo Zero_ctor))] at h2; cases h2
      exact MarkAlt.done ha
    · rw [(by krfl : findDecl D `Nat.succ = some (.ctorInfo Succ_ctor))] at h2; cases h2
      rw [(by krfl : Pure.inferType ⟨D⟩ oracleFuel [] [] idN = .ok (.forallE `n tN tN .default))] at h5
      cases h5
      exact mark_idN

theorem mark_z : MarkOf D cfg [] z z :=
  mark_cas (mark_lit0 (by krfl))
    (mark_cas mark_lit1 (mark_lit0 (by krfl)) (by krfl) (by krfl) (by krfl) (Ta := tN) (by krfl))
    (by krfl) (by krfl) (by krfl) (Ta := .app motN (lit 1)) (by krfl)

theorem mark_minS : MarkOf D cfg [] minS minS :=
  mark_lam (x := fx 0) (by krfl) (fresh_of (by krfl)) (by krfl)
    (mark_lam (x := fx 1) (by krfl)
      (fresh_of (by krfl)) (by krfl)
      (MarkOf.fvar (by krfl)))

theorem hmark : MarkOf D cfg [] e e := by
  refine MarkOf.special (c := `Nat.rec) (us := [l1]) (as := [motN, z, minS, lit 1]) (ar := 4)
    (T := .app motN (lit 1)) (by krfl) (by krfl) (by krfl) (MarkEta.sat (by decide) ?_)
  refine MarkSat.recr (r := Nat_rec) (ivs := [Nat_ind]) (cvs := [Zero_ctor, Succ_ctor]) (ps := [])
    (ms := [motN]) (mins := [z, minS]) (minsM := [z, minS]) (is := []) (îs := []) (maj := lit 1)
    (majM := lit 1) (extra := []) (êxtra := []) (by krfl) (by krfl) (by krfl) (by krfl) (by krfl)
    (by krfl) rfl rfl rfl rfl ⟨l1, by krfl⟩ rfl ?_ rfl (by simp) mark_lit1 rfl (by simp)
  intro i x xM h1 h2
  rcases i with _ | _ | i <;> simp at h1 h2 <;> subst h1 h2
  · exact mark_z
  · exact mark_minS

/-! ## `hcert`: con-leche types `e` (`hg`); there is no mark, and the closure's one value is
`Nat.casesOn`'s, a recognized `casesOn`, whose value the traversal does not erase -/

include hg in
theorem hcert : ProgCert envNV3 D cfg e := by
  refine ⟨typedAt_of (guard hg (by simp [guardTerms])),
    by simp [MarksCert, e, z, cas, minS, motN, idN, lit, tN, mkAppN], ?_⟩
  intro ci hci he v hv
  simp only [D, List.mem_cons, List.not_mem_nil, or_false] at hci
  rcases hci with rfl | rfl | rfl | rfl | rfl <;> cases hv
  exact absurd he.2 (Option.isSome_iff_ne_none.1 (by krfl))

/-! ## `hev`: `e ⇓ 0`, through `recIota` (twice), `casesLitZero` and `casesLitSucc` -/

abbrev σD : EvalEnv := evalEnvOf view cfg D

theorem ev_lit0 : SrcEval envNV3 σD (lit 0) (lit 0) := SrcEval.lit (ok_clean (F := 100) (by krfl) rfl)
theorem ev_lit1 : SrcEval envNV3 σD (lit 1) (lit 1) := SrcEval.lit (ok_clean (F := 100) (by krfl) rfl)

theorem not_short {x : Expr} (h : ∀ c us, x.getAppFn ≠ .const c us) : ¬ ShortSpine σD x := by
  rintro ⟨c, us, ar, h1, -⟩
  exact h c us h1

/-- `(fun n => n) 0 ⇓ 0` -/
theorem ev_idN : SrcEval envNV3 σD (.app idN (lit 0)) (lit 0) :=
  SrcEval.beta (n := `n) (A := tN) (b := .bvar 0) (bi := .default) (not_short (by intro c us h; cases h))
    (SrcEval.atom trivial) ev_lit0 (ok_clean (F := 100) (by krfl) rfl) ev_lit0

/-- `(fun n ih => ih) 0 0 ⇓ 0` -/
theorem ev_minS : SrcEval envNV3 σD (mkAppN minS #[lit 0, lit 0]) (lit 0) :=
  SrcEval.beta (n := `ih) (A := tN) (b := .bvar 0) (bi := .default) (not_short (by intro c us h; cases h))
    (SrcEval.beta (n := `n) (A := tN) (b := .lam `ih tN (.bvar 0) .default) (bi := .default)
      (not_short (by intro c us h; cases h)) (SrcEval.atom trivial) ev_lit0
      (ok_clean (F := 100) (by krfl) rfl) (SrcEval.atom trivial))
    ev_lit0 (ok_clean (F := 100) (by krfl) rfl) ev_lit0

include hg in
theorem ev_inner : SrcEval envNV3 σD (cas 1 (lit 0)) (lit 0) :=
  SrcEval.casesLitSucc (c := `Nat.casesOn) (us := [l1]) (iv := Nat_ind) (k := 0)
    (as := [motN, lit 1, lit 0, idN]) (m := lit 1) (alt := idN) (by krfl) rfl rfl rfl ev_lit1
    (okG hg (t := cas 1 (lit 0)) (by simp [guardTerms]) (by krfl)) (iota_of (by krfl)) rfl ev_idN

include hg in
theorem ev_z : SrcEval envNV3 σD z (lit 0) :=
  SrcEval.casesLitZero (c := `Nat.casesOn) (us := [l1]) (iv := Nat_ind)
    (as := [motN, lit 0, cas 1 (lit 0), idN]) (m := lit 0) (alt := cas 1 (lit 0)) (by krfl) rfl rfl
    rfl ev_lit0 (okG hg (t := z) (by simp [guardTerms]) (by krfl)) (iota_of (by krfl)) rfl (ev_inner hg)

theorem find_succ : findDecl σD.decls `Nat.succ = some (.ctorInfo Succ_ctor) := by krfl
theorem find_zero : findDecl σD.decls `Nat.zero = some (.ctorInfo Zero_ctor) := by krfl

include hg in
/-- the induction hypothesis: `Nat.rec (fun _ => Nat) 0 (fun n ih => ih) 0 ⇓ 0` -/
theorem ev_rec0 : SrcEval envNV3 σD (rec4 (lit 0) (lit 0)) (lit 0) :=
  SrcEval.recIota (c := `Nat.rec) (us := [l1]) (rv := Nat_rec) (T := `Nat) (iv := Nat_ind)
    (cvs := [Zero_ctor, Succ_ctor]) (motives := [[`t]]) (minors := minorsN) (ps := []) (ms := [motN])
    (mins := [lit 0, minS]) (mvs := [lit 0, minS]) (maj := lit 0) (mj := lit 0) (k := 0) (fs := [])
    (mi := ⟨`zero, [], []⟩) (mk := lit 0) (rfs := []) (ihvs := []) (by krfl) rfl rfl (by krfl) rfl
    recShape_N (by decide) rfl rfl rfl rfl
    (by
      intro i m mv h1 h2
      rcases i with _ | _ | i <;> simp at h1 h2 <;> subst h1 h2
      · exact ev_lit0
      · exact SrcEval.atom trivial)
    ev_lit0 ⟨`Nat.zero, [], Zero_ctor, [], find_zero, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl
    (okG hg (t := rec4 (lit 0) (lit 0)) (by simp [guardTerms]) (by krfl)) (iota_of (by krfl)) rfl rfl (by simp)
    (ok_clean (F := 100) (by krfl) rfl) ev_lit0

include hg in
theorem hev : SrcEval envNV3 σD e (lit 0) :=
  SrcEval.recIota (c := `Nat.rec) (us := [l1]) (rv := Nat_rec) (T := `Nat) (iv := Nat_ind)
    (cvs := [Zero_ctor, Succ_ctor]) (motives := [[`t]]) (minors := minorsN) (ps := []) (ms := [motN])
    (mins := [z, minS]) (mvs := [lit 0, minS]) (maj := lit 1) (mj := lit 1) (k := 1) (fs := [lit 0])
    (mi := ⟨`succ, [`n], [⟨0, 0, []⟩]⟩) (mk := minS) (rfs := [lit 0]) (ihvs := [lit 0]) (by krfl) rfl
    rfl (by krfl) rfl recShape_N (by decide) rfl rfl rfl rfl
    (by
      intro i m mv h1 h2
      rcases i with _ | _ | i <;> simp at h1 h2 <;> subst h1 h2
      · exact ev_z hg
      · exact SrcEval.atom trivial)
    ev_lit1 ⟨`Nat.succ, [], Succ_ctor, [], find_succ, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl
    (okG hg (t := rec4 (lit 0) (lit 1)) (by simp [guardTerms]) (by krfl)) (iota_of (by krfl)) rfl rfl
    (by
      intro i f w h1 h2
      rcases i with _ | i <;> simp at h1 h2 <;> subst h1 h2
      exact ev_rec0 hg)
    (ok_clean (F := 100) (by krfl) rfl) ev_minS

end EraseProof.Test.NV3
