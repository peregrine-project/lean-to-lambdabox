import EraseProof.Core.StepsCases

/-!
# Steps of the shipping core's correctness: `casesOn` spines

The step of `visitExpr` on a spine whose head is a recognized `casesOn` constant
(`visitExpr_cases_step`): `visitConstApp` (`LeanToLambdaBox/Erasure.lean:958`) η-expands the spine
to the `casesOn`'s arity (`withAppEta_spec`, `MarkOf.special`, `MarkEta`) and erases the saturated
spine with `visitCases` (`:1092`), whose branches the marking follows (`MarkSat`,
`visitCases_sat`):
* a `casesOn` with as many universe parameters as its inductive gives a proof, and the spine is
  `□` (`casesSat_box`, `MarkSat.casesProp`, `Erases.box`);
* when the discriminant's sort may be zero and the inductive has one constructor, the discriminant
  is not visited (its mark is `reduced`) and the alternative is applied to `□` for each field
  (`casesSat_reduced`, `MarkSat.casesReduced`, `Erases.casesReduced`);
* otherwise the discriminant and the alternatives are erased into a λ□ `case`
  (`casesSat_case`, `MarkSat.cases`, `Erases.cases`, `visitCasesOn_spec`).
The extra arguments are erased one at a time (`visitAppArgs_spec`, `Erases.appS`).

Reference: the `tCase` case of `erases_erase` (`MR E/ErasureFunction.v:1228`), rule
`erases_tCase` (`MR E/Extract.v:109`); the reduction at erasure time is DV-25, the η-expansion
DV-23. Adapted from `ML-V Core/StepsCases.lean`, `ML-V Core/StepsCasesBox.lean:296-599` and
`ML-V Core/StepsCasesCase.lean:938-1216`, whose typing premises are replaced by the marking.
-/

open Lean Erasure

namespace EraseProof

namespace Steps

open RegisterInd OracleRen StateLemmas Decls

section
variable {pc : PureCtx}

/-- `getConst` on a constant of the declarations returns it, states unchanged. Copy of
`ML-V Core/StepsCasesBox.lean:238`. -/
theorem getConst_ok {n : Name} {ci : ConstantInfo} {tc : TravCtx} {st : ErasureState}
    {ps : PureState} (h : findConst pc.decls n = some ci) :
    (getConst (m := PureM) n).runPure st tc pc ps = .ok ((ci, st), ps) := by
  rw [getConst_eq, h]

/-- `getOrFail` on a value returns it, states unchanged. Copy of
`ML-V Core/StepsCasesBox.lean:247`. -/
theorem getOrFail_of {γ : Type} [Inhabited γ] {o : Option γ} {a : γ} {msg : String}
    {tc : TravCtx} {st : ErasureState} {ps : PureState} (h : o = some a) :
    (getOrFail (m := PureM) o msg).runPure st tc pc ps = .ok ((a, st), ps) := by
  subst h; rfl

end

/-- `List.foldl` of λ□ applications is `mkApps`. Copy of `ML-V Core/StepsCasesBox.lean:366`. -/
theorem foldl_app_mkApps (l : List LBTerm) : ∀ t : LBTerm, l.foldl .app t = mkApps t l := by
  induction l with
  | nil => intro t; rfl
  | cons a l ih => intro t; exact ih (.app t a)

/-- The alternatives `ctorAlts` gives: one `.ctor` per constructor, with its number of fields.
Copy of `ML-V Core/StepsCasesCase.lean:622`. -/
theorem ctorAlts_get {decls : List ConstantInfo} : ∀ {l : List Name} {alts : List CasesAltInfo},
    ctorAlts decls l = some alts → alts.length = l.length ∧ ∀ (i : Nat) (cn : Name), l[i]? = some cn →
      ∃ cv, findConst decls cn = some (.ctorInfo cv) ∧ alts[i]? = some (CasesAltInfo.ctor cn cv.numFields)
  | [], alts, h => by simp [ctorAlts] at h; subst h; simp
  | x :: l, alts, h => by
    unfold ctorAlts at h
    split at h
    · rename_i cv as hx hl
      cases h
      obtain ⟨h1, h2⟩ := ctorAlts_get hl
      refine ⟨by simp [h1], fun i cn hi => ?_⟩
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst hi
        exact ⟨cv, hx, rfl⟩
      | succ i => exact h2 i cn (by simpa using hi)
    · cases h

/-- A renamed spine `c.{us} (l₁ ++ l₂)` is the renamed spine of `l₁` applied to the renamed
`l₂`. -/
theorem renFV_spine_append (ρ : FVarId → FVarId) (c : Name) (us : List Level)
    (l₁ l₂ : List Expr) :
    renFV ρ (mkAppN (.const c us) (l₁ ++ l₂).toArray) =
      mkAppN (mkAppN (.const c us) (l₁.map (renFV ρ)).toArray) (l₂.map (renFV ρ)).toArray := by
  rw [renFV_mkAppN, List.map_append, mkAppN_toArray, mkAppN_toArray, mkAppN_toArray,
    List.foldl_append]
  rfl

/-- The positions of a renamed `casesOn` spine `pre ++ [d] ++ L ++ extra`: the discriminant, the
alternatives, and the extra arguments. -/
theorem spine_get (ρ : FVarId → FVarId) (pre L extra : List Expr) (d : Expr) :
    ((pre ++ [d] ++ L ++ extra).map (renFV ρ)).toArray[pre.length]? = some (renFV ρ d) ∧
      (∀ i < L.length, ((pre ++ [d] ++ L ++ extra).map (renFV ρ)).toArray[pre.length + 1 + i]? =
        L[i]?.map (renFV ρ)) ∧
      ((pre ++ [d] ++ L ++ extra).map (renFV ρ)).drop (pre.length + 1 + L.length) =
        extra.map (renFV ρ) := by
  refine ⟨?_, fun i hi => ?_, ?_⟩
  · simp
  · rw [List.getElem?_toArray, List.getElem?_map, List.append_assoc, List.append_assoc,
      List.getElem?_append_right (by omega), List.singleton_append,
      show pre.length + 1 + i - pre.length = i + 1 by omega, List.getElem?_cons_succ,
      List.getElem?_append_left hi]
  · have hl : ((pre ++ [d] ++ L).map (renFV ρ)).length = pre.length + 1 + L.length := by
      simp only [List.length_map, List.length_append, List.length_singleton]
    rw [List.map_append, ← hl, List.drop_left]

/-- The extra arguments of a `casesOn` spine as `Subarray`. Adapted from
`ML-V Core/StepsCasesBox.lean:556` and `ML-V Core/StepsCasesCase.lean:1167`. -/
theorem slice_drop {A : List Expr} {n : Nat} (hn : n ≤ A.length) :
    Std.Slice.toArray (A.toArray.toSubarray n) = (A.drop n).toArray ∧
      (A.toArray.toSubarray n).toList = A.drop n := by
  have h : (A.toArray.toSubarray n).toList = A.drop n := by
    rw [Subarray.toList_eq]
    simp only [Array.array_toSubarray, Array.toList_extract, List.extract_eq_drop_take]
    simp [Nat.min_eq_left hn]
    exact List.take_of_length_le (by simp)
  refine ⟨?_, h⟩
  rw [← Subarray.toArray_eq_sliceToArray, ← Subarray.toArray_toList, h]

section
variable {decls : List ConstantInfo} {view : EnvView} {cfg : ErasureConfig}

/-- The constructors of an inductive of the closure are distinct (`CoreEnvBase.ctorIdx`). -/
theorem ctors_inj (hG : CoreEnvBase view cfg decls) {T : Name} {iv : InductiveVal}
    (hiv : findDecl decls T = some (.inductInfo iv)) {i j : Nat} {cn : Name}
    (hi : iv.ctors[i]? = some cn) (hj : iv.ctors[j]? = some cn) : i = j := by
  obtain ⟨cv, hcv, rfl, -⟩ := hG.ctorIdx T iv hiv i cn hi
  obtain ⟨cv', hcv', hj', -⟩ := hG.ctorIdx T iv hiv j cn hj
  rw [hcv] at hcv'
  cases hcv'
  exact hj'

/-- A constructor of an inductive of the closure has the inductive's parameter count
(`CoreEnvBase.ctorIdx`). -/
theorem ctor_numParams (hG : CoreEnvBase view cfg decls) {T : Name} {iv : InductiveVal}
    (hiv : findDecl decls T = some (.inductInfo iv)) {cn : Name} (hcn : cn ∈ iv.ctors)
    {cv : ConstructorVal} (hcv : findDecl decls cn = some (.ctorInfo cv)) :
    cv.numParams = iv.numParams := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hcn
  obtain ⟨cv', hcv', -, hnp⟩ := hG.ctorIdx T iv hiv j cn hj
  rw [hcv] at hcv'
  cases hcv'
  exact hnp

/-- The `□` branch of `visitCases` (`LeanToLambdaBox/Erasure.lean:1100`): a recognized `casesOn`
with as many universe parameters as its inductive returns `□` without changing the states.
Adapted from `ML-V Core/StepsCasesBox.lean:300`. Reference: the proof case of `erases_tCase`
(`MR E/Extract.v:111`), by `erases_box` (`MR E/Extract.v:140`); justified by the mark
`MarkSat.casesProp`. -/
theorem casesSat_box {j : Nat} {c : Name} {ci : CasesInfo} (hci : casesInfo? decls c = some ci)
    {cd : DefinitionVal} {iv : InductiveVal} (hco : casesOnOf? decls c = some iv)
    (hd : findDecl decls c = some (.defnInfo cd))
    (hlp : cd.levelParams.length = iv.levelParams.length) {args : Array Expr}
    {st st' : ErasureState} {tc : TravCtx} {ps ps' : PureState} {r : LBTerm}
    (hrun : (visitCases (m := PureM) j ci args).runPure st tc ⟨decls, view⟩ ps =
      .ok ((r, st'), ps')) :
    r = .box ∧ st' = st ∧ ps' = ps := by
  obtain ⟨iv', cd', alts, hiv, hd', hdn, -⟩ := casesInfo?_facts hci
  have hiv' : iv' = iv := by simpa [casesOnOf?, hci, hiv] using hco
  subst hiv'
  rw [hd] at hd'
  cases hd'
  cases j with
  | zero => rw [visitCases] at hrun; cases hrun
  | succ j =>
  rw [visitCases, runPure_bind] at hrun
  obtain ⟨⟨⟨discr, st₁⟩, ps₁⟩, hdisc, hrun⟩ := ok_of_bind hrun
  obtain ⟨-, h1, h2⟩ := getOrFail_run hdisc
  subst st₁ ps₁
  dsimp only at hrun
  rw [runPure_bind, getConst_ok (pc := ⟨decls, view⟩) (show findConst decls _ = _ from hiv),
    ok_bind'] at hrun
  dsimp only at hrun
  rw [runPure_bind, hdn, getConst_ok (pc := ⟨decls, view⟩) (show findConst decls _ = _ from hd),
    ok_bind'] at hrun
  dsimp only at hrun
  simp only [show (cd.levelParams.length == iv'.levelParams.length) = true by simpa using hlp,
    ↓reduceIte] at hrun
  cases hrun
  exact ⟨rfl, rfl, rfl⟩

/-- The reduced branch of `visitCases` (`LeanToLambdaBox/Erasure.lean:1130`): on a saturated
renamed spine of a recognized `casesOn` with more universe parameters than its inductive, which
has one constructor `cn`, when the oracle's level of the discriminant's type may be zero, a
successful run erases the alternative and applies it to `□` for each field of `cn` and to the
erasures of the extra arguments, which erases the marking `MarkSat.casesReduced`
(`Erases.casesReduced`, the discriminant marked `reduced`; `Erases.appS` for the extra
arguments). Adapted from `ML-V Core/StepsCasesBox.lean:432`, whose `FieldsErasable` is the mark.
Reference: `eval_iota_sing` (`MR E/EWcbvEval.v:162`) at erasure time; DV-25. -/
theorem casesSat_reduced (hG : CoreEnv view cfg decls) {j : Nat}
    (ih : ∀ m ≤ j, ∀ e, ExprSpec view cfg decls m e) {c : Name} {us : List Level}
    {ci : CasesInfo} (hci : casesInfo? decls c = some ci) {iv : InductiveVal}
    {cd : DefinitionVal} {u : Level} {cn : Name} {cv : ConstructorVal} {d alt âlt : Expr}
    {pre extra êxtra : List Expr} {ρ : FVarId → FVarId} {S : FVarId → Prop} {ls : List Local}
    {Sc : Name → Prop} {st st' : ErasureState} {tc : TravCtx} {ps ps' : PureState} {r : LBTerm}
    (hco : casesOnOf? decls c = some iv) (hd : findDecl decls c = some (.defnInfo cd))
    (hlp : cd.levelParams.length ≠ iv.levelParams.length) (hpre : pre.length = casesMajor iv)
    (hu : Pure.typeLevel ⟨decls⟩ oracleFuel ls d = .ok u) (hz : u.isNeverZero = false)
    (hcn : iv.ctors = [cn]) (hcv : findDecl decls cn = some (.ctorInfo cv))
    (hidx : (indexFields cv.numParams cv.type).all (·.isNone) = true)
    (halt : MarkOf decls cfg ls alt âlt) (hlen : extra.length = êxtra.length)
    (hextra : ∀ (i : Nat) a â, extra[i]? = some a → êxtra[i]? = some â → MarkOf decls cfg ls a â)
    (hctx : CtxOK cfg tc) (hR : RenOK ρ S ls tc.locals ps.next) (hsc : ScopeOK decls Sc)
    (hargs : ∀ a ∈ pre ++ [d] ++ [alt] ++ extra, ArgOK S Sc cfg decls a)
    (hok : StateOK noCert (evalEnvOf view cfg decls) st)
    (hrun : (visitCases (m := PureM) (j + 1) ci
      ((pre ++ [d] ++ [alt] ++ extra).map (renFV ρ)).toArray).runPure st tc ⟨decls, view⟩ ps =
        .ok ((r, st'), ps')) :
    Erases noCert (evalEnvOf view cfg decls) []
        (renFV ρ (mkAppN (.const c us) (pre ++ [markReduced d] ++ [âlt] ++ êxtra).toArray)) r ∧
      closedn 0 r = true ∧ ErasesDeps noCert (evalEnvOf view cfg decls) st'.gdecls r ∧
      Grows (evalEnvOf view cfg decls) Sc st st' ps ps' := by
  obtain ⟨iv', cd', alts, hiv, hd', hdn, -, har, hdp, hca, hanp, hrange⟩ := casesInfo?_facts hci
  have hiv' : iv' = iv := by simpa [casesOnOf?, hci, hiv] using hco
  subst hiv'
  rw [hd] at hd'
  cases hd'
  have hcv' : findConst decls cn = some (.ctorInfo cv) := hcv
  have halts : alts = [.ctor cn cv.numFields] := by
    rw [hcn] at hca
    unfold ctorAlts at hca
    rw [hcv'] at hca
    simp only [ctorAlts] at hca
    cases hca
    rfl
  subst halts
  have har2 : ci.arity = casesMajor iv' + 1 + 1 := by rw [har, casesArity, hcn]; rfl
  obtain ⟨hgd, hgl, hgx⟩ := spine_get ρ pre [alt] extra d
  have hdS : FVarsIn S d := (hargs d (by simp)).1
  have hu' : Pure.typeLevel ⟨decls⟩ oracleFuel tc.locals (renFV ρ d) = .ok u := by
    rw [Pure.typeLevel_ren (cx := ⟨decls⟩) hG.closed hR.supp hR.ren _ d hdS, hu]
  have hidx' : (indexFields iv'.numParams cv.type).all Option.isNone = true := by
    rw [← ctor_numParams hG.toCoreEnvBase hiv (by rw [hcn]; exact List.mem_singleton_self _) hcv]
    exact hidx
  rw [visitCases, runPure_bind, getOrFail_of (by rw [hdp, ← hpre]; exact hgd), ok_bind'] at hrun
  dsimp only at hrun
  rw [runPure_bind, getConst_ok (pc := ⟨decls, view⟩) (show findConst decls _ = _ from hiv),
    ok_bind'] at hrun
  dsimp only at hrun
  rw [runPure_bind, hdn, getConst_ok (pc := ⟨decls, view⟩) (show findConst decls _ = _ from hd),
    ok_bind'] at hrun
  dsimp only at hrun
  simp only [show (cd.levelParams.length == iv'.levelParams.length) = false by simpa using hlp,
    Bool.false_eq_true, ↓reduceIte] at hrun
  rw [runPure_read_bind, runPure_read_bind, runPure_bind, runPure_liftM, typeLevel_run, hu'] at hrun
  dsimp only [Except.map] at hrun
  rw [ok_bind', ok_bind'] at hrun
  dsimp only at hrun
  rw [hz, hanp, hrange, runPure_bind, rco_forIn,
    Nat.toList_rco_eq_singleton (by rw [← har, har2])] at hrun
  have halt' : ((pre ++ [d] ++ [alt] ++ extra).map (renFV ρ)).toArray[casesMajor iv' + 1]? =
      some (renFV ρ alt) := by
    rw [← hpre, ← Nat.add_zero (pre.length + 1)]; exact hgl 0 (by simp)
  simp only [List.forIn_cons, List.forIn_nil,
    show Std.Stream.next? (Std.toStream #[CasesAltInfo.ctor cn cv.numFields]) =
      some (CasesAltInfo.ctor cn cv.numFields, (#[CasesAltInfo.ctor cn cv.numFields].toSubarray 1 1))
      from rfl, runPure_bind, getOrFail_of halt', ok_bind', runPure_pure,
    Bool.not_false, Bool.true_and] at hrun
  have hnc : iv'.numCtors = 1 := by rw [InductiveVal.numCtors, hcn]; rfl
  simp only [hcn, List.forIn_cons, List.forIn_nil, ↓reduceIte, hnc, beq_self_eq_true,
    List.getElem?_cons_zero, Std.HashMap.getElem?_empty] at hrun
  have hrun' : ((do
        let alt_nt ← visitExpr (m := PureM) j (renFV ρ alt)
        let branch ← pure (List.foldl LBTerm.app alt_nt (List.replicate cv.numFields LBTerm.box))
        visitAppArgs j branch (Std.Slice.toArray
          (((pre ++ [d] ++ [alt] ++ extra).map (renFV ρ)).toArray.toSubarray ci.arity))) :
        EraseT PureM LBTerm).runPure st tc ⟨decls, view⟩ ps = .ok ((r, st'), ps') := by
    by_cases hni : iv'.numIndices > 0
    · rw [ite_eq_left_of_eq_true _ _ (by simpa using hni), runPure_bind, runPure_bind,
        runPure_bind, getConst_ok (pc := ⟨decls, view⟩) hcv', ok_bind'] at hrun
      dsimp only at hrun
      simp only [hidx', ↓reduceIte, runPure_pure, ok_bind'] at hrun
      rw [runPure_bind, getOrFail_of rfl, ok_bind'] at hrun
      dsimp only at hrun
      simpa only [Std.HashMap.getElem?_insert_self, Std.HashMap.getElem?_empty] using hrun
    · rw [ite_eq_right_of_eq_false _ _ (by simpa using hni), runPure_bind, getOrFail_of rfl,
        ok_bind'] at hrun
      dsimp only at hrun
      simpa only [Std.HashMap.getElem?_insert_self] using hrun
  clear hrun
  -- the alternative
  rw [runPure_bind] at hrun'
  obtain ⟨⟨⟨alt', st₁⟩, ps₁⟩, halt_run, hrun'⟩ := ok_of_bind hrun'
  rw [runPure_bind, runPure_pure, ok_bind'] at hrun'
  dsimp only at hrun'
  obtain ⟨hfa, hoa, hna, hra⟩ := hargs alt (by simp)
  have ⟨hera, hca, hdepsa, hgra⟩ := ih j (Nat.le_refl _) alt hctx hR hfa hsc hoa hna hra hok halt
    halt_run
  cases j with
  | zero => rw [visitAppArgs] at hrun'; cases hrun'
  | succ i =>
  rw [(slice_drop (n := ci.arity) (by
      rw [har2, ← hpre]
      simp only [List.length_map, List.length_append, List.length_singleton]
      omega)).1, har2, ← hpre, show pre.length + 1 + 1 = pre.length + 1 + [alt].length
    from rfl, hgx] at hrun'
  have hF : Erases noCert (evalEnvOf view cfg decls) []
      (mkAppN (.const c us) ((pre ++ [markReduced d] ++ [âlt]).map (renFV ρ)).toArray)
      (List.foldl LBTerm.app alt' (List.replicate cv.numFields LBTerm.box)) := by
    have key := Erases.casesReduced (cert := noCert) (σ := evalEnvOf view cfg decls) (Γ := [])
      (d := renFV ρ d) (us := us) (pre := pre.map (renFV ρ)) (extra := []) (extra' := []) trivial
      hco hcn hcv hidx (by simp [hpre]) hera rfl (fun _ _ _ h => by simp at h)
    rw [foldl_app_mkApps]
    have hmr : renFV ρ (markReduced d) = markReduced (renFV ρ d) := rfl
    simpa [List.map_append, hmr] using key
  have ⟨her, hc0, hdeps, hgr⟩ := visitAppArgs_spec (as := extra) (âs := êxtra)
    (ih i (by omega)) hctx hsc (hR.mono hgra.next)
    (fun a ha => hargs a (by simp [ha])) hlen hextra hgra.inv hF
    (by
      rw [foldl_app_mkApps]
      exact RecLam.closedn_mkApps.2 ⟨hca, fun a ha => by rw [List.eq_of_mem_replicate ha]; rfl⟩)
    (by
      rw [foldl_app_mkApps]
      exact ErasesDeps.mkApps_iff.2 ⟨hdepsa, fun a ha => by
        rw [List.eq_of_mem_replicate ha]; exact .box⟩)
    hrun'
  refine ⟨?_, hc0, hdeps, hgra.trans hgr⟩
  rw [renFV_spine_append]
  exact her

/-- The `case` branch of `visitCases` (`LeanToLambdaBox/Erasure.lean:1144`): on a saturated
renamed spine of a recognized `casesOn` with more universe parameters than its inductive, when the
oracle's level of the discriminant's type is never zero or the inductive does not have exactly one
constructor, a successful run erases the discriminant, the alternatives under their fields'
binders into a λ□ `case` (`visitCasesOn_spec`), and the extra arguments, which erases the marking
`MarkSat.cases` (`Erases.cases`, `Erases.appS`). The alternatives are collected by constructor
name, so the constructors are distinct (`ctors_inj`). Adapted from
`ML-V Core/StepsCasesCase.lean:938`, whose semantic side conditions are the marking's. Reference:
the `tCase` case of `erases_erase` (`MR E/ErasureFunction.v:1228`), rule `erases_tCase`
(`MR E/Extract.v:109`). -/
theorem casesSat_case (hG : CoreEnv view cfg decls) {j : Nat}
    (ih : ∀ m ≤ j, ∀ e, ExprSpec view cfg decls m e) {c : Name} {us : List Level}
    {ci : CasesInfo} (hci : casesInfo? decls c = some ci)
    (hnm : cfg.nat = .machine → c ≠ ``Nat.casesOn ∧ c ≠ ``Int.casesOn) {iv : InductiveVal}
    {cd : DefinitionVal} {u : Level} {d dM : Expr} {pre alts âlts extra êxtra : List Expr}
    {ρ : FVarId → FVarId} {S : FVarId → Prop} {ls : List Local} {Sc : Name → Prop}
    {st st' : ErasureState} {tc : TravCtx} {ps ps' : PureState} {r : LBTerm}
    (hco : casesOnOf? decls c = some iv) (hd : findDecl decls c = some (.defnInfo cd))
    (hlp : cd.levelParams.length ≠ iv.levelParams.length) (hpre : pre.length = casesMajor iv)
    (hac : alts.length = iv.ctors.length)
    (hu : Pure.typeLevel ⟨decls⟩ oracleFuel ls d = .ok u)
    (hC : u.isNeverZero = false → iv.ctors.length ≠ 1 ∧ ∀ cn ∈ iv.ctors, ∀ cv,
      findDecl decls cn = some (.ctorInfo cv) → (indexFields cv.numParams cv.type).all (·.isNone) = true)
    (hdM : MarkOf decls cfg ls d dM) (hlen : alts.length = âlts.length)
    (htys : ∀ (i : Nat) alt, alts[i]? = some alt →
      ∃ T, Pure.inferType ⟨decls⟩ oracleFuel ls [] alt = .ok T)
    (halts : ∀ (i : Nat) cn cv alt âlt T, iv.ctors[i]? = some cn →
      findDecl decls cn = some (.ctorInfo cv) → alts[i]? = some alt → âlts[i]? = some âlt →
      Pure.inferType ⟨decls⟩ oracleFuel ls [] alt = .ok T → MarkAlt decls cfg ls cv.numFields alt T âlt)
    (hlen' : extra.length = êxtra.length)
    (hextra : ∀ (i : Nat) a â, extra[i]? = some a → êxtra[i]? = some â → MarkOf decls cfg ls a â)
    (hctx : CtxOK cfg tc) (hR : RenOK ρ S ls tc.locals ps.next) (hsc : ScopeOK decls Sc)
    (hargs : ∀ a ∈ pre ++ [d] ++ alts ++ extra, ArgOK S Sc cfg decls a)
    (hok : StateOK noCert (evalEnvOf view cfg decls) st)
    (hrun : (visitCases (m := PureM) (j + 1) ci
      ((pre ++ [d] ++ alts ++ extra).map (renFV ρ)).toArray).runPure st tc ⟨decls, view⟩ ps =
        .ok ((r, st'), ps')) :
    Erases noCert (evalEnvOf view cfg decls) []
        (renFV ρ (mkAppN (.const c us) (pre ++ [dM] ++ âlts ++ êxtra).toArray)) r ∧
      closedn 0 r = true ∧ ErasesDeps noCert (evalEnvOf view cfg decls) st'.gdecls r ∧
      Grows (evalEnvOf view cfg decls) Sc st st' ps ps' := by
  obtain ⟨iv', cd', calts, hiv, hd', hdn, hcname, har, hdp, hca, hanp, hrange⟩ :=
    casesInfo?_facts hci
  have hiv' : iv' = iv := by simpa [casesOnOf?, hci, hiv] using hco
  subst hiv'
  rw [hd] at hd'
  cases hd'
  obtain ⟨hlena, haltsg⟩ := ctorAlts_get hca
  obtain ⟨hgd, hgl, hgx⟩ := spine_get ρ pre alts extra d
  generalize hA : (pre ++ [d] ++ alts ++ extra).map (renFV ρ) = A at hrun hgd hgl hgx
  have hAlen : A.length = casesArity iv' + extra.length := by
    rw [← hA]; simp [casesArity, hpre, hac]; omega
  have hdS : FVarsIn S d := (hargs d (by simp)).1
  have hu' : Pure.typeLevel ⟨decls⟩ oracleFuel tc.locals (renFV ρ d) = .ok u := by
    rw [Pure.typeLevel_ren (cx := ⟨decls⟩) hG.closed hR.supp hR.ren _ d hdS, hu]
  have hname : iv'.name = ci.indName := (findDecl_eq_some hiv).2
  have hnm' : cfg.nat = .machine → iv'.name ≠ ``Nat ∧ iv'.name ≠ ``Int := fun hm' =>
    ⟨fun h => (hnm hm').1 (by rw [hcname, ← hname, h]),
      fun h => (hnm hm').2 (by rw [hcname, ← hname, h])⟩
  have hsat : ci.arity ≤ A.length := by rw [hAlen, har]; omega
  rw [visitCases, runPure_bind, getOrFail_of (by rw [hdp, ← hpre]; exact hgd), ok_bind'] at hrun
  dsimp only at hrun
  rw [runPure_bind, getConst_ok (pc := ⟨decls, view⟩) (show findConst decls _ = _ from hiv),
    ok_bind'] at hrun
  dsimp only at hrun
  rw [runPure_bind, hdn, getConst_ok (pc := ⟨decls, view⟩) (show findConst decls _ = _ from hd),
    ok_bind'] at hrun
  dsimp only at hrun
  simp only [show (cd.levelParams.length == iv'.levelParams.length) = false by simpa using hlp,
    Bool.false_eq_true, ↓reduceIte] at hrun
  rw [runPure_read_bind, runPure_read_bind, runPure_bind, runPure_liftM, typeLevel_run, hu'] at hrun
  dsimp only [Except.map] at hrun
  rw [ok_bind', ok_bind'] at hrun
  dsimp only at hrun
  -- the alternatives, by constructor name
  rw [hanp, hrange, runPure_bind, rco_forIn] at hrun
  obtain ⟨⟨⟨⟨mp, ca, s₀⟩, st₁⟩, ps₁⟩, hloop, hrun⟩ := ok_of_bind hrun
  have hLlen : (casesMajor iv' + 1...casesArity iv').toList.length = calts.length := by
    rw [Nat.length_toList_rco, hlena]; simp [casesArity]
  have hI := forIn_inv (tc := tc) (pc := ⟨decls, view⟩)
    (L := (casesMajor iv' + 1...casesArity iv').toList)
    (fun pl (b : Std.HashMap Name (Nat × Expr) × Option (Nat × Expr) × Subarray CasesAltInfo)
        st₂ ps₂ => st₂ = st ∧ ps₂ = ps ∧ b.2.1 = none ∧ b.2.2.array = calts.toArray ∧
      b.2.2.start = pl.length ∧ b.2.2.stop = calts.length ∧
      ∀ i < pl.length, ∀ cn, iv'.ctors[i]? = some cn → ∃ cv a,
        findConst decls cn = some (.ctorInfo cv) ∧ A[casesMajor iv' + 1 + i]? = some a ∧
        b.1[cn]? = some (cv.numFields, a)) _ ?_ _ [] _ st ps _ _ _ rfl
    ⟨rfl, rfl, rfl, by simp [Std.toStream], by simp [Std.toStream], by simp [Std.toStream],
      fun i hi => by simp at hi⟩ hloop
  rotate_left
  · intro pl i rest ⟨mp, ca, s⟩ st₂ ps₂ res st₃ ps₃ hL ⟨hst, hps, hca', harr, hstart, hstop, hmap⟩ hb
    dsimp only at hst hps hca' harr hstart hstop hmap hb
    subst hst hps
    have hk : pl.length < calts.length := by
      rw [← hLlen, ← hL]; simp
    have hi : i = casesMajor iv' + 1 + pl.length := by
      have h1 : (casesMajor iv' + 1...casesArity iv').toList[pl.length]? = some i := by
        rw [← hL]; simp
      rw [Nat.getElem?_toList_rco] at h1
      split at h1
      · cases h1; rfl
      · cases h1
    subst hi
    obtain ⟨cn, hcn⟩ : ∃ cn, iv'.ctors[pl.length]? = some cn :=
      ⟨_, List.getElem?_eq_getElem (by rw [← hlena]; exact hk)⟩
    obtain ⟨cv, hcv, hacn⟩ := haltsg _ _ hcn
    have hlt : s.start < s.stop := by rw [hstart, hstop]; exact hk
    unfold Std.Stream.next? Std.instStreamSubarray at hb
    dsimp only at hb
    rw [dite_eq_left_of_eq_true (eq_true hlt)] at hb
    have hsa : s.array[s.start]'(Nat.lt_of_lt_of_le hlt s.stop_le_array_size) =
        CasesAltInfo.ctor cn cv.numFields := by
      have := List.getElem?_eq_some_iff.1 hacn
      simp only [harr, hstart, List.getElem_toArray]
      exact this.2
    simp only [hsa] at hb
    have hbd : casesMajor iv' + 1 + pl.length < A.length := by
      rw [hAlen]; simp only [casesArity]; rw [hlena] at hk; omega
    have has : A.toArray[casesMajor iv' + 1 + pl.length]? =
        some (A[casesMajor iv' + 1 + pl.length]'hbd) := by
      simp
    rw [runPure_bind, getOrFail_of has, ok_bind'] at hb
    cases hb
    refine ⟨_, rfl, rfl, rfl, hca', harr,
      by simp only [List.length_append, List.length_singleton, ← hstart]; rfl, hstop,
      fun i' hi' cn' hcn' => ?_⟩
    simp only [List.length_append, List.length_singleton] at hi'
    rw [Std.HashMap.getElem?_insert]
    rcases Nat.lt_or_ge i' pl.length with hlt' | hge
    · have hne : (cn == cn') = false := by
        rcases Bool.eq_false_or_eq_true (cn == cn') with h' | h'
        · have e := beq_iff_eq.mp h'
          subst e
          have := ctors_inj hG.toCoreEnvBase hiv hcn hcn'
          omega
        · exact h'
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      exact hmap i' hlt' cn' hcn'
    · have : i' = pl.length := by omega
      subst this
      rw [hcn] at hcn'
      cases hcn'
      exact ⟨cv, _, hcv, List.getElem?_eq_getElem hbd, by simp⟩
  obtain ⟨hst₁, hps₁, hca₁, -, -, -, hmap⟩ := hI
  dsimp only at hst₁ hps₁ hca₁ hmap hrun
  rw [hst₁, hps₁, hca₁] at hrun
  -- no index is substituted
  have hctorc : ∀ cn ∈ iv'.ctors, ∃ cv, findConst decls cn = some (.ctorInfo cv) := by
    intro cn hcn
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hcn
    obtain ⟨cv, hcv, -⟩ := haltsg _ _ hi
    exact ⟨cv, hcv⟩
  by_cases hni : (!u.isNeverZero && decide (iv'.numIndices > 0)) = true
  all_goals first
    | (have hz : u.isNeverZero = false := by
         cases h : u.isNeverZero
         · rfl
         · rw [h] at hni; simp at hni
       rw [ite_eq_left_of_eq_true _ _ (eq_true hni), runPure_bind] at hrun
       obtain ⟨⟨⟨idx, st₂⟩, ps₂⟩, hloop₂, hrun⟩ := ok_of_bind hrun
       obtain ⟨rfl, hs₂, hp₂⟩ := forIn_inv (tc := tc) (pc := ⟨decls, view⟩) (L := iv'.ctors)
         (fun _ (b : Std.HashMap Name (List (Option Expr))) st₂ ps₂ => b = ∅ ∧ st₂ = st ∧ ps₂ = ps)
         _ (fun pl cn rest b st₂ ps₂ res st₃ ps₃ hL ⟨hb, hs, hp⟩ hrb => by
           subst hb hs hp
           have hcn : cn ∈ iv'.ctors := by rw [← hL]; simp
           obtain ⟨cv, hcv⟩ := hctorc cn hcn
           rw [runPure_bind, getConst_ok (pc := ⟨decls, view⟩) hcv, ok_bind'] at hrb
           dsimp only at hrb
           have hcv' : findDecl decls cn = some (.ctorInfo cv) := hcv
           rw [ite_eq_left_of_eq_true _ _ (eq_true (by
             rw [← ctor_numParams hG.toCoreEnvBase hiv hcn hcv']; exact (hC hz).2 cn hcn cv hcv'))] at hrb
           cases hrb
           exact ⟨_, rfl, rfl, rfl, rfl⟩) _ [] ∅ st ps _ _ _ rfl ⟨rfl, rfl, rfl⟩ hloop₂
       rw [hs₂, hp₂] at hrun)
    | rw [ite_eq_right_of_eq_false _ _ (eq_false hni)] at hrun
  all_goals
  dsimp only at hrun
  have hc2 : (!u.isNeverZero && iv'.numCtors == 1) = false := by
    rw [InductiveVal.numCtors]
    cases hz : u.isNeverZero
    · simp [(hC hz).1]
    · rfl
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by rw [hc2]; decide)), runPure_bind] at hrun
  obtain ⟨⟨⟨dnt, st₂⟩, ps₂⟩, hdrun, hrun⟩ := ok_of_bind hrun
  have hall : (iv'.ctors.all fun x => mp.contains x) = true := by
    rw [List.all_eq_true]
    intro cn hcn
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hcn
    obtain ⟨cv, a, -, -, hma⟩ :=
      hmap i (by rw [hLlen, hlena]; exact (List.getElem?_eq_some_iff.1 hi).1) cn hi
    simp [Std.HashMap.contains_iff_mem, Std.HashMap.mem_iff_isSome_getElem?, hma]
  rw [ite_eq_left_of_eq_true _ _ (eq_true hall), runPure_bind] at hrun
  obtain ⟨⟨⟨ret, st₃⟩, ps₃⟩, hcrun, hrun⟩ := ok_of_bind hrun
  dsimp only at hcrun hrun
  cases j with
  | zero => rw [visitExpr] at hdrun; cases hdrun
  | succ f =>
  -- the discriminant
  obtain ⟨hfd, hod, hnd, hrd⟩ := hargs d (by simp)
  have ⟨herd, hcd, hdepd, hgrd⟩ := ih (f + 1) (Nat.le_refl _) d hctx hR hfd hsc hod hnd hrd hok
    hdM hdrun
  -- the alternatives and the `case`
  obtain ⟨iid, brs, hid, rfl, hlenb, hEb, hcC, hdepsC, hgrC⟩ := visitCasesOn_spec
    (alts := alts) (âlts := âlts) hG (fun j' hj' => ih j' (by omega)) (by rw [hname]; exact hiv)
    hnm' (fun i cn hcn => by
      have hil : i < iv'.ctors.length := (List.getElem?_eq_some_iff.1 hcn).1
      obtain ⟨cv, a, hcv, ha, hma⟩ := hmap i (by rw [hLlen, hlena]; exact hil) cn hcn
      obtain ⟨alt, halt⟩ : ∃ alt, alts[i]? = some alt :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨âlt, hâlt⟩ : ∃ âlt, âlts[i]? = some âlt :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨T, hT⟩ := htys i alt halt
      have hga := hgl i (by omega)
      rw [List.getElem?_toArray, halt, Option.map_some] at hga
      rw [← hpre, hga] at ha
      cases ha
      exact ⟨cv, alt, âlt, T, hcv, halt, hâlt, hma, hT, halts i cn cv alt âlt T hcn hcv halt hâlt hT⟩)
    (fun alt halt => hargs alt (by simp [halt])) hctx hsc (hR.mono hgrd.next) hgrd.inv hdepd hcd
    hcrun
  -- the extra arguments
  have hAr : ci.arity = pre.length + 1 + alts.length := by
    rw [har, casesArity, hpre, hac]
  rw [subarray_forIn, (slice_drop hsat).2, hAr, hgx, runPure_bind] at hrun
  obtain ⟨⟨⟨ret', st₄⟩, ps₄⟩, hext, hrun⟩ := ok_of_bind hrun
  cases hrun
  rw [forIn_app_eq] at hext
  have hF : Erases noCert (evalEnvOf view cfg decls) []
      (mkAppN (.const c us) ((pre ++ [dM] ++ âlts).map (renFV ρ)).toArray)
      (.case (iid, iv'.numParams) dnt brs) := by
    have key := Erases.cases (cert := noCert) (σ := evalEnvOf view cfg decls) (Γ := []) (us := us)
      (pre := pre.map (renFV ρ)) (alts := âlts.map (renFV ρ)) (extra := []) (extra' := []) hco hid
      (by simp [hpre]) (by rw [List.length_map, ← hlen, hac]) herd
      (by simp only [List.length_map]; rw [hlenb, ← hac, hlen])
      (fun i cn hcn => by
        obtain ⟨cv, hcv, -⟩ := haltsg i cn hcn
        simp [ctorFields, evalEnvOf, show findDecl decls cn = _ from hcv])
      (fun i cn alt br k hi ha hb hk => by
        rw [List.getElem?_map] at ha
        obtain ⟨âlt, hâlt, rfl⟩ := Option.map_eq_some_iff.1 ha
        exact hEb i cn âlt br k hi hâlt hb hk)
      rfl (fun _ _ _ h => by simp at h)
    simpa [List.map_append, mkApps] using key
  have ⟨her, hc0, hdeps, hgrE⟩ := visitAppArgs_spec (as := extra) (âs := êxtra)
    (ih (f + 1) (Nat.le_refl _)) hctx hsc (hR.mono (Nat.le_trans hgrd.next hgrC.next))
    (fun a ha => hargs a (by simp [ha])) hlen' hextra hgrC.inv hF hcC hdepsC hext
  refine ⟨?_, hc0, hdeps, hgrd.trans (hgrC.trans hgrE)⟩
  rw [renFV_spine_append]
  exact her

/-- `visitCases j ci`, the continuation of `withAppEtaToMinArity` for a recognized `casesOn` `c`
(`visitConstApp`, `LeanToLambdaBox/Erasure.lean:958`), on saturated spines (`SatSpec`), from
`visitExpr` at the fuels up to `j`: by the marking's branch (`MarkSat.casesProp`,
`MarkSat.casesReduced`, `MarkSat.cases`). Reference: the `tCase` case of `erases_erase`
(`MR E/ErasureFunction.v:1228`). -/
theorem visitCases_sat (hG : CoreEnv view cfg decls) {j : Nat}
    (ih : ∀ m ≤ j, ∀ e, ExprSpec view cfg decls m e) {c : Name} {us : List Level}
    {ci : CasesInfo} (hci : casesInfo? decls c = some ci)
    (hnm : cfg.nat = .machine → c ≠ ``Nat.casesOn ∧ c ≠ ``Int.casesOn) :
    SatSpec view cfg decls ci.arity c us (fun _ args => visitCases (m := PureM) j ci args) := by
  intro ρ S ls Sc ê st tc ps r st' ps' as hctx hR hsc hargs _ hok hs hrun
  dsimp only at hrun
  cases hs with
  | casesProp hco hd hlp =>
    obtain ⟨rfl, rfl, rfl⟩ := casesSat_box hci hco hd hlp hrun
    exact ⟨by simp only [renFV]; exact .box trivial, rfl, .box, .refl hok⟩
  | casesReduced hco hd hlp hpre hu hz hcn hcv hidx halt hlen hextra =>
    cases j with
    | zero => rw [visitCases] at hrun; cases hrun
    | succ j =>
    exact casesSat_reduced hG (fun m hm => ih m (by omega)) hci hco hd hlp hpre hu hz hcn
      hcv hidx halt hlen hextra hctx hR hsc hargs hok hrun
  | cases hco hd hlp hpre hac hu hC hdM hlen _ htys halts hlen' hextra =>
    cases j with
    | zero => rw [visitCases] at hrun; cases hrun
    | succ j =>
    exact casesSat_case hG (fun m hm => ih m (by omega)) hci hnm hco hd hlp hpre hac hu hC hdM
      hlen htys halts hlen' hextra hctx hR hsc hargs hok hrun
  | ctor h₁ | quotMk h₁ | quotLift h₁ | recr h₁ => rw [hci] at h₁; cases h₁

/-- `visitApp (k + 1)` on a spine of a recognized `casesOn` `c` that the oracle keeps, from
`visitExpr` at the fuels up to `k`: the marking is `MarkOf.special` (`c` has its arity,
`markArity?`), `visitConstApp` takes its `casesOn` branch, `withAppEtaToMinArity` η-expands the
spine (`withAppEta_spec`) and `visitCases` erases the saturated spine (`visitCases_sat`). The
head is no `Nat.casesOn`/`Int.casesOn` under `nat := .machine` (`NatPlain`). Adapted from
`ML-V Core/StepsCases.lean:416`. Reference: the `tCase` case of `erases_erase`
(`MR E/ErasureFunction.v:1228`); DV-23. -/
theorem visitApp_cases (hG : CoreEnv view cfg decls) {k : Nat} (ih : StepIH view cfg decls k)
    {ρ : FVarId → FVarId} {S : FVarId → Prop} {ls : List Local} {Sc : Name → Prop}
    {e ê : Expr} {st st' : ErasureState} {tc : TravCtx} {ps ps' : PureState} {r : LBTerm}
    {c : Name} {us : List Level} {ci : CasesInfo} (hfn : e.getAppFn = .const c us)
    (hci : casesInfo? decls c = some ci) (hctx : CtxOK cfg tc)
    (hR : RenOK ρ S ls tc.locals ps.next) (he : FVarsIn S e) (hsc : ScopeOK decls Sc)
    (hocc : ∀ d, nameOccurs d e = true → Sc d) (hnp : NatPlain cfg e) (hrs : RecShaped cfg decls e)
    (hok : StateOK noCert (evalEnvOf view cfg decls) st) (hm : MarkOf decls cfg ls e ê)
    (hor : Pure.isErasable ⟨decls⟩ oracleFuel tc.locals (renFV ρ e) = .ok false)
    (hrun : (visitApp (m := PureM) (k + 1) (renFV ρ e)).runPure st tc ⟨decls, view⟩ ps =
      .ok ((r, st'), ps')) :
    Erases noCert (evalEnvOf view cfg decls) [] (renFV ρ ê) r ∧ closedn 0 r = true ∧
      ErasesDeps noCert (evalEnvOf view cfg decls) st'.gdecls r ∧
      Grows (evalEnvOf view cfg decls) Sc st st' ps ps' := by
  have hma : markArity? decls cfg c = some ci.arity := by simp [markArity?, hci]
  have hor' := oracle_agree hG.closed hR he hor
  cases hm with
  | erase h₁ => rw [h₁] at hor'; cases hor'
  | @app _ f fM as âs _ _ hfa hfc =>
    rw [getAppFn_mkAppN_of hfa] at hfn
    exact absurd hfn (hfc c us)
  | @constApp _ c' us' as âs _ hma' =>
    rw [getAppFn_mkAppN_const] at hfn
    cases hfn
    rw [hma] at hma'; cases hma'
  | @special _ c' us' ar T ê as _ hma' hT hη =>
    rw [getAppFn_mkAppN_const] at hfn
    cases hfn
    rw [hma] at hma'
    cases hma'
    obtain ⟨⟨-, -, hnc, -⟩, hA⟩ := spine_premises (f := .const c us) ⟨he, hocc, hnp, hrs⟩
    have hnm : cfg.nat = .machine → c ≠ ``Nat.casesOn ∧ c ≠ ``Int.casesOn := fun h =>
      ⟨fun e => hnc h (by simp [e]), fun e => hnc h (by simp [e])⟩
    have hren : renFV ρ (mkAppN (.const c us) as.toArray) =
        mkAppN (.const c us) (as.map (renFV ρ)).toArray := renFV_mkAppN ρ _ as
    rw [hren, visitApp] at hrun
    simp only [getAppFn_mkAppN_const] at hrun
    cases k with
    | zero => rw [visitConstApp] at hrun; cases hrun
    | succ j =>
    rw [visitConstApp, withApp_mkAppN rfl] at hrun
    dsimp only at hrun
    rw [runPure_bind, show (liftM (Backend.casesInfo? (m := PureM) c) :
        EraseT PureM (Option CasesInfo)).runPure st tc ⟨decls, view⟩ ps = .ok ((some ci, st), ps) by
      show Except.ok ((casesInfo? decls c, st), ps) = _; rw [hci], ok_bind'] at hrun
    dsimp only at hrun
    exact withAppEta_spec hG.closed (visitCases_sat hG (fun m hm => ih.expr m (by omega)) hci hnm)
      hctx hR hsc hA hok hT hη hrun
  | fvar | mdata | lam | letE | proj | litZero | litSucc => cases hfn

/-- The `casesOn` step: an application or a constant whose head is a recognized `casesOn`
constant, through `visitApp_cases`. Adapted from `ML-V Core/StepsCases.lean:416`. Reference: the
`tCase` case of `erases_erase` (`MR E/ErasureFunction.v:1228`), rule `erases_tCase`
(`MR E/Extract.v:109`); DV-23, DV-25. -/
theorem visitExpr_cases_step (hG : CoreEnv view cfg decls) {fuel : Nat}
    (ih : StepIH view cfg decls fuel) {e : Expr} {c : Name} {us : List Level} {ci : CasesInfo}
    (hfn : e.getAppFn = .const c us) (hci : casesInfo? decls c = some ci) :
    ExprSpec view cfg decls (fuel + 1) e := by
  intro ρ S ls Sc ê st tc ps r st' ps' hctx hR he hsc hocc hnp hrs hok hm hrun
  have hstep : (visitExpr (m := PureM) (fuel + 1) (renFV ρ e)).runPure st tc ⟨decls, view⟩ ps =
      .ok ((r, st'), ps') → (Pure.isErasable ⟨decls⟩ oracleFuel tc.locals (renFV ρ e) = .ok true ∧
        r = .box ∧ st' = st ∧ ps' = ps) ∨
      (Pure.isErasable ⟨decls⟩ oracleFuel tc.locals (renFV ρ e) = .ok false ∧
        (visitApp (m := PureM) fuel (renFV ρ e)).runPure st tc ⟨decls, view⟩ ps =
          .ok ((r, st'), ps')) := by
    cases e with
    | app f a => intro h; simp only [renFV] at h ⊢; rw [visitExpr] at h; exact oracle_run h
    | const c' us' => intro h; simp only [renFV] at h ⊢; rw [visitExpr] at h; exact oracle_run h
    | _ => cases hfn
  rcases hstep hrun with ⟨hor, rfl, rfl, rfl⟩ | ⟨hor, hrun⟩
  · exact visitExpr_box hG.closed hR he hok hm hor
  cases fuel with
  | zero => rw [visitApp] at hrun; cases hrun
  | succ k =>
  exact visitApp_cases hG ⟨fun m hm => ih.expr m (by omega), fun m hm => ih.mutDecl m (by omega)⟩
    hfn hci hctx hR he hsc hocc hnp hrs hok hm hor hrun

end

end Steps

end EraseProof
