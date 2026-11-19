import EraseProof.Core.StepsApp
import EraseProof.Core.StepsRun
import EraseProof.Relation.Deps

/-!
# Steps of the shipping core's correctness: η-expansion and constructor spines

`visitConstApp` (`LeanToLambdaBox/Erasure.lean:958`) η-expands an application of a head with its
own rule to the head's arity (`withAppEtaToMinArity`, `:676`) and hands the saturated spine to the
rule. The marking traces this expansion (`MarkOf.special`, `MarkEta`): each missing argument is a
fresh local of the leading `Π` of the type the oracle infers for the spine (`forallView?`), and its
binder is an `eta`-marked λ. `withAppEta_spec` relates the expansion to `Erases.etaLam`, one λ
per missing argument, given what the rule does on a saturated spine (`SatSpec`); the traversal's
fresh variable is the next one of the counter, to which the marking's is renamed (`RenOK.push`),
and the λ is closed again by `abstract` (`Erases.abstract`).

A constructor spine (`visitExpr_ctor_step`) is saturated and erased by `visitConstructor`
(`:1035`): its inductive's block is registered (`register_inductive_spec`), every field is kept
(`KeepMasks`, `slices_keep`) and the arguments are erased one at a time (`visitAppArgs_list`), which
is `Erases.ctor`. A constructor spine that the oracle keeps is not of an inductive declared in
`Prop` (`CtorPropBoxed`, a fact about the shipping oracle).

Reference: the `tConstruct` case of `erases_erase` (`MR E/ErasureFunction.v:1228`), rule
`erases_tConstruct` (`MR E/Extract.v:106`); η-expansion: DV-23. Adapted from
`ML-V Core/StepsCtor.lean:209-915, 1051-1200`, whose typing premises are replaced by the marking.
-/

open Lean Erasure

namespace EraseProof

namespace Steps

open RegisterInd OracleRen StateLemmas Decls

/-! ## Registering an inductive block from a traversal context -/

section
variable {decls : List ConstantInfo} {view : EnvView} {cfg : ErasureConfig}

/-- `register_inductive` at the pure backend on an inductive `T` of the closure, from a context
with `CtxOK`: the run keeps `StateOK`, grows the λ□ environment freshly, keeps the registered
constants and the counter, and registers `T` with its λ□ inductive, its erased block and masks
that keep every field. From `register_inductive_ok` and `register_inductive_run`. Reference:
`erase_global_deps` (`MR E/ErasureFunction.v:1602`) on an inductive block. -/
theorem register_inductive_spec (hG : CoreEnv view cfg decls) {tc : TravCtx} {st st' : ErasureState}
    {ps ps' : PureState} {T : Name} {iv : InductiveVal} {r : InductiveId × InductiveArgMasks}
    (hctx : CtxOK cfg tc) (hok : StateOK noCert (evalEnvOf view cfg decls) st)
    (hT : findDecl decls T = some (.inductInfo iv))
    (h : (register_inductive (m := PureM) iv).runPure st tc ⟨decls, view⟩ ps = .ok ((r, st'), ps')) :
    StateOK noCert (evalEnvOf view cfg decls) st' ∧ LenvExt st.gdecls st'.gdecls ∧
      st'.constants = st.constants ∧ IndIdOf (evalEnvOf view cfg decls) T = some r.1 ∧
      ErasesInd (evalEnvOf view cfg decls) st'.gdecls T ∧ KeepMasks (evalEnvOf view cfg decls) iv r.2 ∧
      ps' = ps := by
  have hname : iv.name = T := (findDecl_eq_some hT).2
  subst hname
  have hirr : tc.config.remove_irrel_constr_args = false := by
    rw [hctx.config]; exact hG.irr iv ⟨_, (findDecl_eq_some hT).1, rfl⟩
  have hph : ∀ ci ∈ (evalEnvOf view cfg decls).decls,
      PhaseIDecl (⟨decls, view⟩ : PureCtx).view tc.config (evalEnvOf view cfg decls).decls ci := by
    rw [hctx.config]; exact hG.phase
  obtain ⟨hnd, hmem, hco⟩ := hG.block _ iv hT
  obtain ⟨hok', hext, hcst, hiid, hkm⟩ :=
    register_inductive_ok hok rfl hirr hph hG.bn hT hnd hmem hco h
  have hext' : ∀ cn cv, findDecl (evalEnvOf view cfg decls).decls cn = some (.ctorInfo cv) →
      tc.config.1 = .preferAxiom → (⟨decls, view⟩ : PureCtx).view.isExtern cn = false := by
    intro cn cv hc hx
    obtain ⟨hm, hn⟩ := findDecl_eq_some hc
    have := (hph _ hm).2 hx
    rwa [show cv.name = cn from hn] at this
  have hin : st'.inductives[iv.name]? = some r := by
    rcases register_inductive_run rfl hirr hext' hnd st st ps r st' ps' rfl h with
      ⟨hr, rfl⟩ | ⟨-, s₁, -, -, -, hr, rfl⟩
    · exact hr
    · exact hr
  exact ⟨hok', hext, hcst, hiid, (hok'.inductives _ r hin).2.1, hkm,
    KeepsPS.register_inductive iv _ _ _ _ _ _ h⟩

end

/-! ## The arguments of a constructor spine -/

/-- A mask that keeps the first `n ≥ l.length` fields keeps the list. Copy of
`ML-V Core/StepsCtor.lean:226`. -/
theorem filterMap_keep {α : Type} : ∀ (l : List α) (n : Nat), l.length ≤ n →
    ((List.replicate n ConstructorArgRelevance.keep).zip l).filterMap
      (fun (x : ConstructorArgRelevance × α) => match x with
        | (r, a) => match r with | .erase => none | .keep => some a) = l
  | [], _, _ => by simp
  | a :: l, n + 1, h => by
    simp only [List.replicate_succ, List.zip_cons_cons, List.filterMap_cons]
    rw [filterMap_keep l n (by simp at h; omega)]
  | _ :: _, 0, h => by simp at h

/-- A mask that keeps every field leaves the fields unchanged. Copy of
`ML-V Core/StepsCtor.lean:237`. -/
theorem filter_keep {α : Type} (arr : Array α) (n : Nat) (h : arr.size ≤ n) :
    filter (Array.replicate n .keep) arr = arr := by
  apply Array.ext'
  unfold filter
  rw [Array.toList_filterMap, Array.toList_zip, Array.toList_replicate]
  exact filterMap_keep arr.toList n (by simpa using h)

/-- The arguments of a constructor spine reassembled by `visitConstructor` around the kept fields
are the arguments. Copy of `ML-V Core/StepsCtor.lean:246`. -/
theorem slices_keep {α : Type} (l : List α) (p f : Nat) (h : p + f ≤ l.length) :
    Std.Slice.toArray (l.toArray.toSubarray 0 p) ++
      filter (Array.replicate f .keep) ↑(l.toArray.toSubarray p (p + f)) ++
      Std.Slice.toArray (l.toArray.toSubarray (p + f)) = l.toArray := by
  simp only [Subarray.copy_eq_toArray]
  rw [filter_keep _ _ (by
    simp only [Subarray.size_toArray, Subarray.size_eq, Array.start_toSubarray,
      Array.stop_toSubarray, List.size_toArray]
    omega)]
  apply Array.ext'
  rw [Array.toList_append, Array.toList_append, ← Subarray.toArray_toList, ← Subarray.toArray_toList,
    ← Subarray.toArray_toList]
  simp only [List.toList_toArray, Subarray.toList_eq_drop_take, Array.array_toSubarray,
    Array.start_toSubarray, Array.stop_toSubarray, List.size_toArray]
  rw [show min 0 (min p l.length) = 0 by omega, show min p l.length = p by omega,
    show min (p + f) l.length = p + f by omega, show min p (p + f) = p by omega,
    show min l.length l.length = l.length by omega, show min (p + f) l.length = p + f by omega,
    List.take_length, List.drop_zero]
  conv => rhs; rw [← List.take_append_drop (p + f) l]
  congr 1
  conv => rhs; rw [← List.take_append_drop p (List.take (p + f) l)]
  rw [List.take_take, show min p (p + f) = p by omega]

section
variable {decls : List ConstantInfo} {view : EnvView} {cfg : ErasureConfig}

/-- The premises of `ExprSpec` that an argument of a spine carries: its free variables in `S`,
its constants in the scope `Sc`, `NatPlain`, `RecShaped`. Reference: none. -/
abbrev ArgOK (S : FVarId → Prop) (Sc : Name → Prop) (cfg : ErasureConfig)
    (decls : List ConstantInfo) (a : Expr) : Prop :=
  FVarsIn S a ∧ (∀ d, nameOccurs d a = true → Sc d) ∧ NatPlain cfg a ∧ RecShaped cfg decls a

/-- `visitAppArgs (j + 1) tf args`, from `visitExpr` at `j` (`ih`): the head applied to closed
erasures of the arguments' markings, one at a time, each with erased dependencies. Adapted from
`ML-V Core/StepsCtor.lean:518`. Reference: the `tApp` case of `erases_erase`
(`MR E/ErasureFunction.v:1228`). -/
theorem visitAppArgs_list {j : Nat} (ih : ∀ e, ExprSpec view cfg decls j e)
    {ρ : FVarId → FVarId} {S : FVarId → Prop} {ls : List Local} {Sc : Name → Prop}
    {st st' : ErasureState} {tc : TravCtx} {ps ps' : PureState} {r tf : LBTerm}
    {as âs : List Expr} (hctx : CtxOK cfg tc) (hsc : ScopeOK decls Sc)
    (hR : RenOK ρ S ls tc.locals ps.next) (hargs : ∀ a ∈ as, ArgOK S Sc cfg decls a)
    (hlen : as.length = âs.length)
    (hm : ∀ (i : Nat) a â, as[i]? = some a → âs[i]? = some â → MarkOf decls cfg ls a â)
    (hok : StateOK noCert (evalEnvOf view cfg decls) st)
    (hrun : (visitAppArgs (m := PureM) (j + 1) tf (as.map (renFV ρ)).toArray).runPure st tc
      ⟨decls, view⟩ ps = .ok ((r, st'), ps')) :
    ∃ as' : List LBTerm, r = mkApps tf as' ∧ (âs.map (renFV ρ)).length = as'.length ∧
      (∀ (i : Nat) a a', (âs.map (renFV ρ))[i]? = some a → as'[i]? = some a' →
        Erases noCert (evalEnvOf view cfg decls) [] a a') ∧
      (∀ a' ∈ as', closedn 0 a' = true ∧ ErasesDeps noCert (evalEnvOf view cfg decls) st'.gdecls a') ∧
      Grows (evalEnvOf view cfg decls) Sc st st' ps ps' := by
  rw [visitAppArgs, ← Array.foldlM_toList, List.toList_toArray] at hrun
  induction as generalizing âs tf st ps with
  | nil =>
    cases âs with
    | nil => cases hrun; exact ⟨[], rfl, rfl, by simp, by simp, .refl hok⟩
    | cons => cases hlen
  | cons a l ihl =>
    cases âs with
    | nil => cases hlen
    | cons â âl =>
    rw [List.map_cons, List.foldlM_cons, runPure_bind] at hrun
    obtain ⟨⟨⟨x, st₁⟩, ps₁⟩, hx, hrun⟩ := ok_of_bind hrun
    rw [runPure_bind] at hx
    obtain ⟨⟨⟨ta, st₂⟩, ps₂⟩, ha, hx⟩ := ok_of_bind hx
    cases hx
    obtain ⟨hfa, hoa, hna, hra⟩ := hargs a (.head _)
    have ⟨hera, hca, hdepsa, hgra⟩ := ih a hctx hR hfa hsc hoa hna hra hok (hm 0 a â rfl rfl) ha
    obtain ⟨as', rfl, hlen', hers, hdeps, hgr⟩ := ihl (tf := .app tf ta) (hR.mono hgra.next)
      (fun b hb => hargs b (.tail _ hb)) (by simpa using hlen)
      (fun i b bM h1 h2 => hm (i + 1) b bM h1 h2) hgra.inv hrun
    refine ⟨ta :: as', rfl, by simp [hlen'], fun i b b' h1 h2 => ?_, fun b hb => ?_,
      hgra.trans hgr⟩
    · cases i with
      | zero => simp at h1 h2; subst h1 h2; exact hera
      | succ i => exact hers i b b' (by simpa using h1) (by simpa using h2)
    · rcases List.mem_cons.1 hb with rfl | hb
      · exact ⟨hca, ErasesDeps.ext hgr.ext hdepsa⟩
      · exact hdeps b hb

/-- `visitConstructor (j + 1) c args` at the pure backend, from `visitExpr` at the fuels up to `j`,
on a constructor `c` with at least its arity of arguments, of an inductive not declared in `Prop`:
the inductive's block is registered, every field is kept, and the result is the λ□ constructor
applied to erasures of the arguments' markings (`Erases.ctor`), closed, with the block erased.
Adapted from `ML-V Core/StepsCtor.lean:571, 677`. Reference: the `tConstruct` case of
`erases_erase` (`MR E/ErasureFunction.v:1228`), rule `erases_tConstruct` (`MR E/Extract.v:106`). -/
theorem visitConstructor_spec (hG : CoreEnv view cfg decls) {j : Nat}
    (ih : ∀ m ≤ j, ∀ e, ExprSpec view cfg decls m e)
    {ρ : FVarId → FVarId} {S : FVarId → Prop} {ls : List Local} {Sc : Name → Prop}
    {st st' : ErasureState} {tc : TravCtx} {ps ps' : PureState} {r : LBTerm}
    {c : Name} {us : List Level} {cv : ConstructorVal} {as âs : List Expr}
    (hctx : CtxOK cfg tc) (hsc : ScopeOK decls Sc) (hR : RenOK ρ S ls tc.locals ps.next)
    (hargs : ∀ a ∈ as, ArgOK S Sc cfg decls a) (hlen : as.length = âs.length)
    (hm : ∀ (i : Nat) a â, as[i]? = some a → âs[i]? = some â → MarkOf decls cfg ls a â)
    (hc : findDecl decls c = some (.ctorInfo cv)) (har : cv.numParams + cv.numFields ≤ as.length)
    (hnprop : (evalEnvOf view cfg decls).propInd cv.induct = false)
    (hnat : cfg.nat = .machine → c ≠ ``Nat.zero ∧ c ≠ ``Nat.succ)
    (hok : StateOK noCert (evalEnvOf view cfg decls) st)
    (hrun : (visitConstructor (m := PureM) (j + 1) c (as.map (renFV ρ)).toArray).runPure st tc
      ⟨decls, view⟩ ps = .ok ((r, st'), ps')) :
    Erases noCert (evalEnvOf view cfg decls) [] (renFV ρ (mkAppN (.const c us) âs.toArray)) r ∧
      closedn 0 r = true ∧ ErasesDeps noCert (evalEnvOf view cfg decls) st'.gdecls r ∧
      Grows (evalEnvOf view cfg decls) Sc st st' ps ps' := by
  rw [visitConstructor, runPure_bind] at hrun
  obtain ⟨⟨⟨ci, st₁⟩, ps₁⟩, hci, hrun⟩ := ok_of_bind hrun
  obtain ⟨hfc, h1, h2⟩ := getConst_run hci
  subst st₁ ps₁
  rw [show findConst decls c = findDecl decls c from rfl, hc] at hfc
  cases hfc
  dsimp only at hrun
  rw [runPure_bind] at hrun
  obtain ⟨⟨⟨ci, st₁⟩, ps₁⟩, hci, hrun⟩ := ok_of_bind hrun
  obtain ⟨hfi, h1, h2⟩ := getConst_run hci
  subst st₁ ps₁
  cases ci with
  | inductInfo iv =>
    dsimp only at hrun
    rw [runPure_bind] at hrun
    obtain ⟨⟨⟨rr, st₁⟩, ps₁⟩, hreg, hrun⟩ := ok_of_bind hrun
    have hiv : findDecl decls cv.induct = some (.inductInfo iv) := hfi
    obtain ⟨hok₁, hext₁, hcst₁, hiid, hind, hkm, hps⟩ :=
      register_inductive_spec hG hctx hok hiv hreg
    subst ps₁
    dsimp only at hrun
    rw [runPure_bind] at hrun
    obtain ⟨⟨⟨mask, st₂⟩, ps₂⟩, hmask, hrun⟩ := ok_of_bind hrun
    obtain ⟨hmk, h1, h2⟩ := getOrFail_run hmask
    subst st₂ ps₂
    dsimp only at hrun
    rw [runPure_bind, isExtern_runPure, ok_bind'] at hrun
    dsimp only at hrun
    rw [runPure_read_bind] at hrun
    have hmem : ConstantInfo.ctorInfo cv ∈ decls := (findDecl_eq_some hc).1
    have hcn : cv.name = c := (findDecl_eq_some hc).2
    have hne : (view.isExtern c && tc.config.1 == .preferAxiom) = false := by
      rw [hctx.config]
      cases hcfg : cfg.1 with
      | preferAxiom =>
        have := (hG.phase _ hmem).2 hcfg
        rw [hcn] at this
        simp [this]
      | _ => cases view.isExtern c <;> rfl
    rw [hne, ite_eq_right_of_eq_false _ _ (eq_false Bool.false_ne_true), runPure_read_bind, hctx.config]
      at hrun
    obtain ⟨iv', hiv', hpos, -⟩ := hG.ctors c cv hc
    rw [hiv] at hiv'
    cases hiv'
    have hmask' : mask = Array.replicate cv.numFields .keep := by
      have := hkm.2 cv.cidx _ cv hpos hc
      rw [hmk] at this
      cases this; rfl
    split at hrun
    · exact absurd rfl (hnat ‹cfg.nat = .machine›).1
    · exact absurd rfl (hnat ‹cfg.nat = .machine›).2
    all_goals
      rw [hmask', slices_keep (as.map (renFV ρ)) cv.numParams cv.numFields (by simpa using har)]
        at hrun
      cases j with
      | zero => rw [visitAppArgs] at hrun; cases hrun
      | succ i =>
        obtain ⟨as', rfl, hlen', hers, hdeps, hgr⟩ :=
          visitAppArgs_list (ih i (by omega)) hctx hsc hR hargs hlen hm hok₁ hrun
        refine ⟨?_, RecLam.closedn_mkApps.2 ⟨rfl, fun a' ha' => (hdeps a' ha').1⟩,
          ErasesDeps.mkApps_iff.2 ⟨.construct hiid (ErasesInd.ext hgr.ext hind) (by simp),
            fun a' ha' => (hdeps a' ha').2⟩,
          Grows.trans ⟨hok₁, hext₁, Nat.le_refl _, fun c' kn h1 h2 => ?_⟩ hgr⟩
        · rw [renFV_mkAppN]
          have hname : iv.name = cv.induct := (findDecl_eq_some hiv).2
          exact .ctor hc hnprop (hname ▸ hiid) (by simpa [← hlen] using har) hlen' hers
        · rw [hcst₁, h1] at h2
          cases h2
  | _ => dsimp only at hrun; cases hrun

end

/-! ## η-expansion -/

section
variable {pc : PureCtx}

/-- `forallMonocular t k` at the pure backend, where `forallView?` reads the leading `Π` of `t`:
`k` runs on the next variable of the counter, pushed as a local of the `Π`'s domain, and on the
`Π`'s body opened with it. Reference: none. -/
theorem forallMonocular_run {α : Type} {t D C : Expr} {y : Name} {bi : BinderInfo} {tc : TravCtx}
    {st : ErasureState} {ps : PureState} (k : FVarId → Expr → EraseT PureM α)
    (hv : forallView? pc.decls tc.locals t = some (y, D, C, bi)) :
    (forallMonocular (m := PureM) t k).runPure st tc pc ps =
      (k (pureFVar ps.next) (C.instantiate1' (.fvar (pureFVar ps.next)))).runPure st
        { tc with lctx := tc.lctx.mkLocalDecl (pureFVar ps.next) y D bi,
                  locals := ⟨pureFVar ps.next, y, D, none⟩ :: tc.locals } pc ⟨ps.next + 1⟩ := by
  unfold forallMonocular
  by_cases hf : t.isForall = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hf)]
    cases t with
    | forallE y' D' C' bi' =>
      simp only [forallView?] at hv
      cases hv
      rfl
    | _ => cases hf
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hf)]
    have hnf : ∀ y D C bi, t ≠ .forallE y D C bi := by rintro _ _ _ _ rfl; exact hf rfl
    rw [OracleRen.forallView?_of_not hnf] at hv
    have hw : Pure.whnf ⟨pc.decls⟩ oracleFuel tc.locals t = .ok (.forallE y D C bi) := by
      rcases hw : Pure.whnf ⟨pc.decls⟩ oracleFuel tc.locals t with err | w
      · rw [hw] at hv; cases hv
      · rw [hw] at hv
        cases w <;> try cases hv
        rfl
    rw [runPure_read_bind, runPure_read_bind, runPure_bind, runPure_liftM]
    have hrun : ((Backend.whnf (m := PureM) tc.lctx tc.locals t).run pc).run ps =
        .ok (.forallE y D C bi, ps) := by
      change ((match Pure.whnf ⟨pc.decls⟩ oracleFuel tc.locals t with
        | .ok t => (Pure.pure t : PureM Expr) | .error err => throw err).run pc).run ps = _
      rw [hw]; rfl
    rw [hrun]
    rfl

end

section
variable {decls : List ConstantInfo} {view : EnvView} {cfg : ErasureConfig}

/-- What the continuation `kont` of `withAppEtaToMinArity` at the arity `ar` does on the head
`c.{us}` and at least `ar` arguments: on a saturated spine marked by `MarkSat`, from the
premises of `ExprSpec` on the arguments, a successful run on the renamed arguments erases the
renamed marking, closed, with erased dependencies, and `Grows`. Adapted from
`ML-V Core/StepsCtor.lean:704`. Reference: none (DV-23). -/
def SatSpec (view : EnvView) (cfg : ErasureConfig) (decls : List ConstantInfo) (ar : Nat) (c : Name)
    (us : List Level) (kont : Expr → Array Expr → EraseT PureM LBTerm) : Prop :=
  ∀ ⦃ρ : FVarId → FVarId⦄ ⦃S : FVarId → Prop⦄ ⦃ls : List Local⦄ ⦃Sc : Name → Prop⦄ ⦃ê : Expr⦄
    ⦃st : ErasureState⦄ ⦃tc : TravCtx⦄ ⦃ps : PureState⦄ ⦃r : LBTerm⦄ ⦃st' : ErasureState⦄
    ⦃ps' : PureState⦄ ⦃as : List Expr⦄,
    CtxOK cfg tc → RenOK ρ S ls tc.locals ps.next → ScopeOK decls Sc →
    (∀ a ∈ as, ArgOK S Sc cfg decls a) → ar ≤ as.length →
    StateOK noCert (evalEnvOf view cfg decls) st → MarkSat decls cfg ls c us as ê →
    (kont (.const c us) (as.map (renFV ρ)).toArray).runPure st tc ⟨decls, view⟩ ps =
      .ok ((r, st'), ps') →
    Erases noCert (evalEnvOf view cfg decls) [] (renFV ρ ê) r ∧ closedn 0 r = true ∧
      ErasesDeps noCert (evalEnvOf view cfg decls) st'.gdecls r ∧
      Grows (evalEnvOf view cfg decls) Sc st st' ps ps'

/-- The η-expansion loop `withAppEtaToMinArity.go` at the arity `ar` on the renamed spine
`c.{us} as` and the renamed type `T`, given what the continuation does on a saturated spine
(`SatSpec`): each missing argument is the next variable of the counter, to which the marking's
fresh variable is renamed (`RenOK.push`), at the leading `Π` that `forallView?` reads, and its λ is
closed again by `abstract`, which erases the `eta`-marked λ of `MarkEta.intro` (`Erases.etaLam`,
`Erases.abstract`); at the arity the continuation runs (`MarkEta.sat`). Adapted from
`ML-V Core/StepsCtor.lean:725`. Reference: none (MetaRocq η-expands in λ□,
`MR E/EEtaExpanded.v`; DV-23). -/
theorem etaGo_spec (hcl : ClosedDecls decls = true) {ar : Nat} {c : Name} {us : List Level}
    {kont : Expr → Array Expr → EraseT PureM LBTerm} (hk : SatSpec view cfg decls ar c us kont) :
    ∀ (fuel : Nat) {ρ : FVarId → FVarId} {S : FVarId → Prop} {ls : List Local} {Sc : Name → Prop}
      {st st' : ErasureState} {tc : TravCtx} {ps ps' : PureState} {r : LBTerm} {T ê : Expr}
      {as : List Expr},
      CtxOK cfg tc → RenOK ρ S ls tc.locals ps.next → ScopeOK decls Sc →
      (∀ a ∈ as, ArgOK S Sc cfg decls a) → FVarsIn S T →
      StateOK noCert (evalEnvOf view cfg decls) st → MarkEta decls cfg ls ar T c us as ê →
      (withAppEtaToMinArity.go (m := PureM) ar kont fuel (renFV ρ T) (.const c us)
        (as.map (renFV ρ)).toArray).runPure st tc ⟨decls, view⟩ ps = .ok ((r, st'), ps') →
      Erases noCert (evalEnvOf view cfg decls) [] (renFV ρ ê) r ∧ closedn 0 r = true ∧
        ErasesDeps noCert (evalEnvOf view cfg decls) st'.gdecls r ∧
        Grows (evalEnvOf view cfg decls) Sc st st' ps ps' := by
  intro fuel
  induction fuel with
  | zero =>
    intro ρ S ls Sc st st' tc ps ps' r T ê as _ _ _ _ _ _ _ hrun
    rw [withAppEtaToMinArity.go] at hrun; cases hrun
  | succ fuel ihf =>
    intro ρ S ls Sc st st' tc ps ps' r T ê as hctx hR hsc hargs hT hok hη hrun
    rw [withAppEtaToMinArity.go] at hrun
    by_cases hge : (as.map (renFV ρ)).toArray.size ≥ ar
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hge)] at hrun
      cases hη with
      | sat hle hs => exact hk hctx hR hsc hargs hle hok hs hrun
      | intro hlt => simp at hge; omega
    rw [ite_eq_right_of_eq_false _ _ (eq_false hge)] at hrun
    cases hη with
    | sat hle => simp at hge; omega
    | @intro _ _ _ y D C bi x _ _ _ _ hlt hv hfr hη =>
    have ⟨hD, hC⟩ := fvarsIn_view hcl hR.supp hT hv
    have hv' : forallView? decls tc.locals (renFV ρ T) = some (y, renFV ρ D, renFV ρ C, bi) := by
      rw [(forallView?_ren hcl hR.supp hR.ren T hT).1, hv]; rfl
    rw [forallMonocular_run _ hv', runPure_bind] at hrun
    obtain ⟨⟨⟨r₀, st₁⟩, ps₁⟩, hgo, hrun⟩ := ok_of_bind hrun
    dsimp only at hrun
    rw [mkLambda_run (l := ⟨pureFVar ps.next, y, renFV ρ D, none⟩) rfl rfl] at hrun
    cases hrun
    have hR' := hR.push (n := y) (val := none) hfr hD (fun _ h => nomatch h)
    have hxS := hR.not_mem hfr
    have hagree : ∀ z, S z → renExt ρ x (pureFVar ps.next) z = ρ z := fun z hz =>
      renExt_ne fun e => hxS (e ▸ hz)
    have hxC : FVarsIn (· ≠ x) C := fvarsIn_mono (fun z hz (e : z = x) => hxS (e ▸ hz)) hC
    have hrenC : renFV (renExt ρ x (pureFVar ps.next)) (C.instantiate1' (.fvar x)) =
        (renFV ρ C).instantiate1' (.fvar (pureFVar ps.next)) := by
      rw [renFV_inst, renFV_congr (p := (· ≠ x)) (fun z hz => renExt_ne hz) hxC]
      simp only [renFV, renExt_self]
    have hmap : (as ++ [Expr.fvar x]).map (renFV (renExt ρ x (pureFVar ps.next))) =
        as.map (renFV ρ) ++ [.fvar (pureFVar ps.next)] := by
      simp only [List.map_append, List.map_cons, List.map_nil, renFV, renExt_self]
      exact congrArg (· ++ _) (List.map_congr_left fun a ha => renFV_congr hagree (hargs a ha).1)
    rw [List.push_toArray, ← hmap, ← hrenC] at hgo
    have hargs' : ∀ a ∈ as ++ [Expr.fvar x], ArgOK (fun z => S z ∨ z = x) Sc cfg decls a := by
      intro a ha
      rcases List.mem_append.1 ha with ha | ha
      · obtain ⟨h1, h2, h3, h4⟩ := hargs a ha
        exact ⟨fvarsIn_mono (fun _ => .inl) h1, h2, h3, h4⟩
      · rw [List.mem_singleton] at ha
        subst ha
        exact ⟨Or.inr rfl, (fun _ h => nomatch h), trivial, trivial⟩
    have ⟨her, hc0, hdeps, hgr⟩ := ihf (by exact ⟨hctx.config, hctx.fixvars⟩) (by exact hR') hsc hargs'
      (fvarsIn_open hC) hok hη hgo
    have hêS := MarkEta.fvarsIn hcl hη hR'.supp (fvarsIn_open hC) fun a ha => (hargs' a ha).1
    have habs := absFV_renExt (d := 0) (fun z hz => hR.fresh z hz ps.next (Nat.le_refl _)) hêS
    refine ⟨?_, closedn_toBvar _ r₀ 0 hc0, .lambda (ErasesDeps.toBvar hdeps 0),
      ⟨hgr.inv, hgr.ext, Nat.le_trans (Nat.le_succ _) hgr.next, hgr.scope⟩⟩
    simp only [renFV]
    refine .etaLam ?_
    rw [← habs]
    exact Erases.abstract hc0 her

/-- `withAppEtaToMinArity f e ar kont` at the pure backend on the renamed spine of `c.{us} as`,
whose marking is the η-expansion `MarkEta` on the type the oracle infers for the spine, given
what `kont` does on a saturated spine (`SatSpec`): the result erases the renamed marking, closed,
with erased dependencies, and `Grows`. The traversal infers the type of the renamed spine under
its locals, the renamed type (`inferType_ren`). Adapted from `ML-V Core/StepsCtor.lean:841`.
Reference: none (MetaRocq η-expands in λ□, `MR E/EEtaExpanded.v`; DV-23). -/
theorem withAppEta_spec (hcl : ClosedDecls decls = true) {ar f : Nat} {c : Name}
    {us : List Level} {kont : Expr → Array Expr → EraseT PureM LBTerm}
    (hk : SatSpec view cfg decls ar c us kont)
    {ρ : FVarId → FVarId} {S : FVarId → Prop} {ls : List Local} {Sc : Name → Prop}
    {st st' : ErasureState} {tc : TravCtx} {ps ps' : PureState} {r : LBTerm} {T ê : Expr}
    {as : List Expr} (hctx : CtxOK cfg tc) (hR : RenOK ρ S ls tc.locals ps.next)
    (hsc : ScopeOK decls Sc) (hargs : ∀ a ∈ as, ArgOK S Sc cfg decls a)
    (hok : StateOK noCert (evalEnvOf view cfg decls) st)
    (hT : Pure.inferType ⟨decls⟩ oracleFuel ls [] (mkAppN (.const c us) as.toArray) = .ok T)
    (hη : MarkEta decls cfg ls ar T c us as ê)
    (hrun : (withAppEtaToMinArity (m := PureM) f (mkAppN (.const c us) (as.map (renFV ρ)).toArray)
      ar kont).runPure st tc ⟨decls, view⟩ ps = .ok ((r, st'), ps')) :
    Erases noCert (evalEnvOf view cfg decls) [] (renFV ρ ê) r ∧ closedn 0 r = true ∧
      ErasesDeps noCert (evalEnvOf view cfg decls) st'.gdecls r ∧
      Grows (evalEnvOf view cfg decls) Sc st st' ps ps' := by
  have he : FVarsIn S (mkAppN (.const c us) as.toArray) :=
    fvarsIn_mkAppN.2 ⟨trivial, fun a ha => (hargs a ha).1⟩
  have hren : renFV ρ (mkAppN (.const c us) as.toArray) =
      mkAppN (.const c us) (as.map (renFV ρ)).toArray := renFV_mkAppN ρ _ as
  have hT' : Pure.inferType ⟨decls⟩ oracleFuel tc.locals [] (mkAppN (.const c us)
      (as.map (renFV ρ)).toArray) = .ok (renFV ρ T) := by
    have := (inferType_ren (cx := ⟨decls⟩) hcl hR.supp hR.ren oracleFuel [] _ he (by simp)).1
    rw [hT, hren] at this
    exact this
  rw [withAppEtaToMinArity, runPure_read_bind, runPure_read_bind, runPure_bind,
    inferType_runPure, hT'] at hrun
  dsimp only [Except.map] at hrun
  rw [ok_bind'] at hrun
  dsimp only at hrun
  rw [withApp_mkAppN rfl] at hrun
  exact etaGo_spec hcl hk f hctx hR hsc hargs (fvarsIn_oracle_ty hcl hR.supp he hT) hok hη hrun

end

/-! ## Constructor spines -/

/-- On a spine of a constructor of an inductive declared in `Prop` (`EvalEnv.propInd`), the
shipping oracle answers `true` or fails, never `false`, under every list of locals. Statement of
`ML-V Oracle/Atom.lean:515 Pure.isErasable_ctorProp` at `evalEnvOf`, with `propInd` for the
evident proposition of the constructor's type. Reference: `isErasable` on propositional
constructors (`MR E/Extract.v:106 erases_tConstruct`, `~~ isPropositional`); DV-11. -/
def CtorPropBoxed (view : EnvView) (cfg : ErasureConfig) (decls : List ConstantInfo) : Prop :=
  ∀ (ls : List Local) (c : Name) (us : List Level) (as : List Expr) (cv : ConstructorVal) (b : Bool),
    findDecl decls c = some (.ctorInfo cv) →
    (evalEnvOf view cfg decls).propInd cv.induct = true →
    Pure.isErasable ⟨decls⟩ oracleFuel ls (mkAppN (.const c us) as.toArray) = .ok b → b = true

section
variable {decls : List ConstantInfo} {view : EnvView} {cfg : ErasureConfig}

/-- `visitApp (k + 1)` on a constructor spine that the oracle keeps, from `visitExpr` at the fuels
up to `k`: the marking is `MarkOf.special` (the constructor has its arity, `markArity?`),
`visitConstApp` takes its constructor branch, `withAppEtaToMinArity` η-expands the spine
(`withAppEta_spec`) and `visitConstructor` erases the saturated spine (`visitConstructor_spec`,
`MarkSat.ctor`). Adapted from `ML-V Core/StepsCtor.lean:1051`. Reference: the `tConstruct` case of
`erases_erase` (`MR E/ErasureFunction.v:1228`); DV-23. -/
theorem visitApp_ctor (hG : CoreEnv view cfg decls) (hcp : CtorPropBoxed view cfg decls)
    {k : Nat} (ih : StepIH view cfg decls k) {ρ : FVarId → FVarId} {S : FVarId → Prop}
    {ls : List Local} {Sc : Name → Prop} {e ê : Expr} {st st' : ErasureState} {tc : TravCtx}
    {ps ps' : PureState} {r : LBTerm} {c : Name} {us : List Level} {n : Nat}
    (hfn : e.getAppFn = .const c us) (hcs : casesInfo? decls c = none)
    (hca : ctorArity? decls c = some n) (hctx : CtxOK cfg tc)
    (hR : RenOK ρ S ls tc.locals ps.next) (he : FVarsIn S e) (hsc : ScopeOK decls Sc)
    (hocc : ∀ d, nameOccurs d e = true → Sc d) (hnp : NatPlain cfg e) (hrs : RecShaped cfg decls e)
    (hok : StateOK noCert (evalEnvOf view cfg decls) st) (hm : MarkOf decls cfg ls e ê)
    (hor : Pure.isErasable ⟨decls⟩ oracleFuel tc.locals (renFV ρ e) = .ok false)
    (hrun : (visitApp (m := PureM) (k + 1) (renFV ρ e)).runPure st tc ⟨decls, view⟩ ps =
      .ok ((r, st'), ps')) :
    Erases noCert (evalEnvOf view cfg decls) [] (renFV ρ ê) r ∧ closedn 0 r = true ∧
      ErasesDeps noCert (evalEnvOf view cfg decls) st'.gdecls r ∧
      Grows (evalEnvOf view cfg decls) Sc st st' ps ps' := by
  obtain ⟨cv, hc, rfl⟩ : ∃ cv, findDecl decls c = some (.ctorInfo cv) ∧
      n = cv.numParams + cv.numFields := by
    unfold ctorArity? at hca
    split at hca
    · rename_i cv hcv
      cases hca
      exact ⟨cv, hcv, rfl⟩
    · cases hca
  have hma : markArity? decls cfg c = some (cv.numParams + cv.numFields) := by
    simp [markArity?, hcs, hca]
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
    have hnc' : cfg.nat = .machine → c ∉ [``Nat.zero, ``Nat.succ, ``Int.ofNat, ``Int.negSucc,
        ``Nat.casesOn, ``Int.casesOn] := hnc
    have hnat : cfg.nat = .machine → c ≠ ``Nat.zero ∧ c ≠ ``Nat.succ := fun h =>
      ⟨fun e => hnc' h (by rw [e]; simp), fun e => hnc' h (by rw [e]; simp)⟩
    have hren : renFV ρ (mkAppN (.const c us) as.toArray) =
        mkAppN (.const c us) (as.map (renFV ρ)).toArray := renFV_mkAppN ρ _ as
    have hnprop : (evalEnvOf view cfg decls).propInd cv.induct = false := by
      cases hp : (evalEnvOf view cfg decls).propInd cv.induct with
      | false => rfl
      | true => cases hcp _ c us _ cv false hc hp (by rw [← hren]; exact hor)
    have hca' : ctorArity? decls c = some (cv.numParams + cv.numFields) := hca
    rw [hren, visitApp] at hrun
    simp only [getAppFn_mkAppN_const] at hrun
    cases k with
    | zero => rw [visitConstApp] at hrun; cases hrun
    | succ j =>
    rw [visitConstApp, withApp_mkAppN rfl] at hrun
    dsimp only at hrun
    rw [runPure_bind, show (liftM (Backend.casesInfo? (m := PureM) c) :
        EraseT PureM (Option CasesInfo)).runPure st tc ⟨decls, view⟩ ps = .ok ((none, st), ps) by
      show Except.ok ((casesInfo? decls c, st), ps) = _; rw [hcs], ok_bind'] at hrun
    dsimp only at hrun
    rw [runPure_bind, show (liftM (Backend.ctorArity? (m := PureM) c) :
        EraseT PureM (Option Nat)).runPure st tc ⟨decls, view⟩ ps =
          .ok ((some (cv.numParams + cv.numFields), st), ps) by
      show Except.ok ((ctorArity? decls c, st), ps) = _; rw [hca'], ok_bind'] at hrun
    dsimp only at hrun
    refine withAppEta_spec hG.closed ?_ hctx hR hsc hA hok hT hη hrun
    intro ρ₁ S₁ ls₁ Sc₁ ê₁ st₁ tc₁ ps₁ r₁ st₁' ps₁' as₁ hctx₁ hR₁ hsc₁ hargs₁ hle₁ hok₁ hs₁ hrun₁
    dsimp only at hrun₁
    cases hs₁ with
    | ctor _ _ hlen hall =>
      cases j with
      | zero => rw [visitConstructor] at hrun₁; cases hrun₁
      | succ i =>
      exact visitConstructor_spec hG (fun m hm => ih.expr m (by omega)) hctx₁ hsc₁ hR₁ hargs₁ hlen
        hall hc hle₁ hnprop hnat hok₁ hrun₁
    | casesProp h₁ | casesReduced h₁ | cases h₁ => simp [casesOnOf?, hcs] at h₁
    | quotMk _ h₂ | quotLift _ h₂ | recr _ h₂ => rw [hca'] at h₂; cases h₂
  | fvar | mdata | lam | letE | proj | litZero | litSucc => cases hfn

/-- The constructor step: an application or a constant whose head is a constructor and not a
recognized `casesOn` constant, through `visitApp_ctor`. Adapted from
`ML-V Core/StepsCtor.lean:1179`. Reference: the `tConstruct` case of `erases_erase`
(`MR E/ErasureFunction.v:1228`), rule `erases_tConstruct` (`MR E/Extract.v:106`); DV-23. -/
theorem visitExpr_ctor_step (hG : CoreEnv view cfg decls) (hcp : CtorPropBoxed view cfg decls)
    {fuel : Nat} (ih : StepIH view cfg decls fuel) {e : Expr} {c : Name} {us : List Level}
    {n : Nat} (hfn : e.getAppFn = .const c us) (hcs : casesInfo? decls c = none)
    (hca : ctorArity? decls c = some n) :
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
  exact visitApp_ctor hG hcp ⟨fun m hm => ih.expr m (by omega), fun m hm => ih.mutDecl m (by omega)⟩
    hfn hcs hca hctx hR he hsc hocc hnp hrs hok hm hor hrun

end

end Steps

end EraseProof
