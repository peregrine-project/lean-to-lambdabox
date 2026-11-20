import EraseProof.Core.ExistsSteps
import EraseProof.Core.StepsCasesSat

/-!
# The existence of the marking: recursor and `casesOn` spines

The steps of `ExistsSpec` (`Core/ExistsSteps.lean`) on a spine whose head is a recursor that
`visitRec` does not keep as a constant, or a recognized `casesOn`: `visitConstApp`
(`LeanToLambdaBox/Erasure.lean:966`) η-expands the spine to the head's arity
(`withAppEta_exists`, `MarkOf.special`, `MarkEta`), and the saturated spine is marked by the
branch the run takes (`MarkSat`):
* `visitRec` (`:1011`) visits the minor premises, the indices, the major premise and the
  arguments beyond the arity, after registering the block, which keeps the counter and the masks
  (`travMonoAt`) (`MarkSat.recr`, `exists_rec_step`);
* `visitCases` (`:1106`) returns `□` (`MarkSat.casesProp`), reduces the `case` on the only
  constructor (`MarkSat.casesReduced`), or visits the discriminant, each alternative under its
  constructor's fields (`visitAlt`, `:1263`, `MarkAlt`, `visitAlt_exists`) and the extra arguments
  (`MarkSat.cases`, `exists_cases_step`). The alternatives are collected by constructor name, so
  each one is visited because the constructors are distinct (`CoreEnvBase.ctorIdx`); none of them
  has an index field (`PhaseIDecl`), so no field value is substituted; the masks of the
  inductive keep every field and are as many as its constructors (`MasksOK`).

Reference: none (DV-32: the marking is the traversal's decisions written on the term; MetaRocq's
`erase` is a function, `MR E/ErasureFunction.v:989`); DV-23, DV-25, DV-30.
-/

open Lean Erasure

namespace EraseProof

namespace Steps

open RegisterInd OracleRen StateLemmas Decls

section
variable {decls : List ConstantInfo} {view : EnvView} {cfg : ErasureConfig}

/-- A list splits at any length up to its own. -/
theorem split_at {α : Type} {L : List α} {n : Nat} (h : n ≤ L.length) :
    ∃ l₁ l₂, L = l₁ ++ l₂ ∧ l₁.length = n :=
  ⟨L.take n, L.drop n, (List.take_append_drop n L).symm, List.length_take_of_le h⟩

/-- Markings of two lists from a marking of their concatenation. -/
theorem MarkList.split {ls : List Local} {as bs âs : List Expr}
    (h : MarkList decls cfg ls (as ++ bs) âs) :
    ∃ âs₁ âs₂, âs = âs₁ ++ âs₂ ∧ MarkList decls cfg ls as âs₁ ∧ MarkList decls cfg ls bs âs₂ := by
  obtain ⟨âs₁, âs₂, rfl, hl⟩ := split_at (L := âs) (n := as.length)
    (by rw [← h.1, List.length_append]; omega)
  have hl₂ : bs.length = âs₂.length := by have := h.1; simp only [List.length_append] at this; omega
  refine ⟨âs₁, âs₂, rfl, ⟨hl.symm, fun i a â h1 h2 => ?_⟩, ⟨hl₂, fun i a â h1 h2 => ?_⟩⟩
  · have hi := (List.getElem?_eq_some_iff.1 h1).1
    exact h.2 i a â (by rw [List.getElem?_append_left hi, h1])
      (by rw [List.getElem?_append_left (by omega), h2])
  · exact h.2 (as.length + i) a â (by rw [List.getElem?_append_right (by omega)]; simpa using h1)
      (by rw [List.getElem?_append_right (by omega)]; simpa [hl] using h2)

/-- `List.mapM (visitExpr j)` on renamed terms, from `ExistsSpec` at `j`: every term is visited,
each from a counter no smaller than the one before (`travMonoAt`), so each has a marking. -/
theorem mapM_exists {j : Nat} (ih : ∀ e, ExistsSpec view cfg decls j e) {ρ : FVarId → FVarId}
    {S : FVarId → Prop} {ls : List Local} {tc : TravCtx} (hctx : CtxOK cfg tc) :
    ∀ {as : List Expr} {ms : List LBTerm} {st st' : ErasureState} {ps ps' : PureState},
    RenOK ρ S ls tc.locals ps.next → (∀ a ∈ as, ExArgOK S cfg a) →
    MasksOK (evalEnvOf view cfg decls) st →
    ((as.map (renFV ρ)).mapM (visitExpr (m := PureM) j)).runPure st tc ⟨decls, view⟩ ps =
      .ok ((ms, st'), ps') →
    ∃ âs, MarkList decls cfg ls as âs
  | [], _, _, _, _, _, _, _, _, _ => ⟨[], rfl, fun _ _ _ h => nomatch h⟩
  | a :: l, ms, st, st', ps, ps', hR, hargs, hm, hrun => by
    rw [List.map_cons, List.mapM_cons, runPure_bind] at hrun
    obtain ⟨⟨⟨ta, st₁⟩, ps₁⟩, ha, hr1⟩ := ok_of_bind hrun
    rw [runPure_bind] at hr1
    obtain ⟨⟨⟨tl, st₂⟩, ps₂⟩, hl, -⟩ := ok_of_bind hr1
    obtain ⟨â, hâ⟩ := ih a hctx hR (hargs a (.head _)) hm ha
    have ⟨hn, hm'⟩ := (travMonoAt (σ := evalEnvOf view cfg decls) rfl j).expr _ _ _ _ _ _ _ ha
    obtain ⟨âl, hl'⟩ := mapM_exists ih hctx (hR.mono hn) (fun b hb => hargs b (.tail _ hb)) (hm' hm) hl
    exact ⟨â :: âl, MarkList.cons hâ hl'⟩

/-! ## Recursors -/

/-- The recursor step: a spine whose head is a recursor `rv` whose block the closure holds and that
`visitRec` does not keep as a constant (`recStaysConstant`), from `ExistsSpec` at the fuels up to
`fuel`: `visitConstApp` takes its recursor branch; `visitRec` reads the block (`recBlockOf?`) and
the shape of the minors (`recShape`), registers the block, which keeps the counter and the masks
(`travMonoAt`), and η-expands the spine to the recursor's arity (`withAppEta_exists`); the
saturated spine visits the minors, the indices and the major premise, whose sort the oracle
computes, and the arguments beyond the arity (`MarkSat.recr`). So the spine is marked by
`MarkOf.special`. Reference: none (DV-30). -/
theorem exists_rec_step (hcl : ClosedDecls decls = true) {fuel : Nat}
    (ih : ∀ m ≤ fuel, ∀ e, ExistsSpec view cfg decls m e) {e : Expr} {c : Name} {us : List Level}
    {rv : RecursorVal} {ivs : List InductiveVal} {cvs : List ConstructorVal}
    (hfn : e.getAppFn = .const c us) (hrv : findDecl decls c = some (.recInfo rv))
    (hblk : recBlockOf? decls rv = some (ivs, cvs))
    (hst : recStaysConstant cfg.nat rv ivs cvs = false) :
    ExistsSpec view cfg decls (fuel + 1) e := by
  obtain ⟨as, rfl⟩ := spine_of_getAppFn hfn
  obtain ⟨hcs, hca⟩ := rec_heads hrv
  have hma : markArity? decls cfg c =
      some (rv.numParams + rv.numMotives + rv.numMinors + rv.numIndices + 1) := by
    simp [markArity?, hcs, hca, hrv, hblk, hst]
  refine exists_appLike hcl (.inr ⟨c, us, rfl⟩) fun ρ S ls st tc ps r st' ps' hctx hR he hm hor
    hrun => ?_
  obtain ⟨-, hA⟩ := exArg_spine he
  rw [show renFV ρ (mkAppN (.const c us) as.toArray) = mkAppN (.const c us) (as.map (renFV ρ)).toArray
    from renFV_mkAppN ρ _ as] at hrun
  cases fuel with
  | zero => rw [visitApp] at hrun; cases hrun
  | succ k =>
  rw [visitApp] at hrun
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
      EraseT PureM (Option Nat)).runPure st tc ⟨decls, view⟩ ps = .ok ((none, st), ps) by
    show Except.ok ((ctorArity? decls c, st), ps) = _; rw [hca], ok_bind'] at hrun
  dsimp only at hrun
  rw [runPure_bind, show (liftM (Backend.findConst? (m := PureM) c) :
      EraseT PureM (Option ConstantInfo)).runPure st tc ⟨decls, view⟩ ps =
        .ok ((some (.recInfo rv), st), ps) by
    show Except.ok ((findConst decls c, st), ps) = _
    rw [show findConst decls c = findDecl decls c from rfl, hrv], ok_bind'] at hrun
  dsimp only at hrun
  cases j with
  | zero => rw [visitRec] at hrun; cases hrun
  | succ i =>
  rw [visitRec, runPure_bind] at hrun
  obtain ⟨⟨⟨ivs', st₁⟩, ps₁⟩, hivs0, hr1⟩ := ok_of_bind hrun
  obtain ⟨hivs, hs1, hp1⟩ := mapM_run_lookup (g := fun t => match findDecl decls t with
      | some (.inductInfo iv) => some iv
      | _ => none)
    (fun x st ps b st' ps' h => by
      rw [runPure_bind] at h
      obtain ⟨⟨⟨ci, st₁⟩, ps₁⟩, h1, h⟩ := ok_of_bind h
      obtain ⟨hci, rfl, rfl⟩ := getConst_run h1
      cases ci <;> try cases h
      refine ⟨?_, rfl, rfl⟩
      rw [show findDecl decls x = _ from hci]) _ hivs0
  subst st₁ ps₁
  dsimp only at hr1
  rw [runPure_bind] at hr1
  obtain ⟨⟨⟨cvs', st₂⟩, ps₂⟩, hcvs0, hr2⟩ := ok_of_bind hr1
  obtain ⟨hcvs, hs2, hp2⟩ := mapM_run_lookup (g := fun c => match findDecl decls c with
      | some (.ctorInfo cv) => some cv
      | _ => none)
    (fun x st ps b st' ps' h => by
      rw [runPure_bind] at h
      obtain ⟨⟨⟨ci, st₁⟩, ps₁⟩, h1, h⟩ := ok_of_bind h
      obtain ⟨hci, rfl, rfl⟩ := getConst_run h1
      cases ci <;> try cases h
      refine ⟨?_, rfl, rfl⟩
      rw [show findDecl decls x = _ from hci]) _ hcvs0
  subst st₂ ps₂
  dsimp only at hr2
  have hblk' : recBlockOf? decls rv = some (ivs', cvs') := by
    unfold recBlockOf?
    erw [hivs]
    simp only [Option.bind_eq_bind, Option.bind_some]
    erw [hcvs]
    rfl
  rw [hblk] at hblk'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hblk')
  rw [runPure_read_bind, hctx.config, hst] at hr2
  simp only [Bool.false_eq_true, ↓reduceIte] at hr2
  cases hsh : recShape rv.numParams rv.numMotives rv.type (cvs.map (·.numFields)) with
  | none => rw [hsh] at hr2; cases hr2
  | some mm =>
  obtain ⟨motives, minors⟩ := mm
  rw [hsh] at hr2
  dsimp only at hr2
  -- the block's registration keeps the counter and the masks
  rw [runPure_bind] at hr2
  obtain ⟨⟨⟨s3, st₃⟩, ps₃⟩, hloop, hr3⟩ := ok_of_bind hr2
  have hd : (⟨decls, view⟩ : PureCtx).decls = (evalEnvOf view cfg decls).decls := rfl
  obtain ⟨hn₃, hm₃⟩ := (by trav_mono : TravMono (evalEnvOf view cfg decls) ⟨decls, view⟩ _)
    _ _ _ _ _ _ hloop
  rw [runPure_bind] at hr3
  obtain ⟨⟨⟨jj, st₄⟩, ps₄⟩, hj0, hr4⟩ := ok_of_bind hr3
  obtain ⟨-, rfl, rfl⟩ := getOrFail_run hj0
  dsimp only at hr4
  obtain ⟨T, ê, hT, hη⟩ := withAppEta_exists hcl (fun ρ₁ S₁ ls₁ st₁ tc₁ ps₁ r₁ st₁' ps₁' as₁
      hctx₁ hR₁ hargs₁ hle₁ hm₁ hrun₁ => by
    -- the spine's parts
    obtain ⟨L₁, extra, rfl, hl₁⟩ := split_at hle₁
    obtain ⟨L₂, majs, rfl, hl₂⟩ := split_at (L := L₁)
      (n := rv.numParams + rv.numMotives + rv.numMinors + rv.numIndices)
      (by rw [hl₁]; omega)
    obtain ⟨maj, rfl⟩ : ∃ maj, majs = [maj] := by
      have : majs.length = 1 := by simp only [List.length_append] at hl₁; omega
      match majs, this with
      | [maj], _ => exact ⟨maj, rfl⟩
    obtain ⟨L₃, is, rfl, hl₃⟩ := split_at (L := L₂)
      (n := rv.numParams + rv.numMotives + rv.numMinors) (by rw [hl₂]; omega)
    obtain ⟨L₄, mins, rfl, hl₄⟩ := split_at (L := L₃) (n := rv.numParams + rv.numMotives)
      (by rw [hl₃]; omega)
    obtain ⟨ps₀, ms₀, rfl, hl₅⟩ := split_at (L := L₄) (n := rv.numParams) (by rw [hl₄]; omega)
    simp only [List.length_append] at hl₂ hl₃ hl₄
    have hlms : ms₀.length = rv.numMotives := by omega
    have hlmins : mins.length = rv.numMinors := by omega
    have hlis : is.length = rv.numIndices := by omega
    -- the major premise
    rw [runPure_bind] at hrun₁
    obtain ⟨⟨⟨mj, sa⟩, pa⟩, hg, hrun₁⟩ := ok_of_bind hrun₁
    obtain ⟨hmj, rfl, rfl⟩ := getOrFail_run hg
    have hmj' : mj = renFV ρ₁ maj := by
      have hl : (ps₀ ++ ms₀ ++ mins ++ is ++ [maj] ++ extra).map (renFV ρ₁) =
          (ps₀ ++ ms₀ ++ mins ++ is).map (renFV ρ₁) ++ ([renFV ρ₁ maj] ++ extra.map (renFV ρ₁)) := by
        simp
      rw [hl, show rv.numParams + rv.numMotives + rv.numMinors + rv.numIndices + 1 - 1 =
        ((ps₀ ++ ms₀ ++ mins ++ is).map (renFV ρ₁)).length by
          simp only [List.length_map, List.length_append, hl₅, hlms, hlmins, hlis] <;> omega,
        List.getElem?_toArray, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at hmj
      simpa using hmj.symm
    subst hmj'
    dsimp only at hrun₁
    rw [runPure_read_bind, runPure_read_bind, runPure_bind, runPure_liftM, typeLevel_run] at hrun₁
    rcases hTL : Pure.typeLevel ⟨decls⟩ oracleFuel tc₁.locals (renFV ρ₁ maj) with err | u
    · rw [hTL] at hrun₁; cases hrun₁
    rw [hTL] at hrun₁
    dsimp only [Except.map] at hrun₁
    rw [ok_bind', ok_bind'] at hrun₁
    dsimp only at hrun₁
    have hu : Pure.typeLevel ⟨decls⟩ oracleFuel ls₁ maj = .ok u := by
      rw [← Pure.typeLevel_ren (cx := ⟨decls⟩) hcl hR₁.supp hR₁.ren _ maj
        (hargs₁ maj (by simp)).1, hTL]
    -- the minor premises
    rw [runPure_bind] at hrun₁
    obtain ⟨⟨⟨ms', st₈⟩, ps₈⟩, hms, hrun₁⟩ := ok_of_bind hrun₁
    have hex1 : ((ps₀ ++ ms₀ ++ mins ++ is ++ [maj] ++ extra).map (renFV ρ₁)).toArray.extract
        (rv.numParams + rv.numMotives) (rv.numParams + rv.numMotives + rv.numMinors) =
        (mins.map (renFV ρ₁)).toArray := by
      have := extract_mid ((ps₀ ++ ms₀).map (renFV ρ₁)) (mins.map (renFV ρ₁))
        ((is ++ [maj] ++ extra).map (renFV ρ₁))
      simp only [List.length_map, List.length_append, hl₅, hlms, hlmins] at this
      simpa using this
    rw [hex1, List.toList_toArray] at hms
    dsimp only at hrun₁
    obtain ⟨minsM, hminsM⟩ := mapM_exists (ih i (by omega)) hctx₁ hR₁
      (fun a ha => hargs₁ a (by simp [ha])) hm₁ hms
    have ⟨hn₈, hm₈⟩ := TravMono.mapM (travMonoAt (σ := evalEnvOf view cfg decls) rfl i).expr _
      _ _ _ _ _ _ hms
    -- the indices and the major premise, then the arguments beyond the arity
    rw [runPure_bind] at hrun₁
    obtain ⟨⟨⟨app, st₉⟩, ps₉⟩, happ, hrun₁⟩ := ok_of_bind hrun₁
    have ⟨hn₉, hm₉⟩ := (travMonoAt (σ := evalEnvOf view cfg decls) rfl i).appArgs _ _
      _ _ _ _ _ _ happ
    cases i with
    | zero => rw [visitAppArgs] at happ; cases happ
    | succ i' =>
    have hex2 : ((ps₀ ++ ms₀ ++ mins ++ is ++ [maj] ++ extra).map (renFV ρ₁)).toArray.extract
        (rv.numParams + rv.numMotives + rv.numMinors)
        (rv.numParams + rv.numMotives + rv.numMinors + rv.numIndices + 1) =
        ((is ++ [maj]).map (renFV ρ₁)).toArray := by
      have := extract_mid ((ps₀ ++ ms₀ ++ mins).map (renFV ρ₁)) ((is ++ [maj]).map (renFV ρ₁))
        (extra.map (renFV ρ₁))
      simp only [List.length_map, List.length_append, List.length_singleton, hl₅, hlms,
        hlmins, hlis] at this
      simpa [Nat.add_assoc] using this
    rw [hex2] at happ
    obtain ⟨L, hL⟩ := visitAppArgs_exists (ih i' (by omega)) hctx₁ (hR₁.mono hn₈)
      (fun a ha => hargs₁ a (by simp at ha; rcases ha with ha | ha <;> simp [ha])) (hm₈ hm₁) happ
    obtain ⟨îs, majL, rfl, his, hmajL⟩ := MarkList.split hL
    obtain ⟨majM, rfl⟩ : ∃ majM, majL = [majM] := by
      match majL, hmajL.1 with
      | [majM], _ => exact ⟨majM, rfl⟩
    have hex3 : ((ps₀ ++ ms₀ ++ mins ++ is ++ [maj] ++ extra).map (renFV ρ₁)).toArray.extract
        (rv.numParams + rv.numMotives + rv.numMinors + rv.numIndices + 1) =
        (extra.map (renFV ρ₁)).toArray := by
      have := extract_tail ((ps₀ ++ ms₀ ++ mins ++ is ++ [maj]).map (renFV ρ₁))
        (extra.map (renFV ρ₁))
      simp only [List.length_map, List.length_append, List.length_singleton, hl₅, hlms,
        hlmins, hlis] at this
      simpa [Nat.add_assoc] using this
    dsimp only at hrun₁
    rw [hex3] at hrun₁
    obtain ⟨êxtra, hextra⟩ := visitAppArgs_exists (ih i' (by omega)) hctx₁
      (hR₁.mono (Nat.le_trans hn₈ hn₉)) (fun a ha => hargs₁ a (by simp [ha])) (hm₉ (hm₈ hm₁))
      hrun₁
    exact ⟨_, .recr hcs hca hrv hblk hst (by rw [hsh]; rfl) hl₅ hlms hlmins hlis ⟨u, hu⟩
      hminsM.1 hminsM.2 his.1 his.2 (hmajL.2 0 maj majM rfl rfl) hextra.1 hextra.2⟩)
    hctx (hR.mono hn₃) hA (hm₃ hm) hr4
  exact ⟨_, .special hor hma hT hη⟩

/-! ## `casesOn` alternatives -/

/-- `lambdaOrIntroToArity e T k K` at the pure backend on a renamed term `e` and its renamed type
`T`, given that a successful run of `K` on a renamed term has a marking of the term: each binder is
opened with the next variable of the counter at the leading `Π` that `forallView?` reads, which is
the renamed `Π` that `forallView?` reads on `T` (`forallView?_ren`), and to which a variable fresh
for the marking (`exists_fresh`) is renamed (`RenOK.push`); a λ is peeled (`MarkAlt.lam`), any
other term is applied to the variable (`MarkAlt.intro`), and at `0` the run of `K` gives the body's
marking (`MarkAlt.done`). Reference: none (DV-23). -/
theorem lambdaOrIntro_exists (hcl : ClosedDecls decls = true) {α : Type} [Inhabited α] :
    ∀ (k : Nat) {K : Expr → List FVarId → EraseT PureM α},
    (∀ ⦃ρ : FVarId → FVarId⦄ ⦃S : FVarId → Prop⦄ ⦃ls : List Local⦄ ⦃e : Expr⦄
        ⦃xs : List FVarId⦄ ⦃st : ErasureState⦄ ⦃tc : TravCtx⦄ ⦃ps : PureState⦄ ⦃a : α⦄
        ⦃st' : ErasureState⦄ ⦃ps' : PureState⦄,
      CtxOK cfg tc → RenOK ρ S ls tc.locals ps.next → ExArgOK S cfg e →
      MasksOK (evalEnvOf view cfg decls) st →
      (K (renFV ρ e) xs).runPure st tc ⟨decls, view⟩ ps = .ok ((a, st'), ps') →
      ∃ ê, MarkOf decls cfg ls e ê) →
    ∀ {ρ : FVarId → FVarId} {S : FVarId → Prop} {ls : List Local} {e T : Expr}
      {st st' : ErasureState} {tc : TravCtx} {ps ps' : PureState} {a : α},
      CtxOK cfg tc → RenOK ρ S ls tc.locals ps.next → ExArgOK S cfg e → FVarsIn S T →
      MasksOK (evalEnvOf view cfg decls) st →
      (lambdaOrIntroToArity (m := PureM) (renFV ρ e) (renFV ρ T) k K).runPure st tc
        ⟨decls, view⟩ ps = .ok ((a, st'), ps') →
      ∃ ê, MarkAlt decls cfg ls k e T ê := by
  intro k
  induction k with
  | zero =>
    intro K hK ρ S ls e T st st' tc ps ps' a hctx hR he _ hm hrun
    rw [lambdaOrIntroToArity] at hrun
    obtain ⟨ê, hê⟩ := hK hctx hR he hm hrun
    exact ⟨_, .done hê⟩
  | succ k ihk =>
    intro K hK ρ S ls e T st st' tc ps ps' a hctx hR he hT hm hrun
    rw [lambdaOrIntroToArity, lambdaMonocularOrIntro_eq] at hrun
    obtain ⟨y, D', C', bi, hv'⟩ := forallMonocular_inv hrun
    rw [(forallView?_ren hcl hR.supp hR.ren T hT).1] at hv'
    obtain ⟨⟨y₀, D, C, bi₀⟩, hv, hveq⟩ := Option.map_eq_some_iff.1 hv'
    cases hveq
    have hv'' : forallView? decls tc.locals (renFV ρ T) = some (y₀, renFV ρ D, renFV ρ C, bi₀) := by
      rw [(forallView?_ren hcl hR.supp hR.ren T hT).1, hv]; rfl
    rw [forallMonocular_run (pc := ⟨decls, view⟩) _ hv''] at hrun
    have ⟨hD, hC⟩ := fvarsIn_view hcl hR.supp hT hv
    have hK' : ∀ x', ∀ ⦃ρ : FVarId → FVarId⦄ ⦃S : FVarId → Prop⦄ ⦃ls : List Local⦄ ⦃e : Expr⦄
        ⦃xs : List FVarId⦄ ⦃st : ErasureState⦄ ⦃tc : TravCtx⦄ ⦃ps : PureState⦄ ⦃a : α⦄
        ⦃st' : ErasureState⦄ ⦃ps' : PureState⦄,
        CtxOK cfg tc → RenOK ρ S ls tc.locals ps.next → ExArgOK S cfg e →
        MasksOK (evalEnvOf view cfg decls) st →
        ((fun e xs => K e (x' :: xs)) (renFV ρ e) xs).runPure st tc ⟨decls, view⟩ ps =
          .ok ((a, st'), ps') →
        ∃ ê, MarkOf decls cfg ls e ê :=
      fun x' _ _ _ _ _ _ _ _ _ _ _ hctx hR he hm hrun => hK hctx hR he hm hrun
    by_cases hl : ∃ n A b bi', e = .lam n A b bi'
    · obtain ⟨n, A, b, bi', rfl⟩ := hl
      obtain ⟨x, hfr⟩ := exists_fresh ls [T, b]
      have hR' := hR.push (n := y₀) (val := none) hfr hD (fun _ h => nomatch h)
      have hxS := hR.not_mem hfr
      have hxb : FVarsIn (· ≠ x) b := hfr.2 b (by simp)
      have hxC : FVarsIn (· ≠ x) C := fvarsIn_mono (fun z hz (e : z = x) => hxS (e ▸ hz)) hC
      have hrenC : renFV (renExt ρ x (pureFVar ps.next)) (C.instantiate1' (.fvar x)) =
          (renFV ρ C).instantiate1' (.fvar (pureFVar ps.next)) := by
        rw [renFV_inst, renFV_congr (p := (· ≠ x)) (fun z hz => renExt_ne hz) hxC]
        simp only [renFV, renExt_self]
      have hrenb : renFV (renExt ρ x (pureFVar ps.next)) (b.instantiate1' (.fvar x)) =
          (renFV ρ b).instantiate1' (.fvar (pureFVar ps.next)) := by
        rw [renFV_inst, renFV_congr (p := (· ≠ x)) (fun z hz => renExt_ne hz) hxb]
        simp only [renFV, renExt_self]
      simp only [renFV, openAlt] at hrun
      rw [← hrenb, ← hrenC] at hrun
      obtain ⟨bM, hbM⟩ := ihk (hK' (pureFVar ps.next)) (by exact ⟨hctx.config, hctx.fixvars⟩)
        (by exact hR') ⟨fvarsIn_open he.1.2, NatPlain.inst_fvar he.2.1.2, NoStrLit.inst_fvar he.2.2.2⟩
        (fvarsIn_open hC) hm hrun
      exact ⟨_, .lam hv hfr hbM⟩
    · have hne : ∀ n A b bi', e ≠ .lam n A b bi' := fun n A b bi' h => hl ⟨n, A, b, bi', h⟩
      obtain ⟨x, hfr⟩ := exists_fresh ls [T, e]
      have hR' := hR.push (n := y₀) (val := none) hfr hD (fun _ h => nomatch h)
      have hxS := hR.not_mem hfr
      have hxe : FVarsIn (· ≠ x) e := hfr.2 e (by simp)
      have hxC : FVarsIn (· ≠ x) C := fvarsIn_mono (fun z hz (e : z = x) => hxS (e ▸ hz)) hC
      have hrenC : renFV (renExt ρ x (pureFVar ps.next)) (C.instantiate1' (.fvar x)) =
          (renFV ρ C).instantiate1' (.fvar (pureFVar ps.next)) := by
        rw [renFV_inst, renFV_congr (p := (· ≠ x)) (fun z hz => renExt_ne hz) hxC]
        simp only [renFV, renExt_self]
      have hren : renFV (renExt ρ x (pureFVar ps.next)) (.app e (.fvar x)) =
          openAlt (renFV ρ e) (pureFVar ps.next) := by
        simp only [renFV, renExt_self, renFV_congr (p := (· ≠ x)) (fun z hz => renExt_ne hz) hxe]
        cases e with
        | lam n A b bi => exact absurd rfl (hne n A b bi)
        | _ => rfl
      rw [← hren, ← hrenC] at hrun
      have he₁ : ExArgOK (fun z => S z ∨ z = x) cfg (.app e (.fvar x)) :=
        ⟨⟨fvarsIn_mono (fun _ => .inl) he.1, .inr rfl⟩, ⟨he.2.1, trivial⟩, ⟨he.2.2, trivial⟩⟩
      obtain ⟨bM, hbM⟩ := ihk (hK' (pureFVar ps.next)) (by exact ⟨hctx.config, hctx.fixvars⟩)
        (by exact hR') he₁ (fvarsIn_open hC) hm hrun
      exact ⟨_, .intro hne hv hfr hbM⟩

/-- `visitAlt (j + 1) k mask [] alt` at the pure backend on a renamed alternative, with no
substituted field, from `ExistsSpec` at `j`: the oracle types the alternative (its type on the
renamed alternative is the renamed type, `inferType_ren`), and the binders are opened up to `k`
(`lambdaOrIntro_exists`) around the visited body, so the alternative has a marking `MarkAlt` on
that type. Reference: none (DV-23). -/
theorem visitAlt_exists (hcl : ClosedDecls decls = true) {j : Nat}
    (ih : ∀ e, ExistsSpec view cfg decls j e) {ρ : FVarId → FVarId} {S : FVarId → Prop}
    {ls : List Local} {st st' : ErasureState} {tc : TravCtx} {ps ps' : PureState} {k : Nat}
    {mask : ConstructorArgMask} {alt : Expr} {br : List BinderName × LBTerm}
    (hctx : CtxOK cfg tc) (hR : RenOK ρ S ls tc.locals ps.next) (ha : ExArgOK S cfg alt)
    (hm : MasksOK (evalEnvOf view cfg decls) st)
    (hrun : (visitAlt (m := PureM) (j + 1) k mask [] (renFV ρ alt)).runPure st tc ⟨decls, view⟩
      ps = .ok ((br, st'), ps')) :
    ∃ T âlt, Pure.inferType ⟨decls⟩ oracleFuel ls [] alt = .ok T ∧
      MarkAlt decls cfg ls k alt T âlt := by
  have hT' := (inferType_ren (cx := ⟨decls⟩) hcl hR.supp hR.ren oracleFuel [] _ ha.1 (by simp)).1
  rw [visitAlt, runPure_read_bind, runPure_read_bind, runPure_bind, inferType_runPure] at hrun
  erw [hT'] at hrun
  cases hT : Pure.inferType ⟨decls⟩ oracleFuel ls [] alt with
  | error err => rw [hT] at hrun; cases hrun
  | ok T =>
    rw [hT] at hrun
    dsimp only [Except.map] at hrun
    rw [ok_bind'] at hrun
    dsimp only at hrun
    obtain ⟨âlt, h⟩ := lambdaOrIntro_exists hcl k (fun ρ' S' ls' e' xs st₁ tc' ps₁ a st₁' ps₁'
        hctx' hR' he' hm' hrun' => by
      simp only [List.isEmpty_nil, ↓reduceIte] at hrun'
      rw [runPure_bind] at hrun'
      obtain ⟨⟨⟨r, st₂⟩, ps₂⟩, hr, -⟩ := ok_of_bind hrun'
      exact ih e' hctx' hR' he' hm' hr) hctx hR ha (fvarsIn_oracle_ty hcl hR.supp ha.1 hT) hm hrun
    exact ⟨T, âlt, rfl, h⟩

/-- `visitCasesOn (f + 1) iv m ∅ none d` at the pure backend, from `ExistsSpec` below `f`, when the
map `m` gives each constructor of `iv` its number of fields and its renamed alternative and the
machine branches are not taken: registering `iv` keeps the counter and gives masks that keep every
field, one per constructor (`register_inductive_masks`, `MasksOK`), so the loop over the
constructors and their masks visits every alternative (`visitAlt_exists`), each of which has a
marking `MarkAlt` on the type the oracle infers for it. Reference: none (DV-23). -/
theorem visitCasesOn_exists (hcl : ClosedDecls decls = true) {f : Nat}
    (ih : ∀ j < f, ∀ e, ExistsSpec view cfg decls j e) {iv : InductiveVal}
    (hiv : findDecl decls iv.name = some (.inductInfo iv))
    (hnm : cfg.nat = .machine → iv.name ≠ ``Nat ∧ iv.name ≠ ``Int)
    {m : Std.HashMap Name (Nat × Expr)} {ρ : FVarId → FVarId} {S : FVarId → Prop}
    {ls : List Local} {alts : List Expr} {st st' : ErasureState} {tc : TravCtx}
    {ps ps' : PureState} {d r : LBTerm}
    (hmap : ∀ (i : Nat) cn, iv.ctors[i]? = some cn → ∃ cv alt,
      findDecl decls cn = some (.ctorInfo cv) ∧ alts[i]? = some alt ∧
      m[cn]? = some (cv.numFields, renFV ρ alt))
    (halts : ∀ alt ∈ alts, ExArgOK S cfg alt) (hctx : CtxOK cfg tc)
    (hR : RenOK ρ S ls tc.locals ps.next) (hm : MasksOK (evalEnvOf view cfg decls) st)
    (hrun : (visitCasesOn (m := PureM) (f + 1) iv m ∅ none d).runPure st tc ⟨decls, view⟩ ps =
      .ok ((r, st'), ps')) :
    ∃ âlts : List Expr, âlts.length = iv.ctors.length ∧
      ∀ (i : Nat) cn cv alt âlt, iv.ctors[i]? = some cn → findDecl decls cn = some (.ctorInfo cv) →
        alts[i]? = some alt → âlts[i]? = some âlt →
        ∃ T, Pure.inferType ⟨decls⟩ oracleFuel ls [] alt = .ok T ∧
          MarkAlt decls cfg ls cv.numFields alt T âlt := by
  rw [visitCasesOn, runPure_bind, runPure_pure, ok_bind'] at hrun
  dsimp only at hrun
  rw [runPure_read_bind] at hrun
  split at hrun
  · rename_i h1 h2
    exact ((hnm (by rw [← hctx.config]; exact h2)).1 h1).elim
  · rename_i h1 h2
    exact ((hnm (by rw [← hctx.config]; exact h2)).2 h1).elim
  rw [runPure_bind] at hrun
  obtain ⟨⟨⟨⟨indid, argmasks⟩, st₂⟩, ps₂⟩, hreg, hrun₂⟩ := ok_of_bind hrun
  clear hrun
  obtain ⟨hm₂, hin⟩ := register_inductive_masks (σ := evalEnvOf view cfg decls) rfl iv tc st ps _
    st₂ ps₂ hm hreg
  have hps := KeepsPS.register_inductive iv _ _ _ _ _ _ hreg
  subst ps₂
  obtain ⟨iv₂, hiv₂, hkm⟩ := hm₂ iv.name _ hin
  have hiv₂' : findDecl decls iv.name = some (.inductInfo iv₂) := hiv₂
  rw [hiv] at hiv₂'
  cases hiv₂'
  dsimp only at hrun₂
  rw [runPure_bind] at hrun₂
  obtain ⟨⟨⟨⟨brs, s'⟩, st₃⟩, ps₃⟩, hloop, -⟩ := ok_of_bind hrun₂
  have hI := forIn_inv (tc := tc) (pc := ⟨decls, view⟩) (L := iv.ctors)
    (fun pre (b : Array (List BinderName × LBTerm) × List ConstructorArgMask) st₁ ps₁ =>
      b.2 = argmasks.drop pre.length ∧ ps.next ≤ ps₁.next ∧
      MasksOK (evalEnvOf view cfg decls) st₁ ∧
      ∃ âlts : List Expr, âlts.length = pre.length ∧
        ∀ (i : Nat) cn cv alt âlt, iv.ctors[i]? = some cn →
          findDecl decls cn = some (.ctorInfo cv) → alts[i]? = some alt → âlts[i]? = some âlt →
          ∃ T, Pure.inferType ⟨decls⟩ oracleFuel ls [] alt = .ok T ∧
            MarkAlt decls cfg ls cv.numFields alt T âlt) _ ?_ iv.ctors [] (#[], argmasks)
    st₂ ps _ _ _ rfl ⟨rfl, Nat.le_refl _, hm₂, [], rfl, fun _ _ _ _ _ _ _ _ h => nomatch h⟩ hloop
  · exact hI.2.2.2
  · intro pre cn rest ⟨as₁, s₁⟩ st₁ ps₁ res st₁' ps₁' hL ⟨hs, hn₁, hm₁, âlts, hlen, hE⟩ hb
    dsimp only at hs hb
    have hk : pre.length < iv.ctors.length := by rw [← hL]; simp
    have hcn : iv.ctors[pre.length]? = some cn := by rw [← hL]; simp
    obtain ⟨cv, alt, hcv, halt, hmc⟩ := hmap _ _ hcn
    have hmask := hkm.2 pre.length cn cv hcn hcv
    rw [hs, List.drop_eq_getElem_cons (by rw [hkm.1]; exact hk),
      (List.getElem?_eq_some_iff.1 hmask).2] at hb
    simp only [show ∀ (a : ConstructorArgMask) (l : List ConstructorArgMask),
      Std.Stream.next? (a :: l) = some (a, l) from fun _ _ => rfl, hmc,
      Std.HashMap.getD_empty] at hb
    rw [runPure_bind] at hb
    obtain ⟨⟨⟨br, st₄⟩, ps₄⟩, hvis, hb⟩ := ok_of_bind hb
    cases hb
    have ⟨hn₄, hm₄⟩ := (travMonoAt (σ := evalEnvOf view cfg decls) rfl f).alt _ _ _ _
      _ _ _ _ _ _ hvis
    cases f with
    | zero => rw [visitAlt] at hvis; cases hvis
    | succ f =>
    obtain ⟨T, âlt, hT, hma⟩ := visitAlt_exists hcl (ih f (by omega)) hctx (hR.mono hn₁)
      (halts alt (List.mem_of_getElem? halt)) hm₁ hvis
    refine ⟨_, rfl, by simp, Nat.le_trans hn₁ hn₄, hm₄ hm₁, âlts ++ [âlt], by simp [hlen],
      fun i cn' cv' alt' âlt' hi hcv' ha hâ => ?_⟩
    rcases Nat.lt_or_ge i pre.length with hlt | hge
    · rw [List.getElem?_append_left (by omega)] at hâ
      exact hE i cn' cv' alt' âlt' hi hcv' ha hâ
    · rw [List.getElem?_append_right (by omega)] at hâ
      obtain ⟨hi0, rfl⟩ := List.getElem?_eq_some_iff.1 hâ
      simp only [List.length_singleton] at hi0
      obtain rfl : i = pre.length := by omega
      rw [hcn] at hi; cases hi
      rw [hcv] at hcv'; cases hcv'
      rw [halt] at ha; cases ha
      exact ⟨T, hT, by simpa using hma⟩

end

section
variable {decls : List ConstantInfo} {view : EnvView} {cfg : ErasureConfig}

/-- `visitCases j ci`, the continuation of `withAppEtaToMinArity` for a recognized `casesOn` `c`
(`visitConstApp`, `LeanToLambdaBox/Erasure.lean:966`), on saturated spines (`ExSatSpec`), from
`ExistsSpec` at the fuels up to `j`: a `casesOn` with as many universe parameters as its inductive
is marked `□` (`MarkSat.casesProp`); otherwise the oracle's level of the discriminant's type is
computed and the alternatives are collected by constructor name, each one under its own
constructor since the constructors are distinct (`ctors_inj`); no field value is substituted,
since no constructor has an index field (`PhaseIDecl`); the `case` on the only constructor is
reduced (`MarkSat.casesReduced`: the alternative and the extra arguments are visited) or the
discriminant, the alternatives (`visitCasesOn_exists`) and the extra arguments are visited
(`MarkSat.cases`). Reference: none (DV-25). -/
theorem visitCases_exists (hB : CoreEnvBase view cfg decls) {j : Nat}
    (ih : ∀ m ≤ j, ∀ e, ExistsSpec view cfg decls m e) {c : Name} {us : List Level}
    {ci : CasesInfo} (hci : casesInfo? decls c = some ci)
    (hnm : cfg.nat = .machine → c ≠ ``Nat.casesOn ∧ c ≠ ``Int.casesOn) :
    ExSatSpec view cfg decls ci.arity c us (fun _ args => visitCases (m := PureM) j ci args) := by
  intro ρ S ls st tc ps r st' ps' as hctx hR hargs hle hm hrun
  dsimp only at hrun
  obtain ⟨iv, cd, calts, hiv, hd, hdn, hcname, har, hdp, hca, hanp, hrange⟩ :=
    casesInfo?_facts hci
  have hco : casesOnOf? decls c = some iv := by simp [casesOnOf?, hci, hiv]
  by_cases hlp : cd.levelParams.length = iv.levelParams.length
  · exact ⟨_, .casesProp hco hd hlp⟩
  obtain ⟨hlena, haltsg⟩ := ctorAlts_get hca
  have hname : iv.name = ci.indName := (findDecl_eq_some hiv).2
  obtain ⟨-, -, -, hixf⟩ := hB.phase _ (findDecl_eq_some hiv).1
  have hidxf : ∀ cn ∈ iv.ctors, ∀ cv, findDecl decls cn = some (.ctorInfo cv) →
      (indexFields cv.numParams cv.type).all (·.isNone) = true :=
    hixf (by rw [hname, ← hcname, hco]; rfl)
  have hnm' : cfg.nat = .machine → iv.name ≠ ``Nat ∧ iv.name ≠ ``Int := fun hm' =>
    ⟨fun h => (hnm hm').1 (by rw [hcname, ← hname, h]),
      fun h => (hnm hm').2 (by rw [hcname, ← hname, h])⟩
  -- the spine's parts
  rw [har] at hle
  obtain ⟨L, extra, rfl, hlL⟩ := split_at hle
  obtain ⟨L', alts, rfl, hlL'⟩ := split_at (L := L) (n := casesMajor iv + 1)
    (by rw [hlL]; simp only [casesArity]; omega)
  obtain ⟨pre, ds, rfl, hpre⟩ := split_at (L := L') (n := casesMajor iv) (by rw [hlL']; omega)
  obtain ⟨d, rfl⟩ : ∃ d, ds = [d] := by
    have : ds.length = 1 := by simp only [List.length_append] at hlL'; omega
    match ds, this with
    | [d], _ => exact ⟨d, rfl⟩
  have hac : alts.length = iv.ctors.length := by
    simp only [List.length_append, List.length_singleton, casesArity] at hlL; omega
  cases j with
  | zero => rw [visitCases] at hrun; cases hrun
  | succ j =>
  obtain ⟨hgd, hgl, hgx⟩ := spine_get ρ pre alts extra d
  generalize hA : (pre ++ [d] ++ alts ++ extra).map (renFV ρ) = A at hrun hgd hgl hgx
  have hAlen : A.length = casesArity iv + extra.length := by
    rw [← hA]; simp [casesArity, hpre, hac]; omega
  have hsat : ci.arity ≤ A.length := by rw [hAlen, har]; omega
  rw [visitCases, runPure_bind, getOrFail_of (by rw [hdp, ← hpre]; exact hgd), ok_bind'] at hrun
  dsimp only at hrun
  rw [runPure_bind, getConst_ok (pc := ⟨decls, view⟩) (show findConst decls _ = _ from hiv),
    ok_bind'] at hrun
  dsimp only at hrun
  rw [runPure_bind, hdn, getConst_ok (pc := ⟨decls, view⟩) (show findConst decls _ = _ from hd),
    ok_bind'] at hrun
  dsimp only at hrun
  simp only [show (cd.levelParams.length == iv.levelParams.length) = false by simpa using hlp,
    Bool.false_eq_true, ↓reduceIte] at hrun
  rw [runPure_read_bind, runPure_read_bind, runPure_bind, runPure_liftM, typeLevel_run] at hrun
  rcases hTL : Pure.typeLevel ⟨decls⟩ oracleFuel tc.locals (renFV ρ d) with err | u
  · rw [hTL] at hrun; cases hrun
  rw [hTL] at hrun
  dsimp only [Except.map] at hrun
  rw [ok_bind', ok_bind'] at hrun
  dsimp only at hrun
  have hu : Pure.typeLevel ⟨decls⟩ oracleFuel ls d = .ok u := by
    rw [← Pure.typeLevel_ren (cx := ⟨decls⟩) hB.closed hR.supp hR.ren _ d
      (hargs d (by simp)).1, hTL]
  -- the alternatives, by constructor name
  rw [hanp, hrange, runPure_bind, rco_forIn] at hrun
  obtain ⟨⟨⟨⟨mp, ca, s₀⟩, st₁⟩, ps₁⟩, hloop, hrun⟩ := ok_of_bind hrun
  have hLlen : (casesMajor iv + 1...casesArity iv).toList.length = calts.length := by
    rw [Nat.length_toList_rco, hlena]; simp [casesArity]
  have hI := forIn_inv (tc := tc) (pc := ⟨decls, view⟩)
    (L := (casesMajor iv + 1...casesArity iv).toList)
    (fun pl (b : Std.HashMap Name (Nat × Expr) × Option (Nat × Expr) × Subarray CasesAltInfo)
        st₂ ps₂ => st₂ = st ∧ ps₂ = ps ∧ b.2.1 = none ∧ b.2.2.array = calts.toArray ∧
      b.2.2.start = pl.length ∧ b.2.2.stop = calts.length ∧
      ∀ i < pl.length, ∀ cn, iv.ctors[i]? = some cn → ∃ cv a,
        findConst decls cn = some (.ctorInfo cv) ∧ A[casesMajor iv + 1 + i]? = some a ∧
        b.1[cn]? = some (cv.numFields, a)) _ ?_ _ [] _ st ps _ _ _ rfl
    ⟨rfl, rfl, rfl, by simp [Std.toStream], by simp [Std.toStream], by simp [Std.toStream],
      fun i hi => by simp at hi⟩ hloop
  rotate_left
  · intro pl i rest ⟨mp, ca, s⟩ st₂ ps₂ res st₃ ps₃ hL ⟨hst, hps, hca', harr, hstart, hstop, hmap⟩ hb
    dsimp only at hst hps hca' harr hstart hstop hmap hb
    subst hst hps
    have hk : pl.length < calts.length := by
      rw [← hLlen, ← hL]; simp
    have hi : i = casesMajor iv + 1 + pl.length := by
      have h1 : (casesMajor iv + 1...casesArity iv).toList[pl.length]? = some i := by
        rw [← hL]; simp
      rw [Nat.getElem?_toList_rco] at h1
      split at h1
      · cases h1; rfl
      · cases h1
    subst hi
    obtain ⟨cn, hcn⟩ : ∃ cn, iv.ctors[pl.length]? = some cn :=
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
    have hbd : casesMajor iv + 1 + pl.length < A.length := by
      rw [hAlen]; simp only [casesArity]; rw [hlena] at hk; omega
    have has : A.toArray[casesMajor iv + 1 + pl.length]? =
        some (A[casesMajor iv + 1 + pl.length]'hbd) := by
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
          have := ctors_inj hB hiv hcn hcn'
          omega
        · exact h'
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      exact hmap i' hlt' cn' hcn'
    · have : i' = pl.length := by omega
      subst this
      rw [hcn] at hcn'
      cases hcn'
      exact ⟨cv, _, hcv, List.getElem?_eq_getElem hbd, by simp⟩
  obtain ⟨hst₁, hps₁, rfl, -, -, -, hmap⟩ := hI
  subst st₁ ps₁
  dsimp only at hmap hrun
  -- no index is substituted
  have hctorc : ∀ cn ∈ iv.ctors, ∃ cv, findConst decls cn = some (.ctorInfo cv) := by
    intro cn hcn
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hcn
    obtain ⟨cv, hcv, -⟩ := haltsg _ _ hi
    exact ⟨cv, hcv⟩
  by_cases hni : (!u.isNeverZero && decide (iv.numIndices > 0)) = true
  all_goals first
    | (rw [ite_eq_right_of_eq_false _ _ (eq_false hni)] at hrun)
    | (rw [ite_eq_left_of_eq_true _ _ (eq_true hni), runPure_bind] at hrun
       obtain ⟨⟨⟨idx, st₂⟩, ps₂⟩, hloop₂, hrun⟩ := ok_of_bind hrun
       obtain ⟨rfl, hs₂, hp₂⟩ := forIn_inv (tc := tc) (pc := ⟨decls, view⟩) (L := iv.ctors)
         (fun _ (b : Std.HashMap Name (List (Option Expr))) st₂ ps₂ => b = ∅ ∧ st₂ = st ∧ ps₂ = ps)
         _ (fun pl cn rest b st₂ ps₂ res st₃ ps₃ hL ⟨hb, hs, hp⟩ hrb => by
           subst hb hs hp
           have hcn : cn ∈ iv.ctors := by rw [← hL]; simp
           obtain ⟨cv, hcv⟩ := hctorc cn hcn
           rw [runPure_bind, getConst_ok (pc := ⟨decls, view⟩) hcv, ok_bind'] at hrb
           dsimp only at hrb
           have hcv' : findDecl decls cn = some (.ctorInfo cv) := hcv
           rw [ite_eq_left_of_eq_true _ _ (eq_true (by
             rw [← ctor_numParams hB hiv hcn hcv']; exact hidxf cn hcn cv hcv'))] at hrb
           cases hrb
           exact ⟨_, rfl, rfl, rfl, rfl⟩) _ [] ∅ st ps _ _ _ rfl ⟨rfl, rfl, rfl⟩ hloop₂
       subst hs₂ hp₂)
  all_goals
  try dsimp only at hrun
  by_cases hred : (!u.isNeverZero && iv.numCtors == 1) = true
  · -- the reduced `case`
    have hz : u.isNeverZero = false := by
      cases h : u.isNeverZero
      · rfl
      · rw [h] at hred; simp at hred
    have hnc : iv.ctors.length = 1 := by
      simpa [InductiveVal.numCtors, hz] using hred
    obtain ⟨cn, hcn⟩ := List.length_eq_one_iff.1 hnc
    obtain ⟨alt, rfl⟩ : ∃ alt, alts = [alt] := by
      rw [hnc] at hac
      match alts, hac with
      | [alt], _ => exact ⟨alt, rfl⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true hred), runPure_bind,
      getOrFail_of (show iv.ctors[0]? = some cn by rw [hcn]; rfl), ok_bind'] at hrun
    dsimp only at hrun
    obtain ⟨cv, a, hcv, ha, hma⟩ := hmap 0 (by rw [hLlen, hlena, hcn]; simp) cn (by rw [hcn]; rfl)
    have ha' := hgl 0 (by simp)
    rw [List.getElem?_toArray, List.getElem?_cons_zero, Option.map_some] at ha'
    rw [← hpre, ha'] at ha
    cases ha
    simp only [hma, Std.HashMap.getElem?_empty] at hrun
    rw [runPure_bind] at hrun
    obtain ⟨⟨⟨alt_nt, st₃⟩, ps₃⟩, halt_run, hrun⟩ := ok_of_bind hrun
    rw [runPure_bind, runPure_pure, ok_bind'] at hrun
    dsimp only at hrun
    obtain ⟨âlt, hâlt⟩ := ih j (by omega) alt hctx hR (hargs alt (by simp)) hm halt_run
    have ⟨hn₃, hm₃⟩ := (travMonoAt (σ := evalEnvOf view cfg decls) rfl j).expr _ _ _ _ _ _ _
      halt_run
    cases j with
    | zero => rw [visitAppArgs] at hrun; cases hrun
    | succ i =>
    rw [(slice_drop (n := ci.arity) hsat).1,
      show ci.arity = pre.length + 1 + [alt].length by rw [har, casesArity, hpre, hnc]; rfl,
      hgx] at hrun
    obtain ⟨êxtra, hextra⟩ := visitAppArgs_exists (ih i (by omega)) hctx (hR.mono hn₃)
      (fun a ha => hargs a (by simp [ha])) (hm₃ hm) hrun
    exact ⟨_, .casesReduced hco hd hlp hpre hu hz hcn hcv
      (hidxf cn (by rw [hcn]; simp) cv hcv) hâlt hextra.1 hextra.2⟩
  · -- the λ□ `case`
    rw [ite_eq_right_of_eq_false _ _ (eq_false hred), runPure_bind] at hrun
    obtain ⟨⟨⟨dnt, st₂⟩, ps₂⟩, hdrun, hrun⟩ := ok_of_bind hrun
    have hall : (iv.ctors.all fun x => mp.contains x) = true := by
      rw [List.all_eq_true]
      intro cn hcn
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hcn
      obtain ⟨cv, a, -, -, hma⟩ :=
        hmap i (by rw [hLlen, hlena]; exact (List.getElem?_eq_some_iff.1 hi).1) cn hi
      simp [Std.HashMap.contains_iff_mem, Std.HashMap.mem_iff_isSome_getElem?, hma]
    rw [ite_eq_left_of_eq_true _ _ (eq_true hall), runPure_bind] at hrun
    obtain ⟨⟨⟨ret, st₃⟩, ps₃⟩, hcrun, hrun⟩ := ok_of_bind hrun
    dsimp only at hcrun hrun
    obtain ⟨dM, hdM⟩ := ih j (by omega) d hctx hR (hargs d (by simp)) hm hdrun
    have ⟨hn₂, hm₂⟩ := (travMonoAt (σ := evalEnvOf view cfg decls) rfl j).expr _ _ _ _ _ _ _
      hdrun
    cases j with
    | zero => rw [visitExpr] at hdrun; cases hdrun
    | succ f =>
    obtain ⟨âlts, hlâ, hE⟩ := visitCasesOn_exists (alts := alts) hB.closed
      (fun j' hj' => ih j' (by omega)) (by rw [hname]; exact hiv) hnm' (fun i cn hcn => by
        have hil : i < iv.ctors.length := (List.getElem?_eq_some_iff.1 hcn).1
        obtain ⟨cv, a, hcv, ha, hma⟩ := hmap i (by rw [hLlen, hlena]; exact hil) cn hcn
        obtain ⟨alt, halt⟩ : ∃ alt, alts[i]? = some alt :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        have hga := hgl i (by omega)
        rw [List.getElem?_toArray, halt, Option.map_some] at hga
        rw [← hpre, hga] at ha
        cases ha
        exact ⟨cv, alt, hcv, halt, hma⟩)
      (fun alt halt => hargs alt (by simp [halt])) hctx (hR.mono hn₂) (hm₂ hm) hcrun
    have ⟨hn₃, hm₃⟩ := (travMonoAt (σ := evalEnvOf view cfg decls) rfl (f + 1)).caseOf _ _ _ _ _
      _ _ _ _ _ _ hcrun
    -- the extra arguments
    have hAr : ci.arity = pre.length + 1 + alts.length := by
      rw [har, casesArity, hpre, hac]
    rw [subarray_forIn, (slice_drop hsat).2, hAr, hgx, runPure_bind] at hrun
    obtain ⟨⟨⟨ret', st₄⟩, ps₄⟩, hext, -⟩ := ok_of_bind hrun
    rw [forIn_app_eq] at hext
    obtain ⟨êxtra, hextra⟩ := visitAppArgs_exists (ih (f + 1) (by omega)) hctx
      (hR.mono (Nat.le_trans hn₂ hn₃)) (fun a ha => hargs a (by simp [ha])) (hm₃ (hm₂ hm)) hext
    refine ⟨_, .cases hco hd hlp hpre hac hu (fun hz => ⟨fun h1 => hred ?_, hidxf⟩) hdM
      (hac.trans hlâ.symm) (fun i cn hcn => ?_) (fun i alt halt => ?_)
      (fun i cn cv alt âlt T hcn hcv halt hâlt hT => ?_) hextra.1 hextra.2⟩
    · simp [InductiveVal.numCtors, hz, h1]
    · obtain ⟨cv, hcv, -⟩ := haltsg i cn hcn
      exact ⟨cv, hcv⟩
    · have hi : i < iv.ctors.length := hac ▸ (List.getElem?_eq_some_iff.1 halt).1
      obtain ⟨cn, hcn⟩ : ∃ cn, iv.ctors[i]? = some cn := ⟨_, List.getElem?_eq_getElem hi⟩
      obtain ⟨cv, hcv, -⟩ := haltsg i cn hcn
      obtain ⟨âlt, hâlt⟩ : ∃ âlt, âlts[i]? = some âlt :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨T, hT, -⟩ := hE i cn cv alt âlt hcn hcv halt hâlt
      exact ⟨T, hT⟩
    · obtain ⟨T', hT', hma⟩ := hE i cn cv alt âlt hcn hcv halt hâlt
      rw [hT] at hT'
      cases hT'
      exact hma

/-- The `casesOn` step: a spine whose head is a recognized `casesOn`, from `ExistsSpec` at the
fuels up to `fuel`: `visitConstApp` takes its `casesOn` branch, the η-expansion gives `MarkEta`
(`withAppEta_exists`) and `visitCases` marks the saturated spine (`visitCases_exists`), so the
spine is marked by `MarkOf.special`. The head is no `Nat.casesOn`/`Int.casesOn` under
`nat := .machine` (`NatPlain`). Reference: none (DV-23, DV-25). -/
theorem exists_cases_step (hB : CoreEnvBase view cfg decls) {fuel : Nat}
    (ih : ∀ m ≤ fuel, ∀ e, ExistsSpec view cfg decls m e) {e : Expr} {c : Name} {us : List Level}
    {ci : CasesInfo} (hfn : e.getAppFn = .const c us) (hci : casesInfo? decls c = some ci) :
    ExistsSpec view cfg decls (fuel + 1) e := by
  obtain ⟨as, rfl⟩ := spine_of_getAppFn hfn
  have hma : markArity? decls cfg c = some ci.arity := by simp [markArity?, hci]
  refine exists_appLike hB.closed (.inr ⟨c, us, rfl⟩) fun ρ S ls st tc ps r st' ps' hctx hR he hm
    hor hrun => ?_
  obtain ⟨⟨-, hnc, -⟩, hA⟩ := exArg_spine he
  have hnc' : cfg.nat = .machine → c ∉ [``Nat.zero, ``Nat.succ, ``Int.ofNat, ``Int.negSucc,
      ``Nat.casesOn, ``Int.casesOn] := hnc
  have hnm : cfg.nat = .machine → c ≠ ``Nat.casesOn ∧ c ≠ ``Int.casesOn := fun h =>
    ⟨fun e => hnc' h (by rw [e]; simp), fun e => hnc' h (by rw [e]; simp)⟩
  rw [show renFV ρ (mkAppN (.const c us) as.toArray) = mkAppN (.const c us) (as.map (renFV ρ)).toArray
    from renFV_mkAppN ρ _ as] at hrun
  cases fuel with
  | zero => rw [visitApp] at hrun; cases hrun
  | succ k =>
  rw [visitApp] at hrun
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
  obtain ⟨T, ê, hT, hη⟩ := withAppEta_exists hB.closed
    (visitCases_exists hB (fun m hm => ih m (by omega)) hci hnm) hctx hR hA hm hrun
  exact ⟨_, .special hor hma hT hη⟩

end

end Steps

end EraseProof
