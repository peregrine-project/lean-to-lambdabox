import EraseProof.Core.StepsCtor

/-!
# Steps of the shipping core's correctness: quotients

An application or a constant whose head is `Quot.mk` or `Quot.lift` (a quotient constant with an
evaluation arity, `quotEvalArity`): `visitConstApp` (`LeanToLambdaBox/Erasure.lean:958`)
η-expands the spine to the arity (3, resp. 6; `withAppEta_spec`) and erases `Quot.mk α r a` as the
element and `Quot.lift α r β f h q` as `f q`, each applied to the arguments beyond the arity
(`visitAppArgs_list`). The marking traces the same decisions (`MarkOf.special`, `MarkEta`,
`MarkSat.quotMk`, `MarkSat.quotLift`), which `Erases.quotMk` and `Erases.quotLift` relate to the
output.

Reference: none in MetaRocq (PCUIC has no quotients); Lean's code generator
(`Lean/Compiler/LCNF/ToLCNF.lean`, `visitQuotLift`; `ToMono.lean`); DV-29. Adapted from
`ML-V Core/StepsQuot.lean`, whose typing premises are replaced by the marking.
-/

open Lean Erasure

namespace EraseProof

namespace Steps

open RegisterInd OracleRen StateLemmas Decls

section
variable {decls : List ConstantInfo} {view : EnvView} {cfg : ErasureConfig}

/-- A quotient constant is no recognized `casesOn` (`casesInfo?` reads a definition) and no
constructor. Reference: none. -/
theorem quot_heads {c : Name} {qv : QuotVal} (hqv : findDecl decls c = some (.quotInfo qv)) :
    casesInfo? decls c = none ∧ ctorArity? decls c = none := by
  have hf : findConst decls c = some (.quotInfo qv) := hqv
  refine ⟨?_, ?_⟩
  · unfold casesInfo?
    split
    · rw [hf]
    · rfl
  · unfold ctorArity?
    rw [hf]

/-- `visitApp (k + 1)` at the pure backend on a spine that the oracle keeps whose head is `Quot.mk`
or `Quot.lift`, from `visitExpr` at the fuels up to `k`: the marking is `MarkOf.special` (the head
has its arity, `markArity?`), `visitConstApp` takes its quotient branch, `withAppEtaToMinArity`
η-expands the spine (`withAppEta_spec`), and the saturated spine is erased by `Erases.quotMk` (the
element applied to the arguments beyond the arity, `MarkSat.quotMk`) or `Erases.quotLift` (the
function applied to the quotient and the arguments beyond the arity, `MarkSat.quotLift`).
Adapted from `ML-V Core/StepsQuot.lean:65 visitApp_quot`. Reference: `visitConstApp`
(`LeanToLambdaBox/Erasure.lean:958`); DV-29. -/
theorem visitApp_quot (hG : CoreEnv view cfg decls) {k : Nat} (ih : StepIH view cfg decls k)
    {ρ : FVarId → FVarId} {S : FVarId → Prop} {ls : List Local} {Sc : Name → Prop} {e ê : Expr}
    {st st' : ErasureState} {tc : TravCtx} {ps ps' : PureState} {r : LBTerm} {c : Name}
    {us : List Level} {qv : QuotVal} (hfn : e.getAppFn = .const c us)
    (hqv : findDecl decls c = some (.quotInfo qv)) (hqs : (quotEvalArity qv.kind).isSome)
    (hctx : CtxOK cfg tc) (hR : RenOK ρ S ls tc.locals ps.next) (he : FVarsIn S e)
    (hsc : ScopeOK decls Sc) (hocc : ∀ d, nameOccurs d e = true → Sc d) (hnp : NatPlain cfg e)
    (hrs : RecShaped cfg decls e) (hok : StateOK noCert (evalEnvOf view cfg decls) st)
    (hm : MarkOf decls cfg ls e ê)
    (hor : Pure.isErasable ⟨decls⟩ oracleFuel tc.locals (renFV ρ e) = .ok false)
    (hrun : (visitApp (m := PureM) (k + 1) (renFV ρ e)).runPure st tc ⟨decls, view⟩ ps =
      .ok ((r, st'), ps')) :
    Erases noCert (evalEnvOf view cfg decls) [] (renFV ρ ê) r ∧ closedn 0 r = true ∧
      ErasesDeps noCert (evalEnvOf view cfg decls) st'.gdecls r ∧
      Grows (evalEnvOf view cfg decls) Sc st st' ps ps' := by
  obtain ⟨hcs, hca⟩ := quot_heads hqv
  obtain ⟨ar, har⟩ := Option.isSome_iff_exists.1 hqs
  have hma : markArity? decls cfg c = some ar := by
    unfold markArity?
    rw [hcs, hca]
    dsimp only
    rw [hqv]
    exact har
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
  | @special _ c' us' ar' T ê as _ hma' hT hη =>
    rw [getAppFn_mkAppN_const] at hfn
    cases hfn
    rw [hma] at hma'
    cases hma'
    obtain ⟨-, hA⟩ := spine_premises (f := .const c us) ⟨he, hocc, hnp, hrs⟩
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
        EraseT PureM (Option CasesInfo)).runPure st tc ⟨decls, view⟩ ps = .ok ((none, st), ps) by
      show Except.ok ((casesInfo? decls c, st), ps) = _; rw [hcs], ok_bind'] at hrun
    dsimp only at hrun
    rw [runPure_bind, show (liftM (Backend.ctorArity? (m := PureM) c) :
        EraseT PureM (Option Nat)).runPure st tc ⟨decls, view⟩ ps = .ok ((none, st), ps) by
      show Except.ok ((ctorArity? decls c, st), ps) = _; rw [hca], ok_bind'] at hrun
    dsimp only at hrun
    rw [runPure_bind, show (liftM (Backend.findConst? (m := PureM) c) :
        EraseT PureM (Option ConstantInfo)).runPure st tc ⟨decls, view⟩ ps =
          .ok ((some (.quotInfo qv), st), ps) by
      show Except.ok ((findConst decls c, st), ps) = _
      rw [show findConst decls c = findDecl decls c from rfl, hqv], ok_bind'] at hrun
    dsimp only at hrun
    obtain ⟨cval, kind⟩ := qv
    cases kind with
    | type => simp [quotEvalArity] at hqs
    | ind => simp [quotEvalArity] at hqs
    | ctor =>
      obtain rfl : ar = 3 := (Option.some.inj har).symm
      refine withAppEta_spec hG.closed ?_ hctx hR hsc hA hok hT hη hrun
      intro ρ₁ S₁ ls₁ Sc₁ ê₁ st₁ tc₁ ps₁ r₁ st₁' ps₁' as₁ hctx₁ hR₁ hsc₁ hargs₁ hle₁ hok₁ hs₁ hrun₁
      cases hs₁ with
      | @quotMk _ qv' _ a â _ α rr extra êxtra _ _ hq' hk hmA hlen hall =>
        rw [runPure_bind] at hrun₁
        obtain ⟨⟨⟨a₁, sa⟩, pa⟩, hg, hrun₁⟩ := ok_of_bind hrun₁
        obtain ⟨ha, rfl, rfl⟩ := getOrFail_run hg
        simp only [List.map_cons, List.cons_append, List.nil_append, List.getElem?_toArray,
          List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at ha
        subst ha
        rw [runPure_bind] at hrun₁
        obtain ⟨⟨⟨tf, st₂⟩, ps₂⟩, hf, hrun₁⟩ := ok_of_bind hrun₁
        have hsub : ∀ b ∈ extra, b ∈ [α, rr, a] ++ extra := fun b hb => List.mem_append_right _ hb
        obtain ⟨hfa, hoa, hna, hra⟩ := hargs₁ a (by simp)
        have ⟨herf, hcf, hdf, hgf⟩ := ih.expr j (Nat.le_succ _) a hctx₁ hR₁ hfa hsc₁ hoa hna hra
          hok₁ hmA hf
        rw [show (List.toArray (([α, rr, a] ++ extra).map (renFV ρ₁))).extract 3 =
          (extra.map (renFV ρ₁)).toArray by simp [List.take_of_length_le]] at hrun₁
        cases j with
        | zero => rw [visitAppArgs] at hrun₁; cases hrun₁
        | succ i =>
        obtain ⟨as', rfl, hlen', hers, hdeps, hgr⟩ := visitAppArgs_list
          (ih.expr i (by omega)) hctx₁ hsc₁ (hR₁.mono hgf.next) (fun b hb => hargs₁ b (hsub b hb))
          hlen hall hgf.inv hrun₁
        refine ⟨?_, RecLam.closedn_mkApps.2 ⟨hcf, fun a' ha' => (hdeps a' ha').1⟩,
          ErasesDeps.mkApps_iff.2 ⟨ErasesDeps.ext hgr.ext hdf, fun a' ha' => (hdeps a' ha').2⟩,
          hgf.trans hgr⟩
        rw [renFV_mkAppN]
        simp only [List.map_append, List.map_cons, List.map_nil]
        exact .quotMk hq' hk herf hlen' hers
      | quotLift _ _ hq' hk =>
        rw [hq'] at hqv; cases hqv; cases hk
      | ctor _ h₂ => rw [hca] at h₂; cases h₂
      | recr _ _ hr => rw [hr] at hqv; cases hqv
      | casesProp h₁ | casesReduced h₁ | cases h₁ => simp [casesOnOf?, hcs] at h₁
    | lift =>
      obtain rfl : ar = 6 := (Option.some.inj har).symm
      refine withAppEta_spec hG.closed ?_ hctx hR hsc hA hok hT hη hrun
      intro ρ₁ S₁ ls₁ Sc₁ ê₁ st₁ tc₁ ps₁ r₁ st₁' ps₁' as₁ hctx₁ hR₁ hsc₁ hargs₁ hle₁ hok₁ hs₁ hrun₁
      cases hs₁ with
      | @quotLift _ qv' _ f fM q qM _ α rr β h extra êxtra _ _ hq' hk hmF hmQ hlen hall =>
        rw [runPure_bind] at hrun₁
        obtain ⟨⟨⟨f₁, sa⟩, pa⟩, hg, hrun₁⟩ := ok_of_bind hrun₁
        obtain ⟨ha, rfl, rfl⟩ := getOrFail_run hg
        simp only [List.map_cons, List.cons_append, List.nil_append, List.getElem?_toArray,
          List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at ha
        subst ha
        rw [runPure_bind] at hrun₁
        obtain ⟨⟨⟨tf, st₂⟩, ps₂⟩, hf, hrun₁⟩ := ok_of_bind hrun₁
        have hsub : ∀ b ∈ q :: extra, b ∈ [α, rr, β, f, h, q] ++ extra := by
          intro b hb
          rcases List.mem_cons.1 hb with rfl | hb
          · simp
          · exact List.mem_append_right _ hb
        obtain ⟨hfa, hoa, hna, hra⟩ := hargs₁ f (by simp)
        have ⟨herf, hcf, hdf, hgf⟩ := ih.expr j (Nat.le_succ _) f hctx₁ hR₁ hfa hsc₁ hoa hna hra
          hok₁ hmF hf
        rw [show (List.toArray (([α, rr, β, f, h, q] ++ extra).map (renFV ρ₁))).extract 5 =
          ((q :: extra).map (renFV ρ₁)).toArray by simp [List.take_of_length_le]] at hrun₁
        cases j with
        | zero => rw [visitAppArgs] at hrun₁; cases hrun₁
        | succ i =>
        have hlenQ : (q :: extra).length = (qM :: êxtra).length := by simp [hlen]
        have hallQ : ∀ (i : Nat) a â, (q :: extra)[i]? = some a → (qM :: êxtra)[i]? = some â →
            MarkOf decls cfg ls₁ a â := by
          intro i a â h1 h2
          cases i with
          | zero => simp at h1 h2; subst h1 h2; exact hmQ
          | succ i => exact hall i a â (by simpa using h1) (by simpa using h2)
        obtain ⟨as', rfl, hlen', hers, hdeps, hgr⟩ := visitAppArgs_list
          (ih.expr i (by omega)) hctx₁ hsc₁ (hR₁.mono hgf.next) (fun b hb => hargs₁ b (hsub b hb))
          hlenQ hallQ hgf.inv hrun₁
        obtain ⟨q', rest', rfl⟩ : ∃ q' rest', as' = q' :: rest' := by
          rcases as' with _ | ⟨q', rest'⟩
          · simp at hlen'
          · exact ⟨_, _, rfl⟩
        refine ⟨?_, RecLam.closedn_mkApps.2 ⟨hcf, fun a' ha' => (hdeps a' ha').1⟩,
          ErasesDeps.mkApps_iff.2 ⟨ErasesDeps.ext hgr.ext hdf, fun a' ha' => (hdeps a' ha').2⟩,
          hgf.trans hgr⟩
        rw [renFV_mkAppN]
        simp only [List.map_append, List.map_cons, List.map_nil]
        exact .quotLift hq' hk herf (hers 0 _ _ rfl rfl) (by simpa using hlen')
          (fun i a a' h1 h2 => hers (i + 1) a a' h1 h2)
      | quotMk _ _ hq' hk =>
        rw [hq'] at hqv; cases hqv; cases hk
      | ctor _ h₂ => rw [hca] at h₂; cases h₂
      | recr _ _ hr => rw [hr] at hqv; cases hqv
      | casesProp h₁ | casesReduced h₁ | cases h₁ => simp [casesOnOf?, hcs] at h₁
  | fvar | mdata | lam | letE | proj | litZero | litSucc => cases hfn

/-- The quotient step: an application or a constant whose head is `Quot.mk` or `Quot.lift`,
through `visitApp_quot`; when the oracle erases the spine, `visitExpr_box`. Adapted from
`ML-V Core/StepsQuot.lean:226 stepsB_quot`. Reference: none (PCUIC has no quotients); DV-29. -/
theorem visitExpr_quot_step (hG : CoreEnv view cfg decls) {fuel : Nat}
    (ih : StepIH view cfg decls fuel) {e : Expr} {c : Name} {us : List Level} {qv : QuotVal}
    (hfn : e.getAppFn = .const c us) (hqv : findDecl decls c = some (.quotInfo qv))
    (hqs : (quotEvalArity qv.kind).isSome) :
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
  exact visitApp_quot hG ⟨fun m hm => ih.expr m (by omega), fun m hm => ih.mutDecl m (by omega)⟩
    hfn hqv hqs hctx hR he hsc hocc hnp hrs hok hm hor hrun

end

end Steps

end EraseProof
