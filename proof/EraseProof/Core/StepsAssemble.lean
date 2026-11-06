import EraseProof.Core.StepsB
import EraseProof.Core.StepsCtor
import EraseProof.Core.StepsCasesBox

/-!
# The literal step, the dispatch of `visitCases`, and the pure traversal's correctness

* The literal step (`StepsB.lit`): a translated literal binds ``Nat.zero`` and ``Nat.succ`` to the
  constructors `0` and `1` of the inductive bound to ``Nat`` (`TrM.lit`), so the closure's
  constructors of those names are `Nat`'s (`natCtorNames_of_lit`), which is what
  `stepsB_lit_of` needs.
* `visitCases` on a saturated spine (`StepsCases.CasesSatSpec`), by its branches: the `□` branch
  (`casesSat_box`), the reduced branch (`casesSat_reduced`), and the branch that builds a λ□
  `case`, taken as the hypothesis `CasesCaseSpec`.
* `erasePure_erases_statement` from `CasesCaseSpec` (`erasePure_erases_of_case`).

Reference: `erases_erase` (`MR E/ErasureFunction.v:1228`); the `tCase` case of `erase`
(`MR E/ErasureFunction.v:989`) with `erases_tCase` (`MR E/Extract.v:111`).
-/

open Lean Erasure
open Metalean (Defeq)

namespace EraseProof

namespace Steps

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P decls : List ConstantInfo}
  {view : EnvView} {cfg : ErasureConfig}

/-- A constructor of the closure bound to the constructor `k` of the inductive bound to ``Nat``
has inductive ``Nat``, index `k`, no parameter, and the fields of `Nat`'s constructor `k`.
Reference: `declared_constructor` (MC §3.6). -/
theorem natCtor_of_bind (hP : ProgEnv P ζ E B) (hsub : SubEnv decls P)
    {ηNat : Metalean.Head ζ (.inductive natSig)} (hB : B ``Nat = some (.ind ηNat 0))
    {x : Name} {k : Fin 2} {o : List Nat} (hx : B x = some (.ctor ηNat 0 k o))
    {cv : ConstructorVal} (hcv : findDecl decls x = some (.ctorInfo cv)) :
    cv.induct = ``Nat ∧ cv.cidx = k.val ∧ cv.numParams = 0 ∧
      cv.numFields = (natSig.ctors 0 k).nfields + (natSig.ctors 0 k).nrecFields := by
  obtain ⟨ι, η, s, k', order, hBc, hcidx, hnp, hnf, -, hI⟩ :=
    hP.lookup_ctor (Extend.findDecl_sub hsub hcv)
  rw [hx] at hBc
  cases hBc
  obtain ⟨lps, Is, Cs, Rs, orders, hb⟩ := CasesWhred.ProgEnv.block hP ηNat
  exact ⟨(hb.2.2.2.2.1 _ _ hI).trans (hb.2.2.2.2.1 _ _ hB).symm, hcidx, hnp, hnf⟩

/-- The bindings of a translated literal (`TrM.lit`) make the closure's ``Nat.zero`` and
``Nat.succ`` `Nat`'s constructors (`NatCtorNames`). Reference: none (PCUIC has no literals; the
`Nat` literal extension of Lean's kernel). -/
theorem natCtorNames_of_lit (hP : ProgEnv P ζ E B) (hsub : SubEnv decls P)
    {ηNat : Metalean.Head ζ (.inductive natSig)} {o₀ o₁ : List Nat}
    (hB : B ``Nat = some (.ind ηNat 0)) (h₀ : B ``Nat.zero = some (.ctor ηNat 0 0 o₀))
    (h₁ : B ``Nat.succ = some (.ctor ηNat 0 1 o₁)) : NatCtorNames decls :=
  ⟨fun _ hcv => natCtor_of_bind hP hsub hB h₀ hcv, fun _ hcv => natCtor_of_bind hP hsub hB h₁ hcv⟩

/-- The `lit` step (`StepsB.lit`): a string literal has no translation, and a Nat literal's
translation gives `NatCtorNames` (`natCtorNames_of_lit`), whence `stepsB_lit_of`. Reference:
none (PCUIC has no literals; `visitLiteral`, `LeanToLambdaBox/Erasure.lean:704`). -/
theorem stepsB_lit {fuel : Nat} {l : Literal} (hG : CoreEnv E B P decls view cfg)
    (ih : StepIH E B view cfg decls fuel) :
    ExprSpec E B view cfg decls (fuel + 1) (.lit l) := by
  intro lps n Γ Δ S t st tc ps r st' ps' hctx hsc hocc hmf hnp hrf hok he ht hrun
  cases l with
  | strVal s =>
    exfalso
    generalize hx : Expr.lit (.strVal s) = x at he
    cases he with
    | special => exact absurd hx (CasesWhred.ne_mkAppN_const fun _ _ h => by cases h)
    | _ => cases hx
  | natVal k =>
    obtain ⟨ηNat, o₀, o₁, hB, h₀, h₁⟩ := CasesWhred.trM_lit_ctors he
    exact stepsB_lit_of (natCtorNames_of_lit hG.prog hG.sub hB h₀ h₁) hG ih hctx hsc hocc hmf hnp
      hrf hok he ht hrun

end
end Steps

namespace StepsCases

open Steps

/-- The branch of `visitCases` (`LeanToLambdaBox/Erasure.lean:922`) that erases a saturated spine
`c.{us} as` of a recognized `casesOn` constant `c` to a λ□ `case` on the discriminant's erasure:
when `c` has more universe parameters than its inductive `iv`, the oracle's level of the
discriminant's type is `u`, and the reduced branch is not taken (`u` is never zero, or `iv` does
not have exactly one constructor), a successful run erases the spine, with the premises and the
conclusion of `CasesSatSpec`. Reference: `erases_tCase` (`MR E/Extract.v:111`). -/
def CasesCaseSpec : Prop :=
  ∀ {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P decls : List ConstantInfo}
    {view : EnvView} {cfg : ErasureConfig} {j : Nat} {c : Name} {ci : CasesInfo}
    {cd : DefinitionVal} {iv : InductiveVal},
    CoreEnv E B P decls view cfg → StepIH E B view cfg decls j →
    casesInfo? decls c = some ci → findDecl decls c = some (.defnInfo cd) →
    findDecl decls ci.indName = some (.inductInfo iv) →
    cd.levelParams.length ≠ iv.levelParams.length →
    ∀ ⦃lps : List Name⦄ ⦃n : Nat⦄ ⦃Γ : Metalean.Ctx ζ lps.length 0 n⦄ ⦃Δ : MLCtx ζ lps.length n⦄
      ⦃S : Name → Prop⦄ ⦃us : List Level⦄ ⦃as : List Expr⦄ ⦃t : Metalean.Expr ζ lps.length n⦄
      ⦃st : ErasureState⦄ ⦃tc : TravCtx⦄ ⦃ps : PureState⦄ ⦃r : LBTerm⦄ ⦃st' : ErasureState⦄
      ⦃ps' : PureState⦄ ⦃u : Level⦄,
      (∀ m, as[casesMajor iv]? = some m →
        Pure.typeLevel ⟨decls⟩ oracleFuel tc.locals m = .ok u) →
      (u.isNeverZero = true ∨ iv.ctors.length ≠ 1) →
      CtxOK E B lps Γ Δ cfg tc ps → ScopeOK decls S →
      (∀ d, nameOccurs d (mkAppN (.const c us) as.toArray) = true → S d) →
      MachineFree cfg (mkAppN (.const c us) as.toArray) →
      NatPlain cfg (mkAppN (.const c us) as.toArray) →
      RecFree decls (mkAppN (.const c us) as.toArray) →
      StateOK E B (evalEnvOf view cfg decls) st →
      TrM E B lps Γ Δ (mkAppN (.const c us) as.toArray) t → (∃ T, E[Γ] ⊢ t : T) →
      ci.arity ≤ as.length →
      (visitCases (m := PureM) j ci as.toArray).runPure st tc ⟨decls, view⟩ ps =
        .ok ((r, st'), ps') →
      Erases E B lps (evalEnvOf view cfg decls) Γ Δ (mkAppN (.const c us) as.toArray) r ∧
        ErasesDeps E B (evalEnvOf view cfg decls) st'.gdecls r ∧
        Grows E B (evalEnvOf view cfg decls) S st st' ps ps'

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P decls : List ConstantInfo}
  {view : EnvView} {cfg : ErasureConfig}

/-- `visitCases` on saturated spines (`CasesSatSpec`), by its branches in the order it tests them:
`□` when the `casesOn` has as many universe parameters as its inductive (`casesSat_box`); a
failure when the oracle has no level for the discriminant's type; the reduced branch when that
level may be zero and the inductive has one constructor (`casesSat_reduced`); otherwise the λ□
`case` (`CasesCaseSpec`). Reference: `erases_tCase` (`MR E/Extract.v:111`). -/
theorem casesSatSpec_of_case (h3 : CasesCaseSpec) (hG : CoreEnv E B P decls view cfg) {j : Nat}
    (ih : StepIH E B view cfg decls j) {c : Name} {ci : CasesInfo}
    (hci : casesInfo? decls c = some ci) : CasesSatSpec E B view cfg decls j c ci := by
  intro lps n Γ Δ S us as t st tc ps r st' ps' hctx hsc hocc hmf hnp hrf hok he ht hsat hrun
  obtain ⟨iv, cd, hiv, hd, hdn, -, har, hdp⟩ := casesInfo?_eval (view := view) (cfg := cfg) hci
  by_cases hlp : cd.levelParams.length = iv.levelParams.length
  · exact casesSat_box hG hci hd hiv hlp hctx hok he ht hsat hrun
  have hmlt : casesMajor iv < as.length := by simp only [casesArity] at har; omega
  cases hTL : Pure.typeLevel ⟨decls⟩ oracleFuel tc.locals (as[casesMajor iv]'hmlt) with
  | error err =>
    exfalso
    have hdisc : as.toArray[ci.discrPos]? = some (as[casesMajor iv]'hmlt) := by
      rw [hdp]; simp
    cases j with
    | zero => rw [visitCases] at hrun; cases hrun
    | succ j =>
    rw [visitCases, TravFrame.runPure_bind, getOrFail_run hdisc, Steps.ok_bind'] at hrun
    dsimp only at hrun
    rw [TravFrame.runPure_bind,
      getConst_run (pc := ⟨decls, view⟩) (show findConst decls _ = _ from hiv),
      Steps.ok_bind'] at hrun
    dsimp only at hrun
    rw [TravFrame.runPure_bind, hdn,
      getConst_run (pc := ⟨decls, view⟩) (show findConst decls _ = _ from hd),
      Steps.ok_bind'] at hrun
    dsimp only at hrun
    simp only [show (cd.levelParams.length == iv.levelParams.length) = false by simpa using hlp,
      Bool.false_eq_true, ↓reduceIte] at hrun
    rw [TravFrame.runPure_read_bind, TravFrame.runPure_read_bind, TravFrame.runPure_bind,
      TravFrame.runPure_liftM, TravFrame.typeLevel_run, hTL] at hrun
    obtain ⟨_, h, -⟩ := OracleWhnf.ok_of_bind hrun
    cases h
  | «ok» u =>
    have hu : ∀ m, as[casesMajor iv]? = some m →
        Pure.typeLevel ⟨decls⟩ oracleFuel tc.locals m = .ok u := fun m hm => by
      rw [List.getElem?_eq_getElem hmlt] at hm
      cases hm
      exact hTL
    by_cases hred : u.isNeverZero = false ∧ iv.ctors.length = 1
    · exact casesSat_reduced hG ih hci hd hiv hlp hred.2 hu hred.1 hctx hsc hocc hmf hnp hrf hok
        he ht hsat hrun
    · have hc3 : u.isNeverZero = true ∨ iv.ctors.length ≠ 1 := by
        cases hz : u.isNeverZero
        · exact .inr fun h1 => hred ⟨hz, h1⟩
        · exact .inl rfl
      exact h3 hG ih hci hd hiv hlp hu hc3 hctx hsc hocc hmf hnp hrf hok he ht hsat hrun

end
end StepsCases

/-- The pure traversal's correctness (`erasePure_erases_statement`), given the `case` branch of
`visitCases` (`StepsCases.CasesCaseSpec`): the constructor, projection and literal steps, and the
`casesOn` step from `visitCases`'s dispatch (`StepsCases.casesSatSpec_of_case`). Reference:
`erases_erase` (`MR E/ErasureFunction.v:1228`). -/
theorem erasePure_erases_of_case (h : StepsCases.CasesCaseSpec) : erasePure_erases_statement :=
  erasePure_erases_of_stepsB
    ⟨Steps.stepsB_ctor,
      Steps.stepsB_cases_of_sat fun hG ih hci => StepsCases.casesSatSpec_of_case h hG ih hci,
      Steps.stepsB_proj, Steps.stepsB_lit⟩

end EraseProof
