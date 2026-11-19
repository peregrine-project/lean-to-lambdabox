import EraseProof.Core.StepsCasesSat
import EraseProof.Core.StepsProj
import EraseProof.Core.StepsQuot
import EraseProof.Core.StepsRec
import EraseProof.Core.NonRec
import EraseProof.Core.CoreEnv
import EraseProof.Core.CtorProp
import EraseProof.Statements

/-!
# The pure traversal's correctness, assembled from its steps

`erasePure_erases` follows by induction on the fuel of `Erasure.visitExpr` at the pure backend from
one step lemma per case of `visitExpr` (`Core/Steps*.lean`) and the step of `visitMutual`
(`Core/StepsApp.lean`): `stepIH_of` builds the induction hypothesis `StepIH` at every fuel; an
application or a constant is dispatched by its head (`exprSpec_appLike`): a recognized `casesOn`
constant, a constructor, `Quot.mk`/`Quot.lift`, a recursor, or a head without a rule of its own
(`markArity? = none`). `erasePure_erases_of` applies it at the traversal's fuel in the empty
context (`ρ = id`, no local), from the empty state, with the closure's names as the scope;
`erasePure_erases` discharges its premises from those of the statement: `CoreEnv` by `coreEnv_of`,
`CtorPropBoxed` by `ctorPropBoxed_of`, and the facts about the input from the fragment test's scan
of it.

Reference: `erases_erase` (`MR E/ErasureFunction.v:1228`), by induction over `erase`
(`MR E/ErasureFunction.v:989`), with `erase_global_erases_deps`
(`MR E/ErasureFunctionProperties.v:172`). Adapted from `ML-V Core/StepsB.lean:105-170` and
`:391`.
-/

open Lean Erasure

namespace EraseProof

namespace Steps

open OracleRen

section
variable {decls : List ConstantInfo} {view : EnvView} {cfg : ErasureConfig}

/-- An application or a constant, by the head of its spine: a recognized `casesOn` constant
(`visitExpr_cases_step`), a constructor (`visitExpr_ctor_step`), `Quot.mk` or `Quot.lift`
(`visitExpr_quot_step`), a recursor (`visitExpr_rec_step`), or a head without a rule of its own,
`markArity? = none` (`hplain`). Adapted from `ML-V Core/StepsB.lean:105`. Reference: the
`tApp`, `tConst`, `tConstruct`, `tCase` cases of `erases_erase` (`MR E/ErasureFunction.v:1228`). -/
theorem exprSpec_appLike (hG : CoreEnv view cfg decls) (hcp : CtorPropBoxed view cfg decls)
    {fuel : Nat} (ih : StepIH view cfg decls fuel) {e : Expr}
    (hplain : (∀ c us, e.getAppFn = .const c us → markArity? decls cfg c = none) →
      ExprSpec view cfg decls (fuel + 1) e) :
    ExprSpec view cfg decls (fuel + 1) e := by
  by_cases hc : ∃ c us, e.getAppFn = .const c us
  · obtain ⟨c, us, hc⟩ := hc
    cases hci : casesInfo? decls c with
    | some ci => exact visitExpr_cases_step hG ih hc hci
    | none =>
    cases hca : ctorArity? decls c with
    | some k => exact visitExpr_ctor_step hG hcp ih hc hci hca
    | none =>
    by_cases hq : ∃ qv, findDecl decls c = some (.quotInfo qv) ∧ (quotEvalArity qv.kind).isSome
    · obtain ⟨qv, hqv, hs⟩ := hq
      exact visitExpr_quot_step hG ih hc hqv hs
    by_cases hr : ∃ rv, findDecl decls c = some (.recInfo rv)
    · obtain ⟨rv, hrv⟩ := hr
      exact visitExpr_rec_step hG ih hc hrv
    refine hplain fun c' us' h' => ?_
    rw [hc] at h'
    cases h'
    unfold markArity?
    rw [hci, hca]
    dsimp only
    split
    next qv hqv =>
      cases hk : quotEvalArity qv.kind with
      | none => rfl
      | some _ => exact absurd ⟨qv, hqv, by rw [hk]; rfl⟩ hq
    next rv hrv => exact absurd ⟨rv, hrv⟩ hr
    next => rfl
  · exact hplain fun c us h' => absurd ⟨c, us, h'⟩ hc

/-- `ExprSpec` at `fuel + 1`, case by case over `visitExpr`. Adapted from
`ML-V Core/StepsB.lean:137`. Reference: the cases of `erases_erase`
(`MR E/ErasureFunction.v:1228`). -/
theorem exprSpec_succ (hG : CoreEnv view cfg decls) (hcp : CtorPropBoxed view cfg decls)
    {fuel : Nat} (ih : StepIH view cfg decls fuel) : ∀ e, ExprSpec view cfg decls (fuel + 1) e
  | .bvar _ => visitExpr_fail_step hG.closed rfl
  | .sort _ => visitExpr_fail_step hG.closed rfl
  | .forallE .. => visitExpr_fail_step hG.closed rfl
  | .mvar _ => visitExpr_fail_step hG.closed rfl
  | .fvar _ => visitExpr_fvar_step hG.closed
  | .mdata .. => visitExpr_mdata_step hG.closed (ih.expr fuel (Nat.le_refl _))
  | .lam .. => visitExpr_lam_step hG.closed ih.expr
  | .letE .. => visitExpr_letE_step hG.closed ih.expr
  | .lit _ => visitExpr_lit_step hG ih
  | .proj .. => visitExpr_proj_step hG ih
  | .app .. => exprSpec_appLike hG hcp ih fun hp => visitExpr_app_step hG ih hp
  | .const c us => exprSpec_appLike hG hcp ih fun hp => visitExpr_const_step hG ih (hp c us rfl)

/-- The induction hypothesis of the steps holds at every fuel: at `0` every run fails, and at
`fuel + 1` it follows from the steps (`exprSpec_succ`, `visitMutual_step`). Copy of
`ML-V Core/StepsB.lean:156 stepIH_of_stepsB`, with the steps as theorems. Reference: the induction
of `erases_erase` (`MR E/ErasureFunction.v:1228`), on the fuel of the shipping traversal. -/
theorem stepIH_of (hG : CoreEnv view cfg decls) (hcp : CtorPropBoxed view cfg decls)
    (hmk : ValuesMarkedOf decls cfg) : ∀ fuel, StepIH view cfg decls fuel
  | 0 => by
    refine ⟨fun m hm e => ?_, fun m hm c => ?_⟩
    · obtain rfl := Nat.le_zero.1 hm
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrun
      rw [visitExpr] at hrun; cases hrun
    · obtain rfl := Nat.le_zero.1 hm
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ hrun
      rw [visitMutual] at hrun; cases hrun
  | fuel + 1 =>
    have ih := stepIH_of hG hcp hmk fuel
    ⟨fun m hm e => (Nat.lt_or_eq_of_le hm).elim (fun hm => ih.expr m (by omega) e)
        (fun hm => hm ▸ exprSpec_succ hG hcp ih e),
      fun m hm c => (Nat.lt_or_eq_of_le hm).elim (fun hm => ih.mutDecl m (by omega) c)
        (fun hm => hm ▸ visitMutual_step hG hmk ih)⟩

/-- The pure traversal's correctness on the closure facts: from `CoreEnv`, `CtorPropBoxed` and a
marking of every value of the closure, on a closed input whose constants are the closure's,
`NatPlain` and `RecShaped`, the output of `erasePure` is an erasure of the input's marking, with
erased dependencies, in a closed λ□ environment. The induction hypothesis at the traversal's fuel
(`stepIH_of`), in the empty context (`ρ = id`, no local, `RenOK` on the empty set), from the empty
state (`StateOK.empty`), with the closure's names as the scope (a `ScopeOK` scope by
`CoreEnv.value`). Adapted from `ML-V Core/StepsB.lean:391 erasePure_erases_of_stepsB`. Reference:
`erase_correct`, its erasure part (`MR E/ErasureFunctionProperties.v:172`,
`MR E/ErasureFunction.v:1309`). -/
theorem erasePure_erases_of (hG : CoreEnv view cfg decls) (hcp : CtorPropBoxed view cfg decls)
    (hmk : ValuesMarkedOf decls cfg) {e ê : Expr} {p : Program} {inl : List Kername}
    (hfv : HasFVar e = false) (hcE : ConstsIn (fun c => (findDecl decls c).isSome) e)
    (hnp : NatPlain cfg e) (hrs : RecShaped cfg decls e)
    (hrun : erasePure view cfg decls e = .ok (p, inl)) (hm : MarkOf decls cfg [] e ê) :
    ∃ lenv tb, p = .untyped lenv (some tb) ∧
      Erases noCert (evalEnvOf view cfg decls) [] ê tb ∧
      ErasesDeps noCert (evalEnvOf view cfg decls) lenv tb ∧ LenvClosed lenv := by
  unfold erasePure at hrun
  obtain ⟨⟨⟨r, st'⟩, ps'⟩, hvis, hret⟩ := RegisterInd.ok_of_bind hrun
  cases hret
  have hsc : ScopeOK decls (fun d => (findDecl decls d).isSome) := fun c hc => by
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.1 hc
    refine ⟨ci, hci, fun v hv hthm hcs d hd => ?_⟩
    obtain ⟨-, Sc, hSc, hocc, -⟩ := hG.value c ci v hci hv hthm hcs
    obtain ⟨cd, hcd, -⟩ := hSc d (hocc d hd)
    simp [hcd]
  rw [← renFV_id e] at hvis
  obtain ⟨her, -, hdeps, hgr⟩ := (stepIH_of hG hcp hmk travFuel).expr travFuel (Nat.le_refl _) e
    (ρ := id) (S := fun _ => False) (ls := []) ⟨rfl, rfl⟩
    ⟨fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim⟩
    (fvarsIn_of_hasFVar hfv) hsc (fun _ hd => NonRec.nameOccurs_mem hcE hd) hnp hrs
    StateOK.empty hm hvis
  rw [renFV_id] at her
  exact ⟨_, _, rfl, her, hdeps, hgr.inv.closed⟩

end

end Steps

open CollectSpec CoreEnvOf Steps in
/-- **The pure traversal's correctness** (`erasePure_erases_statement`): on the closure the
fragment test returns, part of a program con-leche accepts, without compiled pre-definitions for
what the traversal erases by its value, and with a marking of every value, the output of
`erasePure` is an erasure of the input's marking, with erased dependencies, in a closed λ□
environment. `erasePure_erases_of` with `CoreEnv` (`coreEnv_of`), `CtorPropBoxed`
(`ctorPropBoxed_of`) and the facts about the input that the fragment test's scan gives: its
constants are the closure's (`collectDeps_spec_sub`), it has no free variable and is `NatPlain`
(`exprConsts_plain`), and its recursors are covered, hence in the fragment's shape
(`Run.rec_frag`). Adapted from `ML-V Core/StepsB.lean:391`. Reference: `erases_erase`
(`MR E/ErasureFunction.v:1228`) and `erase_global_erases_deps`
(`MR E/ErasureFunctionProperties.v:172`); DV-32, DV-35. -/
theorem erasePure_erases : erasePure_erases_statement := by
  intro P decls env e ê view cfg p inl hP hsub hnopre hcol hrun hmk hm
  obtain ⟨-, hdep, hcE, -, -⟩ := collectDeps_spec_sub hP hsub hcol
  obtain ⟨cs, cases, hcs, hcl, -⟩ := CollectSpec.collectDeps_ok hcol
  obtain ⟨hvw, -, -, hcov, hscan⟩ := closure_ok hcl nofun nofun
  have hr : Run P env view cfg decls cases := ⟨hP, hsub, hvw, hscan, hdep⟩
  obtain ⟨hfv, hnp⟩ := exprConsts_plain hcs
  refine erasePure_erases_of (coreEnv_of hP hsub hnopre hcol) (ctorPropBoxed_of hP hsub) hmk
    hfv hcE hnp ?_ hrun hm
  refine ConstsIn_mono (fun c hc rv hrv => ?_) (exprConsts_consts hcs)
  obtain ⟨y, hy, hyn, hyr⟩ := hcov c hc
  rw [← hyn, hr.fd hy] at hrv
  cases hrv
  exact hr.rec_frag hy (hyr rv rfl)

end EraseProof
