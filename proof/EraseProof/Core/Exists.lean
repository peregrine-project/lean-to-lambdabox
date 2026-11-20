import EraseProof.Core.ExistsSpines
import EraseProof.Core.CoreEnv
import EraseProof.Statements

/-!
# The existence of the marking, assembled from its steps

`markOf_exists` follows by induction on the fuel of `Erasure.visitExpr` at the pure backend from
one step per case of `visitExpr` (`Core/ExistsSteps.lean`, `Core/ExistsSpines.lean`): an
application or a constant is dispatched by its head as `MarkOf` reads it (`existsSpec_appLike`):
a recognized `casesOn` constant, a constructor, `Quot.mk`/`Quot.lift`, a recursor that `visitRec`
does not keep as a constant, or a head without a rule of its own (`markArity? = none`).
`markOf_exists` applies the induction at the traversal's fuel in the empty context (`ρ = id`, no
local), from the empty state, which registers no inductive; the closure's facts are
`CoreEnvBase` (`coreEnvBase_of`), and the input has no free variable, is `NatPlain` and has no
string literal, from the fragment test's scan of it (`exprConsts_plain`,
`exprConsts_noStrLit`).

Reference: none (DV-32: the marking is the traversal's decisions written on the term; MetaRocq's
`erase` is a function, `MR E/ErasureFunction.v:989`).
-/

open Lean Erasure

namespace EraseProof

namespace Steps

open OracleRen

section
variable {decls : List ConstantInfo} {view : EnvView} {cfg : ErasureConfig}

/-- A term a successful `exprConsts` scanned has no string literal (`exprConsts` rejects one). -/
theorem exprConsts_noStrLit : ∀ {e : Expr} {cs : List Name}, exprConsts cfg e = .ok cs → NoStrLit e
  | .bvar _, _, _ | .sort _, _, _ | .fvar _, _, _ | .mvar _, _, _ | .const .., _, _
  | .lit (.natVal _), _, _ => trivial
  | .lit (.strVal _), _, h => by rw [exprConsts] at h; cases h
  | .app f a, _, h | .lam _ f a _, _, h | .forallE _ f a _, _, h => by
    rw [exprConsts] at h
    obtain ⟨_, hf, h⟩ := RegisterInd.ok_of_bind h
    obtain ⟨_, ha, -⟩ := RegisterInd.ok_of_bind h
    exact ⟨exprConsts_noStrLit hf, exprConsts_noStrLit ha⟩
  | .letE _ t v b _, _, h => by
    rw [exprConsts] at h
    obtain ⟨_, ht, h⟩ := RegisterInd.ok_of_bind h
    obtain ⟨_, hv, h⟩ := RegisterInd.ok_of_bind h
    obtain ⟨_, hb, -⟩ := RegisterInd.ok_of_bind h
    exact ⟨exprConsts_noStrLit ht, exprConsts_noStrLit hv, exprConsts_noStrLit hb⟩
  | .mdata _ e, _, h => by
    rw [exprConsts] at h
    exact exprConsts_noStrLit (e := e) h
  | .proj _ _ e, _, h => by
    rw [exprConsts] at h
    obtain ⟨_, he, -⟩ := RegisterInd.ok_of_bind h
    exact exprConsts_noStrLit (e := e) he

/-- An application or a constant, by the head of its spine: a recognized `casesOn` constant
(`exists_cases_step`), a constructor (`exists_ctor_step`), `Quot.mk` or `Quot.lift`
(`exists_quot_step`), a recursor whose block the closure holds and that `visitRec` does not keep
as a constant (`exists_rec_step`), or a head without a rule of its own, `markArity? = none`
(`exists_app_step`). -/
theorem existsSpec_appLike (hB : CoreEnvBase view cfg decls) {fuel : Nat}
    (ih : ∀ m ≤ fuel, ∀ e, ExistsSpec view cfg decls m e) {e : Expr}
    (hshape : e.isApp = true ∨ ∃ c us, e = .const c us) :
    ExistsSpec view cfg decls (fuel + 1) e := by
  by_cases hc : ∃ c us, e.getAppFn = .const c us
  · obtain ⟨c, us, hc⟩ := hc
    cases hci : casesInfo? decls c with
    | some ci => exact exists_cases_step hB ih hc hci
    | none =>
    cases hca : ctorArity? decls c with
    | some k => exact exists_ctor_step hB.closed hB.ctors ih hc hci hca
    | none =>
    by_cases hq : ∃ qv, findDecl decls c = some (.quotInfo qv) ∧ (quotEvalArity qv.kind).isSome
    · obtain ⟨qv, hqv, hs⟩ := hq
      exact exists_quot_step hB.closed ih hc hqv hs
    by_cases hr : ∃ rv ivs cvs, findDecl decls c = some (.recInfo rv) ∧
        recBlockOf? decls rv = some (ivs, cvs) ∧ recStaysConstant cfg.nat rv ivs cvs = false
    · obtain ⟨rv, ivs, cvs, hrv, hblk, hst⟩ := hr
      exact exists_rec_step hB.closed ih hc hrv hblk hst
    refine exists_app_step hB.closed ih hshape fun c' us' h' => ?_
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
    next rv hrv =>
      split
      next ivs cvs hblk =>
        cases hst : recStaysConstant cfg.nat rv ivs cvs
        · exact absurd ⟨rv, ivs, cvs, hrv, hblk, hst⟩ hr
        · rfl
      next => rfl
    next => rfl
  · exact exists_app_step hB.closed ih hshape fun c us h' => absurd ⟨c, us, h'⟩ hc

/-- `ExistsSpec` at `fuel + 1`, case by case over `visitExpr`, from `ExistsSpec` at the fuels up
to `fuel`. -/
theorem existsSpec_succ (hB : CoreEnvBase view cfg decls) {fuel : Nat}
    (ih : ∀ m ≤ fuel, ∀ e, ExistsSpec view cfg decls m e) :
    ∀ e, ExistsSpec view cfg decls (fuel + 1) e
  | .bvar _ => exists_fail_step hB.closed rfl
  | .sort _ => exists_fail_step hB.closed rfl
  | .forallE .. => exists_fail_step hB.closed rfl
  | .mvar _ => exists_fail_step hB.closed rfl
  | .fvar _ => exists_fvar_step hB.closed
  | .mdata .. => exists_mdata_step hB.closed (ih fuel (Nat.le_refl _))
  | .lam .. => exists_lam_step hB.closed ih
  | .letE .. => exists_letE_step hB.closed ih
  | .lit _ => exists_lit_step hB.closed
  | .proj .. => exists_proj_step hB.closed ih
  | .app .. => existsSpec_appLike hB ih (.inl rfl)
  | .const c us => existsSpec_appLike hB ih (.inr ⟨c, us, rfl⟩)

/-- `ExistsSpec` at every fuel: at `0` every run fails, and at `fuel + 1` it follows from the
steps (`existsSpec_succ`). -/
theorem existsSpec_of (hB : CoreEnvBase view cfg decls) :
    ∀ fuel, ∀ m ≤ fuel, ∀ e, ExistsSpec view cfg decls m e
  | 0 => fun m hm e => by
    obtain rfl := Nat.le_zero.1 hm
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ hrun
    rw [visitExpr] at hrun; cases hrun
  | fuel + 1 => fun m hm e => (Nat.lt_or_eq_of_le hm).elim
      (fun hm => existsSpec_of hB fuel m (by omega) e)
      (fun hm => hm ▸ existsSpec_succ hB (existsSpec_of hB fuel) e)

end

end Steps

open CollectSpec Steps in
/-- **The input has a marking** (`markOf_exists_statement`): wherever the pure traversal erases
the input of a successful fragment test, part of a program con-leche accepts, the input has a
marking. `ExistsSpec` at the traversal's fuel (`existsSpec_of`) in the empty context (`ρ = id`,
no local, `RenOK` on the empty set), from the empty state (no registered inductive), with the
closure's facts `CoreEnvBase` (`coreEnvBase_of`) and the facts about the input that the fragment
test's scan gives: no free variable, `NatPlain` (`exprConsts_plain`), no string literal
(`exprConsts_noStrLit`). Reference: none (DV-32). -/
theorem markOf_exists : markOf_exists_statement := by
  intro P decls env e view cfg p inl hP hsub _ _ hcol hrun
  have hB := coreEnvBase_of hP hsub hcol
  obtain ⟨cs, cases, hcs, -⟩ := CollectSpec.collectDeps_ok hcol
  obtain ⟨hfv, hnp⟩ := CoreEnvOf.exprConsts_plain hcs
  unfold erasePure at hrun
  obtain ⟨⟨⟨r, st'⟩, ps'⟩, hvis, -⟩ := RegisterInd.ok_of_bind hrun
  rw [← OracleRen.renFV_id e] at hvis
  exact existsSpec_of hB travFuel travFuel (Nat.le_refl _) e (ρ := id) (S := fun _ => False)
    (ls := []) ⟨rfl, rfl⟩ ⟨fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim⟩
    ⟨OracleRen.fvarsIn_of_hasFVar hfv, hnp, exprConsts_noStrLit hcs⟩
    (fun _ _ h => by simp at h) hvis

end EraseProof
