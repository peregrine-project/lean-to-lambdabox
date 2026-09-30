import EraseProof.Test.NV1
import EraseProof.Main

/-!
# NV-1 through the entry point of `#erase`

The run of `#erase` on NV-1 (`Test/NV1.lean`) that the hypothesis `hrun` of the final theorem
`erase_correct` (`MR E/ErasureFunctionProperties.v:657`) describes, and `erase_correct` on NV-1.
`hcollect` computes the dependency closure of `e0` by kernel evaluation of the shipping
`collectDeps`, and `eraseEntry_of_erasePure` reduces the entry point on NV-1 to the pure path over
that closure. The pure path's run is evaluated symbolically: the traversal state holds
`Std.HashMap`s, which the kernel does not evaluate, so the run is unfolded one call at a time by
the traversal's equation lemmas at `PureM` (`visitExpr_lam_run`, `visitExpr_appFVar_run`,
`visitExpr_constApp_run`, `get_constant_kername_run`, `visitMutual_one_run`, …), with the state
maps read through `Std.HashMap.getElem?_insert_self`, each oracle call decided by kernel
evaluation, and binder names kept as `binderNameOf` of the user name. `hrun` is the run's result,
and `final` is `erase_correct` with every hypothesis discharged, at its unique witnesses.
-/

open Lean Lean4Lean Erasure

namespace EraseProof.Test.NV1

/-- The dependency closure of `e0`, in the order `collectDeps` returns it: every declaration
after the ones it depends on (`A`, then `CN`, then `one`), the reverse of `decls0`. -/
def decls0' : List ConstantInfo := [.axiomInfo A_val, .defnInfo CN_val, .defnInfo one_val]

/-- `collectDeps` on NV-1's list view returns the closure `decls0'`: the first step of `route`,
by kernel evaluation (the work-list bound `collectFuel` is never reached). Reference: the
environment `Σ'` of `erase_global_deps` (`MR E/ErasureFunction.v:1602`). -/
theorem hcollect : collectDeps view0 e0 = .ok decls0' := by
  rfl

/-- On NV-1, the entry point returns what the pure path returns over `decls0'`: `route` takes
the pure path since `collectDeps` succeeds (`hcollect`). The instance of `eraseEntry_pure`'s
routing on NV-1, in the direction `hrun` needs. Reference: none (S-E). -/
theorem eraseEntry_of_erasePure {r : Program × List Kername}
    (h : erasePure view0 {} decls0' e0 = .ok r) : eraseEntry view0 {} e0 = pure r := by
  simp only [eraseEntry, route, hcollect, h]

/-! ## The pure path's run, one traversal call at a time -/

section Run
variable {pc : PureCtx} {st : ErasureState} {ps : PureState} {tc : TravCtx}

/-- The oracle call that starts each unfolding of `visitExpr` (its equations at `fuel + 1`), when
the oracle answers `false`: the run continues with the branch `K` from the same states. The
converse direction of `oracle_run`. Reference: `is_erasableb` at the start of `erase`
(`MR E/ErasureFunction.v:989`, `:993`). -/
theorem oracle_keep {e : Expr} {K : EraseT PureM LBTerm}
    (hor : Pure.isErasable ⟨pc.decls⟩ oracleFuel tc.locals e = .ok false) :
    (do
        let c₁ ← read
        let c₂ ← read
        let b ← liftM (Backend.isErasable (m := PureM) c₁.lctx c₂.locals e)
        if b = true then pure LBTerm.box else K : EraseT PureM LBTerm).runPure st tc pc ps =
      K.runPure st tc pc ps := by
  rw [runPure_read_bind, runPure_read_bind, runPure_bind, runPure_liftM, isErasable_run, hor]
  rfl

/-- `visitExpr` on a free variable the oracle keeps returns it. Reference: the `tVar` case of
`erase` (`MR E/ErasureFunction.v:996`). -/
theorem visitExpr_fvar_run {n : Nat} {x : FVarId}
    (hor : Pure.isErasable ⟨pc.decls⟩ oracleFuel tc.locals (.fvar x) = .ok false) :
    (visitExpr (m := PureM) (n + 1) (.fvar x)).runPure st tc pc ps = .ok ((.fvar x, st), ps) := by
  rw [visitExpr, oracle_keep hor]
  rfl

/-- `visitExpr` on a λ the oracle keeps: the body, opened with the counter's fresh variable under
the pushed local, runs to `r`, and the result is the λ over `r` abstracted on that variable, named
`binderNameOf` of the binder's user name. Reference: the `tLambda` case of `erase`
(`MR E/ErasureFunction.v:1003`); DV-13. -/
theorem visitExpr_lam_run {n : Nat} {nm : Name} {A b : Expr} {bi : BinderInfo} {r : LBTerm}
    {st' : ErasureState} {ps' : PureState}
    (hor : Pure.isErasable ⟨pc.decls⟩ oracleFuel tc.locals (.lam nm A b bi) = .ok false)
    (hb : (visitExpr (m := PureM) n (b.instantiate1' (.fvar (pureFVar ps.next)))).runPure st
      { tc with lctx := tc.lctx.mkLocalDecl (pureFVar ps.next) nm A bi,
                locals := ⟨pureFVar ps.next, nm, A, none⟩ :: tc.locals } pc ⟨ps.next + 1⟩ =
      .ok ((r, st'), ps')) :
    (visitExpr (m := PureM) (n + 2) (.lam nm A b bi)).runPure st tc pc ps =
      .ok ((.lambda (binderNameOf nm) (_root_.abstract (pureFVar ps.next) r), st'), ps') := by
  rw [visitExpr, oracle_keep hor, visitLambda]
  simp only [lambdaMonocular, withLocalDecl]
  rw [runPure_bind, fresh_run, Except.ok_bind']
  dsimp only
  rw [runPure_withReader, runPure_bind]
  erw [hb]
  rw [Except.ok_bind']
  dsimp only
  rw [mkLambda_run (l := ⟨pureFVar ps.next, nm, A, none⟩) (by simp [Pure.findLocal])]

/-- `visitAppArgs` on one argument applies the head to the argument's erasure. Reference: the
`tApp` case of `erase` (`MR E/ErasureFunction.v:1009`). -/
theorem visitAppArgs_one_run {n : Nat} {tf ta : LBTerm} {a : Expr} {st' : ErasureState}
    {ps' : PureState}
    (ha : (visitExpr (m := PureM) n a).runPure st tc pc ps = .ok ((ta, st'), ps')) :
    (visitAppArgs (m := PureM) (n + 1) tf #[a]).runPure st tc pc ps =
      .ok ((.app tf ta, st'), ps') := by
  rw [visitAppArgs, ← Array.foldlM_toList]
  simp only [List.foldlM_cons, List.foldlM_nil]
  rw [runPure_bind, runPure_bind, ha]
  rfl

/-- `visitExpr` on an application of a free variable that the oracle keeps: the head, then the
argument. Reference: the `tApp` case of `erase` (`MR E/ErasureFunction.v:1009`). -/
theorem visitExpr_appFVar_run {n : Nat} {f : FVarId} {a : Expr} {tf ta : LBTerm}
    {st₁ st₂ : ErasureState} {ps₁ ps₂ : PureState}
    (hor : Pure.isErasable ⟨pc.decls⟩ oracleFuel tc.locals (.app (.fvar f) a) = .ok false)
    (hf : (visitExpr (m := PureM) (n + 1) (.fvar f)).runPure st tc pc ps = .ok ((tf, st₁), ps₁))
    (ha : (visitExpr (m := PureM) n a).runPure st₁ tc pc ps₁ = .ok ((ta, st₂), ps₂)) :
    (visitExpr (m := PureM) (n + 3) (.app (.fvar f) a)).runPure st tc pc ps =
      .ok ((.app tf ta, st₂), ps₂) := by
  rw [visitExpr, oracle_keep hor, visitApp]
  simp only [Expr.getAppFn]
  rw [Expr.withApp_eq]
  rw [runPure_bind, show ((Expr.fvar f).app a).getAppFn = .fvar f from rfl, hf, Except.ok_bind']
  dsimp only
  rw [show ((Expr.fvar f).app a).getAppArgs = #[a] from rfl]
  exact visitAppArgs_one_run ha

/-- `visitConst` outside a recursive block returns the constant's kername from
`get_constant_kername`. Reference: the `tConst` case of `erase` (`MR E/ErasureFunction.v:999`). -/
theorem visitConst_run {n : Nat} {c : Name} {us : List Level} {kn : Kername}
    {st₁ : ErasureState} {ps₁ : PureState} (hfix : tc.fixvars = none)
    (hk : (get_constant_kername (m := PureM) n c).runPure st tc pc ps = .ok ((kn, st₁), ps₁)) :
    (visitConst (m := PureM) (n + 1) (.const c us)).runPure st tc pc ps =
      .ok ((.const kn, st₁), ps₁) := by
  rw [visitConst, runPure_read_bind, hfix]
  dsimp only [Option.bind]
  rw [runPure_bind, hk]
  rfl

/-- `visitExpr` on an application of a constant that the oracle keeps, outside a recursive block:
`visitConstApp` finds no `casesOn` and no constructor at the pure backend, so the head is
`visitConst`, then the argument. Reference: the `tApp` and `tConst` cases of `erase`
(`MR E/ErasureFunction.v:1009`, `:999`). -/
theorem visitExpr_constApp_run {n : Nat} {c : Name} {us : List Level} {a : Expr} {kn : Kername}
    {ta : LBTerm} {st₁ st₂ : ErasureState} {ps₁ ps₂ : PureState}
    (hor : Pure.isErasable ⟨pc.decls⟩ oracleFuel tc.locals (.app (.const c us) a) = .ok false)
    (hfix : tc.fixvars = none)
    (hk : (get_constant_kername (m := PureM) n c).runPure st tc pc ps = .ok ((kn, st₁), ps₁))
    (ha : (visitExpr (m := PureM) n a).runPure st₁ tc pc ps₁ = .ok ((ta, st₂), ps₂)) :
    (visitExpr (m := PureM) (n + 4) (.app (.const c us) a)).runPure st tc pc ps =
      .ok ((.app (.const kn) ta, st₂), ps₂) := by
  rw [visitExpr, oracle_keep hor, visitApp]
  simp only [Expr.getAppFn]
  rw [visitConstApp, Expr.withApp_eq]
  simp only [Expr.getAppFn]
  rw [runPure_bind, show (liftM (Backend.casesInfo? (m := PureM) c) : EraseT PureM _).runPure st tc
    pc ps = .ok ((none, st), ps) from rfl, Except.ok_bind']
  dsimp only
  rw [runPure_bind, show (liftM (Backend.ctorArity? (m := PureM) c) : EraseT PureM _).runPure st tc
    pc ps = .ok ((none, st), ps) from rfl, Except.ok_bind']
  dsimp only
  rw [runPure_bind, visitConst_run hfix hk, Except.ok_bind']
  dsimp only
  rw [show ((Expr.const c us).app a).getAppArgs = #[a] from rfl]
  exact visitAppArgs_one_run ha

/-- `get_constant_kername` on an unregistered constant runs `visitMutual` and returns the kername
it registered. The converse direction of `get_constant_kername_ok`. Reference:
`erase_global_deps` (`MR E/ErasureFunction.v:1602`), which erases the constant's declaration. -/
theorem get_constant_kername_run {n : Nat} {c : Name} {kn : Kername} {st₁ : ErasureState}
    {ps₁ : PureState} (hnone : st.constants[c]? = none)
    (hm : (visitMutual (m := PureM) n c).runPure st tc pc ps = .ok (((), st₁), ps₁))
    (hkn : st₁.constants[c]? = some kn) :
    (get_constant_kername (m := PureM) (n + 1) c).runPure st tc pc ps = .ok ((kn, st₁), ps₁) := by
  rw [EraseT.runPure, get_constant_kername.eq_2]
  simp only [Std.HashMap.get?_eq_getElem?, bind_pure_comp, StateT.run_bind, StateT.run_get,
    pure_bind, hnone, StateT.run_map, map_pure, ReaderT.run_map]
  rw [EraseT.runPure] at hm
  rw [hm]
  simp only [Std.HashMap.getElem!_eq_get!_getElem?]
  show Except.ok ((st₁.constants[c]?.get!, st₁), ps₁) = _
  rw [hkn]
  rfl

end Run

/-- `visitMutual` on `one` over NV-1's closure, under the default configuration: `one` is a
single, non-`@[extern]`, non-inline, non-recursive definition, so its value is erased with no fix
variables and registered as a constant declaration. Reference: the `ConstantDecl` step of
`erase_global_deps` (`MR E/ErasureFunction.v:1602`) with `erase_constant_body`
(`MR E/ErasureFunction.v:1309`). -/
theorem visitMutual_one_run {tc : TravCtx} {st : ErasureState} {ps : PureState} {n : Nat}
    {t : LBTerm} {st₁ : ErasureState} {ps₁ : PureState} (hcfg : tc.config = {})
    (hb : (visitExpr (m := PureM) n oneE).runPure st { tc with fixvars := none }
      ⟨decls0', view0⟩ ps = .ok ((t, st₁), ps₁)) :
    (visitMutual (m := PureM) (n + 1) `one).runPure st tc ⟨decls0', view0⟩ ps =
      .ok (((), { st₁ with constants := st₁.constants.insert `one (toKername `one),
                           gdecls := (toKername `one, .constantDecl ⟨some t⟩) :: st₁.gdecls }),
        ps₁) := by
  rw [visitMutual, runPure_bind, show (liftM (Backend.declInfo? (m := PureM) `one) :
    EraseT PureM _).runPure st tc ⟨decls0', view0⟩ ps = .ok ((some (.defnInfo one_val), st), ps)
    from rfl, Except.ok_bind']
  dsimp only
  rw [runPure_bind, show (liftM (Backend.inlineAttr? (m := PureM) `one) : EraseT PureM _).runPure st
    tc ⟨decls0', view0⟩ ps = .ok ((none, st), ps) from rfl, Except.ok_bind']
  dsimp only
  rw [runPure_bind, show (liftM (Backend.inlineAttr? (m := PureM) `one) : EraseT PureM _).runPure st
    tc ⟨decls0', view0⟩ ps = .ok ((none, st), ps) from rfl, Except.ok_bind']
  dsimp only
  simp only [Option.get!_some, show (ConstantInfo.defnInfo one_val).all.length = 1 from rfl,
    show (ConstantInfo.defnInfo one_val).value? true = some oneE from rfl,
    show (ConstantInfo.defnInfo one_val).value! true = oneE from rfl,
    beq_self_eq_true, Bool.and_false, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
  rw [runPure_bind, show (liftM (Backend.isExtern (m := PureM) `one) : EraseT PureM _).runPure st
    tc ⟨decls0', view0⟩ ps = .ok ((false, st), ps) from rfl, Except.ok_bind']
  dsimp only
  rw [runPure_read_bind, name_occurs_eq, show nameOccurs `one oneE = false from rfl]
  simp only [Bool.not_false, ↓reduceIte]
  rw [runPure_bind, runPure_withReader, runPure_read_bind, runPure_bind,
    show (liftM (Backend.prepare (m := PureM) _ oneE) : EraseT PureM _).runPure st _
      ⟨decls0', view0⟩ ps = .ok ((oneE, st), ps) from rfl, Except.ok_bind']
  dsimp only
  rw [hb, Except.ok_bind']
  rcases tc with ⟨L, ls, F, cfg⟩
  dsimp only at hcfg
  subst hcfg
  rfl

/-! ## The run on NV-1 -/

/-- The local of `one`'s binder `s`, at the counter's first variable. -/
def lS : Local := ⟨pureFVar 0, `s, .forallE `x tyA tyA .default, none⟩

/-- The local of `one`'s binder `z`, at the counter's second variable. -/
def lZ : Local := ⟨pureFVar 1, `z, tyA, none⟩

/-- The local of the argument's binder `a`, at the counter's third variable. -/
def lA : Local := ⟨pureFVar 2, `a, tyA, none⟩

/-- The oracle keeps `one`'s value (type `(A → A) → A → A`, of sort `Type`). -/
theorem oracle_oneE : Pure.isErasable ⟨decls0'⟩ oracleFuel [] oneE = .ok false := rfl

/-- The oracle keeps `fun z => s z` under `s`. -/
theorem oracle_lamZ : Pure.isErasable ⟨decls0'⟩ oracleFuel [lS]
    (.lam `z tyA (.app (.fvar (pureFVar 0)) (.bvar 0)) .default) = .ok false := rfl

/-- The oracle keeps `s z` under `z`, `s`. -/
theorem oracle_app : Pure.isErasable ⟨decls0'⟩ oracleFuel [lZ, lS]
    (.app (.fvar (pureFVar 0)) (.fvar (pureFVar 1))) = .ok false := rfl

/-- The oracle keeps `s` under `z`, `s`. -/
theorem oracle_s : Pure.isErasable ⟨decls0'⟩ oracleFuel [lZ, lS] (.fvar (pureFVar 0)) =
    .ok false := rfl

/-- The oracle keeps `z` under `z`, `s`. -/
theorem oracle_z : Pure.isErasable ⟨decls0'⟩ oracleFuel [lZ, lS] (.fvar (pureFVar 1)) =
    .ok false := rfl

/-- The oracle keeps `e0` (type `CN`, which δ-reduces to a Π of sort `Type`). -/
theorem oracle_e0 : Pure.isErasable ⟨decls0'⟩ oracleFuel [] e0 = .ok false := rfl

/-- The oracle keeps the argument `fun a => a`. -/
theorem oracle_lamA : Pure.isErasable ⟨decls0'⟩ oracleFuel [] (.lam `a tyA (.bvar 0) .default) =
    .ok false := rfl

/-- The oracle keeps `a` under `a`. -/
theorem oracle_a : Pure.isErasable ⟨decls0'⟩ oracleFuel [lA] (.fvar (pureFVar 2)) = .ok false :=
  rfl

/-- The innermost body of `one`, `s z`, erases to itself. -/
theorem body_app_run (n : Nat) (L : LocalContext) (F : Option (Std.HashMap Name FVarId))
    (C : ErasureConfig) (st : ErasureState) :
    (visitExpr (m := PureM) (n + 4) (.app (.fvar (pureFVar 0)) (.fvar (pureFVar 1)))).runPure st
      ⟨L, [lZ, lS], F, C⟩ ⟨decls0', view0⟩ ⟨2⟩ =
      .ok ((.app (.fvar (pureFVar 0)) (.fvar (pureFVar 1)), st), ⟨2⟩) :=
  visitExpr_appFVar_run oracle_app (visitExpr_fvar_run oracle_s) (visitExpr_fvar_run oracle_z)

/-- The body `fun z => s z` of `one` under `s`. -/
theorem body_lamZ_run (n : Nat) (L : LocalContext) (F : Option (Std.HashMap Name FVarId))
    (C : ErasureConfig) (st : ErasureState) :
    (visitExpr (m := PureM) (n + 6)
      (.lam `z tyA (.app (.fvar (pureFVar 0)) (.bvar 0)) .default)).runPure st ⟨L, [lS], F, C⟩
      ⟨decls0', view0⟩ ⟨1⟩ =
      .ok ((.lambda (binderNameOf `z) (_root_.abstract (pureFVar 1)
        (.app (.fvar (pureFVar 0)) (.fvar (pureFVar 1)))), st), ⟨2⟩) :=
  visitExpr_lam_run oracle_lamZ (body_app_run n _ _ _ st)

/-- Abstracting the two binders of `one`'s erased body gives `oneL`. -/
theorem abstract_oneL : LBTerm.lambda (binderNameOf `s) (_root_.abstract (pureFVar 0)
    (.lambda (binderNameOf `z) (_root_.abstract (pureFVar 1)
      (.app (.fvar (pureFVar 0)) (.fvar (pureFVar 1)))))) = oneL := rfl

/-- `one`'s value erases to `oneL` in the empty context, using the counter's first two variables. -/
theorem oneE_run (n : Nat) (L : LocalContext) (F : Option (Std.HashMap Name FVarId))
    (C : ErasureConfig) (st : ErasureState) :
    (visitExpr (m := PureM) (n + 8) oneE).runPure st ⟨L, [], F, C⟩ ⟨decls0', view0⟩ ⟨0⟩ =
      .ok ((oneL, st), ⟨2⟩) := by
  rw [← abstract_oneL]
  exact visitExpr_lam_run oracle_oneE (body_lamZ_run n _ _ _ st)

/-- The argument `fun a => a` erases to `λa. #0`, using the counter's third variable. -/
theorem arg_run (n : Nat) (L : LocalContext) (F : Option (Std.HashMap Name FVarId))
    (C : ErasureConfig) (st : ErasureState) :
    (visitExpr (m := PureM) (n + 3) (.lam `a tyA (.bvar 0) .default)).runPure st ⟨L, [], F, C⟩
      ⟨decls0', view0⟩ ⟨2⟩ = .ok ((.lambda (binderNameOf `a) (.bvar 0), st), ⟨3⟩) := by
  rw [show LBTerm.bvar 0 = _root_.abstract (pureFVar 2) (.fvar (pureFVar 2)) from rfl]
  exact visitExpr_lam_run (n := n + 1) oracle_lamA (visitExpr_fvar_run oracle_a)

/-- The traversal state after the run: `one` registered, with the λ□ environment `lenv0`. -/
def stRun : ErasureState :=
  { constants := (∅ : Std.HashMap Name Kername).insert `one (toKername `one), gdecls := lenv0 }

/-- `get_constant_kername` on `one` from the empty state registers `one` with its erased value. -/
theorem kername_one_run (n : Nat) (L : LocalContext) (C : ErasureConfig) (hC : C = {}) :
    (get_constant_kername (m := PureM) (n + 10) `one).runPure {} ⟨L, [], none, C⟩
      ⟨decls0', view0⟩ ⟨0⟩ = .ok ((toKername `one, stRun), ⟨2⟩) := by
  have h := visitMutual_one_run (tc := ⟨L, [], none, C⟩) hC (oneE_run n L none C {})
  exact get_constant_kername_run Std.HashMap.getElem?_empty h Std.HashMap.getElem?_insert_self

/-- The traversal on `e0` from the empty states returns `t0` with the state `stRun`, at every fuel
from 14 on. -/
theorem e0_run (n : Nat) :
    (visitExpr (m := PureM) (n + 14) e0).runPure {} { «config» := {} } ⟨decls0', view0⟩ {} =
      .ok ((t0, stRun), ⟨3⟩) :=
  visitExpr_constApp_run oracle_e0 rfl (kername_one_run n _ _ rfl) (arg_run (n + 7) _ _ _ _)

/-- The program `#erase` emits for NV-1: `lenv0` and the term `t0`. -/
def p0 : Program := .untyped lenv0 (some t0)

/-- The pure path on NV-1's closure returns `p0` and no constant to inline. Reference: `erase`
(`MR E/ErasureFunction.v:989`) and `erase_global_deps` (`MR E/ErasureFunction.v:1602`). -/
theorem hpure : erasePure view0 {} decls0' e0 = .ok (p0, []) := by
  rw [erasePure, show travFuel = (travFuel - 14) + 14 by decide, e0_run]
  rfl

/-- `#erase` on NV-1 returns `p0` and no constant to inline: the hypothesis `hrun` of
`erase_correct` on NV-1. Reference: the hypotheses `erase … = t'` and
`erase_global_deps … = Σ'` of `erase_correct` (`MR E/ErasureFunctionProperties.v:657`). -/
theorem hrun : eraseEntry view0 {} e0 = pure (p0, []) :=
  eraseEntry_of_erasePure hpure

/-! ## The final theorem on NV-1 -/

/-- `erase_correct` on NV-1: every hypothesis is a checked term (`henv`, `hview`, `he`, `hrun`,
`hev`), and its conclusion holds at the witnesses `lenv0`, `t0` (the program is `p0`) and
`v0' = λz. (λa. a) z`, the only witness (`witness`). Reference: `erase_correct`
(`MR E/ErasureFunctionProperties.v:657`). -/
theorem final : p0 = .untyped lenv0 (some t0) ∧
    Erases venv0 [] σ0.isAtom (RecIn lenv0) [] v0 v0' ∧ LBEval defaultFlags lenv0 t0 v0' := by
  obtain ⟨lenv, t, v', hp, hv, hlv⟩ := erase_correct henv hview he hrun hev
  simp only [p0, ASTType.untyped.injEq, Option.some.injEq] at hp
  obtain ⟨rfl, rfl⟩ := hp
  obtain rfl := witness ⟨hv, hlv⟩
  exact ⟨rfl, hv, hlv⟩

end EraseProof.Test.NV1
