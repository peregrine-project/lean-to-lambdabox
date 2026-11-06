import EraseProof.Core.Steps
import EraseProof.Core.CollectSpec
import EraseProof.Statements

/-!
# The pure traversal's correctness, from the steps of its special cases

`erasePure_erases` follows by induction on the fuel of `Erasure.visitExpr` at the pure backend
from one step lemma per case of `visitExpr` (`Core/Steps.lean`). This module states the steps of
the cases that `visitExpr` sends to special code, as the explicit hypothesis `StepsB`: an
application or a constant whose head is a constructor (`visitConstApp`'s `ctorArity?` branch,
`withAppEtaToMinArity` and `visitConstructor`) or a recognized `casesOn` constant (`visitCases`,
`visitCasesOn`, `visitAlt`), a projection (`visitProj`) and a literal (`visitLiteral`). From
`StepsB` and the steps of `Core/Steps.lean` it builds the induction hypothesis `StepIH` at every
fuel (`stepIH_of_stepsB`), derives the closure facts `CoreEnv` from the fragment test
(`coreEnv_of_collectDeps`), and concludes `erasePure_erases_statement`
(`erasePure_erases_of_stepsB`).

Reference: `erases_erase` (`MR E/ErasureFunction.v:1228`), by induction over `erase`
(`MR E/ErasureFunction.v:989`), with `erase_global_erases_deps`
(`MR E/ErasureFunctionProperties.v:172`).
-/

open Lean Erasure
open Metalean (EnvWF)

namespace EraseProof

namespace Steps

/-- The steps of the cases of `visitExpr` that call special code, each in the shape of the steps
of `Core/Steps.lean`: from the closure facts (`CoreEnv`) and the induction hypothesis at `fuel`
(`StepIH`), `ExprSpec` at `fuel + 1` on
* `ctor`: an application or a constant whose head is a constructor (`ctorArity?`) and not a
  recognized `casesOn` constant: `visitConstApp`'s constructor branch, η-expanded to the
  constructor's arity (`withAppEtaToMinArity`) and erased by `visitConstructor`;
* `cases`: an application or a constant whose head is a recognized `casesOn` constant
  (`casesInfo?`): `visitConstApp`'s `casesOn` branch, η-expanded to the `casesOn`'s arity and
  erased by `visitCases`, `visitCasesOn` and `visitAlt`;
* `proj`: a projection (`visitProj`);
* `lit`: a literal (`visitLiteral`).
Reference: the `tConstruct`, `tCase`, `tProj` cases of `erases_erase`
(`MR E/ErasureFunction.v:1228`), rules `erases_tConstruct`, `erases_tCase`, `erases_tProj`
(`MR E/Extract.v:106,111,118`). -/
structure StepsB : Prop where
  ctor : ∀ {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P decls : List ConstantInfo}
    {view : EnvView} {cfg : ErasureConfig} {fuel : Nat} {e : Expr} {c : Name} {us : List Level}
    {k : Nat},
    CoreEnv E B P decls view cfg → StepIH E B view cfg decls fuel →
    e.getAppFn = .const c us → casesInfo? decls c = none → ctorArity? decls c = some k →
    ExprSpec E B view cfg decls (fuel + 1) e
  cases : ∀ {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P decls : List ConstantInfo}
    {view : EnvView} {cfg : ErasureConfig} {fuel : Nat} {e : Expr} {c : Name} {us : List Level}
    {ci : CasesInfo},
    CoreEnv E B P decls view cfg → StepIH E B view cfg decls fuel →
    e.getAppFn = .const c us → casesInfo? decls c = some ci →
    ExprSpec E B view cfg decls (fuel + 1) e
  proj : ∀ {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P decls : List ConstantInfo}
    {view : EnvView} {cfg : ErasureConfig} {fuel : Nat} {s : Name} {i : Nat} {b : Expr},
    CoreEnv E B P decls view cfg → StepIH E B view cfg decls fuel →
    ExprSpec E B view cfg decls (fuel + 1) (.proj s i b)
  lit : ∀ {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P decls : List ConstantInfo}
    {view : EnvView} {cfg : ErasureConfig} {fuel : Nat} {l : Literal},
    CoreEnv E B P decls view cfg → StepIH E B view cfg decls fuel →
    ExprSpec E B view cfg decls (fuel + 1) (.lit l)

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P decls : List ConstantInfo}
  {view : EnvView} {cfg : ErasureConfig}

/-- An application or a constant, by its head: a recognized `casesOn` constant (`StepsB.cases`), a
constructor (`StepsB.ctor`), or another head (`visitExpr_app_step`, `visitExpr_const_step`). -/
theorem exprSpec_appLike (h : StepsB) (hG : CoreEnv E B P decls view cfg) {fuel : Nat}
    (ih : StepIH E B view cfg decls fuel) {e : Expr}
    (hplain : (∀ c us, e.getAppFn = .const c us →
      casesInfo? decls c = none ∧ ctorArity? decls c = none) →
      ExprSpec E B view cfg decls (fuel + 1) e) :
    ExprSpec E B view cfg decls (fuel + 1) e := by
  by_cases hc : ∃ c us, e.getAppFn = .const c us
  · obtain ⟨c, us, hc⟩ := hc
    cases hci : casesInfo? decls c with
    | some ci => exact h.cases hG ih hc hci
    | none =>
      cases hca : ctorArity? decls c with
      | some k => exact h.ctor hG ih hc hci hca
      | none =>
        refine hplain fun c' us' h' => ?_
        rw [hc] at h'
        cases h'
        exact ⟨hci, hca⟩
  · exact hplain fun c us h' => absurd ⟨c, us, h'⟩ hc

/-- `ExprSpec` at `fuel + 1`, case by case over `visitExpr`. -/
theorem exprSpec_succ (h : StepsB) (hG : CoreEnv E B P decls view cfg) {fuel : Nat}
    (ih : StepIH E B view cfg decls fuel) : ∀ e, ExprSpec E B view cfg decls (fuel + 1) e
  | .bvar _ => visitExpr_fail_step hG rfl
  | .sort _ => visitExpr_fail_step hG rfl
  | .forallE .. => visitExpr_fail_step hG rfl
  | .mvar _ => visitExpr_fail_step hG rfl
  | .fvar _ => visitExpr_fvar_step hG
  | .mdata .. => visitExpr_mdata_step hG ih
  | .lam .. => visitExpr_lam_step hG ih
  | .letE .. => visitExpr_letE_step hG ih
  | .lit _ => h.lit hG ih
  | .proj .. => h.proj hG ih
  | .app .. => exprSpec_appLike h hG ih fun hp => visitExpr_app_step hG ih hp
  | .const c us => exprSpec_appLike h hG ih fun hp => visitExpr_const_step hG ih (hp c us rfl)

/-- The induction hypothesis of the steps holds at every fuel: at `0` every run fails, and at
`fuel + 1` it follows from the steps (`exprSpec_succ`, `visitMutual_step`). Reference: the
induction of `erases_erase` (`MR E/ErasureFunction.v:1228`), on the fuel of the shipping
traversal. -/
theorem stepIH_of_stepsB (h : StepsB) (hG : CoreEnv E B P decls view cfg) :
    ∀ fuel, StepIH E B view cfg decls fuel
  | 0 => by
    refine ⟨fun m hm e => ?_, fun m hm c => ?_⟩
    · obtain rfl := Nat.le_zero.1 hm
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrun
      rw [visitExpr] at hrun; cases hrun
    · obtain rfl := Nat.le_zero.1 hm
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrun
      rw [visitMutual] at hrun; cases hrun
  | fuel + 1 =>
    have ih := stepIH_of_stepsB h hG fuel
    ⟨fun m hm e => (Nat.lt_or_eq_of_le hm).elim (fun hm => ih.expr m (by omega) e)
        (fun hm => hm ▸ exprSpec_succ h hG ih e),
      fun m hm c => (Nat.lt_or_eq_of_le hm).elim (fun hm => ih.mutDecl m (by omega) c)
        (fun hm => hm ▸ visitMutual_step hG ih)⟩

end

/-! ## The closure facts from the fragment test -/

section
open CollectSub CollectSpec
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P decls : List ConstantInfo}

/-- A successful `exprConsts` under `nat := .machine` leaves no Nat literal, `Nat.zero` or
`Nat.casesOn` in the term. -/
theorem exprConsts_natPlain {cfg : ErasureConfig} : ∀ {e : Expr} {cs : List Name},
    exprConsts cfg e = .ok cs → NatPlain cfg e
  | .bvar _, _, _ | .sort _, _, _ | .lit (.strVal _), _, _ | .fvar _, _, _ | .mvar _, _, _ => trivial
  | .lit (.natVal _), _, h => by
    cases hn : cfg.nat with
    | peano => exact hn
    | machine => rw [exprConsts, hn] at h; cases h
  | .const c _, cs, h => by
    rw [exprConsts] at h
    intro hm
    split at h
    · cases h
    · rw [hm] at h
      dsimp only at h
      split at h
      · cases h
      · rename_i hnc
        refine ⟨fun h' => hnc ?_, fun h' => hnc ?_⟩ <;> simp [h']
  | .app f a, cs, h => by
    rw [exprConsts] at h
    obtain ⟨xs, hf, h⟩ := OracleWhnf.ok_of_bind h
    obtain ⟨ys, ha, -⟩ := OracleWhnf.ok_of_bind h
    exact ⟨exprConsts_natPlain hf, exprConsts_natPlain ha⟩
  | .lam _ t b _, cs, h | .forallE _ t b _, cs, h => by
    rw [exprConsts] at h
    obtain ⟨xs, ht, h⟩ := OracleWhnf.ok_of_bind h
    obtain ⟨ys, hb, -⟩ := OracleWhnf.ok_of_bind h
    exact ⟨exprConsts_natPlain ht, exprConsts_natPlain hb⟩
  | .letE _ t v b _, cs, h => by
    rw [exprConsts] at h
    obtain ⟨xs, ht, h⟩ := OracleWhnf.ok_of_bind h
    obtain ⟨ys, hv, h⟩ := OracleWhnf.ok_of_bind h
    obtain ⟨zs, hb, -⟩ := OracleWhnf.ok_of_bind h
    exact ⟨exprConsts_natPlain ht, exprConsts_natPlain hv, exprConsts_natPlain hb⟩
  | .mdata _ e, cs, h => by
    rw [exprConsts] at h
    exact exprConsts_natPlain (e := e) h
  | .proj _ _ e, cs, h => by
    rw [exprConsts] at h
    obtain ⟨xs, he, -⟩ := OracleWhnf.ok_of_bind h
    exact exprConsts_natPlain (e := e) he

/-- The term and every expression the traversal reads from the fragment test's closure are
`NatPlain`: `Erasure.exprConsts` excludes Nat literals, `Nat.zero` and `Nat.casesOn` under
`nat := .machine` and scans each of them. Reference: none. -/
theorem collectDeps_natPlain {lps : List Name} {e : Expr} {t : Metalean.Expr ζ lps.length 0}
    {view : EnvView} {cfg : ErasureConfig} (henv : ProgEnv P ζ E B)
    (hview : ViewAgrees view P) (he : TrM E B lps .nil [] e t)
    (h : collectDeps view cfg e = .ok decls) :
    NatPlain cfg e ∧ ∀ ci ∈ decls, ∀ x, ReadExpr decls ci x → NatPlain cfg x := by
  obtain ⟨cs, cases, hcs, hcl, -, -, -⟩ := CollectSpec.collectDeps_ok h
  obtain ⟨hsub, -, -, -, -, hscan⟩ := closure_ok henv hview hcl nofun
    ((TrM.namesIn henv he).exprConsts hcs) List.nodup_nil nofun
  have hr : Run P view cfg decls cases := ⟨ProgEnv.names_closed henv, hview, hsub, hscan⟩
  refine ⟨exprConsts_natPlain hcs, fun ci hci x hx => ?_⟩
  obtain ⟨xs, hxs, -⟩ := hr.read hci hx
  exact exprConsts_natPlain hxs

/-- Under `remove_irrel_constr_args` the fragment test's closure has no inductive type. -/
theorem collectDeps_irr {e : Expr} {view : EnvView} {cfg : ErasureConfig}
    (h : collectDeps view cfg e = .ok decls) :
    ∀ iv, (∃ ci ∈ decls, ci = .inductInfo iv) → cfg.remove_irrel_constr_args = false := by
  rintro iv ⟨ci, hci, rfl⟩
  unfold collectDeps at h
  obtain ⟨cs, hcs, h⟩ := OracleWhnf.ok_of_bind h
  obtain ⟨⟨ds, cases⟩, hcl, h⟩ := OracleWhnf.ok_of_bind h
  dsimp only at h
  cases hirr : cfg.remove_irrel_constr_args
  · rfl
  exfalso
  simp only [hirr, ite_true] at h
  repeat' (first | (cases h; done) | split at h)
  rename_i _ _ _ hf _ _ _ _
  cases h
  have key : ∀ {p : ConstantInfo → Bool} {l : List ConstantInfo},
      (∀ iv, l.find? p = some (.inductInfo iv) → False) →
      (∀ y, p y = true → ∃ iv, y = .inductInfo iv) → ∀ x ∈ l, p x = false := by
    intro p l hf hp x hx
    cases hy : l.find? p with
    | none => simpa using List.find?_eq_none.1 hy x hx
    | some y =>
      obtain ⟨iv, rfl⟩ := hp _ (List.find?_some hy)
      exact (hf iv hy).elim
  have := key hf (fun y hy => by cases y <;> first | exact ⟨_, rfl⟩ | cases hy) _ hci
  cases this

/-- The block members of a declaration of a program are the declaration itself or inductive types
of the program: definitions, theorems, opaques, axioms, constructors and quotients are alone in
their blocks, and the block of an inductive type or a recursor lists the block's inductive types.
-/
theorem ProgEnv.ownBlock (h : ProgEnv P ζ E B) : ∀ ci ∈ P, ∀ n ∈ ci.all,
    n = ci.name ∨ ∃ iv, ConstantInfo.inductInfo iv ∈ P ∧ iv.name = n := by
  induction h with
  | nil => intro ci hci; cases hci
  | «axiom» _ _ _ _ _ ih =>
    intro ci hci n hn
    rcases List.mem_cons.1 hci with rfl | hci
    · simp only [ConstantInfo.all, List.mem_singleton] at hn; exact .inl hn
    · exact (ih ci hci n hn).imp_right fun ⟨iv, hm, hn⟩ => ⟨iv, List.mem_cons_of_mem _ hm, hn⟩
  | defn _ _ _ _ hall _ _ ih =>
    intro ci hci n hn
    rcases List.mem_cons.1 hci with rfl | hci
    · simp only [ConstantInfo.all, hall, List.mem_singleton] at hn; exact .inl hn
    · exact (ih ci hci n hn).imp_right fun ⟨iv, hm, hn⟩ => ⟨iv, List.mem_cons_of_mem _ hm, hn⟩
  | thm _ _ _ hall _ _ _ ih =>
    intro ci hci n hn
    rcases List.mem_cons.1 hci with rfl | hci
    · simp only [ConstantInfo.all, hall, List.mem_singleton] at hn; exact .inl hn
    · exact (ih ci hci n hn).imp_right fun ⟨iv, hm, hn⟩ => ⟨iv, List.mem_cons_of_mem _ hm, hn⟩
  | «opaque» _ _ _ _ hall _ _ _ ih =>
    intro ci hci n hn
    rcases List.mem_cons.1 hci with rfl | hci
    · simp only [ConstantInfo.all, hall, List.mem_singleton] at hn; exact .inl hn
    · exact (ih ci hci n hn).imp_right fun ⟨iv, hm, hn⟩ => ⟨iv, List.mem_cons_of_mem _ hm, hn⟩
  | @induct _ P _ _ _ _ _ _ Is Cs Rs _ _ _ _ _ _ hblk _ ih =>
    intro ci hci n hn
    rcases List.mem_append.1 hci with hm | hci
    · rcases IndBlock.mem_decls hm with ⟨s, rfl⟩ | ⟨s, k, rfl⟩ | ⟨s, rfl⟩
      · simp only [ConstantInfo.all, List.mem_singleton] at hn; exact .inl hn
      · simp only [ConstantInfo.all, List.mem_singleton] at hn; exact .inl hn
      · simp only [ConstantInfo.all, (hblk.ind s).2.2.1, List.mem_ofFn] at hn
        obtain ⟨u, rfl⟩ := hn
        exact .inr ⟨Is u, List.mem_append_left _ (block_mem.2.2 u), rfl⟩
    · exact (ih ci hci n hn).imp_right fun ⟨iv, hm, hn⟩ => ⟨iv, List.mem_append_right _ hm, hn⟩
  | quot _ _ _ _ _ _ _ ih =>
    intro ci hci n hn
    rcases List.mem_append.1 hci with hm | hci
    · obtain ⟨q, -, rfl⟩ := List.mem_map.1 hm
      simp only [ConstantInfo.all, List.mem_singleton] at hn; exact .inl hn
    · exact (ih ci hci n hn).imp_right fun ⟨iv, hm, hn⟩ => ⟨iv, List.mem_append_right _ hm, hn⟩

/-- The closure of a program has `OwnBlockValues` (`ProgEnv.ownBlock`). -/
theorem ownBlockValues (henv : ProgEnv P ζ E B) (hsub : SubEnv decls P) : OwnBlockValues decls := by
  intro ci hci n hn
  rcases ProgEnv.ownBlock henv ci (findDecl_eq_some (hsub ci hci)).1 n hn with h | ⟨iv, hm, hiv⟩
  · exact .inl h
  · refine .inr fun ci' hci' => ?_
    obtain ⟨hm', hn'⟩ := findDecl_eq_some (c := n) (show findDecl decls n = some ci' from hci')
    have hP := (findDecl_eq_some (hsub ci' hm')).1
    have := List.inj_on_of_nodup_map (ProgEnv.fresh henv) hP hm (hn'.trans hiv.symm)
    subst this
    rfl

/-- The closure of a program has `NoIndexFields`: `PhaseIDecl` excludes index fields in the
constructors of an inductive whose `casesOn` is recognized, and a constructor has its
inductive's parameter count (`ProgEnv.lookup_ind_ctor`). -/
theorem noIndexFields {view : EnvView} {cfg : ErasureConfig} (henv : ProgEnv P ζ E B)
    (hsub : SubEnv decls P) (hph : ∀ ci ∈ decls, PhaseIDecl view cfg decls ci) :
    NoIndexFields decls := by
  intro n ci iv hci hT cn hcn cv hcv
  obtain ⟨T, I, rfl, hind, -, -, -⟩ := casesInfo?_name hci
  rw [hind] at hT
  have hT' : findDecl decls T = some (.inductInfo iv) := hT
  obtain ⟨hm, hTn⟩ := findDecl_eq_some hT'
  have hcas : (EvalEnv.casesOn? ⟨decls, fun _ => false⟩ (.str iv.name "casesOn")).isSome := by
    have hTn' : iv.name = T := hTn
    simp only [EvalEnv.casesOn?, hTn', hci, hind, hT']
    rfl
  have hcv' : findDecl decls cn = some (.ctorInfo cv) := hcv
  have hidx := (hph _ hm).2.2.2 hcas cn hcn cv hcv'
  have hTP : findDecl P iv.name = some (.inductInfo iv) := hsub _ hm
  obtain ⟨hcm, hcn'⟩ := findDecl_eq_some hcv'
  have hcP : findDecl P cn = some (.ctorInfo cv) := hcn' ▸ hsub _ hcm
  obtain ⟨ι, η, s, k, o, hBT, hBc⟩ := ProgEnv.lookup_ind_ctor henv hTP hcn
  obtain ⟨ι', η', s', hBT', hnp, -⟩ := ProgEnv.lookup_ind henv hTP
  obtain ⟨ι'', η'', s'', k'', o'', hBc', -, hnp', -⟩ := ProgEnv.lookup_ctor henv hcP
  have e1 := hBT.symm.trans hBT'
  have e2 := hBc.symm.trans hBc'
  cases e1
  cases e2
  rw [hnp, ← hnp']
  exact hidx

/-- The closure facts of the fragment test's closure (`collectDeps_spec`, `collectDeps_sub`,
`collectDeps_machineFree`, `collectDeps_natPlain`, `ownBlockValues`, `noIndexFields`,
`collectDeps_irr`). Reference: the hypotheses of `erases_erase` (`MR E/ErasureFunction.v:1228`). -/
theorem coreEnv_of_collectDeps {lps : List Name} {e : Expr} {t : Metalean.Expr ζ lps.length 0}
    {view : EnvView} {cfg : ErasureConfig} (henv : ProgEnv P ζ E B) (hwf : EnvWF E)
    (hview : ViewAgrees view P) (he : TrM E B lps .nil [] e t)
    (h : collectDeps view cfg e = .ok decls) : CoreEnv E B P decls view cfg := by
  obtain ⟨hinj, -, -, hdeps, hcl, -, hph, ⟨-, hrf⟩, hbn, har⟩ := collectDeps_spec henv hview he h
  have hsub := collectDeps_sub henv hview he h
  exact ⟨henv, hwf, hsub, hinj, hbn, hcl, hdeps, (collectDeps_machineFree henv hview he h).2,
    (collectDeps_natPlain henv hview he h).2, ownBlockValues henv hsub, noIndexFields henv hsub hph,
    hph, hrf, har, collectDeps_irr h⟩

end

end Steps

open Steps in
/-- `erasePure_erases`, given the steps of the special cases of the traversal (`StepsB`): the
induction hypothesis at the traversal's fuel (`stepIH_of_stepsB`) on the closure facts of the
fragment test (`coreEnv_of_collectDeps`), applied in the empty context, from the empty state, with
the closure's names as the scope. Reference: `erase_correct`, its erasure part
(`MR E/ErasureFunctionProperties.v:172`, `MR E/ErasureFunction.v:1309`). -/
theorem erasePure_erases_of_stepsB (h : StepsB) : erasePure_erases_statement := by
  intro ζ E B P decls lps e view cfg p inl henv hwf hview t he hty hcol hrun
  have hG := coreEnv_of_collectDeps henv hwf hview he hcol
  obtain ⟨-, -, -, -, -, hcE, -, ⟨hrfE, -⟩, -, -⟩ := collectDeps_spec henv hview he hcol
  unfold erasePure at hrun
  obtain ⟨⟨⟨r, st'⟩, ps'⟩, hvis, hret⟩ := OracleWhnf.ok_of_bind hrun
  cases hret
  have hctx : CtxOK E B lps (.nil : Metalean.Ctx ζ lps.length 0 0) [] cfg { «config» := cfg } {} :=
    ⟨.nil, fun _ h => (nomatch h), fun _ => rfl, fun _ _ => rfl, rfl, rfl⟩
  have hsc : ScopeOK decls (fun d => (findDecl decls d).isSome) := fun c hc => by
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.1 hc
    exact ⟨ci, hci, fun v hv hthm hcs d hd =>
      ConstsIn.nameOccurs (hG.value_consts hci hv hthm hcs).1 hd⟩
  obtain ⟨her, hdeps, hgr⟩ := (stepIH_of_stepsB h hG travFuel).expr travFuel (Nat.le_refl _) e hctx
    hsc (fun d hd => ConstsIn.nameOccurs hcE hd) (collectDeps_machineFree henv hview he hcol).1
    (collectDeps_natPlain henv hview he hcol).1 hrfE StateOK.empty he hty hvis
  exact ⟨_, _, rfl, her, hdeps, hgr.inv.closed⟩

end EraseProof
