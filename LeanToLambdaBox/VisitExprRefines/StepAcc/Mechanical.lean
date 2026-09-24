import LeanToLambdaBox.VisitExprRefines.MotivesAcc
import LeanToLambdaBox.VisitExprRefines.Step.Mechanical

/-!
# The mechanical steps of the accumulator induction

`doc/rework/12-REPAIRS-W9.md` §2.5's pass-through column at the six members whose bodies are
pure plumbing: the dispatcher, the spine loop, the two binder members, the spine dispatcher
and the alternative. None of them registers anything, so each is `AccGrows.trans` over the
sub-runs its body makes and `AccGrows.of_eq` at every primitive.

A sub-run's own state, registry and generator facts — what `BridgeInv` at the *next*
sub-run's entry state costs — are `RunRefines`' first three conjuncts, read at the shipping
member the approximation conjunct transports the sub-run to. That is what `ShippingMotives`
is for: `MotiveAccᵢ` concludes `AccGrows` alone.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean Erasure Witness Lean.Order

set_option synthInstance.maxSize 4000

section Steps

variable {lenv : Environment} {env : VEnv} {tbl : SourceTable} {cfg : ErasureConfig}
  {gw : Void IO.RealWorld → NameGenerator}

/-! ## Step 7 — `Erasure.visitAppArgs` -/

/-- **Step 7.** The spine loop: each iteration is one sub-run, and the accumulator composes
along the fold. The run facts carried beside it are what re-reads `BridgeInv` at the next
argument's entry state. -/
theorem stepAcc_visitAppArgs : StepAcc7 lenv env tbl cfg gw := by
  intro _P _A _htbl _hcfg _hcb M vExpr ih1
  refine ⟨?_, bodyLe7 ih1.2⟩
  have ih1le := ih1.2
  replace ih1 := ih1.1
  intro hd args s ctx cctx ref w t s' w' hrun Us Δ e hinv _hhd hargs
  simp only [visitAppArgsBody] at hrun
  have hmem : ∀ a ∈ args.toList, Supported env tbl a ∧ ∃ ve, TrExprS env Us Δ a ve := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    have hi' : i < args.size := by simpa using hi
    simpa using hargs i hi'
  have hP := run_array_foldlM_ok ctx cctx ref
    (P := fun _pre _acc s₁ w₁ =>
      AccGrows lenv env tbl s s₁ ∧ RunConcl s s₁ ∧ IndRegistryModelled env s₁ ∧ gw w ≤ gw w₁)
    ⟨AccGrows.rfl' _, RunConcl.rfl' _, hinv.indcanon, NameGenerator.LE.rfl⟩
    (fun pre x _post acc s₁ w₁ acc' s₂ w₂ hLpre hPacc hg => by
      rw [run_bind_ok] at hg
      obtain ⟨tx, s₃, w₃, hvx, hp⟩ := hg
      rw [run_pure] at hp
      cases hp
      obtain ⟨hacc, hrc, hreg, hle⟩ := hPacc
      obtain ⟨hsx, hex⟩ := hmem x (by rw [hLpre]; exact List.mem_append_right _ List.mem_cons_self)
      have hinv₁ := (hinv.mono_state hrc hreg).mono hle
      obtain ⟨hrc₂, hreg₂, hle₂, -⟩ :=
        M.motive1.1 _ _ _ _ _ _ _ _ _ (run_ok_of_le₁ ih1le hvx) _ Δ hinv₁ hsx hex
      exact ⟨hacc.trans (ih1 _ _ _ _ _ _ _ _ _ hvx _ Δ hinv₁ hsx hex),
        hrc.trans hrc₂, hreg₂, NameGenerator.LE.trans hle hle₂⟩)
    hrun
  exact hP.1

/-! ## Step 1 — `Erasure.visitExpr` -/

/-- **Step 1.** The relevance oracle leaves the state alone, and every arm is either a panic,
a `pure` or one member's sub-run. -/
theorem stepAcc_visitExpr : StepAcc1 lenv env tbl cfg gw := by
  intro P₀ A _htbl _hcfg _hcb _M vExpr vLit vLet vLam vProj vApp ih1 ih2 ih8 ih9 ih10 ih11
  refine ⟨?_, bodyLe1 ih1.2 ih2.2 ih8.2 ih9.2 ih10.2 ih11.2⟩
  replace ih1 := ih1.1
  replace ih2 := ih2.1
  replace ih8 := ih8.1
  replace ih9 := ih9.1
  replace ih10 := ih10.1
  replace ih11 := ih11.1
  intro e s ctx cctx ref w t s' w' hrun Us Δ hinv hsupp hex
  have P := P₀ Us
  simp only [visitExprBody] at hrun
  rw [run_read_bind, run_bind_ok] at hrun
  obtain ⟨c, s₁, w₁, horc, hk⟩ := hrun
  have hs₁ : s₁ = s := run_liftMetaM_state _ _ _ _ _ horc
  rw [hs₁] at horc hk
  have hle₁ : gw w ≤ gw w₁ := (P.oracle_refl e s ctx cctx ref w c s w₁ horc).1
  by_cases hc : c = true
  · subst hc
    rw [if_pos rfl, run_pure] at hk
    cases hk
    exact AccGrows.rfl' _
  · rw [if_neg hc] at hk
    have hinv' := hinv.mono hle₁
    have hnind : ∀ (c' : Name) (us' : List Level), e.getAppFn = .const c' us' →
        ∀ (iid : InductiveId) (np : Nat) (nfs : List Nat), ¬ IndInfo env c' iid np nfs := by
      obtain ⟨ve, hve⟩ := hex
      obtain ⟨m, mwf, hlctx, hvlctx⟩ := hinv.mlc
      refine A.eraser.oracle_informative (by rw [hinv.lparams]; exact mwf) hlctx
        (hvlctx ▸ hinv.kfresh)
        (show Erasure.liftMetaM (Erasure.isErasable ctx.lparams e) s ctx cctx ref w
            = .ok (false, s) w₁ from (Bool.not_eq_true c ▸ hc : c = false) ▸ horc)
        (by rw [hinv.lparams]; exact hvlctx ▸ hve)
    obtain ⟨hterm, hbodies, hkn⟩ := hsupp
    cases hterm with
    | @bvar i _ =>
      simp only [] at hk
      rw [run_panicWithPosWithDecl] at hk
      cases hk
      exact AccGrows.rfl' _
    | @fvar x _ =>
      simp only [] at hk
      rw [run_pure] at hk
      cases hk
      exact AccGrows.rfl' _
    | @sort u _ =>
      simp only [] at hk
      rw [run_panicWithPosWithDecl] at hk
      cases hk
      exact AccGrows.rfl' _
    | @forallE n ty b bi _ =>
      simp only [] at hk
      rw [run_panicWithPosWithDecl] at hk
      cases hk
      exact AccGrows.rfl' _
    | @mdata d b hb =>
      simp only [] at hk
      have hsub : ∀ n ∈ constNames b, n ∈ constNames (Expr.mdata d b) := fun _ h => h
      have hexb : ∃ ve, TrExprS env Us Δ b ve := by
        obtain ⟨ve, hve⟩ := hex; cases hve with | mdata h => exact ⟨_, h⟩
      exact ih1 _ _ _ _ _ _ _ _ _ hk _ Δ hinv'
        (Supported.subterm ⟨hb.mdata, hbodies, hkn⟩ hsub hb) hexb
    | @lam n ty b bi _ hb =>
      simp only [] at hk
      exact ih9 _ _ _ _ _ _ _ _ _ hk _ Δ n ty b bi hinv' rfl ⟨.lam hb, hbodies, hkn⟩ hex
    | @letE n ty v b nd _ hv hb =>
      simp only [] at hk
      exact ih8 _ _ _ _ _ _ _ _ _ hk _ Δ n ty v b nd hinv' rfl ⟨.letE hv hb, hbodies, hkn⟩ hex
    | @proj S i b _ I np nf hind hinf harity hi hb =>
      simp only [] at hk
      have hsub : ∀ n ∈ constNames b, n ∈ constNames (Expr.proj S i b) := fun _ h => h
      have hexb : ∃ ve, TrExprS env Us Δ b ve := by
        obtain ⟨ve, hve⟩ := hex; cases hve with | proj h _ => exact ⟨_, h⟩
      exact ih10 _ _ _ _ _ _ _ _ _ _ _ hk _ Δ I np nf hinv' hind hinf harity hi
        (Supported.subterm ⟨.proj hind hinf harity hi hb, hbodies, hkn⟩ hsub hb) hexb
    | @app f a _ ha hf =>
      simp only [] at hk
      exact ih11 _ _ _ _ _ _ _ _ _ hk _ Δ hinv' ⟨.app ha hf, hbodies, hkn⟩ hex hnind
    | @natLit n _ hpeano hidx =>
      simp only [] at hk
      exact ih2 _ _ _ _ _ _ _ _ _ hk _ Δ n hinv' rfl hpeano hidx
        ⟨.natLit hpeano hidx, hbodies, hkn⟩ hex
    | @const c us _ hplain hcases hrec hsat hknown =>
      simp only [] at hk
      exact ih11 _ _ _ _ _ _ _ _ _ hk _ Δ hinv'
        ⟨.const hplain hcases hrec hsat hknown, hbodies, hkn⟩ hex hnind
    | @casesApp c us _ minors I hplain hcases hind hinf harity hmin hlen htel =>
      simp only [] at hk
      exact ih11 _ _ _ _ _ _ _ _ _ hk _ Δ hinv'
        ⟨.casesApp hplain hcases hind hinf harity hmin hlen htel, hbodies, hkn⟩ hex hnind

/-! ## Steps 8 and 9 — the two binder members -/

/-- **Step 9.** One fresh identifier, one sub-run, one `Erasure.mkLambda`: the identifier and
the closing leave the state alone. -/
theorem stepAcc_visitLambda : StepAcc9 lenv env tbl cfg gw := by
  intro P₀ _A _htbl _hcfg _hcb _M vExpr ih1
  refine ⟨?_, bodyLe9 ih1.2⟩
  replace ih1 := ih1.1
  intro e s ctx cctx ref w t s' w' hrun Us Δ n ty b bi hinv he hsupp hex
  have P := P₀ Us
  subst he
  simp only [visitLambdaBody, Erasure.lambdaMonocular, Erasure.withLocalDecl] at hrun
  rw [run_bind_ok] at hrun
  obtain ⟨x, s₁, w₁, hfresh, hk⟩ := hrun
  obtain ⟨hnres, hxres, hle₁, hkres⟩ := P.fresh_names _ _ _ _ _ _ _ _ hfresh
  have hs₁ : s₁ = s := run_mkFreshFVarId_state _ _ _ _ _ hfresh
  rw [hs₁, run_withReader, run_bind_ok] at hk
  obtain ⟨tb, s₂, w₂, hvb, hm⟩ := hk
  obtain ⟨hs2, hw2, N, hteq⟩ := run_mkLambda_ok hm
  obtain ⟨hterm, hbodies, hkn⟩ := hsupp
  cases hterm with
  | @lam _ _ _ _ _ hb =>
  obtain ⟨ve, hve⟩ := hex
  cases hve with
  | lam hty' hty hbody =>
  have hx : x ∉ Δ.fvars := fun hmem => hnres (hinv.reserved x hmem)
  have hΔ' := TrLCtx.mkLocalDecl (n := n) (bi := bi) hinv.trlctx
    (hinv.trlctx.find?_eq_none.mpr hx) hty hty'
  have hinv' := hinv.mkLocalDecl (n := n) (bi := bi) hty hty' hx hnres hle₁ hxres hkres
  rw [Lean.Expr.instantiate1_eq] at hvb
  have hbext := TrExprS.inst_fvar P.envWF.ordered hΔ'.wf hbody
  have hsuppb : Supported env tbl b :=
    Supported.subterm ⟨.lam hb, hbodies, hkn⟩ (fun _ hd => hd) hb
  have hsuppb' : Supported env tbl (b.instantiate1' (.fvar x)) := by
    have := hsuppb.instantiate1 x; rwa [Lean.Expr.instantiate1_eq] at this
  have hacc := ih1 _ _ _ _ _ _ _ _ _ hvb _ _ hinv' hsuppb' ⟨_, hbext⟩
  subst hs2
  exact hacc

/-- **Step 8.** As step 9, with two sub-runs: the value's exit state is where the body's
`BridgeInv` is re-read. -/
theorem stepAcc_visitLet : StepAcc8 lenv env tbl cfg gw := by
  intro P₀ _A _htbl _hcfg _hcb M vExpr ih1
  refine ⟨?_, bodyLe8 ih1.2⟩
  have ih1le := ih1.2
  replace ih1 := ih1.1
  intro e s ctx cctx ref w t s' w' hrun Us Δ n ty v b nd hinv he hsupp hex
  have P := P₀ Us
  subst he
  simp only [visitLetBody, Erasure.letMonocular, Erasure.withLocalDef] at hrun
  rw [run_bind_ok] at hrun
  obtain ⟨x, s₁, w₁, hfresh, hk⟩ := hrun
  obtain ⟨hnres, hxres, hle₁, hkres⟩ := P.fresh_names _ _ _ _ _ _ _ _ hfresh
  have hs₁ : s₁ = s := run_mkFreshFVarId_state _ _ _ _ _ hfresh
  rw [hs₁, run_withReader, run_bind_ok] at hk
  obtain ⟨tv, s₂, w₂, hvv, hk2⟩ := hk
  rw [run_bind_ok] at hk2
  obtain ⟨tb, s₃, w₃, hvb, hm⟩ := hk2
  obtain ⟨hs3, hw3, N, hteq⟩ := run_mkLetIn_ok hm
  obtain ⟨hterm, hbodies, hkn⟩ := hsupp
  cases hterm with
  | @letE _ _ _ _ _ _ hsv hsb =>
  obtain ⟨ve, hve⟩ := hex
  cases hve with
  | letE hvt hty hval hbody =>
  have hx : x ∉ Δ.fvars := fun hmem => hnres (hinv.reserved x hmem)
  have hΔ' := TrLCtx.mkLetDecl (n := n) (nd := false) hinv.trlctx
    (hinv.trlctx.find?_eq_none.mpr hx) hty hval hvt
  have hinv' := hinv.mkLetDecl (n := n) hty hval hvt hx hnres hle₁ hxres hkres
  have hsuppv : Supported env tbl v :=
    Supported.subterm ⟨.letE hsv hsb, hbodies, hkn⟩ (fun _ hd => List.mem_append_left _ hd) hsv
  have hsuppb : Supported env tbl b :=
    Supported.subterm ⟨.letE hsv hsb, hbodies, hkn⟩ (fun _ hd => List.mem_append_right _ hd) hsb
  have hsuppb' : Supported env tbl (b.instantiate1' (.fvar x)) := by
    have := hsuppb.instantiate1 x; rwa [Lean.Expr.instantiate1_eq] at this
  have hvext := hval.weakFV P.envWF.ordered (.skip_fvar _ _ .refl) hΔ'.wf
  obtain ⟨hrcv, hregv, hle₂, -⟩ :=
    M.motive1.1 _ _ _ _ _ _ _ _ _ (run_ok_of_le₁ ih1le hvv) _ _ hinv' hsuppv ⟨_, hvext⟩
  have haccv := ih1 _ _ _ _ _ _ _ _ _ hvv _ _ hinv' hsuppv ⟨_, hvext⟩
  rw [Lean.Expr.instantiate1_eq] at hvb
  have hbext := TrExprS.inst_fvar P.envWF.ordered hΔ'.wf hbody
  have haccb :=
    ih1 _ _ _ _ _ _ _ _ _ hvb _ _ ((hinv'.mono_state hrcv hregv).mono hle₂) hsuppb' ⟨_, hbext⟩
  subst hs3
  exact haccv.trans haccb

/-! ## Step 11 — `Erasure.visitApp` -/

/-- **Step 11.** A constant head goes to `Erasure.visitConstApp`; any other head is erased on
its own and the spine is rebuilt by `Erasure.visitAppArgs`. -/
theorem stepAcc_visitApp : StepAcc11 lenv env tbl cfg gw := by
  intro _P _A _htbl _hcfg _hcb M vExpr vArgs vConstApp ih1 ih7 ih12
  refine ⟨?_, bodyLe11 ih1.2 ih7.2 ih12.2⟩
  have ih1le := ih1.2
  replace ih1 := ih1.1
  replace ih7 := ih7.1
  replace ih12 := ih12.1
  intro e s ctx cctx ref w t s' w' hrun Us Δ hinv hsupp hex hnind
  simp only [visitAppBody] at hrun
  cases hfn : e.getAppFn with
  | const cn us =>
    rw [hfn] at hrun
    simp only [] at hrun
    exact ih12 _ _ _ _ _ _ _ _ _ hrun _ Δ cn us hinv hfn hsupp hex (hnind cn us hfn)
  | _ =>
    all_goals (
      have hne : ∀ c us, e.getAppFn ≠ .const c us := by
        intro c us h; rw [hfn] at h; exact absurd h (by simp)
      obtain ⟨⟨hsuppfn, fve, htrfn⟩, hargs⟩ := spine_facts hsupp hex (hsupp.head hne)
      rw [hfn] at hrun
      simp only [] at hrun
      rw [Erasure.expr_withApp_eq, run_bind_ok] at hrun
      obtain ⟨tf, s₁, w₁, hvf, hk⟩ := hrun
      obtain ⟨hrc₁, hreg₁, hle₁, hf⟩ :=
        M.motive1.1 _ _ _ _ _ _ _ _ _ (run_ok_of_le₁ ih1le hvf) _ Δ hinv hsuppfn ⟨fve, htrfn⟩
      have hacc₁ := ih1 _ _ _ _ _ _ _ _ _ hvf _ Δ hinv hsuppfn ⟨fve, htrfn⟩
      exact hacc₁.trans (ih7 _ _ _ _ _ _ _ _ _ _ hk _ Δ e.getAppFn
        ((hinv.mono_state hrc₁ hreg₁).mono hle₁) hf hargs))

/-! ## Step 12 — `Erasure.visitConstApp` -/

/-- **Step 12.** The head's classification picks the arm; the two lookups that classify it
leave the state alone. The plain-constant arm is the only one with two sub-runs, and the
head's refinement — `Erasure.visitAppArgs`' own premise — is `Motive4`'s at the shipping
member. -/
theorem stepAcc_visitConstApp (hsafe : TableSafe lenv tbl) :
    StepAcc12 lenv env tbl cfg gw := by
  intro P₀ _A htbl _hcfg _hcb M vConst vArgs vCtorEta vCasesEta ih4 ih7 ih13 ih15
  refine ⟨?_, bodyLe12 ih4.2 ih7.2 ih13.2 ih15.2⟩
  have ih4le := ih4.2
  replace ih4 := ih4.1
  replace ih7 := ih7.1
  replace ih13 := ih13.1
  replace ih15 := ih15.1
  intro e s ctx cctx ref w t s' w' hrun Us Δ cn us hinv hfn hsupp hex hnind
  have P := P₀ Us
  have hargs := spine_args_ok hsupp hex
  have hheadS : SupportedTm env tbl (.const cn us) e.getAppArgs.toList := by
    have hsuppS : SupportedTm env tbl (e.getAppArgs.toList.foldl Expr.app e.getAppFn) [] := by
      rw [getAppArgs_spine]; exact hsupp.term
    have := (supportedTm_foldl_app_inv hsuppS).1
    rw [hfn] at this
    simpa using this
  simp only [visitConstAppBody] at hrun
  rw [Erasure.expr_withApp_eq, hfn] at hrun
  simp only [] at hrun
  rw [run_bind_ok] at hrun
  obtain ⟨o, s₁, w₁, hcs, hk⟩ := hrun
  rw [run_liftCoreM_ok] at hcs
  obtain ⟨hcs, rfl⟩ := hcs
  have hlecs : gw w ≤ gw w₁ := (P.lookup_adequate.casesInfo cn cctx ref w o w₁ hcs).1
  cases o with
  | some ci =>
    obtain ⟨hcname, hdecl, hagreeK⟩ :=
      (P.lookup_adequate.casesInfo cn cctx ref w _ w₁ hcs).2.1 ci rfl
    simp only [] at hk
    cases hheadS with
    | const hplain hcases _ _ _ => rw [hcname] at hcases; exact absurd hcases (by simp)
    | @casesApp _ _ _ minors I hplain hcases hind hinf harity hmin hlen htel =>
      have hag : CasesInfoAgrees ci cn I := CasesInfoAgrees.of_pinned htbl hind hdecl hagreeK
      have hcasesHead : CasesHead env tbl ci cn I := ⟨hplain, hcname, hind, hinf, hag⟩
      have hsat : ci.arity ≤ e.getAppArgs.size := by
        rw [hag.arity]; simpa using harity
      exact ih15 _ _ _ _ _ _ _ _ _ _ hk _ Δ cn us I (hinv.mono hlecs)
        hfn hcasesHead hsat hsupp hargs hex
  | none =>
    have hnc : isCasesOnName cn = false :=
      (P.lookup_adequate.casesInfo cn cctx ref w _ w₁ hcs).2.2 rfl
    simp only [] at hk
    rw [run_bind_ok] at hk
    obtain ⟨o₂, s₂, w₂, hct, hk⟩ := hk
    rw [run_liftCoreM_ok] at hct
    obtain ⟨hct, rfl⟩ := hct
    have hlect : gw w₁ ≤ gw w₂ := (P.lookup_adequate.ctorArity cn cctx ref w₁ o₂ w₂ hct).1
    cases hheadS with
    | casesApp _ hcases _ _ _ _ _ _ => rw [hnc] at hcases; exact absurd hcases (by simp)
    | @const _ _ _ hplain hcases hrec hsatT hknown =>
      cases o₂ with
      | some ar =>
        obtain ⟨cv, hcvf, harar⟩ :=
          (P.lookup_adequate.ctorArity cn cctx ref w₁ _ w₂ hct).2.1 ar rfl
        have hctor : ∃ I k, CtorOf env cn I k := ⟨_, _, P.block_adequate.ctor cn cv hcvf⟩
        have hcol : (ctorOf? tbl cn).isSome := by
          cases hknown with
          | indType hind _ =>
            obtain ⟨iv, hiv, -⟩ := htbl.inds _ _ (mem_of_lookup hind)
            rw [hcvf] at hiv; exact absurd hiv (by simp)
          | ctor hc _ => rw [hc]; rfl
          | defn hd _ => exact hsafe.declCtor cn cv (by rw [hd]; rfl) hcvf
        obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hcol
        obtain ⟨cv', hcvf', hnp, hnf⟩ := ctorOf?_pinned htbl hp
        obtain rfl : cv' = cv := by simpa using hcvf'.symm.trans hcvf
        have harp : ar ≤ p.2.numParams + p.2.numFields :=
          Nat.le_of_eq (by rw [harar, hnp, hnf])
        have hsat : ar ≤ e.getAppArgs.size := by
          have := hsatT p hp
          simpa using Nat.le_trans harp this
        simp only [] at hk
        exact ih13 _ _ _ _ _ _ _ _ _ _ _ hk _ Δ us
          (hinv.mono (NameGenerator.LE.trans hlecs hlect)) hfn hctor hsat hargs
      | none =>
        have hnoctor : ∀ (I : Name) (k : Nat), ¬ CtorOf env cn I k := by
          intro I k hck
          obtain ⟨cv, hcvf, -, -⟩ := P.block_adequate.ctorBwd cn I k hck
          exact (P.lookup_adequate.ctorArity cn cctx ref w₁ _ w₂ hct).2.2 rfl cv hcvf
        have hnone : ctorOf? tbl cn = none := by
          cases hcc : ctorOf? tbl cn with
          | none => rfl
          | some p =>
            obtain ⟨cv, hcvf, -, -⟩ := ctorOf?_pinned htbl hcc
            exact absurd hcvf
              ((P.lookup_adequate.ctorArity cn cctx ref w₁ _ w₂ hct).2.2 rfl cv)
        have hheadNil : SupportedTm env tbl (.const cn us) [] :=
          .const hplain hcases hrec (fun p hp => by rw [hnone] at hp; exact absurd hp (by simp))
            hknown
        have hsubf : ∀ d ∈ constNames (Expr.const cn us), d ∈ constNames e := by
          obtain ⟨hsubf, -⟩ := constNames_spine_sub e.getAppArgs.toList e.getAppFn
          rw [getAppArgs_spine] at hsubf
          rw [← hfn]
          exact hsubf
        have hheadSupp : Supported env tbl (.const cn us) := hsupp.subterm hsubf hheadNil
        simp only [] at hk
        rw [run_bind_ok] at hk
        obtain ⟨tc, s₃, w₃, hvc, hk⟩ := hk
        have hinv₂ := hinv.mono (NameGenerator.LE.trans hlecs hlect)
        obtain ⟨hrc₃, hreg₃, hle₃, hmc⟩ :=
          M.motive4.1 _ _ _ _ _ _ _ _ _ (run_ok_of_le₁ ih4le hvc) _ Δ cn us hinv₂ rfl
            hplain hcases hknown hheadSupp hnoctor hnind
        have hacc₃ := ih4 _ _ _ _ _ _ _ _ _ hvc _ Δ cn us hinv₂ rfl hplain hcases hknown
          hheadSupp hnoctor hnind
        exact hacc₃.trans (ih7 _ _ _ _ _ _ _ _ _ _ hk _ Δ (.const cn us)
          ((hinv₂.mono_state hrc₃ hreg₃).mono hle₃) hmc hargs)

/-! ## Step 18 — `Erasure.visitAlt` -/

/-- **Step 18.** `Erasure.lambdaOrIntroToArity` opens the binders without touching the state,
and `Erasure.mkAlt` closes the body the one sub-run produced. -/
theorem stepAcc_visitAlt : StepAcc18 lenv env tbl cfg gw := by
  intro P₀ _A _htbl _hcfg _hcb _M vExpr ih1
  refine ⟨?_, bodyLe18 ih1.2⟩
  replace ih1 := ih1.1
  intro nf mask e s ctx cctx ref w r s' w' hrun Us Δ hinv hmask hlam hsupp hex
  have P := P₀ Us
  simp only [visitAltBody] at hrun
  rw [run_bind_ok] at hrun
  obtain ⟨ty, s₁, w₁, hity, hk⟩ := hrun
  have hs₁ : s₁ = s := run_liftMetaM_state _ _ _ _ _ hity
  rw [hs₁] at hity hk
  obtain ⟨hlei, hfml⟩ := P.prim_monotone.inferType e s ctx cctx ref w ty s w₁ hity
  obtain ⟨ys, Ns, efin, Δ', ctx', w₂, hlen, hnlen, hle₂, hfx, hyfresh, hinv', hsupp', hex',
    hK, hclose⟩ := bridge_alt_telescope P cctx ref nf e ty Δ _ s ctx w₁ r s' w' hk
      (hinv.mono hlei) hlam hsupp hex hfml
  rw [hmask, filter_replicate_keep_of_size nf ys.toArray (by simp [hlen]), List.toList_toArray,
    run_bind_ok] at hK
  obtain ⟨tb, s₂, w₃, hvb, hm⟩ := hK
  obtain ⟨hs2, hw2, hrlen, hr2⟩ := run_mkAlt_ok hm
  have hacc := ih1 _ _ _ _ _ _ _ _ _ hvb _ Δ' hinv' hsupp' hex'
  subst hs2
  exact hacc

end Steps

end LeanToLambdaBox
