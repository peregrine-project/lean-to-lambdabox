import LeanToLambdaBox.ErasesCorrect.Steps

/-!
# The simulation, and the arms that are not step lemmas

`erases_correct_of_steps` is `erases_correct`'s statement with the ι, projection and δ arms
taken as hypotheses. It is proved by one induction on `SEval`, at the emitted environment,
and the eight remaining arms are discharged here:

* `sort`, `forallE` — a type erases to `□` and evaluates to itself;
* `lam` — a λ is a value on both sides, whether its image is a λ or a block's `.fix` node;
* `lit` — the literal's one-step unfolding, at the same image;
* `zeta` — the `let` congruence, with the two substitution transports;
* `beta` — the `.app` node's two `Lower` readings, the second refuted;
* `ctorVal` — a constructor spine within its arity, built by `construct_atom` and
  `construct_app`;
* `indVal` — an inductive-type-name spine, which has no head erasure and so boxes.

Besides the three step hypotheses the aggregator takes nothing: the forward readings
`ctorVal` and `beta` spend are clauses of `ErasesEnv` itself — `ErasesEnv.ctorArity` at the
reached block, `erases_elimSpine_no_value` at the under-applied eliminator spine — and the
kernel facts are fields of `UpstreamAsks`, which `erases_correct`'s statement already
binds.

`ErasesCorrect/Close.lean` discharges those hypotheses and states `erases_correct` itself;
the arm files import `ErasesCorrect/Steps.lean` and not this module, which is what keeps
the graph acyclic.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean


/-! ## The arms that are not step lemmas

Each is stated at the source rule's own subject, with the induction hypotheses as
`Simulates` premises, so that the induction in `erases_correct_of_steps` reads as one line
per arm.
-/

/-- **`indVal`.** An inductive-type-name spine has no head erasure — neither `ctor` nor
`const` applies to a type former — so the spine inversion leaves only the boxed prefix, and
both sides box. -/
theorem indVal_arm {env : VEnv} (henv : env.WF) {Us : List Name} {bo : Name → Option Expr}
    {fl : SEvalFlags} {Γspec Γ : GlobalDeclarations}
    (A : UpstreamAsks env) {cn : Name} {us : List Level} {iid : InductiveId} {np : Nat}
    {nfs : List Nat} {args argsv : List Expr}
    (hi : IndInfo env cn iid np nfs) (hlen : argsv.length = args.length)
    (hargs : ∀ i, i < args.length → SEval env bo Us fl [] args[i]! argsv[i]!)
    (ihargs : ∀ i, i < args.length → Simulates env bo Us Γspec Γ args[i]! argsv[i]!)
    {ve : VExpr} {t₀ t : LBTerm}
    (hwt : TrExprS env Us [] (mkApps (.const cn us) args) ve)
    (her : Erases env Us [] (mkApps (.const cn us) args) t₀)
    (hlow : Lower Γspec t₀ t) (hspec : ErasesEnv env bo Γspec t₀) :
    ∃ w₀ w', Erases env Us [] (mkApps (.const cn us) argsv) w₀ ∧ Lower Γspec w₀ w' ∧
      WcbvEval Γ eraseFlags t w' ∧ ErasesEnv env bo Γspec w₀ := by
  have hargEv : ∀ (a : Expr), a ∈ args → ∀ (s u : LBTerm), Erases env Us [] a s →
      ErasesEnv env bo Γspec s → Lower Γspec s u → ∃ x, WcbvEval Γ eraseFlags u x := by
    intro a ha s u hes hss hsu
    obtain ⟨w, htrw⟩ := trExprS_spine_mem args hwt a ha
    obtain ⟨i, hi', hia⟩ := Lower.mem_getElem! ha
    rw [← hia] at htrw hes
    obtain ⟨x, y, -, -, hx, -⟩ := ihargs i hi' htrw hes hsu hss
    exact ⟨y, hx⟩
  rcases erases_mkApps_inv args her with
    ⟨th, ts, hth, hts, rfl⟩ | ⟨pre, suf, ts, rfl, hbw, hts, rfl⟩
  · rcases Erases.const_inv hth with ⟨hb, rfl⟩ | ⟨I', iid', k', np', nfs', hc', hi', rfl⟩ |
      ⟨-, ho, rfl⟩
    · refine erases_correct_boxSpineLow (pre := []) (suf := args) henv hwt hb hlow
        hspec (fun s hs u hsu => ?_) (.indVal hi hlen hargs)
      obtain ⟨a, ha, hea⟩ := forall₂_mem_right hts s hs
      exact hargEv a ha s u hea (hspec.subterm (subTerm_mkApps_arg ts .box s hs)) hsu
    · exact absurd hi hc'.not_indInfo
    · exact absurd hi (constOrigin_not_indInfo A ho _ _ _)
  · refine erases_correct_boxSpineLow henv hwt hbw hlow hspec
      (fun s hs u hsu => ?_) (.indVal hi hlen hargs)
    obtain ⟨a, ha, hea⟩ := forall₂_mem_right hts s hs
    exact hargEv a (List.mem_append_right _ ha) s u hea
      (hspec.subterm (subTerm_mkApps_arg ts .box s hs)) hsu

/-- **`zeta`.** The `let` congruence: the bound value's image evaluates, and the body's
image is the substitution instance `Lower.subst_comm` and `erases_subst_let` produce. -/
theorem zeta_arm {env : VEnv} (henv : env.WF) {Us : List Name} {bo : Name → Option Expr}
    {fl : SEvalFlags} {Γspec Γ : GlobalDeclarations}
    (hΓcl : ClosedBodies Γspec) {n : Name} {ty val bd : Expr} {nd : Bool} {vv r : Expr}
    (hfl : fl.zeta) (hvalEv : SEval env bo Us fl [] val vv)
    (hbodyEv : SEval env bo Us fl [] (bd.instantiate1' vv 0) r)
    (ihval : Simulates env bo Us Γspec Γ val vv)
    (ihbody : Simulates env bo Us Γspec Γ (bd.instantiate1' vv 0) r)
    {ve : VExpr} {t₀ t : LBTerm}
    (hwt : TrExprS env Us [] (.letE n ty val bd nd) ve)
    (her : Erases env Us [] (.letE n ty val bd nd) t₀)
    (hlow : Lower Γspec t₀ t) (hspec : ErasesEnv env bo Γspec t₀) :
    ∃ w₀ w', Erases env Us [] r w₀ ∧ Lower Γspec w₀ w' ∧ WcbvEval Γ eraseFlags t w' ∧
      ErasesEnv env bo Γspec w₀ := by
  rcases Erases.letE_inv her with hbw |
    ⟨ty', val', v', b', htrtyE, htrvalE, herv, herb, rfl⟩
  · exact erases_correct_boxLow henv hwt hbw hlow hspec (.zeta hfl hvalEv hbodyEv)
  · obtain ⟨n₂, tv, tb, rfl, hlv, hlb⟩ := Lower.source_letIn hlow rfl
    cases hwt with
    | letE hValT htrty htrval htrb =>
      have hΔ : VLCtx.WF env Us.length ([] : VLCtx) := trivial
      have hΓv := hΔ.toCtx
      obtain ⟨u, h0⟩ := hValT.isType henv hΓv
      have hdty := VEnv.IsDefEqU.of_l henv hΓv
        (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrty htrtyE) h0
      have hdval := VEnv.IsDefEqU.of_l henv hΓv
        (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrval htrvalE) hValT
      have hvalT' := (hdval.hasType.2).defeqU_r henv hΓv ⟨_, hdty⟩
      have hWFlet : VLCtx.WF env Us.length ((none, .vlet _ _) :: ([] : VLCtx)) :=
        ⟨hΔ, nofun, hvalT'⟩
      obtain ⟨bv, htrbE⟩ := htrb.defeqDFC henv
        (VLCtx.IsDefEq.cons (.refl henv.ordered hΔ) (ofv := none) nofun (.vlet hdval hdty))
      obtain ⟨vv₀, vv', hervv, hlvv, hEv, hspecv⟩ :=
        ihval htrvalE herv hlv (hspec.subterm (.letInVal .refl))
      obtain ⟨vvv, htrvv, hdefv⟩ := SEval.defeq henv hΔ htrvalE hvalEv
      have hswap : VLCtx.IsDefEq env Us.length ((none, .vlet _ val') :: ([] : VLCtx))
          ((none, .vlet _ vvv) :: ([] : VLCtx)) :=
        VLCtx.IsDefEq.cons (.refl henv.ordered hΔ) (ofv := none) nofun
          (.vlet (VEnv.IsDefEqU.of_l henv hΓv hdefv hvalT') hdty.hasType.2)
      obtain ⟨bv₂, htrb₂⟩ := htrbE.defeqDFC henv hswap
      obtain ⟨rv₀, rv', herr, hlr, hEr, hspecr⟩ :=
        ihbody (TrExprS.inst_let henv.ordered htrb₂ htrvv)
          (erases_subst_let henv.ordered htrvv hervv .zero
            (Erases.defeqDFC_wt henv herb hswap hWFlet htrbE))
          (Lower.subst_comm hΓcl hlvv hlb 0)
          (hspecv.substPair (hspec.subterm (.letInBody .refl)))
      exact ⟨rv₀, rv', herr, hlr, .zeta hEv hEr, hspecr⟩


/-- **`beta`.** The `.app` node has two `Lower` readings (`ErasesCorrect/Steps.lean`): the
congruence, where the function's image is β-ready by `Lower.appReady`; and a saturated
eliminator spine, where the β rule's own function premise is refuted because an eliminator
spine one minor short heads no value. -/
theorem beta_arm {env : VEnv} (henv : env.WF) {Us : List Name} {bo : Name → Option Expr}
    {fl : SEvalFlags} {Γspec Γ : GlobalDeclarations} (A : UpstreamAsks env)
    (hΓcl : ClosedBodies Γspec)
    {f a : Expr} {n : Name} {ty bd : Expr} {bi : BinderInfo} {av r : Expr}
    (hfl : fl.beta) (hf : SEval env bo Us fl [] f (.lam n ty bd bi))
    (ha : SEval env bo Us fl [] a av)
    (hbody : SEval env bo Us fl [] (bd.instantiate1' av 0) r)
    (ihf : Simulates env bo Us Γspec Γ f (.lam n ty bd bi))
    (iha : Simulates env bo Us Γspec Γ a av)
    (ihbody : Simulates env bo Us Γspec Γ (bd.instantiate1' av 0) r)
    {ve : VExpr} {t₀ t : LBTerm}
    (hwt : TrExprS env Us [] (.app f a) ve) (her : Erases env Us [] (.app f a) t₀)
    (hlow : Lower Γspec t₀ t) (hspec : ErasesEnv env bo Γspec t₀) :
    ∃ w₀ w', Erases env Us [] r w₀ ∧ Lower Γspec w₀ w' ∧ WcbvEval Γ eraseFlags t w' ∧
      ErasesEnv env bo Γspec w₀ := by
  have hΔ : VLCtx.WF env Us.length ([] : VLCtx) := trivial
  have hΓv := hΔ.toCtx
  rcases Erases.app_inv her with hbw | ⟨f', a', hf', ha', rfl⟩
  · exact erases_correct_boxLow henv hwt hbw hlow hspec (.beta hfl hf ha hbody)
  · rcases Lower.source_app hlow rfl with ⟨tf, ta, rfl, hlf, hla⟩ |
      ⟨kn, iid, np, dp, nfs, pre, disc, minors, helim, hpl, hml, heq⟩
    · cases hwt with
      | @app fve A B ave _ _ _ hTf hTa htrf htra =>
        obtain ⟨fv₀, fv', herfv, hlfv, hEf, hspecf⟩ :=
          ihf htrf hf' hlf (hspec.subterm (.appFn .refl))
        obtain ⟨av₀, av', herav, hlav, hEa, hspeca⟩ :=
          iha htra ha' hla (hspec.subterm (.appArg .refl))
        obtain ⟨fvv, htrfvv, hfdef⟩ := SEval.defeq henv hΔ htrf hf
        rcases Erases.lam_inv herfv with ⟨⟨we, htrw, herw⟩, rfl⟩ |
          ⟨ty₂, b'', hty₂, hb'', rfl⟩
        · obtain rfl : fv' = .box := Lower.source_box hlfv rfl
          obtain ⟨rv, htrr, hrdef⟩ :=
            SEval.defeq henv hΔ (.app hTf hTa htrf htra) (.beta hfl hf ha hbody)
          have hferase : Erasable env Us.length (VLCtx.toCtx []) fve :=
            (herw.defeq henv hΓv
                (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrw htrfvv)).defeq
              henv hΓv (VEnv.IsDefEqU.symm hfdef)
          exact ⟨.box, .box,
            .box htrr ((hferase.app henv hΓv hTf hTa).defeq henv hΓv hrdef), .box,
            .app_box hEf hEa, hspec.box⟩
        · obtain ⟨c, hbc, hready⟩ := Lower.appReady (Γ := Γ) (fl := eraseFlags) hΓcl rfl hlfv rfl
          cases htrfvv with
          | @lam ty' _ _ _ body' _ _ hty' htrty htrb =>
            obtain ⟨avv, htravv, hadef⟩ := SEval.defeq henv hΔ htra ha
            have hΔ' : VLCtx.WF env Us.length ((none, .vlam ty') :: ([] : VLCtx)) :=
              ⟨hΔ, nofun, hty'⟩
            obtain ⟨B'', hbodyT⟩ := htrb.wf henv.ordered hΔ'
            have hAty' : env.IsDefEqU Us.length (VLCtx.toCtx []) A ty' := by
              obtain ⟨u, hty'sort⟩ := hty'
              have lamT1 : env.HasType Us.length (VLCtx.toCtx []) (.lam ty' body')
                  (.forallE ty' B'') := VEnv.HasType.lam hty'sort hbodyT
              have lamT2 : env.HasType Us.length (VLCtx.toCtx []) (.lam ty' body')
                  (.forallE A B) := hTf.defeqU_l henv hΓv hfdef
              obtain ⟨⟨_, h⟩, _⟩ := VEnv.IsDefEqU.forallE_inv henv hΓv
                (VEnv.IsDefEq.uniqU henv hΓv lamT2 lamT1)
              exact ⟨_, h⟩
            have havT : env.HasType Us.length (VLCtx.toCtx []) avv ty' :=
              (hTa.defeqU_l henv hΓv hadef).defeqU_r henv hΓv hAty'
            have havTE : env.HasType Us.length (VLCtx.toCtx []) avv ty₂ :=
              havT.defeqU_r henv hΓv (VEnv.IsDefEqU.symm
                (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) hty₂ htrty))
            obtain ⟨rv₀, rv', herr, hlr, hEr, hspecr⟩ :=
              ihbody (TrExprS.inst henv.ordered havT htrb htravv)
                (erases_subst henv.ordered htravv havTE herav .zero hb'')
                (Lower.subst_comm hΓcl hlav hbc 0)
                (hspeca.substPair (hspecf.subterm (.lambda .refl)))
            exact ⟨rv₀, rv', herr, hlr, hready hEf hEa hEr, hspecr⟩
    · exfalso
      have hL : pre ++ disc :: minors ≠ [] := by cases pre <;> simp
      have hsplit : pre ++ disc :: minors
          = (pre ++ disc :: minors).dropLast ++ [(pre ++ disc :: minors).getLast hL] :=
        (List.dropLast_concat_getLast hL).symm
      rw [hsplit] at heq
      obtain ⟨hfe, -⟩ := mkApps_eq_app heq.symm
      have hlenL : (pre ++ disc :: minors).length = dp + 1 + nfs.length := by
        simp only [List.length_append, List.length_cons]
        omega
      have hlt : (pre ++ disc :: minors).dropLast.length < dp + 1 + nfs.length := by
        rw [List.length_dropLast, hlenL]; omega
      exact erases_elimSpine_no_value A (hfe ▸ (hspec.subterm (.appFn .refl))) helim hlt
        (hfe ▸ hf') hf

/-- **`ctorVal`.** A constructor spine within its arity: the head erases to the
`.construct` node (`Erases.const`'s reading is refuted by the rule's own `CtorOf`), the
node's emitted arity comes from the block the program reaches, and the target value is
built by `construct_atom` and `construct_app`. -/
theorem ctorVal_arm {env : VEnv} (henv : env.WF) {Us : List Name} {bo : Name → Option Expr}
    {fl : SEvalFlags} {Γspec Γ : GlobalDeclarations}
    (A : UpstreamAsks env)
    (henvL : LowerEnv Γspec Γ) {cn I : Name} {us : List Level} {iid : InductiveId}
    {k np : Nat} {nfs : List Nat} {args argsv : List Expr}
    (hc : CtorOf env cn I k) (hi : IndInfo env I iid np nfs)
    (harity : args.length ≤ np + nfs[k]!) (hlen : argsv.length = args.length)
    (hargs : ∀ i, i < args.length → SEval env bo Us fl [] args[i]! argsv[i]!)
    (ihargs : ∀ i, i < args.length → Simulates env bo Us Γspec Γ args[i]! argsv[i]!)
    {ve : VExpr} {t₀ t : LBTerm}
    (hwt : TrExprS env Us [] (mkApps (.const cn us) args) ve)
    (her : Erases env Us [] (mkApps (.const cn us) args) t₀)
    (hlow : Lower Γspec t₀ t) (hspec : ErasesEnv env bo Γspec t₀) :
    ∃ w₀ w', Erases env Us [] (mkApps (.const cn us) argsv) w₀ ∧ Lower Γspec w₀ w' ∧
      WcbvEval Γ eraseFlags t w' ∧ ErasesEnv env bo Γspec w₀ := by
  have hargEv : ∀ (a : Expr), a ∈ args → ∀ (s u : LBTerm), Erases env Us [] a s →
      ErasesEnv env bo Γspec s → Lower Γspec s u → ∃ x, WcbvEval Γ eraseFlags u x := by
    intro a ha s u hes hss hsu
    obtain ⟨w, htrw⟩ := trExprS_spine_mem args hwt a ha
    obtain ⟨i, hi', hia⟩ := Lower.mem_getElem! ha
    rw [← hia] at htrw hes
    obtain ⟨x, y, -, -, hx, -⟩ := ihargs i hi' htrw hes hsu hss
    exact ⟨y, hx⟩
  rcases erases_mkApps_inv args her with
    ⟨th, ts, hth, hts, rfl⟩ | ⟨pre, suf, ts, rfl, hbw, hts, rfl⟩
  · rcases Erases.const_inv hth with ⟨hb, rfl⟩ | ⟨I', iid', k', np', nfs', hc', hi', rfl⟩ |
      ⟨-, ho, rfl⟩
    · refine erases_correct_boxSpineLow (pre := []) (suf := args) henv hwt hb hlow
        hspec (fun s hs u hsu => ?_) (.ctorVal hc hi harity hlen hargs)
      obtain ⟨a, ha, hea⟩ := forall₂_mem_right hts s hs
      exact hargEv a ha s u hea (hspec.subterm (subTerm_mkApps_arg ts .box s hs)) hsu
    · obtain ⟨rfl, rfl⟩ := CtorOf.inj A hc hc'
      obtain ⟨rfl, rfl, rfl⟩ := IndInfo.inj A hi hi'
      have hlents : args.length = ts.length := hts.length_eq
      obtain ⟨hd', ts', rfl, hhd, hlen', hpt⟩ :=
        Lower.source_mkApps (fun _ _ => LBTerm.noConfusion)
          (fun _ => LBTerm.noConfusion) ts hlow
      obtain rfl : hd' = .construct iid k [] := by
        rcases Lower.source_construct_nil hhd rfl with h | ⟨defs, j, h⟩
        · exact h
        · exact absurd h
            (Lower.ne_fix_of_block hhd (fun _ => LBTerm.noConfusion) rfl defs j)
      have har := hspec.ctorArity henvL hi
        (ReachableFrom.subterm (subTerm_mkApps_head ts .refl)
          (reachableFrom_of_mem_constRefs (by simp [constRefs, constRefsArgs])))
        (CtorOf.lt_nfs A hc hi)
      have hchoice : ∀ i, i < args.length → ∃ p : LBTerm × LBTerm,
          Erases env Us [] argsv[i]! p.1 ∧ Lower Γspec p.1 p.2 ∧
            WcbvEval Γ eraseFlags ts'[i]! p.2 ∧ ErasesEnv env bo Γspec p.1 := by
        intro i hi'
        obtain ⟨w, htrw⟩ := trExprS_spine_mem args hwt args[i]! (Lower.getElem!_mem hi')
        obtain ⟨x, y, h1, h2, h3, h4⟩ :=
          ihargs i hi' htrw (forall₂_getElem! hts i hi') (hpt i (by omega))
            (hspec.subterm (subTerm_mkApps_arg ts _ _
              (Lower.getElem!_mem (l := ts) (by omega))))
        exact ⟨(x, y), h1, h2, h3, h4⟩
      obtain ⟨ps, hpslen, hps⟩ := exists_list_of_index args.length _ hchoice
      refine ⟨LBTerm.mkApps (.construct iid k []) (ps.map Prod.fst),
        LBTerm.mkApps (.construct iid k []) (ps.map Prod.snd), ?_, ?_, ?_, ?_⟩
      · refine Erases.mkApps_forall₂ (forall₂_of_getElem! (by simp [hpslen, hlen])
          (fun i hi' => ?_)) (.ctor hc hi)
        rw [Lower.getElem!_map _ ps i (by omega), hlen] at *
        exact (hps i (by omega)).1
      · refine Lower.mkApps (.construct rfl (fun i hi' => absurd hi' (by simp)))
          (by simp) (fun i hi' => ?_)
        have hip : i < ps.length := by simpa using hi'
        rw [Lower.getElem!_map _ ps i hip, Lower.getElem!_map _ ps i hip]
        exact (hps i (by omega)).2.1
      · refine wcbvEval_mkApps_construct har ts' (ps.map Prod.snd) (by omega)
          (by simp [hpslen, hlen', ← hlents]) (fun i hi' => ?_)
        rw [Lower.getElem!_map _ ps i (by omega)]
        exact (hps i (by omega)).2.2.1
      · refine ErasesEnv.mkApps (hspec.subterm (subTerm_mkApps_head ts .refl))
          (fun x hx => ?_)
        obtain ⟨i, hi', rfl⟩ := Lower.mem_getElem! hx
        have hip : i < ps.length := by simpa using hi'
        rw [Lower.getElem!_map _ ps i hip]
        exact (hps i (by omega)).2.2.2
    · exact absurd hc (constOrigin_not_ctorOf A ho I k)
  · refine erases_correct_boxSpineLow henv hwt hbw hlow hspec (fun s hs u hsu => ?_)
      (.ctorVal hc hi harity hlen hargs)
    obtain ⟨a, ha, hea⟩ := forall₂_mem_right hts s hs
    exact hargEv a (List.mem_append_right _ ha) s u hea
      (hspec.subterm (subTerm_mkApps_arg ts .box s hs)) hsu

/--
**T5, with the three hard arms as hypotheses.** One induction on `hev`; every other arm is
discharged here, off the eight binders `erases_correct` itself has and nothing more.
-/
theorem erases_correct_of_steps {env : VEnv} {bo : Name → Option Expr} {Us : List Name}
    {fl : SEvalFlags} {Γspec Γ : GlobalDeclarations}
    (step_iota : StepIota env bo Us fl Γspec Γ)
    (step_proj : StepProj env bo Us fl Γspec Γ)
    (step_delta : StepDelta env bo Us fl Γspec Γ) :
    ErasesCorrectStmt env bo Us fl Γspec Γ := by
  intro e₀ v₀ ve₀ t₀₀ t₀ henv hwt₀ hev₀ her₀ hlow₀ hspec₀ henvL A
  have hΓcl : ClosedBodies Γspec := henvL.specClosed
  have key : ∀ {Δ : VLCtx} {e v : Expr}, SEval env bo Us fl Δ e v → Δ = [] →
      Simulates env bo Us Γspec Γ e v := by
    clear hwt₀ her₀ hlow₀ hspec₀ hev₀
    intro Δ e v hev
    induction hev with
    | @lam n ty bd bi =>
        intro rfl ve t₀ t hwt her hlow hspec
        rcases Erases.lam_inv her with hbw | ⟨ty₂, b', hty₂, hb', rfl⟩
        · exact erases_correct_boxLow (fl := fl) henv hwt hbw hlow hspec (.lam n ty bd bi)
        · refine ⟨_, t, her, hlow, ?_, hspec⟩
          rcases Lower.source_lambda hlow rfl with ⟨n', b'', rfl⟩ | ⟨defs, j, rfl⟩
          · exact .lam _ _
          · exact .fix_atom _ _
    | @sort u =>
        intro rfl ve t₀ t hwt her hlow hspec
        exact erases_correct_boxLow (fl := fl) henv hwt (Erases.sort_inv her) hlow hspec
          .sort
    | @forallE n ty bd bi =>
        intro rfl ve t₀ t hwt her hlow hspec
        exact erases_correct_boxLow (fl := fl) henv hwt (Erases.forallE_inv her) hlow hspec
          .forallE
    | @lit l r hfl hlit ih =>
        intro rfl ve t₀ t hwt her hlow hspec
        rcases Erases.lit_inv her with hbw | ⟨hcl, her'⟩
        · exact erases_correct_boxLow henv hwt hbw hlow hspec (.lit hfl hlit)
        · cases hwt with
          | lit _ htrC => exact ih rfl htrC her' hlow hspec
    | @zeta n ty val bd nd vv r hfl hvalEv hbodyEv ihval ihbody =>
        intro rfl ve t₀ t hwt her hlow hspec
        exact zeta_arm henv hΓcl hfl hvalEv hbodyEv (ihval rfl) (ihbody rfl) hwt her
          hlow hspec
    | @beta f a n ty bd bi av r hfl hf ha hbody ihf iha ihbody =>
        intro rfl ve t₀ t hwt her hlow hspec
        exact beta_arm henv A hΓcl hfl hf ha hbody (ihf rfl) (iha rfl) (ihbody rfl)
          hwt her hlow hspec
    | @ctorVal cn I us iid k np nfs args argsv hc hi harity hlen hargs ihargs =>
        intro rfl ve t₀ t hwt her hlow hspec
        exact ctorVal_arm henv A henvL hc hi harity hlen hargs
          (fun i hi' => ihargs i hi' rfl) hwt her hlow hspec
    | @indVal cn us iid np nfs args argsv hi hlen hargs ihargs =>
        intro rfl ve t₀ t hwt her hlow hspec
        exact indVal_arm henv A hi hlen hargs (fun i hi' => ihargs i hi' rfl) hwt her
          hlow hspec
    | @deltaC c us ups args argsv b b' vres hfl hbd hnd hinst hlen hargs hdef hcont
        ihargs ihcont =>
        intro rfl
        exact step_delta A henv henvL hfl hbd hnd hinst hlen
          (fun i hi => ⟨hargs i hi, ihargs i hi rfl⟩) hdef hcont (ihcont rfl)
    | @iota con I ctor us cus pre prev minors minorsv extra extrav cargs disc r np cidx
        nfs hfl hsh ho hct hnp hinf hpre hpres hdiscr hmin hmins hxlen hxs hidx hdef hcont
        ihpres ihdiscr ihmins ihxs ihcont =>
        intro rfl
        exact step_iota A henv henvL hfl hsh ho hct hnp hinf hpre
          (fun i hi => ⟨hpres i hi, ihpres i hi rfl⟩) hdiscr (ihdiscr rfl) hmin
          (fun i hi => ⟨hmins i hi, ihmins i hi rfl⟩) hxlen
          (fun i hi => ⟨hxs i hi, ihxs i hi rfl⟩) hidx hdef hcont (ihcont rfl)
    | @proj S ctor i discr cus cargs np nf cidx r hfl hct hnp hdiscr hlt hdef hcont
        ihdiscr ihcont =>
        intro rfl
        exact step_proj A henv henvL hfl hct hnp hdiscr (ihdiscr rfl) hlt hdef hcont
          (ihcont rfl)
  obtain ⟨w₀, w', her, hlw, hEw, -⟩ := key hev₀ rfl hwt₀ her₀ hlow₀ hspec₀
  exact ⟨w₀, w', her, hlw, hEw⟩

/-! ## Non-vacuity

One witness per arm whose content is more than an inversion: the constructor spine the
`ctorVal` arm builds, the head exclusion the `indVal` arm runs on, and the re-associated
pair the `beta` arm proceeds with at an over-applied eliminator spine.
-/

/-- **`ctorVal`'s target side fires.** A saturated two-argument constructor spine — one
parameter, one field — evaluates to itself by `construct_atom` and `construct_app`. -/
theorem ctorVal_target_fires :
    WcbvEval acΓ eraseFlags (LBTerm.mkApps (.construct acIid 0 []) [.box, .box])
      (LBTerm.mkApps (.construct acIid 0 []) [.box, .box]) := by
  refine wcbvEval_mkApps_construct ac_arity [.box, .box] [.box, .box] (by decide) rfl ?_
  intro i hi
  match i, hi with
  | 0, _ => exact .box
  | 1, _ => exact .box

/-- **`indVal`'s head exclusion fires.** At an inductive type name the constructor reading
is refuted by `CtorOf.not_indInfo` and the constant reading by `constOrigin_not_indInfo`,
so `□` is the only image and the arm's boxed-prefix case is the only one. -/
theorem indVal_head_boxes_fires (A : UpstreamAsks blkEnv) (Us : List Name) (Δ : VLCtx)
    (us : List Level) {t : LBTerm} (h : Erases blkEnv Us Δ (.const blkT us) t) : t = .box := by
  rcases Erases.const_inv h with ⟨-, rfl⟩ | ⟨I', iid', k', np', nfs', hc', -, -⟩ | ⟨-, ho, -⟩
  · rfl
  · exact absurd blk_indInfo hc'.not_indInfo
  · exact absurd blk_indInfo (constOrigin_not_indInfo A ho _ _ _)

/-- **The `beta` arm's re-association fires.** `Lower.source_app` reads
`LowerElimFixture`'s over-applied eliminator spine as the `app` congruence — the `.case`
node at the initial segment against the spine one argument shorter, and the last argument
on its own — which is the reading the arm proceeds on. The saturated reading is refuted
here by the fixture's own numbers. -/
theorem beta_reassociation_fires :
    ∃ f' a', LBTerm.mkApps (.case (LowerElimFixture.iid, 0) (.bvar 0)
          [([], .box), ([.anon], .bvar 0)]) [.bvar 1] = .app f' a' ∧
      Lower LowerElimFixture.env
        (LBTerm.mkApps (.const LowerElimFixture.elimKn)
          [.box, .bvar 0, .box, .lambda .anon (.bvar 0)]) f' ∧
      Lower LowerElimFixture.env (.bvar 1) a' := by
  rcases Lower.source_app LowerElimFixture.elimApp_fires rfl
    with ⟨f', a', heq, hf, ha⟩ |
      ⟨kn, iid', np', dp', nfs', pre, disc, minors, helim, hpl, hml, heq⟩
  · exact ⟨f', a', heq, hf, ha⟩
  · exfalso
    obtain ⟨⟨body, hbody, hEB⟩, ⟨mib', hmib, hnp, oib, hoib, -, hctors⟩⟩ := helim
    rw [LowerElimFixture.env] at hmib hbody
    have hargs := congrArg LBTerm.spineArgs heq
    rw [LBTerm.spineArgs_mkApps] at hargs
    have hlen5 : pre.length + 1 + minors.length = 5 := by
      have := congrArg List.length hargs
      simp [LBTerm.spineArgs] at this
      omega
    have hnfs : nfs' = [0, 1] := by
      rw [LBTerm.envLookup] at hmib
      split at hmib
      · injection hmib with hm
        injection hm with hm
        subst hm
        have hlt : iid'.idx < 1 := by
          by_contra hno
          rw [List.getElem?_eq_none (by simp [LowerElimFixture.mib]; omega)] at hoib
          simp at hoib
        have hidx : iid'.idx = 0 := by omega
        rw [hidx] at hoib
        simp [LowerElimFixture.mib] at hoib
        subst hoib
        simpa using hctors.symm
      · rw [LBTerm.envLookup] at hmib
        split at hmib
        · exact absurd hmib (by simp)
        · simp [LBTerm.envLookup] at hmib
    subst hnfs
    have hdp : dp' = 2 := by simp at hml; omega
    subst hdp
    have hbd : body = mkElimBody LowerElimFixture.iid 0 1 [0, 1] := by
      have hkn : kn = LowerElimFixture.elimKn := by
        have := congrArg LBTerm.spineHead heq
        rw [LBTerm.spineHead_mkApps] at this
        simp [LBTerm.spineHead] at this
        exact this.symm
      subst hkn
      rw [LBTerm.envLookup] at hbody
      split at hbody
      · exact absurd hbody (by simp)
      · rw [LBTerm.envLookup] at hbody
        split at hbody
        · injection hbody with hb; injection hb with hb; injection hb with hb
          exact (Option.some.inj hb).symm
        · simp [LBTerm.envLookup] at hbody
    subst hbd
    cases hEB

end LeanToLambdaBox
