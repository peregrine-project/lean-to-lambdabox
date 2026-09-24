import LeanToLambdaBox.ErasesCorrect.Steps

/-!
# The δ arm: a tabled constant, plain or recursive

`step_delta` proves `StepDelta` (`ErasesCorrect/Steps.lean`), the arm `SEval.deltaC` leaves
to a step lemma. The source unfolds the compiler body `bo c` at the call site's levels and
evaluates the unfolded application; the target does whatever its own environment holds for
the constant's kername — the emitted body, or the block's `.fix` node.

Both shapes are discharged by one move. The induction hypothesis at the unfolded
application is available *at every composite image* of that application, so the arm chooses
the image whose head is the term the target head evaluates to: the emitted body when
`Lower.const` relates the constant to itself, and the block's node — `Lower.fixBody` at the
member's own specification body — when `Lower.fixConst` does. `WcbvEval.mkApps_congr` then
moves the run the hypothesis produced onto the actual spine, replacing the head by one δ
step (`WcbvEval.delta`) or by nothing, and the argument values by the arguments. No fix
unfolding is performed here: the recursive constant's own run is the hypothesis's.

The two sides read the body at different level scopes: `ErasesEnv.defns` holds an erasure at
the declaration's own, `SEval.deltaC` unfolds an instantiation of it at the call site's.
`Erases.instantiateLevelParams_of_stepDefeq` moves the one to the other on the rule's own
`hdef`, which is where MetaRocq spends `erases_subst_instance_decl`
(`../metarocq/erasure/theories/ErasureCorrectness.v:176`).

What the arm must first exclude is the *eliminator* reading of the spine, `Lower.elimApp`.
It is excluded outright: `ErasesEnv.defns` exhibits the tabled constant's entry as an
erasure image, and `erases_ne_elimBody` (`ErasesCorrect/Steps.lean`) says no erasure image
is an eliminator body. The *constructor* reading of the head — at which the key is not
reached at all — is excluded by `ErasesEnv.tabled` through `constOrigin_not_ctorOf`, which
is why `StepDelta` binds `UpstreamAsks env`.

`SEval.deltaC`'s `hnd` is spent only in rebuilding the source derivation for the boxed
readings: the eliminator configuration it rules out is already gone here.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-! ## The `Lower` readings of a tabled constant's spine -/

/-- **A lowered spine at a constant head that is not a runtime key.** The `elimApp`
reading is excluded by the guard, so the whole spine is the congruence reading: head to
head, argument to argument. -/
theorem Lower.source_constSpine {Γ : GlobalDeclarations}
    {kn : Kername} (hnk : ¬ RuntimeKey Γ kn) :
    ∀ (ts : List LBTerm) {t : LBTerm}, Lower Γ (LBTerm.mkApps (.const kn) ts) t →
      ∃ (hd' : LBTerm) (ts' : List LBTerm), t = LBTerm.mkApps hd' ts' ∧
        Lower Γ (.const kn) hd' ∧ ts'.length = ts.length ∧
        ∀ i, i < ts.length → Lower Γ ts[i]! ts'[i]! := by
  suffices h : ∀ (n : Nat) (ts : List LBTerm), ts.length = n → ∀ {t : LBTerm},
      Lower Γ (LBTerm.mkApps (.const kn) ts) t →
      ∃ (hd' : LBTerm) (ts' : List LBTerm), t = LBTerm.mkApps hd' ts' ∧
        Lower Γ (.const kn) hd' ∧ ts'.length = ts.length ∧
        ∀ i, i < ts.length → Lower Γ ts[i]! ts'[i]! from
    fun ts t hlow => h ts.length ts rfl hlow
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro ts hn t hlow
    rcases List.eq_nil_or_concat ts with rfl | ⟨init, last, rfl⟩
    · exact ⟨t, [], rfl, hlow, rfl, by simp⟩
    · rw [List.concat_eq_append, LBTerm.mkApps_concat] at hlow
      rcases Lower.source_app hlow rfl with
        ⟨f', a', rfl, hf, ha⟩ | ⟨kn', iid, np, dp, nfs, pre, disc, minors, helim, -, -, heq⟩
      · obtain ⟨hd', is', rfl, hhd, hilen, hi⟩ :=
          ih init.length (by simp [List.concat_eq_append] at hn; omega) init rfl hf
        refine ⟨hd', is' ++ [a'], (LBTerm.mkApps_concat _ _ _).symm, hhd, ?_, ?_⟩
        · rw [List.concat_eq_append]; exact (Lower.concat hilen hi ha).1
        · rw [List.concat_eq_append]; exact (Lower.concat hilen hi ha).2
      · exfalso
        have heq' : LBTerm.mkApps (.const kn) (init ++ [last])
            = LBTerm.mkApps (.const kn') (pre ++ disc :: minors) := by
          rw [LBTerm.mkApps_concat]; exact heq
        obtain ⟨hhd, -⟩ := mkApps_head_inj (fun _ _ => LBTerm.noConfusion)
          (fun _ _ => LBTerm.noConfusion) heq'
        injection hhd with hkk
        exact hnk ⟨iid, np, dp, nfs, hkk ▸ helim⟩

/-- **What a tabled constant's image evaluates like.** Either it is the constant itself,
or — at a block member — it is an image of the constant's own body, the block's `.fix`
node. Neither reading is available at a runtime key. -/
theorem Lower.const_body {Γ : GlobalDeclarations}
    {kn : Kername} {b s t : LBTerm} (h : Lower Γ s t) (hs : s = .const kn)
    (hd : DefnDecl Γ kn b) : ¬ RuntimeKey Γ kn ∧ (t = .const kn ∨ Lower Γ b t) := by
  cases h with
  | @const kn' hk =>
      have he : kn' = kn := by injection hs
      subst he
      exact ⟨hk, .inl rfl⟩
  | box | bvar | fvar | prim | lambda | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion hs
  | @elimApp kn' iid np dp nfs pre disc disc' minors alts extra extra' =>
      obtain ⟨g, a, he⟩ := mkApps_ne_nil_is_app (f := LBTerm.const kn')
        (args := pre ++ disc :: minors ++ extra) (by cases pre <;> simp)
      rw [he] at hs; exact LBTerm.noConfusion hs
  | @fixConst kn' kns bs bs' ids defs j hb hb' hdf hnd hids hilen hfresh hrarg hdecl hfl
      hlow hcl hnk hj =>
      have he : kn' = kn := by injection hs
      subst he
      exact ⟨hnk, .inr (Lower.fixBody_of_block
        ⟨hb, hb', hdf, hnd, hids, hilen, hfresh, hrarg, hdecl, hfl, hlow, hcl⟩ hj hd)⟩
  | @fixBody b₀ kns bs bs' ids defs j hb hb' hdf hnd hids hilen hfresh hrarg hdecl hfl hlow
      hcl hj hjl =>
      exfalso
      obtain ⟨hjb, hjeq⟩ := Lower.getElem!_of_getElem? hj
      have hlam := (⟨hb, hb', hdf, hnd, hids, hilen, hfresh, hrarg, hdecl, hfl, hlow,
        hcl⟩ : LowerBlock Γ kns bs bs' ids defs).lambda_of_fixLambda j (by omega)
      rw [hjeq, hs] at hlam
      simp [isLambda] at hlam
  | @fixEta b₀ nm kns bs bs' ids defs j hb hb' hdf hnd hids hilen hfresh hrarg hdecl hfl hlow
      hcl hj hjl =>
      exfalso
      obtain ⟨hjb, hjeq⟩ := Lower.getElem!_of_getElem? hj
      have hlam := (⟨hb, hb', hdf, hnd, hids, hilen, hfresh, hrarg, hdecl, hfl, hlow,
        hcl⟩ : LowerBlock Γ kns bs bs' ids defs).lambda_of_fixLambda j (by omega)
      rw [hjeq, hs] at hlam
      simp [isLambda] at hlam

/-! ## The arm -/

/-- **The δ arm.** The head erases to the tabled constant's kername; the constructor
reading is refuted by `ErasesEnv.tabled` through `constOrigin_not_ctorOf`, and the boxed
readings fold. The entry's erasure is read at the call site's level scope by
`Erases.instantiateLevelParams_of_stepDefeq`, at the two further conjuncts of the same
`ErasesEnv.defns` reading. The spine lowers as a congruence, since a tabled constant is no runtime key
— its specification body is an erasure image, and no erasure image is an eliminator body.
The induction hypothesis is taken at the lowering whose head is what the target head
evaluates to: the emitted body, or the block's node at a member. `WcbvEval.mkApps_congr`
then moves the run it produced onto the spine, replacing the head by one `WcbvEval.delta`
step or by nothing. -/
theorem step_delta {env : VEnv} {bo : Name → Option Expr} {lp : Name → List Name}
    {Us : List Name}
    {fl : SEvalFlags} {Γspec Γ : GlobalDeclarations} :
    StepDelta env bo lp Us fl Γspec Γ := by
  intro A c us ups args argsv b b' v henv henvL hfl hbd hnd hinst hlen hargs hdef hcont
    ihcont ve t₀ t hwt her hlow hspec
  have hargEv : ∀ (a : Expr), a ∈ args → ∀ (s u : LBTerm), Erases env Us [] a s →
      ErasesEnv env bo lp Γspec s → Lower Γspec s u → ∃ x, WcbvEval Γ eraseFlags u x := by
    intro a ha s u hes hss hsu
    obtain ⟨w, htrw⟩ := trExprS_spine_mem args hwt a ha
    obtain ⟨i, hi, hia⟩ := Lower.mem_getElem! ha
    rw [← hia] at htrw hes
    obtain ⟨x, y, -, -, hx, -⟩ := (hargs i hi).2 htrw hes hsu hss
    exact ⟨y, hx⟩
  have hev : SEval env bo Us fl [] (mkApps (.const c us) args) v :=
    .deltaC hfl hbd hnd hinst hlen (fun i hi => (hargs i hi).1) hdef hcont
  rcases erases_mkApps_inv args her with ⟨th, ts, hth, hts, rfl⟩ |
    ⟨pre, suf, ts, rfl, hbw, hts, rfl⟩
  case inr =>
    refine erases_correct_boxSpineLow henv hwt hbw hlow hspec (fun s hs u hsu => ?_) hev
    obtain ⟨a, ha, hea⟩ := forall₂_mem_right hts s hs
    exact hargEv a (List.mem_append_right _ ha) s u hea
      (hspec.subterm (subTerm_mkApps_arg ts .box s hs)) hsu
  rcases Erases.const_inv hth with ⟨hb, rfl⟩ | ⟨I', iid', k', np', nfs', hc', hi', rfl⟩ |
    ⟨-, ho, rfl⟩
  · refine erases_correct_boxSpineLow (pre := []) (suf := args) henv hwt hb hlow
      hspec (fun s hs u hsu => ?_) hev
    obtain ⟨a, ha, hea⟩ := forall₂_mem_right hts s hs
    exact hargEv a ha s u hea (hspec.subterm (subTerm_mkApps_arg ts .box s hs)) hsu
  · exact absurd hc' (constOrigin_not_ctorOf A (hspec.tabled c b hbd) I' k')
  · have hlents : args.length = ts.length := hts.length_eq
    have hreach : ReachableFrom Γspec (LBTerm.mkApps (.const (toKername c)) ts) (toKername c) :=
      ReachableFrom.subterm (subTerm_mkApps_head ts .refl)
        (reachableFrom_of_mem_constRefs (by simp [constRefs]))
    obtain ⟨hnmb, b₀, vb, hlook, herb, htrb⟩ := hspec.defns c b hbd hreach
    have hdefn : DefnDecl Γspec (toKername c) b₀ := hlook
    have herb' : Erases env Us [] b' b₀ :=
      Erases.instantiateLevelParams_of_stepDefeq herb hnmb htrb hinst hdef
    have hnk : ¬ RuntimeKey Γspec (toKername c) := by
      rintro ⟨iid, np, dp, nfs, ⟨body, hbody, helim⟩, -⟩
      rw [hlook] at hbody
      obtain rfl : b₀ = body := by simpa using hbody
      exact erases_ne_elimBody herb' helim
    obtain ⟨hd', ts', rfl, hhd, hlen', hpt⟩ := Lower.source_constSpine hnk ts hlow
    obtain ⟨H, hlowH, hstep⟩ : ∃ H, Lower Γspec b₀ H ∧
        ∀ w, WcbvEval Γ eraseFlags H w → WcbvEval Γ eraseFlags hd' w := by
      rcases (Lower.const_body hhd rfl hdefn).2 with rfl | hbody
      · obtain ⟨bΓ, hbΓ⟩ := henvL.defsTotal _ b₀ hdefn hnk
        exact ⟨bΓ, henvL.defs _ b₀ bΓ hdefn hbΓ, fun w hw => .delta hbΓ hw⟩
      · exact ⟨hd', hbody, fun _ hw => hw⟩
    have hchoice : ∀ i, i < args.length → ∃ p : LBTerm × LBTerm,
        Erases env Us [] argsv[i]! p.1 ∧ Lower Γspec p.1 p.2 ∧
          WcbvEval Γ eraseFlags ts'[i]! p.2 ∧ ErasesEnv env bo lp Γspec p.1 := by
      intro i hi
      obtain ⟨w, htrw⟩ := trExprS_spine_mem args hwt args[i]! (Lower.getElem!_mem hi)
      obtain ⟨x, y, h1, h2, h3, h4⟩ :=
        (hargs i hi).2 htrw (forall₂_getElem! hts i hi) (hpt i (by omega))
          (hspec.subterm (subTerm_mkApps_arg ts _ _
            (Lower.getElem!_mem (l := ts) (by omega))))
      exact ⟨(x, y), h1, h2, h3, h4⟩
    obtain ⟨ps, hpslen, hps⟩ := exists_list_of_index args.length _ hchoice
    have hercon : Erases env Us [] (mkApps b' argsv) (LBTerm.mkApps b₀ (ps.map Prod.fst)) := by
      refine Erases.mkApps_forall₂ (forall₂_of_getElem! (by simp [hpslen, hlen])
        (fun i hi => ?_)) herb'
      rw [Lower.getElem!_map _ ps i (by omega)]
      exact (hps i (by omega)).1
    have hlowcon : Lower Γspec (LBTerm.mkApps b₀ (ps.map Prod.fst))
        (LBTerm.mkApps H (ps.map Prod.snd)) := by
      refine Lower.mkApps hlowH (by simp) (fun i hi => ?_)
      have hip : i < ps.length := by simpa using hi
      rw [Lower.getElem!_map _ ps i hip, Lower.getElem!_map _ ps i hip]
      exact (hps i (by omega)).2.1
    have hspeccon : ErasesEnv env bo lp Γspec (LBTerm.mkApps b₀ (ps.map Prod.fst)) := by
      refine ErasesEnv.mkApps
        (hspec.ofReach (fun kn hr => ReachableFrom.through_body hreach hlook hr))
        (fun x hx => ?_)
      obtain ⟨i, hi, rfl⟩ := Lower.mem_getElem! hx
      have hip : i < ps.length := by simpa using hi
      rw [Lower.getElem!_map _ ps i hip]
      exact (hps i (by omega)).2.2.2
    obtain ⟨-, v₂, -, htr₂, -⟩ := hdef
    obtain ⟨w₀, w', herw, hloww, hEw, hspecw⟩ := ihcont htr₂ hercon hlowcon hspeccon
    refine ⟨w₀, w', herw, hloww, ?_, hspecw⟩
    obtain ⟨fv, hfv⟩ := WcbvEval.head_value_of_mkApps (ps.map Prod.snd) hEw
    refine WcbvEval.mkApps_congr ?_ hfv (hstep fv hfv) hEw
    refine forall₂_of_getElem! (by simp [hpslen, hlen', ← hlents]) (fun i hi => ?_)
    have hip : i < ps.length := by simpa using hi
    rw [Lower.getElem!_map _ ps i hip]
    refine ⟨ps[i]!.2, value_final (eval_to_value ((hps i (by omega)).2.2.1)), ?_⟩
    exact (hps i (by omega)).2.2.1

/-! ## Non-vacuity

The arm's two head readings and the transport that carries them, at the tree's own
fixtures: the block member's constant, whose image is the block's node; and the emitted
δ step, at a plain λ body and at a body that is itself a block's node.
-/

/-- **The head reading fires at a block member.** `Lower.const_body` reads member 1's
`.fix` image as an image of the member's own body — the lowering the arm hands the
induction hypothesis. -/
theorem const_body_fires :
    Lower LowerFixFixture.specEnv LowerFixFixture.b₁ (.fix LowerFixFixture.defs 1) := by
  rcases (Lower.const_body
      (Lower.fixConst' (j := 1) LowerFixFixture.lowerfix_nv
        (LowerFixFixture.not_runtimeKey LowerFixFixture.decl₁) rfl)
      rfl LowerFixFixture.decl₁).2 with h | h
  · exact absurd h (by simp)
  · exact h

/-- **The spine inversion fires.** A one-argument spine at a member's constant, which is
no runtime key, reads as the congruence: head to head, argument to argument. -/
theorem source_constSpine_fires :
    ∃ hd' ts', LBTerm.mkApps (.const LowerFixFixture.kn₁) [.box] = LBTerm.mkApps hd' ts' ∧
      Lower LowerFixFixture.specEnv (.const LowerFixFixture.kn₁) hd' ∧ ts'.length = 1 := by
  obtain ⟨hd', ts', heq, hhd, hlen, -⟩ :=
    Lower.source_constSpine
      (LowerFixFixture.not_runtimeKey LowerFixFixture.decl₁) [.box]
      (Lower.mkApps (Γ := LowerFixFixture.specEnv)
        (.const (LowerFixFixture.not_runtimeKey LowerFixFixture.decl₁)) rfl
        (fun i hi => by match i, hi with | 0, _ => exact .box))
  exact ⟨hd', ts', heq, hhd, hlen⟩

/-- **The transport fires at a recursive constant.** The block member's spine evaluates
by unfolding the fix — twice, since member 1 calls member 0 — and `WcbvEval.mkApps_congr`
moves that run onto the constant, whose emitted body is the block's node: the arm's
`.const`-image reading at a recursive definition. -/
theorem delta_recursive_fires :
    WcbvEval LowerFixFixture.targetEnv eraseFlags
      (LBTerm.mkApps (.const LowerFixFixture.kn₁) [.box]) .box :=
  WcbvEval.mkApps_congr (.cons ⟨.box, .box, .box⟩ .nil) (.fix_atom _ _)
    LowerFixFixture.lowerfix_delta LowerFixFixture.lowerfix_target_step

/-- **The transport fires at a plain definition.** The emitted body's own run is moved
onto the constant by one `WcbvEval.delta` step. -/
theorem delta_nonrecursive_fires :
    WcbvEval idEnv eraseFlags (LBTerm.mkApps (.const (rootKername "id")) [.box]) .box :=
  WcbvEval.mkApps_congr (.cons ⟨.box, .box, .box⟩ .nil) (.lam _ _)
    (.delta rfl (.lam _ _)) (.beta (.lam _ _) .box .box)

/-- **The eliminator-body exclusion fires.** The fixture's definition erases to its
kername, which is neither `ElimBody` shape — the fact the arm turns into `¬ RuntimeKey`. -/
theorem erases_ne_elimBody_fires (Us : List Name) (Δ : VLCtx) (us : List Level)
    (iid : InductiveId) (np dp : Nat) (nfs : List Nat) :
    ¬ ElimBody iid np dp nfs (.const (toKername blkDef)) :=
  erases_ne_elimBody (erases_const_fires Us Δ us)

end LeanToLambdaBox
