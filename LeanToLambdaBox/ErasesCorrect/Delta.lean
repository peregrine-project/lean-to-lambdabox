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

What the arm must first exclude is the *eliminator* reading of the spine, `Lower.elimApp`.
It is excluded outright: `ErasesEnv.defns` exhibits the tabled constant's entry as an
erasure image, and `erases_ne_elimBody` says no erasure image is an eliminator body —
`Erases` emits neither a `.case` node nor a `.fix` node, and the two `ElimBody` shapes carry
one each. What it cannot exclude from `hspec` is the *constructor* reading of the head, in
which the key is not reached at all; `TabledNotCtor` is that fact, taken as a premise.

`SEval.deltaC`'s `hnd` is spent only in rebuilding the source derivation for the boxed
readings: the eliminator configuration it rules out is already gone here.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-- An erasure image that is a λ has an erasure image as its body. -/
theorem erases_target_lambda {env : VEnv} {Us : List Name} :
    ∀ {Δ : VLCtx} {e : Expr} {n : BinderName} {b : LBTerm},
      Erases env Us Δ e (.lambda n b) → ∃ Δ' e', Erases env Us Δ' e' b := by
  intro Δ e n b h
  generalize ht : LBTerm.lambda n b = t at h
  induction h generalizing n b with
  | box | bvar | fvar | ctor | const | app | letE | proj => exact LBTerm.noConfusion ht
  | lam _ hb => injection ht with _ hbb; exact ⟨_, _, hbb ▸ hb⟩
  | lit _ _ ih => exact ih ht
  | mdata _ ih => exact ih ht

/-- Peeling a λ-telescope off an erasure image. -/
theorem erases_mkLambdas_inv {env : VEnv} {Us : List Name} :
    ∀ (ns : List BinderName) {Δ : VLCtx} {e : Expr} {body : LBTerm},
      Erases env Us Δ e (mkLambdas ns body) → ∃ Δ' e', Erases env Us Δ' e' body
  | [], _, _, _, h => ⟨_, _, h⟩
  | _ :: ns, _, _, _, h => by
      obtain ⟨_, _, h'⟩ := erases_target_lambda h
      exact erases_mkLambdas_inv ns h'

/-- No erasure image is a `.case` node: the source language has no match node, and every
alternative the target carries is built by the pass. -/
theorem erases_ne_case {env : VEnv} {Us : List Name} {Δ : VLCtx} {e : Expr} {t : LBTerm}
    (h : Erases env Us Δ e t) :
    ∀ (ip : InductiveId × Nat) (d : LBTerm) (alts : List (List BinderName × LBTerm)),
      t ≠ .case ip d alts := by
  induction h with
  | box | bvar | fvar | ctor | const | app | lam | letE | proj =>
      exact fun _ _ _ => LBTerm.noConfusion
  | lit _ _ ih | mdata _ ih => exact ih

/-- No erasure image is a `.fix` node: the block closure is the pass's, not the erasure's. -/
theorem erases_ne_fix {env : VEnv} {Us : List Name} {Δ : VLCtx} {e : Expr} {t : LBTerm}
    (h : Erases env Us Δ e t) :
    ∀ (defs : List (@FixDef LBTerm)) (i : Nat), t ≠ .fix defs i := by
  induction h with
  | box | bvar | fvar | ctor | const | app | lam | letE | proj =>
      exact fun _ _ => LBTerm.noConfusion
  | lit _ _ ih | mdata _ ih => exact ih

/-- **No erasure image is an eliminator body.** Both `ElimBody` shapes carry a node the
erasure never emits: a `.case` under a λ-telescope, or a `.fix`. -/
theorem erases_ne_elimBody {env : VEnv} {Us : List Name} {Δ : VLCtx} {e : Expr}
    {t : LBTerm} {iid : InductiveId} {np dp : Nat} {nfs : List Nat}
    (h : Erases env Us Δ e t) : ¬ ElimBody iid np dp nfs t := by
  intro he
  cases he with
  | cases =>
      obtain ⟨_, _, h'⟩ := erases_mkLambdas_inv _ h
      exact erases_ne_case h' _ _ _ rfl
  | recur => exact erases_ne_fix h _ _ rfl

/-! ## The `Lower` readings of a tabled constant's spine -/

/-- **A lowered spine at a constant head that is not a runtime key.** The `elimApp`
reading is excluded by the guard, so the whole spine is the congruence reading: head to
head, argument to argument. -/
theorem Lower.source_constSpine {Γ : GlobalDeclarations} (hblk : BlockBodiesLambda Γ)
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
      rcases Lower.source_app hblk hlow rfl with
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

/-- A block member's own body has the block's `.fix` node as an image: `fixBody` at the
member the declaration pins. -/
theorem Lower.fixBody_of_block {Γ : GlobalDeclarations} {kns : List Kername}
    {bs bs' : List LBTerm} {ids : List FVarId} {defs : List (@FixDef LBTerm)} {j : Nat}
    {kn : Kername} {b : LBTerm} (hblock : LowerBlock Γ kns bs bs' ids defs)
    (hj : kns[j]? = some kn) (hd : DefnDecl Γ kn b) : Lower Γ b (.fix defs j) := by
  obtain ⟨hjl, hje⟩ := Lower.getElem!_of_getElem? hj
  have hdecl := hblock.hdecl j hjl
  rw [hje] at hdecl
  have hbb : bs[j]! = b := by simpa using (hdecl.symm.trans hd)
  refine Lower.fixBody' hblock ?_ (by rw [hblock.hd]; omega)
  rw [← hbb, getElem?_pos bs j (by rw [hblock.hb]; omega),
    ← getElem!_pos bs j (by rw [hblock.hb]; omega)]

/-- **What a tabled constant's image evaluates like.** Either it is the constant itself,
or — at a block member — it is an image of the constant's own body, the block's `.fix`
node. Neither reading is available at a runtime key. -/
theorem Lower.const_body {Γ : GlobalDeclarations} (hblk : BlockBodiesLambda Γ)
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
  | @fixConst kn' kns bs bs' ids defs j hb hb' hdf hnd hids hilen hfresh hrarg hdecl
      hlow hcl hnk hj =>
      have he : kn' = kn := by injection hs
      subst he
      exact ⟨hnk, .inr (Lower.fixBody_of_block
        ⟨hb, hb', hdf, hnd, hids, hilen, hfresh, hrarg, hdecl, hlow, hcl⟩ hj hd)⟩
  | @fixBody b₀ kns bs bs' ids defs j hb hb' hdf hnd hids hilen hfresh hrarg hdecl hlow
      hcl hj hjl =>
      exfalso
      obtain ⟨hjb, hjeq⟩ := Lower.getElem!_of_getElem? hj
      have hlam := hblk kns bs bs' ids defs
        ⟨hb, hb', hdf, hnd, hids, hilen, hfresh, hrarg, hdecl, hlow, hcl⟩ j (by omega)
      rw [hjeq, hs] at hlam
      simp [isLambda] at hlam

/-! ## What the compiler table owes -/

/-- **A tabled constant is not a constructor.** At a constructor's name the erasure emits
a `.construct` node and reaches no key for it, so `ErasesEnv` says nothing there and this
stays a fact about the compiler table itself. Without it the δ arm's head could erase to a
constructor node the target is stuck on while the source unfolds a body. -/
def TabledNotCtor (env : VEnv) (bo : Name → Option Expr) : Prop :=
  ∀ c b, bo c = some b → ∀ I k, ¬ CtorOf env c I k

/-- The premise follows from the table's positive reading — every tabled constant is
declared as a definition — together with `UpstreamAsks`' exclusion of the other two
readings. -/
theorem TabledNotCtor.of_constOrigin {env : VEnv} {bo : Name → Option Expr}
    (A : UpstreamAsks env) (h : ∀ c b, bo c = some b → ConstOrigin env c) :
    TabledNotCtor env bo :=
  fun c b hbo I k => constOrigin_not_ctorOf A (h c b hbo) I k

/-- An empty compiler table is a table: the premise is inhabited. -/
theorem tabledNotCtor_none {env : VEnv} : TabledNotCtor env (fun _ => none) := by
  intro c b h
  exact absurd h (by simp)

/-! ## The arm -/

/-- **The δ arm.** The head erases to the tabled constant's kername; the constructor
reading is `TabledNotCtor`'s and the boxed readings fold. The spine lowers as a
congruence, since a tabled constant is no runtime key — its specification body is an
erasure image, and no erasure image is an eliminator body. The induction hypothesis is
taken at the lowering whose head is what the target head evaluates to: the emitted body,
or the block's node at a member. `WcbvEval.mkApps_congr` then moves the run it produced
onto the spine, replacing the head by one `WcbvEval.delta` step or by nothing. -/
theorem step_delta {env : VEnv} {bo : Name → Option Expr} {Us : List Name}
    {fl : SEvalFlags} {Γspec Γ : GlobalDeclarations} (hbo : TabledNotCtor env bo) :
    StepDelta env bo Us fl Γspec Γ := by
  intro c us ups args argsv b b' v henv henvL hfl hbd hnd hinst hlen hargs hdef hcont
    ihcont ve t₀ t hwt her hlow hspec
  have hblk : BlockBodiesLambda Γspec := henvL.specBlocks
  have hargEv : ∀ (a : Expr), a ∈ args → ∀ (s u : LBTerm), Erases env Us [] a s →
      ErasesEnv env bo Γspec s → Lower Γspec s u → ∃ x, WcbvEval Γ eraseFlags u x := by
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
    refine erases_correct_boxSpineLow henv hblk hwt hbw hlow hspec (fun s hs u hsu => ?_) hev
    obtain ⟨a, ha, hea⟩ := forall₂_mem_right hts s hs
    exact hargEv a (List.mem_append_right _ ha) s u hea
      (hspec.subterm (subTerm_mkApps_arg ts .box s hs)) hsu
  rcases Erases.const_inv hth with ⟨hb, rfl⟩ | ⟨I', iid', k', np', nfs', hc', hi', rfl⟩ |
    ⟨-, ho, rfl⟩
  · refine erases_correct_boxSpineLow (pre := []) (suf := args) henv hblk hwt hb hlow
      hspec (fun s hs u hsu => ?_) hev
    obtain ⟨a, ha, hea⟩ := forall₂_mem_right hts s hs
    exact hargEv a ha s u hea (hspec.subterm (subTerm_mkApps_arg ts .box s hs)) hsu
  · exact absurd hc' (hbo c b hbd I' k')
  · have hlents : args.length = ts.length := hts.length_eq
    have hreach : ReachableFrom Γspec (LBTerm.mkApps (.const (toKername c)) ts) (toKername c) :=
      ReachableFrom.subterm (subTerm_mkApps_head ts .refl)
        (reachableFrom_of_mem_constRefs (by simp [constRefs]))
    obtain ⟨b₀, hlook, herb⟩ := hspec.defns c b hbd hreach
    have hdefn : DefnDecl Γspec (toKername c) b₀ := hlook
    have herb' : Erases env Us [] b' b₀ := by rw [hinst]; exact herb Us ups us
    have hnk : ¬ RuntimeKey Γspec (toKername c) := by
      rintro ⟨iid, np, dp, nfs, ⟨body, hbody, helim⟩, -⟩
      rw [hlook] at hbody
      obtain rfl : b₀ = body := by simpa using hbody
      exact erases_ne_elimBody herb' helim
    obtain ⟨hd', ts', rfl, hhd, hlen', hpt⟩ := Lower.source_constSpine hblk hnk ts hlow
    obtain ⟨H, hlowH, hstep⟩ : ∃ H, Lower Γspec b₀ H ∧
        ∀ w, WcbvEval Γ eraseFlags H w → WcbvEval Γ eraseFlags hd' w := by
      rcases (Lower.const_body hblk hhd rfl hdefn).2 with rfl | hbody
      · obtain ⟨bΓ, hbΓ⟩ := henvL.defsTotal _ b₀ hdefn hnk
        refine ⟨bΓ, ?_, fun w hw => .delta hbΓ hw⟩
        rcases henvL.defs _ b₀ bΓ hdefn hbΓ with hl | ⟨kns, bs, defs, j, hfix, hj, rfl⟩
        · exact hl
        · obtain ⟨bs', ids, hblock⟩ := hfix
          exact Lower.fixBody_of_block hblock hj hdefn
      · exact ⟨hd', hbody, fun _ hw => hw⟩
    have hchoice : ∀ i, i < args.length → ∃ p : LBTerm × LBTerm,
        Erases env Us [] argsv[i]! p.1 ∧ Lower Γspec p.1 p.2 ∧
          WcbvEval Γ eraseFlags ts'[i]! p.2 ∧ ErasesEnv env bo Γspec p.1 := by
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
    have hspeccon : ErasesEnv env bo Γspec (LBTerm.mkApps b₀ (ps.map Prod.fst)) := by
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

/-- Every member body of every block over the fix fixture's specification environment is a
λ: its two entries are. -/
theorem blockBodiesLambda_lowerFixFixture : BlockBodiesLambda LowerFixFixture.specEnv := by
  intro kns bs bs' ids defs hblock j hj
  obtain ⟨nm, u, hb⟩ := LowerFixFixture.specEnv_body (hblock.hdecl j hj)
  rw [hb]; rfl

/-- **The head reading fires at a block member.** `Lower.const_body` reads member 1's
`.fix` image as an image of the member's own body — the lowering the arm hands the
induction hypothesis. -/
theorem const_body_fires :
    Lower LowerFixFixture.specEnv LowerFixFixture.b₁ (.fix LowerFixFixture.defs 1) := by
  rcases (Lower.const_body blockBodiesLambda_lowerFixFixture
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
    Lower.source_constSpine blockBodiesLambda_lowerFixFixture
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
