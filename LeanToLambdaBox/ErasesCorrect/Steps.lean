import LeanToLambdaBox.ErasesStrengthen
import LeanToLambdaBox.SubjectReduction
import LeanToLambdaBox.Semantics.Metatheory
import LeanToLambdaBox.ErasesLB
import LeanToLambdaBox.ErasesEnv
import LeanToLambdaBox.Origin

/-!
# What the simulation's arms consume: spines, the `□` arms, the step interfaces

`erases_correct` is one induction on `SEval`, at the **emitted** environment, with the ι,
projection and δ arms as step lemmas. This module sits below both the aggregator and the
arm files and holds what they share:

* `trExprS_spine_mem` — every argument of a translated spine translates;
* `Erases.mkApps_forall₂` and `erases_mkApps_inv` — erasure along a spine, and the inversion
  splitting an erased spine into a head erasure with pointwise arguments or a boxed proper
  prefix: the ι arm's own case split;
* `erasable_mkApps` — a spine whose head is irrelevant is irrelevant, `Erasable.app`
  iterated;
* `erases_correct_box`/`erases_correct_boxSpine` at the erasure alone, and
  `erases_correct_boxLow`/`erases_correct_boxSpineLow` at the composite;
* the `Lower` inversions the arms take at a `.app` node, at a spine and at a λ, and
  `Lower.appReady`, the β transport across a block's `.fix` node;
* the closure kit `ErasesEnv.{subterm, ofReach, box, substPair, mkApps}` — every clause of
  the environment relation is antitone in the term — and `ErasesEnv.ctorArity`, the emitted
  arity of a reached block;
* `SEval.no_elimSpine_value` and `erases_elimSpine_no_value` — an eliminator spine one
  minor short heads no value, and is the erasure of no source term that has one — with
  `ErasesEnv.runtimeKey_isCasesOn` and the erasure-image exclusions they run on;
* `TabledLevels` and `Erases.instantiateLevelParams_of_stepDefeq` — the level scope a tabled
  body is erased at, as the bridge asks it of a whole table, and the transport of that erasure
  to the scope the δ rule unfolds it at, as the δ arm reads it off `ErasesEnv.defns`;
* `Simulates`, `StepIota`, `StepProj`, `StepDelta` — the induction's motive and the three
  step interfaces — and `ErasesCorrectStmt`/`ErasesCorrectLBStmt`, the statements
  `ErasesCorrect/Close.lean` inhabits.

The arm files import this module and never the aggregator, which is what keeps the wave's
module graph acyclic.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-! ## Source-side spines -/

/-- Every element of a translated application spine translates. -/
theorem trExprS_spine_mem {env : VEnv} {Us : List Name} {Δ : VLCtx} :
    ∀ (as : List Expr) {hd : Expr} {ve : VExpr},
      TrExprS env Us Δ (mkApps hd as) ve → ∀ a ∈ as, ∃ w, TrExprS env Us Δ a w
  | [], _, _, _, _, ha => absurd ha (by simp)
  | b :: as, hd, _, htr, a, ha => by
      rw [mkApps_cons] at htr
      rcases List.mem_cons.1 ha with rfl | ha'
      · obtain ⟨_, htr'⟩ := trExprS_spine_head as htr
        cases htr' with | app _ _ _ htra => exact ⟨_, htra⟩
      · exact trExprS_spine_mem as htr a ha'

/-! ## `Erases` over a spine -/

/-- Erasure is a congruence along an application spine, at a pointwise argument
relation. -/
theorem Erases.mkApps_forall₂ {env : VEnv} {Us : List Name} {Δ : VLCtx} :
    ∀ {as : List Expr} {ts : List LBTerm}, List.Forall₂ (Erases env Us Δ) as ts →
      ∀ {hd : Expr} {th : LBTerm}, Erases env Us Δ hd th →
        Erases env Us Δ (_root_.LeanToLambdaBox.mkApps hd as)
          (LBTerm.mkApps th ts) := by
  intro as ts hall
  induction hall with
  | nil => exact fun h => h
  | cons ha _ ih => exact fun h => ih (.app h ha)

/--
Inversion along an application spine: either the spine erases structurally, head and
arguments separately, or some prefix of it erases to `□` and the suffix's erasures are
applied to that `□`.
-/
theorem erases_mkApps_inv {env : VEnv} {Us : List Name} {Δ : VLCtx} :
    ∀ (as : List Expr) {hd : Expr} {t : LBTerm},
      Erases env Us Δ (mkApps hd as) t →
      (∃ th ts, Erases env Us Δ hd th ∧ List.Forall₂ (Erases env Us Δ) as ts ∧
          t = LBTerm.mkApps th ts) ∨
      (∃ pre suf ts, as = pre ++ suf ∧
          (∃ ve, TrExprS env Us Δ (mkApps hd pre) ve ∧
            Erasable env Us.length Δ.toCtx ve) ∧
          List.Forall₂ (Erases env Us Δ) suf ts ∧ t = LBTerm.mkApps .box ts)
  | [], _, _, h => .inl ⟨_, [], h, .nil, rfl⟩
  | a :: as, hd, t, h => by
      rw [mkApps_cons] at h
      rcases erases_mkApps_inv as h with ⟨th, ts, hth, hts, rfl⟩ | ⟨pre, suf, ts, heq, hb, hts, rfl⟩
      · rcases Erases.app_inv hth with ⟨⟨ve, htr, her⟩, rfl⟩ | ⟨th', ta, hf, ha, rfl⟩
        · exact .inr ⟨[a], as, ts, rfl, ⟨ve, htr, her⟩, hts, rfl⟩
        · exact .inl ⟨th', ta :: ts, hf, .cons ha hts, rfl⟩
      · exact .inr ⟨a :: pre, suf, ts, by rw [heq]; rfl, hb, hts, rfl⟩

/-- An application spine whose head is irrelevant is irrelevant: `Erasable.app`, iterated
along the spine. -/
theorem erasable_mkApps {env : VEnv} (henv : env.WF) {Us : List Name} {Δ : VLCtx}
    (hΔ : VLCtx.WF env Us.length Δ) :
    ∀ (as : List Expr) {hd : Expr} {ve hve : VExpr},
      TrExprS env Us Δ (mkApps hd as) ve → TrExprS env Us Δ hd hve →
      Erasable env Us.length Δ.toCtx hve → Erasable env Us.length Δ.toCtx ve
  | [], _, _, _, htr, htrh, her =>
      her.defeq henv hΔ.toCtx
        (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrh htr)
  | a :: as, hd, ve, hve, htr, htrh, her => by
      rw [mkApps_cons] at htr
      obtain ⟨_, htrw⟩ := trExprS_spine_head as htr
      cases htrw with
      | @app f' A B a' _ _ _ hTf hTa htrf htra =>
        have hf' : Erasable env Us.length Δ.toCtx f' :=
          her.defeq henv hΔ.toCtx
            (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrh htrf)
        exact erasable_mkApps henv hΔ as htr (.app hTf hTa htrf htra)
          (hf'.app henv hΔ.toCtx hTf hTa)

/-! ## Pointwise lists

`List.Forall₂` is the shape the spine lemmas induct on; `SEval`'s premises are indexed by
position, so the two forms are bridged here.
-/

/-- Read one position of a pointwise relation. -/
theorem forall₂_getElem! {α β : Type _} [Inhabited α] [Inhabited β] {R : α → β → Prop} :
    ∀ {l : List α} {m : List β}, List.Forall₂ R l m → ∀ i, i < l.length → R l[i]! m[i]!
  | _, _, .nil, _, hi => absurd hi (by simp)
  | _, _, .cons h _, 0, _ => by simpa using h
  | _, _, .cons _ hrest, i + 1, hi => by
      simpa using forall₂_getElem! hrest i (by simpa using hi)

/-- Build a pointwise relation from equal lengths and a positionwise proof. -/
theorem forall₂_of_getElem! {α β : Type _} [Inhabited α] [Inhabited β] {R : α → β → Prop} :
    ∀ {l : List α} {m : List β}, l.length = m.length →
      (∀ i, i < l.length → R l[i]! m[i]!) → List.Forall₂ R l m
  | [], [], _, _ => .nil
  | _ :: l, _ :: m, hlen, h =>
      .cons (by simpa using h 0 (by simp))
        (forall₂_of_getElem! (by simpa using hlen)
          (fun i hi => by simpa using h (i + 1) (by simpa using hi)))
  | [], _ :: _, hlen, _ => absurd hlen (by simp)
  | _ :: _, [], hlen, _ => absurd hlen (by simp)

/-- Split a pointwise existential into a witness list and the two relations it satisfies. -/
theorem forall₂_split {α β γ : Type _} {R₁ : α → γ → Prop} {R₂ : β → γ → Prop} :
    ∀ {l : List α} {m : List β},
      List.Forall₂ (fun a b => ∃ c, R₁ a c ∧ R₂ b c) l m →
      ∃ n : List γ, List.Forall₂ R₁ l n ∧ List.Forall₂ R₂ m n
  | _, _, .nil => ⟨[], .nil, .nil⟩
  | _, _, .cons h hrest =>
      let ⟨c, h1, h2⟩ := h
      let ⟨n, hn1, hn2⟩ := forall₂_split hrest
      ⟨c :: n, .cons h1 hn1, .cons h2 hn2⟩

/-- Every element on the right of a pointwise relation is related to one on the left. -/
theorem forall₂_mem_right {α β : Type _} {R : α → β → Prop} :
    ∀ {l : List α} {m : List β}, List.Forall₂ R l m → ∀ b ∈ m, ∃ a ∈ l, R a b
  | _, _, .nil, _, hb => absurd hb (by simp)
  | _, _, .cons (a := a) h hrest, b, hb => by
      rcases List.mem_cons.1 hb with rfl | hb'
      · exact ⟨a, List.mem_cons_self .., h⟩
      · obtain ⟨a', ha', hr⟩ := forall₂_mem_right hrest b hb'
        exact ⟨a', List.mem_cons_of_mem _ ha', hr⟩

/-! ## The `□` arms -/

/-- **The box arm, once for every rule.** A source term whose erasure is `□` has an
irrelevant value, and `□` is already a λ□ value. -/
theorem erases_correct_box {env : VEnv} (henv : env.WF) {Us : List Name} {Δ : VLCtx}
    (hΔ : VLCtx.WF env Us.length Δ) {bo : Name → Option Expr} {fl : SEvalFlags}
    {Γ : GlobalDeclarations} {e v : Expr} {ve : VExpr}
    (htr : TrExprS env Us Δ e ve)
    (hbox : ∃ we, TrExprS env Us Δ e we ∧ Erasable env Us.length Δ.toCtx we)
    (hev : SEval env bo Us fl Δ e v) :
    ∃ v', Erases env Us Δ v v' ∧ WcbvEval Γ eraseFlags .box v' := by
  obtain ⟨we, htrw, herw⟩ := hbox
  obtain ⟨vv, htrv, hdef⟩ := SEval.defeq henv hΔ htr hev
  have h1 : Erasable env Us.length Δ.toCtx ve :=
    herw.defeq henv hΔ.toCtx
      (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrw htr)
  exact ⟨.box, .box htrv (h1.defeq henv hΔ.toCtx hdef), .box⟩

/-- **The box arm at a spine.** A prefix of the spine erases to `□`, so the whole spine is
irrelevant and the target reaches `□` by iterated `eval_box`. -/
theorem erases_correct_boxSpine {env : VEnv} (henv : env.WF) {Us : List Name} {Δ : VLCtx}
    (hΔ : VLCtx.WF env Us.length Δ) {bo : Name → Option Expr} {fl : SEvalFlags}
    {Γ : GlobalDeclarations} {hd : Expr} {pre suf : List Expr} {ts : List LBTerm}
    {ve : VExpr} {v : Expr}
    (htr : TrExprS env Us Δ (mkApps hd (pre ++ suf)) ve)
    (hbox : ∃ we, TrExprS env Us Δ (mkApps hd pre) we ∧ Erasable env Us.length Δ.toCtx we)
    (hts : ∀ s ∈ ts, ∃ x, WcbvEval Γ eraseFlags s x)
    (hev : SEval env bo Us fl Δ (mkApps hd (pre ++ suf)) v) :
    ∃ v', Erases env Us Δ v v' ∧ WcbvEval Γ eraseFlags (LBTerm.mkApps .box ts) v' := by
  obtain ⟨we, htrw, herw⟩ := hbox
  rw [mkApps_append] at htr
  have herve : Erasable env Us.length Δ.toCtx ve :=
    erasable_mkApps henv hΔ suf htr htrw herw
  obtain ⟨vv, htrv, hdef⟩ := SEval.defeq henv hΔ (mkApps_append hd pre suf ▸ htr) hev
  exact ⟨.box, .box htrv (herve.defeq henv hΔ.toCtx hdef),
    WcbvEval.mkApps_box ts hts .box⟩

/-! ## `Lower` at the shapes the arms invert

`Lower.elimApp` is indexed by an application spine, so inverting the pass at an `.app` node
or at a spine means reading that arm's shape back first. `Lower.lean`'s `source_*` kit does
this for every node the pass has a congruence arm for; what the simulation needs beyond it
is the `.app` node, where the `elimApp` reading survives, and the spine.
-/

/-- The spine head of a term that is not itself an application is the term. -/
theorem spineHead_of_not_app {f : LBTerm} (hf : ∀ g b, f ≠ .app g b) :
    LBTerm.spineHead f = f := by
  cases f with
  | app g b => exact absurd rfl (hf g b)
  | _ => rfl

/-- Two spines with non-application heads agree head by head and argument by argument. -/
theorem mkApps_head_inj {f g : LBTerm} {ts us : List LBTerm}
    (hf : ∀ x y, f ≠ .app x y) (hg : ∀ x y, g ≠ .app x y)
    (h : LBTerm.mkApps f ts = LBTerm.mkApps g us) : f = g ∧ ts = us := by
  have h1 := congrArg LBTerm.spineHead h
  have h2 := congrArg LBTerm.spineArgs h
  rw [LBTerm.spineHead_mkApps, LBTerm.spineHead_mkApps, spineHead_of_not_app hf,
    spineHead_of_not_app hg] at h1
  rw [LBTerm.spineArgs_mkApps, LBTerm.spineArgs_mkApps] at h2
  refine ⟨h1, ?_⟩
  have hfa : LBTerm.spineArgs f = [] := by cases f with
    | app x y => exact absurd rfl (hf x y)
    | _ => rfl
  have hga : LBTerm.spineArgs g = [] := by cases g with
    | app x y => exact absurd rfl (hg x y)
    | _ => rfl
  rw [hfa, hga] at h2; simpa using h2

/-- A non-empty spine read as an application: the function is the spine of the initial
segment and the argument is the last entry. -/
theorem mkApps_eq_app {f g a : LBTerm} {l : List LBTerm} {x : LBTerm}
    (h : LBTerm.mkApps f (l ++ [x]) = .app g a) : g = LBTerm.mkApps f l ∧ a = x := by
  rw [LBTerm.mkApps_concat] at h
  injection h with h1 h2
  exact ⟨h1.symm, h2.symm⟩

/-- Splitting a pointwise-related pair of lists at the last entry: the inverse of
`Lower.concat`, at an arbitrary relation. -/
theorem unconcat_index {α : Type} [Inhabited α] {R : α → α → Prop} {l l' : List α} {x : α}
    (hlen : l'.length = (l ++ [x]).length)
    (h : ∀ i, i < (l ++ [x]).length → R (l ++ [x])[i]! l'[i]!) :
    ∃ (m : List α) (y : α), l' = m ++ [y] ∧ m.length = l.length ∧
      (∀ i, i < l.length → R l[i]! m[i]!) ∧ R x y := by
  have hne : l' ≠ [] := by
    intro he; rw [he] at hlen; simp at hlen
  refine ⟨l'.dropLast, l'.getLast hne, (List.dropLast_concat_getLast hne).symm, ?_, ?_, ?_⟩
  · have := List.length_dropLast (xs := l'); rw [hlen] at this; simpa using this
  · intro i hi
    have hi' : i < (l ++ [x]).length := by simp; omega
    have hd : i < l'.dropLast.length := by
      have := List.length_dropLast (xs := l'); rw [hlen] at this; simp at this ⊢; omega
    have := h i hi'
    rw [getElem!_pos (l ++ [x]) i hi', List.getElem_append_left hi, ← getElem!_pos l i hi] at this
    rw [getElem!_pos l'.dropLast i hd, List.getElem_dropLast,
      ← getElem!_pos l' i (by omega)]
    exact this
  · have hxi : l.length < (l ++ [x]).length := by simp
    have := h l.length hxi
    rw [getElem!_append_singleton l x] at this
    have hgl : l'[l.length]! = l'.getLast hne := by
      rw [getElem!_pos l' l.length (by omega), List.getLast_eq_getElem]
      congr 1
      simp at hlen; omega
    rwa [hgl] at this

/-- **The two readings of a lowered application.** The `app` congruence, or a *saturated*
eliminator spine: `elimApp` with a non-empty `extra` re-associates into the congruence
reading, and the three block arms are excluded by `Lower.ne_block_image`, an application
being neither a constant nor a λ. -/
theorem Lower.source_app {Γ : GlobalDeclarations}
    {s t f a : LBTerm} (h : Lower Γ s t) (hs : s = .app f a) :
    (∃ f' a', t = .app f' a' ∧ Lower Γ f f' ∧ Lower Γ a a') ∨
    (∃ (kn : Kername) (iid : InductiveId) (np dp : Nat) (nfs : List Nat)
        (pre : List LBTerm) (disc : LBTerm) (minors : List LBTerm),
      ElimDecl Γ kn iid np dp nfs ∧ pre.length = dp ∧ minors.length = nfs.length ∧
      LBTerm.app f a = LBTerm.mkApps (.const kn) (pre ++ disc :: minors)) := by
  have hni := Lower.ne_block_image h (by rw [hs]; exact fun _ => LBTerm.noConfusion)
    (by rw [hs]; rfl)
  cases h with
  | @app f₀ f' a₀ a' hf ha =>
      injection hs with hff haa
      subst hff; subst haa
      exact .inl ⟨f', a', rfl, hf, ha⟩
  | box | bvar | fvar | prim | const | lambda | letIn | proj | construct | «case» =>
      exact LBTerm.noConfusion hs
  | fixConst | fixBody => exact absurd rfl (hni.1 _ _)
  | fixEta => exact absurd hni.2 (by simp [isLambda])
  | @elimApp kn iid np dp nfs pre disc disc' minors alts extra extra'
      hh hlen hmlen halen hmin hdisc hxlen hx =>
      rcases List.eq_nil_or_concat extra with rfl | ⟨init, last, rfl⟩
      · refine .inr ⟨kn, iid, np, dp, nfs, pre, disc, minors, hh, hlen, hmlen, ?_⟩
        rw [← hs]; simp
      · rw [List.concat_eq_append] at hxlen hx hs
        obtain ⟨init', last', rfl, hilen, hi, hlast⟩ := unconcat_index hxlen hx
        have hsrc : (pre ++ disc :: minors) ++ (init ++ [last])
            = ((pre ++ disc :: minors) ++ init) ++ [last] := by simp
        rw [hsrc] at hs
        obtain ⟨hfe, hae⟩ := mkApps_eq_app hs
        subst hfe; subst hae
        refine .inl ⟨LBTerm.mkApps (.case (iid, np) disc' alts) init', last', ?_,
          ?_, hlast⟩
        · exact LBTerm.mkApps_concat _ _ _
        · exact Lower.elimApp hh hlen hmlen halen hmin hdisc hilen hi

/-- **A lowered spine, at a head the pass has no key for.** A head that is neither an
application nor a constant cannot be `elimApp`'s, so the whole spine is the congruence
reading: head to head, argument to argument. -/
theorem Lower.source_mkApps {Γ : GlobalDeclarations}
    {hd : LBTerm} (hne : ∀ x y, hd ≠ .app x y) (hnc : ∀ kn, hd ≠ .const kn) :
    ∀ (ts : List LBTerm) {t : LBTerm}, Lower Γ (LBTerm.mkApps hd ts) t →
      ∃ (hd' : LBTerm) (ts' : List LBTerm), t = LBTerm.mkApps hd' ts' ∧ Lower Γ hd hd' ∧
        ts'.length = ts.length ∧ ∀ i, i < ts.length → Lower Γ ts[i]! ts'[i]! := by
  suffices h : ∀ (n : Nat) (ts : List LBTerm), ts.length = n → ∀ {t : LBTerm},
      Lower Γ (LBTerm.mkApps hd ts) t →
      ∃ (hd' : LBTerm) (ts' : List LBTerm), t = LBTerm.mkApps hd' ts' ∧ Lower Γ hd hd' ∧
        ts'.length = ts.length ∧ ∀ i, i < ts.length → Lower Γ ts[i]! ts'[i]! from
    fun ts t hlow => h ts.length ts rfl hlow
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro ts hn t hlow
    rcases List.eq_nil_or_concat ts with rfl | ⟨init, last, rfl⟩
    · exact ⟨t, [], rfl, hlow, rfl, by simp⟩
    · rw [List.concat_eq_append, LBTerm.mkApps_concat] at hlow
      rcases Lower.source_app hlow rfl with
        ⟨f', a', rfl, hf, ha⟩ | ⟨kn, iid, np, dp, nfs, pre, disc, minors, _, _, _, heq⟩
      · obtain ⟨hd', is', rfl, hhd, hilen, hi⟩ :=
          ih init.length (by simp [List.concat_eq_append] at hn; omega) init rfl hf
        refine ⟨hd', is' ++ [a'], (LBTerm.mkApps_concat _ _ _).symm, hhd, ?_, ?_⟩
        · rw [List.concat_eq_append]; exact (Lower.concat hilen hi ha).1
        · rw [List.concat_eq_append]; exact (Lower.concat hilen hi ha).2
      · exfalso
        have heq' : LBTerm.mkApps hd (init ++ [last])
            = LBTerm.mkApps (.const kn) (pre ++ disc :: minors) := by
          rw [LBTerm.mkApps_concat]; exact heq
        obtain ⟨hhd, -⟩ :=
          mkApps_head_inj hne (fun _ _ => LBTerm.noConfusion) heq'
        exact hnc kn hhd

/-- A subterm of a spine's head is a subterm of the spine. -/
theorem subTerm_mkApps_head : ∀ (ts : List LBTerm) {f d : LBTerm}, SubTerm d f →
    SubTerm d (LBTerm.mkApps f ts)
  | [], _, _, h => h
  | _ :: ts, _, _, h => subTerm_mkApps_head ts (.appFn h)

/-- Every argument of an application spine is a subterm of it. -/
theorem subTerm_mkApps_arg : ∀ (ts : List LBTerm) (f x : LBTerm), x ∈ ts →
    SubTerm x (LBTerm.mkApps f ts)
  | t :: ts, f, x, hx => by
      rcases List.mem_cons.1 hx with rfl | hx'
      · exact subTerm_mkApps_head ts (.appArg .refl)
      · exact subTerm_mkApps_arg ts (.app f t) x hx'

/-- Everything a specification environment says of a program it says of a subterm: the five
reachability-triggered clauses are antitone in the term, and `keys` and `tabled` mention it
at all. -/
theorem ErasesEnv.subterm {env : VEnv} {bo : Name → Option Expr} {lp : Name → List Name}
    {Γspec : GlobalDeclarations} {d t : LBTerm} (h : ErasesEnv env bo lp Γspec t)
    (hs : SubTerm d t) : ErasesEnv env bo lp Γspec d :=
  .mk h.keys (fun kn hr => h.deps kn (hr.subterm hs)) h.tabled
    (fun c b hbo hr => h.defns c b hbo (hr.subterm hs))
    (fun c hbo hco hnc hr => h.axioms c hbo hco hnc (hr.subterm hs))
    (fun hi hr => h.blocks hi (hr.subterm hs))
    (fun hsh hinf hco hr => h.elims hsh hinf hco (hr.subterm hs))

/-- Nothing is reachable from `□`. -/
theorem not_reachableFrom_box {Γ : GlobalDeclarations} {kn : Kername} :
    ¬ ReachableFrom Γ .box kn := by
  intro h
  rw [ReachableFrom, kernameElem_iff, reachRefs] at h
  rw [show constRefs (.box : LBTerm) = [] from rfl, reachFrom_nil] at h
  exact absurd h (by simp)

/-- The kernames of a spine are the head's and the arguments'. -/
theorem constRefs_mkApps : ∀ (l : List LBTerm) (f : LBTerm),
    constRefs (LBTerm.mkApps f l) = constRefs f ++ l.flatMap constRefs
  | [], f => by simp
  | a :: l, f => by
      rw [LBTerm.mkApps, constRefs_mkApps l (.app f a)]
      simp [constRefs, List.append_assoc]

/-- What a spine reaches, its head or one of its arguments reaches. -/
theorem ReachableFrom.mkApps_inv {Γ : GlobalDeclarations} {kn : Kername}
    (l : List LBTerm) (f : LBTerm) (h : ReachableFrom Γ (LBTerm.mkApps f l) kn) :
    ReachableFrom Γ f kn ∨ ∃ x ∈ l, ReachableFrom Γ x kn := by
  rw [ReachableFrom, kernameElem_iff, reachRefs, constRefs_mkApps] at h
  rcases reachFrom_append _ h with h | h
  · exact .inl (kernameElem_iff.2 h)
  · exact .inr (mem_reachFrom_flatMap l h)

/-- The environment relation reads only the program's reachable kernames. -/
theorem ErasesEnv.ofReach {env : VEnv} {bo : Name → Option Expr} {lp : Name → List Name}
    {Γspec : GlobalDeclarations} {t u : LBTerm} (h : ErasesEnv env bo lp Γspec t)
    (hre : ∀ kn, ReachableFrom Γspec u kn → ReachableFrom Γspec t kn) :
    ErasesEnv env bo lp Γspec u :=
  .mk h.keys (fun kn hr => h.deps kn (hre kn hr)) h.tabled
    (fun c b hbo hr => h.defns c b hbo (hre _ hr))
    (fun c hbo hco hnc hr => h.axioms c hbo hco hnc (hre _ hr))
    (fun hi hr => h.blocks hi (hre _ hr))
    (fun hsh hinf hco hr => h.elims hsh hinf hco (hre _ hr))

/-- `□` is read against every specification environment. -/
theorem ErasesEnv.box {env : VEnv} {bo : Name → Option Expr} {lp : Name → List Name}
    {Γspec : GlobalDeclarations} {t : LBTerm} (h : ErasesEnv env bo lp Γspec t) :
    ErasesEnv env bo lp Γspec .box :=
  h.ofReach (fun _ hr => absurd hr not_reachableFrom_box)

/-- A contractum names no kername its two parts do not: the environment relation survives
the substitution the β and ζ steps perform. -/
theorem ErasesEnv.substPair {env : VEnv} {bo : Name → Option Expr} {lp : Name → List Name}
    {Γspec : GlobalDeclarations} {s b : LBTerm} (hs : ErasesEnv env bo lp Γspec s)
    (hb : ErasesEnv env bo lp Γspec b) :
    ErasesEnv env bo lp Γspec (LBTerm.subst s 0 b) := by
  refine .mk hb.keys (fun kn hr => ?_) hb.tabled (fun c bb hbo hr => ?_)
    (fun c hbo hco hnc hr => ?_) (fun hi hr => ?_) (fun hsh hinf hco hr => ?_) <;>
    rcases ReachableFrom.substList (l := [s]) (t := b) hr with hbr | ⟨x, hx, hxr⟩
  · exact hb.deps kn hbr
  · obtain rfl : x = s := by simpa using hx
    exact hs.deps kn hxr
  · exact hb.defns c bb hbo hbr
  · obtain rfl : x = s := by simpa using hx
    exact hs.defns c bb hbo hxr
  · exact hb.axioms c hbo hco hnc hbr
  · obtain rfl : x = s := by simpa using hx
    exact hs.axioms c hbo hco hnc hxr
  · exact hb.blocks hi hbr
  · obtain rfl : x = s := by simpa using hx
    exact hs.blocks hi hxr
  · exact hb.elims hsh hinf hco hbr
  · obtain rfl : x = s := by simpa using hx
    exact hs.elims hsh hinf hco hxr

/-- A spine is read against the environment its head and its arguments are. -/
theorem ErasesEnv.mkApps {env : VEnv} {bo : Name → Option Expr} {lp : Name → List Name}
    {Γspec : GlobalDeclarations} {f : LBTerm} {l : List LBTerm}
    (hf : ErasesEnv env bo lp Γspec f) (hl : ∀ x ∈ l, ErasesEnv env bo lp Γspec x) :
    ErasesEnv env bo lp Γspec (LBTerm.mkApps f l) := by
  refine .mk hf.keys (fun kn hr => ?_) hf.tabled (fun c bb hbo hr => ?_)
    (fun c hbo hco hnc hr => ?_) (fun hi hr => ?_) (fun hsh hinf hco hr => ?_) <;>
    rcases ReachableFrom.mkApps_inv l f hr with hfr | ⟨x, hx, hxr⟩
  · exact hf.deps kn hfr
  · exact (hl x hx).deps kn hxr
  · exact hf.defns c bb hbo hfr
  · exact (hl x hx).defns c bb hbo hxr
  · exact hf.axioms c hbo hco hnc hfr
  · exact (hl x hx).axioms c hbo hco hnc hxr
  · exact hf.blocks hi hfr
  · exact (hl x hx).blocks hi hxr
  · exact hf.elims hsh hinf hco hfr
  · exact (hl x hx).elims hsh hinf hco hxr

/-! ## An eliminator spine one minor short -/

/-- **A source eliminator spine below its arity heads no value.** `deltaC` is blocked by
`hnone`, `ctorVal` and `indVal` by `hco` through `Origin.lean`, `iota` by `hagree` against
that arm's own `hsh` and `hinf`, and `beta` by the induction on the spine length. The
head's `casesOn`-ness is not a premise: the consumer holds `bo c = none` and the agreement
of any *relevant* `CasesOnShape` at `c` with the target entry's numbers, which is what
`ErasesEnv.runtimeKey_isCasesOn`, `ErasesEnv.elims` and `ElimDecl.uniq` give it. Relevance
is `hagree`'s second hypothesis because `elims` has it among its own. This is what the β
arm's `elimApp` reading at an empty `extra` is refuted by. -/
theorem SEval.no_elimSpine_value {env : VEnv} {bo : Name → Option Expr} {Us : List Name}
    {fl : SEvalFlags} {Δ : VLCtx} {c : Name} {us : List Level} {dp nm : Nat}
    {args : List Expr} {w : Expr}
    (A : UpstreamAsks env) (hco : ConstOrigin env c) (hnone : bo c = none)
    (hagree : ∀ I dp' nm', CasesOnShape env c I dp' nm' → InformativeInd env I →
      dp' = dp ∧ nm' = nm)
    (hlt : args.length < dp + 1 + nm) :
    ¬ SEval env bo Us fl Δ (mkApps (.const c us) args) w := by
  suffices h : ∀ (m : Nat) (e w' : Expr), SEval env bo Us fl Δ e w' →
      ∀ (us' : List Level) (args' : List Expr), args'.length = m →
        args'.length < dp + 1 + nm → e = mkApps (.const c us') args' → False from
    fun hev => h _ _ _ hev us args rfl hlt rfl
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro e w' hev us' args' hlen hlt' he
    cases hev with
    | lam _ _ _ _ => rcases eq_mkApps_const_elim he with h | ⟨_, _, h⟩ <;> simp at h
    | zeta _ _ _ => rcases eq_mkApps_const_elim he with h | ⟨_, _, h⟩ <;> simp at h
    | sort => rcases eq_mkApps_const_elim he with h | ⟨_, _, h⟩ <;> simp at h
    | forallE => rcases eq_mkApps_const_elim he with h | ⟨_, _, h⟩ <;> simp at h
    | proj _ _ _ _ _ => rcases eq_mkApps_const_elim he with h | ⟨_, _, h⟩ <;> simp at h
    | lit _ _ => rcases eq_mkApps_const_elim he with h | ⟨_, _, h⟩ <;> simp at h
    | beta _ hf _ _ =>
        rcases List.eq_nil_or_concat args' with rfl | ⟨init, last, rfl⟩
        · simp [mkApps] at he
        · rw [List.concat_eq_append, mkApps_concat] at he
          injection he with h1 _
          refine ih init.length ?_ _ _ hf us' init rfl ?_ h1
          · simp [List.concat_eq_append] at hlen; omega
          · simp [List.concat_eq_append] at hlt' ⊢; omega
    | deltaC _ hb _ _ _ _ _ _ =>
        obtain ⟨rfl, -, -⟩ := mkApps_const_inj _ rfl he
        exact absurd (hnone.symm.trans hb) (by simp)
    | ctorVal hc _ _ _ _ =>
        obtain ⟨rfl, -, -⟩ := mkApps_const_inj _ rfl he
        exact constOrigin_not_ctorOf A hco _ _ hc
    | indVal hi _ _ =>
        obtain ⟨rfl, -, -⟩ := mkApps_const_inj _ rfl he
        exact constOrigin_not_indInfo A hco _ _ _ hi
    | @iota con I' ctor us₀ cus pre prev minors minorsv extra extrav cargs disc r np cidx
        nfs _ hsh' _ _ _ hinf' _ _ _ _ _ _ _ _ _ _ =>
        obtain ⟨rfl, -, hargs⟩ := mkApps_const_inj _ rfl he
        obtain ⟨hdp, hnm⟩ := hagree _ _ _ hsh' hinf'
        rw [← hargs] at hlt'
        simp only [List.length_append, List.length_cons] at hlt'
        omega

/-! ## The `□` arms at the composite

Each arm of the simulation meets the box rule first, and must answer with a *lowered*
image of the value. The two lemmas above give the erasure; these two carry it across the
pass, which is where `Lower.source_box` and the spine inversion are spent.
-/

/-- **The box arm at the composite.** Both sides box, and `□` lowers only to `□`. -/
theorem erases_correct_boxLow {env : VEnv} (henv : env.WF) {Us : List Name}
    {bo : Name → Option Expr} {lp : Name → List Name} {fl : SEvalFlags}
    {Γspec Γ : GlobalDeclarations}
    {e v : Expr} {ve : VExpr} {t₀ t : LBTerm}
    (htr : TrExprS env Us [] e ve) (hbox : ErasesBox env Us [] e t₀)
    (hlow : Lower Γspec t₀ t) (hspec : ErasesEnv env bo lp Γspec t₀)
    (hev : SEval env bo Us fl [] e v) :
    ∃ v₀ v', Erases env Us [] v v₀ ∧ Lower Γspec v₀ v' ∧ WcbvEval Γ eraseFlags t v' ∧
      ErasesEnv env bo lp Γspec v₀ := by
  obtain ⟨hb, rfl⟩ := hbox
  have ht : t = .box := Lower.source_box hlow rfl
  obtain ⟨v', her, hEv⟩ := erases_correct_box (Γ := Γ) (Δ := []) henv trivial htr hb hev
  obtain rfl : v' = .box := eval_deterministic hEv .box
  exact ⟨.box, .box, her, .box, by rw [ht]; exact .box, hspec.box⟩

/-- **The box arm at a composite spine.** A boxed proper prefix boxes the whole spine; the
target folds by `eval_box`, whose discarded arguments evaluate because the induction
hypotheses at them do. -/
theorem erases_correct_boxSpineLow {env : VEnv} (henv : env.WF) {Us : List Name}
    {bo : Name → Option Expr} {lp : Name → List Name} {fl : SEvalFlags}
    {Γspec Γ : GlobalDeclarations}
    {hd : Expr} {pre suf : List Expr} {ts : List LBTerm}
    {ve : VExpr} {v : Expr} {t : LBTerm}
    (htr : TrExprS env Us [] (mkApps hd (pre ++ suf)) ve)
    (hbox : ∃ we, TrExprS env Us [] (mkApps hd pre) we ∧
      Erasable env Us.length (VLCtx.toCtx []) we)
    (hlow : Lower Γspec (LBTerm.mkApps .box ts) t)
    (hspec : ErasesEnv env bo lp Γspec (LBTerm.mkApps .box ts))
    (hargs : ∀ s ∈ ts, ∀ u, Lower Γspec s u → ∃ x, WcbvEval Γ eraseFlags u x)
    (hev : SEval env bo Us fl [] (mkApps hd (pre ++ suf)) v) :
    ∃ v₀ v', Erases env Us [] v v₀ ∧ Lower Γspec v₀ v' ∧ WcbvEval Γ eraseFlags t v' ∧
      ErasesEnv env bo lp Γspec v₀ := by
  obtain ⟨hd', ts', rfl, hhd, hlen', hpt⟩ :=
    Lower.source_mkApps (fun _ _ => LBTerm.noConfusion) (fun _ => LBTerm.noConfusion)
      ts hlow
  obtain rfl : hd' = .box := Lower.source_box hhd rfl
  have hev' : ∀ s ∈ ts', ∃ x, WcbvEval Γ eraseFlags s x := by
    intro s hsm
    obtain ⟨i, hi, rfl⟩ := Lower.mem_getElem! hsm
    exact hargs _ (Lower.getElem!_mem (by omega)) _ (hpt i (by omega))
  obtain ⟨v', her, hEv⟩ :=
    erases_correct_boxSpine (Γ := Γ) (Δ := []) (ts := ts') henv trivial htr hbox hev' hev
  obtain rfl : v' = .box := eval_deterministic hEv (WcbvEval.mkApps_box ts' hev' .box)
  exact ⟨.box, .box, her, .box, WcbvEval.mkApps_box ts' hev' .box, hspec.box⟩

/-! ## What the target does at a β-redex

The β arm's function value erases to a λ, and a λ has three images: a λ, and — when the
value is a block member's own specification body — that block's `.fix` node or the
η-expansion of it the registration writes. At the second the target unfolds the fix instead
of β-reducing, and the unfolding is a λ again, because `LowerBlock.hfl` says the emitted
definition's body is one; at the third one β precedes that unfolding.
-/

/-- The target reads `X` as a function that β-steps into `c`. -/
def BetaReady (Γ : GlobalDeclarations) (fl : WcbvFlags) (X c : LBTerm) : Prop :=
  ∀ {f a av r : LBTerm}, WcbvEval Γ fl f X → WcbvEval Γ fl a av →
    WcbvEval Γ fl (LBTerm.subst1 av c) r → WcbvEval Γ fl (.app f a) r

/-- Shifting by zero is the identity: the one arm of `shift` that is not a congruence adds
`d` to an index. Spent where a β step substitutes into `LBTerm.etaFix`'s `.bvar 0`. -/
theorem LBTerm.shift_zero : ∀ (t : LBTerm) (c : Nat), LBTerm.shift 0 c t = t := by
  intro t
  induction t using LBTerm.recData with
  | hbox | hfvar | hconst | hprim => exact fun _ => rfl
  | hbvar i => intro c; simp only [LBTerm.shift]; split <;> simp
  | hlam n b ih => intro c; simp only [LBTerm.shift, ih]
  | hletIn n v b ihv ihb => intro c; simp only [LBTerm.shift, ihv, ihb]
  | happ f a ihf iha => intro c; simp only [LBTerm.shift, ihf, iha]
  | hconstruct iid k args ih =>
      intro c
      simp only [LBTerm.shift, LBTerm.shiftArgs_eq_map]
      rw [List.map_congr_left (fun x hx => ih x hx c), List.map_id_fun', id_eq]
  | hcase info discr alts ihd iha =>
      intro c
      simp only [LBTerm.shift, ihd, LBTerm.shiftAlts_eq_map]
      rw [List.map_congr_left (fun a ha => ?_), List.map_id_fun', id_eq]
      rw [iha a ha (c + a.1.length)]
  | hproj p e ih => intro c; simp only [LBTerm.shift, ih]
  | hfix defs i ih =>
      intro c
      simp only [LBTerm.shift]
      congr 1
      have key : ∀ (l : List (@FixDef LBTerm)),
          (∀ x ∈ l, LBTerm.shift 0 (c + defs.length) x.body = x.body) →
          LBTerm.shiftDefs 0 (c + defs.length) l = l := by
        intro l hshl
        induction l with
        | nil => rfl
        | cons fd rest ihr =>
            simp only [LBTerm.shiftDefs, hshl fd (List.mem_cons_self ..),
              ihr (fun x hx => hshl x (List.mem_cons_of_mem _ hx))]
      exact key defs (fun x hx => ih x hx _)

/-- `substFix` leaves a term carrying none of the block's own identifiers alone. -/
theorem substFix_eq_self {ids : List FVarId} {defs : List (@FixDef LBTerm)} {t : LBTerm}
    (h : ∀ x ∈ ids, ¬ hasFVar x t) : substFix ids defs t = t :=
  substFVarList_eq_self_of_not_hasFVar _ t (fun p hp => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact h q.1 (List.fst_mem_of_mem_zipIdx hq))

/-- The η-wrapper's body under the β substitution: the block's node is closed, so only the
`.bvar 0` moves, and it becomes the argument. -/
theorem subst1_app_fix_bvar {defs : List (@FixDef LBTerm)} {j : Nat} (av : LBTerm)
    (hcl : LBClosed (LBTerm.fix defs j) 0) :
    LBTerm.subst1 av (.app (.fix defs j) (.bvar 0)) = .app (.fix defs j) av := by
  show LBTerm.app (LBTerm.subst av 0 (.fix defs j)) (LBTerm.subst av 0 (.bvar 0)) = _
  rw [hcl.subst_eq (Nat.le_refl 0) av]
  congr 1
  simp [LBTerm.subst, LBTerm.shift_zero]

/-- **The β transport at a block's `.fix` node.** The fix fires at `principalArgIdx = 0`
(`LowerBlock.hrarg`) and the unfolded body — a λ, by `LowerBlock.hfl` — carries the
transport on. -/
theorem betaReady_fix {Γspec Γ : GlobalDeclarations} {fl : WcbvFlags}
    (hg : fl.with_guarded_fix = true) {kns : List Kername} {bs bs' : List LBTerm}
    {ids : List FVarId} {defs : List (@FixDef LBTerm)} {j : Nat} {c : LBTerm}
    (hblock : LowerBlock Γspec kns bs bs' ids defs) (hjl : j < defs.length)
    (h : BetaReady Γ fl (LBTerm.substList (LBTerm.fixSubst defs) (defs[j]!).body) c) :
    BetaReady Γ fl (.fix defs j) c := by
  intro f a av r hf ha hr
  obtain ⟨n₁, b₁, he⟩ :=
    isLambda_eq_true (isLambda_substList (LBTerm.fixSubst defs) (hblock.hfl j hjl))
  refine .fix_guarded (argsv := []) hg hf ha (getElem?_getElem! hjl)
    (hblock.hrarg _ (Lower.getElem!_mem hjl)) ?_
  rw [LBTerm.mkApps_nil]
  exact h (by rw [he]; exact .lam n₁ b₁) (value_final (eval_to_value ha)) hr

/-- **The β transport at the η-expanded node.** One `WcbvEval.beta` in front of the node's
own transport: the wrapper's body substitutes to `(fix defs j) av`, the block's node being
closed. This is the shape `Erasure.visitMutual` registers (F-ETA). -/
theorem betaReady_etaFix {Γspec Γ : GlobalDeclarations} (hΓ : ClosedBodies Γspec)
    {fl : WcbvFlags} {kns : List Kername} {bs bs' : List LBTerm} {ids : List FVarId}
    {defs : List (@FixDef LBTerm)} {j : Nat} {c : LBTerm} {n : BinderName}
    (hblock : LowerBlock Γspec kns bs bs' ids defs)
    (h : BetaReady Γ fl (.fix defs j) c) :
    BetaReady Γ fl (.lambda n (.app (.fix defs j) (.bvar 0))) c := by
  intro f a av r hf ha hr
  refine .beta hf ha ?_
  rw [subst1_app_fix_bvar av (hblock.lbClosed_fix hΓ j)]
  exact h (.fix_atom defs j) (value_final (eval_to_value ha)) hr

/-- **The block arms' common step.** A member's own transport, read under the block closure,
is the transport at the block's node: `LowerBlock.substList_fixSubst` identifies the dynamic
unfolding with `substFix`, and `betaReady_fix` supplies the step. -/
theorem Lower.betaReady_of_block {Γspec Γ : GlobalDeclarations} (hΓ : ClosedBodies Γspec)
    {fl : WcbvFlags} (hg : fl.with_guarded_fix = true) {kns : List Kername}
    {bs bs' : List LBTerm} {ids : List FVarId} {defs : List (@FixDef LBTerm)} {j : Nat}
    {b₀ : LBTerm} (hblock : LowerBlock Γspec kns bs bs' ids defs) (hjl : j < defs.length)
    (hmem : ∀ t' : LBTerm, ConstToFVar kns ids bs'[j]! t' →
      ∃ c, Lower Γspec b₀ c ∧ BetaReady Γ fl (substFix ids defs t') c) :
    ∃ c, Lower Γspec b₀ c ∧ BetaReady Γ fl (.fix defs j) c := by
  have hjk : j < kns.length := by rw [← hblock.hd]; exact hjl
  obtain ⟨u, hct, heq⟩ := hblock.hcl j hjk
  obtain ⟨c, hc, hbr⟩ := hmem u hct
  refine ⟨c, hc, betaReady_fix hg hblock hjl ?_⟩
  have hbcl : LBClosed bs'[j]! 0 :=
    Lower.closed hΓ (hblock.hlow j hjk) 0 (hΓ _ _ (hblock.hdecl j hjk))
  rwa [heq, hblock.substList_fixSubst hΓ (hct.closed hbcl)]

/-- **The β transport, with the block closure carried.** A λ's image is β-ready at an image
of the λ's body: at `lambda` outright, at `fixBody` and `fixEta` through the block's own
unfolding, which `LowerBlock.hfl` makes a λ again.

The second conjunct is the same statement read under a block closure — `Lower.constToFix`'s
transport — and it is what the two block arms spend at the member's own `hlow`. It is not
replaceable by inverting the transported derivation body to body: the `fixEta` arm makes
that inversion false, since `Lower Γ (.lambda nm (.bvar 0)) (LBTerm.etaFix defs j)` is
derivable while `Lower Γ (.bvar 0) (.app (.fix defs j) (.bvar 0))` is refuted by
`Lower.source_bvar`. The recursion therefore runs on the derivation, where the block a
wrapper names is reached through the member's own `hlow`. -/
theorem Lower.appReady_aux {Γspec Γ : GlobalDeclarations} (hΓ : ClosedBodies Γspec)
    {fl : WcbvFlags} (hg : fl.with_guarded_fix = true) :
    ∀ {s t : LBTerm}, Lower Γspec s t →
      ∀ (nm : BinderName) (b₀ : LBTerm), s = .lambda nm b₀ →
        (∃ c, Lower Γspec b₀ c ∧ BetaReady Γ fl t c) ∧
        (∀ (kns : List Kername) (bs bs' : List LBTerm) (ids : List FVarId)
            (defs : List (@FixDef LBTerm)), LowerBlock Γspec kns bs bs' ids defs →
          (∀ x ∈ ids, ¬ hasFVar x t) → ∀ t' : LBTerm, ConstToFVar kns ids t t' →
          ∃ c, Lower Γspec b₀ c ∧ BetaReady Γ fl (substFix ids defs t') c) := by
  intro s t h
  induction h using Lower.rec (motive_2 := fun _ _ _ _ => True) with
  | box | bvar | fvar | prim | const | letIn | app | proj | construct | «case» | fixConst =>
      exact fun _ _ hs => LBTerm.noConfusion hs
  | @elimApp kn iid np dp nfs pre disc disc' minors alts extra extra' =>
      intro nm b₀ hs
      obtain ⟨g, b, he⟩ := mkApps_ne_nil_is_app (f := LBTerm.const kn)
        (args := pre ++ disc :: minors ++ extra) (by cases pre <;> simp)
      rw [he] at hs; exact LBTerm.noConfusion hs
  | @lambda n₀ n' b₁ b' hb _ =>
      intro nm b₀ hs
      injection hs with _ hbb
      subst hbb
      refine ⟨⟨b', hb, fun hf ha hr => .beta hf ha hr⟩, ?_⟩
      intro kns bs bs' ids defs hblk hfv t' hct
      cases hct with
      | @lambda _ n₂ _ b'' hb'' =>
          refine ⟨substFix ids defs b'', ?_, ?_⟩
          · exact Lower.constToFix hΓ hblk
              (fun x hx hc => hfv x hx (by simpa only [hasFVar_lambda] using hc)) hb hb''
          · rw [substFix_lambda]
            exact fun hf ha hr => .beta hf ha hr
  | @fixBody b kns bs bs' ids defs j hb hb' hd hnd hids hilen hfresh hrarg hdecl hfl hlow
      hcl hj hjl ih =>
      intro nm b₀ hs
      have hblock : LowerBlock Γspec kns bs bs' ids defs :=
        ⟨hb, hb', hd, hnd, hids, hilen, hfresh, hrarg, hdecl, hfl, hlow, hcl⟩
      have hjk : j < kns.length := by rw [← hd]; exact hjl
      obtain ⟨-, hbsj⟩ := Lower.getElem!_of_getElem? hj
      have hmain := Lower.betaReady_of_block hΓ hg hblock hjl (fun t' hct' =>
        (ih j hjk nm b₀ (hbsj.trans hs)).2 kns bs bs' ids defs hblock
          (fun x hx => hfresh x hx j hjk) t' hct')
      refine ⟨hmain, ?_⟩
      intro kns₂ bs₂ bs₂' ids₂ defs₂ _ hfv t' hct'
      cases hct'
      rw [substFix_eq_self hfv]
      exact hmain
  | @fixEta b nm₀ kns bs bs' ids defs j hb hb' hd hnd hids hilen hfresh hrarg hdecl hfl hlow
      hcl hj hjl ih =>
      intro nm b₀ hs
      have hblock : LowerBlock Γspec kns bs bs' ids defs :=
        ⟨hb, hb', hd, hnd, hids, hilen, hfresh, hrarg, hdecl, hfl, hlow, hcl⟩
      have hjk : j < kns.length := by rw [← hd]; exact hjl
      obtain ⟨-, hbsj⟩ := Lower.getElem!_of_getElem? hj
      have hnode := Lower.betaReady_of_block hΓ hg hblock hjl (fun t' hct' =>
        (ih j hjk nm b₀ (hbsj.trans hs)).2 kns bs bs' ids defs hblock
          (fun x hx => hfresh x hx j hjk) t' hct')
      obtain ⟨c, hc, hbr⟩ := hnode
      refine ⟨⟨c, hc, betaReady_etaFix hΓ hblock hbr⟩, ?_⟩
      intro kns₂ bs₂ bs₂' ids₂ defs₂ _ hfv t' hct'
      cases hct' with
      | @lambda _ n₂ _ w hlam =>
          cases hlam with
          | @app _ f' _ a' hf' ha' =>
              cases hf'
              cases ha'
              refine ⟨c, hc, ?_⟩
              rw [substFix_eq_self (fun x hx hcc => hfv x hx (by
                simpa only [hasFVar_lambda, hasFVar_app, hasFVar_bvar, or_false] using hcc))]
              exact betaReady_etaFix hΓ hblock hbr
  | done | lam => exact trivial

/-- **The β transport.** `Lower.appReady_aux`'s first conjunct: what the β and δ arms of the
simulation spend at a lowered λ. -/
theorem Lower.appReady {Γspec Γ : GlobalDeclarations} (hΓ : ClosedBodies Γspec)
    {fl : WcbvFlags} (hg : fl.with_guarded_fix = true) {nm : BinderName} {b₀ : LBTerm}
    {s t : LBTerm} (h : Lower Γspec s t) (hs : s = .lambda nm b₀) :
    ∃ c, Lower Γspec b₀ c ∧ BetaReady Γ fl t c :=
  (Lower.appReady_aux hΓ hg h nm b₀ hs).1

/-! ## The emitted arity of a reached block

`ErasesEnv.blocks` is the forward reading at an inductive block: at the block kername a
`.construct` node already reaches, the entry is that block's own declaration. Composed with
`LowerEnv.inds` it is the emitted constructor arity the `ctorVal` arm builds its value at.
-/

/-- `getElem!` through a `List.map` read off the mapped list. -/
theorem getElem!_of_map_eq {α β : Type} [Inhabited α] [Inhabited β] {f : α → β}
    {l : List α} {m : List β} (h : l.map f = m) {k : Nat} (hk : k < m.length) :
    ∃ x, l[k]? = some x ∧ f x = m[k]! := by
  subst h
  have hlen : k < l.length := by simpa using hk
  refine ⟨l[k]'hlen, List.getElem?_eq_getElem hlen, ?_⟩
  rw [getElem!_pos (l.map f) k (by simpa using hlen), List.getElem_map]

/-- **The emitted constructor arity of a reached block.** `ErasesEnv.blocks` plus
`LowerEnv.inds` put `IndBodyOf`'s numbers where `WcbvEval.construct_atom` and
`construct_app` read them. -/
theorem ErasesEnv.ctorArity {env : VEnv} {bo : Name → Option Expr} {lp : Name → List Name}
    {Γspec Γ : GlobalDeclarations} {t : LBTerm} (hspec : ErasesEnv env bo lp Γspec t)
    (henvL : LowerEnv Γspec Γ) {I : Name} {iid : InductiveId} {np k : Nat} {nfs : List Nat}
    (hi : IndInfo env I iid np nfs)
    (hr : ReachableFrom Γspec t iid.mutualBlockName) (hk : k < nfs.length) :
    constructorArity Γ iid k = some (np + nfs[k]!) := by
  obtain ⟨-, mib, hspecl, ⟨hnp, oib, hoib, hctors⟩, -⟩ := hspec.blocks hi hr
  obtain ⟨cb, hcb, hnargs⟩ := getElem!_of_map_eq hctors hk
  simp only [constructorArity, henvL.inds _ _ hspecl, hoib, hcb, Option.map_some, hnp,
    hnargs]

/-- A kername the term names is reachable from it. -/
theorem reachableFrom_of_mem_constRefs {Γ : GlobalDeclarations} {t : LBTerm} {kn : Kername}
    (h : kn ∈ constRefs t) : ReachableFrom Γ t kn :=
  kernameElem_iff.2 (subset_reachFrom _ h)

/-- **A constructor spine within its arity evaluates argument by argument.**
`construct_atom` starts it and `construct_app` accumulates, which is the applied form the
erasure emits. -/
theorem wcbvEval_mkApps_construct {Γ : GlobalDeclarations} {iid : InductiveId} {k ar : Nat}
    (har : constructorArity Γ iid k = some ar) :
    ∀ (ts vs : List LBTerm), ts.length ≤ ar → vs.length = ts.length →
      (∀ i, i < ts.length → WcbvEval Γ eraseFlags ts[i]! vs[i]!) →
      WcbvEval Γ eraseFlags (LBTerm.mkApps (.construct iid k []) ts)
        (LBTerm.mkApps (.construct iid k []) vs) := by
  suffices h : ∀ (n : Nat) (ts vs : List LBTerm), ts.length = n → ts.length ≤ ar →
      vs.length = ts.length → (∀ i, i < ts.length → WcbvEval Γ eraseFlags ts[i]! vs[i]!) →
      WcbvEval Γ eraseFlags (LBTerm.mkApps (.construct iid k []) ts)
        (LBTerm.mkApps (.construct iid k []) vs) from
    fun ts vs h1 h2 h3 => h ts.length ts vs rfl h1 h2 h3
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro ts vs hn hle hvlen hall
    rcases List.eq_nil_or_concat ts with rfl | ⟨init, last, rfl⟩
    · obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero (by simpa using hvlen)
      exact .construct_atom rfl har
    · rw [List.concat_eq_append] at hn hle hvlen hall ⊢
      obtain ⟨vinit, vlast, rfl, hvil, hvpt, hvl⟩ := unconcat_index hvlen hall
      rw [LBTerm.mkApps_concat, LBTerm.mkApps_concat]
      refine .construct_app rfl ?_ har ?_ hvl
      · exact ih init.length (by simp at hn; omega) init vinit rfl
          (by simp at hle; omega) hvil hvpt
      · simp at hle; rw [hvil]; omega

/-- A constructor's index is within its type's field-count list. -/
theorem CtorOf.lt_nfs {env : VEnv} (A : UpstreamAsks env) {c I : Name} {k : Nat}
    {iid : InductiveId} {np : Nat} {nfs : List Nat} (hc : CtorOf env c I k)
    (hi : IndInfo env I iid np nfs) : k < nfs.length := by
  obtain ⟨ds, env₀, decl, t, ctor, hds, hd, hle, hmem, hname, hk, hcn⟩ := hc
  obtain ⟨idx, hidx⟩ : ∃ idx : Nat, decl.types[idx]? = some t := List.getElem?_of_mem hmem
  have hi' : IndInfo env I ⟨indBlockKername (decl.types.map (·.name)), idx⟩ decl.nparams
      (ctorFieldCounts decl.nparams t) :=
    ⟨ds, env₀, decl, t, hds, hd, hle, hidx, hname, rfl, rfl, rfl⟩
  obtain ⟨-, -, rfl⟩ := IndInfo.inj A hi hi'
  rw [ctorFieldCounts, List.length_map]
  by_contra hno
  rw [List.getElem?_eq_none (by omega)] at hk
  simp at hk

/-! ## An eliminator spine below its arity is the erasure of nothing with a value

The β arm's second `Lower` reading makes the source's function a saturated eliminator
spine one minor short. What refutes it is the source rule's own premise: no `SEval` arm
applies to such a spine. Reaching `SEval.no_elimSpine_value` from the *erasure* takes three
steps, all of them here.

First, no erasure image is an eliminator body — `Erases` emits neither a `.case` node nor a
`.fix`, and the two `ElimBody` shapes carry one each. Second, that plus `ErasesEnv.defns`
and `ErasesEnv.axioms` says a reached key carrying an eliminator's declaration belongs to a
`casesOn` constant with no compiler body. That is a theorem and not a clause of
`ErasesEnv`: as a clause it would be false, because `RuntimeKey` tests the entry's body
shape and never the key's name, so an ordinary constant with an `mkElimBody`-shaped
specification body refutes it. Third, a source term whose erasure is a constant spine and
which has a value *is* a constant spine at that kername, `lit` unfolded and `β`
re-associated.
-/

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

/-- **A runtime key belongs to a `casesOn` constant.** A reached key carrying an
eliminator's declaration belongs to no tabled constant — its entry would be an erasure
image, and no erasure image is an `ElimBody` — and to no body-less non-eliminator, whose
entry `axioms` pins to `⟨none⟩`. So the constant behind it is a `casesOn` name with no
compiler body. -/
theorem ErasesEnv.runtimeKey_isCasesOn {env : VEnv} {bo : Name → Option Expr}
    {lp : Name → List Name} {Γspec : GlobalDeclarations} {t : LBTerm} {c : Name}
    (h : ErasesEnv env bo lp Γspec t) (hco : ConstOrigin env c)
    (hr : ReachableFrom Γspec t (toKername c)) (hrk : RuntimeKey Γspec (toKername c)) :
    isCasesOnName c = true ∧ bo c = none := by
  obtain ⟨iid, np, dp, nfs, ⟨body, hlook, helim⟩, -⟩ := hrk
  by_cases hb : ∃ b, bo c = some b
  · obtain ⟨b, hb⟩ := hb
    obtain ⟨-, b₀, -, hlook', her, -⟩ := h.defns c b hb hr
    rw [hlook] at hlook'
    cases hlook'
    exact absurd (erases_ne_elimBody her (iid := iid) (np := np) (dp := dp)
      (nfs := nfs)) (by simpa using helim)
  · have hnone : bo c = none := by
      cases hbo : bo c with
      | none => rfl
      | some b => exact absurd ⟨b, hbo⟩ hb
    refine ⟨?_, hnone⟩
    by_cases hcas : isCasesOnName c = true
    · exact hcas
    · have := h.axioms c hnone hco (by simpa using hcas) hr
      rw [hlook] at this
      exact absurd this (by simp)

/-- A constant spine is no node of another shape: its spine head is the constant. -/
theorem not_mkApps_const {kn : Kername} {args : List LBTerm} {u : LBTerm}
    (hu : ∀ x y, u ≠ .app x y) (hc : ∀ k, u ≠ .const k)
    (h : LBTerm.mkApps (.const kn) args = u) : False := by
  obtain ⟨h1, -⟩ :=
    mkApps_head_inj (ts := args) (us := []) (fun _ _ => LBTerm.noConfusion) hu h
  exact hc kn h1.symm

/-- **A source spine whose erasure is a constant spine.** The head erases by the `const`
rule — `box` and `ctor` produce a node of another shape — so the kername is the source
head's and the two spines have the same length. -/
theorem erases_constSpine_head {env : VEnv} {Us : List Name} {Δ : VLCtx} {c : Name}
    {us : List Level} {as : List Expr} {kn : Kername} {args : List LBTerm}
    (her : Erases env Us Δ (mkApps (.const c us) as) (LBTerm.mkApps (.const kn) args)) :
    toKername c = kn ∧ ConstOrigin env c ∧ as.length = args.length := by
  rcases erases_mkApps_inv as her with ⟨th, ts, hth, hts, heq⟩ | ⟨_, _, ts, -, -, -, heq⟩
  · rcases Erases.const_inv hth with ⟨-, rfl⟩ | ⟨I, iid, k, np, nfs, -, -, rfl⟩ | ⟨-, ho, rfl⟩
    · obtain ⟨h1, -⟩ := mkApps_head_inj (fun _ _ => LBTerm.noConfusion)
        (fun _ _ => LBTerm.noConfusion) heq
      exact absurd h1 (by simp)
    · obtain ⟨h1, -⟩ := mkApps_head_inj (fun _ _ => LBTerm.noConfusion)
        (fun _ _ => LBTerm.noConfusion) heq
      exact absurd h1 (by simp)
    · obtain ⟨h1, h2⟩ := mkApps_head_inj (fun _ _ => LBTerm.noConfusion)
        (fun _ _ => LBTerm.noConfusion) heq
      injection h1 with h1
      exact ⟨h1.symm, ho, by rw [h2]; exact hts.length_eq⟩
  · obtain ⟨h1, -⟩ := mkApps_head_inj (fun _ _ => LBTerm.noConfusion)
      (fun _ _ => LBTerm.noConfusion) heq
    exact absurd h1 (by simp)

/-- **A source term whose erasure is a constant spine and which has a value is itself a
spine at that constant.** Induction on the evaluation: `lit` unfolds to its constructor
form, `beta` re-associates the head's spine with one more argument, the four spine arms are
already at the shape, and every other arm's source erases to a node of another shape. The
spine is at most as long as the target's, which is all `SEval.no_elimSpine_value`
reads. -/
theorem erases_constSpine_value {env : VEnv} {bo : Name → Option Expr} {Us : List Name}
    {fl : SEvalFlags} {Δ : VLCtx} {e w : Expr} (hev : SEval env bo Us fl Δ e w) :
    ∀ (kn : Kername) (args : List LBTerm),
      Erases env Us Δ e (LBTerm.mkApps (.const kn) args) →
      ∃ (c : Name) (us : List Level) (as : List Expr),
        toKername c = kn ∧ ConstOrigin env c ∧ as.length ≤ args.length ∧
          SEval env bo Us fl Δ (mkApps (.const c us) as) w := by
  induction hev with
  | @lam n ty b bi =>
      intro kn args her
      rcases Erases.lam_inv her with ⟨-, heq⟩ | ⟨_, ty', b', -, -, heq⟩ <;>
        exact (not_mkApps_const (fun _ _ => LBTerm.noConfusion)
          (fun _ => LBTerm.noConfusion) heq).elim
  | @beta f a n ty bd bi av r hfl hf ha hb ihf _ _ =>
      intro kn args her
      rcases Erases.app_inv her with ⟨-, heq⟩ | ⟨f', a', hf', ha', heq⟩
      · exact (not_mkApps_const (fun _ _ => LBTerm.noConfusion)
          (fun _ => LBTerm.noConfusion) heq).elim
      · rcases List.eq_nil_or_concat args with rfl | ⟨init, last, rfl⟩
        · rw [LBTerm.mkApps_nil] at heq; exact LBTerm.noConfusion heq
        · rw [List.concat_eq_append, LBTerm.mkApps_concat] at heq
          injection heq with hfe hae
          subst hfe
          obtain ⟨c, us, as, hkn, hco, hle, hsev⟩ := ihf kn init hf'
          refine ⟨c, us, as ++ [a], hkn, hco, by simp; omega, ?_⟩
          rw [mkApps_concat]
          exact .beta hfl hsev ha hb
  | @zeta n ty v b nd vv r hfl hv hbd _ _ =>
      intro kn args her
      rcases Erases.letE_inv her with ⟨-, heq⟩ | ⟨_, ty', val', v', b', -, -, -, -, heq⟩ <;>
        exact (not_mkApps_const (fun _ _ => LBTerm.noConfusion)
          (fun _ => LBTerm.noConfusion) heq).elim
  | @deltaC c us ups args argsv b b' v hfl hbd hnd hinst hlen hargs hdef hcont _ _ =>
      intro kn targs her
      obtain ⟨hkn, hco, hlen'⟩ := erases_constSpine_head her
      exact ⟨c, us, args, hkn, hco, Nat.le_of_eq hlen',
        .deltaC hfl hbd hnd hinst hlen hargs hdef hcont⟩
  | @ctorVal cn I us iid k np nfs args argsv hc hi harity hlen hargs _ =>
      intro kn targs her
      obtain ⟨hkn, hco, hlen'⟩ := erases_constSpine_head her
      exact ⟨cn, us, args, hkn, hco, Nat.le_of_eq hlen', .ctorVal hc hi harity hlen hargs⟩
  | @indVal cn us iid np nfs args argsv hi hlen hargs _ =>
      intro kn targs her
      obtain ⟨hkn, hco, hlen'⟩ := erases_constSpine_head her
      exact ⟨cn, us, args, hkn, hco, Nat.le_of_eq hlen', .indVal hi hlen hargs⟩
  | @sort u =>
      intro kn args her
      obtain ⟨-, heq⟩ := Erases.sort_inv her
      exact (not_mkApps_const (fun _ _ => LBTerm.noConfusion)
        (fun _ => LBTerm.noConfusion) heq).elim
  | @forallE n ty b bi =>
      intro kn args her
      obtain ⟨-, heq⟩ := Erases.forallE_inv her
      exact (not_mkApps_const (fun _ _ => LBTerm.noConfusion)
        (fun _ => LBTerm.noConfusion) heq).elim
  | @iota con I ctor us cus pre prev minors minorsv extra extrav cargs disc r np cidx
      nfs hfl hsh ho hct hnp hinf hpre hpres hdiscr hmin hmins hxlen hxs hidx hdef hcont
      _ _ _ _ _ =>
      intro kn targs her
      obtain ⟨hkn, hco, hlen'⟩ := erases_constSpine_head her
      exact ⟨con, us, pre ++ disc :: minors ++ extra, hkn, hco, Nat.le_of_eq hlen',
        .iota hfl hsh ho hct hnp hinf hpre hpres hdiscr hmin hmins hxlen hxs hidx hdef
          hcont⟩
  | @proj S ctor i discr cus cargs np nf cidx r hfl hct hnp hdiscr hlt hdef hcont _ _ =>
      intro kn args her
      rcases Erases.proj_inv her with ⟨-, heq⟩ | ⟨iid, npp, nf', d, -, -, -, -, heq⟩ <;>
        exact (not_mkApps_const (fun _ _ => LBTerm.noConfusion)
          (fun _ => LBTerm.noConfusion) heq).elim
  | @lit l r hfl hr ih =>
      intro kn args her
      rcases Erases.lit_inv her with ⟨-, heq⟩ | ⟨hcl, her'⟩
      · exact (not_mkApps_const (fun _ _ => LBTerm.noConfusion)
          (fun _ => LBTerm.noConfusion) heq).elim
      · obtain ⟨c, us, as, hkn, hco, hle, hsev⟩ := ih kn args her'
        exact ⟨c, us, as, hkn, hco, hle, hsev⟩

/-- **An eliminator spine below its arity is the erasure of no source term with a value.**
The source head is the `casesOn` constant behind the key (`runtimeKey_isCasesOn`), so it
carries no compiler body; `ErasesEnv.elims` at the reached key turns any relevant
`CasesOnShape` at it into an `ElimDecl`, which `ElimDecl.uniq` equates with the entry's own
numbers, and `SEval.no_elimSpine_value` closes it against the under-application bound. -/
theorem erases_elimSpine_no_value {env : VEnv} {bo : Name → Option Expr}
    {lp : Name → List Name} {Us : List Name} {fl : SEvalFlags}
    {Γspec : GlobalDeclarations} (A : UpstreamAsks env)
    {kn : Kername} {iid : InductiveId} {np dp : Nat} {nfs : List Nat}
    {args : List LBTerm} {e w : Expr}
    (hspec : ErasesEnv env bo lp Γspec (LBTerm.mkApps (.const kn) args))
    (hed : ElimDecl Γspec kn iid np dp nfs) (hlt : args.length < dp + 1 + nfs.length)
    (her : Erases env Us [] e (LBTerm.mkApps (.const kn) args)) :
    ¬ SEval env bo Us fl [] e w := by
  intro hev
  obtain ⟨c, us, as, rfl, hco, hle, hsev⟩ := erases_constSpine_value hev kn args her
  have hr : ReachableFrom Γspec (LBTerm.mkApps (.const (toKername c)) args) (toKername c) :=
    ReachableFrom.subterm (subTerm_mkApps_head args .refl)
      (reachableFrom_of_mem_constRefs (by simp [constRefs]))
  obtain ⟨-, hnone⟩ := hspec.runtimeKey_isCasesOn hco hr ⟨iid, np, dp, nfs, hed⟩
  refine SEval.no_elimSpine_value (dp := dp) (nm := nfs.length) A hco hnone
    (fun I dp' nm' hsh hinf => ?_) (by omega) hsev
  obtain ⟨iid', np', nfs', hed', -, hnfs'⟩ := hspec.elims hsh hinf hco hr
  obtain ⟨-, -, rfl, rfl⟩ := ElimDecl.uniq hed' hed
  exact ⟨rfl, hnfs'.symm⟩

/-! ## The level scope of a tabled body

`SEval.deltaC` unfolds a tabled body at a parameter list the rule binds as a *variable*, while
`ErasesEnv.defns` records the erasure at the declaration's own scope. What reconciles the two
is `erases_subst_instance`'s typing premise (`ErasureProperties.v:383`) on both sides: the
rule's own `hdef` translates the instantiated body, and `ErasesEnv.defns`' own last conjunct
translates the uninstantiated one, at the constant the program reaches.
-/

/-- **What the compiler table owes about its level column.** Every tabled body is in the
`max`-free fragment `Erases.instL` transports along, and translates at the level scope the
environment relation records for it — `Σ ;;; [] |- b : T` of `erases_subst_instance_decl`
(`../metarocq/erasure/theories/ErasureProperties.v:412`), which is what pays for the level
arguments `Erases.const` and `Erases.ctor` leave unconstrained. It is stated over the whole
table because a table is where it is checked: `TableSafe.noMaxLevels` gives the first conjunct
and `CompilerBodies` the second. The simulation does not take it — `bridgeEnv_of_regInv` does,
and `ErasesEnv.defns` hands the δ arm only the constants the program reaches, which is where
MetaRocq spends the premise (`ErasureCorrectness.v:176`). -/
def TabledLevels (env : VEnv) (bo : Name → Option Expr) (lp : Name → List Name) : Prop :=
  ∀ c b, bo c = some b → NoMaxLevels b ∧ ∃ vb, TrExprS env (lp c) [] b vb

/-- **`TabledLevels` at a reified table.** The `max`-free half is `TableSafe.noMaxLevels`; the
translation is `CompilerBodies`, read against the table's level column, which
`SourceTableAdequate.levels?_eq` identifies with the declaration's own. This is
`bridgeEnv_of_regInv`'s `hlvl`. -/
theorem tabledLevels_of_table {lenv : Environment} {env : VEnv} {tbl : Witness.SourceTable}
    (htbl : Witness.SourceTableAdequate lenv tbl) (hsafe : TableSafe lenv tbl)
    (hcb : CompilerBodies lenv env tbl.body?) :
    TabledLevels env tbl.body? tbl.levels? := by
  intro c b hbo
  refine ⟨hsafe.noMaxLevels c b hbo, ?_⟩
  obtain ⟨ci, hci, vb, -, htr, -, -⟩ := hcb c b hbo
  have hd : (tbl.decl? c).isSome := by
    cases h : tbl.decl? c with
    | none => simp [Witness.SourceTable.body?, h] at hbo
    | some d => simp
  rw [htbl.levels?_eq hd hci]
  exact ⟨vb, htr⟩

/-- **The δ arm's transport.** The rule's `hdef` carries a translation of the instantiated
spine, whose head is the instantiated body, and that is what rules out an instantiation the
reading scope cannot follow. This is `erases_subst_instance_decl` at the one place MetaRocq
spends it, the constant case of `erases_correct`
(`../metarocq/erasure/theories/ErasureCorrectness.v:176`). -/
theorem Erases.instantiateLevelParams_of_stepDefeq {env : VEnv} {ps Us ups : List Name}
    {c : Name} {us : List Level} {argsv : List Expr} {b b' : Expr} {b₀ : LBTerm} {vb : VExpr}
    (h : Erases env ps [] b b₀) (hnm : NoMaxLevels b) (hb : TrExprS env ps [] b vb)
    (hinst : b' = b.instantiateLevelParams ups us)
    (hdef : StepDefeq env Us [] (_root_.LeanToLambdaBox.mkApps (.const c us) argsv)
      (_root_.LeanToLambdaBox.mkApps b' argsv)) :
    Erases env Us [] b' b₀ := by
  obtain ⟨-, v₂, -, htr₂, -⟩ := hdef
  obtain ⟨w, htrb'⟩ := trExprS_spine_head argsv htr₂
  subst hinst
  exact Erases.instantiateLevelParams_of_trExprS h hnm hb htrb'

/-! ## The motive and the three step interfaces -/

/-- The simulation's claim at one source node: for every composite image of `e` that the
environment relation answers, an image of `v`, a target evaluation reaching it, and the
same environment relation at the image of `v`. The last conjunct is the accumulator the
β, ζ, δ and ι arms take their induction hypothesis at the contractum under. -/
def Simulates (env : VEnv) (bo : Name → Option Expr) (lp : Name → List Name)
    (Us : List Name)
    (Γspec Γ : GlobalDeclarations) (e v : Expr) : Prop :=
  ∀ {ve : VExpr} {t₀ t : LBTerm},
    TrExprS env Us [] e ve → Erases env Us [] e t₀ → Lower Γspec t₀ t →
    ErasesEnv env bo lp Γspec t₀ →
    ∃ v₀ v', Erases env Us [] v v₀ ∧ Lower Γspec v₀ v' ∧ WcbvEval Γ eraseFlags t v' ∧
      ErasesEnv env bo lp Γspec v₀

/-- The ι arm of `SEval`, with the induction hypothesis available at every subderivation.
`UpstreamAsks env` is what `Origin.lean`'s corollaries take while the fork cannot be
edited from here; `hnp` and `hinf` are the rule's own, and are what `CasesOnShape.agree`
and `ErasesEnv.elims` read. -/
abbrev StepIota (env : VEnv) (bo : Name → Option Expr) (lp : Name → List Name)
    (Us : List Name) (fl : SEvalFlags)
    (Γspec Γ : GlobalDeclarations) : Prop :=
  UpstreamAsks env →
  ∀ {con I ctor : Name} {us cus : List Level} {pre prev minors minorsv extra extrav
      cargs : List Expr} {disc r : Expr} {np cidx : Nat} {nfs : List Nat},
    env.WF → LowerEnv Γspec Γ → fl.iota →
    CasesOnShape env con I pre.length minors.length → ConstOrigin env con →
    CtorOf env ctor I cidx → IndArity env I np nfs → InformativeInd env I →
    prev.length = pre.length →
    (∀ i, i < pre.length → SEval env bo Us fl [] pre[i]! prev[i]! ∧
        Simulates env bo lp Us Γspec Γ pre[i]! prev[i]!) →
    SEval env bo Us fl [] disc (mkApps (.const ctor cus) cargs) →
    Simulates env bo lp Us Γspec Γ disc (mkApps (.const ctor cus) cargs) →
    minorsv.length = minors.length →
    (∀ i, i < minors.length → SEval env bo Us fl [] minors[i]! minorsv[i]! ∧
        Simulates env bo lp Us Γspec Γ minors[i]! minorsv[i]!) →
    extrav.length = extra.length →
    (∀ i, i < extra.length → SEval env bo Us fl [] extra[i]! extrav[i]! ∧
        Simulates env bo lp Us Γspec Γ extra[i]! extrav[i]!) →
    cidx < minors.length →
    StepDefeq env Us [] (mkApps (.const con us) (pre ++ disc :: minors ++ extra))
      (mkApps minors[cidx]! (cargs.drop np ++ extra)) →
    SEval env bo Us fl [] (mkApps minors[cidx]! (cargs.drop np ++ extra)) r →
    Simulates env bo lp Us Γspec Γ (mkApps minors[cidx]! (cargs.drop np ++ extra)) r →
    Simulates env bo lp Us Γspec Γ (mkApps (.const con us) (pre ++ disc :: minors ++ extra)) r

/-- The projection arm, with the induction hypothesis at the discriminant and at the
selected field. The rule's own `hct` and `hnp` ride along: they are what classify the
discriminant's value and pin the parameter prefix the two sides skip. -/
abbrev StepProj (env : VEnv) (bo : Name → Option Expr) (lp : Name → List Name)
    (Us : List Name) (fl : SEvalFlags)
    (Γspec Γ : GlobalDeclarations) : Prop :=
  UpstreamAsks env →
  ∀ {S ctor : Name} {i np nf cidx : Nat} {cus : List Level} {disc r : Expr}
      {cargs : List Expr},
    env.WF → LowerEnv Γspec Γ → fl.proj →
    CtorOf env ctor S cidx → IndArity env S np [nf] →
    SEval env bo Us fl [] disc (mkApps (.const ctor cus) cargs) →
    Simulates env bo lp Us Γspec Γ disc (mkApps (.const ctor cus) cargs) →
    np + i < cargs.length →
    StepDefeq env Us [] (.proj S i disc) cargs[np + i]! →
    SEval env bo Us fl [] cargs[np + i]! r →
    Simulates env bo lp Us Γspec Γ cargs[np + i]! r →
    Simulates env bo lp Us Γspec Γ (.proj S i disc) r

/-- The δ arm, at a compiler body, with the induction hypothesis at the arguments and at
the unfolded application. `UpstreamAsks env` is uniform with the other two interfaces: the
constructor reading of the head is refuted by `constOrigin_not_ctorOf` on
`ErasesEnv.tabled`. -/
abbrev StepDelta (env : VEnv) (bo : Name → Option Expr) (lp : Name → List Name)
    (Us : List Name) (fl : SEvalFlags)
    (Γspec Γ : GlobalDeclarations) : Prop :=
  UpstreamAsks env →
  ∀ {c : Name} {us : List Level} {ups : List Name} {args argsv : List Expr}
      {b b' v : Expr},
    env.WF → LowerEnv Γspec Γ → fl.delta →
    bo c = some b → (∀ I dp nm, ¬ CasesOnShape env c I dp nm) →
    b' = b.instantiateLevelParams ups us →
    argsv.length = args.length →
    (∀ i, i < args.length → SEval env bo Us fl [] args[i]! argsv[i]! ∧
        Simulates env bo lp Us Γspec Γ args[i]! argsv[i]!) →
    StepDefeq env Us [] (mkApps (.const c us) argsv) (mkApps b' argsv) →
    SEval env bo Us fl [] (mkApps b' argsv) v →
    Simulates env bo lp Us Γspec Γ (mkApps b' argsv) v →
    Simulates env bo lp Us Γspec Γ (mkApps (.const c us) args) v

/-! ## The statements `ErasesCorrect/Close.lean` inhabits -/

/-- **T5.** Eight binders carrying seven premises — `her`+`hlow` is `ErasesLB` unfolded, so
that `hspec` can name the middle term — of which the last, `UpstreamAsks env`, drops with no
restatement once the pin moves. The δ arm's level-scope premise is not among them: it is a
conjunct of `ErasesEnv.defns`, under that clause's reachability gate. -/
abbrev ErasesCorrectStmt (env : VEnv) (bo : Name → Option Expr) (lp : Name → List Name)
    (Us : List Name)
    (fl : SEvalFlags) (Γspec Γ : GlobalDeclarations) : Prop :=
  ∀ {e v : Expr} {ve : VExpr} {t₀ t : LBTerm},
    env.WF → TrExprS env Us [] e ve → SEval env bo Us fl [] e v →
    Erases env Us [] e t₀ → Lower Γspec t₀ t → ErasesEnv env bo lp Γspec t₀ →
    LowerEnv Γspec Γ → UpstreamAsks env →
    ∃ v₀ v', Erases env Us [] v v₀ ∧ Lower Γspec v₀ v' ∧ WcbvEval Γ eraseFlags t v'

/-- **T5, folded.** The composite read through `ErasesLB`, with the environment premise at
whichever middle term the composite exhibits. -/
abbrev ErasesCorrectLBStmt (env : VEnv) (bo : Name → Option Expr) (lp : Name → List Name)
    (Us : List Name)
    (fl : SEvalFlags) (Γspec Γ : GlobalDeclarations) : Prop :=
  ∀ {e v : Expr} {ve : VExpr} {t : LBTerm},
    env.WF → TrExprS env Us [] e ve → SEval env bo Us fl [] e v →
    ErasesLB env Us Γspec [] e t →
    (∀ t₀, Erases env Us [] e t₀ → Lower Γspec t₀ t → ErasesEnv env bo lp Γspec t₀) →
    LowerEnv Γspec Γ → UpstreamAsks env →
    ∃ v', ErasesLB env Us Γspec [] v v' ∧ WcbvEval Γ eraseFlags t v'

end LeanToLambdaBox
