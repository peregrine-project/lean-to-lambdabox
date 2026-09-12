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
* the `Lower` inversions the arms take at a `.app` node, at a spine and at a λ;
* `SEval.no_elimSpine_value` — an eliminator spine one minor short heads no value;
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
reading, and `fixBody` is excluded because an application is not a λ. -/
theorem Lower.source_app {Γ : GlobalDeclarations} (hblk : BlockBodiesLambda Γ)
    {s t f a : LBTerm} (h : Lower Γ s t) (hs : s = .app f a) :
    (∃ f' a', t = .app f' a' ∧ Lower Γ f f' ∧ Lower Γ a a') ∨
    (∃ (kn : Kername) (iid : InductiveId) (np dp : Nat) (nfs : List Nat)
        (pre : List LBTerm) (disc : LBTerm) (minors : List LBTerm),
      ElimDecl Γ kn iid np dp nfs ∧ pre.length = dp ∧ minors.length = nfs.length ∧
      LBTerm.app f a = LBTerm.mkApps (.const kn) (pre ++ disc :: minors)) := by
  have hnf := Lower.ne_fix_of_block hblk h (by rw [hs]; exact fun _ => LBTerm.noConfusion)
    (by rw [hs]; rfl)
  cases h with
  | @app f₀ f' a₀ a' hf ha =>
      injection hs with hff haa
      subst hff; subst haa
      exact .inl ⟨f', a', rfl, hf, ha⟩
  | box | bvar | fvar | prim | const | lambda | letIn | proj | construct | «case» =>
      exact LBTerm.noConfusion hs
  | fixConst | fixBody => exact absurd rfl (hnf _ _)
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
theorem Lower.source_mkApps {Γ : GlobalDeclarations} (hblk : BlockBodiesLambda Γ)
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
      rcases Lower.source_app hblk hlow rfl with
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

/-- Everything a specification environment says of a program it says of a subterm: the two
program-facing clauses are keyed on reachability, which a subterm inherits. -/
theorem ErasesEnv.subterm {env : VEnv} {bo : Name → Option Expr}
    {Γspec : GlobalDeclarations} {d t : LBTerm} (h : ErasesEnv env bo Γspec t)
    (hs : SubTerm d t) : ErasesEnv env bo Γspec d :=
  .mk h.keys h.decls (fun kn hr => h.deps kn (hr.subterm hs))
    (fun c b hbo hr => h.defns c b hbo (hr.subterm hs))

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
theorem ErasesEnv.ofReach {env : VEnv} {bo : Name → Option Expr}
    {Γspec : GlobalDeclarations} {t u : LBTerm} (h : ErasesEnv env bo Γspec t)
    (hre : ∀ kn, ReachableFrom Γspec u kn → ReachableFrom Γspec t kn) :
    ErasesEnv env bo Γspec u :=
  .mk h.keys h.decls (fun kn hr => h.deps kn (hre kn hr))
    (fun c b hbo hr => h.defns c b hbo (hre _ hr))

/-- `□` is read against every specification environment. -/
theorem ErasesEnv.box {env : VEnv} {bo : Name → Option Expr}
    {Γspec : GlobalDeclarations} {t : LBTerm} (h : ErasesEnv env bo Γspec t) :
    ErasesEnv env bo Γspec .box :=
  h.ofReach (fun _ hr => absurd hr not_reachableFrom_box)

/-- A contractum names no kername its two parts do not: the environment relation survives
the substitution the β and ζ steps perform. -/
theorem ErasesEnv.substPair {env : VEnv} {bo : Name → Option Expr}
    {Γspec : GlobalDeclarations} {s b : LBTerm} (hs : ErasesEnv env bo Γspec s)
    (hb : ErasesEnv env bo Γspec b) :
    ErasesEnv env bo Γspec (LBTerm.subst s 0 b) := by
  refine .mk hb.keys hb.decls (fun kn hr => ?_) (fun c bb hbo hr => ?_) <;>
    rcases ReachableFrom.substList (l := [s]) (t := b) hr with hbr | ⟨x, hx, hxr⟩
  · exact hb.deps kn hbr
  · obtain rfl : x = s := by simpa using hx
    exact hs.deps kn hxr
  · exact hb.defns c bb hbo hbr
  · obtain rfl : x = s := by simpa using hx
    exact hs.defns c bb hbo hxr

/-- A spine is read against the environment its head and its arguments are. -/
theorem ErasesEnv.mkApps {env : VEnv} {bo : Name → Option Expr}
    {Γspec : GlobalDeclarations} {f : LBTerm} {l : List LBTerm}
    (hf : ErasesEnv env bo Γspec f) (hl : ∀ x ∈ l, ErasesEnv env bo Γspec x) :
    ErasesEnv env bo Γspec (LBTerm.mkApps f l) := by
  refine .mk hf.keys hf.decls (fun kn hr => ?_) (fun c bb hbo hr => ?_) <;>
    rcases ReachableFrom.mkApps_inv l f hr with hfr | ⟨x, hx, hxr⟩
  · exact hf.deps kn hfr
  · exact (hl x hx).deps kn hxr
  · exact hf.defns c bb hbo hfr
  · exact (hl x hx).defns c bb hbo hxr

/-! ## An eliminator spine one minor short -/

/-- **A source eliminator spine below its arity heads no value.** `deltaC` is blocked by
its own eliminator guard against `hsh`, `ctorVal` and `indVal` by `hco` through
`Origin.lean`, `iota` by `CasesOnShape.inj` against the under-application, and `beta` by
the induction on the spine length. This is what the β arm's `elimApp` reading at an empty
`extra` is refuted by. -/
theorem SEval.no_elimSpine_value {env : VEnv} {bo : Name → Option Expr} {Us : List Name}
    {fl : SEvalFlags} {Δ : VLCtx} {c I : Name} {us : List Level} {dp nm : Nat}
    {args : List Expr} {w : Expr}
    (A : UpstreamAsks env) (hsh : CasesOnShape env c I dp nm) (hco : ConstOrigin env c)
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
    | deltaC _ _ hnd _ _ _ _ _ =>
        obtain ⟨rfl, -, -⟩ := mkApps_const_inj _ rfl he
        exact hnd _ _ _ hsh
    | ctorVal hc _ _ _ _ =>
        obtain ⟨rfl, -, -⟩ := mkApps_const_inj _ rfl he
        exact constOrigin_not_ctorOf A hco _ _ hc
    | indVal hi _ _ =>
        obtain ⟨rfl, -, -⟩ := mkApps_const_inj _ rfl he
        exact constOrigin_not_indInfo A hco _ _ _ hi
    | @iota con I' ctor us₀ cus pre prev minors minorsv extra extrav cargs disc r np cidx
        _ hsh' _ _ _ _ _ _ _ _ _ _ _ _ =>
        obtain ⟨rfl, -, hargs⟩ := mkApps_const_inj _ rfl he
        have hI : I' = I := (hsh'.2.1).symm.trans hsh.2.1
        subst hI
        obtain ⟨hdp, hnm⟩ := CasesOnShape.inj A hsh hsh'
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
    {bo : Name → Option Expr} {fl : SEvalFlags} {Γspec Γ : GlobalDeclarations}
    (hblk : BlockBodiesLambda Γspec) {e v : Expr} {ve : VExpr} {t₀ t : LBTerm}
    (htr : TrExprS env Us [] e ve) (hbox : ErasesBox env Us [] e t₀)
    (hlow : Lower Γspec t₀ t) (hspec : ErasesEnv env bo Γspec t₀)
    (hev : SEval env bo Us fl [] e v) :
    ∃ v₀ v', Erases env Us [] v v₀ ∧ Lower Γspec v₀ v' ∧ WcbvEval Γ eraseFlags t v' ∧
      ErasesEnv env bo Γspec v₀ := by
  obtain ⟨hb, rfl⟩ := hbox
  have ht : t = .box := Lower.source_box hblk hlow rfl
  obtain ⟨v', her, hEv⟩ := erases_correct_box (Γ := Γ) (Δ := []) henv trivial htr hb hev
  obtain rfl : v' = .box := eval_deterministic hEv .box
  exact ⟨.box, .box, her, .box, by rw [ht]; exact .box, hspec.box⟩

/-- **The box arm at a composite spine.** A boxed proper prefix boxes the whole spine; the
target folds by `eval_box`, whose discarded arguments evaluate because the induction
hypotheses at them do. -/
theorem erases_correct_boxSpineLow {env : VEnv} (henv : env.WF) {Us : List Name}
    {bo : Name → Option Expr} {fl : SEvalFlags} {Γspec Γ : GlobalDeclarations}
    (hblk : BlockBodiesLambda Γspec) {hd : Expr} {pre suf : List Expr} {ts : List LBTerm}
    {ve : VExpr} {v : Expr} {t : LBTerm}
    (htr : TrExprS env Us [] (mkApps hd (pre ++ suf)) ve)
    (hbox : ∃ we, TrExprS env Us [] (mkApps hd pre) we ∧
      Erasable env Us.length (VLCtx.toCtx []) we)
    (hlow : Lower Γspec (LBTerm.mkApps .box ts) t)
    (hspec : ErasesEnv env bo Γspec (LBTerm.mkApps .box ts))
    (hargs : ∀ s ∈ ts, ∀ u, Lower Γspec s u → ∃ x, WcbvEval Γ eraseFlags u x)
    (hev : SEval env bo Us fl [] (mkApps hd (pre ++ suf)) v) :
    ∃ v₀ v', Erases env Us [] v v₀ ∧ Lower Γspec v₀ v' ∧ WcbvEval Γ eraseFlags t v' ∧
      ErasesEnv env bo Γspec v₀ := by
  obtain ⟨hd', ts', rfl, hhd, hlen', hpt⟩ :=
    Lower.source_mkApps hblk (fun _ _ => LBTerm.noConfusion) (fun _ => LBTerm.noConfusion)
      ts hlow
  obtain rfl : hd' = .box := Lower.source_box hblk hhd rfl
  have hev' : ∀ s ∈ ts', ∃ x, WcbvEval Γ eraseFlags s x := by
    intro s hsm
    obtain ⟨i, hi, rfl⟩ := Lower.mem_getElem! hsm
    exact hargs _ (Lower.getElem!_mem (by omega)) _ (hpt i (by omega))
  obtain ⟨v', her, hEv⟩ :=
    erases_correct_boxSpine (Γ := Γ) (Δ := []) (ts := ts') henv trivial htr hbox hev' hev
  obtain rfl : v' = .box := eval_deterministic hEv (WcbvEval.mkApps_box ts' hev' .box)
  exact ⟨.box, .box, her, .box, WcbvEval.mkApps_box ts' hev' .box, hspec.box⟩

/-! ## What the target does at a β-redex

The β arm's function value erases to a λ, and a λ has two images: a λ, and — when the
value is a block member's own specification body — that block's `.fix` node. At the second
the target unfolds the fix instead of β-reducing, and the unfolding is a λ again or the
same node one block deeper, which is why the transport is an induction on the derivation.
-/

/-- The target reads `X` as a function that β-steps into `c`. -/
def BetaReady (Γ : GlobalDeclarations) (fl : WcbvFlags) (X c : LBTerm) : Prop :=
  ∀ {f a av r : LBTerm}, WcbvEval Γ fl f X → WcbvEval Γ fl a av →
    WcbvEval Γ fl (LBTerm.subst1 av c) r → WcbvEval Γ fl (.app f a) r

/-- A λ in the target comes from a λ, body to body: `lambda` is the only arm with a λ
image. -/
theorem Lower.target_lambda {Γ : GlobalDeclarations} {s t : LBTerm} {n : BinderName}
    {b' : LBTerm} (h : Lower Γ s t) (ht : t = .lambda n b') :
    ∃ m b, s = .lambda m b ∧ Lower Γ b b' := by
  cases h with
  | @lambda n₀ n' b₀ b₁ hb =>
      injection ht with _ hbb
      exact ⟨n₀, b₀, rfl, hbb ▸ hb⟩
  | box | bvar | fvar | prim | const | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion ht
  | fixConst | fixBody => exact LBTerm.noConfusion ht
  | @elimApp kn iid np dp nfs pre disc disc' minors alts extra extra' =>
      obtain ⟨rfl, hc⟩ := mkApps_eq_lambda ht
      exact LBTerm.noConfusion hc

/-- The block rewriting maps a `.fix` node to itself: a nested block's members are none of
`kns`. -/
theorem ConstToFVar.fix_inv {kns : List Kername} {ids : List FVarId}
    {defs : List (@FixDef LBTerm)} {k : Nat} {u : LBTerm}
    (h : ConstToFVar kns ids (.fix defs k) u) : u = .fix defs k := by
  cases h with | fix => rfl

/-- **The β transport.** A λ's image is β-ready at the same body: either it is a λ, or it
is a block's `.fix` node, whose unfolding at `principalArgIdx = 0` is β-ready in turn. -/
theorem Lower.appReady {Γspec Γ : GlobalDeclarations} (hΓ : ClosedBodies Γspec)
    {fl : WcbvFlags} (hg : fl.with_guarded_fix = true) {nm : BinderName} {b₀ : LBTerm}
    {s t : LBTerm} (h : Lower Γspec s t) (hs : s = .lambda nm b₀) :
    ∃ c, Lower Γspec b₀ c ∧ BetaReady Γ fl t c := by
  revert hs
  induction h using Lower.rec (motive_2 := fun _ _ _ _ => True) with
  | @lambda n₀ n' b₁ b' hb _ =>
      intro hs
      injection hs with _ hbb
      subst hbb
      exact ⟨b', hb, fun hf ha hr => .beta hf ha hr⟩
  | box | bvar | fvar | prim | const | letIn | app | proj | construct | «case» =>
      intro hs; exact LBTerm.noConfusion hs
  | fixConst => intro hs; exact LBTerm.noConfusion hs
  | @elimApp kn iid np dp nfs pre disc disc' minors alts extra extra' _ _ _ _ _ _ _ _ _ _ =>
      intro hs
      obtain ⟨-, hc⟩ := mkApps_eq_lambda hs
      exact LBTerm.noConfusion hc
  | @fixBody b kns bs bs' ids defs j hb hb' hd hnd hids hilen hfresh hrarg hdecl hlow hcl
      hj hjl ih =>
      intro hs
      have hblock : LowerBlock Γspec kns bs bs' ids defs :=
        ⟨hb, hb', hd, hnd, hids, hilen, hfresh, hrarg, hdecl, hlow, hcl⟩
      have hjk : j < kns.length := by rw [← hd]; exact hjl
      obtain ⟨hjb, hbsj⟩ := Lower.getElem!_of_getElem? hj
      have hlam : bs[j]! = .lambda nm b₀ := hbsj.trans hs
      obtain ⟨u, hct, heq⟩ := hcl j hjk
      have hbcl : LBClosed bs'[j]! 0 :=
        Lower.closed hΓ (hlow j hjk) 0 (hΓ _ _ (hdecl j hjk))
      have hucl : LBClosed u 0 := hct.closed hbcl
      have hsub : LBTerm.substList (LBTerm.fixSubst defs) (defs[j]!).body
          = substFix ids defs u := by
        rw [heq]; exact hblock.substList_fixSubst hΓ hucl
      have hdj : defs[j]? = some defs[j]! := getElem?_getElem! hjl
      have hrarg' : (defs[j]!).principalArgIdx = ([] : List LBTerm).length :=
        hrarg _ (Lower.getElem!_mem hjl)
      refine ?_
      rcases Lower.source_lambda (hlow j hjk) hlam with ⟨n', b', hbs'⟩ | ⟨defs₂, k, hbs'⟩
      · have hlowU : Lower Γspec bs[j]! (substFix ids defs u) :=
          Lower.constToFix hΓ hblock (fun x hx => hfresh x hx j hjk) (hlow j hjk) hct
        have hlamU : isLambda (substFix ids defs u) = true := by
          rw [← hsub]
          refine isLambda_substList _ ?_
          rw [heq, isLambda_closeFix, hct.isLambda_eq, hbs']
          rfl
        obtain ⟨n'', c, hUeq⟩ := isLambda_eq_true hlamU
        rw [hlam, hUeq] at hlowU
        obtain ⟨m, b, hmb, hbc⟩ := Lower.target_lambda hlowU rfl
        injection hmb with _ hb₀
        subst hb₀
        refine ⟨c, hbc, fun {f a av r} hf ha hr => ?_⟩
        refine .fix_guarded (argsv := []) hg hf ha hdj hrarg' ?_
        rw [LBTerm.mkApps_nil, hsub, hUeq]
        exact .beta (.lam _ _) (value_final (eval_to_value ha)) hr
      · have hu : u = .fix defs₂ k := by rw [hbs'] at hct; exact hct.fix_inv
        have hself : substFix ids defs u = bs'[j]! := by
          rw [substFix]
          rw [substFVarList_eq_self_of_not_hasFVar _ u (fun q hq => ?_), hu, hbs']
          obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hq
          rw [hu, ← hbs']
          exact hfresh w.1 (List.fst_mem_of_mem_zipIdx hw) j hjk
        obtain ⟨c, hbc, hready⟩ := ih j hjk hlam
        refine ⟨c, hbc, fun {f a av r} hf ha hr => ?_⟩
        refine .fix_guarded (argsv := []) hg hf ha hdj hrarg' ?_
        rw [hbs'] at hready
        rw [LBTerm.mkApps_nil, hsub, hself, hbs']
        exact hready (.fix_atom _ _) (value_final (eval_to_value ha)) hr
  | done | lam => trivial

/-! ## The forward readings of a specification environment

`ErasesEnv.decls` runs entry-to-justification: at a key it says the entry `Γspec` holds is
justified, not whose entry it is. `ErasesEnv.defns` is the forward reading at a definition;
the two readings below are its twins at an inductive block and at an eliminator, and the
`ctorVal` and `beta` arms consume exactly them. Both are facts about `Γspec` and `env`
alone, true of the environment a run registers, and `ErasesEnv` is where they belong.
-/

/-- The two forward readings the arms take of a specification environment. -/
structure ErasesEnvFwd (env : VEnv) (bo : Name → Option Expr) (Us : List Name)
    (fl : SEvalFlags) (Γspec : GlobalDeclarations) : Prop where
  /-- At an inductive block's kername the entry is that block's own declaration, with the
      numbers the target semantics reads. -/
  blocks : ∀ {I : Name} {iid : InductiveId} {np : Nat} {nfs : List Nat},
    IndInfo env I iid np nfs → (LBTerm.envLookup Γspec iid.mutualBlockName).isSome →
    ∃ mib, LBTerm.envLookup Γspec iid.mutualBlockName = some (.inductiveDecl mib) ∧
      IndBodyOf iid np nfs mib
  /-- An eliminator spine below its arity is the erasure of no source term that has a
      value: `SEval.no_elimSpine_value` at the source constant the key belongs to. -/
  noElimSpine : ∀ {kn : Kername} {iid : InductiveId} {np dp : Nat} {nfs : List Nat}
    {args : List LBTerm} {e w : Expr},
    ElimDecl Γspec kn iid np dp nfs → args.length < dp + 1 + nfs.length →
    Erases env Us [] e (LBTerm.mkApps (.const kn) args) → ¬ SEval env bo Us fl [] e w

/-- `getElem!` through a `List.map` read off the mapped list. -/
theorem getElem!_of_map_eq {α β : Type} [Inhabited α] [Inhabited β] {f : α → β}
    {l : List α} {m : List β} (h : l.map f = m) {k : Nat} (hk : k < m.length) :
    ∃ x, l[k]? = some x ∧ f x = m[k]! := by
  subst h
  have hlen : k < l.length := by simpa using hk
  refine ⟨l[k]'hlen, List.getElem?_eq_getElem hlen, ?_⟩
  rw [getElem!_pos (l.map f) k (by simpa using hlen), List.getElem_map]

/-- **The emitted constructor arity of a reached block.** The forward block reading plus
`LowerEnv.inds` put `IndBodyOf`'s numbers where `WcbvEval.construct_atom` and
`construct_app` read them. -/
theorem ErasesEnvFwd.ctorArity {env : VEnv} {bo : Name → Option Expr} {Us : List Name}
    {fl : SEvalFlags} {Γspec Γ : GlobalDeclarations} (hfwd : ErasesEnvFwd env bo Us fl Γspec)
    (henvL : LowerEnv Γspec Γ) {I : Name} {iid : InductiveId} {np k : Nat} {nfs : List Nat}
    (hi : IndInfo env I iid np nfs)
    (hdep : (LBTerm.envLookup Γspec iid.mutualBlockName).isSome) (hk : k < nfs.length) :
    constructorArity Γ iid k = some (np + nfs[k]!) := by
  obtain ⟨mib, hspecl, hnp, oib, hoib, -, hctors⟩ := hfwd.blocks hi hdep
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

/-! ## The motive and the three step interfaces -/

/-- The simulation's claim at one source node: for every composite image of `e` that the
environment relation answers, an image of `v`, a target evaluation reaching it, and the
same environment relation at the image of `v`. The last conjunct is the accumulator the
β, ζ, δ and ι arms take their induction hypothesis at the contractum under. -/
def Simulates (env : VEnv) (bo : Name → Option Expr) (Us : List Name)
    (Γspec Γ : GlobalDeclarations) (e v : Expr) : Prop :=
  ∀ {ve : VExpr} {t₀ t : LBTerm},
    TrExprS env Us [] e ve → Erases env Us [] e t₀ → Lower Γspec t₀ t →
    ErasesEnv env bo Γspec t₀ →
    ∃ v₀ v', Erases env Us [] v v₀ ∧ Lower Γspec v₀ v' ∧ WcbvEval Γ eraseFlags t v' ∧
      ErasesEnv env bo Γspec v₀

/-- The ι arm of `SEval`, with the induction hypothesis available at every subderivation.
`UpstreamAsks env` is what `Origin.lean`'s corollaries take while the fork cannot be
edited from here. -/
abbrev StepIota (env : VEnv) (bo : Name → Option Expr) (Us : List Name) (fl : SEvalFlags)
    (Γspec Γ : GlobalDeclarations) : Prop :=
  UpstreamAsks env →
  ∀ {con I ctor : Name} {us cus : List Level} {pre prev minors minorsv extra extrav
      cargs : List Expr} {disc r : Expr} {np cidx : Nat},
    env.WF → LowerEnv Γspec Γ → fl.iota →
    CasesOnShape env con I pre.length minors.length → ConstOrigin env con →
    CtorOf env ctor I cidx →
    prev.length = pre.length →
    (∀ i, i < pre.length → SEval env bo Us fl [] pre[i]! prev[i]! ∧
        Simulates env bo Us Γspec Γ pre[i]! prev[i]!) →
    SEval env bo Us fl [] disc (mkApps (.const ctor cus) cargs) →
    Simulates env bo Us Γspec Γ disc (mkApps (.const ctor cus) cargs) →
    minorsv.length = minors.length →
    (∀ i, i < minors.length → SEval env bo Us fl [] minors[i]! minorsv[i]! ∧
        Simulates env bo Us Γspec Γ minors[i]! minorsv[i]!) →
    extrav.length = extra.length →
    (∀ i, i < extra.length → SEval env bo Us fl [] extra[i]! extrav[i]! ∧
        Simulates env bo Us Γspec Γ extra[i]! extrav[i]!) →
    cidx < minors.length →
    StepDefeq env Us [] (mkApps (.const con us) (pre ++ disc :: minors ++ extra))
      (mkApps minors[cidx]! (cargs.drop np ++ extra)) →
    SEval env bo Us fl [] (mkApps minors[cidx]! (cargs.drop np ++ extra)) r →
    Simulates env bo Us Γspec Γ (mkApps minors[cidx]! (cargs.drop np ++ extra)) r →
    Simulates env bo Us Γspec Γ (mkApps (.const con us) (pre ++ disc :: minors ++ extra)) r

/-- The projection arm, with the induction hypothesis at the discriminant and at the
selected field. -/
abbrev StepProj (env : VEnv) (bo : Name → Option Expr) (Us : List Name) (fl : SEvalFlags)
    (Γspec Γ : GlobalDeclarations) : Prop :=
  UpstreamAsks env →
  ∀ {S ctor : Name} {i np : Nat} {cus : List Level} {disc r : Expr}
      {cargs : List Expr},
    env.WF → LowerEnv Γspec Γ → fl.proj →
    SEval env bo Us fl [] disc (mkApps (.const ctor cus) cargs) →
    Simulates env bo Us Γspec Γ disc (mkApps (.const ctor cus) cargs) →
    np + i < cargs.length →
    StepDefeq env Us [] (.proj S i disc) cargs[np + i]! →
    SEval env bo Us fl [] cargs[np + i]! r →
    Simulates env bo Us Γspec Γ cargs[np + i]! r →
    Simulates env bo Us Γspec Γ (.proj S i disc) r

/-- The δ arm, at a compiler body, with the induction hypothesis at the arguments and at
the unfolded application. -/
abbrev StepDelta (env : VEnv) (bo : Name → Option Expr) (Us : List Name) (fl : SEvalFlags)
    (Γspec Γ : GlobalDeclarations) : Prop :=
  ∀ {c : Name} {us : List Level} {ups : List Name} {args argsv : List Expr}
      {b b' v : Expr},
    env.WF → LowerEnv Γspec Γ → fl.delta →
    bo c = some b → (∀ I dp nm, ¬ CasesOnShape env c I dp nm) →
    b' = b.instantiateLevelParams ups us →
    argsv.length = args.length →
    (∀ i, i < args.length → SEval env bo Us fl [] args[i]! argsv[i]! ∧
        Simulates env bo Us Γspec Γ args[i]! argsv[i]!) →
    StepDefeq env Us [] (mkApps (.const c us) argsv) (mkApps b' argsv) →
    SEval env bo Us fl [] (mkApps b' argsv) v →
    Simulates env bo Us Γspec Γ (mkApps b' argsv) v →
    Simulates env bo Us Γspec Γ (mkApps (.const c us) args) v

/-! ## The statements `ErasesCorrect/Close.lean` inhabits -/

/-- **T5.** Seven binders carrying six premises — `her`+`hlow` is `ErasesLB` unfolded, so
that `hspec` can name the middle term — plus the eighth, `UpstreamAsks env`, which drops
with no restatement once the pin moves. -/
abbrev ErasesCorrectStmt (env : VEnv) (bo : Name → Option Expr) (Us : List Name)
    (fl : SEvalFlags) (Γspec Γ : GlobalDeclarations) : Prop :=
  ∀ {e v : Expr} {ve : VExpr} {t₀ t : LBTerm},
    env.WF → TrExprS env Us [] e ve → SEval env bo Us fl [] e v →
    Erases env Us [] e t₀ → Lower Γspec t₀ t → ErasesEnv env bo Γspec t₀ →
    LowerEnv Γspec Γ → UpstreamAsks env →
    ∃ v₀ v', Erases env Us [] v v₀ ∧ Lower Γspec v₀ v' ∧ WcbvEval Γ eraseFlags t v'

/-- **T5, folded.** The composite read through `ErasesLB`, with the environment premise at
whichever middle term the composite exhibits. -/
abbrev ErasesCorrectLBStmt (env : VEnv) (bo : Name → Option Expr) (Us : List Name)
    (fl : SEvalFlags) (Γspec Γ : GlobalDeclarations) : Prop :=
  ∀ {e v : Expr} {ve : VExpr} {t : LBTerm},
    env.WF → TrExprS env Us [] e ve → SEval env bo Us fl [] e v →
    ErasesLB env Us Γspec [] e t →
    (∀ t₀, Erases env Us [] e t₀ → Lower Γspec t₀ t → ErasesEnv env bo Γspec t₀) →
    LowerEnv Γspec Γ → UpstreamAsks env →
    ∃ v', ErasesLB env Us Γspec [] v v' ∧ WcbvEval Γ eraseFlags t v'

end LeanToLambdaBox
