import LeanToLambdaBox.ErasesStrengthen
import LeanToLambdaBox.SubjectReduction
import LeanToLambdaBox.Semantics.Metatheory

/-!
# What the simulation's arms consume: spines, the `□` arms, the pointwise kit

The simulation this module serves — `erases_correct` as `doc/rework/04-AMENDMENT-W2.md` §6
prints it — is one induction on `SEval`, at the **emitted** environment, with the ι,
projection and δ arms as step lemmas. This module holds what those arms take as given:

* `trExprS_spine_mem` — every argument of a translated spine translates;
* `Erases.mkApps_forall₂` and `erases_mkApps_inv` — erasure along a spine, and the inversion
  splitting an erased spine into a head erasure with pointwise arguments or a boxed proper
  prefix: the ι arm's own case split;
* `erasable_mkApps` — a spine whose head is irrelevant is irrelevant, `Erasable.app`
  iterated;
* `erases_correct_box` and `erases_correct_boxSpine` — the `□` arm, at a term and at a spine;
* the `List.Forall₂` kit bridging pointwise lists and `SEval`'s index-keyed premises.

## Deleted by the Wave-2 amendment

| declaration | what it claimed | answered by |
|---|---|---|
| `erases_correct_tabled`, `erases_correct_tabled_ctx` | the simulation over the β/ζ/δ/literal fragment, at the specification environment, under two guards beyond the design's five hypotheses | §6: those arms become the step lemmas of one simulation at the emitted environment |
| `TabledConstants` | every constant the source environment declares has a compiler body — MetaCoq's `axiom_free`, imported as the first guard | §5: `SEval`'s value arms are `[S Fig. 12]`'s `value_head`, so a body-less constant has no source value and the guard has nothing to do |
| `erases_correct_needs_tabled` | W2-R2: without that guard the five hypotheses are jointly satisfiable at a declared, body-less constant, where the target is stuck | §5 |
| `erases_correct_needs_tabled_ctor`, `erases_const_ne_construct` | W2-R1: at a constructor constant the ten-rule `Erases` offers only `.const` or `.box`, while the specification environment gives that kername a `.construct` body which `WcbvEval` unfolds eagerly | §4: the eleventh rule `Erases.ctor`, whose image is that `.construct` node |
| `DeltaAgrees` | the second guard: the specification environment erases the compiler body of every tabled constant, at the level instantiation the δ step takes | §8: `ErasesEnv`'s `defns` clause, in the δ arm's own direction |
| `erasesEnv_not_deltaAgrees` | W2-R3: `ErasesEnv` does not deliver that guard — it is keyed on one program and its `decls` clause runs the opposite direction | §8 |
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
        Erases env Us Δ (mkApps hd as) (LBTerm.mkApps th ts) := by
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

end LeanToLambdaBox
