import LeanToLambdaBox.ErasesEnv
import LeanToLambdaBox.ErasesStrengthen
import LeanToLambdaBox.SubjectReduction
import LeanToLambdaBox.Semantics.Metatheory

/-!
# T5 — erasure correctness, forward simulation

`erases_correct_tabled` is the forward simulation of Sozeau et al. transposed to `Expr`: a
source term that evaluates to `v` erases to a λ□ term that evaluates to an erasure of `v`,
at the specification environment and `eraseFlags`. It holds at **every** `SEvalFlags` point,
`fullFlags` included: what cuts the fragment is the first guard below, not the flags.

It carries two guards beyond the five hypotheses of the design, because the unguarded
statement is false:

* `TabledConstants env bo` — every constant `env` declares has a compiler body. It is
  MetaCoq's `axiom_free Σ` transposed, and it is what refutes `SEval.ctorVal` at a relevant
  head; `erases_correct_needs_tabled` refutes the unguarded statement at a body-less
  constant and `erases_correct_needs_tabled_ctor` at a constructor. Under it no source value is a
  constant-headed spine, so the ι and projection arms are discharged by that refutation and
  the fragment is β, ζ, δ and literal unfolding.
* `DeltaAgrees env bo Us Γ` — the specification environment declares, for every tabled
  constant, a body erasing the compiler body at the level instantiation the δ step takes.
  `ErasesEnv` does not supply it: its `deps` clause is keyed on one program and does not
  propagate to the subterms an induction visits.

`w2Flags` is the design's name for the βζδ + literal + projection point; the theorem needs
no flag hypothesis, so it is only the witnesses that run there.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-! ## The flag point -/

/-- β, ζ, δ, literal unfolding and projection enabled; ι disabled. -/
def w2Flags : SEvalFlags := ⟨true, true, true, false, true, true⟩

theorem w2Flags_iota : w2Flags.iota = false := by decide

theorem w2Flags_on :
    w2Flags.beta = true ∧ w2Flags.zeta = true ∧ w2Flags.delta = true ∧
      w2Flags.lit = true ∧ w2Flags.proj = true := by decide

/-- The point is below `fullFlags`, where the simulation also holds. -/
theorem w2Flags_le_fullFlags : w2Flags ≤ fullFlags := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro <;> rfl

/-! ## Target-side spine metatheory

What an application spine's evaluation depends on: the *values* of its head and of its
arguments, not their syntax. These belong beside `eval_deterministic` in
`Semantics/Metatheory.lean`.
-/

/-- The head of an evaluating application spine evaluates. -/
theorem WcbvEval.head_value_of_mkApps {Γ : GlobalDeclarations} {fl : WcbvFlags} :
    ∀ (as : List LBTerm) {f r : LBTerm}, WcbvEval Γ fl (LBTerm.mkApps f as) r →
      ∃ fv, WcbvEval Γ fl f fv
  | [], _, _, h => ⟨_, h⟩
  | a :: as, f, _, h => by
      obtain ⟨_, hX⟩ := head_value_of_mkApps as (f := .app f a) h
      cases hX with
      | beta hf _ _ => exact ⟨_, hf⟩
      | app_box hf _ => exact ⟨_, hf⟩
      | construct_app _ hf _ _ _ => exact ⟨_, hf⟩
      | fix_guarded _ hf _ _ _ _ => exact ⟨_, hf⟩
      | fix_stuck _ hf _ _ _ => exact ⟨_, hf⟩
      | fix_unguarded _ hf _ _ _ => exact ⟨_, hf⟩
      | app_cong hf _ _ => exact ⟨_, hf⟩

/-- An application's evaluation reads its function and argument only through their values:
every `.app` rule has exactly one premise about each, and none reads their syntax. -/
theorem WcbvEval.app_congr {Γ : GlobalDeclarations} {fl : WcbvFlags}
    {f f' a a' fv av r : LBTerm}
    (hf : WcbvEval Γ fl f fv) (hf' : WcbvEval Γ fl f' fv)
    (ha : WcbvEval Γ fl a av) (ha' : WcbvEval Γ fl a' av)
    (h : WcbvEval Γ fl (.app f a) r) : WcbvEval Γ fl (.app f' a') r := by
  cases h with
  | beta hf₁ ha₁ hb =>
      exact .beta (eval_deterministic hf hf₁ ▸ hf') (eval_deterministic ha ha₁ ▸ ha') hb
  | app_box hf₁ ha₁ =>
      exact .app_box (eval_deterministic hf hf₁ ▸ hf') (eval_deterministic ha ha₁ ▸ ha')
  | construct_app hb hf₁ har hlt ha₁ =>
      exact .construct_app hb (eval_deterministic hf hf₁ ▸ hf') har hlt
        (eval_deterministic ha ha₁ ▸ ha')
  | fix_guarded hg hf₁ ha₁ hd hidx hr =>
      exact .fix_guarded hg (eval_deterministic hf hf₁ ▸ hf')
        (eval_deterministic ha ha₁ ▸ ha') hd hidx hr
  | fix_stuck hg hf₁ ha₁ hd hlt =>
      exact .fix_stuck hg (eval_deterministic hf hf₁ ▸ hf')
        (eval_deterministic ha ha₁ ▸ ha') hd hlt
  | fix_unguarded hg hf₁ hd ha₁ hr =>
      exact .fix_unguarded hg (eval_deterministic hf hf₁ ▸ hf') hd
        (eval_deterministic ha ha₁ ▸ ha') hr
  | app_cong hf₁ hstuck ha₁ =>
      exact .app_cong (eval_deterministic hf hf₁ ▸ hf') hstuck
        (eval_deterministic ha ha₁ ▸ ha')

/-- Same-valued heads and same-valued arguments give the same spine value. -/
theorem WcbvEval.mkApps_congr {Γ : GlobalDeclarations} {fl : WcbvFlags} :
    ∀ {as as' : List LBTerm},
      List.Forall₂ (fun a a' => ∃ av, WcbvEval Γ fl a av ∧ WcbvEval Γ fl a' av) as as' →
      ∀ {f f' fv r : LBTerm}, WcbvEval Γ fl f fv → WcbvEval Γ fl f' fv →
        WcbvEval Γ fl (LBTerm.mkApps f as) r → WcbvEval Γ fl (LBTerm.mkApps f' as') r := by
  intro as as' hall
  induction hall with
  | nil => intro f f' fv r hf hf' h; exact eval_deterministic hf h ▸ hf'
  | @cons a a' as as' hpair _ ih =>
      intro f f' fv r hf hf' h
      obtain ⟨av, ha, ha'⟩ := hpair
      obtain ⟨X, hX⟩ := WcbvEval.head_value_of_mkApps as (f := .app f a) h
      exact ih hX (WcbvEval.app_congr hf hf' ha ha' hX) h

/-- A spine headed by a term evaluating to `□` evaluates to `□`, provided its arguments
evaluate: MetaCoq's `eval_box`, iterated. -/
theorem WcbvEval.mkApps_box {Γ : GlobalDeclarations} {fl : WcbvFlags} :
    ∀ (ts : List LBTerm), (∀ t ∈ ts, ∃ x, WcbvEval Γ fl t x) →
      ∀ {f : LBTerm}, WcbvEval Γ fl f .box → WcbvEval Γ fl (LBTerm.mkApps f ts) .box
  | [], _, _, hf => hf
  | t :: ts, hts, f, hf => by
      obtain ⟨x, hx⟩ := hts t (List.mem_cons_self ..)
      exact WcbvEval.mkApps_box ts (fun u hu => hts u (List.mem_cons_of_mem _ hu))
        (.app_box hf hx)

/-! ## Source-side spines

A source value is a `mkApps` spine, and the head of a spine is what decides whether a
`ctorVal` step could have produced it.
-/

/-- The head of a source application spine (peel every `Expr.app`). -/
def srcSpineHead : Expr → Expr
  | .app f _ => srcSpineHead f
  | e => e

theorem srcSpineHead_mkApps : ∀ (f : Expr) (as : List Expr),
    srcSpineHead (mkApps f as) = srcSpineHead f
  | _, [] => rfl
  | f, a :: as => by rw [mkApps_cons, srcSpineHead_mkApps (.app f a) as]; rfl

/-- A constant-headed spine is not a λ-abstraction. -/
theorem mkApps_const_ne_lam {c : Name} {us : List Level} {as : List Expr}
    {n : Name} {ty b : Expr} {bi : BinderInfo} :
    mkApps (.const c us) as ≠ .lam n ty b bi := by
  intro h
  have := congrArg srcSpineHead h
  rw [srcSpineHead_mkApps] at this
  exact Expr.noConfusion this

/-- Two constant-headed spines agree on their head constant. -/
theorem mkApps_const_head_inj {c c' : Name} {us us' : List Level} {as as' : List Expr}
    (h : mkApps (.const c us) as = mkApps (.const c' us') as') : c = c' := by
  have := congrArg srcSpineHead h
  rw [srcSpineHead_mkApps, srcSpineHead_mkApps] at this
  replace this : Expr.const c us = Expr.const c' us' := this
  rw [Expr.const.injEq] at this
  exact this.1

/-- **Only `SEval.ctorVal` produces a constant-headed value**, and it fires only at a head
the compiler-body table does not define. -/
theorem SEval.untabled_of_constHead_value {env : VEnv} {bo : Name → Option Expr}
    {Us : List Name} {fl : SEvalFlags} {Δ : VLCtx} {e v : Expr}
    (h : SEval env bo Us fl Δ e v) :
    ∀ {cn : Name} {us : List Level} {argsv : List Expr},
      v = mkApps (.const cn us) argsv → bo cn = none := by
  induction h with
  | lam n ty b bi => exact fun heq => absurd heq.symm mkApps_const_ne_lam
  | beta _ _ _ _ _ _ ihb => exact ihb
  | zeta _ _ _ _ ihb => exact ihb
  | deltaC _ _ _ _ _ _ _ _ ihcont => exact ihcont
  | ctorVal hnb _ _ _ => exact fun heq => mkApps_const_head_inj heq ▸ hnb
  | iota _ _ _ _ _ _ ihcont => exact ihcont
  | proj _ _ _ _ _ _ ihcont => exact ihcont
  | lit _ _ ih => exact ih

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

/-! ## `TabledConstants` -/

/--
Every constant `env` declares has a compiler body.

MetaCoq's `axiom_free Σ` (`∀ c decl, declared_constant Σ c decl → cst_body decl ≠ None`)
transposed to the compiler-body table. It is strictly stronger than MetaCoq's, because in
Lean a constructor and a `casesOn` eliminator are `Expr.const` heads too and the table
defines neither: the fragment it names excludes constructor values.
-/
def TabledConstants (env : VEnv) (bo : Name → Option Expr) : Prop :=
  ∀ c ci, env.constants c = some ci → (bo c).isSome

/-- Under `TabledConstants` no well-typed source term evaluates to a constant-headed
spine: the head would be declared and hence tabled, while `ctorVal` needs it untabled. -/
theorem SEval.no_constHead_value {env : VEnv} (henv : env.WF) {Us : List Name} {Δ : VLCtx}
    (hΔ : VLCtx.WF env Us.length Δ) {bo : Name → Option Expr}
    (hbo : TabledConstants env bo) {fl : SEvalFlags} {e : Expr} {ve : VExpr}
    {cn : Name} {us : List Level} {argsv : List Expr}
    (htr : TrExprS env Us Δ e ve)
    (hev : SEval env bo Us fl Δ e (mkApps (.const cn us) argsv)) : False := by
  obtain ⟨_, htrv, _⟩ := SEval.defeq henv hΔ htr hev
  obtain ⟨_, htrhead⟩ := trExprS_spine_head argsv htrv
  cases htrhead with
  | const hc _ _ =>
      have := hbo _ _ hc
      rw [SEval.untabled_of_constHead_value hev rfl] at this
      exact absurd this (by simp)

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

/-! ## The ζ arm's transport

Two moves the de Bruijn transport layer does not carry, both about a `.vlet` entry: swapping
its recorded value for a definitionally equal one, and instantiating it away. Their natural
home is beside `erases_subst` in `ErasesAbstract.lean`.
-/

/--
Erasure transports along a definitionally equal context, given a translation of the source
term in the source context.

The `box` arm moves its witnesses with `TrExprS.defeqDFC'`, `Erasable.defeqDFC` and
`Erasable.defeq`; the binder arms need a `VLocalDecl.IsDefEq` for the entry they cons, which
is typed at a sort and so needs the binder type's `IsType` — data `Erases.lam` does not
carry and the translation does.
-/
theorem Erases.defeqDFC_wt {env : VEnv} (henv : env.WF) {Us : List Name} :
    ∀ {Δ₁ : VLCtx} {e : Expr} {t : LBTerm}, Erases env Us Δ₁ e t →
      ∀ {Δ₂ : VLCtx}, VLCtx.IsDefEq env Us.length Δ₁ Δ₂ → VLCtx.WF env Us.length Δ₁ →
        ∀ {ve : VExpr}, TrExprS env Us Δ₁ e ve → Erases env Us Δ₂ e t := by
  intro Δ₁ e t her
  induction her with
  | box htrb herb =>
      intro Δ₂ hΔ hWF ve htr
      obtain ⟨w, htrw, hdw⟩ := TrExprS.defeqDFC' henv hΔ htrb
      have her₂ : Erasable env Us.length Δ₂.toCtx _ :=
        Erasable.defeqDFC henv.ordered hΔ.defeqCtx herb
      exact .box htrw (Erasable.defeq henv (hΔ.symm henv).wf.toCtx (VEnv.IsDefEqU.symm hdw) her₂)
  | bvar hf =>
      intro Δ₂ hΔ hWF ve htr
      obtain ⟨_, _, h₂⟩ := hΔ.find?_defeqDFC hf
      exact .bvar h₂
  | fvar hf =>
      intro Δ₂ hΔ hWF ve htr
      obtain ⟨_, _, h₂⟩ := hΔ.find?_defeqDFC hf
      exact .fvar h₂
  | const hc => intro Δ₂ hΔ hWF ve htr; exact .const hc
  | app _ _ ihf iha =>
      intro Δ₂ hΔ hWF ve htr
      cases htr with
      | app _ _ s1 s2 => exact .app (ihf hΔ hWF s1) (iha hΔ hWF s2)
  | lam hty hb ihb =>
      intro Δ₂ hΔ hWF ve htr
      cases htr with
      | lam h1 s1 s2 =>
          have hΓ₁ := hWF.toCtx
          obtain ⟨u, h1'⟩ := h1
          have hdty := VEnv.IsDefEqU.of_l henv hΓ₁
            (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hWF) s1 hty) h1'
          have hWF' : VLCtx.WF env Us.length ((none, .vlam _) :: _) :=
            ⟨hWF, nofun, ⟨u, hdty.hasType.2⟩⟩
          obtain ⟨bv', s2'⟩ :=
            s2.defeqDFC henv
              (VLCtx.IsDefEq.cons (.refl henv.ordered hWF) (ofv := none) nofun (.vlam hdty))
          obtain ⟨ty₂, htrty₂, _⟩ := TrExprS.defeqDFC' henv hΔ hty
          have hdty₂ := VEnv.IsDefEqU.of_l henv hΓ₁
            (TrExprS.uniq henv hΔ hty htrty₂) hdty.hasType.2
          exact .lam htrty₂ (ihb (hΔ.cons nofun (.vlam hdty₂)) hWF' s2')
  | letE hty hval hv hb ihv ihb =>
      intro Δ₂ hΔ hWF ve htr
      cases htr with
      | letE h1 s1 s2 s3 =>
          have hΓ₁ := hWF.toCtx
          obtain ⟨u, h0⟩ := h1.isType henv hΓ₁
          have hdty := VEnv.IsDefEqU.of_l henv hΓ₁
            (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hWF) s1 hty) h0
          have hdval := VEnv.IsDefEqU.of_l henv hΓ₁
            (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hWF) s2 hval) h1
          have hvalT := (hdval.hasType.2).defeqU_r henv hΓ₁ ⟨_, hdty⟩
          have hWF' : VLCtx.WF env Us.length ((none, .vlet _ _) :: _) := ⟨hWF, nofun, hvalT⟩
          obtain ⟨bv', s3'⟩ :=
            s3.defeqDFC henv
              (VLCtx.IsDefEq.cons (.refl henv.ordered hWF) (ofv := none) nofun
                (.vlet hdval hdty))
          obtain ⟨ty₂, htrty₂, _⟩ := TrExprS.defeqDFC' henv hΔ hty
          obtain ⟨val₂, htrval₂, _⟩ := TrExprS.defeqDFC' henv hΔ hval
          have hdty₂ := VEnv.IsDefEqU.of_l henv hΓ₁
            (TrExprS.uniq henv hΔ hty htrty₂) hdty.hasType.2
          have hdval₂ := VEnv.IsDefEqU.of_l henv hΓ₁
            (TrExprS.uniq henv hΔ hval htrval₂) hvalT
          exact .letE htrty₂ htrval₂ (ihv hΔ hWF hval)
            (ihb (hΔ.cons nofun (.vlet hdval₂ hdty₂)) hWF' s3')
  | proj hs hi _ ihd =>
      intro Δ₂ hΔ hWF ve htr
      cases htr with
      | proj s1 _ => exact .proj hs hi (ihd hΔ hWF s1)
  | lit hcl _ ih =>
      intro Δ₂ hΔ hWF ve htr
      cases htr with
      | lit _ s1 => exact .lit hcl (ih hΔ hWF s1)
  | mdata _ ih =>
      intro Δ₂ hΔ hWF ve htr
      cases htr with
      | mdata s1 => exact .mdata (ih hΔ hWF s1)

/-- A `VLCtx.InstLet` witness yields the de Bruijn weakening of the substitutee's context
`Δ₀` into the context the let entry is removed from, which carries `dk` binders above it. -/
theorem instLet_toBVLift {Δ₀ Δ₁ Δ : VLCtx} {e₀' A₀ : VExpr} {dk k : Nat}
    (W : VLCtx.InstLet Δ₀ e₀' A₀ dk k Δ₁ Δ) : VLCtx.BVLift Δ₀ Δ dk 0 k 0 := by
  induction W with
  | zero => exact .refl
  | succ _ ih => exact ih.skip _

/-- A bvar below the let keeps its index and stays bound. Only existence is claimed, which
is all `Erases.bvar` asks for. -/
theorem instLet_find?_lt {Δ₀ Δ₁ Δ : VLCtx} {e₀' A₀ : VExpr} {dk k : Nat}
    (W : VLCtx.InstLet Δ₀ e₀' A₀ dk k Δ₁ Δ) :
    ∀ {i : Nat}, i < dk → (∃ p, Δ₁.find? (.inl i) = some p) →
      ∃ p, Δ.find? (.inl i) = some p := by
  induction W with
  | zero => intro i h; omega
  | @succ dk k Γ Γ' d _ ih =>
    rintro (_ | i) hlt ⟨p, H⟩
    · exact ⟨_, rfl⟩
    · simp only [VLCtx.find?, VLCtx.next, Option.bind_eq_bind] at H
      have hsome : ∃ p, Γ.find? (.inl i) = some p := by
        cases hf : Γ.find? (.inl i) with
        | none => rw [hf] at H; simp at H
        | some q => exact ⟨q, rfl⟩
      obtain ⟨⟨qe, qA⟩, h₂⟩ := ih (by omega) hsome
      exact ⟨(qe.liftN d.depth, qA.liftN d.depth), by simp [VLCtx.find?, VLCtx.next, h₂]⟩

/-- A bvar above the let drops by one and stays bound: the entry it pointed past is the one
instantiation removes. -/
theorem instLet_find?_gt {Δ₀ Δ₁ Δ : VLCtx} {e₀' A₀ : VExpr} {dk k : Nat}
    (W : VLCtx.InstLet Δ₀ e₀' A₀ dk k Δ₁ Δ) :
    ∀ {i : Nat}, dk < i → (∃ p, Δ₁.find? (.inl i) = some p) →
      ∃ p, Δ.find? (.inl (i - 1)) = some p := by
  induction W with
  | zero =>
    rintro (_ | i) hgt ⟨p, H⟩
    · omega
    · simp only [VLCtx.find?, VLCtx.next, Option.bind_eq_bind] at H
      cases hf : Δ₀.find? (.inl i) with
      | none => rw [hf] at H; simp at H
      | some q => exact ⟨q, hf⟩
  | @succ dk k Γ Γ' d _ ih =>
    rintro (_ | i) hgt ⟨p, H⟩
    · omega
    · simp only [VLCtx.find?, VLCtx.next, Option.bind_eq_bind] at H
      have hsome : ∃ p, Γ.find? (.inl i) = some p := by
        cases hf : Γ.find? (.inl i) with
        | none => rw [hf] at H; simp at H
        | some q => exact ⟨q, rfl⟩
      obtain ⟨⟨qe, qA⟩, h₂⟩ := ih (by omega) hsome
      obtain _ | m := i
      · omega
      · simp only [Nat.add_sub_cancel] at h₂ ⊢
        exact ⟨(qe.liftN d.depth, qA.liftN d.depth), by simp [VLCtx.find?, VLCtx.next, h₂]⟩

/-- A free variable's lookup survives instantiation of a let entry: `VLCtx.InstLet` touches
no fvar-tagged entry. -/
theorem instLet_find?_fvar {Δ₀ Δ₁ Δ : VLCtx} {e₀' A₀ : VExpr} {dk k : Nat}
    (W : VLCtx.InstLet Δ₀ e₀' A₀ dk k Δ₁ Δ) :
    ∀ {x : FVarId}, (∃ p, Δ₁.find? (.inr x) = some p) →
      ∃ p, Δ.find? (.inr x) = some p := by
  induction W with
  | zero =>
    rintro x ⟨p, H⟩
    simp only [VLCtx.find?, VLCtx.next, Option.bind_eq_bind] at H
    cases hf : Δ₀.find? (.inr x) with
    | none => rw [hf] at H; simp at H
    | some q => exact ⟨q, rfl⟩
  | @succ dk k Γ Γ' d _ ih =>
    rintro x ⟨p, H⟩
    simp only [VLCtx.find?, VLCtx.next, Option.bind_eq_bind] at H
    have hsome : ∃ p, Γ.find? (.inr x) = some p := by
      cases hf : Γ.find? (.inr x) with
      | none => rw [hf] at H; simp at H
      | some q => exact ⟨q, rfl⟩
    obtain ⟨⟨qe, qA⟩, h₂⟩ := ih hsome
    exact ⟨(qe.liftN d.depth, qA.liftN d.depth), by simp [VLCtx.find?, VLCtx.next, h₂]⟩

/--
Erasure commutes with instantiating a `.vlet` entry away: source `Expr.instantiate1'` matches
target `LBTerm.subst` under a `VLCtx.InstLet`, when the substitutee's translation is the
entry's recorded value.

`box`, `lam` and `letE` discharge their lean4lean premises with `TrExprS.instN_let`; the
`Erasable` witness needs no move at all, since a `.vlet` entry contributes nothing to the
pure typing context. The `bvar i = dk` case is the substitutee's own derivation, lifted by
`erases_shift` along `instLet_toBVLift`.
-/
theorem erases_subst_let {env : VEnv} (henv : env.Ordered) {Us : List Name}
    {Δ₀ : VLCtx} {e₀ : Expr} {e₀' A₀ : VExpr} {s' : LBTerm}
    (ht₀ : TrExprS env Us Δ₀ e₀ e₀')
    (h₀ : Erases env Us Δ₀ e₀ s')
    {Δ₁ Δ : VLCtx} {dk k : Nat} (W : VLCtx.InstLet Δ₀ e₀' A₀ dk k Δ₁ Δ)
    {e : Expr} {t : LBTerm} (h : Erases env Us Δ₁ e t) :
    Erases env Us Δ (e.instantiate1' e₀ dk) (LBTerm.subst s' dk t) := by
  induction h generalizing Δ dk k with
  | box htr her => exact .box (TrExprS.instN_let henv ht₀ W htr) (W.toCtx ▸ her)
  | lit hcl _ ih =>
    refine .lit hcl (Expr.instantiate1'_eq_self ?_ ▸ ih W :)
    exact Closed.toConstructor.looseBVarRange_le
  | @bvar _ i _ _ hf =>
    simp only [Expr.instantiate1', LBTerm.subst]
    split <;> rename_i hlt
    · obtain ⟨⟨_, _⟩, h⟩ := instLet_find?_lt W hlt ⟨_, hf⟩
      exact .bvar h
    · split <;> rename_i heq
      · exact heq ▸ erases_shift henv (instLet_toBVLift W) h₀
      · obtain ⟨⟨_, _⟩, h⟩ := instLet_find?_gt W (by omega) ⟨_, hf⟩
        exact .bvar h
  | fvar hf => obtain ⟨⟨_, _⟩, h⟩ := instLet_find?_fvar W ⟨_, hf⟩; exact .fvar h
  | const hc => exact .const hc
  | app _ _ ihf iha => exact .app (ihf W) (iha W)
  | lam hty _ ihb =>
    exact .lam (TrExprS.instN_let henv ht₀ W hty) (ihb (W.succ (d := .vlam _)))
  | letE hty hval _ _ ihv ihb =>
    exact .letE (TrExprS.instN_let henv ht₀ W hty) (TrExprS.instN_let henv ht₀ W hval)
      (ihv W) (ihb (W.succ (d := .vlet ..)))
  | proj hs hi _ ihd => exact .proj hs hi (ihd W)
  | mdata _ ih => exact .mdata (ih W)

/-! ## The δ arm's environment premise -/

/--
What the δ arm owes the target: the specification environment declares, for every constant
the compiler-body table defines, a body that erases the tabled body at the level
instantiation the step takes.

Constant bodies are closed, so the erasure is asked in every context. This is the premise
`ErasesEnv` cannot supply: its `deps` clause is keyed on one program and does not propagate
to the subterms an induction visits, and `ErasesDecl.defn`'s existentially bound level
scope is not the `ups` of `SEval.deltaC`.
-/
def DeltaAgrees (env : VEnv) (bo : Name → Option Expr) (Us : List Name)
    (Γ : GlobalDeclarations) : Prop :=
  ∀ c b us ups, bo c = some b →
    ∃ b₀, LBTerm.envLookup Γ (toKername c) = some (.constantDecl ⟨some b₀⟩) ∧
      ∀ Δ : VLCtx, Erases env Us Δ (b.instantiateLevelParams ups us) b₀

/-! ## T5 on the tabled fragment -/

/-- **Forward simulation at a context.** `erases_correct_tabled` is this at `Δ = []`, where
`VLCtx.WF` is `True`. -/
theorem erases_correct_tabled_ctx {env : VEnv} (henv : env.WF) {Us : List Name} {Δ : VLCtx}
    (hΔ : VLCtx.WF env Us.length Δ) {bo : Name → Option Expr} {fl : SEvalFlags}
    {Γ : GlobalDeclarations} (hbo : TabledConstants env bo) (hδ : DeltaAgrees env bo Us Γ)
    {e v : Expr} {ve : VExpr} {t : LBTerm}
    (htr : TrExprS env Us Δ e ve) (her : Erases env Us Δ e t)
    (hev : SEval env bo Us fl Δ e v) :
    ∃ v', Erases env Us Δ v v' ∧ WcbvEval Γ eraseFlags t v' := by
  induction hev generalizing ve t with
  | lam n ty bd bi =>
      rcases Erases.lam_inv her with ⟨hbw, rfl⟩ | ⟨ty₂, b', hty₂, hb', rfl⟩
      · exact erases_correct_box henv hΔ (bo := bo) (fl := fl) htr hbw (.lam n ty bd bi)
      · exact ⟨_, her, .lam _ _⟩
  | @beta f a n ty bd bi av r hfl' hf ha hbody ihf iha ihbody =>
      rcases Erases.app_inv her with ⟨hbw, rfl⟩ | ⟨f', a', hf', ha', rfl⟩
      · exact erases_correct_box henv hΔ htr hbw (.beta hfl' hf ha hbody)
      · cases htr with
        | @app fve A B ave _ _ _ hTf hTa htrf htra =>
          obtain ⟨fv', herfv, hEf⟩ := ihf htrf hf'
          obtain ⟨av', herav, hEa⟩ := iha htra ha'
          obtain ⟨fvv, htrfvv, hfdef⟩ := SEval.defeq henv hΔ htrf hf
          rcases Erases.lam_inv herfv with ⟨⟨we, htrw, herw⟩, rfl⟩ | ⟨ty₂, b'', hty₂, hb'', rfl⟩
          · obtain ⟨rv, htrr, hrdef⟩ :=
              SEval.defeq henv hΔ (.app hTf hTa htrf htra) (.beta hfl' hf ha hbody)
            have hferase : Erasable env Us.length Δ.toCtx fve :=
              (herw.defeq henv hΔ.toCtx
                  (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrw htrfvv)).defeq
                henv hΔ.toCtx (VEnv.IsDefEqU.symm hfdef)
            exact ⟨.box, .box htrr
              ((hferase.app henv hΔ.toCtx hTf hTa).defeq henv hΔ.toCtx hrdef),
              .app_box hEf hEa⟩
          · cases htrfvv with
            | @lam ty' _ _ _ body' _ _ hty' htrty htrb =>
              obtain ⟨avv, htrav, hadef⟩ := SEval.defeq henv hΔ htra ha
              have hΔ' : VLCtx.WF env Us.length ((none, .vlam ty') :: Δ) :=
                ⟨hΔ, nofun, hty'⟩
              obtain ⟨B'', hbodyT⟩ := htrb.wf henv.ordered hΔ'
              have hAty' : env.IsDefEqU Us.length Δ.toCtx A ty' := by
                obtain ⟨u, hty'sort⟩ := hty'
                have lamT1 : env.HasType Us.length Δ.toCtx (.lam ty' body')
                    (.forallE ty' B'') := VEnv.HasType.lam hty'sort hbodyT
                have lamT2 : env.HasType Us.length Δ.toCtx (.lam ty' body')
                    (.forallE A B) := hTf.defeqU_l henv hΔ.toCtx hfdef
                obtain ⟨⟨_, h⟩, _⟩ := VEnv.IsDefEqU.forallE_inv henv hΔ.toCtx
                  (VEnv.IsDefEq.uniqU henv hΔ.toCtx lamT2 lamT1)
                exact ⟨_, h⟩
              have havT : env.HasType Us.length Δ.toCtx avv ty' :=
                (hTa.defeqU_l henv hΔ.toCtx hadef).defeqU_r henv hΔ.toCtx hAty'
              have havTE : env.HasType Us.length Δ.toCtx avv ty₂ :=
                havT.defeqU_r henv hΔ.toCtx (VEnv.IsDefEqU.symm
                  (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) hty₂ htrty))
              obtain ⟨rv', herr, hEr⟩ := ihbody
                (TrExprS.inst henv.ordered havT htrb htrav)
                (erases_subst henv.ordered htrav havTE herav .zero hb'')
              exact ⟨rv', herr, .beta hEf hEa hEr⟩
  | @zeta n ty val bd nd vv r hfl' hvalEv hbodyEv ihvalEv ihbodyEv =>
      rcases Erases.letE_inv her with
        ⟨hbw, rfl⟩ | ⟨ty', val', v', b', htrtyE, htrvalE, herv, herb, rfl⟩
      · exact erases_correct_box henv hΔ htr hbw (.zeta hfl' hvalEv hbodyEv)
      · cases htr with
        | letE hValT htrty htrval htrb =>
          have hΓ := hΔ.toCtx
          obtain ⟨u, h0⟩ := hValT.isType henv hΓ
          have hdty := VEnv.IsDefEqU.of_l henv hΓ
            (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrty htrtyE) h0
          have hdval := VEnv.IsDefEqU.of_l henv hΓ
            (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htrval htrvalE) hValT
          have hvalT' := (hdval.hasType.2).defeqU_r henv hΓ ⟨_, hdty⟩
          have hWFlet : VLCtx.WF env Us.length ((none, .vlet _ _) :: Δ) := ⟨hΔ, nofun, hvalT'⟩
          obtain ⟨bv, htrbE⟩ :=
            htrb.defeqDFC henv
              (VLCtx.IsDefEq.cons (.refl henv.ordered hΔ) (ofv := none) nofun
                (.vlet hdval hdty))
          obtain ⟨vv', hervv, hEv⟩ := ihvalEv htrvalE herv
          obtain ⟨vvv, htrvv, hdefv⟩ := SEval.defeq henv hΔ htrvalE hvalEv
          have hswap : VLCtx.IsDefEq env Us.length ((none, .vlet _ val') :: Δ)
              ((none, .vlet _ vvv) :: Δ) :=
            VLCtx.IsDefEq.cons (.refl henv.ordered hΔ) (ofv := none) nofun
              (.vlet (VEnv.IsDefEqU.of_l henv hΓ hdefv hvalT') hdty.hasType.2)
          obtain ⟨bv₂, htrb₂⟩ := htrbE.defeqDFC henv hswap
          obtain ⟨rv, herr, hEr⟩ :=
            ihbodyEv (TrExprS.inst_let henv.ordered htrb₂ htrvv)
              (erases_subst_let henv.ordered htrvv hervv .zero
                (Erases.defeqDFC_wt henv herb hswap hWFlet htrbE))
          exact ⟨rv, herr, .zeta hEv hEr⟩
  | @deltaC c us ups args argsv b b' vres hfl' hbd hinst hlen hargs hdef hcont ihargs ihcont =>
      subst hinst
      have hargEvalMem : ∀ a ∈ args, ∀ {s : LBTerm}, Erases env Us Δ a s →
          ∃ x, WcbvEval Γ eraseFlags s x := by
        intro a ha s hs
        obtain ⟨i, hi, hia⟩ := List.getElem_of_mem ha
        have hia' : args[i]! = a := by rw [getElem!_pos args i hi]; exact hia
        obtain ⟨w, htrw⟩ := trExprS_spine_mem args htr a ha
        have h1 : TrExprS env Us Δ args[i]! w := by rw [hia']; exact htrw
        have h2 : Erases env Us Δ args[i]! s := by rw [hia']; exact hs
        obtain ⟨x, _, hx⟩ := ihargs i hi h1 h2
        exact ⟨x, hx⟩
      rcases erases_mkApps_inv args her with
        ⟨th, ts, hth, hts, rfl⟩ | ⟨pre, suf, ts, hsplit, hbw, hts, rfl⟩
      · rcases Erases.const_inv hth with ⟨hbw, rfl⟩ | ⟨⟨ci, hc⟩, rfl⟩
        · refine erases_correct_boxSpine (pre := []) (suf := args) henv hΔ htr hbw
            (fun s hs => ?_) (.deltaC hfl' hbd rfl hlen hargs hdef hcont)
          obtain ⟨a, ha, hEr⟩ := forall₂_mem_right hts s hs
          exact hargEvalMem a ha hEr
        · obtain ⟨b₀, hlook, herb⟩ := hδ c b us ups hbd
          have hlents : args.length = ts.length := hts.length_eq
          have hstep : ∀ i, i < argsv.length →
              ∃ x, Erases env Us Δ argsv[i]! x ∧ WcbvEval Γ eraseFlags ts[i]! x := by
            intro i hi
            have hi' : i < args.length := by rw [hlen] at hi; exact hi
            obtain ⟨w, htrw⟩ := trExprS_spine_mem args htr args[i]!
              (by rw [getElem!_pos args i hi']; exact List.getElem_mem hi')
            exact ihargs i hi' htrw (forall₂_getElem! hts i hi')
          obtain ⟨tav, hav1, hav2⟩ :=
            forall₂_split (forall₂_of_getElem! (hlen.trans hlents) hstep)
          obtain ⟨_, _, _, htrcont, _⟩ := hdef
          obtain ⟨v', herv, hEv⟩ := ihcont htrcont (Erases.mkApps_forall₂ hav1 (herb Δ))
          obtain ⟨bv, hbv⟩ := WcbvEval.head_value_of_mkApps tav hEv
          refine ⟨v', herv, WcbvEval.mkApps_congr ?_ hbv (.delta hlook hbv) hEv⟩
          refine forall₂_of_getElem! hav2.length_eq.symm (fun i hi => ?_)
          have hx := forall₂_getElem! hav2 i (by rw [hav2.length_eq]; exact hi)
          exact ⟨tav[i]!, value_final (eval_to_value hx), hx⟩
      · subst hsplit
        refine erases_correct_boxSpine henv hΔ htr hbw (fun s hs => ?_)
          (.deltaC hfl' hbd rfl hlen hargs hdef hcont)
        obtain ⟨a, ha, hEr⟩ := forall₂_mem_right hts s hs
        exact hargEvalMem a (List.mem_append_right _ ha) hEr
  | @ctorVal cn us args argsv hnb hlen hargs ihargs =>
      exact (SEval.no_constHead_value henv hΔ hbo htr (.ctorVal hnb hlen hargs)).elim
  | @iota con us cus pre minors discr ctor cargs np cidx r hfl' hdiscr hidx hdef hcont
      ihdiscr ihcont =>
      obtain ⟨w, htrd⟩ := trExprS_spine_mem (pre ++ discr :: minors) htr discr
        (List.mem_append_right _ (List.mem_cons_self ..))
      exact (SEval.no_constHead_value henv hΔ hbo htrd hdiscr).elim
  | @proj S i discr ctor cus cargs np r hfl' hdiscr hlt hdef hcont ihdiscr ihcont =>
      cases htr with
      | proj htrd _ => exact (SEval.no_constHead_value henv hΔ hbo htrd hdiscr).elim
  | @lit l r hfl' hlit ih =>
      rcases Erases.lit_inv her with ⟨hbw, rfl⟩ | ⟨hcl, her'⟩
      · exact erases_correct_box henv hΔ htr hbw (.lit hfl' hlit)
      · cases htr with | lit _ htrC => exact ih htrC her'

/-- **T5 on the tabled fragment**, at the empty context: a source term that evaluates to
`v` erases to a λ□ term that evaluates to an erasure of `v`. -/
theorem erases_correct_tabled {env : VEnv} (henv : env.WF) {Us : List Name}
    {bo : Name → Option Expr} {fl : SEvalFlags} {Γ : GlobalDeclarations}
    {e v : Expr} {ve : VExpr} {t : LBTerm}
    (hbo : TabledConstants env bo) (hδ : DeltaAgrees env bo Us Γ)
    (hwt : TrExprS env Us [] e ve) (hev : SEval env bo Us fl [] e v)
    (her : Erases env Us [] e t) :
    ∃ v', Erases env Us [] v v' ∧ WcbvEval Γ eraseFlags t v' :=
  erases_correct_tabled_ctx (Δ := []) henv trivial hbo hδ hwt her hev

/-! ## Why the guards are there

Two refutations of the unguarded statement, one per shape of body-less constant the
specification environment can hold, and one showing that the design's environment
hypothesis does not replace `DeltaAgrees`.
-/

/-- The one-entry specification environment of a body-less constant. -/
def axSpecEnv (c : Name) : GlobalDeclarations := [(toKername c, .constantDecl ⟨none⟩)]

/-- A body-less constant is **stuck**: `WcbvEval` moves a `.const` only by δ. -/
theorem wcbvEval_bodyless_stuck {Γ : GlobalDeclarations} {fl : WcbvFlags} {kn : Kername}
    (h : LBTerm.envLookup Γ kn = some (.constantDecl ⟨none⟩)) :
    ¬ ∃ w, WcbvEval Γ fl (.const kn) w := by
  rintro ⟨w, hev⟩
  cases hev with | delta hl _ => rw [h] at hl; simp at hl

/--
**T5 is false without `TabledConstants`, at an axiom.** Every hypothesis of the statement
holds at a declared constant the table does not define — the source spine is a value by
`SEval.ctorVal`, it erases to its kername, and the one-entry environment is an `ErasesEnv`
for it — while the conclusion fails: the target is stuck.
-/
theorem erases_correct_needs_tabled {env : VEnv} {bo : Name → Option Expr} {Us : List Name}
    {c : Name} {us : List Level} {ci : VConstant} {fl : SEvalFlags}
    (hc : env.constants c = some ci) (hno : bo c = none) (hpat : IotaInert env c) :
    SEval env bo Us fl [] (.const c us) (.const c us) ∧
      Erases env Us [] (.const c us) (.const (toKername c)) ∧
      ErasesEnv env bo (axSpecEnv c) (.const (toKername c)) ∧
      ¬ ∃ v', Erases env Us [] (.const c us) v' ∧
          WcbvEval (axSpecEnv c) eraseFlags (.const (toKername c)) v' := by
  have hlook : LBTerm.envLookup (axSpecEnv c) (toKername c)
      = some (.constantDecl ⟨none⟩) := envLookup_cons_self
  refine ⟨?_, .const hc, ?_, ?_⟩
  · have := SEval.ctorVal (env := env) (bo := bo) (Us := Us) (fl := fl) (Δ := [])
      (cn := c) (us := us) (args := []) (argsv := []) hno rfl (fun i hi => absurd hi (by simp))
    simpa using this
  · refine .mk (by simp [axSpecEnv]) (fun kn d hd => ?_) (fun kn hr => ?_)
    · have hmem := envLookup_mem hd
      simp only [axSpecEnv, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
      obtain ⟨rfl, rfl⟩ := hmem
      exact .ax hc hno hpat
    · have h1 : reachRefs (axSpecEnv c) (.const (toKername c)) (axSpecEnv c).length
          = [toKername c] := by
        show expandRefs (axSpecEnv c) (reachRefs (axSpecEnv c) (.const (toKername c)) 0) = _
        show expandRefs (axSpecEnv c) [toKername c] = _
        unfold expandRefs
        rw [List.foldl_cons, List.foldl_nil, hlook]
      unfold ReachableFrom kernameElem at hr
      rw [h1] at hr
      simp only [List.any_cons, List.any_nil, Bool.or_false] at hr
      rw [Kername.eq_of_beq hr, hlook]
      rfl
  · rintro ⟨v', -, hev⟩
    exact wcbvEval_bodyless_stuck hlook ⟨v', hev⟩

/-- No `Erases` derivation sends a constant to a constructor node: the ten rules emit no
`.construct`. -/
theorem erases_const_ne_construct {env : VEnv} {Us : List Name} {Δ : VLCtx} {c : Name}
    {us : List Level} {iid : InductiveId} {k : Nat} {args : List LBTerm} :
    ¬ Erases env Us Δ (.const c us) (.construct iid k args) := by
  intro h
  rcases Erases.const_inv h with ⟨_, hb⟩ | ⟨_, hb⟩ <;> exact LBTerm.noConfusion hb

/--
**T5 is false without `TabledConstants`, at a constructor.** `ErasesDecl.ctor` gives a
constructor constant the body `.construct iid k []`, so the target's value for its kername
is that node — and `Erases` relates the source constant only to `.box` or to its kername,
never to a constructor node. The saturation step is the pass layer's, not `Erases`'.
-/
theorem erases_correct_needs_tabled_ctor {env : VEnv} {Us : List Name}
    {Γ : GlobalDeclarations} {c : Name} {us : List Level} {iid : InductiveId} {k ar : Nat}
    (hlook : LBTerm.envLookup Γ (toKername c)
      = some (.constantDecl ⟨some (.construct iid k [])⟩))
    (har : constructorArity Γ iid k = some ar) :
    WcbvEval Γ eraseFlags (.const (toKername c)) (.construct iid k []) ∧
      ¬ ∃ v', Erases env Us [] (.const c us) v' ∧
          WcbvEval Γ eraseFlags (.const (toKername c)) v' := by
  have hval : WcbvEval Γ eraseFlags (.const (toKername c)) (.construct iid k []) :=
    .delta hlook (.construct_atom rfl har)
  refine ⟨hval, ?_⟩
  rintro ⟨v', her, hev⟩
  exact erases_const_ne_construct (eval_deterministic hev hval ▸ her)

/--
**`ErasesEnv` does not deliver the δ arm's premise.** It is keyed on one program: at a
program that reaches no kername it holds of the empty environment, whatever the
compiler-body table defines, while `DeltaAgrees` asks the environment about every tabled
constant.
-/
theorem erasesEnv_not_deltaAgrees {env : VEnv} {Us : List Name} {c : Name} {b : Expr} :
    ErasesEnv env (fun n => if n = c then some b else none) [] .box ∧
      ¬ DeltaAgrees env (fun n => if n = c then some b else none) Us [] := by
  refine ⟨.mk (by simp) (fun kn d hd => absurd hd (by simp [LBTerm.envLookup]))
    (fun kn hr => absurd hr (by simp [ReachableFrom, reachRefs, kernameElem, constRefs])), ?_⟩
  intro h
  obtain ⟨b₀, hlook, -⟩ := h c b [] [] (by simp)
  simp [LBTerm.envLookup] at hlook

/-! ## Non-vacuity

The guards and the conclusion are jointly inhabited: a β-redex over `Sort 0` at the empty
environment, where `TabledConstants` and `DeltaAgrees` hold because there is nothing to
table.
-/

/-- `Sort 0`, as a `VExpr`. -/
def vProp : VExpr := .sort .zero

/-- `Sort 0 → Sort 0`, as a `VExpr`. -/
def vArrow : VExpr := .forallE vProp vProp

theorem hasType_vProp {Γ : List VExpr} :
    VEnv.empty.HasType 0 Γ vProp (.sort (.succ .zero)) := .sortDF trivial trivial (by rfl)

theorem isType_vProp {Γ : List VExpr} : VEnv.empty.IsType 0 Γ vProp := ⟨_, hasType_vProp⟩

theorem hasType_vArrow {Γ : List VExpr} :
    VEnv.empty.HasType 0 Γ vArrow (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .forallEDF hasType_vProp hasType_vProp

theorem isType_vArrow {Γ : List VExpr} : VEnv.empty.IsType 0 Γ vArrow := ⟨_, hasType_vArrow⟩

/-- The redex's argument, `fun y : Sort 0 => y`. -/
def idArgSrc : Expr := .lam `y (.sort .zero) (.bvar 0) .default

/-- The redex's function, `fun f : Sort 0 → Sort 0 => f`. -/
def idFunSrc : Expr :=
  .lam `f (.forallE `y (.sort .zero) (.sort .zero) .default) (.bvar 0) .default

/-- The β-redex `(fun f : Sort 0 → Sort 0 => f) (fun y : Sort 0 => y)`. -/
def betaRedexSrc : Expr := .app idFunSrc idArgSrc

/-- The redex's λ□ image; the binder names are the source names, as `Erases.lam` records
them. -/
def betaRedexLB : LBTerm :=
  .app (.lambda (.named (`f).toString) (.bvar 0)) (.lambda (.named (`y).toString) (.bvar 0))

theorem trExprS_vProp {Δ : VLCtx} : TrExprS VEnv.empty [] Δ (.sort .zero) vProp := .sort rfl

theorem trExprS_arrowSrc {Δ : VLCtx} :
    TrExprS VEnv.empty [] Δ (.forallE `y (.sort .zero) (.sort .zero) .default) vArrow :=
  .forallE isType_vProp isType_vProp trExprS_vProp trExprS_vProp

theorem trExprS_idArg {Δ : VLCtx} : TrExprS VEnv.empty [] Δ idArgSrc (.lam vProp (.bvar 0)) :=
  .lam isType_vProp trExprS_vProp (.bvar rfl)

theorem trExprS_idFun {Δ : VLCtx} : TrExprS VEnv.empty [] Δ idFunSrc (.lam vArrow (.bvar 0)) :=
  .lam isType_vArrow trExprS_arrowSrc (.bvar rfl)

theorem hasType_idArg {Γ : List VExpr} :
    VEnv.empty.HasType 0 Γ (.lam vProp (.bvar 0)) vArrow :=
  .lamDF hasType_vProp (.bvar .zero)

theorem hasType_idFun {Γ : List VExpr} :
    VEnv.empty.HasType 0 Γ (.lam vArrow (.bvar 0)) (.forallE vArrow vArrow) :=
  .lamDF hasType_vArrow (.bvar .zero)

theorem trExprS_betaRedex :
    TrExprS VEnv.empty [] [] betaRedexSrc (.app (.lam vArrow (.bvar 0)) (.lam vProp (.bvar 0))) :=
  .app hasType_idFun hasType_idArg trExprS_idFun trExprS_idArg

theorem erases_betaRedex : Erases VEnv.empty [] [] betaRedexSrc betaRedexLB := by
  unfold betaRedexSrc betaRedexLB idFunSrc idArgSrc
  exact .app (.lam (n := `f) trExprS_arrowSrc (.bvar rfl))
    (.lam (n := `y) trExprS_vProp (.bvar rfl))

theorem seval_betaRedex :
    SEval VEnv.empty (fun _ => none) [] w2Flags [] betaRedexSrc idArgSrc := by
  refine .beta rfl (.lam ..) (.lam ..) ?_
  show SEval _ _ _ _ _ (Expr.instantiate1' (.bvar 0) idArgSrc 0) _
  simp only [Expr.instantiate1', Expr.liftLooseBVars_zero, Nat.lt_irrefl, if_false]
  exact .lam ..

/-- Every constant of `VEnv.empty` is tabled, vacuously. -/
theorem tabledConstants_empty (bo : Name → Option Expr) : TabledConstants VEnv.empty bo :=
  fun _ _ h => absurd h (by simp [VEnv.empty])

/-- An empty compiler-body table agrees with every specification environment. -/
theorem deltaAgrees_none {env : VEnv} {Us : List Name} {Γ : GlobalDeclarations} :
    DeltaAgrees env (fun _ => none) Us Γ := fun _ _ _ _ h => absurd h (by simp)

/-- **The simulation fires at β.** -/
theorem erases_correct_tabled_fires :
    ∃ v', Erases VEnv.empty [] [] idArgSrc v' ∧ WcbvEval [] eraseFlags betaRedexLB v' :=
  erases_correct_tabled ⟨[], .empty⟩ (tabledConstants_empty _) deltaAgrees_none
    trExprS_betaRedex seval_betaRedex erases_betaRedex

/-- `let x : Sort 0 → Sort 0 := fun y : Sort 0 => y; x`, the ζ-redex. -/
def letZetaSrc : Expr :=
  .letE `x (.forallE `y (.sort .zero) (.sort .zero) .default) idArgSrc (.bvar 0) false

/-- The ζ-redex's λ□ image. -/
def letZetaLB : LBTerm :=
  .letIn (.named (`x).toString) (.lambda (.named (`y).toString) (.bvar 0)) (.bvar 0)

theorem trExprS_letZeta : TrExprS VEnv.empty [] [] letZetaSrc (.lam vProp (.bvar 0)) :=
  .letE hasType_idArg trExprS_arrowSrc trExprS_idArg (.bvar rfl)

theorem erases_letZeta : Erases VEnv.empty [] [] letZetaSrc letZetaLB := by
  unfold letZetaSrc letZetaLB idArgSrc
  exact .letE trExprS_arrowSrc trExprS_idArg (.lam (n := `y) trExprS_vProp (.bvar rfl))
    (.bvar rfl)

theorem seval_letZeta :
    SEval VEnv.empty (fun _ => none) [] w2Flags [] letZetaSrc idArgSrc := by
  refine .zeta rfl (.lam ..) ?_
  show SEval _ _ _ _ _ (Expr.instantiate1' (.bvar 0) idArgSrc 0) _
  simp only [Expr.instantiate1', Expr.liftLooseBVars_zero, Nat.lt_irrefl, if_false]
  exact .lam ..

/-- **The simulation fires at ζ**, the arm that needs the `.vlet` transport. -/
theorem erases_correct_tabled_fires_zeta :
    ∃ v', Erases VEnv.empty [] [] idArgSrc v' ∧ WcbvEval [] eraseFlags letZetaLB v' :=
  erases_correct_tabled ⟨[], .empty⟩ (tabledConstants_empty _) deltaAgrees_none
    trExprS_letZeta seval_letZeta erases_letZeta

/-! ### A firing δ step

`TabledConstants` is not vacuous at a declared constant: a one-definition environment tables
the definition it declares, and the δ arm fires there, with `DeltaAgrees` discharged at the
erased body.

Discharging `DeltaAgrees` means computing `Expr.instantiateLevelParams`, which core defines
through the kernel-opaque computed field `Expr.data`; the computation goes through
lean4lean's model of it (`Verify/Axioms.lean`). This witness therefore carries that axiom
cluster, and nothing above it does.
-/

namespace DeltaFires

/-- The witness declaration, `f : Sort 0 → Sort 0 := fun y : Sort 0 => y`. -/
def decl : VDefVal where
  name := `f
  uvars := 0
  type := vArrow
  value := .lam vProp (.bvar 0)

/-- `VEnv.empty` extended by that definition, defining equation included. -/
def env : VEnv :=
  ((VEnv.empty.addConst `f decl.toVConstant).getD .empty).addDefEq decl.toDefEq

theorem env_wf : env.WF := ⟨[.def decl], .decl (.def hasType_idArg rfl) .empty⟩

theorem env_constants : env.constants `f = some ⟨0, vArrow⟩ := rfl

theorem empty_le : VEnv.empty ≤ env := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> simp [VEnv.empty] at h

/-- The compiler-body table: `f`'s body, the source term the eraser reads. -/
def table : Name → Option Expr := fun n => if n = `f then some idArgSrc else none

/-- The specification environment: `f`'s kername, with the erased body. -/
def spec : GlobalDeclarations :=
  [(toKername `f, .constantDecl ⟨some (.lambda (.named (`y).toString) (.bvar 0))⟩)]

/-- The one constant the environment declares is tabled. -/
theorem tabled : TabledConstants env table := by
  intro c ci h
  by_cases hc : c = `f
  · simp [table, hc]
  · exact absurd h (by simp [env, VEnv.addConst, VEnv.addDefEq, VEnv.empty, Ne.symm hc])

/-- The tabled body carries no level parameter, so instantiating levels leaves it fixed. -/
theorem instantiateLevelParams_idArgSrc (ups : List Name) (us : List Level) :
    idArgSrc.instantiateLevelParams ups us = idArgSrc := by
  simp [idArgSrc, Expr.instantiateLevelParams_eq, Expr.instantiateLevelParamsCore',
    Level.substParams']

theorem erases_body {Δ : VLCtx} :
    Erases env [] Δ idArgSrc (.lambda (.named (`y).toString) (.bvar 0)) :=
  .lam (n := `y) (.sort rfl) (.bvar rfl)

/-- The specification environment agrees with the table at `f`. -/
theorem agrees : DeltaAgrees env table [] spec := by
  intro c b us ups hb
  have hc : c = `f := by
    by_cases h : c = `f
    · exact h
    · simp [table, h] at hb
  subst hc
  have hb' : idArgSrc = b := by simpa [table] using hb
  subst hb'
  refine ⟨_, envLookup_cons_self, fun Δ => ?_⟩
  rw [instantiateLevelParams_idArgSrc]
  exact erases_body

theorem trExprS_const {Δ : VLCtx} : TrExprS env [] Δ (.const `f []) (.const `f []) :=
  .const env_constants rfl rfl

theorem erases_const : Erases env [] [] (.const `f []) (.const (toKername `f)) :=
  .const env_constants

/-- The environment's own defining equation, at the empty level instantiation. -/
theorem isDefEq_const {Γ : List VExpr} :
    env.IsDefEq 0 Γ (.const `f []) (.lam vProp (.bvar 0)) vArrow :=
  .extra (df := decl.toDefEq) (ls := []) (.inl rfl) (by simp) rfl

/-- One tabled unfolding, at any flag point that enables δ. -/
theorem seval_delta {fl : SEvalFlags} (hfl : fl.delta) :
    SEval env table [] fl [] (.const `f []) idArgSrc := by
  refine SEval.deltaC (args := []) (argsv := []) (b := idArgSrc) (b' := idArgSrc) (ups := [])
    hfl (by simp [table]) rfl rfl (fun i hi => absurd hi (by simp))
    ⟨_, _, trExprS_const, trExprS_idArg.mono empty_le, ⟨_, isDefEq_const⟩⟩ (.lam ..)

/-- **The simulation fires at δ**, under both guards, at a declared and tabled constant. -/
theorem fires :
    ∃ v', Erases env [] [] idArgSrc v' ∧
      WcbvEval spec eraseFlags (.const (toKername `f)) v' :=
  erases_correct_tabled env_wf tabled agrees trExprS_const
    (seval_delta (fl := fullFlags) rfl) erases_const

end DeltaFires

end LeanToLambdaBox
