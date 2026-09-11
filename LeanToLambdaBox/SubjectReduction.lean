import LeanToLambdaBox.SourceEval
import Lean4Lean.Theory.Typing.UniqueTyping
import Lean4Lean.Theory.Typing.Injectivity

/-!
# Subject reduction as definitional equality

The gating fact about `SEval`: if a source term translates to a `VExpr` and it evaluates to
a value, then the value translates too, and the two translations are definitionally equal
in the kernel environment. It is what lets an erasure simulation replace a source term by
its value without leaving the typed world.

The β and ζ arms are proved outright — β from `TrExprS.inst`, lean4lean's
`VEnv.IsDefEq.beta` and type uniqueness; ζ from `TrExpr.inst_let`, at which the `VExpr` side does not move at
all. The δ, ι and projection arms hand back the `StepDefeq` they carry. Constructor-spine
values go through `SEval.defeq_spine`, the abstract-`P` spine schema, which is also what
carries the δ arm from a redex's arguments to their values.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-- The head of a translated application spine itself translates. -/
theorem trExprS_spine_head {env : VEnv} {Us : List Name} {Δ : VLCtx} :
    ∀ (args : List Expr) {head : Expr} {ve : VExpr},
      TrExprS env Us Δ (mkApps head args) ve → ∃ hve, TrExprS env Us Δ head hve
  | [], _, _, htr => ⟨_, htr⟩
  | a :: as, head, ve, htr => by
      rw [mkApps_cons] at htr
      obtain ⟨hve', htr'⟩ := trExprS_spine_head as htr
      cases htr' with
      | app _ _ htrhead _ => exact ⟨_, htrhead⟩

/-- **Subject reduction along an application spine.**

If a head translating to `hve` is definitionally equal to the value head's translation, and
every argument subject-reduces to its value in the sense of `P`, then the whole spine's
translation is definitionally equal to the value spine's.

`P` is abstract so that the schema serves both the constructor-value arm and the δ arm,
whose side condition is stated at the *evaluated* arguments. -/
theorem SEval.defeq_spine {env : VEnv} (henv : env.WF) {Us : List Name}
    {Δ : VLCtx} (hΔ : VLCtx.WF env Us.length Δ)
    (P : Expr → Expr → Prop)
    (hP : ∀ {e v : Expr} {ev : VExpr}, TrExprS env Us Δ e ev → P e v →
      ∃ vv, TrExprS env Us Δ v vv ∧ env.IsDefEqU Us.length Δ.toCtx ev vv) :
    ∀ (n : Nat) (args vs : List Expr) (head head₂ : Expr) (hve hve₂ : VExpr),
      args.length = n → vs.length = n →
      TrExprS env Us Δ head hve → TrExprS env Us Δ head₂ hve₂ →
      env.IsDefEqU Us.length Δ.toCtx hve hve₂ →
      (∀ i (h : i < args.length) (h2 : i < vs.length), P args[i] vs[i]) →
      ∀ {ve : VExpr}, TrExprS env Us Δ (mkApps head args) ve →
        ∃ vve, TrExprS env Us Δ (mkApps head₂ vs) vve ∧
          env.IsDefEqU Us.length Δ.toCtx ve vve := by
  have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro args vs head head₂ hve hve₂ hlenA hlenV hh hh₂ hd hargs ve htr
    rcases List.eq_nil_or_concat args with rfl | ⟨init, last, rfl⟩
    · have : vs = [] := List.eq_nil_of_length_eq_zero (by simp_all)
      subst this
      simp only [mkApps_nil]
      simp only [mkApps_nil] at htr
      exact ⟨hve₂, hh₂,
        VEnv.IsDefEqU.trans henv hΓ (TrExprS.uniq henv
          (VLCtx.IsDefEq.refl henv.ordered hΔ) htr hh) hd⟩
    · rcases List.eq_nil_or_concat vs with rfl | ⟨vinit, vlast, rfl⟩
      · simp [List.concat_eq_append] at hlenA hlenV; omega
      · rw [List.concat_eq_append, List.length_append] at hlenA
        rw [List.concat_eq_append, List.length_append] at hlenV
        simp only [List.length_singleton] at hlenA hlenV
        have hlen : init.length = vinit.length := by omega
        rw [List.concat_eq_append, mkApps_concat] at htr
        simp only [List.concat_eq_append] at hargs
        cases htr with
        | @app fve A B lastVE _Δ _f _a hTf hTa htrf htrlast =>
          have hargsInit : ∀ i (h : i < init.length) (h2 : i < vinit.length),
              P init[i] vinit[i] := by
            intro i h h2
            have := hargs i (by simp; omega) (by simp; omega)
            rwa [List.getElem_append_left h, List.getElem_append_left h2] at this
          obtain ⟨fvv, htrfvv, hfdef⟩ :=
            ih init.length (by omega) init vinit head head₂ hve hve₂ rfl hlen.symm
              hh hh₂ hd hargsInit htrf
          have hlastP : P last vlast := by
            have h := hargs init.length (by simp) (by simp [hlen])
            rw [List.getElem_append_right (Nat.le_refl _),
              List.getElem_append_right (hlen ▸ Nat.le_refl init.length)] at h
            simpa [hlen] using h
          obtain ⟨lvv, htrlvv, hldef⟩ := hP htrlast hlastP
          refine ⟨.app fvv lvv, ?_, ?_⟩
          · rw [List.concat_eq_append, mkApps_concat]
            have hTfvv : env.HasType Us.length Δ.toCtx fvv (.forallE A B) :=
              hTf.defeqU_l henv hΓ hfdef
            have hTlvv : env.HasType Us.length Δ.toCtx lvv A :=
              hTa.defeqU_l henv hΓ hldef
            exact .app hTfvv hTlvv htrfvv htrlvv
          · have hfd : env.IsDefEq Us.length Δ.toCtx fve fvv (.forallE A B) :=
              VEnv.IsDefEqU.of_l henv hΓ hfdef hTf
            have hld : env.IsDefEq Us.length Δ.toCtx lastVE lvv A :=
              VEnv.IsDefEqU.of_l henv hΓ hldef hTa
            exact ⟨_, .appDF hfd hld⟩

/-- **Subject reduction as definitional equality.**

If `e` translates to `ve` and `e` evaluates to `v`, then `v` translates to some `vv`
definitionally equal to `ve`. No flag restriction: the arms whose step is not a kernel
reduction of `env` — δ on a compiler body, ι, projection — carry the step's own
definitional equality, and this theorem is where it is spent. -/
theorem SEval.defeq {env : VEnv} (henv : env.WF) {Us : List Name} {Δ : VLCtx}
    (hΔ : VLCtx.WF env Us.length Δ) {bo : Name → Option Expr} {fl : SEvalFlags}
    {e v : Expr} {ve : VExpr}
    (htr : TrExprS env Us Δ e ve) (hev : SEval env bo Us fl Δ e v) :
    ∃ vv, TrExprS env Us Δ v vv ∧ env.IsDefEqU Us.length Δ.toCtx ve vv := by
  have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
  induction hev generalizing ve with
  | lam n ty b bi => exact ⟨ve, htr, VEnv.IsDefEqU.refl (htr.wf henv.ordered hΔ)⟩
  | @beta f a n ty b bi av r _ hf ha hbody ihf iha ihbody =>
      cases htr with
      | @app f' A B a' _Δ _f _a hTf hTa htrf htra =>
        obtain ⟨fv, htrfv, hfd⟩ := ihf htrf
        cases htrfv with
        | @lam ty' _Δ _ty _body body' _name _bi hty' htrty htrb =>
          obtain ⟨av_v, htrav, had⟩ := iha htra
          have hΔ' : VLCtx.WF env Us.length ((none, .vlam ty') :: Δ) := ⟨hΔ, nofun, hty'⟩
          obtain ⟨B'', hbodyT⟩ := htrb.wf henv.ordered hΔ'
          obtain ⟨u, hty'sort⟩ := hty'
          have lamT1 : env.HasType Us.length Δ.toCtx (.lam ty' body') (.forallE ty' B'') :=
            VEnv.HasType.lam hty'sort hbodyT
          have lamT2 : env.HasType Us.length Δ.toCtx (.lam ty' body') (.forallE A B) :=
            hTf.defeqU_l henv hΓ hfd
          have huForall : env.IsDefEqU Us.length Δ.toCtx (.forallE A B) (.forallE ty' B'') :=
            VEnv.IsDefEq.uniqU henv hΓ lamT2 lamT1
          obtain ⟨⟨w, hAty'⟩, _⟩ := VEnv.IsDefEqU.forallE_inv henv hΓ huForall
          have hadT : env.IsDefEq Us.length Δ.toCtx a' av_v A :=
            VEnv.IsDefEqU.of_l henv hΓ had hTa
          have havT : env.HasType Us.length Δ.toCtx av_v ty' :=
            (hadT.hasType.2).defeqU_r henv hΓ ⟨_, hAty'⟩
          have htrbody : TrExprS env Us Δ (b.instantiate1' av) (body'.inst av_v) :=
            TrExprS.inst henv.ordered havT htrb htrav
          obtain ⟨vve, htrr, hrd⟩ := ihbody htrbody
          refine ⟨vve, htrr, ?_⟩
          have hfdT : env.IsDefEq Us.length Δ.toCtx f' (.lam ty' body') (.forallE A B) :=
            VEnv.IsDefEqU.of_l henv hΓ hfd hTf
          have step1 : env.IsDefEq Us.length Δ.toCtx
              (.app f' a') (.app (.lam ty' body') av_v) (B.inst a') := .appDF hfdT hadT
          have step2 : env.IsDefEq Us.length Δ.toCtx
              (.app (.lam ty' body') av_v) (body'.inst av_v) (B''.inst av_v) :=
            .beta hbodyT havT
          have hcong : env.IsDefEqU Us.length Δ.toCtx (.app f' a') (body'.inst av_v) :=
            VEnv.IsDefEqU.trans henv hΓ ⟨_, step1⟩ ⟨_, step2⟩
          exact VEnv.IsDefEqU.trans henv hΓ hcong hrd
  | @zeta n ty val b nd vv r _ hval hbody ihval ihbody =>
      cases htr with
      | @letE val' ty' _ _ _ _ body' _ _ hValT htrty htrval htrb =>
          obtain ⟨vvv, htrvv, hvald⟩ := ihval htrval
          have hvvTrExpr : TrExpr env Us Δ vv val' :=
            ⟨vvv, htrvv, VEnv.IsDefEqU.symm hvald⟩
          have hΔlet : VLCtx.WF env Us.length ((none, .vlet ty' val') :: Δ) :=
            ⟨hΔ, nofun, hValT⟩
          have hbodyTrExpr : TrExpr env Us ((none, .vlet ty' val') :: Δ) b ve :=
            ⟨ve, htrb, VEnv.IsDefEqU.refl (htrb.wf henv.ordered hΔlet)⟩
          obtain ⟨sub', htrsub, hsubd⟩ :=
            TrExpr.inst_let henv hΔ hValT hbodyTrExpr hvvTrExpr
          obtain ⟨vve, htrr, hrd⟩ := ihbody htrsub
          exact ⟨vve, htrr, VEnv.IsDefEqU.trans henv hΓ (VEnv.IsDefEqU.symm hsubd) hrd⟩
  | @deltaC c us ups args argsv b b' v _ hb hinst hlen hargs hdef _ ihargs ihcont =>
      obtain ⟨hve, htrHead⟩ := trExprS_spine_head args htr
      have hargs' : ∀ i (h : i < args.length) (h2 : i < argsv.length),
          (fun e v => ∀ {ev : VExpr}, TrExprS env Us Δ e ev →
            ∃ vv, TrExprS env Us Δ v vv ∧ env.IsDefEqU Us.length Δ.toCtx ev vv) args[i]
            argsv[i] := by
        intro i h h2
        rw [← getElem!_pos args i h, ← getElem!_pos argsv i h2]
        exact fun htr => ihargs i h htr
      obtain ⟨ve₁, htr₁, hd₁⟩ :=
        SEval.defeq_spine henv hΔ
          (fun e v => ∀ {ev : VExpr}, TrExprS env Us Δ e ev →
            ∃ vv, TrExprS env Us Δ v vv ∧ env.IsDefEqU Us.length Δ.toCtx ev vv)
          (fun htr p => p htr) args.length args argsv (.const c us) (.const c us) hve hve
          rfl hlen htrHead htrHead
          (VEnv.IsDefEqU.refl (htrHead.wf henv.ordered hΔ)) hargs' htr
      obtain ⟨v₁, v₂, h₁, h₂, hd⟩ := hdef
      obtain ⟨vve, htrr, hrd⟩ := ihcont h₂
      refine ⟨vve, htrr, ?_⟩
      have huniq : env.IsDefEqU Us.length Δ.toCtx ve₁ v₁ :=
        TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htr₁ h₁
      exact VEnv.IsDefEqU.trans henv hΓ hd₁ (VEnv.IsDefEqU.trans henv hΓ huniq
        (VEnv.IsDefEqU.trans henv hΓ hd hrd))
  | @ctorVal cn us args argsv hnb hlen hargs ihargs =>
      obtain ⟨hve, htrHead⟩ := trExprS_spine_head args htr
      have hargs' : ∀ i (h : i < args.length) (h2 : i < argsv.length),
          (fun e v => ∀ {ev : VExpr}, TrExprS env Us Δ e ev →
            ∃ vv, TrExprS env Us Δ v vv ∧ env.IsDefEqU Us.length Δ.toCtx ev vv) args[i]
            argsv[i] := by
        intro i h h2
        rw [← getElem!_pos args i h, ← getElem!_pos argsv i h2]
        exact fun htr => ihargs i h htr
      exact SEval.defeq_spine henv hΔ
        (fun e v => ∀ {ev : VExpr}, TrExprS env Us Δ e ev →
            ∃ vv, TrExprS env Us Δ v vv ∧ env.IsDefEqU Us.length Δ.toCtx ev vv)
        (fun htr p => p htr) args.length args argsv
        (.const cn us) (.const cn us) hve hve rfl hlen htrHead htrHead
        (VEnv.IsDefEqU.refl (htrHead.wf henv.ordered hΔ)) hargs' htr
  | @iota con us cus pre minors discr ctor cargs np cidx r _ hdiscr hidx hdef _ _ ihcont =>
      obtain ⟨v₁, v₂, h₁, h₂, hd⟩ := hdef
      obtain ⟨vve, htrr, hrd⟩ := ihcont h₂
      refine ⟨vve, htrr, ?_⟩
      have huniq : env.IsDefEqU Us.length Δ.toCtx ve v₁ :=
        TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htr h₁
      exact VEnv.IsDefEqU.trans henv hΓ huniq (VEnv.IsDefEqU.trans henv hΓ hd hrd)
  | @proj S i discr ctor cus cargs np r _ hdiscr hlt hdef _ _ ihcont =>
      obtain ⟨v₁, v₂, h₁, h₂, hd⟩ := hdef
      obtain ⟨vve, htrr, hrd⟩ := ihcont h₂
      refine ⟨vve, htrr, ?_⟩
      have huniq : env.IsDefEqU Us.length Δ.toCtx ve v₁ :=
        TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) htr h₁
      exact VEnv.IsDefEqU.trans henv hΓ huniq (VEnv.IsDefEqU.trans henv hΓ hd hrd)
  | @lit l r _ _ ih =>
      cases htr with | lit _ htrC => exact ih htrC

end LeanToLambdaBox
