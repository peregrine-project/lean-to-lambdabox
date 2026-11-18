import EraseProof.Bridge.CLRead
import EraseProof.Source.Marks
import EraseProof.Relation.Basic
import ConLeche.Model.Rules.Sound
import ConLeche.Model.Tiers
import ConLeche.Model.Capstone
import ConLeche.Verify.Leaves
import ConLeche.Verify.InstLevels

/-!
# The meaning of source evaluation: the invariant and the first cases

`srcEval_sound` is proved by induction on the source evaluation, one case per rule of `SrcEval`.
A source term is read in con-leche's semantics through its marks: `toCL?` is transparent to every
mark (`mdata` is), so the reading of `unmark t` drops the `erase` and `reduced` marks and
η-contracts each `eta`-marked λ, which is the term `Sound` speaks of. The induction hypothesis of
each case is `SemSim`: the reading of `unmark` of the subject and of the value, and in every model,
where the subject is graded and not the proof point, the value is graded with the same
interpretation. A case's redex, formed from evaluated parts, is graded (`GradedU`); a reduction is
a derivation of con-leche's rules tier (`CL ConLeche/Rules/Rel.lean:106 Red`), built from syntax,
whose soundness `CL ConLeche/Model/Rules/Sound.lean:77 red_sound` at the environment inputs of the
model (`CL ConLeche/Model/Capstone.lean:155 Rules.RulesInputs.ofSem`) gives the equation where the
redex is not the point. This module proves the cases `beta`, `etaBeta`, `zeta`, `delta`, `ctor`,
`appCong`, `frozenApp` and the value rules, each from the grading of its redex and the facts its
premises name, and the passage from `SemSim` to `Sound`.
-/

open Lean Erasure
open ConLeche.Semantics ConLeche.SetModel ConLeche.SetTheory ConLeche.Verify ConLeche.Model
  ConLeche.Model.Rules

namespace EraseProof

universe w

/-! ## Readings in con-leche's semantics -/

/-- `t` is graded through its marks: the reading of `unmark t` is closed and, in every model `m` and
at every level valuation, has a reading graded at every valuation
(`CL ConLeche/Semantics/WellDenoted.lean:49 WellDenoted`). con-leche's inference claim
(`CL ConLeche/Model/Claims.lean:112 InferClaim`) gives it for a closed term whose reading
con-leche types (`SemCases.infer0`). The cases ask it of the redex they form from evaluated
parts. Reference: none (DV-33). -/
def GradedU (env : ConLeche.Env) (t : Expr) : Prop :=
  ∃ c : ConLeche.Expr, toCL? (unmark t) = some c ∧ c.looseBVarsBounded 0 = true ∧
    ∀ (V : Type w) [ConLeche.SetTheory V] (m : EnvModelM V env) (φ : ConLeche.Name → Nat),
      ∃ ta, denote m.base2.acval env φ 0 c = some ta ∧ ∀ ρ : Nat → V, WellDenoted V ρ ta

/-- The conclusion of `srcEval_sound` for one evaluation `t ⇓ v`, the induction hypothesis of each
case: if every `eta` mark of `t` sits on a λ, so does every one of `v`; if `unmark t` has a closed
reading, `unmark v` has one, and in every model `m` (`CL ConLeche/Model/Env/EnvModelM.lean:244
EnvModelM`), at every level valuation, the reading of `v` exists wherever that of `t` does, and at
every valuation where `t`'s is graded and not the proof point (`CL ConLeche/SetTheory/Derive/Pt.lean:69
pt`) `v`'s is graded with the same interpretation. Reference: the invariant of subject reduction
(`MR P/PCUICSR.v`), which con-leche does not have; DV-34. -/
def SemSim (env : ConLeche.Env) (t v : Expr) : Prop :=
  EtaLams t → EtaLams v ∧ ∀ {c : ConLeche.Expr}, toCL? (unmark t) = some c →
    c.looseBVarsBounded 0 = true →
    ∃ c', toCL? (unmark v) = some c' ∧ c'.looseBVarsBounded 0 = true ∧
      ∀ (V : Type w) [ConLeche.SetTheory V] (m : EnvModelM V env) (φ : ConLeche.Name → Nat)
        {ta : ConLeche.Term.Term},
        denote m.base2.acval env φ 0 c = some ta →
        ∃ va, denote m.base2.acval env φ 0 c' = some va ∧
          ∀ ρ : Nat → V, WellDenoted V ρ ta → interp V ρ ta ≠ pt →
            WellDenoted V ρ va ∧ interp V ρ ta = interp V ρ va

namespace SemCases

variable {env : ConLeche.Env}

/-! ## con-leche's facts on readings -/

section
variable {V : Type w} [ConLeche.SetTheory V]

/-- The application congruence where the application is not the point: the function is not the
point (`CL ConLeche/SetTheory/Derive/Graphs.lean:79 app_pt`), so both functions are one graph with
one domain (`CL ConLeche/SetModel/Ops.lean:202 AppliesTo`, `CL ConLeche/SetTheory/Derive/Graphs.lean:61
graph_dom_unique`), a type holding both arguments, which are then equal as soon as one is not the
point (`CL ConLeche/SetTheory/Derive/TypeU.lean:118 IsTy.eq_of_ne_pt`). Reference: none (DV-33). -/
theorem appCongr {ρ : Nat → V} {F A F' A' : ConLeche.Term.Term}
    (hwd : WellDenoted V ρ (.app F A)) (hwd' : WellDenoted V ρ (.app F' A'))
    (hF : interp V ρ F ≠ pt → interp V ρ F = interp V ρ F')
    (hA : interp V ρ A ≠ pt → interp V ρ A = interp V ρ A')
    (hne : interp V ρ (.app F A) ≠ pt) :
    interp V ρ (.app F A) = interp V ρ (.app F' A') := by
  simp only [interp_app] at hne ⊢
  have hFne : interp V ρ F ≠ pt := fun h => hne (by rw [h, app_pt])
  have hFeq := hF hFne
  rw [WellDenoted_app] at hwd hwd'
  rcases hwd.2.2 with h | ⟨G, D, hG, hD, hAmem⟩
  · exact absurd h hFne
  · rcases hwd'.2.2 with h' | ⟨G', D', hG', _, hA'mem⟩
    · exact absurd (hFeq.trans h') hFne
    · have hDD : D = D' := graph_dom_unique (hG.symm.trans (hFeq.trans hG'))
      subst hDD
      have hAeq : interp V ρ A = interp V ρ A' :=
        hD.eq_of_ne_pt hAmem hA'mem fun h _ => hA h
      rw [hFeq, hAeq]

/-- The `let` congruence: a `let` reads its body at its value (`CL ConLeche/Semantics/Interp.lean:161
interp_letE`), so two values that agree away from the point, and of which the second is the point
where the first is, give one interpretation. Reference: none (DV-33). -/
theorem letCongr {ρ : Nat → V} {A A' B : ConLeche.Term.Term}
    (hA : interp V ρ A ≠ pt → interp V ρ A = interp V ρ A')
    (hpt : interp V ρ A = pt → interp V ρ A' = pt) :
    interp V ρ (.letE A B) = interp V ρ (.letE A' B) := by
  simp only [interp_letE]
  by_cases h : interp V ρ A = pt
  · rw [h, hpt h]
  · rw [hA h]

/-- A reduction of a closed reading at depth `0`: con-leche's `CL ConLeche/Model/Rules/Motive.lean:102
RedSem`, by `red_sound` at `RulesInputs.ofSem`, with the frame, the empty context and the leaves
discharged from closedness (`CL ConLeche/Verify/Shift.lean:264 WScoped.of_not_hasFvar`,
`CL ConLeche/Verify/Leaves.lean:24 fvarLeaves_eq_nil_of_not_hasFvar`): the reduct reads, and where
the subject is graded and not the point, the reduct is graded with the same interpretation.
Reference: none (DV-34). -/
theorem red0 (m : EnvModelM V env) (φ : ConLeche.Name → Nat) {e e' : ConLeche.Expr}
    (h : ConLeche.Rules.Red env 0 e e') (hfv : e.hasFvar = false) (hb : e.looseBVarsBounded 0 = true)
    {ea : ConLeche.Term.Term} (hea : denote m.base2.acval env φ 0 e = some ea) :
    ∃ ea', denote m.base2.acval env φ 0 e' = some ea' ∧
      ∀ ρ : Nat → V, WellDenoted V ρ ea → interp V ρ ea ≠ pt →
        WellDenoted V ρ ea' ∧ interp V ρ ea = interp V ρ ea' := by
  have hnil := ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hfv
  have hf : Frame 0 e :=
    ⟨ConLeche.Expr.WScoped.of_not_hasFvar hfv, hb, fun l hl => by rw [hnil] at hl; cases hl⟩
  have hC : CtxOkS m.base2 φ 0 [] e := ⟨rfl, fun l hl => by rw [hnil] at hl; cases hl⟩
  obtain ⟨-, -, ea', hea', hs⟩ := red_sound (Rules.RulesInputs.ofSem m φ) h hf hC hea
  exact ⟨ea', hea', fun ρ hg hne =>
    hs ρ (Sat_nil V ρ) (fun l hl => by rw [hnil] at hl; cases hl) hg hne⟩

/-- A closed reading con-leche's full-grade inference accepts reads in every model and is graded at
every valuation: `CL ConLeche/Model/Tiers.lean:346 acceptedReads_of` and
`CL ConLeche/Model/Rules/Sound.lean:188 infer_sound` on the derivation of
`CL ConLeche/Verify/Rules/Bridge.lean:67 inferTypeCore_bridge`. Reference: none (DV-33). -/
theorem infer0 (m : EnvModelM V env) (φ : ConLeche.Name → Nat) {F : Nat} {e t : ConLeche.Expr}
    (h : ConLeche.inferTypeCore .verified false env F 0 e = .ok t)
    (hfv : e.hasFvar = false) (hb : e.looseBVarsBounded 0 = true) :
    ∃ ea, denote m.base2.acval env φ 0 e = some ea ∧ ∀ ρ : Nat → V, WellDenoted V ρ ea := by
  have hnil := ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hfv
  have hws := ConLeche.Expr.WScoped.of_not_hasFvar (d := 0) hfv
  have hLb : ConLeche.Expr.LeavesBounded e := fun l hl => by rw [hnil] at hl; cases hl
  obtain ⟨ea, hea⟩ := acceptedReads_of m.base2 φ h hws hb hLb
  have hC : CtxOkS m.base2 φ 0 [] e := ⟨rfl, fun l hl => by rw [hnil] at hl; cases hl⟩
  obtain ⟨-, -, ta, -, hs⟩ :=
    infer_sound (Rules.RulesInputs.ofSem m φ) (ConLeche.Rules.inferTypeCore_bridge h) ⟨hws, hb, hLb⟩
      hC hea
  exact ⟨ea, hea, fun ρ => (hs ρ (Sat_nil V ρ) (fun l hl => by rw [hnil] at hl; cases hl)).1⟩

/-- A reading without free variables is scoped below every depth (con-leche's own lemma is private,
`CL ConLeche/Model/Denotes.lean:184`). Reference: none. -/
theorem fvarsBelow0 : ∀ {e : ConLeche.Expr}, e.hasFvar = false → ConLeche.Expr.fvarsBelow 0 e := by
  intro e
  induction e <;> simp_all [ConLeche.Expr.fvarsBelow, ConLeche.Expr.hasFvar]

/-- On a closed reading, con-leche's public reading `Denotes` (`CL ConLeche/Denotes.lean:123`) holds
of exactly the interpretation of the internal reading (`CL ConLeche/Model/Denotes.lean:192
Denotes_of_denote`, `CL ConLeche/Denotes.lean:180 Denotes_functional`). Reference: none (DV-34). -/
theorem denotes_iff (m : EnvModelM V env) (φ : ConLeche.Name → Nat) (ρ : Nat → V) {c : ConLeche.Expr}
    {ta : ConLeche.Term.Term} (hc : denote m.base2.acval env φ 0 c = some ta) (hfv : c.hasFvar = false)
    (hb : c.looseBVarsBounded 0 = true) (X : V) :
    ConLeche.Denotes (Model.ofEnvModelM m).cval env φ ρ c X ↔ X = interp V ρ ta := by
  have hd := Denotes_of_denote (V := V) m.base2.cval_closed 0 c hc (fvarsBelow0 hfv) hb ρ
  rw [ConLeche.Expr.closeN_of_hasFvar c 0 0 hfv] at hd
  exact ⟨fun h => ConLeche.Denotes_functional h hd, fun h => h ▸ hd⟩

end

/-! ## The invariant's algebra -/

/-- A value rule: the subject is its own value. Reference: `eval_atom` (`MR P/PCUICWcbvEval.v:331`). -/
theorem semSim_refl (t : Expr) : SemSim.{w} env t t := fun hη =>
  ⟨hη, fun {c} hc hb => ⟨c, hc, hb, fun _ _ _ _ _ hta => ⟨_, hta, fun _ hwd _ => ⟨hwd, rfl⟩⟩⟩⟩

/-- Two evaluations in sequence. Reference: none. -/
theorem semSim_trans {t u v : Expr} (h₁ : SemSim.{w} env t u) (h₂ : SemSim.{w} env u v) :
    SemSim.{w} env t v := by
  intro hη
  obtain ⟨hηu, h₁⟩ := h₁ hη
  obtain ⟨hηv, h₂⟩ := h₂ hηu
  refine ⟨hηv, fun hc hb => ?_⟩
  obtain ⟨c₁, hc₁, hb₁, hm₁⟩ := h₁ hc hb
  obtain ⟨c₂, hc₂, hb₂, hm₂⟩ := h₂ hc₁ hb₁
  refine ⟨c₂, hc₂, hb₂, fun V _ m φ ta hta => ?_⟩
  obtain ⟨ua, hua, hρ₁⟩ := hm₁ V m φ hta
  obtain ⟨va, hva, hρ₂⟩ := hm₂ V m φ hua
  refine ⟨va, hva, fun ρ hwd hne => ?_⟩
  obtain ⟨hwd', he⟩ := hρ₁ ρ hwd hne
  obtain ⟨hwd'', he'⟩ := hρ₂ ρ hwd' (he ▸ hne)
  exact ⟨hwd'', he.trans he'⟩

/-- A step whose reading is a reduction of con-leche's rules tier: `red0`. Reference: none
(DV-34). -/
theorem semSim_of_red {t u : Expr}
    (hred : EtaLams t → EtaLams u ∧ ∀ c : ConLeche.Expr, toCL? (unmark t) = some c →
      c.looseBVarsBounded 0 = true →
      ∃ c', toCL? (unmark u) = some c' ∧ c'.looseBVarsBounded 0 = true ∧
        ConLeche.Rules.Red env 0 c c') :
    SemSim.{w} env t u := by
  intro hη
  obtain ⟨hηu, hred⟩ := hred hη
  refine ⟨hηu, fun {c} hc hb => ?_⟩
  obtain ⟨c', hc', hb', hr⟩ := hred c hc hb
  exact ⟨c', hc', hb', fun V _ m φ ta hta => red0 m φ hr (toCL?_hasFvar hc) hb hta⟩

/-- The reading of an application. -/
theorem toCL?_unmark_app {f a : Expr} {c : ConLeche.Expr} (h : toCL? (unmark (.app f a)) = some c) :
    ∃ cf ca, toCL? (unmark f) = some cf ∧ toCL? (unmark a) = some ca ∧ c = .app cf ca := by
  simp only [unmark, toCL?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.some.injEq] at h
  obtain ⟨cf, hcf, ca, hca, rfl⟩ := h
  exact ⟨cf, ca, hcf, hca, rfl⟩

/-- The head of a graded application is graded. Reference: none. -/
theorem gradedU_appFn {g a : Expr} (h : GradedU.{w} env (.app g a)) : GradedU.{w} env g := by
  obtain ⟨c, hc, hb, hm⟩ := h
  obtain ⟨cg, ca, hcg, -, rfl⟩ := toCL?_unmark_app hc
  simp only [ConLeche.Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  refine ⟨cg, hcg, hb.1, fun V _ m φ => ?_⟩
  obtain ⟨ta, hta, hwd⟩ := hm V m φ
  obtain ⟨ga, aa, hga, _, rfl⟩ := denote_app_inv hta
  exact ⟨ga, hga, fun ρ => by have h := hwd ρ; rw [WellDenoted_app] at h; exact h.1⟩

/-- The head of a graded spine is graded. Reference: none. -/
theorem gradedU_foldl_head : ∀ {vs : List Expr} {g : Expr}, GradedU.{w} env (vs.foldl .app g) →
    GradedU.{w} env g
  | [], _, h => h
  | _ :: _, _, h => gradedU_appFn (gradedU_foldl_head h)

/-- The application congruence (`appCongr`), the redex graded: the induction hypotheses on the
function and the argument give the application's. Reference: `eval_app_cong`
(`MR P/PCUICWcbvEval.v:311`); DV-33. -/
theorem appSim {f a f' a' : Expr} (hok : GradedU.{w} env (.app f' a'))
    (ihf : SemSim.{w} env f f') (iha : SemSim.{w} env a a') :
    SemSim.{w} env (.app f a) (.app f' a') := by
  intro hη
  obtain ⟨hηf, ihf⟩ := ihf hη.1
  obtain ⟨hηa, iha⟩ := iha hη.2
  refine ⟨⟨hηf, hηa⟩, fun {c} hc hb => ?_⟩
  obtain ⟨cf, ca, hcf, hca, rfl⟩ := toCL?_unmark_app hc
  simp only [ConLeche.Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  obtain ⟨cf', hcf', hbf', hmf⟩ := ihf hcf hb.1
  obtain ⟨ca', hca', hba', hma⟩ := iha hca hb.2
  obtain ⟨c₀, hc₀, -, hg⟩ := hok
  obtain ⟨cf₀, ca₀, hcf₀, hca₀, rfl⟩ := toCL?_unmark_app hc₀
  have e₁ : cf' = cf₀ := Option.some.inj (hcf'.symm.trans hcf₀)
  have e₂ : ca' = ca₀ := Option.some.inj (hca'.symm.trans hca₀)
  subst e₁ e₂
  refine ⟨_, hc₀, by simp [ConLeche.Expr.looseBVarsBounded, hbf', hba'], fun V _ m φ ta hta => ?_⟩
  obtain ⟨fa, aa, hfa, haa, rfl⟩ := denote_app_inv hta
  obtain ⟨fa', hfa', hρf⟩ := hmf V m φ hfa
  obtain ⟨aa', haa', hρa⟩ := hma V m φ haa
  obtain ⟨ra, hra, hwdr⟩ := hg V m φ
  have hra' : denote m.base2.acval env φ 0 (.app cf' ca') = some (.app fa' aa') := by
    rw [denote_app, hfa', haa']; rfl
  rw [hra'] at hra; cases hra
  refine ⟨_, hra', fun ρ hwd hne => ⟨hwdr ρ, appCongr hwd (hwdr ρ) (fun h => ?_) (fun h => ?_) hne⟩⟩
  · rw [WellDenoted_app] at hwd; exact (hρf ρ hwd.1 h).2
  · rw [WellDenoted_app] at hwd; exact (hρa ρ hwd.2.1 h).2

/-- The congruence of a spine of arguments, one `appSim` per argument, the spine graded. Reference:
`eval_construct` (`MR P/PCUICWcbvEval.v:303`); DV-33. -/
theorem spineSim : ∀ {as vs : List Expr} {f f' : Expr}, as.length = vs.length →
    (∀ (i : Nat) a v, as[i]? = some a → vs[i]? = some v → SemSim.{w} env a v) →
    GradedU.{w} env (vs.foldl .app f') → SemSim.{w} env f f' →
    SemSim.{w} env (as.foldl .app f) (vs.foldl .app f')
  | [], [], _, _, _, _, _, hf => hf
  | a :: as, v :: vs, f, f', hl, h, hg, hf =>
    spineSim (as := as) (vs := vs) (f := .app f a) (f' := .app f' v) (by simpa using hl)
      (fun i a v ha hv => h (i + 1) a v (by simpa using ha) (by simpa using hv)) hg
      (appSim (gradedU_foldl_head (vs := vs) hg) hf (h 0 a v rfl rfl))
  | [], _ :: _, _, _, hl, _, _, _ | _ :: _, [], _, _, hl, _, _, _ => by simp at hl

/-! ## `eta` marks under substitution -/

/-- A λ stays a λ under lifting. -/
theorem isLambda_lift {e : Expr} (s n : Nat) (h : e.isLambda = true) :
    (e.liftLooseBVars' s n).isLambda = true := by
  cases e <;> simp_all [Expr.isLambda, Expr.liftLooseBVars']

/-- A λ stays a λ under instantiation. -/
theorem isLambda_inst {e : Expr} (a : Expr) (k : Nat) (h : e.isLambda = true) :
    (e.instantiate1' a k).isLambda = true := by
  cases e <;> simp_all [Expr.isLambda, Expr.instantiate1']

/-- `EtaLams` under lifting. -/
theorem etaLams_lift : ∀ (e : Expr) (s n : Nat), EtaLams e → EtaLams (e.liftLooseBVars' s n)
  | .mdata _ e, s, n, h => ⟨fun hd => isLambda_lift s n (h.1 hd), etaLams_lift e s n h.2⟩
  | .app f a, s, n, h => ⟨etaLams_lift f s n h.1, etaLams_lift a s n h.2⟩
  | .lam _ t b _, s, n, h | .forallE _ t b _, s, n, h =>
    ⟨etaLams_lift t s n h.1, etaLams_lift b (s + 1) n h.2⟩
  | .letE _ t v b _, s, n, h =>
    ⟨etaLams_lift t s n h.1, etaLams_lift v s n h.2.1, etaLams_lift b (s + 1) n h.2.2⟩
  | .proj _ _ e, s, n, h => etaLams_lift e s n h
  | .bvar _, _, _, _ | .fvar _, _, _, _ | .mvar _, _, _, _ | .sort _, _, _, _ | .const .., _, _, _
  | .lit _, _, _, _ => trivial

/-- `EtaLams` under instantiation. -/
theorem etaLams_inst {a : Expr} (ha : EtaLams a) : ∀ (e : Expr) (k : Nat), EtaLams e →
    EtaLams (e.instantiate1' a k)
  | .bvar i, k, _ => by
    simp only [Expr.instantiate1']
    split
    · trivial
    · split
      · exact etaLams_lift a 0 k ha
      · trivial
  | .mdata _ e, k, h => ⟨fun hd => isLambda_inst a k (h.1 hd), etaLams_inst ha e k h.2⟩
  | .app f b, k, h => ⟨etaLams_inst ha f k h.1, etaLams_inst ha b k h.2⟩
  | .lam _ t b _, k, h | .forallE _ t b _, k, h =>
    ⟨etaLams_inst ha t k h.1, etaLams_inst ha b (k + 1) h.2⟩
  | .letE _ t v b _, k, h =>
    ⟨etaLams_inst ha t k h.1, etaLams_inst ha v k h.2.1, etaLams_inst ha b (k + 1) h.2.2⟩
  | .proj _ _ e, k, h => etaLams_inst ha e k h
  | .fvar _, _, _ | .mvar _, _, _ | .sort _, _, _ | .const .., _, _ | .lit _, _, _ => trivial

/-- `EtaLams` under universe instantiation. -/
theorem etaLams_instLevels (ps : List Name) (us : List Level) : ∀ (e : Expr), EtaLams e →
    EtaLams (Pure.instLevels ps us e)
  | .mdata _ e, h => ⟨fun hd => by
      have hl := h.1 hd
      cases e <;> simp_all [Expr.isLambda, Pure.instLevels], etaLams_instLevels ps us e h.2⟩
  | .app f a, h => ⟨etaLams_instLevels ps us f h.1, etaLams_instLevels ps us a h.2⟩
  | .lam _ t b _, h | .forallE _ t b _, h =>
    ⟨etaLams_instLevels ps us t h.1, etaLams_instLevels ps us b h.2⟩
  | .letE _ t v b _, h =>
    ⟨etaLams_instLevels ps us t h.1, etaLams_instLevels ps us v h.2.1,
      etaLams_instLevels ps us b h.2.2⟩
  | .proj _ _ e, h => etaLams_instLevels ps us e h
  | .bvar _, _ | .fvar _, _ | .mvar _, _ | .sort _, _ | .const .., _ | .lit _, _ => trivial

/-- Instantiating at an index that does not occur does not read the substituted term. -/
theorem inst_absent (a a' : Expr) : ∀ (e : Expr) (k : Nat), bvarOccurs k e = false →
    e.instantiate1' a k = e.instantiate1' a' k
  | .bvar i, k, h => by
    simp only [bvarOccurs, beq_eq_false_iff_ne] at h
    simp [Expr.instantiate1', h]
  | .mdata _ e, k, h | .proj _ _ e, k, h => by
    simp only [bvarOccurs] at h
    simp [Expr.instantiate1', inst_absent a a' e k h]
  | .app f b, k, h => by
    simp only [bvarOccurs, Bool.or_eq_false_iff] at h
    simp [Expr.instantiate1', inst_absent a a' f k h.1, inst_absent a a' b k h.2]
  | .lam _ t b _, k, h | .forallE _ t b _, k, h => by
    simp only [bvarOccurs, Bool.or_eq_false_iff] at h
    simp [Expr.instantiate1', inst_absent a a' t k h.1, inst_absent a a' b (k + 1) h.2]
  | .letE _ t v b _, k, h => by
    simp only [bvarOccurs, Bool.or_eq_false_iff] at h
    simp [Expr.instantiate1', inst_absent a a' t k h.1.1, inst_absent a a' v k h.1.2,
      inst_absent a a' b (k + 1) h.2]
  | .fvar _, _, _ | .mvar _, _, _ | .sort _, _, _ | .const .., _, _ | .lit _, _, _ => rfl

/-! ## The reductions -/

/-- β on the reading: `Red.beta` (`CL ConLeche/Rules/Rel.lean:134`); the contractum's reading is the
substituted body's (`unmark_instantiate1'`, `toCL?_instantiate1'_closed`), closed by
`CL ConLeche/Verify/Shift.lean:702 looseBVarsBounded_instantiate1_gen`. Reference: `eval_beta`
(`MR P/PCUICWcbvEval.v:234`). -/
theorem betaRed {n : Name} {A b a' : Expr} {bi : BinderInfo} :
    SemSim.{w} env (.app (.lam n A b bi) a') (b.instantiate1' a') := by
  refine semSim_of_red fun hη => ⟨etaLams_inst hη.2 b 0 hη.1.2, fun c hc hb => ?_⟩
  obtain ⟨cl, ca, hcl, hca, rfl⟩ := toCL?_unmark_app hc
  simp only [unmark, toCL?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.some.injEq] at hcl
  obtain ⟨cA, -, cb, hcb, rfl⟩ := hcl
  simp only [ConLeche.Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  refine ⟨cb.instantiate1 ca, ?_, ConLeche.Expr.looseBVarsBounded_instantiate1_gen hb.2 hb.1.2,
    .beta⟩
  rw [unmark_instantiate1' a' b 0 hη.1.2, toCL?_instantiate1'_closed hca hb.2, hcb]; rfl

/-- A subject is read through `unmark`: two subjects with one unmarking have one meaning. -/
theorem semSim_of_unmark {t t' v : Expr} (hu : unmark t = unmark t') (hη : EtaLams t → EtaLams t')
    (h : SemSim.{w} env t' v) : SemSim.{w} env t v := fun ht =>
  let ⟨hv, h⟩ := h (hη ht)
  ⟨hv, fun hc hb => h (hu ▸ hc) hb⟩

/-- A certificate is read through `unmark`. -/
theorem gradedU_of_unmark {t t' : Expr} (hu : unmark t = unmark t') (h : GradedU.{w} env t') :
    GradedU.{w} env t := by
  unfold GradedU; rw [hu]; exact h

/-- The `let` congruence (`letCongr`), the evaluated `let` graded; `hpt`: where the value reads as
the point, its evaluation does. Reference: none (DV-33). -/
theorem letSim {n : Name} {T val val' b : Expr} {nd : Bool}
    (hok : GradedU.{w} env (.letE n T val' b nd)) (ihv : SemSim.{w} env val val')
    (hpt : ∀ (V : Type w) [ConLeche.SetTheory V] (m : EnvModelM V env) (φ : ConLeche.Name → Nat)
      (cv cv' : ConLeche.Expr) (va va' : ConLeche.Term.Term), toCL? (unmark val) = some cv →
      toCL? (unmark val') = some cv' → denote m.base2.acval env φ 0 cv = some va →
      denote m.base2.acval env φ 0 cv' = some va' → ∀ ρ : Nat → V,
        interp V ρ va = pt → interp V ρ va' = pt) :
    SemSim.{w} env (.letE n T val b nd) (.letE n T val' b nd) := by
  intro hη
  obtain ⟨hηv, ihv⟩ := ihv hη.2.1
  refine ⟨⟨hη.1, hηv, hη.2.2⟩, fun {c} hc hb => ?_⟩
  simp only [unmark, toCL?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.some.injEq] at hc
  obtain ⟨cT, hcT, cv, hcv, cb, hcb, rfl⟩ := hc
  simp only [ConLeche.Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  obtain ⟨cv', hcv', hbv', hmv⟩ := ihv hcv hb.1.2
  obtain ⟨c₀, hc₀, -, hg⟩ := hok
  have hc₁ : toCL? (unmark (.letE n T val' b nd)) = some (.letE cT cv' cb) := by
    simp only [unmark, toCL?, hcT, hcv', hcb]; rfl
  rw [hc₁] at hc₀; cases hc₀
  refine ⟨_, hc₁, by simp [ConLeche.Expr.looseBVarsBounded, hb.1.1, hbv', hb.2],
    fun V _ m φ ta hta => ?_⟩
  obtain ⟨tT, va, ba, htT, hva, hba, rfl⟩ := denote_letE_inv hta
  obtain ⟨va', hva', hρ⟩ := hmv V m φ hva
  have hra : denote m.base2.acval env φ 0 (.letE cT cv' cb) = some (.letE va' ba) := by
    rw [denote_letE, htT, hva', hba]; rfl
  obtain ⟨ra, hra', hwdr⟩ := hg V m φ
  rw [hra] at hra'; cases hra'
  refine ⟨_, hra, fun ρ hwd _ => ⟨hwdr ρ, letCongr (fun h => ?_)
    (hpt V m φ cv cv' va va' hcv hcv' hva hva' ρ)⟩⟩
  rw [WellDenoted_letE] at hwd; exact (hρ ρ hwd.1 h).2

/-- ζ on the reading: `Red.zeta` (`CL ConLeche/Rules/Rel.lean:140`). Reference: `eval_zeta`
(`MR P/PCUICWcbvEval.v:241`). -/
theorem zetaRed {n : Name} {T v b : Expr} {nd : Bool} :
    SemSim.{w} env (.letE n T v b nd) (b.instantiate1' v) := by
  refine semSim_of_red fun hη => ⟨etaLams_inst hη.2.1 b 0 hη.2.2, fun c hc hb => ?_⟩
  simp only [unmark, toCL?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.some.injEq] at hc
  obtain ⟨cT, -, cv, hcv, cb, hcb, rfl⟩ := hc
  simp only [ConLeche.Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  refine ⟨cb.instantiate1 cv, ?_, ConLeche.Expr.looseBVarsBounded_instantiate1_gen hb.1.2 hb.2,
    .zeta⟩
  rw [unmark_instantiate1' v b 0 hη.2.2, toCL?_instantiate1'_closed hcv hb.1.2, hcb]; rfl

/-- β on an `eta`-marked λ: where `unmark` contracts the mark (`λ x. g x` to `g`), the contractum's
reading is the redex's (`Red.refl`, `CL ConLeche/Rules/Rel.lean:111`); otherwise `betaRed`.
Reference: `eval_beta` (`MR P/PCUICWcbvEval.v:234`); DV-23. -/
theorem etaBetaRed {n : Name} {A b a' : Expr} {bi : BinderInfo} :
    SemSim.{w} env (.app (markEta (.lam n A b bi)) a') (b.instantiate1' a') := by
  have hid : etaContract (.lam n (unmark A) (unmark b) bi) = .lam n (unmark A) (unmark b) bi →
      SemSim.{w} env (.app (markEta (.lam n A b bi)) a') (b.instantiate1' a') := fun hs =>
    semSim_of_unmark (t' := .app (.lam n A b bi) a') (by simp only [unmark, hs])
      (fun h => ⟨h.1.2, h.2⟩) betaRed
  by_cases hsh : Marks.EtaShape (.lam n (unmark A) (unmark b) bi)
  · obtain ⟨_, _, g, _, he⟩ := hsh
    injection he with _ _ hub _
    by_cases ho : bvarOccurs 0 g = true
    · exact hid (by rw [hub]; simp [etaContract, ho])
    · have hno : bvarOccurs 0 g = false := by simpa using ho
      refine semSim_of_red fun hη => ⟨etaLams_inst hη.2 b 0 hη.1.2.2,
        fun c hc hb => ⟨c, ?_, hb, .refl⟩⟩
      have hu : unmark (.app (markEta (.lam n A b bi)) a') =
          .app (g.instantiate1' (.bvar 0)) (unmark a') := by
        simp [unmark, hub, etaContract, hno]
      rw [hu] at hc
      simp only [toCL?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        Option.some.injEq] at hc
      obtain ⟨cg, hcg, ca, hca, rfl⟩ := hc
      simp only [ConLeche.Expr.looseBVarsBounded, Bool.and_eq_true] at hb
      have hcg' : toCL? (g.instantiate1' (unmark a') 0) = some cg := by
        rw [inst_absent (unmark a') (.bvar 0) g 0 hno]; exact hcg
      rw [toCL?_instantiate1'_closed hca hb.2] at hcg'
      obtain ⟨cg₁, hcg₁, rfl⟩ := Option.map_eq_some_iff.mp hcg'
      rw [unmark_instantiate1' a' b 0 hη.1.2.2, hub, toCL?_instantiate1'_closed hca hb.2]
      simp [toCL?, hcg₁, ConLeche.Expr.instantiate1]
  · exact hid (Marks.etaContract_of_not hsh)

/-! ## The cases -/

/-- The value rules `constAtom`, `atom`, `etaLam`, `frozen`, `lit` of `srcEval_sound`: a value is
its own evaluation. Reference: `eval_atom` (`MR P/PCUICWcbvEval.v:331`). -/
theorem srcEval_sound_value (t : Expr) : SemSim.{w} env t t := semSim_refl t

/-- The `beta` case of `srcEval_sound`: the application congruence to the redex formed from the
values (graded, `hok`), then β (`betaRed`). Reference: `eval_beta` (`MR P/PCUICWcbvEval.v:234`);
DV-33. -/
theorem srcEval_sound_beta {f a a' b v A : Expr} {n : Name} {bi : BinderInfo}
    (hok : GradedU.{w} env (.app (.lam n A b bi) a'))
    (ihf : SemSim.{w} env f (.lam n A b bi)) (iha : SemSim.{w} env a a')
    (ihb : SemSim.{w} env (b.instantiate1' a') v) : SemSim.{w} env (.app f a) v :=
  semSim_trans (appSim hok ihf iha) (semSim_trans betaRed ihb)

/-- The `etaBeta` case of `srcEval_sound`: as `beta`, on an `eta`-marked λ (`etaBetaRed`).
Reference: `eval_beta` (`MR P/PCUICWcbvEval.v:234`); DV-23, DV-33. -/
theorem srcEval_sound_etaBeta {f a a' b v A : Expr} {n : Name} {bi : BinderInfo}
    (hok : GradedU.{w} env (.app (markEta (.lam n A b bi)) a'))
    (ihf : SemSim.{w} env f (markEta (.lam n A b bi))) (iha : SemSim.{w} env a a')
    (ihb : SemSim.{w} env (b.instantiate1' a') v) : SemSim.{w} env (.app f a) v :=
  semSim_trans (appSim hok ihf iha) (semSim_trans etaBetaRed ihb)

/-- The `zeta` case of `srcEval_sound`: the `let` congruence to the `let` of the value (graded,
`hok`; `hpt`, the value of a proof is a proof), then ζ (`zetaRed`). Reference: `eval_zeta`
(`MR P/PCUICWcbvEval.v:241`); DV-33. -/
theorem srcEval_sound_zeta {n : Name} {T val val' b v : Expr} {nd : Bool}
    (hok : GradedU.{w} env (.letE n T val' b nd))
    (hpt : ∀ (V : Type w) [ConLeche.SetTheory V] (m : EnvModelM V env) (φ : ConLeche.Name → Nat)
      (cv cv' : ConLeche.Expr) (va va' : ConLeche.Term.Term), toCL? (unmark val) = some cv →
      toCL? (unmark val') = some cv' → denote m.base2.acval env φ 0 cv = some va →
      denote m.base2.acval env φ 0 cv' = some va' → ∀ ρ : Nat → V,
        interp V ρ va = pt → interp V ρ va' = pt)
    (ihv : SemSim.{w} env val val') (ihb : SemSim.{w} env (b.instantiate1' val') v) :
    SemSim.{w} env (.letE n T val b nd) v :=
  semSim_trans (letSim hok ihv hpt) (semSim_trans zetaRed ihb)

/-- The `delta` case of `srcEval_sound`: δ is invisible to the reading (`CL ConLeche/Kernel/CoreDefs.lean:115
unfoldDefinition`, `CL ConLeche/Model/Rules/RedSoundKit.lean:734 denote_unfoldDefinition` at the δ
law `CL ConLeche/Model/Env/EnvModelM.lean:266 defn_reads`): the unfolded value, read through
`unmark` (`unmark_instLevels`, `toCL?_instLevels`), is the stored value at the constant's levels,
which reads as the constant. `hst`: `c` is stored as a definition with the value `body` reads as, at
the level parameters of `ci`, closed; `hread`, `hη`: the marking `bM` of `body` reads as `body` and
its `eta` marks sit on λs. Reference: `eval_delta` (`MR P/PCUICWcbvEval.v:247`). -/
theorem srcEval_sound_delta {c : Name} {us : List Level} {ci : ConstantInfo} {body bM v : Expr}
    (hst : ∃ cv value hint, env.find? (Name.toCL c) = some (.defnInfo cv value hint) ∧
      cv.levelParams = ci.levelParams.map Name.toCL ∧ toCL? body = some value ∧
      value.looseBVarsBounded 0 = true)
    (hread : toCL? (unmark bM) = toCL? body) (hη : EtaLams bM)
    (ih : SemSim.{w} env (Pure.instLevels ci.levelParams us bM) v) :
    SemSim.{w} env (.const c us) v := by
  obtain ⟨cv, value, hint, hfind, hlps, hval, hvb⟩ := hst
  intro _
  obtain ⟨hηv, ih⟩ := ih (etaLams_instLevels _ _ bM hη)
  refine ⟨hηv, fun {c₀} hc _ => ?_⟩
  simp only [unmark, toCL?, Option.map_eq_map, Option.map_eq_some_iff] at hc
  obtain ⟨us', hus, rfl⟩ := hc
  have hc₁ : toCL? (unmark (Pure.instLevels ci.levelParams us bM)) =
      some (value.instantiateLevelParams cv.levelParams us') := by
    rw [unmark_instLevels, toCL?_instLevels _ hus, hread, hval, hlps]; rfl
  obtain ⟨c', hc', hb', hm⟩ :=
    ih hc₁ (by rw [ConLeche.Expr.looseBVarsBounded_instantiateLevelParams]; exact hvb)
  refine ⟨c', hc', hb', fun V _ m φ ta hta => ?_⟩
  have hlen : us'.length = cv.levelParams.length := by
    by_cases hne : us'.length = cv.levelParams.length
    · exact hne
    · have hnone : denote m.base2.acval env φ 0 (.const (Name.toCL c) us') = none := by
        rw [denote, hfind]; simp [ConLeche.ConstantInfo.toConstantVal, hne]
      rw [hnone] at hta; cases hta
  have hud : ConLeche.unfoldDefinition env (.const (Name.toCL c) us') =
      some (value.instantiateLevelParams cv.levelParams us') := by
    simp [ConLeche.unfoldDefinition, ConLeche.Expr.getAppFn, ConLeche.Expr.getAppArgs, hfind, hlen,
      ConLeche.Expr.mkAppN]
  exact hm V m φ (denote_unfoldDefinition m.defn_reads hud hta)

/-- The `appCong` case of `srcEval_sound`: the application congruence (`appSim`), the application
of the values graded (`hok`). Reference: `eval_app_cong` (`MR P/PCUICWcbvEval.v:311`); DV-33. -/
theorem srcEval_sound_appCong {f a f' a' : Expr} (hok : GradedU.{w} env (.app f' a'))
    (ihf : SemSim.{w} env f f') (iha : SemSim.{w} env a a') :
    SemSim.{w} env (.app f a) (.app f' a') :=
  appSim hok ihf iha

/-- The `ctor` case of `srcEval_sound`: the congruence of the argument spine (`spineSim`), the
constructor value graded (`hok`). Reference: `eval_construct` (`MR P/PCUICWcbvEval.v:303`); DV-33. -/
theorem srcEval_sound_ctor {c : Name} {us : List Level} {as vs : List Expr}
    (hlen : as.length = vs.length) (hok : GradedU.{w} env (mkAppN (.const c us) vs.toArray))
    (ih : ∀ (i : Nat) a v, as[i]? = some a → vs[i]? = some v → SemSim.{w} env a v) :
    SemSim.{w} env (mkAppN (.const c us) as.toArray) (mkAppN (.const c us) vs.toArray) := by
  rw [mkAppN_toArray] at hok ⊢
  rw [mkAppN_toArray]
  exact spineSim hlen ih hok (semSim_refl _)

/-- The `frozenApp` case of `srcEval_sound`: the frozen value reads as the application of the
values (marks are transparent), so it is the application congruence (`appSim`), the application
graded (`hok`). Reference: `eval_box` (`MR E/EWcbvEval.v:121`); DV-32, DV-33. -/
theorem srcEval_sound_frozenApp {f a s a' : Expr} (hok : GradedU.{w} env (.app s a'))
    (ihf : SemSim.{w} env f (markErase s)) (iha : SemSim.{w} env a a') :
    SemSim.{w} env (.app f a) (markErase (.app s a')) := by
  have hu : unmark (.app (markErase s) a') = unmark (.app s a') := by simp [unmark]
  refine semSim_trans (appSim (gradedU_of_unmark hu hok) ihf iha)
    (semSim_of_red fun hη => ⟨⟨fun h => absurd h (by simp [markMD]), hη.1.2, hη.2⟩,
      fun c hc hb => ⟨c, by simpa [unmark] using hc, hb, .refl⟩⟩)

end SemCases

/-- `Sound` from the invariant: if con-leche types `e`, the marked `ê` reads through `unmark` as `e`
and its `eta` marks sit on λs, and `SemSim env ê v`, then `v` means what `e` means
(`SemCases.denotes_iff`, `SemCases.infer0`). Reference: none (DV-34). -/
theorem Sound.of_semSim {env : ConLeche.Env} {e ê v : Expr} (hty : CLTyped env e)
    (hread : toCL? (unmark ê) = toCL? e) (hη : EtaLams ê) (h : SemSim.{w} env ê v) :
    Sound.{w} env e v := by
  obtain ⟨c, F, T, hc, hinf⟩ := hty
  have hb := CLTyped.closed ⟨c, F, T, hc, hinf⟩ hc
  obtain ⟨-, h⟩ := h hη
  obtain ⟨c', hc', hb', hm⟩ := h (hread.trans hc) hb
  refine ⟨⟨c', hc'⟩, fun V _ m φ ρ X c₁ c₁' he hv hD hX => ?_⟩
  rw [hc] at he; cases he
  rw [hc'] at hv; cases hv
  obtain ⟨ea, hea, hwd⟩ := SemCases.infer0 m φ hinf (toCL?_hasFvar hc) hb
  obtain ⟨va, hva, hρ⟩ := hm V m φ hea
  rw [SemCases.denotes_iff m φ ρ hea (toCL?_hasFvar hc) hb] at hD
  rw [SemCases.denotes_iff m φ ρ hva (toCL?_hasFvar hc') hb']
  subst hD
  exact (hρ ρ (hwd ρ) hX).2

end EraseProof
