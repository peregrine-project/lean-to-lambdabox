import EraseProof.Source.Eval
import EraseProof.Env.Unfold
import EraseProof.Typing.Inst
import EraseProof.Typing.InstLevels
import EraseProof.Typing.Uniq

/-!
# Typed evaluation steps

One lemma per rule of `SrcEval` that is not a reflexivity (`beta`, `zeta`, `delta`, `fixApp`,
`appCong`): given the induction hypotheses of subject reduction for the rule's premises, a
translated and typed redex evaluates to a translated result that is definitionally equal to it at
the same type. The δ rules rest on two model facts about an unfoldable constant: its defining
equation (definitions, lean4lean's `extra` rule) or proof irrelevance (theorems).
-/

open Lean Lean4Lean Erasure

namespace EraseProof

section
variable {venv : VEnv} {P : List ConstantInfo} {σ : EvalEnv}

/-- The value `EvalEnv.unfold?` returns is the declaration's value. Reference: `cst_body decl =
Some body` in `eval_delta` (`MR P/PCUICWcbvEval.v:247`). -/
theorem EvalEnv.unfold?_value (hu : σ.unfold? c = some (ci, b)) :
    ci.value! (allowOpaque := true) = b := by
  unfold EvalEnv.unfold? at hu
  split at hu
  · split at hu
    · cases hu
    · cases hu; rfl
  · split at hu
    · cases hu
    · cases hu; rfl
  · cases hu

/-- A definition or theorem of `P` has a translated definition in the model whose value has its
type (`VDefVal.WF`, a premise of `ProgEnv`'s rules). Reference: `declared_constant_inv`
(`MR P/Typing/PCUICWeakeningEnvTyp.v:252`), the typing of `cst_body`. -/
theorem ProgEnv.lookupDef_wf (h : ProgEnv P venv) (hc : findDecl P c = some ci)
    (hk : (∃ v, ci = .defnInfo v) ∨ ∃ v, ci = .thmInfo v) :
    ∃ ci' : VDefVal, TrDef venv venv ci ci' ∧ venv.constants c = some ci'.toVConstant ∧
      ci'.WF venv := by
  induction h generalizing ci with
  | nil => simp [findDecl] at hc
  | «axiom» _ _ _ h2 ih =>
    have hle := VEnv.addConst_le h2
    rw [findDecl_cons] at hc
    split at hc
    · cases hc; obtain ⟨_, h⟩ | ⟨_, h⟩ := hk <;> cases h
    · have ⟨ci', h1, h2, h3⟩ := ih hc hk
      exact ⟨ci', h1.mono hle hle, hle.constants h2, VEnv.IsDefEq.mono hle h3⟩
  | @defn _ _ _ venv' ci' _ _ htr hw h2 ih =>
    have hle : _ ≤ venv'.addDefEq ci'.toDefEq := (VEnv.addConst_le h2).trans VEnv.addDefEq_le
    rw [findDecl_cons] at hc
    split at hc
    · cases hc; subst c
      exact ⟨ci', htr.mono hle hle, VEnv.addDefEq_le.constants (VEnv.addConst_self h2),
        VEnv.IsDefEq.mono hle hw⟩
    · have ⟨ci', h1, h2, h3⟩ := ih hc hk
      exact ⟨ci', h1.mono hle hle, hle.constants h2, VEnv.IsDefEq.mono hle h3⟩
  | thm _ _ htr hw _ h2 ih =>
    have hle := VEnv.addConst_le h2
    rw [findDecl_cons] at hc
    split at hc
    · cases hc; subst c
      exact ⟨_, htr.mono hle hle, VEnv.addConst_self h2, VEnv.IsDefEq.mono hle hw⟩
    · have ⟨ci', h1, h2, h3⟩ := ih hc hk
      exact ⟨ci', h1.mono hle hle, hle.constants h2, VEnv.IsDefEq.mono hle h3⟩
  | «opaque» _ _ _ _ h2 ih =>
    have hle := VEnv.addConst_le h2
    rw [findDecl_cons] at hc
    split at hc
    · cases hc; obtain ⟨_, h⟩ | ⟨_, h⟩ := hk <;> cases h
    · have ⟨ci', h1, h2, h3⟩ := ih hc hk
      exact ⟨ci', h1.mono hle hle, hle.constants h2, VEnv.IsDefEq.mono hle h3⟩
  | @block _ _ venv' vs cis' _ _ _ htr _ h2 hw ih =>
    have hleV : venv' ≤ venv'.addDefEqs cis' := VEnv.addDefEqs_le
    have hle : _ ≤ venv'.addDefEqs cis' := (VEnv.addConsts_le h2).trans hleV
    simp only [findDecl, List.find?_append] at hc
    cases hb : (vs.reverse.map ConstantInfo.defnInfo).find? (·.name == c) with
    | none =>
      rw [hb, Option.none_or] at hc
      have ⟨ci', h1, h2, h3⟩ := ih hc hk
      exact ⟨ci', h1.mono hle hle, hle.constants h2, VEnv.IsDefEq.mono hle h3⟩
    | some d =>
      rw [hb, Option.some_or] at hc
      injection hc with hc
      subst hc
      have hn : d.name = c :=
        beq_iff_eq.1 (List.find?_some (p := fun x : ConstantInfo => x.name == c) hb)
      have ⟨v, hv, hd⟩ : ∃ v ∈ vs, ConstantInfo.defnInfo v = d := by
        simpa using List.mem_of_find?_eq_some hb
      subst hd hn
      have ⟨ci', hci', htr'⟩ := forall₂_exists_of_mem_left htr hv
      have hname : v.name = ci'.name := htr'.2.1
      refine ⟨ci', htr'.mono hle hleV, ?_, VEnv.IsDefEq.mono hleV (hw ci' hci')⟩
      rw [show (ConstantInfo.defnInfo v).name = ci'.name from hname]
      exact hleV.constants (VEnv.addConsts_constants h2 _ hci')

/-- δ for a definition: its defining equation (`VDefVal.toDefEq`) instantiated at the levels
`us'` by lean4lean's `extra` rule (`l4l Theory/Typing/Basic.lean:54`). Reference: the δ-reduction
`red_delta` (`MR P/PCUICReduction.v:77`), `eval_delta` (`MR P/PCUICWcbvEval.v:247`). -/
theorem SrcEval.delta_defn_step {ci' : VDefVal} (hdf : venv.defeqs ci'.toDefEq)
    (hls : ∀ l ∈ us', l.WF U) (hlen : us'.length = ci'.uvars) :
    venv.IsDefEq U [] (.const ci'.name us') (ci'.value.instL us') (ci'.type.instL us') := by
  have := VEnv.IsDefEq.extra (Γ := []) hdf hls hlen
  simpa [VDefVal.toDefEq, VExpr.instL, VLevel.inst_map_id hlen] using this

/-- δ for a theorem: a constant whose type is a proposition is definitionally equal to its value
by proof irrelevance (`l4l Theory/Typing/Basic.lean:51`), as lean4lean `TrEnv'.of_value`
(`l4l Verify/Environment/Lemmas.lean:215`, `thm` case) relates a theorem to its value. Reference:
`eval_delta` on a theorem (`MR P/PCUICWcbvEval.v:247`); PCUIC unfolds theorems by δ. -/
theorem SrcEval.delta_thm_step {ci' : VDefVal} (hc : venv.constants c = some ci'.toVConstant)
    (hp : venv.HasType ci'.uvars [] ci'.type (.sort .zero)) (hw : ci'.WF venv)
    (hls : ∀ l ∈ us', l.WF U) (hlen : us'.length = ci'.uvars) :
    venv.IsDefEq U [] (.const c us') (ci'.value.instL us') (ci'.type.instL us') := by
  have hp' : venv.HasType U [] (ci'.type.instL us') (.sort .zero) := by
    simpa [VExpr.instL, VLevel.inst] using hp.instL hls
  exact .proofIrrel hp' (VEnv.HasType.const hc hls hlen) (VEnv.HasType.instL (Γ := []) hls hw)

/-- An unfoldable constant, translated in the model, is definitionally equal to the translation
of its value instantiated at the constant's levels (`Pure.instLevels`, which `TrS.instLevels`
translates exactly). Reference: the δ case of `subject_reduction_eval`
(`MR P/PCUICClassification.v:1093`). -/
theorem SrcEval.unfold_step (henv : ProgEnv P venv) (hsub : SubEnv σ.decls P)
    (hu : σ.unfold? c = some (ci, body)) (he : TrS venv Us [] (.const c us) e') :
    ∃ b', TrS venv Us [] (Pure.instLevels ci.levelParams us body) b' ∧
      venv.IsDefEqU Us.length [] e' b' := by
  let .const hc hus hlen := he
  have ⟨ci', htr, hc', hk⟩ := henv.unfold hsub hu
  cases hc.symm.trans hc'
  have hls := VLevel.WF.of_mapM_ofLevel hus
  have hlen' := (List.mapM_eq_some.1 hus).length_eq.symm.trans hlen
  have ⟨hfd, hkind⟩ := EvalEnv.unfold?_some hu
  have hn : ci.name = c :=
    beq_iff_eq.1 (List.find?_some (p := fun x : ConstantInfo => x.name == c) hfd)
  have hval := htr.2.2
  rw [EvalEnv.unfold?_value hu] at hval
  refine ⟨_, TrS.instLevels hus (hlen.trans htr.1.1.symm) hval, ?_⟩
  rcases hk with hdf | hp
  · have := SrcEval.delta_defn_step hdf hls hlen'
    rw [← htr.2.1, hn] at this
    exact ⟨_, this⟩
  · have hP := hsub ci (List.mem_of_find?_eq_some hfd)
    rw [hn] at hP
    have ⟨ci'', htr'', hc'', hw⟩ := henv.lookupDef_wf hP hkind
    have hV : ci'.toVConstant = ci''.toVConstant := Option.some.inj (hc'.symm.trans hc'')
    have hv : ci'.value = ci''.value := TrS.det htr.2.2 htr''.2.2
    have hw' : ci'.WF venv := by
      unfold VDefVal.WF
      rw [hv, show ci'.uvars = ci''.uvars from congrArg VConstant.uvars hV,
        show ci'.type = ci''.type from congrArg VConstant.type hV]
      exact hw
    exact ⟨_, SrcEval.delta_thm_step hc' hp hw' hls hlen'⟩

/-- The `beta` rule preserves translation and typing: the argument's value has the λ's own domain
(unique typing, `l4l Theory/Typing/UniqueTyping.lean:13`, and Π-injectivity,
`l4l Theory/Typing/Injectivity.lean:23`), so lean4lean's β rule
(`l4l Theory/Typing/Basic.lean:45`) and `TrS.inst` apply. Reference: the `eval_beta` case of
`subject_reduction_eval` (`MR P/PCUICClassification.v:1093`). -/
theorem SrcEval.beta_step (henv : ProgEnv P venv)
    (ihf : ∀ {e' T}, TrS venv Us [] f e' → venv.HasType Us.length [] e' T →
      ∃ v', TrS venv Us [] (.lam n A b bi) v' ∧ venv.IsDefEq Us.length [] e' v' T)
    (iha : ∀ {e' T}, TrS venv Us [] a e' → venv.HasType Us.length [] e' T →
      ∃ v', TrS venv Us [] a' v' ∧ venv.IsDefEq Us.length [] e' v' T)
    (ihb : ∀ {e' T}, TrS venv Us [] (b.instantiate1' a') e' → venv.HasType Us.length [] e' T →
      ∃ v', TrS venv Us [] v v' ∧ venv.IsDefEq Us.length [] e' v' T)
    (he : TrS venv Us [] (.app f a) e') (hT : venv.HasType Us.length [] e' T) :
    ∃ v', TrS venv Us [] v v' ∧ venv.IsDefEq Us.length [] e' v' T := by
  have hwf := henv.wf
  have hord := henv.ordered
  let .app h1 h2 hf ha := he
  have ⟨_, hvf, hdf⟩ := ihf hf h1
  let .lam (ty' := A') (body' := b') hA' _ hb := hvf
  have ⟨_, htra, hda⟩ := iha ha h2
  have ⟨_, ⟨_, hb'⟩⟩ := VEnv.HasType.lam_inv hord trivial hdf.hasType.2
  have ⟨_, hA'⟩ := hA'
  have ⟨_, hpi⟩ := hdf.hasType.2.uniq hwf trivial (.lamDF hA' hb')
  have ⟨⟨_, hdom⟩, _⟩ := VEnv.IsDefEqU.forallE_inv hwf trivial ⟨_, hpi⟩
  have hva : venv.HasType Us.length [] _ A' := .defeqDF hdom hda.hasType.2
  have hd := hT.trans_l hwf trivial (.appDF hdf hda) |>.trans_l hwf trivial (.beta hb' hva)
  have ⟨v', hv, hdv⟩ := ihb (TrS.inst (Δ := []) hord hva hb htra) hd.hasType.2
  exact ⟨v', hv, hd.trans hdv⟩

/-- The `zeta` rule preserves translation and typing: the body's translation under the `let`
entry of the value's translation moves to the entry of the evaluated value's (`TrS.defeqDFC`,
`TrS.uniq`), where `TrS.inst_let` substitutes it. Reference: the `eval_zeta` case of
`subject_reduction_eval` (`MR P/PCUICClassification.v:1093`). -/
theorem SrcEval.zeta_step (henv : ProgEnv P venv)
    (ihv : ∀ {e' T}, TrS venv Us [] val e' → venv.HasType Us.length [] e' T →
      ∃ v', TrS venv Us [] val' v' ∧ venv.IsDefEq Us.length [] e' v' T)
    (ihb : ∀ {e' T}, TrS venv Us [] (b.instantiate1' val') e' → venv.HasType Us.length [] e' T →
      ∃ v', TrS venv Us [] v v' ∧ venv.IsDefEq Us.length [] e' v' T)
    (he : TrS venv Us [] (.letE n ty val b nd) e') (hT : venv.HasType Us.length [] e' T) :
    ∃ v', TrS venv Us [] v v' ∧ venv.IsDefEq Us.length [] e' v' T := by
  have hwf := henv.wf
  have hord := henv.ordered
  let .letE h1 _ hv hb := he
  have ⟨vv, hvv, hdv⟩ := ihv hv h1
  have ⟨_, hty⟩ := h1.isType hord trivial
  have hΔ : VLCtx.IsDefEq venv Us.length [(none, .vlet _ _)] [(none, .vlet _ vv)] :=
    .cons .nil nofun (.vlet hdv hty)
  have ⟨e₂, hb₂⟩ := TrS.defeqDFC hwf hΔ hb
  have hd := (TrS.uniq hwf hΔ hb hb₂).of_l hwf trivial hT
  have ⟨v', hv', hdv'⟩ := ihb (TrS.inst_let hord hb₂ hvv) hd.hasType.2
  exact ⟨v', hv', hd.trans hdv'⟩

/-- The `delta` rule preserves translation and typing (`SrcEval.unfold_step`). Reference: the
`eval_delta` case of `subject_reduction_eval` (`MR P/PCUICClassification.v:1093`). -/
theorem SrcEval.delta_step (henv : ProgEnv P venv) (hsub : SubEnv σ.decls P)
    (hu : σ.unfold? c = some (ci, body))
    (ihb : ∀ {e' T}, TrS venv Us [] (Pure.instLevels ci.levelParams us body) e' →
      venv.HasType Us.length [] e' T →
      ∃ v', TrS venv Us [] v v' ∧ venv.IsDefEq Us.length [] e' v' T)
    (he : TrS venv Us [] (.const c us) e') (hT : venv.HasType Us.length [] e' T) :
    ∃ v', TrS venv Us [] v v' ∧ venv.IsDefEq Us.length [] e' v' T := by
  have hwf := henv.wf
  have ⟨_, hb, hd⟩ := SrcEval.unfold_step henv hsub hu he
  have hd := hd.of_l hwf trivial hT
  have ⟨v', hv', hdv'⟩ := ihb hb hd.hasType.2
  exact ⟨v', hv', hd.trans hdv'⟩

/-- The `fixApp` rule preserves translation and typing: the recursive constant the head evaluates
to is δ-equal to its value (its defining equation, for a block member the block's,
`VDecl.WF.mutualDef` at `l4l Theory/Typing/Env.lean:27`, through `SrcEval.unfold_step`), and
application respects definitional equality (`appDF`, `l4l Theory/Typing/Basic.lean:32`).
Reference: the `eval_fix` case of `subject_reduction_eval` (`MR P/PCUICClassification.v:1093`). -/
theorem SrcEval.fixApp_step (henv : ProgEnv P venv) (hsub : SubEnv σ.decls P)
    (hu : σ.unfold? c = some (ci, body))
    (ihf : ∀ {e' T}, TrS venv Us [] f e' → venv.HasType Us.length [] e' T →
      ∃ v', TrS venv Us [] (.const c us) v' ∧ venv.IsDefEq Us.length [] e' v' T)
    (iha : ∀ {e' T}, TrS venv Us [] a e' → venv.HasType Us.length [] e' T →
      ∃ v', TrS venv Us [] a' v' ∧ venv.IsDefEq Us.length [] e' v' T)
    (ihb : ∀ {e' T}, TrS venv Us [] (.app (Pure.instLevels ci.levelParams us body) a') e' →
      venv.HasType Us.length [] e' T →
      ∃ v', TrS venv Us [] v v' ∧ venv.IsDefEq Us.length [] e' v' T)
    (he : TrS venv Us [] (.app f a) e') (hT : venv.HasType Us.length [] e' T) :
    ∃ v', TrS venv Us [] v v' ∧ venv.IsDefEq Us.length [] e' v' T := by
  have hwf := henv.wf
  let .app h1 h2 hf ha := he
  have ⟨_, hvf, hdf⟩ := ihf hf h1
  have ⟨_, hb, hdl⟩ := SrcEval.unfold_step henv hsub hu hvf
  have hfb := hdf.transU_l hwf trivial hdl
  have ⟨_, hva, hda⟩ := iha ha h2
  have hd := hT.trans_l hwf trivial (.appDF hfb hda)
  have ⟨v', hv', hdv'⟩ := ihb (.app hfb.hasType.2 hda.hasType.2 hb hva) hd.hasType.2
  exact ⟨v', hv', hd.trans hdv'⟩

/-- The `appCong` rule preserves translation and typing: application respects definitional
equality (`appDF`, `l4l Theory/Typing/Basic.lean:32`). Reference: the `eval_app_cong` case of
`subject_reduction_eval` (`MR P/PCUICClassification.v:1093`). -/
theorem SrcEval.appCong_step (henv : ProgEnv P venv)
    (ihf : ∀ {e' T}, TrS venv Us [] f e' → venv.HasType Us.length [] e' T →
      ∃ v', TrS venv Us [] f' v' ∧ venv.IsDefEq Us.length [] e' v' T)
    (iha : ∀ {e' T}, TrS venv Us [] a e' → venv.HasType Us.length [] e' T →
      ∃ v', TrS venv Us [] a' v' ∧ venv.IsDefEq Us.length [] e' v' T)
    (he : TrS venv Us [] (.app f a) e') (hT : venv.HasType Us.length [] e' T) :
    ∃ v', TrS venv Us [] (.app f' a') v' ∧ venv.IsDefEq Us.length [] e' v' T := by
  have hwf := henv.wf
  let .app h1 h2 hf ha := he
  have ⟨_, hvf, hdf⟩ := ihf hf h1
  have ⟨_, hva, hda⟩ := iha ha h2
  exact ⟨_, .app hdf.hasType.2 hda.hasType.2 hvf hva, hT.trans_l hwf trivial (.appDF hdf hda)⟩

end

end EraseProof
