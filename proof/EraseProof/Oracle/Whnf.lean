import EraseProof.Env.Unfold
import EraseProof.Typing.Inst
import EraseProof.Typing.InstLevels
import EraseProof.Typing.Weak
import EraseProof.Oracle.Agree
import Lean4Lean.Theory.Typing.UniqueTyping

/-!
# Soundness of the oracle's weak-head reduction

`Pure.whnf_sound`: a successful run of `Erasure.Pure.whnf` on a translated, well-typed term returns
a translated term that is definitionally equal to it in lean4lean's model. The contexts are the
traversal's locals (`LocalsOK`, free-variable entries) under the de Bruijn entries of the binders
the oracle entered (`OracleCtx`).
-/

open Lean Lean4Lean Erasure

namespace EraseProof

/-- The traversal's locals mirror a lean4lean `VLCtx` with free-variable entries only. Reference:
`wf_local Σ Γ` for the context of `MR E/ErasureFunction.v:989 erase` (DV-13). -/
inductive LocalsOK (venv : VEnv) (Us : List Name) : List Local → VLCtx → Prop
  | nil : LocalsOK venv Us [] []
  | lam {Δ : VLCtx} : LocalsOK venv Us ls Δ → l.fvarId ∉ Δ.fvars → l.value? = none →
      TrS venv Us Δ l.type A' → venv.IsType Us.length Δ.toCtx A' →
      LocalsOK venv Us (l :: ls) ((some (l.fvarId, []), .vlam A') :: Δ)
  | letE {Δ : VLCtx} : LocalsOK venv Us ls Δ → l.fvarId ∉ Δ.fvars → l.value? = some val →
      TrS venv Us Δ l.type T' → TrS venv Us Δ val v' → venv.HasType Us.length Δ.toCtx v' T' →
      LocalsOK venv Us (l :: ls) ((some (l.fvarId, []), .vlet T' v') :: Δ)

/-- Contexts of the oracle: the traversal's locals (free-variable entries) under the de Bruijn
entries of the binders the oracle entered. Reference: the context `Γ` of `type_of_typing`
(`MR S/PCUICSafeRetyping.v:806`) extended under binders. -/
inductive OracleCtx (venv : VEnv) (Us : List Name) : List Expr → VLCtx → VLCtx → Prop
  | nil : OracleCtx venv Us [] Δ Δ
  | cons : OracleCtx venv Us Γ Δ₀ Δ → TrS venv Us Δ A A' → venv.IsType Us.length Δ.toCtx A' →
      OracleCtx venv Us (A :: Γ) Δ₀ ((none, .vlam A') :: Δ)

section
variable {venv : VEnv} {P : List ConstantInfo}

/-! ## Contexts -/

/-- A de Bruijn variable found in a context is below its number of de Bruijn entries. The `bvar`
case of lean4lean `TrExprS.closed` (`l4l Verify/Typing/Lemmas.lean:836`). Reference: none. -/
theorem VLCtx.find?_inl_lt : ∀ {Δ : VLCtx} {i : Nat} {e A : VExpr},
    Δ.find? (.inl i) = some (e, A) → i < Δ.bvars
  | [], _, _, _, h => by cases h
  | (none, _) :: _, 0, _, _, _ => Nat.succ_pos _
  | (none, _) :: _, _ + 1, _, _, h => by
    simp [VLCtx.find?, VLCtx.next, bind] at h
    obtain ⟨_, _, h, rfl, rfl⟩ := h
    have := find?_inl_lt h
    simpa [VLCtx.bvars] using Nat.succ_lt_succ this
  | (some _, _) :: _, _, _, _, h => by
    simp [VLCtx.find?, VLCtx.next, bind] at h
    obtain ⟨_, _, h, rfl, rfl⟩ := h
    have := find?_inl_lt h
    simpa [VLCtx.bvars] using this

/-- A translated term has no loose bound variable beyond the context's de Bruijn entries. Port of
lean4lean `TrExprS.closed` (`l4l Verify/Typing/Lemmas.lean:836`) without the `lit` and `proj`
cases. Reference: `subject_closed` (`MR pcuic/theories/Typing/PCUICClosedTyp.v:351`). -/
theorem TrS.closed (H : TrS venv Us Δ e e') : Closed e Δ.bvars := by
  induction H with
  | bvar h1 => exact VLCtx.find?_inl_lt h1
  | fvar | sort | const | mdata => trivial
  | app _ _ _ _ ih1 ih2
  | lam _ _ _ ih1 ih2
  | forallE _ _ _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | letE _ _ _ _ ih1 ih2 ih3 => exact ⟨ih1, ih2, ih3⟩

/-- The traversal's locals form a well-formed context of free-variable entries. Reference:
`wf_local Σ Γ` (`MR common/theories/EnvironmentTyping.v:2251`). -/
theorem LocalsOK.wf (hloc : LocalsOK venv Us ls Δ) :
    VLCtx.WF venv Us.length Δ ∧ Δ.NoBV := by
  induction hloc with
  | nil => exact ⟨trivial, rfl⟩
  | lam _ hf _ _ hA ih =>
    exact ⟨⟨ih.1, fun _ _ h => by cases h; exact ⟨hf, nofun⟩, hA⟩, ih.2⟩
  | letE _ hf _ _ _ hv ih =>
    exact ⟨⟨ih.1, fun _ _ h => by cases h; exact ⟨hf, nofun⟩, hv⟩, ih.2⟩

/-- The oracle's context is well formed over well-formed locals, and it lifts the locals' context
by one de Bruijn entry per binder the oracle entered. Reference: `wf_local Σ Γ`
(`MR common/theories/EnvironmentTyping.v:2251`) extended under binders. -/
theorem OracleCtx.wf (hΓ : OracleCtx venv Us Γ Δ₀ Δ) (h₀ : VLCtx.WF venv Us.length Δ₀) :
    VLCtx.WF venv Us.length Δ ∧ VLCtx.BVLift Δ₀ Δ Γ.length 0 Γ.length 0 := by
  induction hΓ with
  | nil => exact ⟨h₀, .refl⟩
  | cons _ _ hA ih => exact ⟨⟨(ih h₀).1, nofun, hA⟩, .skip _ (ih h₀).2⟩

/-- A term translated over the locals, with no loose bound variables, translates in the oracle's
context to the lifted image, by lean4lean's `TrExprS.weakBV` (`l4l Verify/Typing/Lemmas.lean:690`)
ported as `TrS.weakBV`. Reference: `weakening` (`MR P/Typing/PCUICWeakeningTyp.v:81`). -/
theorem OracleCtx.weak (henv : venv.Ordered) (hΓ : OracleCtx venv Us Γ Δ₀ Δ)
    (h₀ : VLCtx.WF venv Us.length Δ₀) (hc : Closed e) (H : TrS venv Us Δ₀ e e') :
    TrS venv Us Δ e (e'.liftN Γ.length) := by
  have := H.weakBV henv (hΓ.wf h₀).2
  rwa [Expr.liftLooseBVars_eq_self (by simpa using hc.looseBVarRange_le)] at this

/-- A term translated in the empty context translates in every oracle context, to the same
image. Reference: `weakening` (`MR P/Typing/PCUICWeakeningTyp.v:81`) of closed terms. -/
theorem TrS.weak_nil (henv : venv.Ordered) (hloc : LocalsOK venv Us ls Δ₀)
    (hΓ : OracleCtx venv Us Γ Δ₀ Δ) (H : TrS venv Us [] e e') : TrS venv Us Δ e e' := by
  have ⟨h₀, hnb⟩ := hloc.wf
  have hc : e'.ClosedN := (TrS.wf (Δ := []) henv trivial H).closedN henv trivial
  have H1 := H.weakFV henv (VLCtx.FVLift.from_nil hnb) h₀
  rw [hc.liftN_eq (Nat.zero_le _)] at H1
  have H2 := hΓ.weak henv h₀ (H.closed : Closed e 0) H1
  rwa [hc.liftN_eq (Nat.zero_le _)] at H2

/-- The value of a let-bound local translates to the image of its variable. Reference: the
premise of `red_rel` (`MR P/PCUICReduction.v:48`), a local definition read by `nth_error Γ`. -/
theorem LocalsOK.find_value (henv : venv.Ordered) (hloc : LocalsOK venv Us ls Δ)
    (hl : Pure.findLocal ls x = some l) (hv : l.value? = some v) :
    ∃ e₀ A₀, Δ.find? (.inr x) = some (e₀, A₀) ∧ TrS venv Us Δ v e₀ := by
  have hwf := hloc.wf.1
  induction hloc generalizing l with
  | nil => cases hl
  | @lam ls A' l0 Δ _ _ hnone _ _ ih =>
    simp only [Pure.findLocal, List.find?_cons] at hl
    cases hb : l0.fvarId == x with
    | true => rw [hb] at hl; cases hl; rw [hnone] at hv; cases hv
    | false =>
      rw [hb] at hl
      have ⟨e₀, A₀, h1, h2⟩ := ih hl hv hwf.1
      refine ⟨e₀.liftN 1, A₀.liftN 1, ?_, ?_⟩
      · simp [VLCtx.find?, VLCtx.next, hb, h1, VLocalDecl.depth]
      · simpa [VLocalDecl.depth] using h2.weakFV henv (.skip_fvar _ (.vlam A') .refl) hwf
  | @letE ls val T' v' l0 Δ _ _ hsome _ hval _ ih =>
    simp only [Pure.findLocal, List.find?_cons] at hl
    cases hb : l0.fvarId == x with
    | true =>
      rw [hb] at hl; cases hl; rw [hsome] at hv; cases hv
      refine ⟨v', T', ?_, ?_⟩
      · simp [VLCtx.find?, VLCtx.next, hb, VLocalDecl.value, VLocalDecl.type]
      · simpa [VLocalDecl.depth] using hval.weakFV henv (.skip_fvar _ (.vlet T' v') .refl) hwf
    | false =>
      rw [hb] at hl
      have ⟨e₀, A₀, h1, h2⟩ := ih hl hv hwf.1
      refine ⟨e₀, A₀, ?_, ?_⟩
      · simp [VLCtx.find?, VLCtx.next, hb, h1, VLocalDecl.depth]
      · simpa [VLocalDecl.depth] using h2.weakFV henv (.skip_fvar _ (.vlet T' v') .refl) hwf

/-! ## δ -/

/-- A definition of `P` has a translated definition in the model whose defining equation is a
definitional equality of the model. Reference: `declared_constant_inv`
(`MR P/Typing/PCUICWeakeningEnvTyp.v:252`), for a constant with a body. -/
theorem ProgEnv.lookupDefn (h : ProgEnv P venv) (hc : findDecl P c = some (.defnInfo v)) :
    ∃ ci' : VDefVal, TrDef venv venv (.defnInfo v) ci' ∧
      venv.constants c = some ci'.toVConstant ∧ venv.defeqs ci'.toDefEq := by
  induction h with
  | nil => simp [findDecl] at hc
  | «axiom» _ _ _ h2 ih =>
    have hle := VEnv.addConst_le h2
    rw [findDecl_cons] at hc
    split at hc
    · cases hc
    · have ⟨ci', h1, h2, h3⟩ := ih hc
      exact ⟨ci', h1.mono hle hle, hle.constants h2, hle.defeqs h3⟩
  | @defn _ _ _ venv' ci' _ _ htr _ h2 ih =>
    have hle : _ ≤ venv'.addDefEq ci'.toDefEq := (VEnv.addConst_le h2).trans VEnv.addDefEq_le
    rw [findDecl_cons] at hc
    split at hc
    · cases hc; subst c
      exact ⟨ci', htr.mono hle hle, VEnv.addDefEq_le.constants (VEnv.addConst_self h2),
        VEnv.addDefEq_self⟩
    · have ⟨ci', h1, h2, h3⟩ := ih hc
      exact ⟨ci', h1.mono hle hle, hle.constants h2, hle.defeqs h3⟩
  | thm _ _ _ _ _ h2 ih =>
    have hle := VEnv.addConst_le h2
    rw [findDecl_cons] at hc
    split at hc
    · cases hc
    · have ⟨ci', h1, h2, h3⟩ := ih hc
      exact ⟨ci', h1.mono hle hle, hle.constants h2, hle.defeqs h3⟩
  | «opaque» _ _ _ _ h2 ih =>
    have hle := VEnv.addConst_le h2
    rw [findDecl_cons] at hc
    split at hc
    · cases hc
    · have ⟨ci', h1, h2, h3⟩ := ih hc
      exact ⟨ci', h1.mono hle hle, hle.constants h2, hle.defeqs h3⟩
  | @block _ _ venv' vs cis' _ _ _ htr _ h2 _ ih =>
    have hleV : venv' ≤ venv'.addDefEqs cis' := VEnv.addDefEqs_le
    have hle : _ ≤ venv'.addDefEqs cis' := (VEnv.addConsts_le h2).trans hleV
    simp only [findDecl, List.find?_append] at hc
    cases hb : (vs.reverse.map ConstantInfo.defnInfo).find? (·.name == c) with
    | none =>
      rw [hb, Option.none_or] at hc
      have ⟨ci', h1, h2, h3⟩ := ih hc
      exact ⟨ci', h1.mono hle hle, hle.constants h2, hle.defeqs h3⟩
    | some d =>
      rw [hb, Option.some_or] at hc
      injection hc with hc
      subst hc
      have hn : (ConstantInfo.defnInfo v).name = c :=
        beq_iff_eq.1 (List.find?_some (p := fun x : ConstantInfo => x.name == c) hb)
      have hv : v ∈ vs := by simpa using List.mem_of_find?_eq_some hb
      subst hn
      have ⟨ci', hci', htr'⟩ := forall₂_exists_of_mem_left htr hv
      have hname : v.name = ci'.name := htr'.2.1
      refine ⟨ci', htr'.mono hle hleV, ?_, VEnv.addDefEqs_self hci'⟩
      rw [show (ConstantInfo.defnInfo v).name = ci'.name from hname]
      exact hleV.constants (VEnv.addConsts_constants h2 _ hci')

/-! ## The weak-head reduction -/

/-- `Erasure.Pure.whnf` computes a translated term definitionally equal to the input's image, in
the untyped form of lean4lean's `IsDefEqU`; β by `TrS.inst`, ζ by `TrS.inst_let` and the let-bound
locals of `LocalsOK`, δ by `ProgEnv.lookupDefn` and `TrS.instLevels`. Reference: `hnf_sound`
(`MR S/PCUICSafeReduce.v:1841`), through the rules `red_beta`, `red_zeta`, `red_rel` and
`red_delta` of `red1` (`MR P/PCUICReduction.v:38`). -/
theorem Pure.whnf_defeqU (henv : ProgEnv P venv) (hsub : SubEnv cx.decls P)
    (hloc : LocalsOK venv Us ls Δ₀) (hΓ : OracleCtx venv Us Γ Δ₀ Δ) :
    ∀ fuel e e' w, TrS venv Us Δ e e' → Pure.whnf cx fuel ls e = .ok w →
      ∃ w', TrS venv Us Δ w w' ∧ venv.IsDefEqU Us.length Δ.toCtx e' w' := by
  have hord := henv.ordered
  have hwf := henv.wf
  have ⟨h₀, _⟩ := hloc.wf
  have hΔ := (hΓ.wf h₀).1
  have hctx : OnCtx Δ.toCtx (venv.IsType Us.length) := hΔ.toCtx
  have refl {e e'} (he : TrS venv Us Δ e e') :
      ∃ w', TrS venv Us Δ e w' ∧ venv.IsDefEqU Us.length Δ.toCtx e' w' :=
    ⟨e', he, he.wf hord hΔ⟩
  intro fuel
  induction fuel with
  | zero => intro e e' w _ h; simp [Pure.whnf, throw, throwThe, MonadExceptOf.throw] at h
  | succ f ih =>
    intro e e' w he h
    cases he with
    | @app g' A1 B1 a' _ g a hg ha tg ta =>
      simp only [Pure.whnf] at h
      obtain ⟨r, h1, h2⟩ := Except.ok_of_bind h
      have ⟨r', tr, dr⟩ := ih _ _ r tg h1
      have dgr := dr.of_l hwf hctx hg
      split at h2
      · rename_i n t b bi
        cases tr with
        | @lam ty' _ _ _ body' _ _ hty tt tb =>
          have hlam := dgr.hasType.2
          have ⟨B2, hb⟩ := TrS.wf (Δ := (none, .vlam ty') :: Δ) hord ⟨hΔ, nofun, hty⟩ tb
          have ⟨u, hu⟩ := hty
          have hlam2 : venv.HasType Us.length Δ.toCtx (.lam ty' body') (.forallE ty' B2) :=
            VEnv.HasType.lam hu hb
          have ⟨⟨_, hA⟩, _⟩ := (hlam2.uniqU hwf hctx hlam).forallE_inv hwf hctx
          have ha' : venv.HasType Us.length Δ.toCtx a' ty' := .defeqDF hA.symm ha
          have ti := tb.inst hord ha' ta
          have ⟨w', tw, dw⟩ := ih _ _ w ti h2
          refine ⟨w', tw, ?_⟩
          have d1 : venv.IsDefEqU Us.length Δ.toCtx (.app g' a') (.app (.lam ty' body') a') :=
            ⟨_, .appDF dgr ha⟩
          have d2 : venv.IsDefEqU Us.length Δ.toCtx (.app (.lam ty' body') a') (body'.inst a') :=
            ⟨_, .beta hb ha'⟩
          exact (d1.trans hwf hctx d2).trans hwf hctx dw
      · cases h2
        exact ⟨.app r' a', .app dgr.hasType.2 ha tr ta, _, .appDF dgr ha⟩
    | letE hv _ tv tb =>
      simp only [Pure.whnf] at h
      exact ih _ _ w (tb.inst_let hord tv) h
    | mdata te =>
      simp only [Pure.whnf] at h
      exact ih _ _ w te h
    | fvar hf =>
      simp only [Pure.whnf] at h
      split at h
      · rename_i fv nm ty v hl
        have ⟨e₀, A₀, h1, h2⟩ := LocalsOK.find_value hord hloc hl rfl
        have hc : Closed v := by simpa [hloc.wf.2] using h2.closed
        have tv := hΓ.weak hord h₀ hc h2
        have h1' := VLCtx.BVLift.find? (hΓ.wf h₀).2 h1
        simp only [VLCtx.liftVar] at h1'
        rw [hf] at h1'
        cases h1'
        exact ih _ _ w tv h
      · cases h; exact refl (.fvar hf)
    | @const c ci0 us' _ us hc0 hus hlen =>
      simp only [Pure.whnf] at h
      split at h
      · rename_i v hv
        split at h
        · cases h; exact refl (.const hc0 hus hlen)
        · rename_i hl
          have hl : us.length = v.levelParams.length := by simpa using hl
          have hmem := List.mem_of_find?_eq_some hv
          have hname : (ConstantInfo.defnInfo v).name = c :=
            beq_iff_eq.1 (List.find?_some (p := fun x : ConstantInfo => x.name == c) hv)
          have hP := hsub _ hmem
          rw [hname] at hP
          have ⟨ci', ⟨⟨_, _⟩, hn, tval⟩, hc', hdf⟩ := henv.lookupDefn hP
          rw [hc'] at hc0
          cases hc0
          have t1 := tval.instLevels hus hl
          have t2 :
              TrS venv Us Δ (Pure.instLevels v.levelParams us v.value) (ci'.value.instL us') :=
            TrS.weak_nil hord hloc hΓ t1
          have ⟨w', tw, dw⟩ := ih _ _ w t2 h
          refine ⟨w', tw, ?_⟩
          have hls := VLevel.WF.of_mapM_ofLevel hus
          have hlen' : us'.length = ci'.uvars :=
            (List.mapM_eq_some.1 hus).length_eq.symm.trans hlen
          have d1 := VEnv.IsDefEq.extra (uvars := Us.length) (Γ := Δ.toCtx) hdf hls hlen'
          simp only [VDefVal.toDefEq, VExpr.instL, VLevel.inst_map_id hlen'] at d1
          have hn' : ci'.name = c := hn.symm.trans hname
          rw [hn'] at d1
          exact (VEnv.IsDefEqU.trans hwf hctx ⟨_, d1⟩ dw)
      · cases h; exact refl (.const hc0 hus hlen)
    | bvar hb => simp only [Pure.whnf] at h; cases h; exact refl (.bvar hb)
    | sort hu => simp only [Pure.whnf] at h; cases h; exact refl (.sort hu)
    | lam h1 h2 h3 => simp only [Pure.whnf] at h; cases h; exact refl (.lam h1 h2 h3)
    | forallE h1 h2 h3 h4 =>
      simp only [Pure.whnf] at h; cases h; exact refl (.forallE h1 h2 h3 h4)

/-- `whnf` computes a typed definitional equality. Reference: `hnf_sound`
(`MR S/PCUICSafeReduce.v:1841`). -/
theorem Pure.whnf_sound (henv : ProgEnv P venv) (hsub : SubEnv cx.decls P)
    (hloc : LocalsOK venv Us ls Δ₀) (hΓ : OracleCtx venv Us Γ Δ₀ Δ)
    (he : TrS venv Us Δ e e') (hT : venv.HasType Us.length Δ.toCtx e' A)
    (h : Pure.whnf cx fuel ls e = .ok w) :
    ∃ w', TrS venv Us Δ w w' ∧ venv.IsDefEq Us.length Δ.toCtx e' w' A := by
  have ⟨w', tw, dw⟩ := Pure.whnf_defeqU henv hsub hloc hΓ fuel e e' w he h
  exact ⟨w', tw, dw.of_l henv.wf (hΓ.wf hloc.wf.1).1.toCtx hT⟩

end

end EraseProof
