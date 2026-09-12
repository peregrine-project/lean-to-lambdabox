import LeanToLambdaBox.VisitExprRefines.Motives

/-!
# T8 — the shipping erasure refines the composite

`Erasure.visitExpr`'s output is the source term's erasure, lowered by the pass:
`VisitExprRefinesLB` says so outside a mutual block, `VisitExprRefinesLBFix` inside one, where
the block's own constants have already become its fix variables.

Both come from one fixpoint induction over the eighteen-member family. This module holds the
induction — the motives, the eighteen admissibility obligations and the aggregation — and takes
the eighteen steps as explicit hypotheses; each is proved in a file of its own against
`Motives.lean`'s stated interfaces rather than inside an in-progress induction's local context.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean Erasure Witness Lean.Order

set_option synthInstance.maxSize 4000

variable {lenv : Environment} {env : VEnv} {Us : List Name} {tbl : SourceTable}
  {cfg : ErasureConfig} {gw : Void IO.RealWorld → NameGenerator}

/-! ## The induction -/

/-- **The eighteen motives, at the shipping family.** One `partial_fixpoint` induction: the
admissibility obligations are the run-ok toolkit paired with `admissible_and_le`, which is all
the approximation conjunct costs, and the steps are hypotheses. -/
theorem motives_of_steps
    (step1 : Step1 lenv env Us tbl cfg gw)
    (step2 : Step2 lenv env Us tbl cfg gw)
    (step3 : Step3 lenv env Us tbl cfg gw)
    (step4 : Step4 lenv env Us tbl cfg gw)
    (step5 : Step5 lenv env Us tbl cfg gw)
    (step6 : Step6 lenv env Us tbl cfg gw)
    (step7 : Step7 lenv env Us tbl cfg gw)
    (step8 : Step8 lenv env Us tbl cfg gw)
    (step9 : Step9 lenv env Us tbl cfg gw)
    (step10 : Step10 lenv env Us tbl cfg gw)
    (step11 : Step11 lenv env Us tbl cfg gw)
    (step12 : Step12 lenv env Us tbl cfg gw)
    (step13 : Step13 lenv env Us tbl cfg gw)
    (step14 : Step14 lenv env Us tbl cfg gw)
    (step15 : Step15 lenv env Us tbl cfg gw)
    (step16 : Step16 lenv env Us tbl cfg gw)
    (step17 : Step17 lenv env Us tbl cfg gw)
    (step18 : Step18 lenv env Us tbl cfg gw)
    (P : ErasureSpec lenv env Us gw) (htbl : SourceTableAdequate lenv tbl)
    (hcfg : ConfigPinned cfg) (hcb : CompilerBodies lenv env tbl.body?) :
    Motives env Us tbl cfg gw
      Erasure.visitExpr Erasure.visitLiteral Erasure.visitConstructor Erasure.visitConst
      Erasure.get_constant_kername Erasure.visitMutual Erasure.visitAppArgs Erasure.visitLet
      Erasure.visitLambda Erasure.visitProj Erasure.visitApp Erasure.visitConstApp
      Erasure.visitCtorEta Erasure.visitCtorEtaGo Erasure.visitCasesEta Erasure.visitCasesEtaGo
      Erasure.visitCases Erasure.visitAlt := by
  have H :
      Motive1 env Us tbl cfg gw Erasure.visitExpr ∧
      Motive2 env Us tbl cfg gw Erasure.visitLiteral ∧
      Motive3 env Us tbl cfg gw Erasure.visitConstructor ∧
      Motive4 env Us tbl cfg gw Erasure.visitConst ∧
      Motive5 env Us tbl cfg gw Erasure.get_constant_kername ∧
      Motive6 env Us tbl cfg gw Erasure.visitMutual ∧
      Motive7 env Us tbl cfg gw Erasure.visitAppArgs ∧
      Motive8 env Us tbl cfg gw Erasure.visitLet ∧
      Motive9 env Us tbl cfg gw Erasure.visitLambda ∧
      Motive10 env Us tbl cfg gw Erasure.visitProj ∧
      Motive11 env Us tbl cfg gw Erasure.visitApp ∧
      Motive12 env Us tbl cfg gw Erasure.visitConstApp ∧
      Motive13 env Us tbl cfg gw Erasure.visitCtorEta ∧
      Motive14 env Us tbl cfg gw Erasure.visitCtorEtaGo ∧
      Motive15 env Us tbl cfg gw Erasure.visitCasesEta ∧
      Motive16 env Us tbl cfg gw Erasure.visitCasesEtaGo ∧
      Motive17 env Us tbl cfg gw Erasure.visitCases ∧
      Motive18 env Us tbl cfg gw Erasure.visitAlt := by
    apply Erasure.visitExpr.mutual_fixpoint_induct
      (motive_1 := Motive1 env Us tbl cfg gw)
      (motive_2 := Motive2 env Us tbl cfg gw)
      (motive_3 := Motive3 env Us tbl cfg gw)
      (motive_4 := Motive4 env Us tbl cfg gw)
      (motive_5 := Motive5 env Us tbl cfg gw)
      (motive_6 := Motive6 env Us tbl cfg gw)
      (motive_7 := Motive7 env Us tbl cfg gw)
      (motive_8 := Motive8 env Us tbl cfg gw)
      (motive_9 := Motive9 env Us tbl cfg gw)
      (motive_10 := Motive10 env Us tbl cfg gw)
      (motive_11 := Motive11 env Us tbl cfg gw)
      (motive_12 := Motive12 env Us tbl cfg gw)
      (motive_13 := Motive13 env Us tbl cfg gw)
      (motive_14 := Motive14 env Us tbl cfg gw)
      (motive_15 := Motive15 env Us tbl cfg gw)
      (motive_16 := Motive16 env Us tbl cfg gw)
      (motive_17 := Motive17 env Us tbl cfg gw)
      (motive_18 := Motive18 env Us tbl cfg gw)
    · exact admissible_and_le _ _ (eraseM_admissible_ok₁ _)
    · exact admissible_and_le _ _ (eraseM_admissible_ok₁ _)
    · exact admissible_and_le _ _ (eraseM_admissible_ok₂ _)
    · exact admissible_and_le _ _ (eraseM_admissible_ok₁ _)
    · exact admissible_and_le _ _ (eraseM_admissible_ok₁ _)
    · exact admissible_and_le _ _ (eraseM_admissible_ok₁ _)
    · exact admissible_and_le _ _ (eraseM_admissible_ok₂ _)
    · exact admissible_and_le _ _ (eraseM_admissible_ok₁ _)
    · exact admissible_and_le _ _ (eraseM_admissible_ok₁ _)
    · exact admissible_and_le _ _ (eraseM_admissible_ok₃ _)
    · exact admissible_and_le _ _ (eraseM_admissible_ok₁ _)
    · exact admissible_and_le _ _ (eraseM_admissible_ok₁ _)
    · exact admissible_and_le _ _ (eraseM_admissible_ok₃ _)
    · exact admissible_and_le _ _ (eraseM_admissible_ok₅ _)
    · exact admissible_and_le _ _ (eraseM_admissible_ok₂ _)
    · exact admissible_and_le _ _ (eraseM_admissible_ok₄ _)
    · exact admissible_and_le _ _ (eraseM_admissible_ok₂ _)
    · exact admissible_and_le _ _ (eraseM_admissible_ok₃ _)
    · intro vExpr vLit vLet vLam vProj vApp ih1 ih2 ih8 ih9 ih10 ih11
      exact step1 P htbl hcfg hcb vExpr vLit vLet vLam vProj vApp ih1 ih2 ih8 ih9 ih10 ih11
    · intro vCtor ih3
      exact step2 P htbl hcfg hcb vCtor ih3
    · intro vLit vConst vArgs ih2 ih4 ih7
      exact step3 P htbl hcfg hcb vLit vConst vArgs ih2 ih4 ih7
    · intro vGck ih5
      exact step4 P htbl hcfg hcb vGck ih5
    · intro vMut ih6
      exact step5 P htbl hcfg hcb vMut ih6
    · intro vExpr ih1
      exact step6 P htbl hcfg hcb vExpr ih1
    · intro vExpr ih1
      exact step7 P htbl hcfg hcb vExpr ih1
    · intro vExpr ih1
      exact step8 P htbl hcfg hcb vExpr ih1
    · intro vExpr ih1
      exact step9 P htbl hcfg hcb vExpr ih1
    · intro vExpr ih1
      exact step10 P htbl hcfg hcb vExpr ih1
    · intro vExpr vArgs vConstApp ih1 ih7 ih12
      exact step11 P htbl hcfg hcb vExpr vArgs vConstApp ih1 ih7 ih12
    · intro vConst vArgs vCtorEta vCasesEta ih4 ih7 ih13 ih15
      exact step12 P htbl hcfg hcb vConst vArgs vCtorEta vCasesEta ih4 ih7 ih13 ih15
    · intro vCtorEtaGo ih14
      exact step13 P htbl hcfg hcb vCtorEtaGo ih14
    · intro vCtor vCtorEtaGo ih3 ih14
      exact step14 P htbl hcfg hcb vCtor vCtorEtaGo ih3 ih14
    · intro vCasesEtaGo ih16
      exact step15 P htbl hcfg hcb vCasesEtaGo ih16
    · intro vCasesEtaGo vCases ih16 ih17
      exact step16 P htbl hcfg hcb vCasesEtaGo vCases ih16 ih17
    · intro vExpr vAlt ih1 ih18
      exact step17 P htbl hcfg hcb vExpr vAlt ih1 ih18
    · intro vExpr ih1
      exact step18 P htbl hcfg hcb vExpr ih1
  exact ⟨H.1, H.2.1, H.2.2.1, H.2.2.2.1, H.2.2.2.2.1, H.2.2.2.2.2.1, H.2.2.2.2.2.2.1, H.2.2.2.2.2.2.2.1, H.2.2.2.2.2.2.2.2.1, H.2.2.2.2.2.2.2.2.2.1, H.2.2.2.2.2.2.2.2.2.2.1, H.2.2.2.2.2.2.2.2.2.2.2.1, H.2.2.2.2.2.2.2.2.2.2.2.2.1, H.2.2.2.2.2.2.2.2.2.2.2.2.2.1, H.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, H.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, H.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, H.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-! ## T8

Both statements are read off motive 1 at the two fixvar modes. They are `01-DESIGN.md` §5's T8
with `RunConcl` and the generator bound *outside* the specification-environment quantifier,
which is where the induction needs them: a sub-run's state and generator facts have to be
available before any environment is chosen.
-/

/-- **T8 outside a mutual block.** A supported, translatable term whose erasure run succeeds at
a reader with no fixvar map is related to the emitted term by the composite, at every
specification environment of the final state. -/
abbrev VisitExprRefinesLB (env : VEnv) (Us : List Name) (tbl : SourceTable)
    (cfg : ErasureConfig) (gw : Void IO.RealWorld → NameGenerator) : Prop :=
  ∀ {e : Expr} {ve : VExpr} {Δ : VLCtx} {s s' : ErasureState} {ctx : ErasureContext}
    {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {t : LBTerm},
    TrExprS env Us Δ e ve → Supported env tbl e → ctx.fixvars = none →
    Erasure.visitExpr e s ctx cctx ref w = .ok (t, s') w' →
    BridgeInv env Us cfg (gw w) ctx s Δ →
    ∀ Γspec, SpecEnv env tbl.body? s' Γspec →
      ErasesLB env Us Γspec Δ e t ∧ RunConcl s s' ∧ gw w ≤ gw w'

/-- **T8 inside a mutual block.** The same run under the reader `Erasure.visitMutual` installs
for a block: the emitted term carries the block's fix variables where the source names its own
members, which is the third factor `ErasesLBFix` adds. The freshness discipline the block's
identifiers obey is `BridgeInv.fixvars`, so it is not a separate premise. -/
abbrev VisitExprRefinesLBFix (env : VEnv) (Us : List Name) (tbl : SourceTable)
    (cfg : ErasureConfig) (gw : Void IO.RealWorld → NameGenerator) : Prop :=
  ∀ {e : Expr} {ve : VExpr} {Δ : VLCtx} {s s' : ErasureState} {ctx : ErasureContext}
    {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {t : LBTerm} {nms : List Name} {ids : List FVarId},
    TrExprS env Us Δ e ve → Supported env tbl e →
    ctx.fixvars = some (fixvarMap nms ids) →
    Erasure.visitExpr e s ctx cctx ref w = .ok (t, s') w' →
    BridgeInv env Us cfg (gw w) ctx s Δ →
    ∀ Γspec, SpecEnv env tbl.body? s' Γspec →
      ErasesLBFix env Us Γspec (nms.map toKername) ids Δ e t ∧ RunConcl s s' ∧ gw w ≤ gw w'

/-- **T8, ambient mode.** Motive 1 of the induction, read at `ctx.fixvars = none`. -/
theorem visitExpr_refines_erasesLB
    (step1 : Step1 lenv env Us tbl cfg gw)
    (step2 : Step2 lenv env Us tbl cfg gw)
    (step3 : Step3 lenv env Us tbl cfg gw)
    (step4 : Step4 lenv env Us tbl cfg gw)
    (step5 : Step5 lenv env Us tbl cfg gw)
    (step6 : Step6 lenv env Us tbl cfg gw)
    (step7 : Step7 lenv env Us tbl cfg gw)
    (step8 : Step8 lenv env Us tbl cfg gw)
    (step9 : Step9 lenv env Us tbl cfg gw)
    (step10 : Step10 lenv env Us tbl cfg gw)
    (step11 : Step11 lenv env Us tbl cfg gw)
    (step12 : Step12 lenv env Us tbl cfg gw)
    (step13 : Step13 lenv env Us tbl cfg gw)
    (step14 : Step14 lenv env Us tbl cfg gw)
    (step15 : Step15 lenv env Us tbl cfg gw)
    (step16 : Step16 lenv env Us tbl cfg gw)
    (step17 : Step17 lenv env Us tbl cfg gw)
    (step18 : Step18 lenv env Us tbl cfg gw)
    (P : ErasureSpec lenv env Us gw) (htbl : SourceTableAdequate lenv tbl)
    (hcfg : ConfigPinned cfg) (hcb : CompilerBodies lenv env tbl.body?) :
    VisitExprRefinesLB env Us tbl cfg gw := by
  intro e ve Δ s s' ctx cctx ref w w' t hwt hsup hfx hrun hinv Γspec hspec
  have M := motives_of_steps
    step1 step2 step3 step4 step5 step6 step7 step8 step9 step10 step11 step12 step13 step14
    step15 step16 step17 step18
    P htbl hcfg hcb
  obtain ⟨hm, -⟩ := M.motive1
  obtain ⟨hrc, hle, hmode⟩ := hm e s ctx cctx ref w t s' w' hrun Δ hinv hsup ⟨ve, hwt⟩
  exact ⟨(hmode Γspec hspec).ambient hfx, hrc, hle⟩

/-- **T8, block mode.** Motive 1 of the induction, read at a reader carrying a block's map. -/
theorem visitExpr_refines_erasesLBFix
    (step1 : Step1 lenv env Us tbl cfg gw)
    (step2 : Step2 lenv env Us tbl cfg gw)
    (step3 : Step3 lenv env Us tbl cfg gw)
    (step4 : Step4 lenv env Us tbl cfg gw)
    (step5 : Step5 lenv env Us tbl cfg gw)
    (step6 : Step6 lenv env Us tbl cfg gw)
    (step7 : Step7 lenv env Us tbl cfg gw)
    (step8 : Step8 lenv env Us tbl cfg gw)
    (step9 : Step9 lenv env Us tbl cfg gw)
    (step10 : Step10 lenv env Us tbl cfg gw)
    (step11 : Step11 lenv env Us tbl cfg gw)
    (step12 : Step12 lenv env Us tbl cfg gw)
    (step13 : Step13 lenv env Us tbl cfg gw)
    (step14 : Step14 lenv env Us tbl cfg gw)
    (step15 : Step15 lenv env Us tbl cfg gw)
    (step16 : Step16 lenv env Us tbl cfg gw)
    (step17 : Step17 lenv env Us tbl cfg gw)
    (step18 : Step18 lenv env Us tbl cfg gw)
    (P : ErasureSpec lenv env Us gw) (htbl : SourceTableAdequate lenv tbl)
    (hcfg : ConfigPinned cfg) (hcb : CompilerBodies lenv env tbl.body?) :
    VisitExprRefinesLBFix env Us tbl cfg gw := by
  intro e ve Δ s s' ctx cctx ref w w' t nms ids hwt hsup hfx hrun hinv Γspec hspec
  have M := motives_of_steps
    step1 step2 step3 step4 step5 step6 step7 step8 step9 step10 step11 step12 step13 step14
    step15 step16 step17 step18
    P htbl hcfg hcb
  obtain ⟨hm, -⟩ := M.motive1
  obtain ⟨hrc, hle, hmode⟩ := hm e s ctx cctx ref w t s' w' hrun Δ hinv hsup ⟨ve, hwt⟩
  exact ⟨(hmode Γspec hspec).block hfx, hrc, hle⟩

/-- The ambient statement, unfolded, so that a reader need not trust the abbreviation. -/
theorem visitExpr_refines_erasesLB_shape :
    VisitExprRefinesLB env Us tbl cfg gw ↔
      ∀ {e : Expr} {ve : VExpr} {Δ : VLCtx} {s s' : ErasureState} {ctx : ErasureContext}
        {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
        {t : LBTerm},
        TrExprS env Us Δ e ve → Supported env tbl e → ctx.fixvars = none →
        Erasure.visitExpr e s ctx cctx ref w = .ok (t, s') w' →
        BridgeInv env Us cfg (gw w) ctx s Δ →
        ∀ Γspec, SpecEnv env tbl.body? s' Γspec →
          ErasesLB env Us Γspec Δ e t ∧ RunConcl s s' ∧ gw w ≤ gw w' :=
  Iff.rfl

/-- The block statement, unfolded. -/
theorem visitExpr_refines_erasesLBFix_shape :
    VisitExprRefinesLBFix env Us tbl cfg gw ↔
      ∀ {e : Expr} {ve : VExpr} {Δ : VLCtx} {s s' : ErasureState} {ctx : ErasureContext}
        {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
        {t : LBTerm} {nms : List Name} {ids : List FVarId},
        TrExprS env Us Δ e ve → Supported env tbl e →
        ctx.fixvars = some (fixvarMap nms ids) →
        Erasure.visitExpr e s ctx cctx ref w = .ok (t, s') w' →
        BridgeInv env Us cfg (gw w) ctx s Δ →
        ∀ Γspec, SpecEnv env tbl.body? s' Γspec →
          ErasesLBFix env Us Γspec (nms.map toKername) ids Δ e t ∧ RunConcl s s' ∧
            gw w ≤ gw w' :=
  Iff.rfl


end LeanToLambdaBox
