import EraseProof.Source.Steps

/-!
# Subject reduction for source evaluation

`SrcEval.defeq`: a translated, typed closed term evaluates to a translated term that is
definitionally equal to it at its type. The induction on `SrcEval` takes one case per rule: the
step lemmas of `Source/Steps.lean` for `beta`, `zeta`, `delta`, `fixApp` and `appCong`, reflexivity
for the rules whose result is the term itself (`fixAtom`, `constAtom`, `atom`), and the
transparency of `mdata` in the translation.
-/

open Lean Lean4Lean Erasure

namespace EraseProof

section
variable {venv : VEnv} {P : List ConstantInfo} {σ : EvalEnv}

/-- Source evaluation is a typed definitional equality in the model (subject reduction for
evaluation). Reference: `wcbveval_red` (`MR P/PCUICClassification.v:916`) and
`subject_reduction_eval` (`:1093`); MC §5.4; Let. Lemma 2 (subject reduction). -/
theorem SrcEval.defeq (henv : ProgEnv P venv) (hsub : SubEnv σ.decls P)
    (he : TrS venv Us [] e e') (hT : venv.HasType Us.length [] e' T) (hev : SrcEval σ e v) :
    ∃ v', TrS venv Us [] v v' ∧ venv.IsDefEq Us.length [] e' v' T := by
  induction hev generalizing e' T with
  | beta _ _ _ ihf iha ihb => exact SrcEval.beta_step henv ihf iha ihb he hT
  | zeta _ _ ihv ihb => exact SrcEval.zeta_step henv ihv ihb he hT
  | delta hu _ _ _ ihb => exact SrcEval.delta_step henv hsub hu ihb he hT
  | fixAtom => exact ⟨_, he, hT⟩
  | fixApp _ hu _ _ _ ihf iha ihb => exact SrcEval.fixApp_step henv hsub hu ihf iha ihb he hT
  | constAtom => exact ⟨_, he, hT⟩
  | appCong _ _ _ ihf iha => exact SrcEval.appCong_step henv ihf iha he hT
  | mdata _ ih => let .mdata he := he; exact ih he hT
  | atom => exact ⟨_, he, hT⟩

end

end EraseProof
