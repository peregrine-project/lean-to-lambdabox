import EraseProof.Spec
import ConLeche.Model.Fold
import ConLeche.Model.Capstone
import ConLeche.Model.Rules.Recompose
import ConLeche.Semantics.DeclWF

/-!
# What con-leche's acceptance of the program gives

From `ConLecheAccepts P env` (con-leche's pure fold accepts `P`'s records with environment `env`):
the environment is well formed, has a model in every `[SetTheory V]`, and in every model con-leche's
five claims hold at every level valuation and fuel: its reduction, definitional equality and
inference preserve denotations.
-/

open Lean Erasure

namespace EraseProof

universe w

/-- What con-leche proves of an environment its pure fold returns: `wf`, the syntactic
well-formedness of every stored constant and table (`CL ConLeche/Verify/EnvWF.lean:244 EnvWF`);
`model`, a model in every `[SetTheory V]` (`CL ConLeche/Model/Env/EnvModelM.lean:244 EnvModelM`);
`claims`, in every model, at every level valuation and fuel, the claims of con-leche's head
normalisation, reduction loop, definitional equality and inference at both grades
(`CL ConLeche/Model/Claims.lean:52 WhnfCoreClaim`, `:70`, `:90`, `:112`;
`CL ConLeche/Model/ClaimsIO.lean:75 InferClaimIO`). Reference: `wf_ext Σ` (`MR P/PCUICTyping.v:507`)
and the soundness of conversion and typing in the model (MC §5); DV-3. -/
structure CLAccepted (env : ConLeche.Env) : Prop where
  wf : ConLeche.EnvWF env
  model : ∀ (V : Type w) [ConLeche.SetTheory V], Nonempty (ConLeche.Model.EnvModelM V env)
  claims : ∀ (V : Type w) [ConLeche.SetTheory V] (m : ConLeche.Model.EnvModelM V env)
    (φ : ConLeche.LevelParam → Nat) (fuel : Nat),
    ConLeche.Model.WhnfCoreClaim m.base2 φ fuel ∧ ConLeche.Model.WhnfClaim m.base2 φ fuel ∧
      ConLeche.Model.DefEqClaim m.base2 φ fuel ∧ ConLeche.Model.InferClaim m.base2 φ fuel ∧
      ConLeche.Model.InferClaimIO m.base2 φ fuel

/-- con-leche's acceptance of `P` gives `CLAccepted env`: `wf` by
`CL ConLeche/Semantics/DeclWF.lean:319 checkDeclsPure_envWF`, `model` by
`CL ConLeche/Model/Fold.lean:373 checkDeclsPure_sound_of`, `claims` by
`CL ConLeche/Model/Rules/Recompose.lean:49 checkSoundAtP5` at the environment inputs
`CL ConLeche/Model/Capstone.lean:155 Rules.RulesInputs.ofSem` of the model. Reference:
`MR P/PCUICTyping.v:507 wf_ext`; DV-3. -/
theorem ConLecheAccepts.accepted {P : List ConstantInfo} {env : ConLeche.Env}
    (h : ConLecheAccepts P env) : CLAccepted.{w} env := by
  obtain ⟨ds, -, hf, -⟩ := h
  exact ⟨ConLeche.Semantics.checkDeclsPure_envWF hf,
    fun _ _ => ConLeche.Model.checkDeclsPure_sound_of hf,
    fun _ _ m φ => ConLeche.Model.Rules.checkSoundAtP5 (ConLeche.Model.Rules.RulesInputs.ofSem m φ)⟩

end EraseProof
