import LeanToLambdaBox.ErasesCorrect
import LeanToLambdaBox.ErasesCorrect.Delta
import LeanToLambdaBox.ErasesCorrect.Iota
import LeanToLambdaBox.ErasesCorrect.Proj

/-!
# Closing the simulation

`erases_correct` is `erases_correct_of_steps` with its three step hypotheses supplied by the
three arm files. A separate module rather than an edit to `ErasesCorrect.lean`, because the
arms import that aggregator's own dependencies and Lean rejects the cycle the other
arrangement needs.

The theorem's premises are MetaRocq's five — `env.WF`, the source term's typing, the source
evaluation, `Erases`, and `ErasesEnv` for `erases_deps` — plus `LowerEnv`, which carries the
pass layer MetaRocq has no analogue of, plus `UpstreamAsks env`, the lean4lean facts the pin
does not yet prove. `Erases` and `Lower` are two binders here because the statement names the
middle term, so the count is eight binders and seven premises. Nothing is added: each arm
reads what it needs off `ErasesEnv`'s seven clauses, off the source rule's own fields, and
off `UpstreamAsks`.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-- **T5.** The simulation, closed: source evaluation is reproduced by the emitted program,
on the composite of erasure with the pass, at the emitted environment. -/
theorem erases_correct {env : VEnv} {bo : Name → Option Expr} {Us : List Name}
    {fl : SEvalFlags} {Γspec Γ : GlobalDeclarations} :
    ErasesCorrectStmt env bo Us fl Γspec Γ :=
  erases_correct_of_steps step_iota step_proj step_delta

/-- **T5, folded.** The same simulation read through `ErasesLB`, with the environment
premise taken at whichever middle term the composite exhibits. -/
theorem erases_correct_lb {env : VEnv} {bo : Name → Option Expr} {Us : List Name}
    {fl : SEvalFlags} {Γspec Γ : GlobalDeclarations} :
    ErasesCorrectLBStmt env bo Us fl Γspec Γ := by
  intro e v ve t henv hwt hev hlb hspec henvL A
  obtain ⟨t₀, her, hlow⟩ := hlb
  obtain ⟨v₀, v', herv, hlowv, hevt⟩ :=
    erases_correct henv hwt hev her hlow (hspec t₀ her hlow) henvL A
  exact ⟨v', ⟨v₀, herv, hlowv⟩, hevt⟩

/-- **The capstone's `simulate` field, from T5.** `ErasureBridge.simulate` quantifies over
every subterm the applied statement reaches, where T5's `env.WF`, `TrExprS` and `ErasesEnv`
premises hold of the subject and not of the spine; the two quantified premises here are that
gap, named. The conclusion is the field's type, so this is what discharges it. -/
theorem simulate_of_erases_correct {env : VEnv} {bo : Name → Option Expr}
    {Γspec Γ : GlobalDeclarations} (hc : ErasesCorrectStmt env bo [] fullFlags Γspec Γ)
    (henv : env.WF) (henvL : LowerEnv Γspec Γ) (A : UpstreamAsks env)
    (hwt : ∀ {s t₀s : _}, Erases env [] [] s t₀s → ∃ ve, TrExprS env [] [] s ve)
    (hsp : ∀ {s t₀s : _}, Erases env [] [] s t₀s → ErasesEnv env bo Γspec t₀s) :
    ∀ {s t₀s ts v : _}, Erases env [] [] s t₀s → Lower Γspec t₀s ts →
      SEval env bo [] fullFlags [] s v →
      ∃ v₀ v', Erases env [] [] v v₀ ∧ Lower Γspec v₀ v' ∧ WcbvEval Γ eraseFlags ts v' := by
  intro s t₀s ts v her hlow hev
  obtain ⟨ve, hve⟩ := hwt her
  exact hc henv hve hev her hlow (hsp her) henvL A

end LeanToLambdaBox
