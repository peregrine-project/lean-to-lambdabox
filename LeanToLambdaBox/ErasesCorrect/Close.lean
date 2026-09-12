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

The theorem stands with its seven binders and the eighth, `UpstreamAsks env`, **plus one
named premise**, `StepPremises`. Its six fields are not a design choice: each is a fact the
specification relations state in the wrong direction, or a datum a source rule leaves free,
and each was reported with its own repair by the unit that hit it —

* `fwd`, `elims` — `ErasesEnv.decls` reads *entry ⇒ justified*, and the `ctorVal`, `beta`
  and ι arms need *justified ⇒ entry* at a block and at an eliminator key;
* `indSpine` — upstream ask 6 refutes `Erasable`'s type-former disjunct only, and the proof
  disjunct at an informative inductive spine is a second kernel fact;
* `elimTyping` — `CasesOnShape` constrains a name and a block, not the eliminator's type,
  so the major premise's typing and the constructor value's saturation come from outside;
* `proj` — `Erases.proj` carries no relevance side condition and `SEval.proj` classifies
  neither the head of the discriminant's value nor its parameter count;
* `tabled` — nothing in `SEval.deltaC` excludes a tabled constant that is a constructor.

Each retires by a repair in the file that owns the relation, not by a proof here; until then
the bundle is what the arms honestly need, gathered under one name so that
`erases_correct`'s statement stays §5's.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-- The premises the three arms take beyond `erases_correct`'s own binders. -/
structure StepPremises (env : VEnv) (bo : Name → Option Expr) (Us : List Name)
    (fl : SEvalFlags) (Γspec : GlobalDeclarations) : Prop where
  /-- The forward readings of the specification environment at a block and at an
      eliminator spine (`ErasesCorrect/Steps.lean`). -/
  fwd : ErasesEnvFwd env bo Us fl Γspec
  /-- A spine headed by an informative inductive type former is not a proposition. -/
  indSpine : IndSpineNotProp env
  /-- A reached `casesOn` constant's kername is a runtime key carrying that eliminator's
      declaration. -/
  elims : SpecElims env Γspec
  /-- The source-theory typing of an eliminator spine and of a constructor value. -/
  elimTyping : ElimTyping env Us
  /-- What `Erases.proj` and `SEval.proj` leave open at a projection. -/
  proj : ProjSpec env Us Γspec
  /-- No tabled constant is a constructor. -/
  tabled : TabledNotCtor env bo

/-- **T5.** The simulation, closed: source evaluation is reproduced by the emitted program,
on the composite of erasure with the pass, at the emitted environment. -/
theorem erases_correct {env : VEnv} {bo : Name → Option Expr} {Us : List Name}
    {fl : SEvalFlags} {Γspec Γ : GlobalDeclarations} (H : StepPremises env bo Us fl Γspec) :
    ErasesCorrectStmt env bo Us fl Γspec Γ :=
  erases_correct_of_steps H.fwd
    (step_iota_of_elimSpec H.indSpine H.elims H.elimTyping)
    (step_proj_of_projSpec H.indSpine H.fwd H.proj)
    (step_delta H.tabled)

/-- **T5, folded.** The same simulation read through `ErasesLB`, with the environment
premise taken at whichever middle term the composite exhibits. -/
theorem erases_correct_lb {env : VEnv} {bo : Name → Option Expr} {Us : List Name}
    {fl : SEvalFlags} {Γspec Γ : GlobalDeclarations} (H : StepPremises env bo Us fl Γspec) :
    ErasesCorrectLBStmt env bo Us fl Γspec Γ := by
  intro e v ve t henv hwt hev hlb hspec henvL A
  obtain ⟨t₀, her, hlow⟩ := hlb
  obtain ⟨v₀, v', herv, hlowv, hevt⟩ :=
    erases_correct H henv hwt hev her hlow (hspec t₀ her hlow) henvL A
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
