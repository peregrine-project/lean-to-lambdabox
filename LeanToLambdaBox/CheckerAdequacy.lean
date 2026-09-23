import LeanToLambdaBox.RelevanceCheck
import Lean4Lean.Verify.TypeChecker
import Lean4Lean.Verify.NameGenerator

/-!
# Run-adequacy of the verified relevance check at an ambient local context

`RelevanceCheck.lean` proves `isErasable.WF`: lean4lean's *verified* relevance
check, when it returns `true` on a translated term, witnesses `Erasable`. But
that lemma is phrased against an abstract `VContext`/`VState`; the shipping
oracle actually executes `Lean4Lean.TypeChecker.M.run … (RecM.run (isErasable e))`
in the **ambient** `LocalContext` with the definition's `levelParams`.

lean4lean itself supplies that lift — `VContext.ofMLCtx`, `VState.WF.initial` and
`M.WF.run'`, each at an arbitrary ambient `MLCtx`; this file keeps only what it does not:

* `kernelNGen` — the kernel checker's initial name generator, named (the fork
  spells it out inline as `({} : Lean4Lean.TypeChecker.State).ngen`, definitionally
  the same value); `LeanToLambdaBox/Bridge.lean` and `ErasureSpec.lean` read it by
  this name;
* `LeanToLambdaBox.Oracle.kernel_isErasable_sound` — the payoff: a pure `M.run` of
  the verified check returning `.ok true` at a translated ambient `MLCtx` entails
  `Erasable`. Composition of `isErasable.WF` (soundness), `RecM.WF.run` (fuel), and
  the fork's own `M.WF.run'` (run-adequacy at the ambient context).

No new `axiom`/`sorry`: the trust inherited is exactly lean4lean's (its `Verify`
`sorryAx`, and its `Expr`/`Level`/`PersistentHashMap`/`PersistentArray` modeling axioms
surfaced through the executable checker).

What `Oracle.kernel_isErasable_sound` carries is the unique-typing cluster, together with
`Std.TreeMap.all_eq_all_toList` and `Lean.Level.isExplicitSubsumedAux_eq` from the
level-normalization path the executable checker walks. `doc/trust.md` holds the rows.
-/

namespace Lean4Lean.TypeChecker

open Lean hiding Environment Exception
open Kernel
open Lean4Lean
open LeanToLambdaBox (Erasable)

/-- The kernel type-checker's initial name generator (the default `State.ngen`,
`Lean4Lean.TypeChecker.State`). `Reserves` for this generator (`idx = 0`) holds
of every fvar *not* of the shape `⟨.num `_kernel_fresh i⟩` — in particular of
every `_uniq`-named runtime fvar. -/
def kernelNGen : NameGenerator := { namePrefix := `_kernel_fresh, idx := 0 }

end Lean4Lean.TypeChecker

namespace LeanToLambdaBox.Oracle

open Lean hiding Environment Exception
open Kernel
open Lean4Lean Lean4Lean.TypeChecker

/-- **The kernel path of the relevance oracle is sound.** A pure run of
lean4lean's *verified* relevance check (`LeanToLambdaBox.isErasable`) via
`M.run` at the ambient local context `m.lctx` with the declaration's `lparams`,
returning `.ok true` on a term `e` that translates to `ve`, witnesses that `ve`
is `Erasable`. Composition of `isErasable.WF` (soundness), `RecM.WF.run` (fuel),
and `M.WF.run'` (run-adequacy at the ambient context). -/
theorem kernel_isErasable_sound {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    {safety : DefinitionSafety} {lparams : List Name} {fuel : FuelConfig}
    {m : MLCtx} (mwf : m.WF (ves.venv safety) lparams)
    (hfresh : ∀ fv ∈ m.vlctx.fvars, kernelNGen.Reserves fv)
    {e : Expr} {ve : VExpr}
    (he : TrExprS (ves.venv safety) lparams m.vlctx e ve)
    (hrun : M.run env safety m.lctx lparams fuel
      (RecM.run (LeanToLambdaBox.isErasable e)) = .ok true) :
    Erasable (ves.venv safety) lparams.length m.vlctx.toCtx ve :=
  M.WF.run' wf mwf hfresh
    (RecM.WF.run
      (LeanToLambdaBox.isErasable.WF (c := .ofMLCtx wf safety lparams m mwf (fuel := fuel)) he))
    true hrun rfl

end LeanToLambdaBox.Oracle
