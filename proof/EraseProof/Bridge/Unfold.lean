import EraseProof.Bridge.WkEnv
import EraseProof.Bridge.Levels

/-!
# The δ equation

An unfoldable constant reduces in one Metalean step to the translation of its value at the
constant's levels (`ProgEnv.unfold`): the δ-step `ProgEnv.unfold_delta` with the universe
instantiation of translations `TrM.instLevels`. Reference: `eval_delta`
(`MR P/PCUICWcbvEval.v:247`); `WHRed.delta` (`ML Syntax/Reduction.lean:52`).
-/

open Lean Erasure
open Metalean (WHRed)

namespace EraseProof

variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P : List ConstantInfo}

/-- The δ equation: an unfoldable constant reduces to the translation of its instantiated value.
Reference: `eval_delta` (`MR P/PCUICWcbvEval.v:247`); `WHRed.delta`
(`ML Syntax/Reduction.lean:52`). -/
theorem ProgEnv.unfold {σ : EvalEnv} {c : Name} {ci : ConstantInfo} {b : Expr} {lps : List Name}
    {us : List Level} {t : Metalean.Expr ζ lps.length 0}
    (h : ProgEnv P ζ E B) (hsub : SubEnv σ.decls P)
    (hu : σ.unfold? c = some (ci, b)) (hc : TrM E B lps .nil [] (.const c us) t) :
    ∃ b', TrM E B lps .nil [] (Pure.instLevels ci.levelParams us b) b' ∧ E ⊢ t ⤳ b' := by
  obtain ⟨v, η, ls, rfl, rfl, -, hls, htr, hred⟩ := h.unfold_delta hsub hu hc
  exact ⟨_, TrM.instLevels hls htr, hred⟩

end EraseProof
