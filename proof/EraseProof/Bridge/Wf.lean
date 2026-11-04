import EraseProof.Bridge.Proj
import Metalean.Typing.Inversion

/-!
# Typed translations of applications

The translation of an application whose head the translator does not saturate is the Metalean
application of the translations of its parts, and the parts of a typed application are typed
(`TrM.wf_app`, by `Defeq.app_inv`, `ML Typing/Inversion.lean:494`).
-/

open Lean
open Metalean (Defeq EnvWF)

namespace EraseProof

/-- The parts of a typed translated application are typed. Reference: lean4lean `TrExprS.wf`
(`L4 Typing/Basic.lean:95`, its `app` case); `Defeq.app_inv` (`ML Typing/Inversion.lean:494`). -/
theorem TrM.wf_app {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {lps : List Name}
    {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n} {f a : Expr}
    {t T : Metalean.Expr ζ lps.length n} (_hE : EnvWF E) (_hΓ : E[Γ] ⊢ ok)
    (hns : ¬ SpecialHead B f) (he : TrM E B lps Γ Δ (.app f a) t) (ht : E[Γ] ⊢ t : T) :
    ∃ f' a', TrM E B lps Γ Δ f f' ∧ TrM E B lps Γ Δ a a' ∧ t = .app f' a' ∧
      (∃ F, E[Γ] ⊢ f' : F) ∧ ∃ A, E[Γ] ⊢ a' : A := by
  generalize hx : Expr.app f a = x at he
  cases he with
  | app _ hf ha =>
    cases hx
    obtain ⟨_, _, hf', ha', -⟩ := ht.app_inv
    exact ⟨_, _, hf, ha, rfl, ⟨_, hf'⟩, _, ha'⟩
  | @special c us _ _ _ as _ b _ hb hs =>
    have hfn : f.getAppFn = .const c us := by
      change (Expr.app f a).getAppFn = _
      rw [hx, mkAppN_eq_foldl, foldl_app_getAppFn]; rfl
    exact absurd ⟨c, us, b, hfn, hb, hs⟩ hns
  | _ => cases hx

end EraseProof
