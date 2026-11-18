import EraseProof.Core.NonRec
import LeanToLambdaBox.Erasure.Entry

/-!
# Glue between the entry point and the pure path

- `eraseEntry_pure`: when the fragment test accepts the input, a result of the `#erase` entry
  point `Erasure.eraseEntry` is a result of the pure path `Erasure.erasePure`. The `CoreM` lemmas
  it needs (`CoreM.pure_inj`, `CoreM.throwError_ne_pure`, `EIO.bind_err`) run a `CoreM` action at
  an arbitrary context, state reference and world token (`someCtx`, `someRef`, `someW`).
-/

open Lean Erasure

namespace EraseProof

/-! ## `#erase` and the pure path -/

/-- An arbitrary `CoreM` context. -/
noncomputable def someCtx : Core.Context := Classical.choice inferInstance
/-- An arbitrary `CoreM` state reference. -/
noncomputable def someRef : ST.Ref IO.RealWorld Core.State := Classical.choice inferInstance
/-- An arbitrary world token. -/
noncomputable def someW : Void IO.RealWorld := Classical.choice inferInstance

/-- `pure` is injective in `CoreM`. Reference: `L4 Core/Glue.lean:34`. -/
theorem CoreM.pure_inj {α} {a b : α} (h : (pure a : CoreM α) = pure b) : a = b := by
  have h' := congrFun (congrFun (congrFun h someCtx) someRef) someW
  injection h'

/-- An `EIO` bind whose continuation always fails always fails. Reference:
`L4 Core/Glue.lean:39`. -/
theorem EIO.bind_err {ε α β : Type} (x : EIO ε β) (f : β → EIO ε α)
    (hf : ∀ b s, ∃ e s', f b s = .error e s') (s : Void IO.RealWorld) :
    ∃ e s', (x >>= f) s = .error e s' := by
  show ∃ e s', (EST.bind x f) s = _
  simp only [EST.bind]
  split
  · exact hf _ _
  · exact ⟨_, _, rfl⟩

/-- An error is not a result in `CoreM`. Reference: `L4 Core/Glue.lean:49`. -/
theorem CoreM.throwError_ne_pure {α} {a : α} {m : MessageData} :
    (Lean.throwError m : CoreM α) ≠ pure a := by
  intro h
  have h' := congrFun (congrFun (congrFun h someCtx) someRef) someW
  have : ∃ e s', (Lean.throwError m : CoreM α) someCtx someRef someW = .error e s' := by
    simp only [Lean.throwError, bind, ReaderT.bind, getRef, MonadRef.getRef]
    apply EIO.bind_err
    intro r s
    apply EIO.bind_err
    intro r s
    exact ⟨_, _, rfl⟩
  obtain ⟨e, s', he⟩ := this
  rw [h'] at he
  cases he

/-- When the fragment test accepts the input, a returning run of the `#erase` entry point is a run
of the pure path. Reference: `L4 Core/Glue.lean:67`. -/
theorem eraseEntry_pure {view : EnvView} {cfg : ErasureConfig} {r : Program × List Kername}
    (hfrag : collectDeps view cfg e = .ok decls) (hrun : eraseEntry view cfg e = pure r) :
    erasePure view cfg decls e = .ok r := by
  match hp : erasePure view cfg decls e with
  | .ok r' =>
    simp only [eraseEntry, route, hfrag, hp] at hrun
    exact congrArg _ (CoreM.pure_inj hrun)
  | .error _ =>
    simp only [eraseEntry, route, hfrag, hp] at hrun
    exact absurd hrun CoreM.throwError_ne_pure

end EraseProof
