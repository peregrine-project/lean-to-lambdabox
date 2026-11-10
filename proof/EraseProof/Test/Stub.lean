import EraseProof.Main

/-!
# The approved statement of the final theorem

Test, off the path of the final theorem: `Test.Stub.erase_correct` is the statement of
`erase_correct` as approved, written out with the binders of its section, and proved by
`erase_correct`. Check C12 of `proof/scripts/check.sh` fails unless the two have the same type
(`Expr.eqv`), binder order included.
-/

open Lean Lean4Lean Erasure

namespace EraseProof.Test.Stub

variable {venv : VEnv} {P decls : List ConstantInfo} {σ : EvalEnv} {lenv : GlobalDeclarations}

/-- The approved statement of the final theorem. Reference: `erase_correct`
(`MR E/ErasureFunctionProperties.v:657`). -/
theorem erase_correct {view : EnvView} {cfg : ErasureConfig} {p : Program} {inl : List Kername}
    (henv : ProgEnv P venv)                          -- wf_ext Σ
    (hview : ViewAgrees view P)                      -- Σ ∼_ext X: #erase reads Σ
    (he : TrS venv Us [] e e')                       -- welltyped Σ [] t
    (hrun : eraseEntry view cfg e = pure (p, inl))   -- erase … = t', erase_global_deps … = Σ'
    (hev : SrcEval (evalEnvOf view cfg P) e v) :     -- Σ ⊢ t ⇓ v
    ∃ lenv t v', p = .untyped lenv (some t) ∧
      Erases venv Us (evalEnvOf view cfg P).isAtom (RecIn lenv) [] v v' ∧
      LBEval defaultFlags lenv t v' :=
  EraseProof.erase_correct henv hview he hrun hev

end EraseProof.Test.Stub
