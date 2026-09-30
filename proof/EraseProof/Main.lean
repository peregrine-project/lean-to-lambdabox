import EraseProof.Core.Glue
import EraseProof.Core
import EraseProof.Simulation
import EraseProof.Source.Restrict

/-!
# The final theorem

`erase_correct` (`MR E/ErasureFunctionProperties.v:657`): partial correctness of `#erase`. On an
in-scope input, a run of the entry point `Erasure.eraseEntry` that returns a program is a run of the
pure path (`eraseEntry_pure`), whose output is an erasure of the input with erased dependencies
(`erasePure_erases`) over the closure `collectDeps` computes (`collectDeps_spec`,
`collectDeps_sub`). A source evaluation over the program restricts to that closure
(`SrcEval.restrict`), where the relation-level simulation `erases_correct` applies; its conclusion
moves back to the program's atom test (`Erases.congr_ac`). The theorem is about a run that
returns (DV-17) and states no first-order corollary (DV-19).
-/

open Lean Lean4Lean Erasure

namespace EraseProof

section
variable {venv : VEnv} {P decls : List ConstantInfo} {Us : List Name} {e v : Expr} {e' : VExpr}

/-- Final theorem: partial correctness of `#erase` on in-scope inputs. If the entry point returns
a program and the source evaluates, the program's term evaluates in λ□ (at `default_wcbv_flags`) to
an erasure of the source value. Reference: `erase_correct`
(`MR E/ErasureFunctionProperties.v:657`); MC §7.3–7.4 (pp. 8:62–8:64). -/
theorem erase_correct {view : EnvView} {cfg : ErasureConfig} {p : Program} {inl : List Kername}
    (henv : ProgEnv P venv)                          -- wf_ext Σ
    (hview : ViewAgrees view P)                      -- Σ ∼_ext X: #erase reads Σ
    (he : TrS venv Us [] e e')                       -- welltyped Σ [] t
    (hrun : eraseEntry view cfg e = pure (p, inl))   -- erase … = t', erase_global_deps … = Σ'
    (hev : SrcEval (evalEnvOf view cfg P) e v) :     -- Σ ⊢ t ⇓ v
    ∃ lenv t v', p = .untyped lenv (some t) ∧
      Erases venv Us (evalEnvOf view cfg P).isAtom (RecIn lenv) [] v v' ∧
      LBEval defaultFlags lenv t v' := by
  obtain ⟨decls, hdecls, hpure⟩ := eraseEntry_pure ⟨P, venv, Us, e', henv, hview, he⟩ hrun
  obtain ⟨hinj, -, -, hcl, -, hce⟩ := collectDeps_spec hdecls
  have hsub := collectDeps_sub henv hview he hdecls
  obtain ⟨lenv, t, hp, her, hdeps, hblocks, hlc⟩ := erasePure_erases henv hview he hdecls hpure
  obtain ⟨hev', hcv⟩ := SrcEval.restrict hsub hcl hce hev
  obtain ⟨v', hv, hev''⟩ :=
    erases_correct (σ := evalEnvOf view cfg decls) henv hsub hinj hlc he her hdeps hblocks hev'
  exact ⟨lenv, t, v', hp, hv.congr_ac (atom_agree hsub hcl hcv), hev''⟩
where
  /-- The atom tests of `decls` and of `P` agree on `decls`' constants (internal step of the
  final theorem). Reference: none (DV-3, DV-11). -/
  atom_agree {view : EnvView} {cfg : ErasureConfig} {decls P : List ConstantInfo} {v : Expr}
      (hsub : SubEnv decls P) (hcl : DepClosed decls)
      (hcv : ConstsIn (fun c => (findDecl decls c).isSome) v) :
      ConstsIn (fun c => (evalEnvOf view cfg decls).isAtom c = (evalEnvOf view cfg P).isAtom c) v :=
    hcv.mono fun _ hc => evalEnvOf_isAtom hsub hcl hc

end

end EraseProof
