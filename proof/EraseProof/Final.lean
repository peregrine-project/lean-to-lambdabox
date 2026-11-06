import EraseProof.Core.Glue
import EraseProof.Core.CollectSpec
import EraseProof.Source.Restrict
import EraseProof.Source.ProofSound
import EraseProof.Simulation.Main

/-!
# The final theorem from the correctness of the pure traversal

`erase_correct_of_pure` derives the final theorem's statement from `erasePure_erases_statement`:

1. `eraseEntry_pure`: the entry point's result is the pure path's result on the closure `decls`
   that the fragment test returns;
2. `erasePure_erases_statement`: that result is an erasure of the input, at the evaluation
   environment of `decls`, with erased dependencies, in a closed λ□ environment;
3. `collectDeps_sub`, `collectDeps_spec`: `decls` is a dependency-closed sub-environment of the
   program that contains the input's constants, with injective kernames and λ□ block names and
   syntactic arities as inductive types;
4. `SrcEval.restrict`: the source evaluation restricts to `decls`;
5. `erases_correct`: the λ□ program evaluates to an erasure of the value, at `decls`;
6. `Erases.extend`: that erasure is one at the program's evaluation environment;
7. `SrcEval.defeq`: the value translates to a term definitionally equal to the input's.
-/

open Lean Erasure

namespace EraseProof

/-- The final theorem's statement follows from the correctness of the pure traversal on the
fragment test's closure. Reference: `erase_correct` (`MR E/ErasureFunctionProperties.v:657`),
which composes the erasure's correctness with `erases_correct` (`MR E/ErasureCorrectness.v:51`)
and the weakening of the global environment (`erases_extends`, `MR E/ESubstitution.v:73`). -/
theorem erase_correct_of_pure (h : erasePure_erases_statement) : erase_correct_statement := by
  intro P decls ζ E B view cfg lps e v t p inl henv hwf hview he hty hfrag hrun hev
  obtain ⟨lenv, tb, rfl, her, hdeps, hlc⟩ :=
    h henv hwf hview he hty hfrag (eraseEntry_pure hfrag hrun)
  have hsub := collectDeps_sub henv hview he hfrag
  obtain ⟨hinj, -, -, hcl, -, hc, -, -, hblk, harity⟩ := collectDeps_spec henv hview he hfrag
  obtain ⟨hev', hcv⟩ := SrcEval.restrict hsub hcl hc hev
  obtain ⟨vb, hv, hlb⟩ := erases_correct henv hwf hsub hinj hblk harity hlc he hty her hdeps hev'
  exact ⟨lenv, tb, vb, rfl, Erases.extend hsub hcl hcv hv, hlb,
    fun _ hT => SrcEval.defeq henv hwf (fun _ => CollectSub.findDecl_of_view hview) he hT hev⟩

end EraseProof
