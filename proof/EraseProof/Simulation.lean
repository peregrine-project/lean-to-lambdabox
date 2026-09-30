import EraseProof.Simulation.Cases
import EraseProof.Simulation.Fix

/-!
# The relation-level simulation

`erases_correct` (`MR E/ErasureCorrectness.v:51`): an evaluation of a well-typed closed source term
is matched by a λ□ evaluation of any erasure of it whose dependencies are erased, to an erasure of
the source value. The proof is an induction on the source evaluation, one case lemma per rule of
`SrcEval` (`Simulation/Cases.lean`, `Simulation/Fix.lean`), with the translation, the erasure and
its dependencies generalized.
-/

open Lean Lean4Lean Erasure

namespace EraseProof

section
variable {venv : VEnv} {P : List ConstantInfo} {σ : EvalEnv} {lenv : GlobalDeclarations}

/-- Relation-level simulation: an evaluation of a well-typed closed source term is matched by a
λ□ evaluation of any erasure whose dependencies are erased. Typing is in `P`'s model; evaluation
and λ□ dependencies are over its sub-environment `σ.decls`. Reference: `erases_correct`
(`MR E/ErasureCorrectness.v:51`); MC §7.4, p. 8:64; Let. Thm 13, big-step (DV-20, DV-22). -/
theorem erases_correct (henv : ProgEnv P venv) (hsub : SubEnv σ.decls P)
    (hinj : KernameInj σ.decls) (hlc : LenvClosed lenv)
    (he : TrS venv Us [] e e')
    (her : Erases venv Us σ.isAtom (RecIn lenv) [] e t) (hdeps : ErasesDeps venv σ lenv t)
    (hblocks : BlocksErased venv σ lenv) (hev : SrcEval σ e v) :
    ∃ v', Erases venv Us σ.isAtom (RecIn lenv) [] v v' ∧ LBEval defaultFlags lenv t v' := by
  induction hev generalizing e' t with
  | beta hf ha hb ihf iha ihb =>
    exact erases_correct_beta henv hsub hlc ihf iha ihb hf ha hb he her hdeps
  | zeta hv hb ihv ihb => exact erases_correct_zeta henv hsub hlc ihv ihb hv hb he her hdeps
  | delta hu hr hlen hb ihb =>
    exact erases_correct_delta henv hsub hinj hblocks ihb hu hr hlen hb he her hdeps
  | fixAtom hu hr _ => exact erases_correct_fixAtom hinj hu hr her hdeps
  | fixApp hf hu hr ha hb ihf iha ihb =>
    exact erases_correct_fixApp henv hsub hblocks ihf iha ihb hf hu hr ha hb he her hdeps
  | constAtom _ ha _ => exact erases_correct_constAtom ha her
  | appCong hf hbc ha ihf iha =>
    exact erases_correct_appCong henv hsub ihf iha hf hbc ha he her hdeps
  | mdata hev ih => exact erases_correct_mdata henv hsub ih hev he her hdeps
  | atom ha => exact erases_correct_atom ha her

end

end EraseProof
