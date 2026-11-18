import EraseProof.Test.NVUEval
import EraseProof.Test.NVURun

/-!
# NV-U end to end

The remaining hypotheses of the final theorem on NV-U (`Test/NVUData.lean`): NV-A's model,
program and term (`henv`, `hwf`, `he`, `hty`, `Test/NVAModel.lean`) and view (`hview`,
`Test/NVAFinal.lean`), and the fragment test's acceptance of `e` (`hfrag`, the closure `D` of
`hcollect`, `Test/NVUCollect.lean`). `final` applies the final theorem `erase_correct` to all nine
hypotheses, with `hpre` from `Test/NVUModel.lean`, `hrun` from `Test/NVURun.lean` and `hev` from
`Test/NVUEval.lean`. The program `pU` declares
`Nat.add` as a λ□ fixpoint (`addFixL`). The corollary on first-order values
(`erase_correct_firstorder`) does not apply, as for NV-A: the value keeps the literal `2` under its
constructors.
-/

open Lean Erasure Metalean

namespace EraseProof.Test.NVU

open EraseProof.Test.NVA (P e view D E B tE v5 ζ13)

/-- `henv`: the program is the Lean form of NV-A's model `E` with table `B`. -/
theorem henv : ProgEnv P ζ13 E B := NVA.henv

/-- `hwf`: `E` is well formed. -/
theorem hwf : EnvWF E := NVA.hwf

/-- `hview`: the view `#erase` reads agrees with the program. -/
theorem hview : ViewAgrees view P := NVA.hview

/-- `he`: the erased term is the Lean form of `tE`. -/
theorem he : TrM E B [] .nil [] e tE := NVA.he

/-- `hty`: `tE` is typed. -/
theorem hty : ∃ T, E[.nil] ⊢ tE : T := NVA.hty

/-- `hfrag`: the fragment test accepts `e`, with the closure `D`. -/
theorem hfrag : collectDeps view cfgU e = .ok D := hcollect

/-- The final theorem on NV-U: the program `#erase` emits for `Nat.add 2 3` under
`{extern := .preferLogical, nat := .peano}` (structural recursion through the compiled
pre-definition) is an untyped λ□ program whose main term evaluates to an erasure of
`Nat.succ (Nat.succ (Nat.succ 2))`, and that value translates to a term definitionally equal to the
input's at each of its types. -/
theorem final :
    ∃ lenv tb vb, pU = .untyped lenv (some tb) ∧
      Erases E B [] (evalEnvOf view cfgU P) .nil [] v5 vb ∧ LBEval defaultFlags lenv tb vb ∧
      ∀ T, E[.nil] ⊢ tE : T → ∃ t', TrM E B [] .nil [] v5 t' ∧ E[.nil] ⊢ tE ≡ t' : T :=
  erase_correct henv hwf hview hpre he hty hfrag hrun hev

end EraseProof.Test.NVU
