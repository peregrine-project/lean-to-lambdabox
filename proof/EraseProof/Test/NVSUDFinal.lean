import EraseProof.Test.NVSUFinal

/-!
# NV-SUD: NV-SU under the default configuration

NV-SU's program and term (`Test/NVSUData.lean`) under the default configuration `{}`,

    #erase add (N.s N.z) (N.s N.z)   -- evaluates to N.s (N.s N.z)

that is `nat := .machine`, `extern := .preferAxiom` and `structural := .unsafeRec`. The program
has no `Nat`, no Nat literal and no `@[extern]` declaration, and the hypotheses of the final
theorem are NV-SU's at `nat := .machine`: the fragment test accepts `e` with NV-S's closure `D`
(`hcollect_default`, `Test/NVSRun.lean`); the entry point returns NV-SU's program `pSU` and
constants to inline (`hpure`, `Test/NVSURun.lean`, at `cfgOf .machine`, which is `{}`); `hpre` is
NV-SU's at `cfgOf .machine` (`Test/NVSUModel.lean`); and `evalEnvOf view {} P` is NV-SU's `σSU`
(`Test/NVSUEval.lean`), since `evalEnvOf` reads the configuration only through `axiomatized`
(`extern`) and `preDef?` (`structural`), so `hev` and `fo_ssz` are NV-SU's. `final` applies the
final theorem `erase_correct` to the nine hypotheses, and `firstorder` applies
`erase_correct_firstorder`.
-/

open Lean Erasure Metalean

namespace EraseProof.Test.NVSUD

open EraseProof.Test.NVR (iidN)
open EraseProof.Test.NVS (P e view D E B tE ssz ζ12)
open EraseProof.Test.NVSU (pSU)

/-- `henv`: the program is the Lean form of NV-S's model `E` with table `B`. -/
theorem henv : ProgEnv P ζ12 E B := NVSU.henv

/-- `hwf`: `E` is well formed. -/
theorem hwf : EnvWF E := NVSU.hwf

/-- `hview`: the view `#erase` reads agrees with the program. -/
theorem hview : ViewAgrees view P := NVSU.hview

/-- `hpre`: NV-SU's compiled pre-definitions at `nat := .machine`. -/
theorem hpre : PreDefsOK E B view {} P := NVSU.hpre (nat := .machine)

/-- `he`: the erased term is the Lean form of `tE`. -/
theorem he : TrM E B [] .nil [] e tE := NVSU.he

/-- `hty`: `tE` is typed. -/
theorem hty : ∃ T, E[.nil] ⊢ tE : T := NVSU.hty

/-- `hfrag`: the fragment test accepts `e` under `{}`, with the closure `D`. -/
theorem hfrag : collectDeps view {} e = .ok D := NVS.hcollect_default

/-- `hrun`: `#erase`'s entry point under `{}` returns NV-SU's program `pSU` and NV-S's constants
to inline. Reference: the hypotheses `erase … = t'` and `erase_global_deps … = Σ'` of
`erase_correct` (`MR E/ErasureFunctionProperties.v:657`). -/
theorem hrun : eraseEntry view {} e = pure (pSU, NVS.inl0) := by
  simp only [eraseEntry, route, hfrag,
    show erasePure view {} D e = _ from NVSU.hpure (nat := .machine)]

/-- `hev`: `e` evaluates to `N.s (N.s N.z)` at `evalEnvOf view {} P`, which is NV-SU's `σSU`. -/
theorem hev : SrcEval (evalEnvOf view {} P) (SrcConv E B []) e ssz := NVSU.hev

/-- The final theorem on NV-SUD: the program `#erase` emits for `add (N.s N.z) (N.s N.z)` under
the default configuration, `add` defined by structural recursion and erased through its compiled
pre-definition, is an untyped λ□ program whose main term evaluates to an erasure of
`N.s (N.s N.z)`, and `N.s (N.s N.z)` translates to a term definitionally equal to the input's at
each of its types. -/
theorem final :
    ∃ lenv tb vb, pSU = .untyped lenv (some tb) ∧
      Erases E B [] (evalEnvOf view {} P) .nil [] ssz vb ∧ LBEval defaultFlags lenv tb vb ∧
      ∀ T, E[.nil] ⊢ tE : T → ∃ t', TrM E B [] .nil [] ssz t' ∧ E[.nil] ⊢ tE ≡ t' : T :=
  erase_correct henv hwf hview hpre he hty hfrag hrun hev

/-- The final theorem on first-order values on NV-SUD: the main term of the program `#erase`
emits under the default configuration evaluates in λ□ to `N.s (N.s N.z)`'s structural erasure,
the constructor `1` of `N`'s block applied to the constructor `1` applied to the constructor
`0`. -/
theorem firstorder :
    ∃ lenv tb, pSU = .untyped lenv (some tb) ∧ LBEval defaultFlags lenv tb
      (.app (.construct iidN 1 []) (.app (.construct iidN 1 []) (.construct iidN 0 []))) :=
  erase_correct_firstorder henv hwf hview hpre he hty hfrag hrun hev NVSU.fo_ssz

end EraseProof.Test.NVSUD
