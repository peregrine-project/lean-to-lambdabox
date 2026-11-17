import EraseProof.Test.NVSUData
import EraseProof.Test.NVSRun

/-!
# NV-SU: the fragment test

The fragment test on NV-SU (`Test/NVSUData.lean`) accepts the term and returns NV-S's closure `D`
(`Test/NVSRun.lean`), in the same order: `add` is in the fragment through its compiled
pre-definition, whose constants `add.match_1`, `N`, `N.s` and `Unit` are in `D` already, and its
kernel value is read as under `structural := .kernel`.
-/

open Lean Erasure

namespace EraseProof.Test.NVSU

open EraseProof.Test.NVS (view e D)

/-- The fragment test accepts `e` and returns the closure `D`, by kernel evaluation. Reference: the
environment `Σ'` of `erase_global_deps` (`MR E/ErasureFunction.v:1602`). -/
theorem hcollect : collectDeps view cfgSU e = .ok D := by krfl

end EraseProof.Test.NVSU
