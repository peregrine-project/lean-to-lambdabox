import EraseProof.Test.NVUData
import EraseProof.Test.NVARun

/-!
# NV-U: the fragment test

The fragment test on NV-U (`Test/NVUData.lean`) accepts the term and returns NV-A's closure `D`
(`Test/NVARun.lean`), in the same order: `Nat.add` is in the fragment through its compiled
pre-definition, whose constants `Nat.add.match_1`, `Nat` and `Nat.succ` are in `D` already, and its
kernel value is read as under `structural := .kernel`.
-/

open Lean Erasure

namespace EraseProof.Test.NVU

open EraseProof.Test.NVA (view e D)

/-- The fragment test accepts `e` and returns the closure `D`, by kernel evaluation. Reference: the
environment `Σ'` of `erase_global_deps` (`MR E/ErasureFunction.v:1602`). -/
theorem hcollect : collectDeps view cfgU e = .ok D := by krfl

end EraseProof.Test.NVU
