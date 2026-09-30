import EraseProof.Test.NV1
import EraseProof.Main

/-!
# NV-1 through the entry point of `#erase`

The run of `#erase` on NV-1 (`Test/NV1.lean`) that the hypothesis `hrun` of the final theorem
`erase_correct` (`MR E/ErasureFunctionProperties.v:657`) describes. `hcollect` computes the
dependency closure of `e0` by kernel evaluation of the shipping `collectDeps`, and
`eraseEntry_of_erasePure` reduces the entry point on NV-1 to the pure path over that closure.
-/

open Lean Lean4Lean Erasure

namespace EraseProof.Test.NV1

/-- The dependency closure of `e0`, in the order `collectDeps` returns it: every declaration
after the ones it depends on (`A`, then `CN`, then `one`), the reverse of `decls0`. -/
def decls0' : List ConstantInfo := [.axiomInfo A_val, .defnInfo CN_val, .defnInfo one_val]

/-- `collectDeps` on NV-1's list view returns the closure `decls0'`: the first step of `route`,
by kernel evaluation (the work-list bound `collectFuel` is never reached). Reference: the
environment `Σ'` of `erase_global_deps` (`MR E/ErasureFunction.v:1602`). -/
theorem hcollect : collectDeps view0 e0 = .ok decls0' := by
  rfl

/-- On NV-1, the entry point returns what the pure path returns over `decls0'`: `route` takes
the pure path since `collectDeps` succeeds (`hcollect`). The instance of `eraseEntry_pure`'s
routing on NV-1, in the direction `hrun` needs. Reference: none (S-E). -/
theorem eraseEntry_of_erasePure {r : Program × List Kername}
    (h : erasePure view0 {} decls0' e0 = .ok r) : eraseEntry view0 {} e0 = pure r := by
  simp only [eraseEntry, route, hcollect, h]

end EraseProof.Test.NV1
