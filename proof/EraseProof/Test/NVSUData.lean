import EraseProof.Test.NVSData
import EraseProof.Test.Run

/-!
# NV-SU: the program

    inductive N | z | s (n : N)
    def add (n m : N) : N :=
      match m with
      | .z => n
      | .s k => .s (add n k)
    #erase add (N.s N.z) (N.s N.z) config {nat := .peano}   -- evaluates to N.s (N.s N.z)

NV-S's program `P`, term `e` and view (`Test/NVSData.lean`) under `{nat := .peano}`, the other
fields at their defaults, among them `structural := .unsafeRec`. The view holds `add`'s compiled
companion `add._unsafe_rec`, so the eraser erases `add` through its compiled pre-definition
`pre[add]` (`preDef?`): the companion's value with `add` for the companion's name,

    fun n m => add.match_1 (fun m => N) m (fun _ => n) (fun k => N.s (add n k))

whose recursive call is saturated under the second alternative's λ (`preVal`), and emits it as a
λ□ fixpoint. A non-vacuity instance of the final theorem
(`MR E/ErasureFunctionProperties.v:657 erase_correct`) on a definition of the program by structural
recursion, erased as a fixpoint: `Test/NVSUCollect.lean` evaluates the fragment test,
`Test/NVSURun.lean` discharges `hrun`, `Test/NVSUModel.lean` `hpre`, `Test/NVSUEval.lean` `hev`,
and `Test/NVSUFinal.lean` applies the final theorem.
-/

open Lean Erasure

namespace EraseProof.Test.NVSU

open EraseProof.Test.NVS (addUnsafeRecVal add_def view hyg tUnit l1)
open EraseProof.Test.NVR (tN cS)

/-- The configuration `{nat := .peano}`. -/
def cfgSU : ErasureConfig := { nat := .peano }

/-- The configuration `{nat := nat}`, the other fields at their defaults: `cfgSU` at `.peano`, the
default configuration `{}` at `.machine`. -/
def cfgOf (nat : Config.Nat) : ErasureConfig := { nat := nat }

/-- The motive `fun m => N` of the pre-definition's match. -/
def motPre : Expr := .lam (hyg "m" 8) tN tN .default

/-- The alternatives `fun _ => n` and `fun k => N.s (add n k)`, under `n m`. -/
def altPre1 : Expr := .lam `_ tUnit (.bvar 2) .default
def altPre2 : Expr :=
  .lam `k tN (.app cS (.app (.app (.const `add []) (.bvar 2)) (.bvar 0))) .default

/-- `pre[add]`: `fun n m => add.match_1 (fun m => N) m (fun _ => n) (fun k => N.s (add n k))`. -/
def preVal : Expr :=
  .lam `n tN (.lam `m tN
    (.app (.app (.app (.app (.const `add.match_1 [l1]) motPre) (.bvar 0)) altPre1) altPre2)
    .default) .default

/-- `preVal` is the companion's value with `add` for `add._unsafe_rec`. -/
theorem preVal_eq : renameUnsafeRec addUnsafeRecVal = preVal := by krfl

/-- Under `cfgOf nat`, for either `nat`, the pure path erases `add` through `preVal`. Reference:
none (DV-7). -/
theorem preDef_add {nat : Config.Nat} :
    preDef? view (cfgOf nat) (.defnInfo add_def) = some preVal := by
  krfl

end EraseProof.Test.NVSU
