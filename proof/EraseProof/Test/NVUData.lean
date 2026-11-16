import EraseProof.Test.NVAData
import EraseProof.Test.Run

/-!
# NV-U: the program

    #erase Nat.add 2 3 config {extern := .preferLogical, nat := .peano}   -- evaluates to 5

NV-A's program `P`, term `e` and view (`Test/NVAData.lean`) under the default
`structural := .unsafeRec`. The view holds `Nat.add`'s compiled companion `Nat.add._unsafe_rec`,
so the eraser erases `Nat.add`, a definition by structural recursion, through its compiled
pre-definition `pre[Nat.add]` (`preDef?`): the companion's value with `Nat.add` for the
companion's name,

    fun x y => Nat.add.match_1 (fun x y => Nat) x y (fun a => a)
      (fun a b => Nat.succ (Nat.add a b))

whose recursive call is saturated under the second alternative's λs (`preVal`), and emits it as a
λ□ fixpoint. A non-vacuity instance of the final theorem
(`MR E/ErasureFunctionProperties.v:657 erase_correct`) on a definition erased as a fixpoint:
`Test/NVUCollect.lean` evaluates the fragment test, `Test/NVURun.lean` discharges `hrun` and
`Test/NVUModel.lean` `hpre`.
-/

open Lean Erasure

namespace EraseProof.Test.NVU

open EraseProof.Test.NVA (addUnsafeRecVal add_def view x13 x14 x32 x35)
open EraseProof.Test.NVL (tN cS)
open EraseProof.Test.NVS (l1)

/-- The configuration `{extern := .preferLogical, nat := .peano}`, by its fields in order (`extern`,
`nat`, `csimp`, `remove_irrel_constr_args`, `auto_inline_typeclass_dispatch`, `structural`). -/
def cfgU : ErasureConfig := ⟨.preferLogical, .peano, true, false, false, .unsafeRec⟩

/-- `cfgU` is the configuration `{nat := .peano}` with the `@[extern]` policy `.preferLogical`, the
other fields at their defaults (`structural := .unsafeRec`). -/
theorem cfgU_eq : let d : ErasureConfig := { nat := .peano }
    cfgU = ⟨.preferLogical, d.2, d.3, d.4, d.5, d.6⟩ := rfl

/-- The motive `fun x y => Nat` of the pre-definition's match. -/
def motPre : Expr := .lam x32 tN (.lam x35 tN tN .default) .default

/-- The alternatives `fun a => a` and `fun a b => Nat.succ (Nat.add a b)`. -/
def altPre1 : Expr := .lam `a tN (.bvar 0) .default
def altPre2 : Expr := .lam `a tN (.lam `b tN
  (.app cS (.app (.app (.const `Nat.add []) (.bvar 1)) (.bvar 0))) .default) .default

/-- `pre[Nat.add]`: `fun x y => Nat.add.match_1 (fun x y => Nat) x y (fun a => a)
(fun a b => Nat.succ (Nat.add a b))`. -/
def preVal : Expr :=
  .lam x13 tN (.lam x14 tN
    (.app (.app (.app (.app (.app (.const `Nat.add.match_1 [l1]) motPre) (.bvar 1)) (.bvar 0))
      altPre1) altPre2) .default) .default

/-- `preVal` is the companion's value with `Nat.add` for `Nat.add._unsafe_rec`. -/
theorem preVal_eq : renameUnsafeRec addUnsafeRecVal = preVal := by krfl

/-- Under `cfgU` the pure path erases `Nat.add` through `preVal`. Reference: none (DV-7). -/
theorem preDef_add : preDef? view cfgU (.defnInfo add_def) = some preVal := by krfl

end EraseProof.Test.NVU
