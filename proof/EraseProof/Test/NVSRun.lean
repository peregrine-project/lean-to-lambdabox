import EraseProof.Test.NVSData
import EraseProof.Test.NVRRun

/-!
# NV-S through the entry point of `#erase`

The hypotheses `hfrag` and `hrun` of the final theorem (`MR E/ErasureFunctionProperties.v:657
erase_correct`) on NV-S (`Test/NVSData.lean`). `hcollect` computes the fragment test's closure `D`
by kernel evaluation. `hrun` is the run of the entry point, evaluated one traversal call at a time
(`Test/Run.lean`), cut at every read of the traversal's maps.
-/

open Lean Erasure EraseProof.Test

namespace EraseProof.Test.NVS

open EraseProof.Test.NVR (tN cZ cS N_ind Nz_ctor Ns_ctor N_rec motTy mj iidN masksN bodyN)

/-- The closure of `e`, in the order the fragment test returns it. -/
def D : List ConstantInfo :=
  [.defnInfo Unit_unit, .defnInfo N_casesOn, .defnInfo Unit_def, .defnInfo add_match_1,
    .defnInfo add_f, .defnInfo N_brecOn_go, .ctorInfo PProd_mk, .recInfo PProd_rec,
    .inductInfo PProd_ind, .ctorInfo PUnit_unit, .recInfo PUnit_rec, .inductInfo PUnit_ind,
    .recInfo N_rec, .defnInfo N_below, .defnInfo N_brecOn, .ctorInfo Ns_ctor, .ctorInfo Nz_ctor,
    .inductInfo N_ind, .defnInfo add_def]

/-- The fragment test accepts `e` and returns the closure `D`, by kernel evaluation. Reference: the
environment `Σ'` of `erase_global_deps` (`MR E/ErasureFunction.v:1602`). -/
theorem hcollect : collectDeps view cfg e = .ok D := rfl

/-- The pure backend's context over the closure. -/
def pc : PureCtx := ⟨D, view⟩

/-! ## The emitted program -/

/-- The λ□ inductives of `PProd` and `PUnit`. -/
def iidPP : InductiveId := ⟨mutualBlockKername [`PProd], 0⟩
def iidPU : InductiveId := ⟨mutualBlockKername [`PUnit], 0⟩

/-- The argument masks of `PProd.mk` (both fields kept) and `PUnit.unit` (no field). -/
def masksPP : InductiveArgMasks := [#[.keep, .keep]]
def masksPU : InductiveArgMasks := [#[]]

/-- The λ□ bodies of `PProd` (a structure: one projection per kept field) and `PUnit`. -/
def bodyPP : OneInductiveBody :=
  { name := toString `PProd, propositional := false, ctors := [⟨toString `PProd.mk, 2⟩],
    projs := [⟨"0"⟩, ⟨"1"⟩] }
def bodyPU : OneInductiveBody :=
  { name := toString `PUnit, propositional := false, ctors := [⟨toString `PUnit.unit, 0⟩],
    projs := [] }

/-- The first projection of `PProd`. -/
def projPP : ProjectionInfo := { indType := iidPP, paramCount := 2, fieldIdx := 0 }

/-- `N.z`, `N.s`, `PProd.mk`, `PUnit.unit` in λ□. -/
def zL : LBTerm := .construct iidN 0 []
def sL : LBTerm := .construct iidN 1 []
def mkL : LBTerm := .construct iidPP 0 []
def unitL : LBTerm := .construct iidPU 0 []

/-- The erasure of `N.brecOn.go`'s value: the minor premises let-bound around the fixpoint of
`N`'s block (NV-R's `fixL`) applied to `t`. -/
def goL : LBTerm :=
  .lambda (.named "motive") (.lambda (.named "t") (.lambda (.named "F_1")
    (.letIn (.named "z") (.app (.app (.app (.app mkL .box) .box) (.app (.app (.bvar 0) zL) unitL))
        unitL)
      (.letIn (.named "s") (.lambda (.named "n") (.lambda (.named "n_ih")
          (.app (.app (.app (.app mkL .box) .box) (.app (.app (.bvar 3) (.app sL (.bvar 1)))
            (.bvar 0))) (.bvar 0))))
        (.app NVR.fixL (.bvar 3))))))

/-- The erasure of `N.brecOn`'s value. -/
def brecOnL : LBTerm :=
  .lambda (.named "motive") (.lambda (.named "t") (.lambda (.named "F_1")
    (.proj projPP (.app (.app (.app (.const (toKername `N.brecOn.go)) .box) (.bvar 1))
      (.bvar 0)))))

/-- The erasure of `Unit.unit`'s value. -/
def unitUL : LBTerm := unitL

/-- The erasure of `add.match_1`'s value: a λ□ `case` on `N`. -/
def matchL : LBTerm :=
  .lambda (.named "motive") (.lambda (.named (toString (hyg "m" 8))) (.lambda (.named "h_1")
    (.lambda (.named "h_2") (.case (iidN, 0) (.bvar 2)
      [([], .app (.bvar 1) (.const (toKername `Unit.unit))),
       ([.named (toString (hyg "n" 22))], .app (.bvar 1) (.bvar 0))]))))

/-- The erasure of `add._f`'s value. -/
def fL : LBTerm :=
  .lambda (.named "n") (.lambda (.named "m") (.lambda (.named "f")
    (.app (.app (.app (.app (.app (.const (toKername `add.match_1)) .box) (.bvar 1))
      (.lambda (.named "_") (.lambda (.named (toString (hyg "x" 23))) (.bvar 4))))
      (.lambda (.named "k") (.lambda (.named (toString (hyg "x" 23)))
        (.app sL (.proj projPP (.bvar 0)))))) (.bvar 0))))

/-- The erasure of `add`'s value. -/
def addL : LBTerm :=
  .lambda (.named "n") (.lambda (.named "m")
    (.app (.app (.app (.const (toKername `N.brecOn)) .box) (.bvar 0))
      (.app (.const (toKername `add._f)) (.bvar 1))))

/-- The erasure of `e`. -/
def eL : LBTerm := .app (.app (.const (toKername `add)) NVR.mjL) NVR.mjL

/-- The constants `#erase` marks for inlining on NV-S: the `@[inline]` definitions it erases,
the last first. -/
def inl0 : List Kername := [toKername `Unit.unit, toKername `add.match_1]

/-- The program `#erase` emits for NV-S. -/
def p0 : Program :=
  .untyped [(toKername `add, .constantDecl ⟨some addL⟩),
    (toKername `add._f, .constantDecl ⟨some fL⟩),
    (toKername `add.match_1, .constantDecl ⟨some matchL⟩),
    (toKername `Unit.unit, .constantDecl ⟨some unitUL⟩),
    (toKername `N.brecOn, .constantDecl ⟨some brecOnL⟩),
    (toKername `N.brecOn.go, .constantDecl ⟨some goL⟩),
    (mutualBlockKername [`PUnit], .inductiveDecl ⟨.finite, 0, [bodyPU]⟩),
    (mutualBlockKername [`N], .inductiveDecl ⟨.finite, 0, [bodyN]⟩),
    (mutualBlockKername [`PProd], .inductiveDecl ⟨.finite, 2, [bodyPP]⟩)] (some eL)

end EraseProof.Test.NVS
