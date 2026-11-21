import Metalean.Typing.Defs
import Metalean.Metatheory.Unique
import Metalean.Metatheory.SubjectReduction

/-!
Checks that the eraser, which does not use the module system, can import Metalean, which does, and
pins the axioms of two Metalean theorems the translation will rely on. Neither depends on
Metalean's `exists_inaccessibles` axiom, which only its set theory (Metalean.SetTheory) uses.
-/

/-- info: 'Metalean.WHRed.defeq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Metalean.WHRed.defeq

/-- info: 'Metalean.Defeq.uniqTy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Metalean.Defeq.uniqTy
