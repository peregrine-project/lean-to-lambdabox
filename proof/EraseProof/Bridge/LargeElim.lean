import EraseProof.Spec
import EraseProof.Metatheory.Syntax

/-!
# Lean's large elimination and Metalean's

`LeanLargeElim`, the rule by which Lean's kernel gives a recursor a motive universe, implies
Metalean's `Inductive.LargeElim`, and both are invariant under signature morphisms.
-/

namespace EraseProof

variable {ζ ζ₁ ζ₂ : Metalean.Sigs} {ι : Metalean.IndSig}

/-- A block that eliminates into every sort by Lean's rule does so by Metalean's
(`Inductive.LargeElim`, `ML Syntax/Inductive/LargeElimination.lean:53`), which drops the condition
that the block declares one type. -/
theorem LeanLargeElim.toLargeElim {I : Metalean.Inductive ζ ι} (h : LeanLargeElim I) :
    I.LargeElim :=
  h.elim Or.inr fun h => Or.inl h.2

/-- Lean's large elimination is invariant under signature morphisms (as `Inductive.largeElim_map`,
`ML Syntax/Inductive/LargeElimination.lean:114`). -/
theorem leanLargeElim_map (I : Metalean.Inductive ζ₁ ι) (pre : ζ₁ ⟶ ζ₂) :
    LeanLargeElim (I.map pre) ↔ LeanLargeElim I := by
  simp only [LeanLargeElim, Metalean.Inductive.subsingleton_map]
  exact Iff.rfl

end EraseProof
