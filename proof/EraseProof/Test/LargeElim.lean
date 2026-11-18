import EraseProof.Bridge.LargeElim

/-!
# Tests: Lean's large elimination against Metalean's

`LeanLargeElim` is Lean's rule for giving a recursor a motive universe. On a block of one type it
is Metalean's `Inductive.LargeElim`; on the mutual block
`mutual inductive A : Prop | a : A; inductive B : Prop | b : B end`, whose recursors Lean's kernel
lets eliminate only into `Prop` (`elim_only_at_universe_zero`), Metalean's `LargeElim` holds and
`LeanLargeElim` does not.
-/

open Metalean

namespace EraseProof.Test.LargeElim

/-- The constructor signature of `A.a` and `B.b`: no fields. -/
abbrev abCtorSig : CtorSig 2 :=
  { nfields := 0, nrecFields := 0, recursiveArity := ![], recursiveTarget := ![] }

/-- The signature of the block `A`, `B`: two types without parameters or indices, one
constructor each. -/
abbrev abSig : IndSig :=
  { nlevels := 0, nparams := 0, nsorts := 2, nindices _ := 0, nctors _ := 1,
    ctors _ _ := abCtorSig }

/-- `mutual inductive A : Prop | a : A; inductive B : Prop | b : B end` as a Metalean block. -/
@[reducible] def abBlock {ζ : Sigs} : Inductive ζ abSig where
  params := .nil
  indices _ := .nil
  level := .zero
  ctors _ _ := { ordinary := fun f => Fin.elim0 f, recursive := fun f => Fin.elim0 f,
                 targetIndices := fun i => Fin.elim0 i }

/-- Metalean's `LargeElim` holds of the mutual block: each type has one constructor, without
fields. -/
theorem abBlock_largeElim {ζ : Sigs} : (abBlock (ζ := ζ)).LargeElim :=
  Or.inl ⟨fun _ _ _ => Subsingleton.elim _ _,
    fun _ _ => ⟨fun f => Fin.elim0 f, fun f => Fin.elim0 f⟩⟩

/-- Lean's rule does not: the block is in `Prop` and declares two types, so its recursors have no
motive universe. -/
theorem abBlock_not_leanLargeElim {ζ : Sigs} : ¬ LeanLargeElim (abBlock (ζ := ζ)) := by
  rintro (h | ⟨h, -⟩)
  · simpa using h (fun _ => 0)
  · exact absurd h (by decide)

/-- On a block of one type, Lean's rule and Metalean's `LargeElim` agree. -/
theorem leanLargeElim_iff_largeElim {ζ : Sigs} {ι : IndSig} {I : Inductive ζ ι}
    (h : ι.nsorts = 1) : LeanLargeElim I ↔ I.LargeElim :=
  ⟨LeanLargeElim.toLargeElim, fun h' => h'.elim (fun hs => Or.inr ⟨h, hs⟩) Or.inl⟩

end EraseProof.Test.LargeElim
