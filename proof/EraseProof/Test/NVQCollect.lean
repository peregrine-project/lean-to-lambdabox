import EraseProof.Test.NV1Collect
import EraseProof.Test.NVQFinal

/-!
# NV-Q: the lower bound of the fragment test on quotients

The premises of `collectDeps_ok_of` on NV-Q (`Test/NVQData.lean`) with the closure `D`
(`Test/NVQRun.lean`), proved from the declarations, not from a run of the fragment test, as for
NV-1 (`Test/NV1Collect.lean`). The closure holds the quotient constants `Quot`, `Quot.mk` and
`Quot.lift`, which are in Phase I as quotient constants, the axioms `R` and `hR`, `B`, and `Eq`
(from the type of `Quot.lift`) with `Eq.rec`, in Phase I as the recursor of an inductive with one
constructor. No read expression names a recursor. `ok_of` applies `collectDeps_ok_of` to them.
-/

open Lean Erasure

namespace EraseProof.Test.NVQ

open EraseProof.Test.NV1 (B_ind Bf_ctor Bt_ctor)
open EraseProof.Test.NVP (Eq_ind Eq_refl Eq_rec)

theorem mem_D {ci : ConstantInfo} (h : ci ∈ D) :
    ci = .quotInfo QuotMk_val ∨ ci = .axiomInfo hR_ax ∨ ci = .axiomInfo R_ax ∨
      ci = .ctorInfo Bt_ctor ∨ ci = .ctorInfo Bf_ctor ∨ ci = .inductInfo B_ind ∨
      ci = .quotInfo Quot_val ∨ ci = .ctorInfo Eq_refl ∨ ci = .recInfo Eq_rec ∨
      ci = .inductInfo Eq_ind ∨ ci = .quotInfo QuotLift_val := by
  simpa [D] using h

/-- `D` is a sub-environment of the program. -/
theorem subD : SubEnv D P := by
  intro ci h
  rcases mem_D h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The read-closure test, on a declaration's own names. -/
abbrev inD (c : Name) : Bool := (findDecl D c).isSome

/-- `D` is closed under what the traversal reads. -/
theorem readD : ReadClosed D e := by
  refine ⟨constsIn_of_all (fun _ h => h) (p := inD) (by krfl), by decide, ?_⟩
  intro ci hci
  refine ⟨fun x hx => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := readAll_of (p := fun x => constsAll inD x && !HasNatLit x) (by krfl) ci hci x hx
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨constsIn_of_all (fun _ h => h) h.1, fun h' => by simp [h.2] at h'⟩
  all_goals rcases mem_D hci with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | decide
    | exact forall_eq_some (by krfl)
    | (rintro _ h; cases h; done)
    | (rintro _ h; cases h; decide)

/-- Every declaration of `D` is in Phase I. -/
theorem phaseD : ∀ ci ∈ D, PhaseIDecl view cfg D ci := by
  intro ci hci
  rcases mem_D hci with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · trivial
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, fun _ => rfl⟩
  · exact ⟨rfl, fun _ => rfl⟩
  · exact ⟨rfl, rfl, ⟨0, .succ .zero, rfl, .inr (.inl rfl)⟩, fun h => absurd h (by decide)⟩
  · trivial
  · exact ⟨rfl, fun _ => rfl⟩
  · exact .inr (.inl ⟨`Eq, Eq_ind, rfl, by krfl, rfl⟩)
  · exact ⟨rfl, rfl, ⟨3, .zero, rfl, .inl rfl⟩, fun h => absurd h (by decide)⟩
  · trivial

/-- The term and the read expressions are plain. -/
theorem plainD : PlainExpr cfg e ∧ ∀ ci ∈ D, ∀ x, ReadExpr D ci x → PlainExpr cfg x :=
  ⟨plain_of (by krfl), fun ci hci x hx => plain_of (readAll_of (p := plainB) (by krfl) ci hci x hx)⟩

/-- An expression that names no recursor of `D` names recursors only in the fragment's shape. -/
theorem recShapedOf {x : Expr} (h : constsAll (notRec D) x = true) : RecShaped cfg D x :=
  constsIn_of_all (fun c h rv hrv => by simp [notRec, hrv] at h) h

/-- The term and the read expressions name no recursor (`Eq.rec` is in `D` as a block member, and
no expression mentions it), so recursors only in the fragment's shape. -/
theorem recShapedD :
    RecShaped cfg D e ∧ ∀ ci ∈ D, ∀ x, ReadExpr D ci x → RecShaped cfg D x :=
  ⟨recShapedOf (by krfl), fun ci hci x hx => recShapedOf (readAll_of (by krfl) ci hci x hx)⟩

/-- The kernames of `D` are distinct. -/
theorem kernD : KernameInj D := kernameInj_of (by krfl)

/-- The block names of `B` and `Eq` are distinct from each other and from the kernames of the
axioms of `D`. -/
theorem blockD : BlockNamesInj D := by
  rintro iv₁ iv₂ ⟨c₁, h₁, rfl⟩ ⟨c₂, h₂, rfl⟩
  rcases mem_D h₁ with h | h | h | h | h | h | h | h | h | h | h <;> cases h <;>
    rcases mem_D h₂ with h | h | h | h | h | h | h | h | h | h | h <;> cases h <;>
    refine ⟨fun hk => ?_, fun ci hci he => ?_⟩ <;>
    first
    | rfl
    | exact absurd (congrArg Kername.id hk) (by decide)
    | rcases mem_D hci with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | (cases he; done) | exact fun hk => absurd (congrArg Kername.id hk) (by decide)

/-- The fragment test accepts NV-Q's term, by `collectDeps_ok_of` from the premises above. -/
theorem ok_of : ∃ decls', collectDeps view cfg e = .ok decls' :=
  collectDeps_ok_of henv hview he hty rfl subD readD phaseD plainD recShapedD kernD blockD
    (by decide)

end EraseProof.Test.NVQ
