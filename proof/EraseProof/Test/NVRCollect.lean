import EraseProof.Test.NV1Collect
import EraseProof.Test.NVRFinal

/-!
# NV-R: the lower bound of the fragment test on a recursor

The premises of `collectDeps_ok_of` on NV-R (`Test/NVRData.lean`) with the closure `D`
(`Test/NVRRun.lean`), proved from the declarations, not from a run of the fragment test, as for
NV-1 (`Test/NV1Collect.lean`). The term reads the recursor `N.rec`, in the shape the fragment admits
(`RecInFragment`, `recInFragD`): `N.rec` is in Phase I through that shape, and it is the only
recursor the term and the read expressions name. `ok_of` applies `collectDeps_ok_of` to them.
-/

open Lean Erasure

namespace EraseProof.Test.NVR

open EraseProof.Test.NV1 (B_ind Bf_ctor Bt_ctor)

theorem mem_D {ci : ConstantInfo} (h : ci ∈ D) :
    ci = .ctorInfo Bt_ctor ∨ ci = .ctorInfo Bf_ctor ∨ ci = .inductInfo B_ind ∨
      ci = .ctorInfo Ns_ctor ∨ ci = .ctorInfo Nz_ctor ∨ ci = .inductInfo N_ind ∨
      ci = .recInfo N_rec := by
  simpa [D] using h

/-- `D` is a sub-environment of the program. -/
theorem subD : SubEnv D P := by
  intro ci h
  rcases mem_D h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

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
  · rcases mem_D hci with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rintro iv rfl; rcases mem_D hci with h | h | h | h | h | h | h <;> cases h <;> decide
  · rintro cv rfl; rcases mem_D hci with h | h | h | h | h | h | h <;> cases h <;> rfl
  · rcases mem_D hci with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact forall_eq_some (by krfl)
  · rintro iv rfl; rcases mem_D hci with h | h | h | h | h | h | h <;> cases h <;> intro h <;>
      cases h

/-- `N.rec` is in the shape the fragment admits, over the block `[N]` that it reads from `D`. -/
theorem recInFragD : RecInFragment cfg D N_rec :=
  ⟨`N, N_ind, [Nz_ctor, Ns_ctor], rfl, rfl, by krfl, by krfl, by krfl⟩

/-- Every declaration of `D` is in Phase I. -/
theorem phaseD : ∀ ci ∈ D, PhaseIDecl view cfg D ci := by
  intro ci hci
  rcases mem_D hci with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨rfl, fun _ => rfl⟩
  · exact ⟨rfl, fun _ => rfl⟩
  · exact ⟨rfl, rfl, ⟨0, .succ .zero, rfl, .inr (.inl rfl)⟩, fun h => absurd h (by decide)⟩
  · exact ⟨rfl, fun _ => rfl⟩
  · exact ⟨rfl, fun _ => rfl⟩
  · exact ⟨rfl, rfl, ⟨0, .succ .zero, rfl, .inr (.inl rfl)⟩, fun h => absurd h (by decide)⟩
  · exact .inr (.inr recInFragD)

/-- The term and the read expressions are plain. -/
theorem plainD : PlainExpr cfg e ∧ ∀ ci ∈ D, ∀ x, ReadExpr D ci x → PlainExpr cfg x :=
  ⟨plain_of (by krfl), fun ci hci x hx => plain_of (readAll_of (p := plainB) (by krfl) ci hci x hx)⟩

/-- The only recursor that the term and the read expressions name is `N.rec`, so recursors only in
the fragment's shape. -/
theorem recShapedD :
    RecShaped cfg D e ∧ ∀ ci ∈ D, ∀ x, ReadExpr D ci x → RecShaped cfg D x :=
  ⟨recShaped_of recInFragD (by krfl) (by krfl), fun ci hci x hx =>
    recShaped_of recInFragD (by krfl) (readAll_of (by krfl) ci hci x hx)⟩

/-- The kernames of `D` are distinct. -/
theorem kernD : KernameInj D := kernameInj_of (by krfl)

/-- The block names of `B` and `N` are distinct, and `D` holds no λ□ constant. -/
theorem blockD : BlockNamesInj D := by
  rintro iv₁ iv₂ ⟨c₁, h₁, rfl⟩ ⟨c₂, h₂, rfl⟩
  rcases mem_D h₁ with h | h | h | h | h | h | h <;> cases h <;>
    rcases mem_D h₂ with h | h | h | h | h | h | h <;> cases h <;>
    refine ⟨fun hk => ?_, fun ci hci he => ?_⟩ <;>
    first
    | rfl
    | exact absurd (congrArg Kername.id hk) (by decide)
    | rcases mem_D hci with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases he

/-- The fragment test accepts NV-R's term, by `collectDeps_ok_of` from the premises above. -/
theorem ok_of : ∃ decls', collectDeps view cfg e = .ok decls' :=
  collectDeps_ok_of henv hview he hty rfl subD readD phaseD plainD recShapedD kernD blockD
    (by decide)

end EraseProof.Test.NVR
