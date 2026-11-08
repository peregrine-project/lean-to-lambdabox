import EraseProof.Test.NVRCollect
import EraseProof.Test.NVSFinal

/-!
# NV-S: the lower bound of the fragment test on structural recursion

The premises of `collectDeps_ok_of` on NV-S (`Test/NVSData.lean`) under `structural := .kernel`,
with the closure `D` (`Test/NVSRun.lean`) and the view that holds `add`'s compiled companion
`add._unsafe_rec`, proved from the declarations, not from a run of the fragment test, as for NV-1
(`Test/NV1Collect.lean`). `add` is in Phase I as a definition by structural recursion
(`isStructuralRecursive`), the other definitions have no companion; `N.rec` through the recognized
`N.casesOn`, `PProd.rec` and `PUnit.rec` through their single constructor. The values of
`N.brecOn.go` and `N.below` read `N.rec`, in the shape the fragment admits (`RecInFragment`); it is
the only recursor the term and the read expressions name. `ok_of` applies `collectDeps_ok_of` to
them.
-/

open Lean Erasure

namespace EraseProof.Test.NVS

open EraseProof.Test.NVR (N_ind Nz_ctor Ns_ctor N_rec)

theorem mem_D {ci : ConstantInfo} (h : ci ∈ D) :
    ci = .defnInfo Unit_unit ∨ ci = .defnInfo N_casesOn ∨ ci = .defnInfo Unit_def ∨
      ci = .defnInfo add_match_1 ∨ ci = .defnInfo add_f ∨ ci = .defnInfo N_brecOn_go ∨
      ci = .ctorInfo PProd_mk ∨ ci = .recInfo PProd_rec ∨ ci = .inductInfo PProd_ind ∨
      ci = .ctorInfo PUnit_unit ∨ ci = .recInfo PUnit_rec ∨ ci = .inductInfo PUnit_ind ∨
      ci = .recInfo N_rec ∨ ci = .defnInfo N_below ∨ ci = .defnInfo N_brecOn ∨
      ci = .ctorInfo Ns_ctor ∨ ci = .ctorInfo Nz_ctor ∨ ci = .inductInfo N_ind ∨
      ci = .defnInfo add_def := by
  simpa [D] using h

/-- `D` is a sub-environment of the program. -/
theorem subD : SubEnv D P := by
  intro ci h
  rcases mem_D h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

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
  all_goals rcases mem_D hci with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | decide
    | exact forall_eq_some (by krfl)
    | (rintro _ h; cases h; done)
    | (rintro _ h; cases h; decide)

/-- `N.rec` is in the shape the fragment admits, over the block `[N]` that it reads from `D`. -/
theorem recInFragD : RecInFragment cfg D N_rec :=
  ⟨`N, N_ind, [Nz_ctor, Ns_ctor], rfl, rfl, by krfl, by krfl, by krfl⟩

/-- `PUnit` has no field, so the traversal does not eliminate it. -/
theorem notElimPU : ¬ Eliminated D PUnit_ind := by
  rintro (h | ⟨cn, cv, hc, hf, hn⟩)
  · exact absurd h (by decide)
  · cases hc
    rw [show findDecl D `PUnit.unit = some (.ctorInfo PUnit_unit) by krfl] at hf
    cases hf
    exact absurd hn (by decide)

/-- Every declaration of `D` is in Phase I. -/
theorem phaseD : ∀ ci ∈ D, PhaseIDecl view cfg D ci := by
  intro ci hci
  rcases mem_D hci with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨rfl, .inl (by krfl), rfl⟩
  · exact ⟨rfl, .inl (by krfl), rfl⟩
  · exact ⟨rfl, .inl (by krfl), rfl⟩
  · exact ⟨rfl, .inl (by krfl), rfl⟩
  · exact ⟨rfl, .inl (by krfl), rfl⟩
  · exact ⟨rfl, .inl (by krfl), rfl⟩
  · exact ⟨rfl, fun _ => rfl⟩
  · exact .inr (.inl ⟨`PProd, PProd_ind, rfl, by krfl, rfl⟩)
  · exact ⟨rfl, rfl, ⟨2, .max (.max l1 uu) uv, rfl, .inr (.inl rfl)⟩,
      fun h => absurd h (by decide)⟩
  · exact ⟨rfl, fun _ => rfl⟩
  · exact .inr (.inl ⟨`PUnit, PUnit_ind, rfl, by krfl, rfl⟩)
  · exact ⟨rfl, rfl, ⟨0, uu, rfl, .inr (.inr ⟨by krfl, notElimPU⟩)⟩,
      fun h => absurd h (by decide)⟩
  · exact .inl ⟨`N, N_ind, rfl, by krfl, by krfl⟩
  · exact ⟨rfl, .inl (by krfl), rfl⟩
  · exact ⟨rfl, .inl (by krfl), rfl⟩
  · exact ⟨rfl, fun _ => rfl⟩
  · exact ⟨rfl, fun _ => rfl⟩
  · refine ⟨rfl, rfl, ⟨0, l1, rfl, .inr (.inl rfl)⟩, fun _ cn hcn cv hcv => ?_⟩
    simp only [N_ind, List.mem_cons, List.not_mem_nil, or_false] at hcn
    rcases hcn with rfl | rfl
    · rw [show findDecl D `N.z = some (.ctorInfo Nz_ctor) by krfl] at hcv; cases hcv; rfl
    · rw [show findDecl D `N.s = some (.ctorInfo Ns_ctor) by krfl] at hcv; cases hcv; rfl
  · exact ⟨rfl, .inr (by krfl), rfl⟩

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

/-- The block names of `PProd`, `PUnit` and `N` are distinct from each other and from the kernames
of the definitions of `D`. -/
theorem blockD : BlockNamesInj D := by
  rintro iv₁ iv₂ ⟨c₁, h₁, rfl⟩ ⟨c₂, h₂, rfl⟩
  rcases mem_D h₁ with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    cases h <;>
    rcases mem_D h₂ with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    cases h <;>
    refine ⟨fun hk => ?_, fun ci hci he => ?_⟩ <;>
    first
    | rfl
    | exact absurd (congrArg Kername.id hk) (by decide)
    | rcases mem_D hci with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | (cases he; done) | exact fun hk => absurd (congrArg Kername.id hk) (by decide)

/-- The fragment test accepts NV-S's term under `structural := .kernel`, by `collectDeps_ok_of`
from the premises above. -/
theorem ok_of : ∃ decls', collectDeps view cfg e = .ok decls' :=
  collectDeps_ok_of henv hview he hty rfl subD readD phaseD plainD recShapedD kernD blockD
    (by decide)

end EraseProof.Test.NVS
