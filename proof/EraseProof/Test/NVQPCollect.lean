import EraseProof.Test.NV1Collect
import EraseProof.Test.NVQPFinal

/-!
# NV-QP: the lower bound of the fragment test on unordered pairs

The premises of `collectDeps_ok_of` on NV-QP (`Test/NVQPData.lean`) with the closure `D`
(`Test/NVQPRun.lean`), proved from the declarations, not from a run of the fragment test, as for
NV-1 (`Test/NV1Collect.lean`). The closure holds the definitions the term reaches, the theorem
`orU._proof_1` (in Phase I as a theorem, whose value is not read), the quotient constants
`Quot.mk`, `Quot.lift` and `Quot`, and the blocks of `B`, `Prod` and `Eq`: `B.rec` is in Phase I
through the recognized `B.casesOn`, `Prod.rec` and `Eq.rec` through their single constructor. No
read expression names a recursor. `ok_of` applies `collectDeps_ok_of` to them.
-/

open Lean Erasure

namespace EraseProof.Test.NVQP

open EraseProof.Test.NV1 (B_ind Bf_ctor Bt_ctor B_rec B_casesOn)
open EraseProof.Test.NVP (Eq_ind Eq_refl Eq_rec)
open EraseProof.Test.NVQ (Quot_val QuotMk_val QuotLift_val)

theorem mem_D {ci : ConstantInfo} (h : ci ∈ D) :
    ci = .quotInfo QuotMk_val ∨
      ci = .thmInfo resp_thm ∨
      ci = .recInfo B_rec ∨
      ci = .defnInfo B_casesOn ∨
      ci = .defnInfo orB_match_1 ∨
      ci = .defnInfo orB_def ∨
      ci = .quotInfo QuotLift_val ∨
      ci = .defnInfo Prod_fst ∨
      ci = .defnInfo Prod_snd ∨
      ci = .ctorInfo Eq_refl ∨
      ci = .recInfo Eq_rec ∨
      ci = .inductInfo Eq_ind ∨
      ci = .defnInfo swapR_def ∨
      ci = .ctorInfo Prod_mk ∨
      ci = .recInfo Prod_rec ∨
      ci = .inductInfo Prod_ind ∨
      ci = .quotInfo Quot_val ∨
      ci = .defnInfo orU_def ∨
      ci = .ctorInfo Bt_ctor ∨
      ci = .ctorInfo Bf_ctor ∨
      ci = .inductInfo B_ind ∨
      ci = .defnInfo useTF_def := by
  simpa [D] using h

/-- `D` is a sub-environment of the program. -/
theorem subD : SubEnv D P := by
  intro ci h
  rcases mem_D h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

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
  all_goals rcases mem_D hci with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | decide
    | exact forall_eq_some (by krfl)
    | (rintro _ h; cases h; done)
    | (rintro _ h; cases h; decide)

/-- Every declaration of `D` is in Phase I. -/
theorem phaseD : ∀ ci ∈ D, PhaseIDecl view cfg D ci := by
  intro ci hci
  rcases mem_D hci with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact trivial
  · exact trivial
  · exact .inl ⟨`B, B_ind, rfl, by krfl, by krfl⟩
  · exact ⟨rfl, .inl (by krfl), rfl⟩
  · exact ⟨rfl, .inl (by krfl), rfl⟩
  · exact ⟨rfl, .inl (by krfl), rfl⟩
  · exact trivial
  · exact ⟨rfl, .inl (by krfl), rfl⟩
  · exact ⟨rfl, .inl (by krfl), rfl⟩
  · exact ⟨rfl, fun _ => rfl⟩
  · exact .inr (.inl ⟨`Eq, Eq_ind, rfl, by krfl, rfl⟩)
  · exact ⟨rfl, rfl, ⟨3, .zero, rfl, .inl rfl⟩, fun h => absurd h (by decide)⟩
  · exact ⟨rfl, .inl (by krfl), rfl⟩
  · exact ⟨rfl, fun _ => rfl⟩
  · exact .inr (.inl ⟨`Prod, Prod_ind, rfl, by krfl, rfl⟩)
  · exact ⟨rfl, rfl, ⟨2, .max (.succ uu) (.succ uv), rfl, .inr (.inl rfl)⟩,
      fun h => absurd h (by decide)⟩
  · exact trivial
  · exact ⟨rfl, .inl (by krfl), rfl⟩
  · exact ⟨rfl, fun _ => rfl⟩
  · exact ⟨rfl, fun _ => rfl⟩
  · refine ⟨rfl, rfl, ⟨0, .succ .zero, rfl, .inr (.inl rfl)⟩, fun _ cn hcn cv hcv => ?_⟩
    simp only [B_ind, List.mem_cons, List.not_mem_nil, or_false] at hcn
    rcases hcn with rfl | rfl
    · rw [show findDecl D `B.f = some (.ctorInfo Bf_ctor) by krfl] at hcv; cases hcv; rfl
    · rw [show findDecl D `B.t = some (.ctorInfo Bt_ctor) by krfl] at hcv; cases hcv; rfl
  · exact ⟨rfl, .inl (by krfl), rfl⟩

/-- The term and the read expressions are plain. -/
theorem plainD : PlainExpr cfg e ∧ ∀ ci ∈ D, ∀ x, ReadExpr D ci x → PlainExpr cfg x :=
  ⟨plain_of (by krfl), fun ci hci x hx => plain_of (readAll_of (p := plainB) (by krfl) ci hci x hx)⟩

/-- An expression that names no recursor of `D` names recursors only in the fragment's shape. -/
theorem recShapedOf {x : Expr} (h : constsAll (notRec D) x = true) : RecShaped cfg D x :=
  constsIn_of_all (fun c h rv hrv => by simp [notRec, hrv] at h) h

/-- The term and the read expressions name no recursor (`B.rec` is named only by `B.casesOn`'s
value, which the traversal does not read), so recursors only in the fragment's shape. -/
theorem recShapedD :
    RecShaped cfg D e ∧ ∀ ci ∈ D, ∀ x, ReadExpr D ci x → RecShaped cfg D x :=
  ⟨recShapedOf (by krfl), fun ci hci x hx => recShapedOf (readAll_of (by krfl) ci hci x hx)⟩

/-- The kernames of `D` are distinct. -/
theorem kernD : KernameInj D := kernameInj_of (by krfl)

/-- The block names of `B`, `Prod` and `Eq` are distinct from each other and from the kernames of
the constants of `D`. -/
theorem blockD : BlockNamesInj D := by
  rintro iv₁ iv₂ ⟨c₁, h₁, rfl⟩ ⟨c₂, h₂, rfl⟩
  rcases mem_D h₁ with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> cases h <;>
    rcases mem_D h₂ with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> cases h <;>
    refine ⟨fun hk => ?_, fun ci hci he => ?_⟩ <;>
    first
    | rfl
    | exact absurd (congrArg Kername.id hk) (by decide)
    | rcases mem_D hci with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | (cases he; done) | exact fun hk => absurd (congrArg Kername.id hk) (by decide)

/-- The fragment test accepts NV-QP's term, by `collectDeps_ok_of` from the premises above. -/
theorem ok_of : ∃ decls', collectDeps view cfg e = .ok decls' :=
  collectDeps_ok_of henv hview he hty rfl subD readD phaseD plainD recShapedD kernD blockD
    (by decide)

end EraseProof.Test.NVQP
