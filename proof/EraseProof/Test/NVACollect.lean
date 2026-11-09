import EraseProof.Test.NV1Collect
import EraseProof.Test.NVAFinal

/-!
# NV-A: the lower bound of the fragment test on `Init`'s `Nat.add`

The premises of `collectDeps_ok_of` on NV-A (`Test/NVAData.lean`) under
`extern := .preferLogical, structural := .kernel, nat := .peano`, with the closure `D`
(`Test/NVARun.lean`) and the view that holds `Nat.add`'s compiled companion `Nat.add._unsafe_rec`,
proved from the declarations, not from a run of the fragment test, as for NV-S
(`Test/NVSCollect.lean`). `Nat.add` is in Phase I as a definition by structural recursion
(`isStructuralRecursive`), the other definitions have no companion; `Nat.rec` through the
recognized `Nat.casesOn`, `PProd.rec`, `PUnit.rec` and `OfNat.rec` through their single
constructor. The values of `Nat.casesOn`, `Nat.brecOn.go` and `Nat.below` read `Nat.rec`, in the
shape the fragment admits (`RecInFragment`); it is the only recursor the term and the read
expressions name. The term holds Nat literals, which `nat := .peano` admits (`plainP`). `ok_of`
applies `collectDeps_ok_of` to them.
-/

open Lean Erasure

namespace EraseProof.Test.NVA

open EraseProof.Test.NVL (Nat_ind Zero_ctor Succ_ctor Nat_rec)
open EraseProof.Test.NVS (uu uv l1 PUnit_ind PUnit_unit PUnit_rec PProd_ind PProd_mk PProd_rec)

/-- A sufficient condition for `PlainExpr` under `nat := .peano`, as a Boolean test: Nat literals
admitted. -/
def plainP : Expr → Bool
  | .fvar _ | .mvar _ | .lit (.strVal _) => false
  | .lit (.natVal _) => true
  | .sort u => LevelPlain u
  | .const _ us => us.all (LevelPlain ·)
  | .app f a => plainP f && plainP a
  | .lam _ t b _ | .forallE _ t b _ => plainP t && plainP b
  | .letE _ t v b _ => plainP t && plainP v && plainP b
  | .mdata _ e | .proj _ _ e => plainP e
  | .bvar _ => true

theorem plainP_of : ∀ {x : Expr}, plainP x = true → PlainExpr cfg x
  | .sort _, h => h
  | .const c us, h => by
    simp only [plainP, List.all_eq_true] at h
    exact ⟨h, fun hc => nomatch (show Config.Nat.peano = .machine from hc)⟩
  | .lit (.natVal _), _ => rfl
  | .app f a, h | .lam _ f a _, h | .forallE _ f a _, h => by
    simp only [plainP, Bool.and_eq_true] at h
    exact ⟨plainP_of h.1, plainP_of h.2⟩
  | .letE _ t v b _, h => by
    simp only [plainP, Bool.and_eq_true] at h
    exact ⟨plainP_of h.1.1, plainP_of h.1.2, plainP_of h.2⟩
  | .mdata _ e, h | .proj _ _ e, h => plainP_of (x := e) h
  | .bvar _, _ => trivial
  | .fvar _, h | .mvar _, h | .lit (.strVal _), h => nomatch h

theorem mem_D {ci : ConstantInfo} (h : ci ∈ D) :
    ci = .defnInfo inst_def ∨
      ci = .ctorInfo OfNat_mk ∨
      ci = .recInfo OfNat_rec ∨
      ci = .inductInfo OfNat_ind ∨
      ci = .defnInfo ofNat_def ∨
      ci = .defnInfo Nat_casesOn ∨
      ci = .defnInfo match_def ∨
      ci = .defnInfo add_f ∨
      ci = .defnInfo Nat_brecOn_go ∨
      ci = .ctorInfo PProd_mk ∨
      ci = .recInfo PProd_rec ∨
      ci = .inductInfo PProd_ind ∨
      ci = .ctorInfo PUnit_unit ∨
      ci = .recInfo PUnit_rec ∨
      ci = .inductInfo PUnit_ind ∨
      ci = .recInfo Nat_rec ∨
      ci = .defnInfo Nat_below ∨
      ci = .defnInfo Nat_brecOn ∨
      ci = .ctorInfo Succ_ctor ∨
      ci = .ctorInfo Zero_ctor ∨
      ci = .inductInfo Nat_ind ∨
      ci = .defnInfo add_def := by
  simpa [D] using h

/-- `D` is a sub-environment of the program. -/
theorem subD : SubEnv D P := by
  intro ci h
  rcases mem_D h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The read-closure test, on a declaration's own names. -/
abbrev inD (c : Name) : Bool := (findDecl D c).isSome

/-- `D` is closed under what the traversal reads. -/
theorem readD : ReadClosed D e := by
  refine ⟨constsIn_of_all (fun _ h => h) (p := inD) (by krfl),
    fun _ => show (findDecl D `Nat).isSome = true by krfl, ?_⟩
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

/-- `Nat.rec` is in the shape the fragment admits, over the block `[Nat]` that it reads from `D`. -/
theorem recInFragD : RecInFragment cfg D Nat_rec :=
  ⟨`Nat, Nat_ind, [Zero_ctor, Succ_ctor], rfl, rfl, by krfl, by krfl, by krfl⟩

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
  rcases mem_D hci with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨rfl, .inl (by krfl), rfl⟩
  · exact ⟨rfl, fun _ => rfl⟩
  · exact .inr (.inl ⟨`OfNat, OfNat_ind, rfl, by krfl, rfl⟩)
  · exact ⟨rfl, rfl, ⟨2, .succ (.param `u), rfl, .inr (.inl rfl)⟩,
      fun h => absurd h (by decide)⟩
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
  · exact .inl ⟨`Nat, Nat_ind, rfl, by krfl, by krfl⟩
  · exact ⟨rfl, .inl (by krfl), rfl⟩
  · exact ⟨rfl, .inl (by krfl), rfl⟩
  · exact ⟨rfl, fun _ => rfl⟩
  · exact ⟨rfl, fun _ => rfl⟩
  · refine ⟨rfl, rfl, ⟨0, l1, rfl, .inr (.inl rfl)⟩, fun _ cn hcn cv hcv => ?_⟩
    simp only [Nat_ind, List.mem_cons, List.not_mem_nil, or_false] at hcn
    rcases hcn with rfl | rfl
    · rw [show findDecl D `Nat.zero = some (.ctorInfo Zero_ctor) by krfl] at hcv; cases hcv; rfl
    · rw [show findDecl D `Nat.succ = some (.ctorInfo Succ_ctor) by krfl] at hcv; cases hcv; rfl
  · exact ⟨rfl, .inr (by krfl), rfl⟩

/-- The term and the read expressions are plain. -/
theorem plainD : PlainExpr cfg e ∧ ∀ ci ∈ D, ∀ x, ReadExpr D ci x → PlainExpr cfg x :=
  ⟨plainP_of (by krfl), fun ci hci x hx => plainP_of (readAll_of (p := plainP) (by krfl) ci hci x hx)⟩

/-- The only recursor that the term and the read expressions name is `Nat.rec`, so recursors only
in the fragment's shape. -/
theorem recShapedD :
    RecShaped cfg D e ∧ ∀ ci ∈ D, ∀ x, ReadExpr D ci x → RecShaped cfg D x :=
  ⟨recShaped_of recInFragD (by krfl) (by krfl), fun ci hci x hx =>
    recShaped_of recInFragD (by krfl) (readAll_of (by krfl) ci hci x hx)⟩

/-- The kernames of `D` are distinct. -/
theorem kernD : KernameInj D := kernameInj_of (by krfl)

/-- The block names of `PProd`, `PUnit`, `Nat` and `OfNat` are distinct from each other and from the
kernames of the definitions of `D`. -/
theorem blockD : BlockNamesInj D := by
  rintro iv₁ iv₂ ⟨c₁, h₁, rfl⟩ ⟨c₂, h₂, rfl⟩
  rcases mem_D h₁ with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    cases h <;>
    rcases mem_D h₂ with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    cases h <;>
    refine ⟨fun hk => ?_, fun ci hci he => ?_⟩ <;>
    first
    | rfl
    | exact absurd (congrArg Kername.id hk) (by decide)
    | rcases mem_D hci with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | (cases he; done) | exact fun hk => absurd (congrArg Kername.id hk) (by decide)

/-- The fragment test accepts NV-A's term under
`extern := .preferLogical, structural := .kernel, nat := .peano`, by `collectDeps_ok_of` from the
premises above. -/
theorem ok_of : ∃ decls', collectDeps view cfg e = .ok decls' :=
  collectDeps_ok_of henv hview he hty rfl subD readD phaseD plainD recShapedD kernD blockD
    (by decide)

end EraseProof.Test.NVA
