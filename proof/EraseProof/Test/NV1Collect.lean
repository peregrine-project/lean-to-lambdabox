import EraseProof.Core.CollectOk
import EraseProof.Test.NV1Final

/-!
# NV-1: the lower bound of the fragment test

The premises of `collectDeps_ok_of` (the fragment test accepts every typed program of the
fragment) on NV-1 (`Test/NV1Data.lean`) with the closure `D` (`Test/NV1Run.lean`), each proved from
the declarations, not from a run of the fragment test: `D` is a sub-environment of the program,
read-closed, every declaration of it is in Phase I, the term and the read expressions are plain and
read no recursor, kernames and block names are distinct, and `D` is within the fuel. `ok_of`
applies `collectDeps_ok_of` to them. The syntactic conditions on expressions are decided by kernel
evaluation of Boolean versions (`constsAll`, `plainB`).
-/

open Lean Erasure

namespace EraseProof.Test

/-- Every constant of `x`, and the structure of every projection of `x`, passes the test `p`. -/
def constsAll (p : Name → Bool) : Expr → Bool
  | .const c _ => p c
  | .app f a => constsAll p f && constsAll p a
  | .lam _ t b _ | .forallE _ t b _ => constsAll p t && constsAll p b
  | .letE _ t v b _ => constsAll p t && constsAll p v && constsAll p b
  | .mdata _ e => constsAll p e
  | .proj S _ e => p S && constsAll p e
  | _ => true

theorem constsIn_of_all {p : Name → Bool} {q : Name → Prop} (hp : ∀ c, p c = true → q c) :
    ∀ {x : Expr}, constsAll p x = true → ConstsIn q x
  | .const .., h => hp _ h
  | .app f a, h => by
    simp only [constsAll, Bool.and_eq_true] at h
    exact ⟨constsIn_of_all hp h.1, constsIn_of_all hp h.2⟩
  | .lam _ t b _, h | .forallE _ t b _, h => by
    simp only [constsAll, Bool.and_eq_true] at h
    exact ⟨constsIn_of_all hp h.1, constsIn_of_all hp h.2⟩
  | .letE _ t v b _, h => by
    simp only [constsAll, Bool.and_eq_true] at h
    exact ⟨constsIn_of_all hp h.1.1, constsIn_of_all hp h.1.2, constsIn_of_all hp h.2⟩
  | .mdata _ e, h => constsIn_of_all hp (x := e) h
  | .proj _ _ e, h => by
    simp only [constsAll, Bool.and_eq_true] at h
    exact ⟨hp _ h.1, constsIn_of_all hp h.2⟩
  | .bvar _, _ | .fvar _, _ | .mvar _, _ | .sort _, _ | .lit _, _ => trivial

/-- A sufficient condition for `PlainExpr` under every configuration, as a Boolean test: no Nat
literal and none of the constants that `nat := .machine` excludes. -/
def plainB : Expr → Bool
  | .fvar _ | .mvar _ | .lit _ => false
  | .sort u => LevelPlain u
  | .const c us => us.all (LevelPlain ·) &&
      !([``Nat.zero, ``Nat.succ, ``Int.ofNat, ``Int.negSucc, ``Nat.casesOn, ``Int.casesOn].contains c)
  | .app f a => plainB f && plainB a
  | .lam _ t b _ | .forallE _ t b _ => plainB t && plainB b
  | .letE _ t v b _ => plainB t && plainB v && plainB b
  | .mdata _ e | .proj _ _ e => plainB e
  | .bvar _ => true

theorem plain_of {cfg : ErasureConfig} : ∀ {x : Expr}, plainB x = true → PlainExpr cfg x
  | .sort _, h => h
  | .const c us, h => by
    simp only [plainB, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
    exact ⟨h.1, fun _ hc => by have := h.2; simp_all⟩
  | .app f a, h | .lam _ f a _, h | .forallE _ f a _, h => by
    simp only [plainB, Bool.and_eq_true] at h
    exact ⟨plain_of h.1, plain_of h.2⟩
  | .letE _ t v b _, h => by
    simp only [plainB, Bool.and_eq_true] at h
    exact ⟨plain_of h.1.1, plain_of h.1.2, plain_of h.2⟩
  | .mdata _ e, h | .proj _ _ e, h => plain_of (x := e) h
  | .bvar _, _ => trivial
  | .fvar _, h | .mvar _, h | .lit _, h => nomatch h

/-- A statement about `f`'s value, when it has one, as a Boolean test. -/
theorem forall_eq_some {α : Type} {f : Option α} {Q : α → Prop} [DecidablePred Q]
    (h : f.all (fun a => decide (Q a)) = true) : ∀ a, f = some a → Q a := by
  rintro a rfl
  simpa using h

/-- Every expression that the traversal reads from a declaration of `decls` (`ReadExpr`) passes the
test `p`. -/
def readAll (decls : List ConstantInfo) (p : Expr → Bool) : Bool :=
  decls.all fun ci => p ci.type && match ci with
    | .defnInfo d => (EvalEnv.casesOn? ⟨decls, fun _ => false⟩ d.name).isSome || p d.value
    | .opaqueInfo o => p o.value
    | _ => true

theorem readAll_of {decls : List ConstantInfo} {p : Expr → Bool} (h : readAll decls p = true) :
    ∀ ci ∈ decls, ∀ x, ReadExpr decls ci x → p x = true := by
  intro ci hci x hx
  have h := List.all_eq_true.mp h ci hci
  rcases hx with rfl | ⟨d, rfl, rfl, hn⟩ | ⟨o, rfl, rfl⟩
  · exact (Bool.and_eq_true _ _ ▸ h).1
  · simp only [Bool.and_eq_true, Bool.or_eq_true] at h
    exact h.2.resolve_left (by simpa using hn)
  · exact (Bool.and_eq_true _ _ ▸ h).2

/-- `c` is not a recursor of `decls`. -/
def notRec (decls : List ConstantInfo) (c : Name) : Bool :=
  match findDecl decls c with
  | some (.recInfo _) => false
  | _ => true

/-- An expression that names no recursor of `decls` other than `r`, which is in the fragment's
shape, names recursors only in the fragment's shape. -/
theorem recShaped_of {cfg : ErasureConfig} {decls : List ConstantInfo} {r : RecursorVal}
    (hr : RecInFragment cfg decls r) (hf : findDecl decls r.name = some (.recInfo r)) {x : Expr}
    (h : constsAll (fun c => c == r.name || notRec decls c) x = true) : RecShaped cfg decls x :=
  constsIn_of_all (fun c h rv hrv => by
    by_cases hc : c = r.name
    · subst hc; rw [hf] at hrv; cases hrv; exact hr
    · simp [notRec, hc, hrv] at h) h

/-- Two module paths differ, as a Boolean test. -/
def mpNe : ModPath → ModPath → Bool
  | .MPfile a, .MPfile b => !decide (a = b)
  | .MPdot m a, .MPdot n b => !decide (a = b) || mpNe m n
  | _, _ => true

theorem ne_of_mpNe : ∀ {a b : ModPath}, mpNe a b = true → a ≠ b
  | .MPfile _, .MPfile _, h, rfl => by simp [mpNe] at h
  | .MPdot m _, .MPdot n _, h, he => by
    cases he
    simp only [mpNe, decide_true, Bool.not_true, Bool.false_or] at h
    exact ne_of_mpNe h rfl
  | .MPfile _, .MPdot .., _, h | .MPdot .., .MPfile _, _, h => nomatch h

/-- The kernames of distinct declarations of `decls` differ, as a Boolean test. -/
def kernB (decls : List ConstantInfo) : Bool :=
  decls.all fun a => decls.all fun b => a.name == b.name ||
    !decide ((toKername a.name).id = (toKername b.name).id) ||
    mpNe (toKername a.name).mp (toKername b.name).mp

theorem mem_of_findDecl {decls : List ConstantInfo} {c : Name} (h : (findDecl decls c).isSome) :
    ∃ ci ∈ decls, ci.name = c := by
  rw [findDecl, List.find?_isSome] at h
  obtain ⟨ci, hci, hc⟩ := h
  exact ⟨ci, hci, beq_iff_eq.mp hc⟩

theorem kernameInj_of {decls : List ConstantInfo} (h : kernB decls = true) : KernameInj decls := by
  intro c₁ c₂ h₁ h₂ hk
  obtain ⟨a, ha, rfl⟩ := mem_of_findDecl h₁
  obtain ⟨b, hb, rfl⟩ := mem_of_findDecl h₂
  have h := List.all_eq_true.mp (List.all_eq_true.mp h a ha) b hb
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_false_iff_not] at h
  rcases h with (h | h) | h
  · exact h
  · exact absurd (congrArg Kername.id hk) h
  · exact absurd (congrArg Kername.mp hk) (ne_of_mpNe h)

end EraseProof.Test

namespace EraseProof.Test.NV1

theorem mem_D {ci : ConstantInfo} (h : ci ∈ D) :
    ci = .recInfo B_rec ∨ ci = .defnInfo B_casesOn ∨ ci = .ctorInfo Bt_ctor ∨
      ci = .ctorInfo Bf_ctor ∨ ci = .inductInfo B_ind ∨ ci = .defnInfo neg_def := by
  simpa [D] using h

/-- `D` is a sub-environment of the program. -/
theorem subD : SubEnv D P := by
  intro ci h
  rcases mem_D h with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem casesOnD : EvalEnv.casesOn? ⟨D, fun _ => false⟩ `B.casesOn = some B_ind := by rfl

/-- The expressions the traversal reads from a declaration of `D`: its type, and `B.neg`'s value
(`B.casesOn`'s is not read: it is a recognized `casesOn`). -/
theorem readExpr_D {ci : ConstantInfo} (hci : ci ∈ D) {Q : Expr → Prop} (hty : Q ci.type)
    (hneg : Q negVal) {x : Expr} (hx : ReadExpr D ci x) : Q x := by
  rcases hx with rfl | ⟨d, hd, rfl, hn⟩ | ⟨o, ho, -⟩
  · exact hty
  · rcases mem_D hci with rfl | rfl | rfl | rfl | rfl | rfl <;> cases hd
    · rw [show B_casesOn.name = `B.casesOn from rfl, casesOnD] at hn; cases hn
    · exact hneg
  · rcases mem_D hci with rfl | rfl | rfl | rfl | rfl | rfl <;> cases ho

/-- The read-closure test, on a declaration's own names. -/
abbrev inD (c : Name) : Bool := (findDecl D c).isSome

theorem constsD {x : Expr} (h : constsAll inD x = true) :
    ConstsIn (fun c => (findDecl D c).isSome = true) x :=
  constsIn_of_all (fun _ h => h) h

/-- `D` is closed under what the traversal reads. -/
theorem readD : ReadClosed D e := by
  refine ⟨constsD (by krfl), by decide, ?_⟩
  intro ci hci
  refine ⟨fun x hx => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine readExpr_D (Q := fun y => ConstsIn (fun c => (findDecl D c).isSome = true) y ∧
      (HasNatLit y = true → (findDecl D ``Nat).isSome = true)) hci ?_ ?_ hx
    · rcases mem_D hci with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨constsD (by krfl), by decide⟩
    · exact ⟨constsD (by krfl), by decide⟩
  · rcases mem_D hci with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rintro iv rfl; rcases mem_D hci with h | h | h | h | h | h <;> cases h; decide
  · rintro cv rfl; rcases mem_D hci with h | h | h | h | h | h <;> cases h <;> rfl
  · rcases mem_D hci with rfl | rfl | rfl | rfl | rfl | rfl <;> exact forall_eq_some (by krfl)
  · rintro iv rfl; rcases mem_D hci with h | h | h | h | h | h <;> cases h; intro h; cases h

/-- Every declaration of `D` is in Phase I. -/
theorem phaseD : ∀ ci ∈ D, PhaseIDecl view cfg D ci := by
  intro ci hci
  rcases mem_D hci with rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inl ⟨`B, B_ind, rfl, casesOnD, rfl⟩
  · exact ⟨rfl, .inl rfl, rfl⟩
  · exact ⟨rfl, fun _ => rfl⟩
  · exact ⟨rfl, fun _ => rfl⟩
  · refine ⟨rfl, rfl, ⟨0, .succ .zero, rfl, .inr (.inl rfl)⟩, fun _ cn hcn cv hcv => ?_⟩
    simp only [B_ind, List.mem_cons, List.not_mem_nil, or_false] at hcn
    rcases hcn with rfl | rfl <;> cases hcv <;> rfl
  · exact ⟨rfl, .inl rfl, rfl⟩

/-- The term and the read expressions are plain. -/
theorem plainD : PlainExpr cfg e ∧ ∀ ci ∈ D, ∀ x, ReadExpr D ci x → PlainExpr cfg x := by
  refine ⟨plain_of (by krfl), fun ci hci x hx => ?_⟩
  refine readExpr_D hci ?_ ?_ hx
  · rcases mem_D hci with rfl | rfl | rfl | rfl | rfl | rfl <;> exact plain_of (by krfl)
  · exact plain_of (by krfl)

/-- `c` is not a recursor of `D`. -/
def notRecD (c : Name) : Bool :=
  match findDecl D c with
  | some (.recInfo _) => false
  | _ => true

/-- An expression that names no recursor of `D` names recursors only in the fragment's shape. -/
theorem recShapedOf {x : Expr} (h : constsAll notRecD x = true) : RecShaped cfg D x :=
  constsIn_of_all (fun c h rv hrv => by simp [notRecD, hrv] at h) h

/-- The term and the read expressions read no recursor, so recursors only in the fragment's
shape. -/
theorem recShapedD :
    RecShaped cfg D e ∧ ∀ ci ∈ D, ∀ x, ReadExpr D ci x → RecShaped cfg D x := by
  refine ⟨recShapedOf (by krfl), fun ci hci x hx => ?_⟩
  refine readExpr_D hci ?_ ?_ hx
  · rcases mem_D hci with rfl | rfl | rfl | rfl | rfl | rfl <;> exact recShapedOf (by krfl)
  · exact recShapedOf (by krfl)

theorem findDecl_isSome {c : Name} (h : (findDecl D c).isSome) :
    c = `B.rec ∨ c = `B.casesOn ∨ c = `B.t ∨ c = `B.f ∨ c = `B ∨ c = `B.neg := by
  rw [findDecl, List.find?_isSome] at h
  obtain ⟨ci, hci, hc⟩ := h
  have hc := beq_iff_eq.mp hc
  rcases mem_D hci with rfl | rfl | rfl | rfl | rfl | rfl <;> subst hc <;> decide

/-- The kernames of `D` are distinct. -/
theorem kernD : KernameInj D := by
  intro c₁ c₂ h₁ h₂ h
  have hid := congrArg Kername.id h
  rcases findDecl_isSome h₁ with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases findDecl_isSome h₂ with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | exact absurd hid (by decide)

/-- The block name of `B` is distinct from the kernames of `B.casesOn` and `B.neg`. -/
theorem blockD : BlockNamesInj D := by
  rintro iv₁ iv₂ ⟨c₁, h₁, rfl⟩ ⟨c₂, h₂, rfl⟩
  rcases mem_D h₁ with h | h | h | h | h | h <;> cases h
  rcases mem_D h₂ with h | h | h | h | h | h <;> cases h
  refine ⟨fun _ => rfl, fun ci hci he hk => ?_⟩
  have hid := congrArg Kername.id hk
  rcases mem_D hci with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | (cases he; done) | exact absurd hid (by decide)

/-- The fragment test accepts NV-1's term, by `collectDeps_ok_of` from the premises above. -/
theorem ok_of : ∃ decls', collectDeps view cfg e = .ok decls' :=
  collectDeps_ok_of henv hview he hty rfl subD readD phaseD plainD recShapedD kernD blockD
    (by decide)

end EraseProof.Test.NV1
