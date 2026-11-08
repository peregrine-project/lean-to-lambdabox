import EraseProof.Test.NVQPData
import EraseProof.Test.NVSDefs

/-!
# NV-QP: the Metalean block of `Prod`

The Metalean block of `Init`'s `Prod.{u, v} (α : Type u) (β : Type v) : Type (max u v)`
(`prBlock`: two parameters, one constructor with the two ordinary fields `fst : α` and `snd : β`,
a structure; the signature is `PProd`'s, `Test/NVSBlocks.lean`), the typing of its terms in any
environment whose head holds it, the η-terms the translator builds for its constants
(`Frontend.indTerm`, `ctorTerm`, `recrTerm`), typed at the translations of the constants' Lean
types, and the values of `Prod.fst` and `Prod.snd`, whose primitive projections are Metalean's
structure projections (`Inductive.IsStructure.projTerm`). For `Test/NVQPModel.lean`.
-/

open Lean Metalean

namespace EraseProof.Test.NVQP

open EraseProof.Test.NV1 (typed_of_eq var_of_get app_typed fin0_eq)
open EraseProof.Test.NVS (ppSig ppCtorSig mPP mPPmk q0 q1 r0 r1 r2 ppMotM ppMinM ppRecBody)

/-- The sort `max (u + 1) (v + 1)` of `Prod.{u, v}`. -/
abbrev prLevel {ℓ : Nat} (u v : Level ℓ) : Level ℓ := .max (.succ u) (.succ v)

/-- `Prod.{u, v} (α : Type u) (β : Type v) : Type (max u v)` with the fields `fst : α`,
`snd : β`, as a Metalean block. -/
@[reducible] def prBlock {ζ : Sigs} : Inductive ζ ppSig where
  params := #t[.sort (.succ (.param 0)), .sort (.succ (.param 1))]
  indices _ := .nil
  level := prLevel (.param 0) (.param 1)
  ctors _ _ := {
    ordinary
      | ⟨0, _⟩ => ⟨.var ⟨0, by simp⟩, .succ (.param 0)⟩
      | ⟨1, _⟩ => ⟨.var ⟨1, by simp⟩, .succ (.param 1)⟩
    recursive f := Fin.elim0 f
    targetIndices i := Fin.elim0 i }

@[simp] theorem prBlock_map {ζ₁ ζ₂ : Sigs} (pre : ζ₁ ⟶ ζ₂) :
    (@prBlock ζ₁).map pre = @prBlock ζ₂ := by
  dsimp [Inductive.map]
  congr
  funext s c
  refine Fin.cases ?_ (fun i => Fin.elim0 i) s
  refine Fin.cases ?_ (fun i => Fin.elim0 i) c
  dsimp [Ctor.map, Field.map]
  congr
  · funext f
    refine Fin.cases ?_ (fun f => ?_) f
    · simp
    · refine Fin.cases ?_ (fun i => Fin.elim0 i) f
      simp
  · funext i; exact Fin.elim0 i
  · funext i; exact Fin.elim0 i

theorem prLevel_ge {ℓ : Nat} {u v : Level ℓ} : Metalean.Level.one ≤ prLevel u v :=
  fun ν => by simp

theorem prBlock_wf {ζ : Sigs} (E : Env ζ) : InductiveWF E prBlock :=
  ⟨.snoc (.snoc .nil ⟨_, trivial, .sortDF⟩) ⟨_, trivial, .sortDF⟩,
    fun _ => .nil,
    fun _ _ => {
      ordinary
        | ⟨0, _⟩ => ⟨.var .sortDF, fun ν => by simp [Nat.imax]⟩
        | ⟨1, _⟩ => ⟨.var .sortDF, fun ν => by simp [Nat.imax]⟩
      recursive f := Fin.elim0 f
      targetIndices i := Fin.elim0 i
    }⟩

theorem largeElimPr {ζ : Sigs} : (prBlock (ζ := ζ)).LargeElim :=
  fun _ => .large (prLevel_ge (u := .param 0) (v := .param 1))

/-- `Prod` is a structure: its constructor `Prod.mk` is the only one, without indices or recursive
fields, and it eliminates into every sort. -/
theorem prStruct {ζ : Sigs} : (prBlock (ζ := ζ)).IsStructure 0 0 where
  sort_unique _ := Subsingleton.elim _ _
  ctor_unique _ := Subsingleton.elim _ _
  no_indices := ⟨fun i => Fin.elim0 i⟩
  no_recursive := ⟨fun i => Fin.elim0 i⟩
  sortLargeElim := .large (prLevel_ge (u := .param 0) (v := .param 1))

section Prod
variable {ζ : Sigs} {E : Env ζ} {η : Head ζ (.inductive ppSig)} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n}

theorem recAllowedPr (hp : (E.get η).block = prBlock) {ls : Fin 2 → Level ℓ} {l : Level ℓ} :
    (E.get η).block.RecAllowed ls l := by
  rw [hp]; exact largeElimPr.recAllowed ls l

theorem prParams (hp : (E.get η).block = prBlock) {u v : Level ℓ} {α₁ α₂ β₁ β₂ : Expr ζ ℓ n}
    (hα : E[Γ] ⊢ α₁ ≡ α₂ : .sort (.succ u)) (hβ : E[Γ] ⊢ β₁ ≡ β₂ : .sort (.succ v)) :
    ∀ p, E[Γ] ⊢ (![α₁, β₁] : Fin 2 → Expr ζ ℓ n) p ≡ (![α₂, β₂] : Fin 2 → Expr ζ ℓ n) p :
      (E.get η).block.paramType ![u, v] ![α₁, β₁] p := by
  intro p; fin_cases p <;> rw [hp]
  · simpa [Inductive.paramType, Ctx.entry] using hα
  · simpa [Inductive.paramType, Ctx.entry] using hβ

theorem mPr_defeq (hp : (E.get η).block = prBlock) {u v : Level ℓ} {α₁ α₂ β₁ β₂ : Expr ζ ℓ n}
    (hα : E[Γ] ⊢ α₁ ≡ α₂ : .sort (.succ u)) (hβ : E[Γ] ⊢ β₁ ≡ β₂ : .sort (.succ v)) :
    E[Γ] ⊢ mPP η u v α₁ β₁ ≡ mPP η u v α₂ β₂ : .sort (prLevel u v) := by
  have h := Defeq.indDF (E := E) (Γ := Γ) (η := η) (s := 0) (ls := ![u, v]) (ps₁ := ![α₁, β₁])
    (ps₂ := ![α₂, β₂]) (is₁ := Fin.elim0) (is₂ := Fin.elim0) (prParams hp hα hβ)
    (fun i => Fin.elim0 i)
  rw [hp] at h
  simpa [mPP] using h

theorem mPr_typed (hp : (E.get η).block = prBlock) {u v : Level ℓ} {α β : Expr ζ ℓ n}
    (hα : E[Γ] ⊢ α : .sort (.succ u)) (hβ : E[Γ] ⊢ β : .sort (.succ v)) :
    E[Γ] ⊢ mPP η u v α β : .sort (prLevel u v) :=
  mPr_defeq hp hα hβ

theorem mPrmk_typed (hp : (E.get η).block = prBlock) {u v : Level ℓ} {α β a b : Expr ζ ℓ n}
    (hα : E[Γ] ⊢ α : .sort (.succ u)) (hβ : E[Γ] ⊢ β : .sort (.succ v)) (ha : E[Γ] ⊢ a : α)
    (hb : E[Γ] ⊢ b : β) :
    E[Γ] ⊢ mPPmk η u v α β a b : mPP η u v α β := by
  have h := Defeq.ctorDF (E := E) (Γ := Γ) (η := η) (s := 0) (c := 0) (ls := ![u, v])
    (ps₁ := ![α, β]) (ps₂ := ![α, β]) (fds₁ := ![a, b]) (fds₂ := ![a, b])
    (recFds₁ := Fin.elim0) (recFds₂ := Fin.elim0)
    (fieldLevels := ![.succ u, .succ v]) (recFieldLevels := fun f => Fin.elim0 f)
    (prParams hp hα hβ)
    (fun f => by
      fin_cases f <;> rw [hp]
      · simp [Expr.subst]; exact ha
      · simp [Expr.subst]; exact hb)
    (fun f => Fin.elim0 f)
    (fun f => by
      fin_cases f <;> rw [hp]
      · simp [Ctor.ordinaryFieldExpr, Expr.subst]; exact hα
      · simp [Ctor.ordinaryFieldExpr, Expr.subst]; exact hβ)
    (fun f => Fin.elim0 f)
    (by
      have := mPr_typed hp hα hβ
      rw [hp]
      convert this using 2
      · simp only [mPP]; congr 1; funext i; exact i.elim0
      · simp only [mPP]; congr 1; funext i; exact i.elim0
      · simp)
  unfold mPPmk mPP
  convert h using 2

end Prod

/-! ## `Prod`'s, `Prod.mk`'s and `Prod.rec`'s η-terms -/

section PrTerms
variable {ζ : Sigs} {E : Env ζ} {η : Head ζ (.inductive ppSig)}

/-- `Prod`'s type `Type u → Type v → Type (max u v)` (levels `u`, `v` = parameters 0, 1). -/
def prTyM : Expr ζ 2 0 :=
  .forallE (.sort (.succ q0)) (.forallE (.sort (.succ q1)) (.sort (prLevel q0 q1)))

/-- `Prod`'s η-term `fun α β => Prod α β`. -/
def prTermM (η : Head ζ (.inductive ppSig)) : Expr ζ 2 0 :=
  .lam (.sort (.succ q0)) (.lam (.sort (.succ q1)) (mPP η q0 q1 #0 #1))

/-- `Prod.mk`'s type `{α : Type u} → {β : Type v} → α → β → Prod α β`. -/
def prMkTyM (η : Head ζ (.inductive ppSig)) : Expr ζ 2 0 :=
  .forallE (.sort (.succ q0)) (.forallE (.sort (.succ q1)) (.forallE #0 (.forallE #1
    (mPP η q0 q1 #0 #1))))

/-- `Prod.mk`'s η-term. -/
def prMkTermM (η : Head ζ (.inductive ppSig)) : Expr ζ 2 0 :=
  .lam (.sort (.succ q0)) (.lam (.sort (.succ q1)) (.lam #0 (.lam #1 (mPPmk η q0 q1 #0 #1 #2 #3))))

theorem indTerm_eqPr (hp : (E.get η).block = prBlock) :
    Frontend.indTerm (E.get η).block η 0 ![q0, q1] = prTermM η := by
  rw [hp]
  show Metalean.Expr.lam _ (Metalean.Expr.lam _ _) = _
  simp only [prTermM]
  pps [Inductive.argTele]

theorem ctorTerm_eqPr (hp : (E.get η).block = prBlock) :
    Frontend.ctorTerm (E.get η).block η 0 0 ![q0, q1] [0, 1] = .ok (prMkTermM η) := by
  rw [hp]
  have : (match Frontend.ctorTerm (prBlock (ζ := ζ)) η 0 0 ![q0, q1] [0, 1] with
      | .ok t => t | .error _ => .prop) = prMkTermM η := by
    show Metalean.Expr.lam _ (Metalean.Expr.lam _ (Metalean.Expr.lam _ (Metalean.Expr.lam _ _))) = _
    simp only [prMkTermM]
    pps
  rw [← this]
  rfl

theorem prTermM_typed (hp : (E.get η).block = prBlock) : E[.nil] ⊢ prTermM η : prTyM := by
  have h1 : E[(#t[.sort (.succ q0)] : Ctx ζ 2 0 1)] ⊢ ok := .snoc .nil ⟨_, .sortDF⟩
  have hΓ : E[(#t[.sort (.succ q0), .sort (.succ q1)] : Ctx ζ 2 0 2)] ⊢ ok :=
    .snoc h1 ⟨_, .sortDF⟩
  have hα : E[(#t[.sort (.succ q0), .sort (.succ q1)] : Ctx ζ 2 0 2)] ⊢ #0 : .sort (.succ q0) :=
    var_of_get hΓ ⟨0, by decide⟩ (by pps)
  have hβ : E[(#t[.sort (.succ q0), .sort (.succ q1)] : Ctx ζ 2 0 2)] ⊢ #1 : .sort (.succ q1) :=
    var_of_get hΓ ⟨1, by decide⟩ (by pps)
  have h := mPr_typed (η := η) hp hα hβ
  exact Ctx.lam_congr (Γ := .nil) (Δ := #t[.sort (.succ q0), .sort (.succ q1)]) hΓ h

theorem prMkTermM_typed (hp : (E.get η).block = prBlock) :
    E[.nil] ⊢ prMkTermM η : prMkTyM η := by
  have h1 : E[(#t[.sort (.succ q0)] : Ctx ζ 2 0 1)] ⊢ ok := .snoc .nil ⟨_, .sortDF⟩
  have h2 : E[(#t[.sort (.succ q0), .sort (.succ q1)] : Ctx ζ 2 0 2)] ⊢ ok := .snoc h1 ⟨_, .sortDF⟩
  have h3 : E[(#t[.sort (.succ q0), .sort (.succ q1), #0] : Ctx ζ 2 0 3)] ⊢ ok :=
    .snoc h2 ⟨_, var_of_get h2 ⟨0, by decide⟩ (by pps)⟩
  have hΓ : E[(#t[.sort (.succ q0), .sort (.succ q1), #0, #1] : Ctx ζ 2 0 4)] ⊢ ok :=
    .snoc h3 ⟨_, var_of_get h3 ⟨1, by decide⟩ (by pps)⟩
  have hα : E[(#t[.sort (.succ q0), .sort (.succ q1), #0, #1] : Ctx ζ 2 0 4)] ⊢ #0 :
      .sort (.succ q0) := var_of_get hΓ ⟨0, by decide⟩ (by pps)
  have hβ : E[(#t[.sort (.succ q0), .sort (.succ q1), #0, #1] : Ctx ζ 2 0 4)] ⊢ #1 :
      .sort (.succ q1) := var_of_get hΓ ⟨1, by decide⟩ (by pps)
  have ha : E[(#t[.sort (.succ q0), .sort (.succ q1), #0, #1] : Ctx ζ 2 0 4)] ⊢ #2 : #0 :=
    var_of_get hΓ ⟨2, by decide⟩ (by pps)
  have hb : E[(#t[.sort (.succ q0), .sort (.succ q1), #0, #1] : Ctx ζ 2 0 4)] ⊢ #3 : #1 :=
    var_of_get hΓ ⟨3, by decide⟩ (by pps)
  have h := mPrmk_typed (η := η) hp hα hβ ha hb
  exact Ctx.lam_congr (Γ := .nil) (Δ := #t[.sort (.succ q0), .sort (.succ q1), #0, #1]) hΓ h

/-- `Prod.rec`'s type (levels `u_1`, `u`, `v` = parameters 0, 1, 2). -/
def prRecTyM (η : Head ζ (.inductive ppSig)) : Expr ζ 3 0 :=
  .forallE (.sort (.succ r1)) (.forallE (.sort (.succ r2)) (.forallE (ppMotM η) (.forallE (ppMinM η)
    (.forallE (mPP η r1 r2 #0 #1) (.app #2 #4)))))

/-- What `Frontend.recrTerm` builds for `Prod.rec`. -/
def prRecTermM (η : Head ζ (.inductive ppSig)) : Expr ζ 3 0 :=
  .lam (.sort (.succ r1)) (.lam (.sort (.succ r2)) (.lam (ppMotM η) (.lam (ppMinM η)
    (.lam (mPP η r1 r2 #0 #1) (ppRecBody η)))))

set_option linter.unusedTactic false in
theorem recrTerm_eqPr (hp : (E.get η).block = prBlock) :
    Frontend.recrTerm (E.get η).block η 0 ![r1, r2] r0 (fun _ _ => [0, 1]) =
      .ok (prRecTermM η) := by
  rw [hp]
  have : (match Frontend.recrTerm (prBlock (ζ := ζ)) η 0 ![r1, r2] r0 (fun _ _ => [0, 1]) with
      | .ok t => t | .error _ => .prop) = prRecTermM η := by
    show Metalean.Expr.lam _ (Metalean.Expr.lam _ (Metalean.Expr.lam _ (Metalean.Expr.lam _
      (Metalean.Expr.lam _ (Metalean.Expr.recr _ _ _ _ _ _ _ _ _))))) = _
    simp only [prRecTermM, ppRecBody, ppMotM, ppMinM]
    repeat' (first
      | (funext t c; fin_cases t; fin_cases c <;> rfl)
      | (funext t; fin_cases t <;> rfl)
      | (funext i; exact i.elim0)
      | (pps; done)
      | rfl
      | congr 1)
  rw [← this]
  rfl

theorem prRecTermM_typed (hp : (E.get η).block = prBlock) :
    E[.nil] ⊢ prRecTermM η : prRecTyM η := by
  have h1 : E[(#t[.sort (.succ r1)] : Ctx ζ 3 0 1)] ⊢ ok := .snoc .nil ⟨_, .sortDF⟩
  have h2 : E[(#t[.sort (.succ r1), .sort (.succ r2)] : Ctx ζ 3 0 2)] ⊢ ok := .snoc h1 ⟨_, .sortDF⟩
  have hα2 : E[(#t[.sort (.succ r1), .sort (.succ r2)] : Ctx ζ 3 0 2)] ⊢ #0 : .sort (.succ r1) :=
    var_of_get h2 ⟨0, by decide⟩ (by pps)
  have hβ2 : E[(#t[.sort (.succ r1), .sort (.succ r2)] : Ctx ζ 3 0 2)] ⊢ #1 : .sort (.succ r2) :=
    var_of_get h2 ⟨1, by decide⟩ (by pps)
  have hP2 := mPr_typed hp (η := η) hα2 hβ2
  have hmot := Defeq.forallEDF (l₂ := (.succ r0)) hP2
    (.sortDF (Γ := (#t[.sort (.succ r1), .sort (.succ r2), mPP η r1 r2 #0 #1] : Ctx ζ 3 0 3)))
    .sortDF
  have h3 : E[(#t[.sort (.succ r1), .sort (.succ r2), ppMotM η] : Ctx ζ 3 0 3)] ⊢ ok :=
    .snoc h2 ⟨_, hmot⟩
  have h4 : E[(#t[.sort (.succ r1), .sort (.succ r2), ppMotM η, #0] : Ctx ζ 3 0 4)] ⊢ ok :=
    .snoc h3 ⟨_, var_of_get h3 ⟨0, by decide⟩ (by pps)⟩
  have h5 : E[(#t[.sort (.succ r1), .sort (.succ r2), ppMotM η, #0, #1] : Ctx ζ 3 0 5)] ⊢ ok :=
    .snoc h4 ⟨_, var_of_get h4 ⟨1, by decide⟩ (by pps)⟩
  have hmk5 : E[(#t[.sort (.succ r1), .sort (.succ r2), ppMotM η, #0, #1] : Ctx ζ 3 0 5)] ⊢
      .app #2 (mPPmk η r1 r2 #0 #1 #3 #4) : .sort r0 :=
    typed_of_eq (app_typed (var_of_get h5 ⟨2, by decide⟩ (by pps [ppMotM]))
      (mPrmk_typed hp (var_of_get h5 ⟨0, by decide⟩ (by pps)) (var_of_get h5 ⟨1, by decide⟩ (by pps))
        (var_of_get h5 ⟨3, by decide⟩ (by pps)) (var_of_get h5 ⟨4, by decide⟩ (by pps))))
      (by pps)
  have hmin : E[(#t[.sort (.succ r1), .sort (.succ r2), ppMotM η] : Ctx ζ 3 0 3)] ⊢ ppMinM η : _ :=
    .forallEDF (var_of_get h3 ⟨0, by decide⟩ (by pps))
      (.forallEDF (var_of_get h4 ⟨1, by decide⟩ (by pps)) hmk5 hmk5)
      (.forallEDF (var_of_get h4 ⟨1, by decide⟩ (by pps)) hmk5 hmk5)
  have h4' : E[(#t[.sort (.succ r1), .sort (.succ r2), ppMotM η, ppMinM η] : Ctx ζ 3 0 4)] ⊢ ok :=
    .snoc h3 ⟨_, hmin⟩
  have hΓ : E[(#t[.sort (.succ r1), .sort (.succ r2), ppMotM η, ppMinM η, mPP η r1 r2 #0 #1] :
      Ctx ζ 3 0 5)] ⊢ ok :=
    .snoc h4' ⟨_, mPr_typed hp (var_of_get h4' ⟨0, by decide⟩ (by pps))
      (var_of_get h4' ⟨1, by decide⟩ (by pps))⟩
  have hbody : E[(#t[.sort (.succ r1), .sort (.succ r2), ppMotM η, ppMinM η, mPP η r1 r2 #0 #1] :
      Ctx ζ 3 0 5)] ⊢ ppRecBody η : .app #2 #4 := by
    have h := Defeq.recrDF (E := E) (η := η) (s := 0) (ls := ![r1, r2]) (l := r0)
      (Γ := #t[.sort (.succ r1), .sort (.succ r2), ppMotM η, ppMinM η, mPP η r1 r2 #0 #1])
      (ps₁ := ![#0, #1]) (ps₂ := ![#0, #1]) (ms₁ := fun _ => #2) (ms₂ := fun _ => #2)
      (mins₁ := fun _ _ => #3) (mins₂ := fun _ _ => #3) (is₁ := Fin.elim0) (is₂ := Fin.elim0)
      (maj₁ := #4) (maj₂ := #4) (recAllowedPr hp)
      (prParams hp (var_of_get hΓ ⟨0, by decide⟩ (by pps))
        (var_of_get hΓ ⟨1, by decide⟩ (by pps))) ?_ ?_ (fun i => Fin.elim0 i) ?_ ?_
    · exact h
    · intro s; fin_cases s; rw [hp]; exact var_of_get hΓ ⟨2, by decide⟩ (by pps [ppMotM])
    · intro s c; fin_cases s; fin_cases c; rw [hp]
      exact var_of_get hΓ ⟨3, by decide⟩ (by pps [ppMinM])
    · exact typed_of_eq (var_of_get (T := mPP η r1 r2 #0 #1) hΓ ⟨4, by decide⟩ (by pps)) (by pps)
    · have hm : E[(#t[.sort (.succ r1), .sort (.succ r2), ppMotM η, ppMinM η, mPP η r1 r2 #0 #1] :
          Ctx ζ 3 0 5)] ⊢ #2 : .forallE (mPP η r1 r2 #0 #1) (.sort r0) :=
        var_of_get hΓ ⟨2, by decide⟩ (by pps [ppMotM])
      exact typed_of_eq (app_typed hm (var_of_get hΓ ⟨4, by decide⟩ (by pps))) (by pps)
  exact Ctx.lam_congr (Γ := .nil)
    (Δ := #t[.sort (.succ r1), .sort (.succ r2), ppMotM η, ppMinM η, mPP η r1 r2 #0 #1]) hΓ hbody

end PrTerms

/-! ## `Prod.fst`, `Prod.snd`: primitive projections as structure projections -/

section Proj
variable {ζ : Sigs} {E : Env ζ} {η : Head ζ (.inductive ppSig)}

/-- The binders `{α : Type u} {β : Type v} (self : Prod α β)` of the projections. -/
def ΓPr (η : Head ζ (.inductive ppSig)) : Ctx ζ 2 0 3 :=
  #t[.sort (.succ q0), .sort (.succ q1), mPP η q0 q1 #0 #1]

/-- `self.1` under `α β self`, as Metalean's structure projection computes it: the recursor of
`Prod` into `α` whose minor returns the first field. -/
def prFstM (η : Head ζ (.inductive ppSig)) : Expr ζ 2 3 :=
  .recr η 0 ![q0, q1] (.succ q0) ![#0, #1] (fun _ => .lam (mPP η q0 q1 #0 #1) #0)
    (fun _ _ => .lam #0 (.lam #1 #3)) Fin.elim0 #2

/-- `self.2` under `α β self`. -/
def prSndM (η : Head ζ (.inductive ppSig)) : Expr ζ 2 3 :=
  .recr η 0 ![q0, q1] (.succ q1) ![#0, #1] (fun _ => .lam (mPP η q0 q1 #0 #1) #1)
    (fun _ _ => .lam #0 (.lam #1 #4)) Fin.elim0 #2

/-- `Prod.fst`'s type `{α : Type u} → {β : Type v} → Prod α β → α`. -/
def prFstTyM (η : Head ζ (.inductive ppSig)) : Expr ζ 2 0 := (ΓPr η).pi #0
/-- `Prod.snd`'s type `{α : Type u} → {β : Type v} → Prod α β → β`. -/
def prSndTyM (η : Head ζ (.inductive ppSig)) : Expr ζ 2 0 := (ΓPr η).pi #1
/-- `fun α β self => self.1` -/
def prFstValM (η : Head ζ (.inductive ppSig)) : Expr ζ 2 0 := (ΓPr η).lam (prFstM η)
/-- `fun α β self => self.2` -/
def prSndValM (η : Head ζ (.inductive ppSig)) : Expr ζ 2 0 := (ΓPr η).lam (prSndM η)

/-- The parameter `β` among the parameters and the first field. -/
theorem append_one {α : Sort _} (u : Fin 2 → α) (v : Fin 1 → α) : Fin.append u v 1 = u 1 := rfl

theorem projTerm_eqPr0 {I : Inductive ζ ppSig} (h : I.IsStructure 0 0) (hI : I = prBlock) :
    h.projTerm η ![q0, q1] ![#0, #1] ⟨0, by decide⟩ (#2 : Expr ζ 2 3) = prFstM η := by
  subst hI
  rw [Inductive.IsStructure.projTerm_eq_recr]
  simp only [prFstM]
  congr 1
  case e_ms =>
    funext t; fin_cases t
    delta Inductive.IsStructure.projectionMotives
    rsx [Inductive.IsStructure.projTypeWith, Inductive.motiveTele, Inductive.indexTele, Ctx.substN]
  case e_mins =>
    funext t c; fin_cases t; fin_cases c
    delta Inductive.IsStructure.projectionCases
    rsx [Inductive.caseTele, CtorSig.caseOrdinary,
      CtorSig.fieldOrdinary, Ctor.fieldTele, Ctor.ordinaryFieldTele, Ctor.ordinaryTeleAux,
      Ctor.ihTele, Ctx.ofTypes, Ctor.recursiveFieldTeleAux, Expr.boundVars,
      Ctor.ordinaryFieldTeleAux, Tele.foldr, Ctx.substN, Subst.liftN]

theorem projTerm_eqPr1 {I : Inductive ζ ppSig} (h : I.IsStructure 0 0) (hI : I = prBlock) :
    h.projTerm η ![q0, q1] ![#0, #1] ⟨1, by decide⟩ (#2 : Expr ζ 2 3) = prSndM η := by
  subst hI
  rw [Inductive.IsStructure.projTerm_eq_recr]
  simp only [prSndM]
  congr 1
  case e_ms =>
    funext t; fin_cases t
    delta Inductive.IsStructure.projectionMotives
    rsx [Inductive.IsStructure.projTypeWith, Inductive.motiveTele, Inductive.indexTele, Ctx.substN,
      append_one]
  case e_mins =>
    funext t c; fin_cases t; fin_cases c
    delta Inductive.IsStructure.projectionCases
    rsx [Inductive.caseTele, CtorSig.caseOrdinary,
      CtorSig.fieldOrdinary, Ctor.fieldTele, Ctor.ordinaryFieldTele, Ctor.ordinaryTeleAux,
      Ctor.ihTele, Ctx.ofTypes, Ctor.recursiveFieldTeleAux, Expr.boundVars,
      Ctor.ordinaryFieldTeleAux, Tele.foldr, Ctx.substN, Subst.liftN]

theorem projType_eqPr0 {I : Inductive ζ ppSig} (h : I.IsStructure 0 0) (hI : I = prBlock) :
    h.projType η ![q0, q1] ![#0, #1] ⟨0, by decide⟩ (#2 : Expr ζ 2 3) = #0 := by
  subst hI
  rw [Inductive.IsStructure.projType, Inductive.IsStructure.projection]
  simp only [Inductive.IsStructure.projTypeWith]
  rsx

theorem projType_eqPr1 {I : Inductive ζ ppSig} (h : I.IsStructure 0 0) (hI : I = prBlock) :
    h.projType η ![q0, q1] ![#0, #1] ⟨1, by decide⟩ (#2 : Expr ζ 2 3) = #1 := by
  subst hI
  rw [Inductive.IsStructure.projType, Inductive.IsStructure.projection]
  simp only [Inductive.IsStructure.projTypeWith]
  rsx [append_one]

theorem ΓPr_wf (hp : (E.get η).block = prBlock) : E[ΓPr η] ⊢ ok := by
  have h1 : E[(#t[.sort (.succ q0)] : Ctx ζ 2 0 1)] ⊢ ok := .snoc .nil ⟨_, .sortDF⟩
  have h2 : E[(#t[.sort (.succ q0), .sort (.succ q1)] : Ctx ζ 2 0 2)] ⊢ ok := .snoc h1 ⟨_, .sortDF⟩
  exact .snoc h2 ⟨_, mPr_typed hp (var_of_get h2 ⟨0, by decide⟩ (by pps))
    (var_of_get h2 ⟨1, by decide⟩ (by pps))⟩

theorem self_typed (hp : (E.get η).block = prBlock) (hst : (E.get η).block.IsStructure 0 0) :
    E[ΓPr η] ⊢ #2 : .ind η 0 ![q0, q1] ![#0, #1] hst.indices := by
  rw [← hst.indices_eq Fin.elim0]
  exact var_of_get (ΓPr_wf hp) ⟨2, by decide⟩ (by pps [ΓPr])

theorem prParamsΓ (hp : (E.get η).block = prBlock) :
    ∀ p, E[ΓPr η] ⊢ (![#0, #1] : Fin 2 → Expr ζ 2 3) p :
      (E.get η).block.paramType ![q0, q1] ![#0, #1] p :=
  prParams hp (var_of_get (ΓPr_wf hp) ⟨0, by decide⟩ (by pps [ΓPr]))
    (var_of_get (ΓPr_wf hp) ⟨1, by decide⟩ (by pps [ΓPr]))

theorem prFstValM_typed (hE : EnvWF E) (hp : (E.get η).block = prBlock) :
    E[.nil] ⊢ prFstValM η : prFstTyM η := by
  have hst : (E.get η).block.IsStructure 0 0 := hp ▸ prStruct
  have h := hst.projTerm_hasType (hE.entryWF η).block ⟨0, by decide⟩ (ΓPr_wf hp) (prParamsΓ hp)
    (self_typed hp hst)
  rw [projTerm_eqPr0 hst hp, projType_eqPr0 hst hp] at h
  exact Ctx.lam_congr (Γ := .nil) (Δ := ΓPr η) (ΓPr_wf hp) h

theorem prSndValM_typed (hE : EnvWF E) (hp : (E.get η).block = prBlock) :
    E[.nil] ⊢ prSndValM η : prSndTyM η := by
  have hst : (E.get η).block.IsStructure 0 0 := hp ▸ prStruct
  have h := hst.projTerm_hasType (hE.entryWF η).block ⟨1, by decide⟩ (ΓPr_wf hp) (prParamsΓ hp)
    (self_typed hp hst)
  rw [projTerm_eqPr1 hst hp, projType_eqPr1 hst hp] at h
  exact Ctx.lam_congr (Γ := .nil) (Δ := ΓPr η) (ΓPr_wf hp) h

end Proj

end EraseProof.Test.NVQP
