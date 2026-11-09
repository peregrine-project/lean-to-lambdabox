import EraseProof.Test.NVSData
import EraseProof.Test.NVRModel
import Metalean.Metatheory.SubjectReduction
import Metalean.Typing.Structure

/-!
# NV-S: the Metalean blocks of `PUnit` and `PProd`

The Metalean blocks of `Init`'s `PUnit.{u} : Sort u` (`puBlock`: one field-less constructor, at the
level of its universe parameter, a subsingleton) and `PProd.{u, v} (α : Sort u) (β : Sort v) :
Sort (max (max 1 u) v)` (`ppBlock`: two parameters, one constructor with the two ordinary fields
`fst : α` and `snd : β`, a structure), the typing of their terms in any environment whose heads
hold them, and the η-terms the translator builds for their constants (`Frontend.indTerm`,
`ctorTerm`, `recrTerm`), typed at the translations of the constants' Lean types. For
`Test/NVSModel.lean`.
-/

open Lean Metalean

namespace EraseProof.Test.NVS

open EraseProof.Test.NV1 (bCtorSig typed_of_eq var_of_get app_typed fin0_eq)

/-! ## `PUnit` -/

abbrev puSig : IndSig :=
  { nlevels := 1, nparams := 0, nsorts := 1, nindices _ := 0, nctors _ := 1,
    ctors _ _ := bCtorSig }

/-- `PUnit.{u} : Sort u` as a Metalean block. -/
@[reducible] def puBlock {ζ : Sigs} : Inductive ζ puSig where
  params := .nil
  indices _ := .nil
  level := .param 0
  ctors _ _ := { ordinary := fun f => Fin.elim0 f, recursive := fun f => Fin.elim0 f,
                 targetIndices := fun i => Fin.elim0 i }

@[simp] theorem puBlock_map {ζ₁ ζ₂ : Sigs} (pre : ζ₁ ⟶ ζ₂) :
    (@puBlock ζ₁).map pre = @puBlock ζ₂ := by
  dsimp [Inductive.map]
  congr
  funext s c
  dsimp [Ctor.map]
  congr <;> funext i <;> exact Fin.elim0 i

theorem puBlock_wf {ζ : Sigs} (E : Env ζ) : InductiveWF E puBlock :=
  ⟨.nil, fun _ => .nil, fun _ _ =>
    { ordinary := fun f => Fin.elim0 f, recursive := fun f => Fin.elim0 f,
      targetIndices := fun i => Fin.elim0 i }⟩

theorem puBlock_subsingleton {ζ : Sigs} : (puBlock (ζ := ζ)).Subsingleton :=
  ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ _ =>
    ⟨fun f => Fin.elim0 f, fun f => Fin.elim0 f⟩⟩

theorem largeElimPU {ζ : Sigs} : LeanLargeElim (puBlock (ζ := ζ)) :=
  Or.inr ⟨rfl, fun _ _ _ => Subsingleton.elim _ _,
    fun _ _ => ⟨fun f => Fin.elim0 f, fun f => Fin.elim0 f⟩⟩

section PUnit
variable {ζ : Sigs} {E : Env ζ} {η : Head ζ (.inductive puSig)} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n}

/-- `PUnit.{l}`, `PUnit.unit.{l}`. -/
def mPU (η : Head ζ (.inductive puSig)) (l : Level ℓ) : Expr ζ ℓ n :=
  .ind η 0 ![l] Fin.elim0 Fin.elim0
def mPUu (η : Head ζ (.inductive puSig)) (l : Level ℓ) : Expr ζ ℓ n :=
  .ctor η 0 0 ![l] Fin.elim0 Fin.elim0 Fin.elim0

theorem recAllowedPU (hp : (E.get η).block = puBlock) {ls : Fin 1 → Level ℓ} {l : Level ℓ} :
    (E.get η).block.RecAllowed ls l := by
  rw [hp]; exact .inl puBlock_subsingleton

theorem indPU_typed (hp : (E.get η).block = puBlock) {ls : Fin 1 → Level ℓ}
    {ps : Fin 0 → Expr ζ ℓ n} {is : Fin 0 → Expr ζ ℓ n} :
    E[Γ] ⊢ .ind η 0 ls ps is : .sort (ls 0) := by
  have h := Defeq.indDF (E := E) (Γ := Γ) (η := η) (s := 0) (ls := ls) (ps₁ := ps) (ps₂ := ps)
    (is₁ := is) (is₂ := is) (fun p => Fin.elim0 p) (fun i => Fin.elim0 i)
  rw [hp] at h
  simpa using h

theorem mPU_typed (hp : (E.get η).block = puBlock) {l : Level ℓ} :
    E[Γ] ⊢ mPU η l : .sort l :=
  indPU_typed hp

theorem mPUu_typed (_hp : (E.get η).block = puBlock) {l : Level ℓ} :
    E[Γ] ⊢ mPUu η l : mPU η l := by
  have h := Defeq.ctorDF (E := E) (Γ := Γ) (η := η) (s := 0) (c := 0) (ls := ![l])
    (ps₁ := Fin.elim0) (ps₂ := Fin.elim0) (fds₁ := Fin.elim0) (fds₂ := Fin.elim0)
    (recFds₁ := Fin.elim0) (recFds₂ := Fin.elim0)
    (fieldLevels := fun f => Fin.elim0 f) (recFieldLevels := fun f => Fin.elim0 f)
    (fun p => Fin.elim0 p) (fun f => Fin.elim0 f) (fun f => Fin.elim0 f) (fun f => Fin.elim0 f)
    (fun f => Fin.elim0 f) (Defeq.indDF (fun p => Fin.elim0 p) (fun i => Fin.elim0 i))
  unfold mPUu mPU
  convert h using 2

end PUnit

/-! ## `PProd` -/

abbrev ppCtorSig : CtorSig 1 :=
  { nfields := 2, nrecFields := 0, recursiveArity := ![], recursiveTarget := ![] }
abbrev ppSig : IndSig :=
  { nlevels := 2, nparams := 2, nsorts := 1, nindices _ := 0, nctors _ := 1,
    ctors _ _ := ppCtorSig }

/-- The sort `max (max 1 u) v` of `PProd.{u, v}`. -/
abbrev ppLevel {ℓ : Nat} (u v : Level ℓ) : Level ℓ := .max (.max (.succ .zero) u) v

/-- `PProd.{u, v} (α : Sort u) (β : Sort v) : Sort (max (max 1 u) v)` with the fields `fst : α`,
`snd : β`, as a Metalean block. -/
@[reducible] def ppBlock {ζ : Sigs} : Inductive ζ ppSig where
  params := #t[.sort (.param 0), .sort (.param 1)]
  indices _ := .nil
  level := ppLevel (.param 0) (.param 1)
  ctors _ _ := {
    ordinary
      | ⟨0, _⟩ => ⟨.var ⟨0, by simp⟩, .param 0⟩
      | ⟨1, _⟩ => ⟨.var ⟨1, by simp⟩, .param 1⟩
    recursive f := Fin.elim0 f
    targetIndices i := Fin.elim0 i }

@[simp] theorem ppBlock_map {ζ₁ ζ₂ : Sigs} (pre : ζ₁ ⟶ ζ₂) :
    (@ppBlock ζ₁).map pre = @ppBlock ζ₂ := by
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

theorem ppLevel_ge {ℓ : Nat} {u v : Level ℓ} : Metalean.Level.one ≤ ppLevel u v :=
  fun ν => by simp

theorem ppBlock_wf {ζ : Sigs} (E : Env ζ) : InductiveWF E ppBlock :=
  ⟨.snoc (.snoc .nil ⟨_, trivial, .sortDF⟩) ⟨_, trivial, .sortDF⟩,
    fun _ => .nil,
    fun _ _ => {
      ordinary
        | ⟨0, _⟩ => ⟨.var .sortDF, fun ν => by simp [Nat.imax]⟩
        | ⟨1, _⟩ => ⟨.var .sortDF, fun ν => by simp [Nat.imax]⟩
      recursive f := Fin.elim0 f
      targetIndices i := Fin.elim0 i
    }⟩

theorem largeElimPP {ζ : Sigs} : LeanLargeElim (ppBlock (ζ := ζ)) := Or.inl (ppLevel_ge (u := .param 0) (v := .param 1))

/-- `PProd` is a structure: its constructor `PProd.mk` is the only one, without indices or recursive
fields, and it eliminates into every sort. -/
theorem ppStruct {ζ : Sigs} : (ppBlock (ζ := ζ)).IsStructure 0 0 where
  sort_unique _ := Subsingleton.elim _ _
  ctor_unique _ := Subsingleton.elim _ _
  no_indices := ⟨fun i => Fin.elim0 i⟩
  no_recursive := ⟨fun i => Fin.elim0 i⟩
  largeElim := Or.inr (ppLevel_ge (u := .param 0) (v := .param 1))

section PProd
variable {ζ : Sigs} {E : Env ζ} {η : Head ζ (.inductive ppSig)} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n}

/-- `PProd.{u, v} α β`. -/
def mPP (η : Head ζ (.inductive ppSig)) (u v : Level ℓ) (α β : Expr ζ ℓ n) : Expr ζ ℓ n :=
  .ind η 0 ![u, v] ![α, β] Fin.elim0
/-- `PProd.mk.{u, v} α β a b`. -/
def mPPmk (η : Head ζ (.inductive ppSig)) (u v : Level ℓ) (α β a b : Expr ζ ℓ n) : Expr ζ ℓ n :=
  .ctor η 0 0 ![u, v] ![α, β] ![a, b] Fin.elim0

theorem recAllowedPP (hp : (E.get η).block = ppBlock) {ls : Fin 2 → Level ℓ} {l : Level ℓ} :
    (E.get η).block.RecAllowed ls l := by
  rw [hp]; exact largeElimPP.toLargeElim.recAllowed ls l

theorem ppParams (hp : (E.get η).block = ppBlock) {u v : Level ℓ} {α₁ α₂ β₁ β₂ : Expr ζ ℓ n}
    (hα : E[Γ] ⊢ α₁ ≡ α₂ : .sort u) (hβ : E[Γ] ⊢ β₁ ≡ β₂ : .sort v) :
    ∀ p, E[Γ] ⊢ (![α₁, β₁] : Fin 2 → Expr ζ ℓ n) p ≡ (![α₂, β₂] : Fin 2 → Expr ζ ℓ n) p :
      (E.get η).block.paramType ![u, v] ![α₁, β₁] p := by
  intro p; fin_cases p <;> rw [hp]
  · simpa [Inductive.paramType, Ctx.entry] using hα
  · simpa [Inductive.paramType, Ctx.entry] using hβ

theorem mPP_defeq (hp : (E.get η).block = ppBlock) {u v : Level ℓ} {α₁ α₂ β₁ β₂ : Expr ζ ℓ n}
    (hα : E[Γ] ⊢ α₁ ≡ α₂ : .sort u) (hβ : E[Γ] ⊢ β₁ ≡ β₂ : .sort v) :
    E[Γ] ⊢ mPP η u v α₁ β₁ ≡ mPP η u v α₂ β₂ : .sort (ppLevel u v) := by
  have h := Defeq.indDF (E := E) (Γ := Γ) (η := η) (s := 0) (ls := ![u, v]) (ps₁ := ![α₁, β₁])
    (ps₂ := ![α₂, β₂]) (is₁ := Fin.elim0) (is₂ := Fin.elim0) (ppParams hp hα hβ)
    (fun i => Fin.elim0 i)
  rw [hp] at h
  simpa [mPP] using h

theorem mPP_typed (hp : (E.get η).block = ppBlock) {u v : Level ℓ} {α β : Expr ζ ℓ n}
    (hα : E[Γ] ⊢ α : .sort u) (hβ : E[Γ] ⊢ β : .sort v) :
    E[Γ] ⊢ mPP η u v α β : .sort (ppLevel u v) :=
  mPP_defeq hp hα hβ

theorem mPPmk_typed (hp : (E.get η).block = ppBlock) {u v : Level ℓ} {α β a b : Expr ζ ℓ n}
    (hα : E[Γ] ⊢ α : .sort u) (hβ : E[Γ] ⊢ β : .sort v) (ha : E[Γ] ⊢ a : α)
    (hb : E[Γ] ⊢ b : β) :
    E[Γ] ⊢ mPPmk η u v α β a b : mPP η u v α β := by
  have h := Defeq.ctorDF (E := E) (Γ := Γ) (η := η) (s := 0) (c := 0) (ls := ![u, v])
    (ps₁ := ![α, β]) (ps₂ := ![α, β]) (fds₁ := ![a, b]) (fds₂ := ![a, b])
    (recFds₁ := Fin.elim0) (recFds₂ := Fin.elim0)
    (fieldLevels := ![u, v]) (recFieldLevels := fun f => Fin.elim0 f)
    (ppParams hp hα hβ)
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
      have := mPP_typed hp hα hβ
      rw [hp]
      convert this using 2
      · simp only [mPP]; congr 1; funext i; exact i.elim0
      · simp only [mPP]; congr 1; funext i; exact i.elim0
      · simp)
  unfold mPPmk mPP
  convert h using 2

end PProd

/-- Unfold Metalean's telescopes, recursor types and weakenings on `PUnit`'s and `PProd`'s terms;
close equalities of small `Fin` functions. -/
syntax (name := _pps) "pps" ("[" ident,* "]")? : tactic
macro_rules
  | `(tactic| pps) => `(tactic| pps [Ctx.get])
  | `(tactic| pps [$ts,*]) => `(tactic| (nvsimp [$[$ts:ident],*, mPU, mPUu, mPP, mPPmk,
      Inductive.paramType, Inductive.indexType, Ctx.proj, Ctx.entry, Ctor.targetIndex,
      Fin.fun_vecCons, Fin.fun_vecEmpty, Expr.wkN, funext_iff, Fin.forall_fin_two,
      Fin.forall_fin_one, Fin.sum_succ, Fin.sum_zero, Level.inst_param, Subst.liftN, Ren.wkFrom,
      Fin.castLE, ML.Expr.apps_succ, CtorSig.fieldParams, Ctor.ordinaryFieldExpr,
      Expr.boundVars, Ctor.fieldTele, Ctor.ordinaryFieldTele, Expr.subst, Expr.instL, Ctx.instL,
      CtorSig.fieldOrdinary, Ctor.ordinaryTeleAux, Ren.comp] <;> finCongr))

/-! ## `PUnit.rec`'s η-term (levels `u_1` = parameter 0, `u` = parameter 1) -/

section PURec
variable {ζ : Sigs} {E : Env ζ} {η : Head ζ (.inductive puSig)}

abbrev q0 : Level 2 := .param 0
abbrev q1 : Level 2 := .param 1

/-- `PUnit.rec`'s type `{motive : PUnit → Sort u_1} → motive PUnit.unit → (t : PUnit) → motive t`. -/
def puRecTyM (η : Head ζ (.inductive puSig)) : Expr ζ 2 0 :=
  .forallE (.forallE (mPU η q1) (.sort q0)) (.forallE (.app #0 (mPUu η q1))
    (.forallE (mPU η q1) (.app #0 #2)))

/-- What `Frontend.recrTerm` builds for `PUnit.rec`. -/
def puRecTermM (η : Head ζ (.inductive puSig)) : Expr ζ 2 0 :=
  .lam (.forallE (mPU η q1) (.sort q0)) (.lam (.app #0 (mPUu η q1)) (.lam (mPU η q1)
    (.recr η 0 ![q1] q0 Fin.elim0 (fun _ => #0) (fun _ _ => #1) Fin.elim0 #2)))

set_option linter.unusedTactic false in
theorem recrTerm_eqPU (hp : (E.get η).block = puBlock) :
    Frontend.recrTerm (E.get η).block η 0 ![q1] q0 (fun _ _ => []) = .ok (puRecTermM η) := by
  rw [hp]
  have : (match Frontend.recrTerm (puBlock (ζ := ζ)) η 0 ![q1] q0 (fun _ _ => []) with
      | .ok t => t | .error _ => .prop) = puRecTermM η := by
    show Metalean.Expr.lam _ (Metalean.Expr.lam _ (Metalean.Expr.lam _
      (Metalean.Expr.recr _ _ _ _ _ _ _ _ _))) = _
    simp only [puRecTermM]
    repeat' (first
      | (funext t c; fin_cases t; fin_cases c <;> rfl)
      | (funext t; fin_cases t; rfl)
      | (funext i; exact i.elim0)
      | (pps; done)
      | rfl
      | congr 1)
  rw [← this]
  rfl

theorem puRecTermM_typed (hp : (E.get η).block = puBlock) :
    E[.nil] ⊢ puRecTermM η : puRecTyM η := by
  have h1 : E[(#t[.forallE (mPU η q1) (.sort q0)] : Ctx ζ 2 0 1)] ⊢ ok :=
    .snoc .nil ⟨_, .forallEDF (mPU_typed hp) .sortDF .sortDF⟩
  have hv1 : E[(#t[.forallE (mPU η q1) (.sort q0)] : Ctx ζ 2 0 1)] ⊢ #0 :
      .forallE (mPU η q1) (.sort q0) := var_of_get h1 ⟨0, by decide⟩ (by pps)
  have hm1 : E[(#t[.forallE (mPU η q1) (.sort q0)] : Ctx ζ 2 0 1)] ⊢ .app #0 (mPUu η q1) :
      .sort q0 :=
    .appDF (mPU_typed hp) .sortDF hv1 (mPUu_typed hp) .sortDF
  have h2 : E[(#t[.forallE (mPU η q1) (.sort q0), .app #0 (mPUu η q1)] : Ctx ζ 2 0 2)] ⊢ ok :=
    .snoc h1 ⟨_, hm1⟩
  have hΓ : E[(#t[.forallE (mPU η q1) (.sort q0), .app #0 (mPUu η q1), mPU η q1] :
      Ctx ζ 2 0 3)] ⊢ ok := .snoc h2 ⟨_, mPU_typed hp⟩
  have hbody : E[(#t[.forallE (mPU η q1) (.sort q0), .app #0 (mPUu η q1), mPU η q1] :
      Ctx ζ 2 0 3)] ⊢ .recr η 0 ![q1] q0 Fin.elim0 (fun _ => #0) (fun _ _ => #1) Fin.elim0 #2 :
        .app #0 #2 := by
    have h := Defeq.recrDF (E := E) (η := η) (s := 0) (ls := ![q1]) (l := q0)
      (Γ := #t[.forallE (mPU η q1) (.sort q0), .app #0 (mPUu η q1), mPU η q1])
      (ps₁ := Fin.elim0) (ps₂ := Fin.elim0) (ms₁ := fun _ => #0) (ms₂ := fun _ => #0)
      (mins₁ := fun _ _ => #1) (mins₂ := fun _ _ => #1) (is₁ := Fin.elim0) (is₂ := Fin.elim0)
      (maj₁ := #2) (maj₂ := #2) (recAllowedPU hp) (fun p => Fin.elim0 p) ?_ ?_
      (fun i => Fin.elim0 i) ?_ ?_
    · exact h
    · intro s; fin_cases s; rw [hp]; exact var_of_get hΓ ⟨0, by decide⟩ (by pps)
    · intro s c; fin_cases s; fin_cases c; rw [hp]; exact var_of_get hΓ ⟨1, by decide⟩ (by pps)
    · exact var_of_get hΓ ⟨2, by decide⟩ (by pps)
    · have hv : E[(#t[.forallE (mPU η q1) (.sort q0), .app #0 (mPUu η q1), mPU η q1] :
          Ctx ζ 2 0 3)] ⊢ #0 : .forallE (mPU η q1) (.sort q0) :=
        var_of_get hΓ ⟨0, by decide⟩ (by pps)
      have hv2 : E[(#t[.forallE (mPU η q1) (.sort q0), .app #0 (mPUu η q1), mPU η q1] :
          Ctx ζ 2 0 3)] ⊢ #2 : mPU η q1 := var_of_get hΓ ⟨2, by decide⟩ (by pps)
      exact .appDF (mPU_typed hp) .sortDF hv hv2 .sortDF
  exact Ctx.lam_congr (Γ := .nil)
    (Δ := #t[.forallE (mPU η q1) (.sort q0), .app #0 (mPUu η q1), mPU η q1]) hΓ hbody

end PURec

/-! ## `PProd`'s, `PProd.mk`'s and `PProd.rec`'s η-terms -/

section PPTerms
variable {ζ : Sigs} {E : Env ζ} {η : Head ζ (.inductive ppSig)}

/-- `PProd`'s type `Sort u → Sort v → Sort (max (max 1 u) v)` (levels `u`, `v` = parameters 0, 1). -/
def ppTyM : Expr ζ 2 0 := .forallE (.sort q0) (.forallE (.sort q1) (.sort (ppLevel q0 q1)))

/-- `PProd`'s η-term `fun α β => PProd α β`. -/
def ppTermM (η : Head ζ (.inductive ppSig)) : Expr ζ 2 0 :=
  .lam (.sort q0) (.lam (.sort q1) (mPP η q0 q1 #0 #1))

/-- `PProd.mk`'s type `{α : Sort u} → {β : Sort v} → α → β → PProd α β`. -/
def ppMkTyM (η : Head ζ (.inductive ppSig)) : Expr ζ 2 0 :=
  .forallE (.sort q0) (.forallE (.sort q1) (.forallE #0 (.forallE #1 (mPP η q0 q1 #0 #1))))

/-- `PProd.mk`'s η-term. -/
def ppMkTermM (η : Head ζ (.inductive ppSig)) : Expr ζ 2 0 :=
  .lam (.sort q0) (.lam (.sort q1) (.lam #0 (.lam #1 (mPPmk η q0 q1 #0 #1 #2 #3))))

theorem indTerm_eqPP (hp : (E.get η).block = ppBlock) :
    Frontend.indTerm (E.get η).block η 0 ![q0, q1] = ppTermM η := by
  rw [hp]
  show Metalean.Expr.lam _ (Metalean.Expr.lam _ _) = _
  simp only [ppTermM]
  pps [Inductive.argTele]

theorem ctorTerm_eqPP (hp : (E.get η).block = ppBlock) :
    Frontend.ctorTerm (E.get η).block η 0 0 ![q0, q1] [0, 1] = .ok (ppMkTermM η) := by
  rw [hp]
  have : (match Frontend.ctorTerm (ppBlock (ζ := ζ)) η 0 0 ![q0, q1] [0, 1] with
      | .ok t => t | .error _ => .prop) = ppMkTermM η := by
    show Metalean.Expr.lam _ (Metalean.Expr.lam _ (Metalean.Expr.lam _ (Metalean.Expr.lam _ _))) = _
    simp only [ppMkTermM]
    pps
  rw [← this]
  rfl

theorem ppTermM_typed (hp : (E.get η).block = ppBlock) : E[.nil] ⊢ ppTermM η : ppTyM := by
  have h1 : E[(#t[.sort q0] : Ctx ζ 2 0 1)] ⊢ ok := .snoc .nil ⟨_, .sortDF⟩
  have hΓ : E[(#t[.sort q0, .sort q1] : Ctx ζ 2 0 2)] ⊢ ok := .snoc h1 ⟨_, .sortDF⟩
  have hα : E[(#t[.sort q0, .sort q1] : Ctx ζ 2 0 2)] ⊢ #0 : .sort q0 :=
    var_of_get hΓ ⟨0, by decide⟩ (by pps)
  have hβ : E[(#t[.sort q0, .sort q1] : Ctx ζ 2 0 2)] ⊢ #1 : .sort q1 :=
    var_of_get hΓ ⟨1, by decide⟩ (by pps)
  have h := mPP_typed (η := η) hp hα hβ
  exact Ctx.lam_congr (Γ := .nil) (Δ := #t[.sort q0, .sort q1]) hΓ h

theorem ppMkTermM_typed (hp : (E.get η).block = ppBlock) :
    E[.nil] ⊢ ppMkTermM η : ppMkTyM η := by
  have h1 : E[(#t[.sort q0] : Ctx ζ 2 0 1)] ⊢ ok := .snoc .nil ⟨_, .sortDF⟩
  have h2 : E[(#t[.sort q0, .sort q1] : Ctx ζ 2 0 2)] ⊢ ok := .snoc h1 ⟨_, .sortDF⟩
  have h3 : E[(#t[.sort q0, .sort q1, #0] : Ctx ζ 2 0 3)] ⊢ ok :=
    .snoc h2 ⟨_, var_of_get h2 ⟨0, by decide⟩ (by pps)⟩
  have hΓ : E[(#t[.sort q0, .sort q1, #0, #1] : Ctx ζ 2 0 4)] ⊢ ok :=
    .snoc h3 ⟨_, var_of_get h3 ⟨1, by decide⟩ (by pps)⟩
  have hα : E[(#t[.sort q0, .sort q1, #0, #1] : Ctx ζ 2 0 4)] ⊢ #0 : .sort q0 :=
    var_of_get hΓ ⟨0, by decide⟩ (by pps)
  have hβ : E[(#t[.sort q0, .sort q1, #0, #1] : Ctx ζ 2 0 4)] ⊢ #1 : .sort q1 :=
    var_of_get hΓ ⟨1, by decide⟩ (by pps)
  have ha : E[(#t[.sort q0, .sort q1, #0, #1] : Ctx ζ 2 0 4)] ⊢ #2 : #0 :=
    var_of_get hΓ ⟨2, by decide⟩ (by pps)
  have hb : E[(#t[.sort q0, .sort q1, #0, #1] : Ctx ζ 2 0 4)] ⊢ #3 : #1 :=
    var_of_get hΓ ⟨3, by decide⟩ (by pps)
  have h := mPPmk_typed (η := η) hp hα hβ ha hb
  exact Ctx.lam_congr (Γ := .nil) (Δ := #t[.sort q0, .sort q1, #0, #1]) hΓ h

abbrev r0 : Level 3 := .param 0
abbrev r1 : Level 3 := .param 1
abbrev r2 : Level 3 := .param 2

/-- `(t : PProd α β) → Sort u_1`, under `α β`. -/
def ppMotM (η : Head ζ (.inductive ppSig)) : Expr ζ 3 2 :=
  .forallE (mPP η r1 r2 #0 #1) (.sort r0)

/-- `(fst : α) → (snd : β) → motive ⟨fst, snd⟩`, under `α β motive`. -/
def ppMinM (η : Head ζ (.inductive ppSig)) : Expr ζ 3 3 :=
  .forallE #0 (.forallE #1 (.app #2 (mPPmk η r1 r2 #0 #1 #3 #4)))

/-- `PProd.rec`'s type. -/
def ppRecTyM (η : Head ζ (.inductive ppSig)) : Expr ζ 3 0 :=
  .forallE (.sort r1) (.forallE (.sort r2) (.forallE (ppMotM η) (.forallE (ppMinM η)
    (.forallE (mPP η r1 r2 #0 #1) (.app #2 #4)))))

/-- The body of `PProd.rec`'s η-term. -/
def ppRecBody (η : Head ζ (.inductive ppSig)) : Expr ζ 3 5 :=
  .recr η 0 ![r1, r2] r0 ![#0, #1] (fun _ => #2) (fun _ _ => #3) Fin.elim0 #4

/-- What `Frontend.recrTerm` builds for `PProd.rec`. -/
def ppRecTermM (η : Head ζ (.inductive ppSig)) : Expr ζ 3 0 :=
  .lam (.sort r1) (.lam (.sort r2) (.lam (ppMotM η) (.lam (ppMinM η)
    (.lam (mPP η r1 r2 #0 #1) (ppRecBody η)))))

set_option linter.unusedTactic false in
theorem recrTerm_eqPP (hp : (E.get η).block = ppBlock) :
    Frontend.recrTerm (E.get η).block η 0 ![r1, r2] r0 (fun _ _ => [0, 1]) =
      .ok (ppRecTermM η) := by
  rw [hp]
  have : (match Frontend.recrTerm (ppBlock (ζ := ζ)) η 0 ![r1, r2] r0 (fun _ _ => [0, 1]) with
      | .ok t => t | .error _ => .prop) = ppRecTermM η := by
    show Metalean.Expr.lam _ (Metalean.Expr.lam _ (Metalean.Expr.lam _ (Metalean.Expr.lam _
      (Metalean.Expr.lam _ (Metalean.Expr.recr _ _ _ _ _ _ _ _ _))))) = _
    simp only [ppRecTermM, ppRecBody, ppMotM, ppMinM]
    repeat' (first
      | (funext t c; fin_cases t; fin_cases c <;> rfl)
      | (funext t; fin_cases t <;> rfl)
      | (funext i; exact i.elim0)
      | (pps; done)
      | rfl
      | congr 1)
  rw [← this]
  rfl

theorem ppRecTermM_typed (hp : (E.get η).block = ppBlock) :
    E[.nil] ⊢ ppRecTermM η : ppRecTyM η := by
  have h1 : E[(#t[.sort r1] : Ctx ζ 3 0 1)] ⊢ ok := .snoc .nil ⟨_, .sortDF⟩
  have h2 : E[(#t[.sort r1, .sort r2] : Ctx ζ 3 0 2)] ⊢ ok := .snoc h1 ⟨_, .sortDF⟩
  have hα2 : E[(#t[.sort r1, .sort r2] : Ctx ζ 3 0 2)] ⊢ #0 : .sort r1 :=
    var_of_get h2 ⟨0, by decide⟩ (by pps)
  have hβ2 : E[(#t[.sort r1, .sort r2] : Ctx ζ 3 0 2)] ⊢ #1 : .sort r2 :=
    var_of_get h2 ⟨1, by decide⟩ (by pps)
  have hP2 := mPP_typed hp (η := η) hα2 hβ2
  have h2t : E[(#t[.sort r1, .sort r2, mPP η r1 r2 #0 #1] : Ctx ζ 3 0 3)] ⊢ ok :=
    .snoc h2 ⟨_, hP2⟩
  have hmot := Defeq.forallEDF (l₂ := (.succ r0)) hP2 (.sortDF (Γ := (#t[.sort r1, .sort r2, mPP η r1 r2 #0 #1] : Ctx ζ 3 0 3)))
    .sortDF
  have h3 : E[(#t[.sort r1, .sort r2, ppMotM η] : Ctx ζ 3 0 3)] ⊢ ok := .snoc h2 ⟨_, hmot⟩
  have h4 : E[(#t[.sort r1, .sort r2, ppMotM η, #0] : Ctx ζ 3 0 4)] ⊢ ok :=
    .snoc h3 ⟨_, var_of_get h3 ⟨0, by decide⟩ (by pps)⟩
  have h5 : E[(#t[.sort r1, .sort r2, ppMotM η, #0, #1] : Ctx ζ 3 0 5)] ⊢ ok :=
    .snoc h4 ⟨_, var_of_get h4 ⟨1, by decide⟩ (by pps)⟩
  have hmk5 : E[(#t[.sort r1, .sort r2, ppMotM η, #0, #1] : Ctx ζ 3 0 5)] ⊢
      .app #2 (mPPmk η r1 r2 #0 #1 #3 #4) : .sort r0 :=
    typed_of_eq (app_typed (var_of_get h5 ⟨2, by decide⟩ (by pps [ppMotM]))
      (mPPmk_typed hp (var_of_get h5 ⟨0, by decide⟩ (by pps)) (var_of_get h5 ⟨1, by decide⟩ (by pps))
        (var_of_get h5 ⟨3, by decide⟩ (by pps)) (var_of_get h5 ⟨4, by decide⟩ (by pps))))
      (by pps)
  have hmin : E[(#t[.sort r1, .sort r2, ppMotM η] : Ctx ζ 3 0 3)] ⊢ ppMinM η : _ :=
    .forallEDF (var_of_get h3 ⟨0, by decide⟩ (by pps))
      (.forallEDF (var_of_get h4 ⟨1, by decide⟩ (by pps)) hmk5 hmk5)
      (.forallEDF (var_of_get h4 ⟨1, by decide⟩ (by pps)) hmk5 hmk5)
  have h4' : E[(#t[.sort r1, .sort r2, ppMotM η, ppMinM η] : Ctx ζ 3 0 4)] ⊢ ok :=
    .snoc h3 ⟨_, hmin⟩
  have hΓ : E[(#t[.sort r1, .sort r2, ppMotM η, ppMinM η, mPP η r1 r2 #0 #1] : Ctx ζ 3 0 5)] ⊢
      ok :=
    .snoc h4' ⟨_, mPP_typed hp (var_of_get h4' ⟨0, by decide⟩ (by pps))
      (var_of_get h4' ⟨1, by decide⟩ (by pps))⟩
  have hbody : E[(#t[.sort r1, .sort r2, ppMotM η, ppMinM η, mPP η r1 r2 #0 #1] :
      Ctx ζ 3 0 5)] ⊢ ppRecBody η : .app #2 #4 := by
    have h := Defeq.recrDF (E := E) (η := η) (s := 0) (ls := ![r1, r2]) (l := r0)
      (Γ := #t[.sort r1, .sort r2, ppMotM η, ppMinM η, mPP η r1 r2 #0 #1])
      (ps₁ := ![#0, #1]) (ps₂ := ![#0, #1]) (ms₁ := fun _ => #2) (ms₂ := fun _ => #2)
      (mins₁ := fun _ _ => #3) (mins₂ := fun _ _ => #3) (is₁ := Fin.elim0) (is₂ := Fin.elim0)
      (maj₁ := #4) (maj₂ := #4) (recAllowedPP hp)
      (ppParams hp (var_of_get hΓ ⟨0, by decide⟩ (by pps))
        (var_of_get hΓ ⟨1, by decide⟩ (by pps))) ?_ ?_ (fun i => Fin.elim0 i) ?_ ?_
    · exact h
    · intro s; fin_cases s; rw [hp]; exact var_of_get hΓ ⟨2, by decide⟩ (by pps [ppMotM])
    · intro s c; fin_cases s; fin_cases c; rw [hp]
      exact var_of_get hΓ ⟨3, by decide⟩ (by pps [ppMinM])
    · exact typed_of_eq (var_of_get (T := mPP η r1 r2 #0 #1) hΓ ⟨4, by decide⟩ (by pps)) (by pps)
    · have hm : E[(#t[.sort r1, .sort r2, ppMotM η, ppMinM η, mPP η r1 r2 #0 #1] :
          Ctx ζ 3 0 5)] ⊢ #2 : .forallE (mPP η r1 r2 #0 #1) (.sort r0) :=
        var_of_get hΓ ⟨2, by decide⟩ (by pps [ppMotM])
      exact typed_of_eq (app_typed hm (var_of_get hΓ ⟨4, by decide⟩ (by pps))) (by pps)
  exact Ctx.lam_congr (Γ := .nil)
    (Δ := #t[.sort r1, .sort r2, ppMotM η, ppMinM η, mPP η r1 r2 #0 #1]) hΓ hbody

end PPTerms

end EraseProof.Test.NVS
