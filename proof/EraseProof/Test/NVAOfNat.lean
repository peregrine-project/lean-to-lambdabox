import EraseProof.Test.NVAFuns

/-!
# NV-A: the Metalean block of `OfNat`, `OfNat.ofNat` and `instOfNatNat`

The Metalean block of `Init`'s `class OfNat (α : Type u) (_ : Nat) where ofNat : α` (`ofBlock ηN`
over the head `ηN` of `Nat`: two parameters, the second of type `Nat`, one constructor with the
ordinary field `ofNat : α`, a structure in `Type u`), the typing of its terms in any environment
whose heads hold it, the η-terms the translator builds for its constants (`Frontend.indTerm`,
`ctorTerm`, `recrTerm`) typed at the translations of the constants' Lean types, and the Metalean
forms of `OfNat.ofNat` (the structure projection of the field) and `instOfNatNat`, typed at their
types. For `Test/NVAModel.lean`.
-/

open Lean Metalean

namespace EraseProof.Test.NVA

open EraseProof.Test.NV1 (typed_of_eq var_of_get app_typed const_typed fin0_eq lu)

open EraseProof.Test.NVS (one q0 q1 r0 r1 r2)
open EraseProof.Test.NVL (nSig nBlock mN mZ mS mN_typed mZ_typed mS_typed indN_typed)

/-! ## The block -/

abbrev ofCtorSig : CtorSig 1 :=
  { nfields := 1, nrecFields := 0, recursiveArity := ![], recursiveTarget := ![] }
abbrev ofSig : IndSig :=
  { nlevels := 1, nparams := 2, nsorts := 1, nindices _ := 0, nctors _ := 1,
    ctors _ _ := ofCtorSig }

/-- `class OfNat (α : Type u) (_ : Nat) where ofNat : α` as a Metalean block over `Nat`'s head. -/
@[reducible] def ofBlock {ζ : Sigs} (ηN : Head ζ (.inductive nSig)) : Inductive ζ ofSig where
  params := #t[.sort (.succ (.param 0)), mN ηN]
  indices _ := .nil
  level := .succ (.param 0)
  ctors _ _ := {
    ordinary _ := ⟨.var ⟨0, by simp⟩, .succ (.param 0)⟩
    recursive f := Fin.elim0 f
    targetIndices i := Fin.elim0 i }

@[simp] theorem ofBlock_map {ζ₁ ζ₂ : Sigs} (pre : ζ₁ ⟶ ζ₂) (ηN : Head ζ₁ (.inductive nSig)) :
    (ofBlock ηN).map pre = ofBlock (ηN.map pre) := by
  dsimp [Inductive.map]
  congr
  · simp [mN, Expr.map]
  · funext s c
    dsimp [Ctor.map, Field.map]
    congr
    · funext i; exact Fin.elim0 i
    · funext i; exact Fin.elim0 i

theorem ofLevel_ge {ℓ : Nat} {u : Level ℓ} : Metalean.Level.one ≤ (.succ u : Level ℓ) :=
  fun ν => by simp

theorem ofBlock_wf {ζ : Sigs} {E : Env ζ} {ηN : Head ζ (.inductive nSig)}
    (hn : (E.get ηN).block = nBlock) : InductiveWF E (ofBlock ηN) :=
  ⟨.snoc (.snoc .nil ⟨_, trivial, .sortDF⟩) ⟨_, trivial, mN_typed hn⟩,
    fun _ => .nil,
    fun _ _ => {
      ordinary
        | ⟨0, _⟩ => ⟨.var .sortDF, fun ν => by simp [Nat.imax]⟩
      recursive := fun f => Fin.elim0 f
      targetIndices := fun i => Fin.elim0 i
    }⟩

theorem largeElimOf {ζ : Sigs} {ηN : Head ζ (.inductive nSig)} : LeanLargeElim (ofBlock ηN) :=
  Or.inl (ofLevel_ge (u := .param 0))

/-- `OfNat` is a structure: its constructor `OfNat.mk` is the only one, without indices or recursive
fields, and it eliminates into every sort. -/
theorem ofStruct {ζ : Sigs} {ηN : Head ζ (.inductive nSig)} : (ofBlock ηN).IsStructure 0 0 where
  sort_unique _ := Subsingleton.elim _ _
  ctor_unique _ := Subsingleton.elim _ _
  no_indices := ⟨fun i => Fin.elim0 i⟩
  no_recursive := ⟨fun i => Fin.elim0 i⟩
  largeElim := Or.inr (ofLevel_ge (u := .param 0))

section OfNat
variable {ζ : Sigs} {E : Env ζ} {ηN : Head ζ (.inductive nSig)} {η : Head ζ (.inductive ofSig)}
  {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n}

/-- `OfNat.{u} α x`, `OfNat.mk.{u} α x a`. -/
def mOf (η : Head ζ (.inductive ofSig)) (u : Level ℓ) (α x : Expr ζ ℓ n) : Expr ζ ℓ n :=
  .ind η 0 ![u] ![α, x] Fin.elim0
def mOfMk (η : Head ζ (.inductive ofSig)) (u : Level ℓ) (α x a : Expr ζ ℓ n) : Expr ζ ℓ n :=
  .ctor η 0 0 ![u] ![α, x] ![a] Fin.elim0

theorem recAllowedOf (ho : (E.get η).block = ofBlock ηN) {ls : Fin 1 → Level ℓ} {l : Level ℓ} :
    (E.get η).block.RecAllowed ls l := by
  rw [ho]; exact largeElimOf.toLargeElim.recAllowed ls l

theorem ofParams (ho : (E.get η).block = ofBlock ηN) {u : Level ℓ} {α₁ α₂ x₁ x₂ : Expr ζ ℓ n}
    (hα : E[Γ] ⊢ α₁ ≡ α₂ : .sort (.succ u)) (hx : E[Γ] ⊢ x₁ ≡ x₂ : mN ηN) :
    ∀ p, E[Γ] ⊢ (![α₁, x₁] : Fin 2 → Expr ζ ℓ n) p ≡ (![α₂, x₂] : Fin 2 → Expr ζ ℓ n) p :
      (E.get η).block.paramType ![u] ![α₁, x₁] p := by
  intro p; fin_cases p <;> rw [ho]
  · simpa [Inductive.paramType, Ctx.entry] using hα
  · simp only [Inductive.paramType, Ctx.entry]
    convert hx using 2 <;> simp [mN]

theorem mOf_defeq (ho : (E.get η).block = ofBlock ηN) {u : Level ℓ} {α₁ α₂ x₁ x₂ : Expr ζ ℓ n}
    (hα : E[Γ] ⊢ α₁ ≡ α₂ : .sort (.succ u)) (hx : E[Γ] ⊢ x₁ ≡ x₂ : mN ηN) :
    E[Γ] ⊢ mOf η u α₁ x₁ ≡ mOf η u α₂ x₂ : .sort (.succ u) := by
  have h := Defeq.indDF (E := E) (Γ := Γ) (η := η) (s := 0) (ls := ![u]) (ps₁ := ![α₁, x₁])
    (ps₂ := ![α₂, x₂]) (is₁ := Fin.elim0) (is₂ := Fin.elim0) (ofParams ho hα hx)
    (fun i => Fin.elim0 i)
  rw [ho] at h
  simpa [mOf] using h

theorem mOf_typed (ho : (E.get η).block = ofBlock ηN) {u : Level ℓ} {α x : Expr ζ ℓ n}
    (hα : E[Γ] ⊢ α : .sort (.succ u)) (hx : E[Γ] ⊢ x : mN ηN) :
    E[Γ] ⊢ mOf η u α x : .sort (.succ u) :=
  mOf_defeq ho hα hx

theorem mOfMk_typed (ho : (E.get η).block = ofBlock ηN) {u : Level ℓ} {α x a : Expr ζ ℓ n}
    (hα : E[Γ] ⊢ α : .sort (.succ u)) (hx : E[Γ] ⊢ x : mN ηN) (ha : E[Γ] ⊢ a : α) :
    E[Γ] ⊢ mOfMk η u α x a : mOf η u α x := by
  have h := Defeq.ctorDF (E := E) (Γ := Γ) (η := η) (s := 0) (c := 0) (ls := ![u])
    (ps₁ := ![α, x]) (ps₂ := ![α, x]) (fds₁ := ![a]) (fds₂ := ![a])
    (recFds₁ := Fin.elim0) (recFds₂ := Fin.elim0)
    (fieldLevels := ![.succ u]) (recFieldLevels := fun f => Fin.elim0 f)
    (ofParams ho hα hx)
    (fun f => by
      fin_cases f; rw [ho]
      simp [Expr.subst]; exact ha)
    (fun f => Fin.elim0 f)
    (fun f => by
      fin_cases f; rw [ho]
      simp [Ctor.ordinaryFieldExpr, Expr.subst]; exact hα)
    (fun f => Fin.elim0 f)
    (by
      have := mOf_typed ho hα hx
      rw [ho]
      convert this using 2
      · simp only [mOf]; congr 1; funext i; exact i.elim0
      · simp only [mOf]; congr 1; funext i; exact i.elim0
      · simp)
  unfold mOfMk mOf
  convert h using 2

end OfNat

/-- Unfold Metalean's telescopes, recursor types and weakenings on `OfNat`'s terms; close
equalities of small `Fin` functions. -/
syntax (name := _ofs) "ofs" ("[" ident,* "]")? : tactic
macro_rules
  | `(tactic| ofs) => `(tactic| ofs [Ctx.get])
  | `(tactic| ofs [$ts,*]) => `(tactic| (nvsimp [$[$ts:ident],*, mOf, mOfMk, mN,
      Inductive.paramType, Inductive.indexType, Ctx.proj, Ctx.entry, Ctor.targetIndex,
      Fin.fun_vecCons, Fin.fun_vecEmpty, Expr.wkN, funext_iff, Fin.forall_fin_two,
      Fin.forall_fin_one, Fin.sum_succ, Fin.sum_zero, Level.inst_param, Subst.liftN, Ren.wkFrom,
      Fin.castLE, ML.Expr.apps_succ, CtorSig.fieldParams, Ctor.ordinaryFieldExpr,
      Expr.boundVars, Ctor.fieldTele, Ctor.ordinaryFieldTele, Expr.subst, Expr.instL, Ctx.instL,
      CtorSig.fieldOrdinary, Ctor.ordinaryTeleAux, Ren.comp, Expr.rename] <;> finCongr))

/-! ## `OfNat`'s, `OfNat.mk`'s and `OfNat.rec`'s η-terms -/

section OfTerms
variable {ζ : Sigs} {E : Env ζ} {ηN : Head ζ (.inductive nSig)} {η : Head ζ (.inductive ofSig)}

/-- `OfNat`'s type `Type u → Nat → Type u` (level `u` = parameter 0). -/
def ofTyM (ηN : Head ζ (.inductive nSig)) : Expr ζ 1 0 :=
  .forallE (.sort (.succ lu)) (.forallE (mN ηN) (.sort (.succ lu)))

/-- `OfNat`'s η-term `fun α x => OfNat α x`. -/
def ofTermM (ηN : Head ζ (.inductive nSig)) (η : Head ζ (.inductive ofSig)) : Expr ζ 1 0 :=
  .lam (.sort (.succ lu)) (.lam (mN ηN) (mOf η lu #0 #1))

/-- `OfNat.mk`'s type `{α : Type u} → {x : Nat} → α → OfNat α x`. -/
def ofMkTyM (ηN : Head ζ (.inductive nSig)) (η : Head ζ (.inductive ofSig)) : Expr ζ 1 0 :=
  .forallE (.sort (.succ lu)) (.forallE (mN ηN) (.forallE #0 (mOf η lu #0 #1)))

/-- `OfNat.mk`'s η-term. -/
def ofMkTermM (ηN : Head ζ (.inductive nSig)) (η : Head ζ (.inductive ofSig)) : Expr ζ 1 0 :=
  .lam (.sort (.succ lu)) (.lam (mN ηN) (.lam #0 (mOfMk η lu #0 #1 #2)))

theorem indTerm_eqOf (ho : (E.get η).block = ofBlock ηN) :
    Frontend.indTerm (E.get η).block η 0 ![lu] = ofTermM ηN η := by
  rw [ho]
  show Metalean.Expr.lam _ (Metalean.Expr.lam _ _) = _
  simp only [ofTermM]
  ofs [Inductive.argTele]

theorem ctorTerm_eqOf (ho : (E.get η).block = ofBlock ηN) :
    Frontend.ctorTerm (E.get η).block η 0 0 ![lu] [0] = .ok (ofMkTermM ηN η) := by
  rw [ho]
  have : (match Frontend.ctorTerm (ofBlock ηN) η 0 0 ![lu] [0] with
      | .ok t => t | .error _ => .prop) = ofMkTermM ηN η := by
    show Metalean.Expr.lam _ (Metalean.Expr.lam _ (Metalean.Expr.lam _ _)) = _
    simp only [ofMkTermM]
    ofs
  rw [← this]
  rfl

theorem ofTermM_typed (hn : (E.get ηN).block = nBlock) (ho : (E.get η).block = ofBlock ηN) :
    E[.nil] ⊢ ofTermM ηN η : ofTyM ηN := by
  have h1 : E[(#t[.sort (.succ lu)] : Ctx ζ 1 0 1)] ⊢ ok := .snoc .nil ⟨_, .sortDF⟩
  have hΓ : E[(#t[.sort (.succ lu), mN ηN] : Ctx ζ 1 0 2)] ⊢ ok := .snoc h1 ⟨_, mN_typed hn⟩
  have hα : E[(#t[.sort (.succ lu), mN ηN] : Ctx ζ 1 0 2)] ⊢ #0 : .sort (.succ lu) :=
    var_of_get hΓ ⟨0, by decide⟩ (by ofs)
  have hx : E[(#t[.sort (.succ lu), mN ηN] : Ctx ζ 1 0 2)] ⊢ #1 : mN ηN :=
    var_of_get hΓ ⟨1, by decide⟩ (by ofs)
  have h := mOf_typed (η := η) ho hα hx
  exact Ctx.lam_congr (Γ := .nil) (Δ := #t[.sort (.succ lu), mN ηN]) hΓ h

theorem ofMkTermM_typed (hn : (E.get ηN).block = nBlock) (ho : (E.get η).block = ofBlock ηN) :
    E[.nil] ⊢ ofMkTermM ηN η : ofMkTyM ηN η := by
  have h1 : E[(#t[.sort (.succ lu)] : Ctx ζ 1 0 1)] ⊢ ok := .snoc .nil ⟨_, .sortDF⟩
  have h2 : E[(#t[.sort (.succ lu), mN ηN] : Ctx ζ 1 0 2)] ⊢ ok := .snoc h1 ⟨_, mN_typed hn⟩
  have hΓ : E[(#t[.sort (.succ lu), mN ηN, #0] : Ctx ζ 1 0 3)] ⊢ ok :=
    .snoc h2 ⟨_, var_of_get h2 ⟨0, by decide⟩ (by ofs)⟩
  have hα : E[(#t[.sort (.succ lu), mN ηN, #0] : Ctx ζ 1 0 3)] ⊢ #0 : .sort (.succ lu) :=
    var_of_get hΓ ⟨0, by decide⟩ (by ofs)
  have hx : E[(#t[.sort (.succ lu), mN ηN, #0] : Ctx ζ 1 0 3)] ⊢ #1 : mN ηN :=
    var_of_get hΓ ⟨1, by decide⟩ (by ofs)
  have ha : E[(#t[.sort (.succ lu), mN ηN, #0] : Ctx ζ 1 0 3)] ⊢ #2 : #0 :=
    var_of_get hΓ ⟨2, by decide⟩ (by ofs)
  have h := mOfMk_typed (η := η) ho hα hx ha
  exact Ctx.lam_congr (Γ := .nil) (Δ := #t[.sort (.succ lu), mN ηN, #0]) hΓ h

/-- `(t : OfNat α x) → Sort u_1`, under `α x` (levels `u_1`, `u` = parameters 0, 1). -/
def ofMotM (η : Head ζ (.inductive ofSig)) : Expr ζ 2 2 := .forallE (mOf η q1 #0 #1) (.sort q0)

/-- `(ofNat : α) → motive ⟨ofNat⟩`, under `α x motive`. -/
def ofMinM (η : Head ζ (.inductive ofSig)) : Expr ζ 2 3 :=
  .forallE #0 (.app #2 (mOfMk η q1 #0 #1 #3))

/-- `OfNat.rec`'s type. -/
def ofRecTyM (ηN : Head ζ (.inductive nSig)) (η : Head ζ (.inductive ofSig)) : Expr ζ 2 0 :=
  .forallE (.sort (.succ q1)) (.forallE (mN ηN) (.forallE (ofMotM η) (.forallE (ofMinM η)
    (.forallE (mOf η q1 #0 #1) (.app #2 #4)))))

/-- The body of `OfNat.rec`'s η-term. -/
def ofRecBody (η : Head ζ (.inductive ofSig)) : Expr ζ 2 5 :=
  .recr η 0 ![q1] q0 ![#0, #1] (fun _ => #2) (fun _ _ => #3) Fin.elim0 #4

/-- What `Frontend.recrTerm` builds for `OfNat.rec`. -/
def ofRecTermM (ηN : Head ζ (.inductive nSig)) (η : Head ζ (.inductive ofSig)) : Expr ζ 2 0 :=
  .lam (.sort (.succ q1)) (.lam (mN ηN) (.lam (ofMotM η) (.lam (ofMinM η)
    (.lam (mOf η q1 #0 #1) (ofRecBody η)))))

set_option linter.unusedTactic false in
theorem recrTerm_eqOf (ho : (E.get η).block = ofBlock ηN) :
    Frontend.recrTerm (E.get η).block η 0 ![q1] q0 (fun _ _ => [0]) =
      .ok (ofRecTermM ηN η) := by
  rw [ho]
  have : (match Frontend.recrTerm (ofBlock ηN) η 0 ![q1] q0 (fun _ _ => [0]) with
      | .ok t => t | .error _ => .prop) = ofRecTermM ηN η := by
    show Metalean.Expr.lam _ (Metalean.Expr.lam _ (Metalean.Expr.lam _ (Metalean.Expr.lam _
      (Metalean.Expr.lam _ (Metalean.Expr.recr _ _ _ _ _ _ _ _ _))))) = _
    simp only [ofRecTermM, ofRecBody, ofMotM, ofMinM]
    repeat' (first
      | (funext t c; fin_cases t; fin_cases c <;> rfl)
      | (funext t; fin_cases t <;> rfl)
      | (funext i; exact i.elim0)
      | (ofs; done)
      | rfl
      | congr 1)
  rw [← this]
  rfl

theorem ofRecTermM_typed (hn : (E.get ηN).block = nBlock) (ho : (E.get η).block = ofBlock ηN) :
    E[.nil] ⊢ ofRecTermM ηN η : ofRecTyM ηN η := by
  have h1 : E[(#t[.sort (.succ q1)] : Ctx ζ 2 0 1)] ⊢ ok := .snoc .nil ⟨_, .sortDF⟩
  have h2 : E[(#t[.sort (.succ q1), mN ηN] : Ctx ζ 2 0 2)] ⊢ ok := .snoc h1 ⟨_, mN_typed hn⟩
  have hα2 : E[(#t[.sort (.succ q1), mN ηN] : Ctx ζ 2 0 2)] ⊢ #0 : .sort (.succ q1) :=
    var_of_get h2 ⟨0, by decide⟩ (by ofs)
  have hx2 : E[(#t[.sort (.succ q1), mN ηN] : Ctx ζ 2 0 2)] ⊢ #1 : mN ηN :=
    var_of_get h2 ⟨1, by decide⟩ (by ofs)
  have hO2 := mOf_typed ho (η := η) hα2 hx2
  have h2t : E[(#t[.sort (.succ q1), mN ηN, mOf η q1 #0 #1] : Ctx ζ 2 0 3)] ⊢ ok :=
    .snoc h2 ⟨_, hO2⟩
  have hmot := Defeq.forallEDF (l₂ := (.succ q0)) hO2
    (.sortDF (Γ := (#t[.sort (.succ q1), mN ηN, mOf η q1 #0 #1] : Ctx ζ 2 0 3))) .sortDF
  have h3 : E[(#t[.sort (.succ q1), mN ηN, ofMotM η] : Ctx ζ 2 0 3)] ⊢ ok := .snoc h2 ⟨_, hmot⟩
  have h4 : E[(#t[.sort (.succ q1), mN ηN, ofMotM η, #0] : Ctx ζ 2 0 4)] ⊢ ok :=
    .snoc h3 ⟨_, var_of_get h3 ⟨0, by decide⟩ (by ofs)⟩
  have hmk4 : E[(#t[.sort (.succ q1), mN ηN, ofMotM η, #0] : Ctx ζ 2 0 4)] ⊢
      .app #2 (mOfMk η q1 #0 #1 #3) : .sort q0 :=
    typed_of_eq (app_typed (var_of_get h4 ⟨2, by decide⟩ (by ofs [ofMotM]))
      (mOfMk_typed ho (var_of_get h4 ⟨0, by decide⟩ (by ofs)) (var_of_get h4 ⟨1, by decide⟩ (by ofs))
        (var_of_get h4 ⟨3, by decide⟩ (by ofs))))
      (by ofs)
  have hmin : E[(#t[.sort (.succ q1), mN ηN, ofMotM η] : Ctx ζ 2 0 3)] ⊢ ofMinM η : _ :=
    .forallEDF (var_of_get h3 ⟨0, by decide⟩ (by ofs)) hmk4 hmk4
  have h4' : E[(#t[.sort (.succ q1), mN ηN, ofMotM η, ofMinM η] : Ctx ζ 2 0 4)] ⊢ ok :=
    .snoc h3 ⟨_, hmin⟩
  have hΓ : E[(#t[.sort (.succ q1), mN ηN, ofMotM η, ofMinM η, mOf η q1 #0 #1] : Ctx ζ 2 0 5)] ⊢
      ok :=
    .snoc h4' ⟨_, mOf_typed ho (var_of_get h4' ⟨0, by decide⟩ (by ofs))
      (var_of_get h4' ⟨1, by decide⟩ (by ofs))⟩
  have hbody : E[(#t[.sort (.succ q1), mN ηN, ofMotM η, ofMinM η, mOf η q1 #0 #1] :
      Ctx ζ 2 0 5)] ⊢ ofRecBody η : .app #2 #4 := by
    have h := Defeq.recrDF (E := E) (η := η) (s := 0) (ls := ![q1]) (l := q0)
      (Γ := #t[.sort (.succ q1), mN ηN, ofMotM η, ofMinM η, mOf η q1 #0 #1])
      (ps₁ := ![#0, #1]) (ps₂ := ![#0, #1]) (ms₁ := fun _ => #2) (ms₂ := fun _ => #2)
      (mins₁ := fun _ _ => #3) (mins₂ := fun _ _ => #3) (is₁ := Fin.elim0) (is₂ := Fin.elim0)
      (maj₁ := #4) (maj₂ := #4) (recAllowedOf ho)
      (ofParams ho (var_of_get hΓ ⟨0, by decide⟩ (by ofs))
        (var_of_get hΓ ⟨1, by decide⟩ (by ofs))) ?_ ?_ (fun i => Fin.elim0 i) ?_ ?_
    · exact h
    · intro s; fin_cases s; rw [ho]; exact var_of_get hΓ ⟨2, by decide⟩ (by ofs [ofMotM])
    · intro s c; fin_cases s; fin_cases c; rw [ho]
      exact var_of_get hΓ ⟨3, by decide⟩ (by ofs [ofMinM])
    · exact typed_of_eq (var_of_get (T := mOf η q1 #0 #1) hΓ ⟨4, by decide⟩ (by ofs)) (by ofs)
    · have hm : E[(#t[.sort (.succ q1), mN ηN, ofMotM η, ofMinM η, mOf η q1 #0 #1] :
          Ctx ζ 2 0 5)] ⊢ #2 : .forallE (mOf η q1 #0 #1) (.sort q0) :=
        var_of_get hΓ ⟨2, by decide⟩ (by ofs [ofMotM])
      exact typed_of_eq (app_typed hm (var_of_get hΓ ⟨4, by decide⟩ (by ofs))) (by ofs)
  exact Ctx.lam_congr (Γ := .nil)
    (Δ := #t[.sort (.succ q1), mN ηN, ofMotM η, ofMinM η, mOf η q1 #0 #1]) hΓ hbody

end OfTerms

/-! ## `OfNat.ofNat` and `instOfNatNat` -/

section Defs
variable {ζ : Sigs} (ηN : Head ζ (.inductive nSig)) (ηO : Head ζ (.inductive ofSig))

/-- `OfNat.ofNat`'s type `{α : Type u} → (x : Nat) → [self : OfNat α x] → α`. -/
def ofNatTyM : Expr ζ 1 0 :=
  .forallE (.sort (.succ lu)) (.forallE (mN ηN) (.forallE (mOf ηO lu #0 #1) #0))

/-- The projection `self.1` of `self : OfNat α x`, as Metalean's structure projection
(`Inductive.IsStructure.projTerm`) computes it: the recursor of `OfNat` into `α` whose minor
returns the field. -/
def projOfM : Expr ζ 1 3 :=
  .recr ηO 0 ![lu] (.succ lu) ![#0, #1] (fun _ => .lam (mOf ηO lu #0 #1) #0) (fun _ _ => .lam #0 #3)
    Fin.elim0 #2

/-- `fun α x self => self.1` -/
def ofNatValM : Expr ζ 1 0 :=
  .lam (.sort (.succ lu)) (.lam (mN ηN) (.lam (mOf ηO lu #0 #1) (projOfM ηO)))

/-- `instOfNatNat`'s type `(n : Nat) → OfNat Nat n` and value `fun n => OfNat.mk Nat n n`. -/
def instTyM : Expr ζ 0 0 := .forallE (mN ηN) (mOf ηO .zero (mN ηN) #0)
def instValM : Expr ζ 0 0 := .lam (mN ηN) (mOfMk ηO .zero (mN ηN) #0 #0)

end Defs

theorem projTerm_eqOf {ζ : Sigs} {ηN : Head ζ (.inductive nSig)} {ηO : Head ζ (.inductive ofSig)}
    {I : Inductive ζ ofSig} (h : I.IsStructure 0 0) (hI : I = ofBlock ηN) :
    h.projTerm ηO ![lu] ![#0, #1] ⟨0, by decide⟩ (#2 : Expr ζ 1 3) = projOfM ηO := by
  subst hI
  rw [Inductive.IsStructure.projTerm_eq_recr]
  simp only [projOfM]
  congr 1
  case e_ms =>
    funext t; fin_cases t
    delta Inductive.IsStructure.projectionMotives
    arsx [Inductive.IsStructure.projTypeWith, Inductive.motiveTele, Inductive.indexTele, Ctx.substN,
      mOf]
  case e_mins =>
    funext t c; fin_cases t; fin_cases c
    delta Inductive.IsStructure.projectionCases
    arsx [Inductive.caseTele, CtorSig.caseOrdinary,
      CtorSig.fieldOrdinary, Ctor.fieldTele, Ctor.ordinaryFieldTele, Ctor.ordinaryTeleAux,
      Ctor.ihTele, Ctx.ofTypes, Ctor.recursiveFieldTeleAux, Expr.boundVars,
      Ctor.ordinaryFieldTeleAux, Tele.foldr, Ctx.substN, Subst.liftN]

theorem projType_eqOf {ζ : Sigs} {ηN : Head ζ (.inductive nSig)} {ηO : Head ζ (.inductive ofSig)}
    {I : Inductive ζ ofSig} (h : I.IsStructure 0 0) (hI : I = ofBlock ηN) :
    h.projType ηO ![lu] ![#0, #1] ⟨0, by decide⟩ (#2 : Expr ζ 1 3) = #0 := by
  subst hI
  rw [Inductive.IsStructure.projType, Inductive.IsStructure.projection]
  simp only [Inductive.IsStructure.projTypeWith]
  arsx

section DefsTyped
variable {ζ : Sigs} {E : Env ζ} {ηN : Head ζ (.inductive nSig)} {ηO : Head ζ (.inductive ofSig)}
  (hE : EnvWF E) (hn : (E.get ηN).block = nBlock) (ho : (E.get ηO).block = ofBlock ηN)
include hn ho

/-- `OfNat.ofNat`'s binder context `α x self`. -/
def ΓO (ηN : Head ζ (.inductive nSig)) (ηO : Head ζ (.inductive ofSig)) : Ctx ζ 1 0 3 :=
  #t[.sort (.succ lu), mN ηN, mOf ηO lu #0 #1]

include hE in
theorem ofNatValM_typed : E[.nil] ⊢ ofNatValM ηN ηO : ofNatTyM ηN ηO := by
  have h1 : E[(#t[.sort (.succ lu)] : Ctx ζ 1 0 1)] ⊢ ok := .snoc .nil ⟨_, .sortDF⟩
  have h2 : E[(#t[.sort (.succ lu), mN ηN] : Ctx ζ 1 0 2)] ⊢ ok := .snoc h1 ⟨_, mN_typed hn⟩
  have hO := mOf_typed (η := ηO) ho (var_of_get h2 ⟨0, by decide⟩ (by ofs))
    (var_of_get h2 ⟨1, by decide⟩ (by ofs))
  have hΓ : E[ΓO ηN ηO] ⊢ ok := .snoc h2 ⟨_, hO⟩
  have hα : E[ΓO ηN ηO] ⊢ #0 : .sort (.succ lu) := var_of_get hΓ ⟨0, by decide⟩ (by ofs [ΓO])
  have hx : E[ΓO ηN ηO] ⊢ #1 : mN ηN := var_of_get hΓ ⟨1, by decide⟩ (by ofs [ΓO])
  have hst : (E.get ηO).block.IsStructure 0 0 := ho ▸ ofStruct
  have hB : InductiveWF E (E.get ηO).block := (hE.entryWF ηO).block
  have hps := ofParams ho hα hx
  have hmaj : E[ΓO ηN ηO] ⊢ #2 : .ind ηO 0 ![lu] ![#0, #1] hst.indices := by
    rw [← hst.indices_eq Fin.elim0]
    exact var_of_get hΓ ⟨2, by decide⟩ (by ofs [ΓO])
  have h := hst.projTerm_hasType hB ⟨0, by decide⟩ hΓ hps hmaj
  rw [projTerm_eqOf hst ho, projType_eqOf hst ho] at h
  exact Ctx.lam_congr (Γ := .nil) (Δ := ΓO ηN ηO) hΓ h

theorem instValM_typed : E[.nil] ⊢ instValM ηN ηO : instTyM ηN ηO := by
  have h1 : E[(#t[mN ηN] : Ctx ζ 0 0 1)] ⊢ ok := .snoc .nil ⟨_, mN_typed hn⟩
  have hx : E[(#t[mN ηN] : Ctx ζ 0 0 1)] ⊢ #0 : mN ηN := var_of_get h1 ⟨0, by decide⟩ (by ofs)
  have h := mOfMk_typed (η := ηO) ho (mN_typed hn) hx hx
  exact Ctx.lam_congr (Γ := .nil) (Δ := #t[mN ηN]) h1 h

end DefsTyped

end EraseProof.Test.NVA
