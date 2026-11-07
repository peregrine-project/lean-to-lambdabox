import EraseProof.Test.NVPData
import EraseProof.Test.NV1Model
import Metalean.Builtin.Env
import Metalean.Metatheory.SubjectReduction

/-!
# NV-P: the Metalean model of the program

The premises of the final theorem about the program and its model, for NV-P (`Test/NVPData.lean`):
the program `P` is the Lean form of the well-formed Metalean environment `EB` with name table `BB`
(`henv`, `hwf`), and the erased term `e` is the Lean form of the closed Metalean term `tE`, which is
typed (`he`, `hty`).

`Eq`'s Metalean block is Metalean's `Eq.block` (well formed by `Eq.wf`, `ML Builtin/Env.lean:33`).
Typing facts are proved for any environment whose head `η` holds `Eq.block`. `EB` holds three
entries: NV-1's block `B`, the block `Eq` and `Eq.casesOn` (a definition whose value is a saturated
`recr`). The input's typing (`tE_typed_of`) is proved for any such environment with a major premise
of type `@Eq B B.t B.t`, which NV-K (`Test/NVKModel.lean`) shares.
-/

open Lean Metalean

namespace EraseProof.Test.NVP

open EraseProof.Test.NV1 (tB cT mB mT mMot bSig bBlock indB_typed ctorB_typed typed_of_eq var_of_get
  app_typed const_typed ζ1 E1 B1 wf1 henv1 P1 P1_eq tr_B tr_T notSpecial_bvar notSpecial_const
  trLevels_nil)

section Generic
variable {ζ : Sigs} {E : Env ζ} {η : Head ζ (.inductive Eq.sig)} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n}

/-- Retype at an equal sort level. -/
theorem typed_of_eq' {e : Expr ζ ℓ n} {l l' : Level ℓ} (h : E[Γ] ⊢ e : .sort l) (hl : l = l') :
    E[Γ] ⊢ e : .sort l' :=
  hl ▸ h

/-- `@Eq.{l} α a b`. -/
abbrev eqA (η : Head ζ (.inductive Eq.sig)) (l : Level ℓ) (α a b : Expr ζ ℓ n) : Expr ζ ℓ n :=
  Quot.eqApp η l α a b

/-- `@Eq.refl.{l} α a`. -/
def reflA (η : Head ζ (.inductive Eq.sig)) (l : Level ℓ) (α a : Expr ζ ℓ n) : Expr ζ ℓ n :=
  .ctor η 0 0 ![l] ![α, a] Fin.elim0 Fin.elim0

theorem eqA_typed (hq : (E.get η).block = Eq.block) {l : Level ℓ} {α a b : Expr ζ ℓ n}
    (hα : E[Γ] ⊢ α : .sort l) (ha : E[Γ] ⊢ a : α) (hb : E[Γ] ⊢ b : α) :
    E[Γ] ⊢ eqA η l α a b : .prop :=
  Quot.eqApp_typed hq hα ha hb

theorem reflA_typed (hq : (E.get η).block = Eq.block) {l : Level ℓ} {α a : Expr ζ ℓ n}
    (hα : E[Γ] ⊢ α : .sort l) (ha : E[Γ] ⊢ a : α) :
    E[Γ] ⊢ reflA η l α a : eqA η l α a a := by
  have hps : ∀ p, E[Γ] ⊢ (![α, a] : Fin 2 → Expr ζ ℓ n) p ≡ (![α, a] : Fin 2 → Expr ζ ℓ n) p :
      (E.get η).block.paramType ![l] ![α, a] p := by
    intro p; fin_cases p
    · simpa! [hq, Inductive.paramType] using hα
    · simpa! [hq, Inductive.paramType] using ha
  have h := Defeq.ctorDF (E := E) (Γ := Γ) (η := η) (s := 0) (c := 0) (ls := ![l])
    (ps₁ := ![α, a]) (ps₂ := ![α, a]) (fds₁ := Fin.elim0) (fds₂ := Fin.elim0)
    (recFds₁ := Fin.elim0) (recFds₂ := Fin.elim0)
    (fieldLevels := fun f => Fin.elim0 f) (recFieldLevels := fun f => Fin.elim0 f)
    hps (fun f => Fin.elim0 f) (fun f => Fin.elim0 f) (fun f => Fin.elim0 f)
    (fun f => Fin.elim0 f) ?_
  · convert h using 2
    all_goals first
      | rfl
      | (funext i; fin_cases i; rw [hq]; simp! [Ctor.targetIndex, Eq.ctorDecl])
  · refine Defeq.indDF hps ?_
    intro i; fin_cases i
    rw [hq]; simpa! [Ctor.targetIndex, Eq.ctorDecl, Inductive.indexType, Ctx.proj] using ha

end Generic

/-- Close an `Expr` equation whose sides differ in small `Fin` functions, by congruence. -/
macro (name := _finCongr) "finCongr" : tactic => `(tactic| first
  | rfl
  | (congr 1 <;> first | rfl | (funext i; fin_cases i <;> rfl) | (funext i; exact i.elim0)))

/-- Unfold Metalean's telescopes, recursor types and weakenings on `Eq`'s terms; close the
remaining equalities of small `Fin` functions. -/
syntax (name := _eqsimp) "eqsimp" ("[" ident,* "]")? : tactic
macro_rules
  | `(tactic| eqsimp) => `(tactic| eqsimp [Ctx.get])
  | `(tactic| eqsimp [$ts,*]) => `(tactic| (nvsimp [$[$ts:ident],*, Eq.block, Eq.ctorDecl,
      Inductive.paramType, Inductive.indexType, Ctx.proj, Ctor.targetIndex, Fin.fun_vecCons,
      Fin.fun_vecEmpty, reflA, Quot.eqApp, Expr.wkN, funext_iff, Fin.forall_fin_two,
      Fin.forall_fin_one, Fin.sum_succ, Fin.sum_zero, Level.inst_param, Subst.liftN, eqA,
      Ren.wkFrom, Fin.castLE, Expr.apps_succ, CtorSig.fieldParams] <;> finCongr))

/-! ## `Eq`'s and `Eq.refl`'s η-terms (level `u_1` = parameter 0) -/

section Ind
variable {ζ : Sigs} {E : Env ζ} {η : Head ζ (.inductive Eq.sig)}

abbrev pA : Level 1 := .param 0

/-- `Eq`'s type `{α : Sort u_1} → α → α → Prop` in Metalean. -/
def eqTyM (_η : Head ζ (.inductive Eq.sig)) : Expr ζ 1 0 :=
  .forallE (.sort pA) (.forallE #0 (.forallE #0 .prop))

/-- `Eq`'s η-term. -/
def eqIndTermM (η : Head ζ (.inductive Eq.sig)) : Expr ζ 1 0 :=
  .lam (.sort pA) (.lam #0 (.lam #0 (eqA η pA #0 #1 #2)))

/-- `Eq.refl`'s type `{α : Sort u_1} → (a : α) → a = a` in Metalean. -/
def eqReflTyM (η : Head ζ (.inductive Eq.sig)) : Expr ζ 1 0 :=
  .forallE (.sort pA) (.forallE #0 (eqA η pA #0 #1 #1))

/-- `Eq.refl`'s η-term. -/
def eqReflTermM (η : Head ζ (.inductive Eq.sig)) : Expr ζ 1 0 :=
  .lam (.sort pA) (.lam #0 (reflA η pA #0 #1))

theorem indTerm_eq (hq : (E.get η).block = Eq.block) :
    Frontend.indTerm (E.get η).block η 0 ![pA] = eqIndTermM η := by
  rw [hq]
  show Metalean.Expr.lam _ (Metalean.Expr.lam _ (Metalean.Expr.lam _ _)) = _
  simp only [eqIndTermM]
  eqsimp

theorem ctorTerm_eq (hq : (E.get η).block = Eq.block) :
    Frontend.ctorTerm (E.get η).block η 0 0 ![pA] [] = .ok (eqReflTermM η) := by
  rw [hq]
  have : (match Frontend.ctorTerm (Eq.block (ζ := ζ)) η 0 0 ![pA] [] with
      | .ok t => t | .error _ => .prop) = eqReflTermM η := by
    show Metalean.Expr.lam _ (Metalean.Expr.lam _ _) = _
    simp only [eqReflTermM, reflA]
    eqsimp
  rw [← this]
  rfl

theorem Γ3_wf :
    E[(#t[.sort pA, #0, #0] : Ctx ζ 1 0 3)] ⊢ ok := by
  have h1 : E[(#t[.sort pA] : Ctx ζ 1 0 1)] ⊢ ok := .snoc .nil ⟨_, .sortDF⟩
  have h2 : E[(#t[.sort pA, #0] : Ctx ζ 1 0 2)] ⊢ ok :=
    .snoc h1 ⟨pA, var_of_get h1 ⟨0, by decide⟩ (by eqsimp)⟩
  exact .snoc h2 ⟨pA, var_of_get h2 ⟨0, by decide⟩ (by eqsimp)⟩

theorem eqIndTermM_typed (hq : (E.get η).block = Eq.block) :
    E[.nil] ⊢ eqIndTermM η : eqTyM η := by
  have hΓ := Γ3_wf (E := E) (ζ := ζ)
  have h := eqA_typed (η := η) (l := pA) hq (var_of_get hΓ ⟨0, by decide⟩ (by eqsimp))
    (var_of_get hΓ ⟨1, by decide⟩ (by eqsimp)) (var_of_get hΓ ⟨2, by decide⟩ (by eqsimp))
  exact Ctx.lam_congr (Γ := .nil) (Δ := #t[.sort pA, #0, #0]) hΓ h

theorem eqReflTermM_typed (hq : (E.get η).block = Eq.block) :
    E[.nil] ⊢ eqReflTermM η : eqReflTyM η := by
  have h1 : E[(#t[.sort pA] : Ctx ζ 1 0 1)] ⊢ ok := .snoc .nil ⟨_, .sortDF⟩
  have hΓ : E[(#t[.sort pA, #0] : Ctx ζ 1 0 2)] ⊢ ok :=
    .snoc h1 ⟨pA, var_of_get h1 ⟨0, by decide⟩ (by eqsimp)⟩
  have h := reflA_typed (η := η) (l := pA) hq (var_of_get hΓ ⟨0, by decide⟩ (by eqsimp))
    (var_of_get hΓ ⟨1, by decide⟩ (by eqsimp))
  exact Ctx.lam_congr (Γ := .nil) (Δ := #t[.sort pA, #0]) hΓ h

end Ind

/-! ## `Eq.rec`'s η-term and `Eq.casesOn`'s value (levels `u` = parameter 0, `u_1` = parameter 1) -/

section Rec
variable {ζ : Sigs} {E : Env ζ} {η : Head ζ (.inductive Eq.sig)}

abbrev mu0 : Level 2 := .param 0
abbrev mu1 : Level 2 := .param 1

/-- `(a_1 : α) → a = a_1 → Sort u`, under `α a`. -/
def motM (η : Head ζ (.inductive Eq.sig)) : Expr ζ 2 2 :=
  .forallE #0 (.forallE (eqA η mu1 #0 #1 #2) (.sort mu0))

/-- `motive a (Eq.refl a)`, under `α a motive …`. -/
def minM (η : Head ζ (.inductive Eq.sig)) {n : Nat} (h : 3 ≤ n) : Expr ζ 2 n :=
  .app (.app (.var ⟨2, by omega⟩) (.var ⟨1, by omega⟩))
    (reflA η mu1 (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩))

/-- `Eq.rec`'s type in Metalean. -/
def eqRecTyM (η : Head ζ (.inductive Eq.sig)) : Expr ζ 2 0 :=
  .forallE (.sort mu1) (.forallE #0 (.forallE (motM η) (.forallE (minM η (by omega))
    (.forallE #0 (.forallE (eqA η mu1 #0 #1 #4) (.app (.app #2 #4) #5))))))

/-- The body of `Eq.rec`'s η-term. -/
def eqRecBody (η : Head ζ (.inductive Eq.sig)) : Expr ζ 2 6 :=
  .recr η 0 ![mu1] mu0 ![#0, #1] (fun _ => #2) (fun _ _ => #3) ![#4] #5

/-- What `Frontend.recrTerm` builds for `Eq.rec`. -/
def eqRecTermM (η : Head ζ (.inductive Eq.sig)) : Expr ζ 2 0 :=
  .lam (.sort mu1) (.lam #0 (.lam (motM η) (.lam (minM η (by omega))
    (.lam #0 (.lam (eqA η mu1 #0 #1 #4) (eqRecBody η))))))

theorem recrTerm_eqRec (hq : (E.get η).block = Eq.block) :
    Frontend.recrTerm (E.get η).block η 0 ![mu1] mu0 (fun _ _ => []) = .ok (eqRecTermM η) := by
  rw [hq]
  have : (match Frontend.recrTerm (Eq.block (ζ := ζ)) η 0 ![mu1] mu0 (fun _ _ => []) with
      | .ok t => t | .error _ => .prop) = eqRecTermM η := by
    show Metalean.Expr.lam _ (Metalean.Expr.lam _ (Metalean.Expr.lam _ (Metalean.Expr.lam _ (Metalean.Expr.lam _ (Metalean.Expr.lam _
      (Metalean.Expr.recr _ _ _ _ _ _ _ _ _)))))) = _
    simp only [eqRecTermM, eqRecBody, motM, minM]
    refine congrArg₂ Metalean.Expr.lam ?_ (congrArg₂ Metalean.Expr.lam ?_ (congrArg₂ Metalean.Expr.lam ?_
      (congrArg₂ Metalean.Expr.lam ?_ (congrArg₂ Metalean.Expr.lam ?_ (congrArg₂ Metalean.Expr.lam ?_ ?_)))))
    case refine_7 =>
      congr 1 <;> first
        | (funext t c; fin_cases t; fin_cases c; rfl)
        | (funext t; fin_cases t <;> rfl)
    all_goals eqsimp
  rw [← this]
  rfl

theorem eqBlock_subsingleton {ζ : Sigs} {ℓ : Nat} {ls : Fin 1 → Level ℓ} {l : Level ℓ} :
    (Eq.block (ζ := ζ)).RecAllowed ls l :=
  .inl ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ _ => ⟨fun f => Fin.elim0 f, fun f => Fin.elim0 f⟩⟩

/-- `α : Sort u_1, a : α` is well formed. -/
theorem Γ2_wf : E[(#t[.sort mu1, #0] : Ctx ζ 2 0 2)] ⊢ ok := by
  have h1 : E[(#t[.sort mu1] : Ctx ζ 2 0 1)] ⊢ ok := .snoc .nil ⟨_, .sortDF⟩
  exact .snoc h1 ⟨mu1, var_of_get h1 ⟨0, by decide⟩ (by eqsimp)⟩

theorem motM_typed (hq : (E.get η).block = Eq.block) :
    E[(#t[.sort mu1, #0] : Ctx ζ 2 0 2)] ⊢ motM η : .sort (.imax mu1 (.imax .zero (.succ mu0))) := by
  have h2 := Γ2_wf (E := E) (ζ := ζ)
  have h3 : E[(#t[.sort mu1, #0, #0] : Ctx ζ 2 0 3)] ⊢ ok :=
    .snoc h2 ⟨mu1, var_of_get h2 ⟨0, by decide⟩ (by eqsimp)⟩
  have heq := eqA_typed (η := η) (l := mu1) hq (var_of_get h3 ⟨0, by decide⟩ (by eqsimp))
    (var_of_get h3 ⟨1, by decide⟩ (by eqsimp)) (var_of_get h3 ⟨2, by decide⟩ (by eqsimp))
  exact .forallEDF (var_of_get h2 ⟨0, by decide⟩ (by eqsimp)) (.forallEDF heq .sortDF .sortDF)
    (.forallEDF heq .sortDF .sortDF)

/-- `α a motive` is well formed. -/
theorem ΓM_wf (hq : (E.get η).block = Eq.block) :
    E[(#t[.sort mu1, #0, motM η] : Ctx ζ 2 0 3)] ⊢ ok :=
  .snoc Γ2_wf ⟨_, motM_typed hq⟩

/-- `motive a (Eq.refl a) : Sort u` under `α a motive`. -/
theorem minM3_typed (hq : (E.get η).block = Eq.block) :
    E[(#t[.sort mu1, #0, motM η] : Ctx ζ 2 0 3)] ⊢ minM η (by omega) : .sort mu0 := by
  have hΓ := ΓM_wf (η := η) hq
  have hm : E[(#t[.sort mu1, #0, motM η] : Ctx ζ 2 0 3)] ⊢ #2 :
      .forallE #0 (.forallE (eqA η mu1 #0 #1 #3) (.sort mu0)) :=
    var_of_get hΓ ⟨2, by decide⟩ (by eqsimp [motM])
  have h1 := typed_of_eq (app_typed hm (var_of_get hΓ ⟨1, by decide⟩ (by eqsimp)))
    (T' := .forallE (eqA η mu1 #0 #1 #1) (.sort mu0)) (by eqsimp)
  exact typed_of_eq (app_typed h1 (reflA_typed hq (var_of_get hΓ ⟨0, by decide⟩ (by eqsimp))
    (var_of_get hΓ ⟨1, by decide⟩ (by eqsimp)))) (by eqsimp)

/-- `Eq.rec`'s binder context `α a motive refl a_1 t`. -/
def ΓR (η : Head ζ (.inductive Eq.sig)) : Ctx ζ 2 0 6 :=
  #t[.sort mu1, #0, motM η, minM η (by omega), #0, eqA η mu1 #0 #1 #4]

theorem ΓR_wf (hq : (E.get η).block = Eq.block) : E[ΓR η] ⊢ ok := by
  have h3 := ΓM_wf (η := η) hq
  have h4 : E[(#t[.sort mu1, #0, motM η, minM η (by omega)] : Ctx ζ 2 0 4)] ⊢ ok :=
    .snoc h3 ⟨_, minM3_typed hq⟩
  have h5 : E[(#t[.sort mu1, #0, motM η, minM η (by omega), #0] : Ctx ζ 2 0 5)] ⊢ ok :=
    .snoc h4 ⟨mu1, var_of_get h4 ⟨0, by decide⟩ (by eqsimp)⟩
  exact .snoc h5 ⟨_, eqA_typed hq (var_of_get h5 ⟨0, by decide⟩ (by eqsimp))
    (var_of_get h5 ⟨1, by decide⟩ (by eqsimp)) (var_of_get h5 ⟨4, by decide⟩ (by eqsimp))⟩

theorem eqRecTermM_typed (hq : (E.get η).block = Eq.block) :
    E[.nil] ⊢ eqRecTermM η : eqRecTyM η := by
  have hΓ := ΓR_wf (η := η) hq
  have hm : E[ΓR η] ⊢ #2 : .forallE #0 (.forallE (eqA η mu1 #0 #1 #6) (.sort mu0)) :=
    var_of_get hΓ ⟨2, by decide⟩ (by eqsimp [ΓR, motM])
  have hbody : E[ΓR η] ⊢ eqRecBody η : .app (.app #2 #4) #5 := by
    have h := Defeq.recrDF (E := E) (Γ := ΓR η) (η := η) (s := 0) (ls := ![mu1]) (l := mu0)
      (ps₁ := ![#0, #1]) (ps₂ := ![#0, #1]) (ms₁ := fun _ => #2) (ms₂ := fun _ => #2)
      (mins₁ := fun _ _ => #3) (mins₂ := fun _ _ => #3) (is₁ := ![#4]) (is₂ := ![#4])
      (maj₁ := #5) (maj₂ := #5) (by rw [hq]; exact eqBlock_subsingleton) ?_ ?_ ?_ ?_ ?_ ?_
    · exact h
    · intro p; fin_cases p <;> rw [hq]
      · exact var_of_get hΓ ⟨0, by decide⟩ (by eqsimp [ΓR])
      · exact var_of_get hΓ ⟨1, by decide⟩ (by eqsimp [ΓR])
    · intro t; fin_cases t; rw [hq]; exact typed_of_eq hm (by eqsimp)
    · intro t c; fin_cases t; fin_cases c; rw [hq]
      exact var_of_get hΓ ⟨3, by decide⟩ (by eqsimp [ΓR, minM])
    · intro i; fin_cases i; rw [hq]; exact var_of_get hΓ ⟨4, by decide⟩ (by eqsimp [ΓR])
    · exact var_of_get hΓ ⟨5, by decide⟩ (by eqsimp [ΓR])
    · have h1 := typed_of_eq (app_typed hm (var_of_get hΓ ⟨4, by decide⟩ (by eqsimp [ΓR])))
        (T' := .forallE (eqA η mu1 #0 #1 #4) (.sort mu0)) (by eqsimp)
      exact typed_of_eq (app_typed h1 (var_of_get hΓ ⟨5, by decide⟩ (by eqsimp [ΓR])))
        (by eqsimp)
  exact Ctx.lam_congr (Γ := .nil) (Δ := ΓR η) hΓ hbody

/-- `Eq.casesOn`'s type in Metalean. -/
def eqCasesOnTyM (η : Head ζ (.inductive Eq.sig)) : Expr ζ 2 0 :=
  .forallE (.sort mu1) (.forallE #0 (.forallE (motM η) (.forallE #0
    (.forallE (eqA η mu1 #0 #1 #3) (.forallE (minM η (by omega)) (.app (.app #2 #3) #4))))))

/-- The body of `Eq.casesOn`'s value. -/
def eqCasesOnBody (η : Head ζ (.inductive Eq.sig)) : Expr ζ 2 6 :=
  .recr η 0 ![mu1] mu0 ![#0, #1] (fun _ => #2) (fun _ _ => #5) ![#3] #4

/-- `Eq.casesOn`'s value in Metalean: the saturated recursor. -/
def eqCasesOnValM (η : Head ζ (.inductive Eq.sig)) : Expr ζ 2 0 :=
  .lam (.sort mu1) (.lam #0 (.lam (motM η) (.lam #0
    (.lam (eqA η mu1 #0 #1 #3) (.lam (minM η (by omega)) (eqCasesOnBody η))))))

/-- `Eq.casesOn`'s binder context without its minor: `α a motive a_1 t`. -/
def ΓC5 (η : Head ζ (.inductive Eq.sig)) : Ctx ζ 2 0 5 :=
  #t[.sort mu1, #0, motM η, #0, eqA η mu1 #0 #1 #3]

/-- `Eq.casesOn`'s binder context `α a motive a_1 t refl`. -/
def ΓCo (η : Head ζ (.inductive Eq.sig)) : Ctx ζ 2 0 6 := (ΓC5 η).snoc (minM η (by omega))

theorem ΓC5_wf (hq : (E.get η).block = Eq.block) : E[ΓC5 η] ⊢ ok := by
  have h3 := ΓM_wf (η := η) hq
  have h4 : E[(#t[.sort mu1, #0, motM η, #0] : Ctx ζ 2 0 4)] ⊢ ok :=
    .snoc h3 ⟨mu1, var_of_get h3 ⟨0, by decide⟩ (by eqsimp)⟩
  exact .snoc h4 ⟨_, eqA_typed hq (var_of_get h4 ⟨0, by decide⟩ (by eqsimp))
    (var_of_get h4 ⟨1, by decide⟩ (by eqsimp)) (var_of_get h4 ⟨3, by decide⟩ (by eqsimp))⟩

theorem minM5_typed (hq : (E.get η).block = Eq.block) :
    E[ΓC5 η] ⊢ minM η (by omega) : .sort mu0 := by
  have hΓ := ΓC5_wf (η := η) hq
  have hm : E[ΓC5 η] ⊢ #2 : .forallE #0 (.forallE (eqA η mu1 #0 #1 #5) (.sort mu0)) :=
    var_of_get hΓ ⟨2, by decide⟩ (by eqsimp [ΓC5, motM])
  have h1 := typed_of_eq (app_typed hm (var_of_get hΓ ⟨1, by decide⟩ (by eqsimp [ΓC5])))
    (T' := .forallE (eqA η mu1 #0 #1 #1) (.sort mu0)) (by eqsimp)
  exact typed_of_eq (app_typed h1 (reflA_typed hq (var_of_get hΓ ⟨0, by decide⟩
    (by eqsimp [ΓC5])) (var_of_get hΓ ⟨1, by decide⟩ (by eqsimp [ΓC5])))) (by eqsimp)

theorem ΓCo_wf (hq : (E.get η).block = Eq.block) : E[ΓCo η] ⊢ ok :=
  .snoc (ΓC5_wf hq) ⟨_, minM5_typed hq⟩

theorem eqCasesOnValM_typed (hq : (E.get η).block = Eq.block) :
    E[.nil] ⊢ eqCasesOnValM η : eqCasesOnTyM η := by
  have hΓ := ΓCo_wf (η := η) hq
  have hm : E[ΓCo η] ⊢ #2 : .forallE #0 (.forallE (eqA η mu1 #0 #1 #6) (.sort mu0)) :=
    var_of_get hΓ ⟨2, by decide⟩ (by eqsimp [ΓCo, ΓC5, motM])
  have hbody : E[ΓCo η] ⊢ eqCasesOnBody η : .app (.app #2 #3) #4 := by
    have h := Defeq.recrDF (E := E) (Γ := ΓCo η) (η := η) (s := 0) (ls := ![mu1]) (l := mu0)
      (ps₁ := ![#0, #1]) (ps₂ := ![#0, #1]) (ms₁ := fun _ => #2) (ms₂ := fun _ => #2)
      (mins₁ := fun _ _ => #5) (mins₂ := fun _ _ => #5) (is₁ := ![#3]) (is₂ := ![#3])
      (maj₁ := #4) (maj₂ := #4) (by rw [hq]; exact eqBlock_subsingleton) ?_ ?_ ?_ ?_ ?_ ?_
    · exact h
    · intro p; fin_cases p <;> rw [hq]
      · exact var_of_get hΓ ⟨0, by decide⟩ (by eqsimp [ΓCo, ΓC5])
      · exact var_of_get hΓ ⟨1, by decide⟩ (by eqsimp [ΓCo, ΓC5])
    · intro t; fin_cases t; rw [hq]; exact typed_of_eq hm (by eqsimp)
    · intro t c; fin_cases t; fin_cases c; rw [hq]
      exact var_of_get hΓ ⟨5, by decide⟩ (by eqsimp [ΓCo, ΓC5, minM])
    · intro i; fin_cases i; rw [hq]; exact var_of_get hΓ ⟨3, by decide⟩ (by eqsimp [ΓCo, ΓC5])
    · exact var_of_get hΓ ⟨4, by decide⟩ (by eqsimp [ΓCo, ΓC5])
    · have h1 := typed_of_eq (app_typed hm (var_of_get hΓ ⟨3, by decide⟩ (by eqsimp [ΓCo, ΓC5])))
        (T' := .forallE (eqA η mu1 #0 #1 #3) (.sort mu0)) (by eqsimp)
      exact typed_of_eq (app_typed h1 (var_of_get hΓ ⟨4, by decide⟩ (by eqsimp [ΓCo, ΓC5])))
        (by eqsimp)
  exact Ctx.lam_congr (Γ := .nil) (Δ := ΓCo η) hΓ hbody

theorem eqCasesOnTyM_isType (hq : (E.get η).block = Eq.block) : E[.nil] ⊢ eqCasesOnTyM η typ :=
  (eqCasesOnValM_typed hq).regular

end Rec

/-! ## The input, typed in any environment with `B`, `Eq` and `Eq.casesOn` -/

section Input
variable {ζ : Sigs} {E : Env ζ} {ηE : Head ζ (.inductive Eq.sig)} {ηB : Head ζ (.inductive bSig)}
  {ηC : Head ζ (.const .def 2)}

abbrev l1M : Level 0 := .succ .zero

/-- `fun x h => B → B`. -/
def motEn (ηE : Head ζ (.inductive Eq.sig)) (ηB : Head ζ (.inductive bSig)) {n : Nat} :
    Expr ζ 0 n :=
  .lam (mB ηB) (.lam (eqA ηE l1M (mB ηB) (mT ηB) (.var (Fin.last n))) (.forallE (mB ηB) (mB ηB)))

/-- `@Eq.refl B B.t`. -/
abbrev reflv (ηE : Head ζ (.inductive Eq.sig)) (ηB : Head ζ (.inductive bSig)) {n : Nat} :
    Expr ζ 0 n :=
  reflA ηE l1M (mB ηB) (mT ηB)

/-- `fun y => y`. -/
def idM (ηB : Head ζ (.inductive bSig)) {n : Nat} : Expr ζ 0 n := .lam (mB ηB) (.var (Fin.last n))

/-- `Eq.casesOn.{1,1}`'s level arguments. -/
def lsE : Fin 2 → Level 0 := ![l1M, l1M]

/-- `@Eq.casesOn.{1,1} B B.t (fun x h => B → B) B.t m (fun y => y)` in Metalean. -/
def tEm (ηE : Head ζ (.inductive Eq.sig)) (ηB : Head ζ (.inductive bSig))
    (ηC : Head ζ (.const .def 2)) (m : Expr ζ 0 0) : Expr ζ 0 0 :=
  .app (.app (.app (.app (.app (.app (.const ηC lsE) (mB ηB)) (mT ηB)) (motEn ηE ηB)) (mT ηB)) m)
    (idM ηB)

theorem imax_one : (Level.imax l1M l1M : Level 0) = l1M := Level.ext fun ν => by simp

theorem defeq_rhs_of_eq {n : Nat} {Γ : Ctx ζ 0 0 n} {a b b' T : Expr ζ 0 n}
    (h : E[Γ] ⊢ a ≡ b : T) (hb : b = b') : E[Γ] ⊢ a ≡ b' : T := hb ▸ h

theorem mT_typed (hb : (E.get ηB).block = bBlock) {n : Nat} {Γ : Ctx ζ 0 0 n} :
    E[Γ] ⊢ mT ηB : mB ηB := ctorB_typed hb

theorem mB_typed (hb : (E.get ηB).block = bBlock) {n : Nat} {Γ : Ctx ζ 0 0 n} :
    E[Γ] ⊢ mB ηB : .sort l1M := indB_typed hb

theorem BB_typed (hb : (E.get ηB).block = bBlock) {n : Nat} {Γ : Ctx ζ 0 0 n} :
    E[Γ] ⊢ .forallE (mB ηB) (mB ηB) : .sort l1M :=
  typed_of_eq' (.forallEDF (mB_typed hb) (mB_typed hb) (mB_typed hb)) imax_one

variable (hq : (E.get ηE).block = Eq.block) (hb : (E.get ηB).block = bBlock)
include hq hb

theorem motEn_typed :
    E[(.nil : Ctx ζ 0 0 0)] ⊢ motEn ηE ηB :
      .forallE (mB ηB) (.forallE (eqA ηE l1M (mB ηB) (mT ηB) #0) (.sort l1M)) := by
  have h1 : E[(#t[mB ηB] : Ctx ζ 0 0 1)] ⊢ ok := .snoc .nil ⟨_, indB_typed hb⟩
  have hEq : E[(#t[mB ηB] : Ctx ζ 0 0 1)] ⊢ eqA ηE l1M (mB ηB) (mT ηB) #0 : .prop :=
    eqA_typed hq (mB_typed hb) (mT_typed hb) (var_of_get h1 ⟨0, by decide⟩ (by nvsimp))
  exact .lamDF (mB_typed hb) (.forallEDF hEq .sortDF .sortDF) (.forallEDF hEq .sortDF .sortDF)
    (.lamDF hEq .sortDF .sortDF (BB_typed hb) (BB_typed hb))
    (.lamDF hEq .sortDF .sortDF (BB_typed hb) (BB_typed hb))

theorem reflv_typed {n : Nat} {Γ : Ctx ζ 0 0 n} :
    E[Γ] ⊢ reflv ηE ηB : eqA ηE l1M (mB ηB) (mT ηB) (mT ηB) :=
  reflA_typed hq (mB_typed hb) (mT_typed hb)

/-- `(fun x h => B → B) B.t (Eq.refl B.t) ≡ B → B`. -/
theorem conv_mot (hE : EnvWF E) :
    E[(.nil : Ctx ζ 0 0 0)] ⊢ .app (.app (motEn ηE ηB) (mT ηB)) (reflv ηE ηB) ≡
      .forallE (mB ηB) (mB ηB) : .sort l1M := by
  have h1 := typed_of_eq (app_typed (motEn_typed hq hb) (mT_typed hb))
    (T' := .forallE (eqA ηE l1M (mB ηB) (mT ηB) (mT ηB)) (.sort l1M)) (by eqsimp)
  have hty := typed_of_eq (app_typed h1 (reflv_typed hq hb)) (T' := .sort l1M) (by eqsimp)
  have h := WHRedS.defeq hE .nil (Relation.ReflTransGen.tail (Relation.ReflTransGen.single
    (WHRed.frame (K := .app (reflv ηE ηB)) WHRed.beta)) WHRed.beta) hty
  exact defeq_rhs_of_eq h (by eqsimp)

theorem idM_typed (hE : EnvWF E) :
    E[(.nil : Ctx ζ 0 0 0)] ⊢ idM ηB : .app (.app (motEn ηE ηB) (mT ηB)) (reflv ηE ηB) := by
  have h1 : E[(#t[mB ηB] : Ctx ζ 0 0 1)] ⊢ ok := .snoc .nil ⟨_, indB_typed hb⟩
  have hv := var_of_get h1 ⟨0, by decide⟩ (T := mB ηB) (by nvsimp)
  exact .defeqDF (conv_mot hq hb hE).symm
    (.lamDF (mB_typed hb) (mB_typed hb) (mB_typed hb) hv hv)

/-- The input is typed for any major premise `m : @Eq B B.t B.t`. -/
theorem tE_typed_of (hE : EnvWF E) (hc : (E.get ηC).constType = eqCasesOnTyM ηE) {m : Expr ζ 0 0}
    (hm : E[.nil] ⊢ m : eqA ηE l1M (mB ηB) (mT ηB) (mT ηB)) : ∃ T, E[.nil] ⊢ tEm ηE ηB ηC m : T := by
  have h0 : E[(.nil : Ctx ζ 0 0 0)] ⊢ .const ηC lsE :
      .forallE (.sort l1M) (.forallE #0 (.forallE (.forallE #0 (.forallE (eqA ηE l1M #0 #1 #2)
        (.sort l1M))) (.forallE #0 (.forallE (eqA ηE l1M #0 #1 #3)
          (.forallE (.app (.app #2 #1) (reflA ηE l1M #0 #1)) (.app (.app #2 #3) #4)))))) :=
    const_typed hE ηC lsE (by rw [hc]; eqsimp [eqCasesOnTyM, motM, minM, Expr.wkClosed, lsE])
  have h1 := typed_of_eq (app_typed h0 (mB_typed hb))
    (T' := .forallE (mB ηB) (.forallE (.forallE (mB ηB) (.forallE (eqA ηE l1M (mB ηB) #0 #1)
      (.sort l1M))) (.forallE (mB ηB) (.forallE (eqA ηE l1M (mB ηB) #0 #2)
        (.forallE (.app (.app #1 #0) (reflA ηE l1M (mB ηB) #0)) (.app (.app #1 #2) #3))))))
    (by eqsimp)
  have h2 := typed_of_eq (app_typed h1 (mT_typed hb))
    (T' := .forallE (.forallE (mB ηB) (.forallE (eqA ηE l1M (mB ηB) (mT ηB) #0) (.sort l1M)))
      (.forallE (mB ηB) (.forallE (eqA ηE l1M (mB ηB) (mT ηB) #1)
        (.forallE (.app (.app #0 (mT ηB)) (reflv ηE ηB)) (.app (.app #0 #1) #2)))))
    (by eqsimp)
  have h3 := typed_of_eq (app_typed h2 (motEn_typed hq hb))
    (T' := .forallE (mB ηB) (.forallE (eqA ηE l1M (mB ηB) (mT ηB) #0)
      (.forallE (.app (.app (motEn ηE ηB) (mT ηB)) (reflv ηE ηB)) (.app (.app (motEn ηE ηB) #0) #1))))
    (by eqsimp [motEn])
  have h4 := typed_of_eq (app_typed h3 (mT_typed hb))
    (T' := .forallE (eqA ηE l1M (mB ηB) (mT ηB) (mT ηB))
      (.forallE (.app (.app (motEn ηE ηB) (mT ηB)) (reflv ηE ηB))
        (.app (.app (motEn ηE ηB) (mT ηB)) #0)))
    (by eqsimp [motEn])
  have h5 := typed_of_eq (app_typed h4 hm)
    (T' := .forallE (.app (.app (motEn ηE ηB) (mT ηB)) (reflv ηE ηB))
      (.app (.app (motEn ηE ηB) (mT ηB)) m.wk))
    (by eqsimp [motEn])
  exact ⟨_, app_typed h5 (idM_typed hq hb hE)⟩

end Input

/-! ## The environments `EA = E1 + Eq`, `EB = EA + Eq.casesOn` -/

abbrev ζA : Sigs := ζ1.snoc (.inductive Eq.sig)
abbrev ζB : Sigs := ζA.snoc (.const .def 2)

abbrev ηEA : Head ζA (.inductive Eq.sig) := .here
abbrev ηEB : Head ζB (.inductive Eq.sig) := .there .here
abbrev ηBB : Head ζB (.inductive bSig) := .there (.there .here)
abbrev ηCB : Head ζB (.const .def 2) := .here

def EA : Env ζA := E1.snoc (.inductive Eq.block)
def EB : Env ζB := EA.snoc (.def (eqCasesOnTyM ηEA) (eqCasesOnValM ηEA))

theorem hqA : (EA.get ηEA).block = Eq.block := by simp! [EA, Env.get, Entry.block]
theorem hqB : (EB.get ηEB).block = Eq.block := by simp! [EB, EA, Env.get, Entry.block]
theorem hbB : (EB.get ηBB).block = bBlock := by simp! [EB, EA, E1, Env.get, Entry.block]

theorem wfA : EnvWF EA := .snoc wf1 (.inductive (Metalean.Eq.wf _))
theorem wfB : EnvWF EB := .snoc wfA (.def (eqCasesOnTyM_isType hqA) (eqCasesOnValM_typed hqA))

theorem hcB : (EB.get ηCB).constType = eqCasesOnTyM ηEB := by
  simp! [EB, Env.get, Entry.constType, eqCasesOnTyM, motM, minM, reflA, mMot, funext_iff,
    Fin.forall_fin_two, Fin.forall_fin_one]

/-! ## Name tables -/

def BA : Binds ζA := fun n =>
  if n = `Eq then some (.ind ηEA 0)
  else if n = `Eq.refl then some (.ctor ηEA 0 0 [])
  else if n = `Eq.rec then some (.recr ηEA 0 [[[]]])
  else Binds.wk B1 n

def BB : Binds ζB := (Binds.wk BA).set `Eq.casesOn (.const .here)

theorem BA_Eq : BA `Eq = some (.ind ηEA 0) := rfl
theorem BA_refl : BA `Eq.refl = some (.ctor ηEA 0 0 []) := rfl
theorem BA_rec : BA `Eq.rec = some (.recr ηEA 0 [[[]]]) := rfl
theorem BB_Eq : BB `Eq = some (.ind ηEB 0) := rfl
theorem BB_refl : BB `Eq.refl = some (.ctor ηEB 0 0 []) := rfl
theorem BB_B : BB `B = some (.ind ηBB 0) := rfl
theorem BB_t : BB `B.t = some (.ctor ηBB 0 1 []) := rfl
theorem BB_casesOn : BB `Eq.casesOn = some (.const ηCB) := rfl

theorem trLevels_one {lps : List Name} {u : Lean.Level} {l : Metalean.Level lps.length}
    (h : TrLevel lps u = some l) : TrLevels lps [u] 1 = some ![l] := by
  simp only [TrLevels, List.mapM_cons, List.mapM_nil, h]
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, List.length_singleton,
    ↓reduceDIte, Option.some.injEq]
  funext i; fin_cases i; rfl

theorem trLevels_two {lps : List Name} {u v : Lean.Level} {l m : Metalean.Level lps.length}
    (h : TrLevel lps u = some l) (h' : TrLevel lps v = some m) :
    TrLevels lps [u, v] 2 = some ![l, m] := by
  simp only [TrLevels, List.mapM_cons, List.mapM_nil, h, h']
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, List.length_cons,
    List.length_nil, ↓reduceDIte, Option.some.injEq]
  funext i; fin_cases i <;> rfl

/-! ## `Eq`'s block in `EA`/`BA` -/

theorem trLevel_pA : TrLevel [`u_1] (.param `u_1) = some pA := rfl
theorem trLevel_mu0 : TrLevel [`u, `u_1] (.param `u) = some mu0 := rfl
theorem trLevel_mu1 : TrLevel [`u, `u_1] (.param `u_1) = some mu1 := rfl

theorem tr_eqTy : TrM EA BA [`u_1] .nil [] Eq_ind.type (eqTyM ηEA) :=
  TrM.forallE (TrM.sort trLevel_pA) (TrM.forallE (TrM.bvar rfl) (TrM.forallE (TrM.bvar rfl)
    (TrM.sort rfl)))

theorem tr_eqConst : TrM EA BA [`u_1] .nil [] (.const `Eq [.param `u_1]) (eqIndTermM ηEA) := by
  have h : TrM EA BA [`u_1] .nil [] (.const `Eq [.param `u_1])
      (Frontend.indTerm (EA.get ηEA).block ηEA 0 ![pA]) :=
    TrM.special (as := []) (as' := []) BA_Eq rfl rfl (fun _ _ _ h => nomatch h)
      (SatTr.indEta (args := []) (η := ηEA) (s := 0) (trLevels_one trLevel_pA) (by decide))
  rwa [indTerm_eq hqA] at h

/-- `@Eq.{l} α a b`. -/
theorem tr_eqC {ζ : Sigs} {E : Env ζ} {B : Binds ζ} {lps : List Name} {n : Nat}
    {Γ : Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n} {η : Head ζ (.inductive Eq.sig)}
    {u : Lean.Level} {l : Metalean.Level lps.length} {α a b : Lean.Expr}
    {α' a' b' : Metalean.Expr ζ lps.length n}
    (hB : B `Eq = some (.ind η 0)) (hl : TrLevel lps u = some l)
    (hα : TrM E B lps Γ Δ α α') (ha : TrM E B lps Γ Δ a a') (hb : TrM E B lps Γ Δ b b') :
    TrM E B lps Γ Δ (mkAppN (.const `Eq [u]) #[α, a, b]) (eqA η l α' a' b') :=
  TrM.special (as := [α, a, b]) (as' := [α', a', b']) hB rfl rfl
    (by
      intro i x x' h1 h2
      rcases i with _ | _ | _ | i <;> simp at h1 h2 <;> subst h1 h2 <;> assumption)
    (SatTr.indSat (η := η) (s := 0) (ps := ![α', a']) (is := ![b']) (rest := [])
      (trLevels_one hl))

/-- `@Eq.refl.{l} α a`. -/
theorem tr_reflC {ζ : Sigs} {E : Env ζ} {B : Binds ζ} {lps : List Name} {n : Nat}
    {Γ : Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n} {η : Head ζ (.inductive Eq.sig)}
    {u : Lean.Level} {l : Metalean.Level lps.length} {α a : Lean.Expr}
    {α' a' : Metalean.Expr ζ lps.length n}
    (hB : B `Eq.refl = some (.ctor η 0 0 [])) (hl : TrLevel lps u = some l)
    (hα : TrM E B lps Γ Δ α α') (ha : TrM E B lps Γ Δ a a') :
    TrM E B lps Γ Δ (mkAppN (.const `Eq.refl [u]) #[α, a]) (reflA η l α' a') :=
  TrM.special (as := [α, a]) (as' := [α', a']) hB rfl rfl
    (by
      intro i x x' h1 h2
      rcases i with _ | _ | i <;> simp at h1 h2 <;> subst h1 h2 <;> assumption)
    (SatTr.ctorSat (η := η) (s := 0) (c := 0) (order := []) (ps := ![α', a']) (fs := [])
      (rest := []) (fds := Fin.elim0) (recFds := Fin.elim0) (trLevels_one hl) rfl rfl
      (fun o => Fin.elim0 o))

theorem tr_reflTy : TrM EA BA [`u_1] .nil [] Eq_refl.type (eqReflTyM ηEA) :=
  TrM.forallE (TrM.sort trLevel_pA) (TrM.forallE (TrM.bvar rfl)
    (tr_eqC BA_Eq trLevel_pA (TrM.bvar rfl) (TrM.bvar rfl) (TrM.bvar rfl)))

theorem tr_reflConst :
    TrM EA BA [`u_1] .nil [] (.const `Eq.refl [.param `u_1]) (eqReflTermM ηEA) :=
  TrM.special (as := []) (as' := []) BA_refl rfl rfl (fun _ _ _ h => nomatch h)
    (SatTr.ctorEta (args := []) (η := ηEA) (s := 0) (c := 0) (order := [])
      (trLevels_one trLevel_pA) (by decide) (ctorTerm_eq hqA))

theorem tr_motTy : TrM EA BA [`u, `u_1] (#t[.sort mu1, #0]) ((MLCtx.pushLam [] none).pushLam none)
    eqMotTy (motM ηEA) :=
  TrM.forallE (TrM.bvar rfl) (TrM.forallE (tr_eqC BA_Eq trLevel_mu1 (TrM.bvar rfl) (TrM.bvar rfl)
    (TrM.bvar rfl)) (TrM.sort trLevel_mu0))

theorem tr_recTy : TrM EA BA [`u, `u_1] .nil [] eqRecTy (eqRecTyM ηEA) :=
  TrM.forallE (TrM.sort trLevel_mu1) (TrM.forallE (TrM.bvar rfl) (TrM.forallE tr_motTy
    (TrM.forallE (TrM.app notSpecial_bvar (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl))
      (tr_reflC BA_refl trLevel_mu1 (TrM.bvar rfl) (TrM.bvar rfl)))
      (TrM.forallE (TrM.bvar rfl) (TrM.forallE
        (tr_eqC BA_Eq trLevel_mu1 (TrM.bvar rfl) (TrM.bvar rfl) (TrM.bvar rfl))
        (TrM.app notSpecial_bvar (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl))
          (TrM.bvar rfl)))))))

theorem largeElimEq {ζ : Sigs} : (Eq.block (ζ := ζ)).LargeElim :=
  fun _ => .subsingleton rfl (fun _ _ => Subsingleton.elim _ _)
    (fun _ => ⟨fun f => Fin.elim0 f, fun f => Fin.elim0 f⟩)

theorem tr_recConst :
    TrM EA BA [`u, `u_1] .nil [] (.const `Eq.rec [.param `u, .param `u_1]) (eqRecTermM ηEA) :=
  TrM.special (as := []) (as' := []) BA_rec rfl rfl (fun _ _ _ h => nomatch h)
    (SatTr.recrEta (E := EA) (lps := [`u, `u_1]) (args := []) (η := ηEA) (s := 0)
      (us := [.param `u, .param `u_1]) (us' := [.param `u_1]) (l := mu0)
      (fun _ _ => []) (Or.inl ⟨by rw [hqA]; exact largeElimEq, _, rfl, trLevel_mu0⟩)
      (trLevels_one trLevel_mu1) (by intro t c; fin_cases t; fin_cases c; rfl) (by decide)
      (recrTerm_eqRec hqA))

/-! ## `Eq.casesOn` in `EA`/`BA` -/

theorem tr_casesOnTy : TrM EA BA [`u, `u_1] .nil [] eqCasesOnTy (eqCasesOnTyM ηEA) :=
  TrM.forallE (TrM.sort trLevel_mu1) (TrM.forallE (TrM.bvar rfl) (TrM.forallE tr_motTy
    (TrM.forallE (TrM.bvar rfl) (TrM.forallE
      (tr_eqC BA_Eq trLevel_mu1 (TrM.bvar rfl) (TrM.bvar rfl) (TrM.bvar rfl))
      (TrM.forallE (TrM.app notSpecial_bvar (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl))
        (tr_reflC BA_refl trLevel_mu1 (TrM.bvar rfl) (TrM.bvar rfl)))
        (TrM.app notSpecial_bvar (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl))
          (TrM.bvar rfl)))))))

theorem tr_casesOnVal : TrM EA BA [`u, `u_1] .nil [] eqCasesOnVal (eqCasesOnValM ηEA) := by
  have h : TrM EA BA [`u, `u_1] .nil [] eqCasesOnVal _ :=
    TrM.lam (TrM.sort trLevel_mu1) (TrM.lam (TrM.bvar rfl) (TrM.lam tr_motTy
      (TrM.lam (TrM.bvar rfl) (TrM.lam
        (tr_eqC BA_Eq trLevel_mu1 (TrM.bvar rfl) (TrM.bvar rfl) (TrM.bvar rfl))
        (TrM.lam (TrM.app notSpecial_bvar (TrM.app notSpecial_bvar (TrM.bvar rfl) (TrM.bvar rfl))
          (tr_reflC BA_refl trLevel_mu1 (TrM.bvar rfl) (TrM.bvar rfl)))
          (TrM.special (c := `Eq.rec) (us := [.param `u, .param `u_1])
            (as := [.bvar 5, .bvar 4, .bvar 3, .bvar 0, .bvar 2, .bvar 1])
            (as' := [#0, #1, #2, #5, #3, #4]) BA_rec rfl rfl
            (by
              intro i a a' h1 h2
              rcases i with _ | _ | _ | _ | _ | _ | i <;> simp at h1 h2 <;> subst h1 h2 <;>
                exact TrM.bvar rfl)
            (SatTr.recrSat (E := EA) (lps := [`u, `u_1]) (η := ηEA) (s := 0)
              (us := [.param `u, .param `u_1]) (us' := [.param `u_1]) (ls := ![mu1]) (l := mu0)
              (fun _ _ => []) ![#0, #1, #2, #5, #3, #4] [] (fun _ _ => #5)
              (Or.inl ⟨by rw [hqA]; exact largeElimEq, _, rfl, trLevel_mu0⟩)
              (trLevels_one trLevel_mu1)
              (by intro t c; fin_cases t; fin_cases c; rfl)
              (by
                intro t c; fin_cases t; fin_cases c
                simp [Frontend.wrapCase, Frontend.isIdentityOrder]; rfl))))))))
  convert h using 1
  simp only [eqCasesOnValM, eqCasesOnBody]
  repeat' (first
    | (funext t; fin_cases t <;> rfl)
    | rfl
    | congr 1)

/-! ## `ProgEnv P ζB EB BB` -/

def IsE : Fin Eq.sig.nsorts → InductiveVal := fun _ => Eq_ind
def CsE : (s : Fin Eq.sig.nsorts) → Fin (Eq.sig.nctors s) → ConstructorVal := fun _ _ => Eq_refl
def RsE : Fin Eq.sig.nsorts → RecursorVal := fun _ => Eq_rec
def ordersE : (s : Fin Eq.sig.nsorts) → Fin (Eq.sig.nctors s) → List Nat := fun _ _ => []

theorem PE_eq : IndBlock.decls IsE CsE RsE =
    [.recInfo Eq_rec, .ctorInfo Eq_refl, .inductInfo Eq_ind] := rfl

theorem indBlockE : IndBlock EA BA ηEA [`u_1] IsE CsE RsE ordersE where
  levels := rfl
  ind s := by fin_cases s; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  ctor s c := by
    fin_cases s; fin_cases c
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, [], [], rfl, rfl, rfl, .nil, .nil, .nil⟩
  ctorType s c := by fin_cases s; fin_cases c; exact ⟨_, [.bvar 0], rfl, rfl, rfl⟩
  recr s := by
    fin_cases s
    exact ⟨rfl, rfl, fun _ => ⟨`u, rfl⟩, fun h => absurd (by rw [hqA]; exact largeElimEq) h, rfl, rfl,
      rfl, rfl, rfl, rfl⟩
  recrType s := by fin_cases s; rfl
  minors s t c := by fin_cases s; fin_cases t; fin_cases c; rfl
  recIHs s := by
    fin_cases s
    exact ⟨_, _, rfl, rfl, fun t c => by fin_cases t; fin_cases c <;> rfl⟩
  indexVars s c h := by obtain ⟨_, f, _⟩ := h; exact f.elim0

theorem constTypedE : ∀ ci ∈ IndBlock.decls IsE CsE RsE, ConstTyped EA BA ci := by
  rw [PE_eq]
  intro ci hci
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hci
  rcases hci with rfl | rfl | rfl
  · exact ⟨_, _, tr_recTy, tr_recConst, eqRecTermM_typed hqA⟩
  · exact ⟨_, _, tr_reflTy, tr_reflConst, eqReflTermM_typed hqA⟩
  · exact ⟨_, _, tr_eqTy, tr_eqConst, eqIndTermM_typed hqA⟩

theorem henvA : ProgEnv (IndBlock.decls IsE CsE RsE ++ P1) ζA EA BA :=
  ProgEnv.induct (I := Eq.block) (lps := [`u_1]) (orders := ordersE) henv1 (by decide)
    (by rw [PE_eq, P1_eq]; decide) (by decide)
    (fun n hn => by
      rw [PE_eq] at hn
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
        not_or] at hn
      obtain ⟨h1, h2, h3⟩ := hn
      have h1' : n ≠ `Eq.rec := h1
      have h2' : n ≠ `Eq.refl := h2
      have h3' : n ≠ `Eq := h3
      simp [BA, h1', h2', h3'])
    indBlockE constTypedE

/-! ## The input in `EB`/`BB` -/

theorem trLevel_l1 : TrLevel [] l1 = some l1M := rfl

theorem tr_motE {ζ : Sigs} {E : Env ζ} {B : Binds ζ} {ηE : Head ζ (.inductive Eq.sig)}
    {ηB : Head ζ (.inductive bSig)} (hE : B `Eq = some (.ind ηE 0)) (hB : B `B = some (.ind ηB 0))
    (ht : B `B.t = some (.ctor ηB 0 1 [])) :
    TrM E B [] .nil [] motE (motEn ηE ηB) :=
  TrM.lam (tr_B hB) (TrM.lam (tr_eqC hE trLevel_l1 (tr_B hB) (tr_T ht) (TrM.bvar rfl))
    (TrM.forallE (tr_B hB) (tr_B hB)))

/-- The input's spine `@Eq.casesOn.{1,1} B B.t (fun x h => B → B) B.t m (fun y => y)` translates
for any major `m` that does. -/
theorem tr_eOf {ζ : Sigs} {E : Env ζ} {B : Binds ζ} {ηE : Head ζ (.inductive Eq.sig)}
    {ηB : Head ζ (.inductive bSig)} {ηC : Head ζ (.const .def 2)} (hE : B `Eq = some (.ind ηE 0))
    (hB : B `B = some (.ind ηB 0)) (ht : B `B.t = some (.ctor ηB 0 1 []))
    (hC : B `Eq.casesOn = some (.const ηC)) {mj : Lean.Expr} {m : Metalean.Expr ζ 0 0}
    (hm : TrM E B [] .nil [] mj m) :
    TrM E B [] .nil []
      (.app (.app (.app (.app (.app (.app (.const `Eq.casesOn [l1, l1]) tB) cT) motE) cT) mj) idB)
      (tEm ηE ηB ηC m) :=
  TrM.app (notSpecial_const hC ⟨_, rfl⟩)
    (TrM.app (notSpecial_const hC ⟨_, rfl⟩)
      (TrM.app (notSpecial_const hC ⟨_, rfl⟩)
        (TrM.app (notSpecial_const hC ⟨_, rfl⟩)
          (TrM.app (notSpecial_const hC ⟨_, rfl⟩)
            (TrM.app (notSpecial_const hC ⟨_, rfl⟩)
              (TrM.const hC (trLevels_two trLevel_l1 trLevel_l1)) (tr_B hB))
            (tr_T ht))
          (tr_motE hE hB ht))
        (tr_T ht))
      hm)
    (TrM.lam (tr_B hB) (TrM.bvar rfl))

/-! ## The premises -/

/-- The erased term in Metalean. -/
def tE : Expr ζB 0 0 := tEm ηEB ηBB ηCB (reflv ηEB ηBB)

/-- `henv`: the program is the Lean form of `EB` with table `BB`. -/
theorem henv : ProgEnv P ζB EB BB :=
  ProgEnv.defn henvA (by decide) (by decide) rfl rfl tr_casesOnTy tr_casesOnVal

/-- `hwf`: `EB` is well formed. -/
theorem hwf : EnvWF EB := wfB

/-- `he`: the erased term is the Lean form of `tE`. -/
theorem he : TrM EB BB [] .nil [] e tE :=
  tr_eOf BB_Eq BB_B BB_t BB_casesOn (tr_reflC BB_refl trLevel_l1 (tr_B BB_B) (tr_T BB_t))

/-- `hty`: `tE` is typed. -/
theorem hty : ∃ T, EB[.nil] ⊢ tE : T :=
  tE_typed_of hqB hbB wfB hcB (reflv_typed hqB hbB)

end EraseProof.Test.NVP
