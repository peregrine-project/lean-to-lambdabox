import EraseProof.Bridge.Proj
import Mathlib.Tactic.FinCases

/-!
# Weakening along the environment

The translator's term builders commute with weakening along an environment extension, and so does
the bridge `TrM`: a translation stays a translation in an extended environment whose table agrees
with the old one, weakened, on the old names (`TrM.wkEnv`). Reference: `weakening_env`
(`MR P/PCUICWeakeningEnv.v`); `Defeq.map` (`ML Typing/Map.lean:22`).
-/

open Lean CategoryTheory

namespace EraseProof

/-- `Fin.mapM` in `Option` commutes with mapping the results. -/
theorem Fin.mapM_option_map {k : Nat} {α β : Fin k → Type} (f : (i : Fin k) → Option (α i))
    (g : (i : Fin k) → α i → β i) :
    (Fin.mapM (m := Option) (α := β) fun i => (f i).map (g i)) =
      (Fin.mapM (m := Option) (α := α) f).map fun h i => g i (h i) := by
  induction k with
  | zero => simp [Fin.mapM]; funext i; exact i.elim0
  | succ k ih =>
    simp only [Fin.mapM]
    rw [ih (α := fun i => α i.succ) (β := fun i => β i.succ) (fun i => f i.succ) fun i => g i.succ]
    cases f 0 <;> cases Fin.mapM (m := Option) (α := fun i => α i.succ) (fun i => f i.succ) <;>
      first
      | rfl
      | (show some _ = some _
         congr 1; funext i
         match i with
         | ⟨0, _⟩ => rfl
         | ⟨j + 1, _⟩ => rfl)

variable {ζ₁ ζ₂ : Metalean.Sigs}

/-- Partial renaming commutes with weakening along the environment. -/
theorem rename?_map (pre : ζ₁ ⟶ ζ₂) {ℓ m n : Nat} (e : Metalean.Expr ζ₁ ℓ m)
    (ρ : Fin m → Option (Fin n)) :
    (e.map pre).rename? ρ = (e.rename? ρ).map (·.map pre) := by
  induction e generalizing n with
  | var v => simp [Metalean.Expr.rename?]; cases ρ v <;> rfl
  | _ => simp [Metalean.Expr.rename?, Fin.mapM_option_map, Option.bind_map, Option.map_bind,
      Function.comp_def, *]

/-- One step of `Ctx.permuteAux?` (definitional). -/
theorem permuteAux?_succ_wk {ζ : Metalean.Sigs} {ℓ a b k : Nat} (hb : b = a + k)
    (π πinv : Fin k → Option (Fin k)) (Δ : Metalean.Ctx ζ ℓ a b) (j : Nat) (hj : j + 1 ≤ k) :
    Metalean.Ctx.permuteAux? hb π πinv Δ (j + 1) hj =
      (do
        let Γ ← Metalean.Ctx.permuteAux? hb π πinv Δ j (by omega)
        let o ← π ⟨j, by omega⟩
        let t := Δ.entry (p := a + o.val) (by omega) (by omega)
        let t' ← t.rename? (Metalean.Ctx.permuteMap? a j πinv o)
        some (Γ.snoc t')) :=
  rfl

/-- Permuting a telescope commutes with weakening along the environment. -/
theorem permuteAux?_map (pre : ζ₁ ⟶ ζ₂) {ℓ a b k : Nat} (hb : b = a + k)
    (π πinv : Fin k → Option (Fin k)) (Δ : Metalean.Ctx ζ₁ ℓ a b) (j : Nat) (hj : j ≤ k) :
    Metalean.Ctx.permuteAux? hb π πinv (Δ.map pre) j hj =
      (Metalean.Ctx.permuteAux? hb π πinv Δ j hj).map (·.map pre) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [permuteAux?_succ_wk, permuteAux?_succ_wk, ih (by omega)]
    rcases Metalean.Ctx.permuteAux? hb π πinv Δ j (by omega) with _ | Γ
    · rfl
    · simp [Option.bind_map, Option.map_bind, Function.comp_def, ← Metalean.Ctx.entry_map,
        rename?_map]

/-- `Ctx.permute?` commutes with weakening along the environment. -/
theorem permute?_map (pre : ζ₁ ⟶ ζ₂) {ℓ a b k : Nat} (hb : b = a + k)
    (π πinv : Fin k → Option (Fin k)) (Δ : Metalean.Ctx ζ₁ ℓ a b) :
    Metalean.Ctx.permute? hb π πinv (Δ.map pre) =
      (Metalean.Ctx.permute? hb π πinv Δ).map (·.map pre) :=
  permuteAux?_map pre hb π πinv Δ k le_rfl

open Metalean in
/-- `wrapCase` commutes with weakening along the environment. -/
theorem wrapCase_map (pre : ζ₁ ⟶ ζ₂) {ι : IndSig} {ℓ n : Nat} (I : Inductive ζ₁ ι)
    (η : Head ζ₁ (.inductive ι)) (ls : Fin ι.nlevels → Level ℓ) (ps : Fin ι.nparams → Expr ζ₁ ℓ n)
    (ms : Fin ι.nsorts → Expr ζ₁ ℓ n) (t : Fin ι.nsorts) (c : Fin (ι.nctors t)) (mo : List Nat)
    (minor : Expr ζ₁ ℓ n) {ps₂ : Fin ι.nparams → Expr ζ₂ ℓ n} {ms₂ : Fin ι.nsorts → Expr ζ₂ ℓ n}
    {minor₂ : Expr ζ₂ ℓ n} (hps : ps₂ = fun i => (ps i).map pre)
    (hms : ms₂ = fun i => (ms i).map pre) (hm : minor₂ = minor.map pre) :
    Frontend.wrapCase (I.map pre) (η.map pre) ls ps₂ ms₂ t c mo minor₂ =
      (Frontend.wrapCase I η ls ps ms t c mo minor).map (·.map pre) := by
  subst hps hms hm
  delta Frontend.wrapCase
  by_cases h : Frontend.isIdentityOrder mo ((ι.ctors t c).nfields + (ι.ctors t c).nrecFields) = true
  · rw [ite_eq_left h, ite_eq_left h]; rfl
  · rw [ite_eq_right h, ite_eq_right h]
    cases Frontend.orderMaps? mo ((ι.ctors t c).nfields + (ι.ctors t c).nrecFields) with
    | none => rfl
    | some pp =>
      obtain ⟨π, πi⟩ := pp
      dsimp only
      rw [Fin.mapM_option_map, Fin.mapM_option_map]
      cases Fin.mapM (m := Option) π with
      | none => rfl
      | some hπ =>
        show Except.ok _ = Except.ok _
        congr 1
        simp only [Ctx.map_lam, Inductive.caseTele_map, Expr.map_apps, Expr.map_wkN]
        congr 2
        funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

open Metalean in
/-- `indTerm` commutes with weakening along the environment. -/
theorem indTerm_map (pre : ζ₁ ⟶ ζ₂) {ι : IndSig} {ℓ : Nat} (I : Inductive ζ₁ ι)
    (η : Head ζ₁ (.inductive ι)) (s : Fin ι.nsorts) (ls : Fin ι.nlevels → Level ℓ) :
    (Frontend.indTerm I η s ls).map pre = Frontend.indTerm (I.map pre) (η.map pre) s ls := by
  delta Frontend.indTerm
  simp [Inductive.argTele, Inductive.map]

open Metalean in
/-- `quotTerm` commutes with weakening along the environment. -/
theorem quotTerm_map (pre : ζ₁ ⟶ ζ₂) {ℓ : Nat} (η : Head ζ₁ .quot)
    (ηEq : Head ζ₁ (.inductive Eq.sig)) (kind : Export.QuotKind) (ls : List (Level ℓ)) :
    Frontend.quotTerm (η.map pre) (ηEq.map pre) kind ls =
      (Frontend.quotTerm η ηEq kind ls).map (·.map pre) := by
  delta Frontend.quotTerm
  rcases kind with _ | _ | _ | _ <;> rcases ls with _ | ⟨u, _ | ⟨v, _ | ⟨w, ls⟩⟩⟩ <;>
    first
    | rfl
    | (show Except.ok _ = Except.ok _
       congr 1
       simp [Fin.last, Fin.castSucc, Fin.castAdd, Fin.castLE]
       exact ⟨funext fun i => by fin_cases i <;> rfl, funext fun i => by fin_cases i; rfl⟩)

/-- A bind into `some` is a map. -/
theorem option_bind_some {α β : Type} (o : Option α) (f : α → β) :
    (o >>= fun a => some (f a)) = o.map f := by
  cases o <;> rfl

/-- The field variables of `ctorTerm`, as a map of the field order's inverse. -/
theorem fieldVars_eq {ζ : Metalean.Sigs} {ℓ m k p : Nat} (πi : Fin k → Option (Fin k))
    (g : Fin m → Fin k) :
    (Fin.mapM (m := Option) fun f => do
      let j ← πi (g f)
      some (Metalean.Expr.var ⟨p + j.val, Nat.add_lt_add_left j.isLt p⟩ :
        Metalean.Expr ζ ℓ (p + k))) =
      (Fin.mapM (m := Option) fun f => πi (g f)).map
        fun h f => Metalean.Expr.var ⟨p + (h f).val, Nat.add_lt_add_left (h f).isLt p⟩ := by
  simp only [option_bind_some, Fin.mapM_option_map]

open Metalean in
/-- `ctorTerm` commutes with weakening along the environment. -/
theorem ctorTerm_map (pre : ζ₁ ⟶ ζ₂) {ι : IndSig} {ℓ : Nat} (I : Inductive ζ₁ ι)
    (η : Head ζ₁ (.inductive ι)) (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (ls : Fin ι.nlevels → Level ℓ) (mo : List Nat) :
    Frontend.ctorTerm (I.map pre) (η.map pre) s c ls mo =
      (Frontend.ctorTerm I η s c ls mo).map (·.map pre) := by
  delta Frontend.ctorTerm
  dsimp only
  cases Frontend.orderMaps? mo ((ι.ctors s c).nfields + (ι.ctors s c).nrecFields) with
  | none => rfl
  | some pp =>
    obtain ⟨π, πi⟩ := pp
    have hf : ((I.map pre).ctors s c).fieldTele (η.map pre) ls (fun p => Expr.var p) =
        ((I.ctors s c).fieldTele η ls (fun p => Expr.var p)).map pre := by
      rw [Ctor.fieldTele_map]; rfl
    dsimp only
    rw [hf, permute?_map]
    cases Ctx.permute? _ π πi ((I.ctors s c).fieldTele η ls (fun p => Expr.var p)) with
    | none => rfl
    | some f' =>
      dsimp only
      rw [fieldVars_eq, fieldVars_eq, fieldVars_eq, fieldVars_eq]
      cases Fin.mapM (m := Option) fun f => πi (Fin.castAdd (ι.ctors s c).nrecFields f) with
      | none => rfl
      | some h1 =>
        cases Fin.mapM (m := Option) fun r => πi (Fin.natAdd (ι.ctors s c).nfields r) with
        | none => rfl
        | some h2 =>
          show Except.ok _ = Except.ok _
          congr 1
          simp [Inductive.map]

open Metalean in
/-- `leanCaseType` commutes with weakening along the environment. -/
theorem leanCaseType_map (pre : ζ₁ ⟶ ζ₂) {ι : IndSig} {ℓ n : Nat} (I : Inductive ζ₁ ι)
    (η : Head ζ₁ (.inductive ι)) (ls : Fin ι.nlevels → Level ℓ) (ps : Fin ι.nparams → Expr ζ₁ ℓ n)
    (ms : Fin ι.nsorts → Expr ζ₁ ℓ n) (t : Fin ι.nsorts) (c : Fin (ι.nctors t)) (mo : List Nat)
    {ps₂ : Fin ι.nparams → Expr ζ₂ ℓ n} {ms₂ : Fin ι.nsorts → Expr ζ₂ ℓ n}
    (hps : ps₂ = fun i => (ps i).map pre) (hms : ms₂ = fun i => (ms i).map pre) :
    Frontend.leanCaseType (I.map pre) (η.map pre) ls ps₂ ms₂ t c mo =
      (Frontend.leanCaseType I η ls ps ms t c mo).map (·.map pre) := by
  subst hps hms
  delta Frontend.leanCaseType
  dsimp only
  cases Frontend.orderMaps? mo ((ι.ctors t c).nfields + (ι.ctors t c).nrecFields) with
  | none => rfl
  | some pp =>
    obtain ⟨π, πi⟩ := pp
    dsimp only
    rw [← Inductive.caseTele_map, permute?_map]
    cases Ctx.permute? _ _ _ (I.caseTele η ls ps ms t c) with
    | none => rfl
    | some tele =>
      dsimp only
      rw [← Inductive.caseType_map, rename?_map]
      cases Expr.rename? _ (I.caseType η ls ps ms t c) with
      | none => rfl
      | some concl =>
        show Except.ok _ = Except.ok _
        simp

open Metalean in
/-- One step of `leanCaseBinders` (definitional). -/
theorem leanCaseBinders_succ_wk {ζ : Sigs} {ι : IndSig} {ℓ : Nat} (I : Inductive ζ ι)
    (η : Head ζ (.inductive ι)) (ls : Fin ι.nlevels → Level ℓ)
    (mos : (t : Fin ι.nsorts) → Fin (ι.nctors t) → List Nat) (k : Nat)
    (h : k + 1 ≤ Fin.sum ι.nctors) :
    Frontend.leanCaseBinders I η ls mos (k + 1) h =
      (do
        let Γ ← Frontend.leanCaseBinders I η ls mos k (by omega)
        let ty ← Frontend.leanCaseType I η ls
          (fun param => Expr.var (param.castLE (by omega)))
          (fun t => Expr.var ⟨ι.nparams + t.val, by omega⟩)
          (Fin.decodeSigma ι.nctors ⟨k, by omega⟩).1 (Fin.decodeSigma ι.nctors ⟨k, by omega⟩).2
          (mos (Fin.decodeSigma ι.nctors ⟨k, by omega⟩).1 (Fin.decodeSigma ι.nctors ⟨k, by omega⟩).2)
        pure (Γ.snoc ty)) :=
  rfl

open Metalean in
/-- `leanCaseBinders` commutes with weakening along the environment. -/
theorem leanCaseBinders_map (pre : ζ₁ ⟶ ζ₂) {ι : IndSig} {ℓ : Nat} (I : Inductive ζ₁ ι)
    (η : Head ζ₁ (.inductive ι)) (ls : Fin ι.nlevels → Level ℓ)
    (mos : (t : Fin ι.nsorts) → Fin (ι.nctors t) → List Nat) (k : Nat)
    (h : k ≤ Fin.sum ι.nctors) :
    Frontend.leanCaseBinders (I.map pre) (η.map pre) ls mos k h =
      (Frontend.leanCaseBinders I η ls mos k h).map (·.map pre) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [leanCaseBinders_succ_wk, leanCaseBinders_succ_wk, ih (by omega)]
    rcases Frontend.leanCaseBinders I η ls mos k (by omega) with e | Γ
    · rfl
    · show (Frontend.leanCaseType _ _ _ _ _ _ _ _ >>= _) =
        Except.map _ (Frontend.leanCaseType _ _ _ _ _ _ _ _ >>= _)
      rw [leanCaseType_map pre I η ls (fun param => Expr.var (param.castLE (by omega)))
        (fun t => Expr.var ⟨ι.nparams + t.val, by omega⟩) _ _ _
        (ps₂ := fun param => Expr.var (param.castLE (by omega)))
        (ms₂ := fun t => Expr.var ⟨ι.nparams + t.val, by omega⟩) rfl rfl]
      rcases Frontend.leanCaseType I η ls _ _ _ _ _ with e | ty <;> rfl

/-- `Except.toOption` commutes with `Except.map`. -/
theorem except_toOption_map {ε α β : Type} (x : Except ε α) (f : α → β) :
    (x.map f).toOption = x.toOption.map f := by
  cases x <;> rfl

open Metalean in
/-- `recrTerm` commutes with weakening along the environment. -/
theorem recrTerm_map (pre : ζ₁ ⟶ ζ₂) {ι : IndSig} {ℓ : Nat} (I : Inductive ζ₁ ι)
    (η : Head ζ₁ (.inductive ι)) (s : Fin ι.nsorts) (ls : Fin ι.nlevels → Level ℓ) (l : Level ℓ)
    (mos : (t : Fin ι.nsorts) → Fin (ι.nctors t) → List Nat) :
    Frontend.recrTerm (I.map pre) (η.map pre) s ls l mos =
      (Frontend.recrTerm I η s ls l mos).map (·.map pre) := by
  delta Frontend.recrTerm
  dsimp only
  rw [leanCaseBinders_map]
  rcases Frontend.leanCaseBinders I η ls mos (Fin.sum ι.nctors) le_rfl with e | cs
  · rfl
  · have hw : ∀ t c, Frontend.wrapCase (I.map pre) (η.map pre) ls
        (fun p => Expr.var (IndSig.RecrBinder.param (s := s) p).resolve)
        (fun t => Expr.var (IndSig.RecrBinder.motive (s := s) t).resolve) t c (mos t c)
        (Expr.var (IndSig.RecrBinder.case (s := s) t c).resolve) =
        (Frontend.wrapCase I η ls
          (fun p => Expr.var (IndSig.RecrBinder.param (s := s) p).resolve)
          (fun t => Expr.var (IndSig.RecrBinder.motive (s := s) t).resolve) t c (mos t c)
          (Expr.var (IndSig.RecrBinder.case (s := s) t c).resolve)).map (·.map pre) :=
      fun t c => wrapCase_map pre I η ls _ _ t c (mos t c) _ rfl rfl rfl
    have hm : (Fin.mapM (m := Option) fun t => Fin.mapM (m := Option) fun c =>
        (Frontend.wrapCase (I.map pre) (η.map pre) ls
          (fun p => Expr.var (IndSig.RecrBinder.param (s := s) p).resolve)
          (fun t => Expr.var (IndSig.RecrBinder.motive (s := s) t).resolve) t c (mos t c)
          (Expr.var (IndSig.RecrBinder.case (s := s) t c).resolve)).toOption) =
        (Fin.mapM (m := Option) fun t => Fin.mapM (m := Option) fun c =>
          (Frontend.wrapCase I η ls
            (fun p => Expr.var (IndSig.RecrBinder.param (s := s) p).resolve)
            (fun t => Expr.var (IndSig.RecrBinder.motive (s := s) t).resolve) t c (mos t c)
            (Expr.var (IndSig.RecrBinder.case (s := s) t c).resolve)).toOption).map
          fun h t c => (h t c).map pre := by
      simp only [hw, except_toOption_map, Fin.mapM_option_map]
    rw [hm]
    rcases Fin.mapM (m := Option) (fun t => Fin.mapM (m := Option) fun c =>
      (Frontend.wrapCase I η ls
          (fun p => Expr.var (IndSig.RecrBinder.param (s := s) p).resolve)
          (fun t => Expr.var (IndSig.RecrBinder.motive (s := s) t).resolve) t c (mos t c)
          (Expr.var (IndSig.RecrBinder.case (s := s) t c).resolve)).toOption) with _ | mins
    · rfl
    · show Except.ok _ = Except.ok _
      congr 1
      simp [Inductive.map]

open Metalean in
/-- The unary Nat literal commutes with weakening along the environment. -/
theorem natLitM_map (pre : ζ₁ ⟶ ζ₂) {ℓ n : Nat} (ηNat : Head ζ₁ (.inductive natSig)) (k : Nat) :
    (natLitM (ℓ := ℓ) (n := n) ηNat k).map pre = natLitM (ηNat.map pre) k := by
  induction k with
  | zero => simp [natLitM]; funext i; exact i.elim0
  | succ k ih =>
    simp [natLitM, ih]
    exact ⟨funext fun i => i.elim0, funext fun i => by fin_cases i; rfl⟩

open Metalean in
/-- The proof projection commutes with weakening along the environment. -/
theorem projProofTerm_map (pre : ζ₁ ⟶ ζ₂) {E₁ : Env ζ₁} {E₂ : Env ζ₂} {ι : IndSig}
    (η : Head ζ₁ (.inductive ι)) (hblk : (E₂.get (η.map pre)).block = (E₁.get η).block.map pre)
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) {ℓ : Nat} (ls : Fin ι.nlevels → Level ℓ)
    (hi : ι.nindices s = 0) (f : Nat) {n : Nat} (ps : Fin ι.nparams → Expr ζ₁ ℓ n)
    (maj : Expr ζ₁ ℓ n) :
    (projProofTerm E₁ η s c ls hi ps f maj).map pre =
      projProofTerm E₂ (η.map pre) s c ls hi (fun i => (ps i).map pre) f (maj.map pre) := by
  induction f using Nat.strong_induction_on generalizing n with
  | _ f ih =>
    have hfds : ∀ j : Fin (ι.ctors s c).nfields,
        (if j.val < f then projProofTerm E₁ η s c ls hi (fun p => (ps p).wkN (ι.nindices s + 1)) j
            (Expr.var (Fin.last (n + ι.nindices s))) else Expr.prop).map pre =
          if j.val < f then projProofTerm E₂ (η.map pre) s c ls hi
            (fun p => ((ps p).map pre).wkN (ι.nindices s + 1)) j
            (Expr.var (Fin.last (n + ι.nindices s))) else Expr.prop := by
      intro j
      split_ifs with hj
      · rw [ih j hj]; simp
      · rfl
    rw [projProofTerm, projProofTerm]
    by_cases hf : f < (ι.ctors s c).nfields
    · simp [hblk, hf, Ctor.ordinaryFieldExpr_map, hfds, apply_dite, Inductive.map, Expr.prop]
      funext i; exact absurd i.isLt (by omega)
    · simp [hblk, hf, apply_dite, Inductive.map, Expr.prop]
      funext i; exact absurd i.isLt (by omega)

/-! ## The bridge under one new entry -/

/-- The weakening of signatures along one new entry. -/
abbrev wkS {ζ : Metalean.Sigs} {sig : Metalean.Sig} : ζ ⟶ ζ.snoc sig :=
  Metalean.Sigs.Prefix.step Metalean.Sigs.Prefix.refl

/-- The environment prefix of one new entry. -/
abbrev envS {ζ : Metalean.Sigs} {sig : Metalean.Sig} (E : Metalean.Env ζ) (ent : Metalean.Entry ζ sig) :
    E.as ⟶ (E.snoc ent).as :=
  Metalean.Env.Prefix.step Metalean.Env.Prefix.refl

/-- A local's denotation, weakened along the environment. -/
def MLDecl.map {ζ ζ' : Metalean.Sigs} (pre : ζ ⟶ ζ') {ℓ n : Nat} : MLDecl ζ ℓ n → MLDecl ζ' ℓ n
  | .vlam v => .vlam v
  | .vlet e => .vlet (e.map pre)

/-- The locals, weakened along the environment. -/
def MLCtx.envMap {ζ ζ' : Metalean.Sigs} (pre : ζ ⟶ ζ') {ℓ n : Nat} (Δ : MLCtx ζ ℓ n) :
    MLCtx ζ' ℓ n :=
  List.map (fun (p : Option FVarId × MLDecl ζ ℓ n) => (p.1, p.2.map pre)) Δ

section Locals
variable {ζ ζ' : Metalean.Sigs} (pre : ζ ⟶ ζ') {ℓ n : Nat}

/-- A local's denotation commutes with weakening along the environment. -/
theorem MLDecl.denote_map (d : MLDecl ζ ℓ n) : (d.map pre).denote = d.denote.map pre := by
  cases d <;> rfl

/-- Looking up a bound variable commutes with weakening along the environment. -/
theorem MLCtx.findB_envMap (Δ : MLCtx ζ ℓ n) (i : Nat) :
    (MLCtx.envMap pre Δ).findB i = (Δ.findB i).map (·.map pre) := by
  induction Δ generalizing i with
  | nil => rfl
  | cons hd Δ ih =>
    obtain ⟨x, d⟩ := hd
    cases x <;> cases i <;> simp only [MLCtx.envMap, List.map_cons, MLCtx.findB] at * <;>
      first | exact ih _ | simp [MLDecl.denote_map]

/-- Looking up a free variable commutes with weakening along the environment. -/
theorem MLCtx.findF_envMap (Δ : MLCtx ζ ℓ n) (y : FVarId) :
    (MLCtx.envMap pre Δ).findF y = (Δ.findF y).map (·.map pre) := by
  induction Δ with
  | nil => rfl
  | cons hd Δ ih =>
    obtain ⟨x, d⟩ := hd
    cases x with
    | none => exact ih
    | some x =>
      simp only [MLCtx.envMap, List.map_cons, MLCtx.findF] at *
      split
      · simp [MLDecl.denote_map]
      · exact ih

/-- Entering a binder commutes with weakening along the environment. -/
theorem MLCtx.pushLam_envMap (Δ : MLCtx ζ ℓ n) (x : Option FVarId) :
    MLCtx.envMap pre (Δ.pushLam x) = (MLCtx.envMap pre Δ).pushLam x := by
  simp only [MLCtx.pushLam, MLCtx.envMap, List.map_cons, List.map_map]
  congr 2
  funext ⟨y, d⟩
  cases d <;> simp [MLDecl.map, MLDecl.wk]

end Locals

section OneEntry
open Metalean (Sigs Sig Env Entry Head)
variable {ζ : Sigs} {sig : Sig} {E : Env ζ} {ent : Entry ζ sig}

/-- A block after one new entry. -/
theorem get_there_block {ι : Metalean.IndSig} (η : Head ζ (.inductive ι)) :
    ((E.snoc ent).get (η.map wkS)).block = (E.get η).block.map wkS :=
  Metalean.Entry.block_map _ _

/-- The `Eq` head of a quotient entry after one new entry. -/
theorem get_there_eqHead (η : Head ζ .quot) :
    ((E.snoc ent).get (η.map wkS)).eqHead = (E.get η).eqHead.map wkS := by
  show ((E.get η).map wkS).eqHead = _
  generalize E.get η = x
  cases x; rfl

/-- Weakening a binding keeps whether it saturates. -/
theorem MBinding.wk_isSpecial (b : MBinding ζ) : (b.wk (sig := sig)).isSpecial = b.isSpecial := by
  cases b <;> rfl

/-- `Fin.append` of mapped tuples. -/
theorem Fin.append_map {α β : Type} {a b : Nat} (u : Fin a → α) (v : Fin b → α) (g : α → β)
    (o : Fin (a + b)) : Fin.append (fun i => g (u i)) (fun i => g (v i)) o = g (Fin.append u v o) := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) o <;> simp

/-- Rewrite the arguments and the result of a saturation. -/
theorem SatTr.cast {lps : List Name} {n : Nat} {b : MBinding ζ} {us : List Level}
    {as as' : List (Metalean.Expr ζ lps.length n)} {t t' : Metalean.Expr ζ lps.length n}
    (h : SatTr E lps b us as t) (h1 : as = as') (h2 : t = t') : SatTr E lps b us as' t' :=
  h1 ▸ h2 ▸ h

/-- The recursor levels of a block after one new entry. -/
theorem recrLevels_wk {ι : Metalean.IndSig} (η : Head ζ (.inductive ι)) {lps : List Name}
    {us us' : List Level} {l : Metalean.Level lps.length}
    (h : RecrLevels (E.get η).block lps us l us') :
    RecrLevels ((E.snoc ent).get (η.map wkS)).block lps us l us' := by
  rw [get_there_block]
  unfold RecrLevels at *
  simpa only [Metalean.Inductive.largeElim_map] using h

/-- The saturation of a binding stays a saturation after one new entry. -/
theorem SatTr.wkEnv {lps : List Name} {n : Nat} {b : MBinding ζ} {us : List Level}
    {as : List (Metalean.Expr ζ lps.length n)} {t : Metalean.Expr ζ lps.length n}
    (h : SatTr E lps b us as t) :
    SatTr (E.snoc ent) lps b.wk us (as.map (·.map wkS)) (t.map wkS) := by
  cases h with
  | @indSat us ι η s ls ps is rest hls =>
    refine SatTr.cast (SatTr.indSat (E := E.snoc ent) (η := η.map wkS) (fun i => (ps i).map wkS)
      (fun i => (is i).map wkS) (rest.map (·.map wkS)) hls) ?_ ?_ <;>
      simp [List.map_ofFn, Function.comp_def]
  | @indEta us args ι η s ls hls hlt =>
    refine SatTr.cast (SatTr.indEta (E := E.snoc ent) (η := η.map wkS) (args := List.map (·.map wkS) as)
      hls (by simpa using hlt)) rfl ?_
    simp [get_there_block, indTerm_map]
  | @ctorSat us order ι η s c ls ps fs rest fds recFds hls hfs hord hperm =>
    refine SatTr.cast (SatTr.ctorSat (E := E.snoc ent) (η := η.map wkS) (order := order)
      (fun i => (ps i).map wkS) (fs.map (·.map wkS))
      (rest.map (·.map wkS)) (fun i => (fds i).map wkS) (fun i => (recFds i).map wkS) hls
      (by simpa using hfs) hord (fun o => ?_)) ?_ ?_
    · obtain ⟨j, a, h1, h2, h3⟩ := hperm o
      exact ⟨j, a.map wkS, h1, by simp [h2], by rw [Fin.append_map, h3]⟩
    · simp [List.map_ofFn, Function.comp_def]
    · simp
  | @ctorEta us order args ι η s c ls t₀ hls hlt hct =>
    have hct' : Metalean.Frontend.ctorTerm ((E.snoc ent).get (η.map wkS)).block (η.map wkS) s c ls order =
        .ok (t₀.map wkS) := by
      rw [get_there_block, ctorTerm_map, hct]; rfl
    refine SatTr.cast (SatTr.ctorEta (E := E.snoc ent) (args := List.map (·.map wkS) as) hls
      (by simpa using hlt) hct') rfl ?_
    simp
  | @recrSat us us' orders ι η s ls l mo A rest mins hlv hls hmo hw =>
    have hw' : ∀ t c, Metalean.Frontend.wrapCase ((E.snoc ent).get (η.map wkS)).block (η.map wkS) ls
        (fun p => (A (Metalean.IndSig.RecrBinder.param (s := s) p).resolve).map wkS)
        (fun t => (A (Metalean.IndSig.RecrBinder.motive (s := s) t).resolve).map wkS) t c (mo t c)
        ((A (Metalean.IndSig.RecrBinder.case (s := s) t c).resolve).map wkS) =
        .ok ((mins t c).map wkS) := by
      intro t c
      rw [get_there_block, wrapCase_map wkS _ η ls _ _ t c (mo t c) _ rfl rfl rfl, hw]; rfl
    refine SatTr.cast (SatTr.recrSat (E := E.snoc ent) (η := η.map wkS) (orders := orders) mo
      (fun i => (A i).map wkS) (rest.map (·.map wkS)) (fun t c => (mins t c).map wkS)
      (recrLevels_wk η hlv) hls hmo hw') ?_ ?_
    · simp [List.map_ofFn, Function.comp_def]
    · simp
  | @recrEta us us' orders args ι η s ls l mo t₀ hlv hls hmo hlt hrt =>
    have hrt' : Metalean.Frontend.recrTerm ((E.snoc ent).get (η.map wkS)).block (η.map wkS) s ls l mo =
        .ok (t₀.map wkS) := by
      rw [get_there_block, recrTerm_map, hrt]; rfl
    refine SatTr.cast (SatTr.recrEta (E := E.snoc ent) (orders := orders)
      (args := List.map (·.map wkS) as) mo (recrLevels_wk η hlv) hls hmo (by simpa using hlt) hrt')
      rfl ?_
    simp
  | quotType hu =>
    exact SatTr.cast (SatTr.quotType (E := E.snoc ent) hu) (by simp; exact ⟨rfl, rfl, rfl⟩)
      (by simp; rfl)
  | quotMk hu =>
    exact SatTr.cast (SatTr.quotMk (E := E.snoc ent) hu) (by simp; exact ⟨rfl, rfl, rfl, rfl⟩)
      (by simp; rfl)
  | quotLift hu =>
    exact SatTr.cast (SatTr.quotLift (E := E.snoc ent) hu)
      (by simp; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) (by simp; rfl)
  | quotInd hu =>
    exact SatTr.cast (SatTr.quotInd (E := E.snoc ent) hu)
      (by simp; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) (by simp; rfl)
  | @quotEta kind us args η ls' t₀ hu hlt hq =>
    have hq' : Metalean.Frontend.quotTerm (η.map wkS) ((E.snoc ent).get (η.map wkS)).eqHead kind ls' =
        .ok (t₀.map wkS) := by
      rw [get_there_eqHead]
      exact (quotTerm_map wkS η _ _ ls').trans (by rw [hq]; rfl)
    refine SatTr.cast (SatTr.quotEta (E := E.snoc ent) (args := List.map (·.map wkS) as) hu
      (by simpa using hlt) hq') rfl ?_
    simp

/-- The head constant of a translated application is bound in the table. -/
theorem TrM.head_bound {B : Binds ζ} {lps : List Name} {n : Nat}
    {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n} {e : Expr}
    {t : Metalean.Expr ζ lps.length n} (h : TrM E B lps Γ Δ e t) {c : Name} {us : List Level}
    (hc : e.getAppFn = .const c us) : ∃ b, B c = some b := by
  induction h with
  | const hb => cases hc; exact ⟨_, hb⟩
  | @special c' us' _ _ _ as _ b _ hb =>
    rw [mkAppN_eq_foldl, foldl_app_getAppFn] at hc
    cases hc
    exact ⟨b, hb⟩
  | app _ _ _ ih _ => exact ih hc
  | _ => cases hc

/-- `TypedExt` is stable under one new entry (the extension mapped too). -/
theorem WkEnvExt.TypedExt.wkEnv {lps : List Name} {n : Nat}
    {Γ : Metalean.Ctx ζ lps.length 0 n} {e T : Metalean.Expr ζ lps.length n}
    (h : TypedExt E Γ e T) :
    TypedExt (E.snoc ent) (Γ.map wkS) (e.map wkS) (T.map wkS) := by
  obtain ⟨m, Γ', ρ, hρ, hget, hty⟩ := h
  refine ⟨m, Γ'.map wkS, ρ, hρ, fun v => ?_, ?_⟩
  · rw [Metalean.Ctx.get_map, Metalean.Ctx.get_map, hget, Metalean.Expr.map_rename]
  · have h' := Metalean.Defeq.map (envS E ent) hty
    rw [Metalean.Expr.map_rename, Metalean.Expr.map_rename] at h'
    exact h'

/-- A translation stays a translation after one new entry whose table agrees with the old one,
weakened, on the old bindings. Reference: `weakening_env` (`MR P/PCUICWeakeningEnv.v`);
`Defeq.map` (`ML Typing/Map.lean:22`). -/
theorem TrM.wkEnv {B : Binds ζ} {B' : Binds (ζ.snoc sig)}
    (hB : ∀ c b, B c = some b → B' c = some b.wk) {lps : List Name} {n : Nat}
    {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n} {e : Expr}
    {t : Metalean.Expr ζ lps.length n} (h : TrM E B lps Γ Δ e t) :
    TrM (E.snoc ent) B' lps (Γ.map wkS) (MLCtx.envMap wkS Δ) e (t.map wkS) := by
  induction h with
  | bvar h => exact .bvar (by rw [MLCtx.findB_envMap, h]; rfl)
  | fvar h => exact .fvar (by rw [MLCtx.findF_envMap, h]; rfl)
  | sort h => exact .sort h
  | const hb hls => exact .const (hB _ _ hb) hls
  | special hb hsp hl _ hsat ih =>
    refine .special (hB _ _ hb) (by rw [MBinding.wk_isSpecial]; exact hsp) (by simpa using hl)
      (fun i a a' h1 h2 => ?_) (SatTr.wkEnv hsat)
    rw [List.getElem?_map] at h2
    obtain ⟨a₀, h3, rfl⟩ := Option.map_eq_some_iff.mp h2
    exact ih i a a₀ h1 h3
  | app hns hf _ ihf iha =>
    refine .app (fun ⟨c, us, b', hfc, hb', hs⟩ => hns ?_) ihf iha
    obtain ⟨b, hb⟩ := hf.head_bound hfc
    rw [hB _ _ hb] at hb'
    cases hb'
    exact ⟨c, us, b, hfc, hb, by rwa [MBinding.wk_isSpecial] at hs⟩
  | lam _ _ ihA ihb =>
    refine .lam ihA ?_
    simpa [MLCtx.pushLam_envMap] using ihb
  | forallE _ _ ihA ihb =>
    refine .forallE ihA ?_
    simpa [MLCtx.pushLam_envMap] using ihb
  | letE _ _ _ ihT ihv ihb =>
    simpa using TrM.letE ihT ihv ihb
  | mdata _ ih => exact .mdata ih
  | lit hb =>
    rw [natLitM_map]
    exact .lit (hB _ _ hb)
  | @projStruct n i S Γ Δ e e' ι η s c ls ps is hst hi hb _ hty ih =>
    have hty' := WkEnvExt.TypedExt.wkEnv (ent := ent) hty
    rw [show (wkS : ζ ⟶ ζ.snoc sig) = (envS E ent).sigs from rfl,
      Metalean.Env.IsStructure.projTerm_map]
    exact .projStruct _ hi (hB _ _ hb) ih
      (by simpa [show (wkS : ζ ⟶ ζ.snoc sig) = (envS E ent).sigs from rfl] using hty')
  | @projProof n S i Γ Δ e e' ι η s c ls ps is hi hb hs hc hnr hf hnst _ hty ih =>
    have hty' := WkEnvExt.TypedExt.wkEnv (ent := ent) hty
    rw [projProofTerm_map wkS η (get_there_block (ent := ent) η)]
    refine .projProof hi (hB _ _ hb) hs hc hnr hf (fun h' => hnst ?_) ih (by simp at hty'; exact hty')
    rw [get_there_block] at h'
    exact ⟨h'.sort_unique, h'.ctor_unique, h'.no_indices, h'.no_recursive,
      (Metalean.Inductive.sortLargeElim_map _ _ _).mp h'.sortLargeElim⟩

/-- A definition's value after one new entry. -/
theorem get_there_defValue {nl : Nat} (η : Head ζ (.const .def nl)) :
    ((E.snoc ent).get (η.map wkS)).defValue = (E.get η).defValue.map wkS := by
  show ((E.get η).map wkS).defValue = _
  generalize E.get η = x
  cases x; rfl

end OneEntry

section Steps
open Metalean (Sigs Sig Env Entry Head)
variable {ζ : Sigs} {E : Env ζ} {B : Binds ζ} {P : List ConstantInfo}

/-- A single-declaration step keeps the old bindings, weakened. -/
theorem ProgEnv.set_ext (h : ProgEnv P ζ E B) {sig : Sig} {m : Name} (hfr : findDecl P m = none)
    (b' : MBinding (ζ.snoc sig)) : ∀ c b, B c = some b → (B.wk.set m b') c = some b.wk := by
  intro c b hb
  have hne : c ≠ m := fun he => not_mem_of_findDecl_none hfr (he ▸ h.bound (by simp [hb]))
  rw [set_wk_ne hne, hb]; rfl

/-- A block step keeps the old bindings, weakened. -/
theorem ProgEnv.ext_ext (h : ProgEnv P ζ E B) {sig : Sig} {B' : Binds (ζ.snoc sig)}
    {decls : List ConstantInfo} (hfr : ∀ ci ∈ decls, findDecl P ci.name = none)
    (hext : BindsExt B B' (decls.map (·.name))) : ∀ c b, B c = some b → B' c = some b.wk := by
  intro c b hb
  have hnot : c ∉ decls.map (·.name) := fun hm => by
    obtain ⟨ci, hci, hn⟩ := List.mem_map.mp hm
    exact not_mem_of_findDecl_none (hfr ci hci) (hn ▸ h.bound (by simp [hb]))
  rw [hext c hnot, Binds.wk, hb]; rfl

/-- A definition is a Metalean `def` whose value is the translation of its value. Reference:
`declared_constant` with `cst_body` (MC §3.6). -/
theorem ProgEnv.lookup_def {c : Name} {v : DefinitionVal} (h : ProgEnv P ζ E B)
    (hc : findDecl P c = some (.defnInfo v)) :
    ∃ η : Head ζ (.const .def v.levelParams.length), B c = some (.const η) ∧
      TrM E B v.levelParams .nil [] v.value (E.get η).defValue := by
  induction h with
  | nil => simp [findDecl] at hc
  | @«axiom» _ _ _ _ v' _ hP hfr _ _ ih | @thm _ _ _ _ v' _ hP hfr _ _ _ ih
  | @«opaque» _ _ _ _ v' _ hP hfr _ _ _ ih =>
    rw [findDecl_cons] at hc
    split at hc
    · cases hc
    · obtain ⟨η, hB, htr⟩ := ih hc
      refine ⟨η.map wkS, by rw [set_wk_ne (Ne.symm ‹_›), hB]; rfl, ?_⟩
      rw [get_there_defValue]
      exact TrM.wkEnv (hP.set_ext hfr _) htr
  | @defn _ _ _ _ v' _ e hP hfr _ _ _ hv ih =>
    rw [findDecl_cons] at hc
    split at hc
    · rename_i hn
      cases hc
      refine ⟨.here, ?_, TrM.wkEnv (hP.set_ext hfr _) hv⟩
      have hc' : c = v.name := hn.symm
      simp [Binds.set, hc']
    · obtain ⟨η, hB, htr⟩ := ih hc
      refine ⟨η.map wkS, by rw [set_wk_ne (Ne.symm ‹_›), hB]; rfl, ?_⟩
      rw [get_there_defValue]
      exact TrM.wkEnv (hP.set_ext hfr _) htr
  | @induct _ _ _ _ ι _ _ _ Is Cs Rs _ hP _ hfr hext _ _ ih =>
    rw [findDecl_append] at hc
    cases hd : findDecl (IndBlock.decls Is Cs Rs) c with
    | some ci =>
      rw [hd] at hc
      cases hc
      obtain ⟨hm, -⟩ := findDecl_eq_some hd
      rcases IndBlock.mem_decls hm with ⟨s, hs⟩ | ⟨s, k, hs⟩ | ⟨s, hs⟩ <;> cases hs
    | none =>
      rw [hd] at hc
      simp only [Option.none_or] at hc
      obtain ⟨η, hB, htr⟩ := ih hc
      have hnot : c ∉ (IndBlock.decls Is Cs Rs).map (·.name) := not_mem_of_findDecl_none hd
      refine ⟨η.map wkS, by rw [hext c hnot, Binds.wk, hB]; rfl, ?_⟩
      rw [get_there_defValue]
      exact TrM.wkEnv (hP.ext_ext hfr hext) htr
  | @quot _ _ _ _ _ qs _ hP _ _ hfr hext _ ih =>
    rw [findDecl_append] at hc
    cases hd : findDecl (qs.reverse.map ConstantInfo.quotInfo) c with
    | some ci =>
      obtain ⟨hm, -⟩ := findDecl_eq_some hd
      rw [hd] at hc
      cases hc
      simp at hm
    | none =>
      rw [hd] at hc
      simp only [Option.none_or] at hc
      obtain ⟨η, hB, htr⟩ := ih hc
      have hnot := not_mem_of_findDecl_none hd
      rw [quot_names_reverse, List.mem_reverse] at hnot
      refine ⟨η.map wkS, by rw [hext c hnot, Binds.wk, hB]; rfl, ?_⟩
      rw [get_there_defValue]
      exact TrM.wkEnv (hP.ext_ext (decls := qs.map .quotInfo)
        (fun ci hci => by obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hci; exact hfr q hq)
        (by rw [List.map_map]; exact hext)) htr

/-- The δ-step of an unfoldable constant: its translation is the Metalean `def` at the
translated levels, which reduces to the instantiated value, and the value translates to the
stored one. With the universe instantiation of translations, this gives the δ equation
`ProgEnv.unfold`. Reference: `eval_delta` (`MR P/PCUICWcbvEval.v:247`); `WHRed.delta`
(`ML Syntax/Reduction.lean:52`). -/
theorem ProgEnv.unfold_delta {σ : EvalEnv} {c : Name} {ci : ConstantInfo} {b : Expr}
    {lps : List Name} {us : List Level} {t : Metalean.Expr ζ lps.length 0}
    (h : ProgEnv P ζ E B) (hsub : SubEnv σ.decls P) (hu : σ.unfold? c = some (ci, b))
    (hc : TrM E B lps .nil [] (.const c us) t) :
    ∃ (v : DefinitionVal) (η : Head ζ (.const .def v.levelParams.length))
      (ls : Fin v.levelParams.length → Metalean.Level lps.length),
      ci = .defnInfo v ∧ b = v.value ∧ t = .const η ls ∧
      TrLevels lps us v.levelParams.length = some ls ∧
      TrM E B v.levelParams .nil [] v.value (E.get η).defValue ∧
      Metalean.WHRed E t ((E.get η).defValue{ls}.wkClosed) := by
  unfold EvalEnv.unfold? at hu
  split at hu
  · rename_i v hv
    split at hu
    · cases hu
    · cases hu
      have hP : findDecl P c = some (.defnInfo v) := by
        obtain ⟨hm, hn⟩ := findDecl_eq_some hv
        have h' := hsub _ hm
        rwa [hn] at h'
      obtain ⟨η, hB, htr⟩ := h.lookup_def hP
      generalize hx : Expr.const c us = x at hc
      cases hc with
      | const hb hls =>
        cases hx
        rw [hB] at hb
        simp only [Option.some.injEq, MBinding.const.injEq] at hb
        obtain ⟨rfl, rfl, hη⟩ := hb
        cases hη
        exact ⟨v, η, _, rfl, rfl, rfl, hls, htr, .delta⟩
      | @special c' us' _ _ _ as _ b' _ hb hsp =>
        have h1 := congrArg Expr.getAppFn hx
        rw [mkAppN_eq_foldl, foldl_app_getAppFn] at h1
        cases h1
        rw [hB] at hb
        cases hb
        cases hsp
      | _ => cases hx
  · cases hu

end Steps

end EraseProof
