import EraseProof.Bridge.Subst

/-!
# Universe instantiation of the translator's term builders

The total term builders of Metalean's translator (`ML Frontend/Translate.lean`: `wrapCase`,
`indTerm`, `ctorTerm`, `recrTerm`, `quotTerm`) and the proof projections `projProofTerm` commute
with universe instantiation (`Expr.instL`): building with instantiated levels gives the
instantiated term.
-/

open Lean Erasure
open Metalean (InstLevel Ctx Expr IndSig Inductive)

namespace EraseProof

section
variable {ζ : Metalean.Sigs} {ℓ ℓ' : Nat}

/-- `Fin.mapM` in `Option` after mapping every component. -/
theorem mapM_option_map : ∀ {k : Nat} {α β : Fin k → Type} (g : ∀ i, α i → β i)
    (f : ∀ i, Option (α i)),
    Fin.mapM (m := Option) (α := β) (fun i => (f i).map (g i)) =
      (Fin.mapM (m := Option) (α := α) f).map (fun h i => g i (h i))
  | 0, _, _, _, _ => by simp only [Fin.mapM]; exact congrArg some (funext fun i => i.elim0)
  | k + 1, α, β, g, f => by
    have ih := mapM_option_map (α := fun i => α i.succ) (β := fun i => β i.succ)
      (fun i => g i.succ) (fun i : Fin k => f i.succ)
    simp only [Fin.mapM] at ih ⊢
    rw [ih]
    cases f 0 <;> cases Fin.mapM (m := Option) (α := fun i => α i.succ) (fun i : Fin k => f i.succ) <;>
      try rfl
    exact congrArg some (funext fun i => by obtain ⟨_ | j, hj⟩ := i <;> rfl)

/-- Partial renaming (`Expr.rename?`, `ML Frontend/Rename.lean:22`) commutes with universe
instantiation. -/
theorem rename?_instL (ls : Fin ℓ → Metalean.Level ℓ') :
    ∀ {m n : Nat} (e : Metalean.Expr ζ ℓ m) (ρ : Fin m → Option (Fin n)),
      (e{ls}).rename? ρ = (e.rename? ρ).map (·{ls}) := by
  intro m n e ρ
  induction e generalizing n with
  | var v => simp only [Metalean.Expr.inst_var, Metalean.Expr.rename?, Option.map_map]; rfl
  | _ =>
    simp only [Metalean.Expr.rename?, Metalean.Expr.inst_ind, Metalean.Expr.inst_ctor,
      Metalean.Expr.inst_recr, Metalean.Expr.inst_quot, Metalean.Expr.inst_quotMk,
      Metalean.Expr.inst_quotLift, Metalean.Expr.inst_quotInd, Metalean.Expr.instL_app,
      Metalean.Expr.inst_lam, Metalean.Expr.inst_forallE, Metalean.Expr.inst_letE,
      Metalean.Expr.inst_sort, Metalean.Expr.inst_const, Metalean.InstLevel.inst_apply, *,
      mapM_option_map, Option.bind_eq_bind, Option.map_bind, Option.bind_map, Option.map_some,
      Function.comp_def]
    all_goals rfl

/-- The successor equation of `Ctx.permuteAux?` (`ML Frontend/Rename.lean:69`), by definitional
unfolding. -/
theorem permuteAux?_succ {a b k : Nat} (hb : b = a + k) (π πinv : Fin k → Option (Fin k))
    (Δ : Metalean.Ctx ζ ℓ a b) (j : Nat) (hj : j + 1 ≤ k) :
    Metalean.Ctx.permuteAux? hb π πinv Δ (j + 1) hj =
      (do
        let Γ ← Metalean.Ctx.permuteAux? hb π πinv Δ j (by omega)
        let o ← π ⟨j, by omega⟩
        let t' ← (Δ.entry (p := a + o.val) (by omega) (by omega)).rename?
          (Metalean.Ctx.permuteMap? a j πinv o)
        some (Γ.snoc t')) := rfl

/-- `Ctx.permuteAux?` (`ML Frontend/Rename.lean:69`) commutes with universe instantiation. -/
theorem permuteAux?_instL (ls : Fin ℓ → Metalean.Level ℓ') {a b k : Nat} (hb : b = a + k)
    (π πinv : Fin k → Option (Fin k)) (Δ : Metalean.Ctx ζ ℓ a b) :
    ∀ (j : Nat) (hj : j ≤ k), Metalean.Ctx.permuteAux? hb π πinv (Δ{ls}) j hj =
      (Metalean.Ctx.permuteAux? hb π πinv Δ j hj).map (·{ls})
  | 0, _ => rfl
  | j + 1, hj => by
    rw [permuteAux?_succ, permuteAux?_succ, permuteAux?_instL ls hb π πinv Δ j (by omega)]
    rcases Metalean.Ctx.permuteAux? hb π πinv Δ j (by omega) with _ | Γ
    · rfl
    rcases π ⟨j, by omega⟩ with _ | o
    · rfl
    have he := Metalean.Ctx.entry_instL ls Δ (p := a + o.val) (by omega) (by omega)
    dsimp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
    rw [← he, rename?_instL]
    rcases (Δ.entry (p := a + o.val) (by omega) (by omega)).rename?
      (Metalean.Ctx.permuteMap? a j πinv o) with _ | t'
    · rfl
    · rfl

/-- `Ctx.permute?` (`ML Frontend/Rename.lean:79`) commutes with universe instantiation. -/
theorem permute?_instL (ls : Fin ℓ → Metalean.Level ℓ') {a b k : Nat} (hb : b = a + k)
    (π πinv : Fin k → Option (Fin k)) (Δ : Metalean.Ctx ζ ℓ a b) :
    Metalean.Ctx.permute? hb π πinv (Δ{ls}) = (Metalean.Ctx.permute? hb π πinv Δ).map (·{ls}) :=
  permuteAux?_instL ls hb π πinv Δ k le_rfl

/-- Universe instantiation leaves a unary literal unchanged. -/
theorem natLitM_instL (ls : Fin ℓ → Metalean.Level ℓ') {n : Nat}
    (ηNat : Metalean.Head ζ (.inductive natSig)) (k : Nat) :
    (natLitM ηNat k : Metalean.Expr ζ ℓ n){ls} = natLitM ηNat k := by
  induction k with
  | zero =>
    simp only [natLitM, Metalean.Expr.inst_ctor]
    congr <;> funext i <;> exact i.elim0
  | succ k ih =>
    simp only [natLitM, Metalean.Expr.inst_ctor]
    congr
    all_goals funext i
    all_goals first | exact i.elim0 | (refine Fin.cases ?_ (fun j => j.elim0) i; simpa using ih)

/-- `wrapCase` (`ML Frontend/Translate.lean:84`) commutes with universe instantiation. -/
theorem wrapCase_instL {ι : Metalean.IndSig} (I : Metalean.Inductive ζ ι)
    (η : Metalean.Head ζ (.inductive ι)) (ls : Fin ι.nlevels → Metalean.Level ℓ) {n : Nat}
    (ps : Fin ι.nparams → Metalean.Expr ζ ℓ n) (ms : Fin ι.nsorts → Metalean.Expr ζ ℓ n)
    (t : Fin ι.nsorts) (c : Fin (ι.nctors t)) (mo : List Nat) {minor w : Metalean.Expr ζ ℓ n}
    (ls' : Fin ℓ → Metalean.Level ℓ')
    (hw : Metalean.Frontend.wrapCase I η ls ps ms t c mo minor = .ok w) :
    Metalean.Frontend.wrapCase I η ls{ls'} ps{ls'} ms{ls'} t c mo minor{ls'} = .ok w{ls'} := by
  unfold Metalean.Frontend.wrapCase at hw ⊢
  dsimp only at hw ⊢
  by_cases hid : Metalean.Frontend.isIdentityOrder mo
      ((ι.ctors t c).nfields + (ι.ctors t c).nrecFields) = true
  · rw [ite_eq_left hid] at hw ⊢
    cases hw
    rfl
  · rw [ite_eq_right hid] at hw ⊢
    rcases hπ : Metalean.Frontend.orderMaps? mo
        ((ι.ctors t c).nfields + (ι.ctors t c).nrecFields) with _ | ⟨π, snd⟩
    · rw [hπ] at hw; cases hw
    · rw [hπ] at hw
      dsimp only at hw ⊢
      obtain ⟨x, hx⟩ : ∃ x, Fin.mapM (m := Option) (fun j => (π j).map fun o =>
          (Metalean.Expr.var ⟨n + o.val, by omega⟩ : Metalean.Expr ζ ℓ
            (n + (ι.ctors t c).nfields + (ι.ctors t c).nrecFields + (ι.ctors t c).nrecFields))) = x :=
        ⟨_, rfl⟩
      rw [hx] at hw
      rcases x with _ | fieldVars
      · cases hw
      · dsimp only at hw
        cases hw
        have hfv := mapM_option_eq_some hx
        rw [mapM_option_of_eq_some (g := fun j => (fieldVars j){ls'}) fun j => ?_]
        · dsimp only
          simp only [Metalean.Ctx.lam_instL, Metalean.Inductive.caseTele_instL,
            Metalean.Expr.instL_apps, Metalean.Expr.wkN_instL]
          congr 3
          funext i
          cases i using Fin.addCases with
          | left j => simp
          | right r => simp
        · have h := hfv j
          simp only [Option.map_eq_some_iff] at h ⊢
          obtain ⟨o, ho, hvar⟩ := h
          exact ⟨o, ho, by rw [← hvar]; rfl⟩

/-- `indTerm` (`ML Frontend/Translate.lean:103`) commutes with universe instantiation. -/
theorem indTerm_instL {ι : Metalean.IndSig} (I : Metalean.Inductive ζ ι)
    (η : Metalean.Head ζ (.inductive ι)) (s : Fin ι.nsorts) (ls : Fin ι.nlevels → Metalean.Level ℓ)
    (ls' : Fin ℓ → Metalean.Level ℓ') :
    (Metalean.Frontend.indTerm I η s ls){ls'} = Metalean.Frontend.indTerm I η s ls{ls'} := by
  unfold Metalean.Frontend.indTerm
  simp only [Metalean.Ctx.lam_instL, Metalean.Ctx.instL_instL, Metalean.Expr.inst_ind]
  rfl

/-- `quotTerm` (`ML Frontend/Translate.lean:197`) commutes with universe instantiation. -/
theorem quotTerm_instL (η : Metalean.Head ζ .quot)
    (eqHead : Metalean.Head ζ (.inductive Metalean.Eq.sig)) (kind : Metalean.Export.QuotKind)
    (us : List (Metalean.Level ℓ)) {t₀ : Metalean.Expr ζ ℓ 0} (ls' : Fin ℓ → Metalean.Level ℓ')
    (h : Metalean.Frontend.quotTerm η eqHead kind us = .ok t₀) :
    Metalean.Frontend.quotTerm η eqHead kind (us.map (·{ls'})) = .ok t₀{ls'} := by
  match kind, us, h with
  | .type, [u], h => cases h; simp; rfl
  | .ctor, [u], h => cases h; simp; rfl
  | .lift, [u, v], h => cases h; simp; rfl
  | .ind, [u], h => cases h; simp; rfl

/-- `ctorTerm` (`ML Frontend/Translate.lean:109`) commutes with universe instantiation. -/
theorem ctorTerm_instL {ι : Metalean.IndSig} (I : Metalean.Inductive ζ ι)
    (η : Metalean.Head ζ (.inductive ι)) (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (ls : Fin ι.nlevels → Metalean.Level ℓ) (mo : List Nat) {t₀ : Metalean.Expr ζ ℓ 0}
    (ls' : Fin ℓ → Metalean.Level ℓ')
    (h : Metalean.Frontend.ctorTerm I η s c ls mo = .ok t₀) :
    Metalean.Frontend.ctorTerm I η s c ls{ls'} mo = .ok t₀{ls'} := by
  unfold Metalean.Frontend.ctorTerm at h ⊢
  dsimp only at h ⊢
  rcases hπ : Metalean.Frontend.orderMaps? mo
        ((ι.ctors s c).nfields + (ι.ctors s c).nrecFields) with _ | ⟨π, πinv⟩
  · rw [hπ] at h; cases h
  · rw [hπ] at h
    dsimp only at h ⊢
    have hf : ∀ stop, (I.ctors s c).fieldTele η ls{ls'}
        (fun p => (Metalean.Expr.var p : Metalean.Expr ζ ℓ' ι.nparams)) stop =
        ((I.ctors s c).fieldTele η ls (fun p => .var p) stop){ls'} := fun stop => by
      exact (Metalean.Ctor.fieldTele_instL (I.ctors s c) η ls (fun p => .var p) ls' stop).symm
    rw [hf, permute?_instL]
    obtain ⟨x, hx⟩ : ∃ x, Metalean.Ctx.permute? (k := (ι.ctors s c).nfields + (ι.ctors s c).nrecFields)
        (by simp [Nat.add_assoc]) π πinv ((I.ctors s c).fieldTele η ls (fun p => .var p)) = x := ⟨_, rfl⟩
    rw [hx] at h ⊢
    rcases x with _ | fields'
    · cases h
    rw [Option.map_some]
    dsimp only at h ⊢
    obtain ⟨y, hy⟩ : ∃ y, Fin.mapM (m := Option) (fun f : Fin (ι.ctors s c).nfields =>
        (do let j ← πinv (Fin.castAdd (ι.ctors s c).nrecFields f)
            some (Metalean.Expr.var ⟨ι.nparams + j.val, by omega⟩ : Metalean.Expr ζ ℓ
              (ι.nparams + ((ι.ctors s c).nfields + (ι.ctors s c).nrecFields))))) = y := ⟨_, rfl⟩
    have hy' : Fin.mapM (m := Option) (fun f : Fin (ι.ctors s c).nfields =>
        (do let j ← πinv (Fin.castAdd (ι.ctors s c).nrecFields f)
            some (Metalean.Expr.var ⟨ι.nparams + j.val, by omega⟩ : Metalean.Expr ζ ℓ'
              (ι.nparams + ((ι.ctors s c).nfields + (ι.ctors s c).nrecFields))))) =
        y.map (fun g i => (g i){ls'}) := by
      rw [← hy, ← mapM_option_map (fun _ x => x{ls'})]
      congr 1; funext f; cases πinv _ <;> rfl
    obtain ⟨z, hz⟩ : ∃ z, Fin.mapM (m := Option) (fun r : Fin (ι.ctors s c).nrecFields =>
        (do let j ← πinv (Fin.natAdd (ι.ctors s c).nfields r)
            some (Metalean.Expr.var ⟨ι.nparams + j.val, by omega⟩ : Metalean.Expr ζ ℓ
              (ι.nparams + ((ι.ctors s c).nfields + (ι.ctors s c).nrecFields))))) = z := ⟨_, rfl⟩
    have hz' : Fin.mapM (m := Option) (fun r : Fin (ι.ctors s c).nrecFields =>
        (do let j ← πinv (Fin.natAdd (ι.ctors s c).nfields r)
            some (Metalean.Expr.var ⟨ι.nparams + j.val, by omega⟩ : Metalean.Expr ζ ℓ'
              (ι.nparams + ((ι.ctors s c).nfields + (ι.ctors s c).nrecFields))))) =
        z.map (fun g i => (g i){ls'}) := by
      rw [← hz, ← mapM_option_map (fun _ x => x{ls'})]
      congr 1; funext f; cases πinv _ <;> rfl
    rw [hy, hz] at h
    rw [hy', hz']
    rcases y with _ | fds
    · cases h
    rcases z with _ | recFds
    · cases h
    rw [Option.map_some]
    dsimp only at h ⊢
    cases h
    show Except.ok _ = Except.ok _
    congr 1
    simp only [Metalean.Ctx.lam_instL, Metalean.Ctx.instL_append, Metalean.Ctx.instL_instL,
      Metalean.Expr.inst_ctor]
    rfl

/-- `leanCaseType` (`ML Frontend/Translate.lean:130`) commutes with universe instantiation. -/
theorem leanCaseType_instL {ι : Metalean.IndSig} (I : Metalean.Inductive ζ ι)
    (η : Metalean.Head ζ (.inductive ι)) (ls : Fin ι.nlevels → Metalean.Level ℓ) {n : Nat}
    (ps : Fin ι.nparams → Metalean.Expr ζ ℓ n) (ms : Fin ι.nsorts → Metalean.Expr ζ ℓ n)
    (t : Fin ι.nsorts) (c : Fin (ι.nctors t)) (mo : List Nat) {w : Metalean.Expr ζ ℓ n}
    (ls' : Fin ℓ → Metalean.Level ℓ')
    (h : Metalean.Frontend.leanCaseType I η ls ps ms t c mo = .ok w) :
    Metalean.Frontend.leanCaseType I η ls{ls'} ps{ls'} ms{ls'} t c mo = .ok w{ls'} := by
  unfold Metalean.Frontend.leanCaseType at h ⊢
  dsimp only at h ⊢
  rcases hπ : Metalean.Frontend.orderMaps? mo
        ((ι.ctors t c).nfields + (ι.ctors t c).nrecFields) with _ | ⟨π, πinv⟩
  · rw [hπ] at h; cases h
  · rw [hπ] at h
    dsimp only at h ⊢
    obtain ⟨x, hx⟩ : ∃ x, Metalean.Ctx.permute?
        (k := (ι.ctors t c).nfields + (ι.ctors t c).nrecFields + (ι.ctors t c).nrecFields)
        (by omega)
        (fun j => if h : j.val < (ι.ctors t c).nfields + (ι.ctors t c).nrecFields then
            Option.map (Fin.castAdd (ι.ctors t c).nrecFields) (π ⟨j.val, h⟩) else some j)
        (fun o => if h : o.val < (ι.ctors t c).nfields + (ι.ctors t c).nrecFields then
            Option.map (Fin.castAdd (ι.ctors t c).nrecFields) (πinv ⟨o.val, h⟩) else some o)
        (I.caseTele η ls ps ms t c) = x := ⟨_, rfl⟩
    rw [hx] at h
    rw [← Metalean.Inductive.caseTele_instL, permute?_instL, hx]
    rcases x with _ | tele
    · cases h
    rw [Option.map_some]
    dsimp only at h ⊢
    obtain ⟨y, hy⟩ : ∃ y, Metalean.Expr.rename?
        (fun v : Fin (n + (ι.ctors t c).nfields + (ι.ctors t c).nrecFields + (ι.ctors t c).nrecFields) =>
          if h : v.val < n then some (⟨v.val, by omega⟩ : Fin (n + ((ι.ctors t c).nfields +
            (ι.ctors t c).nrecFields + (ι.ctors t c).nrecFields)))
          else Option.map (fun j => ⟨n + j.val, by omega⟩)
            (if h : v.val - n < (ι.ctors t c).nfields + (ι.ctors t c).nrecFields then
              Option.map (Fin.castAdd (ι.ctors t c).nrecFields) (πinv ⟨v.val - n, h⟩)
            else some ⟨v.val - n, by omega⟩))
        (I.caseType η ls ps ms t c) = y := ⟨_, rfl⟩
    rw [hy] at h
    rw [← Metalean.Inductive.caseType_instL, rename?_instL, hy]
    rcases y with _ | concl
    · cases h
    rw [Option.map_some]
    dsimp only at h ⊢
    cases h
    show Except.ok _ = Except.ok _
    rw [Metalean.Ctx.pi_instL]

/-- An `Except` whose option is `some a` is `.ok a`. -/
theorem toOption_eq_some {ε α : Type} {x : Except ε α} {a : α} (h : x.toOption = some a) :
    x = .ok a := by
  rcases x with e | b
  · cases h
  · cases h; rfl

/-- A successful bind in `Except` has a successful first step. -/
theorem except_bind_eq_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  rcases x with e | a
  · cases h
  · exact ⟨a, rfl, h⟩

/-- The successor equation of `leanCaseBinders` (`ML Frontend/Translate.lean:156`), by definitional
unfolding. -/
theorem leanCaseBinders_succ {ι : Metalean.IndSig} (I : Metalean.Inductive ζ ι)
    (η : Metalean.Head ζ (.inductive ι)) (ls : Fin ι.nlevels → Metalean.Level ℓ)
    (mo : (t : Fin ι.nsorts) → Fin (ι.nctors t) → List Nat) (count : Nat)
    (h : count + 1 ≤ Fin.sum ι.nctors) :
    Metalean.Frontend.leanCaseBinders I η ls mo (count + 1) h =
      (match Fin.decodeSigma ι.nctors ⟨count, by omega⟩ with
      | ⟨t, c⟩ => do
        let Γ ← Metalean.Frontend.leanCaseBinders I η ls mo count (by omega)
        let ty ← Metalean.Frontend.leanCaseType I η ls
          (fun param => Metalean.Expr.var (param.castLE (by omega)))
          (fun t => Metalean.Expr.var ⟨ι.nparams + t.val, by omega⟩) t c (mo t c)
        pure (Γ.snoc ty)) := rfl

/-- `leanCaseBinders` (`ML Frontend/Translate.lean:156`) commutes with universe instantiation. -/
theorem leanCaseBinders_instL {ι : Metalean.IndSig} (I : Metalean.Inductive ζ ι)
    (η : Metalean.Head ζ (.inductive ι)) (ls : Fin ι.nlevels → Metalean.Level ℓ)
    (mo : (t : Fin ι.nsorts) → Fin (ι.nctors t) → List Nat) (ls' : Fin ℓ → Metalean.Level ℓ') :
    ∀ (count : Nat) (h : count ≤ Fin.sum ι.nctors) {Γ},
      Metalean.Frontend.leanCaseBinders I η ls mo count h = .ok Γ →
      Metalean.Frontend.leanCaseBinders I η ls{ls'} mo count h = .ok Γ{ls'}
  | 0, h, Γ, hΓ => by cases hΓ; rfl
  | count + 1, h, Γ, hΓ => by
    rw [leanCaseBinders_succ] at hΓ ⊢
    rcases hd : Fin.decodeSigma ι.nctors ⟨count, by omega⟩ with ⟨t, c⟩
    rw [hd] at hΓ
    dsimp only at hΓ ⊢
    obtain ⟨Γ₀, h₀, hΓ⟩ := except_bind_eq_ok hΓ
    obtain ⟨ty, hty, hΓ⟩ := except_bind_eq_ok hΓ
    cases hΓ
    rw [leanCaseBinders_instL I η ls mo ls' count (by omega) h₀]
    have : Metalean.Frontend.leanCaseType I η ls{ls'}
        (fun param => Metalean.Expr.var (param.castLE (by omega)))
        (fun t => Metalean.Expr.var ⟨ι.nparams + t.val, by omega⟩) t c (mo t c) = .ok ty{ls'} :=
      leanCaseType_instL I η ls _ _ t c (mo t c) ls' hty
    rw [this]
    rfl

/-- `recrTerm` (`ML Frontend/Translate.lean:171`) commutes with universe instantiation. -/
theorem recrTerm_instL {ι : Metalean.IndSig} (I : Metalean.Inductive ζ ι)
    (η : Metalean.Head ζ (.inductive ι)) (s : Fin ι.nsorts) (ls : Fin ι.nlevels → Metalean.Level ℓ)
    (l : Metalean.Level ℓ) (mo : (t : Fin ι.nsorts) → Fin (ι.nctors t) → List Nat)
    {t₀ : Metalean.Expr ζ ℓ 0} (ls' : Fin ℓ → Metalean.Level ℓ')
    (h : Metalean.Frontend.recrTerm I η s ls l mo = .ok t₀) :
    Metalean.Frontend.recrTerm I η s ls{ls'} l{ls'} mo = .ok t₀{ls'} := by
  unfold Metalean.Frontend.recrTerm at h ⊢
  obtain ⟨cs, hcs, h⟩ := except_bind_eq_ok h
  rw [leanCaseBinders_instL I η ls mo ls' _ _ hcs]
  dsimp only at h
  obtain ⟨m, hm⟩ : ∃ m, Fin.mapM (m := Option)
      (α := fun t => (c : Fin (ι.nctors t)) → Metalean.Expr ζ ℓ (ι.recrEnd s))
      (fun t => Fin.mapM (m := Option) (α := fun _ => Metalean.Expr ζ ℓ (ι.recrEnd s)) fun c =>
        (Metalean.Frontend.wrapCase I η ls
          (fun p => .var (Metalean.IndSig.RecrBinder.param (s := s) p).resolve)
          (fun t => .var (Metalean.IndSig.RecrBinder.motive (s := s) t).resolve) t c (mo t c)
          (.var (Metalean.IndSig.RecrBinder.case (s := s) t c).resolve)).toOption) = m := ⟨_, rfl⟩
  rw [hm] at h
  rcases m with _ | minsB
  · cases h
  dsimp only at h
  cases h
  have hw : ∀ t c, Metalean.Frontend.wrapCase I η ls
      (fun p => .var (Metalean.IndSig.RecrBinder.param (s := s) p).resolve)
      (fun t => .var (Metalean.IndSig.RecrBinder.motive (s := s) t).resolve) t c (mo t c)
      (.var (Metalean.IndSig.RecrBinder.case (s := s) t c).resolve) = .ok (minsB t c) :=
    fun t c => toOption_eq_some (mapM_option_eq_some (mapM_option_eq_some hm t) c)
  dsimp only
  rw [mapM_option_of_eq_some (g := fun t c => (minsB t c){ls'})
    (f := fun t => Fin.mapM (m := Option) (α := fun _ => Metalean.Expr ζ ℓ' (ι.recrEnd s)) fun c =>
        (Metalean.Frontend.wrapCase I η ls{ls'}
          (fun p => .var (Metalean.IndSig.RecrBinder.param (s := s) p).resolve)
          (fun t => .var (Metalean.IndSig.RecrBinder.motive (s := s) t).resolve) t c (mo t c)
          (.var (Metalean.IndSig.RecrBinder.case (s := s) t c).resolve)).toOption) fun t =>
    mapM_option_of_eq_some fun c =>
      congrArg Except.toOption (wrapCase_instL _ _ _ _ _ _ _ _ ls' (hw t c))]
  show Except.ok _ = Except.ok _
  congr 1
  simp only [Metalean.Ctx.lam_instL, Metalean.Ctx.inst_snoc, Metalean.Ctx.instL_append,
    Metalean.Ctx.instL_instL, Metalean.Inductive.motiveBinders_instL,
    Metalean.Inductive.indexTele_instL, Metalean.Expr.inst_recr, Metalean.Expr.inst_ind,
    Metalean.Expr.wkN_instL, Metalean.InstLevel.inst_tuple, Metalean.Expr.inst_var]

/-- The proof projection `projProofTerm` commutes with universe instantiation. -/
theorem projProofTerm_instL (E : Metalean.Env ζ) {ι : Metalean.IndSig}
    (η : Metalean.Head ζ (.inductive ι)) (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (ls : Fin ι.nlevels → Metalean.Level ℓ) (hi : ι.nindices s = 0) (ls' : Fin ℓ → Metalean.Level ℓ')
    (f : Nat) : ∀ {n : Nat} (ps : Fin ι.nparams → Metalean.Expr ζ ℓ n) (maj : Metalean.Expr ζ ℓ n),
      (projProofTerm E η s c ls hi ps f maj){ls'} =
        projProofTerm E η s c ls{ls'} hi ps{ls'} f maj{ls'} := by
  induction f using Nat.strong_induction_on with
  | _ f ih =>
  intro n ps maj
  rw [projProofTerm, projProofTerm]
  simp only [Metalean.Expr.inst_recr, Metalean.Level.inst_zero]
  congr 1
  · funext t
    simp only [Metalean.InstLevel.inst_apply]
    rw [Metalean.Ctx.lam_instL, Metalean.Inductive.motiveTele_instL]
    congr 1
    split
    · rw [Metalean.Ctor.ordinaryFieldExpr_instL]
      congr 1
      · funext p; exact Metalean.Expr.wkN_instL ls' (ps p) _
      · funext j
        simp only [Metalean.InstLevel.inst_apply]
        split
        · rw [ih j (by omega)]
          congr 1
          funext p; exact Metalean.Expr.wkN_instL ls' (ps p) _
        · rfl
    · rfl
  · funext t d
    split
    · rename_i hf
      rw [Metalean.Ctx.lam_instL, Metalean.Inductive.caseTele_instL,
        Metalean.CtorSig.caseOrdinary_instL]
      congr 2
      funext t'
      simp only [Metalean.InstLevel.inst_apply]
      rw [Metalean.Ctx.lam_instL, Metalean.Inductive.motiveTele_instL]
      congr 1
      split
      · rw [Metalean.Ctor.ordinaryFieldExpr_instL]
        congr 1
        · funext p; exact Metalean.Expr.wkN_instL ls' (ps p) _
        · funext j
          simp only [Metalean.InstLevel.inst_apply]
          split
          · rw [ih j (by omega)]
            congr 1
            funext p; exact Metalean.Expr.wkN_instL ls' (ps p) _
          · rfl
      · rfl
    · rfl
  · funext i; exact absurd i.isLt (by omega)

end

end EraseProof
