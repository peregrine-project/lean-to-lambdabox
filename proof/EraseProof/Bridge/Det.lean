import EraseProof.Bridge.Cong
import EraseProof.Bridge.Proj
import EraseProof.Bridge.Subst
import EraseProof.Bridge.Basic

/-!
# Uniqueness of the translation up to definitional equality

Two translations of one Lean term are congruent (`TrM.dcong`): they differ only where the
translation chooses by typing (the levels and parameters of a projection's major), and in their
locals. With `DCong.defeq`, two translations typed at one type are definitionally equal at it
(`TrM.det`). Reference: lean4lean `TrExprS.uniq`; `Defeq.uniqTy` (`ML Metatheory/Unique.lean:149`).
-/

open Lean Erasure
open Metalean (Defeq EnvWF CtxWF)

namespace EraseProof


section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {ℓ : Nat}

namespace TrDet

/-- Application spines of congruent heads to pointwise congruent arguments. -/
theorem appList {n : Nat} {Γ₁ Γ₂ : Metalean.Ctx ζ ℓ 0 n} {f₁ f₂ : Metalean.Expr ζ ℓ n} :
    ∀ {as₁ as₂ : List (Metalean.Expr ζ ℓ n)}, DCong E Γ₁ Γ₂ f₁ f₂ → as₁.length = as₂.length →
      (∀ (i : Nat) a b, as₁[i]? = some a → as₂[i]? = some b → DCong E Γ₁ Γ₂ a b) →
      DCong E Γ₁ Γ₂ (f₁.appList as₁) (f₂.appList as₂)
  | [], [], hf, _, _ => hf
  | a :: as₁, b :: as₂, hf, hlen, h =>
    appList (f₁ := .app f₁ a) (f₂ := .app f₂ b) (.app hf (h 0 a b rfl rfl))
      (by simpa using hlen) fun i a b ha hb => h (i + 1) a b ha hb
  | [], _ :: _, _, hlen, _ | _ :: _, [], _, hlen, _ => by simp at hlen

/-- Whether `wrapCase` (`ML Frontend/Translate.lean:84`) succeeds depends on the order only. -/
theorem wrapCase_ok {ι : Metalean.IndSig} (I : Metalean.Inductive ζ ι)
    (η : Metalean.Head ζ (.inductive ι)) (ls : Fin ι.nlevels → Metalean.Level ℓ) {n n' : Nat}
    {ps : Fin ι.nparams → Metalean.Expr ζ ℓ n} {ms : Fin ι.nsorts → Metalean.Expr ζ ℓ n}
    {t : Fin ι.nsorts} {c : Fin (ι.nctors t)} {mo : List Nat} {minor w : Metalean.Expr ζ ℓ n}
    (hw : Metalean.Frontend.wrapCase I η ls ps ms t c mo minor = .ok w)
    (ps' : Fin ι.nparams → Metalean.Expr ζ ℓ n') (ms' : Fin ι.nsorts → Metalean.Expr ζ ℓ n')
    (minor' : Metalean.Expr ζ ℓ n') :
    ∃ w', Metalean.Frontend.wrapCase I η ls ps' ms' t c mo minor' = .ok w' := by
  unfold Metalean.Frontend.wrapCase at hw ⊢
  dsimp only at hw ⊢
  by_cases hid : Metalean.Frontend.isIdentityOrder mo
      ((ι.ctors t c).nfields + (ι.ctors t c).nrecFields) = true
  · rw [ite_eq_left hid]; exact ⟨_, rfl⟩
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
      · have hfv := mapM_option_eq_some hx
        have hsome : ∀ j, ∃ o, π j = some o := fun j => by
          have h := hfv j
          simp only [Option.map_eq_some_iff] at h
          obtain ⟨o, ho, -⟩ := h
          exact ⟨o, ho⟩
        rw [mapM_option_of_eq_some (g := fun j => (((π j).map fun o =>
          (Metalean.Expr.var ⟨n' + o.val, by omega⟩ : Metalean.Expr ζ ℓ
            (n' + (ι.ctors t c).nfields + (ι.ctors t c).nrecFields +
              (ι.ctors t c).nrecFields))).get (by obtain ⟨o, ho⟩ := hsome j; simp [ho])))
          fun j => (Option.some_get _).symm]
        exact ⟨_, rfl⟩

/-- Minors wrapped by `wrapCase` from pointwise congruent parameters, motives and minors. -/
theorem wrapCase_dcong {ι : Metalean.IndSig} (I : Metalean.Inductive ζ ι)
    (η : Metalean.Head ζ (.inductive ι)) (ls : Fin ι.nlevels → Metalean.Level ℓ) {n : Nat}
    {Γ₁ Γ₂ : Metalean.Ctx ζ ℓ 0 n} {ps₁ ps₂ : Fin ι.nparams → Metalean.Expr ζ ℓ n}
    {ms₁ ms₂ : Fin ι.nsorts → Metalean.Expr ζ ℓ n} {t : Fin ι.nsorts} {c : Fin (ι.nctors t)}
    {mo : List Nat} {minor₁ minor₂ w₁ w₂ : Metalean.Expr ζ ℓ n}
    (hw₁ : Metalean.Frontend.wrapCase I η ls ps₁ ms₁ t c mo minor₁ = .ok w₁)
    (hw₂ : Metalean.Frontend.wrapCase I η ls ps₂ ms₂ t c mo minor₂ = .ok w₂)
    (hps : ∀ p, DCong E Γ₁ Γ₂ (ps₁ p) (ps₂ p)) (hms : ∀ t, DCong E Γ₁ Γ₂ (ms₁ t) (ms₂ t))
    (hmin : DCong E Γ₁ Γ₂ minor₁ minor₂) : DCong E Γ₁ Γ₂ w₁ w₂ := by
  let psG : Fin ι.nparams → Metalean.Expr ζ ℓ (n + ι.nparams + ι.nsorts + 1) :=
    fun p => .var (Fin.castAdd 1 (Fin.castAdd ι.nsorts (Fin.natAdd n p)))
  let msG : Fin ι.nsorts → Metalean.Expr ζ ℓ (n + ι.nparams + ι.nsorts + 1) :=
    fun t => .var (Fin.castAdd 1 (Fin.natAdd (n + ι.nparams) t))
  let minG : Metalean.Expr ζ ℓ (n + ι.nparams + ι.nsorts + 1) :=
    .var (Fin.natAdd (n + ι.nparams + ι.nsorts) (0 : Fin 1))
  let σ (ps : Fin ι.nparams → Metalean.Expr ζ ℓ n) (ms : Fin ι.nsorts → Metalean.Expr ζ ℓ n)
      (minor : Metalean.Expr ζ ℓ n) : Metalean.Subst ζ ℓ (n + ι.nparams + ι.nsorts + 1) n :=
    Fin.append (Fin.append (Fin.append (fun v => .var v) ps) ms) fun _ => minor
  obtain ⟨w₀, h₀⟩ := wrapCase_ok I η ls hw₁ psG msG minG
  have key {ps ms minor w} (hw : Metalean.Frontend.wrapCase I η ls ps ms t c mo minor = .ok w) :
      w = w₀.subst (σ ps ms minor) := by
    have h := wrapCase_subst I η ls psG msG t c mo (σ ps ms minor) h₀
    simp only [psG, msG, minG, σ, Metalean.Expr.subst, Fin.append_left, Fin.append_right] at h
    rw [hw] at h
    cases h
    rfl
  rw [key hw₁, key hw₂]
  refine DCong.subst w₀ fun v => ?_
  refine Fin.addCases (fun v => ?_) (fun _ => ?_) v
  · refine Fin.addCases (fun v => ?_) (fun t => ?_) v
    · refine Fin.addCases (fun v => ?_) (fun p => ?_) v
      · simp only [σ, Fin.append_left]; exact .refl
      · simp only [σ, Fin.append_left, Fin.append_right]; exact hps p
    · simp only [σ, Fin.append_left, Fin.append_right]; exact hms t
  · simp only [σ, Fin.append_right]; exact hmin

/-- Proof projections of pointwise congruent parameters and congruent majors. -/
theorem projProofTerm_dcong {ι : Metalean.IndSig} (η : Metalean.Head ζ (.inductive ι))
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) (ls : Fin ι.nlevels → Metalean.Level ℓ)
    (hi : ι.nindices s = 0) (f : Nat) {n : Nat} {Γ₁ Γ₂ : Metalean.Ctx ζ ℓ 0 n}
    {ps₁ ps₂ : Fin ι.nparams → Metalean.Expr ζ ℓ n} {maj₁ maj₂ : Metalean.Expr ζ ℓ n}
    (hps : ∀ p, DCong E Γ₁ Γ₂ (ps₁ p) (ps₂ p)) (hmaj : DCong E Γ₁ Γ₂ maj₁ maj₂) :
    DCong E Γ₁ Γ₂ (projProofTerm E η s c ls hi ps₁ f maj₁) (projProofTerm E η s c ls hi ps₂ f maj₂) := by
  let psG : Fin ι.nparams → Metalean.Expr ζ ℓ (n + ι.nparams + 1) :=
    fun p => .var (Fin.castAdd 1 (Fin.natAdd n p))
  let majG : Metalean.Expr ζ ℓ (n + ι.nparams + 1) := .var (Fin.natAdd (n + ι.nparams) (0 : Fin 1))
  let σ (ps : Fin ι.nparams → Metalean.Expr ζ ℓ n) (maj : Metalean.Expr ζ ℓ n) :
      Metalean.Subst ζ ℓ (n + ι.nparams + 1) n :=
    Fin.append (Fin.append (fun v => .var v) ps) fun _ => maj
  have key (ps maj) : projProofTerm E η s c ls hi ps f maj =
      (projProofTerm E η s c ls hi psG f majG).subst (σ ps maj) := by
    rw [projProofTerm_subst]
    simp only [psG, majG, σ, Metalean.Expr.subst, Fin.append_left, Fin.append_right]
  rw [key ps₁ maj₁, key ps₂ maj₂]
  refine DCong.subst _ fun v => ?_
  refine Fin.addCases (fun v => ?_) (fun _ => ?_) v
  · refine Fin.addCases (fun v => ?_) (fun p => ?_) v
    · simp only [σ, Fin.append_left]; exact .refl
    · simp only [σ, Fin.append_left, Fin.append_right]; exact hps p
  · simp only [σ, Fin.append_right]; exact hmaj

/-- A relation between the entries of two appended lists, on each part. -/
theorem rel_append {α : Type} {P : α → α → Prop} {L₁ L₂ R₁ R₂ : List α}
    (hL : L₁.length = L₂.length)
    (h : ∀ (i : Nat) a b, (L₁ ++ R₁)[i]? = some a → (L₂ ++ R₂)[i]? = some b → P a b) :
    (∀ (i : Nat) a b, L₁[i]? = some a → L₂[i]? = some b → P a b) ∧
      ∀ (i : Nat) a b, R₁[i]? = some a → R₂[i]? = some b → P a b := by
  refine ⟨fun i a b ha hb => h i a b ?_ ?_, fun i a b ha hb => h (L₁.length + i) a b ?_ ?_⟩
  · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp ha).1]; exact ha
  · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hb).1]; exact hb
  · rw [List.getElem?_append_right (by omega)]; simpa using ha
  · rw [List.getElem?_append_right (by omega), hL]; simpa using hb

/-- A relation between the entries of two `List.ofFn`. -/
theorem rel_ofFn {α : Type} {P : α → α → Prop} {k : Nat} {f g : Fin k → α}
    (h : ∀ (i : Nat) a b, (List.ofFn f)[i]? = some a → (List.ofFn g)[i]? = some b → P a b)
    (p : Fin k) : P (f p) (g p) :=
  h p.val _ _ (by simp) (by simp)

/-- The level arguments of a recursor are determined. -/
theorem RecrLevels.det {ι : Metalean.IndSig} {I : Metalean.Inductive ζ ι} {lps : List Name}
    {us us₁ us₂ : List Level} {l₁ l₂ : Metalean.Level lps.length}
    (h₁ : RecrLevels I lps us l₁ us₁) (h₂ : RecrLevels I lps us l₂ us₂) : l₁ = l₂ ∧ us₁ = us₂ := by
  rcases h₁ with ⟨hI, u, rfl, hu⟩ | ⟨hI, rfl, rfl⟩ <;>
    rcases h₂ with ⟨hI', u', h', hu'⟩ | ⟨hI', rfl, rfl⟩
  · cases h'; exact ⟨Option.some.inj (hu.symm.trans hu'), rfl⟩
  · exact absurd hI hI'
  · exact absurd hI' hI
  · exact ⟨rfl, rfl⟩

/-- The translation of universe levels is a function. -/
theorem TrLevels.det {lps : List Name} {us : List Level} {k : Nat}
    {ls₁ ls₂ : Fin k → Metalean.Level lps.length} (h₁ : TrLevels lps us k = some ls₁)
    (h₂ : TrLevels lps us k = some ls₂) : ls₁ = ls₂ :=
  Option.some.inj (h₁.symm.trans h₂)

end TrDet

section
variable {E : Metalean.Env ζ} {lps : List Name}
open TrDet

/-- Two images of one saturating binding with pointwise congruent arguments are congruent. -/
theorem SatTr.dcong {n : Nat} {Γ₁ Γ₂ : Metalean.Ctx ζ lps.length 0 n} {b : MBinding ζ}
    {us : List Level} {as₁ as₂ : List (Metalean.Expr ζ lps.length n)}
    {t₁ t₂ : Metalean.Expr ζ lps.length n} (h₁ : SatTr E lps b us as₁ t₁)
    (h₂ : SatTr E lps b us as₂ t₂) (hlen : as₁.length = as₂.length)
    (h : ∀ (i : Nat) a b, as₁[i]? = some a → as₂[i]? = some b → DCong E Γ₁ Γ₂ a b) :
    DCong E Γ₁ Γ₂ t₁ t₂ := by
  cases h₁ with
  | indSat ps₁ is₁ rest₁ hl₁ =>
    cases h₂ with
    | indSat ps₂ is₂ rest₂ hl₂ =>
      obtain rfl := TrLevels.det hl₁ hl₂
      obtain ⟨h₁, hr⟩ := rel_append (by simp) h
      obtain ⟨hp, hi⟩ := rel_append (by simp) h₁
      exact appList (.ind (rel_ofFn hp) (rel_ofFn hi)) (by simpa using hlen) hr
    | indEta _ hlt => simp at hlen; omega
  | indEta hl₁ hlt =>
    cases h₂ with
    | indSat => simp at hlen; omega
    | indEta hl₂ _ =>
      obtain rfl := TrLevels.det hl₁ hl₂
      exact appList .refl hlen h
  | ctorSat ps₁ fs₁ rest₁ fds₁ rf₁ hl₁ hfs₁ hord hperm₁ =>
    cases h₂ with
    | ctorSat ps₂ fs₂ rest₂ fds₂ rf₂ hl₂ hfs₂ _ hperm₂ =>
      obtain rfl := TrLevels.det hl₁ hl₂
      obtain ⟨h₁, hr⟩ := rel_append (by simp [hfs₁, hfs₂]) h
      obtain ⟨hp, hf⟩ := rel_append (by simp) h₁
      have hA (o) : DCong E Γ₁ Γ₂ (Fin.append fds₁ rf₁ o) (Fin.append fds₂ rf₂ o) := by
        obtain ⟨j, a, hj, ha, h1⟩ := hperm₁ o
        obtain ⟨j', a', hj', ha', h2⟩ := hperm₂ o
        rw [hj] at hj'; cases hj'
        rw [h1, h2]; exact hf j a a' ha ha'
      refine appList (.ctor (rel_ofFn hp) (fun f => ?_) (fun f => ?_)) (by simpa [hfs₁, hfs₂] using hlen) hr
      · simpa using hA (Fin.castAdd _ f)
      · simpa using hA (Fin.natAdd _ f)
    | ctorEta _ hlt => simp [hfs₁] at hlen; omega
  | ctorEta hl₁ hlt ht₁ =>
    cases h₂ with
    | ctorSat _ _ _ _ _ _ hfs => simp [hfs] at hlen; omega
    | ctorEta hl₂ _ ht₂ =>
      obtain rfl := TrLevels.det hl₁ hl₂
      rw [ht₁] at ht₂; cases ht₂
      exact appList .refl hlen h
  | recrSat mo₁ A₁ rest₁ mins₁ hR₁ hl₁ hmo₁ hw₁ =>
    cases h₂ with
    | recrSat mo₂ A₂ rest₂ mins₂ hR₂ hl₂ hmo₂ hw₂ =>
      obtain ⟨rfl, rfl⟩ := RecrLevels.det hR₁ hR₂
      obtain rfl := TrLevels.det hl₁ hl₂
      obtain rfl : mo₁ = mo₂ := funext fun t => funext fun c =>
        Option.some.inj ((hmo₁ t c).symm.trans (hmo₂ t c))
      obtain ⟨hA, hr⟩ := rel_append (by simp) h
      have hA := rel_ofFn hA
      exact appList (.recr (fun _ => hA _) (fun _ => hA _)
        (fun t c => wrapCase_dcong _ _ _ (hw₁ t c) (hw₂ t c) (fun _ => hA _) (fun _ => hA _) (hA _))
        (fun _ => hA _) (hA _)) (by simpa using hlen) hr
    | recrEta _ _ _ _ hlt => simp only [List.length_append, List.length_ofFn] at hlen; omega
  | recrEta mo₁ hR₁ hl₁ hmo₁ hlt ht₁ =>
    cases h₂ with
    | recrSat => simp only [List.length_append, List.length_ofFn] at hlen; omega
    | recrEta mo₂ hR₂ hl₂ hmo₂ _ ht₂ =>
      obtain ⟨rfl, rfl⟩ := RecrLevels.det hR₁ hR₂
      obtain rfl := TrLevels.det hl₁ hl₂
      obtain rfl : mo₁ = mo₂ := funext fun t => funext fun c =>
        Option.some.inj ((hmo₁ t c).symm.trans (hmo₂ t c))
      rw [ht₁] at ht₂; cases ht₂
      exact appList .refl hlen h
  | quotType hu₁ | quotMk hu₁ | quotLift hu₁ | quotInd hu₁ =>
    cases h₂ with
    | quotEta _ hlt => simp [quotArity] at hlen hlt; omega
    | _ =>
      rename_i hu₂
      rw [hu₁] at hu₂; cases hu₂
      obtain ⟨h₁, hr⟩ := rel_append (by simp) h
      refine appList ?_ (by simpa using hlen) hr
      first
        | exact .quot (h₁ 0 _ _ rfl rfl) (h₁ 1 _ _ rfl rfl)
        | exact .quotMk (h₁ 0 _ _ rfl rfl) (h₁ 1 _ _ rfl rfl) (h₁ 2 _ _ rfl rfl)
        | exact .quotLift (h₁ 0 _ _ rfl rfl) (h₁ 1 _ _ rfl rfl) (h₁ 2 _ _ rfl rfl)
            (h₁ 3 _ _ rfl rfl) (h₁ 4 _ _ rfl rfl) (h₁ 5 _ _ rfl rfl)
        | exact .quotInd (h₁ 0 _ _ rfl rfl) (h₁ 1 _ _ rfl rfl) (h₁ 2 _ _ rfl rfl)
            (h₁ 3 _ _ rfl rfl) (h₁ 4 _ _ rfl rfl)
  | quotEta hu₁ hlt ht₁ =>
    cases h₂ with
    | quotEta hu₂ _ ht₂ =>
      rw [hu₁] at hu₂; cases hu₂
      rw [ht₁] at ht₂; cases ht₂
      exact appList .refl hlen h
    | _ => simp [quotArity] at hlen hlt; omega

end

end


section
variable {E : Metalean.Env ζ} {B : Binds ζ} {lps : List Name}

/-- Two locals lists whose bound and free variables denote congruent terms. -/
def LocCong (E : Metalean.Env ζ) {n : Nat} (Γ₁ Γ₂ : Metalean.Ctx ζ ℓ 0 n) (Δ₁ Δ₂ : MLCtx ζ ℓ n) :
    Prop :=
  (∀ i a b, Δ₁.findB i = some a → Δ₂.findB i = some b → DCong E Γ₁ Γ₂ a b) ∧
  ∀ x a b, Δ₁.findF x = some a → Δ₂.findF x = some b → DCong E Γ₁ Γ₂ a b

/-- Every locals list is congruent to itself. -/
theorem LocCong.refl {n : Nat} {Γ : Metalean.Ctx ζ ℓ 0 n} (Δ : MLCtx ζ ℓ n) : LocCong E Γ Γ Δ Δ :=
  ⟨fun _ _ _ ha hb => by rw [ha] at hb; cases hb; exact .refl,
    fun _ _ _ ha hb => by rw [ha] at hb; cases hb; exact .refl⟩

/-- Entering a binder on both sides. -/
theorem LocCong.pushLam {n : Nat} {Γ₁ Γ₂ : Metalean.Ctx ζ ℓ 0 n} {Δ₁ Δ₂ : MLCtx ζ ℓ n}
    (A₁ A₂ : Metalean.Expr ζ ℓ n) (h : LocCong E Γ₁ Γ₂ Δ₁ Δ₂) :
    LocCong E (Γ₁.snoc A₁) (Γ₂.snoc A₂) (Δ₁.pushLam none) (Δ₂.pushLam none) := by
  constructor
  · intro i a b ha hb
    cases i with
    | zero =>
      simp only [MLCtx.pushLam, MLCtx.findB, MLDecl.denote, Option.some.injEq] at ha hb
      subst ha hb; exact .refl
    | succ i =>
      simp only [MLCtx.pushLam, MLCtx.findB, MLCtx.findB_map_wk, Option.map_eq_some_iff] at ha hb
      obtain ⟨a, ha, rfl⟩ := ha
      obtain ⟨b, hb, rfl⟩ := hb
      exact DCong.wk A₁ A₂ (h.1 i a b ha hb)
  · intro x a b ha hb
    simp only [MLCtx.pushLam, MLCtx.findF, MLCtx.findF_map_wk, Option.map_eq_some_iff] at ha hb
    obtain ⟨a, ha, rfl⟩ := ha
    obtain ⟨b, hb, rfl⟩ := hb
    exact DCong.wk A₁ A₂ (h.2 x a b ha hb)

/-- Pushing congruent `let` values. -/
theorem LocCong.cons {n : Nat} {Γ₁ Γ₂ : Metalean.Ctx ζ ℓ 0 n} {Δ₁ Δ₂ : MLCtx ζ ℓ n}
    {v₁ v₂ : Metalean.Expr ζ ℓ n} (h : LocCong E Γ₁ Γ₂ Δ₁ Δ₂) (hv : DCong E Γ₁ Γ₂ v₁ v₂) :
    LocCong E Γ₁ Γ₂ ((none, .vlet v₁) :: Δ₁) ((none, .vlet v₂) :: Δ₂) := by
  constructor
  · intro i a b ha hb
    cases i with
    | zero =>
      simp only [MLCtx.findB, MLDecl.denote, Option.some.injEq] at ha hb
      subst ha hb; exact hv
    | succ i => exact h.1 i a b (by simpa [MLCtx.findB] using ha) (by simpa [MLCtx.findB] using hb)
  · intro x a b ha hb
    exact h.2 x a b (by simpa [MLCtx.findF] using ha) (by simpa [MLCtx.findF] using hb)

/-- A term whose head is not a constant is no constant spine. -/
theorem ne_mkAppN_const {e : Expr} (he : ∀ c us, e.getAppFn ≠ .const c us) {c : Name}
    {us : List Level} {as : List Expr} : e ≠ mkAppN (.const c us) as.toArray := fun h =>
  he c us (by rw [h, mkAppN_eq_foldl, foldl_app_getAppFn]; rfl)

/-- An application that is a spine of a saturating constant has a saturating head. -/
theorem specialHead_of_app {f a : Expr} {c : Name} {us : List Level} {as : List Expr}
    {b : MBinding ζ} (h : Expr.app f a = mkAppN (.const c us) as.toArray) (hb : B c = some b)
    (hs : b.isSpecial = true) : SpecialHead B f := by
  refine ⟨c, us, b, ?_, hb, hs⟩
  have := congrArg Expr.getAppFn h
  rw [mkAppN_eq_foldl, foldl_app_getAppFn] at this
  exact this

/-- Proof projections of congruent majors whose types fix their levels and parameters. -/
theorem projProof_dcong {ι : Metalean.IndSig} {η : Metalean.Head ζ (.inductive ι)}
    {s : Fin ι.nsorts} {c₁ c₂ : Fin (ι.nctors s)} (hc : ∀ d, d = c₂) {n : Nat}
    {Γ₁ Γ₂ : Metalean.Ctx ζ ℓ 0 n} {ls₁ ls₂ : Fin ι.nlevels → Metalean.Level ℓ}
    {hi₁ hi₂ : ι.nindices s = 0} {ps₁ ps₂ : Fin ι.nparams → Metalean.Expr ζ ℓ n}
    {is₁ is₂ : Fin (ι.nindices s) → Metalean.Expr ζ ℓ n} {f : Nat} {e₁ e₂ : Metalean.Expr ζ ℓ n}
    (hm : DCong E Γ₁ Γ₂ e₁ e₂) (hty₁ : E[Γ₁] ⊢ e₁ : .ind η s ls₁ ps₁ is₁)
    (hty₂ : E[Γ₂] ⊢ e₂ : .ind η s ls₂ ps₂ is₂) :
    DCong E Γ₁ Γ₂ (projProofTerm E η s c₁ ls₁ hi₁ ps₁ f e₁) (projProofTerm E η s c₂ ls₂ hi₂ ps₂ f e₂) := by
  obtain rfl := hc c₁
  exact .byLevels hm hty₁ hty₂ fun hls => by
    subst hls
    exact TrDet.projProofTerm_dcong _ _ _ _ _ _ (fun p => .param p hm hty₁ hty₂) hm

/-- Two translations of one term, in contexts and locals that denote congruent terms, are
congruent. -/
theorem TrM.dcong {n : Nat} {Γ₁ : Metalean.Ctx ζ lps.length 0 n} {Δ₁ : MLCtx ζ lps.length n}
    {e : Expr} {t₁ : Metalean.Expr ζ lps.length n} (h₁ : TrM E B lps Γ₁ Δ₁ e t₁) :
    ∀ {Γ₂ : Metalean.Ctx ζ lps.length 0 n} {Δ₂ : MLCtx ζ lps.length n}
      {t₂ : Metalean.Expr ζ lps.length n},
      TrM E B lps Γ₂ Δ₂ e t₂ → LocCong E Γ₁ Γ₂ Δ₁ Δ₂ → DCong E Γ₁ Γ₂ t₁ t₂ := by
  induction h₁ with
  | bvar hb =>
    intro Γ₂ Δ₂ t₂ h₂ hL
    generalize hx : Expr.bvar _ = x at h₂
    cases h₂ with
    | bvar hb₂ => cases hx; exact hL.1 _ _ _ hb hb₂
    | special => exact absurd hx (ne_mkAppN_const fun _ _ h => by cases h)
    | _ => cases hx
  | fvar hf =>
    intro Γ₂ Δ₂ t₂ h₂ hL
    generalize hx : Expr.fvar _ = x at h₂
    cases h₂ with
    | fvar hf₂ => cases hx; exact hL.2 _ _ _ hf hf₂
    | special => exact absurd hx (ne_mkAppN_const fun _ _ h => by cases h)
    | _ => cases hx
  | sort hl =>
    intro Γ₂ Δ₂ t₂ h₂ hL
    generalize hx : Expr.sort _ = x at h₂
    cases h₂ with
    | sort hl₂ => cases hx; rw [hl] at hl₂; cases hl₂; exact .refl
    | special => exact absurd hx (ne_mkAppN_const fun _ _ h => by cases h)
    | _ => cases hx
  | const hB hl =>
    intro Γ₂ Δ₂ t₂ h₂ hL
    generalize hx : Expr.const _ _ = x at h₂
    cases h₂ with
    | const hB₂ hl₂ =>
      cases hx; rw [hB] at hB₂; cases hB₂; obtain rfl := TrDet.TrLevels.det hl hl₂; exact .refl
    | special hb hs =>
      rw [mkAppN_eq_foldl] at hx
      obtain ⟨rfl, rfl, -⟩ := foldl_app_const_inj (as := []) hx
      rw [hB] at hb; cases hb; cases hs
    | _ => cases hx
  | @special c us _ _ _ as as' b _ hb hs hlen _ hsat ih =>
    intro Γ₂ Δ₂ t₂ h₂ hL
    generalize hx : mkAppN (Expr.const c us) as.toArray = x at h₂
    cases h₂ with
    | const hB₂ =>
      rw [mkAppN_eq_foldl] at hx
      obtain ⟨rfl, rfl, -⟩ := foldl_app_const_inj (as' := []) hx
      rw [hB₂] at hb; cases hb; cases hs
    | special hb₂ _ hlen₂ hargs₂ hsat₂ =>
      rw [mkAppN_eq_foldl, mkAppN_eq_foldl] at hx
      obtain ⟨rfl, rfl, rfl⟩ := foldl_app_const_inj hx
      rw [hb] at hb₂; cases hb₂
      refine SatTr.dcong hsat hsat₂ (hlen.symm.trans hlen₂) fun i a₁ a₂ ha₁ ha₂ => ?_
      obtain ⟨a, ha⟩ : ∃ a, as[i]? = some a := by
        have := (List.getElem?_eq_some_iff.mp ha₁).1
        exact ⟨as[i], List.getElem?_eq_getElem (by omega)⟩
      exact ih i a a₁ ha ha₁ (hargs₂ i a a₂ ha ha₂) hL
    | app hns => exact absurd (specialHead_of_app hx.symm hb hs) hns
    | _ => exact absurd hx.symm (ne_mkAppN_const fun _ _ h => by cases h)
  | app hns _ _ ihf iha =>
    intro Γ₂ Δ₂ t₂ h₂ hL
    generalize hx : Expr.app _ _ = x at h₂
    cases h₂ with
    | app _ hf₂ ha₂ => cases hx; exact .app (ihf hf₂ hL) (iha ha₂ hL)
    | special hb hs => exact absurd (specialHead_of_app hx hb hs) hns
    | _ => cases hx
  | lam _ _ ihA ihb =>
    intro Γ₂ Δ₂ t₂ h₂ hL
    generalize hx : Expr.lam _ _ _ _ = x at h₂
    cases h₂ with
    | lam hA₂ hb₂ => cases hx; exact .lam (ihA hA₂ hL) (ihb hb₂ (hL.pushLam _ _))
    | special => exact absurd hx (ne_mkAppN_const fun _ _ h => by cases h)
    | _ => cases hx
  | forallE _ _ ihA ihb =>
    intro Γ₂ Δ₂ t₂ h₂ hL
    generalize hx : Expr.forallE _ _ _ _ = x at h₂
    cases h₂ with
    | forallE hA₂ hb₂ => cases hx; exact .forallE (ihA hA₂ hL) (ihb hb₂ (hL.pushLam _ _))
    | special => exact absurd hx (ne_mkAppN_const fun _ _ h => by cases h)
    | _ => cases hx
  | letE _ _ _ ihT ihv ihb =>
    intro Γ₂ Δ₂ t₂ h₂ hL
    generalize hx : Expr.letE _ _ _ _ _ = x at h₂
    cases h₂ with
    | letE hT₂ hv₂ hb₂ =>
      cases hx
      have hv := ihv hv₂ hL
      refine .letE (ihT hT₂ hL) hv ?_
      rw [Metalean.Expr.inst_wk, Metalean.Expr.inst_wk]
      exact ihb hb₂ (hL.cons hv)
    | special => exact absurd hx (ne_mkAppN_const fun _ _ h => by cases h)
    | _ => cases hx
  | mdata _ ih =>
    intro Γ₂ Δ₂ t₂ h₂ hL
    generalize hx : Expr.mdata _ _ = x at h₂
    cases h₂ with
    | mdata h₂ => cases hx; exact ih h₂ hL
    | special => exact absurd hx (ne_mkAppN_const fun _ _ h => by cases h)
    | _ => cases hx
  | lit hB =>
    intro Γ₂ Δ₂ t₂ h₂ hL
    generalize hx : Expr.lit _ = x at h₂
    cases h₂ with
    | lit hB₂ => cases hx; rw [hB] at hB₂; cases hB₂; exact .refl
    | special => exact absurd hx (ne_mkAppN_const fun _ _ h => by cases h)
    | _ => cases hx
  | projStruct hst hi hS _ hty ih =>
    intro Γ₂ Δ₂ t₂ h₂ hL
    generalize hx : Expr.proj _ _ _ = x at h₂
    cases h₂ with
    | projStruct hst₂ hi₂ hS₂ he₂ hty₂ =>
      cases hx; rw [hS] at hS₂; cases hS₂
      exact .projStruct hst hst₂ _ _ rfl (ih he₂ hL) hty hty₂
    | projProof _ hS₂ _ hc₂ _ _ hns₂ =>
      cases hx; rw [hS] at hS₂; cases hS₂
      exact absurd (hc₂ _ ▸ hst) hns₂
    | special => exact absurd hx (ne_mkAppN_const fun _ _ h => by cases h)
    | _ => cases hx
  | projProof hi hS _ hc _ _ hns _ hty ih =>
    intro Γ₂ Δ₂ t₂ h₂ hL
    generalize hx : Expr.proj _ _ _ = x at h₂
    cases h₂ with
    | projStruct hst₂ _ hS₂ =>
      cases hx; rw [hS] at hS₂; cases hS₂
      exact absurd (hc _ ▸ hst₂) hns
    | projProof _ hS₂ _ hc₂ _ _ _ he₂ hty₂ =>
      cases hx; rw [hS] at hS₂; cases hS₂
      exact projProof_dcong hc₂ (ih he₂ hL) hty hty₂
    | special => exact absurd hx (ne_mkAppN_const fun _ _ h => by cases h)
    | _ => cases hx


/-- Two translations typed at `T` are definitionally equal at `T` (projections choose their levels
and parameters by typing). Reference: lean4lean `TrExprS.uniq`; `Defeq.uniqTy`
(`ML Metatheory/Unique.lean:149`). -/
theorem TrM.det {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    {e : Expr} {t₁ t₂ T : Metalean.Expr ζ lps.length n} (hE : EnvWF E) (hΓ : E[Γ] ⊢ ok)
    (h₁ : TrM E B lps Γ Δ e t₁) (h₂ : TrM E B lps Γ Δ e t₂) (ht₁ : E[Γ] ⊢ t₁ : T)
    (_ht₂ : E[Γ] ⊢ t₂ : T) : E[Γ] ⊢ t₁ ≡ t₂ : T :=
  DCong.defeq hE (h₁.dcong h₂ (LocCong.refl Δ)) hΓ (DCong.CtxConv.refl hΓ) ht₁

end

end EraseProof
