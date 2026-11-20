import EraseProof.Relation.Basic
import EraseProof.Source.Marks

/-!
# Reading a marking

`MarkOf decls cfg ls e ê` marks the input `e` as the traversal erases it. `unmark ê` is `e` with
some of its metadata removed (`DropMD`: `MarkOf` drops the metadata of the nodes the traversal
visits and keeps the rest of `e`), so con-leche reads `unmark ê` as it reads `e` (`toCL?` is
transparent to metadata), and every `eta` mark of `ê` sits on a λ (`EtaLams`). Both need that `e`
carries no mark key (`NoMarkKeys`), and so do the types the oracle returns, from which `MarkOf`
takes the domains of the η-introduced binders: the oracle (`Erasure.Pure.whnf`,
`Erasure.Pure.inferType`) builds them from the declarations, the locals and the term
(`MarkRead.whnf_clean`, `MarkRead.inferType_clean`), so neither the declarations' types and values
(`NoMarkKeysDecls`, which con-leche's input `DeclsOf?` requires of the program) nor the locals carry
a mark key either.
-/

open Lean Erasure

namespace EraseProof

/-- `e'` is `e` with some of its `mdata` nodes removed: at the nodes `MarkOf` visits (the binder
domains and the types it keeps stay as they are). Reference: none (DV-32). -/
inductive DropMD : Expr → Expr → Prop
  | refl (e : Expr) : DropMD e e
  | drop {m : MData} {e e' : Expr} : DropMD e e' → DropMD (.mdata m e) e'
  | app {f f' a a' : Expr} : DropMD f f' → DropMD a a' → DropMD (.app f a) (.app f' a')
  | lam {n : Name} {t b b' : Expr} {bi : BinderInfo} : DropMD b b' →
      DropMD (.lam n t b bi) (.lam n t b' bi)
  | letE {n : Name} {t v v' b b' : Expr} {nd : Bool} : DropMD v v' → DropMD b b' →
      DropMD (.letE n t v b nd) (.letE n t v' b' nd)
  | proj {s : Name} {i : Nat} {e e' : Expr} : DropMD e e' → DropMD (.proj s i e) (.proj s i e')

/-- con-leche reads a term with metadata removed as the term. Reference: none. -/
theorem DropMD.toCL {e e' : Expr} (h : DropMD e e') : toCL? e' = toCL? e := by
  induction h with
  | refl => rfl
  | drop _ ih => exact ih
  | app _ _ ih₁ ih₂ | letE _ _ ih₁ ih₂ => simp only [toCL?, ih₁, ih₂]
  | lam _ ih | proj _ ih => simp only [toCL?, ih]

/-- Removing metadata commutes with closing a binder. Reference: none. -/
theorem DropMD.absFV {x : FVarId} {e e' : Expr} {d : Nat} (h : DropMD e e') :
    DropMD (absFV x d e) (absFV x d e') := by
  induction h generalizing d with
  | refl => exact .refl _
  | drop _ ih => exact .drop ih
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂
  | lam _ ih => exact .lam ih
  | letE _ _ ih₁ ih₂ => exact .letE ih₁ ih₂
  | proj _ ih => exact .proj ih

/-- Removing metadata removes no free variable's occurrence but its own. Reference: none. -/
theorem DropMD.fvarsIn {p : FVarId → Prop} {e e' : Expr} (h : DropMD e e') (hp : FVarsIn p e) :
    FVarsIn p e' := by
  induction h with
  | refl => exact hp
  | drop _ ih => exact ih hp
  | app _ _ ih₁ ih₂ => exact ⟨ih₁ hp.1, ih₂ hp.2⟩
  | lam _ ih => exact ⟨hp.1, ih hp.2⟩
  | letE _ _ ih₁ ih₂ => exact ⟨hp.1, ih₁ hp.2.1, ih₂ hp.2.2⟩
  | proj _ ih => exact ih hp

/-- An application with metadata removed is an application. Reference: none. -/
theorem DropMD.app_inv {f a u : Expr} (h : DropMD (.app f a) u) :
    ∃ f' a', u = .app f' a' ∧ DropMD f f' ∧ DropMD a a' := by
  cases h with
  | refl => exact ⟨f, a, rfl, .refl _, .refl _⟩
  | app h₁ h₂ => exact ⟨_, _, rfl, h₁, h₂⟩

/-- A variable with metadata removed is the variable. Reference: none. -/
theorem DropMD.fvar_inv {x : FVarId} {u : Expr} (h : DropMD (.fvar x) u) : u = .fvar x := by
  cases h; rfl

namespace MarkRead

/-! ## Closing a binder -/

/-- Abstraction inverts instantiation by a variable that does not occur. Port of
`ML-V Bridge/Abstract.lean:34 AbsFV.absFV_inst`. -/
theorem absFV_inst {x : FVarId} : ∀ {b : Expr} {d : Nat}, FVarsIn (· ≠ x) b →
    absFV x d (b.instantiate1' (.fvar x) d) = b
  | .bvar i, d, _ => by
    by_cases h₁ : i < d
    · simp [Expr.instantiate1', absFV, h₁]
    · by_cases h₂ : i = d
      · subst h₂; simp [Expr.instantiate1', Expr.liftLooseBVars', absFV, fvarId_beq_iff]
      · simp only [Expr.instantiate1', h₁, h₂, ↓reduceIte, absFV, Expr.bvar.injEq]
        split <;> omega
  | .fvar y, d, h => by
    have hy : (y == x) = false := Bool.eq_false_iff.mpr fun h' => h ((fvarId_beq_iff y x).mp h')
    simp [Expr.instantiate1', absFV, hy]
  | .app f a, d, h => by simp [Expr.instantiate1', absFV, absFV_inst h.1, absFV_inst h.2]
  | .lam _ t b _, d, h => by simp [Expr.instantiate1', absFV, absFV_inst h.1, absFV_inst h.2]
  | .forallE _ t b _, d, h => by simp [Expr.instantiate1', absFV, absFV_inst h.1, absFV_inst h.2]
  | .letE _ t v b _, d, h => by
    simp [Expr.instantiate1', absFV, absFV_inst h.1, absFV_inst h.2.1, absFV_inst h.2.2]
  | .mdata _ e, d, h => by simp [Expr.instantiate1', absFV, absFV_inst (b := e) h]
  | .proj _ _ e, d, h => by simp [Expr.instantiate1', absFV, absFV_inst (b := e) h]
  | .sort _, _, _ | .const .., _, _ | .lit _, _, _ | .mvar _, _, _ => rfl

/-- Abstracting an absent variable lifts. Reference: none. -/
theorem absFV_absent {x : FVarId} : ∀ {e : Expr} {d : Nat}, FVarsIn (· ≠ x) e →
    absFV x d e = e.liftLooseBVars' d 1
  | .bvar _, _, _ => rfl
  | .fvar y, d, h => by
    have hy : (y == x) = false := Bool.eq_false_iff.mpr fun h' => h ((fvarId_beq_iff y x).mp h')
    simp [absFV, Expr.liftLooseBVars', hy]
  | .app f a, _, h => by simp [absFV, Expr.liftLooseBVars', absFV_absent h.1, absFV_absent h.2]
  | .lam _ t b _, _, h | .forallE _ t b _, _, h => by
    simp [absFV, Expr.liftLooseBVars', absFV_absent h.1, absFV_absent h.2]
  | .letE _ t v b _, _, h => by
    simp [absFV, Expr.liftLooseBVars', absFV_absent h.1, absFV_absent h.2.1, absFV_absent h.2.2]
  | .mdata _ e, _, h | .proj _ _ e, _, h => by
    simp [absFV, Expr.liftLooseBVars', absFV_absent (e := e) h]
  | .sort _, _, _ | .const .., _, _ | .lit _, _, _ | .mvar _, _, _ => rfl

/-- Lifting by nothing is the identity. Reference: none. -/
theorem lift_zero : ∀ (e : Expr) (s : Nat), e.liftLooseBVars' s 0 = e := by
  intro e; induction e <;> intro s <;> simp_all [Expr.liftLooseBVars']

/-- Abstracting at `d` does not change whether an index below `d` occurs. Reference: none. -/
theorem bvarOccurs_absFV {x : FVarId} : ∀ (e : Expr) {d k : Nat}, k < d →
    bvarOccurs k (absFV x d e) = bvarOccurs k e
  | .bvar i, d, k, h => by
    by_cases h₁ : i < d
    · simp [absFV, h₁]
    · simp [absFV, bvarOccurs, h₁, Marks.nat_beq_false (show i + 1 ≠ k by omega),
        Marks.nat_beq_false (show i ≠ k by omega)]
  | .fvar y, d, k, h => by
    by_cases hy : (y == x) = true
    · simp [absFV, bvarOccurs, hy, Marks.nat_beq_false (show d ≠ k by omega)]
    · simp [absFV, bvarOccurs, hy]
  | .app f a, _, _, h => by simp [absFV, bvarOccurs, bvarOccurs_absFV f h, bvarOccurs_absFV a h]
  | .lam _ t b _, d, k, h | .forallE _ t b _, d, k, h => by
    simp [absFV, bvarOccurs, bvarOccurs_absFV t h,
      bvarOccurs_absFV b (d := d + 1) (k := k + 1) (by omega)]
  | .letE _ t v b _, d, k, h => by
    simp [absFV, bvarOccurs, bvarOccurs_absFV t h, bvarOccurs_absFV v h,
      bvarOccurs_absFV b (d := d + 1) (k := k + 1) (by omega)]
  | .mdata _ e, _, _, h | .proj _ _ e, _, _, h => by
    simp [absFV, bvarOccurs, bvarOccurs_absFV e h]
  | .sort _, _, _, _ | .const .., _, _, _ | .lit _, _, _, _ | .mvar _, _, _, _ => rfl

/-- Lowering past an absent index `k` (the contraction of `etaContract`) commutes with abstracting
above it. Reference: none. -/
theorem lower_absFV {x : FVarId} : ∀ (f : Expr) {d k : Nat}, k ≤ d → bvarOccurs k f = false →
    (absFV x (d + 1) f).instantiate1' (.bvar 0) k = absFV x d (f.instantiate1' (.bvar 0) k)
  | .bvar i, d, k, h, hk => by
    simp only [bvarOccurs, beq_eq_false_iff_ne] at hk
    by_cases h₁ : i < k
    · simp [absFV, Expr.instantiate1', h₁, show i < d + 1 by omega, show i < d by omega]
    · by_cases h₂ : i < d + 1
      · simp [absFV, Expr.instantiate1', h₁, h₂, hk, show i - 1 < d by omega]
      · simp only [absFV, Expr.instantiate1', h₁, h₂, hk, ↓reduceIte,
          show ¬ i + 1 < k by omega, show ¬ i + 1 = k by omega, show ¬ i - 1 < d by omega,
          Expr.bvar.injEq]
        omega
  | .fvar y, d, k, h, _ => by
    by_cases hy : (y == x) = true
    · simp [absFV, Expr.instantiate1', hy, show ¬ d + 1 < k by omega, show ¬ d + 1 = k by omega]
    · simp [absFV, Expr.instantiate1', hy]
  | .app f b, _, _, h, hk => by
    simp only [bvarOccurs, Bool.or_eq_false_iff] at hk
    simp [absFV, Expr.instantiate1', lower_absFV f h hk.1, lower_absFV b h hk.2]
  | .lam _ t b _, d, k, h, hk | .forallE _ t b _, d, k, h, hk => by
    simp only [bvarOccurs, Bool.or_eq_false_iff] at hk
    simp [absFV, Expr.instantiate1', lower_absFV t h hk.1,
      lower_absFV b (d := d + 1) (k := k + 1) (by omega) hk.2]
  | .letE _ t v b _, d, k, h, hk => by
    simp only [bvarOccurs, Bool.or_eq_false_iff] at hk
    simp [absFV, Expr.instantiate1', lower_absFV t h hk.1.1, lower_absFV v h hk.1.2,
      lower_absFV b (d := d + 1) (k := k + 1) (by omega) hk.2]
  | .mdata _ e, _, _, h, hk | .proj _ _ e, _, _, h, hk => by
    simp only [bvarOccurs] at hk
    simp [absFV, Expr.instantiate1', lower_absFV e h hk]
  | .sort _, _, _, _, _ | .const .., _, _, _, _ | .lit _, _, _, _, _ | .mvar _, _, _, _, _ => rfl

/-- Abstraction creates no η-shape. Reference: none. -/
theorem etaShape_of_absFV {x : FVarId} {d : Nat} {e : Expr} (h : Marks.EtaShape (absFV x d e)) :
    Marks.EtaShape e := by
  obtain ⟨m, t, f, bi, he⟩ := h
  cases e with
  | lam n t' b bi' =>
    simp only [absFV, Expr.lam.injEq] at he
    obtain ⟨-, -, hb, -⟩ := he
    cases b with
    | app g c =>
      simp only [absFV, Expr.app.injEq] at hb
      obtain ⟨-, hc⟩ := hb
      cases c with
      | bvar i =>
        simp only [absFV, Expr.bvar.injEq] at hc
        have : i = 0 := by split at hc <;> omega
        subst this; exact ⟨_, _, _, _, rfl⟩
      | fvar y => simp only [absFV] at hc; split at hc <;> simp at hc
      | _ => simp [absFV] at hc
    | fvar y => simp only [absFV] at hb; split at hb <;> simp at hb
    | _ => simp [absFV] at hb
  | fvar y => simp only [absFV] at he; split at he <;> simp at he
  | _ => simp [absFV] at he

/-- `etaContract` commutes with abstraction. Reference: none. -/
theorem etaContract_absFV (x : FVarId) (e : Expr) (d : Nat) :
    etaContract (absFV x d e) = absFV x d (etaContract e) := by
  by_cases h : Marks.EtaShape e
  · obtain ⟨m, t, f, bi, rfl⟩ := h
    rw [show absFV x d (.lam m t (.app f (.bvar 0)) bi) =
      .lam m (absFV x d t) (.app (absFV x (d + 1) f) (.bvar 0)) bi by simp [absFV]]
    simp only [etaContract, bvarOccurs_absFV f (show 0 < d + 1 by omega)]
    cases hf : bvarOccurs 0 f
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact lower_absFV f (Nat.zero_le d) hf
    · simp [absFV]
  · rw [Marks.etaContract_of_not h, Marks.etaContract_of_not (fun h' => h (etaShape_of_absFV h'))]

/-- `unmark` commutes with abstraction. Reference: none (DV-32). -/
theorem unmark_absFV (x : FVarId) : ∀ (e : Expr) (d : Nat),
    unmark (absFV x d e) = absFV x d (unmark e)
  | .mdata m e, d => by
    simp only [absFV, unmark]
    split
    · exact unmark_absFV x e d
    · exact unmark_absFV x e d
    · rw [unmark_absFV x e d, etaContract_absFV]
    · simp only [absFV, unmark_absFV x e d]
  | .app f a, d => by simp only [absFV, unmark, unmark_absFV x f, unmark_absFV x a]
  | .lam _ t b _, d | .forallE _ t b _, d => by
    simp only [absFV, unmark, unmark_absFV x t, unmark_absFV x b]
  | .letE _ t v b _, d => by
    simp only [absFV, unmark, unmark_absFV x t, unmark_absFV x v, unmark_absFV x b]
  | .proj _ _ e, d => by simp only [absFV, unmark, unmark_absFV x e]
  | .fvar y, d => by
    show unmark (absFV x d (.fvar y)) = absFV x d (.fvar y)
    simp only [absFV]; split <;> rfl
  | .bvar _, _ | .mvar _, _ | .sort _, _ | .const .., _ | .lit _, _ => rfl

/-- Abstraction keeps the λs. Reference: none. -/
theorem isLambda_absFV {x : FVarId} {d : Nat} : ∀ e : Expr, (absFV x d e).isLambda = e.isLambda
  | .fvar y => by simp only [absFV]; split <;> rfl
  | .bvar _ | .mvar _ | .sort _ | .const .. | .lit _ | .app .. | .lam .. | .forallE .. | .letE ..
  | .mdata .. | .proj .. => rfl

/-- Abstraction keeps every `eta` mark on a λ. Reference: none (DV-23). -/
theorem etaLams_absFV {x : FVarId} : ∀ {e : Expr} {d : Nat}, EtaLams e → EtaLams (absFV x d e)
  | .mdata _ e, _, h => ⟨fun hm => (isLambda_absFV e).trans (h.1 hm), etaLams_absFV h.2⟩
  | .app _ _, _, h => ⟨etaLams_absFV h.1, etaLams_absFV h.2⟩
  | .lam _ _ _ _, _, h | .forallE _ _ _ _, _, h => ⟨etaLams_absFV h.1, etaLams_absFV h.2⟩
  | .letE _ _ _ _ _, _, h => ⟨etaLams_absFV h.1, etaLams_absFV h.2.1, etaLams_absFV h.2.2⟩
  | .proj _ _ e, _, h => etaLams_absFV (e := e) h
  | .fvar y, d, _ => by simp only [absFV]; split <;> trivial
  | .bvar _, _, _ | .mvar _, _, _ | .sort _, _, _ | .const .., _, _ | .lit _, _, _ => trivial

/-! ## Terms without mark keys -/

/-- Lifting adds no mark key. Reference: none. -/
theorem clean_lift : ∀ {e : Expr} {s n : Nat}, NoMarkKeys e = true →
    NoMarkKeys (e.liftLooseBVars' s n) = true := by
  intro e; induction e <;> intro s n h <;> simp_all [Expr.liftLooseBVars', NoMarkKeys] <;> exact h.1

/-- Instantiation adds no mark key. Reference: none. -/
theorem clean_inst {a : Expr} (ha : NoMarkKeys a = true) : ∀ {b : Expr} {d : Nat},
    NoMarkKeys b = true → NoMarkKeys (b.instantiate1' a d) = true := by
  intro b
  induction b with
  | bvar i =>
    intro d _
    simp only [Expr.instantiate1']
    split
    · rfl
    · split
      · exact clean_lift ha
      · rfl
  | _ => intro d h; simp_all [Expr.instantiate1', NoMarkKeys] <;> exact h.1

/-- Universe instantiation adds no mark key. Reference: none. -/
theorem clean_instLevels (ps : List Name) (us : List Level) : ∀ {e : Expr},
    NoMarkKeys e = true → NoMarkKeys (Pure.instLevels ps us e) = true := by
  intro e; induction e <;> intro h <;> simp_all [Pure.instLevels, NoMarkKeys] <;> exact h.1

/-- The mark keys of an application spine are those of its parts. Reference: none. -/
theorem clean_foldl : ∀ (as : List Expr) (f : Expr),
    NoMarkKeys (as.foldl .app f) = (NoMarkKeys f && as.all NoMarkKeys)
  | [], f => by simp
  | a :: as, f => by simp [clean_foldl as, NoMarkKeys, Bool.and_assoc]

/-- `clean_foldl` on `mkAppN`. Reference: none. -/
theorem clean_mkAppN {f : Expr} {as : List Expr} : NoMarkKeys (mkAppN f as.toArray) = true ↔
    NoMarkKeys f = true ∧ ∀ a ∈ as, NoMarkKeys a = true := by
  simp [mkAppN_toArray, clean_foldl]

/-- The arguments `spine` reads off a term carry no mark key if the term carries none.
Reference: none. -/
theorem clean_spine : ∀ {e : Expr}, NoMarkKeys e = true → ∀ a ∈ (spine e).2, NoMarkKeys a = true
  | .app f x, h => by
    simp only [NoMarkKeys, Bool.and_eq_true] at h
    simp only [spine, List.mem_append, List.mem_singleton]
    rintro a (ha | rfl)
    · exact clean_spine h.1 a ha
    · exact h.2
  | .bvar _, _ | .fvar _, _ | .mvar _, _ | .sort _, _ | .const .., _ | .lam .., _ | .forallE .., _
  | .letE .., _ | .lit _, _ | .mdata .., _ | .proj .., _ => by simp [spine]

/-- Without mark keys `unmark` is the identity. Reference: none. -/
theorem unmark_clean : ∀ {e : Expr}, NoMarkKeys e = true → unmark e = e
  | .mdata d e, h => by
    simp only [NoMarkKeys, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false] at h
    simp only [unmark]
    split
    · simp at h
    · simp at h
    · simp at h
    · rw [unmark_clean h.2]
  | .app f a, h => by
    simp only [NoMarkKeys, Bool.and_eq_true] at h
    simp only [unmark, unmark_clean h.1, unmark_clean h.2]
  | .lam _ t b _, h | .forallE _ t b _, h => by
    simp only [NoMarkKeys, Bool.and_eq_true] at h
    simp only [unmark, unmark_clean h.1, unmark_clean h.2]
  | .letE _ t v b _, h => by
    simp only [NoMarkKeys, Bool.and_eq_true] at h
    simp only [unmark, unmark_clean h.1.1, unmark_clean h.1.2, unmark_clean h.2]
  | .proj _ _ e, h => by simp only [unmark, unmark_clean (e := e) h]
  | .bvar _, _ | .fvar _, _ | .mvar _, _ | .sort _, _ | .const .., _ | .lit _, _ => rfl

/-- Without mark keys there is no `eta` mark. Reference: none. -/
theorem etaLams_clean : ∀ {e : Expr}, NoMarkKeys e = true → EtaLams e
  | .mdata d e, h => by
    simp only [NoMarkKeys, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false] at h
    exact ⟨fun hd => absurd rfl (h.1 (.anonymous, .ofNat 1) (by simp [hd, markMD])),
      etaLams_clean h.2⟩
  | .app f a, h | .lam _ f a _, h | .forallE _ f a _, h => by
    simp only [NoMarkKeys, Bool.and_eq_true] at h
    exact ⟨etaLams_clean h.1, etaLams_clean h.2⟩
  | .letE _ t v b _, h => by
    simp only [NoMarkKeys, Bool.and_eq_true] at h
    exact ⟨etaLams_clean h.1.1, etaLams_clean h.1.2, etaLams_clean h.2⟩
  | .proj _ _ e, h => etaLams_clean (e := e) h
  | .bvar _, _ | .fvar _, _ | .mvar _, _ | .sort _, _ | .const .., _ | .lit _, _ => trivial

/-- The free variables of an application spine are those of its parts. Reference: none. -/
theorem fvarsIn_foldl {p : FVarId → Prop} : ∀ {as : List Expr} {f : Expr}, FVarsIn p f →
    (∀ a ∈ as, FVarsIn p a) → FVarsIn p (as.foldl .app f)
  | [], _, hf, _ => hf
  | a :: as, f, hf, has => fvarsIn_foldl (p := p) (as := as) (f := .app f a)
      ⟨hf, has a (List.mem_cons_self ..)⟩ fun b hb => has b (List.mem_cons_of_mem _ hb)

/-! ## The oracle's results carry no mark key -/

/-- The locals carry no mark key in their types and values. Reference: none. -/
def CleanLocals (ls : List Local) : Prop :=
  ∀ l ∈ ls, NoMarkKeys l.type = true ∧ ∀ v, l.value? = some v → NoMarkKeys v = true

/-- A clean local added to clean locals. Reference: none. -/
theorem cleanLocals_cons {x : FVarId} {n : Name} {T : Expr} {val : Option Expr} {ls : List Local}
    (hT : NoMarkKeys T = true) (hv : ∀ v, val = some v → NoMarkKeys v = true)
    (hl : CleanLocals ls) : CleanLocals (⟨x, n, T, val⟩ :: ls) := by
  intro l hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact ⟨hT, hv⟩
  · exact hl l hm

/-- The type and the value of a declaration of clean declarations are clean. Reference:
none. -/
theorem decl_clean {decls : List ConstantInfo} (hd : NoMarkKeysDecls decls = true) {c : Name}
    {ci : ConstantInfo} (h : decls.find? (·.name == c) = some ci) :
    NoMarkKeys ci.type = true ∧ ∀ v, ci.value? true = some v → NoMarkKeys v = true := by
  have := List.all_eq_true.mp hd ci (List.mem_of_find?_eq_some h)
  simp only [Bool.and_eq_true] at this
  refine ⟨this.1, fun v hv => ?_⟩
  rw [hv] at this; simpa using this.2

/-- Port of `ML-V Oracle/Whnf.lean:71 OracleWhnf.ok_of_bind`. -/
theorem ok_of_bind {α β ε : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  rcases x with e | a
  · cases h
  · exact ⟨a, rfl, h⟩

/-- Port of `ML-V Oracle/Agree.lean:102 OracleAgree.throw_ne_ok`. -/
theorem throw_ne_ok {α : Type} {e : EraseError} {a : α} :
    (throw e : Except EraseError α) ≠ .ok a := by
  simp [throw, throwThe, MonadExceptOf.throw]

/-- Port of `ML-V Oracle/Agree.lean:109 OracleAgree.mem_of_mapM`. -/
theorem mem_of_mapM {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM f = some r → ∀ y ∈ r, ∃ x ∈ l, f x = some y
  | [], r, h, y, hy => by simp at h; subst h; cases hy
  | x :: l, r, h, y, hy => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨z, hz, zs, hzs, rfl⟩ := h
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨x, List.mem_cons_self .., hz⟩
    · obtain ⟨x', hx', h'⟩ := mem_of_mapM hzs y hy
      exact ⟨x', List.mem_cons_of_mem _ hx', h'⟩

/-- Port of `ML-V Oracle/Whnf.lean:134 OracleWhnf.list_mapM_map`. -/
theorem list_mapM_map {α β γ : Type} (g : α → Option β) (k : β → γ) :
    ∀ (l : List α), (l.mapM fun x => (g x).map k) = (l.mapM g).map (List.map k)
  | [] => rfl
  | x :: l => by
    simp only [List.mapM_cons, list_mapM_map g k l]
    cases g x <;> cases l.mapM g <;> rfl

/-- What `Erasure.Pure.iotaRhs?` reads and builds. Port of
`ML-V Oracle/Whnf.lean:142 OracleWhnf.iotaRhs?_spec`. -/
theorem iotaRhs?_spec {decls : List ConstantInfo} {r : Name} {us : List Level} {rv : RecursorVal}
    {minors : List RecMinor} {args : List Expr} {t e : Expr}
    (h : Pure.iotaRhs? decls r us rv minors args t = some e) :
    ∃ C uC cargs cv mi mk rfs, spine t = (.const C uC, cargs) ∧
      findConst decls C = some (.ctorInfo cv) ∧ rv.all = [cv.induct] ∧
      cargs.length = cv.numParams + cv.numFields ∧ minors[cv.cidx]? = some mi ∧
      ((args.take (rv.numParams + rv.numMotives + rv.numMinors)).drop
        (rv.numParams + rv.numMotives))[cv.cidx]? = some mk ∧
      (mi.ihs.mapM fun h => (cargs.drop cv.numParams)[h.field]?) = some rfs ∧
      e = mkAppN mk (cargs.drop cv.numParams ++ rfs.map fun f => mkAppN (.const r us)
        (args.take (rv.numParams + rv.numMotives + rv.numMinors) ++ [f]).toArray).toArray := by
  unfold Pure.iotaRhs? at h
  split at h
  · rename_i C uC cargs hsp
    split at h
    · rename_i cv hC
      by_cases g1 : (rv.all == [cv.induct] && cargs.length == cv.numParams + cv.numFields) = true
      · simp only [g1, guard, ite_true, pure, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨_, -, mi, hmi, mk, hmk, ihs, hihs, he⟩ := h
        rw [list_mapM_map] at hihs
        obtain ⟨rfs, hrfs, rfl⟩ := Option.map_eq_some_iff.mp hihs
        simp only [Bool.and_eq_true, beq_iff_eq] at g1
        exact ⟨C, uC, cargs, cv, mi, mk, rfs, hsp, hC, g1.1, g1.2, hmi, hmk, hrfs,
          (Option.some.inj he).symm⟩
      · simp [g1, guard, failure] at h
    · cases h
  · cases h

/-- What `Erasure.Pure.iotaApp?` checks of an application. Port of
`ML-V Oracle/Whnf.lean:171 OracleWhnf.iotaApp?_spec`. -/
theorem iotaApp?_spec {decls : List ConstantInfo} {e : Expr} {r : Name} {us : List Level}
    {rv : RecursorVal} {minors : List RecMinor} {args : List Expr}
    (h : Pure.iotaApp? decls e = some (r, us, rv, minors, args)) :
    spine e = (.const r us, args) ∧ findConst decls r = some (.recInfo rv) := by
  unfold Pure.iotaApp? at h
  split at h
  · rename_i r' us' args' hsp
    split at h
    · rename_i rv' hr
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨_, -, h⟩ := h
      by_cases g : (args'.length == rv'.numParams + rv'.numMotives + rv'.numMinors + 1) = true
      · simp only [g, guard, ite_true, pure] at h
        obtain ⟨_, -, h⟩ := h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, -, rfl⟩ := h
        exact ⟨hsp, hr⟩
      · simp [g, guard, failure] at h
    · cases h
  · cases h

/-- A successful `whnf` of an application. Port of `ML-V Oracle/Whnf.lean:197
OracleWhnf.whnf_app_cases`, with what the ι-rule reads only. -/
theorem whnf_app_cases {cx : Pure.Ctx} {f : Nat} {ls : List Local} {g a w : Expr}
    (h : Pure.whnf cx (f + 1) ls (.app g a) = .ok w) :
    ∃ g', Pure.whnf cx f ls g = .ok g' ∧
      ((∃ n t b bi, g' = .lam n t b bi ∧ Pure.whnf cx f ls (b.instantiate1' a) = .ok w) ∨
        w = .app g' a ∨
        ∃ r us args rv minors wa e, spine (.app g' a) = (.const r us, args) ∧
          findConst cx.decls r = some (.recInfo rv) ∧ Pure.whnf cx f ls a = .ok wa ∧ Pure.iotaRhs? cx.decls r us rv minors args wa = some e ∧
          Pure.whnf cx f ls e = .ok w) := by
  simp only [Pure.whnf] at h
  obtain ⟨g', h1, h2⟩ := ok_of_bind h
  refine ⟨g', h1, ?_⟩
  split at h2
  · exact .inl ⟨_, _, _, _, rfl, h2⟩
  have refl : (pure (Expr.app g' a) : Except EraseError Expr) = .ok w → w = .app g' a :=
    fun h' => by simpa [pure, Except.pure] using h'.symm
  split at h2
  · rename_i r us rv minors args hia
    obtain ⟨wa, h3, h4⟩ := ok_of_bind h2
    split at h4
    · rename_i e he
      obtain ⟨hsp, hr⟩ := iotaApp?_spec hia
      exact .inr (.inr ⟨r, us, args, rv, minors, wa, e, hsp, hr, h3, he, h4⟩)
    · exact .inr (.inl (refl h4))
  · exact .inr (.inl (refl h2))

/-- The term the ι-rule of `Erasure.Pure.whnf` builds carries no mark key. Adapted from
`ML-V Oracle/Agree.lean:123 OracleAgree.iotaRhs_fvarsIn`. -/
theorem iotaRhs_clean {decls : List ConstantInfo} {r : Name} {us : List Level} {rv : RecursorVal}
    {minors : List RecMinor} {args : List Expr} {t e : Expr}
    (hargs : ∀ a ∈ args, NoMarkKeys a = true) (ht : NoMarkKeys t = true)
    (h : Pure.iotaRhs? decls r us rv minors args t = some e) : NoMarkKeys e = true := by
  obtain ⟨C, uC, cargs, cv, mi, mk, rfs, hspw, -, -, -, -, hmk, hrfs, rfl⟩ := iotaRhs?_spec h
  have hcargs : ∀ a ∈ cargs, NoMarkKeys a = true := by
    have := clean_spine ht; rw [hspw] at this; exact this
  have hfs : ∀ a ∈ cargs.drop cv.numParams, NoMarkKeys a = true :=
    fun a ha => hcargs a (List.mem_of_mem_drop ha)
  refine clean_mkAppN.mpr ⟨hargs mk (List.mem_of_mem_take (List.mem_of_mem_drop
    (List.mem_of_getElem? hmk))), fun a ha => ?_⟩
  rcases List.mem_append.mp ha with ha | ha
  · exact hfs a ha
  · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp ha
    refine clean_mkAppN.mpr ⟨rfl, fun b hb => ?_⟩
    rcases List.mem_append.mp hb with hb | hb
    · exact hargs b (List.mem_of_mem_take hb)
    · rw [List.mem_singleton] at hb
      subst hb
      obtain ⟨_, -, hh⟩ := mem_of_mapM hrfs _ hf
      exact hfs _ (List.mem_of_getElem? hh)

section
variable {cx : Pure.Ctx} {ls : List Local} (hd : NoMarkKeysDecls cx.decls = true)
  (hls : CleanLocals ls)
include hd hls

/-- `Erasure.Pure.whnf` builds its result from the term, the locals' values, the declarations'
values and instantiation, so it carries no mark key if they carry none. Reference: none. -/
theorem whnf_clean : ∀ (f : Nat) {e w : Expr}, NoMarkKeys e = true →
    Pure.whnf cx f ls e = .ok w → NoMarkKeys w = true
  | 0, _, _, _, h => absurd h throw_ne_ok
  | f + 1, .app g a, w, he, h => by
    simp only [NoMarkKeys, Bool.and_eq_true] at he
    obtain ⟨g', h1, h2⟩ := whnf_app_cases h
    have hg' := whnf_clean f he.1 h1
    have hga : NoMarkKeys (.app g' a) = true := by simp [NoMarkKeys, hg', he.2]
    rcases h2 with ⟨n, t, b, bi, rfl, h2⟩ | rfl |
      ⟨r, us, args, rv, minors, wa, e, hsp, -, hwa, he', hw⟩
    · simp only [NoMarkKeys, Bool.and_eq_true] at hg'
      exact whnf_clean f (clean_inst he.2 hg'.2) h2
    · exact hga
    · have hargs : ∀ x ∈ args, NoMarkKeys x = true := by
        have := clean_spine hga; rw [hsp] at this; exact this
      exact whnf_clean f (iotaRhs_clean hargs (whnf_clean f he.2 hwa) he') hw
  | f + 1, .letE _ _ v b _, w, he, h => by
    simp only [NoMarkKeys, Bool.and_eq_true] at he
    simp only [Pure.whnf] at h
    exact whnf_clean f (clean_inst he.1.2 he.2) h
  | f + 1, .mdata _ e, w, he, h => by
    simp only [NoMarkKeys, Bool.and_eq_true] at he
    simp only [Pure.whnf] at h
    exact whnf_clean f he.2 h
  | f + 1, .fvar x, w, he, h => by
    simp only [Pure.whnf] at h
    split at h
    · rename_i fv nm ty v hl
      exact whnf_clean f ((hls _ (List.mem_of_find?_eq_some hl)).2 v rfl) h
    · cases h; rfl
  | f + 1, .const c us, w, he, h => by
    simp only [Pure.whnf] at h
    split at h
    · rename_i v hv
      split at h
      · cases h; rfl
      · exact whnf_clean f (clean_instLevels _ _ ((decl_clean hd hv).2 _ rfl)) h
    · cases h; rfl
  | f + 1, .proj S i s, w, he, h => by
    simp only [Pure.whnf] at h
    obtain ⟨ws, h1, h2⟩ := ok_of_bind h
    have hargs := clean_spine (whnf_clean f (e := s) he h1)
    split at h2
    · rename_i hsp
      rw [hsp] at hargs
      split at h2
      · split at h2
        · rename_i a ha
          exact whnf_clean f (hargs a (List.mem_of_getElem? ha)) h2
        · cases h2; exact he
      · cases h2; exact he
    · cases h2; exact he
  | f + 1, .bvar _, w, he, h | f + 1, .sort _, w, he, h | f + 1, .lam .., w, he, h
  | f + 1, .forallE .., w, he, h | f + 1, .lit _, w, he, h | f + 1, .mvar _, w, he, h => by
    cases h; exact he

/-- `whnf_clean` for `Erasure.Pure.instForalls`. Reference: none. -/
theorem instForalls_clean (f : Nat) : ∀ {r : Expr} {as : List Expr} {w : Expr},
    NoMarkKeys r = true → (∀ a ∈ as, NoMarkKeys a = true) →
    Pure.instForalls cx f ls r as = .ok w → NoMarkKeys w = true
  | _, [], _, hr, _, h => by cases h; exact hr
  | _, a :: _, _, hr, has, h => by
    simp only [Pure.instForalls] at h
    obtain ⟨r', h1, h2⟩ := ok_of_bind h
    have hr' := whnf_clean hd hls f hr h1
    cases r' with
    | forallE n t b bi =>
      simp only [NoMarkKeys, Bool.and_eq_true] at hr'
      exact instForalls_clean f (clean_inst (has a (List.mem_cons_self ..)) hr'.2)
        (fun x hx => has x (List.mem_cons_of_mem _ hx)) h2
    | _ => exact absurd h2 throw_ne_ok

/-- `whnf_clean` for `Erasure.Pure.instProjs`. Reference: none. -/
theorem instProjs_clean (f : Nat) (S : Name) {s : Expr} (hs : NoMarkKeys s = true) :
    ∀ (k j : Nat) {r w : Expr}, NoMarkKeys r = true →
      Pure.instProjs cx f ls S s k j r = .ok w → NoMarkKeys w = true
  | 0, _, _, _, hr, h => by cases h; exact hr
  | k + 1, j, _, _, hr, h => by
    simp only [Pure.instProjs] at h
    obtain ⟨r', h1, h2⟩ := ok_of_bind h
    have hr' := whnf_clean hd hls f hr h1
    cases r' with
    | forallE n t b bi =>
      simp only [NoMarkKeys, Bool.and_eq_true] at hr'
      exact instProjs_clean f S hs k (j + 1) (clean_inst (a := .proj S j s) hs hr'.2) h2
    | _ => exact absurd h2 throw_ne_ok

/-- `Erasure.Pure.inferType` builds its result from the term, the binder types, the locals'
types, the declarations' types and values and instantiation, so it carries no mark key if they
carry none. Reference: none. -/
theorem inferType_clean : ∀ (f : Nat) {Γ : List Expr} {e T : Expr}, NoMarkKeys e = true →
    (∀ A ∈ Γ, NoMarkKeys A = true) → Pure.inferType cx f ls Γ e = .ok T → NoMarkKeys T = true
  | 0, _, _, _, _, _, h => absurd h throw_ne_ok
  | f + 1, Γ, .bvar i, T, _, hΓ, h => by
    simp only [Pure.inferType] at h
    split at h
    · rename_i A hA; cases h; exact clean_lift (hΓ A (List.mem_of_getElem? hA))
    · exact absurd h throw_ne_ok
  | f + 1, Γ, .fvar x, T, _, _, h => by
    simp only [Pure.inferType] at h
    split at h
    · rename_i l hl; cases h; exact (hls l (List.mem_of_find?_eq_some hl)).1
    · exact absurd h throw_ne_ok
  | f + 1, Γ, .sort u, T, _, _, h => by cases h; rfl
  | f + 1, Γ, .lit (.natVal _), T, _, _, h => by cases h; rfl
  | f + 1, Γ, .lit (.strVal _), T, _, _, h => absurd h throw_ne_ok
  | f + 1, Γ, .mvar _, T, _, _, h => absurd h throw_ne_ok
  | f + 1, Γ, .const c us, T, _, _, h => by
    simp only [Pure.inferType] at h
    split at h
    · rename_i ci hci
      split at h
      · cases h; exact clean_instLevels _ _ (decl_clean hd hci).1
      · exact absurd h throw_ne_ok
    · exact absurd h throw_ne_ok
  | f + 1, Γ, .app g a, T, he, hΓ, h => by
    simp only [NoMarkKeys, Bool.and_eq_true] at he
    simp only [Pure.inferType] at h
    obtain ⟨Tg, h1, h2⟩ := ok_of_bind h
    obtain ⟨w, h3, h4⟩ := ok_of_bind h2
    have hw := whnf_clean hd hls f (inferType_clean f he.1 hΓ h1) h3
    cases w with
    | forallE n t B bi =>
      cases h4
      simp only [NoMarkKeys, Bool.and_eq_true] at hw
      exact clean_inst he.2 hw.2
    | _ => exact absurd h4 throw_ne_ok
  | f + 1, Γ, .lam n t b bi, T, he, hΓ, h => by
    simp only [NoMarkKeys, Bool.and_eq_true] at he
    simp only [Pure.inferType] at h
    obtain ⟨B, h1, h2⟩ := ok_of_bind h
    cases h2
    have := inferType_clean f he.2 (fun A hA => by
      rcases List.mem_cons.mp hA with rfl | hA
      · exact he.1
      · exact hΓ A hA) h1
    simp [NoMarkKeys, he.1, this]
  | f + 1, Γ, .forallE n t b bi, T, he, hΓ, h => by
    simp only [Pure.inferType] at h
    obtain ⟨_, -, h⟩ := ok_of_bind h
    obtain ⟨w, -, h⟩ := ok_of_bind h
    cases w with
    | sort u =>
      obtain ⟨_, -, h⟩ := ok_of_bind h
      obtain ⟨w', -, h⟩ := ok_of_bind h
      cases w' with
      | sort v => cases h; rfl
      | _ => exact absurd h throw_ne_ok
    | _ => exact absurd h throw_ne_ok
  | f + 1, Γ, .letE _ _ v b _, T, he, hΓ, h => by
    simp only [NoMarkKeys, Bool.and_eq_true] at he
    simp only [Pure.inferType] at h
    exact inferType_clean f (clean_inst he.1.2 he.2) hΓ h
  | f + 1, Γ, .mdata _ e, T, he, hΓ, h => by
    simp only [NoMarkKeys, Bool.and_eq_true] at he
    simp only [Pure.inferType] at h
    exact inferType_clean f he.2 hΓ h
  | f + 1, Γ, .proj S i s, T, he, hΓ, h => by
    simp only [Pure.inferType] at h
    obtain ⟨Ts, h1, h⟩ := ok_of_bind h
    obtain ⟨ws, h2, h⟩ := ok_of_bind h
    have hargs := clean_spine (whnf_clean hd hls f (inferType_clean f (e := s) he hΓ h1) h2)
    generalize spine ws = p at hargs h
    obtain ⟨hh, args⟩ := p
    cases hh with
    | const S' us =>
      simp only at h
      split at h
      · split at h
        · exact absurd h throw_ne_ok
        · split at h
          · rename_i c _
            split at h
            · rename_i ci cv hci
              split at h
              · obtain ⟨r, hr, h⟩ := ok_of_bind h
                obtain ⟨x, hx, h⟩ := ok_of_bind h
                obtain ⟨w, hw, h⟩ := ok_of_bind h
                have hr' := instForalls_clean hd hls f
                  (clean_instLevels _ _ (decl_clean hd hci).1)
                  (fun a ha => hargs a (List.mem_of_mem_take ha)) hr
                have hw' :=
                  whnf_clean hd hls f (instProjs_clean hd hls f S (s := s) he i 0 hr' hx) hw
                cases w with
                | forallE n d b bi =>
                  cases h
                  simp only [NoMarkKeys, Bool.and_eq_true] at hw'
                  exact hw'.1
                | _ => exact absurd h throw_ne_ok
              · exact absurd h throw_ne_ok
            · exact absurd h throw_ne_ok
          · exact absurd h throw_ne_ok
      · exact absurd h throw_ne_ok
    | _ => exact absurd h throw_ne_ok

end

/-- The η-binder domain and codomain `forallView?` reads off a type carry no mark key if the type
carries none. Reference: none. -/
theorem forallView_clean {decls : List ConstantInfo} {ls : List Local} {T D C : Expr} {y : Name}
    {bi : BinderInfo} (hd : NoMarkKeysDecls decls = true) (hls : CleanLocals ls)
    (hT : NoMarkKeys T = true) (h : forallView? decls ls T = some (y, D, C, bi)) :
    NoMarkKeys D = true ∧ NoMarkKeys C = true := by
  unfold forallView? at h
  split at h
  · cases h; simpa [NoMarkKeys] using hT
  · split at h
    · rename_i hw
      cases h
      simpa [NoMarkKeys] using whnf_clean (cx := ⟨decls⟩) hd hls _ hT hw
    · cases h

/-! ## The reading of a marking -/

/-- `ê` reads as `e`: `unmark ê` is `e` with some metadata removed, and every `eta` mark of `ê`
sits on a λ. Reference: none (DV-32). -/
def Reads (e ê : Expr) : Prop := DropMD e (unmark ê) ∧ EtaLams ê

/-- Each argument's marking reads as the argument. Reference: none. -/
def ReadsAll (as âs : List Expr) : Prop :=
  as.length = âs.length ∧ ∀ (i : Nat) a â, as[i]? = some a → âs[i]? = some â → Reads a â

/-- A term without mark keys reads as itself. Reference: none. -/
theorem Reads.clean {e : Expr} (h : NoMarkKeys e = true) : Reads e e :=
  ⟨by rw [unmark_clean h]; exact .refl _, etaLams_clean h⟩

/-- An `erase`-marked term reads as the term (`MarkOf.erase`). Reference: none. -/
theorem Reads.erase {e : Expr} (h : NoMarkKeys e = true) : Reads e (markErase e) :=
  ⟨(Reads.clean h).1, fun hm => absurd hm (by simp [markMD]), etaLams_clean h⟩

/-- A `reduced`-marked discriminant reads as itself (`MarkSat.casesReduced`). Reference:
none. -/
theorem Reads.reduced {e : Expr} (h : NoMarkKeys e = true) : Reads e (markReduced e) :=
  ⟨(Reads.clean h).1, fun hm => absurd hm (by simp [markMD]), etaLams_clean h⟩

/-- Terms without mark keys read as themselves. Reference: none. -/
theorem ReadsAll.clean {as : List Expr} (h : ∀ a ∈ as, NoMarkKeys a = true) : ReadsAll as as :=
  ⟨rfl, fun _ a _ ha hâ => by
    rw [ha] at hâ; cases hâ; exact Reads.clean (h a (List.mem_of_getElem? ha))⟩

/-- No arguments. Reference: none. -/
theorem ReadsAll.nil : ReadsAll [] [] := ⟨rfl, fun _ _ _ h => by simp at h⟩

/-- One more argument in front. Reference: none. -/
theorem ReadsAll.cons {a â : Expr} {as âs : List Expr} (h : Reads a â) (t : ReadsAll as âs) :
    ReadsAll (a :: as) (â :: âs) :=
  ⟨by simp [t.1], fun i x y hx hy => by
    cases i with
    | zero => cases hx; cases hy; exact h
    | succ i => exact t.2 i x y hx hy⟩

/-- Two runs of arguments. Reference: none. -/
theorem ReadsAll.append {as âs bs bs' : List Expr} (h₁ : ReadsAll as âs) (h₂ : ReadsAll bs bs') :
    ReadsAll (as ++ bs) (âs ++ bs') := by
  have hl := h₁.1
  refine ⟨by simp [h₁.1, h₂.1], fun i a â ha hâ => ?_⟩
  by_cases hi : i < as.length
  · rw [List.getElem?_append_left hi] at ha
    rw [List.getElem?_append_left (h₁.1 ▸ hi)] at hâ
    exact h₁.2 i a â ha hâ
  · rw [List.getElem?_append_right (by omega)] at ha
    rw [List.getElem?_append_right (by omega), ← h₁.1] at hâ
    exact h₂.2 _ a â ha hâ

/-- An application spine reads as the spine of what its parts read as. Reference: none. -/
theorem Reads.foldl : ∀ {as âs : List Expr} {f fM : Expr}, Reads f fM → ReadsAll as âs →
    Reads (as.foldl .app f) (âs.foldl .app fM)
  | [], [], _, _, h, _ => h
  | [], _ :: _, _, _, _, h => absurd h.1 (by simp)
  | _ :: _, [], _, _, _, h => absurd h.1 (by simp)
  | a :: as, â :: âs, f, fM, hf, h => by
    have ha : Reads a â := h.2 0 a â rfl rfl
    exact Reads.foldl (as := as) (âs := âs) (f := .app f a) (fM := .app fM â)
      ⟨.app hf.1 ha.1, hf.2, ha.2⟩
      ⟨by simpa using h.1, fun i x y hx hy => h.2 (i + 1) x y hx hy⟩

/-- `Reads.foldl` on `mkAppN`. Reference: none. -/
theorem Reads.mkAppN {f fM : Expr} {as âs : List Expr} (hf : Reads f fM) (h : ReadsAll as âs) :
    Reads (mkAppN f as.toArray) (mkAppN fM âs.toArray) := by
  rw [mkAppN_toArray, mkAppN_toArray]; exact Reads.foldl hf h

/-- A constant reads as itself. Reference: none. -/
theorem Reads.const (c : Name) (us : List Level) : Reads (.const c us) (.const c us) :=
  ⟨.refl _, trivial⟩

/-- A λ whose body is marked opened at a fresh variable and closed again (`MarkOf.lam`,
`MarkAlt.lam`) reads as the λ. Reference: none. -/
theorem Reads.lam {n : Name} {A b bM : Expr} {bi : BinderInfo} {x : FVarId}
    (h : Reads (b.instantiate1' (.fvar x)) bM) (hx : FVarsIn (· ≠ x) b) (hA : NoMarkKeys A = true) :
    Reads (.lam n A b bi) (.lam n A (absFV x 0 bM) bi) := by
  have hb := h.1.absFV (x := x) (d := 0)
  rw [absFV_inst hx, ← unmark_absFV] at hb
  refine ⟨?_, etaLams_clean hA, etaLams_absFV h.2⟩
  show DropMD _ (.lam n (unmark A) (unmark (absFV x 0 bM)) bi)
  rw [unmark_clean hA]; exact .lam hb

/-- A `let` whose value and body are marked, the body opened at a fresh variable and closed again
(`MarkOf.letE`), reads as the `let`. Reference: none. -/
theorem Reads.letE {n : Name} {T v vM b bM : Expr} {nd : Bool} {x : FVarId} (hv : Reads v vM)
    (h : Reads (b.instantiate1' (.fvar x)) bM) (hx : FVarsIn (· ≠ x) b) (hT : NoMarkKeys T = true) :
    Reads (.letE n T v b nd) (.letE n T vM (absFV x 0 bM) nd) := by
  have hb := h.1.absFV (x := x) (d := 0)
  rw [absFV_inst hx, ← unmark_absFV] at hb
  refine ⟨?_, etaLams_clean hT, hv.2, etaLams_absFV h.2⟩
  show DropMD _ (.letE n (unmark T) (unmark vM) (unmark (absFV x 0 bM)) nd)
  rw [unmark_clean hT]; exact .letE hv.1 hb

/-- An η-introduced binder (`MarkEta.intro`, `MarkAlt.intro`) reads as the term it expands:
`unmark` contracts it, as the applied variable is fresh. Reference: none (DV-23). -/
theorem Reads.eta {e bM D : Expr} {x : FVarId} {y : Name} {bi : BinderInfo}
    (hb : Reads (.app e (.fvar x)) bM) (hx : FVarsIn (· ≠ x) e) (hD : NoMarkKeys D = true) :
    Reads e (markEta (.lam y D (absFV x 0 bM) bi)) := by
  obtain ⟨f', a', hu, hf, ha⟩ := hb.1.app_inv
  cases ha.fvar_inv
  have hf' : FVarsIn (· ≠ x) f' := hf.fvarsIn hx
  refine ⟨?_, fun _ => rfl, etaLams_clean hD, etaLams_absFV hb.2⟩
  have hc : unmark (markEta (.lam y D (absFV x 0 bM) bi)) = f' := by
    show etaContract (.lam y (unmark D) (unmark (absFV x 0 bM)) bi) = f'
    rw [unmark_absFV, hu]
    simp only [absFV, show (x == x) = true from (fvarId_beq_iff x x).mpr rfl, ↓reduceIte]
    rw [absFV_absent hf']
    simp only [etaContract, Marks.bvarOccurs_lift_out f' (s := 0) (n := 1) (k := 0) (by omega)
      (by omega), Bool.false_eq_true, ↓reduceIte]
    rw [Marks.inst_lift_cancel _ f' (c := 0) (j := 0) (n := 0) (Nat.le_refl 0) (Nat.le_refl 0),
      lift_zero]
  rw [hc]; exact hf

variable {decls : List ConstantInfo} {cfg : ErasureConfig}

mutual
/-- A marking reads as the term it marks, if neither the term, the locals nor the declarations
carry a mark key. Reference: none (DV-32). -/
theorem MarkOf.reads (hd : NoMarkKeysDecls decls = true) : ∀ {ls : List Local} {e ê : Expr},
    MarkOf decls cfg ls e ê → CleanLocals ls → NoMarkKeys e = true → Reads e ê
  | _, _, _, .erase _, _, he => Reads.erase he
  | _, _, _, .fvar _, _, _ => ⟨.refl _, trivial⟩
  | _, _, _, .mdata _ h, hl, he => by
    simp only [NoMarkKeys, Bool.and_eq_true] at he
    have r := MarkOf.reads hd h hl he.2
    exact ⟨.drop r.1, r.2⟩
  | _, _, _, .lam _ hfr h, hl, he => by
    simp only [NoMarkKeys, Bool.and_eq_true] at he
    exact Reads.lam (MarkOf.reads hd h (cleanLocals_cons he.1 (by simp) hl) (clean_inst rfl he.2))
      (hfr.2 _ (List.mem_singleton_self _)) he.1
  | _, _, _, .letE _ hfr hv hb, hl, he => by
    simp only [NoMarkKeys, Bool.and_eq_true] at he
    exact Reads.letE
      (MarkOf.reads hd hv (cleanLocals_cons he.1.1 (fun _ hv => by cases hv; exact he.1.2) hl)
        he.1.2)
      (MarkOf.reads hd hb (cleanLocals_cons he.1.1 (fun _ hv => by cases hv; exact he.1.2) hl)
        (clean_inst rfl he.2))
      (hfr.2 _ (by simp)) he.1.1
  | _, _, _, .proj _ _ h, hl, he => by
    have r := MarkOf.reads hd h hl he
    exact ⟨.proj r.1, r.2⟩
  | _, _, _, .litZero .., _, _ => ⟨.refl _, trivial⟩
  | _, _, _, .litSucc .., _, _ => ⟨.refl _, trivial⟩
  | _, _, _, .app _ _ _ _ hf hlen has, hl, he => by
    obtain ⟨hfc, hasc⟩ := clean_mkAppN.mp he
    exact Reads.mkAppN (MarkOf.reads hd hf hl hfc) ⟨hlen, fun i a â ha hâ =>
      MarkOf.reads hd (has i a â ha hâ) hl (hasc a (List.mem_of_getElem? ha))⟩
  | _, _, _, .constApp _ _ hlen has, hl, he => by
    obtain ⟨-, hasc⟩ := clean_mkAppN.mp he
    exact Reads.mkAppN (Reads.const _ _) ⟨hlen, fun i a â ha hâ =>
      MarkOf.reads hd (has i a â ha hâ) hl (hasc a (List.mem_of_getElem? ha))⟩
  | _, _, _, .special _ _ hT h, hl, he =>
    MarkEta.reads hd h hl (inferType_clean (cx := ⟨decls⟩) hd hl _ he (by simp) hT)
      (clean_mkAppN.mp he).2

/-- `MarkOf.reads` for the η-expansion of a constant spine. Reference: none (DV-23). -/
theorem MarkEta.reads (hd : NoMarkKeysDecls decls = true) : ∀ {ls : List Local} {ar : Nat}
    {T : Expr} {c : Name} {us : List Level} {as : List Expr} {ê : Expr},
    MarkEta decls cfg ls ar T c us as ê → CleanLocals ls → NoMarkKeys T = true →
      (∀ a ∈ as, NoMarkKeys a = true) → Reads (mkAppN (.const c us) as.toArray) ê
  | _, _, _, _, _, _, _, .sat _ h, hl, _, has => MarkSat.reads hd h hl has
  | _, _, _, _, _, _, _, .intro _ hv hfr h, hl, hT, has => by
    obtain ⟨hD, hC⟩ := forallView_clean hd hl hT hv
    have r := MarkEta.reads hd h (cleanLocals_cons hD (by simp) hl) (clean_inst rfl hC) (by
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact has a ha
      · rw [List.mem_singleton] at ha; subst ha; rfl)
    rw [mkAppN_snoc] at r
    refine Reads.eta r ?_ hD
    rw [mkAppN_toArray]
    exact fvarsIn_foldl trivial fun a ha => hfr.2 a (List.mem_cons_of_mem _ ha)

/-- `MarkOf.reads` for the saturated spines. Reference: none (DV-32). -/
theorem MarkSat.reads (hd : NoMarkKeysDecls decls = true) : ∀ {ls : List Local} {c : Name}
    {us : List Level} {as : List Expr} {ê : Expr},
    MarkSat decls cfg ls c us as ê → CleanLocals ls → (∀ a ∈ as, NoMarkKeys a = true) →
      Reads (mkAppN (.const c us) as.toArray) ê
  | _, _, _, _, _, .casesProp .., _, has => Reads.erase (clean_mkAppN.mpr ⟨rfl, has⟩)
  | _, _, _, _, _, .casesReduced (pre := pre) _ _ _ _ _ _ _ _ _ halt hlen hext, hl, has =>
    Reads.mkAppN (Reads.const _ _)
      ((((ReadsAll.clean (as := pre) fun a ha => has a (by simp [ha])).append
        (.cons (Reads.reduced (has _ (by simp))) .nil)).append
        (.cons (MarkOf.reads hd halt hl (has _ (by simp))) .nil)).append
        ⟨hlen, fun i a â ha hâ => MarkOf.reads hd (hext i a â ha hâ) hl
          (has a (by simp [List.mem_of_getElem? ha]))⟩)
  | _, _, _, _, _, .cases (pre := pre) _ _ _ _ hnalts _ _ hdM hlen hctors htys halt hlen' hext,
    hl, has =>
    Reads.mkAppN (Reads.const _ _)
      ((((ReadsAll.clean (as := pre) fun a ha => has a (by simp [ha])).append
        (.cons (MarkOf.reads hd hdM hl (has _ (by simp))) .nil)).append
        ⟨hlen, fun i alt âlt ha hâ => by
          have hi : i < _ := hnalts ▸ (List.getElem?_eq_some_iff.mp ha).1
          obtain ⟨cv, hcv⟩ := hctors i _ (List.getElem?_eq_getElem hi)
          obtain ⟨T, hT⟩ := htys i alt ha
          have hac := has alt (by simp [List.mem_of_getElem? ha])
          exact MarkAlt.reads hd (halt i _ cv alt âlt T (List.getElem?_eq_getElem hi) hcv ha hâ hT)
            hl hac (inferType_clean (cx := ⟨decls⟩) hd hl _ hac (by simp) hT)⟩).append
        ⟨hlen', fun i a â ha hâ => MarkOf.reads hd (hext i a â ha hâ) hl
          (has a (by simp [List.mem_of_getElem? ha]))⟩)
  | _, _, _, _, _, .ctor _ _ hlen h, hl, has =>
    Reads.mkAppN (Reads.const _ _) ⟨hlen, fun i a â ha hâ => MarkOf.reads hd (h i a â ha hâ) hl
      (has a (List.mem_of_getElem? ha))⟩
  | _, _, _, _, _, .quotMk (extra := extra) _ _ _ _ ha hlen hext, hl, has =>
    Reads.mkAppN (Reads.const _ _)
      (.cons (Reads.clean (has _ (by simp))) <| .cons (Reads.clean (has _ (by simp))) <|
        .cons (MarkOf.reads hd ha hl (has _ (by simp)))
        (show ReadsAll extra _ from ⟨hlen, fun i a â ha hâ => MarkOf.reads hd (hext i a â ha hâ) hl
          (has a (by simp [List.mem_of_getElem? ha]))⟩))
  | _, _, _, _, _, .quotLift (extra := extra) _ _ _ _ hf hq hlen hext, hl, has =>
    Reads.mkAppN (Reads.const _ _)
      (.cons (Reads.clean (has _ (by simp))) <| .cons (Reads.clean (has _ (by simp))) <|
        .cons (Reads.clean (has _ (by simp))) <| .cons (MarkOf.reads hd hf hl (has _ (by simp))) <|
        .cons (Reads.clean (has _ (by simp))) <| .cons (MarkOf.reads hd hq hl (has _ (by simp)))
        (show ReadsAll extra _ from ⟨hlen, fun i a â ha hâ => MarkOf.reads hd (hext i a â ha hâ) hl
          (has a (by simp [List.mem_of_getElem? ha]))⟩))
  | _, _, _, _, _, .recr (ps := ps) (ms := ms) _ _ _ _ _ _ _ _ _ _ _ hlm hmins hli his hmaj hle
      hext, hl, has =>
    Reads.mkAppN (Reads.const _ _)
      ((((((ReadsAll.clean (as := ps) fun a ha => has a (by simp [ha])).append
        (ReadsAll.clean (as := ms) fun a ha => has a (by simp [ha]))).append
        ⟨hlm, fun i a â ha hâ => MarkOf.reads hd (hmins i a â ha hâ) hl
          (has a (by simp [List.mem_of_getElem? ha]))⟩).append
        ⟨hli, fun i a â ha hâ => MarkOf.reads hd (his i a â ha hâ) hl
          (has a (by simp [List.mem_of_getElem? ha]))⟩).append
        (.cons (MarkOf.reads hd hmaj hl (has _ (by simp))) .nil)).append
        ⟨hle, fun i a â ha hâ => MarkOf.reads hd (hext i a â ha hâ) hl
          (has a (by simp [List.mem_of_getElem? ha]))⟩)

/-- `MarkOf.reads` for an alternative under its fields. Reference: none (DV-23). -/
theorem MarkAlt.reads (hd : NoMarkKeysDecls decls = true) : ∀ {ls : List Local} {k : Nat}
    {e T ê : Expr}, MarkAlt decls cfg ls k e T ê → CleanLocals ls → NoMarkKeys e = true →
      NoMarkKeys T = true → Reads e ê
  | _, _, _, _, _, .done h, hl, he, _ => MarkOf.reads hd h hl he
  | _, _, _, _, _, .lam hv hfr h, hl, he, hT => by
    obtain ⟨hD, hC⟩ := forallView_clean hd hl hT hv
    simp only [NoMarkKeys, Bool.and_eq_true] at he
    exact Reads.lam (MarkAlt.reads hd h (cleanLocals_cons hD (by simp) hl) (clean_inst rfl he.2)
      (clean_inst rfl hC)) (hfr.2 _ (by simp)) he.1
  | _, _, _, _, _, .intro _ hv hfr h, hl, he, hT => by
    obtain ⟨hD, hC⟩ := forallView_clean hd hl hT hv
    exact Reads.eta (MarkAlt.reads hd h (cleanLocals_cons hD (by simp) hl)
      (by simp [NoMarkKeys, he]) (clean_inst rfl hC)) (hfr.2 _ (by simp)) hD
end

end MarkRead

open MarkRead

/-- The start of `srcEval_sound`: if neither the input `e` nor the declarations' types and values
carry a mark key, its marking `ê` under no locals reads through `unmark` as `e` and every `eta`
mark of `ê` sits on a λ (the premises `hread`, `hη` of `Sound.of_semSim`). Reference: none
(DV-32). -/
theorem markOf_read {decls : List ConstantInfo} {cfg : ErasureConfig} {e ê : Expr}
    (hd : NoMarkKeysDecls decls = true) (he : NoMarkKeys e = true) (h : MarkOf decls cfg [] e ê) :
    toCL? (unmark ê) = toCL? e ∧ EtaLams ê :=
  have r := MarkRead.MarkOf.reads hd h (fun _ hl => nomatch hl) he
  ⟨r.1.toCL, r.2⟩

end EraseProof
