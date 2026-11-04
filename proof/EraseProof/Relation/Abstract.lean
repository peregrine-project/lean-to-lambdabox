import EraseProof.Bridge.Abstract
import EraseProof.Relation.Extend

/-!
# Closing a binder in the erasure relation

The traversal opens a binder with a fresh free variable `x`, erases the opened body to `tb`, and
closes the result with the shipping `abstract x tb = toBvar x 0 tb` (`LeanToLambdaBox/Basic.lean:149`),
which does not shift loose indices. `Erases.abstract`: when `tb` is closed, the body itself erases
to `abstract x tb` under the locals where the binder is a bound variable. The induction abstracts `x`
into the bound variable `d` on the source side (`AbsFV.absFV`) and replaces `x` by the index `d` on
the λ□ side (`toBvar x d`); the translations inside the relation move with `AbsFV.TrM.absN`. The
η-expansions of constructor and `casesOn` spines commute with the abstraction because the
program's types are closed (`ProgEnv`). Reference: `TrS.uninstantiateN`/`Erases.uninstantiateN`
(`L4 Relation/Abstract.lean:170`); none in MetaRocq (DV-13).
-/

open Lean Erasure

namespace EraseProof

namespace AbsFV

/-- Every loose bound variable of `e` is below `k`. -/
def LBV : Nat → Expr → Prop
  | k, .bvar i => i < k
  | k, .app f a => LBV k f ∧ LBV k a
  | k, .lam _ t b _ | k, .forallE _ t b _ => LBV k t ∧ LBV (k + 1) b
  | k, .letE _ t v b _ => LBV k t ∧ LBV k v ∧ LBV (k + 1) b
  | k, .mdata _ e | k, .proj _ _ e => LBV k e
  | _, _ => True

theorem LBV.mono : ∀ {e : Expr} {k k' : Nat}, LBV k e → k ≤ k' → LBV k' e
  | .bvar _, _, _, h, hk => by simp only [LBV] at h ⊢; omega
  | .app f a, _, _, h, hk => ⟨LBV.mono (e := f) h.1 hk, LBV.mono (e := a) h.2 hk⟩
  | .lam _ t b _, _, _, h, hk | .forallE _ t b _, _, _, h, hk =>
    ⟨LBV.mono (e := t) h.1 hk, LBV.mono (e := b) h.2 (by omega)⟩
  | .letE _ t v b _, _, _, h, hk =>
    ⟨LBV.mono (e := t) h.1 hk, LBV.mono (e := v) h.2.1 hk, LBV.mono (e := b) h.2.2 (by omega)⟩
  | .mdata _ e, _, _, h, hk | .proj _ _ e, _, _, h, hk => LBV.mono (e := e) h hk
  | .sort _, _, _, _, _ | .const .., _, _, _, _ | .lit _, _, _, _, _ | .mvar _, _, _, _, _
  | .fvar _, _, _, _, _ => trivial

theorem LBV_foldl {k : Nat} (f : Expr) (as : List Expr) :
    LBV k (as.foldl .app f) ↔ LBV k f ∧ ∀ a ∈ as, LBV k a := by
  induction as generalizing f with
  | nil => simp
  | cons a as ih => simp [ih, LBV, and_assoc]

/-- The number of bound locals. -/
private theorem findB_lt {ζ : Metalean.Sigs} {ℓ n : Nat} :
    ∀ {Δ : MLCtx ζ ℓ n} {i : Nat} {t : Metalean.Expr ζ ℓ n}, Δ.findB i = some t →
      i < Δ.countP (·.1.isNone)
  | [], _, _, h => by cases h
  | (none, _) :: _, 0, _, _ => by simp
  | (none, _) :: Δ, i + 1, _, h => by
    have := findB_lt (Δ := Δ) h
    simp only [List.countP_cons, Option.isNone_none, ite_true]; omega
  | (some _, _) :: Δ, i, _, h => by
    have := findB_lt (Δ := Δ) h
    simpa [List.countP_cons] using this

/-- A translated term's loose bound variables are its bound locals. -/
theorem TrM.lbv {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {lps : List Name}
    {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n} {e : Expr}
    {t : Metalean.Expr ζ lps.length n} (h : TrM E B lps Γ Δ e t) :
    LBV (Δ.countP (·.1.isNone)) e := by
  have hpush : ∀ {n : Nat} (Δ : MLCtx ζ lps.length n),
      (Δ.pushLam none).countP (·.1.isNone) = Δ.countP (·.1.isNone) + 1 := by
    intro n Δ
    simp only [MLCtx.pushLam, List.countP_cons, Option.isNone_none, ite_true, List.countP_map]
    rfl
  induction h with
  | bvar h => exact findB_lt h
  | fvar | sort | const | lit => trivial
  | @special _ _ _ _ _ as as' _ _ _ _ hlen _ _ ih =>
    rw [mkAppN_toArray, LBV_foldl]
    refine ⟨trivial, fun a ha => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    exact ih i _ as'[i] (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem (hlen ▸ hi))
  | app _ _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | @lam _ Γ Δ _ _ _ _ _ _ _ _ ih₁ ih₂ | @forallE _ Γ Δ _ _ _ _ _ _ _ _ ih₁ ih₂ =>
    exact ⟨ih₁, by rw [hpush] at ih₂; exact ih₂⟩
  | letE _ _ _ ih₁ ih₂ ih₃ =>
    refine ⟨ih₁, ih₂, ?_⟩
    simpa [List.countP_cons] using ih₃
  | mdata _ ih | projStruct _ _ _ _ _ ih | projProof _ _ _ _ _ _ _ _ _ ih => exact ih

theorem LBV_instLevels (ps : List Name) (us : List Level) :
    ∀ {e : Expr} {k : Nat}, LBV k e → LBV k (Pure.instLevels ps us e)
  | .bvar _, _, h => h
  | .app f a, _, h => ⟨LBV_instLevels ps us (e := f) h.1, LBV_instLevels ps us (e := a) h.2⟩
  | .lam _ t b _, _, h | .forallE _ t b _, _, h =>
    ⟨LBV_instLevels ps us (e := t) h.1, LBV_instLevels ps us (e := b) h.2⟩
  | .letE _ t v b _, _, h => ⟨LBV_instLevels ps us (e := t) h.1,
    LBV_instLevels ps us (e := v) h.2.1, LBV_instLevels ps us (e := b) h.2.2⟩
  | .mdata _ e, _, h | .proj _ _ e, _, h => LBV_instLevels ps us (e := e) h
  | .sort _, _, _ | .const .., _, _ | .lit _, _, _ | .mvar _, _, _ | .fvar _, _, _ => trivial

theorem FVarsIn_instLevels (ps : List Name) (us : List Level) {p : FVarId → Prop} :
    ∀ {e : Expr}, FVarsIn p e → FVarsIn p (Pure.instLevels ps us e)
  | .app f a, h => ⟨FVarsIn_instLevels ps us (e := f) h.1, FVarsIn_instLevels ps us (e := a) h.2⟩
  | .lam _ t b _, h | .forallE _ t b _, h =>
    ⟨FVarsIn_instLevels ps us (e := t) h.1, FVarsIn_instLevels ps us (e := b) h.2⟩
  | .letE _ t v b _, h => ⟨FVarsIn_instLevels ps us (e := t) h.1,
    FVarsIn_instLevels ps us (e := v) h.2.1, FVarsIn_instLevels ps us (e := b) h.2.2⟩
  | .mdata _ e, h | .proj _ _ e, h => FVarsIn_instLevels ps us (e := e) h
  | .fvar _, h => h
  | .bvar _, _ | .sort _, _ | .const .., _ | .lit _, _ | .mvar _, _ => trivial

/-- Abstraction leaves a term without `x` and without loose indices from `d` on unchanged. -/
theorem absFV_self {x : FVarId} : ∀ {e : Expr} {d : Nat}, LBV d e → FVarsIn (fun _ => False) e →
    absFV x d e = e
  | .bvar i, d, h, _ => by simp only [LBV] at h; simp [absFV, h]
  | .fvar _, _, _, h => h.elim
  | .app f a, _, h, h' => by simp [absFV, absFV_self h.1 h'.1, absFV_self h.2 h'.2]
  | .lam _ t b _, _, h, h' | .forallE _ t b _, _, h, h' => by
    simp [absFV, absFV_self h.1 h'.1, absFV_self h.2 h'.2]
  | .letE _ t v b _, _, h, h' => by
    simp [absFV, absFV_self h.1 h'.1, absFV_self h.2.1 h'.2.1, absFV_self h.2.2 h'.2.2]
  | .mdata _ e, _, h, h' => by simp [absFV, absFV_self (e := e) h h']
  | .proj _ _ e, _, h, h' => by simp [absFV, absFV_self (e := e) h h']
  | .sort _, _, _, _ | .const .., _, _, _ | .lit _, _, _, _ | .mvar _, _, _, _ => rfl

/-- Abstraction commutes with lifting below the abstracted index. -/
theorem absFV_lift (x : FVarId) (k : Nat) :
    ∀ (a : Expr) {s d : Nat}, s ≤ d →
      absFV x (d + k) (a.liftLooseBVars' s k) = (absFV x d a).liftLooseBVars' s k
  | .bvar i, s, d, hs => by
    simp only [Expr.liftLooseBVars', absFV]
    congr 1
    split_ifs <;> omega
  | .fvar y, s, d, hs => by
    simp only [Expr.liftLooseBVars', absFV]
    split
    · simp only [Expr.liftLooseBVars']; congr 1; split_ifs <;> omega
    · rfl
  | .app f a, s, d, hs => by simp [Expr.liftLooseBVars', absFV, absFV_lift x k f hs, absFV_lift x k a hs]
  | .lam _ t b _, s, d, hs => by
    have := absFV_lift x k b (s := s + 1) (d := d + 1) (by omega)
    rw [show d + 1 + k = d + k + 1 by omega] at this
    simp [Expr.liftLooseBVars', absFV, absFV_lift x k t hs, this]
  | .forallE _ t b _, s, d, hs => by
    have := absFV_lift x k b (s := s + 1) (d := d + 1) (by omega)
    rw [show d + 1 + k = d + k + 1 by omega] at this
    simp [Expr.liftLooseBVars', absFV, absFV_lift x k t hs, this]
  | .letE _ t v b _, s, d, hs => by
    have := absFV_lift x k b (s := s + 1) (d := d + 1) (by omega)
    rw [show d + 1 + k = d + k + 1 by omega] at this
    simp [Expr.liftLooseBVars', absFV, absFV_lift x k t hs, absFV_lift x k v hs, this]
  | .mdata _ e, s, d, hs => by simp [Expr.liftLooseBVars', absFV, absFV_lift x k e hs]
  | .proj _ _ e, s, d, hs => by simp [Expr.liftLooseBVars', absFV, absFV_lift x k e hs]
  | .sort _, _, _, _ | .const .., _, _, _ | .lit _, _, _, _ | .mvar _, _, _, _ => rfl

/-- Abstraction commutes with instantiation below the abstracted index. -/
theorem absFV_instantiate1' (x : FVarId) (a : Expr) (d : Nat) :
    ∀ (b : Expr) (k : Nat),
      absFV x (d + k) (b.instantiate1' a k) = (absFV x (d + k + 1) b).instantiate1' (absFV x d a) k
  | .bvar i, k => by
    have hb : ∀ (b : Expr) (j m : Nat), (Expr.bvar j).instantiate1' b m =
        if j < m then .bvar j else if j = m then b.liftLooseBVars' 0 m else .bvar (j - 1) :=
      fun _ _ _ => rfl
    have ha : ∀ m j, absFV x m (.bvar j) = .bvar (if j < m then j else j + 1) := fun _ _ => rfl
    by_cases h₁ : i < k
    · rw [hb]
      simp only [h₁, ↓reduceIte, ha, show i < d + k by omega, show i < d + k + 1 by omega, hb]
    · by_cases h₂ : i = k
      · subst h₂
        rw [hb, ha]
        simp only [h₁, ↓reduceIte, show i < d + i + 1 by omega, hb]
        exact absFV_lift x i a (Nat.zero_le d)
      · rw [hb, ha]
        simp only [h₁, h₂, ↓reduceIte, ha]
        by_cases h₃ : i < d + k + 1
        · simp only [show i - 1 < d + k by omega, h₃, ↓reduceIte, hb, h₁, h₂]
        · simp only [show ¬ i - 1 < d + k by omega, h₃, ↓reduceIte, hb,
            show ¬ i + 1 < k by omega, show ¬ i + 1 = k by omega]
          congr 1; omega
  | .fvar y, k => by
    simp only [Expr.instantiate1', absFV]
    split
    · simp only [Expr.instantiate1', show ¬ d + k + 1 < k by omega,
        show ¬ d + k + 1 = k by omega, ↓reduceIte]
      rfl
    · rfl
  | .app f b, k => by
    simp [Expr.instantiate1', absFV, absFV_instantiate1' x a d f k, absFV_instantiate1' x a d b k]
  | .lam _ t b _, k => by
    have := absFV_instantiate1' x a d b (k + 1)
    rw [show d + (k + 1) = d + k + 1 by omega] at this
    simp [Expr.instantiate1', absFV, absFV_instantiate1' x a d t k, this]
  | .forallE _ t b _, k => by
    have := absFV_instantiate1' x a d b (k + 1)
    rw [show d + (k + 1) = d + k + 1 by omega] at this
    simp [Expr.instantiate1', absFV, absFV_instantiate1' x a d t k, this]
  | .letE _ t v b _, k => by
    have := absFV_instantiate1' x a d b (k + 1)
    rw [show d + (k + 1) = d + k + 1 by omega] at this
    simp [Expr.instantiate1', absFV, absFV_instantiate1' x a d t k,
      absFV_instantiate1' x a d v k, this]
  | .mdata _ e, k => by simp [Expr.instantiate1', absFV, absFV_instantiate1' x a d e k]
  | .proj _ _ e, k => by simp [Expr.instantiate1', absFV, absFV_instantiate1' x a d e k]
  | .sort _, _ | .const .., _ | .lit _, _ | .mvar _, _ => rfl

theorem absFV_piInst (x : FVarId) (d : Nat) :
    ∀ {as : List Expr} {T T' : Expr}, piInst as T = some T' →
      piInst (as.map (absFV x d)) (absFV x d T) = some (absFV x d T')
  | [], _, _, h => by cases h; rfl
  | a :: as, .forallE _ A B _, _, h => by
    simp only [piInst] at h
    simp only [List.map_cons, absFV, piInst]
    have := absFV_instantiate1' x a d B 0
    simp only [Nat.add_zero] at this
    rw [← this]
    exact absFV_piInst x d h
  | _ :: _, .bvar _, _, h | _ :: _, .fvar _, _, h | _ :: _, .mvar _, _, h
  | _ :: _, .sort _, _, h | _ :: _, .const .., _, h | _ :: _, .app .., _, h
  | _ :: _, .lam .., _, h | _ :: _, .letE .., _, h | _ :: _, .lit _, _, h
  | _ :: _, .mdata .., _, h | _ :: _, .proj .., _, h => by cases h

theorem absFV_lamsOf (x : FVarId) :
    ∀ {m d : Nat} {T body e : Expr}, lamsOf m T body = some e →
      lamsOf m (absFV x d T) (absFV x (d + m) body) = some (absFV x d e)
  | 0, d, _, _, _, h => by cases h; rfl
  | m + 1, d, .forallE _ D B _, body, e, h => by
    simp only [lamsOf, Option.map_eq_some_iff] at h
    obtain ⟨e₀, he₀, rfl⟩ := h
    have := absFV_lamsOf x (d := d + 1) he₀
    rw [show d + 1 + m = d + (m + 1) by omega] at this
    simp [absFV, lamsOf, this]
  | _ + 1, _, .bvar _, _, _, h | _ + 1, _, .fvar _, _, _, h | _ + 1, _, .mvar _, _, _, h
  | _ + 1, _, .sort _, _, _, h | _ + 1, _, .const .., _, _, h | _ + 1, _, .app .., _, _, h
  | _ + 1, _, .lam .., _, _, h | _ + 1, _, .letE .., _, _, h | _ + 1, _, .lit _, _, _, h
  | _ + 1, _, .mdata .., _, _, h | _ + 1, _, .proj .., _, _, h => by cases h

/-- The body of an η-expansion commutes with the abstraction. -/
theorem absFV_body (x : FVarId) (d m : Nat) (c : Name) (us : List Level) (as : List Expr) :
    absFV x (d + m) (mkAppN (.const c us)
      (as.map (·.liftLooseBVars' 0 m) ++ (List.range m).reverse.map Expr.bvar).toArray) =
    mkAppN (.const c us) ((as.map (absFV x d)).map (·.liftLooseBVars' 0 m) ++
      (List.range m).reverse.map Expr.bvar).toArray := by
  rw [mkAppN_toArray, mkAppN_toArray, absFV_foldl]
  simp only [absFV, List.map_append, List.map_map]
  congr 2
  · refine List.map_congr_left fun a _ => ?_
    exact absFV_lift x m a (Nat.zero_le d)
  · refine List.map_congr_left fun j hj => ?_
    have : j < m := by simpa using hj
    simp [absFV, show j < d + m by omega]

/-- The η-expansion of a spine commutes with the abstraction, when the head's type is closed. -/
theorem etaSpine?_absFV {σ : EvalEnv} {c : Name} {us : List Level} {as : List Expr} {e' : Expr}
    (x : FVarId) (d : Nat)
    (hty : ∀ ci, findDecl σ.decls c = some ci → LBV 0 ci.type ∧ FVarsIn (fun _ => False) ci.type)
    (h : σ.etaSpine? c us as = some e') :
    σ.etaSpine? c us (as.map (absFV x d)) = some (absFV x d e') := by
  unfold EvalEnv.etaSpine? at h ⊢
  split at h
  · rename_i ci ar hci har
    simp only [List.length_map]
    split at h
    · rename_i hlt
      simp only [hlt, ↓reduceIte, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨ty, hty', he⟩ := h
      obtain ⟨h0, hf⟩ := hty ci hci
      have hcl : absFV x d (Pure.instLevels ci.levelParams us ci.type) =
          Pure.instLevels ci.levelParams us ci.type :=
        absFV_self (LBV.mono (LBV_instLevels _ _ h0) (Nat.zero_le _)) (FVarsIn_instLevels _ _ hf)
      refine ⟨absFV x d ty, by rw [← hcl]; exact absFV_piInst x d hty', ?_⟩
      have hl := absFV_lamsOf x (d := d) he
      rw [absFV_body] at hl
      exact hl
    · cases h
  · cases h

/-! ## The λ□ side -/

theorem toBvar_mkApps (x : FVarId) (d : Nat) :
    ∀ (f : LBTerm) (as : List LBTerm),
      _root_.toBvar x d (mkApps f as) = mkApps (_root_.toBvar x d f) (as.map (_root_.toBvar x d))
  | _, [] => rfl
  | f, a :: as => by
    rw [mkApps, toBvar_mkApps x d (.app f a) as]
    simp [_root_.toBvar, mkApps]

theorem toBvarAlts_eq (x : FVarId) (d : Nat) :
    ∀ brs : List (List BinderName × LBTerm),
      _root_.toBvarAlts x d brs = brs.map fun br => (br.1, _root_.toBvar x (d + br.1.length) br.2)
  | [] => by simp [_root_.toBvarAlts]
  | (ns, b) :: brs => by simp [_root_.toBvarAlts, toBvarAlts_eq x d brs]

theorem closedn_mkApps {k : Nat} : ∀ {f : LBTerm} {as : List LBTerm},
    closedn k (mkApps f as) = true ↔ closedn k f = true ∧ ∀ a ∈ as, closedn k a = true
  | _, [] => by simp [mkApps]
  | f, a :: as => by
    rw [mkApps, closedn_mkApps]
    simp [closedn, and_assoc]

theorem closednB_get {k : Nat} : ∀ {brs : List (List BinderName × LBTerm)} {i : Nat}
    {br : List BinderName × LBTerm}, closednB k brs = true → brs[i]? = some br →
      closedn (k + br.1.length) br.2 = true
  | [], _, _, _, h => by cases h
  | (ns, b) :: brs, 0, br, hc, h => by
    simp only [closednB, Bool.and_eq_true] at hc
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h; exact hc.1
  | (ns, b) :: brs, i + 1, br, hc, h => by
    simp only [closednB, Bool.and_eq_true] at hc
    simp only [List.getElem?_cons_succ] at h
    exact closednB_get hc.2 h

theorem FVarsIn.mono {p q : FVarId → Prop} (hpq : ∀ y, p y → q y) :
    ∀ {e : Expr}, FVarsIn p e → FVarsIn q e
  | .fvar _, h => hpq _ h
  | .app f a, h => ⟨FVarsIn.mono hpq (e := f) h.1, FVarsIn.mono hpq (e := a) h.2⟩
  | .lam _ t b _, h | .forallE _ t b _, h =>
    ⟨FVarsIn.mono hpq (e := t) h.1, FVarsIn.mono hpq (e := b) h.2⟩
  | .letE _ t v b _, h => ⟨FVarsIn.mono hpq (e := t) h.1, FVarsIn.mono hpq (e := v) h.2.1,
    FVarsIn.mono hpq (e := b) h.2.2⟩
  | .mdata _ e, h | .proj _ _ e, h => FVarsIn.mono hpq (e := e) h
  | .bvar _, _ | .sort _, _ | .const .., _ | .lit _, _ | .mvar _, _ => trivial

theorem absFV_eq_lam {x : FVarId} {d : Nat} {e : Expr} {nm : Name} {A b : Expr} {bi : BinderInfo}
    (h : absFV x d e = .lam nm A b bi) : ∃ A' b', e = .lam nm A' b' bi := by
  cases e with
  | lam => simp only [absFV, Expr.lam.injEq] at h; obtain ⟨rfl, -, -, rfl⟩ := h; exact ⟨_, _, rfl⟩
  | fvar y => simp only [absFV] at h; split at h <;> cases h
  | _ => simp only [absFV] at h; cases h

/-! ## The program's types are closed -/

/-- Every declaration's type translates, in the empty context, in some environment. -/
theorem ProgEnv.typeTr {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ}
    {P : List ConstantInfo} (h : ProgEnv P ζ E B) :
    ∀ ci ∈ P, ∃ (ζ' : Metalean.Sigs) (E' : Metalean.Env ζ') (B' : Binds ζ')
      (T : Metalean.Expr ζ' ci.levelParams.length 0), TrM E' B' ci.levelParams .nil [] ci.type T := by
  induction h with
  | nil => intro ci hci; cases hci
  | «axiom» _ _ _ htr ih | defn _ _ _ _ htr _ ih | thm _ _ _ _ htr _ ih
  | «opaque» _ _ _ _ _ htr ih =>
    intro ci hci
    rcases List.mem_cons.mp hci with rfl | hci
    · exact ⟨_, _, _, _, htr⟩
    · exact ih ci hci
  | induct _ _ _ _ _ hct ih =>
    intro ci hci
    rcases List.mem_append.mp hci with hci | hci
    · obtain ⟨T, -, hT, -⟩ := hct ci hci
      exact ⟨_, _, _, _, hT⟩
    · exact ih ci hci
  | quot _ _ _ _ _ hq ih =>
    intro ci hci
    rcases List.mem_append.mp hci with hci | hci
    · simp only [List.mem_map, List.mem_reverse] at hci
      obtain ⟨q, hq', rfl⟩ := hci
      obtain ⟨T, -, hT, -⟩ := (hq q hq').2
      exact ⟨_, _, _, _, hT⟩
    · exact ih ci hci

/-- The types of the declarations of a sub-environment of the program have neither loose bound
variables nor free variables. -/
theorem closed_types {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ}
    {P : List ConstantInfo} {σ : EvalEnv} (henv : ProgEnv P ζ E B) (hsub : SubEnv σ.decls P) :
    ∀ c ci, findDecl σ.decls c = some ci → LBV 0 ci.type ∧ FVarsIn (fun _ => False) ci.type := by
  intro c ci hc
  obtain ⟨hm, -⟩ := findDecl_eq_some (Extend.findDecl_sub hsub hc)
  obtain ⟨_, _, _, _, hT⟩ := ProgEnv.typeTr henv ci hm
  exact ⟨by simpa using TrM.lbv hT, FVarsIn.mono (fun _ h => by simp [MLCtx.findF] at h) hT.fvarsIn⟩

/-! ## The relation -/

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {lps : List Name}

/-- Abstracting `x` into the bound variable `d`, on both sides, keeps the erasure, when the λ□
term has no loose index from `d` on (its indices are then those of the source's binders). -/
theorem Erases.absN {σ : EvalEnv} (x : FVarId)
    (hty : ∀ c ci, findDecl σ.decls c = some ci → LBV 0 ci.type ∧ FVarsIn (fun _ => False) ci.type)
    {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n} {e : Expr}
    {tb : LBTerm} (h : Erases E B lps σ Γ Δ e tb) :
    ∀ (d : Nat) (Δ₁ : MLCtx ζ lps.length n), Rel x d Δ Δ₁ → closedn d tb = true →
      Erases E B lps σ Γ Δ₁ (absFV x d e) (_root_.toBvar x d tb) := by
  have mem : ∀ {l : List Expr} {i : Nat} {y : Expr}, l[i]? = some y → y ∈ l :=
    fun h => List.mem_of_getElem? h
  have gmap : ∀ {d : Nat} {l : List Expr} {i : Nat} {y : Expr},
      (l.map (absFV x d))[i]? = some y → ∃ y₀, l[i]? = some y₀ ∧ absFV x d y₀ = y := fun h => by
    simpa only [List.getElem?_map, Option.map_eq_some_iff] using h
  have gmapB : ∀ {d : Nat} {l : List LBTerm} {i : Nat} {y : LBTerm},
      (l.map (_root_.toBvar x d))[i]? = some y → ∃ y₀, l[i]? = some y₀ ∧ _root_.toBvar x d y₀ = y :=
    fun h => by simpa only [List.getElem?_map, Option.map_eq_some_iff] using h
  have spine : ∀ (d : Nat) (c : Name) (us : List Level) (as : List Expr),
      absFV x d (mkAppN (.const c us) as.toArray) =
        mkAppN (.const c us) (as.map (absFV x d)).toArray := by
    intro d c us as
    rw [mkAppN_toArray, absFV_foldl, ← mkAppN_toArray]; rfl
  refine Erases.rec
    (motive_1 := fun Γ Δ e tb _ => ∀ (d : Nat) Δ₁, Rel x d Δ Δ₁ → closedn d tb = true →
      Erases E B lps σ Γ Δ₁ (absFV x d e) (_root_.toBvar x d tb))
    (motive_2 := fun Γ Δ k e br _ => ∀ (d : Nat) Δ₁, Rel x d Δ Δ₁ →
      closedn (d + br.1.length) br.2 = true →
      ErasesAlt E B lps σ Γ Δ₁ k (absFV x d e) (br.1, _root_.toBvar x (d + br.1.length) br.2))
    ?bvar ?fvar ?lam ?letE ?app ?const ?ctor ?cases ?casesReduced ?eta ?proj ?litZero ?litSucc
    ?mdata ?box ?done ?alam ?intro h
  case bvar =>
    intro _ _ _ i d Δ₁ _ hcl
    simp only [closedn, decide_eq_true_eq] at hcl
    simp only [absFV, _root_.toBvar, hcl, ↓reduceIte]
    exact .bvar
  case fvar =>
    intro _ _ _ y d Δ₁ _ _
    simp only [absFV, _root_.toBvar]
    split
    · exact .bvar
    · exact .fvar
  case lam =>
    intro _ _ _ _ _ _ _ _ _ hA hAt _ ih d Δ₁ W hcl
    simp only [absFV, _root_.toBvar]
    exact .lam (TrM.absN hA W) hAt (ih (d + 1) _ W.pushLam hcl)
  case letE =>
    intro _ _ _ _ _ _ _ _ _ _ _ hv hvt _ _ ihv ihb d Δ₁ W hcl
    simp only [closedn, Bool.and_eq_true] at hcl
    simp only [absFV, _root_.toBvar]
    exact .letE (TrM.absN hv W) hvt (ihv d _ W hcl.1) (ihb (d + 1) _ (W.cons _) hcl.2)
  case app =>
    intro f _ _ _ _ _ _ hns _ _ ihf iha d Δ₁ W hcl
    simp only [closedn, Bool.and_eq_true] at hcl
    simp only [absFV, _root_.toBvar]
    refine .app (fun ⟨c, us, hc, hs⟩ => hns ⟨c, us, ?_, hs⟩) (ihf d _ W hcl.1) (iha d _ W hcl.2)
    rw [absFV_getAppFn] at hc
    exact absFV_eq_const hc
  case const =>
    intro _ _ _ _ _ hat hsa d Δ₁ _ _
    simp only [absFV, _root_.toBvar]
    exact .const hat hsa
  case ctor =>
    intro _ _ _ _ _ _ _ as _ hcv hnp hid hle hlen _ ih d Δ₁ W hcl
    rw [closedn_mkApps] at hcl
    rw [spine, toBvar_mkApps]
    have hc0 : ∀ iid i, _root_.toBvar x d (.construct iid i []) = .construct iid i [] :=
      fun _ _ => rfl
    rw [hc0]
    refine .ctor hcv hnp hid (by simpa using hle) (by simpa using hlen) fun i a a' ha ha' => ?_
    obtain ⟨a₀, ha₀, rfl⟩ := gmap ha
    obtain ⟨a₀', ha₀', rfl⟩ := gmapB ha'
    exact ih i a₀ a₀' ha₀ ha₀' d _ W (hcl.2 _ (List.mem_of_getElem? ha₀'))
  case cases =>
    intro c iv _ _ _ _ _ maj _ pre alts extra _ _ hco hnr hss hid hpre halts _ hbrs hcf _ hlex _
      ihm iha ihe d Δ₁ W hcl
    rw [closedn_mkApps] at hcl
    obtain ⟨hcase, hext⟩ := hcl
    simp only [closedn, Bool.and_eq_true] at hcase
    rw [spine, toBvar_mkApps]
    simp only [List.map_append, List.map_cons, List.map_nil, _root_.toBvar]
    refine .cases hco hnr hss hid (by simpa using hpre) (by simpa using halts)
      (ihm d _ W hcase.1) (by simp [toBvarAlts_eq, hbrs]) hcf
      (fun i cn alt br k h1 h2 h3 h4 => ?_) (by simpa using hlex) (fun i a a' ha ha' => ?_)
    · obtain ⟨a₀, ha₀, rfl⟩ := gmap h2
      rw [toBvarAlts_eq, List.getElem?_map, Option.map_eq_some_iff] at h3
      obtain ⟨br₀, hbr₀, rfl⟩ := h3
      exact iha i cn a₀ br₀ k h1 ha₀ hbr₀ h4 d _ W (closednB_get hcase.2 hbr₀)
    · obtain ⟨a₀, ha₀, rfl⟩ := gmap ha
      obtain ⟨a₀', ha₀', rfl⟩ := gmapB ha'
      exact ihe i a₀ a₀' ha₀ ha₀' d _ W (hext _ (List.mem_of_getElem? ha₀'))
  case casesReduced =>
    intro c iv _ _ _ _ _ alt _ _ maj pre extra _ hco hfe hcs hcv hidx hpre _ hlex _ iha ihe
      d Δ₁ W hcl
    rw [closedn_mkApps] at hcl
    obtain ⟨halt, hext⟩ := hcl
    rw [spine, toBvar_mkApps]
    simp only [List.map_append, List.map_cons, List.map_nil, List.map_replicate]
    have hbox : _root_.toBvar x d .box = .box := rfl
    rw [hbox]
    refine .casesReduced hco hfe hcs hcv hidx (by simpa using hpre) (iha d _ W halt)
      (by simpa using hlex) fun i a a' ha ha' => ?_
    obtain ⟨a₀, ha₀, rfl⟩ := gmap ha
    obtain ⟨a₀', ha₀', rfl⟩ := gmapB ha'
    exact ihe i a₀ a₀' ha₀ ha₀' d _ W (hext _ (by simp [List.mem_of_getElem? ha₀']))
  case eta =>
    intro c _ _ _ _ _ _ _ heta _ ih d Δ₁ W hcl
    rw [spine]
    exact .eta (etaSpine?_absFV x d (hty c) heta) (ih d _ W hcl)
  case proj =>
    intro _ _ _ _ _ _ _ _ _ hss hid hS hsort _ ih d Δ₁ W hcl
    simp only [absFV, _root_.toBvar]
    exact .proj hss hid hS hsort (ih d _ W hcl)
  case litZero =>
    intro _ _ _ _ hid d Δ₁ _ _
    exact .litZero hid
  case litSucc =>
    intro _ _ _ _ _ _ hid _ ih d Δ₁ W hcl
    simp only [closedn, Bool.and_eq_true] at hcl
    exact .litSucc hid (ih d _ W hcl.2)
  case mdata =>
    intro _ _ _ _ _ _ _ ih d Δ₁ W hcl
    exact .mdata (ih d _ W hcl)
  case box =>
    intro _ _ _ _ hb d Δ₁ W _
    obtain ⟨t, ht, hie⟩ := hb
    exact .box ⟨t, TrM.absN ht W, hie⟩
  case done =>
    intro _ _ _ _ _ _ ih d Δ₁ W hcl
    simp only [List.length_nil, Nat.add_zero] at hcl ⊢
    exact .done (ih d _ W hcl)
  case alam =>
    intro _ _ _ _ _ _ _ _ _ _ _ hA hAt _ ih d Δ₁ W hcl
    have e1 : ∀ l : Nat, d + 1 + l = d + (l + 1) := fun l => by omega
    dsimp only at hcl ih ⊢
    simp only [List.length_cons] at hcl ⊢
    have := ih (d + 1) _ W.pushLam (by rw [e1]; exact hcl)
    rw [e1] at this
    simp only [absFV]
    exact .lam (TrM.absN hA W) hAt this
  case intro =>
    intro e _ _ _ _ _ _ _ _ _ _ hne he hty' _ ih d Δ₁ W hcl
    have e1 : ∀ l : Nat, d + 1 + l = d + (l + 1) := fun l => by omega
    dsimp only at hcl ih ⊢
    simp only [List.length_cons] at hcl ⊢
    have := ih (d + 1) _ W.pushLam (by rw [e1]; exact hcl)
    rw [e1] at this
    simp only [absFV, show (0 : Nat) < d + 1 by omega, ↓reduceIte] at this
    rw [show absFV x (d + 1) (e.liftLooseBVars' 0 1) = (absFV x d e).liftLooseBVars' 0 1 from
      absFV_lift x 1 e (Nat.zero_le d)] at this
    refine .intro (fun nm A b bi h => ?_) (TrM.absN he W) hty' this
    obtain ⟨A', b', rfl⟩ := absFV_eq_lam h
    exact hne nm A' b' bi rfl

end

end AbsFV

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {lps : List Name}

/-- Closing a binder that the traversal opened with a fresh free variable (`mkLambda`,
`LeanToLambdaBox/Erasure.lean:508`): if the opened body erases to a closed `tb`, the body erases to
`abstract x tb` (`LeanToLambdaBox/Basic.lean:149`) under the locals where the binder is a bound
variable. Reference: `Erases.uninstantiateN` (`L4 Relation/Abstract.lean:170`); none in MetaRocq
(DV-13). -/
theorem Erases.abstract {P : List ConstantInfo} {σ : EvalEnv} {n : Nat}
    {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n} {x : FVarId} {b : Expr}
    {tb : LBTerm} (henv : ProgEnv P ζ E B) (hsub : SubEnv σ.decls P)
    {A : Metalean.Expr ζ lps.length n} (_hx : Δ.findF x = none)
    (hfv : FVarsIn (· ≠ x) b) (hcl : closedn 0 tb = true)
    (h : Erases E B lps σ (Γ.snoc A) (Δ.pushLam (some x)) (b.instantiate1' (.fvar x)) tb) :
    Erases E B lps σ (Γ.snoc A) (Δ.pushLam none) b (_root_.abstract x tb) := by
  have := AbsFV.Erases.absN x (AbsFV.closed_types henv hsub) h 0 _ (AbsFV.Rel.zero x Δ) hcl
  rwa [AbsFV.absFV_inst hfv] at this

end

end EraseProof
