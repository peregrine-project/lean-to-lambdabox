import EraseProof.Bridge.Inst
import EraseProof.Bridge.Order
import EraseProof.Relation.Abstract
import EraseProof.Erasable.Subst
import EraseProof.Metatheory.NoConf
import EraseProof.Source.Value
import EraseProof.Bridge.Quot

/-!
# Substitution into the erasure relation

`Erases.inst` and `ErasesAlt.inst`: instantiating the innermost bound variable of an erased body
by a typed source value, on the Lean side, and substituting the value's erasure, on the λ□ side,
keeps the erasure (`MR E/ESubstitution.v:612 erases_subst0`). The proof is an induction over the
erasure at a depth `d`, with the locals related by `InstPre.MLCtx.InstA` and the Metalean contexts
by a well-typed substitution (`SubstWF`); binder translations are rebuilt by `InstPre.PreTr.instA`
and `InstPre.PreTr.recover`. At the substituted variable the value's erasure is weakened
(`RelInst.Erases.rename`, `MR E/ESubstitution.v:187 erases_weakening'`). A constructor value
substituted at the head of an application would turn `Erases.app` into a constructor spine; this
never happens in a typed body (`RelInst.NoHead`, from the typing of the body's translation by
Π/inductive no-confusion).
-/

open Lean Erasure

namespace EraseProof

namespace RelInst

/-! ## Lifting and instantiating source terms -/

/-- Lifting twice from inside the first lifted range. -/
theorem lift_lift : ∀ (e : Expr) {c s k j : Nat}, c ≤ s → s ≤ c + k →
    (e.liftLooseBVars' c k).liftLooseBVars' s j = e.liftLooseBVars' c (k + j)
  | .bvar i, c, s, k, j, h₁, h₂ => by
    simp only [Expr.liftLooseBVars']
    congr 1
    split_ifs <;> omega
  | .app f a, c, s, k, j, h₁, h₂ => by
    simp [Expr.liftLooseBVars', lift_lift f h₁ h₂, lift_lift a h₁ h₂]
  | .lam _ t b _, c, s, k, j, h₁, h₂ | .forallE _ t b _, c, s, k, j, h₁, h₂ => by
    simp [Expr.liftLooseBVars', lift_lift t h₁ h₂,
      lift_lift b (c := c + 1) (s := s + 1) (k := k) (j := j) (by omega) (by omega)]
  | .letE _ t v b _, c, s, k, j, h₁, h₂ => by
    simp [Expr.liftLooseBVars', lift_lift t h₁ h₂, lift_lift v h₁ h₂,
      lift_lift b (c := c + 1) (s := s + 1) (k := k) (j := j) (by omega) (by omega)]
  | .mdata _ e, c, s, k, j, h₁, h₂ | .proj _ _ e, c, s, k, j, h₁, h₂ => by
    simp [Expr.liftLooseBVars', lift_lift e h₁ h₂]
  | .sort _, _, _, _, _, _, _ | .const .., _, _, _, _, _, _ | .lit _, _, _, _, _, _, _ | .mvar _, _, _, _, _, _, _ | .fvar _, _, _, _, _, _, _ => rfl

/-- Lifts at two levels commute. -/
theorem lift_comm : ∀ (e : Expr) {c s m k : Nat}, c ≤ s →
    (e.liftLooseBVars' c m).liftLooseBVars' (s + m) k =
      (e.liftLooseBVars' s k).liftLooseBVars' c m
  | .bvar i, c, s, m, k, h => by
    simp only [Expr.liftLooseBVars']
    congr 1
    split_ifs <;> omega
  | .app f a, c, s, m, k, h => by
    simp [Expr.liftLooseBVars', lift_comm f h, lift_comm a h]
  | .lam _ t b _, c, s, m, k, h | .forallE _ t b _, c, s, m, k, h => by
    have := lift_comm b (c := c + 1) (s := s + 1) (m := m) (k := k) (by omega)
    rw [show s + 1 + m = s + m + 1 by omega] at this
    simp [Expr.liftLooseBVars', lift_comm t h, this]
  | .letE _ t v b _, c, s, m, k, h => by
    have := lift_comm b (c := c + 1) (s := s + 1) (m := m) (k := k) (by omega)
    rw [show s + 1 + m = s + m + 1 by omega] at this
    simp [Expr.liftLooseBVars', lift_comm t h, lift_comm v h, this]
  | .mdata _ e, c, s, m, k, h | .proj _ _ e, c, s, m, k, h => by
    simp [Expr.liftLooseBVars', lift_comm e h]
  | .sort _, _, _, _, _, _ | .const .., _, _, _, _, _ | .lit _, _, _, _, _, _ | .mvar _, _, _, _, _, _ | .fvar _, _, _, _, _, _ => rfl

/-- Lifting above an instantiation. -/
theorem inst_lift_above (x : Expr) (c k : Nat) : ∀ (b : Expr) (j : Nat),
    (b.instantiate1' x j).liftLooseBVars' (c + j) k =
      (b.liftLooseBVars' (c + j + 1) k).instantiate1' (x.liftLooseBVars' c k) j
  | .bvar i, j => by
    by_cases h₁ : i < j
    · simp [Expr.instantiate1', Expr.liftLooseBVars', h₁, show i < c + j by omega,
        show i < c + j + 1 by omega]
    · by_cases h₂ : i = j
      · subst h₂
        simp only [Expr.instantiate1', Expr.liftLooseBVars', Nat.lt_irrefl, ↓reduceIte,
          show i < c + i + 1 by omega]
        have := lift_comm x (c := 0) (s := c) (m := i) (k := k) (Nat.zero_le c)
        rw [show c + i = c + i from rfl] at this
        exact this
      · simp only [Expr.instantiate1', Expr.liftLooseBVars', h₁, h₂, ↓reduceIte]
        by_cases h₃ : i - 1 < c + j
        · simp [h₃, show i < c + j + 1 by omega, h₁, h₂]
        · simp [h₃, show ¬ i < c + j + 1 by omega,
            show ¬ i + k < j by omega, show ¬ i + k = j by omega]
          omega
  | .app f a, j => by
    simp [Expr.instantiate1', Expr.liftLooseBVars', inst_lift_above x c k f j,
      inst_lift_above x c k a j]
  | .lam _ t b _, j | .forallE _ t b _, j => by
    have := inst_lift_above x c k b (j + 1)
    rw [show c + (j + 1) = c + j + 1 by omega] at this
    simp [Expr.instantiate1', Expr.liftLooseBVars', inst_lift_above x c k t j, this]
  | .letE _ t v b _, j => by
    have := inst_lift_above x c k b (j + 1)
    rw [show c + (j + 1) = c + j + 1 by omega] at this
    simp [Expr.instantiate1', Expr.liftLooseBVars', inst_lift_above x c k t j,
      inst_lift_above x c k v j, this]
  | .mdata _ e, j | .proj _ _ e, j => by
    simp [Expr.instantiate1', Expr.liftLooseBVars', inst_lift_above x c k e j]
  | .sort _, _ | .const .., _ | .lit _, _ | .mvar _, _ | .fvar _, _ => rfl

/-- Instantiating below a lift. -/
theorem lift_inst_below (a : Expr) : ∀ (e : Expr) {s k d : Nat}, s ≤ d →
    (e.liftLooseBVars' s k).instantiate1' a (d + k) =
      (e.instantiate1' a d).liftLooseBVars' s k
  | .bvar i, s, k, d, h => by
    by_cases h₁ : i < s
    · simp [Expr.liftLooseBVars', Expr.instantiate1', h₁, show i < d + k by omega,
        show i < d by omega]
    · by_cases h₂ : i < d
      · simp [Expr.liftLooseBVars', Expr.instantiate1', h₁, h₂, show i + k < d + k by omega]
      · by_cases h₃ : i = d
        · subst h₃
          simp only [Expr.liftLooseBVars', Expr.instantiate1', h₁, ↓reduceIte, Nat.lt_irrefl]
          exact (lift_lift a (c := 0) (s := s) (k := i) (j := k) (Nat.zero_le s)
            (by omega)).symm
        · simp [Expr.liftLooseBVars', Expr.instantiate1', h₁, h₂, h₃,
            show ¬ i + k < d + k by omega, show ¬ i - 1 < s by omega]
          omega
  | .app f b, s, k, d, h => by
    simp [Expr.liftLooseBVars', Expr.instantiate1', lift_inst_below a f h, lift_inst_below a b h]
  | .lam _ t b _, s, k, d, h | .forallE _ t b _, s, k, d, h => by
    have := lift_inst_below a b (s := s + 1) (k := k) (d := d + 1) (by omega)
    rw [show d + 1 + k = d + k + 1 by omega] at this
    simp [Expr.liftLooseBVars', Expr.instantiate1', lift_inst_below a t h, this]
  | .letE _ t v b _, s, k, d, h => by
    have := lift_inst_below a b (s := s + 1) (k := k) (d := d + 1) (by omega)
    rw [show d + 1 + k = d + k + 1 by omega] at this
    simp [Expr.liftLooseBVars', Expr.instantiate1', lift_inst_below a t h,
      lift_inst_below a v h, this]
  | .mdata _ e, s, k, d, h | .proj _ _ e, s, k, d, h => by
    simp [Expr.liftLooseBVars', Expr.instantiate1', lift_inst_below a e h]
  | .sort _, _, _, _, _ | .const .., _, _, _, _ | .lit _, _, _, _, _ | .mvar _, _, _, _, _ | .fvar _, _, _, _, _ => rfl

/-- Instantiating inside a lifted range removes one lift. -/
theorem inst_lift_cancel (y : Expr) : ∀ (e : Expr) {c j n : Nat}, c ≤ j → j ≤ c + n →
    (e.liftLooseBVars' c (n + 1)).instantiate1' y j = e.liftLooseBVars' c n
  | .bvar i, c, j, n, h₁, h₂ => by
    by_cases h : i < c
    · simp [Expr.liftLooseBVars', Expr.instantiate1', h, show i < j by omega]
    · simp [Expr.liftLooseBVars', Expr.instantiate1', h, show ¬ i + (n + 1) < j by omega,
        show ¬ i + (n + 1) = j by omega]
  | .app f a, c, j, n, h₁, h₂ => by
    simp [Expr.liftLooseBVars', Expr.instantiate1', inst_lift_cancel y f h₁ h₂,
      inst_lift_cancel y a h₁ h₂]
  | .lam _ t b _, c, j, n, h₁, h₂ | .forallE _ t b _, c, j, n, h₁, h₂ => by
    simp [Expr.liftLooseBVars', Expr.instantiate1', inst_lift_cancel y t h₁ h₂,
      inst_lift_cancel y b (c := c + 1) (j := j + 1) (n := n) (by omega) (by omega)]
  | .letE _ t v b _, c, j, n, h₁, h₂ => by
    simp [Expr.liftLooseBVars', Expr.instantiate1', inst_lift_cancel y t h₁ h₂,
      inst_lift_cancel y v h₁ h₂,
      inst_lift_cancel y b (c := c + 1) (j := j + 1) (n := n) (by omega) (by omega)]
  | .mdata _ e, c, j, n, h₁, h₂ | .proj _ _ e, c, j, n, h₁, h₂ => by
    simp [Expr.liftLooseBVars', Expr.instantiate1', inst_lift_cancel y e h₁ h₂]
  | .sort _, _, _, _, _, _ | .const .., _, _, _, _, _ | .lit _, _, _, _, _, _ | .mvar _, _, _, _, _, _ | .fvar _, _, _, _, _, _ => rfl

/-- Two instantiations commute (the substitution lemma). -/
theorem inst_inst (a x : Expr) (d : Nat) : ∀ (b : Expr) (j : Nat),
    (b.instantiate1' x j).instantiate1' a (d + j) =
      (b.instantiate1' a (d + j + 1)).instantiate1' (x.instantiate1' a d) j
  | .bvar i, j => by
    by_cases h₁ : i < j
    · simp [Expr.instantiate1', h₁, show i < d + j by omega, show i < d + j + 1 by omega]
    · by_cases h₂ : i = j
      · subst h₂
        simp only [Expr.instantiate1', Nat.lt_irrefl, ↓reduceIte, show i < d + i + 1 by omega]
        rw [show d + i = d + i from rfl, lift_inst_below a x (s := 0) (k := i) (d := d)
          (Nat.zero_le d)]
      · by_cases h₃ : i < d + j + 1
        · simp [Expr.instantiate1', h₁, h₂, h₃, show i - 1 < d + j by omega]
        · by_cases h₄ : i = d + j + 1
          · subst h₄
            simp only [Expr.instantiate1', h₁, h₂, h₃, ↓reduceIte,
              show d + j + 1 - 1 = d + j by omega, Nat.lt_irrefl]
            exact (inst_lift_cancel _ a (c := 0) (j := j) (n := d + j) (Nat.zero_le j)
              (by omega)).symm
          · simp [Expr.instantiate1', h₁, h₂, h₃, h₄, show ¬ i - 1 < d + j by omega,
              show ¬ i - 1 = d + j by omega, show ¬ i - 1 < j by omega,
              show ¬ i - 1 = j by omega]
  | .app f b, j => by
    simp [Expr.instantiate1', inst_inst a x d f j, inst_inst a x d b j]
  | .lam _ t b _, j | .forallE _ t b _, j => by
    have := inst_inst a x d b (j + 1)
    rw [show d + (j + 1) = d + j + 1 by omega] at this
    simp [Expr.instantiate1', inst_inst a x d t j, this]
  | .letE _ t v b _, j => by
    have := inst_inst a x d b (j + 1)
    rw [show d + (j + 1) = d + j + 1 by omega] at this
    simp [Expr.instantiate1', inst_inst a x d t j, inst_inst a x d v j, this]
  | .mdata _ e, j | .proj _ _ e, j => by
    simp [Expr.instantiate1', inst_inst a x d e j]
  | .sort _, _ | .const .., _ | .lit _, _ | .mvar _, _ | .fvar _, _ => rfl

/-- A term without loose indices from `k` on is unchanged by instantiating at `k`. -/
theorem inst_closed (a : Expr) : ∀ {e : Expr} {k : Nat}, AbsFV.LBV k e → e.instantiate1' a k = e
  | .bvar i, k, h => by
    simp only [AbsFV.LBV] at h
    simp [Expr.instantiate1', h]
  | .app f b, _, h => by simp [Expr.instantiate1', inst_closed a h.1, inst_closed a h.2]
  | .lam _ t b _, _, h | .forallE _ t b _, _, h => by
    simp [Expr.instantiate1', inst_closed a h.1, inst_closed a h.2]
  | .letE _ t v b _, _, h => by
    simp [Expr.instantiate1', inst_closed a h.1, inst_closed a h.2.1, inst_closed a h.2.2]
  | .mdata _ e, _, h | .proj _ _ e, _, h => by simp [Expr.instantiate1', inst_closed a (e := e) h]
  | .sort _, _, _ | .const .., _, _ | .lit _, _, _ | .mvar _, _, _ | .fvar _, _, _ => rfl

/-- A term without loose indices from `c` on is unchanged by lifting from `c`. -/
theorem lift_closed : ∀ {e : Expr} {c k : Nat}, AbsFV.LBV c e → e.liftLooseBVars' c k = e
  | .bvar i, c, k, h => by
    simp only [AbsFV.LBV] at h
    simp [Expr.liftLooseBVars', h]
  | .app f b, _, _, h => by simp [Expr.liftLooseBVars', lift_closed h.1, lift_closed h.2]
  | .lam _ t b _, _, _, h | .forallE _ t b _, _, _, h => by
    simp [Expr.liftLooseBVars', lift_closed h.1, lift_closed h.2]
  | .letE _ t v b _, _, _, h => by
    simp [Expr.liftLooseBVars', lift_closed h.1, lift_closed h.2.1, lift_closed h.2.2]
  | .mdata _ e, _, _, h | .proj _ _ e, _, _, h => by
    simp [Expr.liftLooseBVars', lift_closed (e := e) h]
  | .sort _, _, _, _ | .const .., _, _, _ | .lit _, _, _, _ | .mvar _, _, _, _ | .fvar _, _, _, _ => rfl

theorem inst_foldl (a f : Expr) (as : List Expr) (d : Nat) :
    (as.foldl .app f).instantiate1' a d =
      (as.map (·.instantiate1' a d)).foldl .app (f.instantiate1' a d) := by
  induction as generalizing f with
  | nil => rfl
  | cons x as ih => simp [ih, Expr.instantiate1']

theorem inst_spine (a : Expr) (d : Nat) (c : Name) (us : List Level) (as : List Expr) :
    (mkAppN (.const c us) as.toArray).instantiate1' a d =
      mkAppN (.const c us) (as.map (·.instantiate1' a d)).toArray := by
  rw [mkAppN_toArray, inst_foldl, ← mkAppN_toArray]; rfl

theorem lift_spine (c' k : Nat) (c : Name) (us : List Level) (as : List Expr) :
    (mkAppN (.const c us) as.toArray).liftLooseBVars' c' k =
      mkAppN (.const c us) (as.map (·.liftLooseBVars' c' k)).toArray := by
  rw [mkAppN_toArray, liftLooseBVars'_foldl, ← mkAppN_toArray]; rfl

/-- The head of an instantiated spine is the instantiated head, unless the head is the
instantiated variable. -/
theorem inst_getAppFn_const {a : Expr} {d : Nat} {c : Name} {us : List Level} :
    ∀ {f : Expr}, f.getAppFn ≠ .bvar d → (f.instantiate1' a d).getAppFn = .const c us →
      f.getAppFn = .const c us
  | .app f x, hf, h => by
    simp only [Expr.getAppFn, Expr.instantiate1'] at hf h ⊢
    exact inst_getAppFn_const hf h
  | .bvar i, hf, h => by
    simp only [Expr.getAppFn, Expr.instantiate1'] at hf h
    have : i ≠ d := fun e => hf (e ▸ rfl)
    split_ifs at h <;> simp_all [Expr.getAppFn]
  | .const .., _, h => h
  | .fvar _, _, h | .mvar _, _, h | .sort _, _, h | .lam .., _, h | .forallE .., _, h
  | .letE .., _, h | .lit _, _, h | .mdata .., _, h | .proj .., _, h => by
    simp [Expr.instantiate1', Expr.getAppFn] at h

theorem piInst_inst (a : Expr) (d : Nat) :
    ∀ {as : List Expr} {T T' : Expr}, piInst as T = some T' →
      piInst (as.map (·.instantiate1' a d)) (T.instantiate1' a d) = some (T'.instantiate1' a d)
  | [], _, _, h => by cases h; rfl
  | x :: as, .forallE _ A B _, _, h => by
    simp only [piInst] at h
    simp only [List.map_cons, Expr.instantiate1', piInst]
    have := inst_inst a x d B 0
    simp only [Nat.add_zero] at this
    rw [← this]
    exact piInst_inst a d h
  | _ :: _, .bvar _, _, h | _ :: _, .fvar _, _, h | _ :: _, .mvar _, _, h
  | _ :: _, .sort _, _, h | _ :: _, .const .., _, h | _ :: _, .app .., _, h
  | _ :: _, .lam .., _, h | _ :: _, .letE .., _, h | _ :: _, .lit _, _, h
  | _ :: _, .mdata .., _, h | _ :: _, .proj .., _, h => by cases h

theorem piInst_lift (c k : Nat) :
    ∀ {as : List Expr} {T T' : Expr}, piInst as T = some T' →
      piInst (as.map (·.liftLooseBVars' c k)) (T.liftLooseBVars' c k) =
        some (T'.liftLooseBVars' c k)
  | [], _, _, h => by cases h; rfl
  | x :: as, .forallE _ A B _, _, h => by
    simp only [piInst] at h
    simp only [List.map_cons, Expr.liftLooseBVars', piInst]
    have := inst_lift_above x c k B 0
    simp only [Nat.add_zero] at this
    rw [← this]
    exact piInst_lift c k h
  | _ :: _, .bvar _, _, h | _ :: _, .fvar _, _, h | _ :: _, .mvar _, _, h
  | _ :: _, .sort _, _, h | _ :: _, .const .., _, h | _ :: _, .app .., _, h
  | _ :: _, .lam .., _, h | _ :: _, .letE .., _, h | _ :: _, .lit _, _, h
  | _ :: _, .mdata .., _, h | _ :: _, .proj .., _, h => by cases h

theorem lamsOf_inst (a : Expr) :
    ∀ {m d : Nat} {T body e : Expr}, lamsOf m T body = some e →
      lamsOf m (T.instantiate1' a d) (body.instantiate1' a (d + m)) = some (e.instantiate1' a d)
  | 0, d, _, _, _, h => by cases h; rfl
  | m + 1, d, .forallE _ D B _, body, e, h => by
    simp only [lamsOf, Option.map_eq_some_iff] at h
    obtain ⟨e₀, he₀, rfl⟩ := h
    have := lamsOf_inst a (d := d + 1) he₀
    rw [show d + 1 + m = d + (m + 1) by omega] at this
    simp [Expr.instantiate1', lamsOf, this]
  | _ + 1, _, .bvar _, _, _, h | _ + 1, _, .fvar _, _, _, h | _ + 1, _, .mvar _, _, _, h
  | _ + 1, _, .sort _, _, _, h | _ + 1, _, .const .., _, _, h | _ + 1, _, .app .., _, _, h
  | _ + 1, _, .lam .., _, _, h | _ + 1, _, .letE .., _, _, h | _ + 1, _, .lit _, _, _, h
  | _ + 1, _, .mdata .., _, _, h | _ + 1, _, .proj .., _, _, h => by cases h

theorem lamsOf_lift (k : Nat) :
    ∀ {m c : Nat} {T body e : Expr}, lamsOf m T body = some e →
      lamsOf m (T.liftLooseBVars' c k) (body.liftLooseBVars' (c + m) k) =
        some (e.liftLooseBVars' c k)
  | 0, c, _, _, _, h => by cases h; rfl
  | m + 1, c, .forallE _ D B _, body, e, h => by
    simp only [lamsOf, Option.map_eq_some_iff] at h
    obtain ⟨e₀, he₀, rfl⟩ := h
    have := lamsOf_lift k (c := c + 1) he₀
    rw [show c + 1 + m = c + (m + 1) by omega] at this
    simp [Expr.liftLooseBVars', lamsOf, this]
  | _ + 1, _, .bvar _, _, _, h | _ + 1, _, .fvar _, _, _, h | _ + 1, _, .mvar _, _, _, h
  | _ + 1, _, .sort _, _, _, h | _ + 1, _, .const .., _, _, h | _ + 1, _, .app .., _, _, h
  | _ + 1, _, .lam .., _, _, h | _ + 1, _, .letE .., _, _, h | _ + 1, _, .lit _, _, _, h
  | _ + 1, _, .mdata .., _, _, h | _ + 1, _, .proj .., _, _, h => by cases h

theorem body_inst (a : Expr) (d m : Nat) (c : Name) (us : List Level) (as : List Expr) :
    (mkAppN (.const c us)
      (as.map (·.liftLooseBVars' 0 m) ++ (List.range m).reverse.map Expr.bvar).toArray).instantiate1'
        a (d + m) =
    mkAppN (.const c us) ((as.map (·.instantiate1' a d)).map (·.liftLooseBVars' 0 m) ++
      (List.range m).reverse.map Expr.bvar).toArray := by
  rw [inst_spine]
  simp only [List.map_append, List.map_map]
  congr 3
  · refine List.map_congr_left fun x _ => ?_
    exact lift_inst_below a x (s := 0) (k := m) (Nat.zero_le d)
  · refine List.map_congr_left fun j hj => ?_
    have : j < m := by simpa using hj
    simp [Expr.instantiate1', show j < d + m by omega]

theorem body_lift (c' k m : Nat) (c : Name) (us : List Level) (as : List Expr) :
    (mkAppN (.const c us)
      (as.map (·.liftLooseBVars' 0 m) ++ (List.range m).reverse.map Expr.bvar).toArray).liftLooseBVars'
        (c' + m) k =
    mkAppN (.const c us) ((as.map (·.liftLooseBVars' c' k)).map (·.liftLooseBVars' 0 m) ++
      (List.range m).reverse.map Expr.bvar).toArray := by
  rw [lift_spine]
  simp only [List.map_append, List.map_map]
  congr 3
  · refine List.map_congr_left fun x _ => ?_
    exact lift_comm x (c := 0) (s := c') (Nat.zero_le c')
  · refine List.map_congr_left fun j hj => ?_
    have : j < m := by simpa using hj
    simp [Expr.liftLooseBVars', show j < c' + m by omega]

/-- The η-expansion of a spine commutes with instantiation, when the head's type is closed. -/
theorem etaSpine?_inst {σ : EvalEnv} {c : Name} {us : List Level} {as : List Expr} {e' : Expr}
    (a : Expr) (d : Nat) (hty : ∀ ci, findDecl σ.decls c = some ci → AbsFV.LBV 0 ci.type)
    (h : σ.etaSpine? c us as = some e') :
    σ.etaSpine? c us (as.map (·.instantiate1' a d)) = some (e'.instantiate1' a d) := by
  unfold EvalEnv.etaSpine? at h ⊢
  split at h
  · rename_i ci ar hci har
    simp only [List.length_map]
    split at h
    · rename_i hlt
      simp only [hlt, ↓reduceIte, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨ty, hty', he⟩ := h
      have hcl : (Pure.instLevels ci.levelParams us ci.type).instantiate1' a d =
          Pure.instLevels ci.levelParams us ci.type :=
        inst_closed a (AbsFV.LBV.mono (AbsFV.LBV_instLevels _ _ (hty ci hci)) (Nat.zero_le _))
      refine ⟨ty.instantiate1' a d, by rw [← hcl]; exact piInst_inst a d hty', ?_⟩
      have hl := lamsOf_inst a (d := d) he
      rw [body_inst] at hl
      exact hl
    · cases h
  · cases h

/-- The η-expansion of a spine commutes with lifting, when the head's type is closed. -/
theorem etaSpine?_lift {σ : EvalEnv} {c : Name} {us : List Level} {as : List Expr} {e' : Expr}
    (c' k : Nat) (hty : ∀ ci, findDecl σ.decls c = some ci → AbsFV.LBV 0 ci.type)
    (h : σ.etaSpine? c us as = some e') :
    σ.etaSpine? c us (as.map (·.liftLooseBVars' c' k)) = some (e'.liftLooseBVars' c' k) := by
  unfold EvalEnv.etaSpine? at h ⊢
  split at h
  · rename_i ci ar hci har
    simp only [List.length_map]
    split at h
    · rename_i hlt
      simp only [hlt, ↓reduceIte, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨ty, hty', he⟩ := h
      have hcl : (Pure.instLevels ci.levelParams us ci.type).liftLooseBVars' c' k =
          Pure.instLevels ci.levelParams us ci.type :=
        lift_closed (AbsFV.LBV.mono (AbsFV.LBV_instLevels _ _ (hty ci hci)) (Nat.zero_le _))
      refine ⟨ty.liftLooseBVars' c' k, by rw [← hcl]; exact piInst_lift c' k hty', ?_⟩
      have hl := lamsOf_lift k (c := c') he
      rw [body_lift] at hl
      exact hl
    · cases h
  · cases h

/-! ## The λ□ side -/

theorem csubst_mkApps (t : LBTerm) (k : Nat) :
    ∀ (f : LBTerm) (as : List LBTerm), csubst t k (mkApps f as) = mkApps (csubst t k f) (as.map (csubst t k))
  | _, [] => rfl
  | f, a :: as => by
    rw [mkApps, csubst_mkApps t k (.app f a) as]
    simp [csubst, mkApps]

theorem csubstB_eq (t : LBTerm) (k : Nat) :
    ∀ brs : List (List BinderName × LBTerm),
      csubstB t k brs = brs.map fun br => (br.1, csubst t (k + br.1.length) br.2)
  | [] => by simp [csubstB]
  | (ns, b) :: brs => by simp [csubstB, csubstB_eq t k brs]

/-! ## Typing under substitutions -/

section
open Metalean
variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat}

/-- A thinning into a well-formed context is a well-typed substitution. -/
theorem substWF_ofThin {n m : Nat} {Γ : Ctx ζ ℓ 0 n} {R : Ctx ζ ℓ 0 m} {ρ : Ren n m}
    (hR : E[R] ⊢ ok) (h : InstPre.Thin Γ R ρ) : E[R] ⊢ (fun v => .var (ρ v)) ⊣ Γ := by
  intro v
  rw [Expr.subst_vars, ← h.2 v]
  exact hR.var (ρ v)

/-- Erasability is stable under well-typed substitutions. Reference: `is_type_subst`
(`MR E/ESubstitution.v:346`). -/
theorem erasableTy_subst {n m : Nat} {Γ₁ : Ctx ζ ℓ 0 n} {Γ₂ : Ctx ζ ℓ 0 m}
    {ς : Subst ζ ℓ n m} {T : Expr ζ ℓ n} (hς : E[Γ₂] ⊢ ς ⊣ Γ₁)
    (h : IsArity E Γ₁ T ∨ E[Γ₁] ⊢ T : .prop) :
    IsArity E Γ₂ (T.subst ς) ∨ E[Γ₂] ⊢ T.subst ς : .prop := by
  rcases h with ⟨k, Δ, u, hA⟩ | hP
  · refine .inl ⟨k, Ctx.substN ς k Δ, u, ?_⟩
    simpa [Ctx.pi_subst] using hA.substitution hς
  · exact .inr (by simpa [Expr.subst] using hP.substitution hς)

theorem IsErasable.subst {n m : Nat} {Γ₁ : Ctx ζ ℓ 0 n} {Γ₂ : Ctx ζ ℓ 0 m}
    {ς : Subst ζ ℓ n m} {t : Expr ζ ℓ n} (hς : E[Γ₂] ⊢ ς ⊣ Γ₁) (h : IsErasable E Γ₁ t) :
    IsErasable E Γ₂ (t.subst ς) :=
  let ⟨T, hT, hA⟩ := h
  ⟨T.subst ς, hT.substitution hς, erasableTy_subst hς hA⟩

/-- Erasability transfers along definitional equality at the erasability type. -/
theorem IsErasable.of_defeq {n : Nat} {Γ : Ctx ζ ℓ 0 n} {t t' T : Expr ζ ℓ n}
    (hT : E[Γ] ⊢ t ≡ t' : T) (hA : IsArity E Γ T ∨ E[Γ] ⊢ T : .prop) : IsErasable E Γ t' :=
  ⟨T, hT.right, hA⟩

/-- A term whose type is an inductive or a quotient type, or a constructor or `Quot.mk` node: never
a function. -/
def HB {n : Nat} (E : Env ζ) (R : Ctx ζ ℓ 0 n) (x : Expr ζ ℓ n) : Prop :=
  (∃ (I : Expr ζ ℓ n) (ι : IndSig) (η : Head ζ (.inductive ι)) (s : Fin ι.nsorts)
      (ls : Fin ι.nlevels → Level ℓ) (ps : Fin ι.nparams → Expr ζ ℓ n)
      (is : Fin (ι.nindices s) → Expr ζ ℓ n),
      E[R] ⊢ x : I ∧ E[R] ⊢ I ≡ .ind η s ls ps is typ) ∨
  (∃ (ι : IndSig) (η : Head ζ (.inductive ι)) (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (ls : Fin ι.nlevels → Level ℓ) (ps : Fin ι.nparams → Expr ζ ℓ n)
    (fds : Fin (ι.ctors s c).nfields → Expr ζ ℓ n)
    (recFds : Fin (ι.ctors s c).nrecFields → Expr ζ ℓ n), x = .ctor η s c ls ps fds recFds) ∨
  (∃ (I : Expr ζ ℓ n) (θ : Head ζ .quot) (l : Level ℓ) (α r : Expr ζ ℓ n),
      E[R] ⊢ x : I ∧ E[R] ⊢ I ≡ .quot θ l α r typ) ∨
  ∃ (θ : Head ζ .quot) (l : Level ℓ) (α r a : Expr ζ ℓ n), x = .quotMk θ l α r a

theorem HB.subst {n m : Nat} {R : Ctx ζ ℓ 0 n} {R' : Ctx ζ ℓ 0 m} {ς : Subst ζ ℓ n m}
    {x : Expr ζ ℓ n} (hς : E[R'] ⊢ ς ⊣ R) : HB E R x → HB E R' (x.subst ς)
  | .inl ⟨I, ι, η, s, ls, ps, is, hx, hI⟩ =>
    .inl ⟨I.subst ς, ι, η, s, ls, _, _, hx.substitution hς, by
      simpa [Expr.subst] using hI.substitution hς⟩
  | .inr (.inl ⟨ι, η, s, c, ls, ps, fds, recFds, hx⟩) =>
    .inr (.inl ⟨ι, η, s, c, ls, fun i => (ps i).subst ς, fun i => (fds i).subst ς,
      fun i => (recFds i).subst ς, by subst hx; simp [Expr.subst]⟩)
  | .inr (.inr (.inl ⟨I, θ, l, α, r, hx, hI⟩)) =>
    .inr (.inr (.inl ⟨I.subst ς, θ, l, α.subst ς, r.subst ς, hx.substitution hς, by
      simpa [Expr.subst] using hI.substitution hς⟩))
  | .inr (.inr (.inr ⟨θ, l, α, r, a, hx⟩)) =>
    .inr (.inr (.inr ⟨θ, l, α.subst ς, r.subst ς, a.subst ς, by subst hx; rfl⟩))

theorem HB.wk {n : Nat} {R : Ctx ζ ℓ 0 n} {A x : Expr ζ ℓ n} (hR : E[R] ⊢ ok) (h : HB E R x) :
    HB E (R.snoc A) x.wk := by
  have := h.subst (SubstWF.wk A hR)
  rwa [Expr.subst_wk] at this

theorem HB.false {n : Nat} {R : Ctx ζ ℓ 0 n} {x X : Expr ζ ℓ n} {Y : Expr ζ ℓ (n + 1)}
    (hE : EnvWF E) (hR : E[R] ⊢ ok) (h : HB E R x) (hx : E[R] ⊢ x : .forallE X Y) : False := by
  rcases h with ⟨I, ι, η, s, ls, ps, is, hxI, hI⟩ | ⟨ι, η, s, c, ls, ps, fds, recFds, rfl⟩ |
    ⟨I, θ, l, α, r, hxI, hI⟩ | ⟨θ, l, α, r, a, rfl⟩
  · exact TypeEq.forallE_ne_ind hE hR ((Defeq.uniqTy hE hR hx hxI).trans hI)
  · obtain ⟨_, _, _, _, _, _, hT⟩ := hx.ctor_inv
    exact TypeEq.forallE_ne_ind hE hR hT.2
  · exact TypeEq.forallE_ne_quot hE hR ((Defeq.uniqTy hE hR hx hxI).trans hI)
  · exact TypeEq.forallE_ne_quot hE hR hx.quotMk_inv

end

/-! ## Variables never applied -/

/-- No application node of `e` outside binder types has the bound variable `d` (shifted under
binders) as its head. -/
def NoHead : Nat → Expr → Prop
  | d, .app f x => f.getAppFn ≠ .bvar d ∧ NoHead d f ∧ NoHead d x
  | d, .lam _ _ b _ => NoHead (d + 1) b
  | d, .letE _ _ v b _ => NoHead d v ∧ NoHead (d + 1) b
  | d, .mdata _ e => NoHead d e
  | d, .proj _ _ e => NoHead d e
  | _, _ => True

theorem NoHead.foldl {d : Nat} : ∀ {f : Expr} {as : List Expr}, NoHead d (as.foldl .app f) →
    NoHead d f ∧ ∀ x ∈ as, NoHead d x
  | _, [], h => ⟨h, by simp⟩
  | f, x :: as, h => by
    obtain ⟨⟨-, hf, hx⟩, has⟩ := NoHead.foldl (f := .app f x) (as := as) h
    exact ⟨hf, fun y hy => by
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · exact has y hy⟩

theorem NoHead.of_foldl {d : Nat} : ∀ {f : Expr} {as : List Expr}, f.getAppFn ≠ .bvar d →
    NoHead d f → (∀ x ∈ as, NoHead d x) → NoHead d (as.foldl .app f)
  | _, [], _, hf, _ => hf
  | f, x :: as, hn, hf, has =>
    NoHead.of_foldl (f := .app f x) (as := as) hn
      ⟨hn, hf, has x (by simp)⟩ fun y hy => has y (by simp [hy])

theorem NoHead.spine {d : Nat} {c : Name} {us : List Level} {as : List Expr} :
    NoHead d (mkAppN (.const c us) as.toArray) ↔ ∀ x ∈ as, NoHead d x := by
  rw [mkAppN_toArray]
  exact ⟨fun h => (NoHead.foldl h).2, fun h => NoHead.of_foldl (by simp [Expr.getAppFn]) trivial h⟩

theorem NoHead.lift : ∀ {e : Expr} {d c k : Nat}, c ≤ d → NoHead d e →
    NoHead (d + k) (e.liftLooseBVars' c k)
  | .app f x, d, c, k, hc, ⟨hn, hf, hx⟩ => by
    refine ⟨fun h => hn ?_, NoHead.lift hc hf, NoHead.lift hc hx⟩
    rw [liftLooseBVars'_getAppFn] at h
    generalize f.getAppFn = g at h
    cases g <;> simp only [Expr.liftLooseBVars', Expr.bvar.injEq, reduceCtorEq] at h
    split_ifs at h <;> (congr 1; omega)
  | .lam _ _ b _, d, c, k, hc, h => by
    have := NoHead.lift (e := b) (k := k) (by omega : c + 1 ≤ d + 1) h
    rw [show d + 1 + k = d + k + 1 by omega] at this
    exact this
  | .letE _ _ v b _, d, c, k, hc, ⟨hv, hb⟩ => by
    have := NoHead.lift (e := b) (k := k) (by omega : c + 1 ≤ d + 1) hb
    rw [show d + 1 + k = d + k + 1 by omega] at this
    exact ⟨NoHead.lift hc hv, this⟩
  | .mdata _ e, _, _, _, hc, h | .proj _ _ e, _, _, _, hc, h => NoHead.lift (e := e) hc h
  | .bvar _, _, _, _, _, _ | .fvar _, _, _, _, _, _ | .mvar _, _, _, _, _, _
  | .sort _, _, _, _, _, _ | .const .., _, _, _, _, _ | .forallE .., _, _, _, _, _
  | .lit _, _, _, _, _, _ => trivial

theorem NoHead.of_lamsOf : ∀ {m d : Nat} {T body e : Expr}, lamsOf m T body = some e →
    NoHead (d + m) body → NoHead d e
  | 0, d, _, _, _, h, hb => by cases h; exact hb
  | m + 1, d, .forallE _ D B _, body, e, h, hb => by
    simp only [lamsOf, Option.map_eq_some_iff] at h
    obtain ⟨e₀, he₀, rfl⟩ := h
    exact NoHead.of_lamsOf (d := d + 1) he₀ (by rwa [show d + 1 + m = d + (m + 1) by omega])
  | _ + 1, _, .bvar _, _, _, h, _ | _ + 1, _, .fvar _, _, _, h, _ | _ + 1, _, .mvar _, _, _, h, _
  | _ + 1, _, .sort _, _, _, h, _ | _ + 1, _, .const .., _, _, h, _
  | _ + 1, _, .app .., _, _, h, _ | _ + 1, _, .lam .., _, _, h, _
  | _ + 1, _, .letE .., _, _, h, _ | _ + 1, _, .lit _, _, _, h, _
  | _ + 1, _, .mdata .., _, _, h, _ | _ + 1, _, .proj .., _, _, h, _ => by cases h

theorem NoHead.etaSpine {σ : EvalEnv} {c : Name} {us : List Level} {as : List Expr} {e' : Expr}
    {d : Nat} (h : σ.etaSpine? c us as = some e') (has : ∀ x ∈ as, NoHead d x) : NoHead d e' := by
  unfold EvalEnv.etaSpine? at h
  split at h
  · split at h
    · simp only [Option.bind_eq_some_iff] at h
      obtain ⟨ty, -, he⟩ := h
      refine NoHead.of_lamsOf he (NoHead.spine.mpr fun x hx => ?_)
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        simpa using NoHead.lift (c := 0) (Nat.zero_le d) (has y hy)
      · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
        trivial
    · cases h
  · cases h

section
open Metalean InstPre
variable {ζ : Sigs} {E : Env ζ} {B : Binds ζ} {lps : List Name}

theorem PreTr.app_bvar_inv {n : Nat} {Δ : MLCtx ζ lps.length n} {f x : Lean.Expr}
    {t : Expr ζ lps.length n} {i : Nat} (h : PreTr E B lps Δ (.app f x) t)
    (hf : f.getAppFn = .bvar i) :
    ∃ f' x', t = .app f' x' ∧ PreTr E B lps Δ f f' ∧ PreTr E B lps Δ x x' := by
  generalize he : Lean.Expr.app f x = e at h
  cases h with
  | app _ hf' hx' => cases he; exact ⟨_, _, rfl, hf', hx'⟩
  | special =>
    exfalso
    have := congrArg Lean.Expr.getAppFn he
    rw [mkAppN_toArray, foldl_app_getAppFn] at this
    simp [Lean.Expr.getAppFn, hf] at this
  | _ => cases he

theorem PreTr.bvar_inv {n : Nat} {Δ : MLCtx ζ lps.length n} {i : Nat} {t : Expr ζ lps.length n}
    (h : PreTr E B lps Δ (.bvar i) t) : Δ.findB i = some t := by
  generalize he : Lean.Expr.bvar i = e at h
  cases h with
  | bvar h' => cases he; exact h'
  | special =>
    exfalso
    have := congrArg Lean.Expr.getAppFn he
    rw [mkAppN_toArray, foldl_app_getAppFn] at this
    simp [Lean.Expr.getAppFn] at this
  | _ => cases he

/-- A typed function whose source head is the bound variable `d`: the term `d` denotes is a
function. -/
theorem PreTr.head_forall {n m : Nat} {Δ : MLCtx ζ lps.length n} {R : Ctx ζ lps.length 0 m}
    {ρ : Ren n m} {d : Nat} {hd : Expr ζ lps.length n} (hfd : Δ.findB d = some hd) :
    ∀ {f : Lean.Expr} {f' : Expr ζ lps.length n} {X : Expr ζ lps.length m}
      {Y : Expr ζ lps.length (m + 1)}, PreTr E B lps Δ f f' → f.getAppFn = .bvar d →
      E[R] ⊢ f'.rename ρ : .forallE X Y →
      ∃ (X : Expr ζ lps.length m) (Y : Expr ζ lps.length (m + 1)),
        E[R] ⊢ hd.rename ρ : .forallE X Y
  | .bvar i, f', X, Y, h, hf, ht => by
    simp only [Lean.Expr.getAppFn, Lean.Expr.bvar.injEq] at hf
    subst hf
    have := PreTr.bvar_inv h
    rw [hfd] at this
    cases this
    exact ⟨_, _, ht⟩
  | .app f x, f', X, Y, h, hf, ht => by
    obtain ⟨f₁, x₁, rfl, hf₁, -⟩ := PreTr.app_bvar_inv h hf
    rw [← Expr.subst_vars] at ht
    obtain ⟨_, _, hfa, -, -⟩ := ht.app_inv
    simp only [Expr.subst_vars] at hfa
    exact PreTr.head_forall hfd hf₁ hf hfa
  | .fvar _, _, _, _, _, hf, _ | .mvar _, _, _, _, _, hf, _ | .sort _, _, _, _, _, hf, _
  | .const .., _, _, _, _, hf, _ | .lam .., _, _, _, _, hf, _ | .forallE .., _, _, _, _, hf, _
  | .letE .., _, _, _, _, hf, _ | .lit _, _, _, _, _, hf, _ | .mdata .., _, _, _, _, hf, _
  | .proj .., _, _, _, _, hf, _ => by simp [Lean.Expr.getAppFn] at hf

/-- A pre-translation typed in some well-formed context: the bound variable `d`, whose
denotation is not a function there (`HB`), is never applied. -/
theorem PreTr.noHead (hE : EnvWF E)
    (hord : ∀ c {ι : IndSig} (η : Head ζ (.inductive ι)) (s : Fin ι.nsorts)
      (k : Fin (ι.nctors s)) (o : List Nat), B c = some (.ctor η s k o) →
      MetaOrderOK o (ι.ctors s k).nfields (ι.ctors s k).nrecFields)
    {n : Nat} {Δ : MLCtx ζ lps.length n} {e : Lean.Expr} {t : Expr ζ lps.length n}
    (h : PreTr E B lps Δ e t) :
    ∀ {d : Nat} {hd : Expr ζ lps.length n} {m : Nat} {R : Ctx ζ lps.length 0 m} {ρ : Ren n m},
      Δ.findB d = some hd → E[R] ⊢ ok → HB E R (hd.rename ρ) →
      (∃ T, E[R] ⊢ t.rename ρ : T) → NoHead d e := by
  induction h with
  | bvar _ | fvar _ | sort _ | const _ _ | lit _ => intros; trivial
  | forallE _ _ _ _ => intros; trivial
  | @special c us _ _ as as' b _ hb hs hlen _ hsat ih =>
    intro d hd m R ρ hfd hR hhb ht
    refine NoHead.spine.mpr fun x hx => ?_
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hi' : i < as'.length := hlen ▸ hi
    have hsat' := hsat.subst (fun v => .var (ρ v))
    simp only [Expr.subst_vars] at hsat'
    have hmem : (as'[i]).rename ρ ∈ as'.map (·.rename ρ) :=
      List.mem_map.mpr ⟨_, List.getElem_mem hi', rfl⟩
    obtain ⟨m', R', ρ', hth', hR', T', ht'⟩ := SatTr.args_typed hsat'
      (fun η s k o hbo => hord c η s k o (hbo ▸ hb)) hR (by simpa using ht) _ hmem
    rw [Expr.rename_rename] at ht'
    refine ih i _ as'[i] (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hi') hfd hR' ?_
      ⟨_, ht'⟩
    have := hhb.subst (substWF_ofThin hR' hth')
    rwa [Expr.subst_vars, Expr.rename_rename] at this
  | app _ hf _ ihf ihx =>
    intro d hd m R ρ hfd hR hhb ⟨T, ht⟩
    rw [← Expr.subst_vars] at ht
    obtain ⟨_, _, hfa, hxa, -⟩ := ht.app_inv
    simp only [Expr.subst_vars] at hfa hxa
    refine ⟨fun hfn => ?_, ihf hfd hR hhb ⟨_, hfa⟩, ihx hfd hR hhb ⟨_, hxa⟩⟩
    obtain ⟨X, Y, hX⟩ := PreTr.head_forall hfd hf hfn hfa
    exact HB.false hE hR hhb hX
  | lam _ _ _ ihb =>
    intro d hd m R ρ hfd hR hhb ⟨T, ht⟩
    rw [← Expr.subst_vars] at ht
    simp only [Expr.subst, vars_lift, Expr.subst_vars] at ht
    obtain ⟨_, hb, hT⟩ := ht.lam_inv hR
    obtain ⟨_, hfa⟩ := hT.right
    obtain ⟨_, _, hA, -, -⟩ := hfa.forallE_ty_inv
    refine ihb (d := d + 1) (hd := hd.wk) (ρ := ρ.lift) ?_ (.snoc hR ⟨_, hA⟩) ?_ ⟨_, hb⟩
    · simp [MLCtx.pushLam, MLCtx.findB, MLCtx.findB_map_wk, hfd]
    · rw [wk_rename_lift]
      exact hhb.wk hR
  | letE _ _ _ _ ihv ihb =>
    intro d hd m R ρ hfd hR hhb ⟨T, ht⟩
    rw [← Expr.subst_vars] at ht
    simp only [Expr.subst, vars_lift, Expr.subst_vars] at ht
    obtain ⟨_, ⟨_, hA⟩, hv, hb, -⟩ := ht.letE_inv hR
    rw [wk_rename_lift, Expr.inst_wk] at hb
    exact ⟨ihv hfd hR hhb ⟨_, hv⟩, ihb (d := d + 1) (by simpa [MLCtx.findB] using hfd) hR hhb ⟨_, hb⟩⟩
  | mdata _ ih => intro d hd m R ρ hfd hR hhb ht; exact ih hfd hR hhb ht
  | projStruct hst hi hS _ ih =>
    intro d hd m R ρ hfd hR hhb ⟨T, ht⟩
    rw [← Expr.subst_vars, Inductive.IsStructure.projTerm_subst,
      Inductive.IsStructure.projTerm_eq_recr] at ht
    have hmaj := recr_major ht
    simp only [Expr.subst_vars] at hmaj
    exact ih hfd hR hhb ⟨_, hmaj⟩
  | projProof hi hS hs hc hr hf hns _ ih =>
    intro d hd m R ρ hfd hR hhb ⟨T, ht⟩
    rw [← Expr.subst_vars, projProofTerm_subst, projProofTerm] at ht
    have hmaj := recr_major ht
    simp only [Expr.subst_vars] at hmaj
    exact ih hfd hR hhb ⟨_, hmaj⟩

end

/-! ## Weakening of the erasure -/

section
open Metalean InstPre
variable {ζ : Sigs} {E : Env ζ} {B : Binds ζ} {lps : List Name}

/-- The translation of a lifted term, through a thinning: the renamed image. -/
theorem TrM.rename
    (hord : ∀ c {ι : IndSig} (η : Head ζ (.inductive ι)) (s : Fin ι.nsorts)
      (k : Fin (ι.nctors s)) (o : List Nat), B c = some (.ctor η s k o) →
      MetaOrderOK o (ι.ctors s k).nfields (ι.ctors s k).nrecFields)
    {n m : Nat} {Γ₁ : Ctx ζ lps.length 0 n} {Γ₂ : Ctx ζ lps.length 0 m} {Δ₁ : MLCtx ζ lps.length n}
    {Δ₂ : MLCtx ζ lps.length m} {c j : Nat} {ρ : Ren n m} {e : Lean.Expr} {t : Expr ζ lps.length n}
    (hΓ₂ : E[Γ₂] ⊢ ok) (W : MLCtx.Subs c j (fun v => .var (ρ v)) Δ₁ Δ₂)
    (h : TrM E B lps Γ₁ Δ₁ e t) {T : Expr ζ lps.length m} (ht : E[Γ₂] ⊢ t.rename ρ : T) :
    TrM E B lps Γ₂ Δ₂ (e.liftLooseBVars' c j) (t.rename ρ) := by
  have hp := (PreTr.ofTrM h).subst W
  rw [Expr.subst_vars] at hp
  exact PreTr.recover hord hp (Thin.id Γ₂) hΓ₂ ⟨_, by rw [Expr.rename_id]; exact ht⟩

/-- Weakening: inserting locals below the loose indices from `c` on keeps an erasure whose λ□
term has no loose index from `c` on. Reference: `erases_weakening'`
(`MR E/ESubstitution.v:187`). -/
theorem Erases.rename
    (hord : ∀ c {ι : IndSig} (η : Head ζ (.inductive ι)) (s : Fin ι.nsorts)
      (k : Fin (ι.nctors s)) (o : List Nat), B c = some (.ctor η s k o) →
      MetaOrderOK o (ι.ctors s k).nfields (ι.ctors s k).nrecFields)
    {σ : EvalEnv} (hty : ∀ c ci, findDecl σ.decls c = some ci → AbsFV.LBV 0 ci.type)
    {n : Nat} {Γ₁ : Ctx ζ lps.length 0 n} {Δ₁ : MLCtx ζ lps.length n} {e : Lean.Expr}
    {tb : LBTerm} (h : Erases E B lps σ Γ₁ Δ₁ e tb) :
    ∀ (m : Nat) (Γ₂ : Ctx ζ lps.length 0 m) (Δ₂ : MLCtx ζ lps.length m) (c j : Nat) (ρ : Ren n m),
      E[Γ₂] ⊢ ok → Thin Γ₁ Γ₂ ρ → MLCtx.Subs c j (fun v => .var (ρ v)) Δ₁ Δ₂ →
      closedn c tb = true → Erases E B lps σ Γ₂ Δ₂ (e.liftLooseBVars' c j) tb := by
  have gmap : ∀ {c j : Nat} {l : List Lean.Expr} {i : Nat} {y : Lean.Expr},
      (l.map (·.liftLooseBVars' c j))[i]? = some y →
        ∃ y₀, l[i]? = some y₀ ∧ y₀.liftLooseBVars' c j = y := fun h => by
    simpa only [List.getElem?_map, Option.map_eq_some_iff] using h
  have rtyp : ∀ {n m : Nat} {Γ₁ : Ctx ζ lps.length 0 n} {Γ₂ : Ctx ζ lps.length 0 m} {ρ : Ren n m}
      {x T : Expr ζ lps.length n}, E[Γ₂] ⊢ ok → Thin Γ₁ Γ₂ ρ → E[Γ₁] ⊢ x : T →
      E[Γ₂] ⊢ x.rename ρ : T.rename ρ := fun hΓ₂ hth hx => by
    have := hx.substitution (substWF_ofThin hΓ₂ hth)
    simpa only [Expr.subst_vars] using this
  refine Erases.rec
    (motive_1 := fun {n} Γ₁ Δ₁ e tb _ => ∀ (m : Nat) (Γ₂ : Ctx ζ lps.length 0 m)
      (Δ₂ : MLCtx ζ lps.length m) (c j : Nat) (ρ : Ren n m),
      E[Γ₂] ⊢ ok → Thin Γ₁ Γ₂ ρ → MLCtx.Subs c j (fun v => .var (ρ v)) Δ₁ Δ₂ →
      closedn c tb = true → Erases E B lps σ Γ₂ Δ₂ (e.liftLooseBVars' c j) tb)
    (motive_2 := fun {n} Γ₁ Δ₁ k e br _ => ∀ (m : Nat) (Γ₂ : Ctx ζ lps.length 0 m)
      (Δ₂ : MLCtx ζ lps.length m) (c j : Nat) (ρ : Ren n m),
      E[Γ₂] ⊢ ok → Thin Γ₁ Γ₂ ρ → MLCtx.Subs c j (fun v => .var (ρ v)) Δ₁ Δ₂ →
      closedn (c + br.1.length) br.2 = true →
      ErasesAlt E B lps σ Γ₂ Δ₂ k (e.liftLooseBVars' c j) br)
    ?bvar ?fvar ?lam ?letE ?app ?const ?ctor ?cases ?casesReduced ?eta ?proj ?litZero ?litSucc
    ?quotMk ?quotLift ?recLet ?recFix ?mdata ?box ?done ?alam ?intro h
  case bvar =>
    intro _ _ _ i m Γ₂ Δ₂ c j ρ _ _ _ hcl
    simp only [closedn, decide_eq_true_eq] at hcl
    simp only [Expr.liftLooseBVars', hcl, ↓reduceIte]
    exact .bvar
  case fvar => intro _ _ _ y m Γ₂ Δ₂ c j ρ _ _ _ _; exact .fvar
  case lam =>
    intro _ _ _ _ _ _ _ _ _ hA hAt _ ih m Γ₂ Δ₂ c j ρ hΓ₂ hth W hcl
    have hAt' := hAt.substitution (substWF_ofThin hΓ₂ hth)
    rw [Expr.subst_vars] at hAt'
    obtain ⟨_, hAt''⟩ := hAt'
    simp only [Expr.liftLooseBVars']
    refine .lam (TrM.rename hord hΓ₂ W hA hAt'') ⟨_, hAt''⟩ ?_
    have W' := W.pushLam
    rw [vars_lift] at W'
    exact ih _ _ _ (c + 1) j ρ.lift (.snoc hΓ₂ ⟨_, hAt''⟩) (hth.lift _) W' hcl
  case letE =>
    intro _ _ _ _ _ _ _ _ _ _ _ hv hvt _ _ ihv ihb m Γ₂ Δ₂ c j ρ hΓ₂ hth W hcl
    simp only [closedn, Bool.and_eq_true] at hcl
    obtain ⟨T, hvT⟩ := hvt
    have hvT' := rtyp hΓ₂ hth hvT
    simp only [Expr.liftLooseBVars']
    have hb := ihb _ _ _ (c + 1) j ρ hΓ₂ hth (W.cons _) hcl.2
    rw [Expr.subst_vars] at hb
    exact .letE (TrM.rename hord hΓ₂ W hv hvT') ⟨_, hvT'⟩ (ihv _ _ _ c j ρ hΓ₂ hth W hcl.1) hb
  case app =>
    intro f _ _ _ _ _ _ hns _ _ ihf iha m Γ₂ Δ₂ c j ρ hΓ₂ hth W hcl
    simp only [closedn, Bool.and_eq_true] at hcl
    simp only [Expr.liftLooseBVars']
    refine .app (fun ⟨c', us, hc, hs⟩ => hns ⟨c', us, ?_, hs⟩) (ihf _ _ _ c j ρ hΓ₂ hth W hcl.1)
      (iha _ _ _ c j ρ hΓ₂ hth W hcl.2)
    rw [liftLooseBVars'_getAppFn] at hc
    exact liftLooseBVars'_eq_const hc
  case const =>
    intro _ _ _ _ _ hat hsa hnr m Γ₂ Δ₂ c j ρ _ _ _ _
    exact .const hat hsa hnr
  case ctor =>
    intro _ _ _ _ _ _ _ as _ hcv hnp hid hle hlen _ ih m Γ₂ Δ₂ c j ρ hΓ₂ hth W hcl
    rw [AbsFV.closedn_mkApps] at hcl
    rw [lift_spine]
    refine .ctor hcv hnp hid (by simpa using hle) (by simpa using hlen) fun i a a' ha ha' => ?_
    obtain ⟨a₀, ha₀, rfl⟩ := gmap ha
    exact ih i a₀ a' ha₀ ha' _ _ _ c j ρ hΓ₂ hth W (hcl.2 _ (List.mem_of_getElem? ha'))
  case cases =>
    intro c iv _ _ _ _ _ maj _ pre alts extra _ _ hco hnr hss hid hpre halts _ hbrs hcf _ hlex _
      ihm iha ihe m Γ₂ Δ₂ c' j ρ hΓ₂ hth W hcl
    rw [AbsFV.closedn_mkApps] at hcl
    obtain ⟨hcase, hext⟩ := hcl
    simp only [closedn, Bool.and_eq_true] at hcase
    rw [lift_spine]
    simp only [List.map_append, List.map_cons, List.map_nil]
    refine .cases hco hnr hss hid (by simpa using hpre) (by simpa using halts)
      (ihm _ _ _ c' j ρ hΓ₂ hth W hcase.1) (by simpa using hbrs) hcf
      (fun i cn alt br k h1 h2 h3 h4 => ?_) (by simpa using hlex) (fun i a a' ha ha' => ?_)
    · obtain ⟨a₀, ha₀, rfl⟩ := gmap h2
      exact iha i cn a₀ br k h1 ha₀ h3 h4 _ _ _ c' j ρ hΓ₂ hth W (AbsFV.closednB_get hcase.2 h3)
    · obtain ⟨a₀, ha₀, rfl⟩ := gmap ha
      exact ihe i a₀ a' ha₀ ha' _ _ _ c' j ρ hΓ₂ hth W (hext _ (List.mem_of_getElem? ha'))
  case casesReduced =>
    intro c iv _ _ _ _ _ alt _ _ maj pre extra _ hco hfe hcs hcv hidx hpre _ hlex _ iha ihe
      m Γ₂ Δ₂ c' j ρ hΓ₂ hth W hcl
    rw [AbsFV.closedn_mkApps] at hcl
    obtain ⟨halt, hext⟩ := hcl
    rw [lift_spine]
    simp only [List.map_append, List.map_cons, List.map_nil]
    refine .casesReduced hco hfe hcs hcv hidx (by simpa using hpre)
      (iha _ _ _ c' j ρ hΓ₂ hth W halt) (by simpa using hlex) fun i a a' ha ha' => ?_
    obtain ⟨a₀, ha₀, rfl⟩ := gmap ha
    exact ihe i a₀ a' ha₀ ha' _ _ _ c' j ρ hΓ₂ hth W (hext _ (by simp [List.mem_of_getElem? ha']))
  case eta =>
    intro c _ _ _ _ _ _ _ heta _ ih m Γ₂ Δ₂ c' j ρ hΓ₂ hth W hcl
    rw [lift_spine]
    exact .eta (etaSpine?_lift c' j (hty c) heta) (ih _ _ _ c' j ρ hΓ₂ hth W hcl)
  case proj =>
    intro _ _ _ _ _ _ _ _ _ hss hid hS hsort _ ih m Γ₂ Δ₂ c j ρ hΓ₂ hth W hcl
    exact .proj hss hid hS hsort (ih _ _ _ c j ρ hΓ₂ hth W hcl)
  case litZero => intro _ _ _ _ hid m Γ₂ Δ₂ c j ρ _ _ _ _; exact .litZero hid
  case litSucc =>
    intro _ _ _ _ _ _ hid _ ih m Γ₂ Δ₂ c j ρ hΓ₂ hth W hcl
    simp only [closedn, Bool.and_eq_true] at hcl
    exact .litSucc hid (ih _ _ _ c j ρ hΓ₂ hth W hcl.2)
  case quotMk =>
    intros; rename_i hcq hk _ hlex _ iha ihe m Γ₂ Δ₂ c j ρ hΓ₂ hth W hcl
    rw [AbsFV.closedn_mkApps] at hcl
    obtain ⟨ha, hext⟩ := hcl
    rw [lift_spine]
    simp only [List.map_append, List.map_cons, List.map_nil]
    refine .quotMk hcq hk (iha _ _ _ c j ρ hΓ₂ hth W ha) (by simpa using hlex)
      fun i a a' ha ha' => ?_
    obtain ⟨a₀, ha₀, rfl⟩ := gmap ha
    exact ihe i a₀ a' ha₀ ha' _ _ _ c j ρ hΓ₂ hth W (hext _ (List.mem_of_getElem? ha'))
  case quotLift =>
    intros; rename_i hcq hk _ _ hlex _ ihf ihq ihe m Γ₂ Δ₂ c j ρ hΓ₂ hth W hcl
    rw [AbsFV.closedn_mkApps] at hcl
    obtain ⟨hf, hext⟩ := hcl
    rw [lift_spine]
    simp only [List.map_append, List.map_cons, List.map_nil]
    refine .quotLift hcq hk (ihf _ _ _ c j ρ hΓ₂ hth W hf)
      (ihq _ _ _ c j ρ hΓ₂ hth W (hext _ List.mem_cons_self)) (by simpa using hlex)
      fun i a a' ha ha' => ?_
    obtain ⟨a₀, ha₀, rfl⟩ := gmap ha
    exact ihe i a₀ a' ha₀ ha' _ _ _ c j ρ hΓ₂ hth W
      (hext _ (List.mem_cons_of_mem _ (List.mem_of_getElem? ha')))
  case recLet =>
    intro _ rv _ minors F _ _ _ maj maj' ps ms mins is extra mins' is' extra' hcr hF hps hms hmins
      his hlm _ hli _ _ hle _ ihmin ihis ihmaj ihext m Γ₂ Δ₂ c j ρ hΓ₂ hth W hcl
    obtain ⟨hml, -, -⟩ := RecLam.RecFixOf.closed hF
    have hz : (mins'.zip minors).length = rv.numMinors := by
      simp only [List.length_zip]; omega
    obtain ⟨cm, ci, cj, ce⟩ := RecLam.closedn_recLetTerm_inv (by omega) hz hcl
    rw [lift_spine, show (ps ++ ms ++ mins ++ is ++ [maj] ++ extra).map (·.liftLooseBVars' c j) =
      ps.map (·.liftLooseBVars' c j) ++ ms.map (·.liftLooseBVars' c j) ++
        mins.map (·.liftLooseBVars' c j) ++ is.map (·.liftLooseBVars' c j) ++
          [maj.liftLooseBVars' c j] ++ extra.map (·.liftLooseBVars' c j) by simp]
    refine .recLet hcr hF (by simpa using hps) (by simpa using hms) (by simpa using hmins)
      (by simpa using his) (by simpa using hlm) (fun i x x' hx hx' => ?_) (by simpa using hli)
      (fun i x x' hx hx' => ?_) (ihmaj _ _ _ c j ρ hΓ₂ hth W cj) (by simpa using hle)
      (fun i x x' hx hx' => ?_)
    · obtain ⟨x₀, hx₀, rfl⟩ := gmap hx
      exact ihmin i x₀ x' hx₀ hx' _ _ _ c j ρ hΓ₂ hth W (cm _ (List.mem_of_getElem? hx'))
    · obtain ⟨x₀, hx₀, rfl⟩ := gmap hx
      exact ihis i x₀ x' hx₀ hx' _ _ _ c j ρ hΓ₂ hth W (ci _ (List.mem_of_getElem? hx'))
    · obtain ⟨x₀, hx₀, rfl⟩ := gmap hx
      exact ihext i x₀ x' hx₀ hx' _ _ _ c j ρ hΓ₂ hth W (ce _ (List.mem_of_getElem? hx'))
  case recFix =>
    intro _ rv _ minors F _ _ _ maj maj' ps ms mins is extra ws is' extra' hcr hF hps hms hmins
      his hlw _ hws hli _ _ hle _ ihmin ihis ihmaj ihext m Γ₂ Δ₂ c j ρ hΓ₂ hth W hcl
    rw [AbsFV.closedn_mkApps] at hcl
    obtain ⟨-, hargs⟩ := hcl
    rw [lift_spine, show (ps ++ ms ++ mins ++ is ++ [maj] ++ extra).map (·.liftLooseBVars' c j) =
      ps.map (·.liftLooseBVars' c j) ++ ms.map (·.liftLooseBVars' c j) ++
        mins.map (·.liftLooseBVars' c j) ++ is.map (·.liftLooseBVars' c j) ++
          [maj.liftLooseBVars' c j] ++ extra.map (·.liftLooseBVars' c j) by simp]
    refine .recFix hcr hF (by simpa using hps) (by simpa using hms) (by simpa using hmins)
      (by simpa using his) (by simpa using hlw) (fun i x x' hx hx' => ?_) hws (by simpa using hli)
      (fun i x x' hx hx' => ?_) (ihmaj _ _ _ c j ρ hΓ₂ hth W (hargs _ (by simp)))
      (by simpa using hle) (fun i x x' hx hx' => ?_)
    · obtain ⟨x₀, hx₀, rfl⟩ := gmap hx
      exact ihmin i x₀ x' hx₀ hx' _ _ _ c j ρ hΓ₂ hth W (TargetLift.closedn_mono _ 0 c
        (hws x' (List.mem_of_getElem? hx')).1 (Nat.zero_le _))
    · obtain ⟨x₀, hx₀, rfl⟩ := gmap hx
      exact ihis i x₀ x' hx₀ hx' _ _ _ c j ρ hΓ₂ hth W
        (hargs _ (by simp [List.mem_of_getElem? hx']))
    · obtain ⟨x₀, hx₀, rfl⟩ := gmap hx
      exact ihext i x₀ x' hx₀ hx' _ _ _ c j ρ hΓ₂ hth W
        (hargs _ (by simp [List.mem_of_getElem? hx']))
  case mdata =>
    intro _ _ _ _ _ _ _ ih m Γ₂ Δ₂ c j ρ hΓ₂ hth W hcl
    exact .mdata (ih _ _ _ c j ρ hΓ₂ hth W hcl)
  case box =>
    intro _ _ _ _ hb m Γ₂ Δ₂ c j ρ hΓ₂ hth W _
    obtain ⟨t, ht, hie⟩ := hb
    have hie' := IsErasable.subst (substWF_ofThin hΓ₂ hth) hie
    rw [Expr.subst_vars] at hie'
    obtain ⟨T, hT, hA⟩ := hie'
    exact .box ⟨_, TrM.rename hord hΓ₂ W ht hT, T, hT, hA⟩
  case done =>
    intro _ _ _ _ _ _ ih m Γ₂ Δ₂ c j ρ hΓ₂ hth W hcl
    simp only [List.length_nil, Nat.add_zero] at hcl
    exact .done (ih _ _ _ c j ρ hΓ₂ hth W hcl)
  case alam =>
    intro _ _ _ _ _ _ _ _ _ _ _ hA hAt _ ih m Γ₂ Δ₂ c j ρ hΓ₂ hth W hcl
    have hAt' := hAt.substitution (substWF_ofThin hΓ₂ hth)
    rw [Expr.subst_vars] at hAt'
    obtain ⟨_, hAt''⟩ := hAt'
    simp only [Expr.liftLooseBVars']
    refine .lam (TrM.rename hord hΓ₂ W hA hAt'') ⟨_, hAt''⟩ ?_
    have W' := W.pushLam
    rw [vars_lift] at W'
    dsimp only at hcl ⊢
    simp only [List.length_cons] at hcl
    exact ih _ _ _ (c + 1) j ρ.lift (.snoc hΓ₂ ⟨_, hAt''⟩) (hth.lift _) W'
      (by rw [Nat.add_assoc, Nat.add_comm 1]; exact hcl)
  case intro =>
    intro _ _ _ e _ _ _ _ _ _ _ he hty' _ ih m Γ₂ Δ₂ c j ρ hΓ₂ hth W hcl
    have hty'' := rtyp hΓ₂ hth hty'
    simp only [← Expr.subst_vars, Expr.subst, vars_lift] at hty''
    simp only [Expr.subst_vars] at hty''
    have W' := W.pushLam
    rw [vars_lift] at W'
    dsimp only at hcl ⊢
    simp only [List.length_cons] at hcl
    obtain ⟨_, hfa⟩ := hty''.regular
    obtain ⟨_, _, hA', -, -⟩ := hfa.forallE_ty_inv
    refine .intro (TrM.rename hord hΓ₂ W he hty'') hty'' ?_
    have := ih _ _ _ (c + 1) j ρ.lift (.snoc hΓ₂ ⟨_, hA'⟩) (hth.lift _) W'
      (by rw [Nat.add_assoc, Nat.add_comm 1]; exact hcl)
    simp only [Expr.liftLooseBVars', show 0 < c + 1 by omega, ↓reduceIte] at this
    rwa [lift_comm e (c := 0) (s := c) (m := 1) (k := j) (Nat.zero_le c)] at this

end

/-! ## Substitution -/

section
open Metalean InstPre
variable {ζ : Sigs} {E : Env ζ} {B : Binds ζ} {lps : List Name}

theorem inst_getAppFn_bvar {a : Lean.Expr} {d : Nat} :
    ∀ {f : Lean.Expr}, f.getAppFn = .bvar d →
      (f.instantiate1' a d).getAppFn = (a.liftLooseBVars' 0 d).getAppFn
  | .app f x, h => by
    simp only [Lean.Expr.getAppFn, Lean.Expr.instantiate1'] at h ⊢
    exact inst_getAppFn_bvar h
  | .bvar i, h => by
    simp only [Lean.Expr.getAppFn, Lean.Expr.bvar.injEq] at h
    subst h
    simp [Lean.Expr.instantiate1']
  | .const .., h | .fvar _, h | .mvar _, h | .sort _, h | .lam .., h | .forallE .., h
  | .letE .., h | .lit _, h | .mdata .., h | .proj .., h => by simp [Lean.Expr.getAppFn] at h

theorem thin_snoc {n : Nat} (Γ : Ctx ζ ℓ 0 n) (A : Expr ζ ℓ n) :
    Thin Γ (Γ.snoc A) Fin.castSucc :=
  ⟨Fin.castSucc_injective _, fun v => by
    rw [Ctx.get_castSucc, ← Expr.subst_wk, ← Expr.subst_vars]; rfl⟩

/-- Rebuilding a typed translation after instantiation: a translation of the instantiated term,
congruent and definitionally equal to the substituted image. -/
theorem TrM.instA (hE : EnvWF E)
    (hord : ∀ c {ι : IndSig} (η : Head ζ (.inductive ι)) (s : Fin ι.nsorts)
      (k : Fin (ι.nctors s)) (o : List Nat), B c = some (.ctor η s k o) →
      MetaOrderOK o (ι.ctors s k).nfields (ι.ctors s k).nrecFields)
    {n₁ n₂ : Nat} {Γ₁ : Ctx ζ lps.length 0 n₁} {Γ₂ : Ctx ζ lps.length 0 n₂}
    {Δ₁ : MLCtx ζ lps.length n₁} {Δ₂ : MLCtx ζ lps.length n₂} {a : Lean.Expr} {d : Nat}
    {ς : Subst ζ lps.length n₁ n₂} (hΓ₂ : E[Γ₂] ⊢ ok) (hς : E[Γ₂] ⊢ ς ⊣ Γ₁)
    (W : MLCtx.InstA E B lps a d ς Δ₁ Δ₂) {X : Lean.Expr} {X' T : Expr ζ lps.length n₁}
    (h : TrM E B lps Γ₁ Δ₁ X X') (hT : E[Γ₁] ⊢ X' : T) :
    ∃ X'', TrM E B lps Γ₂ Δ₂ (X.instantiate1' a d) X'' ∧ Cg E (X'.subst ς) X'' ∧
      E[Γ₂] ⊢ X'.subst ς ≡ X'' : T.subst ς := by
  obtain ⟨t, ht, hc⟩ := (PreTr.ofTrM h).instA W
  have hd := DCong.defeq hE not_false (hc (Γ₁ := Γ₂) (Γ₂ := Γ₂)) hΓ₂ (DCong.CtxConv.refl hΓ₂)
    (hT.substitution hς)
  exact ⟨t, PreTr.recover hord ht (Thin.id Γ₂) hΓ₂ ⟨_, by rw [Expr.rename_id]; exact hd.right⟩,
    hc, hd⟩

/-- The value's erasure under one more λ-bound local. -/
theorem Erases.wkLam
    (hord : ∀ c {ι : IndSig} (η : Head ζ (.inductive ι)) (s : Fin ι.nsorts)
      (k : Fin (ι.nctors s)) (o : List Nat), B c = some (.ctor η s k o) →
      MetaOrderOK o (ι.ctors s k).nfields (ι.ctors s k).nrecFields)
    {σ : EvalEnv} (hty : ∀ c ci, findDecl σ.decls c = some ci → AbsFV.LBV 0 ci.type)
    {n : Nat} {Γ : Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n} {A : Expr ζ lps.length n}
    {a : Lean.Expr} {a' : LBTerm} {d : Nat} (hΓA : E[Γ.snoc A] ⊢ ok) (hcl : closedn 0 a' = true)
    (h : Erases E B lps σ Γ Δ (a.liftLooseBVars' 0 d) a') :
    Erases E B lps σ (Γ.snoc A) (Δ.pushLam none) (a.liftLooseBVars' 0 (d + 1)) a' := by
  have := Erases.rename hord hty h _ _ _ 0 1 Fin.castSucc hΓA (thin_snoc Γ A)
    (MLCtx.Subs.bv Δ) hcl
  rwa [liftLooseBVars'_succ] at this

/-- The value's erasure under one more `let`-bound local. -/
theorem Erases.wkLet
    (hord : ∀ c {ι : IndSig} (η : Head ζ (.inductive ι)) (s : Fin ι.nsorts)
      (k : Fin (ι.nctors s)) (o : List Nat), B c = some (.ctor η s k o) →
      MetaOrderOK o (ι.ctors s k).nfields (ι.ctors s k).nrecFields)
    {σ : EvalEnv} (hty : ∀ c ci, findDecl σ.decls c = some ci → AbsFV.LBV 0 ci.type)
    {n : Nat} {Γ : Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n} (w : Expr ζ lps.length n)
    {a : Lean.Expr} {a' : LBTerm} {d : Nat} (hΓ : E[Γ] ⊢ ok) (hcl : closedn 0 a' = true)
    (h : Erases E B lps σ Γ Δ (a.liftLooseBVars' 0 d) a') :
    Erases E B lps σ Γ ((none, .vlet w) :: Δ) (a.liftLooseBVars' 0 (d + 1)) a' := by
  have := Erases.rename hord hty h _ _ _ 0 1 Ren.id hΓ (Thin.id Γ) (MLCtx.Subs.lt Δ w) hcl
  rwa [liftLooseBVars'_succ] at this

/-- The invariant at the substituted variable when the value is a constructor spine: its
context is well formed, the body never applies it, and it denotes a non-function. -/
def HeadInv {n : Nat} (σ : EvalEnv) (E : Env ζ) (a : Lean.Expr) (Γ : Ctx ζ lps.length 0 n)
    (Δ : MLCtx ζ lps.length n) (d : Nat) (b : Lean.Expr) : Prop :=
  SpecialSpine σ a → E[Γ] ⊢ ok ∧ NoHead d b ∧ ∃ hd, Δ.findB d = some hd ∧ HB E Γ hd

/-- Substitution at the bound variable `d`, generalised. -/
theorem Erases.instG (hE : EnvWF E)
    (hord : ∀ c {ι : IndSig} (η : Head ζ (.inductive ι)) (s : Fin ι.nsorts)
      (k : Fin (ι.nctors s)) (o : List Nat), B c = some (.ctor η s k o) →
      MetaOrderOK o (ι.ctors s k).nfields (ι.ctors s k).nrecFields)
    {σ : EvalEnv} (hty : ∀ c ci, findDecl σ.decls c = some ci → AbsFV.LBV 0 ci.type)
    {a : Lean.Expr} {a' : LBTerm} (hcl : closedn 0 a' = true) :
    (∀ (n₁ : Nat) (Γ₁ : Ctx ζ lps.length 0 n₁) (Δ₁ : MLCtx ζ lps.length n₁) (b : Lean.Expr)
      (tb : LBTerm), Erases E B lps σ Γ₁ Δ₁ b tb →
      ∀ (n₂ : Nat) (Γ₂ : Ctx ζ lps.length 0 n₂) (Δ₂ : MLCtx ζ lps.length n₂) (d : Nat)
        (ς : Subst ζ lps.length n₁ n₂), E[Γ₂] ⊢ ok → E[Γ₂] ⊢ ς ⊣ Γ₁ →
        MLCtx.InstA E B lps a d ς Δ₁ Δ₂ →
        Erases E B lps σ Γ₂ Δ₂ (a.liftLooseBVars' 0 d) a' → HeadInv σ E a Γ₁ Δ₁ d b →
        Erases E B lps σ Γ₂ Δ₂ (b.instantiate1' a d) (csubst a' d tb)) ∧
    (∀ (n₁ : Nat) (Γ₁ : Ctx ζ lps.length 0 n₁) (Δ₁ : MLCtx ζ lps.length n₁) (k : Nat)
      (b : Lean.Expr) (br : List BinderName × LBTerm), ErasesAlt E B lps σ Γ₁ Δ₁ k b br →
      ∀ (n₂ : Nat) (Γ₂ : Ctx ζ lps.length 0 n₂) (Δ₂ : MLCtx ζ lps.length n₂) (d : Nat)
        (ς : Subst ζ lps.length n₁ n₂), E[Γ₂] ⊢ ok → E[Γ₂] ⊢ ς ⊣ Γ₁ →
        MLCtx.InstA E B lps a d ς Δ₁ Δ₂ →
        Erases E B lps σ Γ₂ Δ₂ (a.liftLooseBVars' 0 d) a' → HeadInv σ E a Γ₁ Δ₁ d b →
        ErasesAlt E B lps σ Γ₂ Δ₂ k (b.instantiate1' a d)
          (br.1, csubst a' (d + br.1.length) br.2)) := by
  have gmap : ∀ {d : Nat} {l : List Lean.Expr} {i : Nat} {y : Lean.Expr},
      (l.map (·.instantiate1' a d))[i]? = some y →
        ∃ y₀, l[i]? = some y₀ ∧ y₀.instantiate1' a d = y := fun h => by
    simpa only [List.getElem?_map, Option.map_eq_some_iff] using h
  have gmapB : ∀ {d : Nat} {l : List LBTerm} {i : Nat} {y : LBTerm},
      (l.map (csubst a' d))[i]? = some y → ∃ y₀, l[i]? = some y₀ ∧ csubst a' d y₀ = y :=
    fun h => by simpa only [List.getElem?_map, Option.map_eq_some_iff] using h
  have spineHI : ∀ {n₁ : Nat} {Γ₁ : Ctx ζ lps.length 0 n₁} {Δ₁ : MLCtx ζ lps.length n₁}
      {d : Nat} {c : Name} {us : List Level} {as : List Lean.Expr},
      HeadInv σ E a Γ₁ Δ₁ d (mkAppN (.const c us) as.toArray) → ∀ x ∈ as, HeadInv σ E a Γ₁ Δ₁ d x :=
    fun hi x hx hs => let ⟨h1, h2, h3⟩ := hi hs; ⟨h1, NoHead.spine.mp h2 x hx, h3⟩
  refine ⟨@Erases.rec ζ E B lps σ (fun {n₁} Γ₁ Δ₁ b tb _ => ∀ (n₂ : Nat) (Γ₂ : Ctx ζ lps.length 0 n₂)
      (Δ₂ : MLCtx ζ lps.length n₂) (d : Nat) (ς : Subst ζ lps.length n₁ n₂),
      E[Γ₂] ⊢ ok → E[Γ₂] ⊢ ς ⊣ Γ₁ → MLCtx.InstA E B lps a d ς Δ₁ Δ₂ →
      Erases E B lps σ Γ₂ Δ₂ (a.liftLooseBVars' 0 d) a' → HeadInv σ E a Γ₁ Δ₁ d b →
      Erases E B lps σ Γ₂ Δ₂ (b.instantiate1' a d) (csubst a' d tb))
    (fun {n₁} Γ₁ Δ₁ k b br _ => ∀ (n₂ : Nat) (Γ₂ : Ctx ζ lps.length 0 n₂)
      (Δ₂ : MLCtx ζ lps.length n₂) (d : Nat) (ς : Subst ζ lps.length n₁ n₂),
      E[Γ₂] ⊢ ok → E[Γ₂] ⊢ ς ⊣ Γ₁ → MLCtx.InstA E B lps a d ς Δ₁ Δ₂ →
      Erases E B lps σ Γ₂ Δ₂ (a.liftLooseBVars' 0 d) a' → HeadInv σ E a Γ₁ Δ₁ d b →
      ErasesAlt E B lps σ Γ₂ Δ₂ k (b.instantiate1' a d) (br.1, csubst a' (d + br.1.length) br.2))
    ?bvar ?fvar ?lam ?letE ?app ?const ?ctor ?cases ?casesReduced ?eta ?proj ?litZero ?litSucc
    ?quotMk ?quotLift ?recLet ?recFix ?mdata ?box ?done ?alam ?intro,
    @ErasesAlt.rec ζ E B lps σ (fun {n₁} Γ₁ Δ₁ b tb _ => ∀ (n₂ : Nat) (Γ₂ : Ctx ζ lps.length 0 n₂)
      (Δ₂ : MLCtx ζ lps.length n₂) (d : Nat) (ς : Subst ζ lps.length n₁ n₂),
      E[Γ₂] ⊢ ok → E[Γ₂] ⊢ ς ⊣ Γ₁ → MLCtx.InstA E B lps a d ς Δ₁ Δ₂ →
      Erases E B lps σ Γ₂ Δ₂ (a.liftLooseBVars' 0 d) a' → HeadInv σ E a Γ₁ Δ₁ d b →
      Erases E B lps σ Γ₂ Δ₂ (b.instantiate1' a d) (csubst a' d tb))
    (fun {n₁} Γ₁ Δ₁ k b br _ => ∀ (n₂ : Nat) (Γ₂ : Ctx ζ lps.length 0 n₂)
      (Δ₂ : MLCtx ζ lps.length n₂) (d : Nat) (ς : Subst ζ lps.length n₁ n₂),
      E[Γ₂] ⊢ ok → E[Γ₂] ⊢ ς ⊣ Γ₁ → MLCtx.InstA E B lps a d ς Δ₁ Δ₂ →
      Erases E B lps σ Γ₂ Δ₂ (a.liftLooseBVars' 0 d) a' → HeadInv σ E a Γ₁ Δ₁ d b →
      ErasesAlt E B lps σ Γ₂ Δ₂ k (b.instantiate1' a d) (br.1, csubst a' (d + br.1.length) br.2))
    ?bvar ?fvar ?lam ?letE ?app ?const ?ctor ?cases ?casesReduced ?eta ?proj ?litZero ?litSucc
    ?quotMk ?quotLift ?recLet ?recFix ?mdata ?box ?done ?alam ?intro⟩
  case bvar =>
    intro _ _ _ i n₂ Γ₂ Δ₂ d ς _ _ _ Ea _
    simp only [Lean.Expr.instantiate1', csubst]
    by_cases h₁ : i < d
    · simp only [h₁, ↓reduceIte, show d ≠ i by omega, show ¬ d < i by omega]; exact .bvar
    · by_cases h₂ : i = d
      · subst h₂; simp only [h₁, ↓reduceIte]; exact Ea
      · simp only [h₁, h₂, ↓reduceIte, show d ≠ i by omega, show d < i by omega]; exact .bvar
  case fvar => intro _ _ _ y _ _ _ _ _ _ _ _ _ _; exact .fvar
  case lam =>
    intro _ Γ₁ _ _ _ _ _ _ _ hA hAt _ ih n₂ Γ₂ Δ₂ d ς hΓ₂ hς W Ea hi
    obtain ⟨u, hAu⟩ := hAt
    obtain ⟨A'', hA'', -, hd⟩ := TrM.instA hE hord hΓ₂ hς W hA hAu
    have hAt'' : E[Γ₂] ⊢ A'' typ := ⟨u, hd.right⟩
    have hς' := SubstWF.snocConv (TypeEq.ofDefEq hd) (SubstWF.lift ⟨u, hAu⟩ hς)
    simp only [Lean.Expr.instantiate1', csubst]
    refine .lam hA'' hAt'' (ih _ _ _ (d + 1) _ (.snoc hΓ₂ hAt'') hς' W.pushLam
      (Erases.wkLam hord hty (.snoc hΓ₂ hAt'') hcl Ea) fun hs => ?_)
    obtain ⟨hΓ₁, hn, hd₀, hfd, hhb⟩ := hi hs
    exact ⟨.snoc hΓ₁ ⟨u, hAu⟩, hn, hd₀.wk,
      by simp [MLCtx.pushLam, MLCtx.findB, MLCtx.findB_map_wk, hfd], hhb.wk hΓ₁⟩
  case letE =>
    intro _ _ _ _ _ _ _ _ _ _ _ hv hvt _ _ ihv ihb n₂ Γ₂ Δ₂ d ς hΓ₂ hς W Ea hi
    obtain ⟨T, hvT⟩ := hvt
    obtain ⟨v'', hv'', hcv, hd⟩ := TrM.instA hE hord hΓ₂ hς W hv hvT
    simp only [Lean.Expr.instantiate1', csubst]
    refine .letE hv'' ⟨_, hd.right⟩
      (ihv _ _ _ d ς hΓ₂ hς W Ea fun hs => let ⟨h1, h2, h3⟩ := hi hs; ⟨h1, h2.1, h3⟩)
      (ihb _ _ _ (d + 1) ς hΓ₂ hς (W.cons hcv) (Erases.wkLet hord hty _ hΓ₂ hcl Ea) fun hs => ?_)
    obtain ⟨hΓ₁, hn, hd₀, hfd, hhb⟩ := hi hs
    exact ⟨hΓ₁, hn.2, hd₀, by simpa [MLCtx.findB] using hfd, hhb⟩
  case app =>
    intro f _ _ _ _ _ _ hns _ _ ihf iha n₂ Γ₂ Δ₂ d ς hΓ₂ hς W Ea hi
    simp only [Lean.Expr.instantiate1', csubst]
    refine .app (fun ⟨c, us, hc, hs⟩ => ?_)
      (ihf _ _ _ d ς hΓ₂ hς W Ea fun hs => let ⟨h1, h2, h3⟩ := hi hs; ⟨h1, h2.2.1, h3⟩)
      (iha _ _ _ d ς hΓ₂ hς W Ea fun hs => let ⟨h1, h2, h3⟩ := hi hs; ⟨h1, h2.2.2, h3⟩)
    by_cases hfd : f.getAppFn = .bvar d
    · rw [inst_getAppFn_bvar hfd, liftLooseBVars'_getAppFn] at hc
      have hsa : SpecialSpine σ a := ⟨c, us, liftLooseBVars'_eq_const hc, hs⟩
      exact (hi hsa).2.1.1 hfd
    · exact hns ⟨c, us, inst_getAppFn_const hfd hc, hs⟩
  case const =>
    intro _ _ _ _ _ hat hsa hnr _ _ _ _ _ _ _ _ _ _
    exact .const hat hsa hnr
  case ctor =>
    intro _ _ _ _ _ _ _ as _ hcv hnp hid hle hlen _ ih n₂ Γ₂ Δ₂ d ς hΓ₂ hς W Ea hi
    rw [inst_spine, csubst_mkApps]
    have hc0 : ∀ iid i, csubst a' d (.construct iid i []) = .construct iid i [] :=
      fun _ _ => by simp [csubst, csubstL]
    rw [hc0]
    refine .ctor hcv hnp hid (by simpa using hle) (by simpa using hlen) fun i x x' hx hx' => ?_
    obtain ⟨x₀, hx₀, rfl⟩ := gmap hx
    obtain ⟨x₀', hx₀', rfl⟩ := gmapB hx'
    exact ih i x₀ x₀' hx₀ hx₀' _ _ _ d ς hΓ₂ hς W Ea
      (spineHI hi x₀ (List.mem_of_getElem? hx₀))
  case cases =>
    intro c iv _ _ _ _ _ maj _ pre alts extra _ _ hco hnr hss hid hpre halts _ hbrs hcf _ hlex _
      ihm iha ihe n₂ Γ₂ Δ₂ d ς hΓ₂ hς W Ea hi
    have hi' := spineHI hi
    rw [inst_spine, csubst_mkApps]
    simp only [List.map_append, List.map_cons, List.map_nil, csubst]
    refine .cases hco hnr hss hid (by simpa using hpre) (by simpa using halts)
      (ihm _ _ _ d ς hΓ₂ hς W Ea (hi' maj (by simp)))
      (by simp [csubstB_eq, hbrs]) hcf
      (fun i cn alt br k h1 h2 h3 h4 => ?_) (by simpa using hlex) (fun i x x' hx hx' => ?_)
    · obtain ⟨a₀, ha₀, rfl⟩ := gmap h2
      rw [csubstB_eq, List.getElem?_map, Option.map_eq_some_iff] at h3
      obtain ⟨br₀, hbr₀, rfl⟩ := h3
      exact iha i cn a₀ br₀ k h1 ha₀ hbr₀ h4 _ _ _ d ς hΓ₂ hς W Ea
        (hi' a₀ (by simp [List.mem_of_getElem? ha₀]))
    · obtain ⟨x₀, hx₀, rfl⟩ := gmap hx
      obtain ⟨x₀', hx₀', rfl⟩ := gmapB hx'
      exact ihe i x₀ x₀' hx₀ hx₀' _ _ _ d ς hΓ₂ hς W Ea
        (hi' x₀ (by simp [List.mem_of_getElem? hx₀]))
  case casesReduced =>
    intro c iv _ _ _ _ _ alt _ _ maj pre extra _ hco hfe hcs hcv hidx hpre _ hlex _ iha ihe
      n₂ Γ₂ Δ₂ d ς hΓ₂ hς W Ea hi
    have hi' := spineHI hi
    rw [inst_spine, csubst_mkApps]
    simp only [List.map_append, List.map_cons, List.map_nil, List.map_replicate]
    have hbox : csubst a' d .box = .box := rfl
    rw [hbox]
    refine .casesReduced hco hfe hcs hcv hidx (by simpa using hpre)
      (iha _ _ _ d ς hΓ₂ hς W Ea (hi' alt (by simp))) (by simpa using hlex)
      fun i x x' hx hx' => ?_
    obtain ⟨x₀, hx₀, rfl⟩ := gmap hx
    obtain ⟨x₀', hx₀', rfl⟩ := gmapB hx'
    exact ihe i x₀ x₀' hx₀ hx₀' _ _ _ d ς hΓ₂ hς W Ea
      (hi' x₀ (by simp [List.mem_of_getElem? hx₀]))
  case eta =>
    intro c _ _ _ _ _ _ _ heta _ ih n₂ Γ₂ Δ₂ d ς hΓ₂ hς W Ea hi
    rw [inst_spine]
    refine .eta (etaSpine?_inst a d (hty c) heta) (ih _ _ _ d ς hΓ₂ hς W Ea fun hs => ?_)
    obtain ⟨h1, h2, h3⟩ := hi hs
    exact ⟨h1, NoHead.etaSpine heta (NoHead.spine.mp h2), h3⟩
  case proj =>
    intro _ _ _ _ _ _ _ _ _ hss hid hS hsort _ ih n₂ Γ₂ Δ₂ d ς hΓ₂ hς W Ea hi
    simp only [Lean.Expr.instantiate1', csubst]
    exact .proj hss hid hS hsort (ih _ _ _ d ς hΓ₂ hς W Ea hi)
  case litZero => intro _ _ _ _ hid _ _ _ _ _ _ _ _ _ _; exact .litZero hid
  case litSucc =>
    intro _ _ _ _ _ _ hid _ ih n₂ Γ₂ Δ₂ d ς hΓ₂ hς W Ea hi
    simp only [csubst]
    exact .litSucc hid (ih _ _ _ d ς hΓ₂ hς W Ea hi)
  case quotMk =>
    intros; rename_i hcq hk _ hlex _ iha ihe n₂ Γ₂ Δ₂ d ς hΓ₂ hς W Ea hi
    have hi' := spineHI hi
    rw [inst_spine, csubst_mkApps]
    simp only [List.map_append, List.map_cons, List.map_nil]
    refine .quotMk hcq hk (iha _ _ _ d ς hΓ₂ hς W Ea (hi' _ (by simp))) (by simpa using hlex)
      fun i x x' hx hx' => ?_
    obtain ⟨x₀, hx₀, rfl⟩ := gmap hx
    obtain ⟨x₀', hx₀', rfl⟩ := gmapB hx'
    exact ihe i x₀ x₀' hx₀ hx₀' _ _ _ d ς hΓ₂ hς W Ea
      (hi' x₀ (by simp [List.mem_of_getElem? hx₀]))
  case quotLift =>
    intros; rename_i hcq hk _ _ hlex _ ihf ihq ihe n₂ Γ₂ Δ₂ d ς hΓ₂ hς W Ea hi
    have hi' := spineHI hi
    rw [inst_spine, csubst_mkApps]
    simp only [List.map_append, List.map_cons, List.map_nil]
    refine .quotLift hcq hk (ihf _ _ _ d ς hΓ₂ hς W Ea (hi' _ (by simp)))
      (ihq _ _ _ d ς hΓ₂ hς W Ea (hi' _ (by simp))) (by simpa using hlex) fun i x x' hx hx' => ?_
    obtain ⟨x₀, hx₀, rfl⟩ := gmap hx
    obtain ⟨x₀', hx₀', rfl⟩ := gmapB hx'
    exact ihe i x₀ x₀' hx₀ hx₀' _ _ _ d ς hΓ₂ hς W Ea
      (hi' x₀ (by simp [List.mem_of_getElem? hx₀]))
  case recLet =>
    intro _ rv _ minors F _ _ _ maj maj' ps ms mins is extra mins' is' extra' hcr hF hps hms hmins
      his hlm _ hli _ _ hle _ ihmin ihis ihmaj ihext n₂ Γ₂ Δ₂ d ς hΓ₂ hς W Ea hi
    have hi' := spineHI hi
    obtain ⟨hml, hFc, -⟩ := RecLam.RecFixOf.closed hF
    have hz : (mins'.zip minors).length = rv.numMinors := by
      simp only [List.length_zip]; omega
    rw [RecLam.csubst_recLetTerm hcl d rv.numMinors hz hFc, inst_spine,
      show (ps ++ ms ++ mins ++ is ++ [maj] ++ extra).map (·.instantiate1' a d) =
        ps.map (·.instantiate1' a d) ++ ms.map (·.instantiate1' a d) ++
          mins.map (·.instantiate1' a d) ++ is.map (·.instantiate1' a d) ++
            [maj.instantiate1' a d] ++ extra.map (·.instantiate1' a d) by simp]
    refine .recLet hcr hF (by simpa using hps) (by simpa using hms) (by simpa using hmins)
      (by simpa using his) (by simpa using hlm) (fun i x x' hx hx' => ?_) (by simpa using hli)
      (fun i x x' hx hx' => ?_) (ihmaj _ _ _ d ς hΓ₂ hς W Ea (hi' maj (by simp)))
      (by simpa using hle) (fun i x x' hx hx' => ?_)
    · obtain ⟨x₀, hx₀, rfl⟩ := gmap hx
      obtain ⟨x₀', hx₀', rfl⟩ := gmapB hx'
      exact ihmin i x₀ x₀' hx₀ hx₀' _ _ _ d ς hΓ₂ hς W Ea
        (hi' x₀ (by simp [List.mem_of_getElem? hx₀]))
    · obtain ⟨x₀, hx₀, rfl⟩ := gmap hx
      obtain ⟨x₀', hx₀', rfl⟩ := gmapB hx'
      exact ihis i x₀ x₀' hx₀ hx₀' _ _ _ d ς hΓ₂ hς W Ea
        (hi' x₀ (by simp [List.mem_of_getElem? hx₀]))
    · obtain ⟨x₀, hx₀, rfl⟩ := gmap hx
      obtain ⟨x₀', hx₀', rfl⟩ := gmapB hx'
      exact ihext i x₀ x₀' hx₀ hx₀' _ _ _ d ς hΓ₂ hς W Ea
        (hi' x₀ (by simp [List.mem_of_getElem? hx₀]))
  case recFix =>
    intro _ rv _ minors F _ _ _ maj maj' ps ms mins is extra ws is' extra' hcr hF hps hms hmins
      his hlw _ hws hli _ _ hle _ ihmin ihis ihmaj ihext n₂ Γ₂ Δ₂ d ς hΓ₂ hς W Ea hi
    have hi' := spineHI hi
    obtain ⟨hml, hFc, hFx⟩ := RecLam.RecFixOf.closed hF
    have hG := RecLam.substl_fix (ws := ws) (by rw [← hlw, hmins]; exact hFc) hFx
      fun w hw => ⟨(hws w hw).1, (hws w hw).2.1⟩
    rw [csubst_mkApps, TargetSubst.csubst_closedn a' _ 0 d hG.1 (Nat.zero_le _), inst_spine,
      show (ps ++ ms ++ mins ++ is ++ [maj] ++ extra).map (·.instantiate1' a d) =
        ps.map (·.instantiate1' a d) ++ ms.map (·.instantiate1' a d) ++
          mins.map (·.instantiate1' a d) ++ is.map (·.instantiate1' a d) ++
            [maj.instantiate1' a d] ++ extra.map (·.instantiate1' a d) by simp,
      List.map_append, List.map_append, List.map_singleton]
    refine .recFix hcr hF (by simpa using hps) (by simpa using hms) (by simpa using hmins)
      (by simpa using his) (by simpa using hlw) (fun i x x' hx hx' => ?_) hws (by simpa using hli)
      (fun i x x' hx hx' => ?_) (ihmaj _ _ _ d ς hΓ₂ hς W Ea (hi' maj (by simp)))
      (by simpa using hle) (fun i x x' hx hx' => ?_)
    · obtain ⟨x₀, hx₀, rfl⟩ := gmap hx
      have h1 := ihmin i x₀ x' hx₀ hx' _ _ _ d ς hΓ₂ hς W Ea
        (hi' x₀ (by simp [List.mem_of_getElem? hx₀]))
      rwa [TargetSubst.csubst_closedn a' x' 0 d (hws x' (List.mem_of_getElem? hx')).1
        (Nat.zero_le _)] at h1
    · obtain ⟨x₀, hx₀, rfl⟩ := gmap hx
      obtain ⟨x₀', hx₀', rfl⟩ := gmapB hx'
      exact ihis i x₀ x₀' hx₀ hx₀' _ _ _ d ς hΓ₂ hς W Ea
        (hi' x₀ (by simp [List.mem_of_getElem? hx₀]))
    · obtain ⟨x₀, hx₀, rfl⟩ := gmap hx
      obtain ⟨x₀', hx₀', rfl⟩ := gmapB hx'
      exact ihext i x₀ x₀' hx₀ hx₀' _ _ _ d ς hΓ₂ hς W Ea
        (hi' x₀ (by simp [List.mem_of_getElem? hx₀]))
  case mdata =>
    intro _ _ _ _ _ _ _ ih n₂ Γ₂ Δ₂ d ς hΓ₂ hς W Ea hi
    exact .mdata (ih _ _ _ d ς hΓ₂ hς W Ea hi)
  case box =>
    intro _ _ _ _ hb n₂ Γ₂ Δ₂ d ς hΓ₂ hς W _ _
    obtain ⟨t, ht, T, htT, hA⟩ := hb
    obtain ⟨t'', ht'', -, hd⟩ := TrM.instA hE hord hΓ₂ hς W ht htT
    exact .box ⟨t'', ht'', IsErasable.of_defeq hd (erasableTy_subst hς hA)⟩
  case done =>
    intro _ _ _ _ _ _ ih n₂ Γ₂ Δ₂ d ς hΓ₂ hς W Ea hi
    exact .done (ih _ _ _ d ς hΓ₂ hς W Ea hi)
  case alam =>
    intro _ _ _ _ _ _ _ _ _ _ _ hA hAt _ ih n₂ Γ₂ Δ₂ d ς hΓ₂ hς W Ea hi
    obtain ⟨u, hAu⟩ := hAt
    obtain ⟨A'', hA'', -, hd⟩ := TrM.instA hE hord hΓ₂ hς W hA hAu
    have hAt'' : E[Γ₂] ⊢ A'' typ := ⟨u, hd.right⟩
    have hς' := SubstWF.snocConv (TypeEq.ofDefEq hd) (SubstWF.lift ⟨u, hAu⟩ hς)
    simp only [Lean.Expr.instantiate1', List.length_cons]
    have := ih _ _ _ (d + 1) _ (.snoc hΓ₂ hAt'') hς' W.pushLam
      (Erases.wkLam hord hty (.snoc hΓ₂ hAt'') hcl Ea) fun hs => by
        obtain ⟨hΓ₁, hn, hd₀, hfd, hhb⟩ := hi hs
        exact ⟨.snoc hΓ₁ ⟨u, hAu⟩, hn, hd₀.wk,
          by simp [MLCtx.pushLam, MLCtx.findB, MLCtx.findB_map_wk, hfd], hhb.wk hΓ₁⟩
    rw [show d + 1 + _ = d + (_ + 1) from Nat.add_right_comm _ _ _] at this
    exact .lam hA'' hAt'' this
  case intro =>
    intro _ _ _ e _ _ _ _ _ _ _ he hty' _ ih n₂ Γ₂ Δ₂ d ς hΓ₂ hς W Ea hi
    obtain ⟨e'', he'', -, hd⟩ := TrM.instA hE hord hΓ₂ hς W he hty'
    obtain ⟨_, hfa⟩ := hty'.regular
    obtain ⟨_, _, hA', -, -⟩ := hfa.forallE_ty_inv
    have hT := hd.right
    simp only [Expr.subst] at hT
    have hA's := IsType.substitution ⟨_, hA'⟩ hς
    refine .intro he'' hT ?_
    have := ih _ _ _ (d + 1) _ (.snoc hΓ₂ hA's) (SubstWF.lift ⟨_, hA'⟩ hς) W.pushLam
      (Erases.wkLam hord hty (.snoc hΓ₂ hA's) hcl Ea) fun hs => by
        obtain ⟨hΓ₁, hn, hd₀, hfd, hhb⟩ := hi hs
        refine ⟨.snoc hΓ₁ ⟨_, hA'⟩, ⟨fun hfn => ?_, ?_, trivial⟩, hd₀.wk,
          by simp [MLCtx.pushLam, MLCtx.findB, MLCtx.findB_map_wk, hfd], hhb.wk hΓ₁⟩
        · rw [liftLooseBVars'_getAppFn] at hfn
          have hfn' : e.getAppFn = .bvar d := by
            generalize e.getAppFn = g at hfn
            cases g <;> simp only [Lean.Expr.liftLooseBVars', Lean.Expr.bvar.injEq,
              reduceCtorEq] at hfn
            split_ifs at hfn <;> (congr 1; omega)
          cases e with
          | bvar i =>
            simp only [Lean.Expr.getAppFn, Lean.Expr.bvar.injEq] at hfn'
            subst hfn'
            have := PreTr.bvar_inv (PreTr.ofTrM he)
            rw [hfd] at this
            cases this
            exact HB.false hE hΓ₁ hhb hty'
          | app f x => exact hn.1 hfn'
          | _ => simp [Lean.Expr.getAppFn] at hfn'
        · exact NoHead.lift (c := 0) (k := 1) (Nat.zero_le d) hn
    simp only [Lean.Expr.instantiate1', show 0 < d + 1 by omega, ↓reduceIte,
      List.length_cons] at this ⊢
    rw [lift_inst_below a e (s := 0) (k := 1) (Nat.zero_le d),
      show d + 1 + _ = d + (_ + 1) from Nat.add_right_comm _ _ _] at this
    exact this

end

/-! ## Constructor values -/

section
open Metalean InstPre
variable {ζ : Sigs} {E : Env ζ} {B : Binds ζ} {lps : List Name}

theorem atomSpine_head {σ : EvalEnv} {e : Lean.Expr} (h : AtomSpine σ e) :
    ∃ c us, e.getAppFn = .const c us ∧ σ.isAtom c = true := by
  induction h with
  | const hc => exact ⟨_, _, rfl, hc⟩
  | app _ ih => simpa [Lean.Expr.getAppFn] using ih

theorem propProj_head {σ : EvalEnv} {e : Lean.Expr} (h : PropProj σ e) :
    ∃ S i e₀, e.getAppFn = .proj S i e₀ := by
  induction h with
  | proj => exact ⟨_, _, _, rfl⟩
  | projProj => exact ⟨_, _, _, rfl⟩
  | app _ ih => simpa [Lean.Expr.getAppFn] using ih

/-- A source value whose head is a constructor, a recognized `casesOn` or an erased quotient
constant is a saturated constructor spine or a `Quot.mk` spine. -/
theorem srcValue_special {σ : EvalEnv} {a : Lean.Expr} (hval : SrcValue σ a)
    (hs : SpecialSpine σ a) :
    (∃ C us args cv, a = mkAppN (.const C us) (args : List Lean.Expr).toArray ∧
      findDecl σ.decls C = some (.ctorInfo cv) ∧ args.length = cv.numParams + cv.numFields) ∨
    ∃ C us α r x qv, a = mkAppN (.const C us) [α, r, x].toArray ∧
      findDecl σ.decls C = some (.quotInfo qv) ∧ qv.kind = .ctor := by
  obtain ⟨c, us, hc, hsp⟩ := hs
  cases hval with
  | ctor hC hlen => exact .inl ⟨_, _, _, _, rfl, hC, hlen⟩
  | quotMk hC hk _ => exact .inr ⟨_, _, _, _, _, _, rfl, hC, hk⟩
  | spine hsp' =>
    obtain ⟨c', us', hc', hat⟩ := atomSpine_head hsp'
    rw [hc] at hc'
    cases hc'
    exfalso
    unfold EvalEnv.isAtom at hat
    rcases hsp with ⟨cv, hcv⟩ | hco | ⟨qv, hqv, hqa⟩ | ⟨rv, hrv⟩
    · simp [hcv, OwnRules] at hat
    · split at hat
      · simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hat
        rw [hat.1.1.2] at hco
        cases hco
      · cases hat
    · cases hk : qv.kind <;> simp [hqv, OwnRules, hk, quotEvalArity] at hat hqa
    · simp [hrv, OwnRules] at hat
  | propProj hp =>
    obtain ⟨S, i, e₀, he⟩ := propProj_head hp
    rw [he] at hc
    cases hc
  | lam | sort | forallE | lit => simp [Lean.Expr.getAppFn] at hc

/-- The translation of a saturated constructor spine of the program is a constructor node. -/
theorem ctorNode_of_TrM {P : List ConstantInfo} {σ : EvalEnv} (henv : ProgEnv P ζ E B)
    (hsub : SubEnv σ.decls P) {n : Nat} {Γ : Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    {C : Name} {us : List Level} {args : List Lean.Expr} {cv : ConstructorVal}
    {a₀ : Expr ζ lps.length n} (hC : findDecl σ.decls C = some (.ctorInfo cv))
    (hlen : args.length = cv.numParams + cv.numFields)
    (h : TrM E B lps Γ Δ (mkAppN (.const C us) args.toArray) a₀) :
    ∃ (ι : IndSig) (η : Head ζ (.inductive ι)) (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
      (ls : Fin ι.nlevels → Level lps.length) (ps : Fin ι.nparams → Expr ζ lps.length n)
      (fds : Fin (ι.ctors s c).nfields → Expr ζ lps.length n)
      (recFds : Fin (ι.ctors s c).nrecFields → Expr ζ lps.length n),
      a₀ = .ctor η s c ls ps fds recFds := by
  obtain ⟨ι, η, s, k, o, hB, -, hnp, hnf, -, -⟩ :=
    ProgEnv.lookup_ctor henv (Extend.findDecl_sub hsub hC)
  obtain ⟨bs', hlen', -, hsat⟩ := PreTr.special_inv hB rfl (PreTr.ofTrM h)
  cases hsat with
  | ctorSat ps fs rest fds recFds _ hfs _ _ =>
    simp only [List.length_append, List.length_ofFn] at hlen'
    have hr : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hr
    exact ⟨_, _, _, _, _, _, _, _, rfl⟩
  | ctorEta _ hlt _ => omega

/-- A constructor or `Quot.mk` node. -/
def Node {n : Nat} (x : Expr ζ lps.length n) : Prop :=
  (∃ (ι : IndSig) (η : Head ζ (.inductive ι)) (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (ls : Fin ι.nlevels → Level lps.length) (ps : Fin ι.nparams → Expr ζ lps.length n)
    (fds : Fin (ι.ctors s c).nfields → Expr ζ lps.length n)
    (recFds : Fin (ι.ctors s c).nrecFields → Expr ζ lps.length n),
    x = .ctor η s c ls ps fds recFds) ∨
  ∃ (θ : Head ζ .quot) (l : Level lps.length) (α r a : Expr ζ lps.length n), x = .quotMk θ l α r a

/-- The translation of a source value with a special head is a constructor or `Quot.mk` node. -/
theorem node_of_value {P : List ConstantInfo} {σ : EvalEnv} (henv : ProgEnv P ζ E B)
    (hsub : SubEnv σ.decls P) {n : Nat} {Γ : Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    {a : Lean.Expr} {a₀ : Expr ζ lps.length n} (hval : SrcValue σ a) (hs : SpecialSpine σ a)
    (h : TrM E B lps Γ Δ a a₀) : Node a₀ := by
  rcases srcValue_special hval hs with ⟨C, us, args, cv, rfl, hC, hlen⟩ |
    ⟨C, us, α, r, x, qv, rfl, hC, hk⟩
  · obtain ⟨ι, η, s, c, ls, ps, fds, recFds, rfl⟩ := ctorNode_of_TrM henv hsub hC hlen h
    exact .inl ⟨_, _, _, _, _, _, _, _, rfl⟩
  · obtain ⟨η, hB⟩ := henv.lookup_quot (Extend.findDecl_sub hsub hC)
    rw [hk] at hB
    simp only [quotKindOf] at hB
    obtain ⟨bs', hlen', -, hsat⟩ := PreTr.special_inv hB rfl (PreTr.ofTrM h)
    cases hsat with
    | quotEta _ hlt => simp [quotArity] at hlen' hlt; omega
    | @quotMk _ α₀ r₀ x₀ rest _ u hu =>
      obtain rfl : rest = [] := by simpa using hlen'
      exact .inr ⟨_, _, _, _, _, rfl⟩

/-- A node is not a function. -/
theorem HB.of_node {n : Nat} {R : Ctx ζ lps.length 0 n} {x : Expr ζ lps.length n}
    (h : Node x) : HB E R x := by
  rcases h with ⟨ι, η, s, c, ls, ps, fds, recFds, rfl⟩ | ⟨θ, l, α, r, a, rfl⟩
  · exact .inr (.inl ⟨_, _, _, _, _, _, _, _, rfl⟩)
  · exact .inr (.inr (.inr ⟨_, _, _, _, _, rfl⟩))

/-- A term definitionally equal to a node, at the type of the node, is not a function. -/
theorem HB.of_defeq_node {n : Nat} {R : Ctx ζ lps.length 0 n} {x y T : Expr ζ lps.length n}
    (hd : E[R] ⊢ y ≡ x : T) (h : Node x) : HB E R y := by
  rcases h with ⟨ι, η, s, c, ls, ps, fds, recFds, rfl⟩ | ⟨θ, l, α, r, a, rfl⟩
  · obtain ⟨_, _, _, _, _, _, hT⟩ := hd.right.ctor_inv
    exact .inl ⟨_, _, _, _, _, _, _, hd.left, hT.2⟩
  · exact .inr (.inr (.inl ⟨_, _, _, _, _, hd.left, hd.right.quotMk_inv⟩))

/-- The bound variable of a binder whose type is the type of a constructor node is not a
function. -/
theorem HB.var_of_ctor {n : Nat} {Γ : Ctx ζ lps.length 0 n} {A : Expr ζ lps.length n}
    {ι : IndSig} {η : Head ζ (.inductive ι)} {s : Fin ι.nsorts} {c : Fin (ι.nctors s)}
    {ls : Fin ι.nlevels → Level lps.length} {ps : Fin ι.nparams → Expr ζ lps.length n}
    {fds : Fin (ι.ctors s c).nfields → Expr ζ lps.length n}
    {recFds : Fin (ι.ctors s c).nrecFields → Expr ζ lps.length n} (hΓ : E[Γ] ⊢ ok)
    (hΓA : E[Γ.snoc A] ⊢ ok) (hA : E[Γ] ⊢ .ctor η s c ls ps fds recFds : A) :
    HB E (Γ.snoc A) (.var (Fin.last n)) := by
  obtain ⟨_, _, _, _, _, _, hT⟩ := hA.ctor_inv
  have h2 := hT.2.substitution (SubstWF.wk A hΓ)
  rw [Expr.subst_wk] at h2
  simp only [Expr.subst] at h2
  exact .inl ⟨_, _, _, _, _, _, _, hΓA.varLast, h2⟩

/-- The bound variable of a binder whose type is the type of a node is not a function. -/
theorem HB.var_of_node {n : Nat} {Γ : Ctx ζ lps.length 0 n} {A x : Expr ζ lps.length n}
    (hΓ : E[Γ] ⊢ ok) (hΓA : E[Γ.snoc A] ⊢ ok) (hA : E[Γ] ⊢ x : A) (h : Node x) :
    HB E (Γ.snoc A) (.var (Fin.last n)) := by
  rcases h with ⟨ι, η, s, c, ls, ps, fds, recFds, rfl⟩ | ⟨θ, l, α, r, a, rfl⟩
  · exact HB.var_of_ctor hΓ hΓA hA
  · have h2 := hA.quotMk_inv.substitution (SubstWF.wk A hΓ)
    rw [Expr.subst_wk] at h2
    simp only [Expr.subst] at h2
    exact .inr (.inr (.inl ⟨_, _, _, _, _, hΓA.varLast, h2⟩))

end

end RelInst

section
open Metalean InstPre RelInst
variable {ζ : Sigs} {E : Env ζ} {B : Binds ζ} {lps : List Name}

/-- The premises of the generalised substitution at depth `0`, for a λ-bound variable. -/
theorem RelInst.inst_setup {P : List ConstantInfo} {σ : EvalEnv} {n : Nat}
    {Γ : Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n} {a b : Lean.Expr} {a' : LBTerm}
    {b₀ : Expr ζ lps.length (n + 1)} {a₀ : Expr ζ lps.length n}
    (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hΓ : E[Γ] ⊢ ok) (hsub : SubEnv σ.decls P)
    {A : Expr ζ lps.length n} {T : Expr ζ lps.length (n + 1)} (hval : SrcValue σ a)
    (htb : TrM E B lps (Γ.snoc A) (Δ.pushLam none) b b₀) (hbT : E[Γ.snoc A] ⊢ b₀ : T)
    (ha : Erases E B lps σ Γ Δ a a') (hta : TrM E B lps Γ Δ a a₀) (hA : E[Γ] ⊢ a₀ : A) :
    E[Γ] ⊢ Subst.id.extend a₀ ⊣ Γ.snoc A ∧
      MLCtx.InstA E B lps a 0 (Subst.id.extend a₀) (Δ.pushLam none) Δ ∧
      Erases E B lps σ Γ Δ (a.liftLooseBVars' 0 0) a' ∧
      HeadInv σ E a (Γ.snoc A) (Δ.pushLam none) 0 b := by
  have hord := henv.metaOrderOK
  obtain ⟨u, hAu⟩ := hA.regular
  have hΓA : E[Γ.snoc A] ⊢ ok := .snoc hΓ ⟨u, hAu⟩
  have W : MLCtx.InstA E B lps a 0 (Subst.id.extend a₀) (Δ.pushLam none) Δ := by
    constructor
    · intro i t ht
      cases i with
      | zero =>
        simp only [MLCtx.pushLam, MLCtx.findB, MLDecl.denote, Option.some.injEq] at ht
        subst ht
        refine ⟨by omega, fun _ => ⟨a₀, ?_, ?_⟩, by omega⟩
        · rw [liftLooseBVars'_zero]; exact PreTr.ofTrM hta
        · simp only [Expr.subst, Subst.extend_last]; exact fun {_ _} => .refl
      | succ i =>
        simp only [MLCtx.pushLam, MLCtx.findB, MLCtx.findB_map_wk, Option.map_eq_some_iff] at ht
        obtain ⟨u, hu, rfl⟩ := ht
        refine ⟨by omega, by omega, fun _ => ⟨u, by simpa using hu, ?_⟩⟩
        rw [Expr.wk_subst_extend, Expr.subst_id]
        exact fun {_ _} => .refl
    · intro x t ht
      simp only [MLCtx.pushLam, MLCtx.findF, MLCtx.findF_map_wk, Option.map_eq_some_iff] at ht
      obtain ⟨u, hu, rfl⟩ := ht
      refine ⟨u, hu, ?_⟩
      rw [Expr.wk_subst_extend, Expr.subst_id]
      exact fun {_ _} => .refl
  have hς : E[Γ] ⊢ Subst.id.extend a₀ ⊣ Γ.snoc A :=
    SubstWF.extend (by simpa using hA) (SubstWF.id hΓ)
  have Ea : Erases E B lps σ Γ Δ (a.liftLooseBVars' 0 0) a' := by
    rw [liftLooseBVars'_zero]; exact ha
  have hfd : (Δ.pushLam none).findB 0 = some (.var (Fin.last n)) := by
    simp [MLCtx.pushLam, MLCtx.findB, MLDecl.denote]
  refine ⟨hς, W, Ea, fun hs => ?_⟩
  have hhb := HB.var_of_node hΓ hΓA hA (node_of_value henv hsub hval hs hta)
  refine ⟨hΓA, ?_, _, hfd, hhb⟩
  exact PreTr.noHead hE hord (PreTr.ofTrM htb) (ρ := Ren.id) hfd hΓA
    (by rw [Expr.rename_id]; exact hhb) ⟨_, by rw [Expr.rename_id]; exact hbT⟩

/-- Substitution of a typed source value for the innermost bound variable of a typed body: the
erasure of the instantiated body is the closed substitution of the value's erasure into the
body's erasure. Reference: `erases_subst0` (`MR E/ESubstitution.v:612`), with `wf_ext`,
`wf_local` and the typings of the body and the value as `henv`, `hsub`, `hE`, `hΓ` and the
typed translations. -/
theorem Erases.inst {P : List ConstantInfo} {σ : EvalEnv} {n : Nat}
    {Γ : Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n} {a b : Lean.Expr} {b' a' : LBTerm}
    {b₀ : Expr ζ lps.length (n + 1)} {a₀ : Expr ζ lps.length n}
    (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hΓ : E[Γ] ⊢ ok) (hsub : SubEnv σ.decls P)
    {A : Expr ζ lps.length n} {T : Expr ζ lps.length (n + 1)} (hval : SrcValue σ a)
    (hb : Erases E B lps σ (Γ.snoc A) (Δ.pushLam none) b b')
    (htb : TrM E B lps (Γ.snoc A) (Δ.pushLam none) b b₀) (hbT : E[Γ.snoc A] ⊢ b₀ : T)
    (ha : Erases E B lps σ Γ Δ a a')
    (hta : TrM E B lps Γ Δ a a₀) (hA : E[Γ] ⊢ a₀ : A) (hcl : closedn 0 a' = true) :
    Erases E B lps σ Γ Δ (b.instantiate1' a) (csubst a' 0 b') := by
  have hty : ∀ c ci, findDecl σ.decls c = some ci → AbsFV.LBV 0 ci.type :=
    fun c ci h => (AbsFV.closed_types henv hsub c ci h).1
  obtain ⟨hς, W, Ea, hi⟩ := RelInst.inst_setup henv hE hΓ hsub hval htb hbT ha hta hA
  exact (Erases.instG hE henv.metaOrderOK hty hcl).1 _ _ _ _ _ hb _ _ _ 0 _ hΓ hς W Ea hi

/-- Substitution of a typed source value into a `casesOn` alternative erased under its field
binders: the branch's body is substituted below the field binders (the step of `iotaRed`,
`MR E/EGlobalEnv.v:281 iota_red`, `substl`). Reference: `erases_subst0` (`MR E/ESubstitution.v:612`)
on the branches of `MR E/Extract.v:111 erases_tCase`. -/
theorem ErasesAlt.inst {P : List ConstantInfo} {σ : EvalEnv} {n k : Nat}
    {Γ : Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n} {a b : Lean.Expr} {a' t : LBTerm}
    {ns : List BinderName} {b₀ : Expr ζ lps.length (n + 1)} {a₀ : Expr ζ lps.length n}
    (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hΓ : E[Γ] ⊢ ok) (hsub : SubEnv σ.decls P)
    {A : Expr ζ lps.length n} {T : Expr ζ lps.length (n + 1)} (hval : SrcValue σ a)
    (hb : ErasesAlt E B lps σ (Γ.snoc A) (Δ.pushLam none) k b (ns, t))
    (htb : TrM E B lps (Γ.snoc A) (Δ.pushLam none) b b₀) (hbT : E[Γ.snoc A] ⊢ b₀ : T)
    (ha : Erases E B lps σ Γ Δ a a')
    (hta : TrM E B lps Γ Δ a a₀) (hA : E[Γ] ⊢ a₀ : A) (hcl : closedn 0 a' = true) :
    ErasesAlt E B lps σ Γ Δ k (b.instantiate1' a) (ns, csubst a' ns.length t) := by
  have hty : ∀ c ci, findDecl σ.decls c = some ci → AbsFV.LBV 0 ci.type :=
    fun c ci h => (AbsFV.closed_types henv hsub c ci h).1
  obtain ⟨hς, W, Ea, hi⟩ := RelInst.inst_setup henv hE hΓ hsub hval htb hbT ha hta hA
  have := (Erases.instG hE henv.metaOrderOK hty hcl).2 _ _ _ _ _ _ hb _ _ _ 0 _ hΓ hς W Ea hi
  simpa using this

end

end EraseProof
