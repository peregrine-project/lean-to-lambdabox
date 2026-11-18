import EraseProof.Spec

/-!
# Marks under substitution

The marks are metadata (`markErase`, `markEta`, `markReduced`), which `instantiate1'`,
`liftLooseBVars'` and `Pure.instLevels` keep in place (their `mdata` cases), so a substituted
marking is marked at the same positions. `unmark` commutes with lifting (`unmark_liftLooseBVars'`)
and with universe instantiation (`unmark_instLevels`), and with instantiation when every `eta` mark
sits on a λ (`EtaLams`, `unmark_instantiate1'`): an `eta` mark on the substituted variable itself
would be contracted only after the substitution.
-/

open Lean Erasure

namespace EraseProof

namespace Marks

/-! ## Loose bound variables -/

/-- `==` on distinct numbers. Reference: none. -/
theorem nat_beq_false {i k : Nat} (h : i ≠ k) : (i == k) = false := by simpa using h

/-- A lifted term has no loose index in the lifted range. Reference: none. -/
theorem bvarOccurs_lift_out : ∀ (e : Expr) {s n k : Nat}, s ≤ k → k < s + n →
    bvarOccurs k (e.liftLooseBVars' s n) = false
  | .bvar i, s, n, k, h₁, h₂ => by
    by_cases h : i < s
    · simp only [Expr.liftLooseBVars', h, ↓reduceIte, bvarOccurs, nat_beq_false (show i ≠ k by omega)]
    · simp only [Expr.liftLooseBVars', h, ↓reduceIte, bvarOccurs, nat_beq_false (show i + n ≠ k by omega)]
  | .app f a, _, _, _, h₁, h₂ => by
    simp [Expr.liftLooseBVars', bvarOccurs, bvarOccurs_lift_out f h₁ h₂,
      bvarOccurs_lift_out a h₁ h₂]
  | .lam _ t b _, s, n, k, h₁, h₂ | .forallE _ t b _, s, n, k, h₁, h₂ => by
    simp [Expr.liftLooseBVars', bvarOccurs, bvarOccurs_lift_out t h₁ h₂,
      bvarOccurs_lift_out b (s := s + 1) (n := n) (k := k + 1) (by omega) (by omega)]
  | .letE _ t v b _, s, n, k, h₁, h₂ => by
    simp [Expr.liftLooseBVars', bvarOccurs, bvarOccurs_lift_out t h₁ h₂,
      bvarOccurs_lift_out v h₁ h₂,
      bvarOccurs_lift_out b (s := s + 1) (n := n) (k := k + 1) (by omega) (by omega)]
  | .mdata _ e, _, _, _, h₁, h₂ | .proj _ _ e, _, _, _, h₁, h₂ => by
    simp [Expr.liftLooseBVars', bvarOccurs, bvarOccurs_lift_out e h₁ h₂]
  | .sort _, _, _, _, _, _ | .const .., _, _, _, _, _ | .lit _, _, _, _, _, _
  | .mvar _, _, _, _, _, _ | .fvar _, _, _, _, _, _ => rfl

/-- Lifting from above `k` does not change whether `k` occurs. Reference: none. -/
theorem bvarOccurs_lift_below : ∀ (e : Expr) {s n k : Nat}, k < s →
    bvarOccurs k (e.liftLooseBVars' s n) = bvarOccurs k e
  | .bvar i, s, n, k, h => by
    by_cases h₁ : i < s
    · simp only [Expr.liftLooseBVars', h₁, ↓reduceIte]
    · simp only [Expr.liftLooseBVars', h₁, ↓reduceIte, bvarOccurs, nat_beq_false (show i + n ≠ k by omega),
        nat_beq_false (show i ≠ k by omega)]
  | .app f a, _, _, _, h => by
    simp [Expr.liftLooseBVars', bvarOccurs, bvarOccurs_lift_below f h, bvarOccurs_lift_below a h]
  | .lam _ t b _, s, n, k, h | .forallE _ t b _, s, n, k, h => by
    simp [Expr.liftLooseBVars', bvarOccurs, bvarOccurs_lift_below t h,
      bvarOccurs_lift_below b (s := s + 1) (n := n) (k := k + 1) (by omega)]
  | .letE _ t v b _, s, n, k, h => by
    simp [Expr.liftLooseBVars', bvarOccurs, bvarOccurs_lift_below t h, bvarOccurs_lift_below v h,
      bvarOccurs_lift_below b (s := s + 1) (n := n) (k := k + 1) (by omega)]
  | .mdata _ e, _, _, _, h | .proj _ _ e, _, _, _, h => by
    simp [Expr.liftLooseBVars', bvarOccurs, bvarOccurs_lift_below e h]
  | .sort _, _, _, _, _ | .const .., _, _, _, _ | .lit _, _, _, _, _
  | .mvar _, _, _, _, _ | .fvar _, _, _, _, _ => rfl

/-- Instantiating above `k` does not change whether `k` occurs. Reference: none. -/
theorem bvarOccurs_inst : ∀ (e : Expr) (a : Expr) {j k : Nat}, k < j →
    bvarOccurs k (e.instantiate1' a j) = bvarOccurs k e
  | .bvar i, a, j, k, h => by
    by_cases h₁ : i < j
    · simp only [Expr.instantiate1', h₁, ↓reduceIte]
    · by_cases h₂ : i = j
      · subst h₂
        simp only [Expr.instantiate1', Nat.lt_irrefl, ↓reduceIte,
          bvarOccurs_lift_out a (s := 0) (n := i) (k := k) (Nat.zero_le k) (by omega), bvarOccurs,
          nat_beq_false (show i ≠ k by omega)]
      · simp only [Expr.instantiate1', h₁, h₂, ↓reduceIte, bvarOccurs, nat_beq_false (show i - 1 ≠ k by omega),
          nat_beq_false (show i ≠ k by omega)]
  | .app f b, a, _, _, h => by
    simp [Expr.instantiate1', bvarOccurs, bvarOccurs_inst f a h, bvarOccurs_inst b a h]
  | .lam _ t b _, a, j, k, h | .forallE _ t b _, a, j, k, h => by
    simp [Expr.instantiate1', bvarOccurs, bvarOccurs_inst t a h,
      bvarOccurs_inst b a (j := j + 1) (k := k + 1) (by omega)]
  | .letE _ t v b _, a, j, k, h => by
    simp [Expr.instantiate1', bvarOccurs, bvarOccurs_inst t a h, bvarOccurs_inst v a h,
      bvarOccurs_inst b a (j := j + 1) (k := k + 1) (by omega)]
  | .mdata _ e, a, _, _, h | .proj _ _ e, a, _, _, h => by
    simp [Expr.instantiate1', bvarOccurs, bvarOccurs_inst e a h]
  | .sort _, _, _, _, _ | .const .., _, _, _, _ | .lit _, _, _, _, _
  | .mvar _, _, _, _, _ | .fvar _, _, _, _, _ => rfl

/-- Instantiating inside a lifted range removes one lift. Port of
`ML-V Relation/Inst.lean:144 RelInst.inst_lift_cancel`. -/
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
  | .sort _, _, _, _, _, _ | .const .., _, _, _, _, _ | .lit _, _, _, _, _, _
  | .mvar _, _, _, _, _, _ | .fvar _, _, _, _, _, _ => rfl

/-- Lowering past an absent index `k` (`instantiate1' (.bvar 0) k`, the contraction of
`etaContract`) commutes with instantiating above it. Reference: none. -/
theorem lower_inst (a : Expr) : ∀ (f : Expr) {j k : Nat}, k < j → bvarOccurs k f = false →
    (f.instantiate1' a j).instantiate1' (.bvar 0) k =
      (f.instantiate1' (.bvar 0) k).instantiate1' a (j - 1)
  | .bvar i, j, k, h, hk => by
    simp only [bvarOccurs, beq_eq_false_iff_ne] at hk
    by_cases h₁ : i < k
    · simp [Expr.instantiate1', h₁, show i < j by omega, show i < j - 1 by omega]
    · by_cases h₂ : i < j
      · simp [Expr.instantiate1', h₁, h₂, hk, show i - 1 < j - 1 by omega]
      · by_cases h₃ : i = j
        · subst h₃
          have := inst_lift_cancel (.bvar 0) a (c := 0) (j := k) (n := i - 1) (Nat.zero_le k)
            (by omega)
          rw [show i - 1 + 1 = i by omega] at this
          simpa [Expr.instantiate1', h₁, hk] using this
        · simp [Expr.instantiate1', h₁, h₂, h₃, hk, show ¬ i - 1 < k by omega,
            show ¬ i - 1 = k by omega, show ¬ i - 1 < j - 1 by omega,
            show ¬ i - 1 = j - 1 by omega]
  | .app f b, j, k, h, hk => by
    simp only [bvarOccurs, Bool.or_eq_false_iff] at hk
    simp [Expr.instantiate1', lower_inst a f h hk.1, lower_inst a b h hk.2]
  | .lam _ t b _, j, k, h, hk | .forallE _ t b _, j, k, h, hk => by
    simp only [bvarOccurs, Bool.or_eq_false_iff] at hk
    have := lower_inst a b (j := j + 1) (k := k + 1) (by omega) hk.2
    rw [show j + 1 - 1 = j - 1 + 1 by omega] at this
    simp [Expr.instantiate1', lower_inst a t h hk.1, this]
  | .letE _ t v b _, j, k, h, hk => by
    simp only [bvarOccurs, Bool.or_eq_false_iff] at hk
    have := lower_inst a b (j := j + 1) (k := k + 1) (by omega) hk.2
    rw [show j + 1 - 1 = j - 1 + 1 by omega] at this
    simp [Expr.instantiate1', lower_inst a t h hk.1.1, lower_inst a v h hk.1.2, this]
  | .mdata _ e, j, k, h, hk | .proj _ _ e, j, k, h, hk => by
    simp only [bvarOccurs] at hk
    simp [Expr.instantiate1', lower_inst a e h hk]
  | .sort _, _, _, _, _ | .const .., _, _, _, _ | .lit _, _, _, _, _
  | .mvar _, _, _, _, _ | .fvar _, _, _, _, _ => rfl

/-- Lowering past an absent index `k` commutes with lifting above it. Reference: none. -/
theorem lower_lift : ∀ (f : Expr) {s n k : Nat}, k ≤ s → bvarOccurs k f = false →
    (f.liftLooseBVars' (s + 1) n).instantiate1' (.bvar 0) k =
      (f.instantiate1' (.bvar 0) k).liftLooseBVars' s n
  | .bvar i, s, n, k, h, hk => by
    simp only [bvarOccurs, beq_eq_false_iff_ne] at hk
    by_cases h₁ : i < k
    · simp [Expr.instantiate1', Expr.liftLooseBVars', h₁, show i < s + 1 by omega,
        show i < s by omega]
    · by_cases h₂ : i < s + 1
      · simp [Expr.instantiate1', Expr.liftLooseBVars', h₁, h₂, hk, show i - 1 < s by omega]
      · simp [Expr.instantiate1', Expr.liftLooseBVars', h₁, h₂, hk, show ¬ i + n < k by omega,
          show ¬ i + n = k by omega, show ¬ i - 1 < s by omega]
        omega
  | .app f b, _, _, _, h, hk => by
    simp only [bvarOccurs, Bool.or_eq_false_iff] at hk
    simp [Expr.instantiate1', Expr.liftLooseBVars', lower_lift f h hk.1, lower_lift b h hk.2]
  | .lam _ t b _, s, n, k, h, hk | .forallE _ t b _, s, n, k, h, hk => by
    simp only [bvarOccurs, Bool.or_eq_false_iff] at hk
    simp [Expr.instantiate1', Expr.liftLooseBVars', lower_lift t h hk.1,
      lower_lift b (s := s + 1) (n := n) (k := k + 1) (by omega) hk.2]
  | .letE _ t v b _, s, n, k, h, hk => by
    simp only [bvarOccurs, Bool.or_eq_false_iff] at hk
    simp [Expr.instantiate1', Expr.liftLooseBVars', lower_lift t h hk.1.1, lower_lift v h hk.1.2,
      lower_lift b (s := s + 1) (n := n) (k := k + 1) (by omega) hk.2]
  | .mdata _ e, _, _, _, h, hk | .proj _ _ e, _, _, _, h, hk => by
    simp only [bvarOccurs] at hk
    simp [Expr.instantiate1', Expr.liftLooseBVars', lower_lift e h hk]
  | .sort _, _, _, _, _, _ | .const .., _, _, _, _, _ | .lit _, _, _, _, _, _
  | .mvar _, _, _, _, _, _ | .fvar _, _, _, _, _, _ => rfl

/-! ## Universe instantiation -/

section
variable (ps : List Name) (us : List Level)

/-- Port of `ML-V Relation/Levels.lean:295 RelLevels.instLevels_lift`. -/
theorem instLevels_lift : ∀ (e : Expr) (s d : Nat),
    Pure.instLevels ps us (e.liftLooseBVars' s d) = (Pure.instLevels ps us e).liftLooseBVars' s d
  | .bvar _, _, _ => rfl
  | .app f a, s, d => by
    simp only [Expr.liftLooseBVars', Pure.instLevels, instLevels_lift f, instLevels_lift a]
  | .lam _ t b _, s, d | .forallE _ t b _, s, d => by
    simp only [Expr.liftLooseBVars', Pure.instLevels, instLevels_lift t, instLevels_lift b]
  | .letE _ t v b _, s, d => by
    simp only [Expr.liftLooseBVars', Pure.instLevels, instLevels_lift t, instLevels_lift v,
      instLevels_lift b]
  | .mdata _ e, s, d | .proj _ _ e, s, d => by
    simp only [Expr.liftLooseBVars', Pure.instLevels, instLevels_lift e]
  | .fvar _, _, _ | .mvar _, _, _ | .sort _, _, _ | .const .., _, _ | .lit _, _, _ => rfl

/-- Port of `ML-V Relation/Levels.lean:309 RelLevels.instLevels_instantiate1'`. -/
theorem instLevels_instantiate1' (a : Expr) : ∀ (e : Expr) (d : Nat),
    Pure.instLevels ps us (e.instantiate1' a d) =
      (Pure.instLevels ps us e).instantiate1' (Pure.instLevels ps us a) d
  | .bvar i, d => by
    show Pure.instLevels ps us (Expr.instantiate1' (.bvar i) a d) =
      Expr.instantiate1' (.bvar i) (Pure.instLevels ps us a) d
    simp only [Expr.instantiate1']
    split
    · rfl
    · split
      · exact instLevels_lift ps us a 0 d
      · rfl
  | .app f b, d => by
    simp only [Expr.instantiate1', Pure.instLevels, instLevels_instantiate1' a f,
      instLevels_instantiate1' a b]
  | .lam _ t b _, d | .forallE _ t b _, d => by
    simp only [Expr.instantiate1', Pure.instLevels, instLevels_instantiate1' a t,
      instLevels_instantiate1' a b]
  | .letE _ t v b _, d => by
    simp only [Expr.instantiate1', Pure.instLevels, instLevels_instantiate1' a t,
      instLevels_instantiate1' a v, instLevels_instantiate1' a b]
  | .mdata _ e, d | .proj _ _ e, d => by
    simp only [Expr.instantiate1', Pure.instLevels, instLevels_instantiate1' a e]
  | .fvar _, _ | .mvar _, _ | .sort _, _ | .const .., _ | .lit _, _ => rfl

/-- Universe instantiation does not change the loose indices. Reference: none. -/
theorem bvarOccurs_instLevels : ∀ (e : Expr) (k : Nat),
    bvarOccurs k (Pure.instLevels ps us e) = bvarOccurs k e
  | .bvar _, _ => rfl
  | .app f a, k => by simp [Pure.instLevels, bvarOccurs, bvarOccurs_instLevels f, bvarOccurs_instLevels a]
  | .lam _ t b _, k | .forallE _ t b _, k => by
    simp [Pure.instLevels, bvarOccurs, bvarOccurs_instLevels t, bvarOccurs_instLevels b]
  | .letE _ t v b _, k => by
    simp [Pure.instLevels, bvarOccurs, bvarOccurs_instLevels t, bvarOccurs_instLevels v,
      bvarOccurs_instLevels b]
  | .mdata _ e, k | .proj _ _ e, k => by simp [Pure.instLevels, bvarOccurs, bvarOccurs_instLevels e]
  | .fvar _, _ | .mvar _, _ | .sort _, _ | .const .., _ | .lit _, _ => rfl

end

/-! ## η-contraction -/

/-- The shape `etaContract` tests: `λ x. f x`. Reference: none (DV-23). -/
def EtaShape (e : Expr) : Prop := ∃ n t f bi, e = .lam n t (.app f (.bvar 0)) bi

/-- Off its shape, `etaContract` is the identity. Reference: none. -/
theorem etaContract_of_not {e : Expr} (h : ¬ EtaShape e) : etaContract e = e := by
  unfold etaContract
  split
  · exact absurd ⟨_, _, _, _, rfl⟩ h
  · rfl

/-- Lifting creates no η-shape. Reference: none. -/
theorem etaShape_of_lift {e : Expr} {s n : Nat} (h : EtaShape (e.liftLooseBVars' s n)) :
    EtaShape e := by
  obtain ⟨m, t, f, bi, he⟩ := h
  cases e <;> simp only [Expr.liftLooseBVars', reduceCtorEq, Expr.lam.injEq] at he
  rename_i b _
  obtain ⟨-, -, hb, -⟩ := he
  cases b <;> simp only [Expr.liftLooseBVars', reduceCtorEq, Expr.app.injEq] at hb
  rename_i c
  obtain ⟨-, hc⟩ := hb
  cases c <;> simp only [Expr.liftLooseBVars', reduceCtorEq, Expr.bvar.injEq] at hc
  rename_i i
  have : i = 0 := by split at hc <;> omega
  subst this; exact ⟨_, _, _, _, rfl⟩

/-- `etaContract` commutes with lifting. Reference: none. -/
theorem etaContract_lift (e : Expr) (s n : Nat) :
    etaContract (e.liftLooseBVars' s n) = (etaContract e).liftLooseBVars' s n := by
  by_cases h : EtaShape e
  · obtain ⟨m, t, f, bi, rfl⟩ := h
    rw [show (Expr.lam m t (.app f (.bvar 0)) bi).liftLooseBVars' s n =
      .lam m (t.liftLooseBVars' s n) (.app (f.liftLooseBVars' (s + 1) n) (.bvar 0)) bi by
      simp [Expr.liftLooseBVars']]
    simp only [etaContract, bvarOccurs_lift_below f (show 0 < s + 1 by omega)]
    cases hf : bvarOccurs 0 f
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact lower_lift f (Nat.zero_le s) hf
    · simp [Expr.liftLooseBVars']
  · rw [etaContract_of_not h, etaContract_of_not (fun h' => h (etaShape_of_lift h'))]

/-- Universe instantiation creates no η-shape. Reference: none. -/
theorem etaShape_of_instLevels {ps : List Name} {us : List Level} {e : Expr}
    (h : EtaShape (Pure.instLevels ps us e)) : EtaShape e := by
  obtain ⟨m, t, f, bi, he⟩ := h
  cases e <;> simp only [Pure.instLevels, reduceCtorEq, Expr.lam.injEq] at he
  rename_i b _
  obtain ⟨-, -, hb, -⟩ := he
  cases b <;> simp only [Pure.instLevels, reduceCtorEq, Expr.app.injEq] at hb
  rename_i c
  obtain ⟨-, hc⟩ := hb
  cases c <;> simp only [Pure.instLevels, reduceCtorEq, Expr.bvar.injEq] at hc
  subst hc; exact ⟨_, _, _, _, rfl⟩

/-- `etaContract` commutes with universe instantiation. Reference: none. -/
theorem etaContract_instLevels (ps : List Name) (us : List Level) (e : Expr) :
    etaContract (Pure.instLevels ps us e) = Pure.instLevels ps us (etaContract e) := by
  by_cases h : EtaShape e
  · obtain ⟨m, t, f, bi, rfl⟩ := h
    simp only [Pure.instLevels, etaContract, bvarOccurs_instLevels]
    cases hf : bvarOccurs 0 f
    · simp only [Bool.false_eq_true, ↓reduceIte]; rw [instLevels_instantiate1']; rfl
    · simp [Pure.instLevels]
  · rw [etaContract_of_not h, etaContract_of_not (fun h' => h (etaShape_of_instLevels h'))]

/-- Lifting from `0` by at least one never gives `bvar 0`. Reference: none. -/
theorem lift_ne_bvar0 (a : Expr) (d : Nat) : a.liftLooseBVars' 0 (d + 1) ≠ .bvar 0 := by
  cases a <;> simp [Expr.liftLooseBVars']

/-- `etaContract` commutes with instantiation on a λ (instantiation creates no η-shape under a
λ: the substituted term is lifted past the λ's variable). Reference: none. -/
theorem etaContract_inst_lam (a : Expr) (m : Name) (t b : Expr) (bi : BinderInfo) (d : Nat) :
    etaContract ((Expr.lam m t b bi).instantiate1' a d) =
      (etaContract (.lam m t b bi)).instantiate1' a d := by
  by_cases h : EtaShape (.lam m t b bi)
  · obtain ⟨_, _, f, _, he⟩ := h
    cases he
    rw [show (Expr.lam m t (.app f (.bvar 0)) bi).instantiate1' a d =
      .lam m (t.instantiate1' a d) (.app (f.instantiate1' a (d + 1)) (.bvar 0)) bi by
      simp [Expr.instantiate1']]
    simp only [etaContract, bvarOccurs_inst f a (show 0 < d + 1 by omega)]
    cases hf : bvarOccurs 0 f
    · simp only [Bool.false_eq_true, ↓reduceIte]
      simpa using lower_inst a f (j := d + 1) (k := 0) (by omega) hf
    · simp [Expr.instantiate1']
  · rw [etaContract_of_not h, etaContract_of_not]
    rintro ⟨m', t', f, bi', he⟩
    apply h
    simp only [Expr.instantiate1', Expr.lam.injEq] at he
    obtain ⟨-, -, hb, -⟩ := he
    cases b <;> simp only [Expr.instantiate1', reduceCtorEq] at hb
    · rename_i i
      split at hb
      · simp at hb
      · split at hb
        · have := bvarOccurs_lift_out a (s := 0) (n := d + 1) (k := 0) (by omega) (by omega)
          rw [hb] at this; simp [bvarOccurs] at this
        · simp at hb
    · rename_i c
      simp only [Expr.app.injEq] at hb
      obtain ⟨-, hc⟩ := hb
      cases c <;> simp only [Expr.instantiate1', reduceCtorEq] at hc
      rename_i i
      split at hc
      · cases hc; exact ⟨_, _, _, _, rfl⟩
      · split at hc
        · exact absurd hc (lift_ne_bvar0 a d)
        · simp only [Expr.bvar.injEq] at hc; omega

end Marks

open Marks

/-! ## `unmark` -/

/-- `unmark` commutes with lifting. Reference: none (DV-32). -/
theorem unmark_liftLooseBVars' : ∀ (e : Expr) (s n : Nat),
    unmark (e.liftLooseBVars' s n) = (unmark e).liftLooseBVars' s n
  | .bvar _, _, _ => rfl
  | .mdata m e, s, n => by
    simp only [Expr.liftLooseBVars', unmark]
    split
    · exact unmark_liftLooseBVars' e s n
    · exact unmark_liftLooseBVars' e s n
    · rw [unmark_liftLooseBVars' e s n, etaContract_lift]
    · simp only [Expr.liftLooseBVars', unmark_liftLooseBVars' e s n]
  | .app f a, s, n => by
    simp only [Expr.liftLooseBVars', unmark, unmark_liftLooseBVars' f, unmark_liftLooseBVars' a]
  | .lam _ t b _, s, n | .forallE _ t b _, s, n => by
    simp only [Expr.liftLooseBVars', unmark, unmark_liftLooseBVars' t, unmark_liftLooseBVars' b]
  | .letE _ t v b _, s, n => by
    simp only [Expr.liftLooseBVars', unmark, unmark_liftLooseBVars' t, unmark_liftLooseBVars' v,
      unmark_liftLooseBVars' b]
  | .proj _ _ e, s, n => by simp only [Expr.liftLooseBVars', unmark, unmark_liftLooseBVars' e]
  | .fvar _, _, _ | .mvar _, _, _ | .sort _, _, _ | .const .., _, _ | .lit _, _, _ => rfl

/-- `unmark` commutes with universe instantiation: unmarking the instance of a value marked at its
generic levels (`SrcEval.delta`) is the instance of the unmarked value. Reference: none (DV-32). -/
theorem unmark_instLevels (ps : List Name) (us : List Level) : ∀ (e : Expr),
    unmark (Pure.instLevels ps us e) = Pure.instLevels ps us (unmark e)
  | .mdata m e => by
    simp only [Pure.instLevels, unmark]
    split
    · exact unmark_instLevels ps us e
    · exact unmark_instLevels ps us e
    · rw [unmark_instLevels ps us e, etaContract_instLevels]
    · simp only [Pure.instLevels, unmark_instLevels ps us e]
  | .app f a => by simp only [Pure.instLevels, unmark, unmark_instLevels ps us f, unmark_instLevels ps us a]
  | .lam _ t b _ | .forallE _ t b _ => by
    simp only [Pure.instLevels, unmark, unmark_instLevels ps us t, unmark_instLevels ps us b]
  | .letE _ t v b _ => by
    simp only [Pure.instLevels, unmark, unmark_instLevels ps us t, unmark_instLevels ps us v,
      unmark_instLevels ps us b]
  | .proj _ _ e => by simp only [Pure.instLevels, unmark, unmark_instLevels ps us e]
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const .. | .lit _ => rfl

/-- Every `eta` mark sits on a λ, as `MarkOf` writes them (`markEta (.lam …)`). Reference: none
(DV-23). -/
def EtaLams : Expr → Prop
  | .mdata d e => (d = markMD 1 → e.isLambda = true) ∧ EtaLams e
  | .app f a => EtaLams f ∧ EtaLams a
  | .lam _ t b _ | .forallE _ t b _ => EtaLams t ∧ EtaLams b
  | .letE _ t v b _ => EtaLams t ∧ EtaLams v ∧ EtaLams b
  | .proj _ _ e => EtaLams e
  | _ => True

/-- `unmark` commutes with instantiation of a term whose `eta` marks sit on λs (an `eta` mark on
the substituted variable would contract the substituted λ). Reference: `subst` of λ□ and of
PCUIC commute with erasure (`MR E/ESubstitution.v:612 erases_subst0`); DV-23. -/
theorem unmark_instantiate1' (a : Expr) : ∀ (e : Expr) (d : Nat), EtaLams e →
    unmark (e.instantiate1' a d) = (unmark e).instantiate1' (unmark a) d
  | .bvar i, d, _ => by
    simp only [Expr.instantiate1', unmark]
    split
    · rfl
    · split
      · exact unmark_liftLooseBVars' a 0 d
      · rfl
  | .mdata m e, d, h => by
    simp only [Expr.instantiate1', unmark]
    split
    · exact unmark_instantiate1' a e d h.2
    · exact unmark_instantiate1' a e d h.2
    · have hl := h.1 rfl
      cases e with
      | lam n t b bi =>
        rw [unmark_instantiate1' a _ d h.2]
        simp only [unmark]
        exact etaContract_inst_lam _ n _ _ bi d
      | _ => simp [Expr.isLambda] at hl
    · simp only [Expr.instantiate1', unmark_instantiate1' a e d h.2]
  | .app f b, d, h => by
    simp only [Expr.instantiate1', unmark, unmark_instantiate1' a f d h.1,
      unmark_instantiate1' a b d h.2]
  | .lam _ t b _, d, h | .forallE _ t b _, d, h => by
    simp only [Expr.instantiate1', unmark, unmark_instantiate1' a t d h.1,
      unmark_instantiate1' a b (d + 1) h.2]
  | .letE _ t v b _, d, h => by
    simp only [Expr.instantiate1', unmark, unmark_instantiate1' a t d h.1,
      unmark_instantiate1' a v d h.2.1, unmark_instantiate1' a b (d + 1) h.2.2]
  | .proj _ _ e, d, h => by simp only [Expr.instantiate1', unmark, unmark_instantiate1' a e d h]
  | .fvar _, _, _ | .mvar _, _, _ | .sort _, _, _ | .const .., _, _ | .lit _, _, _ => rfl

end EraseProof
