import LeanToLambdaBox.Semantics.Compute

/-!
# Fuel — the monotonicity kit for fuel-indexed functions

Every total stand-in for a partial traversal in this development is fuel-indexed:
the executable evaluator `lbEval`, the fragment checker `supportedB`, the
first-order inductive check. Such a function answers at some fuel and says
nothing at less, so statements about them come in two shapes: *more fuel never
loses an answer* (monotonicity), and *finitely many per-element answers can be
re-checked at one common fuel* (uniformity).

`Mono` and `exists_uniform` state that pair once, at an arbitrary fuel-indexed
predicate; `lbEval_mono'` and `lbEval_exists_uniform` are the instance for the
evaluator, whose per-fuel monotonicity is `Semantics.Compute`'s `lbEval_mono`.
The two `List.mapM` lemmas are the monad-level half: a traversal in `Except`
transports along a pointwise-stronger callback, and per-element successes
assemble into one.
-/

namespace LeanToLambdaBox.Fuel

/-- A fuel-indexed predicate is monotone when more fuel never loses an answer. -/
def Mono {α : Sort u} (P : Nat → α → Prop) : Prop :=
  ∀ {n m : Nat} {a : α}, n ≤ m → P n a → P m a

/-- **Uniform fuel.** For a monotone fuel-indexed predicate, per-element fuels over a
finite list unify to a single fuel that works for every element — the maximum, reached
by monotonicity. -/
theorem exists_uniform {α : Type u} {P : Nat → α → Prop} (hm : Mono P) :
    ∀ (l : List α), (∀ i (hi : i < l.length), ∃ n, P n l[i]) →
      ∃ n, ∀ i (hi : i < l.length), P n l[i] := by
  intro l
  induction l with
  | nil => intro _; exact ⟨0, fun i hi => absurd hi (by simp)⟩
  | cons a as ih =>
      intro h
      obtain ⟨n₀, hn₀⟩ := h 0 (by simp)
      simp only [List.getElem_cons_zero] at hn₀
      obtain ⟨n₁, hn₁⟩ := ih (fun i hi => by
        have := h (i + 1) (by simpa using hi); simpa using this)
      refine ⟨max n₀ n₁, fun i hi => ?_⟩
      cases i with
      | zero => exact hm (Nat.le_max_left _ _) (by simpa using hn₀)
      | succ j =>
          have := hn₁ j (by simpa using hi)
          exact hm (Nat.le_max_right _ _) (by simpa using this)

/-- Evaluator success is a monotone fuel-indexed predicate. -/
theorem lbEval_mono' (Γ : GlobalDeclarations) (fl : WcbvFlags) :
    Mono (fun (n : Nat) (t : LBTerm) => ∃ v, lbEval Γ fl n t = some v) := by
  rintro n m t hnm ⟨v, hv⟩
  exact ⟨v, lbEval_mono hv hnm⟩

/-- Terms that each evaluate at some fuel all evaluate at one common fuel. -/
theorem lbEval_exists_uniform {Γ : GlobalDeclarations} {fl : WcbvFlags} (l : List LBTerm)
    (h : ∀ i (hi : i < l.length), ∃ n v, lbEval Γ fl n l[i] = some v) :
    ∃ n, ∀ i (hi : i < l.length), ∃ v, lbEval Γ fl n l[i] = some v :=
  exists_uniform (P := fun n t => ∃ v, lbEval Γ fl n t = some v) (lbEval_mono' Γ fl) l h

/-- A traversal in `Except` transports along a pointwise-stronger callback: if every
success of `f` is a success of `g` with the same value, a successful `mapM f` is a
successful `mapM g` with the same list. -/
theorem mapM_mono {α : Type u} {β : Type v} {ε : Type w} {f g : α → Except ε β}
    (h : ∀ a b, f a = .ok b → g a = .ok b) :
    ∀ (l : List α) (l' : List β), l.mapM f = .ok l' → l.mapM g = .ok l' := by
  intro l
  induction l with
  | nil => intro l' hl; simpa using hl
  | cons a as ih =>
      intro l' hl
      rw [List.mapM_cons] at hl ⊢
      cases ha : f a with
      | error e => rw [ha] at hl; simp [bind, Except.bind] at hl
      | ok b =>
          rw [ha] at hl; simp only [bind, Except.bind] at hl
          cases has : as.mapM f with
          | error e => rw [has] at hl; simp at hl
          | ok bs =>
              rw [has] at hl; simp only [pure, Except.pure] at hl
              cases hl
              rw [h a b ha]; simp only [bind, Except.bind]
              rw [ih bs has]; simp [pure, Except.pure]

/-- Per-element successes assemble: if the callback succeeds on every element, the
traversal succeeds on the list. -/
theorem exists_mapM_ok {α : Type u} {β : Type v} {ε : Type w} {f : α → Except ε β} :
    ∀ (l : List α), (∀ a ∈ l, ∃ b, f a = .ok b) → ∃ l', l.mapM f = .ok l' := by
  intro l
  induction l with
  | nil => intro _; exact ⟨[], rfl⟩
  | cons a as ih =>
      intro h
      obtain ⟨b, hb⟩ := h a (by simp)
      obtain ⟨bs, hbs⟩ := ih (fun x hx => h x (by simp [hx]))
      refine ⟨b :: bs, ?_⟩
      rw [List.mapM_cons, hb]
      simp only [bind, Except.bind]
      rw [hbs]; simp [pure, Except.pure]

end LeanToLambdaBox.Fuel
