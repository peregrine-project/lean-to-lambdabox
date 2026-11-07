import EraseProof.Spec
import EraseProof.TargetLift

/-!
# The λ□ side of a recursor's erasure

Closedness, free variables, closed substitution and the abstraction of a free variable on the two
λ□ forms of a recursor's erasure (`Erases.recLet`, `Erases.recFix`): the let-bindings of the minors
(`recLets`) around the fixpoint applied to lifted arguments, and the fixpoint with closed minors
substituted. The fixpoint itself (`RecFixOf`) is closed under the bindings and has no free variable.
-/

open Lean Erasure

namespace EraseProof

namespace RecLam

open TargetLift TargetSubst

theorem recLets_nil (d : Nat) (b : LBTerm) : recLets d [] b = b := rfl

theorem recLets_cons (d : Nat) (m : LBTerm) (mi : RecMinor) (ms : List (LBTerm × RecMinor))
    (b : LBTerm) :
    recLets d ((m, mi) :: ms) b = .letIn (binderNameOf mi.name) (lbLift d 0 m) (recLets (d + 1) ms b) :=
  rfl

/-- The bindings are closed under `k` when the minors are and the body is under the bindings. -/
theorem closedn_recLets : ∀ (ms : List (LBTerm × RecMinor)) (d k : Nat) (b : LBTerm),
    (∀ p ∈ ms, closedn k p.1 = true) → closedn (k + d + ms.length) b = true →
      closedn (k + d) (recLets d ms b) = true
  | [], d, k, b, _, hb => hb
  | (m, mi) :: ms, d, k, b, hm, hb => by
    rw [recLets_cons]
    simp only [closedn, Bool.and_eq_true]
    refine ⟨closedn_lbLift d m k 0 (hm _ (.head _)) (Nat.zero_le _), ?_⟩
    have := closedn_recLets ms (d + 1) k b (fun p hp => hm p (.tail _ hp))
      (by simpa [Nat.add_assoc, Nat.add_comm 1] using hb)
    rwa [show k + (d + 1) = k + d + 1 by omega] at this

/-- The converse of `closedn_recLets`. -/
theorem closedn_recLets_inv : ∀ (ms : List (LBTerm × RecMinor)) (d k : Nat) (b : LBTerm),
    closedn (k + d) (recLets d ms b) = true →
      (∀ p ∈ ms, closedn k p.1 = true) ∧ closedn (k + d + ms.length) b = true
  | [], d, k, b, h => ⟨fun _ hp => (nomatch hp), h⟩
  | (m, mi) :: ms, d, k, b, h => by
    rw [recLets_cons] at h
    simp only [closedn, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := closedn_recLets_inv ms (d + 1) k b
      (by rw [show k + (d + 1) = k + d + 1 by omega]; exact h.2)
    refine ⟨fun p hp => ?_, by simpa [Nat.add_assoc, Nat.add_comm 1] using h2⟩
    rcases List.mem_cons.1 hp with rfl | hp
    · exact closedn_of_lbLift d m k 0 h.1 (Nat.zero_le _)
    · exact h1 p hp

/-- A free variable of the bindings is one of a minor or of the body. -/
theorem hasFVar_recLets (x : FVarId) : ∀ (ms : List (LBTerm × RecMinor)) (d : Nat) (b : LBTerm),
    hasFVar x (recLets d ms b) = true → (∃ p ∈ ms, hasFVar x p.1 = true) ∨ hasFVar x b = true
  | [], _, _, h => .inr h
  | (m, mi) :: ms, d, b, h => by
    rw [recLets_cons] at h
    simp only [hasFVar, Bool.or_eq_true, hasFVar_lbLift] at h
    rcases h with h | h
    · exact .inl ⟨_, .head _, h⟩
    · rcases hasFVar_recLets x ms (d + 1) b h with ⟨p, hp, h⟩ | h
      · exact .inl ⟨p, .tail _ hp, h⟩
      · exact .inr h

/-- Abstracting a free variable in the bindings abstracts it in the minors and, under the
bindings, in the body. -/
theorem toBvar_recLets (x : FVarId) : ∀ (ms : List (LBTerm × RecMinor)) (d k : Nat) (b : LBTerm),
    _root_.toBvar x (k + d) (recLets d ms b) =
      recLets d (ms.map (Prod.map (_root_.toBvar x k) id))
        (_root_.toBvar x (k + d + ms.length) b)
  | [], d, k, b => rfl
  | (m, mi) :: ms, d, k, b => by
    rw [List.map_cons, Prod.map, recLets_cons, recLets_cons]
    simp only [_root_.toBvar, id]
    rw [toBvar_lbLift x d m k 0 (Nat.zero_le _),
      show k + d + 1 = k + (d + 1) by omega, toBvar_recLets x ms (d + 1) k b]
    simp only [List.length_cons, show k + (d + 1) + ms.length = k + d + (ms.length + 1) by omega]

/-- A closed substitution in the bindings substitutes in the minors and, under the bindings, in
the body. -/
theorem csubst_recLets {u : LBTerm} (hu : closedn 0 u = true) :
    ∀ (ms : List (LBTerm × RecMinor)) (d k : Nat) (b : LBTerm),
      csubst u (k + d) (recLets d ms b) =
        recLets d (ms.map (Prod.map (csubst u k) id)) (csubst u (k + d + ms.length) b)
  | [], d, k, b => rfl
  | (m, mi) :: ms, d, k, b => by
    rw [List.map_cons, Prod.map, recLets_cons, recLets_cons]
    simp only [csubst, id]
    rw [csubst_lbLift hu d m k 0 (Nat.zero_le _),
      show k + d + 1 = k + (d + 1) by omega, csubst_recLets hu ms (d + 1) k b]
    simp only [List.length_cons, show k + (d + 1) + ms.length = k + d + (ms.length + 1) by omega]

/-- The bindings of closed minors: the lifts are the identity. -/
theorem recLets_closed : ∀ (ms : List (LBTerm × RecMinor)) (d : Nat) (b : LBTerm),
    (∀ p ∈ ms, closedn 0 p.1 = true) →
      recLets d ms b = ms.foldr (fun p b => .letIn (binderNameOf p.2.name) p.1 b) b
  | [], _, _, _ => rfl
  | (m, mi) :: ms, d, b, h => by
    rw [recLets_cons, lbLift_closedn d m 0 (h _ (.head _)),
      recLets_closed ms (d + 1) b (fun p hp => h p (.tail _ hp))]
    rfl

/-- `closedn` of an application spine. -/
theorem closedn_mkApps {k : Nat} : ∀ {f : LBTerm} {as : List LBTerm},
    closedn k (mkApps f as) = true ↔ closedn k f = true ∧ ∀ a ∈ as, closedn k a = true
  | _, [] => by simp [mkApps]
  | _, a :: as => by
    rw [mkApps, closedn_mkApps]
    simp only [closedn, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp, and_assoc]

/-- A free variable of an application spine is one of its head or of an argument. -/
theorem hasFVar_mkApps {x : FVarId} : ∀ {f : LBTerm} {as : List LBTerm},
    hasFVar x (mkApps f as) = true → hasFVar x f = true ∨ ∃ a ∈ as, hasFVar x a = true
  | _, [], h => .inl h
  | f, a :: as, h => by
    rcases hasFVar_mkApps (f := .app f a) (as := as) h with h | ⟨b, hb, h⟩
    · simp only [hasFVar, Bool.or_eq_true] at h
      rcases h with h | h
      · exact .inl h
      · exact .inr ⟨a, .head _, h⟩
    · exact .inr ⟨b, .tail _ hb, h⟩

theorem toBvar_mkApps (x : FVarId) (d : Nat) :
    ∀ (f : LBTerm) (as : List LBTerm),
      _root_.toBvar x d (mkApps f as) = mkApps (_root_.toBvar x d f) (as.map (_root_.toBvar x d))
  | _, [] => rfl
  | f, a :: as => by
    rw [mkApps, toBvar_mkApps x d (.app f a) as]
    simp [_root_.toBvar, mkApps]

theorem csubst_mkApps (t : LBTerm) (k : Nat) :
    ∀ (f : LBTerm) (as : List LBTerm), csubst t k (mkApps f as) = mkApps (csubst t k f) (as.map (csubst t k))
  | _, [] => rfl
  | f, a :: as => by
    rw [mkApps, csubst_mkApps t k (.app f a) as]
    simp [csubst, mkApps]

/-- The fixpoint of `RecFixOf` with closed minors substituted is closed and has no free variable. -/
theorem substl_fix {F : LBTerm} {ws : List LBTerm} (hF : closedn ws.length F = true)
    (hFx : ∀ x, hasFVar x F = false)
    (hws : ∀ w ∈ ws, closedn 0 w = true ∧ ∀ x, hasFVar x w = false) :
    closedn 0 (substl ws.reverse F) = true ∧ ∀ x, hasFVar x (substl ws.reverse F) = false :=
  ⟨closedn_substl _ F 0 (fun w hw => (hws w (List.mem_reverse.1 hw)).1)
      (by simpa using hF),
    fun x => hasFVar_substl x _ F (fun w hw => (hws w (List.mem_reverse.1 hw)).2 x) (hFx x)⟩

/-- The parts of a `RecFixOf` fixpoint used by the λ□ lemmas. -/
theorem RecFixOf.closed {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {σ : EvalEnv}
    {rv : RecursorVal} {us : List Level} {minors : List RecMinor} {F : LBTerm}
    (h : RecFixOf E B σ rv us minors F) :
    minors.length = rv.numMinors ∧ closedn rv.numMinors F = true ∧ ∀ x, hasFVar x F = false := by
  obtain ⟨_, _, _, _, _, _, _, _, -, -, hl, -, -, -, -, -, -, -, -, hc, hx⟩ := h
  exact ⟨hl, hc, hx⟩

/-- The let-bound form of `Erases.recLet`. -/
abbrev recLetTerm (N : Nat) (mins' : List LBTerm) (minors : List RecMinor) (F : LBTerm)
    (is' : List LBTerm) (maj' : LBTerm) (extra' : List LBTerm) : LBTerm :=
  mkApps (recLets 0 (mins'.zip minors) (mkApps F ((is' ++ [maj']).map (lbLift N 0)))) extra'

/-- Abstracting a free variable in the let-bound form abstracts it in the parts. -/
theorem toBvar_recLetTerm (x : FVarId) (d N : Nat) {mins' : List LBTerm} {minors : List RecMinor}
    {F : LBTerm} {is' : List LBTerm} {maj' : LBTerm} {extra' : List LBTerm}
    (hz : (mins'.zip minors).length = N) (hF : ∀ y, hasFVar y F = false) :
    _root_.toBvar x d (recLetTerm N mins' minors F is' maj' extra') =
      recLetTerm N (mins'.map (_root_.toBvar x d)) minors F (is'.map (_root_.toBvar x d))
        (_root_.toBvar x d maj') (extra'.map (_root_.toBvar x d)) := by
  unfold recLetTerm
  rw [toBvar_mkApps]
  congr 1
  have := toBvar_recLets x (mins'.zip minors) 0 d
    (mkApps F ((is' ++ [maj']).map (lbLift N 0)))
  rw [Nat.add_zero] at this
  rw [this, ← List.zip_map_left, hz, toBvar_mkApps, toBvar_noFVar x F _ (hF x)]
  congr 2
  simp only [List.map_append, List.map_map, List.map_cons, List.map_nil]
  congr 1
  · refine List.map_congr_left fun a _ => ?_
    exact toBvar_lbLift x N a d 0 (Nat.zero_le _)
  · rw [toBvar_lbLift x N maj' d 0 (Nat.zero_le _)]

/-- A closed substitution in the let-bound form substitutes in the parts. -/
theorem csubst_recLetTerm {u : LBTerm} (hu : closedn 0 u = true) (d N : Nat) {mins' : List LBTerm}
    {minors : List RecMinor} {F : LBTerm} {is' : List LBTerm} {maj' : LBTerm}
    {extra' : List LBTerm} (hz : (mins'.zip minors).length = N) (hF : closedn N F = true) :
    csubst u d (recLetTerm N mins' minors F is' maj' extra') =
      recLetTerm N (mins'.map (csubst u d)) minors F (is'.map (csubst u d)) (csubst u d maj')
        (extra'.map (csubst u d)) := by
  unfold recLetTerm
  rw [csubst_mkApps]
  congr 1
  have := csubst_recLets hu (mins'.zip minors) 0 d (mkApps F ((is' ++ [maj']).map (lbLift N 0)))
  rw [Nat.add_zero] at this
  rw [this, ← List.zip_map_left, hz, csubst_mkApps,
    csubst_closedn u F N (d + N) hF (by omega)]
  congr 2
  simp only [List.map_append, List.map_map, List.map_cons, List.map_nil]
  congr 1
  · refine List.map_congr_left fun a _ => ?_
    exact csubst_lbLift hu N a d 0 (Nat.zero_le _)
  · rw [csubst_lbLift hu N maj' d 0 (Nat.zero_le _)]

/-- An element of the first list of a zip with a list at least as long. -/
theorem mem_zip_left {α β : Type} : ∀ {l₁ : List α} {l₂ : List β} {a : α},
    l₁.length ≤ l₂.length → a ∈ l₁ → ∃ b, (a, b) ∈ l₁.zip l₂
  | _ :: _, [], _, h, _ => by simp at h
  | x :: l₁, y :: l₂, a, h, ha => by
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨y, by simp⟩
    · obtain ⟨b, hb⟩ := mem_zip_left (l₂ := l₂) (by simp at h; omega) ha
      exact ⟨b, by simp [hb]⟩

/-- The parts of a closed let-bound form are closed. -/
theorem closedn_recLetTerm_inv {d N : Nat} {mins' : List LBTerm} {minors : List RecMinor}
    {F : LBTerm} {is' : List LBTerm} {maj' : LBTerm} {extra' : List LBTerm}
    (hlen : mins'.length ≤ minors.length) (hz : (mins'.zip minors).length = N)
    (h : closedn d (recLetTerm N mins' minors F is' maj' extra') = true) :
    (∀ a ∈ mins', closedn d a = true) ∧ (∀ a ∈ is', closedn d a = true) ∧ closedn d maj' = true ∧
      ∀ a ∈ extra', closedn d a = true := by
  unfold recLetTerm at h
  obtain ⟨h1, h2⟩ := closedn_mkApps.1 h
  have h1' := closedn_recLets_inv (mins'.zip minors) 0 d _ (by simpa using h1)
  rw [Nat.add_zero, hz] at h1'
  obtain ⟨hm, hb⟩ := h1'
  obtain ⟨-, hargs⟩ := closedn_mkApps.1 hb
  have harg : ∀ a ∈ is' ++ [maj'], closedn d a = true := fun a ha =>
    closedn_of_lbLift N a d 0 (hargs _ (by
      have := List.mem_map_of_mem (f := lbLift N 0) ha
      simpa using this)) (Nat.zero_le _)
  refine ⟨fun a ha => ?_, fun a ha => harg a (by simp [ha]), harg maj' (by simp), h2⟩
  obtain ⟨b, hb⟩ := mem_zip_left hlen ha
  exact hm _ hb

/-- A free variable of the let-bound form is one of its parts. -/
theorem hasFVar_recLetTerm {x : FVarId} {N : Nat} {mins' : List LBTerm} {minors : List RecMinor}
    {F : LBTerm} {is' : List LBTerm} {maj' : LBTerm} {extra' : List LBTerm}
    (hF : ∀ y, hasFVar y F = false)
    (h : hasFVar x (recLetTerm N mins' minors F is' maj' extra') = true) :
    (∃ a ∈ mins', hasFVar x a = true) ∨ (∃ a ∈ is', hasFVar x a = true) ∨ hasFVar x maj' = true ∨
      ∃ a ∈ extra', hasFVar x a = true := by
  unfold recLetTerm at h
  rcases hasFVar_mkApps h with h | h
  · rcases hasFVar_recLets x _ 0 _ h with ⟨p, hp, h⟩ | h
    · exact .inl ⟨p.1, (List.of_mem_zip hp).1, h⟩
    · rcases hasFVar_mkApps h with h | ⟨a, ha, h⟩
      · rw [hF x] at h; cases h
      · obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.1 ha
        rw [hasFVar_lbLift] at h
        rcases List.mem_append.1 ha₀ with ha₀ | ha₀
        · exact .inr (.inl ⟨a₀, ha₀, h⟩)
        · rw [List.mem_singleton.1 ha₀] at h; exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr h))

end RecLam

end EraseProof
