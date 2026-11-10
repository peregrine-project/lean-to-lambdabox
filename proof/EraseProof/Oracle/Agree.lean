import LeanToLambdaBox.Erasure.Pure
import Lean4Lean.Verify.Typing.Lemmas

/-!
# The oracle's frame lemma

`Pure.isErasable_agree`: over closed declarations, the pure erasability oracle
`Erasure.Pure.isErasable` answers alike on two lists of locals that agree on a set `S` of free
variables containing the term's free variables and closed under the locals' types and values. The
lemmas below prove the same for the oracle's parts `whnf`, `inferType` and `isArity`, together with
the scoping fact that their results stay within `S`.
-/

open Lean Lean4Lean Erasure

namespace EraseProof

/-- The declarations' types and values have no free variables (`collectDeps` rejects them).
Reference: none (closed PCUIC declarations; DV-13). -/
def ClosedDecls (decls : List ConstantInfo) : Prop :=
  ∀ ci ∈ decls, FVarsIn (fun _ => False) ci.type ∧
    ∀ v, ci.value? (allowOpaque := true) = some v → FVarsIn (fun _ => False) v

/-- `S` is closed under the locals: the type and value of every local found for a variable in `S`
mention only variables in `S`. Reference: none (frame vocabulary, DV-13). -/
def LocalsSupport (S : FVarId → Prop) (ls : List Local) : Prop :=
  ∀ x, S x → ∀ l, Pure.findLocal ls x = some l →
    FVarsIn S l.type ∧ ∀ v, l.value? = some v → FVarsIn S v

/-- Two local lists give the same answer for every variable in `S`. Reference: none (frame
vocabulary, DV-13). -/
def LocalsAgree (S : FVarId → Prop) (ls₁ ls₂ : List Local) : Prop :=
  ∀ x, S x → Pure.findLocal ls₁ x = Pure.findLocal ls₂ x

/-! ## `Except` plumbing -/

/-- Congruence of `Except`'s bind, where the continuations need only agree on the successful
results of the first computation. Reference: none. -/
theorem Except.bind_congr_ok {ε α β} {x y : Except ε α} {k₁ k₂ : α → Except ε β} (hxy : x = y)
    (hk : ∀ a, y = .ok a → k₁ a = k₂ a) : (x >>= k₁) = (y >>= k₂) := by
  subst hxy
  match x, hk with
  | .error _, _ => rfl
  | .ok a, hk => exact hk a rfl

/-- A successful bind of `Except` has a successful first computation. Reference: none. -/
theorem Except.ok_of_bind {ε α β} {x : Except ε α} {k : α → Except ε β} {r : β}
    (h : (x >>= k) = .ok r) : ∃ a, x = .ok a ∧ k a = .ok r := by
  cases x with
  | error e => exact absurd h (by simp [bind, Except.bind])
  | ok a => exact ⟨a, rfl, h⟩

namespace Pure

variable {S : FVarId → Prop}

/-! ## Universe instantiation -/

/-- `Erasure.Pure.instLevel` with metavariable-free levels keeps a level metavariable-free.
Reference: none (lean4lean's `FVarsIn` asks levels to be metavariable-free). -/
theorem instLevel_hasMVar' {ps : List Name} {us : List Level}
    (hus : ∀ v ∈ us, v.hasMVar' = false) :
    ∀ {u : Level}, u.hasMVar' = false → (Erasure.Pure.instLevel ps us u).hasMVar' = false
  | .zero, _ => rfl
  | .succ l, h => by
    simp only [Erasure.Pure.instLevel, Level.hasMVar'] at h ⊢; exact instLevel_hasMVar' hus h
  | .max a b, h | .imax a b, h => by
    simp only [Erasure.Pure.instLevel, Level.hasMVar', Bool.or_eq_false_iff] at h ⊢
    exact ⟨instLevel_hasMVar' hus h.1, instLevel_hasMVar' hus h.2⟩
  | .param n, _ => by
    simp only [Erasure.Pure.instLevel]
    split
    · rename_i p u hp
      exact hus u (List.of_mem_zip (List.mem_of_find?_eq_some hp)).2
    · rfl
  | .mvar _, h => by simp [Level.hasMVar'] at h

/-- `Erasure.Pure.instLevels` with metavariable-free levels keeps the free variables of a term.
Reference: none. -/
theorem fvarsIn_instLevels {ps : List Name} {us : List Level}
    (hus : ∀ v ∈ us, v.hasMVar' = false) : ∀ {e : Expr}, FVarsIn S e →
      FVarsIn S (Erasure.Pure.instLevels ps us e)
  | .bvar _, h | .fvar _, h | .mvar _, h | .lit _, h => h
  | .sort u, h => instLevel_hasMVar' hus h
  | .const c ls, h => by
    simp only [FVarsIn, Erasure.Pure.instLevels, List.mem_map] at h ⊢
    rintro _ ⟨l, hl, rfl⟩; exact instLevel_hasMVar' hus (h l hl)
  | .app f a, ⟨h1, h2⟩ => ⟨fvarsIn_instLevels hus h1, fvarsIn_instLevels hus h2⟩
  | .lam _ t b _, ⟨h1, h2⟩ | .forallE _ t b _, ⟨h1, h2⟩ =>
    ⟨fvarsIn_instLevels hus h1, fvarsIn_instLevels hus h2⟩
  | .letE _ t v b _, ⟨h1, h2, h3⟩ =>
    ⟨fvarsIn_instLevels hus h1, fvarsIn_instLevels hus h2, fvarsIn_instLevels hus h3⟩
  | .mdata _ e, h => fvarsIn_instLevels (e := e) hus h
  | .proj _ _ e, h => fvarsIn_instLevels (e := e) hus h

/-! ## The oracle's parts -/

section
variable {cx : Erasure.Pure.Ctx} {ls₁ ls₂ : List Local}
  (hcl : ClosedDecls cx.decls) (hS : LocalsSupport S ls₁) (hag : LocalsAgree S ls₁ ls₂)
include hcl hS hag

/-- Frame for `Erasure.Pure.whnf`: on a term with free variables in `S`, the two local lists give
the same result, and a successful result has its free variables in `S`. Reference: none (DV-13). -/
theorem whnf_agree : ∀ (f : Nat) (e : Expr), FVarsIn S e →
    Erasure.Pure.whnf cx f ls₁ e = Erasure.Pure.whnf cx f ls₂ e ∧
      ∀ w, Erasure.Pure.whnf cx f ls₁ e = .ok w → FVarsIn S w
  | 0, e, _ => ⟨rfl, fun w h => by
      simp [Erasure.Pure.whnf, throw, throwThe, MonadExceptOf.throw] at h⟩
  | f + 1, .app g a, ⟨hg, ha⟩ => by
    have ⟨ig, fg⟩ := whnf_agree f g hg
    refine ⟨?_, ?_⟩
    · simp only [Erasure.Pure.whnf]
      refine Except.bind_congr_ok ig fun w hw => ?_
      have hw' := fg w (ig ▸ hw)
      split
      · exact (whnf_agree f _ (FVarsIn.instantiate1_go hw'.2 ha)).1
      · rfl
    · intro w h
      simp only [Erasure.Pure.whnf] at h
      obtain ⟨g', h1, h2⟩ := Except.ok_of_bind h
      have hw' := fg g' h1
      split at h2
      · exact (whnf_agree f _ (FVarsIn.instantiate1_go hw'.2 ha)).2 w h2
      · cases h2; exact ⟨hw', ha⟩
  | f + 1, .letE _ _ v b _, ⟨_, hv, hb⟩ => by
    simp only [Erasure.Pure.whnf]
    exact whnf_agree f _ (FVarsIn.instantiate1_go hb hv)
  | f + 1, .mdata _ e, h => by
    simp only [Erasure.Pure.whnf]; exact whnf_agree f e h
  | f + 1, .fvar x, h => by
    have hx : S x := h
    simp only [Erasure.Pure.whnf]
    rw [← hag x hx]
    split
    · rename_i fv nm ty v hl
      exact whnf_agree f v ((hS x hx _ hl).2 v rfl)
    · exact ⟨rfl, fun w hw => by cases hw; exact hx⟩
  | f + 1, .const c us, h => by
    simp only [Erasure.Pure.whnf]
    split
    · rename_i v hv
      split
      · exact ⟨rfl, fun w hw => by cases hw; exact h⟩
      · have hval : FVarsIn (fun _ => False) v.value :=
          (hcl _ (List.mem_of_find?_eq_some hv)).2 v.value rfl
        exact whnf_agree f _ (fvarsIn_instLevels h (FVarsIn.mono (fun _ h => h.elim) hval))
    · exact ⟨rfl, fun w hw => by cases hw; exact h⟩
  | f + 1, .bvar _, h | f + 1, .sort _, h | f + 1, .lam .., h | f + 1, .forallE .., h
  | f + 1, .lit _, h | f + 1, .mvar _, h | f + 1, .proj .., h =>
    ⟨rfl, fun w hw => by cases hw; exact h⟩

/-- Frame for `Erasure.Pure.inferType`: on a term and binder types with free variables in `S`, the
two local lists give the same result, and a successful result has its free variables in `S`.
Reference: none (DV-13). -/
theorem inferType_agree : ∀ (f : Nat) (Γ : List Expr) (e : Expr), FVarsIn S e →
    (∀ A ∈ Γ, FVarsIn S A) →
    Erasure.Pure.inferType cx f ls₁ Γ e = Erasure.Pure.inferType cx f ls₂ Γ e ∧
      ∀ T, Erasure.Pure.inferType cx f ls₁ Γ e = .ok T → FVarsIn S T
  | 0, _, e, _, _ => ⟨rfl, fun w h => by
      simp [Erasure.Pure.inferType, throw, throwThe, MonadExceptOf.throw] at h⟩
  | f + 1, Γ, .bvar i, _, hΓ => by
    refine ⟨rfl, fun T hT => ?_⟩
    simp only [Erasure.Pure.inferType] at hT
    split at hT
    · rename_i A hA
      cases hT
      exact FVarsIn.liftLooseBVars (hΓ A (List.mem_of_getElem? hA))
    · simp [throw, throwThe, MonadExceptOf.throw] at hT
  | f + 1, Γ, .fvar x, h, _ => by
    have hx : S x := h
    simp only [Erasure.Pure.inferType]
    rw [← hag x hx]
    refine ⟨rfl, fun T hT => ?_⟩
    split at hT
    · rename_i l hl; cases hT; exact (hS x hx l hl).1
    · simp [throw, throwThe, MonadExceptOf.throw] at hT
  | f + 1, Γ, .sort u, h, _ => ⟨rfl, fun T hT => by
      simp only [Erasure.Pure.inferType, pure, Except.pure, Except.ok.injEq] at hT
      subst hT; exact (show (Level.succ u).hasMVar' = false from h)⟩
  | f + 1, Γ, .const c us, h, _ => by
    refine ⟨rfl, fun T hT => ?_⟩
    simp only [Erasure.Pure.inferType] at hT
    split at hT
    · rename_i ci hci
      split at hT
      · simp only [pure, Except.pure, Except.ok.injEq] at hT; subst hT
        exact fvarsIn_instLevels h
          (FVarsIn.mono (fun _ h => h.elim) (hcl _ (List.mem_of_find?_eq_some hci)).1)
      · simp [throw, throwThe, MonadExceptOf.throw] at hT
    · simp [throw, throwThe, MonadExceptOf.throw] at hT
  | f + 1, Γ, .app g a, ⟨hg, ha⟩, hΓ => by
    have ⟨ig, fg⟩ := inferType_agree f Γ g hg hΓ
    refine ⟨?_, ?_⟩
    · simp only [Erasure.Pure.inferType]
      refine Except.bind_congr_ok ig fun Tg hTg => ?_
      have ⟨iw, _⟩ := whnf_agree hcl hS hag f Tg (fg Tg (ig ▸ hTg))
      exact Except.bind_congr_ok iw fun _ _ => rfl
    · intro T hT
      simp only [Erasure.Pure.inferType] at hT
      obtain ⟨Tg, h1, hT⟩ := Except.ok_of_bind hT
      obtain ⟨w, h2, hT⟩ := Except.ok_of_bind hT
      have hw := (whnf_agree hcl hS hag f Tg (fg Tg h1)).2 w h2
      split at hT
      · cases hT; exact FVarsIn.instantiate1_go hw.2 ha
      · simp [throw, throwThe, MonadExceptOf.throw] at hT
  | f + 1, Γ, .lam n t b bi, ⟨ht, hb⟩, hΓ => by
    have hΓ' : ∀ A ∈ t :: Γ, FVarsIn S A := by
      intro A hA; simp only [List.mem_cons] at hA; rcases hA with rfl | hA
      exacts [ht, hΓ A hA]
    have ⟨ib, fb⟩ := inferType_agree f (t :: Γ) b hb hΓ'
    refine ⟨?_, ?_⟩
    · simp only [Erasure.Pure.inferType]; rw [ib]
    · intro T hT
      simp only [Erasure.Pure.inferType] at hT
      obtain ⟨B, h1, hT⟩ := Except.ok_of_bind hT
      cases hT; exact ⟨ht, fb B h1⟩
  | f + 1, Γ, .forallE n t b bi, ⟨ht, hb⟩, hΓ => by
    have hΓ' : ∀ A ∈ t :: Γ, FVarsIn S A := by
      intro A hA; simp only [List.mem_cons] at hA; rcases hA with rfl | hA
      exacts [ht, hΓ A hA]
    have ⟨it, ft⟩ := inferType_agree f Γ t ht hΓ
    have ⟨ib, fb⟩ := inferType_agree f (t :: Γ) b hb hΓ'
    refine ⟨?_, ?_⟩
    · simp only [Erasure.Pure.inferType]
      refine Except.bind_congr_ok it fun Tt hTt => ?_
      have ⟨iw, _⟩ := whnf_agree hcl hS hag f Tt (ft Tt (it ▸ hTt))
      refine Except.bind_congr_ok iw fun w1 _ => ?_
      split
      · refine Except.bind_congr_ok ib fun Tb hTb => ?_
        have ⟨iw', _⟩ := whnf_agree hcl hS hag f Tb (fb Tb (ib ▸ hTb))
        exact Except.bind_congr_ok iw' fun _ _ => rfl
      · rfl
    · intro T hT
      simp only [Erasure.Pure.inferType] at hT
      obtain ⟨Tt, h1, hT⟩ := Except.ok_of_bind hT
      obtain ⟨w1, h2, hT⟩ := Except.ok_of_bind hT
      have hw1 := (whnf_agree hcl hS hag f Tt (ft Tt h1)).2 w1 h2
      split at hT
      · obtain ⟨Tb, h3, hT⟩ := Except.ok_of_bind hT
        obtain ⟨w2, h4, hT⟩ := Except.ok_of_bind hT
        have hw2 := (whnf_agree hcl hS hag f Tb (fb Tb h3)).2 w2 h4
        split at hT
        · cases hT
          show (Level.imax _ _).hasMVar' = false
          simp only [Level.hasMVar', Bool.or_eq_false_iff]
          exact ⟨hw1, hw2⟩
        · simp [throw, throwThe, MonadExceptOf.throw] at hT
      · simp [throw, throwThe, MonadExceptOf.throw] at hT
  | f + 1, Γ, .letE _ _ v b _, ⟨_, hv, hb⟩, hΓ => by
    simp only [Erasure.Pure.inferType]
    exact inferType_agree f Γ _ (FVarsIn.instantiate1_go hb hv) hΓ
  | f + 1, Γ, .mdata _ e, h, hΓ => by
    simp only [Erasure.Pure.inferType]; exact inferType_agree f Γ e h hΓ
  | f + 1, Γ, .lit _, _, _ | f + 1, Γ, .mvar _, _, _ | f + 1, Γ, .proj .., _, _ =>
    ⟨rfl, fun T hT => by
      simp [Erasure.Pure.inferType, throw, throwThe, MonadExceptOf.throw] at hT⟩

/-- Frame for `Erasure.Pure.isArity`: on a term with free variables in `S`, the two local lists
give the same result. Reference: none (DV-13). -/
theorem isArity_agree : ∀ (f : Nat) (T : Expr), FVarsIn S T →
    Erasure.Pure.isArity cx f ls₁ T = Erasure.Pure.isArity cx f ls₂ T
  | 0, _, _ => rfl
  | f + 1, T, h => by
    simp only [Erasure.Pure.isArity]
    have ⟨iw, fw⟩ := whnf_agree hcl hS hag f T h
    refine Except.bind_congr_ok iw fun w hw => ?_
    split
    · rfl
    · rename_i B _
      have hB := fw _ (iw ▸ hw)
      exact isArity_agree f B hB.2
    · rfl

end

end Pure

/-- Frame: the answer depends only on the locals reachable from `e` (through their types and
values), given closed declarations. Used at every oracle call of `visit_agree`'s induction.
Reference: none; MetaRocq erases a constant body in the empty context
(`MR E/ErasureFunction.v:1309 erase_constant_body`); DV-13. -/
theorem Pure.isErasable_agree {S : FVarId → Prop} (hcl : ClosedDecls cx.decls)
    (hS : LocalsSupport S ls₁) (hag : LocalsAgree S ls₁ ls₂) (he : FVarsIn S e) :
    Pure.isErasable cx fuel ls₁ e = Pure.isErasable cx fuel ls₂ e := by
  simp only [Erasure.Pure.isErasable]
  have ⟨iT, fT⟩ := inferType_agree hcl hS hag fuel [] e he (by simp)
  refine Except.bind_congr_ok iT fun T hT => ?_
  have hT' := fT T (iT ▸ hT)
  refine Except.bind_congr_ok (isArity_agree hcl hS hag fuel T hT') fun b _ => ?_
  split
  · rfl
  · have ⟨iS, fS⟩ := inferType_agree hcl hS hag fuel [] T hT' (by simp)
    refine Except.bind_congr_ok iS fun S' hS' => ?_
    have ⟨iw, _⟩ := whnf_agree hcl hS hag fuel S' (fS S' (iS ▸ hS'))
    exact Except.bind_congr_ok iw fun _ _ => rfl

end EraseProof
