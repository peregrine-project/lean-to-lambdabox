import EraseProof.Oracle.Whnf

/-!
# The oracle's frame lemma

`Pure.isErasable_agree`: over declarations whose read expressions are closed (`ClosedDecls`), the
pure erasability oracle `Erasure.Pure.isErasable` answers alike on two lists of locals that agree on
a set `S` of free variables containing the term's free variables and closed under the locals' types
and values. The lemmas below prove the same for the oracle's parts.

`ClosedDecls` covers the values of every definition, which `Pure.whnf` δ-unfolds, so the results
of `Pure.whnf` are in `S` (`FVarsIn S`). Port of `L4 Oracle/Agree.lean`.
-/

open Lean Erasure

namespace EraseProof

/-- The expressions the pure traversal reads from the declarations (`ReadExpr`) and the values of
all definitions, which the oracle δ-unfolds, mention no free variable (port of
`L4 Oracle/Agree.lean:20`, there over every type and value). -/
def ClosedDecls (decls : List ConstantInfo) : Prop :=
  ∀ ci ∈ decls, ∀ x, (ReadExpr decls ci x ∨ ∃ d, ci = .defnInfo d ∧ x = d.value) →
    FVarsIn (fun _ => False) x

/-- `S` is closed under the locals (port of `L4 Oracle/Agree.lean:26`). -/
def LocalsSupport (S : FVarId → Prop) (ls : List Local) : Prop :=
  ∀ x, S x → ∀ l, Pure.findLocal ls x = some l →
    FVarsIn S l.type ∧ ∀ v, l.value? = some v → FVarsIn S v

/-- Two local lists agree on `S` (port of `L4 Oracle/Agree.lean:32`). -/
def LocalsAgree (S : FVarId → Prop) (ls₁ ls₂ : List Local) : Prop :=
  ∀ x, S x → Pure.findLocal ls₁ x = Pure.findLocal ls₂ x

namespace OracleAgree

/-! ## Free variables -/

theorem fvarsIn_false {p : FVarId → Prop} : ∀ {e : Expr}, FVarsIn (fun _ => False) e → FVarsIn p e
  | .fvar _, h => h.elim
  | .app f a, h => ⟨fvarsIn_false (e := f) h.1, fvarsIn_false (e := a) h.2⟩
  | .lam _ t b _, h | .forallE _ t b _, h => ⟨fvarsIn_false (e := t) h.1, fvarsIn_false (e := b) h.2⟩
  | .letE _ t v b _, h =>
    ⟨fvarsIn_false (e := t) h.1, fvarsIn_false (e := v) h.2.1, fvarsIn_false (e := b) h.2.2⟩
  | .mdata _ e, h | .proj _ _ e, h => fvarsIn_false (e := e) h
  | .bvar _, _ | .sort _, _ | .const .., _ | .lit _, _ | .mvar _, _ => trivial

theorem fvarsIn_instLevels {p : FVarId → Prop} (ps : List Name) (us : List Level) :
    ∀ {e : Expr}, FVarsIn p e → FVarsIn p (Pure.instLevels ps us e)
  | .app f a, h => ⟨fvarsIn_instLevels ps us (e := f) h.1, fvarsIn_instLevels ps us (e := a) h.2⟩
  | .lam _ t b _, h | .forallE _ t b _, h =>
    ⟨fvarsIn_instLevels ps us (e := t) h.1, fvarsIn_instLevels ps us (e := b) h.2⟩
  | .letE _ t v b _, h => ⟨fvarsIn_instLevels ps us (e := t) h.1,
    fvarsIn_instLevels ps us (e := v) h.2.1, fvarsIn_instLevels ps us (e := b) h.2.2⟩
  | .mdata _ e, h | .proj _ _ e, h => fvarsIn_instLevels ps us (e := e) h
  | .fvar _, h => h
  | .bvar _, _ | .sort _, _ | .const .., _ | .lit _, _ | .mvar _, _ => trivial

theorem fvarsIn_lift {p : FVarId → Prop} : ∀ {e : Expr} {s d : Nat}, FVarsIn p e →
    FVarsIn p (e.liftLooseBVars' s d) := by
  intro e
  induction e <;> intro s d h <;> simp_all [Expr.liftLooseBVars', FVarsIn]

theorem fvarsIn_inst {p : FVarId → Prop} {a : Expr} (ha : FVarsIn p a) :
    ∀ {b : Expr} {d : Nat}, FVarsIn p b → FVarsIn p (b.instantiate1' a d) := by
  intro b
  induction b with
  | bvar i =>
    intro d _
    simp only [Expr.instantiate1']
    split_ifs
    · trivial
    · exact fvarsIn_lift ha
    · trivial
  | _ => intro d h; simp_all [Expr.instantiate1', FVarsIn]

/-- The head of `spine` is the head of the application. -/
theorem spine_fst : ∀ e : Expr, (spine e).1 = e.getAppFn
  | .app f _ => by simp only [spine, Expr.getAppFn]; exact spine_fst f
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const .. | .lam .. | .forallE .. | .letE .. | .lit _
  | .mdata .. | .proj .. => rfl

/-- The arguments of `spine` have their free variables where the term has. -/
theorem spine_snd {p : FVarId → Prop} : ∀ {e : Expr}, FVarsIn p e → ∀ a ∈ (spine e).2, FVarsIn p a
  | .app f x, h => by
    simp only [spine, List.mem_append, List.mem_singleton]
    rintro a (ha | rfl)
    · exact spine_snd h.1 a ha
    · exact h.2
  | .bvar _, _ | .fvar _, _ | .mvar _, _ | .sort _, _ | .const .., _ | .lam .., _ | .forallE .., _
  | .letE .., _ | .lit _, _ | .mdata .., _ | .proj .., _ => by simp [spine]

/-! ## `Except` -/

theorem bind_congr_ok {ε α β : Type} {x y : Except ε α} {k₁ k₂ : α → Except ε β} (hxy : x = y)
    (hk : ∀ a, y = .ok a → k₁ a = k₂ a) : (x >>= k₁) = (y >>= k₂) := by
  subst hxy
  match x, hk with
  | .error _, _ => rfl
  | .ok a, hk => exact hk a rfl

theorem throw_ne_ok {α : Type} {e : EraseError} {a : α} :
    (throw e : Except EraseError α) ≠ .ok a := by
  simp [throw, throwThe, MonadExceptOf.throw]

/-! ## The oracle's parts -/

/-- The members of a successful `mapM` are images of members of the list. -/
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

/-- The term that the ι-rule of `Erasure.Pure.whnf` builds (`Erasure.Pure.iotaRhs?`) has its free
variables where the application and the major premise's normal form have them. -/
theorem iotaRhs_fvarsIn {S : FVarId → Prop} {decls : List ConstantInfo} {X wa e : Expr} {r : Name}
    {us : List Level} {rv : RecursorVal} {minors : List RecMinor} {args : List Expr}
    (hsp : spine X = (.const r us, args)) (hX : FVarsIn S X) (hwa : FVarsIn S wa)
    (he : Pure.iotaRhs? decls r us rv minors args wa = some e) : FVarsIn S e := by
  obtain ⟨C, uC, cargs, cv, mi, mk, rfs, hspw, -, -, -, -, hmk, hrfs, rfl⟩ :=
    OracleWhnf.iotaRhs?_spec he
  have hargs : ∀ a ∈ args, FVarsIn S a := by
    have := spine_snd hX; rw [hsp] at this; exact this
  have hcargs : ∀ a ∈ cargs, FVarsIn S a := by
    have := spine_snd hwa; rw [hspw] at this; exact this
  have hfs : ∀ a ∈ cargs.drop cv.numParams, FVarsIn S a := fun a ha => hcargs a (List.mem_of_mem_drop ha)
  rw [mkAppN_eq_foldl, FVarsIn_foldl]
  refine ⟨hargs mk (List.mem_of_mem_take (List.mem_of_mem_drop (List.mem_of_getElem? hmk))),
    fun a ha => ?_⟩
  rcases List.mem_append.mp ha with ha | ha
  · exact hfs a ha
  · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp ha
    rw [mkAppN_eq_foldl, FVarsIn_foldl]
    refine ⟨trivial, fun b hb => ?_⟩
    rcases List.mem_append.mp hb with hb | hb
    · exact hargs b (List.mem_of_mem_take hb)
    · rw [List.mem_singleton] at hb
      rw [hb]
      obtain ⟨h, -, hh⟩ := mem_of_mapM hrfs f hf
      exact hfs _ (List.mem_of_getElem? hh)

section
variable {S : FVarId → Prop} {cx : Pure.Ctx} {ls₁ ls₂ : List Local}

theorem bind_agree {ε α β : Type} {x₁ x₂ : Except ε α} {k₁ k₂ : α → Except ε β}
    (P : α → Prop) (Q : β → Prop) (hx : x₁ = x₂ ∧ ∀ a, x₁ = .ok a → P a)
    (hk : ∀ a, P a → k₁ a = k₂ a ∧ ∀ b, k₁ a = .ok b → Q b) :
    (x₁ >>= k₁) = (x₂ >>= k₂) ∧ ∀ b, (x₁ >>= k₁) = .ok b → Q b := by
  obtain ⟨rfl, hP⟩ := hx
  rcases x₁ with e | a
  · exact ⟨rfl, fun b h => nomatch h⟩
  · exact hk a (hP a rfl)

variable (hcl : ClosedDecls cx.decls) (hS : LocalsSupport S ls₁) (hag : LocalsAgree S ls₁ ls₂)
include hcl hS hag

/-- Frame for `Erasure.Pure.whnf`: on a term in `S`, the two local lists give the same result, in
`S`. -/
theorem whnf_agree : ∀ (f : Nat) (e : Expr), FVarsIn S e →
    Pure.whnf cx f ls₁ e = Pure.whnf cx f ls₂ e ∧
      ∀ w, Pure.whnf cx f ls₁ e = .ok w → FVarsIn S w
  | 0, e, _ => ⟨rfl, fun w h => absurd h throw_ne_ok⟩
  | f + 1, .app g a, ⟨hg, ha⟩ => by
    have ⟨ig, fg⟩ := whnf_agree f g hg
    have ⟨ia, fa⟩ := whnf_agree f a ha
    refine ⟨?_, fun w h => ?_⟩
    · simp only [Pure.whnf]
      refine bind_congr_ok ig fun g' hg' => ?_
      have hS' := fg g' (ig ▸ hg')
      cases g' with
      | lam n t b bi => exact (whnf_agree f _ (fvarsIn_inst ha hS'.2)).1
      | _ =>
        dsimp only
        split
        · rename_i r us rv minors args hia
          refine bind_congr_ok ia fun wa hwa => ?_
          split
          · rename_i e he
            exact (whnf_agree f e (iotaRhs_fvarsIn (OracleWhnf.iotaApp?_spec hia).1 ⟨hS', ha⟩
              (fa wa (ia ▸ hwa)) he)).1
          · rfl
        · rfl
    · obtain ⟨g', h1, h2⟩ := OracleWhnf.whnf_app_cases h
      have hS' := fg g' h1
      rcases h2 with ⟨n, t, b, bi, rfl, h2⟩ | ⟨-, rfl | ⟨r, us, args, rv, minors, wa, e, hsp, -, -, -,
        hwa, he, hw⟩⟩
      · exact (whnf_agree f _ (fvarsIn_inst ha hS'.2)).2 w h2
      · exact ⟨hS', ha⟩
      · exact (whnf_agree f e (iotaRhs_fvarsIn hsp ⟨hS', ha⟩ (fa wa hwa) he)).2 w hw
  | f + 1, .letE _ _ v b _, ⟨_, hv, hb⟩ => by
    simp only [Pure.whnf]
    exact whnf_agree f _ (fvarsIn_inst hv hb)
  | f + 1, .mdata _ e, h => by
    simp only [Pure.whnf]; exact whnf_agree f e h
  | f + 1, .fvar x, h => by
    have hx : S x := h
    simp only [Pure.whnf]
    rw [← hag x hx]
    split
    · rename_i fv nm ty v hl
      exact whnf_agree f v ((hS x hx _ hl).2 v rfl)
    · exact ⟨rfl, fun w hw => by cases hw; exact hx⟩
  | f + 1, .const c us, h => by
    simp only [Pure.whnf]
    split
    · rename_i v hv
      split
      · exact ⟨rfl, fun w hw => by cases hw; exact h⟩
      · have hval : FVarsIn (fun _ => False) v.value :=
          hcl _ (List.mem_of_find?_eq_some hv) _ (.inr ⟨v, rfl, rfl⟩)
        exact whnf_agree f _ (fvarsIn_instLevels _ _ (fvarsIn_false hval))
    · exact ⟨rfl, fun w hw => by cases hw; exact h⟩
  | f + 1, .proj S' i s, h => by
    have ⟨is, fs⟩ := whnf_agree f s h
    refine ⟨?_, ?_⟩
    · simp only [Pure.whnf]
      refine bind_congr_ok is fun ws hws => ?_
      have hw := fs ws (is ▸ hws)
      have hargs : ∀ a ∈ (Erasure.spine ws).2, FVarsIn S a := spine_snd hw
      generalize Erasure.spine ws = p at hargs ⊢
      obtain ⟨hd, args⟩ := p
      simp only at hargs
      cases hd with
      | const c u =>
        simp only
        cases hfc : findConst cx.decls c with
        | none => rfl
        | some ci =>
          cases ci with
          | ctorInfo cv =>
            simp only
            cases ha : args[cv.numParams + i]? with
            | none => rfl
            | some a =>
              simp only
              exact (whnf_agree f a (hargs a (List.mem_of_getElem? ha))).1
          | _ => rfl
      | _ => rfl
    · intro w hw
      simp only [Pure.whnf] at hw
      obtain ⟨ws, h1, h2⟩ := OracleWhnf.ok_of_bind hw
      have hw' := fs ws h1
      have hargs : ∀ a ∈ (Erasure.spine ws).2, FVarsIn S a := spine_snd hw'
      generalize Erasure.spine ws = p at hargs h2
      obtain ⟨hd, args⟩ := p
      simp only at hargs
      have refl : (pure (Expr.proj S' i s) : Except EraseError Expr) = .ok w → FVarsIn S w :=
        fun h' => by cases h'; exact h
      cases hd with
      | const c u =>
        simp only at h2
        cases hfc : findConst cx.decls c with
        | none => rw [hfc] at h2; exact refl h2
        | some ci =>
          rw [hfc] at h2
          cases ci with
          | ctorInfo cv =>
            simp only at h2
            cases ha : args[cv.numParams + i]? with
            | none => rw [ha] at h2; exact refl h2
            | some a =>
              rw [ha] at h2
              exact (whnf_agree f a (hargs a (List.mem_of_getElem? ha))).2 w h2
          | _ => exact refl h2
      | _ => exact refl h2
  | f + 1, .bvar _, h | f + 1, .sort _, h | f + 1, .lam .., h | f + 1, .forallE .., h
  | f + 1, .lit _, h | f + 1, .mvar _, h =>
    ⟨rfl, fun w hw => by cases hw; exact h⟩


/-- Frame for `Erasure.Pure.instForalls`. -/
theorem instForalls_agree (f : Nat) : ∀ (r : Expr) (as : List Expr), FVarsIn S r →
    (∀ a ∈ as, FVarsIn S a) →
    Pure.instForalls cx f ls₁ r as = Pure.instForalls cx f ls₂ r as ∧
      ∀ w, Pure.instForalls cx f ls₁ r as = .ok w → FVarsIn S w
  | r, [], hr, _ => ⟨rfl, fun w h => by cases h; exact hr⟩
  | r, a :: as, hr, has => by
    have ⟨iw, fw⟩ := whnf_agree hcl hS hag f r hr
    have ha := has a (List.mem_cons_self ..)
    have has' : ∀ a ∈ as, FVarsIn S a := fun a h => has a (List.mem_cons_of_mem _ h)
    simp only [Pure.instForalls]
    refine bind_agree (fun w => FVarsIn S w) _ ⟨iw, fw⟩ fun w hw => ?_
    cases w with
    | forallE n t b bi =>
      exact instForalls_agree f _ as (fvarsIn_inst ha hw.2) has'
    | _ => exact ⟨rfl, fun _ h => absurd h throw_ne_ok⟩

/-- Frame for `Erasure.Pure.instProjs`. -/
theorem instProjs_agree (f : Nat) (S' : Name) {s : Expr} (hs : FVarsIn S s) :
    ∀ (k j : Nat) (r : Expr), FVarsIn S r →
      Pure.instProjs cx f ls₁ S' s k j r = Pure.instProjs cx f ls₂ S' s k j r ∧
        ∀ w, Pure.instProjs cx f ls₁ S' s k j r = .ok w → FVarsIn S w
  | 0, _, r, hr => ⟨rfl, fun w h => by cases h; exact hr⟩
  | k + 1, j, r, hr => by
    have ⟨iw, fw⟩ := whnf_agree hcl hS hag f r hr
    simp only [Pure.instProjs]
    refine bind_agree (fun w => FVarsIn S w) _ ⟨iw, fw⟩ fun w hw => ?_
    cases w with
    | forallE n t b bi =>
      exact instProjs_agree f S' hs k (j + 1) _
        (fvarsIn_inst (a := .proj S' j s) hs hw.2)
    | _ => exact ⟨rfl, fun _ h => absurd h throw_ne_ok⟩

/-- Frame for `Erasure.Pure.inferType`: on a term and binder types in `S`, the two local lists give
the same result, in `S`. -/
theorem inferType_agree : ∀ (f : Nat) (Γ : List Expr) (e : Expr), FVarsIn S e →
    (∀ A ∈ Γ, FVarsIn S A) →
    Pure.inferType cx f ls₁ Γ e = Pure.inferType cx f ls₂ Γ e ∧
      ∀ T, Pure.inferType cx f ls₁ Γ e = .ok T → FVarsIn S T
  | 0, _, e, _, _ => ⟨rfl, fun w h => absurd h throw_ne_ok⟩
  | f + 1, Γ, .bvar i, _, hΓ => by
    refine ⟨rfl, fun T hT => ?_⟩
    simp only [Pure.inferType] at hT
    split at hT
    · rename_i A hA
      cases hT
      exact fvarsIn_lift (hΓ A (List.mem_of_getElem? hA))
    · exact absurd hT throw_ne_ok
  | f + 1, Γ, .fvar x, h, _ => by
    have hx : S x := h
    simp only [Pure.inferType]
    rw [← hag x hx]
    refine ⟨rfl, fun T hT => ?_⟩
    split at hT
    · rename_i l hl; cases hT; exact (hS x hx l hl).1
    · exact absurd hT throw_ne_ok
  | f + 1, Γ, .sort u, h, _ => ⟨rfl, fun T hT => by
      simp only [Pure.inferType, pure, Except.pure, Except.ok.injEq] at hT
      subst hT; trivial⟩
  | f + 1, Γ, .lit (.natVal _), _, _ => ⟨rfl, fun T hT => by
      simp only [Pure.inferType, pure, Except.pure, Except.ok.injEq] at hT
      subst hT; trivial⟩
  | f + 1, Γ, .lit (.strVal _), _, _ => ⟨rfl, fun T hT => absurd hT throw_ne_ok⟩
  | f + 1, Γ, .const c us, h, _ => by
    refine ⟨rfl, fun T hT => ?_⟩
    simp only [Pure.inferType] at hT
    split at hT
    · rename_i ci hci
      split at hT
      · simp only [pure, Except.pure, Except.ok.injEq] at hT; subst hT
        exact fvarsIn_instLevels _ _
          (fvarsIn_false (hcl _ (List.mem_of_find?_eq_some hci) _ (.inl (.inl rfl))))
      · exact absurd hT throw_ne_ok
    · exact absurd hT throw_ne_ok
  | f + 1, Γ, .app g a, ⟨hg, ha⟩, hΓ => by
    simp only [Pure.inferType]
    refine bind_agree (fun T => FVarsIn S T) _ (inferType_agree f Γ g hg hΓ) fun Tg hTg => ?_
    refine bind_agree (fun w => FVarsIn S w) _
      (whnf_agree hcl hS hag f Tg hTg) fun w hw => ?_
    cases w with
    | forallE n t B bi =>
      exact ⟨rfl, fun T h => by cases h; exact fvarsIn_inst ha hw.2⟩
    | _ => exact ⟨rfl, fun _ h => absurd h throw_ne_ok⟩
  | f + 1, Γ, .lam n t b bi, ⟨ht, hb⟩, hΓ => by
    have hΓ' : ∀ A ∈ t :: Γ, FVarsIn S A := by
      intro A hA; simp only [List.mem_cons] at hA; rcases hA with rfl | hA
      exacts [ht, hΓ A hA]
    have ⟨ib, fb⟩ := inferType_agree f (t :: Γ) b hb hΓ'
    refine ⟨?_, ?_⟩
    · simp only [Pure.inferType]; rw [ib]
    · intro T hT
      simp only [Pure.inferType] at hT
      obtain ⟨B, h1, hT⟩ := OracleWhnf.ok_of_bind hT
      cases hT; exact ⟨ht, fb B h1⟩
  | f + 1, Γ, .forallE n t b bi, ⟨ht, hb⟩, hΓ => by
    have hΓ' : ∀ A ∈ t :: Γ, FVarsIn S A := by
      intro A hA; simp only [List.mem_cons] at hA; rcases hA with rfl | hA
      exacts [ht, hΓ A hA]
    simp only [Pure.inferType]
    refine bind_agree (fun T => FVarsIn S T) _ (inferType_agree f Γ t ht hΓ) fun Tt hTt => ?_
    refine bind_agree (fun _ => True) _ ⟨(whnf_agree hcl hS hag f Tt hTt).1, fun _ _ => trivial⟩
      fun w1 _ => ?_
    cases w1 with
    | sort u =>
      refine bind_agree (fun T => FVarsIn S T) _ (inferType_agree f (t :: Γ) b hb hΓ')
        fun Tb hTb => ?_
      refine bind_agree (fun _ => True) _ ⟨(whnf_agree hcl hS hag f Tb hTb).1, fun _ _ => trivial⟩
        fun w2 _ => ?_
      cases w2 with
      | sort v => exact ⟨rfl, fun T h => by cases h; trivial⟩
      | _ => exact ⟨rfl, fun _ h => absurd h throw_ne_ok⟩
    | _ => exact ⟨rfl, fun _ h => absurd h throw_ne_ok⟩
  | f + 1, Γ, .letE _ _ v b _, ⟨_, hv, hb⟩, hΓ => by
    simp only [Pure.inferType]
    exact inferType_agree f Γ _ (fvarsIn_inst hv hb) hΓ
  | f + 1, Γ, .mdata _ e, h, hΓ => by
    simp only [Pure.inferType]; exact inferType_agree f Γ e h hΓ
  | f + 1, Γ, .mvar _, _, _ => ⟨rfl, fun T hT => absurd hT throw_ne_ok⟩
  | f + 1, Γ, .proj S' i s, h, hΓ => by
    have hs : FVarsIn S s := h
    have thr : ∀ (e : EraseError), (throw e : Except EraseError Expr) = throw e ∧
        ∀ b, (throw e : Except EraseError Expr) = .ok b → FVarsIn S b :=
      fun e => ⟨rfl, fun b h => absurd h throw_ne_ok⟩
    -- every unreachable branch of the projection rule is a failure on both sides
    simp only [Pure.inferType]
    refine bind_agree (fun T => FVarsIn S T) _ (inferType_agree f Γ s h hΓ) fun T hT => ?_
    refine bind_agree (fun w => FVarsIn S w) _
      (whnf_agree hcl hS hag f T hT) fun ws hw => ?_
    have hargs : ∀ a ∈ (Erasure.spine ws).2, FVarsIn S a := spine_snd hw
    generalize Erasure.spine ws = p at hargs ⊢
    obtain ⟨hd, args⟩ := p
    simp only at hargs
    cases hd with
    | const S'' us =>
      simp only
      split
      · next I R hSS hfS hfR =>
        · split
          · exact ⟨rfl, fun _ h => nomatch h⟩
          split
          · next c hct hlen =>
            split
            · next ci cv hci =>
              split
              swap
              · exact ⟨rfl, fun _ h => nomatch h⟩
              refine bind_agree (fun r => FVarsIn S r) _
                (instForalls_agree hcl hS hag f _ _
                  (fvarsIn_instLevels _ _ (fvarsIn_false
                    (hcl _ (List.mem_of_find?_eq_some hci) _ (.inl (.inl rfl)))))
                  (fun a ha => hargs a (List.mem_of_mem_take ha))) fun r hr => ?_
              refine bind_agree (fun x => FVarsIn S x) _
                (instProjs_agree hcl hS hag f S' hs i 0 r hr) fun x hx => ?_
              refine bind_agree (fun w => FVarsIn S w) _
                (whnf_agree hcl hS hag f x hx) fun w hw' => ?_
              cases w with
              | forallE n d b bi =>
                exact ⟨rfl, fun _ h' => by cases h'; exact hw'.1⟩
              | _ => exact thr _
            · exact thr _
          · exact thr _
      · exact thr _
    | _ => exact thr _

/-- Frame for `Erasure.Pure.isArity`. -/
theorem isArity_agree : ∀ (f : Nat) (T : Expr), FVarsIn S T →
    Pure.isArity cx f ls₁ T = Pure.isArity cx f ls₂ T
  | 0, _, _ => rfl
  | f + 1, T, h => by
    simp only [Pure.isArity]
    have ⟨iw, fw⟩ := whnf_agree hcl hS hag f T h
    refine bind_congr_ok iw fun w hw => ?_
    cases w with
    | forallE n t B bi =>
      exact isArity_agree f B (show FVarsIn S (.forallE n t B bi) from fw _ (iw ▸ hw)).2
    | _ => rfl

end

end OracleAgree

open OracleAgree in
/-- The oracle reads the locals only on the term's free variables: over declarations whose read
expressions are closed, two lists of locals that agree on a set `S` containing the term's free
variables and closed under the first list's types and values give the same answer. Reference: none; MetaRocq erases a constant body in
the empty context (`MR E/ErasureFunction.v:1309 erase_constant_body`); DV-13; port of
`L4 Oracle/Agree.lean:283`. -/
theorem Pure.isErasable_agree {cx : Pure.Ctx} {fuel : Nat} {ls₁ ls₂ : List Local} {e : Expr}
    {S : FVarId → Prop} (hcl : ClosedDecls cx.decls)
    (hS : LocalsSupport S ls₁) (hag : LocalsAgree S ls₁ ls₂) (he : FVarsIn S e) :
    Pure.isErasable cx fuel ls₁ e = Pure.isErasable cx fuel ls₂ e := by
  unfold Pure.isErasable
  split
  · split
    · rfl
    · have ⟨iT, fT⟩ := inferType_agree hcl hS hag fuel [] e he (by simp)
      refine bind_congr_ok iT fun T hT => ?_
      have hT' := fT T (iT ▸ hT)
      refine bind_congr_ok (isArity_agree hcl hS hag fuel T hT') fun b _ => ?_
      split
      · rfl
      · have ⟨iS, fS⟩ := inferType_agree hcl hS hag fuel [] T hT' (by simp)
        refine bind_congr_ok iS fun S' hS' => ?_
        have ⟨iw, _⟩ := whnf_agree hcl hS hag fuel S' (fS S' (iS ▸ hS'))
        exact bind_congr_ok iw fun _ _ => rfl
  · dsimp only
    have ⟨iT, fT⟩ := inferType_agree hcl hS hag fuel [] e he (by simp)
    refine bind_congr_ok iT fun T hT => ?_
    have hT' := fT T (iT ▸ hT)
    refine bind_congr_ok (isArity_agree hcl hS hag fuel T hT') fun b _ => ?_
    split
    · rfl
    · have ⟨iS, fS⟩ := inferType_agree hcl hS hag fuel [] T hT' (by simp)
      refine bind_congr_ok iS fun S' hS' => ?_
      have ⟨iw, _⟩ := whnf_agree hcl hS hag fuel S' (fS S' (iS ▸ hS'))
      exact bind_congr_ok iw fun _ _ => rfl

end EraseProof
