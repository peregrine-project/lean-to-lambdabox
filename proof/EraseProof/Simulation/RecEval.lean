import EraseProof.Relation.Rec
import EraseProof.Relation.Deps

/-!
# λ□ evaluation facts for a recursor's erasure

Evaluation results are λ□ values, which evaluate to themselves only, in every environment
(`RecEval.LBEval.fixed`); a chain of `let`s of closed terms evaluates as the body with the values
substituted (`RecEval.eval_letChain`); an application spine whose head evaluates like another
term's head evaluates like the other spine (`RecEval.eval_mkApps_head`), so that λs applied to `□`
reduce to their body with `□` substituted (`RecEval.eval_lams_boxes`). Reference:
`MR E/EWcbvEval.v` (`value_final`, `eval_deterministic`, `eval_zeta`, `eval_beta`).
-/

open Lean Erasure

namespace EraseProof

namespace RecEval

open TargetSubst TargetLift

variable {lenv : GlobalDeclarations}

/-- Appending an argument to a λ□ spine. -/
theorem mkApps_snoc : ∀ (t : LBTerm) (l : List LBTerm) (x : LBTerm),
    mkApps t (l ++ [x]) = .app (mkApps t l) x
  | _, [], _ => rfl
  | t, a :: l, x => mkApps_snoc (.app t a) l x

theorem mkApps_append : ∀ (t : LBTerm) (l l' : List LBTerm), mkApps t (l ++ l') = mkApps (mkApps t l) l'
  | _, [], _ => rfl
  | t, a :: l, l' => mkApps_append (.app t a) l l'

/-- The arguments of an application spine. -/
def lbArgs : LBTerm → List LBTerm
  | .app f a => lbArgs f ++ [a]
  | _ => []

theorem lbArgs_mkApps : ∀ (f : LBTerm) (as : List LBTerm), lbArgs (mkApps f as) = lbArgs f ++ as
  | _, [] => by simp [mkApps]
  | f, a :: as => by rw [mkApps, lbArgs_mkApps]; simp [lbArgs]

/-- Spines with a non-application head are equal only with the same head and arguments. -/
theorem mkApps_inj {h h' : LBTerm} {as as' : List LBTerm} (hh : lbArgs h = []) (hh' : lbArgs h' = [])
    (hn : ∀ f a, h ≠ .app f a) (hn' : ∀ f a, h' ≠ .app f a)
    (e : mkApps h as = mkApps h' as') : h = h' ∧ as = as' := by
  have e1 := congrArg headOf e
  have e2 := congrArg lbArgs e
  rw [headOf_mkApps, headOf_mkApps] at e1
  rw [lbArgs_mkApps, lbArgs_mkApps, hh, hh'] at e2
  refine ⟨?_, by simpa using e2⟩
  cases h <;> cases h' <;> simp_all [headOf]

/-- `□` evaluates to itself only. -/
theorem box_only {t' : LBTerm} (h : LBEval defaultFlags lenv .box t') : t' = .box := by
  cases h; rfl

/-- An application of a value head that is no λ, no `□` and no unfoldable fixpoint spine to a
value evaluates to itself only. -/
theorem app_fixed {f a t' : LBTerm} (hf : LBFixed f) (ha : LBFixed a)
    (h : LBEval defaultFlags lenv (.app f a) t') (hnl : isLambdaT f = false) (hnb : f ≠ .box)
    (hfix : ∀ m i (args : List LBTerm) fn, f = mkApps (.fix m i) args →
      cunfoldFix m i ≠ some (args.length, fn)) :
    t' = .app f a := by
  cases h with
  | box h₁ => exact absurd (hf _ _ h₁).symm hnb
  | beta h₁ => rw [← hf _ _ h₁] at hnl; cases hnl
  | fix _ h₁ _ h₄ => exact absurd h₄ (hfix _ _ _ _ (hf _ _ h₁).symm)
  | fixValue _ h₁ h₂ => rw [hf _ _ h₁, ha _ _ h₂]
  | fix' h₁ => cases h₁
  | construct _ _ h₁ _ h₂ => rw [hf _ _ h₁, ha _ _ h₂]
  | appCong h₁ _ h₂ => rw [hf _ _ h₁, ha _ _ h₂]
  | atom ha => simp [lbAtom] at ha

/-- Evaluation results are λ□ values: they evaluate to themselves only, in every environment.
Reference: `eval_to_value`, `value_final` and `eval_deterministic` (`MR E/EWcbvEval.v`). -/
theorem LBEval.fixed {s t : LBTerm} (hev : LBEval defaultFlags lenv s t) : LBFixed t := by
  induction hev using LBEval.ind with
  | box => exact fun _ _ h => box_only h
  | beta _ _ _ _ _ ih => exact ih
  | zeta _ _ _ ih => exact ih
  | iota _ _ _ _ _ _ _ _ ih => exact ih
  | iotaBlock h => cases h
  | iotaSing _ _ _ _ _ _ ih => exact ih
  | fix _ _ _ _ _ _ _ ih => exact ih
  | @fixValue f mfix idx argsv a av narg fn _ _ _ h₄ h₅ ihf iha =>
    intro lenv' t' h
    refine app_fixed ihf iha h ?_ ?_ ?_
    · cases argsv using List.reverseRecOn with
      | nil => rfl
      | append_singleton l x _ => rw [mkApps_snoc]; rfl
    · cases argsv using List.reverseRecOn with
      | nil => intro h; cases h
      | append_singleton l x _ => rw [mkApps_snoc]; intro h; cases h
    · intro m i args fn' he hun
      obtain ⟨h1, rfl⟩ := mkApps_inj rfl rfl (fun _ _ h => by cases h) (fun _ _ h => by cases h) he
      cases h1
      rw [h₄] at hun
      cases hun
      omega
  | fix' h => cases h
  | delta _ _ _ ih => exact ih
  | proj _ _ _ _ _ _ _ ih => exact ih
  | projBlock h => cases h
  | projProp => exact fun _ _ h => box_only h
  | @construct ind c _ _ _ f args a a' _ _ _ _ _ ihf iha =>
    intro lenv' t' h
    refine app_fixed ihf iha h ?_ ?_ ?_
    · cases args using List.reverseRecOn with
      | nil => rfl
      | append_singleton l x _ => rw [mkApps_snoc]; rfl
    · cases args using List.reverseRecOn with
      | nil => intro h; cases h
      | append_singleton l x _ => rw [mkApps_snoc]; intro h; cases h
    · intro m i args' fn' he
      have := congrArg headOf he
      rw [headOf_mkApps, headOf_mkApps] at this
      cases this
  | constructBlock h => cases h
  | @appCong f f' a a' _ h₂ _ ihf iha =>
    intro lenv' t' h
    simp only [defaultFlags, ↓reduceIte, Bool.or_eq_false_iff] at h₂
    obtain ⟨⟨⟨⟨hl, hfx⟩, hb⟩, -⟩, -⟩ := h₂
    refine app_fixed ihf iha h hl (fun h => by subst h; simp [isBoxT] at hb) ?_
    intro m i args fn he
    subst he
    simp [isFixApp, headOf_mkApps, headOf, isFixT] at hfx
  | prim => intro _ _ h; cases h with | prim => rfl | atom => rfl
  | atom ha =>
    rename_i t
    intro lenv' t' h
    cases t with
    | box => exact box_only h
    | lambda => cases h; rfl
    | fix => cases h; rfl
    | construct ind c args =>
      cases h with
      | atom => rfl
      | constructBlock h₁ => cases h₁
    | _ => simp [lbAtom] at ha

/-- A `let` chain of closed values. -/
def letChain (ms : List (LBTerm × RecMinor)) (b : LBTerm) : LBTerm :=
  ms.foldr (fun p b => .letIn (binderNameOf p.2.name) p.1 b) b

/-- A closed substitution passes the closed values of a `let` chain. -/
theorem csubst_letChain {u : LBTerm} : ∀ (ms : List (LBTerm × RecMinor)) (j : Nat) (b : LBTerm),
    (∀ p ∈ ms, closedn 0 p.1 = true) →
      csubst u j (letChain ms b) = letChain ms (csubst u (j + ms.length) b)
  | [], j, b, _ => rfl
  | (m, mi) :: ms, j, b, h => by
    show LBTerm.letIn _ (csubst u j m) (csubst u (j + 1) (letChain ms b)) = _
    rw [csubst_closedn u m 0 j (h _ (.head _)) (Nat.zero_le _),
      csubst_letChain ms (j + 1) b (fun p hp => h p (.tail _ hp))]
    simp only [List.length_cons, Nat.add_assoc, Nat.add_comm 1]
    rfl

/-- A `let` chain of closed terms evaluates as its body with the values substituted. -/
theorem eval_letChain : ∀ (ms : List (LBTerm × RecMinor)) (ws : List LBTerm) (b r : LBTerm),
    ms.length = ws.length →
    (∀ (i : Nat) p w, ms[i]? = some p → ws[i]? = some w → LBEval defaultFlags lenv p.1 w) →
    (∀ p ∈ ms, closedn 0 p.1 = true) → (∀ w ∈ ws, closedn 0 w = true) →
    LBEval defaultFlags lenv (substl ws.reverse b) r →
    LBEval defaultFlags lenv (letChain ms b) r
  | [], [], b, r, _, _, _, _, h => h
  | [], _ :: _, _, _, hl, _, _, _, _ => by simp at hl
  | _ :: _, [], _, _, hl, _, _, _, _ => by simp at hl
  | (m, mi) :: ms, w :: ws, b, r, hl, hev, hm, hw, h => by
    refine .zeta (hev 0 _ _ rfl rfl) ?_
    show LBEval defaultFlags lenv (csubst w 0 (letChain ms b)) r
    rw [csubst_letChain ms 0 b (fun p hp => hm p (.tail _ hp))]
    refine eval_letChain ms ws _ r (by simpa using hl) (fun i p w h1 h2 => hev (i + 1) p w h1 h2)
      (fun p hp => hm p (.tail _ hp)) (fun w' hw' => hw w' (.tail _ hw')) ?_
    have hl' : ms.length = ws.length := by simpa using hl
    rw [Nat.zero_add, hl', ← List.length_reverse (as := ws),
      ← csubst_substl (hw w (.head _)) ws.reverse b
        fun g hg => hw g (.tail _ (List.mem_reverse.1 hg))]
    have : substl (w :: ws).reverse b = csubst w 0 (substl ws.reverse b) := by
      rw [List.reverse_cons, substl, List.foldl_append]; rfl
    rwa [← this]

/-- An application spine whose head evaluates at least like another term evaluates at least like the
spine of that term. -/
theorem eval_mkApps_head {X Y : LBTerm}
    (hXY : ∀ f', LBEval defaultFlags lenv X f' → LBEval defaultFlags lenv Y f') :
    ∀ (rest : List LBTerm) (r : LBTerm), LBEval defaultFlags lenv (mkApps X rest) r →
      LBEval defaultFlags lenv (mkApps Y rest) r := by
  intro rest
  induction rest using List.reverseRecOn with
  | nil => exact hXY
  | append_singleton rest y ih =>
    intro r h
    rw [mkApps_snoc] at h ⊢
    cases h with
    | box h₁ h₂ => exact .box (ih _ h₁) h₂
    | beta h₁ h₂ h₃ => exact .beta (ih _ h₁) h₂ h₃
    | fix h₀ h₁ h₂ h₃ h₄ => exact .fix h₀ (ih _ h₁) h₂ h₃ h₄
    | fixValue h₀ h₁ h₂ h₃ h₄ => exact .fixValue h₀ (ih _ h₁) h₂ h₃ h₄
    | fix' h₀ => cases h₀
    | construct h₀ h₁ h₂ h₃ h₄ => exact .construct h₀ h₁ (ih _ h₂) h₃ h₄
    | appCong h₁ h₂ h₃ => exact .appCong (ih _ h₁) h₂ h₃
    | atom ha => simp [lbAtom] at ha

/-- `mkApps` is a left fold of applications. -/
theorem foldl_app_eq_mkApps : ∀ (as : List LBTerm) (f : LBTerm), as.foldl .app f = mkApps f as
  | [], _ => rfl
  | a :: as, f => foldl_app_eq_mkApps as (.app f a)

/-- λs applied to `□`, one per λ, evaluate as the body with `□` substituted. -/
theorem eval_lams_boxes : ∀ (xs : List BinderName) (b r : LBTerm),
    LBEval defaultFlags lenv (substl (List.replicate xs.length .box) b) r →
    LBEval defaultFlags lenv (mkApps (xs.foldr .lambda b) (List.replicate xs.length .box)) r
  | [], b, r, h => h
  | x :: xs, b, r, h => by
    show LBEval defaultFlags lenv (mkApps (.app (.lambda x (xs.foldr .lambda b)) .box)
      (List.replicate xs.length .box)) r
    refine eval_mkApps_head (X := csubst .box 0 (xs.foldr .lambda b)) (fun f' hf' =>
      .beta (.atom rfl) (.atom rfl) hf') _ _ ?_
    have hcl : ∀ (ys : List BinderName) (j : Nat) (b : LBTerm),
        csubst .box j (ys.foldr .lambda b) = ys.foldr .lambda (csubst .box (j + ys.length) b) := by
      intro ys
      induction ys with
      | nil => intro j b; rfl
      | cons y ys ih =>
        intro j b
        show LBTerm.lambda y (csubst .box (j + 1) (ys.foldr .lambda b)) = _
        rw [ih]
        simp only [List.length_cons, List.foldr_cons, Nat.add_assoc, Nat.add_comm 1]
    rw [hcl xs 0 b, Nat.zero_add]
    refine eval_lams_boxes xs _ r ?_
    have hb : ∀ g ∈ List.replicate xs.length LBTerm.box, closedn 0 g = true := fun g hg => by
      rw [List.eq_of_mem_replicate hg]; rfl
    have : substl (List.replicate (xs.length + 1) .box) b =
        substl (List.replicate xs.length .box) (csubst .box xs.length b) := by
      rw [List.replicate_succ', substl, List.foldl_append]
      show csubst .box 0 (substl (List.replicate xs.length .box) b) = _
      rw [csubst_substl rfl _ b hb, List.length_replicate]
    rw [← this]
    simpa using h

/-- Evaluation results evaluate to themselves. Reference: `value_final` (`MR E/EWcbvEval.v`). -/
theorem LBEval.self {s t : LBTerm} (hev : LBEval defaultFlags lenv s t) :
    LBEval defaultFlags lenv t t := by
  induction hev using LBEval.ind with
  | box => exact .atom rfl
  | beta _ _ _ _ _ ih => exact ih
  | zeta _ _ _ ih => exact ih
  | iota _ _ _ _ _ _ _ _ ih => exact ih
  | iotaBlock h => cases h
  | iotaSing _ _ _ _ _ _ ih => exact ih
  | fix _ _ _ _ _ _ _ ih => exact ih
  | fixValue h₁ _ _ h₄ h₅ ihf iha => exact .fixValue h₁ ihf iha h₄ h₅
  | fix' h => cases h
  | delta _ _ _ ih => exact ih
  | proj _ _ _ _ _ _ _ ih => exact ih
  | projBlock h => cases h
  | projProp => exact .atom rfl
  | construct h₁ h₂ _ h₄ _ ihf iha => exact .construct h₁ h₂ ihf h₄ iha
  | constructBlock h => cases h
  | appCong _ h₂ _ ihf iha => exact .appCong ihf h₂ iha
  | prim => exact .prim
  | atom h => exact .atom h

/-- The arguments of a λ□ constructor value evaluate to themselves. -/
theorem construct_args_self {s t : LBTerm} (hev : LBEval defaultFlags lenv s t) :
    ∀ {i : InductiveId} {c : Nat} {args : List LBTerm}, t = mkApps (.construct i c []) args →
      ∀ a ∈ args, LBEval defaultFlags lenv a a := by
  induction hev using LBEval.ind with
  | box => intro i c args h; cases args using List.reverseRecOn with
    | nil => cases h
    | append_singleton l x _ => rw [mkApps_snoc] at h; cases h
  | beta _ _ _ _ _ ih => exact ih
  | zeta _ _ _ ih => exact ih
  | iota _ _ _ _ _ _ _ _ ih => exact ih
  | iotaBlock h => cases h
  | iotaSing _ _ _ _ _ _ ih => exact ih
  | fix _ _ _ _ _ _ _ ih => exact ih
  | fixValue =>
    intro i c args h
    have := congrArg headOf h
    simp only [headOf, headOf_mkApps] at this
    cases this
  | fix' h => cases h
  | delta _ _ _ ih => exact ih
  | proj _ _ _ _ _ _ _ ih => exact ih
  | projBlock h => cases h
  | projProp => intro i c args h; cases args using List.reverseRecOn with
    | nil => cases h
    | append_singleton l x _ => rw [mkApps_snoc] at h; cases h
  | @construct ind c' _ _ _ f args₀ a a' _ _ _ _ h₅ ihf _ =>
    intro i c args h
    cases args using List.reverseRecOn with
    | nil => cases h
    | append_singleton l x _ =>
      rw [mkApps_snoc] at h
      injection h with h1 h2
      subst h2
      intro b hb
      rcases List.mem_append.1 hb with hb | hb
      · exact ihf h1 b hb
      · rw [List.mem_singleton.1 hb]; exact LBEval.self h₅
  | constructBlock h => cases h
  | @appCong f f' a a' _ h₂ _ _ _ =>
    intro i c args h
    cases args using List.reverseRecOn with
    | nil => cases h
    | append_singleton l x _ =>
      rw [mkApps_snoc] at h
      injection h with h1 h2
      subst h1
      simp [isConstructApp, headOf_mkApps, headOf] at h₂
  | prim => intro i c args h; cases args using List.reverseRecOn with
    | nil => cases h
    | append_singleton l x _ => rw [mkApps_snoc] at h; cases h
  | atom ha =>
    intro i c args h
    cases args using List.reverseRecOn with
    | nil => simp
    | append_singleton l x _ =>
      rw [mkApps_snoc] at h; subst h; simp [lbAtom] at ha

/-- An argument may be replaced by a term that evaluates to it, if it is a value. -/
theorem eval_app_arg {G a av r : LBTerm} (h : LBEval defaultFlags lenv (.app G av) r)
    (ha : LBEval defaultFlags lenv a av) (hf : LBFixed av) :
    LBEval defaultFlags lenv (.app G a) r := by
  cases h with
  | box h₁ h₂ => obtain rfl := hf _ _ h₂; exact .box h₁ ha
  | beta h₁ h₂ h₃ => obtain rfl := hf _ _ h₂; exact .beta h₁ ha h₃
  | fix h₀ h₁ h₂ h₃ h₄ => obtain rfl := hf _ _ h₂; exact .fix h₀ h₁ ha h₃ h₄
  | fixValue h₀ h₁ h₂ h₃ h₄ => obtain rfl := hf _ _ h₂; exact .fixValue h₀ h₁ ha h₃ h₄
  | fix' h₀ => cases h₀
  | construct h₀ h₁ h₂ h₃ h₄ => obtain rfl := hf _ _ h₄; exact .construct h₀ h₁ h₂ h₃ ha
  | appCong h₁ h₂ h₃ => obtain rfl := hf _ _ h₃; exact .appCong h₁ h₂ ha
  | atom h => simp [lbAtom] at h

/-- Arguments of a spine may be replaced by terms that evaluate to them, if they are values. -/
theorem eval_args_replace {H : LBTerm} :
    ∀ {bs cs : List LBTerm}, List.Forall₂ (fun b c => LBEval defaultFlags lenv b c ∧ LBFixed c) bs cs →
      ∀ (pre : List LBTerm) (r : LBTerm), LBEval defaultFlags lenv (mkApps H (pre ++ cs)) r →
        LBEval defaultFlags lenv (mkApps H (pre ++ bs)) r := by
  intro bs cs h
  induction h with
  | nil => exact fun _ _ h => h
  | @cons b c bs cs hbc _ ih =>
    intro pre r hr
    have h1 := ih (pre ++ [c]) r (by simpa using hr)
    rw [show pre ++ [c] ++ bs = (pre ++ [c]) ++ bs from rfl, mkApps_append, mkApps_snoc] at h1
    rw [show pre ++ b :: bs = (pre ++ [b]) ++ bs by simp, mkApps_append, mkApps_snoc]
    exact eval_mkApps_head (fun f' hf' => eval_app_arg hf' hbc.1 hbc.2) bs r h1

end RecEval

end EraseProof
