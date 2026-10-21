import EraseProof.Target

/-!
# Determinism of λ□ evaluation

Test, off the path of the final theorem: `LBEval` is deterministic (`MR E/EWcbvEval.v:1375
eval_deterministic`). The non-vacuity instances use it to show that the final theorem's witness is
the one they exhibit.

The rules of `LBEval` that share a conclusion are told apart by the value of the subterm they
evaluate first, the function of an application or the discriminant of a case or projection: `□`,
a λ, a fixpoint, a fixpoint spine, a constructor spine, or none of these (`appCong`). The lemmas
this takes, on the head and the arguments of an application spine, are in namespace
`EraseProof.Test.LBEval`.
-/

namespace EraseProof.Test

namespace LBEval

/-- The arguments of an application spine, outermost last. Reference: `spine`
(`MR E/EAstUtils.v:19`). -/
def spineArgs : LBTerm → List LBTerm
  | .app f a => spineArgs f ++ [a]
  | _ => []

/-- The head of `mkApps f args` is the head of `f`. Reference: `head_mkApps`
(`MR E/EAstUtils.v:57`). -/
theorem headOf_mkApps : ∀ {f : LBTerm} {args : List LBTerm}, headOf (mkApps f args) = headOf f
  | _, [] => rfl
  | f, a :: as => headOf_mkApps (f := .app f a) (args := as)

/-- The arguments of `mkApps f args` are those of `f` followed by `args`. Reference:
`decompose_app_rec_mkApps` (`MR E/EAstUtils.v:27`). -/
theorem spineArgs_mkApps :
    ∀ {f : LBTerm} {args : List LBTerm}, spineArgs (mkApps f args) = spineArgs f ++ args
  | _, [] => (List.append_nil _).symm
  | f, a :: as => by
    rw [mkApps, spineArgs_mkApps (f := .app f a) (args := as), spineArgs, List.append_assoc,
      List.singleton_append]

/-- A spine whose head is not an application determines its head and its arguments. Reference:
`mkApps_eq_inj` (`MR E/EAstUtils.v:170`). -/
theorem mkApps_inj {f f' : LBTerm} {args args' : List LBTerm} (hf : headOf f = f)
    (hsf : spineArgs f = []) (hf' : headOf f' = f') (hsf' : spineArgs f' = [])
    (h : mkApps f args = mkApps f' args') : f = f' ∧ args = args' := by
  have h1 := congrArg headOf h
  have h2 := congrArg spineArgs h
  rw [headOf_mkApps, headOf_mkApps, hf, hf'] at h1
  rw [spineArgs_mkApps, spineArgs_mkApps, hsf, hsf', List.nil_append, List.nil_append] at h2
  exact ⟨h1, h2⟩

/-- Two fixpoint spines are equal only with the same fixpoint and arguments. -/
theorem mkApps_fix_inj (h : mkApps (.fix mfix idx) args = mkApps (.fix mfix' idx') args') :
    mfix = mfix' ∧ idx = idx' ∧ args = args' := by
  obtain ⟨h1, h2⟩ := mkApps_inj rfl rfl rfl rfl h
  cases h1
  exact ⟨rfl, rfl, h2⟩

/-- Two constructor spines are equal only with the same constructor and arguments. -/
theorem mkApps_construct_inj
    (h : mkApps (.construct ind c []) args = mkApps (.construct ind' c' []) args') :
    ind = ind' ∧ c = c' ∧ args = args' := by
  obtain ⟨h1, h2⟩ := mkApps_inj rfl rfl rfl rfl h
  cases h1
  exact ⟨rfl, rfl, h2⟩

/-- Two lists related pointwise to lists by a relation that is deterministic on each element are
equal. Reference: the `eval_construct_block` case of `eval_deterministic`
(`MR E/EWcbvEval.v:1375`). -/
theorem forall₂_det {R : LBTerm → LBTerm → Prop}
    (ih : List.Forall₂ (fun a a' => ∃ _ : R a a', ∀ {v}, R a v → a' = v) as as₁)
    (h : List.Forall₂ R as as₂) : as₁ = as₂ := by
  induction ih generalizing as₂ with
  | nil => cases h; rfl
  | cons hx _ ihs =>
    cases h with
    | cons hy hr =>
      obtain ⟨_, e⟩ := hx
      rw [e hy, ihs hr]

/-- A constructor applied to arguments is an atom only when its flags do not store arguments in
constructor blocks. Reference: `atom` (`MR E/EWcbvEval.v:36`), `tConstruct` case. -/
theorem lbAtom_construct (hb : fl.with_constructor_as_block = true) :
    lbAtom fl lenv (.construct ind c args) = false := by
  cases args <;> simp [lbAtom, hb]

end LBEval

/-- λ□ evaluation is deterministic; used by the non-vacuity instances to show that the final
theorem's witness is the one exhibited. Reference: `eval_deterministic`
(`MR E/EWcbvEval.v:1375`). -/
theorem LBEval.deterministic (h₁ : LBEval fl lenv t v₁) (h₂ : LBEval fl lenv t v₂) : v₁ = v₂ := by
  induction h₁ using EraseProof.LBEval.ind generalizing v₂ with
  | box _ _ ihf _ =>
    cases h₂ with
    | box => rfl
    | beta hf _ _ | fix _ hf _ _ _ | fixValue _ hf _ _ _ | fix' _ hf _ _ _
    | construct _ _ hf _ _ =>
      exact absurd (congrArg headOf (ihf hf)) (by simp [headOf_mkApps, headOf])
    | appCong hf hc _ => cases ihf hf; simp [isBoxT] at hc
    | atom h => simp [lbAtom] at h
  | beta _ _ _ ihf iha ihr =>
    cases h₂ with
    | beta hf ha hr => cases ihf hf; cases iha ha; exact ihr hr
    | box hf _ | fix _ hf _ _ _ | fixValue _ hf _ _ _ | fix' _ hf _ _ _
    | construct _ _ hf _ _ =>
      exact absurd (congrArg headOf (ihf hf)) (by simp [headOf_mkApps, headOf])
    | appCong hf hc _ => cases ihf hf; simp [isLambdaT] at hc
    | atom h => simp [lbAtom] at h
  | zeta _ _ ih1 ih2 =>
    cases h₂ with
    | zeta h1 h2 => cases ih1 h1; exact ih2 h2
    | atom h => simp [lbAtom] at h
  | iota hb _ hc hbr _ _ _ ihd ihr =>
    cases h₂ with
    | iota _ hd hc' hbr' _ _ hr =>
      obtain ⟨-, rfl, rfl⟩ := mkApps_construct_inj (ihd hd)
      rw [hc] at hc'
      cases hc'
      rw [hbr] at hbr'
      cases hbr'
      exact ihr hr
    | iotaBlock hb' _ _ _ _ _ _ => rw [hb] at hb'; cases hb'
    | iotaSing _ hd _ _ _ =>
      exact absurd (congrArg headOf (ihd hd)) (by simp [headOf_mkApps, headOf])
    | atom h => simp [lbAtom] at h
  | iotaBlock hb _ hc hbr _ _ _ ihd ihr =>
    cases h₂ with
    | iota hb' _ _ _ _ _ _ => rw [hb] at hb'; cases hb'
    | iotaBlock _ hd hc' hbr' _ _ hr =>
      cases ihd hd
      rw [hc] at hc'
      cases hc'
      rw [hbr] at hbr'
      cases hbr'
      exact ihr hr
    | iotaSing _ hd _ _ _ => cases ihd hd
    | atom h => simp [lbAtom] at h
  | iotaSing _ _ _ hbrs _ ihd ihr =>
    cases h₂ with
    | iota _ hd _ _ _ _ _ =>
      exact absurd (congrArg headOf (ihd hd)) (by simp [headOf_mkApps, headOf])
    | iotaBlock _ hd _ _ _ _ _ => cases ihd hd
    | iotaSing _ _ _ hbrs' hr =>
      rw [hbrs] at hbrs'
      cases hbrs'
      exact ihr hr
    | atom h => simp [lbAtom] at h
  | fix hg _ _ hu _ ihf iha ihr =>
    cases h₂ with
    | fix _ hf ha hu' hr =>
      obtain ⟨rfl, rfl, rfl⟩ := mkApps_fix_inj (ihf hf)
      cases iha ha
      rw [hu] at hu'
      cases hu'
      exact ihr hr
    | fixValue _ hf _ hu' hlt =>
      obtain ⟨rfl, rfl, rfl⟩ := mkApps_fix_inj (ihf hf)
      rw [hu] at hu'
      cases hu'
      exact absurd hlt (Nat.lt_irrefl _)
    | fix' hg' _ _ _ _ => rw [hg] at hg'; cases hg'
    | box hf _ | beta hf _ _ | construct _ _ hf _ _ =>
      exact absurd (congrArg headOf (ihf hf)) (by simp [headOf_mkApps, headOf])
    | appCong hf hc _ =>
      cases ihf hf
      simp [hg, isFixApp, headOf_mkApps, headOf, isFixT] at hc
    | atom h => simp [lbAtom] at h
  | fixValue hg _ _ hu hlt ihf iha =>
    cases h₂ with
    | fix _ hf _ hu' _ =>
      obtain ⟨rfl, rfl, rfl⟩ := mkApps_fix_inj (ihf hf)
      rw [hu] at hu'
      cases hu'
      exact absurd hlt (Nat.lt_irrefl _)
    | fixValue _ hf ha _ _ => rw [ihf hf, iha ha]
    | fix' hg' _ _ _ _ => rw [hg] at hg'; cases hg'
    | box hf _ | beta hf _ _ | construct _ _ hf _ _ =>
      exact absurd (congrArg headOf (ihf hf)) (by simp [headOf_mkApps, headOf])
    | appCong hf hc _ =>
      cases ihf hf
      simp [hg, isFixApp, headOf_mkApps, headOf, isFixT] at hc
    | atom h => simp [lbAtom] at h
  | fix' hg _ hu _ _ ihf iha ihr =>
    cases h₂ with
    | fix' _ hf hu' ha hr =>
      cases ihf hf
      cases iha ha
      rw [hu] at hu'
      cases hu'
      exact ihr hr
    | fix hg' _ _ _ _ | fixValue hg' _ _ _ _ => rw [hg] at hg'; cases hg'
    | box hf _ | beta hf _ _ | construct _ _ hf _ _ =>
      exact absurd (congrArg headOf (ihf hf)) (by simp [headOf_mkApps, headOf])
    | appCong hf hc _ =>
      cases ihf hf
      simp [hg, isFixT] at hc
    | atom h => simp [lbAtom] at h
  | delta hc hb _ ihr =>
    cases h₂ with
    | delta hc' hb' hr =>
      rw [hc] at hc'
      cases hc'
      rw [hb] at hb'
      cases hb'
      exact ihr hr
    | atom h => simp [lbAtom] at h
  | proj hb _ _ _ hget _ ihd ihr =>
    cases h₂ with
    | proj _ hd _ _ hget' hr =>
      obtain ⟨-, -, rfl⟩ := mkApps_construct_inj (ihd hd)
      rw [hget] at hget'
      cases hget'
      exact ihr hr
    | projBlock hb' _ _ _ _ _ => rw [hb] at hb'; cases hb'
    | projProp _ hd _ =>
      exact absurd (congrArg headOf (ihd hd)) (by simp [headOf_mkApps, headOf])
    | atom h => simp [lbAtom] at h
  | projBlock hb _ _ _ hget _ ihd ihr =>
    cases h₂ with
    | proj hb' _ _ _ _ _ => rw [hb] at hb'; cases hb'
    | projBlock _ hd _ _ hget' hr =>
      cases ihd hd
      rw [hget] at hget'
      cases hget'
      exact ihr hr
    | projProp _ hd _ => cases ihd hd
    | atom h => simp [lbAtom] at h
  | projProp _ _ _ ihd =>
    cases h₂ with
    | proj _ hd _ _ _ _ =>
      exact absurd (congrArg headOf (ihd hd)) (by simp [headOf_mkApps, headOf])
    | projBlock _ hd _ _ _ _ => cases ihd hd
    | projProp => rfl
    | atom h => simp [lbAtom] at h
  | construct _ _ _ _ _ ihf iha =>
    cases h₂ with
    | construct _ _ hf _ ha => rw [ihf hf, iha ha]
    | box hf _ | beta hf _ _ | fix _ hf _ _ _ | fixValue _ hf _ _ _ | fix' _ hf _ _ _ =>
      exact absurd (congrArg headOf (ihf hf)) (by simp [headOf_mkApps, headOf])
    | appCong hf hc _ =>
      cases ihf hf
      simp [isConstructApp, headOf_mkApps, headOf] at hc
    | atom h => simp [lbAtom] at h
  | constructBlock hb _ _ _ ih =>
    cases h₂ with
    | constructBlock _ _ _ h => rw [forall₂_det ih h]
    | atom h => rw [lbAtom_construct hb] at h; cases h
  | appCong _ hc _ ihf iha =>
    cases h₂ with
    | appCong hf _ ha => rw [ihf hf, iha ha]
    | box hf _ => cases ihf hf; simp [isBoxT] at hc
    | beta hf _ _ => cases ihf hf; simp [isLambdaT] at hc
    | fix hg hf _ _ _ | fixValue hg hf _ _ _ =>
      cases ihf hf
      simp [hg, isFixApp, headOf_mkApps, headOf, isFixT] at hc
    | fix' hg hf _ _ _ =>
      cases ihf hf
      simp [hg, isFixT] at hc
    | construct _ _ hf _ _ =>
      cases ihf hf
      simp [isConstructApp, headOf_mkApps, headOf] at hc
    | atom h => simp [lbAtom] at h
  | prim =>
    cases h₂ with
    | prim => rfl
    | atom h => simp [lbAtom] at h
  | atom h =>
    cases h₂ with
    | atom => rfl
    | constructBlock hb _ _ _ => rw [lbAtom_construct hb] at h; cases h
    | _ => simp [lbAtom] at h

end EraseProof.Test
