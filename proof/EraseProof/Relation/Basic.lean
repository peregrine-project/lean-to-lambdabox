import EraseProof.Spec
import EraseProof.Bridge.Basic
import EraseProof.TargetFacts

/-!
# Basic properties of the erasure relation

The erasure of a translated term has no loose index beyond the context's bound locals
(`Erases.closed`); an erasure of a saturated constructor spine is `□` or a λ□ constructor applied
to erasures of the arguments (`Erases.ctor_inv`), and `□` for an inductive in `Prop`
(`Erases.ctorProp_box`); an erasure of a `PropProj` spine that is a λ□ evaluation result is `□`
(`Erases.propProj_box`).
-/

open Lean Erasure

namespace EraseProof

/-! ## Application spines -/

/-- The head of a left fold of applications is the head of its start. -/
private theorem getAppFn_foldl (f : Expr) : ∀ as : List Expr, (as.foldl .app f).getAppFn = f.getAppFn
  | [] => rfl
  | a :: as => by rw [List.foldl_cons, getAppFn_foldl _ as]; rfl

/-- The arguments of an application spine, outermost last. -/
private def appArgs : Expr → List Expr
  | .app f a => appArgs f ++ [a]
  | _ => []

private theorem appArgs_foldl (f : Expr) : ∀ as : List Expr, appArgs (as.foldl .app f) = appArgs f ++ as
  | [] => (List.append_nil _).symm
  | a :: as => by
    rw [List.foldl_cons, appArgs_foldl _ as, appArgs, List.append_assoc, List.singleton_append]

/-- The head of a constant spine is the constant. -/
private theorem getAppFn_mkAppN_const (c : Name) (us : List Level) (as : List Expr) :
    (mkAppN (.const c us) as.toArray).getAppFn = .const c us := by
  rw [mkAppN_toArray, getAppFn_foldl]; rfl

/-- Constant spines are equal only with the same constant, levels and arguments. -/
private theorem mkAppN_const_inj {c c' : Name} {us us' : List Level} {as as' : List Expr}
    (h : mkAppN (.const c us) as.toArray = mkAppN (.const c' us') as'.toArray) :
    c = c' ∧ us = us' ∧ as = as' := by
  have h1 := congrArg Expr.getAppFn h
  have h2 := congrArg appArgs h
  rw [getAppFn_mkAppN_const, getAppFn_mkAppN_const] at h1
  rw [mkAppN_toArray, mkAppN_toArray, appArgs_foldl, appArgs_foldl] at h2
  cases h1
  exact ⟨rfl, rfl, by simpa [appArgs] using h2⟩

/-! ## Facts about the evaluation environment -/

/-- A recognized `casesOn` constant is a definition. -/
private theorem casesOn?_defn {σ : EvalEnv} {c : Name} {iv : InductiveVal}
    (h : σ.casesOn? c = some iv) : ∃ d, findDecl σ.decls c = some (.defnInfo d) := by
  unfold EvalEnv.casesOn? at h
  split at h
  · rename_i ci hci
    unfold casesInfo? at hci
    split at hci
    · split at hci
      · rename_i d _ _ hd _ _
        exact ⟨d, hd⟩
      · cases hci
    · cases hci
  · cases h

/-- A constant with an arity of a constructor or recognized `casesOn` is one. -/
private theorem specialArity_some {σ : EvalEnv} {c : Name} {ar : Nat} (h : specialArity σ c = some ar) :
    (∃ cv, findDecl σ.decls c = some (.ctorInfo cv)) ∨ ∃ iv, σ.casesOn? c = some iv := by
  unfold specialArity at h
  split at h
  · exact .inl ⟨_, by assumption⟩
  · obtain ⟨iv, hiv, -⟩ := Option.map_eq_some_iff.1 h
    exact .inr ⟨iv, hiv⟩

/-- Only constructor and recognized `casesOn` spines are η-expanded. -/
private theorem etaSpine?_some {σ : EvalEnv} {c : Name} {us : List Level} {as : List Expr} {e' : Expr}
    (h : σ.etaSpine? c us as = some e') :
    ∃ ar, specialArity σ c = some ar ∧ as.length < ar := by
  unfold EvalEnv.etaSpine? at h
  split at h
  · rename_i ar _ har
    split at h
    · exact ⟨ar, har, by assumption⟩
    · cases h
  · cases h

/-- A constant spine of a constructor or recognized `casesOn` is special. -/
private theorem specialSpine_of {σ : EvalEnv} {c : Name} {us : List Level} {e : Expr}
    (he : e.getAppFn = .const c us)
    (h : (∃ cv, findDecl σ.decls c = some (.ctorInfo cv)) ∨ ∃ iv, σ.casesOn? c = some iv) :
    SpecialSpine σ e := by
  refine ⟨c, us, he, ?_⟩
  rcases h with h | ⟨iv, hiv⟩
  · exact .inl h
  · exact .inr (by rw [hiv]; rfl)

/-- A constructor's arity is its number of parameters and fields. -/
private theorem specialArity_ctor {σ : EvalEnv} {c : Name} {cv : ConstructorVal}
    (hc : findDecl σ.decls c = some (.ctorInfo cv)) :
    specialArity σ c = some (cv.numParams + cv.numFields) := by
  unfold specialArity; rw [hc]

/-- An atom constant is neither a constructor nor a recognized `casesOn`. -/
private theorem isAtom_not_special {σ : EvalEnv} {c : Name} (h : σ.isAtom c = true) :
    ¬ ((∃ cv, findDecl σ.decls c = some (.ctorInfo cv)) ∨ ∃ iv, σ.casesOn? c = some iv) := by
  unfold EvalEnv.isAtom at h
  rintro (⟨cv, hc⟩ | ⟨iv, hiv⟩)
  · rw [hc] at h
    simp [OwnRules] at h
  · split at h
    · rw [hiv] at h
      simp at h
    · cases h

/-- The head of an atom spine is an atom constant. -/
private theorem AtomSpine.head {σ : EvalEnv} {e : Expr} (h : AtomSpine σ e) :
    ∃ c us, e.getAppFn = .const c us ∧ σ.isAtom c = true := by
  induction h with
  | const ha => exact ⟨_, _, rfl, ha⟩
  | app _ ih => exact ih

/-- The head of a non-application is itself. -/
private theorem getAppFn_ne_const {e : Expr} {c : Name} {us : List Level}
    (he : ∀ f a, e ≠ .app f a) (hc : ∀ c' us', e ≠ .const c' us') : e.getAppFn ≠ .const c us := by
  cases e with
  | app f a => exact absurd rfl (he f a)
  | const c' us' => exact absurd rfl (hc c' us')
  | _ => intro h; cases h

/-! ## Closedness -/

/-- Every loose bound variable outside binder domains and Π-types is below `k`: the parts of a
term that its erasure keeps. -/
private def BBound : Nat → Expr → Prop
  | k, .bvar i => i < k
  | k, .app f a => BBound k f ∧ BBound k a
  | k, .lam _ _ b _ => BBound (k + 1) b
  | k, .letE _ _ v b _ => BBound k v ∧ BBound (k + 1) b
  | k, .mdata _ e => BBound k e
  | k, .proj _ _ e => BBound k e
  | _, _ => True

private theorem BBound_foldl {k : Nat} : ∀ {f : Expr} {as : List Expr},
    BBound k (as.foldl .app f) ↔ BBound k f ∧ ∀ a ∈ as, BBound k a
  | _, [] => by simp
  | f, a :: as => by
    rw [List.foldl_cons, BBound_foldl]
    simp only [BBound, List.mem_cons, forall_eq_or_imp, and_assoc]

private theorem BBound_mkAppN {k : Nat} {f : Expr} {as : List Expr} :
    BBound k (mkAppN f as.toArray) ↔ BBound k f ∧ ∀ a ∈ as, BBound k a := by
  rw [mkAppN_toArray, BBound_foldl]

private theorem BBound_lift {e : Expr} : ∀ {k s d : Nat}, BBound k e →
    BBound (k + d) (e.liftLooseBVars' s d) := by
  induction e with
  | bvar i =>
    intro k s d h
    simp only [BBound, Expr.liftLooseBVars'] at h ⊢
    split <;> omega
  | app f a ihf iha => intro k s d h; exact ⟨ihf h.1, iha h.2⟩
  | lam _ _ b _ _ ihb =>
    intro k s d h
    have := ihb (k := k + 1) (s := s + 1) (d := d) h
    simp only [BBound, Expr.liftLooseBVars']
    rwa [Nat.add_right_comm] at this
  | letE _ _ v b _ _ ihv ihb =>
    intro k s d h
    have := ihb (k := k + 1) (s := s + 1) (d := d) h.2
    simp only [BBound, Expr.liftLooseBVars']
    exact ⟨ihv h.1, by rwa [Nat.add_right_comm] at this⟩
  | mdata _ _ ih => intro k s d h; exact ih h
  | proj _ _ _ ih => intro k s d h; exact ih h
  | _ => intros; trivial

/-- `lamsOf` adds `m` binders. -/
private theorem BBound_lamsOf : ∀ {m k : Nat} {ty body e : Expr}, lamsOf m ty body = some e →
    BBound (k + m) body → BBound k e
  | 0, _, _, _, _, h, hb => by cases h; exact hb
  | m + 1, k, .forallE _ _ b _, body, e, h, hb => by
    simp only [lamsOf, Option.map_eq_some_iff] at h
    obtain ⟨e', h', rfl⟩ := h
    exact BBound_lamsOf (k := k + 1) h' (by rwa [Nat.add_right_comm, Nat.add_assoc])
  | _ + 1, _, .bvar _, _, _, h, _ | _ + 1, _, .fvar _, _, _, h, _ | _ + 1, _, .mvar _, _, _, h, _
  | _ + 1, _, .sort _, _, _, h, _ | _ + 1, _, .const .., _, _, h, _ | _ + 1, _, .app .., _, _, h, _
  | _ + 1, _, .lam .., _, _, h, _ | _ + 1, _, .letE .., _, _, h, _ | _ + 1, _, .lit _, _, _, h, _
  | _ + 1, _, .mdata .., _, _, h, _ | _ + 1, _, .proj .., _, _, h, _ => by cases h

/-- The η-expansion of a spine keeps the bound. -/
private theorem BBound_etaSpine {σ : EvalEnv} {c : Name} {us : List Level} {as : List Expr} {e' : Expr}
    {k : Nat} (h : σ.etaSpine? c us as = some e') (hb : BBound k (mkAppN (.const c us) as.toArray)) :
    BBound k e' := by
  unfold EvalEnv.etaSpine? at h
  split at h
  · split at h
    · obtain ⟨ty, -, h⟩ := Option.bind_eq_some_iff.1 h
      refine BBound_lamsOf h (BBound_mkAppN.2 ⟨trivial, fun a ha => ?_⟩)
      rcases List.mem_append.1 ha with ha | ha
      · obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.1 ha
        exact BBound_lift ((BBound_mkAppN.1 hb).2 a₀ ha₀)
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 ha
        simp only [List.mem_reverse, List.mem_range] at hj
        show j < _
        omega
    · cases h
  · cases h

/-- Bound variables found in the locals are below the number of bound locals. -/
private theorem findB_lt {ζ : Metalean.Sigs} {ℓ n : Nat} :
    ∀ {Δ : MLCtx ζ ℓ n} {i : Nat} {t : Metalean.Expr ζ ℓ n}, Δ.findB i = some t →
      i < Δ.countP (·.1.isNone)
  | [], _, _, h => nomatch h
  | (none, _) :: _, 0, _, _ => by simp
  | (none, _) :: Δ, i + 1, _, h => by
    simp only [MLCtx.findB] at h
    have := findB_lt h
    simp only [List.countP_cons, Option.isNone_none, ite_true]
    omega
  | (some _, _) :: Δ, _, _, h => by
    simp only [MLCtx.findB] at h
    have := findB_lt h
    simpa [List.countP_cons] using this

private theorem countP_pushLam {ζ : Metalean.Sigs} {ℓ n : Nat} (Δ : MLCtx ζ ℓ n) :
    (Δ.pushLam none).countP (·.1.isNone) = Δ.countP (·.1.isNone) + 1 := by
  simp only [MLCtx.pushLam, List.countP_cons, Option.isNone_none, ite_true, List.countP_map]
  rfl

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {σ : EvalEnv} {lps : List Name}
  {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}

/-- A translated term has no loose index beyond the bound locals. -/
private theorem TrM.bbound {e : Expr} {t : Metalean.Expr ζ lps.length n}
    (h : TrM E B lps Γ Δ e t) : BBound (Δ.countP (·.1.isNone)) e := by
  induction h with
  | bvar h => exact findB_lt h
  | special _ _ hlen _ _ ih =>
    refine BBound_mkAppN.2 ⟨trivial, fun a ha => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    exact ih i _ _ (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem (hlen ▸ hi))
  | app _ _ _ ihf iha => exact ⟨ihf, iha⟩
  | lam _ _ _ ihb => rw [countP_pushLam] at ihb; exact ihb
  | letE _ _ _ _ ihv ihb => exact ⟨ihv, by simpa [List.countP_cons] using ihb⟩
  | mdata _ ih => exact ih
  | projStruct _ _ _ _ _ ih => exact ih
  | projProof _ _ _ _ _ _ _ _ _ ih => exact ih
  | _ => trivial

/-- `closedn` of an application spine. -/
private theorem closedn_mkApps {k : Nat} : ∀ {f : LBTerm} {as : List LBTerm},
    closedn k (mkApps f as) = true ↔ closedn k f = true ∧ ∀ a ∈ as, closedn k a = true
  | _, [] => by simp [mkApps]
  | _, a :: as => by
    rw [mkApps, closedn_mkApps]
    simp only [closedn, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp, and_assoc]

/-- The pointwise premise of a list rule gives the property on every element of the target list. -/
private theorem forall_mem_of_getElem {α β : Type} {as : List α} {bs : List β} {R : α → β → Prop}
    {Q : β → Prop} (hlen : as.length = bs.length)
    (h : ∀ (i : Nat) a b, as[i]? = some a → bs[i]? = some b → R a b)
    (hq : ∀ a b, a ∈ as → R a b → Q b) : ∀ b ∈ bs, Q b := by
  intro b hb
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
  exact hq _ _ (List.getElem_mem (hlen ▸ hi))
    (h i _ _ (List.getElem?_eq_getElem (hlen ▸ hi)) (List.getElem?_eq_getElem hi))

/-- Erasures of terms bounded by `k` (outside binder domains) are closed below `k`. -/
private theorem Erases.closedn_of_bbound {e : Expr} {tb : LBTerm}
    (h : Erases E B lps σ Γ Δ e tb) : ∀ k, BBound k e → closedn k tb = true := by
  refine Erases.rec (motive_1 := fun _ _ e tb _ => ∀ k, BBound k e → closedn k tb = true)
    (motive_2 := fun _ _ _ e br _ => ∀ k, BBound k e → closedn (k + br.1.length) br.2 = true)
    ?bvar ?fvar ?lam ?letE ?app ?const ?ctor ?cases ?casesReduced ?eta ?proj ?litZero ?litSucc
    ?mdata ?box ?done ?alam ?intro h
  case bvar => intro _ _ _ _ k hk; simpa [closedn, BBound] using hk
  case fvar | const | box | litZero => intros; rfl
  case lam => intro _ _ _ _ _ _ _ _ _ _ _ _ ih k hk; exact ih (k + 1) hk
  case letE =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihv ihb k hk
    simp only [closedn, Bool.and_eq_true]
    exact ⟨ihv k hk.1, ihb (k + 1) hk.2⟩
  case app =>
    intro _ _ _ _ _ _ _ _ _ _ ihf iha k hk
    simp only [closedn, Bool.and_eq_true]
    exact ⟨ihf k hk.1, iha k hk.2⟩
  case ctor =>
    intro _ _ _ _ _ _ _ as as' _ _ _ _ hlen _ ih k hk
    refine closedn_mkApps.2 ⟨rfl, forall_mem_of_getElem hlen
      (R := fun a a' => ∀ k, BBound k a → closedn k a' = true) ih fun a a' ha h => ?_⟩
    exact h k ((BBound_mkAppN.1 hk).2 a ha)
  case cases =>
    intro _ iv _ _ _ _ _ maj _ pre alts extra brs _ _ _ _ _ _ hlalts _ hlbrs hcf _ hlex _ ihm iha ihe
      k hk
    have hb := (BBound_mkAppN.1 hk).2
    refine closedn_mkApps.2 ⟨?_, forall_mem_of_getElem hlex
      (R := fun a a' => ∀ k, BBound k a → closedn k a' = true) ihe
      fun a a' ha h => h k (hb a (by simp [ha]))⟩
    simp only [closedn, Bool.and_eq_true]
    refine ⟨ihm k (hb maj (by simp)), ?_⟩
    have key : ∀ brs' : List (List BinderName × LBTerm),
        (∀ br ∈ brs', closedn (k + br.1.length) br.2 = true) → closednB k brs' = true := by
      intro brs' h
      induction brs' with
      | nil => rfl
      | cons br brs' ih =>
        obtain ⟨ns, b⟩ := br
        simp only [closednB, Bool.and_eq_true]
        exact ⟨h _ List.mem_cons_self, ih fun b hb => h b (List.mem_cons_of_mem _ hb)⟩
    refine key brs fun br hbr => ?_
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hbr
    have hia : i < alts.length := hlbrs ▸ hi
    have hic : i < iv.ctors.length := hlalts ▸ hia
    obtain ⟨kf, hkf⟩ := Option.isSome_iff_exists.1 (hcf i _ (List.getElem?_eq_getElem hic))
    exact iha i _ _ _ kf (List.getElem?_eq_getElem hic) (List.getElem?_eq_getElem hia)
      (List.getElem?_eq_getElem hi) hkf k (hb _ (by simp [List.getElem_mem hia]))
  case casesReduced =>
    intro _ _ _ _ _ _ _ alt _ _ _ _ extra extra' _ _ _ _ _ _ _ hlex _ iha ihe k hk
    have hb := (BBound_mkAppN.1 hk).2
    refine closedn_mkApps.2 ⟨iha k (hb alt (by simp)), fun a ha => ?_⟩
    rcases List.mem_append.1 ha with ha | ha
    · rw [List.eq_of_mem_replicate ha]; rfl
    · exact forall_mem_of_getElem hlex (R := fun a a' => ∀ k, BBound k a → closedn k a' = true)
        ihe (fun a a' ha h => h k (hb a (by simp [ha]))) a ha
  case eta => intro _ _ _ _ _ _ _ _ heta _ ih k hk; exact ih k (BBound_etaSpine heta hk)
  case proj => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih k hk; exact ih k hk
  case litSucc => intro _ _ _ _ _ _ _ _ ih k _; simp only [closedn, Bool.and_eq_true]; exact ⟨rfl, ih k trivial⟩
  case mdata => intros; rename_i ih k hk; exact ih k hk
  case done => intros; rename_i ih k hk; exact ih k hk
  case alam =>
    intros; rename_i ih k hk
    have := ih (k + 1) hk
    simp only [List.length_cons] at this ⊢
    rwa [show ∀ m, k + (m + 1) = k + 1 + m from fun m => by omega]
  case intro =>
    intros; rename_i ih k hk
    have := ih (k + 1) ⟨BBound_lift hk, Nat.zero_lt_succ _⟩
    simp only [List.length_cons] at this ⊢
    rwa [show ∀ m, k + (m + 1) = k + 1 + m from fun m => by omega]

/-- The erasure of a translated term is closed under its bound locals. Reference: `erases_closed`
(`MR E/ErasureProperties.v:428`). -/
theorem Erases.closed {e : Expr} {t : Metalean.Expr ζ lps.length n} {tb : LBTerm}
    (he : TrM E B lps Γ Δ e t) (h : Erases E B lps σ Γ Δ e tb) :
    closedn (Δ.countP (·.1.isNone)) tb = true :=
  Erases.closedn_of_bbound h _ (TrM.bbound he)

/-- An erasure of a constructor spine with at least the constructor's arity is `□` or the λ□
constructor applied to erasures of the arguments. Reference: the `tConstruct` inversion of
`erases` (`MR E/Extract.v:106`), `erases_mkApps_inv` (`MR E/ErasureProperties.v:105`). -/
theorem Erases.ctor_inv {c : Name} {cv : ConstructorVal} {us : List Level} {as : List Expr}
    {tb : LBTerm} (hc : findDecl σ.decls c = some (.ctorInfo cv))
    (hle : cv.numParams + cv.numFields ≤ as.length)
    (h : Erases E B lps σ Γ Δ (mkAppN (.const c us) as.toArray) tb) :
    (tb = .box ∧ ErasableS E B lps Γ Δ (mkAppN (.const c us) as.toArray)) ∨
      ∃ iid as', IndIdOf σ cv.induct = some iid ∧ tb = mkApps (.construct iid cv.cidx []) as' ∧
        as.length = as'.length ∧
        ∀ (i : Nat) a a', as[i]? = some a → as'[i]? = some a' → Erases E B lps σ Γ Δ a a' := by
  generalize hx : mkAppN (.const c us) as.toArray = x at h
  have hfn : x.getAppFn = .const c us := hx ▸ getAppFn_mkAppN_const c us as
  have hsp : (∃ cv', findDecl σ.decls c = some (.ctorInfo cv')) ∨ ∃ iv, σ.casesOn? c = some iv :=
    .inl ⟨cv, hc⟩
  cases h with
  | box hb => subst hx; exact .inl ⟨rfl, hb⟩
  | ctor hc' _ hid _ hlen hall =>
    obtain ⟨rfl, rfl, rfl⟩ := mkAppN_const_inj hx
    rw [hc] at hc'
    cases hc'
    exact .inr ⟨_, _, hid, rfl, hlen, hall⟩
  | app hns => exact absurd (specialSpine_of hfn hsp) hns
  | const _ hsa =>
    cases hfn
    rw [specialArity_ctor hc] at hsa
    cases hsa
  | cases hco | casesReduced hco =>
    obtain ⟨rfl, -, -⟩ := mkAppN_const_inj hx
    obtain ⟨d, hd⟩ := casesOn?_defn hco
    rw [hc] at hd
    cases hd
  | eta heta =>
    obtain ⟨rfl, -, rfl⟩ := mkAppN_const_inj hx
    obtain ⟨ar, har, hlt⟩ := etaSpine?_some heta
    rw [specialArity_ctor hc] at har
    cases har
    omega
  | bvar | fvar | lam | letE | proj | litZero | litSucc | mdata =>
    exact absurd hfn (getAppFn_ne_const (fun _ _ h => by cases h) (fun _ _ h => by cases h))

/-- A recognized `casesOn` has its arity as a special constant. -/
private theorem specialArity_casesOn {σ : EvalEnv} {c : Name} {iv : InductiveVal}
    (hc : σ.casesOn? c = some iv) : specialArity σ c = some (casesArity iv) := by
  obtain ⟨d, hd⟩ := casesOn?_defn hc
  unfold specialArity
  rw [hd, hc]
  rfl

/-- An erasure of a recognized `casesOn` spine with at least its arity is `□`, a λ□ `case` on an
erasure of the major premise with one erased alternative per constructor, applied to erasures of
the extra arguments (`Erases.cases`), or the erased alternative applied to `□` for each field and
to the extra arguments (`Erases.casesReduced`); the arguments split at the major premise and after
the alternatives. Reference: the `tCase` inversion of `erases` (`MR E/Extract.v:111`),
`erases_mkApps_inv` (`MR E/ErasureProperties.v:105`). -/
theorem Erases.cases_inv {c : Name} {iv : InductiveVal} {us : List Level} {as : List Expr}
    {tb : LBTerm} (hc : σ.casesOn? c = some iv) (hle : casesArity iv ≤ as.length)
    (h : Erases E B lps σ Γ Δ (mkAppN (.const c us) as.toArray) tb) :
    (tb = .box ∧ ErasableS E B lps Γ Δ (mkAppN (.const c us) as.toArray)) ∨
    (∃ pre maj alts extra iid maj' brs extra', as = pre ++ [maj] ++ alts ++ extra ∧
      ¬ CasesReduced iv us ∧ Subsingleton E B iv.name ∧ IndIdOf σ iv.name = some iid ∧
      pre.length = casesMajor iv ∧ alts.length = iv.ctors.length ∧
      Erases E B lps σ Γ Δ maj maj' ∧ brs.length = alts.length ∧
      (∀ (i : Nat) cn, iv.ctors[i]? = some cn → (ctorFields σ cn).isSome) ∧
      (∀ (i : Nat) cn alt br k, iv.ctors[i]? = some cn → alts[i]? = some alt → brs[i]? = some br →
        ctorFields σ cn = some k → ErasesAlt E B lps σ Γ Δ k alt br) ∧
      extra.length = extra'.length ∧
      (∀ (i : Nat) a a', extra[i]? = some a → extra'[i]? = some a' → Erases E B lps σ Γ Δ a a') ∧
      tb = mkApps (.case (iid, iv.numParams) maj' brs) extra') ∨
    (∃ pre maj alt extra cn cv alt' extra', as = pre ++ [maj] ++ [alt] ++ extra ∧
      FieldsErasable E B iv.name ∧ iv.ctors = [cn] ∧ findDecl σ.decls cn = some (.ctorInfo cv) ∧
      (indexFields cv.numParams cv.type).all (·.isNone) = true ∧ pre.length = casesMajor iv ∧
      Erases E B lps σ Γ Δ alt alt' ∧ extra.length = extra'.length ∧
      (∀ (i : Nat) a a', extra[i]? = some a → extra'[i]? = some a' → Erases E B lps σ Γ Δ a a') ∧
      tb = mkApps alt' (List.replicate cv.numFields .box ++ extra')) := by
  generalize hx : mkAppN (.const c us) as.toArray = x at h
  have hfn : x.getAppFn = .const c us := hx ▸ getAppFn_mkAppN_const c us as
  have hsp : (∃ cv, findDecl σ.decls c = some (.ctorInfo cv)) ∨ ∃ iv, σ.casesOn? c = some iv :=
    .inr ⟨iv, hc⟩
  cases h with
  | box hb => subst hx; exact .inl ⟨rfl, hb⟩
  | cases hco hnr hss hid hpre halts hm hbrs hcf halt hlex hext =>
    obtain ⟨rfl, rfl, rfl⟩ := mkAppN_const_inj hx
    rw [hc] at hco
    cases hco
    exact .inr (.inl ⟨_, _, _, _, _, _, _, _, rfl, hnr, hss, hid, hpre, halts, hm, hbrs, hcf, halt,
      hlex, hext, rfl⟩)
  | casesReduced hco hfe hcs hcv hidx hpre ha hlex hext =>
    obtain ⟨rfl, rfl, rfl⟩ := mkAppN_const_inj hx
    rw [hc] at hco
    cases hco
    exact .inr (.inr ⟨_, _, _, _, _, _, _, _, rfl, hfe, hcs, hcv, hidx, hpre, ha, hlex, hext, rfl⟩)
  | ctor hc' =>
    obtain ⟨rfl, -, -⟩ := mkAppN_const_inj hx
    obtain ⟨d, hd⟩ := casesOn?_defn hc
    rw [hc'] at hd
    cases hd
  | app hns => exact absurd (specialSpine_of hfn hsp) hns
  | const _ hsa =>
    cases hfn
    rw [specialArity_casesOn hc] at hsa
    cases hsa
  | eta heta =>
    obtain ⟨rfl, -, rfl⟩ := mkAppN_const_inj hx
    obtain ⟨ar, har, hlt⟩ := etaSpine?_some heta
    rw [specialArity_casesOn hc] at har
    cases har
    omega
  | bvar | fvar | lam | letE | proj | litZero | litSucc | mdata =>
    exact absurd hfn (getAppFn_ne_const (fun _ _ h => by cases h) (fun _ _ h => by cases h))

/-- An erasure of an atom spine is headed by `□`: an atom constant is neither a constructor nor a
recognized `casesOn`, and `Erases.const` needs a non-atom, so `Erases.box` is its only rule.
Reference: `erases_mkApps_inv` (`MR E/ErasureProperties.v:105`) for `tInd`-headed terms, which
erase only by `erases_box` (`MR E/Extract.v:140`); DV-11. -/
private theorem Erases.headOf_atomSpine {e : Expr} {tb : LBTerm} (hsp : AtomSpine σ e)
    (h : Erases E B lps σ Γ Δ e tb) : headOf tb = .box := by
  obtain ⟨c₀, us₀, he₀, ha₀⟩ := hsp.head
  induction hsp generalizing tb with
  | const ha =>
    generalize hx : Expr.const _ _ = x at h
    have hns := isAtom_not_special ha
    cases h with
    | box => rfl
    | const hat => cases hx; rw [ha] at hat; cases hat
    | ctor hc =>
      have := congrArg Expr.getAppFn hx
      rw [getAppFn_mkAppN_const] at this
      cases this
      exact absurd (.inl ⟨_, hc⟩) hns
    | cases hc | casesReduced hc =>
      have := congrArg Expr.getAppFn hx
      rw [getAppFn_mkAppN_const] at this
      cases this
      exact absurd (.inr ⟨_, hc⟩) hns
    | eta heta =>
      have := congrArg Expr.getAppFn hx
      rw [getAppFn_mkAppN_const] at this
      cases this
      obtain ⟨_, har, _⟩ := etaSpine?_some heta
      exact absurd (specialArity_some har) hns
    | bvar | fvar | lam | letE | app | proj | litZero | litSucc | mdata => cases hx
  | @app f a hf ih =>
    generalize hx : Expr.app f a = x at h
    have hfn : ∀ {c : Name} {us : List Level} {as : List Expr}, x = mkAppN (.const c us) as.toArray → c = c₀ := fun h' => by
      have := he₀
      rw [hx, h', getAppFn_mkAppN_const] at this
      cases this; rfl
    have hns := isAtom_not_special ha₀
    cases h with
    | box => rfl
    | app _ hf' => cases hx; have := ih hf' he₀; exact this
    | ctor hc => cases hfn rfl; exact absurd (.inl ⟨_, hc⟩) hns
    | cases hc | casesReduced hc => cases hfn rfl; exact absurd (.inr ⟨_, hc⟩) hns
    | eta heta =>
      cases hfn rfl
      obtain ⟨_, har, _⟩ := etaSpine?_some heta
      exact absurd (specialArity_some har) hns
    | bvar | fvar | lam | letE | const | proj | litZero | litSucc | mdata => cases hx

/-- An erasure of an atom spine that is a λ□ evaluation result is `□`. Reference: DV-11; the
analogue of `tInd`-headed values, which erase only by `erases_box` (`MR E/Extract.v:140`). -/
theorem Erases.atomSpine_box {e : Expr} {tb s : LBTerm} {lenv : GlobalDeclarations}
    (hsp : AtomSpine σ e) (h : Erases E B lps σ .nil [] e tb)
    (hv : LBEval defaultFlags lenv s tb) : tb = .box :=
  LBEval.eq_box_of_headOf hv (Erases.headOf_atomSpine hsp h)

/-- An erasure of a constructor spine with at least the constructor's arity, of an inductive in
`Prop`, is `□`: `Erases.ctor` needs `¬ PropInductive`. Reference: `erases_tConstruct`
(`MR E/Extract.v:106`, `~~ isPropositional`), whose only alternative is `erases_box`
(`MR E/Extract.v:140`). -/
theorem Erases.ctorProp_box {c : Name} {cv : ConstructorVal} {us : List Level} {as : List Expr}
    {tb : LBTerm} (hc : findDecl σ.decls c = some (.ctorInfo cv))
    (hP : PropInductive E B cv.induct) (hle : cv.numParams + cv.numFields ≤ as.length)
    (h : Erases E B lps σ Γ Δ (mkAppN (.const c us) as.toArray) tb) : tb = .box := by
  generalize hx : mkAppN (.const c us) as.toArray = x at h
  have hfn : x.getAppFn = .const c us := hx ▸ getAppFn_mkAppN_const c us as
  have hsp : (∃ cv', findDecl σ.decls c = some (.ctorInfo cv')) ∨ ∃ iv, σ.casesOn? c = some iv :=
    .inl ⟨cv, hc⟩
  cases h with
  | box => rfl
  | ctor hc' hnp =>
    obtain ⟨rfl, -, -⟩ := mkAppN_const_inj hx
    rw [hc] at hc'
    cases hc'
    exact absurd hP hnp
  | app hns => exact absurd (specialSpine_of hfn hsp) hns
  | const _ hsa =>
    cases hfn
    rw [specialArity_ctor hc] at hsa
    cases hsa
  | cases hco | casesReduced hco =>
    obtain ⟨rfl, -, -⟩ := mkAppN_const_inj hx
    obtain ⟨d, hd⟩ := casesOn?_defn hco
    rw [hc] at hd
    cases hd
  | eta heta =>
    obtain ⟨rfl, -, rfl⟩ := mkAppN_const_inj hx
    obtain ⟨ar, har, hlt⟩ := etaSpine?_some heta
    rw [specialArity_ctor hc] at har
    cases har
    omega
  | bvar | fvar | lam | letE | proj | litZero | litSucc | mdata =>
    exact absurd hfn (getAppFn_ne_const (fun _ _ h => by cases h) (fun _ _ h => by cases h))

/-- The head of a `PropProj` spine is a projection. -/
private theorem PropProj.head {e : Expr} (h : PropProj σ e) : ∃ S i e₀, e.getAppFn = .proj S i e₀ := by
  induction h with
  | proj => exact ⟨_, _, _, rfl⟩
  | projProj => exact ⟨_, _, _, rfl⟩
  | app _ ih => exact ih

/-- An erasure of a `PropProj` spine is headed by `□` or by a λ□ projection: the head is a
projection, which erases by `Erases.proj` or `Erases.box`. -/
private theorem Erases.headOf_propProj {e : Expr} {tb : LBTerm} (hp : PropProj σ e)
    (h : Erases E B lps σ Γ Δ e tb) : headOf tb = .box ∨ ∃ p x, headOf tb = .proj p x := by
  obtain ⟨S₀, i₀, e₀, he₀⟩ := hp.head
  have spine : ∀ {x : Expr} {c : Name} {us : List Level} {as : List Expr},
      x.getAppFn = .proj S₀ i₀ e₀ → x ≠ mkAppN (.const c us) as.toArray := by
    intro x c us as hx h'
    rw [h', getAppFn_mkAppN_const] at hx
    cases hx
  induction hp generalizing tb with
  | proj | projProj =>
    generalize hx : Expr.proj _ _ _ = x at h he₀
    cases h with
    | box => exact .inl rfl
    | proj => exact .inr ⟨_, _, rfl⟩
    | ctor | cases | casesReduced | eta => exact (spine he₀ rfl).elim
    | bvar | fvar | lam | letE | app | const | litZero | litSucc | mdata => cases hx
  | @app f a _ ih =>
    generalize hx : Expr.app f a = x at h he₀
    cases h with
    | box => exact .inl rfl
    | app _ hf =>
      cases hx
      have := @ih _ hf he₀
      exact this
    | ctor | cases | casesReduced | eta => exact (spine he₀ rfl).elim
    | bvar | fvar | lam | letE | const | proj | litZero | litSucc | mdata => cases hx

/-- A λ□ evaluation result is not headed by a projection. Reference: `eval_to_value`
(`MR E/EWcbvEval.v:771`): values are not stuck projections. -/
private theorem LBEval.headOf_ne_proj {fl : WcbvFlags} {lenv : GlobalDeclarations} {s t : LBTerm}
    (hev : LBEval fl lenv s t) : ∀ p x, headOf t ≠ .proj p x := by
  induction hev using LBEval.ind with
  | box | projProp | constructBlock | prim => intro _ _ h; cases h
  | beta _ _ _ _ _ ih | zeta _ _ _ ih | iota _ _ _ _ _ _ _ _ ih | iotaBlock _ _ _ _ _ _ _ _ ih
  | iotaSing _ _ _ _ _ _ ih | fix _ _ _ _ _ _ _ ih | fix' _ _ _ _ _ _ _ ih | delta _ _ _ ih
  | proj _ _ _ _ _ _ _ ih | projBlock _ _ _ _ _ _ _ ih => exact ih
  | fixValue | construct => intro _ _ h; simp only [headOf, headOf_mkApps] at h; cases h
  | appCong _ _ _ ihf => exact ihf
  | atom ha =>
    rename_i t
    intro _ _ h
    cases t with
    | proj => simp [lbAtom] at ha
    | app => simp [lbAtom] at ha
    | _ => cases h

/-- An erasure of a `PropProj` spine that is a λ□ evaluation result is `□`: its head is `□` or a
projection, and no result is headed by a projection or is an application of `□`. Reference: none
(PCUIC evaluates proofs to constructors; theorems have no δ here, DV-24); the λ□ side is
`eval_proj_prop` (`MR E/EWcbvEval.v:238`). -/
theorem Erases.propProj_box {e : Expr} {tb s : LBTerm} {lenv : GlobalDeclarations}
    (hp : PropProj σ e) (h : Erases E B lps σ Γ Δ e tb) (hv : LBEval defaultFlags lenv s tb) :
    tb = .box := by
  rcases Erases.headOf_propProj hp h with hb | ⟨p, x, hpx⟩
  · exact LBEval.eq_box_of_headOf hv hb
  · exact absurd hpx (LBEval.headOf_ne_proj hv p x)

end

end EraseProof
