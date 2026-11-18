import EraseProof.TargetLift

/-!
# Basic properties of the erasure relation

The erasure of a term without loose indices from `k` on is closed below `k` (`Erases.closed`);
without certificates the binder context is irrelevant (`Erases.ctx`); an erasure applied to an
erasure erases the application (`Erases.appS`: a special spine takes the argument as one more
extra argument of its own rule); and the inversions of an application that is no short spine
(`Erases.app_inv`), of a constructor spine (`Erases.ctor_inv`) and of a `casesOn` spine
(`Erases.cases_inv`). Adapted from `ML-V Relation/Basic.lean` and from the application inversion
`ML-V Simulation/Cases.lean:102`: the relation has no typing premise and relates to `□` only
`erase`-marked terms, so no inversion of an unmarked spine has a `□` alternative.
-/

open Lean Erasure

namespace EraseProof

/-! ## Application spines -/

/-- `mkAppN` over a list is a left fold of `Expr.app`. Copy of `ML-V Bridge/Basic.lean:32`. -/
theorem mkAppN_toArray (f : Expr) (as : List Expr) : mkAppN f as.toArray = as.foldl .app f := by
  simp only [mkAppN, List.foldl_toArray]; rfl

/-- One more argument at the end of a spine. -/
theorem mkAppN_snoc (f : Expr) (as : List Expr) (a : Expr) :
    mkAppN f (as ++ [a]).toArray = .app (mkAppN f as.toArray) a := by
  simp only [mkAppN_toArray, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- One more argument at the end of a λ□ spine. Copy of `ML-V Simulation/Cases.lean:45`. -/
theorem mkApps_snoc : ∀ (t : LBTerm) (l : List LBTerm) (x : LBTerm),
    mkApps t (l ++ [x]) = .app (mkApps t l) x
  | _, [], _ => rfl
  | t, a :: l, x => mkApps_snoc (.app t a) l x

/-- The head of a left fold of applications is the head of its start. Copy of
`ML-V Relation/Basic.lean:23`. -/
theorem getAppFn_foldl (f : Expr) : ∀ as : List Expr, (as.foldl .app f).getAppFn = f.getAppFn
  | [] => rfl
  | a :: as => by rw [List.foldl_cons, getAppFn_foldl _ as]; rfl

/-- The head of a constant spine is the constant. Copy of `ML-V Relation/Basic.lean:38`. -/
theorem getAppFn_mkAppN_const (c : Name) (us : List Level) (as : List Expr) :
    (mkAppN (.const c us) as.toArray).getAppFn = .const c us := by
  rw [mkAppN_toArray, getAppFn_foldl]; rfl

/-- A list is empty or has a last element. Copy of `ML-V Simulation/Cases.lean:60`. -/
theorem eq_nil_or_snoc {α : Type} (l : List α) : l = [] ∨ ∃ l' x, l = l' ++ [x] := by
  rcases l.eq_nil_or_concat with h | ⟨L, b, h⟩
  · exact .inl h
  · exact .inr ⟨L, b, by simp [h]⟩

/-- The arguments of an application spine, outermost last. Copy of `ML-V Relation/Basic.lean:28`. -/
private def appArgs : Expr → List Expr
  | .app f a => appArgs f ++ [a]
  | _ => []

/-- The arguments of a left fold of applications. Copy of `ML-V Relation/Basic.lean:32`. -/
private theorem appArgs_foldl (f : Expr) : ∀ as : List Expr, appArgs (as.foldl .app f) = appArgs f ++ as
  | [] => (List.append_nil _).symm
  | a :: as => by
    rw [List.foldl_cons, appArgs_foldl _ as, appArgs, List.append_assoc, List.singleton_append]

/-- Constant spines are equal only with the same constant, levels and arguments. Copy of
`ML-V Relation/Basic.lean:43`. -/
theorem mkAppN_const_inj {c c' : Name} {us us' : List Level} {as as' : List Expr}
    (h : mkAppN (.const c us) as.toArray = mkAppN (.const c' us') as'.toArray) :
    c = c' ∧ us = us' ∧ as = as' := by
  have h1 := congrArg Expr.getAppFn h
  have h2 := congrArg appArgs h
  rw [getAppFn_mkAppN_const, getAppFn_mkAppN_const] at h1
  rw [mkAppN_toArray, mkAppN_toArray, appArgs_foldl, appArgs_foldl] at h2
  cases h1
  exact ⟨rfl, rfl, by simpa [appArgs] using h2⟩

/-- An accumulator that counts applications counts from its start value. Copy of
`ML-V Source/Defeq.lean:264`. -/
theorem getAppNumArgs_shift (g : Expr → Nat → Nat) (happ : ∀ f a n, g (.app f a) n = g f (n + 1))
    (hother : ∀ e n, e.isApp = false → g e n = n) : ∀ e n, g e n = g e 0 + n := by
  intro e
  induction e with
  | app f a ih => intro n; rw [happ, happ, ih (n + 1), ih 1]; omega
  | _ => intro n; rw [hother _ n rfl, hother _ 0 rfl]; omega

/-- One more argument. Copy of `ML-V Source/Defeq.lean:272`. -/
theorem getAppNumArgs_app (f a : Expr) : (Expr.app f a).getAppNumArgs = f.getAppNumArgs + 1 := by
  unfold Expr.getAppNumArgs
  exact getAppNumArgs_shift _ (fun _ _ _ => rfl)
    (fun e n h => by cases e <;> first | rfl | cases h) f 1

/-- The number of arguments of a left fold of applications. -/
theorem getAppNumArgs_foldl : ∀ (f : Expr) (as : List Expr),
    (as.foldl .app f).getAppNumArgs = f.getAppNumArgs + as.length
  | _, [] => rfl
  | f, a :: as => by
    rw [List.foldl_cons, getAppNumArgs_foldl _ as, getAppNumArgs_app, List.length_cons]; omega

/-- The number of arguments of a constant spine. -/
theorem getAppNumArgs_mkAppN_const (c : Name) (us : List Level) (as : List Expr) :
    (mkAppN (.const c us) as.toArray).getAppNumArgs = as.length := by
  rw [mkAppN_toArray, getAppNumArgs_foldl]; exact Nat.zero_add _

/-- Pointwise related lists with one more element each. -/
theorem forall_snoc' {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β} {x : α} {y : β}
    (hlen : l.length = l'.length) (h : ∀ (i : Nat) a b, l[i]? = some a → l'[i]? = some b → R a b)
    (hxy : R x y) : ∀ (i : Nat) a b, (l ++ [x])[i]? = some a → (l' ++ [y])[i]? = some b → R a b := by
  intro i a b ha hb
  rcases Nat.lt_or_ge i l.length with hi | hi
  · rw [List.getElem?_append_left hi] at ha
    rw [List.getElem?_append_left (hlen ▸ hi)] at hb
    exact h i a b ha hb
  · rw [List.getElem?_append_right hi] at ha
    rw [List.getElem?_append_right (hlen ▸ hi)] at hb
    rw [← hlen] at hb
    rcases Nat.lt_or_ge (i - l.length) 1 with h1 | h1
    · rw [show i - l.length = 0 by omega] at ha hb; cases ha; cases hb; exact hxy
    · rw [List.getElem?_eq_none (by simp; omega)] at ha; cases ha

/-- The last argument of a constant spine `.app f a` whose arguments end with a non-empty list
`extra`, related pointwise to `extra'`: `extra` ends with `a`, `extra'` with its partner. -/
theorem split_last {R : Expr → LBTerm → Prop} {c : Name} {us : List Level} {f a : Expr}
    {X extra : List Expr} {extra' : List LBTerm}
    (hx : Expr.app f a = mkAppN (.const c us) (X ++ extra).toArray) (hne : extra ≠ [])
    (hlen : extra.length = extra'.length)
    (h : ∀ (i : Nat) x y, extra[i]? = some x → extra'[i]? = some y → R x y) :
    ∃ ex ex' y, extra = ex ++ [a] ∧ extra' = ex' ++ [y] ∧ f = mkAppN (.const c us) (X ++ ex).toArray ∧
      ex.length = ex'.length ∧ (∀ (i : Nat) x z, ex[i]? = some x → ex'[i]? = some z → R x z) ∧ R a y := by
  obtain ⟨ex, x, rfl⟩ := (eq_nil_or_snoc extra).resolve_left hne
  obtain ⟨ex', y, rfl⟩ := (eq_nil_or_snoc extra').resolve_left
    (by rintro rfl; simp at hlen)
  simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hlen
  rw [← List.append_assoc, mkAppN_snoc] at hx
  cases hx
  refine ⟨ex, ex', y, rfl, rfl, rfl, hlen, fun i x z hx hz => h i x z ?_ ?_, h ex.length a y ?_ ?_⟩
  · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hx).1]; exact hx
  · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hz).1]; exact hz
  · simp
  · simp [hlen]

/-! ## Facts about the evaluation environment -/

/-- A recognized `casesOn` constant is a definition. Copy of `ML-V Source/Defeq.lean:155`. -/
theorem casesOn?_defn {σ : EvalEnv} {c : Name} {iv : InductiveVal}
    (h : σ.casesOn? c = some iv) : ∃ d, findDecl σ.decls c = some (.defnInfo d) := by
  unfold EvalEnv.casesOn? casesOnOf? at h
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

/-- A recognized `casesOn` has its arity as a special constant. Copy of
`ML-V Simulation/Cases.lean:66`. -/
theorem specialArity_casesOn {σ : EvalEnv} {c : Name} {iv : InductiveVal}
    (hc : σ.casesOn? c = some iv) : specialArity σ c = some (casesArity iv) := by
  obtain ⟨d, hd⟩ := casesOn?_defn hc
  unfold specialArity
  rw [hd, hc]
  rfl

/-- A spine `c.{us} as` with `as` at most the arity `ar` of `c` is short. Copy of
`ML-V Simulation/Cases.lean:81`. -/
theorem shortSpine_of {σ : EvalEnv} {c : Name} {us : List Level} {as : List Expr} {f a : Expr}
    {ar : Nat} (hx : Expr.app f a = mkAppN (.const c us) as.toArray)
    (har : specialArity σ c = some ar) (hle : as.length ≤ ar) : ShortSpine σ (.app f a) :=
  ⟨c, us, ar, by rw [hx, getAppFn_mkAppN_const], har,
    by rw [hx, getAppNumArgs_mkAppN_const]; exact hle⟩

/-- A constructor's arity is its number of parameters and fields. Copy of
`ML-V Relation/Basic.lean:118`. -/
theorem specialArity_ctor {σ : EvalEnv} {c : Name} {cv : ConstructorVal}
    (hc : findDecl σ.decls c = some (.ctorInfo cv)) :
    specialArity σ c = some (cv.numParams + cv.numFields) := by
  unfold specialArity; rw [hc]

/-- A constant without an arity that is no recursor is no special head. -/
theorem not_special_of_const {σ : EvalEnv} {c : Name} (hsa : specialArity σ c = none)
    (hnr : ∀ rv, findDecl σ.decls c ≠ some (.recInfo rv)) :
    ¬ ((∃ cv, findDecl σ.decls c = some (.ctorInfo cv)) ∨ (σ.casesOn? c).isSome ∨
      (∃ qv, findDecl σ.decls c = some (.quotInfo qv) ∧ (quotEvalArity qv.kind).isSome) ∨
      ∃ rv, findDecl σ.decls c = some (.recInfo rv)) := by
  rintro (⟨cv, h⟩ | h | ⟨qv, h, hq⟩ | ⟨rv, h⟩)
  · rw [specialArity_ctor h] at hsa; cases hsa
  · obtain ⟨iv, hiv⟩ := Option.isSome_iff_exists.1 h
    rw [specialArity_casesOn hiv] at hsa; cases hsa
  · simp [specialArity, h] at hsa; simp [hsa] at hq
  · exact hnr rv h

/-! ## Closedness -/

/-- Every loose bound variable of `e` is below `k`. Copy of `ML-V Relation/Abstract.lean:26`. -/
def AbsFV.LBV : Nat → Expr → Prop
  | k, .bvar i => i < k
  | k, .app f a => LBV k f ∧ LBV k a
  | k, .lam _ t b _ | k, .forallE _ t b _ => LBV k t ∧ LBV (k + 1) b
  | k, .letE _ t v b _ => LBV k t ∧ LBV k v ∧ LBV (k + 1) b
  | k, .mdata _ e | k, .proj _ _ e => LBV k e
  | _, _ => True

/-- The loose bound variables of an application spine. Copy of `ML-V Relation/Abstract.lean:45`. -/
theorem AbsFV.LBV_foldl {k : Nat} (f : Expr) (as : List Expr) :
    LBV k (as.foldl .app f) ↔ LBV k f ∧ ∀ a ∈ as, LBV k a := by
  induction as generalizing f with
  | nil => simp
  | cons a as ih => simp [ih, LBV, and_assoc]

/-- The loose bound variables of a constant spine. -/
theorem AbsFV.LBV_mkAppN {k : Nat} {c : Name} {us : List Level} {as : List Expr} :
    LBV k (mkAppN (.const c us) as.toArray) ↔ ∀ a ∈ as, LBV k a := by
  rw [mkAppN_toArray, LBV_foldl]; simp [LBV]

/-- The pointwise premise of a list rule gives the property on every element of the target list.
Copy of `ML-V Relation/Basic.lean:283`. -/
theorem forall_mem_of_getElem {α β : Type} {as : List α} {bs : List β} {R : α → β → Prop}
    {Q : β → Prop} (hlen : as.length = bs.length)
    (h : ∀ (i : Nat) a b, as[i]? = some a → bs[i]? = some b → R a b)
    (hq : ∀ a b, a ∈ as → R a b → Q b) : ∀ b ∈ bs, Q b := by
  intro b hb
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
  exact hq _ _ (List.getElem_mem (hlen ▸ hi))
    (h i _ _ (List.getElem?_eq_getElem (hlen ▸ hi)) (List.getElem?_eq_getElem hi))

section
variable {cert : BoxCert} {σ : EvalEnv}

open TargetLift RecLam in
/-- The erasure of a term without loose indices from `k` on is closed below `k`. Adapted from
`ML-V Relation/Basic.lean:293 Erases.closedn_of_bbound`, with `AbsFV.LBV` for the translation's
bound. Reference: `erases_closed` (`MR E/ErasureProperties.v:428`). -/
theorem Erases.closed {Γ : List CtxBinder} {e : Expr} {tb : LBTerm} {k : Nat}
    (he : AbsFV.LBV k e) (h : Erases cert σ Γ e tb) : closedn k tb = true := by
  refine Erases.rec (motive_1 := fun _ e tb _ => ∀ k, AbsFV.LBV k e → closedn k tb = true)
    (motive_2 := fun _ _ e br _ => ∀ k, AbsFV.LBV k e → closedn (k + br.1.length) br.2 = true)
    ?bvar ?fvar ?lam ?etaLam ?letE ?app ?const ?ctor ?cases ?casesReduced ?proj ?litZero ?litSucc
    ?quotMk ?quotLift ?recLet ?recFix ?box ?done ?alam ?aeta h k he
  case bvar => intro _ _ k hk; simpa [closedn, AbsFV.LBV] using hk
  case fvar | const | box | litZero => intros; rfl
  case lam | etaLam => intro _ _ _ _ _ _ _ ih k hk; exact ih (k + 1) hk.2
  case letE =>
    intro _ _ _ _ _ _ _ _ _ _ ihv ihb k hk
    simp only [closedn, Bool.and_eq_true]
    exact ⟨ihv k hk.2.1, ihb (k + 1) hk.2.2⟩
  case app =>
    intro _ _ _ _ _ _ _ _ ihf iha k hk
    simp only [closedn, Bool.and_eq_true]
    exact ⟨ihf k hk.1, iha k hk.2⟩
  case ctor =>
    intro _ _ _ _ _ as as' _ _ _ _ hlen _ ih k hk
    exact closedn_mkApps.2 ⟨rfl, forall_mem_of_getElem hlen
      (R := fun a a' => ∀ k, AbsFV.LBV k a → closedn k a' = true) ih
      fun a a' ha h => h k (AbsFV.LBV_mkAppN.1 hk a ha)⟩
  case cases =>
    intro _ iv _ _ maj _ _ pre alts extra brs _ _ _ _ hlalts _ hlbrs hcf _ hlex _ ihm iha ihe k hk
    have hb := AbsFV.LBV_mkAppN.1 hk
    refine closedn_mkApps.2 ⟨?_, forall_mem_of_getElem hlex
      (R := fun a a' => ∀ k, AbsFV.LBV k a → closedn k a' = true) ihe
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
    intro _ _ _ _ _ _ alt _ _ _ extra extra' _ _ _ _ _ _ _ hlex _ iha ihe k hk
    have hb := AbsFV.LBV_mkAppN.1 hk
    refine closedn_mkApps.2 ⟨iha k (hb alt (by simp)), fun a ha => ?_⟩
    rcases List.mem_append.1 ha with ha | ha
    · rw [List.eq_of_mem_replicate ha]; rfl
    · exact forall_mem_of_getElem hlex (R := fun a a' => ∀ k, AbsFV.LBV k a → closedn k a' = true)
        ihe (fun a a' ha h => h k (hb a (by simp [ha]))) a ha
  case proj => intro _ _ _ _ _ _ _ _ _ _ _ ih k hk; exact ih k hk
  case litSucc =>
    intro _ _ _ _ _ _ ih k _
    simp only [closedn, Bool.and_eq_true]
    exact ⟨rfl, ih k trivial⟩
  case quotMk =>
    intros; rename_i hlex _ iha ihe k hk
    have hb := AbsFV.LBV_mkAppN.1 hk
    exact closedn_mkApps.2 ⟨iha k (hb _ (by simp)), forall_mem_of_getElem hlex
      (R := fun a a' => ∀ k, AbsFV.LBV k a → closedn k a' = true) ihe
      fun a a' ha h => h k (hb a (by simp [ha]))⟩
  case quotLift =>
    intros; rename_i hlex _ ihf ihq ihe k hk
    have hb := AbsFV.LBV_mkAppN.1 hk
    refine closedn_mkApps.2 ⟨ihf k (hb _ (by simp)), fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ihq k (hb _ (by simp))
    · exact forall_mem_of_getElem hlex
        (R := fun a a' => ∀ k, AbsFV.LBV k a → closedn k a' = true) ihe
        (fun a a' ha h => h k (hb a (by simp [ha]))) x hx
  case recLet =>
    intro _ rv minors F _ maj maj' _ _ _ _ _ _ mins' is' _ _ hF _ _ hmins _ hlm _ hli _ _ hle _
      ihmin ihis ihmaj ihext k hk
    have hb := AbsFV.LBV_mkAppN.1 hk
    obtain ⟨_, _, _, _, _, _, _, _, -, -, hml, -, -, -, -, -, -, hFc, -⟩ := hF
    have hz : (mins'.zip minors).length = rv.numMinors := by
      simp only [List.length_zip]; omega
    refine closedn_mkApps.2 ⟨?_, forall_mem_of_getElem hle
      (R := fun a a' => ∀ k, AbsFV.LBV k a → closedn k a' = true) ihext
      fun a a' ha h => h k (hb a (by simp [ha]))⟩
    have key := closedn_recLets (mins'.zip minors) 0 k
      (mkApps F (List.map (lbLift rv.numMinors 0) (is' ++ [maj']))) (fun p hp => ?_) ?_
    · simpa using key
    · exact forall_mem_of_getElem hlm (R := fun a a' => ∀ k, AbsFV.LBV k a → closedn k a' = true)
        ihmin (fun a a' ha h => h k (hb a (by simp [ha]))) p.1 (List.of_mem_zip hp).1
    · rw [Nat.add_zero, hz]
      refine closedn_mkApps.2 ⟨closedn_mono F _ _ hFc (by omega), fun a ha => ?_⟩
      obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.1 ha
      refine closedn_lbLift _ a₀ k 0 ?_ (Nat.zero_le _)
      rcases List.mem_append.1 ha₀ with h | h
      · exact forall_mem_of_getElem hli (R := fun a a' => ∀ k, AbsFV.LBV k a → closedn k a' = true)
          ihis (fun a a' ha hh => hh k (hb a (by simp [ha]))) a₀ h
      · rw [List.mem_singleton.1 h]; exact ihmaj k (hb maj (by simp))
  case recFix =>
    intro _ rv minors F _ maj _ _ _ _ _ _ _ ws _ _ _ hF _ _ hmins _ hlw _ hws hli _ _ hle _
      _ ihis ihmaj ihext k hk
    have hb := AbsFV.LBV_mkAppN.1 hk
    obtain ⟨_, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, -, hFc, -⟩ := hF
    have hs := closedn_substl ws.reverse F 0 (fun w hw => (hws w (List.mem_reverse.1 hw)).1)
      (by simpa [← hlw, hmins] using hFc)
    refine closedn_mkApps.2 ⟨closedn_mono _ 0 k hs (Nat.zero_le _), fun a ha => ?_⟩
    rcases List.mem_append.1 ha with ha | ha
    · rcases List.mem_append.1 ha with ha | ha
      · exact forall_mem_of_getElem hli (R := fun a a' => ∀ k, AbsFV.LBV k a → closedn k a' = true)
          ihis (fun a a' ha hh => hh k (hb a (by simp [ha]))) a ha
      · rw [List.mem_singleton.1 ha]; exact ihmaj k (hb maj (by simp))
    · exact forall_mem_of_getElem hle (R := fun a a' => ∀ k, AbsFV.LBV k a → closedn k a' = true)
        ihext (fun a a' ha hh => hh k (hb a (by simp [ha]))) a ha
  case done => intros; rename_i ih k hk; exact ih k hk
  case alam | aeta =>
    intros; rename_i ih k hk
    have := ih (k + 1) hk.2
    simp only [List.length_cons] at this ⊢
    rwa [show ∀ m, k + (m + 1) = k + 1 + m from fun m => by omega]


/-- Without certificates the binder context is irrelevant: only the certificates read it. -/
theorem Erases.ctx {Γ : List CtxBinder} {e : Expr} {t : LBTerm} (h : Erases noCert σ Γ e t)
    (Γ' : List CtxBinder) : Erases noCert σ Γ' e t :=
  Erases.rec (motive_1 := fun _ e t _ => ∀ Γ', Erases noCert σ Γ' e t)
    (motive_2 := fun _ k e br _ => ∀ Γ', ErasesAlt noCert σ Γ' k e br)
    (fun _ => .bvar) (fun _ => .fvar) (fun _ ih _ => .lam (ih _)) (fun _ ih _ => .etaLam (ih _))
    (fun _ _ ihv ihb _ => .letE (ihv _) (ihb _)) (fun hns _ _ ihf iha _ => .app hns (ihf _) (iha _))
    (fun h1 h2 h3 _ => .const h1 h2 h3)
    (fun h1 h2 h3 h4 h5 _ ih _ => .ctor h1 h2 h3 h4 h5 fun i a a' x y => ih i a a' x y _)
    (fun h1 h2 h3 h4 _ h6 h7 _ h9 _ ihm iha ihe _ => .cases h1 h2 h3 h4 (ihm _) h6 h7
      (fun i cn alt br k x y z w => iha i cn alt br k x y z w _) h9 fun i a a' x y => ihe i a a' x y _)
    (fun _ h1 h2 h3 h4 h5 _ h7 _ iha ihe _ => .casesReduced trivial h1 h2 h3 h4 h5 (iha _) h7
      fun i a a' x y => ihe i a a' x y _)
    (fun h1 h2 h3 _ ih _ => .proj h1 h2 h3 (ih _)) (fun h _ => .litZero h)
    (fun h _ ih _ => .litSucc h (ih _))
    (fun h1 h2 _ h4 _ iha ihe _ => .quotMk h1 h2 (iha _) h4 fun i a a' x y => ihe i a a' x y _)
    (fun h1 h2 _ _ h5 _ ihf ihq ihe _ => .quotLift h1 h2 (ihf _) (ihq _) h5
      fun i a a' x y => ihe i a a' x y _)
    (fun h1 h2 h3 h4 h5 h6 h7 _ h9 _ _ h12 _ ihm ihi ihj ihe _ => .recLet h1 h2 h3 h4 h5 h6 h7
      (fun i a a' x y => ihm i a a' x y _) h9 (fun i a a' x y => ihi i a a' x y _) (ihj _) h12
      fun i a a' x y => ihe i a a' x y _)
    (fun h1 h2 h3 h4 h5 h6 h7 _ h9 h10 _ _ h13 _ ihm ihi ihj ihe _ => .recFix h1 h2 h3 h4 h5 h6 h7
      (fun i a a' x y => ihm i a a' x y _) h9 h10 (fun i a a' x y => ihi i a a' x y _) (ihj _) h13
      fun i a a' x y => ihe i a a' x y _)
    (fun _ _ => .box trivial) (fun _ ih _ => .done (ih _)) (fun _ ih _ => .lam (ih _))
    (fun _ ih _ => .etaLam (ih _)) h Γ'

/-- An erasure applied to an erasure erases the application: by `Erases.app` when the head is no
special spine, otherwise by the head's own rule with the argument as one more extra argument.
Reference: `erases_tApp` (`MR E/Extract.v:101`), `erases_mkApps` (`MR E/ErasureProperties.v:96`). -/
theorem Erases.appS {Γ : List CtxBinder} {f a : Expr} {f' a' : LBTerm}
    (hf : Erases cert σ Γ f f') (ha : Erases cert σ Γ a a') :
    Erases cert σ Γ (.app f a) (.app f' a') := by
  by_cases hs : SpecialSpine σ f
  · cases hf with
    | ctor hc hp hid hle hlen hall =>
      rw [← mkAppN_snoc, ← mkApps_snoc]
      exact .ctor hc hp hid (by simp; omega) (by simp [hlen]) (forall_snoc' hlen hall ha)
    | cases hco hid hpre halts hm hbrs hcf halt hlex hext =>
      simpa only [← List.append_assoc, mkAppN_snoc, mkApps_snoc] using
        Erases.cases hco hid hpre halts hm hbrs hcf halt (by simp [hlex]) (forall_snoc' hlex hext ha)
    | casesReduced hd hco hcs hcv hidx hpre halt hlex hext =>
      simpa only [← List.append_assoc, mkAppN_snoc, mkApps_snoc] using
        Erases.casesReduced hd hco hcs hcv hidx hpre halt (by simp [hlex])
          (forall_snoc' hlex hext ha)
    | quotMk hc hk hx hlex hext =>
      simpa only [← List.append_assoc, mkAppN_snoc, mkApps_snoc] using
        Erases.quotMk hc hk hx (by simp [hlex]) (forall_snoc' hlex hext ha)
    | quotLift hc hk hf hq hlex hext =>
      simpa only [← List.append_assoc, ← List.cons_append, mkAppN_snoc, mkApps_snoc] using
        Erases.quotLift hc hk hf hq (by simp [hlex]) (forall_snoc' hlex hext ha)
    | recLet hc hF hps hms hmins his hlm hmin hli his' hmaj hlex hext =>
      simpa only [← List.append_assoc, mkAppN_snoc, mkApps_snoc] using
        Erases.recLet hc hF hps hms hmins his hlm hmin hli his' hmaj (by simp [hlex])
          (forall_snoc' hlex hext ha)
    | recFix hc hF hps hms hmins his hlw hmin hws hli his' hmaj hlex hext =>
      simpa only [← List.append_assoc, mkAppN_snoc, mkApps_snoc] using
        Erases.recFix hc hF hps hms hmins his hlw hmin hws hli his' hmaj (by simp [hlex])
          (forall_snoc' hlex hext ha)
    | app hns => exact absurd hs hns
    | const _ hsa hnr =>
      obtain ⟨_, _, hc, hd⟩ := hs
      cases hc
      exact absurd hd (not_special_of_const hsa hnr)
    | bvar | fvar | lam | etaLam | letE | proj | litZero | litSucc | box =>
      obtain ⟨_, _, h, -⟩ := hs; cases h
  · exact .app hs hf ha

/-- An erasure of an application that is no short spine is an application of erasures: a special
spine erased by its own rule has an extra argument, which is the last one. Adapted from
`ML-V Simulation/Cases.lean:102 app_inv`, with constructor heads. Reference: `erases_mkApps_inv`
(`MR E/ErasureProperties.v:105`). -/
theorem Erases.app_inv {Γ : List CtxBinder} {f a : Expr} {tb : LBTerm}
    (hns : ¬ ShortSpine σ (.app f a)) (h : Erases cert σ Γ (.app f a) tb) :
    ∃ tf ta, tb = .app tf ta ∧ Erases cert σ Γ f tf ∧ Erases cert σ Γ a ta := by
  generalize hx : Expr.app f a = x at h
  cases h with
  | app _ hf ha => cases hx; exact ⟨_, _, rfl, hf, ha⟩
  | @ctor c cv iid _ us as as' hc hp hid hle hlen hall =>
    have hgt := Nat.lt_of_not_le fun h' => hns (shortSpine_of hx (specialArity_ctor hc) h')
    obtain ⟨ex, ex', y, rfl, rfl, hf, hl, hall', hy⟩ := split_last (X := [])
      (by rwa [List.nil_append]) (by rintro rfl; simp at hgt) hlen hall
    rw [List.nil_append] at hf; subst hf
    refine ⟨_, _, mkApps_snoc _ _ _, .ctor hc hp hid ?_ hl hall', hy⟩
    simp at hgt; omega
  | @cases c iv iid _ maj maj' us pre alts extra brs extra' hco hid hpre halts hm hbrs hcf halt hlex
      hext =>
    have hne : extra ≠ [] := by
      rintro rfl
      exact hns (shortSpine_of hx (specialArity_casesOn hco) (by simp [hpre, halts, casesArity]; omega))
    obtain ⟨ex, ex', y, rfl, rfl, rfl, hl, hext', hy⟩ := split_last hx hne hlex hext
    exact ⟨_, _, mkApps_snoc _ _ _, .cases hco hid hpre halts hm hbrs hcf halt hl hext', hy⟩
  | @casesReduced _ d c iv cn cv alt alt' us pre extra extra' hd hco hcs hcv hidx hpre halt hlex
      hext =>
    have hne : extra ≠ [] := by
      rintro rfl
      exact hns (shortSpine_of hx (specialArity_casesOn hco) (by simp [hpre, hcs, casesArity]))
    obtain ⟨ex, ex', y, rfl, rfl, rfl, hl, hext', hy⟩ := split_last hx hne hlex hext
    exact ⟨_, _, by rw [← List.append_assoc, mkApps_snoc],
      .casesReduced hd hco hcs hcv hidx hpre halt hl hext', hy⟩
  | @quotMk c qv _ b b' us α r extra extra' hc hk hb hlex hext =>
    have hne : extra ≠ [] := by
      rintro rfl
      exact hns (shortSpine_of (ar := 3) hx (by simp [specialArity, hc, hk, quotEvalArity]) (by simp))
    obtain ⟨ex, ex', y, rfl, rfl, rfl, hl, hext', hy⟩ := split_last hx hne hlex hext
    exact ⟨_, _, mkApps_snoc _ _ _, .quotMk hc hk hb hl hext', hy⟩
  | @quotLift c qv _ g g' q q' us α r β hh extra extra' hc hk hg hq hlex hext =>
    have hne : extra ≠ [] := by
      rintro rfl
      exact hns (shortSpine_of (ar := 6) hx (by simp [specialArity, hc, hk, quotEvalArity]) (by simp))
    obtain ⟨ex, ex', y, rfl, rfl, rfl, hl, hext', hy⟩ := split_last hx hne hlex hext
    exact ⟨_, _, by rw [← List.cons_append, mkApps_snoc], .quotLift hc hk hg hq hl hext', hy⟩
  | @recLet c rv minors F _ maj maj' us ps ms mins is extra mins' is' extra' hc hF hps hms hmins his
      hlm hmin hli his' hmaj hlex hext =>
    have hne : extra ≠ [] := by
      rintro rfl
      exact hns (shortSpine_of (ar := rv.numParams + rv.numMotives + rv.numMinors + rv.numIndices + 1)
        hx (by simp [specialArity, hc]) (by simp [hps, hms, hmins, his]; omega))
    obtain ⟨ex, ex', y, rfl, rfl, rfl, hl, hext', hy⟩ := split_last hx hne hlex hext
    exact ⟨_, _, mkApps_snoc _ _ _, .recLet hc hF hps hms hmins his hlm hmin hli his' hmaj hl hext', hy⟩
  | @recFix c rv minors F _ maj maj' us ps ms mins is extra ws is' extra' hc hF hps hms hmins his hlw
      hmin hws hli his' hmaj hlex hext =>
    have hne : extra ≠ [] := by
      rintro rfl
      exact hns (shortSpine_of (ar := rv.numParams + rv.numMotives + rv.numMinors + rv.numIndices + 1)
        hx (by simp [specialArity, hc]) (by simp [hps, hms, hmins, his]; omega))
    obtain ⟨ex, ex', y, rfl, rfl, rfl, hl, hext', hy⟩ := split_last hx hne hlex hext
    exact ⟨_, _, by rw [← List.append_assoc, mkApps_snoc],
      .recFix hc hF hps hms hmins his hlw hmin hws hli his' hmaj hl hext', hy⟩
  | bvar | fvar | lam | etaLam | letE | const | proj | litZero | litSucc | box => cases hx

/-- An erasure of a constructor spine is the λ□ constructor applied to erasures of the arguments,
of an inductive not declared in `Prop`, with at least the constructor's arity of arguments (a
constructor spine erases by `Erases.ctor` only). Adapted from `ML-V Relation/Basic.lean:432`.
Reference: the `tConstruct` inversion of `erases` (`MR E/Extract.v:106`), `erases_mkApps_inv`
(`MR E/ErasureProperties.v:105`). -/
theorem Erases.ctor_inv {Γ : List CtxBinder} {c : Name} {cv : ConstructorVal} {us : List Level}
    {as : List Expr} {tb : LBTerm} (hc : findDecl σ.decls c = some (.ctorInfo cv))
    (h : Erases cert σ Γ (mkAppN (.const c us) as.toArray) tb) :
    ∃ iid as', IndIdOf σ cv.induct = some iid ∧ tb = mkApps (.construct iid cv.cidx []) as' ∧
      as.length = as'.length ∧
      (∀ (i : Nat) a a', as[i]? = some a → as'[i]? = some a' → Erases cert σ Γ a a') ∧
      σ.propInd cv.induct = false ∧ cv.numParams + cv.numFields ≤ as.length := by
  generalize hx : mkAppN (.const c us) as.toArray = x at h
  have hfn : x.getAppFn = .const c us := hx ▸ getAppFn_mkAppN_const c us as
  cases h with
  | ctor hc' hp hid hle hlen hall =>
    obtain ⟨rfl, rfl, rfl⟩ := mkAppN_const_inj hx
    rw [hc] at hc'; cases hc'
    exact ⟨_, _, hid, rfl, hlen, hall, hp, hle⟩
  | quotMk hq | quotLift hq | recLet hq | recFix hq =>
    obtain ⟨rfl, -, -⟩ := mkAppN_const_inj hx
    rw [hc] at hq; cases hq
  | cases hco | casesReduced _ hco =>
    obtain ⟨rfl, -, -⟩ := mkAppN_const_inj hx
    obtain ⟨d, hd⟩ := casesOn?_defn hco
    rw [hc] at hd; cases hd
  | app hns => exact absurd ⟨c, us, hfn, .inl ⟨cv, hc⟩⟩ hns
  | const _ hsa => cases hfn; rw [specialArity_ctor hc] at hsa; cases hsa
  | bvar | fvar | lam | etaLam | letE | proj | litZero | litSucc | box => cases hfn

/-- An erasure of a recognized `casesOn` spine is a λ□ `case` on an erasure of the major premise
with one erased alternative per constructor, applied to erasures of the extra arguments
(`Erases.cases`), or the erased alternative applied to `□` for each field and to the extra
arguments, the discriminant `reduced`-marked and certified (`Erases.casesReduced`). Adapted from
`ML-V Relation/Basic.lean:492`. Reference: the `tCase` inversion of `erases`
(`MR E/Extract.v:109`), `erases_mkApps_inv` (`MR E/ErasureProperties.v:105`). -/
theorem Erases.cases_inv {Γ : List CtxBinder} {c : Name} {iv : InductiveVal} {us : List Level}
    {as : List Expr} {tb : LBTerm} (hc : σ.casesOn? c = some iv)
    (h : Erases cert σ Γ (mkAppN (.const c us) as.toArray) tb) :
    (∃ pre maj alts extra iid maj' brs extra', as = pre ++ [maj] ++ alts ++ extra ∧
      IndIdOf σ iv.name = some iid ∧ pre.length = casesMajor iv ∧ alts.length = iv.ctors.length ∧
      Erases cert σ Γ maj maj' ∧ brs.length = alts.length ∧
      (∀ (i : Nat) cn, iv.ctors[i]? = some cn → (ctorFields σ cn).isSome) ∧
      (∀ (i : Nat) cn alt br k, iv.ctors[i]? = some cn → alts[i]? = some alt → brs[i]? = some br →
        ctorFields σ cn = some k → ErasesAlt cert σ Γ k alt br) ∧
      extra.length = extra'.length ∧
      (∀ (i : Nat) a a', extra[i]? = some a → extra'[i]? = some a' → Erases cert σ Γ a a') ∧
      tb = mkApps (.case (iid, iv.numParams) maj' brs) extra') ∨
    (∃ pre d alt extra cn cv alt' extra', as = pre ++ [markReduced d] ++ [alt] ++ extra ∧
      cert Γ d ∧ iv.ctors = [cn] ∧ findDecl σ.decls cn = some (.ctorInfo cv) ∧
      (indexFields cv.numParams cv.type).all (·.isNone) = true ∧ pre.length = casesMajor iv ∧
      Erases cert σ Γ alt alt' ∧ extra.length = extra'.length ∧
      (∀ (i : Nat) a a', extra[i]? = some a → extra'[i]? = some a' → Erases cert σ Γ a a') ∧
      tb = mkApps alt' (List.replicate cv.numFields .box ++ extra')) := by
  generalize hx : mkAppN (.const c us) as.toArray = x at h
  have hfn : x.getAppFn = .const c us := hx ▸ getAppFn_mkAppN_const c us as
  obtain ⟨dv, hdv⟩ := casesOn?_defn hc
  cases h with
  | cases hco hid hpre halts hm hbrs hcf halt hlex hext =>
    obtain ⟨rfl, rfl, rfl⟩ := mkAppN_const_inj hx
    rw [hc] at hco; cases hco
    exact .inl ⟨_, _, _, _, _, _, _, _, rfl, hid, hpre, halts, hm, hbrs, hcf, halt, hlex, hext, rfl⟩
  | casesReduced hd hco hcs hcv hidx hpre ha hlex hext =>
    obtain ⟨rfl, rfl, rfl⟩ := mkAppN_const_inj hx
    rw [hc] at hco; cases hco
    exact .inr ⟨_, _, _, _, _, _, _, _, rfl, hd, hcs, hcv, hidx, hpre, ha, hlex, hext, rfl⟩
  | ctor hq | quotMk hq | quotLift hq | recLet hq | recFix hq =>
    obtain ⟨rfl, -, -⟩ := mkAppN_const_inj hx
    rw [hq] at hdv; cases hdv
  | app hns => exact absurd ⟨c, us, hfn, .inr (.inl (by rw [hc]; rfl))⟩ hns
  | const _ hsa => cases hfn; rw [specialArity_casesOn hc] at hsa; cases hsa
  | bvar | fvar | lam | etaLam | letE | proj | litZero | litSucc | box => cases hfn

end

end EraseProof
