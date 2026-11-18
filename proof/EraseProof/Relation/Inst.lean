import EraseProof.Relation.Basic

/-!
# Substitution and universe instantiation in the erasure relation

`Erases.inst`, `ErasesAlt.inst`, `Erases.inst_let`: instantiating the innermost bound variable of
an erased body by a term without loose indices, on the Lean side, and substituting the term's
erasure, on the λ□ side, keeps the erasure (`MR E/ESubstitution.v:612 erases_subst0`).
`Erases.instLevels`: instantiating universe parameters keeps the erasure
(`MR E/ErasureProperties.v:383 erases_subst_instance`). Adapted from `ML-V Relation/Inst.lean` and
`ML-V Relation/Levels.lean`, without typing premises: the relation reads no type and no level,
and a substituted head that is a special spine takes the body's arguments as extra arguments of
its own rule (`Erases.appS`), so no premise excludes it.

The lemmas are stated for `noCert`, the relation of the simulation `erases_correct_statement`:
the context and the certificate of a mark are not transported. `CLCert env Γ s` is a fuelled run
of con-leche's inference on `s` under `Γ`; con-leche has no substitution or universe-instantiation
lemma for it, so an instantiated mark is not known to be certified. The certified relation
`Erases (CLCert env)` is the conclusion of the final theorem, about the emitted program, and is
never instantiated.
-/

open Lean Erasure

namespace EraseProof

/-! ## Instantiating source terms -/

/-- Instantiation commutes with the left fold of applications. Copy of
`ML-V Relation/Inst.lean:229`. -/
theorem inst_foldl (a f : Expr) (as : List Expr) (d : Nat) :
    (as.foldl .app f).instantiate1' a d =
      (as.map (·.instantiate1' a d)).foldl .app (f.instantiate1' a d) := by
  induction as generalizing f with
  | nil => rfl
  | cons x as ih => simp [ih, Expr.instantiate1']

/-- Instantiation of a constant spine. Copy of `ML-V Relation/Inst.lean:236`. -/
theorem inst_spine (a : Expr) (d : Nat) (c : Name) (us : List Level) (as : List Expr) :
    (mkAppN (.const c us) as.toArray).instantiate1' a d =
      mkAppN (.const c us) (as.map (·.instantiate1' a d)).toArray := by
  rw [mkAppN_toArray, inst_foldl, ← mkAppN_toArray]; rfl

/-- A term without loose indices from `c` on is unchanged by lifting from `c`. Copy of
`ML-V Relation/Inst.lean:216`. -/
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

/-- Universe instantiation commutes with the left fold of applications. Copy of
`ML-V Bridge/Levels.lean:141`. -/
theorem instLevels_foldl (ps : List Name) (us : List Level) (f : Expr) (as : List Expr) :
    Pure.instLevels ps us (as.foldl .app f) =
      (as.map (Pure.instLevels ps us)).foldl .app (Pure.instLevels ps us f) := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih => simp [ih, Pure.instLevels]

/-- Universe instantiation of a spine. Copy of `ML-V Relation/Levels.lean:361`. -/
theorem instLevels_mkAppN (ps : List Name) (us : List Level) (f : Expr) (as : List Expr) :
    Pure.instLevels ps us (mkAppN f as.toArray) =
      mkAppN (Pure.instLevels ps us f) (as.map (Pure.instLevels ps us)).toArray := by
  rw [mkAppN_toArray, instLevels_foldl, ← mkAppN_toArray]

/-- `csubstB` substitutes in each branch under its binders. Copy of
`ML-V Relation/Inst.lean:412`. -/
theorem csubstB_eq (t : LBTerm) (k : Nat) :
    ∀ brs : List (List BinderName × LBTerm),
      csubstB t k brs = brs.map fun br => (br.1, csubst t (k + br.1.length) br.2)
  | [] => by simp [csubstB]
  | (ns, b) :: brs => by simp [csubstB, csubstB_eq t k brs]

/-- A pointwise relation between lists carries over to their images. -/
theorem forall_map {α β : Type} {R S : α → β → Prop} {l : List α} {l' : List β} {f : α → α}
    {g : β → β} (h : ∀ (i : Nat) a b, l[i]? = some a → l'[i]? = some b → R a b)
    (hRS : ∀ a b, R a b → S (f a) (g b)) :
    ∀ (i : Nat) a b, (l.map f)[i]? = some a → (l'.map g)[i]? = some b → S a b := by
  intro i a b ha hb
  rw [List.getElem?_map] at ha hb
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 ha
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hb
  exact hRS x y (h i x y hx hy)

/-! ## Substitution -/

section
variable {σ : EvalEnv}

open TargetSubst TargetLift RecLam in
/-- Substitution of a term `a` without loose indices, erased to `a'`, for the bound variable `d`
of an erased term, in any context. -/
theorem Erases.instG {a : Expr} {a' : LBTerm} {Γa : List CtxBinder}
    (ha : Erases noCert σ Γa a a') (hla : AbsFV.LBV 0 a) :
    ∀ {Γ : List CtxBinder} {e : Expr} {t : LBTerm}, Erases noCert σ Γ e t →
      ∀ (d : Nat) (Γ' : List CtxBinder),
        Erases noCert σ Γ' (e.instantiate1' a d) (csubst a' d t) := by
  have hcl : closedn 0 a' = true := Erases.closed hla ha
  intro Γ e t h
  refine Erases.rec (motive_1 := fun _ e t _ => ∀ (d : Nat) (Γ' : List CtxBinder),
      Erases noCert σ Γ' (e.instantiate1' a d) (csubst a' d t))
    (motive_2 := fun _ k e br _ => ∀ (d : Nat) (Γ' : List CtxBinder),
      ErasesAlt noCert σ Γ' k (e.instantiate1' a d) (br.1, csubst a' (d + br.1.length) br.2))
    ?bvar ?fvar ?lam ?etaLam ?letE ?app ?const ?ctor ?cases ?casesReduced ?proj ?litZero ?litSucc
    ?quotMk ?quotLift ?recLet ?recFix ?box ?done ?alam ?aeta h
  case bvar =>
    intro _ i d Γ'
    simp only [Expr.instantiate1', csubst]
    rcases Nat.lt_trichotomy i d with h1 | rfl | h1
    · simp only [h1, ite_true, show d ≠ i by omega, show ¬ d < i by omega, ite_false]; exact .bvar
    · simp only [Nat.lt_irrefl, ite_false, ite_true, lift_closed hla]; exact ha.ctx Γ'
    · simp only [show ¬ i < d by omega, show i ≠ d by omega, show d ≠ i by omega, h1, ite_true,
        ite_false]
      exact .bvar
  case fvar => intros; exact .fvar
  case lam => intro _ _ _ _ _ _ _ ih d Γ'; exact .lam (ih _ _)
  case etaLam => intro _ _ _ _ _ _ _ ih d Γ'; exact .etaLam (ih _ _)
  case letE => intro _ _ _ _ _ _ _ _ _ _ ihv ihb d Γ'; exact .letE (ihv _ _) (ihb _ _)
  case app => intro _ _ _ _ _ _ _ _ ihf iha d Γ'; exact (ihf d Γ').appS (iha d Γ')
  case const => intro _ _ _ h1 h2 h3 d Γ'; exact .const h1 h2 h3
  case ctor =>
    intro _ _ _ _ _ _ _ hc hp hid hle hlen _ ih d Γ'
    rw [inst_spine, csubst_mkApps]
    exact .ctor hc hp hid (by simpa using hle) (by simpa using hlen)
      (forall_map ih fun _ _ h => h d Γ')
  case cases =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ hco hid hpre halts _ hbrs hcf _ hlex _ ihm iha ihe d Γ'
    rw [inst_spine, csubst_mkApps]
    simp only [List.map_append, List.map_cons, List.map_nil, csubst, csubstB_eq]
    refine .cases hco hid (by simpa using hpre) (by simpa using halts) (ihm d Γ')
      (by simpa using hbrs) hcf (fun i cn alt br k h1 h2 h3 h4 => ?_) (by simpa using hlex)
      (forall_map ihe fun _ _ h => h d Γ')
    rw [List.getElem?_map] at h2 h3
    obtain ⟨alt₀, h2', rfl⟩ := Option.map_eq_some_iff.1 h2
    obtain ⟨br₀, h3', rfl⟩ := Option.map_eq_some_iff.1 h3
    exact iha i cn alt₀ br₀ k h1 h2' h3' h4 d Γ'
  case casesReduced =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ hco hcs hcv hidx hpre _ hlex _ iha ihe d Γ'
    rw [inst_spine, csubst_mkApps]
    simp only [List.map_append, List.map_cons, List.map_nil, List.map_replicate, csubst]
    exact .casesReduced trivial hco hcs hcv hidx (by simpa using hpre) (iha d Γ')
      (by simpa using hlex) (forall_map ihe fun _ _ h => h d Γ')
  case proj => intro _ _ _ _ _ _ _ h1 h2 h3 _ ih d Γ'; exact .proj h1 h2 h3 (ih d Γ')
  case litZero => intro _ _ h d Γ'; exact .litZero h
  case litSucc => intro _ _ _ _ h _ ih d Γ'; exact .litSucc h (ih d Γ')
  case quotMk =>
    intro _ _ _ _ _ _ _ _ _ _ hc hk _ hlex _ iha ihe d Γ'
    rw [inst_spine, csubst_mkApps]
    simp only [List.map_append, List.map_cons, List.map_nil]
    exact .quotMk hc hk (iha d Γ') (by simpa using hlex) (forall_map ihe fun _ _ h => h d Γ')
  case quotLift =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hk _ _ hlex _ ihf ihq ihe d Γ'
    rw [inst_spine, csubst_mkApps]
    simp only [List.map_append, List.map_cons, List.map_nil]
    exact .quotLift hc hk (ihf d Γ') (ihq d Γ') (by simpa using hlex)
      (forall_map ihe fun _ _ h => h d Γ')
  case recLet =>
    intro _ rv minors F _ _ maj' _ _ _ _ _ _ mins' is' extra' hc hF hps hms hmins his hlm _ hli _ _ hle
      _ ihmin ihis ihmaj ihext d Γ'
    obtain ⟨_, _, _, _, _, _, _, _, -, -, hml, -, -, -, -, -, -, hFc, -⟩ := id hF
    have hz : (mins'.zip minors).length = rv.numMinors := by
      simp only [List.length_zip]; omega
    have := csubst_recLetTerm hcl d rv.numMinors (maj' := maj') (is' := is') (extra' := extra') hz hFc
    simp only [recLetTerm] at this
    rw [inst_spine, this]
    simp only [List.map_append (f := fun x : Expr => x.instantiate1' a d), List.map_cons,
      List.map_nil]
    exact .recLet hc hF (by simpa using hps) (by simpa using hms) (by simpa using hmins)
      (by simpa using his) (by simpa using hlm) (forall_map ihmin fun _ _ h => h d Γ')
      (by simpa using hli) (forall_map ihis fun _ _ h => h d Γ') (ihmaj d Γ') (by simpa using hle)
      (forall_map ihext fun _ _ h => h d Γ')
  case recFix =>
    intro _ rv minors F _ _ _ _ _ _ _ _ _ ws _ _ hc hF hps hms hmins his hlw _ hws hli _ _ hle _
      ihmin ihis ihmaj ihext d Γ'
    obtain ⟨_, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, -, hFc, -⟩ := id hF
    have hs := closedn_substl ws.reverse F 0 (fun w hw => (hws w (List.mem_reverse.1 hw)).1)
      (by simpa [← hlw, hmins] using hFc)
    rw [inst_spine, csubst_mkApps, csubst_closedn a' _ 0 d hs (Nat.zero_le _)]
    simp only [List.map_append, List.map_cons, List.map_nil]
    refine .recFix hc hF (by simpa using hps) (by simpa using hms) (by simpa using hmins)
      (by simpa using his) (by simpa using hlw) (fun i x w h1 h2 => ?_) hws (by simpa using hli)
      (forall_map ihis fun _ _ h => h d Γ') (ihmaj d Γ') (by simpa using hle)
      (forall_map ihext fun _ _ h => h d Γ')
    rw [List.getElem?_map] at h1
    obtain ⟨x₀, h1', rfl⟩ := Option.map_eq_some_iff.1 h1
    have := ihmin i x₀ w h1' h2 d Γ'
    rwa [csubst_closedn a' w 0 d (hws w (List.mem_of_getElem? h2)).1 (Nat.zero_le _)] at this
  case box => intros; exact .box trivial
  case done => intro _ _ _ _ ih d Γ'; exact .done (ih d Γ')
  case alam =>
    intro A _ _ _ ns _ _ _ _ ih d Γ'
    have := ih (d + 1) ((A.instantiate1' a d, none) :: Γ')
    rw [show d + 1 + ns.length = d + (ns.length + 1) by omega] at this
    exact .lam this
  case aeta =>
    intro A _ _ _ ns _ _ _ _ ih d Γ'
    have := ih (d + 1) ((A.instantiate1' a d, none) :: Γ')
    rw [show d + 1 + ns.length = d + (ns.length + 1) by omega] at this
    exact .etaLam this

/-- Substitution of a term without loose indices for the innermost λ-bound variable of an erased
body: the erasure of the instantiated body is the closed substitution of the term's erasure into
the body's erasure. Adapted from `ML-V Relation/Inst.lean:1654`: no typing premise and no value
premise; the term's erasure is closed by `Erases.closed`. Reference: `erases_subst0`
(`MR E/ESubstitution.v:612`). -/
theorem Erases.inst {Γ : List CtxBinder} {A a b : Expr} {a' b' : LBTerm}
    (hb : Erases noCert σ ((A, none) :: Γ) b b') (ha : Erases noCert σ Γ a a')
    (hla : AbsFV.LBV 0 a) : Erases noCert σ Γ (b.instantiate1' a) (csubst a' 0 b') :=
  Erases.instG ha hla hb 0 Γ

/-- Substitution of a term without loose indices for the variable of a `let` body (`SrcEval.zeta`
substitutes the value of the `let` value, not the value itself). Adapted from
`ML-V Simulation/Cases.lean:622 SimCases.inst_let`. Reference: `erases_subst0`
(`MR E/ESubstitution.v:612`). -/
theorem Erases.inst_let {Γ : List CtxBinder} {T v a b : Expr} {a' b' : LBTerm}
    (hb : Erases noCert σ ((T, some v) :: Γ) b b') (ha : Erases noCert σ Γ a a')
    (hla : AbsFV.LBV 0 a) : Erases noCert σ Γ (b.instantiate1' a) (csubst a' 0 b') :=
  Erases.instG ha hla hb 0 Γ

/-- Substitution of a term without loose indices into a `casesOn` alternative erased under its
field binders: the branch's body is substituted below the field binders. Adapted from
`ML-V Relation/Inst.lean:1676`. Reference: `erases_subst0` (`MR E/ESubstitution.v:612`) on the
branches of `MR E/Extract.v:109 erases_tCase`. -/
theorem ErasesAlt.inst {Γ : List CtxBinder} {A a b : Expr} {a' t : LBTerm} {k : Nat}
    {ns : List BinderName} (hb : ErasesAlt noCert σ ((A, none) :: Γ) k b (ns, t))
    (ha : Erases noCert σ Γ a a') (hla : AbsFV.LBV 0 a) :
    ErasesAlt noCert σ Γ k (b.instantiate1' a) (ns, csubst a' ns.length t) := by
  suffices key : ∀ k {Γ₀ : List CtxBinder} {b : Expr} {br : List BinderName × LBTerm},
      ErasesAlt noCert σ Γ₀ k b br → ∀ (d : Nat) (Γ' : List CtxBinder),
        ErasesAlt noCert σ Γ' k (b.instantiate1' a d) (br.1, csubst a' (d + br.1.length) br.2) by
    simpa using key k hb 0 Γ
  intro k
  induction k with
  | zero =>
    intro _ _ _ h d Γ'
    cases h with
    | done h => exact .done (Erases.instG ha hla h d Γ')
  | succ k ih =>
    intro _ _ _ h d Γ'
    cases h with
    | @lam A _ _ _ ns _ _ _ h =>
      have := ih h (d + 1) ((A.instantiate1' a d, none) :: Γ')
      rw [show d + 1 + ns.length = d + (ns.length + 1) by omega] at this
      exact .lam this
    | @etaLam A _ _ _ ns _ _ _ h =>
      have := ih h (d + 1) ((A.instantiate1' a d, none) :: Γ')
      rw [show d + 1 + ns.length = d + (ns.length + 1) by omega] at this
      exact .etaLam this

/-! ## Universe instantiation -/

/-- Universe instantiation keeps the erasure: the relation reads no level. Adapted from
`ML-V Relation/Levels.lean:790`, without the translation premise. Reference:
`erases_subst_instance` (`MR E/ErasureProperties.v:383`). -/
theorem Erases.instLevels {Γ : List CtxBinder} {ps : List Name} {us : List Level} {e : Expr}
    {tb : LBTerm} (h : Erases noCert σ Γ e tb) (Γ' : List CtxBinder) :
    Erases noCert σ Γ' (Pure.instLevels ps us e) tb := by
  refine Erases.rec (motive_1 := fun _ e t _ => ∀ Γ', Erases noCert σ Γ' (Pure.instLevels ps us e) t)
    (motive_2 := fun _ k e br _ => ∀ Γ', ErasesAlt noCert σ Γ' k (Pure.instLevels ps us e) br)
    ?bvar ?fvar ?lam ?etaLam ?letE ?app ?const ?ctor ?cases ?casesReduced ?proj ?litZero ?litSucc
    ?quotMk ?quotLift ?recLet ?recFix ?box ?done ?alam ?aeta h Γ'
  case bvar => intros; exact .bvar
  case fvar => intros; exact .fvar
  case lam => intro _ _ _ _ _ _ _ ih Γ'; exact .lam (ih _)
  case etaLam => intro _ _ _ _ _ _ _ ih Γ'; exact .etaLam (ih _)
  case letE => intro _ _ _ _ _ _ _ _ _ _ ihv ihb Γ'; exact .letE (ihv _) (ihb _)
  case app => intro _ _ _ _ _ _ _ _ ihf iha Γ'; exact (ihf Γ').appS (iha Γ')
  case const => intro _ _ _ h1 h2 h3 Γ'; exact .const h1 h2 h3
  case ctor =>
    intro _ _ _ _ _ _ _ hc hp hid hle hlen _ ih Γ'
    rw [instLevels_mkAppN]
    exact .ctor hc hp hid (by simpa using hle) (by simpa using hlen)
      (by simpa using forall_map (g := id) ih fun _ _ h => h Γ')
  case cases =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ hco hid hpre halts _ hbrs hcf _ hlex _ ihm iha ihe Γ'
    rw [instLevels_mkAppN]
    simp only [List.map_append (f := Pure.instLevels ps us), List.map_cons, List.map_nil]
    refine .cases hco hid (by simpa using hpre) (by simpa using halts) (ihm Γ')
      (by simpa using hbrs) hcf (fun i cn alt br k h1 h2 h3 h4 => ?_) (by simpa using hlex)
      (by simpa using forall_map (g := id) ihe fun _ _ h => h Γ')
    rw [List.getElem?_map] at h2
    obtain ⟨alt₀, h2', rfl⟩ := Option.map_eq_some_iff.1 h2
    exact iha i cn alt₀ br k h1 h2' h3 h4 Γ'
  case casesReduced =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ hco hcs hcv hidx hpre _ hlex _ iha ihe Γ'
    rw [instLevels_mkAppN]
    simp only [List.map_append (f := Pure.instLevels ps us), List.map_cons, List.map_nil]
    exact .casesReduced trivial hco hcs hcv hidx (by simpa using hpre) (iha Γ')
      (by simpa using hlex) (by simpa using forall_map (g := id) ihe fun _ _ h => h Γ')
  case proj => intro _ _ _ _ _ _ _ h1 h2 h3 _ ih Γ'; exact .proj h1 h2 h3 (ih Γ')
  case litZero => intro _ _ h Γ'; exact .litZero h
  case litSucc => intro _ _ _ _ h _ ih Γ'; exact .litSucc h (ih Γ')
  case quotMk =>
    intro _ _ _ _ _ _ _ _ _ _ hc hk _ hlex _ iha ihe Γ'
    rw [instLevels_mkAppN]
    simp only [List.map_append (f := Pure.instLevels ps us), List.map_cons, List.map_nil]
    exact .quotMk hc hk (iha Γ') (by simpa using hlex)
      (by simpa using forall_map (g := id) ihe fun _ _ h => h Γ')
  case quotLift =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hk _ _ hlex _ ihf ihq ihe Γ'
    rw [instLevels_mkAppN]
    simp only [List.map_append (f := Pure.instLevels ps us), List.map_cons, List.map_nil]
    exact .quotLift hc hk (ihf Γ') (ihq Γ') (by simpa using hlex)
      (by simpa using forall_map (g := id) ihe fun _ _ h => h Γ')
  case recLet =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hF hps hms hmins his hlm _ hli _ _ hle _
      ihmin ihis ihmaj ihext Γ'
    rw [instLevels_mkAppN]
    simp only [List.map_append (f := Pure.instLevels ps us), List.map_cons, List.map_nil]
    exact .recLet hc hF (by simpa using hps) (by simpa using hms) (by simpa using hmins)
      (by simpa using his) (by simpa using hlm)
      (by simpa using forall_map (g := id) ihmin fun _ _ h => h Γ') (by simpa using hli)
      (by simpa using forall_map (g := id) ihis fun _ _ h => h Γ') (ihmaj Γ') (by simpa using hle)
      (by simpa using forall_map (g := id) ihext fun _ _ h => h Γ')
  case recFix =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hF hps hms hmins his hlw _ hws hli _ _ hle _
      ihmin ihis ihmaj ihext Γ'
    rw [instLevels_mkAppN]
    simp only [List.map_append (f := Pure.instLevels ps us), List.map_cons, List.map_nil]
    exact .recFix hc hF (by simpa using hps) (by simpa using hms) (by simpa using hmins)
      (by simpa using his) (by simpa using hlw)
      (by simpa using forall_map (g := id) ihmin fun _ _ h => h Γ') hws (by simpa using hli)
      (by simpa using forall_map (g := id) ihis fun _ _ h => h Γ') (ihmaj Γ') (by simpa using hle)
      (by simpa using forall_map (g := id) ihext fun _ _ h => h Γ')
  case box => intros; exact .box trivial
  case done => intro _ _ _ _ ih Γ'; exact .done (ih Γ')
  case alam => intro _ _ _ _ _ _ _ _ _ ih Γ'; exact .lam (ih _)
  case aeta => intro _ _ _ _ _ _ _ _ _ ih Γ'; exact .etaLam (ih _)

end

end EraseProof
