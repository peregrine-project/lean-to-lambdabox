import EraseProof.Relation.Basic

/-!
# Closing a binder in the erasure relation

The traversal opens a binder with a fresh free variable `x`, erases the opened body to `tb` and
closes the result with `abstract x tb = toBvar x 0 tb` (`LeanToLambdaBox/Basic.lean:149`), which
does not shift loose indices; `MarkOf` closes the opened marking `bM` with `absFV x 0 bM`.
`Erases.abstract`: when `tb` is closed, `absFV x 0 bM` erases to `abstract x tb`, for the body of
a λ, of a `let` and of an η-introduced λ alike. `ErasesAlt.absN`: the same for an alternative
under its field binders at any depth, as `mkAlt` (`LeanToLambdaBox/Erasure.lean:563`) abstracts
its fields one depth each. The induction abstracts `x` into the bound variable `d` on the source
side (`absFV x d`) and replaces `x` by the index `d` on the λ□ side (`toBvar x d`). Adapted from
`ML-V Relation/Abstract.lean:413 Erases.absN` and `ML-V Core/StepsCasesCase.lean:91
ErasesAlt.absN`: without certificates the binder context is irrelevant, so no relation between
the contexts is needed, and the relation has no fix variables. Reference: `Erases.uninstantiateN`
(`L4 Relation/Abstract.lean:170`); none in MetaRocq (DV-13).
-/

open Lean Erasure

namespace EraseProof

namespace AbsFV

/-- Abstraction commutes with the left fold of applications. Copy of
`ML-V Bridge/Abstract.lean:57`. -/
theorem absFV_foldl (x : FVarId) (d : Nat) (f : Expr) (as : List Expr) :
    absFV x d (as.foldl .app f) = (as.map (absFV x d)).foldl .app (absFV x d f) := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih => simp [ih, absFV]

/-- Abstraction of a constant spine. -/
theorem absFV_spine (x : FVarId) (d : Nat) (c : Name) (us : List Level) (as : List Expr) :
    absFV x d (mkAppN (.const c us) as.toArray) =
      mkAppN (.const c us) (as.map (absFV x d)).toArray := by
  rw [mkAppN_toArray, absFV_foldl, ← mkAppN_toArray]; rfl

/-- `toBvarAlts` abstracts in each branch under its binders. Copy of
`ML-V Relation/Abstract.lean:287`. -/
theorem toBvarAlts_eq (x : FVarId) (d : Nat) :
    ∀ brs : List (List BinderName × LBTerm),
      _root_.toBvarAlts x d brs = brs.map fun br => (br.1, _root_.toBvar x (d + br.1.length) br.2)
  | [] => by simp [_root_.toBvarAlts]
  | (ns, b) :: brs => by simp [_root_.toBvarAlts, toBvarAlts_eq x d brs]

/-- A branch of closed branches is closed under its binders. Copy of
`ML-V Relation/Abstract.lean:300`. -/
theorem closednB_get {k : Nat} : ∀ {brs : List (List BinderName × LBTerm)} {i : Nat}
    {br : List BinderName × LBTerm}, closednB k brs = true → brs[i]? = some br →
      closedn (k + br.1.length) br.2 = true
  | [], _, _, _, h => by cases h
  | (ns, b) :: brs, 0, br, hc, h => by
    simp only [closednB, Bool.and_eq_true] at hc
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h; exact hc.1
  | (ns, b) :: brs, i + 1, br, hc, h => by
    simp only [closednB, Bool.and_eq_true] at hc
    simp only [List.getElem?_cons_succ] at h
    exact closednB_get hc.2 h

end AbsFV

section
variable {σ : EvalEnv}

open TargetLift RecLam in
/-- Abstracting `x` into the bound variable `d`, on both sides, keeps the erasure, in any context,
when the λ□ term has no loose index from `d` on. Adapted from `ML-V Relation/Abstract.lean:413`. -/
theorem Erases.absN (x : FVarId) {Γ : List CtxBinder} {e : Expr} {tb : LBTerm}
    (h : Erases noCert σ Γ e tb) :
    ∀ (d : Nat) (Γ' : List CtxBinder), closedn d tb = true →
      Erases noCert σ Γ' (absFV x d e) (_root_.toBvar x d tb) := by
  have gmap : ∀ {d : Nat} {l : List Expr} {i : Nat} {y : Expr},
      (l.map (absFV x d))[i]? = some y → ∃ y₀, l[i]? = some y₀ ∧ absFV x d y₀ = y := fun h => by
    simpa only [List.getElem?_map, Option.map_eq_some_iff] using h
  have gmapB : ∀ {d : Nat} {l : List LBTerm} {i : Nat} {y : LBTerm},
      (l.map (_root_.toBvar x d))[i]? = some y → ∃ y₀, l[i]? = some y₀ ∧ _root_.toBvar x d y₀ = y :=
    fun h => by simpa only [List.getElem?_map, Option.map_eq_some_iff] using h
  have hc0 : ∀ d iid i, _root_.toBvar x d (.construct iid i []) = .construct iid i [] :=
    fun _ _ _ => rfl
  refine Erases.rec (motive_1 := fun _ e tb _ => ∀ (d : Nat) (Γ' : List CtxBinder),
      closedn d tb = true → Erases noCert σ Γ' (absFV x d e) (_root_.toBvar x d tb))
    (motive_2 := fun _ k e br _ => ∀ (d : Nat) (Γ' : List CtxBinder),
      closedn (d + br.1.length) br.2 = true →
      ErasesAlt noCert σ Γ' k (absFV x d e) (br.1, _root_.toBvar x (d + br.1.length) br.2))
    ?bvar ?fvar ?lam ?etaLam ?letE ?app ?const ?ctor ?cases ?casesReduced ?proj ?litZero ?litSucc
    ?quotMk ?quotLift ?recLet ?recFix ?box ?done ?alam ?aeta h
  case bvar =>
    intro _ i d Γ' hcl
    simp only [closedn, decide_eq_true_eq] at hcl
    simp only [absFV, _root_.toBvar, hcl, ↓reduceIte]
    exact .bvar
  case fvar =>
    intro _ y d Γ' _
    simp only [absFV, _root_.toBvar]
    split
    · exact .bvar
    · exact .fvar
  case lam => intro _ _ _ _ _ _ _ ih d Γ' hcl; exact .lam (ih (d + 1) _ hcl)
  case etaLam => intro _ _ _ _ _ _ _ ih d Γ' hcl; exact .etaLam (ih (d + 1) _ hcl)
  case letE =>
    intro _ _ _ _ _ _ _ _ _ _ ihv ihb d Γ' hcl
    simp only [closedn, Bool.and_eq_true] at hcl
    exact .letE (ihv d Γ' hcl.1) (ihb (d + 1) _ hcl.2)
  case app =>
    intro _ _ _ _ _ _ _ _ ihf iha d Γ' hcl
    simp only [closedn, Bool.and_eq_true] at hcl
    exact (ihf d Γ' hcl.1).appS (iha d Γ' hcl.2)
  case const => intro _ _ _ h1 h2 h3 d Γ' _; exact .const h1 h2 h3
  case ctor =>
    intro _ _ _ _ _ _ _ hc hp hid hle hlen _ ih d Γ' hcl
    rw [closedn_mkApps] at hcl
    rw [AbsFV.absFV_spine, toBvar_mkApps, hc0]
    refine .ctor hc hp hid (by simpa using hle) (by simpa using hlen) fun i a a' ha ha' => ?_
    obtain ⟨a₀, ha₀, rfl⟩ := gmap ha
    obtain ⟨a₀', ha₀', rfl⟩ := gmapB ha'
    exact ih i a₀ a₀' ha₀ ha₀' d Γ' (hcl.2 _ (List.mem_of_getElem? ha₀'))
  case cases =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ hco hid hpre halts _ hbrs hcf _ hlex _ ihm iha ihe d Γ' hcl
    rw [closedn_mkApps] at hcl
    obtain ⟨hcase, hext⟩ := hcl
    simp only [closedn, Bool.and_eq_true] at hcase
    rw [AbsFV.absFV_spine, toBvar_mkApps]
    simp only [List.map_append, List.map_cons, List.map_nil, _root_.toBvar]
    refine .cases hco hid (by simpa using hpre) (by simpa using halts) (ihm d Γ' hcase.1)
      (by simp [AbsFV.toBvarAlts_eq, hbrs]) hcf (fun i cn alt br k h1 h2 h3 h4 => ?_)
      (by simpa using hlex) (fun i a a' ha ha' => ?_)
    · obtain ⟨a₀, ha₀, rfl⟩ := gmap h2
      rw [AbsFV.toBvarAlts_eq, List.getElem?_map, Option.map_eq_some_iff] at h3
      obtain ⟨br₀, hbr₀, rfl⟩ := h3
      exact iha i cn a₀ br₀ k h1 ha₀ hbr₀ h4 d Γ' (AbsFV.closednB_get hcase.2 hbr₀)
    · obtain ⟨a₀, ha₀, rfl⟩ := gmap ha
      obtain ⟨a₀', ha₀', rfl⟩ := gmapB ha'
      exact ihe i a₀ a₀' ha₀ ha₀' d Γ' (hext _ (List.mem_of_getElem? ha₀'))
  case casesReduced =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ hco hcs hcv hidx hpre _ hlex _ iha ihe d Γ' hcl
    rw [closedn_mkApps] at hcl
    obtain ⟨halt, hext⟩ := hcl
    rw [AbsFV.absFV_spine, toBvar_mkApps]
    simp only [List.map_append, List.map_cons, List.map_nil, List.map_replicate]
    have hbox : _root_.toBvar x d .box = .box := rfl
    rw [hbox]
    refine .casesReduced trivial hco hcs hcv hidx (by simpa using hpre) (iha d Γ' halt)
      (by simpa using hlex) fun i a a' ha ha' => ?_
    obtain ⟨a₀, ha₀, rfl⟩ := gmap ha
    obtain ⟨a₀', ha₀', rfl⟩ := gmapB ha'
    exact ihe i a₀ a₀' ha₀ ha₀' d Γ' (hext _ (by simp [List.mem_of_getElem? ha₀']))
  case proj => intro _ _ _ _ _ _ _ h1 h2 h3 _ ih d Γ' hcl; exact .proj h1 h2 h3 (ih d Γ' hcl)
  case litZero => intro _ _ h d Γ' _; exact .litZero h
  case litSucc =>
    intro _ _ _ _ h _ ih d Γ' hcl
    simp only [closedn, Bool.and_eq_true] at hcl
    exact .litSucc h (ih d Γ' hcl.2)
  case quotMk =>
    intro _ _ _ _ _ _ _ _ _ _ hc hk _ hlex _ iha ihe d Γ' hcl
    rw [closedn_mkApps] at hcl
    obtain ⟨ha, hext⟩ := hcl
    rw [AbsFV.absFV_spine, toBvar_mkApps]
    simp only [List.map_append, List.map_cons, List.map_nil]
    refine .quotMk hc hk (iha d Γ' ha) (by simpa using hlex) fun i a a' ha ha' => ?_
    obtain ⟨a₀, ha₀, rfl⟩ := gmap ha
    obtain ⟨a₀', ha₀', rfl⟩ := gmapB ha'
    exact ihe i a₀ a₀' ha₀ ha₀' d Γ' (hext _ (List.mem_of_getElem? ha₀'))
  case quotLift =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hk _ _ hlex _ ihf ihq ihe d Γ' hcl
    rw [closedn_mkApps] at hcl
    obtain ⟨hf, hext⟩ := hcl
    rw [AbsFV.absFV_spine, toBvar_mkApps]
    simp only [List.map_append, List.map_cons, List.map_nil]
    refine .quotLift hc hk (ihf d Γ' hf) (ihq d Γ' (hext _ List.mem_cons_self))
      (by simpa using hlex) fun i a a' ha ha' => ?_
    obtain ⟨a₀, ha₀, rfl⟩ := gmap ha
    obtain ⟨a₀', ha₀', rfl⟩ := gmapB ha'
    exact ihe i a₀ a₀' ha₀ ha₀' d Γ'
      (hext _ (List.mem_cons_of_mem _ (List.mem_of_getElem? ha₀')))
  case recLet =>
    intro _ rv minors F _ _ maj' _ _ _ _ _ _ mins' is' extra' hc hF hps hms hmins his hlm _ hli _ _
      hle _ ihmin ihis ihmaj ihext d Γ' hcl
    obtain ⟨_, _, _, _, _, _, _, _, -, -, hml, -, -, -, -, -, -, -, hFx⟩ := id hF
    have hz : (mins'.zip minors).length = rv.numMinors := by
      simp only [List.length_zip]; omega
    obtain ⟨cm, ci, cj, ce⟩ := closedn_recLetTerm_inv (by omega) hz hcl
    have := toBvar_recLetTerm x d rv.numMinors (maj' := maj') (is' := is') (extra' := extra') hz hFx
    simp only [recLetTerm] at this
    rw [AbsFV.absFV_spine, this]
    simp only [List.map_append (f := absFV x d), List.map_cons, List.map_nil]
    refine .recLet hc hF (by simpa using hps) (by simpa using hms) (by simpa using hmins)
      (by simpa using his) (by simpa using hlm) (fun i a a' ha ha' => ?_) (by simpa using hli)
      (fun i a a' ha ha' => ?_) (ihmaj d Γ' cj) (by simpa using hle) (fun i a a' ha ha' => ?_)
    · obtain ⟨a₀, ha₀, rfl⟩ := gmap ha
      obtain ⟨a₀', ha₀', rfl⟩ := gmapB ha'
      exact ihmin i a₀ a₀' ha₀ ha₀' d Γ' (cm _ (List.mem_of_getElem? ha₀'))
    · obtain ⟨a₀, ha₀, rfl⟩ := gmap ha
      obtain ⟨a₀', ha₀', rfl⟩ := gmapB ha'
      exact ihis i a₀ a₀' ha₀ ha₀' d Γ' (ci _ (List.mem_of_getElem? ha₀'))
    · obtain ⟨a₀, ha₀, rfl⟩ := gmap ha
      obtain ⟨a₀', ha₀', rfl⟩ := gmapB ha'
      exact ihext i a₀ a₀' ha₀ ha₀' d Γ' (ce _ (List.mem_of_getElem? ha₀'))
  case recFix =>
    intro _ rv minors F _ _ _ _ _ _ _ _ _ ws _ _ hc hF hps hms hmins his hlw _ hws hli _ _ hle _
      ihmin ihis ihmaj ihext d Γ' hcl
    obtain ⟨_, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, -, hFc, hFx⟩ := id hF
    have hG := substl_fix (ws := ws) (by simpa [← hlw, hmins] using hFc) hFx
      fun w hw => ⟨(hws w hw).1, (hws w hw).2.1⟩
    rw [closedn_mkApps] at hcl
    obtain ⟨-, hargs⟩ := hcl
    rw [toBvar_mkApps, toBvar_noFVar x _ d (hG.2 x), AbsFV.absFV_spine]
    simp only [List.map_append, List.map_cons, List.map_nil]
    refine .recFix hc hF (by simpa using hps) (by simpa using hms) (by simpa using hmins)
      (by simpa using his) (by simpa using hlw) (fun i a a' ha ha' => ?_) hws (by simpa using hli)
      (fun i a a' ha ha' => ?_) (ihmaj d Γ' (hargs _ (by simp))) (by simpa using hle)
      (fun i a a' ha ha' => ?_)
    · obtain ⟨a₀, ha₀, rfl⟩ := gmap ha
      have hw := hws a' (List.mem_of_getElem? ha')
      have h1 := ihmin i a₀ a' ha₀ ha' d Γ' (closedn_mono _ 0 d hw.1 (Nat.zero_le _))
      rwa [toBvar_noFVar x _ d (hw.2.1 x)] at h1
    · obtain ⟨a₀, ha₀, rfl⟩ := gmap ha
      obtain ⟨a₀', ha₀', rfl⟩ := gmapB ha'
      exact ihis i a₀ a₀' ha₀ ha₀' d Γ' (hargs _ (by simp [List.mem_of_getElem? ha₀']))
    · obtain ⟨a₀, ha₀, rfl⟩ := gmap ha
      obtain ⟨a₀', ha₀', rfl⟩ := gmapB ha'
      exact ihext i a₀ a₀' ha₀ ha₀' d Γ' (hargs _ (by simp [List.mem_of_getElem? ha₀']))
  case box => intros; exact .box trivial
  case done => intro _ _ _ _ ih d Γ' hcl; exact .done (ih d Γ' hcl)
  case alam =>
    intro A _ _ _ ns _ _ _ _ ih d Γ' hcl
    have := ih (d + 1) ((absFV x d A, none) :: Γ')
      (by rw [show d + 1 + ns.length = d + (ns.length + 1) by omega]; exact hcl)
    rw [show d + 1 + ns.length = d + (ns.length + 1) by omega] at this
    exact .lam this
  case aeta =>
    intro A _ _ _ ns _ _ _ _ ih d Γ' hcl
    have := ih (d + 1) ((absFV x d A, none) :: Γ')
      (by rw [show d + 1 + ns.length = d + (ns.length + 1) by omega]; exact hcl)
    rw [show d + 1 + ns.length = d + (ns.length + 1) by omega] at this
    exact .etaLam this

/-- Closing a binder that the traversal opened with the fresh free variable `x` (`mkLambda`,
`mkLetIn`, `LeanToLambdaBox/Erasure.lean:558`; the η-introduced λs of `withAppEtaToMinArity`): if
the opened marking `bM` erases to a closed `tb`, the closed marking `absFV x 0 bM` (`MarkOf.lam`,
`MarkOf.letE`, `MarkEta.intro`) erases to `abstract x tb` (`LeanToLambdaBox/Basic.lean:149`), in any
context. Adapted from `ML-V Relation/Abstract.lean:657 Erases.abstract` and
`ML-V Core/Steps.lean:424 Erases.abstract_let`. Reference: `Erases.uninstantiateN`
(`L4 Relation/Abstract.lean:170`); none in MetaRocq (DV-13). -/
theorem Erases.abstract {Γ Γ' : List CtxBinder} {x : FVarId} {bM : Expr} {tb : LBTerm}
    (hcl : closedn 0 tb = true) (h : Erases noCert σ Γ bM tb) :
    Erases noCert σ Γ' (absFV x 0 bM) (_root_.abstract x tb) :=
  Erases.absN x h 0 Γ' hcl

/-- Abstracting `x` into the bound variable `d` keeps the erasure of an alternative under its
field binders, in any context, when the λ□ body has no loose index from `d` on below the
binders: the step of `mkAlt` (`LeanToLambdaBox/Erasure.lean:563`), which abstracts the fields one
depth each, on the alternatives that `MarkAlt` closes with `absFV`. Adapted from
`ML-V Core/StepsCasesCase.lean:91`. Reference: `Erases.uninstantiateN`
(`L4 Relation/Abstract.lean:170`); none in MetaRocq (DV-13). -/
theorem ErasesAlt.absN (x : FVarId) {Γ : List CtxBinder} {k : Nat} {e : Expr}
    {ns : List BinderName} {t : LBTerm} (h : ErasesAlt noCert σ Γ k e (ns, t)) (d : Nat)
    (Γ' : List CtxBinder) (hcl : closedn (d + ns.length) t = true) :
    ErasesAlt noCert σ Γ' k (absFV x d e) (ns, _root_.toBvar x (d + ns.length) t) := by
  suffices key : ∀ k {Γ₀ : List CtxBinder} {b : Expr} {br : List BinderName × LBTerm},
      ErasesAlt noCert σ Γ₀ k b br → ∀ (d : Nat) (Γ' : List CtxBinder),
        closedn (d + br.1.length) br.2 = true →
        ErasesAlt noCert σ Γ' k (absFV x d b) (br.1, _root_.toBvar x (d + br.1.length) br.2) from
    key k h d Γ' hcl
  intro k
  induction k with
  | zero =>
    intro _ _ _ h d Γ' hcl
    cases h with
    | done h => exact .done (Erases.absN x h d Γ' hcl)
  | succ k ih =>
    intro _ _ _ h d Γ' hcl
    cases h with
    | @lam A _ _ _ ns _ _ _ h =>
      have := ih h (d + 1) ((absFV x d A, none) :: Γ')
        (by rw [show d + 1 + ns.length = d + (ns.length + 1) by omega]; exact hcl)
      rw [show d + 1 + ns.length = d + (ns.length + 1) by omega] at this
      exact .lam this
    | @etaLam A _ _ _ ns _ _ _ h =>
      have := ih h (d + 1) ((absFV x d A, none) :: Γ')
        (by rw [show d + 1 + ns.length = d + (ns.length + 1) by omega]; exact hcl)
      rw [show d + 1 + ns.length = d + (ns.length + 1) by omega] at this
      exact .etaLam this

end

end EraseProof
