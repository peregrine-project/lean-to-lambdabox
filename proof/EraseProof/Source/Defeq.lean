import EraseProof.Bridge.Wf
import EraseProof.Bridge.Inst
import EraseProof.Bridge.CasesWhred
import EraseProof.Bridge.Unfold
import EraseProof.Bridge.Det
import EraseProof.Bridge.Order
import EraseProof.Bridge.Lookup
import EraseProof.Bridge.Quot
import EraseProof.Bridge.RecWhred

/-!
# Subject reduction of the source semantics

A typed translation of a source term that evaluates is definitionally equal to a translation of
the value (`SrcDefeq.Sound`). `SrcDefeq.sound_of` proves it by induction on `SrcEval`, each rule
a Metalean typed definitional equality: β (`WHRed.beta_defeq`, `TrM.inst`), ζ
(`WHRed.zeta_defeq`, `TrM.inst_let`, with the let-bound local replaced by its value's translation,
`SrcDefeq.PreTr.replace`), δ (`ProgEnv.unfold`), η of a recognized `casesOn` spine (Metalean's
`eta` over the binders of the declared type, `SrcDefeq.eta_lams`, `SrcDefeq.piInst_tr`), ι
(`casesOn_whred`, `casesOnLit_whred` after replacing the major by its value), projections
(`proj_defeq`) and congruence (`DCong.defeq`, `TrM.apps`). A spine of a saturating head (an
inductive type or a saturated constructor) evaluates argument by argument; the induction carries
this (`SrcDefeq.SpineOK`) with the conclusion. η on a constructor spine (`SrcDefeq.eta_ctor`)
needs the constructor's universe parameters to be distinct, which `ProgEnv` gives
(`ProgEnv.levelParams_nodup`); the proof-irrelevant ι is taken as a hypothesis
(`SrcDefeq.ProofSound`). Reference:
`subject_reduction_eval` (`MR P/PCUICWcbvEval.v`); `ML Metatheory/SubjectReduction.lean`.
-/

open Lean Erasure
open Metalean (Defeq EnvWF WHRed WHRedS TypeEq)

namespace EraseProof

namespace SrcDefeq

variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P : List ConstantInfo}
  {σ : EvalEnv} {lps : List Name}

/-- The conclusion of `SrcEval.defeq` for one evaluation `e ⇓ v`. -/
def Sound (E : Metalean.Env ζ) (B : Binds ζ) (lps : List Name) (e v : Expr) : Prop :=
  ∀ {t T : Metalean.Expr ζ lps.length 0}, TrM E B lps .nil [] e t → E[.nil] ⊢ t : T →
    ∃ t', TrM E B lps .nil [] v t' ∧ E[.nil] ⊢ t ≡ t' : T

/-- A spine of a saturating head other than a quotient constant, with at least a constructor's arity
of arguments, evaluates argument by argument, and its head is an inductive type or a
constructor. -/
def SpineOK (σ : EvalEnv) (E : Metalean.Env ζ) (B : Binds ζ) (lps : List Name) (e v : Expr) :
    Prop :=
  ∀ (c : Name) (us : List Level) (bs : List Expr) (b : MBinding ζ),
    e = mkAppN (.const c us) bs.toArray → B c = some b → b.isSpecial = true →
    (∀ η k, b ≠ .quot η k) →
    (∀ (ι : Metalean.IndSig) (η : Metalean.Head ζ (.inductive ι)) (s : Fin ι.nsorts) os,
      b ≠ .recr η s os) →
    (∀ cv, findDecl σ.decls c = some (.ctorInfo cv) → cv.numParams + cv.numFields ≤ bs.length) →
    ((∃ iv, findDecl σ.decls c = some (.inductInfo iv)) ∨
      ∃ cv, findDecl σ.decls c = some (.ctorInfo cv)) ∧
    ∃ vs : List Expr, v = mkAppN (.const c us) vs.toArray ∧ List.Forall₂ (Sound E B lps) bs vs

/-- The empty context is well formed. -/
theorem nil_ok : E[(.nil : Metalean.Ctx ζ lps.length 0 0)] ⊢ ok := .nil

/-- Chaining definitional equalities at the type of the first. -/
theorem dtrans (hE : EnvWF E) {x y z T U : Metalean.Expr ζ lps.length 0}
    (h₁ : E[.nil] ⊢ x ≡ y : T) (h₂ : E[.nil] ⊢ y ≡ z : U) : E[.nil] ⊢ x ≡ z : T :=
  h₁.trans (Defeq.retype hE nil_ok h₂ h₁.right)

/-- The head of a constant spine. -/
theorem getAppFn_mkAppN_const (c : Name) (us : List Level) (as : List Expr) :
    (mkAppN (.const c us) as.toArray).getAppFn = .const c us := by
  rw [mkAppN_eq_foldl, foldl_app_getAppFn]; rfl

/-- `SpineOK` holds of a term that is no constant spine. -/
theorem spineOK_of_head {e v : Expr} (he : ∀ c us, e.getAppFn ≠ .const c us) :
    SpineOK σ E B lps e v := by
  intro c us bs b h
  exact absurd (h ▸ getAppFn_mkAppN_const c us bs) (he c us)


/-- A declaration of the evaluation environment is one of the program. -/
theorem findDecl_sub (hsub : SubEnv σ.decls P) {c : Name} {ci : ConstantInfo}
    (h : findDecl σ.decls c = some ci) : findDecl P c = some ci := by
  obtain ⟨hm, hn⟩ := findDecl_eq_some h
  have h' := hsub _ hm
  rwa [hn] at h'

/-- A name of the program with a saturating binding is an inductive type, a constructor, a
recursor or a quotient constant. -/
theorem special_kind (h : ProgEnv P ζ E B) {c : Name} {b : MBinding ζ} {ci : ConstantInfo}
    (hb : B c = some b) (hs : b.isSpecial = true) (hc : findDecl P c = some ci) :
    (∃ v, ci = .inductInfo v) ∨ (∃ v, ci = .ctorInfo v) ∨ (∃ v, ci = .recInfo v) ∨
      ∃ v, ci = .quotInfo v := by
  induction h with
  | nil => simp [findDecl] at hc
  | @«axiom» _ _ _ _ v _ hP hfr _ _ _ ih | @defn _ _ _ _ v _ _ hP hfr _ _ _ _ _ ih
  | @thm _ _ _ _ v _ hP hfr _ _ _ _ _ ih | @«opaque» _ _ _ _ v _ _ hP hfr _ _ _ _ _ _ ih =>
    rw [findDecl_cons] at hc
    split at hc
    · rename_i hn
      simp only [Binds.set, ← hn] at hb
      split at hb
      · cases hb; cases hs
      · exact absurd rfl ‹_›
    · rw [set_wk_ne (Ne.symm ‹_›)] at hb
      obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.1 hb
      exact ih hb' (by rwa [MBinding.wk_isSpecial] at hs) hc
  | @induct _ _ _ _ ι _ _ _ Is Cs Rs _ hP _ hfr _ hext hblk _ ih =>
    rw [findDecl_append] at hc
    cases hd : findDecl (IndBlock.decls Is Cs Rs) c with
    | some ci' =>
      rw [hd] at hc
      cases hc
      obtain ⟨hm, -⟩ := findDecl_eq_some hd
      rcases IndBlock.mem_decls hm with ⟨s, hs⟩ | ⟨s, k, hs⟩ | ⟨s, hs⟩
      · exact .inr (.inr (.inl ⟨_, hs⟩))
      · exact .inr (.inl ⟨_, hs⟩)
      · exact .inl ⟨_, hs⟩
    | none =>
      rw [hd] at hc
      simp only [Option.none_or] at hc
      have hnot : c ∉ (IndBlock.decls Is Cs Rs).map (·.name) := not_mem_of_findDecl_none hd
      rw [hext c hnot, Binds.wk] at hb
      obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.1 hb
      exact ih hb' (by rwa [MBinding.wk_isSpecial] at hs) hc
  | @quot _ _ _ _ _ qs _ hP _ _ hfr _ hext _ ih =>
    rw [findDecl_append] at hc
    cases hd : findDecl (qs.reverse.map ConstantInfo.quotInfo) c with
    | some ci' =>
      obtain ⟨hm, -⟩ := findDecl_eq_some hd
      rw [hd] at hc
      cases hc
      obtain ⟨q, -, rfl⟩ := List.mem_map.mp hm
      exact .inr (.inr (.inr ⟨q, rfl⟩))
    | none =>
      rw [hd] at hc
      simp only [Option.none_or] at hc
      have hnot := not_mem_of_findDecl_none hd
      rw [quot_names_reverse, List.mem_reverse] at hnot
      rw [hext c hnot, Binds.wk] at hb
      obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.1 hb
      exact ih hb' (by rwa [MBinding.wk_isSpecial] at hs) hc

/-- A definition of the evaluation environment has no saturating binding. -/
theorem defn_not_special (henv : ProgEnv P ζ E B) (hsub : SubEnv σ.decls P) {c : Name}
    {d : DefinitionVal} {b : MBinding ζ} (hd : findDecl σ.decls c = some (.defnInfo d))
    (hb : B c = some b) (hs : b.isSpecial = true) : False := by
  obtain ⟨η, hB, -⟩ := henv.lookup_def (findDecl_sub hsub hd)
  rw [hB] at hb; cases hb; cases hs

/-- A recognized `casesOn` constant is a definition. -/
theorem casesOn?_defn {c : Name} {iv : InductiveVal}
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

/-- An unfoldable constant is a definition. -/
theorem unfold?_defn {c : Name} {ci : ConstantInfo} {b : Expr}
    (h : σ.unfold? c = some (ci, b)) : ∃ d, findDecl σ.decls c = some (.defnInfo d) := by
  unfold EvalEnv.unfold? at h
  split at h
  · exact ⟨_, ‹_›⟩
  · cases h

/-- A constant spine that is an application. -/
theorem spine_app {c : Name} {us : List Level} {bs : List Expr} {f a : Expr}
    (h : mkAppN (.const c us) bs.toArray = .app f a) :
    ∃ bs', bs = bs' ++ [a] ∧ f = mkAppN (.const c us) bs'.toArray := by
  cases bs using List.reverseRecOn with
  | nil => cases h
  | append_singleton bs' x _ =>
    rw [mkAppN_eq_foldl, List.foldl_append] at h
    simp only [List.foldl_cons, List.foldl_nil, Expr.app.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨bs', rfl, (mkAppN_eq_foldl _ _).symm⟩

/-- A constant spine that is a constant. -/
theorem spine_const {c c' : Name} {us us' : List Level} {bs : List Expr}
    (h : mkAppN (.const c us) bs.toArray = .const c' us') : bs = [] ∧ c = c' ∧ us = us' := by
  rw [mkAppN_eq_foldl] at h
  have h' : bs.foldl Expr.app (.const c us) = ([] : List Expr).foldl Expr.app (.const c' us') := h
  obtain ⟨h1, h2, h3⟩ := foldl_app_const_inj h'
  exact ⟨h3, h1, h2⟩

/-- `SpineOK` of a constant whose declaration is a definition. -/
theorem spineOK_defn (henv : ProgEnv P ζ E B) (hsub : SubEnv σ.decls P) {c : Name}
    {us : List Level} {as : List Expr} {v : Expr} {d : DefinitionVal}
    (hd : findDecl σ.decls c = some (.defnInfo d)) :
    SpineOK σ E B lps (mkAppN (.const c us) as.toArray) v := by
  intro c' us' bs b h hb hs _ _ _
  rw [mkAppN_eq_foldl, mkAppN_eq_foldl] at h
  obtain ⟨rfl, -, -⟩ := foldl_app_const_inj h
  exact (defn_not_special henv hsub hd hb hs).elim

/-- A constant atom with a saturating binding is an inductive type. -/
theorem isAtom_ind (henv : ProgEnv P ζ E B) (hsub : SubEnv σ.decls P) {c : Name}
    {b : MBinding ζ} (ha : σ.isAtom c = true) (hb : B c = some b) (hs : b.isSpecial = true) :
    ∃ iv, findDecl σ.decls c = some (.inductInfo iv) := by
  unfold EvalEnv.isAtom at ha
  split at ha
  · rename_i ci hci
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at ha
    obtain ⟨⟨⟨-, -⟩, hown⟩, -⟩ := ha
    rcases special_kind henv hb hs (findDecl_sub hsub hci) with ⟨v, rfl⟩ | ⟨v, rfl⟩ | ⟨v, rfl⟩ |
      ⟨v, rfl⟩
    · exact ⟨v, hci⟩
    all_goals cases hown
  · cases ha

/-- The case of `SrcEval.constAtom`. -/
theorem case_constAtom (henv : ProgEnv P ζ E B) (hsub : SubEnv σ.decls P) {c : Name}
    {us : List Level} (ha : σ.isAtom c = true) :
    Sound E B lps (.const c us) (.const c us) ∧ SpineOK σ E B lps (.const c us) (.const c us) := by
  refine ⟨fun he ht => ⟨_, he, ht⟩, ?_⟩
  intro c' us' bs b h hb hs _ _ _
  obtain ⟨rfl, rfl, rfl⟩ := spine_const h.symm
  exact ⟨.inl (isAtom_ind henv hsub ha hb hs), [], rfl, .nil⟩

/-- The case of `SrcEval.delta`. -/
theorem case_delta (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv σ.decls P) {c : Name}
    {us : List Level} {ci : ConstantInfo} {body v : Expr} (hu : σ.unfold? c = some (ci, body))
    (ih : Sound E B lps (Pure.instLevels ci.levelParams us body) v) :
    Sound E B lps (.const c us) v ∧ SpineOK σ E B lps (.const c us) v := by
  refine ⟨fun he ht => ?_, ?_⟩
  · obtain ⟨b', hb', hred⟩ := ProgEnv.unfold henv hsub hu he
    have hd := WHRed.defeq hE hred nil_ok ht
    obtain ⟨t', ht', hd'⟩ := ih hb' hd.right
    exact ⟨t', ht', dtrans hE hd hd'⟩
  · obtain ⟨d, hd⟩ := unfold?_defn hu
    exact spineOK_defn (as := []) henv hsub hd

/-- The case of `SrcEval.mdata`. -/
theorem case_mdata {d : MData} {e v : Expr} (ih : Sound E B lps e v) :
    Sound E B lps (.mdata d e) v ∧ SpineOK σ E B lps (.mdata d e) v := by
  refine ⟨fun he ht => ?_, spineOK_of_head fun _ _ h => by cases h⟩
  generalize hx : Expr.mdata d e = x at he
  cases he with
  | mdata h => cases hx; exact ih h ht
  | special => exact absurd hx (ne_mkAppN_const fun _ _ h => by cases h)
  | _ => cases hx

/-- A value that evaluates to itself. -/
theorem case_refl {e : Expr} (he : ∀ c us, e.getAppFn ≠ .const c us) :
    Sound E B lps e e ∧ SpineOK σ E B lps e e :=
  ⟨fun h ht => ⟨_, h, ht⟩, spineOK_of_head he⟩

/-- An accumulator that counts applications counts from its start value. -/
theorem getAppNumArgs_shift (g : Expr → Nat → Nat) (happ : ∀ f a n, g (.app f a) n = g f (n + 1))
    (hother : ∀ e n, e.isApp = false → g e n = n) : ∀ e n, g e n = g e 0 + n := by
  intro e
  induction e with
  | app f a ih => intro n; rw [happ, happ, ih (n + 1), ih 1]; omega
  | _ => intro n; rw [hother _ n rfl, hother _ 0 rfl]; omega

/-- One more argument. -/
theorem getAppNumArgs_app (f a : Expr) : (Expr.app f a).getAppNumArgs = f.getAppNumArgs + 1 := by
  unfold Expr.getAppNumArgs
  exact getAppNumArgs_shift _ (fun _ _ _ => rfl)
    (fun e n h => by cases e <;> first | rfl | cases h) f 1

/-- The number of arguments of a constant spine. -/
theorem getAppNumArgs_mkAppN_const (c : Name) (us : List Level) (as : List Expr) :
    (mkAppN (.const c us) as.toArray).getAppNumArgs = as.length := by
  rw [mkAppN_eq_foldl]
  induction as using List.reverseRecOn with
  | nil => rfl
  | append_singleton as a ih =>
    rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, List.length_append, List.length_singleton]
    rw [getAppNumArgs_app, ih]

/-- An application that is no short spine has at least a constructor's arity of arguments
before its last one. -/
theorem spine_cond {c : Name} {us : List Level} {bs : List Expr} {a : Expr}
    (hns : ¬ ShortSpine σ (.app (mkAppN (.const c us) bs.toArray) a)) :
    ∀ cv, findDecl σ.decls c = some (.ctorInfo cv) → cv.numParams + cv.numFields ≤ bs.length := by
  intro cv hc
  refine Nat.le_of_not_lt fun hlt => hns ⟨c, us, cv.numParams + cv.numFields, ?_, ?_, ?_⟩
  · change (mkAppN (.const c us) bs.toArray).getAppFn = _
    exact getAppFn_mkAppN_const c us _
  · simp [specialArity, hc]
  · rw [getAppNumArgs_app, getAppNumArgs_mkAppN_const]; omega

/-- A constructor spine blocks application congruence. -/
theorem blocksCong_ctor {e : Expr} {c : Name} {us : List Level} {cv : ConstructorVal}
    (he : e.getAppFn = .const c us) (hc : findDecl σ.decls c = some (.ctorInfo cv)) :
    BlocksCong σ e := by
  cases e with
  | app f a => exact .inl ⟨c, us, cv, he, hc⟩
  | const => exact .inl ⟨c, us, cv, he, hc⟩
  | _ => cases he

/-- A spine headed by a quotient constant of the program evaluates only if its head is a constant
of the evaluation environment with an arity (`Quot.mk`, `Quot.lift`): `Quot` and `Quot.ind`
have no rule. -/
theorem quot_head_eval (hsub : SubEnv σ.decls P) {e w : Expr} (hev : SrcEval σ e w) :
    ∀ {c : Name} {us : List Level} {bs : List Expr} {q : QuotVal},
      e = mkAppN (.const c us) bs.toArray → findDecl P c = some (.quotInfo q) →
      findDecl σ.decls c = some (.quotInfo q) ∧ (quotEvalArity q.kind).isSome := by
  have agree : ∀ {c : Name} {q : QuotVal} {ci : ConstantInfo}, findDecl P c = some (.quotInfo q) →
      findDecl σ.decls c = some ci → ci = .quotInfo q := fun hP hσ => by
    rw [findDecl_sub hsub hσ] at hP; exact Option.some.inj hP
  have head : ∀ {c c' : Name} {us us' : List Level} {as bs : List Expr},
      mkAppN (.const c' us') as.toArray = mkAppN (.const c us) bs.toArray → c' = c := by
    intro c c' us us' as bs hx
    rw [mkAppN_eq_foldl, mkAppN_eq_foldl] at hx
    exact (foldl_app_const_inj hx).1
  induction hev with
  | beta _ _ _ _ ihf =>
    intro c us bs q hx hq
    obtain ⟨bs', -, rfl⟩ := spine_app hx.symm
    exact ihf rfl hq
  | appCong _ _ _ _ ihf =>
    intro c us bs q hx hq
    obtain ⟨bs', -, rfl⟩ := spine_app hx.symm
    exact ihf rfl hq
  | delta hu =>
    intro c us bs q hx hq
    obtain ⟨-, rfl, -⟩ := spine_const hx.symm
    obtain ⟨d, hd⟩ := unfold?_defn hu
    cases agree hq hd
  | constAtom ha =>
    intro c us bs q hx hq
    obtain ⟨-, rfl, -⟩ := spine_const hx.symm
    unfold EvalEnv.isAtom at ha
    split at ha
    · rename_i ci hci
      cases agree hq hci
      simp [OwnRules] at ha
    · cases ha
  | eta he =>
    intro c us bs q hx hq
    cases head hx
    unfold EvalEnv.etaSpine? at he
    split at he
    · rename_i ar _ har
      unfold specialArity at har
      split at har
      · rename_i cv hcv; cases agree hq hcv
      · rename_i qv hqv; cases agree hq hqv; exact ⟨hqv, by rw [har]; rfl⟩
      · rename_i rv hrv; cases agree hq hrv
      · obtain ⟨iv, hiv, -⟩ := Option.map_eq_some_iff.1 har
        obtain ⟨d, hd⟩ := casesOn?_defn hiv
        cases agree hq hd
    · cases he
  | ctor hc =>
    intro c us bs q hx hq
    cases head hx
    cases agree hq hc
  | casesIota hcs | casesLitZero hcs | casesLitSucc hcs | casesProof hcs =>
    intro c us bs q hx hq
    cases head hx
    obtain ⟨d, hd⟩ := casesOn?_defn hcs
    cases agree hq hd
  | quotMk hc hk | quotLift hc hk =>
    intro c us bs q hx hq
    cases head hx
    cases agree hq hc
    exact ⟨hc, by rw [hk]; rfl⟩
  | recIota hc =>
    intro c us bs q hx hq
    cases head hx
    cases agree hq hc
  | zeta | proj | projProp | lit | mdata =>
    intro c us bs q hx
    exact absurd hx (ne_mkAppN_const fun _ _ h => by cases h)
  | atom ha =>
    rename_i e
    intro c us bs q hx
    refine absurd hx (ne_mkAppN_const fun _ _ h => ?_)
    cases e <;> simp [SrcAtom, Expr.getAppFn] at ha h

/-- An application with no short spine whose head is an evaluated quotient spine: the spine has at
least its arity of arguments, so the application translates to the application of the
translations. -/
theorem quot_app_tr (henv : ProgEnv P ζ E B) (hsub : SubEnv σ.decls P) {c : Name}
    {us : List Level} {bs : List Expr} {a w : Expr} {η : Metalean.Head ζ .quot}
    {k : Metalean.Export.QuotKind} {t T : Metalean.Expr ζ lps.length 0}
    (hb : B c = some (.quot η k)) (hf : SrcEval σ (mkAppN (.const c us) bs.toArray) w)
    (hns : ¬ ShortSpine σ (.app (mkAppN (.const c us) bs.toArray) a))
    (he : TrM E B lps .nil [] (.app (mkAppN (.const c us) bs.toArray) a) t)
    (ht : E[.nil] ⊢ t : T) :
    ∃ f' a', TrM E B lps .nil [] (mkAppN (.const c us) bs.toArray) f' ∧
      TrM E B lps .nil [] a a' ∧ t = .app f' a' ∧ (∃ F, E[.nil] ⊢ f' : F) ∧
      ∃ A, E[.nil] ⊢ a' : A := by
  obtain ⟨q, hq, rfl, -⟩ := henv.quot_bound hb
  obtain ⟨hqσ, har⟩ := quot_head_eval hsub hf rfl hq
  obtain ⟨ar, har⟩ := Option.isSome_iff_exists.mp har
  have hsa : specialArity σ c = some ar := by simp [specialArity, hqσ, har]
  have hle : ar ≤ bs.length := Nat.le_of_not_lt fun hlt => hns ⟨c, us, ar, by
      change (mkAppN (.const c us) bs.toArray).getAppFn = _; exact getAppFn_mkAppN_const c us _,
    hsa, by rw [getAppNumArgs_app, getAppNumArgs_mkAppN_const]; omega⟩
  have hk : quotArity (quotKindOf q.kind) = ar := by
    cases hqk : q.kind <;> rw [hqk] at har <;> simp [quotEvalArity] at har <;> subst har <;> rfl
  exact TrM.wf_app_quot hb (hk ▸ hle) he ht

/-- A spine headed by a constant with a recursor binding evaluates only if the constant is a
recursor of the evaluation environment, whose arity is Metalean's `recrEnd`: by `SrcEval.eta`, by
`SrcEval.recIota`, or as the head of an application. -/
theorem rec_head_eval (henv : ProgEnv P ζ E B) (hsub : SubEnv σ.decls P) {e w : Expr}
    (hev : SrcEval σ e w) :
    ∀ {c : Name} {us : List Level} {bs : List Expr} {ι : Metalean.IndSig}
      {η : Metalean.Head ζ (.inductive ι)} {s : Fin ι.nsorts} {os : List (List (List Nat))},
      e = mkAppN (.const c us) bs.toArray → B c = some (.recr η s os) →
      specialArity σ c = some (ι.recrEnd s) := by
  have head : ∀ {c c' : Name} {us us' : List Level} {as bs : List Expr},
      mkAppN (.const c' us') as.toArray = mkAppN (.const c us) bs.toArray → c' = c := by
    intro c c' us us' as bs hx
    rw [mkAppN_eq_foldl, mkAppN_eq_foldl] at hx
    exact (foldl_app_const_inj hx).1
  have recr : ∀ {c : Name} {ci : ConstantInfo} {ι : Metalean.IndSig}
      {η : Metalean.Head ζ (.inductive ι)} {s : Fin ι.nsorts} {os : List (List (List Nat))},
      findDecl σ.decls c = some ci → B c = some (.recr η s os) →
      specialArity σ c = some (ι.recrEnd s) := by
    intro c ci ι η s os hc hb
    obtain ⟨rv, rfl, har⟩ := henv.recr_arity (findDecl_sub hsub hc) hb
    simp [specialArity, hc, ← har]
  induction hev with
  | beta _ _ _ _ ihf =>
    intro c us bs ι η s os hx hb
    obtain ⟨bs', -, rfl⟩ := spine_app hx.symm
    exact ihf rfl hb
  | appCong _ _ _ _ ihf =>
    intro c us bs ι η s os hx hb
    obtain ⟨bs', -, rfl⟩ := spine_app hx.symm
    exact ihf rfl hb
  | delta hu =>
    intro c us bs ι η s os hx hb
    obtain ⟨-, rfl, -⟩ := spine_const hx.symm
    obtain ⟨d, hd⟩ := unfold?_defn hu
    exact (defn_not_special henv hsub hd hb rfl).elim
  | constAtom ha =>
    intro c us bs ι η s os hx hb
    obtain ⟨-, rfl, -⟩ := spine_const hx.symm
    obtain ⟨iv, hiv⟩ := isAtom_ind henv hsub ha hb rfl
    obtain ⟨_, _, _, hB, -⟩ := henv.lookup_ind (findDecl_sub hsub hiv)
    rw [hB] at hb; cases hb
  | eta he =>
    intro c us bs ι η s os hx hb
    cases head hx
    unfold EvalEnv.etaSpine? at he
    split at he
    · exact recr ‹_› hb
    · cases he
  | ctor hc =>
    intro c us bs ι η s os hx hb
    cases head hx
    obtain ⟨_, _, _, _, _, hB, -⟩ := henv.lookup_ctor (findDecl_sub hsub hc)
    rw [hB] at hb; cases hb
  | casesIota hcs | casesLitZero hcs | casesLitSucc hcs | casesProof hcs =>
    intro c us bs ι η s os hx hb
    cases head hx
    obtain ⟨d, hd⟩ := casesOn?_defn hcs
    exact (defn_not_special henv hsub hd hb rfl).elim
  | quotMk hc | quotLift hc =>
    intro c us bs ι η s os hx hb
    cases head hx
    obtain ⟨_, hB⟩ := henv.lookup_quot (findDecl_sub hsub hc)
    rw [hB] at hb; cases hb
  | recIota hcr =>
    intro c us bs ι η s os hx hb
    cases head hx
    exact recr hcr hb
  | zeta | proj | projProp | lit | mdata =>
    intro c us bs ι η s os hx
    exact absurd hx (ne_mkAppN_const fun _ _ h => by cases h)
  | atom ha =>
    rename_i e
    intro c us bs ι η s os hx
    refine absurd hx (ne_mkAppN_const fun _ _ h => ?_)
    cases e <;> simp [SrcAtom, Expr.getAppFn] at ha h

/-- An application with no short spine whose head is an evaluated recursor spine: the spine has at
least its arity of arguments, so the application translates to the application of the
translations. -/
theorem rec_app_tr (henv : ProgEnv P ζ E B) (hsub : SubEnv σ.decls P) {c : Name}
    {us : List Level} {bs : List Expr} {a w : Expr} {ι : Metalean.IndSig}
    {η : Metalean.Head ζ (.inductive ι)} {s : Fin ι.nsorts} {os : List (List (List Nat))}
    {t T : Metalean.Expr ζ lps.length 0}
    (hb : B c = some (.recr η s os)) (hf : SrcEval σ (mkAppN (.const c us) bs.toArray) w)
    (hns : ¬ ShortSpine σ (.app (mkAppN (.const c us) bs.toArray) a))
    (he : TrM E B lps .nil [] (.app (mkAppN (.const c us) bs.toArray) a) t)
    (ht : E[.nil] ⊢ t : T) :
    ∃ f' a', TrM E B lps .nil [] (mkAppN (.const c us) bs.toArray) f' ∧
      TrM E B lps .nil [] a a' ∧ t = .app f' a' ∧ (∃ F, E[.nil] ⊢ f' : F) ∧
      ∃ A, E[.nil] ⊢ a' : A := by
  have hsa := rec_head_eval henv hsub hf rfl hb
  have hle : ι.recrEnd s ≤ bs.length := Nat.le_of_not_lt fun hlt => hns ⟨c, us, _, by
      change (mkAppN (.const c us) bs.toArray).getAppFn = _; exact getAppFn_mkAppN_const c us _,
    hsa, by rw [getAppNumArgs_app, getAppNumArgs_mkAppN_const]; omega⟩
  exact RecWhred.TrM.wf_app_recr hb hle he ht

/-- A quotient spine blocks application congruence. -/
theorem blocksCong_quot {e : Expr} {c : Name} {us : List Level} {qv : QuotVal}
    (he : e.getAppFn = .const c us) (hc : findDecl σ.decls c = some (.quotInfo qv)) :
    BlocksCong σ e := by
  cases e with
  | app f a => exact .inr (.inr ⟨c, us, qv, he, hc⟩)
  | const => exact .inr (.inr ⟨c, us, qv, he, hc⟩)
  | _ => cases he

/-- The case of `SrcEval.beta`. -/
theorem case_beta (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv σ.decls P)
    {f a a' b v : Expr} {x : Name}
    {A : Expr} {bi : BinderInfo} (hns : ¬ ShortSpine σ (.app f a))
    (hfev : SrcEval σ f (.lam x A b bi))
    (ihf : Sound E B lps f (.lam x A b bi) ∧ SpineOK σ E B lps f (.lam x A b bi))
    (iha : Sound E B lps a a') (ihb : Sound E B lps (b.instantiate1' a') v) :
    Sound E B lps (.app f a) v ∧ SpineOK σ E B lps (.app f a) v := by
  have hlam : ∀ c us (bs : List Expr) (bb : MBinding ζ), f = mkAppN (.const c us) bs.toArray → B c = some bb →
      bb.isSpecial = true → (∀ η k, bb ≠ .quot η k) →
      (∀ (ι : Metalean.IndSig) (η : Metalean.Head ζ (.inductive ι)) (s : Fin ι.nsorts) os,
        bb ≠ .recr η s os) → False := by
    intro c us bs bb hf hb hs hq hr
    subst hf
    obtain ⟨-, vs, hv, -⟩ := ihf.2 c us bs bb rfl hb hs hq hr (spine_cond hns)
    have := congrArg Expr.getAppFn hv
    rw [getAppFn_mkAppN_const] at this
    cases this
  refine ⟨fun {t T} he ht => ?_, ?_⟩
  · obtain ⟨f', a'', hf', ha'', rfl, ⟨F, hF⟩, ⟨A₁, hA₁⟩⟩ : ∃ f' a'', TrM E B lps .nil [] f f' ∧
        TrM E B lps .nil [] a a'' ∧ t = .app f' a'' ∧ (∃ F, E[.nil] ⊢ f' : F) ∧
        ∃ A, E[.nil] ⊢ a'' : A := by
      by_cases hsp : SpecialHead B f
      · obtain ⟨c, us, bb, hfn, hb, hs⟩ := hsp
        obtain ⟨bs, rfl⟩ := eq_mkAppN_of_getAppFn hfn
        by_cases hq : ∃ η k, bb = .quot η k
        · obtain ⟨η, k, rfl⟩ := hq
          exact quot_app_tr henv hsub hb hfev hns he ht
        · by_cases hr : ∃ (ι : Metalean.IndSig) (η : Metalean.Head ζ (.inductive ι))
              (s : Fin ι.nsorts) (os : List (List (List Nat))), bb = .recr η s os
          · obtain ⟨ι, η, s, os, rfl⟩ := hr
            exact rec_app_tr henv hsub hb hfev hns he ht
          · exact (hlam c us bs bb rfl hb hs (fun η k h => hq ⟨η, k, h⟩)
              fun ι η s os h => hr ⟨ι, η, s, os, h⟩).elim
      · exact TrM.wf_app hE nil_ok hsp he ht
    obtain ⟨tl, htl, hdl⟩ := ihf.1 hf' hF
    obtain ⟨ta, hta, hda⟩ := iha ha'' hA₁
    obtain ⟨A₀, b₀, rfl, hb₀⟩ := CasesWhred.trM_lam_inv htl
    have h1 : E[.nil] ⊢ .app f' a'' ≡ .app (.lam A₀ b₀) ta : T :=
      DCong.defeq hE not_false (.app (.leaf hdl) (.leaf hda)) nil_ok (DCong.CtxConv.refl nil_ok) ht
    have h2 := WHRed.beta_defeq hE nil_ok h1.right
    obtain ⟨X, Y, hl, hta', -⟩ := h1.right.app_inv
    obtain ⟨T₀, hb₀T, hπ⟩ := hl.lam_inv nil_ok
    have htaA : E[.nil] ⊢ ta : A₀ := (TypeEq.forallE_inj hE nil_ok hπ).1.conv hta'
    obtain ⟨tb, htb, hdb⟩ := TrM.inst hE nil_ok henv.metaOrderOK hb₀ hta htaA hb₀T
    obtain ⟨t', ht', hd'⟩ := ihb htb hdb.left
    exact ⟨t', ht', dtrans hE (dtrans hE (dtrans hE h1 h2) hdb.symm) hd'⟩
  · intro c us bs bb h hb hs hq hr _
    obtain ⟨bs', rfl, rfl⟩ := spine_app h.symm
    exact (hlam c us bs' bb rfl hb hs hq hr).elim

/-- Typed translations of arguments, each with an evaluation, give translations of the values that
are definitionally equal, argument by argument. -/
theorem args_congr {bs vs : List Expr} (hall : List.Forall₂ (Sound E B lps) bs vs) :
    ∀ {bs' : List (Metalean.Expr ζ lps.length 0)}, List.Forall₂ (TrM E B lps .nil []) bs bs' →
      (∀ a ∈ bs', ∃ A, E[.nil] ⊢ a : A) →
      ∃ vs', List.Forall₂ (TrM E B lps .nil []) vs vs' ∧
        List.Forall₂ (fun x y => ∃ A, E[.nil] ⊢ x ≡ y : A) bs' vs' := by
  induction hall with
  | nil => intro bs' h _; cases h; exact ⟨[], .nil, .nil⟩
  | cons hS _ ih =>
    intro bs' h htyped
    cases h with
    | cons ha hrest =>
      obtain ⟨A, hA⟩ := htyped _ List.mem_cons_self
      obtain ⟨v', hv', hd⟩ := hS ha hA
      obtain ⟨vs', hvs', hds⟩ := ih hrest fun a ha => htyped a (List.mem_cons_of_mem _ ha)
      exact ⟨v' :: vs', .cons hv' hvs', .cons ⟨A, hd⟩ hds⟩

/-- Replacing the arguments of a saturating spine by values with definitionally equal typed
translations. -/
theorem special_congr (hE : EnvWF E) {c : Name} {us : List Level} {bs vs : List Expr}
    {b : MBinding ζ} {t T : Metalean.Expr ζ lps.length 0} (hb : B c = some b)
    (hs : b.isSpecial = true) (he : TrM E B lps .nil [] (mkAppN (.const c us) bs.toArray) t)
    (ht : E[.nil] ⊢ t : T)
    (htyped : ∀ {bs' : List (Metalean.Expr ζ lps.length 0)}, SatTr E lps b us bs' t →
      ∀ a ∈ bs', ∃ A, E[.nil] ⊢ a : A)
    (hall : List.Forall₂ (Sound E B lps) bs vs) :
    ∃ t', TrM E B lps .nil [] (mkAppN (.const c us) vs.toArray) t' ∧ E[.nil] ⊢ t ≡ t' : T := by
  obtain ⟨bs', hlen, hargs, hsat⟩ := TrM.special_inv hb hs he
  obtain ⟨vs', hvs', hds⟩ := args_congr hall (CasesWhred.forall₂_of_getElem? hlen hargs)
    (htyped hsat)
  have hl₁ := hds.length_eq
  have hl₂ := hvs'.length_eq
  obtain ⟨t', hsat'⟩ := InstPre.SatTr.replace hsat vs' hl₁.symm
  have hcong : DCong E False .nil .nil t t' := SatTr.dcong hsat hsat' hl₁ fun i x y hx hy => by
    obtain ⟨A, hA⟩ := forall₂_getElem? hds i x y hx hy
    exact .leaf hA
  refine ⟨t', .special hb hs hl₂ (forall₂_getElem? hvs') hsat', ?_⟩
  exact DCong.defeq hE not_false hcong nil_ok (DCong.CtxConv.refl nil_ok) ht

/-- The arguments of a typed image of an inductive type are typed. -/
theorem satTr_ind_typed {ι : Metalean.IndSig} {η : Metalean.Head ζ (.inductive ι)}
    {s : Fin ι.nsorts} {us : List Level} {bs' : List (Metalean.Expr ζ lps.length 0)}
    {t T : Metalean.Expr ζ lps.length 0} (hsat : SatTr E lps (.ind η s) us bs' t)
    (ht : E[.nil] ⊢ t : T) : ∀ a ∈ bs', ∃ A, E[.nil] ⊢ a : A := by
  cases hsat with
  | indSat ps is rest =>
    obtain ⟨⟨F, hF⟩, hrest⟩ := InstPre.appList_inv ht
    obtain ⟨ps₁, is₁, hps, his, -⟩ := hF.ind_inv
    intro a ha
    simp only [List.mem_append, List.mem_ofFn] at ha
    rcases ha with (⟨p, rfl⟩ | ⟨i, rfl⟩) | ha
    · exact ⟨_, (hps p).right⟩
    · exact ⟨_, (his i).right⟩
    · exact hrest a ha
  | indEta => exact (InstPre.appList_inv ht).2

/-- The arguments of a typed image of a constructor are typed. -/
theorem satTr_ctor_typed {ι : Metalean.IndSig} {η : Metalean.Head ζ (.inductive ι)}
    {s : Fin ι.nsorts} {k : Fin (ι.nctors s)} {order : List Nat} {us : List Level}
    {bs' : List (Metalean.Expr ζ lps.length 0)} {t T : Metalean.Expr ζ lps.length 0}
    (hmo : MetaOrderOK order (ι.ctors s k).nfields (ι.ctors s k).nrecFields)
    (hsat : SatTr E lps (.ctor η s k order) us bs' t) (ht : E[.nil] ⊢ t : T) :
    ∀ a ∈ bs', ∃ A, E[.nil] ⊢ a : A := by
  cases hsat with
  | ctorSat ps fs rest fds recFds hls hfs hord hperm =>
    obtain ⟨⟨F, hF⟩, hrest⟩ := InstPre.appList_inv ht
    obtain ⟨ps₁, fds₁, rf₁, hps, hfds, hrf, -⟩ := hF.ctor_inv
    have happ : ∀ o, ∃ A, E[.nil] ⊢ Fin.append fds recFds o : A := by
      intro o
      refine Fin.addCases (fun f => ?_) (fun f => ?_) o
      · rw [Fin.append_left]; exact ⟨_, (hfds f).right⟩
      · rw [Fin.append_right]; exact ⟨_, (hrf f).right⟩
    intro a ha
    simp only [List.mem_append, List.mem_ofFn] at ha
    rcases ha with (⟨p, rfl⟩ | ha) | ha
    · exact ⟨_, (hps p).right⟩
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
      obtain ⟨-, -, -, -, -, -, -, hp⟩ := hmo
      have hjm : j ∈ order := hp.symm.mem_iff.mp (List.mem_range.mpr (hfs ▸ hj))
      obtain ⟨o, ho, hoj⟩ := List.getElem_of_mem hjm
      obtain ⟨j', a', hj', ha', heq⟩ := hperm ⟨o, hord ▸ ho⟩
      rw [List.getElem?_eq_getElem ho, hoj, Option.some.injEq] at hj'
      subst hj'
      rw [List.getElem?_eq_getElem hj, Option.some.injEq] at ha'
      rw [ha', ← heq]
      exact happ _
    · exact hrest a ha
  | ctorEta => exact (InstPre.appList_inv ht).2

/-- A constant spine with one more argument. -/
theorem mkAppN_snoc (c : Name) (us : List Level) (bs : List Expr) (a : Expr) :
    mkAppN (.const c us) (bs ++ [a]).toArray = .app (mkAppN (.const c us) bs.toArray) a := by
  rw [mkAppN_eq_foldl, mkAppN_eq_foldl, List.foldl_append]; rfl

/-- The case of `SrcEval.appCong`. -/
theorem case_appCong (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv σ.decls P)
    {f a f' a' : Expr} (hns : ¬ ShortSpine σ (.app f a)) (hfev : SrcEval σ f f')
    (hnb : ¬ BlocksCong σ f')
    (ihf : Sound E B lps f f' ∧ SpineOK σ E B lps f f') (iha : Sound E B lps a a') :
    Sound E B lps (.app f a) (.app f' a') ∧ SpineOK σ E B lps (.app f a) (.app f' a') := by
  refine ⟨fun {t T} he ht => ?_, ?_⟩
  · have general : ∀ f'' a'', TrM E B lps .nil [] f f'' → TrM E B lps .nil [] a a'' →
        t = .app f'' a'' → (∃ F, E[.nil] ⊢ f'' : F) → (∃ A, E[.nil] ⊢ a'' : A) →
        ∃ t', TrM E B lps .nil [] (.app f' a') t' ∧ E[.nil] ⊢ t ≡ t' : T := by
      rintro f'' a'' hf' ha'' rfl ⟨F, hF⟩ ⟨A₁, hA₁⟩
      obtain ⟨tf, htf, hdf⟩ := ihf.1 hf' hF
      obtain ⟨ta, hta, hda⟩ := iha ha'' hA₁
      obtain ⟨t₂, ht₂, hred⟩ := TrM.apps htf (.cons hta .nil)
      have h1 : E[.nil] ⊢ .app f'' a'' ≡ .app tf ta : T :=
        DCong.defeq hE not_false (.app (.leaf hdf) (.leaf hda)) nil_ok
          (DCong.CtxConv.refl nil_ok) ht
      exact ⟨t₂, ht₂, dtrans hE h1 (WHRedS.defeq hE nil_ok hred h1.right)⟩
    by_cases hsp : SpecialHead B f
    · obtain ⟨c, us, bb, hfn, hb, hs⟩ := hsp
      obtain ⟨bs, rfl⟩ := eq_mkAppN_of_getAppFn hfn
      by_cases hq : ∃ η k, bb = .quot η k
      · obtain ⟨η, k, rfl⟩ := hq
        obtain ⟨f'', a'', hf', ha'', h₁, h₂, h₃⟩ := quot_app_tr henv hsub hb hfev hns he ht
        exact general f'' a'' hf' ha'' h₁ h₂ h₃
      by_cases hr : ∃ (ι : Metalean.IndSig) (η : Metalean.Head ζ (.inductive ι))
          (s : Fin ι.nsorts) (os : List (List (List Nat))), bb = .recr η s os
      · obtain ⟨ι, η, s, os, rfl⟩ := hr
        obtain ⟨f'', a'', hf', ha'', h₁, h₂, h₃⟩ := rec_app_tr henv hsub hb hfev hns he ht
        exact general f'' a'' hf' ha'' h₁ h₂ h₃
      obtain ⟨hk, vs, rfl, hall⟩ := ihf.2 c us bs bb rfl hb hs (fun η k h => hq ⟨η, k, h⟩)
        (fun ι η s os h => hr ⟨ι, η, s, os, h⟩) (spine_cond hns)
      rcases hk with ⟨iv, hiv⟩ | ⟨cv, hcv⟩
      · obtain ⟨ι, η, s, hB, -⟩ := henv.lookup_ind (findDecl_sub hsub hiv)
        rw [← mkAppN_snoc] at he
        obtain ⟨t', ht', hd⟩ := special_congr hE hB rfl he ht
          (fun hsat => satTr_ind_typed hsat ht) (CasesWhred.forall₂_snoc hall iha)
        exact ⟨t', by rwa [mkAppN_snoc] at ht', hd⟩
      · exact absurd (blocksCong_ctor (getAppFn_mkAppN_const c us vs) hcv) hnb
    · obtain ⟨f'', a'', hf', ha'', h₁, h₂, h₃⟩ := TrM.wf_app hE nil_ok hsp he ht
      exact general f'' a'' hf' ha'' h₁ h₂ h₃
  · intro c us bs bb h hb hs hq hr _
    obtain ⟨bs', rfl, rfl⟩ := spine_app h.symm
    obtain ⟨hk, vs, rfl, hall⟩ := ihf.2 c us bs' bb rfl hb hs hq hr (spine_cond hns)
    exact ⟨hk, vs ++ [a'], (mkAppN_snoc c us vs a').symm, CasesWhred.forall₂_snoc hall iha⟩

/-- The case of `SrcEval.ctor`. -/
theorem case_ctor (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv σ.decls P) {c : Name}
    {us : List Level} {cv : ConstructorVal} {as vs : List Expr}
    (hc : findDecl σ.decls c = some (.ctorInfo cv)) (hlen' : as.length = vs.length)
    (ih : ∀ (i : Nat) a v, as[i]? = some a → vs[i]? = some v → Sound E B lps a v) :
    Sound E B lps (mkAppN (.const c us) as.toArray) (mkAppN (.const c us) vs.toArray) ∧
      SpineOK σ E B lps (mkAppN (.const c us) as.toArray) (mkAppN (.const c us) vs.toArray) := by
  have hall : List.Forall₂ (Sound E B lps) as vs := CasesWhred.forall₂_of_getElem? hlen' ih
  obtain ⟨ι, η, s, k, order, hB, -, -, -, hmo, -⟩ := henv.lookup_ctor (findDecl_sub hsub hc)
  refine ⟨fun he ht => special_congr hE hB rfl he ht (fun hsat => satTr_ctor_typed hmo hsat ht) hall,
    ?_⟩
  intro c' us' bs bb h hb hs _ _ _
  rw [mkAppN_eq_foldl, mkAppN_eq_foldl] at h
  obtain ⟨rfl, rfl, rfl⟩ := foldl_app_const_inj h
  exact ⟨.inr ⟨cv, hc⟩, vs, rfl, hall⟩

/-- Structure projections of congruent majors at the same parameters. -/
theorem projTerm_dcong {ι : Metalean.IndSig} {η : Metalean.Head ζ (.inductive ι)}
    {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} (hst : (E.get η).block.IsStructure s c) {ℓ : Nat}
    (ls : Fin ι.nlevels → Metalean.Level ℓ) (f : Fin (ι.ctors s c).nfields) {n : Nat}
    (ps : Fin ι.nparams → Metalean.Expr ζ ℓ n) {Γ₁ Γ₂ : Metalean.Ctx ζ ℓ 0 n}
    {maj₁ maj₂ : Metalean.Expr ζ ℓ n} {Q : Prop} (hmaj : DCong E Q Γ₁ Γ₂ maj₁ maj₂) :
    DCong E Q Γ₁ Γ₂ (hst.projTerm η ls ps f maj₁) (hst.projTerm η ls ps f maj₂) := by
  let majG : Metalean.Expr ζ ℓ (n + 1) := .var (Fin.last n)
  let σ' (maj : Metalean.Expr ζ ℓ n) : Metalean.Subst ζ ℓ (n + 1) n :=
    Fin.lastCases maj fun v => .var v
  have key (maj) : hst.projTerm η ls ps f maj =
      (hst.projTerm η ls (fun p => (ps p).wk) f majG).subst (σ' maj) := by
    rw [Metalean.Inductive.IsStructure.projTerm_subst]
    congr 1
    · funext p
      simp only [σ', Metalean.Expr.wk, Metalean.Expr.wkFrom, Metalean.Expr.rename_subst]
      conv => lhs; rw [← Metalean.Expr.subst_id (ps p)]
      congr 1
      funext v
      simp [Metalean.Subst.precomp, Metalean.Subst.id]
    · simp [majG, σ', Metalean.Expr.subst]
  rw [key maj₁, key maj₂]
  refine DCong.subst _ fun v => ?_
  cases v using Fin.lastCases with
  | last => simpa [σ'] using hmaj
  | cast v => simp only [σ', Fin.lastCases_castSucc]; exact .refl

/-- A projection of a major that evaluates: the translation of the projection of the value is
definitionally equal. -/
theorem proj_congr (henv : ProgEnv P ζ E B) (hE : EnvWF E) {S : Name} {i : Nat} {e m : Expr}
    (ih : Sound E B lps e m) {t T : Metalean.Expr ζ lps.length 0}
    (he : TrM E B lps .nil [] (.proj S i e) t) (ht : E[.nil] ⊢ t : T) :
    ∃ t₂, TrM E B lps .nil [] (.proj S i m) t₂ ∧ E[.nil] ⊢ t ≡ t₂ : T := by
  generalize hx : Expr.proj S i e = x at he
  cases he with
  | projStruct hst hi hS he' _ =>
    cases hx
    have hmaj := recr_major (by rw [← hst.projTerm_eq_recr]; exact ht)
    obtain ⟨m', hm', hd⟩ := ih he' hmaj
    have hd2 := DCong.defeq hE not_false (projTerm_dcong hst _ _ _ (.leaf hd)) nil_ok
      (DCong.CtxConv.refl nil_ok) ht
    refine ⟨_, InstPre.PreTr.recover henv.metaOrderOK
      (.projStruct hst hi hS (InstPre.PreTr.ofTrM hm')) (InstPre.Thin.id _) nil_ok
      ⟨T, by rw [Metalean.Expr.rename_id]; exact hd2.right⟩, hd2⟩
  | projProof hi hS hs hc hr hf hns he' _ =>
    cases hx
    have hmaj := recr_major (by rw [projProofTerm] at ht; exact ht)
    obtain ⟨m', hm', hd⟩ := ih he' hmaj
    have hd2 := DCong.defeq hE not_false
      (TrDet.projProofTerm_dcong _ _ _ _ _ _ (fun _ => .refl) (.leaf hd)) nil_ok
      (DCong.CtxConv.refl nil_ok) ht
    refine ⟨_, InstPre.PreTr.recover henv.metaOrderOK
      (.projProof hi hS hs hc hr hf hns (InstPre.PreTr.ofTrM hm')) (InstPre.Thin.id _) nil_ok
      ⟨T, by rw [Metalean.Expr.rename_id]; exact hd2.right⟩, hd2⟩
  | special => exact absurd hx (ne_mkAppN_const fun _ _ h => by cases h)
  | _ => cases hx

/-- The case of `SrcEval.proj`. -/
theorem case_proj (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv σ.decls P) {S : Name}
    {i : Nat} {e m a : Expr} {fs : List Expr} (hcv : CtorValue σ S m 0 fs) (ha : fs[i]? = some a)
    (ih : Sound E B lps e m) :
    Sound E B lps (.proj S i e) a ∧ SpineOK σ E B lps (.proj S i e) a := by
  refine ⟨fun he ht => ?_, spineOK_of_head fun _ _ h => by cases h⟩
  obtain ⟨t₂, ht₂, hd⟩ := proj_congr henv hE ih he ht
  obtain ⟨a', ha', hd'⟩ := proj_defeq henv hE nil_ok hsub hcv ha ht₂ hd.right
  exact ⟨a', ha', dtrans hE hd hd'⟩

/-- The case of `SrcEval.projProp`. -/
theorem case_projProp (henv : ProgEnv P ζ E B) (hE : EnvWF E) {S : Name} {i : Nat} {e m : Expr}
    (ih : Sound E B lps e m) :
    Sound E B lps (.proj S i e) (.proj S i m) ∧ SpineOK σ E B lps (.proj S i e) (.proj S i m) :=
  ⟨fun he ht => proj_congr henv hE ih he ht, spineOK_of_head fun _ _ h => by cases h⟩

/-- Replacing related entries at one index keeps two lists related. -/
theorem forall₂_set {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ R l l') {x : α} {y : β} (hxy : R x y) :
    ∀ j, List.Forall₂ R (l.set j x) (l'.set j y) := by
  induction h with
  | nil => intro _; exact .nil
  | cons hr hrest ih =>
    intro j
    cases j with
    | zero => exact .cons hxy hrest
    | succ j => exact .cons hr (ih j)

/-- Replacing the major premise of a `casesOn` spine by its value. -/
theorem major_congr (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv σ.decls P)
    {c : Name} {us : List Level} {iv : InductiveVal} (hcs : σ.casesOn? c = some iv)
    {as : List Expr} {j : Nat} {m mv : Expr} (hm : as[j]? = some m) (ih : Sound E B lps m mv)
    {t T : Metalean.Expr ζ lps.length 0}
    (he : TrM E B lps .nil [] (mkAppN (.const c us) as.toArray) t) (ht : E[.nil] ⊢ t : T) :
    ∃ t₂, TrM E B lps .nil [] (mkAppN (.const c us) (as.set j mv).toArray) t₂ ∧
      E[.nil] ⊢ t ≡ t₂ : T := by
  obtain ⟨d, hd⟩ := casesOn?_defn hcs
  obtain ⟨η, hB, -⟩ := henv.lookup_def (findDecl_sub hsub hd)
  have hns : ¬ SpecialHead B (.const c us) := by
    rintro ⟨c', us', b, hfn, hb, hs⟩
    cases hfn
    rw [hB] at hb; cases hb; cases hs
  obtain ⟨h', as', hh, has, rfl⟩ := CasesWhred.trM_spine_inv hns as he
  obtain ⟨-, htyped⟩ := InstPre.appList_inv ht
  obtain ⟨m', hm', hmm⟩ : ∃ m', as'[j]? = some m' ∧ TrM E B lps .nil [] m m' := by
    have hj : j < as'.length := by
      rw [← has.length_eq]; exact (List.getElem?_eq_some_iff.mp hm).1
    exact ⟨_, List.getElem?_eq_getElem hj, forall₂_getElem? has j m _ hm
      (List.getElem?_eq_getElem hj)⟩
  obtain ⟨A, hA⟩ := htyped m' (List.mem_of_getElem? hm')
  obtain ⟨mv', hmv', hd'⟩ := ih hmm hA
  have hcong : List.Forall₂ (DCong E False .nil .nil) as' (as'.set j mv') := by
    have := forall₂_set (l := as') (l' := as')
      (List.forall₂_same.mpr fun x _ => (DCong.refl : DCong E False .nil .nil x x))
      (x := m') (y := mv') (.leaf hd') j
    have hself : as'.set j m' = as' := by
      obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hm'
      exact List.set_getElem_self hj
    rwa [hself] at this
  have h1 := DCong.defeq hE not_false
    (TrDet.appList .refl hcong.length_eq (forall₂_getElem? hcong)) nil_ok
    (DCong.CtxConv.refl nil_ok) ht
  obtain ⟨t₂, ht₂, hred⟩ := TrM.apps hh (forall₂_set has hmv' j)
  exact ⟨t₂, ht₂, dtrans hE h1 (WHRedS.defeq hE nil_ok hred h1.right)⟩

/-- A list with its entry `j` replaced, split before its last entry. -/
theorem split_set {as : List Expr} {j : Nat} (x : Expr) (hj : j + 1 < as.length) :
    ∃ args a, as.set j x = args ++ [a] ∧ args.length + 1 = as.length ∧ args[j]? = some x ∧
      ∀ k, k ≠ j → (args ++ [a])[k]? = as[k]? := by
  have hne : as.set j x ≠ [] := by
    intro h; have := congrArg List.length h
    simp only [List.length_set, List.length_nil] at this; omega
  refine ⟨_, _, (List.dropLast_append_getLast hne).symm, ?_, ?_, ?_⟩
  · simp; omega
  · rw [List.getElem?_dropLast]
    simp only [List.length_set]
    split
    · exact List.getElem?_set_self (by omega)
    · omega
  · intro k hk
    rw [List.dropLast_append_getLast hne, List.getElem?_set_ne (Ne.symm hk)]

/-- The case of `SrcEval.casesIota`. -/
theorem case_casesIota (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv σ.decls P)
    {c : Name} {us : List Level} {iv : InductiveVal} {as fs : List Expr} {m mv alt v : Expr}
    {i : Nat} (hcs : σ.casesOn? c = some iv) (hlen : as.length = casesArity iv)
    (hm : as[casesMajor iv]? = some m) (hcv : CtorValue σ iv.name mv i fs)
    (halt : as[casesMajor iv + 1 + i]? = some alt) (ihm : Sound E B lps m mv)
    (ihb : Sound E B lps (mkAppN alt fs.toArray) v) :
    Sound E B lps (mkAppN (.const c us) as.toArray) v ∧
      SpineOK σ E B lps (mkAppN (.const c us) as.toArray) v := by
  obtain ⟨d, hd⟩ := casesOn?_defn hcs
  refine ⟨fun he ht => ?_, spineOK_defn henv hsub hd⟩
  obtain ⟨t₂, ht₂, hd2⟩ := major_congr henv hE hsub hcs hm ihm he ht
  have hj : casesMajor iv + 1 < as.length := by
    have := (List.getElem?_eq_some_iff.mp halt).1; omega
  obtain ⟨args, a, hsplit, hlen₂, hm₂, hrest⟩ := split_set mv hj
  rw [hsplit] at ht₂
  obtain ⟨t₃, ht₃, hred⟩ := casesOn_whred henv hsub hcs (by omega) hm₂ hcv
    (by rw [hrest _ (by omega)]; exact halt) ht₂
  have hd3 := WHRedS.defeq hE nil_ok hred hd2.right
  obtain ⟨t', ht', hd'⟩ := ihb ht₃ hd3.right
  exact ⟨t', ht', dtrans hE (dtrans hE hd2 hd3) hd'⟩

/-- The cases of `SrcEval.casesLitZero` and `casesLitSucc`. -/
theorem case_casesLit (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv σ.decls P)
    {c : Name} {us : List Level} {iv : InductiveVal} {as : List Expr} {m alt v : Expr}
    {k : Nat} (hcs : σ.casesOn? c = some iv) (hnat : iv.name = ``Nat)
    (hlen : as.length = casesArity iv) (hm : as[casesMajor iv]? = some m)
    (halt : as[casesMajor iv + 1 + min k 1]? = some alt)
    (ihm : Sound E B lps m (.lit (.natVal k)))
    (ihb : Sound E B lps (if k = 0 then alt else .app alt (.lit (.natVal (k - 1)))) v) :
    Sound E B lps (mkAppN (.const c us) as.toArray) v ∧
      SpineOK σ E B lps (mkAppN (.const c us) as.toArray) v := by
  obtain ⟨d, hd⟩ := casesOn?_defn hcs
  refine ⟨fun he ht => ?_, spineOK_defn henv hsub hd⟩
  obtain ⟨t₂, ht₂, hd2⟩ := major_congr henv hE hsub hcs hm ihm he ht
  have hj : casesMajor iv + 1 < as.length := by
    have := (List.getElem?_eq_some_iff.mp halt).1; omega
  obtain ⟨args, a, hsplit, hlen₂, hm₂, hrest⟩ := split_set (.lit (.natVal k)) hj
  rw [hsplit] at ht₂
  obtain ⟨alt', t₃, halt', ht₃, hred⟩ := casesOnLit_whred henv hsub hcs hnat (by omega) hm₂ ht₂
  rw [hrest _ (by omega), halt, Option.some.injEq] at halt'
  subst halt'
  have hd3 := WHRedS.defeq hE nil_ok hred hd2.right
  obtain ⟨t', ht', hd'⟩ := ihb ht₃ hd3.right
  exact ⟨t', ht', dtrans hE (dtrans hE hd2 hd3) hd'⟩

/-- Locals that denote congruent terms, with definitional equality at the leaves. -/
def LocRel (E : Metalean.Env ζ) {ℓ n : Nat} (Γ₁ Γ₂ : Metalean.Ctx ζ ℓ 0 n) (Δ₁ Δ₂ : MLCtx ζ ℓ n) :
    Prop :=
  (∀ i a, Δ₁.findB i = some a → ∃ b, Δ₂.findB i = some b ∧ DCong E False Γ₁ Γ₂ a b) ∧
  ∀ x a, Δ₁.findF x = some a → ∃ b, Δ₂.findF x = some b ∧ DCong E False Γ₁ Γ₂ a b

/-- Entering a binder on both sides. -/
theorem LocRel.pushLam {ℓ n : Nat} {Γ₁ Γ₂ : Metalean.Ctx ζ ℓ 0 n} {Δ₁ Δ₂ : MLCtx ζ ℓ n}
    (A₁ A₂ : Metalean.Expr ζ ℓ n) (h : LocRel E Γ₁ Γ₂ Δ₁ Δ₂) :
    LocRel E (Γ₁.snoc A₁) (Γ₂.snoc A₂) (Δ₁.pushLam none) (Δ₂.pushLam none) := by
  constructor
  · intro i a ha
    cases i with
    | zero =>
      simp only [MLCtx.pushLam, MLCtx.findB, MLDecl.denote, Option.some.injEq] at ha ⊢
      exact ⟨_, rfl, ha ▸ .refl⟩
    | succ i =>
      simp only [MLCtx.pushLam, MLCtx.findB, MLCtx.findB_map_wk, Option.map_eq_some_iff] at ha ⊢
      obtain ⟨a, ha, rfl⟩ := ha
      obtain ⟨b, hb, hab⟩ := h.1 i a ha
      exact ⟨b.wk, ⟨b, hb, rfl⟩, DCong.wk A₁ A₂ hab⟩
  · intro x a ha
    simp only [MLCtx.pushLam, MLCtx.findF, MLCtx.findF_map_wk, Option.map_eq_some_iff] at ha ⊢
    obtain ⟨a, ha, rfl⟩ := ha
    obtain ⟨b, hb, hab⟩ := h.2 x a ha
    exact ⟨b.wk, ⟨b, hb, rfl⟩, DCong.wk A₁ A₂ hab⟩

/-- No locals. -/
theorem LocRel.nil {ℓ n : Nat} {Γ₁ Γ₂ : Metalean.Ctx ζ ℓ 0 n} : LocRel E Γ₁ Γ₂ [] [] :=
  ⟨fun _ _ h => by simp [MLCtx.findB] at h, fun _ _ h => by simp [MLCtx.findF] at h⟩

/-- Pushing related `let` values. -/
theorem LocRel.cons {ℓ n : Nat} {Γ₁ Γ₂ : Metalean.Ctx ζ ℓ 0 n} {Δ₁ Δ₂ : MLCtx ζ ℓ n}
    {v₁ v₂ : Metalean.Expr ζ ℓ n} (h : LocRel E Γ₁ Γ₂ Δ₁ Δ₂) (hv : DCong E False Γ₁ Γ₂ v₁ v₂) :
    LocRel E Γ₁ Γ₂ ((none, .vlet v₁) :: Δ₁) ((none, .vlet v₂) :: Δ₂) := by
  constructor
  · intro i a ha
    cases i with
    | zero =>
      simp only [MLCtx.findB, MLDecl.denote, Option.some.injEq] at ha ⊢
      exact ⟨_, rfl, ha ▸ hv⟩
    | succ i => exact h.1 i a (by simpa [MLCtx.findB] using ha)
  · intro x a ha
    exact h.2 x a (by simpa [MLCtx.findF] using ha)

/-- Pre-translations of the arguments of a spine in related locals. -/
theorem replace_args {n : Nat} {Δ₂ : MLCtx ζ lps.length n}
    {Γ₁ Γ₂ : Metalean.Ctx ζ lps.length 0 n} {as : List Expr}
    {as₁ : List (Metalean.Expr ζ lps.length n)}
    (h : List.Forall₂ (fun a a₁ => ∃ a₂, InstPre.PreTr E B lps Δ₂ a a₂ ∧
      DCong E False Γ₁ Γ₂ a₁ a₂) as as₁) :
    ∃ as₂, List.Forall₂ (InstPre.PreTr E B lps Δ₂) as as₂ ∧
      List.Forall₂ (DCong E False Γ₁ Γ₂) as₁ as₂ := by
  induction h with
  | nil => exact ⟨[], .nil, .nil⟩
  | cons hh _ ih =>
    obtain ⟨a₂, ha, hc⟩ := hh
    obtain ⟨as₂, h₁, h₂⟩ := ih
    exact ⟨a₂ :: as₂, .cons ha h₁, .cons hc h₂⟩

/-- A pre-translation in locals related by definitional equality gives a congruent
pre-translation. -/
theorem PreTr.replace {n : Nat} {Δ₁ : MLCtx ζ lps.length n} {e : Expr}
    {t₁ : Metalean.Expr ζ lps.length n} (h : InstPre.PreTr E B lps Δ₁ e t₁) :
    ∀ {Γ₁ Γ₂ : Metalean.Ctx ζ lps.length 0 n} {Δ₂ : MLCtx ζ lps.length n},
      LocRel E Γ₁ Γ₂ Δ₁ Δ₂ →
      ∃ t₂, InstPre.PreTr E B lps Δ₂ e t₂ ∧ DCong E False Γ₁ Γ₂ t₁ t₂ := by
  induction h with
  | bvar h =>
    intro _ _ _ hL
    obtain ⟨b, hb, hc⟩ := hL.1 _ _ h
    exact ⟨b, .bvar hb, hc⟩
  | fvar h =>
    intro _ _ _ hL
    obtain ⟨b, hb, hc⟩ := hL.2 _ _ h
    exact ⟨b, .fvar hb, hc⟩
  | sort h => intros; exact ⟨_, .sort h, .refl⟩
  | const h₁ h₂ => intros; exact ⟨_, .const h₁ h₂, .refl⟩
  | lit h h₀ h₁ => intros; exact ⟨_, .lit h h₀ h₁, .refl⟩
  | special hb hs hlen _ hsat ih =>
    intro Γ₁ Γ₂ Δ₂ hL
    obtain ⟨as₂, h₁, h₂⟩ := replace_args (CasesWhred.forall₂_of_getElem? hlen
      fun i a a' ha ha' => ih i a a' ha ha' hL)
    obtain ⟨t₂, hsat₂⟩ := InstPre.SatTr.replace hsat as₂ h₂.length_eq.symm
    exact ⟨t₂, .special hb hs h₁.length_eq (forall₂_getElem? h₁) hsat₂,
      SatTr.dcong hsat hsat₂ h₂.length_eq (forall₂_getElem? h₂)⟩
  | app hns _ _ ih₁ ih₂ =>
    intro _ _ _ hL
    obtain ⟨f₂, hf, hcf⟩ := ih₁ hL
    obtain ⟨a₂, ha, hca⟩ := ih₂ hL
    exact ⟨_, .app hns hf ha, .app hcf hca⟩
  | lam _ _ ih₁ ih₂ =>
    intro _ _ _ hL
    obtain ⟨A₂, hA, hcA⟩ := ih₁ hL
    obtain ⟨b₂, hb, hcb⟩ := ih₂ (hL.pushLam _ A₂)
    exact ⟨_, .lam hA hb, .lam hcA hcb⟩
  | forallE _ _ ih₁ ih₂ =>
    intro _ _ _ hL
    obtain ⟨A₂, hA, hcA⟩ := ih₁ hL
    obtain ⟨b₂, hb, hcb⟩ := ih₂ (hL.pushLam _ A₂)
    exact ⟨_, .forallE hA hb, .forallE hcA hcb⟩
  | letE _ _ _ ih₁ ih₂ ih₃ =>
    intro _ _ _ hL
    obtain ⟨T₂, hT, hcT⟩ := ih₁ hL
    obtain ⟨v₂, hv, hcv⟩ := ih₂ hL
    obtain ⟨b₂, hb, hcb⟩ := ih₃ (hL.cons hcv)
    refine ⟨_, .letE hT hv hb, .letE hcT hcv ?_⟩
    rw [Metalean.Expr.inst_wk, Metalean.Expr.inst_wk]
    exact hcb
  | mdata _ ih =>
    intro _ _ _ hL
    obtain ⟨t₂, h, hc⟩ := ih hL
    exact ⟨t₂, .mdata h, hc⟩
  | projStruct hst hi hS _ ih =>
    intro _ _ _ hL
    obtain ⟨e₂, h, hc⟩ := ih hL
    exact ⟨_, .projStruct hst hi hS h, projTerm_dcong hst _ _ _ hc⟩
  | projProof hi hS hs hc hr hf hns _ ih =>
    intro _ _ _ hL
    obtain ⟨e₂, h, hce⟩ := ih hL
    exact ⟨_, .projProof hi hS hs hc hr hf hns h,
      TrDet.projProofTerm_dcong _ _ _ _ _ _ (fun _ => .refl) hce⟩

/-- The case of `SrcEval.zeta`. -/
theorem case_zeta (henv : ProgEnv P ζ E B) (hE : EnvWF E) {x : Name} {Ty val val' b v : Expr}
    {nd : Bool} (ihv : Sound E B lps val val') (ihb : Sound E B lps (b.instantiate1' val') v) :
    Sound E B lps (.letE x Ty val b nd) v ∧ SpineOK σ E B lps (.letE x Ty val b nd) v := by
  refine ⟨fun {t T} he ht => ?_, spineOK_of_head fun _ _ h => by cases h⟩
  generalize hx : Expr.letE x Ty val b nd = y at he
  cases he with
  | letE _ hv hb =>
    cases hx
    obtain ⟨r, -, hvT, hbr, -⟩ := ht.letE_inv nil_ok
    rw [Metalean.Expr.inst_wk] at hbr
    obtain ⟨tv, htv, hdv⟩ := ihv hv hvT
    have hL := LocRel.cons (Γ₁ := .nil) (Γ₂ := .nil) LocRel.nil (.leaf hdv)
    obtain ⟨b₂, hb₂, hcb⟩ := PreTr.replace (InstPre.PreTr.ofTrM hb) hL
    have hd1 := DCong.defeq hE not_false hcb nil_ok (DCong.CtxConv.refl nil_ok) hbr
    have hb₂' := InstPre.PreTr.recover henv.metaOrderOK hb₂ (InstPre.Thin.id _) nil_ok
      ⟨r, by rw [Metalean.Expr.rename_id]; exact hd1.right⟩
    obtain ⟨tb, htb, hdb⟩ := TrM.inst_let hE nil_ok henv.metaOrderOK hb₂' htv hd1.right
    obtain ⟨t', ht', hd'⟩ := ihb htb hdb.left
    have hz := WHRed.zeta_defeq hE nil_ok ht
    rw [Metalean.Expr.inst_wk] at hz
    exact ⟨t', ht', dtrans hE (dtrans hE (dtrans hE hz hd1) hdb.symm) hd'⟩
  | special => exact absurd hx (ne_mkAppN_const fun _ _ h => by cases h)
  | _ => cases hx

/-- A constant with an arity is a constructor, a recognized `casesOn`, an erased quotient constant
or a recursor. -/
theorem specialArity_some {c : Name} {ar : Nat} (h : specialArity σ c = some ar) :
    (∃ cv, findDecl σ.decls c = some (.ctorInfo cv) ∧ ar = cv.numParams + cv.numFields) ∨
      (∃ iv, σ.casesOn? c = some iv) ∨
      (∃ qv, findDecl σ.decls c = some (.quotInfo qv) ∧ quotEvalArity qv.kind = some ar) ∨
      ∃ rv, findDecl σ.decls c = some (.recInfo rv) ∧
        ar = rv.numParams + rv.numMotives + rv.numMinors + rv.numIndices + 1 := by
  unfold specialArity at h
  split at h
  · cases h; exact .inl ⟨_, ‹_›, rfl⟩
  · exact .inr (.inr (.inl ⟨_, ‹_›, h⟩))
  · cases h; exact .inr (.inr (.inr ⟨_, ‹_›, rfl⟩))
  · obtain ⟨iv, hiv, -⟩ := Option.map_eq_some_iff.1 h
    exact .inr (.inl ⟨iv, hiv⟩)

/-- `SpineOK` of an η-expanded spine: its head is a recognized `casesOn`, a quotient constant or a
constructor with fewer arguments than its arity, none of which `SpineOK` covers. -/
theorem spineOK_eta (henv : ProgEnv P ζ E B) (hsub : SubEnv σ.decls P) {c : Name}
    {us : List Level} {as : List Expr} {e' : Expr} (he : σ.etaSpine? c us as = some e') :
    SpineOK σ E B lps (mkAppN (.const c us) as.toArray) e' := by
  intro c' us' bs b h hb hs hq hr hct
  rw [mkAppN_eq_foldl, mkAppN_eq_foldl] at h
  obtain ⟨rfl, rfl, rfl⟩ := foldl_app_const_inj h
  unfold EvalEnv.etaSpine? at he
  split at he
  · rename_i ar _ har
    split at he
    · rcases specialArity_some har with ⟨cv, hcv, rfl⟩ | ⟨iv, hiv⟩ | ⟨qv, hqv, -⟩ | ⟨rv, hrv, -⟩
      · have := hct cv hcv; omega
      · obtain ⟨d, hd⟩ := casesOn?_defn hiv
        exact (defn_not_special henv hsub hd hb hs).elim
      · obtain ⟨η, hB⟩ := henv.lookup_quot (findDecl_sub hsub hqv)
        rw [hB] at hb; cases hb
        exact (hq _ _ rfl).elim
      · obtain ⟨ι, η, s, os, hB, -⟩ := henv.lookup_recr (findDecl_sub hsub hrv)
        rw [hB] at hb; cases hb
        exact (hr _ _ _ _ rfl).elim
    · cases he
  · cases he

/-- Lifting by `a` then by `b` is lifting by `a + b`. -/
theorem lift_add (e : Expr) (a : Nat) : ∀ b,
    (e.liftLooseBVars' 0 a).liftLooseBVars' 0 b = e.liftLooseBVars' 0 (a + b)
  | 0 => by rw [liftLooseBVars'_zero]; rfl
  | b + 1 => by
    rw [← InstPre.liftLooseBVars'_succ (e.liftLooseBVars' 0 a) 0 b, lift_add e a b,
      InstPre.liftLooseBVars'_succ]
    rfl

/-- The arguments of the body of an η-expansion over `k + 1` binders, as the arguments over the
last `k` binders of the spine applied to the first bound variable. -/
theorem eta_args (as : List Expr) (k : Nat) :
    as.map (fun e : Expr => e.liftLooseBVars' 0 (k + 1)) ++
        (List.range (k + 1)).reverse.map Expr.bvar =
      (as.map (fun e : Expr => e.liftLooseBVars' 0 1) ++ [Expr.bvar 0]).map
          (fun e : Expr => e.liftLooseBVars' 0 k) ++
        (List.range k).reverse.map Expr.bvar := by
  rw [List.map_append, List.map_map, List.range_succ, List.reverse_append, List.append_assoc]
  congr 1
  · apply List.map_congr_left
    intro a _
    simp only [Function.comp, lift_add, Nat.add_comm]
  · simp [Expr.liftLooseBVars']

/-- The translation of a Π is a Π. -/
theorem trM_forallE_inv {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
    {Δ : MLCtx ζ lps.length n} {x : Name} {A b : Expr} {bi : BinderInfo}
    {V : Metalean.Expr ζ lps.length n} (h : TrM E B lps Γ Δ (.forallE x A b bi) V) :
    ∃ A' b', V = .forallE A' b' ∧ TrM E B lps Γ Δ A A' ∧
      TrM E B lps (Γ.snoc A') (Δ.pushLam none) b b' := by
  generalize hx : Expr.forallE x A b bi = e at h
  cases h with
  | forallE hA hb => cases hx; exact ⟨_, _, rfl, hA, hb⟩
  | special => exact absurd hx (ne_mkAppN_const fun _ _ h => by cases h)
  | _ => cases hx

/-- η-expansion over the leading binders of the type: a typed translation of a closed-head
spine is definitionally equal to a translation of the spine's η-expansion over `k` binders of a
Lean type that translates to its type. Reference: Metalean's `eta` (`ML Typing/Defs.lean:144`). -/
theorem eta_lams (hE : EnvWF E)
    (hord : ∀ c {ι : Metalean.IndSig} (η : Metalean.Head ζ (.inductive ι)) (s : Fin ι.nsorts)
      (k : Fin (ι.nctors s)) (o : List Nat), B c = some (.ctor η s k o) →
      MetaOrderOK o (ι.ctors s k).nfields (ι.ctors s k).nrecFields)
    (h₀ : Expr) (hh₀ : h₀.liftLooseBVars' 0 1 = h₀) :
    ∀ (k : Nat) {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
      {as : List Expr} {t T Y : Metalean.Expr ζ lps.length n} {ty e' : Expr},
      E[Γ] ⊢ ok → TrM E B lps Γ Δ (mkAppN h₀ as.toArray) t → E[Γ] ⊢ t : T →
      TrM E B lps Γ Δ ty Y → E[Γ] ⊢ T ≡ Y typ →
      lamsOf k ty (mkAppN h₀ (as.map (·.liftLooseBVars' 0 k) ++
        (List.range k).reverse.map Expr.bvar).toArray) = some e' →
      ∃ t', TrM E B lps Γ Δ e' t' ∧ E[Γ] ⊢ t ≡ t' : T
  | 0, _, _, _, as, t, T, Y, ty, e', _, he, ht, _, _, hl => by
    simp only [lamsOf, Option.some.injEq, List.range_zero, List.reverse_nil, List.map_nil,
      List.append_nil, liftLooseBVars'_zero, List.map_id'] at hl
    subst hl
    exact ⟨t, he, ht⟩
  | k + 1, n, Γ, Δ, as, t, T, Y, ty, e', hΓ, he, ht, hY, hTY, hl => by
    cases ty with
    | forallE x D b bi =>
      simp only [lamsOf] at hl
      obtain ⟨e'', he'', rfl⟩ := Option.map_eq_some_iff.1 hl
      obtain ⟨D', Y₂, rfl, hD, hY₂⟩ := trM_forallE_inv hY
      · have ht' : E[Γ] ⊢ t : .forallE D' Y₂ := hTY.conv ht
        obtain ⟨u, hu⟩ := hTY.right
        obtain ⟨l₁, l₂, hD'l, hY₂l, -⟩ := hu.forallE_ty_inv
        have hΓ' : E[Γ.snoc D'] ⊢ ok := .snoc hΓ ⟨l₁, hD'l⟩
        have hD'w : E[Γ.snoc D'] ⊢ D'.wk : .sort l₁ := Defeq.wk D' hD'l
        have htw : E[Γ.snoc D'] ⊢ t.wk : .forallE D'.wk (Y₂.wkFrom n) := by
          simpa [Metalean.Expr.wk] using Defeq.wk D' ht'
        have heta : E[Γ] ⊢ .lam D' (.app t.wk (.var (Fin.last n))) ≡ t : .forallE D' Y₂ :=
          .eta hD'l hY₂l hD'w htw ht'
        obtain ⟨Y₂', hbody, hπ⟩ := heta.left.lam_inv hΓ
        have happ : E[Γ.snoc D'] ⊢ .app t.wk (.var (Fin.last n)) : Y₂ :=
          (TypeEq.forallE_inj hE hΓ hπ).2.symm.conv hbody
        -- the spine in the extended context
        have hf : TrM E B lps (Γ.snoc D') (Δ.pushLam none)
            (mkAppN h₀ (as.map (fun e : Expr => e.liftLooseBVars' 0 1)).toArray) t.wk := by
          have := TrM.weakBV (A := D') he
          rwa [mkAppN_eq_foldl, liftLooseBVars'_foldl, hh₀, ← mkAppN_eq_foldl] at this
        have hv : TrM E B lps (Γ.snoc D') (Δ.pushLam none) (.bvar 0) (.var (Fin.last n)) :=
          .bvar (by simp [MLCtx.pushLam, MLCtx.findB, MLDecl.denote])
        obtain ⟨t₁, ht₁, hred⟩ := TrM.apps hf (.cons hv .nil)
        have hd1 := WHRedS.defeq hE hΓ' hred happ
        have hsp : mkAppN (mkAppN h₀ (as.map (fun e : Expr => e.liftLooseBVars' 0 1)).toArray) [Expr.bvar 0].toArray =
            mkAppN h₀ (as.map (fun e : Expr => e.liftLooseBVars' 0 1) ++ [Expr.bvar 0]).toArray := by
          simp only [mkAppN_eq_foldl, List.foldl_append]
        rw [hsp] at ht₁
        rw [eta_args] at he''
        obtain ⟨t'', ht'', hd''⟩ := eta_lams hE hord h₀ hh₀ k hΓ' ht₁ hd1.right hY₂
          (Metalean.IsType.typeEq ⟨l₂, hY₂l⟩) he''
        refine ⟨.lam D' t'', .lam hD ht'', ?_⟩
        have hlam : E[Γ] ⊢ .lam D' (.app t.wk (.var (Fin.last n))) ≡ .lam D' t'' :
            .forallE D' Y₂ :=
          .lamDF hD'l hY₂l hY₂l (hd1.trans hd'') (hd1.trans hd'')
        exact hTY.symm.conv (heta.symm.trans hlam)
    | _ => simp [lamsOf] at hl

/-- The Lean type of a spine, instantiated at its arguments, translates to the type of the
translated spine. -/
theorem piInst_tr (hE : EnvWF E)
    (hord : ∀ c {ι : Metalean.IndSig} (η : Metalean.Head ζ (.inductive ι)) (s : Fin ι.nsorts)
      (k : Fin (ι.nctors s)) (o : List Nat), B c = some (.ctor η s k o) →
      MetaOrderOK o (ι.ctors s k).nfields (ι.ctors s k).nrecFields) :
    ∀ (as : List Expr) {as' : List (Metalean.Expr ζ lps.length 0)}
      {f F Y₀ T : Metalean.Expr ζ lps.length 0} {ty₀ ty : Expr},
      TrM E B lps .nil [] ty₀ Y₀ → E[.nil] ⊢ f : F → E[.nil] ⊢ F ≡ Y₀ typ →
      List.Forall₂ (TrM E B lps .nil []) as as' → E[.nil] ⊢ f.appList as' : T →
      piInst as ty₀ = some ty → ∃ Y, TrM E B lps .nil [] ty Y ∧ E[.nil] ⊢ T ≡ Y typ
  | [], _, f, F, Y₀, T, ty₀, ty, hY₀, hf, hFY, has, hT, hp => by
    cases has
    simp only [piInst, Option.some.injEq] at hp
    subst hp
    exact ⟨Y₀, hY₀, (Defeq.uniqTy hE nil_ok hT hf).trans hFY⟩
  | a :: as, _, f, F, Y₀, T, ty₀, ty, hY₀, hf, hFY, has, hT, hp => by
    cases has with
    | @cons _ a' _ as' ha has =>
      cases ty₀ with
      | forallE x D b bi =>
        simp only [piInst] at hp
        obtain ⟨D', Y₂, rfl, hD, hY₂⟩ := trM_forallE_inv hY₀
        · obtain ⟨⟨F₁, hF₁⟩, -⟩ := InstPre.appList_inv (as := as') hT
          obtain ⟨A₁, B₁, hfA, haA, -⟩ := hF₁.app_inv
          have hπ : E[.nil] ⊢ .forallE A₁ B₁ ≡ .forallE D' Y₂ typ :=
            (Defeq.uniqTy hE nil_ok hfA hf).trans hFY
          have haD : E[.nil] ⊢ a' : D' := (TypeEq.forallE_inj hE nil_ok hπ).1.conv haA
          have hfD : E[.nil] ⊢ f : .forallE D' Y₂ := hπ.conv hfA
          obtain ⟨u, hu⟩ := hFY.right
          obtain ⟨l₁, l₂, hD'l, hY₂l, -⟩ := hu.forallE_ty_inv
          obtain ⟨X, hX, hXd⟩ := TrM.inst hE nil_ok hord hY₂ ha haD hY₂l
          have happ : E[.nil] ⊢ .app f a' : Y₂.inst a' :=
            .appDF hD'l hY₂l hfD haD (hY₂l.inst_congr haD)
          exact piInst_tr hE hord as hX happ (TypeEq.ofDefEq hXd).symm has hT hp
      | _ => simp [piInst] at hp

/-- A constant's type after one new entry. -/
theorem get_there_constType {sig : Metalean.Sig} {ent : Metalean.Entry ζ sig}
    {kind : Metalean.ConstKind} {nl : Nat} (η : Metalean.Head ζ (.const kind nl)) :
    ((E.snoc ent).get (η.map wkS)).constType = (E.get η).constType.map wkS := by
  show ((E.get η).map wkS).constType = _
  generalize E.get η = x
  cases x <;> rfl

/-- A definition's Metalean type is the translation of its Lean type. Reference:
`declared_constant` (MC §3.6). -/
theorem lookup_def_type (h : ProgEnv P ζ E B) {c : Name} {v : DefinitionVal}
    (hc : findDecl P c = some (.defnInfo v)) :
    ∃ η : Metalean.Head ζ (.const .def v.levelParams.length), B c = some (.const η) ∧
      TrM E B v.levelParams .nil [] v.type (E.get η).constType := by
  induction h with
  | nil => simp [findDecl] at hc
  | @«axiom» _ _ _ _ v' _ hP hfr _ _ _ ih | @thm _ _ _ _ v' _ hP hfr _ _ _ _ _ ih
  | @«opaque» _ _ _ _ v' _ _ hP hfr _ _ _ _ _ _ ih =>
    rw [findDecl_cons] at hc
    split at hc
    · cases hc
    · obtain ⟨η, hB, htr⟩ := ih hc
      refine ⟨η.map wkS, by rw [set_wk_ne (Ne.symm ‹_›), hB]; rfl, ?_⟩
      rw [get_there_constType]
      exact TrM.wkEnv (hP.set_ext hfr _) htr
  | @defn _ _ _ _ v' t _ hP hfr _ _ _ ht _ ih =>
    rw [findDecl_cons] at hc
    split at hc
    · rename_i hn
      cases hc
      refine ⟨.here, ?_, ?_⟩
      · have hc' : c = v.name := hn.symm
        simp [Binds.set, hc']
      · show TrM _ _ _ _ _ _ ((Metalean.Entry.def t _).map wkS).constType
        exact TrM.wkEnv (hP.set_ext hfr _) ht
    · obtain ⟨η, hB, htr⟩ := ih hc
      refine ⟨η.map wkS, by rw [set_wk_ne (Ne.symm ‹_›), hB]; rfl, ?_⟩
      rw [get_there_constType]
      exact TrM.wkEnv (hP.set_ext hfr _) htr
  | @induct _ _ _ _ ι _ _ _ Is Cs Rs _ hP _ hfr _ hext _ _ ih =>
    rw [findDecl_append] at hc
    cases hd : findDecl (IndBlock.decls Is Cs Rs) c with
    | some ci =>
      rw [hd] at hc
      cases hc
      obtain ⟨hm, -⟩ := findDecl_eq_some hd
      rcases IndBlock.mem_decls hm with ⟨s, hs⟩ | ⟨s, k, hs⟩ | ⟨s, hs⟩ <;> cases hs
    | none =>
      rw [hd] at hc
      simp only [Option.none_or] at hc
      obtain ⟨η, hB, htr⟩ := ih hc
      have hnot : c ∉ (IndBlock.decls Is Cs Rs).map (·.name) := not_mem_of_findDecl_none hd
      refine ⟨η.map wkS, by rw [hext c hnot, Binds.wk, hB]; rfl, ?_⟩
      rw [get_there_constType]
      exact TrM.wkEnv (hP.ext_ext hfr hext) htr
  | @quot _ _ _ _ _ qs _ hP _ _ hfr _ hext _ ih =>
    rw [findDecl_append] at hc
    cases hd : findDecl (qs.reverse.map ConstantInfo.quotInfo) c with
    | some ci =>
      obtain ⟨hm, -⟩ := findDecl_eq_some hd
      rw [hd] at hc
      cases hc
      simp at hm
    | none =>
      rw [hd] at hc
      simp only [Option.none_or] at hc
      obtain ⟨η, hB, htr⟩ := ih hc
      have hnot := not_mem_of_findDecl_none hd
      rw [quot_names_reverse, List.mem_reverse] at hnot
      refine ⟨η.map wkS, by rw [hext c hnot, Binds.wk, hB]; rfl, ?_⟩
      rw [get_there_constType]
      exact TrM.wkEnv (hP.ext_ext (decls := qs.map .quotInfo)
        (fun ci hci => by obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hci; exact hfr q hq)
        (by rw [List.map_map]; exact hext)) htr

/-- A constant bound to a Metalean constant translates to it at the translated levels. -/
theorem trM_const_inv' {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    {c : Name} {us : List Level} {kind : Metalean.ConstKind} {nl : Nat}
    {η : Metalean.Head ζ (.const kind nl)} (hB : B c = some (.const η))
    {t : Metalean.Expr ζ lps.length n} (h : TrM E B lps Γ Δ (.const c us) t) :
    ∃ ls, t = .const η ls ∧ TrLevels lps us nl = some ls := by
  generalize hx : Expr.const c us = e at h
  cases h with
  | const hb hls =>
    cases hx
    rw [hB] at hb
    cases hb
    exact ⟨_, rfl, hls⟩
  | @special c' us' _ _ _ as _ b _ hb hsp =>
    have := congrArg Expr.getAppFn hx
    rw [mkAppN_eq_foldl, foldl_app_getAppFn] at this
    cases this
    rw [hB] at hb
    cases hb
    cases hsp
  | _ => cases hx

/-- The η-rule on a recognized `casesOn` spine with missing arguments. Reference: DV-23. -/
theorem eta_casesOn (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv σ.decls P)
    {c : Name} {us : List Level} {as : List Expr} {e' : Expr} {iv : InductiveVal}
    (hcs : σ.casesOn? c = some iv) (he : σ.etaSpine? c us as = some e') :
    Sound E B lps (mkAppN (.const c us) as.toArray) e' := by
  intro t T htr ht
  obtain ⟨d, hd⟩ := casesOn?_defn hcs
  obtain ⟨η, hB, hty⟩ := lookup_def_type henv (findDecl_sub hsub hd)
  have har : specialArity σ c = some (casesArity iv) := by simp [specialArity, hd, hcs]
  unfold EvalEnv.etaSpine? at he
  rw [hd, har] at he
  simp only at he
  split at he
  · obtain ⟨ty, hpi, hl⟩ := Option.bind_eq_some_iff.1 he
    have hns : ¬ SpecialHead B (.const c us) := by
      rintro ⟨c', us', b, hfn, hb, hs⟩
      cases hfn
      rw [hB] at hb; cases hb; cases hs
    obtain ⟨h', as', hh, has, rfl⟩ := CasesWhred.trM_spine_inv hns as htr
    obtain ⟨ls, rfl, hls⟩ := trM_const_inv' hB hh
    obtain ⟨⟨F, hF⟩, -⟩ := InstPre.appList_inv ht
    have hY₀ := TrM.instLevels hls hty
    obtain ⟨Y, hY, hTY⟩ := piInst_tr hE henv.metaOrderOK as hY₀ hF hF.const_inv has ht hpi
    exact eta_lams hE henv.metaOrderOK (.const c us) rfl _ nil_ok htr ht hY hTY hl
  · cases he


/-- With distinct universe parameters, a declaration's own parameters translate to the Metalean
parameters in order. -/
theorem trLevels_params_nodup {lps' : List Name} (hnd : lps'.Nodup) {k : Nat}
    {ls : Fin k → Metalean.Level lps'.length}
    (h : TrLevels lps' (lps'.map .param) k = some ls) :
    ∃ hk : k = lps'.length, ∀ i : Fin k, ls i = .param (i.cast hk) := by
  obtain ⟨hk, hget⟩ := TrLevels_get h
  simp only [List.length_map] at hk
  refine ⟨hk.symm, fun i => ?_⟩
  have := hget i
  simp only [List.getElem_map, TrLevel] at this
  have hi : i.val < lps'.length := by omega
  have hfi : lps'.finIdxOf? lps'[i.val] = some ⟨i.val, hi⟩ :=
    List.finIdxOf?_eq_some_iff.mpr ⟨rfl, fun j hj heq => by
      have := (List.Nodup.getElem_inj hnd).mp heq
      rw [Fin.lt_def] at hj; simp at hj this; omega⟩
  rw [hfi] at this
  simp only [Option.map_some, Option.some.injEq] at this
  rw [← this]; rfl

/-- Translated levels at a provably equal count. -/
theorem trLevels_cast {lps' : List Name} {us : List Level} {k k' : Nat}
    {ls : Fin k → Metalean.Level lps'.length} (h : TrLevels lps' us k = some ls) (hk : k = k') :
    ∃ ls' : Fin k' → Metalean.Level lps'.length, TrLevels lps' us k' = some ls' ∧
      ∀ i, ls' i = ls (i.cast hk.symm) := by
  subst hk
  exact ⟨ls, h, fun _ => rfl⟩

/-- A constructor image with fewer arguments than the arity is the constructor's η-term. -/
theorem satTr_ctorEta_inv {ι : Metalean.IndSig} {η : Metalean.Head ζ (.inductive ι)}
    {s : Fin ι.nsorts} {k : Fin (ι.nctors s)} {order : List Nat} {lps' : List Name} {n : Nat}
    {us : List Level} {args : List (Metalean.Expr ζ lps'.length n)}
    {t : Metalean.Expr ζ lps'.length n} (h : SatTr E lps' (.ctor η s k order) us args t)
    (hlt : args.length < ι.nparams + ((ι.ctors s k).nfields + (ι.ctors s k).nrecFields)) :
    ∃ ls t₀, TrLevels lps' us ι.nlevels = some ls ∧
      Metalean.Frontend.ctorTerm (E.get η).block η s k ls order = .ok t₀ ∧
      t = t₀.wkClosed.appList args := by
  cases h with
  | ctorSat ps fs rest fds recFds _ hfs =>
    simp only [List.length_append, List.length_ofFn] at hlt; omega
  | ctorEta hls _ hct => exact ⟨_, _, hls, hct, rfl⟩

/-- The η-rule on a constructor spine with missing arguments, for a constructor whose universe
parameters are distinct (as Lean's kernel requires of every declaration). Reference: DV-23. -/
theorem eta_ctor (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv σ.decls P)
    {c : Name} {us : List Level} {as : List Expr} {e' : Expr} {cv : ConstructorVal}
    (hc : findDecl σ.decls c = some (.ctorInfo cv)) (hnd : cv.levelParams.Nodup)
    (he : σ.etaSpine? c us as = some e') :
    Sound E B lps (mkAppN (.const c us) as.toArray) e' := by
  intro t T htr ht
  have hcP := findDecl_sub hsub hc
  have hname : cv.name = c := (findDecl_eq_some hcP).2
  obtain ⟨ι, η, s, k, order, hB, -, hnp, hnf, -, -⟩ := henv.lookup_ctor hcP
  have har : specialArity σ c = some (cv.numParams + cv.numFields) := by simp [specialArity, hc]
  unfold EvalEnv.etaSpine? at he
  rw [hc, har] at he
  simp only at he
  split at he
  · rename_i hlt
    obtain ⟨ty, hpi, hl⟩ := Option.bind_eq_some_iff.1 he
    obtain ⟨as', hlen, hargs, hsat⟩ := TrM.special_inv hB rfl htr
    obtain ⟨ls, t₀, hls, hct, rfl⟩ := satTr_ctorEta_inv hsat (by omega)
    obtain ⟨-, -, Tc, tc, hTc, htc, htcT⟩ := henv.lookup hE hcP
    have htc' : TrM E B cv.levelParams .nil [] (mkAppN (.const c (cv.levelParams.map .param))
        ([] : List Expr).toArray) tc := by rw [← hname]; exact htc
    obtain ⟨as₁, hlen₁, -, hsat₁⟩ := TrM.special_inv hB rfl htc'
    obtain rfl : as₁ = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen₁.symm)
    obtain ⟨ls₁, t₁, hls₁, hct₁, htc₁⟩ := satTr_ctorEta_inv hsat₁ (by simp; omega)
    have htc₁' : tc = t₁ := htc₁
    subst htc₁'
    obtain ⟨hk, hls₁'⟩ := trLevels_params_nodup hnd hls₁
    obtain ⟨ls', hus, hls'⟩ := trLevels_cast hls hk
    have hTc' := TrM.instLevels hus hTc
    have htcT' := Metalean.Defeq.instLevel (ℓ := cv.levelParams.length) ls' htcT
    have hct' := ctorTerm_instL _ _ _ _ _ _ ls' hct₁
    have hlseq : ls₁{ls'} = ls := by
      funext i
      show (ls₁ i){ls'} = ls i
      rw [hls₁' i]
      show ls' (Fin.cast hk i) = ls i
      rw [hls']
      rfl
    rw [hlseq, hct] at hct'
    injection hct' with h0
    subst h0
    obtain ⟨_, hreg⟩ := htcT'.regular
    obtain ⟨Y, hY, hTY⟩ := piInst_tr hE henv.metaOrderOK as hTc' htcT'
      (Metalean.IsType.typeEq ⟨_, hreg⟩) (CasesWhred.forall₂_of_getElem? hlen hargs) ht hpi
    exact eta_lams hE henv.metaOrderOK (.const c us) rfl _ nil_ok htr ht hY hTY hl
  · cases he

/-! ## Quotients -/

/-- The case of `SrcEval.quotMk`: the element's translation is replaced by its value's. -/
theorem case_quotMk (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv σ.decls P) {c : Name}
    {us : List Level} {qv : QuotVal} {α r a a' : Expr}
    (hc : findDecl σ.decls c = some (.quotInfo qv)) (hk : qv.kind = .ctor)
    (iha : Sound E B lps a a') :
    Sound E B lps (mkAppN (.const c us) [α, r, a].toArray)
        (mkAppN (.const c us) [α, r, a'].toArray) ∧
      SpineOK σ E B lps (mkAppN (.const c us) [α, r, a].toArray)
        (mkAppN (.const c us) [α, r, a'].toArray) := by
  obtain ⟨η, hB⟩ := henv.lookup_quot (findDecl_sub hsub hc)
  rw [hk] at hB
  have srefl : ∀ x, Sound E B lps x x := fun _ _ _ he ht => ⟨_, he, ht⟩
  refine ⟨fun he ht => special_congr hE hB rfl he ht (fun hsat => satTr_quot_typed hsat ht)
    (.cons (srefl α) (.cons (srefl r) (.cons iha .nil))), ?_⟩
  intro c₁ us₁ bs b' hx hb _ hq _ _
  rw [mkAppN_eq_foldl, mkAppN_eq_foldl] at hx
  obtain ⟨rfl, -, -⟩ := foldl_app_const_inj hx
  rw [hB] at hb; cases hb
  exact (hq _ _ rfl).elim

/-- The case of `SrcEval.quotLift`: with `f` and `q` replaced by the translations of their values,
the quotient ι (`WHRed.quotIota_defeq`), then β. The quotient constants share one entry
(`ProgEnv.quot_head_unique`). -/
theorem case_quotLift (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv σ.decls P)
    {c c' : Name} {us us' : List Level} {qv qv' : QuotVal} {α r β f h q α' r' a b v A : Expr}
    {x : Name} {bi : BinderInfo}
    (hc : findDecl σ.decls c = some (.quotInfo qv)) (hk : qv.kind = .lift)
    (hc' : findDecl σ.decls c' = some (.quotInfo qv')) (hk' : qv'.kind = .ctor)
    (ihf : Sound E B lps f (.lam x A b bi))
    (ihq : Sound E B lps q (mkAppN (.const c' us') [α', r', a].toArray))
    (ihb : Sound E B lps (b.instantiate1' a) v) :
    Sound E B lps (mkAppN (.const c us) [α, r, β, f, h, q].toArray) v ∧
      SpineOK σ E B lps (mkAppN (.const c us) [α, r, β, f, h, q].toArray) v := by
  obtain ⟨η, hB⟩ := henv.lookup_quot (findDecl_sub hsub hc)
  obtain ⟨η', hB'⟩ := henv.lookup_quot (findDecl_sub hsub hc')
  rw [hk] at hB
  rw [hk'] at hB'
  simp only [quotKindOf] at hB hB'
  obtain rfl := henv.quot_head_unique hB hB'
  refine ⟨fun {t T} he ht => ?_, ?_⟩
  · obtain ⟨as', hlen, hargs, hsat⟩ := TrM.special_inv hB rfl he
    cases hsat with
    | quotEta _ hlt => simp [quotArity] at hlen hlt; omega
    | @quotLift _ α₀ r₀ β₀ f₀ h₀ q₀ rest _ u w hu =>
    obtain rfl : rest = [] := by simpa using hlen
    have hf₀ : TrM E B lps .nil [] f f₀ := hargs 3 f f₀ rfl rfl
    have hq₀ : TrM E B lps .nil [] q q₀ := hargs 5 q q₀ rfl rfl
    have ht' : E[.nil] ⊢ Metalean.Expr.quotLift η u w α₀ r₀ β₀ f₀ h₀ q₀ : T := ht
    obtain ⟨_, _, _, _, _, _, -, -, -, hf, -, hq, -⟩ := ht'.quotLift_prem
    obtain ⟨tl, htl, hdl⟩ := ihf hf₀ hf.right
    obtain ⟨tq, htq, hdq⟩ := ihq hq₀ hq.right
    obtain ⟨bs', hlen', hargs', hsat'⟩ := TrM.special_inv hB' rfl htq
    cases hsat' with
    | quotEta _ hlt => simp [quotArity] at hlen' hlt; omega
    | @quotMk _ α₁ r₁ a₀ rest' _ u' hu' =>
    obtain rfl : rest' = [] := by simpa using hlen'
    have ha₀ : TrM E B lps .nil [] a a₀ := hargs' 2 a a₀ rfl rfl
    have h1 : E[.nil] ⊢ Metalean.Expr.quotLift η u w α₀ r₀ β₀ f₀ h₀ q₀ ≡
        .quotLift η u w α₀ r₀ β₀ tl h₀ (.quotMk η u' α₁ r₁ a₀) : T :=
      DCong.defeq hE not_false (.quotLift .refl .refl .refl (.leaf hdl) .refl (.leaf hdq)) nil_ok
        (DCong.CtxConv.refl nil_ok) ht'
    have h2 := WHRed.quotIota_defeq hE nil_ok h1.right
    obtain ⟨A₀, b₀, rfl, hb₀⟩ := CasesWhred.trM_lam_inv htl
    have h3 := WHRed.beta_defeq hE nil_ok h2.right
    obtain ⟨X, Y, hl, hta', -⟩ := h2.right.app_inv
    obtain ⟨T₀, hb₀T, hπ⟩ := hl.lam_inv nil_ok
    have htaA : E[.nil] ⊢ a₀ : A₀ := (TypeEq.forallE_inj hE nil_ok hπ).1.conv hta'
    obtain ⟨tb, htb, hdb⟩ := TrM.inst hE nil_ok henv.metaOrderOK hb₀ ha₀ htaA hb₀T
    obtain ⟨t', ht'', hd'⟩ := ihb htb hdb.left
    exact ⟨t', ht'', dtrans hE (dtrans hE (dtrans hE (dtrans hE h1 h2) h3) hdb.symm) hd'⟩
  · intro c₁ us₁ bs b' hx hb _ hq _
    rw [mkAppN_eq_foldl, mkAppN_eq_foldl] at hx
    obtain ⟨rfl, -, -⟩ := foldl_app_const_inj hx
    rw [hB] at hb; cases hb
    exact (hq _ _ rfl).elim

/-- A quotient image with fewer arguments than the arity is the quotient's η-term. -/
theorem satTr_quotEta_inv {η : Metalean.Head ζ .quot} {k : Metalean.Export.QuotKind}
    {lps' : List Name} {n : Nat} {us : List Level} {args : List (Metalean.Expr ζ lps'.length n)}
    {t : Metalean.Expr ζ lps'.length n} (h : SatTr E lps' (.quot η k) us args t)
    (hlt : args.length < quotArity k) :
    ∃ ls t₀, us.mapM (TrLevel lps') = some ls ∧
      Metalean.Frontend.quotTerm η (E.get η).eqHead k ls = .ok t₀ ∧
      t = t₀.wkClosed.appList args := by
  cases h with
  | quotEta hu _ ht => exact ⟨_, _, hu, ht, rfl⟩
  | quotType | quotMk | quotLift | quotInd => simp [quotArity] at hlt; omega

/-- Two successful `quotTerm`s at one kind have level lists of one length. -/
theorem quotTerm_length {ℓ ℓ' : Nat} {η : Metalean.Head ζ .quot}
    {eqHead : Metalean.Head ζ (.inductive Metalean.Eq.sig)} {k : Metalean.Export.QuotKind}
    {ls : List (Metalean.Level ℓ)} {ls' : List (Metalean.Level ℓ')} {t : Metalean.Expr ζ ℓ 0}
    {t' : Metalean.Expr ζ ℓ' 0} (h : Metalean.Frontend.quotTerm η eqHead k ls = .ok t)
    (h' : Metalean.Frontend.quotTerm η eqHead k ls' = .ok t') : ls.length = ls'.length := by
  rcases ls with _ | ⟨u, _ | ⟨v, _ | ⟨w, ls⟩⟩⟩ <;>
    rcases ls' with _ | ⟨u', _ | ⟨v', _ | ⟨w', ls'⟩⟩⟩ <;> cases k <;>
    first | rfl | (cases h; done) | (cases h'; done)

/-- The η-rule on a `Quot.mk` or `Quot.lift` spine with missing arguments, as `eta_ctor`: the
translation is the quotient's η-term applied to the arguments. Reference: DV-23, DV-29. -/
theorem eta_quot (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv σ.decls P)
    {c : Name} {us : List Level} {as : List Expr} {e' : Expr} {qv : QuotVal}
    (hc : findDecl σ.decls c = some (.quotInfo qv)) (he : σ.etaSpine? c us as = some e') :
    Sound E B lps (mkAppN (.const c us) as.toArray) e' := by
  intro t T htr ht
  have hcP := findDecl_sub hsub hc
  have hname : qv.name = c := (findDecl_eq_some hcP).2
  have hnd : qv.levelParams.Nodup := henv.levelParams_nodup (findDecl_eq_some hcP).1
  obtain ⟨η, hB⟩ := henv.lookup_quot hcP
  have har : specialArity σ c = quotEvalArity qv.kind := by simp [specialArity, hc]
  unfold EvalEnv.etaSpine? at he
  rw [hc, har] at he
  cases hk : quotEvalArity qv.kind with
  | none => rw [hk] at he; cases he
  | some ar =>
  rw [hk] at he
  simp only at he
  split at he
  · rename_i hlt
    obtain ⟨ty, hpi, hl⟩ := Option.bind_eq_some_iff.1 he
    have hkar : quotArity (quotKindOf qv.kind) = ar := by
      cases hq : qv.kind <;> rw [hq] at hk <;> simp [quotEvalArity] at hk <;> subst hk <;> rfl
    obtain ⟨as', hlen, hargs, hsat⟩ := TrM.special_inv hB rfl htr
    obtain ⟨ls, t₀, hls, hqt, rfl⟩ := satTr_quotEta_inv hsat (by omega)
    obtain ⟨-, -, Tc, tc, hTc, htc, htcT⟩ := henv.lookup hE hcP
    have htc' : TrM E B qv.levelParams .nil [] (mkAppN (.const c (qv.levelParams.map .param))
        ([] : List Expr).toArray) tc := by rw [← hname]; exact htc
    obtain ⟨as₁, hlen₁, -, hsat₁⟩ := TrM.special_inv hB rfl htc'
    obtain rfl : as₁ = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen₁.symm)
    obtain ⟨ls₁, t₁, hls₁, hqt₁, htc₁⟩ := satTr_quotEta_inv hsat₁ (by simp; omega)
    have htc₁' : tc = t₁ := htc₁
    subst htc₁'
    -- the levels: the constant's own parameters, instantiated at `us`
    have hl₁ : ls₁.length = qv.levelParams.length := by
      simpa using (mapM_option_get hls₁).1
    have hlL : ls.length = us.length := (mapM_option_get hls).1
    have hlen₀ : us.length = qv.levelParams.length := by
      rw [← hlL, ← hl₁]; exact quotTerm_length hqt hqt₁
    let ls' : Fin qv.levelParams.length → Metalean.Level lps.length :=
      fun i => ls[i.val]'(by omega)
    have hus : TrLevels lps us qv.levelParams.length = some ls' := by
      simp only [TrLevels, bind, Option.bind_eq_some_iff]
      exact ⟨ls, hls, by rw [dif_pos (by omega)]⟩
    have hps : TrLevels qv.levelParams (qv.levelParams.map .param) qv.levelParams.length =
        some fun i => ls₁[i.val]'(by omega) := by
      simp only [TrLevels, bind, Option.bind_eq_some_iff]
      exact ⟨ls₁, hls₁, by rw [dif_pos hl₁]⟩
    obtain ⟨hk0, hps'⟩ := trLevels_params_nodup hnd hps
    have hmap : ls₁.map (·{ls'}) = ls := by
      refine List.ext_getElem (by simp; omega) fun i h₁ h₂ => ?_
      simp only [List.getElem_map]
      have := hps' ⟨i, by simp at h₁; omega⟩
      simp only at this
      rw [this]
      rfl
    have hqt' := quotTerm_instL η _ _ ls₁ ls' hqt₁
    rw [hmap, hqt] at hqt'
    injection hqt' with h0
    subst h0
    have hTc' := TrM.instLevels hus hTc
    have htcT' := Metalean.Defeq.instLevel (ℓ := qv.levelParams.length) ls' htcT
    obtain ⟨_, hreg⟩ := htcT'.regular
    obtain ⟨Y, hY, hTY⟩ := piInst_tr hE henv.metaOrderOK as hTc' htcT'
      (Metalean.IsType.typeEq ⟨_, hreg⟩) (CasesWhred.forall₂_of_getElem? hlen hargs) ht hpi
    exact eta_lams hE henv.metaOrderOK (.const c us) rfl _ nil_ok htr ht hY hTY hl
  · cases he

/-! ## Recursors -/

/-- The η-rule on a recursor spine with missing arguments, as `eta_quot`: the translation is the
recursor's η-term applied to the arguments, which is the image of the recursor at its own universe
parameters, instantiated at the spine's. Reference: DV-23, DV-30. -/
theorem eta_recr (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv σ.decls P)
    {c : Name} {us : List Level} {as : List Expr} {e' : Expr} {rv : RecursorVal}
    (hc : findDecl σ.decls c = some (.recInfo rv)) (he : σ.etaSpine? c us as = some e') :
    Sound E B lps (mkAppN (.const c us) as.toArray) e' := by
  intro t T htr ht
  have hcP := findDecl_sub hsub hc
  have hname : rv.name = c := (findDecl_eq_some hcP).2
  have hnd : rv.levelParams.Nodup := henv.levelParams_nodup (findDecl_eq_some hcP).1
  obtain ⟨ι, η, s, os, hB, har⟩ := henv.lookup_recr hcP
  have hsa : specialArity σ c = some (ι.recrEnd s) := by simp [specialArity, hc, har]
  unfold EvalEnv.etaSpine? at he
  rw [hc, hsa] at he
  simp only at he
  split at he
  · rename_i hlt
    obtain ⟨ty, hpi, hl⟩ := Option.bind_eq_some_iff.1 he
    obtain ⟨as', hlen, hargs, hsat⟩ := TrM.special_inv hB rfl htr
    obtain ⟨l, us', ls, mo, t₀, hRL, hls, hmo, hrt, rfl⟩ := satTr_recrEta_inv hsat (by omega)
    obtain ⟨-, -, Tc, tc, hTc, htc, htcT⟩ := henv.lookup hE hcP
    have htc' : TrM E B rv.levelParams .nil [] (mkAppN (.const c (rv.levelParams.map .param))
        ([] : List Expr).toArray) tc := by rw [← hname]; exact htc
    obtain ⟨as₁, hlen₁, -, hsat₁⟩ := TrM.special_inv hB rfl htc'
    obtain rfl : as₁ = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen₁.symm)
    obtain ⟨l₁, us₁, ls₁, -, -, hRL₁, hls₁, -, -, -⟩ :=
      satTr_recrEta_inv hsat₁ (by simp [Metalean.IndSig.recrEnd])
    obtain ⟨ls', hus⟩ := recr_spine_levels hRL hls hRL₁ hls₁
    -- the image of the recursor at its own parameters, instantiated at the spine's levels
    have hinst := TrM.instLevels hus htc'
    have hconst : Pure.instLevels rv.levelParams us
        (mkAppN (.const c (rv.levelParams.map .param)) ([] : List Expr).toArray) =
        mkAppN (.const c us) ([] : List Expr).toArray := by
      show Expr.const c _ = Expr.const c us
      rw [params_instLevel hnd (TrLevels_get hus).1]
    rw [hconst] at hinst
    obtain ⟨as₂, hlen₂, -, hsat₂⟩ := TrM.special_inv hB rfl hinst
    obtain rfl : as₂ = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen₂.symm)
    obtain ⟨l₂, us₂, ls₂, mo₂, t₂, hRL₂, hls₂, hmo₂, hrt₂, htc₂⟩ :=
      satTr_recrEta_inv hsat₂ (by simp [Metalean.IndSig.recrEnd])
    obtain ⟨rfl, rfl⟩ := TrDet.RecrLevels.det hRL hRL₂
    obtain rfl := TrDet.TrLevels.det hls hls₂
    obtain rfl : mo = mo₂ := funext fun t => funext fun c =>
      Option.some.inj ((hmo t c).symm.trans (hmo₂ t c))
    rw [hrt] at hrt₂
    injection hrt₂ with h0
    subst h0
    have hTc' := TrM.instLevels hus hTc
    have htcT' := Metalean.Defeq.instLevel (ℓ := rv.levelParams.length) ls' htcT
    rw [htc₂] at htcT'
    obtain ⟨_, hreg⟩ := htcT'.regular
    obtain ⟨Y, hY, hTY⟩ := piInst_tr hE henv.metaOrderOK as hTc' htcT'
      (Metalean.IsType.typeEq ⟨_, hreg⟩) (CasesWhred.forall₂_of_getElem? hlen hargs) ht hpi
    exact eta_lams hE henv.metaOrderOK (.const c us) rfl _ nil_ok htr ht hY hTY hl
  · cases he

/-- An η-expanded head has an arity. -/
theorem etaSpine?_special {c : Name} {us : List Level} {as : List Expr} {e' : Expr}
    (he : σ.etaSpine? c us as = some e') : ∃ ar, specialArity σ c = some ar := by
  unfold EvalEnv.etaSpine? at he
  split at he
  · exact ⟨_, ‹_›⟩
  · cases he

/-- The case of `SrcEval.recIota`: with the minors and the major replaced by the translations of
their values (`special_congr`; the minors are not wrapped, since the recursive fields come last,
`RecWhred.orders_identity`), ι and β (`RecWhred.recIota_whred`). -/
theorem case_recIota (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv σ.decls P)
    {c : Name} {rv : RecursorVal} {T : Name} {iv : InductiveVal} {cvs : List ConstructorVal}
    {motives : List (List Name)} {minors : List RecMinor} {maj mj : Expr} {k : Nat}
    {mi : RecMinor} {mk : Expr} {us : List Level} {v : Expr} {ps ms mins mvs fs rfs : List Expr}
    (hcr : findDecl σ.decls c = some (.recInfo rv)) (hall : rv.all = [T]) (hcT : c = mkRecName T)
    (hblk : σ.recBlock? rv = some ([iv], cvs)) (hni : rv.numIndices = 0)
    (hshape : recShape rv.numParams rv.numMotives rv.type (cvs.map (·.numFields)) =
      some (motives, minors))
    (hihs : ∀ mi ∈ minors, mi.ihs.map (fun h => (h.field, h.binders)) =
      (List.range' (mi.fields.length - mi.ihs.length) mi.ihs.length).map fun f => (f, []))
    (hps : ps.length = rv.numParams) (hms : ms.length = rv.numMotives)
    (hmins : mins.length = rv.numMinors) (hlm : mins.length = mvs.length)
    (ihmin : ∀ (i : Nat) m mv, mins[i]? = some m → mvs[i]? = some mv → Sound E B lps m mv)
    (ihmaj : Sound E B lps maj mj) (hcv : CtorValue σ T mj k fs) (hmi : minors[k]? = some mi)
    (hmk : mvs[k]? = some mk) (hrfs : (mi.ihs.mapM fun h => fs[h.field]?) = some rfs)
    {ihvs : List Expr} (hrl : rfs.length = ihvs.length)
    (ihih : ∀ (i : Nat) f w, rfs[i]? = some f → ihvs[i]? = some w →
      Sound E B lps (mkAppN (.const c us) (ps ++ ms ++ mvs ++ [f]).toArray) w)
    (ihb : Sound E B lps (mkAppN mk (fs ++ ihvs).toArray) v) :
    Sound E B lps (mkAppN (.const c us) (ps ++ ms ++ mins ++ [maj]).toArray) v ∧
      SpineOK σ E B lps (mkAppN (.const c us) (ps ++ ms ++ mins ++ [maj]).toArray) v := by
  obtain ⟨ι, η, s, lps₀, Is, Cs, Rs, orders, hb, rfl, rfl, -, -, hBc, hns, rfl⟩ :=
    RecWhred.rec_block henv hsub hcr hall hcT hblk
  obtain ⟨⟨_, _, _, _, hIB⟩, -⟩ := hb
  refine ⟨fun {t T} he ht => ?_, ?_⟩
  · have srefl : ∀ x, Sound E B lps x x := fun _ _ _ he ht => ⟨_, he, ht⟩
    have hself : ∀ l : List Expr, List.Forall₂ (Sound E B lps) l l := fun l =>
      List.forall₂_same.2 fun x _ => srefl x
    have hall' : List.Forall₂ (Sound E B lps) (ps ++ ms ++ mins ++ [maj])
        (ps ++ ms ++ mvs ++ [mj]) :=
      List.rel_append (List.rel_append (List.rel_append (hself ps) (hself ms))
        (CasesWhred.forall₂_of_getElem? hlm ihmin)) (.cons ihmaj .nil)
    have hid : ∀ (t : Fin ι.nsorts) (c : Fin (ι.nctors t)) mo,
        ((List.ofFn fun t => List.ofFn fun c => orders t c)[t.val]?.bind (·[c.val]?)) = some mo →
        mo = List.range ((ι.ctors t c).nfields + (ι.ctors t c).nrecFields) := by
      intro t c mo h
      simp only [List.getElem?_ofFn, t.isLt, c.isLt, ↓reduceDIte, Option.bind_some,
        Option.some.injEq] at h
      subst h
      obtain rfl : s = t := Fin.ext (by have := t.isLt; have := s.isLt; omega)
      exact RecWhred.orders_identity hIB s hns hshape hihs c
    obtain ⟨t₂, ht₂, hd₂⟩ := special_congr hE hBc rfl he ht
      (fun hsat => RecWhred.satTr_recr_typed hE nil_ok hsat ht hid) hall'
    obtain ⟨a₁, fs₀, ihs₀, ha₁, hfs₀, hihs₀, hred⟩ := RecWhred.recIota_whred henv hsub hcr hall
      hcT hblk hni hshape hihs hps hms (hlm ▸ hmins) hcv hmi hmk hrfs ht₂
    have hd₃ := WHRedS.defeq hE nil_ok hred hd₂.right
    -- the induction hypotheses replaced by their values
    obtain ⟨-, htyped⟩ := InstPre.appList_inv hd₃.right
    have hS : List.Forall₂ (Sound E B lps)
        (rfs.map fun f => mkAppN (.const c us) (ps ++ ms ++ mvs ++ [f]).toArray) ihvs :=
      CasesWhred.forall₂_of_getElem? (by simp [hrl]) fun i x y h1 h2 => by
        rw [List.getElem?_map] at h1
        obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.1 h1
        exact ihih i f y hf h2
    obtain ⟨ihv₀, hihv₀, hds⟩ :=
      args_congr hS hihs₀ fun a ha => htyped a (List.mem_append_right _ ha)
    have hcong : List.Forall₂ (DCong E False .nil .nil) (fs₀ ++ ihs₀) (fs₀ ++ ihv₀) :=
      List.rel_append (List.forall₂_same.mpr fun x _ => DCong.refl)
        (List.Forall₂.imp (fun _ _ ⟨_, hA⟩ => DCong.leaf hA) hds)
    have h1 := DCong.defeq hE not_false
      (TrDet.appList .refl hcong.length_eq (forall₂_getElem? hcong)) nil_ok
      (DCong.CtxConv.refl nil_ok) hd₃.right
    obtain ⟨t₄, ht₄, hred₄⟩ := TrM.apps ha₁ (List.rel_append hfs₀ hihv₀)
    have hd₄ := WHRedS.defeq hE nil_ok hred₄ h1.right
    obtain ⟨t', ht', hd'⟩ := ihb ht₄ hd₄.right
    exact ⟨t', ht', dtrans hE (dtrans hE (dtrans hE (dtrans hE hd₂ hd₃) h1) hd₄) hd'⟩
  · intro c' us' bs b h hb hs _ hr _
    rw [mkAppN_eq_foldl, mkAppN_eq_foldl] at h
    obtain ⟨rfl, -, -⟩ := foldl_app_const_inj h
    rw [hBc] at hb; cases hb
    exact (hr _ _ _ _ rfl).elim

/-- The remaining obligation of `SrcEval.casesProof`, given the conclusions for its two
evaluations: the major is identified with the constructor by proof irrelevance, then ι. -/
def ProofSound (σ : EvalEnv) (E : Metalean.Env ζ) (B : Binds ζ) (lps : List Name) : Prop :=
  ∀ {c : Name} {us vs : List Level} {iv : InductiveVal} {as ps : List Expr}
    {m mv st alt v : Expr} {l : Level} {cn : Name} {cv : ConstructorVal},
    σ.casesOn? c = some iv → as.length = casesArity iv → as[casesMajor iv]? = some m →
    AtomSpine σ mv → casesSortLevel iv us = some l → EvidentZero l = true → iv.ctors = [cn] →
    findDecl σ.decls cn = some (.ctorInfo cv) → cv.numFields = 0 → σ.spineType? mv = some st →
    ps.length = cv.numParams → piInst ps (Pure.instLevels cv.levelParams vs cv.type) = some st →
    as[casesMajor iv + 1]? = some alt → Sound E B lps m mv → Sound E B lps alt v →
    Sound E B lps (mkAppN (.const c us) as.toArray) v

/-- Subject reduction with the argument-wise evaluation of saturating spines, by induction on
`SrcEval`, given the proof-irrelevant ι (`SrcDefeq.ProofSound`). -/
theorem sound_of (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv σ.decls P)
    (hproof : ProofSound σ E B lps)
    {e v : Expr} (hev : SrcEval σ e v) : Sound E B lps e v ∧ SpineOK σ E B lps e v := by
  induction hev with
  | beta hns hf _ _ ihf iha ihb => exact case_beta henv hE hsub hns hf ihf iha.1 ihb.1
  | zeta _ _ ihv ihb => exact case_zeta henv hE ihv.1 ihb.1
  | delta hu _ ih => exact case_delta henv hE hsub hu ih.1
  | constAtom ha => exact case_constAtom henv hsub ha
  | eta he =>
    refine ⟨?_, spineOK_eta henv hsub he⟩
    obtain ⟨ar, har⟩ := etaSpine?_special he
    rcases specialArity_some har with ⟨cv, hcv, -⟩ | ⟨iv, hiv⟩ | ⟨qv, hqv, -⟩ | ⟨rv, hrv, -⟩
    · exact eta_ctor henv hE hsub hcv
        (henv.levelParams_nodup (findDecl_eq_some (findDecl_sub hsub hcv)).1) he
    · exact eta_casesOn henv hE hsub hiv he
    · exact eta_quot henv hE hsub hqv he
    · exact eta_recr henv hE hsub hrv he
  | ctor hc _ hlen' _ ih =>
    exact case_ctor henv hE hsub hc hlen' fun i a v h₁ h₂ => (ih i a v h₁ h₂).1
  | casesIota hcs hlen hm _ hcv halt _ ihm ihb =>
    exact case_casesIota henv hE hsub hcs hlen hm hcv halt ihm.1 ihb.1
  | casesLitZero hcs hnat hlen hm _ halt _ ihm ihb =>
    exact case_casesLit (k := 0) henv hE hsub hcs hnat hlen hm (by simpa using halt) ihm.1 ihb.1
  | casesLitSucc hcs hnat hlen hm _ halt _ ihm ihb =>
    exact case_casesLit henv hE hsub hcs hnat hlen hm (by simpa using halt) ihm.1
      (by simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]; exact ihb.1)
  | casesProof hcs hlen hm _ hsp hl hz hcn hcv hnf hst hps hpi halt _ ihm ihb =>
    obtain ⟨d, hd⟩ := casesOn?_defn hcs
    exact ⟨hproof hcs hlen hm hsp hl hz hcn hcv hnf hst hps hpi halt ihm.1 ihb.1,
      spineOK_defn henv hsub hd⟩
  | quotMk hc hk _ ih => exact case_quotMk henv hE hsub hc hk ih.1
  | quotLift hc hk _ _ hc' hk' _ ihf ihq ihb =>
    exact case_quotLift henv hE hsub hc hk hc' hk' ihf.1 ihq.1 ihb.1
  | recIota hcr hall hcT hblk hni hshape hihs hps hms hmins hlm _ _ hcv hmi hmk hrfs hrl _ _ ihmin
      ihmaj ihih ihb =>
    exact case_recIota henv hE hsub hcr hall hcT hblk hni hshape hihs hps hms hmins hlm
      (fun i m mv h1 h2 => (ihmin i m mv h1 h2).1) ihmaj.1 hcv hmi hmk hrfs hrl
      (fun i f w h1 h2 => (ihih i f w h1 h2).1) ihb.1
  | proj _ hcv ha ih => exact case_proj henv hE hsub hcv ha ih.1
  | projProp _ _ _ ih => exact case_projProp henv hE ih.1
  | lit => exact case_refl fun _ _ h => by cases h
  | appCong hns hf hnb _ ihf iha => exact case_appCong henv hE hsub hns hf hnb ihf iha.1
  | mdata _ ih => exact case_mdata ih.1
  | atom h =>
    rename_i e
    cases e <;> simp only [SrcAtom] at h <;> exact case_refl fun _ _ h => by cases h

end SrcDefeq

end EraseProof
