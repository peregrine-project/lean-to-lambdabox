import EraseProof.Simulation.Cases
import EraseProof.Relation.Lookup
import EraseProof.Source.Restrict

/-!
# Constructor, `casesOn`, projection and literal cases of the relation-level simulation

The cases of `erases_correct` (`MR E/ErasureCorrectness.v:51`) for the rules `ctor`, `casesIota`,
`casesFrozen`, `casesLitZero`, `casesLitSucc`, `proj`, `projFrozen` and `lit` of `SrcEval`, each a
theorem whose premises are premises of the rule and the induction hypotheses `ErasesSim` of its
evaluation premises, as in `Simulation/Cases.lean`. Adapted from `ML-V Simulation/Ind.lean` and
`ML-V Simulation/Iota.lean`.

Every alternative of a `casesOn` is a λ, plain or `eta`-marked, under its field binders
(`ErasesAlt`), so the erasure of the alternative applied to the fields is λ□ λs applied to the
erased fields, which evaluates as λ□'s ι-reduct (`SimCases.eval_lams`, on fields that are closed
λ□ values): the source's alternative applied to the fields is related directly. A constructor
value meets its λ□ `case` at the constructor's position with the constructor's parameter count
only if the environment lists every constructor at its index (`CtorsListed`), and the λ□
literals are constructor values only of a `Nat` of Lean's shape (`NatShaped`). An under-applied
constructor spine has no erasure (`Erases.ctor` asks for its arity) and no evaluation: the marks
η-expand it, and its η-expansion is an `eta`-marked λ (`SimCases.erases_correct_etaLam`).
-/

open Lean Erasure

namespace EraseProof

/-! ## Environment conditions -/

/-- Every constructor of `decls` is listed by its inductive at its index `cidx`, with the
inductive's parameter count, as Lean's kernel generates the records. con-leche's frontend checks
these fields (`CL ConLeche/Frontend/ExportC.lean:241 validateIndF`), and so does `DeclsOf?`
(`blockShapeOK`, `declOf?`; DV-3). Reference: `declared_constructor`
(`MR common/theories/EnvironmentTyping.v:36`). -/
def CtorsListed (decls : List ConstantInfo) : Prop :=
  ∀ c cv, findDecl decls c = some (.ctorInfo cv) → ∃ iv,
    findDecl decls cv.induct = some (.inductInfo iv) ∧ iv.ctors[cv.cidx]? = some c ∧
    iv.numParams = cv.numParams

/-- The inductive `Nat` of `σ`, if there is one, has Lean's shape: no parameters, not declared in
`Prop`, and the constructors `zero`, without a field, and `succ`, with one, in that order: the
λ□ constructors `0` and `1` of the Peano numerals (`Erases.litZero`, `Erases.litSucc`) are its.
con-leche checks a program's `Nat` against this shape (`CL ConLeche/Kernel/Basis/Nat.lean:68
natBasis`). Reference: none (λ□ has no Nat literals; DV-27). -/
def NatShaped (σ : EvalEnv) : Prop :=
  ∀ iv, findDecl σ.decls ``Nat = some (.inductInfo iv) → iv.numParams = 0 ∧
    σ.propInd ``Nat = false ∧
    ∃ z s, iv.ctors = [z, s] ∧ ctorFields σ z = some 0 ∧ ctorFields σ s = some 1

/-! ## λ□ evaluation

Copied from `ML-V TargetFacts.lean:263-354` (closed substitutions commute),
`ML-V Simulation/RecEval.lean:35-141` (evaluation results evaluate to themselves only),
`ML-V Simulation/Iota.lean:799-821` (the head of an application) and
`ML-V Simulation/Ind.lean:260-303, 519-587` (constructor spines), with the list lemmas of
`Relation/Basic.lean` in place of their `SimCases` copies. -/

/-- Induction on a list from its last element (`List.reverseRecOn` of Batteries, which this
package does not depend on). -/
theorem snocInduction {α : Type} {motive : List α → Prop} (nil : motive [])
    (append_singleton : ∀ (l : List α) (a : α), motive l → motive (l ++ [a])) (l : List α) :
    motive l := by
  rw [← List.reverse_reverse l]
  induction l.reverse with
  | nil => exact nil
  | cons a l ih => rw [List.reverse_cons]; exact append_singleton _ a ih

namespace TargetSubst

mutual
/-- Closed substitutions at two indices commute. -/
theorem csubst_comm {f g : LBTerm} (hf : closedn 0 f = true) (hg : closedn 0 g = true) :
    ∀ (t : LBTerm) (j n : Nat), j ≤ n →
      csubst f n (csubst g j t) = csubst g j (csubst f (n + 1) t)
  | .box, _, _, _ => rfl
  | .bvar m, j, n, h => by
    have cf : ∀ i, csubst g i f = f := fun i => csubst_closedn g f 0 i hf (Nat.zero_le _)
    have cg : ∀ i, csubst f i g = g := fun i => csubst_closedn f g 0 i hg (Nat.zero_le _)
    simp only [csubst]
    rcases Nat.lt_trichotomy j m with h1 | rfl | h1
    · rcases Nat.lt_trichotomy (n + 1) m with h2 | rfl | h2
      · rw [ite_eq_right (by omega), ite_eq_left h1, ite_eq_right (by omega), ite_eq_left h2]
        simp only [csubst]
        rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
      · rw [ite_eq_right (by omega), ite_eq_left h1, ite_eq_left rfl, cf]
        simp only [csubst]
        rw [ite_eq_left (by omega)]
      · rw [ite_eq_right (by omega), ite_eq_left h1, ite_eq_right (by omega), ite_eq_right (by omega)]
        simp only [csubst]
        rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h1]
    · rw [ite_eq_left rfl, cg, ite_eq_right (by omega), ite_eq_right (by omega)]
      simp [csubst]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      simp only [csubst]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  | .fvar _, _, _, _ => rfl
  | .lambda na b, j, n, h => by
    simp only [csubst, csubst_comm hf hg b (j + 1) (n + 1) (by omega)]
  | .letIn na b b', j, n, h => by
    simp only [csubst, csubst_comm hf hg b j n h, csubst_comm hf hg b' (j + 1) (n + 1) (by omega)]
  | .app u v, j, n, h => by
    simp only [csubst, csubst_comm hf hg u j n h, csubst_comm hf hg v j n h]
  | .const _, _, _, _ => rfl
  | .construct i c args, j, n, h => by
    simp only [csubst, csubstL_comm hf hg args j n h]
  | .case ip c brs, j, n, h => by
    simp only [csubst, csubst_comm hf hg c j n h, csubstB_comm hf hg brs j n h]
  | .proj p c, j, n, h => by
    simp only [csubst, csubst_comm hf hg c j n h]
  | .fix defs i, j, n, h => by
    simp only [csubst, length_csubstD]
    rw [csubstD_comm hf hg defs (j + defs.length) (n + defs.length) (by omega),
      show n + defs.length + 1 = n + 1 + defs.length by omega]
  | .prim _, _, _, _ => rfl
theorem csubstL_comm {f g : LBTerm} (hf : closedn 0 f = true) (hg : closedn 0 g = true) :
    ∀ (as : List LBTerm) (j n : Nat), j ≤ n →
      csubstL f n (csubstL g j as) = csubstL g j (csubstL f (n + 1) as)
  | [], _, _, _ => rfl
  | a :: as, j, n, h => by
    simp only [csubstL, csubst_comm hf hg a j n h, csubstL_comm hf hg as j n h]
theorem csubstB_comm {f g : LBTerm} (hf : closedn 0 f = true) (hg : closedn 0 g = true) :
    ∀ (bs : List (List BinderName × LBTerm)) (j n : Nat), j ≤ n →
      csubstB f n (csubstB g j bs) = csubstB g j (csubstB f (n + 1) bs)
  | [], _, _, _ => rfl
  | (ns, b) :: bs, j, n, h => by
    simp only [csubstB, csubstB_comm hf hg bs j n h,
      csubst_comm hf hg b (j + ns.length) (n + ns.length) (by omega),
      show n + ns.length + 1 = n + 1 + ns.length by omega]
theorem csubstD_comm {f g : LBTerm} (hf : closedn 0 f = true) (hg : closedn 0 g = true) :
    ∀ (ds : List (@FixDef LBTerm)) (j n : Nat), j ≤ n →
      csubstD f n (csubstD g j ds) = csubstD g j (csubstD f (n + 1) ds)
  | [], _, _, _ => rfl
  | ⟨nm, b, r⟩ :: ds, j, n, h => by
    simp only [csubstD, csubst_comm hf hg b j n h, csubstD_comm hf hg ds j n h]
end

/-- A closed term substituted at index `|gs|` below the closed terms `gs`. -/
theorem csubst_substl {f : LBTerm} (hf : closedn 0 f = true) :
    ∀ (gs : List LBTerm) (t : LBTerm), (∀ g ∈ gs, closedn 0 g = true) →
      csubst f 0 (substl gs t) = substl gs (csubst f gs.length t)
  | [], _, _ => rfl
  | g :: gs, t, hgs => by
    have hg := hgs g List.mem_cons_self
    have hgs' : ∀ g' ∈ gs, closedn 0 g' = true := fun g' h => hgs g' (List.mem_cons_of_mem _ h)
    show csubst f 0 (substl gs (csubst g 0 t)) = substl gs (csubst g 0 (csubst f (gs.length + 1) t))
    rw [csubst_substl hf gs _ hgs', csubst_comm hf hg t 0 gs.length (Nat.zero_le _)]

end TargetSubst

open TargetSubst

/-- The fields of `iota_red` substituted one by one: `substl` of the reversed fields substitutes the
first field at the index of the last binder, below the remaining fields, when the fields are
closed. Reference: `substl` (`MR E/ECSubst.v:46`) and `iota_red` (`MR E/EGlobalEnv.v:281`), with
`closed_subst` (`MR E/ECSubst.v`). -/
theorem substl_cons_closed {f t : LBTerm} {fs : List LBTerm} (hf : closedn 0 f = true)
    (hfs : ∀ g ∈ fs, closedn 0 g = true) :
    substl (f :: fs).reverse t = substl fs.reverse (csubst f fs.length t) := by
  rw [List.reverse_cons, substl, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [← List.length_reverse (as := fs)]
  exact csubst_substl hf fs.reverse t fun g hg => hfs g (List.mem_reverse.mp hg)

namespace RecEval

variable {lenv : GlobalDeclarations}

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
    · cases argsv using snocInduction with
      | nil => rfl
      | append_singleton l x _ => rw [mkApps_snoc]; rfl
    · cases argsv using snocInduction with
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
    · cases args using snocInduction with
      | nil => rfl
      | append_singleton l x _ => rw [mkApps_snoc]; rfl
    · cases args using snocInduction with
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

end RecEval

namespace SimCases

variable {cert : BoxCert} {σ : EvalEnv} {lenv : GlobalDeclarations}

/-- λ□ evaluation of an application depends on the head only through the head's evaluation. -/
theorem lbeval_app_congr {G H x r : LBTerm}
    (hGH : ∀ w, LBEval defaultFlags lenv G w → LBEval defaultFlags lenv H w)
    (h : LBEval defaultFlags lenv (.app G x) r) : LBEval defaultFlags lenv (.app H x) r := by
  generalize hx : LBTerm.app G x = y at h
  cases h with
  | box h1 h2 => cases hx; exact .box (hGH _ h1) h2
  | beta h1 h2 h3 => cases hx; exact .beta (hGH _ h1) h2 h3
  | fix hfl h1 h2 h3 h4 => cases hx; exact .fix hfl (hGH _ h1) h2 h3 h4
  | fixValue hfl h1 h2 h3 h4 => cases hx; exact .fixValue hfl (hGH _ h1) h2 h3 h4
  | fix' hfl h1 h2 h3 h4 => cases hx; exact .fix' hfl (hGH _ h1) h2 h3 h4
  | construct hfl hl h1 h2 h3 => cases hx; exact .construct hfl hl (hGH _ h1) h2 h3
  | appCong h1 h2 h3 => cases hx; exact .appCong (hGH _ h1) h2 h3
  | atom ha => subst hx; simp [lbAtom] at ha
  | zeta | iota | iotaBlock | iotaSing | delta | proj | projBlock | projProp | constructBlock
  | prim => cases hx

/-- `lbeval_app_congr` under further arguments. -/
theorem lbeval_mkApps_congr : ∀ (xs : List LBTerm) {G H r : LBTerm},
    (∀ w, LBEval defaultFlags lenv G w → LBEval defaultFlags lenv H w) →
    LBEval defaultFlags lenv (mkApps G xs) r → LBEval defaultFlags lenv (mkApps H xs) r
  | [], _, _, _, hGH, h => hGH _ h
  | _ :: xs, _, _, _, hGH, h => lbeval_mkApps_congr xs (fun _ hw => lbeval_app_congr hGH hw) h

/-- Pointwise related lists with one more element each: the prefixes are related, and so are the
last elements. Copy of `ML-V Simulation/Cases.lean:51`. -/
theorem forall_snoc {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β} {x : α} {y : β}
    (hlen : l.length = l'.length)
    (h : ∀ (i : Nat) a b, (l ++ [x])[i]? = some a → (l' ++ [y])[i]? = some b → R a b) :
    (∀ (i : Nat) a b, l[i]? = some a → l'[i]? = some b → R a b) ∧ R x y := by
  refine ⟨fun i a b ha hb => h i a b ?_ ?_, h l.length x y (by simp) (by simp [hlen])⟩
  · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp ha).1]; exact ha
  · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hb).1]; exact hb

/-- λ□ evaluates a constructor applied to arguments that evaluate, one by one, up to the
constructor's arity (`eval_construct`). -/
theorem lbeval_construct {lenv : GlobalDeclarations} {iid : InductiveId} {c : Nat}
    {mib : MutualInductiveBody} {ob : OneInductiveBody} {cb : ConstructorBody}
    (hlk : lookupCtor lenv iid c = some (mib, ob, cb)) :
    ∀ (as vs : List LBTerm), as.length = vs.length → as.length ≤ mib.npars + cb.nargs →
      (∀ (i : Nat) a v, as[i]? = some a → vs[i]? = some v → LBEval defaultFlags lenv a v) →
      LBEval defaultFlags lenv (mkApps (.construct iid c []) as) (mkApps (.construct iid c []) vs) := by
  intro as
  induction as using snocInduction with
  | nil =>
    intro vs hl _ _
    obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero hl.symm
    exact .atom (by simp [mkApps, lbAtom, defaultFlags, hlk])
  | append_singleton as a ih =>
    intro vs hl hle hall
    obtain ⟨vs, v, rfl⟩ : ∃ vs' v, vs = vs' ++ [v] := by
      rcases eq_nil_or_snoc vs with rfl | h
      · simp at hl
      · exact h
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hl
    obtain ⟨hall', hav⟩ := forall_snoc hl hall
    rw [mkApps_snoc, mkApps_snoc]
    simp only [List.length_append, List.length_singleton] at hle
    exact .construct rfl hlk (ih vs hl (by omega) hall') (by omega) hav

/-- A choice of one witness per position. -/
theorem choose_list {γ : Type} {n : Nat} {R : Nat → γ → Prop} (h : ∀ i, i < n → ∃ y, R i y) :
    ∃ ys : List γ, ys.length = n ∧ ∀ (i : Nat) y, ys[i]? = some y → R i y := by
  refine ⟨List.ofFn fun i : Fin n => Classical.choose (h i i.2), by simp, fun i y hy => ?_⟩
  rw [List.getElem?_ofFn] at hy
  split at hy
  · rename_i hi
    cases hy
    exact Classical.choose_spec (h i hi)
  · cases hy

/-- A λ□ constructor spine is not `□`. -/
theorem mkApps_construct_ne_box {iid : InductiveId} {c : Nat} {as : List LBTerm} :
    mkApps (.construct iid c []) as ≠ .box := by
  intro h
  have := congrArg headOf h
  rw [headOf_mkApps] at this
  cases this

/-- A λ□ constructor spine ending in an argument. -/
theorem mkApps_construct_app {ind : InductiveId} {c : Nat} {args : List LBTerm} {f a : LBTerm}
    (h : mkApps (.construct ind c []) args = .app f a) :
    ∃ init, args = init ++ [a] ∧ f = mkApps (.construct ind c []) init := by
  rcases eq_nil_or_snoc args with rfl | ⟨init, y, rfl⟩
  · cases h
  · rw [mkApps_snoc] at h
    cases h
    exact ⟨init, rfl, rfl⟩

/-- λ□ constructor spines are injective. -/
theorem mkApps_construct_inj {ind ind' : InductiveId} {c c' : Nat} :
    ∀ {args args' : List LBTerm},
      mkApps (.construct ind c []) args = mkApps (.construct ind' c' []) args' → args = args' := by
  intro args
  induction args using snocInduction with
  | nil =>
    intro args' h
    rcases eq_nil_or_snoc args' with rfl | ⟨init, y, rfl⟩
    · rfl
    · rw [mkApps_snoc] at h; cases h
  | append_singleton init y ih =>
    intro args' h
    rw [mkApps_snoc] at h
    obtain ⟨init', rfl, hf⟩ := mkApps_construct_app h.symm
    rw [ih hf]

/-- The arguments of a λ□ constructor spine that is an evaluation result evaluate to themselves. -/
theorem construct_args {lenv : GlobalDeclarations} {s t : LBTerm}
    (h : LBEval defaultFlags lenv s t) : ∀ (ind : InductiveId) (c : Nat) (args : List LBTerm),
      t = mkApps (.construct ind c []) args → ∀ a ∈ args, LBEval defaultFlags lenv a a := by
  induction h using LBEval.ind with
  | box =>
    intro ind c args h
    exact absurd h.symm mkApps_construct_ne_box
  | beta _ _ _ _ _ ih | zeta _ _ _ ih | iota _ _ _ _ _ _ _ _ ih | iotaBlock _ _ _ _ _ _ _ _ ih
  | iotaSing _ _ _ _ _ _ ih | fix _ _ _ _ _ _ _ ih | fix' _ _ _ _ _ _ _ ih | delta _ _ _ ih
  | proj _ _ _ _ _ _ _ ih | projBlock _ _ _ _ _ _ _ ih => exact ih
  | projProp =>
    intro ind c args h
    exact absurd h.symm mkApps_construct_ne_box
  | fixValue =>
    intro ind c args h
    have := congrArg headOf h
    simp only [headOf, headOf_mkApps] at this
    cases this
  | construct _ _ h₃ _ h₅ ih₃ _ =>
    intro ind c args h
    obtain ⟨init, rfl, hf⟩ := mkApps_construct_app h.symm
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact ih₃ _ _ init (by rw [mkApps_construct_inj hf]) a ha
    · rw [List.mem_singleton.mp ha]; exact LBEval.idem h₅
  | constructBlock h₁ => exact absurd h₁ (by decide)
  | appCong _ h₂ =>
    intro ind c args h
    obtain ⟨init, -, rfl⟩ := mkApps_construct_app h.symm
    simp [isConstructApp, headOf_mkApps, headOf] at h₂
  | prim =>
    intro ind c args h
    have := congrArg headOf h
    simp only [headOf, headOf_mkApps] at this
    cases this
  | atom ha =>
    intro ind c args h
    subst h
    rcases eq_nil_or_snoc args with rfl | ⟨init, y, rfl⟩
    · simp
    · rw [mkApps_snoc] at ha; simp [lbAtom] at ha

/-! ## λ□ ι-reducts of erased alternatives -/

/-- λ□ λs around a body, one per binder name, the first name outermost. -/
def lams : List BinderName → LBTerm → LBTerm
  | [], t => t
  | n :: ns, t => .lambda n (lams ns t)

/-- A closed substitution under λs is shifted by their number. Reference: `csubst`
(`MR E/ECSubst.v:14`). -/
theorem csubst_lams (f : LBTerm) : ∀ (ns : List BinderName) (k : Nat) (t : LBTerm),
    csubst f k (lams ns t) = lams ns (csubst f (k + ns.length) t)
  | [], _, _ => rfl
  | n :: ns, k, t => by
    simp only [lams, csubst, csubst_lams f ns (k + 1) t, List.length_cons,
      show k + 1 + ns.length = k + (ns.length + 1) by omega]

/-- λs around a body with erased dependencies have erased dependencies. -/
theorem ErasesDeps.lams {t : LBTerm} (h : ErasesDeps cert σ lenv t) :
    ∀ ns : List BinderName, ErasesDeps cert σ lenv (SimCases.lams ns t)
  | [] => h
  | _ :: ns => .lambda (ErasesDeps.lams h ns)

/-- A λ□ λ evaluates to itself only. Reference: `eval_atom` (`MR E/EWcbvEval.v:285`). -/
theorem lam_only {na : BinderName} {b r : LBTerm} (h : LBEval defaultFlags lenv (.lambda na b) r) :
    r = .lambda na b := by
  cases h; rfl

/-- A λ□ λ applied to a value that evaluates to itself only evaluates as its body with the value
substituted. Reference: `eval_beta` (`MR E/EWcbvEval.v:127`), with `eval_deterministic`. -/
theorem beta_inv {na : BinderName} {b f r : LBTerm} (hf : LBFixed f)
    (h : LBEval defaultFlags lenv (.app (.lambda na b) f) r) :
    LBEval defaultFlags lenv (csubst f 0 b) r := by
  have hne : ∀ (g : LBTerm) (args : List LBTerm), headOf g ≠ .lambda na b →
      mkApps g args ≠ .lambda na b := fun g args hg he =>
    hg (by rw [← headOf_mkApps (args := args), he]; rfl)
  cases h with
  | box h₁ => cases lam_only h₁
  | beta h₁ h₂ h₃ => cases lam_only h₁; rw [hf _ _ h₂] at h₃; exact h₃
  | fix _ h₁ => exact absurd (lam_only h₁) (hne _ _ (by simp [headOf]))
  | fixValue _ h₁ => exact absurd (lam_only h₁) (hne _ _ (by simp [headOf]))
  | fix' hg => simp [defaultFlags] at hg
  | construct _ _ h₁ => exact absurd (lam_only h₁) (hne _ _ (by simp [headOf]))
  | appCong h₁ h₂ => rw [lam_only h₁] at h₂; simp [isLambdaT] at h₂
  | atom ha => simp [lbAtom] at ha

/-- λs applied to as many closed values that evaluate to themselves only evaluate as the body with
the values substituted, the first for the outermost λ: as λ□'s ι-reduct `iota_red`
(`MR E/EGlobalEnv.v:281`) of a branch with these binders. -/
theorem eval_lams : ∀ {fs : List LBTerm} {ns : List BinderName} {t r : LBTerm},
    ns.length = fs.length → (∀ f ∈ fs, LBFixed f ∧ closedn 0 f = true) →
    LBEval defaultFlags lenv (mkApps (lams ns t) fs) r →
    LBEval defaultFlags lenv (substl fs.reverse t) r
  | [], [], _, _, _, _, h => h
  | [], _ :: _, _, _, hl, _, _ | _ :: _, [], _, _, hl, _, _ => by simp at hl
  | f :: fs, n :: ns, t, r, hl, hfs, h => by
    have hf := hfs f List.mem_cons_self
    have hfs' : ∀ g ∈ fs, LBFixed g ∧ closedn 0 g = true :=
      fun g hg => hfs g (List.mem_cons_of_mem _ hg)
    have h' := lbeval_mkApps_congr fs (G := .app (.lambda n (lams ns t)) f)
      (fun _ hw => beta_inv hf.1 hw) h
    rw [csubst_lams, Nat.zero_add] at h'
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    rw [substl_cons_closed hf.2 fun g hg => (hfs' g hg).2, ← hl]
    exact eval_lams hl hfs' h'

/-! ## Source inversions -/

/-- No rule evaluates a `reduced`-marked term: `casesFrozen` reads the discriminant of a reduced
`casesOn` without evaluating it. -/
theorem SrcEval.not_reduced {env : ConLeche.Env} {d v : Expr} :
    ¬ SrcEval env σ (markReduced d) v := by
  intro h
  generalize hx : markReduced d = x at h
  cases h with
  | ctor | casesIota | casesLitZero | casesLitSucc | casesFrozen | quotMk | quotLift | recIota =>
    cases spine_fn hx
  | etaLam | frozen => simp [markMD] at hx
  | atom ha => subst hx; exact ha
  | beta | etaBeta | zeta | delta | constAtom | proj | projFrozen | lit | appCong | frozenApp =>
    cases hx

/-- A `reduced`-marked term has no erasure: `Erases.casesReduced` drops the discriminant of a
reduced `casesOn`. -/
theorem reduced_not_erases {Γ : List CtxBinder} {d : Expr} {tb : LBTerm} :
    ¬ Erases cert σ Γ (markReduced d) tb := by
  intro h
  generalize hx : markReduced d = y at h
  cases h with
  | ctor | cases | casesReduced | quotMk | quotLift | recLet | recFix => cases spine_fn hx
  | etaLam | box => simp [markMD] at hx
  | bvar | fvar | lam | letE | app | const | proj | litZero | litSucc => cases hx

/-- An erasure of a projection is a λ□ projection of an erasure of the major, at the parameter
count of the structure (`Erases.proj`). -/
theorem proj_inv {Γ : List CtxBinder} {S : Name} {i : Nat} {e : Expr} {tb : LBTerm}
    (h : Erases cert σ Γ (.proj S i e) tb) :
    ∃ iid iv e', tb = .proj ⟨iid, iv.numParams, i⟩ e' ∧ IndIdOf σ S = some iid ∧
      findDecl σ.decls S = some (.inductInfo iv) ∧ Erases cert σ Γ e e' := by
  generalize hx : Expr.proj S i e = y at h
  cases h with
  | proj hid hiv _ he => cases hx; exact ⟨_, _, _, rfl, hid, hiv, he⟩
  | ctor | cases | casesReduced | quotMk | quotLift | recLet | recFix => cases spine_fn hx
  | bvar | fvar | lam | etaLam | letE | app | const | litZero | litSucc | box => cases hx

/-- An alternative erased under `k` field binders erases, as a term, to the λ□ λs of its `k`
binder names around its erased body. -/
theorem ErasesAlt.erases_lams : ∀ {k : Nat} {Γ : List CtxBinder} {e : Expr} {ns : List BinderName}
    {t : LBTerm}, ErasesAlt cert σ Γ k e (ns, t) → ns.length = k ∧ Erases cert σ Γ e (lams ns t)
  | 0, _, _, _, _, h => by cases h with | done h => exact ⟨rfl, h⟩
  | _ + 1, _, _, _, _, h => by
    cases h with
    | lam h => obtain ⟨h1, h2⟩ := ErasesAlt.erases_lams h; exact ⟨by simp [h1], .lam h2⟩
    | etaLam h => obtain ⟨h1, h2⟩ := ErasesAlt.erases_lams h; exact ⟨by simp [h1], .etaLam h2⟩

/-- A head applied to arguments, all related pointwise, erases to the λ□ spine (`Erases.appS`). -/
theorem Erases.spine {Γ : List CtxBinder} : ∀ {as : List Expr} {as' : List LBTerm} {f : Expr}
    {f' : LBTerm}, as.length = as'.length →
    (∀ (i : Nat) a a', as[i]? = some a → as'[i]? = some a' → Erases cert σ Γ a a') →
    Erases cert σ Γ f f' → Erases cert σ Γ (mkAppN f as.toArray) (mkApps f' as')
  | [], [], _, _, _, _, hf => by simp only [mkAppN_toArray, List.foldl_nil]; exact hf
  | [], _ :: _, _, _, hl, _, _ | _ :: _, [], _, _, hl, _, _ => by simp at hl
  | a :: as, a' :: as', f, f', hl, h, hf => by
    rw [mkAppN_toArray, List.foldl_cons, ← mkAppN_toArray]
    show Erases cert σ Γ _ (mkApps (.app f' a') as')
    exact Erases.spine (by simpa using hl) (fun i x y hx hy => h (i + 1) x y (by simpa using hx)
      (by simpa using hy)) (Erases.appS hf (h 0 a a' (by simp) (by simp)))

/-- The major premise of a split `casesOn` spine. Copy of `ML-V Simulation/Ind.lean:697`. -/
theorem get_major (pre rest : List Expr) (maj : Expr) :
    (pre ++ [maj] ++ rest)[pre.length]? = some maj := by
  simp

/-- An alternative of a split `casesOn` spine. Copy of `ML-V Simulation/Ind.lean:702`. -/
theorem get_alt (pre alts extra : List Expr) (maj : Expr) {j : Nat} (hj : j < alts.length) :
    (pre ++ [maj] ++ alts ++ extra)[pre.length + 1 + j]? = alts[j]? := by
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by simp)]
  simp

/-- An erasure, with erased dependencies, of a saturated `casesOn` spine whose major premise
evaluates: a λ□ `case` on an erasure of the major premise, at the inductive's parameter count,
whose branch of each constructor is an erasure of the constructor's alternative under its field
binders (`Erases.cases`, without extra arguments). The reduced form (`Erases.casesReduced`) is
excluded: its discriminant is `reduced`-marked, which does not evaluate. -/
theorem cases_split {env : ConLeche.Env} (hbinj : BlockNamesInj σ.decls) {c : Name}
    {us : List Level} {iv : InductiveVal} {as : List Expr} {m mv : Expr} {tb : LBTerm}
    (hco : σ.casesOn? c = some iv) (hlen : as.length = casesArity iv)
    (hm : as[casesMajor iv]? = some m) (hmv : SrcEval env σ m mv)
    (her : Erases noCert σ [] (mkAppN (.const c us) as.toArray) tb)
    (hdeps : ErasesDeps noCert σ lenv tb) :
    ∃ iid maj' brs, IndIdOf σ iv.name = some iid ∧ tb = .case (iid, iv.numParams) maj' brs ∧
      Erases noCert σ [] m maj' ∧ ErasesDeps noCert σ lenv maj' ∧ ErasesInd σ lenv iv.name ∧
      ∀ (j : Nat) cn alt, iv.ctors[j]? = some cn → as[casesMajor iv + 1 + j]? = some alt →
        ∃ k br, ctorFields σ cn = some k ∧ brs[j]? = some br ∧
          ErasesAlt noCert σ [] k alt br ∧ ErasesDeps noCert σ lenv br.2 := by
  rcases Erases.cases_inv hco her with
    ⟨pre, maj, alts, extra, iid, maj', brs, extra', rfl, hid, hpre, halts, hmaj, hbrs, hcf, halt,
      hlex, -, rfl⟩ |
    ⟨pre, d, _, _, _, _, _, _, rfl, -, -, -, -, hpre, -⟩
  · have hex : extra = [] := List.eq_nil_of_length_eq_zero (by
      simp only [List.length_append, List.length_singleton, hpre, halts, casesArity] at hlen
      omega)
    subst hex
    obtain rfl : extra' = [] := List.eq_nil_of_length_eq_zero hlex.symm
    rw [← hpre, List.append_assoc, get_major] at hm
    cases hm
    cases hdeps with
    | case hidT hindT hdmaj hdbrs =>
    rw [indIdOf_inj hbinj hidT hid] at hindT
    refine ⟨iid, maj', brs, hid, rfl, hmaj, hdmaj, hindT, fun j cn alt hcn halt' => ?_⟩
    have hj : j < alts.length := halts ▸ (List.getElem?_eq_some_iff.1 hcn).1
    rw [← hpre, get_alt _ _ _ _ hj] at halt'
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 (hcf j cn hcn)
    obtain ⟨br, hbr⟩ : ∃ br, brs[j]? = some br := ⟨_, List.getElem?_eq_getElem (hbrs ▸ hj)⟩
    exact ⟨k, br, hk, hbr, halt j cn alt br k hcn halt' hbr hk,
      hdbrs br (List.mem_of_getElem? hbr)⟩
  · rw [← hpre, List.append_assoc, get_major] at hm
    cases hm
    exact absurd hmv SrcEval.not_reduced

/-- The ι step of λ□ on a constructor value of the major premise: the branch of the constructor,
erased under its field binders, is the erasure of the alternative applied to the fields, and
λ□'s ι-reduct evaluates as that application's erasure (`eval_lams`), whose fields are closed
(their source fields have no loose bound variable) λ□ values. Reference: the `eval_iota` case of
`erases_correct` (`MR E/ErasureCorrectness.v:182`), with `iota_red` (`MR E/EGlobalEnv.v:281`). -/
theorem iota_step {iv : InductiveVal} {iid : InductiveId} {i : Nat} {maj' : LBTerm}
    {brs : List (List BinderName × LBTerm)} {br : List BinderName × LBTerm} {args : List LBTerm}
    {cb : ConstructorBody} {alt v : Expr} {fs : List Expr}
    (hlk : ctorIsPropParsDecl lenv iid i = some (false, iv.numParams, cb))
    (hev : LBEval defaultFlags lenv maj' (mkApps (.construct iid i []) args))
    (hargs : args.length = iv.numParams + cb.nargs) (hfl : fs.length = cb.nargs)
    (hfe : ∀ (j : Nat) f f', fs[j]? = some f → args[iv.numParams + j]? = some f' →
      Erases noCert σ [] f f')
    (hcl : ∀ f ∈ fs, AbsFV.LBV 0 f) (hdargs : ∀ a ∈ args, ErasesDeps noCert σ lenv a)
    (hbr : brs[i]? = some br) (halt : ErasesAlt noCert σ [] cb.nargs alt br)
    (hdbr : ErasesDeps noCert σ lenv br.2) (ih : ErasesSim σ lenv (mkAppN alt fs.toArray) v) :
    ∃ vb, Erases noCert σ [] v vb ∧
      LBEval defaultFlags lenv (.case (iid, iv.numParams) maj' brs) vb := by
  obtain ⟨ns, t⟩ := br
  obtain ⟨hns, hlam⟩ := ErasesAlt.erases_lams halt
  have hfl' : (args.drop iv.numParams).length = fs.length := by simp [hargs, hfl]
  have hfe' : ∀ (j : Nat) f f', fs[j]? = some f → (args.drop iv.numParams)[j]? = some f' →
      Erases noCert σ [] f f' :=
    fun j f f' hf hf' => hfe j f f' hf (by simpa [List.getElem?_drop] using hf')
  have hres : ∀ a ∈ args, LBEval defaultFlags lenv a a := construct_args hev _ _ _ rfl
  have hfix : ∀ f' ∈ args.drop iv.numParams, LBFixed f' ∧ closedn 0 f' = true := by
    intro f' hf'
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hf'
    have hjf : j < fs.length := hfl' ▸ hj
    exact ⟨RecEval.LBEval.fixed (hres _ (List.mem_of_mem_drop hf')),
      Erases.closed (hcl _ (List.getElem_mem hjf))
        (hfe' j _ _ (List.getElem?_eq_getElem hjf) (List.getElem?_eq_getElem hj))⟩
  obtain ⟨vb, hvb, hevb⟩ := ih (Erases.spine hfl'.symm hfe' hlam)
    (ErasesDeps.mkApps_iff.2 ⟨ErasesDeps.lams hdbr ns,
      fun a ha => hdargs a (List.mem_of_mem_drop ha)⟩)
  exact ⟨vb, hvb, .iota rfl hev hlk hbr hargs (by simp [hargs, hns])
    (eval_lams (by rw [hns, ← hfl, hfl']) hfix hevb)⟩

/-! ## The cases -/

/-- The `ctor` case of `erases_correct`: a saturated constructor spine erases to the λ□
constructor applied to erasures of its arguments (`Erases.ctor_inv`), which evaluate one by one
(`eval_construct`) to erasures of the arguments' values; the λ□ block entry of the constructor
has its parameter and field counts (`ErasesInd.lookupCtor`, `CtorsListed`). ML-V also has a `□`
erasure of the spine. Adapted from `ML-V Simulation/Ind.lean:799`. Reference: the
`eval_construct` case of `erases_correct` (`MR E/ErasureCorrectness.v:1068`). -/
theorem erases_correct_ctor (hbinj : BlockNamesInj σ.decls) (hcl : CtorsListed σ.decls)
    {c : Name} {us : List Level} {cv : ConstructorVal} {as vs : List Expr}
    (hc : findDecl σ.decls c = some (.ctorInfo cv)) (hl : as.length = cv.numParams + cv.numFields)
    (hlv : as.length = vs.length)
    (ih : ∀ (i : Nat) a v, as[i]? = some a → vs[i]? = some v → ErasesSim σ lenv a v) :
    ErasesSim σ lenv (mkAppN (.const c us) as.toArray) (mkAppN (.const c us) vs.toArray) := by
  intro tb her hdeps
  obtain ⟨iid, as', hid, rfl, hlen, hall, hp, -⟩ := Erases.ctor_inv hc her
  obtain ⟨hd0, hdas⟩ := ErasesDeps.mkApps_iff.1 hdeps
  obtain ⟨iv, hiv, hk, hnp⟩ := hcl c cv hc
  obtain ⟨mib, ob, cb, cv', hlk, hc', hnpars, hnargs, -⟩ :=
    ErasesInd.lookupCtor hid (ErasesDeps.construct_ind hbinj hid hd0) hiv hk
  rw [hc] at hc'
  cases hc'
  obtain ⟨ys, hys, hy⟩ := choose_list (n := as.length)
    (R := fun i y => (∀ v, vs[i]? = some v → Erases noCert σ [] v y) ∧
      ∀ a', as'[i]? = some a' → LBEval defaultFlags lenv a' y) fun i hi => by
    have ha := List.getElem?_eq_getElem hi
    have hv := List.getElem?_eq_getElem (hlv ▸ hi)
    have ha' := List.getElem?_eq_getElem (hlen ▸ hi)
    obtain ⟨vb, hvb, hev⟩ := ih i _ _ ha hv (hall i _ _ ha ha') (hdas _ (List.getElem_mem _))
    exact ⟨vb, fun v h => by rw [hv] at h; cases h; exact hvb,
      fun a' h => by rw [ha'] at h; cases h; exact hev⟩
  refine ⟨mkApps (.construct iid cv.cidx []) ys,
    Erases.ctor hc hp hid (by omega) (by omega) fun i v y hv hy' => (hy i y hy').1 v hv,
    lbeval_construct hlk as' ys (by omega) (by omega) fun i a' y ha' hy' => (hy i y hy').2 a' ha'⟩

/-- The `lit` case of `erases_correct`: a Nat literal erases to λ□'s Peano numeral
(`Erases.litZero`, `Erases.litSucc`), a λ□ value, whose constructors are those of `Nat`
(`NatShaped`). ML-V also has a `□` erasure of the literal. Adapted from
`ML-V Simulation/Ind.lean:733`. Reference: the `eval_atom` case of `erases_correct`
(`MR E/ErasureCorrectness.v:1179`). -/
theorem erases_correct_lit (hbinj : BlockNamesInj σ.decls) (hnat : NatShaped σ) {k : Nat} :
    ErasesSim σ lenv (.lit (.natVal k)) (.lit (.natVal k)) := by
  intro tb her hdeps
  refine ⟨tb, her, ?_⟩
  have lk : ∀ {iid : InductiveId} {c : Nat} {args : List LBTerm} (j : Nat), j < 2 →
      IndIdOf σ ``Nat = some iid → ErasesDeps noCert σ lenv (.construct iid c args) →
      ∃ mib ob cb, lookupCtor lenv iid j = some (mib, ob, cb) ∧ mib.npars + cb.nargs = j := by
    intro iid c args j hj hid hd
    have hind := ErasesDeps.construct_ind hbinj hid hd
    obtain ⟨iv, hiv, -⟩ := id hind
    obtain ⟨hnp, -, z, s, hcs, hz, hs⟩ := hnat iv hiv
    obtain ⟨C, hC, hf⟩ : ∃ C, iv.ctors[j]? = some C ∧ ctorFields σ C = some j := by
      rw [hcs]
      match j, hj with
      | 0, _ => exact ⟨z, rfl, hz⟩
      | 1, _ => exact ⟨s, rfl, hs⟩
    obtain ⟨mib, ob, cb, cv, hlk, hcv, hnpars, hnargs, -⟩ := ErasesInd.lookupCtor hid hind hiv hC
    simp only [ctorFields, hcv, Option.some.injEq] at hf
    exact ⟨mib, ob, cb, hlk, by omega⟩
  induction k generalizing tb with
  | zero =>
    generalize hx : Expr.lit (.natVal 0) = x at her
    cases her with
    | litZero hid =>
      obtain ⟨mib, ob, cb, hlk, -⟩ := lk 0 (by omega) hid hdeps
      exact .atom (by simp [lbAtom, defaultFlags, hlk])
    | litSucc => cases hx
    | ctor | cases | casesReduced | quotMk | quotLift | recLet | recFix => cases spine_fn hx
    | bvar | fvar | lam | etaLam | letE | app | const | proj | box => cases hx
  | succ k ih =>
    generalize hx : Expr.lit (.natVal (k + 1)) = x at her
    cases her with
    | litSucc hid h' =>
      cases hx
      cases hdeps with
      | app hd0 hd1 =>
      obtain ⟨mib, ob, cb, hlk, hn⟩ := lk 1 (by omega) hid hd0
      exact .construct (args := []) rfl hlk (.atom (by simp [lbAtom, defaultFlags, hlk]))
        (by simp; omega) (ih h' hd1)
    | litZero => cases hx
    | ctor | cases | casesReduced | quotMk | quotLift | recLet | recFix => cases spine_fn hx
    | bvar | fvar | lam | etaLam | letE | app | const | proj | box => cases hx

/-- The `casesIota` case of `erases_correct`: the major premise's erasure evaluates to an erasure
of its constructor value, the λ□ constructor of the inductive's block at its index applied to
erasures of the parameters and fields (`Erases.ctor_inv`, `CtorsListed`); λ□'s ι on it reduces
the erased alternative (`iota_step`), as the source evaluates the alternative applied to the fields.
The `casesOn` is not reduced: its major premise evaluates. ML-V relates a head-β reduct of the
alternative applied to the fields (`SimIota.drive`) and has a `□` erasure of the spine. Adapted
from `ML-V Simulation/Iota.lean:1193`. Reference: the `eval_iota` case of `erases_correct`
(`MR E/ErasureCorrectness.v:182`). -/
theorem erases_correct_casesIota (hbinj : BlockNamesInj σ.decls) (hcl : CtorsListed σ.decls)
    {env : ConLeche.Env} {c : Name} {us : List Level} {iv : InductiveVal} {as fs : List Expr}
    {m mv alt v : Expr} {i : Nat}
    (hco : σ.casesOn? c = some iv) (hlen : as.length = casesArity iv)
    (hm : as[casesMajor iv]? = some m) (hmv : SrcEval env σ m mv)
    (hcv : CtorValue σ iv.name mv i fs)
    (hok : CLOk env (mkAppN (.const c us) (as.set (casesMajor iv) mv).toArray))
    (halt : as[casesMajor iv + 1 + i]? = some alt)
    (ihm : ErasesSim σ lenv m mv) (ihalt : ErasesSim σ lenv (mkAppN alt fs.toArray) v) :
    ErasesSim σ lenv (mkAppN (.const c us) as.toArray) v := by
  intro tb her hdeps
  obtain ⟨iid, maj', brs, hid, rfl, hmaj, hdmaj, hind, halts⟩ :=
    cases_split hbinj hco hlen hm hmv her hdeps
  obtain ⟨mb, hmb, hevmb⟩ := ihm hmaj hdmaj
  have hlbv := AbsFV.LBV_mkAppN.1 hok.lbv mv (List.mem_of_getElem? (List.getElem?_set_self
    (List.getElem?_eq_some_iff.1 hm).1))
  obtain ⟨C, us', cv, ps, hC, hind', rfl, hps, hfsl, rfl⟩ := hcv
  obtain ⟨iid', as', hid', rfl, hlen', hall, hpI, -⟩ := Erases.ctor_inv hC hmb
  rw [hind', hid] at hid'
  cases hid'
  have hiv := Restrict.casesOnOf?_ind hco
  obtain ⟨iv₀, hiv₀, hk, hnp⟩ := hcl C cv hC
  rw [hind', hiv] at hiv₀
  cases hiv₀
  obtain ⟨mib, ob, cb, cv', hlk, hC', hnpars, hnargs, hprop⟩ := ErasesInd.lookupCtor hid hind hiv hk
  rw [hC] at hC'
  cases hC'
  obtain ⟨k, br, hk', hbr, haltb, hdbr⟩ := halts cv.cidx C alt hk halt
  simp only [ctorFields, hC, Option.some.injEq] at hk'
  subst hk'
  have hpf : ob.propositional = false :=
    Bool.eq_false_iff.2 fun h => by rw [hind'] at hpI; rw [hprop.1 h] at hpI; cases hpI
  obtain ⟨hdm0, hdargs⟩ := ErasesDeps.mkApps_iff.1 (ErasesDeps.eval hdmaj hevmb)
  refine iota_step (by simp [ctorIsPropParsDecl, hlk, hpf, hnpars]) hevmb
    (by simp only [← hlen', List.length_append]; omega) (by omega) (fun j f f' hf hf' => ?_)
    (fun f hf => (AbsFV.LBV_mkAppN.1 hlbv) f (List.mem_append_right _ hf)) hdargs hbr
    (hnargs ▸ haltb) hdbr ihalt
  refine hall _ f f' ?_ (by rw [hnp] at hf'; exact hf')
  rw [← hps, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  exact hf

/-- The `casesLitZero` case of `erases_correct`: the major premise's erasure evaluates to the
erasure of `0`, λ□'s constructor `0` of `Nat`, whose first alternative is under no field binder
(`NatShaped`); λ□'s ι selects it. Adapted from `ML-V Simulation/Ind.lean:994`. Reference: the
`eval_iota` case of `erases_correct` (`MR E/ErasureCorrectness.v:182`) on the literal `0`. -/
theorem erases_correct_casesLitZero (hbinj : BlockNamesInj σ.decls) (hnat : NatShaped σ)
    {env : ConLeche.Env} {c : Name} {us : List Level} {iv : InductiveVal} {as : List Expr}
    {m alt v : Expr} (hco : σ.casesOn? c = some iv) (hn : iv.name = ``Nat)
    (hlen : as.length = casesArity iv) (hm : as[casesMajor iv]? = some m)
    (hmv : SrcEval env σ m (.lit (.natVal 0))) (halt : as[casesMajor iv + 1]? = some alt)
    (ihm : ErasesSim σ lenv m (.lit (.natVal 0))) (ihalt : ErasesSim σ lenv alt v) :
    ErasesSim σ lenv (mkAppN (.const c us) as.toArray) v := by
  intro tb her hdeps
  obtain ⟨iid, maj', brs, hid, rfl, hmaj, hdmaj, hind, halts⟩ :=
    cases_split hbinj hco hlen hm hmv her hdeps
  obtain ⟨mb, hmb, hevmb⟩ := ihm hmaj hdmaj
  have hiv := Restrict.casesOnOf?_ind hco
  rw [hn] at hid hind hiv
  obtain ⟨hnp, hpN, z, s, hcs, hz, -⟩ := hnat iv hiv
  have hmb0 : mb = .construct iid 0 [] := by
    generalize hx : Expr.lit (.natVal 0) = x at hmb
    cases hmb with
    | litZero hid' => rw [hid] at hid'; cases hid'; rfl
    | litSucc => cases hx
    | ctor | cases | casesReduced | quotMk | quotLift | recLet | recFix => cases spine_fn hx
    | bvar | fvar | lam | etaLam | letE | app | const | proj | box => cases hx
  subst hmb0
  have hz0 : iv.ctors[0]? = some z := by rw [hcs]; rfl
  obtain ⟨mib, ob, cb, cv, hlk, hcv, hnpars, hnargs, hprop⟩ := ErasesInd.lookupCtor hid hind hiv hz0
  obtain ⟨k, br, hk, hbr, haltb, hdbr⟩ := halts 0 z alt hz0 halt
  rw [hz] at hk
  cases hk
  simp only [ctorFields, hcv, Option.some.injEq] at hz
  have hpf : ob.propositional = false :=
    Bool.eq_false_iff.2 fun h => by rw [hprop.1 h] at hpN; cases hpN
  exact iota_step (fs := []) (args := []) (cb := cb) (alt := alt) (by simp [ctorIsPropParsDecl, hlk, hpf, hnpars])
    hevmb (by simp; omega) (by simp; omega) (fun _ _ _ h => by simp at h) (by simp) (by simp) hbr
    (by rw [hnargs, hz]; exact haltb) hdbr (by rw [mkAppN_toArray, List.foldl_nil]; exact ihalt)

/-- The `casesLitSucc` case of `erases_correct`: the major premise's erasure evaluates to the
erasure of `k + 1`, λ□'s constructor `1` of `Nat` applied to the erasure of `k`, whose second
alternative is under one field binder (`NatShaped`); λ□'s ι reduces it at the erasure of `k`, as
the source evaluates the alternative applied to `k` (`iota_step`). Adapted from
`ML-V Simulation/Iota.lean:1370`. Reference: the `eval_iota` case of `erases_correct`
(`MR E/ErasureCorrectness.v:182`) on the literal `k + 1`. -/
theorem erases_correct_casesLitSucc (hbinj : BlockNamesInj σ.decls) (hnat : NatShaped σ)
    {env : ConLeche.Env} {c : Name} {us : List Level} {iv : InductiveVal} {as : List Expr}
    {m alt v : Expr} {k : Nat} (hco : σ.casesOn? c = some iv) (hn : iv.name = ``Nat)
    (hlen : as.length = casesArity iv) (hm : as[casesMajor iv]? = some m)
    (hmv : SrcEval env σ m (.lit (.natVal (k + 1)))) (halt : as[casesMajor iv + 2]? = some alt)
    (ihm : ErasesSim σ lenv m (.lit (.natVal (k + 1))))
    (ihalt : ErasesSim σ lenv (.app alt (.lit (.natVal k))) v) :
    ErasesSim σ lenv (mkAppN (.const c us) as.toArray) v := by
  intro tb her hdeps
  obtain ⟨iid, maj', brs, hid, rfl, hmaj, hdmaj, hind, halts⟩ :=
    cases_split hbinj hco hlen hm hmv her hdeps
  obtain ⟨mb, hmb, hevmb⟩ := ihm hmaj hdmaj
  have hiv := Restrict.casesOnOf?_ind hco
  rw [hn] at hid hind hiv
  obtain ⟨hnp, hpN, z, s, hcs, -, hs⟩ := hnat iv hiv
  obtain ⟨t', rfl, ht'⟩ : ∃ t', mb = .app (.construct iid 1 []) t' ∧
      Erases noCert σ [] (.lit (.natVal k)) t' := by
    generalize hx : Expr.lit (.natVal (k + 1)) = x at hmb
    cases hmb with
    | litSucc hid' h' => cases hx; rw [hid] at hid'; cases hid'; exact ⟨_, rfl, h'⟩
    | litZero => cases hx
    | ctor | cases | casesReduced | quotMk | quotLift | recLet | recFix => cases spine_fn hx
    | bvar | fvar | lam | etaLam | letE | app | const | proj | box => cases hx
  have hs1 : iv.ctors[1]? = some s := by rw [hcs]; rfl
  obtain ⟨mib, ob, cb, cv, hlk, hcv, hnpars, hnargs, hprop⟩ := ErasesInd.lookupCtor hid hind hiv hs1
  obtain ⟨k', br, hk, hbr, haltb, hdbr⟩ := halts 1 s alt hs1 halt
  rw [hs] at hk
  cases hk
  simp only [ctorFields, hcv, Option.some.injEq] at hs
  have hpf : ob.propositional = false :=
    Bool.eq_false_iff.2 fun h => by rw [hprop.1 h] at hpN; cases hpN
  obtain ⟨-, hdargs⟩ := (ErasesDeps.mkApps_iff (f := .construct iid 1 []) (args := [t'])).1
    (ErasesDeps.eval hdmaj hevmb)
  exact iota_step (fs := [.lit (.natVal k)]) (args := [t']) (i := 1) (cb := cb) (alt := alt)
    (by simp [ctorIsPropParsDecl, hlk, hpf, hnpars]) hevmb (by simp; omega) (by simp; omega)
    (fun j f f' hf hf' => by
      rw [hnp, Nat.zero_add] at hf'
      match j, hf, hf' with
      | 0, hf, hf' => cases hf; cases hf'; exact ht')
    (by simp [AbsFV.LBV]) hdargs hbr (by rw [hnargs, hs]; exact haltb) hdbr
    (by rw [mkAppN_toArray, List.foldl_cons, List.foldl_nil]; exact ihalt)

/-- The `casesFrozen` case of `erases_correct`: a `casesOn` with a `reduced`-marked discriminant
erases to its reduced form only (`Erases.casesReduced`; the discriminant has no erasure), the
erased alternative applied to `□` for each field, which is exactly an erasure of the alternative
applied to the frozen projections of the discriminant (`Erases.box`), whose evaluation the
induction hypothesis gives. Reference: `eval_iota_sing` (`MR E/EWcbvEval.v:162`) at erasure time
(DV-25). -/
theorem erases_correct_casesFrozen {c : Name} {us : List Level} {iv : InductiveVal} {cn : Name}
    {cv : ConstructorVal} {as : List Expr} {d alt v : Expr}
    (hco : σ.casesOn? c = some iv) (hlen : as.length = casesArity iv) (hcs : iv.ctors = [cn])
    (hcn : findDecl σ.decls cn = some (.ctorInfo cv))
    (hm : as[casesMajor iv]? = some (markReduced d)) (halt : as[casesMajor iv + 1]? = some alt)
    (ih : ErasesSim σ lenv (mkAppN alt ((List.range cv.numFields).map fun j =>
      markErase (.proj iv.name j d)).toArray) v) :
    ErasesSim σ lenv (mkAppN (.const c us) as.toArray) v := by
  intro tb her hdeps
  rcases Erases.cases_inv hco her with
    ⟨pre, maj, alts, extra, _, _, _, _, rfl, -, hpre, -, hmaj, -⟩ |
    ⟨pre, d', alt', extra, cn', cv', alt'', extra', rfl, -, hcs', hcv', -, hpre, halt', hlex, -, rfl⟩
  · rw [← hpre, List.append_assoc, List.append_assoc, ← List.append_assoc, get_major] at hm
    cases hm
    exact absurd hmaj reduced_not_erases
  · have hex : extra = [] := List.eq_nil_of_length_eq_zero (by
      simp only [List.length_append, hpre, hcs, casesArity, List.length_cons,
        List.length_nil] at hlen
      omega)
    subst hex
    obtain rfl : extra' = [] := List.eq_nil_of_length_eq_zero hlex.symm
    rw [hcs] at hcs'
    cases hcs'
    rw [hcn] at hcv'
    cases hcv'
    have hget : (pre ++ [markReduced d'] ++ [alt'] ++ [])[pre.length + 1]? = some alt' := by simp
    rw [← hpre, hget] at halt
    cases halt
    rw [List.append_nil] at hdeps ⊢
    exact ih (Erases.spine (by simp) (fun j a a' ha ha' => by
      simp only [List.getElem?_map, List.getElem?_replicate] at ha ha'
      obtain ⟨x, -, rfl⟩ := Option.map_eq_some_iff.1 ha
      split at ha' <;> cases ha'
      exact .box trivial) halt') hdeps

/-- The `proj` case of `erases_correct`: the major premise's erasure evaluates to an erasure of its
constructor value, the λ□ constructor `0` of the structure's block applied to erasures of the
parameters and fields (`Erases.ctor_inv`, `CtorsListed`); λ□'s projection selects the erasure of
the field, a λ□ value. ML-V also has a `□` erasure of the projection. Adapted from
`ML-V Simulation/Ind.lean:857`. Reference: the `eval_proj` case of `erases_correct`
(`MR E/ErasureCorrectness.v:489`). -/
theorem erases_correct_proj (hbinj : BlockNamesInj σ.decls) (hcl : CtorsListed σ.decls)
    {S : Name} {i : Nat} {e m a : Expr} {fs : List Expr}
    (hcv : CtorValue σ S m 0 fs) (hfs : fs[i]? = some a) (ihe : ErasesSim σ lenv e m) :
    ErasesSim σ lenv (.proj S i e) a := by
  intro tb her hdeps
  obtain ⟨iid, iv, e', rfl, hid, hiv, he⟩ := proj_inv her
  cases hdeps with
  | proj hidT hindT hd =>
  rw [indIdOf_inj hbinj hidT hid] at hindT
  obtain ⟨mb, hmb, hevmb⟩ := ihe he hd
  obtain ⟨C, us', cv, ps, hC, hind', hcidx, hps, hfsl, rfl⟩ := hcv
  obtain ⟨iid', as', hid', rfl, hlen', hall, hpI, -⟩ := Erases.ctor_inv hC hmb
  rw [hind', hid] at hid'
  cases hid'
  obtain ⟨iv₀, hiv₀, hk, hnp⟩ := hcl C cv hC
  rw [hind', hiv] at hiv₀
  cases hiv₀
  obtain ⟨mib, ob, cb, cv', hlk, hC', hnpars, hnargs, hprop⟩ :=
    ErasesInd.lookupCtor hid hindT hiv hk
  rw [hC] at hC'
  cases hC'
  have hpf : ob.propositional = false :=
    Bool.eq_false_iff.2 fun h => by rw [hind'] at hpI; rw [hprop.1 h] at hpI; cases hpI
  have hi : i < fs.length := (List.getElem?_eq_some_iff.1 hfs).1
  obtain ⟨a', ha'⟩ : ∃ a', as'[iv.numParams + i]? = some a' :=
    ⟨_, List.getElem?_eq_getElem (by simp only [← hlen', List.length_append]; omega)⟩
  have hera : Erases noCert σ [] a a' := hall _ a a' (by
    rw [hnp, ← hps, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]; exact hfs) ha'
  rw [hcidx] at hevmb hlk
  exact ⟨a', hera, .proj (cdecl := cb) rfl hevmb (by simp [ctorIsPropParsDecl, hlk, hpf, hnpars])
    (by simp only [← hlen', List.length_append]; omega) ha'
    (construct_args hevmb _ _ _ rfl a' (List.mem_of_getElem? ha'))⟩

/-- The `projFrozen` case of `erases_correct`: the major premise's erasure evaluates to `□`, an
erasure of its frozen value, and the structure's λ□ block is propositional (`ErasesInd`), so
λ□'s projection of `□` is `□` (`eval_proj_prop`), an erasure of the frozen projection. Adapted
from `ML-V Simulation/Ind.lean:919`. Reference: `eval_proj_prop` (`MR E/EWcbvEval.v:238`). -/
theorem erases_correct_projFrozen (hbinj : BlockNamesInj σ.decls) {S : Name} {i : Nat}
    {e d : Expr} (hp : σ.propInd S = true) (ihe : ErasesSim σ lenv e (markErase d)) :
    ErasesSim σ lenv (.proj S i e) (markErase (.proj S i d)) := by
  intro tb her hdeps
  obtain ⟨iid, iv, e', rfl, hid, hiv, he⟩ := proj_inv her
  cases hdeps with
  | proj hidT hindT hd =>
  rw [indIdOf_inj hbinj hidT hid] at hindT
  obtain ⟨mb, hmb, hevmb⟩ := ihe he hd
  obtain rfl := box_inv hmb
  obtain ⟨b, hb, hbp⟩ := ErasesInd.indIsPropAndPars hid hindT hiv
  rw [hbp.2 hp] at hb
  exact ⟨.box, .box trivial, .projProp rfl hevmb hb⟩

end SimCases

end EraseProof
