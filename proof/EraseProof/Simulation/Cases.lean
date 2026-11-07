import EraseProof.Source.ProofSound
import EraseProof.Relation.Inst
import EraseProof.Relation.Levels
import EraseProof.Relation.Deps
import EraseProof.Relation.Basic
import EraseProof.Erasable.Inv
import EraseProof.Erasable.Subst
import EraseProof.Erasable.Atom

/-!
# Cases of the relation-level simulation

`erases_correct` (`MR E/ErasureCorrectness.v:51`) is proved by induction on the source evaluation,
one case per rule of `SrcEval`. This module proves the cases of the rules `beta`, `zeta`, `delta`,
`constAtom`, `mdata` and `atom`, each as a theorem whose premises are the rule's premises and the
induction hypotheses of its evaluation premises (`ErasesSim`), and whose conclusion is `ErasesSim`
of the rule's conclusion. Every case first handles an erasure to `□` uniformly
(`erases_correct_box`): the value is erasable too (`ErasableS.eval`), so it erases to `□`, a λ□
value.
-/

open Lean Erasure
open Metalean (Defeq EnvWF TypeEq WHRed)

namespace EraseProof

/-- The conclusion of `erases_correct` for one evaluation `e ⇓ v`: every erasure, with erased
dependencies, of a typed translation of `e` evaluates in λ□ to an erasure of `v`. The induction
hypothesis of each case of the simulation. Reference: the induction hypotheses of
`erases_correct` (`MR E/ErasureCorrectness.v:51`). -/
def ErasesSim {ζ : Metalean.Sigs} (E : Metalean.Env ζ) (B : Binds ζ) (lps : List Name)
    (σ : EvalEnv) (lenv : GlobalDeclarations) (e v : Expr) : Prop :=
  ∀ {t : Metalean.Expr ζ lps.length 0} {tb : LBTerm}, TrM E B lps .nil [] e t →
    (∃ T, E[.nil] ⊢ t : T) → Erases E B lps σ .nil [] e tb → ErasesDeps E B σ lenv tb →
    ∃ vb, Erases E B lps σ .nil [] v vb ∧ LBEval defaultFlags lenv tb vb

namespace SimCases

variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P : List ConstantInfo}
  {σ : EvalEnv} {lps : List Name}

/-- Appending an argument to a λ□ spine. -/
theorem mkApps_snoc : ∀ (t : LBTerm) (l : List LBTerm) (x : LBTerm),
    mkApps t (l ++ [x]) = .app (mkApps t l) x
  | _, [], _ => rfl
  | t, a :: l, x => mkApps_snoc (.app t a) l x

/-- The arguments of a constant spine with one more argument. -/
theorem forall_snoc {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β} {x : α} {y : β}
    (hlen : l.length = l'.length)
    (h : ∀ (i : Nat) a b, (l ++ [x])[i]? = some a → (l' ++ [y])[i]? = some b → R a b) :
    (∀ (i : Nat) a b, l[i]? = some a → l'[i]? = some b → R a b) ∧ R x y := by
  refine ⟨fun i a b ha hb => h i a b ?_ ?_, h l.length x y (by simp) (by simp [hlen])⟩
  · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp ha).1]; exact ha
  · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hb).1]; exact hb

/-- A list is empty or has a last element. -/
theorem eq_nil_or_snoc {α : Type} (l : List α) : l = [] ∨ ∃ l' x, l = l' ++ [x] := by
  rcases l.eq_nil_or_concat with h | ⟨L, b, h⟩
  · exact .inl h
  · exact .inr ⟨L, b, by simp [h]⟩

/-- A recognized `casesOn` has its arity as a special constant. -/
theorem specialArity_casesOn {c : Name} {iv : InductiveVal} (hc : σ.casesOn? c = some iv) :
    specialArity σ c = some (casesArity iv) := by
  obtain ⟨d, hd⟩ := SrcDefeq.casesOn?_defn hc
  unfold specialArity
  rw [hd, hc]
  rfl

/-- A spine `c.{us} as` with `as` at most the arity `ar` of `c` is short. -/
theorem shortSpine_of {c : Name} {us : List Level} {as : List Expr} {f a : Expr} {ar : Nat}
    (hx : Expr.app f a = mkAppN (.const c us) as.toArray) (har : specialArity σ c = some ar)
    (hle : as.length ≤ ar) : ShortSpine σ (.app f a) :=
  ⟨c, us, ar, by rw [hx, SrcDefeq.getAppFn_mkAppN_const], har,
    by rw [hx, SrcDefeq.getAppNumArgs_mkAppN_const]; exact hle⟩

/-- An η-expanded spine has fewer arguments than its arity. -/
theorem etaSpine?_lt {c : Name} {us : List Level} {as : List Expr} {e' : Expr}
    (h : σ.etaSpine? c us as = some e') : ∃ ar, specialArity σ c = some ar ∧ as.length < ar := by
  unfold EvalEnv.etaSpine? at h
  split at h
  · rename_i ar _ har
    split at h
    · exact ⟨ar, har, by assumption⟩
    · cases h
  · cases h

/-- A spine headed by a recursor evaluates only with at least the recursor's arity of arguments:
by `SrcEval.recIota`, at the arity, or as the head of an application. -/
theorem rec_spine_len {e w : Expr} (hev : SrcEval σ e w) :
    ∀ {c : Name} {us : List Level} {bs : List Expr} {rv : RecursorVal},
      e = mkAppN (.const c us) bs.toArray → findDecl σ.decls c = some (.recInfo rv) →
      rv.numParams + rv.numMotives + rv.numMinors + rv.numIndices + 1 ≤ bs.length := by
  have head : ∀ {c c' : Name} {us us' : List Level} {as bs : List Expr},
      mkAppN (.const c' us') as.toArray = mkAppN (.const c us) bs.toArray → c' = c := by
    intro c c' us us' as bs hx
    rw [mkAppN_eq_foldl, mkAppN_eq_foldl] at hx
    exact (foldl_app_const_inj hx).1
  induction hev with
  | beta _ _ _ _ ihf | appCong _ _ _ _ ihf =>
    intro c us bs rv hx hr
    obtain ⟨bs', rfl, rfl⟩ := SrcDefeq.spine_app hx.symm
    have := ihf rfl hr
    simp only [List.length_append, List.length_singleton]; omega
  | delta hu =>
    intro c us bs rv hx hr
    obtain ⟨-, rfl, -⟩ := SrcDefeq.spine_const hx.symm
    obtain ⟨d, hd⟩ := SrcDefeq.unfold?_defn hu
    rw [hd] at hr; cases hr
  | constAtom ha =>
    intro c us bs rv hx hr
    obtain ⟨-, rfl, -⟩ := SrcDefeq.spine_const hx.symm
    unfold EvalEnv.isAtom at ha
    rw [hr] at ha
    simp [OwnRules] at ha
  | eta he =>
    intro c us bs rv hx hr
    cases head hx
    obtain ⟨ar, har, -⟩ := etaSpine?_lt he
    rcases SrcDefeq.specialArity_some har with ⟨cv, hcv, -⟩ | ⟨iv, hiv⟩ | ⟨qv, hqv, -⟩
    · rw [hr] at hcv; cases hcv
    · obtain ⟨d, hd⟩ := SrcDefeq.casesOn?_defn hiv
      rw [hr] at hd; cases hd
    · rw [hr] at hqv; cases hqv
  | ctor hc | quotMk hc | quotLift hc =>
    intro c us bs rv hx hr
    cases head hx
    rw [hr] at hc; cases hc
  | casesIota hcs | casesLitZero hcs | casesLitSucc hcs | casesProof hcs =>
    intro c us bs rv hx hr
    cases head hx
    obtain ⟨d, hd⟩ := SrcDefeq.casesOn?_defn hcs
    rw [hr] at hd; cases hd
  | recIota hcr _ _ _ hni _ _ hps hms hmins =>
    intro c us bs rv hx hr
    rw [mkAppN_eq_foldl, mkAppN_eq_foldl] at hx
    obtain ⟨rfl, -, rfl⟩ := foldl_app_const_inj hx
    rw [hr] at hcr; cases hcr
    simp only [List.length_append, List.length_singleton, hps, hms, hmins, hni]
    omega
  | zeta | proj | projProp | lit | mdata =>
    intro c us bs rv hx
    exact absurd hx (CasesWhred.ne_mkAppN_const fun _ _ h => by cases h)
  | atom ha =>
    rename_i e
    intro c us bs rv hx
    refine absurd hx (CasesWhred.ne_mkAppN_const fun _ _ h => ?_)
    cases e <;> simp [SrcAtom, Expr.getAppFn] at ha h

/-- An erasure of an application with more arguments than the arity of its head (no short
spine), whose head is no constructor, is `□` or an application of erasures: a `casesOn` spine
erased by `Erases.cases` or `Erases.casesReduced` has an extra argument, which is the last one.
Reference: `erases_mkApps_inv` (`MR E/ErasureProperties.v:105`). -/
theorem app_inv {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    {f a : Expr} {tb : LBTerm} (hns : ¬ ShortSpine σ (.app f a))
    (hnc : ∀ c us cv, f.getAppFn = .const c us → findDecl σ.decls c ≠ some (.ctorInfo cv))
    (hrl : ∀ c us (bs : List Expr) rv, f = mkAppN (.const c us) bs.toArray →
      findDecl σ.decls c = some (.recInfo rv) →
      rv.numParams + rv.numMotives + rv.numMinors + rv.numIndices + 1 ≤ bs.length)
    (h : Erases E B lps σ Γ Δ (.app f a) tb) :
    (tb = .box ∧ ErasableS E B lps Γ Δ (.app f a)) ∨
      ∃ tf ta, tb = .app tf ta ∧ Erases E B lps σ Γ Δ f tf ∧ Erases E B lps σ Γ Δ a ta := by
  generalize hx : Expr.app f a = x at h
  cases h with
  | app _ hf ha => cases hx; exact .inr ⟨_, _, rfl, hf, ha⟩
  | box hb => subst hx; exact .inl ⟨rfl, hb⟩
  | ctor hc =>
    obtain ⟨bs, -, rfl⟩ := SrcDefeq.spine_app hx.symm
    exact absurd hc (hnc _ _ _ (SrcDefeq.getAppFn_mkAppN_const _ _ _))
  | @cases c iv us iid _ _ _ maj maj' pre alts extra brs extra' hco hnr hss hid hpre halts hm hbrs
      hcf halt hlex hext =>
    rcases eq_nil_or_snoc extra with rfl | ⟨ex, y, rfl⟩
    · refine absurd (shortSpine_of hx (specialArity_casesOn hco) ?_) hns
      simp only [List.length_append, List.length_singleton, List.length_nil, hpre, halts,
        casesArity]
      omega
    obtain ⟨ex', y', rfl⟩ : ∃ ex' y', extra' = ex' ++ [y'] := by
      rcases eq_nil_or_snoc extra' with rfl | h
      · simp at hlex
      · exact h
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hlex
    rw [show pre ++ [maj] ++ alts ++ (ex ++ [y]) = (pre ++ [maj] ++ alts ++ ex) ++ [y] by
      simp] at hx
    obtain ⟨bs, hbs, rfl⟩ := SrcDefeq.spine_app hx.symm
    obtain ⟨rfl, h2⟩ := List.append_inj' hbs.symm rfl
    obtain rfl : y = a := by simpa using h2.symm
    obtain ⟨hext', hy⟩ := forall_snoc hlex hext
    exact .inr ⟨_, _, mkApps_snoc _ _ _,
      .cases hco hnr hss hid hpre halts hm hbrs hcf halt hlex hext', hy⟩
  | @casesReduced c iv cn cv _ _ _ alt alt' us maj pre extra extra' hco hfe hcs hcv hidx hpre ha
      hlex hext =>
    rcases eq_nil_or_snoc extra with rfl | ⟨ex, y, rfl⟩
    · refine absurd (shortSpine_of hx (specialArity_casesOn hco) ?_) hns
      simp only [List.length_append, List.length_singleton, List.length_nil, hpre, hcs,
        casesArity]
      omega
    obtain ⟨ex', y', rfl⟩ : ∃ ex' y', extra' = ex' ++ [y'] := by
      rcases eq_nil_or_snoc extra' with rfl | h
      · simp at hlex
      · exact h
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hlex
    rw [show pre ++ [maj] ++ [alt] ++ (ex ++ [y]) = (pre ++ [maj] ++ [alt] ++ ex) ++ [y] by
      simp] at hx
    obtain ⟨bs, hbs, rfl⟩ := SrcDefeq.spine_app hx.symm
    obtain ⟨rfl, h2⟩ := List.append_inj' hbs.symm rfl
    obtain rfl : y = a := by simpa using h2.symm
    obtain ⟨hext', hy⟩ := forall_snoc hlex hext
    refine .inr ⟨_, _, ?_, .casesReduced hco hfe hcs hcv hidx hpre ha hlex hext', hy⟩
    rw [← List.append_assoc, mkApps_snoc]
  | quotMk hcq hk ha hlex hext =>
    rename_i extra extra'
    rcases eq_nil_or_snoc extra with rfl | ⟨ex, y, rfl⟩
    · exact absurd (shortSpine_of (ar := 3) hx (by simp [specialArity, hcq, hk, quotEvalArity]) (by simp)) hns
    obtain ⟨ex', y', rfl⟩ : ∃ ex' y', extra' = ex' ++ [y'] := by
      rcases eq_nil_or_snoc extra' with rfl | h
      · simp at hlex
      · exact h
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hlex
    rw [← List.append_assoc] at hx
    obtain ⟨bs, hbs, rfl⟩ := SrcDefeq.spine_app hx.symm
    obtain ⟨rfl, h2⟩ := List.append_inj' hbs.symm rfl
    obtain rfl : y = a := by simpa using h2.symm
    obtain ⟨hext', hy⟩ := forall_snoc hlex hext
    exact .inr ⟨_, _, mkApps_snoc _ _ _, .quotMk hcq hk ha hlex hext', hy⟩
  | quotLift hcq hk hf hq hlex hext =>
    rename_i extra extra'
    rcases eq_nil_or_snoc extra with rfl | ⟨ex, y, rfl⟩
    · exact absurd (shortSpine_of (ar := 6) hx (by simp [specialArity, hcq, hk, quotEvalArity]) (by simp)) hns
    obtain ⟨ex', y', rfl⟩ : ∃ ex' y', extra' = ex' ++ [y'] := by
      rcases eq_nil_or_snoc extra' with rfl | h
      · simp at hlex
      · exact h
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hlex
    rw [← List.append_assoc] at hx
    obtain ⟨bs, hbs, rfl⟩ := SrcDefeq.spine_app hx.symm
    obtain ⟨rfl, h2⟩ := List.append_inj' hbs.symm rfl
    obtain rfl : y = a := by simpa using h2.symm
    obtain ⟨hext', hy⟩ := forall_snoc hlex hext
    refine .inr ⟨_, _, ?_, .quotLift hcq hk hf hq hlex hext', hy⟩
    rw [← List.cons_append, mkApps_snoc]
  | @recLet c rv us minors F _ _ _ maj maj' ps ms mins is extra mins' is' extra' hcr hF hps hms
      hmins his hlm hmin hli his' hmaj hlex hext =>
    rcases eq_nil_or_snoc extra with rfl | ⟨ex, y, rfl⟩
    · rw [List.append_nil] at hx
      obtain ⟨bs, hbs, rfl⟩ := SrcDefeq.spine_app hx.symm
      have := hrl c us bs rv rfl hcr
      have := congrArg List.length hbs
      simp only [List.length_append, List.length_singleton] at this
      omega
    obtain ⟨ex', y', rfl⟩ : ∃ ex' y', extra' = ex' ++ [y'] := by
      rcases eq_nil_or_snoc extra' with rfl | h
      · simp at hlex
      · exact h
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hlex
    rw [← List.append_assoc] at hx
    obtain ⟨bs, hbs, rfl⟩ := SrcDefeq.spine_app hx.symm
    obtain ⟨rfl, h2⟩ := List.append_inj' hbs.symm rfl
    obtain rfl : y = a := by simpa using h2.symm
    obtain ⟨hext', hy⟩ := forall_snoc hlex hext
    exact .inr ⟨_, _, mkApps_snoc _ _ _,
      .recLet hcr hF hps hms hmins his hlm hmin hli his' hmaj hlex hext', hy⟩
  | @recFix c rv us minors F _ _ _ maj maj' ps ms mins is extra ws is' extra' hcr hF hps hms
      hmins his hlw hmin hws hli his' hmaj hlex hext =>
    rcases eq_nil_or_snoc extra with rfl | ⟨ex, y, rfl⟩
    · rw [List.append_nil] at hx
      obtain ⟨bs, hbs, rfl⟩ := SrcDefeq.spine_app hx.symm
      have := hrl c us bs rv rfl hcr
      have := congrArg List.length hbs
      simp only [List.length_append, List.length_singleton] at this
      omega
    obtain ⟨ex', y', rfl⟩ : ∃ ex' y', extra' = ex' ++ [y'] := by
      rcases eq_nil_or_snoc extra' with rfl | h
      · simp at hlex
      · exact h
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hlex
    rw [← List.append_assoc] at hx
    obtain ⟨bs, hbs, rfl⟩ := SrcDefeq.spine_app hx.symm
    obtain ⟨rfl, h2⟩ := List.append_inj' hbs.symm rfl
    obtain rfl : y = a := by simpa using h2.symm
    obtain ⟨hext', hy⟩ := forall_snoc hlex hext
    refine .inr ⟨_, _, ?_, .recFix hcr hF hps hms hmins his hlw hmin hws hli his' hmaj hlex hext',
      hy⟩
    rw [← List.append_assoc]; exact mkApps_snoc _ _ _
  | eta heta =>
    obtain ⟨ar, har, hlt⟩ := etaSpine?_lt heta
    exact absurd (shortSpine_of hx har hlt.le) hns
  | bvar | fvar | lam | letE | const | proj | litZero | litSucc | mdata => cases hx

/-- An unfoldable constant is a definition of the evaluation environment that is neither remapped
nor a recognized `casesOn`. -/
theorem unfold?_spec {c : Name} {ci : ConstantInfo} {b : Expr} (h : σ.unfold? c = some (ci, b)) :
    findDecl σ.decls c = some ci ∧ σ.axiomatized ci = false ∧ σ.casesOn? c = none := by
  unfold EvalEnv.unfold? at h
  split at h
  · rename_i v hv
    split at h
    · cases h
    · rename_i hn
      cases h
      simp only [Bool.or_eq_true, Option.isSome_iff_ne_none, not_or, ne_eq, not_not] at hn
      exact ⟨hv, Bool.eq_false_iff.2 hn.1, hn.2⟩
  · cases h

/-- An erasure of an unfoldable constant is the λ□ constant or `□`. -/
theorem const_inv {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    {c : Name} {us : List Level} {ci : ConstantInfo} {b : Expr} {tb : LBTerm}
    (hu : σ.unfold? c = some (ci, b)) (h : Erases E B lps σ Γ Δ (.const c us) tb) :
    tb = .const (toKername c) ∨ (tb = .box ∧ ErasableS E B lps Γ Δ (.const c us)) := by
  obtain ⟨hfd, -, hco⟩ := unfold?_spec hu
  obtain ⟨d, hd⟩ := SrcDefeq.unfold?_defn hu
  generalize hx : Expr.const c us = x at h
  cases h with
  | const => cases hx; exact .inl rfl
  | box hb => subst hx; exact .inr ⟨rfl, hb⟩
  | ctor hc =>
    obtain ⟨-, rfl, -⟩ := SrcDefeq.spine_const hx.symm
    rw [hd] at hc; cases hc
  | cases hc | casesReduced hc =>
    obtain ⟨-, rfl, -⟩ := SrcDefeq.spine_const hx.symm
    rw [hco] at hc; cases hc
  | quotMk hc | quotLift hc | recLet hc | recFix hc =>
    obtain ⟨-, rfl, -⟩ := SrcDefeq.spine_const hx.symm
    rw [hd] at hc; cases hc
  | eta heta =>
    obtain ⟨-, rfl, -⟩ := SrcDefeq.spine_const hx.symm
    obtain ⟨ar, har, -⟩ := etaSpine?_lt heta
    rcases SrcDefeq.specialArity_some har with ⟨cv, hcv, -⟩ | ⟨iv, hiv⟩ | ⟨qv, hqv, -⟩
    · rw [hd] at hcv; cases hcv
    · rw [hco] at hiv; cases hiv
    · rw [hd] at hqv; cases hqv
  | bvar | fvar | lam | letE | app | proj | litZero | litSucc | mdata => cases hx

/-- The translation of a λ: its binder's and body's translations. -/
theorem trM_lam_inv {x : Name} {A b : Expr} {bi : BinderInfo}
    {V : Metalean.Expr ζ lps.length 0}
    (h : TrM E B lps .nil [] (.lam x A b bi) V) :
    ∃ A' b', V = .lam A' b' ∧ TrM E B lps .nil [] A A' ∧
      TrM E B lps (Metalean.Ctx.nil.snoc A') (MLCtx.pushLam [] none) b b' := by
  generalize hx : Expr.lam x A b bi = e at h
  cases h with
  | lam hA hb => cases hx; exact ⟨_, _, rfl, hA, hb⟩
  | special => exact absurd hx (CasesWhred.ne_mkAppN_const fun _ _ h => by cases h)
  | _ => cases hx

/-- Two typed translations of the same term are definitionally equal at the first one's type. -/
theorem trM_defeq (hE : EnvWF E) {e : Expr} {t₁ t₂ T₁ T₂ : Metalean.Expr ζ lps.length 0}
    (h₁ : TrM E B lps .nil [] e t₁) (h₂ : TrM E B lps .nil [] e t₂) (ht₁ : E[.nil] ⊢ t₁ : T₁)
    (ht₂ : E[.nil] ⊢ t₂ : T₂) : E[.nil] ⊢ t₁ ≡ t₂ : T₁ :=
  DCong.defeq₂ hE (h₁.dcong h₂ (LocCong.refl [])) SrcDefeq.nil_ok SrcDefeq.nil_ok
    (DCong.CtxConv.refl SrcDefeq.nil_ok) ⟨T₂, ht₂⟩ ht₁

/-- The erasure of a closed translated term is closed. -/
theorem closed0 {e : Expr} {t : Metalean.Expr ζ lps.length 0} {tb : LBTerm}
    (he : TrM E B lps .nil [] e t) (h : Erases E B lps σ .nil [] e tb) : closedn 0 tb = true := by
  simpa using Erases.closed he h

/-- An erasure to `□` of a spine headed by a projection is by `Erases.box`. -/
theorem box_of_projHead {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    {e e₀ : Expr} {S : Name} {i : Nat} (hfn : e.getAppFn = .proj S i e₀)
    (h : Erases E B lps σ Γ Δ e .box) : ErasableS E B lps Γ Δ e := by
  generalize hx : LBTerm.box = x at h
  cases h with
  | box hb => exact hb
  | ctor | cases | casesReduced | eta | quotMk | quotLift | recLet | recFix =>
    rw [SrcDefeq.getAppFn_mkAppN_const] at hfn; cases hfn
  | bvar | fvar | lam | letE | app | const | proj | litZero | litSucc => cases hx
  | mdata => simp [Expr.getAppFn] at hfn

/-- The image of the head of a saturating spine of an inductive type with one argument less. -/
theorem satTr_ind_init {n : Nat} {ι : Metalean.IndSig} {η : Metalean.Head ζ (.inductive ι)}
    {s : Fin ι.nsorts} {us : List Level} {bs : List (Metalean.Expr ζ lps.length n)}
    {x t : Metalean.Expr ζ lps.length n} (h : SatTr E lps (.ind η s) us (bs ++ [x]) t) :
    ∃ t₁, SatTr E lps (.ind η s) us bs t₁ := by
  generalize hl : bs ++ [x] = l at h
  cases h with
  | indSat ps is rest hls =>
    rcases eq_nil_or_snoc rest with rfl | ⟨r, y, rfl⟩
    · have := congrArg List.length hl
      simp only [List.length_append, List.length_singleton, List.length_ofFn, List.length_nil,
        Nat.add_zero] at this
      exact ⟨_, .indEta hls (by omega)⟩
    · rw [← List.append_assoc] at hl
      obtain ⟨rfl, -⟩ := List.append_inj' hl rfl
      exact ⟨_, .indSat ps is r hls⟩
  | indEta hls hlt =>
    subst hl
    exact ⟨_, .indEta hls (by simp at hlt; omega)⟩

end SimCases

open SimCases

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P : List ConstantInfo}
  {σ : EvalEnv} {lps : List Name} {lenv : GlobalDeclarations}

/-- An alternative erased under no field binder is an erasure of the alternative. Reference: the
branches of `MR E/Extract.v:111 erases_tCase`. -/
theorem ErasesAlt.zero_inv {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
    {Δ : MLCtx ζ lps.length n} {e : Expr} {ns : List BinderName} {t : LBTerm}
    (h : ErasesAlt E B lps σ Γ Δ 0 e (ns, t)) : ns = [] ∧ Erases E B lps σ Γ Δ e t := by
  generalize hk : 0 = k at h
  generalize hbr : (ns, t) = br at h
  cases h with
  | done h => cases hbr; exact ⟨rfl, h⟩
  | lam | intro => cases hk

/-- An alternative erased under `k + 1` field binders is a λ whose body is erased under the
remaining `k` (`ErasesAlt.lam`), or a typed term applied to a new bound variable, erased under the
remaining `k` (`ErasesAlt.intro`, the η-introduction of `lambdaOrIntroToArity`,
`LeanToLambdaBox/Erasure.lean:592`). The step of `iota_red` (`MR E/EGlobalEnv.v:281`) on the first
field: `ErasesAlt.inst` on the body, or β on the η-introduced application. Reference: the branches
of `MR E/Extract.v:111 erases_tCase`. -/
theorem ErasesAlt.succ_inv {n k : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
    {Δ : MLCtx ζ lps.length n} {e : Expr} {ns : List BinderName} {t : LBTerm}
    (h : ErasesAlt E B lps σ Γ Δ (k + 1) e (ns, t)) :
    (∃ x A b bi A' ns', e = .lam x A b bi ∧ ns = binderNameOf x :: ns' ∧
      TrM E B lps Γ Δ A A' ∧ E[Γ] ⊢ A' typ ∧
      ErasesAlt E B lps σ (Γ.snoc A') (Δ.pushLam none) k b (ns', t)) ∨
    (∃ e' A' B'' nm ns', ns = nm :: ns' ∧ TrM E B lps Γ Δ e e' ∧
      E[Γ] ⊢ e' : .forallE A' B'' ∧
      ErasesAlt E B lps σ (Γ.snoc A') (Δ.pushLam none) k
        (.app (e.liftLooseBVars' 0 1) (.bvar 0)) (ns', t)) := by
  generalize hk : k + 1 = k' at h
  generalize hbr : (ns, t) = br at h
  cases h with
  | done => cases hk
  | lam hA hAt hb =>
    cases hk; cases hbr
    exact .inl ⟨_, _, _, _, _, _, rfl, rfl, hA, hAt, hb⟩
  | intro he het hb =>
    cases hk; cases hbr
    exact .inr ⟨_, _, _, _, _, rfl, he, het, hb⟩

/-- The uniform case of `erases_correct`, an erasure to `□`: the value of an erasable term is
erasable (`ErasableS.eval`), so it erases to `□`, which λ□ evaluates to itself. Reference: the
`erases_box` cases of `erases_correct` (`MR E/ErasureCorrectness.v:58-1232`), through
`Is_type_eval` (`MR E/EArities.v:570`). -/
theorem erases_correct_box (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv σ.decls P)
    {e v : Expr} {t T : Metalean.Expr ζ lps.length 0} (he : TrM E B lps .nil [] e t)
    (ht : E[.nil] ⊢ t : T) (hb : ErasableS E B lps .nil [] e) (hev : SrcEval σ e v) :
    ∃ vb, Erases E B lps σ .nil [] v vb ∧ LBEval defaultFlags lenv .box vb :=
  ⟨.box, .box (ErasableS.eval henv hE hsub he ht hev hb), .atom rfl⟩

/-- The `mdata` case of `erases_correct`: metadata is transparent in the translation, the
relation and the source semantics. Reference: none (Lean syntax). -/
theorem erases_correct_mdata (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv σ.decls P)
    {d : MData} {e v : Expr} (hev : SrcEval σ e v) (ih : ErasesSim E B lps σ lenv e v) :
    ErasesSim E B lps σ lenv (.mdata d e) v := by
  intro t tb he ⟨T, ht⟩ her hdeps
  have he' : TrM E B lps .nil [] e t := by
    generalize hx : Expr.mdata d e = x at he
    cases he with
    | mdata h => cases hx; exact h
    | special => exact absurd hx (CasesWhred.ne_mkAppN_const fun _ _ h => by cases h)
    | _ => cases hx
  generalize hx : Expr.mdata d e = x at her
  cases her with
  | mdata h => cases hx; exact ih he' ⟨T, ht⟩ h hdeps
  | box hb => subst hx; exact erases_correct_box henv hE hsub he ht hb (.mdata hev)
  | ctor | cases | casesReduced | eta | quotMk | quotLift | recLet | recFix =>
    exact absurd hx (CasesWhred.ne_mkAppN_const fun _ _ h => by cases h)
  | bvar | fvar | lam | letE | app | const | proj | litZero | litSucc => cases hx

/-- The `atom` case of `erases_correct`: a λ, sort or Π erases to a λ□ λ or to `□`, both λ□
values. Reference: the `eval_atom` case of `erases_correct` (`MR E/ErasureCorrectness.v:1179`,
`eval_atom` at `:1218`). -/
theorem erases_correct_atom {e : Expr} (ha : SrcAtom e) : ErasesSim E B lps σ lenv e e := by
  intro t tb _ _ her _
  refine ⟨tb, her, .atom ?_⟩
  have hns : ∀ {c : Name} {us : List Level} {as : List Expr},
      e ≠ mkAppN (.const c us) as.toArray := by
    intro c us as h
    have := congrArg Expr.getAppFn h
    rw [SrcDefeq.getAppFn_mkAppN_const] at this
    cases e <;> simp [SrcAtom, Expr.getAppFn] at ha this
  generalize hx : e = x at her
  cases her with
  | lam | box => rfl
  | ctor | cases | casesReduced | eta | quotMk | quotLift | recLet | recFix => exact absurd hx hns
  | bvar | fvar | letE | app | const | proj | litZero | litSucc | mdata =>
    subst hx; simp [SrcAtom] at ha

/-- The `constAtom` case of `erases_correct`: an atom constant erases only to `□` (it is neither
special nor a λ□ constant), which λ□ evaluates to itself. Reference: the `eval_atom` case of
`erases_correct` on `tInd` (`MR E/ErasureCorrectness.v:1207`, `eval_atom` at `:1218`), which
erases only by `erases_box` (`MR E/Extract.v:140`); DV-11. -/
theorem erases_correct_constAtom {c : Name} {us : List Level} (ha : σ.isAtom c = true) :
    ErasesSim E B lps σ lenv (.const c us) (.const c us) := by
  intro t tb _ _ her _
  refine ⟨tb, her, ?_⟩
  obtain ⟨c', us', hfn, hat⟩ := RelInst.atomSpine_head (AtomSpine.const (us := us) ha)
  have hns : ¬ ((∃ cv, findDecl σ.decls c = some (.ctorInfo cv)) ∨
      (∃ iv, σ.casesOn? c = some iv) ∨ ∃ qv, findDecl σ.decls c = some (.quotInfo qv)) := by
    unfold EvalEnv.isAtom at ha
    rintro (⟨cv, hc⟩ | ⟨iv, hiv⟩ | ⟨qv, hc⟩)
    · rw [hc] at ha
      simp [OwnRules] at ha
    · split at ha
      · rw [hiv] at ha
        simp at ha
      · cases ha
    · rw [hc] at ha
      simp [OwnRules] at ha
  generalize hx : Expr.const c us = x at her
  cases her with
  | box => exact .atom rfl
  | const hna => cases hx; rw [ha] at hna; cases hna
  | ctor hc =>
    obtain ⟨-, rfl, -⟩ := SrcDefeq.spine_const hx.symm
    exact absurd (.inl ⟨_, hc⟩) hns
  | cases hc | casesReduced hc =>
    obtain ⟨-, rfl, -⟩ := SrcDefeq.spine_const hx.symm
    exact absurd (.inr (.inl ⟨_, hc⟩)) hns
  | quotMk hc | quotLift hc =>
    obtain ⟨-, rfl, -⟩ := SrcDefeq.spine_const hx.symm
    exact absurd (.inr (.inr ⟨_, hc⟩)) hns
  | recLet hc | recFix hc =>
    obtain ⟨-, rfl, -⟩ := SrcDefeq.spine_const hx.symm
    unfold EvalEnv.isAtom at ha
    rw [hc] at ha
    simp [OwnRules] at ha
  | eta heta =>
    obtain ⟨-, rfl, -⟩ := SrcDefeq.spine_const hx.symm
    obtain ⟨ar, har, -⟩ := etaSpine?_lt heta
    rcases SrcDefeq.specialArity_some har with ⟨cv, hcv, -⟩ | ⟨iv, hiv⟩ | ⟨qv, hqv, -⟩
    · exact absurd (.inl ⟨_, hcv⟩) hns
    · exact absurd (.inr (.inl ⟨_, hiv⟩)) hns
    · exact absurd (.inr (.inr ⟨_, hqv⟩)) hns
  | bvar | fvar | lam | letE | app | proj | litZero | litSucc | mdata => cases hx

/-- The `beta` case of `erases_correct`. The head is no saturating spine (its value would be a
spine, not a λ), so the application's erasure is `□` or an application of erasures
(`SimCases.app_inv`). The head's erasure evaluates to an erasure of the λ: a λ□ λ, whose body
with the argument's value substituted (`Erases.inst`) erases the source's substituted body, or
`□`, and then the substituted body is erasable (`IsErasable.lam_inv`, `IsErasable.inst`) and so is
the value. Reference: the `eval_beta` case of `erases_correct` (`MR E/ErasureCorrectness.v:62`);
Let. Thm 13 (β). -/
theorem erases_correct_beta (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv σ.decls P)
    {f a a' b v A : Expr} {x : Name} {bi : BinderInfo} (hns : ¬ ShortSpine σ (.app f a))
    (hf : SrcEval σ f (.lam x A b bi)) (ha : SrcEval σ a a')
    (hb : SrcEval σ (b.instantiate1' a') v)
    (ihf : ErasesSim E B lps σ lenv f (.lam x A b bi)) (iha : ErasesSim E B lps σ lenv a a')
    (ihb : ErasesSim E B lps σ lenv (b.instantiate1' a') v) :
    ErasesSim E B lps σ lenv (.app f a) v := by
  intro t tb he ⟨T, ht⟩ her hdeps
  have hok := SrcDefeq.nil_ok (E := E) (lps := lps)
  have hord := henv.metaOrderOK
  have hev : SrcEval σ (.app f a) v := .beta hns hf ha hb
  have hspine := (SrcDefeq.sound_of (lps := lps) henv hE hsub
    (SrcProof.proofSound henv hE hsub) hf).2
  have hnq : ∀ c us (bs : List Expr) (bb : MBinding ζ), f = mkAppN (.const c us) bs.toArray →
      B c = some bb → bb.isSpecial = true → (∀ η k, bb ≠ .quot η k) →
      (∀ (ι : Metalean.IndSig) (η : Metalean.Head ζ (.inductive ι)) (s : Fin ι.nsorts) os,
        bb ≠ .recr η s os) → False := by
    intro c us bs bb hfe hbb hs hq hr
    subst hfe
    obtain ⟨-, vs, hv, -⟩ := hspine c us bs bb rfl hbb hs hq hr (SrcDefeq.spine_cond hns)
    have := congrArg Expr.getAppFn hv
    rw [SrcDefeq.getAppFn_mkAppN_const] at this
    cases this
  have hnc : ∀ c us cv, f.getAppFn = .const c us → findDecl σ.decls c ≠ some (.ctorInfo cv) := by
    intro c us cv hfn hc
    obtain ⟨ι, η, s, k, o, hB, -⟩ := henv.lookup_ctor (SrcDefeq.findDecl_sub hsub hc)
    obtain ⟨bs, rfl⟩ := eq_mkAppN_of_getAppFn hfn
    exact hnq c us bs _ rfl hB rfl (fun _ _ h => by cases h) fun _ _ _ _ h => by cases h
  rcases app_inv hns hnc (fun _ _ _ _ hfe hrv => rec_spine_len hf hfe hrv) her with
    ⟨rfl, hbx⟩ | ⟨tf, ta, rfl, herf, hera⟩
  · exact erases_correct_box henv hE hsub he ht hbx hev
  obtain ⟨f₀, a₀, hf₀, ha₀, rfl, ⟨F, hF⟩, ⟨A₁, hA₁⟩⟩ : ∃ f₀ a₀, TrM E B lps .nil [] f f₀ ∧
      TrM E B lps .nil [] a a₀ ∧ t = .app f₀ a₀ ∧ (∃ F, E[.nil] ⊢ f₀ : F) ∧
      ∃ A, E[.nil] ⊢ a₀ : A := by
    by_cases hsp : SpecialHead B f
    · obtain ⟨c, us, bb, hfn, hb, hs⟩ := hsp
      obtain ⟨bs, rfl⟩ := eq_mkAppN_of_getAppFn hfn
      by_cases hq : ∃ η k, bb = .quot η k
      · obtain ⟨η, k, rfl⟩ := hq
        exact SrcDefeq.quot_app_tr henv hsub hb hf hns he ht
      · by_cases hr : ∃ (ι : Metalean.IndSig) (η : Metalean.Head ζ (.inductive ι))
            (s : Fin ι.nsorts) (os : List (List (List Nat))), bb = .recr η s os
        · obtain ⟨ι, η, s, os, rfl⟩ := hr
          exact SrcDefeq.rec_app_tr henv hsub hb hf he ht
        · exact (hnq c us bs bb rfl hb hs (fun η k h => hq ⟨η, k, h⟩)
            fun ι η s os h => hr ⟨ι, η, s, os, h⟩).elim
    · exact TrM.wf_app hE hok hsp he ht
  cases hdeps with
  | app hdf hda =>
  obtain ⟨vf, hvf, hevf⟩ := ihf hf₀ ⟨F, hF⟩ herf hdf
  obtain ⟨va, hva, heva⟩ := iha ha₀ ⟨A₁, hA₁⟩ hera hda
  -- the typed translations of the λ and of the argument's value
  obtain ⟨tl, htl, hdl⟩ := SrcEval.defeq henv hE hsub hf₀ hF hf
  obtain ⟨ta', hta', hda'⟩ := SrcEval.defeq henv hE hsub ha₀ hA₁ ha
  obtain ⟨A₀, b₀, rfl, hA₀, hb₀⟩ := trM_lam_inv htl
  have h1 : E[.nil] ⊢ .app f₀ a₀ ≡ .app (.lam A₀ b₀) ta' : T :=
    DCong.defeq hE not_false (.app (.leaf hdl) (.leaf hda')) hok (DCong.CtxConv.refl hok) ht
  obtain ⟨X, Y, hl, hta'', -⟩ := h1.right.app_inv
  obtain ⟨T₀, hb₀T, hπ⟩ := hl.lam_inv hok
  have htaA : E[.nil] ⊢ ta' : A₀ := (TypeEq.forallE_inj hE hok hπ).1.conv hta''
  obtain ⟨u, hA₀u⟩ := htaA.regular
  obtain ⟨tb', htb', hdb'⟩ := TrM.inst hE hok hord hb₀ hta' htaA hb₀T
  have hval := SrcEval.value ha
  generalize hlv : Expr.lam x A b bi = lv at hvf
  cases hvf with
  | lam hA'' hAt hbody =>
    cases hlv
    obtain ⟨l, hl''⟩ := hAt
    have hAA : E[.nil] ⊢ A₀ ≡ _ : .sort u := trM_defeq hE hA₀ hA'' hA₀u hl''
    have hb₀T'' := Defeq.snocConv hAA hb₀T
    have hokA : E[Metalean.Ctx.nil.snoc _] ⊢ ok := .snoc hok ⟨l, hl''⟩
    have htb'' := InstPre.PreTr.recover hord (InstPre.PreTr.ofTrM hb₀) (InstPre.Thin.id _) hokA
      ⟨T₀, by rw [Metalean.Expr.rename_id]; exact hb₀T''⟩
    have hsubst := Erases.inst henv hE hok hsub hval hbody htb'' hb₀T'' hva hta'
      (Defeq.defeqDF hAA htaA) (closed0 hta' hva)
    have hdl' := ErasesDeps.eval hdf hevf
    cases hdl' with
    | lambda hdb =>
    obtain ⟨res, hres, hevres⟩ := ihb htb' ⟨_, hdb'.left⟩ hsubst
      (ErasesDeps.csubst (ErasesDeps.eval hda heva) hdb)
    exact ⟨res, hres, .beta hevf heva hevres⟩
  | box hbx =>
    subst hlv
    obtain ⟨t₁, htr₁, U, ht₁, hU⟩ := hbx
    have hlam : IsErasable E .nil (.lam A₀ b₀) :=
      RelInst.IsErasable.of_defeq (trM_defeq hE htr₁ htl ht₁ hl) hU
    obtain ⟨W, hW, hWe⟩ := IsErasable.inst hE htaA (IsErasable.lam_inv hE hok hlam)
    have hEb : IsErasable E .nil tb' :=
      RelInst.IsErasable.of_defeq (Defeq.retype hE hok hdb'.symm hW) hWe
    exact ⟨.box, .box (ErasableS.eval henv hE hsub htb' hdb'.left hb ⟨tb', htb', hEb⟩),
      .box hevf heva⟩
  | ctor | cases | casesReduced | eta | quotMk | quotLift | recLet | recFix =>
    exact absurd hlv (CasesWhred.ne_mkAppN_const fun _ _ h => by cases h)
  | bvar | fvar | letE | app | const | proj | litZero | litSucc | mdata => cases hlv

/-- Substituting a typed source value for a `let`-bound local whose denotation is definitionally
equal to the value's translation (the local of the erasure denotes the translation of the `let`
value before evaluation). -/
theorem SimCases.inst_let (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv σ.decls P)
    {val b : Expr} {b' val' : LBTerm} {v₀ tv b₀ T₀ U : Metalean.Expr ζ lps.length 0}
    (hval : SrcValue σ val)
    (hb : Erases E B lps σ .nil [(none, .vlet v₀)] b b')
    (htb : TrM E B lps .nil [(none, .vlet tv)] b b₀) (hbU : E[.nil] ⊢ b₀ : U)
    (hv₀ : E[.nil] ⊢ v₀ ≡ tv : T₀) (htv : TrM E B lps .nil [] val tv)
    (hv : Erases E B lps σ .nil [] val val') :
    Erases E B lps σ .nil [] (b.instantiate1' val) (csubst val' 0 b') := by
  have hok := SrcDefeq.nil_ok (E := E) (lps := lps)
  have hord := henv.metaOrderOK
  have hty : ∀ c ci, findDecl σ.decls c = some ci → AbsFV.LBV 0 ci.type :=
    fun c ci h => (AbsFV.closed_types henv hsub c ci h).1
  have hcg : InstPre.Cg E (v₀.subst Metalean.Subst.id) tv := by
    rw [Metalean.Expr.subst_id]
    intro Γ₁ Γ₂
    cases Γ₁
    exact .leaf hv₀
  have W : InstPre.MLCtx.InstA E B lps val 0 Metalean.Subst.id [(none, .vlet v₀)] [] := by
    constructor
    · intro i t ht
      cases i with
      | zero =>
        simp only [MLCtx.findB, MLDecl.denote, Option.some.injEq] at ht
        subst ht
        refine ⟨by omega, fun _ => ⟨tv, ?_, hcg⟩, by omega⟩
        rw [liftLooseBVars'_zero]; exact InstPre.PreTr.ofTrM htv
      | succ i => simp [MLCtx.findB] at ht
    · intro x t ht
      simp [MLCtx.findF] at ht
  have Ea : Erases E B lps σ .nil [] (val.liftLooseBVars' 0 0) val' := by
    rw [liftLooseBVars'_zero]; exact hv
  refine (RelInst.Erases.instG hE hord hty (closed0 htv hv)).1 _ _ _ _ _ hb _ _ _ 0 _ hok
    (Metalean.SubstWF.id hok) W Ea fun hs => ?_
  have hn := RelInst.node_of_value henv hsub hval hs htv
  have hhb : RelInst.HB E .nil v₀ := RelInst.HB.of_defeq_node hv₀ hn
  have hhb' : RelInst.HB E .nil tv := RelInst.HB.of_node hn
  refine ⟨hok, ?_, _, by simp [MLCtx.findB, MLDecl.denote], hhb⟩
  exact RelInst.PreTr.noHead hE hord (InstPre.PreTr.ofTrM htb) (ρ := Metalean.Ren.id)
    rfl hok (by rw [Metalean.Expr.rename_id]; exact hhb')
    ⟨_, by rw [Metalean.Expr.rename_id]; exact hbU⟩

/-- The `zeta` case of `erases_correct`: the `let` value's erasure evaluates to an erasure of its
value, which substituted into the erased body (`SimCases.inst_let`) erases the source's
substituted body. Reference: the `eval_zeta` case of `erases_correct`
(`MR E/ErasureCorrectness.v:110`); Let. Thm 13 (ζ). -/
theorem erases_correct_zeta (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv σ.decls P)
    {x : Name} {Ty val val' b v : Expr} {nd : Bool} (hv : SrcEval σ val val')
    (hb : SrcEval σ (b.instantiate1' val') v) (ihv : ErasesSim E B lps σ lenv val val')
    (ihb : ErasesSim E B lps σ lenv (b.instantiate1' val') v) :
    ErasesSim E B lps σ lenv (.letE x Ty val b nd) v := by
  intro t tb he ⟨T, ht⟩ her hdeps
  have hok := SrcDefeq.nil_ok (E := E) (lps := lps)
  have hord := henv.metaOrderOK
  have hev : SrcEval σ (.letE x Ty val b nd) v := .zeta hv hb
  -- the translation of the substituted body (as `SrcDefeq.case_zeta`)
  obtain ⟨tv, htv, ⟨V, htvV⟩, tb₁, htb₁, hTb₁, b₂, hb₂, ⟨U₂, hb₂T⟩⟩ :
      ∃ tv, TrM E B lps .nil [] val' tv ∧ (∃ V, E[.nil] ⊢ tv : V) ∧
        ∃ tb₁, TrM E B lps .nil [] (b.instantiate1' val') tb₁ ∧
        (∃ U, E[.nil] ⊢ tb₁ : U) ∧ ∃ b₂, TrM E B lps .nil [(none, .vlet tv)] b b₂ ∧
          ∃ U, E[.nil] ⊢ b₂ : U := by
    generalize hx : Expr.letE x Ty val b nd = y at he
    cases he with
    | letE _ hv' hb' =>
      cases hx
      obtain ⟨r, -, hvT, hbr, -⟩ := ht.letE_inv hok
      rw [Metalean.Expr.inst_wk] at hbr
      obtain ⟨tv, htv, hdv⟩ := SrcEval.defeq henv hE hsub hv' hvT hv
      have hL := SrcDefeq.LocRel.cons (Γ₁ := .nil) (Γ₂ := .nil) SrcDefeq.LocRel.nil (.leaf hdv)
      obtain ⟨b₂, hb₂, hcb⟩ := SrcDefeq.PreTr.replace (InstPre.PreTr.ofTrM hb') hL
      have hd1 := DCong.defeq hE not_false hcb hok (DCong.CtxConv.refl hok) hbr
      have hb₂' := InstPre.PreTr.recover hord hb₂ (InstPre.Thin.id _) hok
        ⟨r, by rw [Metalean.Expr.rename_id]; exact hd1.right⟩
      obtain ⟨tb₁, htb₁, hdb⟩ := TrM.inst_let hE hok hord hb₂' htv hd1.right
      exact ⟨tv, htv, ⟨_, hdv.right⟩, tb₁, htb₁, ⟨_, hdb.left⟩, b₂, hb₂', ⟨_, hd1.right⟩⟩
    | special => exact absurd hx (CasesWhred.ne_mkAppN_const fun _ _ h => by cases h)
    | _ => cases hx
  generalize hx : Expr.letE x Ty val b nd = y at her
  cases her with
  | box hbx => subst hx; exact erases_correct_box henv hE hsub he ht hbx hev
  | letE hv₀ hv₀T herv herb =>
    cases hx
    obtain ⟨T₀, hT₀⟩ := hv₀T
    cases hdeps with
    | letIn hdv hdb =>
    obtain ⟨vv, hvv, hevv⟩ := ihv hv₀ ⟨T₀, hT₀⟩ herv hdv
    obtain ⟨tv', htv', hdv'⟩ := SrcEval.defeq henv hE hsub hv₀ hT₀ hv
    have hv₀tv :=
      SrcDefeq.dtrans hE hdv' (trM_defeq hE htv' htv hdv'.right htvV)
    have hsubst := SimCases.inst_let henv hE hsub (SrcEval.value hv) herb hb₂ hb₂T hv₀tv htv hvv
    obtain ⟨res, hres, hevres⟩ := ihb htb₁ hTb₁ hsubst
      (ErasesDeps.csubst (ErasesDeps.eval hdv hevv) hdb)
    exact ⟨res, hres, .zeta hevv hevres⟩
  | ctor | cases | casesReduced | eta | quotMk | quotLift | recLet | recFix =>
    exact absurd hx (CasesWhred.ne_mkAppN_const fun _ _ h => by cases h)
  | bvar | fvar | lam | app | const | proj | litZero | litSucc | mdata => cases hx

/-- The `delta` case of `erases_correct`: an unfoldable constant erases to `□` or to its λ□
constant; the λ□ declaration found at its kername is its own (`KernameInj`), whose body erases
the constant's value (`ErasesDecl`), at the occurrence's levels too (`Erases.instLevels`).
Reference: the `eval_delta` case of `erases_correct` (`MR E/ErasureCorrectness.v:152`); Let.
Thm 13 (δ). -/
theorem erases_correct_delta (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv σ.decls P)
    (hinj : KernameInj σ.decls) {c : Name} {us : List Level} {ci : ConstantInfo} {body v : Expr}
    (hu : σ.unfold? c = some (ci, body))
    (hb : SrcEval σ (Pure.instLevels ci.levelParams us body) v)
    (ih : ErasesSim E B lps σ lenv (Pure.instLevels ci.levelParams us body) v) :
    ErasesSim E B lps σ lenv (.const c us) v := by
  intro t tb he ⟨T, ht⟩ her hdeps
  have hok := SrcDefeq.nil_ok (E := E) (lps := lps)
  have hev : SrcEval σ (.const c us) v := .delta hu hb
  obtain ⟨b', hb', hred⟩ := ProgEnv.unfold henv hsub hu he
  have hd := WHRed.defeq hE hred hok ht
  obtain ⟨hfd, hax, -⟩ := unfold?_spec hu
  obtain ⟨dv, η, ls, rfl, rfl, -, hls, hval, -⟩ := henv.unfold_delta hsub hu he
  rcases const_inv hu her with rfl | ⟨rfl, hbx⟩
  · generalize hk : toKername c = kn at hdeps
    cases hdeps with
    | @const c' ci' cb hfd₂ hl hdecl hbody =>
      cases hinj c c' (by rw [hfd]; rfl) (by rw [hfd₂]; rfl) hk
      rw [hfd] at hfd₂
      cases hfd₂
      simp only [ErasesDecl, ConstantInfo.value?] at hdecl
      rcases hdecl with ⟨hax', -⟩ | ⟨-, b'', hcb, herb⟩
      · rw [hax] at hax'; cases hax'
      · obtain ⟨res, hres, hevres⟩ := ih hb' ⟨_, hd.right⟩
          (Erases.instLevels henv hsub hls hval herb) (hbody b'' hcb)
        exact ⟨res, hres, .delta hl hcb hevres⟩
  · exact erases_correct_box henv hE hsub he ht hbx hev

/-- The `appCong` case of `erases_correct`. The head's value is an atom spine or a `PropProj`
spine (`SrcEval.value`, `¬ BlocksCong`), whose erasure evaluates to `□`
(`Erases.atomSpine_box`, `Erases.propProj_box`), so the application evaluates to `□`; the value
is erasable: an atom spine by `ErasableS.atom`, a `PropProj` spine because its head's erasure `□`
is by `Erases.box` (`IsErasable.app`). When the head is a spine of an inductive type whose
application saturates it, the head's image is the inductive's η-term applied to arguments that the
application's image has inside the inductive node; its typing is the premise `hsat` (subject
expansion of the η-term's β-reduction). Reference: the `eval_app_cong` case of `erases_correct`
(`MR E/ErasureCorrectness.v:1127`, `eval_app_cong` at `:1144`). -/
theorem erases_correct_appCong (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv σ.decls P)
    (hsat : ∀ {ι : Metalean.IndSig} (η : Metalean.Head ζ (.inductive ι)) (s : Fin ι.nsorts)
      {us : List Level} {as₁ as₂ : List (Metalean.Expr ζ lps.length 0)}
      {t₁ t T : Metalean.Expr ζ lps.length 0},
      SatTr E lps (.ind η s) us as₁ t₁ → SatTr E lps (.ind η s) us (as₁ ++ as₂) t →
      E[.nil] ⊢ t : T → ∃ T₁, E[.nil] ⊢ t₁ : T₁)
    {f a f' a' : Expr} (hns : ¬ ShortSpine σ (.app f a)) (hf : SrcEval σ f f')
    (hnb : ¬ BlocksCong σ f') (ha : SrcEval σ a a')
    (ihf : ErasesSim E B lps σ lenv f f') (iha : ErasesSim E B lps σ lenv a a') :
    ErasesSim E B lps σ lenv (.app f a) (.app f' a') := by
  intro t tb he ⟨T, ht⟩ her hdeps
  have hok := SrcDefeq.nil_ok (E := E) (lps := lps)
  have hev : SrcEval σ (.app f a) (.app f' a') := .appCong hns hf hnb ha
  have hspine := (SrcDefeq.sound_of (lps := lps) henv hE hsub
    (SrcProof.proofSound henv hE hsub) hf).2
  have hfv : AtomSpine σ f' ∨ PropProj σ f' := by
    cases SrcEval.value hf with
    | spine h => exact .inl h
    | propProj h => exact .inr h
    | ctor hc _ =>
      exact absurd (SrcDefeq.blocksCong_ctor (SrcDefeq.getAppFn_mkAppN_const _ _ _) hc) hnb
    | quotMk hc _ _ =>
      exact absurd (SrcDefeq.blocksCong_quot (SrcDefeq.getAppFn_mkAppN_const _ _ _) hc) hnb
    | lam | sort | forallE | lit => exact absurd trivial hnb
  have hnc : ∀ c us cv, f.getAppFn = .const c us → findDecl σ.decls c ≠ some (.ctorInfo cv) := by
    intro c us cv hfn hc
    obtain ⟨bs, rfl⟩ := eq_mkAppN_of_getAppFn hfn
    obtain ⟨ι, η, s, k, o, hB, -⟩ := henv.lookup_ctor (SrcDefeq.findDecl_sub hsub hc)
    obtain ⟨-, vs, rfl, -⟩ := hspine c us bs _ rfl hB rfl (fun _ _ h => by cases h)
      (fun _ _ _ _ h => by cases h) (SrcDefeq.spine_cond hns)
    exact hnb (SrcDefeq.blocksCong_ctor (SrcDefeq.getAppFn_mkAppN_const _ _ _) hc)
  obtain ⟨f₀, a₀, hf₀, ha₀, ⟨F, hF⟩, ⟨A₁, hA₁⟩⟩ : ∃ f₀ a₀, TrM E B lps .nil [] f f₀ ∧
      TrM E B lps .nil [] a a₀ ∧ (∃ F, E[.nil] ⊢ f₀ : F) ∧ ∃ A, E[.nil] ⊢ a₀ : A := by
    by_cases hsp : SpecialHead B f
    · obtain ⟨c, us, bb, hfn, hbb, hs⟩ := hsp
      obtain ⟨bs, rfl⟩ := eq_mkAppN_of_getAppFn hfn
      by_cases hq : ∃ η k, bb = .quot η k
      · obtain ⟨η, k, rfl⟩ := hq
        obtain ⟨f₀, a₀, hf₀, ha₀, -, hF, hA⟩ := SrcDefeq.quot_app_tr henv hsub hbb hf hns he ht
        exact ⟨f₀, a₀, hf₀, ha₀, hF, hA⟩
      by_cases hr : ∃ (ι : Metalean.IndSig) (η : Metalean.Head ζ (.inductive ι))
          (s : Fin ι.nsorts) (os : List (List (List Nat))), bb = .recr η s os
      · obtain ⟨ι, η, s, os, rfl⟩ := hr
        obtain ⟨f₀, a₀, hf₀, ha₀, -, hF, hA⟩ := SrcDefeq.rec_app_tr henv hsub hbb hf he ht
        exact ⟨f₀, a₀, hf₀, ha₀, hF, hA⟩
      obtain ⟨hk, vs, rfl, -⟩ := hspine c us bs bb rfl hbb hs (fun η k h => hq ⟨η, k, h⟩)
        (fun ι η s os h => hr ⟨ι, η, s, os, h⟩) (SrcDefeq.spine_cond hns)
      rcases hk with ⟨iv, hiv⟩ | ⟨cv, hcv⟩
      · obtain ⟨ι, η, s, hB, -⟩ := henv.lookup_ind (SrcDefeq.findDecl_sub hsub hiv)
        rw [← SrcDefeq.mkAppN_snoc] at he
        obtain ⟨as', hlen, hargs, hsat'⟩ := TrM.special_inv hB rfl he
        obtain ⟨bs', a₀, rfl⟩ : ∃ bs' a₀, as' = bs' ++ [a₀] := by
          rcases eq_nil_or_snoc as' with rfl | h
          · simp at hlen
          · exact h
        simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hlen
        obtain ⟨hargs', ha₀⟩ := forall_snoc hlen hargs
        obtain ⟨t₁, hsat₁⟩ := satTr_ind_init hsat'
        obtain ⟨T₁, ht₁⟩ := hsat η s hsat₁ hsat' ht
        exact ⟨t₁, a₀, .special hB rfl hlen hargs' hsat₁, ha₀, ⟨T₁, ht₁⟩,
          SrcDefeq.satTr_ind_typed hsat' ht a₀ (by simp)⟩
      · exact absurd (SrcDefeq.blocksCong_ctor (SrcDefeq.getAppFn_mkAppN_const c us vs) hcv) hnb
    · obtain ⟨f₀, a₀, hf₀, ha₀, -, hF, hA⟩ := TrM.wf_app hE hok hsp he ht
      exact ⟨f₀, a₀, hf₀, ha₀, hF, hA⟩
  rcases app_inv hns hnc (fun _ _ _ _ hfe hrv => rec_spine_len hf hfe hrv) her with
    ⟨rfl, hbx⟩ | ⟨tf, ta, rfl, herf, hera⟩
  · exact erases_correct_box henv hE hsub he ht hbx hev
  cases hdeps with
  | app hdf hda =>
  obtain ⟨vf, hvf, hevf⟩ := ihf hf₀ ⟨F, hF⟩ herf hdf
  obtain ⟨va, -, heva⟩ := iha ha₀ ⟨A₁, hA₁⟩ hera hda
  have hvf0 : vf = .box := hfv.elim (fun h => Erases.atomSpine_box h hvf hevf)
    (fun h => Erases.propProj_box h hvf hevf)
  subst hvf0
  obtain ⟨w, hw, hdw⟩ := SrcEval.defeq henv hE hsub he ht hev
  refine ⟨.box, .box ?_, .box hevf heva⟩
  rcases hfv with hsp | hpp
  · exact ErasableS.atom henv hE hsub (.app hsp) hw hdw.right
  · obtain ⟨S, i, e₀, hfn⟩ := RelInst.propProj_head hpp
    have hnsp : ¬ SpecialHead B f' := fun ⟨c, us, _, hfn', _⟩ => by rw [hfn] at hfn'; cases hfn'
    obtain ⟨wf, wa, hwf, -, rfl, ⟨F', hF'⟩, -⟩ := TrM.wf_app hE hok hnsp hw hdw.right
    obtain ⟨t₀, htr₀, U, ht₀, hU⟩ := box_of_projHead hfn hvf
    have hEwf : IsErasable E .nil wf :=
      RelInst.IsErasable.of_defeq (trM_defeq hE htr₀ hwf ht₀ hF') hU
    exact ⟨_, hw, IsErasable.app hE hok hEwf hdw.right⟩

end

end EraseProof
