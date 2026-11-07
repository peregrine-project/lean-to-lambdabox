import EraseProof.Simulation.Ind
import EraseProof.Bridge.SatTyped

/-!
# The ι cases of the simulation

`SrcEval.casesIota` continues with the alternative applied to the fields of the major's value,
`mkAppN alt fs`, while λ□'s ι substitutes the fields' erasures into the erased branch, which erases
the alternative under its field binders (`ErasesAlt`): leading λs peeled, missing ones
η-introduced. Substituting the fields (`ErasesAlt.inst`) gives an erasure of the head-β-reduct of
`mkAppN alt fs` (`HeadBeta`: β-steps at the head of a λ-headed spine whose arguments are values
that evaluate only to themselves, `Fixed`), not of `mkAppN alt fs` itself. The evaluation of the
reduct is nested inside that of `mkAppN alt fs`, so the induction hypothesis of the ι cases is the
conclusion for every head-β-reduct (`erases_correct`'s induction is on this stronger motive). The
fields of a constructor value that is an evaluation result are `Fixed` (`SimIota.res_of_eval`, an
idempotence of the source evaluation). Reference: the `eval_iota` case of `erases_correct`
(`MR E/ErasureCorrectness.v:182`), where PCUIC's `iota_red` substitutes the fields into the branch
body directly.
-/

open Lean Erasure
open Metalean (Defeq EnvWF TypeEq WHRed)

namespace EraseProof

namespace SimIota

variable {σ : EvalEnv}

/-- `a` evaluates to itself only. -/
def Fixed (σ : EvalEnv) (a : Expr) : Prop := ∀ w, SrcEval σ a w → w = a

/-- An evaluation result: a value that evaluates to itself only, and whose arguments are results
when it is a constructor spine. -/
inductive Res (σ : EvalEnv) : Expr → Prop
  | mk {v : Expr} : SrcValue σ v → Fixed σ v →
      (∀ c us cv (as : List Expr), findDecl σ.decls c = some (.ctorInfo cv) →
        v = mkAppN (.const c us) as.toArray → ∀ a ∈ as, Res σ a) → Res σ v

/-- Constant spines are injective in the constant, its levels and the arguments. -/
theorem mkAppN_inj {c c' : Name} {us us' : List Level} {as as' : List Expr}
    (h : mkAppN (.const c us) as.toArray = mkAppN (.const c' us') as'.toArray) :
    c = c' ∧ us = us' ∧ as = as' := by
  rw [mkAppN_eq_foldl, mkAppN_eq_foldl] at h
  exact foldl_app_const_inj h

/-- An atom constant has no δ and is neither a constructor nor a recognized `casesOn`. -/
theorem isAtom_spec {c : Name} (h : σ.isAtom c = true) :
    σ.unfold? c = none ∧ specialArity σ c = none := by
  unfold EvalEnv.isAtom at h
  split at h
  · rename_i ci hci
    simp only [Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none] at h
    obtain ⟨⟨⟨hu, hc⟩, hown⟩, -⟩ := h
    refine ⟨hu, ?_⟩
    unfold specialArity
    rw [hci]
    split
    · rename_i cv hcv
      cases hcv
      cases hown
    · rename_i qv hqv
      cases hqv
      cases hown
    · rw [hc]; rfl
  · cases h

/-- A constructor or a recognized `casesOn` is no atom. -/
theorem special_not_atom {c : Name} {ar : Nat} (h : specialArity σ c = some ar) :
    σ.isAtom c = false := by
  cases ha : σ.isAtom c
  · rfl
  · rw [(isAtom_spec ha).2] at h; cases h

/-- An unfoldable constant is neither a constructor nor a recognized `casesOn`. -/
theorem unfold_not_special {c : Name} {ci : ConstantInfo} {b : Expr}
    (hu : σ.unfold? c = some (ci, b)) : specialArity σ c = none := by
  obtain ⟨d, hd⟩ := SrcDefeq.unfold?_defn hu
  obtain ⟨-, -, hco⟩ := SimCases.unfold?_spec hu
  unfold specialArity
  rw [hd, hco]
  rfl

/-- A spine headed by a constructor or a recognized `casesOn` blocks application congruence. -/
theorem blocksCong_special {e : Expr} {c : Name} {us : List Level} {ar : Nat}
    (he : e.getAppFn = .const c us) (har : specialArity σ c = some ar) : BlocksCong σ e := by
  rcases SrcDefeq.specialArity_some har with ⟨cv, hcv, -⟩ | ⟨iv, hiv⟩ | ⟨qv, hqv, -⟩
  · exact SrcDefeq.blocksCong_ctor he hcv
  · cases e with
    | app f a => exact .inr (.inl ⟨c, us, iv, he, hiv⟩)
    | const => exact .inr (.inl ⟨c, us, iv, he, hiv⟩)
    | _ => cases he
  · exact SrcDefeq.blocksCong_quot he hqv

/-- The evaluations of a spine headed by a constructor or a recognized `casesOn`, with at most its
arity of arguments: the η-expansion, a saturated constructor, or a saturated `casesOn`. -/
theorem eval_spine_inv {c : Name} {us : List Level} {as : List Expr} {w : Expr} {ar : Nat}
    (h : SrcEval σ (mkAppN (.const c us) as.toArray) w) (har : specialArity σ c = some ar)
    (hle : as.length ≤ ar) :
    σ.etaSpine? c us as = some w ∨
    (∃ cv, ∃ vs : List Expr, findDecl σ.decls c = some (.ctorInfo cv) ∧
      as.length = cv.numParams + cv.numFields ∧ as.length = vs.length ∧
      (∀ (i : Nat) a v, as[i]? = some a → vs[i]? = some v → SrcEval σ a v) ∧
      w = mkAppN (.const c us) vs.toArray) ∨
    (∃ iv, σ.casesOn? c = some iv ∧ as.length = casesArity iv) ∨
    (∃ qv, findDecl σ.decls c = some (.quotInfo qv) ∧ quotEvalArity qv.kind = some as.length) := by
  have hfn := SrcDefeq.getAppFn_mkAppN_const c us as
  generalize hx : mkAppN (.const c us) as.toArray = x at h hfn
  cases h with
  | beta hns => exact absurd (SimCases.shortSpine_of hx.symm har hle) hns
  | appCong hns => exact absurd (SimCases.shortSpine_of hx.symm har hle) hns
  | delta hu =>
    obtain ⟨-, rfl, -⟩ := SrcDefeq.spine_const hx
    rw [unfold_not_special hu] at har; cases har
  | constAtom ha =>
    obtain ⟨-, rfl, -⟩ := SrcDefeq.spine_const hx
    rw [special_not_atom har] at ha; cases ha
  | eta he =>
    obtain ⟨rfl, rfl, rfl⟩ := mkAppN_inj hx
    exact .inl he
  | ctor hc hlen hl hev =>
    obtain ⟨rfl, rfl, rfl⟩ := mkAppN_inj hx
    exact .inr (.inl ⟨_, _, hc, hlen, hl, hev, rfl⟩)
  | casesIota hcs hlen | casesLitZero hcs _ hlen | casesLitSucc hcs _ hlen
  | casesProof hcs hlen =>
    obtain ⟨rfl, rfl, rfl⟩ := mkAppN_inj hx
    exact .inr (.inr (.inl ⟨_, hcs, hlen⟩))
  | quotMk hc hk | quotLift hc hk =>
    obtain ⟨rfl, rfl, rfl⟩ := mkAppN_inj hx
    exact .inr (.inr (.inr ⟨_, hc, by rw [hk]; rfl⟩))
  | recIota hcr =>
    obtain ⟨rfl, -, -⟩ := mkAppN_inj hx
    rcases SrcDefeq.specialArity_some har with ⟨cv, hcv, -⟩ | ⟨iv, hiv⟩ | ⟨qv, hqv, -⟩
    · rw [hcr] at hcv; cases hcv
    · obtain ⟨d, hd⟩ := SrcDefeq.casesOn?_defn hiv
      rw [hcr] at hd; cases hd
    · rw [hcr] at hqv; cases hqv
  | zeta | proj | projProp | lit | mdata => cases hfn
  | atom ha =>
    cases w <;> simp [SrcAtom, Expr.getAppFn] at ha hfn

/-- A short spine with fewer arguments than its arity evaluates to its η-expansion only. -/
theorem eval_short {c : Name} {us : List Level} {as : List Expr} {w : Expr} {ar : Nat}
    (h : SrcEval σ (mkAppN (.const c us) as.toArray) w) (har : specialArity σ c = some ar)
    (hlt : as.length < ar) : σ.etaSpine? c us as = some w := by
  rcases eval_spine_inv h har hlt.le with h | ⟨cv, vs, hc, hlen, -⟩ | ⟨iv, hiv, hl⟩ |
    ⟨qv, hqv, hq⟩
  · exact h
  · rw [show specialArity σ c = some (cv.numParams + cv.numFields) by
      unfold specialArity; rw [hc]] at har
    cases har
    omega
  · rw [SimCases.specialArity_casesOn hiv] at har
    cases har
    omega
  · rw [show specialArity σ c = quotEvalArity qv.kind by unfold specialArity; rw [hqv], hq] at har
    cases har
    omega

/-- λ, sort and Π evaluate to themselves only. -/
theorem fixed_atom {e : Expr} (ha : SrcAtom e) : Fixed σ e := by
  intro w h
  have hfn : ∀ c us, e.getAppFn ≠ .const c us := by
    intro c us h'; cases e <;> simp [SrcAtom, Expr.getAppFn] at ha h'
  generalize hx : e = x at h
  cases h with
  | atom => rfl
  | eta | ctor | casesIota | casesLitZero | casesLitSucc | casesProof | quotMk | quotLift | recIota =>
    exact absurd hx (CasesWhred.ne_mkAppN_const hfn)
  | beta | zeta | delta | constAtom | proj | projProp | lit | appCong | mdata =>
    subst hx; simp [SrcAtom] at ha

/-- Nat literals evaluate to themselves only. -/
theorem fixed_lit {k : Nat} : Fixed σ (.lit (.natVal k)) := by
  intro w h
  generalize hx : Expr.lit (.natVal k) = x at h
  cases h with
  | lit => cases hx; rfl
  | eta | ctor | casesIota | casesLitZero | casesLitSucc | casesProof | quotMk | quotLift | recIota =>
    exact absurd hx (CasesWhred.ne_mkAppN_const fun _ _ h => by cases h)
  | atom ha => subst hx; simp [SrcAtom] at ha
  | beta | zeta | delta | constAtom | proj | projProp | appCong | mdata => cases hx

/-- An atom constant evaluates to itself only. -/
theorem fixed_const {c : Name} {us : List Level} (ha : σ.isAtom c = true) :
    Fixed σ (.const c us) := by
  intro w h
  obtain ⟨hu, hsa⟩ := isAtom_spec ha
  generalize hx : Expr.const c us = x at h
  cases h with
  | constAtom => cases hx; rfl
  | delta hu' => cases hx; rw [hu] at hu'; cases hu'
  | eta he =>
    obtain ⟨-, rfl, -⟩ := SrcDefeq.spine_const hx.symm
    obtain ⟨ar, har, -⟩ := SimCases.etaSpine?_lt he
    rw [hsa] at har; cases har
  | ctor hc =>
    obtain ⟨-, rfl, -⟩ := SrcDefeq.spine_const hx.symm
    unfold specialArity at hsa; rw [hc] at hsa; cases hsa
  | casesIota hcs | casesLitZero hcs | casesLitSucc hcs | casesProof hcs =>
    obtain ⟨-, rfl, -⟩ := SrcDefeq.spine_const hx.symm
    rw [SimCases.specialArity_casesOn hcs] at hsa; cases hsa
  | quotMk | quotLift | recIota => exact absurd (SrcDefeq.spine_const hx.symm).1 (by simp)
  | atom ha' => subst hx; simp [SrcAtom] at ha'
  | beta | zeta | proj | projProp | lit | appCong | mdata => cases hx

/-- A saturated constructor spine of fixed arguments evaluates to itself only. -/
theorem fixed_ctor {c : Name} {us : List Level} {cv : ConstructorVal} {vs : List Expr}
    (hc : findDecl σ.decls c = some (.ctorInfo cv)) (hlen : vs.length = cv.numParams + cv.numFields)
    (hfix : ∀ a ∈ vs, Fixed σ a) : Fixed σ (mkAppN (.const c us) vs.toArray) := by
  intro w h
  have har : specialArity σ c = some (cv.numParams + cv.numFields) := by
    unfold specialArity; rw [hc]
  rcases eval_spine_inv h har hlen.le with he | ⟨cv', ws, hc', -, hl, hev, rfl⟩ | ⟨iv, hiv, -⟩ |
    ⟨qv, hqv, -⟩
  · obtain ⟨ar, har', hlt⟩ := SimCases.etaSpine?_lt he
    rw [har] at har'; cases har'; omega
  · congr 2
    refine List.ext_getElem? fun i => ?_
    cases hv : vs[i]? with
    | none =>
      rw [List.getElem?_eq_none_iff] at hv ⊢; omega
    | some a =>
      obtain ⟨b, hb⟩ : ∃ b, ws[i]? = some b :=
        ⟨_, List.getElem?_eq_getElem (by have := (List.getElem?_eq_some_iff.mp hv).1; omega)⟩
      rw [hb, hfix a (List.mem_of_getElem? hv) b (hev i a b hv hb)]
  · obtain ⟨d, hd⟩ := SrcDefeq.casesOn?_defn hiv
    rw [hc] at hd; cases hd
  · rw [hc] at hqv; cases hqv

/-- A source value is not headed by a recursor. -/
theorem srcValue_not_rec {e : Expr} (hv : SrcValue σ e) {c : Name} {us : List Level}
    {rv : RecursorVal} (hfn : e.getAppFn = .const c us) :
    findDecl σ.decls c ≠ some (.recInfo rv) := by
  intro hr
  cases hv with
  | lam | sort | forallE | lit => simp [Expr.getAppFn] at hfn
  | spine hsp =>
    obtain ⟨c', us', hc', hat⟩ := RelInst.atomSpine_head hsp
    rw [hfn] at hc'; cases hc'
    unfold EvalEnv.isAtom at hat
    rw [hr] at hat
    simp [OwnRules] at hat
  | propProj hp =>
    obtain ⟨S, i, e₀, he⟩ := RelInst.propProj_head hp
    rw [he] at hfn; cases hfn
  | ctor hc _ =>
    rw [SrcDefeq.getAppFn_mkAppN_const] at hfn; cases hfn
    rw [hc] at hr; cases hr
  | quotMk hc _ _ =>
    rw [SrcDefeq.getAppFn_mkAppN_const] at hfn; cases hfn
    rw [hc] at hr; cases hr

/-- An application whose head is fixed and blocks no congruence, of a fixed argument, evaluates to
itself only. -/
theorem fixed_app {f a : Expr} (hf : Fixed σ f) (ha : Fixed σ a) (hnb : ¬ BlocksCong σ f)
    (hnr : ∀ c us rv, f.getAppFn = .const c us → findDecl σ.decls c ≠ some (.recInfo rv)) :
    Fixed σ (.app f a) := by
  intro w h
  have hsp : ∀ {c us} {as : List Expr} {ar : Nat}, Expr.app f a = mkAppN (.const c us) as.toArray →
      specialArity σ c = some ar → False := by
    intro c us as ar hx har
    obtain ⟨bs, -, rfl⟩ := SrcDefeq.spine_app hx.symm
    exact hnb (blocksCong_special (SrcDefeq.getAppFn_mkAppN_const c us bs) har)
  generalize hx : Expr.app f a = x at h
  cases h with
  | beta _ hf' =>
    cases hx
    have := hf _ hf'
    subst this
    exact absurd trivial hnb
  | appCong _ hf' _ ha' =>
    cases hx
    rw [hf _ hf', ha _ ha']
  | eta he =>
    obtain ⟨ar, har, -⟩ := SimCases.etaSpine?_lt he
    exact (hsp hx har).elim
  | ctor hc => exact (hsp hx (by unfold specialArity; rw [hc])).elim
  | casesIota hcs | casesLitZero hcs | casesLitSucc hcs | casesProof hcs =>
    exact (hsp hx (SimCases.specialArity_casesOn hcs)).elim
  | quotMk hc hk => exact (hsp (ar := 3) hx (by simp [specialArity, hc, hk, quotEvalArity])).elim
  | quotLift hc hk => exact (hsp (ar := 6) hx (by simp [specialArity, hc, hk, quotEvalArity])).elim
  | recIota hcr =>
    obtain ⟨bs, -, rfl⟩ := SrcDefeq.spine_app hx.symm
    exact (hnr _ _ _ (SrcDefeq.getAppFn_mkAppN_const _ _ _) hcr).elim
  | atom ha' => subst hx; simp [SrcAtom] at ha'
  | zeta | delta | constAtom | proj | projProp | lit | mdata => cases hx

/-- A `Prop` projection of a fixed neutral proof evaluates to itself only. -/
theorem fixed_projProp {S : Name} {i : Nat} {m : Expr} (hm : Fixed σ m)
    (hv : AtomSpine σ m ∨ PropProj σ m) : Fixed σ (.proj S i m) := by
  intro w h
  generalize hx : Expr.proj S i m = x at h
  cases h with
  | proj hm' hcv =>
    cases hx
    have := hm _ hm'
    subst this
    obtain ⟨C, us, cv, ps, hC, -, -, -, -, rfl⟩ := hcv
    exfalso
    rcases hv with hv | hv
    · obtain ⟨c', us', hfn, hat⟩ := RelInst.atomSpine_head hv
      rw [SrcDefeq.getAppFn_mkAppN_const] at hfn
      cases hfn
      rw [special_not_atom (by unfold specialArity; rw [hC])] at hat
      cases hat
    · obtain ⟨S', i', e₀, hfn⟩ := RelInst.propProj_head hv
      rw [SrcDefeq.getAppFn_mkAppN_const] at hfn
      cases hfn
  | projProp _ hm' =>
    cases hx
    rw [hm _ hm']
  | eta | ctor | casesIota | casesLitZero | casesLitSucc | casesProof | quotMk | quotLift | recIota =>
    exact absurd hx (CasesWhred.ne_mkAppN_const fun _ _ h => by cases h)
  | atom ha' => subst hx; simp [SrcAtom] at ha'
  | beta | zeta | delta | constAtom | lit | appCong | mdata => cases hx

/-- A `Quot.mk` spine of a fixed element evaluates to itself only. -/
theorem fixed_quotMk {c : Name} {us : List Level} {qv : QuotVal} {α r a : Expr}
    (hc : findDecl σ.decls c = some (.quotInfo qv)) (hk : qv.kind = .ctor) (ha : Fixed σ a) :
    Fixed σ (mkAppN (.const c us) [α, r, a].toArray) := by
  intro w h
  have har : specialArity σ c = some 3 := by simp [specialArity, hc, hk, quotEvalArity]
  generalize hx : mkAppN (.const c us) [α, r, a].toArray = x at h
  cases h with
  | beta hns => exact absurd (SimCases.shortSpine_of hx.symm har (by simp)) hns
  | appCong hns => exact absurd (SimCases.shortSpine_of hx.symm har (by simp)) hns
  | delta | constAtom => exact absurd (SrcDefeq.spine_const hx).1 (by simp)
  | eta he =>
    obtain ⟨rfl, rfl, rfl⟩ := mkAppN_inj hx
    obtain ⟨ar, har', hlt⟩ := SimCases.etaSpine?_lt he
    rw [har] at har'; cases har'; simp at hlt
  | ctor hc' =>
    obtain ⟨rfl, -, -⟩ := mkAppN_inj hx
    rw [hc] at hc'; cases hc'
  | casesIota hcs | casesLitZero hcs | casesLitSucc hcs | casesProof hcs =>
    obtain ⟨rfl, -, -⟩ := mkAppN_inj hx
    obtain ⟨d, hd⟩ := SrcDefeq.casesOn?_defn hcs
    rw [hc] at hd; cases hd
  | quotMk _ _ ha' =>
    obtain ⟨rfl, rfl, h3⟩ := mkAppN_inj hx
    simp only [List.cons.injEq, and_true] at h3
    obtain ⟨rfl, rfl, rfl⟩ := h3
    rw [ha _ ha']
  | quotLift =>
    obtain ⟨-, -, h3⟩ := mkAppN_inj hx
    simp at h3
  | recIota hcr =>
    obtain ⟨rfl, -, -⟩ := mkAppN_inj hx
    rw [hc] at hcr; cases hcr
  | atom ha' => subst hx; cases ha'
  | zeta | proj | projProp | lit | mdata =>
    exact absurd hx.symm (CasesWhred.ne_mkAppN_const fun _ _ h => by cases h)

/-- Every evaluation result is a `Res`: in particular it evaluates to itself only, and so do the
arguments of a constructor value that is a result. Reference: `eval_to_value`
(`MR P/PCUICWcbvEval.v:570`), `value_final` (`:727`) with `eval_deterministic` (`:1227`). -/
theorem res_of_eval {e v : Expr} (hev : SrcEval σ e v) : Res σ v := by
  have nonspine : ∀ {x : Expr}, (∀ c us, x.getAppFn ≠ .const c us) →
      ∀ c us cv (as : List Expr), findDecl σ.decls c = some (.ctorInfo cv) →
        x = mkAppN (.const c us) as.toArray → ∀ a ∈ as, Res σ a :=
    fun hfn _ _ _ _ _ hx => absurd hx (CasesWhred.ne_mkAppN_const hfn)
  induction hev with
  | beta _ _ _ _ _ _ ih => exact ih
  | zeta _ _ _ ih => exact ih
  | delta _ _ ih => exact ih
  | @constAtom c us h =>
    refine .mk (.spine (.const h)) (fixed_const h) ?_
    intro c' us' cv as _ hx
    obtain ⟨rfl, -, -⟩ := SrcDefeq.spine_const hx.symm
    simp
  | eta h =>
    obtain ⟨x, A, b, bi, rfl⟩ := SimInd.etaSpine?_lam h
    exact .mk .lam (fixed_atom trivial) (nonspine fun _ _ h => by cases h)
  | @ctor c cv us as vs hc hl hlv hev ih =>
    have hres : ∀ a ∈ vs, Res σ a := by
      intro a ha
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
      exact ih i as[i] _ (List.getElem?_eq_getElem (by omega)) (List.getElem?_eq_getElem hi)
    refine .mk (.ctor hc (hlv ▸ hl)) (fixed_ctor hc (hlv ▸ hl) fun a ha => ?_) ?_
    · obtain ⟨-, hf, -⟩ := hres a ha; exact hf
    · intro c' us' cv' as' _ hx
      obtain ⟨-, -, rfl⟩ := mkAppN_inj hx
      exact hres
  | casesIota _ _ _ _ _ _ _ _ ih => exact ih
  | casesLitZero _ _ _ _ _ _ _ _ ih => exact ih
  | casesLitSucc _ _ _ _ _ _ _ _ ih => exact ih
  | casesProof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | quotMk hc hk _ ih =>
    obtain ⟨hv, hf, -⟩ := ih
    refine .mk (.quotMk hc hk hv) (fixed_quotMk hc hk hf) ?_
    intro c' us' cv as hc' hx
    obtain ⟨rfl, -, -⟩ := mkAppN_inj hx
    rw [hc] at hc'; cases hc'
  | quotLift _ _ _ _ _ _ _ _ _ ih => exact ih
  | recIota => rename_i ih; exact ih
  | proj _ hcv hfs ihm =>
    obtain ⟨C, us, cv, ps, hC, -, -, -, -, rfl⟩ := hcv
    obtain ⟨-, -, hargs⟩ := ihm
    exact hargs _ _ _ _ hC rfl _ (List.mem_append_right _ (List.mem_of_getElem? hfs))
  | projProp hS _ hm ihm =>
    obtain ⟨-, hfm, -⟩ := ihm
    refine .mk ?_ (fixed_projProp hfm hm) (nonspine fun _ _ h => by cases h)
    rcases hm with hm | hm
    · exact .propProj (.proj hS hm)
    · exact .propProj (.projProj hS hm)
  | lit => exact .mk .lit fixed_lit (nonspine fun _ _ h => by cases h)
  | appCong hns hf hb ha ihf iha =>
    obtain ⟨-, hff, -⟩ := ihf
    obtain ⟨-, hfa, -⟩ := iha
    refine .mk (SrcEval.appCong hns hf hb ha).value
      (fixed_app hff hfa hb fun _ _ _ h => srcValue_not_rec (SrcEval.value hf) h) ?_
    intro c us cv as hc hx
    obtain ⟨bs, -, rfl⟩ := SrcDefeq.spine_app hx.symm
    exact absurd (SrcDefeq.blocksCong_ctor (SrcDefeq.getAppFn_mkAppN_const c us bs) hc) hb
  | mdata _ ih => exact ih
  | atom h =>
    rename_i e
    refine .mk (SrcEval.atom h).value (fixed_atom h) (nonspine ?_)
    intro c us h'
    cases e <;> simp [SrcAtom, Expr.getAppFn] at h h'

/-- The fields of a constructor value that is an evaluation result are values that evaluate to
themselves only. -/
theorem fields_of_eval {m mv : Expr} {T : Name} {i : Nat} {fs : List Expr}
    (hm : SrcEval σ m mv) (hcv : CtorValue σ T mv i fs) : ∀ f ∈ fs, SrcValue σ f ∧ Fixed σ f := by
  obtain ⟨C, us, cv, ps, hC, -, -, -, -, rfl⟩ := hcv
  obtain ⟨-, -, hargs⟩ := res_of_eval hm
  intro f hf
  obtain ⟨hv, hfx, -⟩ := hargs _ _ _ _ hC rfl f (List.mem_append_right _ hf)
  exact ⟨hv, hfx⟩

/-! ## One more argument on a short spine -/

/-- Instantiating Π-binders with two argument lists in turn. -/
theorem piInst_append : ∀ (as bs : List Expr) (T : Expr),
    piInst (as ++ bs) T = (piInst as T).bind (piInst bs)
  | [], _, _ => rfl
  | _ :: _, _, .forallE _ _ B _ => piInst_append _ _ (B.instantiate1' _)
  | _ :: _, _, .bvar _ | _ :: _, _, .fvar _ | _ :: _, _, .mvar _ | _ :: _, _, .sort _
  | _ :: _, _, .const .. | _ :: _, _, .app .. | _ :: _, _, .lam .. | _ :: _, _, .letE ..
  | _ :: _, _, .lit _ | _ :: _, _, .mdata .. | _ :: _, _, .proj .. => rfl

/-- Instantiating the outermost η-binder of the body of an η-expanded spine appends the
argument to the spine. -/
theorem body_snoc (a : Expr) (k : Nat) (c : Name) (us : List Level) (as : List Expr) :
    (mkAppN (.const c us) (as.map (·.liftLooseBVars' 0 (k + 1)) ++
      (List.range (k + 1)).reverse.map Expr.bvar).toArray).instantiate1' a k =
    mkAppN (.const c us) ((as ++ [a]).map (·.liftLooseBVars' 0 k) ++
      (List.range k).reverse.map Expr.bvar).toArray := by
  rw [RelInst.inst_spine]
  congr 2
  simp only [List.map_append, List.map_map, List.range_succ, List.reverse_append,
    List.reverse_singleton, List.map_cons, List.cons_append, List.append_assoc]
  congr 1
  · refine List.map_congr_left fun x _ => ?_
    exact RelInst.inst_lift_cancel a x (c := 0) (j := k) (n := k) (Nat.zero_le k) (by omega)
  · simp only [Expr.instantiate1', Nat.lt_irrefl, ↓reduceIte, List.cons.injEq, true_and]
    refine List.map_congr_left fun j hj => ?_
    have : j < k := by simpa using hj
    simp [Expr.instantiate1', this]

/-- One more argument on a short spine whose η-expansion is `fun x => b`: the spine with the
argument is short and its η-expansion is `b` instantiated, or it is saturated and is `b`
instantiated. -/
theorem etaSpine?_snoc {c : Name} {us : List Level} {as : List Expr} {x : Name} {A b : Expr}
    {bi : BinderInfo} (a : Expr) (h : σ.etaSpine? c us as = some (.lam x A b bi)) :
    ∃ ar, specialArity σ c = some ar ∧ as.length < ar ∧
      (as.length + 1 < ar → σ.etaSpine? c us (as ++ [a]) = some (b.instantiate1' a)) ∧
      (as.length + 1 = ar → b.instantiate1' a = mkAppN (.const c us) (as ++ [a]).toArray) := by
  unfold EvalEnv.etaSpine? at h
  split at h
  · rename_i ci ar hci har
    split at h
    · rename_i hlt
      obtain ⟨ty, hty, hl⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨k, hk⟩ : ∃ k, ar - as.length = k + 1 := ⟨ar - as.length - 1, by omega⟩
      rw [hk] at hl
      cases ty with
      | forallE n d b' bi' =>
        simp only [lamsOf, Option.map_eq_some_iff] at hl
        obtain ⟨e₀, he₀, heq⟩ := hl
        cases heq
        have hinst := RelInst.lamsOf_inst a (d := 0) he₀
        rw [Nat.zero_add, body_snoc] at hinst
        refine ⟨ar, har, hlt, fun hlt' => ?_, fun heq => ?_⟩
        · unfold EvalEnv.etaSpine?
          rw [hci, har]
          simp only [List.length_append, List.length_singleton, hlt', ↓reduceIte,
            Option.bind_eq_some_iff]
          refine ⟨b'.instantiate1' a, ?_, ?_⟩
          · rw [piInst_append, hty]; rfl
          · rw [show ar - (as.length + 1) = k by omega]; exact hinst
        · have hk0 : k = 0 := by omega
          subst hk0
          simp only [lamsOf, Option.some.injEq] at he₀ hinst
          rw [← hinst]
          simp [liftLooseBVars'_zero]
      | _ => cases hl
    · cases h
  · cases h

/-! ## Head β-reduction of spines of fixed arguments -/

/-- One head β-step of a λ-headed spine whose arguments evaluate to themselves only. -/
inductive HStep (σ : EvalEnv) : Expr → Expr → Prop
  | beta {n : Name} {A b a : Expr} {bi : BinderInfo} :
      Fixed σ a → HStep σ (.app (.lam n A b bi) a) (b.instantiate1' a)
  | app {f f' a : Expr} : HStep σ f f' → Fixed σ a → HStep σ (.app f a) (.app f' a)

/-- Head β-reduction: a sequence of `HStep`s. -/
inductive HeadBeta (σ : EvalEnv) : Expr → Expr → Prop
  | refl {e : Expr} : HeadBeta σ e e
  | step {e e' X : Expr} : HStep σ e e' → HeadBeta σ e' X → HeadBeta σ e X

/-- A head step starts from an application whose head is a λ. -/
theorem HStep.head {e e' : Expr} (h : HStep σ e e') :
    ∃ f a, e = .app f a ∧ ∃ n A b bi, e.getAppFn = .lam n A b bi := by
  induction h with
  | beta => exact ⟨_, _, rfl, _, _, _, _, rfl⟩
  | app _ _ ih =>
    obtain ⟨-, -, -, n, A, b, bi, h⟩ := ih
    exact ⟨_, _, rfl, n, A, b, bi, by simpa [Expr.getAppFn] using h⟩

/-- A term whose head is not a λ has no head β-reduct but itself. -/
theorem HeadBeta.eq_of_head {e X : Expr} (h : HeadBeta σ e X)
    (he : ∀ f a, e = .app f a → ∀ n A b bi, e.getAppFn ≠ .lam n A b bi) : X = e := by
  cases h with
  | refl => rfl
  | step hs _ =>
    obtain ⟨f, a, rfl, n, A, b, bi, h⟩ := hs.head
    exact absurd h (he f a rfl n A b bi)

/-- `HeadBeta.app_inv`, for a term that is an application. -/
theorem HeadBeta.app_inv' {e X : Expr} (h : HeadBeta σ e X) : ∀ {F a : Expr}, e = .app F a →
    X = .app F a ∨ (Fixed σ a ∧ ((∃ XF, HeadBeta σ F XF ∧ X = .app XF a) ∨
      ∃ n A b bi, HeadBeta σ F (.lam n A b bi) ∧ HeadBeta σ (b.instantiate1' a) X)) := by
  induction h with
  | refl => intro F a hx; exact .inl hx
  | step hs _ ih =>
    intro F a hx
    subst hx
    cases hs with
    | beta hfix => exact .inr ⟨hfix, .inr ⟨_, _, _, _, .refl, by assumption⟩⟩
    | app hF hfix =>
      refine .inr ⟨hfix, ?_⟩
      rcases ih rfl with rfl | ⟨-, ⟨XF, hXF, rfl⟩ | ⟨n, A, b, bi, hl, hX⟩⟩
      · exact .inl ⟨_, .step hF .refl, rfl⟩
      · exact .inl ⟨XF, .step hF hXF, rfl⟩
      · exact .inr ⟨n, A, b, bi, .step hF hl, hX⟩

/-- Head β-reducts of an application: itself, or (the argument fixed) an application of a reduct
of the head, or a reduct of the β-reduct once the head has reduced to a λ. -/
theorem HeadBeta.app_inv {F a X : Expr} (h : HeadBeta σ (.app F a) X) :
    X = .app F a ∨ (Fixed σ a ∧ ((∃ XF, HeadBeta σ F XF ∧ X = .app XF a) ∨
      ∃ n A b bi, HeadBeta σ F (.lam n A b bi) ∧ HeadBeta σ (b.instantiate1' a) X)) :=
  h.app_inv' rfl

/-- A head step under fixed arguments. -/
theorem HStep.spine {F F' : Expr} (h : HStep σ F F') :
    ∀ {rest : List Expr}, (∀ a ∈ rest, Fixed σ a) →
      HStep σ (mkAppN F rest.toArray) (mkAppN F' rest.toArray) := by
  intro rest
  induction rest using List.reverseRecOn with
  | nil => intro _; rw [mkAppN_eq_foldl, mkAppN_eq_foldl]; exact h
  | append_singleton rest a ih =>
    intro hfix
    rw [mkAppN_eq_foldl, mkAppN_eq_foldl, List.foldl_append, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [← mkAppN_eq_foldl, ← mkAppN_eq_foldl]
    exact .app (ih fun x hx => hfix x (List.mem_append_left _ hx))
      (hfix a (List.mem_append_right _ (List.mem_singleton_self a)))

/-! ## The ι driver -/

section
open Metalean InstPre RelInst
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P : List ConstantInfo}
  {lps : List Name}

/-- An alternative erased under `k` field binders has `k` binder names. -/
theorem erasesAlt_length : ∀ {k n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
    {Δ : MLCtx ζ lps.length n} {e : Lean.Expr} {ns : List BinderName} {t : LBTerm},
    ErasesAlt E B lps σ Γ Δ k e (ns, t) → ns.length = k
  | 0, _, _, _, _, _, _, h => by rw [(ErasesAlt.zero_inv h).1]; rfl
  | k + 1, _, _, _, _, _, _, h => by
    rcases ErasesAlt.succ_inv h with ⟨_, _, _, _, _, ns', _, rfl, _, _, h'⟩ |
      ⟨_, _, _, _, ns', rfl, _, _, h'⟩
    · simp [erasesAlt_length h']
    · simp [erasesAlt_length h']

/-- A field of a constructor value for the ι driver: a value that evaluates to itself only, with a
closed erasure. -/
def FieldOK (E : Metalean.Env ζ) (B : Binds ζ) (lps : List Name) (σ : EvalEnv) (f : Lean.Expr)
    (f' : LBTerm) : Prop :=
  SrcValue σ f ∧ Fixed σ f ∧ Erases E B lps σ .nil [] f f' ∧ closedn 0 f' = true

/-- A property of the related pairs holds of the left entries. -/
theorem forall₂_left {α β : Type} {R : α → β → Prop} {Q : α → Prop} (hQ : ∀ a b, R a b → Q a)
    {l : List α} {l' : List β} (h : List.Forall₂ R l l') : ∀ a ∈ l, Q a := by
  induction h with
  | nil => simp
  | cons hr _ ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hQ _ _ hr
    · exact ih a ha

/-- A property of the related pairs holds of the right entries. -/
theorem forall₂_right {α β : Type} {R : α → β → Prop} {Q : β → Prop} (hQ : ∀ a b, R a b → Q b)
    {l : List α} {l' : List β} (h : List.Forall₂ R l l') : ∀ b ∈ l', Q b := by
  induction h with
  | nil => simp
  | cons hr _ ih =>
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hQ _ _ hr
    · exact ih b hb

/-- A spine with one argument. -/
theorem mkAppN_single (f a : Lean.Expr) : mkAppN f #[a] = .app f a := by
  rw [show #[a] = [a].toArray from rfl, mkAppN_eq_foldl]; rfl

/-- The first argument of a spine. -/
theorem mkAppN_cons (f a : Lean.Expr) (as : List Lean.Expr) :
    mkAppN f (a :: as).toArray = mkAppN (.app f a) as.toArray := by
  rw [mkAppN_eq_foldl, mkAppN_eq_foldl]; rfl

/-- The ι step on the alternative, field by field: substituting the fields' erasures into the
erased branch (`ErasesAlt.inst`) erases a head-β-reduct of the alternative applied to the fields,
which has a typed translation. Reference: `iota_red` (`MR E/EGlobalEnv.v:281`) with
`erases_subst0` (`MR E/ESubstitution.v:612`). -/
theorem drive (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv σ.decls P) :
    ∀ {fs : List Lean.Expr} {fs' : List LBTerm}, List.Forall₂ (FieldOK E B lps σ) fs fs' →
    ∀ {alt : Lean.Expr} {ns : List BinderName} {t : LBTerm} {alt₀ : Metalean.Expr ζ lps.length 0}
      {fs₀ : List (Metalean.Expr ζ lps.length 0)},
      ErasesAlt E B lps σ .nil [] fs.length alt (ns, t) → TrM E B lps .nil [] alt alt₀ →
      List.Forall₂ (TrM E B lps .nil []) fs fs₀ → (∃ T, E[.nil] ⊢ alt₀.appList fs₀ : T) →
      ∃ X tX, HeadBeta σ (mkAppN alt fs.toArray) X ∧
        Erases E B lps σ .nil [] X (substl fs'.reverse t) ∧ TrM E B lps .nil [] X tX ∧
        ∃ T, E[.nil] ⊢ tX : T := by
  have hok := SrcDefeq.nil_ok (E := E) (lps := lps)
  have hord := henv.metaOrderOK
  intro fs fs' hfs
  induction hfs with
  | nil =>
    intro alt ns t alt₀ fs₀ halt hta hfs₀ hT
    cases hfs₀
    obtain ⟨rfl, h⟩ := ErasesAlt.zero_inv halt
    exact ⟨alt, alt₀, .refl, by simpa [substl] using h, hta, by simpa using hT⟩
  | @cons f f' fs fs' hf hrest ih =>
    intro alt ns t alt₀ fs₀ halt hta hfs₀ hT
    obtain ⟨T, hT⟩ := hT
    cases hfs₀ with
    | @cons _ f₀ _ rest₀ hf₀ hrest₀ =>
    obtain ⟨hval, hfix, herf, hcl⟩ := hf
    have hfixs : ∀ a ∈ fs, Fixed σ a := forall₂_left (fun _ _ h => h.2.1) hrest
    have hcls : ∀ g ∈ fs', closedn 0 g = true := forall₂_right (fun _ _ h => h.2.2.2) hrest
    have hlen : fs.length = fs'.length := hrest.length_eq
    have hsubstl := substl_cons_closed (t := t) hcl hcls
    rw [Metalean.Expr.appList_cons] at hT
    obtain ⟨⟨G, hG⟩, -⟩ := InstPre.appList_inv hT
    obtain ⟨X₁, Y₁, halt₀T, hf₀T, -⟩ := hG.app_inv
    rcases ErasesAlt.succ_inv halt with ⟨x, A, b, bi, A', ns', rfl, rfl, hA', hA't, hb⟩ |
      ⟨e', A'', B'', nm, ns', rfl, he', he'T, hb⟩
    · -- a λ peeled: β
      obtain ⟨A₀, b₀, rfl, hA₀, hb₀⟩ := SimCases.trM_lam_inv hta
      obtain ⟨T₀, hb₀T, hπ⟩ := halt₀T.lam_inv hok
      have hf₀A₀ : E[.nil] ⊢ f₀ : A₀ := (TypeEq.forallE_inj hE hok hπ).1.conv hf₀T
      obtain ⟨u, hA₀u⟩ := hf₀A₀.regular
      obtain ⟨l, hl⟩ := hA't
      have hAA : E[.nil] ⊢ A₀ ≡ A' : .sort u := SimCases.trM_defeq hE hA₀ hA' hA₀u hl
      have hb₀T' := Defeq.snocConv hAA hb₀T
      have hokA : E[Metalean.Ctx.nil.snoc A'] ⊢ ok := .snoc hok ⟨l, hl⟩
      have htb' := PreTr.recover hord (PreTr.ofTrM hb₀) (Thin.id _) hokA
        ⟨T₀, by rw [Metalean.Expr.rename_id]; exact hb₀T'⟩
      have hinst := ErasesAlt.inst henv hE hok hsub hval hb htb' hb₀T' herf hf₀
        (Defeq.defeqDF hAA hf₀A₀) hcl
      obtain ⟨tb', htb'', hdb'⟩ := TrM.inst hE hok hord hb₀ hf₀ hf₀A₀ hb₀T
      have hβ := WHRed.beta_defeq hE hok hG
      obtain ⟨T', hT'⟩ := SatTyped.appList_defeq hE hok rest₀ (SrcDefeq.dtrans hE hdb' hβ.symm) hT
      rw [erasesAlt_length hb] at hinst
      obtain ⟨X, tX, hXb, hXe, hXt, hXT⟩ := ih hinst htb'' hrest₀ ⟨T', hT'⟩
      refine ⟨X, tX, ?_, ?_, hXt, hXT⟩
      · rw [mkAppN_cons]
        exact .step (HStep.spine (.beta hfix) hfixs) hXb
      · rw [hsubstl, ← hlen]; exact hXe
    · -- η-introduced: the alternative applied to the field
      have hdef := SimCases.trM_defeq hE hta he' halt₀T he'T
      have hTy : E[.nil] ⊢ .forallE A'' B'' ≡ .forallE X₁ Y₁ typ :=
        Defeq.uniqTy hE hok he'T hdef.right
      have hf₀A'' : E[.nil] ⊢ f₀ : A'' := (TypeEq.forallE_inj hE hok hTy.symm).1.conv hf₀T
      obtain ⟨u, hA''u⟩ := hf₀A''.regular
      have hokA : E[Metalean.Ctx.nil.snoc A''] ⊢ ok := .snoc hok ⟨u, hA''u⟩
      have hrn : E[Metalean.Ctx.nil.snoc A''] ⊢ e'.rename Fin.castSucc :
          (Metalean.Expr.forallE A'' B'').rename Fin.castSucc := by
        have := he'T.substitution (substWF_ofThin hokA (thin_snoc .nil A''))
        simpa only [Metalean.Expr.subst_vars] using this
      have htrn := TrM.rename hord hokA (MLCtx.Subs.bv []) he' hrn
      have hvar : TrM E B lps (Metalean.Ctx.nil.snoc A'') (MLCtx.pushLam [] none) (.bvar 0)
          (.var (Fin.last 0)) := .bvar (by simp [MLCtx.pushLam, MLCtx.findB, MLDecl.denote])
      have hvarT : E[Metalean.Ctx.nil.snoc A''] ⊢ .var (Fin.last 0) : A''.rename Fin.castSucc := by
        have := hokA.varLast
        rwa [show A''.wk = A''.rename Fin.castSucc by
          rw [← Metalean.Expr.subst_wk, ← Metalean.Expr.subst_vars]; rfl] at this
      simp only [Metalean.Expr.rename] at hrn
      obtain ⟨_, hr⟩ := hrn.regular
      obtain ⟨l₁, l₂, hA, hB, -⟩ := hr.forallE_ty_inv
      have happ := Defeq.appDF hA hB hrn hvarT (hB.inst_congr hvarT)
      obtain ⟨b₀, hb₀, hred⟩ := TrM.apps htrn (List.Forall₂.cons hvar .nil)
      have hb₀T := (WHRedS.defeq hE hokA hred (by simpa using happ)).right
      rw [mkAppN_single] at hb₀
      have hinst := ErasesAlt.inst henv hE hok hsub hval hb hb₀ hb₀T herf hf₀ hf₀A'' hcl
      have hai : (Lean.Expr.app (alt.liftLooseBVars' 0 1) (.bvar 0)).instantiate1' f = .app alt f := by
        simp only [Lean.Expr.instantiate1']
        rw [inst_lift_cancel f alt (c := 0) (j := 0) (n := 0) (Nat.le_refl 0) (by omega),
          liftLooseBVars'_zero]
        simp [liftLooseBVars'_zero]
      obtain ⟨t₁, ht₁, hred₁⟩ := TrM.apps hta (List.Forall₂.cons hf₀ .nil)
      have hd₁ := WHRedS.defeq hE hok hred₁ (by simpa using hG)
      obtain ⟨T', hT'⟩ := SatTyped.appList_defeq hE hok rest₀ hd₁.symm hT
      rw [erasesAlt_length hb, hai] at hinst
      rw [mkAppN_single] at ht₁
      obtain ⟨X, tX, hXb, hXe, hXt, hXT⟩ := ih hinst ht₁ hrest₀ ⟨T', hT'⟩
      exact ⟨X, tX, by rw [mkAppN_cons]; exact hXb, by rw [hsubstl, ← hlen]; exact hXe, hXt, hXT⟩

end

/-! ## The `casesIota` case -/

section
open Metalean
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P : List ConstantInfo}
  {lps : List Name} {lenv : GlobalDeclarations}

/-- A sort under Π-binders is a sort or a Π. -/
theorem pi_shape : ∀ {a b : Nat} (Δ : Metalean.Ctx ζ lps.length a b) (X : Metalean.Expr ζ lps.length b),
    ((∃ u, X = .sort u) ∨ ∃ A Y, X = .forallE A Y) →
      (∃ u, Metalean.Ctx.pi X Δ = .sort u) ∨ ∃ A Y, Metalean.Ctx.pi X Δ = .forallE A Y := by
  intro a b Δ
  induction Δ with
  | nil => intro X hX; exact hX
  | snoc Δ A ih => intro X _; exact ih _ (.inr ⟨_, _, rfl⟩)

/-- A term whose type is an inductive type whose level, at the term's levels, is not zero is not
erasable. -/
theorem ind_not_erasable (hE : EnvWF E) {ι : IndSig} {η : Head ζ (.inductive ι)} {s : Fin ι.nsorts}
    {L : Fin ι.nlevels → Metalean.Level lps.length} {ps : Fin ι.nparams → Metalean.Expr ζ lps.length 0}
    {is : Fin (ι.nindices s) → Metalean.Expr ζ lps.length 0} {t : Metalean.Expr ζ lps.length 0}
    (ht : E[.nil] ⊢ t : .ind η s L ps is) (hl : (E.get η).block.level{L} ≠ .zero) :
    ¬ IsErasable E .nil t := by
  have hok := SrcDefeq.nil_ok (E := E) (lps := lps)
  rintro ⟨T', ht', hT'⟩
  have hTE := Defeq.uniqTy hE hok ht ht'
  rcases hT' with ⟨k, Δ, u, hA⟩ | hP
  · have h := hTE.trans hA
    rcases pi_shape Δ _ (.inl ⟨u, rfl⟩) with ⟨u', hu⟩ | ⟨A, Y, hAY⟩
    · rw [hu] at h; exact TypeEq.sort_ne_ind hE hok h.symm
    · rw [hAY] at h; exact TypeEq.forallE_ne_ind hE hok h.symm
  · obtain ⟨l, hl'⟩ := TypeEq.sort_uniq hE hok hTE.symm
    obtain rfl := TypeEq.sort_inj hE hok (Defeq.uniqTy hE hok hl'.left hP)
    obtain ⟨_, _, -, -, hs⟩ := Defeq.ind_inv hl'.right
    exact hl (TypeEq.sort_inj hE hok hs).symm

/-- Erased dependencies of a closed substitution. -/
theorem deps_substl : ∀ {ts : List LBTerm} {b : LBTerm}, (∀ x ∈ ts, ErasesDeps E B σ lenv x) →
    ErasesDeps E B σ lenv b → ErasesDeps E B σ lenv (substl ts b)
  | [], _, _, hb => hb
  | x :: ts, b, hts, hb => by
    show ErasesDeps E B σ lenv (substl ts (csubst x 0 b))
    exact deps_substl (fun y hy => hts y (List.mem_cons_of_mem _ hy))
      (ErasesDeps.csubst (hts x (List.mem_cons_self ..)) hb)

/-! ### The reduced form: the alternative applied to `□` for each field -/

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

/-- `□` evaluates to itself only. -/
theorem lbeval_box {r : LBTerm} (h : LBEval defaultFlags lenv .box r) : r = .box := by
  generalize hx : LBTerm.box = y at h
  cases h with
  | atom => rfl
  | prim => cases hx
  | box | beta | zeta | iota | iotaBlock | iotaSing | fix | fixValue | fix' | delta | proj
  | projBlock | projProp | construct | constructBlock | appCong => cases hx

/-- An application of an erasable head is erasable. -/
theorem erasable_app (hE : EnvWF E) {F f : Lean.Expr} {F₀ f₀ G : Metalean.Expr ζ lps.length 0}
    (hF : ErasableS E B lps .nil [] F) (hF₀ : TrM E B lps .nil [] F F₀)
    (hf₀ : TrM E B lps .nil [] f f₀) (happ : E[.nil] ⊢ .app F₀ f₀ : G) :
    ErasableS E B lps .nil [] (.app F f) := by
  have hok := SrcDefeq.nil_ok (E := E) (lps := lps)
  obtain ⟨w, hw, Tw, hwT, hwA⟩ := hF
  obtain ⟨X, Y, hF₀T, -, -⟩ := happ.app_inv
  have hF₀E : IsErasable E .nil F₀ :=
    RelInst.IsErasable.of_defeq (SimCases.trM_defeq hE hw hF₀ hwT hF₀T) hwA
  obtain ⟨T', hT', hT'A⟩ := IsErasable.app hE hok hF₀E happ
  obtain ⟨t', ht', hred⟩ := TrM.apps hF₀ (.cons hf₀ .nil)
  rw [mkAppN_single] at ht'
  have hd' := WHRedS.defeq hE hok hred (by simpa using hT')
  exact ⟨t', ht', RelInst.IsErasable.of_defeq (by simpa using hd') hT'A⟩

/-- An erasure of a short spine headed by a constructor or a recognized `casesOn`: `□`, or an
erasure of its η-expansion. -/
theorem short_erases_inv {c : Name} {us : List Level} {as : List Lean.Expr} {ar : Nat}
    {F' : LBTerm} (har : specialArity σ c = some ar) (hlt : as.length < ar)
    (h : Erases E B lps σ .nil [] (mkAppN (.const c us) as.toArray) F') :
    (F' = .box ∧ ErasableS E B lps .nil [] (mkAppN (.const c us) as.toArray)) ∨
      ∃ e', σ.etaSpine? c us as = some e' ∧ Erases E B lps σ .nil [] e' F' := by
  have hfn := SrcDefeq.getAppFn_mkAppN_const c us as
  generalize hx : mkAppN (.const c us) as.toArray = x at h hfn
  cases h with
  | box hb => subst hx; exact .inl ⟨rfl, hb⟩
  | eta he h' =>
    obtain ⟨rfl, rfl, rfl⟩ := mkAppN_inj hx
    exact .inr ⟨_, he, h'⟩
  | ctor hc _ _ hle =>
    obtain ⟨rfl, -, rfl⟩ := mkAppN_inj hx
    unfold specialArity at har; rw [hc] at har; cases har; omega
  | cases hco _ _ _ hpre halts =>
    obtain ⟨rfl, -, rfl⟩ := mkAppN_inj hx
    rw [SimCases.specialArity_casesOn hco] at har; cases har
    simp only [List.length_append, List.length_singleton, hpre, halts, casesArity] at hlt
    omega
  | casesReduced hco _ hcs _ _ hpre =>
    obtain ⟨rfl, -, rfl⟩ := mkAppN_inj hx
    rw [SimCases.specialArity_casesOn hco] at har; cases har
    simp only [List.length_append, hpre, hcs, casesArity, List.length_cons, List.length_nil] at hlt
    omega
  | quotMk hcq hk _ _ | quotLift hcq hk _ _ _ =>
    obtain ⟨rfl, -, rfl⟩ := mkAppN_inj hx
    simp [specialArity, hcq, hk, quotEvalArity] at har
    subst har
    simp at hlt
    omega
  | recLet hcr | recFix hcr =>
    obtain ⟨rfl, -, -⟩ := mkAppN_inj hx
    rcases SrcDefeq.specialArity_some har with ⟨cv, hcv, -⟩ | ⟨iv, hiv⟩ | ⟨qv, hqv, -⟩
    · rw [hcr] at hcv; cases hcv
    · obtain ⟨d, hd⟩ := SrcDefeq.casesOn?_defn hiv
      rw [hcr] at hd; cases hd
    · rw [hcr] at hqv; cases hqv
  | app hns =>
    rcases SrcDefeq.specialArity_some har with ⟨cv, hcv, -⟩ | ⟨iv, hiv⟩ | ⟨qv, hqv, hq⟩
    · exact absurd ⟨c, us, hfn, .inl ⟨cv, hcv⟩⟩ hns
    · exact absurd ⟨c, us, hfn, .inr (.inl (by rw [hiv]; rfl))⟩ hns
    · exact absurd ⟨c, us, hfn, .inr (.inr (.inl ⟨qv, hqv, by rw [hq]; rfl⟩))⟩ hns
  | const _ hsa =>
    obtain ⟨-, rfl, -⟩ := SrcDefeq.spine_const hx
    rw [hsa] at har; cases har
  | bvar | fvar | lam | letE | proj | litZero | litSucc | mdata => cases hfn

/-- An erasure of a λ: `□`, or a λ□ λ erasing the body under the binder's translation. -/
theorem lam_erases_inv {x : Name} {A b : Lean.Expr} {bi : BinderInfo} {F' : LBTerm}
    (h : Erases E B lps σ .nil [] (.lam x A b bi) F') :
    (F' = .box ∧ ErasableS E B lps .nil [] (.lam x A b bi)) ∨
      ∃ A' b', F' = .lambda (binderNameOf x) b' ∧ TrM E B lps .nil [] A A' ∧
        E[.nil] ⊢ A' typ ∧ Erases E B lps σ (Metalean.Ctx.nil.snoc A') (MLCtx.pushLam [] none) b b' := by
  generalize hx : Expr.lam x A b bi = y at h
  cases h with
  | box hb => subst hx; exact .inl ⟨rfl, hb⟩
  | lam hA hAt hb => cases hx; exact .inr ⟨_, _, rfl, hA, hAt, hb⟩
  | ctor | cases | casesReduced | eta | quotMk | quotLift | recLet | recFix =>
    exact absurd hx (CasesWhred.ne_mkAppN_const fun _ _ h => by cases h)
  | bvar | fvar | letE | app | const | proj | litZero | litSucc | mdata => cases hx

/-- Appending an argument to an argument list related entrywise. -/
theorem forall_snoc_intro {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β} {x : α}
    {y : β} (hlen : l.length = l'.length)
    (h : ∀ (i : Nat) a b, l[i]? = some a → l'[i]? = some b → R a b) (hxy : R x y) :
    ∀ (i : Nat) a b, (l ++ [x])[i]? = some a → (l' ++ [y])[i]? = some b → R a b := by
  intro i a b ha hb
  by_cases hi : i < l.length
  · rw [List.getElem?_append_left hi] at ha
    rw [List.getElem?_append_left (by omega)] at hb
    exact h i a b ha hb
  · rw [List.getElem?_append_right (by omega)] at ha
    rw [List.getElem?_append_right (by omega)] at hb
    have : i - l.length = 0 := by
      have := (List.getElem?_eq_some_iff.mp ha).1; simp at this; omega
    rw [this] at ha
    rw [show i - l'.length = 0 by omega] at hb
    cases ha; cases hb; exact hxy

/-- One erasable field applied to an erased head: an erasure of the application whose λ□
evaluations are those of the erased head applied to `□`. -/
theorem appBox_step (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv σ.decls P)
    {F f : Lean.Expr} {F' : LBTerm} {F₀ f₀ G : Metalean.Expr ζ lps.length 0}
    (hF : Erases E B lps σ .nil [] F F') (hdF : ErasesDeps E B σ lenv F')
    (hF₀ : TrM E B lps .nil [] F F₀) (hf₀ : TrM E B lps .nil [] f f₀)
    (happ : E[.nil] ⊢ .app F₀ f₀ : G) (hval : SrcValue σ f)
    (herf : ErasableS E B lps .nil [] f) :
    ∃ G', Erases E B lps σ .nil [] (.app F f) G' ∧ ErasesDeps E B σ lenv G' ∧
      ∀ r, LBEval defaultFlags lenv G' r → LBEval defaultFlags lenv (.app F' .box) r := by
  have hok := SrcDefeq.nil_ok (E := E) (lps := lps)
  have hord := henv.metaOrderOK
  have hbox : F' = .box → ErasableS E B lps .nil [] F → ∃ G', Erases E B lps σ .nil [] (.app F f) G' ∧
      ErasesDeps E B σ lenv G' ∧
      ∀ r, LBEval defaultFlags lenv G' r → LBEval defaultFlags lenv (.app F' .box) r := by
    rintro rfl hb
    refine ⟨.box, .box (erasable_app hE hb hF₀ hf₀ happ), .box, fun r hr => ?_⟩
    rw [lbeval_box hr]
    exact .box (.atom rfl) (.atom rfl)
  by_cases hsp : SpecialSpine σ (.app F f)
  swap
  · exact ⟨.app F' .box, .app hsp hF (.box herf), .app hdF .box, fun _ h => h⟩
  obtain ⟨c, us, hfn, hspc⟩ := hsp
  have hfnF : F.getAppFn = .const c us := by simpa [Expr.getAppFn] using hfn
  obtain ⟨as, rfl⟩ := eq_mkAppN_of_getAppFn hfnF
  have hjoin : Expr.app (mkAppN (.const c us) as.toArray) f =
      mkAppN (.const c us) (as ++ [f]).toArray := by
    rw [mkAppN_eq_foldl, mkAppN_eq_foldl, List.foldl_append]; rfl
  by_cases hrc : ∃ rv, findDecl σ.decls c = some (.recInfo rv)
  · obtain ⟨rv, hrv⟩ := hrc
    rcases Erases.rec_inv hrv hF with ⟨hF', hb⟩ |
      ⟨minors, Fx, ps, ms, mins, is, maj, extra, mins', is', maj', extra', hRF, rfl, hps, hms,
        hmins, his, hlm, hmin, hli, his', hmaj, hle, hext, rfl⟩ |
      ⟨minors, Fx, ps, ms, mins, is, maj, extra, ws, is', maj', extra', hRF, rfl, hps, hms, hmins,
        his, hlw, hmin, hws, hli, his', hmaj, hle, hext, rfl⟩
    · exact hbox hF' hb
    · refine ⟨mkApps (recLets 0 (mins'.zip minors)
        (mkApps Fx ((is' ++ [maj']).map (lbLift rv.numMinors 0)))) (extra' ++ [.box]), ?_, ?_, ?_⟩
      · rw [hjoin, show ps ++ ms ++ mins ++ is ++ [maj] ++ extra ++ [f] =
          ps ++ ms ++ mins ++ is ++ [maj] ++ (extra ++ [f]) by simp]
        exact .recLet hrv hRF hps hms hmins his hlm hmin hli his' hmaj (by simp [hle])
          (forall_snoc_intro hle hext (.box herf))
      · rw [SimCases.mkApps_snoc]; exact .app hdF .box
      · intro r h; rwa [SimCases.mkApps_snoc] at h
    · refine ⟨mkApps (substl ws.reverse Fx) (is' ++ [maj'] ++ (extra' ++ [.box])), ?_, ?_, ?_⟩
      · rw [hjoin, show ps ++ ms ++ mins ++ is ++ [maj] ++ extra ++ [f] =
          ps ++ ms ++ mins ++ is ++ [maj] ++ (extra ++ [f]) by simp]
        exact .recFix hrv hRF hps hms hmins his hlw hmin hws hli his' hmaj (by simp [hle])
          (forall_snoc_intro hle hext (.box herf))
      · rw [← List.append_assoc, SimCases.mkApps_snoc]; exact .app hdF .box
      · intro r h; rwa [← List.append_assoc, SimCases.mkApps_snoc] at h
  obtain ⟨ar, har⟩ : ∃ ar, specialArity σ c = some ar := by
    rcases hspc with ⟨cv, hcv⟩ | hco | ⟨qv, hqv, hq⟩ | ⟨rv, hrv⟩
    · exact ⟨_, by unfold specialArity; rw [hcv]⟩
    · obtain ⟨iv, hiv⟩ := Option.isSome_iff_exists.mp hco
      exact ⟨_, SimCases.specialArity_casesOn hiv⟩
    · obtain ⟨ar, har⟩ := Option.isSome_iff_exists.mp hq
      exact ⟨ar, by unfold specialArity; rw [hqv]; exact har⟩
    · exact absurd ⟨rv, hrv⟩ hrc
  by_cases hlt : as.length < ar
  · rcases short_erases_inv har hlt hF with ⟨hF', hb⟩ | ⟨e', heta, he'⟩
    · exact hbox hF' hb
    obtain ⟨x, A, b, bi, rfl⟩ := SimInd.etaSpine?_lam heta
    obtain ⟨X, Y, hF₀T, hf₀X, -⟩ := happ.app_inv
    obtain ⟨tl, htl, hdl⟩ := SrcEval.defeq henv hE hsub hF₀ hF₀T (.eta heta)
    rcases lam_erases_inv he' with ⟨rfl, hb⟩ | ⟨A', b', rfl, hA', hA't, hb'⟩
    · -- the η-expansion is erasable, hence so is the spine
      obtain ⟨w, hw, Tw, hwT, hwA⟩ := hb
      have htlE : IsErasable E .nil tl :=
        RelInst.IsErasable.of_defeq (SimCases.trM_defeq hE hw htl hwT hdl.right) hwA
      obtain ⟨Tl, hTl, hTlA⟩ := htlE
      exact hbox rfl ⟨F₀, hF₀, RelInst.IsErasable.of_defeq
        (Defeq.retype hE hok hdl.symm hTl) hTlA⟩
    obtain ⟨A₀, b₀, rfl, hA₀, hb₀⟩ := SimCases.trM_lam_inv htl
    obtain ⟨T₀, hb₀T, hπ⟩ := hdl.right.lam_inv hok
    have hf₀A₀ : E[.nil] ⊢ f₀ : A₀ := (TypeEq.forallE_inj hE hok hπ).1.conv hf₀X
    obtain ⟨u, hA₀u⟩ := hf₀A₀.regular
    obtain ⟨l, hl⟩ := hA't
    have hAA : E[.nil] ⊢ A₀ ≡ A' : .sort u := SimCases.trM_defeq hE hA₀ hA' hA₀u hl
    have hb₀T' := Defeq.snocConv hAA hb₀T
    have hokA : E[Metalean.Ctx.nil.snoc A'] ⊢ ok := .snoc hok ⟨l, hl⟩
    have htb' := InstPre.PreTr.recover hord (InstPre.PreTr.ofTrM hb₀) (InstPre.Thin.id _) hokA
      ⟨T₀, by rw [Metalean.Expr.rename_id]; exact hb₀T'⟩
    have hinst := Erases.inst henv hE hok hsub hval hb' htb' hb₀T' (.box herf) hf₀
      (Defeq.defeqDF hAA hf₀A₀) rfl
    obtain ⟨ar', har', -, hs1, hs2⟩ := etaSpine?_snoc f heta
    rw [har] at har'
    cases har'
    cases hdF with
    | lambda hdb =>
    refine ⟨csubst .box 0 b', ?_, ErasesDeps.csubst .box hdb,
      fun r h => .beta (.atom rfl) (.atom rfl) h⟩
    rw [hjoin]
    rcases Nat.lt_or_eq_of_le (show as.length + 1 ≤ ar by omega) with h1 | h1
    · exact .eta (hs1 h1) hinst
    · rw [← hs2 h1]; exact hinst
  · rcases SrcDefeq.specialArity_some har with ⟨cv, hcv, rfl⟩ | ⟨iv, hiv⟩ | ⟨qv, hqv, hq⟩
    rotate_left 2
    · rcases Erases.quot_inv hqv hq (by omega) hF with ⟨hF', hb⟩ |
        ⟨α, r, a, extra, a', extra', hk, rfl, ha, hlex, hext, rfl⟩ |
        ⟨α, r, β, f₁, h₁, q, extra, f', q', extra', hk, rfl, hf₁, hq₁, hlex, hext, rfl⟩
      · exact hbox hF' hb
      · refine ⟨mkApps a' (extra' ++ [.box]), ?_, ?_, ?_⟩
        · rw [hjoin, List.append_assoc]
          exact .quotMk hqv hk ha (by simp [hlex]) (forall_snoc_intro hlex hext (.box herf))
        · rw [SimCases.mkApps_snoc]; exact .app hdF .box
        · intro r h; rwa [SimCases.mkApps_snoc] at h
      · refine ⟨mkApps f' (q' :: (extra' ++ [.box])), ?_, ?_, ?_⟩
        · rw [hjoin, List.append_assoc]
          exact .quotLift hqv hk hf₁ hq₁ (by simp [hlex]) (forall_snoc_intro hlex hext (.box herf))
        · rw [← List.cons_append, SimCases.mkApps_snoc]; exact .app hdF .box
        · intro r h; rwa [← List.cons_append, SimCases.mkApps_snoc] at h
    · rcases Erases.ctor_inv hcv (by omega) hF with ⟨hF', hb⟩ | ⟨iid, as', hid, rfl, hlen, hall⟩
      · exact hbox hF' hb
      have hnp : ¬ PropInductive E B cv.induct := fun hp =>
        SimInd.mkApps_construct_ne_box (Erases.ctorProp_box hcv hp (by omega) hF)
      refine ⟨mkApps (.construct iid cv.cidx []) (as' ++ [.box]), ?_, ?_, ?_⟩
      · rw [hjoin]
        exact .ctor hcv hnp hid (by simp; omega) (by simp [hlen])
          (forall_snoc_intro hlen hall (.box herf))
      · rw [SimCases.mkApps_snoc]; exact .app hdF .box
      · intro r h; rwa [SimCases.mkApps_snoc] at h
    · rw [SimCases.specialArity_casesOn hiv] at har
      cases har
      rcases Erases.cases_inv hiv (by omega) hF with ⟨hF', hb⟩ |
        ⟨pre, maj, alts, extra, iid, maj', brs, extra', rfl, hnr, hss, hid, hpre, halts, hmaj,
          hbrs, hcf, halt, hlex, hext, rfl⟩ |
        ⟨pre, maj, alt, extra, cn, cv, alt', extra', rfl, hfe, hcn, hcv, hidx, hpre, halt, hlex,
          hext, rfl⟩
      · exact hbox hF' hb
      · refine ⟨mkApps (.case (iid, iv.numParams) maj' brs) (extra' ++ [.box]), ?_, ?_, ?_⟩
        · rw [hjoin, show pre ++ [maj] ++ alts ++ extra ++ [f] =
            pre ++ [maj] ++ alts ++ (extra ++ [f]) by simp]
          exact .cases hiv hnr hss hid hpre halts hmaj hbrs hcf halt (by simp [hlex])
            (forall_snoc_intro hlex hext (.box herf))
        · rw [SimCases.mkApps_snoc]; exact .app hdF .box
        · intro r h; rwa [SimCases.mkApps_snoc] at h
      · refine ⟨mkApps alt' (List.replicate cv.numFields .box ++ (extra' ++ [.box])), ?_, ?_, ?_⟩
        · rw [hjoin, show pre ++ [maj] ++ [alt] ++ extra ++ [f] =
            pre ++ [maj] ++ [alt] ++ (extra ++ [f]) by simp]
          exact .casesReduced hiv hfe hcn hcv hidx hpre halt (by simp [hlex])
            (forall_snoc_intro hlex hext (.box herf))
        · rw [← List.append_assoc, SimCases.mkApps_snoc]; exact .app hdF .box
        · intro r h; rwa [← List.append_assoc, SimCases.mkApps_snoc] at h

/-- Erasable fields applied to an erased head: an erasure of the application whose λ□
evaluations are those of the erased head applied to `□` for each field. -/
theorem appBox (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv σ.decls P) :
    ∀ {fs : List Lean.Expr} {fs₀ : List (Metalean.Expr ζ lps.length 0)},
      List.Forall₂ (TrM E B lps .nil []) fs fs₀ →
      (∀ f ∈ fs, SrcValue σ f ∧ ErasableS E B lps .nil [] f) →
      ∀ {F : Lean.Expr} {F' : LBTerm} {F₀ : Metalean.Expr ζ lps.length 0},
      Erases E B lps σ .nil [] F F' → ErasesDeps E B σ lenv F' → TrM E B lps .nil [] F F₀ →
      (∃ T, E[.nil] ⊢ F₀.appList fs₀ : T) →
      ∃ G', Erases E B lps σ .nil [] (mkAppN F fs.toArray) G' ∧ ErasesDeps E B σ lenv G' ∧
        ∀ r, LBEval defaultFlags lenv G' r →
          LBEval defaultFlags lenv (mkApps F' (List.replicate fs.length .box)) r := by
  have hok := SrcDefeq.nil_ok (E := E) (lps := lps)
  intro fs fs₀ hfs
  induction hfs with
  | nil =>
    intro _ F F' F₀ hF hdF _ _
    exact ⟨F', by rw [mkAppN_eq_foldl]; exact hF, hdF, fun _ h => h⟩
  | @cons f f₀ fs fs₀ hf₀ _ ih =>
    intro hfv F F' F₀ hF hdF hF₀ hT
    obtain ⟨T, hT⟩ := hT
    rw [Metalean.Expr.appList_cons] at hT
    obtain ⟨⟨G, hG⟩, -⟩ := InstPre.appList_inv hT
    obtain ⟨hval, herf⟩ := hfv f (List.mem_cons_self ..)
    obtain ⟨G₁, hG₁, hdG₁, hevG₁⟩ := appBox_step henv hE hsub hF hdF hF₀ hf₀ hG hval herf
    obtain ⟨t₁, ht₁, hred₁⟩ := TrM.apps hF₀ (List.Forall₂.cons hf₀ .nil)
    rw [mkAppN_single] at ht₁
    have hd₁ := WHRedS.defeq hE hok hred₁ (by simpa using hG)
    obtain ⟨T', hT'⟩ := SatTyped.appList_defeq hE hok fs₀ hd₁.symm hT
    obtain ⟨G', hG', hdG', hevG'⟩ :=
      ih (fun g hg => hfv g (List.mem_cons_of_mem _ hg)) hG₁ hdG₁ ht₁ ⟨T', hT'⟩
    refine ⟨G', by rw [mkAppN_cons]; exact hG', hdG', fun r h => ?_⟩
    show LBEval defaultFlags lenv (mkApps (.app F' .box) (List.replicate fs.length .box)) r
    exact lbeval_mkApps_congr _ hevG₁ (hevG' r h)

/-- The fields of a typed constructor value of an inductive whose fields are erasable
(`FieldsErasable`) are erasable: each field's translation is one of the node's fields
(constructor field orders are permutations). -/
theorem fields_erasable (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv σ.decls P)
    {C : Name} {us : List Level} {cv : ConstructorVal} {ps fs : List Lean.Expr}
    {m' U : Metalean.Expr ζ lps.length 0} (hC : findDecl σ.decls C = some (.ctorInfo cv))
    (hps : ps.length = cv.numParams) (hfs : fs.length = cv.numFields)
    (hm' : TrM E B lps .nil [] (mkAppN (.const C us) (ps ++ fs).toArray) m')
    (hT : E[.nil] ⊢ m' : U) (hfe : FieldsErasable E B cv.induct) :
    ∀ f ∈ fs, ErasableS E B lps .nil [] f := by
  have hok := SrcDefeq.nil_ok (E := E) (lps := lps)
  obtain ⟨ι, η, s, k, o, hB, -, hnp, hnf, hord, hI⟩ :=
    henv.lookup_ctor (SrcDefeq.findDecl_sub hsub hC)
  obtain ⟨bs', hlen', hargs, hsat⟩ := TrM.special_inv hB rfl hm'
  cases hsat with
  | ctorEta _ hlt _ => simp at hlen' hlt; omega
  | ctorSat ps₀ fs'' rest fds rfs hls hfs'' hord' hmap =>
  simp only [List.length_append, List.length_ofFn] at hlen'
  have hr : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst hr
  simp only [List.append_nil, Metalean.Expr.appList_nil] at hT hargs
  obtain ⟨hfd, hrf⟩ := hfe ι η s hI .nil k _ ps₀ fds rfs hE hok ⟨U, hT⟩
  have happ : ∀ q, IsErasable E .nil (Fin.append fds rfs q) := fun q =>
    Fin.addCases (fun i => by rw [Fin.append_left]; exact hfd i)
      (fun i => by rw [Fin.append_right]; exact hrf i) q
  obtain ⟨-, -, -, -, -, -, -, hperm⟩ := hord
  intro f hf
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hf
  have hjo : j ∈ o := hperm.mem_iff.mpr (List.mem_range.mpr (by omega))
  obtain ⟨q, hq⟩ := List.mem_iff_getElem?.mp hjo
  have hqlt : q < (ι.ctors s k).nfields + (ι.ctors s k).nrecFields := by
    have := (List.getElem?_eq_some_iff.mp hq).1; omega
  obtain ⟨j', a, hj', ha, hqa⟩ := hmap ⟨q, hqlt⟩
  rw [hq] at hj'
  cases hj'
  refine ⟨a, hargs (cv.numParams + j) fs[j] a ?_ ?_, hqa ▸ happ _⟩
  · rw [List.getElem?_append_right (by omega), hps, Nat.add_sub_cancel_left]
    exact List.getElem?_eq_getElem hj
  · rw [List.getElem?_append_right (by simp; omega)]
    simpa [hnp] using ha

end

end SimIota

open SimIota

section
open Metalean
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P : List ConstantInfo}
  {σ : EvalEnv} {lps : List Name} {lenv : GlobalDeclarations}

/-- The `casesIota` case of `erases_correct`. The major's erasure evaluates to an erasure of the
constructor value: not `□` (the `casesOn` is not reduced at erasure time and its inductive is a
subsingleton only if it has one constructor, so the value's inductive is not at level `0`, using
`ArityTypes` to read the discriminant's sort), so a λ□ constructor applied to erasures of the
parameters and fields; λ□'s ι substitutes the fields' erasures into the erased branch, which
erases a head-β-reduct of the alternative applied to the fields (`SimIota.drive`), whose
evaluation is the induction hypothesis `ihb`. Reference: the `eval_iota` case of
`erases_correct` (`MR E/ErasureCorrectness.v:182`). -/
theorem erases_correct_casesIota (henv : ProgEnv P ζ E B) (hE : EnvWF E)
    (hsub : SubEnv σ.decls P) (hbinj : BlockNamesInj σ.decls) (harity : ArityTypes σ.decls)
    {c : Name} {us : List Level} {iv : InductiveVal} {as fs : List Lean.Expr}
    {m mv alt v : Lean.Expr} {i : Nat}
    (hcs : σ.casesOn? c = some iv) (hlen : as.length = casesArity iv)
    (hm : as[casesMajor iv]? = some m) (hmv : SrcEval σ m mv) (hcv : CtorValue σ iv.name mv i fs)
    (halt : as[casesMajor iv + 1 + i]? = some alt) (hv : SrcEval σ (mkAppN alt fs.toArray) v)
    (ihm : ErasesSim E B lps σ lenv m mv)
    (ihb : ∀ X, HeadBeta σ (mkAppN alt fs.toArray) X → ErasesSim E B lps σ lenv X v) :
    ErasesSim E B lps σ lenv (mkAppN (.const c us) as.toArray) v := by
  intro t tb he ⟨T, ht⟩ her hdeps
  have hok := SrcDefeq.nil_ok (E := E) (lps := lps)
  have hsrc : SrcEval σ (mkAppN (.const c us) as.toArray) v :=
    .casesIota hcs hlen hm hmv hcv halt hv
  have hivD := SimInd.casesOn?_ind hcs
  -- the spine with the major's value: recursor form and ι form
  have hsnd : SrcDefeq.Sound E B lps m mv := fun he ht => SrcEval.defeq henv hE hsub he ht hmv
  obtain ⟨t₂, ht₂, hd2⟩ := SrcDefeq.major_congr henv hE hsub hcs hm hsnd he ht
  have hjlt : casesMajor iv < as.length := (List.getElem?_eq_some_iff.mp hm).1
  obtain ⟨ι, η, s, L, l', ps₀, ms, mins, is₀, m', hBT, hm', hredR, hlev, -, -⟩ :=
    SrcProof.casesOn_recr henv hE hsub hcs (by simp [hlen]) (List.getElem?_set_self hjlt) ht₂
  have hR := (WHRedS.defeq hE hok hredR hd2.right).right
  obtain ⟨-, hps₀, -, -, his₀, hmaj⟩ := Defeq.recr_typed hE hok hR
  have hj : casesMajor iv + 1 < as.length := by
    have := (List.getElem?_eq_some_iff.mp halt).1; omega
  obtain ⟨args, a, hsplit, hlen₂, hm₂, hrest⟩ := SrcDefeq.split_set mv hj
  have ht₂' := ht₂
  rw [hsplit] at ht₂'
  obtain ⟨alt₀, fs₀, halt₀, hfs₀, hredI⟩ := CasesWhred.casesOn_whred_spine henv hsub hcs (by omega)
    hm₂ hcv (by rw [hrest _ (by omega)]; exact halt) ht₂'
  have hI : ∃ T, E[.nil] ⊢ alt₀.appList fs₀ : T := ⟨T, (WHRedS.defeq hE hok hredI hd2.right).right⟩
  have hfields := fields_of_eval hmv hcv
  obtain ⟨C, us', cv, ps, hC, hind, hcidx, hps, hfs, rfl⟩ := hcv
  have hlenC : (ps ++ fs).length = cv.numParams + cv.numFields := by simp [hps, hfs]
  obtain ⟨ι', η', s', c', ls, ps', fds, rfs, hBC, rfl⟩ := SimInd.ctorNode_tr henv hsub hC hlenC hm'
  rw [hind, hBT] at hBC
  cases hBC
  obtain ⟨hCi, hnpI⟩ := SimInd.ctor_block henv hsub hC (by rw [hind]; exact hivD)
  obtain ⟨ι₂, η₂, s₂, hB₂, -, -, hnc⟩ := henv.lookup_ind (SrcDefeq.findDecl_sub hsub hivD)
  rw [hBT] at hB₂
  cases hB₂
  have hnc' : iv.ctors.length = ι.nctors s := hnc
  have hipos : cv.cidx < iv.ctors.length := (List.getElem?_eq_some_iff.mp hCi).1
  rcases Erases.cases_inv hcs (by omega) her with ⟨rfl, hbx⟩ |
    ⟨pre, maj, alts, extra, iid, maj', brs, extra', rfl, hnr, hss, hid, hpre, halts, hmaj', hbrs,
      hcf, halt', hlex, -, rfl⟩ |
    ⟨pre, maj, alt₁, extra, cn, cv', alt', extra', rfl, hfe, hcn, hcv', -, hpre, halt₁, hlex, -,
      rfl⟩
  · exact erases_correct_box henv hE hsub he ht hbx hsrc
  · -- a λ□ `case`
    have hex : extra = [] := by
      apply List.eq_nil_of_length_eq_zero
      simp only [List.length_append, List.length_singleton, hpre, casesArity, halts] at hlen
      omega
    subst hex
    obtain rfl : extra' = [] := List.eq_nil_of_length_eq_zero hlex.symm
    have hmaj'' : maj = m := by
      rw [← hpre, List.append_assoc, SimInd.get_major] at hm
      simpa using hm
    subst hmaj''
    cases hdeps with
    | case hidT hindT hdmaj hdbrs =>
    rw [SimInd.indIdOf_inj hbinj hidT hid] at hindT
    -- the major's erasure evaluates to an erasure of the constructor value
    obtain ⟨m₀, M, hm₀, hM⟩ := SimInd.casesOn_arg henv hsub hcs hm he ht
    obtain ⟨mb, hmb, hevmb⟩ := ihm hm₀ ⟨M, hM⟩ hmaj' hdmaj
    -- the inductive is not at level `0`
    have hnz : (E.get η).block.level{L} ≠ .zero := by
      intro hz
      by_cases h1 : iv.ctors.length = 1
      · have harS := harity iv ⟨_, (findDecl_eq_some hivD).1, rfl⟩
        obtain ⟨⟨n, u⟩, hau⟩ := Option.isSome_iff_exists.mp harS
        have hl₀ : casesSortLevel iv us = some (Pure.instLevel iv.levelParams
            (us.drop (us.length - iv.levelParams.length)) u) := by
          simp [casesSortLevel, hau]
        have hnz₀ : (Pure.instLevel iv.levelParams
            (us.drop (us.length - iv.levelParams.length)) u).isNeverZero = true := by
          cases hz' : (Pure.instLevel iv.levelParams
              (us.drop (us.length - iv.levelParams.length)) u).isNeverZero
          · exact absurd ⟨h1, _, hl₀, hz'⟩ hnr
          · rfl
        have := SimInd.isNeverZero_tr hnz₀ (hlev _ hl₀) (fun _ => 0)
        rw [hz, Metalean.Level.eval_zero] at this
        omega
      · have hind' := Defeq.indDF hps₀ his₀
        rw [hz] at hind'
        have hprf : IsProof E .nil (.ctor η s c' ls ps' fds rfs) := ⟨_, hmaj, hind'⟩
        have := (hss ι η s hBT .nil c' ls ps' fds rfs hE hok hprf).1
        omega
    rcases Erases.ctor_inv hC (by omega) hmb with ⟨rfl, hbx⟩ | ⟨iid', as', hid', rfl, hlen', hall⟩
    · exfalso
      obtain ⟨w, hw, Tw, hwT, hwA⟩ := hbx
      exact ind_not_erasable hE hmaj hnz
        (RelInst.IsErasable.of_defeq (SimCases.trM_defeq hE hw hm' hwT hmaj) hwA)
    rw [hind, hid] at hid'
    cases hid'
    have hnp : ¬ PropInductive E B cv.induct := fun hp =>
      SimInd.mkApps_construct_ne_box (Erases.ctorProp_box hC hp (by omega) hmb)
    obtain ⟨mib, ob, cb, hlk, hnpars, hnargs, hprop⟩ :=
      SimInd.lookupCtor_of henv hsub hC (by rw [hind]; exact hid) (by rw [hind]; exact hindT)
    have hpf : ob.propositional = false := by
      cases h : ob.propositional
      · rfl
      · exact absurd (hprop.mp h) hnp
    -- the alternative and its branch
    have halti : alts[cv.cidx]? = some alt := by
      have := SimInd.get_alt pre alts [] maj (j := cv.cidx) (by omega)
      rw [hpre, hcidx] at this
      rw [hcidx, ← this]
      simpa using halt
    obtain ⟨br, hbr⟩ : ∃ br, brs[cv.cidx]? = some br :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hk : ctorFields σ C = some cv.numFields := by unfold ctorFields; rw [hC]
    obtain ⟨ns, tbr⟩ := br
    have halt'' := halt' _ C alt _ _ hCi halti hbr hk
    -- the fields
    have hfs' : (as'.drop cv.numParams).length = fs.length := by simp; omega
    have hok' : List.Forall₂ (FieldOK E B lps σ) fs (as'.drop cv.numParams) := by
      refine CasesWhred.forall₂_of_getElem? hfs'.symm fun j f f' hf hf' => ?_
      obtain ⟨hsv, hfx⟩ := hfields f (List.mem_of_getElem? hf)
      have hf'' : as'[cv.numParams + j]? = some f' := by
        rw [List.getElem?_drop] at hf'; exact hf'
      have hpf' : (ps ++ fs)[cv.numParams + j]? = some f := by
        rw [List.getElem?_append_right (by omega), hps, Nat.add_sub_cancel_left]; exact hf
      have herf := hall _ _ _ hpf' hf''
      obtain ⟨f₀, hf₀, hff₀⟩ := CasesWhred.forall₂_getElem? hfs₀ hf
      exact ⟨hsv, hfx, herf, SimCases.closed0 hff₀ herf⟩
    rw [← hfs] at halt''
    obtain ⟨X, tX, hXb, hXe, hXt, hXT⟩ := drive henv hE hsub hok' halt'' halt₀ hfs₀ hI
    have hdmb := ErasesDeps.eval hdmaj hevmb
    obtain ⟨-, hdargs⟩ := SimInd.deps_mkApps hdmb
    have hdX : ErasesDeps E B σ lenv (substl (as'.drop cv.numParams).reverse tbr) :=
      deps_substl (fun x hx => hdargs x (List.mem_of_mem_drop (List.mem_reverse.mp hx)))
        (hdbrs _ (List.mem_of_getElem? hbr))
    obtain ⟨vb, hvb, hevb⟩ := ihb X hXb hXt hXT hXe hdX
    refine ⟨vb, hvb, .iota (args := as') (cdecl := cb) rfl hevmb ?_ hbr ?_ ?_ ?_⟩
    · show (lookupCtor lenv iid cv.cidx).map _ = _
      rw [hlk]
      simp [hpf, hnpars, hnpI]
    · rw [← hlen', hlenC, hnpI, hnargs]
    · rw [hnpI, hfs', erasesAlt_length halt'']
    · rw [hnpI]; exact hevb
  · -- the reduced form: the alternative applied to `□` for each field
    have hcn1 : iv.ctors.length = 1 := by rw [hcn]; rfl
    have hex : extra = [] := by
      apply List.eq_nil_of_length_eq_zero
      simp only [List.length_append, List.length_singleton, hpre, casesArity, hcn1] at hlen
      omega
    subst hex
    obtain rfl : extra' = [] := List.eq_nil_of_length_eq_zero hlex.symm
    have hi0 : cv.cidx = 0 := by omega
    rw [hcn, hi0] at hCi
    cases hCi
    rw [hC] at hcv'
    cases hcv'
    have halt₁' : alt₁ = alt := by
      rw [hcidx.symm.trans hi0, Nat.add_zero, ← hpre] at halt
      simpa using halt
    subst halt₁'
    have hdalt : ErasesDeps E B σ lenv alt' := (SimInd.deps_mkApps hdeps).1
    have hfv : ∀ f ∈ fs, SrcValue σ f ∧ ErasableS E B lps .nil [] f := fun f hf =>
      ⟨(hfields f hf).1, fields_erasable henv hE hsub hC hps hfs hm' hmaj (hind ▸ hfe) f hf⟩
    obtain ⟨G', hG', hdG', hevG'⟩ := appBox henv hE hsub hfs₀ hfv halt₁ hdalt halt₀ hI
    obtain ⟨tA, htA, hredA⟩ := TrM.apps halt₀ hfs₀
    obtain ⟨TI, hTI⟩ := hI
    have htAT := (WHRedS.defeq hE hok hredA hTI).right
    obtain ⟨vb, hvb, hevb⟩ := ihb _ .refl htA ⟨_, htAT⟩ hG' hdG'
    refine ⟨vb, hvb, ?_⟩
    rw [List.append_nil, ← hfs]
    exact hevG' vb hevb

/-- The `casesLitSucc` case of `erases_correct`: `Nat` has two constructors, so its `casesOn` is
not reduced at erasure time and the major's erasure evaluates to the erasure of `k + 1`, λ□'s `Nat`
constructor `1` applied to an erasure of `k` (`□` is excluded: `Subsingleton` fails on `Nat`); λ□'s
ι substitutes it into the erased second alternative, which erases a head-β-reduct of the
alternative applied to `k` (`SimIota.drive`). Reference: the `eval_iota` case of
`erases_correct` (`MR E/ErasureCorrectness.v:182`) on a successor literal. -/
theorem erases_correct_casesLitSucc (henv : ProgEnv P ζ E B) (hE : EnvWF E)
    (hsub : SubEnv σ.decls P) (hbinj : BlockNamesInj σ.decls) {c : Name} {us : List Level}
    {iv : InductiveVal} {as : List Lean.Expr} {m alt v : Lean.Expr} {k : Nat}
    (hcs : σ.casesOn? c = some iv) (hnat : iv.name = ``Nat) (hlen : as.length = casesArity iv)
    (hm : as[casesMajor iv]? = some m) (hmv : SrcEval σ m (.lit (.natVal (k + 1))))
    (halt : as[casesMajor iv + 2]? = some alt) (hv : SrcEval σ (.app alt (.lit (.natVal k))) v)
    (ihm : ErasesSim E B lps σ lenv m (.lit (.natVal (k + 1))))
    (ihb : ∀ X, HeadBeta σ (.app alt (.lit (.natVal k))) X → ErasesSim E B lps σ lenv X v) :
    ErasesSim E B lps σ lenv (mkAppN (.const c us) as.toArray) v := by
  intro t tb he ⟨T, ht⟩ her hdeps
  have hok := SrcDefeq.nil_ok (E := E) (lps := lps)
  have hsrc : SrcEval σ (mkAppN (.const c us) as.toArray) v :=
    .casesLitSucc hcs hnat hlen hm hmv halt hv
  -- the Metalean `Nat`
  obtain ⟨m₀, M, hm₀, hM⟩ := SimInd.casesOn_arg henv hsub hcs hm he ht
  obtain ⟨z₀, hz₀, hdz⟩ := SrcEval.defeq henv hE hsub hm₀ hM hmv
  obtain ⟨ηNat, hB, rfl⟩ := CasesWhred.trM_lit_inv hz₀
  have hivN := SimInd.casesOn?_ind hcs
  rw [hnat] at hivN
  have hivP := SrcDefeq.findDecl_sub hsub hivN
  obtain ⟨ι', η', s', hB', hpI, -, hnc⟩ := henv.lookup_ind hivP
  rw [hB] at hB'
  cases hB'
  have hnc2 : iv.ctors.length = 2 := hnc
  have hnp0 : iv.numParams = 0 := hpI
  -- a successor literal is no proof of a subsingleton `Nat`
  have hnotProof : Subsingleton E B iv.name →
      ¬ IsProof E .nil (natLitM ηNat (k + 1) : Metalean.Expr ζ lps.length 0) := by
    intro hss hpr
    exact absurd (hss natSig ηNat 0 (by rw [hnat]; exact hB) .nil 1 _ _ _ _ hE hok hpr).1
      (by decide)
  -- the ι form with the major's value
  have hsnd : SrcDefeq.Sound E B lps m (.lit (.natVal (k + 1))) :=
    fun he ht => SrcEval.defeq henv hE hsub he ht hmv
  obtain ⟨t₂, ht₂, hd2⟩ := SrcDefeq.major_congr henv hE hsub hcs hm hsnd he ht
  have hj : casesMajor iv + 1 < as.length := by
    have := (List.getElem?_eq_some_iff.mp halt).1; omega
  obtain ⟨args, a, hsplit, hlen₂, hm₂, hrest⟩ := SrcDefeq.split_set (.lit (.natVal (k + 1))) hj
  rw [hsplit] at ht₂
  obtain ⟨alt₁, alt₀, fs₀, halt₁, halt₀, hfs₀, hredI⟩ :=
    CasesWhred.casesOnLit_whred_spine henv hsub hcs hnat (by omega) hm₂ ht₂
  rw [hrest _ (by omega), show casesMajor iv + 1 + min (k + 1) 1 = casesMajor iv + 2 by omega,
    halt, Option.some.injEq] at halt₁
  subst halt₁
  simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at hfs₀
  have hI : ∃ T, E[.nil] ⊢ alt₀.appList fs₀ : T := ⟨T, (WHRedS.defeq hE hok hredI hd2.right).right⟩
  rcases Erases.cases_inv hcs (by omega) her with ⟨rfl, hbx⟩ |
    ⟨pre, maj, alts, extra, iid, maj', brs, extra', rfl, -, hss, hid, hpre, halts, hmaj, hbrs, hcf,
      halt', hlex, -, rfl⟩ |
    ⟨-, -, -, -, cn', -, -, -, -, -, hcn', -⟩
  · exact erases_correct_box henv hE hsub he ht hbx hsrc
  rotate_left
  · rw [hcn'] at hnc2; simp at hnc2
  have hex : extra = [] := by
    apply List.eq_nil_of_length_eq_zero
    simp only [List.length_append, List.length_singleton, hpre, casesArity, halts] at hlen
    omega
  subst hex
  obtain rfl : extra' = [] := List.eq_nil_of_length_eq_zero hlex.symm
  have hmaj' : maj = m := by
    rw [← hpre, List.append_assoc, SimInd.get_major] at hm
    simpa using hm
  subst hmaj'
  cases hdeps with
  | case hidT hindT hdmaj hdbrs =>
  rw [SimInd.indIdOf_inj hbinj hidT hid] at hindT
  rw [hnat] at hid hindT
  -- the major
  obtain ⟨mb, hmb, hevmb⟩ := ihm hm₀ ⟨M, hM⟩ hmaj hdmaj
  obtain ⟨mib, ob, cb, hlk, hnpars, hnargs, hprop⟩ :=
    SimInd.lookupCtor_ind henv hsub hB hid hindT 1
  have hpf : ob.propositional = false := by
    cases h : ob.propositional
    · rfl
    · obtain ⟨ι', η', s', hB', hl⟩ := hprop.mp h
      rw [hB] at hB'
      cases hB'
      have hz := hdz.right
      simp only [natLitM] at hz
      obtain ⟨_, _, _, -, -, -, hind, hT'⟩ := Defeq.ctor_inv hz
      have := hind.left
      rw [hl, Metalean.Level.inst_zero] at this
      exact (hnotProof hss ⟨_, hT'.conv hz, this⟩).elim
  obtain ⟨tk, rfl, hetk⟩ : ∃ tk, mb = .app (.construct iid 1 []) tk ∧
      Erases E B lps σ .nil [] (.lit (.natVal k)) tk := by
    generalize hx : Expr.lit (.natVal (k + 1)) = x at hmb
    cases hmb with
    | litSucc hid' h' => cases hx; rw [hid] at hid'; cases hid'; exact ⟨_, rfl, h'⟩
    | box hb =>
      subst hx
      obtain ⟨w, hw, hwE⟩ := hb
      obtain ⟨ηN, hBN, rfl⟩ := CasesWhred.trM_lit_inv hw
      rw [hB] at hBN
      cases hBN
      exact (hnotProof hss (SimInd.ctor_isProof hE hok hwE).1).elim
    | litZero => cases hx
    | ctor | cases | casesReduced | eta | quotMk | quotLift | recLet | recFix =>
      exact absurd hx (CasesWhred.ne_mkAppN_const fun _ _ h => by cases h)
    | bvar | fvar | lam | letE | app | const | proj | mdata => cases hx
  -- the second alternative, under one field binder
  have halt1 : alts[1]? = some alt := by
    have := SimInd.get_alt pre alts [] maj (j := 1) (by omega)
    rw [hpre, show casesMajor iv + 1 + 1 = casesMajor iv + 2 by omega] at this
    rw [← this]
    simpa using halt
  obtain ⟨cv1, hcn1, hcP1, hnf1, -⟩ := SimInd.ind_ctor henv hB hivP (1 : Fin 2)
  change iv.ctors[1]? = _ at hcn1
  obtain ⟨n1, hn1⟩ := Option.isSome_iff_exists.mp (hcf 1 _ hcn1)
  have hn1' : n1 = 1 := by
    unfold ctorFields at hn1
    split at hn1
    · rename_i cv' hcv'
      rw [SrcDefeq.findDecl_sub hsub hcv', Option.some.injEq] at hcP1
      cases hcP1
      cases hn1
      exact hnf1
    · cases hn1
  subst hn1'
  obtain ⟨br, hbr⟩ : ∃ br, brs[1]? = some br := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨ns, tbr⟩ := br
  have halt'' := halt' 1 _ _ _ _ hcn1 halt1 hbr hn1
  obtain ⟨f₀, -, hf₀⟩ := CasesWhred.forall₂_getElem? hfs₀ (i := 0) rfl
  have hcl := SimCases.closed0 hf₀ hetk
  have hok' : List.Forall₂ (FieldOK E B lps σ) [.lit (.natVal k)] [tk] :=
    .cons ⟨.lit, fixed_lit, hetk, hcl⟩ .nil
  obtain ⟨X, tX, hXb, hXe, hXt, hXT⟩ := drive henv hE hsub hok' halt'' halt₀ hfs₀ hI
  rw [mkAppN_single] at hXb
  have hdmb := ErasesDeps.eval hdmaj hevmb
  cases hdmb with
  | app _ hdtk =>
  obtain ⟨vb, hvb, hevb⟩ := ihb X hXb hXt hXT hXe
    (deps_substl (by simpa using hdtk) (hdbrs _ (List.mem_of_getElem? hbr)))
  change lookupCtor lenv _ 1 = _ at hlk
  refine ⟨vb, hvb, .iota (args := [tk]) (cdecl := cb) rfl hevmb ?_ hbr ?_ ?_
    (by simpa [iotaRed, hnp0] using hevb)⟩
  · show (lookupCtor lenv iid 1).map _ = _
    rw [hlk]
    simp [hpf, hnpars, hnp0]
  · simp [hnargs, hnp0]
  · simp [hnp0, erasesAlt_length halt'']

end


end EraseProof
