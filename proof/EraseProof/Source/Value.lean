import EraseProof.Relation.Basic

/-!
# Source values

The shapes of source values (`SrcValue`) and `SrcEval.value`: every result of `SrcEval` is a
value. Adapted from `ML-V Source/Value.lean`: the values of the marked semantics add `eta`-marked
λs and frozen terms and have no propositional projection spines (a projection of a frozen proof is
frozen, `SrcEval.projFrozen`); a constructor value records that its arguments are values, the
invariant that ML-V's private `Deep` carries (a projection returns a field of a constructor value).
-/

open Lean Erasure

namespace EraseProof

/-- A spine of an atom constant (`SrcEval.constAtom`) applied by `SrcEval.appCong`. Port of
`ML-V Spec.lean:828`. Reference: `MR P/PCUICWcbvEval.v:500 value` (`value_app` on an atom head). -/
inductive AtomSpine (σ : EvalEnv) : Expr → Prop
  | const : σ.isAtom c = true → AtomSpine σ (.const c us)
  | app : AtomSpine σ f → AtomSpine σ (.app f a)

/-- The shapes of source values: λs (plain or `eta`-marked), sorts, Πs, atom spines, saturated
constructor spines of values, literals, `Quot.mk` of a value and frozen terms. Adapted from
`ML-V Source/Value.lean:18`. Reference: `MR P/PCUICWcbvEval.v:500 value`. -/
inductive SrcValue (σ : EvalEnv) : Expr → Prop
  | lam : SrcValue σ (.lam n A b bi)
  | etaLam : SrcValue σ (markEta (.lam n A b bi))
  | sort : SrcValue σ (.sort u)
  | forallE : SrcValue σ (.forallE n A B bi)
  | spine : AtomSpine σ e → SrcValue σ e
  | ctor {args : List Expr} : findDecl σ.decls c = some (.ctorInfo cv) →
      args.length = cv.numParams + cv.numFields → (∀ a ∈ args, SrcValue σ a) →
      SrcValue σ (mkAppN (.const c us) args.toArray)
  | lit : SrcValue σ (.lit (.natVal k))
  | quotMk : findDecl σ.decls c = some (.quotInfo qv) → qv.kind = .ctor → SrcValue σ a →
      SrcValue σ (mkAppN (.const c us) [α, r, a].toArray)
  | frozen : SrcValue σ (markErase s)

section
variable {σ : EvalEnv}

/-- The head of an atom spine is an atom constant. Copy of `ML-V Source/Value.lean:61`. -/
theorem AtomSpine.head {e : Expr} (h : AtomSpine σ e) :
    ∃ c us, e.getAppFn = .const c us ∧ σ.isAtom c = true := by
  induction h with
  | const ha => exact ⟨_, _, rfl, ha⟩
  | app _ ih => exact ih

/-- A constructor is no atom. Copy of `ML-V Source/Value.lean:74`. -/
theorem isAtom_ctor {c : Name} {cv : ConstructorVal}
    (hc : findDecl σ.decls c = some (.ctorInfo cv)) : σ.isAtom c = false := by
  unfold EvalEnv.isAtom; rw [hc]; simp [OwnRules]

/-- The arguments of a constructor value are values. Adapted from `ML-V Source/Value.lean:79`. -/
theorem SrcValue.ctor_args {c : Name} {us : List Level} {cv : ConstructorVal} {args : List Expr}
    (hc : findDecl σ.decls c = some (.ctorInfo cv))
    (h : SrcValue σ (mkAppN (.const c us) args.toArray)) : ∀ a ∈ args, SrcValue σ a := by
  have hfn := getAppFn_mkAppN_const c us args
  generalize hx : mkAppN (.const c us) args.toArray = x at h hfn
  cases h with
  | lam | etaLam | sort | forallE | lit | frozen => cases hfn
  | spine hs =>
    obtain ⟨c', us', h1, h2⟩ := AtomSpine.head hs
    rw [hfn] at h1; cases h1
    rw [isAtom_ctor hc] at h2; cases h2
  | ctor _ _ hargs =>
    obtain ⟨-, -, rfl⟩ := mkAppN_const_inj hx
    exact hargs
  | quotMk hq =>
    obtain ⟨rfl, -, -⟩ := mkAppN_const_inj hx
    rw [hc] at hq; cases hq

/-- A spine of a constructor blocks `appCong`. Copy of `ML-V Source/Value.lean:120`. -/
theorem blocksCong_ctor {e : Expr} {c : Name} {us : List Level} {cv : ConstructorVal}
    (he : e.getAppFn = .const c us) (hc : findDecl σ.decls c = some (.ctorInfo cv)) :
    BlocksCong σ e := by
  cases e with
  | app f a => exact .inl ⟨c, us, cv, he, hc⟩
  | const => exact .inl ⟨c, us, cv, he, hc⟩
  | _ => cases he

/-- A spine of `Quot.mk` blocks `appCong`. Copy of `ML-V Source/Value.lean:128`. -/
theorem blocksCong_quot {e : Expr} {c : Name} {us : List Level} {qv : QuotVal}
    (he : e.getAppFn = .const c us) (hc : findDecl σ.decls c = some (.quotInfo qv))
    (hk : qv.kind = .ctor) : BlocksCong σ e := by
  cases e with
  | app f a => exact .inr (.inr ⟨c, us, qv, he, hc, hk⟩)
  | const => exact .inr (.inr ⟨c, us, qv, he, hc, hk⟩)
  | _ => cases he

/-- A value that does not block `appCong` is an atom spine. -/
theorem SrcValue.atomSpine {e : Expr} (h : SrcValue σ e) (hb : ¬ BlocksCong σ e) : AtomSpine σ e := by
  cases h with
  | spine hs => exact hs
  | lam | etaLam | sort | forallE | lit | frozen => exact absurd trivial hb
  | ctor hc _ _ => exact absurd (blocksCong_ctor (getAppFn_mkAppN_const _ _ _) hc) hb
  | quotMk hc hk _ => exact absurd (blocksCong_quot (getAppFn_mkAppN_const _ _ _) hc hk) hb

/-- Evaluation results are values. Adapted from `ML-V Source/Value.lean:139 deep`. Reference:
`eval_to_value` (`MR P/PCUICWcbvEval.v:570`). -/
theorem SrcEval.value {env : ConLeche.Env} {e v : Expr} (hev : SrcEval env σ e v) :
    SrcValue σ v := by
  induction hev with
  | beta | etaBeta | zeta | delta | casesIota | casesLitZero | casesLitSucc | casesFrozen
    | quotLift | recIota => assumption
  | constAtom h => exact .spine (.const h)
  | @ctor c cv us as vs hc hl hlv _ _ ih =>
    refine .ctor hc (hlv ▸ hl) fun a ha => ?_
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    exact ih i as[i] _ (List.getElem?_eq_getElem (by omega)) (List.getElem?_eq_getElem hi)
  | quotMk hc hk _ _ ih => exact .quotMk hc hk ih
  | proj _ hcv hfs _ ihm =>
    obtain ⟨C, us, cv, ps, hC, -, -, -, -, rfl⟩ := hcv
    exact SrcValue.ctor_args hC ihm _ (List.mem_append_right _ (List.mem_of_getElem? hfs))
  | projFrozen | frozen | frozenApp => exact .frozen
  | lit => exact .lit
  | appCong _ _ hb _ _ ihf _ => exact .spine (.app (ihf.atomSpine hb))
  | atom h =>
    rename_i e
    cases e <;> first | exact .lam | exact .sort | exact .forallE | exact absurd h id
  | etaLam => exact .etaLam

end

end EraseProof
