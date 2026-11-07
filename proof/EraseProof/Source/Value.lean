import EraseProof.Spec
import EraseProof.Bridge.Proj

/-!
# Source values

The shapes of source values (`SrcValue`) and `SrcEval.value`: every result of `SrcEval` is a
value. A projection returns a field of a constructor value, so the proof carries the stronger
invariant that the arguments of a constructor value are values themselves.
-/

open Lean Erasure

namespace EraseProof

/-- The shapes of source values (partially applied constructors and `casesOn` are η-expanded, so they
are λs). Reference: `MR P/PCUICWcbvEval.v:500 value`. -/
inductive SrcValue (σ : EvalEnv) : Expr → Prop
  | lam : SrcValue σ (.lam n A b bi)
  | sort : SrcValue σ (.sort u)
  | forallE : SrcValue σ (.forallE n A B bi)
  | spine : AtomSpine σ e → SrcValue σ e
  | propProj : PropProj σ e → SrcValue σ e
  | ctor {args : List Expr} : findDecl σ.decls c = some (.ctorInfo cv) →
      args.length = cv.numParams + cv.numFields → SrcValue σ (mkAppN (.const c us) args.toArray)
  | lit : SrcValue σ (.lit (.natVal k))
  | quotMk : findDecl σ.decls c = some (.quotInfo qv) → qv.kind = .ctor → SrcValue σ a →
      SrcValue σ (mkAppN (.const c us) [α, r, a].toArray)

namespace Value

/-- `SrcValue`, with the arguments of constructor values values themselves. -/
private inductive Deep (σ : EvalEnv) : Expr → Prop
  | lam : Deep σ (.lam n A b bi)
  | sort : Deep σ (.sort u)
  | forallE : Deep σ (.forallE n A B bi)
  | spine : AtomSpine σ e → Deep σ e
  | propProj : PropProj σ e → Deep σ e
  | ctor {args : List Expr} : findDecl σ.decls c = some (.ctorInfo cv) →
      args.length = cv.numParams + cv.numFields → (∀ a ∈ args, Deep σ a) →
      Deep σ (mkAppN (.const c us) args.toArray)
  | lit : Deep σ (.lit (.natVal k))
  | quotMk : findDecl σ.decls c = some (.quotInfo qv) → qv.kind = .ctor → Deep σ a →
      Deep σ (mkAppN (.const c us) [α, r, a].toArray)

private theorem Deep.srcValue {σ : EvalEnv} {e : Expr} (h : Deep σ e) : SrcValue σ e := by
  induction h with
  | lam => exact .lam
  | sort => exact .sort
  | forallE => exact .forallE
  | spine h => exact .spine h
  | propProj h => exact .propProj h
  | ctor hc hl _ => exact .ctor hc hl
  | lit => exact .lit
  | quotMk hc hk _ ih => exact .quotMk hc hk ih

private theorem getAppFn_mkAppN_const (c : Name) (us : List Level) (as : List Expr) :
    (mkAppN (.const c us) as.toArray).getAppFn = .const c us := by
  rw [mkAppN_eq_foldl, foldl_app_getAppFn]; rfl

private theorem AtomSpine.head {σ : EvalEnv} {e : Expr} (h : AtomSpine σ e) :
    ∃ c us, e.getAppFn = .const c us ∧ σ.isAtom c = true := by
  induction h with
  | const ha => exact ⟨_, _, rfl, ha⟩
  | app _ ih => exact ih

private theorem PropProj.head {σ : EvalEnv} {e : Expr} (h : PropProj σ e) :
    ∃ S i x, e.getAppFn = .proj S i x := by
  induction h with
  | proj => exact ⟨_, _, _, rfl⟩
  | projProj => exact ⟨_, _, _, rfl⟩
  | app _ ih => exact ih

private theorem isAtom_ctor {σ : EvalEnv} {c : Name} {cv : ConstructorVal}
    (hc : findDecl σ.decls c = some (.ctorInfo cv)) : σ.isAtom c = false := by
  unfold EvalEnv.isAtom; rw [hc]; simp [OwnRules]

/-- The arguments of a constructor value are values. -/
private theorem Deep.ctor_args {σ : EvalEnv} {c : Name} {us : List Level} {cv : ConstructorVal}
    {args : List Expr} (hc : findDecl σ.decls c = some (.ctorInfo cv))
    (h : Deep σ (mkAppN (.const c us) args.toArray)) : ∀ a ∈ args, Deep σ a := by
  have hfn := getAppFn_mkAppN_const c us args
  generalize hx : mkAppN (.const c us) args.toArray = x at h hfn
  cases h with
  | lam | sort | forallE | lit => cases hfn
  | spine hs =>
    obtain ⟨c', us', h1, h2⟩ := AtomSpine.head hs
    rw [hfn] at h1; cases h1
    rw [isAtom_ctor hc] at h2; cases h2
  | propProj hp =>
    obtain ⟨_, _, _, h1⟩ := PropProj.head hp
    rw [hfn] at h1; cases h1
  | ctor _ _ hargs =>
    rw [mkAppN_eq_foldl, mkAppN_eq_foldl] at hx
    obtain ⟨-, -, rfl⟩ := foldl_app_const_inj hx
    exact hargs
  | quotMk hq =>
    rw [mkAppN_eq_foldl, mkAppN_eq_foldl] at hx
    obtain ⟨rfl, -, -⟩ := foldl_app_const_inj hx
    rw [hc] at hq; cases hq

/-- The η-expansion of a short spine is a λ. -/
private theorem etaSpine?_lam {σ : EvalEnv} {c : Name} {us : List Level} {as : List Expr}
    {e' : Expr} (h : σ.etaSpine? c us as = some e') : ∃ n A b bi, e' = .lam n A b bi := by
  unfold EvalEnv.etaSpine? at h
  split at h
  next ci ar _ _ =>
    split at h
    · obtain ⟨ty, -, hl⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨k, hk⟩ : ∃ k, ar - as.length = k + 1 := ⟨ar - as.length - 1, by omega⟩
      rw [hk] at hl
      cases ty with
      | forallE n d b bi =>
        obtain ⟨x, -, rfl⟩ := Option.map_eq_some_iff.1 hl
        exact ⟨_, _, _, _, rfl⟩
      | _ => cases hl
    · cases h
  · cases h

private theorem BlocksCong_ctor {σ : EvalEnv} {e : Expr} {c : Name} {us : List Level}
    {cv : ConstructorVal} (he : e.getAppFn = .const c us)
    (hc : findDecl σ.decls c = some (.ctorInfo cv)) : BlocksCong σ e := by
  cases e with
  | app f a => exact .inl ⟨c, us, cv, he, hc⟩
  | const => exact .inl ⟨c, us, cv, he, hc⟩
  | _ => cases he

private theorem BlocksCong_quot {σ : EvalEnv} {e : Expr} {c : Name} {us : List Level}
    {qv : QuotVal} (he : e.getAppFn = .const c us)
    (hc : findDecl σ.decls c = some (.quotInfo qv)) : BlocksCong σ e := by
  cases e with
  | app f a => exact .inr (.inr ⟨c, us, qv, he, hc⟩)
  | const => exact .inr (.inr ⟨c, us, qv, he, hc⟩)
  | _ => cases he

/-- Every evaluation result is a value whose constructor arguments are values. -/
private theorem deep {σ : EvalEnv} {e v : Expr} (hev : SrcEval σ e v) : Deep σ v := by
  induction hev with
  | beta _ _ _ _ _ _ ih => exact ih
  | zeta _ _ _ ih => exact ih
  | delta _ _ ih => exact ih
  | constAtom h => exact .spine (.const h)
  | eta h =>
    obtain ⟨_, _, _, _, rfl⟩ := etaSpine?_lam h
    exact .lam
  | @ctor c cv us as vs hc hl hlv _ ih =>
    refine .ctor hc (hlv ▸ hl) fun a ha => ?_
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    obtain ⟨a', ha'⟩ : ∃ a', as[i]? = some a' := ⟨as[i], List.getElem?_eq_getElem (by omega)⟩
    exact ih i a' _ ha' (List.getElem?_eq_getElem hi)
  | casesIota _ _ _ _ _ _ _ _ ih => exact ih
  | casesLitZero _ _ _ _ _ _ _ _ ih => exact ih
  | casesLitSucc _ _ _ _ _ _ _ _ ih => exact ih
  | casesProof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | quotMk hc hk _ ih => exact .quotMk hc hk ih
  | quotLift _ _ _ _ _ _ _ _ _ ih => exact ih
  | recIota => rename_i ih; exact ih
  | proj _ hcv hfs ihm =>
    obtain ⟨C, us, cv, ps, hC, -, -, -, -, rfl⟩ := hcv
    exact Deep.ctor_args hC ihm _ (List.mem_append_right _ (List.mem_of_getElem? hfs))
  | projProp hS _ hm _ =>
    rcases hm with hm | hm
    · exact .propProj (.proj hS hm)
    · exact .propProj (.projProj hS hm)
  | lit => exact .lit
  | appCong _ _ hb _ ihf _ =>
    cases ihf with
    | lam | sort | forallE | lit => exact absurd trivial hb
    | spine hs => exact .spine (.app hs)
    | propProj hp => exact .propProj (.app hp)
    | ctor hc _ _ => exact absurd (BlocksCong_ctor (getAppFn_mkAppN_const _ _ _) hc) hb
    | quotMk hc _ _ => exact absurd (BlocksCong_quot (getAppFn_mkAppN_const _ _ _) hc) hb
  | mdata _ ih => exact ih
  | atom h =>
    rename_i e
    cases e <;> first | exact .lam | exact .sort | exact .forallE | exact absurd h id

end Value

/-- Evaluation results are values. Reference: `eval_to_value` (`MR P/PCUICWcbvEval.v:570`). -/
theorem SrcEval.value {σ : EvalEnv} {e v : Expr} (hev : SrcEval σ e v) : SrcValue σ v :=
  (Value.deep hev).srcValue

end EraseProof
