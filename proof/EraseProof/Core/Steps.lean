import EraseProof.Core.LocalsOK
import EraseProof.Core.RegisterInd
import EraseProof.Core.NonRec
import EraseProof.Relation.Abstract
import EraseProof.Relation.Basic
import EraseProof.Oracle.Atom

/-!
# Steps of the shipping core's correctness

`erasePure_erases` is proved by induction on the fuel of the shipping traversal
(`Erasure.visitExpr` and the functions it calls, `LeanToLambdaBox/Erasure.lean`) run at the pure
backend `Erasure.PureM`. Its statement at one fuel is `ExprSpec` for `visitExpr` and `MutualSpec`
for `visitMutual`: a successful run on a translated, typed term returns an erasure of it
(`Erases`) with erased λ□ dependencies (`ErasesDeps`), keeps the state invariant `StateOK`, grows
the λ□ environment freshly and registers only constants of a scope (`Grows`, `ScopeOK`), under
locals that are the Lean form of the Metalean context (`CtxOK`). `StepIH` collects both at every
fuel up to a bound: the induction hypothesis of each step.

This module proves the steps of the cases of `visitExpr` that are not constructor, `casesOn`,
projection or literal cases: the oracle's `□` (`visitExpr_box`), a free variable, a sort, a Π and
the terms without translation, metadata, a λ, a `let`, an application whose head is neither a
constructor nor a recognized `casesOn` (`visitExpr_app_step`, `visitApp_plain`), a constant
(`visitConst_spec`), and `visitMutual` (`visitMutual_step`, every declaration of a program being
non-recursive, `isRecursiveDecl_false`).

Reference: `erases_erase` (`MR E/ErasureFunction.v:1228`), case by case over `erase`
(`MR E/ErasureFunction.v:989`), with `erase_constant_body` (`MR E/ErasureFunction.v:1309`) and
`erase_global_erases_deps` (`MR E/ErasureFunctionProperties.v:172`); port of `L4 Core/Steps.lean`.
-/

open Lean Erasure
open Metalean (Defeq TypeEq EnvWF)
open private getAppNumArgsAux from Lean.Expr

namespace EraseProof

namespace Steps

/-! ## Application spines -/

/-- The arguments of an application spine. -/
def spineArgs : Expr → List Expr
  | .app f a => spineArgs f ++ [a]
  | _ => []

theorem numArgsAux_eq : ∀ (e : Expr) (k : Nat), getAppNumArgsAux e k = getAppNumArgsAux e 0 + k
  | .app f _, k => by
    simp only [getAppNumArgsAux]
    rw [numArgsAux_eq f (k + 1), numArgsAux_eq f 1]; omega
  | .bvar _, _ | .fvar _, _ | .mvar _, _ | .sort _, _ | .const .., _ | .lam .., _
  | .forallE .., _ | .letE .., _ | .lit _, _ | .mdata .., _ | .proj .., _ => by
    simp [getAppNumArgsAux]

theorem numArgs_eq : ∀ e : Expr, e.getAppNumArgs = (spineArgs e).length
  | .app f a => by
    unfold Expr.getAppNumArgs
    simp only [getAppNumArgsAux]
    rw [numArgsAux_eq f 1, ← Expr.getAppNumArgs, numArgs_eq f]
    simp [spineArgs]
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const .. | .lam .. | .forallE .. | .letE .. | .lit _
  | .mdata .. | .proj .. => by simp [Expr.getAppNumArgs, getAppNumArgsAux, spineArgs]

theorem drop_set {α : Type} {l : List α} {i : Nat} {a : α} (h : i < l.length) :
    (l.set i a).drop i = a :: l.drop (i + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using h), List.getElem_set_self]
  congr 1
  apply List.drop_set_of_lt
  omega

theorem withAppAux_toList : ∀ (e : Expr) (as : Array Expr) (i : Nat),
    (spineArgs e).length = i + 1 → i < as.size →
    (Expr.withAppAux (fun _ as => as) e as i).toList = spineArgs e ++ as.toList.drop (i + 1)
  | .app f a, as, i, hl, hi => by
    rw [Expr.withAppAux]
    simp only [spineArgs, List.length_append, List.length_singleton,
      Nat.add_right_cancel_iff] at hl
    cases f with
    | app g b =>
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by simp [spineArgs] at hl; omega⟩
      rw [show j + 1 - 1 = j from rfl,
        withAppAux_toList (.app g b) _ j hl (by simp [Array.size_setIfInBounds]; omega)]
      simp only [Array.set!, Array.toList_setIfInBounds, spineArgs, List.append_assoc,
        List.singleton_append]
      rw [drop_set (by simpa using hi)]
      simp
    | _ =>
      simp only [spineArgs, List.length_nil] at hl
      subst hl
      simp only [Expr.withAppAux, Array.set!, Array.toList_setIfInBounds, spineArgs,
        List.nil_append, List.singleton_append]
      obtain ⟨l⟩ := as
      cases l with
      | nil => simp at hi
      | cons y l => rfl

theorem withApp_toList (e : Expr) : (e.withApp fun _ as => as).toList = spineArgs e := by
  unfold Expr.withApp
  simp only [numArgs_eq]
  rcases h : (spineArgs e).length with _ | m
  · have : spineArgs e = [] := List.eq_nil_of_length_eq_zero h
    cases e with
    | app f a => simp [spineArgs] at this
    | _ => rfl
  · rw [show m + 1 - 1 = m from rfl, withAppAux_toList e _ m h (by simp)]
    simp

theorem mkAppN_spine : ∀ e : Expr, mkAppN e.getAppFn (spineArgs e).toArray = e
  | .app f a => by
    have ih := mkAppN_spine f
    rw [mkAppN_toArray] at ih ⊢
    simp only [Expr.getAppFn, spineArgs, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const .. | .lam .. | .forallE .. | .letE .. | .lit _
  | .mdata .. | .proj .. => rfl

/-! ## Free variables of an erasure -/

/-- Every free variable of the parts of `e` that its erasure keeps satisfies `p`. -/
def KFV (p : FVarId → Prop) : Expr → Prop
  | .fvar x => p x
  | .app f a => KFV p f ∧ KFV p a
  | .lam _ _ b _ => KFV p b
  | .letE _ _ v b _ => KFV p v ∧ KFV p b
  | .mdata _ e | .proj _ _ e => KFV p e
  | _ => True

theorem KFV.of_fvarsIn {p : FVarId → Prop} : ∀ {e : Expr}, FVarsIn p e → KFV p e
  | .fvar _, h => h
  | .app f a, h => ⟨KFV.of_fvarsIn (e := f) h.1, KFV.of_fvarsIn (e := a) h.2⟩
  | .lam _ _ b _, h => KFV.of_fvarsIn (e := b) h.2
  | .letE _ _ v b _, h => ⟨KFV.of_fvarsIn (e := v) h.2.1, KFV.of_fvarsIn (e := b) h.2.2⟩
  | .mdata _ e, h | .proj _ _ e, h => KFV.of_fvarsIn (e := e) h
  | .bvar _, _ | .mvar _, _ | .sort _, _ | .const .., _ | .forallE .., _ | .lit _, _ => trivial

theorem KFV_foldl {p : FVarId → Prop} : ∀ {f : Expr} {as : List Expr},
    KFV p (as.foldl .app f) ↔ KFV p f ∧ ∀ a ∈ as, KFV p a
  | _, [] => by simp
  | f, a :: as => by
    rw [List.foldl_cons, KFV_foldl]
    simp only [KFV, List.mem_cons, forall_eq_or_imp, and_assoc]

theorem KFV_lift {p : FVarId → Prop} : ∀ {e : Expr} {s d : Nat}, KFV p e →
    KFV p (e.liftLooseBVars' s d)
  | .bvar _, _, _, _ => by simp only [Expr.liftLooseBVars']; split <;> trivial
  | .app f a, _, _, h => ⟨KFV_lift (e := f) h.1, KFV_lift (e := a) h.2⟩
  | .lam _ _ b _, _, _, h => KFV_lift (e := b) h
  | .letE _ _ v b _, _, _, h => ⟨KFV_lift (e := v) h.1, KFV_lift (e := b) h.2⟩
  | .mdata _ e, _, _, h | .proj _ _ e, _, _, h => KFV_lift (e := e) h
  | .fvar _, _, _, h => h
  | .mvar _, _, _, _ | .sort _, _, _, _ | .const .., _, _, _ | .forallE .., _, _, _
  | .lit _, _, _, _ => trivial

theorem KFV_lamsOf {p : FVarId → Prop} : ∀ {m : Nat} {ty body e : Expr},
    lamsOf m ty body = some e → KFV p body → KFV p e
  | 0, _, _, _, h, hb => by cases h; exact hb
  | m + 1, .forallE _ _ b _, body, e, h, hb => by
    simp only [lamsOf, Option.map_eq_some_iff] at h
    obtain ⟨e', h', rfl⟩ := h
    have := KFV_lamsOf h' hb
    exact this
  | _ + 1, .bvar _, _, _, h, _ | _ + 1, .fvar _, _, _, h, _ | _ + 1, .mvar _, _, _, h, _
  | _ + 1, .sort _, _, _, h, _ | _ + 1, .const .., _, _, h, _ | _ + 1, .app .., _, _, h, _
  | _ + 1, .lam .., _, _, h, _ | _ + 1, .letE .., _, _, h, _ | _ + 1, .lit _, _, _, h, _
  | _ + 1, .mdata .., _, _, h, _ | _ + 1, .proj .., _, _, h, _ => by cases h

theorem KFV_etaSpine {p : FVarId → Prop} {σ : EvalEnv} {c : Name} {us : List Level}
    {as : List Expr} {e' : Expr} (h : σ.etaSpine? c us as = some e')
    (hk : KFV p (mkAppN (.const c us) as.toArray)) : KFV p e' := by
  unfold EvalEnv.etaSpine? at h
  split at h
  · split at h
    · obtain ⟨ty, -, h⟩ := Option.bind_eq_some_iff.1 h
      refine KFV_lamsOf h ?_
      rw [mkAppN_toArray, KFV_foldl]
      rw [mkAppN_toArray, KFV_foldl] at hk
      refine ⟨trivial, fun a ha => ?_⟩
      rcases List.mem_append.1 ha with ha | ha
      · obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.1 ha
        exact KFV_lift (hk.2 a₀ ha₀)
      · obtain ⟨j, -, rfl⟩ := List.mem_map.1 ha
        trivial
    · cases h
  · cases h

theorem hasFVar_mkApps {x : FVarId} : ∀ {f : LBTerm} {as : List LBTerm},
    hasFVar x (mkApps f as) = true → hasFVar x f = true ∨ ∃ a ∈ as, hasFVar x a = true
  | _, [], h => .inl h
  | f, a :: as, h => by
    rcases hasFVar_mkApps (f := .app f a) (as := as) h with h | ⟨b, hb, h⟩
    · simp only [hasFVar, Bool.or_eq_true] at h
      rcases h with h | h
      · exact .inl h
      · exact .inr ⟨a, .head _, h⟩
    · exact .inr ⟨b, .tail _ hb, h⟩

theorem mem_rel {α β : Type} {as : List α} {bs : List β} {R : α → β → Prop}
    (hlen : as.length = bs.length)
    (h : ∀ (i : Nat) a b, as[i]? = some a → bs[i]? = some b → R a b) :
    ∀ b ∈ bs, ∃ a ∈ as, R a b := by
  intro b hb
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
  have hi' : i < as.length := hlen ▸ hi
  exact ⟨as[i], List.getElem_mem hi', h i _ _ (List.getElem?_eq_getElem hi')
    (List.getElem?_eq_getElem hi)⟩

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {σ : EvalEnv} {lps : List Name}

/-- The free variables of an erasure are free variables of the parts of the source it keeps.
Reference: none (`LBTerm.fvar` has no MetaRocq counterpart, DV-13). -/
theorem Erases.hasFVar_of {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
    {Δ : MLCtx ζ lps.length n} {e : Expr} {tb : LBTerm} (h : Erases E B lps σ Γ Δ e tb) :
    ∀ (p : FVarId → Prop), KFV p e → ∀ x, hasFVar x tb = true → p x := by
  refine Erases.rec
    (motive_1 := fun _ _ e tb _ => ∀ (p : FVarId → Prop), KFV p e → ∀ x, hasFVar x tb = true → p x)
    (motive_2 := fun _ _ _ e br _ => ∀ (p : FVarId → Prop), KFV p e → ∀ x,
      hasFVar x br.2 = true → p x)
    ?bvar ?fvar ?lam ?letE ?app ?const ?ctor ?cases ?casesReduced ?eta ?proj ?litZero ?litSucc
    ?quotMk ?quotLift ?recLet ?recFix ?mdata ?box ?done ?alam ?intro h
  case bvar | const | box | litZero => intros; simp_all [hasFVar, hasFVarL]
  case fvar =>
    intro _ _ _ y p hk x hx
    simp only [hasFVar] at hx
    rw [(fvarId_beq_iff x y).mp hx]; exact hk
  case lam => intro _ _ _ _ _ _ _ _ _ _ _ _ ih p hk x hx; exact ih p hk x hx
  case letE =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihv ihb p hk x hx
    simp only [hasFVar, Bool.or_eq_true] at hx
    exact hx.elim (ihv p hk.1 x) (ihb p hk.2 x)
  case app =>
    intro _ _ _ _ _ _ _ _ _ _ ihf iha p hk x hx
    simp only [hasFVar, Bool.or_eq_true] at hx
    exact hx.elim (ihf p hk.1 x) (iha p hk.2 x)
  case ctor =>
    intro _ _ _ _ _ _ _ as as' _ _ _ _ hlen _ ih p hk x hx
    rw [mkAppN_toArray, KFV_foldl] at hk
    rcases hasFVar_mkApps hx with h | ⟨a', ha', h⟩
    · simp [hasFVar, hasFVarL] at h
    · obtain ⟨a, ha, hr⟩ := mem_rel hlen ih a' ha'
      exact hr p (hk.2 a ha) x h
  case cases =>
    intro _ iv _ _ _ _ _ maj _ pre alts extra brs _ _ _ _ _ _ hlalts _ hlbrs hcf _ hlex _ ihm iha
      ihe p hk x hx
    rw [mkAppN_toArray, KFV_foldl] at hk
    rcases hasFVar_mkApps hx with h | ⟨a', ha', h⟩
    · simp only [hasFVar, Bool.or_eq_true] at h
      rcases h with h | h
      · exact ihm p (hk.2 maj (by simp)) x h
      · have key : ∀ brs' : List (List BinderName × LBTerm), hasFVarB x brs' = true →
            ∃ br ∈ brs', hasFVar x br.2 = true := by
          intro brs' h'
          induction brs' with
          | nil => cases h'
          | cons br brs' ih =>
            obtain ⟨ns, b⟩ := br
            simp only [hasFVarB, Bool.or_eq_true] at h'
            rcases h' with h' | h'
            · exact ⟨_, .head _, h'⟩
            · obtain ⟨b', hb', h''⟩ := ih h'
              exact ⟨b', .tail _ hb', h''⟩
        obtain ⟨br, hbr, hb⟩ := key brs h
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hbr
        have hia : i < alts.length := hlbrs ▸ hi
        have hic : i < iv.ctors.length := hlalts ▸ hia
        obtain ⟨kf, hkf⟩ := Option.isSome_iff_exists.1 (hcf i _ (List.getElem?_eq_getElem hic))
        exact iha i _ _ _ kf (List.getElem?_eq_getElem hic) (List.getElem?_eq_getElem hia)
          (List.getElem?_eq_getElem hi) hkf p (hk.2 _ (by simp [List.getElem_mem hia])) x hb
    · obtain ⟨a, ha, hr⟩ := mem_rel hlex ihe a' ha'
      exact hr p (hk.2 a (by simp [ha])) x h
  case casesReduced =>
    intro _ _ _ _ _ _ _ alt _ _ _ _ extra extra' _ _ _ _ _ _ _ hlex _ iha ihe p hk x hx
    rw [mkAppN_toArray, KFV_foldl] at hk
    rcases hasFVar_mkApps hx with h | ⟨a', ha', h⟩
    · exact iha p (hk.2 alt (by simp)) x h
    · rcases List.mem_append.1 ha' with ha' | ha'
      · rw [List.eq_of_mem_replicate ha'] at h; cases h
      · obtain ⟨a, ha, hr⟩ := mem_rel hlex ihe a' ha'
        exact hr p (hk.2 a (by simp [ha])) x h
  case eta => intro _ _ _ _ _ _ _ _ heta _ ih p hk x hx; exact ih p (KFV_etaSpine heta hk) x hx
  case quotMk =>
    intros; rename_i hlex _ iha ihe p hk x hx
    rw [mkAppN_toArray, KFV_foldl] at hk
    rcases hasFVar_mkApps hx with h | ⟨a', ha', h⟩
    · exact iha p (hk.2 _ (by simp)) x h
    · obtain ⟨a, ha, hr⟩ := mem_rel hlex ihe a' ha'
      exact hr p (hk.2 a (by simp [ha])) x h
  case quotLift =>
    intros; rename_i hlex _ ihf ihq ihe p hk x hx
    rw [mkAppN_toArray, KFV_foldl] at hk
    rcases hasFVar_mkApps hx with h | ⟨a', ha', h⟩
    · exact ihf p (hk.2 _ (by simp)) x h
    · rcases List.mem_cons.1 ha' with rfl | ha'
      · exact ihq p (hk.2 _ (by simp)) x h
      · obtain ⟨a, ha, hr⟩ := mem_rel hlex ihe a' ha'
        exact hr p (hk.2 a (by simp [ha])) x h
  case recLet =>
    intro _ rv _ minors F _ _ _ maj maj' ps ms mins is extra mins' is' extra' _ hF _ _ _ _ hlm _
      hli _ _ hle _ ihmin ihis ihmaj ihext p hk x hx
    rw [mkAppN_toArray, KFV_foldl] at hk
    obtain ⟨-, -, hFx⟩ := RecLam.RecFixOf.closed hF
    rcases RecLam.hasFVar_recLetTerm hFx hx with ⟨a', ha', h⟩ | ⟨a', ha', h⟩ | h | ⟨a', ha', h⟩
    · obtain ⟨a, ha, hr⟩ := mem_rel hlm ihmin a' ha'
      exact hr p (hk.2 a (by simp [ha])) x h
    · obtain ⟨a, ha, hr⟩ := mem_rel hli ihis a' ha'
      exact hr p (hk.2 a (by simp [ha])) x h
    · exact ihmaj p (hk.2 maj (by simp)) x h
    · obtain ⟨a, ha, hr⟩ := mem_rel hle ihext a' ha'
      exact hr p (hk.2 a (by simp [ha])) x h
  case recFix =>
    intro _ rv _ minors F _ _ _ maj maj' ps ms mins is extra ws is' extra' _ hF _ _ hmins _ hlw _
      hws hli _ _ hle _ ihmin ihis ihmaj ihext p hk x hx
    rw [mkAppN_toArray, KFV_foldl] at hk
    obtain ⟨-, hFc, hFx⟩ := RecLam.RecFixOf.closed hF
    have hG := RecLam.substl_fix (ws := ws) (by rw [← hlw, hmins]; exact hFc) hFx
      fun w hw => ⟨(hws w hw).1, (hws w hw).2.1⟩
    rcases hasFVar_mkApps hx with h | ⟨a', ha', h⟩
    · rw [hG.2 x] at h; cases h
    · rcases List.mem_append.1 ha' with ha' | ha'
      · rcases List.mem_append.1 ha' with ha' | ha'
        · obtain ⟨a, ha, hr⟩ := mem_rel hli ihis a' ha'
          exact hr p (hk.2 a (by simp [ha])) x h
        · rw [List.mem_singleton.1 ha'] at h
          exact ihmaj p (hk.2 maj (by simp)) x h
      · obtain ⟨a, ha, hr⟩ := mem_rel hle ihext a' ha'
        exact hr p (hk.2 a (by simp [ha])) x h
  case proj => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih p hk x hx; exact ih p hk x hx
  case litSucc =>
    intro _ _ _ _ _ _ _ _ ih p _ x hx
    simp only [hasFVar, hasFVarL, Bool.false_or] at hx
    exact ih p trivial x hx
  case mdata => intros; rename_i ih p hk x hx; exact ih p hk x hx
  case done => intros; rename_i ih p hk x hx; exact ih p hk x hx
  case alam => intros; rename_i ih p hk x hx; exact ih p hk x hx
  case intro => intros; rename_i ih p hk x hx; exact ih p ⟨KFV_lift hk, trivial⟩ x hx

end

/-! ## Inversions, contexts and λ□ dependencies -/

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {lps : List Name}

theorem trM_lam_inv {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    {x : Name} {A b : Expr} {bi : BinderInfo} {V : Metalean.Expr ζ lps.length n}
    (h : TrM E B lps Γ Δ (.lam x A b bi) V) :
    ∃ A' b', V = .lam A' b' ∧ TrM E B lps Γ Δ A A' ∧
      TrM E B lps (Γ.snoc A') (Δ.pushLam none) b b' := by
  generalize hx : Expr.lam x A b bi = e at h
  cases h with
  | lam hA hb => cases hx; exact ⟨_, _, rfl, hA, hb⟩
  | special => exact absurd hx (CasesWhred.ne_mkAppN_const fun _ _ h => by cases h)
  | _ => cases hx

theorem trM_letE_inv {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    {x : Name} {T v b : Expr} {nd : Bool} {V : Metalean.Expr ζ lps.length n}
    (h : TrM E B lps Γ Δ (.letE x T v b nd) V) :
    ∃ T' v' b', V = .letE T' v' b'.wk ∧ TrM E B lps Γ Δ T T' ∧ TrM E B lps Γ Δ v v' ∧
      TrM E B lps Γ ((none, .vlet v') :: Δ) b b' := by
  generalize hx : Expr.letE x T v b nd = e at h
  cases h with
  | letE hT hv hb => cases hx; exact ⟨_, _, _, rfl, hT, hv, hb⟩
  | special => exact absurd hx (CasesWhred.ne_mkAppN_const fun _ _ h => by cases h)
  | _ => cases hx

theorem trM_mdata_inv {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    {d : MData} {e : Expr} {V : Metalean.Expr ζ lps.length n}
    (h : TrM E B lps Γ Δ (.mdata d e) V) : TrM E B lps Γ Δ e V := by
  generalize hx : Expr.mdata d e = e' at h
  cases h with
  | mdata h => cases hx; exact h
  | special => exact absurd hx (CasesWhred.ne_mkAppN_const fun _ _ h => by cases h)
  | _ => cases hx

/-- Locals without bound entries count no bound local. -/
theorem countP_none {ℓ n : Nat} : ∀ {Δ : MLCtx ζ ℓ n}, (∀ i, Δ.findB i = none) →
    Δ.countP (·.1.isNone) = 0
  | [], _ => rfl
  | (none, d) :: _, h => by have := h 0; simp [MLCtx.findB] at this
  | (some _, _) :: Δ, h => by
    have : ∀ i, MLCtx.findB Δ i = none := fun i => by simpa [MLCtx.findB] using h i
    simpa using countP_none this

/-- Opening a `let` with a fresh `x` is an `MLCtx.InstFV` at `0`. -/
theorem InstFV.zeroLet {ℓ n : Nat} {x : FVarId} {Δ : MLCtx ζ ℓ n} (hx : Δ.findF x = none)
    (d : MLDecl ζ ℓ n) : MLCtx.InstFV x 0 ((none, d) :: Δ) ((some x, d) :: Δ) := by
  have hxx : (x == x) = true := (fvarId_beq_iff x x).mpr rfl
  constructor
  · intro i t ht
    cases i with
    | zero =>
      simp only [MLCtx.findB] at ht
      simp [MLCtx.findF, hxx, ← ht]
    | succ i =>
      refine ⟨by omega, by omega, fun _ => ?_⟩
      simpa [MLCtx.findB] using ht
  · intro y t ht
    simp only [MLCtx.findF] at ht ⊢
    rw [MLCtx.findF_ne hx ht]
    exact ht

/-- Closing a `let` that the traversal opened with a fresh free variable (`mkLetIn`): the
`let`-body counterpart of `Erases.abstract`. Reference: `Erases.uninstantiateN`
(`L4 Relation/Abstract.lean:170`); none in MetaRocq (DV-13). -/
theorem Erases.abstract_let {P : List ConstantInfo} {σ : EvalEnv} {n : Nat}
    {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n} {x : FVarId} {b : Expr}
    {tb : LBTerm} {d : MLDecl ζ lps.length n} (henv : ProgEnv P ζ E B) (hsub : SubEnv σ.decls P)
    (_hx : Δ.findF x = none) (hfv : FVarsIn (· ≠ x) b) (hcl : closedn 0 tb = true)
    (h : Erases E B lps σ Γ ((some x, d) :: Δ) (b.instantiate1' (.fvar x)) tb) :
    Erases E B lps σ Γ ((none, d) :: Δ) b (_root_.abstract x tb) := by
  have hrel : AbsFV.Rel x 0 ((some x, d) :: Δ) ((none, d) :: Δ) := by
    have hxx : (x == x) = true := (fvarId_beq_iff x x).mpr rfl
    constructor
    · intro i t ht
      simpa [MLCtx.findB] using ht
    · intro y t ht
      simp only [MLCtx.findF] at ht
      by_cases hy : (y == x) = true
      · have hxy : (x == y) = true :=
          (fvarId_beq_iff x y).mpr ((fvarId_beq_iff y x).mp hy).symm
        simp only [hxy, ↓reduceIte, Option.some.injEq] at ht
        subst ht
        simp [hy, MLCtx.findB]
      · have hxy : (x == y) = false := by
          rcases Bool.eq_false_or_eq_true (x == y) with h' | h'
          · exact absurd ((fvarId_beq_iff y x).mpr ((fvarId_beq_iff x y).mp h').symm) hy
          · exact h'
        simp only [hxy, Bool.false_eq_true, ↓reduceIte] at ht
        simp only [hy, Bool.false_eq_true, ↓reduceIte, MLCtx.findF]
        exact ht
  have := AbsFV.Erases.absN x (AbsFV.closed_types henv hsub) h 0 _ hrel hcl
  rwa [AbsFV.absFV_inst hfv] at this

variable {σ : EvalEnv} {lenv : GlobalDeclarations}

theorem mem_toBvarList {x : FVarId} {k : Nat} : ∀ {as : List LBTerm} {a' : LBTerm},
    a' ∈ toBvarList x k as → ∃ a ∈ as, a' = toBvar x k a
  | [], _, h => nomatch h
  | a :: as, a', h => by
    simp only [toBvarList, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨a, .head _, rfl⟩
    · obtain ⟨b, hb, rfl⟩ := mem_toBvarList h
      exact ⟨b, .tail _ hb, rfl⟩

theorem mem_toBvarAlts {x : FVarId} {k : Nat} : ∀ {bs : List (List BinderName × LBTerm)}
    {b' : List BinderName × LBTerm}, b' ∈ toBvarAlts x k bs →
      ∃ b ∈ bs, b'.2 = toBvar x (k + b.1.length) b.2
  | [], _, h => nomatch h
  | (ns, t) :: bs, b', h => by
    simp only [toBvarAlts, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨_, .head _, rfl⟩
    · obtain ⟨b, hb, he⟩ := mem_toBvarAlts h
      exact ⟨b, .tail _ hb, he⟩

theorem mem_toBvarDefs {x : FVarId} {k : Nat} : ∀ {ds : List (@FixDef LBTerm)}
    {d' : @FixDef LBTerm}, d' ∈ toBvarDefs x k ds → ∃ d ∈ ds, d'.body = toBvar x k d.body
  | [], _, h => nomatch h
  | d :: ds, d', h => by
    simp only [toBvarDefs, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨_, .head _, rfl⟩
    · obtain ⟨b, hb, he⟩ := mem_toBvarDefs h
      exact ⟨b, .tail _ hb, he⟩

/-- Replacing a free variable by a bound one keeps the erased dependencies, which do not see
variables. Reference: `erases_deps_lift` (`MR E/EDeps.v:44`), for the traversal's abstraction
(DV-13). -/
theorem ErasesDeps.toBvar {t : LBTerm} {x : FVarId} (h : ErasesDeps E B σ lenv t) :
    ∀ k, ErasesDeps E B σ lenv (_root_.toBvar x k t) := by
  induction h with
  | box => intro; exact .box
  | bvar => intro; exact .bvar
  | fvar =>
    intro k
    simp only [_root_.toBvar]
    split
    · exact .bvar
    · exact .fvar
  | lambda _ ih => intro k; exact .lambda (ih _)
  | letIn _ _ ihv ihb => intro k; exact .letIn (ihv _) (ihb _)
  | app _ _ ihf iha => intro k; exact .app (ihf _) (iha _)
  | const hc hl hd hb _ => intro; exact .const hc hl hd hb
  | construct hi hind _ ih =>
    intro k
    refine .construct hi hind fun a' ha' => ?_
    obtain ⟨a, ha, rfl⟩ := mem_toBvarList ha'
    exact ih a ha k
  | case hi hind _ _ ihd ihb =>
    intro k
    refine .case hi hind (ihd k) fun b' hb' => ?_
    obtain ⟨b, hb, he⟩ := mem_toBvarAlts hb'
    rw [he]
    exact ihb b hb _
  | proj hi hind _ ih => intro k; exact .proj hi hind (ih k)
  | fix _ ih =>
    intro k
    simp only [_root_.toBvar]
    refine .fix fun d' hd' => ?_
    obtain ⟨d, hd, he⟩ := mem_toBvarDefs hd'
    rw [he]
    exact ih d hd _

end

/-! ## The invariants and the statement at one fuel -/

/-- The free variable that the pure backend's `freshFVarId` allocates at the counter value `k`.
Reference: none (DV-13). -/
abbrev pureFVar (k : Nat) : FVarId := ⟨.num `_pure k⟩

/-- The pure backend's `freshFVarId` returns `pureFVar` of the counter and increments it. -/
theorem fresh_run {pc : PureCtx} {tc : TravCtx} {st : ErasureState} {ps : PureState} :
    (liftM (Backend.freshFVarId (m := PureM)) : EraseT PureM FVarId).runPure st tc pc ps =
      .ok ((pureFVar ps.next, st), ⟨ps.next + 1⟩) := rfl

theorem runPure_withReader {α : Type} {pc : PureCtx} {tc : TravCtx} {st : ErasureState}
    {ps : PureState} (f : TravCtx → TravCtx) (x : EraseT PureM α) :
    (withReader f x).runPure st tc pc ps = x.runPure st (f tc) pc ps := rfl

/-- Under `nat := .machine`, `e` has no Nat literal and mentions neither `Nat.zero` nor
`Nat.casesOn`, which `Erasure.exprConsts` excludes under that configuration: the traversal erases
them to primitive integers (`visitLiteral`, `visitConstructor`, `visitCasesOn`), which the erasure
relation does not model. -/
def NatPlain (cfg : ErasureConfig) : Expr → Prop
  | .lit (.natVal _) => cfg.nat = .peano
  | .const c _ => cfg.nat = .machine → c ≠ ``Nat.zero ∧ c ≠ ``Nat.casesOn
  | .app f a => NatPlain cfg f ∧ NatPlain cfg a
  | .lam _ t b _ | .forallE _ t b _ => NatPlain cfg t ∧ NatPlain cfg b
  | .letE _ t v b _ => NatPlain cfg t ∧ NatPlain cfg v ∧ NatPlain cfg b
  | .mdata _ e | .proj _ _ e => NatPlain cfg e
  | _ => True

/-- `NatPlain` survives lifting loose bound variables. -/
theorem np_lift {cfg : ErasureConfig} : ∀ {e : Expr} {s d : Nat}, NatPlain cfg e →
    NatPlain cfg (e.liftLooseBVars' s d) := by
  intro e
  induction e <;> intro s d h <;> simp_all [Expr.liftLooseBVars', NatPlain]

/-- `NatPlain` survives instantiating a bound variable with a `NatPlain` term. -/
theorem np_inst {cfg : ErasureConfig} {a : Expr} (ha : NatPlain cfg a) :
    ∀ {b : Expr} {d : Nat}, NatPlain cfg b → NatPlain cfg (b.instantiate1' a d) := by
  intro b
  induction b with
  | bvar i =>
    intro d _
    simp only [Expr.instantiate1']
    split_ifs
    · trivial
    · exact np_lift ha
    · trivial
  | _ => intro d h; simp_all [Expr.instantiate1', NatPlain]

/-- The facts about the program and its closure `decls` that the steps use: the program is the
Lean form of a well-formed Metalean environment, `decls` is a sub-environment closed under what
the traversal reads, with distinct kernames and block names, closed read expressions, in the
fragment (`PhaseIDecl`, `MachineFree`, `NatPlain`, no recursor read, syntactic arities) and with
the shapes that the frame lemma needs (`OwnBlockValues`, `NoIndexFields`); constructor fields are
kept whenever the closure has an inductive type.
Reference: the hypotheses of `erases_erase` (`MR E/ErasureFunction.v:1228`): `wf_ext Σ` and the
abstract environment's relation to `Σ`. -/
structure CoreEnv {ζ : Metalean.Sigs} (E : Metalean.Env ζ) (B : Binds ζ) (P decls : List ConstantInfo)
    (view : EnvView) (cfg : ErasureConfig) : Prop where
  prog : ProgEnv P ζ E B
  wf : EnvWF E
  sub : SubEnv decls P
  inj : KernameInj decls
  bn : BlockNamesInj decls
  closed : ClosedDecls decls
  deps : DepClosed decls
  mfd : ∀ ci ∈ decls, ∀ x, ReadExpr decls ci x → MachineFree cfg x
  npd : ∀ ci ∈ decls, ∀ x, ReadExpr decls ci x → NatPlain cfg x
  blk : OwnBlockValues decls
  idx : NoIndexFields decls
  phase : ∀ ci ∈ decls, PhaseIDecl view cfg decls ci
  recShaped : ∀ ci ∈ decls, ∀ x, ReadExpr decls ci x → RecShaped cfg decls x
  arity : ArityTypes decls
  irr : ∀ iv, (∃ ci ∈ decls, ci = .inductInfo iv) → cfg.remove_irrel_constr_args = false

/-- The traversal's context invariant at the pure backend, over the Metalean context `Γ` and the
locals `Δ`: `Γ` is well formed, the traversal's locals are the Lean form of `Γ` through `Δ`
(`LocalsOK`), `Δ` has only free-variable entries, every variable the counter will allocate is
fresh for `Δ`, no fix variable is bound (the pure path never enters a recursive block,
`isRecursiveDecl_false`), and the configuration is `cfg`. Reference: the context `Γ` of
`erases_erase` (`MR E/ErasureFunction.v:1228`), here locals opened with fresh variables (DV-13). -/
structure CtxOK {ζ : Metalean.Sigs} (E : Metalean.Env ζ) (B : Binds ζ) (lps : List Name) {n : Nat}
    (Γ : Metalean.Ctx ζ lps.length 0 n) (Δ : MLCtx ζ lps.length n) (cfg : ErasureConfig)
    (tc : TravCtx) (ps : PureState) : Prop where
  wf : E[Γ] ⊢ ok
  locals : LocalsOK E B lps Γ Δ tc.locals
  nobv : ∀ i, Δ.findB i = none
  fresh : ∀ k, ps.next ≤ k → Δ.findF (pureFVar k) = none
  fixvars : tc.fixvars = none
  config : tc.config = cfg

/-- What a run of the traversal from the states `st`, `ps` to `st'`, `ps'` guarantees: the state
invariant holds after it (`StateOK`), the λ□ environment grows by fresh kernames (`LenvExt`), the
counter does not decrease, and every constant it registers is in the scope `S`. Reference:
`includes_deps` (`MR E/ErasureFunctionProperties.v:41`), the invariant of `erase_global_deps`
(`MR E/ErasureFunction.v:1602`), and `erase_global_deps_fresh`
(`MR E/ErasureFunctionProperties.v:1206`). -/
structure Grows {ζ : Metalean.Sigs} (E : Metalean.Env ζ) (B : Binds ζ) (σ : EvalEnv)
    (S : Name → Prop) (st st' : ErasureState) (ps ps' : PureState) : Prop where
  inv : StateOK E B σ st'
  ext : LenvExt st.gdecls st'.gdecls
  next : ps.next ≤ ps'.next
  scope : ∀ c kn, st.constants[c]? = none → st'.constants[c]? = some kn → S c

/-- A scope of the traversal: a set of constants declared in `decls`, closed under the constants
that occur (`nameOccurs`, the positions the traversal erases) in the values that `visitMutual`
erases (those of declarations that are neither theorems, which the oracle boxes, nor recognized
`casesOn` constants, which `visitCases` erases). Reference: the dependencies `term_global_deps`
(`MR E/EAstUtils.v:406`) that `erase_global_deps` (`MR E/ErasureFunction.v:1602`) follows,
transitively. -/
def ScopeOK (decls : List ConstantInfo) (S : Name → Prop) : Prop :=
  ∀ c, S c → ∃ ci, findDecl decls c = some ci ∧ ∀ v, ci.value? (allowOpaque := true) = some v →
    IsThm ci = false → casesInfo? decls c = none → ∀ d, nameOccurs d v = true → S d

/-- The correctness of `visitExpr fuel e` at the pure backend over the closure `decls`: from a
state with `StateOK`, under locals that are the Lean form of the context (`CtxOK`), on a term
translated and typed in that context whose constants occur in a scope `S` and which is
`MachineFree` and `NatPlain` and reads recursors only in the fragment's shape (`RecShaped`), a
successful run returns an
erasure of `e` (`Erases`) whose λ□ dependencies are erased in the final environment, and it `Grows` within `S`. Reference: `erases_erase`
(`MR E/ErasureFunction.v:1228`) with `erase_global_erases_deps`
(`MR E/ErasureFunctionProperties.v:172`). -/
def ExprSpec {ζ : Metalean.Sigs} (E : Metalean.Env ζ) (B : Binds ζ) (view : EnvView)
    (cfg : ErasureConfig) (decls : List ConstantInfo) (fuel : Nat) (e : Expr) : Prop :=
  ∀ ⦃lps : List Name⦄ ⦃n : Nat⦄ ⦃Γ : Metalean.Ctx ζ lps.length 0 n⦄ ⦃Δ : MLCtx ζ lps.length n⦄
    ⦃S : Name → Prop⦄ ⦃t : Metalean.Expr ζ lps.length n⦄ ⦃st : ErasureState⦄ ⦃tc : TravCtx⦄
    ⦃ps : PureState⦄ ⦃r : LBTerm⦄ ⦃st' : ErasureState⦄ ⦃ps' : PureState⦄,
    CtxOK E B lps Γ Δ cfg tc ps → ScopeOK decls S → (∀ d, nameOccurs d e = true → S d) →
    MachineFree cfg e → NatPlain cfg e → RecShaped cfg decls e →
    StateOK E B (evalEnvOf view cfg decls) st → TrM E B lps Γ Δ e t → (∃ T, E[Γ] ⊢ t : T) →
    (visitExpr (m := PureM) fuel e).runPure st tc ⟨decls, view⟩ ps = .ok ((r, st'), ps') →
    Erases E B lps (evalEnvOf view cfg decls) Γ Δ e r ∧
      ErasesDeps E B (evalEnvOf view cfg decls) st'.gdecls r ∧
      Grows E B (evalEnvOf view cfg decls) S st st' ps ps'

/-- The correctness of `visitMutual fuel c` at the pure backend: on an unregistered constant of a
scope `S` that is a definition, an opaque or an axiom (`EmitsConst`, not a theorem), or `Quot.ind`,
and not a recognized `casesOn` constant, from a state with
`StateOK`, a successful run registers `c` and `Grows` within `S`. Reference: the `ConstantDecl`
step of `erase_global_deps` (`MR E/ErasureFunction.v:1602`), which erases a declaration with
`erase_constant_body` (`MR E/ErasureFunction.v:1309`). -/
def MutualSpec {ζ : Metalean.Sigs} (E : Metalean.Env ζ) (B : Binds ζ) (view : EnvView)
    (cfg : ErasureConfig) (decls : List ConstantInfo) (fuel : Nat) (c : Name) : Prop :=
  ∀ ⦃S : Name → Prop⦄ ⦃st : ErasureState⦄ ⦃tc : TravCtx⦄ ⦃ps : PureState⦄
    ⦃st' : ErasureState⦄ ⦃ps' : PureState⦄,
    ScopeOK decls S → S c → tc.config = cfg → tc.fixvars = none →
    (∀ v, findDecl decls c ≠ some (.thmInfo v)) → casesInfo? decls c = none →
    (∃ ci, findDecl decls c = some ci ∧
      (EmitsConst ci = true ∨ ∃ q, ci = .quotInfo q ∧ q.kind = .ind)) →
    StateOK E B (evalEnvOf view cfg decls) st → st.constants[c]? = none →
    (visitMutual (m := PureM) fuel c).runPure st tc ⟨decls, view⟩ ps = .ok (((), st'), ps') →
    Grows E B (evalEnvOf view cfg decls) S st st' ps ps' ∧ ∃ kn, st'.constants[c]? = some kn

/-- The induction hypothesis of every step at fuel `fuel + 1`: `ExprSpec` and `MutualSpec` at
every fuel up to `fuel`. The proof of `erasePure_erases` builds it by induction on `fuel` from the
steps of each case. Reference: the induction of `erases_erase`
(`MR E/ErasureFunction.v:1228`), on the fuel of the shipping traversal. -/
structure StepIH {ζ : Metalean.Sigs} (E : Metalean.Env ζ) (B : Binds ζ) (view : EnvView)
    (cfg : ErasureConfig) (decls : List ConstantInfo) (fuel : Nat) : Prop where
  expr : ∀ m ≤ fuel, ∀ e, ExprSpec E B view cfg decls m e
  mutDecl : ∀ m ≤ fuel, ∀ c, MutualSpec E B view cfg decls m c

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {σ : EvalEnv} {S : Name → Prop}

theorem LenvExt.refl {lenv : GlobalDeclarations} : LenvExt lenv lenv :=
  ⟨[], rfl, fun _ h => nomatch h⟩

theorem LenvExt.trans {l₁ l₂ l₃ : GlobalDeclarations} (h₁ : LenvExt l₁ l₂) (h₂ : LenvExt l₂ l₃) :
    LenvExt l₁ l₃ := by
  obtain ⟨n₁, rfl, f₁⟩ := h₁
  obtain ⟨n₂, rfl, f₂⟩ := h₂
  refine ⟨n₂ ++ n₁, by simp, fun kn hkn => ?_⟩
  rw [List.map_append, List.mem_append] at hkn
  rcases hkn with hkn | hkn
  · have := f₂ kn hkn
    rw [List.find?_append, Option.or_eq_none_iff] at this
    exact this.2
  · exact f₁ kn hkn

/-- A run that changes neither state grows. -/
theorem Grows.refl {st : ErasureState} {ps : PureState} (hok : StateOK E B σ st) :
    Grows E B σ S st st ps ps :=
  ⟨hok, LenvExt.refl, Nat.le_refl _, fun _ _ h h' => by rw [h] at h'; cases h'⟩

/-- Consecutive runs grow. -/
theorem Grows.trans {st st₁ st₂ : ErasureState} {ps ps₁ ps₂ : PureState}
    (h₁ : Grows E B σ S st st₁ ps ps₁) (h₂ : Grows E B σ S st₁ st₂ ps₁ ps₂) :
    Grows E B σ S st st₂ ps ps₂ := by
  refine ⟨h₂.inv, LenvExt.trans h₁.ext h₂.ext, Nat.le_trans h₁.next h₂.next, fun c kn h h' => ?_⟩
  cases h1 : st₁.constants[c]? with
  | none => exact h₂.scope c kn h1 h'
  | some kn₁ => exact h₁.scope c kn₁ h h1

variable {lps : List Name} {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
  {Δ : MLCtx ζ lps.length n} {cfg : ErasureConfig}

/-- The context invariant survives the counter's growth. -/
theorem CtxOK.mono {tc : TravCtx} {ps ps' : PureState} (h : CtxOK E B lps Γ Δ cfg tc ps)
    (hle : ps.next ≤ ps'.next) : CtxOK E B lps Γ Δ cfg tc ps' :=
  ⟨h.wf, h.locals, h.nobv, fun k hk => h.fresh k (Nat.le_trans hle hk), h.fixvars, h.config⟩

/-- The context invariant does not read the `LocalContext`, which the pure backend never reads. -/
theorem CtxOK.setLctx {tc : TravCtx} {ps : PureState} (h : CtxOK E B lps Γ Δ cfg tc ps)
    (L : LocalContext) : CtxOK E B lps Γ Δ cfg { tc with lctx := L } ps :=
  ⟨h.wf, h.locals, h.nobv, h.fresh, h.fixvars, h.config⟩

/-- The counter's variables are distinct. -/
theorem pureFVar_inj {k k' : Nat} (h : pureFVar k = pureFVar k') : k = k' := by
  cases h; rfl

/-- The next fresh variable is not a local. -/
theorem CtxOK.freshNext {tc : TravCtx} {ps : PureState} (h : CtxOK E B lps Γ Δ cfg tc ps) :
    Δ.findF (pureFVar ps.next) = none :=
  h.fresh _ (Nat.le_refl _)

/-- Pushing the local of a λ/Π binder with the next fresh variable keeps the context invariant,
with the counter advanced. -/
theorem CtxOK.pushFVar {tc : TravCtx} {ps : PureState} {nm : Name} {A : Expr}
    {A' : Metalean.Expr ζ lps.length n} (h : CtxOK E B lps Γ Δ cfg tc ps)
    (hA : TrM E B lps Γ Δ A A') (hA' : E[Γ] ⊢ A' typ) (L : LocalContext) :
    CtxOK E B lps (Γ.snoc A') (Δ.pushLam (some (pureFVar ps.next))) cfg
      { tc with lctx := L, locals := ⟨pureFVar ps.next, nm, A, none⟩ :: tc.locals }
      ⟨ps.next + 1⟩ := by
  refine ⟨.snoc h.wf hA', h.locals.pushFVar h.freshNext hA hA' h.wf, fun i => ?_,
    fun k hk => ?_, h.fixvars, h.config⟩
  · simp [MLCtx.pushLam, MLCtx.findB, MLCtx.findB_map_wk, h.nobv i]
  · have hne : (pureFVar ps.next == pureFVar k) = false := by
      rcases Bool.eq_false_or_eq_true (pureFVar ps.next == pureFVar k) with h' | h'
      · have := pureFVar_inj ((fvarId_beq_iff _ _).mp h')
        dsimp only at hk; omega
      · exact h'
    simp [MLCtx.pushLam, MLCtx.findF, MLCtx.findF_map_wk, hne, h.fresh k (by dsimp only at hk; omega)]

/-- Pushing the local of a `let` binder with the next fresh variable keeps the context invariant,
with the counter advanced. -/
theorem CtxOK.pushLet {tc : TravCtx} {ps : PureState} {nm : Name} {T v : Expr}
    {T' v' : Metalean.Expr ζ lps.length n} (h : CtxOK E B lps Γ Δ cfg tc ps)
    (hT : TrM E B lps Γ Δ T T') (hv : TrM E B lps Γ Δ v v') (hvT : E[Γ] ⊢ v' : T')
    (L : LocalContext) :
    CtxOK E B lps Γ ((some (pureFVar ps.next), .vlet v') :: Δ) cfg
      { tc with lctx := L, locals := ⟨pureFVar ps.next, nm, T, some v⟩ :: tc.locals }
      ⟨ps.next + 1⟩ := by
  refine ⟨h.wf, h.locals.pushLet h.freshNext hT hv hvT, fun i => ?_, fun k hk => ?_,
    h.fixvars, h.config⟩
  · simpa [MLCtx.findB] using h.nobv i
  · have hne : (pureFVar ps.next == pureFVar k) = false := by
      rcases Bool.eq_false_or_eq_true (pureFVar ps.next == pureFVar k) with h' | h'
      · have := pureFVar_inj ((fvarId_beq_iff _ _).mp h')
        dsimp only at hk; omega
      · exact h'
    simp [MLCtx.findF, hne, h.fresh k (by dsimp only at hk; omega)]

end

/-! ## Runs of the traversal's helpers -/

section
open TravFrame
variable {pc : PureCtx}

/-- `Except`'s bind on a success. -/
theorem ok_bind' {ε α β : Type} {a : α} {f : α → Except ε β} :
    ((Except.ok a : Except ε α) >>= f) = f a := rfl

/-- A successful run of the oracle call that starts each unfolding of `Erasure.visitExpr` either
answered `true` and returned `□` without changing the states, or answered `false` and ran the
branch `K`. Reference: `is_erasableb` at the start of `erase` (`MR E/ErasureFunction.v:992`). -/
theorem oracle_run {e : Expr} {K : EraseT PureM LBTerm} {tc : TravCtx} {st st' : ErasureState}
    {ps ps' : PureState} {r : LBTerm}
    (h : (read >>= fun c₁ => read >>= fun c₂ =>
        (liftM (Backend.isErasable (m := PureM) c₁.lctx c₂.locals e) : EraseT PureM Bool) >>=
          fun b => if b = true then Pure.pure LBTerm.box else K).runPure st tc pc ps =
      .ok ((r, st'), ps')) :
    (Pure.isErasable ⟨pc.decls⟩ oracleFuel tc.locals e = .ok true ∧ r = .box ∧ st' = st ∧
      ps' = ps) ∨
    (Pure.isErasable ⟨pc.decls⟩ oracleFuel tc.locals e = .ok false ∧
      K.runPure st tc pc ps = .ok ((r, st'), ps')) := by
  rw [runPure_read_bind, runPure_read_bind, runPure_bind, runPure_liftM, isErasable_run] at h
  cases hor : Pure.isErasable ⟨pc.decls⟩ oracleFuel tc.locals e with
  | error err => rw [hor] at h; cases h
  | «ok» b =>
    rw [hor] at h
    cases b with
    | true => cases h; exact .inl ⟨rfl, rfl, rfl, rfl⟩
    | false => exact .inr ⟨rfl, h⟩

/-- `mkLambda x body` closes `body` over `x` with the traversal's `abstract`, under the λ□ name of
the local found for `x`. Reference: the `tLambda` case of `erase`
(`MR E/ErasureFunction.v:1003`); DV-13. -/
theorem fvar_to_name_run {tc : TravCtx} {st : ErasureState} {ps : PureState} {x : FVarId}
    {l : Local} (hf : tc.locals.find? (·.fvarId == x) = some l) :
    (fvar_to_name (m := PureM) x).runPure st tc pc ps =
      .ok ((binderNameOf l.userName, st), ps) := by
  unfold fvar_to_name
  have hr : (read : EraseT PureM TravCtx).runPure st tc pc ps = .ok ((tc, st), ps) := rfl
  rw [runPure_bind, hr, ok_bind']
  dsimp only
  simp only [getOrFail, hf]
  rfl

theorem mkLambda_run {tc : TravCtx} {st : ErasureState} {ps : PureState} {x : FVarId} {l : Local}
    {ls : List Local} {body : LBTerm} (hl : tc.locals = l :: ls) (hx : l.fvarId = x) :
    (Erasure.mkLambda (m := PureM) x body).runPure st tc pc ps =
      .ok ((.lambda (binderNameOf l.userName) (_root_.abstract x body), st), ps) := by
  have hf : tc.locals.find? (·.fvarId == x) = some l := by
    rw [hl, List.find?_cons, hx, (fvarId_beq_iff x x).mpr rfl]
  unfold Erasure.mkLambda
  rw [runPure_bind, fvar_to_name_run hf]
  rfl

/-- `mkLetIn x val body` closes `body` over `x` with the traversal's `abstract`, under the λ□ name
of the local found for `x`. Reference: the `tLetIn` case of `erase`
(`MR E/ErasureFunction.v:1005`); DV-13. -/
theorem mkLetIn_run {tc : TravCtx} {st : ErasureState} {ps : PureState} {x : FVarId} {l : Local}
    {ls : List Local} {val body : LBTerm} (hl : tc.locals = l :: ls) (hx : l.fvarId = x) :
    (mkLetIn (m := PureM) x val body).runPure st tc pc ps =
      .ok ((.letIn (binderNameOf l.userName) val (_root_.abstract x body), st), ps) := by
  have hf : tc.locals.find? (·.fvarId == x) = some l := by
    rw [hl, List.find?_cons, hx, (fvarId_beq_iff x x).mpr rfl]
  unfold Erasure.mkLetIn
  rw [runPure_bind, fvar_to_name_run hf]
  rfl

end

/-- Opening a binder with a free variable keeps the constants. -/
theorem ConstsIn_inst_fvar {p : Name → Prop} {x : FVarId} :
    ∀ {b : Expr} {k : Nat}, ConstsIn p b → ConstsIn p (b.instantiate1' (.fvar x) k)
  | .bvar i, k, _ => by
    simp only [Expr.instantiate1']
    split
    · trivial
    · split <;> trivial
  | .app f a, _, h => ⟨ConstsIn_inst_fvar (b := f) h.1, ConstsIn_inst_fvar (b := a) h.2⟩
  | .lam _ t b _, _, h | .forallE _ t b _, _, h =>
    ⟨ConstsIn_inst_fvar (b := t) h.1, ConstsIn_inst_fvar (b := b) h.2⟩
  | .letE _ t v b _, _, h =>
    ⟨ConstsIn_inst_fvar (b := t) h.1, ConstsIn_inst_fvar (b := v) h.2.1,
      ConstsIn_inst_fvar (b := b) h.2.2⟩
  | .mdata _ e, _, h => ConstsIn_inst_fvar (b := e) h
  | .proj _ _ e, _, h => ⟨h.1, ConstsIn_inst_fvar (b := e) h.2⟩
  | .const .., _, h => h
  | .sort _, _, _ | .fvar _, _, _ | .mvar _, _, _ | .lit _, _, _ => trivial

/-- Opening a binder with a free variable keeps the constants that occur. -/
theorem nameOccurs_inst_fvar {c : Name} {x : FVarId} :
    ∀ (b : Expr) (k : Nat), nameOccurs c (b.instantiate1' (.fvar x) k) = nameOccurs c b
  | .bvar i, k => by
    simp only [Expr.instantiate1']
    split
    · rfl
    · split <;> rfl
  | .app f a, k => by
    simp only [Expr.instantiate1', nameOccurs, nameOccurs_inst_fvar f, nameOccurs_inst_fvar a]
  | .lam _ _ b _, k => by simp only [Expr.instantiate1', nameOccurs, nameOccurs_inst_fvar b]
  | .letE _ _ v b _, k => by
    simp only [Expr.instantiate1', nameOccurs, nameOccurs_inst_fvar v, nameOccurs_inst_fvar b]
  | .mdata _ e, k => by simp only [Expr.instantiate1', nameOccurs, nameOccurs_inst_fvar e]
  | .proj _ _ e, k => by simp only [Expr.instantiate1', nameOccurs, nameOccurs_inst_fvar e]
  | .forallE .., _ | .const .., _ | .sort _, _ | .fvar _, _ | .mvar _, _ | .lit _, _ => rfl

/-! ## The steps of `visitExpr` without constants -/

section
open TravFrame
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P decls : List ConstantInfo}
  {view : EnvView} {cfg : ErasureConfig}

/-- The `box` step, shared by every case of `visitExpr`: when the oracle answers `true` on a
translated, typed term, `□` erases it (`Pure.isErasable_sound`, `Erases.box`). Reference: the
`is_erasableb` case of `erases_erase` (`MR E/ErasureFunction.v:1228`), rule `erases_box`
(`MR E/Extract.v:140`). -/
theorem visitExpr_box {lps : List Name} {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
    {Δ : MLCtx ζ lps.length n} {S : Name → Prop} {tc : TravCtx} {ps : PureState}
    {st : ErasureState} {e : Expr} {t : Metalean.Expr ζ lps.length n}
    (hG : CoreEnv E B P decls view cfg) (hctx : CtxOK E B lps Γ Δ cfg tc ps)
    (hok : StateOK E B (evalEnvOf view cfg decls) st) (he : TrM E B lps Γ Δ e t)
    (ht : ∃ T, E[Γ] ⊢ t : T)
    (hor : Pure.isErasable ⟨decls⟩ oracleFuel tc.locals e = .ok true) :
    Erases E B lps (evalEnvOf view cfg decls) Γ Δ e .box ∧
      ErasesDeps E B (evalEnvOf view cfg decls) st.gdecls .box ∧
      Grows E B (evalEnvOf view cfg decls) S st st ps ps :=
  ⟨.box (Pure.isErasable_sound hG.prog hG.wf hG.sub hctx.wf hctx.locals hctx.nobv he ht hor),
    .box, .refl hok⟩

/-- The `fvar` step: a free variable the oracle keeps erases to itself. Reference: the `tVar`
case of `erases_erase` (`MR E/ErasureFunction.v:1228`), rule `erases_tVar` (`MR E/Extract.v:90`);
DV-13. -/
theorem visitExpr_fvar_step (hG : CoreEnv E B P decls view cfg) {fuel : Nat} {x : FVarId} :
    ExprSpec E B view cfg decls (fuel + 1) (.fvar x) := by
  intro lps n Γ Δ S t st tc ps r st' ps' hctx _ _ _ _ _ hok he ht hrun
  rw [visitExpr] at hrun
  rcases oracle_run hrun with ⟨hor, rfl, rfl, rfl⟩ | ⟨-, hrun⟩
  · exact visitExpr_box hG hctx hok he ht hor
  cases hrun
  exact ⟨.fvar, .fvar, .refl hok⟩

/-- The steps on the terms `visitExpr` rejects after the oracle: a sort and a Π, which the oracle
answers `true` on whenever the traversal goes on, a bound variable (no translation under locals
without bound entries) and a metavariable (no translation). Reference: the `tSort` and `tProd`
cases of `erase` (`MR E/ErasureFunction.v:998`, `:1002`), unreachable after `is_erasableb`. -/
theorem visitExpr_fail_step (hG : CoreEnv E B P decls view cfg) {fuel : Nat} {e : Expr}
    (hk : (e.isBVar || e.isSort || e.isForall || e.isMVar) = true) :
    ExprSpec E B view cfg decls (fuel + 1) e := by
  intro lps n Γ Δ S t st tc ps r st' ps' hctx _ _ _ _ _ hok he ht hrun
  cases e <;> simp [Expr.isBVar, Expr.isSort, Expr.isForall, Expr.isMVar] at hk <;>
  · rw [visitExpr] at hrun
    rcases oracle_run hrun with ⟨hor, rfl, rfl, rfl⟩ | ⟨-, hrun⟩
    · exact visitExpr_box hG hctx hok he ht hor
    · cases hrun

/-- The `mdata` step, from `visitExpr` at `fuel`: metadata is transparent. Reference: none (PCUIC
has no metadata). -/
theorem visitExpr_mdata_step (hG : CoreEnv E B P decls view cfg) {fuel : Nat}
    (ih : StepIH E B view cfg decls fuel) {d : MData} {e : Expr} :
    ExprSpec E B view cfg decls (fuel + 1) (.mdata d e) := by
  intro lps n Γ Δ S t st tc ps r st' ps' hctx hsc hocc hmf hnp hrf hok he ht hrun
  rw [visitExpr] at hrun
  rcases oracle_run hrun with ⟨hor, rfl, rfl, rfl⟩ | ⟨-, hrun⟩
  · exact visitExpr_box hG hctx hok he ht hor
  have ⟨her, hdeps, hgr⟩ := ih.expr fuel (Nat.le_refl _) e hctx hsc
    (fun c hc => hocc c (by simpa [nameOccurs] using hc)) hmf hnp hrf hok (trM_mdata_inv he) ht hrun
  exact ⟨.mdata her, hdeps, hgr⟩

/-- The `lam` step, from `visitExpr` at the fuels up to `fuel`: the body is opened with a fresh
variable (`CtxOK.pushFVar`), erased, and closed again by the traversal's `abstract`
(`Erases.abstract`). Reference: the `tLambda` case of `erases_erase`
(`MR E/ErasureFunction.v:1228`), rule `erases_tLambda` (`MR E/Extract.v:93`); DV-13. -/
theorem visitExpr_lam_step (hG : CoreEnv E B P decls view cfg) {fuel : Nat}
    (ih : StepIH E B view cfg decls fuel) {x : Name} {A b : Expr} {bi : BinderInfo} :
    ExprSpec E B view cfg decls (fuel + 1) (.lam x A b bi) := by
  intro lps n Γ Δ S t st tc ps r st' ps' hctx hsc hocc hmf hnp hrf hok he ht hrun
  rw [visitExpr] at hrun
  rcases oracle_run hrun with ⟨hor, rfl, rfl, rfl⟩ | ⟨-, hrun⟩
  · exact visitExpr_box hG hctx hok he ht hor
  cases fuel with
  | zero => rw [visitLambda] at hrun; cases hrun
  | succ k =>
  rw [visitLambda] at hrun
  simp only [lambdaMonocular, withLocalDecl] at hrun
  rw [runPure_bind, fresh_run, ok_bind'] at hrun
  dsimp only at hrun
  rw [runPure_withReader, runPure_bind] at hrun
  obtain ⟨⟨⟨r₀, st₁⟩, ps₁⟩, hbody, hrun⟩ := OracleWhnf.ok_of_bind hrun
  dsimp only at hrun
  rw [mkLambda_run (l := ⟨pureFVar ps.next, x, A, none⟩) rfl rfl] at hrun
  cases hrun
  obtain ⟨A', b', rfl, hA, hb⟩ := trM_lam_inv he
  obtain ⟨T, hT⟩ := ht
  obtain ⟨tb', hb', hTeq⟩ := Metalean.Defeq.lam_inv hT hctx.wf
  have hA' : E[Γ] ⊢ A' typ := by
    obtain ⟨_, h⟩ := hTeq.right
    exact (Metalean.Defeq.forallE_inv h).1
  have hxΔ := hctx.freshNext
  have hctx' := hctx.pushFVar (nm := x) hA hA' (tc.lctx.mkLocalDecl (pureFVar ps.next) x A bi)
  have hbody' := TrM.inst_fvar hxΔ hb
  have ⟨her, hdeps, hgr⟩ := ih.expr k (Nat.le_succ _) _ hctx' hsc
    (fun d hd => hocc d (by rw [nameOccurs_inst_fvar] at hd; simpa [nameOccurs] using hd))
    (mf_inst (a := .fvar (pureFVar ps.next)) trivial hmf.2)
    (np_inst (a := .fvar (pureFVar ps.next)) trivial hnp.2) (ConstsIn_inst_fvar hrf.2) hok hbody'
    ⟨_, hb'⟩ hbody
  have hfv : FVarsIn (· ≠ pureFVar ps.next) b := by
    have h := (TrM.fvarsIn (TrM.lam (x := x) (bi := bi) hA hb)).2
    refine fvarsIn_mono (fun y hy hyx => ?_) h
    subst hyx
    simp [hxΔ] at hy
  have hcl : closedn 0 r₀ = true := by
    have := Erases.closed hbody' her
    rwa [countP_none hctx'.nobv] at this
  exact ⟨.lam hA hA' (Erases.abstract hG.prog hG.sub hxΔ hfv hcl her), .lambda (ErasesDeps.toBvar hdeps 0),
    ⟨hgr.inv, hgr.ext, Nat.le_trans (Nat.le_succ _) hgr.next, hgr.scope⟩⟩

/-- The `letE` step, from `visitExpr` at the fuels up to `fuel`: the value is visited under the
`let`'s own local, which it does not mention, so as under the caller's locals (`visit_agree`),
and erased there; the body as in `visitExpr_lam_step`, under the `let`'s free-variable entry
(`CtxOK.pushLet`), and closed again by the traversal's `abstract` (`Erases.abstract_let`).
Reference: the `tLetIn` case of `erases_erase` (`MR E/ErasureFunction.v:1228`), rule
`erases_tLetIn` (`MR E/Extract.v:96`); DV-13. -/
theorem visitExpr_letE_step (hG : CoreEnv E B P decls view cfg) {fuel : Nat}
    (ih : StepIH E B view cfg decls fuel) {x : Name} {T v b : Expr} {nd : Bool} :
    ExprSpec E B view cfg decls (fuel + 1) (.letE x T v b nd) := by
  intro lps n Γ Δ S t st tc ps r st' ps' hctx hsc hocc hmf hnp hrf hok he ht hrun
  rw [visitExpr] at hrun
  rcases oracle_run hrun with ⟨hor, rfl, rfl, rfl⟩ | ⟨-, hrun⟩
  · exact visitExpr_box hG hctx hok he ht hor
  cases fuel with
  | zero => rw [visitLet] at hrun; cases hrun
  | succ k =>
  rw [visitLet] at hrun
  simp only [letMonocular, withLocalDef] at hrun
  rw [runPure_bind, fresh_run, ok_bind'] at hrun
  dsimp only at hrun
  rw [runPure_withReader, runPure_bind] at hrun
  obtain ⟨⟨⟨tv, st₁⟩, ps₁⟩, hval, hrun⟩ := OracleWhnf.ok_of_bind hrun
  dsimp only at hrun
  rw [runPure_bind] at hrun
  obtain ⟨⟨⟨tb, st₂⟩, ps₂⟩, hbody, hrun⟩ := OracleWhnf.ok_of_bind hrun
  dsimp only at hrun
  rw [mkLetIn_run (l := ⟨pureFVar ps.next, x, T, some v⟩) rfl rfl] at hrun
  cases hrun
  have hfv := TrM.fvarsIn he
  obtain ⟨T', v', b', rfl, hT, hv, hb⟩ := trM_letE_inv he
  obtain ⟨U, hU⟩ := ht
  obtain ⟨R, -, hvT, hbR, -⟩ := Metalean.Defeq.letE_inv hU hctx.wf
  rw [Metalean.Expr.inst_wk] at hbR
  have hxΔ := hctx.freshNext
  have hfx : ∀ {e : Expr}, FVarsIn (fun y => (Δ.findF y).isSome) e →
      FVarsIn (· ≠ pureFVar ps.next) e :=
    fun h => fvarsIn_mono (fun y hy hyx => by subst hyx; simp [hxΔ] at hy) h
  have hne : ∀ y, y ≠ pureFVar ps.next → (pureFVar ps.next == y) = false := fun y hy =>
    Bool.eq_false_iff.mpr fun h => hy ((fvarId_beq_iff _ _).mp h).symm
  -- the value, under the `let`'s own local, is visited as under the caller's locals
  have hval' : (visitExpr (m := PureM) k v).runPure st
      { tc with lctx := tc.lctx.mkLetDecl (pureFVar ps.next) x T v nd } ⟨decls, view⟩
        ⟨ps.next + 1⟩ = .ok ((tv, st₁), ps₁) := by
    rw [← hval]
    refine (visit_agree (S := (· ≠ pureFVar ps.next))
      (tc := { tc with lctx := tc.lctx.mkLetDecl (pureFVar ps.next) x T v nd })
      (ls₁ := ⟨pureFVar ps.next, x, T, some v⟩ :: tc.locals) (ls₂ := tc.locals) hG.closed
      (by rw [show ({ tc with lctx := tc.lctx.mkLetDecl (pureFVar ps.next) x T v nd } :
          TravCtx).config = cfg from hctx.config]; exact hmf.2.1)
      (by rw [show ({ tc with lctx := tc.lctx.mkLetDecl (pureFVar ps.next) x T v nd } :
          TravCtx).config = cfg from hctx.config]; exact hG.mfd)
      hG.blk hG.idx ?_ ?_ (hfx hfv.2.1)).symm
    · intro y hy l hl
      simp only [Pure.findLocal, List.find?_cons, hne y hy] at hl
      obtain ⟨A, a, hA, -, -, hav⟩ := hctx.locals l (List.mem_of_find?_eq_some hl)
      exact ⟨hfx (TrM.fvarsIn hA), fun w hw => hfx (TrM.fvarsIn (hav w hw))⟩
    · intro y hy
      simp [Pure.findLocal, hne y hy]
  have ⟨herv, hdepsv, hgrv⟩ := ih.expr k (Nat.le_succ _) v ((hctx.setLctx _).mono (Nat.le_succ _))
    hsc (fun d hd => hocc d (by simp [nameOccurs, hd])) hmf.2.1 hnp.2.1 hrf.2.1 hok hv ⟨_, hvT⟩ hval'
  have hctx' := (hctx.pushLet (nm := x) hT hv hvT
    (tc.lctx.mkLetDecl (pureFVar ps.next) x T v nd)).mono hgrv.next
  have hbody' : TrM E B lps Γ ((some (pureFVar ps.next), .vlet v') :: Δ)
      (b.instantiate1' (.fvar (pureFVar ps.next))) b' :=
    TrM.instN_fvar hb (InstFV.zeroLet hxΔ _)
  have ⟨herb, hdepsb, hgrb⟩ := ih.expr k (Nat.le_succ _) _ hctx' hsc
    (fun d hd => hocc d (by rw [nameOccurs_inst_fvar] at hd; simp [nameOccurs, hd]))
    (mf_inst (a := .fvar (pureFVar ps.next)) trivial hmf.2.2)
    (np_inst (a := .fvar (pureFVar ps.next)) trivial hnp.2.2) (ConstsIn_inst_fvar hrf.2.2)
    hgrv.inv hbody' ⟨_, hbR⟩ hbody
  have hcl : closedn 0 tb = true := by
    have := Erases.closed hbody' herb
    rwa [countP_none hctx'.nobv] at this
  have hfb : FVarsIn (· ≠ pureFVar ps.next) b := hfx (by simpa [MLCtx.findF] using hfv.2.2)
  exact ⟨.letE hv ⟨_, hvT⟩ herv (Erases.abstract_let hG.prog hG.sub hxΔ hfb hcl herb),
    .letIn (ErasesDeps.ext hgrb.ext hdepsv) (ErasesDeps.toBvar hdepsb 0),
    Grows.trans ⟨hgrv.inv, hgrv.ext, Nat.le_trans (Nat.le_succ _) hgrv.next, hgrv.scope⟩ hgrb⟩

end

/-! ## Application spines and constants -/

theorem forall₂_mem {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ R l l') : ∀ a ∈ l, ∃ b ∈ l', R a b := by
  induction h with
  | nil => intro a ha; cases ha
  | cons hab _ ih =>
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_, .head _, hab⟩
    · obtain ⟨b, hb, h'⟩ := ih a ha
      exact ⟨b, .tail _ hb, h'⟩

/-- A property of applications that holds of both sides holds of a spine's head and arguments. -/
theorem foldl_pred {Q : Expr → Prop} (hQ : ∀ f a, Q (.app f a) → Q f ∧ Q a) :
    ∀ {f : Expr} {as : List Expr}, Q (as.foldl .app f) → Q f ∧ ∀ a ∈ as, Q a
  | _, [], h => ⟨h, by simp⟩
  | f, b :: as, h => by
    obtain ⟨h1, h2⟩ := foldl_pred hQ (f := .app f b) (as := as) h
    obtain ⟨hf, hb⟩ := hQ f b h1
    refine ⟨hf, fun a ha => ?_⟩
    rcases List.mem_cons.1 ha with rfl | ha
    · exact hb
    · exact h2 a ha

theorem getAppFn_getAppFn : ∀ e : Expr, e.getAppFn.getAppFn = e.getAppFn
  | .app f _ => getAppFn_getAppFn f
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const .. | .lam .. | .forallE .. | .letE .. | .lit _
  | .mdata .. | .proj .. => rfl

/-- A spine headed by an atom constant is an atom spine. -/
theorem AtomSpine.of_getAppFn {σ : EvalEnv} {c : Name} {us : List Level} (ha : σ.isAtom c = true) :
    ∀ {e : Expr}, e.getAppFn = .const c us → AtomSpine σ e
  | .const .., h => by cases h; exact .const ha
  | .app f _, h => .app (AtomSpine.of_getAppFn ha (e := f) h)
  | .bvar _, h | .fvar _, h | .mvar _, h | .sort _, h | .lam .., h | .forallE .., h
  | .letE .., h | .lit _, h | .mdata .., h | .proj .., h => nomatch h

section
open TravFrame
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P decls : List ConstantInfo}
  {view : EnvView} {cfg : ErasureConfig}

/-- The head and the arguments of a translated, typed spine whose head does not saturate are
translated and typed. Reference: `inversion_App` (`MR P/PCUICInversion.v:188`). -/
theorem spine_typed {lps : List Name} {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
    {Δ : MLCtx ζ lps.length n} {f : Expr} {as : List Expr} {t : Metalean.Expr ζ lps.length n}
    (hns : ¬ SpecialHead B f) (he : TrM E B lps Γ Δ (mkAppN f as.toArray) t)
    (ht : ∃ T, E[Γ] ⊢ t : T) :
    (∃ f', TrM E B lps Γ Δ f f' ∧ ∃ F, E[Γ] ⊢ f' : F) ∧
      ∀ a ∈ as, ∃ a', TrM E B lps Γ Δ a a' ∧ ∃ A, E[Γ] ⊢ a' : A := by
  obtain ⟨h', as', hh, has, rfl⟩ := CasesWhred.trM_spine_inv hns as he
  obtain ⟨T, hT⟩ := ht
  obtain ⟨hf, hargs⟩ := InstPre.appList_inv hT
  refine ⟨⟨h', hh, hf⟩, fun a ha => ?_⟩
  obtain ⟨a', ha', htr⟩ := forall₂_mem has a ha
  exact ⟨a', htr, hargs a' ha'⟩

/-- `visitAppArgs (j + 1) tf args`, from `visitExpr` at `j` (`ih`): applying an erasure of the head
to the erasures of the arguments, one at a time, erases the spine, when the head is neither a
constructor nor a recognized `casesOn` constant. Reference: the `tApp` case of `erases_erase`
(`MR E/ErasureFunction.v:1228`), rule `erases_tApp` (`MR E/Extract.v:101`). -/
theorem visitAppArgs_spec {j : Nat} (ih : ∀ e, ExprSpec E B view cfg decls j e)
    {lps : List Name} {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    {S : Name → Prop} {st st' : ErasureState} {tc : TravCtx} {ps ps' : PureState}
    {r tf : LBTerm} {f₀ : Expr} {args : List Expr}
    (hctx : CtxOK E B lps Γ Δ cfg tc ps) (hsc : ScopeOK decls S)
    (hargs : ∀ a ∈ args, (∀ d, nameOccurs d a = true → S d) ∧ MachineFree cfg a ∧
      NatPlain cfg a ∧ RecShaped cfg decls a ∧ ∃ a', TrM E B lps Γ Δ a a' ∧ ∃ A, E[Γ] ⊢ a' : A)
    (hns : ∀ c us, f₀.getAppFn = .const c us → (∀ cv, findDecl decls c ≠ some (.ctorInfo cv)) ∧
      (evalEnvOf view cfg decls).casesOn? c = none ∧
      (∀ qv, findDecl decls c = some (.quotInfo qv) → quotEvalArity qv.kind = none) ∧
      ∀ rv, findDecl decls c ≠ some (.recInfo rv))
    (hok : StateOK E B (evalEnvOf view cfg decls) st)
    (hf : Erases E B lps (evalEnvOf view cfg decls) Γ Δ f₀ tf)
    (hdf : ErasesDeps E B (evalEnvOf view cfg decls) st.gdecls tf)
    (hrun : (visitAppArgs (m := PureM) (j + 1) tf args.toArray).runPure st tc ⟨decls, view⟩ ps =
      .ok ((r, st'), ps')) :
    Erases E B lps (evalEnvOf view cfg decls) Γ Δ (mkAppN f₀ args.toArray) r ∧
      ErasesDeps E B (evalEnvOf view cfg decls) st'.gdecls r ∧
      Grows E B (evalEnvOf view cfg decls) S st st' ps ps' := by
  rw [visitAppArgs, ← Array.foldlM_toList, List.toList_toArray] at hrun
  induction args generalizing f₀ tf st ps with
  | nil =>
    cases hrun
    exact ⟨hf, hdf, .refl hok⟩
  | cons a l ihl =>
    rw [List.foldlM_cons, runPure_bind] at hrun
    obtain ⟨⟨⟨x, st₁⟩, ps₁⟩, hx, hrun⟩ := OracleWhnf.ok_of_bind hrun
    rw [runPure_bind] at hx
    obtain ⟨⟨⟨ta, st₂⟩, ps₂⟩, ha, hx⟩ := OracleWhnf.ok_of_bind hx
    cases hx
    obtain ⟨hoa, hma, hna, hra, a', hta, A, hA⟩ := hargs a (.head _)
    have ⟨hera, hdepsa, hgra⟩ := ih a hctx hsc hoa hma hna hra hok hta ⟨A, hA⟩ ha
    have hnsp : ¬ SpecialSpine (evalEnvOf view cfg decls) f₀ := by
      rintro ⟨c, us, hc, hsp⟩
      obtain ⟨hct, hcs, hq, hrc⟩ := hns c us hc
      rcases hsp with ⟨cv, hcv⟩ | hcs' | ⟨qv, hqv, hsq⟩ | ⟨rv, hrv⟩
      · exact hct cv hcv
      · rw [hcs] at hcs'; cases hcs'
      · rw [hq qv hqv] at hsq; cases hsq
      · exact hrc rv hrv
    have ⟨her, hdeps, hgr⟩ := ihl (f₀ := .app f₀ a) (tf := .app tf ta) (hctx.mono hgra.next)
      (fun b hb => hargs b (.tail _ hb)) (fun c us h => hns c us h) hgra.inv
      (.app hnsp hf hera) (.app (ErasesDeps.ext hgra.ext hdf) hdepsa) hrun
    refine ⟨?_, hdeps, hgra.trans hgr⟩
    rw [mkAppN_toArray] at her ⊢
    exact her

/-- `visitConst` at the pure backend, given `MutualSpec` at the fuels up to `j`, on a constant of
the scope that is neither a theorem nor a recognized `casesOn` constant: a successful run returns
the `tConst` of its kername, whose λ□ dependencies are erased, and it `Grows` within the scope.
Reference: the `tConst` case of `erases_erase` (`MR E/ErasureFunction.v:1228`), and
`erase_global_erases_deps` (`MR E/ErasureFunctionProperties.v:172`). -/
theorem visitConst_spec {j : Nat} (ihM : ∀ m ≤ j, ∀ c, MutualSpec E B view cfg decls m c)
    {lps : List Name} {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    {S : Name → Prop} {st st' : ErasureState} {tc : TravCtx} {ps ps' : PureState} {r : LBTerm}
    {c : Name} {us : List Level}
    (hctx : CtxOK E B lps Γ Δ cfg tc ps) (hsc : ScopeOK decls S) (hS : S c)
    (hnt : ∀ v, findDecl decls c ≠ some (.thmInfo v)) (hcs : casesInfo? decls c = none)
    (hem : ∃ ci, findDecl decls c = some ci ∧
      (EmitsConst ci = true ∨ ∃ q, ci = .quotInfo q ∧ q.kind = .ind))
    (hok : StateOK E B (evalEnvOf view cfg decls) st)
    (hrun : (visitConst (m := PureM) j (.const c us)).runPure st tc ⟨decls, view⟩ ps =
      .ok ((r, st'), ps')) :
    r = .const (toKername c) ∧ ErasesDeps E B (evalEnvOf view cfg decls) st'.gdecls r ∧
      Grows E B (evalEnvOf view cfg decls) S st st' ps ps' := by
  cases j with
  | zero => rw [visitConst] at hrun; cases hrun
  | succ i =>
  rw [visitConst] at hrun
  rw [runPure_read_bind, hctx.fixvars] at hrun
  dsimp only [Option.bind] at hrun
  rw [runPure_bind] at hrun
  obtain ⟨⟨⟨kn, st₁⟩, ps₁⟩, hk, hrun⟩ := OracleWhnf.ok_of_bind hrun
  cases hrun
  cases i with
  | zero => rw [get_constant_kername] at hk; cases hk
  | succ h =>
  obtain ⟨hcase, huniq⟩ := get_constant_kername_ok hk
  rcases hcase with ⟨hreg, rfl, rfl⟩ | ⟨hnew, hmut⟩
  · obtain ⟨rfl, hdeps⟩ := hok.kername hreg
    exact ⟨rfl, hdeps, .refl hok⟩
  · obtain ⟨hgr, kn', hkn'⟩ :=
      ihM h (by omega) c hsc hS hctx.config hctx.fixvars hnt hcs hem hok hnew hmut
    cases huniq kn' hkn'
    obtain ⟨rfl, hdeps⟩ := hgr.inv.kername hkn'
    exact ⟨rfl, hdeps, hgr⟩

/-- `visitApp (k + 1)` at the pure backend, on a spine the oracle does not erase whose head is
neither a constructor nor a recognized `casesOn` constant (`hplain`), from `visitExpr` and
`visitMutual` at the fuels up to `k` (`ih`): a spine headed by a constant is erased head first by
`visitConst` (the head is no atom, else the oracle would have answered `true`,
`Pure.isErasable_atom`, and no theorem, `isErasable_thm`), another spine by erasing its head with
`visitExpr`; then the arguments. Reference: the `tApp` and `tConst` cases of `erases_erase`
(`MR E/ErasureFunction.v:1228`). -/
theorem visitApp_spec (hG : CoreEnv E B P decls view cfg) {k : Nat}
    (ih : StepIH E B view cfg decls k)
    {lps : List Name} {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    {S : Name → Prop} {t : Metalean.Expr ζ lps.length n} {st st' : ErasureState} {tc : TravCtx}
    {ps ps' : PureState} {r : LBTerm} {e : Expr}
    (hctx : CtxOK E B lps Γ Δ cfg tc ps) (hsc : ScopeOK decls S)
    (hocc : ∀ d, nameOccurs d e = true → S d) (hmf : MachineFree cfg e) (hnp : NatPlain cfg e)
    (hrf : RecShaped cfg decls e) (hok : StateOK E B (evalEnvOf view cfg decls) st)
    (he : TrM E B lps Γ Δ e t) (ht : ∃ T, E[Γ] ⊢ t : T)
    (hor : Pure.isErasable ⟨decls⟩ oracleFuel tc.locals e = .ok false)
    (hplain : ∀ c us, e.getAppFn = .const c us →
      casesInfo? decls c = none ∧ ctorArity? decls c = none ∧
        (∀ qv, findDecl decls c = some (.quotInfo qv) → quotEvalArity qv.kind = none) ∧
        ∀ rv, findDecl decls c ≠ some (.recInfo rv))
    (hrun : (visitApp (m := PureM) (k + 1) e).runPure st tc ⟨decls, view⟩ ps =
      .ok ((r, st'), ps')) :
    Erases E B lps (evalEnvOf view cfg decls) Γ Δ e r ∧
      ErasesDeps E B (evalEnvOf view cfg decls) st'.gdecls r ∧
      Grows E B (evalEnvOf view cfg decls) S st st' ps ps' := by
  have hA : (e.withApp fun _ as => as) = (spineArgs e).toArray := by
    rw [← withApp_toList e, Array.toArray_toList]
  have hsp : mkAppN e.getAppFn (spineArgs e).toArray = e := mkAppN_spine e
  have hQ : ∀ {Q : Expr → Prop}, (∀ f a, Q (.app f a) → Q f ∧ Q a) → Q e →
      Q e.getAppFn ∧ ∀ a ∈ spineArgs e, Q a := fun hQ' h =>
    foldl_pred hQ' (by rw [← mkAppN_toArray, hsp]; exact h)
  obtain ⟨hoccF, hoccA⟩ := hQ (Q := fun x => ∀ d, nameOccurs d x = true → S d)
    (fun f a h => ⟨fun d hd => h d (by simp [nameOccurs, hd]),
      fun d hd => h d (by simp [nameOccurs, hd])⟩) hocc
  obtain ⟨hmfF, hmfA⟩ := hQ (Q := MachineFree cfg) (fun _ _ h => h) hmf
  obtain ⟨hnpF, hnpA⟩ := hQ (Q := NatPlain cfg) (fun _ _ h => h) hnp
  obtain ⟨hrfF, hrfA⟩ := hQ (Q := RecShaped cfg decls) (fun _ _ h => h) hrf
  rw [visitApp] at hrun
  split at hrun
  · rename_i c us hc
    obtain ⟨hcs, hca, hcq, hcr⟩ := hplain c us hc
    have hS : S c := hoccF c (by rw [hc]; simp [nameOccurs])
    obtain ⟨ci, hci, -⟩ := hsc c hS
    have hnt : ∀ v, findDecl decls c ≠ some (.thmInfo v) := fun v hv => by
      rw [isErasable_thm hc hv] at hor; cases hor
    have hncs : (evalEnvOf view cfg decls).casesOn? c = none := by
      simp [EvalEnv.casesOn?, evalEnvOf, hcs]
    have hnctor : ∀ cv, findDecl decls c ≠ some (.ctorInfo cv) := fun cv hcv => by
      have : ctorArity? decls c = some (cv.numParams + cv.numFields) := by
        unfold ctorArity?
        rw [show findConst decls c = findDecl decls c from rfl, hcv]
      rw [hca] at this; cases this
    have hat : (evalEnvOf view cfg decls).isAtom c = false := by
      cases ha : (evalEnvOf view cfg decls).isAtom c with
      | false => rfl
      | true =>
        cases Pure.isErasable_atom (σ := evalEnvOf view cfg decls) rfl
          (AtomSpine.of_getAppFn ha hc) hor
    have hspec : specialArity (evalEnvOf view cfg decls) c = none := by
      cases ci with
      | ctorInfo cv => exact absurd hci (hnctor cv)
      | quotInfo qv => simp [specialArity, evalEnvOf, hci, hcq qv hci]
      | recInfo rv => exact absurd hci (hcr rv)
      | _ => simp [specialArity, evalEnvOf, hci, EvalEnv.casesOn?, hcs]
    have hciP := SrcDefeq.findDecl_sub (σ := evalEnvOf view cfg decls) hG.sub hci
    have hem : EmitsConst ci = true ∨ ∃ q, ci = .quotInfo q ∧ q.kind = .ind := by
      cases ci with
      | inductInfo iv =>
        have har := hG.arity iv ⟨_, (findDecl_eq_some hci).1, rfl⟩
        have hiv : (arityShape (ConstantInfo.inductInfo iv).type).isSome = true := har
        have : (evalEnvOf view cfg decls).isAtom c = true := by
          simp [EvalEnv.isAtom, evalEnvOf, hci, EvalEnv.unfold?, OwnRules, EvalEnv.casesOn?, hcs,
            hiv]
        rw [hat] at this; cases this
      | ctorInfo cv => exact absurd hci (hnctor cv)
      | recInfo rv => exact absurd hci (hcr rv)
      | quotInfo qv =>
        -- `Quot` spines are types, which the oracle erases; `Quot.mk` and `Quot.lift` are special
        refine .inr ⟨qv, rfl, ?_⟩
        rcases ProgEnv.quot_shape hG.prog hciP with
          ⟨-, hk, u, hu⟩ | ⟨-, hk, -⟩ | ⟨-, hk, -⟩ | ⟨-, hk⟩
        · cases OracleAtom.isErasable_arity (ci := .quotInfo qv) (OracleAtom.ConstSpine.of_getAppFn hc)
            (show findConst decls c = _ from hci) rfl hu hor
        · have := hcq qv hci; rw [hk] at this; cases this
        · have := hcq qv hci; rw [hk] at this; cases this
        · exact hk
      | _ => exact .inl rfl
    have htrA : ∀ a ∈ spineArgs e, ∃ a', TrM E B lps Γ Δ a a' ∧ ∃ A, E[Γ] ⊢ a' : A := by
      rcases hem with hem | ⟨qv, rfl, -⟩
      · have hnsh : ¬ SpecialHead B e.getAppFn := by
          rintro ⟨c', us', b, hc', hb, hs⟩
          rw [hc] at hc'
          cases hc'
          rcases SrcDefeq.special_kind hG.prog hb hs hciP with
            ⟨iv, rfl⟩ | ⟨cv, rfl⟩ | ⟨rv, rfl⟩ | ⟨qv, rfl⟩ <;> cases hem
        exact (spine_typed hnsh (by rw [hsp]; exact he) ht).2
      · obtain ⟨η, hB⟩ := hG.prog.lookup_quot hciP
        rw [hc] at hsp
        exact TrM.quot_args_typed hB (by rw [hsp]; exact he) ht
    cases k with
    | zero => rw [visitConstApp] at hrun; cases hrun
    | succ j =>
    rw [visitConstApp, withApp_eq] at hrun
    split at hrun
    · rename_i c' us' hc'
      rw [hc] at hc'
      cases hc'
      rw [runPure_bind, show (liftM (Backend.casesInfo? (m := PureM) c) :
          EraseT PureM (Option CasesInfo)).runPure st tc ⟨decls, view⟩ ps = .ok ((none, st), ps) by
        show Except.ok ((casesInfo? decls c, st), ps) = _; rw [hcs], ok_bind'] at hrun
      dsimp only at hrun
      rw [runPure_bind, show (liftM (Backend.ctorArity? (m := PureM) c) :
          EraseT PureM (Option Nat)).runPure st tc ⟨decls, view⟩ ps = .ok ((none, st), ps) by
        show Except.ok ((ctorArity? decls c, st), ps) = _; rw [hca], ok_bind'] at hrun
      dsimp only at hrun
      rw [runPure_bind, show (liftM (Backend.findConst? (m := PureM) c) :
          EraseT PureM (Option ConstantInfo)).runPure st tc ⟨decls, view⟩ ps = .ok ((some ci, st), ps) by
        show Except.ok ((findConst decls c, st), ps) = _
        rw [show findConst decls c = findDecl decls c from rfl, hci], ok_bind'] at hrun
      dsimp only at hrun
      split at hrun
      · rename_i q _ _ _ heq
        cases Option.some.inj heq
        cases hcq _ hci
      · rename_i q _ _ _ heq
        cases Option.some.inj heq
        cases hcq _ hci
      · rename_i rv heq
        cases Option.some.inj heq
        exact absurd hci (hcr rv)
      rw [runPure_bind] at hrun
      obtain ⟨⟨⟨tf, st₁⟩, ps₁⟩, hf, hrun⟩ := OracleWhnf.ok_of_bind hrun
      rw [hc] at hf
      obtain ⟨rfl, hdf, hgf⟩ := visitConst_spec (fun m hm c => ih.mutDecl m (by omega) c)
        hctx hsc hS hnt hcs ⟨ci, hci, hem⟩ hok hf
      cases j with
      | zero => rw [visitAppArgs] at hrun; cases hrun
      | succ i =>
      rw [hA] at hrun
      have ⟨her, hdeps, hgr⟩ := visitAppArgs_spec (fun e => ih.expr i (by omega) e)
        (hctx.mono hgf.next) hsc (fun a ha => ⟨hoccA a ha, hmfA a ha, hnpA a ha, hrfA a ha, htrA a ha⟩)
        (fun c'' us'' h => by
          cases h
          exact ⟨hnctor, hncs, hcq, fun rv hrv => hcr rv hrv⟩) hgf.inv
        (.const (us := us) hat hspec fun rv hrv => hcr rv hrv) hdf hrun
      rw [hc] at hsp
      rw [hsp] at her
      exact ⟨her, hdeps, hgf.trans hgr⟩
    · rename_i hne
      exact absurd hc (hne c us)
  · rename_i hnc
    rw [withApp_eq, runPure_bind] at hrun
    obtain ⟨⟨⟨tf, st₁⟩, ps₁⟩, hf, hrun⟩ := OracleWhnf.ok_of_bind hrun
    have hnsh : ¬ SpecialHead B e.getAppFn := fun ⟨c, us, b, hc, _, _⟩ =>
      hnc c us (by rwa [getAppFn_getAppFn] at hc)
    obtain ⟨⟨f', htf, F, hF⟩, htrA⟩ := spine_typed hnsh (by rw [hsp]; exact he) ht
    have ⟨herf, hdf, hgf⟩ := ih.expr k (Nat.le_refl _) _ hctx hsc hoccF hmfF hnpF hrfF hok htf ⟨F, hF⟩ hf
    cases k with
    | zero => rw [visitAppArgs] at hrun; cases hrun
    | succ i =>
    rw [hA] at hrun
    have ⟨her, hdeps, hgr⟩ := visitAppArgs_spec (fun e => ih.expr i (by omega) e)
      (hctx.mono hgf.next) hsc (fun a ha => ⟨hoccA a ha, hmfA a ha, hnpA a ha, hrfA a ha, htrA a ha⟩)
      (fun c us h => absurd (by rwa [getAppFn_getAppFn] at h) (hnc c us)) hgf.inv herf hdf hrun
    rw [hsp] at her
    exact ⟨her, hdeps, hgf.trans hgr⟩

/-- The `app` step, through `visitApp_spec`, on a spine whose head is neither a constructor nor a
recognized `casesOn` constant. Reference: the `tApp` case of `erases_erase`
(`MR E/ErasureFunction.v:1228`), rule `erases_tApp` (`MR E/Extract.v:101`). -/
theorem visitExpr_app_step (hG : CoreEnv E B P decls view cfg) {fuel : Nat}
    (ih : StepIH E B view cfg decls fuel) {f a : Expr}
    (hplain : ∀ c us, (Expr.app f a).getAppFn = .const c us →
      casesInfo? decls c = none ∧ ctorArity? decls c = none ∧
        (∀ qv, findDecl decls c = some (.quotInfo qv) → quotEvalArity qv.kind = none) ∧
        ∀ rv, findDecl decls c ≠ some (.recInfo rv)) :
    ExprSpec E B view cfg decls (fuel + 1) (.app f a) := by
  intro lps n Γ Δ S t st tc ps r st' ps' hctx hsc hocc hmf hnp hrf hok he ht hrun
  rw [visitExpr] at hrun
  rcases oracle_run hrun with ⟨hor, rfl, rfl, rfl⟩ | ⟨hor, hrun⟩
  · exact visitExpr_box hG hctx hok he ht hor
  cases fuel with
  | zero => rw [visitApp] at hrun; cases hrun
  | succ k =>
  exact visitApp_spec hG ⟨fun m hm => ih.expr m (by omega), fun m hm => ih.mutDecl m (by omega)⟩
    hctx hsc hocc hmf hnp hrf hok he ht hor hplain hrun

/-- The `const` step: a constant that is neither a constructor nor a recognized `casesOn` constant
is erased as an application to no argument (`visitApp_spec`). Reference: the `tConst` case of
`erases_erase` (`MR E/ErasureFunction.v:1228`), rule `erases_tConst` (`MR E/Extract.v:104`). -/
theorem visitExpr_const_step (hG : CoreEnv E B P decls view cfg) {fuel : Nat}
    (ih : StepIH E B view cfg decls fuel) {c : Name} {us : List Level}
    (hplain : casesInfo? decls c = none ∧ ctorArity? decls c = none ∧
      (∀ qv, findDecl decls c = some (.quotInfo qv) → quotEvalArity qv.kind = none) ∧
      ∀ rv, findDecl decls c ≠ some (.recInfo rv)) :
    ExprSpec E B view cfg decls (fuel + 1) (.const c us) := by
  intro lps n Γ Δ S t st tc ps r st' ps' hctx hsc hocc hmf hnp hrf hok he ht hrun
  rw [visitExpr] at hrun
  rcases oracle_run hrun with ⟨hor, rfl, rfl, rfl⟩ | ⟨hor, hrun⟩
  · exact visitExpr_box hG hctx hok he ht hor
  cases fuel with
  | zero => rw [visitApp] at hrun; cases hrun
  | succ k =>
  exact visitApp_spec hG ⟨fun m hm => ih.expr m (by omega), fun m hm => ih.mutDecl m (by omega)⟩
    hctx hsc hocc hmf hnp hrf hok he ht hor (fun c' us' h => by cases h; exact hplain) hrun

end

/-! ## Scopes from the order of the program -/

/-- A constant that occurs in `e` (for the traversal) satisfies what every constant of `e`
satisfies. -/
theorem ConstsIn.nameOccurs {p : Name → Prop} {d : Name} :
    ∀ {e : Expr}, ConstsIn p e → Erasure.nameOccurs d e = true → p d
  | .const c _, h, ho => by
    simp only [Erasure.nameOccurs, beq_iff_eq] at ho
    subst ho; exact h
  | .app f a, h, ho => by
    simp only [Erasure.nameOccurs, Bool.or_eq_true] at ho
    exact ho.elim (ConstsIn.nameOccurs h.1) (ConstsIn.nameOccurs h.2)
  | .letE _ _ f a _, h, ho => by
    simp only [Erasure.nameOccurs, Bool.or_eq_true] at ho
    exact ho.elim (ConstsIn.nameOccurs h.2.1) (ConstsIn.nameOccurs h.2.2)
  | .lam _ _ b _, h, ho => ConstsIn.nameOccurs (e := b) h.2 ho
  | .mdata _ b, h, ho => ConstsIn.nameOccurs (e := b) h ho
  | .proj _ _ b, h, ho => ConstsIn.nameOccurs (e := b) h.2 ho
  | .bvar _, _, ho | .fvar _, _, ho | .mvar _, _, ho | .sort _, _, ho | .forallE .., _, ho
  | .lit _, _, ho => by simp [Erasure.nameOccurs] at ho

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P decls : List ConstantInfo}
  {view : EnvView} {cfg : ErasureConfig}

/-- The value of a declaration of a program that is not a theorem mentions only declarations
after it: a value is translated in the table of the earlier declarations. Reference:
`on_global_decls` (`MR common/theories/EnvironmentTyping.v:1743`), each declaration typed in the
environment before it. -/
theorem ProgEnv.value_suffix (h : ProgEnv P ζ E B) {ci : ConstantInfo} {v : Expr}
    (hv : ci.value? (allowOpaque := true) = some v) (hthm : IsThm ci = false) :
    ∀ pre post, P = pre ++ ci :: post → ConstsIn (· ∈ post.map (·.name)) v := by
  induction h with
  | nil => intro pre post h; simp at h
  | «axiom» _ _ _ _ _ ih =>
    intro pre post heq
    cases pre with
    | nil => simp only [List.nil_append, List.cons.injEq] at heq; obtain ⟨rfl, -⟩ := heq; cases hv
    | cons y pre' => simp only [List.cons_append, List.cons.injEq] at heq; exact ih pre' post heq.2
  | defn hP _ _ _ _ _ hval ih =>
    intro pre post heq
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      cases hv
      exact NonRec.ConstsIn_mono (fun c hc => hP.bound hc) (NonRec.TrM.consts hval)
    | cons y pre' => simp only [List.cons_append, List.cons.injEq] at heq; exact ih pre' post heq.2
  | thm _ _ _ _ _ _ _ ih =>
    intro pre post heq
    cases pre with
    | nil => simp only [List.nil_append, List.cons.injEq] at heq; obtain ⟨rfl, -⟩ := heq; cases hthm
    | cons y pre' => simp only [List.cons_append, List.cons.injEq] at heq; exact ih pre' post heq.2
  | «opaque» hP _ _ _ _ _ hval _ ih =>
    intro pre post heq
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      cases hv
      exact NonRec.ConstsIn_mono (fun c hc => hP.bound hc) (NonRec.TrM.consts hval)
    | cons y pre' => simp only [List.cons_append, List.cons.injEq] at heq; exact ih pre' post heq.2
  | induct _ _ _ _ _ _ _ ih =>
    intro pre post heq
    rcases List.append_eq_append_iff.1 heq with ⟨a', rfl, hP'⟩ | ⟨c', hblk, hrest⟩
    · exact ih a' post hP'
    · cases c' with
      | nil => exact ih [] post (by simpa using hrest.symm)
      | cons z c'' =>
        simp only [List.cons_append, List.cons.injEq] at hrest
        obtain ⟨rfl, -⟩ := hrest
        have hm : ci ∈ pre ++ ci :: c'' := List.mem_append_right pre (List.mem_cons_self ..)
        rw [← hblk] at hm
        rcases IndBlock.mem_decls hm with ⟨s, hs⟩ | ⟨s, k, hs⟩ | ⟨s, hs⟩ <;> rw [hs] at hv <;>
          cases hv
  | quot _ _ _ _ _ _ _ ih =>
    intro pre post heq
    rcases List.append_eq_append_iff.1 heq with ⟨a', rfl, hP'⟩ | ⟨c', hblk, hrest⟩
    · exact ih a' post hP'
    · cases c' with
      | nil => exact ih [] post (by simpa using hrest.symm)
      | cons z c'' =>
        simp only [List.cons_append, List.cons.injEq] at hrest
        obtain ⟨rfl, -⟩ := hrest
        have hm : ci ∈ pre ++ ci :: c'' := List.mem_append_right pre (List.mem_cons_self ..)
        rw [← hblk] at hm
        obtain ⟨q, -, rfl⟩ := List.mem_map.1 hm
        cases hv

/-- A value that `visitMutual` erases (of a declaration of `decls` that is neither a theorem nor a
recognized `casesOn` constant) mentions only constants of `decls`. -/
theorem CoreEnv.value_consts (hG : CoreEnv E B P decls view cfg) {d : Name} {cd : ConstantInfo}
    {w : Expr} (hcd : findDecl decls d = some cd) (hw : cd.value? (allowOpaque := true) = some w)
    (hthm : IsThm cd = false) (hcs : casesInfo? decls d = none) :
    ConstsIn (fun x => (findDecl decls x).isSome) w ∧ ReadExpr decls cd w := by
  obtain ⟨hm, hn⟩ := findDecl_eq_some hcd
  have hr : ReadExpr decls cd w := by
    cases cd with
    | defnInfo dv =>
      cases hw
      refine .inr (.inl ⟨dv, rfl, rfl, ?_⟩)
      have hn' : dv.name = d := hn
      simp [EvalEnv.casesOn?, hn', hcs]
    | opaqueInfo o => cases hw; exact .inr (.inr ⟨o, rfl, rfl⟩)
    | thmInfo _ => cases hthm
    | _ => cases hw
  exact ⟨(hG.deps _ hm).1 w hr, hr⟩

/-- The value of a declaration of `decls` that `visitMutual` erases has a scope that does not hold
the declaration: its constants are declarations of `decls` after it in the program. This is what
keeps the traversal from registering a constant while it erases the constant's own value.
Reference: `erase_global_deps_fresh` (`MR E/ErasureFunctionProperties.v:1206`), where the
declarations are erased in the order of the environment. -/
theorem CoreEnv.valueScope (hG : CoreEnv E B P decls view cfg) {c : Name} {ci : ConstantInfo}
    (hci : findDecl decls c = some ci) {v : Expr} (hv : ci.value? (allowOpaque := true) = some v)
    (hthm : IsThm ci = false) (hcs : casesInfo? decls c = none) :
    ∃ S', ScopeOK decls S' ∧ (∀ d, nameOccurs d v = true → S' d) ∧ ¬ S' c := by
  obtain ⟨hm, hn⟩ := findDecl_eq_some (SrcDefeq.findDecl_sub (σ := evalEnvOf view cfg decls) hG.sub hci)
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hm
  have hnd := ProgEnv.fresh hG.prog
  refine ⟨fun d => (findDecl decls d).isSome ∧ d ∈ post.map (·.name), ?_, fun d hd => ?_, ?_⟩
  · rintro d ⟨hds, hdp⟩
    obtain ⟨cd, hcd⟩ := Option.isSome_iff_exists.1 hds
    refine ⟨cd, hcd, fun w hw hthm' hcs' d' hd' =>
      ⟨ConstsIn.nameOccurs (hG.value_consts hcd hw hthm' hcs').1 hd', ?_⟩⟩
    obtain ⟨cd', hcd', hn'⟩ := List.mem_map.1 hdp
    obtain ⟨hmP, hnP⟩ := findDecl_eq_some (SrcDefeq.findDecl_sub (σ := evalEnvOf view cfg decls) hG.sub hcd)
    have heq : cd' = cd := List.inj_on_of_nodup_map hnd
      (by rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hcd')) hmP
      (hn'.trans hnP.symm)
    subst heq
    obtain ⟨post₁, post₂, hpost⟩ := List.append_of_mem hcd'
    have := ProgEnv.value_suffix hG.prog hw hthm' (pre ++ ci :: post₁) post₂
      (by rw [hsplit, hpost]; simp)
    have h2 := ConstsIn.nameOccurs this hd'
    rw [hpost]
    simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons]
    exact .inr (.inr h2)
  · exact ⟨ConstsIn.nameOccurs (hG.value_consts hci hv hthm hcs).1 hd,
      ConstsIn.nameOccurs (ProgEnv.value_suffix hG.prog hv hthm pre post hsplit) hd⟩
  · rintro ⟨-, hcp⟩
    rw [hsplit, List.map_append, List.map_cons] at hnd
    have := (List.nodup_append.1 hnd).2.1
    rw [List.nodup_cons] at this
    exact this.1 (hn ▸ hcp)

end

/-! ## `visitMutual` -/

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P decls : List ConstantInfo}
  {view : EnvView} {cfg : ErasureConfig}

/-- A value that `visitMutual` erases (of a definition or an opaque of the program) translates to
a typed Metalean term in the empty context. Reference: `on_global_env` typing of a declaration's
body (MC §3.6). -/
theorem ProgEnv.value_typed (h : ProgEnv P ζ E B) (hE : EnvWF E) {ci : ConstantInfo}
    (hci : ci ∈ P) {v : Expr} (hv : ci.value? (allowOpaque := true) = some v)
    (hthm : IsThm ci = false) :
    ∃ e T : Metalean.Expr ζ ci.levelParams.length 0,
      TrM E B ci.levelParams .nil [] v e ∧ E[.nil] ⊢ e : T := by
  induction h with
  | nil => cases hci
  | @«axiom» _ _ _ _ v' _ hP hfr _ _ _ ih =>
    have hE' := hE; cases hE'
    rcases List.mem_cons.1 hci with rfl | hci
    · cases hv
    · obtain ⟨e, T, htr, hty⟩ := ih ‹_› hci
      exact ⟨_, _, TrM.wkEnv (hP.set_ext hfr _) htr, Metalean.Defeq.map (envS _ _) hty⟩
  | @defn _ _ _ _ v' _ e hP hfr _ _ _ _ hval ih =>
    have hE' := hE
    cases hE' with
    | snoc hEp hent =>
    rcases List.mem_cons.1 hci with rfl | hci
    · cases hv
      cases hent with
      | «def» _ hty =>
        exact ⟨_, _, TrM.wkEnv (hP.set_ext hfr _) hval, Metalean.Defeq.map (envS _ _) hty⟩
    · obtain ⟨e, T, htr, hty⟩ := ih hEp hci
      exact ⟨_, _, TrM.wkEnv (hP.set_ext hfr _) htr, Metalean.Defeq.map (envS _ _) hty⟩
  | @thm _ _ _ _ v' _ hP hfr _ _ _ _ _ ih =>
    have hE' := hE; cases hE'
    rcases List.mem_cons.1 hci with rfl | hci
    · cases hthm
    · obtain ⟨e, T, htr, hty⟩ := ih ‹_› hci
      exact ⟨_, _, TrM.wkEnv (hP.set_ext hfr _) htr, Metalean.Defeq.map (envS _ _) hty⟩
  | @«opaque» _ _ _ _ v' _ _ hP hfr _ _ _ _ hval hty0 ih =>
    have hE' := hE; cases hE'
    rcases List.mem_cons.1 hci with rfl | hci
    · cases hv
      exact ⟨_, _, TrM.wkEnv (hP.set_ext hfr _) hval, Metalean.Defeq.map (envS _ _) hty0⟩
    · obtain ⟨e, T, htr, hty⟩ := ih ‹_› hci
      exact ⟨_, _, TrM.wkEnv (hP.set_ext hfr _) htr, Metalean.Defeq.map (envS _ _) hty⟩
  | @induct _ _ _ _ ι _ _ _ Is Cs Rs _ hP _ hfr _ hext _ _ ih =>
    have hE' := hE; cases hE'
    rcases List.mem_append.1 hci with hm | hci
    · rcases IndBlock.mem_decls hm with ⟨s, hs⟩ | ⟨s, k, hs⟩ | ⟨s, hs⟩ <;> rw [hs] at hv <;>
        cases hv
    · obtain ⟨e, T, htr, hty⟩ := ih ‹_› hci
      exact ⟨_, _, TrM.wkEnv (hP.ext_ext hfr hext) htr, Metalean.Defeq.map (envS _ _) hty⟩
  | @quot _ _ _ _ _ qs _ hP _ _ hfr _ hext _ ih =>
    have hE' := hE; cases hE'
    rcases List.mem_append.1 hci with hm | hci
    · obtain ⟨q, -, rfl⟩ := List.mem_map.1 hm
      cases hv
    · obtain ⟨e, T, htr, hty⟩ := ih ‹_› hci
      exact ⟨_, _, TrM.wkEnv (hP.ext_ext (decls := qs.map .quotInfo)
        (fun ci hci => by obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hci; exact hfr q hq)
        (by rw [List.map_map]; exact hext)) htr, Metalean.Defeq.map (envS _ _) hty⟩

end

/-- At the pure backend, the traversal's `name_occurs` is `nameOccurs` (no `_unsafe_rec`
stripping). -/
theorem name_occurs_eq : name_occurs (m := PureM) = nameOccurs := by
  funext n e
  induction e <;> simp [name_occurs, nameOccurs, remove_unsafe_rec, *]
  rfl

/-- A run of `x` at the pure backend that keeps the registered constants and inductive types, the
λ□ environment and the counter: the inlining bookkeeping of `visitMutual`. -/
def KeepsCG (pc : PureCtx) {α : Type} (x : EraseT PureM α) : Prop :=
  ∀ st tc ps r st' ps', x.runPure st tc pc ps = .ok ((r, st'), ps') →
    st'.constants = st.constants ∧ st'.inductives = st.inductives ∧ st'.gdecls = st.gdecls ∧
      ps' = ps

section
open TravFrame
variable {pc : PureCtx}

theorem KeepsCG.pure {α : Type} (a : α) : KeepsCG pc (Pure.pure a : EraseT PureM α) := by
  intro st tc ps r st' ps' h; cases h; exact ⟨rfl, rfl, rfl, rfl⟩

theorem KeepsCG.get : KeepsCG pc (MonadState.get : EraseT PureM ErasureState) := by
  intro st tc ps r st' ps' h; cases h; exact ⟨rfl, rfl, rfl, rfl⟩

theorem KeepsCG.modify {f : ErasureState → ErasureState}
    (hf : ∀ s, (f s).constants = s.constants ∧ (f s).inductives = s.inductives ∧
      (f s).gdecls = s.gdecls) :
    KeepsCG pc (_root_.modify f : EraseT PureM PUnit) := by
  intro st tc ps r st' ps' h; cases h; exact ⟨(hf st).1, (hf st).2.1, (hf st).2.2, rfl⟩

theorem KeepsCG.log (m : String) :
    KeepsCG pc (liftM (Backend.log (m := PureM) m) : EraseT PureM Unit) := by
  intro st tc ps r st' ps' h; cases h; exact ⟨rfl, rfl, rfl, rfl⟩

theorem KeepsCG.isInstance (n : Name) :
    KeepsCG pc (liftM (Backend.isInstance (m := PureM) n) : EraseT PureM Bool) := by
  intro st tc ps r st' ps' h; cases h; exact ⟨rfl, rfl, rfl, rfl⟩

theorem KeepsCG.bind {α β : Type} {x : EraseT PureM α} {k : α → EraseT PureM β}
    (hx : KeepsCG pc x) (hk : ∀ a, KeepsCG pc (k a)) : KeepsCG pc (x >>= k) := by
  intro st tc ps r st' ps' h
  rw [runPure_bind] at h
  obtain ⟨⟨⟨a, st₁⟩, ps₁⟩, h1, h2⟩ := OracleWhnf.ok_of_bind h
  obtain ⟨c1, i1, g1, p1⟩ := hx _ _ _ _ _ _ h1
  obtain ⟨c2, i2, g2, p2⟩ := hk a _ _ _ _ _ _ h2
  exact ⟨c2.trans c1, i2.trans i1, g2.trans g1, p2.trans p1⟩

theorem KeepsCG.read_bind {α : Type} {k : TravCtx → EraseT PureM α}
    (hk : ∀ c, KeepsCG pc (k c)) : KeepsCG pc (read >>= k) := by
  intro st tc ps r st' ps' h
  rw [runPure_read_bind] at h
  exact hk tc _ _ _ _ _ _ h

theorem KeepsCG.ite {α : Type} {c : Prop} [Decidable c] {a b : EraseT PureM α}
    (ha : c → KeepsCG pc a) (hb : ¬c → KeepsCG pc b) : KeepsCG pc (if c then a else b) := by
  by_cases h : c
  · rw [if_pos h]; exact ha h
  · rw [if_neg h]; exact hb h

end

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {σ : EvalEnv}

/-- `StateOK` reads only the registered constants and inductive types and the λ□ environment. -/
theorem StateOK.congr {st st' : ErasureState} (h : StateOK E B σ st)
    (hc : st'.constants = st.constants) (hi : st'.inductives = st.inductives)
    (hg : st'.gdecls = st.gdecls) : StateOK E B σ st' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨by rw [hc, hg]; exact h1, by rw [hi, hg]; exact h2, by rw [hc, hi, hg]; exact h3,
    by rw [hi]; exact h4, by rw [hg]; exact h5⟩

end

section
open TravFrame
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P decls : List ConstantInfo}
  {view : EnvView} {cfg : ErasureConfig}

/-- `Quot.ind`'s kername is no λ□ block name: it is not a root kername. -/
theorem quot_knNotBlock {σ : EvalEnv} {c : Name} {q : QuotVal}
    (henv : ProgEnv P ζ E B) (hc : findDecl P c = some (.quotInfo q)) (hk : q.kind = .ind) :
    KnNotBlock σ c := by
  have hn : q.name = c := (findDecl_eq_some hc).2
  intro iv _ h
  rcases ProgEnv.quot_shape henv hc with ⟨-, hk', -⟩ | ⟨-, hk', -⟩ | ⟨-, hk', -⟩ | ⟨hq, -⟩
  all_goals try (rw [hk] at hk'; cases hk')
  rw [← hn, hq] at h
  have := congrArg Kername.mp h
  simp [toKername, toModPath, blockKername, mutualBlockKername, rootKername] at this

/-- The `visitMutual` step, from `visitExpr` at `fuel`: an axiom, or a remapped declaration, is
registered by `addAxiom` (`addAxiom_ok`); a definition's or an opaque's value, which is not
recursive (`isRecursiveDecl_false`), is erased in the empty context (it is closed, so as under the
caller's locals, `visit_agree`), and registered with its erasure (`StateOK.register`); the
traversal cannot register the constant while it erases the value, whose scope does not hold it
(`CoreEnv.valueScope`). The inlining bookkeeping keeps the state invariant (`KeepsCG`).
Reference: `erase_constant_body` (`MR E/ErasureFunction.v:1309`) in the `ConstantDecl` step of
`erase_global_deps` (`MR E/ErasureFunction.v:1602`); `erase_global_deps_fresh`
(`MR E/ErasureFunctionProperties.v:1206`). -/
theorem visitMutual_step (hG : CoreEnv E B P decls view cfg) {fuel : Nat}
    (ih : StepIH E B view cfg decls fuel) {c : Name} :
    MutualSpec E B view cfg decls (fuel + 1) c := by
  intro S st tc ps st' ps' hsc hS hcfg hfix hnt hcs hemc hok hnew hrun
  obtain ⟨ci, hci, hem⟩ := hemc
  have hciP := SrcDefeq.findDecl_sub (σ := evalEnvOf view cfg decls) hG.sub hci
  obtain ⟨hmP, hname⟩ := findDecl_eq_some hciP
  have hnb : KnNotBlock (evalEnvOf view cfg decls) c := by
    rcases hem with hem | ⟨q, rfl, hk⟩
    · exact knNotBlock_of_emits hG.bn hci hem
    · exact quot_knNotBlock hG.prog hciP hk
  have hci' : ci ∈ decls := (findDecl_eq_some hci).1
  have hthm : IsThm ci = false := by
    cases ci with
    | thmInfo v => exact absurd hci (hnt v)
    | _ => rfl
  have hall : ci.all.length = 1 := by
    cases hv : ci.value? (allowOpaque := true) with
    | some v => rw [(NonRec.ProgEnv.scoped hG.prog hmP hv).1]; rfl
    | none =>
      rcases hem with hem | ⟨q, rfl, -⟩
      · cases ci <;> simp_all [ConstantInfo.value?, EmitsConst, ConstantInfo.all]
      · rfl
  -- an axiom: `addAxiom` registers it
  have haxiom : ∀ {sd : ErasureState}, sd.constants = st.constants →
      sd.inductives = st.inductives → sd.gdecls = st.gdecls →
      (ci.value? (allowOpaque := true) = none ∨ axiomatized view cfg ci = true) →
      (addAxiom (m := PureM) c).runPure sd tc ⟨decls, view⟩ ps = .ok (((), st'), ps') →
      Grows E B (evalEnvOf view cfg decls) S st st' ps ps' ∧
        ∃ kn, st'.constants[c]? = some kn := by
    intro sd hcd hid hgd hax hrun
    obtain ⟨st'', hrun'', hc'', hok'', hext''⟩ :=
      addAxiom_ok (StateOK.congr hok hcd hid hgd) hG.inj hci hnb (by rw [hcd]; exact hnew) hax
    rw [hrun''] at hrun
    cases hrun
    refine ⟨⟨hok'', by rw [← hgd]; exact hext'', Nat.le_refl _, fun c' kn h0 h1 => ?_⟩,
      toKername c, by rw [hc'']; exact Std.HashMap.getElem?_insert_self⟩
    rw [hc'', Std.HashMap.getElem?_insert] at h1
    split at h1
    · rename_i hcc
      rw [← beq_iff_eq.1 hcc]
      exact hS
    · rw [hcd, h0] at h1
      cases h1
  rw [visitMutual, runPure_read_bind, runPure_bind, show (liftM (Backend.declInfo? (m := PureM) tc.config c) :
      EraseT PureM _).runPure st tc ⟨decls, view⟩ ps = .ok ((some ci, st), ps) by
    show Except.ok ((findConst decls c, st), ps) = _
    rw [show findConst decls c = findDecl decls c from rfl, hci], ok_bind'] at hrun
  dsimp only at hrun
  rw [runPure_bind, show (getOrFail (m := PureM) (some ci)
    (toString "visitMutual: unknown constant " ++ toString c)).runPure st tc ⟨decls, view⟩ ps =
      .ok ((ci, st), ps) from rfl, ok_bind'] at hrun
  dsimp only at hrun
  rw [runPure_bind, show (liftM (Backend.inlineAttr? (m := PureM) c) : EraseT PureM _).runPure st
    tc ⟨decls, view⟩ ps = .ok ((view.inlineAttr? c, st), ps) from rfl, ok_bind'] at hrun
  dsimp only at hrun
  rw [runPure_bind, show (liftM (Backend.inlineAttr? (m := PureM) c) : EraseT PureM _).runPure st
    tc ⟨decls, view⟩ ps = .ok ((view.inlineAttr? c, st), ps) from rfl, ok_bind'] at hrun
  dsimp only at hrun
  simp only [hall, beq_self_eq_true, Bool.true_and, ↓reduceIte] at hrun
  generalize view.inlineAttr? c = ia at hrun
  rcases ia with _ | ⟨_ | _ | _ | _ | _⟩ <;> simp only [↓reduceIte, Bool.false_eq_true] at hrun
  -- the `@[inline]` bookkeeping before the value touches only `inlinings`
  all_goals first
    | (rw [runPure_bind] at hrun
       replace hrun := OracleWhnf.ok_of_bind hrun
       obtain ⟨⟨⟨_, sa⟩, pa⟩, h1, hrun⟩ := hrun
       obtain ⟨ca, ia, ga, hpa⟩ := KeepsCG.log (pc := ⟨decls, view⟩) _ _ _ _ _ _ _ h1
       subst pa
       try dsimp only at hrun
       rw [runPure_bind] at hrun
       replace hrun := OracleWhnf.ok_of_bind hrun
       obtain ⟨⟨⟨_, sb⟩, pb⟩, h2, hrun⟩ := hrun
       obtain ⟨cb, ib, gb, hpb⟩ :=
         KeepsCG.modify (pc := ⟨decls, view⟩) (fun _ => ⟨rfl, rfl, rfl⟩) _ _ _ _ _ _ h2
       subst pb
       try dsimp only at hrun
       have hcb : sb.constants = st.constants := cb.trans ca
       have hib : sb.inductives = st.inductives := ib.trans ia
       have hgb : sb.gdecls = st.gdecls := gb.trans ga
       clear ca ia ga cb ib gb h1 h2)
    | (obtain ⟨sb, hsb⟩ : ∃ sb, sb = st := ⟨st, rfl⟩
       rw [← hsb] at hrun
       have hcb : sb.constants = st.constants := by rw [hsb]
       have hib : sb.inductives = st.inductives := by rw [hsb]
       have hgb : sb.gdecls = st.gdecls := by rw [hsb]
       clear hsb)
  all_goals
    rw [runPure_bind, show (liftM (Backend.isExtern (m := PureM) c) : EraseT PureM Bool).runPure sb
      tc ⟨decls, view⟩ ps = .ok ((view.isExtern c, sb), ps) from rfl, ok_bind'] at hrun
    dsimp only at hrun
    rw [runPure_read_bind, hcfg] at hrun
  all_goals
    rcases hv : ci.value? (allowOpaque := true) with _ | v <;> cases hie : view.isExtern c <;>
      cases hext : cfg.1 <;> simp only [hv, hie, hext] at hrun
  all_goals first
    | (rw [runPure_bind] at hrun
       replace hrun := OracleWhnf.ok_of_bind hrun
       obtain ⟨⟨⟨_, sd⟩, pd⟩, h1, hrun⟩ := hrun
       obtain ⟨cd, id, gd, hpd⟩ := KeepsCG.log (pc := ⟨decls, view⟩) _ _ _ _ _ _ _ h1
       subst pd
       try dsimp only at hrun
       exact haxiom (cd.trans hcb) (id.trans hib) (gd.trans hgb)
         (by first
           | exact .inl hv
           | exact .inr (by simp [axiomatized, hall, hname, hie, hext] <;> rfl)) hrun)
    | (rw [runPure_bind] at hrun
       replace hrun := OracleWhnf.ok_of_bind hrun
       obtain ⟨⟨⟨_, sb⟩, pd⟩, h1, hrun⟩ := hrun
       obtain ⟨cd, id, gd, hpd⟩ := KeepsCG.log (pc := ⟨decls, view⟩) _ _ _ _ _ _ _ h1
       subst pd
       try dsimp only at hrun
       replace hcb := cd.trans hcb
       replace hib := id.trans hib
       replace hgb := gd.trans hgb
       clear cd id gd h1)
    | skip
  -- a definition or an opaque: its value is erased in the empty context, then registered
  all_goals
    have hax : axiomatized view cfg ci = false := by
      simp [axiomatized, hall, hname, hie, hext] <;> rfl
    have hnr := isRecursiveDecl_false hG.prog hciP hv
    have hval : ci.value! (allowOpaque := true) = v := by cases ci <;> cases hv <;> rfl
    have hno : name_occurs (m := PureM) c v = false := by
      rw [name_occurs_eq]
      unfold isRecursiveDecl at hnr
      simp only [Bool.or_eq_false_iff, hall, hval, hname] at hnr
      exact hnr.2
    simp only [Option.getD_some, hno, Bool.not_false, ↓reduceIte] at hrun
    rw [runPure_bind] at hrun
    obtain ⟨⟨⟨e0, s0⟩, p0⟩, hg0, hrun⟩ := OracleWhnf.ok_of_bind hrun
    cases hg0
    rw [runPure_bind] at hrun
    obtain ⟨⟨⟨t, st₂⟩, ps₂⟩, hW, hrun⟩ := OracleWhnf.ok_of_bind hrun
    rw [runPure_withReader, runPure_read_bind, runPure_bind] at hW
    obtain ⟨⟨⟨v₁, s₁⟩, p₁⟩, hp, hW⟩ := OracleWhnf.ok_of_bind hW
    cases hp
    rw [runPure_bind] at hrun
    obtain ⟨⟨⟨_, st₃⟩, ps₃⟩, hm, hrun⟩ := OracleWhnf.ok_of_bind hrun
    cases hm
    obtain ⟨hc', hi', hg', hps⟩ := (by
      repeat' first
        | with_reducible_and_instances first
          | exact KeepsCG.pure _
          | exact KeepsCG.get
          | exact KeepsCG.log _
          | exact KeepsCG.isInstance _
          | refine KeepsCG.modify fun _ => ⟨rfl, rfl, rfl⟩
          | refine KeepsCG.read_bind fun _ => ?_
          | refine KeepsCG.bind ?_ fun _ => ?_
          | refine KeepsCG.ite (fun _ => ?_) (fun _ => ?_) : KeepsCG ⟨decls, view⟩ _) _ _ _ _ _ _ hrun
    dsimp only at hW
    have hread := (hG.value_consts hci hv hthm hcs).2
    have hvcl : FVarsIn (fun _ => False) v := hG.closed ci hci' v hread
    have hmfv : MachineFree cfg v := hG.mfd ci hci' v hread
    have hnpv : NatPlain cfg v := hG.npd ci hci' v hread
    have hW' : (visitExpr (m := PureM) fuel v).runPure sb
        { lctx := tc.lctx, locals := [], config := tc.config, decl := c } ⟨decls, view⟩ ps =
          .ok ((t, st₂), ps₂) := by
      rw [← hW]
      exact (visit_agree (S := fun _ => False) (pc := ⟨decls, view⟩)
        (tc := { lctx := tc.lctx, locals := [], config := tc.config, decl := c })
        (ls₁ := tc.locals) (ls₂ := []) hG.closed
        (by rw [show ({ lctx := tc.lctx, locals := [], config := tc.config, decl := c } :
          TravCtx).config = cfg from hcfg]; exact hmfv)
        (by rw [show ({ lctx := tc.lctx, locals := [], config := tc.config, decl := c } :
          TravCtx).config = cfg from hcfg]; exact hG.mfd)
        hG.blk hG.idx (fun _ h => h.elim) (fun _ h => h.elim) hvcl).symm
    have hctx0 : CtxOK E B ci.levelParams (.nil : Metalean.Ctx ζ ci.levelParams.length 0 0) []
        cfg { lctx := tc.lctx, locals := [], config := tc.config, decl := c } ps :=
      ⟨.nil, fun _ h => (nomatch h), fun _ => rfl, fun _ _ => rfl, rfl, hcfg⟩
    obtain ⟨e₀, T₀, htr, hty⟩ := ProgEnv.value_typed hG.prog hG.wf hmP hv hthm
    have hoccS : ∀ d, nameOccurs d v = true → S d := by
      obtain ⟨ci₀, hci₀, hval₀⟩ := hsc c hS
      rw [hci] at hci₀
      cases hci₀
      exact hval₀ v hv hthm hcs
    have hokb := StateOK.congr hok hcb hib hgb
    have ⟨her, hdeps, hgr⟩ := ih.expr fuel (Nat.le_refl _) v hctx0 hsc hoccS hmfv hnpv
      (hG.recShaped ci hci' v hread) hokb htr ⟨T₀, hty⟩ hW'
    obtain ⟨S', hsc', hvS', hcS'⟩ := hG.valueScope hci hv hthm hcs
    obtain ⟨-, -, hgr'⟩ := ih.expr fuel (Nat.le_refl _) v hctx0 hsc' hvS' hmfv hnpv
      (hG.recShaped ci hci' v hread) hokb htr ⟨T₀, hty⟩ hW'
    have hnew₂ : st₂.constants[c]? = none := by
      cases h : st₂.constants[c]? with
      | none => rfl
      | some kn => exact (hcS' (hgr'.scope c kn (by rw [hcb]; exact hnew) h)).elim
    have hd : ErasesDecl E B (evalEnvOf view cfg decls) ci ⟨some t⟩ := by
      unfold ErasesDecl
      rw [hv]
      exact .inr ⟨hax, t, rfl, her⟩
    obtain ⟨hok₃, hext₃⟩ := hgr.inv.register hG.inj hci hnb hnew₂ hd fun b hb => by
      cases hb
      refine ⟨hdeps, by simpa using Erases.closed htr her, fun x => ?_⟩
      cases hx : hasFVar x t
      · rfl
      · exact (Erases.hasFVar_of her (fun _ => False) (KFV.of_fvarsIn hvcl) x hx).elim
    refine ⟨⟨StateOK.congr hok₃ hc' hi' hg', ?_, hps ▸ hgr.next, ?_⟩, toKername c, ?_⟩
    · rw [hg', ← hgb]
      exact LenvExt.trans hgr.ext hext₃
    · intro c' kn h0 h1
      rw [hc'] at h1
      change (st₂.constants.insert c (toKername c))[c']? = some kn at h1
      rw [Std.HashMap.getElem?_insert] at h1
      split at h1
      · rename_i hcc
        rw [← beq_iff_eq.1 hcc]
        exact hS
      · exact hgr.scope c' kn (by rw [hcb]; exact h0) h1
    · rw [hc']
      exact Std.HashMap.getElem?_insert_self

end

end Steps

end EraseProof
