import EraseProof.Relation.Inst
import EraseProof.Relation.Deps
import EraseProof.Source.Value
import EraseProof.Bridge.CLRead

/-!
# Cases of the relation-level simulation

`erases_correct` (`MR E/ErasureCorrectness.v:51`) is proved by induction on the source evaluation,
one case per rule of `SrcEval`. This module proves the cases of the rules `beta`, `etaBeta`, `zeta`,
`delta`, `constAtom`, `appCong`, `atom`, `etaLam`, `frozen` and `frozenApp`, each as a theorem
whose premises are premises of the rule and the induction hypotheses of its evaluation premises
(`ErasesSim`), and whose conclusion is `ErasesSim` of the rule's conclusion. Adapted from
`ML-V Simulation/Cases.lean`. The relation has no typing premise and relates to `□` exactly the
`erase`-marked terms, so no case has ML-V's uniform `□` subcase (`erases_correct_box`, which needs
the erasability of the value): a frozen term is a value of its own (`frozen`, `frozenApp`), and
an unmarked term erases by its own rule only. An atom constant and an atom spine have no erasure
(the traversal marks them), so the cases `constAtom` and `appCong` hold vacuously. The closedness
that substitution asks of the substituted value is read from the rule's certificate `CLOk`.
-/

open Lean Erasure

namespace EraseProof

/-- The conclusion of `erases_correct_statement` for one evaluation `e ⇓ v`: every erasure, with
erased dependencies, of `e` evaluates in λ□ to an erasure of `v`. The induction hypothesis of each
case of the simulation. Adapted from `ML-V Simulation/Cases.lean:31`, without the typed
translation. Reference: the induction hypotheses of `erases_correct`
(`MR E/ErasureCorrectness.v:51`). -/
def ErasesSim (σ : EvalEnv) (lenv : GlobalDeclarations) (e v : Expr) : Prop :=
  ∀ {tb : LBTerm}, Erases noCert σ [] e tb → ErasesDeps noCert σ lenv tb →
    ∃ vb, Erases noCert σ [] v vb ∧ LBEval defaultFlags lenv tb vb

namespace SimCases

variable {cert : BoxCert} {σ : EvalEnv} {lenv : GlobalDeclarations}

/-! ## Inversions -/

/-- A constant spine has the constant as its head. -/
theorem spine_fn {e : Expr} {c : Name} {us : List Level} {as : List Expr}
    (h : e = mkAppN (.const c us) as.toArray) : e.getAppFn = .const c us := by
  rw [h, getAppFn_mkAppN_const]

/-- An erasure of a λ is a λ□ λ of an erasure of its body (`Erases.lam`). -/
theorem lam_inv {Γ : List CtxBinder} {x : Name} {A b : Expr} {bi : BinderInfo} {tb : LBTerm}
    (h : Erases cert σ Γ (.lam x A b bi) tb) :
    ∃ b', tb = .lambda (binderNameOf x) b' ∧ Erases cert σ ((A, none) :: Γ) b b' := by
  generalize hx : Expr.lam x A b bi = y at h
  cases h with
  | lam hb => cases hx; exact ⟨_, rfl, hb⟩
  | ctor | cases | casesReduced | quotMk | quotLift | recLet | recFix => cases spine_fn hx
  | bvar | fvar | etaLam | letE | app | const | proj | litZero | litSucc | box => cases hx

/-- An erasure of an `eta`-marked λ is a λ□ λ of an erasure of its body (`Erases.etaLam`). -/
theorem etaLam_inv {Γ : List CtxBinder} {x : Name} {A b : Expr} {bi : BinderInfo} {tb : LBTerm}
    (h : Erases cert σ Γ (markEta (.lam x A b bi)) tb) :
    ∃ b', tb = .lambda (binderNameOf x) b' ∧ Erases cert σ ((A, none) :: Γ) b b' := by
  generalize hx : markEta (.lam x A b bi) = y at h
  cases h with
  | etaLam hb => cases hx; exact ⟨_, rfl, hb⟩
  | ctor | cases | casesReduced | quotMk | quotLift | recLet | recFix => cases spine_fn hx
  | bvar | fvar | lam | letE | app | const | proj | litZero | litSucc | box => cases hx

/-- An erasure of a `let` is a λ□ `let` of erasures of its value and body (`Erases.letE`). -/
theorem letE_inv {Γ : List CtxBinder} {x : Name} {T v b : Expr} {nd : Bool} {tb : LBTerm}
    (h : Erases cert σ Γ (.letE x T v b nd) tb) :
    ∃ v' b', tb = .letIn (binderNameOf x) v' b' ∧ Erases cert σ Γ v v' ∧
      Erases cert σ ((T, some v) :: Γ) b b' := by
  generalize hx : Expr.letE x T v b nd = y at h
  cases h with
  | letE hv hb => cases hx; exact ⟨_, _, rfl, hv, hb⟩
  | ctor | cases | casesReduced | quotMk | quotLift | recLet | recFix => cases spine_fn hx
  | bvar | fvar | lam | etaLam | app | const | proj | litZero | litSucc | box => cases hx

/-- A frozen term erases to `□` only (`Erases.box`). -/
theorem box_inv {Γ : List CtxBinder} {s : Expr} {tb : LBTerm} (h : Erases cert σ Γ (markErase s) tb) :
    tb = .box := by
  generalize hx : markErase s = y at h
  cases h with
  | box => rfl
  | ctor | cases | casesReduced | quotMk | quotLift | recLet | recFix => cases spine_fn hx
  | bvar | fvar | lam | etaLam | letE | app | const | proj | litZero | litSucc => cases hx

/-- A constant evaluated by its own rules is no atom. -/
theorem isAtom_own {c : Name} {ci : ConstantInfo} (hc : findDecl σ.decls c = some ci)
    (ho : OwnRules ci = true) : σ.isAtom c = false := by
  unfold EvalEnv.isAtom; rw [hc]; simp [ho]

/-- A recognized `casesOn` is no atom. -/
theorem isAtom_casesOn {c : Name} {iv : InductiveVal} (hc : σ.casesOn? c = some iv) :
    σ.isAtom c = false := by
  unfold EvalEnv.isAtom; split <;> simp [hc]

/-- The head constant of an erased spine is no atom: `Erases.const` asks `isAtom = false`, and the
heads of the special rules (constructors, recognized `casesOn`, erased quotient constants,
recursors) are evaluated by their own rules. -/
theorem head_not_atom {c : Name} {us : List Level} {e : Expr} {Γ : List CtxBinder} {tb : LBTerm}
    (hfn : e.getAppFn = .const c us) (h : Erases cert σ Γ e tb) : σ.isAtom c = false := by
  induction e generalizing Γ tb with
  | app f a ihf =>
    generalize hx : Expr.app f a = y at h hfn
    cases h with
    | app _ hf _ => cases hx; exact ihf hfn hf
    | ctor hc => rw [getAppFn_mkAppN_const] at hfn; cases hfn; exact isAtom_ctor hc
    | cases hco | casesReduced _ hco =>
      rw [getAppFn_mkAppN_const] at hfn; cases hfn; exact isAtom_casesOn hco
    | quotMk hq hk | quotLift hq hk =>
      rw [getAppFn_mkAppN_const] at hfn; cases hfn; exact isAtom_own hq (by simp [OwnRules, hk])
    | recLet hr | recFix hr => rw [getAppFn_mkAppN_const] at hfn; cases hfn; exact isAtom_own hr rfl
    | bvar | fvar | lam | etaLam | letE | const | proj | litZero | litSucc | box => cases hx
  | const =>
    generalize hx : Expr.const _ _ = y at h hfn
    cases h with
    | const hna => cases hx; cases hfn; exact hna
    | ctor hc => rw [getAppFn_mkAppN_const] at hfn; cases hfn; exact isAtom_ctor hc
    | cases hco | casesReduced _ hco =>
      rw [getAppFn_mkAppN_const] at hfn; cases hfn; exact isAtom_casesOn hco
    | quotMk hq hk | quotLift hq hk =>
      rw [getAppFn_mkAppN_const] at hfn; cases hfn; exact isAtom_own hq (by simp [OwnRules, hk])
    | recLet hr | recFix hr => rw [getAppFn_mkAppN_const] at hfn; cases hfn; exact isAtom_own hr rfl
    | bvar | fvar | lam | etaLam | letE | app | proj | litZero | litSucc | box => cases hx
  | _ => cases hfn

/-- An atom spine has no erasure. -/
theorem _root_.EraseProof.AtomSpine.not_erases {Γ : List CtxBinder} {e : Expr} {tb : LBTerm} (ha : AtomSpine σ e) :
    ¬ Erases cert σ Γ e tb := fun h => by
  obtain ⟨c, us, hfn, hat⟩ := ha.head
  rw [head_not_atom hfn h] at hat; cases hat

/-- An unfoldable constant is a definition of the evaluation environment, unfolded to its value,
that is neither remapped nor a recognized `casesOn`. Adapted from `ML-V Simulation/Cases.lean:237`. -/
theorem unfold?_spec {c : Name} {ci : ConstantInfo} {b : Expr} (h : σ.unfold? c = some (ci, b)) :
    ∃ v, ci = .defnInfo v ∧ b = v.value ∧ findDecl σ.decls c = some ci ∧
      σ.axiomatized ci = false ∧ σ.casesOn? c = none := by
  unfold EvalEnv.unfold? at h
  split at h
  · rename_i v hv
    split at h
    · cases h
    · rename_i hn
      cases h
      simp only [Bool.or_eq_true, Option.isSome_iff_ne_none, not_or, ne_eq, Classical.not_not] at hn
      exact ⟨v, rfl, rfl, hv, Bool.eq_false_iff.2 hn.1, hn.2⟩
  · cases h

/-- An erasure of an unfoldable constant is its λ□ constant. Adapted from
`ML-V Simulation/Cases.lean:253`, without the `□` alternative. -/
theorem const_inv {Γ : List CtxBinder} {c : Name} {us : List Level} {ci : ConstantInfo} {b : Expr}
    {tb : LBTerm} (hu : σ.unfold? c = some (ci, b)) (h : Erases cert σ Γ (.const c us) tb) :
    tb = .const (toKername c) := by
  obtain ⟨v, rfl, -, hfd, -, hco⟩ := unfold?_spec hu
  generalize hx : Expr.const c us = y at h
  have hfn : y.getAppFn = .const c us := by rw [← hx]; rfl
  cases h with
  | const => cases hx; rfl
  | ctor hq | quotMk hq | quotLift hq | recLet hq | recFix hq =>
    rw [getAppFn_mkAppN_const] at hfn; cases hfn; rw [hfd] at hq; cases hq
  | cases hq | casesReduced _ hq =>
    rw [getAppFn_mkAppN_const] at hfn; cases hfn; rw [hco] at hq; cases hq
  | bvar | fvar | lam | etaLam | letE | app | proj | litZero | litSucc | box => cases hx

/-- A term con-leche types has no loose bound variable (`CLTyped.closed`, `AbsFV.LBV_of_toCL?`):
the closedness premise of `Erases.inst`. -/
theorem _root_.EraseProof.CLOk.lbv {env : ConLeche.Env} {t : Expr} (h : CLOk env t) : AbsFV.LBV 0 t := by
  obtain ⟨c, F, T, hc, hinf⟩ := h
  exact AbsFV.LBV_of_toCL? hc (CLTyped.closed ⟨c, F, T, hc, hinf⟩ hc)

/-! ## The cases -/

/-- The common part of the `beta` and `etaBeta` cases: the head's erasure evaluates to an erasure
of the λ `L`, a λ□ λ, whose body with the argument's value substituted (`Erases.inst`) erases the
source's substituted body. -/
theorem beta_core {f a a' b v L A : Expr} (hns : ¬ ShortSpine σ (.app f a))
    (hla : AbsFV.LBV 0 a')
    (hL : ∀ {t}, Erases noCert σ [] L t → ∃ na b', t = .lambda na b' ∧
      Erases noCert σ [(A, none)] b b')
    (ihf : ErasesSim σ lenv f L) (iha : ErasesSim σ lenv a a')
    (ihb : ErasesSim σ lenv (b.instantiate1' a') v) : ErasesSim σ lenv (.app f a) v := by
  intro tb her hdeps
  obtain ⟨tf, ta, rfl, herf, hera⟩ := Erases.app_inv hns her
  cases hdeps with
  | app hdf hda =>
  obtain ⟨vf, hvf, hevf⟩ := ihf herf hdf
  obtain ⟨va, hva, heva⟩ := iha hera hda
  obtain ⟨na, b', rfl, hb'⟩ := hL hvf
  cases ErasesDeps.eval hdf hevf with
  | lambda hdb =>
  obtain ⟨res, hres, hevres⟩ := ihb (Erases.inst hb' hva hla)
    (ErasesDeps.csubst (ErasesDeps.eval hda heva) hdb)
  exact ⟨res, hres, .beta hevf heva hevres⟩

/-- The `beta` case of `erases_correct`. The head is no short spine, so the application's erasure is
an application of erasures (`Erases.app_inv`); the λ value erases to a λ□ λ only (ML-V also has a
`□` erasure of the λ, whose substituted body it shows erasable). Adapted from
`ML-V Simulation/Cases.lean:522`. Reference: the `eval_beta` case of `erases_correct`
(`MR E/ErasureCorrectness.v:62`); Let. Thm 13 (β). -/
theorem erases_correct_beta {env : ConLeche.Env} {f a a' b v A : Expr} {n : Name} {bi : BinderInfo}
    (hns : ¬ ShortSpine σ (.app f a)) (hok : CLOk env (.app (.lam n A b bi) a'))
    (ihf : ErasesSim σ lenv f (.lam n A b bi)) (iha : ErasesSim σ lenv a a')
    (ihb : ErasesSim σ lenv (b.instantiate1' a') v) : ErasesSim σ lenv (.app f a) v :=
  beta_core hns hok.lbv.2 (fun h => (lam_inv h).elim fun b' h' => ⟨_, b', h'⟩) ihf iha ihb

/-- The `etaBeta` case of `erases_correct`: as `beta`, on an `eta`-marked λ (`Erases.etaLam`).
Reference: the `eval_beta` case of `erases_correct` (`MR E/ErasureCorrectness.v:62`). -/
theorem erases_correct_etaBeta {env : ConLeche.Env} {f a a' b v A : Expr} {n : Name}
    {bi : BinderInfo} (hns : ¬ ShortSpine σ (.app f a))
    (hok : CLOk env (.app (markEta (.lam n A b bi)) a'))
    (ihf : ErasesSim σ lenv f (markEta (.lam n A b bi))) (iha : ErasesSim σ lenv a a')
    (ihb : ErasesSim σ lenv (b.instantiate1' a') v) : ErasesSim σ lenv (.app f a) v :=
  beta_core hns hok.lbv.2 (fun h => (etaLam_inv h).elim fun b' h' => ⟨_, b', h'⟩) ihf iha ihb

/-- The `zeta` case of `erases_correct`: the `let` value's erasure evaluates to an erasure of its
value, which substituted into the erased body (`Erases.inst_let`) erases the source's substituted
body (ML-V relates the body under the value's typed translation, `SimCases.inst_let`). Adapted
from `ML-V Simulation/Cases.lean:668`. Reference: the `eval_zeta` case of `erases_correct`
(`MR E/ErasureCorrectness.v:110`); Let. Thm 13 (ζ). -/
theorem erases_correct_zeta {env : ConLeche.Env} {x : Name} {T val val' b v : Expr} {nd : Bool}
    (hok : CLOk env (.letE x T val' b nd)) (ihv : ErasesSim σ lenv val val')
    (ihb : ErasesSim σ lenv (b.instantiate1' val') v) :
    ErasesSim σ lenv (.letE x T val b nd) v := by
  intro tb her hdeps
  obtain ⟨v₀, b', rfl, herv, herb⟩ := letE_inv her
  cases hdeps with
  | letIn hdv hdb =>
  obtain ⟨vv, hvv, hevv⟩ := ihv herv hdv
  obtain ⟨res, hres, hevres⟩ := ihb (Erases.inst_let herb hvv hok.lbv.2.1)
    (ErasesDeps.csubst (ErasesDeps.eval hdv hevv) hdb)
  exact ⟨res, hres, .zeta hevv hevres⟩

/-- The `delta` case of `erases_correct`: an unfoldable constant erases to its λ□ constant
(`SimCases.const_inv`); the λ□ declaration found at its kername is its own (`KernameInj`), whose
body erases every marking of the constant's value (`ErasesDecl`), so the marking `SrcEval.delta`
unfolds, at the occurrence's levels too (`Erases.instLevels`). ML-V also has a `□` erasure of the
constant and relates the body to the value's typed translation. Adapted from
`ML-V Simulation/Cases.lean:725`. Reference: the `eval_delta` case of `erases_correct`
(`MR E/ErasureCorrectness.v:152`); Let. Thm 13 (δ). -/
theorem erases_correct_delta (hinj : KernameInj σ.decls) {c : Name} {us : List Level}
    {ci : ConstantInfo} {body bM v : Expr} (hu : σ.unfold? c = some (ci, body))
    (hm : MarkOf σ.decls σ.cfg [] body bM)
    (ih : ErasesSim σ lenv (Pure.instLevels ci.levelParams us bM) v) :
    ErasesSim σ lenv (.const c us) v := by
  intro tb her hdeps
  obtain rfl := const_inv hu her
  obtain ⟨dv, rfl, rfl, hfd, hax, -⟩ := unfold?_spec hu
  generalize hk : toKername c = kn at hdeps
  cases hdeps with
  | @const c' ci' cb hfd' hl hdecl hbody =>
    cases hinj c c' (by rw [hfd]; rfl) (by rw [hfd']; rfl) hk
    rw [hfd] at hfd'; cases hfd'
    simp only [ErasesDecl, ConstantInfo.value?] at hdecl
    rcases hdecl with ⟨hax', -⟩ | ⟨-, -, b', hcb, herb⟩
    · rw [hax] at hax'; cases hax'
    · obtain ⟨res, hres, hevres⟩ := ih (Erases.instLevels (herb bM hm) []) (hbody b' hcb)
      exact ⟨res, hres, .delta hl hcb hevres⟩

/-- The `constAtom` case of `erases_correct`, vacuous: an atom constant has no erasure
(`AtomSpine.not_erases`; ML-V erases it to `□`, which needs its erasability). Adapted from
`ML-V Simulation/Cases.lean:466`. Reference: the `eval_atom` case of `erases_correct` on `tInd`
(`MR E/ErasureCorrectness.v:1207`). -/
theorem erases_correct_constAtom {c : Name} {us : List Level} (ha : σ.isAtom c = true) :
    ErasesSim σ lenv (.const c us) (.const c us) :=
  fun her _ => absurd her (AtomSpine.const ha).not_erases

/-- The `appCong` case of `erases_correct`, vacuous: the head's value is an atom spine
(`SrcEval.value`, `¬ BlocksCong`), which has no erasure (`AtomSpine.not_erases`), while the
induction hypothesis of the head gives one (ML-V erases the application to `□`, which needs the
typing of the head's image, its premises `hsat`/`hsatq`). Adapted from
`ML-V Simulation/Cases.lean:763`. Reference: the `eval_app_cong` case of `erases_correct`
(`MR E/ErasureCorrectness.v:1127`). -/
theorem erases_correct_appCong {env : ConLeche.Env} {f a f' a' : Expr}
    (hns : ¬ ShortSpine σ (.app f a)) (hf : SrcEval env σ f f') (hnb : ¬ BlocksCong σ f')
    (ihf : ErasesSim σ lenv f f') : ErasesSim σ lenv (.app f a) (.app f' a') := by
  intro tb her hdeps
  obtain ⟨tf, ta, rfl, herf, -⟩ := Erases.app_inv hns her
  cases hdeps with
  | app hdf _ =>
  obtain ⟨vf, hvf, -⟩ := ihf herf hdf
  exact absurd hvf ((SrcEval.value hf).atomSpine hnb).not_erases

/-- The `atom` case of `erases_correct`: a λ erases to a λ□ λ, a λ□ value; a sort and a Π have no
erasure (ML-V erases them to `□`). Adapted from `ML-V Simulation/Cases.lean:446`. Reference: the
`eval_atom` case of `erases_correct` (`MR E/ErasureCorrectness.v:1179`). -/
theorem erases_correct_atom {e : Expr} (ha : SrcAtom e) : ErasesSim σ lenv e e := by
  intro tb her _
  refine ⟨tb, her, .atom ?_⟩
  have hfn : ∀ c us, e.getAppFn ≠ .const c us := by
    cases e <;> simp_all [SrcAtom, Expr.getAppFn]
  generalize hx : e = y at her
  cases her with
  | lam | etaLam | box => rfl
  | ctor | cases | casesReduced | quotMk | quotLift | recLet | recFix =>
    exact absurd (spine_fn hx) (hfn _ _)
  | bvar | fvar | letE | app | const | proj | litZero | litSucc => subst hx; exact absurd ha id

/-- The `etaLam` case of `erases_correct`: an `eta`-marked λ erases to a λ□ λ, a λ□ value.
Reference: the `eval_atom` case of `erases_correct` (`MR E/ErasureCorrectness.v:1179`). -/
theorem erases_correct_etaLam {n : Name} {A b : Expr} {bi : BinderInfo} :
    ErasesSim σ lenv (markEta (.lam n A b bi)) (markEta (.lam n A b bi)) := by
  intro tb her _
  obtain ⟨_, rfl, -⟩ := etaLam_inv her
  exact ⟨_, her, .atom rfl⟩

/-- The `frozen` case of `erases_correct`: a frozen term erases to `□` only (`Erases.box`), a λ□
value. Reference: the `erases_box` cases of `erases_correct` (`MR E/ErasureCorrectness.v:58`), with
the value `□` (`MR E/EWcbvEval.v:36 atom`). -/
theorem erases_correct_frozen {s : Expr} : ErasesSim σ lenv (markErase s) (markErase s) := by
  intro tb her _
  obtain rfl := box_inv her
  exact ⟨.box, .box trivial, .atom rfl⟩

/-- The `frozenApp` case of `erases_correct`: the head is no short spine, so the application's
erasure is an application of erasures (`Erases.app_inv`); the head's erasure evaluates to an
erasure of a frozen term, `□`, so the application evaluates to `□` (λ□ `eval_box`), an erasure of
the frozen value. Reference: `eval_box` (`MR E/EWcbvEval.v:121`). -/
theorem erases_correct_frozenApp {f a s a' : Expr} (hns : ¬ ShortSpine σ (.app f a))
    (ihf : ErasesSim σ lenv f (markErase s)) (iha : ErasesSim σ lenv a a') :
    ErasesSim σ lenv (.app f a) (markErase (.app s a')) := by
  intro tb her hdeps
  obtain ⟨tf, ta, rfl, herf, hera⟩ := Erases.app_inv hns her
  cases hdeps with
  | app hdf hda =>
  obtain ⟨vf, hvf, hevf⟩ := ihf herf hdf
  obtain ⟨va, -, heva⟩ := iha hera hda
  obtain rfl := box_inv hvf
  exact ⟨.box, .box trivial, .box hevf heva⟩

end SimCases

end EraseProof
