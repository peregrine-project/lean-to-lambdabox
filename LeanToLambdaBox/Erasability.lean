import Lean4Lean.Theory.VExpr
import Lean4Lean.Theory.Typing.Basic
import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.UniqueTyping

/-!
# Erasability over lean4lean's `VExpr`

The relevance decision is the heart of erasure: a subterm is replaced by `box`
exactly when it is *irrelevant* — a proof or a type-former. The shipping
`Erasure.isErasable` decides this with `Meta.isProp ∨ Meta.isTypeFormerType` on
the inferred type. This file states the same predicate over lean4lean's formal
type theory (`VExpr` + the `HasType` judgment), so that the (forthcoming) typed
`Erases` relation can carry a *real* irrelevance witness in its `box` rule
instead of the trivial `box : Erases .box .box`.

This is step A1 of the semantic-grounding programme (see the project plan).
-/

namespace LeanToLambdaBox

open Lean4Lean

/--
A `VExpr` is an *arity* when it is a (possibly nullary) telescope ending in a
sort: `∀ x₁ … xₙ, Sort u`. These are the type-formers/predicates whose inhabitants
erasure replaces with `box`.

This is a *syntactic* characterisation of the inferred type. The shipping
`Meta.isTypeFormerType` whnf-reduces while peeling `∀`s; the defeq-closed form that
bridges the two is `IsArityUpTo` below, which `Erasable` is stated with.
-/
inductive IsArity : VExpr → Prop
  | sort (u : VLevel) : IsArity (.sort u)
  | forallE (A B : VExpr) : IsArity B → IsArity (.forallE A B)

/-- `A` is an arity *up to definitional equality* — defeq to a syntactic arity.
Unlike `IsArity`, this is defeq-invariant (by transitivity of `IsDefEqU`), which is
what lets `Erasable` survive reduction (needed for box-soundness in
`erases_correct`). It is also more faithful to `Meta.isTypeFormerType`, which
whnf-reduces while peeling `∀`s. -/
def IsArityUpTo (env : VEnv) (U : Nat) (Γ : List VExpr) (A : VExpr) : Prop :=
  ∃ A', env.IsDefEqU U Γ A A' ∧ IsArity A'

/--
`Erasable env U Γ e` holds when `e` is irrelevant in the typing context `Γ`
(with `U` universe parameters) under environment `env`: either

* a **proof** — its type `A` itself has type `Prop = Sort 0`; or
* a **type-former** — its type `A` is an arity up to defeq (`IsArityUpTo`).

This is the `VExpr` analogue of `Erasure.isErasable`
(`Meta.isProp (inferType e) ∨ Meta.isTypeFormerType (inferType e)`).
-/
def Erasable (env : VEnv) (U : Nat) (Γ : List VExpr) (e : VExpr) : Prop :=
  ∃ A, env.HasType U Γ e A ∧ (env.HasType U Γ A (.sort .zero) ∨ IsArityUpTo env U Γ A)

/-! ### Stability of `IsArity`/`Erasable` under instantiation and weakening (step A2.0).

These are the only genuinely new metatheory the `Expr`-based `Erases` re-base needs:
when a `box`-erased subterm is substituted into or lifted, its irrelevance witness
must survive. `IsArity` survives because `VExpr.inst`/`VExpr.liftN` fix `.sort` and
map `.forallE` structurally; `Erasable` survives by combining that with lean4lean's
`HasType.instN`/`HasType.weakN`. -/

theorem IsArity.inst {A : VExpr} (h : IsArity A) (e₀ : VExpr) (k : Nat) :
    IsArity (A.inst e₀ k) := by
  induction h generalizing k with
  | sort u => exact .sort u
  | forallE _ _ _ ih => exact .forallE _ _ (ih (k + 1))

theorem IsArity.liftN {A : VExpr} (h : IsArity A) (n k : Nat) :
    IsArity (A.liftN n k) := by
  induction h generalizing k with
  | sort u => exact .sort u
  | forallE _ _ _ ih => exact .forallE _ _ (ih (k + 1))

theorem IsArityUpTo.inst {env : VEnv} (henv : env.Ordered)
    {U : Nat} {Γ₀ Γ₁ Γ : List VExpr} {e₀ A₀ : VExpr} {k : Nat}
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (h₀ : env.HasType U Γ₀ e₀ A₀)
    {A : VExpr} (h : IsArityUpTo env U Γ₁ A) :
    IsArityUpTo env U Γ (A.inst e₀ k) := by
  obtain ⟨A', hd, har⟩ := h
  exact ⟨A'.inst e₀ k, hd.instN henv W h₀, har.inst e₀ k⟩

theorem IsArityUpTo.weakN {env : VEnv} (henv : env.Ordered)
    {U : Nat} {Γ Γ' : List VExpr} {n k : Nat} (W : Ctx.LiftN n k Γ Γ')
    {A : VExpr} (h : IsArityUpTo env U Γ A) :
    IsArityUpTo env U Γ' (A.liftN n k) := by
  obtain ⟨A', hd, har⟩ := h
  exact ⟨A'.liftN n k, hd.weakN henv W, har.liftN n k⟩

/-- The payoff of the up-to-defeq refinement: `IsArityUpTo` is **defeq-invariant**
in its type argument (which the syntactic `IsArity` was not). If `A''` is defeq to
`A` and `A` is an arity-up-to-defeq, so is `A''` — by transitivity of `IsDefEqU`.
This is what lets the type-former disjunct of `Erasable` survive reduction in the
forthcoming box-soundness argument. -/
theorem IsArityUpTo.defeq {env : VEnv} (henv : env.WF) {U : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) {A A'' : VExpr}
    (hAA : env.IsDefEqU U Γ A'' A) (h : IsArityUpTo env U Γ A) :
    IsArityUpTo env U Γ A'' := by
  obtain ⟨A', hd, har⟩ := h
  exact ⟨A', VEnv.IsDefEqU.trans henv hΓ hAA hd, har⟩

/-- **Box-soundness core.** `Erasable` is preserved under definitional equality of
the *term*: if `e` is erasable and `e ≡ e'`, then `e'` is erasable. Since a
reduction step `e ⟶ e'` is a definitional equality, this says an irrelevant term
stays irrelevant when reduced — the property that makes erasing it to `box` sound
in `erases_correct`. The type witness transfers via lean4lean's `HasType.defeqU_l`
(same type `A`, so the proof/arity disjunct carries over unchanged). -/
theorem Erasable.defeq {env : VEnv} (henv : env.WF) {U : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) {e e' : VExpr}
    (hee : env.IsDefEqU U Γ e e') (h : Erasable env U Γ e) :
    Erasable env U Γ e' := by
  obtain ⟨A, hA, hcase⟩ := h
  exact ⟨A, hA.defeqU_l henv hΓ hee, hcase⟩

/-- `IsArityUpTo` transports along a definitionally-equal *context*: the witness
defeq transports via `IsDefEqU.defeqDFC`, the syntactic `IsArity` is context-blind. -/
theorem IsArityUpTo.defeqDFC {env : VEnv} (henv : env.Ordered) {U : Nat}
    {Γ₀ Γ₁ Γ₂ : List VExpr} (hΓ : VEnv.IsDefEqCtx env U Γ₀ Γ₁ Γ₂)
    {A : VExpr} (h : IsArityUpTo env U Γ₁ A) : IsArityUpTo env U Γ₂ A :=
  let ⟨A', hd, har⟩ := h; ⟨A', hd.defeqDFC henv hΓ, har⟩

/-- `Erasable` transports along a definitionally-equal *context*: the type witness
transports via `HasType.defeqDFC`, and each disjunct via `HasType.defeqDFC` /
`IsArityUpTo.defeqDFC`. Used to move an irrelevance witness between defeq contexts
(e.g. when a `vlet` binder's value is replaced by a defeq one). -/
theorem Erasable.defeqDFC {env : VEnv} (henv : env.Ordered) {U : Nat}
    {Γ₀ Γ₁ Γ₂ : List VExpr} (hΓ : VEnv.IsDefEqCtx env U Γ₀ Γ₁ Γ₂)
    {e : VExpr} (h : Erasable env U Γ₁ e) : Erasable env U Γ₂ e := by
  obtain ⟨A, hA, hcase⟩ := h
  refine ⟨A, hA.defeqDFC henv hΓ, ?_⟩
  cases hcase with
  | inl hp => exact .inl (hp.defeqDFC henv hΓ)
  | inr ha => exact .inr (ha.defeqDFC henv hΓ)

/-- `Erasable` is preserved by weakening: lifting an irrelevant term keeps it
irrelevant. Uses lean4lean's `HasType.weakN` and `IsArity.liftN`; the type-of-type
`Sort 0` is fixed by `liftN`. -/
theorem Erasable.weakN {env : VEnv} (henv : env.Ordered)
    {U : Nat} {Γ Γ' : List VExpr} {n k : Nat} (W : Ctx.LiftN n k Γ Γ')
    {e : VExpr} (h : Erasable env U Γ e) :
    Erasable env U Γ' (e.liftN n k) := by
  obtain ⟨A, hA, hcase⟩ := h
  refine ⟨A.liftN n k, hA.weakN henv W, ?_⟩
  cases hcase with
  | inl hp => exact .inl (hp.weakN henv W)
  | inr ha => exact .inr (ha.weakN henv W)

/-- `Erasable` is preserved by instantiation: substituting into an irrelevant term
keeps it irrelevant. Uses lean4lean's `HasType.instN` and `IsArity.inst`; the
type-of-type `Sort 0` is fixed by `inst`. This is the witness that discharges the
`box` case of `erases_subst`. -/
theorem Erasable.inst {env : VEnv} (henv : env.Ordered)
    {U : Nat} {Γ₀ Γ₁ Γ : List VExpr} {e₀ A₀ : VExpr} {k : Nat}
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (h₀ : env.HasType U Γ₀ e₀ A₀)
    {e : VExpr} (h : Erasable env U Γ₁ e) :
    Erasable env U Γ (e.inst e₀ k) := by
  obtain ⟨A, hA, hcase⟩ := h
  refine ⟨A.inst e₀ k, hA.instN henv W h₀, ?_⟩
  cases hcase with
  | inl hp => exact .inl (hp.instN henv W h₀)
  | inr ha => exact .inr (ha.inst henv W h₀)

/-! ### Box propagation through application (MetaCoq's `eval_box` content).

If a function `f` is erasable (a proof or a type-former) and `f a` is well-typed,
then `f a` is erasable too. This is the type-theoretic fact behind the target
`Eval.app_box` rule: applying an irrelevant head yields an irrelevant result.

* If `f` is a **proof** (`f : A`, `A : Sort 0`): then `A`, being defeq to the
  function type `∀ x : Aᵈ, B`, is a `Prop`, so `imax · v ≈ 0` forces `v ≈ 0`,
  i.e. `B : Sort 0`; hence `f a : B[a] : Sort 0` is a proof.
* If `f` is a **type-former** (`A` is an arity up to defeq): then `B` is an arity
  up to defeq, so `B[a]` is too (`IsArityUpTo.inst`); hence `f a` is a
  type-former. -/
theorem Erasable.app {env : VEnv} (henv : env.WF) {U : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) {f a A B : VExpr}
    (hf : Erasable env U Γ f)
    (hTf : env.HasType U Γ f (.forallE A B))
    (hTa : env.HasType U Γ a A) :
    Erasable env U Γ (.app f a) := by
  obtain ⟨T, hfT, hcase⟩ := hf
  -- `f`'s type `T` is defeq to its function type `∀ A, B`.
  have hTeq : env.IsDefEqU U Γ T (.forallE A B) :=
    VEnv.IsDefEq.uniqU henv hΓ hfT hTf
  -- `f a : B.inst a`.
  have hTapp : env.HasType U Γ (.app f a) (B.inst a) := hTf.app hTa
  refine ⟨B.inst a, hTapp, ?_⟩
  cases hcase with
  | inl hp =>
      -- Proof case: `∀ A, B : Sort 0`, so `B : Sort 0`, so `B.inst a : Sort 0`.
      left
      -- Transport `T : Sort 0` to `∀ A, B : Sort 0`.
      have hforallProp : env.HasType U Γ (.forallE A B) (.sort .zero) :=
        hp.defeqU_l henv hΓ hTeq
      -- Invert: `B : Sort v` with `imax u v ≈ 0`, i.e. `v ≈ 0`.
      obtain ⟨⟨u, hAu⟩, v, hBv⟩ := VEnv.IsType.forallE_inv henv.ordered ⟨_, hforallProp⟩
      have hforallImax : env.HasType U Γ (.forallE A B) (.sort (.imax u v)) :=
        hAu.forallE hBv
      have hsorteq : env.IsDefEqU U Γ (.sort .zero) (.sort (.imax u v)) :=
        VEnv.IsDefEq.uniqU henv hΓ hforallProp hforallImax
      have hzero : VLevel.imax u v ≈ VLevel.zero :=
        (VEnv.IsDefEqU.sort_inv henv hΓ hsorteq).symm
      have hv0 : v ≈ VLevel.zero := VLevel.imax_eq_zero.1 hzero
      -- `B : Sort v ≡ Sort 0`, so `B : Sort 0` (in `A :: Γ`).
      have hΓA : OnCtx (A :: Γ) (env.IsType U) := ⟨hΓ, _, hAu⟩
      have hvWF : v.WF U := hBv.sort_r henv.ordered hΓA
      have hB0 : env.HasType U (A :: Γ) B (.sort .zero) :=
        (VEnv.IsDefEq.sortDF hvWF (l' := VLevel.zero) trivial hv0).defeq hBv
      -- Instantiate by `a : A` at depth 0: `(Sort 0).inst a = Sort 0`.
      have := hB0.instN henv.ordered (Ctx.InstN.zero) hTa
      simpa [VExpr.inst] using this
  | inr ha =>
      -- Type-former case: `B` is an arity up to defeq, so `B.inst a` is too.
      right
      have hforallAr : IsArityUpTo env U Γ (.forallE A B) :=
        ha.defeq henv hΓ (VEnv.IsDefEqU.symm hTeq)
      obtain ⟨C, hC, harC⟩ := hforallAr
      -- `forallE A B ≡ C` and `IsArity C`; `C` must itself be a `.forallE`.
      cases harC with
      | sort u => exact absurd hC (VEnv.IsDefEqU.sort_forallE_inv henv hΓ ∘ VEnv.IsDefEqU.symm)
      | forallE A' B' harB' =>
          obtain ⟨_, _, hBB'⟩ := VEnv.IsDefEqU.forallE_inv henv hΓ hC
          exact IsArityUpTo.inst henv.ordered (Ctx.InstN.zero) hTa
            ⟨B', ⟨_, hBB'⟩, harB'⟩

/-! ### Relevance of an inductive type former

`Erases.proj` fires only at an inductive whose declared result level is never `Prop`. The
criterion is **semantic** — the level never evaluates to zero — and not the syntactic
successor shape, which is false at `Prod`, whose declared type ends in
`Sort (max (u+1) (v+1))`, and at ten further projection heads of the corpus.
`VLevel.IsNeverZero` is lean4lean's own predicate, the one its kernel theory reads for large
elimination (`VInductDecl.LargeElim`).
-/

/-- The result sort of a `VExpr` Π-telescope. -/
def vResultSort : VExpr → Option VLevel
  | .forallE _ b => vResultSort b
  | .sort l => some l
  | _ => none

/-- Decides `VLevel.IsNeverZero`: a successor is never zero, a parameter can be instantiated
by zero, a `max` needs one nonzero side, and an `imax` is nonzero exactly when its right
argument is. Sound and complete — `neverZeroB_sound`, `neverZeroB_complete`. -/
def neverZeroB : VLevel → Bool
  | .zero | .param _ => false
  | .succ _ => true
  | .max a b => neverZeroB a || neverZeroB b
  | .imax _ b => neverZeroB b

/-- Soundness of `neverZeroB`. -/
theorem neverZeroB_sound : ∀ {l : VLevel}, neverZeroB l = true → l.IsNeverZero
  | .succ _, _, ls => by simp [VLevel.eval]
  | .max a b, h, ls => by
      simp only [neverZeroB, Bool.or_eq_true] at h
      rcases h with h | h
      · have := neverZeroB_sound h ls; simp [VLevel.eval]; omega
      · have := neverZeroB_sound h ls; simp [VLevel.eval]; omega
  | .imax _ b, h, ls => by
      have := neverZeroB_sound (l := b) h ls
      simp [VLevel.eval, Lean.Nat.imax, this]

/-- Completeness of `neverZeroB`: the all-zero instantiation witnesses the failure. -/
theorem neverZeroB_complete : ∀ {l : VLevel}, neverZeroB l = false → l.eval [] = 0
  | .zero, _ => rfl
  | .param _, _ => rfl
  | .max a b, h => by
      simp only [neverZeroB, Bool.or_eq_false_iff] at h
      simp [VLevel.eval, neverZeroB_complete h.1, neverZeroB_complete h.2]
  | .imax _ b, h => by
      simp only [neverZeroB] at h
      simp [VLevel.eval, Lean.Nat.imax, neverZeroB_complete h]

/-- The modelled inductive `I` is **relevant**: `env` knows it, and the result sort of its
model type never evaluates to `Prop`. This is the fragment boundary N18 draws — an
elimination of an irrelevant inductive into data is stuck on the target, because the erasure
marks no inductive propositional. -/
def InformativeInd (env : VEnv) (I : Name) : Prop :=
  ∃ ci, env.constants I = some ci ∧ ∃ l, vResultSort ci.type = some l ∧ l.IsNeverZero

/-- Relevance survives environment extension, which is what `Erases.mono`'s `proj` arm
needs. -/
theorem InformativeInd.mono {env env' : VEnv} {I : Name} (hle : env ≤ env')
    (h : InformativeInd env I) : InformativeInd env' I :=
  let ⟨ci, hci, l, hl, hnz⟩ := h; ⟨ci, hle.constants hci, l, hl, hnz⟩

/-- Every producer of the syntactic successor criterion is a producer of the semantic one,
so `FirstOrderDecl.informative` keeps its successor clause and still supplies relevance. -/
theorem informativeInd_of_succ {env : VEnv} {I : Name}
    (h : ∃ ci, env.constants I = some ci ∧ ∃ l, vResultSort ci.type = some (.succ l)) :
    InformativeInd env I :=
  let ⟨ci, hci, l, hl⟩ := h
  ⟨ci, hci, .succ l, hl, fun ls => by simp [VLevel.eval]⟩

/-! ### The two witnesses that separate the criteria

`Prod`'s declared type is `Sort u → Sort v → Sort (max (u+1) (v+1))` and `VLevel.ofLevel` is
a homomorphism, so the translated result level is `.max (.succ (.param 0)) (.succ (.param
1))` — accepted here, rejected by the successor shape. `And`'s is `Prop → Prop → Prop`,
rejected by both. -/

/-- `Prod`'s translated declared type. -/
def prodVTy : VExpr :=
  .forallE (.sort (.succ (.param 0)))
    (.forallE (.sort (.succ (.param 1)))
      (.sort (.max (.succ (.param 0)) (.succ (.param 1)))))

/-- `And`'s translated declared type. -/
def andVTy : VExpr := .forallE (.sort .zero) (.forallE (.sort .zero) (.sort .zero))

/-- A `.max`-headed result sort is relevant: the criterion accepts `Prod`. -/
theorem informativeInd_prod {env : VEnv} (h : env.constants ``Prod = some ⟨2, prodVTy⟩) :
    InformativeInd env ``Prod :=
  ⟨_, h, _, rfl, neverZeroB_sound (l := .max (.succ (.param 0)) (.succ (.param 1))) rfl⟩

/-- A `Prop`-valued structure is irrelevant: the criterion still rejects `And`. -/
theorem not_informativeInd_and {env : VEnv} (h : env.constants ``And = some ⟨0, andVTy⟩) :
    ¬ InformativeInd env ``And := by
  rintro ⟨ci, hci, l, hl, hnz⟩
  rw [h] at hci; cases hci
  cases Option.some.inj hl
  exact hnz [] rfl

/-! ## The propositional decision, model side

`Erasure.register_inductive` emits `propositional := isPropositionalArity inf.type`
(`Erasure.lean:368`), which is `arityResultSort` then `Lean.Level.isAlwaysZero`
(`Erasure.lean:281`, `:291`). MetaRocq states the emitted flag as an **equality**,
`isPropositionalArity ind_type = ind_propositional`
(`erases_one_inductive_body`, `../metarocq/erasure/theories/Extract.v:276`), so the model side
needs the same decision:
`vResultSort` mirrors `arityResultSort` arm for arm, and `alwaysZeroB` mirrors
`Level.isAlwaysZero`. -/

/-- Decides "this level is `Prop` at every valuation": `zero` is, a parameter and a successor
are not, a `max` needs both sides, and an `imax` is zero exactly when its right argument is.
`Lean.Level.isAlwaysZero`'s mirror (`Lean/Level.lean:212-218`) minus the `mvar` arm, which
`VLevel` does not have. Sound and complete — `alwaysZeroB_sound`, `alwaysZeroB_complete`. -/
def alwaysZeroB : VLevel → Bool
  | .zero => true
  | .param _ | .succ _ => false
  | .max a b => alwaysZeroB a && alwaysZeroB b
  | .imax _ b => alwaysZeroB b

/-- Soundness of `alwaysZeroB`. -/
theorem alwaysZeroB_sound : ∀ {l : VLevel}, alwaysZeroB l = true → ∀ ls, l.eval ls = 0
  | .zero, _, _ => rfl
  | .max a b, h, ls => by
      simp only [alwaysZeroB, Bool.and_eq_true] at h
      simp [VLevel.eval, alwaysZeroB_sound h.1 ls, alwaysZeroB_sound h.2 ls]
  | .imax _ b, h, ls => by
      simp only [alwaysZeroB] at h
      simp [VLevel.eval, Lean.Nat.imax, alwaysZeroB_sound h ls]

/-- Completeness of `alwaysZeroB`: the all-ones instantiation witnesses the failure, at any
width the level is well-formed for. The parameter arm is why a valuation is needed at all —
`neverZeroB_complete` can use the all-zero list, this one cannot. -/
theorem alwaysZeroB_complete {n : Nat} : ∀ {l : VLevel}, alwaysZeroB l = false → l.WF n →
    l.eval (List.replicate n 1) ≠ 0
  | .succ _, _, _ => by simp [VLevel.eval]
  | .param i, _, hwf => by
      simp only [VLevel.WF] at hwf
      simp [VLevel.eval, List.getD, hwf]
  | .max a b, h, hwf => by
      simp only [alwaysZeroB, Bool.and_eq_false_iff] at h
      simp only [VLevel.eval]
      have hl := Nat.le_max_left (a.eval (List.replicate n 1)) (b.eval (List.replicate n 1))
      have hr := Nat.le_max_right (a.eval (List.replicate n 1)) (b.eval (List.replicate n 1))
      intro he
      rcases h with h | h
      · exact alwaysZeroB_complete h hwf.1 (Nat.le_zero.mp (he ▸ hl))
      · exact alwaysZeroB_complete h hwf.2 (Nat.le_zero.mp (he ▸ hr))
  | .imax a b, h, hwf => by
      simp only [alwaysZeroB] at h
      have hb := alwaysZeroB_complete h hwf.2
      simp only [VLevel.eval, Lean.Nat.imax]
      rw [if_neg hb]
      have hr := Nat.le_max_right (a.eval (List.replicate n 1)) (b.eval (List.replicate n 1))
      exact fun he => hb (Nat.le_zero.mp (he ▸ hr))

/-- The decision survives translation: `VLevel.ofLevel` is a homomorphism on the four arms
`alwaysZeroB` reads, and fails outright on the `mvar` arm it does not.
`Lean4Lean.ofLevel_isNeverZero`'s twin (`Lean4Lean/Verify/Typing/Lemmas.lean:1536`). -/
theorem ofLevel_alwaysZeroB {Us : List Name} {u : Lean.Level} {u' : VLevel}
    (h : VLevel.ofLevel Us u = some u') : alwaysZeroB u' = u.isAlwaysZero := by
  induction u generalizing u' with simp [VLevel.ofLevel, bind] at h
  | zero => cases h; rfl
  | succ _ ih => obtain ⟨_, _, ⟨⟩⟩ := h; rfl
  | max _ _ ih1 ih2 =>
      obtain ⟨_, h1, _, h2, ⟨⟩⟩ := h
      simp [alwaysZeroB, Lean.Level.isAlwaysZero, ih1 h1, ih2 h2]
  | imax _ _ _ ih2 =>
      obtain ⟨_, _, _, h2, ⟨⟩⟩ := h
      simp [alwaysZeroB, Lean.Level.isAlwaysZero, ih2 h2]
  | param n => exact h.2 ▸ rfl

/-- The modelled inductive `I` is **propositional**: `env` knows it, and the result sort of
its model type evaluates to `Prop` at every valuation. The model-side reading of
`Erasure.isPropositionalArity`, and MetaRocq's `erases_one_inductive_body`
(`../metarocq/erasure/theories/Extract.v:276`).

Not the complement of `InformativeInd`: `IsNeverZero l` is `∀ ls, l.eval ls ≠ 0` and this is
`∀ ls, l.eval ls = 0`, so the two are **exclusive and jointly incomplete** — a `Sort u` family
is neither. `propositional_false_of_informative` spends the exclusion, which is the only
implication that holds. -/
def PropositionalInd (env : VEnv) (I : Name) : Prop :=
  ∃ ci, env.constants I = some ci ∧ ∃ l, vResultSort ci.type = some l ∧ ∀ ls, l.eval ls = 0

/-- Propositionality survives environment extension, as relevance does. -/
theorem PropositionalInd.mono {env env' : VEnv} {I : Name} (hle : env ≤ env')
    (h : PropositionalInd env I) : PropositionalInd env' I :=
  let ⟨ci, hci, l, hl, hz⟩ := h; ⟨ci, hle.constants hci, l, hl, hz⟩

/-- **An informative inductive is not propositional.** Spent wherever the ι and projection
arms need the emitted flag to be `false`: the registry does not assert `false` outright —
`Erasure.recursorRealizer` registers `Eq`/`And`/`False` with `propositional := true` — it
asserts MetaRocq's equation, and `false` is read off it against the consumer's own
`InformativeInd` premise. Only the soundness half of that equation is hypothesised, which is
all this argument reads and all the model side proves:
`ErasureSpec.propositionalInd_of_arity` derives it, and its converse is refuted by an arity
whose final sort sits under a `let` (`doc/rework/03-DEV-FIX.md`, F-ARITYLET). -/
theorem propositional_false_of_informative {env : VEnv} {I : Name} {p : Bool}
    (heq : p = true → PropositionalInd env I) (hinf : InformativeInd env I) : p = false := by
  cases hp : p with
  | false => rfl
  | true =>
      exfalso
      obtain ⟨ci, hci, l, hl, hz⟩ := heq hp
      obtain ⟨ci', hci', l', hl', hnz⟩ := hinf
      rw [hci] at hci'
      cases Option.some.inj hci'
      rw [hl] at hl'
      cases Option.some.inj hl'
      exact hnz [] (hz [])

end LeanToLambdaBox
