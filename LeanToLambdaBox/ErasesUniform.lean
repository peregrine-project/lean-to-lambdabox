import LeanToLambdaBox.ErasesStrengthen

/-!
# Context uniformity for `Erases`

The two-sided transport `Δ → [] → Δ'`: an erasure derivation produced at one `VLCtx` holds
at any other, for a closed, fvar-free source with an `LBClosed` target.

The weakening leg `[] → Δ'` is `erases_weak_any` and costs nothing. This file supplies the
strengthening leg `Δ → []` and the composition. Strengthening is not free: it needs an
inverse of `Erasable.weakN`, carried as the named premise `ErasableStrengthen`, and a
source-side scope condition.

The route is not lean4lean's `TrExprS.weakFV_inv`, which recovers a small-context
translation only up to definitional equality. That is survivable in the `box` arm and fatal
in `lam`, where the body's induction hypothesis demands the *equation*
`ty' = ty'₀.liftN n k`. Instead the small-context translation is **assumed** (`hwt`), pushed
outwards by `TrExprS.weakFV_fvwf`, and identified with the derivation's witness by
lean4lean's equational `TrExprS.unique` — which is gated on projection-freeness.

Hence two strengthening inductions. `Erases.strengthen_fvlift` runs at `NoProj` and stays
free of the projection uniqueness gap; `Erases.strengthen_fvlift_binders` runs at
`NoProjBinders`, which admits projections in computational position, and pays for the `box`
arm with `TrExprS.uniq` and `Erasable.defeq`. Equational uniqueness at `.proj` is false, not
merely unproved — `TrProj` pins parameters only up to definitional equality — so the binder
clauses of `NoProjBinders` cannot be dropped.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-! ## The commissioned `VExpr`-level obligation -/

/--
An inverse of `Erasable.weakN`: erasability of `ve.liftN n k` in a larger context implies
erasability of `ve` in the smaller one.

`Erasable` ships with `weakN`, `inst`, `defeq` and `defeqDFC` and with no inverse of
`weakN`, and the pinned lean4lean has none for its `VEnv.HasType` either: the only inverse,
`VEnv.IsDefEqU.weakN_iff`, is `sorry` in its forward direction. The obligation is named as a
premise rather than assumed as an axiom; its hard half is the `IsArityUpTo` disjunct, which
needs a `forallE` inversion through a lift.
-/
def ErasableStrengthen (env : VEnv) (Us : List Name) : Prop :=
  ∀ {Γ₀ Γ₁ : List VExpr} {ve : VExpr} {n k : Nat},
    Ctx.LiftN n k Γ₀ Γ₁ → Erasable env Us.length Γ₁ (ve.liftN n k) →
    Erasable env Us.length Γ₀ ve

/-- A `Ctx.LiftN` that lifts by `0` is the identity on contexts. -/
protected theorem Ctx.LiftN.zero_eq :
    ∀ {k : Nat} {Γ₀ Γ₁ : List VExpr}, Ctx.LiftN 0 k Γ₀ Γ₁ → Γ₀ = Γ₁
  | _, _, _, .zero As h => by cases List.eq_nil_of_length_eq_zero h; simp
  | _, _, _, .succ W => by rw [Ctx.LiftN.zero_eq W]; simp

/-- `ErasableStrengthen` is not vacuously false: at every zero lift it holds, and holds as
the identity. This pins the quantifier structure of the named premise. -/
theorem erasableStrengthen_liftN_zero {env : VEnv} {U : Nat} {Γ₀ Γ₁ : List VExpr}
    {ve : VExpr} {k : Nat} (W : Ctx.LiftN 0 k Γ₀ Γ₁)
    (h : Erasable env U Γ₁ (ve.liftN 0 k)) : Erasable env U Γ₀ ve := by
  cases Ctx.LiftN.zero_eq W; simpa using h

/-! ## The source-side scope conditions -/

/--
Projection-freeness of a source `Lean.Expr` at every subterm, including a `let`-binder's
type annotation. Strictly stronger than lean4lean's `TrExprS.IsUnique`, which omits the
`letE` type because the translation of a `let` does not depend on it — but `Erases.letE`
records that type in the body's context entry, so the strengthening has to pin it.
-/
def NoProj : Expr → Prop
  | .bvar _ | .fvar _ | .sort _ | .const .. | .mvar .. | .lit _ => True
  | .app f a => NoProj f ∧ NoProj a
  | .lam _ t b _ => NoProj t ∧ NoProj b
  | .forallE _ t b _ => NoProj t ∧ NoProj b
  | .letE _ t v b _ => NoProj t ∧ NoProj v ∧ NoProj b
  | .mdata _ e => NoProj e
  | .proj .. => False

/-- `NoProj` implies lean4lean's `TrExprS.IsUnique`, which is what `TrExprS.unique`
consumes. -/
theorem NoProj.toIsUnique : ∀ {e : Expr}, NoProj e → TrExprS.IsUnique e
  | .bvar _, _ | .fvar _, _ | .sort _, _ | .const .., _ | .mvar .., _ | .lit _, _ => ⟨⟩
  | .app .., h => ⟨h.1.toIsUnique, h.2.toIsUnique⟩
  | .lam .., h => ⟨h.1.toIsUnique, h.2.toIsUnique⟩
  | .forallE .., h => ⟨h.1.toIsUnique, h.2.toIsUnique⟩
  | .letE .., h => ⟨h.2.1.toIsUnique, h.2.2.toIsUnique⟩
  | .mdata _ e, h => NoProj.toIsUnique (e := e) h
  | .proj .., h => h.elim

/-- The peano unfolding of a `Nat` literal is projection-free. -/
theorem NoProj.natLitToConstructor : ∀ {n : Nat}, NoProj (.natLitToConstructor n)
  | 0 => ⟨⟩
  | _ + 1 => ⟨⟨⟩, ⟨⟩⟩

/-- The `List Char` unfolding of a string literal is projection-free. -/
theorem NoProj.strLitToConstructor {s : String} : NoProj (.strLitToConstructor s) := by
  refine ⟨⟨⟩, ?_⟩
  induction s.toList with simp
  | nil => exact ⟨⟨⟩, ⟨⟩⟩
  | cons _ _ ih => exact ⟨⟨⟨⟨⟩, ⟨⟩⟩, ⟨⟨⟩, ⟨⟩⟩⟩, ih⟩

/-- Every literal's one-step constructor unfolding is projection-free, which is what the
`lit` arms' induction hypothesis needs. -/
theorem NoProj.toConstructor : ∀ {l : Literal}, NoProj l.toConstructor
  | .natVal _ => .natLitToConstructor
  | .strVal _ => .strLitToConstructor

/--
Projection-freeness at the positions the strengthening spends uniqueness on: a λ or ∀
binder's type, and a `let`'s type and bound value. Projections are permitted everywhere
computational — λ and `let` bodies, application heads and arguments, and under a
projection.

These are exactly the three positions at which `Erases` records a `VExpr` witness that a
`VLCtx.FVLift` must match on the nose.
-/
def NoProjBinders : Expr → Prop
  | .bvar _ | .fvar _ | .sort _ | .const .. | .mvar .. | .lit _ => True
  | .app f a => NoProjBinders f ∧ NoProjBinders a
  | .lam _ t b _ => NoProj t ∧ NoProjBinders b
  | .forallE _ t b _ => NoProj t ∧ NoProjBinders b
  | .letE _ t v b _ => NoProj t ∧ NoProj v ∧ NoProjBinders b
  | .mdata _ e => NoProjBinders e
  | .proj _ _ e => NoProjBinders e

/-- The weakening, so that every `NoProj` producer discharges the weaker predicate too. -/
theorem NoProj.toNoProjBinders : ∀ {e : Expr}, NoProj e → NoProjBinders e
  | .bvar _, _ | .fvar _, _ | .sort _, _ | .const .., _ | .mvar .., _ | .lit _, _ => ⟨⟩
  | .app .., h => ⟨h.1.toNoProjBinders, h.2.toNoProjBinders⟩
  | .lam .., h => ⟨h.1, h.2.toNoProjBinders⟩
  | .forallE .., h => ⟨h.1, h.2.toNoProjBinders⟩
  | .letE .., h => ⟨h.1, h.2.1, h.2.2.toNoProjBinders⟩
  | .mdata _ e, h => NoProj.toNoProjBinders (e := e) h
  | .proj .., h => h.elim

/-- Every literal's one-step constructor unfolding satisfies the weaker predicate too. -/
theorem NoProjBinders.toConstructor {l : Literal} : NoProjBinders l.toConstructor :=
  NoProj.toConstructor.toNoProjBinders

/-- `fun (α : Type) (x : Nat) (self : OfNat α x) => self.1` — a class method's prepared
body, as a source `Expr`. -/
def ofNatBody : Expr :=
  .lam `α (.sort (.succ .zero))
    (.lam `x (.const `Nat [])
      (.lam `self (.app (.app (.const `OfNat []) (.bvar 1)) (.bvar 0))
        (.proj `OfNat 0 (.bvar 0)) .instImplicit)
      .default)
    .implicit

/-- The class method's body satisfies the weakened predicate: its three binder types are
projection-free and its projection sits in the body. -/
theorem noProjBinders_ofNatBody : NoProjBinders ofNatBody :=
  ⟨⟨⟩, ⟨⟩, ⟨⟨⟨⟩, ⟨⟩⟩, ⟨⟩⟩, ⟨⟩⟩

/-- …and fails `NoProj`, at the projection in its body. This is what the relaxation
buys. -/
theorem noProj_ofNatBody_refuted : ¬ NoProj ofNatBody := fun h => h.2.2.2

/-! ## Strengthening along an `FVLift` -/

/--
Strengthening for `Erases`, at depth: a derivation at an fvar-extension `Δ'` of `Δ` also
holds at `Δ`, provided the source is projection-free and already translatable at `Δ`.

`hwt` is the engine: pushed out to `Δ'` by `TrExprS.weakFV_fvwf` and identified with the
derivation's witness by `TrExprS.unique`, it turns every `TrExprS`-bearing arm into a
rewrite. It also supplies the lookup premises of `Erases.bvar` and `Erases.fvar` at the
small context, which weakening got for free and strengthening cannot. `hstr` is spent
exactly once, in `box`. The `proj` arm is unreachable at `NoProj`.
-/
theorem Erases.strengthen_fvlift {env : VEnv} (henv : env.Ordered) {Us : List Name}
    (hstr : ErasableStrengthen env Us)
    {Δ' : VLCtx} {e : Expr} {t : LBTerm} (h : Erases env Us Δ' e t) :
    ∀ {Δ : VLCtx} {dk n k : Nat} {ve : VExpr}, VLCtx.FVLift Δ Δ' dk n k → Δ'.FVWF →
      NoProj e → TrExprS env Us Δ e ve → Erases env Us Δ e t := by
  induction h with
  | box htr her =>
    intro _ _ _ _ _ W hΔ' hnp hwt
    cases TrExprS.unique hnp.toIsUnique htr (TrExprS.weakFV_fvwf henv W hΔ' hwt)
    exact .box hwt (hstr W.toCtx her)
  | lit hcl _ ih =>
    intro _ _ _ _ _ W hΔ' _ hwt
    cases hwt with
    | lit _ h2 => exact .lit hcl (ih W hΔ' NoProj.toConstructor h2)
  | proj _ _ _ _ => intro _ _ _ _ _ _ _ hnp _; exact hnp.elim
  | bvar _ =>
    intro _ _ _ _ _ _ _ _ hwt
    cases hwt with | bvar h => exact .bvar h
  | fvar _ =>
    intro _ _ _ _ _ _ _ _ hwt
    cases hwt with | fvar h => exact .fvar h
  | ctor hc hi => intro _ _ _ _ _ _ _ _ _; exact .ctor hc hi
  | const hc ho => intro _ _ _ _ _ _ _ _ _; exact .const hc ho
  | app _ _ ihf iha =>
    intro _ _ _ _ _ W hΔ' hnp hwt
    cases hwt with
    | app _ _ hf ha => exact .app (ihf W hΔ' hnp.1 hf) (iha W hΔ' hnp.2 ha)
  | lam hty _ ihb =>
    intro _ _ _ _ _ W hΔ' hnp hwt
    cases hwt with
    | lam _ hty₀ hb₀ =>
      cases TrExprS.unique hnp.1.toIsUnique hty (TrExprS.weakFV_fvwf henv W hΔ' hty₀)
      exact .lam hty₀ (ihb (W.cons_bvar (.vlam _)) ⟨hΔ', nofun⟩ hnp.2 hb₀)
  | letE hty hval _ _ ihv ihb =>
    intro _ _ _ _ _ W hΔ' hnp hwt
    cases hwt with
    | letE _ hty₀ hval₀ hb₀ =>
      cases TrExprS.unique hnp.1.toIsUnique hty (TrExprS.weakFV_fvwf henv W hΔ' hty₀)
      cases TrExprS.unique hnp.2.1.toIsUnique hval (TrExprS.weakFV_fvwf henv W hΔ' hval₀)
      exact .letE hty₀ hval₀ (ihv W hΔ' hnp.2.1 hval₀)
        (ihb (W.cons_bvar (.vlet ..)) ⟨hΔ', nofun⟩ hnp.2.2 hb₀)
  | mdata _ ih =>
    intro _ _ _ _ _ W hΔ' hnp hwt
    cases hwt with
    | mdata hb => exact .mdata (ih W hΔ' hnp hb)

/--
Strengthening with projections allowed: the same statement at `NoProjBinders`.

Three premises move, each forced by the `box` arm, which now spends `TrExprS.uniq` and
`Erasable.defeq` instead of the equational `TrExprS.unique`. `Δ'.FVWF` becomes
`VLCtx.WF env Us.length Δ'` and `env.Ordered` becomes `env.WF`, both of which the two
consume. The induction can carry `VLCtx.WF` because `hwt`'s `TrExprS.lam` and `TrExprS.letE`
record the binder's `IsType`/`HasType`.
-/
theorem Erases.strengthen_fvlift_binders {env : VEnv} (henv : env.WF) {Us : List Name}
    (hstr : ErasableStrengthen env Us)
    {Δ' : VLCtx} {e : Expr} {t : LBTerm} (h : Erases env Us Δ' e t) :
    ∀ {Δ : VLCtx} {dk n k : Nat} {ve : VExpr}, VLCtx.FVLift Δ Δ' dk n k →
      VLCtx.WF env Us.length Δ' →
      NoProjBinders e → TrExprS env Us Δ e ve → Erases env Us Δ e t := by
  induction h with
  | box htr her =>
    intro _ _ _ _ _ W hΔ' _ hwt
    refine .box hwt (hstr W.toCtx (her.defeq henv hΔ'.toCtx ?_))
    exact TrExprS.uniq henv (.refl henv.ordered hΔ') htr
      (TrExprS.weakFV_fvwf henv.ordered W hΔ'.fvwf hwt)
  | lit hcl _ ih =>
    intro _ _ _ _ _ W hΔ' _ hwt
    cases hwt with
    | lit _ h2 => exact .lit hcl (ih W hΔ' NoProjBinders.toConstructor h2)
  | proj hs hi _ ih =>
    intro _ _ _ _ _ W hΔ' hnp hwt
    cases hwt with
    | proj hd _ => exact .proj hs hi (ih W hΔ' hnp hd)
  | bvar _ =>
    intro _ _ _ _ _ _ _ _ hwt
    cases hwt with | bvar h => exact .bvar h
  | fvar _ =>
    intro _ _ _ _ _ _ _ _ hwt
    cases hwt with | fvar h => exact .fvar h
  | ctor hc hi => intro _ _ _ _ _ _ _ _ _; exact .ctor hc hi
  | const hc ho => intro _ _ _ _ _ _ _ _ _; exact .const hc ho
  | app _ _ ihf iha =>
    intro _ _ _ _ _ W hΔ' hnp hwt
    cases hwt with
    | app _ _ hf ha => exact .app (ihf W hΔ' hnp.1 hf) (iha W hΔ' hnp.2 ha)
  | lam hty _ ihb =>
    intro _ _ _ _ _ W hΔ' hnp hwt
    cases hwt with
    | lam hty₀ty hty₀ hb₀ =>
      cases TrExprS.unique hnp.1.toIsUnique hty
        (TrExprS.weakFV_fvwf henv.ordered W hΔ'.fvwf hty₀)
      exact .lam hty₀ (ihb (W.cons_bvar (.vlam _))
        ⟨hΔ', nofun, hty₀ty.weakN henv.ordered W.toCtx⟩ hnp.2 hb₀)
  | letE hty hval _ _ ihv ihb =>
    intro _ _ _ _ _ W hΔ' hnp hwt
    cases hwt with
    | letE hval₀ty hty₀ hval₀ hb₀ =>
      cases TrExprS.unique hnp.1.toIsUnique hty
        (TrExprS.weakFV_fvwf henv.ordered W hΔ'.fvwf hty₀)
      cases TrExprS.unique hnp.2.1.toIsUnique hval
        (TrExprS.weakFV_fvwf henv.ordered W hΔ'.fvwf hval₀)
      exact .letE hty₀ hval₀ (ihv W hΔ' hnp.2.1.toNoProjBinders hval₀)
        (ihb (W.cons_bvar (.vlet ..))
          ⟨hΔ', nofun, hval₀ty.weakN henv.ordered W.toCtx⟩ hnp.2.2 hb₀)
  | mdata _ ih =>
    intro _ _ _ _ _ W hΔ' hnp hwt
    cases hwt with
    | mdata hb => exact .mdata (ih W hΔ' hnp hb)

/--
Strengthening to the empty context.

`W : VLCtx.FVLift [] Δ 0 n k` is the only shape available: `VLCtx.FVLift.cons_bvar` needs a
bvar entry on both sides, so a lift out of `[]` uses only `refl` and `skip_fvar`. That is
the eraser's situation — a top-level body is erased under a context of opened fvars.
Closedness and fvar-freeness of `e` are consequences of `hwt`, not premises.
-/
theorem erases_strengthen_closed {env : VEnv} (henv : env.WF) {Us : List Name}
    (hstr : ErasableStrengthen env Us)
    {Δ : VLCtx} {n k : Nat} (W : VLCtx.FVLift [] Δ 0 n k)
    (hΔ : VLCtx.WF env Us.length Δ)
    {e : Expr} {t : LBTerm} {ve : VExpr}
    (hnp : NoProjBinders e) (hwt : TrExprS env Us [] e ve)
    (h : Erases env Us Δ e t) :
    Erases env Us [] e t :=
  h.strengthen_fvlift_binders henv hstr W hΔ hnp hwt

/-! ## The two-sided composition -/

/--
Context uniformity for a closed, fvar-free source whose binders are projection-free: the
erasure of a constant body does not depend on the `VLCtx` it was produced at.

The route is `Δ → [] → Δ'`, by `erases_strengthen_closed` and then `erases_weak_any`. The
second leg is `erases_weak_any` rather than `erases_weakFV` because `Δ'` is arbitrary — bvar
entries and shadowing fvar entries included — which is what breaks `Δ'.FVWF`.
-/
theorem erases_uniform_closed {env : VEnv} (henv : env.WF) {Us : List Name}
    (hstr : ErasableStrengthen env Us)
    {Δ : VLCtx} {n k : Nat}
    (W : VLCtx.FVLift [] Δ 0 n k) (hΔ : VLCtx.WF env Us.length Δ)
    {e : Expr} {t : LBTerm} {ve : VExpr}
    (hnp : NoProjBinders e) (hwt : TrExprS env Us [] e ve) (hlb : LBClosed t 0)
    (h : Erases env Us Δ e t) (Δ' : VLCtx) : Erases env Us Δ' e t :=
  erases_weak_any henv.ordered hwt.closed
    (hwt.fvarsIn.mono fun _ h => (by simp at h : False))
    hlb (erases_strengthen_closed henv hstr W hΔ hnp hwt h) Δ'

/-- The one-sided corollary at `Δ = []`, which needs no `ErasableStrengthen`: only the
two-sided transport, which must also come back down from the call site's context, buys the
commissioned obligation. -/
theorem erases_uniform_of_nil {env : VEnv} (henv : env.Ordered) {Us : List Name}
    {e : Expr} {t : LBTerm}
    (hcl : Closed e 0) (hfvf : FVarsIn (fun _ => False) e) (hlb : LBClosed t 0)
    (h : Erases env Us [] e t) (Δ' : VLCtx) : Erases env Us Δ' e t :=
  erases_weak_any henv hcl hfvf hlb h Δ'

/-- Strengthening fires: a λ derivation produced at a one-fvar context is transported back
to the empty one. The `VLCtx.WF` and the small-context translation are constructed. -/
example (env : VEnv) (henv : env.WF) (Us : List Name)
    (hstr : ErasableStrengthen env Us)
    (x : FVarId) (A : VExpr) (hA : env.IsType Us.length [] A)
    (nm : Name) (bi : BinderInfo)
    (H : Erases env Us [(some (x, []), .vlam A)]
      (.lam nm (.sort .zero) (.bvar 0) bi) (.lambda (.named nm.toString) (.bvar 0))) :
    Erases env Us [] (.lam nm (.sort .zero) (.bvar 0) bi)
      (.lambda (.named nm.toString) (.bvar 0)) :=
  have hΔ : VLCtx.WF env Us.length [(some (x, []), .vlam A)] :=
    ⟨trivial, by rintro _ _ ⟨⟩; simp, hA⟩
  have hwt : TrExprS env Us [] (.lam nm (.sort .zero) (.bvar 0) bi)
      (.lam (.sort .zero) (.bvar 0)) :=
    .lam ⟨_, .sort trivial⟩ (.sort rfl) (.bvar rfl)
  have hnp : NoProjBinders (.lam nm (.sort .zero) (.bvar 0) bi) := ⟨trivial, trivial⟩
  erases_strengthen_closed henv hstr (VLCtx.FVLift.from_nil rfl) hΔ hnp hwt H

end LeanToLambdaBox
