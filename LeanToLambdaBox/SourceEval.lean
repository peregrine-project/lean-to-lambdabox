import Lean4Lean.Verify.Typing.Lemmas

/-!
# The source evaluation relation

`SEval` is *the* big-step weak call-by-value evaluation of source `Lean.Expr` terms: the
operational meaning of "the source program computes to this value" in the erasure
correctness statement. One relation covers every fragment the schedule needs, because the
reductions it may use are a parameter — `SEvalFlags` — and not a choice of inductive.

Two further parameters carry the environment data a step reads:

* `env : VEnv` — lean4lean's kernel environment, read by the definitional-equality side
  conditions `StepDefeq` that the δ, ι and projection arms carry;
* `bo : Name → Option Expr` — the **compiler-body table**. δ unfolds the body the compiler
  compiles, which is the body the eraser reads, not the kernel equation; on the capstone
  path it is the reified source table's body column. `CompilerBodies` is the typing
  hypothesis that table owes.

A tabled constant is never a value (`SEval.ctorVal` requires `bo cn = none`), so δ and
the value arm do not both fire at a constant head.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-- Apply `f` to a list of source arguments, left to right:
`mkApps f [a₁, …, aₙ] = (…((f a₁) a₂)… aₙ)`. The source twin of the target's application
spine, and the shape every head-keyed rule of `SEval` matches on. -/
def mkApps (f : Expr) : List Expr → Expr
  | [] => f
  | a :: rest => mkApps (.app f a) rest

@[simp] theorem mkApps_nil (f : Expr) : mkApps f [] = f := rfl

@[simp] theorem mkApps_cons (f a : Expr) (as : List Expr) :
    mkApps f (a :: as) = mkApps (.app f a) as := rfl

theorem mkApps_append (f : Expr) (as bs : List Expr) :
    mkApps f (as ++ bs) = mkApps (mkApps f as) bs := by
  induction as generalizing f with
  | nil => rfl
  | cons x xs ih => simpa using ih (.app f x)

theorem mkApps_concat (f : Expr) (as : List Expr) (a : Expr) :
    mkApps f (as ++ [a]) = .app (mkApps f as) a := by
  simp [mkApps_append]

theorem mkApps_eq_foldl (f : Expr) (as : List Expr) : mkApps f as = as.foldl Expr.app f := by
  induction as generalizing f with
  | nil => rfl
  | cons x xs ih => simpa using ih (.app f x)

/-! ## Flags -/

/-- Which reductions a source evaluation may use. The widening axis of the schedule: a
simulation is proved at a narrow point first and transported along `SEval.mono`, with the
statement never changing. -/
structure SEvalFlags where
  /-- β: contract an application of a λ-abstraction. -/
  beta : Bool
  /-- δ: unfold a constant that the compiler-body table `bo` tables. -/
  delta : Bool
  /-- ζ: contract a `let`. -/
  zeta : Bool
  /-- ι: reduce an eliminator applied to a constructor value. -/
  iota : Bool
  /-- Projection reduction: select a field of a constructor value. -/
  proj : Bool
  /-- Unfold a `Nat`/`String` literal to its constructor form. -/
  lit : Bool
  deriving DecidableEq

/-- `fl ≤ fl'` when every reduction `fl` enables is enabled by `fl'`. -/
instance : LE SEvalFlags := ⟨fun a b =>
  (a.beta → b.beta) ∧ (a.delta → b.delta) ∧ (a.zeta → b.zeta) ∧
    (a.iota → b.iota) ∧ (a.proj → b.proj) ∧ (a.lit → b.lit)⟩

@[refl] theorem SEvalFlags.le_refl (fl : SEvalFlags) : fl ≤ fl := ⟨id, id, id, id, id, id⟩

theorem SEvalFlags.le_trans {a b c : SEvalFlags} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c :=
  ⟨h₂.1 ∘ h₁.1, h₂.2.1 ∘ h₁.2.1, h₂.2.2.1 ∘ h₁.2.2.1,
    h₂.2.2.2.1 ∘ h₁.2.2.2.1, h₂.2.2.2.2.1 ∘ h₁.2.2.2.2.1, h₂.2.2.2.2.2 ∘ h₁.2.2.2.2.2⟩

/-- δ alone: the narrowest point at which a subject-reduction statement is interesting. -/
def deltaOnly : SEvalFlags := ⟨false, true, false, false, false, false⟩

/-- Every reduction enabled — the point the capstone's observable conjunct runs at. -/
def fullFlags : SEvalFlags := ⟨true, true, true, true, true, true⟩

theorem deltaOnly_le_fullFlags : deltaOnly ≤ fullFlags := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro <;> rfl

/-! ## The definitional equality a step owes -/

/-- The definitional-equality obligation of one source reduction `e₁ ⟶ e₂`: both sides
translate, and their translations are definitionally equal in `env`.

It is stated with *both* translations existentially bound, which is what makes it usable:
a consumer stepping from `e₁` needs the reduct's translation to continue, and a form
quantified over given translations cannot supply one (`StepDefeq.uniq_form`,
`forall_form_not_stepDefeq`). -/
def StepDefeq (env : VEnv) (Us : List Name) (Δ : VLCtx) (e₁ e₂ : Expr) : Prop :=
  ∃ v₁ v₂, TrExprS env Us Δ e₁ v₁ ∧ TrExprS env Us Δ e₂ v₂ ∧
    env.IsDefEqU Us.length Δ.toCtx v₁ v₂

/-- A `StepDefeq` survives an environment extension: every component is monotone. -/
theorem StepDefeq.le {env env' : VEnv} (h : env ≤ env') {Us : List Name} {Δ : VLCtx}
    {e₁ e₂ : Expr} : StepDefeq env Us Δ e₁ e₂ → StepDefeq env' Us Δ e₁ e₂
  | ⟨v₁, v₂, h₁, h₂, hd⟩ => ⟨v₁, v₂, h₁.mono h, h₂.mono h, hd.mono h⟩

/-- `StepDefeq` entails the "for every pair of translations" side condition: type
uniqueness transports the recorded defeq to any other pair. So nothing is lost by binding
the translations existentially. -/
theorem StepDefeq.uniq_form {env : VEnv} (henv : env.WF) {Us : List Name} {Δ : VLCtx}
    (hΔ : VLCtx.WF env Us.length Δ) {e₁ e₂ : Expr} (h : StepDefeq env Us Δ e₁ e₂) :
    ∀ w₁ w₂, TrExprS env Us Δ e₁ w₁ → TrExprS env Us Δ e₂ w₂ →
      env.IsDefEqU Us.length Δ.toCtx w₁ w₂ := by
  obtain ⟨v₁, v₂, h₁, h₂, hd⟩ := h
  intro w₁ w₂ hw₁ hw₂
  have e₁u := TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) hw₁ h₁
  have e₂u := TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hΔ) h₂ hw₂
  exact VEnv.IsDefEqU.trans henv hΔ.toCtx e₁u (VEnv.IsDefEqU.trans henv hΔ.toCtx hd e₂u)

/-- Nothing translates a loose bound variable in the empty context. -/
theorem trExprS_bvar_nil_elim {env : VEnv} {Us : List Name} {w : VExpr} :
    ¬ TrExprS env Us [] (.bvar 0) w := by
  intro h
  cases h with | bvar hf => simp [VLCtx.find?] at hf

/-- …and the converse fails: the quantified form is vacuously true whenever the redex has
no translation at all, as at a loose bound variable in the empty context. -/
theorem forall_form_not_stepDefeq {env : VEnv} {Us : List Name} {e₂ : Expr} :
    (∀ w₁ w₂, TrExprS env Us [] (.bvar 0) w₁ → TrExprS env Us [] e₂ w₂ →
        env.IsDefEqU Us.length (VLCtx.toCtx []) w₁ w₂) ∧
      ¬ StepDefeq env Us [] (.bvar 0) e₂ := by
  refine ⟨fun _ _ h _ => absurd h trExprS_bvar_nil_elim, ?_⟩
  rintro ⟨_, _, h, -, -⟩
  exact trExprS_bvar_nil_elim h

/-! ## The relation -/

/-- Weak call-by-value big-step evaluation of a source `Lean.Expr`.

λ-abstractions and spines headed by a table-free constant are values; every other arm is a
reduction gated by its flag. `SEval.deltaC` unfolds the **compiler** body `bo c`, which is
the body the eraser reads. Its side condition, and those of `SEval.iota` and `SEval.proj`,
is the definitional equality the step owes (`StepDefeq`): for δ a fact about the two bodies
at the applied instance, for ι and projection the kernel's own reduction, discharged
through `VEnv.pats` and `VEnv.IsDefEq.pat`. -/
inductive SEval (env : VEnv) (bo : Name → Option Expr) (Us : List Name) (fl : SEvalFlags) :
    VLCtx → Expr → Expr → Prop
  /-- λ-abstractions are values. -/
  | lam {Δ : VLCtx} (n : Name) (ty b : Expr) (bi : BinderInfo) :
      SEval env bo Us fl Δ (.lam n ty b bi) (.lam n ty b bi)
  /-- β: the function evaluates to a λ, the argument to a value, then the substituted body. -/
  | beta {Δ f a n ty b bi av r} (hfl : fl.beta)
      (hf : SEval env bo Us fl Δ f (.lam n ty b bi))
      (ha : SEval env bo Us fl Δ a av)
      (hb : SEval env bo Us fl Δ (b.instantiate1' av 0) r) :
      SEval env bo Us fl Δ (.app f a) r
  /-- ζ: evaluate the bound value, then the substituted body. -/
  | zeta {Δ n ty v b nd vv r} (hfl : fl.zeta)
      (hv : SEval env bo Us fl Δ v vv)
      (hb : SEval env bo Us fl Δ (b.instantiate1' vv 0) r) :
      SEval env bo Us fl Δ (.letE n ty v b nd) r
  /-- δ on a **compiler** body: the arguments evaluate, the tabled body is instantiated at
      the call site's levels, and the unfolded application evaluates. `hdef` is the step's
      definitional equality at the applied instance — `rfl`-grade where the compiler body
      and the kernel body agree on constructor-headed arguments. -/
  | deltaC {Δ c us ups args argsv b b' v} (hfl : fl.delta)
      (hb : bo c = some b)
      (hinst : b' = b.instantiateLevelParams ups us)
      (hlen : argsv.length = args.length)
      (hargs : ∀ i, i < args.length → SEval env bo Us fl Δ args[i]! argsv[i]!)
      (hdef : StepDefeq env Us Δ (mkApps (.const c us) argsv) (mkApps b' argsv))
      (hcont : SEval env bo Us fl Δ (mkApps b' argsv) v) :
      SEval env bo Us fl Δ (mkApps (.const c us) args) v
  /-- A spine headed by a constant the table does not define is a value once its arguments
      are: constructors and erased axioms, the two heads δ cannot move. -/
  | ctorVal {Δ cn us args argsv} (hnb : bo cn = none)
      (hlen : argsv.length = args.length)
      (hargs : ∀ i, i < args.length → SEval env bo Us fl Δ args[i]! argsv[i]!) :
      SEval env bo Us fl Δ (mkApps (.const cn us) args) (mkApps (.const cn us) argsv)
  /-- ι: the discriminee evaluates to a constructor spine and the selected minor is applied
      to the constructor's fields, the `np` parameters dropped, as the target's ι reduct is.
      The eliminated inductive and the constructor's index are tied together by `hdef`, the
      kernel ι fact for this instance. -/
  | iota {Δ con us cus pre minors discr ctor cargs np cidx r} (hfl : fl.iota)
      (hdiscr : SEval env bo Us fl Δ discr (mkApps (.const ctor cus) cargs))
      (hidx : cidx < minors.length)
      (hdef : StepDefeq env Us Δ (mkApps (.const con us) (pre ++ discr :: minors))
        (mkApps minors[cidx]! (cargs.drop np)))
      (hcont : SEval env bo Us fl Δ (mkApps minors[cidx]! (cargs.drop np)) r) :
      SEval env bo Us fl Δ (mkApps (.const con us) (pre ++ discr :: minors)) r
  /-- Projection: the discriminee evaluates to a constructor spine and spine position
      `np + i` — `np` parameters skipped, then field `i` — evaluates. -/
  | proj {Δ S i discr ctor cus cargs np r} (hfl : fl.proj)
      (hdiscr : SEval env bo Us fl Δ discr (mkApps (.const ctor cus) cargs))
      (hlt : np + i < cargs.length)
      (hdef : StepDefeq env Us Δ (.proj S i discr) cargs[np + i]!)
      (hcont : SEval env bo Us fl Δ cargs[np + i]! r) :
      SEval env bo Us fl Δ (.proj S i discr) r
  /-- A literal evaluates by unfolding to its constructor form — the step `TrExprS.lit`
      and the eraser both take. -/
  | lit {Δ l r} (hfl : fl.lit) (h : SEval env bo Us fl Δ l.toConstructor r) :
      SEval env bo Us fl Δ (.lit l) r

/-- **Widening along the flags.** An evaluation using a subset of the reductions is an
evaluation of the wider relation, with the same value. -/
theorem SEval.mono {env : VEnv} {bo : Name → Option Expr} {Us : List Name}
    {fl fl' : SEvalFlags} (h : fl ≤ fl') {Δ : VLCtx} {e v : Expr}
    (hev : SEval env bo Us fl Δ e v) : SEval env bo Us fl' Δ e v := by
  induction hev with
  | lam n ty b bi => exact .lam n ty b bi
  | beta hfl _ _ _ ihf iha ihb => exact .beta (h.1 hfl) ihf iha ihb
  | zeta hfl _ _ ihv ihb => exact .zeta (h.2.2.1 hfl) ihv ihb
  | deltaC hfl hb hinst hlen _ hdef _ ihargs ihcont =>
      exact .deltaC (h.2.1 hfl) hb hinst hlen ihargs hdef ihcont
  | ctorVal hnb hlen _ ihargs => exact .ctorVal hnb hlen ihargs
  | iota hfl _ hidx hdef _ ihd ihc => exact .iota (h.2.2.2.1 hfl) ihd hidx hdef ihc
  | proj hfl _ hlt hdef _ ihd ihc => exact .proj (h.2.2.2.2.1 hfl) ihd hlt hdef ihc
  | lit hfl _ ih => exact .lit (h.2.2.2.2.2 hfl) ih

/-- **Stability under an environment extension.** Only the `StepDefeq` side conditions
mention `env`, and each is monotone. -/
theorem SEval.le {env env' : VEnv} (h : env ≤ env') {bo : Name → Option Expr}
    {Us : List Name} {fl : SEvalFlags} {Δ : VLCtx} {e v : Expr}
    (hev : SEval env bo Us fl Δ e v) : SEval env' bo Us fl Δ e v := by
  induction hev with
  | lam n ty b bi => exact .lam n ty b bi
  | beta hfl _ _ _ ihf iha ihb => exact .beta hfl ihf iha ihb
  | zeta hfl _ _ ihv ihb => exact .zeta hfl ihv ihb
  | deltaC hfl hb hinst hlen _ hdef _ ihargs ihcont =>
      exact .deltaC hfl hb hinst hlen ihargs (hdef.le h) ihcont
  | ctorVal hnb hlen _ ihargs => exact .ctorVal hnb hlen ihargs
  | iota hfl _ hidx hdef _ ihd ihc => exact .iota hfl ihd hidx (hdef.le h) ihc
  | proj hfl _ hlt hdef _ ihd ihc => exact .proj hfl ihd hlt (hdef.le h) ihc
  | lit hfl _ ih => exact .lit hfl ih

/-! ## The compiler-body table's typing hypothesis -/

/-- **Every tabled compiler body is kernel-typeable at the declared type.**

The hypothesis the compiler-body table owes: for each constant `c` the table defines, `c`
is declared in `lenv`, and the tabled body translates and has the translation of `c`'s
declared type, both at `c`'s own level scope and in the empty context. Checkable per
program by running lean4lean's checker on the pair. -/
def CompilerBodies (lenv : Lean.Environment) (env : VEnv) (bo : Name → Option Expr) : Prop :=
  ∀ c b, bo c = some b → ∃ ci, lenv.find? c = some ci ∧
    ∃ vb vty, TrExprS env ci.levelParams [] b vb ∧
      TrExprS env ci.levelParams [] ci.type vty ∧
      env.HasType ci.levelParams.length [] vb vty

/-- `CompilerBodies` survives an environment extension. -/
theorem CompilerBodies.le {lenv : Lean.Environment} {env env' : VEnv} (h : env ≤ env')
    {bo : Name → Option Expr} (hcb : CompilerBodies lenv env bo) :
    CompilerBodies lenv env' bo := by
  intro c b hbo
  obtain ⟨ci, hci, vb, vty, hb, hty, hwt⟩ := hcb c b hbo
  exact ⟨ci, hci, vb, vty, hb.mono h, hty.mono h, hwt.mono h⟩


/-! ## A `SEval.deltaC` witness

A four-constant environment — a base type `N`, a value `z : N`, and two binary operations
whose defining equations are registered — with a compiler body tabled for each. It exhibits
the δ arm at `deltaOnly` and at the applied instance, and shows what discharges the arm's
side condition: the environment's own defining equations. `add`'s tabled body is its kernel
body, the `rfl`-grade case; `sel`'s is not, and the side condition holds there because it is
asked at the applied instance. -/

namespace DeltaWitness

/-- The base type, as a `VExpr`. -/
def natTy : VExpr := .const `N []

/-- The base type, as a source `Expr`. -/
def natSrc : Expr := .const `N []

/-- `add`'s declared type, `N → N → N`. -/
def addTy : VExpr := .forallE natTy (.forallE natTy natTy)

/-- `add`'s body: the projection onto the first argument. -/
def addBodySrc : Expr :=
  .lam `a natSrc (.lam `b natSrc (.bvar 1) .default) .default

/-- The translation of `addBodySrc`. -/
def addBody : VExpr := .lam natTy (.lam natTy (.bvar 1))

/-- `sel`'s **compiler** body: the projection onto the second argument. Its kernel body is
`addBody`, a different term, and the two agree only where the arguments do. -/
def selBodySrc : Expr :=
  .lam `a natSrc (.lam `b natSrc (.bvar 0) .default) .default

/-- The translation of `selBodySrc`. -/
def selBody : VExpr := .lam natTy (.lam natTy (.bvar 0))

/-- The compiler body of `sel` is not its kernel body. -/
theorem selBody_ne_addBody : selBody ≠ addBody := by simp [selBody, addBody]

/-- `add`'s defining equation, as the environment registers it. -/
def addDefEq : VDefEq := ⟨0, .const `add [], addBody, addTy⟩

/-- `sel`'s defining equation: the *kernel* body, which is `add`'s. -/
def selDefEq : VDefEq := ⟨0, .const `sel [], addBody, addTy⟩

/-- The witness environment: four constants and two defining equations. -/
def env : VEnv where
  constants n :=
    if n = `N then some ⟨0, .sort (.succ .zero)⟩
    else if n = `z then some ⟨0, natTy⟩
    else if n = `add then some ⟨0, addTy⟩
    else if n = `sel then some ⟨0, addTy⟩
    else none
  defeqs df := df = addDefEq ∨ df = selDefEq
  pats _ _ := False

/-- The compiler-body table: `add`, whose tabled body is its kernel body, and `sel`, whose
tabled body is not. -/
def bo : Name → Option Expr := fun n =>
  if n = `add then some addBodySrc else if n = `sel then some selBodySrc else none

theorem constants_N : env.constants `N = some ⟨0, .sort (.succ .zero)⟩ := rfl

theorem constants_z : env.constants `z = some ⟨0, natTy⟩ := rfl

theorem constants_add : env.constants `add = some ⟨0, addTy⟩ := rfl

theorem constants_sel : env.constants `sel = some ⟨0, addTy⟩ := rfl

theorem hasType_natTy {Γ : List VExpr} : env.HasType 0 Γ natTy (.sort (.succ .zero)) :=
  .constDF constants_N (by simp) (by simp) rfl .nil

theorem isType_natTy {Γ : List VExpr} : env.IsType 0 Γ natTy := ⟨_, hasType_natTy⟩

theorem hasType_z {Γ : List VExpr} : env.HasType 0 Γ (.const `z []) natTy :=
  .constDF constants_z (by simp) (by simp) rfl .nil

theorem hasType_add {Γ : List VExpr} : env.HasType 0 Γ (.const `add []) addTy :=
  .constDF constants_add (by simp) (by simp) rfl .nil

theorem trExprS_natSrc {Δ : VLCtx} : TrExprS env [] Δ natSrc natTy :=
  .const constants_N rfl rfl

theorem trExprS_z {Δ : VLCtx} : TrExprS env [] Δ (.const `z []) (.const `z []) :=
  .const constants_z rfl rfl

theorem trExprS_add {Δ : VLCtx} : TrExprS env [] Δ (.const `add []) (.const `add []) :=
  .const constants_add rfl rfl

theorem trExprS_addBody {Δ : VLCtx} : TrExprS env [] Δ addBodySrc addBody :=
  .lam isType_natTy trExprS_natSrc
    (.lam isType_natTy trExprS_natSrc (.bvar rfl))

/-- The environment's defining equation, at the empty level instantiation. -/
theorem isDefEq_add {Γ : List VExpr} : env.IsDefEq 0 Γ (.const `add []) addBody addTy :=
  .extra (df := addDefEq) (ls := []) (.inl rfl) (by simp) rfl

theorem hasType_addBody {Γ : List VExpr} : env.HasType 0 Γ addBody addTy :=
  isDefEq_add.hasType.2

/-- **One tabled unfolding at `deltaOnly`.** The δ arm fires on the bare constant; its side
condition is the environment's own defining equation. -/
theorem seval_add_deltaOnly :
    SEval env bo [] deltaOnly [] (.const `add []) addBodySrc := by
  refine .deltaC (b := addBodySrc) (b' := addBodySrc) (ups := []) (args := []) (argsv := [])
    rfl rfl rfl rfl (fun i hi => absurd hi (by simp))
    ⟨_, _, trExprS_add, trExprS_addBody, ⟨_, isDefEq_add⟩⟩ ?_
  exact .lam ..

/-- Flags enabling β and δ, the point at which the applied instance computes. -/
def betaDelta : SEvalFlags := ⟨true, true, false, false, false, false⟩

/-- `z` evaluates to itself: a constant the table does not define, applied to nothing. -/
theorem seval_z {fl : SEvalFlags} : SEval env bo [] fl [] (.const `z []) (.const `z []) := by
  have := SEval.ctorVal (env := env) (bo := bo) (Us := []) (fl := fl) (Δ := [])
    (cn := `z) (us := []) (args := []) (argsv := []) rfl rfl
    (fun i hi => absurd hi (by simp))
  simpa using this

theorem hasType_add_z {Γ : List VExpr} :
    env.HasType 0 Γ (.app (.const `add []) (.const `z [])) (.forallE natTy natTy) :=
  .appDF hasType_add hasType_z

theorem hasType_addBody_z {Γ : List VExpr} :
    env.HasType 0 Γ (.app addBody (.const `z [])) (.forallE natTy natTy) :=
  .appDF hasType_addBody hasType_z

/-- The applied redex translates. -/
theorem trExprS_add_applied :
    TrExprS env [] [] (mkApps (.const `add []) [.const `z [], .const `z []])
      (.app (.app (.const `add []) (.const `z [])) (.const `z [])) :=
  .app hasType_add_z hasType_z (.app hasType_add hasType_z trExprS_add trExprS_z) trExprS_z

/-- The applied reduct translates. -/
theorem trExprS_addBody_applied :
    TrExprS env [] [] (mkApps addBodySrc [.const `z [], .const `z []])
      (.app (.app addBody (.const `z [])) (.const `z [])) :=
  .app hasType_addBody_z hasType_z
    (.app hasType_addBody hasType_z trExprS_addBody trExprS_z) trExprS_z

/-- **The applied instance.** `add z z` unfolds the tabled body once and β-reduces to `z`:
the `add 0 0` shape, with the arm's side condition stated at the evaluated arguments and
discharged from the environment's defining equation. -/
theorem seval_add_applied :
    SEval env bo [] betaDelta [] (mkApps (.const `add []) [.const `z [], .const `z []])
      (.const `z []) := by
  have hargs : ∀ i, i < [Expr.const `z [], Expr.const `z []].length →
      SEval env bo [] betaDelta [] [Expr.const `z [], Expr.const `z []][i]!
        [Expr.const `z [], Expr.const `z []][i]! := by
    intro i hi
    match i, hi with
    | 0, _ => simpa using seval_z
    | 1, _ => simpa using seval_z
  refine .deltaC (b := addBodySrc) (b' := addBodySrc) (ups := []) rfl rfl rfl rfl hargs
    ⟨_, _, trExprS_add_applied, trExprS_addBody_applied, ?_⟩ ?_
  · exact ⟨_, .appDF (.appDF isDefEq_add hasType_z) hasType_z⟩
  · exact .beta rfl (.beta rfl (.lam ..) seval_z (.lam ..)) seval_z seval_z

/-! ### A tabled body that is not the kernel body

`sel`'s compiler body and kernel body are different terms — the situation of every
declaration erased from a compiler body. The arm's side condition is still inhabited,
because it is asked at the *applied* instance, where both bodies reach the same value. -/

theorem hasType_sel {Γ : List VExpr} : env.HasType 0 Γ (.const `sel []) addTy :=
  .constDF constants_sel (by simp) (by simp) rfl .nil

theorem isDefEq_sel {Γ : List VExpr} : env.IsDefEq 0 Γ (.const `sel []) addBody addTy :=
  .extra (df := selDefEq) (ls := []) (.inr rfl) (by simp) rfl

theorem trExprS_sel {Δ : VLCtx} : TrExprS env [] Δ (.const `sel []) (.const `sel []) :=
  .const constants_sel rfl rfl

theorem hasType_selBody {Γ : List VExpr} : env.HasType 0 Γ selBody addTy :=
  .lam hasType_natTy (.lam hasType_natTy (.bvar .zero))

theorem trExprS_selBody {Δ : VLCtx} : TrExprS env [] Δ selBodySrc selBody :=
  .lam isType_natTy trExprS_natSrc
    (.lam isType_natTy trExprS_natSrc (.bvar rfl))

/-- Both arguments are `z`, so a binary λ-body that selects either of them reaches `z`. -/
theorem applied_to_z {inner r : VExpr}
    (hinner : env.HasType 0 [natTy] inner (.forallE natTy natTy))
    (hr : env.HasType 0 [natTy] r natTy)
    (heq : inner.inst (.const `z []) = .lam natTy r)
    (heq₂ : r.inst (.const `z []) = .const `z []) :
    env.IsDefEq 0 [] (.app (.app (.lam natTy inner) (.const `z [])) (.const `z []))
      (.const `z []) natTy := by
  have b₁ : env.IsDefEq 0 [] (.app (.lam natTy inner) (.const `z []))
      (.lam natTy r) (.forallE natTy natTy) := by
    have := VEnv.IsDefEq.beta hinner (hasType_z (Γ := []))
    rwa [heq] at this
  have b₂ : env.IsDefEq 0 [] (.app (.lam natTy r) (.const `z [])) (.const `z []) natTy := by
    have := VEnv.IsDefEq.beta hr (hasType_z (Γ := []))
    rwa [heq₂] at this
  exact .trans (.appDF b₁ hasType_z) b₂

theorem addBody_applied_to_z :
    env.IsDefEq 0 [] (.app (.app addBody (.const `z [])) (.const `z [])) (.const `z [])
      natTy :=
  applied_to_z (r := .const `z []) (.lam hasType_natTy (.bvar (.succ .zero))) hasType_z
    rfl rfl

theorem selBody_applied_to_z :
    env.IsDefEq 0 [] (.app (.app selBody (.const `z [])) (.const `z [])) (.const `z [])
      natTy :=
  applied_to_z (r := .bvar 0) (.lam hasType_natTy (.bvar .zero)) (.bvar .zero) rfl rfl

theorem trExprS_sel_applied :
    TrExprS env [] [] (mkApps (.const `sel []) [.const `z [], .const `z []])
      (.app (.app (.const `sel []) (.const `z [])) (.const `z [])) :=
  .app (.appDF hasType_sel hasType_z) hasType_z
    (.app hasType_sel hasType_z trExprS_sel trExprS_z) trExprS_z

theorem trExprS_selBody_applied :
    TrExprS env [] [] (mkApps selBodySrc [.const `z [], .const `z []])
      (.app (.app selBody (.const `z [])) (.const `z [])) :=
  .app (.appDF hasType_selBody hasType_z) hasType_z
    (.app hasType_selBody hasType_z trExprS_selBody trExprS_z) trExprS_z

/-- **The applied instance at a mismatched body.** `sel z z` unfolds a tabled body its
kernel declaration does not have, and the arm's side condition still holds: both bodies
compute to `z` at these arguments. -/
theorem seval_sel_applied :
    SEval env bo [] betaDelta [] (mkApps (.const `sel []) [.const `z [], .const `z []])
      (.const `z []) := by
  have hargs : ∀ i, i < [Expr.const `z [], Expr.const `z []].length →
      SEval env bo [] betaDelta [] [Expr.const `z [], Expr.const `z []][i]!
        [Expr.const `z [], Expr.const `z []][i]! := by
    intro i hi
    match i, hi with
    | 0, _ => simpa using seval_z
    | 1, _ => simpa using seval_z
  refine .deltaC (b := selBodySrc) (b' := selBodySrc) (ups := []) rfl rfl rfl rfl hargs
    ⟨_, _, trExprS_sel_applied, trExprS_selBody_applied, ?_⟩ ?_
  · exact ⟨_, .trans (.trans (.appDF (.appDF isDefEq_sel hasType_z) hasType_z)
      addBody_applied_to_z) (.symm selBody_applied_to_z)⟩
  · exact .beta rfl (.beta rfl (.lam ..) seval_z (.lam ..)) seval_z seval_z

end DeltaWitness

end LeanToLambdaBox
