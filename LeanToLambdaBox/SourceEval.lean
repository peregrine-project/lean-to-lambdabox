import LeanToLambdaBox.ErasesTotal
import LeanToLambdaBox.Supported

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

Values are `[S Fig. 12]`'s `value_head`: a constructor spine within the constructor's
arity, an inductive-type-name spine, a sort, a Π-type and a λ. A body-less plain constant
therefore has no value at all, which is how PCUIC treats an axiom.
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

/-! ## The eliminator's source-side segmentation -/

/-- The `casesOn` of `I`, at the segmentation `I`'s own block fixes: `dp` arguments before
the major premise — parameters, motive, indices — and then one minor per constructor.

Read off the **inductive declaration**, not off `VEnv.pats`, so it does not depend on how
the pattern table is populated. It constrains `c`'s name and `I`'s declaration and nothing
else: it does not say how `c` is declared, which is why `SEval.iota` carries `ConstOrigin`
beside it. -/
def CasesOnShape (env : VEnv) (c I : Name) (dp nm : Nat) : Prop :=
  isCasesOnName c = true ∧ c.getPrefix = I ∧
  ∃ (ds : List VDecl) (env₀ : VEnv) (decl : VInductDecl) (t : VInductiveType),
    VEnv.WF' ds env₀ ∧ VDecl.induct decl ∈ ds ∧ env₀ ≤ env ∧
    t ∈ decl.types ∧ t.name = I ∧
    dp = decl.nparams + 1 + (t.type.piArity - decl.nparams) ∧ nm = t.ctors.length

/-- The segmentation survives an environment extension: the declaring list sits below
`env`, hence below any extension of it. -/
theorem CasesOnShape.mono {env env' : VEnv} {c I : Name} {dp nm : Nat} (hle : env ≤ env')
    (h : CasesOnShape env c I dp nm) : CasesOnShape env' c I dp nm :=
  let ⟨hn, hp, ds, env₀, decl, t, hds, hd, hle₀, ht, hname, hdp, hnm⟩ := h
  ⟨hn, hp, ds, env₀, decl, t, hds, hd, hle₀.trans hle, ht, hname, hdp, hnm⟩

/-! ## The relation -/

/-- Weak call-by-value big-step evaluation of a source `Lean.Expr`.

The value arms are `[S Fig. 12]`'s `value_head`, keyed on the source theory's own
classification of `Expr.const`: a constructor spine within its arity, an inductive-type-name
spine, a sort, a Π-type, a λ. `SEval.deltaC` unfolds the **compiler** body `bo c`, the body
the eraser reads. Its side condition, and those of `SEval.iota` and `SEval.proj`, is the
definitional equality the step owes (`StepDefeq`): for δ a fact about the two bodies at the
applied instance, for ι and projection the kernel's own reduction. -/
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
      and the kernel body agree on constructor-headed arguments. `hnd` mirrors the eraser's
      own dispatch, which never visits a `casesOn` body: without it a saturated eliminator
      spine has a second derivation, unfolding the eliminator instead of reducing it. -/
  | deltaC {Δ c us ups args argsv b b' v} (hfl : fl.delta)
      (hb : bo c = some b)
      (hnd : ∀ I dp nm, ¬ CasesOnShape env c I dp nm)
      (hinst : b' = b.instantiateLevelParams ups us)
      (hlen : argsv.length = args.length)
      (hargs : ∀ i, i < args.length → SEval env bo Us fl Δ args[i]! argsv[i]!)
      (hdef : StepDefeq env Us Δ (mkApps (.const c us) argsv) (mkApps b' argsv))
      (hcont : SEval env bo Us fl Δ (mkApps b' argsv) v) :
      SEval env bo Us fl Δ (mkApps (.const c us) args) v
  /-- `value_head_cstr`: a constructor spine is a value once its arguments are **and the
      spine is within the constructor's arity**. Keyed on the source theory's
      classification, not on the compiler table and not on a name test, so a `casesOn`
      spine is not a value for a structural reason. `harity` is `[S Fig. 12]`'s own
      `nargs ≤ cstr_arity`, read off the block's parameter count and field counts; without
      it the arm claims a value for a spine the target is stuck on. -/
  | ctorVal {Δ : VLCtx} {cn I : Name} {us : List Level} {iid : InductiveId} {k np : Nat}
      {nfs : List Nat} {args argsv : List Expr} (hc : CtorOf env cn I k)
      (hi : IndInfo env I iid np nfs) (harity : args.length ≤ np + nfs[k]!)
      (hlen : argsv.length = args.length)
      (hargs : ∀ i, i < args.length → SEval env bo Us fl Δ args[i]! argsv[i]!) :
      SEval env bo Us fl Δ (mkApps (.const cn us) args) (mkApps (.const cn us) argsv)
  /-- `value_head_ind`: an inductive type name applied to arguments is a value. Not
      optional — `deltaC` and `ctorVal` evaluate their arguments, and a polymorphic call's
      type argument is exactly this shape. -/
  | indVal {Δ : VLCtx} {cn : Name} {us : List Level} {iid : InductiveId} {np : Nat}
      {nfs : List Nat} {args argsv : List Expr} (hi : IndInfo env cn iid np nfs)
      (hlen : argsv.length = args.length)
      (hargs : ∀ i, i < args.length → SEval env bo Us fl Δ args[i]! argsv[i]!) :
      SEval env bo Us fl Δ (mkApps (.const cn us) args) (mkApps (.const cn us) argsv)
  /-- Types are values: weak evaluation does not enter a binder, and both shapes erase to
      `.box`. Not optional either, for the same reason `indVal` is not. -/
  | sort {Δ : VLCtx} {u : Level} : SEval env bo Us fl Δ (.sort u) (.sort u)
  | forallE {Δ : VLCtx} {n : Name} {ty b : Expr} {bi : BinderInfo} :
      SEval env bo Us fl Δ (.forallE n ty b bi) (.forallE n ty b bi)
  /-- ι: the discriminant evaluates to a constructor spine and the selected minor is
      applied to the constructor's fields, the `np` parameters dropped; `hdef` is the
      kernel ι fact for this instance. Split where the source theory splits it — `hsh`
      counts the arguments before the major premise and the minors after it, `hct` picks
      the selected minor — and headed by a plain constant, which is what `ho` says and
      `hsh` does not. Call-by-value in the **whole** spine, and absorbing the
      over-application the eraser applies outside the emitted node. -/
  | iota {Δ : VLCtx} {con I ctor : Name} {us cus : List Level}
      {pre prev minors minorsv extra extrav cargs : List Expr} {disc r : Expr}
      {np cidx : Nat} (hfl : fl.iota)
      (hsh : CasesOnShape env con I pre.length minors.length)
      (ho : ConstOrigin env con)
      (hct : CtorOf env ctor I cidx)
      (hpre : prev.length = pre.length)
      (hpres : ∀ i, i < pre.length → SEval env bo Us fl Δ pre[i]! prev[i]!)
      (hdiscr : SEval env bo Us fl Δ disc (mkApps (.const ctor cus) cargs))
      (hmin : minorsv.length = minors.length)
      (hmins : ∀ i, i < minors.length → SEval env bo Us fl Δ minors[i]! minorsv[i]!)
      (hxlen : extrav.length = extra.length)
      (hxs : ∀ i, i < extra.length → SEval env bo Us fl Δ extra[i]! extrav[i]!)
      (hidx : cidx < minors.length)
      (hdef : StepDefeq env Us Δ (mkApps (.const con us) (pre ++ disc :: minors ++ extra))
        (mkApps minors[cidx]! (cargs.drop np ++ extra)))
      (hcont : SEval env bo Us fl Δ (mkApps minors[cidx]! (cargs.drop np ++ extra)) r) :
      SEval env bo Us fl Δ (mkApps (.const con us) (pre ++ disc :: minors ++ extra)) r
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
  | deltaC hfl hb hnd hinst hlen _ hdef _ ihargs ihcont =>
      exact .deltaC (h.2.1 hfl) hb hnd hinst hlen ihargs hdef ihcont
  | ctorVal hc hi harity hlen _ ihargs => exact .ctorVal hc hi harity hlen ihargs
  | indVal hi hlen _ ihargs => exact .indVal hi hlen ihargs
  | sort => exact .sort
  | forallE => exact .forallE
  | iota hfl hsh ho hct hpre _ _ hmin _ hxlen _ hidx hdef _ ihpres ihd ihmins ihxs ihc =>
      exact .iota (h.2.2.2.1 hfl) hsh ho hct hpre ihpres ihd hmin ihmins hxlen ihxs hidx
        hdef ihc
  | proj hfl _ hlt hdef _ ihd ihc => exact .proj (h.2.2.2.2.1 hfl) ihd hlt hdef ihc
  | lit hfl _ ih => exact .lit (h.2.2.2.2.2 hfl) ih

/-- **Stability under an environment extension that declares no new eliminator.**

Every side condition that mentions `env` is monotone except one: `deltaC`'s `hnd` is a
*negative* fact about `env`, and an extension that declares a block named `c.getPrefix`
makes `c` a `casesOn` head it was not. `hcs` is exactly the missing direction; the design's
unconditional form is false for that arm. -/
theorem SEval.le {env env' : VEnv} (h : env ≤ env')
    (hcs : ∀ c I dp nm, CasesOnShape env' c I dp nm → CasesOnShape env c I dp nm)
    {bo : Name → Option Expr}
    {Us : List Name} {fl : SEvalFlags} {Δ : VLCtx} {e v : Expr}
    (hev : SEval env bo Us fl Δ e v) : SEval env' bo Us fl Δ e v := by
  induction hev with
  | lam n ty b bi => exact .lam n ty b bi
  | beta hfl _ _ _ ihf iha ihb => exact .beta hfl ihf iha ihb
  | zeta hfl _ _ ihv ihb => exact .zeta hfl ihv ihb
  | deltaC hfl hb hnd hinst hlen _ hdef _ ihargs ihcont =>
      exact .deltaC hfl hb (fun I dp nm hs => hnd I dp nm (hcs _ _ _ _ hs)) hinst hlen
        ihargs (hdef.le h) ihcont
  | ctorVal hc hi harity hlen _ ihargs =>
      exact .ctorVal (hc.mono h) (hi.mono h) harity hlen ihargs
  | indVal hi hlen _ ihargs => exact .indVal (hi.mono h) hlen ihargs
  | sort => exact .sort
  | forallE => exact .forallE
  | iota hfl hsh ho hct hpre _ _ hmin _ hxlen _ hidx hdef _ ihpres ihd ihmins ihxs ihc =>
      exact .iota hfl (hsh.mono h) (ho.mono h) (hct.mono h) hpre ihpres ihd hmin ihmins
        hxlen ihxs hidx (hdef.le h) ihc
  | proj hfl _ hlt hdef _ ihd ihc => exact .proj hfl ihd hlt (hdef.le h) ihc
  | lit hfl _ ih => exact .lit hfl ih

/-! ## What is not a value

The value arms are keyed on the source theory's classification of `Expr.const`, so what
they exclude is a fact rather than a convention: a body-less plain constant heads no value,
and a constructor spine past its arity is not one either.
-/

theorem mkApps_eq_or_app : ∀ (as : List Expr) (f : Expr),
    mkApps f as = f ∨ ∃ g a, mkApps f as = .app g a
  | [], _ => .inl rfl
  | a :: as, f => by
      rcases mkApps_eq_or_app as (.app f a) with h | ⟨g, b, h⟩
      · exact .inr ⟨f, a, by rw [mkApps_cons, h]⟩
      · exact .inr ⟨g, b, by rw [mkApps_cons, h]⟩

theorem eq_mkApps_const_elim {c : Name} {us : List Level} {args : List Expr} {e : Expr}
    (h : e = mkApps (.const c us) args) :
    e = .const c us ∨ ∃ f a, e = .app f a := by
  rcases mkApps_eq_or_app args (.const c us) with hm | ⟨g, a, hm⟩
  · exact .inl (h.trans hm)
  · exact .inr ⟨g, a, h.trans hm⟩

theorem mkApps_const_inj {c c' : Name} {us us' : List Level} :
    ∀ (n : Nat) {as bs : List Expr}, as.length = n →
      mkApps (.const c us) as = mkApps (.const c' us') bs → c = c' ∧ us = us' ∧ as = bs := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro as bs hlen h
    rcases List.eq_nil_or_concat as with rfl | ⟨init, last, rfl⟩
    · rcases List.eq_nil_or_concat bs with rfl | ⟨binit, blast, rfl⟩
      · injection h with h1 h2; exact ⟨h1, h2, rfl⟩
      · rw [List.concat_eq_append, mkApps_concat] at h; simp at h
    · rcases List.eq_nil_or_concat bs with rfl | ⟨binit, blast, rfl⟩
      · rw [List.concat_eq_append, mkApps_concat] at h; simp at h
      · rw [List.concat_eq_append, mkApps_concat, List.concat_eq_append, mkApps_concat] at h
        injection h with h1 h2
        obtain ⟨e1, e2, e3⟩ :=
          ih init.length (by simp [List.concat_eq_append] at hlen; omega) rfl h1
        exact ⟨e1, e2, by rw [e3, h2]⟩

theorem IsArity.piBody_sort {A : VExpr} (h : IsArity A) : ∃ u, A.piBody = .sort u := by
  induction h with
  | sort u => exact ⟨u, rfl⟩
  | forallE _ _ _ ih => exact ih

theorem CtorOf.constant_ctorResult {env : VEnv} {c I : Name} {k : Nat} (h : CtorOf env c I k) :
    ∃ ci np nf nind, env.constants c = some ci ∧ ci.type.CtorResult I np nf nind := by
  obtain ⟨ds, env₀, decl, t, ctor, hds, hd, hle, hmem, hname, hk, hcn⟩ := h
  obtain ⟨e₀, e₁, hdecl, hadd, hle₁⟩ := wf'_induct_origin hds hd
  obtain ⟨envT, envC, envR, hT, hC, hR, hP⟩ := VEnv.addInduct_stages hadd
  have hctor : ctor ∈ t.ctors := List.mem_of_getElem? hk
  have hcmem' : ctor ∈ decl.types.flatMap (·.ctors) := List.mem_flatMap.2 ⟨t, hmem, hctor⟩
  have hfold : decl.consts.foldlM (fun (e : VEnv) b => e.addConst b.1 b.2) e₀ = some envR := by
    rw [← VInductDecl.addTypesCtorsRecs_eq]
    unfold VInductDecl.addTypesCtorsRecs VInductDecl.addTypesCtors
    simp [hT, hC, hR]
  have hcmem : (ctor.name, ctor.toVConstant) ∈ decl.consts :=
    List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hcmem'))
  have hfind := VEnv.addConst_foldlM_find (nm := Prod.fst) (ci := Prod.snd) hfold _ hcmem
  obtain ⟨nf, hres⟩ := hdecl.ctors_result t hmem ctor hctor
  exact ⟨_, _, nf, _,
    hcn ▸ hle.constants (hle₁.constants ((VEnv.addRules_le hP).constants hfind)),
    hname ▸ hres⟩

theorem CtorOf.not_indInfo {env : VEnv} {c I : Name} {k : Nat} {iid : InductiveId}
    {np : Nat} {nfs : List Nat} (hc : CtorOf env c I k) : ¬ IndInfo env c iid np nfs := by
  intro hi
  obtain ⟨ci, np', nf, nind, hcst, hres⟩ := hc.constant_ctorResult
  obtain ⟨ci', hcst', harity⟩ := hi.constant_isArity
  cases hcst.symm.trans hcst'
  obtain ⟨u, hu⟩ := harity.piBody_sort
  have := (VExpr.CtorResult_iff.1 hres).2.1
  rw [hu] at this
  simp [VExpr.headConst?, VExpr.getAppFn] at this

/-- A Π-type's only source value is itself: no other arm has a `.forallE` subject, so
without the arm a δ redex with a Π-type argument has no derivation at all. -/
theorem SEval.forallE_inv {env : VEnv} {bo : Name → Option Expr} {Us : List Name}
    {fl : SEvalFlags} {Δ : VLCtx} {e v : Expr} (hev : SEval env bo Us fl Δ e v)
    {n : Name} {ty b : Expr} {bi : BinderInfo} (he : e = .forallE n ty b bi) : v = e := by
  cases hev <;>
    first
      | rfl
      | (rcases eq_mkApps_const_elim he.symm with h | ⟨_, _, h⟩ <;> simp at h)
      | simp at he

/-- **A body-less, non-constructor, non-type-name, non-eliminator constant heads no value.**
PCUIC's treatment of an axiom, and what keeps an axiom-freedom premise out of the
simulation: at such a head no arm applies, so a run reaching one has no source derivation. -/
theorem untabled_const_not_value {env : VEnv} {bo : Name → Option Expr} {Us : List Name}
    {fl : SEvalFlags} {Δ : VLCtx} {c : Name} (hno : bo c = none)
    (hnc : ∀ I k, ¬ CtorOf env c I k)
    (hni : ∀ iid np nfs, ¬ IndInfo env c iid np nfs)
    (hnd : ∀ I dp nm, ¬ CasesOnShape env c I dp nm)
    (us : List Level) (args : List Expr) (v : Expr) :
    ¬ SEval env bo Us fl Δ (mkApps (.const c us) args) v := by
  suffices h : ∀ (m : Nat) (e w : Expr), SEval env bo Us fl Δ e w →
      ∀ (us' : List Level) (args' : List Expr), args'.length = m →
        e = mkApps (.const c us') args' → False from
    fun hev => h _ _ _ hev us args rfl rfl
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro e w hev us' args' hlen he
    cases hev with
    | lam _ _ _ _ => rcases eq_mkApps_const_elim he with h | ⟨_, _, h⟩ <;> simp at h
    | zeta _ _ _ => rcases eq_mkApps_const_elim he with h | ⟨_, _, h⟩ <;> simp at h
    | sort => rcases eq_mkApps_const_elim he with h | ⟨_, _, h⟩ <;> simp at h
    | forallE => rcases eq_mkApps_const_elim he with h | ⟨_, _, h⟩ <;> simp at h
    | proj _ _ _ _ _ => rcases eq_mkApps_const_elim he with h | ⟨_, _, h⟩ <;> simp at h
    | lit _ _ => rcases eq_mkApps_const_elim he with h | ⟨_, _, h⟩ <;> simp at h
    | beta _ hf _ _ =>
        rcases List.eq_nil_or_concat args' with rfl | ⟨init, last, rfl⟩
        · simp [mkApps] at he
        · rw [List.concat_eq_append, mkApps_concat] at he
          injection he with h1 h2
          exact ih init.length (by simp [List.concat_eq_append] at hlen; omega) _ _ hf
            us' init rfl h1
    | deltaC _ hb _ _ _ _ _ _ =>
        obtain ⟨rfl, -, -⟩ := mkApps_const_inj _ rfl he
        exact absurd (hno.symm.trans hb) (by simp)
    | ctorVal hc _ _ _ _ =>
        obtain ⟨rfl, -, -⟩ := mkApps_const_inj _ rfl he
        exact hnc _ _ hc
    | indVal hi _ _ =>
        obtain ⟨rfl, -, -⟩ := mkApps_const_inj _ rfl he
        exact hni _ _ _ hi
    | iota _ hsh _ _ _ _ _ _ _ _ _ _ _ _ =>
        obtain ⟨rfl, -, -⟩ := mkApps_const_inj _ rfl he
        exact hnd _ _ _ hsh

/-- At a head δ cannot move and ι cannot fire, a spine's value is a spine on the same head:
in particular it is never a λ, so no such spine is a β redex's function. -/
theorem seval_const_head_value {env : VEnv} {bo : Name → Option Expr} {Us : List Name}
    {fl : SEvalFlags} {Δ : VLCtx} {c : Name} (hno : bo c = none)
    (hnd : ∀ I dp nm, ¬ CasesOnShape env c I dp nm)
    (us : List Level) (args : List Expr) (v : Expr)
    (hev : SEval env bo Us fl Δ (mkApps (.const c us) args) v) :
    ∃ argsv, v = mkApps (.const c us) argsv := by
  suffices h : ∀ (m : Nat) (e w : Expr), SEval env bo Us fl Δ e w →
      ∀ (us' : List Level) (args' : List Expr), args'.length = m →
        e = mkApps (.const c us') args' → ∃ argsv, w = mkApps (.const c us') argsv from
    h _ _ _ hev us args rfl rfl
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro e w hev us' args' hlen he
    cases hev with
    | lam _ _ _ _ => rcases eq_mkApps_const_elim he with h | ⟨_, _, h⟩ <;> simp at h
    | zeta _ _ _ => rcases eq_mkApps_const_elim he with h | ⟨_, _, h⟩ <;> simp at h
    | sort => rcases eq_mkApps_const_elim he with h | ⟨_, _, h⟩ <;> simp at h
    | forallE => rcases eq_mkApps_const_elim he with h | ⟨_, _, h⟩ <;> simp at h
    | proj _ _ _ _ _ => rcases eq_mkApps_const_elim he with h | ⟨_, _, h⟩ <;> simp at h
    | lit _ _ => rcases eq_mkApps_const_elim he with h | ⟨_, _, h⟩ <;> simp at h
    | beta _ hf _ _ =>
        rcases List.eq_nil_or_concat args' with rfl | ⟨init, last, rfl⟩
        · simp [mkApps] at he
        · rw [List.concat_eq_append, mkApps_concat] at he
          injection he with h1 h2
          obtain ⟨argsv, hlam⟩ :=
            ih init.length (by simp [List.concat_eq_append] at hlen; omega) _ _ hf
              us' init rfl h1
          rcases eq_mkApps_const_elim hlam with h | ⟨_, _, h⟩ <;> simp at h
    | deltaC _ hb _ _ _ _ _ _ =>
        obtain ⟨rfl, -, -⟩ := mkApps_const_inj _ rfl he
        exact absurd (hno.symm.trans hb) (by simp)
    | ctorVal _ _ _ _ _ =>
        obtain ⟨rfl, rfl, rfl⟩ := mkApps_const_inj _ rfl he
        exact ⟨_, rfl⟩
    | indVal _ _ _ =>
        obtain ⟨rfl, rfl, rfl⟩ := mkApps_const_inj _ rfl he
        exact ⟨_, rfl⟩
    | iota _ hsh _ _ _ _ _ _ _ _ _ _ _ _ =>
        obtain ⟨rfl, -, -⟩ := mkApps_const_inj _ rfl he
        exact absurd hsh (hnd _ _ _)

/-- `n` arguments over-apply `c`: **no** classification of `c` in `env` gives it an arity
that long. Stated over every classification because `CtorOf`/`IndInfo` read a declaration
list below `env` and nothing yet says two such lists agree — `CtorOf.inj` and `IndInfo.inj`
are the kernel-theory facts that would collapse this to the single-classification bound. -/
def OverApplied (env : VEnv) (c : Name) (n : Nat) : Prop :=
  ∀ I k iid np nfs, CtorOf env c I k → IndInfo env I iid np nfs → np + nfs[k]! < n

/-- **An over-applied constructor spine has no source value.** This is what `harity` adds:
without it `ctorVal` would call such a spine a value, and the target is stuck on it. -/
theorem overapplied_ctor_not_value {env : VEnv} {bo : Name → Option Expr} {Us : List Name}
    {fl : SEvalFlags} {Δ : VLCtx} {c I : Name} {k : Nat} {us : List Level} {args : List Expr}
    (hc : CtorOf env c I k) (hno : bo c = none)
    (hnd : ∀ I' dp nm, ¬ CasesOnShape env c I' dp nm)
    (hover : OverApplied env c args.length) (v : Expr) :
    ¬ SEval env bo Us fl Δ (mkApps (.const c us) args) v := by
  intro hev
  suffices h : ∀ (e w : Expr), SEval env bo Us fl Δ e w →
      ∀ (us' : List Level) (args' : List Expr), args'.length = args.length →
        e = mkApps (.const c us') args' → False from h _ _ hev us args rfl rfl
  intro e w hev us' args' hlen he
  cases hev with
  | lam _ _ _ _ => rcases eq_mkApps_const_elim he with h | ⟨_, _, h⟩ <;> simp at h
  | zeta _ _ _ => rcases eq_mkApps_const_elim he with h | ⟨_, _, h⟩ <;> simp at h
  | sort => rcases eq_mkApps_const_elim he with h | ⟨_, _, h⟩ <;> simp at h
  | forallE => rcases eq_mkApps_const_elim he with h | ⟨_, _, h⟩ <;> simp at h
  | proj _ _ _ _ _ => rcases eq_mkApps_const_elim he with h | ⟨_, _, h⟩ <;> simp at h
  | lit _ _ => rcases eq_mkApps_const_elim he with h | ⟨_, _, h⟩ <;> simp at h
  | beta _ hf _ _ =>
      rcases List.eq_nil_or_concat args' with rfl | ⟨init, last, rfl⟩
      · simp [mkApps] at he
      · rw [List.concat_eq_append, mkApps_concat] at he
        injection he with h1 h2
        subst h1
        obtain ⟨argsv, hlam⟩ := seval_const_head_value hno hnd _ _ _ hf
        rcases eq_mkApps_const_elim hlam with h | ⟨_, _, h⟩ <;> simp at h
  | deltaC _ hb _ _ _ _ _ _ =>
      obtain ⟨rfl, -, -⟩ := mkApps_const_inj _ rfl he
      exact absurd (hno.symm.trans hb) (by simp)
  | ctorVal hc' hi' harity _ _ =>
      obtain ⟨rfl, -, rfl⟩ := mkApps_const_inj _ rfl he
      exact absurd harity (Nat.not_le.2 (hlen ▸ hover _ _ _ _ _ hc' hi'))
  | indVal hi _ _ =>
      obtain ⟨rfl, -, -⟩ := mkApps_const_inj _ rfl he
      exact hc.not_indInfo hi
  | iota _ hsh _ _ _ _ _ _ _ _ _ _ _ _ =>
      obtain ⟨rfl, -, -⟩ := mkApps_const_inj _ rfl he
      exact absurd hsh (hnd _ _ _)

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

A two-constant environment — two binary operations whose defining equations are registered
— with a compiler body tabled for each. It exhibits the δ arm at `deltaOnly` and at the
applied instance, and shows what discharges the arm's side condition: the environment's own
defining equations. `add`'s tabled body is its kernel body, the `rfl`-grade case; `sel`'s is
not, and the side condition holds there because it is asked at the applied instance.

The applied instance also exhibits the two type-value arms: its first argument is a sort and
its second a Π-type, and `deltaC` evaluates both before unfolding, so without `SEval.sort`
and `SEval.forallE` the redex would have no derivation at all.
-/

namespace DeltaWitness

/-- `Type`, the sort the first argument inhabits. -/
def tyU : VExpr := .sort (.succ .zero)

/-- The sort of `∀ p : Prop, p`, the second argument. -/
def piU : VExpr := .sort (.imax (.succ .zero) .zero)

/-- `Type`, as a source `Expr`. -/
def tyUSrc : Expr := .sort (.succ .zero)

/-- `piU`, as a source `Expr`. -/
def piUSrc : Expr := .sort (.imax (.succ .zero) .zero)

/-- `add`'s declared type, `Type → (∀ p : Prop, p)'s sort → Type`. -/
def addTy : VExpr := .forallE tyU (.forallE piU tyU)

/-- `add`'s body: the projection onto the first argument. -/
def addBodySrc : Expr :=
  .lam `a tyUSrc (.lam `b piUSrc (.bvar 1) .default) .default

/-- The translation of `addBodySrc`. -/
def addBody : VExpr := .lam tyU (.lam piU (.bvar 1))

/-- `sel`'s **compiler** body: the constant function returning `Prop`. Its kernel body is
`addBody`, a different term, and the two agree only where the first argument is `Prop`. -/
def selBodySrc : Expr :=
  .lam `a tyUSrc (.lam `b piUSrc (.sort .zero) .default) .default

/-- The translation of `selBodySrc`. -/
def selBody : VExpr := .lam tyU (.lam piU (.sort .zero))

/-- The compiler body of `sel` is not its kernel body. -/
theorem selBody_ne_addBody : selBody ≠ addBody := by simp [selBody, addBody]

/-- `add`'s defining equation, as the environment registers it. -/
def addDefEq : VDefEq := ⟨0, .const `add [], addBody, addTy⟩

/-- `sel`'s defining equation: the *kernel* body, which is `add`'s. -/
def selDefEq : VDefEq := ⟨0, .const `sel [], addBody, addTy⟩

/-- The witness environment: two constants and two defining equations. -/
def env : VEnv where
  constants n :=
    if n = `add then some ⟨0, addTy⟩
    else if n = `sel then some ⟨0, addTy⟩
    else none
  defeqs df := df = addDefEq ∨ df = selDefEq
  pats _ _ := False

/-- The compiler-body table: `add`, whose tabled body is its kernel body, and `sel`, whose
tabled body is not. -/
def bo : Name → Option Expr := fun n =>
  if n = `add then some addBodySrc else if n = `sel then some selBodySrc else none

theorem constants_add : env.constants `add = some ⟨0, addTy⟩ := rfl

theorem constants_sel : env.constants `sel = some ⟨0, addTy⟩ := rfl

/-- Neither tabled constant is a `casesOn` name, so `deltaC`'s eliminator guard is a name
test here. -/
theorem not_casesOnShape {c I : Name} {dp nm : Nat} (hc : c = `add ∨ c = `sel) :
    ¬ CasesOnShape env c I dp nm := by
  rintro ⟨hn, -, -⟩
  rcases hc with rfl | rfl <;> simp [isCasesOnName, lastComponent] at hn

theorem hasType_tyU {Γ : List VExpr} : env.HasType 0 Γ tyU (.sort (.succ (.succ .zero))) :=
  VEnv.HasType.sort (l := .succ .zero) trivial

theorem isType_tyU {Γ : List VExpr} : env.IsType 0 Γ tyU := ⟨_, hasType_tyU⟩

theorem hasType_piU {Γ : List VExpr} :
    env.HasType 0 Γ piU (.sort (.succ (.imax (.succ .zero) .zero))) :=
  VEnv.HasType.sort (l := .imax (.succ .zero) .zero) ⟨trivial, trivial⟩

theorem isType_piU {Γ : List VExpr} : env.IsType 0 Γ piU := ⟨_, hasType_piU⟩

theorem trExprS_tyUSrc {Δ : VLCtx} : TrExprS env [] Δ tyUSrc tyU := .sort rfl

theorem trExprS_piUSrc {Δ : VLCtx} : TrExprS env [] Δ piUSrc piU := .sort rfl

/-! ### The two arguments: a sort and a Π-type -/

/-- The first argument, `Prop`. -/
def arg₁Src : Expr := .sort .zero

/-- The second argument, `∀ p : Prop, p`. -/
def arg₂Src : Expr := .forallE `p (.sort .zero) (.bvar 0) .default

/-- The translation of `arg₂Src`. -/
def arg₂ : VExpr := .forallE (.sort .zero) (.bvar 0)

theorem hasType_arg₁ {Γ : List VExpr} : env.HasType 0 Γ (.sort .zero) tyU :=
  VEnv.HasType.sort (l := .zero) trivial

theorem hasType_arg₂ {Γ : List VExpr} : env.HasType 0 Γ arg₂ piU :=
  VEnv.HasType.forallE hasType_arg₁ (VEnv.HasType.bvar .zero)

theorem trExprS_arg₁ {Δ : VLCtx} : TrExprS env [] Δ arg₁Src (.sort .zero) := .sort rfl

theorem trExprS_arg₂ {Δ : VLCtx} : TrExprS env [] Δ arg₂Src arg₂ :=
  .forallE ⟨_, hasType_arg₁⟩ ⟨_, VEnv.HasType.bvar .zero⟩ (.sort rfl) (.bvar rfl)

/-- **`SEval.sort` fires**: a sort is a value. -/
theorem seval_arg₁ {fl : SEvalFlags} : SEval env bo [] fl [] arg₁Src arg₁Src := .sort

/-- **`SEval.forallE` fires**: a Π-type is a value. -/
theorem seval_arg₂ {fl : SEvalFlags} : SEval env bo [] fl [] arg₂Src arg₂Src := .forallE

/-! ### Typing the two bodies -/

theorem hasType_add {Γ : List VExpr} : env.HasType 0 Γ (.const `add []) addTy :=
  .constDF constants_add (by simp) (by simp) rfl .nil

theorem hasType_sel {Γ : List VExpr} : env.HasType 0 Γ (.const `sel []) addTy :=
  .constDF constants_sel (by simp) (by simp) rfl .nil

theorem trExprS_add {Δ : VLCtx} : TrExprS env [] Δ (.const `add []) (.const `add []) :=
  .const constants_add rfl rfl

theorem trExprS_sel {Δ : VLCtx} : TrExprS env [] Δ (.const `sel []) (.const `sel []) :=
  .const constants_sel rfl rfl

theorem hasType_addBody {Γ : List VExpr} : env.HasType 0 Γ addBody addTy :=
  .lam hasType_tyU (.lam hasType_piU (.bvar (.succ .zero)))

theorem hasType_selBody {Γ : List VExpr} : env.HasType 0 Γ selBody addTy :=
  .lam hasType_tyU (.lam hasType_piU hasType_arg₁)

theorem trExprS_addBody {Δ : VLCtx} : TrExprS env [] Δ addBodySrc addBody :=
  .lam isType_tyU trExprS_tyUSrc (.lam isType_piU trExprS_piUSrc (.bvar rfl))

theorem trExprS_selBody {Δ : VLCtx} : TrExprS env [] Δ selBodySrc selBody :=
  .lam isType_tyU trExprS_tyUSrc (.lam isType_piU trExprS_piUSrc (.sort rfl))

/-- The environment's defining equation, at the empty level instantiation. -/
theorem isDefEq_add {Γ : List VExpr} : env.IsDefEq 0 Γ (.const `add []) addBody addTy :=
  .extra (df := addDefEq) (ls := []) (.inl rfl) (by simp) rfl

theorem isDefEq_sel {Γ : List VExpr} : env.IsDefEq 0 Γ (.const `sel []) addBody addTy :=
  .extra (df := selDefEq) (ls := []) (.inr rfl) (by simp) rfl

/-- **One tabled unfolding at `deltaOnly`.** The δ arm fires on the bare constant; its side
condition is the environment's own defining equation, and its eliminator guard is the name
test `not_casesOnShape`. -/
theorem seval_add_deltaOnly :
    SEval env bo [] deltaOnly [] (.const `add []) addBodySrc := by
  refine .deltaC (b := addBodySrc) (b' := addBodySrc) (ups := []) (args := []) (argsv := [])
    rfl rfl (fun _ _ _ => not_casesOnShape (.inl rfl)) rfl rfl (fun i hi => absurd hi (by simp))
    ⟨_, _, trExprS_add, trExprS_addBody, ⟨_, isDefEq_add⟩⟩ ?_
  exact .lam ..

/-- Flags enabling β and δ, the point at which the applied instance computes. -/
def betaDelta : SEvalFlags := ⟨true, true, false, false, false, false⟩

/-! ### The applied instance -/

/-- The two arguments evaluate to themselves, by the sort arm and the Π arm. -/
theorem hargs_applied {fl : SEvalFlags} : ∀ i, i < [arg₁Src, arg₂Src].length →
    SEval env bo [] fl [] [arg₁Src, arg₂Src][i]! [arg₁Src, arg₂Src][i]! := by
  intro i hi
  match i, hi with
  | 0, _ => simpa using seval_arg₁
  | 1, _ => simpa using seval_arg₂

theorem hasType_add_arg₁ {Γ : List VExpr} :
    env.HasType 0 Γ (.app (.const `add []) (.sort .zero)) (.forallE piU tyU) :=
  .appDF hasType_add hasType_arg₁

theorem hasType_addBody_arg₁ {Γ : List VExpr} :
    env.HasType 0 Γ (.app addBody (.sort .zero)) (.forallE piU tyU) :=
  .appDF hasType_addBody hasType_arg₁

theorem hasType_selBody_arg₁ {Γ : List VExpr} :
    env.HasType 0 Γ (.app selBody (.sort .zero)) (.forallE piU tyU) :=
  .appDF hasType_selBody hasType_arg₁

theorem hasType_sel_arg₁ {Γ : List VExpr} :
    env.HasType 0 Γ (.app (.const `sel []) (.sort .zero)) (.forallE piU tyU) :=
  .appDF hasType_sel hasType_arg₁

/-- The applied redex translates. -/
theorem trExprS_add_applied :
    TrExprS env [] [] (mkApps (.const `add []) [arg₁Src, arg₂Src])
      (.app (.app (.const `add []) (.sort .zero)) arg₂) :=
  .app hasType_add_arg₁ hasType_arg₂
    (.app hasType_add hasType_arg₁ trExprS_add trExprS_arg₁) trExprS_arg₂

/-- The applied reduct translates. -/
theorem trExprS_addBody_applied :
    TrExprS env [] [] (mkApps addBodySrc [arg₁Src, arg₂Src])
      (.app (.app addBody (.sort .zero)) arg₂) :=
  .app hasType_addBody_arg₁ hasType_arg₂
    (.app hasType_addBody hasType_arg₁ trExprS_addBody trExprS_arg₁) trExprS_arg₂

/-- **The applied instance.** `add Prop (∀ p : Prop, p)` unfolds the tabled body once and
β-reduces to `Prop`, with the arm's side condition stated at the evaluated arguments and
discharged from the environment's defining equation. Its `hargs` premise is where the sort
and Π arms are spent: by `SEval.forallE_inv` the second argument has no other derivation. -/
theorem seval_add_applied :
    SEval env bo [] betaDelta [] (mkApps (.const `add []) [arg₁Src, arg₂Src]) arg₁Src := by
  refine .deltaC (b := addBodySrc) (b' := addBodySrc) (ups := []) rfl rfl
    (fun _ _ _ => not_casesOnShape (.inl rfl)) rfl rfl hargs_applied
    ⟨_, _, trExprS_add_applied, trExprS_addBody_applied, ?_⟩ ?_
  · exact ⟨_, .appDF (.appDF isDefEq_add hasType_arg₁) hasType_arg₂⟩
  · exact .beta rfl (.beta rfl (.lam ..) seval_arg₁ (.lam ..)) seval_arg₂ .sort

/-! ### A tabled body that is not the kernel body

`sel`'s compiler body and kernel body are different terms — the situation of every
declaration erased from a compiler body. The arm's side condition is still inhabited,
because it is asked at the *applied* instance, where both bodies reach the same value. -/

/-- Both bodies reach `Prop` at these arguments: `addBody` because its first argument is
`Prop`, `selBody` because it is constant. One β-chain serves both, since both bodies
instantiate to the same λ. -/
theorem beta_applied {body : VExpr} (h : env.HasType 0 [tyU] body (.forallE piU tyU))
    (heq : body.inst (.sort .zero) = .lam piU (.sort .zero)) :
    env.IsDefEq 0 [] (.app (.app (.lam tyU body) (.sort .zero)) arg₂) (.sort .zero) tyU := by
  have b₁ := VEnv.IsDefEq.beta h (hasType_arg₁ (Γ := []))
  rw [heq] at b₁
  have b₂ := VEnv.IsDefEq.beta (A := piU) (hasType_arg₁ (Γ := [piU])) (hasType_arg₂ (Γ := []))
  exact .trans (.appDF b₁ hasType_arg₂) b₂

theorem addBody_applied :
    env.IsDefEq 0 [] (.app (.app addBody (.sort .zero)) arg₂) (.sort .zero) tyU :=
  beta_applied (.lam hasType_piU (.bvar (.succ .zero))) rfl

theorem selBody_applied :
    env.IsDefEq 0 [] (.app (.app selBody (.sort .zero)) arg₂) (.sort .zero) tyU :=
  beta_applied (.lam hasType_piU hasType_arg₁) rfl

theorem trExprS_sel_applied :
    TrExprS env [] [] (mkApps (.const `sel []) [arg₁Src, arg₂Src])
      (.app (.app (.const `sel []) (.sort .zero)) arg₂) :=
  .app hasType_sel_arg₁ hasType_arg₂
    (.app hasType_sel hasType_arg₁ trExprS_sel trExprS_arg₁) trExprS_arg₂

theorem trExprS_selBody_applied :
    TrExprS env [] [] (mkApps selBodySrc [arg₁Src, arg₂Src])
      (.app (.app selBody (.sort .zero)) arg₂) :=
  .app hasType_selBody_arg₁ hasType_arg₂
    (.app hasType_selBody hasType_arg₁ trExprS_selBody trExprS_arg₁) trExprS_arg₂

/-- **The applied instance at a mismatched body.** `sel` unfolds a tabled body its kernel
declaration does not have, and the arm's side condition still holds: both bodies compute to
`Prop` at these arguments. -/
theorem seval_sel_applied :
    SEval env bo [] betaDelta [] (mkApps (.const `sel []) [arg₁Src, arg₂Src]) arg₁Src := by
  refine .deltaC (b := selBodySrc) (b' := selBodySrc) (ups := []) rfl rfl
    (fun _ _ _ => not_casesOnShape (.inr rfl)) rfl rfl hargs_applied
    ⟨_, _, trExprS_sel_applied, trExprS_selBody_applied, ?_⟩ ?_
  · exact ⟨_, .trans (.trans (.appDF (.appDF isDefEq_sel hasType_arg₁) hasType_arg₂)
      addBody_applied) (.symm selBody_applied)⟩
  · exact .beta rfl (.beta rfl (.lam ..) seval_arg₁ (.lam ..)) seval_arg₂ .sort

end DeltaWitness

namespace NatWitness

def natN : Name := `Nat
def natZ : Name := `Nat.zero
def natS : Name := `Nat.succ
def natR : Name := `Nat.rec

def natTy : VExpr := .const natN []
def natZeroV : VExpr := .const natZ []
def natSuccV : VExpr := .const natS []
def natSort : VExpr := .sort (.succ .zero)
def natSuccTy : VExpr := .forallE natTy natTy

def natMotiveTy : VExpr := .forallE natTy (.sort .zero)
def natMinor0Ty : VExpr := .app (.bvar 0) natZeroV
def natMinor1Ty : VExpr :=
  .forallE natTy (.forallE (.app (.bvar 2) (.bvar 0)) (.app (.bvar 3) (.app natSuccV (.bvar 1))))
def natRecTy : VExpr :=
  .forallE natMotiveTy (.forallE natMinor0Ty
    (.forallE natMinor1Ty (.forallE natTy (.app (.bvar 3) (.bvar 0)))))

def natRule0Rhs : VExpr := .lam natMotiveTy (.lam natMinor0Ty (.lam natMinor1Ty (.bvar 1)))
def natRule1Rhs : VExpr :=
  .lam natMotiveTy (.lam natMinor0Ty (.lam natMinor1Ty (.lam natTy
    (.app (.app (.bvar 1) (.bvar 0))
      (.app (.app (.app (.app (.const natR []) (.bvar 3)) (.bvar 2)) (.bvar 1)) (.bvar 0))))))

def natZeroVal : VConstVal := { uvars := 0, type := natTy, name := natZ }
def natSuccVal : VConstVal := { uvars := 0, type := natSuccTy, name := natS }
def natTypeVal : VInductiveType :=
  { uvars := 0, type := natSort, name := natN, ctors := [natZeroVal, natSuccVal] }
def natRule0 : VRecRule := { ctor := natZ, ctorParams := 0, nfields := 0, rhs := natRule0Rhs }
def natRule1 : VRecRule := { ctor := natS, ctorParams := 0, nfields := 1, rhs := natRule1Rhs }
def natRecVal : VRecursor :=
  { uvars := 0, type := natRecTy, name := natR, all := [natN], numParams := 0,
    numMotives := 1, numMinors := 2, numIndices := 0, k := false,
    rules := [natRule0, natRule1] }
def natDecl : VInductDecl :=
  { uvars := 0, nparams := 0, types := [natTypeVal], recs := [natRecVal] }

def natEnvT : VEnv :=
  { VEnv.empty with constants := fun n => if natN = n then some ⟨0, natSort⟩ else none }
def natEnvC : VEnv :=
  { natEnvT with
    constants := fun n =>
      if natS = n then some ⟨0, natSuccTy⟩
      else if natZ = n then some ⟨0, natTy⟩ else natEnvT.constants n }
def natEnvR : VEnv :=
  { natEnvC with
    constants := fun n => if natR = n then some ⟨0, natRecTy⟩ else natEnvC.constants n }

theorem natDecl_addTypes : natDecl.addTypes VEnv.empty = some natEnvT := by
  simp [VInductDecl.addTypes, VEnv.addConst, VEnv.empty, natDecl, natTypeVal, natEnvT]

theorem natDecl_addCtors : natDecl.addCtors natEnvT = some natEnvC := by
  simp [VInductDecl.addCtors, VEnv.addConst, natDecl, natTypeVal, natZeroVal, natSuccVal,
    natEnvT, natEnvC, natN, natZ, natS]
  rfl

theorem natDecl_addRecs : natDecl.addRecs natEnvC = some natEnvR := by
  simp [VInductDecl.addRecs, VEnv.addConst, natDecl, natRecVal, natEnvC, natEnvR, natEnvT,
    natN, natZ, natS, natR]
  rfl

theorem natDecl_addTypesCtorsRecs : natDecl.addTypesCtorsRecs VEnv.empty = some natEnvR := by
  simp [VInductDecl.addTypesCtorsRecs, VInductDecl.addTypesCtors, natDecl_addTypes,
    natDecl_addCtors, natDecl_addRecs]

theorem natEnvT_N : natEnvT.constants natN = some ⟨0, natSort⟩ := by simp [natEnvT]
theorem natEnvC_N : natEnvC.constants natN = some ⟨0, natSort⟩ := by
  simp [natEnvC, natEnvT, natN, natZ, natS]
theorem natEnvC_Z : natEnvC.constants natZ = some ⟨0, natTy⟩ := by
  simp [natEnvC, natZ, natS]
theorem natEnvC_S : natEnvC.constants natS = some ⟨0, natSuccTy⟩ := by simp [natEnvC]
theorem natEnvR_N : natEnvR.constants natN = some ⟨0, natSort⟩ := by
  simp [natEnvR, natEnvC, natEnvT, natN, natZ, natS, natR]
theorem natEnvR_Z : natEnvR.constants natZ = some ⟨0, natTy⟩ := by
  simp [natEnvR, natEnvC, natZ, natS, natR]
theorem natEnvR_S : natEnvR.constants natS = some ⟨0, natSuccTy⟩ := by
  simp [natEnvR, natEnvC, natS, natR]
theorem natEnvR_R : natEnvR.constants natR = some ⟨0, natRecTy⟩ := by simp [natEnvR]

theorem natN_ty {Γ : List VExpr} : VEnv.HasType natEnvC 0 Γ natTy natSort :=
  VEnv.HasType.const natEnvC_N nofun rfl
theorem natZ_ty {Γ : List VExpr} : VEnv.HasType natEnvC 0 Γ natZeroV natTy :=
  VEnv.HasType.const natEnvC_Z nofun rfl
theorem natS_ty {Γ : List VExpr} : VEnv.HasType natEnvC 0 Γ natSuccV natSuccTy :=
  VEnv.HasType.const natEnvC_S nofun rfl

theorem natMotive_ty {Γ : List VExpr} :
    VEnv.HasType natEnvC 0 Γ natMotiveTy (.sort (.imax (.succ .zero) (.succ .zero))) :=
  VEnv.HasType.forallE natN_ty (VEnv.HasType.sort (l := .zero) trivial)

theorem natMinor0_ty {Γ : List VExpr} :
    VEnv.HasType natEnvC 0 (natMotiveTy :: Γ) natMinor0Ty (.sort .zero) :=
  VEnv.HasType.app (B := .sort .zero) (VEnv.HasType.bvar .zero) natZ_ty

theorem natMinor1_ty {Γ : List VExpr} :
    VEnv.HasType natEnvC 0 (natMinor0Ty :: natMotiveTy :: Γ) natMinor1Ty
      (.sort (.imax (.succ .zero) (.imax .zero .zero))) :=
  VEnv.HasType.forallE natN_ty <|
    VEnv.HasType.forallE
      (VEnv.HasType.app (B := .sort .zero) (VEnv.HasType.bvar (.succ (.succ .zero)))
        (VEnv.HasType.bvar .zero))
      (VEnv.HasType.app (B := .sort .zero) (VEnv.HasType.bvar (.succ (.succ (.succ .zero))))
        (VEnv.HasType.app (B := natTy) natS_ty (VEnv.HasType.bvar (.succ .zero))))

theorem natRecTy_ty : VEnv.IsType natEnvC 0 [] natRecTy :=
  ⟨_, VEnv.HasType.forallE natMotive_ty <|
    VEnv.HasType.forallE natMinor0_ty <|
      VEnv.HasType.forallE natMinor1_ty <|
        VEnv.HasType.forallE natN_ty <|
          VEnv.HasType.app (B := .sort .zero)
            (VEnv.HasType.bvar (.succ (.succ (.succ .zero)))) (VEnv.HasType.bvar .zero)⟩

/-! ### The ι rules are typed -/

theorem natN_tyR {Γ : List VExpr} : VEnv.HasType natEnvR 0 Γ natTy natSort :=
  VEnv.HasType.const natEnvR_N nofun rfl
theorem natZ_tyR {Γ : List VExpr} : VEnv.HasType natEnvR 0 Γ natZeroV natTy :=
  VEnv.HasType.const natEnvR_Z nofun rfl
theorem natS_tyR {Γ : List VExpr} : VEnv.HasType natEnvR 0 Γ natSuccV natSuccTy :=
  VEnv.HasType.const natEnvR_S nofun rfl
theorem natR_tyR {Γ : List VExpr} : VEnv.HasType natEnvR 0 Γ (.const natR []) natRecTy :=
  VEnv.HasType.const natEnvR_R nofun rfl

theorem natMotive_tyR {Γ : List VExpr} :
    VEnv.HasType natEnvR 0 Γ natMotiveTy (.sort (.imax (.succ .zero) (.succ .zero))) :=
  VEnv.HasType.forallE natN_tyR (VEnv.HasType.sort (l := .zero) trivial)

theorem natMinor0_tyR {Γ : List VExpr} :
    VEnv.HasType natEnvR 0 (natMotiveTy :: Γ) natMinor0Ty (.sort .zero) :=
  VEnv.HasType.app (B := .sort .zero) (VEnv.HasType.bvar .zero) natZ_tyR

theorem natMinor1_tyR {Γ : List VExpr} :
    VEnv.HasType natEnvR 0 (natMinor0Ty :: natMotiveTy :: Γ) natMinor1Ty
      (.sort (.imax (.succ .zero) (.imax .zero .zero))) :=
  VEnv.HasType.forallE natN_tyR <|
    VEnv.HasType.forallE
      (VEnv.HasType.app (B := .sort .zero) (VEnv.HasType.bvar (.succ (.succ .zero)))
        (VEnv.HasType.bvar .zero))
      (VEnv.HasType.app (B := .sort .zero) (VEnv.HasType.bvar (.succ (.succ (.succ .zero))))
        (VEnv.HasType.app (B := natTy) natS_tyR (VEnv.HasType.bvar (.succ .zero))))

open Pattern.RHS (fixed) in
/-- The zero rule is typed: at the generic redex `rec C hz hs zero`, redex and reduct have
the type `C zero` over the context of the motive and the two minors. -/
theorem natDecl_patTyped0 (hc : natRule0Rhs.Closed) :
    natEnvR.PatTyped (SimplePattern.iota natR 3 natZ 0).toPattern
      (SimplePattern.iotaRHS natR natZ 0 1 2 0 0 0 natRule0Rhs hc, .true) := by
  obtain ⟨g1, hm1, hg1⟩ :=
    Pattern.matches_varN_const (c := natR) (ls := []) 3 [.bvar 2, .bvar 1, .bvar 0] rfl
  obtain ⟨g2, hm2, hg2⟩ := Pattern.matches_varN_const (c := natZ) (ls := []) 0 [] rfl
  have happly : Pattern.RHS.apply (p := (SimplePattern.iota natR 3 natZ 0).toPattern)
      (VLevel.params 0) (Sum.elim g1 g2)
      (SimplePattern.iotaRHS natR natZ 0 1 2 0 0 0 natRule0Rhs hc)
      = .app (.app (.app natRule0Rhs (.bvar 2)) (.bvar 1)) (.bvar 0) :=
    SimplePattern.iotaRHS'_apply natR natZ 3 0 0 0 natRule0Rhs hc []
      (Sum.elim g1 g2) (recArgs := [.bvar 2, .bvar 1, .bvar 0]) (ctorArgs := []) rfl rfl hg1 hg2
  refine ⟨0, [natMinor1Ty, natMinor0Ty, natMotiveTy], _, Sum.elim g1 g2,
    .app (.bvar 2) natZeroV, hm1.app hm2, ?_, ?_, ?_⟩
  · have h0 : g1 (some (some none)) = .bvar 2 := hg1 0 (by omega)
    have h1 : g1 (some none) = .bvar 1 := hg1 1 (by omega)
    have h2 : g1 none = .bvar 0 := hg1 2 (by omega)
    have hR : SimplePattern.iotaRHS natR natZ 0 1 2 0 0 0 natRule0Rhs hc =
        (((fixed natRule0Rhs hc).app
          (Pattern.RHS.var (p := (SimplePattern.iota natR 3 natZ 0).toPattern)
            (Sum.inl (some (some none))))).app
          (Pattern.RHS.var (p := (SimplePattern.iota natR 3 natZ 0).toPattern)
            (Sum.inl (some none)))).app
          (Pattern.RHS.var (p := (SimplePattern.iota natR 3 natZ 0).toPattern)
            (Sum.inl none)) := rfl
    rw [show ((SimplePattern.iotaRHS natR natZ 0 1 2 0 0 0 natRule0Rhs hc,
      Pattern.Check.true).fst) = _ from hR]
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      simp only [Pattern.RHS.Uses, false_or] at hx
      rcases hx with (rfl | rfl) | rfl
      · exact ⟨2, by simp, h0⟩
      · exact ⟨1, by simp, h1⟩
      · exact ⟨0, by simp, h2⟩
    · intro x y hx hy hxy
      simp only [Pattern.RHS.Uses, false_or] at hx hy
      rcases hx with (rfl | rfl) | rfl <;> rcases hy with (rfl | rfl) | rfl
      · rfl
      · exact absurd ((h0.symm.trans hxy).trans h1) (by simp)
      · exact absurd ((h0.symm.trans hxy).trans h2) (by simp)
      · exact absurd ((h1.symm.trans hxy).trans h0) (by simp)
      · rfl
      · exact absurd ((h1.symm.trans hxy).trans h2) (by simp)
      · exact absurd ((h2.symm.trans hxy).trans h0) (by simp)
      · exact absurd ((h2.symm.trans hxy).trans h1) (by simp)
      · rfl
    · intro i hi
      simp only [List.length_cons, List.length_nil] at hi
      have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases hi3 with rfl | rfl | rfl
      · exact ⟨Sum.inl none, Or.inr rfl, h2⟩
      · exact ⟨Sum.inl (some none), Or.inl (Or.inr rfl), h1⟩
      · exact ⟨Sum.inl (some (some none)), Or.inl (Or.inl (Or.inr rfl)), h0⟩
  · exact (((natR_tyR.app (VEnv.HasType.bvar (.succ (.succ .zero)))).app
      (VEnv.HasType.bvar (.succ .zero))).app (VEnv.HasType.bvar .zero)).app natZ_tyR
  · rw [happly]
    exact ((((VEnv.HasType.lam natMotive_tyR (VEnv.HasType.lam natMinor0_tyR
      (VEnv.HasType.lam natMinor1_tyR (VEnv.HasType.bvar (.succ .zero))))).app
      (VEnv.HasType.bvar (.succ (.succ .zero)))).app
      (VEnv.HasType.bvar (.succ .zero))).app (VEnv.HasType.bvar .zero))

open Pattern.RHS (fixed) in
/-- The successor rule is typed: at the generic redex `rec C hz hs (succ n)`, redex and
reduct — the second minor applied to the field and to the recursive call — have the type
`C (succ n)` over the context of the motive, the two minors and the field. -/
theorem natDecl_patTyped1 (hc : natRule1Rhs.Closed) :
    natEnvR.PatTyped (SimplePattern.iota natR 3 natS 1).toPattern
      (SimplePattern.iotaRHS natR natS 0 1 2 0 0 1 natRule1Rhs hc, .true) := by
  obtain ⟨g1, hm1, hg1⟩ :=
    Pattern.matches_varN_const (c := natR) (ls := []) 3 [.bvar 3, .bvar 2, .bvar 1] rfl
  obtain ⟨g2, hm2, hg2⟩ :=
    Pattern.matches_varN_const (c := natS) (ls := []) 1 [.bvar 0] rfl
  have happly : Pattern.RHS.apply (p := (SimplePattern.iota natR 3 natS 1).toPattern)
      (VLevel.params 0) (Sum.elim g1 g2)
      (SimplePattern.iotaRHS natR natS 0 1 2 0 0 1 natRule1Rhs hc)
      = .app (.app (.app (.app natRule1Rhs (.bvar 3)) (.bvar 2)) (.bvar 1)) (.bvar 0) :=
    SimplePattern.iotaRHS'_apply natR natS 3 0 0 1 natRule1Rhs hc []
      (Sum.elim g1 g2) (recArgs := [.bvar 3, .bvar 2, .bvar 1]) (ctorArgs := [.bvar 0])
      rfl rfl hg1 hg2
  refine ⟨0, [natTy, natMinor1Ty, natMinor0Ty, natMotiveTy], _, Sum.elim g1 g2,
    .app (.bvar 3) (.app natSuccV (.bvar 0)), hm1.app hm2, ?_, ?_, ?_⟩
  · have h0 : g1 (some (some none)) = .bvar 3 := hg1 0 (by omega)
    have h1 : g1 (some none) = .bvar 2 := hg1 1 (by omega)
    have h2 : g1 none = .bvar 1 := hg1 2 (by omega)
    have h3 : g2 none = .bvar 0 := hg2 0 (by omega)
    have hR : SimplePattern.iotaRHS natR natS 0 1 2 0 0 1 natRule1Rhs hc =
        ((((fixed natRule1Rhs hc).app
          (Pattern.RHS.var (p := (SimplePattern.iota natR 3 natS 1).toPattern)
            (Sum.inl (some (some none))))).app
          (Pattern.RHS.var (p := (SimplePattern.iota natR 3 natS 1).toPattern)
            (Sum.inl (some none)))).app
          (Pattern.RHS.var (p := (SimplePattern.iota natR 3 natS 1).toPattern)
            (Sum.inl none))).app
          (Pattern.RHS.var (p := (SimplePattern.iota natR 3 natS 1).toPattern)
            (Sum.inr none)) := rfl
    rw [show ((SimplePattern.iotaRHS natR natS 0 1 2 0 0 1 natRule1Rhs hc,
      Pattern.Check.true).fst) = _ from hR]
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      simp only [Pattern.RHS.Uses, false_or] at hx
      rcases hx with ((rfl | rfl) | rfl) | rfl
      · exact ⟨3, by simp, h0⟩
      · exact ⟨2, by simp, h1⟩
      · exact ⟨1, by simp, h2⟩
      · exact ⟨0, by simp, h3⟩
    · intro x y hx hy hxy
      simp only [Pattern.RHS.Uses, false_or] at hx hy
      rcases hx with ((rfl | rfl) | rfl) | rfl <;> rcases hy with ((rfl | rfl) | rfl) | rfl
      · rfl
      · exact absurd ((h0.symm.trans hxy).trans h1) (by simp)
      · exact absurd ((h0.symm.trans hxy).trans h2) (by simp)
      · exact absurd ((h0.symm.trans hxy).trans h3) (by simp)
      · exact absurd ((h1.symm.trans hxy).trans h0) (by simp)
      · rfl
      · exact absurd ((h1.symm.trans hxy).trans h2) (by simp)
      · exact absurd ((h1.symm.trans hxy).trans h3) (by simp)
      · exact absurd ((h2.symm.trans hxy).trans h0) (by simp)
      · exact absurd ((h2.symm.trans hxy).trans h1) (by simp)
      · rfl
      · exact absurd ((h2.symm.trans hxy).trans h3) (by simp)
      · exact absurd ((h3.symm.trans hxy).trans h0) (by simp)
      · exact absurd ((h3.symm.trans hxy).trans h1) (by simp)
      · exact absurd ((h3.symm.trans hxy).trans h2) (by simp)
      · rfl
    · intro i hi
      simp only [List.length_cons, List.length_nil] at hi
      have hi4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hi4 with rfl | rfl | rfl | rfl
      · exact ⟨Sum.inr none, Or.inr rfl, h3⟩
      · exact ⟨Sum.inl none, Or.inl (Or.inr rfl), h2⟩
      · exact ⟨Sum.inl (some none), Or.inl (Or.inl (Or.inr rfl)), h1⟩
      · exact ⟨Sum.inl (some (some none)), Or.inl (Or.inl (Or.inl (Or.inr rfl))), h0⟩
  · exact (((natR_tyR.app (VEnv.HasType.bvar (.succ (.succ (.succ .zero))))).app
      (VEnv.HasType.bvar (.succ (.succ .zero)))).app
      (VEnv.HasType.bvar (.succ .zero))).app (natS_tyR.app (VEnv.HasType.bvar .zero))
  · rw [happly]
    have hbody : VEnv.HasType natEnvR 0
        (natTy :: natMinor1Ty :: natMinor0Ty :: natMotiveTy ::
          [natTy, natMinor1Ty, natMinor0Ty, natMotiveTy])
        (.app (.app (.bvar 1) (.bvar 0))
          (.app (.app (.app (.app (.const natR []) (.bvar 3)) (.bvar 2)) (.bvar 1)) (.bvar 0)))
        (.app (.bvar 3) (.app natSuccV (.bvar 0))) :=
      VEnv.HasType.app (B := .app (.bvar 4) (.app natSuccV (.bvar 1)))
        (VEnv.HasType.app (A := natTy)
          (B := .forallE (.app (.bvar 4) (.bvar 0)) (.app (.bvar 5) (.app natSuccV (.bvar 1))))
          (VEnv.HasType.bvar (.succ .zero)) (VEnv.HasType.bvar .zero))
        ((((natR_tyR.app (VEnv.HasType.bvar (.succ (.succ (.succ .zero))))).app
          (VEnv.HasType.bvar (.succ (.succ .zero)))).app
          (VEnv.HasType.bvar (.succ .zero))).app (VEnv.HasType.bvar .zero))
    have hrhs : VEnv.HasType natEnvR 0 [natTy, natMinor1Ty, natMinor0Ty, natMotiveTy]
        natRule1Rhs
        (.forallE natMotiveTy (.forallE natMinor0Ty (.forallE natMinor1Ty
          (.forallE natTy (.app (.bvar 3) (.app natSuccV (.bvar 0))))))) :=
      VEnv.HasType.lam natMotive_tyR (VEnv.HasType.lam natMinor0_tyR
        (VEnv.HasType.lam natMinor1_tyR (VEnv.HasType.lam natN_tyR hbody)))
    exact (((hrhs.app (VEnv.HasType.bvar (.succ (.succ (.succ .zero))))).app
      (VEnv.HasType.bvar (.succ (.succ .zero)))).app
      (VEnv.HasType.bvar (.succ .zero))).app (VEnv.HasType.bvar .zero)

theorem natDecl_wf : natDecl.WF VEnv.empty where
  types_wf := by
    intro t ht
    cases List.mem_singleton.1 ht
    exact ⟨.succ (.succ .zero), VEnv.HasType.sort (l := .succ .zero) trivial⟩
  ctors_wf := by
    intro envT h t ht c hc
    rw [natDecl_addTypes] at h; cases h
    cases List.mem_singleton.1 ht
    simp [natTypeVal] at hc
    rcases hc with rfl | rfl
    · exact ⟨.succ .zero, VEnv.HasType.const (ci := ⟨0, natSort⟩) natEnvT_N nofun rfl⟩
    · exact ⟨_, VEnv.HasType.forallE
        (VEnv.HasType.const (ci := ⟨0, natSort⟩) natEnvT_N nofun rfl)
        (VEnv.HasType.const (ci := ⟨0, natSort⟩) natEnvT_N nofun rfl)⟩
  recs_wf := by
    intro envC h r hr
    rw [show natDecl.addTypesCtors VEnv.empty = some natEnvC by
      simp [VInductDecl.addTypesCtors, natDecl_addTypes, natDecl_addCtors]] at h
    cases h
    cases List.mem_singleton.1 hr
    exact natRecTy_ty
  types_uvars := by intro t ht; cases List.mem_singleton.1 ht; rfl
  ctors_uvars := by
    intro t ht c hc; cases List.mem_singleton.1 ht
    simp [natTypeVal] at hc; rcases hc with rfl | rfl <;> rfl
  universes := by
    intro envT h
    rw [natDecl_addTypes] at h; cases h
    refine ⟨.succ .zero, ?_, ?_, ?_⟩
    · intro t ht; cases List.mem_singleton.1 ht; exact ⟨rfl, Nat.le_refl _⟩
    · intro t ht c hc i hi
      cases List.mem_singleton.1 ht
      simp [natTypeVal] at hc
      rcases hc with rfl | rfl
      · simp [natZeroVal, natTy, natDecl, VExpr.piArity] at hi
      · have : i = 0 := by
          simp [natSuccVal, natSuccTy, natTy, natDecl, VExpr.piArity] at hi; omega
        subst this
        exact ⟨natTy, rfl, .succ .zero,
          VEnv.HasType.const (ci := ⟨0, natSort⟩) natEnvT_N nofun rfl,
          fun _ => by simp [VLevel.eval, Lean.Nat.imax]⟩
    · rintro ⟨r, hr, hu⟩
      cases List.mem_singleton.1 hr
      exact absurd hu (by simp [natRecVal])
  recs_elim := by
    intro r hr
    cases List.mem_singleton.1 hr
    refine ⟨.inl rfl, ?_⟩
    intro i hi
    have : i = 0 := by simpa [natRecVal] using hi
    subst this
    exact ⟨natMotiveTy, rfl, rfl⟩
  rec_params := by intro r hr; cases List.mem_singleton.1 hr; rfl
  ctors_params := by
    intro t ht c hc; cases List.mem_singleton.1 ht
    simp [natTypeVal] at hc; rcases hc with rfl | rfl <;> rfl
  ctors_result := by
    intro t ht c hc
    cases List.mem_singleton.1 ht
    simp [natTypeVal] at hc
    rcases hc with rfl | rfl
    · exact ⟨0, rfl, [], [], rfl, rfl⟩
    · exact ⟨1, rfl, [], [], rfl, rfl⟩
  ctors_positive := by
    intro t ht c hc
    cases List.mem_singleton.1 ht
    simp [natTypeVal] at hc
    rcases hc with rfl | rfl
    · exact ⟨nofun, by intro i hi; simp [natZeroVal, natTy, natDecl, VExpr.piArity] at hi⟩
    · refine ⟨nofun, ?_⟩
      intro i hi
      have : i = 0 := by
        simp [natSuccVal, natSuccTy, natTy, natDecl, VExpr.piArity] at hi; omega
      subst this
      exact ⟨natTy, rfl, .inr ⟨nofun, natN, List.mem_singleton_self _, [], [], rfl, nofun⟩⟩
  recs_over_block := by
    intro r hr; cases List.mem_singleton.1 hr
    exact ⟨natTypeVal, List.mem_singleton_self _, rfl⟩
  rec_counts := by
    intro r hr; cases List.mem_singleton.1 hr
    refine ⟨rfl, rfl, ?_⟩
    intro t ht _; cases List.mem_singleton.1 ht; rfl
  rec_shape := by
    intro r hr; cases List.mem_singleton.1 hr
    refine ⟨rfl, ?_, ?_, 0, Nat.zero_lt_one,
      ⟨_, rfl, natN, rfl, ⟨[], rfl⟩, _, rfl, rfl⟩, rfl⟩
    · intro i hi
      have : i = 0 := by simpa [natRecVal] using hi
      subst this
      exact ⟨natMotiveTy, rfl, ⟨.zero, rfl⟩, rfl⟩
    · intro i hi
      have hi2 : i = 0 ∨ i = 1 := by simp [natRecVal] at hi; omega
      rcases hi2 with rfl | rfl
      · exact ⟨natMinor0Ty, rfl, 0, Nat.zero_lt_one, rfl⟩
      · exact ⟨natMinor1Ty, rfl, 0, Nat.zero_lt_one, rfl⟩
  rules_nodup := by
    intro r hr; cases List.mem_singleton.1 hr
    simp [natRecVal, natRule0, natRule1, natZ, natS]
  rules_ctor := by
    intro r hr ru hru
    cases List.mem_singleton.1 hr
    simp [natRecVal] at hru
    rcases hru with rfl | rfl
    · exact ⟨natTypeVal, List.mem_singleton_self _, rfl, natZeroVal,
        List.mem_cons_self .., rfl, rfl, rfl, [], [], rfl, rfl⟩
    · exact ⟨natTypeVal, List.mem_singleton_self _, rfl, natSuccVal,
        List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl, rfl, rfl, [], [], rfl, rfl⟩
  types_have_rec := by
    intro t ht; cases List.mem_singleton.1 ht
    exact ⟨natRecVal, List.mem_singleton_self _, rfl⟩
  rules_total := by
    intro r hr t ht _ c hc
    cases List.mem_singleton.1 hr; cases List.mem_singleton.1 ht
    simp [natTypeVal] at hc
    rcases hc with rfl | rfl
    · exact ⟨natRule0, List.mem_cons_self .., rfl⟩
    · exact ⟨natRule1, List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl⟩
  rule_shape := by
    intro r hr ru hru
    cases List.mem_singleton.1 hr
    simp [natRecVal] at hru
    rcases hru with rfl | rfl
    · exact ⟨0, by decide, natMinor0Ty, rfl, ⟨⟨_, rfl⟩, _, rfl, rfl⟩, Nat.zero_le _, rfl,
        [], rfl, rfl⟩
    · exact ⟨1, by decide, natMinor1Ty, rfl, ⟨⟨_, rfl⟩, _, rfl, rfl⟩, by decide, rfl,
        [_], rfl, rfl⟩
  rules_wf := by
    intro envR h r hr ru hru hc
    rw [natDecl_addTypesCtorsRecs] at h
    cases h
    cases List.mem_singleton.1 hr
    simp [natRecVal] at hru
    rcases hru with rfl | rfl
    · exact natDecl_patTyped0 hc
    · exact natDecl_patTyped1 hc

/-! ### The fixture environment -/

def natAx : Name := `Nat.stuck
def natId : Name := `Nat.idT
def natC : Name := `Nat.casesOn

def natAxTy : VExpr := .forallE (.sort .zero) (.bvar 0)
def natIdTy : VExpr := .forallE natSort natSort
def natIdBody : VExpr := .lam natSort (.bvar 0)
def natCTy : VExpr :=
  .forallE (.forallE natTy natSort)
    (.forallE natTy
      (.forallE (.app (.bvar 1) natZeroV)
        (.forallE (.forallE natTy (.app (.bvar 3) (.app natSuccV (.bvar 0))))
          (.app (.bvar 3) (.bvar 2)))))

def natAxVal : VConstVal := { uvars := 0, type := natAxTy, name := natAx }
def natIdVal : VDefVal := { uvars := 0, type := natIdTy, value := natIdBody, name := natId }
def natCVal : VConstVal := { uvars := 0, type := natCTy, name := natC }

def natEnvB : VEnv := (VEnv.empty.addInduct natDecl).getD .empty
def natEnvAx : VEnv := (natEnvB.addConst natAx natAxVal.toVConstant).getD .empty
def natEnvId0 : VEnv := (natEnvAx.addConst natId natIdVal.toVConstant).getD .empty
def natEnvId : VEnv := natEnvId0.addDefEq natIdVal.toDefEq
def natEnvCas : VEnv := (natEnvId.addConst natC natCVal.toVConstant).getD .empty

theorem natEnvB_eq : VEnv.empty.addInduct natDecl = some natEnvB := rfl
theorem natEnvAx_eq : natEnvB.addConst natAx natAxVal.toVConstant = some natEnvAx := rfl
theorem natEnvId_eq : natEnvAx.addConst natId natIdVal.toVConstant = some natEnvId0 := rfl
theorem natEnvCas_eq : natEnvId.addConst natC natCVal.toVConstant = some natEnvCas := rfl

theorem natEnvB_N : natEnvB.constants natN = some ⟨0, natSort⟩ := rfl
theorem natEnvB_Z : natEnvB.constants natZ = some ⟨0, natTy⟩ := rfl
theorem natEnvB_S : natEnvB.constants natS = some ⟨0, natSuccTy⟩ := rfl

theorem natN_tyB {Γ : List VExpr} : VEnv.HasType natEnvB 0 Γ natTy natSort :=
  VEnv.HasType.const natEnvB_N nofun rfl
theorem natZ_tyB {Γ : List VExpr} : VEnv.HasType natEnvB 0 Γ natZeroV natTy :=
  VEnv.HasType.const natEnvB_Z nofun rfl
theorem natS_tyB {Γ : List VExpr} : VEnv.HasType natEnvB 0 Γ natSuccV natSuccTy :=
  VEnv.HasType.const natEnvB_S nofun rfl

theorem natEnvB_le_Ax : natEnvB ≤ natEnvAx := VEnv.addConst_le natEnvAx_eq
theorem natEnvAx_le_Id : natEnvAx ≤ natEnvId :=
  (VEnv.addConst_le natEnvId_eq).trans VEnv.addDefEq_le
theorem natEnvId_le_Cas : natEnvId ≤ natEnvCas := VEnv.addConst_le natEnvCas_eq

theorem natAxVal_wf : natAxVal.toVConstant.WF natEnvB :=
  ⟨_, VEnv.HasType.forallE (VEnv.HasType.sort (l := .zero) trivial)
    (VEnv.HasType.bvar .zero)⟩

theorem natIdVal_wf : natIdVal.WF natEnvAx :=
  VEnv.HasType.lam (VEnv.HasType.sort (l := .succ .zero) trivial) (VEnv.HasType.bvar .zero)

theorem natCVal_wf : natCVal.toVConstant.WF natEnvId :=
  have hN : ∀ {Γ : List VExpr}, VEnv.HasType natEnvId 0 Γ natTy natSort := fun {_} =>
    natN_tyB.mono (natEnvB_le_Ax.trans natEnvAx_le_Id)
  have hZ : ∀ {Γ : List VExpr}, VEnv.HasType natEnvId 0 Γ natZeroV natTy := fun {_} =>
    natZ_tyB.mono (natEnvB_le_Ax.trans natEnvAx_le_Id)
  have hS : ∀ {Γ : List VExpr}, VEnv.HasType natEnvId 0 Γ natSuccV natSuccTy := fun {_} =>
    natS_tyB.mono (natEnvB_le_Ax.trans natEnvAx_le_Id)
  ⟨_, VEnv.HasType.forallE (VEnv.HasType.forallE hN (VEnv.HasType.sort (l := .succ .zero) trivial))
    (VEnv.HasType.forallE hN
      (VEnv.HasType.forallE
        (VEnv.HasType.app (B := natSort) (VEnv.HasType.bvar (.succ .zero)) hZ)
        (VEnv.HasType.forallE
          (VEnv.HasType.forallE hN
            (VEnv.HasType.app (B := natSort)
              (VEnv.HasType.bvar (.succ (.succ (.succ .zero))))
              (VEnv.HasType.app (B := natTy) hS (VEnv.HasType.bvar .zero))))
          (VEnv.HasType.app (B := natSort)
            (VEnv.HasType.bvar (.succ (.succ (.succ .zero))))
            (VEnv.HasType.bvar (.succ (.succ .zero)))))))⟩

/-- The fixture's declaration list: the `Nat` block, a body-less constant, a definition and
the eliminator constant. -/
theorem nat_wf'_cas :
    VEnv.WF' [.axiom natCVal, .def natIdVal, .axiom natAxVal, .induct natDecl] natEnvCas :=
  .decl (.axiom natCVal_wf natEnvCas_eq)
    (.decl (.def natIdVal_wf natEnvId_eq)
      (.decl (.axiom natAxVal_wf natEnvAx_eq)
        (.decl (.induct natDecl_wf natEnvB_eq) .empty)))

/-! ### Source terms, the compiler table and the two ι instances -/

def srcN : Expr := .const natN []
def srcZ : Expr := .const natZ []
def srcS : Expr := .const natS []
def srcC : Expr := .const natC []
def srcId : Expr := .const natId []
def srcOne : Expr := .app srcS srcZ
def vOne : VExpr := .app natSuccV natZeroV
def natFun : VExpr := .forallE natTy natTy

def natIdBodySrc : Expr := .lam `α (.sort (.succ .zero)) (.bvar 0) .default
def natBo : Name → Option Expr := fun n => if n = natId then some natIdBodySrc else none

def srcFun : Expr := .forallE `x srcN srcN .default
def srcMot1 : Expr := .lam `α srcN srcN .default
def srcMot2 : Expr := .lam `α srcN srcFun .default
def srcIdFun : Expr := .lam `x srcN (.bvar 0) .default
def srcConstFun : Expr := .lam `n srcN srcIdFun .default
def vIdFun : VExpr := .lam natTy (.bvar 0)
def vConstFun : VExpr := .lam natTy vIdFun

def natRedex1 : VExpr :=
  .app (.app (.app (.app (.const natC []) (.lam natTy natTy)) vOne) natZeroV) vIdFun
def natReduct1 : VExpr := .app vIdFun natZeroV
def natRedex2 : VExpr :=
  .app (.app (.app (.app (.app (.const natC []) (.lam natTy natFun)) vOne) vIdFun) vConstFun)
    natZeroV
def natReduct2 : VExpr := .app (.app vConstFun natZeroV) natZeroV

def natIota1 : VDefEq := ⟨0, natRedex1, natReduct1, natTy⟩
def natIota2 : VDefEq := ⟨0, natRedex2, natReduct2, natTy⟩

/-- The fixture's environment: the four declarations, plus the two ι equations of the
eliminator constant at the instances the witnesses below step at. `Nat.casesOn`'s general ι
rule is not a `VEnv.pats` entry — the pattern shape registered by `addInduct` puts the major
premise last, and `casesOn` takes it before its minors — so the fixture records the two
instances it uses as defining equations. -/
def natEnv : VEnv := (natEnvCas.addDefEq natIota1).addDefEq natIota2

theorem natEnvCas_le : natEnvCas ≤ natEnv := VEnv.addDefEq_le.trans VEnv.addDefEq_le
theorem natEnvB_le : natEnvB ≤ natEnv :=
  natEnvB_le_Ax.trans (natEnvAx_le_Id.trans (natEnvId_le_Cas.trans natEnvCas_le))

theorem natEnv_C : natEnv.constants natC = some ⟨0, natCTy⟩ := rfl
theorem natEnv_Id : natEnv.constants natId = some ⟨0, natIdTy⟩ := rfl
theorem natEnv_Ax : natEnv.constants natAx = some ⟨0, natAxTy⟩ := rfl

theorem natN_tyE {Γ : List VExpr} : VEnv.HasType natEnv 0 Γ natTy natSort :=
  natN_tyB.mono natEnvB_le
theorem natZ_tyE {Γ : List VExpr} : VEnv.HasType natEnv 0 Γ natZeroV natTy :=
  natZ_tyB.mono natEnvB_le
theorem natS_tyE {Γ : List VExpr} : VEnv.HasType natEnv 0 Γ natSuccV natSuccTy :=
  natS_tyB.mono natEnvB_le
theorem natC_ty {Γ : List VExpr} : VEnv.HasType natEnv 0 Γ (.const natC []) natCTy :=
  VEnv.HasType.const natEnv_C nofun rfl
theorem natId_ty {Γ : List VExpr} : VEnv.HasType natEnv 0 Γ (.const natId []) natIdTy :=
  VEnv.HasType.const natEnv_Id nofun rfl
theorem natOne_ty {Γ : List VExpr} : VEnv.HasType natEnv 0 Γ vOne natTy :=
  VEnv.HasType.app (B := natTy) natS_tyE natZ_tyE
theorem natFun_ty {Γ : List VExpr} : VEnv.HasType natEnv 0 Γ natFun natSort :=
  VEnv.IsDefEq.defeqDF
    (VEnv.IsDefEq.sortDF (l := .imax (.succ .zero) (.succ .zero)) (l' := .succ .zero)
      ⟨trivial, trivial⟩ trivial (by simp [VLevel.equiv_def, VLevel.eval, Lean.Nat.imax]))
    (VEnv.HasType.forallE natN_tyE natN_tyE)

theorem trExprS_N {Δ : VLCtx} : TrExprS natEnv [] Δ srcN natTy := .const rfl rfl rfl
theorem trExprS_Z {Δ : VLCtx} : TrExprS natEnv [] Δ srcZ natZeroV := .const rfl rfl rfl
theorem trExprS_S {Δ : VLCtx} : TrExprS natEnv [] Δ srcS natSuccV := .const rfl rfl rfl
theorem trExprS_C {Δ : VLCtx} : TrExprS natEnv [] Δ srcC (.const natC []) := .const rfl rfl rfl
theorem trExprS_Id {Δ : VLCtx} : TrExprS natEnv [] Δ srcId (.const natId []) := .const rfl rfl rfl
theorem trExprS_one {Δ : VLCtx} : TrExprS natEnv [] Δ srcOne vOne :=
  .app (B := natTy) natS_tyE natZ_tyE trExprS_S trExprS_Z
theorem trExprS_fun {Δ : VLCtx} : TrExprS natEnv [] Δ srcFun natFun :=
  .forallE ⟨_, natN_tyE⟩ ⟨_, natN_tyE⟩ trExprS_N trExprS_N

/-! ### The three readings and the eliminator's segmentation, off the fixture's own list -/

/-- The fixture's λ□ inductive identifier. -/
def natIid : InductiveId := ⟨indBlockKername [natN], 0⟩

theorem nat_decl_mem :
    VDecl.induct natDecl ∈
      [VDecl.axiom natCVal, .def natIdVal, .axiom natAxVal, .induct natDecl] :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

theorem nat_ctorOf_zero : CtorOf natEnv natZ natN 0 :=
  ⟨_, _, natDecl, natTypeVal, natZeroVal, nat_wf'_cas, nat_decl_mem, natEnvCas_le,
    List.mem_singleton_self _, rfl, rfl, rfl⟩

theorem nat_ctorOf_succ : CtorOf natEnv natS natN 1 :=
  ⟨_, _, natDecl, natTypeVal, natSuccVal, nat_wf'_cas, nat_decl_mem, natEnvCas_le,
    List.mem_singleton_self _, rfl, rfl, rfl⟩

theorem nat_indInfo : IndInfo natEnv natN natIid 0 [0, 1] :=
  ⟨_, _, natDecl, natTypeVal, nat_wf'_cas, nat_decl_mem, natEnvCas_le, rfl, rfl, rfl, rfl, rfl⟩

theorem nat_constOrigin_cas : ConstOrigin natEnv natC :=
  ⟨_, _, .axiom natCVal, nat_wf'_cas, List.mem_cons_self .., natEnvCas_le, rfl⟩

theorem nat_constOrigin_id : ConstOrigin natEnv natId :=
  ⟨_, _, .def natIdVal, nat_wf'_cas, List.mem_cons_of_mem _ (List.mem_cons_self ..),
    natEnvCas_le, rfl⟩

/-- **R17's test.** The `casesOn` of the fixture's `Nat` has one argument before the major
premise — no parameters, one motive, no indices — and one minor per constructor, read off
the inductive declaration rather than off the pattern table. -/
theorem nat_casesOnShape : CasesOnShape natEnv natC natN 1 2 :=
  ⟨rfl, rfl, _, _, natDecl, natTypeVal, nat_wf'_cas, nat_decl_mem, natEnvCas_le,
    List.mem_singleton_self _, rfl, rfl, rfl⟩

/-- Neither the tabled definition nor the body-less constant is a `casesOn` name. -/
theorem nat_not_casesOnShape {c I : Name} {dp nm : Nat} (hc : c = natId ∨ c = natAx) :
    ¬ CasesOnShape natEnv c I dp nm := by
  rintro ⟨hn, -, -⟩
  rcases hc with rfl | rfl <;> simp [isCasesOnName, lastComponent, natId, natAx] at hn

/-! ### The eliminator instances are typed and translate -/

theorem natSucc0_ty {Γ : List VExpr} :
    VEnv.HasType natEnv 0 (natTy :: Γ) (.app natSuccV (.bvar 0)) natTy :=
  VEnv.HasType.app (B := natTy) natS_tyE (VEnv.HasType.bvar .zero)

theorem hIdFun_ty {Γ : List VExpr} : VEnv.HasType natEnv 0 Γ vIdFun natFun :=
  VEnv.HasType.lam natN_tyE (VEnv.HasType.bvar .zero)

theorem hConstFun_ty {Γ : List VExpr} :
    VEnv.HasType natEnv 0 Γ vConstFun (.forallE natTy natFun) :=
  VEnv.HasType.lam natN_tyE hIdFun_ty

theorem trIdFun {Δ : VLCtx} : TrExprS natEnv [] Δ srcIdFun vIdFun :=
  .lam ⟨_, natN_tyE⟩ trExprS_N (.bvar rfl)

theorem trConstFun {Δ : VLCtx} : TrExprS natEnv [] Δ srcConstFun vConstFun :=
  .lam ⟨_, natN_tyE⟩ trExprS_N trIdFun

theorem trMot1 {Δ : VLCtx} : TrExprS natEnv [] Δ srcMot1 (.lam natTy natTy) :=
  .lam ⟨_, natN_tyE⟩ trExprS_N trExprS_N

theorem trMot2 {Δ : VLCtx} : TrExprS natEnv [] Δ srcMot2 (.lam natTy natFun) :=
  .lam ⟨_, natN_tyE⟩ trExprS_N trExprS_fun

theorem hMot1_ty {Γ : List VExpr} :
    VEnv.HasType natEnv 0 Γ (.lam natTy natTy) (.forallE natTy natSort) :=
  VEnv.HasType.lam natN_tyE natN_tyE

theorem hMot2_ty {Γ : List VExpr} :
    VEnv.HasType natEnv 0 Γ (.lam natTy natFun) (.forallE natTy natSort) :=
  VEnv.HasType.lam natN_tyE natFun_ty

theorem hMot1_beta {Γ : List VExpr} {a : VExpr} (ha : VEnv.HasType natEnv 0 Γ a natTy) :
    VEnv.IsDefEq natEnv 0 Γ (.app (.lam natTy natTy) a) natTy natSort :=
  VEnv.IsDefEq.beta natN_tyE ha

theorem hMot2_beta {Γ : List VExpr} {a : VExpr} (ha : VEnv.HasType natEnv 0 Γ a natTy) :
    VEnv.IsDefEq natEnv 0 Γ (.app (.lam natTy natFun) a) natFun natSort :=
  VEnv.IsDefEq.beta natFun_ty ha

/-- The saturated instance: `Nat.casesOn (fun _ => Nat) (succ zero) zero (fun n => n)`. -/
theorem natRedex1_tr :
    TrExprS natEnv [] [] (mkApps srcC [srcMot1, srcOne, srcZ, srcIdFun]) natRedex1 := by
  have hz' : VEnv.HasType natEnv 0 [] natZeroV (.app (.lam natTy natTy) natZeroV) :=
    VEnv.IsDefEq.defeqDF (hMot1_beta natZ_tyE).symm natZ_tyE
  have hs' : VEnv.HasType natEnv 0 []
      vIdFun (.forallE natTy (.app (.lam natTy natTy) (.app natSuccV (.bvar 0)))) :=
    VEnv.IsDefEq.defeqDF
      (VEnv.IsDefEq.forallEDF natN_tyE (hMot1_beta natSucc0_ty).symm) hIdFun_ty
  have h1 := VEnv.HasType.app (natC_ty (Γ := [])) (hMot1_ty (Γ := []))
  have h2 := VEnv.HasType.app h1 (natOne_ty (Γ := []))
  have h3 := VEnv.HasType.app h2 hz'
  exact .app h3 hs' (.app h2 hz' (.app h1 natOne_ty
    (.app natC_ty hMot1_ty trExprS_C trMot1) trExprS_one) trExprS_Z) trIdFun

theorem natReduct1_tr :
    TrExprS natEnv [] [] (.app srcIdFun srcZ) natReduct1 :=
  .app (B := natTy) hIdFun_ty natZ_tyE trIdFun trExprS_Z

theorem natEnv_defeq_iota1 : natEnv.defeqs natIota1 := Or.inr (Or.inl rfl)
theorem natEnv_defeq_iota2 : natEnv.defeqs natIota2 := Or.inl rfl
theorem natEnv_defeq_id : natEnv.defeqs natIdVal.toDefEq := Or.inr (Or.inr (Or.inl rfl))

theorem natIota1_defeq {Γ : List VExpr} :
    VEnv.IsDefEq natEnv 0 Γ natRedex1 natReduct1 natTy :=
  VEnv.IsDefEq.extra (df := natIota1) (ls := []) natEnv_defeq_iota1 (by simp) rfl

/-- The step's definitional equality at the saturated instance. -/
theorem natIota1_step :
    StepDefeq natEnv [] [] (mkApps srcC [srcMot1, srcOne, srcZ, srcIdFun])
      (.app srcIdFun srcZ) :=
  ⟨_, _, natRedex1_tr, natReduct1_tr, _, natIota1_defeq⟩

/-- The over-applied instance: the same eliminator at a function-valued motive, applied to
one argument past the node. -/
theorem natRedex2_tr :
    TrExprS natEnv [] [] (mkApps srcC [srcMot2, srcOne, srcIdFun, srcConstFun, srcZ])
      natRedex2 := by
  have hz' : VEnv.HasType natEnv 0 [] vIdFun (.app (.lam natTy natFun) natZeroV) :=
    VEnv.IsDefEq.defeqDF (hMot2_beta natZ_tyE).symm hIdFun_ty
  have hs' : VEnv.HasType natEnv 0 []
      vConstFun (.forallE natTy (.app (.lam natTy natFun) (.app natSuccV (.bvar 0)))) :=
    VEnv.IsDefEq.defeqDF
      (VEnv.IsDefEq.forallEDF natN_tyE (hMot2_beta natSucc0_ty).symm) hConstFun_ty
  have h1 := VEnv.HasType.app (natC_ty (Γ := [])) (hMot2_ty (Γ := []))
  have h2 := VEnv.HasType.app h1 (natOne_ty (Γ := []))
  have h3 := VEnv.HasType.app h2 hz'
  have h4 := VEnv.HasType.app h3 hs'
  have h4' : VEnv.HasType natEnv 0 []
      (.app (.app (.app (.app (.const natC []) (.lam natTy natFun)) vOne) vIdFun) vConstFun)
      natFun := VEnv.IsDefEq.defeqDF (hMot2_beta natOne_ty) h4
  exact .app (B := natTy) h4' natZ_tyE
    (.app h3 hs' (.app h2 hz' (.app h1 natOne_ty
      (.app natC_ty hMot2_ty trExprS_C trMot2) trExprS_one) trIdFun) trConstFun) trExprS_Z

theorem natReduct2_tr :
    TrExprS natEnv [] [] (mkApps srcConstFun [srcZ, srcZ]) natReduct2 :=
  .app (B := natTy) (VEnv.HasType.app (B := natFun) hConstFun_ty natZ_tyE) natZ_tyE
    (.app (B := natFun) hConstFun_ty natZ_tyE trConstFun trExprS_Z) trExprS_Z

theorem natIota2_defeq {Γ : List VExpr} :
    VEnv.IsDefEq natEnv 0 Γ natRedex2 natReduct2 natTy :=
  VEnv.IsDefEq.extra (df := natIota2) (ls := []) natEnv_defeq_iota2 (by simp) rfl

/-- The step's definitional equality at the over-applied instance. -/
theorem natIota2_step :
    StepDefeq natEnv [] [] (mkApps srcC [srcMot2, srcOne, srcIdFun, srcConstFun, srcZ])
      (mkApps srcConstFun [srcZ, srcZ]) :=
  ⟨_, _, natRedex2_tr, natReduct2_tr, _, natIota2_defeq⟩

/-! ### The value arms fire -/

/-- **`SEval.ctorVal` fires** at the nullary constructor. -/
theorem seval_zero {fl : SEvalFlags} : SEval natEnv natBo [] fl [] srcZ srcZ :=
  SEval.ctorVal (cn := natZ) (us := []) (args := []) (argsv := [])
    nat_ctorOf_zero nat_indInfo (by decide) rfl (fun i hi => absurd hi (by simp))

/-- **`SEval.indVal` fires**: the inductive type name is a value. -/
theorem seval_natN {fl : SEvalFlags} : SEval natEnv natBo [] fl [] srcN srcN :=
  SEval.indVal (cn := natN) (us := []) (args := []) (argsv := []) nat_indInfo rfl
    (fun i hi => absurd hi (by simp))

/-- **`SEval.ctorVal` fires at `Nat.succ`**, whose spine is exactly at its arity. -/
theorem seval_ctorVal_fires {fl : SEvalFlags} : SEval natEnv natBo [] fl [] srcOne srcOne :=
  SEval.ctorVal (cn := natS) (us := []) (args := [srcZ]) (argsv := [srcZ])
    nat_ctorOf_succ nat_indInfo (by decide) rfl (fun i hi => by
      match i, hi with
      | 0, _ => simpa using seval_zero)

/-! ### δ at a type argument, and the two ι instances -/

theorem natIdBody_ty {Γ : List VExpr} :
    VEnv.HasType natEnv 0 Γ natIdBody natIdTy :=
  VEnv.HasType.lam (VEnv.HasType.sort (l := .succ .zero) trivial) (VEnv.HasType.bvar .zero)

theorem trIdBody {Δ : VLCtx} : TrExprS natEnv [] Δ natIdBodySrc natIdBody :=
  .lam ⟨_, VEnv.HasType.sort (l := .succ .zero) trivial⟩ (.sort rfl) (.bvar rfl)

theorem natId_step :
    StepDefeq natEnv [] [] (mkApps srcId [srcN]) (mkApps natIdBodySrc [srcN]) :=
  ⟨_, _, .app (B := natSort) natId_ty natN_tyE trExprS_Id trExprS_N,
    .app (B := natSort) natIdBody_ty natN_tyE trIdBody trExprS_N,
    _, VEnv.IsDefEq.appDF
      (VEnv.IsDefEq.extra (df := natIdVal.toDefEq) (ls := []) natEnv_defeq_id (by simp) rfl)
      natN_tyE⟩

/-- **`SEval.indVal` is what a δ redex at a type argument needs**: `Nat.idT Nat` evaluates
its argument first, and the argument is the inductive type name. -/
theorem seval_indVal_fires :
    SEval natEnv natBo [] fullFlags [] (mkApps srcId [srcN]) srcN :=
  SEval.deltaC (b := natIdBodySrc) (b' := natIdBodySrc) (ups := []) (argsv := [srcN])
    rfl rfl (fun _ _ _ => nat_not_casesOnShape (.inl rfl)) rfl rfl
    (fun i hi => by match i, hi with | 0, _ => simpa using seval_natN)
    natId_step (.beta rfl (.lam ..) seval_natN seval_natN)

/-- Every λ of the fixture is a value. -/
theorem seval_lam {fl : SEvalFlags} {n : Name} {ty b : Expr} {bi : BinderInfo} :
    SEval natEnv natBo [] fl [] (.lam n ty b bi) (.lam n ty b bi) := .lam ..

/-- **`SEval.iota` fires** at the fixture's two-branch `casesOn`, at the segmentation
`CasesOnShape` reads off the block. -/
theorem seval_iota_fires :
    SEval natEnv natBo [] fullFlags []
      (mkApps srcC ([srcMot1] ++ srcOne :: ([srcZ, srcIdFun] ++ []))) srcZ := by
  refine SEval.iota (I := natN) (ctor := natS) (cus := []) (cargs := [srcZ]) (np := 0)
    (cidx := 1) (prev := [srcMot1]) (minorsv := [srcZ, srcIdFun]) (extrav := [])
    rfl nat_casesOnShape nat_constOrigin_cas nat_ctorOf_succ rfl ?_ seval_ctorVal_fires
    rfl ?_ rfl ?_ (by decide) natIota1_step (.beta rfl (.lam ..) seval_zero seval_zero)
  · intro i hi
    match i, hi with
    | 0, _ => exact seval_lam
  · intro i hi
    match i, hi with
    | 0, _ => simpa using seval_zero
    | 1, _ => exact seval_lam
  · intro i hi; exact absurd hi (by simp)

/-- **`SEval.iota` fires over-applied**: the same fixture with one argument past the node,
the shape the eraser applies outside the emitted `.case`. -/
theorem seval_iota_overapplied_fires :
    SEval natEnv natBo [] fullFlags []
      (mkApps srcC ([srcMot2] ++ srcOne :: ([srcIdFun, srcConstFun] ++ [srcZ]))) srcZ := by
  refine SEval.iota (I := natN) (ctor := natS) (cus := []) (cargs := [srcZ]) (np := 0)
    (cidx := 1) (prev := [srcMot2]) (minorsv := [srcIdFun, srcConstFun]) (extrav := [srcZ])
    rfl nat_casesOnShape nat_constOrigin_cas nat_ctorOf_succ rfl ?_ seval_ctorVal_fires
    rfl ?_ rfl ?_ (by decide) natIota2_step
    (.beta rfl (.beta rfl (.lam ..) seval_zero (.lam ..)) seval_zero seval_zero)
  · intro i hi
    match i, hi with
    | 0, _ => exact seval_lam
  · intro i hi
    match i, hi with
    | 0, _ => exact seval_lam
    | 1, _ => exact seval_lam
  · intro i hi
    match i, hi with
    | 0, _ => simpa using seval_zero

/-! ### The two refutation witnesses at the fixture -/

theorem nat_not_ctorOf_ax {I : Name} {k : Nat} : ¬ CtorOf natEnv natAx I k := by
  intro h
  obtain ⟨ci, np, nf, nind, hcst, hres⟩ := h.constant_ctorResult
  cases natEnv_Ax.symm.trans hcst
  have := (VExpr.CtorResult_iff.1 hres).2.1
  simp [natAxTy, VExpr.piBody, VExpr.headConst?, VExpr.getAppFn] at this

theorem nat_not_indInfo_ax {iid : InductiveId} {np : Nat} {nfs : List Nat} :
    ¬ IndInfo natEnv natAx iid np nfs := by
  intro h
  obtain ⟨ci, hcst, harity⟩ := h.constant_isArity
  cases natEnv_Ax.symm.trans hcst
  obtain ⟨u, hu⟩ := harity.piBody_sort
  simp [natAxTy, VExpr.piBody] at hu

/-- **The body-less constant heads no value.** `Nat.stuck` is declared, has no compiler
body, is not a constructor and is not a type name, so no spine on it evaluates. -/
theorem nat_stuck_not_value {fl : SEvalFlags} (us : List Level) (args : List Expr) (v : Expr) :
    ¬ SEval natEnv natBo [] fl [] (mkApps (.const natAx us) args) v :=
  untabled_const_not_value (by simp [natBo, natAx, natId])
    (fun _ _ => nat_not_ctorOf_ax) (fun _ _ _ => nat_not_indInfo_ax)
    (fun _ _ _ => nat_not_casesOnShape (.inr rfl)) us args v

end NatWitness

end LeanToLambdaBox
