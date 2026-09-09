import Lean4Lean.Verify.Environment.Lemmas
import Lean4Lean.Verify.Typing.Lemmas
import LeanToLambdaBox.Erases
import LeanToLambdaBox.ErasesUniform

/-!
# The projection pattern interface: the first constructed `TrProj`

At the `fee3ada` re-pin, `TrProj` (`Lean4Lean/Verify/Typing/Expr.lean`) stopped being a
`sorry` and became a real definition — a *recursor expansion*. `VExpr` has no projection
node, so a source `Expr.proj S i e` is translated to the structure's recursor applied to
the parameters, a motive, the **field selector** `fun f₀ … f_{n-1} => fᵢ`, and the major
premise.

At `6fd8a1d` that definition was **redesigned**, and this file is written against the new
shape. `TrProjCtor` is a `structure` with eight named fields over the thesis's *dependent*
motive; `TrProj` is its existential closure:

```lean
structure TrProjCtor (env : VEnv) (U : Nat) (Γ : List VExpr) (S : Name) (i : Nat)
    (e e' : VExpr) (ctorName : Name) (usS : List VLevel) (uss : Nat → List VLevel)
    (params : List VExpr) (np : Nat) (fieldTys : List VExpr) : Prop where
  pat           : ∃ r, env.pats (SimplePattern.iota (mkRecName S) (np+1+1+0) ctorName
                    (np + fieldTys.length)).toPattern r
  params_length : params.length = np
  ctor          : ∃ ci, env.constants ctorName = some ci ∧ ci.type.CtorHeaded ∧
                    ∃ cty, (ci.type.instL usS).instPis params = some cty ∧
                      fieldTys = cty.piBinders
  field_lt      : i < fieldTys.length
  minor_arity   : ∃ rci, env.constants (mkRecName S) = some rci ∧
                    rci.type.binderArity? (np+1) = some fieldTys.length
  major_ty      : env.HasType U Γ e ((VExpr.const S usS).mkApps params)
  fn_ty         : env.HasType U Γ (VExpr.projFn S usS uss params fieldTys i)
                    (.forallE ((VExpr.const S usS).mkApps params)
                      (VExpr.projMotiveBody S usS uss params fieldTys i))
  eq            : e' = .app (VExpr.projFn S usS uss params fieldTys i) e

def TrProj (env) (U) (Γ) (S) (i) (e e') : Prop :=
  ∃ ctorName usS uss params np fieldTys, TrProjCtor env U Γ S i e e' ctorName usS uss params np fieldTys
```

Three things changed that matter here. The motive is **dependent**
(`VExpr.projMotiveBody`), so `e'` is `.app (projFn …) e` and not a `mkApps` spine — every
match on the old spine was dead code. The levels are a per-field *function* `uss`, since
field `j`'s elimination level is the sort of `F_j`. And two new obligations appeared:
`ctor`, reading the field telescope off the constructor's type by `instPis`/`piBinders`,
and `minor_arity`, which is what excludes reflexive structures.

**Nobody had ever constructed one** — no `example`, no test, upstream or down. Every
downstream statement about projections was therefore possibly vacuous, and the whole
projection round rests on the answer. This file settles it: **`TrProj` is inhabited, and
so is `TrExprS` at a `.proj` node.** Upstream now settles it too, on a plain *and* a
`Sigma`-shaped dependent structure (`Tests/ProjInhabit.lean`).

## What is here

A synthetic structure, registered exactly the way `VEnv.addInduct` would register it:

```lean
structure MyProd (α : Type) where
  mk :: (fst : α) (snd : α)
```

— one parameter, one constructor, **two** fields, no indices, non-recursive: the
`is_struct` shape `register_inductive` (`Erasure.lean`) gates on, and the shape whose
recursor has `numMotives = numMinors = 1`, `numIndices = 0` — i.e. `TrProj`'s hard-wired
`np+1+1+0`.

* `envP` — a `VEnv` with `N`, `MyProd`, `MyProd.mk`, `MyProd.rec` and **one ι rule**
  registered by `VEnv.addPat`, at the honest `SimplePattern.iotaRHS` shape. Built by
  `addPat` rather than `addInduct` for the same reason `envι` (`IotaDischarge.lean`) is:
  `VEnv.Ordered` has no `addPat` clause and `addInduct_WF` is `sorry` upstream, so a
  `VEnv.WF`-carrying guard is not available at this pin and is not claimed.
* `trProjP_bvar 0/1` and `trProjP_ctor 0/1` — **four positive `TrProj` witnesses**, at a
  variable discriminant and at a saturated constructor spine `MyProd.mk N x y`, for
  *both* fields.
* `trExprSP_proj_bvar` / `trExprSP_proj_ctor` — the second half: `TrExprS` at a real
  `Expr.proj`, via `TrExprS.proj` over those witnesses.
* `trProj_refuted` — the negative polarity: no `TrProj` at a `pats`-free environment.

Since slice **P4** the file also carries the *interface* layer the round consumes:

* `ProjDefeqSpec` — the projection-reduction rule as a **named premise**, stated over
  `TrProjCtor`. It was stated that way because the upstream `TrEnv.proj_defeq` was missing
  the agreement between its two constructor names and was therefore likely unprovable as
  written; upstream adopted the correction at `b6a5a38` and **proved the result at
  `6fd8a1d`** (see §"The statement correction, and what it finally bought" below);
* `ProjDefeqSpec.of_trEnv` — the injection point, and since `6fd8a1d` a **real
  discharge**: upstream's `proj_defeq` has no `sorry` of its own, so this is no longer a
  price tag for a deferred proof but an assumption that became a theorem;
* `ProjShape` — the `rfl`-checkable per-structure certificate, and
  `ProjShape.ctorAgreement`, the accessor that supplies the arity decomposition locally.
  It gained `ival.all = [S]` at the re-pin, because the proved `proj_defeq` derives the
  recursor's telescope split from the kernel's structure facts;
* `TrExprS.proj_inv` / `proj_inv'` — total inversion at a `.proj` source, now handing
  back the six exposed expansion components as well as the constructor.

Everything here is `sorryAx`-free of its own. `ProjDefeqSpec.of_trEnv` inherits
`sorryAx` from upstream's cone — unique typing, Π-injectivity, and the single
consolidated ι obligation `VEnv.WF.patsStrong` — which is the cone every `TrEnv`-premised
result already sits in, not a projection-specific gap (audited in
`scratch/final_audit.lean`).

## The recipe, for the slices that follow

Five of the seven conjuncts are `rfl`, `VEnv.addPat_self` and `by simp`; a sixth,
`env.HasType U Γ e structTy`, is the discriminant's own typing, which every caller has
anyway and `trProjP` therefore takes as a parameter. **The whole cost is the last one,
`env.HasType U Γ e' fieldTy`**, and it decomposes as:

1. `HasType.const` for the recursor at its own type — with `ci.type.instL [] = ci.type`
   by `rfl` at a monomorphic guard.
2. Three `HasType.app` steps whose result types `B.inst a` are `rfl`-computable, so each
   intermediate type can simply be *written down*.
3. **One conversion, and it is the only interesting step.** The recursor's minor premise
   has type `∀ (f₀ f₁ : α), motive (MyProd.mk α f₀ f₁)`, while the field selector
   `fun f₀ f₁ => fᵢ` naturally has type `∀ (f₀ f₁ : α), α`. The *constant* motive
   `fun _ : MyProd N => N` makes the two definitionally equal by **one β step** under two
   `forallEDF` congruences (`hconvP`). That is the whole trick, and it is the reason a
   non-dependent structure goes through by β alone.
4. **One more β step, on the way out.** The recursor spine's own type is
   `.forallE structTy (motive #0)`, while `fn_ty` demands the *motive body* on the nose.
   One `VEnv.IsDefEq.beta` under a `forallEDF` closes it, and it is `rfl`-cheap here
   because `Nty` is closed, so `Nty.lift = Nty` and `Nty.inst d = Nty`.

**What the redesign changed about this recipe.** The dependent motive collapses at these
fixtures: `projMotiveBody … i` is `fieldTys[i]` with the *earlier projections* substituted
for the earlier field binders, and `Nty` is closed, so nothing is substituted and the
motive body is `Nty` by `rfl` at both indices. `VExpr.projFn` therefore unfolds onto the
very spine `eProj` already spelled out, and `projFnP0/1`, `projMotiveBodyP0/1` and
`eProjP0/1_eq` are all `rfl`. The two new obligations are lookups: `ctor` reads
`[Nty, Nty]` off `MKty` by `instPis`/`piBinders`, and `minor_arity` checks
`MRty.binderArity? 2 = some 2` — the minor premise binds the two fields and no
inductive-hypothesis binder.

## Scope, after the redesign

Survey item R2 asked whether the `HasType` conjunct can be met at a **dependent**
structure. Under the old constant motive the answer was "only when `fieldTys[i]` does not
mention the earlier field binders" — field `0` of anything, `Sigma.snd` of nothing. **The
redesign removed that limit**: the motive is now
`Fs[i][f_j := P_j x]`, the earlier projections substituted for the earlier fields, and
upstream inhabits it sorry-free on a `Sigma`-shaped structure (`Tests/ProjInhabit.lean`,
namespace `Dependent`). So the dependent case is in scope, and the fixtures below stay
non-dependent as a *choice of fixture* — they model the typeclass-dispatch payoff — not
as a scope boundary.

The boundary that *is* real, and that the ledger must carry, is the other one upstream
declares: `TrProjCtor` covers single-constructor types that are non-recursive,
non-indexed and non-mutual. `minor_arity` is what excludes reflexive structures (their
minor carries an extra binder), and `ival.all = [S]` is what excludes mutual ones. The
kernel's `inferProj` accepts more than this — reflexive, indexed and nested
single-constructor types included, and core's own `Lean.Language.SnapshotTree.element` is
exactly such a raw `.proj`. That is a **completeness** boundary, not a soundness one, but
it means "the `TrEnv` horizon closes" may not be written without it.

## Other scope notes

* **Monomorphic by construction.** `usS = []`, `uss = fun _ => []`, `U = 0`, `uvars = 0`
  throughout, so `instL` is the identity and no level bookkeeping appears. A
  universe-polymorphic witness would ride `TrProj.instL` (proved upstream); it is not
  needed to answer the inhabitation question and is not attempted.
* **The expansion is now determined; `params`/`fieldTys` are pinned by the kernel.**
  `fieldTys` is no longer a free existential constrained only up to defeq: `ctor` forces
  it to be the constructor's telescope instantiated at `params`, which is what makes the
  expansion a *function* of `(S, ctorName, usS, uss, params, i, e)`. `TrProj.uniq` is
  still open upstream, but for a different reason than before — the `proj` case of
  `IsDefEqE` compares two projections up to the index alone.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-! ### The guard structure

```lean
structure MyProd (α : Type) where
  mk :: (fst : α) (snd : α)
```

with a single base type `N : Type` to instantiate the parameter at. Everything is
monomorphic: the recursor's motive is fixed at `Sort 1` rather than universe-polymorphic,
which is the one place this differs from what `addInduct` would build and which costs
nothing, since `TrProj` quantifies `us` existentially and `instL []` is the identity. -/

/-- `Type`, i.e. `Sort 1`. -/
def Ty1 : VExpr := .sort (.succ .zero)

/-- The base type `N : Type` the structure parameter is instantiated at. -/
def Nty : VExpr := .const `N []

/-- The structure type constant `MyProd : Type → Type`. -/
def MPc : VExpr := .const `MyProd []

/-- The constructor `MyProd.mk : ∀ (α : Type), α → α → MyProd α`. -/
def MKc : VExpr := .const `MyProd.mk []

/-- The recursor `MyProd.rec`. -/
def MRc : VExpr := .const `MyProd.rec []

/-- `MyProd N`. -/
def PN : VExpr := .app MPc Nty

def MPty : VExpr := .forallE Ty1 Ty1

/-- `∀ (α : Type) (fst : α) (snd : α), MyProd α`. -/
def MKty : VExpr :=
  .forallE Ty1 (.forallE (.bvar 0) (.forallE (.bvar 1) (.app MPc (.bvar 2))))

/-- `∀ (α : Type) (motive : MyProd α → Type)
      (mk : ∀ (fst snd : α), motive (MyProd.mk α fst snd)) (t : MyProd α), motive t`.

The `numMotives = numMinors = 1`, `numIndices = 0` telescope `TrProj` assumes: the
argument list is `params ++ [motive, minor, major]`. -/
def MRty : VExpr :=
  .forallE Ty1
    (.forallE (.forallE (.app MPc (.bvar 0)) Ty1)
      (.forallE
        (.forallE (.bvar 1)
          (.forallE (.bvar 2)
            (.app (.bvar 2) (.app (.app (.app MKc (.bvar 3)) (.bvar 1)) (.bvar 0)))))
        (.forallE (.app MPc (.bvar 2)) (.app (.bvar 2) (.bvar 0)))))

/-- The four constants, before the ι rule is registered. -/
noncomputable def envPBase : VEnv :=
  ((((((VEnv.empty.addConst `N ⟨0, Ty1⟩).getD .empty).addConst `MyProd ⟨0, MPty⟩).getD .empty
    ).addConst `MyProd.mk ⟨0, MKty⟩).getD .empty).addConst `MyProd.rec ⟨0, MRty⟩ |>.getD .empty

theorem envPBase_N : envPBase.constants `N = some ⟨0, Ty1⟩ := by
  unfold envPBase VEnv.addConst VEnv.empty; simp

theorem envPBase_MP : envPBase.constants `MyProd = some ⟨0, MPty⟩ := by
  unfold envPBase VEnv.addConst VEnv.empty; simp

theorem envPBase_MK : envPBase.constants `MyProd.mk = some ⟨0, MKty⟩ := by
  unfold envPBase VEnv.addConst VEnv.empty; simp

theorem envPBase_MR : envPBase.constants `MyProd.rec = some ⟨0, MRty⟩ := by
  unfold envPBase VEnv.addConst VEnv.empty; simp

/-- The structure recursor's ι rule template:
`fun α motive minor fst snd => minor fst snd`. Fed to `SimplePattern.iotaRHS`, which
applies it to the recursor's `params ++ motives ++ minors` and the constructor's
**fields** (dropping the parameters) — here `[α, motive, minor] ++ [fst, snd]`. -/
def rhsP : VExpr :=
  .lam Ty1
    (.lam (.forallE (.app MPc (.bvar 0)) Ty1)
      (.lam
        (.forallE (.bvar 1)
          (.forallE (.bvar 2)
            (.app (.bvar 2) (.app (.app (.app MKc (.bvar 3)) (.bvar 1)) (.bvar 0)))))
        (.lam (.bvar 2)
          (.lam (.bvar 3)
            (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))))))

theorem rhsP_closed : rhsP.Closed := by
  unfold rhsP MKc MPc Ty1 VExpr.Closed; simp [VExpr.ClosedN]

/-- The guard environment: the four constants plus **one** ι rule, at the structure
shape `np = 1`, `nmotives = nminors = 1`, `nindices = 0`, `nfields = 2` — so the pattern
arity is `1+1+1+0` on the recursor side and `1+2` on the constructor side, which is
literally `TrProj`'s `(np+1+1+0)` / `(np+fieldTys.length)`. -/
noncomputable def envP : VEnv :=
  envPBase.addPat (SimplePattern.iota `MyProd.rec (1+1+1+0) `MyProd.mk (1+2)).toPattern
    (SimplePattern.iotaRHS `MyProd.rec `MyProd.mk 1 1 1 0 1 2 rhsP rhsP_closed, .true)

theorem envP_N : envP.constants `N = some ⟨0, Ty1⟩ := envPBase_N
theorem envP_MP : envP.constants `MyProd = some ⟨0, MPty⟩ := envPBase_MP
theorem envP_MK : envP.constants `MyProd.mk = some ⟨0, MKty⟩ := envPBase_MK
theorem envP_MR : envP.constants `MyProd.rec = some ⟨0, MRty⟩ := envPBase_MR

/-- `MyProd.rec` really is `mkRecName MyProd` — the first conjunct of `TrProj`, and the
one thing about the recursor's *name* the definition pins. -/
theorem envP_mkRecName : (`MyProd.rec : Name) = mkRecName `MyProd := rfl

/-! ### The typing kit

Everything is stated at an arbitrary `Γ`, because the two families of witnesses below
live at different contexts (`[MyProd N]` and `[N, N]`). -/

theorem hNtyP {Γ} : envP.HasType 0 Γ Nty Ty1 :=
  VEnv.HasType.const envP_N (by simp) (by simp)

theorem hMPc {Γ} : envP.HasType 0 Γ MPc MPty :=
  VEnv.HasType.const envP_MP (by simp) (by simp)

theorem hMKc {Γ} : envP.HasType 0 Γ MKc MKty :=
  VEnv.HasType.const envP_MK (by simp) (by simp)

theorem hMRc {Γ} : envP.HasType 0 Γ MRc MRty :=
  VEnv.HasType.const envP_MR (by simp) (by simp)

theorem hPN {Γ} : envP.HasType 0 Γ PN Ty1 := hMPc.app hNtyP

/-- The saturated constructor spine `MyProd.mk N #1 #0`, under two `N` binders. -/
def mkappP : VExpr := .app (.app (.app MKc Nty) (.bvar 1)) (.bvar 0)

theorem hmkappP {Γ} : envP.HasType 0 (Nty :: Nty :: Γ) mkappP PN :=
  ((hMKc.app hNtyP).app (.bvar (.succ .zero))).app (.bvar .zero)

/-- The **constant** motive `fun _ : MyProd N => N`. Constant is what makes the field
selector fit by one β step; see the module docstring, step 3. Since `7a5e96d` this is
also the only motive `TrProj` admits: it demands `.lam structTy fieldTy.lift`, which at
`structTy = PN`, `fieldTy = Nty` is this term by `rfl` (`Nty` is closed, so
`Nty.lift = Nty`). -/
def motiveP : VExpr := .lam PN Nty

theorem hMotiveP {Γ} : envP.HasType 0 Γ motiveP (.forallE PN Ty1) :=
  VEnv.HasType.lam hPN hNtyP

/-- The field selector `fun (f₀ f₁ : N) => fᵢ`, i.e. `VExpr.fieldSelector [N, N] i`. -/
def selP (i : Nat) : VExpr := VExpr.fieldSelector [Nty, Nty] i

/-- `fieldSelector`'s de Bruijn convention, checked rather than assumed: field `i` is
numbered **from the outside**, so it sits at index `n - 1 - i`. Getting this backwards
would silently select the wrong field. -/
theorem selP_zero : selP 0 = .lam Nty (.lam Nty (.bvar 1)) := rfl
theorem selP_one : selP 1 = .lam Nty (.lam Nty (.bvar 0)) := rfl

theorem hSelP0 {Γ} : envP.HasType 0 Γ (selP 0) (.forallE Nty (.forallE Nty Nty)) :=
  selP_zero ▸ VEnv.HasType.lam hNtyP (VEnv.HasType.lam hNtyP (.bvar (.succ .zero)))

theorem hSelP1 {Γ} : envP.HasType 0 Γ (selP 1) (.forallE Nty (.forallE Nty Nty)) :=
  selP_one ▸ VEnv.HasType.lam hNtyP (VEnv.HasType.lam hNtyP (.bvar .zero))

/-- The type the recursor demands of its minor premise, after the parameter and the
motive have been instantiated: `∀ (f₀ f₁ : N), (fun _ => N) (MyProd.mk N f₀ f₁)`. -/
def selTyP : VExpr := .forallE Nty (.forallE Nty (.app motiveP mkappP))

/-- **The conversion — the only non-mechanical step.** The field selector's natural type
`∀ (f₀ f₁ : N), N` is definitionally the minor premise's type, by one β step under two
`forallEDF` congruences. -/
theorem hconvP {Γ} : envP.IsDefEq 0 Γ (.forallE Nty (.forallE Nty Nty)) selTyP
    (.sort (.imax (.succ .zero) (.imax (.succ .zero) (.succ .zero)))) :=
  .forallEDF hNtyP (.forallEDF hNtyP (VEnv.IsDefEq.beta hNtyP hmkappP).symm)

/-- The translation of `MyProd.i d`: `MyProd.rec N (fun _ => N) (fun f₀ f₁ => fᵢ) d`. -/
def eProj (i : Nat) (d : VExpr) : VExpr :=
  (VExpr.const `MyProd.rec []).mkApps ([Nty] ++ [motiveP, selP i, d])

/-! The recursor spine's own type is `motive d`. `TrProj` demands `fieldTy` on the nose,
so each `hEProj*` is a `raw` derivation at `.app motiveP d` followed by one β step. The
step is cheap only because the motive is constant and `Nty` is closed, so `Nty.inst d`
is `Nty` — the same fact that makes the conversion in `hconvP` work, used on the way out
instead of on the way in. -/

theorem hEProj0raw {Γ} {d} (hd : envP.HasType 0 Γ d PN) :
    envP.HasType 0 Γ (eProj 0 d) (.app motiveP d) := by
  have h := (((hMRc.app hNtyP).app hMotiveP).app (hconvP.defeq hSelP0)).app hd
  simpa [eProj, MRc, motiveP, PN, Nty, MPc, VExpr.inst, VExpr.lift, VExpr.liftN,
    VExpr.mkApps] using h

theorem hEProj0 {Γ} {d} (hd : envP.HasType 0 Γ d PN) :
    envP.HasType 0 Γ (eProj 0 d) Nty :=
  (VEnv.IsDefEq.beta hNtyP hd).defeq (hEProj0raw hd)

theorem hEProj1raw {Γ} {d} (hd : envP.HasType 0 Γ d PN) :
    envP.HasType 0 Γ (eProj 1 d) (.app motiveP d) := by
  have h := (((hMRc.app hNtyP).app hMotiveP).app (hconvP.defeq hSelP1)).app hd
  simpa [eProj, MRc, motiveP, PN, Nty, MPc, VExpr.inst, VExpr.lift, VExpr.liftN,
    VExpr.mkApps] using h

theorem hEProj1 {Γ} {d} (hd : envP.HasType 0 Γ d PN) :
    envP.HasType 0 Γ (eProj 1 d) Nty :=
  (VEnv.IsDefEq.beta hNtyP hd).defeq (hEProj1raw hd)

/-! ### The witnesses

`TrProjCtor` is an 11-argument `structure` over the thesis's *dependent* motive
(`VExpr.projMotiveBody`) since `6fd8a1d`. At this fixture the dependency is vacuous —
both field types are the closed `N` — so the dependent motive collapses to the constant
`motiveP` and the generic builders `VExpr.projFn` / `VExpr.projMotiveBody` unfold onto
the `eProj` spine above by `rfl`. That is what makes the rebuild cheap here and is
exactly the boundary upstream's `Tests/ProjInhabit.lean` draws between its `Plain` and
`Dependent` sections. -/

/-- The per-field level list; constantly `[]` here, since this fixture's recursor is
monomorphic. In general `uss j` is field `j`'s elimination level, which is why the
redesigned relation carries a *function* rather than one level list. -/
def ussP : Nat → List VLevel := fun _ => []

/-- Field `0`'s motive body: `projFns … 0 = []`, so `projMotiveBodyOf` substitutes nothing
into the closed `N`. -/
theorem projMotiveBodyP0 : VExpr.projMotiveBody `MyProd [] ussP [Nty] [Nty, Nty] 0 = Nty := rfl

/-- Field `1`'s motive body: the earlier projection function is substituted into the closed
`N` and vanishes, so this is `N` again — the motive stays constant. -/
theorem projMotiveBodyP1 : VExpr.projMotiveBody `MyProd [] ussP [Nty] [Nty, Nty] 1 = Nty := rfl

/-- The generic builder for field `0` *is* the recursor spine of `eProj`: `mkRecName MyProd`
is `MyProd.rec`, `(const MyProd []).mkApps [Nty]` is `PN`, and the motive body is `Nty`. -/
theorem projFnP0 : VExpr.projFn `MyProd [] ussP [Nty] [Nty, Nty] 0
    = (VExpr.const `MyProd.rec []).mkApps ([Nty] ++ [motiveP, selP 0]) := rfl

/-- Same at field `1`; only the selector changes. -/
theorem projFnP1 : VExpr.projFn `MyProd [] ussP [Nty] [Nty, Nty] 1
    = (VExpr.const `MyProd.rec []).mkApps ([Nty] ++ [motiveP, selP 1]) := rfl

/-- `eProj 0 d` is the field-`0` expansion applied to the discriminant — `TrProjCtor.eq`. -/
theorem eProjP0_eq {d} : eProj 0 d = .app (VExpr.projFn `MyProd [] ussP [Nty] [Nty,Nty] 0) d := rfl

/-- `eProj 1 d` is the field-`1` expansion applied to the discriminant — `TrProjCtor.eq`. -/
theorem eProjP1_eq {d} : eProj 1 d = .app (VExpr.projFn `MyProd [] ussP [Nty] [Nty,Nty] 1) d := rfl

/-- `TrProjCtor.fn_ty` for field `0`: the spine's natural codomain `motiveP #0` is converted
to the motive body `N` by one β step under `forallEDF`. This is the field the redesign
added, and the only one that is a typing derivation rather than a lookup. -/
theorem hProjFnP0 {Γ} : envP.HasType 0 Γ (VExpr.projFn `MyProd [] ussP [Nty] [Nty,Nty] 0)
    (.forallE PN (VExpr.projMotiveBody `MyProd [] ussP [Nty] [Nty,Nty] 0)) :=
  (VEnv.IsDefEq.forallEDF hPN (VEnv.IsDefEq.beta hNtyP (.bvar .zero))).defeq
    (((hMRc.app hNtyP).app hMotiveP).app (hconvP.defeq hSelP0))

/-- `TrProjCtor.fn_ty` for field `1`. -/
theorem hProjFnP1 {Γ} : envP.HasType 0 Γ (VExpr.projFn `MyProd [] ussP [Nty] [Nty,Nty] 1)
    (.forallE PN (VExpr.projMotiveBody `MyProd [] ussP [Nty] [Nty,Nty] 1)) :=
  (VEnv.IsDefEq.forallEDF hPN (VEnv.IsDefEq.beta hNtyP (.bvar .zero))).defeq
    (((hMRc.app hNtyP).app hMotiveP).app (hconvP.defeq hSelP1))

/-- The generic introduction at field `0` of `MyProd`: any well-typed discriminant of type
`MyProd N`. -/
theorem trProjCtorP0 {Γ} {d} (hd : envP.HasType 0 Γ d PN) :
    TrProjCtor envP 0 Γ `MyProd 0 d (eProj 0 d) `MyProd.mk [] ussP [Nty] 1 [Nty, Nty] where
  pat := ⟨_, VEnv.addPat_self⟩
  params_length := rfl
  ctor := ⟨_, envP_MK, ⟨_, _, rfl⟩, _, rfl, rfl⟩
  field_lt := by decide
  minor_arity := ⟨_, envP_MR, rfl⟩
  major_ty := hd
  fn_ty := hProjFnP0
  eq := eProjP0_eq

/-- …and at field `1`, so the guard is not degenerate in `fieldSelector`'s index. -/
theorem trProjCtorP1 {Γ} {d} (hd : envP.HasType 0 Γ d PN) :
    TrProjCtor envP 0 Γ `MyProd 1 d (eProj 1 d) `MyProd.mk [] ussP [Nty] 1 [Nty, Nty] :=
  { trProjCtorP0 hd with
    field_lt := by decide
    fn_ty := hProjFnP1
    eq := eProjP1_eq }

/-- The bare `TrProj` at field `0`: the expansion data is existentially quantified. -/
theorem trProjP0 {Γ} {d} (hd : envP.HasType 0 Γ d PN) : TrProj envP 0 Γ `MyProd 0 d (eProj 0 d) :=
  ⟨_, _, _, _, _, _, trProjCtorP0 hd⟩

/-- The bare `TrProj` at field `1`. -/
theorem trProjP1 {Γ} {d} (hd : envP.HasType 0 Γ d PN) : TrProj envP 0 Γ `MyProd 1 d (eProj 1 d) :=
  ⟨_, _, _, _, _, _, trProjCtorP1 hd⟩

/-- `Γ = [p : MyProd N]` — a variable discriminant. -/
def ΓpV : List VExpr := [PN]

theorem hdV : envP.HasType 0 ΓpV (.bvar 0) PN := .bvar .zero

/-- **THE WITNESS.** `TrProj` is inhabited: the first field of `MyProd N` at a variable
discriminant. -/
theorem trProjP_bvar0 : TrProj envP 0 ΓpV `MyProd 0 (.bvar 0) (eProj 0 (.bvar 0)) :=
  trProjP0 hdV

/-- The second field — so the guard is not degenerate in `fieldSelector`'s index. -/
theorem trProjP_bvar1 : TrProj envP 0 ΓpV `MyProd 1 (.bvar 0) (eProj 1 (.bvar 0)) :=
  trProjP1 hdV

/-- `Γ = [x : N, y : N]` — the discriminant is the saturated constructor spine
`MyProd.mk N x y`, which is the shape `TrEnv.proj_defeq` and hence the whole
`ProjConsistent` discharge (slice P5) will consume. -/
def ΓpC : List VExpr := [Nty, Nty]

theorem hdC : envP.HasType 0 ΓpC mkappP PN := hmkappP

theorem trProjP_ctor0 : TrProj envP 0 ΓpC `MyProd 0 mkappP (eProj 0 mkappP) :=
  trProjP0 hdC

theorem trProjP_ctor1 : TrProj envP 0 ΓpC `MyProd 1 mkappP (eProj 1 mkappP) :=
  trProjP1 hdC

/-! ### `TrExprS` at a `.proj` node

The second half of the kill-check: the `TrExprS.proj` constructor, applied to the
witnesses above. This is `DeltaHyps.prepared`'s second conjunct in miniature — the
conjunct the projection round exists to make satisfiable. -/

/-- `Δ = [p : MyProd N]`, whose `toCtx` is `ΓpV`. -/
def ΔpV : VLCtx := [(none, .vlam PN)]

theorem ΔpV_toCtx : ΔpV.toCtx = ΓpV := rfl

/-- **The second half.** `TrExprS` accepts a real `Expr.proj`. -/
theorem trExprSP_proj_bvar :
    TrExprS envP [] ΔpV (.proj `MyProd 0 (.bvar 0)) (eProj 0 (.bvar 0)) :=
  .proj (.bvar (by rfl)) trProjP_bvar0

theorem trExprSP_proj_bvar1 :
    TrExprS envP [] ΔpV (.proj `MyProd 1 (.bvar 0)) (eProj 1 (.bvar 0)) :=
  .proj (.bvar (by rfl)) trProjP_bvar1

/-- `Δ = [x : N, y : N]`, whose `toCtx` is `ΓpC`. -/
def ΔpC : VLCtx := [(none, .vlam Nty), (none, .vlam Nty)]

theorem ΔpC_toCtx : ΔpC.toCtx = ΓpC := rfl

/-- The source-side constructor application `MyProd.mk N x y`. -/
def mkappSrc : Expr :=
  .app (.app (.app (.const `MyProd.mk []) (.const `N [])) (.bvar 1)) (.bvar 0)

theorem trExprS_mkappSrc : TrExprS envP [] ΔpC mkappSrc mkappP :=
  .app ((hMKc.app hNtyP).app (.bvar (.succ .zero))) (.bvar .zero)
    (.app (hMKc.app hNtyP) (.bvar (.succ .zero))
      (.app hMKc hNtyP
        (.const envP_MK (by simp) (by simp))
        (.const envP_N (by simp) (by simp)))
      (.bvar (by rfl)))
    (.bvar (by rfl))

/-- …and at a compound discriminant, so the `TrExprS Δ e e'` premise of `TrExprS.proj`
is doing work rather than being a variable lookup. -/
theorem trExprSP_proj_ctor :
    TrExprS envP [] ΔpC (.proj `MyProd 0 mkappSrc) (eProj 0 mkappP) :=
  .proj trExprS_mkappSrc trProjP_ctor0

/-! ### The negative polarity

Non-vacuity cuts both ways: at an environment that registers no ι rule, `TrProj` is
uninhabited — so the witnesses above are *about* the registration, not artefacts of a
degenerate definition. (This direction compiled before the witnesses did; it is the half
the earlier survey already had.) -/

theorem trProj_refuted {env : VEnv} {U Γ S i e e'}
    (hp : ∀ (p : Pattern) r, ¬ env.pats p r) : ¬ TrProj env U Γ S i e e' := by
  rintro ⟨_, _, _, _, _, _, h⟩
  obtain ⟨_, hpat⟩ := h.pat
  exact hp _ _ hpat

theorem trProj_refuted_empty {U Γ S i e e'} : ¬ TrProj .empty U Γ S i e e' :=
  trProj_refuted fun _ _ h => h

/-! ### The payoff shape: a one-field type class

`MyProd` answers the inhabitation question at the shape that stresses `fieldSelector`'s
index arithmetic (`nf = 2`). The *payoff* shape — the one the design's `OfNat.ofNat`
trace runs through — is a **type class**: two parameters, one field.

```lean
class MyOfNat (α : Type) (n : N) where
  mk :: (ofNat : α)
```

so `np = 2` and `nf = 1`, and `TrProj`'s pattern arities become `2+1+1+0` and `2+1`. The
construction is the same five `rfl`s and the same single β conversion; what it adds is
that `params` is a **two**-element list, so the `params ++ [motive, selector, major]`
append is not degenerate. `MyOfNat.ofNat`'s prepared body `fun α x self => self.1` is
`DeltaHyps.prepared`'s hard conjunct, and this is the `TrProj` it needs. -/

/-- A closed inhabitant of `N`, to instantiate the class's second (value) parameter. -/
def n0c : VExpr := .const `n0 []

def QCc : VExpr := .const `MyOfNat []
def QKc : VExpr := .const `MyOfNat.mk []
def QRc : VExpr := .const `MyOfNat.rec []

/-- `MyOfNat N n0`. -/
def QN : VExpr := .app (.app QCc Nty) n0c

def QCty : VExpr := .forallE Ty1 (.forallE Nty Ty1)

/-- `∀ (α : Type) (n : N) (ofNat : α), MyOfNat α n`. -/
def QKty : VExpr :=
  .forallE Ty1 (.forallE Nty (.forallE (.bvar 1) (.app (.app QCc (.bvar 2)) (.bvar 1))))

/-- `∀ (α : Type) (n : N) (motive : MyOfNat α n → Type)
      (mk : ∀ (ofNat : α), motive (MyOfNat.mk α n ofNat)) (t : MyOfNat α n), motive t`. -/
def QRty : VExpr :=
  .forallE Ty1
    (.forallE Nty
      (.forallE (.forallE (.app (.app QCc (.bvar 1)) (.bvar 0)) Ty1)
        (.forallE
          (.forallE (.bvar 2)
            (.app (.bvar 1) (.app (.app (.app QKc (.bvar 3)) (.bvar 2)) (.bvar 0))))
          (.forallE (.app (.app QCc (.bvar 3)) (.bvar 2)) (.app (.bvar 2) (.bvar 0))))))

noncomputable def envQBase : VEnv :=
  ((((((((VEnv.empty.addConst `N ⟨0, Ty1⟩).getD .empty).addConst `n0 ⟨0, Nty⟩).getD .empty
    ).addConst `MyOfNat ⟨0, QCty⟩).getD .empty).addConst `MyOfNat.mk ⟨0, QKty⟩).getD .empty
    ).addConst `MyOfNat.rec ⟨0, QRty⟩ |>.getD .empty

theorem envQBase_N : envQBase.constants `N = some ⟨0, Ty1⟩ := by
  unfold envQBase VEnv.addConst VEnv.empty; simp
theorem envQBase_n0 : envQBase.constants `n0 = some ⟨0, Nty⟩ := by
  unfold envQBase VEnv.addConst VEnv.empty; simp
theorem envQBase_QC : envQBase.constants `MyOfNat = some ⟨0, QCty⟩ := by
  unfold envQBase VEnv.addConst VEnv.empty; simp
theorem envQBase_QK : envQBase.constants `MyOfNat.mk = some ⟨0, QKty⟩ := by
  unfold envQBase VEnv.addConst VEnv.empty; simp
theorem envQBase_QR : envQBase.constants `MyOfNat.rec = some ⟨0, QRty⟩ := by
  unfold envQBase VEnv.addConst VEnv.empty; simp

/-- `fun α n motive minor ofNat => minor ofNat`. -/
def rhsQ : VExpr :=
  .lam Ty1
    (.lam Nty
      (.lam (.forallE (.app (.app QCc (.bvar 1)) (.bvar 0)) Ty1)
        (.lam
          (.forallE (.bvar 2)
            (.app (.bvar 1) (.app (.app (.app QKc (.bvar 3)) (.bvar 2)) (.bvar 0))))
          (.lam (.bvar 3) (.app (.bvar 1) (.bvar 0))))))

theorem rhsQ_closed : rhsQ.Closed := by
  unfold rhsQ QKc QCc Nty Ty1 VExpr.Closed; simp [VExpr.ClosedN]

/-- The class environment, with its ι rule at `np = 2`, `nfields = 1`. -/
noncomputable def envQ : VEnv :=
  envQBase.addPat (SimplePattern.iota `MyOfNat.rec (2+1+1+0) `MyOfNat.mk (2+1)).toPattern
    (SimplePattern.iotaRHS `MyOfNat.rec `MyOfNat.mk 2 1 1 0 2 1 rhsQ rhsQ_closed, .true)

theorem envQ_mkRecName : (`MyOfNat.rec : Name) = mkRecName `MyOfNat := rfl

theorem envQ_N : envQ.constants `N = some ⟨0, Ty1⟩ := envQBase_N
theorem envQ_n0 : envQ.constants `n0 = some ⟨0, Nty⟩ := envQBase_n0
theorem envQ_QC : envQ.constants `MyOfNat = some ⟨0, QCty⟩ := envQBase_QC
theorem envQ_QK : envQ.constants `MyOfNat.mk = some ⟨0, QKty⟩ := envQBase_QK
theorem envQ_QR : envQ.constants `MyOfNat.rec = some ⟨0, QRty⟩ := envQBase_QR

theorem hNtyQ {Γ} : envQ.HasType 0 Γ Nty Ty1 :=
  VEnv.HasType.const envQ_N (by simp) (by simp)
theorem hn0c {Γ} : envQ.HasType 0 Γ n0c Nty :=
  VEnv.HasType.const envQ_n0 (by simp) (by simp)
theorem hQCc {Γ} : envQ.HasType 0 Γ QCc QCty :=
  VEnv.HasType.const envQ_QC (by simp) (by simp)
theorem hQKc {Γ} : envQ.HasType 0 Γ QKc QKty :=
  VEnv.HasType.const envQ_QK (by simp) (by simp)
theorem hQRc {Γ} : envQ.HasType 0 Γ QRc QRty :=
  VEnv.HasType.const envQ_QR (by simp) (by simp)

theorem hQN {Γ} : envQ.HasType 0 Γ QN Ty1 := (hQCc.app hNtyQ).app hn0c

/-- The class instance value `MyOfNat.mk N n0 f`, under the field binder. -/
def mkappQ : VExpr := .app (.app (.app QKc Nty) n0c) (.bvar 0)

theorem hmkappQ {Γ} : envQ.HasType 0 (Nty :: Γ) mkappQ QN :=
  ((hQKc.app hNtyQ).app hn0c).app (.bvar .zero)

def motiveQ : VExpr := .lam QN Nty

theorem hMotiveQ {Γ} : envQ.HasType 0 Γ motiveQ (.forallE QN Ty1) :=
  VEnv.HasType.lam hQN hNtyQ

/-- `VExpr.fieldSelector [N] 0 = fun (f : N) => f`. -/
def selQ : VExpr := VExpr.fieldSelector [Nty] 0

theorem selQ_eq : selQ = .lam Nty (.bvar 0) := rfl

theorem hSelQ {Γ} : envQ.HasType 0 Γ selQ (.forallE Nty Nty) :=
  selQ_eq ▸ VEnv.HasType.lam hNtyQ (.bvar .zero)

theorem hconvQ {Γ} : envQ.IsDefEq 0 Γ (.forallE Nty Nty)
    (.forallE Nty (.app motiveQ mkappQ))
    (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .forallEDF hNtyQ (VEnv.IsDefEq.beta hNtyQ hmkappQ).symm

/-- `MyOfNat.ofNat`'s translation: `MyOfNat.rec N n0 (fun _ => N) (fun f => f) d`. -/
def eProjQ (d : VExpr) : VExpr :=
  (VExpr.const `MyOfNat.rec []).mkApps ([Nty, n0c] ++ [motiveQ, selQ, d])

theorem hEProjQraw {Γ} {d} (hd : envQ.HasType 0 Γ d QN) :
    envQ.HasType 0 Γ (eProjQ d) (.app motiveQ d) := by
  have h := ((((hQRc.app hNtyQ).app hn0c).app hMotiveQ).app (hconvQ.defeq hSelQ)).app hd
  simpa [eProjQ, QRc, motiveQ, QN, QCc, Nty, n0c, VExpr.inst, VExpr.lift, VExpr.liftN,
    VExpr.mkApps] using h

theorem hEProjQ {Γ} {d} (hd : envQ.HasType 0 Γ d QN) :
    envQ.HasType 0 Γ (eProjQ d) Nty :=
  (VEnv.IsDefEq.beta hNtyQ hd).defeq (hEProjQraw hd)

/-- The per-field level list; constantly `[]` here (see `ussP`). -/
def ussQ : Nat → List VLevel := fun _ => []

/-- The single field's motive body is the closed constant `N`. -/
theorem projMotiveBodyQ0 : VExpr.projMotiveBody `MyOfNat [] ussQ [Nty, n0c] [Nty] 0 = Nty := rfl

/-- The generic builder unfolds onto `eProjQ`'s recursor spine — with a **two**-element
parameter list, so the `params ++ [motive, selector]` append is not degenerate. -/
theorem projFnQ0 : VExpr.projFn `MyOfNat [] ussQ [Nty, n0c] [Nty] 0
    = (VExpr.const `MyOfNat.rec []).mkApps ([Nty, n0c] ++ [motiveQ, selQ]) := rfl

/-- `eProjQ d` is the expansion applied to the discriminant — `TrProjCtor.eq`. -/
theorem eProjQ_eq {d} : eProjQ d = .app (VExpr.projFn `MyOfNat [] ussQ [Nty, n0c] [Nty] 0) d := rfl

/-- The recursor spine's typing, before the codomain β step. -/
theorem hProjSpineQ {Γ} : envQ.HasType 0 Γ
    ((VExpr.const `MyOfNat.rec []).mkApps ([Nty, n0c] ++ [motiveQ, selQ]))
    (.forallE QN (.app motiveQ (.bvar 0))) := by
  have h := ((((hQRc (Γ := Γ)).app hNtyQ).app hn0c).app hMotiveQ).app (hconvQ.defeq hSelQ)
  simpa [QRc, motiveQ, QN, QCc, Nty, n0c, VExpr.inst, VExpr.lift, VExpr.liftN,
    VExpr.mkApps] using h

/-- `TrProjCtor.fn_ty`: one β step under `forallEDF` takes the spine's natural codomain
`motiveQ #0` to the motive body `N`. -/
theorem hProjFnQ {Γ} : envQ.HasType 0 Γ (VExpr.projFn `MyOfNat [] ussQ [Nty, n0c] [Nty] 0)
    (.forallE QN (VExpr.projMotiveBody `MyOfNat [] ussQ [Nty, n0c] [Nty] 0)) :=
  (VEnv.IsDefEq.forallEDF hQN (VEnv.IsDefEq.beta hNtyQ (.bvar .zero))).defeq hProjSpineQ

/-- The generic introduction at this class. -/
theorem trProjCtorQ {Γ} {d} (hd : envQ.HasType 0 Γ d QN) :
    TrProjCtor envQ 0 Γ `MyOfNat 0 d (eProjQ d) `MyOfNat.mk [] ussQ [Nty, n0c] 2 [Nty] where
  pat := ⟨_, VEnv.addPat_self⟩
  params_length := rfl
  ctor := ⟨_, envQ_QK, ⟨_, _, rfl⟩, _, rfl, rfl⟩
  field_lt := by decide
  minor_arity := ⟨_, envQ_QR, rfl⟩
  major_ty := hd
  fn_ty := hProjFnQ
  eq := eProjQ_eq

/-- …and the bare `TrProj`. -/
theorem trProjQ {Γ} {d} (hd : envQ.HasType 0 Γ d QN) : TrProj envQ 0 Γ `MyOfNat 0 d (eProjQ d) :=
  ⟨_, _, _, _, _, _, trProjCtorQ hd⟩

/-- `Γ = [self : MyOfNat N n0]`. -/
def ΓqV : List VExpr := [QN]

theorem hdQ : envQ.HasType 0 ΓqV (.bvar 0) QN := .bvar .zero

/-- **The payoff witness**: `TrProj` at a one-field type class with **two** parameters —
the shape `OfNat.ofNat` needs. -/
theorem trProjQ_bvar : TrProj envQ 0 ΓqV `MyOfNat 0 (.bvar 0) (eProjQ (.bvar 0)) :=
  trProjQ hdQ

/-- `Δ = [self : MyOfNat N n0]`; `self.ofNat` translates. -/
def ΔqV : VLCtx := [(none, .vlam QN)]

theorem trExprSQ_proj :
    TrExprS envQ [] ΔqV (.proj `MyOfNat 0 (.bvar 0)) (eProjQ (.bvar 0)) :=
  .proj (.bvar (by rfl)) trProjQ_bvar

/-! ### The fragment guard: a class method's body, at the empty context (slice P2)

`DeltaHyps.esrc_shape` asks two things of every body the fragment records:
`NoProjBinders` and a translation at the **empty** `VLCtx`. Until slice P2 its predicate
was `NoProj`, and no projection body could satisfy it at all. This is the check that the
weakened field is not merely weaker but *satisfiable on the intended data*: `MyOfNat.ofNat`'s
prepared body, closed, at `[]`, with the projection where the payoff needs it — the class's
parameters instantiated (`N`, `n0`) rather than abstracted, which is the one respect in
which it is smaller than the real `fun α x self => self.1`. The binder-type half of the
predicate is the interesting one: it holds because `MyOfNat N n0` is a constant
application, and it would *fail* for a body binding at a projection type — which is exactly
the boundary `NoProjBinders` was cut at. -/

/-- `fun (self : MyOfNat N n0) => self.ofNat`, as a source `Expr`. -/
def ofNatBodyQ : Expr :=
  .lam `self (.app (.app (.const `MyOfNat []) (.const `N [])) (.const `n0 []))
    (.proj `MyOfNat 0 (.bvar 0)) .instImplicit

/-- The binder type `MyOfNat N n0` translates to `QN`. -/
theorem trExprSQ_ofNatTy :
    TrExprS envQ [] [] (.app (.app (.const `MyOfNat []) (.const `N [])) (.const `n0 [])) QN :=
  .app (hQCc.app hNtyQ) hn0c
    (.app hQCc hNtyQ (.const envQ_QC (by simp) (by simp)) (.const envQ_N (by simp) (by simp)))
    (.const envQ_n0 (by simp) (by simp))

/-- …and so does the whole body, at the **empty** context. -/
theorem trExprSQ_ofNatBody :
    TrExprS envQ [] [] ofNatBodyQ (.lam QN (eProjQ (.bvar 0))) :=
  .lam ⟨_, hQN⟩ trExprSQ_ofNatTy trExprSQ_proj

/-- **`DeltaHyps.esrc_shape` is satisfiable at a genuine projection body** — the guard the
P2 weakening exists for, in the field's own shape. -/
theorem gEsrcShapeProj :
    NoProjBinders ofNatBodyQ ∧ ∃ ve, TrExprS envQ [] [] ofNatBodyQ ve :=
  ⟨⟨⟨⟨⟨⟩, ⟨⟩⟩, ⟨⟩⟩, ⟨⟩⟩, _, trExprSQ_ofNatBody⟩

/-- …and the field's **old** predicate refutes the same body, so the relaxation is what
admitted it. Together with `gEsrcShapeProj` this is the whole non-vacuity story for slice
P2 at the environment level; `ErasesUniform.noProjBinders_ofNatBody` is the syntactic half,
at the full three-binder `fun α x self => self.1`. -/
theorem gEsrcShapeProj_noProj_refuted : ¬ NoProj ofNatBodyQ := fun h => h.2

/-! ## The projection-reduction interface (slice P4)

Above, `TrProj` was shown inhabited. Here it is turned into the *interface* the
projection round consumes, in the `PatsIotaSpec` two-layer idiom: a named hypothesis
structure stating the reduction rule the discharge needs, plus a `rfl`-checkable
per-structure certificate. Neither is an axiom.

### The statement correction, and what it finally bought

**The finding, and the escalation.** `TrEnv.proj_defeq` used to read

```lean
    (hp : TrProj venv U Γ S i d e'')
    (hd : venv.IsDefEqU U Γ d ((VExpr.const ctorName cus).mkApps (params ++ fields)))
```

where `hp` carries its **own**, existentially bound constructor name — the one in the
`env.pats` membership — while `hd` supplies a *different*, universally quantified
`ctorName` for the spine `d` is defeq to. Nothing tied the two together. Since
`Pattern.Matches` on `SimplePattern.iota recName _ ctorName' _` requires the major premise
to be a spine of `ctorName'`, the reduction cannot fire without the agreement, and
recovering it from `TrEnv` + `HasType` alone is a canonicity argument rather than a
rewrite. So the statement was plausibly **unprovable, not merely unproved** — the disease
`PatsIotaSpec` was created for, in a different field — and the round escalated it as a
*statement* correction rather than a proof request.

**Upstream adopted the correction** (`b6a5a38`): `proj_defeq` was re-stated over
`TrProjCtor`, so its ι rule's constructor and its spine's head became the same name. The
proof stayed deferred, and the residual was re-analysed and reported as *not* the ι
`pat_uniq` gap but the structure-recursor telescope split: the ι pattern records only the
sum `numMotives + numMinors + numIndices`, so `(1, 1, 0)` is not recoverable from it.

**And at `6fd8a1d` upstream proved it.** The route is exactly the one that analysis
implied: stop trying to recover the split from the pattern, and take it from the
*kernel's* structure facts instead — `ival.all = [S]`, `ival.ctors = [ctorName]`,
`ival.numIndices = 0`, via the new `TrEnv.structure_rec`. `TrEnv.proj_defeq` now has no
`sorry` of its own; `Verify/Environment/Lemmas.lean` has none at all. The lengths moved
onto `ival.numParams` / `cval.numFields`, the redundant `hty` premise went (it is
`TrProjCtor.major_ty`), and a context premise `OnCtx Γ (venv.IsType U)` came in.

So the entry below inverts. `ProjDefeqSpec.of_trEnv` used to exist to *price* a gap and
was deliberately used by nothing; it is now a real discharge of an assumption this
development had carried since slice P4. What it inherits — `patsStrong`, unique typing,
Π-injectivity — is the cone every other `TrEnv`-premised result already sits in, so the
projection row stops being a *separate* upstream-gated item. Consumers may still take
`ProjDefeqSpec` as a named premise, which is the right shape for a statement about an
ambient `VEnv`; what changed is that a `TrEnv`-holding caller can now honestly discharge
it rather than assume it.

The cost is that the kernel structure facts are premises of the field, so a route that
holds no `kenv` cannot supply them — see `ProjStructFacts` and the note on
`projConsistent_of_coh` in `ProjDischarge.lean`. -/

end LeanToLambdaBox

namespace Lean4Lean

open Lean LeanToLambdaBox

/-! ### `TrProjCtor` — **upstream's, and redesigned**

`TrProjCtor` used to be *defined here* because upstream had no such thing. At `b6a5a38`
it landed in `Lean4Lean` character-identical to this file's copy, and the copy died. At
`6fd8a1d` upstream then **redesigned** it, and this file follows rather than diverging:

* `def` (an 8-argument existential) → `structure` with **11** arguments and 8 named
  fields (`pat`, `params_length`, `ctor`, `field_lt`, `minor_arity`, `major_ty`,
  `fn_ty`, `eq`). The expansion's data — `usS`, `uss`, `params`, `np`, `fieldTys` — is
  now exposed rather than existentially buried.
* The motive is the thesis's **dependent** one (`VExpr.projMotiveBody`), not the constant
  `.lam structTy fieldTy.lift`, and `e'` is `.app (VExpr.projFn …) e`, not a `mkApps`
  spine `(const recName us).mkApps (params ++ [motive, selector, e])`. Every pattern
  match on that spine was dead code and is gone.
* Consequently **dependent fields come into scope** (`Sigma.snd`), which the constant
  motive could not express; reflexive, indexed and nested single-constructor types stay
  out, excluded by `minor_arity`'s `binderArity?` rather than by the pattern key.
* `TrProj` is now *derived from* `TrProjCtor` — literally
  `∃ ctorName usS uss params np fieldTys, TrProjCtor …` — so `TrProjCtor.toTrProj` and
  `TrProj.exists_ctorName` were deleted with no replacement needed: the anonymous
  constructor introduces and `obtain` eliminates.

The fixtures above were rebuilt against this shape, on the model of upstream's own
`Tests/ProjInhabit.lean`. -/

/-! ### `TrExprS` inversion at a projection

`TrExprS.proj` is the only rule concluding at a `.proj` source, so the inversion is total
and one `cases`. The primed form hands back the constructor witness as well, which is the
shape `projConsistent_of_shape` consumes: it needs the discriminant's translation *and* a
name to instantiate `ProjDefeqSpec` at. -/

theorem TrExprS.proj_inv {env : VEnv} {Us : List Name} {Δ : VLCtx} {S : Name} {i : Nat}
    {e : Expr} {e'' : VExpr} (h : TrExprS env Us Δ (.proj S i e) e'') :
    ∃ e', TrExprS env Us Δ e e' ∧ TrProj env Us.length Δ.toCtx S i e' e'' := by
  cases h with | proj hd hp => exact ⟨_, hd, hp⟩

theorem TrExprS.proj_inv' {env : VEnv} {Us : List Name} {Δ : VLCtx} {S : Name} {i : Nat}
    {e : Expr} {e'' : VExpr} (h : TrExprS env Us Δ (.proj S i e) e'') :
    ∃ (e' : VExpr) (c : Name) (usS : List VLevel) (uss : Nat → List VLevel)
      (params : List VExpr) (np : Nat) (fieldTys : List VExpr),
      TrExprS env Us Δ e e' ∧
        TrProjCtor env Us.length Δ.toCtx S i e' e'' c usS uss params np fieldTys := by
  obtain ⟨e', hd, c, usS, uss, params, np, fieldTys, hpc⟩ := h.proj_inv
  exact ⟨e', c, usS, uss, params, np, fieldTys, hd, hpc⟩

end Lean4Lean

namespace LeanToLambdaBox

open Lean Lean4Lean

/-- **The projection-reduction interface.** `TrEnv.proj_defeq`'s statement, verbatim.

Stated at a `VEnv` with `safety`/`kenv` as parameters — the same discipline
`SEvalDataι_defeq`'s docstring records for `IotaConsistent` — except that the kernel
*structure facts* are now premises of the field itself, because that is what upstream's
proof consumes. See the section docstring for why they replaced the telescope split.

A `Prop` **hypothesis**, and since `6fd8a1d` one with a real discharge below. -/
structure ProjDefeqSpec (safety : DefinitionSafety) (kenv : Lean.Kernel.Environment)
    (venv : VEnv) : Prop where
  /-- A projection whose discriminant is definitionally a saturated spine of *its own
  structure's* constructor is definitionally the spine's `i`-th field.

  The constructor agreement this field used to have to *assume* — that the name heading
  the spine is the one the `TrProjCtor` witness carries — is now structural: `hp` exposes
  `ctorName` and `hd` is stated at the same name. What replaced the old `np`/`nf` and the
  un-recoverable `(1 motive, 1 minor, 0 indices)` telescope split are the kernel's own
  structure facts (`hS`, `hall`, `hctors`, `hnind`, `hctor`), which is exactly what
  `inferProj` and `reduceProjCore` establish before they accept a projection, and the
  lengths are read off `ival.numParams` / `cval.numFields` rather than free variables.
  `hty` is gone: it is subsumed by `TrProjCtor.major_ty`. -/
  proj_defeq : ∀ {U : Nat} {Γ : List VExpr} {S ctorName : Name} {i : Nat}
      {ival : InductiveVal} {cval : ConstructorVal}
      {usS : List VLevel} {uss : Nat → List VLevel} {params' : List VExpr} {np : Nat}
      {fieldTys : List VExpr}
      {cus : List VLevel} {params fields : List VExpr} {d e'' : VExpr},
    OnCtx Γ (venv.IsType U) →
    TrProjCtor venv U Γ S i d e'' ctorName usS uss params' np fieldTys →
    kenv.find? S = some (.inductInfo ival) →
    ival.all = [S] → ival.ctors = [ctorName] → ival.numIndices = 0 →
    kenv.find? ctorName = some (.ctorInfo cval) →
    venv.IsDefEqU U Γ d ((VExpr.const ctorName cus).mkApps (params ++ fields)) →
    params.length = ival.numParams →
    ∀ (hflen : fields.length = cval.numFields) (hi : i < cval.numFields),
    venv.IsDefEqU U Γ e'' (fields[i]'(hflen ▸ hi))

/-- **The injection point, and now a real theorem.** Any `TrEnv` satisfies
`ProjDefeqSpec`, by upstream's `TrEnv.proj_defeq` — whose statement this field is,
verbatim, so the proof is the eta expansion.

**This declaration no longer carries a `sorry` of its own upstream.** At `b6a5a38`
`proj_defeq` was a corrected statement with a deferred proof, and this discharge existed
only to *price* the gap: one printed axiom set saying what accepting the deferred proof
would cost. At `6fd8a1d` upstream **proved it** (`Verify/Environment/Lemmas.lean`, a file
with zero `sorry`s), by deriving the recursor's telescope split from the kernel's
structure facts (`TrEnv.structure_rec`) instead of trying to recover it from the ι
pattern's sum — which is precisely the residual the previous round had analysed and
reported as the blocker. The `sorryAx` it still reports is *inherited*, from unique
typing, Π-injectivity and the single consolidated ι obligation `VEnv.WF.patsStrong`;
upstream pins that cone itself in `Tests/ProjInhabit.lean`.

So this is an assumption that became a theorem. Consumers may keep taking
`ProjDefeqSpec` as a hypothesis — that is still the honest shape for a statement about
an ambient `VEnv` — but the row is no longer *upstream-gated*: a `TrEnv`-holding caller
can discharge it, and the trust ledger's projection entry moves from "priced, not paid"
to the general `patsStrong`/injectivity cone every other `TrEnv` result already sits in. -/
theorem ProjDefeqSpec.of_trEnv {safety : DefinitionSafety} {kenv : Lean.Kernel.Environment}
    {venv : VEnv} (H : TrEnv safety kenv venv) : ProjDefeqSpec safety kenv venv :=
  ⟨fun hΓ hp hS hall hctors hnind hctor hd hlen hflen hi =>
    H.proj_defeq hΓ hp hS hall hctors hnind hctor hd hlen hflen hi⟩

/-- **Per-structure shape certificate** — `IotaShape`'s analogue, and much smaller: four
kernel lookups and no `Expr` equation at all, because a projection's reduct is a *subterm*
of the redex rather than a rule template that has to be β-normalised.
`rfl`/`decide`-checkable for any concrete structure; nothing in it is a typing or
translation assumption.

`ival.all = [S]` (the block is `S` alone, i.e. non-mutual) joined the certificate at the
`6fd8a1d` re-pin: upstream's now-proved `TrEnv.proj_defeq` derives the recursor's
`(1 motive, 1 minor, 0 indices)` split from the kernel's structure facts rather than from
the ι pattern's sum, and non-mutuality is one of the three it reads. It is `rfl`-checkable
like the rest.

`ival.ctors = [ctor]` is the load-bearing conjunct: it is `register_inductive`'s own
`is_struct` gate (`inf.ctors.length == 1`), it is what makes the target rule's hard-wired
constructor index `0` correct, and it is what discharges `ProjDefeqSpec`'s agreement
premise locally — a structure has exactly one constructor, so the `TrProjCtor` witness's
name and the spine's head are the same name.

The `kenv.find?` conjuncts are not constructible in-logic (a `Kernel.Environment` is
opaque), which is the same documented boundary `IotaShape` has; what *is* guarded is the
`Γ` half, and `ProjShape.ctorAgreement` below is the accessor the discharge uses. -/
structure ProjShape (safety : DefinitionSafety) (kenv : Lean.Kernel.Environment)
    (Γ : ErasureCtx) : Prop where
  shape : ∀ {S : Name} {iid : InductiveId} {np nf : Nat},
    Γ.projs S = some (iid, np) → Γ.ctorFields iid = some [nf] →
    ∃ (ival : InductiveVal) (ctor : Name) (cval : ConstructorVal),
      kenv.find? S = some (.inductInfo ival) ∧
      ival.all = [S] ∧
      ival.ctors = [ctor] ∧ ival.numParams = np ∧ ival.numIndices = 0 ∧
      ival.isRec = false ∧
      kenv.find? ctor = some (.ctorInfo cval) ∧
      cval.numParams = np ∧ cval.numFields = nf ∧
      Γ.ctors ctor = some (iid, 0) ∧ Γ.ctorArities ctor = some (np + nf) ∧
      safety ≤ (Lean.ConstantInfo.inductInfo ival).safety

/-- **The agreement, read off the certificate.** The `Γ`-side half of `ProjShape`: the
structure's unique constructor, registered at index `0` with arity `np + nf`. This is what
`projConsistent_of_shape` (slice P5) instantiates `ProjDefeqSpec`'s `ctorName` at, and it
is the step that has no ι analogue — the ι discharge had to *build* its reduct's
translation by application generation, whereas a projection's reduct is a subterm. -/
theorem ProjShape.ctorAgreement {safety : DefinitionSafety}
    {kenv : Lean.Kernel.Environment} {Γ : ErasureCtx} (h : ProjShape safety kenv Γ)
    {S : Name} {iid : InductiveId} {np nf : Nat}
    (hs : Γ.projs S = some (iid, np)) (hnfs : Γ.ctorFields iid = some [nf]) :
    ∃ ctor : Name, Γ.ctors ctor = some (iid, 0) ∧ Γ.ctorArities ctor = some (np + nf) := by
  obtain ⟨ival, ctor, cval, -, -, -, -, -, -, -, -, -, hc, har, -⟩ := h.shape hs hnfs
  exact ⟨ctor, hc, har⟩

/-! ### Guards for the interface

`ProjDefeqSpec` cannot be *constructed* — that is the point of a named premise, and the
one implementation is upstream's deferred lemma. What can be guarded, and what matters, is
that it does not quantify over an empty domain: its premise `TrProjCtor` is inhabited, at
both fixtures above and at both polarities. -/

/-- **`TrProjCtor` is inhabited** — the witness with its constructor *and its expansion
data* named, at `MyProd`'s first field. Since the redesign this exposes six components
(`ctorName`, `usS`, `uss`, `params`, `np`, `fieldTys`) rather than the constructor
alone. -/
theorem trProjCtorP_bvar0 :
    TrProjCtor envP 0 ΓpV `MyProd 0 (.bvar 0) (eProj 0 (.bvar 0)) `MyProd.mk [] ussP
      [Nty] 1 [Nty, Nty] :=
  trProjCtorP0 hdV

/-- …and at the payoff shape, the two-parameter one-field class. This is the
`ProjDefeqSpec` instance the `OfNat.ofNat` trace runs through. -/
theorem trProjCtorQ_bvar :
    TrProjCtor envQ 0 ΓqV `MyOfNat 0 (.bvar 0) (eProjQ (.bvar 0)) `MyOfNat.mk [] ussQ
      [Nty, n0c] 2 [Nty] :=
  trProjCtorQ hdQ

/-- The forgetful direction lands back on `TrProj`. `TrProjCtor.toTrProj` was deleted
upstream and needs no replacement: `TrProj` *is* the existential closure, so this is the
anonymous constructor. -/
example : TrProj envP 0 ΓpV `MyProd 0 (.bvar 0) (eProj 0 (.bvar 0)) :=
  ⟨_, _, _, _, _, _, trProjCtorP_bvar0⟩

/-- …and the naming direction recovers the constructor from the bare witness, by `obtain`
rather than by the deleted `TrProj.exists_ctorName`. -/
example : ∃ c usS uss params np fieldTys,
    TrProjCtor envP 0 ΓpV `MyProd 0 (.bvar 0) (eProj 0 (.bvar 0)) c usS uss params np fieldTys :=
  trProjP_bvar0

/-- The negative polarity travels too: at a `pats`-free environment no `TrProjCtor`
exists, for any constructor name or expansion data. `TrProj` is now literally the
existential closure of `TrProjCtor`, so the forgetful direction is the anonymous
constructor and needs no `toTrProj`. -/
theorem trProjCtor_refuted {env : VEnv} {U Γ S i e e' c usS uss params np fieldTys}
    (hp : ∀ (p : Pattern) r, ¬ env.pats p r) :
    ¬ TrProjCtor env U Γ S i e e' c usS uss params np fieldTys :=
  fun h => trProj_refuted hp ⟨_, _, _, _, _, _, h⟩

/-- **`ProjShape`'s `Γ`-side conjuncts fire** at `Γproj` (`Erases.lean`), the
one-parameter one-field structure fixture: its unique constructor is registered at index
`0` with arity `1 + 1`. The `kenv.find?` half is the documented in-logic boundary
(`IotaShape` has the same one), so what a guard can show is that the certificate's `Γ`
demands are the ones registration actually meets — non-degenerately, since a
`paramCount`/`fieldIdx` confusion would give `2 ≠ 1 + 1`. -/
example : Γproj.ctors `AC.mk = some (projInd, 0) ∧ Γproj.ctorArities `AC.mk = some (1 + 1) :=
  ⟨Γproj_ctors, Γproj_arity⟩

/-- **`TrExprS.proj_inv'` fires**, and hands back exactly what the discharge asks for: the
discriminant's translation, the constructor name and — since the redesign — the expansion
data the reduction is stated over. -/
example : ∃ (e' : VExpr) (c : Name) (usS : List VLevel) (uss : Nat → List VLevel)
    (params : List VExpr) (np : Nat) (fieldTys : List VExpr),
    TrExprS envQ [] ΔqV (.bvar 0) e' ∧
      TrProjCtor envQ 0 ΔqV.toCtx `MyOfNat 0 e' (eProjQ (.bvar 0)) c usS uss params np fieldTys :=
  trExprSQ_proj.proj_inv'

end LeanToLambdaBox

