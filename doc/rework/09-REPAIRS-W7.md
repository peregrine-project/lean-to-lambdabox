# 09 — W7, the level scope and the closing of `hbridge`

W6 left `shipping_erase_correct_firstorder` with one class-**C** binder of this repository's
own making, `hbridge`, carrying two fields — `erasesEnv : ErasesEnv env tbl.body? Γspec t₀` and
`lowerEnv : LowerEnv Γspec Γ` — and `doc/rework/08-REPAIRS-W5.md` §2 as the statement that
would discharge them. This document does two things. §1 records a defect found while preparing
that discharge: one clause of `ErasesEnv` is *unsatisfiable* at a tabled constant whose compiler
body is universe-polymorphic, which is five of the eight rungs, so those five rungs say nothing.
§2 is the unit specification that repairs it and closes `hbridge`, nine units, with the exact
statement of each. §3 says what closing `hbridge` does and does not buy.

Every signature in §2 elaborates at this toolchain against the tree at the W6 checkpoint; the
probes are `scratch/round7/w7_sigs.lean` (the signatures, as `sorry`-stubs) and
`scratch/round7/w7_meas.lean` (the measurements and the two refutations), cited by basename.
Scratch probes are untracked; the one regression that outlives the wave is tracked, as
`test/Vacuity.lean`.

## 1. The finding: `ErasesEnv.defns` asks for more than any environment can give

### 1.1 The clause

`LeanToLambdaBox/ErasesEnv.lean:51-53`, the fourth clause of `ErasesEnv`:

```lean
(defns : ∀ c b, bo c = some b → ReachableFrom Γspec t (toKername c) →
  ∃ b₀, LBTerm.envLookup Γspec (toKername c) = some (.constantDecl ⟨some b₀⟩) ∧
    ∀ Us' ups us, Erases env Us' [] (b.instantiateLevelParams ups us) b₀)
```

Read the quantifier at `Us' = ups = us = []`. The instantiation is then the identity, and the
demand is `Erases env [] [] b b₀` — an erasure of the tabled body **at the empty level scope**.
For a body that binds a universe-polymorphic argument there is none:

```lean
theorem no_erases_lam_sort_param {env : VEnv} {n u : Name} {b : Expr} {bi : BinderInfo}
    {t : LBTerm} : ¬ Erases env [] [] (.lam n (.sort (.succ (.param u))) b bi) t
```

`Erases` has exactly two arms at a λ source (`Erases.lean:246`, `:216`): `lam`, whose `hty` is
the domain's translation, and `box`, whose `htr` carries the domain's translation through
`TrExprS.lam`. Both need `VLevel.ofLevel [] (.succ (.param u))`, which is `none`. The lemma is
`test/Vacuity.lean`, `[propext, Classical.choice, Quot.sound]`, no `sorry`.

This is a defect of the **verification**, not of the eraser. The eraser erases each member body
under `withReader (… lparams := ci.levelParams)` (`Erasure.lean:889`, `:912`) — at the
declaration's own level scope, which is exactly where the clause should have asked. The clause
was written scope-independent because the eighteen bridge motives are stated at one fixed `Us`
(`BridgeInv.lparams`, `Bridge.lean:323`), and universal quantification was the way to make the
environment relation not mention a scope. Universal quantification over instantiations is what
makes it unsatisfiable.

### 1.2 The five rungs

`green_G2`, `green_G3`, `green_G4`, `green_G7` and `green_G8` (`Green.lean:363`, `:464`, `:585`,
`:1436`, `:1495`) carry `ErasesEnv env g<i>Table.body? Γspec t₀` **in their conclusion**, so the
conclusion is what dies, not only a binder: a theorem whose conclusion is unsatisfiable is
vacuous however its hypotheses are read. Two measurements, and one gap between them.

Tabled bodies per rung (`w7_meas.lean`, `#eval`; `polyBodied` is a bodied declaration whose
`levelParams` is non-empty, `maxLevels` a bodied declaration outside the `max`-free fragment):

| rung | decls | bodied | polyBodied | maxLevels | reached, bodied and polymorphic |
|---|---|---|---|---|---|
| G1 | 3 | 1 | 0 | 0 | **0** |
| G2 | 6 | 3 | 1 | 0 | **1** — `OfNat.ofNat` |
| G3 | 6 | 3 | 1 | 0 | **1** — `OfNat.ofNat` |
| G4 | 8 | 4 | 2 | 0 | **2** — `OfNat.ofNat`, `Prod.fst` |
| G5 | 7 | 3 | 0 | 0 | **0** |
| G6 | 5 | 2 | 0 | 0 | **0** |
| G7 | 44 | 30 | 16 | 0 | **15** — the sixteen below, less `outParam` |
| G8 | 43 | 29 | 16 | 0 | **15** — the same |

G7's sixteen, with their level columns: `Add.add [u]`, `HAdd.hAdd [u,v,w]`, `HMul.hMul [u,v,w]`,
`HPow.hPow [u,v,w]`, `HSub.hSub [u,v,w]`, `Mul.mul [u]`, `NatPow.pow [u]`, `OfNat.ofNat [u]`,
`Pow.pow [u,v]`, `Sub.sub [u]`, `instHAdd [u_1]`, `instHMul [u_1]`, `instHPow [u_1,u_2]`,
`instHSub [u_1]`, `instPowNat [u_1]`, `outParam [u]`. Every one of them is a λ whose head domain
is `Expr.sort (Level.succ (Level.param _))` — `no_erases_lam_sort_param`'s shape exactly. The
last column is the reachability measurement of `scratch/round7/p_levels.lean`, re-taken at
kernel grade for six instances in `scratch/round7/r4.lean` (`ReachableFrom g<i>Env g<i>Term
(toKername ``OfNat.ofNat)` and `… ``HAdd.hAdd`, `by decide`, clean axioms).

**The gap, stated plainly.** The refutation needs reachability *in `Γspec` at `t₀`*; what is
measured is reachability *in `Γ` at `t`*. The transfer is not a tracked lemma, and the general
form of it is **false**: `constRefs` counts the block name of a `.case` node
(`Output.lean:295`) while `Lower.elimApp` (`Lower.lean:368`) builds `.case` nodes where the
source spine had a `.const`, so `constRefs` is not monotone along `Lower` in either direction
— mechanised as `constRefs_not_monotone` in `scratch/round7/r2.lean`. The repaired form, with
the block-name disjunct, closes the five rungs' conclusions
(`scratch/round7/r3.lean:g2_conclusion_refuted`, clean axioms), but it is three non-trivial
obligations, and this wave does not land it: U1 deletes the clause, after which no rung depends
on the transfer at all. See the remark in §2.0.

**What is unconditional, with no reachability step at all.** `bridgeEnv_of_regInv`
(`Capstone.lean:122`) is the only route that produces the clause, and its premise

```lean
(hlp : ∀ c b, bo c = some b → b.hasLevelParam' = false ∧ NoMaxLevels b)
```

has no reachability gate, so one polymorphic tabled body refutes it: `hlp_refuted_g2`,
`hlp_refuted_g7`, `hlp_refuted_g8` (`scratch/round7/r1.lean`, `r3.lean`). So the route
`SpecContent.defns → RegInvShape'.defns → bridgeEnv_of_regInv` (`SpecEnv.lean:159`, `:180`,
`Capstone.lean:122`) is dead at G2, G3, G4, G7 and G8 whatever the reachability transfer does,
and U1 is needed either way. *Evidence caveat:* `Expr.hasLevelParam'` bottoms out in
`Level.hasParam`, which reads a cached bitfield and does not reduce; the bridge to the
structural mirror is lean4lean's `Level.hasParam_eq` **axiom**
(`.lake/packages/lean4lean/Lean4Lean/Verify/Axioms.lean:279`), which the kernel-grade `hlp`
refutations therefore inherit. It is already one of the capstone's 33 names.

### 1.3 The casualties are the whole δ column, not one lemma

Every theorem taking `ErasesEnv env tbl.body? Γspec t` as a hypothesis is vacuous at any
`(tbl, Γspec, t)` whose reachability triggers the clause. That includes `erases_correct`'s
environment premise as the capstone instantiates it (`Capstone.lean:213-218`),
`ErasesEnv.runtimeKey_isCasesOn` (`ErasesCorrect/Steps.lean:800`, which spends `her [] [] []` at
`:811`), and `Green.g8_argErasesEnv` (`Green.lean:1406`, `herΓ.defns` at `:1414`). Nine `.defns`
call sites outside `ErasesEnv.lean`/`SpecEnv.lean`, all inside the simulation and the ladder.

### 1.4 What MetaRocq says instead

`../metarocq/erasure/theories/Extract.v:264-268`:

```coq
Definition erases_constant_body (Σ : global_env_ext) (cb : constant_body) (cb' : E.constant_body) :=
  match cst_body cb, E.cst_body cb' with
  | Some b, Some b' => erases Σ [] b b'
  | None, None => True
  | _, _ => False
  end.
```

and it is applied at the constant's **own** universe context, once: `erases_global_cnst` reads
`(…, cst_universes cb)` (`Extract.v:287`), and so does `erases_deps`' constant clause
(`Extract.v:324-331`), which is `ErasesEnv`'s direct analogue. There is no quantifier over
instantiations anywhere in the environment relation. The instantiated reading is a **theorem**,
`erases_subst_instance` / `erases_subst_instance_decl`
(`ErasureProperties.v:383-391`, `:412-424`), spent exactly once, in the constant case of
`erases_correct` (`ErasureCorrectness.v:176`); its box half is `isErasable_subst_instance`
(`ErasureProperties.v:262-267`). The image `t'` is unchanged by the instantiation — erasure
drops universes — and the side conditions are typing and `consistent_instance_ext`.

The project's `∀ Us' ups us` is that theorem with its side conditions deleted and pushed back
into the environment relation. Deleting them is what makes it false. The repair is to put the
clause back where MetaRocq has it and derive the instantiated form where MetaRocq derives it —
and the derivation is already in the tree: `Erases.instL` (`ErasesAbstract.lean:751`), whose
`Hls : ls.mapM (VLevel.ofLevel Us) = some ls'` *is* `consistent_instance_ext`'s content and
whose `hnm : NoMaxLevels e` is the project's own `max`-free fragment restriction, measured
satisfied by every tabled body of every rung (§1.2's `maxLevels` column, 0 everywhere).

### 1.5 The regression

`test/Vacuity.lean` holds `no_trExprS_sort_param` and `no_erases_lam_sort_param` — the general
lemma, which survives the repair — and a header comment saying why the clause-level refutation
is *not* there: after U1 the universally quantified clause does not exist, so a theorem refuting
it would not elaborate. The file compiles with `lake env lean test/Vacuity.lean` and is wired
into no script and no workflow in this wave.

## 2. The units

Gates assume the battery of `doc/rework/07-STATUS.md` §6 stays green and that the measured
axiom footprint of `shipping_erase_correct_firstorder` and of `green_G1`…`green_G8` — the
33-name cluster — does not grow. "R" needs real reasoning, "M" is mechanical.

| id | title | kind | depends |
|---|---|---|---|
| U1 | `defns` at the declaration's own level scope | R | — |
| U2 | erasure commutes with level instantiation | R | U1 |
| U3 | the binder name leaves `Erases` | M | — |
| U4 | `Erases` up to source α | M after U3 | U3 |
| U5 | the level scope inside the eighteen motives | M, large | — |
| U6 | `Γspec` as an output, and the growth relation | R | U5 |
| U7 | the preservation theorem | R | U1, U4, U6 |
| U8 | saturation at the final state | M | U7 |
| U9 | `hbridge` discharged | M | U7, U8 |

U1–U4 are this wave; U5–U9 are specified here and land later.

### 2.0 Remark: the reachability lift is not a unit

`scratch/round7/A-hbridge.md` scheduled the lift `ReachableFrom Γ t kn → ReachableFrom Γspec t₀
kn` as unit U0. It is **false** as stated (§1.2), its repaired form carries a block-name
disjunct, and its cost is three obligations, not one: an induction over `ReachableFrom`'s
`List.foldl` closure (`Output.lean:318-340`), the `LowerEnv.defs` disjunction whose second
branch routes through a lowered block's siblings (`ErasesEnv.lean:231`), and the block-name
exception itself. Nothing in §2 needs it: U1 removes the clause whose refutation wanted it. It
is recorded here so that a later round that wants reachability transfer for another reason
starts from the repaired statement and the right cost.

### 2.1 U1 — `defns` at the declaration's own level scope

**The level column.** The table already records it (`Witness/SourceTable.lean:42`,
`ReifiedDecl.levelParams`); it gains an accessor beside `SourceTable.body?`
(`Witness/SourceTable.lean:79`):

```lean
/-- The level-parameter column of the table, beside `body?`: `cst_universes` of the
declaration, which is the scope the eraser erases its body at (`Erasure.lean:889`, `:912`). -/
def SourceTable.levels? (tbl : SourceTable) (n : Name) : List Name :=
  ((tbl.decl? n).map (·.levelParams)).getD []
```

Measured: `g2Table.levels? ``OfNat.ofNat = [`u]`, `g4Table.levels? ``Prod.fst = [`u, `v]`,
`g7Table.levels? ``HAdd.hAdd = [`u, `v, `w]`, and `[]` at every monomorphic name
(`w7_sigs.lean`, three `by decide` examples; `w7_meas.lean`, the full G7 column).

**The relation.** `ErasesEnv` and `SpecContent` gain the column as a parameter, and their δ
clauses read the declaration's own scope — `erases_constant_body (Σ, cst_universes cb)`,
`Extract.v:264`:

```lean
inductive ErasesEnv (env : VEnv) (bo : Name → Option Expr) (lp : Name → List Name) :
    GlobalDeclarations → LBTerm → Prop
  | mk {Γspec : GlobalDeclarations} {t : LBTerm}
      (keys : (Γspec.map Prod.fst).Nodup)
      (deps : ∀ kn, ReachableFrom Γspec t kn → (LBTerm.envLookup Γspec kn).isSome)
      (tabled : ∀ c b, bo c = some b → ConstOrigin env c)
      (defns : ∀ c b, bo c = some b → ReachableFrom Γspec t (toKername c) →
        ∃ b₀, LBTerm.envLookup Γspec (toKername c) = some (.constantDecl ⟨some b₀⟩) ∧
          Erases env (lp c) [] b b₀)
      (axioms : …) (blocks : …) (elims : …) :
      ErasesEnv env bo lp Γspec t

structure SpecContent (env : VEnv) (bo : Name → Option Expr) (lp : Name → List Name)
    (Γspec : GlobalDeclarations) : Prop where
  keys : (Γspec.map Prod.fst).Nodup
  defns : ∀ c b, bo c = some b → (LBTerm.envLookup Γspec (toKername c)).isSome →
    ∃ b₀, LBTerm.envLookup Γspec (toKername c) = some (.constantDecl ⟨some b₀⟩) ∧
      Erases env (lp c) [] b b₀
  axioms : … blocks : … elims : …
```

The three unchanged clauses are verbatim. `SpecContent.defns`' existential `∃ Us` goes with the
change: one scope, named by the declaration, is what a run records and what the content clause
should say.

**The two derived readings.**

```lean
theorem SpecContent.erasesEnv (H : SpecContent env bo lp Γspec) {t : LBTerm}
    (hdeps : ∀ kn, ReachableFrom Γspec t kn → (LBTerm.envLookup Γspec kn).isSome)
    (htab : ∀ c b, bo c = some b → ConstOrigin env c) :
    ErasesEnv env bo lp Γspec t

theorem bridgeEnv_of_regInv (hreg : RegInvShape' env bo Γspec sf)
    (hsat : RegSaturated env Γspec sf) (hcon : SpecContent env bo lp Γspec)
    (hdeps : ∀ kn, ReachableFrom Γspec t₀ kn → (LBTerm.envLookup Γspec kn).isSome)
    (htab : ∀ c b, bo c = some b → ConstOrigin env c) :
    SpecEnv env bo sf Γspec ∧ LBWfSpec Γspec ∧
      ErasesEnv env bo lp Γspec t₀ ∧ LowerEnv Γspec sf.gdecls
```

`SpecContent.erasesEnv` loses its `hdefns` premise — the transport it existed to accept is gone
— and `bridgeEnv_of_regInv` loses `hlp` entirely, which is the point of the unit: the premise
that was refuted at five rungs is no longer asked for. `RegInvShape'.defns`
(`SpecEnv.lean:159`) collapses to `hdeps` plus the content clause and keeps its name.

**The `max`-free fragment, which does not disappear.** `hlp`'s second conjunct, `NoMaxLevels b`,
is still what `Erases.instL` needs at U2, so it moves to the table side, where it is decidable
and where the ladder already checks such clauses:

```lean
  /-- Every tabled body is in the `max`-free level fragment `Erases.instL` transports
      along. Decidable on a concrete table, like `notUnsafeRec`. -/
  noMaxLevels : ∀ (n : Name) (b : Expr), tbl.body? n = some b → NoMaxLevels b
```

as a clause of `TableSafe` (`Supported.lean:428`). Measured true at all eight rungs
(`w7_meas.lean`, `maxLevels = 0` in every row).

*Files.* `ErasesEnv.lean` (the inductive, its seven projections, `SpecContent`,
`SpecContent.erasesEnv`, the `DemoSource` fixture — whose `defnStable` field, `:374`, is the old
shape and is deleted with it), `SpecEnv.lean` (`RegInvShape'.defns`, `RegInvShape'.erasesEnv`;
`defns_needs_paramFree`, `:194`, loses its subject and is deleted), `ColdStartShape.lean`
(`mapM_ofLevel_replicate_zero`, `instantiateLevelParams_eq_self` and
`erases_any_scope_of_paramFree`, `:684-708`, lose their only consumer and are deleted unless
U2 keeps `instantiateLevelParams_eq_self` for the monomorphic route), `Capstone.lean` (`ErasureBridge`, `bridgeEnv_of_regInv`, the capstone's
`hbridge` binder), `Supported.lean` (the `TableSafe` clause), `Witness/SourceTable.lean` (the
accessor).

*Consumers to rewire.* `ErasesCorrect/Delta.lean:164-166` (the δ arm — the only site that spends
the instantiated form, and U2 is what it spends instead), `ErasesCorrect/Steps.lean:362, 398,
421, 423, 444, 445` (the five congruences, mechanical: the clause is carried, not opened),
`ErasesCorrect/Steps.lean:808` (`runtimeKey_isCasesOn`, whose proof spends `her [] [] []` and
now spends `her` directly — `erases_ne_elimBody`, `Steps.lean:785`, is scope-generic),
`VisitExprRefines/Step/Env.lean:578`, `Green.lean:1414` (`g8_argErasesEnv`), and every rung
statement, which names `ErasesEnv env g<i>Table.body? …` and gains `g<i>Table.levels?`.

*Gate.* All eight rungs elaborate; `scripts/erases_correct.sh` and `scripts/erasesLB.sh` green;
`scripts/ledger.sh` unchanged (the 33-name cluster is a footprint, and a restated hypothesis
adds no axiom); `grep -rn "instantiateLevelParams" LeanToLambdaBox/ErasesEnv.lean
LeanToLambdaBox/SpecEnv.lean` empty.

*Confidence.* The statement is satisfiable and is what the run supplies: the eraser erases each
member body at `ci.levelParams`, which is the column `reify%` records. Probe: the restated
inductive, structure and both theorems elaborate (`w7_sigs.lean`); the level columns are
`decide`-checked there; `VLevel.ofLevel [`u] (.succ (.param `u))` is `some`
(`scratch/round7/r1.lean`), so nothing in the new clause is unsatisfiable for the reason the old
one was.

### 2.2 U2 — erasure commutes with level instantiation

**Not an upstream ask.** `A-hbridge.md` flagged this unit as the likeliest new lean4lean
request. It is not: the transport is already proved in this tree, and the lean4lean side of it
is already proved at the pin.

* In-tree: `Erases.instL` (`ErasesAbstract.lean:751`) and `Erases.instL_core` (`:720`), with
  the box arm discharged by `Erasable.instL` (`:705`).
* At the pin, for the box arm's existential over `HasType`: `VEnv.HasType.instL`, `IsType.instL`
  and `IsDefEqU.instL` (`.lake/packages/lean4lean/Lean4Lean/Theory/Typing/Lemmas.lean:675`,
  `:678`, `:681`), on `IsDefEq.instL` (`:646`) and `Lookup.instL` (`:148`). Nothing is missing.

**The positional form** is `Erases.instL` at the empty local context, and it is *proved*, not
stubbed, in `w7_sigs.lean`:

```lean
/-- Erasure at the declaration's scope transports to any instantiation whose levels the
reading scope knows. The λ□ image is unchanged, as in `erases_subst_instance`
(`ErasureProperties.v:383`); `hus` is `consistent_instance_ext`'s content. -/
theorem Erases.instantiateLevelParams {env : VEnv} {ps Us : List Name} {us : List Level}
    {us' : List VLevel} {b : Expr} {b₀ : LBTerm}
    (hus : us.mapM (VLevel.ofLevel Us) = some us') (hlen : ps.length = us.length)
    (h : Erases env ps [] b b₀) (hnm : NoMaxLevels b) :
    Erases env Us [] (b.instantiateLevelParams ps us) b₀
```

**The consumer's form.** `SEval.deltaC` (`SourceEval.lean:215`) binds `ups` as a *variable* of
the rule — `hinst : b' = b.instantiateLevelParams ups us` — so it is not the declaration's
column, and at `ups = []` the body is unchanged and the demand is §1.1's refuted one
(`deltaC_ups_nil_is_the_refuted_instance`, `scratch/round7/r1.lean`). What rules that
instantiation out is the rule's own `hdef : StepDefeq env Us Δ (mkApps (.const c us) argsv)
(mkApps b' argsv)`, which forces a translation of the instantiated spine
(`SourceEval.lean:106`); at the empty spine it is already unsatisfiable for such a body
(`stepDefeq_blocks_bad_instance`, `r1.lean`). So the unit's consumer form takes that translation
as its premise, which is MetaRocq's own premise shape (typing of the term being instantiated):

```lean
/-- The δ arm's transport: an arbitrary instantiation, with the translation of the
instantiated body as the premise. -/
theorem Erases.instantiateLevelParams_of_trExprS {env : VEnv} {ps Us ups : List Name}
    {us : List Level} {b : Expr} {b₀ : LBTerm} {v : VExpr}
    (h : Erases env ps [] b b₀) (hnm : NoMaxLevels b)
    (htr : TrExprS env Us [] (b.instantiateLevelParams ups us) v) :
    Erases env Us [] (b.instantiateLevelParams ups us) b₀

/-- The form the δ arm holds, at its own spine. -/
theorem Erases.instantiateLevelParams_of_stepDefeq {env : VEnv} {ps Us ups : List Name}
    {Δ : VLCtx} {c : Name} {us : List Level} {argsv : List Expr} {b b' : Expr} {b₀ : LBTerm}
    (h : Erases env ps [] b b₀) (hnm : NoMaxLevels b)
    (hinst : b' = b.instantiateLevelParams ups us)
    (hdef : StepDefeq env Us Δ (mkApps (.const c us) argsv) (mkApps b' argsv)) :
    Erases env Us [] b' b₀
```

The second reduces to the first by two steps, of which the first is stated in `w7_sigs.lean`
and the second is `Erases.noFVar`'s territory:

```lean
theorem trExprS_mkApps_head {env : VEnv} {Us : List Name} {Δ : VLCtx} {f : Expr}
    {args : List Expr} {v : VExpr} (h : TrExprS env Us Δ (mkApps f args) v) :
    ∃ vf, TrExprS env Us Δ f vf
```

— the spine-head inversion — and then strengthening that translation from `Δ` to `[]`, which is
available because `h : Erases env ps [] b b₀` already says `b` is closed and free of free
variables, and instantiation preserves both (`ErasesStrengthen.lean` holds the weakening
direction, `erases_weakFV_nofvars`, `:376`).

The first reduces to `Erases.instantiateLevelParams` by normalising the by-name substitution
`instantiateLevelParams ups us` to the positional one over `ps`: for `p ∈ ps ∩ ups` the two
agree, for `p ∈ ps \ ups` the positional entry is `.param p`, and `htr` is what says such a `p`
is in `Us`. That normalisation is the unit's only real work.

*Files.* `ErasesAbstract.lean` (the three theorems, beside `Erases.instL`),
`ErasesCorrect/Delta.lean` (the δ arm's one line, `:166`), `ErasesCorrect/Steps.lean` and
`ErasesCorrect/Close.lean` (`step_delta` and `erases_correct` gain
`hnm : ∀ c b, bo c = some b → NoMaxLevels b`, supplied at the capstone from `TableSafe`'s new
clause and at the rungs from `hsafe`).

*Gate.* `Delta.lean:164-166` closes with `Erases.instantiateLevelParams_of_stepDefeq` in place
of `herb Us ups us`; `scripts/erases_correct.sh` green with `erases_correct`'s footprint
unchanged.

*Confidence.* The positional form is **proved** (`w7_sigs.lean`). The consumer form is true —
no arm of `Erases` puts a level in its image (`const` drops levels, `ctor`'s `iid`/`k` are
functions of the name, `box` yields `.box`, `proj`'s coordinates come from `IndInfo`), and the
box arm's typing side is `Erasable.instL`, already proved — but the normalisation step above is
an induction, not a one-line reduction, and that is where the unit's risk sits. The two
premises the tree must supply, `NoMaxLevels` per tabled body and `hdef`'s translation, are
measured satisfiable: `maxLevels = 0` at all eight rungs, and `hdef` is a field of the rule.

### 2.3 U3 — the binder name leaves `Erases`

`Erases.lam` and `Erases.letE` copy the source binder name into the image
(`Erases.lean:246`, `:251`), which is the only reason an α-variant of a tabled body erases to a
differently-named λ□ term. λ□'s `WcbvEval` reads binder *counts* only, `Lower.lambda` and
`Lower.letIn` already quantify the target name (`Lower.lean:344`, `:346`), and the condition on
an emitted name lives on the output boundary as `LBWfPeregrine.printableNames`. The two arms
quantify it too:

```lean
  | lam {Δ n n' ty bi b b'} {ty' : VExpr} (hty : TrExprS env Us Δ ty ty')
      (hb : Erases env Us ((none, .vlam ty') :: Δ) b b') :
      Erases env Us Δ (.lam n ty b bi) (.lambda n' b')
  | letE {Δ n n' ty nd v v' b b'} {ty' val' : VExpr}
      (hty : TrExprS env Us Δ ty ty') (hval : TrExprS env Us Δ v val')
      (hv : Erases env Us Δ v v')
      (hb : Erases env Us ((none, .vlet ty' val') :: Δ) b b') :
      Erases env Us Δ (.letE n ty v b nd) (.letIn n' v' b')
```

*Files.* `Erases.lean` (the two arms, `lam_inv`, `letE_inv`), and the inversions that read the
name equation: `ErasesAbstract.lean`, `ErasesUniform.lean`, `ErasesStrengthen.lean`,
`ErasesEnv.lean`, `VisitExprRefines/Step/Mechanical.lean` — an existential binder replaces an
equation at each.

*Gate.* `scripts/erasesLB.sh` green; `firstorder_erases_core`'s uniqueness clause unchanged —
it inducts on `SValue` and its `lam` case is `exfalso` at `FirstOrderInd`
(`FirstOrderInd.lean:518-538`), so no λ survives into it; the rungs' statements unchanged.

*Confidence.* The relation gets more non-deterministic, and the one place that could care is the
uniqueness clause, checked above. What is not checked is whether some inversion elsewhere leans
on the name equation to fix a metavariable; that is a compile-and-see. Probe: the two arms
elaborate as a standalone inductive (`w7_sigs.lean`, `ErasesW7`).

### 2.4 U4 — `Erases` up to source α

`ReifiedDecl.Prepared` (`Witness/SourceTable.lean:195`) pins a tabled body to the value the code
generator reads only up to `Expr.AlphaEq` — deliberately, since on equality the clause is
uninhabited wherever `inlineMatchers` fires — and `lake exe reify --check` reports five of
G7/G8's bodies matching only up to binder names. U7's content clause reads the tabled body, so
it owes the transport. Three declarations, not the two `A-hbridge.md` scheduled, and one of them
is restated rather than re-landed. The deleted file is at `git show 47334eb^:LeanToLambdaBox/Alpha.lean`
(99 declarations; these are its lines 662, 678, 700):

```lean
theorem Witness.Expr.AlphaEq.refl : ∀ e : Expr, Expr.AlphaEq e e

theorem TrExprS.alpha {env : VEnv} {Us : List Name} {Δ : VLCtx} {e e' : Expr} {ve : VExpr}
    (h : TrExprS env Us Δ e ve) (hα : Expr.AlphaEq e e') : TrExprS env Us Δ e' ve

theorem Erases.alpha {env : VEnv} {Us : List Name} {Δ : VLCtx} {e e' : Expr} {t : LBTerm}
    (h : Erases env Us Δ e t) (hα : Expr.AlphaEq e e') : Erases env Us Δ e' t
```

`Expr.AlphaEq.refl` and `TrExprS.alpha` come back verbatim — both re-proved in `w7_sigs.lean`,
no `sorry`, to confirm they still elaborate against the current `TrExprS`. `TrExprS.alpha` is
**not** on `A-hbridge.md`'s list and is unavoidable: `Erases.alpha`'s box arm transports `htr`
and its `lam` arm transports `hty`. `Erases.alpha` itself is restated: the W5 form landed in a
*target* renaming (`∃ t', LBTerm.AlphaEq t t' ∧ …`) and so dragged in the 99-declaration
`LBTerm.AlphaEq` kit; after U3 the image is name-free and the same `t` serves. The rest of
`Alpha.lean` — the λ□ congruence and decision procedure, `SEval.alpha`, `StepDefeq.alpha` — is
**not** re-landed: it has no consumer in this plan.

*Gate.* `SourceTableAdequate.body?_prepared` (`Witness/SourceTable.lean:231`) acquires its first
consumer, which is U7; `lake exe hygiene --dead` does not grow by three orphans.

*Confidence.* `Erases.alpha` in this form is **false before U3** — `Erases.lam` copies
`n.toString` into the image, so an α-variant erases to a differently-named λ□ term — and true
after it. The ordering is load-bearing, which is why U4 depends on U3. The signature elaborates
against the shipping `Erases` (`w7_sigs.lean`, as a stub, flagged there as false pre-U3).

### 2.5 U5 — the level scope inside the eighteen motives

The motives (`VisitExprRefines/Motives.lean:93-272`) are stated at one fixed `Us`, pinned by
`BridgeInv.lparams : ctx.lparams = Us` (`Bridge.lean:323`), which `Erasure.visitMutual` breaks
at `Erasure.lean:889` and `:912` by re-entering a member under `ci.levelParams`. Each motive
quantifies the scope instead, and the two premise bundles follow — which is not a weakening
trick but exactly what `abstract_make_wf_env_ext` gives MetaRocq for free at every constant:

```lean
    (P : ∀ Us, ErasureSpec lenv env Us gw)
    (E : ∀ Us, EraserAsks lenv env Us gw)
```

with, representatively (`RunRefines`, `Motives.lean:38`):

```lean
def RunRefines (env : VEnv) (tbl : SourceTable) (ctx : ErasureContext) (Δ : VLCtx)
    (s s' : ErasureState) (gen gen' : NameGenerator) (e : Expr) (t : LBTerm) : Prop :=
  RunConcl s s' ∧ IndRegistryModelled env s' ∧ gen ≤ gen' ∧
    ∀ Us, ctx.lparams = Us → ∀ Γspec, SpecEnv env tbl.body? s' Γspec →
      ErasesLBMode tbl ctx env Us Γspec Δ e t
```

`RunRefinesAlt` and `HeadRefines` change the same way, and U6 rewrites the `∀ Γspec` half of
all three.

*Files.* `VisitExprRefines/**` (4,155 lines, 191 declarations by
`grep -cE '^(theorem|def|structure|inductive|instance|abbrev|lemma) '`), `Capstone.lean`,
`Green.lean`.

*Gate.* the bridge induction still closes; `lake exe hygiene --dead` budget unchanged; the
rungs' binder lists show `P`/`E` at `∀ Us`.

*Confidence.* No counterexample found; the work is wide and mechanical. Not probed here beyond
the two binder types, which elaborate.

### 2.6 U6 — `Γspec` as an output, and a growth relation the pass survives

`RunRefines` reads the content at *every* `SpecEnv` of the final state, the opposite shape to
the one environment U7 produces. `Γspec` becomes an input-output accumulator, as `deps` is in
MetaRocq's `erase_global_deps`, and `SpecEnv.mono` (`SpecEnv.lean:43`) is replaced by
monotonicity along the growth relation — the analogue of `erases_deps_cons` (`EDeps.v:492`).

**The growth relation is not a bare fresh-prefix extension.** `Lower.const`'s premise is
`¬ RuntimeKey Γ kn` (`Lower.lean:343`), which is *anti*-monotone in the environment, and a fresh
prefix can create a runtime key — mechanised at the shapes `ElimDecl` actually has:

```lean
theorem freshPrefix_not_runtimeKey_stable :
    ∃ (Γ Γ' : GlobalDeclarations) (kn : Kername),
      (∃ pre : GlobalDeclarations, Γ' = pre ++ Γ ∧ ∀ p ∈ pre, ∀ q ∈ Γ, p.1 ≠ q.1) ∧
        ¬ RuntimeKey Γ kn ∧ RuntimeKey Γ' kn
```

(`w7_meas.lean`, proved, `[propext, Quot.sound]`; the witness declares `mkElimBody` at a fresh
key together with its block, and `Lower [] (.const kn) (.const kn)` holds at the smaller
environment, `lower_nil_const`, `[propext]`.)

**Tested against the real run order.** The strengthening `A-hbridge.md` proposes — the prefix
declares no key `Γ` does not — is *unsatisfiable along the run*, and the reason is the shape of
`Γspec`. The eraser registers exactly three kinds of `gdecls` entry: a body-less constant
(`Erasure.lean:187`), a constant with a body (`:892`), a `.fix` body for a block member
(`:918`), and an inductive block (`:242`). It **never** registers an eliminator declaration:
`Erasure.visitCases` turns a `casesOn` application into a `.case` node directly. So every
`ElimDecl` of `Γspec` is specification-side, added by the proof at the step where the run builds
a `.case` node, at a key the emitted environment never declares — that is, at an **undeclared**
key. A growth relation forbidding new runtime keys outright would therefore have no model at the
`visitCases` step. The order inside that step is: the discriminant's sub-run first
(`Erasure.lean:769`), `register_inductive` second (`:818`), the alternatives third — so the
block arrives after a sub-run has already produced a lowered term.

The definitional change is therefore narrower, and it is a definitional change, not a guard: an
extension may make an **undeclared** key a runtime key, and may not do that to a key already
declared.

```lean
/-- `Γ'` extends `Γ` by a prefix of fresh keys and turns no key `Γ` already declares into a
runtime key. The first half is `erases_deps_cons`' weakening (`EDeps.v:492`); the second is
what `Lower.const`'s anti-monotone premise needs, and it is a *fact about the run*, not a
restriction on it: a declared entry is an erasure image or a lowered block member, and no
erasure image is an `ElimBody` (`erases_ne_elimBody`). -/
def SpecGrow (Γ Γ' : GlobalDeclarations) : Prop :=
  ∃ pre : GlobalDeclarations, Γ' = pre ++ Γ ∧ (∀ p ∈ pre, ∀ q ∈ Γ, p.1 ≠ q.1) ∧
    ∀ kn, (LBTerm.envLookup Γ kn).isSome → RuntimeKey Γ' kn → RuntimeKey Γ kn

theorem SpecGrow.lookup (h : SpecGrow Γ Γ') (hd : LBTerm.envLookup Γ kn = some d) :
    LBTerm.envLookup Γ' kn = some d

/-- Every `.const` node of `t` is declared in `Γ`. -/
def ConstsDeclared (Γ : GlobalDeclarations) (t : LBTerm) : Prop :=
  ∀ kn ∈ constRefs t, (LBTerm.envLookup Γ kn).isSome

theorem Lower.specGrow (h : SpecGrow Γ Γ') (hd : ConstsDeclared Γ t) (hl : Lower Γ t u) :
    Lower Γ' t u
```

`ConstsDeclared` is the side condition that makes the `const` arm go through, and it is not new
content: it is `ErasesEnv.deps` at the term's own references, so the threaded motive carries it
as a conjunct beside `ErasesLBMode`. The positive arms need nothing: `elimApp`'s `ElimDecl` and
the two fix arms' `DefnDecl` read declared entries, which `SpecGrow.lookup` preserves.

The threaded motive:

```lean
def RunRefines (env : VEnv) (tbl : SourceTable) (ctx : ErasureContext) (Δ : VLCtx)
    (s s' : ErasureState) (gen gen' : NameGenerator) (e : Expr) (t : LBTerm) : Prop :=
  RunConcl s s' ∧ IndRegistryModelled env s' ∧ gen ≤ gen' ∧
    ∀ Γ₀, RegInvShape' env tbl.body? Γ₀ s → RegContent env tbl.body? tbl.levels? Γ₀ s →
      ∃ Γ₁, SpecGrow Γ₀ Γ₁ ∧ RegInvShape' env tbl.body? Γ₁ s' ∧
        RegContent env tbl.body? tbl.levels? Γ₁ s' ∧ ConstsDeclared Γ₁ t ∧
        ∀ Us, ctx.lparams = Us → ErasesLBMode tbl ctx env Us Γ₁ Δ e t
```

*Files.* `Motives.lean`, the eighteen step lemmas under `VisitExprRefines/Step/`, the aggregator
`VisitExprRefines.lean`, and `Lower.lean`/`LowerFix.lean` for the monotonicity lemmas.

*Gate.* the eighteen step lemmas re-close; the seven state-growing members (`visitConst`,
`get_constant_kername`, `visitMutual`, `visitConstructor`, `visitProj`, `visitCases`,
`visitAlt`) exhibit their prefix and discharge `SpecGrow`'s third clause.

*Confidence.* The relation as defined is what the run satisfies, and the refutation above is
what forces the third clause. The residual risk is the third clause's discharge at the
registration primitives: it needs "a declared body is not an `ElimBody`", which is
`erases_ne_elimBody` (`ErasesCorrect/Steps.lean:785`) at a `RegContent`-declared body and a
`FixDef`-name argument at a lowered block member. Probe: the refutation and both definitions
elaborate (`w7_meas.lean`, `w7_sigs.lean`).

#### 2.6.1 As landed: the environment condition the law needs

The definitional half of U6 is in the tree (`Lower.lean`, `ErasesLB.lean`, `Bridge.lean`,
`Green.lean`); the motive rewrite is not, because the accumulator's registering steps have no
content to build `Γ₁` from until `RegContent` exists (§2.7). Three statements above change.

**`Lower.specGrow` is false as printed.** `ConstsDeclared Γ t` at the source reaches the
block's *other* declared bodies not at all, and `fixConst`'s sub-derivations run on them:
`SpecGrowFixture.specGrow_needs_declaredEnv` (`Lower.lean`) exhibits `Γ` declaring one λ-bodied
member whose body names an undeclared key, a growth declaring that key as an eliminator with
its block, a `Lower Γ (.const kn) (.fix defs 0)` and the absence of any `Lower Γ'` derivation
of the same pair. The law as landed adds the environment's own δ-column well-formedness — the
`tConst` case of MetaRocq's `wellformed` under `wf_glob`
(`../metarocq/erasure/theories/EWellformed.v:166`, `:211`):

```lean
def ConstsDeclaredEnv (Γ : GlobalDeclarations) : Prop :=
  ∀ kn b, DefnDecl Γ kn b → ConstsDeclared Γ b

theorem Lower.specGrow (hg : SpecGrow Γ Γ') (henv : ConstsDeclaredEnv Γ)
    (h : Lower Γ s t) : ConstsDeclared Γ s → Lower Γ' s t
```

It is a condition the proof-built `Γspec` satisfies rather than a restriction: a body enters
`Γspec` only at the step that registers its constant, by which time its own sub-runs have
registered — and the proof has declared — every key it names. It is not a condition no
environment meets: `Green.g7_constsDeclaredEnv` and `g8_constsDeclaredEnv` decide it, through
`constsDeclaredEnvB`, at the two Arith rungs' *emitted* environments. **U7's accumulator must
carry it as a clause**, beside `RegInvShape'` and `RegContent`.

**The side condition lands at the source, not at the emitted term.** The motive sketch's
`ConstsDeclared Γ₁ t` reads the run's output; `Lower`'s source is the *specification* term,
which every composite binds existentially. What the composites take is therefore
`ErasuresDeclared env Us Γ Δ e` — every erasure of the source term names only declared
constants — and `ErasesLB`, `ErasesLBAlt`, `ErasesLBFix`, `ErasesLBFixAlt`, `ErasesLBMode` and
`ErasesLBAltMode` each have their `.specGrow` under it.

**The third clause's discharge is `ElimBlocksDeclared`.** `SpecGrow.of_fresh` asks that every
eliminator body `Γ` declares already has its block declared in `Γ`; that is the weakest form of
"a declared body is not an `ElimBody`" (`erases_ne_elimBody`), and it is what the run satisfies,
since `ElimDecl` bundles entry and block. Measured against the run order at the rungs whose
tables hold a `casesOn` constant — G5–G8, `Nat.casesOn` at each — `Green.elimKeys_undeclared`
decides that no such key is declared in the emitted environment, `Green.g7_natCasesOn_tabled`
that the measurement is not vacuous, and `Green.g7_elimCons_specGrow` closes the step: over any
`Γ` whose keys the emitted environment answers, consing the specification-side eliminator entry
is a `SpecGrow`.

### 2.7 U7 — the preservation theorem

One content clause carrying both readings of a single erasure witness — `SpecContent.defns`
names *some* erasure of the compiler body while `RegInvShape'.defs` demands the emitted body be
the `Lower` image of *that* one, and `Erases` is not deterministic outside the first-order
fragment — now at the declaration's level scope:

```lean
structure RegContent (env : VEnv) (bo : Name → Option Expr) (lp : Name → List Name)
    (Γspec : GlobalDeclarations) (s : ErasureState) : Prop where
  defns : ∀ (n : Name) (b : Expr) (t : LBTerm), bo n = some b →
    DefnDecl s.gdecls (toKername n) t →
    ∃ b₀ : LBTerm, DefnDecl Γspec (toKername n) b₀ ∧ Erases env (lp n) [] b b₀ ∧
      (Lower Γspec b₀ t ∨ ∃ kns bs defs j, LowerFix Γspec kns bs defs ∧
        kns[j]? = some (toKername n) ∧ t = .fix defs j)

theorem visitExpr_regInv_all (P : ErasureSpec lenv env Us gw) (E : EraserAsks lenv env Us gw)
    (htbl : SourceTableAdequate lenv tbl) :
    ∀ e s ctx cctx ref w t s' w', Erasure.visitExpr e s ctx cctx ref w = .ok (t, s') w' →
      ConfigPinned ctx.config →
      ∀ Γspec, RegInvShape' env tbl.body? Γspec s →
        RegContent env tbl.body? tbl.levels? Γspec s →
        ∃ Γspec', SpecGrow Γspec Γspec' ∧ RegInvShape' env tbl.body? Γspec' s' ∧
          RegContent env tbl.body? tbl.levels? Γspec' s'
```

(`A-hbridge.md`'s `∃ Us` inside `RegContent.defns` goes with U1; the two `P`/`E` binders become
`∀ Us, …` with U5.) `SpecContent.defns` and `RegInvShape'.defs` become projections of it at a
declared constant, and the preservation kit it spends exists: `RegInvShape'.{addAxiom_run,
constCons, recConst, axiomCons, blockCons, stateCongr, indsGrow, register_inductive_run}`
(`ColdStartShape.lean:212-680`). The α transport of U4 is what lets the clause read the *tabled*
body while the run erases `prepare_erasure (compilerValue lenv n)`.

*Files.* `ColdStartInduction.lean` (51 declarations), `ColdStartShape.lean`.

*Gate.* it elaborates with the kit unchanged; `lake exe hygiene --dead` records
`SourceTableAdequate.body?_prepared` as reached.

*Confidence.* Stateable, and every ingredient is either proved or scheduled; this is the wave's
largest single obligation and its risk is proof size, not truth.

### 2.8 U8 — saturation at the final state

```lean
def RegKeyed (env : VEnv) (s : ErasureState) : Prop :=
  ∀ kn, LBTerm.envLookup s.gdecls kn ≠ none →
    (∃ n, kn = toKername n ∧ (s.constants.get? n).isSome) ∨
    (∃ n iid np nfs, (s.inductives.get? n).isSome ∧ IndInfo env n iid np nfs ∧
      kn = iid.mutualBlockName)

theorem ConstExt.regKeyed (h : ConstExt s s')
    (hind : ∀ n, (s.inductives.get? n).isSome → (s'.inductives.get? n).isSome)
    (H : RegKeyed env s) : RegKeyed env s'

theorem regSaturated_of_regKeyed (H : RegInvShape' env bo Γspec s) (hk : RegKeyed env s)
    (hsub : ∀ kn, (LBTerm.envLookup Γspec kn).isSome → (LBTerm.envLookup s.gdecls kn).isSome) :
    RegSaturated env Γspec s
```

`RegKeyed` takes `env` as a parameter, which `A-hbridge.md`'s sketch omits and `IndInfo` needs.
No new clause on `ConstExt` is required: `ConstExt.gdecls` (`ErasureRun.lean:1538`) already
records every prefix entry as `(toKername m, .constantDecl ⟨none⟩)` for an `m` the extended
registry knows, so the converse the saturation wants is a theorem about it.

*Files.* `ColdStartShape.lean`, `SpecEnv.lean`.

*Gate.* `RegInvShape'.lowerEnv` (`SpecEnv.lean:137`) applies at the run's final state.

*Confidence.* Mechanical; the only judgement is `hsub`, which holds because U7 builds `Γspec`
from `s.gdecls` plus specification-only eliminator entries — and those are exactly the keys
`LowerEnv`'s pruning clause allows to be absent.

### 2.9 U9 — `hbridge` discharged

```lean
theorem erasure_bridge_env (P : ErasureSpec lenv env [] gw) (E : EraserAsks lenv env [] gw)
    (htbl : SourceTableAdequate lenv tbl) (hcfg : ConfigPinned cfg) :
    ∀ (sf : ErasureState) (wt : Void IO.RealWorld),
      Erasure.visitExpr pe {} { «config» := cfg } cctx ref wp = .ok (t, sf) wt →
      ∃ Γspec : GlobalDeclarations, SpecEnv env tbl.body? sf Γspec ∧
        ∀ t₀ : LBTerm, Erases env [] [] pe t₀ → Lower Γspec t₀ t →
          ErasureBridge env tbl.body? tbl.levels? Γspec sf.gdecls t₀
```

— the shape of `hbridge` exactly (`Capstone.lean:166-170`), by `bridgeEnv_of_regInv` at U7's
output and U8's saturation, starting from `RegInvShape'.empty` (`ColdStartShape.lean:182`) and
the empty `RegContent` at the empty state. `hbridge` then leaves `shipping_erase_correct_firstorder`
and all eight rungs, and `hargReach` at G8 falls out of `Green.g8_argErasesEnv`
(`Green.lean:1406`).

*Files.* `Capstone.lean`, `Green.lean`.

*Gate.* `scripts/ledger.sh` — the 33-name cluster must not grow; `lake exe green-check --all`;
`grep -rn "hbridge" LeanToLambdaBox/` empty.

## 3. What closing `hbridge` gives, and what it does not

It removes the last class-**C** binder specific to this repository's own registration path, and
— with U1 — it is what makes five of the eight rungs say anything at all. It does **not** make
the capstone unconditional. What still stands, in the classes of
`scratch/round7/D-census.md`:

* **D — specifications of Lean `Meta`/`Core` primitives.** `P : ErasureSpec`, eight fields, none
  of which any Lean term can state agreement with, because `Lean.Environment` and
  `IO.RealWorld` are opaque; `htbl`, `hsafe`, `hblk`, `hprep`, `hrun`, mechanised outside Lean by
  `lake exe reify` and the byte-diffed `.ast`.
* **C — this repository's own code.** `E : EraserAsks`, five fields, two of which are false in
  general and bound by reported shipping findings — `kernel_ind_head_true` (F-DEPTH) and
  `block_keys_distinct` (F-UNSAFEREC). `hbridge` is the one this document removes.
* **U — upstream lean4lean.** `A : UpstreamAsks`, four fields (asks 2, 6, 9, 10); `hcb :
  CompilerBodies` at G2–G8, blocked on `TrProj`, which the pin leaves entirely unproven — 10 of
  G7's 30 tabled bodies carry an `Expr.proj`; ask 4, which `hfo` and `ErasesEnv.tabled`'s
  discharge wait on.
* **R — scope.** `hsup : Supported`, the decidable fragment; `hnb : NoBodylessRefs`, false on
  Fannkuch (F-EQREC); the first-order, forward-simulation shape of the observable clause; and,
  newly, `TableSafe.noMaxLevels`, the `max`-free level fragment `Erases.instL` transports along.
* **inherited.** The sixteen lean4lean `sorryAx` roots of `test/lean4lean-sorries.expected`, and
  the 29-name executable-checker cluster that `ErasureSpec.oracle_sound_of_run` brings with it.

`hev`, `hvwt`, `hty` and `hfo` remain Π-bound at every rung, and `lenv`/`env` are universally
quantified there, so a green rung is a statement about every environment modelling its table —
not a closed-world claim about one run. Closing `hbridge` moves one row of that census; the
other rows are where the remaining work is.
