# 07 — Status

## 1. The theorem
`LeanToLambdaBox.shipping_erase_correct_firstorder` (`LeanToLambdaBox/Capstone.lean:190-233`).
Subject: `Erasure.erase`, the function `#erase` calls, from the empty state at a pinned
configuration. If the run returns `.untyped Γ (some t)` on a source term `e` whose prepared form
is `pe`, then there are `Γspec` and `t₀` with `Erases env [] [] pe t₀` and `Lower Γspec t₀ t` —
the emitted term is the lowered image of an erasure of the prepared term — together with
`ErasesEnv env tbl.body? tbl.levels? Γspec t₀`, `LowerEnv Γspec Γ` and `LBWfPeregrine Γ t`: the
emitted environment is the lowered, pruned image of `Γspec`, and the emitted program satisfies
what peregrine's first pass reads. The last conjunct before the observable is the theorem's own
binder `hwf`, carried rather than derived, and every rung discharges it by kernel computation.
The observable conjunct is a forward simulation at first-order answers: for closed `args` whose
λ□ images `targs` each carry an erasure, that erasure's lowering and its own `ErasesEnv` clause,
and whose applied spine has a translation `TrExprS env [] [] (mkApps pe args) vs`, if
`SEval env tbl.body? [] fullFlags [] (mkApps e args) v` and `v` is typed at a spine of an
inductive `I` with `FirstOrderInd env I`, then `WcbvEval Γ eraseFlags (LBTerm.mkApps t targs) tv`
for the `Lower` image `tv` of the unique erasure `tv₀` of `v`, with `NoBox tv`. The fourteen
binders are `P`, `E`, `A`, `htbl`, `hsafe`, `hblk`, `hcfg`, `hcb`, `hwt`, `hsup`, `hprep`, `hrun`,
`hwf`, `hbridge` (`Capstone.lean:196-213`).

**Wave 6** (`740dd7c..18976fa`, seven commits) pruned the zero-consumer surface the wave-5 audit
found to the declarations wave 5's own plan (`12-REPAIRS-W9.md` §2.3–§2.6) or the W9-B
decomposition actually names (`scratch/round7/w6-report.md`: 27 kept, 13 deleted, no ledger or
`--dead` movement), then landed **B-i through B-v**, the five-unit decomposition
`scratch/round7/W9-B-report.md` §4 proposed for `regInv_registerInd_run` — the theorem that
gives `RegAcc` a producer *at a run* of `Erasure.register_inductive` — and **W9-C**, the sibling
producer at a recursive-constant registration, `regInv_recConst_step`. Both theorems are proved,
each with a real proof-term consumer inside the unit that lands it (`scratch/round7/B-v-report.md`
§1, `scratch/round7/W9-C-report.md` §1); `regInv_registerInd_step` (W3) and
`RegContent.register_inductive_run` get their first consumers here, closing the "W9-B attempted
and returned blocked" state wave 5 left. **Wave 7** (`16d2271..e2ff202`, eight commits) re-pinned
lean4lean to `8cc17a5` (the round-4 landing: `PIN`), retired the last declaration this repository
kept inside `namespace Lean4Lean.TypeChecker` (`C21`), retired `UpstreamAsks.constArityInv` and
the local duplicate `wf'_induct_origin` in favour of direct citations of the landed fork theorems
(`U6`, `U7`), derived five of `UpstreamAsks.constsOrigin`'s eight conjuncts from the landed
`VEnv.WF'.consts_origin` while **refuting** a sixth (`U2`), left `hfo` blocked with three
findings (`HFO`, nothing committed), and landed seventeen of the eighteen step obligations of a
second accumulator bundle feeding `StepAcc6` (`W9-D1`/`W9-D2`, `bfc7023`+`fb4e166`).

**The dominant fact this wave, discovered by its own audit and not by design: no environment
satisfies any rung's hypotheses.** `U2`'s refutation of `UpstreamAsks.constOriginExcludes` —
recorded in `doc/trust.md`'s row as "inhabited at no environment declaring an inductive block" —
understates its own consequence. Every rung binds `A : UpstreamAsks env` together with either
`hfo : FirstOrderInd env ``Nat`, or `F : SpikeNatFacts env ni` (five of eight rungs), or
`P`/`htbl` (all eight, and `g<i>Table.ind? ``Nat` = some _` holds by `rfl` at every table); each
combination is independently `False` (`Rungs.green_G5_absurd`, `Rungs.green_G6_absurd`,
`Rungs.green_G6_absurd_table`, `scratch/round7/W7-refute.md` §1.2, mechanised,
`[propext, Classical.choice, Quot.sound]`). The capstone's own binder list does not force this —
`tbl` is a variable — but its observable conjunct is guarded by `FirstOrderInd env I` under the
conclusion's `∀ I`, so under `A` the forward simulation, the theorem's point, is never applied:
the capstone is non-vacuous only at an `env`/`tbl` pair declaring no inductive type at all. Worse,
the conclusion the refuted premise was guarding is itself false at the tree's own fixture:
`Fixture.no_unique_erasure_natZ` shows `Nat.zero` has two distinct erasures at `natEnv`
(`.construct natIid 0 []` and `.const (toKername natZ)`), refuting the rungs' own uniqueness
conjunct at a first-order value — `UpstreamAsks` is not merely an unused premise, it is the
premise whose falsity keeps a false conclusion from being reachable. Nothing in the ladder's
*statement* changed this wave (`LeanToLambdaBox/Green.lean` is not in wave 7's diffstat and
`Capstone.lean` changed by three `import` lines only), so this is a refutation of the wave-6
statements too — what wave 7 introduced is the proof that the premise is refutable, which
converts eight conditionally-green rungs into eight vacuous ones. §4 has the routes and the
repair.

| Class | Binders |
|---|---|
| proved, or per rung a checked term | inside the theorem: the erasure half `erasure_bridge_of_run`, supplying all eighteen bridge steps; the answer's shape and uniqueness from `firstorder_erases_core`, and `NoBox tv` at the *lowered* value from `noBox_lower_of_foSpine`; the simulation, `erases_correct` applied once at the spine with `ErasesEnv.mkApps`; the observable's transport across the preparation passes from `prepare_sound`. At every rung: `hcfg : ConfigPinned`, `hsup : Supported`, `hwf : LBWfPeregrine` by `lbWfPeregrine_of_check (by decide +kernel)`, `hwt : TrExprS`, the target-side `WcbvEval`; `hcb : CompilerBodies` at G1 only; `hev : SEval` at G5 only. `noTabledCasesOnBodies` (four rungs since wave 5, `g5Table..g8Table`), `tableRecPrefixed_rungs` (vacuous at all eight), `no_realizer_exit`/`no_realizer_exit_compiler` (exclude F-QUOT's/F-EQREC's two realizer exits by name): none reaches a rung. Unchanged since wave 5 |
| **C** — this repository's own code | `E : EraserAsks` — four fields, unchanged: `passes_monotone`, `passes_sound`, `oracle_false_refl`, `kernel_ind_head_true`. `hbridge`'s two fields — `erasesEnv` and `lowerEnv` — still open (§4). `hbody` (named `hargReach` before W7/U9), at G8 alone — still open (§4). Since wave 7: `AccAsks` — a fourth field beyond `P`, `htbl`, `A` for the second accumulator bundle's seventeen landed step obligations (`MotivesAcc.lean:354`), itself carrying `upstream : UpstreamAsks env`, so a step whose own premises read a block positively is a four-line corollary of the same vacuity above (`scratch/round7/W9-D2-report.md` §2.3–§2.4, five of the seventeen, including all three block-registering members) |
| **D** — specifications of Lean's `Meta`/`Core` primitives | `P : ∀ Us, ErasureSpec lenv env Us gw` — seven fields, unchanged since U5. `SchemeNames lenv` (wave 5, W9-A) — two fields, still no producer, still read only by the two zero-consumer `no_realizer_exit*` theorems. `htbl : SourceTableAdequate`, `hsafe : TableSafe`, `hblk : TableBlocks`, `hprep`, `hrun` |
| upstream | `A : UpstreamAsks env` — **still four Lean structure fields, packaging three named asks** (items 2, 9, 10, `doc/upstream-asks.md`): `constsOrigin` (five of the original eight conjuncts; two derived and dropped, one split out below, `Upstream.lean:65-81`), `constOriginExcludes` (new this wave, split from `constsOrigin`'s former sixth conjunct — below), `mkAppsInv`, `indSpineInj`. Item 6 (`constArityInv`), the fourth field last wave, is no longer one: landed at the pin, `sorry` (`Injectivity.lean:45`), its three consumers (`not_erasable_of_informative`, `indSpine_ne_forallE`, `FirstOrderInd.notSortNotPi`) now cite `Lean4Lean.VEnv.IsDefEqU.const_arity_inv` directly — the obligation moved from a class-C hypothesis to an inherited `sorryAx` root, with no ledger-row footprint change (the two direct rows already carried `sorryAx` through the same Church-Rosser cluster). `constOriginExcludes : ∀ c, ConstOrigin env c → …` (`Upstream.lean:82-92`) is **refuted** — `test/Vacuity.lean`'s `not_upstreamAsks_natEnv`, off `CtorOf.constOrigin`/`IndInfo.constOrigin` — and is the field that makes `A` uninhabited at any environment declaring an inductive block (above). `hvwt`, `hty` and `hfo` are class **C** too and stand at every rung; `doc/trust.md` has a row each |
| inherited `sorryAx` roots | **seventeen** in the pinned lean4lean `8cc17a54c41c5e364596f8e4039e1f2094523a88` (`test/lean4lean-sorries.expected`), under `.lake/packages/lean4lean/Lean4Lean/`: `Theory/Typing/ChurchRosser.lean:1193,1212`; `Theory/Typing/EnvLemmas.lean:334` (fork-authored); `Theory/Typing/Injectivity.lean:12,21,34,45` (`:45`, `IsDefEqU.const_arity_inv`, new at this pin — backs `UpstreamAsks`'s retired `constArityInv` field, not reached through `TrExprS.uniq`/`IsDefEq.uniqU`, so it sits beside, not inside, the set `doc/trust.md` (a1) tracks); `Theory/Typing/UniqueTyping.lean:174`; `Verify/Environment.lean:208`; `Verify/TypeChecker/InferType.lean:398,410`; `Verify/TypeChecker/IsDefEq.lean:227,488`; `Verify/TypeChecker/Reduce.lean:145`; `Verify/TypeChecker/WHNF.lean:149`; `Verify/Typing/Lemmas.lean:747,995` (`TrProj.weak'_inv`/`TrProj.uniq`, both still `sorry`, round 3's territory, untouched by round 4) |

## 2. The measured axiom footprint
Verbatim from `test/ledger.expected`, which `bash scripts/ledger.sh` re-measures: `shipping_erase_correct_firstorder` and each of `Green.green_G1` …
`Green.green_G8` carry one identical set of 33 names, unmoved since wave 5 — `git diff 18976fa..HEAD -- test/ledger.expected` is empty, and neither the pin bump, `C21`, `U2`, `U6`, `U7` nor `W9-D1`/`W9-D2` touched anything on that proof path.

    propext, sorryAx, Classical.choice, Quot.sound, Lean4Lean.ptrEqConstantInfo_eq, Lean4Lean.ptrEqExpr_eq, Lean.Expr.abstractRange_eq,
    Lean.Expr.abstract_eq, Lean.Expr.eqv_eq, Lean.Expr.hasLooseBVar_eq, Lean.Expr.instantiate1_eq, Lean.Expr.instantiateRange_eq,
    Lean.Expr.instantiateRevRange_eq, Lean.Expr.instantiateRev_eq, Lean.Expr.instantiate_eq, Lean.Expr.looseBVarRange_eq,
    Lean.Expr.lowerLooseBVars_eq, Lean.Expr.mkAppData_eq, Lean.Expr.mkData_eq, Lean.Expr.replace_eq, Lean.Level.hasMVar_eq,
    Lean.Level.hasParam_eq, Lean.Level.instLawfulBEqLevel, Lean.Level.isExplicitSubsumedAux_eq, Lean.Level.normalize_eq,
    Lean.PersistentArray.toList'_push, Lean.PersistentHashMap.findAux_isSome, Lean.Syntax.structEq_eq,
    Std.TreeMap.all_eq_all_toList, Lean.PersistentHashMap.WF.find?_eq, Lean.PersistentHashMap.WF.toList'_insert,
    Lean.Expr.mkData_flags._native.bv_decide.ax_1_12, Lean.Expr.Data.looseBVarRange_le._native.bv_decide.ax_1_7

The 29 non-standard names are the price of the oracle reroute: `ErasureSpec.oracle_sound_of_run` discharges `oracle_refl`'s kernel disjunct through
lean4lean's *executable* checker (`Oracle.kernel_isErasable_sound`) instead of assuming its soundness, so the checker's own reflection axioms and two
`bv_decide` certificates come with it (`doc/trust.md` §(a3) sites all 29). Other rows unchanged: `erases_correct` (T5) and its three step arms `[propext,
sorryAx, Classical.choice, Quot.sound]`; T8's `visitExpr_refines_erasesLB` and `visitExpr_refines_erasesLBFix` `[propext, Classical.choice,
Quot.sound]`, no `sorryAx`; `LBOptimize_correct` `[propext, Quot.sound]`; `lbEval_sound` `[propext]`; `bridgeEnv_of_regInv` and `bridgeEnv_of_regContent`
`[propext, Classical.choice, Quot.sound]`. The theorems wave 6 and wave 7 add — `regInv_registerInd_run`, `regInv_recConst_step` and their B-i..B-v
supporting lemmas, the seventeen landed `stepAcc_*` steps, `constOrigin_of_wf`/`consts_classified`/`not_upstreamAsks_natEnv` and siblings — are not ledger
rows: `#print axioms` measures the declarations `test/Ledger.lean` names, and none of these is named there, because none reaches `shipping_erase_correct_
firstorder`'s own proof term (§4).

`#print axioms` measures a proved theorem and never a hypothesis, which is why the `UpstreamAsks` field count moving from four to three moves no row,
and why the wave's central finding (§1) — that the hypothesis set is jointly unsatisfiable — is invisible here too: a vacuous hypothesis is still a
hypothesis, and `#print axioms` reports a theorem's dependencies, not whether its premises are inhabited. The one substantive trust change of the wave,
`const_arity_inv`'s `sorryAx` root entering through a retired class-C field rather than a ledger-visible route, is likewise invisible to this section and
is recorded in §1's `UpstreamAsks` row and in `test/lean4lean-sorries.expected` instead.

## 3. Coverage
`doc/coverage.md` is generated by `lake exe coverage` from the tree; `lake exe coverage --check` is green at HEAD (`scratch/round7/gate7/21-coverage-check-rerun.out`). The whole-environment constant census moved twice since wave 5's `230,498`: `740dd7c` (wave 6's dead-surface prune) to `230,481` as thirteen declarations left the closure; then, across B-i..B-v, W9-C and the wave-7 units' own new declarations, to `230,655` (the last regeneration wave 6/7 individually committed, `scratch/round7/B-v-report.md`, `scratch/round7/W9-C-report.md`); `e2ff202` (this wave's own bookkeeping fix, `scratch/round7/gate7-report.md` §2.1) regenerates it once more to **230,934**, current at HEAD. None of these regenerations moved a table row, a rung column or the realizer census — each is the constant count alone. The realizer census column (`Tools/Coverage.lean:209`, reading `Supported.isRecursorName`) is still 0 at every rung. Arith is in
the fragment and is the subject of rungs G7 and G8. Sieve and
BinaryTrees are out at `recursorHead` on `Eq.rec` through `Bool.noConfusion` (F-EQREC); Quicksort at F-EQREC, the well-founded
`Nat.div.go`/`Nat.modCore.go` route and `sparseCasesOn`, with a wrong emitted program besides (F-SPARSE); Fannkuch at F-EQREC and `etaContractedMinor`
on `Decidable.casesOn`. `NoBodylessRefs` is true on all five programs and all eight rungs (F-QUOT's/F-EQREC's registering exit); Fannkuch stays outside
the fragment for the two reasons above alone. None of this moved since wave 5 — the corpus, the tables and the fragment boundary are unchanged.

"Arith is covered" means `supportedB` returns `ok` at the entry term and at every tabled body of `reify% arithClosed`; that `green_G7` instantiates
the capstone at the closed `arithClosed` and `green_G8` at `benchArith` applied to `0`; and that both conclusions end in the literal peano numeral
`8`, which `lake exe green-check` re-derives with `lbEval` from the byte-diffed `.ast`. It does **not** mean the source evaluation is derived: `hev`
binds at G7 and G8 as at G1–G4 and G6, because `benchArith 0` runs 45 recursive calls, each owing N20's derivation for its unselected minor, against a
45-line three-`StepDefeq` precedent for one δ and one ι at G5 — the constructed witness is at G5 (`Green.g5_seval`) and nowhere else. Nor does it mean
a rung is unconditional: `lenv` and `env` are universally quantified at every rung, and §1's finding means the quantifier is instantiated at no
environment that also satisfies `A`.

`LBWfPeregrine`'s binder-name clause is `PrintableBinders`, under which the offending-binder count is 0 at all eight rungs (`Tools/Coverage.lean`
recomputes it from `Green.g<i>Env`/`g<i>Term` at every regeneration); `expandedFix` (M3, folding in MetaRocq's `expanded_tFix`) is true at all eight,
F-ETA's `LBTerm.etaFix` wrapping making the spine conjunct true at G6–G8. Unchanged since wave 4.

### Which conclusion conjuncts are vacuous or literal, at which rungs
Unchanged since round 7's audit (`scratch/round7/W2-refute.md`, `W3-refute.md`), and unaffected by this wave's own finding, which is about the
*hypotheses*, not these conjuncts of the *conclusion*:

* **Five carry no content.** `hprep`'s equation is conjunct 1 re-exported verbatim. `LBWfPeregrine g<i>Env g<i>Term`
  is the closed term `hwf`/`g<i>_wf`, checked once and carried. `NoBox (peanoLB 8)` is a literal
  fact about the answer. `WcbvEval g<i>Env eraseFlags g<i>Term (peanoLB 8)` is `Green.g<i>_eval`,
  itself a closed term. `ErasesEnv … Γspec t₀` and
  `LowerEnv Γspec g<i>Env` are `hbridge`'s two fields, assumed verbatim and re-exported.
* **Four carry the theorem's content**: `Erases env [] [] eG<i> t₀` and `Lower Γspec t₀ g<i>Term`, from `erasure_bridge_of_run`, and
  `Erases env [] [] v tv₀`/`Lower Γspec tv₀ (peanoLB 8)` with the uniqueness clause, from `erases_correct`
  and `firstorder_erases_core`. §1.3's refutation is exactly of the uniqueness half of this pair, at the fixture, not of the rung statement.
* At G8 the same five are contentless and the per-argument clause and the spine translation, vacuous at G1–G7 (`args = []`), are the live sixth and
  seventh there.

Three further clauses are vacuous, unchanged: **`ErasesEnv.blocks`' `IndFlagSound` conjunct** (no emitted block at any rung carries
`propositional = true`); **`ErasesEnv.axioms`, `LowerEnv.axioms` and `SpecContent.axioms`** (0 body-less emitted entries, 0 bodied keys lacking a
tabled body, at all eight rungs); **`LBWfPeregrine.etaCtorsTm`/`.casesExh`/`.fixLambda`/`.projDecl`/`ErasesEnv.elims`** at the rung ranges wave 4
recorded. `IndCovered.elims` is not trivial at any rung.

## 4. What is open

### The whole-ladder vacuity — the repair, and what depends on it
The single change that removes `constOriginExcludes`, un-vacuums every rung and the capstone's
observable conjunct, and restores the uniqueness conjunct at `Nat.zero`: read `ConstOrigin`,
`CtorOf`, `IndInfo`, `CasesOnShape` and `IndBlockBelow` off **`env`'s own declaration list**
(`env.WF' ds` fixed, each predicate quantified over `d ∈ ds`), as MetaRocq's `declared_constant`/
`declared_inductive` read `lookup_env Σ c` — a function of the environment, where a `VEnv.WF'`
witness below `env` need only produce a matching sub-environment and so may re-declare a
constructor as an axiom or permute a block's members without perturbing `env` itself. Within one
fixed list a constant has exactly one introducing step (`consts_origin`, landed, plus
`addConst_eq`/`addConst_foldlM_fresh`), so exclusion and uniqueness both follow with **no
further fork change** (`scratch/round7/U2-report.md` §4). The residue is downstream: restating
`ConstOrigin`/`CtorOf`/`IndInfo`/`CasesOnShape`/`IndBlockBelow` in `Erases.lean`/`SourceEval.lean`
and, with them, `Erases.const`/`Erases.ctor` — and `ConstOrigin.mono` and its three siblings do
**not** survive unchanged, since a list is not monotone in `env ≤ env'`, so the restatement is a
unit of its own that must start from where the `mono` lemmas are spent. Until it lands, every
rung, every `AccAsks`-premised accumulator step and the capstone's simulation are vacuous, and a
rung's own green elaboration is evidence that a checked term meets the *stated* interface, not
that the interface is inhabited by anything but the vacuous truth (`scratch/round7/W7-refute.md`
§7).

### `hbridge` — two producers landed, still zero consumers on the theorem's own proof path
`bridgeEnv_of_regContent` (`Capstone.lean:161-174`) composes `hbridge`'s payload out of `RegAcc`,
`RegKeyed`, `ErasuresDeclared env [] Γspec [] pe` and `htab`/`hlvl`, unchanged in shape since wave
4; `hdeps` is derived from `RegContent.declEnv` by `ReachableFrom.isSome_of_declaredEnv`, and the
binder's own `Lower Γspec t₀ t` premise is not spent. It is not on
`shipping_erase_correct_firstorder`'s proof path — which reaches its conclusion through
`erasure_bridge_of_run` plus `hbridge`, taken as a binder — and still has **zero consumers
anywhere in the tree** (`grep -rn bridgeEnv_of_regContent LeanToLambdaBox/ test/`: the
declaration and its ledger row only). Two stale sentences remain uncorrected in the file that
would carry the discharge, since fixing `Capstone.lean` is shipping-adjacent proof work outside
this unit's scope: `:157-158` says "no theorem produces `RegAcc` at a run **or `RegKeyed` at a
run**", but `regKeyed_of_run` (wave 4, W6) does produce `RegKeyed` at a run, and, since wave 6's
B-i..B-v/W9-C, `regInv_registerInd_run` and `regInv_recConst_step` each produce `RegAcc`
at a run *of one registration step* — not yet at a run of the whole eraser.

**What wave 6 and this wave's own commits actually built toward a producer.** `12-REPAIRS-W9.md`
renamed the re-planned pieces **W9-B** (the `register_inductive` prefix producer), **W9-C** (the
`visitMutual` recursive-constant block exit) and **W9-D** (the accumulator conjunct, its own
second bundle of eighteen motives, `AccGrows`). W9-B, blocked at wave 5, was decomposed into
five units (`scratch/round7/W9-B-report.md` §4) and all five landed this wave:

| unit | commit | what it proves | closes |
|---|---|---|---|
| B-i | `f7c1fda` | three `register_inductive` run lemmas (constructor-count threading, constants preservation, registry membership) | F-B-2, F-B-3, F-B-4 |
| B-ii | `3ab4675` | `IndBlocksCover lenv s` — the block table mirrors the emitted blocks | F-B-1 |
| B-iii | `24370d2` | the F-KERNAME layer: `toKername`'s non-injectivity, bounded and excluded on `_`-free root strings | F-B-7, F-W9-3 |
| B-iv | `c332a0b` | `IndPrefixOf`, the specification prefix a block registration conses, `BodiedKeysFresh` restated table-ranged | F-B-6, F-W9-1 |
| B-v | `e133eaa` | `regInv_registerInd_run` — `RegAcc` preserved across one block registration, plus two new re-established invariants, `RuntimeKeysModelled`/`EmittedNotRuntime` (F-B-8, F-B-9) | the row above |

W9-C (`18976fa`) is the recursive-constant sibling, `regInv_recConst_step`, landed the same way —
one commit, five declarations, each with a consumer inside the unit or named for W9-D's
`StepAcc6`. Both theorems are real, proved, `[propext, Classical.choice, Quot.sound]`, and
`regInv_registerInd_step` (W3), `SpecContent.append`, `SpecKeysEmitted.append` and
`RegContent.register_inductive_run` get their **first** consumers through them
(`scratch/round7/B-v-report.md` §1). What is still missing is the theorem that chains them
across a *run of the whole eraser*: `StepAcc6` (`visitMutual`'s own step of the accumulator
induction) is not landed, so nothing yet calls `regInv_registerInd_run`/`regInv_recConst_step`
at the value `Erasure.erase` actually produces, and `bridgeEnv_of_regContent` is therefore still
unreachable from the capstone (§ below, the accumulator bundle).

**The α gap and the ∀-`Γspec` shape mismatch are untouched.** `ReifiedDecl.Prepared` pins a
tabled body only up to `Expr.AlphaEq`, and `lake exe reify --check` reports five of G7/G8's
bodies matching only up to binder names; `RunRefines` still reads content at *every* `SpecEnv` of
the final state where the repair above produces one — superseded by the accumulator plan
(`12-REPAIRS-W9.md` §2.5, W9-D) rather than by restating `RunRefines` itself, so its eighteen
existing step lemmas stay untouched.

### The accumulator bundle (W9-D) — seventeen of eighteen steps, still no producer for `AccState`
`bfc7023` (D1) re-lands the staged bundle (`AccState`, `AccGrows`, the eighteen `MotiveAccᵢ`,
`AccAsks`, the eighteen `StepAccᵢ`, `motives_of_steps_acc`, `accGrows_register_inductive`, and
fifteen proved steps) byte-for-byte against post-`b96a4bc` HEAD; `fb4e166` (D2) proves steps 4, 5
and 17. **Seventeen of eighteen are proved; `StepAcc6` alone is left**, blocked exactly where
`scratch/round7/W9-D-report.md` §3 measured before wave 6's producers landed. `AccGrows`
(`∀ Γ₀, AccState … s → ∃ Γ₁, SpecGrow Γ₀ Γ₁ ∧ AccState … s'`) has **no producer**: `grep AccState`
outside `MotivesAcc.lean` is empty, so even a complete eighteen-step induction yields a
conditional nothing can trigger, and `motives_of_steps_acc`, the new aggregator, has **zero
consumers**. Five of the seventeen landed steps — all three block-registering members (3, 10,
17) and both constructor-η steps (13, 14) — are four-line consequences of `AccAsks.upstream`
alone, since the whole-ladder vacuity above makes every step whose own premises mention a block
positively trivially true (`scratch/round7/W9-D2-report.md` §2.3, mechanised in
`scratch/round7/j_1.lean`); `accGrows_register_inductive`'s entire consumer set is exactly those
three steps.

**Why D2/D3/D4 did not land, and what they now are.** The task's D2 (`Lower.constsDeclared_source`,
`h : Lower Γ u v → ConstsDeclared Γ v → ConstsDeclared Γ u`) is **false**: `Lower.elimApp`'s
dropped eliminator-spine prefix `pre` has no counterpart in the target term, so a constant named
only inside `pre` is invisible to `ConstsDeclared Γ v` (`scratch/round7/W9-D2-report.md` §4,
mechanised, `[propext, Classical.choice, Quot.sound]`, witnessed at a two-entry environment).
What is true is a three-step route through a second induction on `Erases` (every `pre`-position
of an eliminator spine in an erasure image is `□`) that the task's D2 does not name — rescoped as
**D2a** (a third eighteen-motive bundle proving `ConstsDeclared Γspec t` at the emitted term,
F-W9-5) and **D2b** (the `Erases` induction itself); **D3** is the constant-key `SpecEntryOk`
layer (F-D-1), **D4** the block exit's prefix produced from a run (F-D-3), both unchanged from
`W9-D-report.md` §5. All four have exactly one consumer, `StepAcc6`, and none of the seventeen
landed steps needs any of them, so per rule (7) nothing of D2/D3/D4 landed.

### `hfo` (HFO) — nothing landed; the target is self-defeating even before the round-5 asks land
`FirstOrderInd env I` demands a **block** on `env`'s own list (`HasInduct`) and a first-order
property quantified over every member of it (`FirstOrderDecl`); the rung binders reach
`HasInduct` (`indInfo_of_tabled → IndInfo.indDeclOf A → IndDeclOf env J`) but the member-list
identity `decl.types.map (·.name) = iv.all` has **no route**: `BlockAdequate` is per-name, so two
calls of its `fwd` field at two members of one kernel block produce two unrelated model blocks,
and neither `indBlockKername`'s non-injectivity nor ask 2's `indBlock_uniq` (which needs the
identity already) can join them (`scratch/round7/HFO-report.md` §1–§2). Independent of the
findings below, discharging `hfo` from `P`/`htbl` is now **self-defeating**: `indInfo_of_tabled`
alone already gives `IndInfo env ``Nat`, which contradicts `A` by the same route as §1's
`no_tabled_ind` — so the rungs cannot hold `hfo` and `A` together at all, independent of anything
below (`scratch/round7/W7-refute.md` §2.2). Three findings stand, unfixed:

1. **The concrete missing fact.** The landed `TrEnv'.inductInfo_inv`/`TrEnv.inductInfo_inv`
   (round-4 asks, item 4) delivers `TrIndType.all = decl.types.map (·.name)` through
   `InductOrigin`, but `InductOrigin` carries **no declaration list** — `decl.WF env₀` is not
   `env₀.WF' ds₀` — so neither `HasInduct` nor `IndBlockBelow` follows, and the block it exhibits
   cannot be identified with the one `IndDeclOf` exhibits. The missing fact is a fusion of
   `TrEnv'.find?_induct` with `TrEnv'.wf`, stated as `TrEnv'.inductInfo_wf'`
   (`scratch/round7/HFO-report.md` §3, statement elaborated against `8cc17a5` in
   `scratch/round7/hfo_probe5.lean`) — a strengthening of a landed proof, not new mathematics,
   but not reproducible in this repository without transcribing both of the fork's inductions
   (~110 lines).
2. **`env_connect`'s kind is the wrong one.** `TrEnv.inductInfo_inv` reads
   `Lean.Kernel.Environment.find?`; every fact a rung holds about an inductive is stated at
   `Lean.Environment.find?`, and the two are not definitionally equal
   (`scratch/round7/hfo_probe3.lean`, `rfl` refused) — the same irreducible step
   `decl_adequate`'s amendment already records for a different field. Even with finding 1 landed,
   `firstOrderIndB_sound` needs a class-**D** sibling of `decl_adequate`, a specification-bundle
   decision, not a derivation.
3. **`firstOrderIndB` is unsound as written, at no cost to fix.** `foMemberB`'s field test stops
   at the first non-`.forallE` node of a constructor's *model* type, so a telescope interrupted
   by `mdata` or a `let` passes vacuously while `FOType` — admitting only `.const` — then fails;
   no theorem is false today (no soundness statement exists) but the soundness statement cannot
   be proved against the checker as it stands. The fix is one conjunct pinning the kernel
   telescope's length to `cval.numParams + cval.numFields` (from `TrIndType.ctors`), true on
   every table this repository has, and belongs in the same commit as the soundness theorem.

**The round-5 commission.** A draft exists at `../lean4lean/downstream-asks-round5.md`
(untracked in that checkout, branch `trproj`, not committed there). It asks for `mkAppsInv` and
`indSpineInj` (the two open `UpstreamAsks` fields, items 9/10) and re-files the two open `TrProj`
sorries (`TrProj.weak'_inv`, `TrProj.uniq`) by name. Its "Closed, not asked" section marks the
`TrEnv'` induct/`AddInduct` inversion **fully delivered**, needing no further fork work — which
finding 1 above contradicts: `InductOrigin` alone does not supply the declaration list `hfo`
needs. The draft's own closing paragraph anticipated exactly this ("if that turns out false, the
corrected ask will name a concrete missing fact rather than repeat this one"), so the draft as it
stands needs amending with `TrEnv'.inductInfo_wf'` before a round-5 commission is sent; deciding
finding 2's specification-bundle question and adding finding 3's conjunct are downstream work
that lands after, not through, a fork change.

### `C21`, `U6`, `U7` — mechanical, landed, correct
`grep -rn "namespace Lean4Lean" LeanToLambdaBox/` is empty (`C21`, `ae7b9b8`): the round-4 pin
landed `VContext.ofMLCtx`/`VState.WF.initial`/`M.WF.run'` upstream verbatim, and the seventh
declaration, `kernelNGen` — a name the fork never introduces, inlining
`({} : Lean4Lean.TypeChecker.State).ngen` instead — is now `LeanToLambdaBox.kernelNGen`, an
`abbrev` for that same expression, outside any `Lean4Lean` namespace. `U6` (`1fc7c0c`) retires
`UpstreamAsks.constArityInv` in favour of `Lean4Lean.VEnv.IsDefEqU.const_arity_inv` at all three
consumers (one more than the commissioning text named: `FirstOrderInd.notSortNotPi`). `U7`
(`b87b3cc`) retires the local `wf'_induct_origin` in favour of `VEnv.WF'.induct_origin` at all
six call sites (one more than the map's grep found: `ErasesTotal.lean:107` itself). Neither
changes a ledger row. One stale sentence landed with `C21`: `doc/trust.md` (c1) said "this
repository still does not edit the fork **or move the pin**" — the same wave moved the pin
(`16d2271`) — corrected here.

### The disconnection census
`scratch/round7/W7-refute.md` §4 walks the constant graph of every declaration this repository's
modules define (6607 declarations) for a genuine reader in a **statement** or **proof value**,
not by `grep`: **1822** have zero consumers at the environment level, and after removing
compiler-generated declarations and intersecting with source-level declaration sites, **441
hand-written declarations have no consumer anywhere** in `LeanToLambdaBox/`, `test/`, `Tools/`,
`VerifyBench/`. This is the environment-wide count, broader than and not the same measure as
`lake exe hygiene --dead`'s file/import-closure budget (§5).

**New this wave (19).** `motives_of_steps_acc`; the seventeen landed `stepAcc_*` steps —
`visitExpr`, `visitLiteral`, `visitConstructor`, `visitConst`, `getConstantKername`,
`visitAppArgs`, `visitLet`, `visitLambda`, `visitProj`, `visitApp`, `visitConstApp`,
`visitCtorEta`, `visitCtorEtaGo`, `visitCasesEta`, `visitCasesEtaGo`, `visitCases`, `visitAlt`;
and `AccGrows.inl`. `CtorOf.constOrigin`/`IndInfo.constOrigin` (U2) are library-internal
zero-consumer, read only by `test/Vacuity.lean`'s records.

**Standing, re-confirmed at HEAD.** `bridgeEnv_of_regContent` (ledger row only), `regKeyed_of_run`,
`indBlocksCover_of_run`, `env_motive_tabled`, `no_realizer_exit_compiler`, `bridgeInv_member`,
`visitMutual_member_erases`, `visitMutual_member_erases_block`,
`visitExpr_refines_erasesLB_shape`, `visitExpr_refines_erasesLBFix_shape`,
`visitExpr_refines_erasesLBFix`, `Green.noTabledCasesOnBodies`, `Green.g1_noBodylessRefs` …
`g8_noBodylessRefs`, `Green.g7_natCasesOn_tabled`, `FOModel.firstOrderInd_E`,
`firstorder_erases_deterministic`, `firstorder_no_box`, `pass_subarray_next`, `pass_list_next`,
`pass_rco_split`, `visitMutual_block_hfl_of_run`, `fixtureBlock_lowerBlock`. The eight
`green_G<i>` are zero-consumer by design (the ledger reads them from `test/`).
`Green.tableRecPrefixed_rungs` (named at wave 5) is **absent** at HEAD — deleted by wave 6's
prune, per explicit task instruction, being vacuous at every rung by its own docstring.

Ledger-visible unused binders: `erasure_bridge_of_run` still carries the dead `hblk`;
`shipping_erase_correct_firstorder` and `green_G1..G8` have none; `FirstOrderInd.notSortNotPi`
and `indSpine_ne_forallE` carry an unused `A` since U6's swap; `consts_classified` an unused
`_A`; `constOrigin_of_constants` `_A,_hnc,_hni`; `step_visitConst` `_htbl,_hcfg,_hcb`;
`step_visitConstructor` `_htbl,_hcb`; `step_visitCases` `_hcb`.

### Two theorems stated under a premise they no longer use
`U2`'s `consts_classified` and `constOrigin_of_constants` are now unconditional facts (derived
from `constOrigin_of_wf`, off `VEnv.WF'.consts_origin`) stated under the refuted `A :
UpstreamAsks env`, which neither proof body spends (`unused=#[_A]` and `#[_A,_hnc,_hni]`
respectively, `scratch/round7/W7-refute.md` §2.1). Dropping the binder costs two call-site edits
(`step_visitCases`, `step_visitConst`, both of which already hold `env.WF`); not done this unit.

### `Lower`'s non-determinism at a block member
`LowerEnv.defs`'s second disjunct (the η-wrapped arm F-ETA added) is redundant — it collapses
into the first through `Lower.fixEta_of_block` — but its *presence* means `Lower.fixBody` and
`Lower.fixEta` both relate the same specification body to two different emitted terms, so
`Lower` is provably not a function: `¬ ∀ Γ s t t', Lower Γ s t → Lower Γ s t' → t = t'`
(`scratch/round7/W2-refute.md`, R3/R4). Nothing in the tree assumes `Lower` functional. Unchanged
since wave 2.

**lean4lean asks.** The commission trail is `downstream-asks-round4.md`
(landed, `../lean4lean` checkout) and the round-5 draft above (this repo's register is
`doc/upstream-asks.md`). Items 2 and 6 landed this wave (above); item 3 (checker-adequacy) landed
six of seven declarations, the seventh retired downstream instead (`C21`); item 4 (the kind
transfer from `lenv` to `env.constants`) is the `hfo`/`ErasesEnv.tabled` blocker, now with a
concrete missing fact named (above) rather than a bare "waiting on item 4"; items 9 and 10 are
open, drafted for round 5; `TrProj.weak'_inv`/`TrProj.uniq`, entirely unproven at the pin, still
block `hcb` at G2–G8 — 10 of G7's 30 tabled bodies carry an `Expr.proj`, all class projections,
and `TrExprS` at a `.proj` routes through it.

**`hev` stays vacuous outside G5.** `Green.g5_seval` is the only constructed source-evaluation
witness in the tree; every other rung, G7/G8 included, binds `hev` rather than proving it —
`benchArith 0`'s 45 recursive calls each owe N20's derivation for the unselected minor, against
G5's 45-line, three-`StepDefeq` cost for a single δ and ι. Unchanged this round.

**`hbody`'s residue (was `hargReach`, W7/U9) — unchanged this round.** `Green.g8_hargReach`
(`Green.lean:1592-1605`) reduces the binder to a residue quantified over every `Γspec` rather
than the run's own, strictly stronger than what it replaced and forced by the strengthening
(`Γspec` is not in scope at the binder any more). Satisfiable, not vacuous, not refutable
(`scratch/round7/W4-refute.md` §1.2): the tabled body `fun n => 2 ^ (((n * 3) - n) + 3)` erases
through `Erases.lit`'s peano towers, which do name `Nat`'s block.

**Shipping findings from `dev/fix`.** `doc/rework/03-DEV-FIX.md`'s "Applied edits" table remains
the single index, twelve shipping findings plus F-FUEL, unchanged this round: the ten from the
first merge (F-PROP, F-ETA, F-ETA2, F-SPARSE, F-EQREC, F-QUOT, F-ACC, F-DEPTH, F-UNSAFEREC,
F-KERNAME), plus F-DEPLCTX/F-ARITYLET from the second merge. **F-PRODUCT** remains the one item
not fixed and not meant to be: `auto_inline_typeclass_dispatch`
(`LeanToLambdaBox/Erasure.lean:85`, `:88-118`, `:896-903`), off by default, a class-**E** row in
`doc/trust.md`. No wave-6 or wave-7 unit touched a shipping file
(`LeanToLambdaBox/{Basic,Erasure,Printing,Relevance}.lean`), consistent with rule (1).

### Carried into the next wave
1. **Restate the block readings off `env`'s own declaration list** (§ above). Nothing else in
   this list matters until it lands: every rung, every `AccAsks`-premised step and the capstone's
   simulation are vacuous until then.
2. **Land `StepAcc6`.** Needs, in order: the block-exit decomposition W9-C §3 names (chaining
   `run_mkFreshFVarId_list` and `run_rec_exit_siblings_chained` under one statement — unbuilt);
   D2a (a third eighteen-motive bundle for `ConstsDeclared Γspec t`); D2b (the `Erases` induction
   proving `Lower.constsDeclared_source`'s honest form); D3 (`SpecEntryOk`); D4 (the block exit's
   prefix from a run). None has a consumer among the seventeen landed steps, so none lands until
   `StepAcc6` is attempted as a whole.
3. **Land the round-5 fork commission**, amended with `TrEnv'.inductInfo_wf'` (above), before
   `hfo`'s blocker can move; decide the `env_connect`-level specification question (finding 2)
   first, since it changes what the ask buys.
4. **Drop the two refuted-but-unspent binders** from `consts_classified` and
   `constOrigin_of_constants` (two call-site edits each).
5. **Two one-line fixes**: `Capstone.lean:157-158`'s stale "no theorem produces `RegAcc`...or
   `RegKeyed`...at a run" sentence (both now have run producers, though not yet at a run of the
   whole eraser); no other stale text found this wave.
6. `ErasureSpec.propositionalInd_of_arity` still needs a landed consumer.

## 5. Delivery
Branch `dev/verify`: 337 commits ahead of `main`, 85 ahead of the last-pushed
`origin/dev/verify` (`e7894de`), 15 of them since the wave-5 status commit (`99f4da2`) — seven
wave-6 (`740dd7c`, `f7c1fda`, `3ab4675`, `24370d2`, `c332a0b`, `e133eaa`, `18976fa`) and eight
wave-7 (`16d2271`, `ae7b9b8`, `1fc7c0c`, `b87b3cc`, `b96a4bc`, `bfc7023`, `fb4e166`, `e2ff202`).
`lake build` green at 178 jobs, `lake build VerifyBench` at 195
(`scratch/round7/gate7/01-build.out`, `18-build-verifybench.out`); the only `sorry` warnings are
lean4lean's seventeen (§1), and the same two pre-existing linter warnings
(`LeanToLambdaBox/Semantics/Substitution.lean:231`, `LeanToLambdaBox/ColdStartShape.lean:473`)
stand, unmoved by either wave.

`.github/workflows/build.yml` runs the whole battery on pushes to `main` and `dev/verify`, with
only `LICENSE` in `paths-ignore`. Every check in it is green at HEAD, re-run for this document
end-to-end against a clean tracked tree (`scratch/round7/gate7/final/full-rerun.out`, exit 0,
`== ALL GREEN ==`; `scratch/round7/gate7-report.md`), after fixing two bookkeeping drifts the
run itself found — the coverage census (§3, `e2ff202`) and `lake exe hygiene --dead`'s budget,
raised 339→343 the same commit after `b96a4bc` added four counterexample records to
`test/Vacuity.lean` (`natZ_constOrigin`, `natN_constOrigin`, `not_upstreamAsks_natEnv`,
`erases_natZ_two_ways`) using the already-budgeted construction its five siblings use.
`lake exe hygiene --dead` now lands at exactly its **343**-declaration budget: the 240
`doc/coverage.md` accounts for (tooling 107, frozen benchmark sources 43,
`LeanToLambdaBox/Optimize.lean` 71, `LeanToLambdaBox/ErasesUniform.lean` 19), `test/Vacuity.lean`'s
now-**nine** regression lemmas, and the 94 declarations under the twelve `test/fixes/` shipping-fix
regressions. `lake exe hygiene --dup` reports 3225 declarations, 0 duplicated names; `--tables`
26 arms, 0 unnamed; `--cites` 449 cited paths in 134 files, 0 missing; `--schedule` 0 inversions;
`green-check --all` 8/8 rungs green (§1's finding does not change any rung's checked-term status,
only what that status is evidence *of*, per §4).

The pin is lean4lean `8cc17a54c41c5e364596f8e4039e1f2094523a88` (`trproj`, the round-4 landing) —
`lakefile.toml`, both fields of `lake-manifest.json`, the first line of
`test/lean4lean-sorries.expected`, moved this wave (`16d2271`); `lean-toolchain` untouched.
Every measurement in this document was taken at it. Both consumers still pin `main` —
peregrine-tool's Lean test lakefile (`test/lean/lakefile.lean`) and the frontend benchmark's
(`benchmarks/frontend_bench/lean/lakefile.lean`), in the sibling checkouts — resolved to
`42f8f51` and `f54d17d`, ancestors of this branch, so neither builds the verified eraser.

A note the vacuity finding (§1, §4) makes worth stating here: every row of the table below that
reads a rung's own elaboration as evidence ("PASS", "checked term") is evidence that the checked
term meets the *stated* interface, not that anything satisfies it beside the vacuous truth — the
rows are unchanged by the finding, since they answer a different question ("does this term
elaborate at this statement"), but a reader combining a "PASS" row with a claim about the source
program should read §1 first.

| # | Verdict | Reason |
|---|---|---|
| 3, 4, 10, 11, 12, 14, 15, 16, 17, 19 | PASS | — |
| 1, 2, 5, 6, 8 | PASS as amended | eleven `Erases` rules — ten congruences plus `box`, `ctor` the eleventh — with no `.case` and no `.fix`, and `ctor`'s argument list literally `[]`; one L4 pass, `optimize`, with `LBOptimize_correct` and three non-vacuity guards; T5's naming half clean at eight premises; `FirstOrderInd` decides true on `Nat`, `Bool` and `FOFixture.Tree`, with `List` and `Prod` excluded on purpose |
| 9 | PASS as renamed | `ErasureSpec.oracle_sound_of_run` — in the capstone's closure, discharged, not assumed |
| 13 | PARTIAL | `green_G7` and `green_G8` elaborate; four of the capstone's fourteen binders are checked terms at both — `hcfg`, `hwt`, `hsup`, `hwf` — and ten stand, with `hcb` among them from G2 on (`hnb` is gone entirely, not merely discharged); G8 carries one binder the other seven do not, `hbody`, for its non-empty spine |
| 18, 20 | SPLIT | narration clean, comment fraction 28.4% tree-wide (14236/50188 lines, 72 files) with 8 files under 20% (`scratch/round7/status-doc-hygiene.out`); the exception list to the no-dead-code rule is **empty**, and `lake exe hygiene --dead` reports 343 declarations outside the closure (above) |
| 7 | FAIL — no subject | `Subsingleton` does not occur; the condition is `Erasable`, discharged by `Erases.sort_erasable`/`forallE_erasable` and by the oracle |
| 21 | PASS | `grep -rn "namespace Lean4Lean" LeanToLambdaBox/` is empty: `C21`, this wave |
| 22 | FAIL on the branch half | pin and CI pass; the verified eraser is on `dev/verify` and both consumers pin `main` |

## 6. How to re-measure

    lake build ; lake build VerifyBench ; lake exe coverage --check
    bash scripts/fixes.sh
    bash scripts/ledger.sh ; bash scripts/erases_correct.sh ; bash scripts/erasesLB.sh ; bash scripts/lean4lean-sorries.sh
    bash scripts/frozen.sh ; bash scripts/hygiene.sh --allow test/hygiene.allow
    lake exe hygiene --dup ; lake exe hygiene --schedule ; lake exe hygiene --tables ; lake exe hygiene --cites
    lake exe hygiene --anti-epicycle LeanToLambdaBox/Lower.lean ; lake exe hygiene --dead   # --dead is a budget of 343
    lake exe green-check --self-test ; lake exe green-check --all
    lake exe reify --check LeanToLambdaBox.Green …g1Table…g8Table ; lake exe reify --blocks LeanToLambdaBox.Green …g1Table…g8Table
    lake exe reify --prepared LeanToLambdaBox.Green LeanToLambdaBox.Green.spikeZero … arithClosed benchArith

`.github/workflows/build.yml` holds the argument lists in full. `--prepared` takes constant names, not table names, and `lake build VerifyBench` must
precede `coverage --check`, because the five corpus `.ast` files it measures are build artifacts. §1's whole-ladder-vacuity finding is not re-measured
by this battery — every check above asks whether a term elaborates or a fixture computes, never whether a rung's hypothesis set is satisfiable — and is
instead re-checked by reading `scratch/round7/j_1.lean` (`lake env lean scratch/round7/j_1.lean`, `sorry`-free) or by re-deriving §1's three routes from
`LeanToLambdaBox/Origin.lean`'s `CtorOf.constOrigin`/`IndInfo.constOrigin` and `Supported.lean`'s `indInfo_of_tabled` directly.
