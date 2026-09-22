# 07 — Status

## 1. The theorem
`LeanToLambdaBox.shipping_erase_correct_firstorder` (`LeanToLambdaBox/Capstone.lean:187-261`).
Subject: `Erasure.erase`, the function `#erase` calls, from the empty state at a pinned
configuration. If the run returns `.untyped Γ (some t)` on a source term `e` whose prepared form
is `pe`, then there are `Γspec` and `t₀` with `Erases env [] [] pe t₀` and `Lower Γspec t₀ t` —
the emitted term is the lowered image of an erasure of the prepared term — together with
`ErasesEnv env tbl.body? tbl.levels? Γspec t₀`, `LowerEnv Γspec Γ` and `LBWfPeregrine Γ t`: the
emitted environment is the lowered, pruned image of `Γspec`, and the emitted program satisfies
what peregrine's first pass reads — `expandedFix` included, since F-ETA's registered fixpoints
are the η-expansion `LBTerm.etaFix`, not a bare `tFix` node (`PeregrinePre`, the separate,
stronger predicate an earlier draft of this theorem needed, is deleted: `LBWfPeregrine` alone is
now that statement). The last conjunct before the observable is the theorem's own binder `hwf`,
carried rather than derived, and every rung discharges it by kernel computation. The observable
conjunct is a forward simulation at first-order answers: for closed `args` whose λ□ images
`targs` each carry an erasure, that erasure's lowering and its own `ErasesEnv` clause, and whose
applied spine has a translation `TrExprS env [] [] (mkApps pe args) vs`, if
`SEval env tbl.body? [] fullFlags [] (mkApps e args) v` and `v` is typed at a spine of an
inductive `I` with `FirstOrderInd env I`, then `WcbvEval Γ eraseFlags (LBTerm.mkApps t targs) tv`
for the `Lower` image `tv` of the unique erasure `tv₀` of `v`, with `NoBox tv`. That is `[S]`
§7.3–7.4's shape with λ□'s own `WcbvEval` as target semantics, `Lower` carrying the four
Lean-specific compilation steps, and the source evaluation reading the compiler-body table (N8).
The per-argument clause and the spine translation are what `erases_correct` requires of a spine;
at `args = []` both are vacuous, which is where G1–G7 apply them.

**`hbridge` is still a binder; `hargReach` no longer exists under that name.** Round 7 wave 4
(`341e2a9..d16c1c2`, 17 commits: the second `dev/fix` merge plus units W1–W9 and one
bookkeeping commit) worked `doc/rework/11-REPAIRS-W8.md`'s plan; its own re-refutation is
`scratch/round7/W4-refute.md`. `hbridge` is unchanged in kind: `grep -rn "\bhbridge\b"
LeanToLambdaBox/` is 24 hits, `shipping_erase_correct_firstorder`'s signature
(`Capstone.lean:206-210`) and all eight of `Green.lean`'s rungs (`:226`, `:379`, `:480`, `:601`,
`:854`, `:975`, `:1572`, `:1633`) still take it, and `erasure_bridge_env` — the theorem
`doc/rework/09-REPAIRS-W7.md` §2.9 planned to give it that shape — is still stated nowhere
(`grep -rn erasure_bridge_env LeanToLambdaBox/` is empty). `hargReach` is gone as a binder
name: W7/U9 replaced `green_G8`'s `hargReach` with `hbody` (`Green.lean:1638-1640`), a
*stronger*, source-side statement — every erasure of `benchArith`'s tabled body reaches `Nat`'s
block, quantified over every `Γspec` rather than read at the run's own one — and `grep -rn
hargReach LeanToLambdaBox/` now finds only the theorem name `g8_hargReach` (`Green.lean:1528`,
a proved lemma `green_G8`'s proof calls, not a binder) and docstrings recording the rename.
`doc/coverage.md`'s generator has not caught up: `Tools/Coverage.lean:276`'s `audited` list
still reads `"hargReach"` rather than `"hbody"`, so the regenerated ladder table correctly
shows `—` at G8's `hargReach` column (no rung binds that name any more) while the hardcoded
sentence below it, `Tools/Coverage.lean:735`, still asserts "G8 alone binds `hargReach`" — the
table and the prose next to it now contradict each other in the committed, up-to-date
`doc/coverage.md`. Recorded here rather than fixed: `Tools/Coverage.lean` is outside this
wave's file list.

What actually moved: `hbridge`'s repair chain reaches further than wave 3 left it. W1 repairs
the `hsub` premise wave 3 refuted, as `SpecKeysEmitted` (§4); W5 folds it with `RegInvShape'`
and `RegContent` into one accumulator, `RegAcc` (`ColdStartShape.lean:1166-1173`); W6 proves
`RegKeyed` *at a run* for the first time, `regKeyed_of_run`
(`VisitExprRefines/Step/Passes.lean:1447`). None of it reaches the binder:
`bridgeEnv_of_regContent` (`Capstone.lean:158-171`), the theorem that would spend all three, is
still not on `shipping_erase_correct_firstorder`'s proof path — which reaches its conclusion
through `erasure_bridge_of_run` plus the binder `hbridge`, unchanged — and still has **zero
consumers anywhere in the tree** (`grep -rn bridgeEnv_of_regContent LeanToLambdaBox/ test/`:
the declaration and the ledger row, nothing else). No theorem produces `RegAcc` at a run —
that is W5a/b/c, re-planned this wave and not landed (§4) — so the route does not reduce
either binder's cost today. Apart from the one path that does reach a rung
(`Green.g8_t0 → Green.g8_hargReach → Green.green_G8`, W7/U9), this wave's landed or restated
declarations sit in **seven** further components whose roots `scratch/round7/W4-refute.md` §4
finds have zero consumers anywhere in the environment.

| Class | Binders |
|---|---|
| proved, or per rung a checked term | inside the theorem: the erasure half `erasure_bridge_of_run`, supplying all eighteen bridge steps; the answer's shape and uniqueness from `firstorder_erases_core`, and `NoBox tv` at the *lowered* value from `noBox_lower_of_foSpine`; the simulation, `erases_correct` applied once at the spine with `ErasesEnv.mkApps`; the observable's transport across the preparation passes from `prepare_sound`. At every rung: `hcfg : ConfigPinned`, `hsup : Supported`, `hwf : LBWfPeregrine` by `lbWfPeregrine_of_check (by decide +kernel)`, `hwt : TrExprS`, the target-side `WcbvEval`; `hcb : CompilerBodies` at G1 only; `hev : SEval` at G5 only. `hnb : NoBodylessRefs` is gone (W8, `e625855`): the proof never spent it, so it is deleted from the theorem and from all eight rungs' applications rather than carried as an unread premise — the theorem's own unused-binder scan is `#[]` |
| **C** — this repository's own code | `E : EraserAsks` — four fields, unchanged since W5: `passes_monotone`, `passes_sound`, `oracle_false_refl`, `kernel_ind_head_true` (residue: a *reduced* telescope longer than `isArityCheck`'s constant budget, and any other kernel error inside it). `block_keys_distinct` is deleted, F-UNSAFEREC's guard making distinctness a *conclusion* of a successful run (`run_rec_exit_reg`'s fifth conjunct) rather than a bundle field — though nothing today spends that conclusion: both call sites of `run_rec_exit_reg` discard it, and `run_rec_exit_nodup` and its would-be consumer `blockKeyed_install` each have no consumer of their own (§4). `hbridge`'s two fields — `erasesEnv` and `lowerEnv` — open, §4. `hbody` (named `hargReach` before W7/U9), at G8 alone — open, §4; reduced to a source-side statement quantified over every `Γspec`, strengthened but satisfiable (§4) |
| **D** — specifications of Lean's `Meta`/`Core` primitives | `P : ∀ Us, ErasureSpec lenv env Us gw` — seven fields, unchanged: `env_connect`, `lookup_adequate`, `fresh_names`, `oracle_refl`, `decl_adequate`, `prim_monotone`, `block_adequate`; taken at every level scope since U5, which is what a sub-run below `Erasure.visitMutual`'s `withReader` needs. **`prim_monotone : PrimMonotone gw` is per-primitive**, not a blanket `MetaM` claim: eight clauses, one per named primitive (`getEnv`, `logInfo`, `isInstance`, `inferType`, `isProof`, `forallBoundedTelescope`, `lambdaBoundedTelescope`, `liftMetaM`), with the two bounded telescopes and `isProof` stated *compositionally* so the two anonymous continuations F-ACC/F-SPARSE introduced are covered by the derived `PrimGenMono` predicate rather than by a further universal (`ErasureSpec.lean:259-306`; C1, `8bdffca`, closing a finding raised against an earlier single unconditional `PrimMonotone.metaM` field, `scratch/round7/W2-refute.md` §5/R7). **`block_adequate : BlockAdequate lenv env` grew two fields this wave**, `selfName` and `fields` (W6, `ErasureSpec.lean:413-422`), each a property of `Lean.Environment.find?` alone — `fwd`'s fourth premise and the member loop's `.inductInfo` match had no producer at a registration without them (six fields → eight; `ErasureSpec`'s own top-level count stays seven, `block_adequate` being one field of it). `htbl : SourceTableAdequate`, `hsafe : TableSafe`, `hblk : TableBlocks`, `hprep` (the prepared term is the subject), `hrun` (the run produced the committed program) |
| upstream | `A : UpstreamAsks` — `constsOrigin`, `constArityInv`, `mkAppsInv`, `indSpineInj`: `doc/upstream-asks.md` items 2, 6, 9 and 10. `hvwt`, `hty` and `hfo` are class **C** too and stand at every rung; `doc/trust.md` has a row each, and `hfo`'s waits on upstream ask 4 |
| inherited `sorryAx` roots | sixteen in the pinned lean4lean (`test/lean4lean-sorries.expected`), under `.lake/packages/lean4lean/Lean4Lean/`: `Theory/Typing/ChurchRosser.lean:1193,1212`; `Theory/Typing/EnvLemmas.lean:334` (fork-authored); `Theory/Typing/Injectivity.lean:12,21,34`; `Theory/Typing/UniqueTyping.lean:174`; `Verify/Environment.lean:208`; `Verify/TypeChecker/InferType.lean:398,410`; `Verify/TypeChecker/IsDefEq.lean:227,488`; `Verify/TypeChecker/Reduce.lean:145`; `Verify/TypeChecker/WHNF.lean:149`; `Verify/Typing/Lemmas.lean:747,995` |

## 2. The measured axiom footprint
Verbatim from `test/ledger.expected`, which `bash scripts/ledger.sh` re-measures: `shipping_erase_correct_firstorder` and each of `Green.green_G1` …
`Green.green_G8` carry one identical set of 33 names.

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
`bv_decide` certificates come with it (`doc/trust.md` §(a3) sites all 29). Other rows: `erases_correct` (T5) and its three step arms `[propext,
sorryAx, Classical.choice, Quot.sound]`; T8's `visitExpr_refines_erasesLB` and `visitExpr_refines_erasesLBFix` `[propext, Classical.choice,
Quot.sound]`, no `sorryAx`; `LBOptimize_correct` `[propext, Quot.sound]`; `lbEval_sound` `[propext]`. **`bridgeEnv_of_regInv` and, since U9,
`bridgeEnv_of_regContent` are both `[propext, Classical.choice, Quot.sound]`, three names, no `sorryAx`** (`test/ledger.expected:123-124`) — not
"nine names" as an earlier draft of this section said of `bridgeEnv_of_regInv` alone. That earlier figure was true before U9: `bridgeEnv_of_regInv`'s
dependency-closure premise `hdeps` used to carry the `instantiateLevelParams` axiom cluster: U9 replaced it with the *proved*
`ReachableFrom.isSome_of_declaredEnv`, so the theorem sheds the cluster along with the premise that carried it (`doc/trust.md` §(a4)).
`#print axioms` measures a proved theorem and never a hypothesis, which is why relocating a field of the bridge bundle to a binder of the capstone
moves no row, and why `decide +kernel` at a rung adds no name.

## 3. Coverage
`doc/coverage.md` is generated by `lake exe coverage` from the tree; `lake exe coverage --check` is green at HEAD (`scratch/round7/gate4/03c-coverage-check-after-fix.out`, after one bookkeeping regeneration this round, `d16c1c2`, that moved the whole-environment kername count 230,402→230,472 and retired the `NoBodylessRefs`/`hnb` prose W8 made stale). Arith is in
the fragment and is the subject of rungs G7 and G8. Sieve and
BinaryTrees are out at `recursorHead` on `Eq.rec` through `Bool.noConfusion` (F-EQREC); Quicksort at F-EQREC, the well-founded
`Nat.div.go`/`Nat.modCore.go` route and `sparseCasesOn`, with a wrong emitted program besides (F-SPARSE); Fannkuch at F-EQREC and `etaContractedMinor`
on `Decidable.casesOn`. Fannkuch's `NoBodylessRefs` failure — the one the capstone's own premise used to name, its reachable `Eq.rec` declared
body-less — is **closed**: `recursorRealizer` now gives that `Eq.rec` a `.case` body (F-QUOT's and F-EQREC's registering exit, §2.8 of
`doc/rework/10-MERGE-FIXES.md`), a strict gain measured in `doc/coverage.md`'s realizer census, so all five corpus programs and all eight rungs now
satisfy it; Fannkuch stays outside the fragment for the two reasons above alone.

"Arith is covered" means `supportedB` returns `ok` at the entry term and at every tabled body of `reify% arithClosed`; that `green_G7` instantiates
the capstone at the closed `arithClosed` and `green_G8` at `benchArith` applied to `0`; and that both conclusions end in the literal peano numeral
`8`, which `lake exe green-check` re-derives with `lbEval` from the byte-diffed `.ast`. It does **not** mean the source evaluation is derived: `hev`
binds at G7 and G8 as at G1–G4 and G6, because `benchArith 0` runs 45 recursive calls, each owing N20's derivation for its unselected minor, against a
45-line three-`StepDefeq` precedent for one δ and one ι at G5 — the constructed witness is at G5 (`Green.g5_seval`) and nowhere else. Nor does it mean
a rung is unconditional: `lenv` and `env` are universally quantified at every rung.

One clause of `LBWfPeregrine` was mis-specified, and correcting it is what makes five of the eight rungs say anything. The binder-name clause read
`Basic.cleanIdent`'s alphanumeric class, which `toKername` establishes for **kername identifiers** and which the eraser's binder names do not satisfy:
measured over each rung's emitted term and every constant body of its emitted environment, 0/1/1/1/0/0/34/34 offending names at G1…G8, 32 of them
distinct at G7 and G8 — `instOfNatNat`'s hygienic binder at G2–G4, and at G7/G8 the matcher-inlining binders together with the four `.fix` definition
names `Nat.add`, `Nat.mul`, `Nat.pow`, `Nat.sub`. Under that class G2, G3, G4, G7 and G8 had an unsatisfiable well-formedness hypothesis and were
vacuous. The clause is now `PrintableBinders`, the condition the quoted atom the printer emits actually imposes — the name closes and escapes no atom
— under which the count is 0 at all eight rungs; `Tools/Coverage.lean` recomputes both columns from `Green.g<i>Env`/`g<i>Term` at every regeneration,
so `doc/coverage.md` carries the measurement rather than a transcription of it.

A second clause was added rather than mis-specified: `LBWfPeregrine.expandedFix` (M3) folds in the three term-level conjuncts of MetaRocq's
`expanded_tFix` that `LBExpandedFix` alone did not state, and every rung's `hwf` is **re-decided** against the twelve-clause checker. It is true at
all eight without exception — `lbFixSelfAppliedB` and `fixLambdaNode` were already true on all eight, and the new spine conjunct, false exactly at
G6, G7 and G8 (the rungs whose `g<i>Env` registers a `.fix` node), is made true by wrapping those bodies in `LBTerm.etaFix`, `Erasure.etaExpandFix`'s
image, the same regeneration §5 already owes for other reasons. `lake exe green-check --all` re-derives this from the byte-diffed `.ast`, and it is
green.

### Which conclusion conjuncts are vacuous or literal, at which rungs

Round 7's audit (`scratch/round7/W2-refute.md`, `W3-refute.md`) measured the ten conclusion conjuncts of a rung against the committed `g<i>Env`/`g<i>Term`
literals rather than only against the rung's *statement*, and the same verdicts hold at G7 and G8 (`W3-refute.md` §2.1):

* **Five carry no content.** `hprep`'s equation is conjunct 1 re-exported verbatim (`Capstone.lean:203` = `:212`). `LBWfPeregrine g<i>Env g<i>Term`
  is the closed term `hwf`/`g<i>_wf`, checked once and carried, not derived from anything else in the conclusion. `NoBox (peanoLB 8)` is a literal
  fact about the answer, provable from scratch with no rung hypothesis. `WcbvEval g<i>Env eraseFlags g<i>Term (peanoLB 8)` is `Green.g<i>_eval`,
  itself a closed term; the rung's own `eval_deterministic` step only *names* the answer with it. `ErasesEnv … Γspec t₀` and
  `LowerEnv Γspec g<i>Env` are `hbridge`'s two fields, `ErasureBridge.erasesEnv`/`.lowerEnv`, assumed verbatim and re-exported, not derived.
* **Four carry the theorem's content**: `Erases env [] [] eG<i> t₀` and `Lower Γspec t₀ g<i>Term`, from `erasure_bridge_of_run` — a proved term about
  the *shipping* `Erasure.visitExpr` — and `Erases env [] [] v tv₀`/`Lower Γspec tv₀ (peanoLB 8)` with the uniqueness clause, from `erases_correct`
  and `firstorder_erases_core`. Those four are relative to a `Γspec` two of whose properties (the two fields above) the rung assumes rather than
  derives.
* At G8 the same five are contentless and the per-argument clause and the spine translation, vacuous at G1–G7 (`args = []`), are the live sixth and
  seventh there.

Three further clauses are vacuous at the ladder, carried forward from the pre-merge `V-vacuity.md` census and re-measured at HEAD
(`scratch/round7/z_triv.out`, `W2-refute.md` §2.3, `W3-refute.md` §2.3):

* **`ErasesEnv.blocks`' `IndFlagSound` conjunct** is vacuous at all eight rungs — no emitted inductive body at any rung carries
  `propositional = true` (0 of 1/2/2/3/2/1/12/12 declared blocks at G1…G8). It replaced a checkable, true demand (`= false`, unconditionally) with
  an equation whose sound half only is stated, so the biconditional was correctly not written as a guard against its counterexample — but the clause has no subject at any rung to be non-vacuous about. Since F-ARITYLET merged, the walk reads `destArity`'s `tLetIn` arm and the `let`-carrying arity is no longer the counterexample; what refutes the converse is zeta — `inductive FooBVar : (let u := Prop; u)`, whose image under `TrExprS.letE` is `Sort 0` while the walk stops at the `.bvar`, as PCUIC's `destArity` stops at `tRel`. The remaining gap is between lean4lean's translation and `destArity`, so W9's biconditional is not available and the sound half stands. W9 mechanised that refutation at the data `decl_adequate` supplies — `arity_of_propositionalInd_false` (`ErasureSpec.lean`), on `arityResultSort_letBVar` and `trExprS_letBVarArity` — so the clause's shape is a measured fact and not a standing argument.
* **`ErasesEnv.axioms`, `LowerEnv.axioms` and `SpecContent.axioms`** have no witness at any rung: 0 body-less emitted entries and 0 bodied emitted
  keys lacking a tabled body, at all eight rungs (`decide +kernel`). A standing vacuity, not introduced this wave — no rung reaches a quotient
  primitive or a recursor, so F-QUOT's and F-EQREC's registering exits are off every rung's path; `doc/coverage.md`'s realizer census is the only
  place a covered program registering a realizer is actually measured.
* **`LBWfPeregrine.etaCtorsTm`** is trivial at all eight (every `g<i>Term` is a bare `.const`, so `ConstructSpine` is uninhabited); `.casesExh` is
  trivial at G1–G4 (`case = 0`); `.fixLambda` at G1–G5 (`fix = 0`); `.projDecl` at G1, G5, G6 (`proj = 0`); `ErasesEnv.elims` at G1–G4 (no `.case`
  node). `IndCovered.elims`, by contrast, is *not* trivial at any rung — every informative declared block demands an `ElimDecl` — and §4 is where
  that turns into a refutation of a different clause.

## 4. What is open

### `hbridge` — the composition reaches further this wave, and still does not land
`bridgeEnv_of_regContent` (`Capstone.lean:158-171`) composes `hbridge`'s payload out of the
same four antecedents about the run's final state as before, restated: `RegAcc` (W5's fold of
`RegInvShape'`, its content clause `RegContent`, and the saturation clause `SpecKeysEmitted`
into one accumulator, `ColdStartShape.lean:1166-1173`), `RegKeyed`, `ErasuresDeclared env []
Γspec [] pe` at the prepared term, and the unchanged `htab`/`hlvl`; `hdeps`, the dependency
closure `bridgeEnv_of_regInv` still takes, is *derived* from `RegContent.declEnv` by
`ReachableFrom.isSome_of_declaredEnv`, and `hbridge`'s own `Lower Γspec t₀ t` premise is not
spent. Wave 3's refutation of the premise this composition used to take — `hsub : ∀ kn d,
envLookup Γspec kn = some d → envLookup sf.gdecls kn = some d`, jointly `False` with
`RegContent`'s content clause at G5–G8 and with the eliminator entry at all eight rungs
(`scratch/round7/W3-refute.md`, R1) — is **genuinely repaired, not renamed** (W1,
`86ce380`): the one place `hsub` was spent, `regSaturated_of_regKeyed`, now takes
`SpecKeysEmitted Γspec s` — "a specification key that isn't a runtime key has *some* emitted
entry of the matching shape," reading only shape, never body — and `scratch/round7/W4-refute.md`
§2 mechanises at one fixture (`f_repair.lean`, `[propext, Classical.choice, Quot.sound]`, no
`sorryAx`) that `hsub` is false and `SpecKeysEmitted` holds and is not vacuous there.
`SpecKeysEmitted` moved from `SpecEnv.lean` to `ColdStartShape.lean` with W5 and gained
`.nil`/`.append` clauses; W6 proves `RegKeyed` *at a run* for the first time, `regKeyed_of_run`
(`VisitExprRefines/Step/Passes.lean:1447`, by induction over `Erasure.visitExpr`'s own
recursive structure, `RunClosedW`) — the first theorem this wave produced about a run of the
*shipping* eraser rather than about a step lemma.

None of it reaches the binder. `bridgeEnv_of_regContent` is not on
`shipping_erase_correct_firstorder`'s proof path — which reaches its conclusion through
`erasure_bridge_of_run` plus `hbridge`, unchanged — and still has **zero consumers anywhere in
the tree** (`grep -rn bridgeEnv_of_regContent LeanToLambdaBox/ test/`: the declaration and the
ledger row only). What is missing is a theorem that produces `RegAcc` *at a run*:
`regInv_registerInd_step` (`ColdStartShape.lean:1289`, W3, `bf52139`) takes the fresh block's
prefix content — `SpecContent env bo lp pre`, freshness, closedness, ten side conditions in
all — as **premises** rather than deriving them, because `IndCovered` (what every member of a
freshly registered block needs) is never *introduced* anywhere in the tree:
`Erasure.register_inductive` visits every member of `iv.all`, so a step that registers a fresh
block owes coverage of every member, not only of the name it was called at, and nothing
supplies it (`scratch/round7/W5-report.md` §3). Re-planned as **W5a** (the
`register_inductive` → `IndCovered`/`SpecContent` producer, not built), **W5b** (the block exit
and the two `recursorRealizer` realizer sites, F-W8-6; the two constant exits are landed as
`RegAcc`-typed `regInv_addAxiom_step`/`regInv_constCons_step`) and **W5c** (the accumulator
conjunct threaded through all eighteen `visitExpr` motives). W5c's first attempt — fusing the
accumulator into `RunRefines`'s existing ∀-`Γspec` clause — is mechanised **impossible** in
that form (`scratch/round7/w5_probe.lean`, `runRefines_fused_not_composable`, sorry-free): the
composition of two sub-runs' growths has no `Lower` conclusion to carry across. W5's restated
form threads the accumulator as an **independent** fifth conjunct of `RunRefines` instead
(`visitExpr_regInv_all`'s printed statement is unchanged, and would be `RegAcc.coldStart`
instantiating the new conjunct at `Γ₀ = []`); none of W5a/b/c is landed. Separately, `hde`
itself is refuted at a block member's sub-run (`erasuresDeclared_false_at_app`,
`scratch/round7/q_w8.lean`) and its narrower repair (F-W8-7, restricting `hde` to the `t₀` that
actually lowers to `t`) is stated but not landed (`scratch/round7/W7-report.md`). The α gap
(`ReifiedDecl.Prepared` pins a tabled body only up to `Expr.AlphaEq`, and `lake exe reify
--check` reports five of G7/G8's bodies matching only up to binder names) and the ∀-`Γspec`
shape mismatch `RunRefines` still reads are untouched.

**An unrecorded dependency the repair rests on (new this wave).** `SpecContent.defns` carries
no `isCasesOnName` guard where `SpecContent.axioms` does, so a tabled `casesOn` with a compiler
body would make `RegContent`'s content clause self-contradictory through
`ErasesEnv.runtimeKey_isCasesOn`/`erases_ne_elimBody` — the route that made wave 3's attack on
`hsub` look reachable through a body in the first place. Measured at HEAD
(`scratch/round7/W4-refute.md` §1.1, `f_hbody.out`): at G5–G8 the only tabled `casesOn` name is
`Nat.casesOn`, and its `body?` is `false` at every one — the table carries the *declaration*,
not a compiler body — so the trigger never fires and `Green.g7_natCasesOn_tabled`'s reading
holds. But that theorem states only "`Nat.casesOn` is tabled," not "tabled without a body," so
a table regeneration that gave `Nat.casesOn` a compiler body would silently make
`green_G5`…`green_G8` vacuous, and nothing in the tree records that dependency or guards
against it.

### `hbody`'s residue (was `hargReach`, W7/U9) — strengthened, satisfiable, not refutable
`Green.g8_hargReach` (`Green.lean:1528-1541`) reduces the binder further than U9 left it: `Lower
Γspec t₀ g8Term` forces `t₀ = .const (toKername ``benchArith)` through `Lower.source_const`
(`.box` and `ctor` have no `Lower` arm to a `.const`), `ErasesEnv.defns` then produces the
declared erasure `b₀` of `benchArith`'s tabled body, and `ReachableFrom.through_body` reduces
the binder to one residue. W7 (`b26bb10`) makes `green_G8` take that residue directly as
`hbody`, dropping the binder's old dependence on the run's own `Γspec` and `ErasesEnv`:

    hbody : ∀ (Γspec : GlobalDeclarations) (b : Expr), g8Table.body? ``benchArith = some b →
      ∀ b₀ : LBTerm, Erases env (g8Table.levels? ``benchArith) [] b b₀ →
        ReachableFrom Γspec b₀ natIid.mutualBlockName

quantified over **every** `Γspec`, not the run's own. Since `ReachableFrom Γ t kn` is
`kn ∈ constRefs t` at `Γ = []` (`reachable_nil_iff`, `f_final.lean`), the strongest instance of
`hbody` is a direct-occurrence claim, and `scratch/round7/W4-refute.md` §1.2 checks it against
the tabled body itself — `fun n => 2 ^ (((n * 3) - n) + 3)`, whose two `OfNat.ofNat` literals
erase through `Erases.lit`'s `toConstructor` unfolding to peano towers that do name `Nat`'s
block — and finds it **satisfiable, not vacuous, and not refutable**: `hbody` is strictly
stronger than the `hargReach` it replaced (which was read at the run's own `Γspec`), and the
strengthening is forced, because `Γspec` is not in scope at the binder any more. `test/ledger.expected`
gains one row, `Green.g8_hargReach`, `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

### A hidden assumption, benign
C2c (`83382a5`) removed `TabledLevels` from `StepDelta`, where the capstone used to discharge it
by the *proved term* `tabledLevels_of_table htbl hsafe hcb`, and folded its two conjuncts into
`ErasesEnv.defns`, reachability-gated. `ErasesEnv` is what `hbridge` supplies, so at HEAD the
capstone **assumes** what it used to **prove**. Nothing is lost — the added conjuncts remain a
theorem of the capstone's own hypotheses (`defns_level_conjuncts_free (htbl) (hsafe) (hcb) =
tabledLevels_of_table htbl hsafe hcb`, `[propext, Classical.choice, Quot.sound]`) — but the
relocation makes `hbridge` look larger than it is, and `doc/trust.md`'s `ErasesEnv` row should
say the last two conjuncts are dischargeable today (`scratch/round7/W3-refute.md`, R2).
Unchanged this round.

### The disconnection census — this wave's declarations, and what reads them
`scratch/round7/W4-refute.md` §4 walks every constant of the environment (imports included) for
mentions of a target in its **type or proof value**, not by `grep`. Of the components W1–W9
landed or restated, exactly **one** is read by anything that reaches a rung
(`Green.g8_t0 → Green.g8_hargReach → Green.green_G8`, W7/U9); the rest sit in **seven**
components whose roots have zero consumers anywhere:

* zero consumers: `bridgeEnv_of_regContent` and below it `bridgeEnv_of_regInv`,
  `regSaturated_of_regKeyed`, `ErasuresDeclared` (W1/W5); `refsStable_of_freshPrefix`,
  `ErasesLBMode.specGrow`/`ErasesLBAltMode.specGrow` and the composite transports below them
  (W2); `regInv_registerInd_step` and below it `SpecContent.append`, `SpecKeysEmitted.append`,
  `RegContent.register_inductive_run`, plus the whole Green eliminator-key section —
  `noCasesOnKeys`, `elimKey_undeclared_of_noCasesOnKeys`, `elimPrefix_specGrow`,
  `g7_natCasesOn_tabled`, `g7_constsDeclaredEnv`, `g8_constsDeclaredEnv` (W3); `bridgeInv_member`,
  `visitMutual_member_erases`, `visitMutual_member_erases_block` and below the last,
  `visitMutual_block_mode`, `blockKeyed_install` (W4); `RegAcc.coldStart`,
  `regInv_constCons_step`, `regInv_addAxiom_step` (W5); `regKeyed_of_run`, `regKeyed_empty` and
  below them `runClosedW_regKeyed`, `regKeyed_register_inductive`, `RegKeyed.indCons`,
  `regKeyed_recConstState` (W6); all eight `g<i>_noBodylessRefs` (W8, see below).

Two of this wave's own "landed / kept" claims are true only one link deeper than before, not
resolved: `hblk : TableBlocks` (kept at W8, since W4 already gave `blockKeyed_install` a
consumer, `visitMutual_block_mode → visitMutual_member_erases_block`) is a real, three-link
chain now rather than the two-link dead end wave 3 measured — but its *top*,
`visitMutual_member_erases_block`, still has zero consumers of its own, and
`erasure_bridge_of_run`'s own unused-binder scan is still `#[hblk]`: the binder is spent only at
a separate proof term's own copy, never at the one the capstone calls. Likewise
`SourceTableAdequate.compilerLevels` (kept at W8): `compilerLevels → compilerLevels?_eq →
visitMutual_member_erases`/`_block`, chain length 2 → 4, both tops still zero-consumer.
`W3-refute.md` R3a's "a repaired clause nothing reads is a hypothesis the ladder pays for and
never spends" therefore still holds of both; only the chain length moved.

**Cost without reach.** `regKeyed_of_run` is the one theorem this wave proved about a run of the
shipping eraser, and it cost two new class-**D** fields on `BlockAdequate` (§1) that every rung
now carries through `P` — and it has no consumer. The fields are individually consistent
(`Lean.Environment.find?` properties, §1), but by W9's own standard ("nothing in the tree
constructs an `ErasureSpec`, so a field added to make a theorem go through is not
distinguishable, from inside the tree, from assuming the theorem") the pair is a debt taken in
advance of a reader that does not yet exist.

**Two smaller findings from the same audit.** The eight `Green.g<i>_noBodylessRefs` lost their
last reader when W8 deleted `hnb` (below): `Tools/Coverage.lean:305-309`'s `nbTerm` column reads
only whether the *declaration exists* (`env.find?`), never what it says, so
`doc/coverage.md`'s per-rung `NoBodylessRefs` column is an existence census, not a content
check. And two docstrings cite a theorem under the wrong qualified name: `ErasesEnv.lean:48` and
`Erasability.lean:425` cite `ErasureSpec.arity_of_propositionalInd_false` where the declaration
W9 landed is `LeanToLambdaBox.arity_of_propositionalInd_false` (no `ErasureSpec.` prefix); `lake
exe hygiene --cites` checks that a cited *file* exists, not that a cited *declaration* name
does, so the battery does not catch it.

**Two binders this wave actually retired, and one it did not.** `hnb : NoBodylessRefs Γ t` is
**deleted** (W8, `e625855`), not merely dead: `shipping_erase_correct_firstorder`'s proof never
spent it, so it is gone from the theorem's signature and from all eight rungs' applications of
it, and `Capstone.lean`'s own unused-binder scan reads `#[]`. The deleted docstring's vacuity
claim ("without it a run reaching a body-less declaration would satisfy the conclusion
vacuously") is not carried forward, because that non-vacuity was never the binder's — it belongs
to `hev`, which only G5 inhabits (`W3-refute.md`, R4). `hblk : TableBlocks lenv env tbl` is
**not** deleted, and should not be: it now has a real, if still dead-ended, consumer chain
(above), unlike `hnb`, whose proof-term scan found nothing at all.

### `Lower`'s non-determinism at a block member
`LowerEnv.defs`'s second disjunct (the η-wrapped arm F-ETA added) is redundant — it collapses
into the first through `Lower.fixEta_of_block`, so it strengthens nothing — but its *presence*
means `Lower.fixBody` and `Lower.fixEta` both relate the same specification body to two
different emitted terms, so `Lower` is now provably not a function:
`¬ ∀ Γ s t t', Lower Γ s t → Lower Γ s t' → t = t'` (`scratch/round7/W2-refute.md`, R3/R4).
Nothing in the tree assumes `Lower` functional, so this is a recorded cost of the F-ETA repair,
not a defect. Unchanged this round.

**lean4lean asks** (owner: the fork). The commission is `downstream-asks-round4.md` in the
sibling `lean4lean` checkout; `doc/upstream-asks.md` is this side's register. Items 2, 6, 9 and
10 are the four `UpstreamAsks` fields; item 3 is what criterion 21 waits on; item 4, the kind
transfer from `lenv` to `env.constants`, blocks `hfo` and `ErasesEnv.tabled`'s exclusion; and
`TrProj`, entirely unproven at the pin, still blocks `hcb` at G2–G8 — 10 of G7's 30 tabled
bodies carry an `Expr.proj`, all of them class projections, and `TrExprS` at a `.proj` routes
through it. Unchanged this round: the pin is the same commit and no lean4lean-facing proof was
touched.

**`hev` stays vacuous outside G5.** `Green.g5_seval` is the only constructed source-evaluation
witness in the tree; every other rung, G7/G8 included, binds `hev` rather than proving it —
`benchArith 0`'s 45 recursive calls each owe N20's per-branch obligation, against G5's 45-line,
three-`StepDefeq` cost for a single δ and ι. Unchanged this round.

**Shipping findings from `dev/fix`.** `doc/rework/03-DEV-FIX.md`'s "Applied edits" table is the
single index, now **twelve** shipping findings plus F-FUEL: the ten from the first merge —
F-PROP, F-ETA, F-ETA2, F-SPARSE, F-EQREC, F-QUOT, F-ACC, F-DEPTH, F-UNSAFEREC, F-KERNAME, merged
at `2036c853` and repaired at `doc/rework/10-MERGE-FIXES.md`'s M1–M8 — plus two more from this
wave's second merge, `1352ac3` (`341e2a9`/`b3db162`, F-DEPLCTX/F-ARITYLET): **F-DEPLCTX**
resets `ErasureContext.lctx` at `Erasure.visitMutual`'s two dependency re-entries, so a closed
compiler body is erased in the context `erase_constant_body` erases it at rather than under
whatever local context the caller's walk had open — the gate on `Motive6`'s content that W4
spends to rebuild `BridgeInv` at a member sub-run at all — and **F-ARITYLET** extends
`Erasure.arityResultSort` across `.letE`/`.mdata`, as `destArity` does, whose residue is now a
proved refutation of the converse rather than an argued one (W9's `arity_of_propositionalInd_false`,
§3). F-FUEL, verification-authored rather than a shipping finding, reproduces a pre-reroute
oracle verdict and is merged too. Two fixes reach `doc/coverage.md` as strict gains: F-QUOT/F-EQREC
make `NoBodylessRefs` true on Fannkuch, and F-ETA's η-expansion is what lets
`LBWfPeregrine.expandedFix` hold at G6, G7 and G8 (vacuously true at the other five).
**F-PRODUCT is the one item still not fixed, and not meant to be**: `auto_inline_typeclass_dispatch`
(`LeanToLambdaBox/Erasure.lean:85`, `:88-118`, `:896-903`), an unverified product feature that
rode in on the verification branch, off by default. Not a miscompile, no wave depends on it,
and the `.ast.inlinings` channel it drives is a class-**E** row in `doc/trust.md`.

### Carried into the next wave (`scratch/round7/W4-refute.md` §7)
1. Record the `Nat.casesOn` dependency above as a stated theorem (`g7Table.body? ``Nat.casesOn
   = none` at every rung that tables it) or as an `isCasesOnName` guard on `SpecContent.defns`,
   so a table regeneration cannot silently vacuate five rungs.
2. Stop landing leaves: rule (4) forbids a declaration that lost its last consumer, and a
   declaration that never had one is the same debt taken in advance — nothing below W5a/b/c
   should land until it has a reader.
3. If W5a/b/c does not land next, `regKeyed_of_run` and `BlockAdequate`'s two new fields should
   come back out together (cost without reach, above).
4. Fix the two stale citations (`ErasesEnv.lean:48`, `Erasability.lean:425`) and say in
   `Tools/Coverage.lean` that `nbTerm` is an existence check, not a content one.
5. `ErasureSpec.propositionalInd_of_arity` needs a producer or a consumer of its own; paired
   with `arity_of_propositionalInd_false` it is currently a two-sided statement about an
   interface nothing in the tree crosses.

## 5. Delivery
Branch `dev/verify`: 317 commits ahead of `main`, 65 ahead of the last-pushed
`origin/dev/verify` (`e7894de`), 17 of them this round (`341e2a9` F-DEPLCTX … `d16c1c2`
bookkeeping, on top of `15a4af7`, wave 3's status commit). `lake build` green at 174 jobs
(`scratch/round7/gate4/01-lake-build.out`); the only `sorry` warnings are lean4lean's sixteen
(§1), and two standing linter warnings predate this round and sit outside it —
`LeanToLambdaBox/Semantics/Substitution.lean:231` (`recData` should be a `theorem`) and
`LeanToLambdaBox/ColdStartShape.lean:439` (`simpa` where `simp` would do; line moved from `:380`
as this wave's units added declarations above it). Tree-wide, including the two `dev/fix`
merges' shipping fixes and their `test/fixes/` regression suite (`scripts/fixes.sh`, wired into
`.github/workflows/build.yml` as its own step, after the build and before the ledger).

`.github/workflows/build.yml` runs the whole battery on pushes to `main` and `dev/verify`, with
only `LICENSE` in `paths-ignore`. Every check in it is green at HEAD
(`scratch/round7/gate4/`, 23 commands, one run from a checkout at `92522f2` that found and fixed
two bookkeeping regressions before landing as `d16c1c2` — §4's "Carried into the next wave"
list is the substantive residue this round's own gate did not touch); `lake exe
hygiene --schedule` reports **0 inversions** (`8 deletion rows, 45 deleted files, 18 live
imports of them`, unmoved: no unit this wave deleted or scheduled a file). `lake exe hygiene
--dead` lands at exactly its **339**-declaration budget (`scratch/round7/gate4/16-hygiene-dead.out`,
raised from 321 by this round's own bookkeeping commit, `d16c1c2`): the 240 `doc/coverage.md`
accounts for (the tooling 107, the frozen benchmark sources 43, `LeanToLambdaBox/Optimize.lean`
71 and `LeanToLambdaBox/ErasesUniform.lean` 19), plus `test/Vacuity.lean`'s five regression
lemmas and the 94 declarations under the **twelve** `test/fixes/` shipping-fix regressions —
two more than wave 3's ten, `F-ARITYLET.lean` (11 declarations) and `F-DEPLCTX.lean` (7) —
none imported by the theorem it guards. The pin is lean4lean
`20ec229f1a8c6358f3b3852c4e27d2be523d1b87` — `lakefile.toml`, both fields of
`lake-manifest.json`, the first line of `test/lean4lean-sorries.expected` — unchanged this round,
and every measurement here was taken at it. Both consumers still pin `main` — peregrine-tool's
Lean test lakefile and the frontend benchmark's, in the sibling checkouts — resolved to
`42f8f51` and `f54d17d`, ancestors of this branch, so neither builds the verified eraser.

| # | Verdict | Reason |
|---|---|---|
| 3, 4, 10, 11, 12, 14, 15, 16, 17, 19 | PASS | — |
| 1, 2, 5, 6, 8 | PASS as amended | eleven `Erases` rules — ten congruences plus `box`, `ctor` the eleventh — with no `.case` and no `.fix`, and `ctor`'s argument list literally `[]`; one L4 pass, `optimize`, with `LBOptimize_correct` and three non-vacuity guards, `LBCompile` split away so the composition has no subject (A9); T5's naming half clean at eight premises, U3.1's target, not five; `FirstOrderInd` decides true on `Nat`, `Bool` and `FOFixture.Tree`, with `List` and `Prod` excluded on purpose (A6/A15) |
| 9 | PASS as renamed | `ErasureSpec.oracle_sound_of_run` — in the capstone's closure, discharged, not assumed |
| 13 | PARTIAL | `green_G7` and `green_G8` elaborate; four of the capstone's fourteen binders are checked terms at both — `hcfg`, `hwt`, `hsup`, `hwf` — and ten stand, with `hcb` among them from G2 on (`hnb` is gone entirely, W8, not merely discharged); G8 carries one binder the other seven do not, `hbody` (named `hargReach` before W7/U9), for its non-empty spine |
| 18, 20 | SPLIT | narration clean, comment fraction 29.0% tree-wide with 5 of 68 files under 20%; the exception list to the no-dead-code rule is **empty**, and `lake exe hygiene --dead` reports 339 declarations outside the closure (above) |
| 7 | FAIL — no subject | `Subsingleton` does not occur; the condition is `Erasable`, discharged by `Erases.sort_erasable`/`forallE_erasable` and by the oracle |
| 21 | FAIL, deliberate | `LeanToLambdaBox/CheckerAdequacy.lean:41` keeps `namespace Lean4Lean.TypeChecker` until upstream ask 3 lands |
| 22 | FAIL on the branch half | pin and CI pass; the verified eraser is on `dev/verify` and both consumers pin `main` |

## 6. How to re-measure

    lake build ; lake build VerifyBench ; lake exe coverage --check
    bash scripts/fixes.sh
    bash scripts/ledger.sh ; bash scripts/erases_correct.sh ; bash scripts/erasesLB.sh ; bash scripts/lean4lean-sorries.sh
    bash scripts/frozen.sh ; bash scripts/hygiene.sh --allow test/hygiene.allow
    lake exe hygiene --dup ; lake exe hygiene --schedule ; lake exe hygiene --tables ; lake exe hygiene --cites
    lake exe hygiene --anti-epicycle LeanToLambdaBox/Lower.lean ; lake exe hygiene --dead   # --dead is a budget of 339
    lake exe green-check --self-test ; lake exe green-check --all
    lake exe reify --check LeanToLambdaBox.Green …g1Table…g8Table ; lake exe reify --blocks LeanToLambdaBox.Green …g1Table…g8Table
    lake exe reify --prepared LeanToLambdaBox.Green LeanToLambdaBox.Green.spikeZero … arithClosed benchArith

`.github/workflows/build.yml` holds the argument lists in full. `--prepared` takes constant names, not table names, and `lake build VerifyBench` must
precede `coverage --check`, because the five corpus `.ast` files it measures are build artifacts.
