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

**`hbridge` is still a binder, byte-identical to wave 4's.** Round 7 wave 5 (`f65c86f..30b36d5`,
three commits: `f37009c`, `doc/rework/12-REPAIRS-W9.md`'s plan; `eece730`, W9-H; `30b36d5`,
W9-A) changed no statement the ladder reads — `git diff d16c1c2..HEAD -- LeanToLambdaBox/
Capstone.lean` is empty, the `Green.lean` diff touches one docstring and appends declarations,
and the capstone's binder list, the eight rung statements and the 33-name footprint are
byte-identical to wave 4's (`scratch/round7/W5-refute.md` §0, §4.1–4.2). `hbridge` is unchanged
in kind: `grep -rn "\bhbridge\b" LeanToLambdaBox/` is still 24 hits, `shipping_erase_correct_
firstorder`'s signature (`Capstone.lean:206-210`, unmoved) and all eight of `Green.lean`'s
rungs still take it — six at wave 4's line numbers (`:226`, `:379`, `:480`, `:601`, `:854`,
`:975`) and G7/G8 shifted by the new content this wave inserts ahead of them (`:1636`, `:1697`,
were `:1572`, `:1633`) — and `erasure_bridge_env`, the theorem `doc/rework/12-REPAIRS-W9.md`
§2.6 (W9-E) plans to give it that shape, is still stated nowhere (`grep -rn erasure_bridge_env
LeanToLambdaBox/` empty). `12-REPAIRS-W9.md` supersedes `doc/rework/09-REPAIRS-W7.md`/
`11-REPAIRS-W8.md` as the operative plan for what is left; `hargReach`/`hbody` are unchanged
from wave 4 (`hbody` at `Green.lean:1702-1704`, `g8_hargReach` at `:1592-1605`, both shifted the
same +64 lines). The `Tools/Coverage.lean` contradiction wave 4 recorded rather than fixed
(the `audited` list and the hardcoded G8 sentence stuck on `hargReach` while the table already
showed `hbody`) **is fixed this wave**: W9-H corrects `audited` and the ladder-table header
(`:276`, `:670`) and the hardcoded sentence (`:735`) to `hbody`, and the regenerated
`doc/coverage.md` now agrees with itself.

What actually moved: nothing on `hbridge`'s own composition. `bridgeEnv_of_regContent`
(`Capstone.lean:158-171`) is unchanged since wave 4 and still has **zero consumers anywhere in
the tree** (`grep -rn bridgeEnv_of_regContent LeanToLambdaBox/ test/`: the declaration and the
ledger row, nothing else); `regKeyed_of_run` (W6) likewise still has zero consumers; no theorem
produces `RegAcc` at a run. `12-REPAIRS-W9.md` renamed wave 4's re-planned W5a/W5b/W5c to
W9-B/W9-C/W9-D (plus W9-E for W7's `erasure_bridge_env`) and staged two smaller units, W9-H and
W9-A, ahead of them to close two of wave 4's own carried-forward items first (§4's "Carried
into the next wave", items 1 and, in substance, the realizer-exit question §1.1 of
`12-REPAIRS-W9.md` decided). Both landed. `noTabledCasesOnBodies` (W9-H, `Green.lean:1405-
1408`) *measures* rather than guards the tabled-`casesOn` dependency: four `decide +kernel`
conjuncts at `g5Table..g8Table`. `no_realizer_exit_compiler` (W9-A, `VisitExprRefines/
Step/Env.lean:461`) *excludes* F-QUOT's and F-EQREC's two body-less→bodied realizer exits from
the fragment by name, at the cost of one new decidable table property (`TableRecPrefixed`) and
one new class-**D** bundle (`SchemeNames`, two fields; §4 below). **Neither reaches a rung or
the binder**: both sit in components with zero consumers of their own (§4).

W9-B — the unit that would give `RegAcc` a producer at a run, and so give
`bridgeEnv_of_regContent` its first consumer — was attempted and **returned blocked**:
`regInv_registerInd_run` as `12-REPAIRS-W9.md` §2.3 prints it is not provable from its stated
premises. The conclusion's `RegInvShape'.keys` (`(s₁.gdecls.map Prod.fst).Nodup`) needs a state
invariant, `IndBlocksCover`, that nothing in the tree supplies, and mechanised counterexample
states admit the guard's premises while violating the conclusion (`w9b_probe1.lean`,
`m1_guard_blind`); two further run facts the unit needs are absent (`F-B-2`, `F-B-3`); and three
specification-side obligations of `IndPrefixOf.content` need exclusions §2.3 names only one of
(`F-B-6`, `F-B-7`) — `scratch/round7/W9-B-report.md` §2, F-B-1 through F-B-7. Following rule (2)
and the standing prohibition on landing a consumer-less declaration, **nothing was committed**:
every declaration W9-B would have landed exists only to feed `regInv_registerInd_run`, and
landing it without that theorem would leave two more consumer-less roots beside the ones
already standing. The report proposes a five-unit decomposition, B-i through B-v, in dependency
order (§4 below); none is landed. Apart from the one path that already reached a rung before
this wave (`Green.g8_t0 → Green.g8_hargReach → Green.green_G8`, W7/U9), this wave's own landed
declarations sit in **three** further components whose roots have zero consumers, beside the
**seven** `scratch/round7/W4-refute.md` §4 already found (§4).

| Class | Binders |
|---|---|
| proved, or per rung a checked term | inside the theorem: the erasure half `erasure_bridge_of_run`, supplying all eighteen bridge steps; the answer's shape and uniqueness from `firstorder_erases_core`, and `NoBox tv` at the *lowered* value from `noBox_lower_of_foSpine`; the simulation, `erases_correct` applied once at the spine with `ErasesEnv.mkApps`; the observable's transport across the preparation passes from `prepare_sound`. At every rung: `hcfg : ConfigPinned`, `hsup : Supported`, `hwf : LBWfPeregrine` by `lbWfPeregrine_of_check (by decide +kernel)`, `hwt : TrExprS`, the target-side `WcbvEval`; `hcb : CompilerBodies` at G1 only; `hev : SEval` at G5 only. `hnb : NoBodylessRefs` is gone (W8, `e625855`): the proof never spent it, so it is deleted from the theorem and from all eight rungs' applications rather than carried as an unread premise — the theorem's own unused-binder scan is `#[]`. Since round 7 wave 5 (W9-H, W9-A), beside `noCasesOnKeys`: `noTabledCasesOnBodies` (four rungs, `g5Table..g8Table`, `decide +kernel`) measures the tabled-`casesOn` dependency rather than guarding it, and `tableRecPrefixed_rungs` (all eight, `decide +kernel`) is **vacuous** at every one — no tabled name at any rung carries a recursor suffix. `no_realizer_exit`/`no_realizer_exit_compiler` are proved theorems excluding F-QUOT's/F-EQREC's two realizer exits from the fragment by name. None of these four is read by anything reaching a rung (§4) |
| **C** — this repository's own code | `E : EraserAsks` — four fields, unchanged since W5: `passes_monotone`, `passes_sound`, `oracle_false_refl`, `kernel_ind_head_true` (residue: a *reduced* telescope longer than `isArityCheck`'s constant budget, and any other kernel error inside it). `block_keys_distinct` is deleted, F-UNSAFEREC's guard making distinctness a *conclusion* of a successful run (`run_rec_exit_reg`'s fifth conjunct) rather than a bundle field — though nothing today spends that conclusion: both call sites of `run_rec_exit_reg` discard it, and `run_rec_exit_nodup` and its would-be consumer `blockKeyed_install` each have no consumer of their own (§4). `hbridge`'s two fields — `erasesEnv` and `lowerEnv` — open, §4. `hbody` (named `hargReach` before W7/U9), at G8 alone — open, §4; reduced to a source-side statement quantified over every `Γspec`, strengthened but satisfiable (§4) |
| **D** — specifications of Lean's `Meta`/`Core` primitives | `P : ∀ Us, ErasureSpec lenv env Us gw` — seven fields, unchanged: `env_connect`, `lookup_adequate`, `fresh_names`, `oracle_refl`, `decl_adequate`, `prim_monotone`, `block_adequate`; taken at every level scope since U5, which is what a sub-run below `Erasure.visitMutual`'s `withReader` needs. **`prim_monotone : PrimMonotone gw` is per-primitive**, not a blanket `MetaM` claim: eight clauses, one per named primitive (`getEnv`, `logInfo`, `isInstance`, `inferType`, `isProof`, `forallBoundedTelescope`, `lambdaBoundedTelescope`, `liftMetaM`), with the two bounded telescopes and `isProof` stated *compositionally* so the two anonymous continuations F-ACC/F-SPARSE introduced are covered by the derived `PrimGenMono` predicate rather than by a further universal (`ErasureSpec.lean:259-306`; C1, `8bdffca`, closing a finding raised against an earlier single unconditional `PrimMonotone.metaM` field, `scratch/round7/W2-refute.md` §5/R7). **`block_adequate : BlockAdequate lenv env` grew two fields this wave**, `selfName` and `fields` (W6, `ErasureSpec.lean:413-422`), each a property of `Lean.Environment.find?` alone — `fwd`'s fourth premise and the member loop's `.inductInfo` match had no producer at a registration without them (six fields → eight; `ErasureSpec`'s own top-level count stays seven, `block_adequate` being one field of it). `htbl : SourceTableAdequate`, `hsafe : TableSafe`, `hblk : TableBlocks`, `hprep` (the prepared term is the subject), `hrun` (the run produced the committed program). Since round 7 wave 5 (W9-A), `SchemeNames lenv` — two more fields, both properties of `Lean.Environment.find?` alone (`quot`: a `.quotInfo` name is in `quotPrimNames`; `recr`: a `.recInfo` name carries `Supported.recSuffix`), taken beside `P` rather than inside it since neither mentions a level scope, and landed in `Supported.lean` rather than `ErasureSpec.lean` to avoid an import cycle (`Supported.lean` imports `ErasureSpec.lean`). Nothing in the tree constructs one, and its only readers, `no_realizer_exit`/`no_realizer_exit_compiler`, have zero consumers of their own (§4) |
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
`doc/coverage.md` is generated by `lake exe coverage` from the tree; `lake exe coverage --check` is green at HEAD (`scratch/round7/W5-status.coverage-check.out`), after two more bookkeeping regenerations this round: `eece730` (W9-H) moves the whole-environment kername count 230,472→230,476 as its own new declarations enter it, and retires the stale `hargReach`/`hbody` table-header and prose (§1); `30b36d5` (W9-A) moves it again, 230,476→230,498, as `recSuffix`, `SchemeNames`, `TableRecPrefixed` and the two `no_realizer_exit` theorems enter it. `d16c1c2` (wave 4) is the regeneration before that, 230,402→230,472. The realizer census column (`Tools/Coverage.lean:209`, which reads `Supported.isRecursorName`) is **0 at every rung both before and after the widening** (`scratch/round7/w9a_measure.out`), so the correction changes no table row. Arith is in
the fragment and is the subject of rungs G7 and G8. Sieve and
BinaryTrees are out at `recursorHead` on `Eq.rec` through `Bool.noConfusion` (F-EQREC); Quicksort at F-EQREC, the well-founded
`Nat.div.go`/`Nat.modCore.go` route and `sparseCasesOn`, with a wrong emitted program besides (F-SPARSE); Fannkuch at F-EQREC and `etaContractedMinor`
on `Decidable.casesOn`. Fannkuch's `NoBodylessRefs` failure — the one the capstone's own premise used to name, its reachable `Eq.rec` declared
body-less — is **closed**: `recursorRealizer` now gives that `Eq.rec` a `.case` body (F-QUOT's and F-EQREC's registering exit, §2.8 of
`doc/rework/10-MERGE-FIXES.md`), a strict gain measured in `doc/coverage.md`'s realizer census, so all five corpus programs and all eight rungs now
satisfy it; Fannkuch stays outside the fragment for the two reasons above alone.

The `rec_*` widening (W9-A, §4) has one measured cost outside the ladder. Of this toolchain's
3342 `.recInfo` constants every one now carries a `recSuffix`, but the wider test also catches
**18** non-`.recInfo` constants under the same suffix class, **13** of them under a genuine
inductive prefix — `Nat.rec_eq_recCompiled`, `Bool.rec_eq`, `Acc.rec_eq_recC`,
`List.Perm.rec_heq`, and eight `Lean4Lean`-internal theorems
(`scratch/round7/W5-refute.md` §4.4). `Nat` and `Bool` are tabled inductives at the rungs, so
`Supported.isRecursorName` now answers `true` at those thirteen names for any table that tables
them — a coverage cost, `SupportError.recursorHead` rather than acceptance, at a plain theorem
that merely happens to be named like a recursor. All thirteen are theorems, unreachable from a
computational body, so no rung moved; `recSuffix`'s own docstring census (3342/125/0,
`Supported.lean:185-193`) reports only the `.recInfo` side of the widening, not this one.

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

### `hbridge` — the composition is unchanged this wave; W9-B's attempt, and why it did not close
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
supplies it. `doc/rework/12-REPAIRS-W9.md` renamed the three wave-4 re-planned pieces
W5a/W5b/W5c to **W9-B** (the `register_inductive` prefix producer), **W9-C** (the block exit —
the two `recursorRealizer` realizer sites are gone with W9-A's exclusion, below; the two
non-recursive/body-less constant exits are still `RegAcc`-typed `regInv_addAxiom_step`/
`regInv_constCons_step`, landed at wave 4's W5) and **W9-D** (the accumulator conjunct,
restaged as its own second bundle of eighteen motives, `AccGrows`, proved by a second instance
of `Erasure.visitExpr.mutual_fixpoint_induct` that reads the first bundle's conclusion as a
hypothesis at one step only — a correction of wave 4's plan, not what it describes: `RunRefines`,
`RunRefinesAlt`, `HeadRefines` and all eighteen existing step lemmas stay untouched under the
new plan, where wave 4 had planned an independent fifth conjunct of `RunRefines` itself), plus
**W9-E** for W7's `erasure_bridge_env`.

**W9-B was attempted this wave and returned blocked** (`scratch/round7/W9-B-report.md`; no
tracked file changed, no commit made). `regInv_registerInd_run` as `12-REPAIRS-W9.md` §2.3
printed it is not provable from its stated premises, and the gap is not a proof-technique one —
seven findings, F-B-1 through F-B-7. The conclusion's `RegInvShape'.keys`
(`(s₁.gdecls.map Prod.fst).Nodup`) needs a state invariant, `IndBlocksCover`, that nothing in
the tree supplies: `Erasure.checkIndKernameFresh` is blind to `s.gdecls`, so a mechanised
counterexample state (`w9b_probe1.lean`, `sBlind`) satisfies every stated premise while
violating the conclusion (F-B-1); that invariant's own `reg` case needs a run fact the tree
proves only at the block's head member, not at every member (F-B-2); `hnewc` needs
`s₁.constants = s.constants` at `ConfigPinned`, which no theorem records (F-B-3); the
`IndBodyOf` bridge `IndCovered.block` demands is short of a list-length fact
`run_register_inductive_cold_entries` does not expose, though the fact sits inside that
theorem's own proof and only needs threading out (F-B-4); `hfresh`'s eliminator half — that
`Γ` does not already declare a member's `casesOn` key — is not in §2.3's payment table at all
(F-B-5); and `IndPrefixOf.content`'s `axioms`/`blocks` and `keys` clauses are *env-ranged*
where the plan's `BlockKeysFresh` is table-ranged, so F-KERNAME's non-injective `toKername`
leaves two exclusions unpaid — saved at the rungs only by `cleanIdent`'s identity on a
`_`-free root string, a lemma not in the tree (F-B-6, F-B-7). Four payments of §2.3's table do
close as printed (`w9b_probe1.lean` §P: `mutualBlockKn iv = indBlockKername iv.all` by `rfl`;
the eliminator body's `constRefs`/closedness/freshness; `IndFlagSound` from
`ErasureSpec.propositionalInd_of_arity`'s sound half, its first consumer had the unit landed),
and the block-key exclusion is restatable, table-ranged and restricted to *bodied* tabled names
(`BodiedKeysFresh`, F-W9-1) — at the cost of leaving the eliminator conjunct undischarged, since
the redundancy argument needs F-B-7's missing converse: `Green.noTabledCasesOnBodies` would
**still** have had no consumer after a landed W9-B, contrary to §2.1's own *Consumers* line.
Following rule (2) and the standing prohibition on landing a consumer-less declaration,
**nothing was committed**: every declaration W9-B would have landed exists only to feed
`regInv_registerInd_run`. The report proposes a five-unit decomposition in dependency order —
**B-i** (three run lemmas closing F-B-1's block-shaped gap and F-B-3/F-B-4), **B-ii**
(`IndBlocksCover` and its two derived freshness lemmas), **B-iii** (the F-KERNAME layer
F-B-6/F-B-7 need), **B-iv** (`BodiedKeysFresh`/`IndPrefixOf` restated on the specification
side), **B-v** (`regInv_registerInd_run` proper, now also taking `RegKeyed env s`,
`CanonicalConstants s`, `IndBlocksCover s` and a `TableSafe`-style safety column beyond §2.3's
stated premises) — none of which is landed. Separately, `hde` itself is refuted at a block
member's sub-run (`erasuresDeclared_false_at_app`, `scratch/round7/q_w8.lean`) and its narrower
repair (F-W8-7, restricting `hde` to the `t₀` that actually lowers to `t`) is stated but not
landed (`scratch/round7/W7-report.md`). The α gap (`ReifiedDecl.Prepared` pins a tabled body
only up to `Expr.AlphaEq`, and `lake exe reify --check` reports five of G7/G8's bodies matching
only up to binder names) and the ∀-`Γspec` shape mismatch `RunRefines` still reads are
untouched.

**The tabled-`casesOn` dependency — measured this wave, not guarded (W9-H).**
`SpecContent.defns` carries no `isCasesOnName` guard where `SpecContent.axioms` does, so a
tabled `casesOn` with a compiler body would make `RegContent`'s content clause
self-contradictory through `ErasesEnv.runtimeKey_isCasesOn`/`erases_ne_elimBody` — the route
that made wave 3's attack on `hsub` look reachable through a body in the first place, and
confirmed this wave as the load-bearing branch: `SpecContent.runtimeKey_isCasesOn`
(`VisitExprRefines/Step/Env.lean:911`) opens `by_cases hb : ∃ b, bo c = some b` and refutes the
positive branch *through* the unguarded `defns` clause; a guard deletes that branch's only
argument, so wave 4's own carried-forward alternative — add the guard — would have been the
wrong repair (`12-REPAIRS-W9.md` §1.2, `scratch/round7/W5-refute.md` §4.7). W9-H lands
`Green.noTabledCasesOnBodies` (`Green.lean:1394-1408`), a four-conjunct `decide +kernel` at
`g5Table..g8Table`: at G5–G8 the only tabled `casesOn` name is `Nat.casesOn`, and its `body?`
is `none` at every one — the table carries the *declaration*, not a compiler body.

**The measurement's coverage is narrower than the dependency it guards, and G1–G4 are safe for
a different, unrecorded reason** (`scratch/round7/W5-refute.md`, F-G-1). Every rung's answer is
a peano numeral, so every rung's `Γspec` declares `Nat`'s block, and `SpecContent.blocks` forces
an `ElimDecl` at `Nat.casesOn` through `IndCovered.elims` at **all eight** rungs, not only the
four `noTabledCasesOnBodies` is stated at. At G1–G4 `Nat.casesOn` is not tabled at all
(`(g<i>Table.decl? ``Nat.casesOn).isSome = false`) — a weaker, different fact from "tabled
without a body," and nothing in the tree states it, so a table regeneration that pulled
`Nat.casesOn` into, say, G2 with a body would make `green_G2` vacuous and trip no check. A
second gap is unmeasured (F-G-2): the dependency's actual trigger is
`ErasesEnv.runtimeKey_isCasesOn`'s `bo c = some b` branch at a `c` whose *kername* is a declared
eliminator key, not `isCasesOnName c = true` — so a tabled bodied `c` with `isCasesOnName c =
false` whose `toKername c` collides with an eliminator key sits outside
`NoTabledCasesOnBody`'s quantifier and would still break a rung; measured clean at all eight
today (the colliding set is `[]` everywhere) but excluded by nothing general. `Green.
g7_natCasesOn_tabled` keeps its role as the non-vacuity witness that the measurement has a
subject, with a sentence added this wave distinguishing "tabled" (its own claim) from "tabled
without a body" (what the rungs' consistency actually needs).

### The two realizer exits — closed by exclusion, and zero consumers (W9-A)
`Erasure.visitMutual`'s body-less arm dispatches on the looked-up `ConstantInfo` before falling
through to `Erasure.addAxiom`: a `.quotInfo` takes `Erasure.quotRealizer` and a `.recInfo`
takes `Erasure.recursorRealizer`, and both emit a **bodied** entry at a name the model holds
body-less, so no specification clause can read either body — MetaRocq's `erases_constant_body`
(`../metarocq/erasure/theories/Extract.v:264`) relates an emitted body only to the source body
it erased. `12-REPAIRS-W9.md` §1.1 declines the alternative wave 4's successor plan proposed
(admitting the two exits as `ElimDecl`-shaped specification entries) as the wrong half of the
analogy — an eliminator key is *consumed* by `Lower`, a realizer key is *emitted*, and admitting
the latter as a `RuntimeKey` breaks `Lower.const` exactly where it is accepted — and instead
shows the fragment never reaches either exit. `no_realizer_exit_compiler`
(`VisitExprRefines/Step/Env.lean:461`) proves it, at the cost of one new decidable table
property, `TableRecPrefixed` (the gap between N21's `isRecursorName tbl c = false`, which
carries a table lookup, and "`c` is no recursor," which the bare-name test `SchemeNames.recr`
answers), and one new class-**D** bundle, `SchemeNames` (§1). A side effect: `Erasure.
recursorRealizer`'s own `Erasure.register_inductive` call (`Erasure.lean:436`) is unreachable
too, so W9-D's accumulator only owes registration growth at `visitConstructor`/`visitProj`/
`visitCases` (steps 3, 10, 17), not at a fourth site inside `visitMutual`.

`Supported.recSuffix`, factored out of `isRecursorName` and widened from a five-string set to
`rec_*`, is a genuine correction rather than a refactor: 125 of this toolchain's 3342 `.recInfo`
constants are the auxiliary recursors `I.rec_k` of nested and mutual inductives (e.g. `Lean.
Syntax.rec_2`), which the five-string test missed, so before the widening a run at such a head
reached the `.recInfo` exit instead of being excluded by N21. The widening's own coverage cost
is §3's finding.

Four further attacks this wave find no `False` and are recorded, not fixed, since they confirm
rather than break something (`scratch/round7/W5-refute.md` §1): `IndPrefixOf.content`'s
block-key and cross-block-key collisions are clean at all eight rungs though unexcluded in
general (F-G-3, sharing F-B-6's root); an `ElimDecl` key is a `RuntimeKey` (`Lower.lean:108`)
that `LowerEnv.defsTotal` (`ErasesEnv.lean:296`) excepts, so `Green.noCasesOnKeys` and
`IndCovered.elims` are about opposite sides of the pruning and cannot collide (F-G-4);
`no_realizer_exit`'s `us = []` restriction is the established idiom `visitConst_refines`
(`Step/Env.lean:973`) already reduces to, not a coverage loss (F-G-5); and `no_realizer_exit_
compiler`'s `compilerInfo?` is checked against the exact lookup `Erasure.visitMutual` makes
(`Erasure.lean:1226`, `:1240`, `:1243`) (F-G-6).

One stale citation this wave's own citation-fixing commit introduced: `Green.lean:1410` cites
`SpecContent.runtimeKey_isCasesOn` at `VisitExprRefines/Step/Env.lean:821`; the declaration is
at `:911` (`:821` is an unrelated `obtain` inside a different proof). `lake exe hygiene --cites`
checks file paths, not line numbers or declaration names, so the battery does not catch it — the
same blind spot wave 4 reported and W9-H fixed two instances of (`scratch/round7/W5-refute.md`
§4.6).

### `hbody`'s residue (was `hargReach`, W7/U9) — strengthened, satisfiable, not refutable
`Green.g8_hargReach` (`Green.lean:1592-1605`) reduces the binder further than U9 left it: `Lower
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
landed or restated through wave 4, exactly **one** is read by anything that reaches a rung
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
  `regKeyed_recConstState` (W6); all eight `g<i>_noBodylessRefs` (W8, see below). None of these
  seven gained a trunk this wave — measured name for name against `d16c1c2` and again at HEAD,
  every one is still at **0** consumers (`scratch/round7/W5-refute.md` §3.2).

**Wave 5 adds three more roots.** `no_realizer_exit_compiler` and everything that exists only
to feed it — `no_realizer_exit`, `supported_const_names`, and `TableRecPrefixed`/`SchemeNames`
through it — dead-end at the root: `no_realizer_exit_compiler`'s own intended reader, W9-D's
`StepAcc6`, has not landed (`recSuffix`'s *other* consumer, `Supported.isRecursorName`, is real
and pre-existing; the *new* chain `TableRecPrefixed`/`SchemeNames → no_realizer_exit →
no_realizer_exit_compiler` is not). `Green.tableRecPrefixed_rungs`, the eight-rung measurement
beside it, is a second root — **vacuous** at every rung by its own docstring, unlike
`noTabledCasesOnBodies`, which has a subject at G7 (`g7_natCasesOn_tabled`). `Green.
noTabledCasesOnBodies` itself is a third: its intended reader is W9-B's prefix, which did not
land, so it too has no consumer today. A wider consumer scan this wave also finds **five**
declarations below the wave-4 roots above that `W4-refute.md` §4.1 missed —
`ConstsDeclared.specGrow`, `RefsStable.trans`, `SpecGrow.refl`, `SpecGrow.trans`,
`RegContent.stateCongr`, all plumbing below the dead `bridgeEnv_of_regContent`/W2-transport
roots — bringing the zero-consumer surface added since `d61db80` to **32** declarations; with
the eight `g<i>_noBodylessRefs` `hnb`'s deletion (W8) already orphaned, the round-7 dead
surface totals **40** (`scratch/round7/W5-refute.md` §3.1).

**`07-STATUS.md`'s own carried-forward item — "stop landing leaves" — was honoured by W9-B,
which found its route blocked and committed nothing, and violated by W9-A and W9-H, which
landed three more leaves anyway** (`scratch/round7/W5-refute.md` §3.2). The measured facts they
land are individually true and cheaply checked (§1), but by the same standard the
`regKeyed_of_run` paragraph below states of wave 4's own W6, a declaration added to close a
step and read by nothing is not distinguishable, from inside the tree, from a hypothesis.

Two of wave 4's own "landed / kept" claims are true only one link deeper than before, not
resolved (unmoved this round): `hblk : TableBlocks` (kept at W8, since W4 already gave `blockKeyed_install` a
consumer, `visitMutual_block_mode → visitMutual_member_erases_block`) is a real, three-link
chain now rather than the two-link dead end wave 3 measured — but its *top*,
`visitMutual_member_erases_block`, still has zero consumers of its own, and
`erasure_bridge_of_run`'s own unused-binder scan is still `#[hblk]`: the binder is spent only at
a separate proof term's own copy, never at the one the capstone calls. Likewise
`SourceTableAdequate.compilerLevels` (kept at W8): `compilerLevels → compilerLevels?_eq →
visitMutual_member_erases`/`_block`, chain length 2 → 4, both tops still zero-consumer.
`W3-refute.md` R3a's "a repaired clause nothing reads is a hypothesis the ladder pays for and
never spends" therefore still holds of both; only the chain length moved.

**Cost without reach.** `regKeyed_of_run` is the one theorem wave 4 (W6) proved about a run of
the shipping eraser, and it cost two new class-**D** fields on `BlockAdequate` (§1) that every
rung now carries through `P` — and it has no consumer. The fields are individually consistent
(`Lean.Environment.find?` properties, §1), but by W9's own standard ("nothing in the tree
constructs an `ErasureSpec`, so a field added to make a theorem go through is not
distinguishable, from inside the tree, from assuming the theorem") the pair is a debt taken in
advance of a reader that does not yet exist. The same pattern repeats this wave, smaller:
`SchemeNames`'s two fields (§1, W9-A) are individually consistent too — measured true at
230,479 constants, and F-G-6 (above) confirms neither is refutable inside the tree — but
nothing constructs a `SchemeNames` either, and its only readers dead-end at
`no_realizer_exit_compiler` (above). Not yet taken by any rung: `12-REPAIRS-W9.md` §2.5's
`visitExpr_regInv_all` is where a `hS : SchemeNames lenv` field would first enter a rung's
hypothesis list, and that theorem is not landed.

**Two smaller findings from wave 4's audit, both closed this wave (W9-H).** The eight
`Green.g<i>_noBodylessRefs` lost their last reader when W8 deleted `hnb` (below): `Tools/
Coverage.lean`'s `nbTerm` column reads only whether the *declaration exists* (`env.find?`),
never what it says, so `doc/coverage.md`'s per-rung `NoBodylessRefs` column is an existence
census, not a content check — `Tools/Coverage.lean:717`'s generator prose now says so, and the
regenerated `doc/coverage.md` carries the sentence. The two docstrings that cited a theorem
under the wrong qualified name (`ErasesEnv.lean:48`, `Erasability.lean:425`:
`ErasureSpec.arity_of_propositionalInd_false` where the declaration is `LeanToLambdaBox.
arity_of_propositionalInd_false`, no `ErasureSpec.` prefix) are corrected. `lake exe hygiene
--cites` still checks only that a cited *file* exists, not a cited *declaration* or *line* —
the same blind spot that let one new stale citation (`Green.lean:1410`, above) land in the very
commit that fixed the old ones.

**Two binders wave 4 actually retired, and one it did not (unmoved this round).**
`hnb : NoBodylessRefs Γ t` is
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
at `2036c853` and repaired at `doc/rework/10-MERGE-FIXES.md`'s M1–M8 — plus two more from wave
4's second merge, `1352ac3` (`341e2a9`/`b3db162`, F-DEPLCTX/F-ARITYLET): **F-DEPLCTX**
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

### Carried into the next wave (`scratch/round7/W5-refute.md` §6, superseding wave 4's list)
Wave 4's items 1 and 4 are done (measured, W9-H; fixed, W9-H). What replaces and survives them:

1. Widen `noTabledCasesOnBodies` to all eight rungs (F-G-1). It is true at G1–G4 by a
   `decide +kernel` the wave-5 audit already ran; the four extra conjuncts cost nothing and make
   the tripwire cover the rungs the dependency actually reaches, rather than only the four whose
   table tables `Nat.casesOn` at all.
2. Add the eliminator-key and block-key collision censuses (F-G-2, F-G-3): both decidable per
   table, both clean at all eight rungs today, neither in the tree — the rung-side half of
   F-B-6/F-B-7, which W9-B's proposed B-iii/B-iv would need in general anyway.
3. Fix `Green.lean:1410` (`SpecContent.runtimeKey_isCasesOn` is at `Step/Env.lean:911`, not
   `:821`, above) and record the `rec_*` widening's inhabited false-exclusion class in
   `recSuffix`'s docstring — 18 newly caught non-recursors, 13 under real inductive prefixes
   including `Nat` and `Bool` (§3).
4. Stop landing leaves: rule (4) forbids a declaration that lost its last consumer, and a
   declaration that never had one is the same debt taken in advance. This was honoured by W9-B
   (which found its route blocked and landed nothing) and violated by W9-A and W9-H (which
   landed three more) — nothing below W9-B's own five-unit decomposition (B-i…B-v) should land
   until it has a reader, and the **40**-declaration zero-consumer surface (above) is now the
   wave's standing headline, not a one-off.
5. If W9-B's decomposition does not close next, `regKeyed_of_run` and `BlockAdequate`'s two W6
   fields — and now `SchemeNames`'s two W9-A fields — should come back out together (cost
   without reach, above); this is wave 4's item 3, due a second wave running.
6. `ErasureSpec.propositionalInd_of_arity` still needs a landed consumer; W9-B's P4 (above)
   would be its first were B-v to land, but B-v is not landed.

## 5. Delivery
Branch `dev/verify`: 321 commits ahead of `main`, 69 ahead of the last-pushed
`origin/dev/verify` (`e7894de`), 3 of them this round (`f37009c` `12-REPAIRS-W9.md`'s plan,
`eece730` W9-H, `30b36d5` W9-A — W9-B was attempted and landed nothing, above — on top of
`f65c86f`, wave 4's status commit). `lake build` green at 174 jobs
(`scratch/round7/W5-status.build.out`); the only `sorry` warnings are lean4lean's sixteen (§1),
and two standing linter warnings predate this round and are unmoved by it —
`LeanToLambdaBox/Semantics/Substitution.lean:231` (`recData` should be a `theorem`) and
`LeanToLambdaBox/ColdStartShape.lean:439` (`simpa` where `simp` would do). Tree-wide, including
the two `dev/fix` merges' shipping fixes and their `test/fixes/` regression suite
(`scripts/fixes.sh`, wired into `.github/workflows/build.yml` as its own step, after the build
and before the ledger).

`.github/workflows/build.yml` runs the whole battery on pushes to `main` and `dev/verify`, with
only `LICENSE` in `paths-ignore`. Every check in it is green at HEAD, re-run for this document
from a clean tracked tree at `30b36d5` (`scratch/round7/W5-status.*.out`); a companion
read-only audit the same session (`scratch/round7/W5-refute.md`) found the same — no `False`
derivable from any rung or the capstone, no bookkeeping regression, nothing to fix — so §4's
"Carried into the next wave" list is this round's entire substantive residue. `lake exe
hygiene --schedule` reports **0 inversions** (`8 deletion rows, 45 deleted files, 18 live
imports of them`, unmoved: no unit this wave deleted or scheduled a file). `lake exe hygiene
--dead` lands at exactly its **339**-declaration budget (`scratch/round7/W5-status.dead.out`,
**unraised this round**: wave 5's nine new declarations all fall inside the `Green.lean`/
`Supported.lean`/`VisitExprRefines/Step/Env.lean` closure the budget already covers, so the
zero-consumer additions §4 measures do not move this figure — `hygiene --dead` operates at
file/import granularity, not the proof-term consumer scan the disconnection census performs):
the 240 `doc/coverage.md` accounts for (the tooling 107, the frozen benchmark sources 43,
`LeanToLambdaBox/Optimize.lean` 71 and `LeanToLambdaBox/ErasesUniform.lean` 19), plus
`test/Vacuity.lean`'s five regression lemmas and the 94 declarations under the **twelve**
`test/fixes/` shipping-fix regressions, none imported by the theorem it guards. The pin is
lean4lean `20ec229f1a8c6358f3b3852c4e27d2be523d1b87` — `lakefile.toml`, both fields of
`lake-manifest.json`, the first line of `test/lean4lean-sorries.expected` — unchanged this
round, and every measurement here was taken at it. Both consumers still pin `main` —
peregrine-tool's Lean test lakefile and the frontend benchmark's, in the sibling checkouts —
resolved to `42f8f51` and `f54d17d`, ancestors of this branch, so neither builds the verified
eraser.

| # | Verdict | Reason |
|---|---|---|
| 3, 4, 10, 11, 12, 14, 15, 16, 17, 19 | PASS | — |
| 1, 2, 5, 6, 8 | PASS as amended | eleven `Erases` rules — ten congruences plus `box`, `ctor` the eleventh — with no `.case` and no `.fix`, and `ctor`'s argument list literally `[]`; one L4 pass, `optimize`, with `LBOptimize_correct` and three non-vacuity guards, `LBCompile` split away so the composition has no subject (A9); T5's naming half clean at eight premises, U3.1's target, not five; `FirstOrderInd` decides true on `Nat`, `Bool` and `FOFixture.Tree`, with `List` and `Prod` excluded on purpose (A6/A15) |
| 9 | PASS as renamed | `ErasureSpec.oracle_sound_of_run` — in the capstone's closure, discharged, not assumed |
| 13 | PARTIAL | `green_G7` and `green_G8` elaborate; four of the capstone's fourteen binders are checked terms at both — `hcfg`, `hwt`, `hsup`, `hwf` — and ten stand, with `hcb` among them from G2 on (`hnb` is gone entirely, W8, not merely discharged); G8 carries one binder the other seven do not, `hbody` (named `hargReach` before W7/U9), for its non-empty spine |
| 18, 20 | SPLIT | narration clean, comment fraction 29.1% tree-wide with 5 of 68 files under 20%; the exception list to the no-dead-code rule is **empty**, and `lake exe hygiene --dead` reports 339 declarations outside the closure (above) |
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
