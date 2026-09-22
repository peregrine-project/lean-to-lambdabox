# 07 — Status

## 1. The theorem
`LeanToLambdaBox.shipping_erase_correct_firstorder` (`LeanToLambdaBox/Capstone.lean:185-229`).
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

**`hbridge` and `hargReach` are still binders — U9 did not discharge either.**
`doc/rework/09-REPAIRS-W7.md` §2.9 planned a theorem `erasure_bridge_env` that would give
`hbridge` "the shape of `hbridge` exactly … by `bridgeEnv_of_regInv` at U7's output and U8's
saturation", after which "`hbridge` then leaves `shipping_erase_correct_firstorder` and all eight
rungs, and `hargReach` at G8 falls out of `Green.g8_argErasesEnv`". None of that landed:
`erasure_bridge_env` is not stated anywhere in the tree, `grep -rn "hbridge" LeanToLambdaBox/` is
non-empty, `shipping_erase_correct_firstorder`'s own signature (`Capstone.lean:205-209`) still
takes `hbridge` as a binder, and `Green.green_G8` (`Green.lean:1586`) still takes `hargReach`.
What U9 (`6439576`) actually landed is `bridgeEnv_of_regContent` (`Capstone.lean:153-169`), a
*standalone* theorem — not on `shipping_erase_correct_firstorder`'s proof path, which reaches its
conclusion through `erasure_bridge_of_run` plus the binder `hbridge` unchanged — that composes
`hbridge`'s whole *payload* out of four named antecedents about the run's final state, one of
which (`hdeps`) is now proved rather than assumed. §4 gives the antecedents and the round-7 audit
that found them jointly unsatisfiable at the rungs' actual final states, so the route does not in
fact reduce either binder's cost today.

| Class | Binders |
|---|---|
| proved, or per rung a checked term | inside the theorem: the erasure half `erasure_bridge_of_run`, supplying all eighteen bridge steps; the answer's shape and uniqueness from `firstorder_erases_core`, and `NoBox tv` at the *lowered* value from `noBox_lower_of_foSpine`; the simulation, `erases_correct` applied once at the spine with `ErasesEnv.mkApps`; the observable's transport across the preparation passes from `prepare_sound`. At every rung: `hcfg : ConfigPinned`, `hsup : Supported`, `hnb : NoBodylessRefs`, `hwf : LBWfPeregrine` by `lbWfPeregrine_of_check (by decide +kernel)`, `hwt : TrExprS`, the target-side `WcbvEval`; `hcb : CompilerBodies` at G1 only; `hev : SEval` at G5 only |
| **C** — this repository's own code | `E : EraserAsks` — four fields, unchanged since W5: `passes_monotone`, `passes_sound`, `oracle_false_refl`, `kernel_ind_head_true` (residue: a *reduced* telescope longer than `isArityCheck`'s constant budget, and any other kernel error inside it). `block_keys_distinct` is deleted, F-UNSAFEREC's guard making distinctness a *conclusion* of a successful run (`run_rec_exit_reg`'s fifth conjunct) rather than a bundle field — though nothing today spends that conclusion: both call sites of `run_rec_exit_reg` discard it, and `run_rec_exit_nodup` and its would-be consumer `blockKeyed_install` each have no consumer of their own (§4). `hbridge`'s two fields — `erasesEnv` and `lowerEnv` — open, §4. `hargReach`, at G8 alone — open, §4; U9 corrected what its residue is (§4) |
| **D** — specifications of Lean's `Meta`/`Core` primitives | `P : ∀ Us, ErasureSpec lenv env Us gw` — seven fields, unchanged: `env_connect`, `lookup_adequate`, `fresh_names`, `oracle_refl`, `decl_adequate`, `prim_monotone`, `block_adequate`; taken at every level scope since U5, which is what a sub-run below `Erasure.visitMutual`'s `withReader` needs. **`prim_monotone : PrimMonotone gw` is per-primitive**, not a blanket `MetaM` claim: eight clauses, one per named primitive (`getEnv`, `logInfo`, `isInstance`, `inferType`, `isProof`, `forallBoundedTelescope`, `lambdaBoundedTelescope`, `liftMetaM`), with the two bounded telescopes and `isProof` stated *compositionally* so the two anonymous continuations F-ACC/F-SPARSE introduced are covered by the derived `PrimGenMono` predicate rather than by a further universal (`ErasureSpec.lean:259-306`; C1, `8bdffca`, closing a finding raised against an earlier single unconditional `PrimMonotone.metaM` field, `scratch/round7/W2-refute.md` §5/R7). `htbl : SourceTableAdequate`, `hsafe : TableSafe`, `hblk : TableBlocks`, `hprep` (the prepared term is the subject), `hrun` (the run produced the committed program) |
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
`doc/coverage.md` is generated by `lake exe coverage` from the tree; `lake exe coverage --check` is green at HEAD (`scratch/round7/gate3/03c-coverage-check-after-fix.out`, after one bookkeeping regeneration this round, `4e5bd13`, that moved a stale whole-environment kername count). Arith is in
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

* **Five carry no content.** `hprep`'s equation is conjunct 1 re-exported verbatim (`Capstone.lean:201` = `:211`). `LBWfPeregrine g<i>Env g<i>Term`
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
  an equation whose sound half only is stated (the converse is refuted by an arity whose result sort sits under a `let`, F-ARITYLET), so the biconditional was correctly not written as a guard against that counterexample — but the clause has no subject at any rung to be non-vacuous about.
* **`ErasesEnv.axioms`, `LowerEnv.axioms` and `SpecContent.axioms`** have no witness at any rung: 0 body-less emitted entries and 0 bodied emitted
  keys lacking a tabled body, at all eight rungs (`decide +kernel`). A standing vacuity, not introduced this wave — no rung reaches a quotient
  primitive or a recursor, so F-QUOT's and F-EQREC's registering exits are off every rung's path; `doc/coverage.md`'s realizer census is the only
  place a covered program registering a realizer is actually measured.
* **`LBWfPeregrine.etaCtorsTm`** is trivial at all eight (every `g<i>Term` is a bare `.const`, so `ConstructSpine` is uninhabited); `.casesExh` is
  trivial at G1–G4 (`case = 0`); `.fixLambda` at G1–G5 (`fix = 0`); `.projDecl` at G1, G5, G6 (`proj = 0`); `ErasesEnv.elims` at G1–G4 (no `.case`
  node). `IndCovered.elims`, by contrast, is *not* trivial at any rung — every informative declared block demands an `ElimDecl` — and §4 is where
  that turns into a refutation of a different clause.

## 4. What is open

### `hbridge` — the composition is stated, and it is unsatisfiable at the rungs it is tried against
`bridgeEnv_of_regContent` (`Capstone.lean:153-169`) composes `hbridge`'s payload out of four
named antecedents about the run's final state — `RegInvShape'` with its content clause
`RegContent`, `RegKeyed`, the lookup transfer `hsub : ∀ kn d, LBTerm.envLookup Γspec kn = some d →
LBTerm.envLookup sf.gdecls kn = some d` — plus `ErasuresDeclared env [] Γspec [] pe` at the
prepared term, and nothing else: `hdeps`, the dependency closure `bridgeEnv_of_regInv` still
takes as a premise, is here *derived* from `RegContent.declEnv` by
`ReachableFrom.isSome_of_declaredEnv` (§2), and `hbridge`'s own `Lower Γspec t₀ t` premise is not
spent. **No theorem in the tree produces any of the four for a run of the shipping eraser**
(U9-report.md §2), and this round's audit found something stronger: read at the rungs' actual
final state, the four are **jointly contradictory**, so the composition is not a live route to
`hbridge` at any rung tried against it (`scratch/round7/W3-refute.md`, R1; mechanised,
`scratch/round7/z_hsub.lean`, axioms `[propext, Classical.choice, Quot.sound]`):

* **The content route.** `hsub` applied to `RegContent.defns`'s own `DefnDecl Γspec (toKername n) b₀`
  forces `b₀ = t` — the specification entry and the emitted entry become the same declaration —
  collapsing the clause to `Erases env (lp n) [] b t`: the *emitted* body of a tabled name would
  have to be, itself, an `Erases` image (`Round7W3.regContent_hsub_collapse`). `Erases`'s eleven
  arms (`Erases.lean:211-276`) never produce a `.fix` or a `.case` node
  (`Round7W3.erases_shape`), and the emitted environments carry those nodes at tabled keys:
  `spikeCase` (G5, `.case`), `spikeRec` (G6, η-expanded `.fix`), `Nat.add`/`Nat.mul`/`Nat.pow`/`Nat.sub`
  (G7 and G8, η-expanded `.fix`), `Nat.pred` (G7 and G8, `.case`). So `RegContent`'s content
  clause and `hsub` are jointly `False` at G5, G6, G7 and G8, mechanised at each rung's exact
  state (`Round7W3.g5_regContent_hsub_false` … `g8_regContent_hsub_false`) — not a corner case:
  `Lower` exists to turn a `.const`-keyed erasure image into a `.fix`/`.case` node, so demanding
  the two environments agree on bodies denies the pass.
* **The eliminator route, independent of any body, reaching all eight rungs.** `SpecContent.blocks`
  fires at every declared block key and returns `IndCovered`, whose `elims` field puts the
  block's `casesOn` into `Γspec` as an `ElimDecl` — a `RuntimeKey`, which `Lower.const` refuses
  and the eraser never emits. `z_triv.out` counts the declared blocks — 1, 2, 2, 3, 2, 1, 12, 12
  across G1…G8 — against **zero** emitted eliminator keys at every rung, so `hsub` fails there
  too, at G1–G4 as much as G5–G8 (`Round7W3.hsub_false_of_undeclared`,
  `Round7W3.g7_hsub_false_elim`).
* **A principled repair is proved, and not yet landed.** `hsub` is spent in exactly one place,
  `regSaturated_of_regKeyed` (`SpecEnv.lean:162-170`), and both of that theorem's fields read
  only the **shape** of the emitted entry, never its body. The shape-preserving statement —
  `SpecKeysEmitted`, "a specification key that isn't a runtime key has *some* emitted entry of the
  matching shape" — is satisfiable at G5–G8 and proved to give the same conclusion
  (`regSaturated_of_regKeyed_shape`, `scratch/round7/z_hsub.lean`, not shipped in the tree);
  `regSaturated_of_regKeyed`'s `_H : RegInvShape'` argument, already unused there, can be dropped
  with it.
* **The theorem is not on the capstone's own proof path.** `erasure_bridge_of_run` — what
  `shipping_erase_correct_firstorder` actually calls — never mentions `bridgeEnv_of_regContent`,
  and `bridgeEnv_of_regContent` itself has no caller anywhere in the tree.

Below the composition, the same three obstructions `doc/rework/08-REPAIRS-W5.md` §2.1 named still
stand, one of them now partly closed: the eighteen bridge motives used to be stated at one fixed
level scope, which U5 repaired (they are now stated at every scope `Erasure.visitMutual`
re-enters); what is left of that obstruction is a single shipping edit — one `withReader` field
resetting `lctx` at `Erasure.visitMutual`'s two dependency re-entries (F-DEPLCTX,
`doc/rework/03-DEV-FIX.md`) — without which no `RegInvShape'`/`RegContent` exists at a member
sub-run at all. The α gap (`ReifiedDecl.Prepared` pins a tabled body only up to `Expr.AlphaEq`,
and `lake exe reify --check` reports five of G7/G8's bodies matching only up to binder names) and
the ∀-`Γspec` shape mismatch (`RunRefines` reads content at *every* `SpecEnv` of the final state,
where the repair produces one) are untouched by this round.

**`hargReach`'s residue, corrected (U9).** `doc/trust.md` used to say that discharging it "needs
the same content clause `hbridge`'s two fields wait on" — false: `ErasesEnv env g8Table.body?
g8Table.levels? Γspec t₀`, content clause included, is an **antecedent** of the binder, not
something it waits on. `Lower Γspec t₀ g8Term` forces `t₀ = .const (toKername ``benchArith)`
through `Lower.source_const` (`.box` and `ctor` have no `Lower` arm to a `.const`), and
`ErasesEnv.defns` then produces the declared erasure `b₀` of `benchArith`'s tabled body;
`ReachableFrom.through_body` reduces the binder to one residue: **every** erasure of
`benchArith`'s tabled body reaches `Nat`'s block. That is a source-side non-erasability fact about
a reified body, of a kind with `Supported`/`NoMaxLevels`, and it is not produced by, nor waiting
on, the registration invariant at all (`scratch/round7/u9_g8.lean`, sorry-free).

**A hidden assumption, benign.** C2c (`83382a5`) removed `TabledLevels` from `StepDelta`, where
the capstone used to discharge it by the *proved term* `tabledLevels_of_table htbl hsafe hcb`,
and folded its two conjuncts into `ErasesEnv.defns`, reachability-gated. `ErasesEnv` is what
`hbridge` supplies, so at HEAD the capstone **assumes** what it used to **prove**. Nothing is
lost — the added conjuncts remain a theorem of the capstone's own hypotheses
(`defns_level_conjuncts_free (htbl) (hsafe) (hcb) = tabledLevels_of_table htbl hsafe hcb`,
`[propext, Classical.choice, Quot.sound]`) — but the relocation makes `hbridge` look larger than
it is, and `doc/trust.md`'s `ErasesEnv` row should say the last two conjuncts are dischargeable
today (`scratch/round7/W3-refute.md`, R2).

**Two dead binders in the capstone, standing since before this round.** `hnb : NoBodylessRefs Γ t`
is never mentioned by `shipping_erase_correct_firstorder`'s proof body, and `hblk : TableBlocks
lenv env tbl` is never mentioned by `erasure_bridge_of_run`'s (mechanised by an unused-binder scan
of the proof terms, `scratch/round7/z_dead.out`; confirmed directly against `Capstone.lean:230-260`
and `:80-93`). Neither is a regression — `git show d61db80:…/Capstone.lean` has the same shape —
and each rung still discharges `hnb`/`hblk` by a checked term, so nothing here is false; but
`hnb`'s docstring claim ("without it a run reaching a body-less declaration would satisfy the
conclusion vacuously") is not realised in the statement the proof actually builds — the
non-vacuity it describes belongs to `hev`, which only G5 inhabits (`W3-refute.md`, R4).

**Two restatements of this round have no consumer anywhere in the tree.** `TableBlocks`'s
`informative` conjunct (C2a, `d655838`, correctly repaired to read a block member's body at
`tbl.levels? m` rather than at `[]`) is read by nothing: `erasure_bridge_of_run` takes `hblk` and
never destructs it, and the only other occurrence, `blockKeyed_install`
(`VisitExprRefines/Step/Env.lean:609`), reads `.members` alone and has no consumer of its own — a
dead chain two links long, ending every rung's `hblk` at a slot nothing reads. And
`SourceTableAdequate.compilerLevels` (C2d, `3ecf357`) and its transport `compilerLevels?_eq` are
read by nothing: the field is contentless at G1–G5 (no `_unsafe_rec` companion is tabled there),
live but unspent at G6–G8 (`spikeRec`; `Nat.add`/`mul`/`pow`/`sub`), and satisfied with zero
violations wherever it does have a subject — a correct identification, booked for U7's
`RegContent.defns`, which itself is not yet derived at a run (`scratch/round7/W3-refute.md`, R3a,
R3b).

**`Lower`'s non-determinism at a block member.** `LowerEnv.defs`'s second disjunct (the η-wrapped
arm F-ETA added) is redundant — it collapses into the first through `Lower.fixEta_of_block`, so
it strengthens nothing — but its *presence* means `Lower.fixBody` and `Lower.fixEta` both relate
the same specification body to two different emitted terms, so `Lower` is now provably not a
function: `¬ ∀ Γ s t t', Lower Γ s t → Lower Γ s t' → t = t'`
(`scratch/round7/W2-refute.md`, R3/R4). Nothing in the tree assumes `Lower` functional, so this is
a recorded cost of the F-ETA repair, not a defect.

**lean4lean asks** (owner: the fork). The commission is `downstream-asks-round4.md` in the sibling `lean4lean` checkout; `doc/upstream-asks.md` is
this side's register. Items 2, 6, 9 and 10 are the four `UpstreamAsks` fields; item 3 is what criterion 21 waits on; item 4, the kind transfer from
`lenv` to `env.constants`, blocks `hfo` and `ErasesEnv.tabled`'s exclusion; and `TrProj`, entirely unproven at the pin, still blocks `hcb` at
G2–G8 — 10 of G7's 30 tabled bodies carry an `Expr.proj`, all of them class projections, and `TrExprS` at a `.proj` routes through it. Unchanged this
round: the pin is the same commit and no lean4lean-facing proof was touched.

**`hev` stays vacuous outside G5.** `Green.g5_seval` is the only constructed source-evaluation
witness in the tree; every other rung, G7/G8 included, binds `hev` rather than proving it —
`benchArith 0`'s 45 recursive calls each owe N20's per-branch obligation, against G5's 45-line,
three-`StepDefeq` cost for a single δ and ι. Unchanged this round.

**Shipping findings from `dev/fix`.** `doc/rework/03-DEV-FIX.md`'s "Applied edits" table is the
single index: ten findings — F-PROP, F-ETA, F-ETA2, F-SPARSE, F-EQREC, F-QUOT, F-ACC, F-DEPTH,
F-UNSAFEREC, F-KERNAME — each fixed on `dev/fix`, merged at `2036c853`, and repaired here
(`doc/rework/10-MERGE-FIXES.md`, M1–M8), with the commit, the byte measurement and the
verification obligation each closed recorded per row. F-FUEL, verification-authored rather than a
shipping finding, reproduces a pre-reroute oracle verdict and is merged too. Two fixes reach
`doc/coverage.md` as strict gains: F-QUOT/F-EQREC make `NoBodylessRefs` true on Fannkuch, and
F-ETA's η-expansion is what lets `LBWfPeregrine.expandedFix` hold at G6, G7 and G8 (vacuously true
at the other five). **F-PRODUCT is the one item still not fixed, and not meant to be**:
`auto_inline_typeclass_dispatch` (`LeanToLambdaBox/Erasure.lean:85`, `:88-118`, `:896-903`), an
unverified product feature that rode in on the verification branch, off by default. Not a
miscompile, no wave depends on it, and the `.ast.inlinings` channel it drives is a class-**E** row
in `doc/trust.md`.

## 5. Delivery
Branch `dev/verify`: 299 commits ahead of `main`, 47 ahead of the last-pushed `origin/dev/verify`,
14 of them this round (`8bdffca` C1 … `4e5bd13` bookkeeping, on top of `d61db80`, wave 2's last
commit). `lake build` green at 174 jobs (`scratch/round7/gate3/01-lake-build.out`); the only
`sorry` warnings are lean4lean's sixteen (§1), and two standing linter warnings predate this round
and sit outside it — `LeanToLambdaBox/Semantics/Substitution.lean:231` (`recData` should be a
`theorem`) and `LeanToLambdaBox/ColdStartShape.lean:380` (`simpa` where `simp` would do). Tree-wide,
including the `dev/fix` merge's shipping fixes and their `test/fixes/` regression suite
(`scripts/fixes.sh`, wired into `.github/workflows/build.yml` as its own step, after the build and
before the ledger).

`.github/workflows/build.yml` runs the whole battery on pushes to `main` and `dev/verify`, with
only `LICENSE` in `paths-ignore`. Every check in it is green at HEAD
(`scratch/round7/gate3/`, 23 commands, one clean run from a checkout at `4e5bd13`); `lake exe
hygiene --schedule` reports **0 inversions** (`8 deletion rows, 45 deleted files, 18 live imports
of them`). `lake exe hygiene --dead` lands at exactly its 321-declaration budget
(`scratch/round7/gate3/16-hygiene-dead.out`): the 240 `doc/coverage.md` accounts for (the tooling
107, the frozen benchmark sources 43, `LeanToLambdaBox/Optimize.lean` 71 and
`LeanToLambdaBox/ErasesUniform.lean` 19), plus `test/Vacuity.lean`'s five regression lemmas and
the 76 declarations under the ten `test/fixes/` shipping-fix regressions, none imported by the
theorem it guards. The pin is lean4lean `20ec229f1a8c6358f3b3852c4e27d2be523d1b87` —
`lakefile.toml`, both fields of `lake-manifest.json`, the first line of `test/lean4lean-sorries.expected` — and every measurement here was taken at it.
Both consumers still pin `main` — peregrine-tool's Lean test lakefile and the frontend benchmark's, in the sibling checkouts — resolved to `42f8f51`
and `f54d17d`, ancestors of this branch, so neither builds the verified eraser.

| # | Verdict | Reason |
|---|---|---|
| 3, 4, 10, 11, 12, 14, 15, 16, 17, 19 | PASS | — |
| 1, 2, 5, 6, 8 | PASS as amended | eleven `Erases` rules — ten congruences plus `box`, `ctor` the eleventh — with no `.case` and no `.fix`, and `ctor`'s argument list literally `[]`; one L4 pass, `optimize`, with `LBOptimize_correct` and three non-vacuity guards, `LBCompile` split away so the composition has no subject (A9); T5's naming half clean at eight premises, U3.1's target, not five; `FirstOrderInd` decides true on `Nat`, `Bool` and `FOFixture.Tree`, with `List` and `Prod` excluded on purpose (A6/A15) |
| 9 | PASS as renamed | `ErasureSpec.oracle_sound_of_run` — in the capstone's closure, discharged, not assumed |
| 13 | PARTIAL | `green_G7` and `green_G8` elaborate; five of the capstone's fifteen binders are checked terms at both — `hcfg`, `hwt`, `hsup`, `hnb`, `hwf` — and ten stand, with `hcb` among them from G2 on; G8 carries one binder the other seven do not, `hargReach`, for its non-empty spine |
| 18, 20 | SPLIT | narration clean, comment fraction 28.5% tree-wide with 5 of 68 files under 20%; the exception list to the no-dead-code rule is **empty**, and `lake exe hygiene --dead` reports 321 declarations outside the closure (above) |
| 7 | FAIL — no subject | `Subsingleton` does not occur; the condition is `Erasable`, discharged by `Erases.sort_erasable`/`forallE_erasable` and by the oracle |
| 21 | FAIL, deliberate | `LeanToLambdaBox/CheckerAdequacy.lean:41` keeps `namespace Lean4Lean.TypeChecker` until upstream ask 3 lands |
| 22 | FAIL on the branch half | pin and CI pass; the verified eraser is on `dev/verify` and both consumers pin `main` |

## 6. How to re-measure

    lake build ; lake build VerifyBench ; lake exe coverage --check
    bash scripts/fixes.sh
    bash scripts/ledger.sh ; bash scripts/erases_correct.sh ; bash scripts/erasesLB.sh ; bash scripts/lean4lean-sorries.sh
    bash scripts/frozen.sh ; bash scripts/hygiene.sh --allow test/hygiene.allow
    lake exe hygiene --dup ; lake exe hygiene --schedule ; lake exe hygiene --tables ; lake exe hygiene --cites
    lake exe hygiene --anti-epicycle LeanToLambdaBox/Lower.lean ; lake exe hygiene --dead   # --dead is a budget of 321
    lake exe green-check --self-test ; lake exe green-check --all
    lake exe reify --check LeanToLambdaBox.Green …g1Table…g8Table ; lake exe reify --blocks LeanToLambdaBox.Green …g1Table…g8Table
    lake exe reify --prepared LeanToLambdaBox.Green LeanToLambdaBox.Green.spikeZero … arithClosed benchArith

`.github/workflows/build.yml` holds the argument lists in full. `--prepared` takes constant names, not table names, and `lake build VerifyBench` must
precede `coverage --check`, because the five corpus `.ast` files it measures are build artifacts.
