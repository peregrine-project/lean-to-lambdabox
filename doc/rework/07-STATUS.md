# 07 — Status

## 1. The theorem
`LeanToLambdaBox.shipping_erase_correct_firstorder` (`LeanToLambdaBox/Capstone.lean`). Subject: `Erasure.erase`, the function `#erase` calls, from the
empty state at a pinned configuration. If the run returns `.untyped Γ (some t)` on a source term `e` whose prepared form is `pe`, then there are
`Γspec` and `t₀` with `Erases env [] [] pe t₀` and `Lower Γspec t₀ t` — the emitted term is the lowered image of an erasure of the prepared term —
together with `ErasesEnv env tbl.body? Γspec t₀`, `LowerEnv Γspec Γ` and `LBWfPeregrine Γ t`: the emitted environment is the lowered, pruned image of
`Γspec`, and the emitted program satisfies what peregrine's first pass reads (`LBExpandedFix` is **not** concluded, F-ETA). The last conjunct is the
theorem's own binder `hwf`, carried rather than derived, and every rung discharges it by kernel computation. The observable conjunct is a forward
simulation at first-order answers: for closed `args` whose λ□ images `targs` each carry an erasure, that erasure's lowering and its own `ErasesEnv`
clause, and whose applied spine has a translation `TrExprS env [] [] (mkApps pe args) vs`, if `SEval env tbl.body? [] fullFlags [] (mkApps e args) v`
and `v` is typed at a spine of an inductive `I` with `FirstOrderInd env I`, then `WcbvEval Γ eraseFlags (LBTerm.mkApps t targs) tv` for the `Lower`
image `tv` of the unique erasure `tv₀` of `v`, with `NoBox tv`. That is `[S]` §7.3–7.4's shape with λ□'s own `WcbvEval` as target semantics, `Lower`
carrying the four Lean-specific compilation steps, and the source evaluation reading the compiler-body table (N8). The per-argument clause and the
spine translation are what `erases_correct` requires of a spine; at `args = []` both are vacuous, which is where G1–G7 apply them.

| Class | Binders |
|---|---|
| proved, or per rung a checked term | inside the theorem: the erasure half `erasure_bridge_of_run`, supplying all eighteen bridge steps; the answer's shape and uniqueness from `firstorder_erases_core`, and `NoBox tv` at the *lowered* value from `noBox_lower_of_foSpine`; the simulation, `erases_correct` applied once at the spine with `ErasesEnv.mkApps`; the observable's transport across the preparation passes from `prepare_sound`. At every rung: `hcfg : ConfigPinned`, `hsup : Supported`, `hnb : NoBodylessRefs`, `hwf : LBWfPeregrine` by `lbWfPeregrine_of_check (by decide +kernel)`, `hwt : TrExprS`, the target-side `WcbvEval`; `hcb : CompilerBodies` at G1 only; `hev : SEval` at G5 only |
| **C** — this repository's own code | `E : EraserAsks` — `passes_monotone`, `passes_sound`, `oracle_false_refl`, `kernel_ind_head_true` (bounded by F-DEPTH), `block_keys_distinct` (bounded by F-UNSAFEREC). `hbridge`'s two fields — `erasesEnv` and `lowerEnv`, both needing a specification environment for the run's final state. `hargReach`, at G8 alone: that the subject's erasure reaches `Nat`'s block in that environment, which is what `Green.g8_argErasesEnv` leaves of the per-argument clause at the one rung with a non-empty spine |
| **D** — specifications of Lean's `Meta`/`Core` primitives | `P : ErasureSpec` — `env_connect`, `lookup_adequate`, `fresh_names`, `oracle_refl`, `oracle_meta`, `decl_adequate`, `prim_monotone`, `block_adequate`. `htbl : SourceTableAdequate`, `hsafe : TableSafe`, `hblk : TableBlocks`, `hprep` (the prepared term is the subject), `hrun` (the run produced the committed program) |
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
Quot.sound]`, no `sorryAx`; `LBOptimize_correct` `[propext, Quot.sound]`; `lbEval_sound` `[propext]`; `bridgeEnv_of_regInv` nine names, no `sorryAx`.
`#print axioms` measures a proved theorem and never a hypothesis, which is why relocating a field of the bridge bundle to a binder of the capstone
moves no row, and why `decide +kernel` at a rung adds no name.

## 3. Coverage
`doc/coverage.md` is generated by `lake exe coverage` from the tree. Arith is in the fragment and is the subject of rungs G7 and G8. Sieve and
BinaryTrees are out at `recursorHead` on `Eq.rec` through `Bool.noConfusion` (F-EQREC); Quicksort at F-EQREC, the well-founded
`Nat.div.go`/`Nat.modCore.go` route and `sparseCasesOn`, with a wrong emitted program besides (F-SPARSE); Fannkuch at F-EQREC and `etaContractedMinor`
on `Decidable.casesOn`, and it also fails `NoBodylessRefs`.

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

## 4. What is open
**Proof work in this repository, now one item.** `hbridge`'s `erasesEnv`/`lowerEnv`: `bridgeEnv_of_regInv` is the proved interface, but nothing
produces `RegInvShape'` at the run's final state. `doc/rework/08-REPAIRS-W5.md` §2.1 states what would: one content clause carrying both readings of a
*single* erasure witness, read at a `Γspec` threaded as an *output* of the refinement and grown with the state by a fresh-prefix extension. That is
what closes the determinism gap — `SpecContent.defns` names *some* erasure of the compiler body while `RegInvShape'.defs` demands the emitted body be
the `Lower` image of *that* one, and `Erases` is not deterministic outside the first-order fragment — and §2.2 shows the registry-domain converse is a
theorem about `ConstExt`, not a missing clause. Three measured obstructions stand in the way, each independent: the eighteen motives are stated at a
fixed level scope through `BridgeInv.lparams`, which `Erasure.visitMutual` re-enters under the member's own `levelParams`, and 16 of G7's 30 tabled
bodies belong to a polymorphic constant; `ReifiedDecl.Prepared` pins a tabled body only up to
`Expr.AlphaEq` — deliberately, since on equality the clause is uninhabited wherever `inlineMatchers` fires — while `Lower` is not α-closed on its
source, and `lake exe reify --check` reports five of G7/G8's bodies matching only up to binder names; and `RunRefines` reads content at *every*
`SpecEnv` of the final state, the opposite shape to the one environment §2.1 produces. `hargReach` at G8 is the same obligation seen from the ladder:
it is what `Green.g8_argErasesEnv` leaves of the argument's environment clause, and the content clause is what would discharge it.

**lean4lean asks** (owner: the fork). The commission is `downstream-asks-round4.md` in the sibling `lean4lean` checkout; `doc/upstream-asks.md` is
this side's register. Items 2, 6, 9 and 10 are the four `UpstreamAsks` fields; item 3 is what criterion 21 waits on; item 4, the kind transfer from
`lenv` to `env.constants`, blocks `hfo` and `ErasesEnv.tabled`'s exclusion; and `TrProj`, entirely unproven at the pin, blocks `hcb` at G2–G8 — 10 of
G7's 30 tabled bodies carry an `Expr.proj`, all of them class projections, and `TrExprS` at a `.proj` routes through it.

**Shipping findings, reported and not fixed** (`doc/rework/03-DEV-FIX.md`).

| id | Site | Measured symptom |
|---|---|---|
| F-PROP | `LeanToLambdaBox/Erasure.lean:192-241`, `LeanToLambdaBox/Basic.lean:164` | `one_inductive_body … false` on 71 of 71 emitted inductives, so a `.case` on a `□` discriminee is stuck |
| F-ETA | `LeanToLambdaBox/Erasure.lean:859-919` | 50 `tFix` nodes, 50 of them a whole constant body: no emitted fixpoint is applied, so `expanded_eprogram` is false on all five |
| F-ETA2 | `LeanToLambdaBox/Erasure.lean:722-728`, `:705-712` | 982 of 982 emitted `tConstruct` nodes carry an empty argument list, so applied-form λ□ needs no constructor η |
| F-SPARSE | `LeanToLambdaBox/Erasure.lean:770`, `:817` | `PANIC at Erasure.visitCases LeanToLambdaBox.Erasure:817:55`, exit 0, and a wrong `.ast` written (Quicksort) |
| F-EQREC | `LeanToLambdaBox/Erasure.lean:873-876` | one `(constant_body None)` in `Fannkuch.ast`, `((MPdot (MPfile ()) "Eq") "rec")`, and the program applies it |
| F-QUOT | `LeanToLambdaBox/Erasure.lean:873-876` | the same arm emits a `Quot` primitive as a body-less axiom that `peregrine validate` accepts |
| F-ACC | `LeanToLambdaBox/Erasure.lean:768-835` | latent: `largeElimClause` at `Acc` is `some (2,[1])`, so fixing F-PROP alone would box a data field; 0 occurrences on the five |
| F-PRODUCT | `LeanToLambdaBox/Erasure.lean:85`, `:88-118`, `:896-903` | `auto_inline_typeclass_dispatch`, an unverified product feature on the verification branch, default `false` |
| F-DEPTH | `LeanToLambdaBox/Relevance.lean:46` | `approxDepth` saturates at 255 so the arity fuel caps at 256, and is 1 at an alias: `kernel isErasable Bar = error`, `isErasableMeta Bar = false` |
| F-UNSAFEREC | `LeanToLambdaBox/Erasure.lean:906`, `:916-918` | a legal `mutual unsafe def u / u._unsafe_rec` block maps to `[u, u]`: 1 distinct key of 2, two `FixDef`s named `u`, no error |
| F-KERNAME | `LeanToLambdaBox/Basic.lean:35` | `toKername (.num .anonymous 5) = toKername (.str .anonymous "5")` by `rfl`; latent — 228,987 constants, 228,987 distinct keys, 0 collisions |

**The one executed-code edit.** F-FUEL, `LeanToLambdaBox/Relevance.lean`: `isArityCheck.loop` throws on fuel exhaustion instead of returning `false`,
routing such cases to `Erasure.isErasableMeta` and reproducing the pre-reroute verdict. Made on `dev/fix`, merged.

## 5. Delivery
Branch `dev/verify`, 250 commits ahead of `main`; `lake build` green at 173 jobs, the only `sorry` warnings lean4lean's.
`.github/workflows/build.yml` runs the whole battery on pushes to `main` and `dev/verify`, with only `LICENSE` in `paths-ignore`. One check in it is
red, and it reads a document rather than the tree: `lake exe hygiene --schedule` reports a single inversion, because `doc/rework/02-PLAN.md` §4's W2
row backticks `Output.lean` while naming declarations deleted *inside* a standing file, so the tool reads a file deletion that
`LeanToLambdaBox/OutputCheck.lean` then imports. The same row's other half already avoids it by naming the module unbackticked as a path; writing the
first clause the same way clears the inversion and changes no meaning. The pin is lean4lean `20ec229f1a8c6358f3b3852c4e27d2be523d1b87` —
`lakefile.toml`, both fields of `lake-manifest.json`, the first line of `test/lean4lean-sorries.expected` — and every measurement here was taken at it.
Both consumers still pin `main` — peregrine-tool's Lean test lakefile and the frontend benchmark's, in the sibling checkouts — resolved to `42f8f51`
and `f54d17d`, ancestors of this branch, so neither builds the verified eraser.

| # | Verdict | Reason |
|---|---|---|
| 3, 4, 10, 11, 12, 14, 15, 16, 17, 19 | PASS | — |
| 1, 2, 5, 6, 8 | PASS as amended | eleven `Erases` rules — ten congruences plus `box`, `ctor` the eleventh — with no `.case` and no `.fix`, and `ctor`'s argument list literally `[]`; one L4 pass, `optimize`, with `LBOptimize_correct` and three non-vacuity guards, `LBCompile` split away so the composition has no subject (A9); T5's naming half clean at eight premises, U3.1's target, not five; `FirstOrderInd` decides true on `Nat`, `Bool` and `FOFixture.Tree`, with `List` and `Prod` excluded on purpose (A6/A15) |
| 9 | PASS as renamed | `ErasureSpec.oracle_sound_of_run` — in the capstone's closure, discharged, not assumed |
| 13 | PARTIAL | `green_G7` and `green_G8` elaborate; five of the capstone's fifteen binders are checked terms at both — `hcfg`, `hwt`, `hsup`, `hnb`, `hwf` — and ten stand, with `hcb` among them from G2 on; G8 carries one binder the other seven do not, `hargReach`, for its non-empty spine |
| 18, 20 | SPLIT | narration clean, comment fraction 28.6% tree-wide with 5 of 67 files under 20%; the exception list to the no-dead-code rule is **empty**, and 240 declarations sit outside the closure — the tooling (107), the frozen benchmark sources (43), `LeanToLambdaBox/Optimize.lean` (71) and `LeanToLambdaBox/ErasesUniform.lean` (19), the last two reached by the aggregator and by nothing else |
| 7 | FAIL — no subject | `Subsingleton` does not occur; the condition is `Erasable`, discharged by `Erases.sort_erasable`/`forallE_erasable` and by the oracle |
| 21 | FAIL, deliberate | `LeanToLambdaBox/CheckerAdequacy.lean:41` keeps `namespace Lean4Lean.TypeChecker` until upstream ask 3 lands |
| 22 | FAIL on the branch half | pin and CI pass; the verified eraser is on `dev/verify` and both consumers pin `main` |

## 6. How to re-measure

    lake build ; lake build VerifyBench ; lake exe coverage --check
    bash scripts/ledger.sh ; bash scripts/erases_correct.sh ; bash scripts/erasesLB.sh ; bash scripts/lean4lean-sorries.sh
    bash scripts/frozen.sh ; bash scripts/hygiene.sh --allow test/hygiene.allow
    lake exe hygiene --dup ; lake exe hygiene --schedule ; lake exe hygiene --tables ; lake exe hygiene --cites
    lake exe hygiene --anti-epicycle LeanToLambdaBox/Lower.lean ; lake exe hygiene --dead   # --dead is a budget of 242
    lake exe green-check --self-test ; lake exe green-check --all
    lake exe reify --check LeanToLambdaBox.Green …g1Table…g8Table ; lake exe reify --blocks LeanToLambdaBox.Green …g1Table…g8Table
    lake exe reify --prepared LeanToLambdaBox.Green LeanToLambdaBox.Green.spikeZero … arithClosed benchArith

`.github/workflows/build.yml` holds the argument lists in full. `--prepared` takes constant names, not table names, and `lake build VerifyBench` must
precede `coverage --check`, because the five corpus `.ast` files it measures are build artifacts.
