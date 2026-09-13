# 07 — Status

## 1. The theorem
`LeanToLambdaBox.shipping_erase_correct_firstorder` (`LeanToLambdaBox/Capstone.lean`). Subject: `Erasure.erase`, the function `#erase` calls, from the
empty state at a pinned configuration. If the run returns `.untyped Γ (some t)` on a source term `e` whose prepared form is `pe`, then there are
`Γspec` and `t₀` with `Erases env [] [] pe t₀` and `Lower Γspec t₀ t` — the emitted term is the lowered image of an erasure of the prepared term —
together with `ErasesEnv env tbl.body? Γspec t₀`, `LowerEnv Γspec Γ` and `LBWfPeregrine Γ t`: the emitted environment is the lowered, pruned image of
`Γspec` and satisfies what peregrine's first pass reads (`LBExpandedFix` is **not** concluded, F-ETA). The observable conjunct is a forward simulation
at first-order answers: for closed `args` whose λ□ images `targs` lie in `ErasesLB`, if `SEval env tbl.body? [] fullFlags [] (mkApps e args) v` and
`v` is typed at a spine of an inductive `I` with `FirstOrderInd env I`, then `WcbvEval Γ eraseFlags (LBTerm.mkApps t targs) tv` for the `Lower` image
`tv` of the unique erasure `tv₀` of `v`, with `NoBox tv`. That is `[S]` §7.3–7.4's shape with λ□'s own `WcbvEval` as target semantics, `Lower`
carrying the four Lean-specific compilation steps, and the source evaluation reading the compiler-body table (N8).

| Class | Binders |
|---|---|
| proved, or per rung a checked term | inside the theorem: the erasure half `erasure_bridge_of_run`, supplying all eighteen bridge steps; the answer's uniqueness and `NoBox tv₀` from `firstorder_erases_core`; the observable's transport across the preparation passes from `prepare_sound`. At every rung: `hcfg : ConfigPinned`, `hsup : Supported`, `hnb : NoBodylessRefs`, `hwt : TrExprS`, the target-side `WcbvEval`; `hcb : CompilerBodies` at G1 only; `hev : SEval` at G5 only |
| **C** — this repository's own code | `E : EraserAsks` — `passes_monotone`, `passes_sound`, `oracle_false_refl`, `kernel_ind_head_true` (bounded by F-DEPTH), `block_keys_distinct` (bounded by F-UNSAFEREC). `hve : VisitExprRunConcl` — a successful `Erasure.visitExpr` run grows the state canonically, only advances the name generator, and keeps a modelled inductive registry modelled. `hbridge`'s five fields — `erasesEnv` and `lowerEnv`, needing a specification environment for the run's final state; `wf`, needing ten of `LBWfPeregrine`'s twelve clauses; `simulate`, one simulation on the composite at the emitted environment; `noBox`, box-freedom of the *lowered* first-order value |
| **D** — specifications of Lean's `Meta`/`Core` primitives | `P : ErasureSpec` — `env_connect`, `lookup_adequate`, `fresh_names`, `oracle_refl`, `oracle_meta`, `decl_adequate`, `prim_monotone`, `block_adequate`. `htbl : SourceTableAdequate`, `hsafe : TableSafe`, `hblk : TableBlocks`, `hprep` (the prepared term is the subject), `hrun` (the run produced the committed program) |
| upstream | `A : UpstreamAsks` — `constsOrigin`, `constArityInv`, `mkAppsInv`, `indSpineInj`: `doc/upstream-asks.md` items 2, 6, 9 and 10. `hvwt`, `hty` and `hfo` are class **C** too and stand at every rung; `doc/trust.md` has a row each |
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

## 4. What is open
**Proof work in this repository.** `hbridge`'s `erasesEnv`/`lowerEnv`: `bridgeEnv_of_regInv` is the proved interface, but nothing produces
`RegInvShape'` at the run's final state, and the determinism gap is why — `SpecContent.defns` says each declared body is *some* erasure of the
compiler body while `RegInvShape'.defs` demands the emitted body be the `Lower Γspec` image of *that* one, and `Erases` is not deterministic outside
the first-order fragment. The route is to run the eighteen-motive refinement at a `Γspec` built from the run's output and prove `RegInvShape'` in the
same induction (`LeanToLambdaBox/VisitExprRefines/Motives.lean`, plus one `ConstExt` clause in `LeanToLambdaBox/ErasureRun.lean`). `wf`: ten of twelve
clauses have no supplier. `simulate`: `simulate_of_erases_correct` is proved and *stronger* than the field, by premises the capstone cannot supply at
a spine. `noBox`: needs `firstorder_erases_core` (`LeanToLambdaBox/FirstOrderInd.lean`) to export the constructor-tree shape it computes. `hve` is one
premise short — widen `VisitExprRunConcl` (`LeanToLambdaBox/VisitExprRefines/Step/Env.lean`) from `remove_irrel_constr_args = false` to `ConfigPinned
ctx.config`, since `visitExpr` reaches `prepare_erasure` through `visitMutual`'s `@[csimp]` branch, and `visitExprRunConcl_of_pinned` closes it; both
consumers already hold it. `LeanToLambdaBox/Alpha.lean` is 99 proved, `sorryAx`-free declarations outside the `Green.lean` ∪ `Capstone.lean` closure
with no consumer: `Green.lean` consumes its transports, or it takes an exception row naming a scheduled W6 consumer, or it is deleted.

**lean4lean asks** (owner: the fork). The commission is `downstream-asks-round4.md` in the sibling `lean4lean` checkout; `doc/upstream-asks.md` is
this side's register. Items 2, 6, 9 and 10 are the four `UpstreamAsks` fields; item 3 is what criterion 21 waits on; item 4, the kind transfer from
`lenv` to `env.constants`, blocks `hfo` and `ErasesEnv.tabled`'s exclusion; and `TrProj`, entirely unproven at the pin, blocks `hcb` at G2–G8.

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
Branch `dev/verify`, 248 commits ahead of `main`; `lake build` green at 173 jobs, the only `sorry` warnings lean4lean's. `.github/workflows/build.yml`
runs the whole battery on pushes to `main` and `dev/verify`, with only `LICENSE` in `paths-ignore`. The pin is lean4lean
`20ec229f1a8c6358f3b3852c4e27d2be523d1b87` — `lakefile.toml`, both fields of `lake-manifest.json`, the first line of `test/lean4lean-sorries.expected`
— and every measurement here was taken at it. Both consumers still pin `main`: `peregrine-tool/test/lean/lakefile.lean` and
`benchmarks/frontend_bench/lean/lakefile.lean`, resolved to `42f8f51` and `f54d17d`, ancestors of this branch, so neither builds the verified eraser.

| # | Verdict | Reason |
|---|---|---|
| 3, 4, 10, 11, 12, 14, 15, 16, 17, 19 | PASS | — |
| 1, 2, 5, 6, 8 | PASS as amended | eleven `Erases` rules — ten congruences plus `box`, `ctor` the eleventh — with no `.case` and no `.fix`, and `ctor`'s argument list literally `[]`; one L4 pass, `optimize`, with `LBOptimize_correct` and three non-vacuity guards, `LBCompile` split away so the composition has no subject (A9); T5's naming half clean at eight premises, U3.1's target, not five; `FirstOrderInd` decides true on `Nat`, `Bool` and `FOFixture.Tree`, with `List` and `Prod` excluded on purpose (A6/A15) |
| 9 | PASS as renamed | `ErasureSpec.oracle_sound_of_run` — in the capstone's closure, discharged, not assumed |
| 13 | PARTIAL | `green_G7` and `green_G8` elaborate; five of fifteen binders are checked terms, ten stand |
| 18, 20 | SPLIT | narration clean, comment fraction 28.5% tree-wide with 5 of 67 files under 20%; the exception list is one disciplined row, and 315 declarations sit outside the closure |
| 7 | FAIL — no subject | `Subsingleton` does not occur; the condition is `Erasable`, discharged by `Erases.sort_erasable`/`forallE_erasable` and by the oracle |
| 21 | FAIL, deliberate | `LeanToLambdaBox/CheckerAdequacy.lean:41` keeps `namespace Lean4Lean.TypeChecker` until upstream ask 3 lands |
| 22 | FAIL on the branch half | pin and CI pass; the verified eraser is on `dev/verify` and both consumers pin `main` |

## 6. How to re-measure

    lake build ; lake build VerifyBench ; lake exe coverage --check
    bash scripts/ledger.sh ; bash scripts/erases_correct.sh ; bash scripts/erasesLB.sh ; bash scripts/lean4lean-sorries.sh
    bash scripts/frozen.sh ; bash scripts/hygiene.sh --allow test/hygiene.allow
    lake exe hygiene --dup ; lake exe hygiene --schedule ; lake exe hygiene --tables ; lake exe hygiene --cites
    lake exe hygiene --anti-epicycle LeanToLambdaBox/Lower.lean ; lake exe hygiene --dead   # --dead is a budget of 315
    lake exe green-check --self-test ; lake exe green-check --all
    lake exe reify --check LeanToLambdaBox.Green …g1Table…g8Table ; lake exe reify --blocks LeanToLambdaBox.Green …g1Table…g8Table
    lake exe reify --prepared LeanToLambdaBox.Green LeanToLambdaBox.Green.spikeZero … arithClosed benchArith

`.github/workflows/build.yml` holds the argument lists in full. `--prepared` takes constant names, not table names, and `lake build VerifyBench` must
precede `coverage --check`, because the five corpus `.ast` files it measures are build artifacts.
