# Branch `dev/fix` — edits to executed eraser code

Every change that alters what the shipping eraser *executes* is made on `dev/fix`
(branched from `dev/verify`), one commit per finding, and merged into `dev/verify`
afterwards. Verification-only files (proofs, specifications, tools) never go through
`dev/fix`. This file is the single index: applied edits in the two tables below (`F-FUEL` is
verification-authored code, not shipping code, landed to reproduce a pre-reroute verdict),
and shipping findings reported to the owner but not edited here, each specified with its
site, the command that measures it, and that command's real output. A finding fixed on this
branch keeps its section below, marked *Fixed*. No wave depends on any of the unfixed
findings landing, and no unit applies one.

## Applied edits

| id | file | change | why | status |
|---|---|---|---|---|
| F-FUEL | `LeanToLambdaBox/Relevance.lean` | `isArityCheck.loop` throws on fuel exhaustion instead of returning `false` | The fuel is the depth of the *unreduced* type while the loop whnf-reduces, so a definitional alias for a ∀-telescope was judged relevant on the kernel branch (under-erasure); throwing routes such cases to `Erasure.isErasable`'s `.error` arm, i.e. to `isErasableMeta`, reproducing the pre-reroute verdict. `isArityCheck.WF` never mentions the fuel. | merged into `dev/verify` (9363fb9) |

### Shipping edits

One row per finding fixed on `dev/fix`, in landing order. Each commit carries the edit, its
regression test under `test/fixes/`, and its row here; `scripts/fixes.sh` runs every test and
diffs the marked lines of its output, and the `peregrine validate`/`eval` output of the
programs it emits, against the committed expectations. The *commit* column names the commit
by its subject, which `git log --grep` resolves — a hash written into the commit that carries
it would be the hash the commit had before that row was added.

| id | commit | files and functions | behaviour before | behaviour after | emitted bytes | test | verification obligations |
|---|---|---|---|---|---|---|---|
| F-SPARSE | `fix(F-SPARSE)` | `LeanToLambdaBox/Erasure.lean`: `visitCases`; new `LBTerm.hasLooseBVarFrom`/`LBTerm.hasLooseBVar` | A sparse `casesOn` panicked at the `unreachable!`, erased the whole elimination to `.box`, exited 0 and wrote a program `peregrine validate` accepts and `peregrine eval` either mis-evaluates or gets stuck on ("`Case: <15> branch not found`") | The inductive is read from `casesInfo.indName` and the catch-all is expanded into one alternative per uncovered constructor, in constructor order; the shapes that remain uncompilable (side-condition elimination, machine-`Nat`/`Int` discriminee, alternatives that do not match the constructors, a catch-all with a free index) `throwError`. No `unreachable!` and no path to a wrong `.ast` with exit 0 | yes — `Quicksort` only (65474 → 65686 bytes); `Arith`, `Sieve`, `BinaryTrees`, `Fannkuch` and rungs G1–G6 byte-identical | `test/fixes/F-SPARSE.lean` | `visitCases`'s body changed, so the `VisitExprRefines` step bodies that mirror it must be re-proved (no mutual member added or removed: the `partial_fixpoint` arity is unchanged). The fragment is unaffected — `Supported.supportedHead` still refuses `isSparseCasesOn`/`isMatcherName` heads, and `CasesOnShape` (`SourceEval.lean:163`) and `BlockAdequate.casesOnDecl` (`ErasureSpec.lean:202`) may keep `c.getPrefix = I`, which holds of every head they admit. Covering the expanded shape would need `indName` there plus an `Erases`/`Lower` arm for a catch-all alternative and an `ErasesCorrect/Iota.lean` case |
| F-UNSAFEREC | `fix(F-UNSAFEREC)` | `LeanToLambdaBox/Erasure.lean`: `visitMutual`; `LeanToLambdaBox/Basic.lean`: `ModPath`/`Kername` gain `deriving DecidableEq` (`List.Nodup`'s `Decidable` instance needs `DecidableEq` on the element type) | `remove_unsafe_rec` strips one literal `_unsafe_rec` component and is not injective: a `mutual` block legally declaring both `u` and `u._unsafe_rec` mapped to `[u, u]`, so two `FixDef`s were named `u` and two declarations were registered at the one λbox key `u` — `fixvarMap`'s second binding silently overwrote the first, no error, exit 0 | Once the block names are mapped through `remove_unsafe_rec`, `visitMutual` `throwError`s unless the mapped kernames are pairwise distinct (`List.Nodup`), before the `withReader`/registration that would otherwise collide | no — every tracked block (`VerifyBench`'s five programs and rungs G1–G6) is a singleton (`scratch/round7/C-fixes.md` §10(3): 63 blocks, 63 singletons), on which a one-element list's `Nodup` holds unconditionally, so the guard cannot fire; not re-measured by rebuilding `VerifyBench` here, which sits outside this task's shipping-closure build scope | `test/fixes/F-UNSAFEREC.lean` | `EraserAsks.block_keys_distinct` (`ErasureSpec.lean:385-395`) states an *unconditional* fact about `getDeclInfo?`'s mapped keys; the guard does not make that true, it makes the *run* fail on a violating block, so retiring the field means restating distinctness as a conclusion of a successful run and rewiring its consumers (`VisitExprRefines/Step/Env.lean`, `ErasureRun.lean`, `ColdStartRun.lean`, `Bridge.lean`'s `BlockKeyed.nms.Nodup` conjunct) rather than deleting it outright |
| F-KERNAME | `fix(F-KERNAME)` | `LeanToLambdaBox/Erasure.lean`: new `checkKernameFresh`, called from `addAxiom` and from the two `toKername`-minting registration points in `visitMutual` (the nonrecursive single-declaration branch and the mutual-fixpoint registration loop) | `toKername` collapses `.num p k`/`.str p k.repr` to one key, and `cleanIdent`'s escape has fixed points, so two distinct Lean names can mint the same λbox key; the second `gdecls.cons`/`constants.insert` silently overwrote the first entry, no error, exit 0, and the printer emitted whichever declaration was registered last | `checkKernameFresh` scans the already-registered `constants` for an entry at the same kername under a different name and `throwError`s naming both, before the insert that would otherwise collide; the key encoding itself (`toKername`, `cleanIdent`) is unchanged | no — the refuse variant changes no bytes on any input that does not collide; the finding's own census over the whole elaboration environment (228,987 constants, 228,987 distinct keys, 0 collisions) found no live instance, so no tracked program exercises the new check | `test/fixes/F-KERNAME.lean` | `Supported.kernameSepB`/`SupportError.kernameCollision` (`Supported.lean:241-245`) and `Bridge.BlockKeyed`'s fourth conjunct (`Bridge.lean:164-171`) already state kername separation as a restriction over the tabled names rather than assume it holds generally; the guard changes nothing about that — it makes the *run* enforce the restriction the fragment already states, rather than leaving a silent collision unchecked. `toKername_not_injective` (`VisitExprRefines/Step/Env.lean:740`) stays true and is not touched |
| F-DEPTH | `fix(F-DEPTH)` | `LeanToLambdaBox/Relevance.lean`: `isArityCheck` | The loop's fuel was `ty.approxDepth.toNat + 1`, an 8-bit field that saturates at 256 whatever the *reduced* telescope's real depth, and is 0 (fuel 1) at any definitional alias whatever telescope it unfolds to; a ≥ 256-binder telescope or an `@[irreducible]` alias hiding one threw before reaching the closing `.sort`, so `Erasure.isErasable` fell back to `isErasableMeta`, which does not unfold such an alias either and answered `false` — an inductive **type former** judged relevant | The fuel is a fixed constant (100000), independent of the unreduced subject's syntactic depth, so both shapes decide inside the kernel instead of throwing; `isArityCheck.loop` and its call sites are unchanged, and the single `isArityCheck.loop <fuel> ty` call shape is preserved (the constant-fuel variant, not iterative deepening, per C-refute C3) | no — none of the five tracked programs' type formers reach an `@[irreducible]` alias or a ≥ 256-binder telescope (`Nat`/`Bool`/`List`/`Option`/`Prod`/`Tree`-shaped, depth ≤ 4); not re-measured by rebuilding `VerifyBench` here, which sits outside this task's shipping-closure build scope | `test/fixes/F-DEPTH.lean` | `EraserAsks.kernel_ind_head_true` (`ErasureSpec.lean:374-384`) names this row as its refutation (a telescope of ≥ 256 binders or an alias); the fix removes both counterexamples this round demonstrated but does not retire the field by itself — its statement still needs restating (C-refute C2/C4: e.g. as the disjunction "the kernel run answers `true` or raises the fuel error", not a side condition that only excludes the counterexample) since no syntactic bound on the unreduced subject bounds the reduced telescope. `isArityCheck.loop.WF`/`isArityCheck.WF` (`RelevanceCheck.lean:104-137`) are untouched — proved `∀ fuel`, so they hold at the new constant with no proof change |
| F-ETA2 | `fix(F-ETA2)` | `LeanToLambdaBox/Erasure.lean`: `visitCtorEtaGo`, `visitCasesEtaGo`; new `etaArgIsValue` and `withEtaPrefixLets` (a CPS helper outside the mutual block) with its `@[partial_fixpoint_monotone]` lemma `withEtaPrefixLets_mono` | Both loops pushed the fresh variables onto the argument array and erased the whole application at the bottom, so the arguments the call site had already supplied were emitted **under** the binders the loop opened: `λ x⃗. C ⟦a⃗⟧ x⃗`, which weak evaluation re-runs on every application where the source runs it once. Measured at HEAD: `@List.cons Nat (slowSum 12)` erased to `λ. ((C₁ □) (slowSum 12)) #0` and `Nat.casesOn _ (slowSum 12) 0` to `λ. case (slowSum 12) […]` | Each supplied argument that is neither already a variable nor erased to `□` (both are values, so placing them under the binders duplicates nothing) is erased once, in the outer context, and bound by a `let` outside the binders; the loop then opens its binders with that variable in the argument's place — `let a₁ := ⟦a₁⟧; … λ x⃗. C a₁ … x⃗`. Only the outermost round binds anything: every argument the recursion adds is a variable. In the eliminator loop the candidates start at `casesInfo.discrPos`, since `visitCases` reads the major premise and the alternatives and drops what precedes them — binding a dropped index would evaluate an argument the emitted program does not. Measured: `let(slowSum 12). λ. ((C₁ □) #1) #0` and `let(slowSum 12). let(0). λ. case #2 […]`, both `peregrine validate`-clean and evaluating to the same values as before. The deletion the section proposes is *not* taken (C-refute: a short constructor block is ill-formed and stuck after `constructors_as_blocks`), and no mutual member was added or removed | no wherever no occurrence is under-applied — the new code sits in the `args.size < arity` branch alone, and the four other `test/fixes` programs (`pick`, `quicksort`, `plain`, `even`) re-emit byte-identical `.ast` across the edit; `doc/coverage.md` reports `SupportError.underAppliedCtor`/`.underAppliedElim` 0 times over thirteen tables, so no tracked program reaches the branch. Where it does fire, the term gains one `tLetIn` per bound argument (`expanded_tLetIn`, `EEtaExpandedFix.v:38`, preserves expandedness, so the consumer's η conditions are unaffected) | `test/fixes/F-ETA2.lean` | The fix does **not** lift N19: a `let`-prefixed η-expansion still has no `Lower` arm (the `ctorEta`/`elimEta` arms were deleted at A21), so this is a shipping-soundness fix and `Supported.lean:70-77`/`doc/coverage.md` keep the restriction — but `doc/coverage.md`'s N19 paragraph must drop the claim that the constructor half disappears once this row is repaired, which C-refute refutes. The *bodies* of `visitCtorEtaGo`/`visitCasesEtaGo` changed while their signatures did not, so the mirroring `Stepᵢ` bodies in `VisitExprRefines/Step/Mechanical.lean` and `Step/Passes.lean` must be re-proved; the motive count stays 18, since `withEtaPrefixLets` is a helper beside the block and not a member of it, leaving the `partial_fixpoint` arity unchanged |
| F-ACC | `fix(F-ACC)` | `LeanToLambdaBox/Erasure.lean`: `visitCases`; new `arityResultSort`, `isPropositionalArity` and `firstNonProofField` (helpers beside the mutual block) | An elimination of a propositional inductive whose constructor binds a non-proof field was erased to a `.case` binding that field. Lean admits large elimination for such a `Prop` when the field is recovered from the result indices, and `Acc.casesOn` does bind `Acc.intro`'s `x : α`; the downstream collapse (`remove_match_on_box`, `EOptimizePropDiscr.v:48`, and `eval_iota_sing`, `EWcbvEval.v:162`) substitutes `□` for **every** binder of the surviving alternative, so it boxes that data. Today the collapse never fires — every emitted inductive is declared non-propositional (F-PROP) — and the program is merely stuck; the moment the flag is set the same program computes a wrong value under no error | `visitCases` `throwError`s before emitting, naming the inductive, the constructor and the field's index. The criterion is the shape, not the name: `isPropositionalArity` is MetaRocq's own recipe (`destArity` on the declared arity, then `Sort.is_propositional`, `Extract.v:276`) and the fields are classified by `Meta.isProof` under the `forallBoundedTelescope` `register_inductive` already opens, so an `Acc` clone is refused as `Acc` is. `And`, `Iff`, `Eq`, `Or` and `False` are still erased: their fields are all proofs, which the collapse boxes soundly | no — the edit adds a refusal and no emission path; the finding's own measure (`grep -c 'Acc\|WellFounded\|Quot' VerifyBench/ast/*.ast` = 0 on all five) says no tracked program reaches it, and the six `.ast` the other `test/fixes` programs emit (`pick`, `quicksort`, `plain`, `even`, `cons`, `elim`) are byte-identical across the edit, measured by re-emitting them against the stashed pre-fix build | `test/fixes/F-ACC.lean` | The restriction `Supported.propElimIntoData` (`Supported.lean:65-69`, checked at `supportedHead:321`/`supportedGo:355` via `informativeB`) is **not** lifted — the guard makes the shipping code enforce a *subset* of it (C-refute C11: `propElimIntoData` refuses every non-informative inductive, the guard only one with a non-proof field; `Acc` is in both), so `doc/coverage.md`'s row stands. Nothing in `Erases`, `Lower`, `SEval` or the capstone changes. The *body* of `visitCases` changed while its signature did not, so the mirroring `VisitExprRefines` step body must be re-proved; no mutual member was added or removed, since the three helpers sit beside the block, leaving the `partial_fixpoint` arity unchanged. The full treatment — substituting the recursor's own index argument for an index-determined field, i.e. a Lean-specific `iota_sing_idx` in `SEval`/`Erases`/`Lower`/`erases_correct` — stays blocked on lean4lean's `Injectivity.lean` sorries |
| F-PROP | `fix(F-PROP)` | `LeanToLambdaBox/Erasure.lean`: `register_inductive`; `LeanToLambdaBox/Basic.lean`: `OneInductiveBody.propositional` loses its default | `OneInductiveBody.propositional` was never supplied, so the `false` default — carrying the author's own hedge — was emitted for every inductive, `Prop` ones included (71/71 `false` over the five programs). `erases_mutual_inductive_body` (`Extract.v:276`) states the field as an *equality* with `isPropositionalArity` of the source arity, so `false` is as wrong as `true` in the other direction; and since `remove_match_on_box` (`EOptimizePropDiscr.v:48`) and `eval_iota_sing` (`EWcbvEval.v:162`) are the only rules that eliminate a boxed discriminee, an elimination of a `Prop` into data shipped **stuck**: `peregrine eval` answers `Case: <15> branch not found` on the `And` and `Eq` programs of `test/fixes/F-PROP.lean` | `register_inductive` sets the field by MetaRocq's own recipe — `arityResultSort` is `destArity` (syntactic, no reduction) and `isPropositionalArity` is `Sort.is_propositional` on the sort it ends in, taken as `Level.isAlwaysZero` so that a `Prop` reached through `max`/`imax` counts. The default is removed, so the field can no longer be forgotten. `kelim` is untouched (C-refute C9: `ind_kelim` is carried through `EReorderCstrs`/`EUnboxing` and printed, but no MetaRocq or peregrine pass reads it to decide anything), and its docstring now says so. Measured: the `And` and `Eq` programs evaluate to 5 and 3 where they were stuck, under a `.ast` peregrine `validate` accepts as before | yes, one byte per propositional inductive and only there — `one_inductive_body "And" false` → `… true` (2371 → 2370 bytes on `prop-and.ast`, 2970 → 2969 on `prop-eq.ast`). The 23 inductive names the five benchmark programs emit (`Add … Tree`) are all data, so their flag stays `false`; measured directly on the six `.ast` the other `test/fixes` programs emit (`pick`, `quicksort`, `plain`, `even`, `cons`, `elim`) plus `data.ast`, all byte-identical across the edit | `test/fixes/F-PROP.lean` | The flag is read by `isPropositionalInductive` (`Semantics/Env.lean:20-27`) and thence by `WcbvEval.iota`/`iota_block`/`proj` (`= false` premises), `iota_sing`/`proj_prop` (`= true`) and `LBOptimize` (`Optimize.lean:41,60`). Inside the fragment nothing changes: `Supported.informativeB` is `resultSort … |>.isNeverZero`, which no inductive satisfying the new flag can satisfy, so every inductive an elimination site admits keeps `propositional = false`. That argument covers eliminations and projections only, not inductives registered from a *constructor* occurrence (C-refute C10), for which the missing step is that a `Prop`'s constructor occurrence is erasable and never reaches `visitConstructor` — a fact about the relevance oracle. Five comments asserting "the erasure marks no inductive propositional" (`Semantics/Flags.lean:24-30`, `ElimBody.lean:87-89`, `Erasability.lean:280`, `Supported.lean:66`, `:562`) become false as stated and must be restated over the fragment or as a per-rung measurement. `Supported.propElimIntoData` is **not** lifted: that needs the singleton-elimination theory (F-ACC's full treatment), not the flag. `register_inductive`'s body changed, so the `VisitExprRefines` step body mirroring it must be re-proved, and every construction of `OneInductiveBody` in the verification must now supply the field |
| F-QUOT | `fix(F-QUOT)` | `LeanToLambdaBox/Erasure.lean`: the `ci.value? = .none` arm of `visitMutual`; new `addRealizer`, `mkAnonLambdas` and `quotRealizer` (helpers beside the mutual block) | Lean's quotient primitives have no value, so all four took the body-less-axiom arm. A program using `Quot.mk`/`Quot.lift` erased to one that applies two axioms: `peregrine validate` accepts it and `peregrine eval` refuses to compile it — `Axioms found, use Extract Constant to realize them in C: .Quot.lift, .Quot.mk` | The arm keys on `ConstantInfo.quotInfo` and registers the realizer `quotRealizer` gives its `QuotKind`, at the arity the kernel fixes: `Quot.mk` (3) is `λ _ _ x. x`, `Quot.lift` (6) is `λ _ _ _ f _ q. f q`, and `Quot`/`Quot.ind` — a type former and a proof, both erased at every use site — get `□`. `Quot.sound` is an `axiomInfo`, not a `quotInfo` (C-refute), so it is untouched and stays body-less; it is proof-valued, so no use site reaches it. Anything else with no value still takes the axiom arm. Measured: `test/fixes/F-QUOT.lean` goes from two body-less constants and a refused compile to none and `6` | yes, on any program reaching a quotient primitive: two `(constant_body None)` become bodies. None of the five benchmark programs or the other `test/fixes` programs reaches one — `grep -c Quot` is 0 on all five (`F-QUOT`'s own row in this file), and the suite is byte-identical across the edit | `test/fixes/F-QUOT.lean` | `Supported.quotPrim` (`Supported.lean:55`, checked at `supportedHead:313`) is **not** lifted: the fragment still refuses a quotient primitive in a computationally relevant position, and lifting it needs `SEval`/`Erases`/`Lower` arms for `Quot.lift`'s β-like reduction and quotient constants in lean4lean's model. What does change is the *run*: `visitMutual`'s `.none` arm gains a fourth registering exit, so `run_visitMutual_decomp`'s three-disjunct decomposition (`ColdStartRun.lean:376-386`), the `ax` field of the cold-start induction principles (`ColdStartInduction.lean:280-284`, `:114`) and `RegInvShape'.addAxiom` (`ColdStartShape.lean:215`) need an `addRealizer` case — `addRealizerState` registers `(toKername n, .constantDecl ⟨some t⟩)` where `addAxiomState` registers `⟨none⟩`, so the shape lemmas carry over with `DefnDecl` in place of the body-less entry. `visitMutual`'s body changed, so the `VisitExprRefines` step body mirroring it must be re-proved |
| F-EQREC | `fix(F-EQREC)` | `LeanToLambdaBox/Erasure.lean`: the same `ci.value? = .none` arm of `visitMutual`; new `recursorRealizer` (beside `register_inductive`, which it calls) | A recursor has no compiler value, so every recursor reached as a constant was emitted body-less and then applied. `Fannkuch` ships one, `((MPdot (MPfile ()) "Eq") "rec")`; `peregrine validate` accepts the file and `peregrine eval` refuses to compile it — `Axioms found, use Extract Constant to realize them in C: .Eq.rec` — so the benchmarks only ran because they hand peregrine an `eq_rec_c.attr`/`eq_rec_ml.attr` the frontend does not emit | The arm synthesizes the body MetaRocq gets for free (Rocq's `eq_rect` is an ordinary constant whose body is a `match` on a propositional singleton, which `remove_match_on_box` collapses): at the recursor's calling convention — parameters, motives, minors, indices, major premise — `λ…. case (I, nparams) (bvar 0) [alt]`, the alternative binding the constructor's kept fields and handing the single minor every field, an erased one as `□`. The shape is read off the `RecursorVal` and the inductive it names, never off the constant's name: a single non-recursive `Prop` (F-PROP's `isPropositionalArity`) with at most one constructor, all of whose fields are proofs (F-ACC's `firstNonProofField`). `Eq.rec` gets `λ _ _ _ _ _ _. case (Eq,2) (bvar 0) [([], bvar 2)]`, which agrees with the benchmarks' hand-written `fun _ _ _ x _ _ => x`; `And.rec` gets the same shape with two field binders and `bvar 3 (bvar 1) (bvar 0)`, which the collapse substitutes `□` for; `False.rec` a `case` with no alternative. Every other recursor — `Nat.rec`, `Acc.rec`, `Or.rec`, `Exists.rec` — keeps today's body-less emission. Measured: `test/fixes/F-EQREC.lean`'s three programs go from one body-less constant each and a refused compile to none and `9`, `4`, `2`; `runBenchmark 5` of `VerifyBench/Src/Fannkuch.lean`, erased closed, goes from the same refusal to `7`, which is what Lean computes, with no `.attr` | yes — `Fannkuch` only (38653 → 38968 bytes: it gains the `Eq` inductive block and `Eq.rec`'s body and loses its one `(constant_body None)`). `Sieve` is byte-identical, and `Arith`, `BinaryTrees`, `Quicksort` and rungs G1–G8 emit no body-less constant at all (`grep -c '(constant_body None)'` = 0), so the arm never fires on them; the other `test/fixes` programs' expectations are unchanged | `test/fixes/F-EQREC.lean` | `NoBodylessRefs` — the capstone's own decidable premise, false on `Fannkuch` (`doc/coverage.md:60-66`) — becomes true there. `SupportError.recursorHead` (N21) is **not** lifted: `Supported.supportedHead`'s `isRecursorName` arm (`Supported.lean:331`) rejects a recursor head because recursors are tabled body-less, so a program reaching one is vacuously covered; lifting it needs an `SEval` ι rule for Lean recursors, an `Erases`/`Lower` arm at the synthesized body and an `erases_correct` case (`doc/rework/probes/Q2-subsingleton.md` §2's L7 plus `SubsingletonElim`), which inherits lean4lean's `VEnv.WF'.consts_origin` ask. As with F-QUOT, `visitMutual`'s `.none` arm now has a further registering exit, so `run_visitMutual_decomp` (`ColdStartRun.lean:376-386`), the `ax` field of the cold-start induction principles and `RegInvShape'.addAxiom` need the `addRealizer` case; the body registered there is a `.case` over an inductive `register_inductive` has just registered, so the registry invariant sees the two writes in that order |

## Reported, not fixed

The repository's standing rule is *raise implementation issues, do not silently patch
them*. Each section below is a defect in `LeanToLambdaBox/{Erasure,Basic}.lean` that the
verification found, specified with the site, the command that measures it, and that
command's output. No wave depends on any of them landing, and no unit applies one.

Ordered as the design orders them (`doc/rework/01-DESIGN.md` §8.2): **F-PROP** first, because
three other rows are downstream of it. The last three rows — **F-DEPTH**, **F-UNSAFEREC**,
**F-KERNAME** — are `doc/rework/06-REPAIRS-W4.md` §3's findings, in the order that document
raises them; each bounds one class-**C** field of `EraserAsks`.

Every command below runs from the repository root. The `.ast` files are the five csimp-off
duplicates under `VerifyBench/ast/`, regenerated with `lake build VerifyBench`.

### F-PROP — every emitted inductive is declared non-propositional

*Site.* `register_inductive`, `LeanToLambdaBox/Erasure.lean:192-241`; the field's default,
`LeanToLambdaBox/Basic.lean:164`.

*Defect.* `OneInductiveBody.propositional` is never set. The `false` default carries the
author's own hedge ("I think, since erasure should remove anything which ends up in Prop"),
so every emitted inductive — including `Prop` ones — is declared non-propositional.
`isPropositionalInductive` is then identically `false` downstream: an emitted `.case` on a
`□` discriminee is **stuck** at every flag point, and peregrine's verified
`remove_match_on_box` (`EOptimizePropDiscr.v:35,57`) skips it.

*Measure.*

    grep -o 'one_inductive_body "[^"]*" [a-z]*' VerifyBench/ast/*.ast | sed 's/.* //' \
      | sort | uniq -c

    71 false

*Proposed edit.* Set the field from the source sort (`Meta.isProp` on the type former).

*Consequence until it lands.* `And`/`Iff`/`Acc` eliminations into data ship as stuck terms,
which is why the fragment excludes them (`Supported.propElimIntoData`).

*Fixed* on `dev/fix` by `fix(F-PROP)`, after `fix(F-ACC)` — see the shipping-edits table.
`register_inductive` reads the flag off the declared arity, by MetaRocq's own recipe, and the
`false` default is gone, so the field must be supplied. `kelim` is left as it was: no pass in
MetaRocq's erasure pipeline or in peregrine reads it (C-refute C9). Measured: an `And`
elimination into data went from `Case: <15> branch not found` under `peregrine eval` to the
value it computes. `Supported.propElimIntoData` stays — lifting it needs the
singleton-elimination theory, not the flag — but five comments stating "the erasure marks no
inductive propositional" (`Semantics/Flags.lean:24-30`, `ElimBody.lean:87-89`,
`Erasability.lean:280`, `Supported.lean:66` and `:562`) are falsified as stated and must be
restated over the fragment, or as a per-rung measurement.

### F-ETA — every emitted recursive body is a bare unapplied `.fix`

*Site.* `visitMutual`, `LeanToLambdaBox/Erasure.lean:859-919`; the eraser's own TODO sits at
`:911`.

*Defect.* The emitted body of a recursive declaration is `.fix defs i` with no λ-headedness
check — `nonrecursive := single_decl && !name_occurs …` (`:885`) is the only guard — so
MetaRocq's `EEtaExpandedFix.expanded_eprogram` is **false on all five programs**. That
predicate is not paperwork: `guarded_to_unguarded_fix` (`ETransform.v:666-682`) is the
identity on terms and its whole evaluation-preservation obligation is discharged from it, so
with the predicate false no verified semantics-preservation argument covers this frontend's
output past the target-side `WcbvEval`. peregrine's own discharge is `Admitted`
(`Transforms.v:375`) and `peregrine validate` checks no η, so nothing downstream detects it.

*Measure.*

    grep -o '(constant_body (Some (tFix' VerifyBench/ast/*.ast | sed 's/:.*//' | sort | uniq -c
    grep -o '(tFix' VerifyBench/ast/*.ast | wc -l

     4 VerifyBench/ast/Arith.ast
    10 VerifyBench/ast/BinaryTrees.ast
    15 VerifyBench/ast/Fannkuch.ast
    11 VerifyBench/ast/Quicksort.ast
    10 VerifyBench/ast/Sieve.ast
    50

50 `tFix` nodes, 50 of them the whole body of a constant: no emitted fixpoint is applied.

*Proposed edit.* Wrap the emitted body in `rarg+1` lambdas applied to their own binders —
the TODO at `:911`. Adequate here: all 50 `FixDef`s have `principalArgIdx = 0` and every
self-call is applied. Rocq avoids the problem by η-expanding before erasure
(`Template/EtaExpand`).

*Status in the verification.* The capstone's conclusion states `LBWfPeregrine`, which
deliberately does **not** claim fixpoint η; the stronger `PeregrinePre` is defined and *not*
concluded, and the difference is exactly this row.

### F-ETA2 — the η path re-erases supplied arguments, and constructors do not need it

*Site.* `visitCtorEtaGo`, `LeanToLambdaBox/Erasure.lean:722-728`; `visitCasesEtaGo`,
`:705-712`.

*Defect, two halves.*

First, both loops recurse with `args.push (.fvar fvarid)` **inside** `forallMonocular`'s
scope and only then call `visitConstructor`/`visitCases`. The arguments the call site already
supplied are therefore erased again under every new binder, and `mkLambda` abstracts them
back out: the eraser pays one erasure of the whole supplied prefix per missing argument, and
the emitted term is `λ x₁ … xₙ. C a₁ … aₖ x₁ … xₙ` where `C a₁ … aₖ` would do.

Second, and independently: **applied-form λ□ needs no constructor η at all.** At
`with_constructor_as_block = false`, which is what `eraseFlags` sets
(`LeanToLambdaBox/Semantics/Flags.lean:44`), a partially applied constructor spine is already
a value — `Value.construct_app_val` (`LeanToLambdaBox/Semantics/Values.lean:104`) builds
`mkApps (.construct iid c []) args` as a value for every `args.length < ar`, and
`WcbvEval.construct_app` (`LeanToLambdaBox/Semantics/Eval.lean:130-136`) is the rule that
reaches it. So `visitCtorEta`'s whole saturation loop buys nothing that the target semantics
does not already give, and it is the only reason an under-applied constructor occurrence is
not a plain spine.

*Measure.* Every emitted `tConstruct` node carries an empty argument list, so applied form is
what the eraser already emits everywhere:

    python3 - <<'EOF'
    import glob, re
    def nodes(s):
        out = []
        for m in re.finditer(r'\(tConstruct\b', s):
            i = m.start(); d = 0; j = i
            while True:
                if s[j] == '(': d += 1
                elif s[j] == ')':
                    d -= 1
                    if d == 0: break
                j += 1
            out.append(s[i:j+1])
        return out
    tot = empty = 0
    for f in sorted(glob.glob('VerifyBench/ast/*.ast')):
        ns = nodes(open(f).read())
        e = sum(1 for n in ns if n.rstrip()[:-1].rstrip().endswith('()'))
        print(f, len(ns), e); tot += len(ns); empty += e
    print('total', tot, 'empty-arg', empty)
    EOF

    VerifyBench/ast/Arith.ast 42 42
    VerifyBench/ast/BinaryTrees.ast 84 84
    VerifyBench/ast/Fannkuch.ast 101 101
    VerifyBench/ast/Quicksort.ast 697 697
    VerifyBench/ast/Sieve.ast 58 58
    total 982 empty-arg 982

*Proposed edit.* Delete `visitCtorEta`/`visitCtorEtaGo` and dispatch `visitConstructor`
directly at every arity. For `visitCasesEta` the loop is not removable — a `.case` node needs
its discriminant — but the recursion should erase the supplied prefix once, outside
`forallMonocular`, and reuse the result.

*Status in the verification.* `Lower` has no `ctorEta` and no `elimEta` arm: both are
compositional, so an η-expanded head still composes under `app` into
`mkApps (mkLambdas ns body) args'`, a β-redex target with no bound on nesting that every
spine-inverting arm of the simulation would have to collapse. What they covered is the
coverage restriction **N19** — no under-applied constructor or eliminator occurrence — which
`supportedB` decides per program. For constructors N19 costs nothing once this row is
repaired; for eliminators it is a real restriction, and `doc/coverage.md` carries the
per-program verdict.

*Fixed, first half only,* on `dev/fix` by `fix(F-ETA2)` — see the shipping-edits table. Both
loops now erase each supplied argument that is neither a variable nor a `□` once, in the outer
context, and `let`-bind it outside the binders they open (the eliminator loop from the major
premise on, since `visitCases` drops what precedes it). The second half is **refuted**: a
constructor η loop that only saturates *is* needed, because peregrine's
`constructors_as_blocks` rewrites an under-applied `tConstruct` spine into a short block, which
`EWellformed.v:171-175` rejects (`(p + a) == #|block_args|`) and `eval_construct_block` gets
stuck on. `visitCtorEta` is therefore kept, and the two sentences above that say constructors
need no η — the *Proposed edit*'s "delete `visitCtorEta`/`visitCtorEtaGo`" and "for
constructors N19 costs nothing once this row is repaired" — are wrong; `doc/coverage.md`'s N19
paragraph carries the same claim and needs the same correction (verification-side, after the
merge). N19 itself stands: a `let`-prefixed η-expansion has no `Lower` arm either.

### F-SPARSE — a sparse `casesOn` panics and writes a wrong program

*Site.* `visitCases`, `LeanToLambdaBox/Erasure.lean:770` (the name-based recovery) and
`:817` (the panic).

*Defect.* The inductive is recovered as `casesInfo.declName.getPrefix`. Since Lean v4.26,
`getCasesInfo?` also recognises sparse `casesOn` auxiliaries (`…_sparseCasesOn_1`), whose
prefix is the *enclosing function*, not the inductive. `getConstInfo` then fails the
`.inductInfo` pattern and the `unreachable!` fires — which, at `EraseM`, returns `.box` and
lets the run continue, exit `0`, and write an `.ast` that `peregrine validate` accepts.

*Measure.*

    lake env lean VerifyBench/Quicksort.lean > qs.log 2>&1 ; echo "exit $?" ; grep -m1 PANIC qs.log

    exit 0
    PANIC at Erasure.visitCases LeanToLambdaBox.Erasure:817:55: unreachable code has been reached

The run writes `VerifyBench/ast/Quicksort.ast` regardless. `Quicksort` is the one of the five
programs that hits it, through `quicksort_fuel`.

*Proposed edit.* Recover the inductive from `CasesInfo` rather than from the name, and
handle `CasesAltInfo.default`.

*Status in the verification.* Visible as `SupportError.sparseCasesOn`, the value
`supportedB` returns on this program, and as a named row in `doc/coverage.md`.

*Fixed* on `dev/fix` by `fix(F-SPARSE)` — see the shipping-edits table. The inductive comes
from `casesInfo.indName` and the catch-all is expanded into one alternative per uncovered
constructor; every shape that cannot be compiled soundly now throws. The fragment is
unchanged: `supportedHead` still refuses a sparse head, so `SupportError.sparseCasesOn` and
the `doc/coverage.md` row stand.

### F-ACC — a `Prop`-valued inductive with an index-determined field

*Site.* `visitCases`, `LeanToLambdaBox/Erasure.lean:768-835`, at an `Acc`-shaped inductive.

*Defect.* A consequence of F-PROP with a second stage. *Today* the emitted `.case` is stuck
at the environment (F-PROP). *If F-PROP alone is fixed*, `Acc`-shaped inductives then reduce
by `iota_sing`/`remove_match_on_box`, which box a field that is **data** — `Acc.intro`'s
`x : α`, measured as `largeElimClause ``Acc = some (2,[1])` — and compute a wrong program.

*Measure.*

    grep -c 'Acc\|WellFounded\|Quot' VerifyBench/ast/*.ast | sort

    VerifyBench/ast/Arith.ast:0
    VerifyBench/ast/BinaryTrees.ast:0
    VerifyBench/ast/Fannkuch.ast:0
    VerifyBench/ast/Quicksort.ast:0
    VerifyBench/ast/Sieve.ast:0

Latent: no benchmark reaches it.

*Proposed edit.* Any F-PROP fix must keep index-determined-field eliminations refused. The
refusal has to be **shape**-keyed, not name-keyed: `Acc.casesOn` does compile in Lean, so
refusing the name would not close the hole.

*Fixed* on `dev/fix` by `fix(F-ACC)`, before `fix(F-PROP)` — see the shipping-edits table.
`visitCases` refuses a propositional inductive one of whose constructor fields is not a
proof, decided by `Meta.isProof` on the fields of every constructor, so `Acc` and any
`Acc`-shaped user inductive throw while `And`, `Iff`, `Eq`, `Or` and `False` are still
erased. The fragment is unchanged: `Supported.propElimIntoData` refuses strictly more (every
non-informative inductive), and the shipping guard now enforces a subset of it.

### F-QUOT and F-EQREC — body-less constants the consumer cannot realise

*Site.* `LeanToLambdaBox/Erasure.lean:873-876`, the `ci.value? = .none` arm of the
single-declaration branch.

*Defect.* A constant with no compiler value is emitted as a body-less axiom. Two families
reach it: `Quot` primitives (F-QUOT), and recursors reached as constants (F-EQREC) — `Eq.rec`
is emitted body-less in `Fannkuch`. The program is then stuck there unless peregrine's
`.attr`/`.ast.inlinings` channel supplies a realizer, which this frontend does not emit, and
`peregrine validate` still accepts the file.

*Measure.*

    grep -c '(constant_body None)' VerifyBench/ast/*.ast | sort

    VerifyBench/ast/Arith.ast:0
    VerifyBench/ast/BinaryTrees.ast:0
    VerifyBench/ast/Fannkuch.ast:1
    VerifyBench/ast/Quicksort.ast:0
    VerifyBench/ast/Sieve.ast:0

The one body-less declaration is `((MPdot (MPfile ()) "Eq") "rec")`, and `Fannkuch.ast`
applies it.

*Proposed edit.* Emit a realizer, or refuse. For `Eq.rec` the natural channel is the
remapping the backends already take (`.ast.inlinings`/`.attr`); someone must decide whether
the frontend should emit it.

*Status in the verification.* `Quot` in a computationally relevant position is outside the
fragment (`Supported.quotPrim`). `Eq.rec` is covered by an `AxiomRealizer` row — a class-**E**
assumption that the consumer supplies the realizer — and `Fannkuch`'s coverage row records
that its `hax` is false without one.

*F-QUOT fixed* on `dev/fix` by `fix(F-QUOT)` — see the shipping-edits table. The arm keys on
`ConstantInfo.quotInfo`, Lean's own classification rather than a name table, and registers
the realizer of that `QuotKind`: `Quot.mk` the identity on the representative, `Quot.lift`
the application of the lifted function to it, `Quot`/`Quot.ind` the `□` of an erased
constant. `Supported.quotPrim` is unchanged — the fragment still refuses these primitives.

*F-EQREC fixed* on `dev/fix` by `fix(F-EQREC)` — see the shipping-edits table. The recursor
of a single non-recursive `Prop` with at most one constructor, all of whose fields are
proofs, is given the `case` body MetaRocq's `eq_rect` has and `remove_match_on_box`
collapses; the shape is read off the `RecursorVal`, so `Eq.rec` is not named anywhere.
`Fannkuch` loses its one `(constant_body None)` and stops needing
`eq_rec_c.attr`/`eq_rec_ml.attr`. Recursors outside that shape — `Nat.rec`, `Acc.rec`,
`Or.rec`, `Exists.rec` — are unchanged, so the proposal's `.attr`/`.ast.inlinings` channel
is still the open product decision for them.

### F-PRODUCT — an unverified product feature added on the verification branch

*Site.* `auto_inline_typeclass_dispatch` and its helpers: the config flag at
`LeanToLambdaBox/Erasure.lean:85`, `LBTerm.stripLambdas`/`containsFix`/`isTrivialAlias` at
`:88-118`, and the dispatch at `:896-903`.

*Defect.* Not a miscompile: a product feature that rode in on the verification branch, so
"what the verification changed" is not a clean diff. It is off by default and the
verification never depends on it.

*Measure.*

    grep -n 'auto_inline_typeclass_dispatch' LeanToLambdaBox/Erasure.lean

    85:  auto_inline_typeclass_dispatch: Bool := false
    896:      if (← read).config.auto_inline_typeclass_dispatch && !leanInline && !t.containsFix then

*Proposed edit.* Re-home the feature through `dev/fix` (or `main`), so the verification diff
touches only verification files.

*Status in the verification.* The `.ast.inlinings` channel it drives is a class-**E** row in
`doc/trust.md`; nothing in the theorem stack mentions it.

### F-DEPTH — the relevance oracle's arity check has an 8-bit fuel

*Site.* `isArityCheck`, `LeanToLambdaBox/Relevance.lean:46`, whose fuel is
`ty.approxDepth.toNat + 1`; the loop it feeds is at `:32`.

*Defect.* `Lean.Expr.Data.approxDepth` is eight bits, so the fuel saturates at 256 however deep
the type is, and it is **1** at a definitional alias, whose `approxDepth` is 0. `isArityCheck`
then throws, `Erasure.isErasable` (`LeanToLambdaBox/Erasure.lean:177`) takes its `.error` arm,
and the verdict is the unverified `Erasure.isErasableMeta`'s — which will not unfold an
`@[irreducible]` alias either, so it answers `false`. The oracle therefore answers `false` at an
inductive **type former**, the one shape the erasure must not treat as data.

*Measure.*

    cat > /tmp/f-depth.lean <<'EOF'
    import LeanToLambdaBox.Relevance
    import LeanToLambdaBox.Erasure
    open Lean

    def tele : Nat → Expr
      | 0     => .sort .zero
      | n + 1 => .forallE `x (.sort .zero) (tele n) .default

    def DeepArity : Type 1 := Nat → Nat → Nat → Nat → Type
    inductive Bar : DeepArity
    attribute [irreducible] DeepArity

    #eval show CoreM Unit from do
      for k in [4, 100, 255, 300, 1000] do
        let d := (tele k).approxDepth
        IO.println s!"telescope of {k} binders: approxDepth = {d}, isArityCheck fuel = {d.toNat + 1}"
      let al := mkConst ``DeepArity
      IO.println s!"alias DeepArity:          approxDepth = {al.approxDepth}, isArityCheck fuel = {al.approxDepth.toNat + 1}"
      let env ← getEnv
      match Lean4Lean.TypeChecker.M.run env.toKernelEnv (safety := .safe) (lctx := {}) (lparams := [])
          (x := Lean4Lean.TypeChecker.RecM.run (LeanToLambdaBox.isErasable (mkConst ``Bar))) with
      | .ok b    => IO.println s!"kernel isErasable Bar   = ok {b}"
      | .error _ => IO.println s!"kernel isErasable Bar   = error (routes to isErasableMeta)"

    #eval show MetaM Unit from do
      IO.println s!"isErasableMeta Bar      = {← Erasure.isErasableMeta (mkConst ``Bar)}"
    EOF
    lake env lean /tmp/f-depth.lean

    telescope of 4 binders: approxDepth = 4, isArityCheck fuel = 5
    telescope of 100 binders: approxDepth = 100, isArityCheck fuel = 101
    telescope of 255 binders: approxDepth = 255, isArityCheck fuel = 256
    telescope of 300 binders: approxDepth = 255, isArityCheck fuel = 256
    telescope of 1000 binders: approxDepth = 255, isArityCheck fuel = 256
    alias DeepArity:          approxDepth = 0, isArityCheck fuel = 1
    kernel isErasable Bar   = error (routes to isErasableMeta)
    isErasableMeta Bar      = false

*Proposed edit.* Fuel the loop by the *reduced* telescope's own bound rather than by the
unreduced subject's `approxDepth` — count binders as `whnf` produces them, with a budget that
does not come from an eight-bit field. `LeanToLambdaBox/Relevance.lean` is verification-authored,
so this is in scope for a later wave under plan rule N5's scheduled exception; W4b does not take
it.

*Consequence until it lands.* `EraserAsks.kernel_ind_head_true` — "at an inductive head the pure
kernel run answers `true`" — is false in general, at a telescope of ≥ 256 binders or behind an
`@[irreducible]` alias. It is carried as a class-**C** field with this row as its bound, and
`EraserAsks.oracle_informative`, the type-former exclusion the bridge's constant step consumes,
is exactly as strong as it.

*Fixed* on `dev/fix` by `fix(F-DEPTH)` — see the shipping-edits table. The constant-fuel
variant (`scratch/round7/C-refute.md` C3), not iterative deepening: `isArityCheck.loop.WF` is a
single `loop.WF` reduction that survives replacing the fuel *expression* with any `Nat`, but does
not survive replacing the single `loop` call with a retry-on-`tryCatch` wrapper, for which no
`RecM.WF` lemma exists and whose untyped `.other "isArityCheck: fuel exhausted"` error carries no
discriminant to catch by. `isArityCheck.loop`'s body, its `.WF` proof, and every other call site
are unchanged. `EraserAsks.kernel_ind_head_true` does not retire by this alone (C-refute C2/C4):
the field's statement still needs restating — as the disjunction the code actually realises, or
against a stated budget rather than a side condition that only excludes the two counterexamples
this round measured — which is a later wave's edit, not this one's.

### F-UNSAFEREC — a `mutual unsafe def` block with an `_unsafe_rec` twin is miscompiled

*Site.* `visitMutual`, `LeanToLambdaBox/Erasure.lean:906` (`let fixvarnames := names.map
remove_unsafe_rec`) and `:916-918` (the registration loop); `remove_unsafe_rec` at `:520`.

*Defect.* `Erasure.remove_unsafe_rec` strips one literal `_unsafe_rec` component, so it is not
injective. A `mutual` block holding both `u` and `u._unsafe_rec` is legal Lean, and
`Lean.Compiler.LCNF.getDeclInfo?` reports both members in `ci.all`; the eraser maps that block to
`[u, u]`, builds `fixvarMap [u, u] ids` (whose second binding overwrites the first), names both
`FixDef`s `u`, and registers both declarations at the one kername `u`. The emitted program has
two constants under one key, two identically named fix variables, and both members' recursive
calls bound to whichever the map kept. No error is reported.

*Measure.*

    cat > /tmp/f-unsaferec.lean <<'EOF'
    import LeanToLambdaBox.Erasure
    open Lean LeanToLambdaBox

    mutual
      unsafe def u : Nat → Nat
        | 0 => 0
        | n + 1 => u._unsafe_rec n
      unsafe def u._unsafe_rec : Nat → Nat
        | 0 => 1
        | n + 1 => u n
    end

    def keyStr (k : Kername) : String := toString (repr k)

    #eval show CoreM Unit from do
      let some ci ← Lean.Compiler.LCNF.getDeclInfo? ``u | IO.println "getDeclInfo? u = none"
      let mapped := ci.all.map Erasure.remove_unsafe_rec
      IO.println s!"getDeclInfo? u : all = {ci.all}"
      IO.println s!"mapped by remove_unsafe_rec = {mapped}"
      IO.println s!"distinct keys = {(mapped.map (keyStr <| toKername ·)).eraseDups.length} of {mapped.length}"
      let (p, _) ← Erasure.erase (mkConst ``u) {}
      let keys := p.1.map (keyStr ·.1)
      IO.println s!"emitted declarations = {keys.length}, distinct keys = {keys.eraseDups.length}"
      for (kn, d) in p.1 do
        if kn.id == "u" then
          match d with
          | .constantDecl ⟨some (.fix defs i)⟩ =>
              IO.println s!"key u: fix at index {i}, defs named {defs.map (repr ·.name)}"
          | _ => IO.println "key u: not a bare fix"
    EOF
    lake env lean /tmp/f-unsaferec.lean

    Name Unit.unit is marked as inline.
    Name Nat.sub has a value but is tagged @[extern], emitting axiom.
    Name Nat.beq has a value but is tagged @[extern], emitting axiom.
    getDeclInfo? u : all = [u, u._unsafe_rec]
    mapped by remove_unsafe_rec = [u, u]
    distinct keys = 1 of 2
    emitted declarations = 10, distinct keys = 9
    key u: fix at index 1, defs named [BinderName.named "u", BinderName.named "u"]
    key u: fix at index 0, defs named [BinderName.named "u", BinderName.named "u"]

The first three lines are the eraser's own `logInfo` output on this program.

*Proposed edit.* One line after `LeanToLambdaBox/Erasure.lean:906`:

    unless (fixvarnames.map toKername).Nodup do
      throw <| .error .missing s!"mutual block {names} has colliding lambda-box keys"

Refusing is right rather than renaming: the two members are distinct declarations and the λ□
environment has no room for both under one key.

*Consequence until it lands.* `EraserAsks.block_keys_distinct` is a class-**C** field rather than
a fact the run recovers. With the guard the field becomes a consequence of the run's own
conclusion and the field goes.

*Fixed* on `dev/fix` by `fix(F-UNSAFEREC)` — see the shipping-edits table. The guard sits exactly
where proposed, on `fixvarnames.map toKername` rather than on `fixvarnames` itself (the λ□ keys
that would actually collide, robust to `toKername`'s own non-injectivity, F-KERNAME); it uses
`throwError`, matching every other refusal in `visitMutual`'s caller `visitCases`, rather than the
sketch's raw `throw <| .error .missing`. `List.Nodup`'s `Decidable` instance needs `DecidableEq` on
`Kername`, which neither `Kername` nor `ModPath` had, so both gained `deriving DecidableEq` in
`Basic.lean`. Retiring `EraserAsks.block_keys_distinct` is not part of this edit — see the
shipping-edits table's last column.

### F-KERNAME — `toKername` is not injective

*Site.* `toKername`, `LeanToLambdaBox/Basic.lean:35`, through `cleanIdent` at `:24` and the
`.num` arm's `nb.repr`.

*Defect.* `toKername` sends `.num p k` and `.str p k.repr` to one kername, and `cleanIdent`'s
escape has fixed points, so two distinct Lean constants can carry one λ□ key. Registration is a
`gdecls.cons`, so the second such constant shadows the first in the emitted environment and the
program reads whichever the printer emits last. `toKername_not_injective`
(`LeanToLambdaBox/VisitExprRefines/Step/Env.lean:666`) is the witness pair.

*Measure.* The defect is latent rather than live: over the whole elaboration environment of this
repository, no two declared constants collide.

    cat > /tmp/f-kername.lean <<'EOF'
    import LeanToLambdaBox
    open Lean LeanToLambdaBox

    #eval show CoreM Unit from do
      let env ← getEnv
      let mut keys : Std.HashMap String Name := {}
      let mut n := 0
      let mut collisions : Array (Name × Name) := #[]
      for (nm, _) in env.constants.toList do
        if nm != .anonymous then
          n := n + 1
          let k := toString (repr (toKername nm))
          match keys[k]? with
          | some m => collisions := collisions.push (m, nm)
          | none   => keys := keys.insert k nm
      IO.println s!"constants = {n}, distinct keys = {keys.size}, collisions = {collisions.size}"

    example : toKername (.num .anonymous 5) = toKername (.str .anonymous "5") := rfl
    EOF
    lake env lean /tmp/f-kername.lean

    constants = 228987, distinct keys = 228987, collisions = 0

The `example` is the non-injectivity witness and it elaborates by `rfl`; the count is what says
no *declared* pair realises it here.

*Proposed edit.* Make the key injective — carry the `.num`/`.str` distinction and the escape
into the identifier — or refuse a collision at registration, which is the cheaper half and the
one that turns a silent shadowing into an error.

*Consequence until it lands.* The verification excludes colliding inputs rather than assuming
they cannot occur: kername separation over the tabled names is a decidable arm of the fragment
checker, reported as `SupportError.kernameCollision`, and `doc/coverage.md` carries the
restriction row. Nothing in the theorem stack assumes `toKername` injective.

*Fixed* on `dev/fix` by `fix(F-KERNAME)` — see the shipping-edits table. The refuse variant:
`toKername`/`cleanIdent` are unchanged (the key encoding is a byte-level contract with
peregrine, out of scope here), and the new `checkKernameFresh` guards the three sites that mint
a fresh kername from a `Name` — `addAxiom` and `visitMutual`'s two registration points — refusing
when the minted key is already registered under a different Lean name. The injective-key variant
is not taken; `toKername_not_injective` stays true and `Supported.kernameSepB`/
`SupportError.kernameCollision` stand unchanged, now enforced rather than merely stated.
