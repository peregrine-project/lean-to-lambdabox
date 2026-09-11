# 01 — Final design for the Lean → λ□ verification rework

**Status.** Design of record, as amended at the design gate (24 refuter verdicts; every fatal or
major finding resolved in §2.1). It is the synthesis of the three candidate designs
(`doc/rework/designs/{A,B,C}-*.md`) after adversarial review by three judges, and it is
subordinate to `doc/rework/00-REFERENCE-SPEC.md` except where §3.3 below asks that document to be
amended. Every amendment is forced by a measurement, and the measurement is cited.

**Base and grafts.** The skeleton is **design B** (relational λ□→λ□ passes, maximum reuse): two
judges ranked it first, and it is the only one of the three whose `erases_correct` is well-posed
at a recursive constant. Grafted, per the judges' endorsements: from **A** the flag chain, the
eliminator bodies as *constructions* with their ι theorems proved rather than assumed, the
declaration-level `elim` class, the panic table and the upstream-ask file; from **C**
the entire non-vacuity lane (the G-ladder, `Green.lean`, `green-check`), the honest output
predicate (`LBWfPeregrine` without fixpoint η, `PeregrinePre` stated separately), `supportedB :
… → Except SupportError Unit`, the reified `SourceTable`, `lbEval`, and the applied capstone.

**Repairs this document makes that no candidate design contained.** The §2 rows, plus the §2.1
gate resolutions; the machine-checked evidence lives under `scratchpad/probe/` and
`scratchpad/gate/` and is cited row by row.

---

## 1. Overview

### 1.1 Thesis

`Erases` is `[S Fig. 18]` transposed to `Lean.Expr`: ten congruence rules plus one box rule,
indexed by `(env : VEnv, Us : List Name, Δ : VLCtx)` and nothing else. It produces no
`.construct`, no `.case`, no `.fix`. The four Lean-specific compilation steps that the current
relation absorbed leave it, and they leave as **relations between two λ□ terms indexed by the
specification environment `Σ⁺` alone**:

* `Lower Σ⁺ : LBTerm → LBTerm → Prop` — constructor constants become `.construct` heads,
  saturated eliminator applications become `.case` nodes, under-applied heads η-expand, and a
  block member's body or constant becomes the block's `.fix` node;
* `LowerEnv Σ⁺ Σ` — the emitted environment is the lowered, pruned image of the specification's;
* `optimize` — already proved, off the critical path (§3.2).

Each carries `erases_correct`'s shape one layer down:
`R Σ⁺ t t' → WcbvEval Σ⁺ fl t v → ∃ v', R Σ⁺ v v' ∧ WcbvEval Σ fl t' v'`.
T8 concludes membership in the composite `ErasesLB = Erases ⨟ Lower`, and the composite has
**derived introduction lemmas whose signatures are the deleted `Erases` rules**, so seventeen of
the eighteen motives are restated by a rename. The exception is motive 6 (the block branch of
`visitMutual`): there the eraser emits `.fvar id` at a source `.const` position, no factor of
`Erases ⨟ Lower` can state that, and the motive is stated with the explicit third factor
`ErasesLBFix` (§4.5) — genuinely new work, priced in W4, gated by U1.7's stateability test.

One `VEnv` is threaded: **`env`, the kernel environment** (`TrEnv .safe`, via
`ErasureSpec.env_connect`). Compiler bodies (`_unsafe_rec`, N8) are **not** modelled as a second
`VEnv`: a `VEnv.WF` environment grants each constant at most one defining equation (machine-checked
this gate, `scratchpad/gate/d3_defeq_unique.lean`: `WF'.defeqOwn`, axioms `[propext, Quot.sound]`),
so an `env + addDefEq`-style `CompilerEnv` is uninhabitable on every declaration with both a kernel
and a different compiler body — 31 of the 33 measured, including all four of Arith's. Instead the
spec follows N8 of `00-REFERENCE-SPEC.md` verbatim: `SEval` reads the compiler-body table
`tbl.body?` through its `deltaC` arm, and `CompilerBodies` (§4.3) is the class-**C** typing
hypothesis N8 names, measured inhabitable 33/33.

### 1.2 Why relations, in one paragraph

MetaRocq itself ships the precedent: `EWcbvEvalNamed.represents` / `represents_value`
(`EWcbvEvalNamed.v:289, 318-323`) is a term relation paired with a value relation whose
`represents_value_tFix` is exactly the closure-vs-`.fix` value correspondence the fix arms here
need. (`[L Def. 10]`'s `◄` is the analogue of `Erases`, not of a λ□→λ□ pass; and MetaRocq's own
λ□→λ□ passes are functions with a *relational* `obseq` (`Transform.v:38-46`) — this design departs
from that split deliberately, because the function would have to be keyed on the run's fresh-name
state and the `Lean.Environment`, re-importing the registry-indexed specification the review
condemned.) A relation is also the only shape in which the Lean-specific content can be *stated*:
a recursive Lean constant has a λ-headed source body and a `.fix`-headed λ□ body, both of which
are `WcbvEval` **values** (`Semantics/Values.lean:36`; probe `scratchpad/probe/fixval.lean`), so
the correspondence between them is irreducibly a relation between a λ and a `.fix` — not a
function equality (design C's `fixIntro.correct` is false), and not a congruence over `Lean.Expr`
(design A's T5 is false at `Arith`). Finally, a relation between two λ□ terms *cannot mention*
`Expr`, `VEnv`, `Erasable` or the run even by accident, so a premise added to make a case go
through is refutable by a two-term counterexample. That is the structural answer to the review's
central finding (the specification was written to match the implementation).

### 1.3 Layers, files, trust

| Layer | Objects | lean4lean? | Class |
|---|---|---|---|
| **L0** target | `LBTerm`, `WcbvEval`, flags, values, substitution, `Closed`, `IotaBridge`, `FixUnfold`, `lbEval` | no | **A** |
| **L1** specification | `Erases`, `ErasesDecl`/`ErasesEnv`, `Erasable`, `SEval`, `CompilerBodies`, `FirstOrderInd`, T5, T7 | yes | **B** |
| **L4** passes | `Lower`, `LowerFix`, `LowerEnv`, `ElimBody`, `optimize` | no | **A** |
| **L2** bridge | `ErasureSpec`, `Supported`, run algebra, 18 motives, T8 | yes | **B** + **D** |
| **N** non-vacuity | `SourceTable`, `Green.lean`, the G-ladder, coverage, ledger, CI tools | yes | **A** |

Lane **N** is a first-class lane with its own deliverables and its own schedule slot in every
wave. That is design C's structural contribution and it is adopted wholesale: the review's two
worst findings (premises never jointly inhabited; 0/5 benchmark coverage) are scheduling failures,
and they are fixed by scheduling, not by a wave-5 deliverable.

### 1.4 What the deliverable is

For `Erasure.erase e cfg` — the function `#erase` calls — run from the empty state at a pinned
configuration: if the run succeeds with `(Σ, t)`, then `t ∈ (Erases ⨟ Lower Σ⁺)` of `e`, `Σ` is
`LowerEnv`'s image of the dependency-selective erasure `Σ⁺` of the declarations the run
registered, `Σ` satisfies peregrine's input predicate, and every source evaluation of `e` applied
to closed first-order arguments is simulated into a **box-free, unique** λ□ value at
`eraseFlags = ⟨false, true, false⟩`. Peregrine's `untyped_transform_pipeline` declares its input
evaluation at MetaRocq's `EWcbvEval.default_wcbv_flags = ⟨true, true, false⟩` (`EWcbvEval.v:69`,
`peregrine-tool/theories/erasure/Transforms.v:151`), named `entryFlags` here; the one-line bridge
`WcbvEval.propcase_weaken : WcbvEval Σ eraseFlags t v → WcbvEval Σ entryFlags t v` (§3.2,
mechanised at `scratchpad/gate/d6.lean`, class **A**) carries the stronger conclusion to the
consumer's declared point. The deliverable therefore stops at the emitted program, and its
evaluation conjunct is strictly stronger than what the consumer requires.

---

## 2. Fatal flaws named by the judges, and their resolution

Every flaw any judge called fatal or near-fatal, with what this design does about it. Nothing is
left "not fatal because" without a reason.

| # | Flaw (judge) | Applies to | Resolution here |
|---|---|---|---|
| **F1** | `.fix` value mismatch: A's T5 refutable, C's `fixIntro.correct` false, **B's `lower_correct` false as written** (all three judges) | all three | **Repaired.** `Lower` gains two arms, `fixConst` and `fixBody` (§4.5), and the transport lemma `Lower.constToFix`. The inductive and both wrappers are probe-checked to elaborate and to yield a usable recursor; the δ-obligation example is probe-checked at `scratchpad/gate/lowerfix2_fixed.lean` (the original `scratchpad/probe/lowerfix2.lean` never elaborated its final example — `Σ` is a reserved token, so the binder `hΣ` was a parse error; all Lean code in this repo writes the λ□ environment metavariable `Γ`, never `Σ`). This is where today's `Erases.const_fix` content belongs; its docstring's claim ("no arrangement of `fix`'s premises avoids needing it", `Erases.lean:618-624`) is true of the *relation*, and the relation is now `Lower`, not `Erases`. Retired in **W1**, not W4. |
| **F2** | `LBWfPeregrine.etaFix` is false on every emitted program (judges 1, 2; C alone got it right) | A, B | **Repaired.** `LBWfPeregrine` does not claim `EEtaExpandedFix.expanded_eprogram`; `PeregrinePre := LBWfPeregrine ∧ LBExpandedFix` is stated separately and is *not* concluded. Finding **F-ETA** raised (§8.2), one ledger row. Measured: `Arith.ast` has 4 bare `(constant_body (Some (tFix`, and `EEtaExpandedFix`'s only `tFix` rule needs `args ≠ []` and `#args > rarg`. |
| **F3** | The capstone's observable conjunct uses the wrong relation: `Erases v tv` yields a `.const`-headed spine, the emitted `Σ` evaluates to a `.construct` spine (judge 2, M2) | A, B, C | **Repaired.** T9's observable conjunct is stated with the composite: `∃ tv₀ tv, Erases env [] [] v tv₀ ∧ Lower Σ⁺ tv₀ tv ∧ NoBox tv ∧ WcbvEval Σ eraseFlags … tv`. Uniqueness of the answer is `firstorder_erases_deterministic` (T7) on `tv₀` plus `eval_deterministic` (T1) on `tv`; no separate `Lower`-determinism theorem exists (a `firstorder_lower_deterministic` would rest on a `FirstOrderShape` predicate no theorem consumes — policy 6). |
| **F4** | `by decide` on a `Lean.Environment` predicate is impossible; `native_decide` is banned; criteria 8/11/13 unreachable (judges 2, 3; probe `dec.lean`) | A, B | **Repaired.** Every decidable check runs on a **reified `SourceTable`** spliced by the `reify%` term elaborator in the same elaboration as the rung (§4.11); discharges are `by rfl` on the table, and adequacy is the single named class-**D** binder `htbl` beside `hrun` — not a structure field, which could not even bind `tbl` (§4.10). `ErasableAxioms` was the spec's own *hypothesis* `hax`, stated boundedly over the emitted `Σ`'s key list with a `Decidable` instance, so per-rung `by decide` genuinely works — **retired at Wave 2** (`04-AMENDMENT-W2.md` §8: the value arms make an axiom-reaching run have no `SEval` derivation, PCUIC's own answer, so nothing consumes the predicate). |
| **F5** | `benchArith : Nat → Nat`, so T10's `hty : … (.const ``Nat [])` cannot be instantiated (judge 3, C alone noticed) | A, B | **Repaired.** The capstone's observable conjunct is quantified over closed first-order argument spines (§5, T9); `args = []` is the spec's T9 verbatim, `args = [0]` is `benchArith`. The ladder additionally carries the closed rung `arithClosed := benchArith 0`. |
| **F6** | `Lower` has no arm for the eraser's η-expansion of under-applied ctor/`casesOn` heads, so T8 is unprovable on Arith (judges 2 M6, 3 F3) | B | **Repaired.** Two η arms, `ctorEta` and `elimEta` (§4.4), matching `visitCtorEtaGo`/`visitCasesEtaGo` (`Erasure.lean:705-728`) exactly: fresh binders are pushed into the spine and the λ□ result is wrapped in `mkLambdas`. |
| **F7** | A's per-motive `∃ E` does not compose across sibling sub-runs (judges 2 M4, 3 F6) | A | **Avoided by construction.** `Σ⁺` is *universally* quantified in every motive under `SpecEnv`, which is antitone in the run state; `SpecEnv.mono` is proved from the existing `StateLe` (`ErasureRun.lean:1585`) that every motive already concludes. |
| **F8** | C's `LBPass.correct` quantifies over all `CompileTable`s with nothing tying the table to `Σ`; two sources of truth (judge 3, F2) | C | **Avoided.** There is no `CompileTable`. The passes read `Σ⁺` — the same object that justifies them. |
| **F9** | `Erases.bvar`/`.fvar` drop the `Δ.find?` premise `TrExprS` carries (judges 1, 2, 3) | B | **Repaired.** Restored (§4.2). |
| **F10** | T5 written at `env` while the capstone evaluates at `envC` (judge 1) | B | **Repaired, by deletion.** There is **one** `VEnv` index, the kernel `env`, everywhere — `envC`/`CompilerEnv` is gone (§3.1 Q3: it was uninhabitable, `WF'.defeqOwn`). Compiler bodies enter through `SEval`'s table parameter, so no `.mono` lifting between two environments exists to get wrong. |
| **F11** | `LBPassR.correct` has free variables in a structure field (judge 2, M10) | B | **Repaired.** Explicit `∀` binders (§4.10 note). |
| **F12** | `ProjParams` reverse-engineers a parameter count out of an ι-rule key (judges 2, 3) | A | **Avoided.** `IndInfo` reads the block data off `VEnv.WF`'s declaration list; `Erases.proj` keys on it. |
| **F13** | `SelfRefers`/`name_occurs` as a specification premise mirrors the implementation (judges 1, 3) | A | **Avoided.** `LowerFix` tolerates an unused fix binder; no source-side occurrence premise exists anywhere. |
| **F14** | A single monolithic 18-motive wave reproduces the failure that made the current tree (judges 1, 2) | B | **Repaired.** W4 splits the motives into three batches (3 environment-facing **first**, 7 mechanical, 8 pass-facing), each a unit on disjoint files. |
| **F15** | C's `eraseB`/`srEval` are ~2,700 lines no theorem needs, and `eraseB` is a larger `EraseCore.lean` (judges 1, 2, 3) | C | **Not adopted.** `lbEval` (class **A**, ~420 lines, unconditional) is adopted because it turns the target-side evaluation of every green rung into `by rfl` and cross-checks `peregrine eval`. `srEval` is **W6-optional** and scoped per flag slice; `eraseB` is **not built** — the `Erases`/`Lower` witnesses the ladder needs are produced by the derived introduction lemmas plus the reified table. |
| **F16** | Criterion 21 (no `Lean4Lean`-namespace declarations) vs `CheckerAdequacy.lean`'s eight (all three) | all | **Deferred past W3; not met by this schedule.** `kernel_isErasable_sound` mentions `LeanToLambdaBox.isErasable`, so it is renamed `LeanToLambdaBox.Oracle.kernel_isErasable_sound` in W1. The seven kernel-generic declarations cannot leave until the pin moves, and moving the pin is a separate agent's work on the fork, not this repository's (§8.3): **U3.4** only *files* the ask (`doc/upstream-asks.md` item 3), it does not edit the fork or bump `lake-manifest.json`. `CheckerAdequacy.lean`'s `namespace Lean4Lean` block therefore stays until an external pin bump lands; the criterion-21 gate check — `grep -rn "^namespace Lean4Lean" LeanToLambdaBox/` empty — is not run as a W3 acceptance test for this reason, and `doc/trust.md` records the exception rather than a check papering over it. |
| **F17** | `hwt : TrExprS envC [] [] e ve` and `hty` must be *inhabited* for a 39-declaration program or criterion 13 is theatre (judge 3, shared blind spot) | all | **Scheduled**, W3 unit `TrWitness`: read `TrExprS` off a successful run of lean4lean's checker (`CheckerAdequacy.lean:94,112`, `M.WF.run'`, `VState.WF.initial`). **Named fallback:** if that does not land, `hwt`/`hty` stay class-**D** binders beside `ErasureSpec`, `test/ledger.expected` grows the rows, and criterion 13's wording (A14) is re-amended in the same commit that records the fallback — never silently. |
| **F18** | `hrun` can never be discharged inside Lean (`Void IO.RealWorld` is opaque) (judge 3) | A, B | **Stated, not hidden.** `hrun` is a permanent binder; it is named as such in the capstone's docstring, in the ledger (class **D**), and in `doc/coverage.md`, and it is mechanised externally by `lake exe green-check` (re-run `#erase`, byte-diff the committed `.ast`). |
| **F19** | `by rfl` on a 19-node peano tower through 27 constants may exceed kernel budgets (judge 1) | C | **Priced.** `lbEval` is fuel-indexed and structurally recursive; G7's evaluation is done by `lbEval` + `lbEval_sound`, not by `WcbvEval` derivation building. Risk **R9** with the fallback (evaluate `arithClosed` at a smaller exponent rung, recorded in the coverage table). |
| **F20** | B lists criterion 5 as "met" while replacing `LBPass` with a relational `LBPassR` (judge 3) | B | **Filed as amendment A8** (§3.3), not silently. |

### 2.1 Design-gate findings (24 refuter verdicts) and their resolution

Every fatal or major gate finding, resolved in this document; probe files under
`scratchpad/gate/` are the evidence.

| # | Finding (gate) | Resolution |
|---|---|---|
| **G-D1a** | T8 unstateable on every recursive declaration: `visitMutual`'s block branch emits `.fvar id` at a source `.const` position, which no factor of `Erases ⨟ Lower` relates (fatal; 50/50 emitted `FixDef`s exercise it) | `ErasesLBFix` third factor + T8 split on `ctx.fixvars` (§4.5, §4.7, §5); U1.7's acceptance gains the stateability test; §1.1's "rename" claim retracted for motive 6 |
| **G-D1b** | `lower_correct` false: `LowerEnv` had no totality clause, so a pruned plain definition strands the target | `LowerEnv.defsTotal` added (§4.8); real instantiation satisfies it — pruning removes only `RuntimeKey`s |
| **G-D1c** | `mkElimBody_iota`'s `↔` false in the ⇐ direction (β needs every argument to evaluate) and at block flags | split into `_fwd` (unconditional) and `_bwd` (guarded by evaluability of `pre`/minors — the same obligation `ErasesLB.cases`'s `hpre` supplies); both pinned at `with_constructor_as_block = false` (§4.6) |
| **G-D1d** | T9 ill-formed: `t₀`, `fo` free (auto-bound universally — absurd), and the headline `Erases … e t₀` conjunct missing | T9 rewritten: `∃ Σ⁺ t₀` binds, the subject's `Erases` conjunct restored, `fo` eliminated by closing `FirstOrderInd` (§5, §4.12) |
| **G-D2a** | `lower_correct` false without a `principalArgIdx` premise (machine-checked counterexample `gate/rarg_ce.lean`: at `rarg = 1` source ⇓ `□`, target stuck) | `LowerBlock.hrarg : ∀ d ∈ defs, d.principalArgIdx = 0` (§4.4) — a fact about the emitter (`mkDef` never sets the field, `Basic.lean:67`; `FixUnfoldChain` already carries it), not a filter |
| **G-D2b** | `CloseConst`'s per-member `ids` cannot feed `closeFix_substList_fixSubst` (freshness needed against the whole block; `LBClosed` says nothing about fvars) | `ids` hoisted into `LowerBlock` — one Nodup list for the block, freshness against every member, matching `visitMutual`'s single `ids` (§4.4-4.5) |
| **G-D2c** | `Lower.const`'s `DefnDeclFix` premise undefined; on one reading it empties the fix arms on every recursive block (probe `gate/d2_vacuity.lean`), on the other it is vacuous | deleted; the deliberate `const`/`fixConst` non-determinism at a block member is documented as what `Lower.constToFix` transports (§4.4) |
| **G-D2d** | `lowerFix_correct` needs λ-headed specification bodies; asserted in prose only, unenforced by the eraser | explicit premise on the emitted `defs` (`isLambda`), transported to `bs` by `LowerBlock.lambda_of_fixLambda`; the missing eraser-side guard is raised as part of **F-ETA** (§4.4, §8.2), never assumed silently |
| **G-D3** | `CompilerEnv` jointly contradictory (fatal, machine-checked `gate/d3_defeq_unique.lean`): `le + wf + bodies` force compiler body = kernel body, refuted 31/31; T9/T10 vacuous on 5/5 programs | `CompilerEnv`/`envC` **deleted**; N8 adopted verbatim: `CompilerBodies` typing hypothesis + `SEval.deltaC` reading the table, with the applied-instance defeq side condition that is `rfl`-provable for structural recursion (measured 12/12 incl. Arith's four, `gate/d3_eqlemmas.lean`) (§4.3); `WF'.defeqOwn` filed upstream (§8.3) |
| **G-D4** | `table_adequate` field could not bind `tbl` (auto-bound ∀ — every table adequate; `PrimSpec` uninhabited); committed-JSON reify circular (regenerate-and-diff); `oracle`/`cfg` columns dead; `supportedB` unfuelled; wrong env index | field deleted → named binder `htbl`; `reify%` elaborator replaces the JSON; `SourceTable` shrunk to `decls`+`inds`; `supportedB` fuelled with `outOfFuel : SupportError`; one env, so no index mismatch (§4.10-4.11) |
| **G-D5** | `oracle_sound` overstated ("discharged" hides the assumed `isErasableMeta` fallback and the `lparams = Us` scope); `env_connect` ill-typed at `Lean.Environment`; SI-1 (the `approxDepth` fuel) unraised | field split into `oracle_refl` (kernel arm, class **B**) + `oracle_meta` (fallback + polymorphic-scope, class **D**, measured empirically dead: 0 fallbacks / 139,196 constants, `gate/d5_census.lean`); `env_connect` stated at `lenv.toKernelEnv`; the fuel defect is **F-FUEL**, fixed in **W0 on `dev/verify`** — `Relevance.lean` is verification-authored (absent from `main`), so this is not a transpiler edit, and `isArityCheck.WF` never mentions the fuel, so the fix is proof-free (§4.10, §8.1) |
| **G-D6** | tree has no `⟨true,true,false⟩` point; §3.2's name map wrong twice; `with_prop_case` inert on emitted output (683/683 `propositional = false`); `mkElimBody_iota_sing`'s premise uninhabitable on any real Σ; U0.1's grep unsatisfiable | flag chain re-derived (§3.2): deliverable at `eraseFlags = ⟨false,true,false⟩` (= today's `appliedFlags`, = the point all 103 existing simulation sites use), `propcase_weaken` bridges to `entryFlags`; the singleton-elim machinery is deleted with restriction **N18** and shipping finding **F-PROP** (§3.1 Q2, §8.2); U0.1 re-scoped as a tree-wide mechanical rename |
| **G-D7** | `subsingletonElim_of_wf` false (`Acc` satisfies the hypotheses, refutes the conclusion — `LargeElim` minus a disjunct is stronger than what `WF` gives); "codegen refuses `Acc.rec`" true of `.rec` only (`Acc.casesOn` compiles, probe `gate/d7e.lean`); F-ACC's mechanism wrong (the emitted `.case` is *stuck*, not mis-boxed) | the theorem and its consumers are deleted with N18; the honest kernel fact (`largeElim_of_wf`, both disjuncts) is recorded as the future shape gated on F-PROP; `SupportError` keys on the *shape* (`propElimIntoData I`), never the name (§3.1 Q2, §4.11, §8.2) |
| **G-D8** | `FirstOrderInd`'s free `fo` makes T7/T9 false (`fo := fun _ => True` admits a `True`-fielded `Type` — probe `gate/d8b.lean`); `FOType`'s `.bvar` clause dead (lean4lean names block formers by `.const`), so no stratified `fo` accepts `Nat` | `fo` closed by `FOClosed` (∃-quantified post-fixed point; the checker's visited set is the witness); `FOType` takes the block's own names; `mono`/`noIndices` declared as scope restrictions with ledger rows, not attributed to the papers (§4.12) |
| **G-D9** | `etaCtors` quantified over `t` only — vacuous on all five programs (982/982 constructor occurrences live in Σ's bodies; every emitted `t` is a bare `tConst`); no proof route budgeted; "(boxed, being types)" false (`OfNat.mk`'s numeral parameter is data) | `etaCtors` split env+term, mirroring `expanded_eprogram_cstrs`; `Lower.ctorApp` gains the saturation premise `hsat` (the eraser's own `args.size ≥ arity` guard), which also makes `ctorApp`/`ctorEta` disjoint; Q5's parenthetical corrected (§4.4, §4.9, §3.1 Q5) |
| **G-D10** | the schedule is not topological (62 import-order inversions), `Supported`/`SEvalDataC`/`PrimSpec` name clashes, the build root unowned in four waves, three acceptance greps vacuous or unrunnable, budgets off by ~5,650 lines, ledger provenance not `#print`-measurable | `02-PLAN.md` re-derived: topological deletion invariant + `hygiene --schedule` check, the **W1 cut** (U1.0), gate-owned standing files (N3a), `PrimSpec → ErasureSpec` (upstream `Lean4Lean.PrimSpec` exists, `Verify/Typing/Expr.lean:315`), greps fixed, budgets restated (§7.3), ledger fixture = `#print` output only with provenance in `doc/trust.md` |
| **G-D11** | criterion 13 silently narrowed; `hnp : ¬ Panicked run` undefined with `run` unbound; `ErasesDecl.ax` admits ι-reducible constants (T5 false at an applied `Eq.rec`); criteria 21/22 mutually unsatisfiable at a frozen pin | amendments A14/A15 filed (§3.3); `hnp` deleted — N12 is met by its option 2 (the per-site table + `Supported`, which is what the tree actually does); `ax` gains ι-inertness (§4.8); the U3.1 pin-bump unit is added |
| **G-D12** | the dev/fix queue had no tracked home; B4's row reason false (both inline paths sit under `single_decl` — behaviour-neutral); `auto_inline_typeclass_dispatch` (review SI-10) unnamed; `ErasableAxioms` as a conclusion made true by an assumed name table | `doc/rework/03-DEV-FIX.md` is a U0.5 deliverable; B4 corrected, **F-PRODUCT** row added; `hax` restored as the spec's hypothesis with `AxiomRealizer` rows named class-**E** per name — **retired at Wave 2**, the rows becoming `doc/coverage.md`'s F-EQREC row (`04-AMENDMENT-W2.md` §8) |

### 2.2 Wave 1 findings

Every place W1's units found this document's printed signature false, unstateable, or reliant on
a function that does not exist, resolved by a strictly stronger or differently-scoped statement.
`§4`/`§5` above already carry the delivered form; this table is the index — id, what was printed,
what is true, the name it was delivered under, and the evidence (a machine-checked refutation or a
failing goal).

| # | Design statement as written | What is true | Delivered as | Evidence |
|---|---|---|---|---|
| **U1.1-a** | `structure IndInfo (env) (I) (iid) (np) (nfs) : Prop` with no body shown | quantifying the witness declaration list at `env` itself makes `Erases.mono`'s `proj` arm unprovable: `env ≤ env'` gives no declaration list for `env'` | `IndInfo.block : ∃ ds env₀ decl t, VEnv.WF' ds env₀ ∧ … ∧ env₀ ≤ env ∧ …` — quantified at an `env₀ ≤ env` below `env` (`Erases.lean:51-57`) | `IndInfo.mono` (`Erases.lean:70-74`) is provable only at this form |
| **U1.1-b** | §4.2's ten rules plus the carried transport lemmas, no inversion lemmas | every downstream consumer that cases on an `Erases` derivation needs the two-way form | eleven `Erases.*_inv` lemmas sharing `ErasesBox` (`Erases.lean:158-236`); no design counterpart | self-motivated groundwork, not itself a refutation — recorded because §4.2 now cites it |
| **U1.3-a** | `Erases.forallE_erasable (henv : env.WF) : TrExprS … (.forallE …) ve → Erasable …` | level well-formedness (`u.WF Us.length`) is not derivable from `TrExprS.forallE`'s premises alone (they give only `IsType`, not a level fact) | `Erases.forallE_erasable` gains `(hΔ : VLCtx.WF env Us.length Δ)` (`ErasesTotal.lean:68-71`); `sort_erasable` unchanged, `henv` unused | failing goal: `u.WF Us.length` unreachable from `IsType Δ.toCtx ty'`/`IsType (ty'::Δ.toCtx) body'` alone |
| **U1.3-b** | `Erases.exists_of_trExprS (henv) (hΔ) (h : TrExprS env Us Δ e ve) : ∃ t, Erases env Us Δ e t` — total over every `Expr` former | unprovable at `.proj`: the only route needs `HasType.app_inv` (`Theory/Typing/Strong.lean:886`), which needs `OrderedStrong`, built only from `VEnv.WF.orderedStrong` (`EnvLemmas.lean:338`), built from `VEnv.WF.patsStrong := sorry` (`EnvLemmas.lean:334`) — importing a ~200-line spine-peeling detour through lean4lean's own inherited `sorryAx` cluster for one case | `Erases.exists_of_trExprS_of_projInfo (henv) (hΔ) (hpi : ProjInfo env e) (h : TrExprS …) : ∃ t, Erases …` (`ErasesTotal.lean:126-128`) — an added `ProjInfo` premise carves the proj case out, discharged trivially (`ProjInfo.toConstructor`) everywhere `Erases.lit` needs it | failing goal, in the `.proj` case: `IndInfo env S ?iid ?np [?nf]` with `i < ?nf`, unreachable without the `sorryAx`-rooted route |
| **U1.4-a** | `SEval.deltaC`'s `hdef : ∀ vc vb, TrExprS … vc → TrExprS … vb → env.IsDefEqU … vc vb` | the ∀-form is inert for the induction (`hcont`'s IH needs a translation of the *reduct*, which a premise quantified over *given* translations never supplies) and holds vacuously wherever the redex has no translation at all | `hdef : StepDefeq env Us Δ (mkApps (.const c us) argsv) (mkApps b' argsv)`, `StepDefeq e₁ e₂ := ∃ v₁ v₂, TrExprS … e₁ v₁ ∧ TrExprS … e₂ v₂ ∧ env.IsDefEqU … v₁ v₂` (`SourceEval.lean:104-106,172-179`) | `forall_form_not_stepDefeq` exhibits the ∀-form holding vacuously true of `.bvar 0` at `Δ = []`, where `StepDefeq` itself is false |
| **U1.4-b** | `SEval.defeq (henv) (hΔ) (hcb : CompilerBodies lenv env bo) (htr) (hev) : ∃ vv, …` | with `hdef` in `StepDefeq`'s ∃-form, nothing in the proof of `SEval.defeq` consumes `CompilerBodies`; keeping the binder would leave it unused in a class-**B** theorem | `SEval.defeq (henv) (hΔ) (htr) (hev) : ∃ vv, …` — no `lenv`, no `hcb` (`SubjectReduction.lean:112-116`); strictly stronger than the printed form | none of the theorem's tactic block mentions `hcb`/`CompilerBodies`/`lenv` |
| **U1.6-a** | `mkElimBody_iota_fwd`/`_bwd` with only `hbl`, `hk`, `harity`, `hprop` (`_bwd` also `hpre`/`hmin`) | four more guards are load-bearing, not bookkeeping: `hplen`/`hmlen` pin the spine's shape, `hval` is needed because ι fires on the discriminant's *value* not its syntax, `hfields` is needed because the ι-reduct substitutes fields *sequentially* so an unclosed later field can be hit by an earlier substitution | `hplen : pre.length = dp`, `hmlen : minors.length = nfs.length`, `hval : WcbvEval Γ fl (mkApps (.construct iid k []) args) (mkApps (.construct iid k []) args)`, `hfields : ∀ a ∈ args.drop np, LBClosed a 0` added to both directions (`ElimBody.lean:697-745`) | `mkElimBody_iota_needs_minor_count` refutes dropping `hmlen`; `mkElimBody_iota_needs_closed_fields` refutes dropping `hfields`, by a two-field constructor whose second field carries a loose index |
| **U1.6-b** | `inductive ElimBody … \| cases … \| rec …` | `ElimBody.rec` is the name Lean's kernel reserves for the structure's own auto-generated recursor and refuses to redeclare | the second constructor is named `recur` (`ElimBody.lean:118-120`) | `(kernel) constant has already been declared 'LeanToLambdaBox.ElimBody.rec'` |
| **U1.6-c** | `def mkElimBodyRec (iid) (np) (dp) (nfs) : LBTerm` presented beside `mkElimBody` as if equally determined by these four arguments | `(iid, np, dp, nfs)` carries only constructors' field *counts*, never which fields are recursive, so no function of these four arguments can write the recursive calls a faithful `I.rec` body needs; a real recursor needs a fifth index (a per-constructor recursive-field mask) | `mkElimBodyRec iid np dp nfs := .fix [⟨.anon, mkElimBody iid np dp nfs, dp⟩] 0` (`ElimBody.lean:108-109`) — `mkElimBody`'s dispatch under a guarded, unused-variable `fix`; the recursor *shape* at the recursor's calling convention, not a recursor | delivered with no `mkElimBodyRec_iota_*` theorem — the design gap is recorded, not silently closed |
| **U1.7-a** | `Lower.constToFix (hblk : LowerBlock …) (hcl : LBClosed t 0) (h : Lower Σ s t) (hct : ConstToFVar …) : Lower Σ s (substFix ids defs t')` | at `s = t = t' = .fvar ids[0]!` every premise holds (`LBClosed (.fvar x) 0` is `True`) while the conclusion is underivable — no specification body is a free variable; `LowerBlock.hfresh` alone covers only the block's own bodies `bs'`, not an arbitrary externally-supplied `t` | `Lower.constToFix` gains `(hΓ : ClosedBodies Γ)` and `(hfv : ∀ x ∈ ids, ¬ hasFVar x t)` in place of `hcl` (`LowerFix.lean:598-603`) | `LowerFixFixture.constToFix_needs_freshness` |
| **U1.7-b** | `LowerBlock.lambda_of_fixLambda (hblk) (hfl : ∀ j, … → isLambda (defs[j]!).body) : ∀ j, … → isLambda bs[j]! = true` | a block member whose specification body is a bare `.const` can still η-expand to a λ under `Lower.ctorEta`, giving a λ-headed `bs'[j]!` over a non-λ `bs[j]!`, refuting the conclusion | gains `(hη : ∀ j, j < kns.length → ¬ EtaSpine Γ bs[j]!)` (`LowerFix.lean:927-936`); discharged for eraser-derived bodies by `not_etaSpine_lambda_named` | one-inductive fixture: a member body `.const lfC` whose lowered image `Lower.ctorEta` sends to `λ_. lfC #0` |
| **U1.9-a** | `ErasesDecl.defn {c body b₀} (hd : bo c = some body) (hb : Erases env (levelParamsOf env c) [] body b₀) : …` | `levelParamsOf env c` cannot exist: `VConstant` (lean4lean) records `uvars : Nat`, a count, never parameter names, and `Erases`'s second index is a `List Name` | `defn {c body b₀ Us ci} (hc : env.constants c = some ci) (huv : Us.length = ci.uvars) (hd) (hb : Erases env Us [] body b₀) : …` — `Us` existentially bound at the declared width (`ErasesEnv.lean:110-112`) | none of the level-scope-parametric transport lemmas (U1.2) need more than the width |
| **U1.9-b** | `ErasesDecl.ind {I iid np nfs} (h : IndInfo …) : ErasesDecl iid.blockName (.inductiveDecl (indBodyOf env I))` | `indBodyOf` is not definable: `MutualInductiveBody` carries λ□ `Ident` strings, `kelim`, `propositional`, none of which a `VInductiveType` determines in λ□ coordinates | `ind {I iid np nfs mib} (h : IndInfo …) (hm : IndBodyOf iid np nfs mib) : ErasesDecl env bo iid.mutualBlockName (.inductiveDecl mib)` — a relational premise reading only the three numbers the target semantics consults (`ErasesEnv.lean:93-96,120-121`); strictly more permissive, which is exactly the slack the semantics cannot observe | — |
| **U1.9-c** | `hpat : ∀ p, p ∈ patsOf env → p.head ≠ c`; `closed : ClosedEnv Σ`; `prune : ∀ kn, envLookup Σ kn ≠ none → Reachable Σ kn` | `patsOf : VEnv → List Pattern` does not exist (`VEnv.pats` is a relation) and `Pattern` has no `head`; `ClosedEnv` would be a second name for `Lower.lean`'s existing `ClosedBodies`; `Reachable Σ kn` has no root and is either undefined or (rootless) vacuous | `PatOf env p := ∃ r, env.pats p r`, `patHead`, `IotaInert env c := ∀ p, PatOf env p → patHead p ≠ c` (`ErasesEnv.lean:63-73`); `LowerEnv.closed : ClosedBodies Σ`; `LowerEnv.sub : ∀ kn, envLookup Σ kn ≠ none → envLookup Σ⁺ kn ≠ none` plus the standalone, program-rooted `PrunedFor Σ t := ∀ kn, envLookup Σ kn ≠ none → ReachableFrom Σ t kn` | — |
| **G1-O1** | T9's `hsup : Supported env e` | `Supported.lean`'s Prop `Supported` and `supportedB_sound` are U1.8's, not yet landed | T9 currently takes `hsup : supportedB tbl fuel e = .ok ()` — the checker verdict directly (`Capstone.lean:157`) | swaps to `Supported env e` once U1.8 lands, at three call sites — a statement edit, no reproof |
| **G1-O2** | T9's `FirstOrderInd env I` premise inside the ∀-clause | `FirstOrderInd.lean` (U3.5) is not yet landed | T9 currently takes a free implicit `{fo : Name → Prop}` with the premise `fo I` (`Capstone.lean:151,175`) | instantiates to `FirstOrderInd env I` once U3.3 lands, at the three sites named in `Capstone.lean`'s own module docstring |
| **G1-O3** | T9's spine premise `∀ i, i < args.length → ErasesLB env [] Σ⁺ [] args[i]! targs[i]!` | `ErasesLB.lean` (§4.7, U2.2) is not yet landed | T9 currently takes `targs.length = args.length` plus `∀ i, i < args.length → ∃ a₀, Erases env [] [] args[i]! a₀ ∧ Lower Σ⁺ a₀ targs[i]!` — the composite unfolded, with the length equation `Lower.mkApps` needs (`Capstone.lean:169-171`) | folding back to `ErasesLB` once it exists is definitional (the unfolded form and the composite agree by `Lower.mkApps`'s own length premise) |
| **G1-O4** | §4.14's ledger names `P`, `htbl`, `hrun`, `hwt` as the class-**D** binders (A14) | `green_G1`'s discharge of `hcb` needs an extra fact about the reified table beyond `htbl`'s adequacy | a fourth class-**D** binder, `hsafe : TableSafe lenv g1Table` (`Supported.lean:327`), guards `g1_compilerBodies` | recorded as a `doc/trust.md` row beside `hsafe`, outside A14's original list |
| **G1-O5** | T9's eight remaining binders (`P`, `htbl`, `hcfg`, `hcb`, `hwt`, `hsup`, `hrun`, `hax`) are load-bearing hypotheses of the composed theorem | at this wave the entire proof is `obtain ⟨Σ⁺, t₀, B⟩ := hbridge; …` — none of those eight names occurs in the proof body | `set_option linter.unusedVariables false in` immediately precedes the theorem (`Capstone.lean:130,179-192`) | zero occurrences of any of the eight names in the tactic block; each becomes load-bearing only as W2–W4 discharge `hbridge`'s own fields |
| **G1-O6** | `lower_correct (hwf : LBWfSpec Σ⁺) (hcl : LBClosed t 0) (hE) (h : Lower Σ⁺ t t') (hev : WcbvEval Σ⁺ eraseFlags t v) : ∃ v', Lower Σ⁺ v v' ∧ WcbvEval Σ eraseFlags t' v'` — unrestricted over all 17 arms | the unrestricted statement is false at the `ctorEta` arm: an under-applied constructor constant δ-unfolds, on the specification side, to the applied-form constructor node (a value), the pass sends the *same constant* to the η-expanded λ (also a value), and no arm of `Lower` relates a constructor node to a λ | delivered as `lower_correct_deltaChain`, on the δ/constructor/fix fragment (`DeltaChain`, a sub-relation of `WcbvEval`) under three named guards `LowerNoEta`, `BlockBodiesLambda`, `DefsSurvive` (`LowerCorrect.lean:449-453`); W2 refuted the general statement outright and retired both — §2.3 | `lower_correct_needs_ctorEta_guard` (`LowerCorrect.lean:565-568`), on a one-inductive, single-unary-constructor fixture |
| **G1-O7** | T7's `firstorder_no_box` composed directly with `lower_correct` to conclude the *lowered* value is box-free | box-freedom does not transport along `Lower` in general: `Lower.fixConst` relates the box-free `.const kn` to a block's `.fix`, whose `defs` carry the members' own boxed bodies | T9's value-side conjunct states `NoBox tv` of the lowered value `tv` directly (via `hbridge.firstorder`), not by citing `firstorder_no_box` on `tv₀` alone | `noBox_lower_needs_noFix` (`LowerCorrect.lean:187-192`), witnessed on the `LowerFixFixture` two-member block |
| **G1-O8** | §6's non-vacuity lane rests on "a committed `.ast`" per rung, and `GreenCheck.lean`/`Green.lean`/`VerifyBench/Spikes/G1.lean`'s docstrings asserted the rung's `.ast` was committed | `VerifyBench/ast/.gitignore` ignores `*` (the root `.gitignore` also has `*.ast`), so `git status` never showed the file and the byte-diff compared against whatever happened to be on disk, not a tracked artifact — the three docstrings' claim was false | fixed by three lines in `VerifyBench/ast/.gitignore` (`!Spikes/`, `!Spikes/*.ast`, plus a comment): `VerifyBench/ast/Spikes/G1.ast` is trackable while `G1.ast.inlinings` and the five benchmark `.ast`s stay ignored | `git check-ignore -q` and `git add -n` on `VerifyBench/ast/Spikes/G1.ast` before and after the `.gitignore` edit |


### 2.3 Wave 2 findings

Six refutations, each machine-checked in the file that delivered it. They retire the
two-simulation architecture, not a lemma in it; the amended architecture is `04-AMENDMENT-W2.md`,
and §3.1 Q9–Q12 carry its decisions.

| # | Design text refuted | Why it is false | Replacement | Refutation |
|---|---|---|---|---|
| **W2-R1** | T5's ι/constructor arm at `Σ⁺` | `SEval.ctorVal` makes a constructor constant its own value; the ten-rule `Erases` relates that value only to `.const kn` or `.box`, while `Σ⁺` gives the kername the body `.construct iid k []`, which `WcbvEval` unfolds eagerly | the eleventh rule `Erases.ctor` (Q9) | `erases_correct_needs_tabled_ctor`, `erases_const_ne_construct` (`ErasesCorrect.lean:808`) |
| **W2-R2** | T5's five hypotheses | at a declared, untabled constant every hypothesis holds and the target is stuck at a body-less declaration | `SEval`'s value arms become `[S Fig. 12]`'s `value_head` (§4.3): such a constant has **no source value**, so the counterexample has no `hev`. No axiom-freedom premise — MetaRocq has none either (A18) | `erases_correct_needs_tabled` |
| **W2-R3** | `hΣ : ErasesEnv env bo Σ⁺ t` as the δ arm's premise | program-keyed, and `decls` runs the direction opposite to the arm's | `ErasesEnv` gains the `defns` clause `erases_deps` has (§4.8) | `erasesEnv_not_deltaAgrees` |
| **W2-R4** | `lower_correct` over all 17 arms | false at `elimEta` with an `ElimBody`-shaped head, at `Σ⁺ = Σ = []`, with every design guard proved in the same statement | `ElimHeadOf` deleted, both eliminator arms `.const`-headed (§4.4); nothing transports along `Lower` at all (Q10) | `lower_correct_needs_elimBody_head` |
| **W2-R5** | `LowerNoEta` as a guard | it forces `cstrArity Σ iid k = 0` for every declared constructor, so it is false on every environment reaching `Nat.succ` — `lower_correct_deltaChain` was vacuous as guarded | deleted with the statements that carried it | `lowerNoEta_forces_nullary_ctors`, `lowerNoEta_fails` |
| **W2-R6** | `elimApp` inside an induction on `WcbvEval` | at a saturated eliminator spine the derivation's top rule is `beta` at the last minor, whose IH sees neither the discriminant's evaluation nor the selected minor's application | one induction on `SEval`, where the ι arm's IH is taken at the un-contracted branch application (Q11) | U2.1 obstruction 2 |

What Wave 2 delivered and this design keeps: the composite `ErasesLB` and its seventeen
introduction lemmas, the βζδ+lit arms and their metatheory (`Erases.defeqDFC_wt`,
`erases_subst_let`, the `WcbvEval` spine kit, `erases_mkApps_inv`, `erasable_mkApps`),
`LowerFix.constToFix`, `IotaBridge`, T9 with its single `hbridge` binder, `green_G1`. Not
`Fuel.lean`: it has zero references tree-wide and no importer, so U2.10 deletes it.

### 2.4 Wave-2 delivery findings

W2's second half (U2.5–U2.10, G2) delivered the amended architecture; six of its own unit
reports carry a machine-checked finding against what §4/§5 printed at the time. None retires a
rule; each narrows a signature or a status this design's text must now match (policy §6/§9.1).

| # | §4/§5 text | Why it does not hold as printed | What is landed instead | Evidence |
|---|---|---|---|---|
| **W2b-F1** | `LowerEnv.specBlocks : BlockBodiesLambda Σ⁺` (§4.8), consumed unconditionally by the `Lower.source_*` kit | **Unsatisfiable at every specification environment the five programs produce.** `BlockBodiesLambda Σ⁺` quantifies over *every* `LowerBlock` over `Σ⁺`, and a `LowerBlock`'s only membership condition is that each member is declared with that body — so any single declared non-λ body is a one-member block that refutes it. `Unit.unit ↦ .construct … []` is exactly such a body, present once per file in all five programs and in G1's own `Σ⁺` | Landed **verbatim**, and REFUTED as printed: `LowerEnv Σ⁺ Σ` — hence T5 — is uninhabitable on every realistic `Σ⁺`. **No repair is landed.** The obligation for U3.1/U3.2/U3.3, whichever unit's step first spends `specBlocks`: restrict the clause to the blocks the pass actually builds (key it on `LowerFix`/`visitMutual` groups, i.e. on the emitted `.fix` declarations), or restate it as "every body that is a member of an emitted `.fix` block is a λ" | `ctorBodyEnv_block`, `not_blockBodiesLambda_ctorBodyEnv`, `lowerEnv_needs_lambda_bodies` (`ErasesEnv.lean:271-312`); U2.8 |
| **W2b-F2** | `theorem SEval.le (h : env ≤ env') : SEval env … → SEval env' …` (§4.3), unconditional | **False.** `deltaC`'s `hnd : ∀ I dp nm, ¬ CasesOnShape env c I dp nm` is negative in `env`, and `CasesOnShape` is monotone the *wrong* way (`CasesOnShape.mono : env ≤ env' → CasesOnShape env … → CasesOnShape env' …`): an extension that declares an inductive block named `c.getPrefix` can make `CasesOnShape env' c …` hold where `CasesOnShape env c …` did not, so an `SEval env` derivation need not survive to `env'` | Gains a premise `hcs : ∀ c I dp nm, CasesOnShape env' c I dp nm → CasesOnShape env c I dp nm` — "the extension declares no eliminator shape `env` did not already have". No consumer exists tree-wide (`grep -rn "SEval.le"` matches only its own definition) | `SourceEval.lean:298-304`; U2.6 |
| **W2b-F3** | `SpecEnv.erasesEnv (H : SpecEnv env bo s Σ⁺) (hdeps : …) : ErasesEnv env bo Σ⁺ t` (§4.8), one premise | `SpecEnv`'s six fields never mention `bo`, so no proof of `ErasesEnv`'s `defns` clause can come out of `H` alone | Gains a second explicit premise `hdefns`, exactly `defns`'s shape. U3.6's `SpecEnv.exists` is where it must be discharged from the run's registry (no consumer exists yet: `grep -rn "SpecEnv.erasesEnv"` matches only its definition) | `SpecEnv.lean:67-76`; U2.8 |
| **W2b-F4** | `Erases.exists_of_trExprS_of_projInfo (henv) (hΔ) (hpi) (h) : ∃ t, Erases env Us Δ e t` (§4.2), four binders | The three-way classification of `Expr.const` (§4.2) is not derivable from `env.WF` alone at the pin (upstream ask 2, §8.3) | Gains a fifth, explicit binder `hclass : ∀ c ci, env.constants c = some ci → (∃ I k, CtorOf env c I k) ∨ (∃ iid np nfs, IndInfo env c iid np nfs) ∨ ConstOrigin env c` — a binder of *this theorem only*, never of `Erases` itself, never of T5 | `ErasesTotal.lean:203-207`; U2.5 |
| **W2b-F5** | `patHead`/`PatOf` (§4.8), printed as live definitions replacing a nonexistent `patsOf` | `IotaInert` — their only consumer — is deleted with `ErasesDecl.ax`'s `hpat` (§4.8 below); `patHead`/`PatOf` are then consumer-free | Left undeleted pending an owning unit (out of scope for U2.5/U2.8's own file lists); assigned to **U3.6**, which owns `ErasesEnv.lean` in W3 | `grep -rn "patHead\|PatOf" LeanToLambdaBox/` empty of consumers; U2.5, U2.8 |
| **W2b-F6** | `CasesOnShape` (§4.3) is defined in `SourceEval.lean`, which the module plan (§7.3) lists as depending only on the carried `Semantics/*`/`Closed`/`Abstract` layer | `CasesOnShape` names `isCasesOnName`, which lives in `Supported.lean`; `SourceEval.lean` therefore gains `import LeanToLambdaBox.Supported`, dragging the whole shipping-code closure (`ErasureSpec`/`CheckerAdequacy`) into `SubjectReduction`'s and `ErasesCorrect`'s import closures (a layering defect, not a soundness gap — no cycle results) | Landed as is (`lake build` unaffected, cost measured at +46 jobs). Fix scheduled for W3: relocate `isCasesOnName`/`lastComponent` out of `Supported.lean` into a small leaf names module, owned by **U3.8** | `SourceEval.lean:1-2`; U2.6 obstruction 3 |

Also landed, general facts about lean4lean's `VEnv.WF'`/`VInductDecl.WF` with no dedicated home
(`SourceEval.lean:362-386`, sorryAx-free): `IsArity.piBody_sort`, `CtorOf.constant_ctorResult`,
`CtorOf.not_indInfo` — the constructor-side twins of U2.5's `wf'_induct_origin`/
`IndInfo.constant_isArity` (`ErasesTotal.lean`). Filed to `doc/upstream-asks.md` for
consolidation (§8.3); natural home is `Origin.lean` once U3.4 lands.

---

## 3. Decisions

### 3.1 The open questions

**Q1 — does the pass layer reproduce `visitExpr` exactly?** **No; state membership in the
composite.** T8 concludes `∃ t₀, Erases env Us Δ e t₀ ∧ Lower Σ⁺ t₀ t` (over the prepared
subject — `prepare_erasure` is monadic, so its output is bound by the run decomposition, never
written as a pure application). Exact
functional equality is attainable only against a compile table keyed on the `Lean.Environment` (a
sixth assumed obligation threaded through every motive), under two extra `Supported` conjuncts,
and resting on an unverified claim that `Meta.inferType` preserves λ binder names. The relation
needs none of the three; it is the papers' own posture; and — decisively — it is the only posture
in which the `.fix` correspondence can be written down at all (§2 F1). *Judges' arguments
settled:* judge 3 preferred A's functional conclusion on fidelity grounds and rated A's exactness
"the design's soft centre" in the same breath; judges 1 and 2 showed the functional reading is
false at the one place it matters. The functional refinement survives as an **optional additive
theorem** (W6): `Lower Σ⁺ t₀ (lowerTerm E t₀)` on the exactness fragment recovers `[S §7.4]`'s
"same result" reading without any of it being load-bearing.

**Q2 — where is Lean's subsingleton criterion derived?** **Nowhere in the first cut: the
prop-case fragment has no subject on emitted output, so it is restricted (N18) and the shipping
gap is raised (F-PROP).** The eraser never sets `OneInductiveBody.propositional` (`Basic.lean:164`
defaults `false`; `register_inductive`, `Erasure.lean:199-240`, never overrides it — measured
683/683 emitted `one_inductive_body` entries across all 72 `.ast` in the tree carry `false`), and
`LowerEnv.inds` transports declarations unchanged, so `isPropositionalInductive` is identically
`false` at every `Σ⁺` and `Σ` a run produces. Consequently a `.case` on a `□` discriminee is
**stuck** at every flag point (`iota` needs a `.construct` spine; `iota_sing` needs the flag) —
verified end-to-end: erased `And.casesOn` at a `Nat` motive fails `peregrine eval` with "branch
not found" — and MetaRocq's `remove_match_on_box` skips it too (`EOptimizePropDiscr.v:35,57` gates
on the same bit). So: restriction **N18** — `Supported` rejects any `casesOn`-like elimination of
a non-informative inductive (`SupportError.propElimIntoData I`, shape-keyed) — and
`ErasesDecl.elim` carries the informativity premise, making the fragment's hypotheses jointly
inhabitable (measured: 0 of the 120 `tCase` nodes in the five fixtures eliminate a `Prop`
inductive, so N18 costs nothing on the corpus). The subsingleton machinery
(`mkElimBodySing`, `ElimBody.sing`, `mkElimBody_iota_sing`, `SubsingletonElim`,
`subsingletonElim_of_wf`) is **deleted** — the last of these was also false as stated: `Acc`
satisfies its hypotheses (`ind_uvars = 1`, `rec_uvars = 2`) and refutes its conclusion, because
lean4lean's `VInductDecl.LargeElim` (`Theory/Inductive.lean:226`) *includes* the `FieldInIndices`
disjunct and no origin lemma can deliver the strengthened form. The honest future shape, recorded
for the day F-PROP lands on `dev/fix`: `largeElim_of_wf` (both disjuncts, = `consts_origin` +
`WF.universes`) plus a decidable no-index-determined-field side condition in `Supported` — the
target's contract (`remove_match_on_box` boxes every branch binder) is strictly stronger than
Lean's kernel criterion, and the difference is a fact about erasure, not proof convenience.
`Eq.rec`/`False.rec` reached as constants are body-less axioms (`ErasesDecl.ax`; a run that
*forces* one has no `SEval` derivation, which is that program's coverage row — F-EQREC); `Decidable` is `Type`-valued (informative — `largeElimClause ``Decidable = some (0,[])`)
and eliminates through the ordinary ι path. On what ships: Lean's code generator refuses `Acc.rec`
(`ToImpure.lean:184`) and `WellFounded.fix` is `noncomputable`, but it does **not** refuse
`Acc.casesOn` at a data motive (measured: compiles and evaluates), so N18 does exclude a construct
Lean ships — at zero cost on the tracked programs, not zero in general.

**Q3 — `_unsafe_rec`: hypothesis or restriction?** **Hypothesis, exactly as N8 words it — a
typing hypothesis, not a second environment.** The one-`VEnv`-extension device (`envC = env +
addDefEq per compiler body`) is **uninhabitable**: a `VEnv.WF` environment grants each constant at
most one defining equation (`WF'.defeqOwn`, machine-checked at the pin,
`scratchpad/gate/d3_defeq_unique.lean`, axioms `[propext, Quot.sound]`), so `le + wf + bodies`
force the compiler body definitionally equal to the kernel body — refuted 31/31 by measurement,
and the equation it smuggles in (`c ≡ F c`, a fixpoint axiom, self-referential and
non-normalizing) is false in the intended model for `partial def`. Instead: **one** `VEnv`, the
kernel `env`; `SEval` takes the compiler-body table as a parameter (`body? : Name → Option Expr`,
the `decls` column of the reified `SourceTable`) and reads it through its `deltaC` arm (§4.3),
whose per-instance side condition `env.IsDefEqU … (mkApps (.const c ls) argsv) (mkApps vb argsv)`
is a **fact about the two bodies**: `rfl`-provable for structural recursion at constructor-headed
recursive arguments (measured 12/12 incl. `Nat.add/mul/sub/pow`, `gate/d3_eqlemmas.lean` —
mirroring λ□'s own `tFix`, which unfolds only there), propositional-only for well-founded
recursion (one class-**E** row), and unavailable for `partial def` (visible in the rung's `hev`
derivation, never hidden inside a `.WF`). The class-**C** binder is N8's own:
`hcb : CompilerBodies lenv env tbl` — every tabled body kernel-typeable at the declared type —
measured inhabitable 33/33 and discharged per program by running lean4lean's checker. The
restriction alternative stays **deleted** from the spec (A5): it covers 0 of 5 benchmarks.

**Q4 — do the emitted eliminator declarations blow up the deliverable?** **No.** The runtime
library lives in `Σ⁺`, which never reaches disk; `LowerEnv` carries the pruning clause and
`Σ = s'.gdecls` is the pruned image. Measured +4.5%…+13.6% un-pruned, **0% pruned**. Size is an
N14 ledger row with the measured `.peano`/hygienic-name split, not a disclaimer.

**Q5 — parameters in constructor applications.** **The frontend keeps them; peregrine drops
them** (`remove_params_optimization`, pass 2 of `verified_lambdabox_pipeline`, at
`with_constructor_as_block = false`). `ErasesDecl.ctor`'s body is `.construct iid k []` and
parameters arrive through `Erases.app`. They are *not* required to be boxed — measured: `OfNat`'s
`n : Nat` parameter is emitted as data (`instOfNatNat = λ n. OfNat.mk □ (tRel 0) (tRel 0)`; 5 of
181 parameter slots across the five programs) — which is harmless because `ERemoveParams.strip`
drops the first `ind_npars` arguments positionally and unconditionally (parameters are not
fields; `cstr_nargs` counts fields only). Measured 982/982 constructor occurrences at exactly
`ind_npars + cstr_nargs`, 0 under-applied — **all 982 in Σ's constant bodies, 0 in the emitted
main term**, which is a bare `.const` in all five programs; the saturation invariant therefore
lives on the environment, and `LBWfPeregrine.etaCtors` states it over env **and** term (§4.9),
with the proof route named (`Lower.ctorApp`'s `hsat`, §4.4). `etaFix` does **not** appear (§2 F2).

**Q6 — is `FirstOrderInd` `[L Def. 14]` / `[L Def. 6]` / `[S §7.3]`?** `fields` is Def. 14
restricted to unapplied field types (matching `firstorder_type`'s `args = []`); `informative` is
the *result-sort* half of Def. 6, whose *conclusion* is `firstorder_no_box`; the shipped
`firstorder_ind` (`PCUICFirstorder.v:59` — the code, not `[S §7.3]`'s prose, which states no sort
condition) is cited as origin and **not transcribed**, because its sort conjunct makes it `false`
on `nat` (reproduced three ways by `vm_compute`; the upstream report is filed in
`doc/upstream-asks.md` at W0). `FirstOrderInd` is typed over `VEnv.WF`'s declaration list — `VEnv`
stores no inductive declarations (`Theory/VEnv.lean:17-23`), so the spec's signature is unwritable
— its closure parameter is **closed** inside the definition (§4.12; a free `fo` made T7/T9
refutable), and the checker is a sound-only fuelled Boolean over the reified table, which is what
criterion 8's "decidable" becomes (A6/A15). Criterion 8's list is narrowed to `Nat`, `Bool`,
`Tree` — because the predicate is chosen at the *declaration* level following `firstorder_ind`'s
shape (`List Nat`/`Nat × Nat` are data-types under Def. 14 itself; they fall outside the
declaration-level, parameter-hostile shape, and all five benchmarks return `Nat`).

**Q7 — `Quot`.** **Restrict (N16).** No `Quot`/`Quot.mk`/`Quot.lift`/`Quot.ind` in a
computationally relevant position, as a `Supported` conjunct over the dependency closure.
`Quot.sound` is *not* excluded (it is `Prop`-typed, hence boxed, hence never reachable in the
emitted program). `ErasesDecl.quot` is **deleted**: it promised an `ElimBody` obligation nothing
constructs, consumes or validates. The eraser emits `Quot` primitives as body-less axioms
(`Erasure.lean:873-877`), so a quotient program erases to a stuck term that still passes
`peregrine validate` — raised, not patched.

**Q8 — compare `Erases` to MetaRocq's `erases` mechanically?** **Ship two tracked tables; drop the
Rocq transport, once, in writing.** `doc/rules-Erases.md` (every rule of `[S Fig. 18]` against
every rule of `Erases`) and `doc/rules-Lower.md` (`Lower`/`LowerFix` against `iota_red`,
`fixSubst`, `optimize`) live next to the definitions and are CI-checked for coverage. The second
table is not optional: after this rework the *pass layer* carries the Lean-specific content and
would otherwise have no external anchor — which is precisely the defect the review found in
`Erases`. A Rocq-side transport reaching the relation is out of scope (`grep -rn Erases rocq/` is
empty today; scoping it would add a second formalisation of `Erases` to keep in sync across
repos). One class-**E** ledger row.

**Q9 — does `Erases` get the `tConstruct` congruence?** **Yes; eleven rules, and `Erases.const`
is restricted to constants that are neither constructors nor inductive type names.** Wave 2
machine-refuted the ten-rule reading at the ι/constructor arm: `SEval.ctorVal` makes a constructor
constant its own value, the ten-rule relation sends that value only to `.const kn` or `.box`, and
`Σ⁺` gives the kername the body `.construct iid k []`, which `WcbvEval` unfolds eagerly
(`erases_correct_needs_tabled_ctor`). Rocq has three syntactic nodes where Lean has one
`Expr.const` — `tConstruct`, `tInd`, `tConst` — so the node distinction becomes premises: `ctor`
keys on `CtorOf` + `IndInfo`, `const` on `ConstOrigin`, all three *exhibiting* the declaration
they read. That is what makes the erasure of a first-order value unique (T7) and what deletes the
stuck image an inductive *type* name used to have (the eraser emits its kername only as an
`.inductiveDecl`); stating the third reading positively is what keeps every introduction site free
of upstream ask 2 (W2 refuter B-F7). `ErasesDecl.ctor` is **deleted**, not kept: it demands
`CtorOf`, and the one constructor-bodied declaration the eraser emits — `Unit.unit`, 1 per file
across `VerifyBench/ast` — is a Lean *definition*, justified by `ErasesDecl.defn` through the new
rule (A22). `Lower.ctorApp` and `CtorDecl` are deleted with it (§4.4), and `ErasesLB.ctor_head`/
`.ctor` become one-line consequences (§4.7). Full argument: `04-AMENDMENT-W2.md` §§4, 7, 8.

**Q10 — one simulation or two?** **One, on the composite, at the emitted `Σ`.** Both halves of the
two-simulation strategy are refuted: T5 at `Σ⁺` by the constructor arm above, and the transport
along `Lower` by `lower_correct_needs_elimBody_head` (false at `Σ⁺ = Σ = []` with every design
guard proved in the same statement) together with `lowerNoEta_fails` (the guard it leaned on is
false on every environment reaching `Nat.succ`). So `Σ⁺` is never an evaluation environment: it is
the pass layer's metadata environment — the unlowered λ□ program, in which eliminators are honest
λ-terms — and evaluation happens only at the emitted `Σ`. The runtime library's *evaluation* theory
(`mkElimBody_iota_fwd/_bwd`, `wcbvEval_mkLambdas_fwd`, `ElimHeadOf`) is deleted; its *shape* is
kept, because that is what `ElimDecl` declares. §5's T5 is the one load-bearing theorem and §4.6 is
scoped to shapes.

**Q11 — how is the ι arm proved without a relevance premise?** **By the box rule's own `Erasable`
witness, plus a call-by-value ι in the source.** `Erases.box` *can* box a proper prefix of an ι
redex — when the motive lands in `Prop` or in a sort — and then the whole redex is erasable
(`erasable_mkApps`, iterating the proved `Erasable.app`), the source value is erasable
(`SEval.defeq` + defeq-invariance), and **both sides box**. Folding the target
`mkApps .box args'` to `.box` needs each argument image to evaluate, because `WcbvEval.app_box`
evaluates the argument it discards (MetaRocq's `eval_box` likewise) — which is why `SEval.iota`
becomes call-by-value in its whole spine (§4.3). The relevant-discriminant fact the arm still needs
— a value of an informative inductive is neither a proof nor a type-former, and a well-typed
constructor value is saturated — is the **theorem** `not_erasable_of_informative`, resting on one
upstream discrimination lemma (`IsDefEqU.const_arity_inv`, §8.3), not a hypothesis: nothing named `IotaRelevant` appears, and no rung
carries a binder for it. The arm's *other* need — that the source spine split is the emitted
`.case` node's split — is not a relevance premise either: it is `CasesOnShape`, the eliminator's
own segmentation read off the inductive declaration, carried by `SEval.iota` on the source side and
by `ErasesDecl.elim` on the target side, where Rocq carries it in `tCase`'s syntax (§4.3, §4.8;
W2 refuter B-F3).

**Q12 — what happens to η-expansion?** **It is not covered; it is restricted (N19).**
*Over*-application is the opposite case and is **covered, not restricted**: `Lower.elimApp` carries
the `extra` list the eraser applies outside the emitted node (`Erasure.lean:828-832`) and
`SEval.iota`'s subject is generalised to match it, at the cost of one existing target lemma
(`wcbvEval_mkApps_head_congr`). It fires — Quicksort has three over-applied `casesOn` spines —
and an over-applied *constructor* spine is excluded instead by `SEval.ctorVal`'s arity bound,
which is `[S Fig. 12]`'s own and which the target enforces anyway (§4.3).
`Lower.ctorEta`/`elimEta` at a non-empty, under-applied prefix are unsound in any architecture: the
expansion moves the supplied arguments under a binder, where weak evaluation never reaches them, so
the source value and the target value are related by no derivation. Re-keying them to the bare head
does not save them either, because `Lower` is compositional: an η-expanded head still composes
under `app` into `mkApps (mkLambdas ns body) args'`, a β-redex target with no bound on nesting that
every spine-inverting arm of T5 would have to collapse (W2 refuter B-F4). **Both arms are deleted**
(§4.4); an under-applied constructor or eliminator occurrence is a `Supported` conjunct decided by
`supportedB` per program (U3.8), and the shipping repair is **F-ETA2** on the `dev/fix` queue —
where the constructor half is a wart rather than a necessity, since applied-form λ□ evaluates a
partially applied constructor spine natively.

### 3.2 The flag chain — the one place the design *removes* work

Measured facts the chain is derived from:

* peregrine's `untyped_transform_pipeline` declares its input evaluation at MetaRocq's
  `EWcbvEval.default_wcbv_flags = ⟨true, true, false⟩` (`EWcbvEval.v:69`; `Transforms.v:151`;
  `eval_eprogram_mapping` ignores the inductives mapping, `ETransform.v:1023`).
* `with_prop_case` is **inert on this frontend's output**: the eraser never sets
  `OneInductiveBody.propositional` (683/683 emitted entries are `false`), and both prop-gated
  rules (`iota_sing`, `proj_prop`) require it `true` — so on every emitted `Σ`,
  `WcbvEval Σ ⟨true,true,false⟩ = WcbvEval Σ ⟨false,true,false⟩`. peregrine's
  `remove_match_on_box` is gated by the same bit (`EOptimizePropDiscr.v:35,57`) and is therefore
  the identity on every declaration this frontend emits: the prop-case obligation is discharged
  locally-by-vacuity, not downstream. (The bit being always-`false` is itself shipping finding
  **F-PROP**, §8.2.)
* every existing simulation statement in the tree — 103 sites across 16 files — is at
  `appliedFlags = ⟨false, true, false⟩`, and `WcbvEval` has no negative `with_prop_case` guard,
  so the weakening to the consumer's point is one ~25-line lemma (mechanised,
  `scratchpad/gate/d6.lean`).

So the capstone's evaluation conjunct is stated at `⟨false, true, false⟩` — the *stronger* point —
and bridged:

```lean
def eraseFlags     : WcbvFlags := ⟨false, true, false⟩  -- deliverable point; = MetaRocq opt_wcbv_flags;
                                                        --   value of today's `appliedFlags` (renamed)
def entryFlags     : WcbvFlags := ⟨true,  true, false⟩  -- = default_wcbv_flags = peregrine's declared input
def blockFlags     : WcbvFlags := ⟨false, true, true⟩   -- value of today's `optFlags` (renamed);
                                                        --   conclusion flag of the proved LBOptimize_correct
def propBlockFlags : WcbvFlags := ⟨true,  true, true⟩   -- value of today's `defaultFlags` (renamed);
                                                        --   LBOptimize_correct's source flag; Optimize.lean only
theorem WcbvEval.propcase_weaken : WcbvEval Γ eraseFlags t v → WcbvEval Γ entryFlags t v  -- class A
```

The old→new map, stated so U0.1 is a mechanical rename: `appliedFlags → eraseFlags`,
`optFlags → blockFlags`, `defaultFlags → propBlockFlags` (all values unchanged);
`targetFlags = ⟨false,false,true⟩` is deleted (zero uses tree-wide; not a MetaRocq point).
Neither `⟨true,true,true⟩` nor `⟨false,false,true⟩` appears anywhere in `EWcbvEval.v` or the
`ErasurePlugin`; `propBlockFlags` exists only so `LBOptimize_correct` (proved) keeps compiling
until W6. Consequences:

* the capstone concludes about **the emitted program `(Σ, t)`** — the artefact — not about
  `LBOptimize Σ t`, which nobody ships; peregrine's obligation is met via `propcase_weaken`;
* `optimize` leaves the critical path. `Optimize.lean` stays wired as the **template** every pass
  follows and as the W6 corollary; the four *non-block* arms it would need (`construct_atom`,
  `construct_app`, `iota`, `proj` — gated on `with_constructor_as_block = false`, already present
  in `Semantics/Eval.lean`, missing only inside `LBOptimize_correct`) are W6, not W2;
* the singleton-elimination companion (`mkElimBody_iota_sing`) is **deleted**: its
  `isPropositionalInductive Σ iid = true` premise is uninhabitable at any `Σ⁺` that lowers to a
  real emitted environment (Q2, N18).

### 3.3 Amendments requested of `00-REFERENCE-SPEC.md`

| # | Spec text | Amendment | Forced by |
|---|---|---|---|
| A1 | §2 T3 lines 213-221 ("verbatim `[L §3.3]` … `Acc.rec` … **inside** the fragment") | the emitted environment marks every inductive non-propositional (F-PROP), so *every* elimination of a `Prop`-valued inductive into data is stuck on the target and is restricted (**N18**, subsuming N17); `Eq.rec`/`False.rec` are inside via the body-less-axiom route (`ErasesDecl.ax`, with F-EQREC as
the coverage row once a run forces one); `Decidable` (Type-valued) is inside via ordinary ι; `And.rec`/`Iff.rec`/`Acc.rec` are **outside** until F-PROP lands | 683/683 `propositional = false`; erased `And.casesOn` fails `peregrine eval`; `largeElimClause ``Acc = some (2,[1])` |
| A2 | §7 criterion 7's example list, and its "derived from the environment" clause | example list becomes `Nat.casesOn`/`Bool.casesOn`/`Decidable.casesOn` (checked `ElimBody` instances) + `Eq.rec`/`False.rec` (axiom route); the Subsingleton condition appears zero times in the first cut — it has no subject (N18/F-PROP), which the criterion's own "demonstrably inside the fragment" test forces | same, plus `subsingletonElim_of_wf` refuted on `Acc` (gate) |
| A3 | §2 T8's conclusion `t = LBCompile.term s'.gdecls t₀` | `∃ Σ⁺ t₀, Erases … t₀ ∧ Lower Σ⁺ t₀ t`, with `ErasesEnv env bo Σ⁺ t₀` and `LowerEnv Σ⁺ s'.gdecls` | 1 ctor declaration (`Unit.unit ↦ tConstruct PUnit 0`, the `CtorDecl` shape) and 0 `casesOn`/rec declarations in all five `.ast`; `elimInline` would have nothing to δ-expand, and the functional conclusion cannot see a fix-bodied `tConst`'s call sites |
| A4 | §2 T3 `ErasesDecl.defn`'s premise `env.constants c = some ⟨_, some body⟩` | `VConstant` carries no body at the pin; the defining body is read from the compiler-body table (N8), `tbl.body? c = some body` | `Theory/VEnv.lean:6-21`; Q3 (`envC` uninhabitable) |
| A5 | §5 N8's "or a restriction to declarations where the two coincide" | delete the restriction alternative | covers 0/5 |
| A6 | §7 criterion 8's list (`List Nat`, `Nat × Nat`) and its word "decidable" | list becomes `Nat`, `Bool`, `Tree`; "decidable" becomes "a sound Boolean checker `firstOrderIndB` discharged `by rfl` on the reified table, under the named binder `htbl`" | the predicate is declaration-level following `firstorder_ind`'s shape (`List Nat` *is* a data-type under Def. 14 — the honest reason is the shape choice plus "all five benchmarks return `Nat`"); `FirstOrderInd` quantifies over `VEnv.WF'` chains and admits no `Decidable` instance |
| A7 | §7 criterion 12 ("matching what `peregrine validate` checks") | "matching `untyped_transform_pipeline`'s precondition **minus** fixpoint η, which is stated separately as `PeregrinePre` and **not** concluded" | `ETransform.v:710-716`; `EEtaExpandedFix.v:47-53`; 4 bare `tFix` bodies in `Arith.ast`; peregrine's own discharge is `Admitted` (`Transforms.v:375`) |
| A8 | §2 T6's `LBPass` (functional) and criterion 5 | passes are relations (`LBPassR`); `correct` keeps `optimize_correct`'s shape with the value existentially quantified | §2 F1 |
| A9 | §2 T6's `LBCompile := optimize ∘ fixIntro ∘ elimInline ∘ ctorInline`, used as both T8's factor and T9's tail | split: `Lower` is T8's factor; `optimize` is an optional post-pass. Removes an unstated idempotence obligation, and `fixIntro` disappears (it has no true `correct`) | §2 F1, §3.2 |
| A10 | §5 N-list | add **N16** (`Quot`), **N18** (no `casesOn`-like elimination of a non-informative inductive — subsumes N17's `Acc` case while F-PROP stands) | Q7, Q2 |
| A11 | §2 T8's four `PrimSpec` fields | the bundle is renamed **`ErasureSpec`** (upstream `Lean4Lean.PrimSpec` exists, `Verify/Typing/Expr.lean:315`, and this tree opens `Lean4Lean` pervasively) and has six fields: `env_connect`, `lookup_adequate`, `fresh_names`, `oracle_refl`, `oracle_meta`, `decl_adequate`; table adequacy is the separate named binder `htbl` (a `Prop`-valued structure cannot hold `tbl` as a field, and an unbound `tbl` auto-binds to a false ∀) | Q6; §2 F4; gate G-D4/G-D5 |
| A12 | §2 T9's observable conjunct | value side is the **composite**, not `Erases`; and the conjunct is quantified over closed first-order argument spines | §2 F3, F5 |
| A13 | §2 T1's "the `optimize` pass (T6) discharges `with_prop_case`, landing the deliverable at `⟨false,true,false⟩`" | the deliverable **is stated at** `⟨false,true,false⟩` directly (prop-case is inert on emitted output) and `propcase_weaken` bridges to the consumer's `⟨true,true,false⟩`; `optimize` is optional | §3.2 |
| A14 | §7 criterion 13 ("every hypothesis of T9 simultaneously inhabited by a checked term") | "every class-**C** hypothesis of T9 inhabited by a checked term; `hrun`, `htbl` and `ErasureSpec`'s class-**D** fields are permanent named binders mechanised externally by `lake exe green-check`; `hwt`/`hty` per F17's schedule and named fallback; **`hev` is class **C** and uninhabited at G1–G4** — `Green.lean:186` is a binder no rung discharges, G3's `green_G5` is the first rung that constructs an `SEval` derivation, and `test/ledger.expected` and `doc/trust.md` carry the row until then" | F17, F18; `Void IO.RealWorld` is opaque; the bundle's fields model opaque `Lean.Environment`/`Meta` primitives; W2 second-round refuter F4 |
| A15 | §7 criteria 8 and 11's "decidable"/"decides" | "`by rfl` on the `reify%`-spliced `SourceTable`, sound under the named binder `htbl`" | §2 F4: no term denotes the ambient environment |
| A16 | §7 criterion 9 ("`oracle_sound` … discharged rather than assumed") | "discharged on its kernel-reflection arm (`oracle_refl`, class **B**); the `isErasableMeta` fallback and the polymorphic-scope arm remain one named class-**D** field (`oracle_meta`) with a ledger row" — the reduction is real but partial, and saying so costs one field | §4.10; measured 0 fallback hits / 139,196 constants |
| A17 | §7 criteria 1-2 ("exactly ten rules"; "no rule produces `.construct`, `.case` or `.fix`") | eleven rules; the prohibition stands for `.case`/`.fix` and is lifted for `.construct` **at the bare head**, which is `[S Fig. 18]`'s own `tConstruct` congruence | Q9; `erases_correct_needs_tabled_ctor` |
| A18 | §7 criterion 6 ("exactly five hypotheses") | exactly MetaRocq's **five** — `wf`, `welltyped`, evaluation, `erases`, `erases_deps` — plus `LowerEnv`, which MetaRocq has no analogue of because it has no pass layer and which carries the pass layer's environment well-formedness (`ClosedBodies Σ⁺`, `BlockBodiesLambda Σ⁺`) as clauses rather than binders. **No `axiom_free`**: `SEval`'s value arms are `[S Fig. 12]`'s `value_head`, so a body-less plain constant has no source value. Seven binders, six premises; the name prohibition is unchanged | `erases_correct_needs_tabled`; W2 refuters A-F2/A-F3/B-F2 |
| A19 | §2 T5's conclusion at `Σ⁺` | the simulation is stated at the **emitted** `Σ`; `Σ⁺` indexes the pass relation only | Q10 |
| A20 | §2 T4's `SEval` value and ι rules | values are `[S Fig. 12]`'s `value_head` — constructor spines (`CtorOf`), inductive-type-name spines (`IndInfo`), sorts, Π-types — and nothing else constant-headed; ι is call-by-value in the whole spine (restriction **N20**) and split where the source theory splits it (`CasesOnShape`) | Q11, §4.3; W2 refuters A-F5/B-F3/B-F9 |
| A21 | §2 T6's `elimInline` row ("η-expanding under-applied heads") | η-expansion is **not covered**: both η arms are deleted from `Lower` (they compose under `app` into unbounded β-redex targets), their coverage becomes restriction **N19** — decided by `supportedB`, U3.8 — and shipping finding **F-ETA2** | Q12; W2 refuter B-F4 |
| A22 | §2 T3's `ErasesDecl` arm list | `ctor` is deleted — it demands `CtorOf`, and the single constructor-bodied declaration in the five programs (`Unit.unit`) is a *definition*, so the arm can justify no entry any run produces — and `elim` gains the eliminator's source-side segmentation `CasesOnShape`, which makes the emitted `.case` node's shape a fact about the source theory rather than an assumption | W2 refuters A-F1/B-F3 |

### 3.4 Acceptance criteria — how each is met

1-2 (eleven rules, no `.case`/`.fix`; as amended by A17): §4.2 verbatim; `ErasureContext.lean` is
deleted, so the grep is empty by construction. CI grep over `Erases.lean` for `\.case|\.fix`, and
the `erasesArms%` guard pins the eleven names.
3 (rule table): `doc/rules-Erases.md`, plus `doc/rules-Lower.md`. 4 (one `SEval`, one environment
relation, one bundle, one ledger): §4.3, §4.8, §4.10, §4.14 + CI greps. 5 (pass shape + guards +
composition): §4.4-§4.7, §5 T6, as amended by A8. 6 (T5's hypotheses, as amended by
A18): §5 T5 literally — MetaRocq's five plus `LowerEnv`, none named from the prohibited list; the
fixture `test/t5.expected` pins the statement from W3 on. 7 (Subsingleton): zero
occurrences in the first cut, as amended by A2 — the condition has no subject on emitted output
(Q2, N18, F-PROP). 8 (`FirstOrderInd`): §4.12, `by rfl` on the reified table under `htbl`, as
amended by A6/A15. 9 (`OracleDischarge` in the closure, `oracle_refl` discharged): §4.10, as
amended by A16. 10 (`sort_erasable`/`forallE_erasable` + the panic table): §4.2, `doc/panics.md` —
this pair is also how N12 is met (its option 2: the per-site table plus `Supported`; there is no
`Panicked` predicate and no `hnp` binder). 11 (`Supported` decidable, sparse-`casesOn` visible):
§4.11, and `supportedB` *names* the hole. 12 (`LBWfPeregrine` in the conclusion): §4.9, as
amended by A7. 13-14 (non-vacuity, coverage table): §6 and `02-PLAN.md`'s per-wave green
obligation, as amended by A14. 15-17 (ledger, `sorryAx` roots, no `sorry`/`axiom`): §4.14; the
class-**C** binders that appear in stated theorems are `hcfg`, `hcb`, `hsup` (criterion 17;
`hax` is retired with `ErasableAxioms`, `04-AMENDMENT-W2.md` §8). 18-21 (hygiene; no `Lean4Lean`-namespace declaration): §9; criterion 21 is met from W3 (F16,
U3.4). 22 (delivery): W5.

---

## 4. Core definitions — exact signatures

Written against the pinned lean4lean rev (`lake-manifest.json`) and `LeanToLambdaBox/Basic.lean`
at `dev/verify`.
`GlobalDeclarations = List (Kername × GlobalDecl)` (`Basic.lean:190`); `envLookup` is
`Semantics/Substitution.lean:35`.

**Two signature constraints, machine-checked this session** (`scratchpad/probe/lowerfix2.lean`,
`forall2b.lean`), binding on every implementer:

* A premise of an inductive that mentions the inductive **under `∃` or `∧`** is rejected by the
  kernel: `invalid nested inductive datatype 'Exists', nested inductive datatypes parameters
  cannot contain local variables`. Block premises are therefore stated with an **explicit list of
  lowered bodies** and separate `∀`-clauses.
* `List.Forall₂` is not in scope at this toolchain from `Semantics.Metatheory` (nor from
  `import Lean`); it is reachable only through `IotaPattern.lean`'s import chain, and as a premise
  it is a nested-inductive occurrence anyway. **All list premises inside `Lower` and `Erases` use
  the indexed form** `hlen : xs'.length = xs.length` + `∀ i, i < xs.length → R xs[i]! xs'[i]!`,
  which is probe-checked to produce a usable recursor with the induction hypothesis
  `∀ i, i < xs.length → motive xs[i]! xs'[i]!`.
* `Σ` is a **reserved token** in Lean 4 (the sigma binder): the snippets below use it as
  mathematical notation, but in the actual `.lean` files the λ□-environment metavariable is
  written `Γ` (the existing `Semantics/` convention) or `Sg`. An implementer transcribing a
  snippet verbatim will hit a parse error at the first binder named over `Σ` — this is why the
  original probe `scratchpad/probe/lowerfix2.lean` never elaborated its final example
  (repaired at `scratchpad/gate/lowerfix2_fixed.lean`, which does hold).

### 4.1 Flags — `Semantics/Flags.lean`

As §3.2. The module header is rewritten to state the current fact (it currently asserts block
form, which is the opposite of what every capstone runs).

### 4.2 `Erases` — T2, eleven rules — `Erases.lean`

```lean
/-- `[S Fig. 18]` transposed to `Lean.Expr`: lean4lean's `TrExprS` with the target `VExpr`
replaced by `LBTerm`, `sort`/`forallE` absorbed into `box`, and `box` added. Eleven rules, no
registry. The only side conditions are the ones Rocq's syntax carries for free: Lean writes
`tConstruct`, `tInd` and `tConst` all as `Expr.const`, so `ctor` and `const` say which. -/
inductive Erases (env : VEnv) (Us : List Name) : VLCtx → Expr → LBTerm → Prop
  | box   {Δ e ve} (htr : TrExprS env Us Δ e ve)
          (her : Erasable env Us.length Δ.toCtx ve) :
          Erases env Us Δ e .box
  | bvar  {Δ i e' A} (h : Δ.find? (.inl i) = some (e', A)) :
          Erases env Us Δ (.bvar i) (.bvar i)
  | fvar  {Δ x e' A} (h : Δ.find? (.inr x) = some (e', A)) :
          Erases env Us Δ (.fvar x) (.fvar x)
  | ctor  {Δ c us I iid k np nfs} (hc : CtorOf env c I k) (hi : IndInfo env I iid np nfs) :
          Erases env Us Δ (.const c us) (.construct iid k [])
  /-- Rocq's `tConst`: a constant declared as a definition, an opaque constant or an axiom.
      `ConstOrigin` **exhibits** the declaration, exactly as `CtorOf` and `IndInfo` do for the
      other two readings, so every introduction site (the rungs, T8's bridge) discharges it from
      the declaration list it already has; the *exclusion* direction is upstream ask 2, consumed
      as a theorem by T7 and by the ι arm's head step only (W2 refuter B-F7). -/
  | const {Δ c us ci} (hc : env.constants c = some ci) (ho : ConstOrigin env c) :
          Erases env Us Δ (.const c us) (.const (toKername c))
  | app   {Δ f f' a a'} (hf : Erases env Us Δ f f') (ha : Erases env Us Δ a a') :
          Erases env Us Δ (.app f a) (.app f' a')
  | lam   {Δ n ty bi b b'} {ty' : VExpr} (hty : TrExprS env Us Δ ty ty')
          (hb : Erases env Us ((none, .vlam ty') :: Δ) b b') :
          Erases env Us Δ (.lam n ty b bi) (.lambda (.named n.toString) b')
  | letE  {Δ n ty nd v v' b b'} {ty' val' : VExpr}
          (hty : TrExprS env Us Δ ty ty') (hval : TrExprS env Us Δ v val')
          (hv : Erases env Us Δ v v')
          (hb : Erases env Us ((none, .vlet ty' val') :: Δ) b b') :
          Erases env Us Δ (.letE n ty v b nd) (.letIn (.named n.toString) v' b')
  | proj  {Δ S i e t iid np nf} (hs : IndInfo env S iid np [nf]) (hi : i < nf)
          (hd : Erases env Us Δ e t) :
          Erases env Us Δ (.proj S i e) (.proj ⟨iid, np, i⟩ t)
  | lit   {Δ l t} (hcl : env.ContainsLits l) (h : Erases env Us Δ l.toConstructor t) :
          Erases env Us Δ (.lit l) t
  | mdata {Δ d e t} (h : Erases env Us Δ e t) : Erases env Us Δ (.mdata d e) t
```

The three readings of `Expr.const` are three declaration kinds, each *exhibited* off a declaration
list of `VEnv.WF'` below `env`. `CtorOf` moves here from `ErasesEnv.lean` (the `ctor` rule reads
it); `IndInfo` is already here (§4.6); `ConstOrigin` is new. All three elaborate against the tree
(`scratchpad/amend/p3_w2rev.lean`, exit 0).

```lean
/-- Does this declaration introduce `c` as a plain constant? -/
def VDeclDefines : VDecl → Name → Prop
  | .axiom cv, c => cv.name = c   | .def dv, c => dv.name = c
  | .opaque dv, c => dv.name = c  | .example dv, c => dv.name = c
  | .mutualDef dvs, c => ∃ dv ∈ dvs, dv.name = c
  | .quot, _ => False             | .induct _, _ => False        -- `quot` is N16

/-- Rocq's `tConst` reading: `c` is declared as a definition, an opaque constant or an axiom. -/
def ConstOrigin (env : VEnv) (c : Name) : Prop :=
  ∃ ds env₀ d, VEnv.WF' ds env₀ ∧ d ∈ ds ∧ env₀ ≤ env ∧ VDeclDefines d c
```

Five notes, each answering a judge or a Wave-2 refutation. (i) `bvar`/`fvar` keep the `Δ.find?`
premise (F9); the transport lemmas' arms use it and without it the relation admits out-of-scope
indices, which would break `erases_subst`, `LBClosed` and T7. (ii) `const` takes no `Kername`
parameter and no registry premise: `toKername` (`Basic.lean:34`) is a *function*, which lets
`BridgeInv.knames` and `.consts` collapse into the existing `CanonicalConstants`
(`ErasureRun.lean:1482`). Its `ConstOrigin` premise is Rocq's node distinction, not a guard on
derivations: without it `.const c us` erases both to `.const (toKername c)` and (for a
constructor) to `.construct iid k []`, and T7's uniqueness on first-order values is false; and an
inductive *type* name keeps an image the target is stuck on, since the eraser emits its kername
only as an `.inductiveDecl` (Q9). It is stated **positively** — the defining declaration exhibited,
as `CtorOf`/`IndInfo` exhibit theirs — so that introduction is a fixture fact and only the
exclusion direction needs upstream ask 2 (W2 refuter B-F7). (v) `ctor` is `[S Fig. 18]`'s `tConstruct` congruence at the bare
head — arguments arrive through `app`, `.construct` carries none (Q5) — and `iid`/`k` are functions
of the block, exactly as `toKername` is of the name.
(iii) `proj` keys on `IndInfo` (§4.6) — the environment predicate — and deliberately carries no
`TrExprS` premise, because `TrProj.uniq` yields `IsDefEqU`, not equality. (iv) `lam`/`letE` record
the **source** name: the ASCII-graphic filter in `fvar_to_name` (`Erasure.lean:245-252`, "otherwise
the λbox parser will complain") is a printer constraint, and it reappears as
`LBWfPeregrine.asciiNames`, not inside the specification.

Carried metatheory (statements unchanged except for dropping the `Γ` index): `erases_shift`,
`erases_subst`, `Erases.abstract`, `Erases.uninstantiateN`, `Erases.thin_vlet`, `erases_weakFV*`,
`erases_uniform_*`. Nine of fifteen arms survive per lemma; six die with their rules.

**Inversion.** Every downstream consumer that cases on an `Erases` derivation needs the two-way
form, so each rule has an `*_inv` twin sharing one box alternative:

```lean
/-- The box alternative every inversion lemma shares. -/
def ErasesBox (env : VEnv) (Us : List Name) (Δ : VLCtx) (e : Expr) (t : LBTerm) : Prop :=
  (∃ ve, TrExprS env Us Δ e ve ∧ Erasable env Us.length Δ.toCtx ve) ∧ t = .box

theorem Erases.bvar_inv {i} (h : Erases env Us Δ (.bvar i) t) :
    ErasesBox env Us Δ (.bvar i) t ∨ ((∃ e' A, Δ.find? (.inl i) = some (e', A)) ∧ t = .bvar i)
theorem Erases.proj_inv {S i e} (h : Erases env Us Δ (.proj S i e) t) :
    ErasesBox env Us Δ (.proj S i e) t ∨
      (∃ iid np nf d, IndInfo env S iid np [nf] ∧ i < nf ∧ Erases env Us Δ e d ∧
        t = .proj ⟨iid, np, i⟩ d)
-- and one `*_inv` lemma per rule: fvar, ctor, const, app, lam, letE, lit, mdata, plus `sort_inv`
-- and `forallE_inv` (both `ErasesBox`-only, since `Erases` has no `sort`/`forallE` rule).
-- `const_inv` now also reports the two negative premises, which is what the ι arm inverts with.
```

`IndInfo` (used by `Erases.proj` and `.proj_inv`) reads the block data off the declaration list
underneath `env`, not off `env` itself — `VEnv` stores no inductive declarations
(`Theory/VEnv.lean:17-23`):

```lean
/-- `env`'s inductive block data for `I`, in λ□ coordinates: some well-formed declaration list
below `env` contains the block, `iid` names it by the eraser's own block-kername convention, and
`nfs` is each constructor's field count. Quantifying over an environment `env₀ ≤ env` rather than
over `env` itself is what makes `IndInfo.mono` provable — `VEnv.WF'` is not itself monotone in
`env`, so `env`'s own declaration list is not always available at `env'`, but the one that already
sits below `env` sits below `env'` too. Declared here (not in `ElimBody.lean`) because
`Erases.proj` is its first consumer. -/
structure IndInfo (env : VEnv) (I : Name) (iid : InductiveId) (np : Nat) (nfs : List Nat) : Prop
    where
  block : ∃ (ds : List VDecl) (env₀ : VEnv) (decl : VInductDecl) (t : VInductiveType),
    VEnv.WF' ds env₀ ∧ VDecl.induct decl ∈ ds ∧ env₀ ≤ env ∧
    decl.types[iid.idx]? = some t ∧ t.name = I ∧
    iid.mutualBlockName = indBlockKername (decl.types.map (·.name)) ∧
    decl.nparams = np ∧ ctorFieldCounts np t = nfs

theorem IndInfo.of_wf' {env env₀ I iid np nfs ds decl t} (hds : VEnv.WF' ds env₀)
    (hd : VDecl.induct decl ∈ ds) (hle : env₀ ≤ env) (ht : decl.types[iid.idx]? = some t)
    (hname : t.name = I) (hkn : iid.mutualBlockName = indBlockKername (decl.types.map (·.name)))
    (hnp : decl.nparams = np) (hnfs : ctorFieldCounts np t = nfs) : IndInfo env I iid np nfs
theorem IndInfo.mono {env env' I iid np nfs} (hle : env ≤ env') (h : IndInfo env I iid np nfs) :
    IndInfo env' I iid np nfs
```

There is no `SubsingletonElim` clause and no `sing` disjunct here (Q2, N18, F-PROP): see §4.6.

New, and load-bearing (criterion 10 earns its place here: the composite's `cases` rule must erase
the arguments the `.case` node drops) — in `ErasesTotal.lean`:

```lean
theorem Erasable.mono (hle : env ≤ env') {U : Nat} {Γ : List VExpr} {e : VExpr}
    (h : Erasable env U Γ e) : Erasable env' U Γ e
theorem Erases.mono (hle : env ≤ env') {e : Expr} {t : LBTerm}
    (h : Erases env Us Δ e t) : Erases env' Us Δ e t
theorem Erases.sort_erasable (_henv : env.WF) {u : Level} {ve : VExpr}
    (h : TrExprS env Us Δ (.sort u) ve) : Erasable env Us.length Δ.toCtx ve
theorem Erases.forallE_erasable (henv : env.WF) {n : Name} {A B : Expr} {bi : BinderInfo}
    {ve : VExpr} (hΔ : VLCtx.WF env Us.length Δ)
    (h : TrExprS env Us Δ (.forallE n A B bi) ve) : Erasable env Us.length Δ.toCtx ve

/-- Block data for every projection head: free everywhere but `.proj`, where it is `IndInfo`.
`Literal.toConstructor` is projection-free, so `lit` needs no clause of its own
(`ProjInfo.toConstructor`). -/
inductive ProjInfo (env : VEnv) : Expr → Prop
theorem ProjInfo.toConstructor {env : VEnv} (l : Literal) : ProjInfo env l.toConstructor

/-- The largest true fragment of totality. Unconditional totality is not provable: at the `proj`
case, inverting `TrExprS.proj` yields a `TrProj` witness, not an `IndInfo`, and closing that gap
needs an application-spine inversion (`HasType.app_inv`, `Theory/Typing/Strong.lean:886`) that
exists only under `OrderedStrong`, whose only introduction (`VEnv.WF.orderedStrong`,
`EnvLemmas.lean:338`) rests on `VEnv.WF.patsStrong := sorry` (`EnvLemmas.lean:334`) — the exact
`sorryAx` root `00-REFERENCE-SPEC.md` §1 already names. `ProjInfo` is the side premise that keeps
this lemma off that route. -/
theorem Erases.exists_of_trExprS_of_projInfo (henv : env.WF)
    -- the totality hypothesis, a binder of THIS theorem only — never of `Erases`, never of T5.
    -- Distinguishes the three readings of `Expr.const` (§2.4 finding W2b-F4); U3.4's `Origin.lean`
    -- discharges it as `consts_classified` once the pin bump lands (§8.3).
    (hclass : ∀ c ci, env.constants c = some ci →
      (∃ I k, CtorOf env c I k) ∨ (∃ iid np nfs, IndInfo env c iid np nfs) ∨ ConstOrigin env c)
    {e : Expr} {ve : VExpr}
    (hΔ : VLCtx.WF env Us.length Δ) (hpi : ProjInfo env e)
    (h : TrExprS env Us Δ e ve) : ∃ t, Erases env Us Δ e t
```

### 4.3 `SEval`, `SEvalFlags`, `CompilerBodies` — T4 — `SourceEval.lean`

```lean
structure SEvalFlags where beta, delta, zeta, iota, proj, lit : Bool
  deriving DecidableEq
instance : LE SEvalFlags := ⟨fun a b => (a.beta → b.beta) ∧ … ∧ (a.lit → b.lit)⟩
def deltaOnly : SEvalFlags := ⟨false, true, false, false, false, false⟩
def fullFlags : SEvalFlags := ⟨true, true, true, true, true, true⟩

/-- The one source evaluation: weak call-by-value big-step over `Lean.Expr`, parameterised by
which reductions are enabled `[S §5.6]` and by the compiler-body table `bo` (N8). **Uniformly**
call-by-value: every arm evaluates the subterms of its subject before contracting, the ι arm
included (A20). δ is the arm `deltaC` below: it unfolds the body the **compiler** compiles — the same
body the eraser reads — never the kernel equation, so the two sides of T5 step in lockstep and no
equation-lemma transport is ever needed. Its side condition keeps T4's `IsDefEqU` conclusion:
`rfl`-provable for structural recursion at constructor-headed recursive arguments (measured
12/12 incl. `Nat.add/mul/sub/pow`), propositional for well-founded recursion (class-**E** row),
unavailable for `partial def` — visibly, in the rung's own `hev` derivation. -/
/-- `env.IsDefEqU` between the translations of `e₁` and `e₂`, with both translations
existentially bound rather than universally quantified over every translation. The universal
form is inert for `deltaC`'s purpose (the induction hypothesis for `hcont` needs a translation of
the *reduct*, and a premise quantified over given translations supplies none) and is strictly
weaker at a context with no translation at all: `forall_form_not_stepDefeq` exhibits it holding
vacuously true of `.bvar 0` at `Δ = []`, where `StepDefeq` itself is false
(`trExprS_bvar_nil_elim`). `StepDefeq.uniq_form` recovers the universal reading from this one, by
`TrExprS.uniq`, under `env.WF` and `VLCtx.WF`. -/
def StepDefeq (env : VEnv) (Us : List Name) (Δ : VLCtx) (e₁ e₂ : Expr) : Prop :=
  ∃ v₁ v₂, TrExprS env Us Δ e₁ v₁ ∧ TrExprS env Us Δ e₂ v₂ ∧ env.IsDefEqU Us.length Δ.toCtx v₁ v₂

inductive SEval (env : VEnv) (bo : Name → Option Expr) (Us : List Name) (fl : SEvalFlags) :
    VLCtx → Expr → Expr → Prop
  -- among the arms:
  | deltaC {Δ c us ups args argsv b b' v} (hfl : fl.delta)
      (hb : bo c = some b) (hinst : b' = b.instantiateLevelParams ups us)
      -- `hnd` mirrors the eraser's own dispatch: `visitCases` (`Erasure.lean:768`) never visits
      -- a `casesOn` body, so neither does δ here. It is not optional — `reify%` tables a
      -- `.defnInfo` with a body (`Witness/SourceTable.lean:213-216`) and `Nat.casesOn` is one, so
      -- without it a saturated eliminator spine has a second derivation that unfolds the
      -- eliminator, and T5's δ arm would owe the `ElimBody` evaluation theory §7.4 retires (N21).
      (hnd : ∀ I dp nm, ¬ CasesOnShape env c I dp nm)
      (hlen : argsv.length = args.length)
      (hargs : ∀ i, i < args.length → SEval env bo Us fl Δ args[i]! argsv[i]!)
      (hdef : StepDefeq env Us Δ (mkApps (.const c us) argsv) (mkApps b' argsv))
      (hcont : SEval env bo Us fl Δ (mkApps b' argsv) v) :
      SEval env bo Us fl Δ (mkApps (.const c us) args) v
  /-- ι, call-by-value in the **whole** spine: the dropped prefix, the unselected minors and any
      over-application are arguments of an application, and call-by-value evaluates arguments. The
      premises are what the simulation's boxed-ι case consumes — the image of such a redex is
      `mkApps .box args'`, and `WcbvEval.app_box` evaluates the argument it discards (Q11). -/
  | iota {Δ con us I pre prev disc minors minorsv extra extrav ctor cus cargs np cidx r}
      (hfl : fl.iota)
      -- the split, from the source theory: `hsh` is how many arguments precede the major premise
      -- and how many minors follow it, read off `I`'s own declaration; `hct` is which minor the
      -- matched constructor selects. Rocq's `tCase` carries both in its syntax; without them
      -- nothing ties this derivation's split to the emitted `.case` node (W2 refuter B-F3), and
      -- `CasesOnShape.inj` is what makes the split unique once `extra` is admitted.
      (hsh : CasesOnShape env con I pre.length minors.length)
      -- the head's *reading*. `CasesOnShape` constrains `con`'s name and `I`'s declaration and
      -- nothing else — it transports to any name with the same `isCasesOnName` verdict and prefix
      -- (`scratchpad/refute2/step3.lean`) — so without `ho` the head may still erase by
      -- `Erases.ctor` and T5's ι head step does not follow.
      (ho : ConstOrigin env con)
      (hct : CtorOf env ctor I cidx)
      (hpre : prev.length = pre.length)
      (hpres : ∀ i, i < pre.length → SEval env bo Us fl Δ pre[i]! prev[i]!)
      (hdiscr : SEval env bo Us fl Δ disc (mkApps (.const ctor cus) cargs))
      (hmin : minorsv.length = minors.length)
      (hmins : ∀ i, i < minors.length → SEval env bo Us fl Δ minors[i]! minorsv[i]!)
      -- over-application rides outside the node, exactly as `visitCases` emits it
      -- (`Erasure.lean:828-832`) and as `Lower.elimApp`'s `extra` carries it; measured firing on
      -- three `casesOn` spines in Quicksort.
      (hxlen : extrav.length = extra.length)
      (hxs : ∀ i, i < extra.length → SEval env bo Us fl Δ extra[i]! extrav[i]!)
      (hidx : cidx < minors.length)
      (hdef : StepDefeq env Us Δ (mkApps (.const con us) (pre ++ disc :: minors ++ extra))
        (mkApps minors[cidx]! (cargs.drop np ++ extra)))
      (hcont : SEval env bo Us fl Δ (mkApps minors[cidx]! (cargs.drop np ++ extra)) r) :
      SEval env bo Us fl Δ (mkApps (.const con us) (pre ++ disc :: minors ++ extra)) r
  /-- `[S Fig. 12]`'s `value_head_cstr`: a constructor spine within the constructor's arity is a
      value once its arguments are. Keyed on the source theory's classification — not on the
      compiler table, not on a name test: a `casesOn` spine is not a value because `casesOn` is not
      a constructor. A body-less *plain* constant then has no value at all, which is PCUIC's
      treatment of an axiom and what removes the axiom-freedom premise W2-R2 seemed to force (A18).
      `harity` is Fig. 12's own `nargs ≤ cstr_arity`, here `np + nfs[k]` off `IndInfo`: the target
      is stuck on an over-applied constructor spine (`WcbvEval.construct_app` fires only while
      `args.length < ar`, `Semantics/Eval.lean:130-136`), and this is what gives T5's `ctorVal` arm
      its no-over-application fact without an upstream lemma. -/
  | ctorVal {Δ cn us I iid k np nfs args argsv} (hc : CtorOf env cn I k)
      (hi : IndInfo env I iid np nfs) (harity : args.length ≤ np + nfs[k]!)
      (hlen : argsv.length = args.length)
      (hargs : ∀ i, i < args.length → SEval env bo Us fl Δ args[i]! argsv[i]!) :
      SEval env bo Us fl Δ (mkApps (.const cn us) args) (mkApps (.const cn us) argsv)
  /-- `value_head_ind`: an inductive type name applied to arguments is a value. Not optional —
      `deltaC` and `ctorVal` evaluate their arguments, and a polymorphic call's type argument is
      exactly this shape (`@List.length Nat xs`). -/
  | indVal {Δ cn us iid np nfs args argsv} (hi : IndInfo env cn iid np nfs)
      (hlen : argsv.length = args.length)
      (hargs : ∀ i, i < args.length → SEval env bo Us fl Δ args[i]! argsv[i]!) :
      SEval env bo Us fl Δ (mkApps (.const cn us) args) (mkApps (.const cn us) argsv)
  /-- Types are values: weak evaluation does not enter a binder, and both shapes erase to `.box`
      (`Erases.sort_erasable`, `Erases.forallE_erasable`). Not a cost of A20: `deltaC` and
      `ctorVal` already evaluate every argument, so without these arms `SEval` cannot evaluate any
      δ redex one of whose arguments is a sort or a Π — `@id (Nat → Nat) f`, and every polymorphic
      call at a function type. -/
  | sort {Δ u} : SEval env bo Us fl Δ (.sort u) (.sort u)
  | forallE {Δ n ty b bi} : SEval env bo Us fl Δ (.forallE n ty b bi) (.forallE n ty b bi)

/-- The `casesOn` of `I`, at the segmentation `I`'s own block fixes: `dp` arguments before the
major premise (parameters, motive, indices), then one minor per constructor. Read off the
**inductive declaration**, not off `VEnv.pats`, so that it does not depend on how the pattern table
is populated (R17); it is the data Rocq's `tCase` node carries in its syntax, and it is what ties
`SEval.iota`'s spine split to the emitted `.case` node through `ErasesDecl.elim` (§4.8). -/
def CasesOnShape (env : VEnv) (c I : Name) (dp nm : Nat) : Prop :=
  isCasesOnName c = true ∧ c.getPrefix = I ∧
  ∃ ds env₀ decl t, VEnv.WF' ds env₀ ∧ VDecl.induct decl ∈ ds ∧ env₀ ≤ env ∧
    t ∈ decl.types ∧ t.name = I ∧
    dp = decl.nparams + 1 + (t.type.piArity - decl.nparams) ∧ nm = t.ctors.length
```

`isCasesOnName` (`Supported.lean:151`) is presently the only reason `SourceEval.lean` imports
`Supported.lean` — a layering defect, not a soundness gap (§2.4 finding W2b-F6): it drags the
shipping-code closure (`ErasureSpec`/`CheckerAdequacy`) into `SubjectReduction`'s and
`ErasesCorrect`'s import closures a wave early. Fix scheduled for U3.8 (§7.3): relocate
`isCasesOnName`/`lastComponent` into a leaf names module neither file's closure need drag in.

Three general facts about lean4lean's `VEnv.WF'`/`VInductDecl.WF` — the constructor-side twins of
`ErasesTotal.lean`'s `wf'_induct_origin`/`IndInfo.constant_isArity` — are parked here for want of
a dedicated home, sorryAx-free at the pin (§2.4):

```lean
theorem IsArity.piBody_sort {A : VExpr} (h : IsArity A) : ∃ u, A.piBody = .sort u
theorem CtorOf.constant_ctorResult {env c I k} (h : CtorOf env c I k) :
    ∃ ci np nf nind, env.constants c = some ci ∧ ci.type.CtorResult I np nf nind
theorem CtorOf.not_indInfo {env c I k iid np nfs} (hc : CtorOf env c I k) :
    ¬ IndInfo env c iid np nfs
```

Filed to `doc/upstream-asks.md` for consolidation; natural home is `Origin.lean` once U3.4 lands.

```lean
theorem SEval.mono  (h : fl ≤ fl') : SEval env bo Us fl Δ e v → SEval env bo Us fl' Δ e v
-- REFUTED as printed (§2.4 finding W2b-F2): `deltaC`'s `hnd` is negative in `env`, and
-- `CasesOnShape` is monotone the wrong way for it, so an extension that newly declares a
-- same-named eliminator shape can drop a derivation. Landed with an added premise; no consumer
-- exists tree-wide.
theorem SEval.le    (h : env ≤ env')
    (hcs : ∀ c I dp nm, CasesOnShape env' c I dp nm → CasesOnShape env c I dp nm) :
    SEval env bo Us fl Δ e v → SEval env' bo Us fl Δ e v
/-- No flag restriction and no `hcb`/`lenv` binder: `CompilerBodies` is not consumed by this
proof (the δ arm's obligation is `hdef`, already discharged at the arm), so keeping the binder
would leave it unused in a class-**B** theorem. Strictly stronger than the design's printed
signature for exactly that reason. -/
theorem SEval.defeq (henv : env.WF) (hΔ : VLCtx.WF env Us.length Δ)
    (htr : TrExprS env Us Δ e ve) (hev : SEval env bo Us fl Δ e v) :
    ∃ vv, TrExprS env Us Δ v vv ∧ env.IsDefEqU Us.length Δ.toCtx ve vv
```

`SEvalFlags` is the **widening axis of the schedule** (design C's device, adopted): T5 is proved
first at `deltaOnly`, then at `βζδ + lit + proj`, then at `fullFlags`, with `SEval.mono` as the
inclusion and *the statement never changing from W3 on* (§3.4, criterion 6). `SEval.defeq`
unifies `SubjectReduction{,Full,Iota}`: the β/ζ/δ arms are written once (today three times, two
byte-identical at `SubjectReductionFull.lean:398-430` = `SubjectReductionIota.lean:157-189`) via
the abstract-`P` spine schema at `SubjectReductionFull.lean:309`. It already holds at
`fullFlags`, so the ι and projection arms carry their obligation in their own `StepDefeq` side
condition rather than in a flag restriction on T4; `SEval.defeq` is already at the point T5 needs.

```lean
/-- Q3 = N8 of `00-REFERENCE-SPEC.md`. Every tabled compiler body is kernel-typeable at a
declared type read out of `lenv` itself — a strengthening of the naive reading (the declaration
must exist in `lenv` and its declared *type* must itself translate), which is exactly what
running lean4lean's checker on the (body, type) pair establishes. `levelParams lenv c` and
`typeOf lenv c` are not existing functions and the second could not type `HasType`'s `VExpr`
argument anyway; `ci` and its own fields replace them. Class **C**, genuinely checkable per
program (measured inhabitable 33/33 on the five programs' closures). There is **no** second
`VEnv`: the `envC = env + addDefEq` device is uninhabitable — a `VEnv.WF` environment grants each
constant at most one defining equation (`WF'.defeqOwn`, `scratchpad/gate/d3_defeq_unique.lean`,
filed upstream §8.3) — and weakening its `wf` to `Ordered` would legalise a per-declaration
fixpoint axiom `c ≡ F c`, false in the intended model for `partial def`. -/
def CompilerBodies (lenv : Lean.Environment) (env : VEnv) (bo : Name → Option Expr) : Prop :=
  ∀ c b, bo c = some b → ∃ ci, lenv.find? c = some ci ∧
    ∃ vb vty, TrExprS env ci.levelParams [] b vb ∧ TrExprS env ci.levelParams [] ci.type vty ∧
              env.HasType ci.levelParams.length [] vb vty
```

`bo` at the capstone is `tbl.body?` — the `decls` column of the reified `SourceTable` (§4.11),
i.e. exactly the `prepare_erasure`d bodies the run reads; `ErasesDecl.defn` (§4.8) reads the same
table, so the specification's δ and the eraser's input are the same object by construction.

### 4.4 `Lower` — the term-level pass relation — `Lower.lean` (landed, U2.7)

`Lower.lean` is landed: fourteen arms, `LowerCorrect.lean` deleted as a file with its simulation
half retired and its `NoBox` family, `BlockBodiesLambda` and the `Lower.source_*`/`target_*`
inversion kit relocated here; `IndBodyOf` relocated in from `ErasesEnv.lean` (§4.8). This section
is transcribed against the landed state; §2.4 records the one clause (`BlockBodiesLambda`, hence
`LowerEnv.specBlocks`, §4.8) landed verbatim but refuted as unsatisfiable.

Sixteen arms: eleven congruence, three redex, two fix. Indexed by `Σ : GlobalDeclarations` and
by nothing else — no source term, no `VEnv`, no run state, no fresh-name *generator*, no
evaluation-shaped or relevance-shaped side condition anywhere. (`LowerBlock`'s `ids : List
FVarId` is λ□'s own fvar type — `LBTerm.fvar` is syntax, `Lower.fvar` is an arm — quantified like
any other metavariable, never read off a run; the anti-epicycle scan therefore bans `Expr`,
`VEnv`, `Erasable`, `ErasureState`, `NameGenerator`, not `FVarId`.) Free on `BinderName`s (`WcbvEval` reads only their
lengths, `Eval.lean:143-153,171`).

```lean
-- There is no `CtorDecl`. Its only consumers were `ctorApp`/`ctorEta`, both deleted, and keeping
-- it inside `RuntimeKey` made `Lower.const` — hence the composite — **uninhabitable at every use
-- site of `Unit.unit`**, a *definition* whose compiler body is a bare constructor (measured
-- 2/11/9/16/20 sites in the five programs; `scratchpad/amend/r1_unit.lean`).
/-- An eliminator declaration **together with its block**: the second conjunct is what puts the
    `.case` node's arity data in scope on the target — `constructorArity` and
    `isPropositionalInductive` read exactly it, through `LowerEnv.inds`. -/
def ElimDecl (Σ) (kn : Kername) (iid : InductiveId) (np dp : Nat) (nfs : List Nat) : Prop :=
  (∃ body, envLookup Σ kn = some (.constantDecl ⟨some body⟩) ∧ ElimBody iid np dp nfs body) ∧
  (∃ mib, envLookup Σ iid.mutualBlockName = some (.inductiveDecl mib) ∧ IndBodyOf iid np nfs mib)
def DefnDecl (Σ) (kn : Kername) (b : LBTerm) : Prop :=
  envLookup Σ kn = some (.constantDecl ⟨some b⟩)
/-- A key the pass consumes rather than emits: an eliminator constant, whose occurrences become
`.case` nodes and whose declaration is pruned. Guards `const` **and** `fixConst`. -/
def RuntimeKey (Σ) (kn : Kername) : Prop :=
  ∃ iid np dp nfs, ElimDecl Σ kn iid np dp nfs

-- There is deliberately no `CtorHeadOf`: a post-δ constructor value
-- `mkApps (.construct iid k []) args` is related by the `app` + `construct` congruence arms
-- alone, so a second disjunct would add zero pairs and one inversion case per consumer.
-- A constructor value's image is that congruence pair and nothing else (Q9).

-- There is no `ElimHeadOf`. Its second disjunct existed only for the δ chain *inside* a
-- simulation run at `Σ⁺`, which Q10 retires; while it stood, `lower_correct` was refutable at
-- every environment (`lower_correct_needs_elimBody_head`, §2.2), because an `ElimBody` shape is
-- an eliminator head at every `Σ`. Both eliminator arms take a `.const kn` head with `ElimDecl`.

inductive Lower (Σ : GlobalDeclarations) : LBTerm → LBTerm → Prop   -- fourteen arms
  -- congruence (11)
  | box                                    : Lower Σ .box .box
  | bvar (i)                               : Lower Σ (.bvar i) (.bvar i)
  | fvar (x)                               : Lower Σ (.fvar x) (.fvar x)
  | prim (p)                               : Lower Σ (.prim p) (.prim p)
  | const {kn} (h : ¬ RuntimeKey Σ kn)     : Lower Σ (.const kn) (.const kn)
      -- deliberately non-deterministic at a block member: `const` relates it to `.const kn`
      -- (what `CloseConstAt` abstracts) and `fixConst` to the block's `.fix` (what a fix
      -- unfolding installs); both are needed, and `Lower.constToFix` is the transport.
      -- ¬RuntimeKey is load-bearing: without it a pruned ctor/elim constant strands the target.
  | lambda {n n' b b'} (h : Lower Σ b b')  : Lower Σ (.lambda n b) (.lambda n' b')
  | letIn  {n n' v v' b b'} (hv : Lower Σ v v') (hb : Lower Σ b b') :
                                             Lower Σ (.letIn n v b) (.letIn n' v' b')
  | app    {f f' a a'} (hf : Lower Σ f f') (ha : Lower Σ a a') :
                                             Lower Σ (.app f a) (.app f' a')
  | proj   {p e e'} (h : Lower Σ e e')     : Lower Σ (.proj p e) (.proj p e')
  | construct {iid k args args'} (hlen : args'.length = args.length)
      (h : ∀ i, i < args.length → Lower Σ args[i]! args'[i]!) :
      Lower Σ (.construct iid k args) (.construct iid k args')
  | «case» {ip d d' alts alts'} (hd : Lower Σ d d')
      (hlen : alts'.length = alts.length)
      (hn : ∀ i, i < alts.length → (alts'[i]!).1.length = (alts[i]!).1.length)
      (hb : ∀ i, i < alts.length → Lower Σ (alts[i]!).2 (alts'[i]!).2) :
      Lower Σ (.case ip d alts) (.case ip d' alts')
  -- redex (1)
  -- There is no `ctorApp`: a constructor spine is `.construct`-headed already, because
  -- `Erases.ctor` (§4.2) is the `tConstruct` congruence and the arguments arrive through
  -- `Erases.app`. `LBWfPeregrine.etaCtors`' saturation invariant is discharged from the eraser's
  -- own dispatch guard (`visitCtorEtaGo`, `Erasure.lean:722-728`, measured 982/982), as before.
  -- There is no `ctorEta` and no `elimEta`. `Lower` is compositional, so an η-expanded head
  -- still composes under `app` into `mkApps (mkLambdas ns body) args'` — a β-redex target with no
  -- bound on nesting, which every spine-inverting arm of T5 would have to collapse. What the two
  -- arms covered is restriction **N19** (no under-applied constructor or eliminator occurrence),
  -- a decidable conjunct of `Supported` (U3.8), and shipping finding **F-ETA2**. For constructors
  -- N19 costs nothing once F-ETA2 is repaired: applied-form λ□ evaluates a partially applied
  -- constructor spine natively (`Value.construct_app_val`). For eliminators it is a real
  -- restriction, with the one-arm contingency in `04-AMENDMENT-W2.md` §12.
  /-- `R_case`: a saturated eliminator application becomes a `.case` node. The `dp` arguments
      before the discriminant (parameters, motive, and for `rec` the minors' prefix) are
      *dropped* — sound for a forward simulation and exactly what MetaRocq's own expansion does.
      Over-application rides outside the node, matching `visitCases`' `args[casesInfo.arity:]`
      loop (`Erasure.lean:832`). -/
  | elimApp {kn iid np dp nfs pre disc disc' minors alts extra extra'}
      (hh    : ElimDecl Σ kn iid np dp nfs)
      (hlen  : pre.length = dp)
      (hmin  : LowerAlts Σ nfs minors alts)
      (hdisc : Lower Σ disc disc')
      (hxlen : extra'.length = extra.length)
      (hx    : ∀ i, i < extra.length → Lower Σ extra[i]! extra'[i]!) :
      Lower Σ (LBTerm.mkApps (.const kn) (pre ++ disc :: minors ++ extra))
              (LBTerm.mkApps (.case (iid, np) disc' alts) extra')
  -- recursion (2) — the repair of §2 F1. Both arms inline the fields of `LowerBlock` below
  -- (the kernel rejects the structure as a nested premise); read them through the wrappers.
  /-- `R_fix` at a *call*: a block member's constant relates to the block's `.fix` node. -/
  | fixConst {kn kns bs bs' ids defs j}
      (hblk… : the `LowerBlock` fields, inlined)
      (hnk   : ¬ RuntimeKey Σ kn)   -- `ElimDecl` implies `DefnDecl`, so nothing else keeps a
                                    -- `.fix` image off an eliminator constant (W2 refuter B-F3)
      (hj    : kns[j]? = some kn) :
      Lower Σ (.const kn) (.fix defs j)
  /-- `R_fix` at a *value*: the member's specification body relates to the same `.fix` node.
      This is the arm the δ step needs, and the one whose absence makes design A's T5 and
      design C's `fixIntro.correct` false. -/
  | fixBody {b kns bs bs' ids defs j}
      (hblk… : the `LowerBlock` fields, inlined)
      (hj : bs[j]? = some b) (hjl : j < defs.length) :
      Lower Σ b (.fix defs j)

/-- Branch peeling: the minor's λ-chain becomes the alternative's binder list. Names are free;
only their *number* — the field arity, which `WcbvEval.iota` reads — is pinned. -/
inductive LowerAlt (Σ) : Nat → LBTerm → (List BinderName × LBTerm) → Prop
  | done {m b}           (h : Lower Σ m b)         : LowerAlt Σ 0 m ([], b)
  | lam  {nf n n' m alt} (h : LowerAlt Σ nf m alt) :
      LowerAlt Σ (nf+1) (.lambda n m) (n' :: alt.1, alt.2)
def LowerAlts (Σ) (nfs : List Nat) (minors : List LBTerm)
    (alts : List (List BinderName × LBTerm)) : Prop :=
  minors.length = nfs.length ∧ alts.length = nfs.length ∧
  ∀ i, i < nfs.length → LowerAlt Σ nfs[i]! minors[i]! alts[i]!
```

**No `fix` congruence arm.** The specification environment declares no `.fix` (block members hold
their plain bodies), and `visitExpr_shape_all` (`ColdStartInduction.lean:1104`) proves `NoFix t`
for the subject term unconditionally, so the source side of `Lower` never contains one. Adding a
congruence arm for it would be dead code (policy 6).

**The block premises are packaged after the fact**, so the arms read as one hypothesis without
creating the kernel-rejected nested-inductive premise. Two fields answer machine-checked
refutations: `hrarg` (without it T5's δ arm is false — probe `gate/rarg_ce.lean` builds the
counterexample at `principalArgIdx = 1`, where the source ⇓ `□` and the target is a stuck spine;
the field is a fact about the emitter: `mkDef` never sets it, `FixDef.principalArgIdx := 0` is
the default, `Basic.lean:67`, whose comment "this doesn't matter computationally" is false under
this `WcbvEval`, and `FixUnfoldChain` already carries exactly this premise, `FixUnfold.lean:803`);
and the **block-shared** `ids` (per-member existential `ids` cannot feed
`closeFix_substList_fixSubst`, whose freshness clause is against *every* `.fix defs j`, and
`ClosedEnv` cannot supply it — `LBClosed (.fvar _) k = True`, `Closed.lean:40`; `visitMutual`
mints one `ids` list for the whole block, `Erasure.lean:905`, so the shared form is what the
emitter does):

```lean
structure LowerBlock (Σ) (kns : List Kername) (bs bs' : List LBTerm) (ids : List FVarId)
    (defs : List (@FixDef LBTerm)) : Prop where
  hb : bs.length = kns.length ; hb' : bs'.length = kns.length
  hd : defs.length = kns.length ; hnd : kns.Nodup
  hids : ids.Nodup ; hilen : ids.length = kns.length
  hfresh : ∀ x ∈ ids, ∀ i, i < kns.length → ¬ hasFVar x bs'[i]!
  hrarg : ∀ d ∈ defs, d.principalArgIdx = 0
  hdecl : ∀ i, i < kns.length → DefnDecl Σ kns[i]! bs[i]!
  hlow  : ∀ i, i < kns.length → Lower Σ bs[i]! bs'[i]!
  hcl   : ∀ i, i < kns.length → CloseConstAt kns ids bs'[i]! (defs[i]!).body
theorem Lower.fixConst' (h : LowerBlock Σ kns bs bs' ids defs) (hnk : ¬ RuntimeKey Σ kn)
    (hj : kns[j]? = some kn) :
    Lower Σ (.const kn) (.fix defs j)
theorem Lower.fixBody'  (h : LowerBlock Σ kns bs bs' ids defs) (hj : bs[j]? = some b)
    (hjl : j < defs.length) : Lower Σ b (.fix defs j)
```

The inductive, both wrappers and the δ-obligation example are probe-checked
(`scratchpad/probe/lowerfix.lean`, `probe/lowerfix2.lean` up to its parse error,
`gate/lowerfix2_fixed.lean` for the repaired final example; axioms `[propext]`).

### 4.5 `LowerFix` — `LowerFix.lean` (`ConstToFVar`/`CloseConstAt` in `Lower.lean`)

`ConstToFVar` and `CloseConstAt` are declared in `Lower.lean`, not here: `LowerBlock.hcl` (§4.4)
needs them, so they sit beside `LowerBlock`; `LowerFix.lean` imports and uses them rather than
redeclaring them (rule N1).

```lean
/-- Replace `.const kns[j]` by `.fvar ids[j]`: the λ□-only residue of today's `Erases.fixvar`,
with the source side removed. Does **not** descend under a `.fix` node (there is none to descend
under: the source side of `Lower` is `NoFix`, §4.4). -/
inductive ConstToFVar (kns : List Kername) (ids : List FVarId) : LBTerm → LBTerm → Prop

/-- The `Kername`-keyed fix closure at a **block-shared** `ids`, phrased through the existing
`closeFix` so that `closeFix_substList_fixSubst` (`FixUnfold.lean:748`) applies verbatim — its
freshness hypothesis is against every `.fix defs j`, which only the shared `ids` (Nodup,
fresh for every member, `LowerBlock`'s fields) can supply — and no const-keyed twin of
`FixUnfold`'s 41 theorems has to be re-proved. -/
def CloseConstAt (kns : List Kername) (ids : List FVarId) (t u : LBTerm) : Prop :=
  ∃ t', ConstToFVar kns ids t t' ∧ u = closeFix ids 0 t'

/-- **The transport that makes the fix arms usable.** A fix unfolding
(`WcbvEval.fix_guarded`'s `substList (fixSubst defs)`) puts `.fix defs i` exactly where the
lowered body has the sibling `.const knᵢ`; this lemma says the result is still `Lower`-related to
the same specification body, by re-deriving each such position with `fixConst`. `ids` is the
block's own list, taken from `hblk`.

The premise is `hfv`, not `hcl : LBClosed t 0`: at `s = t = t' = .fvar ids[0]!` every premise
of the closedness form holds (`LBClosed (.fvar x) 0` is `True`, `Closed.lean:66`) while the
conclusion is underivable (`Lower.target_fix` needs a body in `Γ` equal to a free variable, and
none is), so the closedness form is false — `LowerFixFixture.constToFix_needs_freshness`. `hfv`
is what the intended call site (`t = bs'[i]!`) already has as `LowerBlock.hfresh`; `hΓ` is the
same `ClosedBodies` companion `Lower.closed`/`shift_comm`/`subst_comm` already take, needed here
wherever `substFix` must commute with `shift` (it was the `ctorEta` arm that first forced it; the
arm is gone, the companion stays, since `elimApp`'s alternatives and `fixBody` need it too). -/
theorem Lower.constToFix {Γ kns bs bs' ids defs s t t'} (hΓ : ClosedBodies Γ)
    (hblk : LowerBlock Γ kns bs bs' ids defs) (hfv : ∀ x ∈ ids, ¬ hasFVar x t)
    (h : Lower Γ s t) (hct : ConstToFVar kns ids t t') :
    Lower Γ s (substFix ids defs t')

/-- Declaration-level statement, for `LowerEnv`. Tolerates an unused fix binder: `visitMutual`
decides recursiveness by `name_occurs` on the **source** body (`Erasure.lean:885`), and if
erasure removes the only self-reference the emitted `.fix` binder is unused — which is why no
`name_occurs`-mirroring premise exists anywhere in this design. -/
def LowerFix (Γ : GlobalDeclarations) (kns : List Kername) (bs : List LBTerm)
    (defs : List (@FixDef LBTerm)) : Prop := ∃ bs' ids, LowerBlock Γ kns bs bs' ids defs

/-- **The block-body motive.** Inside `visitMutual`'s block branch the eraser rewrites a source
`.const` to `.fvar id` (`visitConst`, `Erasure.lean:658-664`; the ids come from `mkFreshFVarId`,
so they are in neither `Δ` nor the local context) — a pair no factor of `Erases ⨟ Lower` can
state. The sub-runs under `ctx.fixvars = some …` therefore conclude membership in this
three-factor composite; `mkDef`'s `toBvar` chain then discharges `LowerBlock.hcl` directly from
the `ConstToFVar` witness. This is the λ□-only replacement for today's `Erases.fixvar` and
`BridgeInv.fixvars`, and it is **new work** (motive 6 of W4, gated by U1.7), not a rename. Landed
stateable and inhabited on the two-member fixture (`LowerFixFixture.lowerfix_erasesLBFix`), so
risk R1's motive face does not fire. -/
def ErasesLBFix (env : VEnv) (Us : List Name) (Γ : GlobalDeclarations)
    (kns : List Kername) (ids : List FVarId) (Δ : VLCtx) (e : Expr) (t : LBTerm) : Prop :=
  ∃ t₀ t₁, Erases env Us Δ e t₀ ∧ Lower Γ t₀ t₁ ∧ ConstToFVar kns ids t₁ t
```

`LowerBlock.lambda_of_fixLambda` (used by T5's δ arm at an empty spine, §5) is **unconditional**
again. It needed a third premise `hη : ∀ j, … → ¬ EtaSpine Γ bs[j]!` only because `Lower.ctorEta`
could send a member body `.const lfC` to `λ_. lfC #0`, making `bs'[j]!` λ-headed over a non-λ
`bs[j]!` (finding U1.7-b); with both η arms deleted (A21) that derivation does not exist, so `hη`,
`EtaSpine`, `Lower.source_isLambda`'s second disjunct and `not_etaSpine_lambda_named` are deleted
with it. `LowerBlock.targetLambda_of_fixLambda` (on `bs'`) is unchanged.

### 4.6 `ElimBody`, `IndInfo` — `ElimBody.lean`

The runtime library's bodies are **constructions**, and the file is scoped to their *shapes*:
`Σ⁺` is never evaluated (Q10), so nothing needs its ι-reproduction. `mkElimBody_iota_fwd`,
`mkElimBody_iota_bwd`, `wcbvEval_mkLambdas_fwd` and the `mkElimBodyRec` unfolding are **deleted**
with the simulation that consumed them; `mkElimBody`, `mkCtorBody`, `ElimBody` and the inversion
lemmas stay, because they are what `ElimDecl` declares and what `LowerEnv` transports
(`mkCtorBody` survives only as long as `ErasesDecl.ctor`'s one emitted instance needs it —
`hygiene --dead` decides that at the wave gate). Letouzey's
`(◄₄)` is discharged in the ι arm of §5's T5 instead, from `LowerAlt` and `IotaBridge`
(criterion 7, `[L R4]`).

```lean
def mkCtorBody (iid : InductiveId) (k : Nat) (ns : List BinderName) : LBTerm :=
  mkLambdas ns (LBTerm.mkApps (.construct iid k []) (fieldArgs ns.length))
def mkElimBody (iid : InductiveId) (np dp : Nat) (nfs : List Nat) : LBTerm :=
  mkLambdas (List.replicate (dp + 1 + nfs.length) .anon)
    (.case (iid, np) (.bvar nfs.length) (elimAlts nfs))
/-- The λ□ body of an eliminator constant, as a *syntactic* shape — decidable, one constructor
per shape, no semantic side condition. No `sing` shape: the emitted environment marks every
inductive non-propositional (F-PROP), so a `□`-discriminant `.case` is stuck at every flag point
and N18 keeps such programs out of the fragment (Q2). The second constructor is named `recur`,
not `rec`: `ElimBody.rec` is the name Lean's kernel reserves for the structure's own
auto-generated recursor and refuses to redeclare. -/
inductive ElimBody : InductiveId → Nat → Nat → List Nat → LBTerm → Prop
  | cases {iid np dp nfs} : ElimBody iid np dp nfs (mkElimBody iid np dp nfs)
  | recur {iid np dp nfs} : ElimBody iid np dp nfs (.fix [⟨.anon, mkElimBody iid np dp nfs, dp⟩] 0)

theorem mkCtorBody_beta {Γ fl iid k ns args r} (h : args.length = ns.length) :
    WcbvEval Γ fl (LBTerm.mkApps (mkCtorBody iid k ns) args) r ↔
    WcbvEval Γ fl (LBTerm.mkApps (.construct iid k []) args) r
```

`IndInfo`'s body is stated in full in §4.2, where it is declared (`Erases.lean`, U1.1, since
`Erases.proj` is its first consumer); `ElimBody.lean` imports it.

There is **no** `SubsingletonElim` in the first cut (Q2, N18, F-PROP): the emitted environment
gives the prop-case fragment no subject, and the strengthened criterion the old draft assumed
(`LargeElim` minus `FieldInIndices`) is refutable on `Acc` from `env.WF` alone. Recorded for the
day F-PROP lands on `dev/fix`: the derivable kernel fact is
`largeElim_of_wf (henv : env.WF) (hI : env.constants I = some ic) (hrec : env.constants
(mkRecName I) = some ci) (huv : ci.uvars = ic.uvars + 1) : ∃ decl ℓ envT, …LargeElim…` — with
**both** disjuncts, `declUvars` bound to `I`'s own constant, and `consts_origin` (§8.3) as its
one missing upstream link — plus a decidable no-index-determined-field conjunct in `Supported`,
which is the target's contract (`remove_match_on_box` boxes every branch binder) and must never
be sent upstream.

### 4.7 `ErasesLB` — the composite and the derived introduction lemmas — `ErasesLB.lean`

```lean
def ErasesLB (env : VEnv) (Us : List Name) (Σ : GlobalDeclarations)
    (Δ : VLCtx) (e : Expr) (t : LBTerm) : Prop :=
  ∃ t₀, Erases env Us Δ e t₀ ∧ Lower Σ t₀ t
```

Each deleted `Erases` rule reappears as a **theorem** with the same argument shape, so the 18
motives' proof scripts change by a name (`exact .ctor …` becomes `exact ErasesLB.ctor …`). Two of
them are no longer about the pass layer at all: since `Erases.ctor` is now a rule (§4.2),
`ErasesLB.ctor_head` and `ErasesLB.ctor` are `Erases.ctor` + `Erases.app` + `Lower.construct`, and
`ctor_head`'s W2 arity premise `hnul` disappears with `Lower.ctorApp`
(`ErasesLB.ctor_head_needs_nullary` is deleted with it):

```lean
theorem ErasesLB.box   : TrExprS env Us Δ e ve → Erasable env Us.length Δ.toCtx ve →
                         ErasesLB env Us Σ Δ e .box
theorem ErasesLB.app   : ErasesLB env Us Σ Δ f f' → ErasesLB env Us Σ Δ a a' →
                         ErasesLB env Us Σ Δ (.app f a) (.app f' a')
theorem ErasesLB.ctor_head {cn us I iid k np nfs} (hc : CtorOf env cn I k)
    (hi : IndInfo env I iid np nfs) :
    ErasesLB env Us Σ Δ (.const cn us) (.construct iid k [])
theorem ErasesLB.ctor {cn us I iid k np nfs args args'} (hc : CtorOf env cn I k)
    (hi : IndInfo env I iid np nfs)
    (hlen : args'.length = args.length)
    (ha : ∀ i, i < args.length → ErasesLB env Us Σ Δ args[i]! args'[i]!) :
    ErasesLB env Us Σ Δ (args.foldl Expr.app (.const cn us))
                        (LBTerm.mkApps (.construct iid k []) args')
-- ErasesLB.ctor_eta / .cases_eta — DELETED with the two η arms (A21); see the prose below.
theorem ErasesLB.cases {con : Name} {us : List Level} {ci : VConstant} {iid : InductiveId}
    {np dp : Nat} {nfs : List Nat} {args : List Expr} {disc : LBTerm}
    {alts : List (List BinderName × LBTerm)}
    (hE : ElimDecl Σ (toKername con) iid np dp nfs) (hcst : env.constants con = some ci)
    -- the ι rule's own two new premises (§4.3/§4.8): the head's origin, and the totality
    -- classification `exists_of_trExprS_of_projInfo` needs for `hpre`'s images (§2.4 W2b-F4)
    (hco : ConstOrigin env con)
    (hclass : ∀ c ci, env.constants c = some ci → (∃ I k, CtorOf env c I k) ∨
      (∃ iid np nfs, IndInfo env c iid np nfs) ∨ ConstOrigin env c)
    (henv : env.WF) (hΔ : VLCtx.WF env Us.length Δ)
    (hpre : ∀ a ∈ args.take dp, ∃ ve, TrExprS env Us Δ a ve)
    (hppi : ∀ a ∈ args.take dp, ProjInfo env a)
    (hlen : args.length = dp + 1 + nfs.length)
    (hd : ErasesLB env Us Σ Δ args[dp]! disc)
    (hm : ErasesLBAlts env Us Σ Δ nfs (args.drop (dp+1)) alts) :
    ErasesLB env Us Σ Δ (args.foldl Expr.app (.const con us)) (.case (iid, np) disc alts)
theorem ErasesLB.fix {cn : Name} {us : List Level} {ci : VConstant} {kns : List Kername}
    {bs bs' : List LBTerm} {ids : List FVarId} {defs : List (@FixDef LBTerm)} {j : Nat}
    (hblk : LowerBlock Σ kns bs bs' ids defs)
    -- fixConst's guard and const's positive premise (§4.4/§4.2), gained with the amendment
    (hnk : ¬ RuntimeKey Σ (toKername cn)) (hj : kns[j]? = some (toKername cn))
    (h : env.constants cn = some ci) (ho : ConstOrigin env cn) :
    ErasesLB env Us Σ Δ (.const cn us) (.fix defs j)
```

`ErasesLB.cases`'s `hpre`/`hppi` are discharged by `Erases.exists_of_trExprS_of_projInfo` (which
itself now takes `hclass`, §2.4 finding W2b-F4 — hence `.cases` takes it too) from the `TrExprS`
every motive already carries: the arguments a `.case` node drops still need an erasure image in
`t₀`, because `Erases` is a congruence over the whole spine. `hco` is the ι rule's own
`ConstOrigin` reading of the head (§4.3, §4.8). The `ErasesLB.ctor_eta`/`cases_eta` twins are
**deleted** with the two η arms (A21), which is also how U2.2's obstruction O5 — the middle term
not being determined by `(args, ns)` — disappears: the shapes it was about are absent from the
relation, and the occurrences they covered are restriction N19 (Q12).

The introduction lemmas above serve the `ctx.fixvars = none` runs. The block-branch sub-runs
conclude `ErasesLBFix` (§4.5) instead, and each lemma has an `ErasesLBFix.*` twin obtained by
post-composing with `ConstToFVar`'s congruence — mechanical, since `ConstToFVar` is itself a
congruence everywhere except at the `kns` constants.

### 4.8 `ErasesDecl`, `ErasesEnv`, `LowerEnv`, `SpecEnv` — T3 — `ErasesEnv.lean`, `SpecEnv.lean`

Four helper predicates read the environment in λ□ coordinates, against lean4lean's actual API
rather than against functions the design's first draft named but that do not exist (§2.2, finding
U1.9-b/c): `CtorOf env c I k` (the block/constructor existential `IndInfo` itself uses, keyed on
the constructor's own name); `CasesOnOf env I kn` (`kn` is a `casesOn`-like constant of `I`,
`Lean/Meta/CasesInfo.lean:56`'s `isCasesOnLike`); `IndBodyOf iid np nfs mib` (a λ□ inductive body
`mib` *agrees with the block on what the target semantics reads* — parameter count, constructor
field counts, non-propositionality — since no function computes `mib`'s `Ident` strings, `kelim`
or `propositional` flag from a `VInductiveType`, and none of those needs to be pinned tighter than
the semantics can observe); `patHead`/`PatOf` (below), replacing a `patsOf : VEnv → List Pattern`
that does not exist — `VEnv.pats` is a relation, and `Pattern` has no `head` field. **`IotaInert`
is deleted** (U2.5): once `SEval`'s value arms are keyed on `CtorOf`/`IndInfo`/`ConstOrigin`
rather than on a name test, a tabled recursor's own dispatch is excluded by `hnd`/`hsh` and the
`ax` arm needs no ι-freedom conjunct — restriction N21 (§4.3) and U3.8's `supportedB` rejection
of a recursor head do that work instead. `patHead`/`PatOf` are consumer-free once `IotaInert` is
gone (§2.4 finding W2b-F5) and are left for **U3.6** to delete, which owns `ErasesEnv.lean` in W3:

```lean
def patHead : Pattern → Name
  | .const c => c | .app f _ => patHead f | .var f => patHead f
def PatOf (env : VEnv) (p : Pattern) : Prop := ∃ r, env.pats p r

inductive ErasesDecl (env : VEnv) (bo : Name → Option Expr) : Kername → GlobalDecl → Prop
  /-- The defining body is the **compiler's** (N8, §4.3) — the same table `SEval.deltaC` reads,
      so the specification's δ and the environment's entries agree by construction. `Us` is
      existentially bound at the declared width: `VConstant` records only `uvars : Nat`, a count,
      never level-parameter names, so no `levelParamsOf env c` function exists to supply the
      canonical scope `Erases`'s second index wants. A `defn` entry gives *some* level scope of
      the right width, which is all the level-scope-parametric transport lemmas (U1.2) need. -/
  | defn {c body b₀ Us ci} (hc : env.constants c = some ci) (huv : Us.length = ci.uvars)
         (hd : bo c = some body) (hb : Erases env Us [] body b₀) :
         ErasesDecl env bo (toKername c) (.constantDecl ⟨some b₀⟩)
  /-- Inert constants only: no compiler body. `IotaInert`'s ι-freedom conjunct is deleted (U2.5):
      restriction N21 already keeps a tabled recursor out of the fragment (`supportedB` rejects a
      recursor head, U3.8), so an `Eq.rec` in `Fannkuch.ast` is excluded there, not here. A program
      reaching a body-less constant `SEval` can still step at has no `ErasesEnv` witness; that is
      its coverage row (F-EQREC), not a hidden premise. -/
  | ax   {c ci} (h : env.constants c = some ci) (hno : bo c = none) :
         ErasesDecl env bo (toKername c) (.constantDecl ⟨none⟩)
  | ind  {I iid np nfs mib} (h : IndInfo env I iid np nfs) (hm : IndBodyOf iid np nfs mib) :
         ErasesDecl env bo iid.mutualBlockName (.inductiveDecl mib)
  -- There is no `ctor` arm: it demands `CtorOf`, and no `.ast` in the fragment declares a
  -- genuine constructor constant. The one constructor-bodied entry — `Unit.unit ↦ tConstruct
  -- PUnit 0`, 1 per file in all five — is a *definition* whose compiler body is `PUnit.unit`,
  -- justified by `defn` through `Erases.ctor` (A22, W2 refuter A-F1).
  /-- `casesOn`-like constants only; never `X.rec`, and matchers are gone by `prepare_erasure`'s
      `inlineMatchers`. `hinf` is N18's environment half: an eliminator of a non-informative
      inductive has no entry, because its emitted `.case` is stuck on every `Σ⁺` a run produces
      (F-PROP) — a fact about the target, not a proof convenience. `InformativeInd` is
      `Supported.lean`'s name (U1.8); `iid.mutualBlockName` (not `.blockName`) is `Basic.lean:50`. -/
  | elim {I c kn iid np dp nfs body} (hi : IndInfo env I iid np nfs)
         (he : CasesOnOf' env I c kn) (hinf : InformativeInd env I)
         -- the emitted `.case` node's segmentation **is** the source eliminator's: without this
         -- clause nothing relates `SEval.iota`'s spine split to `dp`/`nfs` (W2 refuter B-F3)
         (hsh : CasesOnShape env c I dp nfs.length)
         -- the eliminator constant's own reading, the same positive fact `Erases.const` takes.
         -- T5's β arm reaches it through `hspec` to discharge `SEval.no_elimSpine_value` at a
         -- saturated eliminator spine, where `Lower.elimApp` is the second reading of an `.app`
         -- node (`04-AMENDMENT-W2.md` §6; second-round fidelity F6)
         (hco : ConstOrigin env c)
         (hb : ElimBody iid np dp nfs body) :
         ErasesDecl env bo kn (.constantDecl ⟨some body⟩)
```

`ErasesDecl.quot` is deleted (Q7). `ErasesEnv` is `[S §7.4]`'s `erases_deps` — bottom-up,
dependency-selective, the **only** relation between a `VEnv` and λ□. Its body is written out
(the elided form left the no-slack story unstated): lookups go through `envLookup` (first match),
keys are `Nodup` — so a junk shadowing entry cannot retarget `Lower` — and every kername
reachable from `t` in `Σ⁺` has an `ErasesDecl` image:

```lean
inductive ErasesEnv (env : VEnv) (bo : Name → Option Expr) : GlobalDeclarations → LBTerm → Prop
  | mk {Σ⁺ t} (keys : (Σ⁺.map Prod.fst).Nodup)
       (decls : ∀ kn d, envLookup Σ⁺ kn = some d → ErasesDecl env bo kn d)
       (deps : ∀ kn, ReachableFrom Σ⁺ t kn → (envLookup Σ⁺ kn).isSome)
       /-- The δ arm's own premise, in the δ arm's own direction — `erases_deps`' constant clause.
           `decls` runs the other way (entry ⇒ justified) and cannot supply it: at a tabled
           constant it does not even say which arm justifies the entry
           (`erasesEnv_not_deltaAgrees`, §2.2). -/
       (defns : ∀ c b, bo c = some b → ReachableFrom Σ⁺ t (toKername c) →
          ∃ b₀, envLookup Σ⁺ (toKername c) = some (.constantDecl ⟨some b₀⟩) ∧
                ∀ Us' ups us, Erases env Us' [] (b.instantiateLevelParams ups us) b₀) :
       ErasesEnv env bo Σ⁺ t
```

`ErasesDecl.ctor` is **deleted** (A22). The one constructor-bodied declaration in the five
programs is `Unit.unit ↦ tConstruct PUnit 0` (1 per file), and `Unit.unit` is a Lean *definition*:
`CtorOf env ``Unit.unit I k` is false, so the `ctor` arm could never have justified that entry,
while `defn` justifies it through the new `Erases.ctor` rule. The only path that would emit a
genuine constructor declaration is `visitConstructor`'s `isExtern ∧ extern == .preferAxiom` branch
(`Erasure.lean:739`), which is out of fragment and named in `doc/coverage.md`.

The emitted environment is the lowered, pruned image — class **A**. `EnvAgree` and its five
lemmas, the planned `WcbvEval.congr_env`/`LowerEnv.congr_env`, and `PrunedFor` are **deleted**: no
statement in the tree or in this design consumes any of them, `PrunedFor`'s only occurrence is its
own definition (`ErasesEnv.lean:329`), and `congr_env`'s acceptance was that it elaborates. The
conclusion is stated at the emitted `Σ` itself.

```lean
/-- `closed` reads `ClosedBodies` (`Lower.lean`, U1.5) rather than a new `ClosedEnv`: the two
predicates coincide, and minting a second name would split every downstream rewrite (N1). `sub`
replaces the design's `prune : ∀ kn, envLookup Σ kn ≠ none → Reachable Σ kn`, which does not
typecheck as written — `Reachable` has no root — and could only be *the* rootless reading (every
key reaches itself), which is vacuous. `sub` is the binary half a `const`-arm argument can
actually use ("pruning only removes"). The term-rooted size claim was carried as a standalone
`PrunedFor`; it is deleted, having acquired no consumer. -/
structure LowerEnv (Σ⁺ Σ : GlobalDeclarations) : Prop where
  keys   : (Σ.map Prod.fst).Nodup
  defs   : ∀ kn b₀ b, DefnDecl Σ⁺ kn b₀ → DefnDecl Σ kn b →
             Lower Σ⁺ b₀ b ∨ ∃ kns bs defs j, LowerFix Σ⁺ kns bs defs ∧
                                              kns[j]? = some kn ∧ b = .fix defs j
  /-- Totality of `defs` — without it a plain definition present in `Σ⁺` but pruned out of `Σ`
      satisfies everything vacuously while the target is stuck at its `.const` (no δ rule, and
      `atomValue` excludes `.const`). The `fix` disjunct is gone: the eraser declares **every**
      definition, recursive ones with a `.fix` body (measured: `Arith.ast` has 4 `tFix` and 27
      `ConstantDecl`, every `tFix` inside one), and `Lower.const` relates a block member to its own
      `.const`, so without the stronger clause that image is stranded. -/
  defsTotal : ∀ kn b₀, DefnDecl Σ⁺ kn b₀ → ¬ RuntimeKey Σ⁺ kn → ∃ b, DefnDecl Σ kn b
  axioms : ∀ kn, envLookup Σ⁺ kn = some (.constantDecl ⟨none⟩) →
             envLookup Σ kn = some (.constantDecl ⟨none⟩) ∨ envLookup Σ kn = none
  inds   : ∀ kn d, envLookup Σ⁺ kn = some (.inductiveDecl d) → envLookup Σ kn = some (.inductiveDecl d)
  sub    : ∀ kn, envLookup Σ kn ≠ none → envLookup Σ⁺ kn ≠ none
  closed : ClosedBodies Σ
  /-- The pass layer's own environment well-formedness, on `Σ⁺`, where the `Lower` metatheory
      T5's arms consume actually needs it: `specClosed` is `Lower.subst_comm`'s hypothesis (every
      β/ζ/ι step) and `specBlocks` is the whole `Lower.source_*` inversion kit's — it is what
      excludes a `.fix` image of a constructor value at the ι arm's discriminant step. Clauses,
      not extra binders of T5 (A18, W2 refuter B-F2); U3.6 derives them with the rest. -/
  specClosed : ClosedBodies Σ⁺
  -- REFUTED as printed (§2.4 finding W2b-F1): `BlockBodiesLambda Σ⁺` quantifies over EVERY
  -- `LowerBlock` over `Σ⁺`, and a single declared non-λ body (`Unit.unit`'s shape, present in
  -- every one of the five programs' Σ⁺, G1's included) is a one-member block that refutes it.
  -- `LowerEnv Σ⁺ Σ` is landed and inhabited only on fixtures whose blocks are all λ-bodied
  -- (`lowerEnv_idEnv`); it is UNINHABITED on every real specification environment. No repair is
  -- landed; the obligation is the owning W3 unit's: restrict the clause to the blocks the pass
  -- actually builds (key it on `LowerFix`/`visitMutual` groups — the emitted `.fix` declarations
  -- — not on every `LowerBlock`), or restate it as "every body that is a member of an emitted
  -- `.fix` block is a λ".
  specBlocks : BlockBodiesLambda Σ⁺
```

**Environment threading.** The bridge's motives quantify `Σ⁺` *universally* under an antitone
premise, so sibling sub-runs never merge environments. `SpecEnv`'s three state-facing fields
quantify the registry entry's witness *existentially*: `StateLe` gives only domain growth
(`(s.constants.get? n).isSome → (s'.constants.get? n).isSome`), never equality of a stored value,
so a field phrased on the stored value would make `.mono` false as stated.

```lean
/-- `Σ⁺` is a specification environment for the run state `s`: every constant `s` registered has
its `ErasesDecl` image in `Σ⁺`, and every inductive `s` registered contributes its `ind`, `ctor`
and `elim` declarations, existentially over the witness `IndInfo`/`CtorOf`/`CasesOnOf` supply.
Antitone in the state (`.mono`), which is what makes it compose. -/
structure SpecEnv (env : VEnv) (bo : Name → Option Expr) (s : ErasureState)
    (Σ⁺ : GlobalDeclarations) : Prop where
  keys  : (Σ⁺.map Prod.fst).Nodup
  decls : ∀ kn d, envLookup Σ⁺ kn = some d → ErasesDecl env bo kn d
  consts : ∀ n : Name, (s.constants.get? n).isSome → (envLookup Σ⁺ (toKername n)).isSome
  inds  : ∀ n : Name, (s.inductives.get? n).isSome →
            ∃ iid np nfs, IndInfo env n iid np nfs ∧ (envLookup Σ⁺ iid.mutualBlockName).isSome
  ctors : ∀ n : Name, (s.inductives.get? n).isSome →
            ∀ c k, CtorOf env c n k → (envLookup Σ⁺ (toKername c)).isSome
  elims : ∀ n : Name, (s.inductives.get? n).isSome →
            ∀ kn, CasesOnOf env n kn → InformativeInd env n → (envLookup Σ⁺ kn).isSome

theorem SpecEnv.mono (h : StateLe s₁ s) (H : SpecEnv env bo s Σ⁺) : SpecEnv env bo s₁ Σ⁺
/-- The only `ErasesEnv` clause mentioning a program is `deps`; the other two come straight from
`SpecEnv`. -/
-- WEAKENED (§2.4 finding W2b-F3): `SpecEnv`'s six fields never mention `bo`, so no proof of
-- `ErasesEnv`'s `defns` clause can come out of `H` alone. Gains `hdefns`, exactly `defns`'s
-- shape, as a second explicit premise. U3.6's `SpecEnv.exists` discharges it from the run's
-- registry; no consumer exists yet.
theorem SpecEnv.erasesEnv (H : SpecEnv env bo s Σ⁺) {t : LBTerm}
    (hdeps : ∀ kn, ReachableFrom Σ⁺ t kn → (envLookup Σ⁺ kn).isSome)
    (hdefns : ∀ c b, bo c = some b → ReachableFrom Σ⁺ t (toKername c) →
      ∃ b₀, envLookup Σ⁺ (toKername c) = some (.constantDecl ⟨some b₀⟩) ∧
            ∀ Us' ups us, Erases env Us' [] (b.instantiateLevelParams ups us) b₀) :
    ErasesEnv env bo Σ⁺ t
```

`ErasesEnv` is not (yet) known to transport along `≐`, unlike `LowerEnv`: `ReachableFrom` is
computed by a fuel-bounded fold whose accumulator order depends on the list, and relating two
agreeing environments' closures needs a permutation-invariance argument not yet made. Not needed
by the design — the conclusion is stated at the emitted `Σ` itself and `ErasesEnv` constrains `Σ⁺`,
which is why `EnvAgree` is deleted rather than carried — but a unit that re-keys `Σ⁺` must prove it
first.

`StateLe` (`ErasureRun.lean:1585`) and `RunConcl` (`:1609`) already exist and carry unchanged.
`SpecEnv.mono` and `SpecEnv.erasesEnv` are landed (above); `SpecEnv.exists`, which builds `Σ⁺`
from `RegInvShape` (`ColdStartShape.lean:314`) plus `ErasureSpec.lookup_adequate`, is U3.6's (W3)
— keeping the tree's genuine advantage over the papers' presentation: the environment relation is
*derived from what the run registered and consulted*.

### 4.9 Output boundary — `Output.lean` (landed, U2.8)

`Output.lean` is landed, `NoBodylessRefs` included, with reachability tracking inductive blocks
(the `.construct`/`.case`/`.proj` cases added to `constRefs`) — this section is transcribed
against the landed state. `Supported.lean` and `ErasureSpec.lean` remain U1.8's/W3's (§4.10,
§4.11); the schedule consequence of `ErasureSpec.lean` importing `CheckerAdequacy.lean` is
`02-PLAN.md` §2's.

```lean
/-- One constructor spine of `t` or of a constant body of `Σ`, with its argument count — the
subject of the saturation invariant. -/
inductive ConstructSpine (Σ : GlobalDeclarations) : LBTerm → InductiveId → Nat → Nat → Prop

/-- What `untyped_transform_pipeline` needs from us, on the emitted program alone. `fresh`…
`projDecl` are `EWellformed all_env_flags` (what `peregrine validate` checks); `etaCtors` is the
constructor-saturation invariant `validate` omits and `remove_params_optimization` consumes —
env **and** term, mirroring `EEtaExpanded.expanded_eprogram_cstrs = isEtaExp_env p.1 && isEtaExp
p.1 p.2`; the term half is vacuous on every `#erase` of a constant (the emitted `t` is a bare
`.const`), so the env half carries the measured 982/982. It is discharged from `Supported`'s N19
conjunct through the bridge (`visitExpr_ctorSat`), not assumed — `Lower.ctorApp` is gone with Q9. The same env+term split applies to `ctorApplied`,
`closed`, `fixLambda`, `casesExh`, `projDecl`, `constsOk`, `ctorDecl`. Fixpoint η is **not**
claimed: it is false on all five programs — F-ETA. -/
structure LBWfPeregrine (Σ : GlobalDeclarations) (t : LBTerm) : Prop where
  keys, declsWf, closed, constsOk, ctorApplied, ctorDecl, casesExh, fixLambda, projDecl : …
  etaCtorsEnv : ∀ kn b iid k n, envLookup Σ kn = some (.constantDecl ⟨some b⟩) →
                  ConstructSpine Σ b iid k n → n ≥ cstrArity Σ iid k
  etaCtorsTm  : ∀ iid k n, ConstructSpine Σ t iid k n → n ≥ cstrArity Σ iid k
  asciiNames  : ∀ nm ∈ binderNames Σ t, nm.isAsciiGraphic          -- the λ□ parser's constraint

/-- The fix-clause half of `EEtaExpandedFix.expanded`, over env and term: every `tFix` occurs
applied, `args ≠ []` and `#args > principalArgIdx` (`EEtaExpandedFix.v:47-53`). -/
def LBExpandedFix (Σ : GlobalDeclarations) (t : LBTerm) : Prop

/-- What peregrine's first pass actually requires. `LBWfPeregrine` is strictly weaker; the
difference is exactly `LBExpandedFix`. This is not paperwork: `guarded_to_unguarded_fix`
(`ETransform.v:666-682`) is the identity on terms and its **entire evaluation-preservation
obligation** is discharged from `EEtaExpandedFix.expanded_eprogram` via `eval_opt_to_target`, so
with F-ETA no verified semantics-preservation argument covers the frontend's output past T9's
`WcbvEval` — T9's docstring says so and names F-ETA. peregrine's own discharge is `Admitted`
(`Transforms.v:375`) and `validate` checks no η, so nothing downstream detects it.
**Not concluded by T9.** -/
def PeregrinePre (Σ) (t) : Prop := LBWfPeregrine Σ t ∧ LBExpandedFix Σ t

-- `ErasableAxioms` and `AxiomRealizer` are **deleted**, and the `AxiomFree` the first cut of the
-- W2 amendment proposed is not landed (A18, A-F2/B-F8). `ErasableAxioms`' realizer whitelist
-- *permitted* `Eq.rec` and `False.rec` while nothing realizes them, so it was not `axiom_free`'s
-- analogue; and `AxiomFree` as printed was *false* on the green rung G1 the moment reachability
-- tracks inductive blocks, since a block kername is answered by an `.inductiveDecl` and never by a
-- bodied `.constantDecl` (`scratchpad/amend2/r1_axiomfree.lean`). What survives is the honest
-- analogue, and it sits where MetaRocq puts it: on T9, not on T5.
--
-- T5 needs none: with `SEval`'s value arms keyed on `CtorOf`/`IndInfo` (§4.3), a run that forces a
-- body-less plain constant has no `SEval` derivation at all — PCUIC's own treatment of an axiom,
-- where `value_head` admits no body-less `tConst` and `erases_correct` carries no `axiom_free`
-- hypothesis (`refs/metacoq-erasure.md:552`). But `erase_correct_firstorder` *does* take one
-- (`:600`), and for a reason this design cannot do without: measured, `Fannkuch.ast` emits `Eq.rec`
-- as `(ConstantDecl (constant_body None))`, so a Fannkuch rung's `hev` is uninhabitable and the
-- rung would be **vacuously** green with nothing flagging it (A24).

/-- `[S §7.3]`'s `axiom_free Σ` at the emitted environment, with no realizer whitelist: no constant
reachable from `t` is declared without a body. Decidable, hence `by decide +kernel` per rung; false
exactly where the target is stuck at a `delta` step. T9's premise, and nothing else's. -/
def NoBodylessRefs (Σ : GlobalDeclarations) (t : LBTerm) : Prop :=
  ∀ kn, ReachableFrom Σ t kn → isBodylessConst (envLookup Σ kn) = false
```

The `Eq.rec`/`False.rec` realizer rows survive as `doc/coverage.md`'s F-EQREC row, which is what
they always were: a claim about the consumer's runtime, not a premise of any theorem here. The
coverage table records that **Fannkuch** fails `NoBodylessRefs` and is therefore outside T9's
domain.

**Reachability tracks inductive blocks.** `constRefs` collects `.const` kernames only
(`Output.lean:225`), so nothing forces the emitted `Σ` to declare the block a `.construct`,
`.case` or `.proj` node reads — and `constructorArity`/`isPropositionalInductive`, which the ι,
proj and constructor arms of T5 all consult, read exactly those declarations. The three cases are
added; `ReachableFrom` stays decidable and the rungs' `rfl`-computed closures are re-measured at
the gate.

`ctorApplied` (`NoBlock t`) and `closed` are supplied **unconditionally and panic-tolerantly** by
`visitExpr_shape_all` — two conjuncts for free. `etaCtorsEnv` is supplied by U4.5's
`visitExpr_ctorSat` (the run-side saturation lemma, lifted through `RegInvShape'`), and
`fixLambda` by the shape of `visitMutual`'s output under `Supported` — the eraser itself checks
neither (raised inside **F-ETA**, §8.2).

### 4.10 `ErasureSpec` — the one bundle — `ErasureSpec.lean` (U1.8, being completed)

What follows is what the design requires of `ErasureSpec.lean`; the file is being landed by
U1.8 and this section is not transcribed against its current partial state. `Capstone.lean`
already names the bundle (`ErasureSpec lenv env [] gw`, §5 T9) as a binder, ahead of U1.8's own
field-by-field delivery.

Renamed from the draft's `PrimSpec` — `Lean4Lean.PrimSpec` exists upstream
(`Verify/Typing/Expr.lean:315`) and this tree opens `Lean4Lean` pervasively. Built from
`OracleDischarge.ResidualHyps` (`OracleDischarge.lean:65`): three fields carried (`orc_refl` split
in two below; `fresh_run`; `cases_run`+`ctor_run` merged into `lookup_adequate`) and three new.
Table adequacy is **not** a field: a `Prop`-valued structure cannot hold `tbl` as data, and an
unbound `tbl` in a field auto-binds to `∀ tbl, …` — false, hence the bundle uninhabitable. It is
the named binder `htbl` beside `hrun` (§5).

```lean
structure ErasureSpec (lenv : Lean.Environment) (env : VEnv) (Us : List Name)
    (gw : Void IO.RealWorld → NameGenerator) : Prop where
  /-- `VEnvs.WF : Lean.Kernel.Environment → VEnvs → Prop`, so the bridge object is named:
      `lenv.toKernelEnv = lenv.checked.get` is where the elaboration environment and the modelled
      one are joined — the same conversion the shipping call site makes (`Erasure.lean:178`). -/
  env_connect     : ∃ ves : VEnvs, ves.WF lenv.toKernelEnv ∧ env = ves.venv .safe
  lookup_adequate : …    -- getConstInfo / getCasesInfo? / getCtorArity? / getDeclInfo?
  fresh_names     : …    -- `mkFreshFVarId` returns identifiers absent from the ambient context
  /-- Class **D** with a proved kernel branch: an `Erasure.isErasable` run at `lps` returning
      `true` either reflects `M.run env₀ .safe ctx.lctx lps (isErasable e) = .ok true` with
      `lps = Us` (the arm `Oracle.kernel_isErasable_sound` discharges — class **B**), or the
      `.error` arm fired and `isErasableMeta` answered. The disjunctive shape is
      `OracleDischarge.lean:69-88` verbatim; a structure field cannot be "discharged", only its
      kernel arm can. -/
  oracle_refl     : …
  /-- Class **D**: soundness of the `isErasableMeta` fallback, and of any run at
      `ctx.lparams ≠ Us` (`BridgeInv.lparams` is a strict-prefix guard, so at the capstone's
      `Us = []` the kernel arm covers only monomorphic declarations' runs — a real scope limit,
      stated). Measured empirically dead on the error route: 0 kernel-run errors over 139,196
      non-internal constants, 1 divergence and that one planted (`gate/d5_census.lean`). -/
  oracle_meta     : …
  /-- `InductiveVal` ↔ `VInductDecl` in `env`'s declaration list. U1.8 first *attempts the
      derivation* from `env_connect` by `TrEnv'` inversion on the `induct`/`AddInduct` clause —
      upstream ships the shape twice (`TrEnv'.structure_rec`, `TrEnv'.pats_iota'`) — and keeps
      the field only if that fails, with the obstruction named. -/
  decl_adequate   : …

theorem ErasureSpec.envWF (P : ErasureSpec lenv env Us gw) : env.WF     -- via `TrEnv'.wf`;
    -- measured sorryAx-free: [propext, Classical.choice, Quot.sound] (gate/d5_envwf.lean)
theorem ErasureSpec.oracle_sound_of_run (P : ErasureSpec …) … :
    Erasure.isErasable lps e = .ok true → ctx.lparams = Us → TrExprS env lps Δ e ve →
    Erasable env lps.length Δ.toCtx ve
    -- kernel branch via `Oracle.kernel_isErasable_sound`; fallback branch by `P.oracle_meta`
```

Fields 1, 2, 3, 6 are class **D** (field 6 pending its derivation attempt); `oracle_refl` +
`oracle_meta` are class **D** with the kernel arm class **B**, discharged through
`Relevance` → `RelevanceCheck.isArityCheck.WF` → `Oracle.kernel_isErasable_sound`. That chain is
the development's only trust *reduction* — real but **partial** (A16): what remains assumed is
the impure→pure reflection, the `Meta` fallback, and the polymorphic-scope arm, each with its
ledger row. It costs 33 axioms (measured: 29 non-standard names, exactly two `_native.bv_decide`
from Lean core — `gate/d5_axioms.lean`), and it is why shipping edit **B1** (the `isErasable`
kernel reroute) is kept — conditional on **F-FUEL** landing in W0 (§8.1): with the fuel defect
fixed, the residual kernel-arm assumption is near-definitional (`Erasure.isErasable` literally
calls `M.run … (RecM.run (isErasable e))`), a genuinely weaker trust obligation than
"`Meta.isProp ∨ Meta.isTypeFormerType` is sound". `ErasureSpec.envWF` is a genuine trust
reduction over the current tree, which assumes `env.WF` outright.

The relational pass interface, with explicit binders (§2 F11). `LBWfSpec Σ⁺` is the
specification environment's own well-formedness — `(Σ⁺.map Prod.fst).Nodup ∧ ClosedEnv Σ⁺` —
defined in `ErasesEnv.lean` and derived from `ErasesEnv` (there is no other `LBWf`):

```lean
structure LBPassR where
  rel        : GlobalDeclarations → LBTerm → LBTerm → Prop
  flIn flOut : WcbvFlags
  correct    : ∀ {Σ⁺ Σ t t' v}, LBWfSpec Σ⁺ → LBClosed t 0 → LowerEnv Σ⁺ Σ → rel Σ⁺ t t' →
               WcbvEval Σ⁺ flIn t v → ∃ v', rel Σ⁺ v v' ∧ WcbvEval Σ flOut t' v'
```

### 4.11 `Supported`, `supportedB`, `SourceTable` — `Supported.lean`, `Witness/SourceTable.lean`

`Witness/SourceTable.lean` (`SourceTable`, `SourceTableAdequate`, the `reify%` elaborator) is
landed (U0.3, W0) and is what follows. `Supported.lean` (`SupportError`, `supportedB`, `Supported`,
`supportedB_sound`) is being landed by U1.8; what follows for it is what the design requires, not
a transcription of its current partial state — at this wave `supportedB` and `SupportError` exist
but the Prop `Supported` and `supportedB_sound` do not yet, so T9 currently takes `hsup` as the
`supportedB` verdict directly rather than as `Supported env e` (§2.2, finding G1-O1).

```lean
inductive SupportError where
  | sparseCasesOn (c : Name)       -- the measured Quicksort miscompile
  | sideConditionElim (c : Name) | etaContractedMinor (c : Name)
  | strLit | machineNat | quotPrim (c : Name) | ioLike (c : Name) | implementedBy (c : Name)
  | mvar | propElimIntoData (I : Name)      -- N18, *shape*-keyed: `Acc.casesOn` compiles in Lean,
                                            -- so a name-keyed `accRec` would not close the hole
  | unknownConst (c : Name)
  | outOfFuel                               -- exhaustion never certifies an untraversed closure
  deriving Repr, DecidableEq

/-- Total and fuel-indexed — the dependency closure is cyclic through mutual blocks, so this is
not structural on `e`, and a `partial def` would be kernel-opaque (`by rfl` fails on one).
Decidable over `e` **and its dependency closure**, on the reified table, and it *names the
hole* — which is what generates the coverage table; `Bool` would lose the name. -/
def supportedB (tbl : SourceTable) (fuel : Nat) (e : Expr) : Except SupportError Unit
def Supported (env : VEnv) (e : Expr) : Prop                    -- one named conjunct per SupportError
theorem supportedB_sound (P : ErasureSpec lenv env Us gw) (ht : SourceTableAdequate lenv tbl) :
    supportedB tbl fuel e = .ok () → Supported env e
```

`Supported.casesApp` requires the head to be `I.casesOn` for an inductive in the fragment —
**informative** (N18) — with a **plain** `CasesInfo` (no `CasesAltInfo.default`, no
`hasSideCondition`) and every minor a syntactic λ-chain of its alt's field arity
(`IsLamTelescope`, `Bridge.lean:60`, already assumed by motive 18 — zero churn). The first
exclusion is the shipping bug of `VerifyBench/Quicksort`; the second is what makes the
composite's branch rule exact; the informativity conjunct is F-PROP's fragment boundary (Q2). A
*reporting* predicate `HasCompilerBody` excludes nothing and feeds the coverage table.

```lean
/-- A reified slice of the `Lean.Environment`: the `prepare_erasure`d bodies of the dependency
closure and the inductive metadata with constructor arities — nothing else (an `oracle` column
would re-enter as assumed data the one fact the development discharges, and a `cfg` column
duplicates `hcfg`). Spliced by the `reify%` term elaborator, which reads `getEnv` **in the same
elaboration as the rung** — so there is no committed-artifact ingestion step, no JSON parser in
the trust base, and no regenerate-and-diff circularity; the assumption shrinks to "a ten-line
elaborator copies `find?`'s result". `lake exe green-check` still re-runs `#erase` and byte-diffs
the emitted `.ast`, the output half of `hrun`. This is the only way a `by rfl`/`by decide`
discharge can exist: no term denotes the ambient environment (the private constructor and opaque
`EnvExtensionState` hold of `Lean.Kernel.Environment` too), and `native_decide` is banned. -/
structure SourceTable where
  decls  : List (Name × ReifiedDecl)      -- levelParams, type, prepared body?
  inds   : List (Name × ReifiedInduct)
def SourceTable.body? (tbl : SourceTable) : Name → Option Expr   -- `SEval`/`ErasesDecl`'s table

/-- Two clauses: (a) a per-declaration pin — `∀ d ∈ tbl.decls, lenv.find? d.name` matches
`d`'s type and levels; (b) the run clause for the one column that is not a `find?` output —
`prepare_erasure` on `d.name`'s value returns `d.body?` (`prepare_erasure : Expr → EraseM Expr`
is monadic, so this clause is run-indexed like `lookup_adequate`, not a pure equation). Carried
as the named class-**D** binder `htbl` in every rung and in T9. -/
def SourceTableAdequate (lenv : Lean.Environment) (tbl : SourceTable) : Prop
```

The reflection posture is the ecosystem's own: MetaRocq reifies the Rocq environment through an
unverified OCaml quoter (`quoter.ml`/`ast_quoter.ml` in rocq-metarocq-template, vendored by
`peregrine-tool/plugin`), so a reification TCB already sits under `Peregrine Extract`, unnamed.
Here it is one named binder. Because `lenv` is universally quantified in every rung, the ladder
delivers **conditional** non-vacuity — no computation can make it unconditional, and saying so
costs this sentence (§6).

### 4.12 `FirstOrderInd` — T7 — `FirstOrderInd.lean`

```lean
def HasInduct (env : VEnv) (decl : VInductDecl) : Prop :=       -- LeanToLambdaBox namespace, no
  ∃ ds, VEnv.WF' ds env ∧ VDecl.induct decl ∈ ds                --   dot notation (criterion 21)
/-- Field types are `.const`-headed only. lean4lean names a block's own type formers by
`.const` — constructor types are **closed** (`VConstant.WF` types them in the empty context) and
`ctors_result` pins `piBody = (.const t.name us).mkApps …` — so MetaRocq's `tRel` clause has no
counterpart here and the block's self-reference is admitted through `own`. There is no `.bvar`
clause: `piBinders[i]` sits under `i` binders, so a `.bvar j` there has `j < i` and can never be
a type former. -/
def FOType (own : List Name) (fo : Name → Prop) : VExpr → Prop
  | .const I _ => I ∈ own ∨ fo I
  | _          => False
structure FirstOrderDecl (own : List Name) (fo : Name → Prop) (decl : VInductDecl) : Prop where
  mono        : decl.uvars = 0                    -- declared scope restriction, see below
  informative : ∀ t ∈ decl.types, ∃ ℓ, t.type.piBody = .sort ℓ ∧ ℓ.IsNeverZero
  noIndices   : ∀ t ∈ decl.types, t.type.piArity = decl.nparams   -- declared scope restriction
  fields      : ∀ t ∈ decl.types, ∀ c ∈ t.ctors, ∀ i < c.type.piArity,
                  ∃ A, c.type.piBinders[i]? = some A ∧ FOType own fo A
/-- The closure is **closed inside the definition** — a free `fo` parameter made T7/T9
refutable (`fo := fun _ => True` accepts a `True`-fielded `Type`). `FOClosed` is a post-fixed
point: every name in `fo` is declared, informative and first-order w.r.t. `fo` itself; the
checker's visited set is the witness. `Nat` is accepted with `fo = {Nat}` (succ's field is the
block's own former); a `True`-fielded wrapper is rejected because `True` has no informative
declaration in any `fo`. -/
def FOClosed (env : VEnv) (fo : Name → Prop) : Prop :=
  ∀ J, fo J → ∃ decl, HasInduct env decl ∧
    FirstOrderDecl (decl.types.map (·.name)) fo decl ∧ ∃ t ∈ decl.types, t.name = J
def FirstOrderInd (env : VEnv) (I : Name) : Prop := ∃ fo, FOClosed env fo ∧ fo I
def firstOrderIndB (tbl : SourceTable) (fuel : Nat) (I : Name) : Bool
theorem firstOrderIndB_sound (P : ErasureSpec …) (ht : SourceTableAdequate lenv tbl) :
    firstOrderIndB tbl fuel I = true → FirstOrderInd env I    -- visited set = the fo witness
```

`fields` is `[L Def. 14]` restricted to unapplied field types (matching `firstorder_type`'s
`args = []`); `informative` is the *result-sort* half of `[L Def. 6]`, whose *conclusion* is
`firstorder_no_box`. `mono` and `noIndices` come from **neither** paper nor from
`firstorder_ind`: they are declared scope restrictions with class-**C** ledger rows beside
N16/N18 — they reject types (universe-polymorphic, indexed) that are genuinely first-order and
box-free, and they are stated as such, not booked to the sources. `Nat`, `Bool` and
BinaryTrees' `Tree` satisfy all four conjuncts at the pinned lean4lean.

### 4.13 `lbEval` — the certified target evaluator — `Semantics/Compute.lean`

```lean
def lbEval (Σ : GlobalDeclarations) (fl : WcbvFlags) (fuel : Nat) : LBTerm → Option LBTerm
theorem lbEval_sound (h : lbEval Σ fl fuel t = some v) : WcbvEval Σ fl t v      -- class A
```

Unconditional; **already in the tree** (`Semantics/Compute.lean`, 338 lines, proved,
`#print axioms lbEval_sound = [propext]` — U0.4 wires it into the build root and adds
`green-check`, it does not rewrite it); every step one `WcbvEval` rule. It turns the target-side
evaluation of
every green rung into `by rfl`, and it doubles as a differential oracle: `lake exe green-check`
compares `lbEval Σ eraseFlags` on the committed `.ast` with `peregrine eval` — a
cross-implementation agreement test on the λ□ semantics itself (CLAUDE.md's cheapest real
functional check). `srEval` (the source-side twin) is **W6-optional** and is built per flag slice
only if its soundness proof stays small; `eraseB` is **not built**.

### 4.14 The ledger — T11 — `test/Ledger.lean`

```lean
#print axioms LeanToLambdaBox.erases_correct
#print axioms LeanToLambdaBox.LowerBlock.lambda_of_fixLambda
#print axioms LeanToLambdaBox.Lower.constToFix
#print axioms LeanToLambdaBox.visitExpr_refines_erasesLB
#print axioms LeanToLambdaBox.visitExpr_refines_erasesLBFix
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorder
#print axioms LeanToLambdaBox.green_G1
#print axioms LeanToLambdaBox.green_G8
```

`test/ledger.expected` holds **exactly** the `#print axioms` output and nothing else — that is
what a `diff` can measure; `#print axioms` reports `sorryAx` as one flat name with no provenance,
so provenance lives in `doc/trust.md`, whose every `file:line` and identifier `lake exe hygiene`
resolves. Its rows: **(a1)** lean4lean's inherited `sorryAx` cluster at the pinned rev with
`file:line` (`Injectivity.lean:12,21,34`, `UniqueTyping.lean:174`, `ChurchRosser.lean:1193,1212`),
reaching here through `TrExprS.uniq` and `IsDefEq.uniqU`; **(a2)** `EnvLemmas.lean:334
VEnv.WF.patsStrong`, marked **fork-authored, not inherited** — which no current document does;
**(a3)** the 29-name executable-checker cluster criterion 9 brings in, including two
`_native.bv_decide` axioms from Lean core; **(b)** `ErasureSpec`'s class-**D** fields
(`env_connect`, `lookup_adequate`, `fresh_names`, `oracle_refl`'s reflection clause,
`oracle_meta`, `decl_adequate` if underived), plus `hrun` and `htbl` — each a permanent named
binder, mechanised externally by `lake exe green-check`; **(c)** the class-**C** hypotheses
(`hcfg`, `hcb`, `hsup`, `mono`/`noIndices`' scope restrictions, and the source evaluation
per N7) — each a binder in a stated §5 theorem (criterion 17); **(d)** the class-**E** rows: N1
csimp, N2 extern (one coverage row per name), N3 machine `Nat`, N4 argmask, N5
auto-inline, N7 termination, N10 serialisation, N11 `.inlinings`/`.mli`, N14 size, N16 `Quot`,
N18 prop-elimination (F-PROP), the well-founded compiler-vs-kernel body gap (`deltaC`'s
propositional-only instances), peregrine's `Admitted` precondition and its `validate` gap,
MetaRocq's `firstorder_ind` defect, and Q8's dropped Rocq transport. **No second prose copy
exists anywhere else in the repository.**

---

## 5. Theorems

```lean
-- T1  (carried; `Semantics/*`)
theorem eval_deterministic : WcbvEval Σ fl t v → WcbvEval Σ fl t v' → v = v'
theorem value_final        : Value Σ fl v → WcbvEval Σ fl v v

-- T4  subject reduction                                                            class B
-- no `hcb`/`lenv` binder: `CompilerBodies` is not consumed (§4.3), so the theorem is stronger
-- than a version that carried it. Already holds at `fullFlags`, no flag restriction.
theorem SEval.defeq (henv : env.WF) (hΔ : VLCtx.WF env Us.length Δ)
    (htr : TrExprS env Us Δ e ve) (hev : SEval env bo Us fl Δ e v) :
    ∃ vv, TrExprS env Us Δ v vv ∧ env.IsDefEqU Us.length Δ.toCtx ve vv

-- T5  erases_correct — THE load-bearing simulation, on the composite, at the      class B
--     EMITTED environment (A18, A19; `bo` and `fl` are indices, not hypotheses).
--     `her`+`hlow` is `ErasesLB env Us Σ⁺ [] e t` unfolded, so that `hspec` can name the middle
--     term; `erases_correct_lb` is the folded corollary. One induction on `hev`, each arm a step
--     lemma of `ErasesCorrect/`. Six hypotheses: MetaRocq's five — `wf`, `welltyped`, evaluation,
--     `erases`, `erases_deps` — plus `LowerEnv`, which MetaRocq has no analogue of because it has
--     no pass layer, and which carries `ClosedBodies Σ⁺`/`BlockBodiesLambda Σ⁺` as clauses.
--     Seven binders, six premises: `her`+`hlow` is one. No `axiom_free` (§4.3, §4.9).
--     Elaborates as printed: `scratchpad/amend/p3_w2rev.lean`, `lake env lean`, exit 0.
theorem erases_correct
    (henv  : env.WF) (hwt : TrExprS env Us [] e ve)
    (hev   : SEval env bo Us fl [] e v)
    (her   : Erases env Us [] e t₀) (hlow : Lower Σ⁺ t₀ t)
    (hspec : ErasesEnv env bo Σ⁺ t₀)
    (henvL : LowerEnv Σ⁺ Σ) :
    ∃ v₀ v', Erases env Us [] v v₀ ∧ Lower Σ⁺ v₀ v' ∧ WcbvEval Σ eraseFlags t v'

-- T5's modules, and why there are five. `ErasesCorrect/Steps.lean` sits BELOW the aggregator and
-- holds the spine inversion kit the arms consume (`erases_mkApps_inv`, `erasable_mkApps`,
-- `erases_correct_box`/`_boxSpine`), the motive, the three step interfaces, and
-- `SEval.no_elimSpine_value`; `ErasesCorrect.lean` proves the aggregator and the ten structural
-- arms; the three arm files import `Steps.lean` only; `ErasesCorrect/Close.lean` sits ABOVE them
-- and instantiates. Without the split the graph is circular — the arms need the aggregator's file
-- for the inversion kit, and the closing edit needs theirs — and no unit's acceptance is reachable
-- inside its own dependencies (`04-AMENDMENT-W2.md` §6).
--
-- The motive, so that the arms and the aggregator state the same thing:
def Simulates (env : VEnv) (bo : Name → Option Expr) (Us : List Name)
    (Σ⁺ Σ : GlobalDeclarations) (e v : Expr) : Prop :=
  ∀ {ve : VExpr} {t₀ t : LBTerm},
    TrExprS env Us [] e ve → Erases env Us [] e t₀ → Lower Σ⁺ t₀ t →
    ErasesEnv env bo Σ⁺ t₀ →
    ∃ v₀ v', Erases env Us [] v v₀ ∧ Lower Σ⁺ v₀ v' ∧ WcbvEval Σ eraseFlags t v'

-- The three step interfaces: each is "the arm of `SEval`, with the induction hypothesis already
-- available at every subderivation". `erases_correct_of_steps` takes them as explicit hypotheses
-- and is proved by `induction hev`; `Close.lean` instantiates them with U3.2/U3.2b/U3.3's lemmas.
abbrev StepIota (env : VEnv) (bo : Name → Option Expr) (Us : List Name) (fl : SEvalFlags)
    (Σ⁺ Σ : GlobalDeclarations) : Prop :=
  -- U3.4's upstream handoff (§8.3, `04-AMENDMENT-W2.md` §14): `constOrigin_not_ctorOf`,
  -- `CasesOnShape.inj` and `IndInfo.inj` (below) each take `UpstreamAsks env` explicitly, since
  -- this development does not edit the fork that would otherwise supply them unconditionally.
  UpstreamAsks env →
  ∀ {con us I pre prev disc minors minorsv extra extrav ctor cus cargs np cidx r},
    env.WF → LowerEnv Σ⁺ Σ → fl.iota →
    CasesOnShape env con I pre.length minors.length → ConstOrigin env con →
    CtorOf env ctor I cidx →
    prev.length = pre.length →
    (∀ i, i < pre.length → SEval env bo Us fl [] pre[i]! prev[i]! ∧
        Simulates env bo Us Σ⁺ Σ pre[i]! prev[i]!) →
    SEval env bo Us fl [] disc (mkApps (.const ctor cus) cargs) →
    Simulates env bo Us Σ⁺ Σ disc (mkApps (.const ctor cus) cargs) →
    minorsv.length = minors.length →
    (∀ i, i < minors.length → SEval env bo Us fl [] minors[i]! minorsv[i]! ∧
        Simulates env bo Us Σ⁺ Σ minors[i]! minorsv[i]!) →
    extrav.length = extra.length →
    (∀ i, i < extra.length → SEval env bo Us fl [] extra[i]! extrav[i]! ∧
        Simulates env bo Us Σ⁺ Σ extra[i]! extrav[i]!) →
    cidx < minors.length →
    StepDefeq env Us [] (mkApps (.const con us) (pre ++ disc :: minors ++ extra))
      (mkApps minors[cidx]! (cargs.drop np ++ extra)) →
    SEval env bo Us fl [] (mkApps minors[cidx]! (cargs.drop np ++ extra)) r →
    Simulates env bo Us Σ⁺ Σ (mkApps minors[cidx]! (cargs.drop np ++ extra)) r →
    Simulates env bo Us Σ⁺ Σ (mkApps (.const con us) (pre ++ disc :: minors ++ extra)) r

abbrev StepProj (env : VEnv) (bo : Name → Option Expr) (Us : List Name) (fl : SEvalFlags)
    (Σ⁺ Σ : GlobalDeclarations) : Prop :=
  -- `not_erasable_of_informative` (U3.2, reused) takes `UpstreamAsks env` — see `StepIota`.
  UpstreamAsks env →
  ∀ {S i disc ctor cus cargs np r},
    env.WF → LowerEnv Σ⁺ Σ → fl.proj →
    SEval env bo Us fl [] disc (mkApps (.const ctor cus) cargs) →
    Simulates env bo Us Σ⁺ Σ disc (mkApps (.const ctor cus) cargs) →
    np + i < cargs.length →
    StepDefeq env Us [] (.proj S i disc) cargs[np + i]! →
    SEval env bo Us fl [] cargs[np + i]! r →
    Simulates env bo Us Σ⁺ Σ cargs[np + i]! r →
    Simulates env bo Us Σ⁺ Σ (.proj S i disc) r

abbrev StepDelta (env : VEnv) (bo : Name → Option Expr) (Us : List Name) (fl : SEvalFlags)
    (Σ⁺ Σ : GlobalDeclarations) : Prop :=
  ∀ {c us ups args argsv b b' v},
    env.WF → LowerEnv Σ⁺ Σ → fl.delta →
    bo c = some b → (∀ I dp nm, ¬ CasesOnShape env c I dp nm) →
    b' = b.instantiateLevelParams ups us →
    argsv.length = args.length →
    (∀ i, i < args.length → SEval env bo Us fl [] args[i]! argsv[i]! ∧
        Simulates env bo Us Σ⁺ Σ args[i]! argsv[i]!) →
    StepDefeq env Us [] (mkApps (.const c us) argsv) (mkApps b' argsv) →
    SEval env bo Us fl [] (mkApps b' argsv) v →
    Simulates env bo Us Σ⁺ Σ (mkApps b' argsv) v →
    Simulates env bo Us Σ⁺ Σ (mkApps (.const c us) args) v

theorem erases_correct_of_steps
    (step_iota : StepIota env bo Us fl Σ⁺ Σ) (step_proj : StepProj env bo Us fl Σ⁺ Σ)
    (step_delta : StepDelta env bo Us fl Σ⁺ Σ) : … -- `erases_correct`'s statement

/-- The β arm's second reading of an `.app` node: `Lower.elimApp` at `extra = []` makes the source
an eliminator spine one minor short, and no `SEval` arm applies to one. Its two premises are
`ErasesDecl.elim`'s `hsh` and `hco` (§4.8). `ErasesCorrect/Steps.lean`, U3.1. -/
theorem SEval.no_elimSpine_value (hsh : CasesOnShape env c I dp nm) (hco : ConstOrigin env c)
    (hlt : args.length < dp + 1 + nm) :
    ¬ SEval env bo Us fl Δ (mkApps (.const c us) args) w

-- T6  the passes                                                                    class A
-- There is no `lower_correct`: nothing evaluates at `Σ⁺` and nothing transports along `Lower`
-- (Q10). The unrestricted statement is refuted at `elimEta` with an `ElimBody`-shaped head
-- (`lower_correct_needs_elimBody_head`) and the guard it leaned on is false on every environment
-- reaching `Nat.succ` (`lowerNoEta_fails`); `LowerNoEta`, `DeltaChain`, `LowerPlain` and
-- `lower_correct_deltaChain`/`lowerFix_correct_atom`/`lower_correct_plain` are deleted with it.
-- What the pass layer keeps is its own metatheory, now consumed by T5's arms: the `Lower`
-- inversion kit, `Lower.{subst_comm, substList_comm, mkApps}`, `LowerFix.constToFix`,
-- `Lower.fixUnfold`, and
def BlockBodiesLambda (Σ : GlobalDeclarations) : Prop :=
  ∀ kns bs bs' ids defs, LowerBlock Σ kns bs bs' ids defs → ∀ j, j < kns.length → isLambda bs[j]!
-- `hη` and `EtaSpine` are **deleted** with the two η arms (A21): U1.7-b's counterexample was a
-- member body `.const lfC` sent to `λ_. lfC #0` by `Lower.ctorEta`, which is no longer a
-- derivation, so the conclusion is unconditional again.
theorem LowerBlock.lambda_of_fixLambda (hblk : LowerBlock Σ⁺ kns bs bs' ids defs)
    (hfl : ∀ j, j < defs.length → isLambda (defs[j]!).body = true) :
    ∀ j, j < kns.length → isLambda bs[j]! = true
theorem LBOptimize_correct  -- optional corollary, W6; blockFlags source point, §3.2
    : WcbvEval Σ propBlockFlags t v → WcbvEval (LBOptimize_env Σ) blockFlags (LBOptimize Σ t) (LBOptimize Σ v)
-- box-freedom does NOT transport along `Lower` in general (`noBox_lower_needs_noFix`, §2.2
-- finding G1-O7): `Lower.fixConst` relates the box-free `.const kn` to a block's `.fix`, whose
-- definitions carry the members' boxes. T7's box-freedom conclusion is of the erasure `tv₀`,
-- not of the lowered value `tv`; T9's own value-side conjunct (below) is stated of `tv`
-- directly, which is why it does not cite `firstorder_no_box` alone.

-- T7  first-order uniqueness and box-freedom                                        class B
theorem firstorder_erases_deterministic
    (henv : env.WF) (hfo : FirstOrderInd env I)
    (hwt : TrExprS env Us [] v vv)
    (hty : env.HasType Us.length [] vv (VExpr.mkApps (.const I us) args))
    (hval : SEval env bo Us fl [] v v)
    (h₁ : Erases env Us [] v t₁) (h₂ : Erases env Us [] v t₂) : t₁ = t₂
theorem firstorder_no_box (… same premises …) (h : Erases env Us [] v t) : NoBox t
-- (no `firstorder_lower_deterministic`: T9's answer is pinned by T7 on `tv₀` and by
--  `eval_deterministic` (T1) on `tv`; a Lower-determinism theorem would be load-bearing for
--  nothing and would need a `FirstOrderShape` predicate with no other consumer — policy 6)

-- T8  the bridge — two statements, split on the fixvar mode (§4.5)                  class B
theorem visitExpr_refines_erasesLB
    (P    : ErasureSpec lenv env Us gw)
    (htbl : SourceTableAdequate lenv tbl)
    (hcfg : ConfigPinned cfg)
    (hcb  : CompilerBodies lenv env tbl.body?)          -- N8, class C
    (hwt  : TrExprS env Us Δ e ve)                      -- e is already prepared: T8 is about
    (hsup : Supported env e)                            --   `visitExpr`, whose input is post-
    (hfx  : ctx.fixvars = none)                         --   `prepare_erasure` (`erase_run_ok`)
    (hrun : Erasure.visitExpr e s ctx cctx ref w = .ok (t, s') w')
    (hinv : BridgeInv env Us cfg (gw w) ctx s Δ) :
    ∀ Σ⁺, SpecEnv env tbl.body? s' Σ⁺ →
      ErasesLB env Us Σ⁺ Δ e t ∧ RunConcl s s' ∧ gw w ≤ gw w'
theorem visitExpr_refines_erasesLBFix   -- the block-branch companion; genuinely new work (W4)
    (…same P/htbl/hcfg/hcb/hwt/hsup/hrun/hinv…)
    (hfx : ctx.fixvars = some (fixvarMap kns ids)) (hfr : FreshFor ids ctx s) :
    ∀ Σ⁺, SpecEnv env tbl.body? s' Σ⁺ →
      ErasesLBFix env Us Σ⁺ kns ids Δ e t ∧ RunConcl s s' ∧ gw w ≤ gw w'
-- There is no `hnp`: N12 is met by its option 2 — the per-site panic table (`doc/panics.md`)
-- plus the `Supported` conjuncts that exclude the reachable sites; `visitExpr_shape_all` is
-- panic-tolerant and the bridge's arms discharge the panic branches under `Supported`.

-- T9  the capstone, applied form                                                    class B
-- Proved by composition through one named binder, `hbridge`, whose fields are the results
-- later waves prove (below); three clauses are stated in the form this wave can express
-- rather than in §4's target form, each named in the theorem's own docstring, and one further
-- binder, `hsafe`, is needed beyond the class-D list A14 names (§2.2, findings G1-O1/O2/O3/O4).
structure ErasureBridge (env : VEnv) (bo : Name → Option Expr) (fo : Name → Prop) (e : Expr)
    (Σ⁺ Σ : GlobalDeclarations) (t t₀ : LBTerm) : Prop where
  erases     : Erases env [] [] e t₀                                          -- T8, W4
  erasesEnv  : ErasesEnv env bo Σ⁺ t₀                                         -- SpecEnv.exists, W3
  lower      : Lower Σ⁺ t₀ t                                                  -- T8, W4
  lowerEnv   : LowerEnv Σ⁺ Σ                                                  -- W3
  wfSpec     : LBWfSpec Σ⁺
  wf         : LBWfPeregrine Σ t                                             -- W4; not PeregrinePre (F-ETA)
  -- one field, not two: T5 is now the whole simulation, at the emitted `Σ` (A19). Stronger
  -- than T5 by the premises T9's clause cannot supply at an applied subject (`TrExprS`/
  -- `ErasesEnv` of the subject, not of the spine); they coincide at `args = []`
  simulate     : ∀ {s t₀s ts v}, Erases env [] [] s t₀s → Lower Σ⁺ t₀s ts →
      SEval env bo [] fullFlags [] s v →
      ∃ v₀ v', Erases env [] [] v v₀ ∧ Lower Σ⁺ v₀ v' ∧ WcbvEval Σ eraseFlags ts v'  -- T5, W3
  -- stronger than T7 by the value premise `SEval … v v`, and by asking box-freedom of the
  -- LOWERED value (`noBox_lower_needs_noFix`, §2.2 finding G1-O7)
  firstorder   : ∀ {I us idx v vv tv₀ tv}, fo I → TrExprS env [] [] v vv →
      env.HasType 0 [] vv (VExpr.mkApps (.const I us) idx) →
      Erases env [] [] v tv₀ → Lower Σ⁺ tv₀ tv →
      NoBox tv ∧ ∀ tv', Erases env [] [] v tv' → tv' = tv₀                   -- T7, W3

theorem shipping_erase_correct_firstorder
    {lenv : Lean.Environment} {env : VEnv} {gw : Void IO.RealWorld → NameGenerator}
    {tbl : SourceTable} {cfg : ErasureConfig} {fuel : Nat} {e : Expr} {ve : VExpr}
    {Σ : GlobalDeclarations} {t : LBTerm} {fo : Name → Prop}
    (P     : ErasureSpec lenv env [] gw)                 -- class D, named (A14)
    (htbl  : SourceTableAdequate lenv tbl)                -- class D, named (A14)
    (hcfg  : ConfigPinned cfg)                            -- N1-N5
    (hcb   : CompilerBodies lenv env tbl.body?)           -- N8, class C (33/33 measured)
    (hwt   : TrExprS env [] [] e ve)                      -- F17: W3 witness or named fallback
    -- the `supportedB` VERDICT, not `Supported env e`: `Supported`/`supportedB_sound` are
    -- U1.8's and land in W2 (finding G1-O1); this is also the only form a rung can discharge
    -- by a checked term, since `Supported env e` mentions the non-computable `env`
    (hsup  : supportedB tbl fuel e = .ok ())              -- N6/N16/N18, decidable
    (hrun  : Erasure.erase e cfg cctx ref w = .ok (.untyped Σ (some t), inls) w')
    -- T9's decidable `axiom_free` analogue (§4.9, A24; landed by U2.8, gained by G2 — §2.4 finding
    -- W2b's own capstone premise, not a design refutation): a rung discharges it `by decide
    -- +kernel`. False exactly on Fannkuch, whose coverage row (F-EQREC) is where that fact lives.
    (hnb   : NoBodylessRefs Σ t)
    (hbridge : ∃ Σ⁺ t₀, ErasureBridge env tbl.body? fo e Σ⁺ Σ t t₀) :
    ∃ (Σ⁺ : GlobalDeclarations) (t₀ : LBTerm),
      Erases env [] [] e t₀
      ∧ ErasesEnv env tbl.body? Σ⁺ t₀
      ∧ Lower Σ⁺ t₀ t
      ∧ LowerEnv Σ⁺ Σ
      ∧ LBWfPeregrine Σ t                                 -- not PeregrinePre: F-ETA, §4.9
      -- the FIRST-ORDER SIDE CONDITION is the parameter `fo : Name → Prop` with premise `fo I`,
      -- not the closed `FirstOrderInd env I` of §4.12: `FirstOrderInd` is U3.5's (W3) and minting
      -- it here would put one name in two files. T9 holds for every `fo`; instantiating
      -- `fo := FirstOrderInd env` once U3.5 lands recovers §4.12's reading with no reproof —
      -- three sites: this binder, `ErasureBridge`'s `fo`, and `Green.lean`'s `hfo` (finding G1-O2)
      ∧ ∀ (args : List Expr) (targs : List LBTerm) (I : Name) (us : List VLevel)
          (idx : List VExpr) (v : Expr) (vv : VExpr),
          -- the SPINE PREMISE, folded through `ErasesLB` (§4.7) rather than written out as
          -- `Erases` composed with `Lower` plus the length equation `Lower.mkApps` needs — the two
          -- forms are definitionally equal (finding G1-O3, retired by G2: `erases_mkApps` deleted
          -- in favour of `ErasesLB.lean`'s `Erases.mkApps`):
          targs.length = args.length →
          (∀ i, i < args.length → ErasesLB env [] Σ⁺ [] args[i]! targs[i]!) →
          SEval env tbl.body? [] fullFlags [] (mkApps e args) v →
          TrExprS env [] [] v vv →
          env.HasType 0 [] vv (VExpr.mkApps (.const I us) idx) →
          fo I →
          ∃ tv₀ tv, Erases env [] [] v tv₀ ∧ Lower Σ⁺ tv₀ tv ∧ NoBox tv
                  ∧ (∀ tv', Erases env [] [] v tv' → tv' = tv₀)
                  ∧ WcbvEval Σ eraseFlags (LBTerm.mkApps t targs) tv
```

At `args = []` this is the spec's T9 up to the three deviations named above; at `args = [.lit 0]`
it is the observation for `benchArith`. The answer is unique: `firstorder` pins `tv₀` and
`eval_deterministic` (T1) pins `tv` given `hrun`'s emitted program. `hrun`, `htbl`, `P` and `hwt`
are the named class-**D** binders (§2 F18, A14). T9 carries **no** axiom-freedom binder: a run
that forces `Fannkuch`'s body-less `Eq.rec` has no `SEval` derivation, so that program's coverage
row (F-EQREC) is where the fact lives, not a hypothesis (§4.9).

`hcb` needs one further binder to discharge at a rung: `SourceTableAdequate` pins level
parameters, types and the constructor split, but not `ConstantInfo.safety`, and without a safety
fact `ErasureSpec`'s declaration-adequacy step cannot type the one tabled body. The added binder
is `hsafe : TableSafe lenv tbl`, `TableSafe lenv tbl := ∀ n ci, (tbl.decl? n).isSome →
lenv.find? n = some ci → DefinitionSafety.safe ≤ ci.safety` (`Green.lean`) — a fourth class-**D**
binder, filed as an amendment to A14's list (finding G1-O4).

At this wave `P`, `htbl`, `hcfg`, `hcb`, `hwt`, `hsup`, `hrun` and `hnb` are present in the
signature but consumed by nothing in the proof term, which destructures only `hbridge` and
composes its fields (finding G1-O5) — exactly what a wave landing the composition ahead of the
results it composes looks like, and the reason a reviewer must check the *statement*, not only
the proof, at this wave. `green_G1`–`green_G4` (§6) do better: they discharge
`hcfg`/`hsup`/`hnb`/`hcb` by checked terms rather than carrying them as binders (`ErasableAxioms`,
the design's first cut for this premise, is gone — retired at Wave 2, `04-AMENDMENT-W2.md` §8 —
and `NoBodylessRefs` is its landed replacement, gained at G2), and each rung's `hcb` derivation is
what first consumes `P`, `htbl` and `hsafe` for real (G1's alone, so far — G2–G4's `hcb` is class-**C**
and uninhabited, §2.4).

Composition, mirroring `[S §7.3]`: `erase_run_ok` (`ColdStartRun.lean:651`) decomposes the run into
`prepare_erasure` then `visitExpr`; T8 puts the output in `Erases ⨟ Lower` at a `Σ⁺` that
`SpecEnv.exists` constructs; T5 simulates the source evaluation into λ□ **at the emitted `Σ` and
`eraseFlags`** — the deliverable point (§3.2), reached in one step rather than two; T7 identifies
the value uniquely and shows it box-free. `hbridge`'s fields are named after exactly
these theorems.

```lean
-- T10 non-vacuity (per rung; §6)                                                    class A/B
theorem green_G1 : … ∧ WcbvEval Σ eraseFlags t (.construct natIid 0 []) := …
theorem green_G8 : … ∧ WcbvEval Σ eraseFlags (.app t (peanoLB 0)) (peanoLB 8) := …
```

---

## 6. The non-vacuity lane

Eight rungs under `VerifyBench/Spikes/`, each a real `#erase` run with a committed `.ast` and a
committed `SourceTable`. G1–G7 are closed nullary definitions (`: Nat`), following `[L Thm 15]`'s
closed-normal-term posture; G8 is the tracked `benchArith`.

| Rung | Program | Adds | Green in |
|---|---|---|---|
| G1 | `spikeZero : Nat := Nat.zero` | ctor constants, inductive declarations, δ | **W1** |
| G2 | `spikeLit : Nat := Nat.succ 3` | `Erases.lit`, the peano tower | W2 |
| G3 | `spikeLet : Nat := let x := 2; Nat.succ x` | ζ in **both** semantics | W2 |
| G4 | `spikeProj : Nat := (Prod.mk 1 2).1` | `Erases.proj`, boxed type parameters, polymorphic dependencies | W2 |
| G5 | `spikeCase : Nat := match 3 with \| 0 => 7 \| n+1 => n` | matcher inlining, `casesOn`, `.case`, ι | W3 |
| G6 | `spikeFix : Nat := Nat.add 2 3` | `_unsafe_rec`, `deltaC` + the compiler-body table, `.fix` | W3 |
| G7 | `arithClosed : Nat := benchArith 0` | the typeclass tower: 10 projections, 4 fix blocks, 5 `.case`, 19-node peano tower | W5 |
| G8 | `benchArith : Nat → Nat` | function-typed subject; the applied capstone | W5 |

`LeanToLambdaBox/Green.lean` is a tracked default build target holding, for every rung reached so
far, a theorem whose conclusion ends in a **literal** peano numeral — so it cannot be satisfied by
`□` or a stuck term — with every class-**C** hypothesis G1 inhabits by a checked term (A14: the
class-**D** binders — `P`, `htbl`, `hrun`, and `hwt` until F17's witness lands — remain named
binders in each rung's docstring, mechanised externally by `lake exe green-check`). Two class-**C**
binders are **not yet inhabited at every rung** (§2.4): `hcb : CompilerBodies …` is discharged only
at G1 — G2–G4's tabled bodies run through structure-projection unfolding (`OfNat.ofNat`,
`Prod.fst`), which routes through lean4lean's entirely-unproven `TrProj`, so `hcb` stays a named
binder at G2–G4 until that lands; `hev : SEval …` is inhabited at **no** rung before G3's
`green_G5` constructs the first `SEval` derivation. Both rows are `doc/trust.md`'s. `lenv` and
`env` are universally quantified in every rung, so the lane delivers **conditional** non-vacuity;
no computation can make it unconditional, and this sentence is where that is said. Waves that
predate T8 carry one extra binder `hbridge`; W4 discharges it and the rungs become conditional
statements about the shipping eraser with only the named class-**D** binders outstanding. `lake exe green-check` re-runs `#erase` on every rung,
byte-diffs the committed `.ast` and the committed `SourceTable`, and cross-checks `lbEval` against
`peregrine eval` where the tool is available. **Every wave from W1 on must leave `Green.lean`
elaborating**; that is a per-wave acceptance test, not a wave-5 deliverable.

---

## 7. Module plan

### 7.1 Carried unchanged (≈10,200 lines, of which 1,422 are shipping code)

| Module | Lines | Note |
|---|---|---|
| `Semantics/{Values,Eval,Env,Substitution,Metatheory}.lean` | 1,164 | flag-polymorphic throughout |
| `Closed.lean` | 871 | consumed by every simulation and by `IotaBridge` |
| `Abstract.lean` | 423 | `toBvar` metatheory; the fvar↔de Bruijn transport |
| `FixMetatheory.lean`, `FixUnfold.lean` | 1,184 | re-aimed at T5's δ arm; **statements unchanged** |
| `IotaBridge.lean` | 207 | consumed by T5's ι arm (the β-chain **is** `iota_red`); statements unchanged |
| `Erasability.lean` | 230 | + `Erasable.mono` (~10 lines, from `HasType.mono`) |
| `Relevance.lean`, `RelevanceCheck.lean` | 229 | the executable oracle and its `M.WF` soundness; **one W0 edit**: F-FUEL (§8.1) — verification-authored code, exhaustion routed to the fallback, proof-free (`isArityCheck.WF` never mentions the fuel) |
| `OutputShape.lean` | 155 | panic-**tolerant** output-shape lemmas (`noFix_toBvar`/`noBlock_toBvar` family — the panic arms are discharged, not refuted); feeds `doc/panics.md` |
| `ErasureRun.lean` | 3,234 | 74 `run_*`, `RunConcl`, `StateLe`, `⊑`/admissibility, `mutual_le_of` — relation-independent, **zero edits** |
| `Optimize.lean` | 1,090 | the pass template + W6 corollary; from W0 it consumes the renamed `propBlockFlags`/`blockFlags` (§3.2) and sits on the tracked exception list with its W6 consumer named (§9.6) — an import into the closure is not a consumer |
| `Basic.lean`, `Erasure.lean`, `Printing.lean` | 1,422 | **shipping; untouched** (§8) |

### 7.2 Re-anchored

Files in this table whose statements mention `ErasureCtx` or the six deleted `Erases` rules are
**deleted in the W1 cut** (`02-PLAN.md` U1.0) and their carried content is **re-landed from git
history** by the owning unit in the wave shown — the tree never holds a file that references a
deleted name, which is the only way N1, N2 and the per-wave green obligation can jointly hold
(the alternative — a surviving compatibility `ErasureCtx` or a second `Erases` — is the review-§2
failure mode by name). "Carried verbatim" below means re-landed with only the index rename.

| Module | Lines | What changes | Wave |
|---|---|---|---|
| `Semantics/Flags.lean` | 61 | §3.2's four constants + `propcase_weaken`; header rewritten | W0 |
| `Erases.lean` | 1,426 | eleven rules (§4.2); transport half carried; six rules' arms deleted (W1), the `tConstruct` congruence added (W2) | W1/W2 |
| `ErasesAbstract/Strengthen/Uniform.lean` | 1,865 | nine arms survive per lemma; six die with their rules (W1); one arm added (W2) | W1/W2 |
| `SourceEval.lean` (+`SourceEvalData.lean`) | 701 → ~250 | one flag-parameterised `SEval`; seven relations deleted (W1); call-by-value ι, irreducible-head values, type values (W2, A20) | W1/W2 |
| `SubjectReduction{,Full,Iota}.lean` | 1,414 → ~1,050 | merged into `SubjectReduction.lean`; β/ζ/δ written once | W1/W2/W3 |
| `EnvErasure{,Nonrec,Rec}.lean` | 1,640 → ~700 | become `ErasesEnv.lean` + `SpecEnv.lean` | W1/W3 |
| `CheckerAdequacy.lean` | 143 | the eraser-specific lemma renamed into `LeanToLambdaBox.Oracle` (W1); the seven kernel-generic declarations are *asked* upstream (U3.4, W3, `doc/upstream-asks.md` item 3) but not relocated in this schedule — moving them to the fork and deleting the file's `Lean4Lean` namespace block is a separate agent's work, deferred past W3 (§8.3, F16) | W1/deferred |
| `OracleDischarge.lean` | 123 | becomes `ErasureSpec.lean` (deleted in the W1 cut; `orc_refl`'s disjunction re-landed as `oracle_refl`/`oracle_meta`) | W1 |
| `Bridge.lean` | 674 | deleted in the W1 cut (no `Supported` name clash); `Supported`/`IsLamTelescope` re-land in `Supported.lean` (W1), `BridgeInv` re-lands in `Bridge.lean` (U4.1, W4) keeping 7 of 10 fields — `fixvars` is *not* dropped silently: its content is `ErasesLBFix`'s `kns`/`ids` indices (§4.5) | W1/W4 |
| `FirstOrder.lean` | 762 → ~250 | `informativeType_not_erasable` (`:103-131`) carried verbatim; becomes `FirstOrderInd.lean` | W3 |
| `ColdStartShape.lean` | 1,055 → ~600 | deleted in the W1 cut; `RegInvShape` re-lands keeping `kn`/`cover`/`closed`/`nofix`; five `Registered*On` fields move to `SpecEnv` | W3 (U3.5) |
| `ColdStartInduction.lean` | 1,503 | deleted in the W1 cut; `visitExpr_shape_all` re-lands carried verbatim, plus the new `visitExpr_ctorSat` (§4.9); `RegBridgeHyps` and its fixtures stay deleted | W4 (U4.5) |
| `ColdStartRun.lean` | 672 | deleted in the W1 cut; `erase_run_ok`, `run_prepare_erasure_ok` re-land carried | W4 (U4.5) |
| `VisitExprRefines.lean` | 4,641 | deleted in the W1 cut; the motives re-land against `ErasesLB`/`ErasesLBFix` + `SpecEnv` — **the long pole**, split in three files (measured shape today: 93 top-level declarations, largest `visitExpr_refines_erases_core` at 1,744 lines; the ~2,430 auxiliary lines — `Supported.*_inv`, `run_*`, `Std.Subarray` plumbing — land in `Step/Mechanical.lean` and `Supported.lean`) | W4 |
| `ErasesCorrect.lean` | 650 | deleted in the W1 cut; re-lands as T5 with five hypotheses; ι/proj arms absorbed from the deleted chains | W2-W3 |
| `ColdStart.lean` | 2,000 → ~500 | deleted in the W1 cut; T9's composition re-lands as `Capstone.lean` | W4/W5 |
| `LeanToLambdaBox.lean` | 217 | import list and header rewritten — **gate-owned in every wave** (N3a): units hand their one-line root edits to the wave gate | every wave |
| `VerifyBench/STATUS.md` | 230 | retired **into** `doc/coverage.md`, not duplicated; the F-SPARSE reproduction is carried into `doc/rework/03-DEV-FIX.md` first | W5 |

### 7.3 New

| File | Contents | Est. |
|---|---|---|
| `Semantics/Compute.lean` | `lbEval`, `lbEval_sound` — **already in the tree** (338 lines, proved, `[propext]`); U0.4 wires it | 0 |
| `Lower.lean` | `Lower` (**14 arms**), `LowerAlt(s)`, `ElimDecl`/`DefnDecl`/`RuntimeKey` (no `CtorDecl`, no `ElimHeadOf`), `LowerBlock`, inversion + shift/subst commutation, `BlockBodiesLambda`, the spine toolkit, and the **`NoBox` family** relocated from `LowerCorrect.lean` | 1,850 |
| `ErasesCorrect/Steps.lean`, `ErasesCorrect.lean`, `ErasesCorrect/{Iota,Proj,Delta}.lean`, `ErasesCorrect/Close.lean` | the spine inversion kit + `Simulates` + the three step interfaces + `SEval.no_elimSpine_value`; T5's aggregator (steps as explicit hypotheses); the three step lemmas; the closing instantiation (§5) | 3,900 |
| `Upstream.lean` (new) | `UpstreamAsks env` — the two load-bearing asks (§8.3 items 2, 6) as one named class-**C** structure, taken as an explicit hypothesis by every W3 consumer until the pin moves — U3.4 | 40 |
| `Origin.lean` | the five corollaries of `WF'.consts_origin` this tree consumes (`constOrigin_not_ctorOf`, `constOrigin_not_indInfo`, `IndInfo.inj`, `CtorOf.inj`, `CasesOnShape.inj`) plus `consts_classified`, each taking `(A : UpstreamAsks env)` — discharged unconditionally with no restatement once the pin bump lands, U3.4 | 200 |
| `LowerFix.lean` | `ConstToFVar`, `CloseConstAt`, `LowerFix`, `Lower.constToFix`, `ErasesLBFix` | 650 |
| `ElimBody.lean` | `fieldArgs`, `elimAlts`, `mkElimBody`, `mkElimBodyRec` (`ElimBody.recur`'s own right-hand side — it stays), `ElimBody`, the closedness chain up to `ElimBody.closed`, and criterion 7's three checked instances — shapes only, no evaluation theory (Q10) and no `mkCtorBody` family (its one consumer, `ErasesDecl.ctor`, is deleted); no `sing`, no `SubsingletonElim` (Q2/N18). 953 today, ≈215 after U2.10 | 0 |
| `ErasesLB.lean` | the composite + seven derived introduction lemmas + transport | 500 |
| `ErasesEnv.lean` | `ErasesDecl`, `ErasesEnv`, `LowerEnv` (no `EnvAgree`, no `congr_env`, no `PrunedFor`, no `IotaInert` — §4.8) | 650 |
| `SpecEnv.lean` | `SpecEnv`, `.mono`, `.exists` | 350 |
| `ErasesTotal.lean` | `Erases.exists_of_trExprS`, `sort_erasable`, `forallE_erasable`, `Erases.mono` | 300 |
| *(no `CompilerEnv.lean`)* | `CompilerBodies` lives in `SourceEval.lean` (§4.3); there is no second `VEnv` and no lifting kit | 0 |
| `ErasureSpec.lean` | `ErasureSpec`, `envWF`, `oracle_sound_of_run`, `LBPassR` | 280 |
| `Supported.lean` | `SupportError`, `Supported`, fuelled `supportedB`, soundness, closure lemmas, the re-landed `IsLamTelescope`/`Supported.*_inv` | 800 |
| `Output.lean` | `LBWfPeregrine`, `PeregrinePre`, reachability (`constRefs` incl. block kernames, `ReachableFrom` + its threading kit), checkers, and `NoBodylessRefs` — T9's decidable `axiom_free` analogue, with no realizer whitelist (A24). T5 carries no axiom-freedom premise (A18) | 420 |
| `FirstOrderInd.lean` | `HasInduct`, `FOType`, `FirstOrderDecl`, `FOClosed`, `FirstOrderInd`, `firstOrderIndB` + soundness, `firstorder_no_box` | 500 |
| `Witness/SourceTable.lean` | `SourceTable`, `body?`, `SourceTableAdequate`, the `reify%` elaborator, lookups | 380 |
| `Witness/TrWitness.lean` | F17's `TrExprS` witnesses via `M.WF.run'` (U3.7) | 500 |
| `VisitExprRefines/Motives.lean` | `Motives f`, the eighteen conjuncts (U4.1) | 900 |
| `VisitExprRefines/Step/Env.lean` | motives 4, 5, 6 — 6 against `ErasesLBFix` (U4.2) | 1,100 |
| `VisitExprRefines/Step/Mechanical.lean` | motives 1, 7, 8, 9, 11, 12, 18 + re-landed plumbing (U4.3) | 1,300 |
| `VisitExprRefines/Step/Passes.lean` | motives 2, 3, 10, 13, 14, 15, 16, 17 (U4.4) | 1,600 |
| `Capstone.lean` | T9 | 550 |
| `Green.lean` | the ladder's theorems | 400 |
| `VerifyBench/Spikes/G1..G8.lean` + `VerifyBench/tables/*` | the rungs and their committed tables | 300 |
| `Tools/{Reify,GreenCheck,Hygiene,Coverage}.lean` | `lake exe` drivers | 450 |
| `test/Ledger.lean` + `test/ledger.expected` | the measured ledger; its `#print axioms` rows follow their subjects, so a unit that deletes a subject owns the row | 80 |
| `doc/{rules-Erases,rules-Lower,panics,coverage,upstream-asks}.md` | criteria 3, 10, 14, 21 | — |

Net: ≈15,100 new lines against 19,302 deleted (`02-PLAN.md` §4; `VerifyBench/STATUS.md` is 230
lines, not 520) and ≈8,800 carried untouched, plus the 1,422 shipping lines this development
edits only at F-FUEL's one site (§8.1).

### 7.4 Deleted, and when

Full schedule in `02-PLAN.md` §4. Summary: `ErasureContext.lean` (251, criterion 1);
`DeltaHyps` (1,499), `CasesBridgeHyps` (287), `DataBridgeHyps` (137), `ProjBridgeHyps` (182),
`PrepareHyps` (118) — one `ErasureSpec`; `ErasesCorrectData` (1,731), `ErasesCorrectIota` (1,075) —
their ι/proj content re-lands in T5's arms; `IotaPattern` (485), `IotaDischarge` (604),
`ProjPattern` (1,059), `ProjDischarge` (415), `SubjectReductionIota` (458) — the discharge chains
keyed on the six deleted rules, with `IotaRelevant`/`IotaShape`; `RecBlockErasure` (811) —
replaced by `LowerFix`; `EraseCore` (643) minus the fuel lemmas; `FirstOrderShipping` (254),
`FirstOrderShippingIota` (553), `ShippingCorrect` (207), `ShippingCorrectData` (127) — four
capstone flavours become one; `Export/EvalT` (296), `Semantics.lean` (17), `Eval.lean` (11);
`ErasesLevels`/`ErasesInstL`/`ErasesDeltaL` (1,146, of which ~200 survive as level-instantiation
lemmas T5's δ arm needs); the three prose ledgers; ~3,000-3,500 comment lines of changelog. W2's
findings add, all **in W2**: `ElimBody.lean`'s evaluation theory — the de-Bruijn/eval kit
(`LBTerm.shift_zero`, `LBTerm.subst_spine`, `LBTerm.substList_mkApps`, `substTele` with its nine
lemmas, `elimAltsSub` with its two, `substList_reverse_fields`, `eval_self`, `EvalArgs` with its
six), the nine `wcbvEval_*` lemmas, `mkCtorBody` with `mkCtorBody_closed` and `mkCtorBody_beta`,
`mkElimBody_iota_fwd`/`_bwd`, and the `*_iota_fires` fixture block: **≈740 lines**, by **U2.10**,
which owns the file. `mkElimBodyRec` **stays** — it is `ElimBody.recur`'s right-hand side
(`ElimBody.lean:108,120`), feeds `ElimBody.closed`, and is destructed by the two surviving
inversions (`LowerFix.lean:875,885`). Also, by **U2.7**, `LowerCorrect.lean` as a whole file
(above) with its simulation half (`LowerPlain`, `lower_correct_plain`, `lowerFix_correct_plain`,
`lower_correct_deltaChain`, `lowerFix_correct_atom`, `LowerNoEta`, `DeltaChain`) and
`Lower.ctorApp`, `Lower.ctorEta`, `Lower.elimEta`, `ElimHeadOf`, `CtorDecl`, `EtaSpine`; by
**U2.5**, `IotaInert` (its two consumers, `ErasesDecl.ax`'s `hpat` and `DemoSource.ax`'s ι-freedom
conjunct, die with it — §4.8); by **U2.8**, `ErasesDecl.ctor`, `ErasableAxioms`/`AxiomRealizer`,
`PrunedFor`, `EnvAgree` with its five lemmas, all reference-free (`patHead`/`PatOf` are left
consumer-free rather than deleted — §2.4 finding W2b-F5, U3.6's); by **U2.10**, `Fuel.lean`
(Q9, W2-R4, A21, A22, A18, A24).

---

## 8. Transpiler edits

### 8.1 Required by the verification: none new; one inherited (B1), kept; one verification-authored defect (F-FUEL), fixed in W0

No wave edits `LeanToLambdaBox/{Erasure,Basic,Printing}.lean`. The proof-only edits already on
`dev/verify` (P1-P7: the `partial_fixpoint` mutual block, nine `@[partial_fixpoint_monotone]`
lemmas, `expr_withApp_eq`, `visitCasesEta`/`visitCtorEta`, the `.toArray` over-application loop,
`Basic.lean`'s de-partialized `toBvar` family, the `Relevance` import) are carried unchanged.

**B1** (the `isErasable` kernel reroute, `Erasure.lean:151-187`, plus the
`ErasureContext.lparams` threading it needs) is **kept, conditional on F-FUEL landing in W0**.
Plainly: B1 is not required to *build* the verification — T8/T9 keep their shape with the oracle
assumed — it is required by criterion 9's "discharged rather than assumed", and keeping it is a
judgement call priced at 33 axioms (29 non-standard, two Lean-core `_native.bv_decide`; measured)
against a genuinely weaker residual assumption (the near-definitional reflection of
`M.run … (RecM.run (isErasable e))`, versus "`Meta.isProp ∨ Meta.isTypeFormerType` is sound").
The discharge is **partial** (A16): the `isErasableMeta` fallback and the polymorphic-scope arm
(`ctx.lparams = Us` — at the capstone's `Us = []` the kernel arm reaches only monomorphic
declarations' runs; measured: 101 of the 191 constants in BinaryTrees' closure are polymorphic)
stay class **D** as `oracle_meta`, empirically dead on the error route (0 fallback hits /
139,196 constants). B1 introduced `Relevance.lean` onto the shipping path and changes emitted
verdicts on the success path — that is named here, not hidden. If the owner declines F-FUEL,
revert B1 (~40 lines in 5 hunks: `ErasureContext.lparams` `:120-129`, the reroute `:164-182`,
the `isErasableMeta` rename `:151`, the call sites `:217`/`:591`, the `Relevance` import) — the
one-line switch is `oracle_refl` at class **D** with criterion 9 amended; shipping a measured
regression to satisfy an acceptance criterion is not an option.

**F-FUEL** (W0, on `dev/verify` — `Relevance.lean` does not exist on `main`, so this is
verification-authored code, not a transpiler edit, and N5 does not apply): `Relevance.lean:44-45`
seeds `isArityCheck`'s ∀-telescope peel with `ty.approxDepth.toNat + 1` computed on the
*unreduced* type while the loop whnf-reduces, so a definitional alias for a ∀-telescope is judged
relevant **on the success path** — review SI-1, reproduced (`kernel=false meta=true, raw=ok
false`), latent on the corpus (0 divergences over the five programs' 82 local + 56 core
constants' closed subterms) but live in general, and arity-changing under
`remove_irrel_constr_args := true`. Fix: make fuel exhaustion `throw`, so the run `.error`s and
`Erasure.isErasable` falls back to `isErasableMeta`, reproducing the pre-B1 verdict exactly.
Proof cost zero: `isArityCheck.WF`'s statement never mentions the fuel and its proof is
`isArityCheck.loop.WF hty` (`RelevanceCheck.lean:133-137`).

Shipping-side facts under N11: **B4** (the `@[inline]` restructure at `Erasure.lean:857-875`) is
**behaviour-neutral** — both the registration and the auto-inline block sit under `single_decl`
(`:863-872`, `:885-903`), so `.ast.inlinings` is unchanged for mutual blocks and B4 needs no
ledger row. **B6** (the `MLType` extension at `:934-980`) affects only the `.mli` sidecar — one
ledger row. **B5** (`withLocalDef` dropping `nd`, `:283-295`) is argued behaviour-neutral and is
unmeasured in-repo; W5's coverage script diffs the five regenerated `.ast` files against the
frozen originals and settles it. If it diverges, that is a raised finding, not a patch. The
unverified product surface that rode in with the branch — `auto_inline_typeclass_dispatch` and
its three helpers (review SI-10) — is raised as **F-PRODUCT** (§8.2) so the verification diff is
clean.

### 8.2 Proposed for branch `dev/fix` — raised here, never applied on `dev/verify`

The repository's standing rule is *raise implementation issues, do not silently patch them*. Each
edit below is therefore specified, justified, and assigned to a separate branch; the verification
tree never depends on any of them landing.

| Id | Site | Defect | Proposed edit | Justification |
|---|---|---|---|---|
| **F-PROP** | `register_inductive`, `Erasure.lean:199-240`; `Basic.lean:164` | `OneInductiveBody.propositional` is never set (the `false` default carries the author's own hedge "I think"), so every emitted inductive — including `Prop` ones — is declared non-propositional (683/683 across all 72 `.ast`). `isPropositionalInductive` is then identically `false`, an emitted `.case` on a `□` discriminee is **stuck** at every flag point (verified: erased `And.casesOn` at a `Nat` motive fails `peregrine eval` with "branch not found"), and peregrine's verified `remove_match_on_box` (`EOptimizePropDiscr.v:35,57`) skips it | set the field from the source sort (`Meta.isProp` on the type former) | one-word change; until it lands, `And`/`Iff`/`Acc` eliminations into data ship as stuck terms, which is why N18 restricts them (Q2) |
| **F-ETA** | `visitMutual`, `Erasure.lean:878-918` | every emitted recursive body is a bare unapplied `.fix` (50/50 across the five programs: 4/10/15/11/10) with no λ-headedness check (`nonrecursive := single_decl && !name_occurs` is the only guard), so `EEtaExpandedFix.expanded_eprogram` is **false on all five programs**. The violated condition guards *evaluation preservation of peregrine's first pass*: `guarded_to_unguarded_fix` (`ETransform.v:666-682`) is the identity on terms and its whole obligation is discharged from that predicate via `eval_opt_to_target` — with it false, no verified semantics-preservation argument covers the output past T9's `WcbvEval`. peregrine's own discharge is `Admitted` (`Transforms.v:375`) and `validate` checks no η, so nothing detects it | wrap the emitted body in `rarg+1` lambdas applied to their own binders (the eraser's own TODO at `:911`) — adequate: all 50 `FixDef`s have `rarg = 0` and every self-call is applied | Coq avoids this by η-expanding before erasure (`Template/EtaExpand`). Without the edit the frontend's output violates a documented precondition of the consumer it is written for |
| **F-SPARSE** | `visitCases`, `Erasure.lean:770,817` | the inductive is recovered by `casesInfo.declName.getPrefix`, so a sparse `casesOn` (`_sparseCasesOn_`, named after the enclosing function) hits `unreachable!`, which *succeeds* at `EraseM` returning `.box`: `Quicksort` panics, exits 0, and writes a **wrong** `.ast` that passes `peregrine validate` | recover the inductive from `CasesInfo` rather than from the name, and handle `CasesAltInfo.default` | already `RAISED-not-fixed`; this design makes it visible as `SupportError.sparseCasesOn` in the predicate a reader audits and as a named row in the generated coverage table |
| **F-ACC** | `visitCases` at a `Prop`-valued inductive with an index-determined field | a consequence of F-PROP with a second stage: *today* the emitted `.case` is stuck at `Σ` (F-PROP); *if F-PROP alone is fixed*, `Acc`-shaped inductives then reduce by `iota_sing`/`remove_match_on_box`, which box a field that is **data** (`Acc.intro`'s `x : α`; measured `largeElimClause ``Acc = some (2,[1])`) and compute a wrong program | any F-PROP fix must keep `Acc`-shaped (index-determined-field) eliminations refused | restricted here by N18 (shape-keyed: `Acc.casesOn` *does* compile in Lean, so a name-keyed refusal would not close the hole); the full treatment needs type-former injectivity at the redex and is W6-at-best. Latent: `Acc`/`WellFounded`/`Quot` occur in none of the five `.ast` |
| **F-QUOT** | `Erasure.lean:873-877` | `Quot` primitives are emitted as body-less axioms, so a quotient program erases to a stuck term that passes `validate` | emit a realizer, or refuse | restricted here by N16 |
| **F-EQREC** | `Erasure.lean:873-877` | recursors reached as constants have no compiler value and are emitted body-less (`Eq.rec` in `Fannkuch.ast`), so the program is stuck there unless peregrine's `.attr` channel supplies a realizer — which the frontend does not emit | emit the remapping into `.ast.inlinings`/`.attr` | covered here by `Fannkuch`'s coverage row alone: after A18 there is no axiom-freedom premise to grant, and a run that forces the body-less constant simply has no `SEval` derivation; someone must decide whether the frontend should emit the remapping |
| **F-ETA2** | `visitCtorEtaGo`/`visitCasesEtaGo`, `Erasure.lean:705-728` | η-expansion of an under-applied constructor or eliminator pushes the **already-supplied** arguments under the new binders, where weak evaluation never reaches them: the source evaluates them once, the emitted `λ⃗. C a⃗ x⃗` evaluates them once per application, and a source value `C av` and the target value `λy. C a' y` are related by no derivation. Today's programs may not exercise it — the emitted `.ast` cannot tell an η-expansion from a user λ — but the pass is unsound as written | bind the supplied prefix first: emit `let a₁ := …; … λ⃗ x⃗. C a⃗ x⃗` | the fragment restriction **N19** (§4.4, Q12) is the verification's containment; the edit is what would remove it |
| **F-PRODUCT** | `Erasure.lean:71-118` (`auto_inline_typeclass_dispatch`, `stripLambdas`/`containsFix`/`isTrivialAlias`, the `Meta.isInstance` call) | unverified product feature added on the verification branch (review SI-10), so "what verification changed" is not a clean diff | re-home the feature via `dev/fix` (or `main`) | the verification never depends on it; N5 covers the class-**E** row for the `.inlinings` channel it drives |

### 8.3 Upstream asks (lean4lean, N15) — `doc/upstream-asks.md`

Editing the lean4lean fork is a separate agent's work; this repository only **files** asks
(`doc/upstream-asks.md`, U3.4). Until the pin actually moves, every W3 consumer of ask 2 or ask 6
takes the asked fact as a named, class-**C** hypothesis — the structure `UpstreamAsks env` in
`LeanToLambdaBox/Upstream.lean` (U3.4.md) — rather than a design assuming the fork has already
changed. This is not a premise of `IotaRelevant`'s shape (criterion 6): it is the two already-filed
asks, unweakened and unrestated, made an explicit, auditable, tracked binder until the fork
accepts them, at which point `UpstreamAsks` is discharged by the re-pin with no change to any
consumer's statement shape (`doc/trust.md`'s row says so).

1. `VEnv.WF'.defeqOwn` — a `WF'` environment grants each constant at most one defining equation
   (the `defeqs` twin of `WF'.pats_origin`; the 130-line proof exists,
   `scratchpad/gate/d3_defeq_unique.lean`, no frontend dependency) — the fact that decided Q3
   and belongs upstream, cited in the ledger as why `envC` was dropped. Not consumed by any W3
   theorem, so not a field of `UpstreamAsks`.
2. `VEnv.WF'.consts_origin`, the constants-keyed twin of `WF'.pats_origin`
   (`InductiveParams.lean:93`), plus `iotaRHS'_Generic` — the missing link in `largeElim_of_wf`
   (§4.6). **Load-bearing from W3** (`04-AMENDMENT-W2.md` §9): its corollaries
   `constOrigin_not_ctorOf`, `constOrigin_not_indInfo`, `IndInfo.inj`, `CtorOf.inj` and
   `CasesOnShape.inj`, plus the totality direction `consts_classified` (§2.4 finding W2b-F4's
   `hclass`), are what T7, T5's ι arm and `SEval.no_elimSpine_value` need. `Origin.lean` derives
   them from `UpstreamAsks.constsOrigin` as theorems taking `(A : UpstreamAsks env)`; introduction
   sites need none of it — `Erases.const`'s premise is the positive `ConstOrigin` (§4.2), which a
   rung discharges from its own declaration list.
3. The seven kernel-generic declarations currently in `CheckerAdequacy.lean` (`VContext.ofMLCtx`
   and its three `@[simp]` projections, `VState.WF.initial`, `M.WF.run'`, `kernelNGen`), which
   criterion 21 forbids here and criterion 9 needs. **Deferred**, not landed in W3: relocating them
   requires the fork to hold them first, which this repository cannot do; `CheckerAdequacy.lean`'s
   `Lean4Lean` namespace block is therefore *not* deleted this wave (`02-PLAN.md` §4), and criterion
   21's grep is expected to fail until the pin bump, which is a fact `doc/trust.md` states rather
   than a check any W3 gate runs.
4. A `TrEnv'` inversion on the `induct`/`AddInduct` clause yielding `InductiveVal ↔ VInductDecl`
   (the shape of `TrEnv'.structure_rec`/`TrEnv'.pats_iota'`), which turns `decl_adequate` from an
   assumed field into a theorem off `env_connect`; and `addDecl.WF`'s `inductDecl` case
   (`Verify/Environment.lean:208`, `sorry` at the pin), the lemma that would let `env_connect`
   itself be derived.
5. The `Quot.ind` divergence between `Theory/Quot.lean:11` and the executable checker.
6. **`IsDefEqU.const_arity_inv`** — an application headed by an inductive type constant is defeq
   to neither a sort nor a Π. Its home is `Theory/Typing/Injectivity.lean` ("A bunch of important
   structural theorems which we can't prove :("), beside `sort_inv`, `forallE_inv_stratified` and
   `sort_forallE_inv`, all three `sorry` at the pin and all three already inherited here through
   `Erasable.app`. Three consumers, all of them theorems and none of them a binder **once the pin
   has moved** — until then each takes `UpstreamAsks.constArityInv` explicitly: T5's ι arm (a
   value of an informative inductive is not erasable, so the `.case` node's discriminant evaluates
   to a `.construct` spine and not to `.box`), T5's proj arm (same fact), and T7's
   `firstorder_no_box` (same fact, plus the saturation of a well-typed constructor value). MetaRocq
   discharges the same obligation from PCUIC's inversion lemmas; this is the one place where
   lean4lean's incomplete metatheory is load-bearing for the ι fragment (R14).
7. **Reported, not asked:** MetaRocq's shipped `firstorder_ind` is `false` on `nat`
   (`PCUICFirstorder.v:59`'s sort conjunct — the code's defect, not `[S §7.3]`'s prose), so every
   theorem guarded by it is vacuously guarded; peregrine's `run_untyped_transforms` precondition
   obligation is `Admitted` (`Transforms.v:375`); and `peregrine validate` is
   `parse_ast ;; get_config ;; check_wf` only (`Pipeline.v:245-248`, `CheckWf.v:182-183`) — no
   expandedness check, which is what makes F-ETA undetectable downstream.
8. **Kernel-generic, proved locally, filed for consolidation** (§2.4; not load-bearing — no fork
   change is needed for any of the three): the constructor-side twins of `wf'_induct_origin`/
   `IndInfo.constant_isArity` (`ErasesTotal.lean`), currently parked in `SourceEval.lean:362-386`
   for want of a dedicated home (sorryAx-free at the pin):

   ```lean
   theorem IsArity.piBody_sort {A : VExpr} (h : IsArity A) : ∃ u, A.piBody = .sort u
   theorem CtorOf.constant_ctorResult {env : VEnv} {c I : Name} {k : Nat} (h : CtorOf env c I k) :
       ∃ ci np nf nind, env.constants c = some ci ∧ ci.type.CtorResult I np nf nind
   theorem CtorOf.not_indInfo {env : VEnv} {c I : Name} {k : Nat} {iid : InductiveId}
       {np : Nat} {nfs : List Nat} (hc : CtorOf env c I k) : ¬ IndInfo env c iid np nfs
   ```

   Natural home is `Origin.lean` (item 2) once U3.4 lands, alongside `wf'_induct_origin`/
   `IndInfo.constant_isArity`, which make the same argument from the type-former side.

---

## 9. Documentation and code-quality policy

1. **Current fact only.** No "used to", commit hash, date, slice tag, round name, memory
   reference, or untracked-handoff citation in any docstring. History goes in commit messages.
   The specific repairs the review demanded are in scope and scheduled in W0:
   `Semantics/Flags.lean:19-24` (asserts the opposite of the design), the seven "no `addPat`
   clause" sites and the eight "`addInduct_WF` is `sorry`" sites (both measured **false** at
   the pinned lean4lean rev), the five stale oracle descriptions, `Supported.casesApp`'s
   sparse-`casesOn` sentence, and the `ProjDischarge`/`ProjPattern` contradiction about
   `proj_defeq`.
2. **One fact, one home.** Every claim about upstream state lives once, in `test/ledger.expected`,
   with the `file:line` and the command that measured it. CI greps for a second copy.
3. **Length budget.** ≤ 8 lines per lemma/field docstring, ≤ 40 per module header. Longer is a
   status document and belongs in `doc/`, tracked.
4. **Every backticked identifier resolves; every cited document exists.** CI grep
   (`lake exe hygiene`).
5. **A docstring says what the object *is*, and why a hypothesis is not slack** — with a
   counterexample where one exists. The models are `IotaBridge.lean:96-111`,
   `Semantics/Values.lean:79`, `Semantics/Eval.lean:29`. Under this design that duty is heaviest
   on `Lower`'s `elimApp` arm and two fix arms, and on the **absence** of the two η arms — whose
   replacement comment states the two real reasons (a supplied prefix would sit under a binder weak
   evaluation never enters; and a bare η-expanded head still composes under `app` into an unbounded
   β-redex target, §4.4, Q12).
6. **No dead code.** Every declaration is in `Green.lean`'s or `Capstone.lean`'s transitive import
   closure, or on a short tracked exception list in `doc/coverage.md`. At W5 the list may carry
   only rows naming a scheduled **W6** unit as consumer (today: `Optimize.lean` → U6.2), each with
   the trigger "deleted if its W6 unit is not executed this cycle" — an import into the closure is
   not a consumer and never counts. No module receives a standing exemption.
7. **No duplicate definitions, no forked relations.** Growth is by parameterisation: `SEval` by
   `SEvalFlags`, `WcbvEval` by `WcbvFlags`, `LBPassR` by its relation field. The known duplicates
   are deleted, not documented. In particular there is exactly one λ□→λ□ relation (`Lower`); the
   stuck-value cases are handled by head predicates inside it, not by an auxiliary twin.
8. **Kernel lemmas upstream** (§8.3); no `Lean4Lean`-namespace declaration remains here.
9. **One measured ledger** (§4.14); no prose ledger anywhere.
10. **Non-vacuity guards** for every relation and every pass, in the style of
    `Semantics/Metatheory.lean:417` and `Optimize.lean:1066` — including a hand-built **two-member
    mutual block** for `Lower`'s fix arms, since 0 of the 50 emitted `FixDef`s are mutual and that
    case would otherwise ship unmeasured.
11. **No `native_decide`**; `set_option` only with a stated reason; no `@[simp]` on foreign
    namespaces. The tree is clean here and stays so.

---

## 10. Risk register

| # | Risk | Likelihood | Impact | Mitigation / trigger |
|---|---|---|---|---|
| R1 | The fix wall: `Lower.constToFix` harder than budget, **or the block-body motive unstateable** | medium | high | The hard half — `closeFix_substList_fixSubst` (`FixUnfold.lean:748`) and `FixUnfoldChain.eval` (`:830`, gated on `with_guarded_fix`, which `eraseFlags` satisfies) — is already proved. It is **W1** work with its own unit and its own acceptance test, so a failure surfaces in week one, not in W4. **Trigger — on the motive, not only the transport:** if by the end of W1 `Lower.constToFix` is unproved *or* `ErasesLBFix` cannot be exhibited on the two-member fixture (U1.7's stateability test — a `constToFix` that elaborates while the motive is unstateable does not clear the wall), stop and re-scope: the fallback is to restrict the fragment to non-recursive declarations (which covers 0/5 benchmarks) and say so, i.e. the project has no viable deliverable — this is the one risk that can end it |
| R2 | `SpecEnv`'s antitone threading does not compose at some motive | medium | high | `SpecEnv.mono` is proved from `StateLe`, which every motive already concludes; W4 sequences the three environment-facing motives (4, 5, 6) **first** so a failure surfaces on day one of the wave |
| R3 | T5's ι arm needs `pats` ↔ `ElimBody` agreement, touching the `patsStrong` residual | high | medium | The known seam, declared in §1 of the spec. `IndInfo` states the agreement at declaration level, where a pats-carrying `VEnv.WF` is constructible today (21/22 clauses discharged in the Q2 probe); the nine "unconstructible" docstrings are false and are deleted in W0 |
| R4 | `VEnv.WF'.consts_origin` does not land upstream in time | medium | **medium** | Refreshed at Wave 2: the eleventh rule makes the constructor/inductive-name/plain-constant classification part of `Erases`, so the *exclusion* direction is load-bearing from W3 — T7's uniqueness and T5's ι head step (§8.3 ask 2). Not load-bearing for *introduction*: `Erases.const` takes the positive `ConstOrigin`, so every rung and T8's bridge discharge it from a declaration list. **Trigger:** U3.4 is scheduled first in W3; if the ask is refused, T7 and the ι/proj arms are blocked and `doc/trust.md` says so |
| R5 | The four redex arms' exactness against `visitCases`/`visitConstructor` is worse than believed (over-application placement, `mkAlt` binder order) | medium | medium | The relation is *name-free* and drops the `pre` args, so the two known sources of exactness trouble do not arise; the residual risk is spine shape, which W2's differential test measures directly (reconstruct the `Erases`-image from the run, check the emitted term is in `Lower Σ⁺` of it by a decidable checker, on all five programs). This is the check no candidate design proposed and the one that would have caught A's own T5 hole |
| R6 | `Erases.exists_of_trExprS` is harder than budgeted (`proj` case needs `TrProj`) | medium | low | The two hard cases are criterion 10's lemmas, required anyway; the `proj` case reuses `Erases.proj`'s deliberate `TrProj`-freedom. Fallback: make `hpre` a premise of `ErasesLB.cases` discharged in the bridge from `BridgeInv.mlc` |
| R7 | Reified `SourceTable` drifts from the real environment | low | high | `reify%` reads `getEnv` in the same elaboration as the rung, so there is no committed artifact to drift and no regenerate-and-diff circularity; the residual assumption is the named binder `htbl` (elaborator-copy + the `prepare_erasure` run clause), and `green-check` still byte-diffs the emitted `.ast` (the output half of `hrun`) |
| R8 | Genuine mutual blocks are unexercised (0/50 emitted `FixDef`s are mutual) | medium | medium | `LowerBlock` is stated for lists, not singletons; W1's non-vacuity guard is a hand-built two-element block; the coverage table records that no benchmark exercises it |
| R9 | `by rfl` at G7 (2^3 through a 19-node peano tower and 27 constants) exceeds kernel budgets | medium | low | `lbEval` is fuel-indexed and structurally recursive; `set_option maxRecDepth` with a stated reason. Fallback recorded in the coverage table: evaluate a smaller closed rung and state that G7's arithmetic is checked by `green-check` externally |
| R10 | The 33-axiom fixture (criterion 9 × 15) is judged unacceptable at review | low | low | The ledger classifies all 29 non-standard names and distinguishes Lean-core `_native.bv_decide` from lean4lean's `sorryAx`; the alternative — `oracle_refl` at class **D**, criterion 9 amended, B1 reverted (~40 lines, §8.1) — is documented as the switch and its price named; §8.1 owns the decision, this row only prices it |
| R11 | `hwt`/`hty` cannot be inhabited for a 39-declaration program (§2 F17) | medium | medium | W3's `TrWitness` unit routes lean4lean's checker; named fallback is class-**D** binders plus an amendment to criterion 13, recorded in the same commit |
| R12 | The relational conclusion is read as weaker than a functional one | low | low | §1.2 states the papers' posture; W6's functional refinement is additive and needs no restatement of T8, since a function equality implies relation membership |
| R14 | The upstream discrimination lemma ("an application headed by an inductive type constant is defeq to neither a sort nor a Π") is refused, or the fork cannot be re-pinned | medium | high | It is one statement in lean4lean's `Injectivity.lean`, beside three `sorry`s of the same kind that this development already inherits through `Erasable.app`. It is a *theorem*, so no rung carries a binder for it; its three consumers are T5's ι and proj arms and T7's `firstorder_no_box`. **Trigger:** U3.4 is scheduled first in W3, so a refusal surfaces on day one; the fallback is that those three are blocked and `doc/trust.md` says so — never a premise of `IotaRelevant`'s shape (§8.3) |
| R15 | Restriction **N19** (no under-applied constructor or eliminator occurrence) fails on a tracked program | medium | medium | `supportedB` decides it at U3.8, **before** the ι arm is proved. The emitted `.ast` cannot settle it — an η-expansion and a user λ print identically (measured: 1-3 such nodes per file in `VerifyBench/ast`) — so the check is on the source. Contingency if it fails: one new `elimEta` arm whose saturated body is forced to be an `elimApp` image (so it cannot nest), plus one collapse lemma through `wcbvEval_mkApps_mkLambdas_substList` and `Lower.substList_comm` — ≈300 lines and two extra step-lemma cases, no theorem statement changes. For constructors the restriction disappears once **F-ETA2** is repaired, since applied-form λ□ evaluates partial constructor spines natively |
| R17 | `CasesOnShape` does not match how `casesOn`/`pats` are actually shaped at the pin | medium | medium | It is read off the *inductive declaration* (`VInductDecl.nparams`, `VInductiveType.ctors`), not off the pattern table, precisely so that it does not depend on how `pats` is populated. **Trigger:** U2.6's `_fires` witness on `Nat.casesOn`, due before anything consumes it; if the shape is wrong, the fix is local to `CasesOnShape` and `ErasesDecl.elim` |
| R18 | The `.case` node's arity data is in scope only if reachability tracks inductive blocks, and the `constRefs` extension changes every rung's `rfl`-computed closure | low | low | U2.8 re-measures G1's closure in the same commit; the gate re-runs it. The extension is now unopposed, `AxiomFree` having been deleted (`04-AMENDMENT-W2.md` A-F2) |
| R19 | T5's β arm cannot discharge `Lower.elimApp`'s saturated reading, because `ErasesDecl.elim`'s `hsh`/`hco` do not reach it through `hspec` | medium | medium | The case arises only at `extra = []`, where the source `.app f a` *is* a saturated eliminator spine and the β rule's own `hf` is uninhabited (`SEval.no_elimSpine_value`, §5). U3.1 owns it and prices it at ≈150 lines. **Fallback:** state the eliminator reading as an explicit side condition of `StepBeta` and discharge it at `Close.lean` from the rung's environment — one extra hypothesis on a step interface, no change to `erases_correct`'s statement |
| R20 | Restriction **N21** empties a tracked rung: a program reaches a recursor, which has no `SEval` derivation at all | medium | medium | Recursors are tabled body-less (`Witness/SourceTable.lean:211`), so `deltaC` cannot fire and no value arm applies; that is why `supportedB` must reject them rather than let them through (`Supported.lean:239`). What keeps the five programs clear is N8: the eraser and `SEval` read *compiler* bodies, in which structural recursion is direct rather than `brecOn`-mediated. **Trigger:** U3.8 decides it, second in W3, in the same unit that lands the rejection; a failure takes the program out of the fragment and `doc/coverage.md` names the construct |
| R16 | Restriction **N20**'s per-branch obligation is larger than its decidable check suggests, or is uninhabitable on a rung | **medium** | medium | The decidable sufficient condition — every prefix argument, minor and extra argument already a syntactic value — **fails on all five programs**, and the earlier "measured mitigation" was false: Lean's match compiler thunks a nullary branch into an *application*, not a λ (measured across `VerifyBench/ast/*.ast`: no nullary alternative has a `tLambda` head; `Arith.ast`'s `Nat` zero-branch is `(tApp (tRel 1) (tConst Unit.unit))`). So `hmins` needs an `SEval` derivation per unselected branch per ι step. That is a cost, not a vacuity — Lean is total, so every well-typed closed term normalises and each unselected branch has a value, while partial and `unsafe` bodies are already outside through N8 — but it is proof volume proportional to the program, not to its trace. **Trigger:** G3's `green_G5` is the first rung that builds one; if it runs long, the rungs stay small and `doc/coverage.md` records which programs carry a constructed `hev` and which carry it as a binder |
| R13 | Shipping edit B1's under-erasure (review SI-1) fires inside the fragment | low — measured: 1 divergence in 139,196 constants, and that one planted by the probe; 0 on the five programs' closures | medium | **Removed at W0 by F-FUEL** (§8.1). Until then, contained because `Erases.box` carries no `¬Erasable` guard and the structural rules carry no negative side condition (mirroring MetaRocq `Extract.v:88-141`), so a structurally-erased type-former is a legal `Erases` image and T8's refinement is unaffected; `isErasable` on a syntactic `.sort`/`.forallE` returns `true` unconditionally, so SI-1 cannot reach `Erasure.lean:602`'s `unreachable!`; the argmask half is off by default (N4's `hprune`). `Supported` and the oracle fields do **not** constrain a false verdict — the containment is the relation's, not theirs |
