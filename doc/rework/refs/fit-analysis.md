# Fit analysis — the current verification project against the reference papers

**Scope.** This maps every formal object of the three reference developments
(Letouzey TYPES 2002; Sozeau *et al.* J. ACM 72(1) §7; Dima's MPRI report as the
specification of the *subject*) onto what exists today under
`LeanToLambdaBox/`, judges fidelity, and says keep / re-anchor / rewrite / delete.
Inputs: the four analyses in this directory, the 2026-09-10 critical review
(§1 crown-theorem audits, §2 lens verdicts, §4 completeness critic), and the code
at `dev/verify` (42,632 lines under `LeanToLambdaBox/`, 67 modules).

**Verdict in one paragraph.** The *target* half of the development is already the
paper's: one flag-parameterised `WcbvEval` transcribed rule-for-rule from
`EWcbvEval` with a correspondence table, its metatheory, the de Bruijn kit, and
`optimize`. The *bridge* half — the 18-motive fixpoint induction over the real
`visitExpr`, the run algebra it stands on, the fvar↔de-Bruijn transport, the fix
closing/unfolding inverse — is genuine, sorryAx-free engineering with no
counterpart in any of the papers (the papers erase a de Bruijn term with a total
function; this repo erases a locally-nameless `Expr` inside a `partial_fixpoint`
monad, and that gap had to be built). What does *not* fit is the middle: the
erasure relation `Erases` is not Fig. 18 and not Def. 10 — it is a
*registry-indexed compiler specification* that absorbed four of the paper's L4
optimisation passes (constructor blocking, `casesOn`→`.case`, mutual-block
→`.fix`, literal towers) into the relation itself, and the premise layer that
grew around that decision (seven `Prop` bundles, eight source-evaluation
relations, `IotaRelevant`, `Supported`) is the epicycle. The rework therefore
keeps almost all of L0 and most of L2's machinery, rewrites L1, and re-derives
L3–L5 on top.

---

## 0. The reference skeleton the rework must instantiate

The three papers agree on a five-layer architecture; the disagreements are only
about vocabulary. Written in the Lean setting (from `metacoq-erasure.md` §4.1):

| Layer | Object | Letouzey | Sozeau §7 |
|---|---|---|---|
| **L0** | λ□ syntax + one weak-cbv evaluation with the box rules + flags | CIC□, `→_rw`, `→_□w`, Def. 8 | `E.term`, `⇓`, amendments (1)(2)(3), `WcbvFlags` |
| **L1** | erasure *relation*: strict congruence over the source + one box rule | `(Γ,t) ◄ (Γ₀,t₀)` (Def. 10, four clauses) | `Σ;Γ ⊢ t ⇝E t'` (Fig. 18) |
| **L2** | erasure *function* + relation ⊇ its graph | `E` (Def. 3), Lemma 11 | `E` (Fig. 17), `erases_erase`; oracle `is_erasableb`; abstract env |
| **L3** | forward simulation + environment relation | Thm 12 / Thm 13 (both squares) | `erases_correct` + `erases_deps`, on subject reduction |
| **L4** | λ□→λ□ passes, each with its own preservation theorem | §4 (700 unproved lines, explicitly outside) | `optimize`/`optimize_correct`, flag-discharging |
| **L5** | first-order collapse + observational capstone | Def. 6/14, Thm 15 | `firstorder_ind`, `firstorder_erases_deterministic`, `erase_correct_firstorder` |

Two structural rules follow, and they are what the current tree violates:

* **R-cong (from both papers).** Every rule of L1 except the box rule is a
  congruence over a *source constructor*, producing the *same-named* target
  constructor. `Lean.Expr` has no `construct`/`case`/`fix` constructor, so those
  three λ□ nodes may not be produced by L1 at all — they are L4.
* **R-prune (Letouzey Def. 3).** L2's function is *pruning only*: same tree, same
  binder count, same spine length, `□` the only change. Anything that changes
  shape (argmasks, η-expansion to arity, minors→alternatives, literal towers,
  `casesOn` spine splitting) is L4.

---

## 1. Object-by-object map

### 1.1 L0 — λ□ syntax and semantics

| Paper object | Current counterpart | Fidelity | Verdict |
|---|---|---|---|
| `E.term` (Fig. 16) / CIC□ | `LBTerm`, `LeanToLambdaBox/Basic.lean:90` | faithful modulo three deliberate, documented deviations | **keep as is** |
| `WcbvFlags`, `disable_prop_cases` | `WcbvFlags`, `Semantics/Flags.lean:37`; `defaultFlags`/`optFlags`/`targetFlags`/`appliedFlags` | faithful | **keep, fix the header** |
| `Σ ⊢ t ⇓ v` with amendments (1)(2)(3) | `WcbvEval`, `Semantics/Eval.lean:79` | faithful, rule-for-rule, with an in-code correspondence table (`Eval.lean:24-45`) | **keep as is** |
| `(□ u) →□ □` (Letouzey Def. 5 = `eval_box`) | `WcbvEval.app_box`, `Eval.lean:97` | faithful (evaluates and drops the argument, as `eval_box` does) | **keep** |
| `Cases_n □ of f end →ι f □…□` (Def. 8 = `eval_iota_sing`) | `WcbvEval.iota_sing`, `Eval.lean:171`, guarded by `with_prop_case` | faithful | **keep** — this is what makes `Acc.rec`/`WellFounded.fix` runnable |
| Def. 8's "guard is `□` **or** a constructor" fixpoint clause | `WcbvEval.fix_guarded`, `Eval.lean:210` — unfolds on *argument count*, with no constructor side condition | faithful to `EWcbvEval.eval_fix`, and *a fortiori* covers the boxed-guard case | **keep**; record explicitly that Letouzey's clause is subsumed |
| `value`/`value_head`/`atom` (§5.6 Fig. 12) | `Value`, `atomValue`, `isFixApp`/`isConstructApp`/`isStuckApp`, `Semantics/Values.lean` | faithful, with a MetaCoq correspondence table | **keep** |
| `inductive_isprop_and_pars`, `cstr_arity` | `isPropositionalInductive`, `constructorArity`, `Semantics/Env.lean` | faithful | **keep** |
| `eval_deterministic`, `eval_value`, `eval_to_value`, `value_final` | `Semantics/Metatheory.lean` (25 theorems, non-vacuity guards at :417/:421/:425) | faithful, sorryAx-free | **keep** |
| block vs applied constructors | both modelled, kept disjoint by `with_constructor_as_block`; the shipping path pinned at `appliedFlags` | correct, and matches the Zulip contract (T1: peregrine's pass ordering *requires* applied form) | **keep**; `Flags.lean:19-24`'s header states the opposite and must be rewritten |

**L0 is the one layer that already satisfies every requirement** (metacoq R1,
letouzey R8/R9, zulip Z2). No paper object is missing. Three defects, all
documentation: `Flags.lean:19-24` asserts "we are always block form" (false — the
capstones run at `appliedFlags`); the aggregator `Semantics.lean` and the shim
`Eval.lean` add nothing; `Export/EvalT.lean` (296 lines) is a `Type`-valued twin
for a Rocq transport programme that `grep -rn Erases rocq/` shows was never
scoped to reach the relation.

### 1.2 L1 — the erasure relation

This is where the fit fails, and it is the *most important missing fact* the
review identified.

| Paper object | Current counterpart | Fidelity | Verdict |
|---|---|---|---|
| `Σ;Γ ⊢ t ⇝E t'` (Fig. 18) / `◄` (Def. 10) | `Erases`, `Erases.lean:415`, 15 rules: `box lit proj bvar fvar const app lam letE ctor ctor_head cases fixvar const_fix fix` | **deviates fundamentally**: 6 of 15 rules have no Fig. 18 / Def. 10 counterpart, and the relation is indexed by the eraser's own registry | **rewrite** |
| `erases_box` (the one nondeterministic rule) | `Erases.box`, `Erases.lean:419` — `TrExprS` witness + `Erasable` | **faithful, and the best rule in the file** | **keep and re-anchor** (re-index onto the new context) |
| `isErasable Σ Γ t` (proof ∨ arity) | `Erasable`, `Erasability.lean:~62`: `∃ A, HasType e A ∧ (HasType A (sort 0) ∨ IsArityUpTo A)` | **faithful**, both disjuncts, arity taken *up to defeq* (more faithful than a syntactic `isArity`) | **keep as is** |
| `isArity` (fn. 13) / Letouzey Def. 1 type scheme | `IsArity` + `IsArityUpTo`, `Erasability.lean` | faithful | **keep** |
| Lemma 2 (Stability) / weakening + substitutivity of `⇝E` (§7.3) | `IsArity.inst/.liftN`, `IsArityUpTo.inst/.weakN/.defeq`, `Erasable.weakN/.inst/.defeq` (`Erasability.lean`); `erases_shift`, `erases_subst`, `Erases.abstract`, `Erases.thin_vlet` (`Erases.lean`, `ErasesAbstract.lean`, `ErasesStrengthen.lean`) | **faithful and complete** — this is exactly Letouzey's Lemma 2 + Lemma 16 and the paper's "global weakening, weakening, substitutivity" (metacoq R13, letouzey R6) | **keep and re-anchor** — the proofs are structural in the rule set, so each survives a rule's removal |
| `erases_tRel`, `tConst` (drops universes), `tApp`, `tLambda`, `tLetIn` | `Erases.bvar/.fvar/.const/.app/.lam/.letE` | faithful; `const` correctly drops `us`; `lam`/`letE` extend the `VLCtx` exactly as `TrExprS` does | **keep and re-anchor** — remove the `hctor`/`hcases` registry side conditions from `const` |
| `erases_tCase` with the **`Subsingleton`** side condition | *nothing.* `Erases.cases` is a `casesOn`-**application** rule keyed on `Γ.casesOns`/`Γ.casesDiscrPos`/`Γ.ctorFields`; propositional inductives are **excluded** by a `nonProp` conjunct (`EnvErasureNonrec.lean:87,:99,:137,:202) | **missing**, and the exclusion is a fragment restriction where the paper has a modelled rule | **rewrite**: L1 gets `.casesOn` as a plain `.const` head (R-cong); the subsingleton criterion becomes a *derived* environment lemma (Letouzey R4: (◄₄) discharged, not assumed), and `casesOn`→`.case` becomes an L4 pass |
| `erases_tConstruct` | `Erases.ctor` (block form, spine source) + `Erases.ctor_head` (applied form) | **over-specialised**: two rules for one target, both registry-keyed, both exact only when the argmask is all-`keep` (their own docstrings say so) | **delete from L1**; constructor blocking is L4 (MetaRocq already has a verified pass, and peregrine runs it) |
| `erases_tFix` | `Erases.fix` (13 premises, environment-level mutual block) + `Erases.const_fix` (a constant relates to its own block) | **not a congruence at all**: it manufactures a target node Lean's syntax does not have, and `const_fix` makes the relation deliberately nondeterministic at every recursive constant | **delete from L1**; recursion becomes an L4 pass over the emitted environment (`.const kn` + `delta` is the L1-correct erasure, which the relation already has) |
| `erases_tProj` | `Erases.proj`, `Erases.lean:482`, keyed on `Γ.projs`/`Γ.ctorFields` | **faithful in shape**, over-specialised in indexing; the field index is exact only at an all-`keep` argmask | **keep and re-anchor**: drop the registry premises, key on the source `Expr.proj S i e` and the *environment*, keep the `TrProj`-free formulation (it deliberately avoids `TrProj.uniq`) |
| (no counterpart) `Expr.mdata` | *nothing* — `Erases` has no rule, `Supported` excludes it | **missing** (metacoq §4.6 asks for a transparent congruence) | **add** in the rewrite |
| (no counterpart) `Expr.lit` | `Erases.lit`, `Erases.lean:443` — unfolds one constructor step via `l.toConstructor`, mirroring `TrExprS.lit` | **faithful given the design**, but it only exists to let the peano tower be *built by* `ctor_head`+`app`, i.e. it is L4 machinery in L1 | **re-anchor**: keep the "a literal is its kernel unfolding" idea as the L1 rule (it mirrors `TrExprS.lit` and needs no target machinery); machine-`Nat` lowering stays an L4 pass with a data-refinement statement |
| (no counterpart) `Erases.fixvar` | `Erases.lean:612` — `.const nm` ↦ `.fvar x` while inside a block | **implementation artefact** (models `visitConst`'s block branch) | **delete from L1**; it belongs to the L2 bridge's binder bookkeeping |
| the index of the relation: `Σ`/`Γ` | `ErasureCtx`, `ErasureContext.lean:20` — **twelve columns** (`inductives constants ctors ctorArities casesOns ctorFields casesDiscrPos natPeano fixvars recBodies projs …`), **with no well-formedness predicate** relating it to the Lean `Environment` | **the structural deviation**: "e erases to t" is not a run-independent statement (review P8, §4 critical) | **delete**; L1 must be indexed by the Lean environment (via lean4lean's `VEnv`, which `Erases` already carries as `env`) and a `VLCtx`, nothing else |

**Rule-by-rule verdict against Fig. 18** (metacoq R11 / zulip: the table the
review says would settle it in a day, and that the rework must ship):

| Fig. 18 rule | L1 rule in the rework | today |
|---|---|---|
| `erases_box` | `box` | ✅ `Erases.box` |
| `erases_tRel` | `bvar` (+ `fvar`, locally-nameless) | ✅ |
| `erases_tLambda` | `lam` | ✅ |
| `erases_tLetIn` | `letE` | ✅ |
| `erases_tApp` | `app` | ✅ |
| `erases_tConst` | `const` | ✅ (drop the two registry premises) |
| `erases_tProj` | `proj` | ⚠️ re-anchor |
| `erases_tCase` + `Subsingleton` | — (no `Expr` node; `casesOn` is a `const`) | ❌ delete `cases`; L4 pass |
| `erases_tConstruct` | — (no `Expr` node) | ❌ delete `ctor`, `ctor_head`; L4 pass |
| `erases_tFix`/`tCoFix` | — (no `Expr` node; no coinduction) | ❌ delete `fix`, `const_fix`; L4 pass |
| — | `mdata` (transparent) | ➕ add |
| — | `lit` (kernel unfolding) | ✅ keep |

### 1.3 L2 — the erasure function, the oracle, the abstract environment

| Paper object | Current counterpart | Fidelity | Verdict |
|---|---|---|---|
| `E` (Fig. 17) — the executable eraser | `Erasure.visitExpr` & the 18-function `partial_fixpoint` family, `Erasure.lean:588-929` (shipping) | **the right subject** (report R1). Not pruning-only (R-prune): it η-expands to arity, splits `casesOn` spines, filters argmasks, builds literal towers | **keep the subject**; the *statement* about it changes (see below) |
| the Task-A de-partialization that made it inducible | `Basic.lean`'s `toBvar`/`toBvarArgs`/`toBvarAlts`/`toBvarDefs`; `visitCasesEta`/`visitCtorEta`; nine `@[partial_fixpoint_monotone]` lemmas (`Erasure.lean:364-500`) | reviewed as "a line-for-line transcription … the model for a verification-forced shipping edit" | **keep as is** — it is a precondition of *any* rework |
| `erases_erase` (the single bridge lemma) | `visitExpr_refines_erases`, `VisitExprRefines.lean:3645`, via `visitExpr_refines_erases_core` (18 motives, `:1901`) | **the correct shape**, and sorryAx-free — but it carries 7 hypothesis bundles + a syntactic fragment `Supported`, where the paper carries `X ∼ext Σ` and `welltyped` | **keep the machinery, rewrite the statement**: one lemma, hypotheses = well-typedness + the oracle interface |
| `is_erasableb` (the oracle) | `Erasure.isErasable` (shipping, kernel-routed with a `Meta` fallback) modelled by `LeanToLambdaBox.isErasable`, `Relevance.lean:48` | faithful to `Meta.isProp ∨ isTypeFormerType` | **keep** |
| soundness of the oracle | `isErasableProp.WF` / `isArityCheck.WF` / `isErasable.WF`, `RelevanceCheck.lean`; run-adequacy `kernel_isErasable_sound`, `CheckerAdequacy.lean`; `ResidualHyps.toBridgeHyps`, `OracleDischarge.lean:106` | **faithful, and the one place in the development where trust is *reduced* rather than repackaged** | **keep, and route it into the capstone** — today `OracleDischarge` is not even in the crown module's import closure (review §4 minor) |
| completeness of the oracle (the paper's hard negative half, needing `CumulProp`) | *nothing, and nothing needed* | correct: Lean has no `Prop ≤ Type`, so §7.2's sort-quality apparatus is unnecessary (metacoq §4.2); and `erases_erase` needs only soundness | **do not build it** |
| `abs_env_struct`/`abs_env_prop` (squashed connection, `abs_env_irr`, lookup as the only query) | *no analogue.* The four `*BridgeHyps` bundles + `DeltaHyps`/`BlockHyps`/`RecBlockAgreement` are Hoare specs of individual `EraseM` primitives, split "for change management" (review P4) | **the right idea, four times over, at the wrong granularity** | **rewrite as one interface** with named obligations (metacoq R4): oracle soundness, fresh-name discipline, `getCasesInfo?`/`getCtorArity?`/`getDeclInfo?` lookup adequacy, `Environment` connection + uniqueness |
| `retyping` (§6.4) | lean4lean's `inferType` inside `Relevance.isErasable` | faithful in role | **keep** (upstream's) |
| `prepare_erasure` (report §4.1: `_unsafe_rec`, `macro_inline`, matcher inlining, `csimp`) | `Erasure.prepare_erasure`, `Erasure.lean:548-576`; specified by `PrepareHyps`, `PrepareHyps.lean:74` | **stated at a relation no capstone uses** (review GA-06), so the `e → pe` link is open | **rewrite**: state it per-transformation, with `csimp := false` in the core theorem (report R5/R6) |
| the pure de Bruijn model `eraseCore` | `EraseCore.lean:91`, with `eraseCore_refines`/`eraseCore_correct` | **refuted as a bridge** (its own 2026-07-07 addendum: no context-free oracle can reproduce the shipping one); it survives only as a first-order fixture | **delete** except the fuel/monotonicity lemmas `FirstOrder.lean` reuses |

### 1.4 L3 — forward simulation, subject reduction, environment erasure

| Paper object | Current counterpart | Fidelity | Verdict |
|---|---|---|---|
| `Σ ⊢ t ⇓ v` (one source evaluation) | **eight**: `SEval`, `SEvalβ`, `SEvalβδ`, `SEvalβζδ`, `SEvalβζδι`, `SEvalData`, `SEvalDataC`, `SEvalDataι` (`SourceEval.lean:30/70/114/144`, `SubjectReduction.lean:35`, `SourceEvalData.lean:38/180`, `ErasesCorrectData.lean:960`) | **violates metacoq R2 / letouzey R8**; two dead, one documented incorrect, two incomparable, and neither capstone flavour can evaluate a `let` (review GA-05) | **rewrite to one**, with fragments as *hypotheses on the derivation* or definitional restrictions with an inclusion lemma |
| subject reduction (§5.4) — used to keep `isErasable` premises alive | `SEvalβζδ_defeq` (`SubjectReductionFull.lean`), `SEvalDataι_defeq` (`SubjectReductionIota.lean`), `SubjectReduction.lean` | **faithful in role and genuinely proved**; the β arm is written out three times, two copies byte-identical (review R4) | **keep and unify** |
| `erases_correct` | `erases_correct`, `ErasesCorrect.lean:525`; `erases_correct_data` (`ErasesCorrectData.lean`); `erases_correct_dataι` (`ErasesCorrectIota.lean:290`) | **the right shape** (∃ value-erasure + target evaluation), but with `SEnvConsistent`, `ErasesEnvDelta`, `RecEnvConsistent`, `hnfv` where the paper has `wf Σ`, `welltyped`, `⇓`, `⇝E`, `erases_deps` | **rewrite the statement, keep the proof skeleton** — the case analysis (box arm via subject reduction, β via `erases_subst`, δ via the env relation) is the paper's and is right |
| Letouzey Thm 12 (target step ⇒ **≥1** source steps) | *nothing* | **missing** | **build** if the terminal theorem is to be observational (letouzey R7/R11); optional if the capstone stays conditional on `⇓` |
| Letouzey Thm 13 (source step ⇒ target step or □-steps) | this *is* `erases_correct`'s content, in big-step form | faithful | keep |
| `Σ ⇝E Σ'` (pointwise env erasure, listed but unused) | `ErasesEnvDelta`, `ErasesCorrect.lean:449` | matches the *unused* definition | **delete** in favour of the next row |
| **`erases_deps`** (the dependency-selective relation the paper actually uses) | `RegisteredClosure`/`RegisteredClosureData` (`EnvErasureNonrec.lean:531/:551`), `RegisteredClosureRec` (`EnvErasureRec.lean:112`), plus `RegisteredCtors/Cases/CtorFieldsAll/Projs/ProjCtorFields` | **the right idea, unnamed and split five ways**; it is genuinely *discharged from registration records* rather than assumed, which is better than the paper's own presentation | **keep the content, rewrite as one `erases_deps`** (metacoq R6, letouzey R13) |
| `abs_pop_decls` | none, and none needed | correct | — |
| `axiom_free Σ` | *nothing*; `Supported`'s `known` names the δ fragment instead | **missing**, and the naive form is unusable in Lean (`propext`/`Quot.sound`/`Classical.choice`) | **build the generalisation** (metacoq §4.4): every axiom in the erased closure is Prop-typed (hence boxed) or explicitly remapped by an L4 pass. This is the single change that moves benchmark coverage off 0/5 |
| `Supported` (fragment predicate) | `Bridge.lean:100`, with real closure lemmas (`:219`, `:268`) | **no paper counterpart**, but a legitimate device *if* it is decidable on real input and inhabited (report R16). Today it is a `Prop` over `(known, Γ)` and its `casesApp` docstring is false about sparse `casesOn` (review P3) | **keep the technique, rewrite the predicate**: syntactic, decidable, checked on the five VerifyBench programs |

### 1.5 L4 — the passes (where four current `Erases` rules must go)

| Pass | Paper model | Current status | Verdict |
|---|---|---|---|
| `optimize` (Prop-case expansion) | §7.4, `optimize_correct`, flag-discharging | `LBOptimize` + `LBOptimize_env` (`Optimize.lean:49/:81`); `LBOptimize_correct` (`:927`) `EvalProp Γ t v → Eval (LBOptimize_env Γ) (LBOptimize Γ t) (LBOptimize Γ v)`; non-vacuity guard at `:1066`. Also does `projCollapse` (MetaCoq's `remove_match_on_box` for `tProj`). **Not imported by any capstone; not in the crown module's import closure** | **keep as is, wire it in** — 1,090 lines of the exactly-right shape, currently dead |
| constructor blocking (applied → block) | Letouzey §4 / MetaRocq's verified pass; Zulip T1 says peregrine *runs* it and requires applied input | absorbed into `Erases.ctor` vs `ctor_head`, plus a `NoBlock` predicate threaded through the capstones | **delete from L1**; state the frontend theorem in applied form (zulip Z2) and cite peregrine's pass |
| `casesOn` application → `.case` | no paper counterpart (this is compilation) | `Erases.cases` (`Erases.lean:562`) + `CasesBridgeHyps` + `IotaPattern`/`IotaDischarge` + `SEvalDataι` + `IotaRelevant` | **rewrite as an L4 pass** with an `optimize_correct`-shaped statement |
| mutual block → `.fix` | no paper counterpart | `Erases.fix`/`.const_fix` + `RecBlockErasure.lean` + `FixMetatheory.closeFix` + `FixUnfold` | **rewrite as an L4 pass** over the emitted environment |
| `Nat` literal lowering (peano ↔ machine) | none (paper excludes primitive ints) | `Erases.lit` + `Γ.natPeano` + `Supported.natLit`; machine mode explicitly out of scope | **L4 pass** with a data-refinement relation (report R8), or a stated exclusion |
| argmask constructor pruning | Letouzey §4 "removing dummy arguments" (explicitly unproved) | not modelled; `Erases.ctor`/`.proj`/`.cases` are exact only at an all-`keep` mask (their own docstrings) | **state as an exclusion** (`remove_irrel_constr_args = false`) or build the masked-erasure invariant (report R12) |
| `csimp`, `@[extern]`, `macro_inline`, matcher inlining | none (Letouzey §4's honest "700 unproved lines") | `PrepareHyps`; `csimp = false` is a premise of every capstone | **keep the exclusion, itemise it** (letouzey R14) |
| unboxing | delegated to peregrine | out of scope | — |

### 1.6 L5 — first-order collapse and the capstone

| Paper object | Current counterpart | Fidelity | Verdict |
|---|---|---|---|
| `firstorder_ind Σ i` (syntactic, on the *inductive*) | `FirstOrderValue` (`FirstOrder.lean:75`) + `InformativeType` (`:50`) — a predicate on the **value**, carrying a typing side condition per node | **deviates**: the paper's is a decidable property of the inductive declaration; this one cannot be checked on a benchmark, and its `Γ.ctors` premise ties it to a registry | **rewrite** as `firstorder_ind` over the Lean environment; keep `InformativeType`'s *proof* as the bridge lemma |
| `firstorder_erases_deterministic` | `firstOrderValue_not_erasable` (`FirstOrder.lean:131`) + `firstOrderValue_erases_eq_eraseCore` (`:385`); the capstones' uniqueness conjunct `∀ tu, Erases … → NoBlock tu → tu = t'` | **faithful in content** — "on first-order values neither box nor any nondeterministic choice fires", proved via `TrExprS.uniq`/`IsDefEq.uniqU`, exactly the paper's argument | **keep and re-anchor** |
| `Σ ⊢ v ⇓ v` (v is a value) | `sevalβδ_value_is_lam` and the value shape lemmas | partial | **re-anchor onto `Value`** |
| `erase_correct_firstorder` | `erase_correct_firstorder` (`FirstOrder.lean:473`); shipping flavours `shipping_erase_correct_firstorder` (`FirstOrderShipping.lean:55`), `…ι` (`FirstOrderShippingIota.lean:130`), `…_coldstart` (`ColdStart.lean:827`), `…ι_coldstart` (`ColdStart.lean:664`) | **the composition is right and the cold-start subject (`Erasure.erase`, the function `#erase` calls) is right**; the hypothesis list (~24 `Prop`s, 7 never-inhabited bundles) is not | **keep the composition, rewrite the premises** |
| `wcbv_standardization` / `progress` / normalization axiom | *nothing* (lean4lean has none) | missing by necessity | **mirror the paper's conditional form** (metacoq §4.5 option 1): take source evaluation as a hypothesis, plus a decidable benchmark side-check |
| Letouzey Def. 6 (logic-free) / Def. 14 (data-type) / Thm 15 (no residual `□`, syntactic equality) | *nothing* | missing | **build** — Def. 14 ≈ `firstorder_ind`; the "no `□` survives" conclusion is cheap once uniqueness is there and is what makes the theorem *observational* |

### 1.7 The trusted base

| Paper object | Current counterpart | Fidelity | Verdict |
|---|---|---|---|
| the single `normalization` axiom; §1's "trusted theory base" | **four** trust bundles (`BridgeHyps`, `DataBridgeHyps`, `CasesBridgeHyps`, `ProjBridgeHyps`) + `DeltaHyps`/`BlockHyps`/`RecBlockAgreement`/`RegBridgeHyps` + commissioned premises (`ErasableStrengthen`, `ProjDefeqSpec`, `PatsIotaSpec`) + inherited lean4lean `sorryAx` | **the honesty is real** (`#print axioms` on all four capstones prints one identical eight-axiom set; the commissioned premises are named hypotheses, never axioms) — the *organisation* is not | **rewrite into one documented bundle** (metacoq R10): (a) lean4lean's unique-typing cluster (`TrExprS.uniq`, `IsDefEq.uniqU`) — the right place, since the paper needs a metatheorem there too; (b) the oracle/runtime interface obligations; (c) the source-evaluation hypothesis. One line of justification each |
| `#print axioms` discipline | `scratch/final_audit.lean` (4,546 lines, git-tracked, third copy of the ledger) | the *measurement* is right, the *triplication* is not | **keep the audit as CI, delete the prose ledgers** |

### 1.8 The deliverable (not a paper object; a Zulip/report obligation)

| Object | Current counterpart | Fidelity | Verdict |
|---|---|---|---|
| the `.ast` S-expression file (peregrine's `PAst`, byte-level) | `Printing.lean:15` `Serialize` — **zero verification coverage** (review GA-01) | missing | **build a minimal statement or one honest ledger row** (zulip Z1) |
| `prog.ast.inlinings` (must exist, even empty) | emitted by `eraseElab` (`Erasure.lean:1005-1010`), unmodelled | missing | zulip Z5: prove the cheap true statement or scope out loudly |
| `#erase` (the command, 8 steps around the verified `erase`) | `eraseElab`, `Erasure.lean:984-1012`; `cfg` comes from an `unsafe evalTerm` at `:993` | the capstone's `hcsimp : cfg.csimp = false` constrains an object produced outside the proofs | **state the boundary** (report R14) |
| well-formedness of the emitted environment (`peregrine validate`) | `RegInvShape` (`ColdStartShape.lean:314`), `NoBlock`, `LBClosed` | partial and scattered | **rewrite as one output predicate** (zulip Z3) |
| panics | 16 `panic!`/`unreachable!` sites; `run_panicWithPosWithDecl` makes a panic *succeed* at `EraseM`; `visitExpr_shape_all` discharges its panic arms | **honestly modelled, and the honesty is load-bearing**: `.ok` does **not** exclude a panicked run (review §4 major) | **keep the modelling, state it in the capstone** (report R13, zulip Z8) |
| coverage on real programs | `VerifyBench/` (5 programs, `csimp := false`, `STATUS.md` records 0/5 covered and the Quicksort sparse-`casesOn` bug as RAISED-not-fixed) | **exactly the right artefact and the right discipline** | **keep as is; make it the acceptance test** |

---

## 2. Reusable proven assets

Ranked by value-per-line. Sizes are file line counts at HEAD; where an asset is
part of a file the figure is noted as such.

| # | Asset | File(s) | Lines | Why it survives the rework |
|---|---|---|---|---|
| A1 | λ□ semantics: flags, values, `WcbvEval`, env queries, substitution kit, metatheory | `LeanToLambdaBox/Semantics/*.lean` | **1,225** | The rework's L0 *verbatim*. Rule-for-rule MetaCoq correspondence, `eval_deterministic`/`eval_value`/`eval_unique` with non-vacuity guards, sorryAx-free, flag-parametric so an L4 pass can discharge a rule. Nothing in the papers asks for more. |
| A2 | de Bruijn / closedness kit: `LBClosed`, `shift`/`subst` commutation, `subst_subst` | `Closed.lean` | **871** (46 thms) | Target-side, lean4lean-free, rule-set-independent. Consumed by every simulation and by `IotaBridge`. |
| A3 | `toBvar` (fvar→bvar) metatheory | `Abstract.lean` (+ `Basic.lean`'s de-partialized `toBvar*`) | **423** (35 thms) + 236 | The reason the bridge can treat "open with a fresh fvar, recurse, abstract" as a binder rule. No paper needs it (they are pure de Bruijn); the Lean eraser cannot be verified without it. |
| A4 | `closeFix` / `substFix`: static fix-closing inverts dynamic fix-unfolding | `FixMetatheory.lean` + `FixUnfold.lean` | **1,184** (41 thms in FixUnfold) | Pure `LBTerm`. Whatever produces `.fix` — L1 rule today, L4 pass tomorrow — needs exactly this identity (`closeFix_substList_fixSubst`). |
| A5 | ι reversal: a β-chain of field applications *is* MetaRocq's `iota_red` | `IotaBridge.lean` | **207** | Target-side, sorryAx-free, mentions neither `Erases` nor lean4lean. It is precisely the lemma an L4 `casesOn`→`.case` pass must prove. Reusable unchanged. |
| A6 | `Erasable` + its stability kit (`IsArity`, `IsArityUpTo`, `.inst/.weakN/.defeq`) | `Erasability.lean` | **230** | Letouzey's Lemma 2 and Sozeau's `isErasable`, in one file, faithful, both disjuncts separated as the papers require. Untouched by the L1 rewrite. |
| A7 | verified relevance oracle: executable check, soundness, run-adequacy, discharge | `Relevance.lean` + `RelevanceCheck.lean` + `CheckerAdequacy.lean` + `OracleDischarge.lean` | **495** | The development's **only** trust *reduction* (`isErasable.WF` → `M.WF.run'` → `kernel_isErasable_sound` → `ResidualHyps.toBridgeHyps`). It is the Lean analogue of `is_erasableb`'s soundness half — the only half `erases_erase` needs. Currently outside the crown import closure; the rework must route it in. |
| A8 | run algebra for `EraseM` | `ErasureRun.lean` | **3,234** (147 thms, 75 run lemmas) | The `.ok (r,s') w'` calculus every bridge motive is written in. Independent of which relation the bridge concludes; survives an L1 rewrite entirely. |
| A9 | the 18-motive fixpoint induction over the real `visitExpr` | `VisitExprRefines.lean` (`visitExpr_refines_erases_core` `:1901`, exported `:3645`) | **4,641** | The single hardest thing in the tree and the thing no paper had to do. **The skeleton is reusable; the per-motive conclusions are not** — each motive's `Erases …` conjunct must be restated. Realistic reuse: the induction scaffolding, admissibility, the `⊑` conjunct, the binder/telescope lemmas, the run plumbing (~55-65%); the rule-specific arms for `ctor`/`cases`/`fix`/`fixvar` (~35-45%) go with the rules they conclude. |
| A10 | `Erases` transport metatheory: `erases_shift`, `erases_subst`, `Erases.abstract`, `Erases.uninstantiate`, `Erases.thin_vlet`, context uniformity | `Erases.lean` (transport half) + `ErasesAbstract.lean` (298) + `ErasesStrengthen.lean` (747) + `ErasesUniform.lean` (820) | **~2,300** | Letouzey Lemma 16 / the paper's weakening + substitutivity — the reusable core the β and δ cases consume (metacoq R13, letouzey R6). Proofs are per-rule inductions: the arms for surviving rules transfer verbatim; deleted rules take their arms with them. |
| A11 | `optimize` and its correctness | `Optimize.lean` | **1,090** | `LBOptimize_correct : EvalProp Γ t v → Eval (LBOptimize_env Γ) (LBOptimize Γ t) (LBOptimize Γ v)` is `optimize_correct` in the paper's exact flag-discharging shape, with a non-vacuity guard, sorryAx-free. Dead today (not in the import closure); it is the **template** for every L4 pass. |
| A12 | first-order non-erasability | `FirstOrder.lean:103-155` (`informativeType_not_erasable`, `firstOrderValue_not_erasable`) | **~55** of 762 | The content of `firstorder_erases_deterministic`, proved by the paper's own argument (type uniqueness). Re-anchor onto a `firstorder_ind`-based predicate. |
| A13 | subject reduction as defeq | `SubjectReduction.lean` (477) + `SubjectReductionFull.lean` (479) + `SubjectReductionIota.lean` (458) | **1,414**, ~1,050 after de-duplication (the β arm is written three times, two byte-identical) | §5.4's role: keeps `Erasable` premises alive across a source step, which is what the box arm of `erases_correct` consumes. |
| A14 | environment erasure discharged from registration | `EnvErasureNonrec.lean` (639) + `EnvErasureRec.lean` (818) + `EnvErasure.lean` (183) | **1,640** | The content of `erases_deps`, and better than the paper's presentation in one respect: it is *derived from what the run registers*, not assumed. Needs one name and one shape. |
| A15 | cold-start: the subject is `Erasure.erase`, and `E`, `t`, the registration records, `ClosedEnv`, `LBClosed`, `NoBlock` are **produced by the run** | `ColdStartShape` (1,055) + `ColdStartInduction` (1,503) + `ColdStartRun` (672) + `ColdStartDelta` (1,185) + `ColdStart` (2,000) | **6,415** | Reviewed as "genuine, principled work". The technique — derive the output environment from the run rather than assume it — is what makes any statement about `#erase` (as opposed to about a model) possible. Much of the bulk is premise plumbing that the rework deletes; the *shape induction* (`visitExpr_shape_all`, unconditional, panic-tolerant) and the run decomposition (`erase_run_ok`) are the durable parts. |
| A16 | the coverage artefact | `VerifyBench/` (5 programs + `STATUS.md`) | **520** | The five real programs at `csimp := false`, byte-diffable against the frozen originals, with an honest 0/5 record and a raised-not-patched shipping bug. This is the acceptance test the rework's non-vacuity requirement (metacoq R8, letouzey R12, report R15, zulip Z6) is measured against. |
| A17 | the shipping-side edits that made induction possible | `Erasure.lean:364-500` (nine monotonicity lemmas), `Basic.lean` de-partialization, `visitCasesEta`/`visitCtorEta` | **~380 diff lines** vs `main` | Precondition of any rework. Note `Erasure.lean:151-187`'s kernel reroute is a *behaviour-changing* edit (review SI-1) and is a separate question. |

**Total reusable, conservatively: ~13,000–15,000 lines** of the 42,632, of which
~6,500 (A1–A7, A11, A12) transfer essentially unchanged and ~7,000 (A8–A10,
A13–A15) transfer as skeletons that need restating.

---

## 3. What the papers force to change, ranked

1. **`Erases` is rewritten as a congruence over `Expr` + one box rule.** Six of
   the fifteen rules (`ctor`, `ctor_head`, `cases`, `fix`, `const_fix`,
   `fixvar`) leave L1; `mdata` arrives; `proj`, `const`, `lit` lose their
   registry premises. The relation is indexed by `env : VEnv` and a `VLCtx`
   only — `ErasureCtx`'s twelve columns disappear from the specification.
   (metacoq R3/R11, letouzey R3, report R3, review P8 + §4 critical.)
2. **Four L4 passes are created** — constructor blocking (or a citation of
   peregrine's verified pass), `casesOn`→`.case`, mutual block→`.fix`, literal
   lowering — each with an `optimize_correct`-shaped statement, and
   `Optimize.lean` is wired in as the template and as the discharger of
   `with_prop_case`. (metacoq R9, letouzey R1, report R9.)
3. **The subsingleton-elimination criterion becomes a derived environment
   lemma** rather than a `nonProp` exclusion. This is Letouzey's (◄₄) and
   Sozeau's `Subsingleton`, and in Lean it is *derivable* from the kernel's
   large-elimination rule over a well-formed environment. It is also what
   unblocks `Acc.rec`/`WellFounded.fix`/`Decidable`/`And`/`Iff` — pervasive in
   real Lean code and currently excluded. (letouzey R4, metacoq §4.6.)
4. **One source-evaluation relation** replaces eight; fragments become
   hypotheses or restrictions with inclusion lemmas; `let` must be evaluable.
   (metacoq R2, letouzey R8, review P7/GA-05.)
5. **One environment relation named `erases_deps`**, replacing `ErasesEnvDelta`
   + five `Registered*` predicates + three `RegisteredClosure*` structures.
   (metacoq R6, letouzey R13.)
6. **One trust interface** in the `abs_env_struct` style replaces four
   `*BridgeHyps` bundles + `DeltaHyps`/`BlockHyps`/`RecBlockAgreement`/
   `RegBridgeHyps`, and the verified oracle discharge is routed into the
   capstone instead of sitting outside its import closure. (metacoq R4/R10,
   review P4/GA-07/§4 minor.)
7. **`firstorder_ind` replaces `FirstOrderValue`+`InformativeType`** as the
   observational domain, defined syntactically on the inductive so that it is
   *checkable* on `Nat`, `Bool`, `List Nat`, `Nat × Nat` — i.e. on the
   VerifyBench observables. (metacoq R7.)
8. **An `erasable_axioms`-style hypothesis replaces `axiom_free`** (Prop-typed
   axioms box; relevant ones are remapped by a named L4 pass; `Classical.choice`
   excluded by dependency tracking). This is the change that moves benchmark
   coverage off 0/5. (metacoq §4.4/R8.)
9. **The capstone's premises must be jointly inhabited on at least one real
   program**, with a checked instantiation per VerifyBench program and an honest
   per-program coverage table. `IotaRelevant`/`IotaShape` — constructed nowhere,
   at any Γ — are deleted rather than re-proved. (metacoq R8, letouzey R12,
   report R15, zulip Z6; review P1/P2/TA-06/GA-03.)
10. **The output boundary is stated**: applied-constructor form as the *primary*
    target (not a "representation gap"), one well-formedness predicate matching
    `peregrine validate`, the `.ast` serializer either covered or one honest
    ledger row, and `.ok`-does-not-exclude-panic said in the capstone.
    (zulip Z1/Z2/Z3/Z8, report R13/R14.)
11. **Documentation policy**: docstrings state what an object is; history goes in
    git. Deletes ~3,000–3,500 comment lines and every false claim the review
    found (`Flags.lean:19-24`, the seven `no addPat clause` sites, the eight
    `addInduct_WF is sorry` sites, the five stale oracle descriptions,
    `Supported.casesApp`'s sparse-`casesOn` sentence). (metacoq R12.)
12. **Land it where consumers pin.** `main` is 207 commits and eleven Lean
    releases behind, CI builds `main` only, and `main`'s eraser is a *different*
    function. (zulip Z10, review §4 major.)

---

## 4. Impact on effort — an honest reading

**What is genuinely lost.** The rules `ctor`/`ctor_head`/`cases`/`fix`/
`const_fix`/`fixvar` and everything keyed on them: their arms in `erases_shift`/
`erases_subst`/`Erases.abstract`/`Erases.uninstantiate`/`thin_vlet`/uniformity;
their arms in the 18 motives; `SEvalData*`/`SEvalDataC`/`SEvalDataι` and their
simulations (`ErasesCorrectData` 1,731, `ErasesCorrectIota` 1,075); the ι
discharge chain (`IotaPattern` 485, `IotaDischarge` 604, `SubjectReductionIota`
458, `CasesBridgeHyps` 287); the proj discharge chain (`ProjPattern` 1,059,
`ProjDischarge` 415, `ProjBridgeHyps` 182) as *chains* — though `Erases.proj`
itself survives; `RecBlockErasure` 811 and the recursion premise layer;
`DeltaHyps` 1,499 and `RegBridgeHyps`; the Γ-level campaign (`ErasesLevels` 373,
`ErasesInstL` 493, `ErasesDeltaL` 280) insofar as it services deleted rules.
Call it **~12,000–14,000 lines that do not survive as proofs**, of which the
review already classifies ~4,500 as deletable today with no proved statement
lost.

**What is re-anchored rather than rewritten.** ~7,000 lines (A8–A10, A13–A15):
the statements change, the proof skeletons and the lemma inventories do not. The
per-motive conclusions in `VisitExprRefines.lean` are the largest single item —
restating 18 motives is mechanical but not free, and the file is 4,641 lines.

**What is untouched.** ~6,500 lines (A1–A7, A11, A12, A16, A17), plus the
shipping code, which the rework must not edit.

**Net.** The rework is not a from-scratch rebuild: **roughly a third of the tree
carries over unchanged, a sixth is re-anchored, and a third is deleted** (the
remainder being comment). The expensive part is not re-proving metatheory — it is
that four things currently proved *once*, inside `Erases`, must be proved *four
times*, once per L4 pass, in the `optimize_correct` shape. That is more theorems
but each is smaller, target-side (hence lean4lean-free and sorryAx-free), and
independently checkable — and three of the four already have their hardest lemma
in hand (`IotaBridge` for ι, `FixUnfold`+`FixMetatheory` for `fix`,
`Optimize.lean` as the worked template).

**Risk.** The one place the effort could exceed the estimate is the
subsingleton-elimination lemma (item 3): deriving Lean's large-elimination
criterion inside lean4lean's `VEnv` model is genuinely new metatheory, and the
review's evidence (`Ordered.pat`, `addInduct_WF` proved at rev 20ec229) says the
upstream ingredients now exist but have never been assembled here. Budget it as
the rework's single research risk; everything else is engineering.

**The cheapest thing that most improves the claim**, and it should be done first
because it is the referee for every later decision: the rule-by-rule
correspondence table of §1.2 against Fig. 18, tracked next to the relation, with
every deviation named. The review calls it "worth more than any further slice",
and this document contains its first draft.
