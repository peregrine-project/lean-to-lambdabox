# Issues found while writing the blueprint

Observed in the `lean-to-lambdabox` repository at `dev/verify` HEAD `e7894de`, while writing the
`leanblueprint` documentation of its formalisation. Reported here, not fixed; ids are stable. `confirmed`
means a second pass re-checked the entry against the cited sources (occasionally correcting a description
or citation, folded in below); `confirmed (measured)` means that pass re-ran the measurement; `unclear`
means it could not settle the entry; `unverified` means no second pass ran — the default for every
**note**-severity entry, deliberately not re-verified, and for entries the sample did not reach. Items
already in the repository's own register, `doc/rework/03-DEV-FIX.md` (F-* findings), are listed last under
heading (F), only where this pass found detail beyond what that register says.

> **Time scope.** Every entry describes `dev/verify` at `e7894de`. Since then, round 7 fixed the ten
> code-bearing F-* findings on branch `dev/fix` (`dd2e2ee`..`76055ea`, merged into `dev/verify` at
> `2036c85`) and refuted the `ErasesEnv.defns` clause (restated at `92105c6`); several entries under
> (A), (B) and (F) are therefore resolved on `dev/verify`. The blueprint's chapter 12 carries the
> per-finding status with commit hashes; this file is not re-verified against later commits.

## Counts

| Heading | Major | Minor | Note | Total |
|---|---|---|---|---|
| (A) Shipping-code defects | 3 | 6 | 11 | 20 |
| (B) Verification-side issues | 7 | 37 | 76 | 120 |
| (C) Documentation drift | 5 | 18 | 21 | 44 |
| (D) Tooling / CI / infrastructure | 0 | 2 | 4 | 6 |
| (E) Trust-boundary observations (already in `doc/trust.md`) | 0 | 0 | 6 | 6 |
| (F) Restatements of registered F-* findings | 1 | 0 | 1 | 2 |
| **Total** | **16** | **63** | **119** | **198** |

Verification totals across the 198 entries above: **75** confirmed, **2** confirmed (measured), **0**
unclear, **121** unverified (mostly notes, by design not re-verified). One entry from the original ledger
(B28) was **refuted** and is removed from these counts; see "Refuted on verification" at the end.

## Executive summary — ten most consequential confirmed entries

1. **B3** — `RegInvShape'` (the invariant `hbridge` needs) is produced nowhere for a shipping run; `hbridge`
   is a bare, undischarged assumption at every rung.
2. **B97** — T8's registration motive (`Motive6`) concludes nothing about the emitted environment, so the
   `ErasesEnv`/`LowerEnv` facts the capstone needs remain assumed `ErasureBridge` fields (ties into B3).
3. **B73** — `WcbvEval`'s `iota`/`proj` family drops two of MetaRocq's `EWcbvEval` side conditions, so the
   target semantics is strictly more permissive than MetaRocq's despite the header's "rule-for-rule" claim.
4. **B59/B60** — `firstOrderIndB`'s soundness is unproved; the only proved `FirstOrderInd` model is vacuous.
5. **A3** — `register_inductive` never sets `kelim` or `finite`, an unregistered extension of F-PROP.
6. **A4** — sixteen `panic!`/`unreachable!` sites in `Erasure.lean` all succeed silently under `CoreM`'s default.
7. **A10** — the default `ErasureConfig` differs from `ConfigPinned` on three of five fields, so a bare
   `#erase` with no explicit config runs a configuration no theorem in the repository covers.
8. **C9/C18** — `01-DESIGN.md`'s printed capstone is obsolete on every axis that matters, and `02-PLAN.md`'s
   wave table still records the landed wave W6 as "not started."
9. **B1** — the capstone's `hnb : NoBodylessRefs` binder is unused in its own proof, yet trust docs present it
   as the exclusion mechanism it is not.
10. **B105** — two panicking proof arms' correctness rests on `LBTerm.box` being the accidental constructor.

## (A) Shipping-code defects not already in `doc/rework/03-DEV-FIX.md`
### A3 — register_inductive never sets kelim or finite (major, confirmed)
`register_inductive` never sets `OneInductiveBody.kelim` (stays `.IntoAny`) or `MutualInductiveBody.finite`
(stays `.finite`) on any emitted inductive. `kelim` is precisely the field MetaRocq uses to record elimination
restrictions on `Prop` inductives — an unregistered extension of F-PROP.
**Where:** Erasure.lean:240-241; Basic.lean:165,177.
### A4 — Sixteen panic!/unreachable! sites all succeed silently (major, confirmed)
`Erasure.lean` has sixteen `panic!`/`unreachable!` sites. Because `CoreM` is an exception+state monad and
`LBTerm`'s derived `Inhabited` default is `.box`, a panic always *succeeds*: `addAxiom`'s duplicate-declaration
guard still conses a second `gdecls` entry, `register_inductive`'s unreachable arms fall through
non-preservingly, and binder helpers can silently emit `default : LBTerm` — every run exits 0 (broader than, but
the same mechanism as, F-SPARSE).
**Where:** Erasure.lean:185,200,206,982-1008; ErasureRun.lean:248,253,1719,1788.
### A10 — Default ErasureConfig diverges from ConfigPinned on three fields (major, confirmed)
The default `ErasureConfig` (`extern := .preferAxiom, nat := .machine, csimp := true`) differs from
`ConfigPinned` (`.preferLogical, .peano, false`) on three of its five fields, so a bare `#erase foo to
"foo.ast"` with no explicit config runs a configuration no theorem in the repository covers.
**Where:** Erasure.lean:64-68; ErasureSpec.lean:43.
### A1 — eraseElab logs the program twice, never the inlinings string (minor, confirmed)
`eraseElab`'s no-output-path branch of the inlinings write is `logInfo s`, re-logging the whole program instead
of the attributes-config string `c_s` computed two lines above (`:1004`), so `#erase foo` with no `to "..."`
prints the program twice and never shows the inlinings. [Erasure.lean:1008,1004]
### A2 — filter and visitCases silently truncate mismatched-length sequences (minor, confirmed)
`filter` and `visitCases`'s three-way `for` (`:820`) both silently truncate to the shortest of their input
sequences with no diagnostic, so a `CasesAltInfo.default` alternative or a sparse `casesOn` can yield a `.case`
node with fewer branches than the inductive has constructors — a distinct failure mode from F-SPARSE (silent
truncation, not panic). [Erasure.lean:23,820]
### A6 — Dead commented-out mkCase, no-op let, and a still-partial dead def (minor, confirmed)
Three stale artefacts sit in shipping source: a commented-out `mkCase` referencing a nonexistent type `ppname`
(the real type is `BinderName`); a no-op `let _ := Expr` inside `register_inductive` (`:230`); and
`withAppEtaToMinArity` (`:506`), still a `partial def` though its own doc comment says the erasure family no
longer calls it. [Erasure.lean:266-270,230,506]
### A11 — isErasable's "no axiom of ours" doc comment overstates the trust footprint (minor, confirmed)
`isErasable`'s doc comment says "no axiom of ours," but shows `isErasable.WF`'s footprint does include `sorryAx`
and lean4lean's modelling axioms — true only in the narrow sense of "not newly introduced here." The same
comment's call to re-validate extracted output against the benchmarks after a relevance-decision change appears
never to have been carried out. [Erasure.lean:167,175-176; RelevanceCheck.lean:158-172]
### A16 — The byte-level printer is an unverified partial def (minor, confirmed)
`Printing.lean` (`LBTerm.to_sexpr`) is the byte-level printer, a `partial def` with no equational lemmas. Its
companion line is not a second `partial def` as originally logged — it is the `Serialize LBTerm` instance
wrapping the same function — but the substantive point holds: nothing under `LeanToLambdaBox/` outside
`Printing.lean`/`Erasure.lean` mentions `sexpr`/`to_sexpr`, so the verified stack stops one step short of the
`.ast` bytes peregrine actually parses. [Printing.lean:68,91; Erasure.lean]
### A17 — Basic.lean/Printing.lean are root-namespace; Erasure files use bare Erasure (minor, confirmed)
`Basic.lean`/`Printing.lean` declare no namespace at all (root-level declarations);
`Erasure.lean`/`ErasureRun.lean` open bare `namespace Erasure`; only `Relevance.lean` sits under `namespace
LeanToLambdaBox` — a genuine structural inconsistency across the four shipping files. [Basic.lean;
Printing.lean; Erasure.lean; ErasureRun.lean; Relevance.lean]
### A5 — logInfo message missing its s! interpolation prefix (note, unverified)
`register_inductive`'s `@[extern]`-constructor `logInfo` message is missing its `s!` interpolation prefix, so
the braces print literally, unlike every neighbouring `logInfo` in the file. [Erasure.lean:204]
### A7 — ProjectionBody comment contradicts OneInductiveBody.projs and actual behaviour (note, unverified)
`ProjectionBody`'s comment reads "should be unused," but `OneInductiveBody.projs`'s neighbouring comment
(`:167`) says peregrine rejects an empty list, and `register_inductive` does populate it for structures — a
stale, self-contradicting comment. [Basic.lean:149,167]
### A8 — gdecls doc comment wrongly claims it is never read (note, unverified)
`ErasureState.gdecls`'s doc comment, "only updated, not read," is false as written: `Erasure.erase` does read
it; true only during the run. [Erasure.lean:31,929]
### A9 — ErasureConfig term is chosen by an unsafe Elab.Term.evalTerm at command entry (note, unverified)
`eraseElab` evaluates the user's `ErasureConfig` term with `unsafe Elab.Term.evalTerm`, so the configuration
under which the capstone is stated is chosen by an unsafe evaluation at the shipping command's entry point.
[Erasure.lean:993]
### A12 — Binder-order doubts ("may be wrong") left live in shipping doc comments (note, unverified)
Doc comments record unresolved doubt about binder order still present in shipping source — "the other way around
led to segfaults" (`mkAlt`), "Check binding order here as well, may be wrong" (`mkDef`, `:272`) — for exactly
the ordering the abstraction/lowering rules must get right. [Erasure.lean:258,272]
### A13 — A local Nat shadows the natural numbers inside namespace Erasure.Config (note, unverified)
An `inductive Nat` declared inside `namespace Erasure.Config` shadows the natural numbers within that namespace
— contained, since the namespace closes a few lines later, but a citation hazard. [Erasure.lean:49]
### A14 — Serialize (a x b) pair instance declared twice, second silently shadows first (note, unverified)
The `Serialize (a × b)` pair instance is declared twice with identical bodies (and `:55-56`); the second
silently shadows the first — a copy-paste artefact in the byte-level printer. [Printing.lean:49-50,55-56]
### A15 — rocq_escape/rocq_print are dead debug helpers (note, unverified)
`rocq_escape` and `rocq_print` have no caller anywhere in the repository — dead debug helpers.
[Printing.lean:161,165]
### A18 — remapInductive breaks the file's upper-camel naming convention (note, unverified)
`remapInductive` is spelled lower-camel while every sibling type in the file (`RemappedInductive`,
`ExtractInductive`, `InductiveMapping`) is upper-camel — a cosmetic naming inconsistency. [Basic.lean:219]
### A19 — FixDef.principalArgIdx comment says "safe to be 0"; LowerBlock.hrarg makes it load-bearing (note, unverified)
`Basic.lean:67`'s comment on `FixDef.principalArgIdx` says the field is "safe to let this be 0"; but
`LowerBlock.hrarg` (`Lower.lean`) makes `principalArgIdx = 0` load-bearing for the pass's
evaluation-preservation results. The comment is misleading about the field's actual role. [Basic.lean:67;
Lower.lean]
### A20 — ConstructorBody.nargs has no doc comment and invites an arity/nargs mix-up (note, unverified)
`Basic.lean:144-147`'s `ConstructorBody` gives no doc comment to `nargs`, and nothing calls it an "arity"; the
codebase's own convention treats "arity" as strictly larger than `nargs` (`ind_npars + cstr_nargs`) — the thin
comment invites the same mix-up the blueprint itself made. [Basic.lean:144-147]
## (B) Verification-side issues
### B1 — hnb : NoBodylessRefs is bound but unused; trust docs overstate its role (major, confirmed)
`shipping_erase_correct_firstorder`'s binder `hnb : NoBodylessRefs Γ t` is unused in the proof term (`:190-223`)
and absent from the conclusion, yet `doc/trust.md` row N2 and `doc/coverage.md` present `NoBodylessRefs` as the
mechanism excluding `@[extern]`/body-less-reference programs (F-EQREC/Fannkuch) and as MetaRocq's `axiom_free`
analogue — a role the statement itself does not give it.
**Where:** Capstone.lean:164,190-223; doc/trust.md; doc/coverage.md.
### B3 — RegInvShape' is never produced for a real shipping run (major, confirmed)
Nothing in the repository produces `RegInvShape'` for a state a shipping `Erasure.erase`/`visitExpr` run reaches
— the only inhabitants are `RegInvShape'.empty` and one hand-built one-definition fixture. `bridgeEnv_of_regInv`
takes the invariant as an input, not an output, so the nine-theorem `ColdStartShape` preservation kit has no
live proof path to the capstone, and the capstone's `hbridge` binder is a bare assumption, discharged nowhere in
the proof.
**Where:** ColdStartShape.lean:142; SpecEnv.lean:222-227; Capstone.lean:124,166-169.
### B59 — firstOrderIndB's soundness against FirstOrderInd is not proved (major, confirmed)
Soundness of the Boolean checker `firstOrderIndB` against the semantic predicate `FirstOrderInd` is not proved:
only the table-side half, `firstOrderIndB_step`, exists; the model-side half needs an inversion of
`Lean4Lean.TrEnv'` filed as upstream ask 4. The seven `by rfl` decisions deciding it are anonymous, uncitable
`example`s, and none establishes first-orderness in the model itself.
**Where:** FirstOrderInd.lean:36-39,198,248-264.
### B60 — The only proved FirstOrderInd model instance is constructor-free (vacuous) (major, confirmed)
The only proved model inhabitant of `FirstOrderInd` anywhere in the tree is `firstOrderInd_E`, a
constructor-free (empty) inductive `E` (`:615-736`) — so the substantive `ctor` branch of
`firstorder_erases_core`, the entire content of the development's first-order results, is vacuous at the only
instance anyone has exhibited; all eight green rungs merely assume `FirstOrderInd env Nat` as an undischarged
hypothesis.
**Where:** FirstOrderInd.lean:728,615-736.
### B73 — WcbvEval's iota/proj rules drop MetaRocq's arity and saturation side conditions (major, confirmed)
`Semantics/Eval.lean`'s module header claims `WcbvEval` "matches `EWcbvEval.eval` rule-for-rule" at the
non-block flags. It does not: the five rules `iota`/`iota_block`/`iota_sing`/`proj`/`proj_block` drop MetaRocq's
tie between a case/projection node's parameter count and the inductive's declared arity, plus the argument-spine
saturation premise, so `WcbvEval` is strictly more permissive than `EWcbvEval` on ill-formed input and every
conclusion proved against it is correspondingly weaker.
**Where:** Semantics/Eval.lean:50-52,143-197.
### B97 — T8's registration motive concludes nothing about the emitted environment (major, confirmed)
`Motive6`, the motive for the entire registration path `Erasure.visitMutual`, concludes only `(s'.constants.get?
n).isSome ∧ RunConcl s s' ∧ IndRegistryModelled env s' ∧ gw w ≤ gw w'` — nothing about the emitted environment.
T8 therefore establishes nothing about `ErasesEnv`/`LowerEnv`; both remain assumed `ErasureBridge` fields,
inhabited nowhere at any rung. Presenting T8 as "erasure correctness of the shipping eraser" without this
qualification is wrong.
**Where:** VisitExprRefines/Motives.lean:152; Capstone.lean:99-107.
### B105 — Panic-arm correctness rests on LBTerm.box being the accidental first constructor (major, confirmed)
`step_visitExpr`'s `.sort`/`.forallE` arms go through `run_panicWithPosWithDecl`, which returns `default :
LBTerm` on panic. Their correctness rests on `default` being `.box` purely because `box` happens to be
`LBTerm`'s first constructor under a derived `Inhabited` instance — reordering the constructors would silently
change what these arms prove, with no statement text changing.
**Where:** VisitExprRefines/Step/Mechanical.lean; ErasureRun.lean:249-253; Basic.lean:90.
### B2 — hblk : TableBlocks is bound but unused in erasure_bridge_of_run (minor, confirmed)
`erasure_bridge_of_run`'s binder `hblk : TableBlocks lenv env tbl` is unused in its own proof term (none of the
eighteen steps at `:78-88` takes it) and is forwarded, unused a second time, by the capstone (`:157,199`); the
theorem is annotated `set_option linter.unusedVariables false`. [Capstone.lean:71,157]
### B11 — MaskKeeps/CtorSatConcl saturation layer has no consumer and no proved instance (minor, confirmed)
The constructor-saturation layer
`MaskKeeps`/`CtorSatConcl`/`visitConstructor_ctorSat`/`visitApp_ctorSat`/`visitExpr_ctorSat`/`ctorSat_fires` has
no consumer anywhere, and no instance of `MaskKeeps` is ever proved; `doc/rework/01-DESIGN.md`'s claim that it
is "lifted through `RegInvShape'`" describes a lift that does not exist (and cannot, until B3 closes).
[ColdStartInduction.lean:2033-2206; doc/rework/01-DESIGN.md:1831]
### B12 — visitExpr_runConcl_gen is dead, shadowed by the live visitExpr_runConcl (minor, confirmed)
`visitExpr_runConcl_gen` is dead — no caller anywhere — and is superseded by the live `visitExpr_runConcl`,
which proves the same two conjuncts plus an extra `IndRegistryModelled` implication; two confusingly similar
names. [ColdStartInduction.lean:1788; VisitExprRefines/Step/Env.lean:134]
### B13 — Three dead closedBodies lemmas misdescribe their own role vs hwf (minor, confirmed)
`runClosedW_closedBodies`/`visitExpr_closedBodies`/`closedBodies_empty` are dead, and their doc comments
misdescribe their role as "the environment half of `LBWfPeregrine`'s closedness conjunct" — the capstone
actually gets `LBWfPeregrine` from the `hwf` binder via `lbWfPeregrine_of_check`.
[ColdStartInduction.lean:1891,1929,1943]
### B14 — ColdStartRun's "no assumption" docstring is false of its own prepare_sound (minor, confirmed)
`ColdStartRun.lean:19-20`'s module docstring claims "no erasure relation, no lean4lean, no assumption" for the
whole file; `prepare_sound` (`:518-527`) takes the `EraserAsks` bundle, mentions `Lean4Lean.VEnv`/`VLCtx`, and
concludes about `SEval` — contradicting the disclaimer. (The blueprint's own chapter 10 already flags this, at
`10-coldstart.tex:147`.) [ColdStartRun.lean:19-20,518-527; 10-coldstart.tex:147]
### B15 — InlineExt and six decomposition lemmas (~330 lines) have no consumer (minor, confirmed)
`InlineExt` and six decomposition lemmas (~330 of the file's 610 lines) have no consumer anywhere; the live
delta path instead runs through `VisitExprRefines/Step/Env.lean`'s `step5`/`step6`, and
`doc/rework/06-REPAIRS-W4.md` row BD22 records the intended consumer (`visitMutual_lowerBlock_hfl`) as never
landed. [ColdStartRun.lean:51-451; VisitExprRefines/Step/Env.lean; doc/rework/06-REPAIRS-W4.md]
### B27 — ErasesUniform.lean (19 declarations) reached only by the root aggregator (minor, confirmed)
`ErasesUniform.lean` (19 declarations, including the commissioned premise `ErasableStrengthen`) is outside the
import closure of `Green.lean`/`Capstone.lean`, reached only by the root aggregator; `doc/coverage.md` already
counts it in the dead-declaration budget. [ErasesUniform.lean; Green.lean; Capstone.lean; doc/coverage.md]
### B32 — step_proj is non-vacuous only via lean4lean's sorry'd TrProj adequacy (minor, confirmed)
`step_proj` is non-vacuous today only on hand-built witnesses: its premise is inhabitable only through
lean4lean's `TrProj`, whose kernel adequacy (`inferProj.WF`/`WF_struct`) is `sorry` at the pin — proved, but no
pipeline run currently produces its subject. [ErasesCorrect/Proj.lean:26-29]
### B36 — FixMetatheory.lean is mostly orphaned; LowerFix re-derives weaker halves (minor, confirmed)
`FixMetatheory.lean` (16 declarations) has only three with a consumer outside the file (`closeFixFold_cons`,
`closeFixFold_eq_foldl`, `hasFVar_closeFix_of`); the other eleven have none, and `LowerFix.lean` separately
re-proves, from scratch and only one direction each, two of its results (`hasFVar_of_closeFixFold`,
`not_hasFVar_closeFixFold_of_mem`) rather than calling them. [FixMetatheory.lean; LowerFix.lean:159-214]
### B38 — Four FixUnfold docstrings cite Erases constructors/lemmas that do not exist (minor, confirmed)
Four `FixUnfold.lean` docstrings (`:160,235,490,893`) motivate their theorems by citing declarations that exist
nowhere in the tree — `Erases.instFixvars`, deleted `const_fix`/`fix` rules and their `htobv` premise,
`RecBlockErasure`, `RecBlockErasure.erases_fix_of_closed`. [FixUnfold.lean:160,235,490,893]
### B39 — FixUnfoldChain and Lower.fixUnfold have no consumer anywhere (minor, confirmed)
The whole `FixUnfoldChain` sub-theory has no reference anywhere outside its own file, and `Lower.fixUnfold` has
no consumer either — its own docstring admits the transport the simulation actually spends is `Lower.appReady`.
[FixUnfold.lean:776-899; LowerFix.lean:766]
### B48 — LBPassR is dead and forward-references a nonexistent lower_correct (minor, confirmed)
`LBPassR` is dead — no consumer anywhere — and its doc comment forward-references a theorem `lower_correct` that
does not exist in the tree. [ErasureSpec.lean:452]
### B49 — erasable_indSpine is unconsumed and doc-placed in the wrong module (minor, confirmed)
`erasable_indSpine` is proved but has no consumer, and `doc/rework/06-REPAIRS-W4.md` places its home in a
different module (`ErasesTotal.lean`) than the one it is actually declared in. [ErasureSpec.lean:401;
doc/rework/06-REPAIRS-W4.md:873; ErasesTotal.lean]
### B50 — decl_adequate_of_kernelFind is proved but never discharges decl_adequate (minor, confirmed)
`decl_adequate_of_kernelFind` is proved but never applied, referenced only from `decl_adequate`'s own doc
comment; a reader may mistake it for a discharge of that field, which remains open as upstream ask 4.
[ErasureSpec.lean:313]
### B54 — doc/trust.md's oracle_meta evidence covers only the error route, not the scope-mismatch arm (minor, confirmed)
`doc/trust.md:146`'s `oracle_meta` evidence — "0 fallback hits in 139,196 constants" — measures only the
`isErasableMeta` error route, not the field's scope-mismatch arm (which fires on a *successful* kernel run below
a polymorphic declaration); the field's own doc comment is accurate, the trust row over-reads.
[doc/trust.md:146]
### B61 — SValue.ctor omits the arity bound SEval.ctorVal actually carries (minor, confirmed)
`SValue.ctor` has no arity bound at all, while `SEval.ctorVal` carries `args.length ≤ np + nfs[k]!` ([S] Fig.
12's `nargs ≤ cstr_arity`); `SValue` is strictly wider than what `SEval` actually produces, overstating the doc
comment's claimed correspondence. [FirstOrderInd.lean:271-280; SourceEval.lean:232]
### B62 — SpikeNatFacts row claims WF' for natEnv; only the pre-extension natEnvCas is proved WF' (minor, confirmed)
`doc/trust.md`'s `SpikeNatFacts` row claims a `VEnv.WF'` proof for `natEnv`; the only proved `VEnv.WF'` covers
the smaller pre-extension `natEnvCas`, not `natEnv` itself (`:1435`, two further `addDefEq` extensions) — the
satisfiability claim is weaker than described. [doc/trust.md; SourceEval.lean:1391,1435]
### B66 — SEval.iota's hnp is tied to CasesOnShape only via a separate agreement lemma (minor, confirmed)
`SEval.iota`'s `hnp : IndArity env I np nfs` is not tied to the block `CasesOnShape`'s own existential except
via a separate agreement lemma, `CasesOnShape.agree`, which itself needs `UpstreamAsks`'s block-uniqueness
conjunct — the rule looks stronger standing alone than it is. [SourceEval.lean:257-284]
### B67 — supportedHead's sparseCasesOn also fires for any untabled casesOn prefix (minor, confirmed)
`supportedHead` reports `sparseCasesOn` for *any* `casesOn` whose name prefix is untabled, while the
constructor's own doc comment (`:39-41`) defines the hole narrowly as a name-shape defect; since these error
names feed `doc/coverage.md`, a "sparseCasesOn" row may just mean "untabled inductive."
[Supported.lean:317-320,39-41; doc/coverage.md]
### B68 — SupportError.implementedBy is never produced by the checker at all (minor, confirmed)
`SupportError.implementedBy` is never produced by the checker at all (its own doc comment says so) — the
`@[implemented_by]` hole is actually closed by the `ConfigPinned` hypothesis, not by `SupportedTm`.
[Supported.lean:57-62]
### B69 — isRecursorName misses a tabled recursor whose own prefix is untabled (minor, confirmed)
`isRecursorName` fires only when the recursor's own name prefix is itself tabled; a program naming `Foo.rec`
where `Foo` is untabled but `Foo.rec` is tabled body-less falls through to the constant branch and is accepted —
precisely the coverage gap the `recursorHead` exclusion exists to prevent. [Supported.lean:183-189]
### B71 — kernameSepB checks a broader separation than Supported.kernames states (minor, confirmed)
`kernameSepB` decides separation over both the constant and inductive columns, while `Supported.kernames`
(`:599`), the Prop clause it is proved to decide, quantifies only over the constant column; the Boolean is the
stronger side (no unsoundness), but the fragment predicate alone does not exclude an inductive/constant key
collision. [Supported.lean:246,599]
### B75 — Eval/EvalProp docstrings misattribute MetaCoq flag names and erases_correct's output (minor, confirmed)
`Eval`/`EvalProp`'s docstrings misattribute MetaCoq flag names (`opt_wcbv_flags`, `default_wcbv_flags`) that
`Flags.lean` actually assigns to `eraseFlags`/`entryFlags`, and claim `erases_correct` produces `Eval` when it
actually produces `WcbvEval Γ eraseFlags` — different flag records. [Semantics/Flags.lean:42-49;
Semantics/Eval.lean:249-255]
### B77 — LBTerm.mkApps_spine sits inside namespace LeanToLambdaBox, unlike its siblings (minor, confirmed)
`LBTerm.mkApps_spine` sits inside `namespace LeanToLambdaBox`, unlike every sibling `LBTerm.*` lemma (`LBTerm`
itself is declared at top level in `Basic.lean`) — a citation trap. [Semantics/Compute.lean:35; Basic.lean]
### B83 — Flags.lean's "683/683 propositional=false" claim was measured and revised to 82/82, never updated (minor, confirmed)
`Semantics/Flags.lean:24-27`'s docstring asserts "all 683 inductive entries of the benchmark suite's emitted
environments carry `propositional := false`." This is not merely unverifiable: `doc/rework/05-REPAIRS-W3.md`
§16(e) already re-measured it and found it does not reproduce — the correct count is 82 of 82
`one_inductive_body` entries, among 296 declarations. The shipping docstring was never updated to match the
repository's own later audit. [Semantics/Flags.lean:24-27; doc/rework/05-REPAIRS-W3.md:910-912]
### B84 — Optimize.lean is dead code whose correctness is stated at the wrong flag regime (minor, confirmed)
`Optimize.lean` (60 declarations, not 71 as originally logged) is outside the import closure of
`Capstone.lean`/`Green.lean` (`doc/coverage.md` counts it among 240 dead declarations); `LBOptimize_correct`
(`:785`) is also stated at block-form flags while the shipping erasure emits applied form and the capstone
concludes at `eraseFlags` — genuinely different flag records, so the proved pass cannot compose with the
capstone without re-proving its arms. [Optimize.lean:785; Capstone.lean; Green.lean; doc/coverage.md]
### B89 — About a dozen ErasureRun docstrings cite declarations deleted in the W0-W6 rework (minor, confirmed)
About a dozen `ErasureRun.lean` docstrings cite declarations absent from the whole tree — names deleted in the
W0-W6 rework (`RegBridgeHyps`, `PrepareHyps`, `ColdStartShape.ConstKeysCovered`, and others) or misplace an
existing one. [ErasureRun.lean:1771,2555,1534]
### B91 — run_mkDef_rarg docstring cites a nonexistent Erases.fix constructor (minor, confirmed)
`run_mkDef_rarg`'s docstring cites "`Erases.fix`'s `hrarg`" as a premise; `Erases` has no `fix` constructor at
all — the premise actually lives on the lowering relation's fix rules. The lemma also has no consumer.
[ErasureRun.lean:2452; Erases.lean:211-273]
### B92 — run_visitMutual docstring cites a nonexistent trust class PrepareHyps (minor, confirmed)
`run_visitMutual`'s R7 section docstring attributes `hprep` to a trust class "`PrepareHyps`" that no longer
exists — `run_prepare_erasure_state` now proves the fact outright under `csimp = false`; the hypothesis is
genuine, the narrative is stale, and the `csimp = true` case remains unhandled. [ErasureRun.lean:2536-2556;
ColdStartRun.lean:507]
### B100 — Motives.lean cites a nonexistent aggregator visitExpr_refines_of_steps (minor, confirmed)
`Motives.lean:809` names a nonexistent aggregator `visitExpr_refines_of_steps`; the real aggregator is
`motives_of_steps` (`VisitExprRefines.lean:30`). [VisitExprRefines/Motives.lean:809; VisitExprRefines.lean:30]
### B104 — Mechanical.lean's own premise-count docstring is stale (5/7, not 6/7) (minor, confirmed)
`Mechanical.lean:20-22`'s own docstring claims "six of seven steps carry no premise beyond their `Stepᵢ`" and
names a premise `hctab` that does not exist; at HEAD it is five of seven (`step_visitExpr` also takes `E :
EraserAsks`), and the one kept premise is `hsafe : TableSafe`, not `hctab`.
[VisitExprRefines/Step/Mechanical.lean:20-22; VisitExprRefines/Step/Passes.lean:18-22]
### B109 — SourceTable.check mechanises one run, not all runs, of SourceTableAdequate (minor, confirmed)
`SourceTable.check` mechanises strictly less than `SourceTableAdequate` asserts (its own doc comment says so):
the body column is re-derived by running `prepare_erasure` once, while `ReifiedDecl.Prepared` quantifies over
all runs; "`lake exe reify --check` decides table adequacy" would be false. [Witness/SourceTable.lean:457]
### B110 — No theorem connects Expr.AlphaEq to the opaque Lean.Expr.eqv the checker uses (minor, confirmed)
`Prepared` is stated up to `Expr.AlphaEq`, while the external checker compares bodies with the `@[extern]`,
opaque `Lean.Expr.eqv`; no theorem connects the two, and the gap is patched only by empirically cross-checking
`eqv` against the hand-written `Expr.alphaEqB`. [Witness/SourceTable.lean:195,170]
### B111 — RegInvShape'.specEnv's docstring says three fields; the proof supplies four (minor, confirmed)
`RegInvShape'.specEnv`'s docstring says "the three fields are exactly the invariant's specification-side ones";
the proof term actually supplies four (`spec`, `consts`, `inds`, `fvarFree`). [SpecEnv.lean:117-118]
### B117 — IotaBridge docstring names the wrong consumer module (ElimBody, not ErasesCorrect/Iota) (minor, confirmed)
`IotaBridge.lean:24-26`'s docstring says the module sits below `ElimBody.lean`, "whose ι theorems consume it";
`ElimBody.lean` never mentions "iota" at all — the actual (and only) consumer is `ErasesCorrect/Iota.lean`.
[IotaBridge.lean:24-26; ElimBody.lean; ErasesCorrect/Iota.lean]
### B119 — ErasesCorrectStmt's doc-comment actually describes ErasesCorrectLBStmt (minor, unverified)
A doc-comment above `abbrev ErasesCorrectStmt` (`ErasesCorrect/Steps.lean:1046-1048`) describes it as
"`her+hlow` is `ErasesLB` unfolded, so `hspec` can name the middle term" — but `ErasesCorrectStmt` never
mentions `ErasesLB`; that description matches the composite `ErasesCorrectLBStmt` defined a few lines below. The
comment appears to have drifted onto the wrong declaration. [ErasesCorrect/Steps.lean:1046-1048]
### B120 — ErasesLB.cases's docstring is stale about the design doc, which now prints all three premises (minor, confirmed)
`ErasesLB.lean`'s docstring (`:241-260`) claims `doc/rework/01-DESIGN.md` §4.7 omits the `hclass`/`hpre`/`hppi`
premises of `ErasesLB.cases`. As the design doc stands (`01-DESIGN.md:1408-1421`) it prints all three, with
inline comments — the design doc is not stale here; the shipping docstring's claim about it is. (Corrected form
of the ledger's original B28; see "Refuted" below.) [ErasesLB.lean:241-260; doc/rework/01-DESIGN.md:1408-1421]
### B4 — Two capstone conjuncts (hprep, hwf) are re-exported hypotheses, not derived (note, unverified)
Two capstone conclusion conjuncts — the `prepare_erasure` run equation `hprep` and `LBWfPeregrine`/`hwf` — are
literally its own hypotheses, re-exported rather than derived. [Capstone.lean:162,165,167,172,177]
### B5 — erase_run_ok's environment equation is discarded by injection (note, unverified)
`erase_run_ok`'s environment-equation component (`Γ = sf.gdecls`) is discarded by `injection hp with _ h`; `Γ`
is related to the run only through `hrun`. [Capstone.lean:196]
### B6 — green_G1's comment misattributes hev's inhabitant to itself instead of G5 (note, unverified)
`green_G1`'s doc comment calls `green_G5` "the first rung" to inhabit `hev`; G5 is in fact the only one that
does. [Green.lean:206-209]
### B7 — G7/G8 environments are hand transcriptions checked only by external byte-diff (note, unverified)
G7/G8's emitted environments are hand transcriptions of committed `.ast` files, including hygienic binder names
and macro-scope tags; their correspondence to a real run rests solely on `hrun`, byte-diffed externally by `lake
exe green-check` — data, never proved. [Green.lean:1205,1261,1283]
### B8 — The eight rung subjects sit at the root namespace, not Green's own (note, unverified)
The eight rung subjects and `benchArith` are declared at the root namespace, deliberately outside `namespace
LeanToLambdaBox.Green`. [Green.lean:25-59; VerifyBench/Src/Arith.lean:3]
### B9 — G8 reads/concludes hev at a different spine shape than the other seven rungs (note, unverified)
`green_G8` reads `hev` at the spine `mkApps eG8 [g8Arg]` and concludes at `.app g8Term (peanoLB 0)`, unlike the
other seven rungs, which read both at the bare constant. [Green.lean:1521]
### B10 — Several ColdStartInduction lemmas carry matcher-index fragility and inflated heartbeats (note, unverified)
`ColdStartInduction.lean` carries several fragility markers: matcher-index-dependent lemmas tied to
`Erasure.visitCases.match_7`/`.visitConstructor.match_1` (`:55,88`), heartbeat budgets 5x-30x default
(`:682/687`, `ColdStartRun.lean:376/380`), a doc comment overclaiming two arms as "proved, not refuted"
(`:83-87`), and a `MaskKeeps` universally quantified over all runs from the entry state (`:2033,2157`), heavier
than needed by its own admission. [ColdStartInduction.lean:55,88]
### B16 — register_inductive_run assumes part of its own conclusion (a known-good-state transport) (note, unverified)
`RegInvShape'.register_inductive_run` assumes part of its own conclusion (`hkeys` is the very `keys` field it
concludes) plus three further final-state conditions — a transport at a known-good state, not a preservation
step, though its docstring is honest about this. [ColdStartShape.lean:614]
### B17 — Section header oversells its content; the real bridging theorem lives in SpecEnv.lean (note, unverified)
The section header "The delta column, from the registry" oversells its content — the real bridging theorem
`RegInvShape'.defns` lives in `SpecEnv.lean`; only a level-transport lemma and two arithmetic helpers sit here.
[ColdStartShape.lean:670-681; SpecEnv.lean]
### B18 — Erasability.lean's docstring is stale ("forthcoming", a nonexistent rule, a superseded plan) (note, unverified)
`Erasability.lean`'s module docstring and two doc comments (`:6-18,93-97,105-110`) are stale: they call `Erases`
"forthcoming," cite a nonexistent rule `box : Erases .box .box`, cite a superseded "project plan," and still
call the box-soundness argument "forthcoming" though `erases_correct` now exists. [Erasability.lean:6-18]
### B19 — Expr.const and Expr.ctor rules are asymmetric, breaking const_inv's symmetry (note, unverified)
`Expr.const` and `Expr.ctor` are asymmetric — `const` carries an `env.constants` premise, `ctor` doesn't —
intended, but it makes `const_inv`'s three alternatives non-symmetric. [Erases.lean:211,238]
### B20 — Five lemmas live outside Erasability.lean purely for import-order reasons (note, unverified)
`IsArity.instL`, `Erasable.mono`, `IsArity.of_piBody`, `IsArityUpTo.instL`, `Erasable.instL` live outside
`Erasability.lean` purely for import-order reasons. [Erases.lean:43; ErasesTotal.lean:32,110;
ErasesAbstract.lean:695,705; Erasability.lean]
### B21 — ErasesEnv is a one-constructor inductive with hand-written accessors, not a structure (note, unverified)
`ErasesEnv` is written as a one-constructor inductive with seven hand-written `cases`-based accessors rather
than a genuine structure; adding a clause means hand-writing a new accessor. [ErasesEnv.lean:44-124]
### B22 — SpecContent.erasesEnv never actually uses the structure's own defns field (note, unverified)
`SpecContent.erasesEnv` never actually uses the structure's own `defns` field — an all-scopes `hdefns` premise
is supplied separately instead — though the name suggests it converts the whole bundle. [ErasesEnv.lean:183-193]
### B23 — ErasesEnv.defns demands all-scope erasure witnesses, needing the unstated NoMaxLevels fragment (note, unverified)
`ErasesEnv.defns` demands an erasure witness at *all* level scopes and instantiations, satisfiable only via
`Erases.instL`, which itself needs the unstated `NoMaxLevels` fragment — exactly the strength behind the open
`hbridge` gap (B3). [ErasesEnv.lean:51-89]
### B24 — ErasesEnv non-vacuity needs an 11-field DemoSource bundle, three fields only vacuously (note, unverified)
Non-vacuity of `ErasesEnv` is conditional on an eleven-field `DemoSource` bundle that cannot be hand-built
directly; `lowerEnv_idEnv`'s witness discharges three further fields (`axioms`,`inds`,`defsTotal`) only
vacuously, on a one-definition environment. [ErasesEnv.lean:360-486]
### B25 — ErasableStrengthen's non-vacuity witness exercises only the trivial n=0 case (note, unverified)
The advertised non-vacuity witness for `ErasableStrengthen` (`erasableStrengthen_liftN_zero`) exercises only the
trivial `n = 0` case; the hard `IsArityUpTo` disjunct its own doc comment names is untested.
[ErasesUniform.lean:56-61]
### B26 — Erases.sort_erasable binds an unused env.WF hypothesis (note, unverified)
`Erases.sort_erasable` binds `_henv : env.WF` and never uses it (the doc comment admits it); the statement must
not be read as requiring a well-formed environment. [ErasesTotal.lean:64]
### B29 — erasesLB_of_spine's hlen hypothesis is genuinely unused (theorem is Iff.rfl) (note, unverified)
`erasesLB_of_spine`'s `hlen : targs.length = args.length` is genuinely unused — the theorem is `Iff.rfl` and the
file disables the unused-variable linter for it. [ErasesLB.lean:470-479]
### B30 — erases_correct_of_steps discards a fourth Simulates conjunct before publishing T5 (note, unverified)
`erases_correct_of_steps` proves the four-conjunct motive `Simulates` and then discards the fourth conjunct
(`ErasesEnv` at the value) when producing the published `ErasesCorrectStmt` (T5) — T5 as published is strictly
weaker than its own proof. [ErasesCorrect.lean:380-381; ErasesCorrect/Steps.lean:968,1049]
### B31 — General Erases/Lower lemmas live in correctness-arm files, not Erases.lean/Lower.lean (note, unverified)
General properties of `Erases`/`Lower` (`Erases.lbClosed`;
`Lower.source_app`/`source_mkApps`/`target_lambda`/`appReady`) are declared inside correctness-arm files rather
than `Erases.lean`/`Lower.lean`, purely because those arms are the first consumers — a module-story caveat, not
a defect. [Erases.lean; Lower.lean; ErasesCorrect/Iota.lean:160; ErasesCorrect/Steps.lean:272]
### B33 — SEval.no_elimSpine_value's doc comment under-describes its own eleven-arm case split (note, unverified)
`SEval.no_elimSpine_value`'s doc comment names only five refuted arms; the proof in fact dispatches all eleven,
six of them by shape. [ErasesCorrect/Steps.lean:455-489]
### B34 — Three inconsistent premise counts are given for T5 across two files and a status doc (note, unverified)
Three differently-worded premise counts are given for T5 — "seven binders, six premises... plus the eighth";
"eight binders and seven premises"; "eight premises" — all resolving to the same eight binders but not literally
consistent. [ErasesCorrect/Steps.lean:1046; ErasesCorrect/Close.lean:14-18; doc/rework/07-STATUS.md:120]
### B35 — Simulates/ErasesCorrectStmt are stated only at the empty local context (closed terms only) (note, unverified)
`Simulates`, `ErasesCorrectStmt` and all three step interfaces are stated only at the empty local context — T5
is a closed-term-only statement (consistent with [S] §7.4), which no doc comment says explicitly.
[ErasesCorrect/Steps.lean:968,1049; ErasesCorrect.lean:319]
### B37 — FixMetatheory's header cites a stale Erasure.mkDef line and contradicts itself on layering (note, unverified)
`FixMetatheory.lean`'s header cites `Erasure.mkDef` at a stale line and elsewhere contradicts itself about which
layer carries the fixvars-lookup reconciliation. [FixMetatheory.lean:7-8,65,24-26]
### B40 — FixUnfold.lean has duplicated/out-of-order Part numbers and an unexplained process tag (note, unverified)
`FixUnfold.lean`'s section headings (`~657,752,776,880`) duplicate/misorder Part numbers ("Part 5" appears
twice); one docstring (`:534`) carries an unexplained internal process tag. [FixUnfold.lean:534]
### B41 — Assorted unused Lower/LowerFix/FixUnfold declarations read as deleted-arm residue (note, unverified)
Assorted apparently-unused declarations across `Lower.lean`/`LowerFix.lean`/`FixUnfold.lean`
(`ConstToFVar.of_shift`, `substFix_shift_comm`, `NoBox_mkLambdas`, `mkLambdas_is_lambda`, the whole `bvarsDesc`
law family) read as residue of the deleted η-expansion arms. [Lower.lean; LowerFix.lean; FixUnfold.lean]
### B42 — Lower.elimApp drops pre-arguments; Lower is a forward simulation, not a bisimulation (note, unverified)
`Lower.elimApp` discards the `pre` arguments with only a length premise; under call-by-value this is sound only
as a *forward* simulation — `Lower` is not a bisimulation, worth stating plainly. [Lower.lean:365-381]
### B43 — Lower is deliberately non-deterministic; prose must not say "the pass emits" (note, unverified)
`Lower` is deliberately non-deterministic (both `const` and `fixConst` can apply at a block member) and
`LowerFix` (`:44`) hides its witnesses behind existentials — `Lower Γ s t` does not determine `t`; prose must
say "there is an emission such that," not "the pass emits." [Lower.lean:336; LowerFix.lean:44]
### B44 — Lower.lean's header documents declarations that were deleted (note, unverified)
`Lower.lean`'s header (`:35-40,1766-1773`) documents at length declarations that were deleted — two refutations,
the `ctorEta`/`elimEta` arms, `EtaSpine` — deliberate per a scheduled hygiene tool that does not exist in the
tree. [Lower.lean:35-40]
### B45 — mkElimBodyRec's fixpoint variable is unused and its principalArgIdx disagrees with hrarg's convention (note, unverified)
`mkElimBodyRec`'s fixpoint variable is provably unused (the body is closed at level 0), and its `principalArgIdx
:= dp` does not match every emitted block's `principalArgIdx = 0` — two different objects; no uniform rarg-0
convention holds. [ElimBody.lean:79-84; Lower.lean:444]
### B46 — ElimBody.lean's header self-contradicts on whether eliminator bodies are ever evaluated (note, unverified)
`ElimBody.lean`'s header (`:6-21`) self-contradicts: it opens by describing eliminator bodies as what a runtime
library "must give" (implying execution), then says the specification environment is never evaluated and the
file carries no evaluation theory. [ElimBody.lean:6-21]
### B47 — Three distinct declarations are all named natIid, separated only by namespace (note, unverified)
Three distinct declarations are all named `natIid`; `LeanToLambdaBox.natIid` and `Green.natIid` are the same
value spelled twice, `NatWitness.natIid` is built differently — only namespaces separate them.
[ElimBody.lean:145; Green.lean:79; SourceEval.lean:1476]
### B51 — ForallMatchesLam is vacuously true whenever the subject is not a lambda (note, unverified)
`ForallMatchesLam` (feeding `PrimMonotone.inferType`) is vacuously true whenever the subject is not a lambda, so
that conjunct asserts nothing about a constant's or application's inferred type. [ErasureSpec.lean:72-77]
### B52 — decl_adequate's "at least .safe" premise actually forces ci.safety = .safe exactly (note, unverified)
`decl_adequate`'s premise `DefinitionSafety.safe ≤ ci.safety` reads as "at least .safe," but since `.safe` is
the top of lean4lean's order it forces `ci.safety = .safe` exactly — easy to misparse as admitting
unsafe/partial declarations. [ErasureSpec.lean:271]
### B53 — preparePasses lists three entries; prepare_erasure actually makes four calls plus a conditional walk (note, unverified)
`preparePasses` lists three entries while `prepare_erasure` makes four calls (`macroInline` twice) plus a
conditional `csimp` walk; must not be read as the literal call sequence. [ErasureSpec.lean:333;
Erasure.lean:556]
### B55 — Seven CheckerAdequacy declarations sit inside the dependency's own namespace; "vacuous" should read "cheap" (note, unverified)
Seven `CheckerAdequacy.lean` declarations (`:22-23,41`) sit inside the dependency's own namespace
`Lean4Lean.TypeChecker` — a deliberately deferred hygiene issue (upstream ask 3) — and the file calls a premise
"vacuous" where "cheap" is the accurate word. [CheckerAdequacy.lean:22-23]
### B56 — Origin.lean's header is stale on which kernel corollaries take an UpstreamAsks binder (note, unverified)
`Origin.lean`'s header (`:15-24,61`) self-contradicts about whether the four kernel corollaries take an
`UpstreamAsks` binder (three of four do; only `elim_major` does not), and `consts_classified` separately carries
an unused `(_hwf : env.WF)` that call sites supply for nothing. (Independently confirmed by a blueprint review
of `07-eraser.tex`.) [Origin.lean:15-24,61; 07-eraser.tex]
### B57 — CasesOnShape.inj has no consumer, unlike its three sibling injectivity lemmas (note, unverified)
`CasesOnShape.inj` has no consumer anywhere, unlike its three sibling injectivity lemmas (`IndInfo.inj`,
`CtorOf.inj`, `IndArity.inj`), which all have several. [Origin.lean:55]
### B58 — constsOrigin's first conjunct is assumed though already proved elsewhere in this development (note, unverified)
`UpstreamAsks.constsOrigin`'s first conjunct is assumed even though it is already proved in this same
development (`CtorOf.not_indInfo`) — deliberate, but renders in a dependency graph as a proved fact sitting
inside a hypothesis node. [Upstream.lean:60-66; SourceEval.lean:417]
### B63 — DeltaWitness.env is never shown to be a well-formed VEnv at all (note, unverified)
`DeltaWitness.env` is never shown to be a well-formed `VEnv` at all (an ad hoc pattern table set to `False` and
a two-element `defeqs` predicate); its derivations establish joint satisfiability of side conditions, not a
legitimate kernel model. [SourceEval.lean:655]
### B64 — SEval.mono/SEval.le and siblings have no consumer despite a documented widening schedule (note, unverified)
`SEval.mono`/`SEval.le` and siblings (`CasesOnShape.mono`, `StepDefeq.le`, `deltaOnly*`) have no consumer
anywhere, though the module docstring describes a "widening axis" schedule built on them.
[SourceEval.lean:300,327]
### B65 — SEval indexes with getElem!, so an out-of-range read silently returns a default (note, unverified)
`SEval`'s argument-wise premises index with `getElem!`, so an out-of-range read silently yields a default;
`ctorVal`'s arity bound reads `nfs` at `k` with no `k < nfs.length` premise in the arm itself.
[SourceEval.lean:193-297,533]
### B70 — Supported.projInfo takes a SupportedTm, not a Supported, despite its namespace (note, unverified)
`Supported.projInfo` takes a `SupportedTm`, not a `Supported`, despite living in the `Supported` namespace, so
dot-notation on a `Supported` value does not elaborate — misnamed. [Supported.lean:1051]
### B72 — casesOn/mdata handling is asymmetric by design (spine-index-dependent), easy to misstate (note, unverified)
Metadata handling in `Supported.lean` is asymmetric by design: `.mdata` is accepted only at an empty spine
accumulator, so a metadata node under an application is excluded while one at the root is transparent; a
rendering that drops the spine index states the rule wrong. [Supported.lean:345-367,513-531]
### B74 — fix_guarded fires on argument count alone, never inspecting the guard's head (note, unverified)
`WcbvEval.fix_guarded` fires purely on the accumulated argument count equalling `principalArgIdx` and never
inspects the guard's head, so a boxed guard unfolds like any other value — a reader counting the module
docstring's "three box rules" finds only two constructors. [Semantics/Eval.lean:210]
### B76 — Compute.lean's header overclaims lbEval "implements every rule"; only soundness is proved (note, unverified)
`Compute.lean`'s header (`:7-14`) claims `lbEval` "implements every rule of `WcbvEval`"; only soundness
(`lbEval_sound`) is proved, and no completeness theorem can exist (fuel exhaustion).
[Semantics/Compute.lean:7-14]
### B78 — Env.lean's header doesn't match its contents; the real query lives in Substitution.lean (note, unverified)
`Semantics/Env.lean`'s header claims "global-environment queries," but the principal query `LBTerm.envLookup`
actually lives in `Substitution.lean` instead, while `Env.lean` hosts `wouldCollapse`, which the semantics
itself never reads (only `Optimize.lean` does). [Semantics/Env.lean; Semantics/Substitution.lean:40;
Optimize.lean]
### B79 — propcase_weaken and entryFlags are proved/defined but consumed nowhere (note, unverified)
`WcbvEval.propcase_weaken` and `entryFlags` are proved/defined but consumed nowhere in the repository, despite
docs presenting the theorem as what peregrine's pipeline "needs." [Semantics/Metatheory.lean:479;
Semantics/Flags.lean:49]
### B80 — The anti-vacuity section's own guarantee fails for five of its own lemmas (note, unverified)
The anti-vacuity section header claims every hypothesis-bearing lemma above is guarded and shown to fire;
`WcbvEval.propcase_weaken` and the four `isStuckApp_*` lemmas (`:33,40,47,53`) get no witness.
[Semantics/Metatheory.lean:508]
### B81 — Two "anti-vacuity" lemmas state the trivial (.box : LBTerm) = .box (note, unverified)
`eval_deterministic_fires`/`eval_value_fires` both state literally `(.box : LBTerm) = .box` — trivially true as
Lean declarations, all real content in the proof term, an anti-vacuity smell inside the anti-vacuity suite.
[Semantics/Metatheory.lean:535,539]
### B82 — Two unreconciled kername-equality notions coexist in the Semantics cluster (note, unverified)
Two kername-equality notions coexist in the Semantics cluster with no local reconciliation — a hand-rolled
`ModPath.beq`/`Kername.beq` and a derived `DecidableEq`; the reconciling lemmas live in `Output.lean`, which
this cluster does not import. [Output.lean; Semantics/Substitution.lean:23,31; Semantics/Compute.lean:28-30]
### B85 — isStuckApp_LBOptimize_of_value duplicates its sibling; only the derived one is used (note, unverified)
`isStuckApp_LBOptimize` and `isStuckApp_LBOptimize_of_value` are the same statement up to one implicit binder's
name, the second a direct application of the first; only the derived one is used. [Optimize.lean:668,691]
### B86 — Optimize.lean carries superseded plan tags, an empty section, and a misnamed rule in a comment (note, unverified)
`Optimize.lean` carries superseded "Task B"/B1-B3 plan tags (`:2-8,19,453,544-550,775,891-894,926`); section
"B2" (`:544`) is empty (content moved to `Semantics/Eval.lean`), a vacuity-guard docstring names a renamed rule,
and `LBOptimize` itself has no attached doc comment. [Optimize.lean:544; Semantics/Eval.lean]
### B87 — LBWfPeregrine's term-side clauses are vacuous at every current rung (all terms are bare consts) (note, unverified)
`LBWfPeregrine.etaCtorsTm` and siblings `closed`/`ctorApplied`/`printableNames` have a vacuous *term* half at
every current rung, since every emitted term is a bare `.const`; all content comes from the environment half of
`OnProgram`. [Output.lean:252-256]
### B88 — Before W6, LBWfPeregrine's binder-name clause was unsatisfiable at five of eight rungs (note, unverified)
Until wave W6, `LBWfPeregrine`'s binder-name clause demanded `Basic.cleanIdent`'s alphanumeric class, which the
emitted binder names failed at 0/1/1/1/0/0/34/34 offenders across G1-G8 — G2,G3,G4,G7,G8 carried an
unsatisfiable hypothesis and were vacuous; now `PrintableBinders`. [Output.lean:189,227,257]
### B90 — run_lambdaOrIntroToArity_ok's panic fallthrough drops the world-equation clause its siblings carry (note, unverified)
`run_lambdaOrIntroToArity_ok`'s panic fall-through disjunct drops the `w' = w` clause that all four sibling
binder lemmas carry (forced by the proof, which loses the world equation through an existential) — weakens the
rule for a world-indexed consumer. [ErasureRun.lean:3510]
### B93 — Registration-path lemmas carry undefined design tags R3-R7,R9,R10; R8 is missing entirely (note, unverified)
Registration-path lemmas in `ErasureRun.lean` carry design tags R3-R7,R9,R10 with no legend defined anywhere
under `doc/`, and R8 is entirely absent from the file — a dropped item. [ErasureRun.lean:1717,2379]
### B94 — About eleven ErasureRun declarations have no consumer anywhere in the tree (note, unverified)
About eleven `ErasureRun.lean` declarations (e.g. `visitExpr_run_shape:1184`,
`run_register_inductive_hit_mk:1772`, `run_mkFreshFVarId_list:3276`) have no consumer anywhere in the tree; none
is wrong, but none is load-bearing either. [ErasureRun.lean:1184,1772]
### B95 — The PProd tuple slot order in the *_eq_mutual equations differs from the source order (note, unverified)
The eighteen `*_eq_mutual` unsealing equations order their `PProd` tuple slots differently from the source order
of `Erasure.lean`'s mutual block (e.g. `visitLambda` is second in source, ninth in the tuple) — a standing
source of cross-file confusion. [Erasure.lean:588-919; ErasureRun.lean:516-568]
### B96 — ErasureRun's "model-free" docstring is narrower than it reads (imports Semantics.Values, lean4lean's NameGenerator) (note, unverified)
`ErasureRun.lean`'s "model-free" module docstring is narrower than it reads: the file does import
`Semantics.Values` and lean4lean's `NameGenerator`; neither is a trust bridge, but the docstring should say so
precisely rather than "nothing here mentions `Erases` or `VEnv`." [ErasureRun.lean]
### B98 — Motive14/Motive16's universally-quantified us leaves the run's actual head unpinned (sound, understated) (note, unverified)
`Motive14`/`Motive16`, the two η-loops, conclude about `srcSpine (.const cn us) args` with `us` universally
quantified and no premise tying the loop's own parameters to that head — sound (re-established one level up),
but as stated the motives don't pin the run's actual head expression. [VisitExprRefines/Motives.lean:227,246]
### B99 — The eighteen abstract motive bodies are hand-copies of shipping code, checked only at elaboration (note, unverified)
The eighteen abstract motive bodies are hand-maintained verbatim copies of the shipping `Erasure.lean`
definitions; drift is caught only at elaboration time, and the copies reproduce the shipping code's
`panic!`/`unreachable!` leaves. [VisitExprRefines/Motives.lean:339-623; Erasure.lean]
### B101 — blockKeyed_install carries a premise no specification bundle currently supplies (note, unverified)
`blockKeyed_install` carries a premise no specification bundle supplies (`hfb : fixBlock? lenv n = some
(ci.all.map remove_unsafe_rec)`); if it ever acquires a consumer this becomes a new upstream ask.
[VisitExprRefines/Step/Env.lean:467]
### B102 — Four proved Step/Env and Step/Mechanical results have no consumer (note, unverified)
Four proved results — `blockKeyed_install`, `env_motive_tabled`, `visitMutual_block_hfl_of_run`, and the
`fixtureBlock_*` group — have no consumer anywhere; `env_motive_tabled` alone carries no in-code explanation.
[VisitExprRefines/Step/Env.lean:467,555; VisitExprRefines/Step/Mechanical.lean:1169,1184-1237]
### B103 — run_visitMutual_registers needs a 16x default heartbeat bump (note, unverified)
`run_visitMutual_registers` needs `set_option maxHeartbeats 2000000`, a 16x bump over default — the only visible
elaboration-cost hot spot in this cluster. [VisitExprRefines/Step/Env.lean:328-329]
### B106 — ErasesLBMode.cases spells out a three-way disjunction instead of using consts_classified (note, unverified)
`ErasesLBMode.cases`'s hypothesis `hclass` spells out a three-way disjunction inline instead of naming
`consts_classified`, which discharges it everywhere — harder to state and read than necessary.
[VisitExprRefines/Step/Passes.lean:227-228]
### B107 — Two lemma pairs are verbatim duplicates across the Mechanical/Passes cluster (note, unverified)
`getAppArgs_spine`/`pass_getAppArgs_foldl` are identical in statement and proof, and
`filter_replicate_keep_of_size`/`pass_filter_replicate_keep` are the same fact at two hypothesis strengths —
verbatim duplication across the cluster. [VisitExprRefines/Step/Mechanical.lean:76,825;
VisitExprRefines/Step/Passes.lean:33,89]
### B108 — Two partial defs sit on the verified path in Witness/SourceTable.lean, unreachable from any theorem (note, unverified)
`Reify.visit`/`Expr.alphaEqB` are `partial def`s sitting in a module on the verified path; neither is reachable
from any theorem, but `partial` declarations are opaque constants worth flagging even where documented.
[Witness/SourceTable.lean:283,385]
### B112 — Closed.lean's "sorryAx-free" header claim is unbacked by any measured #print axioms row (note, unverified)
`Closed.lean`'s header (`:27`) claims "no lean4lean, hence sorryAx-free" while the module imports
`Abstract.lean` and `Semantics/Metatheory.lean`; correct for the file's own declarations, but unbacked by any
measured `#print axioms` row. [Closed.lean:27; Abstract.lean; Semantics/Metatheory.lean]
### B113 — Erases.proj deliberately carries no TrExprS premise, which is why NoProjBinders needs binder clauses (note, unverified)
`Erases.proj` deliberately carries no `TrExprS` premise, because lean4lean's `TrProj` pins parameters only up to
defeq — the same fact makes equational uniqueness at `.proj` false, which is why `NoProjBinders` must keep its
binder clauses. [Erases.lean:256-267]
### B114 — Erases is non-deterministic by design; "the erasure of e" is not well defined at this level (note, unverified)
`Erases`'s `box` arm is non-deterministic by design with no negative side condition, so "the erasure of `e`" is
never well defined at this level; determinism is recovered only downstream, on first-order answers.
[Erases.lean:211-218]
### B115 — Thirteen repo-local lemmas use upstream-looking lean4lean names inside namespace LeanToLambdaBox (note, unverified)
Thirteen repo-local lemmas are declared under upstream-looking names (`TrExprS.*`, `VLCtx.*`, `Ctx.LiftN.*`)
inside `namespace LeanToLambdaBox`; several are re-proofs of lean4lean scripts under weaker, pin-tied
hypotheses. [ErasesStrengthen.lean:94-363; ErasesAbstract.lean:645,685]
### B116 — The IotaBridge non-droppability argument is prose with a worked example, not a mechanised refutation (note, unverified)
The argument that `IotaBridge.lean`'s `LBClosed` hypothesis cannot be dropped is prose with a worked
counterexample, not a mechanised `*_refuted` lemma, unlike comparable claims elsewhere; only the positive
witness is mechanised. [IotaBridge.lean:95-110]
### B118 — Most sorry-inheritance status in two large clusters is inferred, not re-measured by #print axioms (note, unverified)
The sorry-free/sorry-inheriting status of most declarations in the `Semantics/Metatheory.lean` and
`ErasesCorrect.lean` clusters was inferred against `doc/trust.md`'s roster rather than by re-running `#print
axioms` on each; only `neverZeroB_sound`, `lbEval_sound`, `LBOptimize_correct` are actually confirmed by a
committed measurement. [Semantics/Metatheory.lean; ErasesCorrect.lean; doc/trust.md]
### B121 — FirstOrderInd's header omits the concrete fact that MetaRocq's firstorder_ind is false on Nat (note, unverified)
`FirstOrderInd.lean`'s module header (lines 1-40) never states the concrete fact — recorded in
`doc/upstream-asks.md:254` and `doc/trust.md:212` — that MetaRocq's shipped `firstorder_ind` evaluates to false
on `Nat`; worth folding that citation into the header. [FirstOrderInd.lean:1-40; doc/upstream-asks.md:254;
doc/trust.md:212]
## (C) Documentation drift
### C2 — 00-REFERENCE-SPEC.md claims normativity but was never amended; ~20 claims are false (major, confirmed)
`doc/rework/00-REFERENCE-SPEC.md` (`:4`) declares itself normative "until amended" but was never edited: roughly
twenty of its claims are false at HEAD (ten `Erases` rules instead of eleven; `LBCompile`, `ErasableAxioms`,
`PrimSpec`, `ErasesDecl`, an `eraseFlags` with `with_prop_case := true` — none of which exist), with the errata
living in `01-DESIGN.md` §3.3 and `04-AMENDMENT-W2.md` and no forward pointer from `00` itself.
**Where:** doc/rework/00-REFERENCE-SPEC.md:4; doc/rework/01-DESIGN.md; 04-AMENDMENT-W2.md.
### C9 — 01-DESIGN.md's printed capstone (hve, five-field bridge) is obsolete on every axis (major, confirmed)
`doc/rework/01-DESIGN.md` §5's printed capstone (`~2592-2710`) is stale on every axis that matters: it shows a
binder `hve : VisitExprRunConcl` (discharged and deleted in W6) and a five-field `ErasureBridge`; the landed
`shipping_erase_correct_firstorder` has no `hve`, a new `hwf : LBWfPeregrine` binder, and `ErasureBridge` has
exactly two fields.
**Where:** doc/rework/01-DESIGN.md; Capstone.lean:99-107.
### C11 — One 01-DESIGN.md table cell states a repair both landed and refuted (major, confirmed)
One table cell in `doc/rework/01-DESIGN.md` §2.4 (row W2b-F1) contradicts itself: it first says a repair "landed
in W3R... measured inhabited, 51 of 51," then in the same cell says "as printed it was REFUTED... no repair is
landed" — the second half is stale pre-repair text left beside the update (`BlockBodiesLambda` is in fact gone).
**Where:** doc/rework/01-DESIGN.md.
### C12 — Three different arm counts given for Lower; the code has fourteen (major, confirmed)
Three different arm counts are given for `Lower` across `01-DESIGN.md` ("fourteen," two lines later "sixteen:
eleven congruence, three redex, two fix") and `02-PLAN.md` ("the 17 arms"); the code has exactly fourteen:
eleven congruence arms plus `elimApp`, `fixConst`, `fixBody`.
**Where:** doc/rework/01-DESIGN.md; 02-PLAN.md; Lower.lean:337-416.
### C18 — 02-PLAN.md's wave table still records landed W6 as "not started" (major, confirmed)
`doc/rework/02-PLAN.md` §1's wave-summary table still records wave W6 as "not started," though it landed
(commits `47334eb`, `e7894de`) and `doc/rework/07-STATUS.md` documents its measured results.
**Where:** doc/rework/02-PLAN.md; doc/rework/07-STATUS.md.
### C3 — 00-REFERENCE-SPEC.md's printed eval_value is actually eval_to_value; the real eval_value differs (minor, confirmed)
`00-REFERENCE-SPEC.md:81` prints `theorem eval_value : WcbvEval Σ fl t v → Value Σ fl v`, which is actually the
repository's `eval_to_value` (`Semantics/Metatheory.lean:95`); the real `eval_value` (`:384`) is a different
statement, `Value Γ fl v → WcbvEval Γ fl v v' → v = v'`. [doc/rework/00-REFERENCE-SPEC.md:81;
Semantics/Metatheory.lean:95,384]
### C4 — Tag namespaces collide across the rework docs (N, F, Q prefixes reused for different things) (minor, confirmed)
Tag namespaces collide across the rework docs: `N1..N6`/`N3a` wave rules vs. a different `N1..N22`
scope-restriction namespace; `F1..F20` judge findings vs. `F-PROP`/`F-ETA`-style shipping findings in the same
document; `Q1..Q8` vs. `Q1..Q12` reusing numbers for different questions. [doc/rework/00-REFERENCE-SPEC.md;
doc/rework/01-DESIGN.md; doc/rework/02-PLAN.md]
### C5 — 00-REFERENCE-SPEC.md's example ledger names two theorems that do not exist (minor, confirmed)
`00-REFERENCE-SPEC.md` §2's example ledger block prints `#print axioms LeanToLambdaBox.LBCompile_correct` and
`...visitExpr_refines_erases`; neither declaration exists — the real bridge theorems are
`visitExpr_refines_erasesLB`/`...Fix` instead. [doc/rework/00-REFERENCE-SPEC.md:502;
VisitExprRefines.lean:190,222]
### C6 — 00-REFERENCE-SPEC.md names six inherited sorryAx sites; the pinned fixture lists sixteen (minor, confirmed)
`00-REFERENCE-SPEC.md` §1 names six inherited `sorryAx` sites and calls the `TrExprS.uniq`/`IsDefEq.uniqU` seam
"the only inherited one"; the pinned fixture (`07-STATUS.md`) now lists sixteen roots, including sites the
executable-checker route brings in. [doc/rework/00-REFERENCE-SPEC.md; doc/rework/07-STATUS.md]
### C8 — 00-REFERENCE-SPEC.md names a flag constant targetFlags that does not exist (minor, confirmed)
`doc/rework/00-REFERENCE-SPEC.md:532` names a flag constant `targetFlags` that exists nowhere in the repository
(other rework docs describe its deletion); the real far end of the chain is `entryFlags`
(`Semantics/Flags.lean:49`). [doc/rework/00-REFERENCE-SPEC.md:532; Semantics/Flags.lean:49]
### C13 — 01-DESIGN.md says the axiom ledger holds 34 rows; it now holds 42 (minor, confirmed)
`01-DESIGN.md` §4.14 states `test/ledger.expected` holds "34 rows... and nothing else"; `test/Ledger.lean` now
has 42 `#print axioms` lines, and W6's U6.5 deletes one row from that list. [doc/rework/01-DESIGN.md;
test/Ledger.lean]
### C14 — 01-DESIGN.md still prints the renamed asciiNames clause as live (minor, confirmed)
`01-DESIGN.md` §4.9 still prints `asciiNames` as a live `LBWfPeregrine` clause; W6 renamed it `printableNames`
after measuring the old clause **false** at five of eight rungs (G2,G3,G4,G7,G8), per `07-STATUS.md` §3.
[doc/rework/01-DESIGN.md; 07-STATUS.md; Output.lean:257]
### C21 — 03-DEV-FIX.md cites a nonexistent AxiomRealizer class-E row for F-EQREC (minor, confirmed)
`03-DEV-FIX.md`'s F-EQREC "Status in the verification" names an `AxiomRealizer` class-E row for `Eq.rec`;
`doc/trust.md`'s class-E table has no such row, and `AxiomRealizer` occurs nowhere in shipping code (deleted per
`02-PLAN.md` U2.8). [doc/rework/03-DEV-FIX.md; doc/trust.md; 02-PLAN.md]
### C25 — 06-REPAIRS-W4.md's "four fields" undercounts EraserAsks's five, plus a derived theorem read as a sixth (minor, confirmed)
`ErasureSpec.lean`'s `EraserAsks` structure has exactly five fields; `doc/rework/03-DEV-FIX.md` writes
`EraserAsks.oracle_informative` as if it were a sixth, though it is a derived theorem with no row of its own in
`doc/trust.md`. The "four fields" undercount traces to a design-stage `06-REPAIRS-W4.md` statement predating the
fifth field. [ErasureSpec.lean:340-391; doc/rework/03-DEV-FIX.md:333; doc/trust.md;
doc/rework/06-REPAIRS-W4.md:19]
### C28 — 08-REPAIRS-W5.md's rung binder list omits hprep/hrun and misstates hcb/hargReach (minor, confirmed)
`08-REPAIRS-W5.md` §8's rung binder list omits `hprep`/`hrun` (which every rung binds), wrongly implies G1 binds
`hcb` (it is discharged there instead), and predates G8's later `hargReach` binder.
[doc/rework/08-REPAIRS-W5.md; doc/trust.md:170; Green.lean:1517]
### C31 — doc/rules-Erases.md still names the deleted clause LBWfPeregrine.asciiNames (minor, confirmed)
`doc/rules-Erases.md:23` still names the deleted clause `LBWfPeregrine.asciiNames`; it no longer exists anywhere
under `LeanToLambdaBox/`, replaced by `printableNames` (`Output.lean:257`). [doc/rules-Erases.md:23;
Output.lean:257]
### C32 — doc/rules-Lower.md labels the construct arm "Block form," the opposite of the actual regime (minor, confirmed)
`doc/rules-Lower.md`'s congruence table labels the `construct` arm "Block form," but the development's
evaluation point is `with_constructor_as_block := false` (applied form) and `LBWfPeregrine.ctorApplied` requires
no `.construct` node carry arguments — the label suggests the opposite regime. [doc/rules-Lower.md;
Semantics/Flags.lean:44]
### C34 — doc/trust.md's SpikeNatFacts row omits that G8 also carries it (minor, confirmed)
`doc/trust.md`'s `SpikeNatFacts` row states only `green_G5` carries it; `green_G8` also binds `(F :
SpikeNatFacts env natIid)`, consumed by `g8_argErasesEnv` (`:1406`) — the row is short one rung.
`doc/coverage.md`, by contrast, does not mention `SpikeNatFacts` at all, so only `doc/trust.md`, not both
documents as originally logged, is incomplete. [doc/trust.md; Green.lean:1507,1406; doc/coverage.md]
### C36 — doc/trust.md calls SpecEnv theorems "fields" of RegInvShape'; they are theorems, not fields (minor, confirmed)
`doc/trust.md:122` calls `RegInvShape'.defns`/`.erasesEnv` "fields" of `RegInvShape'`; they are theorems
declared in `SpecEnv.lean:119-178`, and `RegInvShape'` (`ColdStartShape.lean:142`) has twelve fields, none named
`defns`. [doc/trust.md:122; SpecEnv.lean:119-178,119; ColdStartShape.lean:142]
### C37 — Three unreconciled constant/key counts for what looks like one measurement (minor, confirmed)
Three different, unreconciled constant/key counts appear for what looks like one whole-elaboration-environment
measurement: 228,937, 228,987 (F-KERNAME), and 229,593; no document states whether these are the same population
at different times. [doc/trust.md:167; doc/rework/07-STATUS.md:101; doc/coverage.md:138]
### C38 — doc/trust.md names a route through Witness.sevalValue_of_table that was never written (minor, confirmed)
`doc/trust.md:174` names `Witness.sevalValue_of_table` as a route that would move a rung from trust class A to
class B; no declaration of that name exists anywhere in the tree. [doc/trust.md:174]
### C42 — doc/coverage.md's "permanent binders" list wrongly includes hcb and omits hrun (minor, confirmed)
`doc/coverage.md`'s "permanent binders every rung keeps" list includes `hcb` (which the same paragraph says is
actually discharged at G1) and omits `hrun` (which does stand at every rung and has its own class-D row
elsewhere in the same file). [doc/coverage.md]
### C44 — doc/trust.md's hblk discussion cites a nonexistent lemma run_mkDef_box_not_lambda (minor, unverified)
`doc/trust.md`'s class-D deferral note (the `hblk` discussion) cites a lemma `run_mkDef_box_not_lambda`; no
declaration of that name exists anywhere in the repository — renamed, deleted, or never landed. The blueprint's
chapter 3 does not cite it, so only the trust-doc row is stale. [doc/trust.md]
### C1 — 00-REFERENCE-SPEC.md's ErasureRun.lean size/lemma-count figures and one module placement are stale (note, unverified)
`00-REFERENCE-SPEC.md`, `01-DESIGN.md`, `02-PLAN.md` and `06-REPAIRS-W4.md` describe `ErasureRun.lean` as "3,234
lines" with "74/75 run_* lemmas" and place `run_register_inductive_models` in it; the file is now 3,620 lines
with 136 theorems, and that declaration is correctly in `Bridge.lean` instead. [doc/rework/00-REFERENCE-SPEC.md;
01-DESIGN.md; 02-PLAN.md; 06-REPAIRS-W4.md; ErasureRun.lean; Bridge.lean:230]
### C7 — 00-REFERENCE-SPEC.md's Flags.lean rewrite to-do is stale; the rewrite already landed (note, unverified)
`00-REFERENCE-SPEC.md:636` still lists `Flags.lean`'s header as needing a rewrite to document both flag regimes;
that rewrite has since landed (`Flags.lean:18-30`). [doc/rework/00-REFERENCE-SPEC.md:636;
Semantics/Flags.lean:18-30]
### C10 — 01-DESIGN.md's printed T8 call and 02-PLAN.md's bare-def acceptance count are stale (note, unverified)
`01-DESIGN.md` §5's printed T8 shows the block step supplied as `step6 E hve hsafe` where HEAD passes `step6 E
hsafe` (`hve` discharged in W6); `02-PLAN.md`'s zero-bare-defs acceptance grep now reports 2 (`closeAlt`,
`fixtureBlockProg`, both innocuous). [doc/rework/01-DESIGN.md; doc/rework/02-PLAN.md:537]
### C15 — Several 01-DESIGN.md/02-PLAN.md sections stay in future tense for work that landed long ago (note, unverified)
Several `01-DESIGN.md`/`02-PLAN.md` sections (§§4.10,4.11,7.3, W1 row) remain in future/partial tense ("being
completed," "in progress") for units that landed long ago. [doc/rework/01-DESIGN.md; doc/rework/02-PLAN.md]
### C16 — 01-DESIGN.md's amendment table stops at A22; A23/A24 exist only in a second document (note, unverified)
`01-DESIGN.md` §3.3's own amendment table ends at A22; A23/A24 are defined only in `04-AMENDMENT-W2.md`, with no
pointer from `01-DESIGN.md` — the amendment chain spans two documents silently. [doc/rework/01-DESIGN.md;
doc/rework/04-AMENDMENT-W2.md:647]
### C17 — 02-PLAN.md's zero-bare-defs acceptance criterion now reports 2 (both innocuous) (note, unverified)
`02-PLAN.md:537`'s acceptance criterion asserts a grep over `Step/*.lean` reports 0 bare top-level `def`s; at
HEAD it reports 2 (`closeAlt`, `fixtureBlockProg`), both innocuous lambda-box-level definitions unrelated to the
deleted premise the criterion targeted. [doc/rework/02-PLAN.md:537]
### C19 — 02-PLAN.md names a dev-fix queue file that does not exist under that name (note, unverified)
`02-PLAN.md` §2's W0 "Delivered" paragraph names the dev-fix queue as `doc/dev-fix-queue.md`; that file does not
exist — every other reference in the tree uses `doc/rework/03-DEV-FIX.md`. [doc/rework/02-PLAN.md;
doc/dev-fix-queue.md; doc/rework/03-DEV-FIX.md]
### C20 — lake exe hygiene --schedule is documented red but is measured green at HEAD (note, confirmed (measured))
`build.yml`/`02-PLAN.md` §4/`07-STATUS.md` §5 disclose `lake exe hygiene --schedule` as knowingly red in CI (a
backticked `Output.lean` in `02-PLAN.md`'s W2 row makes the tool read a file deletion for a file that still
stands). Re-measured directly at HEAD (commit `e7894de` already fixed the row): `--schedule` reports 8 deletion
rows, 45 deleted files, 17 live imports, 0 inversions, exiting 0 — the check is green, and `07-STATUS.md` §5's
red claim is itself the stale artifact now. [.github/workflows/build.yml; 02-PLAN.md; 07-STATUS.md; Output.lean]
### C22 — 03-DEV-FIX.md carries a stale line citation and one verification-model name presented as shipping code (note, unverified)
`doc/rework/03-DEV-FIX.md`'s F-KERNAME site citation for `toKername_not_injective` is stale (the witness moved),
and its F-UNSAFEREC prose names a verification-side model, `fixvarMap`, as if it were shipping code, which
actually builds the map inline via `Std.HashMap.ofList` instead. [doc/rework/03-DEV-FIX.md:340;
VisitExprRefines/Step/Env.lean:740; Erasure.lean:907]
### C23 — Three mutually inconsistent line citations for Value.construct_app_val (note, unverified)
Two rework docs cite `Value.construct_app_val` one line off from where the code actually declares it — a small
but mutually inconsistent set of line citations for the same lemma. [doc/rework/03-DEV-FIX.md:110;
doc/rules-Lower.md:49; doc/coverage.md:81; Semantics/Values.lean:104,105]
### C24 — Several rework docs carry stale line/size citations for Output.lean and Optimize.lean (note, unverified)
Several rework docs (`05-REPAIRS-W3.md`, `08-REPAIRS-W5.md`, `probes/reuse-inventory.md`,
`refs/fit-analysis.md`) carry stale line/size citations for `Output.lean` and `Optimize.lean`, including
"`Optimize.lean` 1,090 lines" against the current 948; the declarations all still exist, only the coordinates
drifted. [doc/rework/05-REPAIRS-W3.md; 08-REPAIRS-W5.md; probes/reuse-inventory.md; refs/fit-analysis.md;
Output.lean; Optimize.lean]
### C26 — 07-STATUS.md's commit-count figure is stale, alongside the already-corrected red-CI claim (note, unverified)
`07-STATUS.md` §5 carries a stale commit-ahead-of-main figure ("250," now 252) alongside the red-CI claim that
HEAD's own later commit message already says it corrected (see C20). [doc/rework/07-STATUS.md]
### C27 — The axiom-ledger fixture's trailing inaccessible-name marker is dropped in 07-STATUS.md's transcription (note, unverified)
`test/ledger.expected` writes `Lean.Expr.mkData_flags._native.bv_decide.ax_1_12` with a trailing
inaccessible-name marker that `07-STATUS.md` §2's transcription of the 33 axiom names drops.
[doc/rework/07-STATUS.md; test/ledger.expected]
### C29 — 08-REPAIRS-W5.md's filename says W5 but its title and content are W6 (note, unverified)
`doc/rework/08-REPAIRS-W5.md`'s own title line reads "08 — W6, the closing round" (and does document the W6
round) while its filename says `REPAIRS-W5`; every cross-reference in the tree searches by filename, so a search
for "W6" content fails. [doc/rework/08-REPAIRS-W5.md]
### C30 — reuse-inventory.md's ErasesUniform.lean line count is off by more than 2x (note, unverified)
`doc/rework/probes/reuse-inventory.md:1074` describes "`ErasesUniform.lean` (820 lines)"; the file is 349 lines.
[doc/rework/probes/reuse-inventory.md:1074; ErasesUniform.lean]
### C33 — doc/rules-Lower.md carries several stale line citations and an unattributed axiom-print claim (note, unverified)
`doc/rules-Lower.md` carries several stale line citations for `closeFix_substList_fixSubst`, `FixUnfoldChain`'s
`hrarg`, and a `Closed.lean` claim, plus an unattributed, apparently unverified `#print axioms Lower` claim in
its last line. [doc/rules-Lower.md; Closed.lean:41; FixUnfold.lean:741,804]
### C35 — trust.md and the sorries fixture disagree on two inferProj sorry line numbers, in swapped order (note, unverified)
`doc/trust.md` §(a4) cites two `inferProj.WF`/`inferProj.WF_struct` sorry-site line numbers; the CI-diffed
fixture `test/lean4lean-sorries.expected` and `07-STATUS.md` §1 give different line numbers, in the opposite
order (independently confirmed by grepping the pinned lean4lean source directly). [doc/trust.md; 07-STATUS.md;
test/lean4lean-sorries.expected; Verify/TypeChecker/InferType.lean:392,407]
### C39 — Two docs name a waiting theorem firstOrderIndB_sound that does not exist (note, unverified)
`doc/trust.md`'s `ErasesEnv.tabled` row and `doc/upstream-asks.md` item 4 both name a waiting theorem
`firstOrderIndB_sound` that does not exist as a declaration anywhere; only `firstOrderIndB` and
`firstOrderIndB_step` do. [doc/trust.md; doc/upstream-asks.md; FirstOrderInd.lean:148,198]
### C40 — doc/panics.md excludes one row by prose rather than by a named premise or constructor (note, unverified)
`doc/panics.md` row 8 excludes the `.bvar` head "by the locally-nameless invariant" — prose, not a named premise
or `SupportError` constructor like every other row's exclusion reason. [doc/panics.md]
### C41 — Three different spellings of F-SPARSE's own site citation across two docs and a runtime string (note, unverified)
`doc/panics.md` row 16, `07-STATUS.md` §4, and `doc/coverage.md` give three different spellings of F-SPARSE's
own site citation: a bare line number alone, a two-line-number pair, and a fully qualified runtime string
`LeanToLambdaBox.Erasure:817:55`. [doc/panics.md; 07-STATUS.md; doc/coverage.md; Erasure.lean:817]
### C43 — The blueprint's own Erases.lit rule table omits the env.ContainsLits premise (note, unverified)
`blueprint/src/chapters/04-erases.tex:445`'s rule table for `Erases.lit` omits the `env.ContainsLits l` premise
the actual constructor carries. Documentation-only; already flagged as a MUST-FIX in the chapter's own review
file. [blueprint/src/chapters/04-erases.tex:445; Erases.lean]
## (D) Tooling / CI / infrastructure
### D3 — Coverage.lean's program exclusion-reason strings are hand-written prose, not cross-checked (minor, confirmed)
`Tools/Coverage.lean`'s per-program exclusion-reason strings (`Coverage.progs`'s `why` fields for
Sieve/BinaryTrees/Quicksort/Fannkuch) are hand-written prose, not cross-validated by the tool against the actual
`SupportError` each program's `supportedTerm` run reports; only aggregate error-shape counts across all thirteen
tables are independently verified. [Tools/Coverage.lean]
### D6 — VerifyBench's Sieve and Quicksort roots are not co-importable (duplicate divmod) (minor, confirmed (measured))
The `VerifyBench` `lean_lib` roots are not co-importable: importing all of them fails because
`VerifyBench/Src/Sieve.lean` and `VerifyBench/Src/Quicksort.lean` both declare a root-level `divmod`. Deliberate
given the byte-frozen benchmark sources, but undocumented; any tool that imports every root of every `lean_lib`
— including stock leanblueprint `checkdecls` — cannot run on this workspace. [lakefile.toml;
VerifyBench/Src/Sieve.lean; VerifyBench/Src/Quicksort.lean]
### D1 — Tools/Coverage.lean opens/closes its namespace four times; main sits at the root (note, unverified)
`Tools/Coverage.lean` (`:24-795`) opens and closes `namespace Coverage` four separate times rather than once,
and `main`/`usage` at the file's end are declared at the root namespace, not `Coverage.main`.
[Tools/Coverage.lean:24-795]
### D2 — Coverage.lean and GreenCheck.lean use two different lookup strategies for "the same" eight rungs (note, unverified)
`Coverage.lean`'s `measureRungs` and `GreenCheck.lean`'s `rungs` use two different lookup strategies (reflective
`Name.mkStr3`+`evalConstCheck` vs. a static qualified reference) to reach "the same" eight rung constants — the
two tools check overlapping but not identical properties. [Tools/Coverage.lean; Tools/GreenCheck.lean]
### D4 — Three unsafe defs in Tools/Reify.lean are opaque @[implemented_by] wrappers with no spec (note, unverified)
Three `unsafe def`s in `Tools/Reify.lean` (`blocksModuleUnsafe`/`blocksModule`,
`preparedModuleUnsafe`/`preparedModule`, `checkModuleUnsafe`/`checkModule`) are opaque `@[implemented_by]`
wrappers with zero specification connecting the opaque name to its implementation — acceptable for CI-only
tooling, a pattern that does not occur in the proof layer. [Tools/Reify.lean]
### D5 — The lean4lean-sorries.sh declaration-name attribution is a best-effort awk heuristic (note, unverified)
`scripts/lean4lean-sorries.sh`'s declaration-name attribution for each sorry site is a line-oriented `awk`
heuristic; only the `path:line` locations the fixture diff actually gates are guaranteed stable, not necessarily
the printed declaration name. [scripts/lean4lean-sorries.sh]
## (E) Trust-boundary observations already documented in `doc/trust.md`
### E1 — kernel_ind_head_true/block_keys_distinct being refuted is already in doc/trust.md (note, unverified)
`EraserAsks.kernel_ind_head_true`/`.block_keys_distinct` being refuted in general (F-DEPTH, F-UNSAFEREC) and
bounding the capstone and all eight rungs is already stated, near-verbatim, in `doc/trust.md` §(c)'s own rows
for both fields. [doc/trust.md]
### E2 — hbridge being inhabited nowhere is already stated in doc/trust.md; B3 adds the mechanism (note, unverified)
`hbridge` being inhabited nowhere at any rung is already stated in `doc/trust.md` §(c)'s `hbridge` row
("nowhere, at any rung"); B3 supplies the mechanistic detail — which fixtures exist — that the trust row does
not. [doc/trust.md]
### E3 — step_visitExpr's sole sorryAx role is already documented; the clean axiom footprint is an artefact (note, unverified)
`step_visitExpr` being the sole `sorryAx` entry point of the bridge, and the two `visitExpr_refines_*` theorems'
clean axiom footprint being an artefact of their eighteen steps being hypotheses rather than a genuinely
sorry-free result, is already stated in `doc/trust.md` §(a3). [doc/trust.md]
### E4 — The unused sevalValue_of_table trust-class upgrade route is already documented (note, unverified)
`Witness.sevalValue_of_table`'s route through `SEval.defeq` moving a rung from trust class A to B, and no rung
taking it, is already stated verbatim in `doc/trust.md` §(c)'s `hvwt`/`hty` row. [doc/trust.md]
### E5 — hfo being discharged nowhere is already documented; B60 adds that the general theorem is vacuous too (note, unverified)
`hfo : FirstOrderInd env Nat` being discharged "nowhere" at any rung is already stated in `doc/trust.md` §(c)'s
`hfo` row; B60 supplies the further, undocumented fact that even the general theorem's only witness is vacuous.
[doc/trust.md]
### E6 — Optimize.lean's live trust row despite never running is consistent with the existing class-E note (note, unverified)
`Optimize.lean`'s `LBOptimize_correct` being a "live" trust-ledger row despite the pass never running in the
shipping pipeline is consistent with, and already implicit in, `doc/trust.md`'s class-E note that peregrine's
own optimisation obligations are `Admitted`/unchecked; B84 supplies the specific import-closure and flag-regime
detail. [Optimize.lean; doc/trust.md]
## (F) Restatements of registered F-* findings — new detail only
### F1 — The emitted program fails PeregrinePre/LBExpandedFix, the exact clause peregrine's own fix pass needs (major, unverified)
Beyond what `doc/rework/03-DEV-FIX.md` already says for F-ETA, `Output.lean` names the Lean-level shape of the
same gap: the emitted program does not satisfy `PeregrinePre`/`LBExpandedFix`, exactly the clause peregrine's
own `guarded_to_unguarded_fix` needs for its evaluation-preservation obligation — so the gap is the reason no
verified semantics-preservation argument covers this frontend's fixpoints past the target-side `WcbvEval`.
**Where:** doc/rework/03-DEV-FIX.md; Output.lean:261-272; ETransform.v:666-682.
### F2 — rootKername's numeric branch renders via nb.repr with no cleanIdent escaping at all (note, unverified)
Beyond `toKername`'s `.num`/`.str` alias (the registered F-KERNAME witness), `rootKername` additionally applies
`cleanIdent` to its argument — omitted by the design document's own statement of the node — and the `.num`
branch renders its component via `nb.repr` with no `cleanIdent` escaping at all, so numeric and string
*rendered* components can also collide: a second collision path beyond the one the registered finding measures.
[Basic.lean:41]

## Refuted on verification

**B28** — claimed `01-DESIGN.md` §4.7 prints `ErasesLB.cases` without its `hclass`/`hpre`/`hppi` premises;
the design doc actually prints all three. The drift runs the other way (stale docstring); see B120.
