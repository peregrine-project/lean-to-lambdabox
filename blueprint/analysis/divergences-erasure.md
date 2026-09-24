# Track E -- divergences of the Lean erasure verification from its references of record

## 1. Scope and method

This document compares the verification tree of `lean-to-lambdabox-blueprint`
(`LeanToLambdaBox/*.lean`, built) with its references of record for erasure: [JACM] Sec 7 (canonical for
every theorem statement), [HAB] Spec 20-25 and Sec 6.5-6.6 (lambda-box as a shared artifact, and the
post-erasure pipeline), [L] (origin of box and of the relation-over-function method), [MRD] (module
structure). MetaRocq's sources are ground truth wherever paper and code differ, cited by file and line
relative to `erasure/theories/` and `pcuic/theories/` of `rocq-metarocq-{erasure,pcuic}.1.5.1+9.1` in the
`peregrine` opam switch; Lean-side citations are file and line in this worktree. A divergence is any place
where a reference element has no counterpart here, a counterpart of a different shape, or one carrying
premises the reference does not carry. No divergence is asserted that the code does not show. Alignments are
in section 4, so the list reads as complete relative to the reference's structure; what is open is stated as
open, with the document specifying its closure.

## 2. Summary table

| id | area | reference element | our element | kind | reason |
|---|---|---|---|---|---|
| T1 | target calculus | `EAst.tRel` (`EAst.v:31`) | `LBTerm.bvar` + `LBTerm.fvar` (`Basic.lean:93,94`); `Erases.bvar` + `Erases.fvar` (`Erases.lean:221,225`) | FORCED-ERASER | the eraser opens binders with fresh `FVarId`s, so a bound occurrence has two readings |
| T2 | target calculus | `EAst.tVar`, `tEvar` (`EAst.v:32,33`) | absent | DESIGN | no goal metavariable reaches an erased Lean program |
| T3 | target calculus | `tCoFix`, `erases_tCoFix`, `eval_cofix_*` (`EAst.v:42`, `Extract.v:129`, `EWcbvEval.v:198`) | absent throughout | FORCED-LEAN | Lean has no coinductive types |
| T4 | target calculus | `tLazy`/`tForce`, `eval_force` (`EAst.v:44`, `EWcbvEval.v:279`) | absent | GAP | a consumer running the lazy-force pass leaves the modelled calculus |
| T5 | target calculus | `prim_val` over int/float/string/array, `erases_tPrim` (`Extract.v:137`) | `PrimTag.primInt` only (`Basic.lean:70-85`); no `Erases` arm produces `.prim` | DESIGN | machine primitives are outside `ConfigPinned` (N3) |
| T6 | target calculus | `def term`'s `rarg`, read by `eval_fix` (`EWcbvEval.v:171`) | `FixDef.principalArgIdx`, pinned `0` (`Basic.lean:67`, `Lower.lean:411`) | FORCED-ERASER | the eraser registers every fixpoint at principal argument `0` |
| T7 | target semantics | `erases_correct` at `default_wcbv_flags` (`ErasureCorrectness.v:51`) | conclusion at `eraseFlags = opt_wcbv_flags` (`ErasesCorrect/Steps.lean:1247`) | DESIGN | the stronger point; `propcase_weaken` reaches peregrine's `entryFlags` |
| T8 | target semantics | branch and binder names in `tLambda`/`tLetIn`/`tCase` | names free in `Erases.lam`/`letE` and in `Lower` (`Erases.lean:247,253`, `Lower.lean:361-380`) | DESIGN | `WcbvEval` reads binder counts only, and freeing the name buys alpha |
| B1 | erasability | `isErasable` (`Extract.v:18`) | `Erasable` over `VExpr` (`Erasability.lean:55`), arity disjunct closed under defeq (`:42`) | FORCED-LEAN4LEAN | typing exists only on lean4lean's `VExpr`; the closure matches `Meta.isTypeFormerType` |
| B2 | erasability | `Sort.is_propositional` on a resolved sort (`PCUICFirstorder.v:109-113`) | `InformativeInd`/`PropositionalInd` via `VLevel.IsNeverZero` (`Erasability.lean:281,409`) | FORCED-LEAN | a Lean inductive's sort can be a level parameter, unresolved until instantiation |
| B3 | erasability | `is_erasableb` reflected inside Rocq ([JACM] Sec 7.2) | `Oracle.kernel_isErasable_sound` against lean4lean's executable checker | DESIGN | a trust reduction, at 33 axiom names (`doc/trust.md` (a3)) |
| B4 | erasability | -- | `oracle_false_refl`, `kernel_ind_head_true` (`ErasureSpec.lean:697,717`) | FORCED-ERASER | the oracle is a `MetaM` run with a fallback arm and a fixed arity budget |
| R1 | erasure relation | `erases_tCase` (`Extract.v:109-117`) | no rule; `Lower.elimApp` (`Lower.lean:385`) | FORCED-LEAN | `Lean.Expr` has no case node; a match is a `casesOn` application |
| R2 | erasure relation | `erases_tFix` (`Extract.v:122-128`) | no rule; `Lower.fixConst`/`fixBody`/`fixEta` (`Lower.lean:402,418,441`) | FORCED-LEAN | recursion is a declaration in Lean, not a term former |
| R3 | erasure relation | `erases_tConst` (`Extract.v:104`), `erases_tConstruct` with `~~ isPropositional` (`:106`) | `Erases.const` with `ConstOrigin` (`Erases.lean:238`); `Erases.ctor` with `CtorOf` + `IndInfo`, no propositionality premise (`:231`) | FORCED-LEAN | `Expr.const` writes constant, constructor and type former alike; propositionality gates the elimination sites |
| R4 | erasure relation | `declared_constant`/`declared_inductive` read `lookup_env Sigma c` (`PCUICTyping.v`) | `ConstOrigin`, `CtorOf`, `IndInfo` (`Erases.lean:69,144,173`), `CasesOnShape` (`SourceEval.lean:163`), `IndBlockBelow` (`Upstream.lean:43`) read any `VEnv.WF'` list below `env` | OPEN | the chosen reading makes every constant of a block a `ConstOrigin`, so `UpstreamAsks` is uninhabited; `07-STATUS.md` section 4 specifies the repair |
| R5 | erasure relation | `erases_tProj` with `Subsingleton` (`Extract.v:118`) | `Erases.proj` with `InformativeInd`, no discriminant typing premise (`Erases.lean:266`) | FORCED-LEAN | `Expr.proj` occurs on `Prop` structures; `TrProj` pins parameters only up to defeq |
| R6 | erasure relation | -- | `Erases.mdata`, `Erases.lit` (`Erases.lean:275,272`) | FORCED-LEAN | `Expr.mdata` and `Expr.lit` have no PCUIC node |
| R7 | erasure relation | sort and Pi left to the box rule by typing | `Erases.sort_inv`, `forallE_inv` prove box is the only rule (`Erases.lean:301,305`) | DESIGN | makes two `unreachable!` sites of the shipping eraser provably dead |
| R8 | erasure relation | `erases_subst_instance_decl` under `consistent_instance_ext` (`ErasureProperties.v:412`) | `Erases.instL` under `NoMaxLevels` (`ErasesAbstract.lean:755`) | DESIGN | positional level substitution does not commute with `Level.max` |
| R9 | erasure relation | -- | `Erases.alpha` (`ErasesAlpha.lean:86`) | FORCED-ERASER | a tabled body is pinned only up to `Expr.AlphaEq`, `inlineMatchers` renaming binders |
| R10 | erasure relation | -- | `Lower`, fifteen arms (`Lower.lean:353-450`) | FORCED-LEAN | [JACM] Sec 7.4's own method: a second pass for what a congruence cannot state |
| R11 | erasure relation | `welltyped Sigma [] t` as the single typing premise | `TrExprS` premises on `box`, `lam`, `letE` (`Erases.lean:216,247,253`) | FORCED-LEAN4LEAN | two source representations where PCUIC has one |
| V1 | environment | `erases_deps`, syntax-directed, 17 clauses (`Extract.v:306-366`) | `ErasesEnv`, one clause with seven conditions (`ErasesEnv.lean:74-98`) | FORCED-ERASER | the registry is built incrementally by a monadic run |
| V2 | environment | `term_global_deps`/`includes_deps` (`ErasureFunctionProperties.v:176`) | `ReachableFrom`, a fuel-bounded list closure (`Output.lean:344-359`) | DESIGN | the closure must be decidable at a concrete program |
| V3 | environment | `declared_constant` and `cst_body` (`Extract.v:324`) | the compiler body table `bo` (`ErasesEnv.lean:74`) | FORCED-LEAN | Lean's compiler bodies differ from the kernel-typed ones |
| V4 | environment | `erases_global`/`erases_global_decls` (`Extract.v:284-295`) | no counterpart; only the selective `ErasesEnv` | FORCED-ERASER | the run registers on demand and emits no whole-environment image |
| V5 | environment | -- | `ErasesEnv.elims` and `ElimDecl` (`ErasesEnv.lean:93`, `Lower.lean:66`) | FORCED-LEAN | the eliminator is a declaration here and a term node there |
| V6 | environment | `declared_constant` inside the `tConst` clause | `ErasesEnv.tabled`, ungated by reachability (`ErasesEnv.lean:80`) | DESIGN | `bo` ranges over every tabled name, not only the reached ones |
| V7 | environment | `isPropositionalArity ind_type = ind_propositional` (`Extract.v:276`) | `IndFlagSound`, one direction (`ErasesEnv.lean:64-70`) | FORCED-LEAN4LEAN | the converse is refuted by `arity_of_propositionalInd_false`: lean4lean's translation zeta-reduces a `let`-bound arity sort that `destArity` stops at |
| V8 | environment | `wf_glob` on the one erased environment (`EWellformed.v:199`) | `LowerEnv` (`ErasesEnv.lean:284-311`) and `LBWfSpec` | FORCED-LEAN | R10 creates a second lambda-box environment, pruned and lowered from the first |
| C1 | correctness | `Sigma \|-p t => v` on kernel bodies | `SEval env bo Us fl` with `StepDefeq` (`SourceEval.lean`) | FORCED-LEAN | V3; the defeq obligation reconnects the compiler body to the kernel term |
| C2 | correctness | five premises of `erases_correct` (`ErasureCorrectness.v:52-56`) | eight binders, seven premises (`ErasesCorrect/Steps.lean:1240-1247`) | FORCED-LEAN | `Lower`, `LowerEnv` and `UpstreamAsks` have no reference counterpart |
| C3 | correctness | PCUIC subject reduction and principality, proved | `SubjectReduction.lean` routed through lean4lean's `TrExprS.uniq`/`IsDefEq.uniqU` | FORCED-LEAN4LEAN | the source metatheory is a pinned dependency with its own `sorry` roots |
| C4 | correctness | `NormalizationIn`; [JACM] Sec 5.6 standardisation | no analogue; `hev : SEval ...` is a premise of the observable clause (`Capstone.lean:245`) | FORCED-LEAN4LEAN | nothing Lean-side has the status of wcbv standardisation (N7) |
| C5 | correctness | `firstorder_evalue` (`ErasureFunctionProperties.v:2027`) | `FOSpine` plus `NoBox` and uniqueness (`FirstOrderInd.lean:518,605`) | DESIGN | box-freedom and determinism are what the consumer reads; the shape is exported apart |
| C6 | correctness | `firstorder_erases_deterministic` concludes `t' = erase ... v` (`:2079`) | concludes `t1 = t2` for two relation derivations, under `UpstreamAsks` (`FirstOrderInd.lean:596`) | OPEN | the relation-to-function step at the environment is `hbridge`; `07-STATUS.md` section 4 |
| C7 | correctness | `firstorder_ind` (`PCUICFirstorder.v:67`): no monomorphy, no index clause | `FirstOrderDecl` with `mono` and `noIndices` (`FirstOrderInd.lean:65-77`) | DESIGN | declared scope restrictions, disclaimed at the definition site |
| C8 | correctness | `axiom_free Sigma`, a premise (`ErasureFunctionProperties.v:2316`) | no premise; `NoBodylessRefs Gamma t` decided per rung at the emitted environment (`Output.lean:952`) | DESIGN | the proof never spends it; the source semantics gives a body-less constant no value |
| C9 | correctness | `red Sigma [] t v` to a normal form (`:2322`) | `SEval` to an `SValue` | DESIGN | weak call-by-value on both sides, matching the target's regime |
| P1 | pipeline | `wf_eprogram` over `EEnvFlags`/`ETermFlags` (`EProgram.v:38`) | `LBWfPeregrine`, twelve unparameterised clauses (`Output.lean:304-334`) | DESIGN | one entry point is targeted, so one flag point suffices |
| P2 | pipeline | `expanded_eprogram` inherited from a pre-erasure `eta_expand` (`EEtaExpandedFix.v:187`) | `LBExpandedTFix` concluded of the emitted program (`Output.lean:292`), fed by `Lower.fixEta` | FORCED-ERASER | Lean has no source-level expansion to inherit; recursion appears at registration |
| P3 | pipeline | `constructors_as_blocks`, `remove_params`, `inline_projections` ([HAB] Spec 24-25) | both regimes modelled; theorem at applied form; only `etaCtorsEnv`/`etaCtorsTm` stated | DESIGN | everything downstream of lambda-box is inherited, not redone |
| P4 | pipeline | `remove_match_on_box_correct` with `wf_glob` and `closed_env` | `LBOptimize_correct` with neither (`Optimize.lean:785`) | DESIGN | the induction rebuilds each rule at the optimised environment |
| P5 | pipeline | -- | `LBWfPeregrine.printableNames` (`Output.lean:334`) | FORCED-ERASER | the eraser emits hygienic binder names that no alphanumeric class accepts |
| M1 | method | `erases_erase`, unconditional (`ErasureFunction.v:1228`) | `visitExpr_refines_erasesLB`, conditional on `Supported`, `BridgeInv`, `SpecEnv`, `ErasureSpec` (`VisitExprRefines.lean:190`) | FORCED-ERASER | the shipping eraser is partial, monadic, stateful and can panic |
| M2 | method | `NormalizationIn` threaded abstractly | `Supported`/`supportedB`, a decidable fragment (`Supported.lean`) | FORCED-ERASER | nothing plays `NormalizationIn`'s role, so the gate is syntactic and checkable |
| M3 | method | `erase_global_deps`, a total fold over a finite environment | the cold-start run model and the registry invariant (`ColdStartRun.lean`, `ColdStartShape.lean`) | FORCED-ERASER | registration is incremental and side-effecting |
| M4 | method | `erase_global_erases_deps`, proved (`ErasureFunctionProperties.v:172`) | `ErasureBridge`, the binder `hbridge` (`Capstone.lean:111,209`); `bridgeEnv_of_regContent` (`:161`) derives it from `RegAcc` | OPEN | `RegAcc` is produced for one registration step only; `StepAcc6` is open; `07-STATUS.md` section 4 |
| M5 | method | Rocq's quoting and extraction, outside the proof development | `ErasureSpec`, seven class-D fields, assumed at every level scope (`ErasureSpec.lean:436-484`) | DESIGN | the same gap, named and `Prop`-typed rather than left implicit |
| M6 | method | -- | `EraserAsks`, four fields (`ErasureSpec.lean:668-720`) | FORCED-ERASER | `Erasure.prepare_erasure`'s passes precede the erasure and have no counterpart |
| U1 | trust | PCUIC inversion and injectivity, proved | `UpstreamAsks`, four fields (`Upstream.lean:64-106`) | FORCED-LEAN4LEAN | asks 2, 9, 10 of `doc/upstream-asks.md`; the fork can discharge only asks 9 and 10 |
| U2 | trust | a complete metatheory library | lean4lean's `sorryAx` roots; `hcb`, `hfo` open (`doc/trust.md` (a1),(a2),(a4)) | FORCED-LEAN4LEAN | the pin leaves `TrProj.weak'_inv`, `TrProj.uniq` and ask 4 unproven |
| S1 | scope | erasure for PCUIC, no configuration parameter | `ConfigPinned`, five restrictions (`ErasureSpec.lean:45-47`), plus N1-N18 | DESIGN | each shipping feature outside the theorem is a hypothesis, not an omission |
| S2 | scope | any `t : mkApps (tInd i u) args` in any well-formed environment | eight rungs over one benchmark program plus five spike constants (`Green.lean`) | DESIGN | the rungs check that terms meet the stated interface; no environment satisfies their hypotheses (R4) |
| S3 | scope | -- | `TableSafe.noMaxLevels`, the `max`-free level fragment (`Supported.lean:612`) | DESIGN | the side condition `Erases.instL` transports a body's erasure along (R8) |

## 3. The divergences

### T1 -- the extra `fvar` constructor, and the rule split it forces

**Reference.** `EAst.term` has one variable node, `tRel (n : nat)` (`EAst.v:31`); [HAB] Spec 20 lists it as lambda-box's
de Bruijn index. `erases_tRel` (`Extract.v:89`) is one rule.
**Ours.** `LBTerm` carries `bvar : Nat -> LBTerm` and `fvar : FVarId -> LBTerm` (`Basic.lean:93,94`), the definition
stating the reason at `:88`. `Erases` splits accordingly: `Erases.bvar` (`Erases.lean:221`) and `Erases.fvar` (`:225`),
each carrying `TrExprS`'s own lookup premise, `Delta.find? (.inl i)` or `(.inr x)`.
**Nature.** FORCED-ERASER. **Reason.** `Erasure.visitLambda` and `visitLet` open a binder with a fresh `Lean.FVarId` and
close it with `abstract` (`Basic.lean:142`), so an occurrence under an open binder is an identifier, not an index. A
single-node target cannot represent the state the run passes through.
**Consequence.** `LBTerm` is strictly larger than `EAst.term`, `WcbvEval` makes a free variable a value where
`eval_atom` does so for `tVar` and not `tRel`, and closedness of the emitted program becomes a separate conclusion,
`LBWfPeregrine.closed` (`Output.lean:312`), decided per rung.
**Evidence.** `Basic.lean:88-142`; `Erases.lean:219-226,310-322`; `ConstToFVar` (`Lower.lean:224-251`). (verified)

### T2 -- `tVar` and `tEvar` have no counterpart

**Reference.** `tVar (i : ident)` and `tEvar (n : nat) (l : list term)` (`EAst.v:32,33`), with
`erases_deps_tVar`/`_tEvar` (`Extract.v:309,310`) and the switches `has_tVar`/`has_tEvar` (`EWellformed.v:40,41`).
**Ours.** No `LBTerm` constructor.
**Nature.** DESIGN. **Reason.** Both nodes exist for terms read out of an open proof state; the Lean eraser runs on
elaborated, metavariable-free `Lean.Expr`, and peregrine reads neither.
**Consequence.** The emitted program sits inside the sublanguage every peregrine backend accepts, `LBWfPeregrine` needs
no such switch, and no theorem is weakened.
**Evidence.** `Basic.lean:90-106`; `EWellformed.v:37-53`. (verified)

### T3 -- coinduction has no counterpart anywhere

**Reference.** `tCoFix` (`EAst.v:42`), `erases_tCoFix` (`Extract.v:129-136`), `erases_deps_tCoFix` (`:353`),
`eval_cofix_case`/`eval_cofix_proj` (`EWcbvEval.v:198-211`).
**Ours.** No constructor, no erasure rule, no environment clause, no evaluation rule.
**Nature.** FORCED-LEAN. **Reason.** Lean has no primitive coinductive types, so no source term erases to a cofixpoint.
**Consequence.** The target calculus is a proper sublanguage of `EAst.term` here, at no downstream cost: peregrine's
passes are total on the smaller language.
**Evidence.** `Basic.lean:174-178`; `grep -rn CoFix LeanToLambdaBox/` returns only that line. (verified)

### T4 -- no `tLazy`/`tForce` node and no `eval_force`

**Reference.** `tLazy`, `tForce` (`EAst.v:44,45`), `eval_force` (`EWcbvEval.v:279-284`), the switch `has_tLazy_Force`.
The pass that introduces them, `EImplementLazyForce.v`, is not part of MetaRocq's `erasure/theories` -- it lives in
`peregrine-tool/theories/erasure/EImplementLazyForce.v`, one of the `extra_unsafe_transforms` `Transforms.v` names
alongside `EImplementBox`; [HAB] Sec 6.5-6.6 covers the shared, verified pipeline phases and does not name it.
**Ours.** Neither node nor rule.
**Nature.** GAP. **Reason.** The lazy-force pass is a middle-end transform on the peregrine side; the erasure never
emits the nodes.
**Consequence.** A consumer running that pass leaves the calculus `WcbvEval` models, so the correctness statement says
nothing about the program afterwards. The pass sits outside the pipeline `LBWfPeregrine` targets, but the omission is a
real coverage boundary rather than a forced one.
**Evidence.** `Basic.lean:90-106`; `Semantics/Eval.lean:26-48`. (verified)

### T5 -- primitives restricted to one tag, and unreachable from the relation

**Reference.** `prim_val term` over `primInt`, `primFloat`, `primString`, `primArray`, with `erases_tPrim`
(`Extract.v:137-139`), `eval_prim` (`EWcbvEval.v:275`), four `erases_deps` clauses (`Extract.v:355-364`) and
`all_primitive_flags` (`EWellformed.v:62-66`).
**Ours.** `PrimTag` has the single constructor `primInt` and `PrimModel .primInt = BitVec 63` (`Basic.lean:70-85`).
**Nature.** DESIGN, with the target node kept so the semantics stays total. **Reason.** `ConfigPinned` fixes `cfg.nat =
.peano` (`ErasureSpec.lean:45-47`), and `Supported`'s `strLit`, `machineNat` and `ioLike` errors
(`Supported.lean:47-58`) reject the shapes that would produce one.
**Consequence.** The theorem says nothing about a run with machine `Nat` enabled, which is the shipping default;
restriction N3 of `doc/trust.md` (d) records this.
**Evidence.** `Basic.lean:70-85`; `Erases.lean:283-286`; `Supported.lean:47-58`. (verified)

### T6 -- the principal argument index is pinned to zero

**Reference.** `def term` carries `rarg`; `eval_fix` unfolds exactly when the accumulated spine reaches it
(`EWcbvEval.v:171-179`), and `expanded_tFix` demands `#|args| > d.(rarg)` (`EEtaExpandedFix.v:52`).
**Ours.** `FixDef.principalArgIdx : Nat := 0` (`Basic.lean:67`), documented there as computationally inert.
`Lower.fixConst`, `fixBody` and `fixEta` each carry `hrarg : forall d in defs, d.principalArgIdx = 0`
(`Lower.lean:411,427,450`), and `fixEta`'s target is the one-binder wrapper `.lambda n (.app (.fix defs j) (.bvar 0))`.
**Nature.** FORCED-ERASER. **Reason.** `Erasure.mkDef` emits every registered fixpoint at index `0`, so the wrapper
`Erasure.etaExpandFix` builds is one binder wide.
**Consequence.** A fixpoint whose real principal argument is later unfolds early, which is sound at call-by-value and is
what the relation records.
**Evidence.** `Basic.lean:62-68`; `Lower.lean:402-450`; `Output.lean:235-237`. (verified)

### T7 -- the flag point the theorem is stated at

**Reference.** `WcbvFlags` (`EWcbvEval.v:34`) with `default_wcbv_flags`, `opt_wcbv_flags`, `target_wcbv_flags`
(`:69-71`). Both `erases_correct` (`ErasureCorrectness.v:51`) and `erase_correct_firstorder`
(`ErasureFunctionProperties.v:2310`) are stated at `default_wcbv_flags`.
**Ours.** The same record with the same three field names (`Semantics/Flags.lean:36-40`) and four named points
(`:44-57`). `ErasesCorrectStmt` (`ErasesCorrect/Steps.lean:1232`) and the capstone (`Capstone.lean:190`) conclude at
`eraseFlags = <false, true, false>`, which is `opt_wcbv_flags`.
**Nature.** DESIGN. **Reason.** `eraseFlags` is the stronger point: a derivation there uses no propositional-case rule.
`WcbvEval.propcase_weaken` (`Semantics/Metatheory.lean:22`) carries the conclusion to `entryFlags = default_wcbv_flags`,
which is what peregrine's `untyped_transform_pipeline` declares for its input.
**Consequence.** The Lean conclusion implies the reference's point and not conversely.
**Evidence.** `Semantics/Flags.lean:42-57`; `Semantics/Metatheory.lean:16-30`. (verified)

### T8 -- binder names are free in both relations

**Reference.** `erases_tLambda` and `erases_tLetIn` carry the source `aname` into the target node (`Extract.v:93-100`);
branch binders are a `list name` in `tCase`.
**Ours.** `Erases.lam` binds `{n n'}` and relates `.lam n ty b bi` to `.lambda n' b'` (`Erases.lean:247-249`);
`Erases.letE` likewise (`:253-257`); `Lower.lambda`, `letIn`, `case` and `LowerAlt.lam` all leave the target name free
(`Lower.lean:361-380,460`).
**Nature.** DESIGN. **Reason.** `WcbvEval` reads binder counts and never names -- `iota` matches on `(args.drop
np).length = names.length`, and `beta`/`zeta` substitute positionally. Freeing the name is what makes `Erases.alpha`
(R9) true, which is what the alpha-pinned table needs.
**Consequence.** The relation is coarser than the reference's on names; emitted names are constrained only by
`LBWfPeregrine.printableNames` (P5), and nothing observable depends on them.
**Evidence.** `Erases.lean:243-257`; `Lower.lean:361-380`; `ErasesAlpha.lean:86-101`. (verified)

### B1 -- `Erasable` over `VExpr`, with the arity condition closed under defeq

**Reference.** `isErasable Sigma Gamma t := { T & Sigma ;;; Gamma |- t : T x (isArity T + { u & (Sigma ;;; Gamma |- T :
tSort u) * Sort.is_propositional u }) }` (`Extract.v:18-20`); [JACM] Sec 7.2 and [HAB] Spec 22 give the same two
disjuncts.
**Ours.** `Erasable env U Gamma e := exists A, env.HasType U Gamma e A /\ (env.HasType U Gamma A (.sort .zero) \/
IsArityUpTo env U Gamma A)` (`Erasability.lean:55-56`), with `IsArityUpTo env U Gamma A := exists A', env.IsDefEqU U
Gamma A A' /\ IsArity A'` (`:42-43`).
**Nature.** FORCED-LEAN4LEAN for the carrier, DESIGN for the defeq closure. **Reason.** The defeq closure matches
`Meta.isTypeFormerType`, which whnf-reduces while peeling `forallE`, and is what makes `Erasable.defeq`
(`Erasability.lean:110`) provable -- the fact the box case spends at every step.
**Consequence.** The proof disjunct is cheaper than the reference's -- Lean's `Prop` has definitional proof irrelevance,
so no `CumulProp` or sort-quality apparatus of [JACM] Sec 7.2 is built -- and the arity disjunct is strictly wider than
a syntactic `isArity`.
**Evidence.** `Erasability.lean:20-56,93-116`; `Extract.v:14-20`. (verified)

### B2 -- relevance is semantic, not a resolved flag

**Reference.** `isPropositional Sigma ind` reads `lookup_inductive` and applies `isPropositionalArity` -- `destArity`
followed by `Sort.is_propositional` on the sort it returns -- to `idecl.(ind_type)` (`PCUICFirstorder.v:109-113`);
`erases_tConstruct`, `erases_tCase` and `erases_tProj` gate on it or on `Subsingleton` (`Extract.v:107,112,120`).
**Ours.** `InformativeInd env I := exists ci, env.constants I = some ci /\ exists l, vResultSort ci.type = some l /\
l.IsNeverZero` (`Erasability.lean:281-282`); `PropositionalInd` is the same walk with `forall ls, l.eval ls = 0`
(`:409-410`). `vResultSort` (`:240`) mirrors the eraser's own `arityResultSort` (`Erasure.lean:281`) arm for arm.
**Nature.** FORCED-LEAN. **Reason.** A Lean inductive's declared sort can be a universe parameter whose Prop-ness is
fixed only at instantiation, so a once-and-for-all Boolean is unsound. `IsNeverZero` is lean4lean's own predicate,
quantified over valuations.
**Consequence.** The two are not complements -- a level zero at some valuations and not others satisfies neither, stated
at `Erasability.lean:405-408` -- so consumers spend only the exclusion `propositional_false_of_informative`.
**Evidence.** `Erasability.lean:232-282,400-410`; `Erases.lean:258-269,755-780`. (verified)

### B3 -- the oracle is discharged against lean4lean's executable checker

**Reference.** [JACM] Sec 7.2 reflects `is_erasableb` to `isErasable` inside Rocq; there is one implementation and no
second reference to check it against.
**Ours.** `ErasureSpec.oracle_refl` (`ErasureSpec.lean:437-444`) reduces a `true` verdict of the shipping
`Erasure.isErasable` either to a successful run of the pure verified checker `LeanToLambdaBox.isErasable` or to the
assumed-sound `Erasure.isErasableMeta` fallback; the kernel disjunct is proved by `Oracle.kernel_isErasable_sound`
(`CheckerAdequacy.lean`), reached through `ErasureSpec.oracle_sound_of_run`.
**Nature.** DESIGN. **Reason.** This is the one clause where an assumption is replaced by a proof rather than
repackaged.
**Consequence.** The measured footprint of `shipping_erase_correct_firstorder` and of every rung carries 33 axiom names
-- 29 non-standard lean4lean or Lean-core names and two `_native.bv_decide` certificates -- that keeping the clause as a
named binder would not. `doc/trust.md` (a3) names the alternative and its size: about 40 lines in 5 hunks.
**Evidence.** `ErasureSpec.lean:430-459`; `doc/trust.md` (a3), (b). (verified)

### B4 -- two further oracle clauses with no reference counterpart

**Reference.** none.
**Ours.** `EraserAsks.oracle_false_refl` (`ErasureSpec.lean:697`) and `EraserAsks.kernel_ind_head_true` (`:717`).
**Nature.** FORCED-ERASER. **Reason.** The shipping oracle is a `MetaM` computation: it has a fallback arm whose
soundness no term states, and `Erasure.isArityCheck` walks a head's type under a fixed budget (`Relevance.lean:49-50`),
so a reduced telescope longer than the budget routes the verdict to the fallback. The oracle's level scope needs no
clause: `P` holds at every level scope (M5).
**Consequence.** `kernel_ind_head_true` is explicitly not a theorem; `doc/trust.md` (c) records what would make it one
and that it is measured `.ok true` at 2,940 of 2,940 inductive type formers.
**Evidence.** `ErasureSpec.lean:436-484,668-720`; `doc/trust.md` (b), (c). (verified)

### R1 -- no case rule in the erasure relation

**Reference.** `erases_tCase` (`Extract.v:109-117`): the discriminant erases, the branches erase under their contexts,
and a `Subsingleton` side condition governs the collapse.
**Ours.** No `Erases` arm produces `.case`. `Lower.elimApp` (`Lower.lean:385-401`) consumes an `ElimDecl` for the
eliminator constant, drops the `dp` arguments before the discriminant, peels the minors into alternatives through
`LowerAlt`, and lets over-application ride outside the node.
**Nature.** FORCED-LEAN. **Reason.** `Lean.Expr` has no case node. A source match is an application of a `casesOn` or
recursor constant, an `Expr.const` head under `Erases.app`; a congruence over `Lean.Expr` cannot introduce a node the
source does not have.
**Consequence.** The `Subsingleton` content is relocated rather than dropped: it becomes `InformativeInd` on
`ErasesEnv.elims` (`ErasesEnv.lean:93-97`) and on `SEval.iota`. The cost is that the composite `ErasesLB = Erases ;
Lower` (`ErasesLB.lean:40-42`) is what the theorem relates the output to, so every statement about the emitted term
names two relations.
**Evidence.** `Erases.lean:283-286`; `Lower.lean:383-401`; `ErasesEnv.lean:93-97`. (verified)

### R2 -- no fixpoint rule in the erasure relation

**Reference.** `erases_tFix` (`Extract.v:122-128`): a `tFix` erases to a `tFix` whose bodies erase under the block's
context.
**Ours.** No `Erases` arm produces `.fix`. Three `Lower` arms do: `fixConst` (`Lower.lean:402-417`) at the call site,
`fixBody` (`:418-433`) at the member's own body, and `fixEta` (`:441-450`) at the registered eta-expansion, all three
inlining the same `LowerBlock` premises.
**Nature.** FORCED-LEAN. **Reason.** Top-level recursion is a declaration in Lean. `Erasure.visitMutual` decides
recursiveness and emits a whole-block `.fix` at registration, so the relation must span a constant occurrence and a term
node.
**Consequence.** `Lower` has no `fix` congruence arm at all, so a `.fix` image arises only from these three arms, and
`Lower.source_lambda`'s two-disjunct inversion is what reads them back.
**Evidence.** `Lower.lean:353-450`; `LowerFix.lean`; `doc/rules-Lower.md`. (verified)

### R3, R4 -- the three readings of `Expr.const`, and where they are read

**Reference.** PCUIC writes a constant `tConst`, a constructor `tConstruct` and a type name `tInd`, so `erases_tConst`
(`Extract.v:104-105`) and `erases_tConstruct` (`:106-108`) are keyed on distinct nodes and neither needs a side
condition saying which kind of name it holds. Each reading is `declared_constant`/`declared_inductive`, which read
`lookup_env Sigma c`, a function of the environment.
**Ours.** `Erases.const` (`Erases.lean:238-239`) carries `hc : env.constants c = some ci` and `ho : ConstOrigin env c`
(`:173-175`) -- a positive reading exhibiting an axiom, definition, opaque constant, example or mutual-block member off
a `VEnv.WF'` list below `env`. `Erases.ctor` (`:231-232`) carries `CtorOf env c I k` (`:144-148`) and `IndInfo env I iid
np nfs` (`:69-76`), and no propositionality premise. `CasesOnShape` (`SourceEval.lean:163`) and `IndBlockBelow`
(`Upstream.lean:43`) read a block the same way. An inductive type name has no structural rule: `box` is its only image,
and `erasable_indSpine` makes that sound.
**Nature.** R3 (the three readings) is FORCED-LEAN; R4 (the list they are read off) is OPEN. **Reason.** `Lean.Expr.const`
writes all three kinds of name, so the relation must say which reading it takes, positively, so an introduction site
discharges it from the declaration list it holds. Reading that list off *any* well-formed list below `env`, rather than
off `env`'s own, is a choice, and it is the wrong one: a block's own `addConst` chain is a run of well-formed `axiom`
declarations, so every type former, constructor and recursor of a block is also a `ConstOrigin` (`Origin.lean`'s
`CtorOf.constOrigin`, `IndInfo.constOrigin`).
**Consequence.** `Erases.const_inv` (`Erases.lean:329-337`) has three alternatives where the reference's inversion has
one per node; the reference's `~~ isPropositional` premise on the constructor rule sits at the elimination sites
instead. The exclusion the readings need, `UpstreamAsks.constOriginExcludes` (`Upstream.lean:91`), is refuted at the
fixture environment (`test/Vacuity.lean`'s `not_upstreamAsks_natEnv`), and `erases_natZ_two_ways` gives `Nat.zero` two
distinct erasures there. Every rung binds `UpstreamAsks` beside a fact a block supplies, so no environment satisfies a
rung's hypotheses. `doc/rework/07-STATUS.md` section 4 specifies the repair: read the five predicates off `env`'s own
declaration list (`env.WF' ds`), as `lookup_env` does, after which `VEnv.WF'.consts_origin` gives exclusion and
uniqueness with no further fork change.
**Evidence.** `Erases.lean:134-199,227-239,324-337`; `Upstream.lean:64-106`; `Origin.lean:107-125`;
`test/Vacuity.lean:85-115`. (verified)

### R5 -- the projection rule

**Reference.** `erases_tProj p c c'` (`Extract.v:118-121`) with `Subsingleton Sigma ind`.
**Ours.** `Erases.proj` (`Erases.lean:266-269`) carries `hs : IndInfo env S iid np [nf]`, `hinf : InformativeInd env S`,
`hi : i < nf` and the discriminant's erasure -- and no `TrExprS` premise on the discriminant.
**Nature.** FORCED-LEAN. **Reason.** `Expr.proj` occurs on `Prop`-valued structures, where PCUIC's typing forbids the
analogous elimination, so a relevance premise must be present; it is the semantic test of B2 rather than a syntactic
successor-shape test, which would exclude `Prod` and ten further corpus projection heads. The typing premise is absent
because `TrProj.uniq` pins parameters only up to `IsDefEqU`.
**Consequence.** The arm covers strictly fewer source projections than the reference's rule -- a field of a
propositional structure is a proof, and `box` is its rule -- and widening it is unsound at `eraseFlags`, not merely
unproved. `doc/trust.md` (a4) records the other face: `step_proj` consumes a `TrProj` from `TrExprS.proj`'s own premise
and never builds one, so the arm is non-vacuous only on hand-built witnesses while `TrProj.weak'_inv` and `TrProj.uniq`
are `sorry` at the pin.
**Evidence.** `Erases.lean:258-269,755-780`; `doc/trust.md` (a4). (verified)

### R6 -- two rules with no reference counterpart

**Reference.** none; `Lean.Expr.mdata` and `Lean.Expr.lit` have no PCUIC node.
**Ours.** `Erases.mdata` (`Erases.lean:275`) is a transparent congruence with the identity on the image. `Erases.lit`
(`:272-273`) relates a literal to whatever its one-step kernel unfolding `l.toConstructor` relates to, under
`TrExprS.lit`'s premise `env.ContainsLits l`.
**Nature.** FORCED-LEAN. **Reason.** Both nodes exist in the elaborator's syntax and reach the eraser.
**Consequence.** `Literal.strVal` is outside the fragment (`Supported.lean:50`).
**Evidence.** `Erases.lean:270-275,339-351`; `Supported.lean:47-52`. (verified)

### R7 -- sorts and Pi-types absorbed into `box` by proof

**Reference.** [JACM] Fig. 18 and [HAB] Spec 23 leave `tSort` and `tProd` to the box rule, their erasability following
from typing.
**Ours.** The same placement, made explicit: `Erases.sort_inv` and `Erases.forallE_inv` (`Erases.lean:301-308`) show
`box` is the only rule at either head, and the erasability witness is `Erases.sort_erasable`/`forallE_erasable`.
**Nature.** DESIGN. **Reason.** The two theorems make two `unreachable!` panic sites of the shipping eraser provably
dead (`doc/panics.md`).
**Consequence.** No divergence of content; the relation's coverage at these heads is a theorem here and an observation
in the reference.
**Evidence.** `Erases.lean:288-308`. (verified)

### R8 -- level instantiation under a `max`-free premise

**Reference.** `erases_subst_instance` (`ErasureProperties.v:383`) and `erases_subst_instance_decl` (`:412`) state that
erasure commutes with universe instantiation, under typing and `consistent_instance_ext`; the theorem is spent exactly
once, in the constant case of `erases_correct` (`ErasureCorrectness.v:176`). The image is unchanged, erasure dropping
universes.
**Ours.** `Erases.instL` (`ErasesAbstract.lean:755-761`) concludes `Erases env Us (Delta.instL ls')
(e.instantiateLevelParams ps ls) t` from `Hls : ls.mapM (VLevel.ofLevel Us) = some ls'`, `eq : ps.length = ls.length`,
the erasure at `ps`, and `hnm : NoMaxLevels e`. It is spent at the same place, in `step_delta`, through
`Erases.instantiateLevelParams_of_stepDefeq`.
**Nature.** DESIGN. **Reason.** `Hls` carries `consistent_instance_ext`'s content. `NoMaxLevels` is this development's
own restriction: the positional level substitution the proof runs on does not commute with `Level.max`.
**Consequence.** A new scope restriction, recorded as `TableSafe.noMaxLevels` (`Supported.lean:612`) and as S3 below,
measured satisfied at every tabled body of all eight rungs. The typing premise the reference carries rides on
`ErasesEnv.defns` (`ErasesEnv.lean:94-97`) under the same reachability gate the reference spends it under, rather than
on a separate universal over the table.
**Evidence.** `ErasesAbstract.lean:724-761`; `ErasesEnv.lean:87-110`; `Supported.lean:600-615`. (verified)

### R9 -- erasure is alpha-blind on its source

**Reference.** none; PCUIC's `erases` reads the same `cst_body cb` the environment holds, so no alpha question arises.
**Ours.** `Erases.alpha` (`ErasesAlpha.lean:86-101`): `Erases env Us Delta e t` and `Expr.AlphaEq e e'` give `Erases env
Us Delta e' t`, at the same image.
**Nature.** FORCED-ERASER. **Reason.** `ReifiedDecl.Prepared` pins a tabled body only up to `Expr.AlphaEq` -- binder
names and binder info ignored, nothing else -- because `Lean.Compiler.LCNF.inlineMatchers` renames binders and on
equality the clause is uninhabited wherever that pass fires. `lake exe reify --check` reports five of G7/G8's bodies
matching only up to binder names.
**Consequence.** The theorem holds of a body the run visits rather than of one representative, which is the only reading
`htbl` supports. The lemma is true only because T8 frees the target binder name.
**Evidence.** `ErasesAlpha.lean:80-125`; `doc/trust.md` (b) row `htbl`. (verified)

### R10 -- `Lower` as a separate pass layer

**Reference.** No single relation plays this role. The content is distributed: `iota_red` inside `eval_iota`
(`EWcbvEval.v:140-150`), `cunfold_fix`/`fixSubst` inside `eval_fix` (`:171-179`), and the pass family
`EOptimizePropDiscr`, `ERemoveParams`, `EInlineProjections`, `EConstructorsAsBlocks`. [JACM] Sec 7.4 states the method:
"this direct expansion of cases considerably complicates the correctness proof ... we decide not to include it into the
erasure function, and instead define it as a second pass".
**Ours.** `Lower Gamma t t'` (`Lower.lean:353-450`), fifteen arms: eleven congruence (`box`, `bvar`, `fvar`, `prim`,
`const`, `lambda`, `letIn`, `app`, `proj`, `construct`, `case`), one redex (`elimApp`) and three recursion arms. It is
indexed by the specification environment and by nothing else -- no source term, no typing context, no run state.
**Nature.** FORCED-LEAN, applied through the reference's own stated method. **Reason.** R1 and R2: the two compilation
steps have nowhere else to live.
**Consequence.** Every statement about the emitted program names the composite `ErasesLB`; `erases_correct` carries
`Lower Gammaspec t0 t` and `LowerEnv Gammaspec Gamma` as two extra premises (C2); and `doc/trust.md` (d) records the
class-E row "no Rocq-side copy of `Erases`/`Lower` exists; `doc/rules-Erases.md` and `doc/rules-Lower.md` are the anchor
instead".
**Evidence.** `Lower.lean:6-40,353-450`; `ErasesLB.lean:1-30`; `doc/trust.md` (d). (verified)

### R11 -- every rule carrying a translation premise

**Reference.** PCUIC's `typing` is a single-representation judgment: the syntax the elaborator produces is the syntax
the kernel checks, so `erases` needs no premise beyond `isErasable` in the box case.
**Ours.** `Erases.box` carries `htr : TrExprS env Us Delta e ve` beside `her : Erasable env Us.length Delta.toCtx ve`
(`Erases.lean:216-218`); `Erases.lam` carries `hty` (`:247`); `Erases.letE` carries two (`:253-254`).
**Nature.** FORCED-LEAN4LEAN. **Reason.** Lean has two term representations -- the elaborator's `Lean.Expr`, over which
the eraser and every source-side relation are stated, and lean4lean's `VExpr`, over which `HasType` and `IsDefEq` are
stated. `TrExprS` is the bridge, and it types while it translates.
**Consequence.** `ErasesCorrectStmt` takes `TrExprS env Us [] e ve` where the reference takes `welltyped Sigma [] t`,
and the capstone needs the value-side twins `hvwt` and `hty` as premises of its observable clause, which no rung discharges by a checked
term.
**Evidence.** `Erases.lean:211-257`; `ErasesCorrect/Steps.lean:1240-1247`; `doc/trust.md` (c). (verified)

### V1, V2 -- the environment relation is flat and reachability-keyed

**Reference.** `erases_deps Sigma Sigma'` (`Extract.v:306-366`) is an inductive over the lambda-box term, one clause per
node kind, and `erase_global_erases_deps` (`ErasureFunctionProperties.v:172-177`) derives it from `includes_deps Sigma
Sigma' (term_global_deps et)` by the same induction `erases_erase` walks.
**Ours.** `ErasesEnv env bo lp Gammaspec t` (`ErasesEnv.lean:74-98`) is one constructor with seven named conditions --
`keys`, `deps`, `tabled`, `defns`, `axioms`, `blocks`, `elims` -- keyed on `ReachableFrom Gammaspec t kn`, a
fuel-bounded list closure over the constant bodies (`Output.lean:344-359`).
**Nature.** FORCED-ERASER for the flatness, DESIGN for the closure's shape. **Reason.** The specification environment is
accumulated across many mutually recursive, side-effecting `EraseM` calls, so the coherence fact must be maintainable
incrementally per declaration. The closure must be decidable at a concrete program, which a `Gamma.length`-bounded fold
is and a structural recursion through cyclic mutual blocks is not.
**Consequence.** `ReachableFrom` is not monotone along `Lower` in either direction -- a `.case` node names its block
where the source spine had a `.const` -- so no reachability transfer between the two environments is available; the
repaired form and its three obligations are at `doc/rework/09-REPAIRS-W7.md` section 2.0.
**Evidence.** `ErasesEnv.lean:6-30,74-98,195-237`; `Output.lean:341-380`; `doc/rework/09-REPAIRS-W7.md` section 2.0. (verified)

### V3 -- the compiler body table replaces `cst_body`

**Reference.** `erases_constant_body (Sigma, cst_universes cb) cb cb'` (`Extract.v:264-268`) reads the kernel's declared
body, and `erases_deps_tConst` (`:324-329`) reads the one `eval_delta` unfolds (`EWcbvEval.v:212-217`).
**Ours.** `ErasesEnv` is parameterised by `bo : Name -> Option Expr` (`ErasesEnv.lean:74`), and `ErasesEnv.defns`
(`:129-134`) reads it. `SEval.deltaC` unfolds the same table, so the environment relation and the source delta rule
unfold one term.
**Nature.** FORCED-LEAN. **Reason.** Lean's compiler-facing bodies -- post well-founded-recursion elaboration and
`_unsafe_rec` replacement -- differ from the kernel-typed ones. There is no single "the" body the way `cst_body` is one
thing.
**Consequence.** `SEval.deltaC` carries `hdef : StepDefeq` reconnecting the compiler body to the kernel term, and `hcb :
CompilerBodies` is a separate hypothesis that every tabled body is kernel-typeable at its declared type. `doc/trust.md`
(d) records the class-E row "compiler-vs-kernel bodies ... only propositional instances are covered"; `hcb` is
discharged at G1 only and stays a binder at G2-G8.
**Evidence.** `ErasesEnv.lean:67-84`; `SourceEval.lean` `deltaC`; `doc/trust.md` (c), (d). (verified)

### V4 -- no total environment erasure

**Reference.** `erases_global_decls` and `erases_global` (`Extract.v:284-295`) relate a whole PCUIC `global_env` to a
whole lambda-box `global_declarations`, declaration by declaration.
**Ours.** No counterpart. `ErasesEnv` states only what the reached keys hold.
**Nature.** FORCED-ERASER. **Reason.** The run registers on demand: `Erasure.visitConst` and `visitMutual` add entries
as the traversal reaches them, so the final `gdecls` is a dependency-selective slice.
**Consequence.** No theorem here says that the emitted environment is the erasure of the source environment; the
strongest statement is the seven-clause `ErasesEnv` at one program, which matches `erases_deps` and loses what
`erases_global` supports.
**Evidence.** `ErasesEnv.lean:74-98`; `Extract.v:284-295`. (verified)

### V5 -- an eliminator-declaration clause

**Reference.** none; `tCase` and `tProj` are term nodes whose metadata comes from `declared_inductive` directly
(`Extract.v:336-351`).
**Ours.** `ErasesEnv.elims` (`ErasesEnv.lean:93-97`): at a reached `casesOn` constant of an informative inductive the
environment holds an `ElimDecl` (`Lower.lean:66-73`) -- an `ElimBody`-shaped constant body together with its block's
declaration at the same numbers and not propositional.
**Nature.** FORCED-LEAN. **Reason.** R1: the `.case` node is a pass output whose source is a constant, so the
environment relation must say what that constant's entry is.
**Consequence.** `ErasesEnv.runtimeKey_isCasesOn` (`ErasesCorrect/Steps.lean:929-933`) is a theorem rather than a
clause: a reached runtime key belongs to a `casesOn` constant with no compiler body, derived from `defns` and `axioms`
together. This is also where the reference's `Subsingleton` content lands.
**Evidence.** `ErasesEnv.lean:145-166`; `Lower.lean:63-73`; `ErasesCorrect/Steps.lean:929-940`. (verified)

### V6 -- `tabled` has no reachability trigger

**Reference.** `declared_constant Sigma kn cb` sits inside `erases_deps_tConst` (`Extract.v:325`), so it is asked only
at a constant the term reaches.
**Ours.** `ErasesEnv.tabled : forall c b, bo c = some b -> ConstOrigin env c` (`ErasesEnv.lean:80`), quantified over the
whole table.
**Nature.** DESIGN. **Reason.** `bo` ranges over every tabled name, and the reading it refutes is at a constant the
erasure emits no key for, so there is no occurrence to trigger on.
**Consequence.** The clause is a global fact about the table rather than about the program, which is why
`bridgeEnv_of_regInv` takes it as the separate argument `htab` (`Capstone.lean:137`). Its discharge is blocked on
upstream ask 4: `Origin.lean` proves the two halves that surround it and nothing at the pin joins them.
**Evidence.** `ErasesEnv.lean:126-130`; `Capstone.lean:133-141`; `doc/trust.md` (c). (verified)

### V7 -- the propositional flag holds in one direction only

**Reference.** `erases_one_inductive_body` (`Extract.v:271-276`) ends in `isPropositionalArity oib.(ind_type) =
oib'.(E.ind_propositional)`, an equality, and `erase_one_inductive_body` sets the field from that walk.
**Ours.** `IndFlagSound env I iid mib := forall oib, mib.bodies[iid.idx]? = some oib -> oib.propositional = true ->
PropositionalInd env I` (`ErasesEnv.lean:64-70`) -- an implication, carried beside `IndBodyOf` (`Lower.lean:49-55`),
which holds no propositional clause at all. `ErasureSpec.propositionalInd_of_arity` (`ErasureSpec.lean:610`) proves
that half from `decl_adequate` and the arity walk's commutation with translation.
**Nature.** FORCED-LEAN4LEAN. **Reason.** The converse is false: `arity_of_propositionalInd_false`
(`ErasureSpec.lean:639`) refutes it at `inductive FooBVar : (let u := Prop; u)`. `Erasure.arityResultSort`
(`Erasure.lean:300-305`) walks `forallE`, `letE` and `mdata`, and stops at the `let`'s bound variable exactly as PCUIC's
`destArity` stops at `tRel` (`PCUICAst.v:486-490`); lean4lean's `TrExprS.letE` zeta-reduces the same arity to `Sort 0`
(`trExprS_letBVarArity`). A walk that reduced further would break the sound half at an alias-headed arity, where
`TrExprS.const` keeps the `.const`.
**Consequence.** The half the consumers spend is available -- `IndFlagSound.notPropositional` (`ErasesEnv.lean:72`)
gives the `= false` that `WcbvEval.iota` and `WcbvEval.proj` test -- and assuming the equality would assume something
refuted. The clause fires only at a `true` flag, and no block any rung emits carries one, so it is vacuous at all eight
rungs; an emitted `.case` on a `let`-bound propositional arity is stuck at `eraseFlags`, and `SEval.iota`'s `hinf` has
no derivation there.
**Evidence.** `ErasesEnv.lean:36-75`; `Lower.lean:45-62`; `ErasureSpec.lean:580-660`; `doc/rework/03-DEV-FIX.md`
F-ARITYLET. (verified)

### V8 -- `LowerEnv` in place of environment well-formedness

**Reference.** `wf_glob` (`EWellformed.v:199`) and `wf_eprogram` (`EProgram.v:38`) state well-formedness of the erased
environment; there is no relation between two lambda-box environments, because there is only one.
**Ours.** `LowerEnv Gammaspec Gamma` (`ErasesEnv.lean:284-311`), eight fields: `keys`, `defs`, `defsTotal`, `axioms`,
`inds`, `sub`, `closed`, `specClosed`. `defs` asks a body declared by both to be a `Lower` image; the eta-expansion the
registration side emits for a block member is one, `Lower.fixEta`, read off the block by `Lower.fixEta_of_block`.
**Nature.** FORCED-LEAN. **Reason.** R10 creates a second lambda-box environment: the specification one the relations
are stated against, and the emitted one the run produces. The pruning direction (`sub`) and its totality (`defsTotal`)
both need stating, without which a definition pruned out of `Gamma` satisfies `defs` vacuously while the target is stuck
at its `.const`.
**Consequence.** One more premise on every statement about the emitted program, and a second well-formedness predicate,
`LBWfSpec`, for what the `Lower` metatheory reads of `Gammaspec`.
**Evidence.** `ErasesEnv.lean:270-360`; `LowerFix.lean`. (verified)

### C1 -- the source semantics

**Reference.** `Sigma |-p t => v` is PCUIC's `eval` (`PCUICWcbvEval.v`), with `eval_delta` reading
`declared_constant_gen (lookup_env Sigma) c decl` -- the kernel's own declaration.
**Ours.** `SEval env bo Us fl` (`SourceEval.lean`), eleven rules: `lam`, `beta`, `zeta`, `deltaC`, `ctorVal`, `indVal`,
`sort`, `forallE`, `iota`, `proj`, `lit`. `deltaC` reads `bo`, instantiates the body at the call site's levels, carries
`hdef : StepDefeq` and carries `hnd : forall I dp nm, not CasesOnShape env c I dp nm`, which keeps a saturated
eliminator spine on the `iota` route alone.
**Nature.** FORCED-LEAN. **Reason.** V3 for the table; `hnd` mirrors the eraser's own dispatch, which never visits a
`casesOn` body, and without it a saturated eliminator spine has two derivations.
**Consequence.** `ctorVal` and `indVal` are top-level rules rather than instances of a separate `value` predicate, which
is [JACM] Fig. 12's `value_head_cstr` and `value_head_ind` stated directly, `harity` transcribing `nargs <= cstr_arity`.
**Evidence.** `SourceEval.lean:1-30` and the rule block; `SubjectReduction.lean:5-19`. (verified)

### C2 -- the premise list of the simulation

**Reference.** `erases_correct` (`ErasureCorrectness.v:51-57`): `wf_ext Sigma`, `welltyped Sigma [] t`, the erasure,
`erases_deps Sigma Sigma' t'`, `Sigma |-p t => v`, concluding `exists v', Sigma;;; [] |- v => v' /\
|| Sigma' |- t' => v' ||`.
**Ours.** `ErasesCorrectStmt` (`ErasesCorrect/Steps.lean:1240-1247`): `env.WF`, `TrExprS env Us [] e ve`, `SEval env bo
Us fl [] e v`, `Erases env Us [] e t0`, `Lower Gammaspec t0 t`, `ErasesEnv env bo lp Gammaspec t0`, `LowerEnv Gammaspec
Gamma`, `UpstreamAsks env`, concluding `exists v0 v', Erases env Us [] v v0 /\ Lower Gammaspec v0 v' /\ WcbvEval Gamma
eraseFlags t v'`. Eight binders and seven premises, the statement naming the middle term.
**Nature.** FORCED-LEAN. **Reason.** `Lower`/`LowerEnv` carry the pass layer of R10; `UpstreamAsks env` carries the
lean4lean facts the pin does not prove (U1). Nothing else is added: each arm reads what it needs off `ErasesEnv`'s seven
clauses, off the source rule's own fields, and off `UpstreamAsks`.
**Consequence.** The theorem is the reference's forward simulation with two extra layers and one extra trust premise.
The existential quantification of the value's erasure is the reference's, for the reference's reason. The conclusion is
not squashed, `Prop` being the ambient sort.
**Evidence.** `ErasesCorrect/Steps.lean:1240-1259`; `ErasesCorrect/Close.lean:9-43`. (verified)

### C3 -- subject reduction routed through lean4lean

**Reference.** [JACM] Sec 7.2 states the erasure proof against PCUIC declarative typing and consumes subject reduction,
principality strengthened to unique sort quality, and canonicity, all proved in the development.
**Ours.** `SubjectReduction.lean` proves that a term's translation and its value's translation are definitionally equal
in `env`: the beta and zeta arms outright, the delta, iota and projection arms by handing back the `StepDefeq` the
source rule carries, the two spine-value arms through `SEval.defeq_spine`. Uniqueness comes from lean4lean's
`TrExprS.uniq` and `IsDefEq.uniqU`.
**Nature.** FORCED-LEAN4LEAN. **Reason.** The source metatheory is a pinned dependency, not a chapter of this
development.
**Consequence.** `SEval.defeq` inherits lean4lean's `sorryAx` and is the one class-B ledger row; the five inherited
roots are at `doc/trust.md` (a1) and the fork-authored `VEnv.WF.patsStrong` at (a2). Three of the eleven `SEval` rules
carry their definitional equality as an explicit obligation rather than deriving it, which is what makes the source
relation usable without a full source metatheory.
**Evidence.** `SubjectReduction.lean:5-19`; `doc/trust.md` (a1), (a2). (verified)

### C4 -- no normalisation hypothesis, and no standardisation

**Reference.** `erase` is built by well-founded recursion on an assumed `NormalizationIn` (`ErasureFunction.v:1228`,
`ErasureFunctionProperties.v:2313`), citable because Rocq's metatheory supplies strong-normalisation witnesses
PCUIC-side; [JACM] Sec 5.6 is the one place weak call-by-value standardisation is used.
**Ours.** No analogue exists and none is assumed. The source evaluation enters as a hypothesis: `hev : SEval env
tbl.body? [] fullFlags [] (mkApps e args) v`, a premise of the observable clause (`Capstone.lean:245`), discharged by a
checked derivation at G5 only.
**Nature.** FORCED-LEAN4LEAN. **Reason.** Nothing Lean-side has the status of wcbv standardisation or of canonicity;
`Supported` (M2) takes the structural place `NormalizationIn` holds.
**Consequence.** Restriction N7 of `doc/trust.md` (d): the capstone keeps the conditional form. A rung other than G5
binds `hev` rather than proving it; at G7-G8 no witness is attempted,
Arith's evaluation being 45 recursive calls each owing the unselected minor's derivation as well.
**Evidence.** `Capstone.lean:190-264`; `doc/trust.md` (c) row `hev`, (d) row N7. (verified)

### C5, C6 -- the first-order observation and its uniqueness

**Reference.** `erase_correct_firstorder` (`ErasureFunctionProperties.v:2310-2328`) concludes `|| Sigma'.1
|- t' => et' ||` with `firstorder_evalue Sigma'.1 et'` (`:2027-2032`), a constructor-spine predicate reading
`lookup_constructor_pars_args` and demanding saturation. `firstorder_erases_deterministic` (`:2079-2090`)
concludes `t' = erase X_type Xext ... v`: the relation's image at a first-order value equals the extraction
function's output.
**Ours.** `firstorder_erases_core` (`FirstOrderInd.lean:522`) returns `FOSpine t` and `forall t', Erases env Us [] v
t' -> t' = t` in one induction over `SValue`; `firstorder_no_box` (`:609`) projects box-freedom and
`noBox_lower_of_foSpine` transports it to the lowered value; `firstorder_erases_deterministic` (`:596`) concludes
`t1 = t2` for two arbitrary derivations. All three take `UpstreamAsks env`.
**Nature.** DESIGN for the observation's shape; OPEN for the uniqueness target. **Reason.** The shape divergence is a
choice: `NoBox` and the image's uniqueness are what the consumer reads, and `FOSpine` is exported separately for the
`Lower` transport, box-freedom not transporting along `Lower`, whose `fixConst` arm relates a box-free constant to a
block whose definitions carry their own boxes. The uniqueness divergence is architectural: MetaRocq's `erase` is a total
function already known by `erases_erase` to inhabit the relation everywhere, so pinning the image to it is free; here
the relation-to-function link is M1 at the term level and `hbridge` at the environment level.
**Consequence.** The capstone concludes relation-level determinism and box-freedom, one step short of "the emitted value
is the function's output at `v`". The uniqueness holds only under `UpstreamAsks`, which no environment declaring an
inductive inhabits; without it `Nat.zero` has two erasures (R4). Closing the step to the function needs the same
content M4 waits on; `doc/rework/07-STATUS.md` section 4 specifies it.
**Evidence.** `FirstOrderInd.lean:15-38,522-615`; `Capstone.lean:260-264`; `test/Vacuity.lean:107-113`;
`doc/rework/07-STATUS.md` section 4. (verified)

### C7 -- the first-order predicate is strictly stronger

**Reference.** `firstorder_type`, `firstorder_con`, `firstorder_oneind`, `firstorder_mutind`, `firstorder_ind`
(`PCUICFirstorder.v:43-70`). `firstorder_oneind` conjoins `negb (Sort.is_level (ind_sort ind))`; `firstorder_mutind`
excludes `CoFinite`. There is no monomorphism check -- `ind_universes` is never inspected -- and no index-freedom check:
`firstorder_con` walks `cstr_args ++ ind_params` and never `ind_indices`.
**Ours.** `FirstOrderDecl` (`FirstOrderInd.lean:65-77`) has four clauses: `mono` (`decl.uvars = 0`), `informative`
(every type former lands in a successor sort), `noIndices` (`t.type.piArity = decl.nparams`) and `fields`. The closure
is existentially quantified inside `FirstOrderInd` (`:86`) as a post-fixed point, a free `fo` being satisfied by `fun _
=> True`.
**Nature.** DESIGN. **Reason.** `mono` and `noIndices` are declared scope restrictions, disclaimed at the definition
site as "booked to this development, not to Letouzey's Def. 14 or to MetaRocq's `firstorder_ind`". The shipped
`firstorder_ind` is not transcribed at all, because it answers `false` on `nat`, the one type all eight rungs need
classified first order.
**Consequence.** The observable clause covers a narrower class of answer types than [JACM]'s. `firstOrderIndB` decides
the property on a reified table and `firstOrderIndB_step` is its table-side half, but the model-side half is the kind
transfer from `lenv` to `env.constants` filed as upstream ask 4, so `hfo` is a binder at every rung.
**Evidence.** `FirstOrderInd.lean:24-38,65-86,130-150`; `PCUICFirstorder.v:43-70`; `doc/trust.md` (c) row `hfo`, (d) row
"MetaRocq". (verified)

### C8, C9 -- the two remaining sides of the first-order statement

**Reference.** `erase_correct_firstorder` takes `axiom_free Sigma` and `red Sigma [] t v` with `not { v' & Sigma ;;; []
|- v => v' }`.
**Ours.** The capstone takes neither. `NoBodylessRefs Gamma t` (`Output.lean:952-953`) -- no constant the program
reaches is declared without a body -- is decided per rung as the standalone term `Green.g<i>_noBodylessRefs`, `by
decide +kernel`, read by `doc/coverage.md`'s census. The evaluation premise is `SEval` to an `SValue` (C1), with no
separate normal-form side condition, `SValue` being the value predicate `SEval` returns.
**Nature.** DESIGN. **Reason.** The proof never spends axiom-freedom: the source semantics gives a body-less constant no
value, so a run reaching one has no `hev` derivation and the non-vacuity the reference's premise protects is `hev`'s to
guard (`Capstone.lean:37-44`). `NoBodylessRefs` is the same content as `axiom_free` on the emitted side, where
`EWellformed.wellformed`'s own constant clause -- `has_axioms || isSome d.(cst_body)` (`EWellformed.v:143-147`) -- puts
it.
**Consequence.** Measured true on all five corpus programs and all eight rungs. Restriction N2 records the source-side
face: an `@[extern]` constant is emitted body-less and a program reaching one has no source evaluation to simulate.
**Evidence.** `Capstone.lean:37-44`; `Output.lean:946-960`; `Green.lean` (`g<i>_noBodylessRefs`); `doc/trust.md` (d)
N2. (verified)

### P1 -- output well-formedness is unparameterised

**Reference.** `wf_eprogram (efl : EEnvFlags) p := wf_glob p.1 /\ wellformed p.1 0 p.2` (`EProgram.v:38`), where
`EEnvFlags` carries `has_axioms`, `has_cstr_params`, `cstr_as_blocks` and an `ETermFlags` record with one switch per
node (`EWellformed.v:37-60`); each pipeline phase declares its own flag point.
**Ours.** `LBWfPeregrine Gamma t` (`Output.lean:304-334`), twelve clauses with no flag parameter: `keys`, `declsWf`,
`closed`, `constsOk`, `ctorApplied`, `ctorDecl`, `casesExh`, `expandedFix`, `projDecl`, `etaCtorsEnv`, `etaCtorsTm`,
`printableNames`. Every clause is stated over the environment and the term, mirroring `expanded_eprogram_cstrs`
(`EEtaExpanded.v:557-558`).
**Nature.** DESIGN. **Reason.** One entry point is targeted -- peregrine's `untyped_transform_pipeline` -- so one flag
point suffices: `ctorApplied` fixes `cstr_as_blocks = false`, `constsOk` asks every reached constant to be declared, and the
node switches are all true for the nodes `LBTerm` has.
**Consequence.** A consumer running the pipeline at another flag point reads nothing from this conclusion.
**Evidence.** `Output.lean:5-27,295-339`; `doc/trust.md` (c) row `hwf`. (verified)

### P2 -- fixpoint eta happens after erasure, not before

**Reference.** MetaRocq never eta-expands lambda-box. `EEtaExpandedFix.expanded` (`EEtaExpandedFix.v:33-70`) is a
precondition read on the erased program, and it holds because the expansion happens before erasure, on the Template
program, by `EtaExpand.eta_expand_program` whose fixpoint arm is `eta_fixpoint`. Erasure inherits expandedness from an
already-expanded source, and no lambda-box-level relation between a fixpoint and its wrapper appears.
**Ours.** Lean has no source-level expansion to inherit from -- recursive definitions become `.fix` at registration,
inside the eraser -- so the expansion is on the lambda-box side and a relation must span the two shapes.
`Erasure.visitMutual` registers `Erasure.etaExpandFix defs j`, and `Lower.fixEta` (`Lower.lean:441-450`) relates the
member's specification body to `.lambda n (.app (.fix defs j) (.bvar 0))`, its premises those of `Lower.fixBody`
verbatim. `LBWfPeregrine.expandedFix` (`Output.lean:322`) concludes `LBExpandedTFix` (`:292`), all three term-level
conjuncts of `expanded_tFix` (`EEtaExpandedFix.v:46-54`): the spine (`LBExpandedFix`, `:235`), the lambda-headed member
bodies (`FixLambda`, `:176`) and the applied self-references (`LBFixSelfApplied`, `:283`).
**Nature.** FORCED-ERASER. **Reason.** Where the expansion can happen is fixed by where recursion is introduced.
**Consequence.** `Lower` gains an arm and a second image at a block member's body, so the relation is non-deterministic
there; the target is a closed fixed shape carrying no supplied arguments and no sub-image under the binder, which is why
the inversion kit is unaffected. The payoff is that the capstone concludes the whole precondition
`guarded_to_unguarded_fix` reads, with no separate weaker predicate beside it.
**Evidence.** `Lower.lean:434-450`; `Output.lean:230-293,321-322`; `doc/rework/10-MERGE-FIXES.md` sections 4.1-4.7. (verified)

### P3 -- the downstream passes are inherited, not modelled

**Reference.** [HAB] Spec 24-25 and Sec 6.5-6.6 give the thirteen-phase pipeline: `guarded_to_unguarded_fix`,
`remove_params`, `constructors_as_blocks`, `inline_projections`, `optimize_prop_discr` and the rest, each a verified
`Transform.t` with declared pre- and post-conditions.
**Ours.** Nothing downstream of lambda-box is redone. Both constructor regimes are modelled in `WcbvEval` and the
theorem is at applied form, which is what the eraser emits; The entry invariants `remove_params_optimization` consumes
are `etaCtorsEnv` and `etaCtorsTm` (`Output.lean:325-332`), which `peregrine validate` itself omits.
**Nature.** DESIGN. **Reason.** [HAB] Sec 6.5-6.6 verifies everything from lambda-box onward, so the Lean eraser only
has to land in lambda-box satisfying the pipeline's entry preconditions.
**Consequence.** The theorem's reach ends at the emitted program. `doc/trust.md` (d) records the two caveats:
peregrine's `run_untyped_transforms` precondition obligation is `Admitted`, and `validate` checks no expandedness, so
`LBWfPeregrine` is stronger than what the tool checks and weaker than what the pipeline's own proofs assume.
**Evidence.** `Semantics/Flags.lean:42-57`; `Output.lean:5-27,325-332`; `doc/trust.md` (d). (verified)

### P4 -- the prop-discriminee pass, stated without well-formedness premises

**Reference.** `remove_match_on_box_correct` (`EOptimizePropDiscr.v`) takes `wf_glob Sigma`, `closed_env Sigma`, `eval
fl Sigma t v` and `closed t`, concluding at `disable_prop_cases fl`.
**Ours.** `LBOptimize_correct` (`Optimize.lean:785-786`): `EvalProp Gamma t v -> Eval (LBOptimize_env Gamma) (LBOptimize
Gamma t) (LBOptimize Gamma v)`, from `propBlockFlags` to `blockFlags` -- the same flag discharge, with no `wf` or
`closed` premise.
**Nature.** DESIGN. **Reason.** The proof is a direct induction on the evaluation derivation, each arm rebuilding its
own rule at the optimised environment; nothing it does needs a global closedness fact.
**Consequence.** The pass is proved and unreached from the capstone's path: `LBOptimize` runs at block form while the
erasure emits applied form. `LBOptimize_correct_hyps_satisfiable` and `LBOptimize_correct_fires`
(`Optimize.lean:924,941`) show it is non-vacuous.
**Evidence.** `Optimize.lean:785-786,918-947`. (verified)

### P5 -- a printability clause with no reference counterpart

**Reference.** none; `EWellformed.wellformed` has no condition on binder names, and MetaRocq's printer is outside the
theorem.
**Ours.** `LBWfPeregrine.printableNames` (`Output.lean:334`) over `PrintableBinderName` (`:186-188`): a named binder
contains neither a quote nor a backslash.
**Nature.** FORCED-ERASER. **Reason.** `Printing.lean`'s `quote_atom` wraps a name in quotes and escapes nothing, and
peregrine's `Deserialize_ident` accepts any string atom. The alphanumeric class of `Basic.cleanIdent` is a condition on
kername identifiers, which `toKername` establishes by construction; on a binder name it is false, the eraser emitting
one hygienic name at G2-G4 and thirty-four at G7-G8.
**Consequence.** Restriction N10 keeps the printer and the grammar themselves outside the theorem.
**Evidence.** `Output.lean:179-193,333-334`; `doc/coverage.md`; `doc/trust.md` (c), (d) N10. (verified)

### M1, M2 -- a conditional refinement in place of a verified function

**Reference.** `erase` is a Rocq function, and `erases_erase` (`ErasureFunction.v:1228-1230`) is unconditional: for
every `wt : welltyped Sigma Gamma t`, `erases Sigma Gamma t (erase X_type X Gamma t wt)`, by one well-founded induction
over the whole source syntax under an abstractly threaded `NormalizationIn`.
**Ours.** `visitExpr_refines_erasesLB` (`VisitExprRefines.lean:190-219`) concludes `VisitExprRefinesLB env Us tbl cfg
gw`, unfolded at `:254-264`: given `TrExprS`, `Supported env tbl e`, `ctx.fixvars = none`, a successful run
`Erasure.visitExpr e s ctx cctx ref w = .ok (t, s') w'`, `BridgeInv`, and any `Gammaspec` with `SpecEnv env tbl.body?
tbl.levels? s' Gammaspec`, the output satisfies `ErasesLB env Us Gammaspec Delta e t` together with `RunConcl s s'` and
generator monotonicity. It comes from one eighteen-motive `partial_fixpoint` induction (`:30-56`) whose steps are
explicit hypotheses, under `ErasureSpec`, `SourceTableAdequate`, `ConfigPinned` and `CompilerBodies`.
**Nature.** FORCED-ERASER. **Reason.** `Erasure.visitExpr` is a partial, monadic computation over `EraseM`: stateful
name generation, a mutable registry, external oracle and `Meta`/`Core` calls, and panic sites. It terminates through
Lean's `partial_fixpoint` admissibility machinery, not through a normalisation witness. `Supported` takes the structural
place `NormalizationIn` holds, and is syntactic and decidable precisely because nothing plays that role here.
**Consequence.** The refinement is conditional on a fragment predicate, a run-state invariant and a caller-supplied
specification environment, and the conclusion factors through `ErasesLB` rather than landing in `Erases`. `Supported`'s
error constructors (`Supported.lean:37-60`) make the coverage holes readable off the predicate: sparse `casesOn`,
matcher applications surviving inlining, eta-contracted minors, string literals, machine `Nat`, `Quot` primitives,
IO-like primitives.
**Evidence.** `VisitExprRefines.lean:1-56,190-282`; `Supported.lean:6-30,37-60`. (verified)

### M3, M4 -- the registry invariant, and `hbridge` as an open item

**Reference.** `erase_global_deps` computes the dependency-closed erased environment by a pure structural fold over a
finite `global_env`, so `erase_global_erases_deps` (`ErasureFunctionProperties.v:172-177`) is proved by the same
induction `erases_erase` walks, from `includes_deps Sigma Sigma' (term_global_deps et)`.
**Ours.** `ErasureBridge` (`Capstone.lean:111-119`) carries `erasesEnv : ErasesEnv env bo lp Gammaspec t0` and `lowerEnv
: LowerEnv Gammaspec Gamma`, and is the binder `hbridge` of `shipping_erase_correct_firstorder` (`:209`).
`bridgeEnv_of_regContent` (`:161-174`) composes the binder's payload out of `RegAcc`, `RegKeyed`, `ErasuresDeclared` at the
prepared term, `htab` and `hlvl`; it is proved, has no consumer, and is not on the capstone's proof path.
`regInv_registerInd_run` (`VisitExprRefines/Step/Passes.lean:1940`) and `regInv_recConst_step`
(`ColdStartShape.lean:1401`) preserve `RegAcc` across one block registration and one recursive-constant registration.
**Nature.** OPEN. **Reason.** The environment is accumulated incrementally across many mutually recursive,
side-effecting calls, so the coherence fact needs a run-level invariant threaded through the whole call graph rather
than falling out of one fold.
**Consequence.** The capstone's environment conjuncts hold under one binder no theorem inhabits. The chain across a whole
run is the accumulator bundle (`VisitExprRefines/MotivesAcc.lean`): seventeen of its eighteen steps are proved,
`StepAcc6` (`visitMutual`'s step) is open, and `AccGrows` has no producer. `doc/rework/07-STATUS.md` section 4 specifies
what `StepAcc6` needs; five of the proved steps rest on `AccAsks.upstream` and so on R4's vacuity.
**Evidence.** `Capstone.lean:103-174,190-233`; `VisitExprRefines/MotivesAcc.lean:78,354,438`; `doc/rework/07-STATUS.md`
section 4; `doc/trust.md` (c) row `hbridge`. (verified)

### M5 -- `ErasureSpec` as the analogue of trusting the quoting layer

**Reference.** MetaRocq's PCUIC-level proofs start from an already-quoted term and end at a Rocq function. Neither
Template-Rocq's quoting nor Rocq's program extraction is formalised inside `erasure/theories` or `pcuic/theories`; they
are the trusted core, outside the development.
**Ours.** `ErasureSpec lenv env Us gw` (`ErasureSpec.lean:436-484`), seven fields: `env_connect`, `lookup_adequate`,
`fresh_names`, `oracle_refl`, `decl_adequate`, `prim_monotone`, `block_adequate`. Each names a `Lean.*` primitive or the
`lenv`-to-`env` connection, so each is a fact about an object no term denotes. The capstone takes it as `P : forall Us,
ErasureSpec lenv env Us gw`, at every level scope.
**Nature.** DESIGN. **Reason.** A proof about an abstract syntax cannot certify from inside that the concrete elaborator
producing terms of that syntax is faithful. The choice is to make the gap a `Prop`-typed structure appearing in every
statement that depends on it.
**Consequence.** `decl_adequate` is kept in an amended shape with the obstruction named:
`ErasureSpec.decl_adequate_of_kernelFind` proves the statement from `env_connect` alone for the kernel environment's own
lookup, and what it cannot cross is `Lean.Environment.find?` against `Lean.Kernel.Environment.find?`.
**Evidence.** `ErasureSpec.lean:8-30,436-484`; `Capstone.lean:196`; `doc/trust.md` (b). (verified)

### M6 -- `EraserAsks`, the preparation passes and the oracle's other arms

**Reference.** none. MetaRocq's erasure function has no preprocessing stage; the term it receives is the one the kernel
typed.
**Ours.** `EraserAsks lenv env gw` (`ErasureSpec.lean:668-720`), four fields: `passes_monotone`, `passes_sound`,
`oracle_false_refl`, `kernel_ind_head_true`. `passes_sound` asks that each of `Erasure.prepare_erasure`'s passes
preserves the source evaluation of the subject under an arbitrary application spine, the spine quantified because the
capstone reads its observable at `mkApps e args` while a pass is a whole-tree `Lean.Core.transform` walk.
**Nature.** FORCED-ERASER. **Reason.** `Erasure.prepare_erasure` runs `Erasure.replaceUnsafeRecNames`,
`Lean.Compiler.LCNF.macroInline` and `Lean.Compiler.LCNF.inlineMatchers` before `visitExpr` sees the term. These are
ordinary Lean definitions with an owner, which is why the four fields are class C rather than class D.
**Consequence.** The capstone's syntactic conjuncts read the prepared term `pe` while the observable reads the subject
`e`, and the two cannot be identified -- `macroInline` replaces a constant by its body. `prepare_sound` is proved from
`passes_sound`, and `hprep` pins `pe = e` per rung, checked by `lake exe reify --prepared`, green at all eight rung
subjects.
**Evidence.** `ErasureSpec.lean:16-24,668-720`; `Capstone.lean:17-23,206`; `doc/trust.md` (b) row `hprep`, (c)
rows `E.passes_*`. (verified)

### U1 -- the upstream asks as one premise

**Reference.** PCUIC's inversion and injectivity lemmas are theorems of the development.
**Ours.** `UpstreamAsks env` (`Upstream.lean:64-106`), four fields packaging three asks: `constsOrigin` (ask 2's
uniqueness corollaries), `constOriginExcludes` (ask 2's exclusion conjunct, refuted -- R4), `mkAppsInv` (ask 9, spine
typing inversion with `OrderedStrong` explicit), `indSpineInj` (ask 10, two definitionally equal spines headed by
inductively declared formers have the same head). Ask 2's classification conjunct is the theorem `consts_classified`,
off `VEnv.WF'.consts_origin`; ask 6 is cited directly as `Lean4Lean.VEnv.IsDefEqU.const_arity_inv` (U2).
**Nature.** FORCED-LEAN4LEAN. **Reason.** Editing the pinned fork is outside this repository's work.
**Consequence.** `erases_correct`, `not_erasable_of_informative`, `indSpine_not_prop`, `elim_major`, `ctor_saturated`,
`CasesOnShape.agree`, `fOFields_of_asks`, `firstorder_erases_deterministic`, `firstorder_no_box` and
`erasure_bridge_of_run` all take it, so every rung carries it. A pin bump discharges `mkAppsInv` and `indSpineInj` with
no change to any consumer's statement shape; the two ask-2 fields wait on R4's restatement, not on the fork.
**Evidence.** `Upstream.lean:1-106`; `Origin.lean:262`; `doc/trust.md` (c) row `UpstreamAsks env`. (verified)

### U2 -- what the pin leaves open

**Reference.** PCUIC's metatheory library is complete for the erasure proof's needs.
**Ours.** Six inherited `sorryAx` roots on the proof path: five reached through `TrExprS.uniq` and `IsDefEq.uniqU`
(`VEnv.IsDefEqU.sort_inv`, `forallE_inv_stratified`, `sort_forallE_inv`, `weakN_iff`, `VEnv.NormalEq.parRed`), and
`VEnv.IsDefEqU.const_arity_inv` (`Theory/Typing/Injectivity.lean:45`), cited directly by `not_erasable_of_informative`,
`indSpine_ne_forallE` and `FirstOrderInd.notSortNotPi`; plus the fork-authored `VEnv.WF.patsStrong`. Two further
clusters bound what a rung can inhabit: `addDecl.WF`'s `inductDecl` case and the executable checker's
`TrProj.weak'_inv`/`TrProj.uniq`, both `sorry` at the pin.
**Nature.** FORCED-LEAN4LEAN. **Reason.** The pin.
**Consequence.** The projection exposure is inhabitation rather than axioms: `step_proj` consumes a `TrProj` from
`TrExprS.proj`'s own premise and never builds one, so a projection in a real program has a `TrExprS` derivation only
through the open `TrProj` lemmas. `hcb : CompilerBodies` stays a binder at G2-G8 for the same reason -- ten of G7's
thirty tabled bodies carry an `Expr.proj` -- and `hfo` and `ErasesEnv.tabled`'s exclusion both wait on ask 4.
**Evidence.** `doc/trust.md` (a1), (a2), (a4), (c) rows `hcb`, `hfo`; `test/lean4lean-sorries.expected`. (verified)

### S1 -- the configuration and the stated restrictions

**Reference.** [JACM] Sec 7 covers erasure for PCUIC with no configuration parameter.
**Ours.** `ConfigPinned cfg` (`ErasureSpec.lean:45-47`): `csimp = false`, `extern = .preferLogical`, `nat = .peano`,
`remove_irrel_constr_args = false`, `auto_inline_typeclass_dispatch = false`. Beside it, `doc/trust.md` (d) lists N1-N18
and four consumer facts as class-E rows.
**Nature.** DESIGN. **Reason.** Each shipping feature outside the theorem is stated as a hypothesis rather than omitted
silently. `csimp = false` is the sharpest: the shipping default is `true`, and `csimp` silently substitutes
tail-recursive variants.
**Consequence.** A reader can tell exactly which shipping configuration the theorem describes, and it is not the default
one.
**Evidence.** `ErasureSpec.lean:40-47`; `doc/trust.md` (d). (verified)

### S2 -- the measured domain

**Reference.** `erase_correct_firstorder` is stated for any `t : mkApps (tInd i u) args` in any well-formed environment.
**Ours.** `shipping_erase_correct_firstorder` (`Capstone.lean:190-233`) is likewise universally quantified over `lenv`,
`env`, `tbl`, `e` and the rest; eight rungs, `green_G1` through `green_G8` (`Green.lean`), instantiate it over five spike
constants and Arith's `arithClosed` and `benchArith`.
**Nature.** DESIGN. **Reason.** A rung is where every decidable hypothesis is discharged by computation --
`supportedB_sound`, `lbWfPeregrine_of_check` for `hwf`, `spike_configPinned` for `hcfg`.
**Consequence.** A green rung shows that checked terms meet the stated interface, and nothing more: every rung binds
`UpstreamAsks env` beside `hfo`, `SpikeNatFacts` or a tabled block through `P`/`htbl`, each combination is `False`
(R4), so no environment satisfies a rung's hypotheses. `hev`, `hvwt`, `hty` and `hfo` stay bound and `lenv`/`env`
universally quantified. Four of the five corpus programs -- Sieve, BinaryTrees, Quicksort, Fannkuch -- sit outside the
rungs.
**Evidence.** `Capstone.lean:190-233`; `Green.lean`; `doc/coverage.md`; `doc/rework/07-STATUS.md` sections 1, 4.
(verified)

### S3 -- the `max`-free level fragment

**Reference.** none; `erases_subst_instance_decl` carries `consistent_instance_ext` and no syntactic restriction on the
levels.
**Ours.** `NoMaxLevels`, a clause of `TableSafe` (`Supported.lean:612`) and a conjunct of `ErasesEnv.defns`
(`ErasesEnv.lean:94-97`) beside the body's translation, under the clause's reachability gate. The table-wide form is
`TabledLevels` (`ErasesCorrect/Steps.lean:1102`), produced by `tabledLevels_of_table` (`:1109`) and taken as `hlvl` by
`bridgeEnv_of_regInv` and `bridgeEnv_of_regContent`.
**Nature.** DESIGN. **Reason.** R8: the positional level substitution `Erases.instL` runs on does not commute with
`Level.max`.
**Consequence.** One more scope restriction, decidable on a concrete table and measured satisfied at every tabled body
of all eight rungs. `TabledLevels` asks for a translation of every tabled body, reached or not, and so overlaps `hcb :
CompilerBodies`; `ErasesEnv.defns` reads it only at reached constants, as the reference gates its own typing premise.
**Evidence.** `Supported.lean:600-615`; `ErasesEnv.lean:87-110`; `ErasesCorrect/Steps.lean:1100-1120`. (verified)

## 4. What is aligned

These follow the reference exactly, name for name, so the divergence list above reads as complete
relative to the reference's own structure.

**Target calculus.** `LBTerm.box`/`tBox`, `lambda`/`tLambda`, `letIn`/`tLetIn`, `app`/`tApp`, `const`/`tConst`,
`construct`/`tConstruct` (block argument list included), `case`/`tCase` (an inductive identifier with a parameter count,
a discriminee, a list of binder-list-and-body pairs), `proj`/`tProj`, `fix`/`tFix` (`Basic.lean:90-106` against
`EAst.v:29-45`); `Kername`/`kername`, `ModPath`/`modpath` (`Basic.lean:8-42`); `OneInductiveBody`/`one_inductive_body`
field for field, likewise `MutualInductiveBody`/`mutual_inductive_body` and `ConstantBody`/`constant_body`
(`Basic.lean:144-194` against `EAst.v:185-208`), `AllowedEliminations`/`allowed_eliminations` carried for format
faithfulness.

**Target semantics.** `WcbvFlags`/`WcbvFlags`, three booleans with the same names (`Semantics/Flags.lean:36-40` against
`EWcbvEval.v:34`), and the points `eraseFlags`/`opt_wcbv_flags` and `entryFlags`/`default_wcbv_flags`. `WcbvEval`/`eval`
rule for rule: `box`/`lam`/`fvar`/`prim`/`fix_atom` decompose `eval_atom`; then `beta`, `app_box`/`eval_box` (which
evaluates the argument and discards it), `zeta`, `delta`, `construct`/`eval_construct_block`, `construct_atom`,
`construct_app`/`eval_construct`, `iota`, `iota_block`, `iota_sing`, `proj`, `proj_block`, `proj_prop`,
`fix_guarded`/`eval_fix`, `fix_stuck`/`eval_fix_value`, `fix_unguarded`/`eval_fix'`, `app_cong`
(`Semantics/Eval.lean:26-48` states the table; the rules are at `:79-245`). Both constructor regimes are modelled, kept
mutually exclusive by the same flag, and `iota_red`'s arithmetic is transcribed.
`eval_deterministic`/`eval_deterministic` (`Semantics/Metatheory.lean:143`).

**Erasure relation.** `Erases.box`/`erases_box`, the only non-deterministic rule on both sides and the only rule
reachable from a sort or a Pi; `Erases.app`/`erases_tApp`, a plain congruence; `Erases.lam`/`erases_tLambda` and
`Erases.letE`/`erases_tLetIn`, extending the local context exactly as `TrExprS.lam` and `TrExprS.letE` do, with zeta
enabled on both sides and `Expr.letE`'s non-dependence flag ignored, matching `tLetIn`'s carrying no such flag. Universe
levels are dropped at `Erases.const` as `erases_tConst` drops `u`. The image of a term is not unique, and the value's
erasure is existentially quantified in the conclusion -- the reference's own reason for having a relation at all.

**Environment relation.** `ErasesEnv.defns` reads each tabled body at the declaration's own level parameters, which is
where `erases_constant_body` reads it (`Extract.v:264-268`, applied at `cst_universes cb` by `erases_global_cnst` at
`:287` and by `erases_deps_tConst` at `:324-331`); `SourceTable.levels?` is that column. `ErasesEnv.axioms` matches
`erases_constant_body`'s `None, None => True` arm. `ErasesEnv.blocks` carries the `declared_inductive
Sigma`/`declared_inductive Sigma'` pair of `erases_deps_tConstruct`/`_tCase`/`_tProj`, with `IndBodyOf` in the role of
`erases_mutual_inductive_body`'s arity data. `ErasesEnv.keys` is `wf_glob`'s `fresh_global` half. The typing premise of
`erases_subst_instance_decl` rides on `defns` under the same reachability gate the reference spends it under
(`ErasureCorrectness.v:176`).

**The simulation and the observable.** The proof structure is the reference's: induction on the evaluation derivation,
inversion on the erasure relation at each step, and a box-versus-structural split, the arm files `Delta.lean`,
`Iota.lean` and `Proj.lean` matching PCUIC's delta, iota and projection case split. The two-step method -- a
non-deterministic relation extending the function, then a bridge from the function's graph to it -- is [L]'s and
[JACM]'s, and is why the `visitExpr`-to-`ErasesLB` bridge exists. The first-order specialisation keeps the reference's
shape: a source value at an inductive spine, an answer reproduced by the emitted program under lambda-box's own
semantics, box-free, under a first-order side condition on the answer's inductive. Values are `[JACM]` Fig. 12's:
`SEval.ctorVal`/`value_head_cstr` and `SEval.indVal`/`value_head_ind`, `harity` transcribing `nargs <= cstr_arity`, and
a body-less plain constant has no value at all, which is how PCUIC treats an axiom.

**Naming.** `PrimTag`/`prim_tag`, `RecursivityKind`/`recursivity_kind`, `ConstructorBody`/`constructor_body`
(`name`/`cstr_name`, `nargs`/`cstr_nargs`), `FixDef`/`def` (`name`/`dname`, `body`/`dbody`, `principalArgIdx`/`rarg`),
`ProjectionInfo`/`projection` (`indType`/`proj_ind`, `paramCount`/`proj_npars`, `fieldIdx`/`proj_arg`),
`GlobalDecl`/`global_decl`, `GlobalDeclarations`/`global_declarations`.
