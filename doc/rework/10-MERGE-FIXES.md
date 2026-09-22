# 10 — The `dev/fix` merge, and the repairs it owes

`dev/fix` carried ten fixes to the shipping eraser, their follow-ups and `F-FUEL`; the merge is
`2036c85`. The shipping closure builds — `LeanToLambdaBox/Erasure.lean` itself compiled clean in
the merge run — and the verification does not: `lake build` stops at `LeanToLambdaBox.Lower` and
`LeanToLambdaBox.ErasureRun`, leaving 27 modules unscheduled
(`scratch/round7/merge-errors.md`, log `scratch/round7/merge.build.out`).

This document says, fix by fix, what changed in the shipping functions, which verification
declarations mirror them and what the repair is (§2); states the three rules the repairs share
(§3); gives the F-ETA design in full, which is the one fix that asks for new theory (§4); lists
what must be regenerated (§5) and what joins CI (§6); and schedules the work as eight clusters in
dependency order (§7).

Every signature §4 and §2.1 quote elaborates at this toolchain as a `sorry`-stub:
`scratch/round7/w8_sigs.lean`, run with `lake env lean` against the tree with the two missing-field
literals of M1 supplied (`scratch/round7/w8_sigs.out`, eight `declaration uses 'sorry'` warnings
and no error). The shipping diff this document is written against is
`git diff e7894de dev/fix -- LeanToLambdaBox/{Basic,Erasure,Relevance,Printing}.lean`: 391
insertions over three files; `Printing.lean` is untouched.

**The rule the repairs run under.** The four shipping files are not edited on this branch. Where a
proof shows a fix wrong, the finding is reported in `doc/rework/03-DEV-FIX.md` and the proof is
stated around the code as it is. No statement acquires a hypothesis whose only content is that the
counterexample does not occur; §2.6 is where that rule bites and §2.6 says what is done instead.

## 1. What the merge broke, and why the list is short

Two modules fail, for two reasons.

`LeanToLambdaBox/Lower.lean:2102` — `Fields missing: propositional`. `F-PROP` removed
`OneInductiveBody.propositional`'s `false` default (`Basic.lean:166`), so every structure literal
must supply it. Five literals in the tree do not: `Lower.lean:2102` (`LowerElimFixture.mib`),
`ErasesEnv.lean:334` (`demoMib`), `ErasesCorrect/Proj.lean:129` (`LowerProjFixture.mib`),
`SpecEnv.lean:211` and `ErasureRun.lean:1898` (the reconstructed body inside
`run_register_inductive_cold_ok`). Only the first is reported, because the other four sit in
modules lake never scheduled.

`LeanToLambdaBox/ErasureRun.lean:1735`, `:1738`, `:1814` — `rewrite` cannot find
`modify ?g ?s ?ctx ?cctx ?ref ?w`. `F-KERNAME` put `checkKernameFresh name kn` between
`addAxiom`'s `let kn := …` and its `modify` (`Erasure.lean:240-243`), and put
`checkIndKernameFresh` into `register_inductive` (`Erasure.lean:322`), whose `modify` now also
writes `indBlocks`. The later failures in that module — `:2053`, the `split` internal errors at
`:2870`, the application mismatches at `:2871`/`:2872`, the three heartbeat timeouts — are the
same root cause reaching `run_register_inductive_cold_entries` and `run_visitMutual_ok`, whose
`split` runs on `visitMutual`'s now-larger `.none` arm.

Nothing else is reported because nothing else was built. §2 works from the shipping diff, not from
the error list.

## 2. The ten fixes

| id | shipping functions | mirroring declarations | repair | cluster |
|---|---|---|---|---|
| F-PROP | `register_inductive` (`Erasure.lean:316`), `OneInductiveBody.propositional` (`Basic.lean:166`) | `IndBodyOf` (`Lower.lean:52`), `isPropositionalInductive` (`Semantics/Env.lean:21`), five literals, five comments | the flag equation replaces the constant `false` | M1, M5 |
| F-ACC | `visitCases`'s refusal (`Erasure.lean:1106-1115`) | `step_visitCases` (`Step/Passes.lean:816`) | a new throw branch, discharged by the toolkit | M7 |
| F-SPARSE | `visitCases` (`Erasure.lean:1043-1170`) | `visitCasesBody` (`Motives.lean:561`), `step_visitCases`, `CasesInfoAgreesK` (`ErasureSpec.lean:87`) | two class-**D** clauses, then the step | M4, M7 |
| F-UNSAFEREC | `visitMutual`'s `Nodup` guard (`Erasure.lean:1263-1264`) | `EraserAsks.block_keys_distinct` (`ErasureSpec.lean:385-395`), `blockKeyed_install` (`Step/Env.lean:467`) | the field is **deleted**; the run supplies the fact | M2, M4, M7 |
| F-KERNAME | `checkKernameFresh`, `checkIndKernameFresh`, `ErasureState.indBlocks` | `run_addAxiom_ok` (`ErasureRun.lean:1719`), `run_register_inductive_*`, `ConstExt` | the guards are stepped through; freshness becomes a run conclusion | M2 |
| F-DEPTH | `isArityCheck` (`Relevance.lean:49-50`) | `EraserAsks.kernel_ind_head_true` (`ErasureSpec.lean:374-384`) | the field stands, its docstring is corrected — §2.6 | M4 |
| F-ETA2 | `visitCtorEtaGo`, `visitCasesEtaGo`, `withEtaPrefixLets` | `visitCtorEtaGoBody`/`visitCasesEtaGoBody` (`Motives.lean:530`, `:549`), `step_visitCtorEtaGo`/`step_visitCasesEtaGo` | the mirrors are re-copied; the loops stay dead in the fragment | M7 |
| F-QUOT | `visitMutual`'s `.none` arm, `addRealizer`, `quotRealizer` | `run_visitMutual_decomp` (`ColdStartRun.lean:376`), `RunClosed.ax`, `RegInvShape'.addAxiom` | a fourth and fifth registering exit — §3.2 | M2, M6 |
| F-EQREC | the same arm, `recursorRealizer` (`Erasure.lean:409`) | the same, plus `NoBodylessRefs` (`Output.lean:862`) | the same | M2, M6 |
| F-ETA | `etaExpandFix` (`Erasure.lean:478`), `visitMutual`'s registration loop | `LowerEnv.defs` (`ErasesEnv.lean:231`), `Lower`, `ErasesCorrect/Delta.lean:182-192`, nine `ColdStartShape` sites, `LBWfPeregrine` | one new `Lower` arm, and the expanded-fixpoint clause — §4 | M1, M3, M5, M6, M8 |

`F-FUEL` is already merged (`9363fb9`) and mirrored by nothing: `isArityCheck.loop.WF` is stated
`∀ fuel` (`RelevanceCheck.lean:104-137`), and F-DEPTH's constant fuel is a different `Nat`
expression in the same single-call shape, so no proof moves.

### 2.1 F-PROP — the emitted flag, as MetaRocq's equation

*What changed.* `register_inductive` sets `propositional := isPropositionalArity inf.type`
(`Erasure.lean:368`), `isPropositionalArity` being `destArity` then `Sort.is_propositional`
(`arityResultSort`, `Erasure.lean:281`; MetaRocq `ErasureFunction.v:1325-1338`). The default is
gone, so the field cannot be forgotten. `kelim` is untouched and its docstring now says why
(C-refute C9).

*What mirrors it.* `IndBodyOf` (`Lower.lean:52`) reads

```lean
  mib.npars = np ∧ ∃ oib, mib.bodies[iid.idx]? = some oib ∧
    oib.propositional = false ∧ oib.ctors.map (·.nargs) = nfs
```

and is spent by `ErasesEnv.blocks` (`ErasesEnv.lean:60-65`), `IndCovered.block`
(`ErasesEnv.lean:147`), `ElimDecl` (`Lower.lean:62`) and, through `LowerEnv.inds`, by
`ErasesCorrect/Iota.lean:363` and `ErasesCorrect/Proj.lean:94`, each of which needs
`isPropositionalInductive Γ iid = false` for `WcbvEval.iota`/`.proj`
(`Semantics/Eval.lean:147`, `:183`).

*The repair.* `oib.propositional = false` is no longer a fact about emitted output, so it stops
being an axiom of the shape and becomes the equation MetaRocq states.
`erases_mutual_inductive_body` (`../metarocq/erasure/theories/Extract.v:276`) has
`ind_propositional = isPropositionalArity ind_type`, an equality in both directions; the λ□ side
gets the same:

```lean
/-- `I` is propositional: the declared arity's result sort is `Prop` at every valuation. The
complement of `InformativeInd`'s `VLevel.IsNeverZero`, and the model-side reading of
`Erasure.isPropositionalArity`; MetaRocq's `isPropositionalArity` (`Extract.v:276`). -/
def PropositionalInd (env : VEnv) (I : Name) : Prop :=
  ∃ ci, env.constants I = some ci ∧ ∃ l, vResultSort ci.type = some l ∧ ∀ ls, l.eval ls = 0

def IndBodyOf (env : VEnv) (I : Name) (iid : InductiveId) (np : Nat) (nfs : List Nat)
    (mib : MutualInductiveBody) : Prop :=
  mib.npars = np ∧ ∃ oib, mib.bodies[iid.idx]? = some oib ∧
    (oib.propositional = true ↔ PropositionalInd env I) ∧ oib.ctors.map (·.nargs) = nfs
```

`vResultSort` (`Erasability.lean:240`) is `arityResultSort`'s mirror arm for arm, so the two sides
of the equation are the same walk. The `= false` the ι and projection arms read is then derived,
not assumed:

```lean
theorem propositional_false_of_informative {env : VEnv} {I : Name} … (h : IndBodyOf env I iid np nfs mib)
    (hinf : InformativeInd env I) : ∃ oib, mib.bodies[iid.idx]? = some oib ∧ oib.propositional = false
```

`InformativeInd` is `∃ l, vResultSort ci.type = some l ∧ l.IsNeverZero` (`Erasability.lean:281`),
and a level that is never zero is not zero at every valuation, so the two are exclusive — C-refute
C10's sound implication, now spent where it is sound rather than asserted over a quantifier it does
not cover. `Erases.proj` carries `hinf` (`Erases.lean:267`) and `SEval.iota` carries its own, so
both consumers have the premise in hand.

*Which inductives a run registers* (C-refute C10). The old argument — "every inductive `supportedB`
admits keeps `propositional = false`" — quantifies over the wrong set: `informativeB` is consulted
at elimination and projection sites only (`Supported.lean:321`, `:355`), while
`register_inductive` is also reached from `visitConstructor`, from `visitProj` and now from
`recursorRealizer` (`Erasure.lean:410`, the `(indid, argmasks) ← register_inductive ind` inside
it). Under the equation the gap closes at the statement rather than in an argument: the registry
shape no longer claims anything about which inductives are registered, only that each registered
body's flag is the decision on that inductive's own arity, which `register_inductive` computes
unconditionally. The two comments that assert the old reading are restated:
`Semantics/Flags.lean:24-30` and `Supported.lean:66`, `:562` over the fragment,
`ElimBody.lean:87-89` and `Erasability.lean:280` over the elimination sites.

*The transfer.* The run establishes `oib.propositional = Erasure.isPropositionalArity inf.type`
(a computation — M2 carries it into `RegisteredBodyAt`, `ErasureRun.lean:1672`); the equation
needs `Erasure.isPropositionalArity iv.type = true ↔ PropositionalInd env I`. Derive it if
`TrConstant`'s Π-telescope translation makes `arityResultSort` and `vResultSort` commute; if the
`Us`-scope mismatch blocks that, state it as a sixth clause of `BlockAdequate`
(`ErasureSpec.lean:181`), class **D** for the reason `env_connect` is, and say so in
`doc/trust.md`. The derivation is attempted first and the outcome recorded, as `decl_adequate`'s
own amendment was.

*Files.* `Erasability.lean` (`PropositionalInd`, the exclusion lemma), `Lower.lean` (`IndBodyOf`,
`ElimDecl`, the fixture literal), `ErasesEnv.lean` (`blocks`, `IndCovered.block`, `demoMib`),
`ErasesCorrect/Iota.lean`, `ErasesCorrect/Proj.lean`, `SpecEnv.lean`, `ErasureRun.lean`,
`ErasureSpec.lean`, `Semantics/Flags.lean`, `ElimBody.lean`, `Supported.lean`.

### 2.2 F-ACC — a refusal, and nothing else

`visitCases` throws before emitting when the eliminated inductive's declared arity ends in `Prop`
and some constructor field is not a proof (`Erasure.lean:1106-1115`, using `firstNonProofField`,
`:301`). Nothing in `Erases`, `Lower`, `SEval` or the capstone changes: `Supported.propElimIntoData`
refuses strictly more (every non-informative inductive), so the guard enforces a subset of a
restriction the fragment already carries (C-refute C11). `visitProj` needs no twin and the
follow-up commit `341a996` records the check that establishes it.

The only repair is `step_visitCases`: two new `throwError` branches on the path, killed by
`run_throwError_ne_ok` under §3.1's rule. The `Meta.isProof` calls inside `firstNonProofField` run
under `liftMetaM`, so `run_liftMetaM_state` leaves the state alone and
`ErasureSpec.prim_monotone` bounds the generator.

### 2.3 F-SPARSE — `visitCases`, rebuilt

*What changed.* The inductive is read from `casesInfo.indName` instead of
`casesInfo.declName.getPrefix` (`Erasure.lean:1098`); `typeName` survives as the key of the
machine-`Nat`/`Int` arms alone and its comment says so (`:1045-1048`). Five `throwError`s replace
the `unreachable!`: a non-inductive `indName`, a machine-numeral discriminee under `nat = .machine`,
a side-condition elimination (`altsRange.lower ≠ discrPos + 1`), alternatives not one-to-one with
the constructors, more than one catch-all, a catch-all with a free de Bruijn index
(`LBTerm.hasLooseBVar`, `:133`) or one binding a non-proof hypothesis. The alternatives loop is
re-indexed: it walks `altIdx : Array (Option Nat)`, one slot per constructor in constructor order,
and fills an uncovered slot from the erased catch-all applied to `□` per hypothesis.

*What mirrors it.* `visitCasesBody` (`Motives.lean:561`), a copy of the shipping body with the
family's calls abstracted, and `step_visitCases` (`Step/Passes.lean:816`), whose proof walks that
body. The `bodyLe17` conjunct is `fix_step_le … Erasure.visitExpr.mutual._proof_1`, so the copy
must match the shipping body exactly or the cluster does not elaborate — which is the enforcement
mechanism for all four mirrored bodies, in place of a tool.

*The repair, in two parts.* The fragment is unchanged: `supportedHead` still refuses an
`isSparseCasesOn`/`isMatcherName` head, so on a supported run `altIdx` is total and `dflt` is
`none`. Making that a *proof* needs two facts about `Lean.CasesInfo` the specification bundle does
not yet state, both true of a plain `casesOn` by construction (`Lean/Meta/CasesInfo.lean:64-82`)
and both class **D** for the reason the other `getCasesInfo?` clauses are:

```lean
  /-- The information names the inductive the major premise is typed at. -/
  indName : ci.indName = iv.name
  /-- Every alternative slot is its constructor's, in constructor order: a plain `casesOn`
      builds each from `C (ctor …)`, never from the catch-all shape. -/
  altCtor : ∀ (j : Nat) (a : Lean.CasesAltInfo) (cn : Name),
    ci.altNumParams[j]? = some a → iv.ctors[j]? = some cn → ∃ nf, a = .ctor cn nf
```

as clauses of `CasesInfoAgreesK` (`ErasureSpec.lean:87`) with table-side twins on
`CasesInfoAgrees` (`Supported.lean:1084`) and a case added to `CasesInfoAgrees.of_pinned`
(`:1104`). From `altCtor`, `altIdx = (List.range I.ctors.length).map some` and the expansion path
is dead; `numAlts` then gives the loop's length as before. `numFields` is unchanged and still
reads `altNumFields`.

The catch-all expansion, the free-index check and the hypothesis check are therefore not covered —
they are refutation paths in the fragment — and `SupportError.sparseCasesOn` and the
`doc/coverage.md` row stand. C-refute C12's lift caveat is a shipping concern that the fix answers
with `hasLooseBVar`; the verification records it as the reason the branch is a refusal and not a
covered shape.

### 2.4 F-UNSAFEREC — `block_keys_distinct` retires

*What changed.* `visitMutual` throws unless `(fixvarnames.map toKername).Nodup`, before the
`withReader` that installs the fixvar map (`Erasure.lean:1263-1264`). `Kername` and `ModPath`
gained `DecidableEq` (`Basic.lean:12`, `:17`).

*What mirrors it.* `EraserAsks.block_keys_distinct` (`ErasureSpec.lean:385-395`) is an
**unconditional** claim about `Lean.Compiler.LCNF.getDeclInfo?` — for every `n`, the mapped keys
are `Nodup` — and it is false (the finding's `mutual unsafe def u / u._unsafe_rec`). It has exactly
one consumer: `blockKeyed_install` (`Step/Env.lean:467`), which spends it at `:481` to build
`BlockKeyed`'s third conjunct.

*The repair* (C-refute C5). The guard does not make the unconditional claim true; it makes the run
fail on a violating block. So distinctness becomes a conclusion of a successful run and the field
goes:

* M2 adds, beside `run_rec_exit_ok` (`ErasureRun.lean:2729`) and its world-indexed twin
  (`:3046`), the guard's reading —
  `run_rec_exit_nodup : … → ((ci.all.map Erasure.remove_unsafe_rec).map toKername).Nodup` —
  proved by stepping the `unless` with `run_throwError_ne_ok`, which is the whole proof.
* M4 deletes the field from `EraserAsks`, leaving four.
* M7 gives `blockKeyed_install` that `Nodup` as a hypothesis in the field's place. The shape is a
  drop-in: the existing proof already goes through `List.Pairwise.of_map toKername`, so the
  run-derived fact is *literally* what the field supplied. `run_visitMutual_registers`
  (`Step/Env.lean:329`) and `run_rec_exit_reg` (`:233`) thread it, and `step6` (`:536`) loses the
  `E.block_keys_distinct` spend.

`Bridge.BlockKeyed`'s fourth conjunct, the key separation over tabled names, is untouched:
`toKername_not_injective` (`Step/Env.lean:742`) stays true, and `Supported.kernameSepB` still
decides the restriction — the guard makes the run *enforce* it rather than proving it general.

*Gate.* `grep -rn "block_keys_distinct" LeanToLambdaBox/` empty; `scripts/ledger.sh` unchanged (a
deleted hypothesis moves no `#print axioms` row); `07-STATUS.md` §1's class-**C** row lists four
`EraserAsks` fields.

### 2.5 F-KERNAME — guards on three registration points

*What changed.* `checkKernameFresh` (`Erasure.lean:221`) scans `ErasureState.constants` and the new
`ErasureState.indBlocks` (`:36`) and throws on a key already minted for a different name; it is
called from `addAxiom` (`:243`), from `addRealizer` (`:254`) and from `visitMutual`'s two
registration points (`:1243`, `:1275`). `checkIndKernameFresh` (`:233`) guards
`register_inductive`'s block key (`:322`), which `rootKername (String.join …)` mints and which is
no more injective than `toKername` is.

*What mirrors it.* Every run lemma that steps one of those functions: `run_addAxiom_ok`
(`ErasureRun.lean:1719`) — the three reported errors — `run_register_inductive_cold_ok` (`:1788`),
`run_register_inductive_cold_entries` (`:2015`), `run_nonrec_exit_ok`/`run_rec_exit_ok` and their
world-indexed twins, and through them `ConstExt`/`AxiomExt` (`:1536`, `:1543`) and
`registerIndState` (`:1666`), which must now also write `indBlocks`.

*The repair.* §3.1. Each guard is two `get`s and two `if let`s; on a `.ok` hypothesis both tests
failed, so the state is unchanged and the two `find?` results are `none`. The lemma to add once and
reuse is

```lean
theorem run_checkKernameFresh_ok {n : Name} {kn : Kername} … (hrun : checkKernameFresh n kn s ctx cctx ref w = .ok (u, s₁) w₁) :
    s₁ = s ∧ w₁ = w ∧
      (∀ m k, s.constants.get? m = some k → k = kn → m = n) ∧
      ∀ ms, (kn, ms) ∉ s.indBlocks
```

with `run_checkIndKernameFresh_ok` beside it. The state half restores every broken `rw [run_modify]`
by rewriting the guard away first; the freshness half is a *payoff* — `RegInvShape'.addAxiom`
(`ColdStartShape.lean:215`) takes `hfresh : ∀ q ∈ s.gdecls, q.1 ≠ toKername n` as a hypothesis, and
half of it now comes from the run. M6 takes the payoff where `ConstKeysCovered` already carries the
key discipline; it is not required for the build to go green, and the cluster brief says so.

### 2.6 F-DEPTH — the field stands, the docstring is corrected

*What changed.* `isArityCheck` fuels its loop from the constant `100000` instead of
`ty.approxDepth.toNat + 1` (`Relevance.lean:49-50`). The single `loop` call shape is preserved, so
`isArityCheck.loop.WF`/`isArityCheck.WF` (`RelevanceCheck.lean:104-137`), stated `∀ fuel`, hold
unchanged. No proof moves.

*The decision.* `EraserAsks.kernel_ind_head_true` (`ErasureSpec.lean:374-384`) **stays a field,
with its statement unchanged and its docstring corrected.** C-refute C2 rules out the guard the
earlier design proposed — "the reduced telescope is shorter than the cap" is a
counterexample-excluding side condition on a statement, which this project does not write — and
offers instead weakening the conclusion to the disjunction the code realises: the kernel run
answers `true`, or raises the fuel error and the verdict routes to `isErasableMeta`
(`Erasure.lean:206-211`). That route does not work, and the reason is worth recording so it is not
re-proposed.

The field exists for one consumer, `EraserAsks.oracle_informative` (`ErasureSpec.lean:426-439`),
which contradicts it against `oracle_false_refl` ("a `false` verdict means the pure kernel run did
not answer `true`") to exclude an inductive-type head. Under the disjunction the contradiction
breaks in the `.error` arm, and closing that arm needs `isErasableMeta` to answer `true` at an
inductive head. `ErasureSpec.oracle_meta` is **soundness of a `true` verdict**, not completeness,
so it does not supply it; and F-DEPTH's own measurement is the refutation of the missing clause —
`isErasableMeta Bar = false` at the alias (`03-DEV-FIX.md`, F-DEPTH's measure). The restatement
would therefore trade one refuted field for a refuted field plus a new class-**D** clause about
unverified elaborator code. It is not taken.

*The docstring, as it must now read.* The two counterexamples this round demonstrated are gone: a
telescope of ≥ 256 binders decides inside the kernel, and so does a definitional alias whose
`approxDepth` is 0. What remains is what the constant fuel cannot bound — a *reduced* telescope
longer than the budget, and any other kernel error inside `isArityCheck` — so the field is still
not a theorem. The docstring drops "Refuted in general at a telescope of ≥ 256 binders", names the
residue, drops "plus a fuel that counts the reduced telescope" from the discharge plan (F-DEPTH
answered that with a constant) and keeps "three executable-shape lemmas lean4lean does not have".
`07-STATUS.md` §1's class-**C** row loses "(bounded by F-DEPTH)" and gains the residue;
`doc/trust.md`'s row follows.

### 2.7 F-ETA2 — four mirrored bodies, and the fragment unchanged

*What changed.* `visitCtorEtaGo` (`Erasure.lean:990`) and `visitCasesEtaGo` (`:957`) bind each
already-supplied argument that is neither a variable nor a `□` in a `let` *outside* the binders the
expansion opens, through `withEtaPrefixLets` (`:589`) and `etaArgIsValue` (`:576`); the eliminator
loop binds the discriminee only (follow-up `e347ed7`, the review's diverging-alternative
reproducer). `withEtaPrefixLets` sits beside the mutual block with its own
`@[partial_fixpoint_monotone]` lemma, so the family still has eighteen members and the
`partial_fixpoint` arity is unchanged.

*The repair.* `visitCtorEtaGoBody` (`Motives.lean:530`) and `visitCasesEtaGoBody` (`:549`) are
re-copied from the shipping bodies. `step_visitCtorEtaGo` (`Step/Passes.lean:791`) and
`step_visitCasesEtaGo` (`:776`) are one-liners on the saturated path — `rw [if_pos har]` — and stay
that way: the new code is in the `else` branch, which `CasesInfoAgrees.arity` and the constructor
arity already make dead. `N19` stands: a `let`-prefixed η-expansion has no `Lower` arm either, the
`ctorEta`/`elimEta` arms having been deleted at A21. The refuted sentence — that the constructor
half of N19 disappears once this row is repaired — must be deleted from all four copies C-refute C8
lists: `doc/coverage.md:79-81`, `01-DESIGN.md:1133`, `:3219` and `:440-444`.

### 2.8 F-QUOT and F-EQREC — two new registering exits

*What changed.* `visitMutual`'s `ci.value? = .none` arm (`Erasure.lean:1219-1227`) now dispatches on
the `ConstantInfo` before falling through to `addAxiom`: a `.quotInfo` registers `quotRealizer`'s
body (`:269`), a `.recInfo` whose inductive is a single non-recursive `Prop` with at most one
constructor all of whose fields are proofs registers `recursorRealizer`'s synthesized `case`
(`:409`). Both go through `addRealizer` (`:251`), which differs from `addAxiom` only in writing
`⟨some t⟩` where `addAxiom` writes `⟨none⟩`.

*The repair.* §3.2 states the rule; the concrete work is:

* M2: `addRealizerState` beside `addAxiomState` (`ErasureRun.lean:1523`), `run_addRealizer_ok`
  beside `run_addAxiom_ok`, and `run_visitMutual_ok`/`run_nonrec_exit_ok'` extended so the `.none`
  arm has three exits rather than one. `ConstExt.gdecls`' prefix clause says every prefix entry is
  `.constantDecl ⟨none⟩`, which an `addRealizer` falsifies, so the clause weakens to "a
  `constantDecl`, at a canonical kername of an extended registry"; `AxiomExt` keeps the body-less
  form and is used only where the arm is known to be `addAxiom`.
* M6: `run_visitMutual_decomp`'s three disjuncts (`ColdStartRun.lean:376-386`) become five;
  `RunClosed.ax` (`ColdStartInduction.lean:112`) and the run-form `ax`
  (`ColdStartInduction.lean:280-284`) gain the realizer case; `RegInvShape'.addAxiom`
  (`ColdStartShape.lean:215`) gains an `addRealizer` twin. The twin's premise is a `DefnDecl`
  where `addAxiom`'s is the body-less entry, and `register_inductive` runs *before*
  `recursorRealizer` returns, so the registry invariant sees the block's write first.

*Why the statements stay true.* §3.2, in full: the two exits are proved rather than refuted, the
`axioms` clauses are conditional on the entry they are about and a realizer satisfies the
`DefnDecl` branch instead of the body-less one, and the fragment's role is to keep a realizer key
off a supported program's reachable set — a measured condition, with the residue §3.2 names.
`NoBodylessRefs` becomes *true* on `Fannkuch`, which is a strict gain and is recorded in
`doc/coverage.md` by M8. `SupportError.recursorHead` and `SupportError.quotPrim` are **not**
lifted.

### 2.9 F-ETA

§4.

## 3. Three rules the repairs share

### 3.1 Every new throw branch and every new state read goes through the toolkit

`ErasureRun.lean`'s run library is the only way a branch is discharged. A `throwError` on the path
of a `= .ok` hypothesis is closed by `run_throwError_ne_ok` (`:163`); a `get` is stepped by
`run_get` (`:116`), a `modify` by `run_modify` (`:124`), a `liftMetaM` by `run_liftMetaM_ok`/
`run_liftMetaM_state` (`:226`, `:241`). No branch is assumed away — not by a hypothesis that the
guard does not fire, not by a `Config` pin that happens to make it dead, and not by leaving the
`unless` folded into an opaque `Bool`. The pattern is: step to the test, `by_cases` on it, kill the
throwing side with `run_throwError_ne_ok`, and carry the surviving side's *content* out as a
conclusion. That content is where the payoffs of §2.4 and §2.5 come from.

The new reads are `ErasureState.indBlocks` (a list, consulted by both guards and extended by
`register_inductive`) and `casesInfo.indName` (a field of the reader's argument, not of the state).
`indBlocks` joins `ConstExt`'s description of how the state grows; nothing outside the guards reads
it, so it needs no invariant of its own beyond being extended alongside `gdecls`.

### 3.2 The new registering exits are proved, not refuted; the fragment keeps them out of the way

It is tempting to close F-QUOT's and F-EQREC's branches by refuting them from the fragment. Two
facts say not to.

First, `run_visitMutual_registers` (`Step/Env.lean:329`) — the lemma `step6` spends — takes
`htab : (tbl.decl? n).isSome` and **no** `Supported` premise; `Motive6` (`Motives.lean:153`)
carries `Supported env tbl (.const n [])`, but the run lemma below it does not, and its conclusion
(`n` is in the registry, `RunConcl`, `IndRegistryModelled`, the generator bound) is what the
bridge consumes for *every* run. `addRealizer` (`Erasure.lean:251`) satisfies all four exactly as
`addAxiom` does: it inserts `n` into `constants`, conses one `gdecls` entry, runs no `visitExpr`,
and touches `inductives` only through the `register_inductive` call `recursorRealizer` makes
first. So the two exits are discharged by *proving the same conclusion at them*, and the shape of
the proof is `addAxiom`'s with `⟨some t⟩` in place of `⟨none⟩`. They likewise stay in
`run_visitMutual_decomp`'s disjunction (M6), which `ColdStartShape`'s registry invariant is proved
over for every run.

Second, the `axioms` clauses are not falsified by a realizer, because each is *conditional* on the
entry it is about. `ErasesEnv.axioms` (`ErasesEnv.lean:56-58`) fires at
`bo c = none ∧ ConstOrigin env c ∧ isCasesOnName c = false ∧ ReachableFrom Γspec t (toKername c)`;
`LowerEnv.axioms` (`ErasesEnv.lean:240-242`) fires where `Γspec` declares the key body-less;
`RegInvShape'.addAxiom` (`ColdStartShape.lean:215`) takes
`hax : envLookup Γspec (toKername n) = some (.constantDecl ⟨none⟩)` as a hypothesis, and its new
twin `RegInvShape'.addRealizer` takes `DefnDecl Γspec (toKername n) t` in its place. What would
falsify them is a `Γspec` that declares a realizer constant body-less while the emitted
environment gives it a body, and no producer of `Γspec` does that — the specification environment
is built from the same run. `NoBodylessRefs` (`Output.lean:862`) is decided per program and only
improves.

Where the fragment *does* work is one step further out, at the capstone's premises:
`supportedHead` refuses a quotient primitive (`Supported.lean:314`, `quotPrimNames` at `:156`) and
a recursor head (`:333`, `isRecursorName`), so a supported program applies no such constant, and
`ErasesEnv.axioms`' reachability gate therefore never fires at a realizer key. That is a statement
about *heads of the program*, not about what the run registers, and the difference matters:
`isRecursorName tbl c` is a five-string test on the last component with the prefix tabled
(`Supported.lean:184-189`), so a recursor whose name it does not match — an untabled prefix, or a
name outside `rec`/`recOn`/`brecOn`/`below`/`ndrec` — passes `supportedHead` through the
`(tbl.decl? c).isSome` arm and could in principle reach `recursorRealizer`. The condition "no
covered program registers a realizer" is therefore **measured, not assumed**: M8 adds the census
column to `doc/coverage.md` beside the existing per-program verdicts, and `grep -c '(constant_body
None)'` over the corpus is its companion. Nothing in the theorem stack assumes it.

### 3.3 The mirrored bodies are checked by elaboration, not by a tool

`Motives.lean` holds a copy of each of the eighteen shipping bodies with the family's calls
abstracted, and each `bodyLeᵢ` is `fix_step_le … Erasure.visitExpr.mutual._proof_1`
(`Motives.lean:679-681`). A copy that has drifted does not elaborate. Four copies changed:
`visitMutualBody` (`:420`), `visitCasesBody` (`:561`), `visitCtorEtaGoBody` (`:530`),
`visitCasesEtaGoBody` (`:549`). Re-copy them verbatim from `Erasure.lean`, replacing only the
family's own calls; do not "tidy" the copies.

## 4. F-ETA: the η-expanded fixpoint

### 4.1 What the eraser now emits

`visitMutual`'s registration loop registers `etaExpandFix defs i` (`Erasure.lean:1276`) where it
registered `.fix defs i`. `etaExpandFix` (`:478`) wraps in `defs[i].principalArgIdx + 1` binders
applied to their own indices. `Erasure.mkDef` emits `principalArgIdx = 0` at every member — which
the run already proves, `run_mkDef_rarg` (`ErasureRun.lean:2455`) — so on any run the wrapper is
exactly one binder:

```lean
/-- MetaRocq's `eta_fixpoint` (`template-rocq/theories/EtaExpand.v:72`) at `1 + rarg = 1`
binder, the only shape a lowered block admits (`LowerBlock.hrarg`, `Lower.lean:445`): the
fixpoint applied to its own binder. This is `Erasure.etaExpandFix`'s image. -/
def LBTerm.etaFix (defs : List (@FixDef LBTerm)) (j : Nat) : LBTerm :=
  .lambda .anon (.app (.fix defs j) (.bvar 0))
```

It lives in `FixMetatheory.lean`, which `Lower.lean` already imports and which every consumer
reaches. The general `rarg + 1` form is not stated: `Lower.fixConst`/`fixBody` carry
`hrarg : ∀ d ∈ defs, d.principalArgIdx = 0` as a premise (`Lower.lean:391`, `:407`), so no block the
relation admits has another shape, and a general definition would be dead.

### 4.2 How MetaRocq treats this, and why it needs no such relation

MetaRocq never η-expands λ□. `EEtaExpandedFix.expanded` (`EEtaExpandedFix.v:33-70`) is a
*precondition*, read on the erased program: `expanded_eprogram_env` (`:190`) is the declared `pre`
of `guarded_to_unguarded_fix` (`ETransform.v:666-672`), and — C-refute C13's correction — it is
already the `pre` of the pipeline's first component, `rebuild_wf_env_transform_mapping`
(`peregrine-tool/theories/erasure/Transforms.v:154`;
`../metarocq/erasure-plugin/theories/Erasure.v:1043-1049` → `ETransform.v:701-716`). It holds
because the expansion happened **before erasure**, on the Template program: the `eta_expand`
transform (`../metarocq/erasure-plugin/theories/Erasure.v:103-109`) runs
`EtaExpand.eta_expand_program` and `eta_fixpoint` (`template-rocq/theories/EtaExpand.v:72`) is its
fixpoint arm. Erasure then inherits expandedness from an already-expanded source, and no λ□-level
relation between a fixpoint and its wrapper ever appears.

Two things follow. First, the Lean frontend has no source-level expansion to inherit from — Lean's
recursive definitions become `.fix` at registration, in the eraser — so the expansion must happen
on the λ□ side and *something* must relate the two shapes. Second, MetaRocq's own precedent for
what that relation costs is encouraging rather than alarming: the `eta_expand` transform does not
claim the value is unchanged. Its observable equation is
`obseq p hp p' v v' := v' = EtaExpand.eta_expand p.1 [] v` (`Erasure.v:109`) — the target value is
the η-expansion of the source value. C1's observation that the emitted constant's *value* is now
`λx. fix x` where the `Lower` image of the specification constant's value is `.fix defs j` is the
same phenomenon, and §4.4 resolves it the same way: by putting the expansion inside the relation
that says what the eraser may emit, so that the wrapper *is* an image of the same source.

### 4.3 Why A21's refutation does not reach this arm

`Lower`'s `ctorEta` and `elimEta` arms were deleted at A21 (`doc/rework/01-DESIGN.md:437-444`, W2
refuter B-F4) for a stated reason: at a non-empty, under-applied prefix the expansion moves supplied
arguments under a binder where weak evaluation never reaches them; and re-keying to the bare head
does not save them, because `Lower` is compositional and an η-expanded head still composes under
`app` into `mkApps (mkLambdas ns body) args'` — a β-redex target with **no bound on nesting** that
every spine-inverting arm of T5 would have to collapse.

Neither half applies here. The new arm's target is `.lambda .anon (.app (.fix defs j) (.bvar 0))`:
a **closed, fixed shape**. It carries no supplied arguments (so nothing is moved under a binder),
no `Lower` sub-image under the binder (so nothing recurses), and no spine (so no spine-inverting
arm meets an unbounded redex). Its source, `bs[j]!`, is the same source `Lower.fixBody` already
admits at the same key, under the same `LowerBlock` premises — so the arm adds no
non-determinism that `fixBody` did not already add, which is the honest measure of its cost.
Concretely, the target-keyed inversion lemmas are unaffected: `Lower.source_lambda`
(`Lower.lean:2017`) already returns "a λ, or a block's `.fix` node" — and the wrapper *is* a λ, so
the new case lands in the existing first disjunct and its statement does not change.

### 4.4 The arm, and its two readings

```lean
  /-- A block member's specification body relates to the η-expansion of the block's node,
      beside `fixBody`'s bare node: what `Erasure.visitMutual` registers for the member
      (`Erasure.etaExpandFix`), and MetaRocq's `eta_fixpoint` at `1 + rarg = 1`. Read it
      through `Lower.fixEta'`. -/
  | fixEta {b : LBTerm} {kns : List Kername} {bs bs' : List LBTerm} {ids : List FVarId}
      {defs : List (@FixDef LBTerm)} {j : Nat}
      (hb : bs.length = kns.length) … (hcl : ∀ i, i < kns.length → CloseConstAt kns ids bs'[i]! (defs[i]!).body)
      (hj : bs[j]? = some b) (hjl : j < defs.length) :
      Lower Γ b (LBTerm.etaFix defs j)
```

— the premises are `fixBody`'s verbatim, inlined as the other block arms inline them, with
`Lower.fixEta'` the `LowerBlock`-shaped reading beside `Lower.fixBody'` (`Lower.lean:457`). The
declaration-level reading is `fixBody_of_block`'s twin, in the file that holds it:

```lean
/-- A block member's own body has the η-expansion of the block's node as an image: `fixEta`
at the member the declaration pins. `Lower.fixBody_of_block`'s twin
(`ErasesCorrect/Delta.lean:83`). -/
theorem Lower.fixEta_of_block {Γ : GlobalDeclarations} {kns : List Kername}
    {bs bs' : List LBTerm} {ids : List FVarId} {defs : List (@FixDef LBTerm)} {j : Nat}
    {kn : Kername} {b : LBTerm} (hblock : LowerBlock Γ kns bs bs' ids defs)
    (hj : kns[j]? = some kn) (hd : DefnDecl Γ kn b) : Lower Γ b (LBTerm.etaFix defs j)
```

Every `cases`/`induction` over `Lower` gains a `fixEta` case. In the target-keyed inversion kit
(`Lower.lean:1815-2090`) the case is `LBTerm.noConfusion` wherever `fixBody`'s is, except at
`source_lambda`, `source_isLambda` and `target_lambda`, where the wrapper is a λ. In the
structural metatheory — `Lower.mono`, `Lower.subst_comm`, `Lower.shift_comm`, `Lower.closed`,
`noBox_lower`, `Lower.ne_fix_of_block` — the case mirrors `fixBody`'s, since the wrapper's only
content is the same `defs`. `LowerFixFixture` gains `lowerfix_fixEta` beside `lowerfix_fixBody`
(`LowerFix.lean:945`), so the arm is exhibited non-vacuously on the tree's own block.

### 4.5 The environment relation

`LowerEnv.defs` (`ErasesEnv.lean:229-232`) keeps its shape; its second disjunct names the emitted
body the registration actually writes:

```lean
  /-- A body declared by both is a `Lower` image, or the η-expansion of one lowered block's
      node — `Erasure.visitMutual` registers `Erasure.etaExpandFix defs j`, not `.fix defs j`
      (F-ETA). -/
  defs : ∀ kn b₀ b, DefnDecl Γspec kn b₀ → DefnDecl Γ kn b →
    Lower Γspec b₀ b ∨ ∃ kns bs defs j, LowerFix Γspec kns bs defs ∧
      kns[j]? = some kn ∧ b = LBTerm.etaFix defs j
```

The second disjunct exists because the registration side produces the block shape, not a `Lower`
derivation; `fixEta_of_block` is the converter, exactly where `fixBody_of_block` was.

**Superseded by C3** (W2-refute R3). The disjunct adds no strength: `LowerFix`' own `hdecl`
identifies `b₀` with `bs[j]`, so `fixEta_of_block` returns the *first* disjunct, and the clause is
back to `Lower Γspec b₀ b` with the registration side discharging it through that converter. The
`LowerFix` predicate, whose only consumer this was, is deleted with it.

### 4.6 The δ step, and where the extra β is absorbed

`ErasesCorrect/Delta.lean:182-192` is unchanged in structure. The witness `H` is still the emitted
body `bΓ`, the step is still one `WcbvEval.delta`, and `WcbvEval.mkApps_congr` still moves the run
onto the spine at the *same* head value — because the wrapper, being an image of `b₀`, is what the
IH is taken at:

```lean
  rcases (Lower.const_body hhd rfl hdefn).2 with rfl | hbody
  · obtain ⟨bΓ, hbΓ⟩ := henvL.defsTotal _ b₀ hdefn hnk
    refine ⟨bΓ, ?_, fun w hw => .delta hbΓ hw⟩
    rcases henvL.defs _ b₀ bΓ hdefn hbΓ with hl | ⟨kns, bs, defs, j, hfix, hj, rfl⟩
    · exact hl
    · obtain ⟨bs', ids, hblock⟩ := hfix
      exact Lower.fixEta_of_block hblock hj hdefn      -- was fixBody_of_block
```

One line moves. In particular the empty spine — a bare recursive constant, where the emitted value
is `λ. (fix defs j) (bvar 0)` and the bare `.fix` node is *not* what the target evaluates to — is
not a gap: the target value is a `Lower` image of the source value by `fixEta`, so the arm's
conclusion holds with `w' = LBTerm.etaFix defs j`, and `erases_correct`'s `lam` arm closes it
through `Lower.source_lambda`'s unchanged first disjunct and `WcbvEval.lam`.

The extra β step appears only when the constant is *applied*, and it is absorbed in one place:
`Lower.appReady` (`ErasesCorrect/Steps.lean:599`), the single lemma that says what a lowered λ does
under application. Its `fixBody` case already builds `.fix_guarded … (.beta …)`; the `fixEta` case
puts one `WcbvEval.beta` in front of that same chain, since
`LBTerm.subst1 av ((fix defs j) (bvar 0)) = .app (.fix defs j) av` and `.fix defs j` evaluates to
itself:

```lean
theorem Lower.appReady_fixEta … (hblock : LowerBlock Γspec kns bs bs' ids defs) (hj : j < defs.length)
    (hs : bs[j]! = .lambda nm b₀) :
    ∃ c, Lower Γspec b₀ c ∧ BetaReady Γ fl (LBTerm.etaFix defs j) c
```

No simulation arm is added, no step statement is weakened, and `Erases`, `SEval` and the capstone's
observable are untouched. That is the answer to C1: its first option, the bounded η arm, taken with
its cost paid at `appReady` rather than by restating the δ step.

### 4.7 The payoff: `expanded_tFix`, all conjuncts

With every registered fixpoint applied, the capstone can conclude what peregrine's first pass
requires instead of the weaker `LBWfPeregrine`. `LBExpandedFix` (`Output.lean:259-263`) currently
states two of `expanded_tFix`'s five conjuncts (`EEtaExpandedFix.v:46-54`): `args ≠ []` and
`#|args| > rarg`, with `nth_error mfix idx = Some d` folded into the second. `isLambda d.dbody` is
`LBWfPeregrine.fixLambda`, already decided. The missing conjunct is the one inside
`expanded (ctx ++ Γ) d.dbody` with `ctx = rev_map (fun d => 1 + d.rarg) mfix`, which through
`expanded_tRel_app` forces every de Bruijn occurrence resolving into the block's own binder region
to head a spine of at least `1 + rarg` arguments. That is a decidable walk with a depth counter —
`scratch/round7/eta_selfrefs.py` is the same walk in Python and measures 56 self-references over
the five corpus programs with 0 unapplied — and it becomes `LBFixSelfApplied`.

`LBWfPeregrine` (`Output.lean:227`) gains the three together as one clause, `expandedFix`;
`lbWfPeregrineB` (`OutputCheck.lean:652`) gains the matching Boolean conjunct and
`lbWfPeregrine_of_check` (`:666`) the matching field, so every rung's `hwf` stays one
`by decide +kernel`. `PeregrinePre` (`Output.lean:268`) then has no content beyond
`LBWfPeregrine` and is deleted with its docstring's claim that the difference "is false on emitted
output". `07-STATUS.md` §1's parenthesis — "`LBExpandedFix` is **not** concluded (F-ETA)" — is
struck, and `doc/coverage.md` records the eight rung measurements.

### 4.8 Blast radius

`Lower.lean` (the arm, `fixEta'`, the inversion kit, the metatheory), `FixMetatheory.lean`
(`LBTerm.etaFix`), `LowerFix.lean` (the fixture), `ErasesEnv.lean` (`LowerEnv.defs`),
`ErasesCorrect/Delta.lean` (the converter, one line of the arm, the `const_body_fires` fixture),
`ErasesCorrect/Steps.lean` (`appReady`), `Output.lean`/`OutputCheck.lean` (§4.7),
`ColdStartShape.lean`'s nine `LowerEnv` reconstruction sites — `:237, :247, :309, :319, :437, :439,
:507, :510, :535` (C-refute C1), each of which rebuilds a `LowerEnv` from a smaller one and must
carry the new disjunct — `ColdStartRun.lean` and `ErasureRun.lean`'s `recConstState`
(`:2563`)/`recConstStep` (`:2574`), which cons the registered body, `Bridge.lean`,
`VisitExprRefines/Step/Env.lean`, `Witness/SourceTable.lean` and `Green.lean`.

## 5. Regeneration

| artifact | what moves | how |
|---|---|---|
| `VerifyBench/ast/*.ast` | the five corpus programs: +32 bytes per registered fixpoint (F-ETA), `Fannkuch` +315 (F-EQREC), `Quicksort` +231 (F-SPARSE) | `lake build VerifyBench`; gitignored, rebuilt in CI |
| `VerifyBench/ast/Spikes/G1..G8.ast` | tracked; the rungs that register a fixpoint (G6, G7, G8) gain the wrapper | rebuild the spikes, commit the bytes |
| `Green.lean`'s `g<i>Env`/`g<i>Term` | the literal transcription of those `.ast` | transcribe from the regenerated files; `lake exe green-check --all` re-derives every answer with `lbEval` from the byte-diffed `.ast`, which is the check that the transcription is faithful |
| `Green.lean`'s tables | `g<i>Table` reify the *source* environment, which no fix changes | `lake exe reify --check` on all eight; expect no diff |
| `doc/coverage.md` | the `NoBodylessRefs` column at `Fannkuch`, the N19 paragraph (C8), the new `expandedFix` measurement, the inductive census | `lake exe coverage`, then `--check` |
| `test/frozen` | the five frozen sources are not touched by the merge | `bash scripts/frozen.sh`; expect green, record the verdict |
| `test/ledger.expected` | a deleted hypothesis and a restated one move no `#print axioms` row | `bash scripts/ledger.sh`; expect no diff |
| `lake exe hygiene --dead` | the budget of 245 moves as declarations are added and `defns_needs_paramFree`-style orphans are deleted | re-measure; the budget is lowered by hand, never raised |

The `.ast` regeneration and the `Green.lean` transcription must happen in one commit: a
half-regenerated ladder elaborates and lies.

## 6. CI

`scripts/fixes.sh` — the ten regression tests under `test/fixes/`, each importing
`LeanToLambdaBox.Erasure` alone — joins `.github/workflows/build.yml` as its own step, after the
build and before the ledger:

```yaml
      # The shipping fixes' own regression suite. It runs against the shipping closure, not
      # the verification. `peregrine` is absent in CI, so the `validate`/`eval` half reports
      # itself skipped rather than failing.
      - name: Shipping fix regressions
        run: bash scripts/fixes.sh
```

The script already finds the sibling `peregrine-tool` build when there is one and reports the
peregrine half as skipped when there is not, so no workflow-level guard is needed. The `paths-ignore`
list keeps only `LICENSE`.

## 7. The clusters

Eight, in dependency order; each builds its own modules before the next starts, and the tree is
green only at M8. Every cluster commits with the configured author alone and names in its commit
body which modules still fail.

| id | title | build gate | kind |
|---|---|---|---|
| M1 | `Lower`: the flag equation and the η arm | `lake build LeanToLambdaBox.LowerFix` | R |
| M2 | `ErasureRun`: the guarded registration paths | `lake build LeanToLambdaBox.ErasureRun` | R |
| M3 | The output predicate: `expanded_tFix` in full | `lake build LeanToLambdaBox.OutputCheck` | R |
| M4 | The bundles and the fragment | `lake build LeanToLambdaBox.Supported` | R |
| M5 | The environment relations and the simulation | `lake build LeanToLambdaBox.ErasesCorrect.Close LeanToLambdaBox.FirstOrderInd` | R |
| M6 | The cold start and the bridge | `lake build LeanToLambdaBox.Bridge` | R |
| M7 | The eighteen refinement steps | `lake build LeanToLambdaBox.VisitExprRefines.Step.Passes LeanToLambdaBox.VisitExprRefines.Step.Env LeanToLambdaBox.VisitExprRefines.Step.Mechanical` | R |
| M8 | The capstone, the ladder, the artifacts, CI | `lake build` and the §7 battery | M |

M1 and M2 are independent roots and M3 is a third; the order above is one linearisation of a
three-rooted graph, chosen so that a cluster's reviewer never reads a module whose upstream is
still red. M4 needs M2; M5 needs M1, M3 and M4; M6 needs M2 and M5; M7 needs M5 and M6; M8 needs
all of them.

**M1** — `Erasability.lean`, `FixMetatheory.lean`, `Lower.lean`, `LowerFix.lean`. `PropositionalInd`
and `propositional_false_of_informative` (§2.1); `LBTerm.etaFix` (§4.1); `IndBodyOf` restated,
`ElimDecl` following it; the `fixEta` arm, `fixEta'`, the inversion kit and the structural
metatheory (§4.3, §4.4); `LowerElimFixture.mib`'s missing field; `lowerfix_fixEta`.

**M2** — `ErasureRun.lean` alone. `run_checkKernameFresh_ok`/`run_checkIndKernameFresh_ok` and the
repair of `run_addAxiom_ok` and the `register_inductive` lemmas (§2.5); `RegisteredBodyAt` and
`registerIndState` carrying `propositional` and `indBlocks`; the reconstructed body at `:1898`;
`addRealizerState`/`run_addRealizer_ok` and `run_visitMutual_ok`'s two new exits (§2.8);
`run_rec_exit_nodup` (§2.4); `recConstState`/`recConstStep` cons'ing `LBTerm.etaFix`. The three
heartbeat timeouts at `:2807`, `:2842`, `:2871` are the `visitMutual` decomposition meeting a larger
`.none` arm; re-stage the `split`s, do not raise the budget past what the shape needs.

**M3** — `Output.lean`, `OutputCheck.lean`. `LBFixSelfApplied` and its decision; the `expandedFix`
clause of `LBWfPeregrine`; `lbWfPeregrineB` and `lbWfPeregrine_of_check`; `PeregrinePre` deleted
(§4.7).

**M4** — `ErasureSpec.lean`, `Supported.lean`. `block_keys_distinct` deleted (§2.4);
`kernel_ind_head_true`'s docstring corrected (§2.6); `CasesInfoAgreesK.indName`/`.altCtor` and
their `CasesInfoAgrees` twins and `of_pinned` cases (§2.3); `BlockAdequate.propositional` if §2.1's
derivation does not go through; the two falsified comments at `Supported.lean:66` and `:562`.

**M5** — `ErasesEnv.lean`, `ErasesLB.lean`, `ErasesCorrect*.lean`, `FirstOrderInd.lean`.
`ErasesEnv.blocks`/`IndCovered.block` at the new `IndBodyOf`; `demoMib`'s field;
`LowerEnv.defs`' new disjunct (§4.5); `Lower.fixEta_of_block` and the one-line δ change (§4.6);
`Lower.appReady`'s `fixEta` case; the `= false` derivations in `Iota.lean` and `Proj.lean` and
`LowerProjFixture.mib`'s field.

**M6** — `ColdStartShape.lean`, `ColdStartInduction.lean`, `ColdStartRun.lean`, `SpecEnv.lean`,
`Bridge.lean`. The nine `LowerEnv` reconstruction sites at `LBTerm.etaFix`;
`run_visitMutual_decomp`'s five disjuncts and `RunClosed.ax`'s realizer case (§2.8);
`RegInvShape'.addRealizer`; `SpecEnv.lean:211`'s field; `BlockKeyed`'s `Nodup` threaded from M2.

**M7** — `VisitExprRefines/Motives.lean`, `VisitExprRefines/Step/{Env,Mechanical,Passes}.lean`,
`VisitExprRefines.lean`. The four re-copied bodies (§3.3); `step_visitCases` at the rebuilt loop
(§2.3) and the two F-ACC refusals (§2.2); `blockKeyed_install` rewired (§2.4); `step6` and
`run_visitMutual_registers` at the five exits with the two new ones refuted from the fragment
(§3.2).

**M8** — `Capstone.lean`, `Green.lean`, `Witness/TrWitness.lean`, `Origin.lean`, `Tools/*.lean`,
`VerifyBench/ast/Spikes/*`, `doc/*`, `.github/workflows/build.yml`. §5 and §6, plus: the capstone's
conclusion at the strengthened `LBWfPeregrine`, the eight rungs' `hwf` re-decided,
`07-STATUS.md` §1/§3/§4 and `doc/trust.md` restated, `03-DEV-FIX.md`'s verification-obligation
column closed row by row. `07-STATUS.md` §5's red-CI claim is **stale**: `lake exe hygiene
--schedule` reports `8 deletion rows, 45 deleted files, 18 live imports of them, 0 inversions`
at the merge, measured both with and without this document
(`scratch/round7/w8.sched.out`, `w8.sched.base.out`), so the §5 paragraph about
`doc/rework/02-PLAN.md` §4's W2 row is rewritten rather than acted on.
