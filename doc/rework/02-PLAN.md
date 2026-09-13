# 02 — Implementation plan

Companion to `01-DESIGN.md`, which is normative for every signature named below. Seven waves.
Within a wave, the numbered units are **independent** and may be executed in parallel by separate
agents on **disjoint files** — except a unit marked **first**, which the rest of its wave depends
on; each wave ends with a single **gate** unit that integrates them and carries the wave's green
light. Dependencies inside a wave are *interface-only* — the signatures are fixed by
`01-DESIGN.md` §4, so a unit may import a sibling's file and use its declarations, but may never
edit it. Dependencies marked **(proof)** need the sibling's proofs, not just its statements, and
are only ever on an earlier wave or on the wave's own gate.

**The standing obligation.** From W1's gate onwards, `LeanToLambdaBox/Green.lean` must elaborate
under `lake build` at the end of **every** wave, with every class-**D** binder named per A14 (`P`,
`htbl`, `hrun`, and `hwt` until U3.7) and every conclusion ending in a literal peano numeral. Not
every class-**C** hypothesis is inhabited at every rung yet: `hcb` is discharged only at G1 (G2–G4
route a tabled body through lean4lean's unproven `TrProj`) and `hev` at no rung before G3's
`green_G5` — both tracked rows in `doc/trust.md`, not silent gaps (`01-DESIGN.md` §2.4, §6). A wave
that leaves `Green.lean` red is not finished, whatever else it landed.

**Estimate columns.** `Est.` is the lines of finished Lean the unit lands — new files **plus**
content re-landed from git history in adapted form (§4). `01-DESIGN.md` §7.3's "new" total counts
only brand-new files; the two figures measure different things and both are stated.

---

## 0. Rules that hold in every wave

**N1 — One name, one home, one wave.** New code and old code never both define the same name.
The unit that introduces the final version of a declaration deletes the old declaration of that
name **in the same commit** — or depends on the cut unit (U1.0) that already deleted it. Primed
twins kept "so the old one still compiles" are forbidden: if a statement changes, the new
statement keeps the old name and every consumer inside the unit's own files is updated in the
same commit; a consumer outside them makes that file a co-owned file of the unit, listed in the
unit's file list. Enforced by `lake exe hygiene --dup`, which fails if any declaration name is
defined in two modules.

**N2 — Deletion is scheduled, not opportunistic, and topological.** Every file scheduled for
deletion (§4) is removed in its scheduled wave by the unit that owns it, never later. A file
scheduled for deletion in wave *n* may not gain new content in wave *n−1*. **A file may be
deleted in wave *n* only if every module importing it is deleted in wave ≤ *n* or is owned (or
co-owned) by a unit of wave *n*.** Enforced by `lake exe hygiene --schedule`, which reads §4's
table and the `import LeanToLambdaBox.*` graph and fails on any inversion; it runs at every
gate. A surviving compatibility shim (`ErasureCtx` kept "so the old files compile", a second
`Erases`) is the review-§2 failure mode by name and is what this rule exists to prevent.

**N3 — Ownership is per wave.** A file may be owned by different units in different waves; within
one wave exactly one unit owns it. **N3a — gate-owned standing files.** `LeanToLambdaBox.lean`,
`lakefile.toml`, `lake-manifest.json` and `test/ledger.expected` are owned by the wave **gate**
in every wave: a unit that deletes a module, adds a module, adds a `lean_exe`, or changes an
axiom footprint hands the corresponding one-line edit to its gate; no unit edits them directly.
This is the only way N3 and N6 hold together, since nearly every proof unit changes an axiom
footprint and every wave changes the build root.

**N4 — Every unit's acceptance test is machine-checkable** and is run by the wave gate:
a `lake build` target, a `#print axioms` diff against a committed fixture, a `by decide` / `by rfl`
example, a `lake exe` tool exit code, or a `grep` whose expected output is stated. Greps are
written as commands that run verbatim (`grep -E` alternations unescaped; counts via
`grep -rl … | wc -l`, never `grep -rc … = 1`).

**N5 — Findings are raised, never patched.** No unit edits
`LeanToLambdaBox/{Erasure,Basic,Printing}.lean`. Defects found go to `doc/upstream-asks.md` (for
lean4lean, MetaRocq, peregrine) or to `doc/rework/03-DEV-FIX.md` (the tracked `dev/fix` queue,
`01-DESIGN.md` §8.2). One scheduled exception, U0.6: `Relevance.lean` is verification-authored
(absent from `main`), so fixing F-FUEL there is not a transpiler edit and is in scope
(`01-DESIGN.md` §8.1).

**N6 — The ledger is measured, never narrated.** `test/ledger.expected` holds exactly the
`#print axioms` output of `test/Ledger.lean` and nothing else; the gate diffs it. Provenance and
classification (`sorryAx` roots with `file:line`, class rows) live in `doc/trust.md`, whose every
identifier and `file:line` `lake exe hygiene` resolves — `#print axioms` cannot measure
provenance, so no acceptance test claims it does. A unit that changes an axiom footprint hands
the fixture diff and the `doc/trust.md` row to its wave gate (N3a).

---

## 1. Wave summary

| Wave | Goal | Units | Green rung at the gate | Status |
|---|---|---|---|---|
| **W0** | Foundation: flags renamed tree-wide, tooling, ledger, F-FUEL, dead shims deleted | 6 + gate | — (tooling self-test) | **Delivered** |
| **W1** | **The cut**, then specification + pass layers; **the recursion wall retired**; first end-to-end instance | 1 + 9 + gate | **G1** `spikeZero` | **Delivered**, except U1.5 and U1.8 (in progress) |
| **W2** | β, ζ, literals; the composite; then the re-anchoring the W2 refutations force | 4 + 6 + gate | G2, G3, G4 | **Delivered** |
| **W3** | the one simulation (β ζ δ ι proj lit), first-order domain, `TrExprS` witnesses, the fragment, the pin bump | 9 + gate | G5, G6 | **Delivered**, under `StepPremises` (retired by W3R) |
| **W3R** | **The repair wave**: the definitions the W3 arms had to work around — `ErasesEnv` forward (seven clauses), `Erases.proj`'s relevance (semantic, not syntactic), `SEval`'s pinned block data in source coordinates, `CasesOnShape`'s type, `LowerBlock.hfl`, the table modulo α — so that `erases_correct` needs MetaRocq's five, `LowerEnv` and `UpstreamAsks` and nothing else. Re-planned after its own refutation (`05-REPAIRS-W3.md` §16) | 9 + gate | G1–G6 unchanged and still green **at the gate** | **Delivered**; delivered files below |
| **W4** | The bridge: 18 motives against `ErasesLB`/`ErasesLBFix`, plus the block λ-headedness `LowerBlock.hfl` now asks of it | 6 + gate | G1–G6 lose `hbridge` | **Delivered in part**: the motives, the aggregator and fourteen of the eighteen steps; steps 3, 4, 10 and 17 have no supplier and step 4 is refuted at a block reader, so `hbridge` stands |
| **W4b** | **The bridge repair wave**: the fixvar mode keyed at the tabled names, which un-refutes step 4, the inductive registry in `BridgeInv`, the two bundles that retire the seventeen step premises (`ErasureSpec` for the primitives, `EraserAsks` for this repository's own code), `Lower.abstract`, the two `SupportedTm` repairs, N22 moved to the input side, step 17, and the capstone's erasure half. `doc/rework/06-REPAIRS-W4.md` is the design; its §14 is the refutation round, its §15 the delivery findings | 9 + gate | G1–G6 green at every unit | **Delivered in part**: seventeen of the eighteen member steps landed, `erasure_bridge_of_run` proved modulo six named obligations (`Step4`, `VisitExprRunConcl`, `DeclInfoAtHead`, `hall`, `hseg`, `hctab`); those six are being closed by a follow-up to G4R, tracked outside this document |
| **W5** | The registration invariant at a run's final state, discharging `hbridge`'s six fields; capstone at Arith, coverage, delivery | 6 + gate | **G7, G8** | **Delivered in part**: eight rungs green, the world-indexed run induction (`RunClosedW`, `visitExpr_shapeW`), `bridgeEnv_of_regInv` and a five-field `ErasureBridge`; the registration invariant is refuted as specified (`08-REPAIRS-W5.md` §2) and `hve`/`hbridge` stand |
| **W6** | **The closing round**: `hve` discharged, `hbridge` reduced from five fields to two (`wf` a per-rung checked term, `noBox` and `simulate` retired), the mis-specified printable-binder clause restated, the α kit deleted. `doc/rework/08-REPAIRS-W5.md` is the design | 8 + gate | G1–G8, `hve`-free | not started |

---

## 2. Waves in detail

### W0 — foundation (6 parallel units + gate) — done

All six units and the gate are landed; every file below exists and `G0`'s command line is green.

**Goal.** Make the flag points exist under their final names, stand up the CI tools the whole
schedule depends on, fix the one verification-authored shipping defect, and delete what is
provably dead — before anything is proved on top of the tree.

**Delivered.** All six units and the gate landed together: `Semantics/Flags.lean` carries
`eraseFlags`/`entryFlags`/`blockFlags`/`propBlockFlags` and `WcbvEval.propcase_weaken`;
`test/{Ledger.lean,ledger.expected,hygiene.allow}` and `lakefile.toml` exist; `LeanToLambdaBox/
Witness/SourceTable.lean` and `Tools/{Reify,GreenCheck,Hygiene}.lean` exist and `lake exe
green-check --self-test` and `lake exe hygiene` both run; `doc/{rules-Erases,rules-Lower,panics,
coverage,upstream-asks,trust,dev-fix-queue}.md` exist; `Relevance.lean`'s F-FUEL fix landed. The
deletion U1.0 (below) describes was executed in this same pass, ahead of its scheduled wave — the
surviving tree at G0 already has no reference to `ErasureCtx` or a retired `Erases` rule.

| Unit | Files owned | Depends | Est. | Acceptance |
|---|---|---|---|---|
| **U0.1 flags-rename** | `LeanToLambdaBox/Semantics/Flags.lean` (§3.2's four constants + `propcase_weaken`; header rewritten); **co-owns, for the mechanical rename only**, every `.lean` file holding `appliedFlags`/`optFlags`/`defaultFlags`/`targetFlags` (103 sites / 16 files, including `Semantics/Eval.lean`'s `Eval`/`EvalProp` abbrevs, `Optimize.lean`, `Semantics/Metatheory.lean`); **deletes** `Export/EvalT.lean`, `Semantics.lean`, `Eval.lean` (re-export shims), co-owning their importers' import lines | — | 250 | `lake build` green; `grep -rn "defaultFlags\|appliedFlags\|targetFlags" LeanToLambdaBox/` empty and `grep -rn "optFlags" LeanToLambdaBox/` empty; `grep -c "⟨false, true, false⟩" LeanToLambdaBox/Semantics/Flags.lean` = 1; `#print axioms WcbvEval.propcase_weaken` = `[propext]`; the three files absent from `git ls-files` |
| **U0.2 ledger-and-CI** | `test/Ledger.lean`, `test/ledger.expected`, `lakefile.toml`, `lake-manifest.json`, `.github/workflows/build.yml` (from W1 on these pass to gate ownership, N3a) | — | 140 | `diff <(lake env lean test/Ledger.lean) test/ledger.expected` exits 0; `git show HEAD:lakefile.toml` pins the `lean4lean` dependency by an explicit `rev`, matching the `rev` field `lake-manifest.json` records for the `lean4lean` package; the workflow's `branches:` list contains `dev/verify`; `lean_exe` stanzas exist for `reify`, `green-check`, `hygiene` (texts supplied by U0.3–U0.5) |
| **U0.3 reify-elaborator** | `LeanToLambdaBox/Witness/SourceTable.lean` (`SourceTable`, `body?`, `SourceTableAdequate`, the `reify%` term elaborator — §4.11: no committed JSON, no ingestion parser), `Tools/Reify.lean` (`lake exe reify --check`: field-by-field comparison of a named table against the **live** environment, for CI drift detection) | — | 420 | a self-test module reifies one toy declaration with `reify%` and `by rfl`-checks its type and body fields against hand-written literals; `lake exe reify --check` exits 0 on it and exits 1 when the module deliberately mismatches |
| **U0.4 lbEval-wiring** | `LeanToLambdaBox/Semantics/Compute.lean` (**exists**, 338 lines, proved — this unit only reviews and wires it), `Tools/GreenCheck.lean` | — | 250 | `Semantics/Compute.lean` is in the root's import closure (gate applies the root edit); `#print axioms lbEval_sound` = `[propext]` (measured); `example : lbEval nvΣ eraseFlags 1000 nvT = some (peanoLB 3) := by rfl`; `lake exe green-check --self-test` exits 0 |
| **U0.5 docs-and-hygiene** | `Tools/Hygiene.lean` (incl. `--dup`, `--schedule` (N2), `--anti-epicycle FILE` (comment-stripped token scan), `--dead`, `--tables`), `doc/rules-Erases.md`, `doc/rules-Lower.md`, `doc/panics.md`, `doc/coverage.md`, `doc/upstream-asks.md`, `doc/trust.md`, `doc/rework/03-DEV-FIX.md` | — | 420 | `lake exe hygiene` exits 0 on the files W0 touched; `--dup` exits 0; `--schedule` exits 0 against §4's table; the seven documents exist, `doc/rework/03-DEV-FIX.md` carries the six §8.2 rows (F-PROP, F-ETA, F-SPARSE, F-ACC, F-QUOT/F-EQREC, F-PRODUCT) each with `file:line`, the measuring command and its output, and `doc/upstream-asks.md` carries §8.3's six items; every `doc/…` citation in `01-DESIGN.md` resolves |
| **U0.6 F-FUEL** | `LeanToLambdaBox/Relevance.lean` (verification-authored; N5's scheduled exception) | — | 30 | fuel exhaustion in `isArityCheck.loop` becomes `throw`, so `Erasure.isErasable` routes to `isErasableMeta` and reproduces the pre-B1 verdict; `lake build` green; `#print axioms isArityCheck.WF` unchanged (the statement never mentions the fuel); the SI-1 reproducer (`def T2 : Type 1 := Nat → Nat → Nat → Type; def foo : T2 := fun _ _ _ => Nat`) now gets `isErasable = isErasableMeta`'s verdict; the five committed `.ast` re-erase byte-identically |
| **G0 gate** | integration; N3a files | U0.1–U0.6 | 40 | `lake build && lake exe hygiene && lake exe hygiene --dup && lake exe hygiene --schedule && lake exe green-check --self-test && diff <(lake env lean test/Ledger.lean) test/ledger.expected` |

### W1 — the cut, then specification + pass layers, the recursion wall, and the first green light (1 + 9 + gate)

**Goal.** Delete the old proof chain in one commit, then build everything L1 and L4 need at the
δ/constructor fragment, prove the fix correspondence, and land a real `#erase` run of
`spikeZero : Nat := Nat.zero` whose every class-**C** hypothesis is inhabited.

**Delivered**, with two units still in progress. **U1.0**'s deletion is confirmed done (it landed
together with W0, above; nothing in the surviving tree references `ErasureCtx` or a retired
`Erases` rule). **Done**, each on its own file(s): `Erases.lean` (U1.1, ten rules plus `IndInfo`);
`ErasesAbstract/Strengthen/Uniform.lean` (U1.2); `ErasesTotal.lean` (U1.3); `SourceEval.lean` and
`SubjectReduction.lean` (U1.4); `ElimBody.lean` (U1.6); `LowerFix.lean` (U1.7, the wall did not
stop the schedule — §2.2 of `01-DESIGN.md` records the two repairs it needed); `ErasesEnv.lean`
and `SpecEnv.lean` (U1.9); `LowerCorrect.lean`, `Capstone.lean`, `VerifyBench/Spikes/G1.lean` and
`Green.lean` (**G1**, `green_G1` elaborates). Every delivered signature that changed shape from
this document's printed form is in `01-DESIGN.md` §2.2, §4 and §5, by file:line. **In progress**:
**U1.5** (`Lower.lean`, `doc/rules-Lower.md`) and **U1.8** (`ErasureSpec.lean`, `Supported.lean`,
`Output.lean`, `CheckerAdequacy.lean`) — W2's units below depend on their interfaces, which are
stable, and on their proofs where marked.

| Unit | Files owned | Depends | Est. | Acceptance |
|---|---|---|---|---|
| **U1.0 the-cut — first** | **deletes**, in one commit, every file whose statements mention `ErasureCtx` or the six retired `Erases` rules (§4 lists all 37): the four old capstone flavours, `ErasureContext.lean`, old `Erases.lean`, `ErasesLevels/InstL/DeltaL.lean`, `SourceEvalData.lean`, old `SubjectReduction{,Full,Iota}.lean`, the five `*Hyps.lean`, `OracleDischarge.lean`, `EnvErasure{,Nonrec,Rec}.lean`, `ErasesCorrect{,Data,Iota}.lean`, `IotaPattern/IotaDischarge/ProjPattern/ProjDischarge.lean`, `RecBlockErasure.lean`, `EraseCore.lean`, `FirstOrder.lean`, `ColdStart{,Delta,Shape,Induction,Run}.lean`, `VisitExprRefines.lean`, `Bridge.lean`; gate applies the root-import edit | W0 | — | `lake build` green (the surviving tree — semantics, metatheory, `ErasureRun.lean`, `Optimize.lean`, shipping code — has no reference to any deleted name); `lake exe hygiene --schedule` exits 0; `git log -1` shows one commit. Content scheduled for re-landing (§4) is recovered from git history by its owning unit — never kept as a live file |
| **U1.1 erases-relation** | `LeanToLambdaBox/Erases.lean` (the ten rules of §4.2 **plus `IndInfo`**, its first consumer being `Erases.proj`), `doc/rules-Erases.md` | U1.0 | 900 | `grep -rn "ErasureCtx" LeanToLambdaBox/` empty (criterion 1); a `#guard` fixing the constructor list at exactly the ten names of `01-DESIGN` §4.2; `doc/rules-Erases.md` covers every `[S Fig. 18]` rule (`lake exe hygiene --tables`) |
| **U1.2 erases-transport** | `ErasesAbstract.lean`, `ErasesStrengthen.lean`, `ErasesUniform.lean` (the ~200 surviving level lemmas re-land inside `ErasesAbstract.lean`) | U1.1 | 700 | `erases_subst`, `erases_shift`, `Erases.abstract`, `Erases.uninstantiateN`, `Erases.thin_vlet` elaborate; `#print axioms erases_subst` ⊆ `[propext, Classical.choice, Quot.sound]` |
| **U1.3 erases-total** | `ErasesTotal.lean` | U1.1 | 300 | `Erases.exists_of_trExprS`, `Erases.sort_erasable`, `Erases.forallE_erasable`, `Erases.mono` elaborate (criterion 10, first half) |
| **U1.4 one-SEval** | `SourceEval.lean` (`SEvalFlags`, `SEval` with `deltaC`, `CompilerBodies` — §4.3), `SubjectReduction.lean` | U1.0 | 850 | `test $(grep -rl "^inductive SEval" LeanToLambdaBox/ \| wc -l)` = 1 (criterion 4); `SEval.mono`, `SEval.le` and `SEval.defeq` at `deltaOnly` elaborate; a `deltaC` example steps `Nat.add 0 0` through one tabled unfolding with the `IsDefEqU` side condition closed `by rfl`-grade defeq |
| **U1.5 lower-relation** | `Lower.lean`, `doc/rules-Lower.md` | U1.0 | 850 | `Lower` elaborates with the 17 arms of `01-DESIGN` §4.4 (incl. `ctorApp.hsat`, `ctorEta.hns`, the `LowerBlock` fields with `hrarg` and shared `ids`) and `#print axioms Lower` = `[propext]`; **the anti-epicycle guard** `lake exe hygiene --anti-epicycle LeanToLambdaBox/Lower.lean` exits 0 (comment-stripped scan for `Lean.Expr`, `VEnv`, `Erasable`, `ErasureState`, `NameGenerator` — not `FVarId`, which is λ□'s own fvar syntax, `01-DESIGN` §4.4); `Lower.shift_comm`, `Lower.subst_comm` elaborate |
| **U1.6 elim-body** | `ElimBody.lean` (imports `IndInfo` from U1.1) | U1.0, U1.1 (interface) | 700 | `#print axioms mkElimBody_iota_fwd` and `mkElimBody_iota_bwd` = `[propext, Quot.sound]` (class **A**); one checked `ElimBody` instance each for `Nat.casesOn`, `Bool.casesOn`, `Decidable.casesOn` (criterion 7 as amended by A2 — informative inductives only; N18) |
| **U1.7 lower-fix — THE WALL** | `LowerFix.lean` (`ConstToFVar`, `CloseConstAt`, `LowerFix`, `Lower.constToFix`, `ErasesLBFix`, `LowerBlock.lambda_of_fixLambda`) | U1.5 | 700 | four obligations in one file, all on the hand-built two-member mutual-block fixture `lowerfix_nv`: (i) `Lower.constToFix` elaborates, class **A**; (ii) the fixture exhibits `LowerBlock Σ⁺ [kn₀,kn₁] bs bs' ids defs` (with `hrarg` and shared `ids`), `Lower Σ⁺ bs[1]! (.fix defs 1)`, `WcbvEval Σ eraseFlags (.const kn₁) (.fix defs 1)`, and **one application step through the block** — for a source `WcbvEval Σ⁺ eraseFlags (.app bs[1]! a) v`, a target `WcbvEval Σ eraseFlags (.app (.fix defs 1) a') v'` with `Lower Σ⁺ v v'` (this is what would have caught the `principalArgIdx` refutation); (iii) `isLambda bs[1]! = true` discharged via `LowerBlock.lambda_of_fixLambda` from the fixture's own `defs`; (iv) **stateability**: `example : ErasesLBFix env Us Σ⁺ kns ids [] e t` is exhibited on the fixture — a `constToFix` that elaborates while the block-body motive is unstateable does not clear the wall. **If any of the four fails, the schedule stops** (risk R1) |
| **U1.8 erasurespec-supported-output** | `ErasureSpec.lean`, `Supported.lean` (incl. re-landed `IsLamTelescope`, `Supported.*_inv`), `Output.lean`, `CheckerAdequacy.lean` (eraser-specific lemma renamed to `LeanToLambdaBox.Oracle.kernel_isErasable_sound`; the seven kernel-generic declarations stay in their `Lean4Lean` namespace until U3.1's pin bump) | U0.3 | 1,300 | `grep -rn "structure .*Hyps" LeanToLambdaBox/` empty (criterion 4); `example : supportedB g1Table 64 eG1 = .ok () := by rfl`; `example : supportedB qsTable 64 eQuicksort = .error (.sparseCasesOn _) := by rfl` (criterion 11); `#print axioms ErasureSpec.envWF` = `[propext, Classical.choice, Quot.sound]`; the `decl_adequate` **derivation attempt** from `env_connect` (via `TrEnv'` inversion) is made and its outcome recorded — field kept only with the obstruction named in the docstring; per remaining class-**D** field, the docstring states why it is irreducibly about an opaque primitive |
| **U1.9 erases-env** | `ErasesEnv.lean` (`ErasesDecl`, `ErasesEnv`, `LowerEnv` incl. `defsTotal`, `EnvAgree`, `LBWfSpec`, `WcbvEval.congr_env`), `SpecEnv.lean` | U1.1, U1.5, U1.6 | 1,050 | an `example : ErasesEnv env bo Σ⁺ t` elaborates for a hand-built environment holding one inductive, one `ctor` entry, one `elim` entry (informative) and one fix definition; `SpecEnv.mono` elaborates from `StateLe` |
| **G1 gate — green_G1** | `LowerCorrect.lean` (δ / `ctorApp` / fix fragment), `Capstone.lean` (T9 stated in full, proved modulo one `hbridge` binder), `VerifyBench/Spikes/G1.lean`, `LeanToLambdaBox/Green.lean`; N3a files | U1.1–U1.9 **(proof)** | 1,200 | `lake build` elaborates `green_G1`, whose conclusion ends in the literal `.construct natIid 0 []`, with `hcfg`, `hsup`, `hax`, `hcb` inhabited by checked terms, `P`/`htbl`/`hwt` named class-**D** binders per A14, and `hbridge`/`hrun` outstanding; `lake exe green-check G1` byte-diffs the `.ast`; `lake exe hygiene --dup && lake exe hygiene --schedule`; ledger diff clean |

### W2 — β, ζ, literals, projections, then the re-anchoring (4 + 6 + gate) — done

**What the gate handed over.** G1 already delivered `lower_correct_deltaChain` — `lower_correct`
at the δ/constructor/fix fragment, under three named guards (`LowerNoEta`, `BlockBodiesLambda`,
`DefsSurvive`) that are load-bearing, not interim: the unrestricted statement is machine-refuted
at the `ctorEta` arm (`lower_correct_needs_ctorEta_guard`, `01-DESIGN.md` §2.2 finding **G1-O6**),
and box-freedom does not transport along `Lower` without a `NoFix`-shaped guard either
(`noBox_lower_needs_noFix`, finding **G1-O7**). T9 is proved in full modulo one binder, `hbridge :
∃ Σ⁺ t₀, ErasureBridge …`, whose nine fields are the actual W2–W4 work list (`01-DESIGN.md` §5);
three of its own statement's deviations from `01-DESIGN.md`'s printed T9 (**G1-O1/O2/O3**) are
retired by the units below and by U3.5, not by this wave restating T9 itself.

`Capstone.lean` is **gate-owned for this wave** (an addition to N3a's list, tracked here since W1
already set the precedent of the wave gate assembling `hbridge`'s fields from sibling units'
proofs): each of U2.1–U2.3 below delivers a standalone theorem in its own file and hands its
one-line `ErasureBridge` field assignment to **G2**, which is the only unit that edits
`Capstone.lean` this wave. This is what rule N3 requires once three sibling units all feed one
shared consumer file.

| Unit | Files owned | Depends | Est. | Acceptance |
|---|---|---|---|---|
| **U2.1 lower-correct — general case** | `LowerCorrect.lean` | W1 **(proof)**, U1.5 **(proof)** | 900 | `lower_correct` generalises `lower_correct_deltaChain` to all 17 arms of `Lower` (η, ι, proj, `case`, block flags), carrying `LowerNoEta`/`BlockBodiesLambda`/`DefsSurvive` as permanent class-**C** hypotheses — **not** discharged by waiting on the eraser-side fix **F-ETA** (policy N5: `dev/verify` never depends on `dev/fix` landing). `#print axioms lower_correct` = `[propext, Classical.choice, Quot.sound]`; a `_fires` non-vacuity guard per arm (`Optimize.lean:1066`'s style), including one exercising `ElimHeadOf`'s second disjunct, on pain of deleting it (§4.4); `lake exe green-check --differential` reconstructs the `Erases`-image from each rung and checks membership in `Lower Σ⁺` by a decidable checker. **Outcome: the 17-arm statement is refuted** (`01-DESIGN.md` §2.3, W2-R4/R5); delivered as `lower_correct_plain` over a named fragment, itself retired by U2.7/U3.1. The `--differential` flag does not exist in `Tools/GreenCheck.lean`; `lake exe green-check --all` is what runs |
| **U2.2 composite** | `ErasesLB.lean` (new: the composite, the seven derived introduction lemmas, their `ErasesLBFix.*` twins) | U1.1, U1.5 **(proof)**, U1.7 **(proof)**, U1.9 | 600 | the introduction lemmas elaborate and their `#check` output diffs clean against `test/erasesLB.expected` — the fixture pinning them to the deleted rules' signatures; a lemma that T9's spine premise (`targs.length = args.length → ∀ i, … → ∃ a₀, Erases … a₀ ∧ Lower Σ⁺ a₀ targs[i]!`) implies `∀ i, i < args.length → ErasesLB env [] Σ⁺ [] args[i]! targs[i]!` (and conversely), so **G2** can fold `Capstone.lean`'s statement back with no reproof (finding **G1-O3** retired) |
| **U2.3 T5-interim** | `ErasesCorrect.lean` (new: T5 at the W2 fragment) | U1.1, U1.9, U1.4 (interface only — `SEval.defeq` already holds unconditionally at `fullFlags` with no `CompilerBodies`/`lenv` binder, finding **U1.4-b**, so U2.3 does not edit `SourceEval.lean`/`SubjectReduction.lean`) | 750 | `erases_correct` elaborates with **six** binders — the five of `01-DESIGN.md` §5 plus the named interim `hfl : fl ≤ w2Flags` (the induction does not yet cover the `case`/ι step), deleted at U3.2 once the ι arm lands (§3.4; the W3 statement is the pinned one); none is named `Supported`/`Relevant`/`Iota*`/`*Consistent`/`*Hyps`; `#print axioms erases_correct` = the class-**B** set. **Outcome: delivered as `erases_correct_tabled`**, with `hfl` unnecessary and `hΣ` replaced (W2-R1/R2/R3); its arms become U3.1's step lemmas |
| **U2.4 fuel** | `Fuel.lean` (the surviving `EraseCore` fuel lemmas, re-landed from git history) | U1.0 | 250 | **Retired.** The lemmas elaborated, but nothing consumes them and no module imports the file (101 lines, zero references tree-wide); `Fuel.lean` is deleted by U2.10 and `01-DESIGN.md` §7.3's row for it is gone. The `grep -rn "IotaRelevant\|IotaShape\|RecBlockAgreement" LeanToLambdaBox/` obligation it carried moves to G2 |

**W2's second half — the re-anchoring its own refutations force.** U2.1 and U2.3 refuted both
halves of the composition strategy (`01-DESIGN.md` §2.3), and two rounds of refutation then
reshaped the re-anchoring (`04-AMENDMENT-W2.md` §2, §13). The six units below land the amended
architecture; none of them proves a simulation — W3 does that, once. They are **not** independent:
a rule change to `Erases` or `Lower` breaks `LowerCorrect.lean`, `ErasesLB.lean` and
`ErasesCorrect.lean`, all inside `Green.lean`'s import closure, so each unit owns everything it
breaks and the chain is U2.9 → U2.5 → {U2.6, U2.7} → U2.8 → U2.10 → G2 (refuter findings B-F4,
F9). `Capstone.lean` stays gate-owned. Every document and fixture the rule changes falsify is in a
unit's file list, not left for a gate to discover: `doc/rules-Erases.md` (U2.5),
`doc/rules-Lower.md` and `test/Ledger.lean` (U2.7), `doc/trust.md` (U2.8).

| Unit | Files owned | Depends | Est. | Acceptance |
|---|---|---|---|---|
| **U2.9 demolition and relocation — first — done** | `ErasesCorrect.lean`, `Semantics/Metatheory.lean`, `Closed.lean`, `ErasesAbstract.lean` | U2.1, U2.2, U2.3 **(proof)** | 450 | every statement the amended architecture retires is **deleted with its subject** and recorded in `ErasesCorrect.lean`'s header with the refutation it carried (`erases_correct_tabled`/`_ctx`, `TabledConstants`, `DeltaAgrees`, `erasesEnv_not_deltaAgrees`, `erases_const_ne_construct`, `erases_correct_needs_tabled`, `erases_correct_needs_tabled_ctor`); `Erases.defeqDFC_wt`/`erases_subst_let`/the four `InstLet` helpers elaborate in `ErasesAbstract.lean` and `WcbvEval.{head_value_of_mkApps, app_congr, mkApps_congr, mkApps_box}` in `Semantics/Metatheory.lean`, each with its `#print axioms` unchanged; `erases_mkApps_inv`/`erasable_mkApps`/`erases_correct_box`/`_boxSpine` stay (U3.1 moves them down into `ErasesCorrect/Steps.lean`, where the arm files can reach them without importing the aggregator); **the missing target-side lemma lands**: `WcbvEval.lbClosed : ClosedBodies Γ → LBClosed t 0 → WcbvEval Γ fl t v → LBClosed v 0` — no lemma relates `WcbvEval` and `LBClosed` in the tree today (refuter finding B-F5) — with a `_fires` witness; `grep -n "WcbvEval Σ⁺" LeanToLambdaBox/ErasesCorrect.lean` empty; `lake build` green; `lake exe hygiene --dup` = 0 |
| **U2.5 the three readings of `Expr.const` — done** | `Erases.lean`, `ErasesTotal.lean`, `ErasesAbstract.lean`, `ErasesStrengthen.lean`, `ErasesUniform.lean`, `ErasesEnv.lean` (co-owned with U2.8, which runs after: the `CtorOf` move and the dead `IotaInert`), `doc/rules-Erases.md` | U2.9 **(proof)**, U1.1, U1.2, U1.3 **(proof)** | 750 | `CtorOf` moves into `Erases.lean` beside `IndInfo`; `VDeclDefines`/`ConstOrigin` land as `01-DESIGN.md` §4.2 prints them; `Erases` has eleven arms (`#guard erasesArms%` lists `Erases.ctor`) with `const` re-keyed to `(hc : env.constants c = some ci) (ho : ConstOrigin env c)` — **positive**, so introduction needs no upstream lemma; `ctor_inv` and the three-alternative `const_inv` land; every transport lemma re-elaborates with its measured axiom set; `Erases.exists_of_trExprS_of_projInfo` re-proved, taking the classification as the explicit hypothesis `hclass` (U3.4 discharges it; invent no alternative); `doc/rules-Erases.md` gains the `Erases.ctor` row and its `erases_tConstruct` row is rewritten — it currently asserts the opposite of A17, and `Hygiene.checkTables` (`Tools/Hygiene.lean:280`) fails on an arm the table does not name; `grep -nE "\.case\|\.fix" LeanToLambdaBox/Erases.lean` empty; **two `_fires` witnesses** — `ctor` at a one-inductive fixture, and `const` with `ConstOrigin` exhibited from that fixture's own declaration list — **these two, with U2.6's five, are this wave's real test of the amendment**, since `green_G1` takes `hbridge` as a binder and constructs no `Erases`, `Lower` or `SEval` (`Green.lean:185`; refuter finding F4); `lake build LeanToLambdaBox.ErasesUniform` green; `lake exe hygiene --dup` = 0 |
| **U2.6 `SEval` = `[S Fig. 12]`'s `value_head`, and the ι split — done** | `SourceEval.lean`, `SubjectReduction.lean` | U2.5 **(proof)**, U1.4 **(proof)** | 650 | `CasesOnShape` lands as `01-DESIGN.md` §4.3 prints it; `ctorVal` is keyed on `CtorOf` **with `IndInfo` and Fig. 12's arity bound `harity : args.length ≤ np + nfs[k]!`** and loses `hnb`, the one side condition the tree's rule carries (`SourceEval.lean:181-185`; `hpat`/`hne` were a proposal and never landed, so no grep on them can fail); `indVal`/`sort`/`forallE` are added; ι carries `hsh`/`ho`/`hct`/`hpres`/`hmins` and the `extra` spine (A20, N20); `deltaC` gains `hnd : ∀ I dp nm, ¬ CasesOnShape env c I dp nm` (N21 — the source semantics quantifies over an abstract body table `bo`, so without `hnd` a saturated eliminator spine could have a second derivation that unfolds the eliminator); `SEval.mono`/`le`/`defeq` re-proved with no new binder and the same measured axioms; **five** `_fires` witnesses — ι at a two-branch `casesOn` with `CasesOnShape ``Nat.casesOn ``Nat 1 2` discharged from a concrete `VEnv.WF'` fixture (risk R17's test and the earliest point it can fail), ι at an **over-applied** `casesOn` (`extra ≠ []`), `ctorVal` at `Nat.succ`, `indVal` at `Nat` as a type argument, `forallE` inside a δ redex that has **no** derivation without the arm; two refutation witnesses — `untabled_const_not_value` (a body-less plain constant spine has no `SEval` value, the fact that keeps `axiom_free` off T5) and `overapplied_ctor_not_value` (`harity` fires) |
| **U2.7 the pass layer, fourteen arms — done** | `Lower.lean`, `LowerFix.lean`, `LowerCorrect.lean` (**deleted**), `ErasesLB.lean`, `doc/rules-Lower.md`, `test/Ledger.lean` | U2.9 **(proof)**, U1.5, U1.7 **(proof)** | 1,900 | `Lower` has fourteen arms as `01-DESIGN.md` §4.4 prints them: `ctorApp`, `ctorEta`, `elimEta`, `CtorDecl`, `ElimHeadOf`, `EtaSpine` **deleted**, `RuntimeKey` eliminator-only, `elimApp` `.const`-headed with `ElimDecl` and **keeping its `extra`**, `fixConst` guarded by `¬ RuntimeKey`, `ElimDecl` carrying its block clause; **`LowerCorrect.lean` is deleted as a file** — the simulation half goes, `BlockBodiesLambda`, the `Lower.source_*`/`target_*` inversion kit, the spine toolkit and the **`NoBox` family** (`:37-203`, consumed by `Capstone.lean:126,177` and `Green.lean:198`) move to `Lower.lean`, `LowerFixFixture.constToFix_needs_freshness` moves to `LowerFix.lean`, and its duplicate `ElimBody` head inversion (`:2229-2251` = `LowerFix.lean:871-885`) goes; `Lower.source_const` re-proved **by induction on the `Lower` derivation** with **two** alternatives under `BlockBodiesLambda` (the `fixBody` reading is excluded because `isLambda (.const kn)` is false — `hnk` alone is necessary, not sufficient, second-round fidelity F5) and `Lower.source_construct_nil` with two; `ErasesLB.ctor_head`/`.ctor` re-derived from `Erases.ctor` + `Erases.app` + `Lower.construct` (`hnul` and `ctor_head_needs_nullary` gone) and the two `*_eta` twins deleted; `LowerBlock.lambda_of_fixLambda` loses `hη`; `doc/rules-Lower.md` loses the `ctorApp`/`ctorEta`/`elimEta` rows, the `CtorDecl`/`ElimHeadOf`/`EtaSpine` entries and `lambda_of_fixLambda`'s `hη` deviation, and gains `fixConst`'s guard; `test/Ledger.lean` loses its `#print axioms` rows for `lower_correct_deltaChain` and `lowerFix_correct_atom` (`:24-25`), whose subjects die here; every deleted refutation recorded in a module header; `test/erasesLB.expected` regenerated, diff handed to the gate; **F-ETA2** filed in `doc/rework/03-DEV-FIX.md` (per N5: raised, never patched); `lake build LeanToLambdaBox.ErasesLB` green; `lake exe hygiene --dup` = 0 |
| **U2.8 the environment relation — done** | `ErasesEnv.lean`, `Output.lean`, `SpecEnv.lean`, `doc/trust.md`, `doc/coverage.md` | U2.5, **U2.6**, U2.7 **(proof)**, U1.8, U1.9 **(proof)** | 800 | `ErasesEnv` carries `defns`; `ErasesDecl.ctor` **deleted** and `ErasesDecl.elim` carries `hsh : CasesOnShape env c I dp nfs.length` (whence the **U2.6 edge**) and `hco : ConstOrigin env c` through the `c`-exposing `CasesOnOf'`; `LowerEnv` gains `specClosed`/`specBlocks` and `defsTotal` loses its `fix` disjunct (`01-DESIGN.md` §4.8); `constRefs` collects the block kername of `.construct`/`.case`/`.proj`, `ReachableFrom` stays `Decidable`, and **G1's closure is re-measured and printed in the unit report**; `ErasableAxioms`, `AxiomRealizer`, `axiomRealizerNames`, `axiomRealizerB`, `axiomRealizer_iff` **deleted** and **no `AxiomFree` landed** (it never landed: zero occurrences tree-wide) — in their place `NoBodylessRefs Σ t`, T9's decidable `axiom_free` analogue with no realizer whitelist (`01-DESIGN.md` §4.9, A24), which `doc/coverage.md` records as **failing on Fannkuch** (its `.ast` emits `Eq.rec` body-less) with F-EQREC as the shipping finding; `PrunedFor`, `EnvAgree` with its five lemmas and `IotaInert` **deleted** — zero consumers each; `doc/trust.md` loses its `ErasableAxioms`/`AxiomRealizer` rows; the threading kit `ReachableFrom.{subterm, app, alt, through_body, substList}` elaborates; the two new `LowerEnv` clauses exhibited on the G1 fixture; build target `lake build LeanToLambdaBox.SpecEnv` green (the tree is red until G2 swaps T9's premise, which is that gate's job) |
| **U2.10 the eliminator shape, without its evaluation theory — done** | `ElimBody.lean`, `Fuel.lean` (**deleted**) | U2.8 **(proof)** | 100 | `ElimBody.lean` keeps `fieldArgs`, `elimAlts`, `mkElimBody`, **`mkElimBodyRec`** (it is `ElimBody.recur`'s right-hand side, `:108,120`, feeds `ElimBody.closed` and is destructed by `LowerFix.lean:875,885`), the closedness chain, and criterion 7's three checked instances; it loses the ≈740 lines `01-DESIGN.md` §7.4 enumerates — the de-Bruijn/eval kit, the nine `wcbvEval_*` lemmas, the `mkCtorBody` family (dead once `ErasesDecl.ctor` goes, and `mkCtorBody_beta` goes through `wcbvEval_mkLambdas_fwd`, itself retired), `mkElimBody_iota_fwd`/`_bwd`, and the `*_iota_fires` fixtures. `Fuel.lean` is **deleted**: 101 lines, zero references tree-wide, no importer — the root import line goes to the gate (N3a). `grep -rn "mkCtorBody\|mkElimBody_iota\|wcbvEval_mkLambdas" LeanToLambdaBox/` empty; `#print axioms ElimBody.closed` unchanged; `lake build` green |
| **G2 gate — green_G2–G4, the merged `simulate` field, and T9's premise swap — done** | `Capstone.lean`, `Green.lean`, `VerifyBench/Spikes/{G2,G3,G4}.lean`, `test/{ErasesLBCheck.lean,erasesLB.expected,ledger.expected}`, `scripts/erasesLB.sh`; N3a files | U2.1–U2.10 **(proof)**, U1.8 **(proof)** | 650 | `ErasureBridge.simulate` and `.lowerCorrect` merge into the one field `01-DESIGN.md` §5 prints (T9's proof loses an `obtain`); T9's `hax : ErasableAxioms Σ t` is **replaced** by `hnb : NoBodylessRefs Σ t` and `Green.lean`'s `g1_erasableAxioms` by `g1_noBodylessRefs`, `by decide +kernel`; `erases_mkApps` deleted in favour of `ErasesLB.lean`'s `Erases.mkApps` and the spine premise folded per U2.2 (finding **G1-O3** retired); **`green_G1` still elaborates** — the standing obligation, re-measured after U2.5–U2.10. It is **not** the wave's test of the amendment and the gate does not report it as one: it takes `hbridge` as a binder (`Green.lean:185`) and constructs no `Erases`/`Lower`/`SEval`, so U2.5's two and U2.6's five `_fires` witnesses are what exercise the new rules. `green_G2`/`green_G3`/`green_G4` elaborate with literal peano answers; `hbridge` has **eight** fields (the merge of `simulate`/`lowerCorrect` from nine); `hcb` is discharged only at G1 and stays class-**C**, uninhabited at G2–G4 (their tabled bodies route through lean4lean's unproven `TrProj`); **`hev` is recorded as a class-**C** binder still uninhabited** (A14, second-round refuter F4) with its `test/ledger.expected` and `doc/trust.md` rows, discharged first at G3's `green_G5`; `lake exe green-check --all` green **on G1 only** (the rung registry, `Tools/GreenCheck.lean`, is G3's to extend — see G3's row); `lake exe hygiene --dup` exit 0; `lake exe hygiene --schedule` exit 1, one **pre-existing** inversion unrelated to this gate's edits (`CheckerAdequacy.lean`/`ErasureSpec.lean`, restated at U3.4's row below); `test/ledger.expected` re-measured; `doc/coverage.md` updated by hand (the generator is U5.4's) |

Two absorptions Task-level review might expect as new W2 units are not: landing the `Supported`
Prop and `supportedB_sound` is **U1.8's own completion**, not new W2 scope — it is a W1 unit still
in progress, and G2 only consumes it (above); and `FirstOrderInd` plus T9's `fo`-parameter swap
(finding **G1-O2**) is **U3.5's** (W3), since `FirstOrderInd.lean` needs the first-order domain
work that wave does. `NoBox` transport along the general `Lower` (finding **G1-O7**) is likewise
**U3.5's**, not a separate W2 unit: `01-DESIGN.md` §7.3 assigns `firstorder_no_box` to
`FirstOrderInd.lean`, and `ErasureBridge.firstorder`'s field (§5) already states box-freedom of
the *lowered* value, not the erasure, so that is the theorem the guard has to be proved into.

### W3 — the one simulation, first-order domain, witnesses, the fragment, and the upstream handoff (9 + gate)

**The wave's single theorem.** `erases_correct` (`01-DESIGN.md` §5, T5) is proved once, by one
induction on `SEval`, at the emitted `Σ`, with **eight binders and seven premises** — MetaRocq's
five plus `LowerEnv` plus `UpstreamAsks`. (W3 closed it under one further named premise,
`StepPremises`, whose six fields **W3R** retires by repairing the definitions that state them
backwards; see that wave's section and `05-REPAIRS-W3.md`.) Its arms are step lemmas taking the induction hypothesis as a parameter, and the
aggregator takes **those step lemmas as explicit hypotheses**, exactly as W4's U4.1 does (refuter
finding B-F6).

**The upstream handoff, and its one cost.** Editing the lean4lean fork is a separate agent's work
(U3.4's row, below): this wave can *file* the two load-bearing asks but cannot make the fork accept
them. Until the pin moves, `erases_correct` therefore carries an **eighth binder**,
`(A : UpstreamAsks env)` — U3.4's named, class-**C**, `doc/trust.md`-tracked stand-in for the two
asks (`01-DESIGN.md` §8.3) — everywhere `SEval.no_elimSpine_value` (the β arm, U3.1) or
`not_erasable_of_informative` (the ι/proj arms and T7, U3.2/U3.2b/U3.5) is spent. This is not a
premise of `IotaRelevant`'s shape: it is the two already-filed asks, unweakened, made explicit
rather than assumed. The pin bump discharges `A` and the binder drops with no restatement of
anything else — criterion 6's "statement never changes from W3 on" is read modulo that one,
reversible widening, and G3's acceptance says so rather than papering over it.

**The module graph, which is why no unit is blocked by another's file.** The first cut's three
files were circular: the arm files need the aggregator's spine-inversion kit, and the closing
instantiation needs the arms. Five files, acyclic (`01-DESIGN.md` §5, `04-AMENDMENT-W2.md` §6):

```
  ErasesCorrect/Steps.lean  (U3.1)   the inversion kit, Simulates, StepIota/StepProj/StepDelta,
        │                            SEval.no_elimSpine_value
  ErasesCorrect.lean        (U3.1)   erases_correct_of_steps + the ten structural arms
        ├── ErasesCorrect/Iota.lean  (U3.2)    step_iota
        ├── ErasesCorrect/Proj.lean  (U3.2b)   step_proj
        └── ErasesCorrect/Delta.lean (U3.3)    step_delta
  ErasesCorrect/Close.lean  (G3)     erases_correct, erases_correct_lb
```

The arm files import `Steps.lean` only; `Close.lean` imports all four. No unit edits a file it also
imports, and nothing is "stated and left" — U3.1's `sorry`-free acceptance is reachable inside its
own dependencies.

**U3.4 is scheduled first**: two upstream asks are load-bearing this wave (R14, R4) and the file
that hands them off — plus the `UpstreamAsks` structure every later unit consumes — must exist
before U3.1 states `erases_correct`. A refusal upstream does not stop the wave any more: it is not
a "day one" gate, since nothing in W3 is *blocked* on the fork accepting the ask — `UpstreamAsks`
lets the wave proceed with the cost named above. **U3.8 is scheduled second**: a failed N19 verdict is what would force an
η arm back into `Lower` (R15), and an N21 failure would empty a rung (R20); both are cheaper to
learn before the ι arm is written than after.

| Unit | Files owned | Depends | Est. | Acceptance |
|---|---|---|---|---|
| **U3.4 upstream handoff and named premises — first** | `doc/upstream-asks.md`; **new** `LeanToLambdaBox/Upstream.lean` (`UpstreamAsks`); **new** `LeanToLambdaBox/Origin.lean`; `doc/trust.md` | W2 | 250 | Editing the lean4lean fork is a separate agent's work — this unit **files asks, it does not edit the fork or bump `lake-manifest.json`**. `doc/upstream-asks.md` lists `VEnv.IsDefEqU.const_arity_inv` (ask 6), `VEnv.WF'.consts_origin` (ask 2), `VEnv.WF'.defeqOwn` (ask 1), the seven `CheckerAdequacy` kernel-generic declarations (ask 3), and the three lemmas U2.6 parked in `SourceEval.lean` (`IsArity.piBody_sort`, `CtorOf.constant_ctorResult`, `CtorOf.not_indInfo`, filed for consolidation, not load-bearing) — each with a full Lean statement. `Upstream.lean` holds `structure UpstreamAsks (env : VEnv) : Prop` with one field per load-bearing ask (2 and 6 only; 1 and 3 have no W3 consumer), docstring stating it is discharged by the re-pin with no change to any consumer's statement shape. `Origin.lean` holds the five corollaries `UpstreamAsks.constsOrigin` feeds — `constOrigin_not_ctorOf`, `constOrigin_not_indInfo`, `IndInfo.inj`, `CtorOf.inj`, `CasesOnShape.inj` — plus the totality direction U2.5's `hclass` needs (`consts_classified`), each now taking `(A : UpstreamAsks env)` explicitly rather than assuming the fork has already changed; `#print axioms` recorded for each (footprint: `A`'s own class-**C** status, nothing inherited). `doc/trust.md` gains the `UpstreamAsks` row: the ledger cannot measure a hypothesis, so provenance lives here. **This is not the `IotaRelevant` premise the reference spec forbids**: it is the two already-filed asks, unweakened, made an explicit, tracked binder instead of an assumption that the fork has already moved — reversible with no restatement once it has |
| **U3.8 the fragment — second** | `Supported.lean`, **new** `LeanToLambdaBox/CasesNames.lean`, `LeanToLambdaBox/SourceEval.lean` (one-line import only — co-owned with U2.6, W2, done), `doc/coverage.md` | W2 | 450 | **Layering fix** (`01-DESIGN.md` §2.4 finding W2b-F6): relocate `isCasesOnName`/`lastComponent` out of `Supported.lean` into the new leaf module `CasesNames.lean`, and swap `SourceEval.lean`'s `import LeanToLambdaBox.Supported` for `import LeanToLambdaBox.CasesNames` (the only reason it imported `Supported.lean` at all) — this removes the shipping-code closure (`ErasureSpec`/`CheckerAdequacy`) from `SubjectReduction`'s and `ErasesCorrect`'s import closures, closing the wave-early layering gap §2.4 named. `supportedB` gains the **N19** conjunct (no under-applied constructor or eliminator occurrence) **and the N21 rejection of recursor heads** — `Supported.lean:239` is `else if isRecursorName tbl c then .ok ()`, which lets through a constant that has no `SEval` derivation at all (tabled body-less, no value arm, no ι rule), so a program reaching one is **vacuously** green — each with its soundness lemma into `Supported`; the verdict is computed and recorded for all five VerifyBench programs, and `doc/coverage.md` states per program whether **N19**, **N20** and **N21** hold. N20's row records the measurement honestly: its decidable sufficient condition **fails on all five**, because Lean's match compiler thunks a nullary branch into an *application* (`Arith.ast`'s `Nat` zero-branch is `(tApp (tRel 1) (tConst Unit.unit))`; no nullary alternative anywhere has a `tLambda` head), so `hmins` is discharged semantically per unselected branch — a cost that Lean's totality makes payable, not a vacuity, and partial/`unsafe` bodies are outside through N8. F-ETA2's row cites the N19 verdict. **If N19 fails on a tracked program**, the unit stops and reports: the contingency (one non-nesting `elimEta` arm plus one collapse lemma, ≈300 lines) is scoped in `04-AMENDMENT-W2.md` §12 and belongs to U2.7's owner. **If N21 fails**, the program leaves the fragment and the row names the construct that took it out |
| **U3.1 the simulation — aggregator and structural arms** | **new** `ErasesCorrect/Steps.lean`, `ErasesCorrect.lean` | W2 **(proof)**, U3.4 (interface) | 1,100 | `Steps.lean` receives `erases_mkApps_inv`, `erasable_mkApps`, `erases_correct_box`/`_boxSpine` and the spine helpers from `ErasesCorrect.lean` (so the arm files reach them without importing the aggregator) and lands `Simulates`, `StepIota`/`StepProj`/`StepDelta` and `SEval.no_elimSpine_value` exactly as `01-DESIGN.md` §5 prints them; `erases_correct` is **stated** there too — seven binders, six premises, **plus the eighth `(A : UpstreamAsks env)` U3.4 hands off** (dropped with no restatement once the pin moves), none named `Supported`/`Relevant`/`Iota*`/`*Consistent`/`*Hyps` — and `erases_correct_of_steps` is proved by `induction hev` with **every** non-hypothesis case discharged: `lam`/`sort`/`forallE`/`ctorVal`/`indVal`/`box`/`app`/β/ζ/`lit`, re-using U2.3's bodies. Three are new work: `ctorVal` (the value's image is `mkApps (.construct iid k []) cargs₀`, built by `WcbvEval.construct_atom`/`construct_app`, whose arity side condition is the rule's own `harity` — **no upstream lemma**); `indVal` (an inductive-name spine has no head erasure, so `erases_mkApps_inv` leaves only the boxed-prefix case and `mkApps_box` folds); and the β arm's **`Lower.elimApp` reading**, which at `extra ≠ []` re-associates into `app`-congruence and at `extra = []` is killed by `SEval.no_elimSpine_value` (`A.constsOrigin`) from `ErasesDecl.elim`'s `hsh`/`hco` (second-round fidelity F6; R19). **`specBlocks` obligation** (`01-DESIGN.md` §2.4 finding W2b-F1): `LowerEnv.specBlocks : BlockBodiesLambda Σ⁺` as printed is unsatisfiable on every real `Σ⁺` (U2.8 machine-checked it); if `Steps.lean`'s spine-inversion kit spends it before `Iota.lean` does, restate the consuming lemma's premise per the repair option named there rather than carrying the unsatisfiable clause forward silently. `erases_correct_lb` stated over `ErasesLB`; T5's row of `test/ledger.expected` committed and pinned from here on (criterion 6); `#print axioms` in the class-**B** set (plus `A`'s own class-**C** status); `_fires` witnesses for `ctorVal` and `indVal`; `lake build LeanToLambdaBox.ErasesCorrect` green; `grep -rn "sorry\|axiom " LeanToLambdaBox/ErasesCorrect.lean LeanToLambdaBox/ErasesCorrect/Steps.lean` empty |
| **U3.2 the ι arm** | **new** `ErasesCorrect/Iota.lean` (imports `ErasesCorrect/Steps.lean`) | U3.1 (interface), U3.4 (interface), U2.7, U2.8 **(proof)** | 1,600 | `step_iota` elaborates against `StepIota`, by the six steps of `04-AMENDMENT-W2.md` §6: `erases_mkApps_inv` split; boxed prefix via `erasable_mkApps` + `WcbvEval.mkApps_box`, consuming N20's premises and **adding no premise of its own**; head via `Lower.source_const` under `LowerEnv.specBlocks` — an induction on the `Lower` derivation, not a three-arm check, since `Lower.fixBody`'s source is constrained only by `hj` (`Lower.lean:228-239`); **`specBlocks` obligation** (`01-DESIGN.md` §2.4 finding W2b-F1): as printed it is unsatisfiable on every real `Σ⁺` (U2.8), so this step is the one most likely to need the repair — restrict `BlockBodiesLambda` to the pass's own emitted blocks, or state the obligation and report rather than carrying a vacuous premise — plus the ι rule's own `ho : ConstOrigin env con` through `constOrigin_not_ctorOf` (`A.constsOrigin`, U3.4's `UpstreamAsks`; **not** `hsh`, which fixes only the head's name) and `CasesOnShape.inj` for the split; **over-application handled, not excluded**: `extra` rides outside the node as `elimApp` carries it, and the branch rewrite runs under `wcbvEval_mkApps_head_congr` (`IotaBridge.lean:40-44`); discriminant via `not_erasable_of_informative` (takes `A.constArityInv`) and `specBlocks`, with saturation from `hdiscr`'s own `harity` rather than from the upstream lemma; node facts via `IndBodyOf`/`LowerEnv.inds`; branch via `LowerAlt` + `wcbvEval_mkApps_mkLambdas_substList` + `WcbvEval.lbClosed` + `WcbvEval.iota`; `grep -rn "IotaRelevant\|IotaShape" LeanToLambdaBox/` empty; `not_erasable_of_informative` is a theorem **taking `A` explicitly**, not a binder of its own beyond that, and is stated here for U3.5 too; `_fires` witnesses at the saturated and at the over-applied `casesOn` fixtures U2.6 built; `#print axioms` class-**B** plus `A`'s class-**C** status — no `sorryAx` inherited while the pin has not moved, since nothing here assumes it has. If it overruns 1,600 by more than half, stop and report rather than adding a premise |
| **U3.2b the proj arm** | **new** `ErasesCorrect/Proj.lean` (imports `ErasesCorrect/Steps.lean`) | U3.2 **(proof)** | 400 | `step_proj` elaborates, re-using `not_erasable_of_informative` and the `propositional = false` fact and nothing else; its `TrProj` obligation runs through the part of lean4lean's `Verify` layer that is entirely unproven, and the unit's report states exactly which `sorryAx` roots that adds (`doc/trust.md` row handed to the gate); a `_fires` witness on a structure fixture |
| **U3.3 the δ arm, including recursion** | **new** `ErasesCorrect/Delta.lean` (imports `ErasesCorrect/Steps.lean`) | U3.1 (interface), U2.7, U2.8 **(proof)** | 700 | `step_delta` elaborates for both target shapes — `Lower.const` (δ at `Σ` through `LowerEnv.defsTotal` and `wcbvEval_mkApps_head_congr`) and `Lower.fixConst` (`fix_atom` at the empty spine via `Lower.fixBody` + the now-unconditional `LowerBlock.lambda_of_fixLambda`; `fix_guarded` at a non-empty spine via `LowerFix.constToFix`/`Lower.fixUnfold`); neither route spends `LowerEnv.specBlocks` directly (`hfl`/`LowerBlock.lambda_of_fixLambda` supply what `Lower.fixUnfold` needs unconditionally), but **if `specBlocks`'s repair (§2.4 finding W2b-F1, U3.1's row) changes `BlockBodiesLambda`'s statement, re-check this file's `LowerBlock`-based reasoning against the new form before relying on it being unaffected**; the level-instantiation step consumes `ErasesEnv.defns` and is the only place the `instantiateLevelParams` axiom cluster appears (its `doc/trust.md` row handed to the gate); `_fires` witnesses at a recursive and a non-recursive constant |
| **U3.5 first-order** | `FirstOrderInd.lean`; co-owns `Capstone.lean` for the `fo`-parameter swap (finding **G1-O2**) | U3.4 (interface), **U3.2 (proof — `not_erasable_of_informative`)**, W2 | 650 | `example : firstOrderIndB arithTable 64 ``Nat = true := by rfl`, likewise `Bool` and `BinaryTrees`' `Tree` (criterion 8 as amended by A6/A15); `firstorder_erases_deterministic` on the eleven-rule `Erases`, where a first-order value's image is unique because a competing `const` derivation's `ConstOrigin` contradicts `CtorOf` through `Origin.lean`'s `constOrigin_not_ctorOf` — takes `(A : UpstreamAsks env)` like every other consumer of that corollary; `firstorder_no_box` proved of the **lowered** value (finding **G1-O7**), consuming the same `not_erasable_of_informative` as U3.2 — stated once, used twice, `A` threaded through unchanged; `Capstone.lean`'s `{fo : Name → Prop}` instantiated with no reproof of `shipping_erase_correct_firstorder` |
| **U3.6 lowerenv-from-records** | `ColdStartShape.lean` (re-lands `RegInvShape'` adapted), `ErasesEnv.lean`, `SpecEnv.lean` | U2.8 **(proof)** | 750 | `SpecEnv.exists` elaborates from `RegInvShape'` + `ErasureSpec.lookup_adequate` + `htbl`, and discharges `ErasesEnv.defns` from the run's own registry and `ErasesDecl.elim`'s `hsh` from the source table's inductive data; `LowerEnv Σ⁺ s'.gdecls` is **derived** — including `defsTotal` without its `fix` disjunct and the two new clauses `specClosed`/`specBlocks` — not assumed, and if `specBlocks` is derivable from the registry's own shape at all (block members are the recursive definitions, whose compiler bodies are λs) that derivation is where `01-DESIGN.md` §2.4 finding W2b-F1 is finally closed rather than merely worked around; if it is not derivable there either, report rather than assuming it, per that finding's own unit spec (`U3.6.md`); `patHead`/`PatOf` (`ErasesEnv.lean`, consumer-free since U2.5 deleted `IotaInert` — §2.4 finding W2b-F5) are **deleted** in this unit's pass over the file; `EnvAgree`, `WcbvEval.congr_env` and `PrunedFor` are **not** deliverables — they are deleted at U2.8 for want of a consumer |
| **U3.7 TrExprS-witnesses** | `Witness/TrWitness.lean` | U1.8 | 500 | `arith_trExprS : TrExprS env [] [] eArith ve` produced by routing lean4lean's checker (`M.WF.run'`, `VState.WF.initial`); **or** the named fallback lands (class-**D** binders, the two ledger/trust rows, A14 re-amended in the same commit — risk R11) |
| **G3 gate — green_G5–G6, the first ι rung, and the closing of T5** | `VerifyBench/Spikes/{G5,G6}.lean`, `Green.lean`, `Capstone.lean`, **new** `ErasesCorrect/Close.lean`, `Tools/GreenCheck.lean` (extend the rung registry to G2–G4 and G5–G6 — G2's outstanding item, `01-DESIGN.md` §6); N3a files | U3.1–U3.8 **(proof)** | 600 | `erases_correct` is closed: `Close.lean` instantiates the aggregator's step hypotheses with U3.2/U3.2b/U3.3's lemmas and the theorem stands with **no hypothesis beyond its seven binders and the eighth, `A : UpstreamAsks env`**, U3.4's — this is where criterion 6 is met (modulo `A`, which drops with no restatement once the pin moves) and T5's row of `test/ledger.expected` is re-pinned; **`green_G5` — a `match`, hence `.case`, ι and the amended `SEval.iota` — is attempted in the same gate that takes U3.2's arm, not deferred**; `green_G6` (`Nat.add`, hence `_unsafe_rec`, `deltaC`, `.fix`) elaborates with a literal answer; G1–G4 still green; `lake exe green-check --all` checks **all six** rungs now that `Tools/GreenCheck.lean`'s registry is extended; one file constructs a pats-carrying `VEnv.WF` with every ι-round premise, retiring review findings P1 and TA-06 by construction; U3.8's N19/N20 verdicts are reflected in `doc/coverage.md`; **criterion-21 grep is not run** — `CheckerAdequacy.lean`'s `Lean4Lean` namespace block stays until the fork accepts U3.4's asks (`01-DESIGN.md` §8.3 item 3, F16), and `doc/trust.md` records the deferral rather than a passing check that isn't one; `test/ledger.expected` matches; **`hev` stops being an uninhabited binder**: `green_G5` constructs the first `SEval` derivation, discharging `CasesOnShape`, `ho`, `hct` and N20's per-branch obligations, and the A14 ledger row G2 opened is closed or re-stated with the rungs that still carry it |

### W3R — the repair wave (9 + gate)

**What the wave is for.** W3 closed T5 under one named premise, `StepPremises`, whose six fields
are each a fact a specification relation states in the wrong direction or a datum a source rule
leaves free; W2b-F1's `LowerEnv.specBlocks` is still refuted, `Erases.proj` is false at a
propositional structure, and `SourceTableAdequate` is uninhabited on a matcher-bearing
declaration, which is what stops a rung on a tracked program. W3R repairs the definitions in the
files that own them. The target is one line: after the gate, `erases_correct`'s premises are
MetaRocq's five, `LowerEnv`, and `UpstreamAsks` — no bundle, no forward-reading structure, no
`specBlocks`. Decisions, evidence and full signatures: `doc/rework/05-REPAIRS-W3.md`; unit specs
`U3R.*.md`, gate `G3R.md`.

**Delivered**, all nine units and the gate. `erases_correct` closes exactly on the target line:
`ErasesCorrect/Close.lean` states it as `ErasesCorrectStmt env bo Us fl Γspec Γ` with no explicit
argument, `#check @erases_correct`/`erases_correct_target_shape` pinned by `test/
erases_correct.expected` (new, `scripts/erases_correct.sh`, new). `StepPremises` and its six
fields (`ErasesEnvFwd`, `IndSpineNotProp`, `SpecElims`, `ElimTyping`, `ProjSpec`,
`TabledNotCtor`) are gone tree-wide, and so are `ErasesDecl`, `BlockBodiesLambda`,
`LowerEnv.specBlocks`, `CasesOnOf`/`CasesOnOf'`. Delivered files, by unit: **U3R.1**
`Erasability.lean` (new: `vResultSort`, `neverZeroB`, `InformativeInd`), `Erases.lean` (`IndArity`,
`IndInfo.arity`, `Erases.proj`'s `hinf`, `erases_proj_needs_informative`), `ErasesTotal.lean`
(`ProjInfo.proj`'s two new conjuncts), `Supported.lean` (`succSortB`); **U3R.2** `SourceEval.lean`
(`MajorPremiseAt`, `CasesOnShape`'s third conjunct, `SEval.iota`/`.proj`'s `IndArity`/
`InformativeInd`, the `NatWitness`/`ProjWitness` fixtures), `SubjectReduction.lean`; **U3R.3**
`Lower.lean` (`LowerBlock.hfl`, `ElimDecl.uniq`, `LowerCtorBodyFixture`, and the six declarations
relocated in from `LowerFix.lean`: `isLambda_toBvar`, `isLambda_closeFix`,
`ConstToFVar.isLambda_eq`, `LowerBlock.targetLambda_of_fixLambda`, `Lower.source_isLambda`,
`LowerBlock.lambda_of_fixLambda`), `LowerFix.lean`; **U3R.9** `Witness/SourceTable.lean`
(`Expr.AlphaEq`, `Expr.alphaEqB`, `ReifiedDecl.Prepared` modulo α), `Tools/Reify.lean`; **U3R.4**
`ErasesEnv.lean` (`ErasesEnv`'s seven clauses, `IndCovered`, `SpecContent`,
`SpecContent.erasesEnv`), `ColdStartShape.lean`, `SpecEnv.lean` (`SpecEnv` re-keyed to
`SpecContent`, `SpecEnv.erasesEnv`'s three premises, `RegInvShape'.defns`/`.erasesEnv`/
`.lowerEnv`); **U3R.5** `Upstream.lean` (`UpstreamAsks`'s four fields, `IndBlockBelow`, `Peel`),
`Origin.lean` (`indSpine_not_prop`, `not_erasable_of_informative`, `CasesOnShape.agree`,
`IndArity.inj`, `constants_of_tabled`, `constOrigin_of_constants`, `peel_piSpine_head`,
`MajorPremiseAt.instL`, `majorPremiseAt_of_piBinders`), `doc/upstream-asks.md`, `doc/trust.md`;
**U3R.6** `ErasesCorrect/Iota.lean` (`step_iota`), `ErasesCorrect/Proj.lean`
(`step_proj`); **U3R.7** `ErasesCorrect/Steps.lean` (`ErasesEnv.runtimeKey_isCasesOn`,
`erases_elimSpine_no_value`, `erases_constSpine_value`/`_head`, `not_mkApps_const`,
`ErasesEnv.ctorArity`, the five closure-kit lemmas, `Lower.appReady`, the five lemmas relocated
in from `Delta.lean`), `ErasesCorrect/Delta.lean` (`step_delta`), `ErasesCorrect.lean`;
**U3R.8** `FirstOrderInd.lean` (`fOFields_of_asks`); **gate** `ErasesCorrect/Close.lean`,
`Green.lean`, `test/{Ledger.lean,ledger.expected,erases_correct.expected}` (34 ledger rows),
`scripts/erases_correct.sh`. One declaration `01-DESIGN.md` §2.4 scheduled for this wave was
not landed as first printed and is recorded as a delivery finding rather than silently
resolved (`05-REPAIRS-W3.md` §17): `constOrigin_of_tabled` does not exist, replaced by
`constants_of_tabled` + `constOrigin_of_constants`, blocked on filed ask 4. `IndArity.inj`
(landed inside U3R.6's files) and `peel_piSpine_head`/`MajorPremiseAt.instL`/
`majorPremiseAt_of_piBinders` (landed inside U3R.8's file) are placed above in their settled
home, `Origin.lean`, folding in a rename-free relocation onto their natural site beside
`CasesOnShape.agree`/`peel_piSpine`/`MajorPremiseAt.inst`.

**The wave was refuted before any unit ran and re-planned against the refutation.** Two of the
thirteen findings are kernel-checked: the relevance criterion on `Erases.proj` cannot be the
syntactic `InformativeInd` (refuted at `Prod` and at 11 of 24 measured `.proj` heads), and the
proposed `ErasesEnv.elimsOnly` clause is false at a constructible Γ. Both amendments are folded
in below; `05-REPAIRS-W3.md` §16 answers every finding. The re-planning is visible in three
places: U3R.1 grows (the relevance vocabulary is a definition change, not a premise), U3R.4 is
re-budgeted from 900 to 1,300 (`ErasesDecl` is read by *inversion* in `RegInvShape'.defns`, ~14
sites, not re-packed at 5), and U3R.2 owns one more restatement (`SEval.no_elimSpine_value`).

**The tree is red between the units and the gate**, by construction: U3R.1's arity change and
U3R.4's relation change touch files their owners re-prove later in the wave. Each unit's own
build target is green at its own boundary, the gate's is the tree. **G1-G6 must be green at the
gate and are not required to be green inside the window**; G4 in particular is inhabitable only
under U3R.1's amended criterion, which is why U3R.1 lands it and not a later unit.

| Unit | Files owned | Depends | Est. | Acceptance |
|---|---|---|---|---|
| **U3R.1 relevance, semantically** | `Erasability.lean`, `Erases.lean`, `ErasesTotal.lean`, `ErasesUniform.lean`, `ErasesStrengthen.lean`, `ErasesAbstract.lean`, `Supported.lean`, `ErasesCorrect/Iota.lean` (the `IndDeclOf` deletion only, co-owned with U3R.6), `doc/rules-Erases.md` | — | 650 | `InformativeInd` becomes `IsNeverZero` on the declared result level, with `neverZeroB` **sound and complete** and `informativeInd_of_succ`; `Erases.proj` gains `hinf` (`01-DESIGN.md` §4.2); `IndArity`/`IndInfo.arity` land beside `IndInfo`; `vResultSort`/`InformativeInd`/`neverZeroB` move to `Erasability.lean` and `IndDeclOf` into `Erases.lean`, with `InformativeInd.mono`; `Supported.lean`'s `informativeB` becomes the never-zero test and `succSortB` the successor one; `informativeInd_of_tabled` re-proved; `ProjInfo.proj` gains the conjunct so totality still closes; `lake build LeanToLambdaBox.Supported` green; the refutation witness `erases_proj_needs_informative`; `--tables` 0 |
| **U3R.2 the two source rules** | `SourceEval.lean`, `SubjectReduction.lean`, `ErasesCorrect/Steps.lean` (`SEval.no_elimSpine_value` only, co-owned with U3R.7) | U3R.1 (interface) | 700 | `SEval.iota` gains `IndArity` + `InformativeInd`, `SEval.proj` gains `CtorOf` + `IndArity`, `CasesOnShape` gains `MajorPremiseAt` (§4.3); `SEval.no_elimSpine_value` restated on `bo c = none` (`05-REPAIRS-W3.md` §1); `SEval.mono`/`.le`/`.defeq` re-proved and `#print axioms SEval.defeq` unchanged; `NatWitness` discharges the new `CasesOnShape` clause; `SpikeNatFacts`-shaped relevance is `rfl`-grade at the fixture; a proj `_fires` witness |
| **U3R.3 the pass relation's blocks** | `Lower.lean`, `LowerFix.lean`, `doc/rules-Lower.md` | — | 700 | `LowerBlock` gains `hfl` — the **emitted** definitions' λ-headedness, `LBWfPeregrine.fixLambda`'s clause at this block — and `BlockBodiesLambda` is deleted (§4.4); `lambda_of_fixLambda`/`targetLambda_of_fixLambda` lose their `hfl` *argument* and keep their statements; `Lower.notFix_of_block`, `ne_fix_of_block` and the whole `Lower.source_*` kit lose `hblk`; `ElimDecl.uniq` lands; `grep -rn "BlockBodiesLambda" LeanToLambdaBox/` empty; `fixdefs.py` re-run and quoted (51/51, after building the five `VerifyBench` roots — five of the eleven `.ast`s are build artefacts) |
| **U3R.4 `ErasesEnv` forward** | `ErasesEnv.lean`, `ColdStartShape.lean`, `SpecEnv.lean` | U3R.1 **(proof)**, U3R.2 (interface), U3R.3 **(proof)** | 1,300 | `ErasesDecl` and `ErasesEnv.decls` deleted, **seven** clauses (`keys`, `deps`, `tabled`, `defns`, `axioms`, `blocks`, `elims`) — `axioms` is `ErasesDecl.ax` forward, `elimsOnly` is **not** a clause and `ErasesEnv.runtimeKey_isCasesOn` is its theorem (§4.8); `RegInvShape'.defns` **rewritten**, not re-packed (it is an inversion on `ErasesDecl`); `LowerEnv.specBlocks` deleted; `IndCovered` strengthened, keeping `InformativeInd` in its hypotheses; the acceptance fixture is an environment with a block **and** an eliminator entry — G5's specification environment (`refute3/joint.lean`'s `g5Spec`), not `demoEnv`; `lake build LeanToLambdaBox.SpecEnv` green |
| **U3R.5 the kernel asks** | `Upstream.lean`, `Origin.lean`, `doc/upstream-asks.md`, `doc/trust.md` | U3R.1 **(proof)**, U3R.2 **(proof)** | 600 | `UpstreamAsks` gains `mkAppsInv` and `indSpineInj` (asks **9** and **10**) and `constsOrigin` gains its two declaration-level conjuncts — **no `TrEnv'` field**, that ask is withdrawn (§8.3); `Origin.lean` proves `indSpine_not_prop`, `not_erasable_of_informative` (moved down), `elim_major`, `ctor_saturated`, `CasesOnShape.agree`, `constOrigin_of_tabled`, each taking `A`; the `VLevel.inst`/`eval` substitution lemma and the `mkApps`/`instL` commutation lemma land beside their consumers; `doc/trust.md` loses the rows for the six retired premises; **acceptance on axioms is "same roots as the W3 checkpoint, no new root"** — `[propext, Classical.choice, Quot.sound]` is unsatisfiable and was measured so (`refute3/ax_now.lean`) |
| **U3R.6 the ι and proj arms** | `ErasesCorrect/Iota.lean` (co-owned with U3R.1 for the `IndDeclOf` deletion), `ErasesCorrect/Proj.lean` | U3R.1-U3R.5 **(proof)** | 500 | `SpecElims`, `ElimTyping`, `ProjSpec`, `IndSpineNotProp` deleted; `example : StepIota env bo Us fl Γspec Γ := step_iota` typechecks, same for `step_proj`; `#print axioms` on both keeps exactly the five `sorryAx` roots of the W3 checkpoint; both files' `_fires` witnesses still fire |
| **U3R.7 the δ arm, motive and aggregator** | `ErasesCorrect/Delta.lean`, `ErasesCorrect/Steps.lean` (co-owned with U3R.2), `ErasesCorrect.lean` | U3R.1-U3R.5 **(proof)** | 500 | `ErasesEnvFwd` and `TabledNotCtor` deleted; `erases_elimSpine_no_value` proved from `defns`/`axioms`/`elims` + `erases_ne_elimBody` + `ElimDecl.uniq` — **no `elimsOnly`** — and `ErasesEnv.ctorArity` lands, each with a use in an arm; `StepDelta` gains the `UpstreamAsks` prefix; `erases_correct_of_steps` takes exactly three hypotheses and `ErasesCorrectStmt` is unchanged; the closure kit re-proved over seven clauses |
| **U3R.8 T7 without `FOFields`** | `FirstOrderInd.lean` | U3R.1 (interface), U3R.5 **(proof)** | 300 | `FOFields` deleted, `fOFields_of_asks` proved off asks 9/10 and ask 2's uniqueness conjunct; `foMemberB` reads `succSortB` and `FirstOrderInd.informativeInd` goes through `informativeInd_of_succ`; T7's two theorems take `A` and nothing else beyond MetaRocq's list; `#print axioms firstorder_erases_deterministic` keeps `IsDefEq.uniqU`/`TrExprS.uniq` as its only `sorryAx` roots; the header records that `firstOrderIndB_sound` is blocked on **filed ask 4** |
| **U3R.9 the table modulo α** | `Witness/SourceTable.lean`, `Tools/Reify.lean` | — | 250 | `Expr.AlphaEq` (inductive; binder names and binder info only, **no `mdata` arms** — `SEval` has no `mdata` arm and the deferred transport would be false); `Prepared`/`body?_prepared` conclude it; `reify --check`'s pass condition becomes `==` and it also runs `partial def Expr.alphaEqB`, one arm per constructor, reporting disagreement with `eqv` as a hard mismatch; the unit report quotes a PASS on a `match`-bearing subject and on `Nat.add`, where the W3 checkpoint FAILs |
| **G3R gate — `erases_correct` with no bundle** | `ErasesCorrect/Close.lean`, `Green.lean`, `Capstone.lean`, `LeanToLambdaBox.lean`, `test/Ledger.lean`, `test/ledger.expected`, `doc/coverage.md`, `doc/trust.md` (co-owned with U3R.5), `Tools/GreenCheck.lean` | U3R.1-U3R.9 **(proof)** | 450 | `StepPremises` deleted and `erases_correct = erases_correct_of_steps step_iota step_proj step_delta`; the mechanical premise check `example : ∀ {env bo Us fl Γspec Γ}, ErasesCorrectStmt … := fun {..} => erases_correct` **elaborates** (it fails today, `H` being explicit at `Close.lean:58`) and `grep -rn "StepPremises" LeanToLambdaBox/` is empty; `lake build` green tree-wide; **G1-G6 all re-elaborate** with `g5_seval` threading `SEval.iota`'s `hnp`/`hinf` and no rung premise changed; `.ast` files byte-identical and `green-check --all` 0; ledger re-measured; `doc/coverage.md`'s stale five-program rows replaced by the re-measurement (Arith **inside** the fragment) with the N22 row added, the `Prod` false-exclusion paragraph **deleted** (the never-zero criterion removes it) and the matcher-free-subjects paragraph rewritten; `--schedule`/`--dup`/`--tables` 0 |

### W4 — the bridge (6 + gate)

**Structural prerequisite, and it is a deliverable in its own right.** The old
`VisitExprRefines.lean` re-lands split. Measured at `git show 2006835~1:LeanToLambdaBox/
VisitExprRefines.lean` — the recovery source for every proof script in this wave — it is 4,641
lines and 88 top-level declarations, of which one, `visitExpr_refines_erases_core`
(lines 1901-3645), is the 1,744-line eighteen-motive induction; the two applied statements
`visitExpr_refines_erases` (3645) and `visitExpr_refines_erases_block` (3711) follow it, and the
run plumbing (`run_mkAlt`, `run_mapM_fvar_to_name`, `subarray_next?_facts`, the `Supported.*_inv`
kit) precedes it. `Motives.lean` defines `Motives f` (the eighteen conjuncts for an arbitrary
eraser family `f` — seventeen against `ErasesLB`, motive 6 against `ErasesLBFix`), each step
becomes a standalone lemma `step_… : Motives f → Motive… (F f)` in one of three files, and
`VisitExprRefines.lean` shrinks to the ~300 lines that state the two T8 conjunctions (§5) and
apply the steps. Only then are motives parallelisable. Proof scripts are recovered from that
revision and adapted: the introduction-lemma renames of §4.7 for seventeen, genuinely new work
for motive 6.

**What W3R changes here, and it is not cosmetic.** The old motive 10 concludes
`Erases … (.proj tn i e) r` from `Γ.projs tn = some (iid, np)` and `Γ.ctorFields iid = some [nf]`
alone. `Erases.proj` now also demands `InformativeInd env tn` (`01-DESIGN.md` §4.2), which the
run's `ErasureCtx` does not record, so the motive needs it from the environment side: either a
coherence clause of `BridgeInv`/`ErasureCtx` discharged from the source table, or — the
principled form, since the eraser emits a `.proj` node for a propositional structure and the
target cannot reduce it — a **`Supported` clause**, N18's projection half, decided by
`informativeB` on the table exactly as the `casesOn` half is. U4.4 owns the choice and the
measurement (how many `.proj` nodes across the five `.ast`s have a non-informative head; the
prediction from `doc/coverage.md`'s `Prod` note is zero, with `Prod` itself a false exclusion of
`informativeB`'s syntactic successor test). Motives 4-6 target the **seven-clause** `ErasesEnv`
(§4.8), through `SpecContent`/`IndCovered` rather than a `decls` re-packing: `blocks`/`axioms`
are `SpecContent`'s own declaredness-keyed clauses once `deps` supplies presence, `elims` is
`IndCovered.elims` at the registered inductive, and only `tabled`/`defns` are not registry facts
at all — U4.2's own obligation, off `constants_of_tabled`/`constOrigin_of_constants`, since no
theorem named `constOrigin_of_tabled` exists (`05-REPAIRS-W3.md` §17 WD6).

| Unit | Files owned | Depends | Est. | Acceptance |
|---|---|---|---|---|
| **U4.1 motive-split + BridgeInv** | `VisitExprRefines/Motives.lean`, `VisitExprRefines.lean` (aggregator), `Bridge.lean` (re-lands `BridgeInv`, 7 of the old 10 fields; the `fixvars` field's content is now `ErasesLBFix`'s `kns`/`ids` indices) | W3 **(proof)** | 900 | `Motives` is defined and both `visitExpr_refines_erasesLB` and `visitExpr_refines_erasesLBFix` are stated (§5), with the eighteen steps as **explicit hypotheses** of the aggregator (no `sorry`, no named holes — `#print axioms` on the aggregator = `[propext, Classical.choice, Quot.sound]`); `BridgeInv`'s binder list contains no `*Hyps` other than `ErasureSpec` |
| **U4.2 motives-env (4, 5, 6) — first** | `VisitExprRefines/Step/Env.lean` | U4.1, **W3R U3R.4 (proof)** | 1,200 | the three environment-facing steps elaborate — motive 6 against `ErasesLBFix` — against the **seven**-clause `ErasesEnv`, taken through `SpecContent`/`IndCovered` (`01-DESIGN.md` §4.8): `blocks`/`axioms` come from `SpecContent`'s own clauses once `deps` supplies declaredness, and `elims` from `IndCovered.elims` at the registered inductive (U3R.4's `RegInvShape'`/`SpecEnv`) — **this unit owns the two clauses that are not registry facts, `tabled` and `defns`**, the gap G3R's `ErasesEnv` inhabitation probe leaves open (`01-DESIGN.md` §5, `hbridge`'s notes; `05-REPAIRS-W3.md` §17 WD6 corrects §16 S3c's theorem name): `tabled` composes `constants_of_tabled` (`P.decl_adequate`/`htbl`/`hsafe` ⇒ `∃ vc, env.constants c = some vc`) with `constOrigin_of_constants` (`A.constsOrigin` ⇒ `ConstOrigin`), **not** a single `constOrigin_of_tabled` — that theorem does not exist and is blocked on filed ask 4 (`doc/upstream-asks.md` item 4); until ask 4 lands, `defns` carries the two exclusions (`∀ I k, ¬ CtorOf env c I k`, `∀ iid np nfs, ¬ IndInfo env c iid np nfs`) as an explicit premise of this unit's own step lemma, exactly as `SpecEnv.erasesEnv`'s `htab` does; there is no `elimsOnly` clause; **scheduled first inside the wave** so `SpecEnv.mono`, the forward clauses or the motive-6 shape fails on day one if it is going to (risks R2, R1's W4 residue) |
| **U4.3 motives-mechanical (1, 7, 8, 9, 11, 12, 18)** | `VisitExprRefines/Step/Mechanical.lean` (+ the re-landed run plumbing) | U4.1 | 1,300 | the seven steps elaborate |
| **U4.3b block λ-headedness — runs after U4.3** | `VisitExprRefines/Step/Mechanical.lean` (the `visitMutual` step only, co-owned with U4.3, which lands first and owns every other step in the file), `Output.lean` (`FixLambda.of_onProgram` only) | U4.1, U4.3, **W3R U3R.3 (proof)** | 200 | `LowerBlock` now carries `hfl` (`01-DESIGN.md` §4.4), so the bridge must supply it per block. It has the fact — `ErasureBridge` carries `LBWfPeregrine Γ t`, whose `fixLambda` is `OnProgram Γ t FixLambda` — and what is owed is the subterm-closure step to the block's own `.fix defs j` node: `FixLambda.of_onProgram`. One lemma, named here rather than discovered at the step (`05-REPAIRS-W3.md` §16 F5) |
| **U4.4 motives-passes (2, 3, 10, 13, 14, 15, 16, 17)** | `VisitExprRefines/Step/Passes.lean`, `Supported.lean` (N18's projection half, if that is the route chosen), `doc/coverage.md` (the `.proj`-head measurement row) | U4.1, U2.2, **W3R U3R.1 (proof)** | 1,700 | the eight steps elaborate, each via a derived introduction lemma of `ErasesLB` (the acceptance test greps that each of the eight uses `ErasesLB.` and none re-proves a `Lower` fact inline); motive 10 supplies `Erases.proj`'s `hinf` from a stated source — a `Supported` clause or a coherence clause, decided and **measured** here, with the count of non-informative `.proj` heads across the five `.ast`s in the unit report. The criterion is the **semantic** one (U3R.1): measured over the 11 committed environments, all 15 distinct `.proj` heads pass it, where the syntactic one rejected 7 of them (`scratchpad/refute3/projheads.lean`) |
| **U4.5 cold-start + panics** | `ColdStartRun.lean`, `ColdStartInduction.lean` (re-landed adapted; **plus the new `visitExpr_ctorSat`** — §4.9's saturation route), `doc/panics.md` | U4.1 | 800 | `erase_run_ok`, `run_prepare_erasure_ok`, `visitExpr_shape_all` re-landed; `visitExpr_ctorSat` elaborates; `doc/panics.md` lists all sixteen sites with the premise excluding each — two closed by `Erases.sort_erasable`/`forallE_erasable`, the rest by named `Supported` conjuncts (criterion 10 = N12 option 2) |
| **G4 gate — the bridge lands** | `Capstone.lean`, `Green.lean`, `.github/workflows/build.yml` (N3a); N3a files | U4.1–U4.5 **(proof)** | 700 | both T8 statements elaborate proved; `#print axioms` on them shows `sorryAx` present exactly for the theorems `test/ledger.expected` predicts, and `doc/trust.md` names the lean4lean roots with `file:line` (provenance is documented there, not claimed measured — N6); **`green_G1`…`green_G6` stop taking `hbridge`**; ledger diff clean; **three CI steps W3R's gate left owed** (`.github/workflows/build.yml`, gate-owned since W1, N3a): `bash scripts/erases_correct.sh` beside the `Trust ledger` step (the only guard on T5's premise list), `bash scripts/erasesLB.sh` (exists, was not run), and `LeanToLambdaBox.Witness.SelfTest.matchTable` added beside `toyTable`/`staleTable` in the `Reified table drift` step (the only regression guard on the α-note path) — all three pass locally today and are owed to CI, not to a proof |

### W4b — the bridge repair wave (9 + gate)

`doc/rework/06-REPAIRS-W4.md` is this wave's design: it names each W4 finding, the decision it
takes, the exact signature that lands, and the probe that checks it; its §14 records the
refutation round the design went through and what each of the seven findings changed. Four member
steps had no supplier and one of them was refuted, so W4's two T8 statements are implications no
reader satisfies at a mutual block; seventeen named `Prop` premises carry the fourteen that were
supplied. The wave closes both — all eighteen steps, no named premise beyond the standing
binders — and discharges the erasure half of `hbridge`.

**Three repairs are definition changes, and the tree still builds at every unit.**
`ErasesLBMode`'s block conjunct is keyed by `BlockKeyed` (length, `Nodup`, and separation *at the
tabled names*) and `BridgeInv.fixvars` names such a pair; `BridgeInv` gains the inductive registry
and the motives carry it forward, since `Erasure.RunConcl` bounds growth alone and
`LeanToLambdaBox/ErasureRun.lean` is model-free; `SpecEnv` gains the free-variable-freedom clause
`Lower.abstract` needs, and `SupportedTm`'s `mdata` and `proj` rules are repaired against the
shipping dispatch. `ErasureSpec` is constructed nowhere and `Supported` only by
`supportedB_sound`, so the first two ripple into no consumer; `BlockKeyed`'s new `tbl` index is
threaded through the three step files by U4R.4 itself, under rule N1's co-ownership clause. So
`lake build` and `green-check --all` 6/6 are acceptance tests of every unit, not only of the gate.

**Two bundles, not one.** Four clauses the first draft put in `ErasureSpec` are about *this
repository's* code — `Erasure.isErasable`, the `prepare_erasure` passes, `Erasure.remove_unsafe_rec`
— and two of them are outright false as stated about the Lean API. They move to `EraserAsks`,
class **C**, five fields, one home, one row each in `doc/trust.md`; the oracle clause the bridge
consumes is **proved** from two weaker ones. Three findings are filed, not fixed: **F-DEPTH**
(`Expr.Data.approxDepth` is 8 bits, so the relevance oracle's kernel arm throws on any arity
deeper than 256 or behind an irreducible alias), **F-UNSAFEREC** (a legal `mutual unsafe def u /
u._unsafe_rec` block is silently miscompiled — one kername for two declarations), **F-KERNAME**
(`toKername` is not injective, so two constants can share one λ□ key and the second shadows the
first).

**`ConfigPinned` moves to `LeanToLambdaBox/ErasureSpec.lean`.** While it lives in
`LeanToLambdaBox/Capstone.lean`, `LeanToLambdaBox/Bridge.lean` must import the capstone and the
capstone can never import the bridge — which is why no `ErasureBridge` field could be discharged
in the file that declares it, and why 282 declarations sit outside `lake exe hygiene --dead`'s
closure.

| Unit | Files owned | Depends | Est. | Acceptance |
|---|---|---|---|---|
| **U4R.1 the two bundles** | `LeanToLambdaBox/ErasureSpec.lean`, `LeanToLambdaBox/ErasesTotal.lean` (one theorem, `erasable_indSpine`), `LeanToLambdaBox/Capstone.lean` (the `ConfigPinned` relocation only, co-owned with U4R.9), `doc/rework/03-DEV-FIX.md` | — | 550 | `ConfigPinned` has exactly one home and it is `ErasureSpec.lean`; `LookupAdequate`'s `declInfo`/`ctorArity`/`casesInfo` carry the guarded block membership, the two negative directions and `CasesInfoAgreesK`; `ErasureSpec` gains `prim_monotone` and `block_adequate` and **no clause of it specifies this repository's own code**; `EraserAsks`'s five fields elaborate, each docstring naming the repository function it is about, its class **C**, its owner and what retires it; `EraserAsks.oracle_informative` is a **theorem** and `erasable_indSpine` is proved; F-DEPTH, F-UNSAFEREC and F-KERNAME are filed with the command that measures each and its output; `#print axioms` on `ErasureSpec.envWF`/`.oracle_sound_of_run` unchanged; `lake build` green and `green-check --all` 6/6 |
| **U4R.2 abstraction** | `LeanToLambdaBox/{Abstract,FixMetatheory,Lower,SpecEnv,ColdStartShape}.lean` | U4R.1, U4R.3 (for `visitMutual_lowerBlock_hfl` only; the abstraction half has no dependency and starts on day one) | 550 | `Lower.abstract`, `Lower.noFVar` and `LowerAlt.abstract` elaborate with `FVarFreeBodies` as their only new premise, each within `[propext, Quot.sound]` (the probe's footprint, quoted); the two necessity refutations land beside `LowerFixFixture`; the occurrence metatheory lands with them; `SpecEnv.fvarFree`, `RegInvShape'.specFVarFree` and `Erases.noFVar` land and every existing construction site is discharged; the five relocated `gdecls` lemmas and `visitMutual_lowerBlock_hfl` land beside `RegInvShape'.recConst`; `--dup` 0; `green-check --all` 6/6 |
| **U4R.3 the fragment and the table's checks** | `LeanToLambdaBox/Supported.lean`, `LeanToLambdaBox/Erases.lean` (one theorem), `LeanToLambdaBox/Witness/SourceTable.lean` (one definition, `fixBlock?`), `Tools/Reify.lean` | U4R.1 | 550 | `SupportedTm.mdata` at the empty spine and `SupportedTm.proj` with the model arity and the index bound, both decided by `supportedGo` and transported by `supportedB_sound`; `Supported.head`, `Supported.projInfo`, `IndArity.indInfo` and `CasesInfoAgrees.of_pinned` are theorems; `KnownHead`'s three columns carry the model's three readings; `kernameSepB` is an arm of `supportedB` and `Supported.kernames` its reading; `fixBlock?` and `TableBlocks` land; `lake exe reify --blocks` and `--prepared` run green on the six rungs; `green-check --all` 6/6 and `reify --check` green — the ripple changes no committed verdict; the unit report **measures** metadata-wrapped heads, `.proj` heads, key collisions and installed blocks over the eleven committed environments |
| **U4R.4 the invariant** | `LeanToLambdaBox/Bridge.lean`, `LeanToLambdaBox/VisitExprRefines/Motives.lean`, `LeanToLambdaBox/VisitExprRefines.lean`, and the three `LeanToLambdaBox/VisitExprRefines/Step/*.lean` **for the `tbl` parameter and the `BlockKeyed` premise only** (co-owned with U4R.6/U4R.7/U4R.8, which land after and own every proof in them) | U4R.1 | 550 | `BlockKeyed` at the tabled names, the keyed `ErasesLBMode`/`ErasesLBAltMode`, `BridgeInv.indcanon`, `BridgeInv.fixvars_ids_subset` and the registry conjunct on `RunRefines`; `Bridge.lean` imports `SpecEnv` and `ColdStartRun` and **not** `Capstone`; `blockKeyed_append_absurd` shows the refuting pair is excluded; both T8 statements still elaborate with the eighteen steps as hypotheses; **`lake build` green** — the re-parameterisation is mechanical and lands in the same commit |
| **U4R.5 the registry run** | `LeanToLambdaBox/ErasureRun.lean` | U4R.1, U4R.4 | 350 | `run_register_inductive_models` — `RegisterModels` **proved**, guarded by the invariant so it is not refutable at a hand-made state; `run_mkDef_isLambda`, `isLambda_foldl_toBvar`, the four `pass_*_core` bridges and the two `run_mkDef_*` relocations land |
| **U4R.6 env steps** | `LeanToLambdaBox/VisitExprRefines/Step/Env.lean` | U4R.1, U4R.3, U4R.4, U4R.5 | 400 | steps 4, 5, 6 conclude `Step4`/`Step5`/`Step6` with no named premise; the install site's `BlockKeyed` is discharged from `Supported.kernames`, `TableBlocks.members` and `EraserAsks.block_keys_distinct`; `grep "^def .* : Prop$"` empty |
| **U4R.7 mechanical steps** | `LeanToLambdaBox/VisitExprRefines/Step/Mechanical.lean` | U4R.1–U4R.5 | 400 | steps 1, 7, 8, 9, 11, 12, 18 with no named premise; the seven relocated declarations gone; step 1 produces the type-former exclusion the spine steps thread |
| **U4R.8 pass steps** | `LeanToLambdaBox/VisitExprRefines/Step/Passes.lean`, `LeanToLambdaBox/ErasesLB.lean`, `test/ErasesLBCheck.lean`, `test/erasesLB.expected` | U4R.1–U4R.5 | 950 | steps 2, 3, 10, 13, 14, 15, 16 at the induction's own interfaces (`*Reg` gone) and **step 17**; the four `ErasesLB` intros relocated, the fixture's `#check` lines added and `bash scripts/erasesLB.sh` green against the regenerated fixture; with U4R.6/U4R.7, `motives_of_steps` composes with all eighteen supplied, and its `#print axioms` is the 33-name cluster of `06-REPAIRS-W4.md` §8 and nothing else |
| **U4R.9 the capstone** | `LeanToLambdaBox/Capstone.lean`, `LeanToLambdaBox/Green.lean`, `LeanToLambdaBox/ColdStartRun.lean`, `test/Ledger.lean`, `doc/trust.md` | U4R.1–U4R.8 | 500 | `prepare_sound` at the spine; `ErasureBridge` loses `erases` and `lower`, which `erasure_bridge_of_run` proves; the capstone's syntactic conjunct reads the prepared term and its observable conjunct still reads the subject; the six rungs pass a proved term for the erasure half and carry `hprep`; the ledger gains the `ErasureSpec.oracle_sound_of_run` row (its fixture diff handed to the gate, N3a) and `doc/trust.md` loses its step-premise row and gains one row per `EraserAsks` field and `TableBlocks` clause |
| **G4R gate — the bridge closes** | `.github/workflows/build.yml`, `doc/coverage.md`, `test/ledger.expected` (N3a); N3a files | U4R.1–U4R.9 **(proof)** | 250 | both T8 statements proved in full; the measured footprint is the predicted one; `--dup`/`--schedule`/`--tables`/`--cites` 0; `--dead` reports 172, down 282; `green-check --all` 6/6; `reify --check`, `--blocks` and `--prepared` green and wired into CI; the ledger diff is exactly the predicted one and `scripts/ledger.sh` is **unchanged**; `doc/trust.md` and `doc/coverage.md` carry the N22 input-side row and the kername-separation row, and **no class-E F-KERNAME row** |

5,050 lines. Serial path **U4R.1 → U4R.4 → U4R.5 → U4R.8 → U4R.9 → G4R** (3,150); U4R.3 runs
beside U4R.4 and gates U4R.2's last lemma; U4R.6 and U4R.7 run beside U4R.8, the long pole.

**What W4b does not close, and says so.** The environment half of `ErasureBridge` —
`erasesEnv`, `lowerEnv`, `wfSpec` and the environment clauses of `wf` — waits on the registration
invariant at the final state (`RegInvShape'`, `SpecEnv.exists`, `RegSaturated`), which is W5's.
`hbridge` therefore survives as a six-field binder, with each field's supplier named in its
docstring and in `doc/trust.md`. `SpecEnv.fvarFree` is carried the way `specClosed` is: W4b lands
`Erases.noFVar`, the theorem that pays it, and W5's supplier spends it when it first inhabits
`RegInvShape'` at a final state.

### W5 — the registration invariant, the capstone's final form, Arith, coverage, delivery (6 + gate)

**Where W4b actually left the bridge.** `erasure_bridge_of_run` is proved, but six named
obligations survive on it — `Step4`, `VisitExprRunConcl`, `DeclInfoAtHead`, `hall`, `hseg`,
`hctab` (`06-REPAIRS-W4.md` §15's delivery findings BD6-BD13; a follow-up to G4R is closing all
six outside this document, in the `.lean` files and in `doc/trust.md`/`doc/coverage.md`). W5 does
**not** own that closure. What W5 owns is what `06-REPAIRS-W4.md`'s own text already named as
out of scope for W4b: `ErasureBridge`'s six *fields* — `erasesEnv`, `lowerEnv`, `wfSpec`, `wf`,
`simulate`, `firstorder` — of which the last two are already proved (W3, `simulate_of_
erases_correct`/`firstorder_erases_deterministic`/`firstorder_no_box`) and the first four wait,
as `SpecEnv.lean`'s own comments say, on **the registration invariant at a run's final state**
(`RegInvShape'`, `SpecEnv.exists`, `RegSaturated`) — a fact no theorem in the tree currently
produces for an actual run, only for the hand-built `idEnv`/`natSpecEnv` toy fixtures
(`lowerEnv_of_cold_run`, `natEnv_elimCovered`). U5.1 is that theorem; U5.2 composes it with the
two already-proved fields into `hbridge`'s discharge and puts the capstone in its final,
`hbridge`-free form; U5.3 applies both to Arith.

**Two W3R consequences already fixed what G7/G8 were separately blocked on**, unrelated to
`hbridge`: a rung's subject must be nameable by a library module, and `VerifyBench/<P>.lean` runs
`#erase` on elaboration, so no library module can import it (U5.0 splits `VerifyBench/Src/<P>.lean`
out, as G1-G6's subjects already live in `Green.lean`); and `htbl` was uninhabited on any closure
that inlines a matcher, which `benchArith`'s does (W3R U3R.9 fixed this on the source side; U5.0
adds the matching λ□-side transports, `LeanToLambdaBox/Alpha.lean`, since `benchArith`'s emitted
`.lambda`/`.letIn` binder names are the frontend's own generator's choice). `doc/coverage.md`
already measures Arith **inside** the fragment (`hsup`/`hnb` clear, 0 erroring tabled bodies) and
names its own program row "the applied capstone's subject, G7/G8 (W5)".

**What stays a binder at every rung, unconditionally on this wave** — restated so no unit treats
it as an Arith-specific gap: `hcb` (class C, discharged only at G1; lean4lean's `TrProj` is
unproven), `hfo` (upstream ask 4, `firstOrderIndB_sound`'s model-side half), and `hev`/`hvwt`/
`hty` (the correctness statement is universally quantified over "any value the source evaluates
to"; non-vacuity, T10, is a separate per-rung witness, `Green.g5_seval` the precedent — not a
discharge of these three).

| Unit | Files owned | Depends | Est. | Acceptance |
|---|---|---|---|---|
| **U5.0 rung subjects and the α transports** | **new** `VerifyBench/Src/{Arith,Sieve,Quicksort,BinaryTrees,Fannkuch}.lean`, the five `VerifyBench/<P>.lean` roots, **new** `test/frozen/<P>.lean.expected`, **new** `scripts/frozen.sh`, **new** `LeanToLambdaBox/Alpha.lean` (`lakefile.toml`'s one-line glob addition is G5's, N3a) | — (needs only `Erases`/`Lower`/`TrExprS`/`SEval`, stable since W1-W3; independent of the six residual bridge obligations and of U5.1) | 550 | each `VerifyBench/Src/<P>.lean` is the frozen original's definitions with no `#erase` and no `import LeanToLambdaBox`; each `VerifyBench/<P>.lean` is `import VerifyBench.Src.<P>` plus its unchanged `#erase` line; `lake build` elaborates the `Src` modules and **writes no `.ast`**; `scripts/frozen.sh` diffs the `Src` copies against `test/frozen/` and is wired into CI; `Alpha.lean` proves `LBTerm.AlphaEq` (decidable), `TrExprS.alpha` (a triviality — `VExpr` has no binder names), `SEval.alpha` and `Erases.alpha`/`Lower.alpha` up to it, with `NoBox`/`constRefs`/`ReachableFrom`/`WcbvEval` invariance — **only** those four, each with its U5.1-U5.3 consumer named or stated to have none |
| **U5.1 the registration invariant at the final state** | `LeanToLambdaBox/ColdStartInduction.lean` | the six residual bridge obligations closed (reuses `VisitExprRunConcl`'s exit-rule vocabulary and, where available, its literal conclusion) | 900-1,100 | `visitExpr_regInv_all` (homed beside `visitExpr_shape_all`, the nearest existing model) proves `∃ Γspec, RegInvShape' env bo Γspec s' ∧ RegSaturated env Γspec s'` at the state an actual `Erasure.visitExpr`/`visitMutual` run reaches, reusing rather than duplicating the run-algebra kit already in `ColdStartShape.lean` (`.stateCongr`/`.indsGrow`/`.constCons`/`.recConst`/`.axiomCons`/`.blockCons`/`.register_inductive_run`) and `run_register_inductive_models`/`_gen` (`Bridge.lean:230,291`); **fallback, stated up front**: if the fully generic form overruns by more than half, land eight specialised instances (one per rung, in the style of `lowerEnv_of_cold_run`) instead — either form is a complete delivery for U5.2, and the no-regression floor is `hbridge` staying exactly the binder it is today |
| **U5.2 the capstone in its final form** | `Capstone.lean`, `Green.lean` (co-owned — the mechanical `hbridge`-removal edit at `green_G1`-`green_G6` only) | U5.1 | 450 | `erasureBridge_of_run` composes U5.1's theorem with the already-proved `simulate_of_erases_correct`/`firstorder_erases_deterministic`/`firstorder_no_box` into the six-field `ErasureBridge`; `shipping_erase_correct_firstorder` **loses the `hbridge` parameter entirely** (discharged inside the proof) — its final signature is quoted verbatim in the unit report, with every remaining binder classified class C/D and its discharge mechanism named; `grep -n "hbridge" LeanToLambdaBox/Capstone.lean LeanToLambdaBox/Green.lean` matches nothing; `green_G1`-`green_G6`'s conclusions do not move, only their binder list shrinks |
| **U5.3 Arith rungs** | **new** `VerifyBench/Spikes/{G7,G8}.lean`, `Green.lean` (co-owned, after U5.2), `Witness/TrWitness.lean` (co-owned — one corollary for `benchArith`'s function-typed subject, if `hasType_const_of_table`'s existing route does not already cover a Π-typed table entry), `Tools/GreenCheck.lean` (co-owned — two new `Rung` entries; `checkRung` generalised for G8's applied term) | U5.0, U5.2 | 1,000-1,400 | `green_G7` (`arithClosed = benchArith 0`) and `green_G8` (the applied capstone at `args = [.lit 0]`) elaborate, both ending in `peanoLB 8`, in U5.2's final binder shape (no `hbridge`; `hev`/`hvwt`/`hty`/`hfo` standing as at every other rung); `g7_compilerBodies` types every tabled body the ten projections and four fix blocks reach; `g7_noBodylessRefs`/`g8_noBodylessRefs` close `by decide +kernel`; `lake exe reify --check` on `g7Table` passes, α-notes included; **`hev`'s non-vacuity witness (T10) is a target, not a requirement** — restriction N20 (every ι spine's unselected minors need their own `SEval` derivation) costs real proof volume at Arith's five `.case`s, and Lean's totality makes it payable, not vacuous; if it overruns the unit's budget by more than half, the accepted fallback (R9/R16) is no constructed witness at Arith, `hev` staying a binder exactly as at G1-G4/G6, with T10 demonstrated on a smaller rung instead — recorded in `doc/coverage.md` by U5.4, not silently taken |
| **U5.4 coverage** | **new** `Tools/Coverage.lean`, `doc/coverage.md`, **deletes** the benchmark status document (230 lines; its one load-bearing fact, the F-SPARSE reproduction, is already in `doc/rework/03-DEV-FIX.md`) | U5.3 | 450 | `lake exe coverage` regenerates `doc/coverage.md` byte-identically; five program rows plus the eight rungs, covered count ≥ 3 (criterion 14); carries the `hrun`/`htbl`/`hsafe` rows verbatim from `doc/trust.md`, the N22 row and the fragment rows regenerated rather than transcribed, and the G7/G8 rows in their measured (not "W5") state; the exception list gains no row for anything this wave leaves as an open proof obligation (only a genuine W6-scheduled dependency qualifies, per criterion 6) |
| **U5.5 hygiene + delivery** | `README.md`, module headers **of files owned by W0–W5 units** (never `{Erasure,Basic,Printing}.lean`), **deletes** the three superseded candidate designs ( — 57 of `--cites --all`'s 94 tree-wide misses; deleted rather than cited-fixed, per "history goes in commit messages" and the zero reader benefit of fixing citations in judged-and-rejected prose) | U5.4 | 350 | `lake exe hygiene` exits 0 tree-wide including `--cites --all` (green in CI for the first time in this development); `--dead`'s budget lowered to whatever U5.0-U5.4 leave, exception list carrying only W6-consumer rows; comment fraction < 20% scoped to owned files; `--dup`/`--schedule`/`--tables`/`--anti-epicycle` all exit 0 |
| **G5 gate — delivery** | integration; N3a files (`.github/workflows/build.yml`, `LeanToLambdaBox.lean`, `lakefile.toml`, `lake-manifest.json`, `test/ledger.expected`) | U5.0–U5.5 **(proof)** | 130 | every W0–W5 acceptance test re-run in one CI job; `hbridge` is gone from every rung; the eight rungs green (`green-check --all` 8/8); the ledger fixture matches; `--cites --all` exits 0; the gate's report separates three different reasons "still open" persists past this wave — `UpstreamAsks` (lean4lean, retires with the pin bump), `EraserAsks` (this repository's own code, class C by design, never expected to become class D), and the one `ErasureSpec`/`firstOrderIndB_sound` gap pending upstream ask 4 — rather than conflating them into one residual list; CI builds the branch consumers pin (criterion 22) |

3,830-4,430 lines (550 + 900-1,100 + 450 + 1,000-1,400 + 450 + 350 + 130). Serial path
**U5.1 → U5.2 → U5.3 → U5.4 → U5.5 → G5**; U5.0 runs beside U5.1 (and, if needed, beside U5.2)
and joins the path at U5.3, which is the first unit to need both.

### W6 — the closing round: `hve` discharged, `hbridge` reduced to two fields (8 + gate)

`doc/rework/08-REPAIRS-W5.md` is this wave's design; every signature below is quoted there in
full, with the probe that elaborates it. What W6 closes: `hve`, by deleting the premise `def` and
proving its conclusion under `ConfigPinned`; three of `hbridge`'s five fields — `wf`, which
becomes a per-rung `decide +kernel` term once one mis-specified clause is restated, `noBox`, by
exporting the constructor-tree shape `firstorder_erases_core` already computes, and `simulate`, by
applying `erases_correct` at the one spine the capstone needs it at. What W6 does **not** close,
and says so in its own design document's §2.3: `erasesEnv` and `lowerEnv`, for three measured
reasons — the eighteen-motive family is stated at a fixed level scope while 16 of G7's 30 tabled
bodies are erased at their own, `ReifiedDecl.Prepared` pins a tabled body only up to
`Expr.AlphaEq` while `Lower` is not α-closed on its source, and `RunRefines` reads content at
*every* specification environment of the final state where the repair produces one. `hbridge`
survives as a two-field binder with that section as its discharge story.

**One finding of this wave is load-bearing for what the ladder means.** `LBWfPeregrine.asciiNames`
is **false** at five of the eight rungs — 1 offending binder name at G2/G3/G4 and 34 at G7/G8, all
of them hygienic binders or `.fix` definition names carrying `.` and `@` — so those five rungs'
`hbridge` is unsatisfiable and their statements are vacuous. The clause, not the eraser, is wrong:
it mirrors `Basic.cleanIdent`'s character class, which `toKername` applies to **kername
identifiers**, while `Printing.lean:25` emits a binder name as a quoted atom and peregrine's
`Deserialize_ident` accepts any `Str` atom. U6.3 restates it and U6.4 checks the restated clause,
green at all eight rungs.

**What stays a binder at every rung, unconditionally on this wave**, restated so no unit treats it
as a W6 gap: `hcb` (upstream — 10 of G7's 30 tabled bodies carry an `Expr.proj` and lean4lean's
`TrProj` is unproven at the pin), `hfo` (upstream ask 4), `hev`/`hvwt`/`hty` (the statement is
quantified over any value the source evaluates to; T10 is a separate per-rung witness), and
`hbridge`'s two remaining fields.

| Unit | Files owned | Depends | Est. | Acceptance |
|---|---|---|---|---|
| **U6.1 `hve` discharged** | `LeanToLambdaBox/VisitExprRefines/Step/Env.lean` | — | 120 | `def VisitExprRunConcl` is **deleted** and `runClosedW_indReg`/`visitExpr_runConcl` land in its place, both `[propext, Classical.choice, Quot.sound]`; `run_visitMutual_registers` and `step6` take `hcfg : ConfigPinned ctx.config` in place of `hve`+`hcs`+`hpru` and neither gains a premise; `grep -rn "VisitExprRunConcl" --include='*.lean' LeanToLambdaBox/` is empty; `grep -nE "^def [A-Za-z0-9_']+ " LeanToLambdaBox/VisitExprRefines/Step/*.lean` reports 0 (was 1); `lake build` green |
| **U6.2 box-freedom of the lowered value** | `LeanToLambdaBox/FirstOrderInd.lean` | — | 150 | `FOSpine` with its two rules, `FOSpine.{noBox, mkApps, spineHead, lower}`, `spineHead_mkApps` and `noBox_lower_of_foSpine` land; `firstorder_erases_core` concludes `FOSpine t ∧ ∀ t', Erases env Us [] v t' → t' = t`; `firstorder_no_box`'s **statement** is byte-identical (`git diff` over its signature empty) and its `test/Ledger.lean` footprint unchanged; the unit report quotes `#print axioms` for each new declaration |
| **U6.3 the printable-binder clause** | `LeanToLambdaBox/Output.lean` | — | 60 | `AsciiBinderName`/`AsciiBinders` become `PrintableBinderName`/`PrintableBinders` at the condition the quoted atom needs (no `"`, no `\`), `LBWfPeregrine.asciiNames` becomes `printableNames`, and the docstring names `Printing.lean:25`, `Basic.lean:26-42` and `DeserializeCommon.v:13-18` as the three facts that fix the class; `hygienic_binder_not_alphanum` is a `by decide` refutation at the name the eraser actually emits; `lake build` green tree-wide (no consumer projects the clause) |
| **U6.4 the well-formedness checker** | **new** `LeanToLambdaBox/OutputCheck.lean` | U6.3 | 900 | `lbWfPeregrineB` and `lbWfPeregrine_of_check` land, with `subtermAll`/`subtermAll_sound` and `onProgramB`/`onProgramB_sound` as the two generic engines and one Boolean per clause; **every** definition in the file is structurally recursive (`grep -c "termination_by\|decreasing_by"` = 0), because a well-founded one does not reduce under `decide +kernel`; the file adds no `axiom`, no `sorry`, no `native_decide`; `lbWfPeregrineB Γ t = true` decided `by decide +kernel` at all eight `Green.g<i>Env`/`g<i>Term` pairs, the whole file under 30 s; the unit report gives the per-rung elaboration time |
| **U6.5 the simulation at the spine** | `LeanToLambdaBox/ErasesEnv.lean`, `LeanToLambdaBox/ErasesCorrect/Close.lean` | — | 120 | `ReachableFrom.mkApps_inv` and `ErasesEnv.mkApps` land, both `[propext, Classical.choice, Quot.sound]`; `simulate_of_erases_correct` is **deleted** (its two ∀-premises are false at any `Γspec`, U5.2 blocker 3) and its `test/Ledger.lean` row goes with it, handed to G6 under N3a; `erases_correct`/`erases_correct_lb` are untouched |
| **U6.6 the α kit's disposal** | `LeanToLambdaBox/Alpha.lean` (**deleted**, 1,050 lines, 99 declarations) | — | 10 | the file is gone and no `.lean` file outside `LeanToLambdaBox.lean` referenced it (`grep -rn "import LeanToLambdaBox.Alpha"` = 1 line, the aggregator's, handed to G6 under N3a); `02-PLAN.md` §4 gains its deletion row naming `08-REPAIRS-W5.md` §6 as the reason and §2.3's O2 as the round that re-lands it; no exception row is added |
| **U6.7 the capstone and the ladder** | `LeanToLambdaBox/Capstone.lean`, `LeanToLambdaBox/Green.lean` | U6.1, U6.2, U6.4, U6.5 | 200 | `ErasureBridge` has exactly two fields, `erasesEnv` and `lowerEnv`, and drops the `t` index; `shipping_erase_correct_firstorder` loses `hve`, gains `hwf : LBWfPeregrine Γ t`, and its observable clause gains the per-argument `ErasesEnv` conjunct and the spine translation `TrExprS env [] [] (mkApps pe args) vs`; all eight rungs discharge `hwf` by `lbWfPeregrine_of_check (by decide +kernel)` and pass `hwt` for the spine translation at `args = []`; no rung's conclusion moves (`git diff LeanToLambdaBox/Green.lean` adds and removes no `∧` inside any `green_G*` statement); `lake exe green-check --all` 8/8 |
| **U6.8 the record** | `doc/trust.md`, `Tools/Coverage.lean`, `doc/coverage.md` | U6.7 | 250 | `doc/trust.md`'s `hve` row is gone, its `hbridge` row names two fields and cites `08-REPAIRS-W5.md` §2.3's three obstructions, and it gains a `hwf` row in the `hnb` class (checked term, `decide +kernel`); `doc/coverage.md` is regenerated byte-identically by `lake exe coverage` and carries the F6 measurement table and the fact that T5 is now inside the closure; `lake exe coverage --check` exit 0 |
| **G6 gate — the closing round** | integration; N3a files (`.github/workflows/build.yml`, `LeanToLambdaBox.lean`, `test/Ledger.lean`, `test/ledger.expected`, `test/hygiene.allow`), `doc/rework/07-STATUS.md` | U6.1–U6.8 **(proof)** | 150 | every W0–W5 acceptance test re-run in one CI job; `grep -n "hve" LeanToLambdaBox/Capstone.lean LeanToLambdaBox/Green.lean` **empty**; `grep -n "hbridge" LeanToLambdaBox/Capstone.lean LeanToLambdaBox/Green.lean` reports **exactly 20 lines**, the W5 count unchanged — 4 in `Capstone.lean` (two docstring sentences, the binder, its one application) and 16 in `Green.lean` (one binder and one argument per rung) — and `grep -A 6 "structure ErasureBridge" LeanToLambdaBox/Capstone.lean` shows `erasesEnv` and `lowerEnv` and no third field; `lake exe green-check --all` **8/8**; `bash scripts/ledger.sh` green against a re-measured `test/ledger.expected` whose only diff is the deleted `simulate_of_erases_correct` row (the 33-name cluster is unchanged at the capstone and at all eight rungs — `#print axioms` never measures a hypothesis, and `decide` adds no axiom); `lake exe hygiene --dead` **re-measured**, its CI budget set to the measured value, with the two movements accounted in the gate report — Alpha's 99 leaving, and `erases_correct` with the arms it reaches entering; `--dup`/`--schedule`/`--tables`/`--cites`/`--anti-epicycle` all exit 0; `07-STATUS.md` §1's binder table and §4's open list rewritten against the measurement, not against this plan |

1,960 lines added, 1,065 deleted. Serial path **U6.3 → U6.4 → U6.7 → U6.8 → G6** (1,560); U6.1,
U6.2, U6.5 and U6.6 run beside it and join at U6.7, the first unit to need any of them. U6.4 is the
long pole and the only unit above 300 lines; its risk is the soundness proof for the two saturation
clauses, whose Boolean twin has to implement `ConstructSpine`'s maximal-application-depth guard —
**fallback, stated up front**: if that proof overruns by more than half, land the ten other clauses
in `lbWfPeregrine_of_check` and take `etaCtorsEnv`/`etaCtorsTm` as two explicit hypotheses of it,
leaving `wf` a two-clause residual binder at the rungs instead of a checked term. The no-regression
floor for the whole wave is that `hbridge` stays exactly the binder it is at the W5 checkpoint and
`green-check --all` stays 8/8.

**W6's file graph, checked disjoint.** Eight units' FILES: U6.1
(`VisitExprRefines/Step/Env.lean`), U6.2 (`FirstOrderInd.lean`), U6.3 (`Output.lean`), U6.4
(`OutputCheck.lean`, new), U6.5 (`ErasesEnv.lean`, `ErasesCorrect/Close.lean`), U6.6
(`Alpha.lean`, deleted), U6.7 (`Capstone.lean`, `Green.lean`), U6.8 (`doc/trust.md`,
`Tools/Coverage.lean`, `doc/coverage.md`). No file is named twice and no co-ownership is declared;
the aggregator's import line, the ledger row and the CI budget are the gate's, under N3a.

**Off the critical path, not scheduled.** Four additive hardening items survive from the earlier
W6 plan and are not part of the closing round: the functional refinement `Lower Σ⁺ t₀ (lowerTerm E t₀)`
on the exactness fragment (`LowerFun.lean`, ≈900); `LBOptimize_correct` generalised over
`with_constructor_as_block` (`Optimize.lean`, ≈600); the `Prop`-case fragment, gated on F-PROP
landing on `dev/fix` and on lean4lean's open `Injectivity.lean` (`ElimBody.lean`,
`Semantics/Eval.lean`, ≈800); and `srEval_sound`, which would turn each rung's source-evaluation
hypothesis into `by rfl` (`Witness/SrEval.lean`, ≈900). Each is additive and restates no W0–W6
statement.

---

## 3. Dependency graph (waves)

```
W0 ──► W1 ──► W2 ──► W3 ──► W3R ──► W4 ──► W4b ──► W5 ──► W6
```

Inside W1: **U1.0 first**, then the only constraints are U1.1 → {U1.2, U1.3, U1.6 (interface:
`IndInfo`), U1.9}, U1.5 → {U1.7, U1.9}, U1.6 → U1.9, U0.3 → U1.8; everything else is
interface-only. Inside W2's second half the units form a **chain**, because a rule change to
`Erases` or `Lower` breaks every consumer inside `Green.lean`'s import closure: U2.9 → U2.5 →
{U2.6, U2.7} → U2.8 → U2.10 → G2 (only U2.6 and U2.7 are parallel). Two edges the first cut left
undeclared are in it: **U2.8 → U2.6**, because `ErasesDecl.elim`'s `hsh` is `CasesOnShape`, which
`SourceEval.lean` defines; and **U2.10 → U2.8**, because `mkCtorBody`'s last consumer is
`ErasesDecl.ctor`. Inside W3, **U3.4 is scheduled first** (two load-bearing asks, risks R14/R4) and
**U3.8 second** (risk R15: a failed N19 verdict is what would force an η arm back into `Lower`;
risk R20: a failed N21 verdict empties a rung); U3.1 precedes U3.2/U3.2b/U3.3 by *interface* only,
because its aggregator takes their step lemmas as explicit hypotheses and they import
`ErasesCorrect/Steps.lean` rather than the aggregator, and **G3** owns `ErasesCorrect/Close.lean`,
where they are instantiated and T5 first stands alone; U3.5 needs U3.4's **interface** (U3.4 no
longer proves anything pin-dependent — §2's row — so nothing in W3 needs its *proof*) and
**U3.2's** proof (`not_erasable_of_informative`, stated once and used twice).

**W3's file graph, checked disjoint.** Nine units' FILES: U3.4 (`doc/upstream-asks.md`,
`LeanToLambdaBox/{Upstream,Origin}.lean`, `doc/trust.md`), U3.8 (`Supported.lean`,
`LeanToLambdaBox/CasesNames.lean`, `SourceEval.lean`'s one import line — co-owned with W2's
done U2.6, `doc/coverage.md`), U3.1 (`ErasesCorrect/Steps.lean`, `ErasesCorrect.lean`), U3.2
(`ErasesCorrect/Iota.lean`), U3.2b (`ErasesCorrect/Proj.lean`), U3.3 (`ErasesCorrect/Delta.lean`),
U3.5 (`FirstOrderInd.lean`, `Capstone.lean`'s `fo`-swap — co-owned with G3), U3.6
(`ColdStartShape.lean`, `ErasesEnv.lean`, `SpecEnv.lean`), U3.7 (`Witness/TrWitness.lean`) — no
two units name the same file outside the two declared co-ownerships (`SourceEval.lean` with W2's
closed U2.6; `Capstone.lean` with G3, which runs after every W3 unit). `lake exe hygiene
--schedule` (reads this document and `01-DESIGN.md` §7 for deletion rows) reports **0
inversions** against this plan.

**W3R's file graph, checked disjoint.** Nine units' FILES: U3R.1 (`Erasability.lean`,
`Erases.lean`, `ErasesTotal.lean`, `ErasesUniform.lean`, `ErasesStrengthen.lean`,
`ErasesAbstract.lean`, `Supported.lean`, `ErasesCorrect/Iota.lean`, `doc/rules-Erases.md`),
U3R.2 (`SourceEval.lean`, `SubjectReduction.lean`, `ErasesCorrect/Steps.lean`), U3R.3
(`Lower.lean`, `LowerFix.lean`, `doc/rules-Lower.md`), U3R.4 (`ErasesEnv.lean`,
`ColdStartShape.lean`, `SpecEnv.lean`), U3R.5 (`Upstream.lean`, `Origin.lean`,
`doc/upstream-asks.md`, `doc/trust.md`), U3R.6 (`ErasesCorrect/{Iota,Proj}.lean`), U3R.7
(`ErasesCorrect/{Delta,Steps}.lean`, `ErasesCorrect.lean`), U3R.8 (`FirstOrderInd.lean`), U3R.9
(`Witness/SourceTable.lean`, `Tools/Reify.lean`). **Three declared co-ownerships**, each a single
declaration rather than a file: `ErasesCorrect/Iota.lean` (U3R.1 deletes `IndDeclOf`, which moves
to `Erases.lean`; U3R.6 owns the rest of the file — without this U3R.1's own `--dup` is
unachievable and `Iota.lean` does not elaborate); `ErasesCorrect/Steps.lean` (U3R.2 restates
`SEval.no_elimSpine_value`, U3R.7 owns the rest); `doc/trust.md` (U3R.5 rewrites the class-**C**
table, G3R checks it afterwards). **Order:** U3R.1, U3R.3 and U3R.9 are independent and run
first, in parallel; U3R.2 needs U3R.1's interface (`IndArity`, `InformativeInd`); U3R.4 needs
U3R.1's and U3R.3's proofs and U3R.2's interface; U3R.5 needs U3R.1's and U3R.2's; U3R.6, U3R.7
and U3R.8 need U3R.4/U3R.5; **G3R** is last and owns `ErasesCorrect/Close.lean`, where
`StepPremises` dies. Serial path: **U3R.1 → U3R.4 → U3R.6 → G3R** (four links). The wave changes
four relation signatures, so the tree does not build between the first unit and the gate; that is
declared in the wave's own section and is the reason the gate's acceptance, not a unit's, is
`lake build` tree-wide, and the reason **G1-G6's green obligation is the gate's**.

**Serial path** (the longest true dependency chain — everything on it needs an earlier link's
*proof*, not just its interface): **U3.4 → U3.1 → U3.2 → U3.2b → G3** (five links; U3.2 → U3.5 →
G3 is the same length and runs alongside U3.2b). `U3.4`'s own link is an *interface* dependency
for U3.1 (its structure/theorem *signatures*, not a proof it discharges anything pin-dependent),
so U3.4 need not fully land before U3.1 starts drafting against its stated interface — only before
U3.1's own acceptance (`#print axioms` recorded) can be measured.

**Parallel groups**, relative to that spine:
- **Group 0 — no W3-unit dependency, may start together at W3's outset**: U3.4, U3.8, U3.6, U3.7.
  `U3.4` and `U3.8` are run **first and second** in that order for **risk**, not file-dependency,
  reasons (R14/R4, R15/R20 — a refusal or a failed fragment verdict should surface before other
  units invest work on top of it); the schedule tool sees no inversion either way, since nothing
  in Group 0 imports another Group-0 unit's new file.
- **Group 1 — after U3.4's interface and U2.7/U2.8's proofs (already landed in W2)**: U3.1.
- **Group 2 — after U3.1's interface**: U3.2 (also needs U3.4's interface).
- **Group 3 — after U3.2's proof, run in parallel with each other**: U3.2b, U3.5 (U3.5 also needs
  U3.4's interface and W2).
- **U3.3** needs only U3.1's interface and U2.7/U2.8's proofs — it does **not** need U3.2, so it
  runs alongside Group 2/3, not serially after them.
- **G3** waits on all nine units' *proofs* (its own DEPENDS ON list) — the join point, not on the
  spine.

Inside W4, U4.1 precedes the three motive units, and **U4.2 is scheduled before U4.3/U4.4** even
though it is independent of them. **U4.3b** (the block λ-headedness `LowerBlock.hfl` asks of the
bridge, W3R's F5) needs U4.1 and W3R U3R.3's proof and is otherwise independent; it is small and
can run alongside U4.3, whose file it shares one step with.

**W4b's file graph, checked disjoint.** Nine units' FILES: U4R.1 (`ErasureSpec.lean`,
`ErasesTotal.lean`'s `erasable_indSpine`, `Capstone.lean`'s `ConfigPinned` relocation,
`doc/rework/03-DEV-FIX.md`), U4R.2 (`Abstract.lean`, `FixMetatheory.lean`, `Lower.lean`,
`SpecEnv.lean`, `ColdStartShape.lean`), U4R.3 (`Supported.lean`, `Erases.lean`,
`Witness/SourceTable.lean`'s `fixBlock?`, `Tools/Reify.lean`), U4R.4 (`Bridge.lean`,
`VisitExprRefines/Motives.lean`, `VisitExprRefines.lean`, and the three
`VisitExprRefines/Step/*.lean` for the `tbl` re-parameterisation plus `Passes.lean`'s
`IndRegistryModelled` block), U4R.5 (`ErasureRun.lean`), U4R.6
(`VisitExprRefines/Step/Env.lean`), U4R.7 (`VisitExprRefines/Step/Mechanical.lean`), U4R.8
(`VisitExprRefines/Step/Passes.lean`, `ErasesLB.lean`, `test/ErasesLBCheck.lean`,
`test/erasesLB.expected`), U4R.9 (`Capstone.lean`, `Green.lean`, `ColdStartRun.lean`,
`test/Ledger.lean`, `doc/trust.md`). `test/ledger.expected` is **not** in that list: it is
gate-owned in every wave (N3a), and U4R.9 hands its diff to G4R.

**Four declared co-ownerships**, each a single block rather than a file: `Capstone.lean` (U4R.1
removes `ConfigPinned`, U4R.9 owns the rest and runs last); `VisitExprRefines/Step/Passes.lean`
(U4R.4 removes `IndRegistryModelled` and the four `*Reg` declarations and re-parameterises the
statements, U4R.8 owns every proof and runs after); and `Step/Env.lean` and `Step/Mechanical.lean`
(U4R.4 re-parameterises, U4R.6 and U4R.7 own the proofs). `ErasesTotal.lean` is U4R.1's alone —
one added theorem, no other unit names the file. The three re-parameterisation
co-ownerships are what rule N1 prescribes for a definition change with consumers outside the
unit's files, and they are what keeps the tree building.

**Order:** U4R.1 and U4R.2's abstraction half are independent and run first, in parallel; U4R.3
and U4R.4 need U4R.1, and U4R.3 gates U4R.2's `visitMutual_lowerBlock_hfl`; U4R.5 needs U4R.4's
interface; U4R.6, U4R.7 and U4R.8 need U4R.5's proof, and U4R.8 is the long pole (its step-17 half
starts only after its own first half); U4R.9 waits on all eight and G4R on all nine. Serial path:
**U4R.1 → U4R.4 → U4R.5 → U4R.8 → U4R.9 → G4R** (six links).

**Unlike W3R, the tree builds at every unit of W4b**, and `lake build` plus
`lake exe green-check --all` 6/6 is each unit's own acceptance test, not only the gate's: nothing
constructs an `ErasureSpec` (it is a binder everywhere, and its three existing readers take `.1`
of the strengthened conjunctions), `Supported` is constructed only by `supportedB_sound` in
U4R.3's own file, and `BlockKeyed`'s `tbl` index is threaded through the three step files by
U4R.4 in the same commit.

---

## 4. Deletion schedule

Every file below is deleted by the named unit, in the named wave; `lake exe hygiene --schedule`
enforces N2's topological rule at every gate. Nothing is "kept for reference"; git remembers, and
re-landed content is recovered from git history by its owning unit (the unit column of
`01-DESIGN.md` §7.2).

**Filenames in the "files deleted" column are written bare**, as `` `X.lean` ``, never as
`` `X.lean` ``'s-something: `Hygiene.cellFiles` (`Tools/Hygiene.lean:144-166`) treats a backticked
token followed by `'s` as a citation of *part* of a file and drops it, so a possessive cell yields
no file and the row escapes the check this section says enforces it — a possessive cell is
invisible to it. The
rows below are restated accordingly; the tool defect itself is a `doc/rework/03-DEV-FIX.md` row, since
`Tools/Hygiene.lean` is not a design deliverable.

**A row that deletes declarations *inside* a standing file names the module without the
extension**, as `` `ErasesEnv` ``: `cellFiles` reads every backticked `.lean` token as a deleted
path, so a partial row spelled with one makes every importer of a file that still exists an
inversion. Measured at the W3 checkpoint, that is exactly what happened twice — the W1 cut row
named the subject-reduction module, which U1.4 re-lands under the same name inside the same
wave, and the W2 row named the environment-relation module, of which only declarations go — and
`--schedule` reported 2 inversions against `ErasesCorrect/Steps.lean`, which imports both. Both
rows are written in the module form above, and the W1 row likewise names in prose the five
modules it cuts and a later unit re-lands under the same name, so the check is 0
(`--schedule`: 6 rows, 45 deleted files, 19 live imports of them, 0 inversions). The alternative the tool
offers, the `importers' import lines` co-ownership marker, is not used here: on the W1 row it
would mark thirty deleted files covered to silence one.

| Wave | Unit | Files deleted | Lines | Replaced by |
|---|---|---|---|---|
| W0 | U0.1 | `Export/EvalT.lean`, `Semantics.lean`, `Eval.lean` (shims; importers' import lines co-owned) | 324 | direct imports of `Semantics/*` |
| W1 | U1.0 | **the cut** — `ShippingCorrect.lean` (207), `ShippingCorrectData.lean` (127), `FirstOrderShipping.lean` (254), `FirstOrderShippingIota.lean` (553), `ErasureContext.lean` (251), `Erases.lean` (1,426), `ErasesLevels.lean`/`ErasesInstL.lean`/`ErasesDeltaL.lean` (1,146), `SourceEvalData.lean`/`SubjectReductionFull.lean`/`SubjectReductionIota.lean` (1,454), the subject-reduction module itself (cut and re-landed under the same name by U1.4 inside this wave, so not a schedule deletion), `DeltaHyps.lean`/`CasesBridgeHyps.lean`/`DataBridgeHyps.lean`/`ProjBridgeHyps.lean`/`PrepareHyps.lean` (2,223), `OracleDischarge.lean` (123), `EnvErasure.lean`/`EnvErasureNonrec.lean`/`EnvErasureRec.lean` (1,640), `ErasesCorrect.lean` (650), `ErasesCorrectData.lean`/`ErasesCorrectIota.lean`/`IotaPattern.lean`/`IotaDischarge.lean`/`ProjPattern.lean`/`ProjDischarge.lean`/`RecBlockErasure.lean`/`EraseCore.lean` (6,823), `FirstOrder.lean` (762), `ColdStart.lean`/`ColdStartDelta.lean` (3,185), the cold-start shape, induction and run modules (1,055 + 1,503 + 672) and the bridge's refinement and invariant modules (4,641 + 674) — each cut here and re-landed under the same name by U1.4/U3R.4/U4.1/U4.5, so none of the five is a schedule deletion | ≈29,500 (≈18,750 retired outright; ≈10,700 re-landed adapted in W1–W4 per `01-DESIGN.md` §7.2) | the new L0–L4/N modules of `01-DESIGN.md` §7.3 |
| W2 | U2.7 | `LowerCorrect.lean` — **the whole file**: the simulation half goes (`LowerPlain`, `lower_correct_plain`, `lowerFix_correct_plain`, `lower_correct_deltaChain`, `lowerFix_correct_atom`, `LowerNoEta`, `DeltaChain`, `BlockBodiesPlain`, `BlockDefsLambda`, `LowerEnvPlain`, and its duplicate `ElimBody` head inversion at `:2229-2251`), `BlockBodiesLambda`, the inversion and spine kit and the `NoBox` family move to `Lower.lean`, `LowerFixFixture.constToFix_needs_freshness` to `LowerFix.lean`. Also `Lower.{ctorApp, ctorEta, elimEta}`, `CtorDecl`, `ElimHeadOf`, `EtaSpine` in `Lower.lean`, and the two `#print axioms` rows in `test/Ledger.lean` whose subjects die here | 2,561 (≈1,780 retired, ≈780 relocated) | T5's one induction (`01-DESIGN.md` §2.3, §5; `04-AMENDMENT-W2.md` §7) |
| W2 | U2.8, U2.9 | in `Output.lean`: `ErasableAxioms`, `AxiomRealizer` and the axiom-realizer table; in the environment-relation module (`ErasesEnv`, partial — the file stands): `ErasesDecl.ctor`, `PrunedFor`, `EnvAgree` with its five lemmas, `IotaInert`; in `ErasesCorrect.lean`: `DeltaAgrees` and the four W2 refutation statements | ≈400 | the value arms of `SEval` (A18), `NoBodylessRefs` at T9 (A24), `ErasesDecl.defn` (A22); the rest had no consumer |
| W2 | U2.10 | `Fuel.lean` — the whole file (101 lines, zero references, no importer); `ElimBody.lean` — partial: the de-Bruijn/evaluation kit (`LBTerm.shift_zero`, `LBTerm.subst_spine`, `LBTerm.substList_mkApps`, `substTele` + nine lemmas, `elimAltsSub` + two, `substList_reverse_fields`, `eval_self`, `EvalArgs` + six), `wcbvEval_{app_inv, mkApps_inv, beta_step, mkApps_head_swap, app_arg_swap, mkApps_args_swap, case_inv, mkLambdas_fwd, mkLambdas_bwd}`, `mkCtorBody` + `mkCtorBody_closed` + `mkCtorBody_beta`, `mkElimBody_iota_fwd`/`_bwd`, and the `*_iota_fires` fixture block. **`mkElimBodyRec` is not deleted** — it is `ElimBody.recur`'s right-hand side | 101 + ≈740 | nothing evaluates at `Σ⁺` (`01-DESIGN.md` §2.3); `mkCtorBody`'s one consumer was `ErasesDecl.ctor` |
| W5 | U5.3 | the benchmark status document | 230 | `doc/coverage.md`, generated; F-SPARSE evidence carried into `doc/rework/03-DEV-FIX.md` first |
| W6 | U6.5 | in `ErasesCorrect/Close` (partial — the file stands): `simulate_of_erases_correct`, and its `#print axioms` row in the ledger fixture module (handed to G6, N3a) | 15 | `erases_correct` applied at the spine inside the capstone (`08-REPAIRS-W5.md` §5); the lemma's content was two ∀-premises that are false at any `Γspec` |
| W6 | U6.6 | `Alpha.lean` (the aggregator's import line co-owned, N3a) | 1,050 | nothing — it is the α-transport kit for `ReifiedDecl.Prepared`, whose only consumer is the content clause of `08-REPAIRS-W5.md` §2.1, which W6 does not schedule; the round that lands §2.1 re-lands it from git |

**Not scheduled here: `CheckerAdequacy.lean`'s partial deletion.** Its `namespace Lean4Lean`
block (the seven kernel-generic declarations, `01-DESIGN.md` §8.3 item 3) moves to the fork only
once an external pin bump lands there; editing the fork is a separate agent's work, not a W3
unit's (§2's U3.4 row), so no wave/unit/date is named for this row and none of U3.1–U3.8 or G3
deletes it. `01-DESIGN.md` §7.2/§7.4 and F16 record the deferral.

Outright-retired total: **≈19,900 lines**, plus ~3,000–3,500 comment lines removed in place
across the files W0–W5 own.

---

## 5. Per-wave green obligation (the standing acceptance test)

```
lake build \
  && lake exe hygiene && lake exe hygiene --dup && lake exe hygiene --schedule \
  && lake exe green-check \
  && diff <(lake env lean test/Ledger.lean) test/ledger.expected
```

`test/Ledger.lean`'s `#print axioms` rows follow their subjects: a unit that deletes a subject
deletes the row in the same commit (U2.7 does, for `lower_correct_deltaChain` and
`lowerFix_correct_atom`), and the gate re-measures `test/ledger.expected`. Without that the diff
above does not elaborate between the deleting unit and its gate.

`lake exe green-check` re-runs `#erase` on every rung reached so far and byte-diffs the committed
`.ast` — the external half of `hrun`, the one output-side check no Lean term can perform — and,
where the tool is on PATH, compares `lbEval Σ eraseFlags` with `peregrine eval`. `reify --check`
compares the rungs' tables field-by-field against the **live** environment (it does not
regenerate-and-diff, which would be blind to a reifier bug). These are the external mechanisms
behind the named class-**D** binders `hrun` and `htbl`; that is why those are binders rather than
hidden.

---

## 6. What stops the schedule

Exactly one unit is allowed to end the project: **U1.7**. Its wall has two faces and both must
fall: `Lower.constToFix` (the transport) **and** the stateability of the block-body motive
(`ErasesLBFix` exhibited on the two-member fixture). If either fails, then the `.fix`
correspondence has no home in any of the four architectures considered (a functional pass is
refuted, a congruence over `Lean.Expr` is refuted, and the relational arm with its three-factor
motive is what remains), and the honest conclusion is that the fragment excludes recursive
declarations — which covers 0 of 5 benchmarks. That verdict is to be recorded in
`doc/coverage.md` and raised, not worked around. Every other risk in `01-DESIGN.md` §10 has a
named fallback that keeps a smaller but true deliverable.
