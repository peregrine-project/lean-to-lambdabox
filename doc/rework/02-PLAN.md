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
under `lake build` at the end of **every** wave, with every class-**C** hypothesis of the rungs
reached so far inhabited by a checked term (class-**D** binders — `P`, `htbl`, `hrun`, and `hwt`
until U3.4 — stay named binders, per A14) and every conclusion ending in a literal peano numeral.
A wave that leaves `Green.lean` red is not finished, whatever else it landed.

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
lean4lean, MetaRocq, peregrine) or to `doc/dev-fix-queue.md` (the tracked `dev/fix` queue,
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
| **W2** | β, ζ, literals, projections; the general `lower_correct`; the composite | 4 + gate | G2, G3, G4 | in progress |
| **W3** | ι, first-order domain, `TrExprS` witnesses, the pin bump | 5 + gate | G5, G6 |
| **W4** | The bridge: 18 motives against `ErasesLB`/`ErasesLBFix` | 5 + gate | G1–G6 lose `hbridge` |
| **W5** | Capstone at Arith, coverage, delivery | 4 + gate | **G7, G8** |
| **W6** | Optional hardening, off the critical path | 4 | unchanged |

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
| **U0.5 docs-and-hygiene** | `Tools/Hygiene.lean` (incl. `--dup`, `--schedule` (N2), `--anti-epicycle FILE` (comment-stripped token scan), `--dead`, `--tables`), `doc/rules-Erases.md`, `doc/rules-Lower.md`, `doc/panics.md`, `doc/coverage.md`, `doc/upstream-asks.md`, `doc/trust.md`, `doc/dev-fix-queue.md` | — | 420 | `lake exe hygiene` exits 0 on the files W0 touched; `--dup` exits 0; `--schedule` exits 0 against §4's table; the seven documents exist, `doc/dev-fix-queue.md` carries the six §8.2 rows (F-PROP, F-ETA, F-SPARSE, F-ACC, F-QUOT/F-EQREC, F-PRODUCT) each with `file:line`, the measuring command and its output, and `doc/upstream-asks.md` carries §8.3's six items; every `doc/…` citation in `01-DESIGN.md` resolves |
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
| **U1.8 erasurespec-supported-output** | `ErasureSpec.lean`, `Supported.lean` (incl. re-landed `IsLamTelescope`, `Supported.*_inv`), `Output.lean`, `CheckerAdequacy.lean` (eraser-specific lemma renamed to `LeanToLambdaBox.Oracle.kernel_isErasable_sound`; the seven kernel-generic declarations stay in their `Lean4Lean` namespace until U3.1's pin bump) | U0.3 | 1,300 | `grep -rn "structure .*Hyps" LeanToLambdaBox/` empty (criterion 4); `example : supportedB g1Table 64 eG1 = .ok () := by rfl`; `example : supportedB qsTable 64 eQuicksort = .error (.sparseCasesOn _) := by rfl` (criterion 11); `#print axioms ErasureSpec.envWF` = `[propext, Classical.choice, Quot.sound]`; the `ind_adequate` **derivation attempt** from `env_connect` (via `TrEnv'` inversion) is made and its outcome recorded — field kept only with the obstruction named in the docstring; per remaining class-**D** field, the docstring states why it is irreducibly about an opaque primitive |
| **U1.9 erases-env** | `ErasesEnv.lean` (`ErasesDecl`, `ErasesEnv`, `LowerEnv` incl. `defsTotal`, `EnvAgree`, `LBWfSpec`, `WcbvEval.congr_env`), `SpecEnv.lean` | U1.1, U1.5, U1.6 | 1,050 | an `example : ErasesEnv env bo Σ⁺ t` elaborates for a hand-built environment holding one inductive, one `ctor` entry, one `elim` entry (informative) and one fix definition; `SpecEnv.mono` elaborates from `StateLe` |
| **G1 gate — green_G1** | `LowerCorrect.lean` (δ / `ctorApp` / fix fragment), `Capstone.lean` (T9 stated in full, proved modulo one `hbridge` binder), `VerifyBench/Spikes/G1.lean`, `LeanToLambdaBox/Green.lean`; N3a files | U1.1–U1.9 **(proof)** | 1,200 | `lake build` elaborates `green_G1`, whose conclusion ends in the literal `.construct natIid 0 []`, with `hcfg`, `hsup`, `hax`, `hcb` inhabited by checked terms, `P`/`htbl`/`hwt` named class-**D** binders per A14, and `hbridge`/`hrun` outstanding; `lake exe green-check G1` byte-diffs the `.ast`; `lake exe hygiene --dup && lake exe hygiene --schedule`; ledger diff clean |

### W2 — β, ζ, literals, projections (4 + gate)

**What the gate handed over.** G1 already delivered `lower_correct_deltaChain` — `lower_correct`
at the δ/constructor/fix fragment, under three named guards (`LowerNoEta`, `BlockBodiesLambda`,
`DefsSurvive`) that are load-bearing, not interim: the unrestricted statement is machine-refuted
at the `ctorEta` arm (`lower_correct_needs_ctorEta_guard`, `01-DESIGN.md` §2.2 finding **G1-O6**),
and box-freedom does not transport along `Lower` without a `NoFix`-shaped guard either
(`noBox_lower_needs_noFix`, finding **G1-O7**). T9 is proved in full modulo one binder, `hbridge :
∃ Σ⁺ t₀, ErasureBridge …`, whose nine fields are the actual W2–W4 work list (`01-DESIGN.md` §5);
three of its own statement's deviations from `01-DESIGN.md`'s printed T9 (**G1-O1/O2/O3**) are
retired by the units below and by U3.3, not by this wave restating T9 itself.

`Capstone.lean` is **gate-owned for this wave** (an addition to N3a's list, tracked here since W1
already set the precedent of the wave gate assembling `hbridge`'s fields from sibling units'
proofs): each of U2.1–U2.3 below delivers a standalone theorem in its own file and hands its
one-line `ErasureBridge` field assignment to **G2**, which is the only unit that edits
`Capstone.lean` this wave. This is what rule N3 requires once three sibling units all feed one
shared consumer file.

| Unit | Files owned | Depends | Est. | Acceptance |
|---|---|---|---|---|
| **U2.1 lower-correct — general case** | `LowerCorrect.lean` | W1 **(proof)**, U1.5 **(proof)** | 900 | `lower_correct` generalises `lower_correct_deltaChain` to all 17 arms of `Lower` (η, ι, proj, `case`, block flags), carrying `LowerNoEta`/`BlockBodiesLambda`/`DefsSurvive` as permanent class-**C** hypotheses — **not** discharged by waiting on the eraser-side fix **F-ETA** (policy N5: `dev/verify` never depends on `dev/fix` landing). `#print axioms lower_correct` = `[propext, Classical.choice, Quot.sound]`; a `_fires` non-vacuity guard per arm (`Optimize.lean:1066`'s style), including one exercising `ElimHeadOf`'s second disjunct, on pain of deleting it (§4.4); `lake exe green-check --differential` reconstructs the `Erases`-image from each rung and checks membership in `Lower Σ⁺` by a decidable checker |
| **U2.2 composite** | `ErasesLB.lean` (new: the composite, the seven derived introduction lemmas, their `ErasesLBFix.*` twins) | U1.1, U1.5 **(proof)**, U1.7 **(proof)**, U1.9 | 600 | the introduction lemmas elaborate and their `#check` output diffs clean against `test/erasesLB.expected` — the fixture pinning them to the deleted rules' signatures; a lemma that T9's spine premise (`targs.length = args.length → ∀ i, … → ∃ a₀, Erases … a₀ ∧ Lower Σ⁺ a₀ targs[i]!`) implies `∀ i, i < args.length → ErasesLB env [] Σ⁺ [] args[i]! targs[i]!` (and conversely), so **G2** can fold `Capstone.lean`'s statement back with no reproof (finding **G1-O3** retired) |
| **U2.3 T5-interim** | `ErasesCorrect.lean` (new: T5 at the W2 fragment) | U1.1, U1.9, U1.4 (interface only — `SEval.defeq` already holds unconditionally at `fullFlags` with no `CompilerBodies`/`lenv` binder, finding **U1.4-b**, so U2.3 does not edit `SourceEval.lean`/`SubjectReduction.lean`) | 750 | `erases_correct` elaborates with **six** binders — the five of `01-DESIGN.md` §5 plus the named interim `hfl : fl ≤ w2Flags` (the induction does not yet cover the `case`/ι step), deleted at U3.2 once the ι arm lands (§3.4; the W3 statement is the pinned one); none is named `Supported`/`Relevant`/`Iota*`/`*Consistent`/`*Hyps`; `#print axioms erases_correct` = the class-**B** set |
| **U2.4 fuel** | `Fuel.lean` (the surviving `EraseCore` fuel lemmas, re-landed from git history) | U1.0 | 250 | the lemmas elaborate; `grep -rn "IotaRelevant\|IotaShape\|RecBlockAgreement" LeanToLambdaBox/` empty; `lake build` green |
| **G2 gate — green_G2–G4** | `Capstone.lean` (assigns `ErasureBridge.lowerCorrect` from U2.1, `.simulate` from U2.3, and folds the spine premise per U2.2's lemma — finding **G1-O3** retired), `VerifyBench/Spikes/{G2,G3,G4}.lean`, `Green.lean`; N3a files | U2.1–U2.4 **(proof)**, U1.8 **(proof, for `Supported`/`supportedB_sound`)** | 500 | `green_G2`, `green_G3`, `green_G4` elaborate with literal peano answers; `green_G1` still elaborates and, once U1.8 lands, `hsup` swaps from the `supportedB` verdict to `Supported env e` at the three sites `Capstone.lean`'s module docstring names (finding **G1-O1** retired); `lake exe green-check` covers four rungs; `lake exe hygiene --dup && lake exe hygiene --schedule` exit 0; `doc/coverage.md` updated by hand this wave (the generator is U5.3's; its interim absence is stated in the file header) |

Two absorptions Task-level review might expect as new W2 units are not: landing the `Supported`
Prop and `supportedB_sound` is **U1.8's own completion**, not new W2 scope — it is a W1 unit still
in progress, and G2 only consumes it (above); and `FirstOrderInd` plus T9's `fo`-parameter swap
(finding **G1-O2**) is **U3.3's** (W3), since `FirstOrderInd.lean` needs the first-order domain
work that wave does. `NoBox` transport along the general `Lower` (finding **G1-O7**) is likewise
**U3.3's**, not a separate W2 unit: `01-DESIGN.md` §7.3 assigns `firstorder_no_box` to
`FirstOrderInd.lean`, and `ErasureBridge.firstorder`'s field (§5) already states box-freedom of
the *lowered* value, not the erasure, so that is the theorem the guard has to be proved into.

### W3 — ι, first-order domain, witnesses, the pin bump (5 + gate)

| Unit | Files owned | Depends | Est. | Acceptance |
|---|---|---|---|---|
| **U3.1 upstream-and-repin** | the lean4lean **fork** (lands the seven kernel-generic `CheckerAdequacy` declarations, `WF'.defeqOwn`, and — best-effort — `consts_origin`); `CheckerAdequacy.lean` (deletes its `namespace Lean4Lean` block); gate applies the `lake-manifest.json` bump | W2 | 300 | `git show HEAD:lake-manifest.json` pins the new fork rev; `grep -rn "^namespace Lean4Lean" LeanToLambdaBox/` empty (criterion 21, gate-checked from G3 on); `lake build` green at the new pin; `test/ledger.expected` re-measured by the gate |
| **U3.2 T5-full** | `ErasesCorrect.lean`, `SubjectReduction.lean` | U1.6, W2 **(proof)** | 900 | T5 at `fullFlags` with the final five-binder statement (`hfl` deleted); the fixture `test/t5.expected` is committed **now** and pinned from here on (criterion 6); the ι arm is discharged via `mkElimBody_iota_bwd` with its guard fed by `hpre`'s image (§4.6-4.7); `#print axioms erases_correct` unchanged |
| **U3.3 first-order** | `FirstOrderInd.lean` (`firstorder_erases_deterministic`, `firstorder_no_box` — proved of the LOWERED value, closing finding **G1-O7**, not only of the erasure `tv₀`); co-owns `Capstone.lean` for the `fo`-parameter swap (finding **G1-O2**) | W2 | 650 | `example : firstOrderIndB arithTable 64 ``Nat = true := by rfl`, likewise `Bool` and `BinaryTrees`' `Tree` (criterion 8 as amended by A6/A15); `firstOrderIndB_sound` elaborates with the visited-set `fo` witness; `firstorder_no_box (henv) (hfo : FirstOrderInd env I) (hwt) (hty) (hval) (hlow : Lower Σ⁺ t₀ t) (h : Erases env Us [] v t₀) : NoBox t` — the `Lower`-transported form `ErasureBridge.firstorder` needs, discharged either by re-deriving box-freedom structurally over `Lower`'s congruence arms with a `NoFix`-shaped side guard, or by a decidable check on the lowered value at each rung (the choice and its cost are recorded in this unit's own commit, not assumed); `Capstone.lean`'s `{fo : Name → Prop}` binder and `ErasureBridge`'s `fo` parameter are instantiated to `FirstOrderInd env I` at the three sites `Capstone.lean`'s module docstring names, with no reproof of `shipping_erase_correct_firstorder` itself |
| **U3.4 TrExprS-witnesses** | `Witness/TrWitness.lean` | U1.8 | 500 | `arith_trExprS : TrExprS env [] [] eArith ve` is produced by routing lean4lean's checker (`M.WF.run'`, `VState.WF.initial`); **or**, if that fails, the unit lands the named fallback: `hwt`/`hty` stay class-**D** binders, the gate grows `test/ledger.expected` and `doc/trust.md` by the two rows, and A14's wording is re-amended in the same commit (risk R11) |
| **U3.5 lowerenv-from-records** | `ColdStartShape.lean` (re-lands `RegInvShape'` adapted), `ErasesEnv.lean`, `SpecEnv.lean` | U1.9, W2 **(proof)** | 700 | `SpecEnv.exists` elaborates from `RegInvShape'` + `ErasureSpec.lookup_adequate` + `htbl`; `LowerEnv Σ⁺ s'.gdecls` is **derived** — including `defsTotal` — not assumed; `EnvAgree`/`WcbvEval.congr_env` elaborate |
| **G3 gate — green_G5–G6** | `VerifyBench/Spikes/{G5,G6}.lean`, `Green.lean`; N3a files | U3.1–U3.5 **(proof)** | 450 | `green_G5` (a `match`, hence `.case` and ι) and `green_G6` (`Nat.add`, hence `_unsafe_rec`, `deltaC` and `.fix`) elaborate with literal answers; G1–G4 still green; one file constructs a pats-carrying `VEnv.WF` together with every ι-round premise, retiring review findings P1 and TA-06 by construction; criterion-21 grep green |

### W4 — the bridge (5 + gate)

**Structural prerequisite, and it is a deliverable in its own right.** The old
`VisitExprRefines.lean` (4,641 lines, deleted in the cut; measured shape: 93 top-level
declarations, the largest single theorem 1,744 lines) re-lands split: `Motives.lean` defines
`Motives f` (the eighteen conjuncts for an arbitrary eraser family `f` — seventeen against
`ErasesLB`, motive 6 against `ErasesLBFix`), each step becomes a standalone lemma
`step_… : Motives f → Motive… (F f)` in one of three files, and `VisitExprRefines.lean` shrinks
to the ~300 lines that state the two T8 conjunctions (§5) and apply the steps. Only then are
motives parallelisable. Proof scripts are recovered from git history and adapted (the
introduction-lemma renames of §4.7 for seventeen; genuinely new work for motive 6).

| Unit | Files owned | Depends | Est. | Acceptance |
|---|---|---|---|---|
| **U4.1 motive-split + BridgeInv** | `VisitExprRefines/Motives.lean`, `VisitExprRefines.lean` (aggregator), `Bridge.lean` (re-lands `BridgeInv`, 7 of the old 10 fields; the `fixvars` field's content is now `ErasesLBFix`'s `kns`/`ids` indices) | W3 **(proof)** | 900 | `Motives` is defined and both `visitExpr_refines_erasesLB` and `visitExpr_refines_erasesLBFix` are stated (§5), with the eighteen steps as **explicit hypotheses** of the aggregator (no `sorry`, no named holes — `#print axioms` on the aggregator = `[propext, Classical.choice, Quot.sound]`); `BridgeInv`'s binder list contains no `*Hyps` other than `ErasureSpec` |
| **U4.2 motives-env (4, 5, 6) — first** | `VisitExprRefines/Step/Env.lean` | U4.1 | 1,100 | the three environment-facing steps elaborate — motive 6 against `ErasesLBFix`; **scheduled first inside the wave** so `SpecEnv.mono` or the motive-6 shape fails on day one if it is going to (risks R2, R1's W4 residue) |
| **U4.3 motives-mechanical (1, 7, 8, 9, 11, 12, 18)** | `VisitExprRefines/Step/Mechanical.lean` (+ the re-landed run plumbing) | U4.1 | 1,300 | the seven steps elaborate |
| **U4.4 motives-passes (2, 3, 10, 13, 14, 15, 16, 17)** | `VisitExprRefines/Step/Passes.lean` | U4.1, U2.2 | 1,600 | the eight steps elaborate, each via a derived introduction lemma of `ErasesLB` (the acceptance test greps that each of the eight uses `ErasesLB.` and none re-proves a `Lower` fact inline) |
| **U4.5 cold-start + panics** | `ColdStartRun.lean`, `ColdStartInduction.lean` (re-landed adapted; **plus the new `visitExpr_ctorSat`** — §4.9's saturation route), `doc/panics.md` | U4.1 | 800 | `erase_run_ok`, `run_prepare_erasure_ok`, `visitExpr_shape_all` re-landed; `visitExpr_ctorSat` elaborates; `doc/panics.md` lists all sixteen sites with the premise excluding each — two closed by `Erases.sort_erasable`/`forallE_erasable`, the rest by named `Supported` conjuncts (criterion 10 = N12 option 2) |
| **G4 gate — the bridge lands** | `Capstone.lean`, `Green.lean`; N3a files | U4.1–U4.5 **(proof)** | 700 | both T8 statements elaborate proved; `#print axioms` on them shows `sorryAx` present exactly for the theorems `test/ledger.expected` predicts, and `doc/trust.md` names the lean4lean roots with `file:line` (provenance is documented there, not claimed measured — N6); **`green_G1`…`green_G6` stop taking `hbridge`**; ledger diff clean |

### W5 — capstone at Arith, coverage, delivery (4 + gate)

| Unit | Files owned | Depends | Est. | Acceptance |
|---|---|---|---|---|
| **U5.1 capstone** | `Capstone.lean` | W4 **(proof)** | 600 | `shipping_erase_correct_firstorder` elaborates in the applied form of `01-DESIGN` §5 (with `hax` a hypothesis and `∃ Σ⁺ t₀` binding the subject's own `Erases` conjunct); its conclusion contains `LBWfPeregrine` (criterion 12) and **not** `LBExpandedFix`, and its docstring names F-ETA; `#print axioms` matches the fixture |
| **U5.2 Arith rungs** | `VerifyBench/Spikes/{G7,G8}.lean`, `Green.lean` | U5.1 | 700 | `green_G7` (`arithClosed = benchArith 0`) and `green_G8` (the applied capstone at `args = [0]`) elaborate, both ending in `peanoLB 8`; `arith_hcb : CompilerBodies …` is discharged by four checker runs (`Nat.add/mul/sub/pow` typed via `M.WF.run'`), and the `deltaC` side conditions inside `hev` close by the four `rfl` equation instances (`01-DESIGN` §3.1 Q3) |
| **U5.3 coverage** | `Tools/Coverage.lean`, `doc/coverage.md`; **deletes** `VerifyBench/STATUS.md` (230 lines) **after** its F-SPARSE reproduction is verified present in `doc/dev-fix-queue.md` | U5.1 | 400 | `lake exe coverage` regenerates `doc/coverage.md` byte-identically; it has five program rows plus the eight rungs, names the excluding `SupportError` per uncovered program (incl. `Fannkuch`'s `hax`/`AxiomRealizer` row and any N18 row), and its covered count is ≥ 3 (criterion 14); it carries the `hrun`, `htbl` and `hwt` rows verbatim from `doc/trust.md` |
| **U5.4 hygiene + delivery** | `README.md`, module headers **of files owned by W0–W5 units** (never `{Erasure,Basic,Printing}.lean`) | U5.1 | 500 | `lake exe hygiene` exits 0 over the whole tree: zero slice tags / commit hashes / dates / memory references / "used to"-narration, every backticked identifier resolves, every cited document exists (criteria 18-19); comment fraction < 20% **scoped to the files the rework owns** (the carried set measures 22.3% and shipping code may not be edited — the threshold is per-owned-file, stated in the tool); `lake exe hygiene --dead` reports zero declarations outside `Green.lean` ∪ `Capstone.lean`'s import closure except `doc/coverage.md`'s exception list, which may carry **only W6-consumer rows** (`01-DESIGN` §9.6 — today: `Optimize.lean` → U6.2); `git rev-list --count main..HEAD` = 0 after the merge (criterion 22) |
| **G5 gate — delivery** | integration; N3a files | U5.1–U5.4 | 100 | every W0–W5 acceptance test re-run in one CI job; the eight rungs green; the ledger fixture matches; CI builds the branch consumers pin |

### W6 — optional hardening (4 units, no gate; each additive)

| Unit | Files owned | Est. | Acceptance |
|---|---|---|---|
| **U6.1 functional refinement** | `LowerFun.lean` | 900 | `Lower Σ⁺ t₀ (lowerTerm E t₀)` on the exactness fragment — `[S §7.4]`'s "same result" reading — added **without restating T8** |
| **U6.2 optimize corollary** | `Optimize.lean` | 600 | `LBOptimize_correct` generalised over `with_constructor_as_block` (the four non-block arms), giving the optional corollary chain from `eraseFlags`; `Optimize.lean` leaves the §9.6 exception list |
| **U6.3 prop-case fragment** | `ElimBody.lean`, `Semantics/Eval.lean` | 800 | gated on **F-PROP landing on `dev/fix`** and on lean4lean's open `Injectivity.lean`: re-introduces the singleton machinery with `largeElim_of_wf` (both disjuncts) + the decidable index-determined-field conjunct, and a green rung with a `Prop` discriminee (`And.casesOn` at a `Nat` motive) — the rung that today is an N18 coverage row |
| **U6.4 srEval** | `Witness/SrEval.lean` | 900 | `srEval_sound` per flag slice, turning the source-evaluation hypothesis of each rung into `by rfl`; built only if the soundness proof stays under budget |

Every W6 unit's acceptance also includes: all W0–W5 acceptance tests still pass unchanged, and no
statement from W0–W5 is restated.

---

## 3. Dependency graph (waves)

```
W0 ──► W1 ──► W2 ──► W3 ──► W4 ──► W5
             └──────────────────────► W6 (any time after W2; additive — except U6.3, gated on dev/fix F-PROP)
```

Inside W1: **U1.0 first**, then the only constraints are U1.1 → {U1.2, U1.3, U1.6 (interface:
`IndInfo`), U1.9}, U1.5 → {U1.7, U1.9}, U1.6 → U1.9, U0.3 → U1.8; everything else is
interface-only. Inside W4, U4.1 precedes the three motive units, and **U4.2 is scheduled before
U4.3/U4.4** even though it is independent of them.

---

## 4. Deletion schedule

Every file below is deleted by the named unit, in the named wave; `lake exe hygiene --schedule`
enforces N2's topological rule at every gate. Nothing is "kept for reference"; git remembers, and
re-landed content is recovered from git history by its owning unit (the unit column of
`01-DESIGN.md` §7.2).

| Wave | Unit | Files deleted | Lines | Replaced by |
|---|---|---|---|---|
| W0 | U0.1 | `Export/EvalT.lean`, `Semantics.lean`, `Eval.lean` (shims; importers' import lines co-owned) | 324 | direct imports of `Semantics/*` |
| W1 | U1.0 | **the cut** — `ShippingCorrect.lean` (207), `ShippingCorrectData.lean` (127), `FirstOrderShipping.lean` (254), `FirstOrderShippingIota.lean` (553), `ErasureContext.lean` (251), `Erases.lean` (1,426), `ErasesLevels.lean`/`ErasesInstL.lean`/`ErasesDeltaL.lean` (1,146), `SourceEvalData.lean`/`SubjectReductionFull.lean`/`SubjectReductionIota.lean` (1,454), `SubjectReduction.lean`, `DeltaHyps.lean`/`CasesBridgeHyps.lean`/`DataBridgeHyps.lean`/`ProjBridgeHyps.lean`/`PrepareHyps.lean` (2,223), `OracleDischarge.lean` (123), `EnvErasure.lean`/`EnvErasureNonrec.lean`/`EnvErasureRec.lean` (1,640), `ErasesCorrect.lean` (650), `ErasesCorrectData.lean`/`ErasesCorrectIota.lean`/`IotaPattern.lean`/`IotaDischarge.lean`/`ProjPattern.lean`/`ProjDischarge.lean`/`RecBlockErasure.lean`/`EraseCore.lean` (6,823), `FirstOrder.lean` (762), `ColdStart.lean`/`ColdStartDelta.lean` (3,185), `ColdStartShape.lean` (1,055), `ColdStartInduction.lean` (1,503), `ColdStartRun.lean` (672), `VisitExprRefines.lean` (4,641), `Bridge.lean` (674) | ≈29,500 (≈18,750 retired outright; ≈10,700 re-landed adapted in W1–W4 per `01-DESIGN.md` §7.2) | the new L0–L4/N modules of `01-DESIGN.md` §7.3 |
| W3 | U3.1 | `CheckerAdequacy.lean`'s `namespace Lean4Lean` block (declarations move to the fork at the pin bump) | — | the fork |
| W5 | U5.3 | `VerifyBench/STATUS.md` | 230 | `doc/coverage.md`, generated; F-SPARSE evidence carried into `doc/dev-fix-queue.md` first |

Outright-retired total: **≈19,300 lines**, plus ~3,000–3,500 comment lines removed in place
across the files W0–W5 own.

---

## 5. Per-wave green obligation (the standing acceptance test)

```
lake build \
  && lake exe hygiene && lake exe hygiene --dup && lake exe hygiene --schedule \
  && lake exe green-check \
  && diff <(lake env lean test/Ledger.lean) test/ledger.expected
```

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
