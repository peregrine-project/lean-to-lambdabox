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
| **W2** | β, ζ, literals; the composite; then the re-anchoring the W2 refutations force | 4 + 6 + gate | G2, G3, G4 | in progress |
| **W3** | the one simulation (β ζ δ ι proj lit), first-order domain, `TrExprS` witnesses, the fragment, the pin bump | 9 + gate | G5, G6 |
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
| **U2.1 lower-correct — general case** | `LowerCorrect.lean` | W1 **(proof)**, U1.5 **(proof)** | 900 | `lower_correct` generalises `lower_correct_deltaChain` to all 17 arms of `Lower` (η, ι, proj, `case`, block flags), carrying `LowerNoEta`/`BlockBodiesLambda`/`DefsSurvive` as permanent class-**C** hypotheses — **not** discharged by waiting on the eraser-side fix **F-ETA** (policy N5: `dev/verify` never depends on `dev/fix` landing). `#print axioms lower_correct` = `[propext, Classical.choice, Quot.sound]`; a `_fires` non-vacuity guard per arm (`Optimize.lean:1066`'s style), including one exercising `ElimHeadOf`'s second disjunct, on pain of deleting it (§4.4); `lake exe green-check --differential` reconstructs the `Erases`-image from each rung and checks membership in `Lower Σ⁺` by a decidable checker. **Outcome: the 17-arm statement is refuted** (`01-DESIGN.md` §2.3, W2-R4/R5); delivered as `lower_correct_plain` over a named fragment, itself retired by U2.7/U3.1. The `--differential` flag does not exist in `Tools/GreenCheck`; `lake exe green-check --all` is what runs |
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
| **G2 gate — green_G2–G4, the merged `simulate` field, and T9's premise swap — done** | `Capstone.lean`, `Green.lean`, `VerifyBench/Spikes/{G2,G3,G4}.lean`, `test/{ErasesLBCheck.lean,erasesLB.expected,ledger.expected}`, `scripts/erasesLB.sh`; N3a files | U2.1–U2.10 **(proof)**, U1.8 **(proof)** | 650 | `ErasureBridge.simulate` and `.lowerCorrect` merge into the one field `01-DESIGN.md` §5 prints (T9's proof loses an `obtain`); T9's `hax : ErasableAxioms Σ t` is **replaced** by `hnb : NoBodylessRefs Σ t` and `Green.lean`'s `g1_erasableAxioms` by `g1_noBodylessRefs`, `by decide +kernel`; `erases_mkApps` deleted in favour of `ErasesLB.lean`'s `Erases.mkApps` and the spine premise folded per U2.2 (finding **G1-O3** retired); **`green_G1` still elaborates** — the standing obligation, re-measured after U2.5–U2.10. It is **not** the wave's test of the amendment and the gate does not report it as one: it takes `hbridge` as a binder (`Green.lean:185`) and constructs no `Erases`/`Lower`/`SEval`, so U2.5's two and U2.6's five `_fires` witnesses are what exercise the new rules. `green_G2`/`green_G3`/`green_G4` elaborate with literal peano answers; `hbridge` has **eight** fields (the merge of `simulate`/`lowerCorrect` from nine); `hcb` is discharged only at G1 and stays class-**C**, uninhabited at G2–G4 (their tabled bodies route through lean4lean's unproven `TrProj`); **`hev` is recorded as a class-**C** binder still uninhabited** (A14, second-round refuter F4) with its `test/ledger.expected` and `doc/trust.md` rows, discharged first at G3's `green_G5`; `lake exe green-check --all` green **on G1 only** (the rung registry, `Tools/GreenCheck.lean`, is G3's to extend — see G3's row); `lake exe hygiene --dup` exit 0; `lake exe hygiene --schedule` exit 1, one **pre-existing** inversion unrelated to this gate's edits (`CheckerAdequacy.lean`/`ErasureSpec.lean`, restated at U3.4's row below); `test/ledger.expected` re-measured; `doc/coverage.md` updated by hand (the generator is U5.3's) |

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
induction on `SEval`, at the emitted `Σ`, with **seven binders and six premises** — MetaRocq's five
plus `LowerEnv`. Its arms are step lemmas taking the induction hypothesis as a parameter, and the
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
| **U3.1 the simulation — aggregator and structural arms** | **new** `ErasesCorrect/Steps.lean`, `ErasesCorrect.lean` | W2 **(proof)**, U3.4 (interface) | 1,100 | `Steps.lean` receives `erases_mkApps_inv`, `erasable_mkApps`, `erases_correct_box`/`_boxSpine` and the spine helpers from `ErasesCorrect.lean` (so the arm files reach them without importing the aggregator) and lands `Simulates`, `StepIota`/`StepProj`/`StepDelta` and `SEval.no_elimSpine_value` exactly as `01-DESIGN.md` §5 prints them; `erases_correct` is **stated** there too — seven binders, six premises, **plus the eighth `(A : UpstreamAsks env)` U3.4 hands off** (dropped with no restatement once the pin moves), none named `Supported`/`Relevant`/`Iota*`/`*Consistent`/`*Hyps` — and `erases_correct_of_steps` is proved by `induction hev` with **every** non-hypothesis case discharged: `lam`/`sort`/`forallE`/`ctorVal`/`indVal`/`box`/`app`/β/ζ/`lit`, re-using U2.3's bodies. Three are new work: `ctorVal` (the value's image is `mkApps (.construct iid k []) cargs₀`, built by `WcbvEval.construct_atom`/`construct_app`, whose arity side condition is the rule's own `harity` — **no upstream lemma**); `indVal` (an inductive-name spine has no head erasure, so `erases_mkApps_inv` leaves only the boxed-prefix case and `mkApps_box` folds); and the β arm's **`Lower.elimApp` reading**, which at `extra ≠ []` re-associates into `app`-congruence and at `extra = []` is killed by `SEval.no_elimSpine_value` (`A.constsOrigin`) from `ErasesDecl.elim`'s `hsh`/`hco` (second-round fidelity F6; R19). **`specBlocks` obligation** (`01-DESIGN.md` §2.4 finding W2b-F1): `LowerEnv.specBlocks : BlockBodiesLambda Σ⁺` as printed is unsatisfiable on every real `Σ⁺` (U2.8 machine-checked it); if `Steps.lean`'s spine-inversion kit spends it before `Iota.lean` does, restate the consuming lemma's premise per the repair option named there rather than carrying the unsatisfiable clause forward silently. `erases_correct_lb` stated over `ErasesLB`; `test/t5.expected` committed and pinned from here on (criterion 6); `#print axioms` in the class-**B** set (plus `A`'s own class-**C** status); `_fires` witnesses for `ctorVal` and `indVal`; `lake build LeanToLambdaBox.ErasesCorrect` green; `grep -rn "sorry\|axiom " LeanToLambdaBox/ErasesCorrect.lean LeanToLambdaBox/ErasesCorrect/Steps.lean` empty |
| **U3.2 the ι arm** | **new** `ErasesCorrect/Iota.lean` (imports `ErasesCorrect/Steps.lean`) | U3.1 (interface), U3.4 (interface), U2.7, U2.8 **(proof)** | 1,600 | `step_iota` elaborates against `StepIota`, by the six steps of `04-AMENDMENT-W2.md` §6: `erases_mkApps_inv` split; boxed prefix via `erasable_mkApps` + `WcbvEval.mkApps_box`, consuming N20's premises and **adding no premise of its own**; head via `Lower.source_const` under `LowerEnv.specBlocks` — an induction on the `Lower` derivation, not a three-arm check, since `Lower.fixBody`'s source is constrained only by `hj` (`Lower.lean:228-239`); **`specBlocks` obligation** (`01-DESIGN.md` §2.4 finding W2b-F1): as printed it is unsatisfiable on every real `Σ⁺` (U2.8), so this step is the one most likely to need the repair — restrict `BlockBodiesLambda` to the pass's own emitted blocks, or state the obligation and report rather than carrying a vacuous premise — plus the ι rule's own `ho : ConstOrigin env con` through `constOrigin_not_ctorOf` (`A.constsOrigin`, U3.4's `UpstreamAsks`; **not** `hsh`, which fixes only the head's name) and `CasesOnShape.inj` for the split; **over-application handled, not excluded**: `extra` rides outside the node as `elimApp` carries it, and the branch rewrite runs under `wcbvEval_mkApps_head_congr` (`IotaBridge.lean:40-44`); discriminant via `not_erasable_of_informative` (takes `A.constArityInv`) and `specBlocks`, with saturation from `hdiscr`'s own `harity` rather than from the upstream lemma; node facts via `IndBodyOf`/`LowerEnv.inds`; branch via `LowerAlt` + `wcbvEval_mkApps_mkLambdas_substList` + `WcbvEval.lbClosed` + `WcbvEval.iota`; `grep -rn "IotaRelevant\|IotaShape" LeanToLambdaBox/` empty; `not_erasable_of_informative` is a theorem **taking `A` explicitly**, not a binder of its own beyond that, and is stated here for U3.5 too; `_fires` witnesses at the saturated and at the over-applied `casesOn` fixtures U2.6 built; `#print axioms` class-**B** plus `A`'s class-**C** status — no `sorryAx` inherited while the pin has not moved, since nothing here assumes it has. If it overruns 1,600 by more than half, stop and report rather than adding a premise |
| **U3.2b the proj arm** | **new** `ErasesCorrect/Proj.lean` (imports `ErasesCorrect/Steps.lean`) | U3.2 **(proof)** | 400 | `step_proj` elaborates, re-using `not_erasable_of_informative` and the `propositional = false` fact and nothing else; its `TrProj` obligation runs through the part of lean4lean's `Verify` layer that is entirely unproven, and the unit's report states exactly which `sorryAx` roots that adds (`doc/trust.md` row handed to the gate); a `_fires` witness on a structure fixture |
| **U3.3 the δ arm, including recursion** | **new** `ErasesCorrect/Delta.lean` (imports `ErasesCorrect/Steps.lean`) | U3.1 (interface), U2.7, U2.8 **(proof)** | 700 | `step_delta` elaborates for both target shapes — `Lower.const` (δ at `Σ` through `LowerEnv.defsTotal` and `wcbvEval_mkApps_head_congr`) and `Lower.fixConst` (`fix_atom` at the empty spine via `Lower.fixBody` + the now-unconditional `LowerBlock.lambda_of_fixLambda`; `fix_guarded` at a non-empty spine via `LowerFix.constToFix`/`Lower.fixUnfold`); neither route spends `LowerEnv.specBlocks` directly (`hfl`/`LowerBlock.lambda_of_fixLambda` supply what `Lower.fixUnfold` needs unconditionally), but **if `specBlocks`'s repair (§2.4 finding W2b-F1, U3.1's row) changes `BlockBodiesLambda`'s statement, re-check this file's `LowerBlock`-based reasoning against the new form before relying on it being unaffected**; the level-instantiation step consumes `ErasesEnv.defns` and is the only place the `instantiateLevelParams` axiom cluster appears (its `doc/trust.md` row handed to the gate); `_fires` witnesses at a recursive and a non-recursive constant |
| **U3.5 first-order** | `FirstOrderInd.lean`; co-owns `Capstone.lean` for the `fo`-parameter swap (finding **G1-O2**) | U3.4 (interface), **U3.2 (proof — `not_erasable_of_informative`)**, W2 | 650 | `example : firstOrderIndB arithTable 64 ``Nat = true := by rfl`, likewise `Bool` and `BinaryTrees`' `Tree` (criterion 8 as amended by A6/A15); `firstorder_erases_deterministic` on the eleven-rule `Erases`, where a first-order value's image is unique because a competing `const` derivation's `ConstOrigin` contradicts `CtorOf` through `Origin.lean`'s `constOrigin_not_ctorOf` — takes `(A : UpstreamAsks env)` like every other consumer of that corollary; `firstorder_no_box` proved of the **lowered** value (finding **G1-O7**), consuming the same `not_erasable_of_informative` as U3.2 — stated once, used twice, `A` threaded through unchanged; `Capstone.lean`'s `{fo : Name → Prop}` instantiated with no reproof of `shipping_erase_correct_firstorder` |
| **U3.6 lowerenv-from-records** | `ColdStartShape.lean` (re-lands `RegInvShape'` adapted), `ErasesEnv.lean`, `SpecEnv.lean` | U2.8 **(proof)** | 750 | `SpecEnv.exists` elaborates from `RegInvShape'` + `ErasureSpec.lookup_adequate` + `htbl`, and discharges `ErasesEnv.defns` from the run's own registry and `ErasesDecl.elim`'s `hsh` from the source table's inductive data; `LowerEnv Σ⁺ s'.gdecls` is **derived** — including `defsTotal` without its `fix` disjunct and the two new clauses `specClosed`/`specBlocks` — not assumed, and if `specBlocks` is derivable from the registry's own shape at all (block members are the recursive definitions, whose compiler bodies are λs) that derivation is where `01-DESIGN.md` §2.4 finding W2b-F1 is finally closed rather than merely worked around; if it is not derivable there either, report rather than assuming it, per that finding's own unit spec (`U3.6.md`); `patHead`/`PatOf` (`ErasesEnv.lean`, consumer-free since U2.5 deleted `IotaInert` — §2.4 finding W2b-F5) are **deleted** in this unit's pass over the file; `EnvAgree`, `WcbvEval.congr_env` and `PrunedFor` are **not** deliverables — they are deleted at U2.8 for want of a consumer |
| **U3.7 TrExprS-witnesses** | `Witness/TrWitness.lean` | U1.8 | 500 | `arith_trExprS : TrExprS env [] [] eArith ve` produced by routing lean4lean's checker (`M.WF.run'`, `VState.WF.initial`); **or** the named fallback lands (class-**D** binders, the two ledger/trust rows, A14 re-amended in the same commit — risk R11) |
| **G3 gate — green_G5–G6, the first ι rung, and the closing of T5** | `VerifyBench/Spikes/{G5,G6}.lean`, `Green.lean`, `Capstone.lean`, **new** `ErasesCorrect/Close.lean`, `Tools/GreenCheck.lean` (extend the rung registry to G2–G4 and G5–G6 — G2's outstanding item, `01-DESIGN.md` §6); N3a files | U3.1–U3.8 **(proof)** | 600 | `erases_correct` is closed: `Close.lean` instantiates the aggregator's step hypotheses with U3.2/U3.2b/U3.3's lemmas and the theorem stands with **no hypothesis beyond its seven binders and the eighth, `A : UpstreamAsks env`**, U3.4's — this is where criterion 6 is met (modulo `A`, which drops with no restatement once the pin moves) and `test/t5.expected` is re-pinned; **`green_G5` — a `match`, hence `.case`, ι and the amended `SEval.iota` — is attempted in the same gate that takes U3.2's arm, not deferred**; `green_G6` (`Nat.add`, hence `_unsafe_rec`, `deltaC`, `.fix`) elaborates with a literal answer; G1–G4 still green; `lake exe green-check --all` checks **all six** rungs now that `Tools/GreenCheck.lean`'s registry is extended; one file constructs a pats-carrying `VEnv.WF` with every ι-round premise, retiring review findings P1 and TA-06 by construction; U3.8's N19/N20 verdicts are reflected in `doc/coverage.md`; **criterion-21 grep is not run** — `CheckerAdequacy.lean`'s `Lean4Lean` namespace block stays until the fork accepts U3.4's asks (`01-DESIGN.md` §8.3 item 3, F16), and `doc/trust.md` records the deferral rather than a passing check that isn't one; `test/ledger.expected` matches; **`hev` stops being an uninhabited binder**: `green_G5` constructs the first `SEval` derivation, discharging `CasesOnShape`, `ho`, `hct` and N20's per-branch obligations, and the A14 ledger row G2 opened is closed or re-stated with the rungs that still carry it |

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
| **U5.3 coverage** | `Tools/Coverage.lean`, `doc/coverage.md`; **deletes** `VerifyBench/STATUS.md` (230 lines) **after** its F-SPARSE reproduction is verified present in `doc/rework/03-DEV-FIX.md` | U5.1 | 400 | `lake exe coverage` regenerates `doc/coverage.md` byte-identically; it has five program rows plus the eight rungs, names the excluding `SupportError` per uncovered program (incl. `Fannkuch`'s `hax`/`AxiomRealizer` row and any N18 row), and its covered count is ≥ 3 (criterion 14); it carries the `hrun`, `htbl` and `hwt` rows verbatim from `doc/trust.md` |
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

Inside W4, U4.1 precedes the
three motive units, and **U4.2 is scheduled before U4.3/U4.4** even though it is independent of
them.

---

## 4. Deletion schedule

Every file below is deleted by the named unit, in the named wave; `lake exe hygiene --schedule`
enforces N2's topological rule at every gate. Nothing is "kept for reference"; git remembers, and
re-landed content is recovered from git history by its owning unit (the unit column of
`01-DESIGN.md` §7.2).

**Filenames in the "files deleted" column are written bare**, as `` `X.lean` ``, never as
`` `X.lean` ``'s-something: `Hygiene.cellFiles` (`Tools/Hygiene.lean:144-166`) treats a backticked
token followed by `'s` as a citation of *part* of a file and drops it, so a possessive cell yields
no file and the row escapes the check this section says enforces it — measured, `--schedule` read
7 rows, 45 files and 0 inversions while all three partial-deletion rows contributed nothing. The
rows below are restated accordingly; the tool defect itself is a `doc/rework/03-DEV-FIX.md` row, since
`Tools/Hygiene.lean` is not a design deliverable.

| Wave | Unit | Files deleted | Lines | Replaced by |
|---|---|---|---|---|
| W0 | U0.1 | `Export/EvalT.lean`, `Semantics.lean`, `Eval.lean` (shims; importers' import lines co-owned) | 324 | direct imports of `Semantics/*` |
| W1 | U1.0 | **the cut** — `ShippingCorrect.lean` (207), `ShippingCorrectData.lean` (127), `FirstOrderShipping.lean` (254), `FirstOrderShippingIota.lean` (553), `ErasureContext.lean` (251), `Erases.lean` (1,426), `ErasesLevels.lean`/`ErasesInstL.lean`/`ErasesDeltaL.lean` (1,146), `SourceEvalData.lean`/`SubjectReductionFull.lean`/`SubjectReductionIota.lean` (1,454), `SubjectReduction.lean`, `DeltaHyps.lean`/`CasesBridgeHyps.lean`/`DataBridgeHyps.lean`/`ProjBridgeHyps.lean`/`PrepareHyps.lean` (2,223), `OracleDischarge.lean` (123), `EnvErasure.lean`/`EnvErasureNonrec.lean`/`EnvErasureRec.lean` (1,640), `ErasesCorrect.lean` (650), `ErasesCorrectData.lean`/`ErasesCorrectIota.lean`/`IotaPattern.lean`/`IotaDischarge.lean`/`ProjPattern.lean`/`ProjDischarge.lean`/`RecBlockErasure.lean`/`EraseCore.lean` (6,823), `FirstOrder.lean` (762), `ColdStart.lean`/`ColdStartDelta.lean` (3,185), `ColdStartShape.lean` (1,055), `ColdStartInduction.lean` (1,503), `ColdStartRun.lean` (672), `VisitExprRefines.lean` (4,641), `Bridge.lean` (674) | ≈29,500 (≈18,750 retired outright; ≈10,700 re-landed adapted in W1–W4 per `01-DESIGN.md` §7.2) | the new L0–L4/N modules of `01-DESIGN.md` §7.3 |
| W2 | U2.7 | `LowerCorrect.lean` — **the whole file**: the simulation half goes (`LowerPlain`, `lower_correct_plain`, `lowerFix_correct_plain`, `lower_correct_deltaChain`, `lowerFix_correct_atom`, `LowerNoEta`, `DeltaChain`, `BlockBodiesPlain`, `BlockDefsLambda`, `LowerEnvPlain`, and its duplicate `ElimBody` head inversion at `:2229-2251`), `BlockBodiesLambda`, the inversion and spine kit and the `NoBox` family move to `Lower.lean`, `LowerFixFixture.constToFix_needs_freshness` to `LowerFix.lean`. Also `Lower.{ctorApp, ctorEta, elimEta}`, `CtorDecl`, `ElimHeadOf`, `EtaSpine` in `Lower.lean`, and the two `#print axioms` rows in `test/Ledger.lean` whose subjects die here | 2,561 (≈1,780 retired, ≈780 relocated) | T5's one induction (`01-DESIGN.md` §2.3, §5; `04-AMENDMENT-W2.md` §7) |
| W2 | U2.8, U2.9 | in `Output.lean`: `ErasableAxioms`, `AxiomRealizer` and the axiom-realizer table; in `ErasesEnv.lean`: `ErasesDecl.ctor`, `PrunedFor`, `EnvAgree` with its five lemmas, `IotaInert`; in `ErasesCorrect.lean`: `DeltaAgrees` and the four W2 refutation statements | ≈400 | the value arms of `SEval` (A18), `NoBodylessRefs` at T9 (A24), `ErasesDecl.defn` (A22); the rest had no consumer |
| W2 | U2.10 | `Fuel.lean` — the whole file (101 lines, zero references, no importer); `ElimBody.lean` — partial: the de-Bruijn/evaluation kit (`LBTerm.shift_zero`, `LBTerm.subst_spine`, `LBTerm.substList_mkApps`, `substTele` + nine lemmas, `elimAltsSub` + two, `substList_reverse_fields`, `eval_self`, `EvalArgs` + six), `wcbvEval_{app_inv, mkApps_inv, beta_step, mkApps_head_swap, app_arg_swap, mkApps_args_swap, case_inv, mkLambdas_fwd, mkLambdas_bwd}`, `mkCtorBody` + `mkCtorBody_closed` + `mkCtorBody_beta`, `mkElimBody_iota_fwd`/`_bwd`, and the `*_iota_fires` fixture block. **`mkElimBodyRec` is not deleted** — it is `ElimBody.recur`'s right-hand side | 101 + ≈740 | nothing evaluates at `Σ⁺` (`01-DESIGN.md` §2.3); `mkCtorBody`'s one consumer was `ErasesDecl.ctor` |
| W5 | U5.3 | `VerifyBench/STATUS.md` | 230 | `doc/coverage.md`, generated; F-SPARSE evidence carried into `doc/rework/03-DEV-FIX.md` first |

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
