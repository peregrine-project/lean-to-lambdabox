# 02 — Implementation plan

Companion to `01-DESIGN.md`, which is normative for every signature named below. Seven waves.
Within a wave, the numbered units are **independent** and may be executed in parallel by separate
agents on **disjoint files**; each wave ends with a single **gate** unit that integrates them and
carries the wave's green light. Dependencies inside a wave are *interface-only* — the signatures
are fixed by `01-DESIGN.md` §4, so a unit may import a sibling's file and use its declarations,
but may never edit it. Dependencies marked **(proof)** need the sibling's proofs, not just its
statements, and are only ever on an earlier wave or on the wave's own gate.

**The standing obligation.** From W1's gate onwards, `LeanToLambdaBox/Green.lean` must elaborate
under `lake build` at the end of **every** wave, with every class-**C** hypothesis of the rungs
reached so far inhabited by a checked term and every conclusion ending in a literal peano numeral.
A wave that leaves `Green.lean` red is not finished, whatever else it landed.

---

## 0. Rules that hold in every wave

**N1 — One name, one home, one wave.** New code and old code never both define the same name.
The unit that introduces the final version of a declaration deletes the old declaration of that
name **in the same commit**. Primed twins kept "so the old one still compiles" are forbidden: if a
statement changes, the new statement keeps the old name and every consumer inside the unit's own
files is updated in the same commit; a consumer outside them makes that file a co-owned file of
the unit, listed in the unit's file list. Enforced by `lake exe hygiene --dup`, which fails if any
declaration name is defined in two modules.

**N2 — Deletion is scheduled, not opportunistic.** Every file scheduled for deletion (§4) is
removed in its scheduled wave by the unit that owns it, never later. A file scheduled for deletion
in wave *n* may not gain new content in wave *n−1*.

**N3 — Ownership is per wave.** A file may be owned by different units in different waves; within
one wave exactly one unit owns it.

**N4 — Every unit's acceptance test is machine-checkable** and is run by the wave gate:
a `lake build` target, a `#print axioms` diff against a committed fixture, a `by decide` / `by rfl`
example, a `lake exe` tool exit code, or a `grep` whose expected output is stated.

**N5 — Findings are raised, never patched.** No unit edits
`LeanToLambdaBox/{Erasure,Basic,Printing}.lean`. Defects found go to `doc/upstream-asks.md` (for
lean4lean, MetaRocq, peregrine) or to the `dev/fix` branch queue (`01-DESIGN.md` §8.2).

**N6 — The ledger is measured, never narrated.** Any unit that changes an axiom footprint updates
`test/ledger.expected` in the same commit, and the gate diffs it.

---

## 1. Wave summary

| Wave | Goal | Units | Green rung at the gate |
|---|---|---|---|
| **W0** | Foundation: flags, tooling, ledger, hygiene, provably-dead deletions | 5 + gate | — (tooling self-test) |
| **W1** | Specification and pass layers; **the recursion wall retired**; first end-to-end instance | 9 + gate | **G1** `spikeZero` |
| **W2** | β, ζ, literals, projections; the full `lower_correct`; the composite | 4 + gate | G2, G3, G4 |
| **W3** | ι, eliminators, first-order domain, `TrExprS` witnesses | 5 + gate | G5, G6 |
| **W4** | The bridge: 18 motives against the composite | 5 + gate | G1–G6 lose `hbridge` |
| **W5** | Capstone at Arith, coverage, delivery | 4 + gate | **G7, G8** |
| **W6** | Optional hardening, off the critical path | 4 | unchanged |

---

## 2. Waves in detail

### W0 — foundation (5 parallel units + gate)

**Goal.** Make the flag points exist, stand up the four CI tools the whole schedule depends on,
and delete what is provably dead — before anything is proved on top of the tree.

| Unit | Files owned | Depends | Est. | Acceptance |
|---|---|---|---|---|
| **U0.1 flags-and-dead-code** | `LeanToLambdaBox/Semantics/Flags.lean`, `LeanToLambdaBox.lean`; **deletes** `Export/EvalT.lean`, `Semantics.lean`, `Eval.lean`, `ShippingCorrect.lean`, `ShippingCorrectData.lean`, `FirstOrderShipping.lean`, `FirstOrderShippingIota.lean` | — | 150 | `lake build` green; `grep -rn "defaultFlags\|appliedFlags" LeanToLambdaBox/` empty; `grep -c "⟨true, true, false⟩" Semantics/Flags.lean` = 1; the seven files absent from `git ls-files` |
| **U0.2 ledger-and-CI** | `test/Ledger.lean`, `test/ledger.expected`, `lakefile.toml`, `lake-manifest.json`, `.github/workflows/build.yml` | — | 140 | `diff <(lake env lean test/Ledger.lean) test/ledger.expected` exits 0; `git show HEAD:lakefile.toml \| grep -c 20ec229` = 1; the workflow's `branches:` list contains `dev/verify` |
| **U0.3 reify-tool** | `Tools/Reify.lean`, `LeanToLambdaBox/Witness/SourceTable.lean`, `VerifyBench/tables/` (supplies its `lean_exe` stanza text to U0.2, which owns `lakefile.toml`) | — | 420 | `lake exe reify --check VerifyBench/Spikes/G1.lean` exits 0 and reproduces `VerifyBench/tables/G1.json` byte-identically |
| **U0.4 lbEval** | `LeanToLambdaBox/Semantics/Compute.lean`, `Tools/GreenCheck.lean` | — | 500 | `#print axioms lbEval_sound` = `[propext, Quot.sound]`; `example : lbEval nvΣ eraseFlags 1000 nvT = some (peanoLB 3) := by rfl`; `lake exe green-check --self-test` exits 0 |
| **U0.5 docs-and-hygiene** | `Tools/Hygiene.lean`, `doc/rules-Erases.md`, `doc/rules-Lower.md`, `doc/panics.md`, `doc/coverage.md`, `doc/upstream-asks.md` | — | 320 | `lake exe hygiene` exits 0 on the files W0 touched; `lake exe hygiene --dup` exits 0; the five documents exist and every `doc/…` citation in `01-DESIGN.md` resolves |
| **G0 gate** | integration only | U0.1–U0.5 | 40 | `lake build && lake exe hygiene && lake exe hygiene --dup && lake exe reify --check && diff <(lake env lean test/Ledger.lean) test/ledger.expected` |

### W1 — specification + pass layers, the recursion wall, and the first green light (9 + gate)

**Goal.** Everything L1 and L4 needs at the δ/constructor fragment, the fix correspondence proved,
and a real `#erase` run of `spikeZero : Nat := Nat.zero` whose every hypothesis is inhabited.

| Unit | Files owned | Depends | Est. | Acceptance |
|---|---|---|---|---|
| **U1.1 erases-relation** | `LeanToLambdaBox/Erases.lean`, `doc/rules-Erases.md`; **deletes** `ErasureContext.lean` | W0 | 900 | `grep -n "ErasureCtx" LeanToLambdaBox/Erases.lean` empty (criterion 1); a `#guard` fixing the constructor list at exactly the ten names of `01-DESIGN` §4.2; `doc/rules-Erases.md` covers every `[S Fig. 18]` rule (`lake exe hygiene --tables`) |
| **U1.2 erases-transport** | `ErasesAbstract.lean`, `ErasesStrengthen.lean`, `ErasesUniform.lean`; **deletes** `ErasesLevels.lean`, `ErasesInstL.lean`, `ErasesDeltaL.lean` (the ~200 surviving level lemmas move into `ErasesAbstract.lean`) | U1.1 | 700 | `erases_subst`, `erases_shift`, `Erases.abstract`, `Erases.uninstantiateN`, `Erases.thin_vlet` elaborate; `#print axioms erases_subst` ⊆ `[propext, Classical.choice, Quot.sound]` |
| **U1.3 erases-total** | `ErasesTotal.lean` | U1.1 | 300 | `Erases.exists_of_trExprS`, `Erases.sort_erasable`, `Erases.forallE_erasable`, `Erases.mono` elaborate (criterion 10, first half) |
| **U1.4 one-SEval** | `SourceEval.lean`, `SubjectReduction.lean`, `CompilerEnv.lean`; **deletes** `SourceEvalData.lean`, `SubjectReductionFull.lean`, `SubjectReductionIota.lean` | W0 | 750 | `grep -rc "^inductive SEval" LeanToLambdaBox/` = 1 (criterion 4); `SEval.mono`, `SEval.le` and `SEval.defeq` at `deltaOnly` elaborate |
| **U1.5 lower-relation** | `Lower.lean`, `doc/rules-Lower.md` | W0 | 850 | `Lower` elaborates with the 17 arms of `01-DESIGN` §4.4 and `#print axioms Lower` = `[propext]`; **the anti-epicycle grep** `grep -nE "Expr\|VEnv\|Erasable\|ErasureState" LeanToLambdaBox/Lower.lean` is empty; `Lower.shift_comm`, `Lower.subst_comm` elaborate |
| **U1.6 elim-body** | `ElimBody.lean` | W0 | 850 | `#print axioms mkElimBody_iota` and `mkElimBody_iota_sing` = `[propext, Quot.sound]` (class **A**); one checked `ElimBody` instance each for `Eq.rec`, `And.rec`, `Iff.rec`, `False.rec`, `Decidable.casesOn` (criterion 7, as amended) |
| **U1.7 lower-fix — THE WALL** | `LowerFix.lean` | U1.5 | 650 | `Lower.constToFix` elaborates, class **A**; **and** the two-member mutual-block fixture `lowerfix_nv` exhibits `LowerBlock Σ⁺ [kn₀,kn₁] bs bs' defs`, `Lower Σ⁺ bs[1]! (.fix defs 1)`, and `WcbvEval Σ eraseFlags (.const kn₁) (.fix defs 1)` in one term. **If this unit fails, the schedule stops** (risk R1) |
| **U1.8 primspec-supported-output** | `PrimSpec.lean`, `Supported.lean`, `Output.lean`, `CheckerAdequacy.lean`; **deletes** `DeltaHyps.lean`, `CasesBridgeHyps.lean`, `DataBridgeHyps.lean`, `ProjBridgeHyps.lean`, `PrepareHyps.lean`, `OracleDischarge.lean` | U0.3 | 1,300 | `grep -rn "structure .*Hyps" LeanToLambdaBox/` empty (criterion 4); `example : supportedB g1Table eG1 = .ok () := by rfl`; `example : supportedB qsTable eQuicksort = .error (.sparseCasesOn _) := by rfl` (criterion 11); `#print axioms PrimSpec.envWF`; `grep -rn "Lean4Lean\." LeanToLambdaBox/ \| grep -v "^.*--"` empty except the renamed `Oracle` lemma (criterion 21) |
| **U1.9 erases-env** | `ErasesEnv.lean`, `SpecEnv.lean`; **deletes** `EnvErasure.lean`, `EnvErasureNonrec.lean`, `EnvErasureRec.lean` | U1.1, U1.5, U1.6 | 1,050 | an `example : ErasesEnv envC Σ⁺ t` elaborates for a hand-built environment holding one inductive, one `ctor` entry, one `elim` entry and one fix definition; `SpecEnv.mono` elaborates from `StateLe` |
| **G1 gate — green_G1** | `LowerCorrect.lean` (δ / `ctorApp` / fix fragment), `Capstone.lean` (T9 stated in full, proved modulo one `hbridge` binder), `VerifyBench/Spikes/G1.lean`, `LeanToLambdaBox/Green.lean`, `VerifyBench/tables/G1.json` | U1.1–U1.9 **(proof)** | 1,200 | `lake build` elaborates `green_G1`, whose conclusion ends in the literal `.construct natIid 0 []`, with `hcfg`, `hsup`, `hax`, `hfo`, `hcomp` inhabited by checked terms and only `hbridge` and `hrun` outstanding; `lake exe green-check G1` byte-diffs both the `.ast` and the table; `lake exe hygiene --dup`; ledger diff clean |

### W2 — β, ζ, literals, projections (4 + gate)

| Unit | Files owned | Depends | Est. | Acceptance |
|---|---|---|---|---|
| **U2.1 lower-correct** | `LowerCorrect.lean` | W1 **(proof)** | 1,100 | `#print axioms lower_correct` = `[propext, Classical.choice, Quot.sound]` (criterion 15); a `_fires` non-vacuity guard per arm in the style of `Optimize.lean:1066`; `lake exe green-check --differential` reconstructs the `Erases`-image from each of the five runs and checks membership in `Lower Σ⁺` by a decidable checker |
| **U2.2 composite** | `ErasesLB.lean` | U2.1, U1.9 | 500 | the seven derived introduction lemmas elaborate, and their `#check` output diffs clean against `test/erasesLB.expected` — the fixture that pins them to the deleted rules' signatures |
| **U2.3 T5-widen** | `ErasesCorrect.lean`, `SubjectReduction.lean` | U1.1, U1.4, U1.9 | 800 | T5 elaborates at `βζδ + lit + proj`; its signature diffs clean against `test/t5.expected` (exactly five binders, none named `Supported`/`Relevant`/`Iota*`/`*Consistent`/`*Hyps` — criterion 6); `#print axioms erases_correct` = the class-**B** set |
| **U2.4 chain-deletion** | `Fuel.lean` (new, the surviving `EraseCore` fuel lemmas); **deletes** `ErasesCorrectData.lean`, `ErasesCorrectIota.lean`, `IotaPattern.lean`, `IotaDischarge.lean`, `ProjPattern.lean`, `ProjDischarge.lean`, `RecBlockErasure.lean`, `EraseCore.lean` | U2.3 | 250 | the eight files are absent; `grep -rn "IotaRelevant\|IotaShape\|RecBlockAgreement" LeanToLambdaBox/` empty; `lake build` green |
| **G2 gate — green_G2–G4** | `VerifyBench/Spikes/{G2,G3,G4}.lean`, `Green.lean`, `VerifyBench/tables/{G2,G3,G4}.json` | U2.1–U2.4 **(proof)** | 400 | `green_G2`, `green_G3`, `green_G4` elaborate with literal peano answers; `green_G1` still elaborates; `lake exe green-check` covers four rungs; `doc/coverage.md` regenerates with `lake exe coverage` |

### W3 — ι, eliminators, first-order domain, witnesses (5 + gate)

| Unit | Files owned | Depends | Est. | Acceptance |
|---|---|---|---|---|
| **U3.1 subsingleton-derivation** | `ElimBody.lean`, `doc/upstream-asks.md` | W2 | 450 | `subsingletonElim_of_wf` elaborates modulo the single named upstream ask, which is filed with the `file:line` of its existing twin (`InductiveParams.lean:93`); a pats-carrying `VEnv.WF` fixture (one `Prop`-valued singleton, one `Type`-valued) discharges `SubsingletonElim` on both |
| **U3.2 T5-full** | `ErasesCorrect.lean`, `SubjectReduction.lean` | U3.1, W2 **(proof)** | 900 | T5 at `fullFlags` with **the same statement** as W2's (the fixture `test/t5.expected` is unchanged — the widening axis is `fl`, not the theorem); `#print axioms erases_correct` unchanged |
| **U3.3 first-order** | `FirstOrderInd.lean`; **deletes** `FirstOrder.lean` | W2 | 550 | `example : firstOrderIndB arithTable 64 ``Nat = true := by rfl`, likewise `Bool` and `BinaryTrees`' `Tree` (criterion 8 as amended); `firstorder_no_box` and `firstorder_lower_deterministic` elaborate |
| **U3.4 TrExprS-witnesses** | `Witness/TrWitness.lean` | U1.8 | 500 | `arith_trExprS : TrExprS envC [] [] eArith ve` is produced by routing lean4lean's checker (`M.WF.run'`, `VState.WF.initial`); **or**, if that fails, the unit lands the amendment: `hwt`/`hty` become class-**D** binders in `PrimSpec`, `test/ledger.expected` grows the two rows, and criterion 13's wording is amended in the same commit (risk R11) |
| **U3.5 lowerenv-from-records** | `ErasesEnv.lean`, `SpecEnv.lean`, `ColdStartShape.lean` | U1.9, W2 **(proof)** | 700 | `SpecEnv.exists` elaborates from `RegInvShape` + `PrimSpec.lookup_adequate`; `LowerEnv Σ⁺ s'.gdecls` is derived, not assumed; `EnvAgree`/`WcbvEval.congr_env` elaborate |
| **G3 gate — green_G5–G6** | `VerifyBench/Spikes/{G5,G6}.lean`, `Green.lean`, tables | U3.1–U3.5 **(proof)** | 450 | `green_G5` (a `match`, hence `.case` and ι) and `green_G6` (`Nat.add`, hence `_unsafe_rec`, `envC` and `.fix`) elaborate with literal answers; G1–G4 still green; one file constructs a pats-carrying `VEnv.WF` together with every ι-round premise, retiring review findings P1 and TA-06 by construction |

### W4 — the bridge (5 + gate)

**Structural prerequisite, and it is a deliverable in its own right.** `VisitExprRefines.lean`
(4,641 lines) is today one theorem whose proof carries all eighteen steps, which is the monolith
that produced the current tree. U4.1 splits it: `VisitExprRefines/Motives.lean` defines
`Motives f` (the eighteen conjuncts for an arbitrary eraser family `f`), each step becomes a
standalone lemma `step_… : Motives f → Motive… (F f)` in one of three files, and
`VisitExprRefines.lean` shrinks to the ~300 lines that state the conjunction and apply the steps.
Only then are motives parallelisable.

| Unit | Files owned | Depends | Est. | Acceptance |
|---|---|---|---|---|
| **U4.1 motive-split + BridgeInv** | `VisitExprRefines/Motives.lean`, `VisitExprRefines.lean` (aggregator), `Bridge.lean` | W3 **(proof)** | 900 | `Motives` is defined and `visitExpr_refines_erasesLB` is stated against `ErasesLB` + `SpecEnv`, `sorry`-free at the top level with the eighteen steps as named holes; `BridgeInv` has 7 fields and its binder list contains no `*Hyps` other than `PrimSpec` |
| **U4.2 motives-env (4, 5, 6) — first** | `VisitExprRefines/Step/Env.lean` | U4.1 | 1,100 | the three environment-facing steps elaborate; **scheduled first inside the wave** so `SpecEnv.mono` fails on day one if it is going to (risk R2) |
| **U4.3 motives-mechanical (1, 7, 8, 9, 11, 12, 18)** | `VisitExprRefines/Step/Mechanical.lean` | U4.1 | 1,300 | the seven steps elaborate |
| **U4.4 motives-passes (2, 3, 10, 13, 14, 15, 16, 17)** | `VisitExprRefines/Step/Passes.lean` | U4.1, U2.2 | 1,600 | the eight steps elaborate, each via a derived introduction lemma of `ErasesLB` (this is where the reuse dividend is measured: the acceptance test greps that each of the eight uses `ErasesLB.` and none re-proves a `Lower` fact inline) |
| **U4.5 cold-start + panics** | `ColdStartRun.lean`, `ColdStartInduction.lean`, `doc/panics.md` | U4.1 | 700 | `erase_run_ok`, `run_prepare_erasure_ok`, `visitExpr_shape_all` carried; `doc/panics.md` lists all sixteen sites with the premise excluding each, two of them closed by `Erases.sort_erasable`/`forallE_erasable` (criterion 10) |
| **G4 gate — the bridge lands** | `Capstone.lean`, `Green.lean`; **deletes** `ColdStart.lean`, `ColdStartDelta.lean` | U4.1–U4.5 **(proof)** | 700 | `visitExpr_refines_erasesLB` elaborates; `#print axioms` on it shows `sorryAx` only through the lean4lean roots named in `test/ledger.expected`; **`green_G1`…`green_G6` no longer take `hbridge`**; ledger diff clean |

### W5 — capstone at Arith, coverage, delivery (4 + gate)

| Unit | Files owned | Depends | Est. | Acceptance |
|---|---|---|---|---|
| **U5.1 capstone** | `Capstone.lean` | W4 **(proof)** | 600 | `shipping_erase_correct_firstorder` elaborates in the applied form of `01-DESIGN` §5; its conclusion contains `LBWfPeregrine` (criterion 12) and **not** `LBExpandedFix`; `#print axioms` matches the fixture |
| **U5.2 Arith rungs** | `VerifyBench/Spikes/{G7,G8}.lean`, `VerifyBench/tables/{G7,G8}.json`, `Green.lean` | U5.1 | 700 | `green_G7` (`arithClosed = benchArith 0`) and `green_G8` (the applied capstone at `args = [0]`) elaborate, both ending in `peanoLB 8`; `arith_hcomp : CompilerEnv …` is four checked `TrExprS`+`HasType` facts (`Nat.add/mul/sub/pow`) |
| **U5.3 coverage** | `Tools/Coverage.lean`, `doc/coverage.md`; **deletes** `VerifyBench/STATUS.md` | U5.1 | 400 | `lake exe coverage` regenerates `doc/coverage.md` byte-identically; it has five program rows plus the eight rungs, names the excluding `SupportError` per uncovered program, and its covered count is ≥ 3 (criterion 14); it carries the `hrun` and `hwt` rows verbatim from the ledger |
| **U5.4 hygiene + delivery** | `LeanToLambdaBox.lean`, `README.md`, `.github/workflows/build.yml`, every module header | U5.1 | 500 | `lake exe hygiene` exits 0 over the whole tree: comment fraction < 20%, zero slice tags / commit hashes / dates / memory references / "used to"-narration, every backticked identifier resolves, every cited document exists (criteria 18-19); `lake exe hygiene --dead` reports zero declarations outside `Green.lean` ∪ `Capstone.lean`'s import closure and `doc/coverage.md`'s exception list is **empty** (criterion 20); `git rev-list --count main..HEAD` = 0 after the merge (criterion 22) |
| **G5 gate — delivery** | integration only | U5.1–U5.4 | 100 | every W0–W5 acceptance test re-run in one CI job; the eight rungs green; the ledger fixture matches; CI builds the branch consumers pin |

### W6 — optional hardening (4 units, no gate; each additive)

| Unit | Files owned | Est. | Acceptance |
|---|---|---|---|
| **U6.1 functional refinement** | `LowerFun.lean` | 900 | `Lower Σ⁺ t₀ (lowerTerm E t₀)` on the exactness fragment — `[S §7.4]`'s "same result" reading — added **without restating T8** |
| **U6.2 optimize corollary** | `Optimize.lean` | 600 | `LBOptimize_correct` generalised over `with_constructor_as_block` (four new arms), giving the optional deliverable at `optFlags` |
| **U6.3 Acc.rec** | `ElimBody.lean`, `Semantics/Eval.lean` | 800 | `iota_sing_idx` + the two-class field treatment lift N17; requires type-former injectivity at the redex, i.e. lean4lean's open `Injectivity.lean` |
| **U6.4 srEval** | `Witness/SrEval.lean` | 900 | `srEval_sound` per flag slice, turning the source-evaluation hypothesis of each rung into `by rfl`; built only if the soundness proof stays under budget |

Every W6 unit's acceptance also includes: all W0–W5 acceptance tests still pass unchanged, and no
statement from W0–W5 is restated.

---

## 3. Dependency graph (waves)

```
W0 ──► W1 ──► W2 ──► W3 ──► W4 ──► W5
             └──────────────────────► W6 (any time after W2; additive)
```

Inside W1 the only proof-order constraints are U1.1 → {U1.2, U1.3, U1.9}, U1.5 → {U1.7, U1.9},
U1.6 → U1.9, U0.3 → U1.8; everything else is interface-only. Inside W4, U4.1 precedes the three
motive units, and **U4.2 is scheduled before U4.3/U4.4** even though it is independent of them.

---

## 4. Deletion schedule

Every file below is deleted by the named unit, in the named wave, in the commit that lands its
replacement (rule N1). Nothing is "kept for reference"; git remembers.

| Wave | Unit | Files deleted | Lines | Replaced by |
|---|---|---|---|---|
| W0 | U0.1 | `Export/EvalT.lean`, `Semantics.lean`, `Eval.lean`, `ShippingCorrect.lean`, `ShippingCorrectData.lean`, `FirstOrderShipping.lean`, `FirstOrderShippingIota.lean` | 1,465 | one capstone (`Capstone.lean`, W1); the `Type`-valued twin served a transport never scoped (Q8) |
| W1 | U1.1 | `ErasureContext.lean` | 251 | `Erases`'s `(env, Us, Δ)` index (criterion 1) |
| W1 | U1.2 | `ErasesLevels.lean`, `ErasesInstL.lean`, `ErasesDeltaL.lean` | 1,146 | ~200 surviving level lemmas inside `ErasesAbstract.lean` |
| W1 | U1.4 | `SourceEvalData.lean`, `SubjectReductionFull.lean`, `SubjectReductionIota.lean` | 1,454 | one `SEval` + one `SEval.defeq` (criterion 4) |
| W1 | U1.8 | `DeltaHyps.lean`, `CasesBridgeHyps.lean`, `DataBridgeHyps.lean`, `ProjBridgeHyps.lean`, `PrepareHyps.lean`, `OracleDischarge.lean` | 2,346 | one `PrimSpec` (criterion 4) |
| W1 | U1.9 | `EnvErasure.lean`, `EnvErasureNonrec.lean`, `EnvErasureRec.lean` | 1,640 | `ErasesEnv.lean` + `SpecEnv.lean` |
| W2 | U2.4 | `ErasesCorrectData.lean`, `ErasesCorrectIota.lean`, `IotaPattern.lean`, `IotaDischarge.lean`, `ProjPattern.lean`, `ProjDischarge.lean`, `RecBlockErasure.lean`, `EraseCore.lean` | 6,823 | T5's ι/proj arms; `LowerFix`; `Fuel.lean` |
| W3 | U3.3 | `FirstOrder.lean` | 762 | `FirstOrderInd.lean` (`:103-155` carried verbatim) |
| W4 | G4 | `ColdStart.lean`, `ColdStartDelta.lean` | 3,185 | `Capstone.lean` |
| W5 | U5.3 | `VerifyBench/STATUS.md` | 520 | `doc/coverage.md`, generated |

Total deleted: **19,592 lines** (plus ~3,000–3,500 comment lines removed in place across W0–W5).

---

## 5. Per-wave green obligation (the standing acceptance test)

```
lake build \
  && lake exe hygiene && lake exe hygiene --dup \
  && lake exe reify --check \
  && lake exe green-check \
  && diff <(lake env lean test/Ledger.lean) test/ledger.expected
```

`lake exe green-check` re-runs `#erase` on every rung reached so far, byte-diffs the committed
`.ast` and `SourceTable`, and — where the tool is on PATH — compares `lbEval Σ eraseFlags` with
`peregrine eval`. It is the external half of the two hypotheses Lean can never discharge (`hrun`,
and `SourceTableAdequate`), and it is why those are stated as binders rather than hidden.

---

## 6. What stops the schedule

Exactly one unit is allowed to end the project: **U1.7**. If `Lower.constToFix` and the two-member
mutual-block fixture cannot be proved, then the `.fix` correspondence has no home in any of the
four architectures considered (a functional pass is refuted, a congruence over `Lean.Expr` is
refuted, and the relational arm is what remains), and the honest conclusion is that the fragment
excludes recursive declarations — which covers 0 of 5 benchmarks. That verdict is to be recorded
in `doc/coverage.md` and raised, not worked around. Every other risk in `01-DESIGN.md` §10 has a
named fallback that keeps a smaller but true deliverable.
