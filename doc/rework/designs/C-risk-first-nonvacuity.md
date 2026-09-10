# Design C — risk-first, non-vacuity-first

**Angle.** Order the whole rework so that **wave 1 ends with a green end-to-end instance** — a
checked term inhabiting *every* hypothesis of the capstone simultaneously, on a real `#erase` run
of a real `VerifyBench` program, with a *concrete numeral* coming out of the target evaluation —
and every later wave **widens the fragment while keeping that instance green**. Nothing lands
that does not either (a) keep the green instance green, or (b) move it one rung up the ladder.

**Why this angle.** The 2026-09-10 review's two most severe findings are non-vacuity findings:
`[P1]` "the crown theorems' premise sets have never been jointly inhabited", and `[TA-06]`
"`IotaRelevant` and `IotaShape` are uninhabited: nothing in the tree constructs either, at any Γ".
`VerifyBench/STATUS.md` records 0/5 coverage. A rework that re-derives the same stack in the same
order — definitions, metatheory, bridge, capstone, *then* benchmarks — reproduces exactly that
failure mode, because the first moment at which joint inhabitation is testable is the last moment
of the schedule. Design C inverts the order: joint inhabitation is tested in wave 1 and in every
wave after it, on a program whose `.ast` is committed and byte-diffed in CI.

**What is new here relative to the reference spec.** Six things, each forced by a probe:

1. **The ladder and the green instance** (§1.2, §6) — a sequence of eight closed `VerifyBench`
   spike programs G1…G8 ending at `benchArith`, each adding exactly one erasure feature, with a
   tracked `Green.lean` that must elaborate at every wave.
2. **`SEvalFlags` is the widening axis** (§3.6, §6) — T5 is proved at an increasing flag set;
   wave 1's T5 is at `⟨delta⟩` alone and is ~150 lines, and every later wave adds one flag and one
   arm. This is what makes a wave-1 green instance affordable.
3. **Pass inertness** (§3.4) — `LBLower` is the *full* three-pass composition from wave 1, but a
   pass that does not fire on a program is correct on it for free. Wave 1 therefore needs only
   `ctorInline.correct`.
4. **The witness generator** (§3.9) — a total, table-driven model eraser `eraseB` with
   `eraseB_sound : eraseB tbl e = .ok (Σ,t) → ∃ t₀, Erases … ∧ ErasesEnv … ∧ t = LBLower.term E t₀`.
   This is `[S §7.2]`'s `erases_erase` **for the model function**, which the papers all have and this
   tree never had; it is what supplies `Erases`/`ErasesEnv` witnesses at Arith scale without hand
   derivations, and it is *not* a bridge (`EraseCore.lean`'s addendum refuted that, correctly).
5. **Two certified evaluators** (§3.10) — `srEval` on `Lean.Expr` (sound for `SEval`) and `lbEval`
   on `LBTerm` (sound for `WcbvEval`). They turn "source evaluation is a hypothesis nobody
   discharges" (`N7`, review `GA-05`) into "source evaluation is discharged by `rfl` on every
   benchmark", and they make the target side's `2^3 = 8` a computation instead of a 400-step
   hand derivation.
6. **The applied capstone** (§4.5) — T9's observational conjunct is quantified over closed
   first-order argument spines, so it covers both `benchArith : Nat → Nat` (the thing `#erase` is
   actually run on) and the closed rung `arithClosed : Nat := benchArith 0` with one statement.

**Two measured facts that change the contract**, both established while preparing this design:

* **`LBWfPeregrine` may not claim `EEtaExpandedFix.expanded_eprogram`, because it is false on all
  five programs.** `untyped_transform_pipeline` (peregrine `theories/erasure/Transforms.v:147`)
  begins with `rebuild_wf_env_transform_mapping true true`, whose `pre` is
  `wf_eprogram efl p ∧ preserves_expansion true p` = `… ∧ EEtaExpandedFix.expanded_eprogram p`
  (MetaRocq `ErasurePlugin/ETransform.v:702-716`). `expanded_eprogram` needs
  `expanded_constant_decl`, i.e. `expanded Σ [] body` for every constant body, and
  `EEtaExpandedFix.expanded`'s only `tFix` rule (`Erasure/EEtaExpandedFix.v:47-53`) requires
  `args ≠ []` and `#|args| > d.(rarg)`. Every recursive Lean declaration erases to a **bare,
  unapplied** `tFix` at the head of its constant body — `Arith.ast`'s `Nat.add` is
  `(ConstantDecl (constant_body (Some (tFix ((def (nNamed "Nat.add") …) 0)))))` — so no rule
  applies. Coq does not hit this because its own pipeline η-expands fixpoints before erasure
  (`Template/EtaExpand`); the Lean eraser does not, and says so (`Erasure.lean:911`,
  `-- TODO: eta-expand fixpoints?`). Peregrine's discharge of that precondition is `Admitted`
  (`Transforms.v:375`). §8 raises this; §3.7 states the honest predicate and §6 W6 sketches the
  one-pass repair without editing shipping code.
* **`Erases` may be indexed by exactly one `VEnv`, and it must be the *compiler* environment.**
  Q3 measured that all 33 `_unsafe_rec` bodies are kernel-typeable and none is defeq to the kernel
  body, so N8 resolves as an environment extension `envC = env + one `VEnv.addDefEq` per compiler
  body`. Since `VEnv.addDefEq` (`Theory/VEnv.lean:37`) touches only `defeqs` and never `constants`,
  and `TrExprS.mono` (`Verify/Typing/Lemmas.lean:781`) lifts translations along `≤`, **all of
  `Erases`, `Erasable`, `TrExprS` and `SEval` can live at `envC` with no second index**. The
  kernel `env` appears only in `PrimSpec.env_connect` and `CompilerEnv`.

---

## 1. Overview

### 1.1 Four lanes

| Lane | Contents | Depends on lean4lean? | Trust class |
|---|---|---|---|
| **T (target)** | `LBTerm`, `WcbvEval`, flags, values, substitution, `Closed`, `IotaBridge`, `FixUnfold`, `LBPass` + the five passes, `lbEval` | no | **A** |
| **S (specification)** | `Erases`, `ErasesDecl`/`ErasesEnv`, `Erasable`, `SEval`, `SubsingletonElim`, `FirstOrderInd`, T5, T7 | yes | **B** |
| **B (bridge)** | `PrimSpec`, `Supported`, run algebra, the 18 motives, T8, the cold-start decomposition | yes | **B** + D |
| **N (non-vacuity)** | fixtures, `eraseB`, `srEval`, the ladder G1–G8, `Green.lean`, the coverage table, the ledger, the CI harness | yes | **A** |

Lane T is independently checkable and unblocked from day one. Lane N is the schedule's referee.
The reference spec has lanes T, S, B; adding N as a *first-class lane with its own deliverables*
is this design's structural contribution.

### 1.2 The ladder

Eight programs under `VerifyBench/`, each a real `#erase` run with a committed `.ast`. Rungs
G1–G7 are **closed nullary definitions** (`: Nat`), following `[L Thm 15]`'s "closed normal term"
posture and `backend_bench`'s closed-term convention, so the observable needs no argument spine
and no environment extension. G8 is the real `benchArith`.

| Rung | Program | Adds | Needs |
|---|---|---|---|
| G1 | `spikeZero : Nat := Nat.zero` | ctor constants, inductive decls, δ | `ctorInline`, `ErasesDecl.{defn,ctor,ind}`, `SEval` δ |
| G2 | `spikeLit : Nat := Nat.succ (nat_lit 3)` | `Erases.lit`, the peano tower | `SEval` lit |
| G3 | `spikeLet : Nat := let x := nat_lit 2; Nat.succ x` | ζ in **both** semantics | `SEval` ζ, `WcbvEval.zeta` |
| G4 | `spikeProj : Nat := (Prod.mk (nat_lit 1) (nat_lit 2)).1` | `Erases.proj`, boxed type parameters, polymorphic dependencies (N9) | `SEval` proj, `Erases.proj` |
| G5 | `spikeCase : Nat := match nat_lit 3 with \| 0 => nat_lit 7 \| n+1 => n` | matcher inlining, `casesOn`, `.case`, ι | `elimInline`, `ErasesDecl.elim`, `ElimBody`, `SEval` ι |
| G6 | `spikeFix : Nat := Nat.add (nat_lit 2) (nat_lit 3)` | `_unsafe_rec`, `envC`, `.fix` | `fixIntro`, `CompilerEnv`, β |
| G7 | `arithClosed : Nat := benchArith 0` | the typeclass tower: 10 projections, 4 fix blocks, 5 `.case`, 19-node peano tower | everything |
| G8 | `benchArith : Nat → Nat` (the tracked `VerifyBench/Arith.lean`) | function-typed subject | the applied capstone (§4.5) |

Measured at G7/G8: 39 declarations (27 constants, 12 inductives), 14,113 bytes, 155 `tApp`,
49 `tBox`, 5 `tCase`, 42 `tConstruct`, 4 `tFix` (all singleton), 10 `tProj`, 75 `tLambda`,
10 `tLetIn`; 4 `_unsafe_rec` bodies (`Nat.add/mul/sub/pow`); 0 axioms; 0 recursor, `casesOn` or
matcher declarations; 42/42 constructor occurrences saturated at `ind_npars + cstr_nargs`.

### 1.3 The green instance, precisely

`LeanToLambdaBox/Green.lean` (tracked, in `lake build`'s default target) holds, for the current
top rung `Gk`:

```lean
/-- Every class-C hypothesis of `shipping_erase_correct`, inhabited simultaneously at `Gk`. -/
def greenGk : GreenWitness := { hcfg := by decide, hsup := by decide, hax := by decide,
                                hfo := by decide, hcomp := gk_compilerEnv, hev := by rfl, … }

theorem green_Gk : <T9's full conclusion, instantiated at Gk, with a *literal* answer> := …
```

Three things make it a real green light rather than a ritual:

1. **The answer is a literal.** The conclusion ends in
   `WcbvEval (LBDeliver.decls E Σ) targetFlags (LBDeliver.term E t) (peano 8)` with `peano 8`
   written out, so the theorem cannot be satisfied by `□` or by a stuck term. This is T7
   (`firstorder_erases_deterministic` + `firstorder_no_box`) doing the work it exists for.
2. **The run is pinned outside Lean.** Waves 1–3 predate T8, so `green_Gk` takes one binder
   `hrun : Erasure.erase eGk cfg … = .ok (.untyped Σ (some t), inls)` and the *prediction check*
   `lake exe green-check` re-runs `#erase` and byte-diffs the emitted `.ast` against the committed
   fixture. From W4 (T8) the binder is discharged and the check becomes redundancy.
3. **CI fails if it stops elaborating.** `Green.lean` is a default target and its axiom set is
   diffed against a committed fixture (T11).

### 1.4 What is deleted, in one sentence each

Six `Erases` rules and everything keyed on them; `ErasureCtx`'s twelve columns; seven of the eight
`SEval*` relations; `ErasesEnvDelta` and the five `Registered*`/three `RegisteredClosure*`
predicates; four `*BridgeHyps` bundles plus `DeltaHyps`/`BlockHyps`/`RecBlockAgreement`/
`RegBridgeHyps`; `IotaRelevant`/`IotaShape`; the ι and proj discharge *chains*; `EraseCore` except
its fuel lemmas; `FirstOrderValue`/`InformativeType` as the observational domain; the three museum
sections, the seven consumer-free theorems, `Export/EvalT.lean`, `ShippingCorrect.lean`; the three
prose trust ledgers; ~3,200 comment lines of changelog. Full table in §5.

---

## 2. Decisions

### 2.1 The eight open questions

**Q1 — does `LBCompile` reproduce `visitExpr` exactly? — YES, against a compile table, on the
fragment.** Adopt the probe's verdict in full:

* Passes are parameterised by `CompileTable`, a pure function of the `Lean.Environment`, **not** by
  `GlobalDeclarations` — the shipping `Σ` contains no `casesOn`, ctor or recursor declarations
  (measured: 0 in all five `.ast`), so `LBCompile.term s'.gdecls t₀` is unsatisfiable as written.
* `LBCompile` is **split**: `LBLower := fixIntro ∘ elimInline ∘ ctorInline` is T8's factor;
  `LBDeliver := pruneEnv ∘ optimize` is what T9 composes afterwards. This removes the unstated
  idempotence obligation the spec's single `LBCompile` created.
* `Supported` gains three conjuncts: plain-`casesOn`-only (no `CasesAltInfo.default`, no
  `hasSideCondition`), every minor a syntactic λ-chain of the alt's arity, and `name_occurs`
  agrees with λ□ self-reference. These are what buy binder-name exactness.
* T8's subject is `prepare_erasure e`, not `e`.
* `mkAlt` and `mkDef` are MetaCoq-exact (`iota_red`, `fix_subst`); their two hedging docstrings are
  replaced by cross-references, not by hypotheses.

**Q2 — the subsingleton criterion. — DERIVED, narrow first cut, one upstream ask.**
`VInductDecl.LargeElim` (lean4lean `Theory/Inductive.lean:226`) exists and is reachable from
`VEnv.WF`; the derivation needs exactly one missing kernel-generic lemma
(`VEnv.WF'.consts_origin`, the constants-keyed twin of `WF'.pats_origin`), which goes **upstream**
by N15. Take the probe's recommended first cut:

```
SubsingletonElim env decl k  :=  LargeElim-with-the-FieldInIndices-disjunct-dropped
```

i.e. at most one constructor, every non-parameter field a proof. This covers `False.rec`,
`Eq.rec`, `And.rec`, `Iff.rec` and `Decidable`'s elimination, and puts `Acc.rec`/`WellFounded.fix`
on the restriction list as **N17** with one ledger row. The reference spec's §2 T3 claim that
Lean's criterion is "verbatim `[L §3.3]`" is **false** and must be amended: Lean's `LargeElim`
admits index-determined *data* fields (`FieldInIndices`), `Acc.intro`'s `x : α` is one, and
MetaRocq's `eval_iota_sing` — which boxes *every* branch binder — is therefore unsound for Lean's
`Acc.rec`. The full repair (`iota_sing_idx` + two-class field treatment) is scoped as W6-optional
and lands on lean4lean's `Injectivity`/`patsStrong` residual; the narrow cut costs nothing that
ships, because Lean's own code generator refuses `Acc.rec` too.

**Q3 — `_unsafe_rec`: hypothesis or restriction? — HYPOTHESIS, in the form of an environment
extension.** Restricting covers 0/5 (Arith's `Nat.add/mul/sub/pow` are all `_unsafe_rec`). Adopt
`envC = env + one `VEnv.addDefEq` per compiler body`, with `CompilerEnv` (§3.8) as the class-C
binder, decidable per program because F1 measured all 33 bodies kernel-typeable. `Erases`,
`SEval` and T5 are stated at `envC`; the kernel `env` survives only in `PrimSpec` and
`CompilerEnv`. `partial def` (Fannkuch's two) is uniform under this treatment — `TrEnv'.opaque`
gives a constant with no defeq, and `envC` gives it the compiler's. One class-E ledger row: the
two bodies agree only propositionally (equation lemmas), never transported; for `partial def` the
gap is total.

**Q4 — do emitted eliminator declarations blow up the deliverable? — NO, and on the shipping path
they are not emitted at all.** Measured cost of the runtime-library design is +4.5%…+13.6%
(median +9.3%) un-pruned and **0% pruned**; `.ast` size is dominated by the `.peano` tower (49% of
Quicksort) and hygienic binder names (7–17%), not by eliminators. Adopt T3's design, give
`pruneEnv` a dead-declaration clause with its own `WcbvEval`-preservation lemma, and record the
size split in N14's ledger row so the non-goal is measured rather than asserted. Consequence for
T8: its environment conclusion is
`s'.gdecls = pruneEnv.decls (LBLower.decls E Σ⁺) ++ s.gdecls` — the run's environment is the
*pruned image* of the specification's, not the specification's itself.

**Q5 — parameters in constructor applications. — PEREGRINE DROPS THEM; THE FRONTEND KEEPS THEM.**
`remove_params_optimization` is pass 2 of `verified_lambdabox_pipeline`, run verbatim by
`untyped_transform_pipeline`, at `wcon : with_constructor_as_block = false`. `dearg_ctors/consts`
belong to the *typed* `ExAst` pipeline and never run on Lean output. Measured: 982/982 constructor
occurrences saturated at `ind_npars + cstr_nargs` with empty block payload, 0 under-applied.
`ErasesDecl.ctor` must **not** drop parameters; they arrive through `Erases.app` and are boxed by
`Erases.box` because a type parameter is `Erasable`. N4 (`remove_irrel_constr_args = false`) stays
pinned and is load-bearing for the arity bookkeeping, not only for pruning soundness.

**Q6 — is `FirstOrderInd` `[L Def. 14]` / `[L Def. 6]`? — Def. 14 yes, Def. 6 no; and it is not
`[S §7.3]` verbatim.** MetaRocq's shipped `firstorder_ind` is **false on `nat`** (a wrong sort
conjunct, `PCUICFirstorder.v:59`, reproduced three ways by `vm_compute`), so it may be cited as the
origin and never transcribed. `[L Def. 14]` is exactly the `fields` clause; `[L Def. 6]` is
`firstorder_no_box`'s *conclusion*, not a definition — the fidelity table's shared row splits in
two. The signature `FirstOrderInd (env : VEnv) (I : Name)` is unwritable because `VEnv` stores no
inductive declarations (`Theory/VEnv.lean:17-23`); re-type it through `VEnv.WF`'s declaration list
(`HasInduct`). Acceptance criterion 8 narrows to `Nat`, `Bool`, `Tree` — `List Nat` and `Nat × Nat`
are outside both papers' predicates and outside the domain (the predicate is on the *declaration*),
and all five benchmarks return `Nat`, so `FirstOrderInd envC ``Nat` is the entire requirement.

**Q7 — `Quot`. — RESTRICT (N16).** Nothing in the five programs touches it; the eraser emits
`Quot.mk/lift/ind` as body-less axioms (`Erasure.lean:873-877`), so a quotient program erases to a
stuck term; lean4lean models `Quot.lift`'s ι-rule but not `Quot.ind`'s. `ErasesDecl.quot` is
**deleted** from T3 — it promised an `ElimBody` obligation nothing constructs, consumes or
validates. `Quot.sound` is **not** restricted: it is `Prop`-typed, hence `Erasable`, hence boxed,
and `ErasableAxioms` covers it. The `Quot.ind` theory/checker divergence is raised upstream (N15).

**Q8 — mechanical comparison with MetaRocq's `erases`. — SCOPED OUT, with the table mandatory.**
The §3.3 rule-by-rule table ships next to `Erases.lean` in W1 and is CI-checked for coverage of
every `[S Fig. 18]` rule and every `Erases` rule. A Rocq transport reaching the *relation* is
declined and the decline is recorded as a ledger row with its reason: the source side is
`Lean.Expr` + lean4lean's `VEnv`/`TrExprS`, which have no PCUIC counterpart, so transporting the
relation means transporting lean4lean's model — out of proportion. What *is* in scope, optionally
at W6, is finishing the transport that already exists (`rocq/` covers `LBTerm` and `WcbvEval`) with
a machine-checked `WcbvEval ↔ EWcbvEval` rule correspondence.

### 2.2 Acceptance criteria, one line each

| # | How it is met | Wave |
|---|---|---|
| 1 | `Erases` has ten rules; signature is `(env : VEnv) (Us : List Name) : VLCtx → Expr → LBTerm → Prop`. `ErasureContext.lean` is deleted, so the grep is empty by construction | W1 |
| 2 | No rule mentions `.construct`/`.case`/`.fix`; a CI grep over `Erases.lean`'s inductive block asserts it | W1 |
| 3 | `doc/Erases-vs-Fig18.md` tracked next to `Erases.lean`; CI checks it names all 13 Fig. 18 rules and all 10 `Erases` rules | W1 |
| 4 | One `inductive SEval`, one `ErasesEnv`, one `PrimSpec`, one `test/Ledger.lean`; CI greps for `inductive SEval`, `*BridgeHyps`, `Registered*` and fails on >1 | W1 (S), W4 (B) |
| 5 | Five passes, each an `LBPass` with `correct` and a `NonVacuity` guard; `LBLower.correct`/`LBDeliver.correct` are `LBPass.comp` applications | W1–W3 |
| 6 | T5 has exactly five binders (`henv`, `hwt`, `hev`, `her`, `hΣ`); CI greps its statement for the forbidden names | W1 (at `⟨delta⟩`), W3 (full) |
| 7 | `SubsingletonElim` appears once, in `ErasesDecl.elim`, and is derived from `envC.WF` modulo the one upstream ask; `Eq.rec`/`And.rec`/`Iff.rec`/`False.rec`/`Decidable` are inside, `Acc.rec` is N17 with a ledger row | W3 |
| 8 | `firstOrderIndB` decides `true` on `Nat`, `Bool`, `Tree`; criterion narrowed per Q6, with the narrowing recorded in the criterion's own row | W1 |
| 9 | `OracleDischarge` is imported by `Green.lean` and by T8; `PrimSpec.oracle_sound` is a *theorem* from `ResidualHyps.oracle_refl` via `kernel_isErasable_sound` | W4 |
| 10 | `Erases.sort_erasable`/`Erases.forallE_erasable` refute two sites; `doc/panic-table.md` lists all 16 with the excluding premise; CI checks the count against `grep -c 'panic!\|unreachable!' Erasure.lean` | W4 |
| 11 | `supportedB : SourceTable → Expr → Except SupportError Unit` — an `Except`, not a `Bool`, so the *hole is named*; `SupportError.sparseCasesOn` is a constructor, and the coverage table is generated by running it | W1 (v1), W4 (final) |
| 12 | `LBWfPeregrine` = `EWellformed(all_env_flags)` + `etaCtors` (spine ≥ `cstrArity` from Σ). It does **not** claim `expanded_eprogram`, which is measured false; the gap is one ledger row and one raised finding (§8) | W1 (def), W5 |
| 13 | `green_G8` elaborates under `lake build` with every hypothesis inhabited | W5 |
| 14 | `doc/coverage.md`, generated by `lake exe coverage`, one row per program with the first `SupportError` and the discharged/undischarged hypothesis list | W5 |
| 15 | `test/Ledger.lean` prints axioms for T5, `LBLower_correct`, `LBDeliver_correct`, T8, T9, `green_G*`; diffed against `test/axioms.expected` | W1, extended each wave |
| 16 | The CI job re-measures `sorryAx` roots at the pinned rev and distinguishes fork-authored (`VEnv.WF.patsStrong`) from inherited | W1 |
| 17 | CI greps for `sorry`/`axiom` in `LeanToLambdaBox/`; `PrimSpec` is a `structure`; every class-C hypothesis is a named binder listed in `doc/hypotheses.md` | W1 |
| 18 | CI grep for slice tags/hashes/dates/`memory `/`used to`/`no longer`/`retired`; comment fraction computed by `lake exe hygiene` and asserted < 20% | W1, enforced thereafter |
| 19 | `lake exe hygiene` resolves every backticked identifier in a docstring against the environment and every cited path against the repo | W2 |
| 20 | `lake exe hygiene` computes the import closure of `Green.lean` + `test/Ledger.lean` and diffs against `doc/exceptions.md` | W4 |
| 21 | **Amended.** `CheckerAdequacy.lean` declares 8 `Lean4Lean.TypeChecker`-namespace declarations and is on criterion 9's critical path. Resolution: upstream `M.WF.run'`, `VState.WF.initial` and `VContext.ofMLCtx` to lean4lean (they are kernel-generic, N15), and keep `kernel_isErasable_sound` here under the `LeanToLambdaBox` namespace. Until upstream lands, criterion 21 reads "no `Lean4Lean`-namespace declaration except the four named in `doc/upstream-asks.md`" | W4 |
| 22 | `.github/workflows/build.yml` triggers on the verification branch; `lakefile.toml` pins the measured rev; the branch consumers pin is the one CI builds | W5 |

---

## 3. Core definitions

Exact proposed signatures. Everything below type-checks against the pinned lean4lean (rev
`20ec229`) accessor set unless marked *(new upstream ask)*.

### 3.1 `LBTerm` — unchanged

No change. `LBTerm` is `Basic.lean:90`, shipping code, and already matches `[S Fig. 16]` + `.fvar`
+ `.prim`, no `tCoFix`, branches carrying `List BinderName`. **Zero transpiler edits here.**

### 3.2 Flags

```lean
-- LeanToLambdaBox/Semantics/Flags.lean
def eraseFlags  : WcbvFlags := ⟨with_prop_case := true,  with_guarded_fix := true,
                                with_constructor_as_block := false⟩
def targetFlags : WcbvFlags := ⟨with_prop_case := false, with_guarded_fix := true,
                                with_constructor_as_block := false⟩
def blockFlags  : WcbvFlags := ⟨with_prop_case := false, with_guarded_fix := true,
                                with_constructor_as_block := true⟩   -- peregrine's pass 8 output
```

`defaultFlags`/`optFlags`/`appliedFlags` are deleted; the tree's `targetFlags = ⟨false,false,true⟩`
is redefined (nothing is stated at it today). `Flags.lean:19-24`'s header is rewritten: both forms
are modelled, the shipping path is applied form, block form exists for `Optimize`'s generality and
for `blockFlags`.

### 3.3 `Erases` — ten rules, one `VEnv`, no registry

```lean
-- LeanToLambdaBox/Erases.lean
/-- Binder names are filtered exactly as `Erasure.fvar_to_name` filters them. -/
def binderOf (n : Lean.Name) : BinderName := …          -- = the eraser's filter, one definition

/-- `S` is the `k`-th type of a single-constructor block `decl` with `np` parameters and
`nf` fields. Pure lean4lean data; replaces the eraser's `Γ.projs`/`Γ.ctorFields` columns. -/
structure StructureOf (env : VEnv) (S : Name) (decl : VInductDecl) (k np nf : Nat) : Prop where
  has    : env.HasInduct decl
  named  : (decl.types[k]?).map (·.name) = some S
  pars   : decl.nparams = np
  single : ∃ c, (decl.types[k]?).map (·.ctors) = some [c] ∧ c.type.piArity - np = nf

/-- The canonical `Name → InductiveId` translation, a function of the *declaration*. -/
def VInductDecl.iidOf (decl : VInductDecl) (k : Nat) : InductiveId :=
  ⟨toKername ((decl.types.head?).map (·.name) |>.getD .anonymous), k⟩

inductive Erases (env : VEnv) (Us : List Name) : VLCtx → Expr → LBTerm → Prop
  | box   {Δ e ve} (htr : TrExprS env Us Δ e ve)
          (her : Erasable env Us.length Δ.toCtx ve) :
          Erases env Us Δ e .box
  | bvar  {Δ i e' A} (h : Δ.find? (.inl i) = some (e', A)) :
          Erases env Us Δ (.bvar i) (.bvar i)
  | fvar  {Δ x e' A} (h : Δ.find? (.inr x) = some (e', A)) :
          Erases env Us Δ (.fvar x) (.fvar x)
  | const {Δ c us ci} (h : env.constants c = some ci) :
          Erases env Us Δ (.const c us) (.const (toKername c))
  | app   {Δ f f' a a'} (hf : Erases env Us Δ f f') (ha : Erases env Us Δ a a') :
          Erases env Us Δ (.app f a) (.app f' a')
  | lam   {Δ n ty bi b b'} {ty' : VExpr} (hty : TrExprS env Us Δ ty ty')
          (hb : Erases env Us ((none, .vlam ty') :: Δ) b b') :
          Erases env Us Δ (.lam n ty b bi) (.lambda (binderOf n) b')
  | letE  {Δ n ty nd v v' b b'} {ty' val' : VExpr}
          (hty : TrExprS env Us Δ ty ty') (hval : TrExprS env Us Δ v val')
          (hv : Erases env Us Δ v v')
          (hb : Erases env Us ((none, .vlet ty' val') :: Δ) b b') :
          Erases env Us Δ (.letE n ty v b nd) (.letIn (binderOf n) v' b')
  | proj  {Δ S i e t decl k np nf} (hs : StructureOf env S decl k np nf) (hi : i < nf)
          (hd : Erases env Us Δ e t) :
          Erases env Us Δ (.proj S i e) (.proj ⟨decl.iidOf k, np, i⟩ t)
  | lit   {Δ l t} (hcl : env.ContainsLits l) (h : Erases env Us Δ l.toConstructor t) :
          Erases env Us Δ (.lit l) t
  | mdata {Δ d e t} (h : Erases env Us Δ e t) :
          Erases env Us Δ (.mdata d e) t
```

Two lemmas that refute two panic sites, required by criterion 10:

```lean
theorem Erases.sort_erasable    (henv : env.WF) (h : TrExprS env Us Δ (.sort u) ve) :
    Erases env Us Δ (.sort u) .box
theorem Erases.forallE_erasable (henv : env.WF) (h : TrExprS env Us Δ (.forallE n a b bi) ve) :
    Erases env Us Δ (.forallE n a b bi) .box
```

### 3.4 The pass layer

```lean
-- LeanToLambdaBox/Pass/Basic.lean
structure CtorShape  where iid : InductiveId; cidx : Nat; npars : Nat; nfields : Nat
structure CasesShape where
  iid : InductiveId; npars : Nat; arity : Nat; discrPos : Nat
  altBinders : List (List BinderName)          -- per constructor, in constructor order

/-- Everything the Lean-specific passes consume that is static per constant. Each field is a
pure function of the `Lean.Environment`; adequacy is a theorem from `PrimSpec.lookup_adequate`,
not a new obligation. Inert for evaluation. -/
structure CompileTable where
  ctor  : Kername → Option CtorShape
  cases : Kername → Option CasesShape
  ind   : Kername → Option (InductiveId × Nat)
  block : Kername → Option (List Kername)      -- ci.all order; singleton on 50/50 of the corpus

def CompileTable.of (lenv : Lean.Environment) : CompileTable := …

structure LBPass where
  term    : CompileTable → LBTerm → LBTerm
  decls   : CompileTable → GlobalDeclarations → GlobalDeclarations
  flIn    : WcbvFlags
  flOut   : WcbvFlags
  correct : ∀ {E Σ t v}, LBWf Σ → LBClosed 0 t → WcbvEval Σ flIn t v →
            WcbvEval (decls E Σ) flOut (term E t) (term E v)

/-- A pass that does not fire is correct on that program for free. This is what lets `LBLower`
be the full composition from wave 1 while only the passes a rung exercises are proved. -/
structure LBPass.Inert (p : LBPass) (E : CompileTable) (Σ : GlobalDeclarations) (t : LBTerm)
    : Prop where
  tm : p.term E t = t
  en : p.decls E Σ = Σ
theorem LBPass.correct_of_inert {p E Σ t v} (h : p.Inert E Σ t) (hv : p.Inert E Σ v)
    (hfl : p.flIn = p.flOut) : WcbvEval Σ p.flIn t v → WcbvEval (p.decls E Σ) p.flOut (p.term E t) (p.term E v)

def LBPass.comp (q p : LBPass) (h : p.flOut = q.flIn) : LBPass
```

The five passes:

| Pass | `term` | `decls` | flIn → flOut | Hardest lemma |
|---|---|---|---|---|
| `ctorInline` | `.const c` applied ⇝ `.construct iid k []` applied, at `E.ctor c = some s` | pointwise on bodies | `eraseFlags → eraseFlags` | δ+β preservation against `ErasesDecl.ctor` |
| `elimInline` | saturated `casesOn`-like head ⇝ `.case`, minors β-normalised to alts, over-application left outside | pointwise, then drops the `elim` declarations it inlined | `eraseFlags → eraseFlags` | `IotaBridge` (β-chain of field applications = `iota_red`) — **in hand**, 207 lines |
| `fixIntro` | identity | a `ConstantDecl` body mentioning its own kername ⇝ `.fix defs i` at `E.block` order | `eraseFlags → eraseFlags` | `closeFix_substList_fixSubst` — **in hand**, `FixUnfold`+`FixMetatheory`, 1,184 lines |
| `optimize` | `[S §7.4]` Prop-case expansion + `projCollapse` | pointwise | `⟨true,g,b⟩ → ⟨false,g,b⟩` | `LBOptimize_correct` — **proved**, needs generalising over `b` (four new arms: `construct_atom`, `construct_app`, `iota`, `proj`) |
| `pruneEnv` | identity | keep exactly the declarations reachable from `t` | `f → f` | reachability preserves `WcbvEval` (standard) |

```lean
def LBLower   : LBPass := (fixIntro.comp (elimInline.comp ctorInline rfl) rfl)   -- T8's factor
def LBDeliver : LBPass := (pruneEnv.comp optimize rfl)                          -- T9's tail
```

`ctorInline` and `elimInline` act on disjoint `.const` heads; a commutation lemma
`ctorInline_elimInline_comm` makes the composition order immaterial and is proved once.

### 3.5 `ErasesDecl` / `ErasesEnv`

```lean
-- LeanToLambdaBox/ErasesEnv.lean
/-- The enumerated relevant axioms (T9). `realizer = none` means "assumed never to occur in a
relevant position"; `some r` records the λ□ body peregrine's `.attr` channel is assumed to
supply, with its evaluation spec. Class **D**. -/
structure AxiomSpec where
  name     : Name
  realizer : Option LBTerm
  spec     : ∀ Σ, realizer.isSome → Prop
abbrev AxiomTable := List AxiomSpec

inductive ErasesDecl (env : VEnv) (tbl : AxiomTable) : Name → Kername → GlobalDecl → Prop
  /-- A definition: the body is read off `env.defeqs` — at the capstone `env` is `envC`, so this
      is the *compiler* body (Q3). `VConstant` carries no body at the pinned rev. -/
  | defn  {c us vbody ty body b'}
          (hd  : env.defeqs ⟨us.length, .const c (levelParamsOf us), vbody, ty⟩)
          (htr : TrExprS env us [] body vbody)
          (he  : Erases env us [] body b') :
          ErasesDecl env tbl c (toKername c) (.constantDecl ⟨some b'⟩)
  /-- A body-less constant: a real axiom, a recursor reached as a constant (measured: `Eq.rec`
      in `Fannkuch.ast`), `@[extern]` at `.preferAxiom`, or a `Quot` primitive. Admitted only
      with an `AxiomSpec` row. -/
  | ax    {c ci} (h : env.constants c = some ci) (hno : ¬ HasDefn env c)
          (hok : ∃ s ∈ tbl, s.name = c) :
          ErasesDecl env tbl c (toKername c) (.constantDecl ⟨none⟩)
  | ind   {decl} (h : env.HasInduct decl) :
          ErasesDecl env tbl (blockHead decl) (toKername (blockHead decl))
                     (.inductiveDecl (lowerInduct decl))
  | ctor  {decl k j c} (h : env.HasInduct decl) (hc : ctorNameAt decl k j = some c) :
          ErasesDecl env tbl c (toKername c)
                     (.constantDecl ⟨some (.construct (decl.iidOf k) j [])⟩)
  /-- The eliminator runtime library. Lives only in the *specification* environment Σ⁺;
      `elimInline` δ-expands it and `pruneEnv` removes it, so it never reaches `.ast`
      (measured: 0 recursor/`casesOn` declarations in all five files). It is nevertheless
      load-bearing: `elimInline.correct` is a statement about Σ⁺, and without a body for the
      eliminator constant the pass would not be semantics-preserving. -/
  | elim  {decl k c body} (h : env.HasInduct decl) (hc : ElimConstant env decl k c)
          (hb : ElimBody env decl k body) :
          ErasesDecl env tbl c (toKername c) (.constantDecl ⟨some body⟩)

/-- `erases_deps` — dependency-selective, bottom-up, the only environment relation. -/
structure ErasesEnv (env : VEnv) (tbl : AxiomTable)
    (Σ : GlobalDeclarations) (t : LBTerm) : Prop where
  keys    : (Σ.map Prod.fst).Nodup
  sound   : ∀ kn d, Σ.lookup kn = some d → ∃ c, toKername c = kn ∧ ErasesDecl env tbl c kn d
  closedT : ∀ kn ∈ t.consts, (Σ.lookup kn).isSome
  closedΣ : ∀ kn d, Σ.lookup kn = some d → ∀ kn' ∈ d.consts, (Σ.lookup kn').isSome
  ordered : ∀ kn d, Σ.lookup kn = some d → ∀ kn' ∈ d.consts, kn' ∈ declsBefore Σ kn
```

`ElimBody env decl k body` is the obligation "the λ□ body's evaluation reproduces the kernel's
ι-rule for the `k`-th type's eliminator at every constructor", stated against `env.pats` and
discharged generically for the plain `casesOn` shape, with `SubsingletonElim` as the side
condition in the `Prop`-valued case:

```lean
def SubsingletonElim (env : VEnv) (decl : VInductDecl) (k : Nat) : Prop :=
  ∃ ℓ, ¬ ℓ.IsNeverZero ∧
    ((decl.types[k]?).map (·.ctors) = some [] ∨
     ∃ c, (decl.types[k]?).map (·.ctors) = some [c] ∧
       ∀ i < c.type.piArity - decl.nparams,
         ∃ F, c.type.piBinders[decl.nparams + i]? = some F ∧
           env.HasType decl.uvars (c.type.fieldCtx decl.nparams i) F (.sort .zero))

/-- Derived, not assumed. One link is the upstream ask `VEnv.WF'.consts_origin` (N15). -/
theorem subsingletonElim_of_wf (henv : env.WF) (h : env.HasInduct decl)
    (hlarge : LargeElimAdmitted env decl k) : SubsingletonElim env decl k
```

### 3.6 `SEval` and `SEvalFlags`

```lean
-- LeanToLambdaBox/SourceEval.lean
structure SEvalFlags where
  beta, delta, zeta, iota, proj, lit : Bool
  deriving DecidableEq, Repr
instance : LE SEvalFlags := ⟨fun a b => a.beta ≤ b.beta ∧ a.delta ≤ b.delta ∧ a.zeta ≤ b.zeta ∧
                                        a.iota ≤ b.iota ∧ a.proj ≤ b.proj ∧ a.lit ≤ b.lit⟩
def δ  : SEvalFlags := { beta := false, delta := true,  zeta := false, iota := false,
                         proj := false, lit := false }                    -- wave 1
def βδ : SEvalFlags := { δ with beta := true }                            -- wave 2
def full : SEvalFlags := ⟨true, true, true, true, true, true⟩             -- wave 3

/-- Weak call-by-value big-step evaluation on `Lean.Expr`, `[S §5.6]`, one relation.
`env` is the *compiler* environment `envC`: δ unfolds `env.defeqs`, ι consults `env.pats`. -/
inductive SEval (env : VEnv) (Us : List Name) (fl : SEvalFlags) : VLCtx → Expr → Expr → Prop
  | value    {Δ e}        (hv : SValue env Δ e) : SEval env Us fl Δ e e
  | beta     {Δ f a n ty b bi av v} (h : fl.beta = true) …
  | delta    {Δ c us body v} (h : fl.delta = true)
             (hd : env.defeqs ⟨us.length, .const c us', vbody, ty⟩)
             (htr : TrExprS env Us [] body vbody) (hv : SEval env Us fl Δ body v) :
             SEval env Us fl Δ (.const c us) v
  | zeta     {Δ n ty v b nd w} (h : fl.zeta = true) …
  | iota     {Δ} (h : fl.iota = true) …           -- via `env.pats`, `Pattern.Matches`
  | proj     {Δ S i e j args v} (h : fl.proj = true) …
  | lit      {Δ l v} (h : fl.lit = true) (hv : SEval env Us fl Δ l.toConstructor v) :
             SEval env Us fl Δ (.lit l) v
  | mdata    {Δ d e v} (hv : SEval env Us fl Δ e v) : SEval env Us fl Δ (.mdata d e) v
  | app_cong {Δ f a f' a'} …                       -- stuck head, arguments evaluated

theorem SEval.mono  {fl fl'} (h : fl ≤ fl') : SEval env Us fl Δ e v → SEval env Us fl' Δ e v
theorem SEval.defeq (henv : env.WF) (hΔ : VLCtx.WF env Us.length Δ)
    (htr : TrExprS env Us Δ e ve) (hev : SEval env Us fl Δ e v) :
    ∃ vv, TrExprS env Us Δ v vv ∧ env.IsDefEqU Us.length Δ.toCtx ve vv
theorem SEval.value_idem : SEval env Us fl Δ e v → SEval env Us fl Δ v v
```

`SEval.defeq` is the single re-anchoring of `SubjectReduction{,Full,Iota}` (1,414 lines → ~1,050);
`SEvalβζδ_defeq_spine`'s abstract-`P` schema (`SubjectReductionFull.lean:309`) is the template that
makes it one proof rather than three.

### 3.7 The output predicate

```lean
-- LeanToLambdaBox/Output.lean
/-- What `untyped_transform_pipeline` needs from us, stated on the emitted program alone.
`fresh`…`projDecl` are `EWellformed all_env_flags`, i.e. what `peregrine validate` checks;
`etaCtors` is the additional constructor-saturation invariant `validate` omits and
`remove_params_optimization` consumes (measured 982/982). `expanded_eprogram` (fixpoint
η-expansion) is **not** claimed: it is false on all five programs — see §8, finding F-ETA. -/
structure LBWfPeregrine (Σ : GlobalDeclarations) (t : LBTerm) : Prop where
  fresh       : (Σ.map Prod.fst).Nodup
  declsWf     : ∀ kn d, Σ.lookup kn = some d → LBWfDecl (declsBefore Σ kn) d
  closed      : LBClosed 0 t
  constsOk    : ∀ kn ∈ t.consts, (Σ.lookup kn).isSome
  ctorApplied : NoBlock t ∧ NoBlockEnv Σ
  ctorDecl    : ∀ iid k, OccursConstruct Σ t iid k → ResolvesCtor Σ iid k
  casesExh    : ∀ iid np brs, OccursCase Σ t iid np brs → brs.length = numCtors Σ iid
  fixLambda   : ∀ defs i, OccursFix Σ t defs i → i < defs.length ∧ ∀ d ∈ defs, d.body.isLambda
  projDecl    : ∀ p, OccursProj Σ t p → ResolvesProj Σ p
  etaCtors    : ∀ iid k n, ConstructSpine Σ t iid k n → n ≥ cstrArity Σ iid k

/-- What peregrine's first pass actually requires. `LBWfPeregrine` is strictly weaker; the
difference is exactly `fixEta` (§6 W6, §8 F-ETA). -/
def PeregrinePre (Σ) (t) : Prop := LBWfPeregrine Σ t ∧ LBExpandedFix Σ t
```

### 3.8 `PrimSpec`, `Supported`, `ErasableAxioms`, `CompilerEnv`, `FirstOrderInd`

```lean
-- LeanToLambdaBox/PrimSpec.lean
/-- The one assumed interface: specifications of external `MetaM`/`CoreM` primitives this
development cannot execute. Built by renaming `OracleDischarge.ResidualHyps` (which already has
fields 2–4 in this shape) and adding `env_connect` and `ind_adequate`. Never an `axiom`. -/
structure PrimSpec (lenv : Lean.Environment) (env : VEnv) : Prop where
  env_connect     : ∃ ves : VEnvs, ves.WF lenv ∧ ves.venv .safe = env
  lookup_adequate : ∀ n, LookupAgrees lenv env n     -- getConstInfo / getCasesInfo? /
                                                      -- LCNF.getCtorArity? / LCNF.getDeclInfo?
  fresh_names     : FreshDiscipline lenv
  oracle_refl     : OracleReflects lenv env          -- the *reflection* residue only
  ind_adequate    : ∀ I, InductiveAgrees lenv env I  -- InductiveVal ↔ VInductDecl (Q6.6 field 5)

theorem PrimSpec.envWF (P : PrimSpec lenv env) : env.WF          -- via TrEnv'.wf
theorem PrimSpec.oracle_sound (P : PrimSpec lenv env) :          -- *proved*, not assumed
    Erasure.isErasable lps e = true → TrExprS env lps Δ e ve → Erasable env lps.length Δ.toCtx ve
theorem PrimSpec.table_adequate (P : PrimSpec lenv env) :
    CompileTableAdequate (CompileTable.of lenv) env
```

`abs_env_irr` is **not** a field and is not needed: `env` is a parameter of every theorem, not an
output of the function, so `[S §6.2]`'s uniqueness obligation has no work to do here. Recorded in
the fidelity table as a deliberate simplification.

```lean
-- LeanToLambdaBox/Supported.lean
inductive SupportError where
  | sparseCasesOn (c : Name)        -- `_sparseCasesOn_`: the measured Quicksort miscompile
  | sideConditionElim (c : Name)    -- per-constructor eliminator: altsRange skips an argument
  | etaContractedMinor (c : Name)   -- a minor that is not a λ-chain of the alt's arity
  | strLit | machineNat | quotPrim (c : Name) | ioLike (c : Name) | implementedBy (c : Name)
  | mvar | fixNameOccursMismatch (c : Name) | unknownConst (c : Name)
  deriving Repr, DecidableEq

/-- Decidable, over `e` **and its dependency closure**, and it *names the hole*. The coverage
table is generated by running it; `Bool` would lose the name. -/
def supportedB (tbl : SourceTable) (e : Expr) : Except SupportError Unit

def Supported (env : VEnv) (e : Expr) : Prop := …          -- named conjuncts, one per SupportError
theorem supportedB_sound (P : PrimSpec lenv env) (ht : SourceTableAdequate lenv tbl) :
    supportedB tbl e = .ok () → Supported env e
```

```lean
-- LeanToLambdaBox/Axioms.lean
/-- `[S §5.6]`'s `axiom_free` is uninhabited in Lean (`propext`/`Quot.sound`/`Classical.choice` are
in every realistic closure). The generalisation: every body-less constant in the *erased* closure
is either `Prop`-typed — hence `Erasable`, hence boxed, hence never a stuck head — or carries an
`AxiomSpec` row. `Classical.choice` is neither and is excluded by dependency tracking. -/
def ErasableAxioms (env : VEnv) (tbl : AxiomTable) (e : Expr) : Prop :=
  ∀ c ∈ depClosure env e, ¬ HasDefn env c →
    (ProofTyped env c ∨ ∃ s ∈ tbl, s.name = c)
def erasableAxiomsB (tbl : SourceTable) (at : AxiomTable) (e : Expr) : Bool
```

```lean
-- LeanToLambdaBox/CompilerEnv.lean
/-- N8, resolved as an extension (Q3). Class **C**, decidable per program: F1 measured all 33
compiler bodies kernel-typeable at the declared type. -/
structure CompilerEnv (env envC : VEnv) (lenv : Lean.Environment) (e : Expr) : Prop where
  le     : env ≤ envC
  wf     : envC.WF
  consts : envC.constants = env.constants        -- `addDefEq` never touches constants
  bodies : ∀ c ∈ depClosure env e, ∀ b, compilerBody lenv c = some b →
             ∃ vb ty, TrExprS env (levelParams lenv c) [] b vb ∧
                      envC.defeqs ⟨_, .const c _, vb, ty⟩
  only   : ∀ d, envC.defeqs d → env.defeqs d ∨ IsCompilerDefn lenv d
```

```lean
-- LeanToLambdaBox/FirstOrder.lean
def VEnv.HasInduct (env : VEnv) (decl : VInductDecl) : Prop :=
  ∃ ds, VEnv.WF' ds env ∧ VDecl.induct decl ∈ ds
def FOType (fo : Name → Prop) (n k : Nat) : VExpr → Prop
  | .const I _ => fo I
  | .bvar i    => k ≤ i ∧ i < n + k
  | _          => False
structure VInductDecl.FirstOrder (env : VEnv) (fo : Name → Prop) (decl : VInductDecl) : Prop where
  mono        : decl.uvars = 0
  informative : ∀ t ∈ decl.types, ∃ ℓ, t.type.piBody = .sort ℓ ∧ ℓ.IsNeverZero
  noIndices   : ∀ t ∈ decl.types, t.type.piArity = decl.nparams
  fields      : ∀ t ∈ decl.types, ∀ c ∈ t.ctors, ∀ i < c.type.piArity,
                  ∃ A, c.type.piBinders[i]? = some A ∧ FOType fo decl.types.length i A
def FirstOrderInd (env : VEnv) (fo : Name → Prop) (I : Name) : Prop :=
  ∃ decl, env.HasInduct decl ∧ decl.FirstOrder env fo ∧ ∃ t ∈ decl.types, t.name = I
def firstOrderIndB (tbl : SourceTable) (fuel : Nat) (I : Name) : Bool
theorem firstOrderIndB_sound (P : PrimSpec lenv env) (ht : SourceTableAdequate lenv tbl) :
    firstOrderIndB tbl fuel I = true → FirstOrderInd env (foClosure tbl) I
```

*(This definition elaborates clean against the pinned lean4lean — probe `q6.lean`, axioms
`[propext, Quot.sound]`.)*

### 3.9 The witness generator

```lean
-- LeanToLambdaBox/Witness/SourceTable.lean
/-- A reified, committed slice of the `Lean.Environment`: the `prepare_erasure`d bodies of the
dependency closure, the inductive metadata, and — crucially — **the relevance oracle's verdict at
every subterm position**, recorded when the fixture was generated. With the verdicts in the table
the model eraser needs no `MetaM`, and its soundness reduces pointwise to `PrimSpec.oracle_sound`.
Generated by `lake exe reify`, byte-diffed in CI. -/
structure SourceTable where
  decls   : List (Name × ReifiedDecl)
  inds    : List (Name × ReifiedInduct)
  oracle  : List (Name × List (SubtermPos × Bool))
  cfg     : Erasure.ErasureConfig

-- LeanToLambdaBox/Witness/EraseB.lean
/-- The L2 *function* both papers have and this tree never had (`[L Def. 3]`, `[S Fig. 17]`):
total, structural, table-driven, no monad, no fresh names, no `partial_fixpoint`. It is **not** a
bridge — `EraseCore.lean`'s 2026-07-07 addendum refuted that, correctly, and this file says so in
one line. Its job is to supply `Erases`/`ErasesEnv` witnesses at benchmark scale. -/
def eraseB (tbl : SourceTable) (e : Expr) : Except SupportError (GlobalDeclarations × LBTerm)

theorem eraseB_sound (P : PrimSpec lenv env) (hC : CompilerEnv env envC lenv e)
    (ht : SourceTableAdequate lenv tbl) (hrun : eraseB tbl e = .ok (Σ, t)) :
    ∃ Σ⁺ t₀, Erases envC [] [] e t₀ ∧ ErasesEnv envC tbl.axioms Σ⁺ t₀ ∧
             t = LBLower.term (CompileTable.of lenv) t₀ ∧
             Σ = pruneEnv.decls (LBLower.decls (CompileTable.of lenv) Σ⁺)
```

### 3.10 The certified evaluators

```lean
-- LeanToLambdaBox/Witness/SrEval.lean
def srEval (tbl : SourceTable) (fl : SEvalFlags) (fuel : Nat) : Expr → Option Expr
theorem srEval_sound (P : PrimSpec lenv env) (hC : CompilerEnv env envC lenv e)
    (ht : SourceTableAdequate lenv tbl) (h : srEval tbl fl fuel e = some v) :
    SEval envC [] fl [] e v

-- LeanToLambdaBox/Semantics/Compute.lean
def lbEval (Σ : GlobalDeclarations) (fl : WcbvFlags) (fuel : Nat) : LBTerm → Option LBTerm
theorem lbEval_sound (h : lbEval Σ fl fuel t = some v) : WcbvEval Σ fl t v          -- class A
```

`lbEval_sound` is class **A** and unconditional — every step of `lbEval` is one `WcbvEval` rule.
`srEval_sound` inherits `PrimSpec`'s class. Together they turn the two hypotheses that no previous
capstone ever discharged (`SEval …` and the concrete target evaluation) into `by rfl`.

`lbEval` doubles as a differential oracle: `lake exe green-check` compares `lbEval Σ targetFlags`
on the committed `.ast` with `peregrine eval Arith.ast` (CLAUDE.md's cheapest real functional
check), which is a cross-implementation agreement test on the λ□ semantics itself.

### 3.11 The ledger

```lean
-- test/Ledger.lean, in CI, diffed against test/axioms.expected
#print axioms LeanToLambdaBox.erases_correct
#print axioms LeanToLambdaBox.LBLower_correct
#print axioms LeanToLambdaBox.LBDeliver_correct
#print axioms LeanToLambdaBox.visitExpr_refines_erases
#print axioms LeanToLambdaBox.shipping_erase_correct
#print axioms LeanToLambdaBox.green_G8
```

Rows, measured, never narrated: (a) lean4lean's inherited `sorryAx` cluster by `file:line` at the
pinned rev, with `VEnv.WF.patsStrong` marked **fork-authored, not inherited**; (b) the ~29-name
`Lean4Lean`-executable-checker cluster that criterion 9 brings in, including the two
`_native.bv_decide` axioms from Lean core (`Lean.Expr.mkData_flags._native.bv_decide.ax_1_12`,
`Lean.Expr.Data.looseBVarRange_le._native.bv_decide.ax_1_7`) — routing the oracle in takes the
capstone from 8 axioms to 33, which the fixture must accommodate; (c) `PrimSpec`'s four assumed
fields (class **D**); (d) the class-**C** hypotheses; (e) the class-**E** rows: N10 serialisation,
N11 sidecars, N14 size, the `envC`/kernel propositional-agreement row, the peregrine `Admitted`
precondition row, and **F-ETA** (§8).

---

## 4. Theorems

### 4.1 T4 — subject reduction

```lean
theorem SEval.defeq {env : VEnv} (henv : env.WF) {Us : List Name} {Δ : VLCtx}
    (hΔ : VLCtx.WF env Us.length Δ) {fl : SEvalFlags} {e v : Expr} {ve : VExpr}
    (htr : TrExprS env Us Δ e ve) (hev : SEval env Us fl Δ e v) :
    ∃ vv, TrExprS env Us Δ v vv ∧ env.IsDefEqU Us.length Δ.toCtx ve vv
```

Exactly four binders beyond the derivation. No `SEnvConsistent`, no `IotaConsistent`, no
`ProjConsistent` — those were consequences of `Esrc` being a second, unconnected source
environment; with δ reading `env.defeqs` and ι reading `env.pats` directly, they are theorems of
`env.WF`, not hypotheses. Class **B**.

### 4.2 T5 — `erases_correct`

```lean
theorem erases_correct {env : VEnv} {Us : List Name} {fl : SEvalFlags} {tbl : AxiomTable}
    {e v : Expr} {ve : VExpr} {t : LBTerm} {Σ : GlobalDeclarations}
    (henv : env.WF)
    (hwt  : TrExprS env Us [] e ve)
    (hev  : SEval env Us fl [] e v)
    (her  : Erases env Us [] e t)
    (hΣ   : ErasesEnv env tbl Σ t) :
    ∃ v', Erases env Us [] v v' ∧ WcbvEval Σ eraseFlags t v'
```

Five hypotheses, none named `Supported`/`Relevant`/`Iota*`/`*Consistent`/`*Hyps`. The value's
erasure is existential — that is the point of the relation (`[S §7.3]`, `[L Ex. 4]`). Class **B**.

**Staging.** `erases_correct` is proved at increasing `fl`: W1 at `δ`, W2 at `βζδ+lit+proj`, W3 at
`full`. The statement never changes; only the flag instance does, and `SEval.mono` is the
inclusion. This is the design's widening axis and it is why a wave-1 green instance is affordable.

### 4.3 T6 — the passes

```lean
theorem ctorInline_correct : ctorInline.correct       -- W1
theorem elimInline_correct : elimInline.correct       -- W3, via IotaBridge
theorem fixIntro_correct   : fixIntro.correct         -- W3, via closeFix_substList_fixSubst
theorem optimize_correct {b : Bool} {Σ t v} :          -- W2, generalised over block form
    WcbvEval Σ ⟨true, g, b⟩ t v →
    WcbvEval (LBOptimize_env Σ) ⟨false, g, b⟩ (LBOptimize Σ t) (LBOptimize Σ v)
theorem pruneEnv_correct   : pruneEnv.correct         -- W1
theorem LBLower_correct    : LBLower.correct
theorem LBDeliver_correct  : LBDeliver.correct
```

Each ships a non-vacuity guard in the style of `Optimize.lean:1066` — a concrete `Σ`, `t`, `v`
where the hypotheses hold *and the pass actually fires* (the existing guard triple
`_hyps_satisfiable` / `_not_refutable` / `_fires` is the model and is reused verbatim). All class
**A**: no pass mentions `Expr` or lean4lean.

### 4.4 T7 — first-order values

```lean
theorem firstorder_erases_deterministic {env : VEnv} {Us fo I us args v t₁ t₂}
    (henv : env.WF) (hfo : FirstOrderInd env fo I)
    (hwt  : TrExprS env Us [] v vv)
    (hty  : env.HasType Us.length [] vv (mkApps (.const I us) args))
    (hval : SEval env Us fl [] v v)
    (h₁ : Erases env Us [] v t₁) (h₂ : Erases env Us [] v t₂) : t₁ = t₂

theorem firstorder_no_box {env : VEnv} {Us fo I us args v t}
    (henv : env.WF) (hfo : FirstOrderInd env fo I)
    (hwt : TrExprS env Us [] v vv)
    (hty : env.HasType Us.length [] vv (mkApps (.const I us) args))
    (hval : SEval env Us fl [] v v) (h : Erases env Us [] v t) : NoBox t
```

Class **B** (runs through `TrExprS.uniq`/`IsDefEq.uniqU`). `FirstOrder.lean:103-155`
(`informativeType_not_erasable`, `firstOrderValue_not_erasable`, ~55 lines) is re-indexed onto
`FirstOrderInd` and carries the proof content.

### 4.5 T8 — the bridge

```lean
theorem visitExpr_refines_erases
    {lenv : Lean.Environment} {env envC : VEnv} {tbl : AxiomTable}
    (P     : PrimSpec lenv env)
    (hcfg  : ConfigPinned cfg₀)                       -- §4.6
    (hcomp : CompilerEnv env envC lenv e)
    (hsup  : Supported envC e)
    (hwt   : TrExprS envC Us Δ e ve)
    (hinv  : RunInv P Us Δ cfg₀ ctx s (gw w))
    (hrun  : Erasure.visitExpr e s ctx cctx ref w = .ok (t, s') w') :
    ∃ (t₀ : LBTerm) (Σ⁺ : GlobalDeclarations),
        Erases envC Us Δ e t₀
      ∧ ErasesEnv envC tbl Σ⁺ t₀
      ∧ t = LBLower.term (CompileTable.of lenv) t₀
      ∧ s'.gdecls = pruneEnv.decls (LBLower.decls (CompileTable.of lenv) Σ⁺) ++ s.gdecls
      ∧ RunConcl P s s' ∧ gw w ≤ gw w'
```

Four corrections to the spec's shape, each measured: the subject of the *capstone* is
`prepare_erasure e` (Q1 §2.8); the passes read a `CompileTable`, not `s'.gdecls` (Q1 §3.1); the
run's environment is the **pruned image** of the specification's (Q4.5(2)/F5); and `envC`, not
`env`, indexes the relation (Q3). `PrimSpec` replaces seven bundles. Class **B**, with
`PrimSpec` fields 1–3, 5 at **D** and field 4 (`oracle_sound`) *proved* from `oracle_refl` via
`kernel_isErasable_sound` — the development's one trust reduction, in the capstone's import
closure by construction.

**Panics.** `.ok` does not exclude a panicked run. The theorem carries `hnp : ¬ run.panicked`
*only for the fourteen sites that `Supported` does not already exclude*; `Erases.sort_erasable`
and `Erases.forallE_erasable` refute two outright, and `doc/panic-table.md` lists all sixteen with
the excluding premise (criterion 10).

### 4.6 T9 — the capstone, applied form

```lean
structure ConfigPinned (cfg : Erasure.ErasureConfig) : Prop where
  csimp   : cfg.csimp = false                              -- N1
  nat     : cfg.nat = .peano                               -- N3
  prune   : cfg.remove_irrel_constr_args = false           -- N4
  extern  : cfg.extern = .preferLogical                    -- N2
  inline  : cfg.auto_inline_typeclass_dispatch = false     -- N5

theorem shipping_erase_correct
    {lenv : Lean.Environment} {env envC : VEnv} {tbl : AxiomTable} {e : Expr} {cfg}
    (P     : PrimSpec lenv env)
    (hcfg  : ConfigPinned cfg)
    (hcomp : CompilerEnv env envC lenv e)
    (hwt   : TrExprS envC [] [] e ve)
    (hsup  : Supported envC (prepare e))
    (hax   : ErasableAxioms envC tbl (prepare e))
    (hnp   : ¬ Panicked run)
    (hrun  : Erasure.erase e cfg cctx ref w = .ok (.untyped Σ (some t), inls) w') :
      ErasesEnv envC tbl (LBLower.decls E Σ⁺) t'                     -- the program half
    ∧ LBWfPeregrine Σ t
    ∧ (∀ (args : List Expr) (targs : List LBTerm) (I : Name) (us idx) (v : Expr) (vv : VExpr),
         (∀ i, Erases envC [] [] args[i]! targs[i]!) →
         SEval envC [] full [] (mkApps e args) v →
         TrExprS envC [] [] v vv →
         envC.HasType 0 [] vv (mkApps (.const I us) idx) →
         FirstOrderInd envC (foClosure lenv) I →
         ∃ tv, Erases envC [] [] v tv ∧ NoBox tv ∧
               (∀ tv', Erases envC [] [] v tv' → tv' = tv) ∧
               WcbvEval (LBDeliver.decls E (LBLower.decls E Σ⁺)) targetFlags
                        (mkApps (LBDeliver.term E t) (targs.map (LBDeliver.term E))) tv)
```

At `args = []` this is the spec's T9 verbatim; at `args = [.lit 0]` it is the observation for
`benchArith`. The uniqueness conjunct `(∀ tv', … → tv' = tv)` is T7 and is what makes the
conclusion *an answer* rather than an existential. Class **B** + class-**C** binders `hcfg`,
`hcomp`, `hsup`, `hax`, `hnp`, and (inside the ∀) the source evaluation, per N7.

`ErasableAxioms` replaces `axiom_free`: this is the single change that moves benchmark coverage off
zero, and Arith needs it only vacuously (0 axioms in `Arith.ast`), while Fannkuch needs the
`Eq.rec` row.

### 4.7 T10 — non-vacuity, as a theorem

```lean
-- VerifyBench/Green.lean
example : ConfigPinned arithCfg                                  := by decide
example : supportedB arithTable (prepare eArith) = .ok ()        := by rfl
example : erasableAxiomsB arithTable [] (prepare eArith) = true  := by rfl
example : firstOrderIndB arithTable 64 ``Nat = true               := by rfl
theorem arith_compilerEnv : CompilerEnv env envC lenv eArith     := …   -- 4 TrExprS+HasType checks
theorem arith_seval : srEval arithTable full 100000 (mkApps eArith [.lit 0]) = some (peanoExpr 8)
  := by rfl

theorem green_G8
    (P : PrimSpec lenv env) (hcomp : CompilerEnv env envC lenv eArith) (hnp : ¬ Panicked run)
    (hrun : Erasure.erase eArith arithCfg cctx ref w = .ok (.untyped Σ (some t), inls) w') :
      LBWfPeregrine Σ t
    ∧ WcbvEval (LBDeliver.decls E (LBLower.decls E Σ⁺)) targetFlags
               (.app (LBDeliver.term E t) (peanoLB 0)) (peanoLB 8) := …
```

Plus `doc/coverage.md`, generated, one row per VerifyBench program stating what is covered and what
is not, in the honest style of the existing `VerifyBench/STATUS.md` — which is retired into it, not
duplicated.

---

## 5. Module plan

**Shipping (never edited): `Basic.lean`, `Erasure.lean`, `Printing.lean` (1,422 lines).**

### 5.1 Carried unchanged (≈ 5,700 lines)

| Module | Lines | Note |
|---|---|---|
| `Semantics/Eval.lean`, `Values.lean`, `Env.lean`, `Substitution.lean`, `Metatheory.lean` | 1,164 | flag-polymorphic, free |
| `Semantics/Flags.lean` | 61 | **header rewritten**, three flag constants redefined (§3.2) |
| `Closed.lean` | 871 | target-side, rule-set-independent |
| `Abstract.lean` | 423 | `toBvar` metatheory |
| `FixMetatheory.lean`, `FixUnfold.lean` | 1,184 | re-aimed at `fixIntro`, statements unchanged |
| `IotaBridge.lean` | 207 | re-aimed at `elimInline`, unchanged |
| `Erasability.lean` | 230 | `Erasable` + `[L Lemma 2]` stability kit |
| `Relevance.lean`, `RelevanceCheck.lean`, `CheckerAdequacy.lean`, `OracleDischarge.lean` | 495 | routed into the capstone; four declarations move upstream (criterion 21) |
| `Optimize.lean` | 1,090 | generalised over `with_constructor_as_block`; 14 arms verbatim, 3 die, 4 new |

### 5.2 Re-anchored

| Module | Lines | What changes |
|---|---|---|
| `Erases.lean` | 1,426 → ~700 | six rules deleted, `mdata` added, `ErasureCtx` index removed, `proj` re-keyed on `StructureOf`, `const` loses registry premises; the ~30 fixtures split — `natLit`/`proj` families kept as guards, `fixRec`/`fixMut`/`fixOpen` deleted with their rules |
| `ErasesAbstract.lean`, `ErasesStrengthen.lean`, `ErasesUniform.lean` | 1,865 → ~1,200 | per-rule inductions: nine surviving arms transfer verbatim, six die; three `TrExprS.*` lemmas go upstream |
| `ErasureRun.lean` | 3,234 | survives intact — the run algebra is independent of which relation the bridge concludes |
| `VisitExprRefines.lean` | 4,641 → ~3,000 | 7 motives mechanical, 3 environment-facing, 8 pass-facing; `BridgeInv` keeps 7 of 10 fields (`natcfg`/`fixvars`/`fixfresh` die with their rules) |
| `SubjectReduction{,Full,Iota}.lean` | 1,414 → ~700 | one `SEval.defeq` from the abstract-`P` spine schema; the β arm once, not three times |
| `EnvErasure{,Nonrec,Rec}.lean` | 1,640 → ~800 | five `Registered*` + three `RegisteredClosure*` collapse into `ErasesEnv`; the `_of_registered*` implications become its derivation from the run. `ContentlessFix`/`not_contentlessFix` survive as `fixIntro`'s guard |
| `ColdStart{Run,Shape,Induction}.lean` | 3,230 → ~1,600 | `erase_run_ok`, `visitExpr_shape_all` (hypothesis-free, panic-tolerant, supplies `NoBlock` + `LBClosed` of `LBWfPeregrine`), `RegInvShape.empty` carry; the premise plumbing goes |
| `ColdStart.lean`, `ColdStartDelta.lean` | 3,185 → ~400 | the 497-line worklog and the premise plumbing delete; the capstone composition moves to `Capstone.lean` |
| `FirstOrder.lean` | 762 → ~200 | `:103-155` re-indexed; `FirstOrderValue`/`InformativeType` as the observational domain deleted |
| `Bridge.lean` | 674 → ~250 | `Supported` rewritten (§3.8); `IsLamTelescope` kept |
| `SourceEval.lean` | 184 → ~350 | one flag-parameterised `SEval` replaces four here and four elsewhere |

### 5.3 Deleted (≈ 12,500 lines of proof + ~3,200 comment lines)

`ErasureContext.lean` (251) · `SourceEvalData.lean` (517) · `ErasesCorrectData.lean` (1,731) ·
`ErasesCorrectIota.lean` (1,075) · `ErasesCorrect.lean`'s `ErasesEnvDelta` half (~200) ·
`IotaPattern.lean` (485) · `IotaDischarge.lean` (604) · `SubjectReductionIota.lean` (458 → merged) ·
`ProjPattern.lean` (1,059) · `ProjDischarge.lean` (415) · `RecBlockErasure.lean` (811) ·
`DeltaHyps.lean` (1,499) · `CasesBridgeHyps.lean` (287) · `DataBridgeHyps.lean` (137) ·
`ProjBridgeHyps.lean` (182) · `PrepareHyps.lean` (118 → restated in 20 lines at the single `SEval`) ·
`EraseCore.lean` (643, minus the fuel lemmas `FirstOrder` reuses) ·
`FirstOrderShipping.lean` (254) · `FirstOrderShippingIota.lean` (553) ·
`ShippingCorrect.lean` (207) · `ShippingCorrectData.lean` (127) · `Export/EvalT.lean` (296) ·
`ErasesLevels.lean` (373) · `ErasesInstL.lean` (493) · `ErasesDeltaL.lean` (280) ·
`Eval.lean` (11) · `Semantics.lean` (17) · `OutputShape.lean` (155 → merged into `Output.lean`).

### 5.4 New

| Module | Contents | Est. lines |
|---|---|---|
| `Pass/Basic.lean` | `CompileTable`, `LBPass`, `Inert`, `comp`, guards scaffold | 260 |
| `Pass/CtorInline.lean` | pass + correctness + guard | 320 |
| `Pass/ElimInline.lean` | pass + correctness (via `IotaBridge`) + guard | 620 |
| `Pass/FixIntro.lean` | declaration-level pass + correctness (via `FixUnfold`) + guard | 540 |
| `Pass/Prune.lean` | dead-declaration pruning + preservation + guard | 240 |
| `Pass/Lower.lean` | `LBLower`, `LBDeliver`, commutation, composed correctness | 200 |
| `Semantics/Compute.lean` | `lbEval` + `lbEval_sound` | 420 |
| `ErasesEnv.lean` | `AxiomSpec`, `ErasesDecl`, `ErasesEnv`, `ElimBody`, `SubsingletonElim` + derivation | 900 |
| `CompilerEnv.lean` | `CompilerEnv`, its lifting lemmas along `≤` | 260 |
| `PrimSpec.lean` | `PrimSpec` (from `ResidualHyps`), `envWF`, `oracle_sound`, `table_adequate` | 340 |
| `Supported.lean` | `SupportError`, `supportedB`, `Supported`, soundness, closure lemmas | 620 |
| `Axioms.lean` | `ErasableAxioms`, `erasableAxiomsB`, soundness | 220 |
| `Output.lean` | `LBWfPeregrine`, `PeregrinePre`, derivation from `visitExpr_shape_all` | 380 |
| `Witness/SourceTable.lean` | reified fixture type + adequacy predicate | 300 |
| `Witness/Reify.lean` | `lake exe reify` — the generator (elaboration-time, not proved) | 380 |
| `Witness/EraseB.lean` | `eraseB` + `eraseB_sound` | 1,400 |
| `Witness/SrEval.lean` | `srEval` + `srEval_sound` | 900 |
| `Capstone.lean` | T9, the applied form, composition | 500 |
| `VerifyBench/Spikes/G1..G7.lean` | the ladder | 90 |
| `VerifyBench/Green.lean` | the green instance, one rung at a time | 500 |
| `test/Ledger.lean`, `test/axioms.expected` | T11 | 60 |
| `Tools/Hygiene.lean`, `Tools/Coverage.lean`, `Tools/GreenCheck.lean` | CI executables | 500 |
| `doc/Erases-vs-Fig18.md`, `doc/panic-table.md`, `doc/coverage.md`, `doc/hypotheses.md`, `doc/exceptions.md`, `doc/upstream-asks.md` | tracked docs | — |

Net: ≈ 41,200 verification lines → ≈ 26,000, of which ≈ 9,600 are new.

---

## 6. Waves

Dependencies are on **units**, not waves; units within a wave with no arrow between them run in
parallel. Every wave's acceptance test is a command.

### W1 — the green light (parallel units: 6)

**Goal.** `green_G1` elaborates: a real `#erase` run of `spikeZero`, every hypothesis inhabited,
a literal answer.

| Unit | Deliverable | Depends on |
|---|---|---|
| 1a | §3.2 flags; `Flags.lean` header; delete `defaultFlags`/`optFlags`/`appliedFlags` | — |
| 1b | `Pass/Basic.lean`; `ctorInline` + correctness + guard; `pruneEnv` + correctness; `Inert` lemmas for `elimInline`/`fixIntro`/`optimize`; `LBLower`/`LBDeliver` defined | 1a |
| 1c | `Erases.lean` rewritten (§3.3) + `doc/Erases-vs-Fig18.md`; transport arms for the nine surviving rules re-anchored | — |
| 1d | `SourceEval.lean`: `SEvalFlags`, `SEval`, `mono`; `SEval.defeq` at `δ` | 1c |
| 1e | `ErasesEnv.lean` `defn`/`ax`/`ind`/`ctor` (not `elim`); `CompilerEnv.lean`; `PrimSpec.lean`; `Supported.lean` v1; `Axioms.lean`; `Output.lean` | 1c |
| 1f | `FirstOrder.lean` re-indexed: `FirstOrderInd`, `firstOrderIndB`, T7 | 1c, 1e |
| 1g | `Witness/{SourceTable,Reify,EraseB,SrEval}` restricted to the `δ` fragment; `Semantics/Compute.lean` | 1b, 1c, 1d |
| 1h | T5 at `fl = δ` (value + δ + box arms only, ~150 lines) | 1c, 1d, 1e |
| 1i | `Capstone.lean` T9 stated in full, proved modulo a `hbridge` binder | 1b, 1e, 1f, 1h |
| 1j | `VerifyBench/Spikes/G1.lean`; `VerifyBench/Green.lean`; `test/Ledger.lean`; `Tools/GreenCheck.lean`; `Tools/Hygiene.lean` | all |

**Acceptance.** `lake build && lake exe green-check && lake exe hygiene && diff <(lake env lean
test/Ledger.lean) test/axioms.expected` — all green, where `green-check` re-runs `#erase` on G1
and byte-diffs `VerifyBench/ast/G1.ast` against the committed fixture, and `green_G1`'s conclusion
ends in the literal `.construct ⟨Nat,0⟩ 0 []`.

Also in W1, two cheap measurements that the design depends on: confirm `EEtaExpandedFix.expanded`
fails on all five `.ast` (expected; §8 F-ETA) and confirm 982/982 constructor saturation
(`etaCtors`) with the reify tool.

### W2 — β, ζ, literals, projections (parallel units: 5)

**Goal.** `green_G2`, `green_G3`, `green_G4`.

| Unit | Deliverable |
|---|---|
| 2a | `erases_subst`, `erases_shift`, `Erases.abstract`/`uninstantiate`/`thin_vlet` re-anchored |
| 2b | `SEval.defeq` at `βζδ + lit + proj`; T5 at that flag set (β arm consumes 2a, δ arm consumes `ErasesEnv`, box arm consumes `SEval.defeq`) |
| 2c | `optimize` generalised over `with_constructor_as_block` — four new arms |
| 2d | `eraseB`/`srEval` extended to β/ζ/lit/proj; `lbEval` completed |
| 2e | `Supported` closure lemmas; `doc/coverage.md` v1 generated for all five programs |

**Acceptance.** As W1, at G2/G3/G4; plus `#print axioms LBLower_correct` prints class **A**
(`[propext, Quot.sound]` only), and `doc/coverage.md` has five rows with a named `SupportError`
for Quicksort (`sparseCasesOn`).

### W3 — ι, eliminators, recursion (parallel units: 4)

**Goal.** `green_G5`, `green_G6`; T5 at `full`.

| Unit | Deliverable | Depends |
|---|---|---|
| 3a | `ErasesDecl.elim`, `ElimBody`, `SubsingletonElim` + `subsingletonElim_of_wf` modulo the upstream ask; a pats-carrying `VEnv.WF` fixture (Q2's probe scales to it: 21/22 clauses by `decide`) | W2 |
| 3b | `elimInline` + correctness via `IotaBridge` | 3a |
| 3c | `fixIntro` + correctness via `closeFix_substList_fixSubst`; `CompilerEnv` discharged for `Nat.add` | W2 |
| 3d | `SEval` ι and proj arms + `SEval.defeq` at `full`; T5 at `full` | 3a |

**Acceptance.** `green_G5`/`green_G6` elaborate; `elimInline`/`fixIntro` guards *fire*
(the `_fires` lemma exhibits a non-trivial `WcbvEval`); the ι round has an end-to-end witness,
retiring the review's `[TA-06]`/`[P1]` findings by construction.

### W4 — the bridge (parallel units: 3)

**Goal.** `hbridge` discharged; `green_G1..G6` become unconditional.

| Unit | Deliverable |
|---|---|
| 4a | `ErasureRun.lean` re-pointed (survives intact); `RunInv` (7 of `BridgeInv`'s 10 fields + `CanonicalConstants`) |
| 4b | the 18 motives restated: 7 mechanical, 3 environment-facing, 8 pass-facing; `visitExpr_refines_erases` |
| 4c | `PrimSpec` routed (criterion 9); `doc/panic-table.md`; `Erases.sort_erasable`/`forallE_erasable`; the four `Lean4Lean`-namespace declarations packaged as upstream asks |

**Acceptance.** `green_G*` no longer take `hbridge`; `#print axioms shipping_erase_correct` matches
the extended fixture (33 axioms, the `bv_decide` pair classified); `lake exe hygiene` reports zero
declarations outside the closure except `doc/exceptions.md`'s list.

### W5 — Arith, coverage, delivery (parallel units: 3)

| Unit | Deliverable |
|---|---|
| 5a | `green_G7` (`arithClosed`) — the full typeclass tower, 27 constants, `srEval`/`lbEval` doing the 2^3 computation by `rfl` |
| 5b | `green_G8` (`benchArith`) via the applied capstone; `doc/coverage.md` final for all five |
| 5c | CI on the verification branch; `lakefile.toml` pinned at the measured rev; `VerifyBench/STATUS.md` retired into `doc/coverage.md`; the three prose ledgers deleted |

**Acceptance.** Criteria 13, 14, 22; `lake exe green-check` runs all eight rungs.

### W6 — optional hardening (parallel units: 4)

* `fixEta` pass, so the verification can conclude `PeregrinePre` (§8 F-ETA) without editing
  shipping code; the delivered bytes stay whatever the tool emits, and the theorem says what would
  be needed.
* Q2 full: `iota_sing_idx` + two-class field treatment, lifting N17 (`Acc.rec`).
* Q1 strongest form: `eraseB_matches_run` — `eraseB tbl (prepare e) = .ok (Σ,t)` and a successful
  run agree, giving `[S §7.4]`'s "same result" reading.
* Q8: `WcbvEval ↔ EWcbvEval` rule correspondence in `rocq/`.

---

## 7. Risk register

| # | Risk | Likelihood | Mitigation |
|---|---|---|---|
| R1 | **`eraseB` + `srEval` + `lbEval` are ~2,700 new lines that no wave strictly *needs*.** | medium | They are the schedule's insurance, not decoration: without them the green instance stops at hand-derivable rungs (G1–G4) and `arithClosed`'s 2^3 becomes a 400-step hand derivation. Wave 1 builds only the `δ` slice (~400 lines); if W2 shows the soundness proofs blowing up, the fallback is to keep them for the *target* side only (`lbEval`, class A, cheap and unconditional) and take `SEval` as N7's hypothesis at G7/G8 with a ledger row |
| R2 | **`VEnv.WF'.consts_origin` (Q2's upstream ask) does not land.** | medium | `SubsingletonElim` becomes a single named class-**C** hypothesis with a ledger row, which criterion 7 explicitly permits. `Eq.rec`/`And.rec`/`Decidable` stay inside the fragment either way; only the *derivation* is deferred. W3 is not blocked — 3a states the predicate and proves everything downstream of it |
| R3 | **The 18-motive restatement (W4) overruns.** | medium-high | It is the single largest item (4,641 lines, realistic reuse 55–65%). Mitigation is structural: waves 1–3 deliver a green instance *without* it, so an overrun delays unconditionality, not the demonstration that the specification is inhabited and correct. Split 4b by motive class (7 / 3 / 8) across three agents |
| R4 | **`elimInline` exactness fails on a binder name.** | low | Measured: the only non-reconstructible datum is an η-contracted minor's binder name, already outside the fragment (`Supported.etaContractedMinor`). If it appears at G7, the conclusion weakens for that program to equality-up-to-binder-names, which `WcbvEval` does not observe — a one-line lemma `WcbvEval_binderName_irrel` covers it |
| R5 | **The reified fixture drifts from the live environment.** | medium | `lake exe reify` regenerates and CI byte-diffs; the fixture's adequacy is a `PrimSpec` obligation, so drift is a *failed check*, never a silent unsoundness. The same mechanism catches a Lean toolchain bump changing `Nat.add`'s compiler body |
| R6 | **`hrun` is never discharged inside Lean** (waves 1–3), so "green" overstates. | certain, by design | Said in the statement (`hrun` is a binder), in `doc/coverage.md`, and in the ledger; the prediction check is an external, byte-level, CI-run measurement, and W4 removes it. The design never claims a checked run |
| R7 | **`PrimSpec.env_connect` is class D and is the largest single assumption.** | certain | It is lean4lean's own boundary (`VEnvs.WF`), it is exactly what the `lean4lean` executable establishes by re-checking the environment, and it *buys* `env.WF` rather than assuming it — a trust reduction relative to the current tree, which assumes `env.WF`/`env.Ordered` directly. One ledger row, one sentence |
| R8 | **Routing the oracle in (criterion 9) enlarges the axiom set 8 → 33, including two `_native.bv_decide` axioms.** | certain | Ledger row (b) with all 29 names; criterion 15's fixture accommodates it; the alternative (leave `oracle_sound` at class D) forfeits the one trust reduction and is rejected explicitly |
| R9 | **F-ETA (fixpoint η) turns out to matter for a *shipping* consumer.** | medium | It already does — peregrine's precondition is unmet and `Admitted`. §8 raises it with the repair sketched; W6's `fixEta` lets the verification state `PeregrinePre` without touching shipping code |
| R10 | **Quicksort stays uncovered** (`_sparseCasesOn_` miscompile). | certain | `Supported.sparseCasesOn` makes it visible in the predicate a reader audits (criterion 11), `doc/coverage.md` names it, and the finding stays RAISED-not-fixed per the repository's standing rule |
| R11 | **Scope creep back into `Erases`.** | medium | Criterion 2's CI grep (no `.construct`/`.case`/`.fix` in the inductive block) is mechanical and fails the build |

---

## 8. Transpiler edits required

**None.** No wave of this design edits `Erasure.lean`, `Basic.lean` or `Printing.lean`. The
shipping-side edits already on `dev/verify` (P1–P7: the `partial_fixpoint` restructure, the nine
monotonicity lemmas, `expr_withApp_eq`, `visitCasesEta`/`visitCtorEta`, the `.toArray`, `Basic`'s
de-partialization, the `Relevance` import) are **preconditions** of T8 and are carried, not
extended. B1 (the `isErasable` kernel reroute) is **kept**, because reverting it demotes
`PrimSpec.oracle_sound` from class B to class D and makes criterion 9 unsatisfiable; its measured
under-erasure (review `SI-1`) is owned inside `Supported`, not papered over.

Three findings are **raised** for a separate `dev/fix` branch, none of which this design depends on:

* **F-ETA — fixpoint η-expansion is missing, and peregrine's precondition is therefore unmet.**
  `untyped_transform_pipeline`'s first pass requires `EEtaExpandedFix.expanded_eprogram`
  (peregrine `theories/erasure/Transforms.v:147`, MetaRocq `ErasurePlugin/ETransform.v:710-716`),
  whose `tFix` rule (`Erasure/EEtaExpandedFix.v:47-53`) needs `args ≠ []` and `#|args| > rarg`.
  Every recursive Lean declaration emits a bare unapplied `tFix` as its constant body
  (`Arith.ast`'s `Nat.add`), so the condition fails on all five programs. Coq avoids it by
  η-expanding before erasure (`Template/EtaExpand`); the eraser's own TODO at `Erasure.lean:911`
  anticipates this. *Repair (one function):* in `visitMutual`'s recursive branch, wrap the emitted
  `.fix defs i` body in `rarg+1` lambdas applied to their own binders. *Justification for not doing
  it here:* it changes emitted bytes, and the repository's standing rule is to raise, not patch.
  Peregrine's own discharge of the obligation is `Admitted` (`Transforms.v:375`), so nothing
  currently detects it — which is exactly why it needs raising rather than absorbing.
* **F-SPARSE — `visitCases` panics on sparse `casesOn` and emits a wrong program.** Pre-existing,
  already registered in `VerifyBench/STATUS.md`; this design makes it visible in `Supported` and
  in the generated coverage table rather than hiding it in a trust bundle.
* **F-EQREC — recursors reach the eraser as body-less axioms.** `Eq.rec` in `Fannkuch.ast` is
  `(ConstantDecl (constant_body None))`; the realizer is assumed to arrive through peregrine's
  `.attr` channel, which the frontend does not emit. Covered here by an `AxiomSpec` row at class
  **D**; raised so someone decides whether the frontend should emit the remapping.

Two **upstream asks to lean4lean** (N15), neither an edit to this repository's shipping code:
`VEnv.WF'.consts_origin` + `iotaRHS'_Generic` (Q2's derivation), and the four kernel-generic
declarations currently sitting in `CheckerAdequacy.lean` (criterion 21). Both are tracked in
`doc/upstream-asks.md`, one row each, with the `file:line` of the existing twin.

---

## 9. Documentation policy compliance

* **One fact, one home.** Every claim about upstream state lives once, in `test/Ledger.lean`'s
  output and `doc/upstream-asks.md`, measured at the pin by a CI job. The nine "a pats-carrying
  `VEnv.WF` is unconstructible" docstrings are deleted — Q2's probe builds one — as are the seven
  "no `addPat` clause" sites, the eight "`addInduct_WF` is `sorry`" sites, the five stale oracle
  descriptions, `Flags.lean:19-24`, and the `ProjDischarge`/`ProjPattern` contradiction.
* **Current fact only.** No "used to", no commit hash, no date, no slice tag, no memory reference,
  no untracked-handoff citation. `lake exe hygiene` greps for all of them and fails the build.
  The 497-line worklog at the head of `ColdStart.lean` goes to git history.
* **Length budget.** ≤ 8 lines per field/lemma docstring, ≤ 40 per module header; the 76-line
  docstring on a 4-line definition (`ErasesUniform:122`) and the 363-line `DeltaHyps` header go
  with their files.
* **Every backticked identifier resolves; every cited document exists.** `lake exe hygiene`
  elaborates each backticked name against the environment and stats each cited path.
  `closeFix_fvar`, `isProp_refines_Erasable`, the two memory references and the two
  `PROJECT_STATUS_HANDOFF.md` citations (one from shipping code) are removed.
* **No dead code.** The import closure of `Green.lean` + `test/Ledger.lean` is computed by CI and
  diffed against `doc/exceptions.md`, whose only entries are the witness generator (with its
  reason: it supplies the coverage table and the differential cross-check) and `blockFlags`
  (with its reason: it names peregrine's own pass's output).
* **No forked relations.** One `SEval`, one `ErasesEnv`, one `PrimSpec`, one ledger; growth is by
  parameterisation (`SEvalFlags`, `WcbvFlags`, `CompileTable`), which is also the widening axis of
  §6. CI greps for a second `inductive SEval` or a `*BridgeHyps`.
* **Non-vacuity guards everywhere.** Every relation and every pass ships a concrete inhabitant
  witnessing satisfiable hypotheses and a non-trivial conclusion — the existing triple at
  `Optimize.lean:1066-1083` is the template, and `Green.lean` is the same discipline applied to the
  capstone.
* **No `native_decide`**, no unexplained `set_option`, no `@[simp]` on foreign namespaces. The
  tree is already clean here; `lake exe hygiene` keeps it so. Note that `by rfl` on `srEval`/
  `lbEval` at G7 will need `set_option maxRecDepth`, with a comment saying why.
* **Docstrings say why a hypothesis is not slack.** `IotaBridge.lean:96-111`,
  `Semantics/Values.lean:79` and `Semantics/Eval.lean:29` are the models; every class-C hypothesis
  in `doc/hypotheses.md` carries its counterexample or its measurement.
