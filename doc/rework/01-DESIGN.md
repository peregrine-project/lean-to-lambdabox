# 01 — Final design for the Lean → λ□ verification rework

**Status.** Design of record. It is the synthesis of the three candidate designs
(`doc/rework/designs/{A,B,C}-*.md`) after adversarial review by three judges, and it is
subordinate to `doc/rework/00-REFERENCE-SPEC.md` except where §3.3 below asks that document to be
amended. Every amendment is forced by a measurement, and the measurement is cited.

**Base and grafts.** The skeleton is **design B** (relational λ□→λ□ passes, maximum reuse): two
judges ranked it first, and it is the only one of the three whose `erases_correct` is well-posed
at a recursive constant. Grafted, per the judges' endorsements: from **A** the flag chain, the
eliminator bodies as *constructions* with their ι theorems proved rather than assumed, the
declaration-level `elim` class, `EnvAgree`, the panic table and the upstream-ask file; from **C**
the entire non-vacuity lane (the G-ladder, `Green.lean`, `green-check`), the honest output
predicate (`LBWfPeregrine` without fixpoint η, `PeregrinePre` stated separately), `supportedB :
… → Except SupportError Unit`, the reified `SourceTable`, `lbEval`, and the applied capstone.

**Repairs this document makes that no candidate design contained.** Six, listed in §2; two of them
are machine-checked here (`scratchpad/probe/lowerfix2.lean`, `scratchpad/probe/fixval.lean`).

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
**derived introduction lemmas whose signatures are the deleted `Erases` rules**, so the 4,641-line
18-motive induction is restated by a rename rather than rewritten.

One `VEnv` is threaded: `envC`, the environment the *compiler* compiles (`env` extended by one
`VEnv.addDefEq` per `_unsafe_rec` body). The kernel `env` survives only inside `PrimSpec` and
`CompilerEnv`.

### 1.2 Why relations, in one paragraph

`[L Def. 10]`'s `◄` is a relation and `[S §7.2]`'s posture is graph ⊆ relation, so a theorem of
the form "the run's output is in the composite" is the papers' own theorem shape. It is also the
only shape in which the Lean-specific content can be *stated*: a recursive Lean constant has a
λ-headed source body and a `.fix`-headed λ□ body, both of which are `WcbvEval` **values**
(`Semantics/Values.lean:36`; probe `scratchpad/probe/fixval.lean`), so the correspondence between
them is irreducibly a relation between a λ and a `.fix` — not a function equality (design C's
`fixIntro.correct` is false), and not a congruence over `Lean.Expr` (design A's T5 is false at
`Arith`). Finally, a relation between two λ□ terms *cannot mention* `Expr`, `VEnv`, `Erasable` or
the run even by accident, so a premise added to make a case go through is refutable by a two-term
counterexample. That is the structural answer to the review's central finding (the specification
was written to match the implementation).

### 1.3 Layers, files, trust

| Layer | Objects | lean4lean? | Class |
|---|---|---|---|
| **L0** target | `LBTerm`, `WcbvEval`, flags, values, substitution, `Closed`, `IotaBridge`, `FixUnfold`, `lbEval` | no | **A** |
| **L1** specification | `Erases`, `ErasesDecl`/`ErasesEnv`, `Erasable`, `SEval`, `SubsingletonElim`, `FirstOrderInd`, T5, T7 | yes | **B** |
| **L4** passes | `Lower`, `LowerFix`, `LowerEnv`, `ElimBody`, `optimize` | no | **A** |
| **L2** bridge | `PrimSpec`, `Supported`, run algebra, 18 motives, T8 | yes | **B** + **D** |
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
`eraseFlags = ⟨true, true, false⟩` — which is *exactly* MetaRocq's `EWcbvEval.default_wcbv_flags`
(`EWcbvEval.v:69`) and *exactly* what peregrine's `untyped_transform_pipeline` declares as its
input evaluation (`peregrine-tool/theories/erasure/Transforms.v:151`). The deliverable therefore
stops at the emitted program, at the flag point the consumer names.

---

## 2. Fatal flaws named by the judges, and their resolution

Every flaw any judge called fatal or near-fatal, with what this design does about it. Nothing is
left "not fatal because" without a reason.

| # | Flaw (judge) | Applies to | Resolution here |
|---|---|---|---|
| **F1** | `.fix` value mismatch: A's T5 refutable, C's `fixIntro.correct` false, **B's `lower_correct` false as written** (all three judges) | all three | **Repaired.** `Lower` gains two arms, `fixConst` and `fixBody` (§4.5), and the transport lemma `Lower.constToFix`. Probe-checked to elaborate and to yield a usable recursor (`scratchpad/probe/lowerfix2.lean`). This is where today's `Erases.const_fix` content belongs; its docstring's claim ("no arrangement of `fix`'s premises avoids needing it", `Erases.lean:618-624`) is true of the *relation*, and the relation is now `Lower`, not `Erases`. Retired in **W1**, not W4. |
| **F2** | `LBWfPeregrine.etaFix` is false on every emitted program (judges 1, 2; C alone got it right) | A, B | **Repaired.** `LBWfPeregrine` does not claim `EEtaExpandedFix.expanded_eprogram`; `PeregrinePre := LBWfPeregrine ∧ LBExpandedFix` is stated separately and is *not* concluded. Finding **F-ETA** raised (§8.2), one ledger row. Measured: `Arith.ast` has 4 bare `(constant_body (Some (tFix`, and `EEtaExpandedFix`'s only `tFix` rule needs `args ≠ []` and `#args > rarg`. |
| **F3** | The capstone's observable conjunct uses the wrong relation: `Erases v tv` yields a `.const`-headed spine, the emitted `Σ` evaluates to a `.construct` spine (judge 2, M2) | A, B, C | **Repaired.** T9's observable conjunct is stated with the composite: `∃ tv₀ tv, Erases envC [] [] v tv₀ ∧ Lower Σ⁺ tv₀ tv ∧ NoBox tv ∧ WcbvEval Σ eraseFlags … tv`, and T7 becomes uniqueness-of-`Erases` **plus** determinism-of-`Lower` on first-order data (§5, T7/T9). |
| **F4** | `by decide` on a `Lean.Environment` predicate is impossible; `native_decide` is banned; criteria 8/11/13 unreachable (judges 2, 3; probe `dec.lean`) | A, B | **Repaired.** Every decidable check runs on a **reified, committed `SourceTable`** produced by `lake exe reify` and byte-diffed in CI; discharges are `by rfl` on the table, and adequacy (`SourceTableAdequate`) is a `PrimSpec` field. `ErasableAxioms` stays on the *emitted* `(Σ,t)`, where `decide` genuinely works. |
| **F5** | `benchArith : Nat → Nat`, so T10's `hty : … (.const ``Nat [])` cannot be instantiated (judge 3, C alone noticed) | A, B | **Repaired.** The capstone's observable conjunct is quantified over closed first-order argument spines (§5, T9); `args = []` is the spec's T9 verbatim, `args = [0]` is `benchArith`. The ladder additionally carries the closed rung `arithClosed := benchArith 0`. |
| **F6** | `Lower` has no arm for the eraser's η-expansion of under-applied ctor/`casesOn` heads, so T8 is unprovable on Arith (judges 2 M6, 3 F3) | B | **Repaired.** Two η arms, `ctorEta` and `elimEta` (§4.4), matching `visitCtorEtaGo`/`visitCasesEtaGo` (`Erasure.lean:705-728`) exactly: fresh binders are pushed into the spine and the λ□ result is wrapped in `mkLambdas`. |
| **F7** | A's per-motive `∃ E` does not compose across sibling sub-runs (judges 2 M4, 3 F6) | A | **Avoided by construction.** `Σ⁺` is *universally* quantified in every motive under `SpecEnv`, which is antitone in the run state; `SpecEnv.mono` is proved from the existing `StateLe` (`ErasureRun.lean:1585`) that every motive already concludes. |
| **F8** | C's `LBPass.correct` quantifies over all `CompileTable`s with nothing tying the table to `Σ`; two sources of truth (judge 3, F2) | C | **Avoided.** There is no `CompileTable`. The passes read `Σ⁺` — the same object that justifies them. |
| **F9** | `Erases.bvar`/`.fvar` drop the `Δ.find?` premise `TrExprS` carries (judges 1, 2, 3) | B | **Repaired.** Restored (§4.2). |
| **F10** | T5 written at `env` while the capstone evaluates at `envC` (judge 1) | B | **Repaired.** One `VEnv` index, `envC`, everywhere in L1/L4; `env` appears only in `PrimSpec.env_connect` and `CompilerEnv env envC`. `Erasable.mono`, `TrExprS.mono` (`Verify/Typing/Lemmas.lean:781`) and `HasType.mono` (`Theory/Typing/Lemmas.lean:414`) do the lifting. |
| **F11** | `LBPassR.correct` has free variables in a structure field (judge 2, M10) | B | **Repaired.** Explicit `∀` binders (§4.10 note). |
| **F12** | `ProjParams` reverse-engineers a parameter count out of an ι-rule key (judges 2, 3) | A | **Avoided.** `IndInfo` reads the block data off `VEnv.WF`'s declaration list; `Erases.proj` keys on it. |
| **F13** | `SelfRefers`/`name_occurs` as a specification premise mirrors the implementation (judges 1, 3) | A | **Avoided.** `LowerFix` tolerates an unused fix binder; no source-side occurrence premise exists anywhere. |
| **F14** | A single monolithic 18-motive wave reproduces the failure that made the current tree (judges 1, 2) | B | **Repaired.** W4 splits the motives into three batches (3 environment-facing **first**, 7 mechanical, 8 pass-facing), each a unit on disjoint files. |
| **F15** | C's `eraseB`/`srEval` are ~2,700 lines no theorem needs, and `eraseB` is a larger `EraseCore.lean` (judges 1, 2, 3) | C | **Not adopted.** `lbEval` (class **A**, ~420 lines, unconditional) is adopted because it turns the target-side evaluation of every green rung into `by rfl` and cross-checks `peregrine eval`. `srEval` is **W6-optional** and scoped per flag slice; `eraseB` is **not built** — the `Erases`/`Lower` witnesses the ladder needs are produced by the derived introduction lemmas plus the reified table. |
| **F16** | Criterion 21 (no `Lean4Lean`-namespace declarations) vs `CheckerAdequacy.lean`'s eight (all three) | all | **Met without an exception clause.** Seven are kernel-generic and go upstream (`doc/upstream-asks.md`); `kernel_isErasable_sound` mentions `LeanToLambdaBox.isErasable` and is renamed `LeanToLambdaBox.Oracle.kernel_isErasable_sound`. |
| **F17** | `hwt : TrExprS envC [] [] e ve` and `hty` must be *inhabited* for a 39-declaration program or criterion 13 is theatre (judge 3, shared blind spot) | all | **Scheduled**, W3 unit `TrWitness`: read `TrExprS` off a successful run of lean4lean's checker (`CheckerAdequacy.lean:94,112`, `M.WF.run'`, `VState.WF.initial`). **Named fallback:** if that does not land, `hwt`/`hty` stay class-**D** binders beside `PrimSpec`, and criterion 13's wording is amended in the same commit that records the fallback — never silently. |
| **F18** | `hrun` can never be discharged inside Lean (`Void IO.RealWorld` is opaque) (judge 3) | A, B | **Stated, not hidden.** `hrun` is a permanent binder; it is named as such in the capstone's docstring, in the ledger (class **D**), and in `doc/coverage.md`, and it is mechanised externally by `lake exe green-check` (re-run `#erase`, byte-diff the committed `.ast`). |
| **F19** | `by rfl` on a 19-node peano tower through 27 constants may exceed kernel budgets (judge 1) | C | **Priced.** `lbEval` is fuel-indexed and structurally recursive; G7's evaluation is done by `lbEval` + `lbEval_sound`, not by `WcbvEval` derivation building. Risk **R9** with the fallback (evaluate `arithClosed` at a smaller exponent rung, recorded in the coverage table). |
| **F20** | B lists criterion 5 as "met" while replacing `LBPass` with a relational `LBPassR` (judge 3) | B | **Filed as amendment A8** (§3.3), not silently. |

---

## 3. Decisions

### 3.1 The eight open questions

**Q1 — does the pass layer reproduce `visitExpr` exactly?** **No; state membership in the
composite.** T8 concludes `∃ t₀, Erases envC Us Δ (prepare_erasure e) t₀ ∧ Lower Σ⁺ t₀ t`. Exact
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

**Q2 — where is Lean's subsingleton criterion derived?** **Derived from `envC.WF`, first cut
excludes the index-determined case.** `SubsingletonElim envC I` (§4.6) comes from
`VInductDecl.LargeElim` (`Theory/Inductive.lean:226`) **minus** the `FieldInIndices` disjunct; the
one missing link, `VEnv.WF'.consts_origin` (the constants-keyed twin of `WF'.pats_origin`,
`InductiveParams.lean:93`), is kernel-generic and goes upstream by N15. Until it lands,
`SubsingletonElim` is one named class-**C** hypothesis with one ledger row, which criterion 7
permits. `Eq.rec`, `And.rec`, `Iff.rec`, `False.rec` and `Decidable`'s elimination are inside the
fragment, each exhibited by a checked `ElimBody` instance; `Acc.rec`/`WellFounded.fix` go to
restriction **N17** plus a raised finding (measured: `largeElimClause ``Acc = some (2,[1])`, so
`Acc.intro`'s field `x : α` is index-determined *data* and MetaRocq's `eval_iota_sing`, which
boxes every branch binder, computes a wrong program). Lean's own code generator refuses `Acc.rec`,
so nothing shipping is lost.

**Q3 — `_unsafe_rec`: hypothesis or restriction?** **Hypothesis, as a one-`VEnv` extension.**
`envC = env + one VEnv.addDefEq per compiler body in the run's closure`
(`Theory/VEnv.lean:37`: `addDefEq` touches only `defeqs`, never `constants`), carried by the
class-**C** binder `hcomp : CompilerEnv env envC lenv e`, decidable per program (measured 33/33
compiler bodies kernel-typeable at the declared type). Everything in L1/L4 is stated at `envC`.
The restriction alternative is **deleted** from the spec: it covers 0 of 5 benchmarks
(`Nat.add/mul/sub/pow` are all `_unsafe_rec`, so `Arith` — T10's minimum — covers zero). One
class-**E** ledger row records that the two bodies agree only propositionally, and not at all for
`partial def`.

**Q4 — do the emitted eliminator declarations blow up the deliverable?** **No.** The runtime
library lives in `Σ⁺`, which never reaches disk; `LowerEnv` carries the pruning clause and
`Σ = s'.gdecls` is the pruned image. Measured +4.5%…+13.6% un-pruned, **0% pruned**. Size is an
N14 ledger row with the measured `.peano`/hygienic-name split, not a disclaimer.

**Q5 — parameters in constructor applications.** **The frontend keeps them; peregrine drops
them** (`remove_params_optimization`, pass 2 of `verified_lambdabox_pipeline`, at
`with_constructor_as_block = false`). `ErasesDecl.ctor`'s body is `.construct iid k []` and
parameters arrive through `Erases.app` (boxed, being types). Measured 982/982 constructor
occurrences at exactly `ind_npars + cstr_nargs`, 0 under-applied. `LBWfPeregrine.etaCtors` states
that invariant; `etaFix` does **not** appear (§2 F2).

**Q6 — is `FirstOrderInd` `[L Def. 14]` / `[L Def. 6]` / `[S §7.3]`?** `fields` ≡ Def. 14; Def. 6
is `firstorder_no_box`'s *conclusion*, not a definition (the fidelity table's shared row is
split); `[S §7.3]`'s `firstorder_ind` is cited as origin and **not transcribed**, because its sort
conjunct makes it `false` on `nat` (reproduced three ways by `vm_compute`; raised upstream).
`FirstOrderInd` is typed over `VEnv.WF`'s declaration list — `VEnv` stores no inductive
declarations (`Theory/VEnv.lean:17-23`), so the spec's signature is unwritable — and the decidable
checker runs on the reified table. Criterion 8 is narrowed to `Nat`, `Bool`, `Tree`.

**Q7 — `Quot`.** **Restrict (N16).** No `Quot`/`Quot.mk`/`Quot.lift`/`Quot.ind` in a
computationally relevant position, as a `Supported` conjunct over the dependency closure.
`Quot.sound` is *not* excluded (it is `Prop`-typed, hence boxed, hence covered by
`ErasableAxioms`). `ErasesDecl.quot` is **deleted**: it promised an `ElimBody` obligation nothing
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

### 3.2 The flag chain — the one place the design *removes* work

Measured, by two judges independently:

```
eraseFlags := ⟨with_prop_case := true, with_guarded_fix := true, with_constructor_as_block := false⟩
            = MetaRocq  EWcbvEval.default_wcbv_flags                     (EWcbvEval.v:69)
            = peregrine untyped_transform_pipeline's INPUT evaluation    (Transforms.v:151)
```

So the frontend's obligation stops at `eraseFlags`, and `with_prop_case` is discharged downstream
by peregrine's own verified `remove_match_on_box` pass. Consequences:

* the capstone concludes about **the emitted program `(Σ, t)`** — the artefact — not about
  `LBOptimize Σ t`, which nobody ships;
* `optimize` leaves the critical path. `Optimize.lean` is still wired into the import closure (no
  dead code) as the **template** every pass follows and as an optional corollary at
  `optFlags = ⟨false, true, false⟩`; the four block-form arms it would need
  (`construct_atom`, `construct_app`, `iota`, `proj`) are W6, not W2.

Definitions replacing the four current constants (whose header asserts the opposite of the
design):

```lean
def eraseFlags  : WcbvFlags := ⟨true,  true,  false⟩   -- deliverable point; = default_wcbv_flags
def optFlags    : WcbvFlags := ⟨false, true,  false⟩   -- = MetaRocq opt_wcbv_flags; W6 corollary
def blockFlags  : WcbvFlags := ⟨false, true,  true⟩    -- today's `targetFlags`, renamed; unused
```

### 3.3 Amendments requested of `00-REFERENCE-SPEC.md`

| # | Spec text | Amendment | Forced by |
|---|---|---|---|
| A1 | §2 T3 lines 213-221 ("verbatim `[L §3.3]` … `Acc.rec` … **inside** the fragment") | Lean's criterion admits index-determined data fields; `Acc.rec` is **outside** the first cut (N17); `Eq.rec`/`And.rec`/`Iff.rec`/`False.rec`/`Decidable` are inside | `largeElimClause ``Acc = some (2,[1])` |
| A2 | §7 criterion 7's example list | replace `Acc.rec` by `Eq.rec`/`And.rec`/`Iff.rec`/`Decidable` | same |
| A3 | §2 T8's conclusion `t = LBCompile.term s'.gdecls t₀` | `∃ Σ⁺ t₀, Erases … t₀ ∧ Lower Σ⁺ t₀ t`, with `ErasesEnv envC Σ⁺ t₀` and `LowerEnv Σ⁺ s'.gdecls` | 0 ctor/`casesOn`/rec declarations in all five `.ast`; `elimInline` would have nothing to δ-expand |
| A4 | §2 T3 `ErasesDecl.defn`'s premise `env.constants c = some ⟨_, some body⟩` | `VConstant` carries no body at the pin; read the defining equation from `envC.defeqs` | `Theory/VEnv.lean:6-21` |
| A5 | §5 N8's "or a restriction to declarations where the two coincide" | delete the restriction alternative | covers 0/5 |
| A6 | §7 criterion 8's list (`List Nat`, `Nat × Nat`) | `Nat`, `Bool`, `Tree` | `List`/`Prod` are outside Def. 14 and outside `firstorder_ind`; all five benchmarks return `Nat` |
| A7 | §7 criterion 12 ("matching what `peregrine validate` checks") | "matching `untyped_transform_pipeline`'s precondition **minus** fixpoint η, which is stated separately as `PeregrinePre` and **not** concluded" | `ETransform.v:710-716`; `EEtaExpandedFix.v:47-53`; 4 bare `tFix` bodies in `Arith.ast`; peregrine's own discharge is `Admitted` (`Transforms.v:375`) |
| A8 | §2 T6's `LBPass` (functional) and criterion 5 | passes are relations (`LBPassR`); `correct` keeps `optimize_correct`'s shape with the value existentially quantified | §2 F1 |
| A9 | §2 T6's `LBCompile := optimize ∘ fixIntro ∘ elimInline ∘ ctorInline`, used as both T8's factor and T9's tail | split: `Lower` is T8's factor; `optimize` is an optional post-pass. Removes an unstated idempotence obligation, and `fixIntro` disappears (it has no true `correct`) | §2 F1, §3.2 |
| A10 | §5 N-list | add **N16** (`Quot`), **N17** (subsingleton inductives with an index-determined field) | Q7, Q2 |
| A11 | §2 T8's four `PrimSpec` fields | six: add `ind_adequate` and `table_adequate` | Q6; §2 F4 |
| A12 | §2 T9's observable conjunct | value side is the **composite**, not `Erases`; and the conjunct is quantified over closed first-order argument spines | §2 F3, F5 |
| A13 | §2 T1's "the `optimize` pass (T6) discharges `with_prop_case`, landing the deliverable at `⟨false,true,false⟩`" | the deliverable lands at `eraseFlags`; `optimize` is optional | §3.2 |

### 3.4 Acceptance criteria — how each is met

1-2 (ten rules, no `.construct`/`.case`/`.fix`): §4.2 verbatim; `ErasureContext.lean` is deleted,
so the grep is empty by construction. CI grep over `Erases.lean` for `\.construct|\.case|\.fix`.
3 (rule table): `doc/rules-Erases.md`, plus `doc/rules-Lower.md`. 4 (one `SEval`, one environment
relation, one bundle, one ledger): §4.3, §4.8, §4.10, §4.14 + CI greps. 5 (pass shape + guards +
composition): §4.4-§4.7, §5 T6, as amended by A8. 6 (T5's five hypotheses): §5 T5 literally.
7 (Subsingleton once, derived or one class-**C** row): §4.6. 8 (`FirstOrderInd` decidable):
§4.12 on the reified table, `by rfl`, as amended by A6. 9 (`OracleDischarge` in the closure,
`oracle_sound` discharged): §4.10. 10 (`sort_erasable`/`forallE_erasable` + the panic table):
§4.2, `doc/panics.md`. 11 (`Supported` decidable, sparse-`casesOn` visible): §4.11, and
`supportedB` *names* the hole. 12 (`LBWfPeregrine` in the conclusion): §4.9, as amended by A7.
13-14 (non-vacuity, coverage table): §6 and `02-PLAN.md`'s per-wave green obligation.
15-17 (ledger, `sorryAx` roots, no `sorry`/`axiom`): §4.14. 18-21 (hygiene, no `Lean4Lean`
namespace): §9. 22 (delivery): W5.

---

## 4. Core definitions — exact signatures

Written against lean4lean rev `20ec229` and `LeanToLambdaBox/Basic.lean` at `dev/verify`.
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

### 4.1 Flags — `Semantics/Flags.lean`

As §3.2. The module header is rewritten to state the current fact (it currently asserts block
form, which is the opposite of what every capstone runs).

### 4.2 `Erases` — T2, ten rules — `Erases.lean`

```lean
/-- `[S Fig. 18]` transposed to `Lean.Expr`: lean4lean's `TrExprS` with the target `VExpr`
replaced by `LBTerm`, `sort`/`forallE` absorbed into `box`, and `box` added. Ten rules, no side
condition, no registry. -/
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

Four notes, each answering a judge. (i) `bvar`/`fvar` keep the `Δ.find?` premise (F9); the
transport lemmas' arms use it and without it the relation admits out-of-scope indices, which
would break `erases_subst`, `LBClosed` and T7. (ii) `const` takes no `Kername` parameter and no
registry premise: `toKername` (`Basic.lean:34`) is a *function*, which lets `BridgeInv.knames`
and `.consts` collapse into the existing `CanonicalConstants` (`ErasureRun.lean:1482`).
(iii) `proj` keys on `IndInfo` (§4.6) — the environment predicate — and deliberately carries no
`TrExprS` premise, because `TrProj.uniq` yields `IsDefEqU`, not equality. (iv) `lam`/`letE` record
the **source** name: the ASCII-graphic filter in `fvar_to_name` (`Erasure.lean:245-252`, "otherwise
the λbox parser will complain") is a printer constraint, and it reappears as
`LBWfPeregrine.asciiNames`, not inside the specification.

Carried metatheory (statements unchanged except for dropping the `Γ` index): `erases_shift`,
`erases_subst`, `Erases.abstract`, `Erases.uninstantiateN`, `Erases.thin_vlet`, `erases_weakFV*`,
`erases_uniform_*`. Nine of fifteen arms survive per lemma; six die with their rules.

New, and load-bearing (criterion 10 earns its place here: the composite's `cases` rule must erase
the arguments the `.case` node drops):

```lean
theorem Erases.exists_of_trExprS (henv : env.WF) {Δ e ve} (hΔ : VLCtx.WF env Us.length Δ)
    (h : TrExprS env Us Δ e ve) : ∃ t, Erases env Us Δ e t
theorem Erases.sort_erasable    (henv : env.WF) : TrExprS env Us Δ (.sort u) ve →
    Erasable env Us.length Δ.toCtx ve
theorem Erases.forallE_erasable (henv : env.WF) : TrExprS env Us Δ (.forallE n A B bi) ve →
    Erasable env Us.length Δ.toCtx ve
theorem Erases.mono (h : env ≤ env') : Erases env Us Δ e t → Erases env' Us Δ e t
```

### 4.3 `SEval`, `SEvalFlags`, `CompilerEnv` — T4 — `SourceEval.lean`, `CompilerEnv.lean`

```lean
structure SEvalFlags where beta, delta, zeta, iota, proj, lit : Bool
  deriving DecidableEq
instance : LE SEvalFlags := ⟨fun a b => (a.beta → b.beta) ∧ … ∧ (a.lit → b.lit)⟩
def deltaOnly : SEvalFlags := ⟨false, true, false, false, false, false⟩
def fullFlags : SEvalFlags := ⟨true, true, true, true, true, true⟩

/-- The one source evaluation: weak call-by-value big-step over `Lean.Expr`, parameterised by
which reductions are enabled `[S §5.6]`. δ reads `env.defeqs`; ι reads `env.pats`. -/
inductive SEval (env : VEnv) (Us : List Name) (fl : SEvalFlags) : VLCtx → Expr → Expr → Prop

theorem SEval.mono  (h : fl ≤ fl') : SEval env Us fl Δ e v → SEval env Us fl' Δ e v
theorem SEval.le    (h : env ≤ env') : SEval env Us fl Δ e v → SEval env' Us fl Δ e v
theorem SEval.defeq (henv : env.WF) (hΔ : VLCtx.WF env Us.length Δ)
    (htr : TrExprS env Us Δ e ve) (hev : SEval env Us fl Δ e v) :
    ∃ vv, TrExprS env Us Δ v vv ∧ env.IsDefEqU Us.length Δ.toCtx ve vv
```

`SEvalFlags` is the **widening axis of the schedule** (design C's device, adopted): T5 is proved
first at `deltaOnly`, then at `βζδ + lit + proj`, then at `fullFlags`, with `SEval.mono` as the
inclusion and *the statement never changing*. `SEval.defeq` unifies
`SubjectReduction{,Full,Iota}`: the β/ζ/δ arms are written once (today three times, two
byte-identical at `SubjectReductionFull.lean:398-430` = `SubjectReductionIota.lean:157-189`) via
the abstract-`P` spine schema at `SubjectReductionFull.lean:309`.

```lean
/-- Q3. The environment the compiler compiles: `env` plus one defining equation per declaration
whose `_unsafe_rec` body the eraser reads. Class **C**, decidable per program. -/
structure CompilerEnv (env envC : VEnv) (lenv : Lean.Environment) (e : Expr) : Prop where
  le     : env ≤ envC
  wf     : envC.WF
  consts : envC.constants = env.constants
  bodies : ∀ c ∈ depClosure env e, ∀ b, compilerBody lenv c = some b →
             ∃ vb ty, TrExprS env (levelParams lenv c) [] b vb ∧
                      envC.defeqs ⟨(levelParams lenv c).length, .const c _, vb, ty⟩
  only   : ∀ d, envC.defeqs d → env.defeqs d ∨ IsCompilerDefn lenv d
  pats   : envC.pats = env.pats
```

### 4.4 `Lower` — the term-level pass relation — `Lower.lean`

Seventeen arms: eleven congruence, four redex, two fix. Indexed by `Σ : GlobalDeclarations` and
by nothing else — no source term, no `VEnv`, no run state, no fresh names, no evaluation-shaped or
relevance-shaped side condition anywhere. Free on `BinderName`s (`WcbvEval` reads only their
lengths, `Eval.lean:143-153,171`).

```lean
def CtorDecl (Σ) (kn : Kername) (iid : InductiveId) (k : Nat) : Prop :=
  envLookup Σ kn = some (.constantDecl ⟨some (.construct iid k [])⟩)
def ElimDecl (Σ) (kn : Kername) (iid : InductiveId) (np dp : Nat) (nfs : List Nat) : Prop :=
  ∃ body, envLookup Σ kn = some (.constantDecl ⟨some body⟩) ∧ ElimBody iid np dp nfs body
def DefnDecl (Σ) (kn : Kername) (b : LBTerm) : Prop :=
  envLookup Σ kn = some (.constantDecl ⟨some b⟩)
def RuntimeKey (Σ) (kn : Kername) : Prop :=
  (∃ iid k, CtorDecl Σ kn iid k) ∨ (∃ iid np dp nfs, ElimDecl Σ kn iid np dp nfs)

/-- A constructor head, before **or after** the specification environment's own δ step.
Both disjuncts are needed: `lower_correct`'s source side δ-unfolds `.const kn` to
`.construct iid k []`, and an under-applied constructor spine is a `WcbvEval` **value**, so the
value correspondence must be expressible at the post-δ head as well. -/
def CtorHeadOf (Σ) (h : LBTerm) (iid : InductiveId) (k : Nat) : Prop :=
  (∃ kn, h = .const kn ∧ CtorDecl Σ kn iid k) ∨ h = .construct iid k []
/-- Likewise for an eliminator: `.const kn` pre-δ, `mkElimBody …` post-δ. Dropping the second
disjunct makes `lower_correct` false at a stuck discriminant, where both sides are stuck values. -/
def ElimHeadOf (Σ) (h : LBTerm) (iid : InductiveId) (np dp : Nat) (nfs : List Nat) : Prop :=
  (∃ kn, h = .const kn ∧ ElimDecl Σ kn iid np dp nfs) ∨ h = mkElimBody iid np dp nfs

inductive Lower (Σ : GlobalDeclarations) : LBTerm → LBTerm → Prop
  -- congruence (11)
  | box                                    : Lower Σ .box .box
  | bvar (i)                               : Lower Σ (.bvar i) (.bvar i)
  | fvar (x)                               : Lower Σ (.fvar x) (.fvar x)
  | prim (p)                               : Lower Σ (.prim p) (.prim p)
  | const {kn} (h : ¬ RuntimeKey Σ kn) (h2 : ¬ ∃ b, DefnDeclFix Σ kn b) :
                                             Lower Σ (.const kn) (.const kn)
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
  -- redex (4)
  /-- `R_ctor`, saturated or over-applied: applied form, so no arity is stored in the node and
      inductive parameters are kept (Q5). -/
  | ctorApp {h iid k args args'} (hh : CtorHeadOf Σ h iid k)
      (hlen : args'.length = args.length)
      (ha : ∀ i, i < args.length → Lower Σ args[i]! args'[i]!) :
      Lower Σ (LBTerm.mkApps h args) (LBTerm.mkApps (.construct iid k []) args')
  /-- `R_ctorη`: `visitCtorEtaGo` (`Erasure.lean:721-728`) pushes fresh binders into the spine
      and wraps the λ□ result in `mkLambdas`. `n` binders are added, `shift n 0` moves the
      already-lowered prefix under them. -/
  | ctorEta {h iid k args args' ns} (hh : CtorHeadOf Σ h iid k)
      (hund : args.length + ns.length = cstrArity Σ iid k)
      (hlen : args'.length = args.length)
      (ha : ∀ i, i < args.length → Lower Σ args[i]! args'[i]!) :
      Lower Σ (LBTerm.mkApps h args)
              (mkLambdas ns (LBTerm.mkApps (.construct iid k [])
                 ((args'.map (LBTerm.shift ns.length 0)) ++ bvarsDesc ns.length)))
  /-- `R_case`: a saturated eliminator application becomes a `.case` node. The `dp` arguments
      before the discriminant (parameters, motive, and for `rec` the minors' prefix) are
      *dropped* — sound for a forward simulation and exactly what MetaRocq's own expansion does.
      Over-application rides outside the node, matching `visitCases`' `args[casesInfo.arity:]`
      loop (`Erasure.lean:832`). -/
  | elimApp {hd iid np dp nfs pre disc disc' minors alts extra extra'}
      (hh    : ElimHeadOf Σ hd iid np dp nfs)
      (hlen  : pre.length = dp)
      (hmin  : LowerAlts Σ nfs minors alts)
      (hdisc : Lower Σ disc disc')
      (hxlen : extra'.length = extra.length)
      (hx    : ∀ i, i < extra.length → Lower Σ extra[i]! extra'[i]!) :
      Lower Σ (LBTerm.mkApps hd (pre ++ disc :: minors ++ extra))
              (LBTerm.mkApps (.case (iid, np) disc' alts) extra')
  /-- `R_caseη`: `visitCasesEtaGo` (`Erasure.lean:705-712`), same shape as `ctorEta`. -/
  | elimEta {hd iid np dp nfs args args' ns} (hh : ElimHeadOf Σ hd iid np dp nfs) … :
      Lower Σ (LBTerm.mkApps hd args) (mkLambdas ns (…))
  -- recursion (2) — the repair of §2 F1
  /-- `R_fix` at a *call*: a block member's constant relates to the block's `.fix` node. -/
  | fixConst {kn kns bs bs' defs j}
      (hb : bs.length = kns.length) (hb' : bs'.length = kns.length)
      (hd : defs.length = kns.length) (hnd : kns.Nodup)
      (hdecl : ∀ i, i < kns.length → DefnDecl Σ kns[i]! bs[i]!)
      (hlow  : ∀ i, i < kns.length → Lower Σ bs[i]! bs'[i]!)
      (hcl   : ∀ i, i < kns.length → CloseConst kns bs'[i]! (defs[i]!).body)
      (hj    : kns[j]? = some kn) :
      Lower Σ (.const kn) (.fix defs j)
  /-- `R_fix` at a *value*: the member's specification body relates to the same `.fix` node.
      This is the arm the δ step needs, and the one whose absence makes design A's T5 and
      design C's `fixIntro.correct` false. -/
  | fixBody {b kns bs bs' defs j}
      (hb …) (hb' …) (hd …) (hnd …) (hdecl …) (hlow …) (hcl …)
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
creating the kernel-rejected nested-inductive premise:

```lean
structure LowerBlock (Σ) (kns : List Kername) (bs bs' : List LBTerm)
    (defs : List (@FixDef LBTerm)) : Prop where
  hb : bs.length = kns.length ; hb' : bs'.length = kns.length
  hd : defs.length = kns.length ; hnd : kns.Nodup
  hdecl : ∀ i, i < kns.length → DefnDecl Σ kns[i]! bs[i]!
  hlow  : ∀ i, i < kns.length → Lower Σ bs[i]! bs'[i]!
  hcl   : ∀ i, i < kns.length → CloseConst kns bs'[i]! (defs[i]!).body
theorem Lower.fixConst' (h : LowerBlock Σ kns bs bs' defs) (hj : kns[j]? = some kn) :
    Lower Σ (.const kn) (.fix defs j)
theorem Lower.fixBody'  (h : LowerBlock Σ kns bs bs' defs) (hj : bs[j]? = some b)
    (hjl : j < defs.length) : Lower Σ b (.fix defs j)
```

Both wrappers are probe-checked (`scratchpad/probe/lowerfix2.lean`, axioms `[propext]`).

### 4.5 `LowerFix` — `LowerFix.lean`

```lean
/-- Replace `.const kns[j]` by `.fvar ids[j]`: the λ□-only residue of today's `Erases.fixvar`,
with the source side removed. -/
inductive ConstToFVar (kns : List Kername) (ids : List FVarId) : LBTerm → LBTerm → Prop

/-- The `Kername`-keyed fix closure, phrased through the **existing** `closeFix` so that
`closeFix_substList_fixSubst` (`FixUnfold.lean:748`) applies verbatim and no const-keyed twin of
`FixUnfold`'s 41 theorems has to be re-proved. -/
def CloseConst (kns : List Kername) (t u : LBTerm) : Prop :=
  ∃ ids t', ids.Nodup ∧ ids.length = kns.length ∧ (∀ x ∈ ids, ¬ hasFVar x t) ∧
    ConstToFVar kns ids t t' ∧ u = closeFix ids 0 t'

/-- **The transport that makes the fix arms usable.** A fix unfolding
(`WcbvEval.fix_guarded`'s `substList (fixSubst defs)`) puts `.fix defs i` exactly where the
lowered body has the sibling `.const knᵢ`; this lemma says the result is still `Lower`-related to
the same specification body, by re-deriving each such position with `fixConst`. -/
theorem Lower.constToFix (hblk : LowerBlock Σ kns bs bs' defs)
    (hcl : LBClosed t 0) (h : Lower Σ s t)
    (hct : ConstToFVar kns ids t t') :
    Lower Σ s (LBTerm.substFix ids defs t')

/-- Declaration-level statement, for `LowerEnv`. Tolerates an unused fix binder: `visitMutual`
decides recursiveness by `name_occurs` on the **source** body (`Erasure.lean:878`), and if
erasure removes the only self-reference the emitted `.fix` binder is unused — which is why no
`name_occurs`-mirroring premise exists anywhere in this design. -/
def LowerFix (Σ) (kns : List Kername) (bs : List LBTerm)
    (defs : List (@FixDef LBTerm)) : Prop := ∃ bs', LowerBlock Σ kns bs bs' defs
```

### 4.6 `ElimBody`, `IndInfo`, `SubsingletonElim` — `ElimBody.lean`

The runtime library's bodies are **constructions**, and their ι-reproduction is a **theorem**, not
an assumed obligation. This is design A's move, and it is what discharges Letouzey's `(◄₄)` rather
than assuming it (criterion 7, `[L R4]`).

```lean
def mkCtorBody (iid : InductiveId) (k : Nat) (ns : List BinderName) : LBTerm
def mkElimBody (iid : InductiveId) (np dp : Nat) (nfs : List Nat) : LBTerm
def mkElimBodySing (iid : InductiveId) (np dp : Nat) (nf : Nat) : LBTerm

/-- The λ□ body of an eliminator constant, as a *syntactic* shape — decidable, one constructor
per shape, no semantic side condition. -/
inductive ElimBody : InductiveId → Nat → Nat → List Nat → LBTerm → Prop
  | cases {iid np dp nfs} : ElimBody iid np dp nfs (mkElimBody iid np dp nfs)
  | rec   {iid np dp nfs} : ElimBody iid np dp nfs (mkElimBodyRec iid np dp nfs)
  | sing  {iid np dp nf}  : ElimBody iid np dp [nf] (mkElimBodySing iid np dp nf)

/-- `[S Fig. 18]`'s side condition reproduced: applying the canonical body to parameters, a
motive, a constructor spine and the minors evaluates exactly as MetaRocq's `iota_red` does.
Class **A** — `LBTerm` only. -/
theorem mkElimBody_iota {Σ fl iid np dp nfs k args minors pre r}
    (hk : k < nfs.length) (harity : (args.drop np).length = nfs[k]!)
    (hprop : isPropositionalInductive Σ iid = false) :
    WcbvEval Σ fl (LBTerm.mkApps (mkElimBody iid np dp nfs)
                     (pre ++ LBTerm.mkApps (.construct iid k []) args :: minors)) r ↔
    WcbvEval Σ fl (LBTerm.mkApps minors[k]! (args.drop np)) r

/-- The `with_prop_case` companion (`[S §7.1]` amendment (2), `[L Def. 8]` clause 2): a
subsingleton discriminant that erased to `□`. -/
theorem mkElimBody_iota_sing {Σ iid np dp nf minors pre r}
    (hprop : isPropositionalInductive Σ iid = true) :
    WcbvEval Σ eraseFlags (LBTerm.mkApps (mkElimBodySing iid np dp nf) (pre ++ .box :: minors)) r ↔
    WcbvEval Σ eraseFlags (LBTerm.mkApps minors[0]! (List.replicate nf .box)) r

theorem mkCtorBody_beta {Σ fl iid k ns args r} (h : args.length = ns.length) :
    WcbvEval Σ fl (LBTerm.mkApps (mkCtorBody iid k ns) args) r ↔
    WcbvEval Σ fl (LBTerm.mkApps (.construct iid k []) args) r

/-- `env`'s inductive block data for `I`, read off `VEnv.WF`'s declaration list (`VEnv` itself
stores none — `Theory/VEnv.lean:17-23`), in λ□ coordinates. -/
structure IndInfo (env : VEnv) (I : Name) (iid : InductiveId) (np : Nat) (nfs : List Nat) : Prop

/-- Lean's large-elimination criterion, **minus** the index-determined disjunct (N17, Q2).
Derived from `envC.WF` via `VInductDecl.LargeElim` (`Theory/Inductive.lean:226`) once
`VEnv.WF'.consts_origin` lands upstream; one named class-**C** hypothesis with one ledger row
until then. -/
def SubsingletonElim (env : VEnv) (I : Name) : Prop
theorem subsingletonElim_of_wf (henv : env.WF) (hrec : env.constants (mkRecName I) = some ci)
    (hlarge : ci.uvars = declUvars + 1) : SubsingletonElim env I     -- modulo the upstream ask
```

### 4.7 `ErasesLB` — the composite and the derived introduction lemmas — `ErasesLB.lean`

```lean
def ErasesLB (env : VEnv) (Us : List Name) (Σ : GlobalDeclarations)
    (Δ : VLCtx) (e : Expr) (t : LBTerm) : Prop :=
  ∃ t₀, Erases env Us Δ e t₀ ∧ Lower Σ t₀ t
```

Each deleted `Erases` rule reappears as a **theorem** with the same argument shape, so the 18
motives' proof scripts change by a name (`exact .ctor …` becomes `exact ErasesLB.ctor …`):

```lean
theorem ErasesLB.box   : TrExprS env Us Δ e ve → Erasable env Us.length Δ.toCtx ve →
                         ErasesLB env Us Σ Δ e .box
theorem ErasesLB.app   : ErasesLB env Us Σ Δ f f' → ErasesLB env Us Σ Δ a a' →
                         ErasesLB env Us Σ Δ (.app f a) (.app f' a')
theorem ErasesLB.ctor_head {cn us iid k} (hc : CtorDecl Σ (toKername cn) iid k)
    (h : env.constants cn = some ci) :
    ErasesLB env Us Σ Δ (.const cn us) (.construct iid k [])
theorem ErasesLB.ctor {cn us iid k args args'} (hc : CtorDecl Σ (toKername cn) iid k)
    (hlen : args'.length = args.length)
    (ha : ∀ i, i < args.length → ErasesLB env Us Σ Δ args[i]! args'[i]!) :
    ErasesLB env Us Σ Δ (args.foldl Expr.app (.const cn us))
                        (LBTerm.mkApps (.construct iid k []) args')
theorem ErasesLB.ctor_eta {…} : …                              -- `visitCtorEta`'s shape
theorem ErasesLB.cases {con us iid np dp nfs args disc alts} (hE : ElimDecl Σ (toKername con) …)
    (henv : env.WF) (hΔ : VLCtx.WF env Us.length Δ)
    (hpre : ∀ a ∈ args.take dp, ∃ ve, TrExprS env Us Δ a ve)   -- discharged by exists_of_trExprS
    (hd : ErasesLB env Us Σ Δ (args.get! dp) disc)
    (hm : ErasesLBAlts env Us Σ Δ nfs (args.drop (dp+1)) alts) :
    ErasesLB env Us Σ Δ (args.foldl Expr.app (.const con us)) (.case (iid, np) disc alts)
theorem ErasesLB.cases_eta {…} : …                             -- `visitCasesEta`'s shape
theorem ErasesLB.fix {cn us kns bs defs j} (hblk : LowerBlock Σ kns bs bs' defs)
    (hj : kns[j]? = some (toKername cn)) (h : env.constants cn = some ci) :
    ErasesLB env Us Σ Δ (.const cn us) (.fix defs j)
```

`ErasesLB.cases`'s `hpre` is the one genuinely new premise, and it is discharged by
`Erases.exists_of_trExprS` from the `TrExprS` every motive already carries: the arguments a
`.case` node drops still need an erasure image in `t₀`, because `Erases` is a congruence over the
whole spine.

### 4.8 `ErasesDecl`, `ErasesEnv`, `LowerEnv`, `EnvAgree`, `SpecEnv` — T3 — `ErasesEnv.lean`, `SpecEnv.lean`

```lean
inductive ErasesDecl (envC : VEnv) : Kername → GlobalDecl → Prop
  | defn {c us body b₀ ty} (hd : envC.defeqs ⟨us.length, .const c (levelsOf us), body, ty⟩)
         (hb : Erases envC us [] body b₀) :
         ErasesDecl (toKername c) (.constantDecl ⟨some b₀⟩)
  | ax   {c ci} (h : envC.constants c = some ci) (hno : ∀ df, ¬ IsDefnOf envC c df) :
         ErasesDecl (toKername c) (.constantDecl ⟨none⟩)
  | ind  {I iid np nfs} (h : IndInfo envC I iid np nfs) :
         ErasesDecl iid.blockName (.inductiveDecl (indBodyOf envC I))
  | ctor {c I iid k np nfs} (h : CtorOf envC c I k) (hi : IndInfo envC I iid np nfs) :
         ErasesDecl (toKername c) (.constantDecl ⟨some (.construct iid k [])⟩)
  /-- `casesOn`-like constants only (`Lean/Meta/CasesInfo.lean:56`'s `isCasesOnLike`:
      `isCasesOnRecursor ∨ isSparseCasesOn`; never `X.rec`, and matchers are gone by
      `prepare_erasure`'s `inlineMatchers`). A recursor reached as a constant is body-less and
      arrives through `ax` + `AxiomRealizer` — measured: `Eq.rec` is
      `(ConstantDecl (constant_body None))` in `Fannkuch.ast`. -/
  | elim {I kn iid np dp nfs body} (hi : IndInfo envC I iid np nfs) (he : CasesOnOf envC I kn)
         (hs : nfs.length = 1 → IsPropositional envC I → SubsingletonElim envC I)
         (hb : ElimBody iid np dp nfs body) :
         ErasesDecl kn (.constantDecl ⟨some body⟩)
```

`ErasesDecl.quot` is deleted (Q7). `ErasesEnv` is `[S §7.4]`'s `erases_deps` — bottom-up,
dependency-selective, the **only** relation between a `VEnv` and λ□:

```lean
inductive ErasesEnv (envC : VEnv) : GlobalDeclarations → LBTerm → Prop
```

The emitted environment is the lowered, pruned image — class **A**, and the conclusion is stated
up to `EnvAgree` (design A's graft: literal list equality is brittle and *meaningless*, since
`WcbvEval`, `constructorArity` and `isPropositionalInductive` read only `envLookup`):

```lean
def EnvAgree (Σ Σ' : GlobalDeclarations) : Prop :=      -- notation: `Σ ≐ Σ'`
  (∀ kn, envLookup Σ kn = envLookup Σ' kn) ∧ (Σ.map Prod.fst).Nodup ∧ (Σ'.map Prod.fst).Nodup
theorem WcbvEval.congr_env (h : Σ ≐ Σ') : WcbvEval Σ fl t v → WcbvEval Σ' fl t v

structure LowerEnv (Σ⁺ Σ : GlobalDeclarations) : Prop where
  keys   : (Σ.map Prod.fst).Nodup
  defs   : ∀ kn b₀ b, DefnDecl Σ⁺ kn b₀ → DefnDecl Σ kn b →
             Lower Σ⁺ b₀ b ∨ ∃ kns bs defs j, LowerFix Σ⁺ kns bs defs ∧
                                              kns[j]? = some kn ∧ b = .fix defs j
  axioms : ∀ kn, envLookup Σ⁺ kn = some (.constantDecl ⟨none⟩) →
             envLookup Σ kn = some (.constantDecl ⟨none⟩) ∨ envLookup Σ kn = none
  inds   : ∀ kn d, envLookup Σ⁺ kn = some (.inductiveDecl d) → envLookup Σ kn = some (.inductiveDecl d)
  prune  : ∀ kn, envLookup Σ kn ≠ none → Reachable Σ kn         -- Q4: the library costs 0% on disk
  closed : ClosedEnv Σ
```

**Environment threading.** The bridge's motives quantify `Σ⁺` *universally* under an antitone
premise, so sibling sub-runs never merge environments:

```lean
/-- `Σ⁺` is a specification environment for the run state `s`: every constant `s` registered has
its `ErasesDecl` image in `Σ⁺`, and every inductive `s` registered contributes its `ind`, `ctor`
and `elim` declarations. Antitone in the state, which is what makes it compose. -/
def SpecEnv (envC : VEnv) (s : ErasureState) (Σ⁺ : GlobalDeclarations) : Prop
theorem SpecEnv.mono   (h : StateLe s₁ s) : SpecEnv envC s Σ⁺ → SpecEnv envC s₁ Σ⁺
theorem SpecEnv.exists (hreg : RegInvShape' s) (P : PrimSpec …) : ∃ Σ⁺, SpecEnv envC s Σ⁺
```

`StateLe` (`ErasureRun.lean:1585`) and `RunConcl` (`:1609`) already exist and carry unchanged;
`SpecEnv.exists` builds `Σ⁺` from `RegInvShape` (`ColdStartShape.lean:314`) plus
`PrimSpec.lookup_adequate`, keeping the tree's genuine advantage over the papers' presentation:
the environment relation is *derived from what the run registered and consulted*.

### 4.9 Output boundary — `Output.lean`

```lean
/-- What `untyped_transform_pipeline` needs from us, on the emitted program alone. `fresh`…
`projDecl` are `EWellformed all_env_flags` (what `peregrine validate` checks); `etaCtors` is the
constructor-saturation invariant `validate` omits and `remove_params_optimization` consumes
(measured 982/982). Fixpoint η is **not** claimed: it is false on all five programs — F-ETA. -/
structure LBWfPeregrine (Σ : GlobalDeclarations) (t : LBTerm) : Prop where
  keys, declsWf, closed, constsOk, ctorApplied, ctorDecl, casesExh, fixLambda, projDecl : …
  etaCtors    : ∀ iid k n, ConstructSpine Σ t iid k n → n ≥ cstrArity Σ iid k
  asciiNames  : ∀ nm ∈ binderNames Σ t, nm.isAsciiGraphic          -- the λ□ parser's constraint

/-- What peregrine's first pass actually requires. `LBWfPeregrine` is strictly weaker; the
difference is exactly fixpoint η (§8.2 F-ETA; peregrine's own discharge is `Admitted`,
`Transforms.v:375`, so nothing downstream detects it). **Not concluded by T9.** -/
def PeregrinePre (Σ) (t) : Prop := LBWfPeregrine Σ t ∧ LBExpandedFix Σ t

/-- `[S §5.6]`'s `axiom_free` generalised — the naive form is uninhabited in Lean, which is why
the current capstones cover 0/5. A `Prop`-typed axiom is `Erasable`, hence boxed, hence never
*reachable*; so the condition is reachability on the emitted program, and it is decidable there. -/
def ErasableAxioms (Σ : GlobalDeclarations) (t : LBTerm) : Prop :=
  ∀ kn, ReachableFrom Σ t kn → envLookup Σ kn = some (.constantDecl ⟨none⟩) → AxiomRealizer Σ kn
inductive AxiomRealizer (Σ) : Kername → Prop          -- N2, one row per name (`Eq.rec`, `@[extern]`)
```

`ctorApplied` (`NoBlock t`) and `closed` are supplied **unconditionally and panic-tolerantly** by
`visitExpr_shape_all` — two conjuncts for free.

### 4.10 `PrimSpec` — the one bundle — `PrimSpec.lean`

Built by renaming `OracleDischarge.ResidualHyps` (`OracleDischarge.lean:65`, already four fields
in this shape) and adding two.

```lean
structure PrimSpec (lenv : Lean.Environment) (env : VEnv) (Us : List Name)
    (gw : Void IO.RealWorld → NameGenerator) : Prop where
  env_connect     : ∃ ves : VEnvs, ves.WF lenv ∧ env = ves.venv .safe     -- + `abs_env_irr`
  lookup_adequate : …    -- getConstInfo / getCasesInfo? / getCtorArity? / getDeclInfo?
  fresh_names     : …    -- `mkFreshFVarId` returns identifiers absent from the ambient context
  oracle_sound    : …    -- **discharged**, not assumed (below)
  ind_adequate    : …    -- `InductiveVal` ↔ `VInductDecl` in `env`'s declaration list
  table_adequate  : SourceTableAdequate lenv tbl                          -- §2 F4

theorem PrimSpec.envWF (P : PrimSpec lenv env Us gw) : env.WF            -- via `TrEnv'.wf`
theorem PrimSpec.oracle_sound_of_run (P : PrimSpec …) … :
    Erasure.isErasable lps e = .ok true → TrExprS env lps Δ e ve →
    Erasable env lps.length Δ.toCtx ve                                    -- via `Oracle.kernel_isErasable_sound`
```

Fields 1, 2, 3, 5, 6 are class **D**; field 4 is class **B**, discharged through
`Relevance` → `RelevanceCheck.isErasable.WF` → `Oracle.kernel_isErasable_sound`. That chain is the
development's only trust *reduction*; keeping it is what makes criterion 9 satisfiable, it costs
33 axioms (measured, all classified in the ledger), and it is why shipping edit **B1** (the
`isErasable` kernel reroute) must stay. `PrimSpec.envWF` is a genuine trust reduction over the
current tree, which assumes `env.WF` outright.

The relational pass interface, with explicit binders (§2 F11):

```lean
structure LBPassR where
  rel        : GlobalDeclarations → LBTerm → LBTerm → Prop
  flIn flOut : WcbvFlags
  correct    : ∀ {Σ⁺ Σ t t' v}, LBWf Σ⁺ → LBClosed t 0 → LowerEnv Σ⁺ Σ → rel Σ⁺ t t' →
               WcbvEval Σ⁺ flIn t v → ∃ v', rel Σ⁺ v v' ∧ WcbvEval Σ flOut t' v'
```

### 4.11 `Supported`, `supportedB`, `SourceTable` — `Supported.lean`, `Witness/SourceTable.lean`

```lean
inductive SupportError where
  | sparseCasesOn (c : Name)       -- the measured Quicksort miscompile
  | sideConditionElim (c : Name) | etaContractedMinor (c : Name)
  | strLit | machineNat | quotPrim (c : Name) | ioLike (c : Name) | implementedBy (c : Name)
  | mvar | accRec (c : Name) | unknownConst (c : Name)
  deriving Repr, DecidableEq

/-- Decidable over `e` **and its dependency closure**, on the reified table, and it *names the
hole* — which is what generates the coverage table; `Bool` would lose the name. -/
def supportedB (tbl : SourceTable) (e : Expr) : Except SupportError Unit
def Supported (env : VEnv) (e : Expr) : Prop                    -- one named conjunct per SupportError
theorem supportedB_sound (P : PrimSpec …) (ht : SourceTableAdequate lenv tbl) :
    supportedB tbl e = .ok () → Supported env e
```

`Supported.casesApp` requires the head to be `I.casesOn` for an inductive in the fragment with a
**plain** `CasesInfo` (no `CasesAltInfo.default`, no `hasSideCondition`) and every minor a
syntactic λ-chain of its alt's field arity (`IsLamTelescope`, `Bridge.lean:60`, already assumed by
motive 18 — zero churn). The first exclusion is the shipping bug of `VerifyBench/Quicksort`; the
second is what makes the composite's branch rule exact. A *reporting* predicate
`HasCompilerBody` excludes nothing and feeds the coverage table.

```lean
/-- A reified, committed slice of the `Lean.Environment`: the `prepare_erasure`d bodies of the
dependency closure, the inductive metadata, the constructor arities, and the relevance oracle's
verdict at every subterm position. Generated by `lake exe reify`, byte-diffed in CI. This is the
only way a `by rfl`/`by decide` discharge can exist: `Lean.Environment` has a private constructor
and an opaque `EnvExtensionState`, and `native_decide` is banned. -/
structure SourceTable where
  decls  : List (Name × ReifiedDecl)
  inds   : List (Name × ReifiedInduct)
  oracle : List (Name × List (SubtermPos × Bool))
  cfg    : Erasure.ErasureConfig
def SourceTableAdequate (lenv : Lean.Environment) (tbl : SourceTable) : Prop
```

### 4.12 `FirstOrderInd` — T7 — `FirstOrderInd.lean`

```lean
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
theorem firstOrderIndB_sound (P : PrimSpec …) (ht : SourceTableAdequate lenv tbl) :
    firstOrderIndB tbl fuel I = true → FirstOrderInd env (foClosure tbl) I
```

`fields` ≡ `[L Def. 14]`; `informative` is the syntactic sufficient condition for `[L Def. 6]`,
whose *conclusion* is `firstorder_no_box`. This definition elaborates clean against the pinned
lean4lean (probe `q6.lean`, axioms `[propext, Quot.sound]`).

### 4.13 `lbEval` — the certified target evaluator — `Semantics/Compute.lean`

```lean
def lbEval (Σ : GlobalDeclarations) (fl : WcbvFlags) (fuel : Nat) : LBTerm → Option LBTerm
theorem lbEval_sound (h : lbEval Σ fl fuel t = some v) : WcbvEval Σ fl t v      -- class A
```

Unconditional, ~420 lines, every step one `WcbvEval` rule. It turns the target-side evaluation of
every green rung into `by rfl`, and it doubles as a differential oracle: `lake exe green-check`
compares `lbEval Σ eraseFlags` on the committed `.ast` with `peregrine eval` — a
cross-implementation agreement test on the λ□ semantics itself (CLAUDE.md's cheapest real
functional check). `srEval` (the source-side twin) is **W6-optional** and is built per flag slice
only if its soundness proof stays small; `eraseB` is **not built**.

### 4.14 The ledger — T11 — `test/Ledger.lean`

```lean
#print axioms LeanToLambdaBox.erases_correct
#print axioms LeanToLambdaBox.lower_correct
#print axioms LeanToLambdaBox.lowerFix_correct
#print axioms LeanToLambdaBox.visitExpr_refines_erasesLB
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorder
#print axioms LeanToLambdaBox.green_G1
#print axioms LeanToLambdaBox.green_G8
```

Rows, measured, never narrated: **(a1)** lean4lean's inherited `sorryAx` cluster at `20ec229` with
`file:line` (`Injectivity.lean:12,21,34`, `UniqueTyping.lean:174`, `ChurchRosser.lean:1193,1212`),
reaching here through `TrExprS.uniq` and `IsDefEq.uniqU`; **(a2)** `EnvLemmas.lean:334
VEnv.WF.patsStrong`, marked **fork-authored, not inherited** — which no current document does;
**(a3)** the 29-name executable-checker cluster criterion 9 brings in, including two
`_native.bv_decide` axioms from Lean core; **(b)** `PrimSpec`'s five class-**D** fields and `hrun`;
**(c)** the class-**C** hypotheses (`hcfg`, `hcomp`, `hsup`, `hax`, `hfo`, `hnp`, `hsub`, and the
source evaluation per N7); **(d)** the class-**E** rows: N1 csimp, N2 extern, N3 machine `Nat`,
N4 argmask, N5 auto-inline, N7 termination, N10 serialisation, N11 `.inlinings`/`.mli`, N14 size,
N16 `Quot`, N17 `Acc`, the compiler-vs-kernel body gap, peregrine's `Admitted` precondition and
its `validate` gap, MetaRocq's `firstorder_ind` defect, and Q8's dropped Rocq transport. **No
prose copy exists anywhere else in the repository.**

---

## 5. Theorems

```lean
-- T1  (carried; `Semantics/*`)
theorem eval_deterministic : WcbvEval Σ fl t v → WcbvEval Σ fl t v' → v = v'
theorem value_final        : Value Σ fl v → WcbvEval Σ fl v v

-- T4  subject reduction                                                            class B
theorem SEval.defeq (henv : envC.WF) (hΔ : VLCtx.WF envC Us.length Δ)
    (htr : TrExprS envC Us Δ e ve) (hev : SEval envC Us fl Δ e v) :
    ∃ vv, TrExprS envC Us Δ v vv ∧ envC.IsDefEqU Us.length Δ.toCtx ve vv

-- T5  erases_correct — exactly five hypotheses, at the specification environment    class B
theorem erases_correct
    (henv : envC.WF) (hwt : TrExprS envC Us [] e ve)
    (hev  : SEval envC Us fl [] e v)
    (her  : Erases envC Us [] e t)
    (hΣ   : ErasesEnv envC Σ⁺ t) :
    ∃ v', Erases envC Us [] v v' ∧ WcbvEval Σ⁺ eraseFlags t v'

-- T6  the passes                                                                    class A
theorem lower_correct
    (hwf : LBWf Σ⁺) (hcl : LBClosed t 0) (hE : LowerEnv Σ⁺ Σ) (h : Lower Σ⁺ t t')
    (hev : WcbvEval Σ⁺ eraseFlags t v) :
    ∃ v', Lower Σ⁺ v v' ∧ WcbvEval Σ eraseFlags t' v'
theorem lowerFix_correct    -- the block clause of `lower_correct`, stated separately for reuse
    (hE : LowerEnv Σ⁺ Σ) (hblk : LowerBlock Σ⁺ kns bs bs' defs) … :
    WcbvEval Σ⁺ eraseFlags (LBTerm.mkApps (.const kns[j]!) args) v →
    ∃ v', Lower Σ⁺ v v' ∧ WcbvEval Σ eraseFlags (LBTerm.mkApps (.fix defs j) args') v'
theorem LBOptimize_correct  -- optional corollary, W6; eraseFlags → optFlags
    : WcbvEval Σ eraseFlags t v → WcbvEval (LBOptimize_env Σ) optFlags (LBOptimize Σ t) (LBOptimize Σ v)

-- T7  first-order uniqueness and box-freedom                                        class B
theorem firstorder_erases_deterministic
    (henv : envC.WF) (hfo : FirstOrderInd envC fo I)
    (hwt : TrExprS envC Us [] v vv)
    (hty : envC.HasType Us.length [] vv (VExpr.mkApps (.const I us) args))
    (hval : SEval envC Us fl [] v v)
    (h₁ : Erases envC Us [] v t₁) (h₂ : Erases envC Us [] v t₂) : t₁ = t₂
theorem firstorder_lower_deterministic   -- §2 F3: determinism of the *composite* on data class A
    (hfo : FirstOrderShape Σ⁺ t) (h₁ : Lower Σ⁺ t u₁) (h₂ : Lower Σ⁺ t u₂) : u₁ = u₂
theorem firstorder_no_box (… same premises …) (h : Erases envC Us [] v t) : NoBox t

-- T8  the bridge                                                                    class B
theorem visitExpr_refines_erasesLB
    (P    : PrimSpec lenv env Us gw)
    (hcfg : ConfigPinned cfg)
    (hC   : CompilerEnv env envC lenv e)
    (hwt  : TrExprS envC Us Δ (prepare_erasure e) ve)
    (hsup : Supported envC (prepare_erasure e))
    (hnp  : ¬ Panicked run)
    (hrun : Erasure.visitExpr (prepare_erasure e) s ctx cctx ref w = .ok (t, s') w')
    (hinv : BridgeInv envC Us cfg (gw w) ctx s Δ) :
    ∀ Σ⁺, SpecEnv envC s' Σ⁺ →
      ErasesLB envC Us Σ⁺ Δ (prepare_erasure e) t ∧ RunConcl s s' ∧ gw w ≤ gw w'

-- T9  the capstone, applied form                                                    class B
theorem shipping_erase_correct_firstorder
    (P     : PrimSpec lenv env [] gw)
    (hcfg  : ConfigPinned cfg)                          -- N1-N5
    (hC    : CompilerEnv env envC lenv e)               -- N8, class C
    (hwt   : TrExprS envC [] [] e ve)
    (hsup  : Supported envC e)                          -- N6/N16/N17, class C, decidable
    (hnp   : ¬ Panicked run)                            -- N12, class C
    (hrun  : Erasure.erase e cfg cctx ref w = .ok (.untyped Σ (some t), inls) w') :
    ∃ Σ⁺, ErasesEnv envC Σ⁺ t₀ ∧ Lower Σ⁺ t₀ t
        ∧ LowerEnv Σ⁺ Σ
        ∧ LBWfPeregrine Σ t
        ∧ ErasableAxioms Σ t                            -- decidable on the emitted program
        ∧ ∀ (args : List Expr) (targs : List LBTerm) (I : Name) (us idx) (v : Expr) (vv : VExpr),
            (∀ i, i < args.length → ErasesLB envC [] Σ⁺ [] args[i]! targs[i]!) →
            SEval envC [] fullFlags [] (mkApps e args) v →
            TrExprS envC [] [] v vv →
            envC.HasType 0 [] vv (VExpr.mkApps (.const I us) idx) →
            FirstOrderInd envC fo I →
            ∃ tv₀ tv, Erases envC [] [] v tv₀ ∧ Lower Σ⁺ tv₀ tv ∧ NoBox tv
                    ∧ (∀ tv', Erases envC [] [] v tv' → tv' = tv₀)
                    ∧ WcbvEval Σ eraseFlags (LBTerm.mkApps t targs) tv
```

At `args = []` this is the spec's T9 verbatim; at `args = [.lit 0]` it is the observation for
`benchArith`. The uniqueness conjunct is T7 and is what makes the conclusion *an answer* rather
than an existential. `hrun` is a permanent class-**D** binder (§2 F18).

Composition, mirroring `[S §7.3]`: `erase_run_ok` (`ColdStartRun.lean:651`) decomposes the run into
`prepare_erasure` then `visitExpr`; T8 puts the output in `Erases ⨟ Lower` at a `Σ⁺` that
`SpecEnv.exists` constructs; T5 simulates the source evaluation into λ□ at `Σ⁺` and `eraseFlags`;
`lower_correct` carries it to `Σ` at the same flags — which is the deliverable point (§3.2); T7
identifies the value uniquely and shows it box-free.

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
| G6 | `spikeFix : Nat := Nat.add 2 3` | `_unsafe_rec`, `envC`, `.fix` | W3 |
| G7 | `arithClosed : Nat := benchArith 0` | the typeclass tower: 10 projections, 4 fix blocks, 5 `.case`, 19-node peano tower | W5 |
| G8 | `benchArith : Nat → Nat` | function-typed subject; the applied capstone | W5 |

`LeanToLambdaBox/Green.lean` is a tracked default build target holding, for every rung reached so
far, a theorem whose conclusion ends in a **literal** peano numeral — so it cannot be satisfied by
`□` or a stuck term — with every class-**C** hypothesis inhabited by a checked term. Waves that
predate T8 carry one extra binder `hbridge`; W4 discharges it and the rungs become unconditional
statements about the shipping eraser. `lake exe green-check` re-runs `#erase` on every rung,
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
| `FixMetatheory.lean`, `FixUnfold.lean` | 1,184 | re-aimed at `lowerFix_correct`; **statements unchanged** |
| `IotaBridge.lean` | 207 | re-aimed at `lower_correct`'s `elimApp` arm; statements unchanged |
| `Erasability.lean` | 230 | + `Erasable.mono` (~10 lines, from `HasType.mono`) |
| `Relevance.lean`, `RelevanceCheck.lean` | 229 | the executable oracle and its `M.WF` soundness |
| `OutputShape.lean` | 155 | panic modelling; feeds `doc/panics.md` |
| `ErasureRun.lean` | 3,234 | 74 `run_*`, `RunConcl`, `StateLe`, `⊑`/admissibility, `mutual_le_of` — relation-independent, **zero edits** |
| `Optimize.lean` | 1,090 | wired into the closure as the pass template + W6 corollary |
| `Basic.lean`, `Erasure.lean`, `Printing.lean` | 1,422 | **shipping; untouched** (§8) |

### 7.2 Re-anchored

| Module | Lines | What changes | Wave |
|---|---|---|---|
| `Semantics/Flags.lean` | 61 | §3.2's three constants; header rewritten | W0 |
| `Erases.lean` | 1,426 | ten rules (§4.2); transport half carried; six rules' arms deleted | W1 |
| `ErasesAbstract/Strengthen/Uniform.lean` | 1,865 | nine arms survive per lemma; six die with their rules | W1 |
| `SourceEval.lean` (+`SourceEvalData.lean`) | 701 → ~250 | one flag-parameterised `SEval`; seven relations deleted | W1 |
| `SubjectReduction{,Full,Iota}.lean` | 1,414 → ~1,050 | merged into `SubjectReduction.lean`; β/ζ/δ written once | W1/W2/W3 |
| `EnvErasure{,Nonrec,Rec}.lean` | 1,640 → ~700 | become `ErasesEnv.lean` + `SpecEnv.lean` | W1/W3 |
| `CheckerAdequacy.lean` | 143 | seven declarations upstreamed; the eighth renamed into `LeanToLambdaBox.Oracle` | W1 |
| `OracleDischarge.lean` | 123 | becomes `PrimSpec.lean` | W1 |
| `Bridge.lean` | 674 | `Supported` moves to `Supported.lean`; `BridgeInv` keeps 7 of 10 fields | W1/W4 |
| `FirstOrder.lean` | 762 → ~250 | `informativeType_not_erasable` (`:103-131`) carried verbatim; becomes `FirstOrderInd.lean` | W3 |
| `ColdStartShape.lean` | 1,055 → ~600 | `RegInvShape` keeps `kn`/`cover`/`closed`/`nofix`; five `Registered*On` fields move to `SpecEnv` | W4 |
| `ColdStartInduction.lean` | 1,503 | `visitExpr_shape_all` carried verbatim; `RegBridgeHyps` and its fixtures deleted | W4 |
| `ColdStartRun.lean` | 672 | `erase_run_ok`, `run_prepare_erasure_ok` carried | W4 |
| `VisitExprRefines.lean` | 4,641 | 18 motives restated against `ErasesLB` + `SpecEnv` — **the long pole**, split in three | W4 |
| `ErasesCorrect.lean` | 650 | becomes T5 with five hypotheses; ι/proj arms absorbed from the deleted chains | W1-W3 |
| `ColdStart.lean` | 2,000 → ~500 | becomes `Capstone.lean` | W4/W5 |
| `LeanToLambdaBox.lean` | 217 | import list and header rewritten | every wave |
| `VerifyBench/STATUS.md` | 520 | retired **into** `doc/coverage.md`, not duplicated | W5 |

### 7.3 New

| File | Contents | Est. |
|---|---|---|
| `Semantics/Compute.lean` | `lbEval`, `lbEval_sound` | 420 |
| `Lower.lean` | `Lower` (17 arms), `LowerAlt(s)`, `CtorDecl`/`ElimDecl`/`DefnDecl`/`RuntimeKey`/`CtorHeadOf`/`ElimHeadOf`, `LowerBlock`, inversion + shift/subst commutation | 850 |
| `LowerCorrect.lean` | `lower_correct`, `lowerFix_correct`, non-vacuity guards | 1,100 |
| `LowerFix.lean` | `ConstToFVar`, `CloseConst`, `LowerFix`, `Lower.constToFix` | 600 |
| `ElimBody.lean` | `mkCtorBody`/`mkElimBody`/`mkElimBodySing`, the three ι theorems, `ElimBody`, `IndInfo`, `SubsingletonElim`, `subsingletonElim_of_wf` | 850 |
| `ErasesLB.lean` | the composite + seven derived introduction lemmas + transport | 500 |
| `ErasesEnv.lean` | `ErasesDecl`, `ErasesEnv`, `LowerEnv`, `EnvAgree`, `WcbvEval.congr_env` | 650 |
| `SpecEnv.lean` | `SpecEnv`, `.mono`, `.exists` | 350 |
| `ErasesTotal.lean` | `Erases.exists_of_trExprS`, `sort_erasable`, `forallE_erasable`, `Erases.mono` | 300 |
| `CompilerEnv.lean` | `CompilerEnv`, `CompilerBodyOf`, the `env ≤ envC` lifting kit | 280 |
| `PrimSpec.lean` | `PrimSpec`, `envWF`, `oracle_sound_of_run`, `LBPassR` | 260 |
| `Supported.lean` | `SupportError`, `Supported`, `supportedB`, soundness, closure lemmas | 550 |
| `Output.lean` | `LBWfPeregrine`, `PeregrinePre`, `ErasableAxioms`, `AxiomRealizer`, checkers | 420 |
| `FirstOrderInd.lean` | `FirstOrderInd`, `firstOrderIndB`, adequacy, `firstorder_no_box`, `firstorder_lower_deterministic` | 500 |
| `Witness/SourceTable.lean` | `SourceTable`, `SourceTableAdequate`, lookups | 320 |
| `Capstone.lean` | T9 | 550 |
| `Green.lean` | the ladder's theorems | 400 |
| `VerifyBench/Spikes/G1..G8.lean` + `VerifyBench/tables/*` | the rungs and their committed tables | 300 |
| `Tools/{Reify,GreenCheck,Hygiene,Coverage}.lean` | `lake exe` drivers | 450 |
| `test/Ledger.lean` + `test/ledger.expected` | the measured ledger | 80 |
| `doc/{rules-Erases,rules-Lower,panics,coverage,upstream-asks}.md` | criteria 3, 10, 14, 21 | — |

Net: ≈9,400 new lines against 19,592 deleted (`02-PLAN.md` §4) and ≈8,800 carried untouched,
plus the 1,422 shipping lines this development never edits.

### 7.4 Deleted, and when

Full schedule in `02-PLAN.md` §4. Summary: `ErasureContext.lean` (251, criterion 1);
`DeltaHyps` (1,499), `CasesBridgeHyps` (287), `DataBridgeHyps` (137), `ProjBridgeHyps` (182),
`PrepareHyps` (118) — one `PrimSpec`; `ErasesCorrectData` (1,731), `ErasesCorrectIota` (1,075) —
their ι/proj content re-lands in T5's arms; `IotaPattern` (485), `IotaDischarge` (604),
`ProjPattern` (1,059), `ProjDischarge` (415), `SubjectReductionIota` (458) — the discharge chains
keyed on the six deleted rules, with `IotaRelevant`/`IotaShape`; `RecBlockErasure` (811) —
replaced by `LowerFix`; `EraseCore` (643) minus the fuel lemmas; `FirstOrderShipping` (254),
`FirstOrderShippingIota` (553), `ShippingCorrect` (207), `ShippingCorrectData` (127) — four
capstone flavours become one; `Export/EvalT` (296), `Semantics.lean` (17), `Eval.lean` (11);
`ErasesLevels`/`ErasesInstL`/`ErasesDeltaL` (1,146, of which ~200 survive as level-instantiation
lemmas T5's δ arm needs); the three prose ledgers; ~3,000-3,500 comment lines of changelog.

---

## 8. Transpiler edits

### 8.1 Required by the verification: **none**

No wave edits `LeanToLambdaBox/{Erasure,Basic,Printing}.lean`. The proof-only edits already on
`dev/verify` (P1-P7: the `partial_fixpoint` mutual block, nine `@[partial_fixpoint_monotone]`
lemmas, `expr_withApp_eq`, `visitCasesEta`/`visitCtorEta`, the `.toArray` over-application loop,
`Basic.lean`'s de-partialized `toBvar` family, the `Relevance` import) are carried unchanged, and
the behaviour-affecting edit **B1** (the `isErasable` kernel reroute, `Erasure.lean:151-187`) is
**kept**, because `PrimSpec.oracle_sound` is discharged through it; reverting it would demote that
field to class **D** and make criterion 9 unsatisfiable. Its measured under-erasure (review SI-1)
is owned inside `Supported` and `PrimSpec`, with the finding raised.

Two shipping-side facts need a **ledger row each** rather than a code change, under N11: **B4**
(the `@[inline]` restructure at `Erasure.lean:857-875`, which changes `.ast.inlinings` for
multi-declaration mutual blocks) and **B6** (the `MLType` extension at `:934-980`, affecting only
the `.mli` sidecar). **B5** (`withLocalDef` dropping `nd`, `:283-295`) is argued behaviour-neutral
and is unmeasured in-repo; W5's coverage script diffs the five regenerated `.ast` files against
the frozen originals and settles it. If it diverges, that is a raised finding, not a patch.

### 8.2 Proposed for branch `dev/fix` — raised here, never applied on `dev/verify`

The repository's standing rule is *raise implementation issues, do not silently patch them*. Each
edit below is therefore specified, justified, and assigned to a separate branch; the verification
tree never depends on any of them landing.

| Id | Site | Defect | Proposed edit | Justification |
|---|---|---|---|---|
| **F-ETA** | `visitMutual`, `Erasure.lean:878-911` | a recursive declaration's body is a bare unapplied `.fix`, so `EEtaExpandedFix.expanded_eprogram` — the precondition of `untyped_transform_pipeline` (`Transforms.v:147` → `ETransform.v:710-716`) — is **false on all five programs**; peregrine's own discharge is `Admitted` (`Transforms.v:375`), so nothing detects it | wrap the emitted body in `rarg+1` lambdas applied to their own binders (the eraser's own TODO at `:911`) | Coq avoids this by η-expanding before erasure (`Template/EtaExpand`). Without the edit the frontend's output violates a documented precondition of the consumer it is written for |
| **F-SPARSE** | `visitCases`, `Erasure.lean:770,817` | the inductive is recovered by `casesInfo.declName.getPrefix`, so a sparse `casesOn` (`_sparseCasesOn_`, named after the enclosing function) hits `unreachable!`, which *succeeds* at `EraseM` returning `.box`: `Quicksort` panics, exits 0, and writes a **wrong** `.ast` that passes `peregrine validate` | recover the inductive from `CasesInfo` rather than from the name, and handle `CasesAltInfo.default` | already `RAISED-not-fixed`; this design makes it visible as `SupportError.sparseCasesOn` in the predicate a reader audits and as a named row in the generated coverage table |
| **F-ACC** | `visitCases` at a `Prop`-valued inductive with an index-determined field | for `Acc`-shaped inductives the emitted `.case` on a boxed discriminee evaluates by `iota_sing`, which boxes a field that is **data** (`Acc.intro`'s `x : α`; measured `largeElimClause ``Acc = some (2,[1])`) | refuse `Acc.rec`/`WellFounded.fix`, as Lean's own code generator does | restricted here by N17; the alternative (a two-class field treatment plus `iota_sing_idx`) needs type-former injectivity at the redex and is W6 |
| **F-QUOT** | `Erasure.lean:873-877` | `Quot` primitives are emitted as body-less axioms, so a quotient program erases to a stuck term that passes `validate` | emit a realizer, or refuse | restricted here by N16 |
| **F-EQREC** | `Erasure.lean:873-877` | recursors reached as constants have no compiler value and are emitted body-less (`Eq.rec` in `Fannkuch.ast`), so the program is stuck there unless peregrine's `.attr` channel supplies a realizer — which the frontend does not emit | emit the remapping into `.ast.inlinings`/`.attr` | covered here by an `AxiomRealizer` row at class **D** plus a ledger row; someone must decide whether the frontend should emit it |

### 8.3 Upstream asks (lean4lean, N15) — `doc/upstream-asks.md`

1. `VEnv.WF'.consts_origin`, the constants-keyed twin of `WF'.pats_origin`
   (`InductiveParams.lean:93`), plus `iotaRHS'_Generic` — the missing link in Q2's derivation.
2. The seven kernel-generic declarations currently in `CheckerAdequacy.lean` (`VContext.ofMLCtx`
   and its three `@[simp]` projections, `VState.WF.initial`, `M.WF.run'`, `kernelNGen`), which
   criterion 21 forbids here and criterion 9 needs.
3. The `Quot.ind` divergence between `Theory/Quot.lean:11` and the executable checker.
4. **Reported, not asked:** MetaRocq's `firstorder_ind` is `false` on `nat`
   (`PCUICFirstorder.v:59`'s sort conjunct), so every theorem guarded by it is vacuously guarded;
   and peregrine's `run_untyped_transforms` precondition obligation is `Admitted`
   (`Transforms.v:375`) while `peregrine validate` does not check η-expandedness.

---

## 9. Documentation and code-quality policy

1. **Current fact only.** No "used to", commit hash, date, slice tag, round name, memory
   reference, or untracked-handoff citation in any docstring. History goes in commit messages.
   The specific repairs the review demanded are in scope and scheduled in W0:
   `Semantics/Flags.lean:19-24` (asserts the opposite of the design), the seven "no `addPat`
   clause" sites and the eight "`addInduct_WF` is `sorry`" sites (both measured **false** at
   `20ec229`), the five stale oracle descriptions, `Supported.casesApp`'s sparse-`casesOn`
   sentence, and the `ProjDischarge`/`ProjPattern` contradiction about `proj_defeq`.
2. **One fact, one home.** Every claim about upstream state lives once, in `test/ledger.expected`,
   with the `file:line` and the command that measured it. CI greps for a second copy.
3. **Length budget.** ≤ 8 lines per lemma/field docstring, ≤ 40 per module header. Longer is a
   status document and belongs in `doc/`, tracked.
4. **Every backticked identifier resolves; every cited document exists.** CI grep
   (`lake exe hygiene`).
5. **A docstring says what the object *is*, and why a hypothesis is not slack** — with a
   counterexample where one exists. The models are `IotaBridge.lean:96-111`,
   `Semantics/Values.lean:79`, `Semantics/Eval.lean:29`. Under this design that duty is heaviest
   on `Lower`'s four redex arms and two fix arms, and on `CtorHeadOf`/`ElimHeadOf`'s second
   disjuncts (§4.4 records the stuck-discriminant counterexample that forces them).
6. **No dead code.** Every declaration is in `Green.lean`'s or `Capstone.lean`'s transitive import
   closure, or on a short tracked exception list in `doc/coverage.md` that must be **empty** at
   W5. No module receives a standing exemption.
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
| R1 | `Lower.constToFix` (the fix transport) is harder than the 600-line budget | medium | high | The hard half — `closeFix_substList_fixSubst` (`FixUnfold.lean:748`) and `FixUnfoldChain.eval` (`:830`, gated on `with_guarded_fix`, which `eraseFlags` satisfies) — is already proved. It is **W1** work with its own unit and its own acceptance test, so a failure surfaces in week one, not in W4. **Trigger:** if the transport is not proved by the end of W1, stop and re-scope: the fallback is to restrict the fragment to non-recursive declarations (which covers 0/5 benchmarks) and say so, i.e. the project has no viable deliverable — this is the one risk that can end it |
| R2 | `SpecEnv`'s antitone threading does not compose at some motive | medium | high | `SpecEnv.mono` is proved from `StateLe`, which every motive already concludes; W4 sequences the three environment-facing motives (4, 5, 6) **first** so a failure surfaces on day one of the wave |
| R3 | T5's ι arm needs `pats` ↔ `ElimBody` agreement, touching the `patsStrong` residual | high | medium | The known seam, declared in §1 of the spec. `IndInfo` states the agreement at declaration level, where a pats-carrying `VEnv.WF` is constructible today (21/22 clauses discharged in the Q2 probe); the nine "unconstructible" docstrings are false and are deleted in W0 |
| R4 | `VEnv.WF'.consts_origin` does not land upstream in time | medium | low | `SubsingletonElim` is a named class-**C** hypothesis with a ledger row until it does; criterion 7 explicitly permits this, and no other theorem depends on the derivation |
| R5 | The four redex arms' exactness against `visitCases`/`visitConstructor` is worse than believed (over-application placement, `mkAlt` binder order) | medium | medium | The relation is *name-free* and drops the `pre` args, so the two known sources of exactness trouble do not arise; the residual risk is spine shape, which W2's differential test measures directly (reconstruct the `Erases`-image from the run, check the emitted term is in `Lower Σ⁺` of it by a decidable checker, on all five programs). This is the check no candidate design proposed and the one that would have caught A's own T5 hole |
| R6 | `Erases.exists_of_trExprS` is harder than budgeted (`proj` case needs `TrProj`) | medium | low | The two hard cases are criterion 10's lemmas, required anyway; the `proj` case reuses `Erases.proj`'s deliberate `TrProj`-freedom. Fallback: make `hpre` a premise of `ErasesLB.cases` discharged in the bridge from `BridgeInv.mlc` |
| R7 | Reified `SourceTable` drifts from the real environment | medium | high | `SourceTableAdequate` is a `PrimSpec` field (so drift is a *stated* assumption, not a silent one) and `lake exe reify` + byte-diff runs in CI on every rung |
| R8 | Genuine mutual blocks are unexercised (0/50 emitted `FixDef`s are mutual) | medium | medium | `LowerBlock` is stated for lists, not singletons; W1's non-vacuity guard is a hand-built two-element block; the coverage table records that no benchmark exercises it |
| R9 | `by rfl` at G7 (2^3 through a 19-node peano tower and 27 constants) exceeds kernel budgets | medium | low | `lbEval` is fuel-indexed and structurally recursive; `set_option maxRecDepth` with a stated reason. Fallback recorded in the coverage table: evaluate a smaller closed rung and state that G7's arithmetic is checked by `green-check` externally |
| R10 | The 33-axiom fixture (criterion 9 × 15) is judged unacceptable at review | low | low | The ledger classifies all 29 non-standard names and distinguishes Lean-core `_native.bv_decide` from lean4lean's `sorryAx`; the alternative (field 4 at class **D**) is documented as a one-line switch that costs the development's only trust reduction |
| R11 | `hwt`/`hty` cannot be inhabited for a 39-declaration program (§2 F17) | medium | medium | W3's `TrWitness` unit routes lean4lean's checker; named fallback is class-**D** binders plus an amendment to criterion 13, recorded in the same commit |
| R12 | The relational conclusion is read as weaker than a functional one | low | low | §1.2 states the papers' posture; W6's functional refinement is additive and needs no restatement of T8, since a function equality implies relation membership |
| R13 | Shipping edit B1's under-erasure (review SI-1) is inside the fragment | medium | medium | Owned explicitly by `Supported` + `PrimSpec.oracle_sound`, and raised (§8.2); reverting B1 is not an option (criterion 9) |
