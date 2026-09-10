# Design B — relational passes, maximum reuse, minimum churn

**Angle.** Meet every acceptance criterion of `00-REFERENCE-SPEC.md` while restating as little
proved material as possible. The lever is a single decision: **the Lean-specific compilation
steps are specified as *relations* between the pruned λ□ term and the compiled λ□ term, each
carrying a forward-simulation theorem in the shape of `erases_correct`, not as *functions*
carrying an equation.** Everything else follows from that decision, and what follows is
consistently *less* restatement than the functional alternative.

**Status.** A design proposal against the normative spec. Where it asks the spec to be amended,
the amendment is stated in §2 with the measurement that forces it. Nothing here edits shipping
code (§8).

---

## 1. Overview

### 1.1 The one-paragraph thesis

`Erases` becomes exactly `[S Fig. 18]`: ten congruence rules over `Lean.Expr` plus `box`, indexed
by `(env : VEnv, Us, Δ : VLCtx)` and nothing else (T2). The four Lean-specific steps that the
current relation absorbed — constructor heads, `casesOn`→`.case`, mutual-block→`.fix`, literal
towers — move out, but they move out as **relations on λ□ indexed by the specification environment
`Σ⁺` alone**: `Lower` (term-level: `R_ctor` and `R_case` as two redex arms of one congruence),
`LowerFix` (declaration-level: `R_fix`), and `optimize` (already proved, a *function*, lifted into
the same interface). Each carries `correct : R Σ⁺ t t' → WcbvEval Σ⁺ flIn t v → ∃ v', R Σ⁺ v v' ∧
WcbvEval Σ flOut t' v'` — which is `optimize_correct`'s shape with the value existentially
quantified, i.e. literally `erases_correct`'s shape one layer down. T8 then concludes membership
in the composite relation, `∃ t₀, Erases env Us Δ e t₀ ∧ Lower Σ⁺ t₀ t`, and the composite has
**derived introduction lemmas whose signatures are the deleted `Erases` rules**, so the 4,641-line
18-motive induction is restated by a rename, not by a rewrite.

### 1.2 Why relations, and why that is following the papers rather than dodging them

1. **Letouzey's `◄` is a relation.** `[L Def. 10]` is `(Γ,t) ◄ (Γ₀,t₀)`, a four-clause *relation*
   between a source pair and a target pair; `E` (Def. 3) is a function whose graph is contained in
   it (Lemma 11). Sozeau's posture is identical: `erases` is the relation, `erase` the function,
   `erases_erase` the containment `[S §7.2]`. A theorem of the form "the shipping run's output is
   in the composite relation" is *the papers' own theorem shape*, not a weakened one.
2. **`[S §7.4]` sanctions the factorisation, and only gestures at the equation.** The paper says a
   fused eraser can be proved "*yields the same result*" as erasure-then-pass. That sentence is an
   invitation, not a requirement; the theorem the paper actually proves about its own two-stage
   pipeline is a simulation, and the deliverable (`erase_correct_firstorder`) never mentions
   syntactic equality with a fused function.
3. **The measurement says the equation costs more than it buys.** Probe Q1 establishes that exact
   functional equality is attainable, but only (a) against a `CompileTable` that is a function of
   the `Lean.Environment` rather than of `Σ` — a sixth `PrimSpec` obligation and a new parameter
   threaded through every pass, every motive and every `BridgeInv` field; (b) under two new
   `Supported` conjuncts; and (c) resting on a *Medium*-confidence claim that `Meta.inferType`
   preserves λ binder names and that instantiation does not rename ∀-binders, which is **not**
   machine-checked. Angle B pays none of (a), keeps only the one conjunct of (b) that is needed
   anyway (§2, Q1), and is independent of (c) by construction.
4. **The names in the target are a printer constraint, not an erasure fact.**
   `Erasure.fvar_to_name` (`Erasure.lean:245-252`) returns `.anon` for any name that is not
   ASCII-graphic, "*otherwise the λbox parser will complain*", and the current specification
   mirrors that character-class test inside itself (`ErasureContext.lean:248-251`,
   `nameToBinder`). That is the review's central complaint in miniature: the specification was
   written to match the implementation. Under a **name-free `Lower`** (§3.4), `Erases.lam` carries
   the source name, the ASCII filter is confined to the pass, and the constraint reappears where
   it belongs — as a conjunct of the output predicate `LBWfPeregrine` (§3.9).

### 1.3 How this differs from the current epicyclic `Erases`

The current relation's defect is not that it has fifteen rules; it is *what the extra rules are
indexed by* and *what they license*. Three precise differences:

| | current `Erases` (`Erases.lean:415`) | design B |
|---|---|---|
| index | `(env, Us, Γ : ErasureCtx, Δ)` — twelve columns of the eraser's own registry, with **no well-formedness predicate** relating `Γ` to any Lean environment | `Erases` is indexed by `(env, Us, Δ)`; `Lower`/`LowerFix` are indexed by `Σ⁺ : GlobalDeclarations` — **a λ□ object**, and the *specification* environment T3 relates to `env`. Neither mentions `ErasureCtx`, run state, fresh names, config or `Esrc` |
| what a rule may consult | `Γ.ctors`, `Γ.casesOns`, `Γ.casesDiscrPos`, `Γ.ctorFields`, `Γ.fixvars`, `Γ.natPeano`, `Γ.projs` — i.e. the run's answers | `Erases` consults `env` (via `TrExprS`/`Erasable`/`IndInfo`); `Lower` consults `Σ⁺` by `envLookup` only. `Lower`'s two redex arms have exactly one premise each about `Σ⁺` (`CtorDecl`, `ElimDecl`), both positive lookups |
| semantic guards | `IotaRelevant`, `IotaShape`, `SEnvConsistent`, `RecEnvConsistent`, `RecBlockAgreement` — premises that delete falsifying derivations and are **constructed nowhere** | **none.** No arm of `Lower`, `LowerFix` or `LowerEnv` carries an evaluation-shaped or relevance-shaped side condition. `ElimBody` (§3.5) is a *syntactic shape predicate on λ□*, decidable, with an explicit inhabitant per shape |

Two consequences worth stating because they are what makes the epicycle impossible to re-grow.
First, `Lower` is a relation *between two λ□ terms*: it cannot mention `Expr`, `VEnv`, `Erasable`
or the run even by accident, so a premise added "to make a case go through" is visible as a
premise about λ□ and is refutable by a two-term counterexample. Second, the composite's derived
introduction lemmas (§3.6) are **theorems**, so a rule that is not derivable simply cannot be
added: the only way to widen coverage is to widen `Lower`, and `Lower`'s correctness theorem is
target-side, class **A**, and independently checkable.

### 1.4 The three reuse levers, quantified

| Lever | What it saves | Evidence |
|---|---|---|
| composite relation with derived intro lemmas | the 18 motives' conclusions change by a rename (`Erases … Γ Δ e t` ⇝ `ErasesLB … Σ⁺ Δ e t`); motives 3/13/14/15/16/17 keep their proof text instead of being restated against a function equality | reuse-inventory §11.2-11.3: 8 of 18 motives are "pass-facing"; under a functional T8 all eight are rewritten, under B all eight are renamed |
| `Lower` indexed by `Σ⁺`, not a `CompileTable` | no sixth `PrimSpec` field, no new parameter in `BridgeInv`, passes stay lean4lean-free and class **A** | Q1 §3.1 forces the table only because it assumed `Σ = s'.gdecls`; §3.8 here uses `Σ⁺ ⊇ s'.gdecls` instead |
| `LowerFix` phrased through the existing `closeFix` | `FixMetatheory` + `FixUnfold` (1,184 lines, `closeFix_substList_fixSubst` at `FixUnfold.lean:748`) transfer with **no** const-keyed twin to re-prove | §3.7; the const→fvar renaming is exactly what today's `Erases.fixvar` arm proves, moved to λ□ |

---

## 2. Decisions

### 2.1 The eight open questions

**Q1 — does `LBCompile` reproduce `visitExpr` exactly?** *Decision: do not state it.* T8 concludes
membership in `Erases ⨟ Lower` (§4.4). Grounds: Q1's own verdict is "(a) for the whole chain,
against a compile table, on a fragment", and the three prerequisites (compile table, two
`Supported` conjuncts, unverified binder-name preservation) are all avoidable. `Supported` keeps
**one** of Q1's conjuncts — every minor of a `casesOn` application is a syntactic λ-chain of the
alt's field arity — because it is needed *relationally*, not for names: the shipping eraser
η-expands a non-λ minor **before** erasing it, so if the η-expanded minor `m x` is `Erasable` while
`m` is not (a minor returning a proof: `m : A → P` is not an arity, `m x : P` is a proof), the
emitted branch body is `.box` where the composite predicts an application. That conjunct already
exists in the tree as `IsLamTelescope` (`Bridge.lean:60`) and is already assumed by motive 18, so
it is zero churn. Q1's other two conjuncts (plain-`casesOn`, `name_occurs` agreement) are decided
separately: the first is kept for **criterion 11**, not for exactness; the second is **dropped** —
a relational `LowerFix` tolerates a `.fix` binder that the erased body never uses.
*Optional follow-up, explicitly out of the critical path:* a theorem `Lower Σ⁺ t₀ (lowerTerm E t₀)`
for the exactness fragment, which recovers `[S §7.4]`'s "same result" reading without any of the
above being load-bearing. Scheduled as W6, not required by any criterion.

**Q2 — where is the subsingleton criterion derived?** *Decision: derive it, upstream the
kernel-generic half, and restrict the index-determined case.* `SubsingletonElim env I` (§3.5) is
an environment predicate derived from `env.WF` through `VInductDecl.LargeElim`
(`Theory/Inductive.lean:226`) — the chain Q2 §2.3 lays out, whose only missing link is
`VEnv.WF'.consts_origin`, the constants-keyed twin of the existing `WF'.pats_origin`
(`InductiveParams.lean:93`). That lemma is kernel-generic and goes upstream by **N15** (ask filed
with `iotaRHS'_Generic`). Until it lands, `SubsingletonElim` is a single named class-**C**
hypothesis with one ledger row, as criterion 7 permits. On the `FieldInIndices` disjunct we take
Q2's recommended first cut: the criterion is `LargeElim` **minus** the index-determined disjunct,
which covers `False.rec`, `Eq.rec`, `And.rec`, `Iff.rec` and `Decidable`'s elimination, and puts
`Acc.rec`/`WellFounded.fix` on the restriction list as **N17**. *This requires amending
`00-REFERENCE-SPEC.md:213-221` and criterion 7*, and the amendment is not cosmetic: Q2 measures
`largeElimClause ``Acc = some (2,[1])`, i.e. `Acc.intro`'s field `x : α` is data, so MetaRocq's
`eval_iota_sing` — which substitutes `tBox` for *every* branch binder — computes a **wrong
program** for Lean's `Acc.rec`. The shipping eraser emits exactly that `.case`, so this is a
finding to raise (§8.2), not a semantics to repair. Lean's own code generator refuses `Acc.rec`,
so the restriction costs nothing that ships today.

**Q3 — `_unsafe_rec`: hypothesis or restriction?** *Decision: hypothesis, in the environment-
extension form (B) of the Q3 probe.* `envC := env` extended by one `VEnv.addDefEq` per compiler
body in the run's closure (§3.3); the capstone gains one class-**C** binder `hcomp : CompilerEnv
env envC e`, decidable and discharged per program; `ErasesDecl.defn` reads bodies off
`envC.defeqs`; T4's δ unfolds `envC`. The restriction alternative is deleted from the spec: it is
measured to cover **0 of 5** benchmarks (`Nat.add`/`mul`/`sub`/`pow` are all `_unsafe_rec`, so
Arith — T10's minimum — covers zero). One class-**E** ledger row records that the compiler and
kernel bodies agree only propositionally, totally for `partial def`.

**Q4 — do emitted eliminator declarations blow up the deliverable?** *Decision: no; adopt T3's
runtime library and prune.* Measured cost +4.5%…+13.6% un-pruned, **0% pruned**, and the emitted
`.ast` is unaffected because `Σ⁺` never reaches disk: `LowerEnv Σ⁺ Σ` (§3.8) carries a pruning
clause and `Σ = s'.gdecls` is the pruned image. Size is an N14 ledger row with the measured
`.peano`/hygiene split (49% of Quicksort is the peano tower), not a disclaimer.

**Q5 — parameters in constructor applications.** *Decision: the frontend keeps them; peregrine
drops them.* `remove_params_optimization` is pass 2 of `verified_lambdabox_pipeline`, run verbatim
by `untyped_transform_pipeline`, at `with_constructor_as_block = false`. `ErasesDecl.ctor`'s body
is `.construct iid k []` and parameters arrive through `Erases.app` (boxed, because a type
parameter is `Erasable`); measured 982/982 constructor occurrences at exactly
`ind_npars + cstr_nargs`, 0 under-applied. `LBWfPeregrine` (§3.9) states
`EWellformed(all_env_flags) + etaCtors + etaFix`, i.e. the *pipeline precondition*, not what
`peregrine validate` checks — criterion 12 is amended accordingly (§2.2).

**Q6 — is `FirstOrderInd` `[L Def. 14]` / `[L Def. 6]`?** *Decision: `fields` ≡ Def. 14; Def. 6 is
`firstorder_no_box`'s conclusion, not the definition; `[S §7.3]`'s `firstorder_ind` is cited as
origin and **not transcribed**, because its sort conjunct makes it `false` on `nat` (reproduced
three ways by `vm_compute`).* `FirstOrderInd` is typed over `VEnv.WF`'s declaration list (§3.10),
not over `VEnv` (which stores no inductive declarations); the `decide`able checker
`firstOrderIndB` lives on `Lean.Environment` and is connected by a fifth `PrimSpec` field.
Criterion 8 is amended to `Nat`, `Bool`, `Tree` (§2.2).

**Q7 — `Quot`.** *Decision: restrict, do not support.* New **N16**: no `Quot`/`Quot.mk`/
`Quot.lift`/`Quot.ind` in a computationally relevant position, as a `Supported` conjunct over the
dependency closure. `Quot.sound` is *not* excluded — it is `Prop`-typed, hence boxed, hence
covered by `ErasableAxioms`. `ErasesDecl.quot` is deleted from T3 (it promised an `ElimBody`
obligation nothing constructs or consumes). The `Quot.ind` theory/checker divergence in lean4lean
is an upstream note, not a row here (N15).

**Q8 — mechanical comparison of `Erases` to MetaRocq's `erases`.** *Decision: ship the two tables,
drop the Rocq transport, say so once.* `doc/rework/rules-Erases.md` (rule-by-rule against
`[S Fig. 18]`, criterion 3) and `doc/rework/rules-Lower.md` (`Lower`/`LowerFix`/`optimize` against
MetaRocq's `iota_red`, `fixSubst`, `optimize`) are tracked next to the definitions. A Rocq-side
transport reaching the relation is **out of scope**: `grep -rn Erases rocq/` is empty today and
scoping it would add a second formalisation of `Erases` to keep in sync — precisely the failure
mode CLAUDE.md warns about across repos. One ledger row (class **E**).

### 2.2 Amendments this design asks of the reference spec

Each is forced by a measurement, and each is small.

| # | Spec text | Amendment | Forced by |
|---|---|---|---|
| A1 | §2 T3, lines 213-221 ("verbatim `[L §3.3]`… `Acc.rec` … **inside** the fragment") | Lean's criterion admits index-determined data fields (`FieldInIndices`); `Acc.rec` is **outside** the first-cut fragment (N17), `Eq.rec`/`And.rec`/`Iff.rec`/`False.rec`/`Decidable` are inside | Q2 §4, `Tests/IotaShape.lean:578` |
| A2 | §7 criterion 7 ("`Acc.rec`…demonstrably inside the fragment either way") | replace `Acc.rec` with `Eq.rec`/`And.rec`/`Iff.rec`/`Decidable`; `Acc.rec` becomes N17 + a raised finding | same |
| A3 | §2 T8 conclusion `t = LBCompile.term s'.gdecls t₀` | `∃ Σ⁺ t₀, Erases … t₀ ∧ Lower Σ⁺ t₀ t ∧ ErasesEnv envC Σ⁺ t₀ ∧ LowerEnv Σ⁺ s'.gdecls` | Q4 F5 (the run registers **0** eliminator declarations in all five `.ast`), Q1 §3.2 |
| A4 | §2 T3 `ErasesDecl.defn`'s premise `env.constants c = some ⟨_, some body⟩` | `VConstant` carries no body at the pin; read the defining equation from `envC.defeqs` | Q3 §1.5, `Theory/VEnv.lean:6-21` |
| A5 | §5 N8 ("…or a restriction to declarations where the two coincide") | delete the restriction alternative | Q3 §1.4(A): covers 0/5 |
| A6 | §7 criterion 8 (`List Nat`, `Nat × Nat`) | `Nat`, `Bool`, `Tree` | Q6.4: `List`/`Prod` are outside Def. 14 and outside `firstorder_ind`; all five benchmarks return `Nat` |
| A7 | §7 criterion 12 ("matching what `peregrine validate` checks") | "matching `untyped_transform_pipeline`'s precondition"; `validate` omits η | Q5 §2.3 |
| A8 | §2 T6's `LBCompile := optimize ∘ …` used both as T8's factor and as T9's post-pass | split: `Lower` (T8's factor) and `optimize` (T9's flag-discharger). Removes an unstated idempotence obligation | Q1 §3.2 |
| A9 | §5 N-list | add **N16** (`Quot`), **N17** (subsingleton inductives with an index-determined field: `Acc`, `WellFounded.fix`) | Q7.5, Q2 §4 |
| A10 | §2 T8's four `PrimSpec` fields | five: add `ind_adequate` (inductive-declaration adequacy) for `firstOrderIndB` | Q6.6, Q4-Q6-Q7 F8 |

### 2.3 Every acceptance criterion, and how it is met

**Structure.**

1. *`Erases` has exactly ten rules; signature mentions `VEnv`, `List Name`, `VLCtx`, `Expr`,
   `LBTerm` and nothing else; no `ErasureCtx`.* Met by §3.2 verbatim. `ErasureContext.lean` is
   deleted (§5), so the grep is empty by construction, not by discipline.
2. *No rule produces `.construct`, `.case` or `.fix`.* Met: those three nodes appear only in
   `Lower`'s two redex arms, in `LowerFix`, and in `ErasesDecl.ctor`/`.elim` — none of which is a
   rule of `Erases`. Enforced by a CI grep over `Erases.lean` for `\.construct|\.case|\.fix`.
3. *Rule-by-rule table tracked next to `Erases.lean`.* `doc/rework/rules-Erases.md`, W1
   deliverable, plus `rules-Lower.md` (Q8).
4. *Exactly one `SEval*`, one environment relation, one hypothesis bundle, one ledger.* Met:
   `SEval` (§3.3), `ErasesEnv` (§3.8), `PrimSpec` (§3.11), `test/Ledger.lean` (§3.13). CI greps
   `inductive SEval`, `structure .*Hyps`, `#print axioms`.
5. *Every pass has an `optimize_correct`-shaped theorem and a non-vacuity guard, and the
   composition exists.* Met by §4.3: `lower_correct`, `lowerFix_correct`, `LBOptimize_correct`
   (generalised), each with a guard in the style of `Optimize.lean:1066`, composed in
   `lbcompile_correct`. The shape is `optimize_correct`'s with the value existentially quantified
   — which is what a relation forces and what `erases_correct` already does one layer up.

**Content.**

6. *T5 has exactly five hypotheses, none named `Supported`/`Relevant`/`Iota*`/`*Consistent`/
   `*Hyps`.* Met by §4.2 literally: `henv`, `hwt`, `hev`, `her`, `hΣ`.
7. *`Subsingleton` appears exactly once, in T3, derived — or one named class-**C** hypothesis with
   a ledger row — and the named recursors are demonstrably inside the fragment.* Met as amended
   (A1/A2): `SubsingletonElim` is stated once in `ElimBody.lean`, derived when `consts_origin`
   lands upstream, class-**C** with a ledger row until then, and W2's acceptance test exhibits
   `Eq.rec`, `And.rec`, `Iff.rec`, `False.rec` and `Decidable.casesOn` inside the fragment by a
   checked `ElimBody` instance each.
8. *`FirstOrderInd` decidable, `decide`s true on the listed types.* Met as amended (A6) on `Nat`,
   `Bool`, `VerifyBench/BinaryTrees`' `Tree`, via `firstOrderIndB` (§3.10).
9. *`OracleDischarge` in the capstone's import closure; `oracle_sound` discharged.* Met: the
   bundle is `PrimSpec` and its field 4 is *proved* from `Oracle.kernel_isErasable_sound`
   (§3.11), which `Capstone.lean` imports. Cost measured and accepted: 33 axioms, two of them
   `_native.bv_decide` from Lean core; the fixture (criterion 15) accommodates them and the ledger
   carries the 29-name row.
10. *`Erases.sort_erasable` / `Erases.forallE_erasable` exist; the other fourteen panic sites
    enumerated.* Met, and load-bearing rather than decorative: they are the two hard cases of
    `Erases.exists_of_trExprS` (§4.1), which the composite needs in order to erase the *dropped*
    arguments of a `casesOn` spine. The panic table is `doc/rework/panics.md`, one row per site
    with the premise that excludes it.
11. *`Supported` decidable, `decide`s on the five programs, sparse-`casesOn` visible in it.* Met by
    §3.12: `Supported.casesApp` requires the head to be `I.casesOn` for an inductive `I` in the
    fragment with a **plain** `CasesInfo` (no `CasesAltInfo.default`, no `hasSideCondition`), and
    the accompanying `supportedB` returns `false` on `Quicksort`'s `quicksort_fuel._sparseCasesOn_1`.
    The exclusion is one readable conjunct in the predicate a reader audits, in the same file.
12. *Capstone's conclusion contains `LBWfPeregrine`.* Met as amended (A7) by §3.9.

**Non-vacuity.**

13. *`arith_covered` elaborates, every T9 hypothesis inhabited by a checked term.* W5's acceptance
    test. The added binder `hcomp` (Q3) is four `TrExprS`+`HasType` checks, measured to hold.
14. *Per-program coverage table, number not zero.* `VerifyBench/STATUS.md` becomes the tracked
    table; Arith is fully covered, and the four others are covered or excluded by a *named*
    conjunct (Fannkuch by N2's `Eq.rec` realizer + `partial def` under `envC`; Quicksort by
    `Supported`'s plain-`casesOn` conjunct — the honest record of a shipping bug).

**Trust.**

15. *`#print axioms` on T5, T6, T8, T9 matches a committed fixture; T6's passes print class **A**.*
    Met: `Lower`/`LowerFix`/`optimize` mention neither `Expr` nor lean4lean, so their correctness
    theorems cannot inherit `sorryAx`; W2's acceptance test asserts exactly
    `[propext, Classical.choice, Quot.sound]` for each.
16. *Every `sorryAx` root named with `file:line` at the pinned rev, fork-authored distinguished.*
    Met by `test/Ledger.lean` + `doc/rework/ledger-fixture.txt`; `VEnv.WF.patsStrong`
    (`EnvLemmas.lean:334`) is listed as **fork-authored**, which no current document does.
17. *No `sorry`, no `axiom`; `PrimSpec` is a structure; class-**C** hypotheses are binders.* Met by
    construction; CI grep.

**Hygiene.**

18-20. *Comment fraction < 20%; no slice tags/hashes/dates; every backticked identifier resolves;
    no declarations outside the import closure.* Met by §9 and by the deletions in §5 (the
    consumer-free modules `Optimize`, `Export/EvalT`, `ShippingCorrect`, `OracleDischarge`,
    `Semantics` aggregate — 1,733 lines measured outside `ColdStart.lean`'s closure — are either
    wired in or deleted).
21. *No `Lean4Lean`-namespace declaration in this repository.* Met without an exception clause:
    of `CheckerAdequacy.lean`'s eight `Lean4Lean.TypeChecker` declarations, seven are
    kernel-generic (`VContext.ofMLCtx` and its three `@[simp]` projections, `VState.WF.initial`,
    `M.WF.run'`, `kernelNGen`) and go upstream with the Q2 ask; the eighth,
    `kernel_isErasable_sound`, is *about* `LeanToLambdaBox.isErasable` and is restated as
    `LeanToLambdaBox.Oracle.kernel_isErasable_sound`. Cost: one rename plus one upstream PR.
22. *Verified eraser on the branch consumers pin; CI builds it; committed lakefile pins the
    measured rev.* W5: merge `dev/verify` into `main` behind the `20ec229` pin, switch
    `.github/workflows/build.yml` from `branches: ['main']`-only, commit `lakefile.toml`'s pin.

---

## 3. Core definitions

All signatures are written against the pinned lean4lean (rev `20ec229`) and the shipping
`LeanToLambdaBox/Basic.lean` at `dev/verify`. `GlobalDeclarations = List (Kername × GlobalDecl)`
(`Basic.lean:190`); `envLookup` is `Semantics/Substitution.lean:35`.

### 3.1 `LBTerm` — unchanged

**No change.** Every node T1 needs exists (`Basic.lean:90-104`), branches already carry
`List BinderName`, there is no `tCoFix`, `.fvar` and `.prim` are present. This is a hard
requirement of the angle: `Basic.lean` is shipping code (§8).

### 3.2 `Erases` — T2, ten rules

```lean
/-- `[S Fig. 18]` transposed to `Lean.Expr`: `TrExprS` with `VExpr` replaced by `LBTerm`,
`sort`/`forallE` absorbed into `box`, and `box` added. Ten rules; no side condition; no
`ErasureCtx`. -/
inductive Erases (env : VEnv) (Us : List Name) : VLCtx → Expr → LBTerm → Prop
  | box   {Δ e ve} (htr : TrExprS env Us Δ e ve)
          (her : Erasable env Us.length Δ.toCtx ve) : Erases env Us Δ e .box
  | bvar  {Δ i} : Erases env Us Δ (.bvar i) (.bvar i)
  | fvar  {Δ x} : Erases env Us Δ (.fvar x) (.fvar x)
  | const {Δ c us ci} (h : env.constants c = some ci) :
          Erases env Us Δ (.const c us) (.const (toKername c))
  | app   {Δ f f' a a'} (hf : Erases env Us Δ f f') (ha : Erases env Us Δ a a') :
          Erases env Us Δ (.app f a) (.app f' a')
  | lam   {Δ n ty bi b b'} {ty' : VExpr} (hty : TrExprS env Us Δ ty ty')
          (hb : Erases env Us ((none, .vlam ty') :: Δ) b b') :
          Erases env Us Δ (.lam n ty b bi) (.lambda (.named n.toString) b')
  | letE  {Δ n ty nd v v' b b'} {ty' val' : VExpr}
          (hty : TrExprS env Us Δ ty ty') (hval : TrExprS env Us Δ v val')
          (hv : Erases env Us Δ v v') (hb : Erases env Us ((none, .vlet ty' val') :: Δ) b b') :
          Erases env Us Δ (.letE n ty v b nd) (.letIn (.named n.toString) v' b')
  | proj  {Δ S i e t iid np nf} (hs : IndInfo env S iid np [nf]) (hi : i < nf)
          (hd : Erases env Us Δ e t) : Erases env Us Δ (.proj S i e) (.proj ⟨iid, np, i⟩ t)
  | lit   {Δ l t} (hcl : env.ContainsLits l) (h : Erases env Us Δ l.toConstructor t) :
          Erases env Us Δ (.lit l) t
  | mdata {Δ d e t} (h : Erases env Us Δ e t) : Erases env Us Δ (.mdata d e) t
```

Three deltas from the spec's draft, each grounded. (i) `const` no longer takes a `Kername`
parameter with a `Γ.constants n = kn` premise; the naming convention `toKername` (`Basic.lean:34`)
is a *function*, and making it one removes `BridgeInv.knames`/`consts` in favour of the existing
`CanonicalConstants` (`ErasureRun.lean:1482`). (ii) `proj` keys its `(iid, np, nf)` on `IndInfo`
(§3.5), the environment predicate, not on `Γ.projs`/`Γ.ctorFields`; it still carries **no**
`TrExprS` premise, for the reason the current docstring gives correctly (`TrProj.uniq` yields
`IsDefEqU`, not equality). (iii) `lam`/`letE` record the **source** name, not
`nameToBinder`'s ASCII-filtered image: the filter is a printer constraint (§1.2(4)) and moves to
`Lower`'s name-freedom plus `LBWfPeregrine.asciiNames`.

Metatheory carried from `Erases.lean`/`ErasesAbstract.lean`/`ErasesStrengthen.lean`/
`ErasesUniform.lean` with statements unchanged except for dropping the `Γ` index: `erases_shift`,
`erases_subst`, `Erases.abstract`, `Erases.uninstantiateN`, `Erases.thin_vlet`,
`erases_weakFV*`, `erases_uniform_*`. Nine of fifteen arms survive per lemma; six die with their
rules.

**New, and load-bearing:**

```lean
/-- Totality: every translatable term has an erasure. `[L Def. 3]`'s `E` is total on well-typed
terms; the two hard cases are `sort` and `forallE`, which have no congruence rule and are always
`Erasable` (criterion 10). Consumed by the composite's `elim` arm, which must erase the
arguments the `.case` node drops. -/
theorem Erases.exists_of_trExprS (henv : env.WF) {Δ e ve} (hΔ : VLCtx.WF env Us.length Δ)
    (h : TrExprS env Us Δ e ve) : ∃ t, Erases env Us Δ e t

theorem Erases.sort_erasable    (henv : env.WF) : TrExprS env Us Δ (.sort u) ve →
    Erasable env Us.length Δ.toCtx ve
theorem Erases.forallE_erasable (henv : env.WF) : TrExprS env Us Δ (.forallE n A B bi) ve →
    Erasable env Us.length Δ.toCtx ve
```

### 3.3 `SEval` + `SEvalFlags` — T4, one relation

```lean
structure SEvalFlags where
  beta, delta, zeta, iota, proj, lit : Bool
  deriving DecidableEq
instance : LE SEvalFlags := ⟨fun a b => (a.beta → b.beta) ∧ … ⟩

/-- The one source evaluation: weak call-by-value big-step over `Lean.Expr`, parameterised by
which reductions are enabled `[S §5.6]`. δ reads `env.defeqs`; ι reads `env.pats`. -/
inductive SEval (env : VEnv) (Us : List Name) (fl : SEvalFlags) : VLCtx → Expr → Expr → Prop

theorem SEval.mono  (h : fl ≤ fl') : SEval env Us fl Δ e v → SEval env Us fl' Δ e v
theorem SEval.le    (h : env ≤ env') : SEval env Us fl Δ e v → SEval env' Us fl Δ e v
theorem SEval.defeq (henv : env.WF) (hΔ : VLCtx.WF env Us.length Δ)
    (htr : TrExprS env Us Δ e ve) (hev : SEval env Us fl Δ e v) :
    ∃ vv, TrExprS env Us Δ v vv ∧ env.IsDefEqU Us.length Δ.toCtx ve vv
```

`SEval.defeq` is `SubjectReduction{,Full,Iota}`'s content unified: the β/ζ/δ arms are written once
(today three times, two byte-identical at `SubjectReductionFull.lean:398-430` =
`SubjectReductionIota.lean:157-189`), the ι and proj arms come from the third, and
`SEvalβζδ_defeq_spine`'s abstract-`P` schema (`SubjectReductionFull.lean:309`) is the template that
makes one proof serve every flag setting. `SEval.le` is new (three lines) and is what lets the
capstone run at `envC` while `Erases`/`Erasable`/`TrExprS` stay at `env` (Q3).

```lean
/-- Q3: the environment the compiler compiles. `env` extended by one defining equation per
declaration whose `_unsafe_rec` body the eraser reads. Decidable per program. -/
structure CompilerEnv (env envC : VEnv) (e : Expr) : Prop where
  le    : env ≤ envC
  defs  : ∀ df, envC.defeqs df → env.defeqs df ∨ ∃ c, CompilerBodyOf env c df
  typed : ∀ df, envC.defeqs df → env.HasType df.uvars [] df.lhs df.type ∧
                                 env.HasType df.uvars [] df.rhs df.type
  pats  : envC.pats = env.pats
```

### 3.4 `Lower` — the term-level pass relation (`R_ctor`, `R_case`, `R_lit`)

```lean
/-- The Lean-specific λ□→λ□ compilation, as a relation. Indexed by the specification
environment `Σ` and by nothing else: no source term, no `VEnv`, no run state, no fresh names.
Free on `BinderName`s (`WcbvEval` reads only their *lengths*: `Eval.lean:143-153,171`), which
is what makes it independent of `fvar_to_name`'s printer-driven ASCII filter. -/
inductive Lower (Σ : GlobalDeclarations) : LBTerm → LBTerm → Prop
  -- congruence (10 arms)
  | box                                  : Lower Σ .box .box
  | bvar (i)                             : Lower Σ (.bvar i) (.bvar i)
  | fvar (x)                             : Lower Σ (.fvar x) (.fvar x)
  | prim (p)                             : Lower Σ (.prim p) (.prim p)
  | const {kn} (h : ¬ RuntimeKey Σ kn)   : Lower Σ (.const kn) (.const kn)
  | lambda {n n' b b'} (h : Lower Σ b b') : Lower Σ (.lambda n b) (.lambda n' b')
  | letIn  {n n' v v' b b'} (hv : Lower Σ v v') (hb : Lower Σ b b') :
      Lower Σ (.letIn n v b) (.letIn n' v' b')
  | app    {f f' a a'} (hf : Lower Σ f f') (ha : Lower Σ a a') :
      Lower Σ (.app f a) (.app f' a')
  | proj   {p e e'} (h : Lower Σ e e') : Lower Σ (.proj p e) (.proj p e')
  | construct {iid k args args'} (h : List.Forall₂ (Lower Σ) args args') :
      Lower Σ (.construct iid k args) (.construct iid k args')
  | «case» {ip d d' alts alts'} (hd : Lower Σ d d')
      (ha : List.Forall₂ (fun a a' => a.1.length = a'.1.length ∧ Lower Σ a.2 a'.2) alts alts') :
      Lower Σ (.case ip d alts) (.case ip d' alts')
  | «fix» {defs defs' i}
      (h : List.Forall₂ (fun d d' => d.principalArgIdx = d'.principalArgIdx ∧
                                     Lower Σ d.body d'.body) defs defs') :
      Lower Σ (.fix defs i) (.fix defs' i)
  -- redex arms: the two Lean-specific steps
  /-- `R_ctor`: a constructor *constant* becomes a `.construct` head. Applied form: the
      arguments arrive by `.app` through the congruence, so no arity premise is needed and
      inductive parameters are kept (Q5). -/
  | ctorHead {kn iid k} (h : CtorDecl Σ kn iid k) :
      Lower Σ (.const kn) (.construct iid k [])
  /-- `R_case`: a saturated eliminator application becomes a `.case` node. `dp` args before
      the discriminant (parameters, motive) are *dropped* — sound for a forward simulation,
      and exactly what MetaRocq's own expansion does. Over-application rides outside the
      node, matching `visitCases`'s `args[casesInfo.arity:]` loop (`Erasure.lean:832`). -/
  | elim {kn iid np dp nfs pre disc alts args extra extra'}
      (hE    : ElimDecl Σ kn iid np dp nfs)
      (hlen  : pre.length = dp)
      (hargs : args = pre ++ disc :: minors)
      (hmin  : List.Forall₃ (LowerAlt Σ) nfs minors alts)
      (hd    : Lower Σ disc disc')
      (hx    : List.Forall₂ (Lower Σ) extra extra') :
      Lower Σ (LBTerm.mkApps (.const kn) (args ++ extra))
              (LBTerm.mkApps (.case (iid, np) disc' alts) extra')

/-- A branch: peel the minor's λ-chain. Names are free; the *number* of them is the field
    arity, which is what `WcbvEval.iota` reads. -/
inductive LowerAlt (Σ : GlobalDeclarations) : Nat → LBTerm → (List BinderName × LBTerm) → Prop
  | done {m b}       (h : Lower Σ m b)         : LowerAlt Σ 0 m ([], b)
  | lam  {nf n n' m alt} (h : LowerAlt Σ nf m alt) :
      LowerAlt Σ (nf+1) (.lambda n m) (n' :: alt.1, alt.2)
```

`List.Forall₂` is in the project's import closure (used at `IotaPattern.lean:132`); `Forall₃` is
**not** — it is a three-list zip to be defined once in `Lower.lean` (six lines), or replaced by the
indexed form `∀ i (h : i < nfs.length), LowerAlt Σ nfs[i] minors[i] alts[i]` that the current
motives already use.

`R_lit` is **the identity relation on this path** and is named for the record: at
`cfg.nat = .peano` the literal work is entirely `Erases.lit` (the kernel unfolding, mirroring
`TrExprS.lit`) plus `ctorHead` on each `Nat.succ`/`Nat.zero` head, so no λ□ pass is involved. The
slot is kept so that **N3**'s machine-`Nat` lowering is a *pass to be added* — a data refinement
with an overflow side condition — rather than an omission.

Environment queries, the only things `Lower` may consult, all by `envLookup`:

```lean
def CtorDecl (Σ : GlobalDeclarations) (kn : Kername) (iid : InductiveId) (k : Nat) : Prop :=
  envLookup Σ kn = some (.constantDecl ⟨some (.construct iid k [])⟩)
def ElimDecl (Σ : GlobalDeclarations) (kn : Kername)
    (iid : InductiveId) (np dp : Nat) (nfs : List Nat) : Prop :=
  ∃ body, envLookup Σ kn = some (.constantDecl ⟨some body⟩) ∧ ElimBody iid np dp nfs body
def RuntimeKey (Σ : GlobalDeclarations) (kn : Kername) : Prop :=
  (∃ iid k, CtorDecl Σ kn iid k) ∨ (∃ iid np dp nfs, ElimDecl Σ kn iid np dp nfs)
```

`RuntimeKey` is the negative premise on the `const` congruence arm; it is what stops `Lower` from
leaving a `.const` behind that the *emitted* environment (which contains no ctor or eliminator
declarations — measured, Q1 §1) could not resolve.

### 3.5 `ElimBody`, `IndInfo`, `SubsingletonElim` — the runtime library's shape

```lean
/-- The λ□ body of an eliminator constant, as a *syntactic* shape on λ□ — decidable, with a
    constructor per shape, no semantic side condition. `dp` binders precede the discriminant
    (parameters, motive, and for `rec` the minors), `nfs` is the per-constructor field arity. -/
inductive ElimBody : InductiveId → Nat → Nat → List Nat → LBTerm → Prop
  /-- Non-recursive: `λ x₁…x_dp d ↦ case d of | fields ↦ minor_k fields`. -/
  | cases {iid np dp nfs ns} (hlen : ns.length = dp) :
      ElimBody iid np dp nfs (mkLambdas ns (.case (iid, np) (.bvar 0) (elimAlts dp nfs)))
  /-- Recursive: the same, wrapped in a one-element `.fix` whose self-reference feeds the
      recursive minors. -/
  | rec  {iid np dp nfs ns} … :
      ElimBody iid np dp nfs (mkLambdas ns (.fix [⟨.anon, elimFixBody iid np dp nfs, dp⟩] 0))
  /-- Subsingleton (`[S §7.1]` amendment (2), `[L §3.3]`): a single branch applied to boxes,
      no `.case` node. Admitted only under `SubsingletonElim`, i.e. `LargeElim` **without**
      the index-determined disjunct (N17). -/
  | sing {iid np dp nf ns} (hlen : ns.length = dp) :
      ElimBody iid np dp [nf] (mkLambdas ns (mkApps (.bvar minorIdx) (List.replicate nf .box)))

/-- `env`'s inductive block data for `I`, read off `VEnv.WF`'s declaration list (`VEnv` itself
    stores no inductive declarations — `Theory/VEnv.lean:17-23`), in λ□ coordinates. -/
structure IndInfo (env : VEnv) (I : Name) (iid : InductiveId) (np : Nat) (nfs : List Nat) : Prop

/-- Fig. 18's side condition, as an *environment* predicate (there is no case node in
    `Lean.Expr`, so it has no term-level home). Derived from `env.WF` via
    `VInductDecl.LargeElim` (`Theory/Inductive.lean:226`) once `VEnv.WF'.consts_origin` lands
    upstream; a named class-**C** hypothesis with a ledger row until then. -/
def SubsingletonElim (env : VEnv) (I : Name) : Prop
```

### 3.6 `ErasesLB` — the composite, and the derived introduction lemmas

```lean
/-- What the shipping eraser's output satisfies: erasure followed by lowering. -/
def ErasesLB (env : VEnv) (Us : List Name) (Σ : GlobalDeclarations)
    (Δ : VLCtx) (e : Expr) (t : LBTerm) : Prop :=
  ∃ t₀, Erases env Us Δ e t₀ ∧ Lower Σ t₀ t
```

The reuse engine: each deleted `Erases` rule reappears as a **theorem** with the same argument
shape, so the 18 motives' proof scripts change by a name.

```lean
theorem ErasesLB.app  : ErasesLB env Us Σ Δ f f' → ErasesLB env Us Σ Δ a a' →
                        ErasesLB env Us Σ Δ (.app f a) (.app f' a')
theorem ErasesLB.box  : TrExprS env Us Δ e ve → Erasable env Us.length Δ.toCtx ve →
                        ErasesLB env Us Σ Δ e .box
theorem ErasesLB.ctor_head {cn us iid k} (hc : CtorDecl Σ (toKername cn) iid k)
    (h : env.constants cn = some ci) :
    ErasesLB env Us Σ Δ (.const cn us) (.construct iid k [])
theorem ErasesLB.ctor {cn us iid k args args'} (hc : CtorDecl Σ (toKername cn) iid k)
    (hargs : List.Forall₂ (ErasesLB env Us Σ Δ) args args') :
    ErasesLB env Us Σ Δ (args.foldl Expr.app (.const cn us))
                        (LBTerm.mkApps (.construct iid k []) args')
theorem ErasesLB.cases {con us iid np dp nfs args disc alts} (hE : ElimDecl Σ (toKername con) …)
    (henv : env.WF) (hΔ : VLCtx.WF env Us.length Δ)
    (hpre : ∀ a ∈ args.take dp, ∃ ve, TrExprS env Us Δ a ve)    -- dropped args: totality
    (hd : ErasesLB env Us Σ Δ (args.get dp) disc)
    (hm : List.Forall₃ (ErasesLBAlt env Us Σ Δ) nfs (args.drop (dp+1)) alts) :
    ErasesLB env Us Σ Δ (args.foldl Expr.app (.const con us)) (.case (iid, np) disc alts)
```

`ErasesLB.cases`'s `hpre` is the one genuinely new premise, and it is discharged by
`Erases.exists_of_trExprS` (§3.2) from the `TrExprS` the motive already carries — the arguments a
`.case` node drops still need an erasure image in `t₀`, because `Erases` is a congruence over the
whole spine. This is where criterion 10's two lemmas earn their place.

Transport for the composite factors: `erases_subst` (carried) + `Lower`'s own commutation lemmas,
which are λ□-only, class **A**, and mirror `Optimize.lean`'s existing `LBOptimize_subst_comm`
(`:164`), `LBOptimize_shift_comm` (`:160`), `LBOptimize_substList` (`:173`).

### 3.7 `LowerFix` — `R_fix`, at declaration level

The subject term never contains a `.fix`: `visitExpr_shape_all` (`ColdStartInduction.lean:1104`)
proves `NoFix t` **unconditionally and panic-tolerantly**, and all 50 emitted `FixDef`s live in
declaration bodies (Q1 §1). So `R_fix` is an environment-level relation, and `Lower` needs no fix
redex arm.

```lean
/-- Replace `.const kns[j]` by `.fvar ids[j]`; the λ□-only residue of today's `Erases.fixvar`,
    with the source side removed. -/
inductive ConstToFVar (kns : List Kername) (ids : List FVarId) : LBTerm → LBTerm → Prop

/-- The `Kername`-keyed fix closure, phrased through the *existing* `closeFix` so that
    `closeFix_substList_fixSubst` (`FixUnfold.lean:748`) applies verbatim and no const-keyed
    twin of `FixUnfold`'s 41 theorems has to be re-proved. -/
def CloseConst (kns : List Kername) (t u : LBTerm) : Prop :=
  ∃ ids t', ids.Nodup ∧ ids.length = kns.length ∧ (∀ x ∈ ids, ¬ hasFVar x t) ∧
    ConstToFVar kns ids t t' ∧ u = closeFix ids 0 t'

/-- `R_fix`: the specification declares each member of a mutual block by its pruned body, with
    recursive calls as `.const`; the emitted environment declares all of them as one `.fix`. -/
def LowerFix (Σ : GlobalDeclarations) (kns : List Kername)
    (b₀ : List LBTerm) (defs : List (@FixDef LBTerm)) : Prop :=
  defs.length = kns.length ∧ b₀.length = kns.length ∧
  ∀ j (hj : j < kns.length), ∃ b, Lower Σ b₀[j] b ∧ CloseConst kns b (defs[j].body)
```

Note what is *not* required: that the fix binder actually occurs. `visitMutual` decides
recursiveness by `name_occurs` on the **source** body (`Erasure.lean:878`); if erasure removes the
only self-reference, the emitted `.fix` has an unused binder and `LowerFix` still holds. The
functional formulation would need a `Supported` conjunct asserting that `name_occurs` agrees with
λ□ self-reference (Q1 §3.4); the relational one does not.

### 3.8 `ErasesDecl` / `ErasesEnv` / `LowerEnv` — T3 and the two-layer environment

```lean
/-- One Lean declaration's λ□ image. `env` types; `envC` supplies bodies (Q3). -/
inductive ErasesDecl (env envC : VEnv) : Kername → GlobalDecl → Prop
  | defn {c us body b₀} (hd : envC.defeqs ⟨us.length, .const c (levelsOf us), body, ty⟩)
         (hb : Erases envC us [] body b₀) :
         ErasesDecl (toKername c) (.constantDecl ⟨some b₀⟩)
  | ax   {c ci} (h : env.constants c = some ci) (hno : ∀ df, ¬ CompilerBodyOf envC c df) :
         ErasesDecl (toKername c) (.constantDecl ⟨none⟩)
  | ind  {I iid np nfs} (h : IndInfo env I iid np nfs) :
         ErasesDecl iid.mutualBlockName (.inductiveDecl (indBodyOf env I))
  | ctor {c I iid k} (h : CtorOf env c I k) (hi : IndInfo env I iid np nfs) :
         ErasesDecl (toKername c) (.constantDecl ⟨some (.construct iid k [])⟩)
  /-- `I.rec` **and** `I.casesOn`: both are given an `ElimBody` declaration. `casesOn`'s Lean
      body is `I.rec` applied, so the two are δ-equal and this is `casesOn`'s δ-normal form;
      the shortcut removes one δ step from every case redex and is named in the §3.3 table. -/
  | elim {I kn iid np dp nfs body} (hi : IndInfo env I iid np nfs) (helim : ElimOf env I kn)
         (hs : nfs.length = 1 → SubsingletonElim env I) (hb : ElimBody iid np dp nfs body) :
         ErasesDecl kn (.constantDecl ⟨some body⟩)

/-- `erases_deps` `[S §7.4]`: dependency-selective, bottom-up. The **only** environment
    relation between `VEnv` and λ□. -/
inductive ErasesEnv (env envC : VEnv) : GlobalDeclarations → LBTerm → Prop

/-- λ□→λ□: the emitted environment is the lowered, pruned image of the specification's.
    Class **A** (no `Expr`, no `VEnv`). -/
structure LowerEnv (Σ⁺ Σ : GlobalDeclarations) : Prop where
  keys    : (Σ.map Prod.fst).Nodup
  defs    : ∀ kn b₀, envLookup Σ⁺ kn = some (.constantDecl ⟨some b₀⟩) →
              envLookup Σ kn = some (.constantDecl ⟨some b⟩) →
              Lower Σ⁺ b₀ b ∨ ∃ kns bs, LowerFix Σ⁺ kns bs defsOf ∧ b = .fix defsOf (indexOf kn kns)
  axioms  : ∀ kn, envLookup Σ⁺ kn = some (.constantDecl ⟨none⟩) →
              envLookup Σ kn = some (.constantDecl ⟨none⟩) ∨ envLookup Σ kn = none
  inds    : ∀ kn d, envLookup Σ⁺ kn = some (.inductiveDecl d) → envLookup Σ kn = some (.inductiveDecl d)
  /-- pruning: `Σ` keeps exactly what the emitted program can reach. Q4: this is why the
      runtime library costs 0% on disk. -/
  prune   : ∀ kn, envLookup Σ kn ≠ none → Reachable Σ kn
  closed  : ClosedEnv Σ
```

**The registration bridge, and why `Σ⁺` is threaded rather than existentially guessed.** The
bridge's motives quantify `Σ⁺` *universally* under a monotone premise:

```lean
/-- `Σ⁺` is a specification environment for the run state `s`: every constant `s` registered
    has its `ErasesDecl` image in `Σ⁺`, every inductive `s` registered contributes its `ind`,
    `ctor` and `elim` declarations. Antitone in the state, which is what makes it compose. -/
def SpecEnv (env envC : VEnv) (s : ErasureState) (Σ⁺ : GlobalDeclarations) : Prop

theorem SpecEnv.mono (h : StateLe s₁ s) : SpecEnv env envC s Σ⁺ → SpecEnv env envC s₁ Σ⁺
theorem SpecEnv.exists (hreg : RegInvShape' s) (P : PrimSpec …) : ∃ Σ⁺, SpecEnv env envC s Σ⁺
```

`SpecEnv.mono` is the whole trick: a motive concludes `∀ Σ⁺, SpecEnv env envC s' Σ⁺ → …`, and a
sub-run's state `s₁ ≤ s'` inherits the same `Σ⁺` — so no two environments ever have to be merged,
and `Lower`'s premises (positive lookups in one fixed `Σ⁺`) compose for free. `StateLe` and
`RunConcl` already exist (`ErasureRun.lean:1585,1609`) and carry unchanged. `SpecEnv.exists` is the
non-vacuity direction, built from `RegInvShape` (`ColdStartShape.lean:314`, re-anchored) plus
`PrimSpec.lookup_adequate` — i.e. the specification environment is *constructed from what the run
consulted and registered*, which keeps the tree's genuine advantage over the paper's presentation.

### 3.9 `LBWfPeregrine` — the output boundary

```lean
/-- `untyped_transform_pipeline`'s precondition, not what `peregrine validate` checks
    (which omits η; and peregrine's own discharge is `Admitted`,
    `theories/erasure/Transforms.v:375`). -/
structure LBWfPeregrine (Σ : GlobalDeclarations) (t : LBTerm) : Prop where
  keys       : (Σ.map Prod.fst).Nodup
  declsWf    : ∀ p ∈ Σ, LBWfDecl (declsBefore Σ p.1) p.2
  closed     : LBClosed t 0
  constsOk   : ∀ kn ∈ t.consts, envLookup Σ kn ≠ none
  ctorApplied: NoBlock t ∧ NoBlockEnv Σ          -- `with_constructor_as_block = false`
  casesExh   : ∀ node, branchCount = ctorCount Σ iid
  fixLambda  : ∀ `.fix defs i`, i < defs.length ∧ ∀ d ∈ defs, d.body.isLambda
  projDecl   : ∀ `.proj ⟨iid, np, i⟩ _`, the projection resolves in Σ
  etaCtors   : ∀ `.construct iid k []` at spine length n, n ≥ cstrArity Σ iid k
  etaFix     : LBExpandedFix Σ t
  asciiNames : ∀ binder name in Σ, t, it is ASCII-graphic     -- the λ□ parser's constraint
```

`ctorApplied` and `closed` are supplied *unconditionally* by `visitExpr_shape_all`
(`NoBlock t ∧ LBClosed t 0 ∧ NoFix t`, no hypotheses, panic-tolerant) — two of the ten conjuncts
for free. `etaCtors` uses `cstrArity = ind_npars + cstr_nargs` read off `Σ`'s own `InductiveDecl`,
so the predicate is checkable on the emitted program alone. `etaFix` is the open one: the probe
verified the constructor half (982/982) but not `EEtaExpandedFix.expanded`, and `Erasure.lean:911`
carries the code's own `-- TODO: eta-expand fixpoints?`. **W3's acceptance test measures it on the
five `.ast` files before T9's conclusion is committed to it**; if it fails, the honest move is a
ledger row plus an upstream report, not a weaker predicate.

### 3.10 `FirstOrderInd` — T7

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

/-- the `decide`able side (criterion 8), on `Lean.Environment`; connected by `PrimSpec.ind_adequate`. -/
def firstOrderIndB (lenv : Lean.Environment) (fuel : Nat) (I : Name) : Bool
theorem firstOrderIndB_sound (P : PrimSpec lenv env …) :
    firstOrderIndB lenv fuel I = true → FirstOrderInd env (fun J => firstOrderIndB lenv fuel J) I
```

`fields` ≡ `[L Def. 14]`; `mono`/`noIndices` are the two hygiene clauses Letouzey's parameterless
setting leaves implicit; `informative` is the syntactic sufficient condition for `[L Def. 6]`,
whose *conclusion* is `firstorder_no_box`. `[S §7.3]`'s `firstorder_ind` is cited as origin and not
transcribed (its `negb (Sort.is_level …)` conjunct is `false` on `nat`).

### 3.11 `PrimSpec` — the one bundle, five fields

Built by renaming `OracleDischarge.ResidualHyps` (`OracleDischarge.lean:65`, already four fields in
exactly this shape) and adding two.

```lean
structure PrimSpec (lenv : Lean.Kernel.Environment) (env : VEnv) (Us : List Name)
    (gw : Void IO.RealWorld → NameGenerator) : Prop where
  env_connect     : ∃ ves : VEnvs, ves.WF lenv ∧ env = ves.venv .safe   -- + `abs_env_irr`
  lookup_adequate : …   -- getConstInfo / getCasesInfo? / getCtorArity? / getDeclInfo?
                        --   = `ResidualHyps.cases_run` + `.ctor_run`, re-aimed at `env`
  fresh_names     : …   -- = `ResidualHyps.fresh_run`
  oracle_sound    : …   -- = `ResidualHyps.orc_refl`; **discharged**, not assumed
  ind_adequate    : …   -- Q6 F8: `getConstInfo I : inductInfo` ↔ a `VInductDecl` in `env`'s list

theorem PrimSpec.oracle_sound_of_run (P : PrimSpec …) (wf : ves.WF lenv) …
    (hrun : … LeanToLambdaBox.isErasable e … = .ok true) :
    Erasable env Us.length Δ.toCtx ve      -- via `Oracle.kernel_isErasable_sound`
```

Fields 1, 2, 3, 5 are class **D**; field 4 is class **B**, discharged through
`Relevance` → `RelevanceCheck.isErasable.WF` → `Oracle.kernel_isErasable_sound` →
`PrimSpec.oracle_sound_of_run`. That chain is the development's only trust *reduction*, it costs
33 axioms (measured), and keeping it is what makes criterion 9 satisfiable; it also means shipping
edit **B1** (the `isErasable` kernel reroute) must stay, and therefore that its measured
under-erasure (review SI-1) is owned inside `Supported` (§3.12) with a raised finding (§8.2).

### 3.12 `Supported` — the fragment, and where the holes are visible

```lean
/-- Syntactic, decidable on `e` **and its dependency closure**. Every conjunct is a coverage
    statement a reader audits; nothing here is a proof convenience. -/
inductive Supported (lenv : Lean.Environment) : Expr → Prop
  | bvar | fvar | app | lam | letE | mdata
  | const     (hk : InFragment lenv n)                    -- N6, N16: no IO/Task/String/UInt*/
                                                          --   Float/@[implemented_by]/Quot-relevant
  | natLit    (hn : cfg.nat = .peano)
  | proj      (hs : StructInFragment lenv S)
  | ctorApp   (hc : lenv.getCtorArity? cn = some ar)
  /-- `casesApp` — the **plain**-`casesOn` conjunct. The head must be `I.casesOn` for an
      inductive `I` in the fragment whose `CasesInfo` has no `CasesAltInfo.default` (sparse
      match) and no `hasSideCondition` (per-constructor eliminator), and every minor must be a
      syntactic λ-chain of its alt's field arity (`IsLamTelescope`). The first exclusion is the
      shipping bug of `VerifyBench/Quicksort` (`quicksort_fuel._sparseCasesOn_1`); the second
      is what makes the composite's branch rule exact (§2.1, Q1). -/
  | casesApp  (hplain : PlainCases lenv con) (hmin : ∀ m ∈ minors, IsLamTelescope nf m)

def supportedB (lenv : Lean.Environment) (fuel : Nat) : Expr → Bool
theorem supportedB_sound : supportedB lenv fuel e = true → Supported lenv e
```

Plus a *reporting* predicate that excludes nothing: `HasCompilerBody lenv n` (Q3), so the
coverage table shows which declarations were erased from `_unsafe_rec` bodies rather than hiding
it or excluding them.

### 3.13 `ErasableAxioms` and the ledger

```lean
/-- `[S §5.6]`'s `axiom_free` generalised — the naive form is uninhabited in Lean, which is why
    the current capstones cover 0/5. A `Prop`-typed axiom is `Erasable`, hence boxed, hence
    never *reachable* in the emitted program; so the condition is on reachability, and it is a
    decidable check on the emitted `(Σ, t)`. -/
def ErasableAxioms (Σ : GlobalDeclarations) (t : LBTerm) : Prop :=
  ∀ kn, ReachableFrom Σ t kn → envLookup Σ kn = some (.constantDecl ⟨none⟩) → AxiomRealizer Σ kn

/-- N2: the enumerated realizer specification for a reachable axiom (`@[extern]`, `Eq.rec`
    remapped by peregrine). One entry per name, each with its assumed evaluation behaviour. -/
inductive AxiomRealizer (Σ : GlobalDeclarations) : Kername → Prop
```

```lean
-- test/Ledger.lean, diffed against doc/rework/ledger-fixture.txt in CI
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorder
#print axioms LeanToLambdaBox.visitExpr_refines_erasesLB
#print axioms LeanToLambdaBox.erases_correct
#print axioms LeanToLambdaBox.lower_correct
#print axioms LeanToLambdaBox.lowerFix_correct
#print axioms LeanToLambdaBox.LBOptimize_correct
```

Rows: (a) lean4lean's inherited `sorryAx` cluster at `20ec229` with `file:line`, with
`EnvLemmas.lean:334 VEnv.WF.patsStrong` marked **fork-authored**; (b) the 29-name executable-checker
cluster including two `_native.bv_decide` axioms; (c) `PrimSpec`'s four class-**D** fields;
(d) the class-**C** hypotheses (`hcfg`, `hsup`, `hax`, `hfo`, `hcomp`, `hsub`, `hev`); (e) the
class-**E** rows: N1 csimp, N2 extern, N3 machine `Nat`, N4 argmask, N5 auto-inline, N7
termination, N10 serialisation, N11 `.inlinings`/`.mli`, N14 size, N16 `Quot`, N17 `Acc`, the
compiler-vs-kernel body gap (Q3), peregrine's `Admitted` pipeline precondition, and Q8's dropped
Rocq transport. **No prose copy anywhere else.**

---

## 4. Theorems

### 4.1 Supporting

```lean
theorem Erases.exists_of_trExprS (henv : env.WF) (hΔ : VLCtx.WF env Us.length Δ)
    (h : TrExprS env Us Δ e ve) : ∃ t, Erases env Us Δ e t                          -- class B
```

### 4.2 T4 subject reduction / T5 `erases_correct`

```lean
theorem SEval.defeq                                                                 -- T4, class B
    (henv : env.WF) (hΔ : VLCtx.WF env Us.length Δ)
    (htr : TrExprS env Us Δ e ve) (hev : SEval env Us fl Δ e v) :
    ∃ vv, TrExprS env Us Δ v vv ∧ env.IsDefEqU Us.length Δ.toCtx ve vv

theorem erases_correct                                                              -- T5, class B
    (henv : env.WF) (hwt : TrExprS env Us [] e ve)
    (hev  : SEval env Us fl [] e v)
    (her  : Erases env Us [] e t)
    (hΣ   : ErasesEnv env env Σ⁺ t) :
    ∃ v', Erases env Us [] v v' ∧ WcbvEval Σ⁺ eraseFlags t v'
```

Exactly five hypotheses, none named `Supported`/`Relevant`/`Iota*`/`*Consistent`/`*Hyps`
(criterion 6). The value's erasure is existential — the whole reason a relation exists. Note the
environment is `Σ⁺`, the **specification** environment: T5 is the paper's theorem with no pass
contamination, and the passes carry it the rest of the way. Proof structure unchanged from the
tree: induction on `hev`, inversion on `her`, box arms consume T1's rules (1)(2)(3), β consumes
`erases_subst`, δ consumes `ErasesEnv`, and the `Erasable` premise crosses each step by
`SEval.defeq`. The ι arm consumes `ErasesDecl.elim`'s `ElimBody` and the `pats` agreement inside
`IndInfo` — this is where `IotaPattern`/`IotaDischarge`'s content re-lands, at declaration level,
without `IotaRelevant`.

### 4.3 T6 the pass layer — `optimize_correct`'s shape, relationally

```lean
structure LBPassR where
  rel        : GlobalDeclarations → GlobalDeclarations → LBTerm → LBTerm → Prop
  flIn flOut : WcbvFlags
  correct    : LBWf Σ⁺ → LBClosed t 0 → LowerEnv Σ⁺ Σ → rel Σ⁺ Σ t t' →
               WcbvEval Σ⁺ flIn t v → ∃ v', rel Σ⁺ Σ v v' ∧ WcbvEval Σ flOut t' v'

theorem lower_correct                                                               -- class A
    (hwf : LBWf Σ⁺) (hcl : LBClosed t 0) (hE : LowerEnv Σ⁺ Σ) (h : Lower Σ⁺ t t')
    (hev : WcbvEval Σ⁺ eraseFlags t v) :
    ∃ v', Lower Σ⁺ v v' ∧ WcbvEval Σ eraseFlags t' v'

theorem lowerFix_correct                                                            -- class A
    (hE : LowerEnv Σ⁺ Σ) (hfix : LowerFix Σ⁺ kns b₀ defs) … :
    WcbvEval Σ⁺ eraseFlags (mkApps (.const kns[j]) args) v →
    ∃ v', Lower Σ⁺ v v' ∧ WcbvEval Σ eraseFlags (mkApps (.fix defs j) args') v'

theorem LBOptimize_correct'                                                         -- class A
    {b g : Bool} : WcbvEval Σ ⟨true, g, b⟩ t v →
    WcbvEval (LBOptimize_env Σ) ⟨false, g, b⟩ (LBOptimize Σ t) (LBOptimize Σ v)

def lbcompile_correct : … -- `lower_correct` ⨟ `LBOptimize_correct'`, eraseFlags → targetFlags
```

Three facts about the cost. (i) `lower_correct`'s `elim` arm **is** `IotaBridge.lean`'s
`wcbvEval_mkApps_mkLambdas_substList` (`:111`) plus `value_mkApps_construct_args` (`:69`) — 207
lines, flag-polymorphic, already proved, with a non-vacuity guard already at `appliedFlags`.
(ii) `lowerFix_correct` **is** `closeFix_substList_fixSubst` (`FixUnfold.lean:748`) plus
`FixUnfoldChain.eval` (`:830`, gated on `with_guarded_fix = true`, which `eraseFlags` satisfies) —
1,184 lines, already proved. (iii) `LBOptimize_correct'` is the *only* re-proof in the carried
list: today's statement runs `defaultFlags → optFlags`, both **block** form, and 14 of its 22 rule
arms transfer verbatim while exactly four (`construct_atom`, `construct_app`, `iota`, `proj`) must
be newly proved; generalising over `with_constructor_as_block` (as written above) discharges T6 at
any flag point in one theorem. Flags:

```lean
def eraseFlags  : WcbvFlags := ⟨true,  true, false⟩   -- new; nothing in the tree is at this point
def targetFlags : WcbvFlags := ⟨false, true, false⟩   -- = today's `appliedFlags`
def blockFlags  : WcbvFlags := ⟨false, false, true⟩   -- today's `targetFlags`, renamed
```

### 4.4 T8 — the bridge

```lean
theorem visitExpr_refines_erasesLB                                                  -- class B
    (P    : PrimSpec lenv env Us gw)
    (hcfg : cfg.csimp = false ∧ cfg.nat = .peano ∧
            cfg.remove_irrel_constr_args = false ∧ cfg.extern = .preferLogical ∧
            cfg.auto_inline_typeclass_dispatch = false)
    (hC   : CompilerEnv env envC e)
    (hwt  : TrExprS envC Us Δ (prepare_erasure e) ve)
    (hsup : Supported lenv (prepare_erasure e))
    (hnp  : ¬ run.panicked)
    (hrun : Erasure.visitExpr (prepare_erasure e) s ctx cctx ref w = .ok (t, s') w')
    (hinv : BridgeInv env envC Us cfg (gw w) ctx s Δ) :
    ∀ Σ⁺, SpecEnv env envC s' Σ⁺ →
      ErasesLB envC Us Σ⁺ Δ (prepare_erasure e) t ∧ RunConcl s s' ∧ gw w ≤ gw w'
```

and, at the top level, `LowerEnv Σ⁺ s'.gdecls` from the registration records. Four things to say.
*The subject is `prepare_erasure e`*, per Q1 §2.8 — `replaceUnsafeRecNames`, `macroInline`,
`inlineMatchers` are source-side and are enumerated by `run_prepare_erasure_ok`
(`ColdStartRun.lean:169`) under exactly `hcfg`'s `csimp = false`. *`Σ⁺` is universally quantified*
under `SpecEnv`, which is antitone in the state (§3.8), so sub-runs compose without merging
environments. *Panics*: `hnp` is stated, and two of the sixteen sites are refuted by
`Erases.sort_erasable`/`forallE_erasable`; the other fourteen are in `doc/rework/panics.md`.
*`BridgeInv` keeps 7 of its 10 fields* (`mlc`, `lparams`, `cfg`, `kfresh`, `reserved`, and
`knames`/`consts` collapsed into the existing `CanonicalConstants`); `natcfg` dies with N3's flag
duplication and `fixvars`/`fixfresh` die with `Erases.fixvar`.

### 4.5 T7 uniqueness and T9 the capstone

```lean
theorem firstorder_erases_deterministic                                             -- T7, class B
    (henv : env.WF) (hfo : FirstOrderInd env fo I)
    (hwt : TrExprS env Us [] v vv)
    (hty : env.HasType Us.length [] vv (VExpr.mkApps (.const I us) args))
    (hval : SEval env Us fl [] v v)
    (h₁ : Erases env Us [] v t₁) (h₂ : Erases env Us [] v t₂) : t₁ = t₂

theorem firstorder_no_box (… same premises …) (h : Erases env Us [] v t) : NoBox t

theorem shipping_erase_correct_firstorder                                           -- T9, class B
    (P    : PrimSpec lenv env [] gw)
    (hcfg : … as T8 …)
    (hC   : CompilerEnv env envC e)                       -- Q3, class C
    (hwt  : TrExprS envC [] [] e ve)
    (hsup : Supported lenv e)                             -- N6/N16, class C, decidable
    (hnp  : ¬ run.panicked)                               -- N12, class C
    (hfo  : FirstOrderInd env fo I)                       -- class C, decidable
    (hty  : envC.HasType 0 [] ve (VExpr.mkApps (.const I us) args))
    (hrun : Erasure.erase e cfg cctx ref w = .ok (.untyped Σ (some t), inls) w') :
    ∃ Σ⁺, ErasesEnv env envC Σ⁺ t
        ∧ LowerEnv Σ⁺ Σ
        ∧ LBWfPeregrine Σ t
        ∧ ErasableAxioms Σ t                              -- decidable on the emitted program
        ∧ ∀ v, SEval envC [] fl [] e v →
            ∃ tv, Erases envC [] [] v tv ∧ NoBox tv ∧
                  WcbvEval (LBOptimize_env Σ) targetFlags (LBOptimize Σ t) tv
```

Composition, mirroring `[S §7.3]`: `erase_run_ok` (`ColdStartRun.lean:651`) decomposes the run into
`prepare_erasure` then `visitExpr` and produces `Σ = sf.gdecls`, `t`, `inls`; T8 puts the output in
`Erases ⨟ Lower` at a `Σ⁺` that `SpecEnv.exists` constructs; T5 simulates the source evaluation
into λ□ at `Σ⁺`, `eraseFlags`; `lower_correct`/`lowerFix_correct` carry it to `Σ` at `eraseFlags`;
`LBOptimize_correct'` discharges `with_prop_case` to `targetFlags`; T7 identifies the value's
erasure uniquely and shows it box-free. `ErasableAxioms` — reachability, not `axiom_free` — is what
moves coverage off zero.

### 4.6 T10 — the Arith instance

```lean
-- VerifyBench/ArithCovered.lean, elaborated by `lake build`
example : supportedB lenv fuel (expr_of benchArith) = true := by decide
example : firstOrderIndB lenv fuel ``Nat = true := by decide
example : ErasableAxioms arithΣ arithT := by decide          -- Arith has 0 axioms: vacuous
theorem arith_hcomp : CompilerEnv arithEnv arithEnvC (expr_of benchArith) := …
                      -- 4 `TrExprS` + `HasType` checks: Nat.add/mul/sub/pow
theorem arith_covered : <the full conclusion of T9, instantiated at Arith> := …
```

Arith is the minimum because its residue is exactly the typeclass-dictionary layer the
collaborators care about: 10 typeclass projections, 4 singleton `fix` blocks, a 19-node peano
tower, 5 `.case` nodes, 42 `.construct`, **0 axioms** and **0 mutual blocks** (measured).

---

## 5. Module plan

Sixty-eight modules at HEAD (42,632 lines) plus the three shipping files. "Re-anchored" means the
statements change and the proof skeleton does not.

### 5.1 Carried unchanged

| Module | Lines | Note |
|---|---|---|
| `Semantics/{Values,Eval,Env,Substitution,Metatheory}.lean` | 1,164 | flag-polymorphic throughout; nothing pinned at a flag point that changes |
| `Closed.lean` | 871 | consumed by every simulation and by `IotaBridge` |
| `Abstract.lean` | 423 | `toBvar` metatheory; the fvar↔de Bruijn transport `LowerFix` and the bridge need |
| `FixMetatheory.lean` + `FixUnfold.lean` | 1,184 | re-aimed at `lowerFix_correct`; **statements unchanged** |
| `IotaBridge.lean` | 207 | re-aimed at `lower_correct`'s `elim` arm; statements unchanged |
| `Erasability.lean` | 230 | `Erasable` + Letouzey Lemma 2's stability kit |
| `Relevance.lean`, `RelevanceCheck.lean` | 229 | the executable oracle and its `M.WF` soundness |
| `OutputShape.lean` | 155 | the panic modelling; feeds `doc/rework/panics.md` |
| `ErasureRun.lean` | 3,234 | 74 `run_*`, `RunConcl`, `StateLe`, the `⊑`/admissibility kit, `mutual_le_of` — relation-independent, transfers with **zero** edits |

### 5.2 Re-anchored

| Module | Lines | What changes |
|---|---|---|
| `Semantics/Flags.lean` | 61 | `+ eraseFlags`; `targetFlags := ⟨false,true,false⟩`; old block one renamed `blockFlags`; header rewritten (it currently asserts the opposite of the design) |
| `Optimize.lean` | 1,090 | statement generalised over `with_constructor_as_block`; four new rule arms (`construct_atom`, `construct_app`, `iota`, `proj`); wired into the capstone's closure |
| `CheckerAdequacy.lean` | 143 | seven kernel-generic declarations upstreamed; `kernel_isErasable_sound` renamed into `LeanToLambdaBox.Oracle` (criterion 21) |
| `OracleDischarge.lean` | 123 | becomes `PrimSpec.lean`: `ResidualHyps` renamed, `env_connect` and `ind_adequate` added |
| `Erases.lean` | 1,426 | ten rules (§3.2); the transport half carried, six rules' arms deleted; the `natLit`/`proj` fixtures kept as non-vacuity guards, the `fixRec`/`fixMut`/`fixOpen` ones deleted |
| `ErasesAbstract.lean`, `ErasesStrengthen.lean`, `ErasesUniform.lean` | 1,865 | per-rule inductions: nine arms survive verbatim per lemma; `ErasableStrengthen` (a commissioned premise) is discharged or becomes one ledger row |
| `SubjectReduction{,Full,Iota}.lean` | 1,414 → ~1,050 | merged into one `SubjectReduction.lean` proving `SEval.defeq`; β/ζ/δ written once via the abstract-`P` spine schema |
| `SourceEval.lean` (+`SourceEvalData.lean`) | 701 → ~250 | one flag-parameterised `SEval`; seven relations deleted |
| `EnvErasure{,Nonrec,Rec}.lean` | 1,640 → ~700 | one `ErasesEnv` + `SpecEnv`; the `_of_registered*` implications become `SpecEnv.exists` |
| `ColdStartShape.lean` | 1,055 → ~600 | `RegInvShape` keeps `kn`/`cover`/`closed`/`nofix`, loses the five `Registered*On` fields to `SpecEnv` |
| `ColdStartInduction.lean` | 1,503 | `visitExpr_shape_all` carried verbatim (hypothesis-free, panic-tolerant); `RegBridgeHyps` and its fixtures deleted |
| `ColdStartRun.lean` | 672 | `erase_run_ok`, `run_prepare_erasure_ok` carried; `prepare_sound_of_prepareHyps` re-aimed at `SEval` |
| `VisitExprRefines.lean` | 4,641 | the 18 motives' conclusions restated against `ErasesLB` + `SpecEnv`; `BridgeInv` keeps 7 of 10 fields. **This is the wave-4 long pole** |
| `Bridge.lean` | 674 | `Supported` re-indexed onto `Lean.Environment`, `+ supportedB`, `+ PlainCases` |
| `FirstOrder.lean` | 762 → ~250 | `informativeType_not_erasable` (`:103-131`) carried verbatim; `FirstOrderValue` replaced by `FirstOrderInd`; `eraseCore` fuel lemmas absorbed |
| `ErasesCorrect.lean` | 650 | becomes T5 with five hypotheses; the ι/proj arms absorbed from the deleted chains |
| `ColdStart.lean` | 2,000 → ~500 | becomes `Capstone.lean`: one T9, the premise plumbing deleted |
| `LeanToLambdaBox.lean` | 217 | import list and header rewritten |

### 5.3 Deleted

`ErasureContext.lean` (251) — the twelve-column index, criterion 1. `DeltaHyps.lean` (1,499),
`CasesBridgeHyps.lean` (287), `DataBridgeHyps.lean` (137), `ProjBridgeHyps.lean` (182),
`PrepareHyps.lean` (118) — one `PrimSpec`, criterion 4. `ErasesCorrectData.lean` (1,731),
`ErasesCorrectIota.lean` (1,075) — the two extra simulations; their ι/proj content re-lands in T5's
arms. `IotaPattern.lean` (485), `IotaDischarge.lean` (604), `SubjectReductionIota.lean` (458, after
its arms are absorbed), `ProjPattern.lean` (1,059), `ProjDischarge.lean` (415) — the discharge
chains keyed on the six deleted rules, and `IotaRelevant`/`IotaShape` with them.
`RecBlockErasure.lean` (811) — recursion's premise layer, replaced by `LowerFix`.
`EraseCore.lean` (643) minus the fuel lemmas — refuted as a bridge by its own addendum.
`FirstOrderShipping.lean` (254), `FirstOrderShippingIota.lean` (553), `ShippingCorrect.lean` (207),
`ShippingCorrectData.lean` (127) — four capstone flavours become one. `Export/EvalT.lean` (296) —
the `Type`-valued twin for a transport that was never scoped (Q8). `Semantics.lean` (17),
`Eval.lean` (11) — aggregator and shim. `ErasesLevels.lean` (373), `ErasesInstL.lean` (493),
`ErasesDeltaL.lean` (280) — the Γ-level campaign, insofar as it serviced deleted rules (keep any
level-instantiation lemma T5's δ arm still needs; expect ~200 of 1,146 to survive).
Plus the ~3,000-3,500 comment lines of changelog and every claim the review measured false.

### 5.4 New

| File | Contents | Est. lines |
|---|---|---|
| `Lower.lean` | `Lower`, `LowerAlt`, `CtorDecl`, `ElimDecl`, `RuntimeKey`; commutation with `shift`/`subst`/`substList`; inversion lemmas | 700 |
| `LowerCorrect.lean` | `lower_correct` (13 congruence arms + 2 redex arms), non-vacuity guards | 900 |
| `LowerFix.lean` | `ConstToFVar`, `CloseConst`, `LowerFix`, `lowerFix_correct` | 550 |
| `ElimBody.lean` | `ElimBody` (3 shapes), `IndInfo`, `SubsingletonElim`, the derivation from `env.WF`, one checked instance per shape and per named recursor (criterion 7) | 700 |
| `ErasesLB.lean` | the composite + the five derived introduction lemmas + transport | 450 |
| `ErasesEnv.lean` | `ErasesDecl`, `ErasesEnv`, `LowerEnv`, `SpecEnv`, `SpecEnv.mono/.exists` | 800 |
| `CompilerEnv.lean` | `CompilerEnv`, `CompilerBodyOf`, the `env ≤ envC` lifting lemmas (Q3) | 250 |
| `ErasesTotal.lean` | `Erases.exists_of_trExprS`, `sort_erasable`, `forallE_erasable` | 250 |
| `FirstOrderInd.lean` | `FirstOrderInd`, `firstOrderIndB`, adequacy, `firstorder_no_box` | 450 |
| `LBWf.lean` | `LBWfPeregrine`, `ErasableAxioms`, `AxiomRealizer`, the decidable checkers | 400 |
| `Capstone.lean` | T9 | 500 |
| `test/Ledger.lean` + `doc/rework/ledger-fixture.txt` | the measured ledger | 60 |
| `VerifyBench/ArithCovered.lean` | T10 | 300 |
| `doc/rework/{rules-Erases,rules-Lower,panics,coverage}.md` | criteria 3, 10, 14 | — |

Net: ~7,300 new lines against ~14,000 deleted and ~13,000 carried untouched.

---

## 6. Waves

Each wave states its dependencies, its parallelisable units, and one **machine-checkable**
acceptance test. Units within a wave are independent.

### W0 — foundation (1 unit)
*Goal.* Make the flag points exist, delete what is provably dead, stand up the ledger.
*Deliverables.* `eraseFlags`/`targetFlags`/`blockFlags`; delete `Export/EvalT`, `Semantics.lean`,
`Eval.lean`, `ShippingCorrect*`; `test/Ledger.lean` + fixture + CI job; the two rule tables as
stubs.
*Acceptance.* `lake build` clean; `lake env lean test/Ledger.lean` output equals the committed
fixture; `grep -rn "targetFlags" LeanToLambdaBox/ | grep -c "true⟩"` is 0.

### W1 — the specification layer (3 parallel units; depends on W0)
*Goal.* `Erases`, `SEval`, `Optimize` at the right flags.
*Units.* (1a) `Erases` ten rules + transport re-anchoring + `ErasesTotal.lean` + `rules-Erases.md`.
(1b) one `SEval` + `SEval.defeq` + `SEval.mono/.le` + `CompilerEnv.lean`. (1c)
`LBOptimize_correct'` generalised over `with_constructor_as_block` (four new arms).
*Acceptance.* `grep -c "| " Erases.lean`'s rule count is 10 and `grep -n ErasureCtx Erases.lean` is
empty (criterion 1); `grep -c "inductive SEval" LeanToLambdaBox/` is 1 (criterion 4);
`#print axioms LBOptimize_correct'` = `[propext, Quot.sound]` and a guard fires at `eraseFlags`
(criterion 5, 15).

### W2 — the pass layer (3 parallel units; depends on W1)
*Goal.* The relations and their forward simulations; the runtime library's shape.
*Units.* (2a) `Lower.lean` + `LowerCorrect.lean`. (2b) `LowerFix.lean`. (2c) `ElimBody.lean` +
`IndInfo` + `SubsingletonElim` + the upstream ask for `VEnv.WF'.consts_origin`.
*Acceptance.* `#print axioms lower_correct` and `lowerFix_correct` = `[propext, Classical.choice,
Quot.sound]` (class **A**, criterion 15); each pass has a `_fires` guard in the style of
`Optimize.lean:1066`; `example : ElimBody … (Eq.rec's body) := by decide` and the same for
`And.rec`, `Iff.rec`, `False.rec`, `Decidable.casesOn` (criterion 7 as amended).

### W3 — environment, fragment, first-order (4 parallel units; depends on W2)
*Goal.* Everything T9 needs that is not the bridge.
*Units.* (3a) `ErasesEnv.lean` (`ErasesDecl`/`ErasesEnv`/`LowerEnv`/`SpecEnv`). (3b)
`ErasesLB.lean` — the composite and the five derived intro lemmas. (3c) `FirstOrderInd.lean`.
(3d) `LBWf.lean` + `Bridge.lean`'s `Supported`/`supportedB`.
*Acceptance.* `example : firstOrderIndB lenv fuel ``Nat = true := by decide`, likewise `Bool` and
`Tree` (criterion 8); `supportedB` returns `true` on Arith/BinaryTrees/Sieve and **`false` on
`Quicksort`'s `_sparseCasesOn_` head** (criterion 11); a script measures
`EEtaExpandedFix.expanded` on all five `.ast` files and the result decides `LBWfPeregrine.etaFix`
(Q5's open sub-question) before W5 starts.

### W4 — the bridge (1 unit, the long pole; depends on W3)
*Goal.* `visitExpr_refines_erasesLB`.
*Deliverables.* `BridgeInv` at 7 fields; the 18 motives restated against `ErasesLB` + `SpecEnv`;
`LowerEnv Σ⁺ s'.gdecls` from the registration records; the panic table.
*Sequencing inside the unit.* the 7 mechanical motives (1, 7, 8, 9, 11, 12, 18) → the 3
environment-facing (4, 5, 6) → the 8 pass-facing (2, 3, 10, 13, 14, 15, 16, 17), which is where the
derived intro lemmas pay for themselves.
*Acceptance.* `#print axioms visitExpr_refines_erasesLB` contains `sorryAx` only through the
lean4lean cluster named in the fixture, and the theorem's binder list contains no `*Hyps` other
than `PrimSpec` (criteria 4, 15).

### W5 — capstone, non-vacuity, delivery (3 parallel units; depends on W4)
*Goal.* T9, T10, T11, and landing it where consumers pin.
*Units.* (5a) `Capstone.lean`. (5b) `VerifyBench/ArithCovered.lean` + the five-program coverage
table. (5c) the hygiene pass (comment fraction, CI greps for hashes/dates/slice tags/unresolved
backticks), the `main` merge and the CI trigger change.
*Acceptance.* `lake build` elaborates `arith_covered` with every T9 hypothesis inhabited by a
checked term (criterion 13); `doc/rework/coverage.md` is tracked and its covered count is ≥ 1
(criterion 14); the ledger fixture matches (criteria 15-16); the hygiene greps are empty
(criteria 18-21); CI builds the branch consumers pin (criterion 22).

### W6 — optional, not on the critical path
The functional refinement `Lower Σ⁺ t₀ (lowerTerm E t₀)` on the exactness fragment (Q1's "(a)"),
recovering `[S §7.4]`'s "same result" reading; and Q2's option 1 (`FieldInIndices` field class +
`iota_sing_idx`), which would move `Acc.rec`/`WellFounded.fix` from N17 into the fragment.

---

## 7. Risk register

| # | Risk | Likelihood | Mitigation |
|---|---|---|---|
| R1 | `SpecEnv`'s antitone threading does not compose at some motive (a sub-run registers into a state the parent's `Σ⁺` does not cover) | medium | `SpecEnv.mono` is proved from `StateLe` (`ErasureRun.lean:1585`), which every motive already concludes; W4 sequences the three environment-facing motives (4, 5, 6) **first** so the failure surfaces on day one of the wave, not at motive 17 |
| R2 | T5's ι arm needs the `pats` ↔ `ElimBody` agreement, which touches the `patsStrong` residual | high | this is the *known* seam, already declared in §1 of the spec. `IndInfo` states the agreement at declaration level, where Q2's probe shows a pats-carrying `VEnv.WF` **is constructible today** (21/22 clauses discharged); the nine "unconstructible" docstrings are false and are deleted in W1 |
| R3 | `VEnv.WF'.consts_origin` does not land upstream in time | medium | `SubsingletonElim` is a named class-**C** hypothesis with a ledger row until it does — criterion 7 explicitly permits this. No other theorem depends on the derivation |
| R4 | `etaFix` is false on the emitted programs (`Erasure.lean:911`'s own TODO) | medium | W3's acceptance test measures it *before* T9's conclusion is committed. If false: one ledger row + an upstream report, and `LBWfPeregrine` keeps the nine conjuncts that hold |
| R5 | `Erases.exists_of_trExprS` is harder than budgeted (it is an induction over `TrExprS` with a `proj` case needing `TrProj`) | medium | the two hard cases are the criterion-10 lemmas, which are required anyway; the `proj` case reuses `Erases.proj`'s deliberate `TrProj`-freedom. Fallback: state `hpre` as a decidable premise of `ErasesLB.cases` and discharge it in the bridge from `BridgeInv.mlc` |
| R6 | `LBOptimize_correct'`'s four new arms are harder than the block twins suggest | low | the `iota`/`proj` arms have block twins to copy from, and `LBOptimize_iota_red` (`:909`) and `projCollapse_subst` (`:392`) are already stated form-independently |
| R7 | The 33-axiom fixture (criterion 9 × 15) is judged unacceptable at review | low | the ledger classifies all 29 non-standard names, distinguishing Lean-core `_native.bv_decide` from lean4lean's `sorryAx`; the alternative (field 4 at class **D**) is documented as a one-line switch that costs the development's only trust reduction |
| R8 | Genuine mutual blocks are unexercised (0/50 emitted `FixDef`s are mutual), so `LowerFix`'s multi-`kn` case ships unmeasured | medium | `LowerFix` is stated for lists, not singletons, so the *statement* is general; W2's non-vacuity guard is a hand-built two-element block, and the coverage table records that no benchmark exercises it |
| R9 | The relational conclusion is read as weaker than the functional one by a reviewer | low | §1.2 states the papers' own posture, and W6 offers the functional refinement as an additive theorem — it can be added later **without** restating T8, because a function equality implies relation membership |
| R10 | Shipping edit B1's measured under-erasure (review SI-1) is inside the fragment | medium | owned explicitly: `Supported` and `PrimSpec.oracle_sound` bound it, and the finding is raised (§8.2) rather than patched. Reverting B1 is *not* an option — it would demote field 4 to class **D** and make criterion 9 unsatisfiable |

---

## 8. Transpiler edits required

### 8.1 Edits: **none**

No change to `LeanToLambdaBox/{Erasure,Basic,Printing}.lean` is required by this design. Everything
the bridge needs already exists on `dev/verify` as the proof-only edits P1-P7 (the
`partial_fixpoint` mutual block, the nine `@[partial_fixpoint_monotone]` lemmas, `expr_withApp_eq`,
`visitCasesEta`/`visitCtorEta`, the `.toArray` loop, `Basic.lean`'s de-partialized `toBvar` family,
the `Relevance` import), and B1 (the `isErasable` kernel reroute) is *kept* because
`PrimSpec.oracle_sound` is discharged through it.

It is worth recording what a **functional** T8 would have required, because avoiding it is the
angle's main dividend: a compile table threaded through the shipping context or a new query
surface for it; or, failing that, edits to `fvar_to_name`/`mkAlt` to make binder names
reconstructible from `Σ`. Design B needs neither.

Two shipping-side edits currently carry no hypothesis and need one *ledger row each*, not a code
change: **B4** (the `@[inline]` restructure, which changes the `inlinings` output for mutual
blocks) and **B6** (the `MLType` extension, which affects only the `.mli` sidecar) — both under
N11. **B5** (`withLocalDef` dropping `nd`) is behaviour-neutral by argument but unmeasured
in-repo; W5's coverage script diffs the five `.ast` files against the frozen originals and settles
it.

### 8.2 Findings to raise (never patch — repository standing rule)

1. **Sparse `casesOn`.** `visitCases` mis-compiles a `casesOn` with a `.default` catch-all
   (`Erasure.lean:770,817`); `VerifyBench/Quicksort` panics, exits 0 and writes a wrong `.ast`.
   Already `RAISED-not-fixed`; design B makes it *visible in `Supported`* (criterion 11).
2. **Subsingleton elimination with an index-determined field.** For `Acc`-shaped inductives the
   emitted `.case` on a boxed discriminee evaluates by `iota_sing`, which boxes a field that is
   *data* (`Acc.intro`'s `x : α`). Measured: `largeElimClause ``Acc = some (2,[1])`. N17 restricts
   it; the eraser should refuse it, as Lean's own code generator does.
3. **`Quot` primitives as body-less axioms** (`Erasure.lean:873-877`): the erased program is stuck,
   exits 0 and passes `peregrine validate`. N16 restricts it.
4. **peregrine**: `run_untyped_transforms`' precondition obligation is `Admitted`
   (`theories/erasure/Transforms.v:375`), and `peregrine validate` does not check η-expandedness.
5. **MetaRocq**: `firstorder_ind` is `false` on `nat` (`PCUICFirstorder.v:59`'s
   `negb (Sort.is_level …)`), so every theorem guarded by it is vacuously guarded.
6. **lean4lean** (upstream asks, N15): `VEnv.WF'.consts_origin` + `iotaRHS'_Generic`; the seven
   kernel-generic declarations currently in `CheckerAdequacy.lean`; the `Quot.ind` theory/checker
   divergence.

---

## 9. Documentation policy compliance

* **Current fact only.** Every module header is rewritten to state what the module *is*. The three
  worked repairs the review asked for are in scope: `Semantics/Flags.lean:19-24` (which asserts the
  opposite of the design), the seven "no `addPat` clause" sites and the eight "`addInduct_WF` is
  `sorry`" sites (both measured **false** at `20ec229`), the five stale oracle descriptions,
  `Supported.casesApp`'s sparse-`casesOn` sentence, and the `ProjDischarge`/`ProjPattern`
  contradiction about `proj_defeq`.
* **One fact, one home.** Every claim about upstream state lives once, in `test/Ledger.lean`'s
  fixture, with the `file:line` and the command that measured it. The three prose ledgers are
  deleted; CI greps for a second copy.
* **Length budget.** ≤ 8 lines per lemma/field docstring, ≤ 40 per module header. Anything longer
  becomes a tracked document under `doc/`.
* **Resolvable references.** CI grep: every backticked identifier resolves; every cited document
  exists in the repository. `doc/rework/{rules-Erases,rules-Lower,panics,coverage}.md` and
  `ledger-fixture.txt` are tracked, so the citations in §3-§4 above resolve after W0.
* **No dead code, no duplicates, no forked relations.** §5.3 deletes the five modules measured
  outside the capstone's closure and the duplicate definitions the review machine-confirmed. Growth
  is by parameterisation: `SEval` by `SEvalFlags`, `WcbvEval` by `WcbvFlags`, `LBPassR` by its
  relation field — never by copying a relation and adding a rule.
* **Non-vacuity guards.** `Erases` (the `natLit`/`proj` fixtures, carried), `Lower`, `LowerAlt`,
  `LowerFix`, `ElimBody` (one per shape), `ErasesEnv`, `SpecEnv`, and each pass — in the style of
  `Semantics/Metatheory.lean:417` and `Optimize.lean:1066`.
* **Kernel lemmas upstream.** Criterion 21 is met without an exception list (§2.3).
* **No `native_decide`**; `set_option` only with a reason; no `@[simp]` on foreign namespaces. The
  tree is already clean here and stays so.
