# Design A — the papers' shape: one congruence relation, functional λ□→λ□ passes

**Angle.** `Erases` is `[S Fig. 18]` transposed — a strict congruence over `Lean.Expr` plus the
single `box` rule, ten rules, no side conditions, no registry. Every Lean-specific compilation
step is a **function** on λ□ carrying an `optimize_correct`-shaped theorem. The bridge concludes
a **term equality**, `t = LBLower.term Σ⁺ t₀`, not membership in a composite relation. This
document pushes that angle to its limit and names, in §2.1 and §7, the three places where it
cannot reproduce `visitExpr` exactly and what each costs.

**Status.** Design proposal against `doc/rework/00-REFERENCE-SPEC.md` (normative) and the six
probe reports under `doc/rework/probes/`. Every claim below cites a probe, a `file:line`, or a
measurement taken in this session. Where this design contradicts the reference spec, §2.3 lists
the amendment and its evidence.

---

## 1. Overview

### 1.1 The four structural moves

1. **The relation shrinks to a congruence.** `Erases : VEnv → List Name → VLCtx → Expr → LBTerm
   → Prop`, ten rules, producing no `.construct`, `.case` or `.fix`. Six of today's fifteen rules
   (`ctor`, `ctor_head`, `cases`, `fixvar`, `const_fix`, `fix`) and the twelve-column
   `ErasureCtx` index leave the specification.

2. **`.fix` moves to the *declaration*, not to a pass.** A recursive Lean declaration is a
   fixpoint; in Coq it literally is (`Fixpoint f` elaborates to `Definition f := fix f …`, so
   `tFix` arrives inside the body through the congruence). Lean puts the recursion at the
   declaration level, so `ErasesDecl` — not `Erases`, and not a pass — introduces `.fix`. This
   deletes the spec's `fixIntro` pass entirely, and with it the value mismatch that pass would
   have carried (a `.const c` that δ-unfolds to a λ under one environment and to a `.fix` value
   under the other). Evidence it is the right home: `visitExpr_shape_all`
   (`ColdStartInduction.lean:1104`) proves `NoFix t` for the *subject term* unconditionally —
   the shipping eraser never puts a `.fix` in a term, only in a declaration body.

3. **`.construct` and `.case` come from *inlining a runtime library*, and the library is
   functional.** `ErasesEnv` emits one λ□ declaration per constructor constant and one per
   `casesOn`-like constant reached (`ErasesDecl.ctor`, `ErasesDecl.elim`); two passes,
   `ctorInline` and `elimInline`, δβ-expand them at use sites; the library declarations are then
   dropped. Q1 concluded that a Σ-only pass "cannot see" the constructor/`casesOn` data —
   correct **about the shipping `Σ`**, which registers none of it (measured: 0 ctor/casesOn/rec
   declarations in all five `.ast`). Q4's repair supplies the missing half: the specification
   environment `Σ⁺` is *not* `s'.gdecls`; `s'.gdecls` is its lowered image. Put the two together
   and every input the passes need is in `Σ⁺`, so **no `CompileTable` and no new class-D field
   are required** — `LBPass.term : GlobalDeclarations → LBTerm → LBTerm` stands exactly as the
   spec writes it.

4. **The deliverable flag point is MetaRocq's `default_wcbv_flags`, and it is peregrine's
   input.** Measured this session:
   `EWcbvEval.v:69  default_wcbv_flags = {| with_prop_case := true ; with_guarded_fix := true ;
   with_constructor_as_block := false |}` — identical to the spec's `eraseFlags` — and
   `peregrine-tool theories/erasure/Transforms.v:151` declares `untyped_transform_pipeline`'s
   *input* evaluation to be `eval_eprogram_mapping EWcbvEval.default_wcbv_flags`. So the
   frontend's obligation stops at `eraseFlags`; `with_prop_case` is discharged downstream by
   peregrine's own verified `remove_match_on_box_trans`. `optimize` therefore leaves the critical
   path and is retained as (a) the worked template every pass copies and (b) an optional proved
   corollary at `optFlags = ⟨false, true, false⟩` = MetaRocq's `opt_wcbv_flags`.

### 1.2 The deliverable, in one block

```lean
theorem shipping_erase_correct_firstorder
    (P    : PrimSpec lenv env Us gw)                    -- one interface; fields 1-3 class D, 4-5 discharged
    (hcfg : cfg.csimp = false ∧ cfg.nat = .peano ∧
            cfg.remove_irrel_constr_args = false ∧ cfg.extern = .preferLogical ∧
            cfg.auto_inline_typeclass_dispatch = false)
    (hUs  : Us = [])
    (hwt  : TrExprS env [] [] e ve)
    (hsup : Supported lenv e)                            -- decidable, on `e` and its closure
    (hax  : ErasableAxioms env e)
    (hfo  : FirstOrderInd env ``Nat)
    (hty  : env.HasType 0 [] ve (.const ``Nat []))
    (hrun : (Erasure.erase e cfg).ok (.untyped Σ (some t), inls) w') :
      (∃ E t₀, ErasesEnv env E t₀ ∧ Erases env [] [] (prepare e) t₀ ∧
               t = LBLower.term E.all t₀ ∧ Σ ≐ LBLower.env E)
    ∧ LBWfPeregrine Σ t
    ∧ ∀ v, SEval env [] fullFlags [] (prepare e) v →
        ∃ tv, Erases env [] [] v tv ∧ NoBox tv ∧ WcbvEval Σ eraseFlags t tv
```

`≐` is `EnvAgree` (§3.5): equal `envLookup` on every kername, plus `Nodup` keys — the only
property `WcbvEval`, `constructorArity` and `isPropositionalInductive` read. It is the honest
form of "the run's environment *is* the lowered specification environment": it avoids a
list-order equality that carries no meaning and would be brittle.

### 1.3 What the probes forced, in one list

| Probe | Force |
|---|---|
| Q1 | The passes' inputs are not in the *shipping* `Σ`. Answered by move 3, not by a table (§2.1). |
| Q1 | `optimize` is not on the shipping path; splitting `LBCompile` is mandatory. Adopted as `LBLower`. |
| Q1 | Two `Supported` conjuncts buy binder-name exactness: plain `casesOn` only, minors are λ-chains. Adopted (S2, S3). |
| Q1 | Recursors reached as constants are `ax`, not `recr`. Adopted; `ErasesDecl.elim` covers `casesOn` only, which is *all* `getCasesInfo?` accepts (`Lean/Meta/CasesInfo.lean:56`, `isCasesOnLike`). |
| Q2 | Lean's large-elimination criterion admits index-determined **data** fields (`Acc.intro`'s `x`), so MetaRocq's `eval_iota_sing` is unsound for `Acc.rec`. Adopted the recommended first cut: `SubsingletonElim` = `LargeElim` minus `FieldInIndices`; `Acc.rec`/`WellFounded.fix` restricted (N17). |
| Q2 | A pats-carrying `VEnv.WF` is constructible now. Adopted: T3's and T5's non-vacuity guards are built, the nine "unconstructible" docstrings deleted. |
| Q3 | `ErasesDecl.defn` must read bodies from `defeqs`, and the eraser reads the `_unsafe_rec` body. Adopted: **one** `VEnv`, the compiler's, via `PrimSpec.env_connect` (§3.6). |
| Q4 | `t = LBCompile.term s'.gdecls t₀` is unsatisfiable. Adopted the augmented-environment form (§1.2). |
| Q5 | Parameters stay; `LBWfPeregrine` = `EWellformed(all_env_flags)` + `etaCtors` + `etaFix`. Adopted. |
| Q6 | `FirstOrderInd (env : VEnv) (I : Name)` is unwritable; MetaRocq's predicate is `false` on `nat`. Adopted Q6.2's definition over `VEnv.WF`'s declaration list; criterion 8 narrowed. |
| Q7 | `Quot` restricted (N16); `ErasesDecl.quot` deleted. |
| Reuse | `eraseFlags` does not exist and `targetFlags` is block form. Fixed in W0. |
| Reuse | `optimize` needs four new rule arms at applied form. Scheduled (W1). |
| Reuse | Routing the oracle in costs 33 axioms and 8 `Lean4Lean`-namespace declarations. Adopted with a split (§2.2, criterion 21). |

---

## 2. Decisions

### 2.1 The eight open questions

**Q1 — does the pass layer reproduce `visitExpr` exactly? YES, on `Supported`, against `Σ⁺`,
with three named exceptions.**

The pass layer is two functions. Both read only `Σ⁺ = E.decls ++ E.lib` and the term.

* `ctorInline Σ⁺` δβ-expands every declaration of `E.lib` whose body is a *constructor body*
  `mkLambdas ns (mkApps (.construct iid k []) (bvars ns))`. At a saturated application δ+β
  yields `mkApps (.construct iid k []) args'` — literally `visitConstructor`'s output at N4
  (`Erasure.lean:753-759`, argmask `Array.replicate numFields .keep`, `filter` the identity).
  At an under-applied one, δ leaves the λ-chain and β consumes what is there — literally
  `visitCtorEta`'s output, **including the binder names**, because the library body's binder
  names are the constructor's own ∀-binder names, which is exactly what
  `lambdaMonocularOrIntro` (`Erasure.lean:334`) takes from `Meta.inferType` (Q1 §2.7: for a
  partially applied constant `inferType` returns the declaration's type instantiated, and
  instantiation does not rename). Over-application: extra arguments stay applied outside.
  **Exact.**
* `elimInline Σ⁺` acts at an application whose head is `.const kn` with `E.lib` mapping `kn` to
  an *eliminator body* (§3.3) and whose spine is at least the body's arity: it takes the
  discriminant by position, splits each minor into `(names, body)` by `splitLambdas`, and builds
  `.case (iid, np) discr alts` with the extra arguments applied outside. This is `visitCases`
  (`Erasure.lean:768-838`) transcribed. It is *not* plain δβ: plain δβ would leave a β-redex per
  alternative and take the alternative's binder names from the *declaration*; `visitAlt`
  (`Erasure.lean:842`) strips the λs off the minor and uses the *minor's* names. The
  β-normalisation step is precisely `IotaBridge.lean:111`'s content, so the pass's hardest lemma
  is already proved. **Exact** whenever every minor is a syntactic λ-chain of the alt's arity —
  `Supported.S3`. Under-applied `casesOn`: as for constructors, δ then β, names from the library
  body = `casesInfo`-typed ∀-binder names = what `visitCasesEta` gets. **Exact.**

Where exactness genuinely fails, and the cost of each:

| # | Case | Why not reconstructible | Disposition |
|---|---|---|---|
| X1 | A `casesOn` minor that is **not** a λ-chain (`Option.casesOn o none Some`) | `visitAlt`'s fresh binder names come from `Meta.inferType` of an arbitrary function's type — not static per constant, not in `t₀`, not in `Σ⁺` | Excluded by `Supported.S3`. Q1 measured this is outside the fragment today too (`Bridge.lean:198-200`). Cost: hand-η-contracted minors. |
| X2 | **Sparse** `casesOn` (`CasesAltInfo.default`) and per-constructor eliminators (`hasSideCondition`) | `visitCases`'s three-way zip truncates and mis-pairs; the emitted `.case` is *wrong*, not merely unreproducible (`VerifyBench/STATUS.md`, Quicksort) | Excluded by `Supported.S2`, **visible in `Supported`** (criterion 11). Raised, not patched. |
| X3 | `.machine` `Nat`/`Int`, `csimp`, `extern = .preferAxiom`, `auto_inline_typeclass_dispatch` | different shipping code paths | Excluded by `hcfg` (N1/N2/N3/N5), all five already `false`/`.peano` in `VerifyBench`. |

Three Q1 recommendations this design **declines**, each with a reason:

* the `CompileTable` — unnecessary once `Σ⁺` carries the library (move 3). Declining it keeps
  `LBPass` at the spec's signature and adds no class-D obligation.
* the `block` table field — unnecessary once `.fix` is introduced by `ErasesDecl` (move 2); the
  block order is `ci.all`, a source-environment fact consumed where every other source fact is,
  in `PrimSpec.lookup_adequate`.
* the third `Supported` conjunct for `fixIntro` (`name_occurs` agrees with λ□ self-reference) —
  unnecessary: `ErasesDecl.fixdefn` takes `SelfRefers c body` as a *source-side* premise, so a
  block whose only self-reference is erased still produces a `.fix` with an unused binder, which
  is exactly what the eraser emits. The divergence Q1 anticipated cannot arise.

**Q2 — where is the subsingleton criterion derived? Upstream inversion + one pipeline theorem;
first cut excludes `Acc`.** Adopt Q2's §2.2 statement `SubsingletonElim env I` as an
*environment* predicate, defined as `LargeElim` clause (2) **restricted to the proof disjunct**
(drop `FieldInIndices`). It covers `False.rec`, `Eq.rec`, `And.rec`, `Iff.rec` and `Decidable`'s
elimination; `Acc.rec`/`WellFounded.fix` become restriction **N17** with one ledger row, which
costs nothing the shipping pipeline delivers (Lean's own code generator refuses `Acc.rec`).
Derivation chain L1–L6 of Q2 §2.3 is available except the inversion `VEnv.WF'.consts_origin`,
which is kernel-generic and goes upstream (N15, ask 1 of §8.2). Until it lands, `SubsingletonElim`
is one named class-**C** hypothesis with a ledger row — criterion 7's own escape clause. Note
that the benchmark corpus does not exercise it: the only eliminated `Prop`-adjacent inductive is
`Decidable`, which is `Type`-valued (Q6.4 metadata), and `Eq.rec` arrives as an axiom. So Q2 is
**off T10's critical path**, exactly as Q1 predicted.

**Q3 — hypothesis or restriction? Neither: one environment.** The `VEnv` this development is
about *is* the compiler's. `PrimSpec.env_connect` relates `lenv : Lean.Environment` to `env :
VEnv` by `TrEnvC := TrEnv` **followed by** one `VEnv.addDefEq` per declaration whose body the
eraser reads through `Compiler.LCNF.getDeclInfo?` (i.e. per `_unsafe_rec`). Q3 measured the
`WF` obligation true and decidable on all 33 such declarations (`inferType body` defeq the
declared type, 33/33), and it is the *only* way to give the two `partial def`s a body at all
(they reach the kernel as `opaque` with value `Inhabited.default`). Consequences: no `envC`
binder anywhere; `SEval`'s δ unfolds the compiler equations; T3's `defn` reads
`env.defeqs`; one class-**E** ledger row states that compiler and kernel bodies agree only
propositionally (equation lemmas, never transported) and that for `partial def` the gap is total.
The spec's alternative "restrict to declarations where the bodies coincide" is **deleted**: it
covers 0/5 programs, Arith included.

**Q4 — do the eliminator declarations blow up the `.ast`? No, they never reach it.** `E.lib` is
dropped by `LBLower.env`, so the deliverable is byte-for-byte today's file (Q4.3 reading 1). The
un-pruned worst case was measured at +4.5%…+13.6%, median +9.3%, bounded by the program's data
vocabulary (≤ 7 distinct eliminated inductives across the suite) rather than its size. Adopt and
freeze. Record in the N14 ledger row that `.ast` size is dominated by the `.peano` tower (49% of
Quicksort) and hygienic binder names (7–17%), not by the verification design.

**Q5 — parameters: the frontend keeps them.** `remove_params_optimization` is pass 2 of
`verified_lambdabox_pipeline`, run verbatim by peregrine and carrying `wcon :
with_constructor_as_block = false`. `ErasesDecl.ctor`'s body is η-expanded at
`npars + nfields = cstr_arity`, and `LBWfPeregrine.etaCtors` states the invariant on the emitted
program alone. `dearg_*` is the typed pipeline and never runs on Lean output.

**Q6 — `FirstOrderInd`.** Adopt Q6.2's definition verbatim (it elaborates clean at the pin), over
`VEnv.WF`'s declaration list, with `fo : Name → Prop` a stratification parameter. Cite `[S §7.3]`
as the **origin**, never as a transcription: the shipped `firstorder_ind` computes `false` on
`nat` (F1, reproduced three ways). `[L Def. 14]` ≡ the `fields` clause; `[L Def. 6]` is
`firstorder_no_box`'s *conclusion*, not the predicate — the fidelity table gets two rows, not one.

**Q7 — `Quot`: restrict.** New **N16**: no `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` in a
computationally relevant position, as a conjunct of `Supported`. `Quot.sound` is **not**
excluded (Prop-typed, hence `Erasable`, hence boxed; it is in every realistic closure).
`ErasesDecl.quot` is deleted from T3. The `Quot.ind` theory/implementation divergence in
lean4lean is an upstream note (N15), not a row here.

**Q8 — mechanical comparison with MetaRocq's `erases`: the §3.3 table, and nothing more.** The
rule-by-rule table tracked next to `Erases.lean` is required (criterion 3) and is the review's
"most important missing fact". A Rocq transport reaching the relation is **explicitly dropped**:
`grep -rn Erases rocq/` is empty today, the transport programme was never scoped to the relation,
and the cheapest honest anchor is the table plus the fact that under this design each of the ten
rules is *literally* `TrExprS`'s corresponding rule with `VExpr` replaced by `LBTerm` — a
correspondence a reader can check by diffing two inductives in the same repository. Recorded as
a non-goal in the ledger.

### 2.2 The twenty-two acceptance criteria

| # | Criterion | How this design meets it |
|---|---|---|
| 1 | `Erases` has ten rules; signature mentions only `VEnv`, `List Name`, `VLCtx`, `Expr`, `LBTerm`; no `ErasureCtx` | §3.2. The `proj` rule's `np` comes from `env.pats` (`ProjParams`, §3.2), not from a registry; `const`'s kername comes from the total function `toKername` (`Basic.lean:35`). `ErasureContext.lean` is deleted. |
| 2 | No rule produces `.construct`, `.case`, `.fix` | §3.2 by inspection: ten rules, targets are `.box .bvar .fvar .const .app .lambda .letIn .proj` and (for `lit`/`mdata`) a recursive target. |
| 3 | Rule-by-rule table tracked next to `Erases.lean` | New file `doc/Erases-vs-Fig18.md`, CI-grepped for the identifiers it names (criterion 19). |
| 4 | One `SEval`, one environment relation, one hypothesis bundle, one ledger | §3.4 (`SEval` + `SEvalFlags`), §3.3 (`ErasesEnv`), §3.6 (`PrimSpec`), §3.11 (`test/Ledger.lean`). CI greps `inductive SEval` count = 1. |
| 5 | Every pass has an `optimize_correct`-shaped theorem and a guard; `LBLower.correct` composes | §3.5: `ctorInline`, `elimInline`, `optimize` are `LBPass`; `LBLower := elimInline ∘ ctorInline`; guards in the style of `Optimize.lean:1066`. |
| 6 | T5 has exactly five hypotheses, none named `Supported`/`Relevant`/`Iota*`/`*Consistent`/`*Hyps` | §4, T5. |
| 7 | `Subsingleton` appears once, in T3, derived — or one named class-C hypothesis with a ledger row, and `Acc.rec`/`Eq.rec`/`And.rec`/`Decidable` demonstrably inside the fragment either way | §3.3 `SubsingletonElim`, derived modulo the upstream inversion; class **C** with a ledger row until it lands. **Amendment**: `Acc.rec` is *not* inside the fragment under the honest criterion (Q2 §4) — it is N17 with its own row. `Eq.rec`, `And.rec`, `Iff.rec`, `False.rec`, `Decidable` are. |
| 8 | `FirstOrderInd` decidable, `decide`s on `Nat`, `Bool`, `List Nat`, `Nat × Nat`, `Tree` | **Amended** per F6: `Nat`, `Bool`, `Tree`. `List Nat`/`Nat × Nat` are outside `[S §7.3]`'s and `[L Def. 14]`'s predicates and outside Q6.2's; no benchmark needs them (all five return `Nat`). Decidability lives in `firstOrderIndB` on `Lean.Environment` with an adequacy lemma through `PrimSpec.ind_adequate` (§3.8). |
| 9 | `OracleDischarge` in the capstone's import closure; `oracle_sound` discharged | §3.6 field 4 is `ResidualHyps.orc_refl` renamed; the capstone imports `OracleDischarge`. Cost measured: 33 axioms (§3.11). |
| 10 | `sort_erasable`/`forallE_erasable` exist; the other fourteen panic sites tabulated | §4 T8, `Erases.sort_erasable`, `Erases.forallE_erasable`; `doc/panic-sites.md` names the premise excluding each of the remaining fourteen. |
| 11 | `Supported` decidable, `decide`s on the five programs, sparse-`casesOn` visible in it | §3.7 conjunct **S2**, named `Supported.plainCases`, with a docstring naming `_sparseCasesOn_` and `VerifyBench/STATUS.md`. |
| 12 | Capstone's conclusion contains `LBWfPeregrine` | **Amended** per Q5 §2.5: matching *the pipeline's precondition*, not what `validate` checks — `EWellformed(all_env_flags)` + `etaCtors` + `etaFix` (§3.10). One ledger row records that peregrine's own discharge of that precondition is `Admitted` (`Transforms.v:375`) and that `validate` omits η. |
| 13 | `arith_covered` elaborates under `lake build`, every T9 hypothesis inhabited | W6. Arith's residue is 4 compiler bodies (`Nat.add/mul/sub/pow`), 10 typeclass projections, 4 singleton `fix` blocks, a 19-node peano tower — all inside the fragment. |
| 14 | Per-program coverage table for all five | `VerifyBench/STATUS.md` rewritten as the T10 artefact; Quicksort's row states X2 explicitly. |
| 15 | `#print axioms` on T5/T6/T8/T9 matches a committed fixture; T6 prints class A | §3.11. The fixture carries 33 names including two `_native.bv_decide` axioms from Lean core. T6's passes are `LBTerm`-only and print `[propext, Quot.sound]` (measured today for `LBOptimize_correct`, `closeFix_substList_fixSubst`, `wcbvEval_mkApps_mkLambdas_substList`). |
| 16 | Every `sorryAx` root named with `file:line` at the pin; fork-authored distinguished | §3.11 rows (a1) inherited: `Injectivity.lean:12,21,34`, `UniqueTyping.lean:174`, `ChurchRosser.lean:1193,1212`; (a2) **fork-authored**: `EnvLemmas.lean:334 VEnv.WF.patsStrong`. |
| 17 | No `sorry`, no `axiom`; `PrimSpec` a structure; every class-C hypothesis a binder | §3.6, §4. CI grep. |
| 18 | Comment fraction < 20%; zero slice tags/hashes/dates/"used to" | §9. |
| 19 | Every backticked identifier resolves; every cited document exists | §9, CI grep. |
| 20 | Zero declarations outside the capstone closure except a tracked list | §5; the tracked exceptions are `optimize` (off-path by design, §1.1 move 4) and the non-vacuity guards. |
| 21 | No `Lean4Lean`-namespace declaration here | **Resolved, not waived**: of `CheckerAdequacy.lean`'s eight, seven (`kernelNGen`, `VContext.ofMLCtx` + three projections, `VState.WF.initial`, `M.WF.run'`) are kernel-generic and go upstream (N15, ask 4); `kernel_isErasable_sound` mentions `LeanToLambdaBox.isErasable` and is renamed into `LeanToLambdaBox`. Criterion 9 stays satisfiable. |
| 22 | Verified eraser on the branch consumers pin; CI builds it; committed pin = measured pin | W6: merge `dev/verify` → `main`, CI trigger on both, `lakefile.toml` pinning `20ec229` committed. |

### 2.3 Amendments to `00-REFERENCE-SPEC.md` this design requires

Each is a spec edit, not a code edit, and each is evidenced.

1. **T1 flags.** `eraseFlags := ⟨true, true, false⟩` = MetaRocq `default_wcbv_flags`
   (`EWcbvEval.v:69`) = peregrine's pipeline input (`Transforms.v:151`). The deliverable stops
   there; `targetFlags` in the spec's sense is **not** required for composition. Retain
   `optFlags := ⟨false, true, false⟩` (= `opt_wcbv_flags` = the tree's `appliedFlags`) as the
   optional post-`optimize` point. The tree's current `defaultFlags`/`optFlags`/`targetFlags` are
   block-form and are renamed `blockFlags*` or deleted (`Flags.lean:46-59`).
2. **T3 `ErasesDecl`.** `defn` reads `env.defeqs`, not `env.constants c = some ⟨_, some body⟩`
   (`VConstant` has no body, `Theory/VEnv.lean:6-9`). `recr` → `elim`, over `casesOn`-like
   constants only, because `getCasesInfo?` accepts only those (`isCasesOnLike`); recursors reached
   as constants are `ax` (measured: `Eq.rec` in `Fannkuch.ast`). `quot` deleted (Q7).
   New class `fixdefn` (move 2). New class `opaque` folded into `defn` via the compiler equation
   (Q3, F3).
3. **T6 pass list.** `ctorInline`, `elimInline`, `optimize`. `fixIntro` deleted (move 2);
   `natLower` stays out of scope (N3).
4. **T8 conclusion.** `∃ E t₀, ErasesEnv env E t₀ ∧ Erases env Us Δ (prepare e) t₀ ∧
   t = LBLower.term E.all t₀ ∧ s'.gdecls ≐ LBLower.env E`; subject is `prepare_erasure e`
   (Q1 §2.8). `PrimSpec` gains a fifth field (`ind_adequate`, F8).
5. **T7 signature.** `FirstOrderInd (env : VEnv) (fo : Name → Prop) (I : Name)` over `VEnv.WF`'s
   declaration list (F4); cited as *based on* `[S §7.3]` (F1).
6. **§2 T3's Subsingleton paragraph (`00-REFERENCE-SPEC.md:213-221`).** The claim that Lean's
   criterion is "verbatim `[L §3.3]`" is false (Q2 §4); the `Acc.rec` conclusion does not follow.
7. **N8** resolves as Q3(B) — one environment; delete the "or restrict" alternative.
8. **N16** (`Quot`), **N17** (`Acc.rec`/`WellFounded.fix`) added.
9. **Criteria 8, 12, 21** as in §2.2.

---

## 3. Core definitions

Namespace `LeanToLambdaBox` throughout unless stated.

### 3.1 `LBTerm` and flags

`LBTerm` is **unchanged** (`Basic.lean:90`, shipping). It already carries `.fvar`, `.prim`,
`List BinderName` on branches, and no `tCoFix`. §8: no transpiler edit.

```lean
-- Semantics/Flags.lean, replacing the four current constants
/-- MetaRocq `EWcbvEval.default_wcbv_flags`; peregrine's `untyped_transform_pipeline` input. -/
def eraseFlags  : WcbvFlags := ⟨with_prop_case := true,  with_guarded_fix := true,
                                with_constructor_as_block := false⟩
/-- MetaRocq `EWcbvEval.opt_wcbv_flags`; the point `optimize` lands on. -/
def optFlags    : WcbvFlags := ⟨false, true,  false⟩
/-- MetaRocq `EWcbvEval.target_wcbv_flags`; not used by this development. -/
def targetFlags : WcbvFlags := ⟨false, false, false⟩
```

### 3.2 `Erases` — T2, ten rules

```lean
/-- `S`'s parameter count, read off the ι-rule key `TrProjCtor.pat` uses
(`Verify/Typing/Expr.lean:93`). Unique under `env.WF` (`ProjParams.uniq`). -/
def ProjParams (env : VEnv) (S : Name) (np : Nat) : Prop :=
  ∃ c nf r, env.pats (SimplePattern.iota (mkRecName S) (np+1+1+0) c (np+nf)).toPattern r

/-- The `InductiveId` `register_inductive` computes for a structure (`all = [S]`, `idx = 0`). -/
def indIdOf (S : Name) : InductiveId := ⟨rootKername (toString S), 0⟩

inductive Erases (env : VEnv) (Us : List Name) : VLCtx → Expr → LBTerm → Prop
  | box   {Δ e ve} (htr : TrExprS env Us Δ e ve)
          (her : Erasable env Us.length Δ.toCtx ve) :
            Erases env Us Δ e .box
  | bvar  {Δ i e' A} (h : Δ.find? (.inl i) = some (e', A)) :
            Erases env Us Δ (.bvar i) (.bvar i)
  | fvar  {Δ x e' A} (h : Δ.find? (.inr x) = some (e', A)) :
            Erases env Us Δ (.fvar x) (.fvar x)
  | const {Δ} (c : Name) (us : List Level) {ci} (h : env.constants c = some ci) :
            Erases env Us Δ (.const c us) (.const (toKername c))
  | app   {Δ f f' a a'} (hf : Erases env Us Δ f f') (ha : Erases env Us Δ a a') :
            Erases env Us Δ (.app f a) (.app f' a')
  | lam   {Δ n ty bi b b'} {ty' : VExpr} (hty : TrExprS env Us Δ ty ty')
          (hb : Erases env Us ((none, .vlam ty') :: Δ) b b') :
            Erases env Us Δ (.lam n ty b bi) (.lambda (nameToBinder n) b')
  | letE  {Δ n ty nd v v' b b'} {ty' val' : VExpr}
          (hty : TrExprS env Us Δ ty ty') (hval : TrExprS env Us Δ v val')
          (hv : Erases env Us Δ v v')
          (hb : Erases env Us ((none, .vlet ty' val') :: Δ) b b') :
            Erases env Us Δ (.letE n ty v b nd) (.letIn (nameToBinder n) v' b')
  | proj  {Δ} (S : Name) (i np : Nat) {e t} (hnp : ProjParams env S np)
          (hd : Erases env Us Δ e t) :
            Erases env Us Δ (.proj S i e) (.proj ⟨indIdOf S, np, i⟩ t)
  | lit   {Δ} {l : Literal} {t} (hcl : env.ContainsLits l)
          (h : Erases env Us Δ l.toConstructor t) :
            Erases env Us Δ (.lit l) t
  | mdata {Δ d e t} (h : Erases env Us Δ e t) :
            Erases env Us Δ (.mdata d e) t
```

Notes. `nameToBinder` (`ErasureContext.lean:249`) is `fvar_to_name`'s ASCII filter
(`Erasure.lean:245-252`) as a pure function — carried over, the file it lives in is deleted, the
definition moves to `Erases.lean`. `Erases.proj` deliberately carries no `TrExprS` premise
(`TrProj.uniq` gives `IsDefEqU`, not equality). The relation is a function of its inputs except
at `box`: `Erases.deterministic_of_not_erasable` (T7's engine) is the statement.

*Metatheory carried* (all re-anchored, statements lose the `Γ` index and their six dead arms):
`erases_shift`, `erases_subst`, `Erases.abstract`, `Erases.uninstantiate`, `Erases.thin_vlet`,
`erases_weakFV`, `erases_uniform_closed`, plus `Erases.sort_erasable`/`forallE_erasable`
(criterion 10) which are new and two lines each given `Erasable`'s definition.

### 3.3 `ErasesDecl` / `ErasesEnv` — T3

```lean
/-- The two halves of the specification environment. `decls` is the deliverable — inductives and
erased constants, one per declaration the run registers. `lib` is the inlining library — one
declaration per constructor constant and one per `casesOn`-like constant reached — which the
lowering passes consume and `LBLower.env` drops. -/
structure ErasedEnv where
  decls : GlobalDeclarations
  lib   : GlobalDeclarations
def ErasedEnv.all (E : ErasedEnv) : GlobalDeclarations := E.decls ++ E.lib

/-- `mkCtorBody iid k names` = `λ names. (.construct iid k []) (bvars names)`, η-expanded at
`cstr_arity = npars + nfields`. -/
def mkCtorBody (iid : InductiveId) (k : Nat) (names : List BinderName) : LBTerm

/-- `mkElimBody iid np npre nfs` = the λ□ body of a plain `casesOn`: `npre` leading binders
(parameters, motive, and the discriminant at `discrPos`), one binder per minor, and a `.case`
selecting on the discriminant with alternative `j` applying minor `j` to its `nfs[j]` fields. -/
def mkElimBody (iid : InductiveId) (np discrPos npre : Nat)
    (pre : List BinderName) (nfs : List (List BinderName)) : LBTerm

/-- `mkFixDefs bodies names` closes each body over the block's own constants, in block order:
`.const (toKername cⱼ)` becomes the fix binder `j`, using `Semantics.fixSubst`'s convention
(`Substitution.lean:220`, MetaRocq `fix_subst`, matching `Erasure.mkDef`). -/
def mkFixDefs (cs : List Name) (bodies : List LBTerm) : List (@FixDef LBTerm)

/-- `c` refers to itself in `body` — shipping's `Erasure.name_occurs` as a `Prop`
(`name_occurs_iff_selfRefers` proves them equal). -/
def SelfRefers (c : Name) (e : Expr) : Prop

inductive ErasesDecl (env : VEnv) : Name → GlobalDecl → Prop
  /-- A non-recursive constant: the compiler's defining equation, erased. -/
  | defn  {c n us body ty b'}
          (hd : env.defeqs ⟨n, .const c us, body, ty⟩)
          (hnr : ¬ SelfRefers c src)                                  -- src ↦ body under TrExprS
          (h  : Erases env lvls [] src b') :
            ErasesDecl env c (.constantDecl ⟨some b'⟩)
  /-- A mutual block `cs` in `ci.all` order; member `i`. -/
  | fixdefn {cs : List Name} {srcs : List Expr} {bs : List LBTerm} {i : Nat}
          (hblock : ∀ j, env.defeqs ⟨_, .const cs[j]! _, _, _⟩)
          (hrec  : ∃ j, SelfRefers cs[j]! srcs[j]!)
          (h     : ∀ j, Erases env lvls [] srcs[j]! bs[j]!) (hi : i < cs.length) :
            ErasesDecl env cs[i]! (.constantDecl ⟨some (.fix (mkFixDefs cs bs) i)⟩)
  /-- No defining equation: axioms, `@[extern] .preferAxiom`, recursors, `Quot` primitives. -/
  | ax    {c ci} (h : env.constants c = some ci) (hno : ∀ d, ¬ IsDefnOf env c d) :
            ErasesDecl env c (.constantDecl ⟨none⟩)
  /-- The mutual inductive block, as `register_inductive` builds it. -/
  | ind   {I decl} (h : HasInduct env decl) (hmatch : IndDeclMatches decl body) :
            ErasesDecl env (blockNameOf decl) (.inductiveDecl body)
  /-- Library: a constructor constant. -/
  | ctor  {c iid k names} (h : CtorOf env c iid k names) :
            ErasesDecl env c (.constantDecl ⟨some (mkCtorBody iid k names)⟩)
  /-- Library: a plain `casesOn`-like constant. Carries the `[S Fig. 18]` side condition. -/
  | elim  {C I iid np dp npre pre nfs}
          (hC   : CasesOnOf env C I iid np dp npre pre nfs)
          (hsub : IsPropositional env I → SubsingletonElim env I) :
            ErasesDecl env C (.constantDecl ⟨some (mkElimBody iid np dp npre pre nfs)⟩)

/-- `erases_deps` (`[S §7.4]`): bottom-up, dependency-selective. Every kername occurring in `t`
or in a body of `E.all` has a declaration in `E.all` produced by `ErasesDecl`, `E.decls` and
`E.lib` are disjoint with `Nodup` keys, and `E.lib` holds exactly the `ctor`/`elim` classes. -/
inductive ErasesEnv (env : VEnv) : ErasedEnv → LBTerm → Prop
```

`ElimSpec`, the ι-reproduction obligation, is discharged **by construction** rather than assumed:

```lean
/-- `mkElimBody` reproduces the ι rule: applying it to parameters, a motive, a constructor spine
and the minors evaluates exactly as `iota_red` does. Class **A** — `LBTerm` only. -/
theorem mkElimBody_iota {Σ fl iid np dp npre pre nfs k args minors r}
    (hk : k < nfs.length) (harity : (args.drop np).length = nfs[k]!.length)
    (hprop : isPropositionalInductive Σ iid = false) :
    WcbvEval Σ fl (mkApps (mkElimBody iid np dp npre pre nfs)
                          (pre' ++ [mkApps (.construct iid k []) args] ++ minors)) r ↔
    WcbvEval Σ fl (mkApps minors[k]! (args.drop np)) r

/-- The `with_prop_case` companion: a subsingleton discriminant that erases to `□`. -/
theorem mkElimBody_iota_sing {Σ iid np dp npre pre nfs minors r}
    (hprop : isPropositionalInductive Σ iid = true) (hsing : nfs.length = 1) :
    WcbvEval Σ eraseFlags (mkApps (mkElimBody …) (pre' ++ [.box] ++ minors)) r ↔
    WcbvEval Σ eraseFlags (mkApps minors[0]! (List.replicate nfs[0]!.length .box)) r
```

`SubsingletonElim` (Q2 §2.2, first cut — proof fields only):

```lean
def SubsingletonElim (env : VEnv) (I : Name) : Prop :=
  ∃ decl t ℓ, HasInduct env decl ∧ decl.types = [t] ∧ t.name = I ∧ ¬ ℓ.IsNeverZero ∧
    (t.ctors = [] ∨ ∃ c, t.ctors = [c] ∧
      ∀ i < c.type.piArity - decl.nparams, ∃ F,
        c.type.piBinders[decl.nparams + i]? = some F ∧
        env.HasType decl.uvars (c.type.fieldCtx decl.nparams i) F (.sort .zero))

/-- Derived from `env.WF` once `VEnv.WF'.consts_origin` lands upstream (Q2 §2.3 L1-L6). -/
theorem subsingletonElim_of_wf (henv : env.WF) (hrec : env.constants (mkRecName I) = some ci)
    (hlarge : ci.uvars = declUvars + 1) (hproofFields : …) : SubsingletonElim env I
```

### 3.4 `SEval` and `SEvalFlags` — T4

```lean
structure SEvalFlags where beta, delta, zeta, iota, proj, lit : Bool
  deriving DecidableEq
instance : LE SEvalFlags := ⟨fun a b => a.beta ≤ b.beta ∧ … ⟩
def fullFlags : SEvalFlags := ⟨true, true, true, true, true, true⟩

inductive SEval (env : VEnv) (Us : List Name) (fl : SEvalFlags) : VLCtx → Expr → Expr → Prop
  -- one rule per enabled reduction, each gated on the corresponding field:
  -- beta, delta (env.defeqs — the compiler's equations, Q3), zeta, iota (env.pats),
  -- proj, lit (Expr.toConstructor), plus congruence/value rules.

theorem SEval.mono  (h : fl ≤ fl') : SEval env Us fl Δ e v → SEval env Us fl' Δ e v
theorem SEval.defeq (henv : env.WF) (hΔ : VLCtx.WF env Us.length Δ)
    (htr : TrExprS env Us Δ e ve) (hev : SEval env Us fl Δ e v) :
    ∃ vv, TrExprS env Us Δ v vv ∧ env.IsDefEqU Us.length Δ.toCtx ve vv
```

`SEval.defeq` is written **once**, over the abstract spine schema
`SEvalβζδ_defeq_spine` (`SubjectReductionFull.lean:309`) instantiated per rule — the reuse
inventory identifies that schema as the single-relation template. ζ is enabled at the capstone
(`fullFlags`), closing the spec's "no capstone can evaluate a `let`" coverage bug.

### 3.5 The pass layer — T6

```lean
structure LBPass where
  term       : GlobalDeclarations → LBTerm → LBTerm
  env        : GlobalDeclarations → GlobalDeclarations
  flIn flOut : WcbvFlags
  correct    : ∀ {Σ t v}, LBWf Σ → LBClosed t 0 →
               WcbvEval Σ flIn t v → WcbvEval (env Σ) flOut (term Σ t) (term Σ v)

/-- Equal on every lookup, with distinct keys — the only property `WcbvEval`,
`constructorArity` and `isPropositionalInductive` read of an environment. -/
def EnvAgree (Σ Σ' : GlobalDeclarations) : Prop :=
  (∀ kn, LBTerm.envLookup Σ kn = LBTerm.envLookup Σ' kn) ∧
  (Σ.map Prod.fst).Nodup ∧ (Σ'.map Prod.fst).Nodup
infix:50 " ≐ " => EnvAgree
theorem WcbvEval.congr_env (h : Σ ≐ Σ') : WcbvEval Σ fl t v → WcbvEval Σ' fl t v

def ctorInline : LBPass  -- flIn = flOut = eraseFlags
def elimInline : LBPass  -- flIn = flOut = eraseFlags
def optimize   : LBPass  -- flIn = eraseFlags, flOut = optFlags  (off the shipping path)

def LBLower : LBPass := elimInline.comp ctorInline
/-- The deliverable environment: lower every body, then drop the library. -/
def LBLower.env (E : ErasedEnv) : GlobalDeclarations :=
  (E.decls.map fun (kn, d) => (kn, d.mapBody (LBLower.term E.all))) 
```

`ctorInline.term Σ t` rewrites, bottom-up: at `mkApps (.const kn) args` where
`envLookup Σ kn = some (.constantDecl ⟨some b⟩)` and `isCtorBody b = some (iid, k, names)`, emit
`mkApps (.construct iid k []) args` when `args.length ≥ names.length`, otherwise
`mkLambdas (names.drop args.length) (mkApps (.construct iid k []) (args ++ bvars))`.
`elimInline.term Σ t` likewise, at `isElimBody b = some sh` with `args.length ≥ sh.arity`:
`mkApps (.case (sh.iid, sh.np) args[sh.discrPos] (alts sh args)) (args.drop sh.arity)`, where
`alts` splits each minor by `splitLambdas` and, if a minor is not a λ-chain of the right length,
the pass is the identity at that node (which `Supported.S3` then makes unreachable).

Hardest lemmas, both already in hand: `elimInline.correct` consumes
`IotaBridge.wcbvEval_mkApps_mkLambdas_substList` (`IotaBridge.lean:111`, class A) and
`mkElimBody_iota`; `ctorInline.correct` is δ + β + `mkApps_construct_inj`
(`Substitution.lean:177`). `optimize.correct` is `LBOptimize_correct` (`Optimize.lean:927`,
class A) **generalised over `with_constructor_as_block`**: 14 of 22 arms transfer verbatim, 3
block arms die, 4 (`construct_atom`, `construct_app`, `iota`, `proj`) are new, `fix_unguarded`
stays unreachable.

Each pass ships a non-vacuity guard in the style of `Optimize.lean:1066` /
`Semantics/Metatheory.lean:417`.

### 3.6 `PrimSpec` — T8's one interface

```lean
structure PrimSpec (lenv : Lean.Environment) (env : VEnv) (Us : List Name)
    (gw : Void IO.RealWorld → NameGenerator) : Prop where
  /-- 1. The `VEnv` is the *compiler's*: `lenv`'s kernel translation extended by one
  `VEnv.addDefEq` per declaration whose body `Compiler.LCNF.getDeclInfo?` returns
  (`_unsafe_rec`). Functional: `abs_env_irr`. Class **D**. -/
  env_connect : TrEnvC lenv env ∧ ∀ env', TrEnvC lenv env' → env' = env
  /-- 2. `getConstInfo`, `getCasesInfo?`, `getCtorArity?`, `getDeclInfo?` agree with
  `env_connect` — including `ci.all`'s order, which is `ErasesDecl.fixdefn`'s block order.
  Class **D**. Today: `ResidualHyps.cases_run` + `ctor_run` (`OracleDischarge.lean:65`). -/
  lookup_adequate : …
  /-- 3. `getConstInfo I : inductInfo` corresponds to a `VInductDecl` in `env`'s declaration
  list with matching `types`/`ctors`/`nparams`/`uvars` (F8). Class **D**. -/
  ind_adequate : …
  /-- 4. `mkFreshFVarId` returns identifiers absent from the ambient context. Class **D**.
  Today: `ResidualHyps.fresh_run`. -/
  fresh_names : …
  /-- 5. `Erasure.isErasable lparams e = true → Erasable env …`. **Discharged**, not assumed,
  through `Relevance.isErasable` → `isErasable.WF` → `kernel_isErasable_sound`. Class **B**. -/
  oracle_sound : …
```

Built by renaming `OracleDischarge.ResidualHyps` (four fields, already the right shape) and
adding fields 1 and 3. Completeness of the oracle is **not built** (`[S §7.2]`'s `CumulProp`
apparatus is unnecessary: Lean has no `Prop ≤ Type`).

### 3.7 `Supported` — the fragment, decidable, on `e` and its closure

```lean
/-- Decidable, over `e` and every declaration in its dependency closure. Each conjunct is a
`Bool`-valued check on `Lean.Environment` plus its `Prop` reflection. -/
structure Supported (lenv : Lean.Environment) (e : Expr) : Prop where
  noMeta      : no `.mvar`; `#erase` runs `instantiateMVars` first
  noStrLit    : no `Literal.strVal`                                        -- N6, panic site
  plainCases  : every `casesOn`-like head reached has `altNumParams` all `.ctor` and no
                side-condition argument — **the sparse-`casesOn` hole, named here** (X2)
  lamMinors   : every minor of every `casesOn` application is a syntactic λ-chain of the
                alternative's field arity (X1)
  noQuot      : no `Quot`/`Quot.mk`/`Quot.lift`/`Quot.ind` in a relevant position (N16);
                `Quot.sound` is *not* excluded
  noAccRec    : no `Acc.rec`/`WellFounded.fix` in a relevant position (N17, Q2 §4)
  noRuntime   : no `IO`, `Task`, `String`, `UInt*`, `Float`, `@[implemented_by]`,
                computed fields (N6)
  compilerBodies : reported, not excluded — the list of closure declarations whose body is the
                `_unsafe_rec` one (Q3: 4 in Arith, 33 across the suite)
```

`Supported.plainCases`'s docstring names `quicksort_fuel._sparseCasesOn_1` and
`VerifyBench/STATUS.md`; that is criterion 11's requirement that the hole be visible where a
reader audits it.

### 3.8 `FirstOrderInd` — T7

Q6.2's definition verbatim (it elaborates clean at the pin), plus the decidable checker:

```lean
def VEnv.HasInduct (env : VEnv) (decl : VInductDecl) : Prop :=
  ∃ ds, VEnv.WF' ds env ∧ VDecl.induct decl ∈ ds
def FOType (fo : Name → Prop) (n k : Nat) : VExpr → Prop
structure VInductDecl.FirstOrder (env : VEnv) (fo : Name → Prop) (decl : VInductDecl) : Prop where
  mono, informative, noIndices, fields
def FirstOrderInd (env : VEnv) (fo : Name → Prop) (I : Name) : Prop

/-- Decidable on `Lean.Environment`; `fuel = lenv.constants.size` always suffices. -/
def firstOrderIndB (lenv : Lean.Environment) (fuel : Nat) (I : Name) : Bool
theorem firstOrderIndB_sound (P : PrimSpec lenv env Us gw) :
    firstOrderIndB lenv fuel I = true → FirstOrderInd env fo I
```

### 3.9 `ErasableAxioms` and `AxiomSpec` — T9

```lean
/-- The assumed realizer behaviour of one relevant axiom (`@[extern]`, `Eq.rec`). -/
structure AxiomSpec where
  kn      : Kername
  arity   : Nat
  realizes : LBTerm → List LBTerm → LBTerm → Prop
/-- Every body-less declaration in the erased closure is either Prop-typed at the source —
hence `Erasable`, hence boxed, hence never a stuck head in a relevant position — or named in
an enumerated `AxiomSpec` list. `Classical.choice` is neither, and dependency tracking
(`ErasesEnv`) excludes it for free. -/
structure ErasableAxioms (env : VEnv) (e : Expr) : Prop where
  propTyped : ∀ c ∈ axiomClosure e, IsPropTyped env c ∨ c ∈ specs.map (·.kn)
  specs     : List AxiomSpec
```

This is the change that moves benchmark coverage off zero: `propext`, `Quot.sound` and
`Classical.choice` are in every realistic closure, `axiom_free` is uninhabited in Lean, and
Fannkuch's `Eq.rec` is exactly an `AxiomSpec` row.

### 3.10 `LBWfPeregrine` — the output boundary

Q5 §2.4 verbatim: `EWellformed(all_env_flags)` — `Nodup` keys, declarations well-formed in the
preceding prefix, `LBClosed t 0`, every `tConst` resolves, `.construct … blk` with `blk = []`,
branch count = constructor count, `.fix` index in range with every `dbody` a λ, projections
resolve, `ind_npars` unconstrained — **plus** the two conjuncts the pipeline requires and
`validate` omits: `etaCtors` (every constructor spine ≥ `Σ.cstrArity iid k = ind_npars +
cstr_nargs`, measured 982/982 saturated, 0 under-applied) and `etaFix`
(`EEtaExpandedFix.expanded`). `NoBlock t` and `LBClosed t 0` come free and unconditionally from
`visitExpr_shape_all` (`ColdStartInduction.lean:1104`).

**Open sub-question inherited from Q3 §2.4 and scheduled in W1:** `etaFix` was not verified on
the five programs (the eraser carries its own `-- TODO: eta-expand fixpoints?` at
`Erasure.lean:911`). W1's acceptance test measures `EEtaExpandedFix.expanded` on all five `.ast`
before T9's conclusion is committed to it. If it fails, the honest move is a ledger row plus an
upstream report — not a weaker predicate matched to what the frontend happens to emit.

### 3.11 The ledger — T11

```lean
-- test/Ledger.lean, run in CI, diffed against test/ledger.expected
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorder
#print axioms LeanToLambdaBox.visitExpr_refines_erases
#print axioms LeanToLambdaBox.erases_correct
#print axioms LeanToLambdaBox.LBLower_correct
#print axioms LeanToLambdaBox.arith_covered
```

Rows: **(a1)** inherited `sorryAx`, at `20ec229`: `Injectivity.lean:12,21,34`,
`UniqueTyping.lean:174`, `ChurchRosser.lean:1193,1212`, reaching here through `TrExprS.uniq` and
`IsDefEq.uniqU`. **(a2)** fork-authored `sorryAx`: `EnvLemmas.lean:334 VEnv.WF.patsStrong`,
labelled as this project's own hole, not inherited. **(a3)** the lean4lean executable checker:
29 non-standard names including two `_native.bv_decide` axioms from Lean core, entering through
criterion 9. **(b)** `PrimSpec` fields 1–4, class **D**. **(c)** class-**C** hypotheses: `hcfg`,
`hsup`, `hax`, `hfo`, `hev`, and `SubsingletonElim` until the upstream inversion lands.
**(d)** class-**E** rows: N10 `.ast` serialisation (`Printing.lean`'s `Serialize` has zero
coverage; peregrine's `theories/serialization/` Sound/Complete proofs are the counterpart on the
other side), N11 `.inlinings`/`.mli`/`eraseElab`, the Q3 compiler/kernel body gap, peregrine's
`Admitted` pipeline precondition (`Transforms.v:375`) and `validate`'s missing η check, N14 AST
size with the `.peano`/hygiene measurement, N16 `Quot`, N17 `Acc.rec`, and the MetaRocq
`firstorder_ind` defect (F1) as an upstream report. **No prose copy exists anywhere else.**

---

## 4. Theorems

### T1 — λ□ syntax and evaluation
Unchanged from the tree (`Semantics/*`, 1,225 lines, class A, flag-polymorphic): 22 rules
including `app_box`, `iota_sing` (gated `with_prop_case`), `fix_guarded`;
`eval_deterministic`/`eval_value`/`value_final` with guards. Only the four flag constants change
(§3.1) and `Flags.lean:19-24`'s false header is rewritten.

### T2 — `Erases`
§3.2. Class **B** (the `box` rule's witness is `TrExprS` + `HasType`).

### T3 — `ErasesDecl` / `ErasesEnv`
§3.3. Class **B**, except `mkElimBody_iota`/`mkElimBody_iota_sing`, which are class **A**, and
`SubsingletonElim`, class **C** until the upstream inversion lands.

### T4 — subject reduction
```lean
theorem SEval.defeq (henv : env.WF) {Us Δ} (hΔ : VLCtx.WF env Us.length Δ)
    {e v ve} (htr : TrExprS env Us Δ e ve) (hev : SEval env Us fl Δ e v) :
    ∃ vv, TrExprS env Us Δ v vv ∧ env.IsDefEqU Us.length Δ.toCtx ve vv
```
Exactly five binders; no `SEnvConsistent`, no `IotaConsistent`, no `ProjConsistent` — the ι arm's
premises are supplied by `env.WF` through `VEnv.pats`, and the proj arm's by `TrProj`. Class **B**.

### T5 — `erases_correct`
```lean
theorem erases_correct
    (henv : env.WF) (hwt : TrExprS env Us [] e ve)
    (hev  : SEval env Us fl [] e v)
    (her  : Erases env Us [] e t)
    (hΣ   : ErasesEnv env E t) :
    ∃ v', Erases env Us [] v v' ∧ WcbvEval E.all eraseFlags t v'
```
Five hypotheses, none named `Supported`/`Relevant`/`Iota*`/`*Consistent`/`*Hyps`. The value's
erasure is existential — that is why a relation exists. Induction on `hev`, inversion on `her`,
each case splitting "erased structurally" / "erased to `□`"; the box arms consume `app_box`,
`iota_sing`, the fixpoint rule; β consumes `erases_subst`; δ and ι consume `ErasesEnv`
(δ through `ErasesDecl.defn`/`fixdefn`, ι through `ErasesDecl.elim` and `mkElimBody_iota`); the
`Erasable` premise is carried across steps by `SEval.defeq`. Class **B**.

Note the conclusion is at `E.all`, the *specification* environment (library included). T9
transports it to the deliverable `Σ` by `LBLower.correct` and `WcbvEval.congr_env`.

### T6 — the passes
```lean
theorem LBLower_correct {Σ t v} (hwf : LBWf Σ) (hcl : LBClosed t 0) :
    WcbvEval Σ eraseFlags t v →
    WcbvEval (LBLower.env' Σ) eraseFlags (LBLower.term Σ t) (LBLower.term Σ v)
theorem optimize_correct {Σ t v} … :
    WcbvEval Σ eraseFlags t v → WcbvEval (optimize.env Σ) optFlags (optimize.term Σ t) (optimize.term Σ v)
```
Class **A** throughout: every pass mentions `LBTerm` and `GlobalDeclarations` only — no
lean4lean, no `Expr`. Each ships a non-vacuity guard.

### T7 — first-order uniqueness
```lean
theorem firstorder_erases_deterministic
    (henv : env.WF) (hfo : FirstOrderInd env fo I)
    (hwt : TrExprS env Us [] v vv)
    (hty : env.HasType Us.length [] vv ((VExpr.const I us).mkApps args))
    (hval : SEval env Us fl [] v v)
    (h₁ : Erases env Us [] v t₁) (h₂ : Erases env Us [] v t₂) : t₁ = t₂

theorem firstorder_no_box
    (henv : env.WF) (hfo : FirstOrderInd env fo I) (hwt : …) (hty : …) (hval : …)
    (h : Erases env Us [] v t) : NoBox t
```
Proof content: `informativeType_not_erasable` (`FirstOrder.lean:103`) carries **unchanged** — it
is stated over `InformativeType`, which mentions neither `Γ` nor a constructor spine. The one
genuinely new obligation is the bridge `FirstOrderInd env fo I → HasType vv (mkApps (.const I us)
args) → InformativeType env Us [] v`. Class **B** (`TrExprS.uniq`, `IsDefEq.uniqU`).

### T8 — the bridge
```lean
theorem visitExpr_refines_erases
    (P    : PrimSpec lenv env Us gw)
    (hcfg : cfg.csimp = false ∧ cfg.nat = .peano ∧
            cfg.remove_irrel_constr_args = false ∧ cfg.extern = .preferLogical ∧
            cfg.auto_inline_typeclass_dispatch = false)
    (hwt  : TrExprS env Us Δ pe ve)
    (hsup : Supported lenv pe)
    (hinv : BridgeInv env Us cfg (gw w) ctx s Δ)
    (hrun : Erasure.visitExpr pe s ctx cctx ref w = .ok (t, s') w') :
    ∃ E t₀, ErasesEnv env E t₀
          ∧ Erases env Us Δ pe t₀
          ∧ t = LBLower.term E.all t₀
          ∧ s'.gdecls ≐ LBLower.env E ++ s.gdecls
          ∧ RunConcl s s' ∧ gw w ≤ gw w'
```
Subject: the real `partial_fixpoint` family, one induction, eighteen motives.
`BridgeInv` keeps seven of its ten fields (`mlc`, `lparams`, `cfg`, `kfresh`, `reserved`,
`knames`, `consts`); `natcfg` is redundant with `hcfg`, and `fixvars`/`fixfresh` die with
`Erases.fixvar`.

*Panics.* `.ok` does not exclude a panicked run. Two of the sixteen sites are **refuted by
lemma** — `Erases.sort_erasable` and `Erases.forallE_erasable` show a well-typed `.sort`/
`.forallE` is always `Erasable`, so the oracle fires first and `visitExpr`'s `unreachable!` arm
is unreachable (criterion 10). The remaining fourteen are enumerated in `doc/panic-sites.md`
with the premise excluding each: `.mvar` by `TrExprS`, `strVal` and machine-`Nat` by `hcfg`+
`Supported`, the sparse-`casesOn` and per-ctor-eliminator sites by `Supported.plainCases`,
the `getConstInfo` mismatch sites by `PrimSpec.lookup_adequate`.

*Subject is `prepare_erasure e`.* `run_prepare_erasure_ok` (`ColdStartRun.lean:169`) decomposes
it into `replaceUnsafeRecNames`, `macroInline`, `inlineMatchers`, `macroInline` under
`hcsimp`; `prepare_sound_of_prepareHyps` (`:589`) is re-aimed at T4's single `SEval` and supplies
`SEval env Us fl [] (prepare e) v ↔ SEval env Us fl [] e v` for the fragment. Class **B**;
`PrimSpec` 1–4 class **D**, field 5 class **B**.

### T9 — the capstone
§1.2. Composition, mirroring `[S §7.3]`: T8 puts the output in `Erases ; LBLower`; T5 simulates
the source evaluation into λ□ at `eraseFlags` **over `E.all`**; `LBLower_correct` +
`WcbvEval.congr_env` carry it to the deliverable `Σ`; T7 identifies the value's erasure uniquely
and shows it box-free. `erase_run_ok` (`ColdStartRun.lean:651`) supplies the decomposition
`erase = prepare_erasure ; visitExpr` with `Σ`, `t` and `inls` produced by the run — the current
tree's durable contribution, carried verbatim. Class **B** plus the class-**C** binders.

### T10 — non-vacuity
```lean
example : Supported lenv (expr_of benchArith)                := by decide
example : ErasableAxioms env (expr_of benchArith)            := by decide
example : FirstOrderInd env fo ``Nat                          := by decide  -- via firstOrderIndB_sound
example : firstOrderIndB lenv fuel ``Bool = true               := by decide
example : firstOrderIndB lenv fuel ``VerifyBench.Tree = true   := by decide
theorem arith_covered : <T9 instantiated at benchArith>       := …
```
plus `test/CompilerBodies.lean` discharging `PrimSpec.env_connect`'s `WF` obligation for
`Nat.add`, `Nat.mul`, `Nat.sub`, `Nat.pow` (four `TrExprS` + `HasType` checks; Q3 measured all
four true) and the rewritten `VerifyBench/STATUS.md` coverage table for all five programs.
Class **A** for the discharges.

### T11 — the ledger
§3.11. Class **A** (it is a measurement).

---

## 5. Module plan

`new` = written from scratch. `carried` = statement unchanged. `re-anchored` = statement changes,
proof skeleton and lemma inventory survive. `deleted` = no proved statement lost.

### 5.1 Shipping — untouched

| Module | Lines | Status |
|---|---|---|
| `LeanToLambdaBox/Basic.lean` | 236 | carried (shipping; `LBTerm`, `toBvar` family, `toKername`) |
| `LeanToLambdaBox/Erasure.lean` | 1,018 | carried (shipping; T8's subject) |
| `LeanToLambdaBox/Printing.lean` | 168 | carried (shipping; N10 ledger row) |

### 5.2 Carried

| Module | Lines | Change |
|---|---|---|
| `Semantics/Flags.lean` | 61 | four flag constants redefined (§3.1); `:19-24` header rewritten |
| `Semantics/Values.lean` | 132 | none |
| `Semantics/Eval.lean` | 257 | none |
| `Semantics/Env.lean` | 52 | none |
| `Semantics/Substitution.lean` | 223 | none |
| `Semantics/Metatheory.lean` | 500 | none (all flag-polymorphic) |
| `Closed.lean` | 871 | delete the `subst_shift_cancel` duplicate |
| `Abstract.lean` | 423 | none |
| `FixMetatheory.lean` | 183 | none; consumer becomes `ErasesDecl.fixdefn` |
| `FixUnfold.lean` | 1,001 | none; `closeFix_substList_fixSubst` becomes `mkFixDefs`'s pivot |
| `IotaBridge.lean` | 207 | none; consumer becomes `elimInline.correct` |
| `Erasability.lean` | 230 | none |
| `Relevance.lean` | 54 | none |
| `RelevanceCheck.lean` | 175 | none |
| `OracleDischarge.lean` | 123 | `ResidualHyps` renamed `PrimSpec`, +2 fields (§3.6) |
| `FirstOrder.lean:49-155` | ~110 | `InformativeType` + `informativeType_not_erasable` carried; the other 650 lines deleted |
| `VerifyBench/*` | 520 | becomes the T10 artefact; `STATUS.md` rewritten |

### 5.3 Re-anchored

| Module | Lines | What changes |
|---|---|---|
| `Optimize.lean` | 1,090 | generalise `LBOptimize_correct` over `with_constructor_as_block`; 4 new arms (`construct_atom`, `construct_app`, `iota`, `proj`), 3 block arms retired; becomes T6 `optimize`, off the shipping path |
| `ErasureRun.lean` | 3,234 | survives intact — 74 `run_*`, `RunConcl`, the admissibility/`⊑` kit, `mutual_le_of`; `RunConclδ` (in `DeltaHyps`) replaced by `RunConcl` + `ErasesEnv` |
| `VisitExprRefines.lean` | 4,641 | scaffolding, admissibility, `⊑`, binder/telescope lemmas and run plumbing survive; 18 motive conclusions restated (7 mechanical, 3 environment-facing, 8 pass-facing); `BridgeInv` keeps 7 of 10 fields |
| `Erases.lean` | 1,426 | rewritten to §3.2 (10 rules); the transport half and the `natLit`/`proj` fixtures survive |
| `ErasesAbstract.lean` | 298 | `Erases.abstract`/`uninstantiate`, six arms dropped |
| `ErasesStrengthen.lean` | 747 | `thin_vlet`/`weakFV` family, six arms dropped; the three kernel-generic `TrExprS.*` lemmas go upstream (criterion 21) |
| `ErasesUniform.lean` | 820 | uniformity, six arms dropped; `ErasableStrengthen` re-examined against the ten-rule relation |
| `SubjectReduction.lean` | 477 | becomes T4's single `SEval.defeq`, built on `SEvalβζδ_defeq_spine`'s abstract-`P` schema |
| `ColdStartRun.lean` | 672 | `erase_run_ok`, `run_prepare_erasure_ok` carried; `prepare_sound_of_prepareHyps` re-aimed at `SEval` |
| `ColdStartInduction.lean` | 1,503 | `visitExpr_shape_all` and the `RunClosed`/`ShapeC` induction carried (hypothesis-free, panic-tolerant); `RegBridgeHyps` and the `g*` fixtures for deleted rules dropped |
| `ColdStartShape.lean` | 1,055 | `RegInvShape` collapses into `ErasesEnv`'s derived-from-the-run half; `.empty` (the cold-start base case) carried verbatim |
| `EnvErasureNonrec.lean` | 639 | the five `Registered*` predicates and three `RegisteredClosure*` structures collapse into one `ErasesEnv`; the `_of_registered*` implications become its derivation |
| `Bridge.lean` | 674 | `Supported` rewritten to §3.7 (decidable, on `Lean.Environment`); the closure lemmas' shape survives |
| `ColdStart.lean` | 2,000 | the capstone; most bulk is premise plumbing T9 deletes |
| `FirstOrderShipping.lean` | 254 | folds into the single capstone |
| `CheckerAdequacy.lean` | 143 | 7 of 8 declarations upstream; `kernel_isErasable_sound` renamed into `LeanToLambdaBox` |

### 5.4 Deleted

| Module(s) | Lines | Reason |
|---|---|---|
| `ErasureContext.lean` | 251 | the twelve-column registry index (`nameToBinder` moves to `Erases.lean`) |
| `SourceEval.lean`, `SourceEvalData.lean` | 701 | seven of eight source relations; one survives, flag-parameterised |
| `SubjectReductionFull.lean`, `SubjectReductionIota.lean` | 937 | merged into T4 (the β arm is written three times, two byte-identical) |
| `ErasesCorrect.lean`, `ErasesCorrectData.lean`, `ErasesCorrectIota.lean` | 3,456 | three simulations become one T5; `ErasesEnvDelta` is the pointwise relation the paper does not use |
| `EnvErasure.lean`, `EnvErasureRec.lean`, `RecBlockErasure.lean` | 1,812 | keyed on `Erases.fix`/`const_fix`/`fixvar`; `ContentlessFix`/`not_contentlessFix` re-aim onto `ErasesDecl.fixdefn`'s guard |
| `IotaPattern.lean`, `IotaDischarge.lean` | 1,089 | the ι discharge chain; `IotaRelevant`/`IotaShape` are constructed nowhere |
| `ProjPattern.lean`, `ProjDischarge.lean` | 1,474 | the proj discharge chain; `Erases.proj` survives in §3.2 |
| `CasesBridgeHyps.lean`, `DataBridgeHyps.lean`, `ProjBridgeHyps.lean`, `DeltaHyps.lean`, `PrepareHyps.lean` | 2,223 | four `*BridgeHyps` + `DeltaHyps`/`BlockHyps`/`RecBlockAgreement`/`RegBridgeHyps` → one `PrimSpec` |
| `ErasesLevels.lean`, `ErasesInstL.lean`, `ErasesDeltaL.lean` | 1,146 | the Γ-level campaign, insofar as it services deleted rules |
| `EraseCore.lean` | 643 | refuted as a bridge by its own addendum; the fuel/monotonicity lemmas move into T7's file |
| `ColdStartDelta.lean` | 1,185 | δ-record plumbing keyed on `RunConclδ` |
| `FirstOrderShippingIota.lean`, `ShippingCorrect.lean`, `ShippingCorrectData.lean` | 887 | duplicate capstone flavours; one capstone |
| `Export/EvalT.lean` | 296 | `Type`-valued twin for a Rocq transport never scoped to the relation |
| `Semantics.lean`, `Eval.lean` | 28 | aggregator and shim, no content |
| `OutputShape.lean` | 155 | folds into `LBWfPeregrine` + the panic table |
| `FirstOrder.lean` (rest) | ~650 | `FirstOrderValue`/`InformativeType`-as-domain, `eraseCore` reuse |

Deleted total ≈ 17,000 lines; carried ≈ 4,900; re-anchored ≈ 20,000 of which ≈ 60% survives as
proof. Net expected tree ≈ 20,000–23,000 lines, against 42,632 today.

### 5.5 New

| File | Contents | Est. lines |
|---|---|---|
| `Erases.lean` (rewrite) | §3.2: ten rules + `ProjParams`/`indIdOf`/`nameToBinder`, determinism-off-`box`, `sort_erasable`/`forallE_erasable`, `natLit`/`proj` guards | 600 |
| `ErasesDecl.lean` | §3.3: `ErasedEnv`, `mkCtorBody`, `mkElimBody`, `mkFixDefs`, `SelfRefers`, `ErasesDecl`, `SubsingletonElim`, `subsingletonElim_of_wf` | 850 |
| `ErasesEnv.lean` | §3.3: `ErasesEnv` + its derivation from the run's registration records (`RegInvShape` re-anchored) | 700 |
| `ElimBody.lean` | `mkElimBody_iota`, `mkElimBody_iota_sing`, `mkCtorBody_beta`, guards. Class **A**, `LBTerm` only | 500 |
| `Pass.lean` | §3.5: `LBPass`, `EnvAgree`, `WcbvEval.congr_env`, `comp`, `LBLower`, prune/restriction lemma | 350 |
| `Passes/CtorInline.lean` | `ctorInline` + `correct` + guard | 450 |
| `Passes/ElimInline.lean` | `elimInline` + `correct` (consumes `IotaBridge`, `mkElimBody_iota`) + guard | 750 |
| `SourceEval.lean` (rewrite) | §3.4: `SEvalFlags`, `SEval`, `mono`, value lemmas | 450 |
| `SubjectReduction.lean` (rewrite) | `SEval.defeq` over the abstract-`P` spine schema | 900 |
| `ErasesCorrect.lean` (rewrite) | T5 | 1,100 |
| `FirstOrder.lean` (rewrite) | §3.8 + T7 + `firstOrderIndB` + adequacy | 700 |
| `Supported.lean` | §3.7, decidable, with `Decidable` instances and the closure walk | 600 |
| `PrimSpec.lean` | §3.6 (from `OracleDischarge`) | 250 |
| `Wf.lean` | §3.10 `LBWfPeregrine`, `etaCtors`, `etaFix`, and the `visitExpr_shape_all` plumbing | 450 |
| `Axioms.lean` | §3.9 `AxiomSpec`, `ErasableAxioms`, decidability | 300 |
| `Capstone.lean` | T9 | 900 |
| `test/Ledger.lean`, `test/ledger.expected` | §3.11 | 60 |
| `test/Arith.lean` | T10 discharges | 400 |
| `test/CompilerBodies.lean` | `PrimSpec.env_connect`'s per-declaration `WF` checks for Arith | 250 |
| `doc/Erases-vs-Fig18.md` | criterion 3 | 120 |
| `doc/panic-sites.md` | criterion 10 | 60 |
| `doc/upstream-asks.md` | §8.2 | 80 |

---

## 6. Implementation waves

Dependencies are on wave completion, not on individual files. "Units" counts work items that can
proceed in parallel within the wave.

### W0 — flags, deletion, documentation policy (units: 3; depends: —)
*Goal.* Make the tree small and correctly flagged before anything is proved on top of it.
*Deliverables.* §3.1's four flag constants; delete every module in §5.4 whose deletion needs no
replacement (`Export/EvalT`, `Semantics.lean`, `Eval.lean`, `EraseCore`, the duplicate
definitions, `ShippingCorrect*`); the docstring pass of §9; CI greps for §9's rules; the pinned
`lakefile.toml` (`20ec229`) committed.
*Acceptance.* `lake build` green; `grep -c` for slice tags / commit hashes / dates / "used to" in
`LeanToLambdaBox/**` returns 0; comment fraction < 20%; `#print axioms` on
`Semantics.eval_deterministic` unchanged.

### W1 — target-side: passes and well-formedness (units: 5; depends: W0)
*Goal.* Everything class **A** and lean4lean-free, finished and shippable independently.
*Deliverables.* `ElimBody.lean`; `Pass.lean` (incl. `EnvAgree`, `WcbvEval.congr_env`);
`Passes/CtorInline.lean`; `Passes/ElimInline.lean`; `Optimize.lean` generalised over
`with_constructor_as_block` (4 new arms); `Wf.lean` (`LBWfPeregrine`).
*Acceptance.* `#print axioms LBLower_correct` ⊆ `{propext, Classical.choice, Quot.sound}`;
each pass's guard elaborates; and the measured side-check: a script reports
`EEtaExpandedFix.expanded` and `etaCtors` on all five `VerifyBench/ast/*.ast` (settling §3.10's
open sub-question before T9 commits to `etaFix`).

### W2 — the relation and its metatheory (units: 4; depends: W0)
*Goal.* `Erases` and the transport kit, and the table that anchors them.
*Deliverables.* `Erases.lean` (rewrite); the four transport modules re-anchored;
`doc/Erases-vs-Fig18.md`; `Erases.sort_erasable`/`forallE_erasable`; the `natLit` and `proj`
non-vacuity guards.
*Acceptance.* `grep -n "ErasureCtx" LeanToLambdaBox/Erases.lean` empty; the rule count is 10
(a `#guard` on the constructor list); `erases_subst` and `erases_shift` elaborate;
`doc/Erases-vs-Fig18.md` passes criterion 19's identifier grep.

### W3 — declarations and the environment (units: 4; depends: W1, W2)
*Goal.* `ErasesDecl`/`ErasesEnv`, and the Q2 fixture that proves they are inhabited.
*Deliverables.* `ErasesDecl.lean`, `ErasesEnv.lean`; `Supported.lean`; the pats-carrying
`VEnv.WF` fixture generalised from `doc/rework/probes/Q2-probe.lean` (a `Prop`-valued singleton
and a `Type`-valued one), discharging `SubsingletonElim` on `Eq`-like and `And`-like inductives;
the nine false "unconstructible" docstrings deleted.
*Acceptance.* `example : ErasesEnv env Eexample tExample := by …` elaborates for a hand-built
two-declaration environment containing one inductive, one constructor library entry, one
`casesOn` library entry and one `fix` definition; `Supported` `decide`s on all five VerifyBench
programs (`by decide` in `test/`, exit 0).

### W4 — source semantics and the simulation (units: 3; depends: W2, W3)
*Goal.* One `SEval`, one subject-reduction theorem, one `erases_correct`.
*Deliverables.* `SourceEval.lean` (rewrite), `SubjectReduction.lean` (rewrite),
`ErasesCorrect.lean` (rewrite); `FirstOrder.lean` (rewrite) with T7 and `firstOrderIndB`.
*Acceptance.* `grep -c "^inductive SEval" LeanToLambdaBox/**` = 1; T5 elaborates with exactly
five binders (a `#check` diffed against a committed expected signature);
`firstOrderIndB lenv fuel ``Nat = true`, `` `Bool ``, `` `Tree `` by `decide`;
`#print axioms erases_correct` = the class-B set.

### W5 — the bridge (units: 6; depends: W1, W3, W4)
*Goal.* T8 over the real `partial_fixpoint` family.
*Deliverables.* `PrimSpec.lean`; `VisitExprRefines.lean` re-anchored — the 18 motives restated
against §3.2 and §3.5, in three independent batches (7 mechanical / 3 environment-facing /
8 pass-facing); `doc/panic-sites.md`; `ColdStartRun`/`ColdStartInduction`/`ColdStartShape`
re-anchored.
*Acceptance.* `visitExpr_refines_erases` elaborates; `#print axioms` on it contains no `sorryAx`
beyond the inherited cluster; the panic table names all sixteen sites and two are closed by
lemma; `grep -c "BridgeHyps\|DeltaHyps\|BlockHyps\|RecBlockAgreement" LeanToLambdaBox/**` = 0.

### W6 — capstone, non-vacuity, delivery (units: 4; depends: W5)
*Goal.* T9, T10, T11, and landing it where consumers pin.
*Deliverables.* `Capstone.lean`; `test/Arith.lean`, `test/CompilerBodies.lean`;
`test/Ledger.lean` + fixture + CI job; `VerifyBench/STATUS.md` rewritten as the coverage table;
`doc/upstream-asks.md`; merge to `main`, CI trigger on both branches.
*Acceptance.* `lake build` elaborates `arith_covered` with every T9 hypothesis inhabited by a
checked term; `test/Ledger.lean`'s output diffs clean against the committed fixture; the
coverage table's covered count is ≥ 1 and each of the five rows states what is and is not
covered; `git rev-list --count main..HEAD` = 0.

**Critical path.** W0 → W2 → W3 → W4 → W5 → W6. W1 is off the critical path entirely (class A,
no lean4lean) and can be finished first or in parallel; it is also the wave that de-risks the
most, because it turns Q1's exactness argument into compiled code.

---

## 7. Risk register

| # | Risk | Severity | Mitigation |
|---|---|---|---|
| R1 | **`elimInline` is not exactly `visitCases` at some node the corpus does not reach.** Q1's exactness claim for the η-intro regime is Medium-confidence (it rests on `Meta.inferType` preserving λ binder names and instantiation not renaming ∀-binders — observed, not machine-checked). | high | W1's acceptance test is a *differential* one: for each of the five programs, run `LBLower.term` on the `Erases`-image reconstructed from the run and diff against the emitted term. If a node diverges, the fallback is stated in advance: weaken T8's `t = LBLower.term E.all t₀` to `LBLowerRel E.all t₀ t` (graph ⊆ relation, `[S §7.2]`'s own posture) **for that node class only**, and add a `Supported` conjunct naming it. Cost: one conjunct, no re-architecture. |
| R2 | **Genuine mutual blocks are unexercised** (50/50 emitted fix defs are singletons), so `mkFixDefs`'s ordering convention is analytic, not measured. | medium | W3's acceptance includes a two-member mutual fixture built by hand and evaluated with `WcbvEval` (`fixSubst`'s convention is already pinned by `Substitution.lean:220` and matched to `mkDef` by `run_mkDef_ok`, `ErasureRun.lean:2023`). If the order is wrong, the fix is one `List.reverse` in `mkFixDefs`, localised. |
| R3 | **The upstream inversion `VEnv.WF'.consts_origin` does not land**, so `SubsingletonElim` stays class **C**. | medium | Criterion 7's own escape clause: one named hypothesis, one ledger row. The corpus does not exercise it (no `Prop`-valued eliminated inductive; `Decidable` is `Type`-valued), so T10 is unaffected. |
| R4 | **`etaFix` fails on the emitted programs** (`Erasure.lean:911`'s own TODO), making `LBWfPeregrine` unprovable as stated. | medium | Measured in W1, before T9 commits. If it fails: a ledger row and an upstream report, not a weakened predicate. The failure would be a real shipping finding, and the repository rule is to raise it. |
| R5 | **Routing the oracle in costs 33 axioms**, two of them `_native.bv_decide` from Lean core, and criterion 15's fixture becomes large and brittle across toolchain bumps. | medium | The fixture is a committed file diffed in CI, with the 29 checker names in one labelled block. A bump that changes them is a visible, reviewable diff — which is the point of measuring rather than narrating. |
| R6 | **`EnvAgree` is too weak for some consumer** who wants literal list equality with `s'.gdecls`. | low | `EnvAgree` is exactly what `WcbvEval`/`constructorArity`/`isPropositionalInductive` read, and `LBWfPeregrine`'s `Nodup` makes lookup determine the multiset. If literal equality is later wanted, it is a separate lemma about registration order, not a change to any theorem's meaning. |
| R7 | **18-motive restatement overruns.** `VisitExprRefines.lean` is 4,641 lines and eight motives are pass-facing. | high | The three batches are independent (W5 units); the pass-facing motives all conclude the same shape `∃ t₀, Erases … t₀ ∧ t = pass.term Σ⁺ t₀`, so the first one written is the template for the other seven. The run algebra (`ErasureRun.lean`, 3,234 lines) and the `⊑`/admissibility kit survive untouched, which is the part that was expensive to build. |
| R8 | **`Supported` decidability on the dependency closure is expensive** (a closure walk per benchmark inside `decide`). | medium | The checker is `Bool`-valued on `Lean.Environment` with a `Decidable` instance by reflection, not a `Prop`-level `decide`; fuel bounded by `lenv.constants.size`, exactly as `firstOrderIndB`. No `native_decide` (criterion 12 of the code policy). |
| R9 | **The `_unsafe_rec` environment extension breaks `env.WF`** for some declaration outside the measured 33. | low | `PrimSpec.env_connect`'s obligation is decidable per program and discharged in `test/CompilerBodies.lean`. A declaration that fails it is visible in `Supported.compilerBodies` and excluded by the discharge failing to elaborate — loudly, not silently. |
| R10 | **Q1's X1/X2 exclusions are read as "the theorem covers nothing real".** | low | The five VerifyBench programs satisfy S2/S3 today except Quicksort, whose failure is the known shipping bug; the coverage table (criterion 14) states this per program. That is the honest position and it is strictly better than 0/5. |

---

## 8. Transpiler edits required

### 8.1 None.

`Basic.lean`, `Erasure.lean` and `Printing.lean` are used exactly as they stand on `dev/verify`.
Specifically:

* `LBTerm` needs no constructor and no field change: `.fvar`, `.prim`, `List BinderName`
  branches and the absence of `tCoFix` are all already right (`Basic.lean:90-104`).
* The `partial_fixpoint` family, the nine monotonicity lemmas, `visitCasesEta`/`visitCtorEta`
  and the de-partialized `toBvar` family (edits P1–P7 of the reuse inventory §16.1) are
  **preconditions** of T8 and are already in the tree.
* `mkAlt`'s and `mkDef`'s binder conventions are MetaCoq-exact as they stand (`mkAlt` matches
  `iota_red`, `mkDef` matches `fixSubst`; Q1 §2.10, verified against `BinaryTrees.ast`). The two
  hedging docstrings ("the other way around led to segfaults", "may be wrong") are *documentation*
  defects, and documentation in shipping files is outside this design's edit rights: they go on
  the raise list, not the patch list.
* `name_occurs`, `remove_unsafe_rec`, `fvar_to_name`, `toKername`, `register_inductive`'s
  `mutualBlockName` computation are consumed as pure functions and mirrored in the specification
  (`SelfRefers`, `nameToBinder`, `indIdOf`), with an equality lemma each.

### 8.2 Raised, not patched — the standing rule

| # | Where | Finding |
|---|---|---|
| F-a | `Erasure.lean:768-838` | sparse `casesOn` / per-constructor eliminators: the three-way zip truncates, the emitted `.case` is wrong, the run exits 0 and `peregrine validate` accepts the file. Pre-existing; excluded by `Supported.plainCases`. |
| F-b | `Erasure.lean:873-877` | `Quot.mk`/`lift`/`ind` are emitted as body-less axioms; a quotient program erases to a stuck term. Same failure class as F-a. Excluded by N16. |
| F-c | `Erasure.lean:911` | `-- TODO: eta-expand fixpoints?` — `EEtaExpandedFix.expanded` is a precondition of peregrine's first pass and is unchecked here. Measured in W1. |
| F-d | `Erasure.lean:151-187` | the `isErasable` kernel reroute is behaviour-changing (measured under-erasure on the success path, review SI-1). This design **keeps** it — reverting it demotes `PrimSpec` field 5 from class B to class D and makes criterion 9 unsatisfiable — and therefore owns the divergence inside `Supported`/`PrimSpec`, with a ledger row. |
| F-e | `Erasure.lean:857-875` (B4), `:934-980` (B6) | the `@[inline]` restructure and the `MLType` extension have no hypothesis today; both get N11 ledger rows. |
| F-f | peregrine-tool `theories/erasure/Transforms.v:375` | `run_untyped_transforms`' precondition obligation is `Admitted`, with a comment claiming `check_wf` ensures it; `check_wf` does not check η. Upstream report. |
| F-g | MetaRocq `PCUIC/PCUICFirstorder.v:59` | `firstorder_oneind`'s sort conjunct uses `Sort.is_level` where propositionality is meant, so `firstorder_ind` is `false` on `nat`. Upstream report. |
| F-h | lean4lean `Theory/Quot.lean:11` vs `Lean4Lean/Quot.lean:106` | the theory models only `Quot.lift`'s ι-rule; the executable checker reduces `Quot.ind` too. Upstream note (N15). |

### 8.3 Upstream asks (lean4lean, N15) — `doc/upstream-asks.md`

1. `VEnv.WF'.consts_origin` — the constants-keyed twin of `WF'.pats_origin`
   (`InductiveParams.lean:93`); the only route by which any client can use `VInductDecl.WF`.
   Load-bearing for `subsingletonElim_of_wf`.
2. `SimplePattern.iotaRHS'_Generic` / `iotaRHS'_Uses` — a normal form for ι-reduct holes; the one
   thing that stopped `Q2-probe.lean` from being `sorry`-free.
3. `VInductDecl.WF.largeElim_of_rec` — one-line packaging of `universes` (nice to have).
4. The seven kernel-generic declarations of `CheckerAdequacy.lean` (`kernelNGen`,
   `VContext.ofMLCtx` + three projections, `VState.WF.initial`, `M.WF.run'`) — criterion 21.
5. The three kernel-generic `TrExprS.*` lemmas in `ErasesStrengthen.lean` (`thin_vlet`,
   `weakFV'_fvwf`, `weakFV_nofvars`).
6. F-h, as a note.

---

## 9. Documentation policy compliance

1. **Current fact only.** Every docstring in the new and re-anchored modules states what the
   object is. History goes in commit messages. CI grep over `LeanToLambdaBox/**` for
   `slice|no longer|used to|retired|re-pin|\b[0-9a-f]{7,40}\b|\d{4}-\d{2}-\d{2}` returns 0
   outside the ledger fixture.
2. **One fact, one home.** Every claim about upstream state lives once, in `test/Ledger.lean`'s
   fixture with the `file:line` and the command that measured it. The nine "`VEnv.WF`
   unconstructible" docstrings, the seven "no `addPat` clause" sites, the eight "`addInduct_WF`
   is `sorry`" sites, the five stale oracle descriptions, `Flags.lean:19-24`, and the
   `ProjDischarge`/`ProjPattern` `proj_defeq` contradiction are all **deleted in W0** — each was
   measured false at the pin.
3. **Length budget.** Field/lemma docstrings ≤ 8 lines, module headers ≤ 40. The three current
   headers over 300 lines (`ColdStart:4`, `DeltaHyps:8`, `VisitExprRefines:1817`) die with their
   modules or are cut to a header plus a `doc/` file.
4. **Every backticked identifier resolves; every cited document exists.** CI grep. The four
   current dangling references (`closeFix_fvar`, `isProp_refines_Erasable`, two memory-store
   references, `PROJECT_STATUS_HANDOFF.md` ×2 — one from shipping code) are on the W0 list;
   the shipping-code one goes on the raise list (§8.2), since shipping files are not editable
   here.
5. **Why a hypothesis is not slack.** Every class-**C** binder's docstring gives the reason and,
   where one exists, the counterexample — the model being `IotaBridge.lean:96-111`,
   `Semantics/Values.lean:79`, `Semantics/Eval.lean:29`. `Supported.plainCases` names
   `_sparseCasesOn_`; `Supported.lamMinors` names `Option.casesOn o none Some`;
   `Supported.noAccRec` names `Acc.intro`'s index-determined field and Q2 §4.
6. **No dead code.** Criterion 20's tracked exception list has exactly two entries: `optimize`
   (off the shipping path by §1.1 move 4, kept because it is the flag-discharging template and a
   proved corollary) and the non-vacuity guards (kept by criterion 11 of the code policy).
7. **No duplicate definitions, no forked relations.** One `SEval`, one environment relation, one
   hypothesis bundle, one ledger, one capstone. Growth is by parameterisation: `SEvalFlags`,
   `WcbvFlags`, `LBPass`.
8. **Kernel lemmas upstream.** §8.3.
9. **No `native_decide`;** `set_option` only with a stated reason; no `@[simp]` on foreign
   namespaces. The tree is already clean here and the CI grep keeps it so.
