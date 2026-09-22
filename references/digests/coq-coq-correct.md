# Coq Coq Correct! -- Sozeau, Boulier, Forster, Tabareau, Winterhalter, POPL 2020

## Identity

Full entry: Matthieu Sozeau, Simon Boulier, Yannick Forster, Nicolas Tabareau, and Theo
Winterhalter. 2020. "Coq Coq Correct! Verification of Type Checking and Erasure for Coq, in
Coq." Proc. ACM Program. Lang. 4, POPL, Article 8 (January 2020), 28 pages.
https://doi.org/10.1145/3371076.

Object: a conference paper (POPL 2020, published in PACMPL vol. 4). Standalone, 28 pages
(printed page range 8:1-8:28). It is the original venue for the verified PCUIC type checker and
the verified erasure procedure that MetaCoq/MetaRocq later carry forward and extend; the later
MetaCoq JACM article (`metacoq-erasure-jacm`) is the broader, updated journal treatment of the
whole MetaCoq project (parsing, type checking, erasure, safe checker, plugin, extraction to
several languages) and supersedes/extends this paper's erasure chapter with more machinery
(e.g. optimizations, more evaluation strategies) - this POPL paper is the earlier, narrower,
original erasure-correctness result being extended there. Based on the "MetaCoq project" HAL
report (`metarocq-project`, an earlier tech-report version of the overall MetaCoq framework this
paper builds on for PCUIC syntax and typing).

## One-paragraph summary

The paper presents (1) a fully formalized, Coq-mechanized specification of PCUIC (Predicative
Calculus of Cumulative Inductive Constructions), a mild simplification of Coq's actual kernel
calculus, together with parts of its metatheory (confluence of reduction proved via a
Tait-Martin-Lof triangle/rho-function method; subject reduction, validity, principality assumed
as axioms/conjectures pending completion; strong normalisation and the fixpoint/inductive guard
conditions taken as axioms, consistent with Godel's incompleteness theorem); (2) a certified type
checker for PCUIC built on a stack-machine weak-head reduction that terminates by well-founded
recursion on an order derived from the strong-normalisation axiom, plus a graph-based decision
procedure for universe-constraint consistency (proved equivalent to the existence of a
satisfying valuation); and (3) a certified type-and-proof erasure procedure translating PCUIC to
an untyped target calculus lambda-box (called lambda_box in the paper, syntax `eterm` with a
`Box` constructor for erased content), proved correct via a non-deterministic erasure *relation*
(following Letouzey) that is shown to (a) contain the erasure *function*'s graph, (b) be stable
under weak call-by-value evaluation (the central forward-simulation theorem, Thm 4.7), and (c) to
coincide with the function and be fully deterministic on first-order values, yielding a strong
"the erased value literally equals evaluation of the erased term" corollary for first-order
result types (supporting separate compilation of erased code). The whole development is
~17kLoc spec + 30kLoc proof + 3kLoc doc, Coq 8.9, ~10 min to compile, and moves the correctness
argument from a "trusted code base" (TCB, i.e., trust the OCaml implementation) to a "trusted
theory base" (TTB, i.e., trust only a handful of stated metatheoretic axioms about PCUIC).

## What it establishes

- Coq-mechanized syntax and typing judgment for PCUIC, syntactically close to Coq's actual kernel
  `constr` type (only differences: binary vs n-ary application, no cast constructor) -> Sec 2.1,
  Fig. 1, p.8:4.
- Universe hierarchy and constraints given a direct valuation-based specification of consistency
  (`consistent`), rather than only a graph-acyclicity check -> Sec 2.2.1, Fig. 3, p.8:6-7.
- Confluence of PCUIC reduction, proved via parallel reduction + an optimal-reduction function rho
  and the "triangle method" -> Thm 2.2 ("Triangle property"), Cor 2.2.1 ("Confluence of Parallel
  Reduction"), Sec 2.3.2, p.8:11-13.
- Strong normalisation, subject reduction, validity, principal typing, and the inductive/fixpoint
  guard conditions are all explicitly axiomatized/assumed (`Conjecture`/`Axiom`), not proved in
  Coq, because of Godel's second incompleteness theorem -> Sec 2.2.4 (Fig. 5), Sec 2.3.3-2.3.4,
  p.8:9, 8:13-14.
- A terminating, well-founded weak-head reduction machine (`reduce_stack`) built from a
  stack+position-based measure, correct-by-construction w.r.t. the `red1` specification, relying
  on the strong-normalisation axiom for its accessibility proof -> Sec 3.1-3.2, Fig. 8, p.8:14-17.
- A verified decision procedure for universe consistency via weighted-graph acyclicity, proved
  equivalent to the existence of a correct labelling/valuation (`lsp`, longest simple path) ->
  Sec 3.3, Fig. 9, p.8:16-18.
- A verified conversion/cumulativity checker `convert_leq`, correct w.r.t. the `cumul`
  specification -> Sec 3.4, p.8:18-19.
- A certified bidirectional type-inference algorithm `infer` returning `typing_result ({A & ||Σ;Γ
  ⊢ t:A||})`, correct by construction (soundness), but *not* proved complete -> Sec 3.5, Fig. 10,
  p.8:19-20.
- Extraction of the type checker to OCaml and a benchmark against Coq's own kernel (~10x slower;
  extraction encountered and worked around a genuine bug/limitation in Coq's own extraction
  producing ill-typed OCaml) -> Sec 3.6, p.8:20-21.
- The target calculus lambda-box (`eterm`, Fig. 11) as a "PCUIC minus types plus a Box
  constructor" with a weak CBV evaluation relation extended by three amendments for Box-headed
  applications/cases/fix -> Sec 4.1, p.8:21-22.
- The erasure function `E` defined via `is_erasable` (an oracle deciding whether a term is a type
  or proof) and structural recursion, using Equations -> Sec 4.2, Fig. 12, p.8:22-23.
- The counterexample showing the naive "erase-commutes-with-evaluation" statement is false in
  general (the `(fun Z:Type => (1, fun x:X=>x)) Type` example) -> Sec 4.3, p.8:22.
- The non-deterministic erasure *relation* `erases` (Fig. 13) extending the function, with rules
  `erases_tRel` .. `erases_tFix`, `erases_box` (via `Is_Type_or_Proof`), and a special
  `Informative`-gated `erases_tCase1`/`erases_tProj` treatment of case/projection on proofs ->
  Sec 4.3, Fig. 13, p.8:24.
- Lemma 4.1: the erasure function's graph is contained in the erasure relation -> p.8:23.
- Lemma 4.2: global weakening, weakening, and substitutivity of the erasure relation -> p.8:23.
- Lemma 4.3: erasable terms are closed under `mkApps`, sub-lambda, and evaluation -> p.8:23.
- Lemmas 4.4, 4.5, 4.6: environment-erasure lookup coherence, and mkApps introduction/inversion
  lemmas for the erasure relation -> p.8:23-24.
- Theorem 4.7 (Erasure Correctness): the central forward-simulation result: if `Σ;Γ ⊢ t:T`
  erases to `t'` and evaluates to `v`, then `t'` evaluates (weak CBV, in lambda-box) to some `v'`
  with `v` erasing to `v'` -> Thm 4.7, p.8:24.
- Lemma 4.8 and Corollaries 4.8.1/4.8.2: on fully-applied first-order inductive types the erasure
  relation is functional and coincides with the erasure function, giving the sharp corollary that
  erasing-then-evaluating equals evaluating-then-erasing (supports separate compilation) ->
  p.8:24-25.
- Positioning w.r.t. Letouzey's thesis, Glondu's mechanization, and CertiCoq: this work replaces
  CertiCoq's earlier unsafe, cast-based erasure phase with a fully verified one usable in the
  MetaCoq+CertiCoq+CompCert pipeline -> Sec 6.1, p.8:25-26.

## Structure

| Section | Pages | What it covers | Relevance |
|---|---|---|---|
| 1 Introduction | 8:1-8:3 | TCB->TTB paradigm shift motivation, Godel incompleteness caveat, outline | Low |
| 2 PCUIC: Coq's core calculus | 8:3-8:14 | Syntax (Fig.1), typing rules (Fig.2), universes/constraints/valuations (Fig.3), reduction (Fig.4), guard-condition axioms (Fig.5), well-formed arities, metatheory: substitution/weakening, sigma-calculus, confluence via parallel reduction + rho (Fig.6-7, Thm 2.1-2.2), context conversion, subject reduction/principality as axioms, strong normalisation axiom | Medium (grounds the source calculus MetaRocq PCUIC/EAst come from; not directly used by lean-to-lambdabox which targets a different source, but useful for understanding the trust axioms MetaRocq inherits) |
| 3 A verified checker for PCUIC | 8:14-8:21 | Stack-machine reduction w/o fuel (Fig.8), weak-head normalisation via accessibility, universe graph/acyclicity/lsp (Fig.9), cumulativity/conversion checker, type inference algorithm (Fig.10), extraction & performance | Low-Medium (kernel-verification layer; not directly relevant to erasure semantics but establishes "verified checker" pattern MetaRocq/CertiRocq follow) |
| 4 Type and proof erasure for PCUIC | 8:21-8:25 | Target calculus lambda-box/eterm (Fig.11), erasure function E via is_erasable (Fig.12), counterexample motivating the relation, erasure relation `erases` (Fig.13), Lemmas 4.1-4.6, Theorem 4.7 (erasure correctness/forward simulation), Lemma 4.8 + Corollaries 4.8.1-4.8.2 (first-order strong result) | HIGH -- this is the original erasure-relation/is_erasable/Box-rule/forward-simulation design that MetaCoq's EAst/isErasable/erases/erasure-correctness (and hence Peregrine's lambda-box, and lean-to-lambdabox's target semantics) descend from |
| 5 Related work | 8:25 | Abel et al. NbE, Strub et al. F*, Ouef, Hupel-Nipkow (Isabelle->CakeML), Myreen-Owens (HOL->CakeML), Forster-Kunze (Coq->CBV lambda-calculus w/ time bounds), Glondu's Letouzey mechanization | Low |
| 6 Conclusion and future work | 8:25-8:26 | LoC counts, CertiCoq+CompCert integration story, planned SProp support, planned call-by-name/lazy account, planned semantic (axiom-tolerant) erasure correctness a la Letouzey | Medium (states open problems later work, incl. MetaCoq JACM, closes) |

## Key definitions and results

| id as printed | name | one-line statement | page |
|---|---|---|---|
| Fig. 1 | `term` (PCUIC syntax) | Inductive AST: tRel, tSort, tProd, tLambda, tLetIn, tApp (binary), tConst, tInd, tConstruct, tCase, tProj, tFix, tCoFix | 8:4 |
| (typing judgment) | `typing : global_env_ext -> context -> term -> term -> Type`, notation `Σ;Γ ⊢ t:T` | the PCUIC typing relation | 8:5 |
| Fig. 2 | `typing` (excerpt) | inference rules type_Rel, type_Sort, type_Prod, type_Lambda, type_LetIn, type_App, type_Cumul; plus `cumul` (subtyping) via cumul_refl/red_l/red_r and `leq_term` | 8:6 |
| Sec 2.2.1 | `Level`, `universe`, `val`, `leq_universe` | four-kind universe levels (lProp/lSet/Level s/Var n); universes as non-empty lists of (level,bool); valuations into Z; leq_universe defined via all valuations | 8:5-8:6 |
| Fig. 3 | `ConstraintType`, `univ_constraint`, `valuation`, `val`, `satisfies0`, `consistent` | constraint kinds Lt/Le/Eq; valuation semantics; a hierarchy is consistent iff some valuation satisfies its constraints | 8:6-8:7 |
| Fig. 4 | `red1` (excerpt) | one-step reduction: red_beta, red_zeta, red_rel (delayed let-unfolding), red_iota, red_fix (guarded by is_constructor on the recursive arg), red_cofix_case, red_cofix_proj, red_delta, red_proj | 8:7-8:8 |
| Fig. 5 | `fix_guard`, `ind_guard` (axioms) | fixpoint/inductive guard conditions treated as syntactic oracles; fix_guard is stable under reduction (`fix_guard_red1`) | 8:9 |
| Sec 2.2.3 | well-formed arities | an arity is `forall Γ, s`; validity ensures every well-typed term's type is itself typed by an arity | 8:9 |
| Sec 2.3.1 | `subslet` | well-typed parallel substitution structure respecting let-bound definientia | 8:10 |
| Fig. 6 | `pred1`, `psubst` | parallel one-step reduction (pred_beta, pred_zeta, pred_rel_def_unfold, pred_iota, pred_app, pred_atom_refl) and typed parallel substitution | 8:11 |
| Thm 2.1 | Parallel substitution | stability of parallel reduction under parallel (well-typed) substitution | 8:11 |
| Fig. 7 | rho (`ρ`) | the optimal-reduction function reducing every redex it can find in one pass | 8:11-8:12 |
| Thm 2.2 | Triangle property | every one-step parallel-reduct of `t` also parallel-reduces into `ρ(t)` | 8:13 |
| Cor 2.2.1 | Confluence of Parallel Reduction | follows from the triangle property applied twice | 8:13 |
| Conjecture (Sec 2.3.3) | `subject_reduction` | well-typed terms preserve their type under reduction (assumed, work in progress) | 8:13 |
| Conjecture (Sec 2.3.3) | `principal_typing` | any two derivable types of a term have a common lower bound that also types the term (assumed) | 8:13 |
| Sec 2.3.4 | `cored`, `normalisation` (axiom) | co-reduction transitive closure; the strong-normalisation axiom: every well-typed term is `Acc`-accessible for `cored` | 8:14 |
| Fig. 8 | `stack`, `position`, `R`, `R_Acc` | stack-machine positions/order for defining fuel-free reduction; `R_Acc` (Corollary): `R` is well-founded on well-formed term/stack pairs, using the SN axiom | 8:15-8:16 |
| Sec 3.2 | `reduce_stack` | verified weak-head normalisation defined by well-founded recursion on `R_Acc`, correct w.r.t. `red1` (via `Req`) | 8:16 |
| Fig. 9 | `RootedGraph`, `Paths`, `acyclic` | weighted rooted graph model of universe constraints; acyclicity = all reflexive paths have weight 0 | 8:16-8:17 |
| Sec 3.3 | `correct_labelling`, `lsp`, Lemma `acyclic_labelling`, Lemma `acyclic_lsp`, Lemma `lsp_correctness` | longest-simple-path function; acyclicity of the constraint graph is equivalent to the existence of a correct labelling/valuation, giving a decision procedure | 8:17-8:18 |
| Sec 3.4 | `leq_vertices`, `leqb_vertices`, `convert_leq` | graph-based decidable universe comparison; the verified cumulativity/conversion checker | 8:18-8:19 |
| Fig. 10 | `infer`, `infer_cumul` | verified, correct-by-construction bidirectional type-inference algorithm (Equations-style, monadic) returning `typing_result {A & ||Σ;Γ⊢t:A||}` | 8:19 |
| Sec 4.1 / Fig. 11 | lambda-box target calculus, `eterm` | untyped target AST: eBox, eRel, eLambda, eLetIn, eApp, eConst, eConstruct, eCase, eProj, eFix, eCoFix; WCBV eval extended by 3 Box-propagation rules (app-of-box, case-of-box picks the all-erasable branch, fix guarded-arg-is-box) | 8:21-8:22 |
| Sec 4.2 | `is_erasable` | oracle: `Σ; Γ ⊢ t` is either provably `isErasable` or provably not-erasable-and-welltyped (informative return type) | 8:22 |
| Fig. 12 | `E` (erasure function) | structurally recursive erasure function: erasable terms -> `E.tBox`; otherwise homomorphic translation (tRel->eRel, tLambda->eLambda, tApp->eApp, tCase->eCase dropping the predicate `p`, etc.) | 8:23 |
| Sec 4.3 (counterexample) | -- | `(fun Z:Type => (1, fun x:X=>x)) Type` shows erase(eval(t)) != eval(erase(t)) in general, motivating the relation | 8:22 |
| Fig. 13 | `erases` (erasure relation), notation `Σ;Γ ⊢ t ⇝E t'` | non-deterministic relation extending E: erases_tRel/tVar/tLambda/tLetIn/tApp/tConst/tConstruct/tCase1(gated by `Informative`)/tProj(gated by `Informative`)/tFix, plus erases_box (any `Is_Type_or_Proof` term erases to tBox) | 8:24 |
| Lemma 4.1 | Erasure function correctness | if `E Σ,Γ t = Checked t'` then `Σ;Γ ⊢ t ⇝E t'` (function's graph ⊆ relation) | 8:23 |
| Lemma 4.2 | erasure-relation weakening/substitutivity | global weakening, context weakening, and substitution compatibility of `⇝E` | 8:23 |
| Lemma 4.3 | erasable-term closure properties | erasability closed under mkApps, sub-lambda-body, and evaluation | 8:23 |
| (env erasure) | `Σ ⇝E Σ'` | pointwise inductive extension of the erasure relation to global environments | 8:23 |
| Lemma 4.4 | environment lookup coherence | if a constant's declaration erases in `Σ⇝E Σ'`, its erased declaration is found correspondingly in `Σ'` | 8:23 |
| Lemma 4.5 | mkApps introduction | pointwise erasure of a function and its argument list gives erasure of the applied term | 8:24 |
| Lemma 4.6 | mkApps inversion | inversion principle for erasure of an applied term, accounting for the box-collapsing nondeterminism | 8:24 |
| Thm 4.7 | Erasure Correctness (forward simulation) | well-typed `t` erasing to `t'` and evaluating to `v` implies `t'` evaluates (in lambda-box, weak CBV) to some `v'` with `v` erasing to `v'` | 8:24 |
| Lemma 4.8 | functionality on first-order types | on fully-applied first-order inductive types, the erasure relation is functional and coincides with the erasure function `E` | 8:24-8:25 |
| Cor 4.8.1 | first-order value correspondence | for first-order-typed `t`, `E(eval(t)) = eval(E(t))` | 8:25 |
| Cor 4.8.2 | separate compilation | for `mkApps f L : T` with `T` first-order, the value of `mkApps (Ef)(EL)` is the erasure of the value of `mkApps f L` | 8:25 |
| Sec 3.6 | extraction bug/workaround | Coq's own extraction produced an ill-typed OCaml term for the type checker; fixed by restructuring a dependent-if-then-else return type | 8:20 |

## Position in the pipeline

- [kernel theory]: establishes PCUIC syntax, typing, reduction, confluence proof, and states the
  remaining metatheoretic assumptions (SR/validity/principality/SN/guard) as axioms -- Sec 2, p.
  8:3-8:14.
- [kernel verification (type checker correctness)]: verified fuel-free weak-head reduction,
  universe-consistency decision procedure, cumulativity checker, and type-inference algorithm,
  all proved sound w.r.t. the Sec 2 specification -- Sec 3, p.8:14-8:21. Prover: Coq (for Coq's
  own kernel, minus modules/template polymorphism).
- [erasure theory]: defines the lambda-box target calculus and its weak-CBV semantics, the
  `is_erasable`/erasure function, and (crucially) the non-deterministic erasure relation with its
  Box rule and Informative-gated case/proj rules -- Sec 4.1-4.3, p.8:21-8:24. Prover: Coq.
- [erasure verification]: proves the forward-simulation Theorem 4.7 and the first-order
  strengthening Lemma 4.8/Corollaries -- Sec 4.3, p.8:23-8:25. Prover: Coq.
- [erasure implementation]: the erasure function `E` (Fig. 12) is a real, extracted, executable
  Equations-defined program (not just a relation) -- Sec 4.2, p.8:22-8:23.
- [post-erasure pipeline]: not covered in this paper beyond mentioning that the CertiCoq pipeline
  (compiling lambda-box-erased terms onward to CompCert C-light) can now build on this verified
  erasure instead of CertiCoq's earlier unsafe cast-based erasure -- Sec 6.1, p.8:25-8:26.
- [extraction implementation]: the type checker itself is extracted to OCaml and benchmarked
  (Sec 3.6, p.8:20-8:21); the erasure procedure's *target* is lambda-box, one step short of
  concrete-language (OCaml/Malfunction) extraction, which the paper explicitly defers to future
  work relating it to Letouzey's actual MiniML-with-Obj.magic extraction -- Sec 4 intro, p.8:21.

## Relation to the other sources named in the task

- metarocq-project: predecessor/subset. This paper's PCUIC syntax/typing/reduction machinery is
  drawn from and cites the (earlier) MetaCoq project report; this paper *adds* the verified
  checker (Sec 3) and verified erasure (Sec 4) on top of that shared syntactic/typing groundwork.
- metacoq-erasure-jacm: this POPL paper is the direct ancestor/subset of the later, broader MetaCoq
  JACM article's erasure chapter. The JACM article is a successor that extends coverage (e.g. more
  of the pipeline, more optimizations/evaluation strategies, updated names such as `EWcbvEval`,
  and likely closes some of the "work in progress" metatheory gaps this paper leaves open, e.g.
  subject reduction/validity/principality). Where they overlap on the erasure relation
  (`erases`/Box rule/Theorem 4.7-equivalent), the JACM version should be treated as the more
  current reference; this paper is the original source of that design and its first proof.
- sozeau-habilitation: independent but overlapping; likely surveys/synthesizes this same PCUIC +
  erasure work (and more) as part of a broader habilitation narrative. Expect it to restate
  Theorem 4.7-equivalent results with possibly updated framing/notation and additional
  perspective on the guard-condition/SN axioms; treat as a successor/superset survey rather than
  a primary technical source distinct from this paper.
- letouzey-new-extraction: primary predecessor this paper explicitly follows for the very design
  of the erasure *relation* (as opposed to only the function) and for the separation of
  "erasure to untyped lambda calculus" from "MiniML extraction with Obj.magic." This paper is a
  mechanized, Coq-verified realization of ideas from Letouzey's thesis, restricted to weak CBV
  and to axiom-free (non-axiom-blocking) evaluation; it explicitly leaves Letouzey's more general
  semantic/axiom-tolerant erasure correctness account to future work (Sec 6.2, p.8:26).
- lean-extraction-report: independent target (different source proof assistant, Lean rather than
  Coq/PCUIC) but shares the same terminal calculus family (lambda-box / untyped WCBV lambda
  calculus with a Box-like erased marker) that this paper defines; useful as the frontend-side
  analogue this paper's lambda-box target is meant to be reusable for (per the Peregrine
  architecture, though this 2020 paper itself has no notion of a multi-frontend pipeline).
- metarocq-docs: independent, later, informal/reference documentation of the current
  MetaCoq/MetaRocq codebase; likely uses updated names (`EAst`, `isErasable`, `erases`,
  `EWcbvEval`) for exactly the constructs this paper introduces under its own paper-specific
  names (`eterm`, `isErasable`/`is_erasable`, `erases`, unnamed WCBV relation); treat metarocq-docs
  as the current ground truth for names/APIs and this paper as the theorem-proof reference for
  *why* they are correct.
- carneiro-thesis: independent (likely Lean-kernel- or Metamath-related trusted-checker work by a
  different author/prover ecosystem); relation to this paper is at most a shared methodological
  theme (verified kernel/checker correctness, TCB-to-TTB style arguments) rather than a shared
  formal object; treat as independent unless the digest content shows direct engagement with
  MetaCoq/PCUIC.

## Terminology map

- lambda-box / lambda_box (this paper's target calculus name, "λ□") = `EAst`/lambda-box in
  MetaCoq/MetaRocq codebase and in the Peregrine project's own terminology (`peregrine-tool`
  docs) = the untyped erased calculus that Peregrine calls "λ□ (lambda-box/LambdaBox)".
- `eterm` (this paper's target-term type, Fig. 11) = MetaCoq's `EAst.term` in later code/docs.
- `□` / `E.tBox` / `eBox` (this paper's erased-content marker) = `tBox` in MetaCoq `EAst` and in
  Peregrine's node-name convention (`tBox`).
- `is_erasable` (this paper's Boolean/decision function, Sec 4.2) = `isErasable`/`is_erasable` in
  later MetaCoq code (same concept, casing may differ); the underlying *type-level* predicate
  used inside is written `isErasable Σ Γ t` in this paper already (an inductive/Prop predicate
  distinct from the Boolean oracle function of the same informal name) -- so within this very
  paper there are already two related but distinct objects: the decision procedure `is_erasable`
  and the specification predicate `isErasable`.
- `erases` (Fig. 13, this paper's non-deterministic erasure relation, notation `Σ;Γ ⊢ t ⇝E t'`) =
  what later MetaCoq sources typically also call `erases` (the name is already used verbatim
  here) -- this is the "erasure relation" referenced throughout the Peregrine CLAUDE.md's
  verification-landscape section.
- `Is_Type_or_Proof` (side condition of rule `erases_box`) = the semantic erasability judgment
  underlying the Box rule; likely renamed or refined as `isErasable`/`isTypeOrProof` in later
  MetaCoq code.
- `Informative` (predicate gating `erases_tCase1`/`erases_tProj`, meaning the inductive type is
  not a non-informative/proof-irrelevant proposition) = related to later notions of
  "singleton/propositional-but-informative" inductive classification in MetaCoq's erasure code.
- big-step call-by-value evaluation, written `Σ;Γ ⊢ t ▷ v` for both PCUIC (`PCUIC:WcbvEval`) and
  (implicitly, unnamed in the paper) lambda-box = `WcbvEval`/`EWcbvEval` in later MetaCoq/MetaRocq
  code and in the Peregrine memory note "λ□ WcbvEval semantics"; this paper's lambda-box
  evaluation relation is the direct ancestor of what other sources call `EWcbvEval`.
- PCUIC ("Predicative Calculus of Cumulative Inductive Constructions", this paper's simplified
  Coq kernel calculus) = MetaRocq's `PCUIC` development (same name carried forward verbatim);
  contrasted with `TemplateCoq`/`Ast` (Coq's actual surface `constr`, which this paper notes
  PCUIC differs from only in application arity and absence of casts).
- TCB / TTB ("trusted code base" / "trusted theory base", this paper's coined framing in Sec 1
  and Sec 6) = the general "trust boundary" / "verification landscape" concept referenced in the
  Peregrine project's own CLAUDE.md ("Verification landscape" section, e.g. "verified modulo an
  axiom").
- block vs applied constructor form: not discussed in this paper (PCUIC/lambda-box constructors
  `tConstruct`/`E.tConstruct` here are always parameterless nodes combined via `mkApps`/`tApp`,
  i.e. this paper's convention is uniformly the "applied form"; the "block form" distinction
  described in Peregrine's CLAUDE.md is a later development-specific concern, e.g. for
  CertiCoq's calling convention, not present here).
