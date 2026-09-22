# Correct and Complete Type Checking and Certified Erasure for Coq, in Coq -- Sozeau, Forster, Lennon-Bertrand, Nielsen, Tabareau, Winterhalter, J. ACM 2025

## Identity

Full entry: Matthieu Sozeau, Yannick Forster, Meven Lennon-Bertrand, Jakob Nielsen, Nicolas
Tabareau, Théo Winterhalter. "Correct and Complete Type Checking and Certified Erasure for Coq,
in Coq." *Journal of the ACM* 72(1), Article 8, 74 pages, January 2025.
https://doi.org/10.1145/3706056.

Object: peer-reviewed journal article (J. ACM). It is an explicit **journal extension of a prior
conference paper**, Sozeau et al. 2019b ("The MetaCoq Project" / the ITP-era PCUIC type-checker
paper) -- see p.8:5 "Prior publication." Stated additions over the conference version:
(1) the completeness proof (via an intermediate bidirectional-typing specification), (2) a
two-step certification (declarative <-> algorithmic <-> decision-procedure, vs. one step before),
(3) the first formal treatment of cumulative inductive types with a subject-reduction proof, and
(4) a complete, conjecture-free proof of erasure correctness (the conference version's erasure
correctness relied on conjectures). Describes MetaCoq **v1.2**, for Coq 8.16 (opam package),
~300kloc Coq + ~10kloc OCaml glue, ~15 min compile.

## One-paragraph summary

The paper gives the first Coq-verified, executable type checker for the kernel of Coq (restricted
to a calculus called PCUIC: no modules, no template polymorphism, no eta, no nested inductives,
guard condition left abstract), proved both sound and complete against a declarative specification,
by threading declarative -> algorithmic (universe graphs, reduction-based conversion, bidirectional
typing) -> decision-procedure presentations, each proved equivalent, with normalization-dependent
proofs isolated to one axiom (a "trusted-code-base to trusted-theory-base" move). On top of the
verified checker it builds a verified **type-and-proof erasure** function E : PCUIC -> lambda-box
(a simplified untyped calculus with an explicit box constructor for erased content), following
Letouzey's method: an erasure *relation* extends the erasure *function* and is closed under weak
call-by-value (wcbv) evaluation, giving a general forward-simulation lemma (`simple_erases_correct`
/ `erases_correct`), from which the paper derives the sharpest usable statement -- for closed,
axiom-free programs of *first-order inductive* result type, evaluating-then-erasing and
erasing-then-evaluating agree (`erase_correct_firstorder`), which also yields separate
compilability of first-order-typed functions. A dependency-pruning environment-erasure relation
(`erases_deps`) and a case-optimization pass (`optimize`) are proved separately correct and
composed with the core theorem to get the full, usable statement `erases_correct`.

## What it establishes

- A declarative specification of PCUIC (universes, cumulativity/conversion, typing) close to
  mathematical presentation -> Section 3, pp. 8:9-8:24 (approx).
- An algorithmic specification (acyclic-graph universes, reduction-based conversion, bidirectional
  typing) proved equivalent to the declarative one, axiom-free -> Section 4, p. 8:4 (equivalence
  claim), pp. 8:24ff.
- Confluence, subject reduction, strong-normalization-dependent standardization, canonicity,
  consistency of PCUIC -> Section 5, subsections 5.3-5.8, pp. 8:46-8:59 (Weak CBV standardization
  5.6 at p.8:46; Canonicity 5.7 p.8:47; Consistency 5.8).
- A sound and complete type-checking/retyping algorithm parametrized by decision procedures,
  found a genuine **completeness bug fixed in Coq 8.14** -> Section 6, pp. 8:56-8:59 (bug
  mentioned p.8:4-8:5; retyping algorithm and performance benchmark: Section 6.4, p.8:59).
- Definition of the target calculus lambda-box (Fig. 16) and its wcbv evaluation with three
  erasure-specific amendments (box-application, box-discriminee case, box-recursion fix) ->
  Section 7.1, p.8:60.
- Definition of an erasure function E via a retyping-based `is_erasableb` decision procedure
  reflecting `isErasable` -> Section 7.2, Fig. 17, p.8:61.
- The erasure relation (Fig. 18) extending E, closed under wcbv evaluation, with the
  Subsingleton-gated `erases_tCase` rule -> Section 7.3, Fig. 18, p.8:61-8:62.
- A general (non-first-order) forward-simulation lemma `simple_erases_correct` (stated but not
  the one actually proved/used) and the first-order specialization `erase_correct_firstorder`
  with separate-compilation corollary -> Section 7.3, p.8:62-8:63.
- The `optimize` case-expansion pass and its correctness (`optimize_correct`) plus the
  dependency-pruning `erases_deps` relation and the full theorem `erases_correct` -> Section 7.4,
  p.8:63-8:64.
- Identification of a counterexample showing the naive statement "eval then erase = erase then
  eval" fails in general (the `(fun X:Type => (1, fun x:X=>x)) Type` example) -> Section 7.3,
  p.8:61-8:62, motivating the relation-based proof method.

## Structure

| Section | Pages (8:x) | What it covers | Relevance to Lean-to-lambdabox / lean4lean |
|---|---|---|---|
| 1 Introduction | 8:2-8:5 | Motivation, TCB->TTB paradigm, guard condition as abstract parameter, outline, prior-publication note | Medium -- framing/trust-boundary language reused by lean-to-lambdabox docs |
| 2 Overview of Coq's type theory | 8:5-8:9 | Inductives, positivity, pattern matching/fixpoints, guard condition, records/projections, coinductives, sorts/universes (informal) | Low |
| 3 PCUIC specification | 8:9-8:24ish | Syntax, universes, cumulativity, guard condition, declarative typing, well-formed environments (isArity-adjacent material, Prop rules) | Medium -- source typing PCUIC feeds isErasable's tProp/isArity conditions |
| 4 Algorithmic specification | ~8:24-8:35 | Universe graphs, reduction-based conversion, bidirectional typing, cumulative-inductive pattern-matching fix | Low-Medium |
| 5 Metatheory | ~8:35-8:59 | Weakening/substitution, confluence, subject reduction, strong normalization, **5.6 weak CBV standardization** (source-language eval, direct ancestor of lambda-box eval), canonicity, consistency | High (5.6) -- defines the wcbv evaluation method later reused/amended for lambda-box; canonicity underlies erasability reasoning |
| 6 Sound/complete checker | 8:56-8:59 | Technical insight, abstract computational environment, fuel-free conversion/cumulativity, **6.4 retyping algorithm** used directly by erasure's `is_erasableb`, completeness bug fix, performance (11.2x slower than kernel on HoTT-light) | High (6.4) -- the exact decision procedure erasure depends on |
| **7 Type and proof erasure** | 8:59-8:64 | Target calculus lambda-box (7.1), erasure function (7.2), erasure relation + correctness (7.3), optimizations/erases_deps/full theorem (7.4) | **Highest** -- the reference-of-record for the erasure relation, isErasable, EWcbvEval amendments, erase_correct |
| 8 Related work | 8:64-8:6x | Mechanized metatheory/checkers (Barras, Strub et al.), certified erasure/extraction (Hupel-Nipkow, Myreen-Owens, Forster-Kunze, Glondu vs Letouzey), work building on MetaCoq (ConCert/Annenkov et al., Olesen/Futhark, CertiCoq, Forster et al. 2024 OCaml) | Medium -- positions ConCert/CertiCoq/OCaml-extraction lineage that Peregrine's backends use |
| 9 Conclusion/future work | ~8:6x-8:7x | Summary, future: verify Coq's OCaml extraction proper, lift restrictions (nested inductives, modules, eta) | Low-Medium |

## Key definitions and results

| id as printed | name | one-line statement | page |
|---|---|---|---|
| Fig. 16 | Syntax of lambda-box (`E.term`) | Untyped calculus: box, tRel, tLambda, tLetIn, tApp, tConst, tConstruct, tCase, tProj, tFix, tCoFix -- same shape as PCUIC minus type-only subterms, plus box | 8:60 |
| (Sec 7.1, unlabeled) | lambda-box wcbv evaluation, 3 amendments to Sec 5.6's relation | (1) `a ⇓ box` implies `tApp a t ⇓ box`; (2) `a ⇓ box` and branch-on-boxes `⇓ v` implies `tCase (i,p) a [(n,t)] ⇓ v` (Subsingleton elimination); (3) tFix rule extended to fire when the principal argument evaluates to box | 8:60 |
| Fig. 17 | Erasure function E (excerpt), via `Equations` | On `is_erasableb`=left, return box; else erase structurally, dropping type-only info (e.g. universe instance in tConst) | 8:61 |
| (Sec 7.2, unlabeled) | `isErasable` | `isErasable Σ Γ t := {T & Σ;Γ ⊢ t:T × (isArity T + Σ;Γ ⊢ T:tProp)}` -- t is erasable iff typeable by an arity (t is a type) or by something of sort tProp (t is a proof) | 8:61 |
| (Sec 7.2, unlabeled) | unique sort-quality / "sort quality equivalence" | coarser than cumulativity (identifies all Type sorts, symmetric), used to prove principality needed for `is_erasableb`'s completeness w.r.t. `isErasable` in presence of cumulative inductives | 8:61 |
| Fig. 18 | Erasure relation `Σ;Γ ⊢ t ⇝E t'` (excerpt) | Nondeterministic extension of E, closed under evaluation: structural rules (erases_tRel/tLambda/tApp/tConst/...), `erases_tCase` gated by `Subsingleton Σ ci.(ci_ind)`, and `erases_box : isErasable Σ Γ t -> Σ;Γ ⊢ t ⇝E box` | 8:61-8:62 |
| (unlabeled, Sec 7.3) | motivating counterexample | `(fun X:Type => (1, fun x:X=>x)) Type` shows eval-then-erase != erase-then-eval under the naive functional formulation, motivating the relational approach | 8:61-8:62 |
| Lemma `erases_erase` | erasure relation contains E's graph | `∀ Γ t wt Σ, X ~ext Σ -> Σ;Γ ⊢ t ⇝E (E Γ t wt)` | 8:62 |
| Lemma `simple_erases_correct` | general (non-optimized) erasure forward simulation | `wf Σ, welltyped Σ t, Σ ⊢ t⇓v, Σ;[]⊢t⇝E t', Σ⇝E Σ' ⊢> ∃v', Σ;[]⊢v⇝E v' ∧ Σ'⊢t'⇓v'` -- **stated but not the one actually proved** (superseded by the optimized version) | 8:62 |
| Def. (unlabeled) | `firstorder_ind` | An inductive `i` is first-order in Σ if all params/indices/constructor-argument types are (recursively) first-order applied inductives -- excludes proofs and function types | 8:62 |
| Lemma `firstorder_erases_deterministic` | E and the erasure relation coincide on first-order values | For values `v` of first-order inductive type, the erasure relation's image is exactly `E [] v wv` | 8:62 |
| Lemma `erase_correct_firstorder` | **erasure correctness theorem, first-order/observational form** | For closed, axiom-free Σ, first-order inductive `i`, `t : mkApps (tInd i u) args`, if `t ⇝* v` (irreducible), then `E [] t wt ⇓ E [] v wv'` -- the "strongest possible" result for the plain erasure function; separate-compilation corollary follows | 8:62-8:63 |
| Function `optimize` | propositional-case-branch inlining | Replaces `tCase` on a Prop-sorted inductive with box-only branches by direct substitution of the sole branch (avoids stuck extraction on box scrutinees); makes evaluation rule (2) above unnecessary post-pass | 8:63 |
| Class `WcbvFlags` / `with_prop_case` | evaluation flag record | Parametrizes lambda-box eval so rule (2) (box-discriminee case) can be disabled after `optimize` | 8:63-8:64 |
| Lemma `optimize_correct` | correctness of the optimize pass | `wf Σ, closed t, eval fl Σ t v -> eval (disable_prop_cases fl) (optimize_env Σ) (optimize Σ t) (optimize Σ v)` | 8:64 |
| Predicate `erases_deps` | dependency-pruned environment erasure | `erases_deps Σ Σ' t'` : Σ' obtained by erasing only Σ's declarations reachable from erased term t', bottom-up, using `abs_pop_decls` to drop unneeded decls -- models Coq's `Recursive Extraction` command | 8:64 |
| Lemma `erases_correct` | **full/final erasure correctness theorem** | `wf Σ, welltyped Σ t, Σ⊢t⇓v, Σ;[]⊢t⇝E t', erases_deps Σ Σ' t' ⊢> ∃v', Σ;[]⊢v⇝E v' ∧ Σ'⊢t'⇓v'` -- combines the relational correctness with dependency pruning; this (not `simple_erases_correct`) is the one actually proved | 8:64 |
| Sec 5.6, unlabeled | Weak call-by-value evaluation of PCUIC (source side) | One-shot big-step wcbv relation `Σ⊢t⇓v` on closed terms, built from one-step wcbv reduction (Fig. 11) + values (Fig. 12); lambda-box's eval (used in erasure) is this relation transported/amended, not independently invented | 8:46 |
| Lemma `progress` (5.6) | progress for wcbv reduction | `wf Σ, axiom_free Σ, Σ;[]⊢t:T -> {t' & Σ⊢t⇝wcbv t'} + value Σ t` | 8:46 |
| Lemma `SN_to_WN` (5.6) | strongly normalizing terms evaluate | `Acc (cored Σ []) t, Σ;[]⊢t:A -> {v & Σ⊢t⇓v}` | 8:47 |
| Lemma `wcbv_standardization` (5.6) | wcbv evaluation reaches the same normal form as full reduction | `Σ;[]⊢t:T, Σ;[]⊢t⇝*v, v irreducible -> {v' & Σ⊢t⇓v' ∧ Σ;[]⊢v'⇝*v}` -- **the only place strong normalization (an axiom) is used** in this part of the development | 8:47-8:48 |
| Sec 6.4, unlabeled | Retyping algorithm | Given a term and a proof it is well-typed, computes an explicit type by an optimized, assumption-exploiting variant of type inference (elides re-checking conversions already known valid); directly used by `is_erasableb` | 8:59 |
| Sec 6, unlabeled | Completeness bug | Verification found a source of incompleteness in Coq's official type checker, fixed in Coq 8.14 | 8:2, 8:4 |
| Def. `isArity` (used, not displayed as own figure) | arity | An n-ary dependent function type ending in a sort (i.e., t "is a type") -- one disjunct of `isErasable` | 8:61 |
| Def. `axiom_free` | axiom-freedom | `∀ c decl, declared_constant Σ c decl -> cst_body decl ≠ None` -- required for progress/erase_correct_firstorder since axioms could get stuck | 8:46 |

## Position in the pipeline

- **[kernel theory]**: yes, Section 3 (declarative PCUIC) and Section 4 (algorithmic PCUIC),
  fully mechanized in Coq.
- **[kernel verification / type-checker correctness]**: yes, Section 6, "sound and complete
  checker" -- soundness and completeness proved against the declarative spec; found and helped
  fix a real Coq completeness bug (8.14). For Coq/Rocq via the MetaCoq/MetaRocq project.
- **[erasure theory]**: yes, Section 7 in full -- lambda-box syntax/semantics, isErasable,
  erasure function and relation, correctness statements, for Coq/Rocq (PCUIC -> lambda-box).
- **[erasure verification]**: yes -- `erase_correct_firstorder` and `erases_correct` are proved
  in Coq (this is the "certified" in the title); axiom-dependence is isolated and stated
  (strong normalization, via `wcbv_standardization`, Sec 5.6; `axiom_free` hypothesis on Σ).
- **[erasure implementation]**: partially -- the erasure function/decision procedures (`E`,
  `is_erasableb`, retyping, `optimize`) are defined and extracted as part of MetaCoq's tooling
  (Sec 7.2, 7.4, 6.4), but this is the *type-and-proof erasure* stage only, not a full compiler.
- **[post-erasure pipeline]**: touched only in passing -- `optimize` (case-branch inlining) is
  the one post-erasure transform proved correct here (Sec 7.4); the paper explicitly defers
  full verified extraction to OCaml to future/companion work (Forster et al. 2024, cited
  Sec 8/9) and does not itself cover Malfunction, CertiCoq's C pipeline, or CertiCoq-Wasm.
- **[extraction implementation]**: no -- explicitly out of scope ("we plan to also verify Coq's
  extraction mechanism to OCaml... in future work", Sec 7 opening, p.8:59-60); notes only that
  Letouzey's actual MiniML extraction (with `Obj.magic`) is a separate, still-unverified layer
  built on top of the lambda-box erasure this paper verifies.

## Relation to the other sources named in the task

- **metarocq-project**: this is "The MetaCoq Project" (Sozeau, Anand, Boulier, Cohen, Forster,
  Kunze, Malecha, Tabareau, Winterhalter, JAR 2020) -- an earlier, **independent/prior-layer**
  paper covering the Template-Coq/MetaCoq **reification-and-typing-specification** stage (Coq
  8.9), chronologically and technically *prior to* and *not containing* the certified erasure
  machinery (EAst, isErasable, box) this JACM article establishes. Relation: metarocq-project is
  a foundational predecessor this article builds PCUIC/typing infrastructure on top of, not a
  sibling version of the same erasure result; the two are complementary rather than
  superset/subset on erasure specifically (metarocq-project has none), though metarocq-project's
  typing/reification layer is a subset of what this article's Sections 2-6 formalize in more
  depth and with completeness added.
- **coq-coq-correct**: this is "Coq Coq Correct! Verification of Type Checking and Erasure for
  Coq, in Coq" (Sozeau, Boulier, Forster, Tabareau, Winterhalter, POPL 2020) -- the **direct
  predecessor/conference version** this JACM article extends (the paper's own "Prior
  publication" note, p.8:5, cites it as Sozeau et al. 2019b). This article is the **journal
  superset**: it adds the completeness proof (via bidirectional typing as intermediate spec),
  restructures certification into two equivalence steps (declarative<->algorithmic<->decision
  procedure) instead of one, adds the first treatment of cumulative inductive types with subject
  reduction, and discharges as full proofs the erasure-correctness results that coq-coq-correct
  left as conjectures.
- **sozeau-habilitation**: presumably a broader synthesis (habilitation thesis) by the first
  author covering multiple projects; this article is one concrete, fully-detailed technical
  source likely **subsumed/surveyed at a higher level** there -- expect the habilitation to
  cite this JACM article as its primary erasure-correctness reference rather than duplicate the
  proofs.
- **letouzey-new-extraction**: this article's erasure method is explicitly **built on and
  verifies (a Coq-mechanized version of) Letouzey's** proof technique (Letouzey 2004 PhD thesis,
  cited repeatedly in Sec 7) -- Letouzey's original work is pen-and-paper / partially syntactic
  and targets MiniML with `Obj.magic`-based extraction to OCaml/Haskell/Scheme; this article
  verifies the *erasure-to-untyped-lambda-calculus* phase only (lambda-box), leaving the MiniML
  extraction step Letouzey also covers as future/companion work. So: this article is a
  **certified, restricted-target formalization** of a fragment of Letouzey's broader,
  unverified system.
- **lean-extraction-report**: presumably reports on Lean's own extraction mechanism; likely
  **independent** of this article (different source language, different erasure implementation)
  but shares the lambda-box target concept and evaluation-preservation goal structurally --
  useful as a terminology cross-reference (see Terminology map) rather than a formal ancestor.
- **metarocq-docs**: online/reference documentation for the MetaRocq software; **subset in
  formal content, superset in engineering/API detail** -- docs describe the current shipping
  `EAst`/`ExAst`/`EWcbvEval` etc. as implemented today (possibly renamed/refactored since this
  article's v1.2/Coq 8.16 snapshot), whereas this article is the fixed, dated theoretical
  reference with theorem statements and proofs. Cross-check names against docs since the
  Coq->Rocq rename and code evolution may have shifted identifier names post-publication.
- **carneiro-thesis**: independent -- presumably concerns a different kernel/foundations
  project (e.g. Metamath or Lean-related kernel verification by Mario Carneiro); no known
  formal dependency; relevant only as a comparandum in "mechanized metatheory of proof
  assistant kernels" (this article's own Related Work Section 8 surveys that same space --
  Barras 1996, Strub et al. 2012 -- and carneiro-thesis would sit alongside those).

## Terminology map

| This paper's term | Notion | Other sources' likely term |
|---|---|---|
| PCUIC | Predicative Calculus of Cumulative Inductive Constructions (the source calculus, Coq kernel minus modules/eta/template polymorphism/nested inductives) | "Coq's kernel language" / CIC (informally) |
| lambda-box (`E.term`, prefixed `E.`) | the untyped erasure target calculus with an explicit box constructor | Peregrine/MetaRocq: **EAst** (untyped constructors: tBox, tLambda, tApp, tConst, tConstruct, tCase, tFix, ...) -- this paper's `E.term`/box = EAst's `tBox` |
| box (□) | placeholder value/term for erased (computationally irrelevant) content | Peregrine glossary's **box (□)**; MetaRocq `tBox` |
| isErasable | the typing-based erasability predicate (`{T & t:T × (isArity T + T:tProp)}`) | MetaRocq/Peregrine: **isErasable** (same name, likely definitionally close); sometimes glossed as `is_box`/`Erasable` in adjacent literature |
| is_erasableb | boolean decision procedure reflecting isErasable, based on retyping | implementation-level name in MetaRocq's erasure checker; may appear as `is_erasable`/`inspect_erasable` variants in code |
| erasure relation (`⇝E`, Fig. 18) | nondeterministic nucleus of erasure correctness, extends the erasure function, closed under evaluation | MetaRocq: **erases** (the `Σ;Γ ⊢ t ⇝ t'` inductive relation is generally named `erases` in the Coq sources) |
| erasure function (E) | the deterministic, decidable erasure procedure (Fig. 17) | MetaRocq: **erase** |
| erases_deps | dependency-pruned, selective environment erasure relation | MetaRocq: **erases_deps** / "erasure of global environments" |
| firstorder_ind | syntactic first-order-ness of an inductive (no proofs/functions reachable) | may appear as "flat"/"data-only" inductive in other write-ups |
| Subsingleton | a Prop-sorted inductive with at most one non-erasable branch, licensing case-elimination through box | sometimes called a "squash type" / "singleton elimination" candidate elsewhere (Coq manual's own "singleton elimination" terminology) |
| wcbv evaluation (`⇓`), Weak Call-by-Value | one-shot big-step evaluation, weak (no reduction under binders/into fix-bodies), call-by-value (arguments evaluated before use) | Peregrine/lean-to-lambdabox: **EWcbvEval** (the "faithful WcbvEval" per this project's own MEMORY.md); "block-mode" pinning refers to the constructor-application convention layered on top of this same relation |
| optimize (case-branch inlining pass) | post-erasure transform collapsing Prop-sorted case analyses to their sole branch | in Peregrine's middle-end, analogous to (but not identical to) the "box pass" / part of what Peregrine's `extra_unsafe_transforms` group covers; not the same pass, but the same *kind* of post-erasure case-optimization idea |
| erase_correct_firstorder / erases_correct | the forward-simulation ("erasure correctness") theorem, in first-order/observational form and full form respectively | commonly cited elsewhere simply as **erase_correct** or "erasure preserves evaluation" |
| retyping algorithm | assumption-exploiting type-inference variant used by is_erasableb | sometimes called "type reconstruction" / "fast retyping" in MetaRocq's `PCUICSafeRetyping` module naming |
| Trusted Code Base -> Trusted Theory Base | the paper's framing for reducing what must be trusted from an implementation to a mathematical axiom (strong normalization) | reused informally elsewhere as "TCB/TTB"; Peregrine's own verification-landscape language ("verified modulo axiom X") echoes this framing |
