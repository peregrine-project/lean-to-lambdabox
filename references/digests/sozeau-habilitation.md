# Mechanized Metatheory and Certified Compilation for The Rocq Prover -- Matthieu Sozeau, Habilitation (HDR), Universite de Nantes, 2026

## Identity

Full entry: Matthieu Sozeau. *Mechanized Metatheory and Certified Compilation for The Rocq
Prover*. Computer Science [cs]. Universite de Nantes -- UFR Sciences et Techniques; Ecole
Doctorale MaSTIC (ED 641), 2026. HAL Id tel-05544162, submitted 10 Mar 2026,
https://nantes-universite.hal.science/tel-05544162v1. 152 pages, CC BY 4.0.

Exact object: an **Habilitation a Diriger des Recherches (HDR)** thesis, i.e. a
retrospective/synthesis manuscript, not a fresh research paper. It is explicitly a
manuscript-form aggregation: the front matter states "This manuscript is based on the following
articles" and lists four prior publications the two technical parts rewrite and extend (see
"Structure" and "Relation to the other sources" below). It carries its own French-language
introduction (pp. 3-9) preceding the English one (pp. 10-15), standard for French HDR theses.
Distinct from a PhD thesis (Sozeau has no separate PhD thesis in this line; his PhD was on
Russell/Program, a different topic) and from the individual papers it subsumes -- it is their
unifying, updated exposition, current as of MetaRocq v1.4 / Rocq 9.0.

## One-paragraph summary

This habilitation presents, as a single coherent development, roughly a decade of MetaRocq/MetaCoq
work: (Part I) a fully formal, declarative specification PCUIC of Rocq's core type theory
(universes, cumulativity, typing, well-formed global environments), an equivalent algorithmic
specification (acyclic-graph universes, reduction-based conversion, bidirectional typing), the
metatheory needed to connect them (confluence, subject reduction, weak call-by-value
standardization, canonicity, consistency -- all axiom-free except where strong normalization of
reduction is assumed), and finally a machine-checked **sound and complete type-checker** for
PCUIC, parametrized over decision procedures; and (Part II) a verified **type-and-proof erasure**
procedure from PCUIC to an untyped target calculus **lambda-box**, a pipeline of ~13 verified
program transformations that bring lambda-box operationally closer to real target languages
(constructors-as-blocks, unary fixpoints, parameter stripping, box-as-fixpoint, etc.), and a
verified compiler from (a variant of) lambda-box to **Malfunction**, OCaml's untyped
intermediate language, with a from-scratch Rocq formalization of Malfunction's operational
semantics and two correctness theorems: full simulation for first-order data, and safe
interoperability with arbitrary (even effectful) OCaml code for first-order functions. The thesis
frames its overall contribution as shifting proof-assistant trust from a "Trusted Code Base" to a
"Trusted Theory Base": modulo an abstract, axiomatized guard/strong-normalization assumption, the
Rocq type checker and the erasure+extraction-to-OCaml pipeline are proved correct in Rocq itself.

## What it establishes

- A declarative specification of PCUIC (syntax, universes, cumulativity, typing, well-formed
  environments including positivity, cumulative inductive types, allowed eliminations) ->
  Chapter 2 (Specifications 1-2, 18-19), pp. 26-43.
- An equivalent algorithmic specification (acyclic-graph universe checking, reduction-based
  conversion, bidirectional typing) and its correctness/completeness w.r.t. the declarative one,
  including the fix to cumulativity for pattern matching on cumulative inductives -> Chapter 3
  (Specs 4,6,7,8), pp. 44-56.
- Core metatheory: confluence via the triangle method, subject reduction, strong normalization
  (assumed as an axiom, its only use), weak call-by-value standardization, canonicity, consistency
  -> Chapter 4, pp. 58-71.
- A machine-checked, parametrized (over decision procedures), proof-carrying-code **type checker
  for PCUIC**, proved sound and complete w.r.t. the declarative specification, using an abstract
  global-environment interface and fuel-free weak-head normalization via a stack machine ->
  Chapter 5, pp. 73-84 (Specs 16-17).
- The target calculus **lambda-box** (Spec 20, p. 92) and its parametrized (WcbvFlags) weak
  call-by-value big-step semantics (Spec 21, pp. 92-94), including the three amended evaluation
  rules relative to PCUIC (eval_box, eval_iota_sing, unguarded eval_fix).
- The **isErasable** predicate and an erasure function `E` built via decision procedure
  `is_erasableb` and retyping (Spec 22, p. 95; Section 6.2), grounded in a "unique sort quality
  principle" needed because Prop <= Type must be disabled for erasability to be stable under
  expansion.
- The nondeterministic **erasure relation** `Sigma;Gamma |- t ~>_E t'` (Spec 23, p. 96) extending
  the function, with weakening/substitutivity/global-weakening lemmas, and the general
  (unproved-directly, superseded) correctness lemma `simple_erases_correct` plus the actual proved
  `erases_correct` using `erases_deps` for minimal/dependency-pruned environment erasure
  (Section 6.3-6.4, pp. 95-99) -> the **erasure correctness theorem**
  `erase_correct_firstorder`: for first-order-inductive-typed terms, evaluation commutes with
  erasure (p. 96), entailing separate compilation.
- The full **erasure pipeline** as 13 chained, individually verified `Transform.t` phases (Spec
  24-25, pp. 99-104), each with explicit pre/post-conditions and observational-equivalence
  relations on values (Section 6.5-6.6): eta-expand, TemplateRocq->PCUIC, lets-in-constructor-types
  (10kLoC of type-preservation proof), type-and-proof erasure, typed extraction (ConCert dearging),
  constructor reordering, unary fixpoint translation, parameter stripping, remove-match-on-box,
  inline-projections, constructors-as-blocks, implement-box-as-fixpoint, and global-environment
  AVL-tree rebuilding for efficient lookups.
- A from-scratch **operational semantics of Malfunction in Rocq** (Spec 26, p. 113-114;
  Section 7.4), derived from and sanity-checked against Malfunction's OCaml reference interpreter
  (finding two real bugs in it: a vector-bounds-check bug and an OCaml-4.14+flambda
  pattern-match miscompilation) -> Section 7.4.2, pp. 113-115.
- The Malfunction compilation pipeline's four extra passes (linearize-case, named-variable
  translation, enforce-extractability, lambda-box->Malfunction) -> Section 7.5, pp. 115-116.
- **Extraction Theorem for First-Order Data Types**, `verified_malfunction_pipeline_theorem`:
  full evaluation-preservation simulation from Rocq to Malfunction for closed, axiom-free,
  first-order-typed, eta-expanded terms -> Section 7.6, p. 117 (theorem statement).
- **Extraction Theorem for First-Order Functions**, `interoperability_firstorder_function`: safe
  interoperability with arbitrary (even effectful, nonterminating) OCaml code at first-order
  interfaces, via a realizability semantics (`camlType`, `v |- (adt,ind)`) and a
  decompilation theorem -> Section 7.7, pp. 118-119; the `assumes_purity`/`impure` counterexample
  showing the boundary of this guarantee is Section 7.1, pp. 110-112.
- Applications: drop-in replacement discussion vs. Rocq's native extraction (Section 7.8.1),
  self-hosting/bootstrapped compiler via Malfunction (Section 7.8.2), a new `<<<:` cast typing
  rule using verified extraction to implement conversion on closed first-order terms (Section
  7.8.3, p. 122), and microbenchmarks vs. Rocq's native OCaml extraction and CertiCoq/C (Figure 2,
  p. 123; Section 7.8.4).
- Related-work survey and explicit list of open problems (eta/SProp extensionality, guard-checker
  verification, primitive-op and cofixpoint coverage in extraction, proof-producing alternative to
  simulation) -> Chapter 8, pp. 127-131.

## Structure

| Section | Pages (printed) | What it covers | Relevance to Lean-to-lambda-box / lean4lean |
|---|---|---|---|
| Front matter, Fr./En. Introduction | 1-15 | Personal history of the MetaCoq/MetaRocq line of work (2014-2026); motivation (kernel bugs, TCB->TTB shift); manuscript outline; list of 4 source articles it is "based on"; Rocq-formalization stats (300kloc Rocq + 10kloc OCaml, MetaRocq v1.4, Rocq 9.0) | Medium -- gives dating/versioning and the authoritative subsumption list |
| Ch.1 Overview of Rocq's type theory | 19-24 | Informal tour: inductive types, positivity, sorts/universes, features in/out of PCUIC | Low |
| Ch.2 PCUIC: core calculus specification | 26-42 | Declarative syntax, universes, cumulativity (ordering/cumulativity/computation/congruence rules), guard as abstract parameter, typing, well-formed environments (positivity, cumulative inductives, allowed eliminations) | Medium -- source-language typing that erasure is proved against; not itself about lambda-box |
| Ch.3 Algorithmic specification of PCUIC | 44-56 | Universe valuation vs. acyclicity, reduction-based conversion/cumulativity, bidirectional typing + correctness/completeness, fix for cumulative-inductive pattern matching | Low-medium |
| Ch.4 Metatheory of PCUIC | 58-71 | Accessibility/WF induction, substitution/weakening, sigma-calculus, guard-checker correctness, confluence (triangle method), subject reduction, strong normalization, **weak call-by-value standardization** (Section 4.6 -- the semantics erasure/evaluation correctness is stated against), canonicity, consistency | Medium-high (4.6 defines the WcbvEval baseline lambda-box extends) |
| Ch.5 Sound and complete checker for PCUIC | 73-84 | Proof-carrying-code checker design (Equations, views, open recursion, monadic style), abstract global-environment interface, fuel-free conversion via weak-head-normalization stack machine, verified conversion, the checking algorithm, performance | Low -- kernel/type-checker layer, upstream of erasure |
| Conclusion Part I | 84 | Wrap-up of type-checking result | Low |
| **Ch.6 Type and Proof Erasure for PCUIC** | **91-105** | lambda-box syntax+semantics (Spec 20-21), erasure function `E` and `is_erasableb`/isErasable (Spec 22), erasure relation and its correctness incl. `erases_correct`/`erases_deps` (Spec 23), remove-match-on-box optimization, the 13-phase erasure pipeline (Spec 24-25) with per-phase pre/post-conditions | **High -- this is the direct erasure-theory/erasure-verification reference of record** |
| **Ch.7 Certified Extraction to OCaml** | **107-125** | Scope/limits of OCaml extraction (Obj.magic, the `assumes_purity` counterexample), choice of Malfunction as target and its from-scratch Rocq semantics (Spec 26), the extra Malfunction pipeline passes, the two central correctness theorems (first-order data, first-order functions/interoperability), applications (drop-in replacement, bootstrapping, `<<<:` cast, benchmarks) | **High -- post-erasure pipeline / extraction-implementation layer; the direct analogue of what a Lean or Agda erasure->target pipeline must match** |
| Ch.8 Related and Future Work | 127-131 | Positions vs. Barras, Abel-Ohman-Vezzosi, Adjedj et al., Anand-Rahli/Nuprl, Ouef, CertiCoq, ConCert, CakeML/Candle, Isabelle/HOL4-to-CakeML, Lean 4's unverified C backend, Idris 2, F*/KaRaMeL; explicit statement "A recent experiment was developed to compile Agda programs to lambda-box" (footnote 44, links agda2lambox); open problems | High for positioning claims (explicitly cites agda2lambox; frames Lean's backend as unverified) |
| Bibliography, List of Specifications/Figures | 133-152 | -- | Low |

## Key definitions and results (reference of record)

| id as printed | name | one-line statement | page |
|---|---|---|---|
| Specification 19 | PCUIC Typing rules | Full declarative typing judgment of PCUIC | 87 (stated after Ch.5, gathering typing+cumulativity) |
| Specification 20 | Syntax of lambda-box | `E.term` inductive: tBox, tRel, tLambda, tLetIn, tApp, tConst, tConstruct (block-form, `list E.term` arg), tCase, tProj, tFix, tCoFix, tPrim, tLazy, tForce | 92 |
| `Class WcbvFlags` | Evaluation flags | `with_prop_case`, `with_guarded_fix`, `with_constructor_as_block` -- one typeclass instantiates a whole family of eval relations | 92 |
| Specification 21 | lambda-box Weak call-by-value evaluation | Big-step `eval : E.term -> E.term -> Set`, extending PCUIC's WCBV with eval_box, eval_iota(_block/_sing), eval_fix(_value/_noguard), eval_cofix_case/proj, eval_delta, eval_proj(_block/_prop), eval_construct(_block), eval_app_cong, eval_prim, eval_force, eval_atom | 92-94 |
| (informal, Section 6.1) | Three amendments to PCUIC eval | (1) box absorbs application (eval_box); (2) `iota_sing`: subsingleton-Prop case with box discriminee reduces to the (boxed-substituted) single branch; (3) unguarded fixpoint unfolding on box-producing recursion | 92-93 |
| `Definition isErasable` | isErasable (source-language erasability) | `{T & Sigma;Gamma |- t : T x (isArity T + Sigma;Gamma |- T : tProp)}` -- t erasable iff typable at an arity or at a Prop-sorted type | 96 |
| Specification 22 | Erasure function `E` (excerpt) | Defined via Equations over `is_erasableb`; erasable terms -> tBox; else structural erasure of subterms | 95 |
| Specification 23 | Erasure relation (excerpt) | Nondeterministic `Sigma;Gamma |- t ~>_E t'`, agrees with `E` on first-order values; `erases_tCase` forces whole-case erasure unless the inductive is a Subsingleton | 96 |
| `Lemma erases_erase` | Erasure relation contains erasure function | The relation's graph includes `E`'s graph | 96 |
| `Lemma simple_erases_correct` | (superseded) simple erasure correctness | eval-preservation via the erasure relation, for a single global-env erasure `Sigma ~>_E Sigma'` (not proved directly; subsumed) | 96-97 |
| `Lemma firstorder_erases_deterministic` | Determinism on first-order values | On first-order-typed values, the erasure relation and function coincide | 97 |
| `Lemma erase_correct_firstorder` | **Erasure correctness theorem** | For axiom-free Sigma, first-order-inductive `i`, closed `t : mkApps (tInd i u) args` reducing (via non-det `~>*`) to irreducible `v`: `E [] t` evaluates (in lambda-box) to `E [] v` | 97 |
| `Definition remove_match_on_box` / `Lemma remove_match_on_box_correct` | Subsingleton-case elimination pass | Statically inlines the `eval_iota_sing` rule; eval-preserving, switches `with_prop_case` to false | 97-98 |
| `Lemma erases_correct` | Full erasure theorem w/ dependency pruning | Uses `erases_deps Sigma Sigma' t'` to erase only the reachable global environment; eval-preservation modulo that | 98-99 |
| Specification 24 | The erasure pipeline | 13-stage `Transform.t` composition: build-env, eta-expand, template->pcuic, erase, reorder-cstrs, guarded->unguarded-fix, remove-params, rebuild-env, optimize-prop-discr, rebuild-env, inline-projections, rebuild-env, constructors-as-blocks | 99 |
| Specification 25 | Definition of transformations (`Transform.t`) | Generic record: `pre`, `post`, `transform`, `correctness`, `obseq`, `preservation` -- the compositional verified-compiler-phase abstraction used throughout | 100 |
| Section 6.6.1-6.6.13 | The 13 individual transformation phases | Eta-expand (assumed correct); TemplateRocq->PCUIC; lets-in-constructor-types (10kLoC type-preservation); type/proof erasure; ConCert typed extraction/dearging; constructor reordering (permutation-indexed, e.g. Rocq bool vs OCaml bool); unary-fixpoint translation; parameter stripping; remove-match-on-box; inline-projections; constructors-as-blocks; implement-box-as-`fix f x := f`; AVL-tree global-env rebuilding | 100-104 |
| Specification 26 | Syntax of Malfunction formalized in Rocq | `Malfunction.t` inductive: Mvar, Mlambda, Mapply, Mlet, Mnum, Mstring, Mglobal, Mswitch, Mnumop1/2, Mconvert, Mvecnew/get/set/len, Mlazy, Mforce, Mblock, Mfield, with `binding` (Unnamed/Named/Recursive) | 113 |
| Section 7.4.2 | Malfunction `eval` relation in Rocq | Inductive, heap-explicit, weak CBV `eval (locals : Ident.t -> value) : heap -> t -> heap -> value -> Prop`, derived/sanity-checked against the OCaml reference interpreter (found 2 real interpreter/compiler bugs) | 114-115 |
| Theorem `verified_malfunction_pipeline_theorem` | **Extraction Theorem for First-Order Data Types** | Axiom-free, eta-expanded, first-order-typed `t` reducing to irreducible `v`: `eval Sigma' empty_locals h (compile_malfunction_pipeline ... t) h (compile_value_mf Sigma v)` -- heap unchanged | 117 |
| `Inductive camlType` / `Definition ADT` | OCaml-side type/value representation | `Arrow | Rel n | Adt kername nargs (list camlType)`; ADT = nargs x list-of-constructors-of-camlType-lists; realizer relation `v |- (adt,ind)` | 118 |
| Theorem `interoperability_firstorder_function` | **Extraction Theorem for First-Order Functions** | For well-typed first-order `f : I -> I'`, any argument realizing `adt` at `ind` that terminates gives a result realizing `adt` at `ind'` under Malfunction application -- safe interop even with effectful/nonterminating OCaml code | 118-119 |
| Section 7.1 example | `assumes_purity`/`impure` counterexample | Shows a well-typed-in-OCaml, higher-order-dependent extracted function that segfaults when applied to an impure OCaml closure -- delimits exactly where the correctness theorems stop applying | 110-112 |
| Section 7.5.3 | Enforce-extractability conditions | 5 side-conditions (constructor-count/arity bounds fitting OCaml int/array, axiom-freedom, no residual box/proj/cofix) assumed via an Axiom, not enforced by aborting compilation | 116 |
| Section 7.8.3, rule `Cast-Erase` | `<<<:` cast typing rule | New bidirectional typing rule using bootstrapped erasure+Malfunction evaluation to decide convertibility of closed first-order inductive terms, admissible via the extraction theorems | 122 |
| Figure 2 | Microbenchmarks | Runtime of Rocq-native-OCaml-extraction vs. verified-extraction-to-Malfunction vs. CertiCoq/C on demo1/demo2/list_sum/vs_easy/vs_hard/binom/color/sha, normalized to Malfunction -O2 | 123 |

## Position in the pipeline

- [kernel theory]: yes -- Chapters 1-2 (PCUIC declarative specification), for **Rocq**.
- [kernel verification (type checker correctness)]: yes -- Chapters 3-5 (algorithmic spec,
  metatheory, sound+complete checker), for **Rocq**.
- [erasure theory]: yes -- Chapter 6, Sections 6.1-6.4 (lambda-box calculus, erasure function and
  relation, correctness theorem), for **Rocq/PCUIC**.
- [erasure verification]: yes -- same sections; `erase_correct_firstorder`/`erases_correct` are
  machine-checked in Rocq, for **Rocq**.
- [erasure implementation]: yes -- Section 6.5-6.6, the 13-phase erasure pipeline shipped as part
  of MetaRocq, for **Rocq**.
- [post-erasure pipeline]: yes -- Section 6.5-6.6 (pipeline phases through constructors-as-blocks)
  and Chapter 7's Malfunction-specific extra passes (Section 7.5), for **Rocq -> lambda-box ->
  Malfunction**.
- [extraction implementation]: yes -- Chapter 7 in full: Malfunction Rocq semantics, compiler,
  correctness theorems, applications/benchmarks, for **Rocq -> OCaml via Malfunction**.
- Not covered for any prover other than Rocq/PCUIC: this manuscript is Rocq-only end to end; Lean
  and Agda appear solely in the related-work/future-work discussion (Chapter 8, explicitly citing
  agda2lambox in a footnote, and noting Lean 4's compiler-to-C backend as *unverified*).

## Relation to the other sources named in the task

- **sozeau-habilitation** (this document) is a **superset/successor** of **coq-coq-correct**
  (POPL'20): the habilitation's Part I (Chapters 1-5: PCUIC spec, algorithmic equivalence,
  metatheory, sound+complete checker) is explicitly the updated, feature-extended write-up of that
  paper's kernel-verification content (cumulative inductive types, universe handling, and the
  bidirectional-typing completeness fix in Section 3.4 post-date and extend the conference
  version). It adds material (guard-as-abstract-parameter framing, performance discussion, updated
  MetaRocq v1.4 numbers) not in the original paper.
- It is a **superset/successor** of **metacoq-erasure-jacm** (JACM 2025, "Correct and Complete
  Type Checking and Certified Erasure for Coq, in Coq") -- the front matter lists this JACM paper
  first among the four source articles, and it is the direct ancestor of *both* Part I (checker)
  and Chapter 6 (erasure theory/correctness) here; the habilitation reproduces its erasure relation,
  isErasable, and `erase_correct_firstorder`-style theorem essentially verbatim, updated to current
  MetaRocq naming (Rocq vs Coq) and reorganized as chapters rather than a single paper's sections.
- It is a **superset/successor** of the PLDI'24 "Verified Extraction from Coq to OCaml" paper
  (second source article listed): Chapter 7 is that paper's content re-exposed, extended with the
  Section 7.8.3 `<<<:` cast-typing application (not in the original PLDI paper) and updated
  benchmark numbers/commit references.
- It is a **superset/successor** of **metarocq-project** (JAR 2020, "The MetaCoq Project" --
  fourth source article listed): that paper is the original whole-project overview (quoting,
  template-coq, early erasure); the habilitation supersedes its scope with a decade's worth of
  further-developed, machine-checked results, while the JAR paper remains the reference for the
  meta-programming/quotation layer that this habilitation does not re-detail.
- Relative to **letouzey-new-extraction** (Letouzey's PhD, cited throughout as "[81]"): the
  habilitation explicitly positions itself as **formalizing and completing** Letouzey's
  pen-and-paper erasure-correctness theorems (Thm 6 and Thm 9 of [81], cited by page number, p.
  107) inside Rocq -- i.e. sozeau-habilitation is the machine-checked descendant of
  letouzey-new-extraction's erasure relation and its "erasure of higher-order functions" theorem;
  it also explicitly reproduces Letouzey's `assumes_purity`-style discussion (Section 7.1, citing
  Letouzey Section 3.1.3/3.2.1) as its own counterexample.
- Relative to **lean-extraction-report** (a report on Lean's own erasure/extraction, presumably
  the Lean-to-lambdabox project's own writeup): **independent**, cited only glancingly -- the
  habilitation mentions "Lean 4 proof assistant comes with unverified compilation to C" (Section
  8.2.3, p. 130) as related but unverified work, and separately notes (Chapter 6, "Uses of the
  erasure pipeline," p. 104) that lambda-box "can also be used as a target for other proof
  assistants like Agda, Idris or Lean," directly anticipating the lean-to-lambdabox project's
  premise without describing or verifying it itself.
- Relative to **metarocq-docs** (the online MetaRocq documentation): **superset in exposition,
  subset in exact code-level detail** -- the habilitation is a curated, prose-and-theorem
  narrative referencing the same Rocq development (and explicitly points the reader to "the Rocq
  formalization for details" and to the docs' table of contents, p. 15), whereas metarocq-docs is
  the more exhaustive, always-current API-level reference.
- Relative to **carneiro-thesis** (presumably Mario Carneiro's thesis on Metamath Zero /
  lean4lean-adjacent kernel verification): **independent** -- not cited in this manuscript at all;
  no direct relation stated. Both works share the general genre of machine-checked kernel/erasure
  verification for a proof assistant but for different systems (Rocq here vs. Lean/Metamath
  there), with no explicit cross-reference in either direction found in this document.

## Terminology map

| This source's term | Meaning | Other sources' term(s) |
|---|---|---|
| lambda-box / lambda\_\_ (rendered `𝜆□`) | Untyped target calculus of erasure | Same term used identically by metacoq-erasure-jacm, letouzey-new-extraction (as "the target of extraction"), and by lean-to-lambdabox / Peregrine docs as "lambda-box"/"LambdaBox" |
| `isErasable` | Source-typing-based erasability predicate (`{T & t:T x (isArity T + T:Prop)}`) | Same name in metacoq-erasure-jacm/MetaRocq source; conceptually the same role as "is_box"/"Erasable" terminology used in some lean-to-lambdabox internal writeups |
| `is_erasableb` | Decidable/boolean reflection of `isErasable`, via retyping | Sometimes glossed elsewhere as "erasure oracle" or "isErasableRel"-style boolean check |
| `eval` (lambda-box, Specification 21) | Big-step weak call-by-value evaluation of lambda-box, flag-parametrized | Same relation is what Peregrine/lean-to-lambdabox call **EWcbvEval** (the "faithful WcbvEval" unified semantics per this project's own memory notes) |
| PCUIC | Predicative, Polymorphic Calculus of CUmulative Inductive Constructions -- the formalized core of Rocq's type theory | Referred to elsewhere simply as "Rocq's/Coq's kernel calculus" or CIC-with-cumulativity |
| Constructor "block" representation (`with_constructor_as_block`, `tConstruct ind c args`) | Fully-applied constructors carrying their argument list directly in the AST node | Matches Peregrine/agda2lambox's "block vs applied form" distinction exactly; this source's "block" = Peregrine's "block", vs. the alternative "applied through tApp" form |
| Malfunction | OCaml's untyped compiler-internal IR, target of the verified extraction backend | Same term, used identically across all sources discussing the `ocaml`/malfunction backend |
| `erases_deps` | Dependency-pruning relation restricting erased global environments to reachable declarations | Not given a distinct name elsewhere in this fan-out; functionally what other erasure write-ups may call "minimal/relevant environment erasure" |
| Trusted Code Base (TCB) / "Trusted Theory Base" (TTB) | This source's framing for what remains unverified after this work (guard/normalization axiom only) | General proof-assistant-verification terminology; not given a distinct name in the sibling sources, though the same TCB-reduction goal is the shared motivation across metacoq-erasure-jacm, letouzey-new-extraction discussion of extraction's trust status, and Peregrine's own "Verification landscape" framing |
| `remove_match_on_box` | Pass eliminating pattern-matching on `tBox`/subsingleton residues | Corresponds to Peregrine pipeline's own "remove match on box" transform (same name, same role) |
| `constructors_as_blocks_transformation` | Pass converting eta-expanded bare constructor applications into block-form `tConstruct` nodes | Corresponds directly to Peregrine's "constructors as blocks" backend requirement / the "block vs applied form" trap noted in Peregrine's CLAUDE.md |
| `Transform.t` | Generic record type packaging a compiler pass with pre/post-conditions, an evaluation-preservation theorem, and an observational-equivalence relation on values | Not named identically elsewhere in this fan-out, but the same "verified compiler pass" shape (pre/post + simulation theorem) is the pattern metacoq-erasure-jacm and metarocq-project use for individual erasure phases, and the pattern lean-to-lambdabox's own pipeline transforms (fix-unfolding, Nat-literal, etc., per this project's memory notes) are modeled on |
| firstorder\_ind / "first-order data type" | An inductive whose parameters, indices, and constructor arguments are themselves (recursively) first-order inductive applications -- i.e. contains no functions or proofs | The qualifying condition under which erasure/extraction correctness is unconditional; comparable to "closed term of ground type" phrasing used informally in benchmark write-ups (e.g. Peregrine's backend_bench closed-term digest programs) |
| realizer / `v |- (adt, ind)` | Semantic-typing (realizability) relation between an untyped Malfunction value and an OCaml-shaped algebraic-data-type description | A logical-relations notion; Letouzey's PhD proves an analogous but weaker higher-order-function correctness result via logical relations (letouzey-new-extraction, Thm 9) without naming it "realizability" |

## Notable side findings reported in the source

- **Two real bugs found in Malfunction's own OCaml reference interpreter/compiler** while
  sanity-checking the Rocq-formalized semantics against it (Section 7.4.2, p. 115): (1) an
  out-of-bounds vector access that crashed instead of being reported by a bound check; (2) a
  miscompilation of pattern matching under OCaml 4.14+flambda, producing wrong values or
  segfaults. Neither bug is load-bearing for the correctness theorems (the sanity check itself
  switches off Rocq's termination checker and is explicitly "not required" for the main results),
  but both are concrete evidence the target-language trust boundary is not merely theoretical.
- **Extraction can currently produce genuinely ill-typed terms**: the manuscript notes in the
  Motivation section (p. 12) that during development of the type-checking algorithm itself, Rocq's
  *existing*, unverified extraction produced an ill-typed OCaml term -- cited as direct evidence
  motivating the whole verified-extraction effort.
- **`color` benchmark cannot run under Rocq's native OCaml extraction at all** (Section 7.8.4,
  p. 123): the generated code contains type errors, so that benchmark is excluded from the
  OCaml-extraction comparison columns of Figure 2 while still being run through Malfunction and
  CertiCoq/C.
- The habilitation explicitly disclaims proving Rocq's consistency (an appeal to Godel's second
  incompleteness theorem, p. 12): all correctness results are conditional on an axiomatized
  guard/strong-normalization assumption, which the author frames as the sole "Achilles heel" of
  the whole development.
