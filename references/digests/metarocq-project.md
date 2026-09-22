# The MetaCoq Project -- Sozeau, Anand, Boulier, Cohen, Forster, Kunze, Malecha, Tabareau, Winterhalter, Journal of Automated Reasoning 64:947-999, 2020

## Identity

Full entry: M. Sozeau, A. Anand, S. Boulier, C. Cohen, Y. Forster, F. Kunze, G. Malecha,
N. Tabareau, T. Winterhalter, "The MetaCoq Project", Journal of Automated Reasoning
64:947-999 (2020), https://doi.org/10.1007/s10817-019-09540-0. Received 30 Apr 2019,
accepted 19 Dec 2019, published online 18 Feb 2020, (c) Springer Nature B.V. 2020.

Object type: journal article (JAR), 53 pages (pp. 947-999, printed pagination 947-998 body
+ refs to 999). It is the extended journal version of an ITP'18 conference paper "Towards
Certified Meta-Programming with Typed Template-Coq" (Anand, Boulier, Cohen, Sozeau,
Tabareau, ITP 2018, ref [5] in this paper). Per the paper's own "What is new" note (p. 952,
end of Sect. 1.3), the journal version adds: (1) a complete exposition of Coq's type system
formalization (all of Sect. 2, described as previously only "on paper" in the reference
manual), (2) the certified `tauto` tactic example (Sect. 4.2), and (3) the extraction-to-weak-CBV-lambda-calculus
plugin (Sect. 4.4). The system described (Coq 8.9, noted explicitly p. 951) is the
**Template-Coq / MetaCoq reification-and-typing-specification** stage of the project — this
is chronologically and technically prior to, and does not itself contain, the certified
**erasure** machinery (EAst, isErasable, box) that peregrine's pipeline is built on; that is
the subject of the later `metacoq-erasure-jacm` paper (Sozeau et al., JACM 2025) named
elsewhere in this fan-out.

## One-paragraph summary

The paper presents Template-Coq/MetaCoq: a reification of Coq's kernel term syntax (`term`,
mirroring `constr`, Fig. 1) and of Coq's global/local environments into an inductive type in
Coq itself, together with a formal, on-paper-style but Coq-mechanized specification of Coq's
typing judgment, conversion/cumulativity, reduction and universe algebra (Sect. 2) — stated
as a full account of a subset of CIC (no eta, no template polymorphism, no modules, no guard/positivity
checking, no cumulative inductives, pre-8.10 Coq). On top of the reification it builds the
`TemplateMonad`, a free monad reifying Coq's vernacular commands (quoting, unquoting,
declaring definitions/inductives/axioms, printing, running interactive obligations), letting
users write meta-programs ("plugins") directly in Coq (Sect. 3-4), demonstrated on an
inductive-constructor-adding plugin, a certified `tauto` tactic, a unary-parametricity
translation, and — as the paper's fourth and final example, added for the journal version —
a hand-written, restricted, *not fully verified-end-to-end* extraction of a first-order-ish
polymorphic Coq fragment into Forster & Smolka's untyped weak-call-by-value lambda-calculus
via Scott encodings (Sect. 4.4), independent of and different in kind from the later
certified MetaCoq erasure to EAst/lambda-box. Section 5 covers running these plugins after
extraction to OCaml via a "phase-split" `TM` monad that separates object-language (`Ast.term`)
from meta-language values, because naive extraction of `TemplateMonad` is impossible.

## What it establishes

- A Coq inductive type `term` reifying the full syntax of Coq/Gallina terms (sorts, `tRel`,
  `tCast`, `tProd`, `tLambda`, `tLetIn`, `tApp`, `tConst`, `tInd`, `tConstruct`, `tCase`,
  `tProj`, `tFix`, `tCoFix`) -> Sect. 2.1, Fig. 1, pp. 952-954.
- A full bidirectional-style typing judgment `Sigma ;;; Gamma |- t : T` given as an
  Coq-mechanized inductive relation covering all term formers, including primitive
  projections (`type_Proj`, p. 962) and fixed/cofixed points (`type_Fix`/`type_CoFix`,
  pp. 963-964) and a conversion/cumulativity closure rule (`type_Conv`, p. 964) -> Sect. 2.3,
  pp. 956-964.
- A reduction relation `red1` (one-step, congruence + beta/zeta/iota/fix-unfolding/
  cofix-unfolding/delta/projection rules) and cumulativity/conversion defined from it
  (`cumul`, `conv`) -> Sect. 2.4, pp. 964-967.
- Well-formedness of local contexts (`wf_local`/`All_local_env`) and of global environments
  (`on_global_env`, fresh names, well-formed universe declarations) and of inductive
  declarations (`mutual_inductive_body`, `one_inductive_body`, positivity NOT checked) ->
  Sect. 2.5, pp. 967-970.
- A formal universe algebra: levels, algebraic universes, `valuation`, constraint
  satisfiability, `eq_universe`/`leq_universe` -> Sect. 2.6, pp. 970-972.
- Unverified (no soundness/completeness proof yet, stated explicitly p. 973) executable
  algorithms `infer`/`check`/`check_conv` with a fuel parameter, plus a naive Bellman-Ford
  universe-graph consistency checker -> Sect. 2.7, pp. 972-973.
- The `Template-Coq` plugin: `Test Quote`/`Quote Definition`/`Make Definition`/`Quote
  Recursively Definition`/`Make Inductive` commands moving between concrete and reified
  syntax -> Sect. 3.1, pp. 973-974.
- The `TemplateMonad` free-monad reification of Coq vernacular commands (`tmDefinition`,
  `tmAxiom`, `tmLemma`, `tmQuoteInductive`, `tmMkInductive`, `tmUnquoteTyped`, ... — Table 1,
  Fig. 2) -> Sect. 3.2, pp. 974-977.
- Worked example plugins: constructor-adding plugin (Sect. 4.1, pp. 978-979), certified
  `tauto` decision procedure with a reflection-based correctness proof modulo one Ltac hole
  noted in Remark 5 (Sect. 4.2, pp. 979-984), a unary parametricity translation and a
  "times-bool" translation with a `NotFunext`-axiom-introducing correctness caveat about
  eta-conversion (Sect. 4.3, pp. 984-991, Fig. 3).
- A restricted, hand-verified-per-instance extraction to the weak-CBV lambda-calculus of
  Forster & Smolka via Scott encoding (`tmEncode`, `tmExtract`, `tmGenEncode`, a `computable`
  type class with per-fixpoint/per-match correctness lemmas w.r.t. reduction `>*`) -> Sect.
  4.4, pp. 991-994.
- The `TM`/phase-split monad enabling plugins to run as native, extracted OCaml programs ->
  Sect. 5, pp. 994-997.

## Structure

| Section | Pages | What it covers | Relevance to lean-to-lambdabox / lean4lean |
|---|---|---|---|
| 1 Introduction (+1.1-1.3) | 948-952 | Motivation, first example plugin, explicit list of departures from real Coq (no eta, no guard check, no positivity, no template polymorphism, no cumulative inductives, no modules), what's new vs. ITP'18 | Low — scoping/history context only |
| 2.1 Reification of terms | 952-955 | `term` inductive (Fig. 1), examples, de Bruijn conventions | Medium — canonical source-calculus AST shape that PCUIC/EAst later specialize; useful for cross-checking what a "faithful surface term" looks like pre-erasure |
| 2.2 Reification of environment | 955-956 | context, global declarations (brief) | Low |
| 2.3 Typing judgements | 956-964 | Full inductive typing relation for every term former, incl. fix/cofix and primitive projections | Medium — baseline kernel typing rules that any erasure-soundness statement (isErasable etc., in the sibling erasure paper) is stated *relative to*; useful background for the source side of the forward-simulation, but this paper itself proves no metatheory about it |
| 2.4 Conversion/cumulativity/reduction | 964-967 | `red1`, beta/zeta/iota/fix-unfold/cofix-unfold/delta/proj rules, `cumul`, `conv` | Medium — direct ancestor of the reduction rules erasure/lambda-box semantics must mirror at the source level (iota/fix-unfolding shape is structurally close to lambda-box's own iota/fix rules) |
| 2.5 Typing environments | 967-970 | `wf_local`, `on_global_env`, `mutual_inductive_body`/`one_inductive_body` well-formedness, no positivity check | Medium — environment/declaration shape that erasure's "environment erasure" (in the erasure paper) consumes as input |
| 2.6 Universes | 970-972 | Universe algebra, valuations, constraint satisfiability | Low for lambda-box itself (erased away), but relevant to isErasable's `Prop`/`Set`/`Type` sort case analysis in later erasure work |
| 2.7 Towards bootstrapping Coq | 972-973 | Unverified `infer`/`check`/`check_conv` + universe-graph algorithms, explicitly no soundness/completeness proof yet | Medium — this is the *predecessor, unverified* stage of what `coq-coq-correct` later proves correct; useful to cite as "before" |
| 3 The Template-Coq plugin | 973-977 | Quote/unquote commands, `TemplateMonad`, Table 1, Fig. 2 | Low — meta-programming API, not semantics |
| 4.1-4.3 Plugins in Coq | 977-991 | Constructor-adding, certified tauto, parametricity translations | Low — illustrative, not pipeline-relevant |
| 4.4 Extraction to lambda-calculus | 991-994 | Restricted admissible-types extraction to Forster-Smolka's untyped weak-CBV lambda-calculus via Scott encoding; per-definition `computable`/correctness-lemma discipline, not a general theorem | High for terminology/history, but note: this is a **different target language and a different, weaker verification discipline** than the later certified MetaCoq erasure to EAst/lambda-box that CertiCoq/peregrine build on — do not conflate the two |
| 5 Running plugins in OCaml | 994-997 | `TM` phase-split monad, extraction of TemplateMonad programs to OCaml, performance numbers | Low |
| 6 Related work / refs | 997-999 | Related meta-programming work; no discussion of erasure correctness | Low |

## Additional detail on Sects. 2.1-2.2 (source-calculus representation)

Two caveats worth carrying forward when citing this paper as the reference for the
source-term representation:

- `tVar` (named variables from Coq sections/interactive proofs) and `tEvar` (existential
  variables/holes) are included in the `term` reification (Fig. 1) but the paper states
  explicitly (p. 955) that **typing is not defined for these two constructors** "for the
  moment" — the typing judgment of Sect. 2.3 is total only over the other constructors.
  Any later claim of "MetaCoq's typing relation covers all terms" should be checked against
  whether `tVar`/`tEvar` were later handled or remain excluded, and whether the sibling
  erasure paper's source language inherits this gap.
- Example 2 (p. 954) works through the representation of `Fixpoint add (a b : nat) : nat :=
  match a with 0 => b | S a => S (add a b) end` as a concrete `tFix [...] 0` term, showing
  the `tCase (inat, 0) <motive> <scrutinee> [(0, branch0); (1, branch1)]` shape and the use of
  `tConstruct inat 1 [ ]` applied via `tApp` for the successor case — i.e., this example
  already uses the "applied form" of a constructor (bare `tConstruct` under `tApp`) rather
  than the "block form" (arguments folded into the `tConstruct` node itself) that the
  peregrine-tool ecosystem calls out as a recurring cross-frontend inconsistency; note,
  however, that this is the *source* (pre-erasure) representation, not lambda-box's own
  block-vs-applied distinction, which this paper does not discuss.
- Environment reification (Sect. 2.2, pp. 955-956): the global environment is `global_env :=
  list global_decl` with `global_decl := ConstantDecl kername constant_body | InductiveDecl
  kername mutual_inductive_body`; an extended global environment `global_env_ext := global_env
  * universes_decl` additionally carries universe declarations used to typecheck one
  declaration. `constant_body` records `cst_type`, `cst_body : option term` (`None` for an
  axiom), and `cst_universes`. Local contexts (`context := list context_decl`) are in snoc
  order, written `Gamma ,, d`; `vass`/`vdef` build assumption/definition entries; `Gamma ,,,
  Gamma'` is concatenation. Remark 1 (p. 955) flags that MetaCoq's de Bruijn indices start at
  0, whereas Coq's own OCaml kernel implementation starts them at 1 — a numbering
  discrepancy worth remembering when cross-checking indices against Coq-internal traces.

## Key definitions and results (reference of record)

| id as printed | name | one-line statement | page |
|---|---|---|---|
| Fig. 1 | `term` inductive | MetaCoq's reification of Coq's kernel `constr` type: `tRel, tVar, tMeta, tEvar, tSort, tCast, tProd, tLambda, tLetIn, tApp, tConst, tInd, tConstruct, tCase, tProj, tFix, tCoFix` | 953 |
| (unnamed) | `mfixpoint`/`def` record | `dname, dtype, dbody, rarg` for a mutual (co)fixed-point block | 954 |
| `type_Rel`/`type_Sort`/... | core typing rules | typing rule per term constructor (`tRel`, `tSort` — only non-algebraic universes typeable, Remark 2) | 956-957 (rule names p.957 area) |
| `type_Prod`, `type_Lambda`, `type_LetIn`, `type_App` | typing rules | product/abstraction/let/application typing | ~959-961 |
| `type_Const`, `type_Ind`, `type_Construct` | typing rules | typing of constant/inductive/constructor references via `universe_instance` | ~961 |
| `type_Case` | typing rule | pattern-match typing, checks branch types via `All2` against `btys` and arities via `fst` component | 961-962, 962 |
| `type_Proj` | typing rule | primitive-projection typing via `declared_projection`, requires `#|args| = ind_npars mdecl` | 962 |
| `type_Fix` | typing rule | mutual fixed-point typing: extends context with `fix_context mfix`, requires each body `isLambda`, no termination check implemented | 963 |
| `type_CoFix` | typing rule | analogous rule for cofixed points, no productivity check implemented | 963-964 |
| `type_Conv` | typing rule | conversion/cumulativity closure of typing, requires target well-sorted | 964 |
| (unnamed, `cumul`) | cumulativity | `cumul_refl`/`cumul_red_l`/`cumul_red_r`: A <= B iff they reduce to syntactically-`leq_term`-comparable normal forms | 964-965 |
| (unnamed, `conv`) | conversion | `conv := cumul /\ cumul-flipped` | 965 |
| `red_beta`, `red_zeta`, `red_rel`, `red_iota`, `red_fix`, `red_cofix_case`, `red_cofix_proj`, `red_delta`, `red_proj` | one-step reduction rules | beta/zeta(-eager and -lazy via `red_rel`)/iota/fix-unfolding (guarded by `is_constructor`)/cofix-unfolding-on-case/cofix-unfolding-on-proj/delta/projection-reduction | 965-967 |
| (unnamed) | `iota_red` | `iota_red npar c args brs := mkApps (nth c brs) (skipn npar args)` — the concrete iota-reduction function | 966 |
| (unnamed) | `All_local_env`/`wf_local` | inductive well-formedness of local contexts (assumption well-sorted / definition well-typed) | 967 |
| (unnamed) | `on_global_env`/`on_global_decl` | well-formedness of global environments: fresh names, satisfiable universe constraints, well-typed constant/inductive bodies | 967-968 |
| (unnamed) | `mutual_inductive_body`/`one_inductive_body` | records for a block of mutual inductive types; explicit well-formedness conditions (arity shape, constructor typing under arity context, squashed-Prop exception, no positivity check, no `ind_kelim` check) | 968-970 |
| Remark 4 | body vs. entry | Coq internally has two representations (bodies vs. entries); kernel elaborates entries to bodies; MetaCoq provides `mind_body_to_entry` | 969-970 |
| (unnamed) | `level`/`universe` | `level := lProp | lSet | Level string | Var N`; `universe := list (level * bool)`; algebraic vs. non-algebraic universes | 971 |
| (unnamed) | `valuation`, `consistent`, `eq_universe`, `leq_universe` | universe-constraint semantics: satisfiability and equality/order of universes under a valuation | 971 |
| (unnamed) | `infer`/`check`/`check_conv` | fuel-parameterized, **unverified** (no soundness/completeness proof stated, p. 973) type-checking algorithms mimicking Coq's WHNF-based abstract machine, sans memoizing/lazy reduction | 972-973 |
| Table 1, Fig. 2 | `TemplateMonad` commands | vernacular-command reification table (`tmDefinition`, `tmQuoteInductive`, `tmMkInductive`, `tmUnquoteTyped`, etc.) | 975-976 |
| Sect. 4.4 (unnamed) | weak-CBV lambda-calculus target | `s,t,u,v : lterm ::= n | s t | \s` (de Bruijn); Scott encodings `eps_bool`, `eps_nat`; fixpoint combinator `rho` with correctness schema `rho u v >* u (rho u) v` | 991-993 |
| Sect. 4.4 (unnamed) | admissible types/terms | restriction of the extraction target: `A` admissible iff `forall X1..Xn:Type. B1 -> ... -> Bm` with `Bm <> Type`; terms admissible under a syntactic left/right-application discipline for type-parameter instantiation | 993 |
| Sect. 4.4 (unnamed) | `computable`/correctness relation | `ta ~ a` ("ta computes a"), a logical relation between extracted lambda-terms and Coq values, established per-definition via Ltac, not a blanket theorem | 993-994 |
| Sect. 5 (unnamed) | `TM` / phase-split monad | extractable variant of `TemplateMonad` separating object-language `Ast.term` values from meta-language (Coq) values, to make plugins extractable to OCaml | 994-996 |

Not present in this paper (flagged because the task's checklist asks for them and later
sources cover them instead): `isErasable`/`is_erasable`/box, `EAst`, environment erasure,
the lambda-box target calculus and its weak-call-by-value *evaluation* semantics
(`EWcbvEval`), an erasure correctness/forward-simulation theorem, first-order/observational
equivalence statements, and any post-erasure pipeline/transformation. None of these notions
occur in this paper; the "extraction" of Sect. 4.4 targets a different, hand-verified,
narrow lambda-calculus fragment (Forster-Smolka's, with Scott encoding) rather than MetaCoq's
own erased calculus, and is not connected to a `EWcbvEval`-style semantics or a
forward-simulation theorem — its correctness is per-definition Ltac-automated instance proofs
of a logical relation, not a general soundness theorem.

## Position in the pipeline

- [kernel theory]: established, in full, for a documented subset of CIC (terms, typing,
  conversion/cumulativity/reduction, environments, universes) -> Sect. 2 (pp. 952-973), for
  Coq/Rocq.
- [kernel verification (type checker correctness)]: NOT established here — the paper
  explicitly states (p. 973, end of Sect. 2.7) that the `infer`/`check`/`check_conv`
  algorithms have no soundness/completeness proof yet; this is the predecessor stage to what
  `coq-coq-correct` later proves.
- [erasure theory]: not present in this paper (no `EAst`, no `isErasable`); Sect. 4.4's
  extraction is a different, narrower, hand-driven translation, not a general erasure theory.
- [erasure verification]: not present.
- [erasure implementation]: not present (Sect. 4.4's plugin is a worked example of translation
  to a different target, verified per-instance via Ltac, not a shipping erasure pipeline).
- [post-erasure pipeline]: not present.
- [extraction implementation]: partially — Sect. 5 describes running MetaCoq/Template-Coq
  meta-programs themselves after Coq's ordinary program extraction to OCaml (a
  meta-programming/tooling concern, not the erasure-to-lambda-box pipeline); Sect. 4.4
  separately gives a worked but restricted/non-general extraction-to-lambda-calculus example,
  for Coq.

## Relation to the other sources named in the task

- `metarocq-project` (this paper) is chronologically and technically the **predecessor
  foundation** of `metacoq-erasure-jacm`: it fixes the syntax/typing/reduction/environment/
  universe specification of the source calculus that erasure is later defined and proved
  correct against, but contains none of the erasure-specific machinery (`isErasable`, `EAst`,
  environment erasure, `EWcbvEval`, forward simulation) — `metacoq-erasure-jacm` is a
  **successor/superset** that adds an entirely new theory and target calculus on top of (a
  by-then-renamed/PCUIC-ified version of) this paper's kernel specification.
- Relative to `coq-coq-correct`: this paper is the **predecessor/unverified stage** — its
  Sect. 2.7 algorithms are exactly what `coq-coq-correct` is expected to prove sound/complete;
  `coq-coq-correct` is a **successor** adding the correctness proof this paper explicitly
  leaves open.
- Relative to `sozeau-habilitation`: likely a **subset** — a habilitation typically surveys
  and extends a body of work including this paper and its successors; expect
  `sozeau-habilitation` to be a superset covering this paper's content plus PCUIC, erasure,
  and further metatheory (not verified from this digest pass alone; check that source's own
  digest for confirmation).
- Relative to `letouzey-new-extraction`: **independent, different lineage** — Letouzey's
  extraction is Coq's classical (unverified, OCaml/Haskell-targeting, type-based) program
  extraction from the pre-MetaCoq era; this paper's Sect. 4.4 lambda-calculus extraction and
  Sect. 5 OCaml-extraction-of-plugins are both distinct efforts from Letouzey's, though Sect. 5
  literally uses Coq's Letouzey-style program extraction as a mechanism to run MetaCoq plugins
  natively. No erasure-to-lambda-box relation to Letouzey's work is drawn in this paper.
- Relative to `lean-extraction-report`: **independent** — different proof assistant (Lean)
  and, per this paper, no lambda-box target at all; only comparable at the "how do you erase a
  dependently-typed kernel to something executable" level of generality.
- Relative to `metarocq-docs`: expect `metarocq-docs` to be a **successor, evolving reference**
  documenting the current (post-rename MetaRocq, PCUIC-based) state of the toolchain that this
  2020 paper's `term`/`TemplateMonad`/Coq-8.9-era design historically preceded; naming
  (Coq -> Rocq, MetaCoq -> MetaRocq, CertiCoq -> CertiRocq) will differ, per this
  fan-out's `CLAUDE.md` terminology note.
- Relative to `carneiro-thesis`: likely **independent/orthogonal** unless that thesis is
  specifically about MetaCoq/Lean kernel verification; no direct textual relation is stated in
  this paper.

## Terminology map

- This paper's `term` (Fig. 1, "reification of Coq terms") vs. later PCUIC/`EAst` naming:
  this paper predates the PCUIC name entirely — the word "PCUIC" never occurs in this paper;
  its `term` type is the ancestor of what later work splits into a typed source language
  (PCUIC) and an untyped target language (`EAst`).
- `TemplateMonad` (Prop-valued, for use inside Coq) vs. `TM` (Type-valued, phase-split,
  extractable variant) — Sect. 5; both are meta-programming command monads, not to be
  confused with any evaluation/semantics monad in the erasure line of work.
- "Extraction" here (Sect. 4.4, Sect. 5) denotes two different things, neither of which is
  MetaCoq's later certified erasure: (a) Sect. 4.4's hand-restricted translation of an
  "admissible" polymorphic Coq fragment to Forster-Smolka's untyped weak-CBV lambda-calculus
  via Scott encoding, verified per-definition through a `computable` logical relation and Ltac
  automation; (b) Sect. 5's ordinary Coq-to-OCaml program extraction (Letouzey-style) applied
  to MetaCoq's own meta-programs, for performance. Neither is "erasure" in the
  `isErasable`/`EAst`/lambda-box sense used by CertiCoq and the sibling erasure paper — that
  vocabulary (`is_erasable`/`isErasable`, `box`/`tBox`, `EWcbvEval`, environment erasure) does
  not appear anywhere in this paper.
- `lterm` (Sect. 4.4's target de Bruijn syntax `n | s t | \s`) is Forster & Smolka's untyped
  weak-CBV lambda-calculus, a different calculus from lambda-box/`EAst`; do not conflate
  Scott-encoded inductives (used here) with lambda-box's native `tConstruct`/block-vs-applied
  constructor representation (used by CertiCoq/peregrine), which is not discussed in this
  paper at all.
- `is_constructor` (used in the `red_fix` guard, p. 966) is this paper's guarded-fixpoint-unfolding
  predicate at the *source* (Coq kernel) reduction level, not to be confused with any
  target-level (lambda-box) constructor-recognition predicate used in erasure semantics.
