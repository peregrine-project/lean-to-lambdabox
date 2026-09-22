# A New Extraction for Coq -- Pierre Letouzey, TYPES 2002 (LNCS 2646, pp. 200-219; HAL deposit hal-00150914)

## Identity

Conference paper. Full citation as printed on the HAL cover page: Pierre Letouzey,
"A New Extraction for Coq", in Herman Geuvers and Freek Wiedijk (eds.), *Types
for Proofs and Programs: International Workshop, TYPES 2002*, Berg en Dal,
Netherlands, Springer LNCS, 2004 (workshop held Feb 2002; proceedings volume dated
2004; the HAL record lists p.617 for the volume). The PDF digested here (18 pages,
1 HAL cover page + 17 numbered content pages "1"-"17") is the author's self-archived
copy, submitted to HAL on 1 Jun 2007. No later journal version exists for this exact
paper; it is the original theoretical write-up of the extraction mechanism shipped in
Coq 7.3 (2002), and is the direct ancestor of the "is_arity/is_logical" pruning
machinery later re-formalized and verified inside MetaCoq/MetaRocq's certified erasure
(the `isErasable`/`Extract.v` line of work) and of the terminology "box" (written `O`
here, rendered as a dummy constant/symbol by the OCR of this scan) used throughout the
Peregrine project as **□**.

**Text-extraction note**: the archived PDF's fonts have no ToUnicode/cmap tables
(1990s/2000s TeX Type-1/Type-3 fonts), so `pdftotext` produces mojibake. This digest
is based on OCR (`pdftoppm` -> `tesseract`, 300 dpi, `--psm 6`) of the full 18-page
scan, cross-checked paragraph by paragraph. The paper's dummy/box constant (denoted
by a small square in the typeset PDF) OCRs as the letter/digit `O`/`0`; it is written
below as **□** for clarity and to match Peregrine's own notation.

## One-paragraph summary

Letouzey presents the theoretical foundations of the extraction mechanism rewritten
for Coq version 7 (replacing the pre-1999 extraction, which only handled a restricted
term subset). The paper (1) diagnoses two classes of problems with naive erasure of
`Prop`-sorted/type-scheme subterms of the Calculus of Inductive Constructions (CIC):
changes to evaluation order/strictness (interacting badly with `False_rec`-style
absurd-case exceptions) and target-language typability; (2) defines an untyped target
calculus CIC□ (CIC extended with one extra untyped constant, the "box" □, non-reducible
except by an ad-hoc rule □ applied to anything reduces to □) and an extraction function
`E` from well-typed CIC terms to CIC□ that replaces every `Prop`-sorted or type-scheme
subterm by □, homomorphically otherwise; (3) proves, first for a syntactically
restricted subsystem (Thm. 7) and then for full CIC with two extra reduction rules
needed for singleton-elimination and logical-guard fixpoints (Def. 8/9, Thm. 12/13/15),
that reduction of the extracted term simulates reduction of the source term up to
positions blocked by □, so that for closed terms of a "logic-free data-type" the
extracted term's normal form *is* (not just simulates) the source normal form; and (4)
describes the Coq 7.3 OCaml/Haskell implementation (dummy-argument removal, singleton
optimisation, `Obj.magic`/`unsafeCoerce` for target-language typing, benchmark suite).
This is the historical origin of the λ□ idea (untyped lambda calculus with an erased-proof
placeholder, later called `box`) that MetaCoq/MetaRocq formalizes and verifies as `EAst`
+ `isErasable`, and that Peregrine adopts as its middle-end IR.

## What it establishes

- A syntactic notion of erasable term ("type scheme" or `Prop`-sorted) closed under
  reduction and substitution in the relevant cases -> Definition 1 + Lemma 2
  (Stability Lemma), Sect. 3.1, p. 6.
- An extraction function `E : CIC -> CIC□` erasing exactly these subterms, defined by
  structural induction on typing derivations, plus its extension to contexts (constant
  bodies, axioms, inductive declarations) -> Definition 3, Sect. 3.2, p. 6-7.
- A restricted correctness theorem for terms/typing avoiding empty/singleton logical
  elimination and logical fixpoint guards, under *strong* (under-binder) reduction ->
  Theorem 7, Sect. 3.3, p. 8.
- Identification of exactly two typing situations that break the naive picture even
  outside strong reduction: singleton-inductive `Cases` elimination producing an
  informative result, and fixpoints whose decreasing ("guard") argument has a logical
  inductive type -> Sect. 3.3 case enumeration (1/2/3a/3b), p. 7-8.
- Two new reduction rules patching exactly these two situations (a special
  iota-reduction for annotated singleton `Cases_n`, and a relaxed fixpoint iota-reduction
  triggered by □ as well as by a constructor) plus a full *weak* (head-only) reduction
  relation `->w` on CIC□, matching what OCaml/Haskell can execute -> Definition 8
  (new iota-reduction), Definition 9 (weak reductions), Sect. 3.4, p. 9-10.
- A cross-calculus simulation invariant `(Gamma,t) <| (Gamma0,t0)` relating a CIC□ term/context to
  the CIC term/context it erases from, used to carry reduction back and forth ->
  Definition 10, p. 11.
- The two simulation directions: erasure-then-reduce-in-CIC□ can be matched by
  reduction in CIC (Theorem 12, forward), and reduction in CIC can be matched by
  reduction (or a □-reduction) in CIC□ (Theorem 13, backward) -> p. 11, proofs in
  Appendix A (p. 16) and Appendix B (p. 17-18).
- The headline correctness result: for a closed, well-typed CIC term of a *logic-free
  data-type* (Definitions 6 and 14), every weak-reduction derivation of `E(t)` in
  CIC□ terminates on exactly the CIC normal form of `t` (no residual □, i.e. the
  extracted computation reproduces the source value, not merely simulates it) ->
  Theorem 15, p. 11, proof in Appendix C (p. 18).
- A description of the gap between this idealized theory and the shipped Coq 7.3
  extractor: singleton-elimination optimisation done eagerly (even under binders) is
  justified informally as safe because all *other* reductions stay weak; the dummy
  constant □ is implemented as an error value in Haskell and as
  `let rec box x = Obj.magic box` (using the then-undocumented `Obj.magic` escape hatch)
  in OCaml because OCaml's type system cannot type □ directly; fixpoints are
  eta-expanded to the right arity; unused ("dummy") logical arguments are dropped from
  function signatures (keeping at least one argument to avoid `False_rec` misfires) and
  call sites are patched to match -> Sect. 4, p. 12-13.
- Explicit statement of what is *not* proved: point 2 of the four-point Coq-6-vs-Coq-7
  comparison in the Conclusion, i.e. that the extracted program actually type-checks in
  OCaml/Haskell, is left as ongoing work, not a theorem -> Sect. 5, p. 14-15.

## Section 2 in more detail: the two challenge classes (informal motivation for the theory)

Because Sect. 2 is where the paper first names the hazards that Sect. 3's theorems
exist to close, it is worth unpacking on its own:

- **Evaluation-order hazard** (Sect. 2.1, p. 3-4): given `f : (x:A)(P x) -> B`, the
  Coq terms `(f t)` and `(f t p)` reduce differently (`(f t)` is stuck without the
  proof argument `p`), but a naive extraction dropping all logical arguments would
  send both to the same term `(E(f) E(t))`. Left unfixed, this silently changes
  strictness. The paper's fix, worked out fully only in the implementation
  (Sect. 4, "Removing Dummy Arguments"), is to keep at least one dummy abstraction
  per function so `False_rec`-based absurd branches stay behind a lambda and are
  never forced by a partial application such as `(f 0)`.
- **`False_rec` interaction** (Sect. 2.1, p. 3-4): `False_rec : (P:Set)False -> P`
  compiles to a runtime exception; because Coq's typing allows a term to be well-typed
  even though one of its arguments can never actually be supplied a real proof (e.g.
  `(f 0)` when `f : (n:nat)(n<>0) -> nat`), extraction must not let this dead branch's
  exception "leak" into positions that are actually reachable. This is precisely what
  the dummy-abstraction discipline and Theorem 15's "reduces to the *same* value, not
  an exception" guarantee jointly rule out.
- **`Type`-sorted "hybrid" terms** (Sect. 2.1, p. 4): because `Type` contains both
  `Set` and `Prop`, a term like `if b then nat else True` is well-typed at sort `Type`
  but is informative or logical depending on a run-time boolean `b` -- the pre-1999
  extractor simply rejected any use of sort `Type`. Definition 3's "type scheme or
  `Prop`-sorted" test is precisely general enough to erase such terms to `□` (they are
  type schemes) without needing a syntactic `Type`-avoidance restriction; this is the
  concrete reason the erasability test is stated as a semantic/typing condition rather
  than a sort-based syntactic filter.
- **Target-language typability** (Sect. 2.2, p. 4-5): OCaml and Haskell are simply
  typed (no dependent types, no universes, different polymorphism from Coq's), so a
  direct translation of well-typed CIC terms need not produce well-typed ML/Haskell
  terms; a prior encoding by Loic Pottier [12] still produced ill-typed terms. The
  paper's chosen workaround -- `Obj.magic` in OCaml, `unsafeCoerce` in Haskell -- is
  explicitly *not* accompanied by a proof that the escape hatch is used soundly; this
  is the same gap restated as open point 2 in the Conclusion (Sect. 5).
- **Why not an untyped target like Scheme** (Sect. 2.2, p. 5): considered and rejected
  because mainstream Scheme lacks first-class inductive types (would need encoding)
  and early speed tests favoured Haskell/OCaml; this is the paper's only discussion of
  an *untyped* target calculus for the final output, as opposed to the *untyped
  intermediate* CIC□ used internally for the correctness proof -- CIC□ itself is never
  proposed as an executable target language, only as a proof device, which is a point
  of contrast with Peregrine/MetaCoq/MetaRocq's λ□, which *is* used as an actual
  executable/compiled intermediate representation.

## Structure

| Section | Pages | What it covers | Relevance (lean-to-lambdabox / lean4lean) |
|---|---|---|---|
| Abstract + Sect. 1 Introduction | 1 | Motivation (Curry-Howard, dead-code elimination via `Set`/`Prop`), why an external typed target language (OCaml/Haskell) is used instead of internal beta-reduction or Grégoire's compiled reduction | Low -- historical motivation only |
| Sect. 2 Challenges (2.1 logical-part elimination, 2.2 translation problems) | 3-4 | Evaluation-order/strictness hazard from dropping logical arguments (`False_rec`), the "hybrid" `Type`-sorted terms (`if b then nat else True`), why a real ML-like typed target needs `Obj.magic`/`unsafeCoerce` | Medium -- the `False_rec`/dummy-abstraction discussion is the informal ancestor of `isErasable`'s treatment of `tCase`/`tProj` on `Prop` and of why untyped λ□ needs a dedicated non-reducing box rather than plain elimination |
| Sect. 3.1 The Calculus of Inductive Constructions | 5-6 | CIC term syntax (products, lambda, let, app, `Cases`, `Fix`), typing judgment, the five base reductions (beta, delta, zeta, iota for `Cases`, iota for `Fix`), Definition 1 (type scheme), Lemma 2 (Stability Lemma: subject reduction + substitution stability for `Prop`-sorted/inductive-typed/type-scheme terms) | Medium -- the source calculus is exactly what MetaRocq's Rocq frontend erases from; the Stability Lemma is the informal precursor of MetaRocq's typing/erasability preservation lemmas |
| Sect. 3.2 The Extraction Function | 6-7 | Definition of CIC□ (CIC + non-typed dummy constant □); Definition 3, the extraction function `E` (case `(box)`: erase `Prop`/type-scheme subterms; homomorphic elsewhere: `id`, `lam`, `let`, `app`, `cases`, `Fix`); extension of `E` to contexts (`def`, `ax`, `ind`) | **High** -- this is the direct informal ancestor of MetaRocq's `erase`/`isErasable` and of the "environment erasure" (`erase_global_decls`) that every frontend (Rocq, Lean-to-lambdabox, agda2lambox) must reproduce or match against |
| Sect. 3.3 Strong Reduction in a Restriction of CIC□ | 7-8 | The three failure cases (beta-redex-under-□, `Cases`-on-□ from empty/singleton elimination, `Fix`-redex-blocked-by-□ from logical-guard fixpoints); ad-hoc □-reduction (Def. 5); restricted Theorem 7 (strong reduction, syntactically restricted CIC') | High -- states precisely why plain structural erasure is *not* semantics-preserving in general, motivating the extra reduction machinery lean-to-lambdabox's Lean-side box/lazy-force passes must also handle (cf. Peregrine's `extra_unsafe_transforms`, still `Admitted` in places) |
| Sect. 3.4 Weak Reductions in the Complete CIC□ | 9-11 | Singleton-elimination annotation `Cases_n`; new iota-reduction (Def. 8); definition of weak reductions `->w` (beta/delta/zeta/iota, head-only, Def. 9); no-axiom restriction; simulation invariant `<|` (Def. 10); Lemma 11 (`E` produces a `<|`-related pair); **Theorem 12** (forward simulation), **Theorem 13** (backward simulation); Definition 14 (data-type); **Theorem 15** (full correctness for logic-free data-types) | **Highest** -- this is the paper's core correctness argument and the literal starting point for MetaCoq/MetaRocq's `erasure_correctness` and for what a Lean-to-lambdabox forward-simulation proof (dev/verify) is reproving formally, using a WcbvEval-style weak/head reduction exactly analogous to `->w` here |
| Sect. 4 Implementation Considerations | 12-14 | Removing singleton eliminations eagerly (even under lambdas) as an implementation optimisation justified informally; implementing □ (Haskell error vs. OCaml `Obj.magic`); implementing fixpoints (eta-expansion to declared arity; why OCaml/Haskell CBV/lazy guard evaluation matches the theoretical guard condition); removing dummy arguments (with call-site compensation); code optimisations (`sig`/`exist` erasure, inlining recursors, `Cases e of true true end -> true`); pointer to the Coq 7.3 source (`contrib/extraction`, ~3000 lines OCaml) and worked `pred` example; benchmark suite (Higman's Lemma, CIC type-checker, unification, tautology checkers, ~6000 lines) | Medium -- documents exactly which optimisation passes are *unverified engineering* (dummy-argument removal, singleton-`sig` erasure, `Obj.magic` insertion) as opposed to the proved core `E`; directly analogous to Peregrine's own unverified glue layer and to what should *not* be assumed correct without separate argument |
| Sect. 5 Conclusion | 14-15 | Four-condition comparison Coq 6 vs Coq 7 extraction; explicit admission that OCaml/Haskell type-checking of the extracted term (point 2) is *not* proved, only points 1 (accepts any term) and 3 (no spurious exceptions) are now guaranteed | High -- an early, explicit statement of a trust-boundary gap (target-language typability) of exactly the kind Peregrine's "Verification landscape" section tracks per pass/backend |
| References | 15-16 | 14 items: Berardi/Boerio (pruning), Peyton Jones et al. (Haskell 98), Gregoire-Leroy (compiled strong reduction), Hayashi-Nakano (PX), Jackson (Nuprl), Kelsey et al. (Scheme), Leroy et al. (OCaml 3.04), Monniaux, Paulin-Mohring x2 (1989 POPL paper and 1989 thesis -- the *original* Coq extraction), Pottier (2001, `Obj.magic` encoding), Severi-Szasz, Coq 7.3 Reference Manual | Low |
| Appendix A: Proof of Theorem 12 | 16 | Case analysis on the reduction step: singleton `Cases_n`-reduction, logical-guard fixpoint reduction, beta-reduction (uses Lemma 16: `<|` is a congruence for substitution), remaining cases (delta/zeta/iota) analogous | Medium -- template for how a forward-simulation proof over an erasure relation is structured; Lemma 16's substitution-congruence argument is the direct analogue of substitution lemmas needed in any mechanized erasure-correctness proof |
| Appendix B: Proof of Theorem 13 | 17-18 | Case analysis by position of the CIC redex relative to a □ in the CIC□ counterpart: matching redex, redex swallowed by □, or one of the four intermediate cases 1/2/3a/3b from Sect. 3.3, each closed by a corresponding □-reduction or new iota-reduction | Medium -- backward-simulation half; the "swallowed by □" case is exactly the erasure-relation clause every mechanized erasure correctness proof (MetaRocq's, and Lean-to-lambdabox's target) needs for terms that go to `tBox` |
| Appendix C: Proof of Theorem 15 | 18 | Combines Thm. 12/13 with well-foundedness of CIC reduction (`->r` is finite) and strict decrease of □-reductions in size, to conclude the weak-reduction derivation of `E(t)` terminates exactly on the CIC normal form | Medium -- shows the termination argument needed on top of simulation to get *equality* of normal forms, not just a simulation relation; relevant to any claim that a translated/erased program's evaluation result literally equals the source's |

## Key definitions and results (reference of record)

| id as printed | name | one-line statement | page |
|---|---|---|---|
| Def. 1 | type scheme | A well-typed term is a type scheme if it has some type of the form `(a1:X1)...(an:Xn)s` for a sort `s` (i.e. becomes a type when fully applied) | 6 |
| Lemma 2 | Stability Lemma | Subject reduction (type/sort of `t` preserved by reduction of `t`); substitution preserves `Prop`-sortedness, inductive-typedness, and type-scheme-ness of a term; applying a `Prop`-sorted or type-scheme term preserves that property | 6 |
| -- (unnamed, Sect. 3.2 opening) | CIC□ | CIC extended with one extra untyped constant `□` ("box" -- OCR'd as `O`); reductions of CIC□ are exactly those of CIC, with `□` non-reducible (until Def. 5) | 6 |
| Def. 3 | extraction function `E` | Structural-on-typing-derivation function: `E_Gamma(t) = □` if `t` is `Prop`-sorted or a type scheme in `Gamma`; otherwise homomorphic on `id`/`lam`/`let`/`app`/`Cases`/`Fix`; extended to contexts via `nil`/`def`/`ax`/`ind` clauses | 6-7 |
| -- (Sect. 3.3, case list) | three CIC-redex / CIC□-non-redex mismatches | (1) beta-redex `([x:X]t u)` vs. non-redex `(□ u')`; (2) `Cases`-iota-redex vs. non-redex `Cases □ of ... end` (from empty/singleton logical elimination); (3) `Fix`-iota-redex vs. non-redex, either the whole redex collapsed to `□` (3a) or only the guard argument collapsed to `□` (3b, logical-guard fixpoint) | 7-8 |
| Def. 5 | □-reduction | `(□ u) ->_box □` -- applying `□` to anything reduces to `□` (the literal "`box x -> box`" rule from Peregrine's terminology) | 8 |
| Def. 6 | logic-free (type) | A type `T` is logic-free if for every closed normal term `t : T`, `E(t) = t` (extraction is the identity, no residual `□`) | 8 |
| Thm. 7 | restricted correctness | For a closed, well-typed term `t` of logic-free type `T` in the syntactically restricted systems CIC'/CIC'□ (forbidding empty/singleton informative elimination and logical fixpoint guards), all reductions of `E(t)` terminate on the CIC normal form of `t` -- proved for *strong* reduction, proof omitted (said to resemble Thm. 15's) | 8 |
| Def. 8 | new iota-reduction | Two extra clauses added to iota: `Cases_n □ of f end -> (f □ ... □)` (n copies, for a singleton elimination annotated `Cases_n`); fixpoint iota-reduction fires when the guard argument equals `□` *or* begins with a constructor | 9-10 |
| Def. 9 | weak reductions | `->w_beta`, `->w_zeta`, `->w_delta`, `->w_box` defined from the same base cases as strong beta/zeta/delta/box but with head-only (non-congruent-into-subterms) compatibility rules; full weak reduction `->w` is the union of all weak base relations | 10 |
| Def. 10 | the `<\|` (erasure/simulation) invariant | `(Gamma,t) <\| (Gamma0,t0)` iff: (<|1) `t0` well-typed in `Gamma0`; (<|2) `t`,`t0` (and `Gamma`,`Gamma0`) differ only at positions where `t`/`Gamma` has `□`; (<|3) every subterm of `t0`/`Gamma0` corresponding to a `□` is `Prop`-sorted or a type scheme; (<|4) every `Cases`/`Cases_n` in `t`/`Gamma` eliminates an inductive type that is informative, or a logical singleton, or empty | 11 |
| Lemma 11 | `E` respects `<\|` | If `t` is well-typed in `Gamma`, then `(E(Gamma), E_Gamma(t)) <\| (Gamma, t)` | 11 |
| Thm. 12 | forward simulation | If `(Gamma,t) <\| (Gamma0,t0)` and `t ->w u`, then there exists `u0` with `t0 ->r u0` (some, possibly zero, CIC reduction) and `(Gamma,u) <\| (Gamma0,u0)` | 11 (proof: App. A, p. 16) |
| Thm. 13 | backward simulation | If `(Gamma,t) <\| (Gamma0,t0)` and `t0 ->r u0`, then there exists `u` with `(Gamma,u) <\| (Gamma0,u0)` and either `t ->w u` or `t ->_box u` | 11 (proof: App. B, p. 17-18) |
| Def. 14 | data-type | An inductive type `D` whose constructors expect only arguments of type `D` or of another data-type (recursively) | 11 |
| Thm. 15 | full correctness (main theorem) | For a closed, well-typed CIC term `t` of a logic-free data-type `T`, every `->w`-derivation of `E(t)` terminates on the CIC normal form of `t` (extraction's evaluation result literally *is* the source value, e.g. `true`/`false` for `bool`) | 11 (proof: App. C, p. 18) |
| Lemma 16 (in App. A) | `<\|` is a substitution congruence | If `a <\| a0` and `b <\| b0` then `a{x/b} <\| a0{x/b0}` | 16 |
| -- (Sect. 4, "Implementing □") | implementation of `□` | Haskell: `□` compiled to a runtime error (safe because after singleton-elimination optimisation `□` never reaches head position); OCaml: `let rec box x = Obj.magic box` (needs `Obj.magic` since `□`'s pseudo-type is inconsistent) -- i.e. the **trust boundary**: type-safety of the OCaml output is not proved, only asserted as future work (Sect. 5) | 13, 14-15 |
| -- (Sect. 4, "Removing Dummy Arguments") | dummy-argument elision | Post-extraction optimisation: drop `□`-typed arguments from a constant's declared lambdas (keeping >=1 to preserve the `False_rec`-exception-avoidance property from Sect. 2.1), with call-site compensation `(f a p) -> (f E(a))`, `(f a) -> fun _ -> (f E(a))` | 12-13 |

## Notable worked examples (quoted, for citation)

The paper illustrates each theoretical hazard with a concrete term; these are useful
as ready-made test cases when checking a mechanized erasure against the informal one.

- **Example 4** (Sect. 3.3, p. 8) -- a lambda that only becomes `Prop`-sorted *after*
  reduction, illustrating case 1 (the need for the `□`-reduction, Def. 5):
  `t = ([X:Type][f:nat->X][g:X->nat](g (f □)) Prop [_:nat]True)` erases to
  `E(t) = ([X:□][f:□][g:□]g (f □)) □ □) [g:□]g (f □)` (the OCR of this line is
  degraded but the point, stated in prose immediately after, is that a beta-redex
  `([x:X]t u)` in the source can correspond to a *non*-redex `(□ u')` in CIC□ once
  `X` has been instantiated, forcing the ad-hoc box rule `(□ u) ->_box □`).
- **`cast` function** (Sect. 3.4, "Singleton Elimination", p. 9) -- shows why eager
  singleton-`Cases` reduction is unsound *under binders* (motivating the restriction
  to weak reduction): `cast = [H:nat==bool][n:nat]<[t:Set]t>Cases H of n end`; then
  inside `[H:nat==bool]<...>Cases (cast H □) of ... end`, reducing `(cast H □)` to
  `□` eagerly would produce a `□` where a boolean constructor is expected by the
  surrounding `Cases`, a type error avoided only because strong (under-lambda)
  reduction is forbidden.
- **`loop` function** (Sect. 3.4, "Fixpoints with Logical Guards", p. 9-10) -- a
  fixpoint over an accessibility proof (`Acc nat gt`) whose "guard" argument is
  logical; naively dropping the guard condition on this fixpoint's reduction (as a
  naive erasure might, since the guard is erased to `□`) makes the erased term loop
  even unapplied: `E(loop) = [Az:□] Fix F {F/2:□ := [a:nat][b:□](F (S a) □)} □ Az`,
  which without the new fixpoint iota-reduction (Def. 8, firing when the guard is
  `□` *or* a constructor) would strong-reduce forever.
- **`pred` worked example** (Sect. 4, p. 13-14) -- a dependently pre/post-conditioned
  predecessor function `pred : (n:nat)~0=n -> {p:nat|n=(S p)}` defined by tactics,
  whose printed CIC term uses `False_rec` in the `O` branch and `exist`/`refl_equal`
  in the `S n0` branch; the Coq 7.3 `Extraction pred.` output is
  `let pred = function | 0 -> assert false (* absurd case *) | S n0 -> n0`, i.e. the
  logical argument of type `~0=n`, the `False_rec` (turned into an `assert false`
  exception marker), and the `exist` wrapper (recognised as the identity on its sole
  informative argument, cf. Sect. 4 "Code Optimizations") have all vanished.

## Position in the pipeline

- **[kernel theory]**: yes, partially -- Sect. 3.1 restates (without proof, citing the Coq Reference Manual Chap. 4) the CIC term syntax, typing judgment, and the five base reductions (beta/delta/zeta/iota-Cases/iota-Fix), plus the Stability Lemma (Lemma 2) needed for the erasure argument.
- **[kernel verification (type checker correctness)]**: no -- the paper assumes CIC typing/reduction metatheory as given (citing the Reference Manual), proves nothing about the type-checker implementation itself.
- **[erasure theory]**: yes, this is the paper's core contribution -- Sect. 3.2 (Definition 3, the extraction function `E`) and Sect. 3.3-3.4 (the box/`□`-reduction machinery, the `<|` simulation invariant, Theorems 7/12/13/15).
- **[erasure verification]**: yes, but pen-and-paper only, for Coq/CIC -- Theorems 12, 13, 15 with proofs in Appendices A, B, C; not mechanized in Coq/Rocq itself (this predates MetaCoq).
- **[erasure implementation]**: yes -- Sect. 4 describes the actual Coq 7.3 implementation (`contrib/extraction`, ~3000 lines OCaml, ~900 for the theoretical core / ~700 for optimisations) shipped and used in a benchmark suite (Sect. 4, "A Benchmark Suite").
- **[post-erasure pipeline]**: yes, informally -- Sect. 4's dummy-argument removal, singleton (`sig`/`exist`) elimination, small `Cases` simplifications, and fixpoint eta-expansion are exactly the kind of post-erasure cleanup transforms that Peregrine's middle-end (and MetaRocq's optimisation passes) perform, though none of these specific optimisations are proved correct here (justified only informally, "we can prove that type error possibilities ... are avoided").
- **[extraction implementation]**: yes -- OCaml and Haskell code generation, including the `Obj.magic`/`unsafeCoerce` trust boundary for target-language typability (Sect. 2.2, Sect. 4).

## Relation to the other sources named in the task

- **metarocq-project / metacoq-erasure-jacm** (successor, formalized+verified superset): MetaCoq/MetaRocq's certified erasure directly descends from this paper's `E` function and correctness argument. Where Letouzey erases to an ad-hoc CIC□ with a single unverified □-reduction rule and proves Theorems 12/13/15 on paper for the Coq 7.3 kernel informally cited, MetaCoq/MetaRocq (i) mechanizes the source calculus (PCUIC) and target calculus (`EAst`, with `tBox`) inside Coq itself, (ii) replaces the "type scheme or `Prop`-sorted" erasability test with a mechanically decided/verified `isErasable` predicate, and (iii) proves erasure correctness as a Coq theorem with an extracted, executable erasure function, not just a hand-checked simulation. Nothing in Letouzey's paper is dropped in the sense of being contradicted; the singleton/logical-guard-fixpoint case split (Sect. 3.3-3.4) reappears in MetaCoq's erasure as the handling of `tCase`/`tProj`/`tFix` on erasable types.
- **coq-coq-correct** (independent, complementary layer): that work verifies the Coq *kernel*/type-checker itself; Letouzey's paper assumes kernel correctness as a black box (citing the Reference Manual) and works one layer up, on erasure. No direct dependency either way, but coq-coq-correct would be the natural discharge of the "reader will find a complete description of CIC in the Reference Manual" citation in Sect. 3.1.
- **sozeau-habilitation**: superset/successor -- surveys and extends the MetaCoq programme including the certified-erasure line that formalizes exactly this paper's ideas; likely cites Letouzey 2002 as the origin of the extraction-correctness question.
- **lean-extraction-report**: sibling/independent frontend design document for a *different* source language (Lean) targeting the same downstream idea (erase to an untyped λ-calculus with a box placeholder); where Letouzey's box-reduction rule and singleton/guard case analysis are specific to CIC's `Cases`/`Fix`/inductive typing, the Lean-side report must re-derive analogous erasability and simulation arguments for `Lean.Expr`'s different typing/reduction rules (no shared kernel).
- **metarocq-docs**: subset/practical companion -- documents the *use* of the mechanized descendant of `E` (MetaRocq's erasure pass) rather than proving anything; Letouzey's paper is the theory this documents an implementation of, several eraser-config decisions (block vs. applied constructors, etc.) are not addressed at all in this 2002 paper.
- **carneiro-thesis**: independent -- if concerned with a different proof assistant's kernel/metatheory (e.g. Lean/Mathlib foundations rather than CIC extraction), there is no direct technical dependency; relevant only as background on kernel trust more generally.

## What is explicitly left open / trust boundary (Sect. 5, p. 14-15)

The Conclusion states the comparison as four numbered conditions that had to hold
under the *old* (pre-7.0) Coq extraction for a computation via extracted code to be
trustworthy, then reports which are discharged by this paper's work:

1. The term must avoid sort `Type` and strong elimination, else the old extractor
   rejects it -- **obsolete** under the new extraction (any well-typed CIC term is
   now accepted, by Definition 3 handling `Type` via the type-scheme test rather
   than outright rejection).
2. The extracted term must be accepted by the OCaml or Haskell type-checker -- **still
   open**; the paper states this is "currently working on", not proved, and is
   patched in practice only by `Obj.magic`/`unsafeCoerce` insertion (Sect. 2.2, Sect. 4).
   This is the paper's own named trust boundary.
3. Execution must not raise a spurious exception from `False_rec`/absurd cases --
   **obsolete**, guaranteed by Theorem 15 combined with the dummy-abstraction
   discipline of Sect. 2.1 (an argument of `False`/absurd type is never actually
   forced because it can never reduce to a constructor in a well-typed derivation).
4. Execution must terminate without exhausting stack/memory -- **unaffected**,
   resource behaviour is not addressed by extraction correctness at all and remains
   the programmer's/algorithm's responsibility.

So the paper's own summary is: extraction is now proved semantics-preserving
(conditions 1 and 3), but *target-language well-typedness* (condition 2) is
acknowledged as an unverified, ongoing engineering concern -- the same shape of gap
Peregrine's own "Verification landscape" tracks for each backend (e.g. Rust/Elm
*printing* being unverified even though the underlying typed erasure is verified).

## Terminology map

| This paper's term | Other sources' term |
|---|---|
| `□` (the dummy/box constant, OCR'd as `O`) | `tBox` (MetaCoq/MetaRocq `EAst`); "box" (Peregrine's λ□); "erased placeholder" |
| CIC□ | untyped target calculus of erasure -- ancestor of λ□ / MetaCoq's `EAst` (untyped) |
| CIC (with restriction CIC') | PCUIC (MetaCoq/MetaRocq's mechanized presentation of CIC) |
| "type scheme or `Prop`-sorted" (the erasability test of Def. 3) | `isErasable` / `is_erasable` (MetaCoq/MetaRocq); "is_box" in some informal writing |
| extraction function `E` | `erase` (MetaCoq/MetaRocq); "erasure function" generically |
| `<\|` (Definition 10) | the erasure relation `Erases` (MetaCoq/MetaRocq: `Ee.erases`/`erases_context` relating a PCUIC term/env to its `EAst` erasure) |
| weak reduction `->w` (Definition 9) | weak call-by-value evaluation, `EWcbvEval` (MetaCoq/MetaRocq); WcbvEval (Peregrine/lean-to-lambdabox's unified target semantics) |
| logic-free data-type (Definitions 6, 14) | closed, "propositionally clean" / erasure-transparent type -- no single standard name downstream; related to but not identical to MetaRocq's per-type erasability well-formedness side conditions |
| □-reduction (Definition 5) | the rule "`box x -> box`" cited verbatim in Peregrine's own terminology (CLAUDE.md) |
| singleton elimination / `Cases_n` annotation | "singleton inductive" optimisation (`sig`/`exist` erasure survives into modern Coq/Rocq extraction and into ConCert's typed extraction, Peregrine's λ□ᵀ) |
| dummy-argument removal (Sect. 4) | arity/eta trimming, related to (but not identical to) Peregrine's constructor block-vs-applied-form distinction and to inlining/remapping `.attr` hints |
| `Obj.magic` / Haskell `unsafeCoerce` (Sect. 2.2, Sect. 4) | the OCaml/Haskell-backend trust boundary; analogous in spirit to Peregrine's CakeML-glue `Axiom trust_coq_kernel` and to the untyped-vs-typed λ□/λ□ᵀ split motivating Rust/Elm's *typed* extraction |
