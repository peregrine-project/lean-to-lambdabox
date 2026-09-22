# Reference digests -- de-duplication, layer map, and citation policy

Eight digests live here, and they overlap heavily: four of them ([MR], [CCC],
[JACM], [HAB]) are successive write-ups of ONE Rocq-side research programme,
and [L] is its pen-and-paper ancestor. This README says which to cite for
what, gives the corrected layer grid, and corrects the owner's reading.
All eight digest files are KEPT; superseded ones are marked below and remain
the right place to look for the things in their "keep for" column.

## 1. De-duplication: supersession chains and canonical references

### 1a. The Rocq programme, in chronological order

    [L]    Letouzey, TYPES 2002      pen-and-paper erasure theory + Coq 7.3 impl.
      | mechanized by
    [MR]   Sozeau et al., JAR 2020   Template-Coq: reification + typing SPEC only.
      | PCUIC introduced; checker and erasure verified
    [CCC]  Sozeau et al., POPL 2020  first mechanized checker + erasure; erasure
      |                              correctness still rests on conjectures.
      | journal extension: + completeness, two-step certification,
      |                    cumulative inductives, conjecture-free erasure
    [JACM] Sozeau et al., J.ACM 2025 the theorem reference of record.
      | HDR synthesis: + 13-phase pipeline, + Malfunction backend (PLDI'24)
    [HAB]  Sozeau, HDR Nantes 2026   MetaRocq v1.4 / Rocq 9.0 naming.

    [MRD]  metarocq.github.io        the live code, ahead of every paper; never
                                     superseded; no theorem or page numbers.

Key relation facts, stated exactly:
- [JACM] p. 8:5 "Prior publication" names the POPL 2020 paper as the conference
  version it extends. So [CCC] is EARLIER than [JACM], not later.
- [HAB] front matter lists [JACM] FIRST among the four articles it "is based
  on", alongside the PLDI'24 OCaml-extraction paper and [MR].
- [MR] Sect. 2.7, p. 973 states that its `infer`/`check`/`check_conv` have NO
  soundness or completeness proof; [MR] is the pre-verification stage.
- The word "PCUIC" never occurs in [MR]; PCUIC is introduced in [CCC] Sec 2.

### 1b. Status of each digest

| digest key | status | superseded by | keep for |
|---|---|---|---|
| `letouzey-new-extraction` | HISTORICAL ORIGIN | theorems re-proved by [JACM]/[HAB] | origin of box and of the erasure relation; the unverified post-erasure optimisations (Sect. 4, pp. 12-14); the four-point trust list (Sect. 5, pp. 14-15) |
| `metarocq-project` | SUPERSEDED for kernel theory | [CCC] Sec 2, then [JACM] Sec 3-4, then [HAB] Ch.2 | Template-Coq quoting / `TemplateMonad` / the phase-split `TM` monad (Sect. 3, 5, pp. 973-977, 994-997); the historical Scott-encoding experiment (Sect. 4.4, pp. 991-994), which is NOT the lambda-box line |
| `coq-coq-correct` | SUPERSEDED | [JACM] on every shared topic | the original framing (TCB -> TTB, Sec 1); `eterm`/`Is_Type_or_Proof`/`Informative` naming; the confluence-by-triangle proof (Thm 2.2, p. 8:13) |
| `metacoq-erasure-jacm` | CANONICAL (theory) | partially by [HAB] for the pipeline | all numbered erasure theorem statements |
| `sozeau-habilitation` | CANONICAL (pipeline, current naming) | -- | the 13-phase pipeline, flag-parametrized eval, Malfunction |
| `metarocq-docs` | CANONICAL (code map) | -- | file/module names; passes postdating the papers |
| `lean-extraction-report` | CANONICAL (Lean impl., unverified) | -- | the only description of a shipping Lean eraser |
| `carneiro-thesis` | CANONICAL (Lean kernel theory) | -- | the only Lean source-calculus metatheory |

### 1c. Canonical reference per layer

| layer | canonical | fallback / also cite |
|---|---|---|
| kernel theory (Rocq) | [JACM] Sec 3-4 | [HAB] Ch.2, pp. 26-42 (current naming) |
| kernel verification (Rocq) | [JACM] Sec 6, pp. 8:56-8:59 | [HAB] Ch.5, pp. 73-84; [MRD] safechecker README |
| lambda-box syntax + semantics | [HAB] Spec 20-21, pp. 92-94 | [JACM] Fig. 16, p. 8:60; [MRD] `EAst.v`, `EWcbvEval.v` |
| erasure theory (isErasable, `erases`) | [JACM] Sec 7.2-7.3, pp. 8:61-8:62 | [HAB] Spec 22-23, pp. 95-96; [L] Def. 3, Def. 10 |
| erasure verification | [JACM] `erase_correct_firstorder` / `erases_correct`, pp. 8:62-8:64 | [HAB] pp. 97-99; [L] Thm 12/13/15, p. 11 |
| erasure implementation (Rocq) | [MRD] `ErasureFunction.v` | [JACM] Sec 7.2, Fig. 17, p. 8:61 |
| post-erasure pipeline | [HAB] Sec 6.5-6.6, pp. 99-104 | [MRD] `ETransform.v`, `Erasure.v`; [JACM] Sec 7.4 (one pass only) |
| backends / extraction | [HAB] Ch.7, pp. 107-125 | [R] Sec 3.3, pp. 8-9 (consumer's view) |
| Lean kernel theory | [CT] `axioms.tex`, `typesys.tex`, `unique.tex` | -- |
| Lean erasure implementation | [R] Sec 4, pp. 10-15 | -- |

## 2. The grid

Rows = provers, columns = layers. Bare tags are digest keys; see Sect. 5.

              C1 kernel      C2 kernel      C3 erasure     C4 erasure     C5 erasure     C6 post-erasure
                 theory         verif.         theory         verif.         implem.        pipeline+backends
            +--------------+--------------+--------------+--------------+--------------+------------------+
            | PCUIC        | MetaRocq     | lambda-box,  | erases_      | MetaRocq     | 13 Transform.t   |
    R       | declarative  | SafeChecker  | isErasable,  | correct,     | Erasure-     | phases, then     |
    O       | specificat.  | (sound AND   | `erases`,    | erase_corr_  | Function.v,  | Malfunction / C  |
    C       |              |  complete)   | EWcbvEval    | firstorder   | plugin,      | / Wasm / CakeML  |
    Q       |              |              |              |              | Peregrine    | / Rust / Elm     |
            +--------------+--------------+--------------+--------------+--------------+------------------+
            | MR CCC JACM  | CCC JACM HAB | L CCC JACM   | L CCC JACM   | CCC JACM     | JACM HAB MRD     |
            | HAB MRD      | MRD (NOT MR) | HAB MRD      | HAB MRD      | HAB MRD      | L R              |
            +--------------+--------------+--------------+--------------+--------------+------------------+
            | Lean DTT:    | lean4lean    | Lean-side    | THIS PROJECT | `#erase` in  | ==== SHARED ==== |
    L       | typing,      | verified     | Erases rel.  | (dev/verify) | LeanTo-      | nothing here is  |
    E       | def. eq.,    | checker      | + visitExpr  |              | LambdaBox    | Lean-specific;   |
    A       | unique typ.  |              | bridge       |              |              | same cell as the |
    N       |              |              |              |              |              | Rocq row         |
            +--------------+--------------+--------------+--------------+--------------+------------------+
            | CT           | (none here;  | CT only, and | NO SOURCE    | R            | R, as a consumer |
            |              |  CT bounds   | thin/negativ.| (this is the |              | (+ one lbox      |
            |              |  it only)    | + JACM/HAB   |  work);      |              |  unboxing patch) |
            |              |              |   as model   | [R] 6.3 only |              |                  |
            +--------------+--------------+--------------+--------------+--------------+------------------+

Two things the grid makes visible that the owner's diagram does not:
- C3's target half (lambda-box and its WcbvEval) is NOT duplicated per prover.
  It is one shared artifact owned by MetaRocq; the Lean side re-implements it
  and must stay faithful to [HAB] Spec 20-21, not redefine it.
- C6 is entirely shared and already done. No Lean-specific backend work is
  needed; the Lean frontend only has to land in lambda-box satisfying the
  pipeline's entry preconditions (well-formedness, eta-expansion/block form).

### Same grid, as a table with full source references

| | C1 kernel theory | C2 kernel verification | C3 erasure theory | C4 erasure verification | C5 erasure implementation | C6 post-erasure pipeline / backends |
|---|---|---|---|---|---|---|
| **Rocq** -- artifact | PCUIC declarative spec | MetaRocq SafeChecker | lambda-box + `isErasable` + `erases` + EWcbvEval | `erases_correct`, `erase_correct_firstorder` | `ErasureFunction.v`, erasure plugin, `Peregrine Extract` | 13 `Transform.t` phases; Malfunction, C, Wasm, CakeML, Rust, Elm |
| **Rocq** -- sources | [MR] Sect. 2, pp. 952-973 (pre-PCUIC `term`); [CCC] Sec 2, pp. 8:3-8:14; [JACM] Sec 3-4, pp. 8:9-8:35; [HAB] Ch.2, pp. 26-42; [MRD] `pcuic/theories/README.md` | [CCC] Sec 3, pp. 8:14-8:21 (sound only); [JACM] Sec 6, pp. 8:56-8:59 (sound + complete; found a real Coq 8.14 bug); [HAB] Ch.3-5, pp. 44-84; [MRD] `safechecker/theories/README.md`. NOT [MR]: Sect. 2.7, p. 973 says no proof | [L] Sect. 3.2-3.4, pp. 6-11 (Def. 3, Def. 5, Def. 8-10); [CCC] Sec 4.1-4.3, pp. 8:21-8:24 (Fig. 11-13); [JACM] Sec 7.1-7.3, pp. 8:60-8:62 (Fig. 16-18); [HAB] Sec 6.1-6.3, pp. 92-96 (Spec 20-23); [MRD] `EAst.v`, `EWcbvEval.v`, `Extract.v` | [L] Thm 12, 13, 15, p. 11 (pen-and-paper); [CCC] Thm 4.7, p. 8:24, Lem 4.8 + Cor 4.8.1-2, pp. 8:24-8:25 (conjecture-dependent); [JACM] Sec 7.3-7.4, pp. 8:62-8:64 (conjecture-free); [HAB] pp. 97-99; [MRD] `ErasureCorrectness.v` | [CCC] Sec 4.2, Fig. 12, pp. 8:22-8:23; [JACM] Sec 7.2, Fig. 17, p. 8:61 + retyping Sec 6.4, p. 8:59; [HAB] Spec 22, p. 95; [MRD] `ErasureFunction.v`, `Loader.v`, `Extraction.v` | [JACM] Sec 7.4, p. 8:63 (`optimize` only); [HAB] Sec 6.5-6.6, pp. 99-104 (Spec 24-25) and Ch.7, pp. 107-125; [MRD] `ETransform.v`, `Erasure.v`, `EConstructorsAsBlocks.v` etc.; [L] Sect. 4, pp. 12-14 (unverified ancestors); [R] Sec 3.3, pp. 8-9 |
| **Lean** -- artifact | Lean's DTT: typing, def. eq., unique typing | lean4lean verified checker | Lean-side `Erases` relation + `visitExpr` bridge | THIS PROJECT (`dev/verify`) | `#erase` in LeanToLambdaBox | same as Rocq row |
| **Lean** -- sources | [CT] `axioms.tex`, `typesys.tex` (`thm:reg`, `thm:weak`, `thm:subst`), `unique.tex` (`thm:unique`, `thm:church_rosser`, `thm:ckappa`), `Wtypes.tex`, `soundness.tex` (`thm:sound2`) | none in this set. [CT] `typesys.tex` only bounds it negatively: definitional equality is undecidable, algorithmic equality is not transitive, subject reduction fails for the algorithmic typing judgment | [CT] `soundness.tex` Sect. "Proof splitting" (`sort`/`lvl`) and `compilation.tex` (25 lines, `*`/`obj`, no theorem, no target semantics). The model to mirror is [JACM] Sec 7.3 / [HAB] Spec 23 | NO SOURCE. [R] Sec 6.3, pp. 19-20 names it as future work; [HAB] Sec 8.2.3, p. 130 calls Lean's compilation unverified | [R] Sec 4, pp. 10-15 (`EraseM`, eta-expansion, `.fix`, preprocessing); Listing 2, p. 9 (`LBTerm`); `#erase ... to ...`, p. 11; Sec 4.2, pp. 12-13 (`@[extern]`, Zarith) | [R] Sec 3.3, pp. 8-9 (reuse); Sec 4.4, pp. 14-15 (the one `lbox` unboxing patch) |

### Every source, positioned in one line
- **[MR]** (JAR 2020): Rocq C1 + an off-grid quoting/plugin layer; explicitly
  NOT C2 (Sect. 2.7, p. 973); nothing at C3-C6.
- **[CCC]** (POPL 2020): first to fill Rocq C1-C5 at once; superseded by [JACM].
- **[JACM]** (J.ACM 2025): Rocq C1-C5 conjecture-free; C6 via `optimize` only.
- **[HAB]** (HDR 2026): Rocq C1-C6, the only source filling C6 in full.
- **[L]** (TYPES 2002): Rocq C3-C6, pen-and-paper / unverified; ancestor of C3
  and C4; assumes C1-C2.
- **[MRD]** (live site): Rocq C1-C6 as a file index, no theorem numbers; the
  tiebreaker when paper and code disagree.
- **[R]** (Dima, MPRI 2025): Lean C5 only, plus C6 as a consumer; empty C1-C4.
- **[CT]** (Carneiro, MSc draft): Lean C1 in full, C2 only negatively, C3 as a
  25-line unfinished sketch; empty at C4-C6.

## 3. Corrections to the owner's reading

The reading being corrected: 1R = [MR] as the Rocq kernel-verification theory;
1L = lean4lean + [CT] as its Lean equivalent; 2 = [CCC] as the erasure layer on
top of 1R; 3 = [R] as the unverified shipping Lean eraser; "our work = port 2 to
Lean, on top of 1L, to verify 3".

Right, and worth keeping: the four-box shape (kernel layer under erasure layer,
Rocq column mirrored by a Lean column), the placement of [R] as unverified
implementation, and the direction of the work.

Wrong or imprecise:

1. **[MR] is an overview paper, not the kernel-verification paper.** It
   specifies Coq's typing/reduction/environments (Sect. 2, pp. 952-973), then
   says at p. 973 that its `infer`/`check`/`check_conv` have no soundness or
   completeness proof. Kernel VERIFICATION is [CCC] Sec 3 (sound) and [JACM]
   Sec 6 (sound and complete); "1R" splits into C1 and C2.

2. **[CCC] is EARLIER than [JACM], and it is not only about erasure.**
   [CCC] = POPL 2020, PACMPL 4, Article 8, 28 pp; [JACM] = J.ACM 72(1),
   Article 8, 74 pp, Jan 2025, whose p. 8:5 "Prior publication" note names
   [CCC] as its conference version. [CCC] covers kernel verification (Sec 3)
   AND erasure (Sec 4). Cite [JACM]: it adds completeness, the two-step
   certification, cumulative inductive types, and -- decisively -- discharges
   the conjectures [CCC]'s erasure correctness rested on.

3. **"2 on top of 1R" overstates the dependency.** [CCC] reuses Template-Coq's
   reification and environment infrastructure, but PCUIC itself is introduced
   in [CCC] Sec 2; the string "PCUIC" does not occur in [MR]. The kernel theory
   [CCC]'s erasure is stated against is [CCC]'s own, not [MR]'s.

4. **The habilitation is missing from the reading and subsumes most of it.**
   [HAB] (HDR, Nantes 2026, HAL tel-05544162, 152 pp) is a superset of [MR],
   [CCC], [JACM] and the PLDI'24 OCaml paper, and the only source documenting
   the 13-phase pipeline (Spec 24-25, pp. 99-104) and the verified Malfunction
   backend (Ch.7, pp. 107-125). It anticipates this project: p. 104 notes
   lambda-box "can also be used as a target for other proof assistants like
   Agda, Idris or Lean"; Sect. 8.2.3, p. 130 calls Lean's C backend unverified.

5. **[L] is missing and is the actual origin of the method being ported.**
   The relation-extends-the-function technique, the box reduction
   `box u -> box` (Def. 5, p. 8), the singleton-elimination and
   logical-guard-fixpoint cases (Def. 8, pp. 9-10) and the forward/backward
   simulation (Thm 12/13, p. 11) are Letouzey's; [JACM] and [HAB] mechanize
   them, they did not invent them.

6. **"lean4lean and Carneiro's thesis" are not one layer, and neither is a
   kernel-verification result of the kind [JACM] Sec 6 is.** [CT] is a
   pen-and-paper MSc draft about the IDEAL judgments, two of whose chapters
   end in the literal token `UNFINISHED`. Its most load-bearing content here
   is negative: `typesys.tex` proves definitional equality undecidable,
   algorithmic equality non-transitive, and subject reduction FALSE for the
   algorithmic judgment the real kernel implements -- so "the Lean kernel
   accepted this" is weaker than "this is definitionally well-typed".
   lean4lean is the mechanization, is not digested here, and carries its own
   `sorry` boundary.

7. **[R] is not a specification either, not just "no verification".** It has no
   typing judgment, no erasure relation, no `isErasable` analogue, no target
   semantics and no theorem (Sec 6.2, pp. 18-19). It is an MPRI internship
   report (Simon Dima, advised by Forster, 2025-10-01) describing
   `inria-cambium/lean-to-lambdabox`, an ancestor or sibling of the current
   repo (footnote 16, p. 15) -- a design precedent and hard-case checklist,
   not the current code.

## 4. The claim "port 2 to Lean to verify 3, on top of 1L"

**What is right.** The target statement: a forward simulation in the shape of
[JACM] `erases_correct` (p. 8:64) with its first-order specialization
`erase_correct_firstorder` (pp. 8:62-8:63), obtained from a non-deterministic
`Erases` relation that extends the shipping function and is closed under wcbv
evaluation. The two-step structure -- relation first, then connect the
function's graph to it ([JACM] `erases_erase`, p. 8:62) -- is the structure to
copy, and is why the `visitExpr`-to-`Erases` bridge is load-bearing.

**Four refinements.**

1. **lambda-box is not ported; it is shared.** C3's target half is fixed by
   MetaRocq. The Lean-side re-formalization of the syntax and of `EWcbvEval`
   must be faithful to [HAB] Spec 20-21, pp. 92-94 -- the three amendments
   (box absorbs application, subsingleton iota, unguarded fix) and the
   `WcbvFlags` choices, notably `with_constructor_as_block`. Divergence here
   is a bug, not a design choice.

2. **1L is an ASSUMPTION, not a thing to port.** [JACM]'s erasure proof is
   stated against PCUIC's declarative typing and consumes specific metatheory:
   subject reduction, principality strengthened to unique sort quality
   ([JACM] Sec 7.2, p. 8:61), canonicity, and weak-CBV standardization
   ([JACM] Sec 5.6, pp. 8:46-8:48 -- the one place strong normalization is
   used). Not all Lean analogues exist: unique typing is [CT] `thm:unique`, but
   nothing Lean-side has the status of wcbv standardization, canonicity or
   principality, and lean4lean's typing judgment has its own unproven parts.
   The Lean kernel layer thus enters as a trust boundary with named holes, not
   a ported chapter. [CT] `soundness.tex` Sect. "Proof splitting" adds a limit
   the Rocq side lacks: its `sort`/`lvl` machinery is scoped to a FIXED
   universe valuation -- the universe-polymorphic regime this project has
   already hit on the environment side.

3. **MetaRocq's post-erasure pipeline is a gift and a contract.** [HAB]
   Sec 6.5-6.6 and Ch.7 verify everything from lambda-box onward, so nothing
   downstream is redone for Lean; in exchange the Lean eraser must land in
   lambda-box satisfying the pipeline's entry preconditions
   (`EWellformed`/`EProgram`, eta-expansion of constructors and fixpoints, the
   block-vs-applied convention). Caveats: `peregrine-tool` does not ship only
   the verified MetaRocq phases (its `extra_unsafe_transforms` group has
   `Admitted` obligations), and [L] Sect. 4, pp. 12-14 is the reminder that
   these optimisations were historically the unverified part.

4. **Verifying "3" is not the same as verifying "a" Lean eraser.** [R] is not
   the current code, and the shipping eraser's Lean-specific layers -- machine
   `Nat`, `csimp`, `@[extern]`/axioms, matcher and `macro_inline`
   preprocessing, constructor pruning -- have no counterpart in [JACM]'s
   theorem. [R] footnote 13, p. 12 says `@[extern]` is "a source of unsoundness
   if the external implementation does not match the logical definition". Each
   such layer is separately discharged or carried as a named assumption; none
   is covered by porting [JACM] Sec 7.

**Corrected one-liner.** We are reconstructing [JACM] Sec 7.3-7.4 / [HAB] Ch.6
for Lean: a Lean-side `Erases` relation into the SHARED MetaRocq lambda-box, a
forward simulation for it, and a bridge from the shipping `#erase` -- resting
on lean4lean plus [CT] as an explicitly bounded assumption rather than a ported
layer, and inheriting, not rebuilding, everything downstream of lambda-box.

## 5. How to cite in the blueprints

| digest key | tag | canonical for |
|---|---|---|
| `metarocq-project` | `[MR]` | Template-Coq quoting/`TemplateMonad`; the historical statement that the early checker was unverified (Sect. 2.7, p. 973). Do NOT cite for kernel verification. |
| `coq-coq-correct` | `[CCC]` | historical firsts only: first mechanized verified PCUIC checker, first mechanized erasure correctness (Thm 4.7, p. 8:24). Superseded by `[JACM]`. |
| `metacoq-erasure-jacm` | `[JACM]` | all erasure theorem statements: `isErasable`, the `erases` relation, `erase_correct_firstorder`, `erases_correct`, `erases_deps`; sound+complete checker. THE default citation. |
| `sozeau-habilitation` | `[HAB]` | lambda-box syntax/semantics as currently shipped (Spec 20-21); the 13-phase pipeline (Spec 24-25); Malfunction extraction (Ch.7); current MetaRocq v1.4 naming. |
| `letouzey-new-extraction` | `[L]` | provenance of the method: box reduction, the relation-over-function technique, the singleton/logical-guard cases, and the named trust boundary (Sect. 5). |
| `lean-extraction-report` | `[R]` | the shipping Lean eraser's design and its hard cases; the Lean-specific unsoundness risks (`@[extern]`, pruning/unboxing); benchmark lineage. |
| `metarocq-docs` | `[MRD]` | file and module names in MetaRocq; passes that postdate the papers; the tiebreaker when paper and code disagree. |
| `carneiro-thesis` | `[CT]` | Lean's source-calculus metatheory: typing, def. eq., unique typing (`thm:unique`), and the limits of the algorithmic judgment (`typesys.tex`). Do NOT cite `compilation.tex` as an erasure specification. |
