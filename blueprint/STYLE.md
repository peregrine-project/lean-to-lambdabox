# Blueprint readability style (binding)

**Goal.** A reviewer grasps any node in 15 seconds and any chapter's shape in one minute. Write for
skimming: schematic, bulleted, with bold run-in labels, one highlight per node, tables for anything
enumerable. This guide governed the rewrite of the first prose draft (tag `bp-before-readability`) and
binds every later edit.

Apply Strunk's *Elements of Style*:
active voice, positive form, definite concrete language, **omit needless words**, one idea per sentence,
emphatic word last, parallel form for parallel ideas.

## 1. Invariants — never change these (a script checks them)

- Every node stays, in the same order: same environment (`definition`, `lemma`, `proposition`, `theorem`,
  `corollary`, `assumption`), same `\label{}`, same `\lean{...}` list, same `\leanok`, same `\uses{...}`
  lists — in the statement and in the proof. Copy these lines verbatim. Add no node, remove no node.
- A `proof` environment FOLLOWS `\end{theorem}` (never nested inside it). Definitions and assumptions have
  no proof.
- Keep every `\label{}` in the file (chapter, sections, nodes): other chapters reference them.
  Keep the `\chapter{...}` line as is.
- **Fidelity.** The old text is the reviewed, accurate reference. Add no fact. Drop no hypothesis and no
  conclusion of a statement. Keep every number that a bullet states. When you cut, cut commentary.
- ASCII only. Escape underscores inside `\code{}`/`\texttt{}` (`\code{erases\_correct}`). `\Box` only in
  math mode. A title containing a math macro needs `\texorpdfstring{math}{plain}`.
- Allowed LaTeX: `itemize`, `enumerate`, `description`, `tabular` with booktabs rules (`\toprule`,
  `\midrule`, `\bottomrule`), `remark`, `\emph`, `\textbf`, `\code{}`, `\ref`, math, and the macros of
  `blueprint/src/macros/common.tex` (read it). No new packages, no `\cite`, no tikz, no footnotes.

## 2. Macros for the schematic style (defined in macros/common.tex)

- `\lead{Label}` — bold run-in label. Fixed vocabulary: `In short`, `Given`, `Then`, `Where`, `Lean`,
  `Idea`, `Steps`, `Status`, `Caveat`, `Deviation`, `Why`, `Non-vacuity`, `Goal`, `Main results`,
  `Lean files`, `Paper`.
- `\hl{phrase}` — coloured bold highlight. **At most one per node**: the phrase a skimmer must not miss.
- Status badges — use one wherever a status is asserted:
  `\stProved` (proved in this repository), `\stChecked` (discharged by a checked term or kernel
  computation at a rung), `\stAssumed` (a hypothesis binder or bundle field), `\stInherited` (trust
  inherited from lean4lean's `sorry`s or Lean's reflection axioms), `\stOpen` (open proof obligation),
  `\stOutside` (outside the verified perimeter).

## 3. Node templates

### 3.1 Result (lemma / proposition / theorem / corollary)

```latex
\begin{theorem}[Short title, 2-6 words]
\label{thm:...}
\lean{...}
\leanok
\uses{...}
\lead{In short} One sentence, at most 25 words, plain words, with \hl{the key phrase}.
\begin{itemize}
\item \lead{Given} first hypothesis;
\item second hypothesis (one hypothesis per bullet; group trivial side conditions in one bullet);
\item \lead{Then} the conclusion (split into sub-bullets if it is a conjunction).
\end{itemize}
\lead{Lean} OPTIONAL: one clause on what the Lean statement carries beyond the bullets (flags,
closedness, universe scope). The print version already typesets the \lean{} names under the title and
the web version links them, so NEVER write a \lead{Lean} line that only restates the name.
\lead{Status} only on `theorem` nodes: \stProved{}; add ``\stInherited{} through lean4lean'' when the
proof \uses asm:lean4lean-trust; add ``conditional on \stAssumed{} <bundle or binder>'' when the OLD
text says the Lean statement takes an assumed bundle (EraserAsks, ErasureSpec, UpstreamAsks,
ErasureBridge) or a standing hypothesis binder -- whether or not that bundle is in the node's own \uses.
\end{theorem}
\begin{proof}
\leanok
\uses{...}
\lead{Idea} One sentence.
\lead{Steps} (optional) an `enumerate` of at most 5 short items, or one more sentence.
\end{proof}
```

Budget: statement at most 90 words (a top-level theorem at most 150); proof at most 60 words.
Small technical lemmas: `\lead{In short}` plus at most two bullets is enough; a one-line lemma needs no list.

### 3.2 Definition

```latex
\begin{definition}[Short title]
\label{def:...}
\lean{...}
\leanok
\uses{...}
\lead{In short} What it is and what it is for, one sentence.
\begin{itemize}            % or `description`; use a `tabular` when there are more than 6 rows
\item \code{ctor\_or\_field}: meaning in at most 15 words;
\item ...
\end{itemize}
\lead{Lean} OPTIONAL, same rule as for results: only information beyond the name (e.g. ``an inductive
with 11 constructors'', ``an \code{abbrev}'', ``a Boolean function'').
\end{definition}
```

Relations with many rules (WcbvEval, SEval, Erases, Lower, the twelve clauses of LBWfPeregrine, the
eighteen motives and steps): **one table**, columns e.g. `Rule | Source shape | Image or condition`.

### 3.3 Assumption (chapter 12)

```latex
\begin{assumption}[Short title]
\label{asm:...}  \lean{...} \leanok   % exactly as they are now (some have neither)
\uses{...}
\stAssumed{} \lead{In short} What is assumed, one sentence.
\begin{itemize}
\item \lead{Class} C (this repository's code) / D (specification of a Lean Meta/Core primitive) / upstream (lean4lean ask N);
\item \lead{Stands at} which rungs; \lead{Discharged at} which rungs and how (\stChecked{});
\item \lead{Would be discharged by} what, in one line.
\end{itemize}
\end{assumption}
```
Use `\stInherited{}` for the lean4lean and reflection-axiom nodes, `\stOpen{}` for the two ErasureBridge fields.

### 3.4 Remark

Keep a remark only if a reader needs it to understand the mathematics or to not be misled: a deviation
from the papers, a caveat limiting a claim, a non-vacuity guard. Start with `\lead{Deviation}`,
`\lead{Caveat}`, `\lead{Why}` or `\lead{Non-vacuity}`. At most 50 words; bullets if more than one point.

**Delete** remarks (and sentences) about: the history of the development (what was refuted, renamed,
deleted, re-measured); disagreements between doc comments or status files; design-tag archaeology;
measurement trivia; which module imports which. Those live in `blueprint/ISSUES-FOUND.md`.

## 4. Chapter frame

- **Opener.** Replace the overview paragraphs by an unnumbered block directly after the `\chapter`/`\label` lines:
  ```latex
  \section*{At a glance}
  \begin{itemize}
  \item \lead{Goal} one sentence.
  \item \lead{Main results} Theorem~\ref{...} (gist in 8 words); Theorem~\ref{...} (...).
  \item \lead{Status} \stProved{} ... ; \stAssumed{} ... ; \stInherited{} ... (what applies).
  \item \lead{Lean files} \code{A.lean}, \code{B.lean}.
  \item \lead{Paper} [S, Sec. 7.3] ... (only if the chapter has a counterpart).
  \end{itemize}
  ```
- **Sections.** Each opens with at most two sentences of orientation. No other free prose between nodes
  unless it carries a definition of notation.
- **Closer.** "Deviations and caveats" as at most 6 bullets of at most 30 words each (keep the existing
  `\section*` or paragraph heading and any label it has).

## 5. Words

- Sentences at most 25 words. No chains of `---` asides: at most one per paragraph, prefer none.
- Ban: "it should be noted", "in other words", "load-bearing", "none cosmetic", "exactly" as filler,
  "simply", "of course", "the point is", rhetorical contrasts ("not X but Y") when "Y" suffices.
- Design tags (`N8`, `A6`, `U3.1`, `W5` ...): replace by words. Keep only the repository's public names:
  `T5` (erasure correctness) and `T8` (the refinement), each introduced once per chapter, and the
  shipping findings `F-*` where a claim depends on them.
- File and line citations: drop line numbers inside nodes (they rot). File names belong in "At a glance".
  Exception: chapter 12's tables, where `file:line` is the content.
- Prefer a table or bullets to any sentence that enumerates three or more things.

## 6. Worked examples

### 6.1 A definition — before (155 words)

> `ErasesCorrectStmt` is the proposition: for every closed source term $e$ that translates to $ve$ and
> evaluates to $v$ under SEval at source flags $fl$, and every λ□ program $t$ obtained by erasing $e$ to
> $t_0$ and lowering $t_0$ at a specification environment Γspec that satisfies ErasesEnv at $t_0$ and whose
> pruning to the emitted Γ satisfies LowerEnv, granted the kernel environment is well formed and granted
> `UpstreamAsks env`, there are $v_0$ and $v'$ with Erases relating $v$ to $v_0$, Lower relating $v_0$ to
> $v'$, and WcbvEval taking $t$ to $v'$ at `eraseFlags`. Eight binders carry seven premises: MetaRocq's
> five (…), plus LowerEnv for the pass layer MetaRocq has no analogue of, plus `UpstreamAsks env`; the
> erasure and the lowering are two binders so that … The target flags are fixed at `eraseFlags`; the
> source flag record stays a parameter.

after (about 85 words):

```latex
\begin{definition}[T5: the erasure-correctness statement]
\label{def:ErasesCorrectStmt}
\lean{LeanToLambdaBox.ErasesCorrectStmt}
\leanok
\uses{def:Simulates, def:Erases, def:ErasesEnv, def:Lower, def:LowerEnv, def:SEval, def:WcbvEval,
def:eraseFlags, def:UpstreamAsks, def:SEvalFlags, def:lean4lean-grounding}
\lead{In short} The proposition that \hl{source evaluation is simulated by the erased, lowered program}.
\begin{itemize}
\item \lead{Given} a well-formed kernel environment and \code{UpstreamAsks\ env};
\item a closed source term $e$ that translates ($\TrExprS$) and evaluates, $\SEval\ e\ v$, at source flags $fl$;
\item an erasure $\Erases\ e\ t_0$ and a lowering $\Lower\ \Gamma_{spec}\ t_0\ t$;
\item $\ErasesEnv$ at $(\Gamma_{spec}, t_0)$, and $\LowerEnv\ \Gamma_{spec}\ \Gamma$ for the emitted $\Gamma$;
\item \lead{Then} there are $v_0, v'$ with $\Erases\ v\ v_0$, $\Lower\ \Gamma_{spec}\ v_0\ v'$ and
      $\WcbvEval\ \Gamma\ t\ v'$ at \code{eraseFlags}.
\end{itemize}
\lead{Lean} \code{ErasesCorrectStmt}, an \code{abbrev}; the source flags stay a parameter, the target flags are fixed.
\lead{Paper} [S]'s five premises plus $\LowerEnv$ and \code{UpstreamAsks}.
\end{definition}
```

### 6.2 A remark — delete

> Two module doc-comments and the project's own status notes disagree on how to count the premises
> (`Steps.lean`: "seven binders carrying six premises … plus the eighth"; `Close.lean`: "eight binders and
> seven premises"; `07-STATUS.md`: "eight premises"); all three resolve to the eight binders above.

This is documentation drift, recorded in ISSUES-FOUND.md. Delete it.

### 6.3 A remark — keep, tightened

before: "T5 as *published* is weaker than what its proof establishes: the inner induction proves
`Simulates`, whose fourth conjunct is ErasesEnv at $v_0$, and the aggregator discards that conjunct when
it exits, so a consumer wanting the environment relation at the value must re-derive it."

```latex
\begin{remark}
\lead{Caveat} T5 drops $\ErasesEnv$ at the value $v_0$, although its inner induction (\code{Simulates})
proves it. A consumer that needs it must re-derive it.
\end{remark}
```

### 6.4 A proof

```latex
\begin{proof}
\leanok
\uses{...unchanged...}
\lead{Idea} Induction on the source evaluation; each rule is one step interface.
\begin{enumerate}
\item $\beta$, $\zeta$: substitution commutes with $\Erases$ and $\Lower$.
\item $\iota$, projection, $\delta$: Theorems~\ref{thm:step_iota}, \ref{thm:step_proj}, \ref{thm:step_delta}.
\item Values: the erasure of a value is a value.
\end{enumerate}
\end{proof}
```

## 7. Procedure for a rewriter

1. Read this file, `elements-of-style.md`, `blueprint/src/macros/common.tex`, then the whole chapter.
2. Rewrite the chapter section by section, in place. Work node by node: copy the annotation lines
   verbatim, then rewrite the body from the old body only.
   Work efficiently: compose a whole section, then replace it with ONE edit (or write the new chapter
   as a few part files under a scratch directory and `cat` them over the chapter). Do not
   edit node by node: aim for fewer than 40 tool calls in total.
3. Run `python3 blueprint/scripts/skeleton.py blueprint/src/chapters/<file>` from the repository root
   until it prints `SKELETON OK`. It also reports the word ratio against the committed version: reach
   **at most 60%** (lemma-dense chapters 5, 9, 10 and chapters 1, 12: at most 65%). Symbolic bullets
   (`$\exists v'.\ \Erases\ v\ v' \wedge \WcbvEval\ t\ v'$`) are welcome where they are clearer
   than relational prose; never trade a hypothesis for the word budget.
4. Do not run lake, leanblueprint, latexmk or xelatex. Edit no other file.

## 8. Status updates (time-scoped facts)

The Lean declarations this blueprint cites are those of one snapshot commit of `dev/verify`. Facts learned
or changed later are recorded without pretending the snapshot moved:

- Every such statement is time-scoped with a run-in label: `\lead{At the snapshot}` (a fact about the
  snapshot commit itself, e.g. that a theorem is vacuous there), `\lead{Since the snapshot}` (landed on a
  named branch, with the commit hash), `\lead{In progress}` / `\lead{Planned}` (with the unit or document
  that specifies it). Never state a planned change as done, never state a landed change as part of the
  snapshot.
- Badges: `\stVacuous` (proved from hypotheses that cannot all hold), `\stRefuted` (a hypothesis or clause
  shown unsatisfiable or false), `\stFixed` (fixed after the snapshot on the branch named), `\stLanded`
  (landed on `dev/verify` after the snapshot), `\stPlanned` (specified, not yet done).
- No node is added for a declaration that does not exist at the snapshot, and no `\lean{}` list changes:
  later declarations are named in `\code{}` inside a remark or a status line.
- Every such fact cites its source: a commit hash, or a document of `doc/rework/` at the commit named.
