# Blueprint style (binding)

**Goal.** A reader grasps any node in 15 seconds and any chapter's shape in one minute. Write
schematically: bullets with bold run-in labels, one highlight per node, tables for anything
enumerable. Apply Strunk's rules: active voice, positive form, definite concrete language, omit
needless words, one idea per sentence, parallel form for parallel ideas.

## 1. Present state only

The blueprint describes the commit it is built from. It is not a changelog.

- State what is. Never write "previously", "since the last version", "was fixed", "no longer",
  "used to", "now", "yet", or describe a state and then its changes. Git holds the history.
- What is not done is an open item in the present tense (`\stOpen{}`, or a row of the chapter
  "What is open"), never a plan with dates.
- A planned node (marked `\planned`) states a declaration of the owner-approved design (the
  planned statements and definitions) under the name the declaration will have; it is written in
  the present tense as a statement ("`X` is ..."), and the badge says that it is not formalized.
  Every other node documents a declaration that exists. When the declaration lands, the node drops
  `\planned` and gains `\leanok` (as the audit computes it) and `\srcloc`.
- The registers are rendered as they are (their entries record changes, with a before and an
  after); the prose around them follows this section.

## 2. Nodes

- Environments: `definition` (def, abbrev, structure, inductive, class, instance), `theorem`
  (headline results), `lemma` (everything else, and families: one node for parallel
  declarations), `proposition`, `corollary`; `imported` (a lean4lean module) only in
  `generated/lean4lean-imports.tex`, which the audit writes. A `remark` is prose, not a node.
- Kinds follow from the environment and the Lean names (README, "Node kinds and dependency
  graphs"): a `theorem` of the proof library is a milestone, so the final theorem must depend on
  it; never choose an environment for its colour.
- Shape, in this order: `\begin{env}[Title]`, `\label`, `\lean{...}`, `\leanok` or `\planned`,
  `\uses{...}`, `\srcloc{path}{line}` (not on a planned node), `\inherited{...}` (when the audit
  measures inherited trust), the body, `\end{env}`; for a result, a sibling `\begin{proof}`
  `\uses{...}` `\leanok` ... `\end{proof}` after it, never inside it (a planned node's proof has
  no `\leanok`).
- `\label`: `<prefix>:<principal Lean name>`, prefix `def`, `lem`, `prop`, `thm`, `cor` (`imp` for
  an imported node, with its module), the name with `.` replaced by `-` (`def:Erasure-erase`).
  Unique; never renamed.
- `\lean{...}`: names of the compiled environment only, or, on a planned node, the names of the
  approved design; never invent one. Each name belongs to one node. Every declaration of the
  verification library (`proof/EraseProof`) is cited by a node that is not planned: a helper goes
  into the `\lean` list of the node it serves.
- `\planned`: the node's declarations do not exist (the audit checks it); a node that is not
  planned never uses a planned node.
- `\leanok`: exactly as the audit computes it (README, section Audit). Never add it by hand to make
  a node look formalized.
- `\uses{...}`: labels only. In the statement, what the statement mentions; in the proof, what the
  proof relies on. The `\uses` of the final theorem and of the milestones make the step lemmas:
  the audit checks that they name only nodes the Lean declarations use directly, and every result
  they use directly.
- `\inherited{...}`: the labels (`L1`, ..., `TrProj`; `audit.toml`, rendered in the trust chapter)
  of the lean4lean sorry sources that the audit measures for the node.

### Result template

```latex
\begin{theorem}[Short title, 2-6 words]
  \label{thm:...}
  \lean{...}
  \leanok
  \uses{...}
  \srcloc{path}{line}
  \lead{In short} One sentence, at most 25 words, with \hl{the key phrase}.
  \begin{itemize}
  \item \lead{Given} one hypothesis per bullet, with the reason it is there;
  \item \lead{Then} the conclusion.
  \end{itemize}
  \lead{Reference} the paper section and the MetaRocq file:identifier it follows.
\end{theorem}
\begin{proof}
  \uses{...}
  \leanok
  \lead{Idea} One sentence. \lead{Steps} at most 4 items.
\end{proof}
```

Budget: statement at most 90 words (the final theorem at most 150); proof at most 40.

### Definition template

```latex
\begin{definition}[Short title]
  \label{def:...}
  \lean{...}
  \leanok
  \uses{...}
  \srcloc{path}{line}
  \lead{In short} What it is and what it is for, one sentence.
  \begin{itemize}
  \item \code{field\_or\_ctor}: meaning in at most 15 words;
  \end{itemize}
\end{definition}
```

A relation with many rules is one table (`Rule | Premises | Conclusion`). A node body carries no
status word (`\stShipping`, `\stProved`, ...): the badges after its heading give its kind and
status (checked).

## 3. Chapters

- Opener, after `\chapter{...}\label{chap:...}`: `\section*{At a glance}` with bullets `\lead{Goal}`,
  `\lead{Main results}`, `\lead{Status}`, `\lead{Nodes} \bpnodes{chap:...}` (its own label; only in
  a chapter with nodes), `\lead{Lean files}`, and `\lead{Reference}` when the chapter has a
  counterpart in the references.
- Sections open with at most two sentences of orientation; no other prose between nodes unless it
  fixes notation.
- Closer, in a chapter with nodes: `\section*{Caveats}`, at most 6 bullets of at most 30 words:
  only facts that limit what the chapter's nodes mean.
- Files under `src/generated/` are written by scripts: never edit them; change the source (the
  register, the Lean code) and regenerate.

## 4. Macros (`src/macros/common.tex`)

| Macro | Use |
|---|---|
| `\lead{Label}` | bold run-in label, a noun phrase of one to three words; in nodes: In short, Given, Then, Where, Lean, Idea, Steps, Caveat, Why, Reference |
| `\hl{phrase}` | the one phrase of a node a skimmer must not miss |
| `\code{...}` | inline code; escape `_` as `\_` |
| `\stProved`, `\stInherited`, `\stShipping`, `\stPlanned`, `\stOpen` | status words of the prose (not of node bodies): proved; trust inherited from lean4lean; shipping code, described, not verified; not formalized; not done |
| `\planned` | marks a planned node and prints its badge (checked: its declarations do not exist) |
| `\srcloc{path}{line}` | where the node's first declaration is (checked; the web version links it) |
| `\leandecl{name}` | a declaration by its full name, written as it is (no escapes, like `\lean`); the web version links it to its source (checked) |
| `\leanfile{path}`, `\leanfiles{dir/}{A, B}` | a `.lean` file (a path ending with `/`: a directory), or several files of one directory, printed `dir/{A, B}.lean`; escape `_`; linked (checked) |
| `\leanloc{path}{lines}`, `\leanlinesof{path}{lines}` | lines of a file (`26`, `7-13`, `642,723`), printed `path:lines` or `:lines`; linked (checked) |
| `\inherited{labels}` | the lean4lean sorries the node depends on, by label (checked) |
| `\bpkind{key}` | the badge of a node kind (`final`, `milestone`, `step`, `lemma`, `definition`, `shipping`, `test`, `leanfourlean`, `leanfourleansorry`; README, "Node kinds and dependency graphs") |
| `\bpnodes{chap:...}` | the nodes of a chapter by kind, in its opener (generated counts; checked) |
| `\usedbystatements`, `\usedbyproofs` | in an imported node (generated only): the nodes whose declarations use its declarations directly |

Allowed LaTeX: `itemize`, `enumerate`, `tabular` with booktabs rules and `p{...}` columns (no
`\multirow`, no `longtable`: plasTeX renders neither), `\emph`, `\textbf`, `\ref`, math, and the
macros above. No new package, no `\cite`, no footnote, no macro defined in a chapter. ASCII only;
a title with math needs `\texorpdfstring{math}{text}`.

## 5. Words

- Sentences at most 25 words; at most one dash aside per paragraph.
- Ban: "it should be noted", "in other words", "simply", "of course", "clearly", evaluative
  adjectives, and rhetorical contrasts ("not X but Y") when "Y" suffices.
- Line numbers live only in `\srcloc{}` and in generated tables.
- Cite the Lean sources with the citation macros of section 4, never with `\code`: a declaration
  named in full with `\leandecl`, a `.lean` file with `\leanfile` or `\leanfiles`, from the root of
  its repository (`proof/...`, `LeanToLambdaBox/...`, `Lean4Lean/...`). The audit rejects a `\code`
  that holds a `.lean` path or a full declaration name. A name relative to its namespace stays
  `\code`.
- Prefer a table or bullets to a sentence that enumerates three or more things.
