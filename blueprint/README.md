# Blueprint

A [leanblueprint](https://github.com/PatrickMassot/leanblueprint) of the formal verification on
`dev/verify`: what is proved about the shipping eraser, what is assumed, and what is inherited
as trust. Twelve chapters, about 550 dependency-graph nodes citing about 1600 Lean declarations.

## Building

From the **repository root**, one-time setup:

```
python3 -m venv .venv
.venv/bin/pip install leanblueprint
```

Then build:

```
source .venv/bin/activate
leanblueprint pdf      # print/print.pdf (xelatex)
leanblueprint web      # web/index.html, web/dep_graph_document.html, lean_decls
leanblueprint serve    # serves web/ on localhost so the JS dep graph renders
lake env lean --run blueprint/CheckDecls.lean blueprint/lean_decls   # after `leanblueprint web`
python3 blueprint/scripts/audit.py               # after `lake build`; see "Audit" below
```

Activate the venv rather than calling `.venv/bin/leanblueprint` by path: `leanblueprint web`
shells out to a bare `plastex`, which only resolves when `.venv/bin` is on `PATH`.

The stock `leanblueprint checkdecls` (`lake exe checkdecls`) cannot be used in this repository:
it imports every root of every `lean_lib` in the workspace, and the `VerifyBench.Src.*` frozen
benchmark sources are not co-importable (`Sieve` and `Quicksort` both declare a root-level
`divmod`). `blueprint/CheckDecls.lean` is a drop-in replacement that only imports
`LeanToLambdaBox`; run it after `leanblueprint web` has written `blueprint/lean_decls` (see its
header comment for details).

Note that the web version's `\lean{}` links point at a doc-gen4 site (`\dochome` in
`blueprint/src/web.tex`) that is not built, so those links do not resolve.

## Outputs

- `print/` — PDF build artifacts (`print.pdf`, `.log`, `.synctex.gz`). Gitignored.
- `web/` — HTML build artifacts (`index.html`, per-chapter pages, `dep_graph_document.html`).
  Gitignored.
- `lean_decls` — flat list of every `\lean{...}` name cited, written by `web`. Gitignored.

## Chapter layout

`src/content.tex` `\input`s twelve files under `src/chapters/`, numbered `01-intro.tex`
through `12-trust.tex`, one per topic area of the verification (target language, source side,
erasure spec, correctness, lowering, the shipping eraser, its run model, the refinement, cold
start, the capstone, the trust boundary). Shared notation lives in `src/macros/common.tex`.

## Labels

Every node's label is `<kind>:<name>`, where `<kind>` is `def`/`lem`/`prop`/`thm`/`cor`/`asm`
matching its environment, and `<name>` is the principal Lean declaration's fully-qualified
name with the leading `LeanToLambdaBox.` stripped, `.` replaced by `-` and `'` by `-prime`.
This lets any chapter `\uses{}` a node from any other chapter without coordinating names in
advance. Many declarations are root-namespace names (`LBTerm`, `toKername`, `Erasure.erase`),
not `LeanToLambdaBox.*`; a Lean declaration is cited by exactly one node.

## `assumption` nodes and graph colors

`assumption` is a theorem-like environment (added to `macros/common.tex` and to the `thms=`
list in `web.tex`) for things the development assumes rather than proves: hypothesis-bundle
fields, standalone hypothesis binders, and the inherited lean4lean/axiom trust boundary.
Assumption nodes carry `\lean{}`+`\leanok` on the statement when a real Lean name states them,
but never a `proof` environment, so the dependency graph renders them stated-but-unproved.
In the graph, a node's **border** color reports its statement status (green = `\leanok`, blue
= ready to state, orange = `\notready`) and its **fill** color reports proof status (green =
proved, blue = ready to prove, dark green = proved and all ancestors proved) — an `assumption`
node is therefore never green-filled, since it has no proof.

A hypothesis bundle's definition node `\uses` its field assumptions, never the reverse: a
cycle in the `\uses` graph makes `leanblueprint web` die with a `RecursionError`. Result nodes
`\uses{asm:lean4lean-trust}` exactly when `#print axioms` reports `sorryAx` for one of their
declarations, and `\uses{asm:lean-reflection-axioms}` exactly when it reports an axiom beyond
`propext`, `Classical.choice`, `Quot.sound` and `sorryAx`.

## Audit

`python3 blueprint/scripts/audit.py` re-checks all of the above against the built library:
labels and their prefixes, dangling and cyclic `\uses`, the `\leanok` policy, single ownership
of declarations, existence of every cited declaration, and the two trust edges against
`#print axioms` measured on every cited name. It writes `blueprint/.audit/` (report, node
index, measured footprints; gitignored) and exits non-zero on any defect.

## Snapshot and status

The cited Lean declarations are those of `dev/verify` at `e7894de`. What was learned or changed after
that commit is recorded time-scoped (`At the snapshot` / `Since the snapshot` / `Planned`, with commit
hashes and the badges `[VACUOUS]`, `[REFUTED]`, `[FIXED]`, `[LANDED]`, `[PLANNED]`; see `STYLE.md`
section 8) without moving the snapshot: the graph and every `\lean{}` list are unchanged. Start from
the introduction's section "Status since the snapshot"; the trust chapter carries the detail.

## References and divergences

`references/digests/` holds a digest of each reference source and `references/digests/README.md` the
de-duplicated map (which source is canonical for which layer, the reworked two-prover diagram).
`blueprint/analysis/divergences-erasure.md` is the verified list of divergences between this
development and the MetaRocq erasure references (56 items, each with the reference element, our
declaration, kind, reason, consequence); `blueprint/analysis/divergences-kernel.md` is the three-way
kernel comparison (MetaRocq PCUIC, Carneiro's thesis, lean4lean). Chapter 13 of the blueprint
presents both.

## Writing style

`STYLE.md` is the binding style guide: every node is schematic (`\lead{In short}`, `\lead{Given}` /
`\lead{Then}` bullets, tables for rule lists, at most one `\hl{}` highlight, a status badge
`\stProved` / `\stChecked` / `\stAssumed` / `\stInherited` / `\stOpen` / `\stOutside` wherever a status
is asserted), every chapter opens with an "At a glance" block and closes with bulleted caveats. In print
`\lean{}` typesets the cited declarations under the node title. `python3 blueprint/scripts/skeleton.py
blueprint/src/chapters/<file> [git-ref]` checks that an edit left the graph skeleton (nodes, labels,
`\lean`, `\leanok`, `\uses`) unchanged against a reference commit. Tables must not use `\multirow`
(plasTeX has no shim for it); text-heavy columns take `p{<fraction>\linewidth}`.

`leanblueprint pdf` runs latexmk without `-interaction=nonstopmode`, so a LaTeX error makes it wait
forever on a prompt. To see the error, run from `blueprint/src`:
`latexmk -xelatex -interaction=nonstopmode -halt-on-error -output-directory=../print print.tex`.

## Issues found

`ISSUES-FOUND.md` lists what writing the blueprint turned up in the repository's code and
documents, observed at `dev/verify` `e7894de`: reported, not fixed, classified by kind and
severity, with a `verified` field saying whether a second pass confirmed the entry.
