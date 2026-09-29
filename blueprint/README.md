# Blueprint

A [leanblueprint](https://github.com/PatrickMassot/leanblueprint) of the verification of the
`#erase` eraser of `lean-to-lambdabox`. It is a picture of the commit it is built from: the scope,
the trust boundary, the definitions and theorems with their status (proved, or planned: stated
under the name the declaration will have), the two registers (`doc/SHIPPING-CHANGES.md`,
`doc/DIVERGENCES.md`) and what is open. It describes the present state only; the history is in
git. The Lean code it documents is the shipping code (`LeanToLambdaBox/`) and the proof package
(`proof/`, library `EraseProof`).

## Layout

```
audit.toml              configuration of the audit (builds, imports, allowed axioms, labelled
                        lean4lean sorries, coverage prefix, roots file)
build.sh                builds the web and pdf versions
CheckDecls.lean         Lean side of the audit (existence, axioms, sorry sources, censuses,
                        the declarations of the proof package)
requirements.txt        the Python packages of the build (leanblueprint, plasTeX), pinned
scripts/audit.py        the audit
scripts/render_registers.py   renders the registers and the pins as chapters
scripts/unlink_lean_decls.py  removes the documentation links of the \lean names (web version)
STYLE.md                how chapters and nodes are written (binding)
src/content.tex         chapter order
src/chapters/*.tex      hand-written chapters: intro, scope, trust, model, pure, source,
                        relation, simulation, oracle, core, final, tests, open
src/generated/*.tex     generated chapters and tables (never edit them)
src/macros/             common.tex (shared macros), web.tex, print.tex
src/web.tex, print.tex  drivers of the web and print versions
```

## Build

One-time setup: a Python 3.14 venv with the packages of `requirements.txt` (leanblueprint, plasTeX;
the `pygraphviz` wheel bundles Graphviz), and for the pdf `latexmk` and `xelatex`.

```
python3 -m venv <venv> && <venv>/bin/pip install -r blueprint/requirements.txt
export PATH="<venv>/bin:$PATH"
blueprint/build.sh          # or: blueprint/build.sh web | blueprint/build.sh pdf
```

`build.sh` first runs `scripts/render_registers.py`, then `plastex` (web version in
`blueprint/web/`, and the list of cited declarations in `blueprint/lean_decls`) followed by
`scripts/unlink_lean_decls.py`, then `latexmk` (`blueprint/print/print.pdf`). With the default
target `all`, it then copies the pdf to `blueprint/web/blueprint.pdf`, which the title page of the
web version links to; `blueprint/web/` is then the whole site. `leanblueprint web` and
`leanblueprint pdf` run plasTeX and latexmk only: they neither render the registers nor remove the
documentation links. `leanblueprint serve` serves `blueprint/web/` so that the dependency graph
renders. The latexmk configuration runs xelatex with `-interaction=nonstopmode -halt-on-error`, so a
LaTeX error stops the build instead of waiting on a prompt.

## Links of Lean names

leanblueprint links every `\lean` name to `<dochome>/find/#doc/<name>`, and without a `\dochome` the
target is the Mathlib documentation, which does not document this repository. The web version has
no such links: `src/macros/web.tex` sets `\dochome` to `https://no-doc-site.invalid` (the top-level
domain `.invalid` is reserved and never resolves), and `scripts/unlink_lean_decls.py` turns each link
to it into plain text that carries the name, failing the build if a link to that address or to the
Mathlib documentation remains. Each node gives the file and line of its first declaration
(`\srcloc`, checked by the audit).

The alternative, a doc-gen4 site built by CI next to the blueprint, is not used because it is not
cheap here. doc-gen4 documents every module the documented libraries import: Lean core (`Init`,
`Std`, `Lean`, `Lake`), batteries and lean4lean, besides the eraser: several thousand module pages,
and a build that typically takes tens of minutes, on every push. It would also need a doc-gen4 revision
that matches the release-candidate toolchain of `lean-toolchain`, pinned in a separate Lake
workspace so that the root `lake-manifest.json` stays unchanged, and updated with every toolchain
change.

## Audit

```
python3 blueprint/scripts/audit.py              # builds the Lake targets of audit.toml first
python3 blueprint/scripts/audit.py --no-build   # when they are built
python3 blueprint/scripts/audit.py --update     # also rewrites the five generated tables
```

The audit first runs `lake build` of the `[[build]]` entries of `audit.toml`: in the root the
eraser and the lean4lean libraries `Lean4Lean`, `Lean4Lean.Theory`, `Lean4Lean.Verify` (about two
minutes the first time), then in `proof/` the library `EraseProof`. It then runs
`lake env lean --run blueprint/CheckDecls.lean measure ...` in `proof/` (`env_dir`: that package
resolves the eraser, lean4lean and `EraseProof`) on every cited declaration and checks:

| Check | Rule |
|---|---|
| Nodes | every node (`definition`, `lemma`, `proposition`, `theorem`, `corollary`) has a unique `\label` with the prefix of its environment (`def:`, `lem:`, `prop:`, `thm:`, `cor:`) and a non-empty `\lean{...}`; no declaration is cited twice |
| Graph | every `\uses` resolves to a node; no node uses itself; no cycle; a proof follows its statement, never inside it; a result has a proof, a definition none |
| Planned nodes | a node marked `\planned` cites only names that do not exist, and carries no `\leanok`, `\srcloc` or `\inherited`; a node that is not planned uses no planned node |
| Existence | every `\lean` name of a node that is not planned is a declaration of the environment of `audit.toml`'s imports |
| `\leanok` | in a statement iff the node is not planned, every cited declaration exists and its axioms are allowed; in the proof of a result iff its statement has it |
| Allowed axioms | `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` only when every sorry source is a labelled lean4lean sorry of `audit.toml` allowed for the node: L1-L6 for every node, `TrProj` for test nodes (all names in `EraseProof.Test`), L7, L8 for none. A sorry source is a declaration of the closure whose own type or value uses `sorryAx`. No lean4lean axiom is allowed |
| Axiom closure | the measured axioms of every cited declaration equal `Lean.collectAxioms` (`#print axioms`); the closure follows types, values and constructors |
| `\inherited{...}` | lists exactly the labels of the lean4lean sorry sources the node's declarations depend on |
| Coverage | every declaration of the modules `EraseProof*` that has a source position is cited by a node that is not planned |
| Roots | every line of `proof/ROOTS.txt` names a root cited by a formalized node and a consumer cited by a planned node whose statement or proof uses the root's node |
| `\srcloc{path}{line}` | is the file and line of the node's first declaration |
| Hygiene | ASCII only outside `\lean{}`; underscores escaped in `\code`, `\texttt`, `\inherited`, `\srcloc` |
| Generated chapters | `render_registers.py --check` passes, and the census tables equal what the environment gives |

It writes `blueprint/.audit/report.md` (defects, per-node axioms and inherited trust, the full
lean4lean census with the entries the nodes reach), `measure.json` and the Lake logs, prints a
summary with the inherited sorries the nodes reach, and exits with status 1 on a defect.

After `build.sh web`, `python3 blueprint/scripts/audit.py --check-lean-decls blueprint/lean_decls`
checks that the names plasTeX collected exist, except the names of planned nodes (it runs
`CheckDecls.lean check` in `proof/`). It replaces `leanblueprint checkdecls`, which needs a
`checkdecls` dependency in the root `lakefile.toml` and knows no planned nodes.

## Generated files

| File | Written by | Source |
|---|---|---|
| `src/generated/shipping-changes.tex` | `scripts/render_registers.py` | `doc/SHIPPING-CHANGES.md` |
| `src/generated/divergences.tex` | `scripts/render_registers.py` | `doc/DIVERGENCES.md` |
| `src/generated/pins.tex` | `scripts/render_registers.py` | `lean-toolchain`, `lake-manifest.json` |
| `src/generated/inherited-sorries.tex` | `scripts/audit.py --update` | `audit.toml`, the Lean environment |
| `src/generated/roots.tex` | `scripts/audit.py --update` | `proof/ROOTS.txt` |
| `src/generated/planned.tex` | `scripts/audit.py --update` | the chapters |
| `src/generated/census-shipping.tex` | `scripts/audit.py --update` | the Lean environment |
| `src/generated/census-lean4lean.tex` | `scripts/audit.py --update` | the Lean environment |

All are committed. `build.sh` rewrites the first three; the audit fails when any of the eight is
stale. The renderer converts the Markdown of a register block by block and stops with an error on a
construct it does not handle (a table, a fenced code block, an unknown non-ASCII character), so a
register is never rendered partially. In `doc/DIVERGENCES.md` the entries are the `###` sections
under `## Entries`; the chapter renders the whole file, with a table of the entries after the prose
that opens `## Entries`.

## Continuous integration and the published site

`.github/workflows/blueprint.yml` runs on every push to the `blueprint` branch, and on demand
(`workflow_dispatch`). Its job `build` runs, on `ubuntu-latest`:

1. `leanprover/lean-action`: installs the toolchain of `lean-toolchain`, fetches the dependencies
   of `lake-manifest.json` (lean4lean, batteries) and runs `lake build LeanToLambdaBox Lean4Lean
   Lean4Lean.Theory Lean4Lean.Verify` (the `build_targets` of `audit.toml`). It restores and saves
   `.lake` in the GitHub cache, keyed by toolchain, manifest and commit, so a later run replays the
   lean4lean build. `build.yml` builds the same targets with the same cache key prefix.
2. Python 3.14 with `requirements.txt`; `latexmk`, `texlive-xetex`, `texlive-latex-recommended`,
   `texlive-fonts-recommended`, `texlive-plain-generic` and `fonts-lmodern` from apt.
3. `python3 blueprint/scripts/audit.py`, before the build, so that it checks the committed generated
   chapters; it also builds the proof package `proof/`. A defect fails the job. The report (`blueprint/.audit/`) is uploaded as the artifact
   `blueprint-audit`, also when the audit fails.
4. `blueprint/build.sh all`, then `audit.py --check-lean-decls blueprint/lean_decls`, and a check
   that `blueprint/web/blueprint.pdf` exists (`build.sh` skips the pdf without xelatex).
5. `actions/upload-pages-artifact` with `blueprint/web/`.

Its job `deploy` publishes that artifact with `actions/deploy-pages`, with the permissions
`pages: write` and `id-token: write`, in the environment `github-pages`, and in the concurrency
group `pages`, which runs one deployment at a time and never cancels a running one. A newer push to
`blueprint` cancels a running `build`.

The site is at the Pages address of the repository,
`https://peregrine-project.github.io/lean-to-lambdabox/` unless a custom domain is set:
`index.html` (web version), `dep_graph_document.html` (dependency graph), `blueprint.pdf`.

One-time repository settings, by an administrator:

- Settings, Pages, Build and deployment: Source "GitHub Actions".
- Settings, Environments, `github-pages`, Deployment branches and tags: add the branch `blueprint`.
  GitHub creates this environment with a rule that admits the default branch only, and the
  deployment from `blueprint` fails without it.

`workflow_dispatch` offers "Run workflow" only for workflow files on the default branch; while
`blueprint.yml` is on `blueprint` only, a push to `blueprint` is what runs it.

## Limitations

- The web version has no documentation links for the `\lean` names (see "Links of Lean names").
- The published site shows the `blueprint` branch; the other branches are not published.
- The census covers the lean4lean libraries that are built (`Lean4Lean`, `Lean4Lean.Theory`,
  `Lean4Lean.Verify`), not `Lean4Lean.Tests` or `Lean4Lean.Experimental`.
- The pdf has overfull lines where long code does not break.
