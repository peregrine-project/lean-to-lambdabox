# Blueprint

A [leanblueprint](https://github.com/PatrickMassot/leanblueprint) of the verification of the
`#erase` eraser of `lean-to-lambdabox`. It is a picture of the commit it is built from: the scope,
the trust boundary, the definitions and theorems with their status, the two registers
(`doc/SHIPPING-CHANGES.md`, `doc/DIVERGENCES.md`) and what is open. It describes the present
state only; the history is in git.

## Layout

```
audit.toml              configuration of the audit (imports, allowed axioms, inherited prefix)
build.sh                builds the web and pdf versions
CheckDecls.lean         Lean side of the audit (existence, axioms, sorry sources, censuses)
scripts/audit.py        the audit
scripts/render_registers.py   renders the registers and the pins as chapters
STYLE.md                how chapters and nodes are written (binding)
src/content.tex         chapter order
src/chapters/*.tex      hand-written chapters: intro, trust, open
src/generated/*.tex     generated chapters and tables (never edit them)
src/macros/             common.tex (shared macros), web.tex, print.tex
src/web.tex, print.tex  drivers of the web and print versions
```

## Build

One-time setup: a Python venv with leanblueprint (plasTeX), Graphviz, and for the pdf `latexmk`
and `xelatex`.

```
python3 -m venv <venv> && <venv>/bin/pip install leanblueprint
export PATH="<venv>/bin:$PATH"
blueprint/build.sh          # or: blueprint/build.sh web | blueprint/build.sh pdf
```

`build.sh` first runs `scripts/render_registers.py`, then `plastex` (web version in
`blueprint/web/`, and the list of cited declarations in `blueprint/lean_decls`), then `latexmk`
(`blueprint/print/print.pdf`). `leanblueprint web` and `leanblueprint pdf` run the same commands
but do not render the registers. `leanblueprint serve` serves `blueprint/web/` so that the
dependency graph renders. The latexmk configuration runs xelatex with
`-interaction=nonstopmode -halt-on-error`, so a LaTeX error stops the build instead of waiting on
a prompt.

## Audit

```
python3 blueprint/scripts/audit.py              # builds the Lake targets of audit.toml first
python3 blueprint/scripts/audit.py --no-build   # when they are built
python3 blueprint/scripts/audit.py --update     # also rewrites the two census tables
```

The first `lake build` of the targets (the eraser and the lean4lean libraries `Lean4Lean`,
`Lean4Lean.Theory`, `Lean4Lean.Verify`) takes about two minutes. The audit then runs
`lake env lean --run blueprint/CheckDecls.lean measure ...` on every cited declaration and checks:

| Check | Rule |
|---|---|
| Nodes | every node (`definition`, `lemma`, `proposition`, `theorem`, `corollary`) has a unique `\label` with the prefix of its environment (`def:`, `lem:`, `prop:`, `thm:`, `cor:`) and a non-empty `\lean{...}`; no declaration is cited twice |
| Graph | every `\uses` resolves to a node; no node uses itself; no cycle; a proof follows its statement, never inside it; a result has a proof, a definition none |
| Existence | every `\lean` name is a declaration of the environment of `audit.toml`'s imports |
| `\leanok` | in a statement iff every cited declaration exists and its axioms are allowed; in the proof of a result iff its statement has it |
| Allowed axioms | `propext`, `Classical.choice`, `Quot.sound`; the axioms declared in lean4lean; `sorryAx` only when every sorry source is in lean4lean. A sorry source is a declaration of the closure whose own type or value uses `sorryAx` |
| `\inherited{...}` | lists exactly the lean4lean sorry sources and axioms the node's declarations depend on |
| `\srcloc{path}{line}` | is the file and line of the node's first declaration |
| Hygiene | ASCII only outside `\lean{}`; underscores escaped in `\code`, `\texttt`, `\inherited`, `\srcloc` |
| Generated chapters | `render_registers.py --check` passes, and the census tables equal what the environment gives |

It writes `blueprint/.audit/report.md` (defects, per-node axioms and inherited trust, the full
lean4lean census with the entries the nodes reach), `measure.json` and the Lake logs, prints a
summary with the inherited sorries the nodes reach, and exits with status 1 on a defect.

After `build.sh web`, `lake env lean --run blueprint/CheckDecls.lean check blueprint/lean_decls
$(python3 blueprint/scripts/audit.py --print-imports)` checks the names that plasTeX collected. It
replaces `leanblueprint checkdecls`, which needs a `checkdecls` dependency in the root
`lakefile.toml`.

## Generated files

| File | Written by | Source |
|---|---|---|
| `src/generated/shipping-changes.tex` | `scripts/render_registers.py` | `doc/SHIPPING-CHANGES.md` |
| `src/generated/divergences.tex` | `scripts/render_registers.py` | `doc/DIVERGENCES.md` |
| `src/generated/pins.tex` | `scripts/render_registers.py` | `lean-toolchain`, `lake-manifest.json` |
| `src/generated/census-shipping.tex` | `scripts/audit.py --update` | the Lean environment |
| `src/generated/census-lean4lean.tex` | `scripts/audit.py --update` | the Lean environment |

All are committed. `build.sh` rewrites the first three; the audit fails when any of the five is
stale. The renderer converts the Markdown of a register block by block and stops with an error on a
construct it does not handle (a table, a fenced code block, an unknown non-ASCII character), so a
register is never rendered partially. In `doc/DIVERGENCES.md` the entries are the `###` sections
under `## Entries`; the chapter renders the whole file, with a table of the entries after the prose
that opens `## Entries`.

## Limitations

- The web version links each `\lean` name to leanblueprint's default documentation site, which does
  not document this repository: the links do not resolve.
- No CI job builds or audits the blueprint.
- The census covers the lean4lean libraries that are built (`Lean4Lean`, `Lean4Lean.Theory`,
  `Lean4Lean.Verify`), not `Lean4Lean.Tests` or `Lean4Lean.Experimental`.
- The pdf has overfull lines where long code does not break.
