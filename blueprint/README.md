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
                        lean4lean sorries, coverage prefix, roots file, descriptions of the
                        lean4lean modules the proof uses)
build.sh                builds the web and pdf versions
CheckDecls.lean         Lean side of the audit (existence, axioms, sorry sources, censuses,
                        the declarations of the proof package, direct uses)
requirements.txt        the Python packages of the build (leanblueprint, plasTeX), pinned
scripts/audit.py        the audit
scripts/kinds.py        node kinds and their colours, shapes and badges; writes the kinds tables
scripts/kindgraph.py    lays out the dependency graphs (Graphviz, through pygraphviz)
scripts/bpkinds.py      plasTeX package: badges, graph pages and their CSS in the web version
scripts/render_registers.py   renders the registers and the pins as chapters
scripts/leanlinks.py    the links of the web version to the Lean sources (URLs, revisions)
STYLE.md                how chapters and nodes are written (binding)
src/content.tex         chapter order
src/chapters/*.tex      hand-written chapters: intro, scope, trust, model, pure, source,
                        relation, simulation, oracle, core, final, tests, open
src/generated/*.tex     generated chapters, tables and imported nodes (never edit them)
src/macros/             common.tex (shared macros), web.tex, print.tex
src/web.tex, print.tex  drivers of the web and print versions
templates/dep_graph.html  the template of the dependency-graph pages
```

## Build

One-time setup: a Python 3.14 venv with the packages of `requirements.txt` (leanblueprint, plasTeX;
the `pygraphviz` wheel bundles Graphviz, which lays out the dependency graphs), and for the pdf
`latexmk` and `xelatex`.

```
python3 -m venv <venv> && <venv>/bin/pip install -r blueprint/requirements.txt
export PATH="<venv>/bin:$PATH"
blueprint/build.sh          # or: blueprint/build.sh web | blueprint/build.sh pdf
```

`build.sh` first runs `scripts/render_registers.py` and `scripts/kinds.py`, then `plastex` (web
version in `blueprint/web/`, and the list of cited declarations in `blueprint/lean_decls`), then
`latexmk` (`blueprint/print/print.pdf`). With the default target `all`, it then copies the pdf to
`blueprint/web/blueprint.pdf`, which the title page of the web version links to; `blueprint/web/`
is then the whole site. The web version links the Lean sources at the commit `HEAD` (section
"Links to the Lean sources"); `build.sh` warns when the working tree differs from `HEAD` outside
`blueprint/`. `leanblueprint web` and `leanblueprint pdf` run plasTeX and latexmk only: they do not
render the registers. The web version needs no server: its graphs are SVG drawn at build time, and
`index.html` opens from disk. The latexmk configuration runs xelatex with
`-interaction=nonstopmode -halt-on-error`, so a LaTeX error stops the build instead of waiting on a
prompt.

`<venv>/bin/python blueprint/scripts/kindgraph.py OUTDIR` writes the DOT, SVG and PNG of every
dependency graph, to look at a layout without building the site.

## Node kinds and dependency graphs

Every node has a kind and a status. `scripts/kinds.py` derives both from the chapters,
`proof/ROOTS.txt` and the Lean names, and holds their colours, shapes and badges; the audit checks
the derivation. The introduction (Section "Kinds, statuses and dependency graphs") shows the same
legend, generated.

### Kinds

The layer of a Lean name is test for `EraseProof.Test.*`, proof for `EraseProof.*`, lean4lean for
`Lean4Lean.*` and `Lean.*` (lean4lean extends Lean's namespaces, as in `Lean.Expr.instantiate1'`),
and shipping for any other name. The audit checks that the names of a node share one layer and
that the module of each declaration has the layer of its name (`EraseProof.Test*`, `EraseProof*`,
`Lean4Lean*`, `LeanToLambdaBox*`): a node citing a declaration of Lean itself is a defect.

| Kind | Badge | Graph node | Fill, line | Derived from |
|---|---|---|---|---|
| final | FINAL THEOREM | double octagon, large | `#F0C24B`, `#7A5A00` | the node of the declaration on the `FINAL` line of `proof/ROOTS.txt`; the audit checks there is exactly one, a `theorem` environment |
| milestone | MILESTONE | hexagon, large | `#8FBCE6`, `#0B5394` | any other `theorem` environment of the proof layer; the audit checks that the final theorem depends on it (through `\uses`) |
| step | STEP LEMMA | double ellipse | `#C4DBF2`, `#0B5394` | a result of the proof layer that the proof of the final theorem or of a milestone `\uses` directly; the audit checks these `\uses` against the Lean proofs (below) |
| lemma | LEMMA | ellipse | `#E6F0FA`, `#0B5394` | any other result of the proof layer |
| definition | DEFINITION | box | `#E6F0FA`, `#0B5394` | any other definition of the proof layer |
| shipping | SHIPPING CODE | box with two tabs | `#F9D3AE`, `#9A4A00` | a node of the shipping layer |
| test | TEST | note | `#EBDDF0`, `#7B3F8C` | a node of the test layer |
| lean4lean | LEAN4LEAN MODULE | folder | `#CDEBDD`, `#0A6B4B` | a node of the lean4lean layer: an `imported` node, which the audit writes (below); the audit checks that the `imported` environment holds exactly these nodes |
| lean4leansorry | LEAN4LEAN SORRY | cylinder | `#E8F5EE`, `#0A6B4B` | in the graphs only: one node per labelled lean4lean sorry of `audit.toml` that some node lists in `\inherited` |

The `\uses` of the final theorem and of the milestones decide which results are step lemmas, so
the audit measures them: every node they name is one whose declarations the node's declarations
use directly (a statement `\uses` in their types), and every result whose declarations they use
directly is named. The measure is `CheckDecls.lean`'s: the constants that a declaration's type
and value mention, a constructor, recursor, equation lemma or other auxiliary constant counting
for the declaration it belongs to.

The fills are light tints of hues of the Okabe-Ito palette (yellow, blue, orange, reddish purple,
bluish green), a palette made for colour-blind readers. Every kind has its own shape (the step
lemma differs from the lemma by its double outline), so no kind depends on colour alone. Dark text
on every fill has a contrast of at least 8.7:1, and every line colour at least 5.8:1 on white and
on the tints of the frames. The plasTeX theme has no dark mode; every graph draws on its own white
background, and every legend swatch on a white tile.

### Imported lean4lean nodes

`audit.py --update` writes `src/generated/lean4lean-imports.tex`, which the trust chapter inputs
(Section "What the proof uses from lean4lean"): one `imported` node per lean4lean module whose
declarations the proof library (outside its tests) or the shipping code uses directly, with

- `\lean`: those declarations (a constructor or auxiliary constant counts for its declaration);
- `\leanok`, `\srcloc` and `\inherited`, as the audit measures them;
- the description of the module from `[lean4lean_modules]` of `audit.toml` (the audit checks that
  every such module, and no other, has one);
- `\usedbystatements{...}` and `\usedbyproofs{...}`: the nodes whose declarations use them
  directly, in their types (or in a definition) and only in their proofs. The graphs draw them as
  green arrows.

The audit fails when the file is stale. The tests use lean4lean declarations too (the bridge tests
state `TrExprS`); they are not counted, so no imported node reaches `TrProj`.

### Statuses

| Status | Graph border | Badge after the heading | Derived from |
|---|---|---|---|
| standard (Within standard axioms) | thin, `#333333` | none (the check mark of `\leanok`) | otherwise: the declarations exist and depend on `propext`, `Classical.choice` and `Quot.sound` only |
| inherits | thick, crimson `#B2182B` | INHERITS and the labels | `\inherited{...}` lists lean4lean sorries (the audit measures them) |
| planned | dashed, white fill | PLANNED | `\planned` |

The legend draws a status as a border sample (the corner of an outline, with no fill), so that no
status swatch looks like a kind swatch.

### Where the conventions appear

- **Headings.** After the heading of every node, its kind badge and, for the statuses inherits
  (with the labels of the sorries) and planned, a status badge: in the web version from
  `scripts/bpkinds.py` (`thm_header_extras_tpl`), in the pdf from `generated/kinds.tex`
  (`\bpsetkind`, read by a hook on `\label` in `macros/print.tex`). In the web version the bar
  beside a node takes the line colour of its kind. A node body carries no status word: the audit
  rejects `\stShipping`, `\stProved` and the others there.
- **Chapter openers.** `\lead{Nodes} \bpnodes{chap:...}` prints the chapter's nodes by kind, and in
  the web version links to the chapter's graph (and to the graph of lean4lean, in the trust
  chapter); the audit checks that every chapter with nodes has this line, with its own label.
- **Text.** `\bpkind{key}` prints a kind badge (`final`, `milestone`, `step`, `lemma`,
  `definition`, `shipping`, `test`, `leanfourlean`, `leanfourleansorry`); the status words of the
  prose `\stProved`, `\stInherited`, `\stShipping` take the colours of the lemma line, the
  inherits border and the shipping line; `\inherited` prints in crimson.
- **Introduction.** `generated/kinds-legend.tex` (kinds, statuses, arrows) and
  `generated/kinds-chapters.tex` (nodes per chapter and kind).

### Graphs

`scripts/kindgraph.py` lays out every graph at build time with the Graphviz library of the pinned
`pygraphviz` wheel (Graphviz 14.1.5), and the pages show the SVG. Every graph has the `\uses`
arrows (a statement use wins over a proof use of the same pair: dashed), the arrows of the
imported nodes' `\usedby...` lists (green), an arrow from each lean4lean sorry to every node that
lists it (dotted crimson), and none that a path of other arrows implies (transitive reduction),
except the arrows of the `\uses` of the final theorem and of the milestones: these are all drawn,
in blue, so that the chain final theorem, milestones, step lemmas, definitions shows in full. An
arrow into a test is violet.

| Page | Content and layout |
|---|---|
| `dep_graph_chapters.html` (Chapter map; table of contents: "Dependency graph by chapter") | one box per chapter with its nodes by kind, and one for lean4lean (imported modules and sorries); an arrow between two boxes carries the number of arrows between their nodes; dot, top to bottom; a box links to its graph |
| `dep_graph_document.html` (All nodes; table of contents: "Dependency graph") | every node. Block layout: each block (a chapter of the proof library; lean4lean, framed by library with a frame for the sorries; the shipping code, framed by chapter; the tests, framed by section) is laid out by dot on its own, top to bottom; dot then places the blocks, as boxes of their size, along the arrows between them, so a block sits below the blocks it uses; Graphviz's `nop2` engine routes the arrows between blocks around the nodes. Those arrows are faint, except the blue ones. The title of a frame that holds the nodes of one chapter, or of lean4lean, links to that graph |
| `dep_graph_chap-<name>.html` (one per chapter with nodes), `dep_graph_lean4lean.html` | the nodes of the chapter (framed by section in the tests chapter), or of lean4lean (framed by library), with the nodes outside it that they use on the left and that use them on the right, faded and labelled with their chapter number (or lean4lean); dot, left to right, with invisible barriers that keep those columns apart |

On every graph page: a bar links the pages; a field finds a node by any of its Lean names (on the
chapter map, a chapter by its title or by a Lean name of its nodes); a click on a node shows its
statement and draws only its arrows and neighbours, and a halo marks it without hiding its
outline; `#<label>` in the address does the same, and the link "graph" in the heading of every node
opens its graph there.

### How the web version gets them

`src/web.tex` loads the plasTeX package `scripts/bpkinds.py` (found through `packages-dirs` in
`src/plastex.cfg`), and passes `tpl=../templates/dep_graph.html` and the node environments
(`thms`, with `imported`) to the blueprint package. The package uses the extension points of
plastexdepgraph 0.0.5 and leanblueprint 0.0.20 only, and patches no installed file:

- plastexdepgraph's document graph becomes a `KindGraph`, which hands the SVG to the template;
  a pre-cleanup callback writes the other graph pages with the same template;
- `document.userdata['thm_header_extras_tpl']` and `['thm_header_hidden_extras_tpl']` carry the
  badges and the "graph" link; `['dep_graph']['legend']` the legend;
- the commands `\bpkind` and `\bpnodes`, and `styles/bpkinds.css`, written from `kinds.css()` into
  `blueprint/.build/bpkinds/` (ignored by git), from where plasTeX copies it.

`templates/dep_graph.html` starts from plastexdepgraph 0.0.5's template (its sha256 is in the
template's header) and keeps its statement modals; update both together. The build stops when the
`\uses` arrows plasTeX collected differ from those the scripts read from the chapters. If Graphviz
finds touching nodes in the graph of all nodes, it draws the arrows between blocks straight; the
build prints a warning and goes on (`BLOCK_SEP` in `kindgraph.py` sets the spacing).

## Links to the Lean sources

In the web version every citation of the Lean sources is a link to GitHub, at the revision the site
documents; `scripts/leanlinks.py` makes the URLs and `scripts/bpkinds.py` puts them in the pages.

| Citation | Where | Links to |
|---|---|---|
| `\lean{...}` names of a node | the line "Lean: ..." under the heading (the print version prints the same line), the list "L∃∀N" of the heading, the pop-up of the node in every graph | the lines of each declaration |
| `\srcloc{path}{line}` | under the heading | the lines of the node's first declaration |
| `\leandecl{name}` | prose, the generated tables (census, inherited sorries, roots), the registers | the lines of the declaration |
| `\leanfile{path}`, `\leanfiles{dir/}{A, B}` | "Lean files" of the chapter openers, prose, the tables, the registers | the file (a path ending with `/`: the directory) |
| `\leanloc{path}{lines}`, `\leanlinesof{path}{lines}` | the tables, the registers (`path:7-13`, `:68`) | the file, and each line or range of lines |
| a labelled lean4lean sorry | its node in the graphs | the lines of the declaration |

**Revisions.** A path belongs to the repository that `[links.roots]` of `audit.toml` gives for its
first component, else to this repository:

| Repository | URL | Revision |
|---|---|---|
| this repository (`proof/`, `LeanToLambdaBox/`, ...) | `[links] repository` of `audit.toml` (`$BP_REPOSITORY_URL` overrides it; CI sets it to the repository the workflow runs in) | the commit the site is built from: `$BP_COMMIT`, else `$GITHUB_SHA` (CI), else `git rev-parse HEAD` |
| lean4lean (`Lean4Lean/`), batteries (`Batteries/`) | `url` of `lake-manifest.json` | `rev` of `lake-manifest.json` (`8223d223...`, `76e1c118...`; the second is the commit of the tag `v4.33.0-rc2` of batteries) |
| Lean (`Init/`, `Std/`, `Lean/`) | `[links] lean4` of `audit.toml`, under `src/` | the tag of `lean-toolchain` (`v4.33.0-rc2`) |

So a declaration of the proof library links to
`https://github.com/peregrine-project/lean-to-lambdabox/blob/<commit>/proof/EraseProof/Main.lean#L26-L54`,
one of lean4lean to `https://github.com/barabbs/lean4lean/blob/8223d223.../Lean4Lean/Theory/VExpr.lean#L7-L13`,
and one of Lean to `https://github.com/leanprover/lean4/blob/v4.33.0-rc2/src/Init/Prelude.lean#L1231-L1253`.
A pinned commit, unlike a branch, keeps every line number right; a link of a site built from a
commit that GitHub does not have resolves once that commit is pushed.

**Lines of a declaration.** A name links to its declaration range, from the first line of its doc
comment and modifiers to its last line, as the source links of doc-gen4 do (`#L<start>-L<end>`).
`CheckDecls.lean measure` reads the ranges from the Lean environment (`locations` of
`measure.json`); a declaration that has none (an auxiliary declaration an elaborator adds, such as
`f.unsafe_1`), or that Lean added in another module than the declaration it belongs to (an equation
lemma realized where a proof first uses it), takes the range of that declaration. `audit.py
--update` writes `src/generated/lean-locations.tsv`: the repository, path and range of every name
of a node that is not planned, of every `\leandecl` and of every labelled lean4lean sorry, and of
every full name of a declaration in the registers (the inline code `EraseProof.<name>`,
`Lean4Lean.<name>` and `Erasure.<name>` that is a declaration). The build reads it and needs no Lean.

**Registers.** `render_registers.py` turns the inline code of a register that cites the Lean
sources into these citations, outside headings: a full name with a row in `lean-locations.tsv`
becomes `\leandecl`; a `.lean` path from the root of a repository (of this repository only where
the file exists), with lines or not, `\leanfile` or `\leanloc`; `:<lines>` after such a file in the
same paragraph, `\leanlinesof`. Any other inline code (a name relative to its namespace, a
MetaRocq citation, a path relative to a directory named nearby) stays plain.

**Checks.** The audit checks, before the build:

- every name of `lean-locations.tsv` is held by its range: the text at the position of its name in
  the local source is its name, or that of the declaration it belongs to (`holds`); a mismatch
  means a stale build;
- every path of a citation is a file (or a directory) of its repository, tracked by git in this
  repository, and every cited line is a line of it;
- the chapters and the generated tables cite no `.lean` file and no full declaration name with
  `\code` or `\texttt` (they use the citations above), and no file sets `\dochome`;
- `lean-locations.tsv` is up to date.

After the build, `python3 blueprint/scripts/audit.py --check-links blueprint/web` checks every page:
every element that carries a Lean name (`data-lean`, class `lean_decl`) is a link, except a name of
a planned node; every GitHub link is at the revision of its repository, to a file (or directory) that
exists there (in git at that commit for this repository, in the package checkout or the toolchain
of that revision otherwise), at lines of that file; a name links exactly to its row of
`lean-locations.tsv`, and those lines mention it; the files of this repository that the site links
do not differ between the working tree (where the ranges were measured) and the linked commit; no
page contains the address of a documentation site leanblueprint would use (`/find/#doc/`,
`mathlib4_docs`); and every name of a node that is not planned is a link on the chapter pages and on
the graph of all nodes. It prints the links by repository and kind.

leanblueprint links each `\lean` name to a doc-gen4 site (`\dochome`, by default the Mathlib
documentation, which does not document this repository). `scripts/bpkinds.py` replaces those
templates of leanblueprint 0.0.20, so no such link is written. A doc-gen4 site of its own is not
built: it would document every module the libraries import (Lean core, batteries, lean4lean), take
tens of minutes on every push, and need a doc-gen4 pinned to the release-candidate toolchain in a
separate Lake workspace. The source links point at the code the blueprint describes, at no cost.

## Audit

```
python3 blueprint/scripts/audit.py              # builds the Lake targets of audit.toml first
python3 blueprint/scripts/audit.py --no-build   # when they are built
python3 blueprint/scripts/audit.py --update     # also rewrites the seven generated files it owns
python3 blueprint/scripts/audit.py --check-links blueprint/web   # after build.sh web
```

The audit first runs `lake build` of the `[[build]]` entries of `audit.toml`: in the root the
eraser and the lean4lean libraries `Lean4Lean`, `Lean4Lean.Theory`, `Lean4Lean.Verify` (about two
minutes the first time), then in `proof/` the library `EraseProof`. It then runs
`lake env lean --run blueprint/CheckDecls.lean measure ...` in `proof/` (`env_dir`: that package
resolves the eraser, lean4lean and `EraseProof`) on every cited declaration, and on the direct
uses of every declaration of the proof library and of the shipping code, and checks:

| Check | Rule |
|---|---|
| Nodes | every node (`definition`, `lemma`, `proposition`, `theorem`, `corollary`, `imported`) has a unique `\label` with the prefix of its environment (`def:`, `lem:`, `prop:`, `thm:`, `cor:`, `imp:`) and a non-empty `\lean{...}`; no declaration is cited twice |
| Graph | every `\uses`, and every `\ref` of `\usedbystatements` and `\usedbyproofs`, resolves to a node; no node uses itself; no cycle; a proof follows its statement, never inside it; a result has a proof, a definition and an imported node none |
| Planned nodes | a node marked `\planned` cites only names that do not exist, and carries no `\leanok`, `\srcloc` or `\inherited`; a node that is not planned uses no planned node |
| Existence | every `\lean` name of a node that is not planned is a declaration of the environment of `audit.toml`'s imports |
| `\leanok` | in a statement iff the node is not planned, every cited declaration exists and its axioms are allowed; in the proof of a result iff its statement has it |
| Allowed axioms | `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` only when every sorry source is a labelled lean4lean sorry of `audit.toml` allowed for the node: L1-L6 for every node, `TrProj` for the nodes whose declarations all belong to the module `EraseProof.Test.Bridge` (the bridge tests; check C5 of `proof/scripts/check.sh` allows the same), L7, L8 for none. A sorry source is a declaration of the closure whose own type or value uses `sorryAx`. No lean4lean axiom is allowed |
| Axiom closure | the measured axioms of every cited declaration equal `Lean.collectAxioms` (`#print axioms`), for an inductive together with its constructors (the axioms Lean stores for an imported inductive can miss those only its constructors reach); the closure follows types, values and constructors |
| `\inherited{...}` | lists exactly the labels of the lean4lean sorry sources the node's declarations depend on |
| Coverage | every declaration of the modules `EraseProof*` that has a source position is cited by a node that is not planned |
| Roots | every line of `proof/ROOTS.txt` names a root cited by a formalized node and a consumer cited by a planned node whose statement or proof uses the root's node, or `FINAL` for the final theorem, which has no consumer; a line whose unit is a decision of the plan (`O-<n>`) names a placeholder consumer: no planned statement uses the root, so the consumer's node must not use the root's node, and `roots.tex` marks the row |
| `\srcloc{path}{line}` | is the file and line of the node's first declaration |
| Hygiene | ASCII only outside `\lean{}` and `\leandecl{}`; underscores escaped in `\code`, `\texttt`, `\inherited`, `\srcloc`, `\leanfile`, `\leanfiles`, `\leanloc`, `\leanlinesof` |
| Links | the checks before the build of section "Links to the Lean sources": every linked name is held by its declaration range in the local source, every cited path and line exists, no `\code` cites a `.lean` file or a full declaration name, no `\dochome`, and `generated/lean-locations.tsv` is up to date |
| Present state | no word that narrates history (`STYLE.md` section 1: previously, since the last version, was fixed, no longer, used to, now, yet), as a whole word outside comments, in the hand-written chapters and the generated tables; the rendered registers record changes and are exempt |
| Kinds | the rules of section "Node kinds and dependency graphs": the names of a node share one layer; the module of each declaration has the layer of its name; the `imported` environment holds exactly the nodes of the lean4lean layer; one final node, a `theorem` environment; the final theorem depends on every milestone; the `\uses` of the final theorem and of the milestones agree with the declarations they use directly; no node body carries a status word; every chapter with nodes cites `\bpnodes` with its own label |
| Imported nodes | `generated/lean4lean-imports.tex` equals what `--update` writes from the Lean environment and `[lean4lean_modules]` of `audit.toml`, which has one entry per lean4lean module whose declarations the proof library (outside its tests) or the shipping code uses directly; their declarations are within the allowed axioms |
| Generated chapters | `render_registers.py --check` passes, the census tables equal what the environment gives, and the tables of `scripts/kinds.py` equal what it writes |

It writes `blueprint/.audit/report.md` (defects, per-node kind, status, axioms and inherited trust,
the full lean4lean census with the entries the nodes reach), `measure.json` and the Lake logs,
prints a summary with the number of nodes of each kind, the linked names by repository and the
inherited sorries the nodes reach, and exits with status 1 on a defect. With `--update`, when
`lean-locations.tsv` changes, it renders the registers again (they link the names it locates) and
audits again.

After `build.sh web`, `audit.py --check-links blueprint/web` checks the links of every page (section
"Links to the Lean sources"); it needs the built proof package (for `lake env lean`), the package
checkouts under `.lake/packages` and the commit the site links, and exits with status 1 on a defect.

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
| `src/generated/planned.tex` | `scripts/audit.py --update` | the chapters (a sentence when no node is planned) |
| `src/generated/census-shipping.tex` | `scripts/audit.py --update` | the Lean environment |
| `src/generated/census-lean4lean.tex` | `scripts/audit.py --update` | the Lean environment |
| `src/generated/kinds.tex` | `scripts/kinds.py` | the chapters, `proof/ROOTS.txt`, `audit.toml` |
| `src/generated/kinds-legend.tex` | `scripts/kinds.py` | the chapters, `scripts/kinds.py` |
| `src/generated/kinds-chapters.tex` | `scripts/kinds.py` | the chapters |
| `src/generated/lean4lean-imports.tex` | `scripts/audit.py --update` | the Lean environment, `audit.toml` |
| `src/generated/lean-locations.tsv` | `scripts/audit.py --update` | the Lean environment, the chapters, the generated tables, the registers |

All are committed. `build.sh` rewrites those of `render_registers.py` and `kinds.py`; the audit
fails when any of the thirteen is stale. The renderer converts the Markdown of a register block by block and stops with an error on a
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
2. Python 3.14 with `requirements.txt` (its `pygraphviz` wheel brings the Graphviz library that
   lays out the graphs); `latexmk`, `texlive-xetex`, `texlive-latex-recommended`,
   `texlive-fonts-recommended`, `texlive-plain-generic` and `fonts-lmodern` from apt.
3. `python3 blueprint/scripts/audit.py`, before the build, so that it checks the committed generated
   chapters; it also builds the proof package `proof/`. A defect fails the job. The report (`blueprint/.audit/`) is uploaded as the artifact
   `blueprint-audit`, also when the audit fails.
4. `blueprint/build.sh all`, then `audit.py --check-lean-decls blueprint/lean_decls`,
   `audit.py --check-links blueprint/web` (the links to the Lean sources), a check that
   `blueprint/web/blueprint.pdf` exists (`build.sh` skips the pdf without xelatex), and one that
   the graph pages exist. The job sets `BP_REPOSITORY_URL` to the repository it runs in; the links
   of this repository point at `$GITHUB_SHA`, the commit it builds.
5. `actions/upload-pages-artifact` with `blueprint/web/`.

Its job `deploy` publishes that artifact with `actions/deploy-pages`, with the permissions
`pages: write` and `id-token: write`, in the environment `github-pages`, and in the concurrency
group `pages`, which runs one deployment at a time and never cancels a running one. A newer push to
`blueprint` cancels a running `build`.

The site is at the Pages address of the repository,
`https://peregrine-project.github.io/lean-to-lambdabox/` unless a custom domain is set:
`index.html` (web version), `dep_graph_chapters.html` (chapter map), `dep_graph_document.html`
(graph of all nodes), `dep_graph_chap-<name>.html` (graph of a chapter), `blueprint.pdf`.

One-time repository settings, by an administrator:

- Settings, Pages, Build and deployment: Source "GitHub Actions".
- Settings, Environments, `github-pages`, Deployment branches and tags: add the branch `blueprint`.
  GitHub creates this environment with a rule that admits the default branch only, and the
  deployment from `blueprint` fails without it.

`workflow_dispatch` offers "Run workflow" only for workflow files on the default branch; while
`blueprint.yml` is on `blueprint` only, a push to `blueprint` is what runs it.

## Limitations

- The links to the Lean sources are in the web version only; the pdf prints the same names and
  paths without links.
- Only citations link (section "Links to the Lean sources"): a name in prose relative to its
  namespace (`\code{erase\_correct}`), and the MetaRocq citations, stay plain text.
- A register's citation of a line of Lean's own sources links at the tag of the documented
  commit's `lean-toolchain`; an entry written under another toolchain cites the lines of that one.
- A site built from a commit that GitHub does not have links to a commit GitHub cannot show until
  it is pushed.
- The published site shows the `blueprint` branch; the other branches are not published.
- The census covers the lean4lean libraries that are built (`Lean4Lean`, `Lean4Lean.Theory`,
  `Lean4Lean.Verify`), not `Lean4Lean.Tests` or `Lean4Lean.Experimental`.
- The pdf has overfull lines where long code does not break.
- The graph of all nodes has every node of the blueprint; its labels are legible once zoomed in. The
  chapter map and the graphs of the chapters are the readable overviews.
- The pdf has no dependency graph; the web version has them all.
- The imported nodes are one per lean4lean module, not one per declaration; their arrows lead from
  the module to the nodes that use one of its declarations directly. The lean4lean declarations
  that only the tests use have no node.
- The audit checks the `\uses` of the final theorem and of the milestones against the Lean proofs;
  the other `\uses` are written by hand, and only their resolution and acyclicity are checked.
