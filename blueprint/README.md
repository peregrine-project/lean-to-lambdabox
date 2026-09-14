# Blueprint

A [leanblueprint](https://github.com/PatrickMassot/leanblueprint) skeleton documenting the
formal verification on `dev/verify`.

## Building

From the **repository root**, one-time setup:

```
python3 -m venv .venv
.venv/bin/pip install leanblueprint
```

Then build:

```
PATH=$PWD/.venv/bin:$PATH leanblueprint pdf      # print/print.pdf (xelatex)
PATH=$PWD/.venv/bin:$PATH leanblueprint web      # web/index.html, web/dep_graph_document.html, lean_decls
PATH=$PWD/.venv/bin:$PATH leanblueprint serve    # serves web/ on localhost so the JS dep graph renders
lake env lean --run blueprint/CheckDecls.lean blueprint/lean_decls   # after `leanblueprint web`
```

`leanblueprint web` needs `plastex` resolvable on `PATH`, hence the `PATH=...` prefix on every
command (it shells out to the bare `plastex` executable, not an absolute path).

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
start, the capstone, the trust boundary). Each currently holds only a `\chapter{}`/`\label{}`
placeholder; writers overwrite these in place.

## Labels

Every node's label is `<kind>:<name>`, where `<kind>` is `def`/`lem`/`prop`/`thm`/`cor`/`asm`
matching its environment, and `<name>` is the principal Lean declaration's fully-qualified
name with the leading `LeanToLambdaBox.` stripped and `.` replaced by `-`. This lets any
chapter `\uses{}` a node from any other chapter without coordinating names in advance.

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
