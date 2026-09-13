# lean_to_lambdabox

Type and proof erasure from Lean's term language (`Lean.Expr`) into the untyped
lambda-calculus $\lambda_\square$ (LambdaBox), in the S-expression syntax of the
[`peregrine` tool](https://github.com/peregrine-project/peregrine-tool).

Two things live here. **The frontend** — `LeanToLambdaBox/{Basic,Printing,Relevance,Erasure}.lean`
— is the shipping `#erase` command. **The verification** is everything else: a re-formalisation of
$\lambda_\square$'s weak call-by-value semantics, an erasure specification relation, and a
correctness theorem about the shipping eraser's own output. It is developed on branch
`dev/verify`; branch `main` carries the frontend alone.

## Build

Lean is pinned by `lean-toolchain` (v4.33.0-rc2) and the kernel theory comes from a
[lean4lean](https://github.com/barabbs/lean4lean) fork pinned by rev in `lakefile.toml`.

```
lake build          # the library, including the verification
lake build VerifyBench   # the benchmark roots; this WRITES the .ast files under VerifyBench/ast/
```

`lake build` writes no `.ast`: every module that runs `#erase` is a `VerifyBench` root, outside
`defaultTargets`.

## Usage

```lean
import LeanToLambdaBox

def val_at_false (f : Bool → Nat) : Nat := f .false

#erase val_at_false to "out.ast"
```

Elaborating this writes `out.ast`, a $\lambda_\square$ program for `val_at_false`, beside an
`out.ast.inlinings` sidecar. The command takes an optional configuration and an optional `.mli`
path:

```lean
#erase val_at_false config { extern := .preferLogical, nat := .peano, csimp := false }
  to "out.ast"
```

`peregrine` turns the `.ast` into Malfunction, C, Wasm, CakeML, Rust or Elm; the OCaml route then
runs the Malfunction compiler and `ocamlopt`, as in Rocq's verified extraction pipeline. The
sibling [`benchmarks` repository](benchmarks/README.md) documents those postprocessing steps.

## What is verified

`LeanToLambdaBox/Capstone.lean`, `shipping_erase_correct_firstorder`: for a source term the
shipping `Erasure.erase` ran on, its emitted program `(Γ, t)` is the image, under the pass
relation `Lower`, of a specification environment that `Erases` the prepared term; `(Γ, t)` is
well-formed for peregrine's first pass (`LBWfPeregrine`); and every **first-order** value the
source evaluation produces is reproduced — uniquely and box-free — by `(Γ, t)` under
$\lambda_\square$'s own `WcbvEval`.

The statement is universally quantified, so it is paired with concrete rungs.
`LeanToLambdaBox/Green.lean` instantiates it at eight programs, each ending in a literal numeral;
`lake exe green-check --all` re-runs each rung's `#erase`, byte-diffs the emitted program against
the transcription the theorem is stated about, and evaluates it with the certified evaluator
`lbEval`.

The theorem is **conditional**: several hypotheses are named binders rather than proved terms.
`doc/trust.md` classifies every one of them and every `sorryAx` root inherited from lean4lean;
`doc/coverage.md` says which of the five benchmark programs each result covers.

## Checks

| Command | What it checks |
|---|---|
| `lake exe green-check --all` | the eight rungs: committed `.ast` = transcription = re-run output, and its `lbEval` answer |
| `lake exe reify --check MOD NAME…` | a committed `SourceTable` against the environment it was reified from |
| `lake exe reify --blocks` / `--prepared` | the installed fix blocks and the prepared subjects a rung's hypotheses name |
| `lake exe hygiene` | comment hygiene; `--dup`, `--schedule`, `--tables`, `--dead`, `--cites` add the module-graph and inventory checks |
| `bash scripts/ledger.sh` | `#print axioms` on the tracked results against `test/ledger.expected` |
| `bash scripts/lean4lean-sorries.sh` | the pinned fork's `sorry` inventory against `test/lean4lean-sorries.expected` |
| `bash scripts/frozen.sh` | the benchmark sources against `test/frozen/` and the sibling repository |

`Tools/Coverage.lean` regenerates `doc/coverage.md`; `doc/panics.md`, `doc/rules-Erases.md` and
`doc/rules-Lower.md` are the tracked rule and panic tables. `doc/upstream-asks.md` lists what is
asked of lean4lean.
