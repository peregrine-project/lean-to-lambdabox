# lean-to-lambdabox

The Lean 4 frontend of [Peregrine](https://github.com/peregrine-project/peregrine-tool). It erases
Lean's kernel terms (`Expr`) to the untyped λ□ (LambdaBox) and writes them in Peregrine's
S-expression format.

> **This branch** is `l4l/translate`, the first layer of the Lean4Lean verification stack
> ([Verification](#verification)). It is not meant for `main`; use `main` for the production
> frontend. Here `#erase` erases the programs of the verified fragment with the [pure path](#routing).
> The branch stays on lean4lean's Lean version, so it does not have the fixes of `main` made after
> the bump to `v4.35.0`.

- Builds with Lean `v4.33.0-rc2` ([`lean-toolchain`](lean-toolchain)), the version lean4lean requires.
- Depends on [lean4lean](https://github.com/digama0/lean4lean), on which the verified translation builds.

## Usage

```lean
import LeanToLambdaBox

def val_at_false (f : Bool → Nat) : Nat := f .false

#erase val_at_false to "out.ast"
```

The full syntax is:

```
#erase <term> [config { <field> := <value>, … }] [to "<file>.ast"] [mli "<file>.mli"]
```

| Clause | Writes | Without the clause |
|---|---|---|
| `config {…}` | — (sets the [options](#options)) | the defaults |
| `to "f.ast"` | the λ□ program to `f.ast`, and the constants Peregrine should inline to `f.ast.inlinings` | both are logged |
| `mli "f.mli"` | the program's OCaml signature, `val main: …` | it is logged |

### Routing

`#erase` checks whether the program's dependency closure lies in the verified fragment
(`Erasure.collectDeps`, [`Erasure/Collect.lean`](LeanToLambdaBox/Erasure/Collect.lean)):

| Program | Path |
|---|---|
| In the fragment | The **pure path**: the same traversal, with an oracle on kernel terms instead of `MetaM`. It skips the compiler's preprocessing (`macro_inline`, matcher inlining, `csimp`), so an `if` evaluates both branches. |
| Outside it | The path of `main`. |

## Options

The fields of `Erasure.ErasureConfig` ([`Erasure.lean`](LeanToLambdaBox/Erasure.lean)). The first value is the default.

| Field | Values | Effect |
|---|---|---|
| `extern` | `.preferAxiom`, `.preferLogical` | Whether an `@[extern]` constant becomes an axiom (implemented in the target language) or keeps its Lean definition. |
| `nat` | `.machine`, `.peano` | Whether `Nat` becomes primitive integers or stays an inductive type. |
| `csimp` | `true`, `false` | Whether to apply the `@[csimp]` replacements (e.g. tail-recursive variants). |
| `remove_irrel_constr_args` | `false`, `true` | Whether to drop computationally irrelevant constructor arguments. |
| `auto_inline_typeclass_dispatch` | `false`, `true` | Whether to also list in `.ast.inlinings` the instances and trivial aliases that typeclass dispatch goes through (e.g. `HAdd.hAdd → instHAdd → instAddNat → Nat.add`). |

Notes:
- **`nat := .machine`** needs `extern := .preferAxiom`. The arithmetic functions on `Nat` are then axioms, implemented in the target language (e.g. with Zarith for OCaml).
- **`auto_inline_typeclass_dispatch`** lists a constant only if:
  - it is not recursive;
  - it is not `@[noinline]`;
  - its erased body is a value;
  - its body has at most 40 nodes after inlining.

  Each decision is logged.
- **A program with no axioms**, such as one erased with `config {nat := .peano, extern := .preferLogical}`, runs with `peregrine eval`.

## With Peregrine

| Task | Command |
|---|---|
| Evaluate | `peregrine eval out.ast` |
| Compile to OCaml (Malfunction) | `peregrine ocaml out.ast --attributes=out.ast.inlinings -o out.mlf` |

The Malfunction output is compiled with `malfunction` and linked with `ocamlopt`. Axioms are linked
in as OCaml code. [`benchmarks/`](benchmarks/README.md) shows the whole pipeline.

## Tests

| Command | Checks |
|---|---|
| `scripts/regress.sh [<test>…]` | Each `tests/regress/<test>.lean` writes exactly the files in `tests/regress/expected/<test>/`, with no error and no `PANIC`. |
| `PEREGRINE=<binary> scripts/regress.sh` | Also each test's `-- peregrine: validate\|eval <file>` lines, against `tests/regress/expected-peregrine/<test>/`. |
| `scripts/regress.sh --update [<test>…]` | Rewrites the expected files; review the diff. |
| `scripts/corpus.sh <dir>` | Erases the corpus (the benchmarks and `tests/corpus/*.lean`) into `<dir>`. |
| `scripts/pure-harness.sh [--update]` | Erases each corpus program in the fragment with both paths, and compares the summary with `tests/harness/expected/pure-harness.txt`. |

[`doc/SHIPPING-CHANGES.md`](doc/SHIPPING-CHANGES.md) records every change to the code of `main` on
this branch, with its effect on the corpus, and the defects found but not fixed.

## Verification

The correctness of `#erase` is proved twice, against two formal models of Lean's type theory, in
the style of MetaRocq's `erase_correct`. Both theorems state partial correctness on a fragment of
Lean: if a term in the fragment evaluates to a value, the program `#erase` emits evaluates, under
MetaRocq's λ□ semantics, to an erasure of that value.

The proofs are about this variant of the frontend, kept on separate branches. `main` is the
production frontend: it erases every program with its own path, which is not verified.

Each stack is three branches, each a PR on the one before:

| Branch | Content |
|---|---|
| `*/translate` | The frontend, with its traversal generic over its backend. It adds the [pure path](#routing), whose oracle is proved sound against the model, and the fragment test that routes `#erase` programs to it. |
| `*/verification` | `proof/`: the theorem, the non-vacuity instances (concrete programs on which every hypothesis is proved), and `proof/scripts/check.sh`. `doc/DIVERGENCES.md` lists the departures from MetaRocq's erasure. |
| `*/blueprint` | `blueprint/`: a [leanblueprint](https://github.com/PatrickMassot/leanblueprint) of the proof, with an audit of its links to the Lean code. |

| | Lean4Lean stack (this one) | Metalean stack |
|---|---|---|
| Model of the kernel | [lean4lean](https://github.com/digama0/lean4lean) | [Metalean](https://github.com/intgrah/metalean) |
| Lean | `v4.33.0-rc2` (lean4lean's) | `v4.35.0` |
| Branches (PRs) | [`l4l/translate`](https://github.com/peregrine-project/lean-to-lambdabox/tree/l4l/translate) ([#12](https://github.com/peregrine-project/lean-to-lambdabox/pull/12)), [`l4l/verification`](https://github.com/peregrine-project/lean-to-lambdabox/tree/l4l/verification) ([#13](https://github.com/peregrine-project/lean-to-lambdabox/pull/13)), [`l4l/blueprint`](https://github.com/peregrine-project/lean-to-lambdabox/tree/l4l/blueprint) ([#14](https://github.com/peregrine-project/lean-to-lambdabox/pull/14)) | [`ml/translate`](https://github.com/peregrine-project/lean-to-lambdabox/tree/ml/translate) ([#15](https://github.com/peregrine-project/lean-to-lambdabox/pull/15)), [`ml/verification`](https://github.com/peregrine-project/lean-to-lambdabox/tree/ml/verification) ([#16](https://github.com/peregrine-project/lean-to-lambdabox/pull/16)), [`ml/blueprint`](https://github.com/peregrine-project/lean-to-lambdabox/tree/ml/blueprint) ([#17](https://github.com/peregrine-project/lean-to-lambdabox/pull/17)) |
| Theorem | `EraseProof.erase_correct` (`proof/EraseProof/Main.lean`) | `EraseProof.erase_correct` (`proof/EraseProof/Final.lean`), which adds subject reduction, and a first-order corollary (`proof/EraseProof/FirstOrder.lean`) |
| Fragment | definitions, axioms, theorems, `unsafe` definitions; no inductive types, projections, literals or quotients | adds inductive types, `casesOn`/`match`, projections, quotients, recursors of a restricted shape, and structural recursion (with the option `structural := .kernel`); no `unsafe`, mutual or well-founded definitions |
| Axioms | `propext`, `Classical.choice`, `Quot.sound`, and 6 unproved lean4lean declarations | `propext`, `Classical.choice`, `Quot.sound` |
| Non-vacuity instances | 1 | 10 |
| Based on | `main` before the bump to `v4.35.0` | `main` |
