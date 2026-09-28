# lean_to_lambdabox
An implementation of type and proof erasure from Lean's term language (represented in Lean by the type `Expr`) into the untyped lambda-calculus $\lambda_\square$ (LambdaBox),
using the same syntax as the [`peregrine` tool](https://github.com/peregrine-project/peregrine-tool).

The package builds with Lean `v4.33.0-rc2` (see [`lean-toolchain`](lean-toolchain)) and depends on [`lean4lean`](https://github.com/digama0/lean4lean), on which the verified translation builds.

## Usage
```
import LeanToLambdaBox

def val_at_false (f: Bool -> Nat): Nat := f .false

#erase val_at_false to "out.ast"
```

Elaborating the above Lean code will produce a file `out.ast`
containing $\lambda_\square$ code for the function `val_at_false`,
and a file `out.ast.inlinings` listing the constants that `peregrine` should inline
(pass it with `--attributes=out.ast.inlinings`).
This can then be converted to Malfunction code
using the `peregrine` tool,
compiled to a `.cmx` object file with the Malfunction compiler,
and linked with other OCaml object files using `ocamlopt`,
following the same steps as Rocq's verified extraction pipeline.

The full syntax is `#erase <term> [config <ErasureConfig>] [to "<file>.ast"] [mli "<file>.mli"]`.
`mli` writes the OCaml signature of the erased program, `val main: ...`.
Without `to` or `mli`, the corresponding output is logged instead.
The fields of `Erasure.ErasureConfig` (in [`Erasure.lean`](LeanToLambdaBox/Erasure.lean)) are
- `extern` (default `.preferAxiom`): whether a constant tagged `@[extern]` becomes an axiom, or keeps its Lean definition (`.preferLogical`);
- `nat` (default `.machine`): whether `Nat` is erased to primitive integers, or kept as an inductive type (`.peano`);
- `csimp` (default `true`): whether to apply `@[csimp]` replacements;
- `remove_irrel_constr_args` (default `false`): whether to remove irrelevant constructor arguments;
- `auto_inline_typeclass_dispatch` (default `false`): whether to also list in `.ast.inlinings` the instances and trivial aliases (projections, `def f := g`) that typeclass dispatch goes through, so that `peregrine` collapses chains such as `HAdd.hAdd → instHAdd → instAddNat → Nat.add`.
  A constant is listed only if it is not recursive, not tagged `@[noinline]`, its erased body is a value, and its body is small (at most 40 nodes once the listed constants are inlined into it). Each decision is logged.

For example, `#erase f config {nat := .peano, extern := .preferLogical} to "f.ast"` gives a program that `peregrine eval f.ast` can run.

For more details on these postprocessing steps, see the [benchmarks README](benchmarks/README.md).

## Tests
```
scripts/regress.sh
```
builds the package and elaborates each file `tests/regress/<test>.lean`, which writes its outputs with `#erase`.
The files written must equal those in `tests/regress/expected/<test>/` byte for byte.
With `PEREGRINE=<path to the peregrine binary>`, the script also runs the lines `-- peregrine: validate|eval <file> [<option>...]` of each test,
and compares their output with `tests/regress/expected-peregrine/<test>/<file>.<validate|eval>` when that file exists.
After an intended change of the output, `scripts/regress.sh --update [<test>...]` rewrites the expected files; review the resulting diff.
