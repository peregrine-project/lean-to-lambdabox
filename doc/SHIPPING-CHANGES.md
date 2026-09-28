# Shipping changes

This register lists every change to the shipping code on the `shipping` branch: the eraser
(`LeanToLambdaBox.lean`, `LeanToLambdaBox/`), the package files (`lakefile.toml`, `lean-toolchain`,
`lake-manifest.json`), the benchmarks (`benchmarks/`) and the tooling that checks them (`scripts/`,
`tests/`, `.github/workflows/`). The branch starts from `main` at `58701f8`.

Each change has an id `S-<n>` and exactly one commit, whose subject is
`shipping(S-<n>): <what changed and its observable effect>`. Its entry has these fields:

- **Commit:** the commit whose subject starts with `shipping(S-<n>):` (find it with
  `git log --grep='^shipping(S-<n>):'`); for a merge, say so.
- **Files and functions:** every file and function/declaration touched.
- **Why necessary:** the concrete reason (a reproduced defect, a compile error, a requirement of the
  spec).
- **Behaviour before:** observable behaviour, with the reproduction.
- **Behaviour after:** observable behaviour, with the same reproduction.
- **Effect on emitted .ast (corpus):** byte-level: which corpus files change (or "byte-identical for
  all N files"), and the nature of every difference.
- **Regression test:** the test under `tests/regress/` that fails before and passes after (or, for a
  non-behavioural change, what it guards).

Defects found but not fixed are listed at the end, under "Reported, not fixed", as `R-<n>` entries.

## The fixed corpus

The corpus is everything the eraser emits for a fixed set of inputs:

- **Benchmarks.** The 20 programs of `benchmarks/TESTS` whose harness is `natio`, erased through
  `benchmarks/via_malfunction/Makefile` as the benchmark pipeline does it, once with
  `PRUNE_CONSTRUCTORS=1` (the Makefile default, used by 12 of the 14 benchmark backends) and once
  with `PRUNE_CONSTRUCTORS=0`. Each run yields `<test>.ast`, `<test>.ast.inlinings` and
  `<test>.mli`: 120 files.
- **Examples.** The files `tests/corpus/*.lean`. Each one imports `LeanToLambdaBox` and writes its
  outputs with `#erase ... to "<file>"`:
  - `PortProbe.lean`: Nat functions, a Prop-carrying argument, a subtype, a structure with a Prop
    field, wildcard matches, derived `BEq`/`DecidableEq` (3 and 10 constructors); each erased with
    the default configuration, with constructor pruning, and applied to a literal under
    `{nat := .peano, extern := .preferLogical}`.
  - `Scope.lean`: programs with no inductive type in their dependency closure (Church numerals and
    booleans, polymorphic combinators, proof and type arguments, `let` of values, types and proofs,
    universe polymorphism, a Prop-typed axiom used as an argument).
  - `Defects.lean`: reproductions of the `R-<n>` entries below.

Regenerate it from the current checkout with

    scripts/corpus.sh OUTDIR

which writes `OUTDIR/benchmarks/{prune,noprune}/` and `OUTDIR/examples/<Stem>/`, plus logs and run
information under `OUTDIR/_meta/` (not part of the corpus; `_meta/panics` counts `PANIC` messages
per log). The script uses only `lake` and `make` from `PATH`; the toolchain is the one the
checkout's `lean-toolchain` files name. Compare two corpora with

    scripts/corpus-diff.sh [--normalize] [--summary] A B

It prints the files that are identical, differing, or present on one side only, then a unified diff
per differing file (with a line break before every constructor). `--normalize` also compares the
files after replacing hygienic name suffixes (`x._@.M._hyg.N`, `x._@.M.<hash>._hygCtx._hyg.N`) by a
fixed token, to separate toolchain-induced renamings from real changes. The exit status is 0 when
the corpora agree.

## Regression tests

A regression test is a file `tests/regress/<name>.lean` that writes its outputs with
`#erase ... to "<file>"`. Its expected outputs are `tests/regress/expected/<name>/`. Run

    scripts/regress.sh [TEST...]

It builds the package, elaborates each test in a fresh directory, and compares the files written
with the expected ones byte for byte. A test fails if Lean reports an error, if a `PANIC` message
appears (unless the test contains the line `-- regress: allow-panic`), or if any file is missing,
extra or different. With `PEREGRINE=<path to the peregrine binary>`, it also runs the lines
`-- peregrine: validate <file> [<option>...]` and `-- peregrine: eval <file> [<option>...]` of each
test; each must succeed and, when `tests/regress/expected-peregrine/<name>/<file>.<verb>` exists,
print exactly that. `scripts/regress.sh --update [TEST...]` rewrites the expected files from the
current checkout. CI (`.github/workflows/build.yml`) runs `scripts/regress.sh` after the build,
without peregrine.

---

## S-1: Change register, corpus and regression harness

- **Commit:** the commit whose subject starts with `shipping(S-1):`
  (`git log --grep='^shipping(S-1):'`).
- **Files and functions:**
  - new `doc/SHIPPING-CHANGES.md` (this register);
  - new `scripts/common.sh` (`die`, `build_frontend`, `run_lean`, `tokenize`,
    `normalize_hygiene`), `scripts/corpus.sh`, `scripts/corpus-diff.sh`, `scripts/regress.sh`;
  - new `tests/corpus/PortProbe.lean`, `tests/corpus/Scope.lean`, `tests/corpus/Defects.lean`;
  - new `tests/regress/smoke.lean`, `tests/regress/expected/smoke/` (5 files),
    `tests/regress/expected-peregrine/smoke/` (3 files), `tests/regress/.gitignore` (re-includes
    the `*.ast` files that the root `.gitignore` excludes), `tests/regress/.gitattributes` (expected
    files are kept verbatim: no end-of-line conversion, no whitespace check);
  - `.github/workflows/build.yml`: new step "Shipping regression tests".

  No file under `LeanToLambdaBox/`, no package file and no file under `benchmarks/` changes.
- **Why necessary:** the specification (§5.1) requires this register, the byte-level effect of each
  change on a fixed corpus of the benchmark programs plus own examples, and a regression test per
  change; §5.3 asks CI to run the shipping regression tests.
- **Behaviour before:** the eraser as on `main`; there was no register, no corpus tooling and no
  test, and CI ran only `lake build`.
- **Behaviour after:** the eraser is unchanged. `scripts/regress.sh` prints `ok   smoke` and
  `all 1 tests passed`; with `PEREGRINE` set, `fact3.ast` validates and evaluates to
  `Nat.succ` applied six times to `Nat.zero` (`fact 3 = 6`). `scripts/corpus.sh OUTDIR` writes 284
  files.
- **Effect on emitted .ast (corpus):** byte-identical for all 284 files (116 `.ast`,
  116 `.ast.inlinings`, 52 `.mli`), since no shipping code changes. The benchmark part (120 files)
  is byte-identical to the outputs of an unmodified `58701f8` checkout erased through the same
  Makefile rules, and two runs of `scripts/corpus.sh` give byte-identical corpora.
- **Regression test:** `tests/regress/smoke.lean` guards the README example under the default
  configuration and a closed recursive program under Peano naturals (`fact 3`).

---

## Reported, not fixed

Each entry below was reproduced on this branch. Unless stated otherwise, the reproduction is an
example in `tests/corpus/Defects.lean` whose output lies in `examples/Defects/` of a corpus, and
`peregrine` is `../peregrine-tool/_build/default/bin/main.exe`.

### R-1: Primitive integers are printed as quoted strings

- **What:** a machine-mode Nat literal is printed as `(tPrim (primInt "7"))`, a string atom.
  `peregrine-tool/doc/format.md` specifies a numeric atom, `(primInt 7)`, and peregrine's parser
  accepts only that (since peregrine commit `556fe09`).
- **Where:** `LeanToLambdaBox/Printing.lean`: instance `Serialize (BitVec n)`.
- **Reproduction:** `primint.ast` (`def seven : Nat := 7`, default configuration):
  `peregrine validate primint.ast` fails with `could not read integral type, got a non-Num atom "7"`.
  All 40 benchmark `.ast` files contain such atoms.
- **Impact:** no output of the default configuration (`nat := .machine`) that contains a Nat literal
  can be read by the current peregrine. Outputs with `nat := .peano` contain no primitive integer.
- **Why not fixed:** not required by the verification goal unless it later becomes required.

### R-2: String atoms are not escaped

- **What:** string atoms are written between double quotes with no escaping. Kername identifiers are
  sanitized, but module-path components and inductive and constructor names are printed from the
  Lean name as they are, so a `"` or `\` in them breaks the S-expression.
- **Where:** `LeanToLambdaBox/Printing.lean`: `quote_atom`; `LeanToLambdaBox/Basic.lean`:
  `toModPath`; `LeanToLambdaBox/Erasure.lean`: `register_inductive` (`toString ind_name`,
  `toString ctor_name`).
- **Reproduction:** `quote_modpath.ast` (`«ns"q».f 1`): `peregrine validate` fails with
  `could not read 'prod', expected list of length 2, got list of a different length`;
  `quote_inductive.ast` (`inductive «Q"T» where | «m"k»`): `Invalid character`.
- **Impact:** programs with such names produce unreadable files.
- **Why not fixed:** not required by the verification goal unless it later becomes required.

### R-3: Kernames are not injective

- **What:** `cleanIdent` replaces every character outside `[A-Za-z0-9_]` by `_u<code>`, so `a b`
  and `a_u32b` get the same identifier; numeric name components and digit strings coincide; a mutual
  block's kername is the concatenation of its members' names (`[A, B]` and `AB` coincide); and the
  module (`DirPath`) is always empty.
- **Where:** `LeanToLambdaBox/Basic.lean`: `cleanIdent`, `toKername`, `toModPath`, `rootKername`;
  `LeanToLambdaBox/Erasure.lean`: `register_inductive` (`mutualBlockName`).
- **Reproduction:** `collide.ast` (`colA.«a b» + colA.a_u32b`): `peregrine validate` fails with
  `Duplicate definition .Defects.colA.a_u32b`.
- **Impact:** distinct Lean constants can be emitted under one λ□ name.
- **Why not fixed:** not required by the verification goal unless it later becomes required.

### R-4: Unsupported literals are erased to □ after a panic

- **What:** string literals, and Nat literals above `2^62 - 1` in machine mode, reach `panic!`. A
  Lean panic prints `PANIC ...` and continues with the default value, here `□`, so `#erase`
  succeeds, writes the file and exits with status 0.
- **Where:** `LeanToLambdaBox/Erasure.lean`: `erase.visitLiteral`.
- **Reproduction:** `strlit.ast` (`#erase "abc"`) is `(Untyped () (Some tBox))`; in `biglit.ast`
  (`5000000000000000000 : Nat`) the literal is `tBox`. The log contains
  `PANIC at Erasure.erase.visitLiteral`. Both files pass `peregrine validate`.
- **Impact:** silent miscompilation.
- **Why not fixed:** not required by the verification goal unless it later becomes required.

### R-5: An alternative whose Π-type is not syntactic gets a branch without binders

- **What:** a `casesOn` alternative that is not a λ is η-expanded through its inferred type with
  `forallMonocular`, which expects a syntactic `∀`. If the type is a Π only after unfolding, it hits
  `unreachable!`; the panic's default yields a branch with no binders, which no longer matches the
  constructor's arity.
- **Where:** `LeanToLambdaBox/Erasure.lean`: `forallMonocular`, `lambdaMonocularOrIntro`,
  `lambdaOrIntroToArity` (called by `erase.visitAlt`); `withAppEtaToMinArity` has the same
  limitation.
- **Reproduction:** `nonsyn_pi.ast` (`viaCases 3`, where the successor alternative is
  `g : MyFun` with `def MyFun := Nat → Nat`; Lean value 2). The log contains
  `PANIC at Erasure.forallMonocular`; `peregrine validate` accepts the file; `peregrine eval`
  prints `constr con_15` / `constr con_106` instead of `Nat.succ (Nat.succ Nat.zero)`.
- **Impact:** silent miscompilation that `peregrine validate` does not detect.
- **Why not fixed:** not required by the verification goal unless it later becomes required.

### R-6: Peano literals exhaust the stack

- **What:** with `nat := .peano`, a literal `n` is translated by `n` nested calls
  (`visitLiteral` → `visitConstructor` → `visitAppArgs` → `visitExpr`).
- **Where:** `LeanToLambdaBox/Erasure.lean`: `erase.visitLiteral` (Peano branch).
- **Reproduction:** a file containing `import LeanToLambdaBox` and
  `#erase (5000 : Nat) config {nat := .peano, extern := .preferLogical} to "p.ast"` makes Lean abort
  (exit status 134) with `deep recursion was detected at 'interpreter'`; `300` succeeds. It is not
  in the corpus because it aborts the elaboration.
- **Impact:** Peano mode fails on literals of a few thousand; the output grows linearly with the
  value.
- **Why not fixed:** not required by the verification goal unless it later becomes required.

### R-7: Inductive types are always declared non-propositional

- **What:** every inductive body is printed with `ind_propositional = false` and `IntoAny`, also for
  inductives in Prop (`And`, `Eq`, `Acc`, …). A match on a proof of a large-eliminating Prop
  inductive becomes a `tCase` on `□`. MetaRocq evaluates such a case only for inductives flagged
  propositional (`eval_iota_sing`, `erasure/theories/EWcbvEval.v`), and removes such cases only for
  them (`EOptimizePropDiscr.v`).
- **Where:** `LeanToLambdaBox/Basic.lean`: `OneInductiveBody` (defaults `propositional := false`,
  `kelim := .IntoAny`); `LeanToLambdaBox/Erasure.lean`: `register_inductive`.
- **Reproduction:** `and_elim.ast` (`andElim True True ⟨trivial, trivial⟩`, Lean value 7):
  `peregrine eval` fails with `Case: <15> branch not found`. With the flag of `And` set to `true`
  by hand in a copy, it evaluates to 7.
- **Impact:** programs that eliminate proofs of `And`, `Eq`, `Acc`, … into data do not evaluate.
- **Why not fixed:** not required by the verification goal unless it later becomes required.

### R-8: Informative index fields of large-eliminating Prop inductives are lost

- **What:** Lean lets a Prop inductive with one constructor eliminate into any sort when each
  non-Prop field of the constructor also appears as an index of its result type (for instance
  `Foo.mk (n : Nat) : Foo 0 n`, or `Acc.intro`, whose `x` is an index). The branch of such a match
  receives the field. The eraser turns the proof into `□` and binds the field in the branch; the
  value exists only in the index argument, which is dropped. Setting the propositional flag (R-7)
  does not help, since MetaRocq's rule for a case on `□` fills the fields with `□`.
- **Where:** `LeanToLambdaBox/Erasure.lean`: `erase.visitCases` (generic path).
- **Reproduction:** `index_field.ast` (`getN 1 (Foo.mk 1)`, `#reduce` gives 1): `peregrine eval`
  fails with `Case: <15> branch not found`; with the flag of `Foo` set to `true` by hand in a copy,
  it prints `constr con_15` / `constr con_107` instead of `Nat.succ Nat.zero`.
- **Impact:** such programs do not evaluate, and would compute wrong values once R-7 is fixed
  alone.
- **Why not fixed:** not required by the verification goal unless it later becomes required.

### R-9: Recursors and other constants without a value become axioms

- **What:** a constant without a value (every recursor `T.rec`, the `Quot` primitives, Lean
  axioms) is emitted as `ConstantDecl None`. Casts along equalities (`h ▸ x`, matches on `rfl`) go
  through `Eq.rec`, well-founded recursion reaches `False.rec`, and noncomputable recursion reaches
  `T.rec`; none of them gets a λ□ definition.
- **Where:** `LeanToLambdaBox/Erasure.lean`: `erase.visitMutual` (the branch where `ci.value?` is
  `none`), `addAxiom`.
- **Reproduction:** `eq_cast.ast` (`castTo Nat rfl 3`): `peregrine eval` fails with
  `Axioms found ... .Eq.rec`; `wf_rec.ast` (`log2 8`, well-founded recursion):
  `Axioms found ... .False.rec`.
- **Impact:** such programs run only where the axioms are implemented outside λ□; the benchmark
  runtime implements `Eq.rec` only.
- **Why not fixed:** not required by the verification goal unless it later becomes required.

### R-10: Recursive structures get no projection declarations

- **What:** projection declarations are generated only for a non-recursive inductive with one
  constructor alone in its block, but `Expr.proj` on any structure is translated to `tProj`.
- **Where:** `LeanToLambdaBox/Erasure.lean`: `register_inductive` (`is_struct`), `erase.visitProj`.
- **Reproduction:** `rec_struct_proj.ast` (`structure RS where val : Nat; kids : List RS`,
  `rsVal ⟨3, []⟩`): `peregrine validate` fails with
  `Projection .Defects_u46RS,0:0,0 not found`.
- **Impact:** programs that project out of recursive structures are rejected.
- **Why not fixed:** not required by the verification goal unless it later becomes required.

### R-11: Fixpoints have recursive-argument index 0 and bodies that are not η-expanded

- **What:** every fixpoint definition is printed with `rarg = 0`, and its body is used as it is
  (the code has a TODO to η-expand it). MetaRocq's fixpoint well-formedness requires a λ body and
  its guarded-fixpoint evaluation reads `rarg`. Current outputs work because the compiler's
  pre-definitions are λs and evaluation is call by value.
- **Where:** `LeanToLambdaBox/Basic.lean`: `FixDef` (`principalArgIdx := 0`);
  `LeanToLambdaBox/Erasure.lean`: `erase.visitMutual`, `mkDef`.
- **Reproduction:** every recursive definition, e.g. corpus `examples/PortProbe/fact.default.ast`:
  `(def (nNamed "Tiny.fact") (tLambda ...) 0)`.
- **Impact:** none observed; a fixpoint whose body is not a λ is not guaranteed to be well formed.
- **Why not fixed:** not required by the verification goal unless it later becomes required.

### R-12: Mutual blocks skip the `@[extern]` and `@[inline]` handling

- **What:** the rules that turn `@[extern]` constants into axioms and record `@[inline]` /
  `@[always_inline]` constants run only for blocks with a single declaration.
- **Where:** `LeanToLambdaBox/Erasure.lean`: `erase.visitMutual`.
- **Reproduction:** `mutual_inline.ast.inlinings` does not list `fooI`, which is `@[inline]` in a
  mutual block. For `@[extern]`: with the default configuration, a recursive `@[extern "f"] def`
  becomes an axiom, while the same definition inside a `mutual` block is erased to its `tFix` (this
  case is not in the corpus because Lean 4.22's own compiler panics on it).
- **Impact:** inconsistent treatment of attributes; low.
- **Why not fixed:** not required by the verification goal unless it later becomes required.

### R-13: `@[implemented_by]` is ignored

- **What:** the eraser always uses a constant's logical definition, while Lean's compiler runs its
  `@[implemented_by]` implementation. When the two disagree, the erased program and Lean's compiled
  code compute different values.
- **Where:** `LeanToLambdaBox/Erasure.lean`: `erase.visitMutual` (uses `ci.value?`),
  `erase.visitConstApp` (no `implemented_by` check).
- **Reproduction:** `implemented_by.ast` (`fastId 2`, where `fastId n := n + 1` is implemented by
  `slowId n := n`): `#eval fastId 2` prints 2; `peregrine eval implemented_by.ast` prints 3.
- **Impact:** differs from Lean's compiled code for such constants; the logical definition is what
  a proof about the kernel term refers to.
- **Why not fixed:** not required by the verification goal unless it later becomes required.

### R-14: Erasability is decided by the elaborator at default transparency

- **What:** `isErasable` uses `Meta.inferType`, `Meta.isProp` and `Meta.isTypeFormerType`; the last
  one weak-head normalizes at default transparency, which does not unfold `@[irreducible]`
  definitions. A type behind an irreducible alias is therefore kept as a relevant term.
- **Where:** `LeanToLambdaBox/Erasure.lean`: `isErasable`.
- **Reproduction:** `irreducible_alias.ast`: `mkT : MyType`, with `@[irreducible] def MyType := Type`,
  is emitted as the declaration `mkT := id □ □` instead of being erased.
- **Impact:** under-erasure; the value computed is unaffected in the observed case.
- **Why not fixed:** not required by the verification goal unless it later becomes required.

### R-15: `#erase` without `to` logs the program in place of the attributes

- **What:** without an output path, the branch meant to log the attributes configuration logs the
  program a second time.
- **Where:** `LeanToLambdaBox/Erasure.lean`: `eraseElab` (the `.none` case of the `.inlinings`
  match).
- **Reproduction:** a file containing `import LeanToLambdaBox`, `def seven : Nat := 7` and
  `#erase seven`: the messages contain the program twice and no `(attributes_config ...)`.
- **Impact:** cosmetic.
- **Why not fixed:** not required by the verification goal unless it later becomes required.

### R-16: A log message lacks string interpolation

- **What:** the message for `@[extern]` constructors is a plain string literal, so it prints the
  placeholders literally.
- **Where:** `LeanToLambdaBox/Erasure.lean`: `register_inductive`.
- **Reproduction:** after `scripts/corpus.sh OUT`, `OUT/_meta/logs/benchmarks-prune.log` contains
  `Constructor {ctor_name} of type {ind_name} is marked @[extern], emitting axiom.`
- **Impact:** cosmetic.
- **Why not fixed:** not required by the verification goal unless it later becomes required.

### R-17: The `.mli` signature falls back to `unit`

- **What:** `to_ml_type` handles `Nat`, `Unit`/`PUnit`, `Bool`, `List` and arrows; any other type is
  reported with a warning and printed as `unit`, which does not describe the value. The file has no
  final newline.
- **Where:** `LeanToLambdaBox/Erasure.lean`: `to_ml_type`, `gen_mli`, `eraseElab`.
- **Reproduction:** `mli_fallback.mli` (`toMy : Nat → MyNat`, a user inductive) is
  `val main: Z.t -> unit`, with the warning
  `failed to translate Defects.MyNat into ML type, emitting unit instead`.
- **Impact:** an OCaml harness written against such a signature is type-unsound.
- **Why not fixed:** not required by the verification goal unless it later becomes required.

### R-18: The benchmark Makefile does not re-erase after a frontend change

- **What:** the rule that produces `%.ast` and `%.mli` depends on the generated `.lean` file and on
  `../FromLeanCommon*`, not on the frontend sources, and `%.ast.inlinings` is not a declared output.
  A build directory keeps the outputs of the frontend that first produced them.
- **Where:** `benchmarks/via_malfunction/Makefile`: rule
  `$(build)/%.ast $(build)/%.mli: $(build)/%.lean ../FromLeanCommon.lean ../FromLeanCommon/`.
- **Reproduction:** in `benchmarks/via_malfunction`, after `make build/<id>/even.ast`, edit
  `LeanToLambdaBox/Erasure.lean` and run the same command: make prints
  `make: 'build/<id>/even.ast' is up to date.` `scripts/corpus.sh` deletes the outputs before
  erasing for this reason.
- **Impact:** stale benchmark outputs after frontend changes.
- **Why not fixed:** not required by the verification goal unless it later becomes required.

### R-19: `lake build` in `benchmarks/` builds nothing

- **What:** `benchmarks/lakefile.toml` sets `default_targets`; Lake's key is `defaultTargets`, so
  the package has no default target.
- **Where:** `benchmarks/lakefile.toml`.
- **Reproduction:** in a copy of `benchmarks/` without `.lake`, `lake build` prints
  `Build completed successfully.` and writes no `.lake/build/lib/lean`.
- **Impact:** low; the benchmark Makefile builds what it needs through `lake lean`.
- **Why not fixed:** not required by the verification goal unless it later becomes required.

### R-20: The benchmark runtime disagrees with Lean on some operations

- **What:**
  - `def__Nat_pred = Z.pred` gives `Nat.pred 0 = -1`; Lean gives 0.
  - `def__Int_sub = Z.add` in `int.ml` (the inline variant `int-inline.ml` is correct).
  - `nat.mli` types the second argument of `Nat.shiftl`, `Nat.shiftr` and `Nat.pow` as OCaml
    `int`, while the erased program passes a `Z.t`.
  - `def__Array_get_u33Internal` (`Array.get!`) out of bounds runs `assert false`; Lean panics and
    returns the default element.
- **Where:** `benchmarks/via_malfunction/nat.ml:25` and `nat-inline.ml:58` (`def__Nat_pred`),
  `int.ml:9` (`def__Int_sub`), `nat.mli:16-18`, `JCFArray.ml:168-170`.
- **Reproduction:** the cited lines. No benchmark program references `Nat.pred` or `Int.sub` (none
  of the 40 benchmark `.ast` files names them).
- **Impact:** wrong results or aborts for programs that use these operations on these inputs.
- **Why not fixed:** not required by the verification goal unless it later becomes required.

### R-21: Axioms without an OCaml implementation fail only at link time

- **What:** the eraser emits an axiom for every constant without a value and, under
  `extern := .preferAxiom`, for every `@[extern]` constant; the benchmark runtime implements a fixed
  set (`Nat`, `Int`, `Eq.rec`, `Decidable`, eight `Array` operations). Any other axiom (for instance
  `False.rec`, `Quot.lift`, `Array.pop`, `UInt32` operations) erases without error and fails when
  the OCaml program is linked.
- **Where:** `LeanToLambdaBox/Erasure.lean`: `erase.visitMutual`, `addAxiom`;
  `benchmarks/via_malfunction/axioms.ml`.
- **Reproduction:** `wf_rec.ast` references the axiom `False.rec`; no file in
  `benchmarks/via_malfunction/` defines `def__False_rec`.
- **Impact:** missing implementations are reported by the OCaml linker, not by the eraser.
- **Why not fixed:** not required by the verification goal unless it later becomes required.

### R-22: The benchmark `list_sum_rev` does not reverse

- **What:** `list_sum_rev n := List.replicate n 1 |>.foldl Nat.add 0` is the same program as
  `list_sum_foldl`; the reversing variant is `shared_list_sum_rev`, which is not in
  `benchmarks/TESTS`.
- **Where:** `benchmarks/FromLeanCommon.lean`: `list_sum_rev`.
- **Reproduction:** corpus `benchmarks/prune/list_sum_rev.ast` equals `list_sum_foldl.ast` byte for
  byte once the name `list_sum_rev` is replaced by `list_sum_foldl`.
- **Impact:** the benchmark measures the left fold twice.
- **Why not fixed:** not required by the verification goal unless it later becomes required.

### R-23: Documentation drift

- **What:** `README.md` shows `import Erasure`; the module is `LeanToLambdaBox`.
  `benchmarks/via_malfunction/README.md` says "These four switches" and lists three.
- **Where:** `README.md:7`; `benchmarks/via_malfunction/README.md:12`.
- **Reproduction:** a file whose first line is `import Erasure` fails with
  `unknown module prefix 'Erasure'`.
- **Impact:** documentation only.
- **Why not fixed:** not required by the verification goal unless it later becomes required.
