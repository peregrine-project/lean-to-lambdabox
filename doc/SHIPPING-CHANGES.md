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

A regression test is a file `tests/regress/<name>.lean` that writes its outputs into its working
directory, normally with `#erase ... to "<file>"`. Its expected outputs are
`tests/regress/expected/<name>/`. Run

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

## S-2: Merge of `dev/zulip-issues`

- **Commit:** the merge commit whose subject starts with `shipping(S-2):`
  (`git log --grep='^shipping(S-2):'`). It is a `--no-ff` merge of `dev/zulip-issues` at `28955eb`
  (`main` plus `94a429c`, `e46224f` and `8db2dd9`), and it also adds the tests and register text
  listed below.
- **Files and functions:**
  - `LeanToLambdaBox/Erasure.lean`: `ErasureConfig` (new field `auto_inline_typeclass_dispatch`,
    default `false`); new `LBTerm.stripLambdas`, `LBTerm.containsFix`, `LBTerm.isTrivialAlias`;
    `erase.visitMutual` (the `@[inline]` check is computed first, as `leanInline`; new
    post-erasure auto-inline step in the non-recursive branch); `MLType` (new constructors
    `string`, `option`, `array`, `prod`); `MLType.toString` (now `partial`; `protArrow` and
    `protCtor` replace `toStringProtected`); `to_ml_type` (new cases `Int`, `String`, `Option`,
    `Array`, `Prod`).
  - `benchmarks/via_malfunction/Makefile`: the `lake lean` rule also names `%.ast.inlinings` as a
    target.
  - `benchmarks/via_malfunction/nat-inline.ml` (15 attributes) and `int-inline.ml` (9 attributes):
    `[@inlined]` becomes `[@inlined hint]` on Zarith calls.
  - new `tests/regress/mli_types.lean`, `tests/regress/auto_inline.lean`,
    `tests/regress/runtime_inlined_hint.lean`, their expected outputs in
    `tests/regress/expected/<test>/`, and `tests/regress/expected-peregrine/auto_inline/`;
  - `tests/regress/expected/smoke/fact3.ast`: re-baselined; its 6 hygienic suffixes grow by 1, as in
    the corpus below (`fact3.ast` is written with a `config` clause);
  - `scripts/regress.sh`: header comment only (a test may write its outputs without `#erase`);
  - `doc/SHIPPING-CHANGES.md`: this entry; the paragraph on regression tests; R-17 and R-18
    updated to the merged code; new R-24, R-25, R-26.
- **Why necessary:** §5.1 of the specification requires merging `dev/zulip-issues` after checking,
  before and after, each issue it claims to address. Its commit messages make five claims; each was
  reproduced on this branch before and after the merge, with these verdicts:
  - C1 (`94a429c`): the `.mli` printer covers `Int`, `String`, `Option`, `Array` and `Prod`, with
    OCaml-correct precedence. **Partially correct**; defects D1, D2, D3.
  - C2 (`94a429c`, `e46224f`, `8db2dd9`): `auto_inline_typeclass_dispatch` marks
    typeclass-dispatch constants for inlining. **Correct as an option that is off by default and
    leaves the default output unchanged; defective when turned on**: defects D5 to D10.
  - C3 (`94a429c`): `[@inlined hint]` silences OCaml warning 55. **Correct; the generated code is
    unchanged** (D12).
  - C4 (`94a429c`): declaring `%.ast.inlinings` as an output of the `lake lean` rule prevents
    peregrine's "no … inlinings file" failure. **Not fixed by this change alone** (D4).
  - C5 (`94a429c`): the note `references/inlining_diagnosis.md` shows that the kernames match and
    that the `instDecidableEqNat` symptom lies in peregrine. **The conclusion holds; the note's
    candidate causes are wrong, and no commit contains the note** (D11).

  The defects found in the branch are numbered D1 to D12 below. D1 to D9 remain at this commit and
  are fixed in later entries of this register. D10, D11 and D12 are informational and are reported
  as R-24, R-25 and R-26.
- **Behaviour before:** the native checks of C1 compile the erased program with peregrine
  (`unbox.config`, after rewriting `(primInt "N")` to `(primInt N)` because of R-1), malfunction and
  `ocamlopt` 4.14.2 without flambda, and link it with the `via_malfunction` runtime and an OCaml
  harness written against the emitted `.mli`.
  - C1: a result of type `Int`, `Option Nat`, `Nat × Bool`, `List (Nat × Nat)`,
    `Option (Nat → Nat)`, `(Nat → Nat) × Nat`, `Array Nat`, `(Nat × Nat) × Nat`, `Nat × (Nat × Nat)`
    or `String` gets the signature `unit` (`unit list` for the list), with the warning
    `failed to translate … into ML type, emitting unit instead`. `List (Nat → Nat)` is printed
    `Z.t -> Z.t -> Z.t list`, which OCaml reads as a function of two arguments; a harness that
    matches a list does not type-check (`This pattern should not be a list literal`).
  - C2: `config {auto_inline_typeclass_dispatch := true}` is an error:
    `'auto_inline_typeclass_dispatch' is not a field of structure 'Erasure.ErasureConfig'`.
  - C3: `make build/<id>/axioms.cmx FLAMBDA=0 MALFUNCTION_NO_FLAMBDA_SWITCH=peregrine
    ARRAYML=JCFArrayOCaml4.ml` in `benchmarks/via_malfunction` prints warning 55
    (`Cannot inline: Function information unavailable`) 20 times, for `nat.ml` and `int.ml`.
  - C4: in `benchmarks/via_malfunction`, after `make build/<id>/even.mlf` (with the options of C3 and
    `PEREGRINE` set to a wrapper applying the R-1 rewrite), delete `even.ast.inlinings` and
    `even.mlf` and run the same command: peregrine fails with
    `option '--attributes': invalid element in list (build/<id>/even.ast.inlinings): no
    build/<id>/even.ast.inlinings file or directory`, the error reported on Zulip on Feb 17. With a
    copy of the Makefile whose `INLINING=1` rule for `%.mlf` also lists `$(build)/%.ast.inlinings` as a
    prerequisite, make stops with `No rule to make target 'build/<id>/even.mlf'`, the failure
    reported on Zulip on Feb 13 (`No rule to make target 'bin/even'`).
  - C5: `scr n := isZeroIf n + (match isZeroDec n with | .isTrue _ => 10 | .isFalse _ => 20)`, with
    `isZeroIf n := if n = 0 then 1 else 2` and `isZeroDec n : Decidable (n = 0) := inferInstance`,
    erased with `{remove_irrel_constr_args := true}`: `instDecidableEqNat` has the same kername in
    its call sites, its declaration and `scr.ast.inlinings`. After
    `peregrine compile scr.ast unbox.config --attributes=scr.ast.inlinings`, `isZeroDec` calls
    `$def__Nat_decEq`, but `isZeroIf` still computes
    `(let ($discr (apply $def__instDecidableEqNat $n …)) (switch $discr …))`.
- **Behaviour after:**
  - C1: the same results get `Z.t`, `Z.t option`, `Z.t * bool`, `(Z.t * Z.t) list`,
    `(Z.t -> Z.t) option`, `(Z.t -> Z.t) * Z.t`, `(Z.t -> Z.t) list` and `Z.t LeanArray.array`,
    without warning, and the harnesses print the Lean values (`-7`, `None / Some 5`, `0 true`,
    `5 6`, `6`, `6 5`, `6`, `2`). Remaining defects:
    - D1: both nested products are printed `Z.t * Z.t * Z.t`, an OCaml triple, while the value is a
      pair with a pair inside. The harness written against it crashes (exit status 139) for
      `Nat × (Nat × Nat)` and prints garbage for `(Nat × Nat) × Nat`; with the signatures corrected
      by hand to `Z.t * (Z.t * Z.t)` and `(Z.t * Z.t) * Z.t`, both print `5 6 7`. Before the merge
      both were a warning and `unit`. `MLType.toString` prints the components of `prod` with
      `protArrow`, which does not parenthesize products.
    - D2: the benchmark Makefile cannot compile the `.mli` of an `Array` result: its `%.cmi` rule runs
      `ocamlfind ocamlopt -package zarith -c build/<id>/<test>.mli` without `-I $(build)` and fails
      with `Unbound module LeanArray`. The same file compiles with `-I`.
    - D3: `String` is printed `string`, but nothing represents a Lean `String` as an OCaml string: a
      program returning `String.mk …` references axioms that `axioms.ml` does not implement
      (`malfunction cmx` fails with `Unbound value Axioms.def__String_mk`), and string literals
      become `□` (R-4).
    - A user inductive result type, the case raised on Zulip on Feb 10, still gets `unit` (R-17).
  - C2: the option exists and is `false` by default. With it on, the 20 natio benchmarks erased with
    `{remove_irrel_constr_args := true, auto_inline_typeclass_dispatch := true}` have the same `.ast`
    as without the option, up to hygienic suffixes (see below), and longer `.ast.inlinings`
    (binarytrees 3 to 19 entries, unionfind 16 to 37) that add instances and projection chains
    (`instHAdd`, `instAddNat`, `HAdd.hAdd`, `OfNat.ofNat`, …). `peregrine eval --attributes=…` of
    `binarytrees 4`, `triangle_rec 12`, `iflazy 7`, `even 9` and `const_fold 3` (Peano naturals,
    logical externs) gives 610, 66, 42, 0 and 22, the values of Lean's `#eval`, before the merge,
    after it, and with the option on. Remaining defects, all with the option on:
    - D5: unbounded code growth. The `.mlf` of unionfind grows from 126 374 to 14 510 809 bytes and
      peregrine's compile time from 0.04 s to 3.27 s (unionfind_noinline: 89 106 to 5 818 655 bytes);
      among the marked constants are the monad instances `Id.instMonad`,
      `UnionFind.StateT'.instMonad` and `UnionFind.ExceptT'.instMonad`. `e46224f` limited inlined
      instances to 40 erased nodes; `8db2dd9` removed that limit (`autoInlineMaxBodySize`,
      `LBTerm.size`) without saying so.
    - D6: repeated work. Every instance is marked, whatever its body. With
      `instance instTbl : Tbl := let s := slowSum 100000; ⟨fun i => s + i⟩` and
      `useTbl n := (List.range n).foldl (fun acc i => acc + Tbl.get i) 0`, the native `useTbl 1000`
      takes 0.007 s with the option off and 0.764 s with it on (`useTbl 3000`: 0.010 s and 2.257 s):
      `slowSum 100000` is recomputed at every use.
    - D7: the guard `!t.containsFix`, meant to refuse recursive bodies, never applies: `LBTerm.fix` is
      built only in the recursive branch of `erase.visitMutual`, and the guard is in the
      non-recursive branch.
    - D8: `@[noinline]` is ignored: `@[noinline] instance instBar : Inhabited Nat := ⟨42⟩` is logged
      `Auto-inlining typeclass instance instBar.` and listed in `.ast.inlinings`.
    - D9: the documentation does not match the code. The docstring of the option promises "a
      single-ctor structure literal whose fields are shallow", and that of `LBTerm.isTrivialAlias`
      "a single-ctor structure literal (the usual `Foo.mk arg₁ … argₙ` shape …)"; the code
      accepts `.construct _ 0 _` after stripping λs, which matches only argument-less constructors
      of index 0, since constructors are emitted in applied form, and it also accepts constant
      functions. With the option on, `fLit : Bool := false` and
      `kfun (_ : Nat) : Nat := seven` are marked; `tLit : Bool := true` and the structure literal
      `pLit : P := ⟨1, 2⟩` are not.
    - D10 (R-24): the benchmark Makefile cannot turn the option on, and it does not make the `.ast`
      smaller.
  - C3: the same `make` prints no warning 55. The Cmm of `nat.ml` and `int.ml` (`-dcmm`) is the same
    as before up to source locations: every Zarith call is still an out-of-line call
    (`app "camlZ__…"`, 12 in `nat.ml`, 8 in `int.ml`). D12 (R-26).
  - C4: the same experiment with the repository Makefile fails with the same peregrine error. With
    the prerequisite added, make now re-runs `lake lean` and builds `even.mlf`: the co-target is one
    half of the fix. Remaining defect:
    - D4: the `%.mlf` rules do not list `%.ast.inlinings` as a prerequisite, so make does not
      regenerate a missing `.ast.inlinings` before running peregrine.
  - C5: the same `.mlf`. Peregrine's inlining pass (MetaRocq 1.5.1 `EInlining.inline`, extracted to
    `peregrine-tool/_build/default/src/extraction/EInlining.ml:32-33`) does not rewrite `tCase`
    scrutinees, and `if n = 0` puts `instDecidableEqNat n 0` in one. D11 (R-25).
- **Effect on emitted .ast (corpus):** of 284 files, 214 are byte-identical and 70 `.ast` files
  differ only in hygienic binder names; all 116 `.ast.inlinings` and 52 `.mli` files are
  byte-identical. `scripts/corpus-diff.sh --normalize` reports 214 identical, 70 identical after
  normalization, 0 differing. Every difference is a suffix `_hyg.N` of a binder name (the `_alt`
  binders that `inlineMatchers` creates during erasure, and binders of definitions), whose number
  grows by the number of `config` clauses elaborated in the same file before the name was created:
  each `config` clause now takes one more macro scope, as `ErasureConfig` has one more field.
  - Benchmarks (the Makefile writes `config {remove_irrel_constr_args := true,}` for `prune` and
    `config {}` for `noprune`): in each variant 19 of the 20 `.ast` files differ, in 300 suffixes,
    all by +1; `iflazy.ast` has no hygienic name and is identical.
  - `examples/Defects` (7 `.ast` files) and `examples/PortProbe` (25): in a file written by the
    k-th `#erase` with a `config` clause, or by a later `#erase` without one, the suffixes grow by 0
    to k, and by k for the `_alt` binders created by that `#erase` (k is at most 22).
  - `examples/Scope`: identical.

  Without a `config` clause the output is unchanged: the 20 natio benchmarks erased with a bare
  `#erase <test> to "<test>.ast" mli "<test>.mli"` give byte-identical `.ast`, `.ast.inlinings` and
  `.mli` files (60) before and after the merge. Binder names carry no meaning in λ□, whose terms
  use de Bruijn indices. In the logs, the signature logged for `#erase "abc"` (no `mli` path)
  becomes `val main: string`, without the warning.
- **Regression test:**
  - `tests/regress/mli_types.lean` fails before (8 of its 9 `.mli` files differ) and passes after.
    It holds the eight signatures checked natively above, and `(Nat → Nat) → Nat`, printed
    `(Z.t -> Z.t) -> Z.t` before and after (checked natively too), which guards arrows in argument
    position. The cases of D1 to D3 are left to their fixes.
  - `tests/regress/auto_inline.lean` fails before (the option is not a field) and passes after. Its
    outputs `default.ast` and `default.ast.inlinings` are byte-identical to those of the code before
    the merge, `off.*` equals `default.*`, `on.ast` equals `default.ast`, and `on.ast.inlinings`
    adds six constants. With `PEREGRINE` set, `on3.ast` validates, and `default3.ast` and `on3.ast`
    evaluate to 3 with their inlinings.
  - `tests/regress/runtime_inlined_hint.lean` checks the runtime files instead of calling `#erase`.
    It fails before (`nat-inline.ml: 15 bare [@inlined] attribute(s)`) and, after, writes
    `nat-inline.ml: [@inlined hint] 15, [@inlined] 0` and `int-inline.ml: [@inlined hint] 9,
    [@inlined] 0`.
  - C4 has no test, as the co-target alone changes no observable behaviour; the fix of D4 adds one.
    C5 concerns peregrine and a file outside the repository.
  - `tests/regress/smoke.lean` passes with `fact3.ast` re-baselined (hygienic suffixes only); its
    other outputs and its peregrine outputs are unchanged.

## S-3: Nested products are parenthesized in the `.mli` signature

- **Commit:** the commit whose subject starts with `shipping(S-3):`
  (`git log --grep='^shipping(S-3):'`).
- **Files and functions:**
  - `LeanToLambdaBox/Erasure.lean`: `MLType.toString`, case `prod`: both components are printed
    with `protCtor`, which parenthesizes arrows and products, instead of `protArrow`, which
    parenthesizes only arrows.
  - `tests/regress/mli_types.lean`: docstring; new cases `rNestL`, `rNestR`, `rNestArg`; their 9
    expected outputs in `tests/regress/expected/mli_types/`.
  - `doc/SHIPPING-CHANGES.md`: this entry.
- **Why necessary:** defect D1 of S-2, reproduced on this branch. A product nested in a product is
  printed as an OCaml triple, while the erased value is a pair containing a pair, so an OCaml
  harness written against the `.mli` type-checks and then crashes or reads garbage without any
  warning. Before S-2 the same programs gave a warning and `unit`.
- **Behaviour before:** the programs `rNestL n := ((n, n + 1), n + 2)`,
  `rNestR n := (n, (n + 1, n + 2))`, `rNestArg (p : (Nat × Nat) × Nat) := p.1.1 + p.1.2 + p.2` and
  `rNestFun n : (Nat × Nat) × (Nat → Nat) := ((n, n + 1), (· + n))` are erased with
  `{remove_irrel_constr_args := true}` and compiled natively as for S-2 (peregrine with
  `unbox.config` after the R-1 rewrite, malfunction, OCaml 4.14.2 without flambda, the
  `via_malfunction` runtime objects), each linked with a harness written against its `.mli`:
  - `rNestL.mli` is `val main: Z.t -> Z.t * Z.t * Z.t`; the harness
    `let (a, b, c) = RNestL.main (Z.of_int 5)` prints a garbage number of about 235 digits (it
    varies between runs), then `7 3195`;
  - `rNestR.mli` is the same; its harness exits with status 139 (segmentation fault);
  - `rNestArg.mli` is `val main: Z.t * Z.t * Z.t -> Z.t`; the harness passing `(5, 6, 7)` exits
    with status 139;
  - `rNestFun.mli` is `val main: Z.t -> Z.t * Z.t * (Z.t -> Z.t)`; its harness exits with status 139.
- **Behaviour after:** the signatures are `val main: Z.t -> (Z.t * Z.t) * Z.t`,
  `val main: Z.t -> Z.t * (Z.t * Z.t)`, `val main: (Z.t * Z.t) * Z.t -> Z.t` and
  `val main: Z.t -> (Z.t * Z.t) * (Z.t -> Z.t)`. Harnesses written against them print `5 6 7`,
  `5 6 7`, `18` and `5 6 15` (the Lean values; the function is applied to 10). The harnesses of
  before no longer compile (`This expression has type (Z.t * Z.t) * Z.t but an expression was
  expected of type 'a * 'b * 'c`). The `.ast` and `.ast.inlinings` of these programs are
  byte-identical before and after, and products that are not nested print as before (`rPair`,
  `rFunPair` and `rListPair` of `tests/regress/mli_types.lean` are unchanged).
- **Effect on emitted .ast (corpus):** byte-identical for all 284 files (116 `.ast`,
  116 `.ast.inlinings`, 52 `.mli`); `scripts/corpus-diff.sh` against the corpus of S-2 reports 284
  identical. No corpus `.mli` contains a product: 51 are `val main: Z.t -> Z.t`, one is
  `val main: Z.t -> unit`.
- **Regression test:** `tests/regress/mli_types.lean`, cases `rNestL`, `rNestR` and `rNestArg`. It
  fails before (their 3 `.mli` files are `Z.t * Z.t * Z.t` forms) and passes after; the 27 outputs
  of its other cases are unchanged.

## S-4: The benchmark Makefile compiles a `.mli` that names `LeanArray`

- **Commit:** the commit whose subject starts with `shipping(S-4):`
  (`git log --grep='^shipping(S-4):'`).
- **Files and functions:**
  - `benchmarks/via_malfunction/Makefile`: pattern rule `$(build)/%.cmi` (new prerequisite
    `$(build)/LeanArray.cmi`; the command gains `-I $(build)`; one comment line added); new explicit
    rules `$(build)/decidable.cmi`, `$(build)/eq.cmi` and `$(build)/LeanArray.cmi`, each with the
    command the pattern rule gave it before (`$(OCAMLOPT) -c $<`), in place of the comments
    `# <module>.cmi handled by generic rule (no prerequisites)`.
  - new `tests/regress/makefile_cmi.lean` and `tests/regress/expected/makefile_cmi/cmi_commands.txt`.
  - `doc/SHIPPING-CHANGES.md`: this entry.
- **Why necessary:** defect D2 of S-2, reproduced on this branch. Since S-2 the eraser writes
  `Z.t LeanArray.array` for an `Array` in the `.mli`, but the Makefile compiles a generated `.mli`
  without `-I $(build)`, the directory that holds `LeanArray.cmi`, and without building
  `LeanArray.cmi` first; the build of a program with an `Array` in its signature stops there. The
  three explicit rules are needed because the pattern rule now depends on `LeanArray.cmi`, which
  would be a circular dependency for `LeanArray.cmi` itself; they keep the commands for these three
  runtime interfaces as they were.
- **Behaviour before:** reproduction: a fresh build directory `B` holds `rArr.ast`,
  `rArr.ast.inlinings` and `rArr.mli` written by
  `#erase rArr config {remove_irrel_constr_args := true} to ... mli ...` for
  `rArr (n : Nat) : Array Nat := Array.mk [n, n + 1]`; `rArr.mli` is
  `val main: Z.t -> Z.t LeanArray.array`. In `benchmarks/via_malfunction`,
  `make build=B FLAMBDA=0 MALFUNCTION_NO_FLAMBDA_SWITCH=peregrine ARRAYML=JCFArrayOCaml4.ml
  PEREGRINE=<wrapper applying the R-1 rewrite> -o B/rArr.mli -o B/rArr.ast -o B/rArr.ast.inlinings
  B/rArr.cmi` runs `ocamlfind ocamlopt -package zarith -c B/rArr.mli`, which fails with
  `Error: Unbound module LeanArray` (make exits with status 2). The target `B/rArr.cmx` fails the
  same way after running peregrine. There, `rArr.cmi` comes before `axioms.cmx`, the only target
  that leads to `LeanArray.cmi`, so adding `-I` alone would not be enough in a fresh directory.
- **Behaviour after:** the same `make ... B/rArr.cmi` copies `LeanArray.mli`, compiles
  `LeanArray.cmi`, then runs `ocamlfind ocamlopt -package zarith -I B -c B/rArr.mli`, and
  succeeds. `make ... B/rArr.cmx` succeeds too. After `make ... B/LeanArray.cmx`, the objects link
  with a harness written against `rArr.mli`
  (`LeanArray.def__Array_size (Obj.repr ()) (RArr.main (Z.of_int 5))`), which prints `2`, the size
  of `rArr 5 = #[5, 6]`. The benchmarks are unaffected: in a fresh build directory, `make -n` for
  the binary of `even` lists the same commands before and after, except `-I $(build)` in the
  compilation of `even.mli`; a real build of `even` with the options above gives byte-identical
  `even.mli` and `even.mlf`, and the binary prints 1, 0 and 1 for the inputs 0, 7 and 1000, before
  and after.
- **Effect on emitted .ast (corpus):** byte-identical for all 284 files, since the Makefile's
  erasure rules are unchanged; `scripts/corpus-diff.sh` against the corpus of S-3 reports 284
  identical.
- **Regression test:** `tests/regress/makefile_cmi.lean` erases `rArr` into a fresh build directory,
  asks `make -n` for the commands that build `rArr.cmi` there (with `OCAMLOPT=ocamlopt`, so it needs
  `make` but not OCaml), and writes them to `cmi_commands.txt`. It fails before
  (`LeanArray.cmi is not built before rArr.cmi`: the only command is
  `ocamlopt -c $(build)/rArr.mli`) and passes after, with the commands
  `cp LeanArray.mli $(build)/LeanArray.mli`, `ocamlopt -c $(build)/LeanArray.mli` and
  `ocamlopt -I $(build) -c $(build)/rArr.mli`.

## S-5: `String` is no longer printed as `string` in the `.mli` signature

- **Commit:** the commit whose subject starts with `shipping(S-5):`
  (`git log --grep='^shipping(S-5):'`).
- **Files and functions:**
  - `LeanToLambdaBox/Erasure.lean`: `MLType` (constructor `string` removed), `MLType.toString`
    (case `string` removed), `to_ml_type` (case `String` removed). These are the `String` parts of
    `94a429c`; the code for `String` is again that of `main`.
  - `tests/regress/mli_types.lean`: docstring; new case `rStr`; its 3 expected outputs in
    `tests/regress/expected/mli_types/`.
  - `doc/SHIPPING-CHANGES.md`: this entry; R-17 no longer lists `String` among the handled types;
    new R-27, a defect of the benchmark Makefile found while checking S-4.
- **Why necessary:** defect D3 of S-2, reproduced on this branch. The `.mli` states the OCaml
  representation of the value, and since S-2 it gave `string` for a Lean `String`, without a
  warning. Nothing in the pipeline represents a Lean `String` as an OCaml `string`: a string
  literal is erased to `□` after a panic (R-4), and the constructor `String.mk` and every `String`
  operation are `@[extern]` constants, erased to axioms that the benchmark runtime does not
  implement (R-21). A program that builds or inspects a string therefore cannot be linked, and one
  that does neither links whatever type the `.mli` gives. The signature `string` made an
  unfounded claim and removed the warning that says the type is not supported.

  Two fixes were possible. Implementing `String` would mean choosing an OCaml representation of
  Lean strings (UTF-8 bytes, or a list of code points as in `String.mk`), writing in the runtime
  `String.mk` and each `String`, `Char` and `UInt32` operation that a program uses, and erasing
  string literals (R-4). That is a new feature, which neither the verification goal nor any
  benchmark requires. The fix taken withdraws the claim: `String` goes back to the fallback path
  (warning and `unit`) that every type without a runtime representation takes (R-17).
- **Behaviour before:** reproduction: `rStr n := String.mk (List.replicate n (Char.ofNat 97))`,
  `strLen (s : String) : Nat := s.length`, `strId (s : String) : String := s` and the literal
  `"abc"`, erased with `{remove_irrel_constr_args := true}`, give the signatures
  `val main: Z.t -> string`, `val main: string -> Z.t`, `val main: string -> string` and
  `val main: string`, with no warning. `rStr.ast` has the axioms `String.mk`, `Char.ofNatAux`,
  `UInt32.ofBitVec`, `Nat.pow`, `Nat.decLt`, `Nat.beq` and `Nat.sub`, and `strLen.ast` has
  `String.length`. The literal becomes `(Untyped () (Some tBox))`, after
  `PANIC ... String literals not supported.` Compiled natively as for S-3, `rStr` fails in
  `malfunction cmx` with `Unbound value Axioms.def__String_mk`, and `strLen` with
  `Unbound value Axioms.def__String_length`. Only `strId`, which does not touch its argument,
  links: its harness passes `"abc"` and prints `abc`.
- **Behaviour after:** the four signatures are `val main: Z.t -> unit`, `val main: unit -> Z.t`,
  `val main: unit -> unit` and `val main: unit`, byte-identical to those of `main` (`58701f8`),
  and each `String` in them is reported with
  `warning: failed to translate String into ML type, emitting unit instead.` The `.ast` and
  `.ast.inlinings` files are byte-identical before and after. Linking still fails for `rStr` and
  `strLen`, since the program itself needs the missing axioms (R-21).
- **Effect on emitted .ast (corpus):** byte-identical for all 284 files; `scripts/corpus-diff.sh`
  against the corpus of S-4 reports 284 identical. No corpus `.mli` involves `String`. In the logs
  (`_meta/logs`, not part of the corpus), the signature logged for `#erase "abc"` in
  `tests/corpus/Defects.lean` becomes `val main: unit`, with the warning above, as on `main`.
- **Regression test:** `tests/regress/mli_types.lean`, case `rStr`, whose `#guard_msgs (warning)`
  requires the warning. It fails before (Lean reports that the `#guard_msgs` docstring does not
  match: no warning is produced) and passes after, with `rStr.mli` equal to
  `val main: Z.t -> unit`; the outputs of the other cases are unchanged.

## S-6: The benchmark Makefile regenerates a missing `.ast.inlinings` before running peregrine

- **Commit:** the commit whose subject starts with `shipping(S-6):`
  (`git log --grep='^shipping(S-6):'`).
- **Files and functions:**
  - `benchmarks/via_malfunction/Makefile`: the `INLINING=1` pattern rule `$(build)/%.mlf` gains the
    prerequisite `$(build)/%.ast.inlinings`, and a comment line above the `ifeq` says why; its
    command is unchanged. The `INLINING=0` rule is unchanged.
  - new `tests/regress/makefile_inlinings.lean` and
    `tests/regress/expected/makefile_inlinings/mlf_commands.txt`.
  - `doc/SHIPPING-CHANGES.md`: this entry; new R-28, found while running the new test with GNU
    make 4.3.
- **Why necessary:** defect D4 of S-2 (claim C4), reproduced on this branch. With `INLINING=1` the
  rule for `%.mlf` runs `peregrine compile %.ast <config> --attributes=%.ast.inlinings`, but its
  only prerequisite is `%.ast`. Since `94a429c`, `%.ast.inlinings` is a target of the rule that
  runs `lake lean`, so make knows how to rebuild it, but make rebuilds a file only when a target
  depends on it. When the `.ast` is present and up to date and the `.ast.inlinings` is missing
  (for instance in a build directory filled by a frontend that did not write the file yet, the
  situation of the Zulip report of Feb 17), make runs peregrine on a missing file. The target
  added by `94a429c` is what makes the new prerequisite possible: without it, as at `a104486`,
  the prerequisite gives `No rule to make target` (Zulip, Feb 13).
- **Behaviour before:** reproduction: in `benchmarks/via_malfunction`, with the options
  `FLAMBDA=0 MALFUNCTION_NO_FLAMBDA_SWITCH=peregrine ARRAYML=JCFArrayOCaml4.ml
  PEREGRINE=<wrapper applying the R-1 rewrite>` (build directory `build/7ee730d2`),
  `make build/7ee730d2/even.mlf` succeeds from scratch. After deleting `even.ast.inlinings` and
  `even.mlf`, the same command runs peregrine alone, which fails with
  `peregrine: option '--attributes': invalid element in list (build/7ee730d2/even.ast.inlinings):
  no build/7ee730d2/even.ast.inlinings file or directory`, and make exits with status 2: the error
  reported on Zulip on Feb 17. Every later run fails the same way, and so does `make bin/even`,
  until the file is restored by hand.
- **Behaviour after:** the same command first runs `lake lean build/7ee730d2/even.lean`, which
  rewrites `even.ast`, `even.ast.inlinings` and `even.mli`, then runs peregrine, and succeeds; the
  next run prints `make: 'build/7ee730d2/even.mlf' is up to date.` With `even.ast.inlinings`
  deleted, `make bin/even` erases, compiles and links, and the binary prints 1, 0 and 1 for the
  inputs 0, 7 and 1000. The regenerated `even.ast` and `even.mli` are byte-identical to those of a
  build from scratch. In a fresh build directory, `make -n bin/even` lists the same commands before
  and after, with `INLINING=1` and with `INLINING=0`.
- **Effect on emitted .ast (corpus):** byte-identical for all 284 files, since the erasure rule is
  unchanged; `scripts/corpus-diff.sh` against the corpus of S-5 reports 284 identical.
- **Regression test:** `tests/regress/makefile_inlinings.lean` erases `rInl` into a fresh build
  directory and asks `make -n` for the commands that build `rInl.mlf` there, with
  `PEREGRINE=peregrine` and the generated `rInl.lean` taken as old (`-o`), so it needs `make` but
  neither peregrine nor OCaml. With every output present, the only command is peregrine's. With
  `rInl.ast.inlinings` deleted, `lake lean $(build)/rInl.lean` comes before it. With the file
  deleted and `INLINING=0`, the only command is peregrine's, without `--attributes`. The three
  lists are written to `mlf_commands.txt`. Before, the second list is the peregrine command alone
  and the test fails with `rInl.ast.inlinings missing: expected the lake lean command before the
  peregrine command`; after, it passes with GNU make 4.4.1 and with make 4.3.

## S-7: Auto-inlining marks a constant only if its inlined body is small

- **Commit:** the commit whose subject starts with `shipping(S-7):`
  (`git log --grep='^shipping(S-7):'`).
- **Files and functions:**
  - `LeanToLambdaBox/Basic.lean`: `ModPath` and `Kername` also derive `BEq` and `Hashable`, so that
    kernames can key a hash map.
  - `LeanToLambdaBox/Erasure.lean`: `ErasureState` (new field `inlinedSizes`); `ErasureConfig`
    (docstring of `auto_inline_typeclass_dispatch`); new `autoInlineMaxSize` (40) and
    `LBTerm.inlinedSize`; `erase.visitMutual`: in the non-recursive branch, the inlined size of the
    erased body is computed and recorded for an `@[inline]` constant, and a constant that the option
    would mark is marked only if its inlined size is at most `autoInlineMaxSize`, with a log message
    that gives the size or the refusal; in the recursive branch, the inlined size of the fixpoint of
    an `@[inline]` constant is recorded.
  - new `tests/regress/auto_inline_size.lean`, its expected outputs
    `tests/regress/expected/auto_inline_size/` (8 files) and
    `tests/regress/expected-peregrine/auto_inline_size/` (4 files).
  - `doc/SHIPPING-CHANGES.md`: this entry.
- **Why necessary:** defect D5 of S-2, reproduced on this branch. With the option on, every instance
  and every trivial alias is marked, whatever its size. Peregrine's inlining pass (MetaRocq
  `EInlining.inline_env`) replaces each use of a marked constant by its body, into which the marked
  constants were already inlined, so the code grows without bound. `e46224f` limited the erased
  body of an instance to 40 nodes; `8db2dd9` removed the limit. A limit on the erased body alone
  does not bound the growth either: in a chain of instances where each one calls the method of the
  previous one twice, every body has at most 12 nodes, and the inlined code doubles at each level
  (see below). The limit is therefore put on what Peregrine substitutes: the body with the marked
  constants, including `@[inline]` ones, inlined into it (`LBTerm.inlinedSize`). The bound 40 is
  the value of `e46224f`. On the 20 benchmarks, every constant still marked measures at most 38
  and every refused one at least 140, so any bound from 38 to 139 marks the same constants.
- **Behaviour before:** reproduction: the 20 `natio` benchmarks are erased with
  `config {remove_irrel_constr_args := true, auto_inline_typeclass_dispatch := true}` (source file
  elaborated with `lake env lean` in `benchmarks/via_malfunction`), and each `.ast` is compiled with
  `peregrine compile <t>.ast unbox.config --attributes=<t>.ast.inlinings` after the R-1 rewrite.
  - unionfind: 37 constants are marked, among them `UnionFind.StateT'.instMonad` and
    `UnionFind.ExceptT'.instMonad`. The `.mlf` has 14 510 809 bytes (126 374 with the option off)
    and peregrine takes 3.34 s (0.05 s). The benchmark Makefile (`FLAMBDA=0`, switch `peregrine`,
    OCaml 4.14.2, `ARRAYML=JCFArrayOCaml4.ml`, the given `.ast` files) builds the binary in 15.2 s
    (0.9 s), and the binary has 36 297 424 bytes (2 972 176). unionfind_noinline: 5 818 655 bytes
    (89 106).
  - `tests/regress/auto_inline_size.lean` (option on): `instMonadSt`, a `Monad` instance, and the
    four instances `i0` to `i3` of the chain are marked; `chain.mlf` has 3 208 bytes and
    `twice.mlf` 20 223. With the chain extended to eleven levels (`j0` to `j10`, each calling the
    previous method twice), all eleven are marked, and the `.mlf` of a program calling level 3, 6 or
    10 has 3 208, 26 332 or 425 747 bytes.
- **Behaviour after:** same reproduction.
  - unionfind: 35 constants are marked; the two monad instances are refused (inlined sizes 881 and
    1 098). The `.mlf` has 129 332 bytes, peregrine takes 0.05 s, the Makefile builds the binary in
    0.8 s, and the binary has 2 900 376 bytes. unionfind_noinline: 88 726 bytes, without its two
    monad instances. In qsort, qsort_fin and qsort_single, `Array.instGetElem?NatLtSize` (140) and
    `Vector.instGetElemNatLt` (146) are no longer marked (qsort `.mlf`: 34 933 to 34 583 bytes). The
    other 15 benchmarks mark the same constants as before, and their `.mlf` files are identical.
  - The binaries print the same results. Running times, minimum of 5 runs, with the option off /
    on before / on after: binarytrees 17: 0.75 / 0.38 / 0.39 s; qsort 1000: 0.51 / 0.36 / 0.37 s;
    triangle_rec 10000000 (with `ulimit -s unlimited`): 7.51 / 0.109 / 0.107 s; unionfind 100000:
    0.75 / 0.37 / 0.72 s. The speedup of unionfind came from inlining its two monad instances, at
    the price of the code growth above; it is lost. The other speedups are kept.
  - `tests/regress/auto_inline_size.lean`: `instMonadSt` is refused (inlined size 453); `i0`, `i1`
    and `i3` are marked (8, 30 and 16) and `i2` is refused (74), after which `i3` refers to `i2`
    without inlining it. `chain.mlf` has 1 416 bytes and `twice.mlf` 7 892. In the eleven-level
    chain, `j0` and the odd levels are marked, and the three programs give 1 416, 2 292 and 3 468
    bytes.
  - `peregrine eval` of `chain 2` and `(twice 3).1` under Peano naturals, with their inlinings,
    gives 10 and 7, before and after.
  - Each decision is logged, for example `Auto-inlining typeclass instance i1 (inlined size 30).`
    and `Not auto-inlining typeclass instance i2: inlined size 74 exceeds 40.`
  - The bound concerns Peregrine's inlining pass. Its beta-reduction pass (MetaRocq `EBeta.betared`)
    then substitutes the arguments of an inlined λ into its body, which copies an argument once per
    occurrence of the bound variable.
- **Effect on emitted .ast (corpus):** byte-identical for all 284 files; `scripts/corpus-diff.sh`
  against the corpus of S-6 reports 284 identical. The corpus does not turn the option on, and the
  `.ast.inlinings` of other configurations lists only `@[inline]` constants, which this change
  does not affect. With the option on (outside the corpus), the 20 benchmark `.ast` files are
  byte-identical before and after, and only the `.ast.inlinings` files of the five benchmarks named
  above change, each losing the constants named above.
- **Regression test:** `tests/regress/auto_inline_size.lean` erases `twice` and `chain` with the
  option on, and `(twice 3).1` and `chain 2` under Peano naturals. It fails before
  (`chain.ast.inlinings` and `chain2.ast.inlinings` list `i2`, and `twice.ast.inlinings` and
  `twice3.ast.inlinings` list `instMonadSt`) and passes after. With `PEREGRINE` set, `chain2.ast`
  and `twice3.ast` validate and evaluate to 10 and 7.

## S-8: Auto-inlining marks only constants whose erased body is a value

- **Commit:** the commit whose subject starts with `shipping(S-8):`
  (`git log --grep='^shipping(S-8):'`).
- **Files and functions:**
  - `LeanToLambdaBox/Erasure.lean`: new `LBTerm.isValue` (with its auxiliary
    `LBTerm.isValue.isConstructorApp`); `ErasureConfig` (docstring of
    `auto_inline_typeclass_dispatch`); `erase.visitMutual`: in the non-recursive branch, a constant
    that the option would mark is not marked if its erased body is not a value, with a log message.
  - new `tests/regress/auto_inline_values.lean`, its expected outputs
    `tests/regress/expected/auto_inline_values/` (4 files) and
    `tests/regress/expected-peregrine/auto_inline_values/` (2 files).
  - `doc/SHIPPING-CHANGES.md`: this entry.
- **Why necessary:** defect D6 of S-2, reproduced on this branch. The option marks an instance
  whatever its body. The compiled program evaluates a top-level constant once; once the constant is
  inlined, its body is evaluated at every use, so a body that computes is computed again each time.
  The bound of S-7 does not prevent this, since a small body can start a long computation. The
  example of S-2, `instTbl` (`let s := slowSum 100000; ⟨fun i => s + i⟩`), is refused by that bound
  (inlined size 75), but smaller bodies of the same kind are marked. The fix marks a constant only if
  its erased body is a value (`LBTerm.isValue`): a λ, □, a primitive, a constant, or a constructor
  applied to such values. Evaluating such a body at each use repeats no computation other than
  building it. A constant counts as a value because it refers to a top-level definition, which the
  compiled program evaluates once.
- **Behaviour before:** reproduction: `slowSum : Nat → Nat` adds `n + (n-1) + … + 1` by recursion,
  `instSlow : Inhabited Nat := ⟨slowSum 100000⟩` with
  `useSlow n := (List.range n).foldl (fun acc _ => acc + (default : Nat)) 0`, and
  `instLet : Tbl := let s := slowSum 100000; ⟨Nat.add s⟩` (with `class Tbl where get : Nat → Nat`)
  with `useLet n := (List.range n).foldl (fun acc i => acc + Tbl.get (self := instLet) i) 0`. Both
  programs are erased with
  `config {remove_irrel_constr_args := true, auto_inline_typeclass_dispatch := true}` and built
  natively as for S-7 (benchmark Makefile, `FLAMBDA=0`, OCaml 4.14.2, peregrine after the R-1
  rewrite).
  - `instSlow` and `instLet` are marked (inlined sizes 26 and 28).
  - `useSlow 1000` takes 0.64 s and `useSlow 3000` 1.85 s; `useLet 1000` takes 0.68 s and
    `useLet 3000` 2.05 s. `slowSum 100000` is computed once per list element.
  - Benchmarks with the option on (as for S-7): qsort, qsort_fin and qsort_single mark `instMinNat`
    and `Nat.instMax` (inlined size 25), whose bodies are the applications `minOfLe …` and
    `maxOfLe …` that build a dictionary.
- **Behaviour after:** same reproduction.
  - `instSlow` and `instLet` are not marked, with the log messages
    `Not auto-inlining typeclass instance instSlow: its body is not a value.` and the same for
    `instLet`.
  - `useSlow 1000` and `useSlow 3000` take 0.006 s each, and `useLet` 0.004 s and 0.005 s. The
    printed results are unchanged: 5000050000000 and 15000150000000 for `useSlow`, 5000050499500 and
    15000154498500 for `useLet`.
  - Benchmarks: `instMinNat` and `Nat.instMax` are no longer marked, in the three qsort benchmarks
    only (47 to 45, 52 to 50 and 46 to 44 marked constants; qsort `.mlf` 34 583 to 34 009 bytes).
    Running times, minimum of 5 runs, before / after: qsort 1000: 0.371 / 0.369 s; qsort_fin 1000:
    0.382 / 0.385 s; qsort_single 100000: 0.179 / 0.177 s; the results are unchanged. The other 17
    benchmarks mark the same constants, and their `.mlf` files are identical.
- **Effect on emitted .ast (corpus):** byte-identical for all 284 files; `scripts/corpus-diff.sh`
  against the corpus of S-7 reports 284 identical. The corpus does not turn the option on. With the
  option on (outside the corpus), the 20 benchmark `.ast` files are byte-identical before and after,
  and only the `.ast.inlinings` files of qsort, qsort_fin and qsort_single change, each losing
  `instMinNat` and `Nat.instMax`.
- **Regression test:** `tests/regress/auto_inline_values.lean` erases `useAll`, which uses
  `instSlow`, `instLet` and `instLam` (`⟨fun i => slowSum i⟩`, a value), with the option on, and
  `useAll 2` under Peano naturals. It fails before (`useAll.ast.inlinings` lists `instSlow` and
  `instLet`) and passes after, where only `instLam` of the three is listed. With `PEREGRINE` set,
  `useAll2.ast` validates and evaluates to 25.

## S-9: The dead `containsFix` guard of auto-inlining is removed

- **Commit:** the commit whose subject starts with `shipping(S-9):`
  (`git log --grep='^shipping(S-9):'`).
- **Files and functions:**
  - `LeanToLambdaBox/Erasure.lean`: `LBTerm.containsFix` removed; `erase.visitMutual`: the condition
    `!t.containsFix` of the auto-inline step and its comment removed, and the comment now says that
    recursive definitions are never marked; `ErasureConfig`: the paragraph of the docstring of
    `auto_inline_typeclass_dispatch` about `LBTerm.fix` is replaced by one that says that only
    non-recursive definitions are considered.
  - new `tests/regress/auto_inline_recursive.lean`, its expected outputs
    `tests/regress/expected/auto_inline_recursive/` (4 files) and
    `tests/regress/expected-peregrine/auto_inline_recursive/` (2 files).
  - `doc/SHIPPING-CHANGES.md`: this entry.
- **Why necessary:** defect D7 of S-2, confirmed on this branch. `8db2dd9` added the guard
  `!t.containsFix`, documented as refusing to inline recursive bodies, in the non-recursive branch
  of `erase.visitMutual`. The term `t` there is the result of `visitExpr`, and `LBTerm.fix` is built
  only in the recursive branch of `erase.visitMutual` (the declaration `.fix defs i`), so `t` never
  contains one and the guard never applies. Recursive definitions were never candidates, since the
  auto-inline step exists only in the non-recursive branch. The guard and its documentation
  described a protection that the code gets elsewhere, and they suggested that a body calling a
  recursive function is refused, which it is not (it contains a constant, not a fixpoint). The
  change removes the dead code and states where the protection comes from.
- **Behaviour before:** reproduction: `tests/regress/auto_inline_recursive.lean` with the option on.
  `depthInst : (n : Nat) → Depth n`, recursive and declared an instance with `attribute [instance]`,
  is erased to a fixpoint and is not marked; `instSum : Tbl := ⟨fun i => sumTo i⟩`, which calls the
  recursive `sumTo`, is marked (inlined size 6). A copy of the eraser at the commit of S-8 that logs
  every non-recursive body for which `containsFix` holds logs nothing on the corpus examples, the
  nine regression tests and the 20 benchmarks erased with the option on (164 `.ast` files, 88 of
  them with a fixpoint).
- **Behaviour after:** the same: outputs and log messages of the test above are byte-identical, and
  so are the `.ast`, `.ast.inlinings` and `.mlf` files of the 20 benchmarks erased with the option
  on. With `PEREGRINE` set, `useBoth 2` evaluates to 6 under Peano naturals, before and after.
- **Effect on emitted .ast (corpus):** byte-identical for all 284 files; `scripts/corpus-diff.sh`
  against the corpus of S-8 reports 284 identical.
- **Regression test:** the change does not alter behaviour, so no test fails before it.
  `tests/regress/auto_inline_recursive.lean` guards what the removed guard claimed and what holds
  without it: with the option on, a recursive instance (`depthInst`) is not marked, and a
  non-recursive instance that calls a recursive function (`instSum`) is marked. It passes before and
  after.

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

- **What:** `to_ml_type` handles `Nat`, `Int`, `Unit`/`PUnit`, `Bool`, `List`, `Option`, `Array`,
  `Prod` and arrows; any other type, for instance a user inductive or `String` (S-5), is reported
  with a warning and printed as `unit`, which does not describe the value. The file has no final
  newline.
- **Where:** `LeanToLambdaBox/Erasure.lean`: `to_ml_type`, `gen_mli`, `eraseElab`.
- **Reproduction:** `mli_fallback.mli` (`toMy : Nat → MyNat`, a user inductive) is
  `val main: Z.t -> unit`, with the warning
  `failed to translate Defects.MyNat into ML type, emitting unit instead`.
- **Impact:** an OCaml harness written against such a signature is type-unsound.
- **Why not fixed:** not required by the verification goal unless it later becomes required.

### R-18: The benchmark Makefile does not re-erase after a frontend change

- **What:** the rule that produces `%.ast`, `%.ast.inlinings` and `%.mli` depends on the generated
  `.lean` file and on `../FromLeanCommon*`, not on the frontend sources. A build directory keeps the
  outputs of the frontend that first produced them.
- **Where:** `benchmarks/via_malfunction/Makefile`: rule
  `$(build)/%.ast $(build)/%.ast.inlinings $(build)/%.mli: $(build)/%.lean ../FromLeanCommon.lean ../FromLeanCommon/`.
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

### R-24: Auto-inlining cannot be turned on in the benchmarks and does not shrink the `.ast`

- **What:** `ErasureConfig.auto_inline_typeclass_dispatch` (defect D10 of S-2) is off by default,
  and the benchmark Makefile has no variable for it: the only way is to override `ERASURE_CONFIG`
  on the `make` command line, which also replaces the `remove_irrel_constr_args` setting that
  `PRUNE_CONSTRUCTORS` adds. Commit `94a429c` expected the option to "shrink the AST bloat from
  typeclass dispatch" (2 to 4 times); the option changes only `.ast.inlinings`, not the `.ast`, and
  the constants it marks are shrunk only by peregrine's inlining, which keeps their declarations.
- **Where:** `LeanToLambdaBox/Erasure.lean`: `ErasureConfig.auto_inline_typeclass_dispatch`,
  `erase.visitMutual`; `benchmarks/via_malfunction/Makefile` (`ERASURE_CONFIG`).
- **Reproduction:** `tests/regress/auto_inline.lean`: `on.ast` equals `default.ast`, and only
  `on.ast.inlinings` differs. `grep -rn auto_inline benchmarks/` finds nothing.
- **Impact:** informational: the option has no effect on any benchmark, and the size of the emitted
  program is unchanged.
- **Why not fixed:** not a defect of the eraser's output. A benchmark switch is a feature of the
  benchmark pipeline that the verification goal does not require.

### R-25: The inlining diagnosis note is not committed, and its candidate causes are wrong

- **What:** commit `94a429c` lists `references/inlining_diagnosis.md` (defect D11 of S-2) among its
  changes, but `references/.gitignore` (`*`) excludes the file and no commit contains it. The note's
  conclusion holds: the kername of `instDecidableEqNat` is the same in its call sites, its
  declaration and the `.ast.inlinings` file, so the symptom of Zulip (Feb 17: the constant is listed
  but not inlined) lies in peregrine. Its three candidate causes (phase ordering, a filter on
  λ-shaped bodies, an allow-list) and its statement that inlining removes the declaration are wrong.
  Peregrine's inlining pass, MetaRocq 1.5.1 `EInlining.inline`, does not rewrite `tCase`
  scrutinees, and `if n = 0` puts `instDecidableEqNat n 0` in a scrutinee; inlining keeps all
  declarations. MetaRocq changed the `tCase` case to inline the scrutinee in commit `6b4d5ebc`
  (`erasure/theories/EInlining.v:30`), on its `9.1` branch and in no release; peregrine requires
  `rocq-metarocq-erasure-plugin` 1.5.1.
- **Where:** `references/inlining_diagnosis.md` (ignored, not in the repository);
  `peregrine-tool/_build/default/src/extraction/EInlining.ml:32-33` (extracted from MetaRocq 1.5.1
  `EInlining.v`).
- **Reproduction:** `git log --all -- references/inlining_diagnosis.md` prints nothing, and
  `git check-ignore -v references/inlining_diagnosis.md` prints `references/.gitignore:1:*`. For the
  program `scr` of S-2 (claim C5), compiled with
  `peregrine compile scr.ast unbox.config --attributes=scr.ast.inlinings`, the `.mlf` keeps
  `(let ($discr (apply $def__instDecidableEqNat $n …)) (switch $discr …))` in `isZeroIf`, while the
  call outside a scrutinee, in `isZeroDec`, becomes `$def__Nat_decEq`.
- **Impact:** informational: a constant marked for inlining that occurs in the scrutinee of a
  `match` or `if`, such as `instDecidableEqNat`, stays a call in the compiled code.
- **Why not fixed:** the cause is in peregrine's MetaRocq dependency, outside this repository, and
  the note is not part of the repository.

### R-26: `[@inlined hint]` silences warning 55 without inlining anything

- **What:** the Zarith calls of `nat-inline.ml` and `int-inline.ml` carry `[@inlined hint]` (defect
  D12 of S-2). With OCaml 4.14.2 without flambda, the generated code is the same as with `[@inlined]`:
  every Zarith call stays an out-of-line call; only warning 55
  (`Cannot inline: Function information unavailable`) is no longer printed. The question of Zulip
  (Feb 17) whether these inlinings work has the answer no, for this compiler, and the warning that
  showed it is gone.
- **Where:** `benchmarks/via_malfunction/nat-inline.ml`, `benchmarks/via_malfunction/int-inline.ml`.
- **Reproduction:** in `benchmarks/via_malfunction`,
  `make build/<id>/axioms.cmx FLAMBDA=0 MALFUNCTION_NO_FLAMBDA_SWITCH=peregrine ARRAYML=JCFArrayOCaml4.ml`
  prints warning 55 20 times before S-2 and never after. Compiling the copied `nat.ml` and `int.ml`
  with `ocamlfind ocamlopt -package zarith -c -dcmm` gives the same Cmm before and after up to
  source locations, with 12 and 8 calls `app "camlZ__…"`.
- **Impact:** informational: no change in the generated code.
- **Why not fixed:** not a defect: the change does what its commit message says.

### R-27: The benchmark Makefile builds `axioms.cmx` without waiting for `LeanArray.cmx`

- **What:** `axioms.ml` contains `include LeanArray`, but the rule for `$(build)/axioms.cmx` lists
  `nat.cmx`, `int.cmx` and `eq.cmx` as prerequisites, not `LeanArray.cmx`. When `axioms.cmx` is
  compiled before `LeanArray.cmx`, OCaml prints `Warning 58 [no-cmx-file]: no cmx file was found in
  path for module LeanArray, and its interface was not compiled with -opaque` and compiles
  `axioms.cmx` without the optimization information of `LeanArray`.
- **Where:** `benchmarks/via_malfunction/Makefile`: rule `$(build)/axioms.cmx`.
- **Reproduction:** in `benchmarks/via_malfunction`, with a build directory `B` that does not exist
  yet, `make build=B FLAMBDA=0 MALFUNCTION_NO_FLAMBDA_SWITCH=peregrine ARRAYML=JCFArrayOCaml4.ml
  B/axioms.cmx` prints the warning. The target `B/<test>.cmx` in a fresh directory prints it too.
- **Impact:** a serial build of `bin/<test>` is not affected, since the link rule lists
  `LeanArray.cmx` before `axioms.cmx`. A parallel build (`make -j`), or a build of `axioms.cmx` or
  `<test>.cmx` on its own, can compile `axioms.cmx` without cross-module information for
  `LeanArray`. That can change the machine code, and so the timings, of programs that use `Array`,
  not their results.
- **Why not fixed:** not required by the verification goal unless it later becomes required; it
  concerns the build of the benchmark runtime, not the emitted programs.

### R-28: The benchmark Makefile needs GNU make 4.4 and does not say so

- **What:** `benchmarks/via_malfunction/Makefile` uses two features that are new in GNU make 4.4:
  the function `$(let ...)` in `register_test`, and the special target `.NOTINTERMEDIATE`. Older
  versions do not reject them. There `$(let ...)` expands to nothing, so the variable `benches` is
  empty and no rule `$(build)/<test>_main.ml` exists; and `.NOTINTERMEDIATE` is an ordinary target,
  so a file that make creates through a chain of pattern rules is removed as an intermediate file
  at the end of the run. Neither the Makefile nor `benchmarks/via_malfunction/README.md` states the
  requirement.
- **Where:** `benchmarks/via_malfunction/Makefile`: `define register_test` and `.NOTINTERMEDIATE:`;
  `benchmarks/via_malfunction/README.md`.
- **Reproduction:** with GNU make 4.3, in `benchmarks/via_malfunction`,
  `make -n FLAMBDA=0 MALFUNCTION_NO_FLAMBDA_SWITCH=peregrine ARRAYML=JCFArrayOCaml4.ml build=B
  bin=C C/even` stops with `No rule to make target 'C/even'`, where make 4.4.1 lists the whole
  build; `make -p` shows `benches :=` empty with make 4.3 and 20 programs with make 4.4.1. In the
  setting of `tests/regress/makefile_inlinings.lean`, make 4.3 ends the run with
  `rm $(build)/rInl.ast.inlinings`: the file regenerated for peregrine is removed again.
- **Impact:** low. With make older than 4.4 the benchmark binaries cannot be built, and the
  message does not name the cause. The dry-run tests `makefile_cmi` and `makefile_inlinings` pass
  with make 4.3, the version on CI's `ubuntu-latest`.
- **Why not fixed:** not required by the verification goal unless it later becomes required.
