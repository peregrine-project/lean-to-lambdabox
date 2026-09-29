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
  outputs with `#erase ... to "<file>"`. A file must elaborate without error; an `#erase` that fails
  is wrapped in `#guard_msgs`, which pins its error, and writes no file.
  - `PortProbe.lean`: Nat functions, a Prop-carrying argument, a subtype, a structure with a Prop
    field, wildcard matches, derived `BEq`/`DecidableEq` (3 and 10 constructors); each erased with
    the default configuration, with constructor pruning, and applied to a literal under
    `{nat := .peano, extern := .preferLogical}`.
  - `Scope.lean`: programs with no inductive type in their dependency closure (Church numerals and
    booleans, polymorphic combinators, proof and type arguments, `let` of values, types and proofs,
    universe polymorphism, a Prop-typed axiom used as an argument).
  - `Defects.lean`: reproductions of the `R-<n>` entries below.
  - `Examples.lean`, `Names.lean`, `NearMiss.lean`: the example programs of the scope note
    (checkpoint 1). `Examples.lean` has 61 programs without an inductive type in their dependency
    closure (Church numerals and booleans, universe-polymorphic combinators at `Sort 2`, `Sort 1`
    and `Prop`, type and type-former arguments, sort and type aliases, proof arguments by axiom,
    theorem and λ, `let` and `have`, an opaque, `@[implemented_by]`, `@[inline]` and
    `@[macro_inline]`, a `Prop` alias made `@[irreducible]`, relevant axioms) and 48 readouts, which
    apply such a program to `Nat`, `Nat.succ`, `Nat.zero` (or `Bool`, `true`, `false`).
    `Names.lean` has 7 programs of the same kind whose constant names need escaping or collide as
    kernames, and 2 readouts. `NearMiss.lean` has 8 programs that each add one feature outside
    that fragment (a literal, a projection, a match, structural recursion, a quotient, a
    `partial def`, a term metavariable, a universe metavariable), and 2 readouts. Each program is
    erased under `{nat := .peano}` to `<name>.peano.ast` and under the default configuration to
    `<name>.default.ast`; each readout under `{nat := .peano}` only.
  - `IrrAlias.lean`: 3 programs without an inductive type whose types are propositions or Π-types
    only through an `@[irreducible]` alias, erased as the programs of `Examples.lean`.
  - `UnsafeRec.lean`: 3 programs without an inductive type that use `unsafe` recursion (a recursive
    constant, a two-member mutual block, a recursive constant whose value is not a λ), erased as
    the programs of `Examples.lean`.

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

## S-10: Auto-inlining does not mark constants tagged `@[noinline]`

- **Commit:** the commit whose subject starts with `shipping(S-10):`
  (`git log --grep='^shipping(S-10):'`).
- **Files and functions:**
  - `LeanToLambdaBox/Erasure.lean`: `erase.visitMutual` (new local `leanNoinline`, read from
    `Compiler.getInlineAttribute?`; in the non-recursive branch, a constant that the option would
    mark is not marked if it is tagged `@[noinline]`, with a log message); `ErasureConfig`
    (docstring of `auto_inline_typeclass_dispatch`).
  - new `tests/regress/auto_inline_noinline.lean`, its expected outputs
    `tests/regress/expected/auto_inline_noinline/` (4 files) and
    `tests/regress/expected-peregrine/auto_inline_noinline/` (2 files).
  - `doc/SHIPPING-CHANGES.md`: this entry.
- **Why necessary:** defect D8 of S-2, reproduced on this branch. `@[noinline]` is the user's
  request that a definition not be inlined. `erase.visitMutual` consulted only `@[inline]` and
  `@[always_inline]`, so the option marked a `@[noinline]` instance or alias like any other, and
  Peregrine inlined it. The example of S-2, `@[noinline] instance instBar : Inhabited Nat := ⟨42⟩`,
  is no longer marked since S-8, because the literal `42` is erased to an application of
  `OfNat.ofNat`, which is not a value; the reproduction below uses bodies that are values.
- **Behaviour before:** reproduction: `tests/regress/auto_inline_noinline.lean`, which declares
  `@[noinline] instance instNo : OpNo := ⟨fun n => n.succ⟩` and
  `@[noinline] def addNo : Nat → Nat → Nat := Nat.add`, and the same without the attribute
  (`instYes`, `addYes`), and erases `useAll n := addNo (OpNo.op n) (addYes (OpYes.op n) n)` with
  the option on. `useAll.ast.inlinings` lists `instNo` and `addNo`, and the log says
  `Auto-inlining typeclass instance instNo (inlined size 6).` and
  `Auto-inlining trivial alias addNo (inlined size 1).`
- **Behaviour after:** `instNo` and `addNo` are not listed, and the log says
  `Not auto-inlining typeclass instance instNo: it is tagged @[noinline].` and the same for
  `addNo`; `instYes` and `addYes` are still listed. The `.ast` files are byte-identical. With
  `PEREGRINE` set, `useAll 2` evaluates to 8 under Peano naturals, before and after. The 20
  benchmarks erased with the option on give byte-identical `.ast` and `.ast.inlinings` files: none
  of their candidates is tagged `@[noinline]`.
- **Effect on emitted .ast (corpus):** byte-identical for all 284 files; `scripts/corpus-diff.sh`
  against the corpus of S-9 reports 284 identical. The corpus does not turn the option on.
- **Regression test:** `tests/regress/auto_inline_noinline.lean` fails before (`useAll.ast.inlinings`
  and `useAll2.ast.inlinings` list `instNo` and `addNo`) and passes after.

## S-11: The documentation of auto-inlining describes the shapes the code accepts

- **Commit:** the commit whose subject starts with `shipping(S-11):`
  (`git log --grep='^shipping(S-11):'`).
- **Files and functions:**
  - `LeanToLambdaBox/Erasure.lean`: docstrings of `ErasureConfig.auto_inline_typeclass_dispatch`
    (the list of candidates), `LBTerm.isTrivialAlias` and `LBTerm.stripLambdas`. No code changes.
  - new `tests/regress/auto_inline_shapes.lean`, its expected outputs
    `tests/regress/expected/auto_inline_shapes/` (4 files) and
    `tests/regress/expected-peregrine/auto_inline_shapes/` (2 files).
  - `doc/SHIPPING-CHANGES.md`: this entry.
- **Why necessary:** defect D9 of S-2, confirmed on this branch. The docstring of the option said
  that a non-instance is a candidate when its erased body is "a bare `const`/`proj`, or a
  single-ctor structure literal whose fields are shallow", and that of `LBTerm.isTrivialAlias`
  named "a single-ctor structure literal (the usual `Foo.mk arg₁ … argₙ` shape …)". The code tests,
  after the leading λs, for `.const`, `.proj` or `.construct _ 0 _`. The eraser emits a
  constructor as a `construct` node with an empty argument list, applied to its parameters and
  fields with `LBTerm.app` (`erase.visitConstructor`), so the third case matches only a constructor
  of index 0 without parameters or fields: never a structure literal, whatever its fields, and
  `false` but not `true`. The first case also matches constant functions, which the documentation
  called aliases. The docstring of `LBTerm.stripLambdas` said that the stripped λs are
  typeclass-instance parameters; they are any parameters, and in a projection function they include
  the structure argument. The docstrings now state what the code accepts. The code is kept: a
  definition of any of these shapes is marked only after the checks of S-7 to S-10 (at most 40
  nodes once inlined, a value, not recursive, not `@[noinline]`), and matching structure literals
  would be a new feature.

  The commit messages of `94a429c` and `8db2dd9`, which D9 also concerns, cannot be changed; S-2
  records what they claim.
- **Behaviour before:** reproduction: `tests/regress/auto_inline_shapes.lean` with the option on.
  Marked: `addAlias : Nat → Nat → Nat := Nat.add` (a constant), `kfun (_ : Nat) : Nat := seven` (a
  constant function), the projection function `P.b`, and `falseDef : Bool := false`. Not marked:
  `trueDef : Bool := true`, `noneDef : Option Nat := none` (a constructor applied to its type
  parameter) and the structure literal `pVal : P := ⟨Nat.zero, Nat.succ Nat.zero⟩`. This
  contradicts the old documentation for `pVal` (a single-constructor structure literal with shallow
  fields) and for `kfun` (not an alias).
- **Behaviour after:** the same outputs and log messages, byte for byte; the documentation now
  describes them. The 20 benchmarks erased with the option on give byte-identical `.ast` and
  `.ast.inlinings` files. With `PEREGRINE` set, `useAll 2` evaluates to 10 under Peano naturals.
- **Effect on emitted .ast (corpus):** byte-identical for all 284 files; `scripts/corpus-diff.sh`
  against the corpus of S-10 reports 284 identical.
- **Regression test:** the change does not alter behaviour, so no test fails before it.
  `tests/regress/auto_inline_shapes.lean` guards the documented shapes: it pins the four marked and
  the three unmarked definitions above. It passes before and after.

## S-12: Port to Lean v4.33.0-rc2, with a Lake dependency on `lean4lean`

- **Commit:** the commit whose subject starts with `shipping(S-12):`
  (`git log --grep='^shipping(S-12):'`).
- **Files and functions:**
  - `lean-toolchain`: `leanprover/lean4:v4.22.0` becomes `leanprover/lean4:v4.33.0-rc2`.
  - `lakefile.toml`: new `[[require]]` of `lean4lean`, git `https://github.com/barabbs/lean4lean`,
    rev `8223d223ed98661882e95d9d6a7126df7097cd76` (the fork's `master`, whose toolchain is
    `v4.33.0-rc2`). `defaultTargets` is unchanged (`LeanToLambdaBox`).
  - `lake-manifest.json`: regenerated by `lake update`. The format goes from 1.1.0 to 1.2.0 (new key
    `fixedToolchain: false`), and it lists `lean4lean` at `8223d223…` and, inherited from it,
    `batteries` at `76e1c118b0700b4ceafe99532e887d6431625e1a` (input rev `v4.33.0-rc2`).
  - `LeanToLambdaBox/Erasure.lean`:
    - `register_inductive`: the type ascription `List projection_body` becomes
      `List ProjectionBody` (E1);
    - `fvar_to_name`: the predicate passed to `String.all` becomes
      `fun (c : Char) => decide (33 <= c.toNat /\ c.toNat < 127)` (E2);
    - new `csimpReplaceConstants`; `prepare_erasure` calls it in place of
      `Compiler.CSimp.replaceConstants` (E3);
    - `erase.visitCases`: `casesInfo.altsRange.start` becomes `casesInfo.altsRange.lower` (four
      places, in the machine-`Nat` and machine-`Int` paths); in the generic path, the loop reads
      each entry of `casesInfo.altNumParams` as `.ctor _ numFields` and throws an error on a
      `.default` entry (E4).
  - `benchmarks/via_malfunction/lean-toolchain` (to `v4.33.0-rc2`) and
    `benchmarks/via_malfunction/lake-manifest.json` (regenerated by `lake update`: the same format
    change, and `lean4lean` and `batteries` as inherited git packages);
    `benchmarks/lean-toolchain` and `benchmarks/via_lean/lean-toolchain.template` (to
    `v4.33.0-rc2`).
  - `.github/workflows/build.yml`: the lean-action step gets
    `build-args: "LeanToLambdaBox Lean4Lean Lean4Lean.Theory Lean4Lean.Verify"` and a comment.
  - new `tests/regress/compiler_api.lean`, its expected outputs
    `tests/regress/expected/compiler_api/` (19 files) and
    `tests/regress/expected-peregrine/compiler_api/` (2 files).
  - `tests/regress/expected/`: 29 `.ast` files re-baselined: `auto_inline/{default,default3,off,on,
    on3}.ast`, `auto_inline_noinline/useAll2.ast`, `auto_inline_recursive/{useBoth,useBoth2}.ast`,
    `auto_inline_shapes/{useAll,useAll2}.ast`, `auto_inline_size/{chain2,twice,twice3}.ast`,
    `auto_inline_values/{useAll,useAll2}.ast`, `mli_types/{rArr,rFunPair,rHof,rInt,rListFun,
    rListPair,rNestArg,rNestL,rNestR,rOpt,rOptFun,rPair,rStr}.ast`, `smoke/fact3.ast`.
  - `doc/SHIPPING-CHANGES.md`: this entry; the reproductions of R-6, R-12 and R-19, which named
    the behaviour of Lean v4.22, now give that of v4.33.

  No file of the shipping code imports `lean4lean`.
- **Why necessary:** §4 of the specification: the `shipping` branch is the shipping code ported to
  the `lean4lean` base, with a Lake dependency on `lean4lean` `master` at `8223d223` and the
  toolchain bumped to its `v4.33.0-rc2`, so that the verification code can build on `lean4lean`
  and the eraser in one Lake workspace. With only `lean-toolchain`, `lakefile.toml` and
  `lake-manifest.json` changed, `lake build` fails with 11 errors in `Erasure.lean`; the four code
  edits are the smallest ones that remove them:
  - E1: `Unknown identifier 'projection_body'`. No such name exists. Lean v4.22 accepted it because
    its `do` elaborator did not elaborate the type ascription of `let x : T ← if … then … else …`
    (a probe `let xs : List noSuchType ← if b then pure [1] else pure []` runs on v4.22 and is
    rejected with `Unknown identifier` on v4.33). The value already had type
    `List ProjectionBody`.
  - E2: three errors, all caused by the predicate of line 264 (`Invalid field notation: Type of c
    is not known` twice, `stuck at solving universe constraint`). In v4.33,
    `String.all (s : String) (pat : ρ) [ForwardPattern pat]` takes a pattern instead of a
    `Char → Bool` (`Init/Data/String/TakeDrop.lean:241`), so the binder type of the lambda is no
    longer known. The edit states the binder type and the `decide` that v4.22 inserted; the
    `ForwardPattern` instance of a `Char → Bool` accepts a string iff every character satisfies
    the predicate.
  - E3: `Unknown identifier 'Compiler.CSimp.replaceConstants'`. v4.33 removed it; only the
    single-constant `CSimp.replaceConstant?` remains, and the map of the `csimp` extension now
    holds `CSimp.Entry` records (`fromDeclName`, `toDeclName`, `thmName`) instead of names
    (`Lean/Compiler/CSimpAttr.lean`). `csimpReplaceConstants` is the v4.22 body with
    `entry.toDeclName` in place of the name.
  - E4: five errors. `CasesInfo` moved from `Lean.Compiler.LCNF` to `Lean`
    (`Lean/Meta/CasesInfo.lean`); `altsRange` is a `Std.Rco Nat` (field `lower`, no `start`) and
    `altNumParams` an `Array CasesAltInfo` (`.ctor ctorName numFields` or `.default numHyps`) instead
    of an `Array Nat`. For a `T.casesOn`, every entry is `.ctor` and `lower` is the old `start`.

  Benchmarks: `benchmarks/via_malfunction` is the Lake workspace in which the benchmark Makefile
  runs `lake lean`, and it requires the root package by path; with its toolchain left at v4.22,
  `lake build LeanToLambdaBox` there fails with 6 errors (`Invalid field 'toDeclName'`,
  `Invalid field 'lower'` four times, `Unknown identifier 'Nat.ctor'`). `from_lean_common`
  (`benchmarks/`) is compiled by `via_malfunction` with v4.33 and by the per-test packages of
  `via_lean` with the toolchain of `lean-toolchain.template`, both into `benchmarks/.lake/build`;
  with two toolchains each build recompiles it for its own (observed: 15 jobs rebuilt at every
  alternation), and the Lean-native baseline of the benchmarks would be compiled by another Lean
  than the one whose terms the eraser reads. `FromLeanCommon` compiles on v4.33 without change, and
  `make -C benchmarks/via_lean bin/even` builds a binary that prints 1, 0 and 1 for 0, 7 and 1000.

  CI: lean-action installs the toolchain that `lean-toolchain` names, and saves `.lake` to the
  cache right after its build step, so the `lean4lean` libraries are built in that step
  (`build-args`) to be cached with it. `Lean4Lean`, `Lean4Lean.Theory` and `Lean4Lean.Verify` take
  130 jobs (1 min 42 s here) and give 22 `declaration uses 'sorry'` warnings and no error. The
  regression step still runs `lake build` without arguments, which builds `LeanToLambdaBox` only.
- **Behaviour before:** at the parent commit (Lean v4.22), the eraser as in S-11. With only
  `lean-toolchain`, `lakefile.toml` and `lake-manifest.json` changed, `lake build` fails:
  `Erasure.lean:242:22` (E1), `:264:27`, `:264:38`, `:260:48` (E2), `:443:9` (E3), `:602:47`,
  `:604:47`, `:622:48`, `:623:50`, `:641:27` (E4), line numbers of the parent commit.
- **Behaviour after:** `lake build` succeeds (6 jobs), with one warning that no edit requires:
  `Printing.lean:162`: `List.asString` has been deprecated. `lake build LeanToLambdaBox Lean4Lean
  Lean4Lean.Theory Lean4Lean.Verify` succeeds (136 jobs); a plain `lake build` does not build
  `lean4lean`. `scripts/regress.sh` passes its 12 tests, with and without `PEREGRINE`.
  - On the inputs of `tests/regress/compiler_api.lean`, which exercise E1 to E4, the 19 outputs are
    those of the parent commit on v4.22 up to hygienic names (8 `.ast` files differ only there; the
    `.ast.inlinings` and `.mli` files are byte-identical), and peregrine prints the same result
    (`all` evaluates to 21 under Peano naturals).
  - Re-baselined goldens: 28 of the 29 `.ast` files differ only in hygienic binder names. Lean v4.33
    encodes macro scopes differently: `x._@.M._hyg.N` is now `x._@.M.<hash>._hygCtx._hyg.N'`
    (for example `x._@._stdin._hyg.18` becomes `x._@._stdin.303384890._hygCtx._hyg.5`); the
    number of such names per file is unchanged. `mli_types/rStr.ast` differs in two more ways,
    both from the standard library: the two hygienic binders of `List.replicateTR.loop` are based
    on `a` instead of `x`, and the declaration of the inductive `String` is no longer emitted. In
    v4.33, `String` is `structure String where ofByteArray :: bytes : ByteArray …` and `String.mk`
    is a deprecated `@[extern "lean_string_mk"]` definition
    (`Init/Data/String/Bootstrap.lean:149`), so the program refers to the axiom `String.mk` without
    registering `String` through a constructor. Its seven axioms and its `.mli` are unchanged.
    Every peregrine output of the regression tests is unchanged.
  - **Known defect left at this commit, fixed by the next entry: sparse `casesOn`.** In v4.33,
    `getCasesInfo?` also recognizes two new kinds of declarations as cases-like
    (`Lean.isCasesOnLike`, `Lean/AuxRecursor.lean:63`): the sparse `casesOn` that the match
    compiler creates for a match with a wildcard or inaccessible pattern (`F._sparseCasesOn_<i>`:
    alternatives for some constructors, and a catch-all alternative whose `CasesAltInfo` is
    `.default`), and the per-constructor eliminators `T.c.elim` of the derived `BEq` and
    `DecidableEq` of an inductive with at least 10 constructors. `erase.visitCases` takes the type
    name as `casesInfo.declName.getPrefix`, which for these is a definition or a constructor, so
    `let .inductInfo indVal ← getConstInfo typeName | unreachable!` panics
    (`PANIC at Erasure.erase.visitCases LeanToLambdaBox.Erasure:652:55: unreachable code has been
    reached`); the panic's default value makes the whole match `□`. `#erase` still succeeds,
    exits with status 0, and peregrine validates the output. Reproductions:
    - peregrine eval of corpus `examples/PortProbe/predOr0.peano.ast` (`predOr0 3`, with
      `predOr0 : | n+1 => n | _ => 0`) prints `constr con_15` / `constr con_105` instead of
      `Nat.succ (Nat.succ Nat.zero)`; `secondN.peano.ast` (`secondN 3`) prints `constr con_15` /
      `constr con_108` instead of `Nat.succ Nat.zero`;
    - the 20 natio benchmarks built natively (benchmark Makefile, peregrine with `unbox.config`
      after the R-1 rewrite, malfunction and OCaml 4.14.2 without flambda, `JCFArrayOCaml4.ml`) and
      run on 0, 1, 2, 5, 10, 50 and 1000 (0, 1, 2, 5 and 8 for binarytrees, const_fold and deriv):
      15 programs print the same values as at the parent commit; `rbmap_beans`, `rbmap_std`,
      `rbmap_mono` and `rbmap_raw` print 1 for 50 and 1000 instead of 5 and 100; `const_fold`
      crashes with a segmentation fault on every input; `deriv` crashes on 0 and runs past a 60 s
      timeout without output on 1, 2, 5 and 8 (the parent commit prints 2, 6, 22, 2202 and
      598592).
    The affected declarations of the corpus are listed below, under "sparse `casesOn`".
- **Effect on emitted .ast (corpus):** of 284 files, 155 are byte-identical to the corpus of S-11
  and 129 differ (none added or removed). All 129 contain hygienic names, which Lean v4.33 prints
  in the new encoding; `scripts/corpus-diff.sh --normalize` reports 155 identical, 55 identical
  after normalization and 74 differing (53 `.ast`, 21 `.ast.inlinings`; every `.mli` is
  byte-identical). The 55 are `benchmarks/{prune,noprune}/{even,iflazy,triangle_acc,
  triangle_rec}.ast`, 14 of the 16 `examples/Defects/*.ast` (`strlit.ast` is byte-identical and
  `wf_rec.ast` differs), 20 of the 27 `examples/Scope/*.ast` (the other 7 are byte-identical) and
  13 of the 33 `examples/PortProbe/*.ast` (`double`, `fact` and `width` in the three
  configurations, `useHalf` and `usePred` default and pruned). The axioms of every file are
  unchanged, except in predOr0 default and pruned, which lose `Nat.beq` and `Nat.sub` (sparse
  `casesOn`, below). Every difference of the 74 files
  falls in one of these classes (declarations compared after parsing, per kername):
  - **Printing (standard library):** names that Lean v4.33 gives differently, the terms being the
    same. The hygienic binders of the core definitions `List.mapTR.loop`, `List.replicateTR.loop`
    and `List.range.loop` are based on `a` instead of `x` (binarytrees, list_sum_foldl,
    list_sum_foldr, list_sum_rev, triangle_foldl, qsort, qsort_fin); the core made
    `Array.qsort.sort` and `Array.qpartition.loop` private, so their kernames become
    `_private.Init.Data.Array.QSort.Basic.0.Array.qsort.sort` and
    `_private.Init.Data.Array.QSort.Basic.0.Array.qpartition.loop` (qsort, qsort_fin,
    qsort_single); and `Nat.recCompiled` is no longer private (`colorCode.peano`,
    `shapeEq.peano`, `bigEq.peano`). 16 benchmark `.ast` files (binarytrees, list_sum_foldl,
    list_sum_foldr, list_sum_rev, triangle_foldl, qsort, qsort_fin, qsort_single, both variants)
    differ only in these names.
  - **`@[inline]` attributes (standard library):** v4.33 tags `Array.empty` and `Array.qpartition`
    `@[inline]`, so the `.ast.inlinings` of qsort, qsort_fin and qsort_single list both, and those
    of unionfind and unionfind_noinline list `Array.empty` (both variants, 10 files).
  - **Value patterns (standard library):** a match on literals now goes through the new
    `abbrev Eq.ndrec_symm` (`Init/Prelude.lean:385`) instead of two nested `Eq.ndrec`. It changes
    `Deriv.Expr.pown`, `Tiny.colorCode`, `Tiny.shapeOf` and `Tiny.bigOf`, adds the declaration
    `Eq.ndrec_symm` (an ordinary definition whose body applies `Eq.ndrec`, so no axiom is added),
    and adds `Eq.ndrec_symm` to the `.ast.inlinings` of deriv (both variants) and of colorCode,
    shapeEq and bigEq (three configurations each), 11 files.
  - **`do` notation (elaborator):** in `mkNodes` (`| n+1 => do _ ← mk; mkNodes n`) the ignored
    result is no longer bound by a trivial `let`, and the binders that `do` introduces in `test`,
    `findEntryAux`, `mkNodes`, `mk` and `StateT'.bind` are named `__r` and `__x` instead of `x` and
    `__discr` (unionfind, unionfind_noinline, both variants).
  - **Derived instances (standard library):** the auxiliary definitions of derived `BEq` and
    `DecidableEq` get stable names (`Tiny.instBEqPt.beq`, `Tiny.instBEqShape.beq`,
    `Tiny.instDecidableEqShape.decEq`, …) instead of hygienic ones (`Tiny.beqPt._@._stdin._hyg.N`,
    …), with bodies identical for ptEqN (three configurations) and for the `DecidableEq` of Shape.
    For the 10 constructors of `Tiny.Big`, v4.33 compares `Tiny.Big.ctorIdx` (a new declaration)
    with the root-level `decEq` (also new) and uses per-constructor eliminators.
  - **Core `Nat` functions (standard library)**, erased from their definitions under Peano
    naturals: `Nat.div` and `Nat.modCore` pass `Nat.succ x` instead of `x + 1` (so `Nat.add`,
    `instAddNat`, `instHAdd`, `Add`, `Add.add`, `HAdd` and `HAdd.hAdd` are no longer emitted in
    `colorCode.peano`); `Nat.div.go` and `Nat.modCore.go` are compiled differently (new
    `Nat.modCore.go._f` and `Nat.brecOn.go`); `Nat.ble` no longer splits on its second argument
    when the first is 0. Files: `Defects/wf_rec.ast`, `PortProbe/{useHalf,usePred}.peano.ast`, and
    the peano variants of colorCode, shapeEq and bigEq. The declaration order changes in wf_rec,
    useHalf.peano and bigEq.peano, whose dependencies change.
  - **Sparse `casesOn` (the known defect above):** a match compiled to a sparse `casesOn` or a
    per-constructor eliminator becomes `□`: `Expr.reassoc`, `Expr.appendAdd`, `Expr.appendMul`,
    `Expr.constFolding` (const_fold, 6 matches); `Deriv.Expr.ln`, `add`, `mul`, `pow` (deriv);
    `setBlack`, `isRed`, `balance1`, `balance2` (each rbmap benchmark); `Tiny.isRed`
    (colorCode), `Tiny.second` (secondN), `Tiny.predOr0` (predOr0), the three branches of
    `Tiny.instBEqShape.beq` (shapeEq), and the ten eliminator branches of each of
    `Tiny.instBEqBig.beq` and `Tiny.instDecidableEqBig.decEq` (bigEq). These are all the `PANIC`
    messages of the corpus logs apart from the four of R-4 and R-5: 26 per benchmark variant, 78 in
    `PortProbe`. Declarations reachable only from a lost match are no longer emitted (`Unit.unit`
    and `PUnit` in deriv, which also loses `Unit.unit` from its `.ast.inlinings`; `Nat`, `Bool`,
    `Nat.beq` and `Nat.sub` in predOr0 default and pruned), and the declaration order changes in
    the rbmap benchmarks and secondN.

  No difference comes from a change of the eraser's behaviour on an unchanged input term: E1 to E4
  change no output (see `compiler_api` above), and the sparse `casesOn` defect comes from
  declarations that the v4.22 match compiler did not produce.
- **Regression test:** `tests/regress/compiler_api.lean` guards E1 to E4: the projections of a
  structure (`ptSum.ast` declares `Pt` with two `projection_body` entries), an ASCII and a non-ASCII
  binder (`names.ast`: `a` is named, `α₁` is `nAnon`), `csimp` on and off (`sumFoldr.ast` uses
  `List.foldrTR`, `sumFoldr.nocsimp.ast` uses `List.foldr`), and the alternatives of the machine
  `Nat` and `Int` paths and of a user inductive (`natCase.ast`, `intCase.ast`, `triVal.ast`); with
  `PEREGRINE` set, `all.ast` validates and evaluates to 21. The parent commit cannot run it on
  v4.33, since the package does not compile there; on v4.22 it passes with the same outputs up to
  hygienic names. The 29 re-baselined goldens keep guarding what they guarded, and `smoke`,
  `mli_types` and the auto-inline tests pass unchanged apart from them.

## S-13: Sparse `casesOn` and per-constructor eliminators are erased by constructor name

- **Commit:** the commit whose subject starts with `shipping(S-13):`
  (`git log --grep='^shipping(S-13):'`).
- **Files and functions:**
  - `LeanToLambdaBox/Erasure.lean`: `erase.visitCases` (new docstring). The inductive type is
    `casesInfo.indName` instead of the prefix of `casesInfo.declName`. The alternatives are collected
    by constructor name from the `.ctor` entries of `casesInfo.altNumParams`, and the catch-all from
    its `.default` entry. The branch of a constructor without an alternative is the catch-all
    applied to one `□` per hypothesis, or `□` when there is no catch-all; the catch-all is erased
    once, and only if some constructor lacks an alternative. The machine-`Nat` path (arms of
    `Nat.zero` and `Nat.succ`), the machine-`Int` path (arms of `Int.ofNat` and `Int.negSucc`) and
    the generic path (a loop over the constructors of the type) look up each arm by name. The
    generic path no longer throws an error on a `.default` entry (the E4 edit of S-12).
  - new `tests/regress/sparse_cases.lean`, its expected outputs
    `tests/regress/expected/sparse_cases/` (32 files) and
    `tests/regress/expected-peregrine/sparse_cases/` (4 files).
  - `doc/SHIPPING-CHANGES.md`: this entry; new R-29.
- **Why necessary:** the known defect of S-12 ("sparse `casesOn`"), a silent miscompilation: in
  Lean v4.33, `getCasesInfo?` (`Lean/Meta/CasesInfo.lean:56`) also describes two kinds of
  declarations that are not a `T.casesOn`, and `erase.visitCases` turned each application of them
  into `□` after a panic, with exit status 0 and output that `peregrine validate` accepts.
  - The sparse `casesOn` `F._sparseCasesOn_<i>` that the match compiler creates for a match with a
    wildcard or inaccessible pattern. Its alternatives are those of the constructors that the match
    names, in the order in which they first appear in the match (`collectCtors`,
    `Lean/Meta/Match/Match.lean:543`), so not necessarily the constructor order; a last argument,
    the catch-all, takes a proof of `Nat.hasNotBit mask x.ctorIdx`. Its definition
    (`mkSparseCasesOn`, `Lean/Meta/Constructions/SparseCasesOn.lean:59`) is a `T.rec` whose minor
    premise for a constructor without alternative applies the catch-all to such a proof; the
    erasure of that application is the erased catch-all applied to `□`.
  - The per-constructor eliminator `T.c.elim motive x h alt` (`mkConstructorElim`,
    `Lean/Meta/Constructions/CtorElim.lean:165`), whose side condition `h : x.ctorIdx = i` makes
    every constructor other than `c` unreachable; it has one alternative and no catch-all. The
    derived `BEq` and `DecidableEq` of an inductive with at least 10 constructors use it.

  Lean's own compiler treats both the same way (`ToLCNF.visitAlt` and `ToLCNF.visitCases`,
  `Lean/Compiler/LCNF/ToLCNF.lean:584,621`): it applies the catch-all to erased arguments and
  leaves constructors without an alternative out of the `cases`. A λ□ `case` needs one branch per
  constructor, so an unreachable branch is `□`.
- **Behaviour before:** at the parent commit, with `tests/regress/sparse_cases.lean` copied into a
  checkout: `lake env lean` exits with status 0 after 47 messages
  `PANIC at Erasure.erase.visitCases LeanToLambdaBox.Erasure:652:55: unreachable code has been
  reached`, and every match that Lean compiles to a sparse `casesOn` or an eliminator is `□`: for
  example `Sparse.isRed` is `λx. let _alt := … in let _alt := … in □` and `Sparse.viaElim` is
  `λx h k. □ k`. `peregrine validate` accepts `count.ast` and `sum.ast`, and `peregrine eval` of
  either fails with `Could not evaluate program: Case: <15> branch not found`. The corpus
  reproductions of S-12 hold: `peregrine eval` of `examples/PortProbe/predOr0.peano.ast` and
  `secondN.peano.ast` prints `constr con_15` / `constr con_105` and `constr con_15` /
  `constr con_108`; natively, `rbmap_beans`, `rbmap_std`, `rbmap_mono` and `rbmap_raw` print 1
  for 50 and 1000, `const_fold` crashes on every input, and `deriv` crashes or runs past a 60 s
  timeout.
- **Behaviour after:** no panic. The same reproduction gives, for example, with `r` and `w` the
  let-bound alternatives of `.red` and of the wildcard,
  `Sparse.isRed = λx. let r := … in let w := … in case x of red => r Unit.unit |
  green => (λh. w x) □ | blue => (λh. w x) □ | black => (λh. w x) □`;
  `Sparse.pick`, whose match lists `.c` before `.a`, gets each alternative in its constructor's
  branch; the machine-`Nat` path gives, with `s` and `w` the alternatives of `n + 1` and of the
  wildcard, `Sparse.predOr0 = λx. let s := … in let w := … in let n := x in
  case (Nat.beq n 0) of false => (λn. s n) (Nat.sub n 1) | true => (λh. w x) □`; and
  `Sparse.viaElim = λx h k. (case x of c0 _ => □ | c1 a b => λk. a + b * k | c2 => □ | … |
  c9 _ => □) k`. With `PEREGRINE` set, `count.ast`
  evaluates to 25 (all 25 results of the test equal Lean's values, which `#guard` checks) and
  `sum.ast` to 90 (their sum). Further checks, with the tools of the benchmark pipeline
  (peregrine with `unbox.config` after the R-1 rewrite, malfunction, OCaml 4.14.2 without flambda,
  the runtime of `benchmarks/via_malfunction` with `decidable-pruned.ml` and
  `JCFArrayOCaml4.ml`):
  - `peregrine eval` of the corpus files `predOr0.peano.ast` and `secondN.peano.ast` prints
    `Nat.succ (Nat.succ Nat.zero)` and `Nat.succ Nat.zero`, Lean's values of `predOr0 3` and
    `secondN 3`;
  - the 20 natio benchmarks, built natively and run on 0, 1, 2, 5, 10, 50 and 1000 (0, 1, 2, 5
    and 8 for binarytrees, const_fold and deriv), print in all 134 runs the values of S-11, which
    are those of Lean's `#eval`;
  - the 11 functions of `tests/corpus/PortProbe.lean`, erased with constructor pruning and run
    natively on 16 inputs from 0 to 101, print Lean's `#eval` values in all 176 runs; so do the 13
    functions of `tests/regress/sparse_cases.lean`, each wrapped as a function `Nat → Nat` and
    erased with constructor pruning, in all 208 runs; these cover the machine-`Nat` and
    machine-`Int` paths, which peregrine cannot evaluate (R-1).

  On a plain `T.casesOn` every constructor has an alternative, in constructor order, and there is
  no catch-all, so `visitCases` makes the same calls in the same order as before: the 12 other
  regression tests pass unchanged, `compiler_api` among them (the machine-`Nat` and machine-`Int`
  paths and a user inductive), and 252 of the 284 corpus files are byte-identical.
- **Effect on emitted .ast (corpus):** 252 of the 284 files are byte-identical to the corpus of
  S-12; 32 differ (27 `.ast` and 5 `.ast.inlinings` files; every `.mli` is byte-identical), all
  listed by S-12 under "sparse `casesOn`". In each file, the declarations that change are exactly
  those that contain such a match, whose `□` is now the match:
  - `benchmarks/{prune,noprune}/const_fold.ast`: `Expr.reassoc`, `Expr.appendAdd`,
    `Expr.appendMul`, `Expr.constFolding`.
  - `benchmarks/{prune,noprune}/deriv.ast`: `Deriv.Expr.ln`, `add`, `mul`, `pow`; the
    declarations `Unit.unit` and `PUnit`, reachable only from these matches, are emitted again,
    and `deriv.ast.inlinings` (both variants) lists `Unit.unit` again.
  - `benchmarks/{prune,noprune}/rbmap_{beans,mono,raw,std}.ast`: `setBlack`, `isRed`,
    `balance1`, `balance2`; the declaration order is that of S-11 again.
  - `examples/PortProbe/`, each in its three configurations (`default`, `prune`, `peano`):
    `colorCode` (`Tiny.isRed`), `secondN` (`Tiny.second`; the declaration order is that of S-11
    again), `predOr0` (`Tiny.predOr0`; in `default` and `prune`, `Bool` and the axioms `Nat.beq`
    and `Nat.sub` are emitted again), `shapeEq` (`Tiny.instBEqShape.beq`), `bigEq`
    (`Tiny.instBEqBig.beq`, `Tiny.instDecidableEqBig.decEq`; the declarations and the entries of
    `bigEq.*.ast.inlinings` change order).

  Against the corpus of S-11 (Lean v4.22), with binder names and `_private` prefixes ignored, the
  axioms of all 32 files are the same, the declarations are the same apart from the standard-library
  differences listed in S-12, and the recovered matches differ from v4.22 only where v4.33's match
  compiler does. A constructor that a wildcard covers gets `(λh. alt d) □`, where `d` is the
  discriminant, in place of v4.22's `alt (C args)` with the constructor rebuilt from the matched
  fields (for `RBNode.isRed`: `leaf => (λh. alt t) □` for `alt (leaf □ □)`); and the case trees of
  `Deriv.Expr.mul`, `Deriv.Expr.pow` and `Expr.constFolding` have 33, 22 and 13 `case` nodes where
  v4.22 had 35, 23 and 15.
- **Regression test:** `tests/regress/sparse_cases.lean` erases a match of each kind on each path
  of `visitCases`: the generic path with a catch-all for three constructors (`isRed`), alternatives
  out of constructor order (`pick`), a catch-all that receives the scrutinee (`leftOr`), nested
  matches (`second`), a discriminant that is not a variable (`redCode`, see R-29), a catch-all for a
  constructor with a proof field with and without pruning (`optVal`) and a match applied to an extra
  argument (`applyTo`); the machine `Nat` path with a catch-all for `Nat.zero` (`predOr0`) and for
  `Nat.succ` (`isZero`); the machine `Int` path with a catch-all for `Int.ofNat` (`negPart`) and
  for `Int.negSucc` (`natPart`); and eliminators, called directly with an extra argument
  (`viaElim`) and through a derived `BEq` of 10 constructors (`bigEq`). With `PEREGRINE` set,
  `count.ast` and `sum.ast` validate and evaluate to 25 and 90. It fails before (47 panics, 23 of
  its 32 outputs differ, `peregrine eval` fails) and passes after.

## S-14: A catch-all no longer re-evaluates a discriminant that is not a variable

- **Commit:** the commit whose subject starts with `shipping(S-14):`
  (`git log --grep='^shipping(S-14):'`).
- **Files and functions:**
  - `LeanToLambdaBox/Erasure.lean`: `erase.visitCases` (docstring extended) and new
    `erase.visitCasesOn`. `visitCases` erases the discriminant and collects the alternatives and
    the catch-all as in S-13, then drops the catch-all if every constructor has an alternative.
    If the catch-all is used and the erased discriminant is neither a variable nor □, it adds a
    let-declaration `discr` whose value is the discriminant to the local context, replaces every
    occurrence of the discriminant in the catch-all by `discr` (the catch-all stays well-typed,
    since `discr` unfolds to the discriminant), builds the `case` with `discr` as its discriminant,
    and returns `let discr := <erased discriminant> in <case>`. The extra arguments of an
    over-applied `casesOn` are applied to the result, outside the `let`, as before.
    `visitCasesOn` is the rest of S-13's `visitCases`, unchanged: the erasure of the catch-all, then
    the machine-`Nat`, machine-`Int` and generic paths.
  - new `tests/regress/sparse_discr.lean`, its expected outputs
    `tests/regress/expected/sparse_discr/` (12 files) and
    `tests/regress/expected-peregrine/sparse_discr/` (2 files).
  - `tests/regress/expected/sparse_cases/{redCode,count,sum}.ast`: the declaration
    `Sparse.redCode`, the only match of that test whose discriminant is not a variable.
  - `doc/SHIPPING-CHANGES.md`: this entry; R-29 now points here.
- **Why necessary:** R-29, a defect of S-13 and a performance regression against Lean v4.22
  (`main`, and S-11 on this branch). In Lean v4.33, the matcher of a match with a wildcard passes
  its discriminant to the wildcard's alternative inside the catch-all of its sparse `casesOn`
  (`fun motive x h_1 h_2 => F._sparseCasesOn_1 x (h_1 ()) fun h => h_2 x`), and `inlineMatchers`
  substitutes the discriminant for `x`. S-13 erases the catch-all as given, so a discriminant that
  is a call is computed once as the scrutinee and once more in every branch of the catch-all. The
  results are right, but a function that matches on its own recursive call computes that call
  twice at every level, and takes time exponential in the depth of the recursion. Under v4.22 the
  same match was a plain `casesOn` whose wildcard alternative received the constructor rebuilt from
  the matched fields, so the discriminant was computed once, as it is in Lean's own compiled code.
- **Behaviour before:** at the parent commit, with `tests/regress/sparse_discr.lean` copied in,
  `lean` exits with status 1 and the error `expected one reference each: [stepN.ast refers to
  Discr.step 3 times, predSub2.ast refers to Discr.sub2 2 times, negOr.ast refers to Discr.neg 2
  times]`, and 4 of the 12 outputs differ from the expected ones (`stepN`, `predSub2`, `negOr` and
  `all`). With `g` and `w` the let-bound alternatives of `.green` and of the wildcard,
  `Discr.stepN = λn. let g := … in let w := … in case (Discr.step n) of red =>
  (λh. w (Discr.step n)) □ | green => g Unit.unit | blue => (λh. w (Discr.step n)) □`, and
  `Discr.step` puts its recursive call `step n` in the same three places. On the machine paths,
  `Discr.predSub2 = λn. … let n := Discr.sub2 n in case (Nat.beq n 0) of false => … | true =>
  (λh. w (Discr.sub2 n)) □`, and `Discr.negOr` likewise with `Discr.neg`. Built natively with the
  tools of the benchmark pipeline (as in S-13), `stepN` erased with constructor pruning prints 1
  (Lean's value) for 20, 22, 24, 26 and 28 after 0.012, 0.034, 0.120, 0.460 and 1.830 s; under
  Peano naturals, `peregrine eval` of `stepN 16` and `stepN 20` prints 1 after 0.105 and 1.476 s.
- **Behaviour after:** the test passes. For example,
  `Discr.stepN = λn. let g := … in let w := … in let discr := Discr.step n in case discr of red =>
  (λh. w discr) □ | green => g Unit.unit | blue => (λh. w discr) □`; `Discr.step` binds its
  recursive call in the same way; `Discr.predSub2 = λn. … let discr := Discr.sub2 n in
  let n := discr in case (Nat.beq n 0) of false => … | true => (λh. w discr) □`, and
  `Discr.negOr` likewise. Natively, `stepN` prints 1 for each of 20 to 28 after 0.004 s, and for
  1000 and 100000 after 0.004 and 0.006 s (for 1000000 the stack overflows, as the recursion of
  `step` is not a tail call); `peregrine eval` of `stepN 20` and `stepN 200` takes 0.011 and
  0.029 s. For comparison, S-11 (Lean v4.22) takes 0.004 to 0.007 s natively for 20 to 100000, and
  Lean v4.33's own compiled code 0.006 to 0.008 s.

  A match gets no `let` if its `casesOn` has no catch-all, if its catch-all is not used, or if its
  discriminant is a variable. So the 12 tests other than `sparse_cases` and `sparse_discr` pass
  unchanged, `compiler_api` (plain `casesOn` on the three paths) among them; in `sparse_cases`
  only the declaration `Sparse.redCode` changes, and `count.ast` and `sum.ast` still evaluate to 25
  and 90; and in the new test, `codeOf` (a plain `casesOn` on a call) and `shiftBy` (a match
  applied to an extra argument, which `inlineMatchers` leaves as a β-redex whose parameter is the
  discriminant) are byte-identical to the parent's output.
- **Effect on emitted .ast (corpus):** byte-identical for all 284 files. In the corpus, every
  `case` with a catch-all branch (`(λh. …) □`) has a variable discriminant: 267 on the generic
  path, whose scrutinee is a variable, and 2 on the machine-`Nat` path (`Tiny.predOr0` in
  `examples/PortProbe/predOr0.{default,prune}.ast`), whose `n` is bound to a variable.
- **Regression test:** `tests/regress/sparse_discr.lean` erases a match with a used catch-all and a
  discriminant that is a call on each path of `visitCases`: the generic path (`stepN`, and R-29's
  `step`, which matches on its own recursive call), the machine `Nat` path (`predSub2`) and the
  machine `Int` path (`negOr`); and, as controls, a plain `casesOn` on a call (`codeOf`) and a match
  applied to an extra argument (`shiftBy`). The expected outputs show one `let discr` per such
  match. An `#eval` counts, in each file, the references to the function that computes the
  discriminant, and fails unless there is exactly one: a check of the emitted term, independent of
  timing. With `PEREGRINE` set, `all.ast` (every function applied to arguments, under Peano
  naturals) validates and evaluates to 26, Lean's value, which `#guard` checks. It fails before (the
  `#eval` reports 3, 2 and 2 references; 4 of 12 outputs differ) and passes after. The expected
  outputs of `sparse_cases` pin `Sparse.redCode` with its `let`.

## S-15: The corpus gains the scope-note examples, irreducible-alias programs and unsafe recursion

- **Commit:** the commit whose subject starts with `shipping(S-15):`
  (`git log --grep='^shipping(S-15):'`).
- **Files and functions:**
  - new `tests/corpus/Examples.lean`, `tests/corpus/Names.lean`, `tests/corpus/NearMiss.lean`:
    the example files of the scope note (checkpoint 1), with its commands replaced by `#erase`.
    Each `#example "<n>" t` became `#erase t config {nat := .peano} to "<n>.peano.ast"` and
    `#erase t to "<n>.default.ast"`, each `#readout "<n>" t` the first of these two; the closure
    checks, `#reduce_as` and the two closing `#eval`s of `Examples.lean` are dropped, and the
    declarations are unchanged. In `NearMiss.lean`, the two `#erase`s of `(_ : NM.CNat)` fail and
    are wrapped in `#guard_msgs (error, substring := true)` on `unknown metavariable` (the
    metavariable's id depends on what the file elaborates before it).
  - new `tests/corpus/IrrAlias.lean`: `Irr.useFI := fI two` with `fI : EndoC` and
    `@[irreducible] def EndoC : Type 1 := CNat → CNat`; `Irr.useLamHR := guardR (lamHR two) six`
    with `theorem lamHR : CNat → R := fun _ => hR`; `Irr.pidHR := pid hR`; where `axiom R : IProp`,
    `axiom hR : R` and `@[irreducible] def IProp : Type := Prop`. The four `#erase`s of `useFI` and
    `useLamHR` fail and are wrapped in `#guard_msgs (error)` with their exact errors.
  - new `tests/corpus/UnsafeRec.lean`, over `CN.{u} := (α : Type u) → (α → α) → α → α`:
    `URec.uf one.{0}` with `unsafe def uf (n : CN.{0}) : CN.{0} := (fun _ => n) (fun x => uf x)`;
    `URec.ua bfalse one.{0}` with the mutual block `unsafe def ua b n := b _ (fun m => m)
    (fun m => ub btrue (csucc m)) n` and `ub` symmetric, over Church booleans in `Type 2`; and
    `URec.ug one.{0}` with `unsafe def ug : CN.{0} → CN.{0} := (fun _ n => n) (fun x => ug x)`,
    whose value is an application.
  - `doc/SHIPPING-CHANGES.md`: this entry; the corpus description above; the reproductions of
    R-11 and R-14.

  No file under `LeanToLambdaBox/`, no package file, no file under `benchmarks/` or `scripts/`
  and no regression test changes.
- **Why necessary:** the verification plans a second erasure path for programs without inductive
  types, to be checked against today's path, and with `peregrine validate` and `eval`, on every
  corpus program of that fragment. Before this change the corpus had 25 such programs
  (`Scope.lean`). None of them has an `@[irreducible]` alias, a `@[macro_inline]` constant, an
  opaque, a name that collides or needs escaping, a universe-polymorphic type that is a proposition
  at universe 0, or recursion. Without the new files, those checks would cover neither the
  behaviours in which the two paths are expected to differ (an irreducible alias, `@[macro_inline]`)
  nor recursion (`tFix`). The new files add 74 programs of the fragment: 61 in `Examples.lean`, 7 in
  `Names.lean`, 3 in `IrrAlias.lean` and 3 in `UnsafeRec.lean`.
- **Behaviour before:** the eraser as at S-14. `scripts/corpus.sh` writes 284 files.
- **Behaviour after:** the eraser is unchanged. `scripts/corpus.sh` writes 704 files, with no
  `PANIC` in the logs of the new files. On the new programs:
  - `#erase Irr.useFI` fails with `function expected` on `Irr.fI Irr.two`, and
    `#erase Irr.useLamHR` with `type expected` on `Irr.R` (R-14). `Irr.pidHR` is emitted with the
    axioms `Irr.R` and `Irr.hR` (R-14): it validates, and `peregrine eval` stops with
    `Axioms found … .Irr.R, .Irr.hR`.
  - `URec.uf` is a one-member `tFix`; the program validates and evaluates to `one`.
    `URec.ua` and `URec.ub` are two declarations, each the two-member `tFix` of the block (at
    index 0 and 1); `ua bfalse one` validates and evaluates to `csucc one`, a λ. `URec.ug` is a
    `tFix` whose body is an application; `peregrine validate` and `eval` reject the program with
    `Fixpoint body is not a lambda` (R-11).
  - The emitted files of `Examples.lean`, `Names.lean` and `NearMiss.lean` are those the scope
    note reports (erased at S-13), up to hygienic name suffixes and, in `N_private.*`, the main
    module's name in `_private.<module>.0`.
- **Effect on emitted .ast (corpus):** the 284 files of S-14 are byte-identical. 420 files are new
  (210 `.ast`, 210 `.ast.inlinings`, no `.mli`): `examples/Examples/` 340, `examples/Names/` 32,
  `examples/NearMiss/` 32, `examples/IrrAlias/` 4 (`pidHR`), `examples/UnsafeRec/` 12.
- **Regression test:** the eraser is unchanged, so no test fails before. The new corpus files
  guard the fragment's behaviours listed above, byte for byte through the corpus, and the failing
  `#erase`s through `#guard_msgs`: `scripts/corpus.sh` stops if a corpus file reports an error, so
  a change of these errors, or an `#erase` that starts to succeed, shows. The regression tests are
  unchanged and pass.

## S-16: The erasure traversal is total and generic over its backend

- **Commit:** the commit whose subject starts with `shipping(S-16):`
  (`git log --grep='^shipping(S-16):'`).
- **Files and functions:**
  - `LeanToLambdaBox/Basic.lean`: `toBvar` is no longer `partial`: it is defined by structural
    recursion, together with the new `toBvarList`, `toBvarAlts` and `toBvarDefs`, which apply it to
    the arguments of a `construct`, the alternatives of a `case` and the definitions of a `fix`
    (in place of `List.map`).
  - `LeanToLambdaBox/Erasure.lean`:
    - new class `Backend m`: the environment and `Meta` operations of the traversal (`findConst?`,
      `unknownConstant`, `declInfo?`, `unsafeRecBase?`, `freshFVarId`, `instantiate1`,
      `isErasable`, `inferType`, `casesInfo?`, `ctorArity?`, `argMask`, `isExtern`,
      `inlineAttr?`, `isInstance`, `prepare`, `log`, `outOfFuel`); `isErasable`, `inferType` and
      `argMask` receive the traversal's `LocalContext`;
    - new `instance : Backend CoreM`, whose operations are the calls the traversal made before:
      `Environment.find?`, `throwUnknownConstant`, `Compiler.LCNF.getDeclInfo?`,
      `Compiler.isUnsafeRecName?`, `mkFreshFVarId`, `Expr.instantiate1`, `isErasable` and
      `Meta.inferType` run by the new `runMetaM` (the former `liftMetaM`, in `CoreM`),
      `getCasesInfo?`, `getCtorArity?`, the new `argMaskCore` (the argument-mask code of
      `register_inductive`, moved unchanged), `isExtern`, `Compiler.getInlineAttribute?`,
      `Meta.isInstance`, `prepareErasure` (the former `prepare_erasure`, which now receives the
      configuration), `logInfo`, and `throwError` for `outOfFuel`;
    - new `EraseT m := StateT ErasureState (ReaderT ErasureContext m)` in place of `EraseM`
      (which was `EraseT CoreM`); `run` is generic;
    - new `getConst`: `getConstInfo` through the backend (`findConst?`, then `unknownConstant`);
    - generic over the backend, with bodies otherwise unchanged: `addAxiom`,
      `register_inductive`, `fvar_to_name`, `mkLambda`, `mkLetIn`, `mkAlt`, `mkDef`,
      `withLocalDecl`, `withLocalDef`, `lambdaMonocular`, `letMonocular`, `forallMonocular`,
      `lambdaMonocularOrIntro`, `lambdaOrIntroToArity`, `remove_unsafe_rec`, `name_occurs`;
    - `withAppEtaToMinArity` is no longer `partial`: it takes a `fuel` argument, and its `go`
      recurses structurally on it;
    - the functions of the `where` block of `erase` (`visitExpr`, `visitLiteral`, `visitLambda`,
      `visitLet`, `visitProj`, `visitApp`, `visitConst`, `visitConstApp`, `visitConstructor`,
      `visitAppArgs`, `visitCases`, `visitCasesOn`, `visitAlt`, `get_constant_kername`,
      `visitMutual`) become the top-level `mutual` block `Erasure.visitExpr`, …, generic over the
      backend. Each takes a first argument `fuel`, fails with `Backend.outOfFuel` at 0 and calls
      the functions of the block with `fuel - 1`; they are defined by structural recursion on it.
      Their bodies are otherwise unchanged;
    - new `travFuel := 2 ^ 32`; `erase` is no longer `partial`: it runs
      `visitExpr travFuel` after `prepare` with the `CoreM` backend, as before.
  - new `tests/regress/traversal_total.lean`, its expected outputs
    `tests/regress/expected/traversal_total/` (4 files) and
    `tests/regress/expected-peregrine/traversal_total/` (2 files).
  - `tests/regress/compiler_api.lean`, `tests/regress/sparse_cases.lean`: the module docstrings
    name `Erasure.visitCases` in place of `erase.visitCases`.
  - `doc/SHIPPING-CHANGES.md`: this entry; the "Where" fields of R-4, R-5, R-6, R-8, R-9, R-10,
    R-11, R-12, R-13, R-21 and R-24, and the reproduction of R-4, name the new functions.
- **Why necessary:** the verification (DESIGN Q8, S-A) proves a theorem about the traversal that
  `#erase` runs. A `partial` definition is an opaque constant: it has no equations, so nothing about
  `erase`, its `where` block, `withAppEtaToMinArity` or `toBvar` can be proved. The traversal
  cannot be structural on the term, since `visitMutual` erases the body of another constant and
  `lambdaMonocular` instantiates the body it visits; a fuel argument that bounds the depth of the
  recursion makes it total without changing the calls it makes. The traversal also ran in `CoreM`,
  whose state and `Meta` operations are opaque to proofs; being generic over the backend lets the
  verified path run this same traversal with a pure backend (DESIGN Q8, S-D) instead of a copy of
  it, while `#erase` keeps the `CoreM` backend.
- **Behaviour before:** `erase`, its `where` functions, `withAppEtaToMinArity` and `toBvar` are
  `partial`. Reproduction: `tests/regress/traversal_total.lean` at the parent commit fails with 21
  errors (`Unknown identifier visitExpr`, `Unknown identifier Backend.outOfFuel`, …), and a file
  stating `toBvar x 0 (.letIn .anon (.fvar x) (.fvar x)) = .letIn .anon (.bvar 0) (.bvar 1) := rfl`
  fails with `Type mismatch`, because `toBvar` does not unfold.
- **Behaviour after:** `#erase` gives the same outputs and the same log messages; a `PANIC`
  message names the new function (`PANIC at Erasure.visitLiteral` in place of
  `PANIC at Erasure.erase.visitLiteral`). The traversal functions and `toBvar` have equation
  lemmas (`Erasure.visitExpr.eq_1`: `visitExpr 0 e = liftM (Backend.outOfFuel "visitExpr")`;
  `visitExpr.eq_2`: at `fuel + 1` on `.app`, the body of `visitExpr`; likewise for the other
  functions and for `withAppEtaToMinArity.go`), and `rfl` computes `toBvar`. With fuel 2,
  `visitExpr` on `fun (x : Nat) => x` fails with `erasure: recursion bound reached in visitExpr`;
  with fuel 3 it gives `λx. x`. `#erase` runs with fuel `2 ^ 32`, which no program reaches: the
  recursion is as deep as before and exhausts the stack first (R-6). All axioms of `visitExpr` and
  `visitMutual` are `propext`, `Classical.choice` and `Quot.sound`; `toBvar` has none.
- **Effect on emitted .ast (corpus):** byte-identical for all 704 files; `scripts/corpus-diff.sh`
  against the corpus of S-15 reports 704 identical. The corpus logs are identical except for the
  location lines of the 4 `PANIC` messages of `Defects.lean` (the function names and line numbers)
  and their backtraces.
- **Regression test:** `tests/regress/traversal_total.lean` states, for every backend, the equations
  of `visitExpr` at fuel 0 and at `fuel + 1` on a free variable, of `visitAppArgs` and of
  `visitMutual` at fuel 0 (proved by `rw` with the equation lemmas); the value of `toBvar` under a λ,
  a let, a case with two alternatives and a fixpoint with two definitions (proved by `rfl`); the
  fuel error and the result at sufficient fuel of `visitExpr` with the `CoreM` backend
  (`#guard_msgs`); and it pins the output of a program that goes through every function of the
  traversal: a let of a literal, a projection, a match with its alternatives, a constructor
  η-expanded to its arity (`List.map T.b`), a mutual recursion (`ev`/`od`), under Peano naturals
  (`all.ast`, which peregrine evaluates to 10, Lean's value) and under the default configuration
  (`go.ast`). It fails before (21 errors; the outputs are the same) and passes after.

## S-17: The traversal's context lists its locals, and binder names come from that list

- **Commit:** the commit whose subject starts with `shipping(S-17):`
  (`git log --grep='^shipping(S-17):'`).
- **Files and functions:**
  - `LeanToLambdaBox/Erasure.lean`:
    - `ErasureContext` becomes `TravCtx`, with the fields `lctx`, `locals`, `fixvars` and `config`:
      the new field `locals : List Local` holds the same binders as `lctx`, innermost first;
    - new structure `Local` (`fvarId`, `userName`, `type`, `value?`);
    - new `binderNameOf`: the name test of `fvar_to_name`, as a function of the user name (an ASCII
      graphic name is kept, any other becomes anonymous); new `fixDefName`: the name that `mkDef`
      gave a fixpoint definition;
    - `withLocalDecl` and `withLocalDef` push the new binder onto `locals` (with its value for a
      `let`) as well as into `lctx`;
    - `fvar_to_name` is `binderNameOf` of the user name of the variable's entry in `locals`, in
      place of a lookup in `lctx`; `mkDef` names the definition with `fixDefName`;
    - `Backend.isErasable` and `Backend.inferType` also receive the list of locals; the `CoreM`
      backend ignores it and runs `Meta` in `lctx`, as before; `EraseT m` reads a `TravCtx`.
  - new `tests/regress/traversal_locals.lean`, its expected outputs
    `tests/regress/expected/traversal_locals/` (6 files) and
    `tests/regress/expected-peregrine/traversal_locals/` (2 files).
  - `tests/regress/traversal_total.lean`: its equation of `visitExpr` on a free variable passes the
    list of locals to `Backend.isErasable`.
  - `doc/SHIPPING-CHANGES.md`: this entry.
- **Why necessary:** DESIGN Q8, S-B. The verified backend's oracle types free variables from a list
  of locals: a `LocalContext` lookup goes through a `PersistentHashMap`, whose operations are
  opaque to proofs (lean4lean states them as axioms). The erasure relation of the verification
  fixes the λ□ name of a binder as a function of its Lean user name (`binderNameOf`) and the name of
  a fixpoint definition as a function of the constant's name (`fixDefName`), so the traversal
  computes them from these. Keeping `lctx` leaves the `CoreM` backend unchanged.
- **Behaviour before:** `fvar_to_name` reads the binder's user name from `lctx`
  (`lctx.fvarIdToDecl.find!`), and the context has no list of locals. Reproduction:
  `tests/regress/traversal_locals.lean` at the parent commit fails with 9 errors
  (`Unknown identifier binderNameOf`, `Invalid field locals`, …); its six output files are those
  expected.
- **Behaviour after:** `#erase` gives the same outputs and the same log messages. After
  `withLocalDecl a` and `withLocalDef b`, `locals` is `[b (with its value), a]` and `lctx` holds
  both. `binderNameOf` gives `x ↦ "x"`, `α₁ ↦ anonymous`, `a.b ↦ "a.b"`, `«a b» ↦ anonymous`, as
  `fvar_to_name` did. A variable without an entry in `locals` makes `fvar_to_name` panic
  (`Option.get!`), as a variable without an entry in `lctx` did (`PersistentHashMap.find!`);
  the traversal introduces every variable it names with `withLocalDecl` or `withLocalDef`, and no
  corpus or regression log has a new `PANIC`.
- **Effect on emitted .ast (corpus):** byte-identical for all 704 files; `scripts/corpus-diff.sh`
  against the corpus of S-16 reports 704 identical. The corpus logs are identical except for the
  line numbers in the locations of the 4 `PANIC` messages of `Defects.lean`, and their backtraces.
- **Regression test:** `tests/regress/traversal_locals.lean` checks `binderNameOf` and `fixDefName`
  on ASCII, non-ASCII and hierarchical names, and the contents of `locals` and `lctx` after a
  `withLocalDecl` and a `withLocalDef` (`#guard_msgs`); and it pins the output of programs with a
  binder at every place where the traversal introduces one: a λ with an ASCII and a non-ASCII
  binder, a `let`, a constructor η-expanded to its arity (`List.map T.b`), a `casesOn` with an
  alternative that is not a λ (`g`, η-expanded through its type) and one that is, a sparse
  `casesOn` whose discriminant is let-bound (`discr`, S-14), a `Nat` match in machine mode (`n`),
  and a recursive definition (the fixpoint definition `Loc.step`): `names.ast`, `step.ast`
  (default configuration) and `all.ast` (Peano naturals, which peregrine evaluates to 11, Lean's
  value). A binder missing from `locals` would make the test fail on the panic. It fails before
  (9 errors; the outputs are the same) and passes after.

## S-18: The dependency closure of a program is computed by `collectDeps`, which `#erase` does not call yet

- **Commit:** the commit whose subject starts with `shipping(S-18):`
  (`git log --grep='^shipping(S-18):'`).
- **Files and functions:**
  - new `LeanToLambdaBox/Erasure/Collect.lean` (module `LeanToLambdaBox.Erasure.Collect`; it
    imports `LeanToLambdaBox.Basic` and lean4lean's `Lean4Lean.Verify.Axioms`):
    - derived `DecidableEq` instances for `ModPath` and `Kername` (`instDecidableEqModPath`,
      `instDecidableEqKername`);
    - `Erasure.EraseError`, with the constructors `outOfFragment`, `nameCollision`, `fuel`,
      `failed`;
    - `Erasure.EnvView`, with the fields `find?`, `isExtern`, `inlineAttr?`, and
      `Erasure.EnvView.ofEnvironment`, which reads them from an `Environment`
      (`Environment.find?`, `isExtern`, `Compiler.getInlineAttribute?`);
    - `Erasure.findConst`: lookup by name in a list of declarations;
    - `Erasure.exprConsts`: the constants of a term, or `outOfFragment` for a free variable, a
      metavariable, a universe metavariable (tested with lean4lean's `Level.hasMVar'`), a literal or
      a projection;
    - `Erasure.declDeps`: the names that an axiom, a definition, a theorem or an opaque depends on
      (its type, its value, the members `all` of its block), or `outOfFragment` for a quotient, an
      inductive type, a constructor or a recursor;
    - `Erasure.closure`: the depth-first closure of a list of names, each name expanded once, with
      a bound on its steps (`fuel` when reached); a name the view does not have is
      `outOfFragment`, and a view that answers with a declaration of another name is `failed`;
    - `Erasure.findCollision`: two declarations of a list with the same kername (`toKername`);
    - `Erasure.collectFuel := 2 ^ 32` and `Erasure.collectDeps view e`: the closure of the
      constants of `e`, and `nameCollision` if two of its declarations have the same kername.
  - `LeanToLambdaBox.lean`: imports the new module.
  - new `tests/regress/collect_deps.lean`, its expected outputs
    `tests/regress/expected/collect_deps/` (2 files) and
    `tests/regress/expected-peregrine/collect_deps/` (2 files).
  - `doc/SHIPPING-CHANGES.md`: this entry.
- **Why necessary:** DESIGN Q8, S-C. The verified path erases a program over its own environment,
  the dependency closure of the term, not over the whole Lean environment, and `collectDeps`
  computes that closure from a view of the environment. DESIGN Q8 S-E routes on its result: a
  program whose closure meets an inductive type, a literal, a projection, a metavariable or an
  unknown constant (`outOfFragment`) is to keep the unchanged path. The verification's statements
  `collectDeps_spec`, `collectDeps_sub` and `collectDeps_not_outOfFragment` are about this
  function, so it is total and works on lists, which proofs and kernel evaluation see through. It
  tests universe metavariables with lean4lean's structural `Level.hasMVar'`: Lean's
  `Level.hasMVar` reads a cached field, which lean4lean relates to `hasMVar'` only by an axiom
  (`Level.hasMVar_eq`, `Lean4Lean/Verify/Axioms.lean:289`). The collision check makes the kernames
  of the closure distinct, since `toKername` is not injective (R-3). `findCollision` compares
  kernames with the derived `BEq`; the `DecidableEq` instances decide the equality of kernames that
  the verification states (`KernameInj`).
- **Behaviour before:** none of these declarations exists. Reproduction:
  `tests/regress/collect_deps.lean` at the parent commit fails with 21 errors
  (`Unknown identifier collectDeps`, `Unknown identifier EnvView.ofEnvironment`, `The expected type
  EnvView is not an inductive type`, …); its two output files are those expected.
- **Behaviour after:** `#erase` is unchanged: nothing calls the new functions. Over the elaboration
  environment (`EnvView.ofEnvironment`), `collectDeps` gives `[A, CN, one]` for
  `one (fun a : A => a)` (`axiom A : Type`, `def CN := (A → A) → A → A`,
  `def one : CN := fun s z => s z`); `[one, ub, ua, A, CN, useU]` for a constant `useU` that uses a
  two-member `unsafe` block `ua`/`ub`, so the block is closed under its members;
  `outOfFragment "level metavariable"` for `@pid` at a universe metavariable;
  `outOfFragment "literal"` for `«a b»`, whose closure contains `a_u32b` (the same kername) and a
  literal, so the scan of the fragment comes before the collision check; and
  `nameCollision c_u32d «c d»` for an in-fragment closure with those two constants. The kernel
  evaluates `collectDeps` with its bound `2 ^ 32` (`decide`). No new declaration depends on an axiom
  of lean4lean: `exprConsts`, `declDeps`, `closure`, `findConst` and the two instances depend on no
  axiom, `findCollision`, `collectDeps` and `EnvView.ofEnvironment` on `propext`,
  `Classical.choice` and `Quot.sound`. Every file that imports `LeanToLambdaBox` now also imports
  `Lean4Lean.Verify.Axioms` and, through it, 25 modules of `batteries` and 2 more of `lean4lean`
  (28 modules): their declarations, including lean4lean's axioms and `@[simp]` axioms about `Expr`
  and `Level`, are in scope. For every constant declared outside these 28 modules, the
  `@[inline]`-family attribute, `@[extern]`, `@[implemented_by]`, the reducibility, the instance
  status and the `@[csimp]` replacement are the same with and without them (64119 constants with a
  value other than the default, all equal); the 16 `@[csimp]` lemmas that the 28 modules add all
  replace functions declared in `batteries` (`Batteries.Data.List.Basic`, e.g. `List.sublists`).
  The first `lake lean` of the benchmark pipeline in `benchmarks/via_malfunction` builds the 28
  modules once.
- **Effect on emitted .ast (corpus):** byte-identical for all 704 files; `scripts/corpus-diff.sh`
  against the corpus of S-17 reports 704 identical. The corpus logs are identical except for the
  job counts of `lake` (6 jobs become 37 for the build of the package, 21 become 52 for each
  `lake lean` of the benchmarks) and the addresses in the backtraces of the 4 `PANIC` messages of
  `Defects.lean`. In a benchmark workspace where the 28 modules are not built yet, the first
  benchmark log also lists their build.
- **Regression test:** `tests/regress/collect_deps.lean` proves by `decide` that `collectDeps` gives
  `[A, CN, one]` for `one (fun a : A => a)` over a view built by hand; checks with `#guard_msgs` its
  results over the elaboration environment on that program, on the `unsafe` block, on `@pid` at a
  universe metavariable, on the collision-first program and on the in-fragment collision (as
  above); proves by `decide`, over views built by hand, the closure `[A, B]` of `B := A`, that the
  collision-first program is `outOfFragment`, that the in-fragment collision is `nameCollision`,
  that a constant missing from the view is `outOfFragment`, and that a view answering `find? a` with
  a declaration named `b` gives `failed`; and pins the output of `#erase` on
  `one (fun a : A => a)` (`nv1.ast`, which peregrine validates and evaluates to
  `λz. (λa. a) z`). It fails before (21 errors; the outputs are the same) and passes after.

## S-19: A pure erasability oracle and the monad of a pure backend, which `#erase` does not use yet

- **Commit:** the commit whose subject starts with `shipping(S-19):`
  (`git log --grep='^shipping(S-19):'`).
- **Files and functions:**
  - new `LeanToLambdaBox/Erasure/Pure.lean` (module `LeanToLambdaBox.Erasure.Pure`; it imports
    `LeanToLambdaBox.Erasure` and `LeanToLambdaBox.Erasure.Collect`):
    - the oracle, in namespace `Erasure.Pure`:
      - `instLevel ps us`: the level with each parameter of `ps` replaced by the level at the same
        position of `us`, without normalization; `instLevels ps us`: the same on every sort and
        constant of a term;
      - `Ctx`, whose only field `decls : List ConstantInfo` holds the declarations the oracle
        reads;
      - `alwaysZero`: a level that is zero under every assignment of its parameters, read off its
        shape (`zero`, `max` of two such levels, `imax` whose right side is one);
      - `findLocal`: the local of a free variable in a list of `Erasure.Local`s;
      - `whnf cx fuel ls e`: the weak-head normal form of `e` by head β (with lean4lean's
        `Expr.instantiate1'`), ζ (a `let`, a local of `ls` with a value), `mdata` removal, and δ of
        every definition (`defnInfo`) of `cx.decls` used at its number of universe levels, whether
        or not it is `@[irreducible]`;
      - `inferType cx fuel ls Γ e`: the type of `e`, inferred without checking. Inside `e` bound
        variables stay de Bruijn indices: `Γ` holds the types of the binders entered, and `bvar i`
        has type `Γ[i]` lifted by `i + 1` (lean4lean's `Expr.liftLooseBVars'`). A free variable has
        its type in `ls`, a constant the type of its declaration at the given levels. The type of
        the function of an application is reduced by `whnf` to a Π, and the types of the domain and
        codomain of a Π to sorts;
      - `isArity cx fuel ls T`: `whnf` of `T` is a sort, or a Π whose codomain is an arity;
      - `isErasable cx fuel ls e`: the type `T` of `e` is an arity, or the type of `T` reduces to a
        sort that is `alwaysZero`.

      Each of `whnf`, `inferType`, `isArity` recurses on its fuel and fails with
      `EraseError.fuel` when it runs out. A literal, a projection, a metavariable, a loose bound
      variable, or a constant or free variable the oracle does not know gives `outOfFragment`; a
      constant at the wrong number of levels, an application whose function type does not reduce to
      a Π, and a Π whose domain or codomain type does not reduce to a sort give `failed`;
    - `Erasure.oracleFuel := 2 ^ 20`, the fuel of one oracle call;
    - `Erasure.PureCtx` (fields `decls : List ConstantInfo` and `view : EnvView`),
      `Erasure.PureState` (field `next : Nat`) and
      `Erasure.PureM := ReaderT PureCtx (StateT PureState (Except EraseError))`, the monad of a
      backend without `Meta`; `Erasure.EraseT.runPure x st tc pc ps` runs an action `x` of
      `EraseT PureM` from the traversal's state `st` and context `tc` and the backend's context
      `pc` and state `ps`;
    - operations of `PureM`: `Erasure.PureM.findConst?` (`findConst` on `decls`),
      `Erasure.PureM.freshFVarId` (the free variable `_pure.<next>`, then `next + 1`),
      `Erasure.PureM.instantiate1` (`Expr.instantiate1'`), `Erasure.PureM.isErasable ls e`
      (`Pure.isErasable ⟨decls⟩ oracleFuel ls e`, whose error it throws),
      `Erasure.PureM.casesInfo?` and `Erasure.PureM.ctorArity?` (always `none`).
  - `LeanToLambdaBox.lean`: imports the new module.
  - new `tests/regress/pure_oracle.lean`, its expected outputs
    `tests/regress/expected/pure_oracle/` (2 files) and
    `tests/regress/expected-peregrine/pure_oracle/` (1 file).
  - `doc/SHIPPING-CHANGES.md`: this entry.
- **Why necessary:** DESIGN Q6 and Q8, S-D. The erasability test of `#erase`, `Erasure.isErasable`,
  runs `Meta.inferType`, `Meta.isProp` and `Meta.isTypeFormerType` in `MetaM`, whose state and
  operations are opaque to proofs, so its answers cannot be proved sound. The verification proves
  that an "erasable" answer of the oracle is sound (`Pure.isErasable_sound`), which needs the
  oracle to be a total function on data: lists of declarations and locals, fuel, and lean4lean's
  `Expr.instantiate1'` and `Expr.liftLooseBVars'`, which are definitions (Lean's
  `Expr.instantiate1` and `Expr.liftLooseBVars` are related to them only by lean4lean's axioms
  `Expr.instantiate1_eq` and `Expr.liftLooseBVars_eq`). The kernel can evaluate it (`decide`). Its
  reductions unfold every definition, as the reductions of MetaRocq's `is_erasableb`
  (`erasure/theories/ErasureFunction.v:894`), at `RedFlags.default`, unfold every constant with a
  body; this is decision 13 of checkpoint 1. `PureM`, its operations and `EraseT.runPure` are the
  backend with which the verified path is to run the traversal of S-16 (S-20 completes the
  backend), and the verification's statements about that run are stated with `EraseT.runPure`.
  The `Meta` oracle `Erasure.isErasable` is unchanged, and `#erase` keeps using it.
- **Behaviour before:** none of these declarations exists. Reproduction:
  `tests/regress/pure_oracle.lean` at the parent commit fails with 49 errors (`Unknown constant
  Pure.isErasable`, `Unknown identifier PureM.isErasable`, `Unknown constant Pure.Ctx`, …); its two
  output files are those expected.
- **Behaviour after:** `#erase` is unchanged: nothing calls the new functions. The kernel evaluates
  the oracle at `oracleFuel` (`decide`), on environments built by hand: the ill-typed spine `hq A a`
  of a proof `hq : Q`, where `Q : Prop := ∀ P : Prop, P → P`, `a : A` and `A : Type`, is kept; the
  proof `hq.{v} : P.{v}` of `P.{v} : Sort v` is kept at the parameter `v` and erased at level `0`;
  with `IProp : Type := Prop`, `R : IProp`, `hR : R`, `Endo : Type := A → A`, `fI : Endo` and
  `a : A`, the oracle types and keeps `fun (_ : R) (x : A) => x` and `fI a`, and erases `R` and
  `hR`. With fuel 1 the oracle fails on `fI a` with `fuel "inferType"`, and with fuel 8 it keeps
  it. `PureM.freshFVarId` from the counter 3 gives `_pure.3`, then `_pure.4`, and leaves 5. Over
  the declarations that `collectDeps` collects from the elaboration environment for
  `pidHR : R := pid hR`, with `IProp` made `@[irreducible]` after `R` and `hR` are declared, the
  oracle erases `R`, `hR` and `pidHR` and keeps `pid.{1}`, while `#erase Irr.pidHR` keeps `R` and
  `hR` (R-14). `instLevel`, `Ctx`, `findLocal`, `oracleFuel`, `PureCtx`, `PureState`, `PureM` and
  the operations of `PureM` other than `isErasable` depend on no axiom; `instLevels`,
  `alwaysZero`, `whnf`, `inferType`, `isArity`, `Pure.isErasable` and `PureM.isErasable` on
  `propext`; `EraseT.runPure` on `propext`, `Classical.choice` and `Quot.sound`, as `EraseT` does
  (the hash maps of `ErasureState` and `TravCtx`). None depends on an axiom of lean4lean. `whnf`,
  `inferType`, `isArity`, `alwaysZero`, `instLevel` and `instLevels` have equation lemmas.
- **Effect on emitted .ast (corpus):** byte-identical for all 704 files; `scripts/corpus-diff.sh`
  against the corpus of S-18 reports 704 identical. The corpus logs are identical except for the
  job counts of `lake` (37 jobs become 38 for the build of the package, 52 become 53 for each
  `lake lean` of the benchmarks) and the addresses in the backtraces of the 4 `PANIC` messages of
  `Defects.lean`.
- **Regression test:** `tests/regress/pure_oracle.lean` proves by `decide`, at `oracleFuel`, the
  oracle's answers above on the three environments built by hand (the environments and terms of
  the verification's register tests `defHead_kept`, `levelDependent_kept` and `irreducibleAlias`,
  DESIGN Q13); proves by `decide` that fuel 1 and fuel 0 give `fuel` and fuel 8 an answer, and
  pins the messages with `#guard_msgs`; proves by `decide` the results of `PureM.findConst?`,
  `casesInfo?`, `ctorArity?` and `isErasable` (its answers, the error it throws on an unknown free
  variable, and the types it reads from a list of locals, one of them with a value), and by `rfl`
  one instance of `PureM.instantiate1`; pins with `#guard_msgs` `PureM.freshFVarId` and a run of
  `EraseT.runPure`; pins with `#guard_msgs` the oracle's answers over the elaboration environment
  on `Irr.R`, `Irr.hR`, `Irr.pidHR` and `Irr.pid.{1}`; and pins the output of `#erase` on
  `Irr.pidHR` (`pidHR.ast`, which peregrine validates). It fails before (49 errors; the outputs are
  the same) and passes after.

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
- **Where:** `LeanToLambdaBox/Erasure.lean`: `visitLiteral`.
- **Reproduction:** `strlit.ast` (`#erase "abc"`) is `(Untyped () (Some tBox))`; in `biglit.ast`
  (`5000000000000000000 : Nat`) the literal is `tBox`. The log contains
  `PANIC at Erasure.visitLiteral`. Both files pass `peregrine validate`.
- **Impact:** silent miscompilation.
- **Why not fixed:** not required by the verification goal unless it later becomes required.

### R-5: An alternative whose Π-type is not syntactic gets a branch without binders

- **What:** a `casesOn` alternative that is not a λ is η-expanded through its inferred type with
  `forallMonocular`, which expects a syntactic `∀`. If the type is a Π only after unfolding, it hits
  `unreachable!`; the panic's default yields a branch with no binders, which no longer matches the
  constructor's arity.
- **Where:** `LeanToLambdaBox/Erasure.lean`: `forallMonocular`, `lambdaMonocularOrIntro`,
  `lambdaOrIntroToArity` (called by `visitAlt`); `withAppEtaToMinArity` has the same
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
- **Where:** `LeanToLambdaBox/Erasure.lean`: `visitLiteral` (Peano branch).
- **Reproduction:** a file containing `import LeanToLambdaBox` and
  `#erase (1000000 : Nat) config {nat := .peano, extern := .preferLogical} to "p.ast"` makes Lean
  abort (exit status 134) with `deep recursion was detected at 'interpreter'`; `200000` succeeds and
  writes 23 601 044 bytes (`5000`: 591 044 bytes). It is not in the corpus because it aborts the
  elaboration.
- **Impact:** Peano mode fails on large literals, and the output grows linearly with the value.
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
- **Where:** `LeanToLambdaBox/Erasure.lean`: `visitCases` (generic path).
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
- **Where:** `LeanToLambdaBox/Erasure.lean`: `visitMutual` (the branch where `ci.value?` is
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
- **Where:** `LeanToLambdaBox/Erasure.lean`: `register_inductive` (`is_struct`), `visitProj`.
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
  `LeanToLambdaBox/Erasure.lean`: `visitMutual`, `mkDef`.
- **Reproduction:** every recursive definition, e.g. corpus `examples/PortProbe/fact.default.ast`:
  `(def (nNamed "Tiny.fact") (tLambda ...) 0)`. A body that is not a λ: corpus
  `examples/UnsafeRec/ugOne.default.ast`, from `unsafe def ug : CN.{0} → CN.{0} :=
  (fun _ n => n) (fun x => ug x)`, has `(def (nNamed "URec.ug") (tApp ...) 0)`, and
  `peregrine validate` rejects it: `Error while checking .URec.ug: Fixpoint body is not a lambda`.
- **Impact:** none observed on recursive definitions whose value is a λ, which includes every
  compiler pre-definition; a recursive `unsafe def` whose value is not a λ gives a program that
  peregrine rejects.
- **Why not fixed:** not required by the verification goal unless it later becomes required.

### R-12: Mutual blocks skip the `@[extern]` and `@[inline]` handling

- **What:** the rules that turn `@[extern]` constants into axioms and record `@[inline]` /
  `@[always_inline]` constants run only for blocks with a single declaration.
- **Where:** `LeanToLambdaBox/Erasure.lean`: `visitMutual`.
- **Reproduction:** `mutual_inline.ast.inlinings` does not list `fooI`, which is `@[inline]` in a
  mutual block. For `@[extern]`: with the default configuration, a recursive `@[extern "f"] def`
  becomes an axiom, while the same definition inside a `mutual` block is erased to its `tFix` (this
  case is not in the corpus).
- **Impact:** inconsistent treatment of attributes; low.
- **Why not fixed:** not required by the verification goal unless it later becomes required.

### R-13: `@[implemented_by]` is ignored

- **What:** the eraser always uses a constant's logical definition, while Lean's compiler runs its
  `@[implemented_by]` implementation. When the two disagree, the erased program and Lean's compiled
  code compute different values.
- **Where:** `LeanToLambdaBox/Erasure.lean`: `visitMutual` (uses `ci.value?`),
  `visitConstApp` (no `implemented_by` check).
- **Reproduction:** `implemented_by.ast` (`fastId 2`, where `fastId n := n + 1` is implemented by
  `slowId n := n`): `#eval fastId 2` prints 2; `peregrine eval implemented_by.ast` prints 3.
- **Impact:** differs from Lean's compiled code for such constants; the logical definition is what
  a proof about the kernel term refers to.
- **Why not fixed:** not required by the verification goal unless it later becomes required.

### R-14: Erasability is decided by the elaborator at default transparency

- **What:** `isErasable` uses `Meta.inferType`, `Meta.isProp` and `Meta.isTypeFormerType`; the last
  one weak-head normalizes at default transparency, which does not unfold `@[irreducible]`
  definitions. A type behind an irreducible alias is therefore kept as a relevant term, and so is
  a proof whose proposition's sort is behind such an alias. Where `Meta.inferType` needs to unfold
  the alias to a Π-type or a sort, `#erase` fails.
- **Where:** `LeanToLambdaBox/Erasure.lean`: `isErasable`.
- **Reproduction:** `irreducible_alias.ast`: `mkT : MyType`, with `@[irreducible] def MyType := Type`,
  is emitted as the declaration `mkT := id □ □` instead of being erased. In the corpus files
  `tests/corpus/IrrAlias.lean` and `tests/corpus/Examples.lean`, with
  `@[irreducible] def IProp : Type := Prop`, `axiom R : IProp` and `axiom hR : R`:
  `examples/IrrAlias/pidHR.default.ast` (`pid hR`) declares the axioms `Irr.R` and `Irr.hR`, and
  `examples/Examples/irrAxiomArg.default.ast` (`guardR hR six`) declares `Ex.hR`. `#erase` of
  `Irr.useFI := fI two`, with `fI : EndoC` and `@[irreducible] def EndoC : Type 1 := CNat → CNat`,
  fails with `function expected`; `#erase` of `Irr.useLamHR := guardR (lamHR two) six`, with
  `theorem lamHR : CNat → R`, fails with `type expected`.
- **Impact:** under-erasure. In `irreducible_alias.ast` the value computed is unaffected; a kept
  proof axiom stops `peregrine eval` (`Axioms found … .Irr.R, .Irr.hR`); and `#erase` refuses
  some programs.
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
  `warning: no targets specified and no default targets configured` and `Nothing to build.`, and
  creates no `.lake`.
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
- **Where:** `LeanToLambdaBox/Erasure.lean`: `visitMutual`, `addAxiom`;
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
  `visitMutual`; `benchmarks/via_malfunction/Makefile` (`ERASURE_CONFIG`).
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

### R-29: A catch-all re-evaluates a discriminant that is not a variable (fixed in S-14)

Fixed in S-14, which describes the defect, its reproduction and the fix. The entry keeps its number
so that references to R-29 stay valid.
