# Coverage — what the theorems reach, and what they do not

Two tables: the five benchmark programs, and the eight rungs of the green ladder. Together
they are the answer to "on what does this development actually say something?", and the rule
is that an uncovered program is named with the reason it is uncovered.

This file is maintained by hand in this cut; `lake exe coverage` (U5.3) will regenerate it
byte-identically from the tree, and `VerifyBench/STATUS.md` retires into it at the same time.
The `hrun`, `htbl` and `hwt` rows below are carried verbatim from `doc/trust.md`, which is
their home.

## The five programs

Sources are the csimp-off duplicates `VerifyBench/{Arith,Sieve,Quicksort,BinaryTrees,
Fannkuch}.lean`; every correctness statement needs `csimp := false`, which the sibling
`benchmarks` repository's frozen originals do not set. Sizes and run results are of the
`.ast` written by `lake env lean VerifyBench/<P>.lean`.

| Program | `.ast` bytes | Erase run | In the fragment? | Capstone |
|---|---|---|---|---|
| Arith | 14,113 | exit 0, no panic | yes | the applied capstone's subject, G7/G8 (W5) |
| Sieve | 28,207 | exit 0, no panic | yes | not a rung; reached only by the general statement |
| BinaryTrees | 29,680 | exit 0, no panic | yes | not a rung; its `Tree` is one of the first-order witnesses |
| Quicksort | 66,374 | exit 0, **one panic** | **no** — `SupportError.sparseCasesOn` | none: the emitted program is wrong (`F-SPARSE`, `doc/rework/03-DEV-FIX.md`) |
| Fannkuch | 39,861 | exit 0, no panic | yes, with one caveat | needs an `AxiomRealizer` row for `Eq.rec`: its `hax` is false without one (`F-EQREC`) |

Two measurements behind the table: the panic is
`PANIC at Erasure.visitCases LeanToLambdaBox.Erasure:817:55`, and the run still exits 0 and
still writes the file; `Fannkuch.ast` is the only one of the five carrying a body-less
constant, `((MPdot (MPfile ()) "Eq") "rec")`. Both commands are in `doc/rework/03-DEV-FIX.md`.

Not exercised by any of the five, and recorded so that the gap is visible rather than
inferred: a genuinely **mutual** fixpoint block — 0 of the 50 emitted `FixDef`s are mutual,
so the fix layer's two-member case is covered only by a hand-built fixture; `Acc`,
`WellFounded` and `Quot` occur in none of the five; and every emitted inductive is declared
non-propositional, so no `Prop`-discriminee elimination is covered at all (`F-PROP`, and the
fragment excludes them through `Supported.propElimIntoData`).

## The green ladder

Eight rungs under `VerifyBench/Spikes/`, each a real `#erase` run with a committed `.ast` and
a committed `SourceTable`. G1-G7 are closed nullary definitions, following the closed-normal-
term posture of Letouzey's Theorem 15; G8 is the tracked `benchArith`. Each rung's conclusion
ends in a **literal** peano numeral, so it cannot be satisfied by `□` or by a stuck term.

| Rung | Program | What it adds | Green in |
|---|---|---|---|
| G1 | `spikeZero : Nat := Nat.zero` | constructor constants, inductive declarations, δ | W1 |
| G2 | `spikeLit : Nat := Nat.succ 3` | the literal rule, the peano tower | W2 |
| G3 | `spikeLet : Nat := let x := 2; Nat.succ x` | ζ in both semantics | W2 |
| G4 | `spikeProj : Nat := (Prod.mk 1 2).1` | the projection rule, boxed type parameters, polymorphic dependencies | W2 |
| G5 | `spikeCase : Nat := match 3 with …` | matcher inlining, `casesOn`, `.case`, ι | W3 |
| G6 | `spikeFix : Nat := Nat.add 2 3` | `_unsafe_rec`, the compiler-body table, `.fix` | W3 |
| G7 | `arithClosed : Nat := benchArith 0` | the typeclass tower: 10 projections, 4 fix blocks, 5 `.case`, a 19-node peano tower | W5 |
| G8 | `benchArith : Nat → Nat` | a function-typed subject; the applied capstone | W5 |

`lenv` and `env` are universally quantified in every rung, so the ladder delivers
**conditional** non-vacuity. No computation can make it unconditional, and this sentence is
where that is said.

## The permanent binders every rung keeps

| Binder | What it assumes | External mechanism |
|---|---|---|
| `hrun` | the `#erase` run produced the committed `.ast` | `green-check` re-runs `#erase` and byte-diffs the file; `IO.RealWorld` is opaque, so no Lean proof of this can exist |
| `htbl` | the reified `SourceTable` is the live environment's slice, including the `prepare_erasure` run clause | `lake exe reify --check` compares field by field against the live environment |
| `hwt` | the subject's `TrExprS` witness, until the checker-routed witness lands (U3.4) | lean4lean's checker, run on the subject |

## Exceptions to the no-dead-code rule

Every declaration must sit in the import closure of `LeanToLambdaBox/Green.lean` or
`LeanToLambdaBox/Capstone.lean`; `lake exe hygiene --dead` checks it against this list. A row
is admissible only if it names a **scheduled W6 unit as its consumer**, and its trigger is
that the file is deleted if that unit is not executed this cycle. An import into the closure
is not a consumer, and no module gets a standing exemption.

| File | Consumer | Trigger |
|---|---|---|
| `LeanToLambdaBox/Optimize.lean` | U6.2, the pass corollary over the non-block constructor regimes | deleted if U6.2 is not executed this cycle |
