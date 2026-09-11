# Coverage — what the theorems reach, and what they do not

Two tables: the five benchmark programs, and the eight rungs of the green ladder. Together
they are the answer to "on what does this development actually say something?", and the rule
is that an uncovered program is named with the reason it is uncovered.

This file is maintained by hand in this cut; `lake exe coverage` (U5.3) will regenerate it
byte-identically from the tree, and `VerifyBench/STATUS.md` is folded into it at the same
time.
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
| Fannkuch | 39,861 | exit 0, no panic | yes, with one caveat | **fails `NoBodylessRefs`** and is outside the capstone's domain: it reaches the body-less `Eq.rec` (`F-EQREC`) |

Two measurements behind the table: the panic is
`PANIC at Erasure.visitCases LeanToLambdaBox.Erasure:817:55`, and the run still exits 0 and
still writes the file; `Fannkuch.ast` is the only one of the five carrying a body-less
constant, `((MPdot (MPfile ()) "Eq") "rec")`. Both commands are in `doc/rework/03-DEV-FIX.md`.

`NoBodylessRefs Σ t` — no constant the emitted program reaches is declared without a body —
is the capstone's premise and is decidable. Measured over the five emitted environments, by
the closure `ReachableFrom` computes: Arith, Sieve, BinaryTrees and Quicksort satisfy it;
**Fannkuch does not**, because its reachable `Eq.rec` is declared `(constant_body None)`, so
a Fannkuch rung's evaluation hypothesis is uninhabitable and the rung would be vacuously
green. The same closure reaches every declared kername of all five — the eraser prunes to
exactly what the program reads — and it now includes the inductive block of every
`tConstruct`, `tCase` and `tProj` node, which is what `constructorArity` and
`isPropositionalInductive` are answered from.

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
| G1 | `spikeZero : Nat := Nat.zero` | constructor constants, inductive declarations, δ | **W1, green** |
| G2 | `spikeLit : Nat := Nat.succ 3` | the literal rule, the peano tower, the `OfNat` class tower | **W2, green** |
| G3 | `spikeLet : Nat := let x := 2; Nat.succ x` | ζ in both semantics | **W2, green** |
| G4 | `spikeProj : Nat := (Prod.mk 1 2).1` | the projection rule, boxed type parameters, polymorphic dependencies | **W2, green** |
| G5 | `spikeCase : Nat := match 3 with …` | matcher inlining, `casesOn`, `.case`, ι | W3 |
| G6 | `spikeFix : Nat := Nat.add 2 3` | `_unsafe_rec`, the compiler-body table, `.fix` | W3 |
| G7 | `arithClosed : Nat := benchArith 0` | the typeclass tower: 10 projections, 4 fix blocks, 5 `.case`, a 19-node peano tower | W5 |
| G8 | `benchArith : Nat → Nat` | a function-typed subject; the applied capstone | W5 |

`lenv` and `env` are universally quantified in every rung, so the ladder delivers
**conditional** non-vacuity. No computation can make it unconditional, and this sentence is
where that is said.

What each of G1-G4 settles by computation is `hcfg`, `hsup` (through `supportedB`'s kernel
verdict), `hnb` and the target-side evaluation, which is what pins the answer to the literal
numeral. Two class-**C** hypotheses are still binders and `doc/trust.md` carries the rows:
`hcb` is discharged at G1 and not at G2-G4, whose reified tables carry the class projection
`OfNat.ofNat`, and `hev` — the source evaluation — is inhabited at **no** rung yet, the first
`SEval` derivation being G3's `green_G5`. Until then a rung says that the conditions are
consistent with a literal answer, not that they hold.

A measured note on what a source literal costs. Under `nat := .peano` a `Nat` literal is
emitted as a peano tower, but the source syntax `3` is `@OfNat.ofNat Nat 3 (instOfNatNat 3)`,
so `OfNat`, `OfNat.ofNat` and `instOfNatNat` come with it: G2's emitted environment has five
declarations for a one-line subject, and reaches all five. G4 adds `Prod` and `Prod.fst`,
for seven. Every kername those closures reach is declared with a body, so all four rungs
satisfy `NoBodylessRefs` by `decide +kernel`.

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
