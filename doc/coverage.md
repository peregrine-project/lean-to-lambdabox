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
| Arith | 14,113 | exit 0, no panic | **no** — `recursorHead` at `Nat.brecOn` | the applied capstone's subject, G7/G8 (W5) |
| Sieve | 28,207 | exit 0, no panic | **no** — `recursorHead` at `List.below` | not a rung; reached only by the general statement |
| BinaryTrees | 29,680 | exit 0, no panic | **no** — `recursorHead` at `Nat.brecOn` | not a rung; its `Tree` is one of the first-order witnesses |
| Quicksort | 66,374 | exit 0, **one panic** | **no** — `recursorHead` at `Nat.brecOn`, and `sparseCasesOn` | none: the emitted program is wrong (`F-SPARSE`, `doc/rework/03-DEV-FIX.md`) |
| Fannkuch | 39,861 | exit 0, no panic | **no** — `recursorHead` at `Nat.brecOn` | **fails `NoBodylessRefs`** and is outside the capstone's domain: it reaches the body-less `Eq.rec` (`F-EQREC`) |

The verdict column is the checker's, not a judgement: it is the first error
`supportedTerm` plus `checkNames` return over the dependency closure of a
`Witness.reify%` table built on the program's entry constant. **No tracked program is
inside the fragment**, and the section below says which restriction takes each one out
and which of the two closures is responsible.

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

### The four per-program restrictions

Three of the four are conjuncts of `Supported` and are decided by `supportedB`
(`LeanToLambdaBox/Supported.lean`). **N20 is not a conjunct** — it constrains `hev`, T9's
evaluation hypothesis, not the eraser's output — so its column records a decidable
*sufficient* condition, and the paragraph below it says what the semantic obligation costs
when that condition fails.

* **N19** — no under-applied constructor and no under-applied eliminator occurrence: a tabled
  constructor head is applied to at least `numParams + numFields`, a `casesOn` head to at
  least `dp + 1 + nm`. Reported as `SupportError.underAppliedCtor` / `.underAppliedElim`.
* **N20** — every ι spine's dropped prefix, every unselected minor and every extra argument
  has a source value. Sufficient condition: each is already a syntactic value.
* **N21** — a recursor head is outside the fragment: it is tabled body-less, so δ cannot fire
  at it; it is neither a constructor nor a type former, so no `SEval` value arm applies; and
  ι is keyed on `casesOn` names. A spine headed by one has no source evaluation at all, so a
  program reaching one would be **vacuously** covered. Reported as
  `SupportError.recursorHead`.
* **`NoBodylessRefs`** — no constant the *emitted* program reaches is declared without a
  body. Measured on the emitted environment, not on the source closure.

| Program | N19 | N20 (sufficient condition) | N21 | `NoBodylessRefs` |
|---|---|---|---|---|
| Arith | **holds** | fails, 3/3 non-value minors | fails: `Nat.brecOn`, `Nat.rec`, `Nat.below` | holds |
| Sieve | **holds** | fails, 25/26 | fails: 10 heads, incl. `List.rec`, `Nat.brecOn`, `Eq.rec` | holds |
| BinaryTrees | **holds** | fails, 16/19 | fails: 14 heads, incl. `Tree.rec`, `Tree.brecOn` | holds |
| Quicksort | **holds** | fails, 28/40 | fails: 14 heads, incl. `False.rec`, `Prod.rec` | holds |
| Fannkuch | **holds** | fails, 2/2 | fails: `Nat.brecOn`, `Nat.rec`, `Nat.below` | **fails**: `Eq.rec` |

**N19 holds on all five**, in both closures below and at every occurrence, not just at the
first: no `underAppliedCtor` and no `underAppliedElim` anywhere. So the deletion of the two η
arms costs the tracked programs nothing, the R15 contingency is not triggered, and F-ETA2's
containment claim is measured rather than assumed. Its constructor half disappears entirely
once F-ETA2 is repaired: applied-form λ□ evaluates a partially applied constructor spine
natively (`Value.construct_app_val`, `LeanToLambdaBox/Semantics/Values.lean:105`).

**N21 fails on all five**, and the closure it is measured over decides how badly. Two
closures answer the question, because `Supported.Reaches` and the eraser do not read the same
bodies:

* the **table closure** — `Reaches` over a `Witness.reify%` table, which is what `supportedB`
  actually decides. `Reify.visit` tables `ConstantInfo.value` prepared
  (`Witness/SourceTable.lean:215`), i.e. the **kernel** body, and it tables the bodies of
  `casesOn`-like heads. So `Nat.add`, `Nat.mul`, `Nat.sub`, `Nat.pow`, `List.append` come in
  `brecOn`-mediated, and `Nat.casesOn`/`Nat.brecOn`/`Nat.below` come in with bodies naming
  `Nat.rec`. Every recursor in the table column above arrives this way.
* the **eraser closure** — the bodies `Erasure.visitMutual` reads, which are
  `Compiler.LCNF.getDeclInfo?`'s (`LeanToLambdaBox/Erasure.lean:861`), with the body of a
  `casesOn`-like head not traversed at all, because `visitConstApp` dispatches it to a `.case`
  node. Over that closure Arith is **clean** — no `SupportError` at any occurrence — and the
  other four are left with exactly one recursor route, `Bool.noConfusion` → `Eq.ndrec` →
  `Eq.rec` (Fannkuch also `Eq.ndrec_symm`), which is `F-EQREC` again. The emitted programs
  agree: `grep` over `VerifyBench/ast/*.ast` finds no recursor kername at all in Arith,
  Sieve, BinaryTrees or Quicksort, and only `Eq.rec`/`Eq.ndrec` in Fannkuch.

N8's claim — that the compiler bodies the eraser reads carry direct structural recursion
rather than `brecOn` — is therefore **confirmed for the eraser and false for the table**. The
gap is `Reify.visit`'s body column, not the fragment. A table built on compiler bodies takes
Arith into the fragment outright, with no `SupportError` at any occurrence; Sieve is left
with `F-EQREC` alone; BinaryTrees, Quicksort and Fannkuch are left with `F-EQREC` plus holes
of their own — Quicksort's `sparseCasesOn` (`F-SPARSE`), Fannkuch's two `etaContractedMinor`
occurrences at `Decidable.casesOn`, and the `propElimIntoData` false exclusion at `Prod`
described below.

N20's sufficient condition **fails on all five**, and the earlier claim that the `match`
fragment is unaffected is false: Lean's match compiler thunks a nullary branch into an
*application*, not a λ. Measured over the emitted alternatives of `VerifyBench/ast/*.ast`, no
nullary alternative anywhere has a `tLambda` head — the heads are `tApp` (5 Arith, 16
BinaryTrees, 29 Fannkuch, 23 Quicksort, 26 Sieve), `tCase` and `tRel` — and `Arith.ast`'s
`Nat` zero-branch is `(tApp (tRel 1) (tConst Unit.unit))`. Non-value minors per total ι spine
are the column above; bad prefix arguments are 0 everywhere, so `hpres` stays cheap. `hmins`
is therefore discharged semantically, one `SEval` derivation per unselected branch per ι
step. That is a cost, not a vacuity: Lean is total, so every well-typed closed term
normalises and each unselected branch has a value, while partial and `unsafe` bodies are
outside the fragment through N8. What the restriction deletes is exactly the derivations
where the source converges and eager minor evaluation would not.

One measured false exclusion, recorded so that the rows above are read correctly.
`informativeB` tests the result sort syntactically for `Level.succ`, and `Prod`'s declared
type ends in `Sort (max (u+1) (v+1))`, whose level is `Level.max (succ u) (succ v)` — not a
`Level.succ`. So `Prod.casesOn` is reported `propElimIntoData` on Quicksort, BinaryTrees and
Fannkuch although `Prod` is informative. It is a conservative error, never an unsound one,
and it is the reason BinaryTrees' pre-existing "in the fragment: yes" row was not a
measurement.

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
