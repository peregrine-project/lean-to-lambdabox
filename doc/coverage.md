# Coverage — what the theorems reach, and what they do not

Two tables: the five benchmark programs, and the eight rungs of the green ladder. Together
they are the answer to "on what does this development actually say something?", and the rule
is that an uncovered program is named with the reason it is uncovered.

This file is maintained by hand in this cut; `lake exe coverage` (U5.3) will regenerate it
byte-identically from the tree, and `VerifyBench/STATUS.md` is folded into it at the same
time.
The `hrun`, `htbl` and `hsafe` rows below are carried verbatim from `doc/trust.md`, which is
their home.

## The five programs

Sources are the csimp-off duplicates `VerifyBench/{Arith,Sieve,Quicksort,BinaryTrees,
Fannkuch}.lean`; every correctness statement needs `csimp := false`, which the sibling
`benchmarks` repository's frozen originals do not set. Sizes and run results are of the
`.ast` written by `lake env lean VerifyBench/<P>.lean`.

| Program | `.ast` bytes | Erase run | In the fragment? | Capstone |
|---|---|---|---|---|
| Arith | 14,113 | exit 0, no panic | **yes** — no `SupportError` at the entry term or at any tabled body | the applied capstone's subject, G7/G8 (W5) |
| Sieve | 28,207 | exit 0, no panic | **no** — `recursorHead` at `Eq.rec`, through `Bool.noConfusion` (`F-EQREC`) | not a rung; reached only by the general statement |
| BinaryTrees | 29,680 | exit 0, no panic | **no** — `F-EQREC` | not a rung; its `Tree` is one of the first-order witnesses |
| Quicksort | 66,374 | exit 0, **one panic** | **no** — `F-EQREC`, the well-founded `Nat.div.go`/`Nat.modCore.go` route, and `sparseCasesOn` | none: the emitted program is wrong (`F-SPARSE`, `doc/rework/03-DEV-FIX.md`) |
| Fannkuch | 39,861 | exit 0, no panic | **no** — `F-EQREC` and `etaContractedMinor` at `Decidable.casesOn` | **fails `NoBodylessRefs`** and is outside the capstone's domain: it reaches the body-less `Eq.rec` (`F-EQREC`) |

The verdict column is the checker's, not a judgement: it is what `supportedTerm` returns
over a `Witness.reify%` table built on the program's entry constant, at the entry term and
at every tabled body. **Arith is inside the fragment**; the section below gives the erroring
bodies of the other four, one row per program.

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

### The five per-program restrictions

N19 and N21 are conjuncts of `Supported` and are decided by `supportedB`
(`LeanToLambdaBox/Supported.lean`). **N20 is not a conjunct** — it constrains `hev`, T9's
evaluation hypothesis, not the eraser's output — so its column records a decidable
*sufficient* condition, and the paragraph below it says what the semantic obligation costs
when that condition fails. **N22 is not a conjunct either**, and not a bound on programs: it
is a clause of the emitted program's own well-formedness, read at one block.
`NoBodylessRefs` is the capstone's own premise, decided on the emitted environment.

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
* **N22** — every definition of an emitted mutual fixpoint block is λ-headed. This is
  `LBWfPeregrine.fixLambda` (`LeanToLambdaBox/Output.lean`) read at one block, carried by the
  pass relation as `LowerBlock.hfl` (`doc/rules-Lower.md`): λ□'s own `tFix` well-formedness
  rejects anything else and `peregrine` requires it, so it is a property the shipping output
  already has rather than a new demand on source programs. Decidable on the `.ast`, and no
  tracked program fails it — measured **51 of 51** emitted `FixDef` bodies `tLambda` (Arith
  4/4, Sieve 10/10, BinaryTrees 10/10, Quicksort 11/11, Fannkuch 15/15, G6 1/1).
* **`NoBodylessRefs`** — no constant the *emitted* program reaches is declared without a
  body. Measured on the emitted environment, not on the source closure.
* **N18, projection half** — the head of a `.proj` node is a tabled inductive type whose
  declared result sort never evaluates to `Prop`. Without it the emitted `.proj` is stuck on
  the target at every flag point, for the same reason the `casesOn` half covers, and
  `Erases.proj`'s `hinf` has no source. Reported as `SupportError.propElimIntoData` at a
  non-informative head and `.unknownConst` at an untabled one.

**N18's projection half costs the tracked programs nothing**, and the criterion choice is
load-bearing. Measured over the `.proj` nodes of the five emitted `.ast`s:

| Program | `.proj` nodes | distinct heads | rejected by `informativeB` | rejected by `succSortB` |
|---|---|---|---|---|
| Arith | 10 | 10 | **0** | 5 |
| Sieve | 8 | 8 | **0** | 3 |
| BinaryTrees | 9 | 9 | **0** | 4 |
| Quicksort | 9 | 9 | **0** | 4 |
| Fannkuch | 6 | 6 | **0** | 2 |
| all five | 42 | 14 | **0** | 6 |

The fourteen distinct heads are `Add`, `Append`, `BEq`, `HAdd`, `HAppend`, `HMul`, `HPow`,
`HSub`, `Max`, `Mul`, `NatPow`, `OfNat`, `Pow` and `Sub` — every one a typeclass structure.
All fourteen pass the semantic criterion, so the restriction excludes no node on the corpus.
The syntactic successor criterion passes only eight: it rejects the six heterogeneous classes
`HAdd`, `HAppend`, `HMul`, `HPow`, `HSub` and `Pow`, whose declared result sort is a `max` of
successors rather than a successor, and each of the five programs carries at least two such
nodes. So the successor form would have emptied the projection machinery on every tracked
program, which is the same false exclusion it makes at `Prod`.

`Witness.Reify.visit` reads `compilerInfo?` — the `_unsafe_rec` companion first — and tables
no body for a `casesOn`-like head, so the reified table *is* built on compiler bodies and the
"table closure" and the "eraser closure" coincide. The measurement is `supportedTerm` on the
entry constant together with `supportedTerm` on **every** tabled body of `reify% <entry>` — a
superset of `Supported.Reaches`' closure, so a zero here is stronger than the fragment check:

| Program | tabled decls | entry term | N19 | N20 (sufficient condition) | erroring bodies | what they are | `NoBodylessRefs` |
|---|---|---|---|---|---|---|---|
| Arith | 43 | `ok` | **holds** | fails, 3/3 non-value minors | **0** | — | holds |
| Sieve | 81 | `ok` | **holds** | fails, 25/26 | 2 | `Bool.noConfusion` → `Eq.ndrec` → `Eq.rec` (`F-EQREC`) | holds |
| BinaryTrees | 89 | `ok` | **holds** | fails, 16/19 | 2 | `F-EQREC` | holds |
| Quicksort | 126 | `ok` | **holds** | fails, 28/40 | 8 | `F-EQREC`; `Nat.below`/`Nat.brecOn.go`/`Nat.div.go`/`Nat.modCore.go`/`Nat.modCore.go._f` through the well-founded route; `sparseCasesOn` at `quicksort_fuel` | holds |
| Fannkuch | 95 | `ok` | **holds** | fails, 2/2 | 5 | `F-EQREC` three times; `etaContractedMinor` at `Decidable.casesOn`, twice | **fails**: `Eq.rec` |

So **Arith is inside the fragment**: no `SupportError` at any tabled body and none at the
entry term. N8's claim — that the compiler bodies the eraser reads carry direct structural
recursion rather than `brecOn` — holds of the table as it now stands; the `brecOn` verdicts
an earlier body column produced survive only on Quicksort, through the well-founded
`Nat.div.go` and `Nat.modCore.go`. No program is excluded at `Prod`: `informativeB` tests the
result sort for never-zero rather than for a syntactic `Level.succ`, so `Prod`'s
`Sort (max (u+1) (v+1))` is accepted and `Prod.casesOn` is reported `propElimIntoData`
nowhere.

**N19 holds on all five**, at every occurrence and not just at the first: no
`underAppliedCtor` and no `underAppliedElim` anywhere. So the deletion of the two η arms
costs the tracked programs nothing, the R15 contingency is not triggered, and F-ETA2's
containment claim is measured rather than assumed. Its constructor half disappears entirely
once F-ETA2 is repaired: applied-form λ□ evaluates a partially applied constructor spine
natively (`Value.construct_app_val`, `LeanToLambdaBox/Semantics/Values.lean:105`).

N20's sufficient condition **fails on all five**, and the claim that the `match` fragment is
unaffected is false: Lean's match compiler thunks a nullary branch into an *application*, not
a λ. Measured over the emitted alternatives of `VerifyBench/ast/*.ast`, no nullary alternative
anywhere has a `tLambda` head — the heads are `tApp` (5 Arith, 16 BinaryTrees, 29 Fannkuch, 23
Quicksort, 26 Sieve), `tCase` and `tRel` — and `Arith.ast`'s `Nat` zero-branch is
`(tApp (tRel 1) (tConst Unit.unit))`. Non-value minors per total ι spine are the column above;
bad prefix arguments are 0 everywhere, so `hpres` stays cheap. `hmins` is therefore discharged
semantically, one `SEval` derivation per unselected branch per ι step. That is a cost, not a
vacuity: Lean is total, so every well-typed closed term normalises and each unselected branch
has a value, while partial and `unsafe` bodies are outside the fragment through N8. What the
restriction deletes is exactly the derivations where the source converges and eager minor
evaluation would not.

Not exercised by any of the five, and recorded so that the gap is visible rather than
inferred: a genuinely **mutual** fixpoint block — none of the 51 emitted `.fix` nodes has more
than one member, so the fix layer's two-member case is covered only by a hand-built fixture;
`Acc`, `WellFounded` and `Quot` occur in none of the five; and every emitted inductive is
declared non-propositional, so no `Prop`-discriminee elimination is covered at all (`F-PROP`,
and the fragment excludes them through `Supported.propElimIntoData`).

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
| G5 | `spikeCase : Nat := Nat.casesOn 2 (thunk) (fun n => n)` | `casesOn`, `.case`, ι, and the first constructed `SEval` derivation | **W3, green** |
| G6 | `spikeFix : Nat := spikeRec 2` | a recursive constant: the compiler-body table, `.fix`, two guarded unfoldings | **W3, green** |
| G7 | `arithClosed : Nat := benchArith 0` | the typeclass tower: 10 projections, 4 fix blocks, 5 `.case`, a 19-node peano tower | W5 |
| G8 | `benchArith : Nat → Nat` | a function-typed subject; the applied capstone | W5 |

`lenv` and `env` are universally quantified in every rung, so the ladder delivers
**conditional** non-vacuity. No computation can make it unconditional, and this sentence is
where that is said.

What each of G1-G6 settles by computation is `hcfg`, `hsup` (through `supportedB`'s kernel
verdict), `hnb` and the target-side evaluation, which is what pins the answer to the literal
numeral. `hwt` is settled too, at every rung, by a checked term rather than a computation:
each subject is `#erase <constant>`, so `Witness.trExprS_const_of_table` builds its `TrExprS`
witness from `P`, `htbl` and `hsafe`.

Two class-**C** hypotheses are binders at most rungs, and `doc/trust.md` carries the rows.
`hcb` is discharged at G1 and not at G2-G6. `hev` — the source evaluation — is discharged at
**G5**, by `Green.g5_seval`: δ at the subject, then ι at `Nat.casesOn`, with the discriminant
a constructor value, the selected branch applied to its field, and the *unselected* nullary
branch evaluated through its thunk and the δ step at `Unit.unit` the thunk's argument needs.
That is N20's per-branch obligation, paid. At G1-G4 and G6 `hev` is still a binder, and there
a rung says that the conditions are consistent with a literal answer, not that they hold. The
value-side typings `hvwt` and `hty` are binders at every rung: a rung's value is a
constructor spine, not a constant.

`hbridge` is a binder at every rung too, and it is the largest one: the eight-field
`ErasureBridge` bundle that ties the emitted program to a specification environment erasing
the subject. Its first two fields would come from `visitExpr_refines_erasesLB`, which is
proved but takes the erasure's eighteen member steps as hypotheses; four of those — the
`visitConstructor`, `visitConst`, `visitProj` and `visitCases` steps — have no supplier, and
the `visitConst` one is refuted at a mutual-block reader. `doc/trust.md` carries the row.
Until it is discharged, what a rung says about the shipping erasure is conditional on the
bundle, and the bridge modules sit outside the import closure of `Green.lean` and
`Capstone.lean` because nothing consumes them yet.

**What a matcher-bearing subject costs the ladder, and what it no longer costs.**
`ReifiedDecl.Prepared` — the run clause of `SourceTableAdequate` — pins the compiler body
**up to α**: `Expr.AlphaEq`, an inductive relation blind to binder names and binder info and
to nothing else. `Lean.Compiler.LCNF.inlineMatchers` draws the `let` binder names it
introduces from the name generator, so a declaration whose preparation inlines a matcher has
prepared bodies that agree across runs only up to those names — which the clause now allows.
Measured: a table reified on `match 3 with …` and one reified on `Nat.add 2 3` both pass
`lake exe reify --check`, each with a `tabled body matches up to binder names` note and no
mismatch, so `htbl` is inhabited for them. G5 and G6 keep their `Nat.casesOn` and
hand-written recursive subjects, which are matcher-free and pass with no note; `lake exe
reify --check` passes on all six rung tables. What G7/G8 still need is the list in
`doc/rework/05-REPAIRS-W3.md` §11: a rung subject a library module can name (the
`VerifyBench/Src/` split), `hsup` and `hnb` — both measured clear on Arith — the target
evaluation by `lbEval` on the committed `.ast`, and `hwt` by
`Witness.trExprS_const_of_table`.

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
| `htbl` | the reified `SourceTable` is the live environment's slice, including the `prepare_erasure` run clause, which pins the compiler body up to α (`Witness.Expr.AlphaEq`: binder names and binder info ignored, nothing else) | `lake exe reify --check` compares field by field against the live environment, and cross-checks `Expr.eqv` against a Boolean written arm-for-arm against the relation |
| `hsafe` | `TableSafe`: every declaration the reified table pins — constants, inductive types and their constructors — is safe in the ambient environment, the one column `SourceTableAdequate` does not record. Load-bearing twice: `Green.g1_compilerBodies` and `supportedB_sound`, which reads it to put a tabled name in the model | `lake exe reify --check` reads the live declarations; the column is an upstream ask |

## Exceptions to the no-dead-code rule

Every declaration must sit in the import closure of `LeanToLambdaBox/Green.lean` or
`LeanToLambdaBox/Capstone.lean`; `lake exe hygiene --dead` checks it against this list. A row
is admissible only if it names a **scheduled W6 unit as its consumer**, and its trigger is
that the file is deleted if that unit is not executed this cycle. An import into the closure
is not a consumer, and no module gets a standing exemption.

| File | Consumer | Trigger |
|---|---|---|
| `LeanToLambdaBox/Optimize.lean` | U6.2, the pass corollary over the non-block constructor regimes | deleted if U6.2 is not executed this cycle |
