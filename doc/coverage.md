# Coverage — what the theorems reach, and what they do not

Two tables: the five benchmark programs, and the eight rungs of the green ladder. Together
they are the answer to "on what does this development actually say something?", and the rule
is that an uncovered program is named with the reason it is uncovered.

`lake exe coverage` writes this file, `--stdout` prints it and `--check` diffs the two, so a
figure below drifts only if the tree does. The `hrun`, `htbl` and `hsafe` rows are read out of
`doc/trust.md`, whose rows they are.

## What is measured on each run

Every number in this file that a command can produce is produced by one: each emitted `.ast`'s
size and its `tProj`/`tCase`/`tFix` and body-less-declaration counts; each program's reified
`SourceTable`, with the `supportedTerm` verdict at its entry constant and at every tabled
body, the `SupportError` of each erroring body, the fix blocks `Witness.fixBlock?` installs,
the `.proj` heads with their `informativeB` and `succSortB` verdicts, the metadata-headed
spines and `kernameSepB`; the same measurements on the eight committed rung tables; each rung
theorem's presence, the hypotheses it still binds and whether its `hwf` term is declared; every
binder name of each rung's emitted program, under both the retired alphanumeric class and the
printability condition that replaced it; and the constant and λ□-key counts of the environment
`LeanToLambdaBox/Green.lean` elaborates in.

Five things here are prose a reader maintains: the panic reproduction and the erase-run
column (`doc/rework/03-DEV-FIX.md` holds the commands), the wave a rung went green in, N20's
per-program minor counts, the elaboration cost of the eight `hwf` terms, and the
dead-declaration budget. Each is attributed where it appears.

## The five programs

The definitions are the frozen copies `VerifyBench/Src/Arith.lean`, `VerifyBench/Src/Sieve.lean`,
`VerifyBench/Src/Quicksort.lean`, `VerifyBench/Src/BinaryTrees.lean` and
`VerifyBench/Src/Fannkuch.lean`, held against the sibling `benchmarks` repository's originals by
`scripts/frozen.sh`; the roots `VerifyBench/*.lean` add the `#erase` line, which sets
`csimp := false` — every correctness statement needs it, and the frozen originals do not set
it. Sizes are of the `.ast` those runs write.

| Program | `.ast` bytes | Erase run | In the fragment? | Capstone |
|---|---|---|---|---|
| Arith | 14,241 | exit 0, no panic | **yes** — no `SupportError` at the entry term or at any tabled body | the applied capstone's subject, G7/G8 |
| Sieve | 28,555 | exit 0, no panic | **no** — `recursorHead` at `Eq.rec`, through `Bool.noConfusion` (`F-EQREC`) | not a rung; reached only by the general statement |
| BinaryTrees | 30,056 | exit 0, no panic | **no** — `F-EQREC` | not a rung; its `Tree` is one of the first-order witnesses |
| Quicksort | 67,033 | exit 0, **one panic** | **no** — `F-EQREC`, the well-founded `Nat.div.go`/`Nat.modCore.go` route, and `sparseCasesOn` | none: the emitted program is wrong (`F-SPARSE`, `doc/rework/03-DEV-FIX.md`) |
| Fannkuch | 40,808 | exit 0, no panic | **no** — `F-EQREC` and `etaContractedMinor` at `Decidable.casesOn` | not a rung; outside the capstone's fragment at `F-EQREC` and `etaContractedMinor`. `NoBodylessRefs` now **holds** here — `recursorRealizer` gives the reachable `Eq.rec` a body (§2.8's strict gain) — so the exclusion is the fragment check alone, not the capstone's own premise |

The verdict column is the checker's, not a judgement: it is what `supportedTerm` returns over a
`Witness.reify%` table built on the program's entry constant, at the entry term and at every
tabled body. Inside the fragment: **Arith**. The fragment table below gives the erroring bodies
of the others, one row per program.

The panic is `PANIC at Erasure.visitCases LeanToLambdaBox.Erasure:817:55`, and the run still
exits 0 and still writes the file; both commands are in `doc/rework/03-DEV-FIX.md`. Emitted
programs carrying a body-less constant: **none**.

`NoBodylessRefs Σ t` — no constant the emitted program reaches is declared without a body — is
the capstone's premise and is decidable. The closure `ReachableFrom` computes reaches every
declared kername of all five, so the body-less count of the emitted file decides it:
**all five** satisfy it. Before F-QUOT's and F-EQREC's registering exits (§2.8), Fannkuch's
reachable `Eq.rec` was declared body-less and a rung there would have had an uninhabitable
evaluation hypothesis and been vacuously green; `recursorRealizer` now gives it a body
wherever a covered program reaches it, which is the strict gain the realizer census below
records. The closure includes the
inductive block of every `tConstruct`, `tCase` and `tProj` node, which is what
`constructorArity` and `isPropositionalInductive` are answered from.

### The per-program restrictions

N19, N21 and the three fragment restrictions at the end of the list are conjuncts of
`Supported` and are decided by `supportedB` (`LeanToLambdaBox/Supported.lean`). **N20 is not a
conjunct** — it constrains `hev`, T9's evaluation hypothesis, not the eraser's output — so its
entry records a decidable *sufficient* condition, and says what the semantic obligation costs
when that condition fails. **N22 is not a conjunct either**: it is a condition on the *input*,
one clause of the class-**D** binder `TableBlocks`, read at the blocks the run installs a fixvar
map for. `NoBodylessRefs` is the capstone's own premise, decided on the emitted environment.

* **N19** — no under-applied constructor and no under-applied eliminator occurrence: a tabled
  constructor head is applied to at least `numParams + numFields`, a `casesOn` head to at least
  `dp + 1 + nm`. Reported as `SupportError.underAppliedCtor` / `.underAppliedElim`, and reported
  **0 times** over the thirteen tables measured here, so the restriction excludes nothing
  on the corpus though both halves stand: `visitCtorEta`'s saturation loop is not deletable —
  peregrine's `constructors_as_blocks` rewrites an under-applied `tConstruct` spine into a short
  block that `EWellformed.v:171-175` rejects — so the constructor half does **not** disappear
  once F-ETA2 is repaired, the claim `doc/rework/03-DEV-FIX.md`'s F-ETA2 row calls out and
  refutes (C-refute C8). What F-ETA2 fixed is a different defect, upstream of N19 entirely:
  a supplied argument re-erased under the binders the η loop opens, measured contained at 0
  occurrences here.
* **N20** — every ι spine's dropped prefix, every unselected minor and every extra argument has
  a source value. Sufficient condition: each is already a syntactic value. It **fails on all
  five**, and the counts are the carried W3R measurement: non-value minors per total ι spine are
  3/3 at Arith, 25/26 at Sieve, 16/19 at BinaryTrees, 28/40 at Quicksort and 2/2 at Fannkuch,
  with 0 bad prefix arguments everywhere, so `hpres` stays cheap and `hmins` is discharged
  semantically — one `SEval` derivation per unselected branch per ι step. Lean's match compiler
  thunks a nullary branch into an *application*, not a λ: no nullary alternative of any emitted
  program has a `tLambda` head, and `Arith.ast`'s `Nat` zero-branch is
  `(tApp (tRel 1) (tConst Unit.unit))`. That is a cost, not a vacuity — Lean is total, so every
  well-typed closed term normalises and each unselected branch has a value, while partial and
  `unsafe` bodies are outside the fragment through N8.
* **N21** — a recursor head is outside the fragment: it is tabled body-less, so δ cannot fire at
  it; it is neither a constructor nor a type former, so no `SEval` value arm applies; and ι is
  keyed on `casesOn` names. A spine headed by one has no source evaluation at all, so a program
  reaching one would be **vacuously** covered. Reported as `SupportError.recursorHead`.
* **N22** — every definition of an emitted mutual fixpoint block is λ-headed. The emitted reading
  is `LBWfPeregrine.fixLambda` (`LeanToLambdaBox/Output.lean`), carried by the pass relation as
  `LowerBlock.hfl` (`doc/rules-Lower.md`). What supplies it is read on the **input** side, in two
  halves, as clauses of `TableBlocks` (`LeanToLambdaBox/Supported.lean`) at the blocks
  `Witness.fixBlock?` names: `lamHeaded`, the tabled body of every member is λ-headed, and
  `informative`, no member is erasable. The second is a conjunct and not a formality —
  `run_mkDef_box_not_lambda` registers an erasable member with a non-λ body — and it is
  model-side, so no computation reaches it. Measured over the thirteen tables — the eight
  committed rung tables and the five reified on the corpus entry constants: **63 blocks**
  install a fixvar map, **63** of them are singletons, and every member is tabled with a
  λ-headed body (0 untabled members, 0 non-λ bodies). A blanket clause would be
  false on every table: the non-λ tabled bodies are the non-recursive instance constants and the
  rung subjects themselves. `lake exe reify --blocks` is the CI mechanism.
* **`NoBodylessRefs`** — no constant the *emitted* program reaches is declared without a body.
  Measured on the emitted environment, not on the source closure.
* **N18, projection half** — the head of a `.proj` node is a tabled inductive type whose declared
  result sort never evaluates to `Prop`. Without it the emitted `.proj` is stuck on the target at
  every flag point, for the same reason the `casesOn` half covers, and `Erases.proj`'s `hinf` has
  no source. Reported as `SupportError.propElimIntoData` at a non-informative head and
  `.unknownConst` at an untabled one.
* **Metadata heads** — `SupportedTm.mdata` reads a metadata node at the empty spine only, so a
  metadata-wrapped application head is outside the fragment. The restriction is what makes
  `Supported.head` a theorem: `Lean.Expr.getAppFn` does not see through `.mdata`, so at a
  non-empty spine the head the checker approved and the head the run dispatches on are different
  terms. Reported as `SupportError.mdataSpine`. Measured over the thirteen tables: **0**
  application heads are metadata nodes — the restriction excludes nothing on the corpus.
* **Projection shape** — `SupportedTm.proj` carries the block's arity and the field bound: the
  structure's tabled block has exactly one constructor, of `nf` fields, and the field index is
  below `nf`. That is what retires the separate `ProjSupported` premise and what supplies step
  17's dropped-prefix `ProjInfo` through `Supported.projInfo`. Reported as
  `SupportError.projField`, and reported 0 times on the 79 `.proj` nodes of the
  thirteen tables: every head has one reified constructor and every index is in range.
* **Kername separation** — no two tabled names share a λ□ key. `toKername` is not injective
  (`toKername_not_injective`), so two tabled constants can print as one kername and the second
  shadows the first in the emitted environment; the fragment excludes that input, and the block
  conjunct `BlockKeyed` spends the exclusion at the one name step 4 visits. Decided table-wide by
  `kernameSepB` and reported as `SupportError.kernameCollision`. Measured `true` on
  13 of the thirteen tables. The shipping half of the finding — that the eraser emits the
  collision rather than rejecting it — is `F-KERNAME` in `doc/rework/03-DEV-FIX.md`.

Over the whole elaboration environment of `LeanToLambdaBox/Green.lean` the same check is
230,472 constants against 230,472 distinct keys, so no collision is
excluded by the fragment that the environment does not already avoid.

### The nodes each program emits, and the projection heads behind them

The first three columns are the emitted program's; the last four are read on the tabled bodies
the eraser walks, so the `.proj` counts differ — a source projection can be erased away, and a
head is counted once per table.

| Program | `tProj` | `tCase` | `tFix` | source `.proj` | distinct heads | non-informative | non-successor |
|---|---|---|---|---|---|---|---|
| Arith | 10 | 5 | 4 | 10 | 10 | 0 | 5 |
| Sieve | 8 | 28 | 10 | 9 | 9 | 0 | 3 |
| BinaryTrees | 9 | 20 | 10 | 11 | 11 | 0 | 4 |
| Quicksort | 9 | 28 | 11 | 17 | 16 | 0 | 7 |
| Fannkuch | 6 | 39 | 15 | 8 | 8 | 0 | 2 |

The 21 distinct heads across the five programs are typeclass structures and `PProd`:

`Add`, `Append`, `BEq`, `Div`, `HAdd`, `HAppend`, `HDiv`, `HMod`, `HMul`, `HPow`, `HSub`, `LE`, `LT`, `Max`, `Mod`, `Mul`, `NatPow`, `OfNat`, `PProd`, `Pow`, `Sub`

The two verdict columns are what makes N18's projection half free on the corpus. The semantic
criterion `informativeB` — the declared result sort never evaluates to `Prop` — rejects
0 of them. The syntactic criterion rejects 9: the heterogeneous
classes, whose declared result sort is a `max` of successors rather than a successor. Every
tracked program carries at least two such nodes, so the successor form would have emptied the
projection machinery on all five, which is the same false exclusion it makes at `Prod`.

### The fragment table

`Witness.Reify.visit` reads `compilerInfo?` — the `_unsafe_rec` companion first — and tables no
body for a `casesOn`-like head, so the reified table *is* built on compiler bodies and the
"table closure" and the "eraser closure" coincide. The measurement is `supportedTerm` on the
entry constant together with `supportedTerm` on **every** tabled body of `reify% <entry>` — a
superset of `Supported.Reaches`' closure, so a zero here is stronger than the fragment check.
The last column is the census `doc/rework/10-MERGE-FIXES.md` §3.2 asks for: tabled names
shaped like a recursor of a tabled inductive (`isRecursorName`) or a `Quot` primitive
(`quotPrimNames`) — the population F-QUOT's and F-EQREC's registering exits draw from, not a
restriction by itself, since `supportedHead` already refuses every one of them as an
application head regardless of count:

| Program | tabled decls | inds | entry term | erroring bodies | what they are | `NoBodylessRefs` | realizer census |
|---|---|---|---|---|---|---|---|
| Arith | 43 | 12 | `ok` | 0 | — | holds | 0 |
| Sieve | 81 | 17 | `ok` | 2 | `Bool.noConfusion` (recursorHead Eq.ndrec), `Eq.ndrec` (recursorHead Eq.rec) | holds | 2 |
| BinaryTrees | 89 | 21 | `ok` | 2 | `Bool.noConfusion` (recursorHead Eq.ndrec), `Eq.ndrec` (recursorHead Eq.rec) | holds | 2 |
| Quicksort | 126 | 26 | `ok` | 8 | `Bool.noConfusion` (recursorHead Eq.ndrec), `Eq.ndrec` (recursorHead Eq.rec), `Nat.below` (recursorHead Nat.rec), `Nat.brecOn.go` (recursorHead Nat.below), `Nat.div.go` (recursorHead False.rec), `Nat.modCore.go` (recursorHead Nat.brecOn), `Nat.modCore.go._f` (recursorHead False.rec), `quicksort_fuel` (sparseCasesOn quicksort_fuel._sparseCasesOn_1) | holds | 6 |
| Fannkuch | 95 | 18 | `ok` | 5 | `Bool.noConfusion` (recursorHead Eq.ndrec), `Eq.ndrec` (recursorHead Eq.rec), `Eq.ndrec_symm` (recursorHead Eq.ndrec), `countFlipsAux` (etaContractedMinor Decidable.casesOn), `rotatePrefix` (etaContractedMinor Decidable.casesOn) | holds | 2 |

`grep -c '(constant_body None)' VerifyBench/ast/<Program>.ast` is this column's companion by
hand: on the current tree it is 0 on all five — F-QUOT's and F-EQREC's realizer exits give
`Eq.rec` a body wherever a covered program reaches it, and no program's entry term or tabled
closure applies a `Quot` primitive or an untabled recursor as a head, so the residue §3.2 names
— an untabled prefix reaching `recursorRealizer` — is measured absent here rather than assumed
absent everywhere: the capstone's own argument for it is `supportedHead`'s refusal
(`doc/rework/10-MERGE-FIXES.md` §3.2, last paragraph), and this table is the corpus-side check
of that argument's premise, not a substitute for it.

N8's claim — that the compiler bodies the eraser reads carry direct structural recursion rather
than `brecOn` — holds of the tables as they now stand; the `brecOn` verdicts an earlier body
column produced survive only on Quicksort, through the well-founded `Nat.div.go` and
`Nat.modCore.go`. No program is excluded at `Prod`: `informativeB` tests the result sort for
never-zero rather than for a syntactic `Level.succ`, so `Prod`'s `Sort (max (u+1) (v+1))` is
accepted and `Prod.casesOn` is reported `propElimIntoData` nowhere.

Not exercised by any of the five, and recorded so that the gap is visible rather than inferred:
a genuinely **mutual** fixpoint block — every block the run installs a fixvar map for across the
thirteen tables is a singleton, so the fix layer's two-member case is covered only by a
hand-built fixture, and the block machinery is correct by construction over the compiler's SCC
but measured only at self-recursive singletons; `Acc`, `WellFounded` and `Quot` occur in none of
the five; and every emitted inductive is declared non-propositional, so no `Prop`-discriminee
elimination is covered at all (`F-PROP`, and the fragment excludes them through
`Supported.propElimIntoData`).

## The green ladder

Eight rungs under `VerifyBench/Spikes/`, each a real `#erase` run with a committed `.ast` and a
committed `SourceTable`. G1-G7 are closed nullary definitions, following the closed-normal-term
posture of Letouzey's Theorem 15; G8 is the tracked `benchArith` applied to its argument. Each
rung's conclusion ends in a **literal** peano numeral, so it cannot be satisfied by `□` or by a
stuck term.

| Rung | Program | What it adds | Green in |
|---|---|---|---|
| G1 | `spikeZero : Nat := Nat.zero` | constructor constants, inductive declarations, δ | **W1** |
| G2 | `spikeLit : Nat := Nat.succ 3` | the literal rule, the peano tower, the `OfNat` class tower | **W2** |
| G3 | `spikeLet : Nat := let x := 2; Nat.succ x` | ζ in both semantics | **W2** |
| G4 | `spikeProj : Nat := (Prod.mk 1 2).1` | the projection rule, boxed type parameters, polymorphic dependencies | **W2** |
| G5 | `spikeCase : Nat := Nat.casesOn 2 (thunk) (fun n => n)` | `casesOn`, `.case`, ι, and the first constructed `SEval` derivation | **W3** |
| G6 | `spikeFix : Nat := spikeRec 2` | a recursive constant: the compiler-body table, `.fix`, two guarded unfoldings | **W3** |
| G7 | `arithClosed : Nat := benchArith 0` | the typeclass tower: 10 projections, 4 fix blocks, 5 `.case`, a 19-node peano tower | **W5** |
| G8 | `benchArith : Nat → Nat` | a function-typed subject; the applied capstone | **W5** |

Each rung's theorem and the hypotheses it still binds, read off `LeanToLambdaBox.Green`:

| Rung | Theorem | `.ast` bytes | `hcb` | `hev` | `hbridge` | `hargReach` |
|---|---|---|---|---|---|---|
| G1 | elaborates | 354 | — | binder | binder | — |
| G2 | elaborates | 1,556 | binder | binder | binder | — |
| G3 | elaborates | 1,469 | binder | binder | binder | — |
| G4 | elaborates | 2,284 | binder | binder | binder | — |
| G5 | elaborates | 966 | binder | — | binder | — |
| G6 | elaborates | 885 | binder | binder | binder | — |
| G7 | elaborates | 14,625 | binder | binder | binder | — |
| G8 | elaborates | 14,291 | binder | binder | binder | — |

`lenv` and `env` are universally quantified in every rung, so the ladder delivers
**conditional** non-vacuity. No computation can make it unconditional, and this sentence is
where that is said.

What every rung settles by computation is `hcfg`, `hsup` (through `supportedB`'s kernel
verdict), `hwf` and the target-side evaluation, which is what pins the answer to the
literal numeral; at G8 the evaluated term is the emitted term applied to its argument. `hwt`
is settled too, by a checked term rather than a computation: each subject is `#erase <constant>`, so
`Witness.trExprS_const_of_table` builds its `TrExprS` witness from `P`, `htbl` and `hsafe` —
including at G8, whose subject is function-typed, since that lemma reads only the table's level
parameters.

Two class-**C** hypotheses are binders at most rungs, and `doc/trust.md` carries the rows. `hcb`
is discharged at G1 and binds at every other rung — G2, G3, G4, G5, G6, G7, G8. Arith's table has ten
class projections among its tabled bodies, whose typing routes through lean4lean's unproven
`TrProj`, and twenty-eight of its declarations are polymorphic, which G1's monomorphic route
does not reach. `hev` — the source evaluation — is discharged at G5, by `Green.g5_seval`:
δ at the subject, then ι at `Nat.casesOn`, with the discriminant a constructor value, the
selected branch applied to its field, and the *unselected* nullary branch evaluated through its
thunk and the δ step at `Unit.unit` the thunk's argument needs. That is N20's
per-branch obligation, paid.

**No `SEval` witness is constructed at Arith**, and that is a recorded fallback rather than an
oversight: `benchArith 0` runs 45 recursive calls through `Nat.pow`, `Nat.mul`, `Nat.add` and
`Nat.sub`, each a δ on a `.fix`-carrying constant and an ι on its compiled match, and N20 owes
an `SEval` derivation for every unselected minor of every one of them — against a 45-line,
three-`StepDefeq`-binder precedent at G5 for a single δ and ι. The obligation is volume, not
vacuity: Arith is total, so every unselected branch has a value. So `hev` binds at G7 and G8 as
it does at G1-G4 and G6, and T10, non-vacuity, stays demonstrated at G5. The value-side typings
`hvwt` and `hty` are binders at every rung: a rung's value is a constructor spine, not a
constant.

`hwf : LBWfPeregrine Γ t` is a checked term at every rung: `lbWfPeregrine_of_check` reduces
all **twelve** clauses to one Boolean and `Green.g<i>_wf` is `by decide +kernel` on it,
declared at all eight rungs. It is a binder
of the capstone rather than a field of `hbridge`, so no rung assumes what peregrine's first
pass reads. The eight kernel checks cost about twelve seconds of elaboration, most of it at G7
and G8 — a carried figure, re-timed by `lake build LeanToLambdaBox.Green`.

`NoBodylessRefs Γ t` no longer has even `hwf`'s shape: `shipping_erase_correct_firstorder`'s
proof never spent its `hnb` binder, so W8 deletes it from the theorem and from all eight
rungs' applications (`doc/rework/11-REPAIRS-W8.md` §2.8). `Green.g<i>_noBodylessRefs` stays a
standalone `by decide +kernel` term, declared at all eight rungs, and this file's `nbTerm` column is its only remaining reader.

`hbridge` is a binder at every rung too, and it now carries **two** fields, `erasesEnv` and
`lowerEnv`, the environment half: `erasure_bridge_of_run` proves
`Erases env [] [] pe t₀ ∧ Lower Γspec t₀ t` from the run, supplying all eighteen member steps.
Both fields are composed by `bridgeEnv_of_regInv` out of a registration invariant that no
theorem produces for a run of the shipping eraser, and `doc/rework/08-REPAIRS-W5.md` §2.3 names
the three measured obstructions in the way: the eighteen motives are stated at a fixed level
scope while 16 of G7's 30 tabled bodies are erased at their own, `ReifiedDecl.Prepared` pins a
tabled body only up to `Expr.AlphaEq` while `Lower` is not α-closed on its source, and
`RunRefines` reads content at *every* specification environment of the final state where the
repair produces one. The three fields that left the bundle are discharged, not deferred: `wf`
is the `hwf` above, `simulate` is the capstone's own application of `erases_correct` at the
spine — which is what puts that theorem and the arms it composes inside the closure — and
`noBox` is `FOSpine.lower` transporting the constructor-tree shape `firstorder_erases_core`
computes. So what a rung says about the shipping erasure is conditional on the environment half
and on nothing else the bridge once carried; `doc/trust.md` carries the row.

G8 alone binds `hargReach`, the last column above: that the erasure of its subject reaches
`Nat`'s block in the specification environment the capstone produces. It is what remains of the
argument's own `ErasesEnv` conjunct after `Green.g8_argErasesEnv`, and it is a G8 fact because
G1–G7 apply the observable clause at the empty spine.

### The printable-binder finding

`LBWfPeregrine`'s binder-name clause read `Basic.cleanIdent`'s alphanumeric class until the
closing round, and on the emitted output it is **false**: `cleanIdent` is what `toKername`
applies to a **kername identifier**, while a binder name is emitted as a quoted atom
(`Printing.lean`) that peregrine's `Deserialize_ident` accepts in full. Measured over each
rung's emitted program — the term and every constant body of the emitted environment:

| Rung | offending names, alphanumeric class | of them distinct | offending names, printability |
|---|---|---|---|
| G1 | 0 | 0 | 0 |
| G2 | 1 | 1 | 0 |
| G3 | 1 | 1 | 0 |
| G4 | 1 | 1 | 0 |
| G5 | 0 | 0 | 0 |
| G6 | 0 | 0 | 0 |
| G7 | 34 | 32 | 0 |
| G8 | 34 | 32 | 0 |

The offenders at G2-G4 are
`x._@.Init.Prelude.1822880135._hygCtx._hyg.3`, `instOfNatNat`'s binder. G7 and G8 add the hygienic binders the matcher
inlining introduces, and the four `.fix` definition names
`Nat.sub`, `Nat.pow`, `Nat.mul`, `Nat.add`,
which carry a `.`. Under the retired clause five of the eight rungs would have had an
unsatisfiable `wf` field and would have been vacuous; under the printability condition the
clause holds everywhere, and `hwf` is the checked term above. The finding is F6 of
`doc/rework/08-REPAIRS-W5.md` §3.1.

**What a matcher-bearing subject costs the ladder.** `ReifiedDecl.Prepared` — the run clause of
`SourceTableAdequate` — pins the compiler body **up to α**: `Expr.AlphaEq`, an inductive relation
blind to binder names and binder info and to nothing else. `Lean.Compiler.LCNF.inlineMatchers`
draws the `let` binder names it introduces from the name generator, so a declaration whose
preparation inlines a matcher has prepared bodies that agree across runs only up to those names —
which the clause allows. `lake exe reify --check` passes on all eight rung tables; at G7 and G8
it reports five bodies matching up to binder names — `Nat.add`, `Nat.mul`, `Nat.pow`, `Nat.pred`
and `Nat.sub`, the five whose preparation inlines a matcher — and no mismatch, while G1-G6 pass
with no note at all. The λ□ side of the same phenomenon has no transport kit in the tree: the
emitted binder names are the frontend generator's choice and embed the spike module's own name,
so a rung's `.ast` is pinned to that module's name and import line, and `green-check` reports a
rename as a byte diff rather than absorbing it.

A measured note on what a source literal costs. Under `nat := .peano` a `Nat` literal is emitted
as a peano tower, but the source syntax `3` is `@OfNat.ofNat Nat 3 (instOfNatNat 3)`, so `OfNat`,
`OfNat.ofNat` and `instOfNatNat` come with it: G2's emitted environment has five declarations for
a one-line subject, and reaches all five. G4 adds `Prod` and `Prod.fst`, for seven. Every kername
those closures reach is declared with a body, so all four rungs satisfy `NoBodylessRefs` by
`decide +kernel`.

## The permanent binders every rung keeps

Eight binders stand at every rung of the ladder: `P : ErasureSpec`, `htbl :
SourceTableAdequate`, `hsafe : TableSafe`, `E : EraserAsks`, `A : UpstreamAsks`, `hblk :
TableBlocks`, `hcb : CompilerBodies` and `hprep`, together with `hbridge` at its two fields;
`hcb` is discharged at G1, and `doc/trust.md` carries a row per binder and per field. The three
below are the ones a rung can neither discharge nor ever expect to; `lake exe coverage` reads
them out of `doc/trust.md` rather than copying them.

| Binder | What it assumes | External mechanism |
|---|---|---|
| `hrun` | the `#erase` run produced the committed `.ast` | `green-check` re-runs `#erase` and byte-diffs the file; `IO.RealWorld` is opaque, so no Lean proof of this can exist |
| `htbl` | the reified `SourceTable` is the live environment's slice, including the `prepare_erasure` run clause, which pins the compiler body up to α (`Witness.Expr.AlphaEq`: binder names and binder info ignored, nothing else), and `compilerLevels`, that the **compiler** declaration `Lean.Compiler.LCNF.getDeclInfo?` answers with — the `_unsafe_rec` companion where the elaborator emitted one — carries the table's level column, which is the identification the run relies on when `Erasure.visitMutual` installs `lparams := ci.levelParams` from that constant while the table's column and `CompilerBodies` read `lenv.find?` | `lake exe reify --check` compares field by field against the live environment, `compilerLevels` included, and cross-checks `Expr.eqv` against a Boolean written arm-for-arm against the relation |
| `hsafe` | `TableSafe`: every declaration the reified table pins — constants, inductive types and their constructors — is safe in the ambient environment, the one column `SourceTableAdequate` does not record, plus two clauses about the table's own constant column: `notUnsafeRec`, no tabled constant is an `_unsafe_rec` companion, which is the guard `lookup_adequate.declInfo`'s membership arm takes, and `declCtor`, a tabled constant that `lenv` declares a constructor is in the table's constructor column too, which is what `Erasure.visitConstApp` needs to read the fragment's saturation condition at a `getCtorArity?` hit, and `noMaxLevels`, every tabled body is in the `max`-free level fragment, which is the fragment `Erases.instL` transports a body's erasure along and so what `TabledLevels` — `bridgeEnv_of_regInv`'s level-scope premise, which the reachability gate of `ErasesEnv.defns` then hands the δ arm one constant at a time — spends. Load-bearing five times: `Green.g1_compilerBodies`, `supportedB_sound`, `step6`, `step_visitConstApp` and `tabledLevels_of_table` | `lake exe reify --check` reads the live declarations for the three safety clauses; the column is an upstream ask. `notUnsafeRec`, `declCtor` and `noMaxLevels` are decidable on a concrete table, and the first two hold by construction of `Witness.reify%`, whose `.ctorInfo` arm reifies the constructor's own inductive block; no `reify` verb reads any of the three |

## The dead-declaration budget

`lake exe hygiene --dead` reports **240** declarations outside the import closure of
`LeanToLambdaBox/Green.lean` and `LeanToLambdaBox/Capstone.lean`, and the workflow fails above
its budget: a module falling out of the closure is caught, while the standing residue is not
re-litigated at every push. The residue is four things and nothing else: the tooling (107 — 44 in
`Tools/Hygiene.lean`, 41 in `Tools/Coverage.lean`, 11 each in `Tools/Reify.lean` and
`Tools/GreenCheck.lean`), the frozen benchmark sources under `VerifyBench/Src/` (43), the
uniform-erasure module `LeanToLambdaBox/ErasesUniform.lean` (19), and the λ□ optimisation pass
`LeanToLambdaBox/Optimize.lean` (71) — the last two reached by the aggregator and by nothing
else. The count is a measurement of the tree rather than of this file, and is the one figure
here a reader re-runs by hand.

Two movements account for it, and they run in opposite directions. The α-transport kit for the
reified-body clause — 99 declarations, the λ□ α-relation with its transports, which git holds —
is **deleted**: its only possible consumer is a content clause for the registration invariant that
the closing round does not schedule, and a file outside the closure earns a row below only by
naming a scheduled consumer. In the other direction `erases_correct`, the simulation, together
with the δ, ι and projection arms it composes, **entered** the closure: the capstone applies it
at the spine, so the largest single result of the development is now reachable from the
shipping theorem instead of from the aggregator alone.

This paragraph is deliberately outside the section below: `--dead` reads every backticked
`.lean` token in the exception section as an exemption, prose included.

## Exceptions to the no-dead-code rule

Every declaration must sit in the import closure of `LeanToLambdaBox/Green.lean` or
`LeanToLambdaBox/Capstone.lean`; `lake exe hygiene --dead` checks it against this list. A row
is admissible only if it names a **scheduled unit as its consumer**, and its trigger is that
the file is deleted if that unit is not executed. An import into the closure is not a consumer,
and no module gets a standing exemption. An open proof obligation — a hypothesis a theorem
still binds — is not a dead declaration and does not belong here.

The list is **empty**. The closing round schedules no consumer for any file outside the
closure, so the two that remain there are counted in the budget above rather than exempted from
it, and the tooling and the frozen sources are counted with them.
