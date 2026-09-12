# Trust — provenance for the measured ledger

`test/ledger.expected` holds exactly the `#print axioms` output of `test/Ledger.lean` and
nothing else; `scripts/ledger.sh` re-measures it and the wave gate diffs it. That is what a
diff can check. `#print axioms` reports `sorryAx` as one flat name with **no provenance**, so
provenance lives here, and no acceptance test claims to have measured it. This file is the
only prose ledger in the repository.

Its live rows are the results of `doc/rework/01-DESIGN.md` §4.14 that exist: `erases_correct`
with its folded form, its three step arms and the aggregator they feed, the two first-order
results, `simulate_of_erases_correct`, `LowerBlock.lambda_of_fixLambda`, `Lower.constToFix`,
`shipping_erase_correct_firstorder`, `green_G1`-`green_G6` with `green_G5`'s source
evaluation, and the three §5 results already standing — `SEval.defeq`, `LBOptimize_correct`,
`lbEval_sound`. The two `visitExpr_refines_*` bridges (W4) and `green_G8` (W5) are commented
out in `test/Ledger.lean` and are uncommented by the wave that proves them. A second fixture,
`test/erasesLB.expected` (`scripts/erasesLB.sh`), measures the composite's introduction
lemmas — statement and footprint — so a premise silently added to or dropped from `ErasesLB`
shows as a diff.

Five classes are used throughout, in decreasing strength:

| Class | Meaning |
|---|---|
| **A** | proved here, footprint within `[propext, Classical.choice, Quot.sound]` |
| **B** | proved here, footprint additionally contains `sorryAx` inherited from lean4lean — in the ledger, `SEval.defeq` |
| **C** | a hypothesis of a stated theorem — visible in the statement a reader checks |
| **D** | a permanent named binder, mechanised outside Lean (`lake exe green-check`) |
| **E** | a scope restriction or a fact about a consumer, stated and not formalised |

## (a) Where `sorryAx` comes from

### (a1) lean4lean, inherited

The pinned revision is `20ec229f1a8c6358f3b3852c4e27d2be523d1b87`; sites below are relative
to `.lake/packages/lean4lean/Lean4Lean/`.
`scripts/lean4lean-sorries.sh` lists every `sorry` in the package and diffs it against
`test/lean4lean-sorries.expected`; the entries that reach this development do so through
`TrExprS.uniq` and `IsDefEq.uniqU`:

| Declaration | Site |
|---|---|
| `VEnv.IsDefEqU.sort_inv` | `Theory/Typing/Injectivity.lean:12` |
| `VEnv.IsDefEqU.forallE_inv_stratified` | `Theory/Typing/Injectivity.lean:21` |
| `VEnv.IsDefEqU.sort_forallE_inv` | `Theory/Typing/Injectivity.lean:34` |
| `VEnv.IsDefEqU.weakN_iff` | `Theory/Typing/UniqueTyping.lean:174` |
| `VEnv.NormalEq.parRed` | `Theory/Typing/ChurchRosser.lean:1193,1212` |

### (a2) lean4lean, fork-authored

`VEnv.WF.patsStrong` (`Theory/Typing/EnvLemmas.lean:334`) is **not** inherited from upstream:
it is the ι residue consolidated by the fork's own redesign. Every use of the substitution
family and of the primitives layer that demands `OrderedStrong` rather than `Ordered` routes
through `VEnv.WF.orderedStrong`, which carries it. Stating that this root is fork-authored
rather than upstream is a fact no other document in this repository records.

Also `sorry` at the pin, and load-bearing only for an upstream ask rather than for a theorem
here: `addDecl.WF`'s `inductDecl` case (`Verify/Environment.lean:208`), and the executable
checker's `TrProj.weak'_inv`/`TrProj.uniq` (`Verify/Typing/Lemmas.lean:747,995`).

### (a3) The executable-checker cluster

Discharging the relevance oracle against lean4lean's *executable* checker — rather than
assuming its soundness — brings in a cluster of 33 axioms, of which 29 are non-standard
lean4lean or Lean-core names and two are Lean core's `_native.bv_decide`. The cluster is the
price of criterion 9, and the alternative is named in `doc/rework/01-DESIGN.md` §8.1: revert
the kernel reroute (about 40 lines in 5 hunks) and keep the oracle's reflection clause as a
class-**D** binder instead. The measuring command is `#print axioms` on the capstone, i.e.
the ledger fixture itself; the classification of each name is this row's business.

### (a4) What the projection arm and the δ arm do **not** add

Measured, not assumed. The projection arm's footprint is the ι arm's, name for name:
`Lean4Lean.TrProj.uniq`, `VEnv.IsDefEqU.forallE_inv_stratified`,
`VEnv.IsDefEqU.sort_forallE_inv`, `VEnv.IsDefEqU.sort_inv`, `VEnv.WF.patsStrong`. `TrProj.uniq`
is already inside `SEval.defeq`'s footprint, reaching it through `TrExprS.uniq`, and the two
entirely open projection lemmas of the executable checker — `inferProj.WF` and
`inferProj.WF_struct` (`Verify/TypeChecker/InferType.lean:392,407`) — do not appear at all,
because `step_proj_of_projSpec` *consumes* a `TrProj` from `TrExprS.proj`'s own premise and
never builds one. So the `TrProj` exposure at a projection is **inhabitation**, not axioms: a
projection in a real program has a `TrExprS` derivation only through `inferProj.WF`, which is
`sorry` at the pin, so the proj arm is non-vacuous only on hand-built witnesses.

The δ arm brings in no `instantiateLevelParams` axiom cluster: `ErasesEnv.defns` is already
quantified over the instantiation, so `step_delta` names no lemma about
`Expr.instantiateLevelParams` and the cluster has no subject in the ledger. Where it does
appear is `RegInvShape'.defns`/`.erasesEnv` and `erases_any_scope_of_paramFree`
(`LeanToLambdaBox/ColdStartShape.lean`, `LeanToLambdaBox/SpecEnv.lean`), which inherit
lean4lean's `Erases.instL` footprint verbatim: `Expr.mkAppData_eq`, `Expr.mkData_eq`,
`Expr.replace_eq`, `Level.hasParam_eq` and two `_native.bv_decide` axioms. None of those
declarations is a ledger subject.

## (b) Class-**D**: permanent named binders

Each is a hypothesis no Lean term can discharge, mechanised outside the kernel instead. They
appear by name in the statements that take them, and `lake exe green-check` is the mechanism.

| Binder | What it assumes | External mechanism |
|---|---|---|
| `hrun` | the `#erase` run produced the committed `.ast` | `green-check` re-runs `#erase` and byte-diffs the file; `IO.RealWorld` is opaque, so no Lean proof of this can exist |
| `htbl` | the reified `SourceTable` is the live environment's slice, including the `prepare_erasure` run clause | `lake exe reify --check` compares field by field against the live environment |
| `hsafe` | `TableSafe`: every declaration the reified table pins — constants, inductive types and their constructors — is safe in the ambient environment, the one column `SourceTableAdequate` does not record. Load-bearing twice: `Green.g1_compilerBodies` and `supportedB_sound`, which reads it to put a tabled name in the model | `lake exe reify --check` reads the live declarations; the column is an upstream ask |
| `env_connect` | the ambient `Lean.Environment` is `TrEnv`-related to the `VEnv` the specification quantifies over | upstream ask 4 would derive it |
| `lookup_adequate` | a run's constant and inductive lookups agree with the specification environment | — |
| `fresh_names` | the run's fresh `FVarId`s are fresh | — |
| `oracle_refl` (reflection clause) | the monadic oracle run reflects the kernel predicate | near-definitional; the discharge's price is (a3) |
| `oracle_meta` | the `isErasableMeta` fallback and the polymorphic-scope arm are sound | empirically dead on the error route: 0 fallback hits in 139,196 constants |
| `decl_adequate` | inductive metadata of the run matches the specification's | kept only with the obstruction named; upstream ask 4 |

`hwt` is not in this table. Every rung's subject is `#erase <constant>`, so its `TrExprS`
witness is a checked term: `Witness.trExprS_const_of_table` builds it from `P`, `htbl` and
`hsafe` with a `by rfl` side condition on the reified table, and its footprint is class **A**
(`LeanToLambdaBox/Witness/TrWitness.lean`). The value-side twins `hvwt` and `hty` are class
**C** rows below, since the *value* of a rung is not a constant.
## (c) Class-**C**: hypotheses of stated theorems

Each is a hypothesis of a theorem a reader checks by reading its statement. A rung is
expected to inhabit each by a checked term; where one is still a binder the row says so, and
that is the only place in this repository where that is recorded.

| Binder | What it assumes | Where a rung discharges it |
|---|---|---|
| `hcfg` | the erasure configuration is the fragment's | `Green.spike_configPinned`, at G1-G6 |
| `hsup` | `Supported`, the fragment predicate | `supportedB_sound` on `supportedB`'s computed verdict, at G1-G6 |
| `hnb` | `NoBodylessRefs`, `erase_correct_firstorder`'s `axiom_free` at the emitted environment; decidable, and false on Fannkuch | `by decide +kernel`, at G1-G6 |
| `hcb` | `CompilerBodies`: every tabled compiler body is kernel-typeable at its declared type | `Green.g1_compilerBodies` from `P`, `htbl` and `hsafe`, at **G1 only**. It stays a binder at G2-G6: G2-G4's tables carry the class projection `OfNat.ofNat`, whose typing needs a `TrExprS` derivation through the `TrProj` layer, unproven at the pin (a2), and G5-G6's carry an eliminator spine and a recursive body |
| `hvwt`, `hty` | the *value*'s `TrExprS` witness and its typing at the first-order inductive's spine | nowhere: a rung's value is a constructor spine, not a constant, so `Witness.trExprS_const_of_table` does not reach it. `Witness.sevalValue_of_table`'s route through `SEval.defeq` would discharge both and move the rung from class **A** to class **B**; no rung takes it |
| `UpstreamAsks env` | the two load-bearing upstream asks (`doc/upstream-asks.md` items 2 and 6), as the two fields `constsOrigin` — a plain constant is neither a constructor nor an inductive type name, the block declaring a type former is unique, and every declared constant is one of the three — and `constArityInv` — an application headed by an inductive type former is defeq to neither a sort nor a Π. Taken by `erases_correct` (hence T5 and everything closed on it), `not_erasable_of_informative`, `firstorder_erases_deterministic` and `firstorder_no_box`, and unpacked by `LeanToLambdaBox/Origin.lean`'s six corollaries | the pin bump: the fork's `VEnv.WF'.consts_origin` and `VEnv.IsDefEqU.const_arity_inv` build the structure, and `Origin.lean`'s theorems drop the `A` binder with no change of statement shape. Not measurable in the ledger — `#print axioms` reports a proved theorem's footprint, never a hypothesis — so this row is where it lives |
| `hev` | the source evaluation `SEval env bo [] fullFlags [] e v` the capstone observes | `Green.g5_seval`, at **G5 only** — the one rung whose answer is computed by the source semantics rather than assumed of it. It is a binder at G1-G4 and at G6, where a rung says that its conditions are consistent with a literal answer and not that they hold. The derivation is δ at the subject, then ι at `Nat.casesOn`, and it pays N20's per-branch obligation in full: the *unselected* nullary branch is evaluated too, through its thunk and the δ step at `Unit.unit` that thunk's argument needs |
| `SpikeNatFacts env ni`, `SpikeUnitFacts env pi` | how `env` declares `Nat`, `PUnit`, their constructors and `Nat.casesOn` — the seven facts `Green.g5_seval` reads off the model. Each is a column the reified table records for `lenv`; nothing at the pin transports a tabled inductive back to its declaring block | upstream ask 3 (`doc/upstream-asks.md`), or the ask U3.5 filed for a `TrEnv'` inversion at an inductive name. Until one lands, `green_G5` carries both. The `Nat` half is **satisfiable**, not merely assumed: `Green.spikeNatFacts_natEnv` inhabits it at `SourceEval.lean`'s `NatWitness` fixture, a pats-carrying `VEnv.WF'` declaring `Nat`, its constructors, its recursor and `Nat.casesOn`. The `PUnit` half needs a second block in that fixture |
| `hd`, `hdu`, `hio` at G5 | the three `StepDefeq`s `Green.g5_seval`'s δ, δ and ι steps owe: the constant is definitionally its compiler body, twice, and the eliminator spine is definitionally the selected branch applied to the constructor's field | the kernel's own reductions; a `TrExprS`-level discharge needs the same block inversion `SpikeNatFacts` does |
| `StepPremises env bo Us fl Γspec` | the six facts the three simulation arms need beyond `erases_correct`'s own binders: `fwd` and `elims` (`ErasesEnv.decls` runs entry ⇒ justified, and the `ctorVal`, `beta` and ι arms need the converse at a block and at an eliminator key), `indSpine` (upstream ask 6 refutes only `Erasable`'s type-former disjunct), `elimTyping` (`CasesOnShape` says nothing about the eliminator's *type*), `proj` (`Erases.proj` carries no relevance side condition; `SEval.proj` classifies neither the value's head nor its parameter count), `tabled` (nothing in `SEval.deltaC` excludes a tabled constructor) | each by a repair in the file owning the relation, named in `LeanToLambdaBox/ErasesCorrect/Close.lean`'s header — a forward clause on `ErasesEnv`, a fourth conjunct on `CasesOnShape`, a relevance premise on `Erases.proj`, an `IndInfo`/`CtorOf` premise on `SEval.iota` and `SEval.proj`. None is a pin bump |
| `IndSpineNotProp env` | a spine headed by an informative inductive type former is not a proposition — the half of `not_erasable_of_informative` upstream ask 6 does not cover | the new ask U3.2 filed, `HasType.mkApps_inv`, plus `IsDefEqU.sort_inv`. Taken by the ι arm, the projection arm and T7 |
| `FOFields env Us` | a field of a first-order constructor value is itself typed at a first-order inductive — what T7's ctor case takes its induction hypothesis under | the same `HasType.mkApps_inv` ask, plus the identification of the value's declared inductive with the typing's |
| `LowerEnv.specBlocks` | `BlockBodiesLambda Γspec`, spent by the `Lower` inversion kit in five of the eight structural arms and in all three step arms | **nowhere**: machine-refuted on any specification environment holding one non-λ body (`ctorBodyEnv_block`, `not_blockBodiesLambda_ctorBodyEnv`, `LeanToLambdaBox/ErasesEnv.lean`), which is every realistic one. `erases_correct` is therefore a true theorem with an uninhabited premise until the clause is keyed on the pass's own emitted blocks |

## (c1) One deferral, recorded as a deferral

Criterion 21 asks that no declaration of this repository sit in the `Lean4Lean` namespace.
`grep -rn "^namespace Lean4Lean" LeanToLambdaBox/` returns one line,
`LeanToLambdaBox/CheckerAdequacy.lean:41`, and that is the expected state: the seven
kernel-generic declarations in that block move to the fork only when the pin bump lands
(`doc/upstream-asks.md` item 3, `doc/rework/01-DESIGN.md` §8.3 item 3). This repository does
not edit the fork and does not move the pin, so the grep is **not** run as a gate check while
that ask is open. The row exists so that the criterion is not reported as passing when it is
deferred.

## (d) Class-**E**: scope restrictions and consumer facts

| Row | Content |
|---|---|
| N1 `csimp` | `csimp := false` is required by every correctness statement; the shipping default is `true` |
| N2 `@[extern]` | an `@[extern]` constant is emitted body-less and its realizer is the consumer's; a program reaching one fails `NoBodylessRefs` and is outside the capstone's domain |
| N3 machine `Nat` | `nat := .peano` only |
| N4 argmask | `remove_irrel_constr_args := false` |
| N5 auto-inline | the `.ast.inlinings` channel, including `F-PRODUCT`'s feature |
| N7 termination | no source strong normalization: the capstone keeps `[S]`'s conditional form |
| N10 serialisation | the printer and the `.ast` grammar are outside the theorem |
| N11 sidecars | `.ast.inlinings` and the `.mli` sidecar are unverified output |
| N14 size | no claim about output size |
| N16 `Quot` | no `Quot` primitive in a computationally relevant position |
| N18 prop-elimination | no elimination of a `Prop`-valued inductive into data — the fragment boundary `F-PROP` forces |
| compiler-vs-kernel bodies | the well-founded definitions' compiler bodies differ from their kernel bodies; only propositional instances are covered |
| peregrine | its `run_untyped_transforms` precondition obligation is `Admitted`, and `validate` checks no expandedness (`doc/upstream-asks.md`) |
| MetaRocq | the shipped `firstorder_ind` is `false` on `nat`, so this development cites and does not transcribe it |
| Rocq transport | no Rocq-side copy of `Erases`/`Lower` exists; `doc/rules-Erases.md` and `doc/rules-Lower.md` are the anchor instead |

`doc/coverage.md` carries the `hrun`, `htbl` and `hsafe` rows verbatim from this file; every
other fact above lives here and only here.
