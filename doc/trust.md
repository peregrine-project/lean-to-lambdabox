# Trust — provenance for the measured ledger

`test/ledger.expected` holds exactly the `#print axioms` output of `test/Ledger.lean` and
nothing else; `scripts/ledger.sh` re-measures it and the wave gate diffs it. That is what a
diff can check. `#print axioms` reports `sorryAx` as one flat name with **no provenance**, so
provenance lives here, and no acceptance test claims to have measured it. This file is the
only prose ledger in the repository.

Its live rows are the results of `doc/rework/01-DESIGN.md` §4.14 that exist:
`LowerBlock.lambda_of_fixLambda`, `Lower.constToFix`,
`shipping_erase_correct_firstorder`, `green_G1`-`green_G4`, and the three §5 results already
standing — `SEval.defeq`, `LBOptimize_correct`, `lbEval_sound`. `erases_correct` (W3), the two
`visitExpr_refines_*` bridges (W4) and `green_G8` (W5) are commented out in `test/Ledger.lean`
and are uncommented by the wave that proves them. A second fixture,
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

## (b) Class-**D**: permanent named binders

Each is a hypothesis no Lean term can discharge, mechanised outside the kernel instead. They
appear by name in the statements that take them, and `lake exe green-check` is the mechanism.

| Binder | What it assumes | External mechanism |
|---|---|---|
| `hrun` | the `#erase` run produced the committed `.ast` | `green-check` re-runs `#erase` and byte-diffs the file; `IO.RealWorld` is opaque, so no Lean proof of this can exist |
| `htbl` | the reified `SourceTable` is the live environment's slice, including the `prepare_erasure` run clause | `lake exe reify --check` compares field by field against the live environment |
| `hwt` | the subject's `TrExprS` witness, until the checker-routed witness lands (U3.4) | lean4lean's checker, run on the subject |
| `hsafe` | `TableSafe`: every declaration the reified table pins — constants, inductive types and their constructors — is safe in the ambient environment, the one column `SourceTableAdequate` does not record. Load-bearing twice: `Green.g1_compilerBodies` and `supportedB_sound`, which reads it to put a tabled name in the model | `lake exe reify --check` reads the live declarations; the column is an upstream ask |
| `env_connect` | the ambient `Lean.Environment` is `TrEnv`-related to the `VEnv` the specification quantifies over | upstream ask 4 would derive it |
| `lookup_adequate` | a run's constant and inductive lookups agree with the specification environment | — |
| `fresh_names` | the run's fresh `FVarId`s are fresh | — |
| `oracle_refl` (reflection clause) | the monadic oracle run reflects the kernel predicate | near-definitional; the discharge's price is (a3) |
| `oracle_meta` | the `isErasableMeta` fallback and the polymorphic-scope arm are sound | empirically dead on the error route: 0 fallback hits in 139,196 constants |
| `decl_adequate` | inductive metadata of the run matches the specification's | kept only with the obstruction named; upstream ask 4 |

## (c) Class-**C**: hypotheses of stated theorems

Each is a hypothesis of a theorem a reader checks by reading its statement. A rung is
expected to inhabit each by a checked term; where one is still a binder the row says so, and
that is the only place in this repository where that is recorded.

| Binder | What it assumes | Where a rung discharges it |
|---|---|---|
| `hcfg` | the erasure configuration is the fragment's | `Green.spike_configPinned`, at G1-G4 |
| `hsup` | `Supported`, the fragment predicate | `supportedB_sound` on `supportedB`'s computed verdict, at G1-G4 |
| `hnb` | `NoBodylessRefs`, `erase_correct_firstorder`'s `axiom_free` at the emitted environment; decidable, and false on Fannkuch | `by decide +kernel`, at G1-G4 |
| `hcb` | `CompilerBodies`: every tabled compiler body is kernel-typeable at its declared type | `Green.g1_compilerBodies` from `P`, `htbl` and `hsafe`, at **G1 only**. It stays a binder at G2-G4, whose tables carry the class projection `OfNat.ofNat`: typing that body needs a `TrExprS` derivation through the `TrProj` layer, which is unproven at the pin (a2) |
| `hev` | the source evaluation `SEval env bo [] fullFlags [] e v` the capstone observes | **nowhere yet.** No rung below G5 constructs an `SEval` derivation, so `hev` is an **uninhabited** class-**C** binder at G1-G4 (`Green.lean`, one per rung). The first one built is G3's `green_G5`, whose subject is a `match`: it discharges `CasesOnShape`, `ConstOrigin`, `CtorOf` and N20's per-branch obligations. Until then a rung's non-vacuity is conditional on this binder as well as on the class-**D** ones |

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

`doc/coverage.md` carries the `hrun`, `htbl` and `hwt` rows verbatim from this file; every
other fact above lives here and only here.
