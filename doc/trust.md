# Trust — provenance for the measured ledger

`test/ledger.expected` holds exactly the `#print axioms` output of `test/Ledger.lean` and
nothing else; `scripts/ledger.sh` re-measures it and the wave gate diffs it. That is what a
diff can check. `#print axioms` reports `sorryAx` as one flat name with **no provenance**, so
provenance lives here, and no acceptance test claims to have measured it. This file is the
only prose ledger in the repository.

Its live rows are the results of `doc/rework/01-DESIGN.md` §4.14 that exist: `erases_correct`
with its folded form, its three step arms and the aggregator they feed, the corollaries of
`ErasesEnv` and of `UpstreamAsks` the arms spend — `ErasesEnv.runtimeKey_isCasesOn`,
`erases_elimSpine_no_value`, `ErasesEnv.ctorArity`, `not_erasable_of_informative`,
`CasesOnShape.agree`, `ElimDecl.uniq`, `neverZeroB_sound`, `Lower.appReady` — the two
first-order results with `fOFields_of_asks`,
`LowerBlock.lambda_of_fixLambda`, `Lower.constToFix`, the two halves of `ErasesEnv.tabled`'s
discharge (`constants_of_tabled`, `constOrigin_of_constants`),
`shipping_erase_correct_firstorder`, `bridgeEnv_of_regInv`, `green_G1`-`green_G8` with
`green_G5`'s source evaluation, and the three §5 results already standing — `SEval.defeq`,
`LBOptimize_correct`,
`lbEval_sound`. The two `visitExpr_refines_*` bridges are live rows, measured as they stand: an
implication whose eighteen member steps are hypotheses. `ErasureSpec.oracle_sound_of_run` is a
live row too, and it is the row that measures the executable-checker cluster of §(a3) at its
entry point. Every rung of the ladder has a row, and none is commented out. A second fixture,
`test/erasesLB.expected` (`scripts/erasesLB.sh`), measures the composite's introduction
lemmas — statement and footprint — so a premise silently added to or dropped from `ErasesLB`
shows as a diff. `lbWfPeregrine_of_check` is a live row too, beside `neverZeroB_sound`: the
checker-to-structure transport `hwf` reads at every rung, footprint `[propext, Classical.choice,
Quot.sound]`.

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
class-**D** binder instead.

The cluster's entry point is `Oracle.kernel_isErasable_sound`, reached through
`ErasureSpec.oracle_sound_of_run`, and the row that measures it is that theorem's own line in
`test/Ledger.lean`. What the row measures is the **set of axiom names**: `#print axioms` prints
the two `_native.bv_decide` certificates' names and never their LRAT contents, so a swapped
certificate is invisible to it, and `scripts/ledger.sh` normalises nothing. The same 33 names
stand on `shipping_erase_correct_firstorder` and on all eight rungs, because
`erasure_bridge_of_run` supplies the bridge's step 1 and step 1 *is* the oracle. Sites of the
twenty-nine non-standard names, relative to `.lake/packages/lean4lean/Lean4Lean/`:

| Names | Site |
|---|---|
| `ptrEqExpr_eq`, `ptrEqConstantInfo_eq` | `PtrEq.lean:17,22` |
| `Std.TreeMap.all_eq_all_toList` | `Verify/Axioms.lean:10` |
| `PersistentArray.toList'_push` | `Verify/Axioms.lean:39` |
| `PersistentHashMap.WF.toList'_insert`, `WF.find?_eq`, `findAux_isSome` | `Verify/Axioms.lean:72,78,83` |
| `Syntax.structEq_eq` | `Verify/Axioms.lean:115` |
| `Level.isExplicitSubsumedAux_eq`, `normalize_eq`, `hasParam_eq`, `hasMVar_eq`, `instLawfulBEqLevel` | `Verify/Axioms.lean:194,257,279,289,292` |
| `Expr.mkData_eq`, `mkAppData_eq`, `looseBVarRange_eq`, `replace_eq`, `lowerLooseBVars_eq` | `Verify/Axioms.lean:325,342,360,363,402` |
| `Expr.instantiate1_eq`, `instantiate_eq`, `instantiateRev_eq`, `instantiateRange_eq`, `instantiateRevRange_eq` | `Verify/Axioms.lean:421,428,432,436,440` |
| `Expr.abstract_eq`, `abstractRange_eq`, `hasLooseBVar_eq`, `eqv_eq` | `Verify/Axioms.lean:463,467,485,505` |
| `Expr.Data.looseBVarRange_le._native.bv_decide.ax_1_7`, `Expr.mkData_flags._native.bv_decide.ax_1_12` | `Verify/Expr.lean:203,256` — the LRAT certificates of two `bv_decide` proofs |

`Expr.instantiate1_eq` and the three persistent-structure names also reach the bridge
outside the oracle, through the binder transports `BridgeInv.mkLocalDecl`/`.mkLetDecl`
that the `visitLambda`, `visitLet` and `visitAlt` steps consume.

### (a4) What the projection arm does **not** add, and what the δ arm does

Measured, not assumed, by walking the constant graph of each arm rather than by comparing
`#print axioms` lines. `step_proj`'s `sorryAx` roots are `step_iota`'s, name for name and set
for set: `Lean4Lean.TrProj.uniq`, `VEnv.IsDefEqU.forallE_inv_stratified`,
`VEnv.IsDefEqU.sort_forallE_inv`, `VEnv.IsDefEqU.sort_inv`, `VEnv.WF.patsStrong`. `TrProj.uniq`
is already inside `SEval.defeq`'s footprint, reaching it through `TrExprS.uniq`, and the two
entirely open projection lemmas of the executable checker — `inferProj.WF` and
`inferProj.WF_struct` (`Verify/TypeChecker/InferType.lean:392,407`) — do not appear at all,
because `step_proj` *consumes* a `TrProj` from `TrExprS.proj`'s own premise and never builds
one. So the `TrProj` exposure at a projection is **inhabitation**, not axioms: a
projection in a real program has a `TrExprS` derivation only through `inferProj.WF`, which is
`sorry` at the pin, so the proj arm is non-vacuous only on hand-built witnesses.

The δ arm brings in the `instantiateLevelParams` axiom cluster, and it has ledger subjects.
`ErasesEnv.defns` records the erasure of a tabled body at the declaration's own level scope,
which is where `erases_constant_body` records it (`../metarocq/erasure/theories/Extract.v:264`),
so `step_delta` derives the instantiated reading itself, by
`Erases.instantiateLevelParams_of_stepDefeq` on `Erases.instL`. `step_delta`, `erases_correct`
and `erases_correct_lb` therefore inherit lean4lean's `Erases.instL` footprint verbatim:
`Expr.mkAppData_eq`, `Expr.mkData_eq`, `Expr.replace_eq`, `Level.hasParam_eq` and two
`_native.bv_decide` axioms. Every one of the six is already in the capstone's cluster, so
neither the capstone's footprint nor any rung's grows; `bridgeEnv_of_regInv` sheds the cluster
with the level-parameter-freedom premise that used to carry it.

## (b) Class-**D**: permanent named binders

Each is a hypothesis no Lean term can discharge, mechanised outside the kernel instead. They
appear by name in the statements that take them, and `lake exe green-check` is the mechanism.

| Binder | What it assumes | External mechanism |
|---|---|---|
| `hrun` | the `#erase` run produced the committed `.ast` | `green-check` re-runs `#erase` and byte-diffs the file; `IO.RealWorld` is opaque, so no Lean proof of this can exist |
| `htbl` | the reified `SourceTable` is the live environment's slice, including the `prepare_erasure` run clause, which pins the compiler body up to α (`Witness.Expr.AlphaEq`: binder names and binder info ignored, nothing else), and `compilerLevels`, that the **compiler** declaration `Lean.Compiler.LCNF.getDeclInfo?` answers with — the `_unsafe_rec` companion where the elaborator emitted one — carries the table's level column, which is the identification the run relies on when `Erasure.visitMutual` installs `lparams := ci.levelParams` from that constant while the table's column and `CompilerBodies` read `lenv.find?` | `lake exe reify --check` compares field by field against the live environment, `compilerLevels` included, and cross-checks `Expr.eqv` against a Boolean written arm-for-arm against the relation |
| `hsafe` | `TableSafe`: every declaration the reified table pins — constants, inductive types and their constructors — is safe in the ambient environment, the one column `SourceTableAdequate` does not record, plus two clauses about the table's own constant column: `notUnsafeRec`, no tabled constant is an `_unsafe_rec` companion, which is the guard `lookup_adequate.declInfo`'s membership arm takes, and `declCtor`, a tabled constant that `lenv` declares a constructor is in the table's constructor column too, which is what `Erasure.visitConstApp` needs to read the fragment's saturation condition at a `getCtorArity?` hit, and `noMaxLevels`, every tabled body is in the `max`-free level fragment, which is the fragment `Erases.instL` transports a body's erasure along and so what `TabledLevels` — `bridgeEnv_of_regInv`'s level-scope premise, which the reachability gate of `ErasesEnv.defns` then hands the δ arm one constant at a time — spends. Load-bearing five times: `Green.g1_compilerBodies`, `supportedB_sound`, `step6`, `step_visitConstApp` and `tabledLevels_of_table` | `lake exe reify --check` reads the live declarations for the three safety clauses; the column is an upstream ask. `notUnsafeRec`, `declCtor` and `noMaxLevels` are decidable on a concrete table, and the first two hold by construction of `Witness.reify%`, whose `.ctorInfo` arm reifies the constructor's own inductive block; no `reify` verb reads any of the three |
| `env_connect` | the ambient `Lean.Environment` is `TrEnv`-related to the `VEnv` the specification quantifies over | upstream ask 4 would derive it |
| `lookup_adequate` | a run's constant and inductive lookups agree with the specification environment. Three clauses are guarded or two-sided: `declInfo` puts the visited name in the block `Lean.Compiler.LCNF.getDeclInfo?` answers with, under the guard `Lean.Compiler.isUnsafeRecName? n = none` — the primitive prefers the `_unsafe_rec` twin, so the membership is false at such a name — and answers `none` only for a name `lenv` does not know, which is what makes the query total at a tabled head; `ctorArity` answers exactly for the constructors `lenv` declares and for no other name, whose negative direction is `Motive4`'s constructor exclusion; `casesInfo` answers exactly for the `casesOn` constants, at metadata agreeing with the declared block through `CasesInfoAgreesK`, whose `numAlts`, `discrPos`, `indName` (the eliminated inductive is the one at the head's name prefix) and `altCtor` (slot `j` is constructor `j`'s, never a catch-all) `CasesInfoAgrees.of_pinned` carries to the reified block; measured at 3,161 of 3,161 `casesOn` constants whose prefix is an inductive type, 0 failures | — |
| `prim_monotone` | the calls the erasure makes for their effect alone only advance the name generator, one clause per named primitive: `Lean.getEnv`, `Lean.logInfo`, `Lean.Meta.isInstance` and `Lean.Meta.inferType`, which additionally reports a Π-telescope matching the subject's λ-telescope (`ForallMatchesLam`); `Lean.Meta.isProof`, the proof test run under a telescope; the two bounded telescopes `Lean.Meta.forallBoundedTelescope` and `Lean.Meta.lambdaBoundedTelescope`, each **compositionally** — the telescope opens binders of its own, so it advances the generator, and no further than its continuation does; and `Erasure.liftMetaM`, which carries the bound from the shape a `MetaM` computation is applied in (where `>>=` is the underlying `EST.bind`, so the bound composes — `MetaGenMono`) to the shape the run lemmas read. Nothing here quantifies over an arbitrary `Lean.MetaM` computation: the two anonymous continuations the erasure passes to the telescopes are covered by `PrimGenMono`, a *derived* predicate discharged at each call site by the `pure`/`>>=`/`forIn` combinators | — |
| `block_adequate` | the kernel's inductive blocks, constructors and eliminators are the model's, at the identifier `Erasure.register_inductive` mints: `fwd` and `bwd` between `IndInfo` and a declared block with its `KernelFields`, `ctor` and `ctorBwd` between `CtorOf` and a declared `ConstructorVal`, `casesOnDecl` for the eliminator's `CasesOnShape` **at the block's own segmentation** `iv.numParams + 1 + iv.numIndices`, which is what pins the model's discriminant position to the elaborator's, and `selfMem`, a declared inductive is a member of its own block (`iv.name ∈ iv.all`), which is what the registration loop of `Erasure.register_inductive` is indexed by. The emitted propositional flag is **not** a sixth clause: `ErasureSpec.propositionalInd_of_arity` *derives* the half the consumers spend — a `true` `Erasure.isPropositionalArity` verdict gives `PropositionalInd env I` — from `decl_adequate` and the arity walk's commutation with translation, and the converse is false at an arity whose final sort sits under a `let` (`doc/rework/03-DEV-FIX.md`, F-ARITYLET), so assuming the equation here would assume something refuted | — |
| `hblk` | `TableBlocks`: every member of a block the run installs a fixvar map for is tabled (`members`), its tabled body is λ-headed (`lamHeaded`, N22's first half) and no member is erasable (`informative`, N22's second half) | `lake exe reify --blocks` reads `Witness.fixBlock?` off the live environment and checks `members` and `lamHeaded`; `informative` is model-side and no computation reaches it |
| `hprep` | the prepared term is the rung's own subject — `Erasure.prepare_erasure` is the identity at it. Load-bearing because the capstone's syntactic conjuncts read the prepared term while `Supported` and `TrExprS` are checked at the subject, and transporting those two across the passes is a stronger statement about `Lean.Compiler.LCNF.macroInline`, false in general | `lake exe reify --prepared` runs `Erasure.prepare_erasure` against the live environment and reports identity; green at all eight rung subjects — the six spike constants and Arith's `arithClosed` and `benchArith` |
| `fresh_names` | the run's fresh `FVarId`s are fresh | — |
| `oracle_refl` (reflection clause) | the monadic oracle run reflects the kernel predicate | near-definitional; the discharge's price is (a3) |
| `oracle_meta` | the `isErasableMeta` fallback and the polymorphic-scope arm are sound **at the scope the verdict was taken under**, `ctx.lparams`, which is the only scope `Erasure.isErasable ctx.lparams` speaks of. Read at the reader's `Us` the payload holds outright below a polymorphic declaration, since no subject mentioning a level parameter translates at the capstone's `[]`; there is no transport between the two scopes and none is assumed, so a consumer with its witness at `Us` spends `oracle_refl` at `ctx.lparams = Us` and the clause is unreachable while `BridgeInv.lparams` pins the two together | empirically dead on the error route: 0 fallback hits in 139,196 constants |
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
| `hbridge` | the two environment results the run's final state carries beyond the erasure itself, together with the existence of the specification environment they are read at: `erasesEnv : ErasesEnv env bo Γspec t₀` and `lowerEnv : LowerEnv Γspec Γ`, both composed by `bridgeEnv_of_regInv` out of `RegInvShape'` and `RegSaturated` at that state, which no theorem produces for a run of the shipping eraser. `doc/rework/08-REPAIRS-W5.md` §2 is the statement that would produce it — the content clause with the erasure witness shared, read at a specification environment grown from the run's output — and its §2.3 names the three measured obstructions in the way. **The level scope**: the eighteen motives are stated at a fixed `Us` through `BridgeInv.lparams`, which `Erasure.visitMutual` re-enters under the member's own `levelParams`, and 16 of G7's 30 tabled bodies belong to a polymorphic constant. **α**: `ReifiedDecl.Prepared` pins a tabled body only up to `Expr.AlphaEq` — deliberately, since on equality the clause is uninhabited wherever `inlineMatchers` fires, and `lake exe reify --check` reports five of G7/G8's bodies matching only up to binder names — while `Lower` is not α-closed on its source, its two `fix` arms reading a declared body out of `Γ` by equality. **The ∀-`Γspec` shape**: `RunRefines` reads content at *every* `SpecEnv` of the final state, where the repair produces one, and the two cannot be proved in one induction without restating all eighteen motives | nowhere, at any rung. These two fields are all the bundle carries. the well-formedness field left it and is the capstone's own binder `hwf`, a checked term at every rung; the simulation field is retired, the capstone applying `erases_correct` once at the spine with `ErasesEnv.mkApps` and a per-argument premise; the box-freedom field is retired, box-freedom of the lowered value coming from `noBox_lower_of_foSpine` on the constructor-tree shape `firstorder_erases_core` now exports; and the answer's uniqueness is the capstone's own `firstorder_erases_core` call. The erasure half is `erasure_bridge_of_run`, which proves `Erases env [] [] pe t₀ ∧ Lower Γspec t₀ t` from the run and supplies all eighteen member steps |
| `E.passes_monotone` | the four `Erasure.prepare_erasure` calls only advance the name generator. Owner: this repository, wave W5 | unfolding `Lean.Core.transform`'s generator discipline at `Erasure.replaceUnsafeRecNames`, `Lean.Compiler.LCNF.macroInline` and `Lean.Compiler.LCNF.inlineMatchers` |
| `E.passes_sound` | each of those passes preserves the source evaluation of the subject **under an arbitrary application spine**; the spine is quantified because the capstone reads its observable at `mkApps e args` while the pass is a whole-tree `Lean.Core.transform` walk, and `f (mkApps e args)` is not `mkApps (f e) args`. Owner: this repository, wave W5 | a δ-expansion argument for `Lean.Compiler.LCNF.macroInline` and a renaming argument for `Erasure.replaceUnsafeRecNames`; `prepare_sound`, the composition over the four calls, is proved |
| `E.oracle_false_refl` | a `false` verdict of `Erasure.isErasable` means the pure kernel run did not answer `true`. Near-definitional — the `| .ok b => return b` arm, modulo the `getEnv`/`getLCtx` reads — and stated at the one scope both runs are made at, `ctx.lparams`, with no reader's scope in it. Owner: this repository, wave W5 | a `MetaM` reflection lemma for that arm |
| `E.kernel_ind_head_true` | at an inductive-type head the pure kernel run answers `true`. **Not a theorem**: `Erasure.isArityCheck` walks the head's type under a fixed budget (`Relevance.lean:49-50`), so a *reduced* telescope longer than that budget — and any other kernel error raised inside `isArityCheck` — leaves the walk short of the closing sort and routes the verdict to `Erasure.isErasableMeta`, of which only soundness is assumed (`ErasureSpec.oracle_meta`); measured `.ok true` at 2,940 of 2,940 inductive type formers. The scope is the run's own, universally quantified, not a reader's: fixed at `[]` the clause's premises are uninhabited below a universe-polymorphic declaration, which is where the `casesOn` verdicts of the fragment are taken, and the field would say nothing there. Owner: this repository, wave W5 | three executable-shape lemmas lean4lean does not have — `inferType` on a `.const`-headed spine returns the instantiated declared telescope, `whnf` is the identity on a syntactic `.forallE`, the budget covers the telescope — together with a bound on the *reduced* telescope, which a constant budget does not supply |
| `hcfg` | the erasure configuration is the fragment's | `Green.spike_configPinned`, at G1-G8 |
| `hsup` | `Supported`, the fragment predicate | `supportedB_sound` on `supportedB`'s computed verdict, at G1-G8 |
| `hnb` | `NoBodylessRefs`, `erase_correct_firstorder`'s `axiom_free` at the emitted environment; decidable. Measured **0 failures** across the five corpus programs and the eight rungs — Fannkuch's one body-less `Eq.rec` (the pre-fix counterexample this row used to cite) is now a `.case` body of `recursorRealizer`'s registering, F-QUOT's and F-EQREC's exit (§2.8 of `doc/rework/10-MERGE-FIXES.md`), a strict gain `doc/coverage.md` records | `by decide +kernel`, at G1-G8 |
| `hwf` | `LBWfPeregrine Γ t`, what peregrine's first pass reads of the emitted program. Twelve clauses, every one of them a bounded quantifier once `OnProgram`'s `∀ kn` is a fold over `Γ` and `SubTerm` a structural walk, so `lbWfPeregrineB` decides it and `lbWfPeregrine_of_check` transports the verdict; its footprint carries no `sorryAx`. `expandedFix` is one of the twelve (replacing the weaker `fixLambda`, which survives as a theorem projecting it): the three term-level conjuncts of MetaRocq's `expanded_tFix` (`EEtaExpandedFix.v:46-54`), F-ETA's registered-fixpoint η-expansion (`LBTerm.etaFix`) makes true on all eight rungs — `PeregrinePre`, the earlier separate conjunction, is deleted, since `LBWfPeregrine` alone is now that strong. The binder-name clause it reads is `PrintableBinders` — a name closes or escapes no atom — because the class it replaced, `Basic.cleanIdent`'s alphanumeric one, is a condition on kername identifiers and is **false** on the emitted output at five of the eight rungs: one offending binder name at G2-G4 and thirty-four at G7/G8, which `doc/coverage.md` measures per rung | `lbWfPeregrine_of_check (by decide +kernel)`, at G1-G8 |
| `hargReach` | at **G8 only**: that the erasure of the subject reaches `Nat`'s block in the specification environment the capstone produces. It is what remains of the observable clause's per-argument `ErasesEnv` conjunct after `Green.g8_argErasesEnv`, which reduces that conjunct at the argument's image `peanoLB 0` to this one reachability. It is not slack: at `Γspec = []` the conjunct is false — `peanoLB 0` reaches the block key and the lookup answers `none` — while `Lower [] (.const kn) (.const kn)` still holds, which is why the binder carries `ErasesEnv env g8Table.body? Γspec t₀` and `LowerEnv Γspec g8Env` as antecedents rather than being stated at every `Γspec` | nowhere. It is true of any real run — `ErasesEnv.defns` at the tabled body of `benchArith` forces `Γspec` to declare an erasure of it whose closure runs to `Nat.succ` and `Nat.zero` — and proving it needs the same content clause `hbridge`'s two fields wait on (`doc/rework/08-REPAIRS-W5.md` §2.1, deferred by §2.3). G1-G7 apply the observable clause at the empty spine, where the premise is vacuous |
| `hcb` | `CompilerBodies`: every tabled compiler body is kernel-typeable at its declared type | `Green.g1_compilerBodies` from `P`, `htbl` and `hsafe`, at **G1 only**. It stays a binder at G2-G8: G2-G4's tables carry the class projection `OfNat.ofNat`, whose typing needs a `TrExprS` derivation through the `TrProj` layer, unproven at the pin (a2); G5-G6's carry an eliminator spine and a recursive body; and G7-G8's Arith table carries ten `Expr.proj`-bearing bodies among its thirty, with twenty-eight of its forty-four declarations polymorphic, which the monomorphic G1 route does not reach either |
| `hvwt`, `hty` | the *value*'s `TrExprS` witness and its typing at the first-order inductive's spine | nowhere: a rung's value is a constructor spine, not a constant, so `Witness.trExprS_const_of_table` does not reach it. `Witness.sevalValue_of_table`'s route through `SEval.defeq` would discharge both and move the rung from class **A** to class **B**; no rung takes it |
| `UpstreamAsks env` | the four load-bearing upstream asks (`doc/upstream-asks.md` items 2, 6, 9 and 10), as the four fields `constsOrigin` — a plain constant is neither a constructor nor an inductive type name, every declared constant is one of the three, and the block declaring a type former is unique both in its λ□ coordinates and as a declaration — `constArityInv` — an application headed by an inductive type former is defeq to neither a sort nor a Π — `mkAppsInv` — spine typing inversion, stated with `OrderedStrong` explicit — and `indSpineInj` — two defeq spines headed by inductively declared formers have the same head. Taken by `erases_correct` (hence T5 and everything closed on it), `not_erasable_of_informative`, `indSpine_not_prop`, `elim_major`, `ctor_saturated`, `CasesOnShape.agree`, `fOFields_of_asks`, `firstorder_erases_deterministic` and `firstorder_no_box`, and unpacked by `LeanToLambdaBox/Origin.lean`'s corollaries. `erasure_bridge_of_run` takes it too, for the bridge's steps 3, 4 and 17, so every rung now carries it | the pin bump: the fork's `VEnv.WF'.consts_origin`, `VEnv.IsDefEqU.const_arity_inv`, `HasType.mkApps_inv` and `IsDefEqU.indSpine_inj` build the structure, and `Origin.lean`'s theorems drop the `A` binder with no change of statement shape. Not measurable in the ledger — `#print axioms` reports a proved theorem's footprint, never a hypothesis — so this row is where it lives |
| `ErasesEnv.tabled`'s exclusion at a tabled constant | that a constant the compiler table gives a body for is neither a constructor nor an inductive type name **in the model**. `Origin.lean` proves the two halves that surround it — `constants_of_tabled` (the tabled constant is a constant of `env`, class **D** through `ErasureSpec.decl_adequate`) and `constOrigin_of_constants` (ask 2's classification, given the exclusion) — and nothing at the pin joins them | class **D**, and blocked: the join is a kind transfer from `lenv`'s `ConstantInfo` to the model's classification of `env.constants`, whose only witness would be a `TrEnv'` inversion — `doc/upstream-asks.md` item 4, the same ask `firstOrderIndB_sound` waits on. Until it lands the exclusion is a premise of `SpecEnv.erasesEnv` beside `hdefns` |
| `hfo` | `FirstOrderInd env I`: the answer's inductive is first order in the model — every constructor field of every member of its block is itself a first-order inductive, and the block has no parameter, index or `Prop` member. Read at `` `Nat`` by all eight rungs | nowhere. `firstOrderIndB` decides the same property on a reified `SourceTable` and `firstOrderIndB_step` is its table-side half, but the model-side half is the kind transfer from `lenv` to `env.constants` — `doc/upstream-asks.md` item 4, the same ask `ErasesEnv.tabled`'s exclusion waits on — so no rung discharges it by computation |
| `hev` | the source evaluation `SEval env bo [] fullFlags [] e v` the capstone observes | `Green.g5_seval`, at **G5 only** — the one rung whose answer is computed by the source semantics rather than assumed of it. It is a binder at G1-G4 and at G6-G8, where a rung says that its conditions are consistent with a literal answer and not that they hold. At G7-G8 no witness was attempted: Arith's evaluation is 45 recursive calls, each owing N20's derivation for the unselected minor as well, against the 45 lines and three `StepDefeq` binders one δ and one ι cost at G5. The derivation is δ at the subject, then ι at `Nat.casesOn`, and it pays N20's per-branch obligation in full: the *unselected* nullary branch is evaluated too, through its thunk and the δ step at `Unit.unit` that thunk's argument needs |
| `SpikeNatFacts env ni`, `SpikeUnitFacts env pi` | how `env` declares `Nat`, `PUnit`, their constructors and `Nat.casesOn`, and that `Nat` eliminates into data — the eight facts `Green.g5_seval` reads off the model, the last of them `natInf : InformativeInd env ``Nat`, which is `SEval.iota`'s relevance premise. Each is a column the reified table records for `lenv`; nothing at the pin transports a tabled inductive back to its declaring block | upstream ask 3 (`doc/upstream-asks.md`), or the ask U3.5 filed for a `TrEnv'` inversion at an inductive name. Until one lands, `green_G5` carries both. The `Nat` half is **satisfiable**, not merely assumed: `Green.spikeNatFacts_natEnv` inhabits it at `SourceEval.lean`'s `NatWitness` fixture, a pats-carrying `VEnv.WF'` declaring `Nat`, its constructors, its recursor and `Nat.casesOn`. The `PUnit` half needs a second block in that fixture |
| `hd`, `hdu`, `hio` at G5 | the three `StepDefeq`s `Green.g5_seval`'s δ, δ and ι steps owe: the constant is definitionally its compiler body, twice, and the eliminator spine is definitionally the selected branch applied to the constructor's field | the kernel's own reductions; a `TrExprS`-level discharge needs the same block inversion `SpikeNatFacts` does |

Four premises a reader may look for have **no row**, because none of them exists any longer. `StepPremises env bo Us fl Γspec` (with its `indSpine`, `elimTyping`, `proj` and `tabled` fields): four of its six fields became clauses of the restated `ErasesEnv` and of `SEval.iota`/`SEval.proj`, and the other two became `UpstreamAsks` fields, so the bundle is deleted. `IndSpineNotProp env`: a theorem, `Origin.lean`'s `indSpine_not_prop`, off asks 9 and 2. `FOFields env Us`: a theorem, `fOFields_of_asks`, off asks 9, 10 and ask 2's block uniqueness. `LowerEnv.specBlocks`: refuted, and deleted with `BlockBodiesLambda`; `LowerBlock.hfl` asserts the λ-headedness of the **emitted** definitions, and the condition that supplies it is read on the **input** side, as `TableBlocks.lamHeaded` together with `TableBlocks.informative` — the second a conjunct and not a formality, because `run_mkDef_box_not_lambda` shows that an erasable member is registered with a non-λ body.

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
