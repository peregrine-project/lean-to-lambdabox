# 11 — W8, what closing `hbridge` actually costs

`doc/rework/09-REPAIRS-W7.md` planned nine units, U1–U9, that would end with `hbridge` gone
from `shipping_erase_correct_firstorder` and from the eight rungs. U1–U4 landed in wave 1.
Wave 3 landed U5–U9 **partially** (`8bdffca`…`6439576`), and its audit refuted the headline:
`bridgeEnv_of_regContent`, the theorem that composes the binder's payload, has a premise set
that is jointly unsatisfiable at the rungs (`scratch/round7/W3-refute.md`, R1). §1 records
what the wave established and what it refuted. §2 is the unit specification that repairs it
and discharges the binder — nine units, each with its exact statement. §3 says what still
stands after W8.

Every signature in §2 elaborates at this toolchain against the tree at `15a4af7`; the probe is
`scratch/round7/w8_sigs.lean` (`w8_sigs.out`, exit 0, fourteen `sorry`-stubs and eight proved
statements, all `[propext, Classical.choice, Quot.sound]` or less). Scratch probes are
untracked. Two units wait on a **shipping** merge, F-DEPLCTX and F-ARITYLET, both recorded in
`doc/rework/03-DEV-FIX.md` and both owned by `dev/fix`; the per-unit tables say which.

## 1. What wave 3 established, and what it refuted

### 1.1 U5 — the mechanical half only

`2c2bd06` states the eighteen motives, the eighteen `Stepᵢ` interfaces, `motives_of_steps`,
both T8 theorems, `erasure_bridge_of_run`, the capstone and all eight rungs at **every** level
scope, with `ctx.lparams = Us` supplied by `BridgeInv.lparams` (`Bridge.lean:339`) rather than
by a fresh equation, and the premise bundle following as `P : ∀ Us, ErasureSpec lenv env Us gw`.
That is `abstract_make_wf_env_ext`'s reading at every constant, and it costs one clause:
`erasureSpec_scope_shift` measures that six of the bundle's seven fields do not mention a
scope (`U5-report.md` §1). `ErasureSpec.oracle_meta` is deleted with it.

The unit's second half — `Motive6` reporting the registered block's **content** — did not
land, and the reason is not the level scope. `Erasure.visitMutual` re-enters a dependency
under `withReader (fun e => { e with fixvars := …, lparams := ci.levelParams })`
(`Erasure.lean:889`, `:912`) and leaves `lctx` in place, so `BridgeInv.mlc` asks the
*caller's* local context to be modelled at the member's level column. Mechanised sorry-free:
`U5.mlctx_not_wf_at_empty`, `U5.bridgeInv_nil_lctx`, `U5.bridgeInv_member_nil_lctx`
(`scratch/round7/u5_lctx.lean`). Reading the member's motive at `Δ = []` — the context
`erase_constant_body` erases at (`../metarocq/erasure/theories/Extract.v:264`) — therefore
asks the caller to hold no binder at all, and a term walk reaches a `.const` node under
binders routinely. This is **F-DEPLCTX**, a shipping defect with a one-field fix.

### 1.2 U6 — the definitional half

`7c79e48`/`420c584` land `SpecGrow` (`Lower.lean:2385`), its seven transports,
`ElimBlocksDeclared` and `SpecGrow.of_fresh` (`:2455`, `:2493`), `ConstsDeclared` /
`ConstsDeclaredEnv` with the decidable twin (`:2310`, `:2317`, `:2301`), `Lower.specGrow` and
`LowerAlt.specGrow` (`:2564`), the four composite transports (`ErasesLB.lean:483`–`:515`),
the two mode transports (`Bridge.lean:216`, `:225`), and the run-order measurement at the
Arith rungs (`Green.lean:1367`–`:1396`). Two restatements against §2.6 as printed: the law
needs `ConstsDeclaredEnv Γ` (the `tConst` case of MetaRocq's `wellformed` under `wf_glob`,
`../metarocq/erasure/theories/EWellformed.v:166`, `:211`), refuted otherwise by
`SpecGrowFixture.specGrow_needs_declaredEnv`; and the composites' side condition sits at the
**source** term, as `ErasuresDeclared` (`ErasesLB.lean:478`), not at the emitted one.

The motive rewrite did not land, and wave 3's mid-wave audit found why it cannot land as
stated (`scratch/round7/W3-mid-refute.md`):

* **F1.** `Erasure.visitMutual` erases *every* member body (`Erasure.lean:1266-1272`) before
  it registers *any* member (`:1273-1276`). A member body's erasure image names the block's
  own keys at a moment when none of them is declared, so `ErasuresDeclared env Us Γ Δ e` is
  **false** at that sub-run (`erasuresDeclared_undeclared_const`), and with it every
  `.specGrow` transport of the sub-run's conclusion. The fact the transport wants is true
  there — `notRuntimeKey_cons_of_erases`, `lower_const_survives_fresh_defn` — so the law's
  *shape*, not the run, is what fails. It bites at G6 and at G7/G8's four `Nat.*` blocks.
* **F2.** `ErasuresDeclared` quantifies over every erasure image where only the composite's
  own witness is used, and is false at exactly the terms the run boxes
  (`erasuresDeclared_too_strong_at_box`). Not reachable at G1–G8; the bridge theorem
  quantifies over every supported term, so the ladder's silence is not a defence.
* **F3.** `ElimBlocksDeclared` follows from `ConstsDeclaredEnv` — both `ElimBody` shapes carry
  a `.case` node at the block and `constRefs` reads it — so the accumulator needs one clause,
  not two (`elimBlocksDeclared_of_constsDeclaredEnv`, landed at U7).
* **F5.** `Green.g7_constsDeclaredEnv`/`g8_constsDeclaredEnv` decide the condition at the
  **emitted** environments, where the law reads it at `Γspec`. They are non-vacuity evidence
  for the clause's shape, not instances of the hypothesis the law spends.

### 1.3 U7 — the content clause, and no aggregation

`64b8b17` lands `RegContent` (`ColdStartShape.lean:852`) — one witness read both ways, the
erasure at the declaration's level column and the `Lower` image of the emitted body — with
`declEnv : ConstsDeclaredEnv Γspec` beside it, `RegInvShape'.specGrow` and
`RegContent.specGrow` (`:796`, `:873`), `SpecEntryOk` and `SpecContent.cons` (`:742`, `:759`),
the two registration steps at a growing environment (`:959`, `:994`) and `regInv_cold_start`
(`:934`).

`visitExpr_regInv_all` is **not** stated, and the obstruction is not proof size. Its content
obligation at `Erasure.visitMutual`'s registering exits is the member's erasure at the empty
local context, which F-DEPLCTX leaves without a witness; and it cannot be got from the shape
induction instead, because `RunClosedW`'s registering clauses report the stored term's shape
while `RegInvShape'.defs` asks for `Lower Γspec b₀ t` (`U7-report.md` §2).

Two further findings bind this wave:

* **F4.** `SpecContent.blocks` fires at *every declared block key* and answers `IndCovered`,
  whose `elims` field demands an `ElimDecl` for the `casesOn` of every informative member
  (`ErasesEnv.lean:196-208`). The eliminator entry therefore enters `Γspec` at
  `Erasure.register_inductive`, not at `Erasure.visitCases`, and on **every** rung — including
  the four whose tables hold no `casesOn` name. Declared blocks per rung: 1, 2, 2, 3, 2, 1,
  12, 12 at G1…G8 (`scratch/round7/z_triv.out`).
* **F8.** Under a growing `Γspec`, nine of `RegInvShape'`'s twelve fields are preserved on
  general grounds; `defs` is the one the growth exists for, `spec.blocks`/`spec.elims` are
  threatened at `register_inductive` (F4) and `spec.defns` at a constant registration
  (F-DEPLCTX).

### 1.4 U8 — `RegKeyed` restated

`cc7560e` lands `RegKeyed` (`ColdStartShape.lean:1048`), `ConstExt.regKeyed` and
`regSaturated_of_regKeyed` (`SpecEnv.lean:162`). §2.8's own `RegKeyed` — one inclusive `Or`
triggered by mere key presence — makes `RegSaturated.inds` unprovable: `toKername` and
`rootKername` collide (`toKername \`id = rootKername "id"`, `by decide`), so the "constant"
disjunct cannot be excluded at a genuine block key. Reading each disjunct off the emitted
entry's own `GlobalDecl` shape closes that without assuming the collision away, and is what a
proof by induction on the run would produce anyway. `RegKeyed env sf` at a run is not proved.

### 1.5 U9 — a composition whose premises are jointly unsatisfiable

`6439576` lands `ReachableFrom.isSome_of_declaredEnv` — `erases_deps`' transitive condition,
proved from the δ column rather than assumed (`../metarocq/erasure/theories/Extract.v:324-329`)
— and `bridgeEnv_of_regContent` (`Capstone.lean:153`), which composes `hbridge`'s whole payload
out of four facts about the run's final state: `RegInvShape'`, `RegContent`, `RegKeyed`, and

```lean
(hsub : ∀ kn d, LBTerm.envLookup Γspec kn = some d → LBTerm.envLookup sf.gdecls kn = some d)
```

**`hsub` is declaration equality, and the four are contradictory at the rungs** (R1,
mechanised in `scratch/round7/z_hsub.lean`, clean axioms). Two independent arguments:

* *The content route.* `hsub` at `RegContent.defns`' own witness forces `b₀ = t`, collapsing
  the clause to `Erases env (lp n) [] b t`: the **emitted** body of a tabled name would have
  to be an erasure image. `Erases`' eleven arms produce no `.fix` and no `.case` node
  (`erases_shape`), and the emitted environments carry those at tabled keys — `spikeCase` at
  G5, `spikeRec` at G6, `Nat.add`/`mul`/`pow`/`sub` and `Nat.pred` at G7 and G8. Four
  refutations at the rungs' exact final states, `g5_regContent_hsub_false` …
  `g8_regContent_hsub_false`. This is not a corner of the fragment: `Lower` exists to turn a
  `.const`-keyed erasure image into a `.fix` or a `.case` node, so demanding that the two
  environments agree on bodies denies the pass.
* *The eliminator route*, independent of any body and reaching **all eight** rungs. `Γspec`
  declares every informative block's `casesOn` as an `ElimDecl` (F4) — a `RuntimeKey`, which
  `Lower.const` refuses and the eraser never emits. Zero emitted eliminator keys at every
  rung (`Green.elimKeys_undeclared`), so `hsub` fails there too
  (`hsub_false_of_undeclared`, `g7_hsub_false_elim`).

The repair is proved in the same probe: `hsub` is spent in exactly one place,
`regSaturated_of_regKeyed`, whose two fields read only the emitted entry's **shape**. W1 lands
it. Separately, U9 corrected `hargReach`'s residue: the content clause is an *antecedent* of
that binder, not something it waits on, and what is left is a source-side non-erasability fact
about `benchArith`'s tabled body (`scratch/round7/u9_g8.lean`).

### 1.6 The two shipping findings this wave waits on

* **F-DEPLCTX** (`03-DEV-FIX.md`): `Erasure.visitMutual` re-enters a dependency at
  `Erasure.lean:889` and `:912` without resetting `ErasureContext.lctx`. The edit is one
  `withReader` field, `lctx := {}` beside the level column; the dependency's body is closed,
  so nothing is lost. Until it merges, **no `BridgeInv` exists at a member sub-run**, so
  `Motive6` cannot report content and W4, W5, W6 and W7 have no statement to prove.
* **F-ARITYLET** (`03-DEV-FIX.md`): `Erasure.arityResultSort` (`Erasure.lean:281-285`) stops
  at `.letE` and `.mdata` where the kernel's `destArity`
  (`../metarocq/pcuic/theories/PCUICAst.v:486-490`) and lean4lean's `TrExprS` see through, so
  `IndFlagSound` has only its sound half (`ErasesEnv.lean:66`). W9 was to be the biconditional
  after the merge; it is not available, and §2.9 records the refutation instead.

## 2. The units

Gates assume the battery of `doc/rework/07-STATUS.md` §6 stays green and that the measured
33-name footprint of `shipping_erase_correct_firstorder` and of `green_G1`…`green_G8` does not
grow. "R" needs real reasoning, "M" is mechanical.

| id | title | kind | depends | waits for merge |
|---|---|---|---|---|
| W1 | `hsub` restated, the composition rebuilt | M | — | no |
| W2 | the transport law's side condition | R | — | no |
| W3 | the eliminator entry at `register_inductive` | R | W1 | no |
| W4 | `Motive6`'s content at a member sub-run | R | W2 | **F-DEPLCTX** |
| W5 | the aggregation `visitExpr_regInv_all` | R, large | W2, W3, W4 | **F-DEPLCTX** |
| W6 | `RegKeyed` at a run | R | — | no (F-W8-8; the row was wrong) |
| W7 | `hbridge` discharged, `hargReach` reduced | M | W1, W5, W6 | **F-DEPLCTX** |
| W8 | the three dead slots | M | W4 | no |
| W9 | the inductive flag as MetaRocq's equation | R | — | **F-ARITYLET** |

W1, W2, W3, W6 and W8's `compilerLevels` item can be worked today; the rest are gated.

### 2.1 W1 — `hsub` restated as `SpecKeysEmitted`

**The statement**, landed from `scratch/round7/z_hsub.lean`, where it is proved:

```lean
/-- A specification key that is not a runtime key has *some* emitted entry of the matching
shape. MetaRocq's pruning statement (`erases_global_decls`, `Extract.v:287`) reads the same
way: the emitted environment answers the keys the specification keeps, not their bodies. -/
structure SpecKeysEmitted (Γspec : GlobalDeclarations) (s : ErasureState) : Prop where
  consts : ∀ (kn : Kername) (cb : ConstantBody),
    LBTerm.envLookup Γspec kn = some (.constantDecl cb) → ¬ RuntimeKey Γspec kn →
    ∃ cb' : ConstantBody, (kn, GlobalDecl.constantDecl cb') ∈ s.gdecls
  inds : ∀ (kn : Kername) (mib : MutualInductiveBody),
    LBTerm.envLookup Γspec kn = some (.inductiveDecl mib) →
    ∃ mib' : MutualInductiveBody, (kn, GlobalDecl.inductiveDecl mib') ∈ s.gdecls

theorem regSaturated_of_regKeyed (hk : RegKeyed env s) (hs : SpecKeysEmitted Γspec s) :
    RegSaturated env Γspec s
```

The name stays; the `_H : RegInvShape'` argument, unspent since `cc7560e`, goes with `hsub`.
`bridgeEnv_of_regContent` then takes `hkeys : SpecKeysEmitted Γspec sf` in `hsub`'s place and
is otherwise unchanged — the proof is four lines, `regSaturated_of_regKeyed` followed by
`bridgeEnv_of_regInv` at the derived `hdeps`.

*Files.* `SpecEnv.lean` (the structure beside `RegSaturated`, `:107`; the theorem, `:162`),
`Capstone.lean` (`bridgeEnv_of_regContent`, `:153`, and its docstring's residue list).

*Consumers.* `bridgeEnv_of_regContent` is the only one today; W5 makes `SpecKeysEmitted` a
clause of the accumulator and W7 spends the pair.

*Gate.* `scripts/ledger.sh` — `test/ledger.expected`'s `bridgeEnv_of_regContent` row stays at
three names; `grep -n "hsub" LeanToLambdaBox/SpecEnv.lean LeanToLambdaBox/Capstone.lean`
empty; `lake exe green-check --all`.

*Confidence.* High: both statements are **proved**, at the rungs' own data in
`z_hsub.lean` and again at HEAD in `w8_sigs.lean` (`regSaturated_of_regKeyed_shape`,
`bridgeEnv_of_regContent`, `[propext, Classical.choice, Quot.sound]`). Unlike `hsub`,
`SpecKeysEmitted` is satisfiable at G5–G8: it says nothing about bodies and exempts runtime
keys.

### 2.2 W2 — the transport law's side condition, after F1 and F2

**The choice, decided by the probe.** W3-mid F1 offers two repairs: state the `.specGrow` side
condition as runtime-key stability at the witness's references, or widen `SpecGrow`'s third
clause to exempt the growing prefix's own keys and carry "no prefix entry at a reference is an
`ElimBody`" where the eliminator step needs it. **The first.** Read at the fix-block member
sub-run the two differ only in where the same fact sits: `Lower.const`'s premise is
`¬ RuntimeKey Γ kn` and what the step must carry forward is that it survives the block's own
prefix. The prefix entries are the registered member bodies, each
`Erasure.etaExpandFix defs j = LBTerm.etaFix defs j` (F-ETA), and

```lean
theorem notElimBody_etaFix : ¬ ElimBody iid np dp nfs (LBTerm.etaFix defs j)
```

(`w8_sigs.lean`, proved, `[propext, Quot.sound]`), so no prefix key of that step is a runtime
key at all. Widening `SpecGrow`'s clause buys nothing that this does not: the widened clause
is derivable from the landed one — a runtime key of `pre ++ Γ` is declared there, hence in
`pre` or in `Γ` — and it would still need the same prefix-side fact, while rebuilding
`SpecGrow.of_fresh`, `SpecGrow.trans` and the seven transports around a second shape.
`SpecGrow` therefore stays verbatim.

```lean
/-- The keys a term names, at which a growth must not create a runtime key: `Lower.const`'s
anti-monotone premise (`Lower.lean:343`), carried across the growth at exactly those keys. -/
def RefsStable (Γ Γ' : GlobalDeclarations) (t : LBTerm) : Prop :=
  ∀ kn ∈ constRefs t, ¬ RuntimeKey Γ kn → ¬ RuntimeKey Γ' kn

theorem RefsStable.of_constsDeclared (hg : SpecGrow Γ Γ') (hd : ConstsDeclared Γ t) :
    RefsStable Γ Γ' t
theorem RefsStable.trans (h : RefsStable Γ Γ' t) (h' : RefsStable Γ' Γ'' t) :
    RefsStable Γ Γ'' t
theorem refsStable_of_freshPrefix (hg : SpecGrow Γ (pre ++ Γ))
    (hpre : ∀ p ∈ pre, ∀ body iid np dp nfs,
      p.2 = GlobalDecl.constantDecl ⟨some body⟩ → ¬ ElimBody iid np dp nfs body) :
    RefsStable Γ (pre ++ Γ) t

/-- `Lower` is monotone along growth, at the term's own references. -/
theorem Lower.specGrow (hg : SpecGrow Γ Γ') (henv : ConstsDeclaredEnv Γ) (h : Lower Γ s t)
    (hst : RefsStable Γ Γ' s) : Lower Γ' s t
theorem LowerAlt.specGrow (hg : SpecGrow Γ Γ') (henv : ConstsDeclaredEnv Γ)
    (h : LowerAlt Γ nf m alt) (hst : RefsStable Γ Γ' m) : LowerAlt Γ' nf m alt
```

`RefsStable.of_constsDeclared` keeps every existing call site working: the old premise is the
new one under `SpecGrow`. The `const` arm is the only one that reads it; the three fix arms
read `ConstsDeclaredEnv` at the block's declared bodies and `SpecGrow`'s third clause at the
block key, which is declared.

**F2's half.** The composites' side condition moves from every erasure image of the source to
the images that lower to the emitted term, which is the witness the transport actually
destructs:

```lean
/-- The side condition at the composite's own witness. Restricting to images that lower to
`t` is what removes the boxed-constant counterexample (`W3-mid-refute.md` F2): a boxed source
constant's other image is a `.const` node, which lowers to no `.box`. -/
def ErasuresStable (env : VEnv) (Us : List Name) (Γ Γ' : GlobalDeclarations) (Δ : VLCtx)
    (e : Expr) (t : LBTerm) : Prop :=
  ∀ t₀, Erases env Us Δ e t₀ → Lower Γ t₀ t → RefsStable Γ Γ' t₀

theorem ErasesLB.specGrow (hg : SpecGrow Γ Γ') (henv : ConstsDeclaredEnv Γ)
    (hst : ErasuresStable env Us Γ Γ' Δ e t) (h : ErasesLB env Us Γ Δ e t) :
    ErasesLB env Us Γ' Δ e t
theorem ErasesLBMode.specGrow (hg : SpecGrow Γ Γ') (henv : ConstsDeclaredEnv Γ)
    (hst : ErasuresStable env Us Γ Γ' Δ e t) (h : ErasesLBMode tbl ctx env Us Γ Δ e t) :
    ErasesLBMode tbl ctx env Us Γ' Δ e t
```

with `ErasesLBAlt`, `ErasesLBFix`, `ErasesLBFixAlt` and `ErasesLBAltMode` following at their
own targets (`ErasesLBFix`'s condition reads the `Lower` target *before* `ConstToFVar`, which
is the term the pass's premise mentions). `ErasuresDeclared` is **not** deleted: it keeps one
consumer, `bridgeEnv_of_regContent`'s `hde`, where the closure
`ReachableFrom.isSome_of_declaredEnv` reads it at the prepared term and where F1's
counterexample does not apply — the prepared term is the run's entry, not a block member's
body.

*Files.* `Lower.lean` (`RefsStable` and its three lemmas beside `ConstsDeclared`, `:2310`; the
two laws at `:2564`, `:2640`), `ErasesLB.lean` (`ErasuresStable` at `:478`, the four
transports `:483`–`:515`), `Bridge.lean` (`:216`, `:225`).

*Consumers to rewire.* The six `SpecEnv.mono` sites U6 §5 schedules —
`VisitExprRefines/Step/Mechanical.lean:342`, `:592`, `VisitExprRefines/Step/Passes.lean:1197`,
`:1276`, `:1330`, `:1333` — and `ColdStartShape.lean`'s two uses of the law inside
`RegInvShape'.specGrow` (`:796`) and `RegContent.specGrow` (`:873`), which pass
`RefsStable.of_constsDeclared` at a declared body and are unchanged in content.

*Gate.* `lake build`; the four composite transports and the two laws re-close;
`Green.g7_elimCons_specGrow` and `g7_constsDeclaredEnv` unchanged; `scripts/ledger.sh`
unchanged.

*Confidence.* The `const` arm is a one-line substitution and the rest of `Lower.specGrow`'s
induction does not read the side condition except to propagate it, so `RefsStable` needs the
same four projections `ConstsDeclared` has (`.args`, `.alts`, `.discr`, `.spine`). The risk is
`refsStable_of_freshPrefix`, whose proof is a case split on whether the reference lands in the
prefix. Probe: all six statements elaborate and three are proved (`w8_sigs.lean`); the
fix-step facts are proved in `scratch/round7/y_law.lean`.

### 2.3 W3 — the eliminator entry at `register_inductive` (F4)

`Erasure.register_inductive` conses the block; `SpecContent.blocks` then fires at that key and
`IndCovered.elims` demands an `ElimDecl` for the `casesOn` of every informative member. The
specification-side prefix the step conses is therefore the block **together with** its
eliminator entries, and `SpecEntryOk` cannot state it: that structure says the key is neither
a modelled block's nor a modelled eliminator's, which is the shape a *constant* registration
has.

```lean
/-- What one `Erasure.register_inductive` owes the specification environment: the block the
run conses, and one eliminator body per informative member — `erases_mutual_inductive_body`
(`../metarocq/erasure/theories/Extract.v:276`) plus the `casesOn` declarations λ□ prunes. -/
structure IndPrefixOk (env : VEnv) (bo : Name → Option Expr) (lp : Name → List Name)
    (I : Name) (pre : GlobalDeclarations) : Prop where
  covered : IndCovered env pre I
  entries : ∀ p ∈ pre, (∃ mib : MutualInductiveBody, p.2 = .inductiveDecl mib) ∨
    ∃ body iid np dp nfs, p.2 = .constantDecl ⟨some body⟩ ∧ ElimBody iid np dp nfs body

theorem SpecContent.consBlock (H : SpecContent env bo lp Γ)
    (hfresh : ∀ p ∈ pre, ∀ q ∈ Γ, p.1 ≠ q.1) (hnd : (pre.map Prod.fst).Nodup)
    (hpre : IndPrefixOk env bo lp I pre) : SpecContent env bo lp (pre ++ Γ)

theorem regInv_registerInd_step (P : ErasureSpec lenv env Us gw)
    (H : RegInvShape' env bo lp Γ s) (C : RegContent env bo lp Γ s)
    (K : SpecKeysEmitted Γ s)
    (hfind : lenv.find? indinfo.name = some (.inductInfo indinfo))
    (hmiss : s.inductives.get? indinfo.name = none)
    (hrun : Erasure.register_inductive indinfo s ctx cctx ref w = .ok (r, s₁) w₁) :
    ∃ Γ' : GlobalDeclarations, SpecGrow Γ Γ' ∧ RegInvShape' env bo lp Γ' s₁ ∧
      RegContent env bo lp Γ' s₁ ∧ SpecKeysEmitted Γ' s₁
```

The model content of the prefix is `ErasureSpec.BlockAdequate` (`ErasureSpec.lean:379`):
`fwd` gives `IndInfo env m ⟨indBlockKername iv.all, i⟩ iv.numParams nfs` at each member and
`casesOnDecl` gives the eliminator's `CasesOnShape` and `ConstOrigin`, which are exactly
`IndCovered`'s two fields. `SpecGrow`'s third clause is `SpecGrow.of_fresh` at
`ElimBlocksDeclared`, discharged from `RegContent.declEnv` by
`elimBlocksDeclared_of_constsDeclaredEnv` (F3); `SpecKeysEmitted` survives because the prefix
adds one block key, which the run emits, and eliminator keys, which are runtime keys and so
exempt from its `consts` clause.

**G1–G4 accounted.** `Green.elimKeys_undeclared` measures the tabled `casesOn` keys at G5–G8
only; the entry is owed on every rung (1, 2, 2, 3 declared blocks at G1–G4), so the unit
generalises `Green.g7_elimCons_specGrow` (`Green.lean:1396`) from a G7 statement about one key
to a statement over any `Γ` whose declared keys the emitted environment answers, and adds the
kernel-grade freshness measurement at the other seven rungs — `y_chain.out`'s
`g2_spec_keys_nodup`/`g7_spec_keys_nodup` are the precedent.

*Files.* `ErasesEnv.lean` (`IndPrefixOk` beside `IndCovered`, `:196`), `ColdStartShape.lean`
(`SpecContent.consBlock` beside `SpecContent.cons`, `:759`; the step beside
`regInv_constCons_step`, `:994`), `Green.lean` (`:1367`–`:1396`).

*Consumers.* W5, at `Step3`, `Step10` and `Step17` — `Erasure.visitConstructor`,
`Erasure.visitProj` and `Erasure.visitCases`, the three members that call
`register_inductive`.

*Gate.* `lake exe green-check --all`; the generalised `elimCons` lemma decides at all eight
rungs; `lake exe hygiene --dead` does not grow (both files are inside the closure).

*Confidence.* Not F-DEPLCTX-blocked: a block key and a `casesOn` key owe no erasure, `bo`
being `none` at a `casesOn` name — measured at G5–G8, where `Nat.casesOn` is tabled *without*
a body, so `SpecContent.defns` never fires at it and `erases_ne_elimBody` is never
contradicted (`W3-mid-refute.md` F6). The risk is `SpecContent.consBlock`'s `defns` case at a
second source name mapping to a prefix key (`toKername` is not injective, F-KERNAME), which is
what `SpecEntryOk`'s quantifier handles and what `IndPrefixOk` must handle the same way.
Probe: all three statements elaborate (`w8_sigs.lean`).

### 2.4 W4 — `Motive6`'s content at a member sub-run

**Waits for F-DEPLCTX.** With `lctx := {}` installed beside the level column at
`Erasure.lean:889` and `:912`, `BridgeInv` holds at `Δ = []` at the member's own column, which
is what `U5.bridgeInv_nil_lctx` says is otherwise impossible, and `Motive1` at that scope —
U5's quantifier — reports there.

```lean
/-- The member's body, erased where `erase_constant_body` erases it: the empty local context,
at the declaration's own universe context (`Extract.v:264`). -/
theorem visitMutual_member_erases (P : ∀ Us, ErasureSpec lenv env Us gw)
    (E : EraserAsks lenv env gw) (htbl : SourceTableAdequate lenv tbl)
    (hsafe : TableSafe lenv tbl) (hblk : TableBlocks lenv env tbl) (hcfg : ConfigPinned cfg)
    (hbo : tbl.body? m = some b) (hsup : Supported env tbl (.const m []))
    (hvis : Erasure.visitExpr b s { «config» := cfg } cctx ref w = .ok (t, s') w') :
    ∀ Γ₀, RegInvShape' env tbl.body? tbl.levels? Γ₀ s →
      RegContent env tbl.body? tbl.levels? Γ₀ s →
      ∃ Γ₁ b₀, SpecGrow Γ₀ Γ₁ ∧ Erases env (tbl.levels? m) [] b b₀ ∧ Lower Γ₁ b₀ t
```

The α transport U4 landed is what lets the conclusion read the **tabled** body while the run
erases `prepare_erasure (compilerValue lenv n)`; `SourceTableAdequate.body?_prepared`
(`Witness/SourceTable.lean:251`) is its premise, and `compilerLevels` (`:246`) is what makes
`tbl.levels? m` the column the run installed. `Motive6` then carries the accumulator:

```lean
def Motive6 (f : Name → EraseM Unit) : Prop :=
  (∀ n s ctx cctx ref w u s' w', f n s ctx cctx ref w = .ok (u, s') w' →
    ∀ Us Δ, BridgeInv env Us tbl cfg (gw w) ctx s Δ → Supported env tbl (.const n []) →
      (tbl.decl? n).isSome →
      (s'.constants.get? n).isSome ∧ RunConcl s s' ∧ IndRegistryModelled env s' ∧
        gw w ≤ gw w' ∧
        ∀ Γ₀, RegInvShape' env tbl.body? tbl.levels? Γ₀ s →
          RegContent env tbl.body? tbl.levels? Γ₀ s → SpecKeysEmitted Γ₀ s →
          ∃ Γ₁, SpecGrow Γ₀ Γ₁ ∧ RegInvShape' env tbl.body? tbl.levels? Γ₁ s' ∧
            RegContent env tbl.body? tbl.levels? Γ₁ s' ∧ SpecKeysEmitted Γ₁ s') ∧
  f ⊑ Erasure.visitMutual
```

**`TableBlocks` gets its consumer here.** The block branch's sub-runs conclude `ErasesLBFix`,
not `ErasesLB`, and the pair they conclude against is what `blockKeyed_install`
(`VisitExprRefines/Step/Env.lean:609`) builds — from `TableBlocks.members`, the table's key
separation, and the distinctness `run_rec_exit_reg`'s fifth conclusion (`:268`) reports off
the successful run rather than assuming. The consumer is one line:

```lean
theorem visitMutual_block_mode (hblk : TableBlocks lenv env tbl) (hsup : Supported env tbl e)
    (htab : (tbl.decl? n).isSome)
    (hnd : ((ci.all.map remove_unsafe_rec).map toKername).Nodup)
    (hfb : fixBlock? lenv n = some (ci.all.map remove_unsafe_rec))
    (hlen : ids.length = ci.all.length)
    (hfx : ctx.fixvars = some (fixvarMap (ci.all.map remove_unsafe_rec) ids))
    (h : ErasesLBMode tbl ctx env Us Γ Δ e t) :
    ErasesLBFix env Us Γ ((ci.all.map remove_unsafe_rec).map toKername) ids Δ e t :=
  h.2 _ _ (blockKeyed_install hblk hsup htab hnd hfb hlen hfx)
```

which is **proved** in `w8_sigs.lean` at HEAD. What `blockKeyed_install` still needs is `hfb`,
the correspondence between the run's `Lean.Compiler.LCNF.getDeclInfo?` answer and
`Witness.fixBlock?`; that is a class-**D** clause about a named Lean primitive, admissible
under rule (2), and it is the one new bundle field this wave adds. If W4 lands without it —
i.e. if the block branch's content cannot be stated — then `TableBlocks` and its ten binders
are deleted under W8 instead.

*Files.* `VisitExprRefines/Motives.lean` (`Motive6`, `:176`; `Step6`, `:977`),
`VisitExprRefines/Step/Env.lean` (`step6`, `:674`; the install's consumer),
`ErasureSpec.lean` (the `fixBlock?` clause, if taken).

*Gate.* `step6` closes; `lake exe hygiene --dead` loses `blockKeyed_install`,
`run_rec_exit_nodup` and `run_rec_exit_reg`'s fifth conclusion from its unconsumed set;
`grep -rn "no consumer" LeanToLambdaBox/VisitExprRefines/Step/Env.lean` empty.

*Confidence.* The statement is what the run supplies once the reader is repaired, and the α
and level transports are landed. The residual risk is `erases_strengthen_closed`'s two
premises (`ErasableStrengthen env (lp n)`, `NoProjBinders b`) if any sub-derivation still
needs strengthening from a non-empty `Δ` — after F-DEPLCTX it should not, the reader's context
being empty. Probe: both statements elaborate, the second proved (`w8_sigs.lean`).

*Landed* (`scratch/round7/W4-report.md`), with one boundary correction. The three theorems a
member sub-run needs are in `VisitExprRefines/Step/Env.lean`, sorry-free: `bridgeInv_member`
— the invariant at the reader the switch installs, `Δ = []` at the member's own column, which
is F-DEPLCTX made positive; `visitMutual_block_mode`, `blockKeyed_install`'s consumer; and
`visitMutual_member_erases` / `..._block`, which carry a sub-run's `ErasesLBMode` conclusion
to the **tabled** body at the **tabled** column through `SourceTableAdequate.erases_prepared`
(U4's α) and `compilerLevels?_eq`. `hfb` stays a premise, so no bundle field is added yet.

The **`Motive6`/`Step6` extension is W5's, not this unit's.** The printed clause needs a `Γ₁`
with `RegInvShape'`/`RegContent` at the *sub-run's* exit state, and the only hypothesis
`Step6` has about that sub-run is `Motive1`, whose `RunRefines` (`Motives.lean:55`) carries no
such clause: its fourth conjunct is guarded by a `SpecEnv` of the exit state, which is what
the accumulator would have to produce. So a stronger `Motive6` and a stronger `Motive1` are
one fixpoint induction, and the §2 table's `W5 depends on W4` is right about the *lemmas* and
wrong about the motive — extending `Motive6` ahead of `RunRefines` costs a `sorry`.

Nor is the weaker, ∀-`Γspec` clause a way round it, and the reason is the one §3 already
names. At the **non-recursive** exit it would go through: `SpecEnv.mono` carries a final-state
environment down to the sub-run's exit state, `Motive1` reports there, and
`visitMutual_member_erases` is the rest. At the **block** exit it does not: the registered
body is `Erasure.etaExpandFix defs j`, its `Lower` fact is `Lower.fixEta_of_block`, and
`LowerBlock.hdecl` asks the environment to declare each member with *the run's own* erasure
witness where `SpecContent.defns` supplies only *some* erasure of that body. That is the
determinism gap `RegContent` was introduced to close, and closing it is what makes the
environment an output. The second induction does not avoid it either — `visitExpr_shapeW`'s
`RunClosedW` gives a registering exit only the emitted term's *shape*, never that it is an
erasure image.

### 2.5 W5 — the aggregation

**Waits for F-DEPLCTX**, through W4. The accumulator is threaded through the three refinement
relations and the eighteen step lemmas:

```lean
def RunRefines (env : VEnv) (Us : List Name) (tbl : SourceTable) (ctx : ErasureContext)
    (Δ : VLCtx) (s s' : ErasureState) (gen gen' : NameGenerator) (e : Expr) (t : LBTerm) :
    Prop :=
  RunConcl s s' ∧ IndRegistryModelled env s' ∧ gen ≤ gen' ∧
    ∀ Γ₀, RegInvShape' env tbl.body? tbl.levels? Γ₀ s →
      RegContent env tbl.body? tbl.levels? Γ₀ s → SpecKeysEmitted Γ₀ s →
      ∃ Γ₁, SpecGrow Γ₀ Γ₁ ∧ RegInvShape' env tbl.body? tbl.levels? Γ₁ s' ∧
        RegContent env tbl.body? tbl.levels? Γ₁ s' ∧ SpecKeysEmitted Γ₁ s' ∧
        (∀ Γ₂, SpecGrow Γ₁ Γ₂ → ErasuresStable env Us Γ₁ Γ₂ Δ e t) ∧
        ErasesLBMode tbl ctx env Us Γ₁ Δ e t
```

with `RunRefinesAlt` and `HeadRefines` the same shape at their own composites
(`Motives.lean:55`, `:62`, `:71`). The fifth conjunct is what W2 makes payable: a later step's
growth is a fresh prefix of the run's own registrations, and `refsStable_of_freshPrefix` is
what discharges it at a block registration, `RefsStable.of_constsDeclared` everywhere else.

```lean
theorem visitExpr_regInv_all (P : ∀ Us, ErasureSpec lenv env Us gw)
    (E : EraserAsks lenv env gw) (A : UpstreamAsks env)
    (htbl : SourceTableAdequate lenv tbl) (hsafe : TableSafe lenv tbl)
    (hblk : TableBlocks lenv env tbl) (hcb : CompilerBodies lenv env tbl.body?)
    (hcfg : ConfigPinned ctx.config) (hsup : Supported env tbl e)
    (hvis : Erasure.visitExpr e s ctx cctx ref w = .ok (t, s') w') :
    ∀ Γ₀, RegInvShape' env tbl.body? tbl.levels? Γ₀ s →
      RegContent env tbl.body? tbl.levels? Γ₀ s → SpecKeysEmitted Γ₀ s →
      ∃ Γ₁, SpecGrow Γ₀ Γ₁ ∧ RegInvShape' env tbl.body? tbl.levels? Γ₁ s' ∧
        RegContent env tbl.body? tbl.levels? Γ₁ s' ∧ SpecKeysEmitted Γ₁ s'
```

`SpecKeysEmitted` is a clause of the accumulator rather than a premise beside it, which is
what `U8-report.md` §5 asks: it is a property of how `Γ₁` is *built*, so only the induction
that builds it can prove it.

**Which fields need real preservation, per step** (F8; `Γ₁ = Γ₀` and `SpecGrow.refl` at a step
that registers nothing):

| steps | what the step does | fields needing a real argument |
|---|---|---|
| 1, 2, 7, 8, 9, 11, 12, 13, 14, 15, 16 — `visitExpr`, `visitLiteral`, `visitAppArgs`, `visitLet`, `visitLambda`, `visitApp`, `visitConstApp`, the four η walkers | compose sub-runs | none of their own: `SpecGrow.trans` composes the sub-runs' growths, and `defs` is re-derived at each by `Lower.specGrow`, whose premise is `RegContent.declEnv` at that body |
| 4, 5, 6 — `visitConst`, `get_constant_kername`, `visitMutual` | register a constant or a block | **`spec.defns`** — the member's erasure at `Δ = []` (W4, F-DEPLCTX); **`defs`** at the new key, `regInv_constCons_step`'s `hlow`; `defsTotal` at the new key; `axioms` at the body-less exits |
| 3, 10, 17 — `visitConstructor`, `visitProj`, `visitCases` | call `register_inductive` | **`spec.blocks`, `spec.elims`** — W3's prefix supplies `IndCovered` where `SpecEntryOk` refutes the trigger; `inds`, `indsEmitted` at the new registry entry |
| 18 — `visitAlt` | a sub-run under a binder telescope | none of its own; the growth is the sub-run's, and `ErasesLBAltMode` transports by `LowerAlt.specGrow` |

Preserved on general grounds at every step: `specClosed`, `specFVarFree`, `consts`, `keys`,
`sub`, `closed`, and `defsTotal` whose `¬ RuntimeKey Γ₁` premise is the *stronger* one
(`RuntimeKey.specGrow` is the free direction).

*Files.* `VisitExprRefines/Motives.lean` (the three relations and the eighteen motives),
`VisitExprRefines/Step/{Mechanical,Passes,Env}.lean` (the eighteen step lemmas),
`VisitExprRefines.lean` (the aggregator), `ColdStartInduction.lean`.

*Consumers.* W6 reads the same induction for `RegKeyed`; W7 spends the conclusion at the
entry state, where `regInv_cold_start` (`ColdStartShape.lean:934`) inhabits the accumulator at
`Γ₀ = []` and `s = {}` unconditionally and `SpecKeysEmitted [] {}` is vacuous.

*Gate.* the eighteen step lemmas re-close; `lake build`; `scripts/erasesLB.sh` green with T8's
footprint unchanged; `lake exe hygiene --dead` unchanged at 321.

*Confidence.* This is the wave's largest obligation. Every ingredient is landed or specified —
the growth transports (U6), the two registration steps and the content clause (U7), W3's
inductive step, W4's member content — and the risk is proof size plus the eleven transport
steps' mechanical rewrite, not truth. Probe: the three relations and the theorem elaborate
(`w8_sigs.lean`).

*Not landed* (`scratch/round7/W5-report.md`), with one restatement and one measured blocker.
The accumulator itself is landed — `RegAcc` (`ColdStartShape.lean`), the triple this section
quantifies, with `RegAcc.coldStart`, `SpecKeysEmitted.nil`/`.cons`, and the three registration
steps restated to take and return it; `bridgeEnv_of_regContent` reads it in place of its first
three premises. `visitExpr_regInv_all` is not stated.

**The relations are restated: the accumulator is an independent conjunct, not a rewrite of the
fourth.** F-W8-1 refutes the fifth conjunct and prescribes "drop the promise, transport at the
growth site as the six `SpecEnv.mono` uses do". Dropping it leaves this section's fused
`RunRefines` unprovable at *every* composition step: the fourth conjunct then reads the
accumulator's own `Γ₁`, a sibling's conclusion has to cross the next sub-run's growth, and the
step's only fact about that growth is `SpecGrow` — which does not carry a `Lower` conclusion.
Mechanised at the tree's own fixture, `scratch/round7/w5_probe.lean`
(`runRefines_fused_not_composable`, `[propext, Quot.sound]`): `Lower gsmall aBody aBody`,
`SpecGrow gsmall ggrown`, `¬ Lower ggrown aBody aBody`, the prefix being the eliminator entries
`Erasure.register_inductive` conses. There is no growth site to transport at either — the later
sub-run binds its `Γ₂` existentially.

The principled form keeps the fourth conjunct as it stands, `∀ Γspec, SpecEnv … s' Γspec →
ErasesLBMode … Γspec …`, and adds the accumulator beside it as a conjunct mentioning no term:

```lean
  RunConcl s s' ∧ IndRegistryModelled env s' ∧ gen ≤ gen' ∧
    (∀ Γspec, SpecEnv env tbl.body? tbl.levels? s' Γspec →
      ErasesLBMode tbl ctx env Us Γspec Δ e t) ∧
    ∀ Γ₀, RegAcc env tbl.body? tbl.levels? Γ₀ s →
      ∃ Γ₁, SpecGrow Γ₀ Γ₁ ∧ RegAcc env tbl.body? tbl.levels? Γ₁ s'
```

Composition is then `SpecGrow.trans` with no term-side transport at all, the eleven transport
steps keep their proofs unchanged, and `HeadRefines` needs no thread. §2.4's objection to "the
weaker, ∀-`Γspec` clause" does not apply to this shape: what it refutes is instantiating at an
environment *fixed in advance*, and the accumulator hands step 6 the environment of the member
sub-run's **own exit state** — `RegAcc.shape.specEnv` there, `SpecEnv.mono` down to each earlier
sub-run — so the witness `LowerBlock.hdecl` needs is the one the step itself declared. The
environment is still an output; `visitExpr_regInv_all`'s printed statement is unchanged.

**Blocker: steps 3, 10 and 17 have no `register_inductive` growth to take.** The table reads
"W3's prefix supplies `IndCovered`". It does not: W3 (`W3-report.md` §2.1) landed
`SpecContent.append` and `regInv_registerInd_step`, which *assume* `hpre : SpecContent env bo
lp pre` together with seven further side conditions, and declined `IndPrefixOk`; nothing
constructs the prefix from a run. `IndCovered` is never *introduced* anywhere in the tree — its
only lemma is `IndCovered.lookupMono`, which transports one, and the `natEnv` fixture supplies
its `elims` payload alone (`SpecEnv.lean`, `natEnv_elimCovered`) — and `RegInvShape'.inds`,
`.indsEmitted` and `SpecContent.blocks` all fire at every member `Erasure.register_inductive`
inserts. Until that producer exists — block entry plus one `mkElimBody` entry per informative
member, `IndBodyOf`/`IndFlagSound`/`ElimDecl` from `BlockAdequate`, and an F-KERNAME
collision-freeness clause for the prefix's `defns`/`axioms` — the eighteen motives cannot be
inhabited, and the change to the relations is all-or-nothing. The unit's remainder is therefore
re-planned as W5a (the `register_inductive` producer), W5b (`visitMutual`'s registering exits at
a growing environment, of which the two constant ones are now landed), W5c (the motive conjunct,
the eighteen steps and the aggregator).

### 2.6 W6 — `RegKeyed` at a run

**Waits for F-DEPLCTX** only in its `inds` clause's provenance, not in its shape. The `consts`
clause is each registration primitive's own writer — `addAxiomState`, `nonrecConstState`,
`addRealizerState` and the block loop all write a `.constantDecl` at a `toKername` — and is a
`RunClosedW` motive (`ColdStartInduction.lean:225`), which reads the state alone. The `inds`
clause needs `IndInfo env n iid np nfs` at every registered inductive; today only
`BridgeInv.indRegistryModelled` (`Bridge.lean:339`, `:238`) carries model content at the
registry, and it is conditional on `IndArity`.

```lean
theorem regKeyed_of_run (P : ∀ Us, ErasureSpec lenv env Us gw)
    (htbl : SourceTableAdequate lenv tbl) (hcfg : ConfigPinned ctx.config)
    (hvis : Erasure.visitExpr e s ctx cctx ref w = .ok (t, s') w') (hk : RegKeyed env s) :
    RegKeyed env s'

theorem regKeyed_empty : RegKeyed env ({} : ErasureState)
```

The `inds` case is discharged where the block is registered, from
`ErasureSpec.BlockAdequate.fwd` at the `InductiveVal` `Erasure.register_inductive` was called
with — which gives `IndInfo env m ⟨indBlockKername iv.all, i⟩ iv.numParams nfs` directly, at
the key `Erasure.lean:321` mints — rather than from `IndRegistryModelled`, whose `IndArity`
premise the step has no reason to hold. That is the measurement `U9-report.md` §6.2 asks for,
and it comes out in favour of the `RunClosedW` motive with `BlockAdequate` at the registering
clause: no new bundle field, and the model content is the one `P` already carries.

*Files.* `ColdStartShape.lean` (beside `RegKeyed`, `:1048`), `ColdStartInduction.lean` (the
motive).

*Consumers.* W7, through `regSaturated_of_regKeyed` (W1).

*Gate.* `scripts/ledger.sh` unchanged; the theorem's footprint is `P`'s, so no new axiom;
`lake build`.

*Confidence.* `regKeyed_empty` is proved (`w8_sigs.lean`). The run-level statement is a
sixteen-clause `RunClosedW` instantiation whose only non-mechanical clause is the block
registration's; the shape-indexed restatement U8 landed is what makes each clause immediate,
since a registration primitive writes a statically known `GlobalDecl` constructor.

*Landed* (`scratch/round7/W6-report.md`), sorry-free, with three corrections. **F-W8-8 is
right and the gate row was wrong**: the route reads the state alone, needs no `BridgeInv`, and
was workable at this checkpoint. `regKeyed_of_run` and `runClosedW_regKeyed` are in
`VisitExprRefines/Step/Passes.lean`, not `ColdStartInduction.lean`: the `inds` clause spends
`pass_register_inductive_entry` (`:411`) for "a member of the block is in the registry", and
`ColdStartInduction` is upstream of both it and `run_prepare_erasure_ok`. The shape half —
`regKeyed_empty`, `RegKeyed.indCons`, `regKeyed_recConstState` — is in `ColdStartShape.lean`
beside `ConstExt.regKeyed`. `htbl : SourceTableAdequate lenv tbl` is dropped: the motive sees
no term, so no registration it observes is known to be tabled and the binder is unspent.

**It costs two bundle fields, not none.** `BlockAdequate.fwd` has a fourth premise,
`KernelFields lenv ivm nfs`, whose only producer in the tree is
`Witness.SourceTableAdequate.inds` through `Supported.indInfo_of_tabled` — the tabled names
alone — while `BlockAdequate.bwd`'s is `IndArity`, the conclusion. A registration made at
whatever `Lean.getConstInfo` returned has neither. And `pass_register_inductive_entry` needs
`lenv.find? ii.name = some (.inductInfo ii)` where the provenance disjunct gives only
`lenv.find? hd = some (.inductInfo ii)`; without it the member loop's `unreachable!`
(`Erasure.lean:346`) can leave the registry untouched while `Erasure.lean:392` conses the
block entry, which is `RegKeyed.inds` false at the new key. Both gaps are closed by class-**D**
fields of `BlockAdequate`, beside `selfMem` and of its kind — `selfName` (a declared inductive
is declared under its own name) and `fields` (a declared block's constructor records are the
kernel's own at their positions) — so the cost is `P`'s and nothing new reaches a rung's binder
list. `ErasureSpec` is never constructed anywhere, so no site had to discharge them.

### 2.7 W7 — `hbridge` discharged, `hargReach` reduced

**Waits for F-DEPLCTX**, through W5.

```lean
/-- `hbridge`'s shape exactly (`Capstone.lean:185`), at a run of the shipping
`Erasure.visitExpr` from the empty state: `visitExpr_regInv_all` at `regInv_cold_start`, then
`bridgeEnv_of_regContent` at the final accumulator. -/
theorem erasure_bridge_env (P : ∀ Us, ErasureSpec lenv env Us gw)
    (E : EraserAsks lenv env gw) (A : UpstreamAsks env)
    (htbl : SourceTableAdequate lenv tbl) (hsafe : TableSafe lenv tbl)
    (hblk : TableBlocks lenv env tbl) (hcb : CompilerBodies lenv env tbl.body?)
    (hcfg : ConfigPinned cfg) (hsup : Supported env tbl pe) :
    ∀ (sf : ErasureState) (wt : Void IO.RealWorld),
      Erasure.visitExpr pe {} { «config» := cfg } cctx ref wp = .ok (t, sf) wt →
      ∃ Γspec : GlobalDeclarations, SpecEnv env tbl.body? tbl.levels? sf Γspec ∧
        ∀ t₀ : LBTerm, Erases env [] [] pe t₀ → Lower Γspec t₀ t →
          ErasureBridge env tbl.body? tbl.levels? Γspec sf.gdecls t₀
```

`bridgeEnv_of_regContent`'s fifth antecedent, `ErasuresDeclared env [] Γspec [] pe`, is
discharged at the final accumulator: every erasure of the prepared term names constants the
run registered, which is `RegInvShape'.consts` at `SpecContent`'s own keys — F1's
counterexample is at a *member's* sub-run, not at the entry term. `hbridge` then leaves
`shipping_erase_correct_firstorder` and all eight rungs.

**`hargReach` at G8 is reduced, not discharged.** U9 proved the reduction
(`scratch/round7/u9_g8.lean`): `Lower Γspec t₀ g8Term` forces
`t₀ = .const (toKername ``benchArith)`, `ErasesEnv.defns` produces the declared erasure `b₀` of
the tabled body, and `ReachableFrom.through_body` closes it. The unit lands that:

```lean
theorem g8_hargReach (hbo : g8Table.body? ``benchArith = some b)
    (hbody : ∀ b₀, Erases env (g8Table.levels? ``benchArith) [] b b₀ →
      ReachableFrom Γspec b₀ natIid.mutualBlockName)
    (her : Erases env [] [] eG8 t₀)
    (herΓ : ErasesEnv env g8Table.body? g8Table.levels? Γspec t₀)
    (hlow : Lower Γspec t₀ g8Term) :
    ReachableFrom Γspec t₀ natIid.mutualBlockName
```

so `green_G8`'s binder becomes `hbody`: every erasure of `benchArith`'s tabled body reaches
`Nat`'s block. That is a source-side non-erasability fact of a kind with `Supported` and
`NoMaxLevels` — `Erases.box` is the only arm that can drop the reference, and what refutes it
at the positions that carry the block name is the rung's own `InformativeInd`/typing data. The
unit is **not** expected to close it; §3 records it.

*Files.* `Capstone.lean` (`erasure_bridge_env`, the capstone's binder list), `Green.lean` (the
eight rungs' binder lists, `green_G8`'s `hargReach` → `hbody`).

*Gate.* `grep -rn "hbridge" LeanToLambdaBox/` empty; `scripts/ledger.sh` — the 33-name cluster
of `shipping_erase_correct_firstorder` and `green_G1`…`green_G8` **must not grow**, and
relocating a binder into a proved term is exactly where it could: `bridgeEnv_of_regContent`
and `bridgeEnv_of_regInv` are at three names today, and `visitExpr_regInv_all` inherits
whatever T8's induction carries, which is `[propext, Classical.choice, Quot.sound]`. Any
growth is a finding, not a bookkeeping update. Also `lake exe green-check --all` 8/8, and
`test/ledger.expected` gains one row for `erasure_bridge_env`.

*Confidence.* Mechanical once W5 and W6 land; the composition is proved at HEAD in
`w8_sigs.lean` modulo its four antecedents. The `hargReach` half is a landed reduction plus a
named residue.

### 2.8 W8 — the three dead slots, decided per item

* **`hnb : NoBodylessRefs Γ t`** — **deleted** from `shipping_erase_correct_firstorder` and
  from the eight rungs. The proof never mentions it (`scratch/round7/z_dead.out`), its
  docstring's claim that it prevents a vacuous conclusion is not realised in the statement the
  proof builds, and the non-vacuity it describes belongs to `hev`. Deleting a binder nothing
  reads strengthens the theorem. The eight `g<i>_noBodylessRefs` terms stay, consumed by
  `Tools/Coverage.lean`'s per-rung census, which already recomputes such columns from
  `Green.g<i>Env`/`g<i>Term` — so `lake exe hygiene --dead` does not grow by eight. Probe:
  `example : NoBodylessRefs g7Env g7Term := g7_noBodylessRefs` (`w8_sigs.lean`).
* **`hblk : TableBlocks lenv env tbl`** — **kept, with W4's consumer**. `erasure_bridge_of_run`
  never destructs it (`z_dead.out`) and its only reader, `blockKeyed_install`, has no consumer
  of its own; W4 gives both one. If W4 does not land — i.e. if F-DEPLCTX stays unmerged
  through this wave — the bundle and its ten binders are deleted instead, together with
  `blockKeyed_install`, `run_rec_exit_nodup` and `run_rec_exit_reg`'s fifth conclusion. The
  decision is W4's outcome, and it is recorded either way.
* **`SourceTableAdequate.compilerLevels`** (`Witness/SourceTable.lean:246`) and its transport
  `compilerLevels?_eq` (`:283`) — **kept, with a reader**, stated now:

  ```lean
  theorem compilerLevels_transport (htbl : SourceTableAdequate lenv tbl)
      (hd : (n, d) ∈ tbl.decls) (hci : compilerInfo? lenv n = some ci) :
      ci.levelParams = tbl.levels? n
  ```

  which is the equation W4's `visitMutual_member_erases` spends to identify the column the run
  installed (`Erasure.lean:889`, `:912`) with the column `RegContent.defns` reads. The field
  is contentless at G1–G5 and has one resp. four subjects at G6–G8 (`scratch/round7/z_c2d.out`),
  satisfied everywhere. This item does not wait for the merge.

*Gate.* `lake exe hygiene --dead` at its 321 budget or below; `z_dead.out`'s unused-binder
scan reports `#[]` for `shipping_erase_correct_firstorder` and `erasure_bridge_of_run`;
`lake exe green-check --all`.

*Landed*, with the gate corrected on two counts (rule 2). **`hnb` deleted**: the binder leaves
`shipping_erase_correct_firstorder`'s signature and all eight rungs' applications of it; the
docstring's vacuity claim is rewritten rather than carried (`Capstone.lean`). The eight
`g<i>_noBodylessRefs` stay — F-W8-9 is right that they had **no** consumer before this landing:
`Tools/Coverage.lean` did not already recompute a per-rung body-less column, so one is built —
`RungFacts.nbTerm`, read the same way `wfTerm` reads `g<i>_wf` (`env.find?` on
`g<i>_noBodylessRefs`), fed into a new `ladderSection` paragraph and `nbAll`. This item did not
wait on anything and needed no restatement. **`hblk` and `compilerLevels` were already
resolved, by W4**, landed after this section was written: `blockKeyed_install` has
`visitMutual_block_mode` as its consumer, and `compilerLevels?_eq` is spent inline at
`visitMutual_member_erases`/`_block` (`VisitExprRefines/Step/Env.lean:705`, `:735`) rather than
through a separately named `compilerLevels_transport` — same equation, no second declaration.
Both are simple presence checks this wave, confirmed unchanged.

**The printed gate is wrong on both figures, mechanised (`scratch/round7/w8_dead.lean`).**
`erasure_bridge_of_run`'s scan reports `#[hblk]`, not `#[]`, and by design: its own docstring
already says `hblk` "is the standing block binder, consumed at the install site rather than
here" (W4), and no argument list downstream of it mentions the fvar. The corrected gate reads
`#[]` for `shipping_erase_correct_firstorder` only — met — and `#[hblk]` for
`erasure_bridge_of_run`, unchanged and correct. `--dead` measures **339**, not the printed
321: W1–W3 grew it past that figure before this unit and no wave since corrected the written
budget (`doc/rework/07-STATUS.md`'s "321-declaration budget" is stale from `15a4af7`, the same
staleness class as `doc/coverage.md`'s uncommitted regeneration, `git log` stopping at
`4e5bd13`). This unit's own edits add nothing to the count: 339 before and after
(`scratch/round7/W8.hygiene_dead.out`). Fixing the written 321/339 gap and refreshing
`doc/coverage.md` and `doc/rework/07-STATUS.md` against the cumulative drift of W1–W7 is
outside this unit's three items and is not attempted here.

### 2.9 W9 — the inductive flag as MetaRocq's equation

**Waits for F-ARITYLET.** Once `Erasure.arityResultSort` walks `.letE` and `.mdata`,
`isPropositionalArity` decides `PropositionalInd` in both directions and the clause is
`erases_mutual_inductive_body`'s equation rather than its sound half:

```lean
def IndFlagSound (env : VEnv) (I : Name) (iid : InductiveId) (mib : MutualInductiveBody) :
    Prop :=
  ∀ oib, mib.bodies[iid.idx]? = some oib → (oib.propositional = true ↔ PropositionalInd env I)

theorem arity_of_propositionalInd (P : ErasureSpec lenv env Us gw)
    (hfind : lenv.find? I = some (.inductInfo iv))
    (hsafe : DefinitionSafety.safe ≤ (ConstantInfo.inductInfo iv).safety)
    (hprop : PropositionalInd env I) : Erasure.isPropositionalArity iv.type = true
```

`ErasureSpec.propositionalInd_of_arity` (`ErasureSpec.lean:554`) is the other direction,
already proved; the new one is `vResultSort_of_arityResultSort` (`:518`) run backwards, the
level transfer being the equation `ofLevel_alwaysZeroB`. `IndFlagSound.notPropositional`
(`ErasesEnv.lean:74`) keeps its statement and its consumers — the ι and projection arms read
`= false` off an informative inductive, and that half does not change.

The clause is vacuous at all eight rungs either way (no emitted inductive body carries
`propositional = true`, 0 of 1/2/2/3/2/1/12/12), so this unit buys **faithfulness, not a
rung**: it removes the standing note that the project states one direction of an equation
MetaRocq states in full, and it is the only place where a shipping defect is visible in a
*specification* rather than in a proof.

*Files.* `ErasesEnv.lean` (`:66`, `:74`), `ErasureSpec.lean` (`:554` and the new converse),
`Erasability.lean` (`propositional_false_of_informative`, `:425`, unchanged).

*Gate.* `lake build`; `test/Vacuity.lean` gains the rung measurement if it is re-taken;
`scripts/ledger.sh` unchanged.

*Confidence.* The statement elaborates (`w8_sigs.lean`) and the mathematics is the existing
induction reversed; the risk is that `vResultSort_of_arityResultSort`'s induction is not
symmetric at `.mdata`, where `TrExprS` is transparent and `arityResultSort` will be after the
merge. If the converse needs a further premise, the honest fallback is to keep the sound half
and record F-ARITYLET's residue at the clause, as `03-DEV-FIX.md` does today.

*Resolved at the merge — the fallback, not the biconditional.* The induction is symmetric at
both new arms, and `vResultSort_of_arityResultSort` takes them; what this unit assumed the
merge would remove, it does not. The walk and `destArity` now agree, so the residue is no
longer a `let`-carrying arity but zeta: `inductive FooBVar : (let u := Prop; u)` elaborates
with a `.bvar`-headed body, where `TrExprS.letE` substitutes the let value and the image is
`Sort 0`, while the walk — and PCUIC's `destArity` at `tRel` — answers `None`
(`arityResultSort_letBVar`, `ErasureSpec.lean`). Reducing past it would flag an alias-headed
arity and falsify `propositionalInd_of_arity`, the direction the consumers spend, so no
premise-free biconditional is available and none may be written as a guard. `IndFlagSound`
keeps its statement and its consumers; the residue is recorded at the clause, in
`03-DEV-FIX.md`'s F-ARITYLET row, and in `07-STATUS.md`'s vacuity census.

*Landed* (`scratch/round7/W9-report.md`): the refutation, as a theorem rather than as the
argument above. `arity_of_propositionalInd_false` (`ErasureSpec.lean`) is `§2.9`'s
`arity_of_propositionalInd` with `P`, `hfind` and `hsafe` replaced by their joint output —
`decl_adequate`'s `env.constants I = some vc` and `TrConstant .safe env (.inductInfo iv) vc`,
the bundle's only route from `iv.type` to `env` — and it is false, at `letBVarInduct`. Its two
halves are `arityResultSort_letBVar`, restated over the named subject `letBVarArity`, and
`trExprS_letBVarArity`, the semantic half, which was prose until now and holds at every
environment and every level scope. Sorry-free, `[propext, Classical.choice, Quot.sound]`.
The bundle itself cannot be refuted in the tree — nothing constructs an `ErasureSpec` — but no
field of it excludes the shape, and a field that did would be the guard rule (2) forbids.

## 3. What remains open after W8

W8 closes one class-**C** binder and rewires two dead slots. It does not make the capstone
unconditional; `doc/rework/07-STATUS.md` §4 is the standing census, and these rows survive:

* **C — this repository's own code.** `E : EraserAsks`, four fields, `kernel_ind_head_true`
  bounded by F-DEPTH's residue (a reduced telescope past `isArityCheck`'s constant budget, or
  any other kernel error inside it). `hbody`, W7's replacement for `hargReach` at G8: every
  erasure of `benchArith`'s tabled body reaches `Nat`'s block. If W4 takes the `fixBlock?`
  clause, one new class-**D** field identifying `Lean.Compiler.LCNF.getDeclInfo?`'s answer with
  `Witness.compilerInfo?`.
* **D — specifications of Lean's `Meta`/`Core` primitives.** `P : ∀ Us, ErasureSpec lenv env
  Us gw`, seven fields; `htbl`, `hsafe`, `hprep`, `hrun`, mechanised outside Lean by
  `lake exe reify` and the byte-diffed `.ast`.
* **U — upstream lean4lean.** `A : UpstreamAsks`, four fields (`doc/upstream-asks.md` items 2,
  6, 9, 10); `hcb : CompilerBodies` at G2–G8, blocked on `TrProj`, entirely unproven at the
  pin — 10 of G7's 30 tabled bodies carry an `Expr.proj`; item 4, which `hfo` and
  `ErasesEnv.tabled`'s discharge wait on. The sixteen inherited `sorryAx` roots
  (`test/lean4lean-sorries.expected`) and the 29-name executable-checker cluster
  `ErasureSpec.oracle_sound_of_run` brings with it.
* **R — scope.** `hsup : Supported`, the decidable fragment; `TableSafe.noMaxLevels`; the
  first-order forward-simulation shape of the observable; `hev`, constructed at G5 alone, so
  the source evaluation is assumed at the other seven rungs.
* **The α gap and the ∀-`Γspec` shape**, named in `08-REPAIRS-W5.md` §2.1: `ReifiedDecl.Prepared`
  pins a tabled body only up to `Expr.AlphaEq` and `lake exe reify --check` reports five of
  G7/G8's bodies matching only up to binder names. U4's `Erases.alpha` is what covers it, and
  W4 is the first unit to spend it — if the transport does not reach those five bodies, the
  gap reopens at the same place.
* **Coverage.** Sieve, BinaryTrees, Quicksort and Fannkuch stay outside the fragment at
  F-EQREC, F-SPARSE and `etaContractedMinor`; closing `hbridge` moves no coverage row.
* **F-PRODUCT**, `auto_inline_typeclass_dispatch` — the one shipping finding not meant to be
  fixed, off by default, class **E** in `doc/trust.md`.

Two of this wave's nine units are unblocked by a two-line shipping edit that three consecutive
wave reports have now put on `dev/fix` (`U5-report.md` §5, `U7-report.md` §5, `U9-report.md`
§6). Until F-DEPLCTX merges, W1, W2, W3 and W8's third item are the whole of what W8 can land,
and `hbridge` stays a binder.

W6 belongs in that list too, and not because of the merge: it reads the state alone (F-W8-8).
It landed at §2.6, so the two antecedents of `bridgeEnv_of_regContent` that W7 still owes are
`RegInvShape'` and `RegContent` at a run — the aggregation — and not `RegKeyed`.
