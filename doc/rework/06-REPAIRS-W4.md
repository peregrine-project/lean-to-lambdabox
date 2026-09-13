# 06 — W4b, the bridge repair round

W4 landed the eighteen motives, the aggregator and fourteen member steps; four steps have no
supplier and one of the four is refuted, so `LeanToLambdaBox/VisitExprRefines.lean`'s two T8
statements are implications whose antecedent no reader satisfies at a mutual block. This
document settles the repairs, with the evidence for each, and re-plans the wave as W4b.

Every signature below is the one W4b lands. Probe files, all elaborating at this toolchain
against the tree at the W4 checkpoint, are named per decision; they live outside the
repository and are cited by basename only.

## 0. The findings, and the decision each takes

| # | Finding (source) | Decision |
|---|---|---|
| F1 | `ErasesLBMode`'s block conjunct is unsatisfiable at a constant target, so `Motive4` is false and step 4 is refuted (`erasesLBMode_block_refuted`, U4.2 obstruction 1) | the conjunct is keyed by `BlockKeyed` — length, `Nodup`, and separation **at the tabled names** — and `BridgeInv.fixvars` names a `BlockKeyed` pair (§1) |
| F2 | The block conjunct quantifies over representations whose `ids` may hold a freshly opened binder, so `FixvarsAllReserved` is false as stated (U4.3 obstruction 4) | the same keying; `BridgeInv.fixvars_ids_subset` **proves** the premise (§1) |
| F3 | The inductive registry is in no invariant, so motives 3, 10, 17 are unprovable (U4.4 obstruction 1) | `BridgeInv.indcanon : IndRegistryModelled env s`, and `RunRefines` carries the invariant forward (§2) |
| F4 | Eight step premises are `ErasureSpec`-field-shaped facts about primitives (U4.2, U4.3, U4.4; `doc/trust.md`'s step-premise row) | `ErasureSpec` gains `prim_monotone` and `block_adequate` and `LookupAdequate`'s three clauses are strengthened; the four that are about **this repository's code** go to a second bundle, `EraserAsks`, class **C** (§3) |
| F5 | Six premises are model-side readings `decl_adequate` does not classify (same row) | all six are **proved** from `block_adequate` and the strengthened lookups, or from the repaired fragment (§3, §5) |
| F6 | `SpecEnv` does not imply that `Lower` commutes with abstraction; the `fixConst`/`fixBody` arms cannot be replayed (U4.3 obstruction 3) | `Lower.abstract` under `FVarFreeBodies Γ`, a new `SpecEnv` clause; `LowerAbstracts`/`SpecEnvAbstracts` retired (§4) |
| F7 | `SupportedTm.mdata` passes a spine through, so `NonConstHeadSupported` is not derivable (U4.3 obstruction 1) | the `mdata` rule is restricted to the empty spine; the premise becomes `Supported.head` (§5) |
| F8 | `SupportedTm.proj` misses the model arity and the field bound (U4.3 obstruction 2, U4.4 route 2) | the rule carries both; `ProjSupported` retired and `Supported.projInfo` supplies step 17's `hppi` (§5) |
| F9 | Step 17 is not written and needs six facts with no supplier (U4.4 obstruction 2) | each of the six is assigned a supplier in §5; the step is U4R.7 |
| F10 | `Motive4`'s premises do not exclude a constructor or type-former head, and `ConstOrigin` is not derivable from `KnownHead` (U4.2 obstruction 2) | `KnownHead` becomes the model's three-way classification; the constructor column is excluded by the run, the type-former column by `EraserAsks.oracle_informative`, which is **proved** from the two oracle clauses (§3, §5) |
| F11 | λ-headedness is not a run invariant: a block member erased to `.box` breaks `LowerBlock.hfl` (U4.3b obstruction 2) | N22 moves to the **input** side, in two halves — the tabled bodies of an installed block are λ-headed, and no member is erasable (`TableBlocks`, §6) |
| F12 | `ConfigPinned` in `LeanToLambdaBox/Capstone.lean` makes the bridge unreachable from the capstone (G4 obstruction 5) | it moves to `LeanToLambdaBox/ErasureSpec.lean`; `LeanToLambdaBox/Bridge.lean` imports `SpecEnv` and `ColdStartRun` instead (§7) |
| F13 | T8's closed footprint is 33 axioms, 29 of them predicted by no ledger row (G4 obstruction 2) | the cluster is measured **now**, at `ErasureSpec.oracle_sound_of_run`, by a ledger row that measures axiom names and by a `doc/trust.md` class-D row (§8) |
| F14 | 282 declarations of the bridge and cold-start modules are outside the `Green.lean` ∪ `Capstone.lean` closure (G4 obstruction 4) | the closure consumes them once §7 lands; measured prediction 454 → 172 (§9) |
| F15 | Seven declarations are homed in a step file for want of an owner, and `prepare_sound` has no home (U4.3b obstruction 4, U4.5 obstruction 1) | homes assigned in §10 |
| F16 | The capstone's `erases` conjunct is at the source term while T8 is about the **prepared** term, and no relation carries one to the other (this round) | the syntactic conjunct moves to `pe`, the observable conjunct stays at `e`, `prepare_sound` transports the evaluation **through the spine**, and each rung gains one premise fixing `pe` (§3, §11) |

§14 records the refutation round this document went through after W4b was first written: seven
findings, the decision each took, and the measurements. Every section above it reads as current
fact.

## 1. The fixvar mode, keyed

`fixvarMap nms ids = Std.HashMap.ofList (nms.zip ids)` loses information twice: `List.zip`
truncates, and a repeated name is overwritten. Reading the block conjunct at *every* pair whose
zip rebuilds the reader's map is therefore not "the block", and two W4 units hit it from
opposite sides — the appended pair refutes step 4, the duplicated pair admits an `ids` holding a
freshly opened binder.

```lean
/-- The conditions under which a pair of index lists faithfully describes the map the reader
carries, read at the table the run is checked against: `Erasure.visitMutual` installs one pair,
and the zip admits many others. The fourth conjunct is a **separation** condition and it is
quantified over the *tabled* names, which is where the premise is consumed — the miss branch of
`Erasure.visitConst`, at the constant it is visiting, which `Motive4` supplies as
`tbl.decl? n = some d`. Over all names it is false: `toKername` collapses `.num k` onto
`.str k.repr` and has escape fixed points, so a colliding name can always be invented
(`toKername_not_injective`). -/
def BlockKeyed (tbl : SourceTable) (ctx : ErasureContext) (nms : List Name)
    (ids : List FVarId) : Prop :=
  ctx.fixvars = some (fixvarMap nms ids) ∧ nms.length = ids.length ∧ nms.Nodup ∧
    ∀ m : Name, (tbl.decl? m).isSome → toKername m ∈ nms.map toKername → m ∈ nms

def ErasesLBMode (tbl : SourceTable) (ctx : ErasureContext) (env : VEnv) (Us : List Name)
    (Γspec : GlobalDeclarations) (Δ : VLCtx) (e : Expr) (t : LBTerm) : Prop :=
  (ctx.fixvars = none → ErasesLB env Us Γspec Δ e t) ∧
  (∀ nms ids, BlockKeyed tbl ctx nms ids →
    ErasesLBFix env Us Γspec (nms.map toKername) ids Δ e t)

def ErasesLBAltMode (tbl : SourceTable) (ctx : ErasureContext) (env : VEnv) (Us : List Name)
    (Γspec : GlobalDeclarations) (Δ : VLCtx) (nf : Nat) (m : Expr)
    (alt : List BinderName × LBTerm) : Prop :=
  (ctx.fixvars = none → ErasesLBAlt env Us Γspec Δ nf m alt) ∧
  (∀ nms ids, BlockKeyed tbl ctx nms ids →
    ErasesLBFixAlt env Us Γspec (nms.map toKername) ids Δ nf m alt)
```

The `tbl` index is new and it is the price of the restriction: the mode predicate is read in
`Motives.lean`, in the two T8 statements and in the congruences of
`LeanToLambdaBox/VisitExprRefines/Step/Mechanical.lean`, all of which already carry `tbl`, so
the change is a parameter added at each, not a new obligation.

`ErasesLBMode.block` takes `BlockKeyed tbl ctx nms ids` in place of the bare map equation, and so
do `ErasesLBMode.lam`, `.letE`, `.congr_fixvars` and `ErasesLBAltMode.mk` — the congruences carry
the four conditions transparently, which is why the repair costs the other thirteen steps
nothing.

Four conditions, not the two G4's repair order names. The third, `nms.Nodup`, is what F2 needs:
without it `fixvarMap [a, a] [x, y] = fixvarMap [a] [y]`, and the conjunct is read at an `ids`
containing an arbitrary `x`.

**The one consumption site.** `LeanToLambdaBox/VisitExprRefines/Step/Env.lean:609-615`, the miss
branch of step 4's content, is the only place the separation conjunct is spent, and it is spent
at one name:

```lean
      · intro nms ids hfx hlen hsep
        refine ErasesLBFix.of_erasesLB ⟨.const (toKername n), …⟩ (.miss ?_)
        intro hin
        …
        exact fixvarMap_get?_none hlen hopt (hsep n hin)
```

`hsep` is applied to `n`, the constant `Erasure.visitConst` is visiting; `hin` is
`toKername n ∈ nms.map toKername`, and the goal is the `ConstToFVar.miss` side condition. The
restricted conjunct serves it because `Motive4` carries `tbl.decl? n = some d` (§5): the
constructor and type-former columns of `KnownHead` are excluded before the branch is reached, so
the visited head is a *tabled* name. `grep -rn "hsep" LeanToLambdaBox/` finds no second site.

**Its supply chain, both halves input-side.** At the install site `nms` is
`(getDeclInfo? n).all.map remove_unsafe_rec` and the conjunct follows from two facts about the
table, neither of them a scope restriction on Lean names:

* `Supported.kernames` — the tabled names have pairwise-distinct λ□ keys. **Decidable**: a new
  arm `kernameSepB tbl` of `supportedB`, reporting `SupportError.kernameCollision`, so a rung
  discharges it with the `by rfl` it already runs (§5).
* `TableBlocks.members` — every member of a block the run installs is itself tabled (§6). Class
  **D**, beside `htbl` and `hsafe`, and mechanised by `lake exe reify` for the same reason
  `TableSafe` is: the block is a `lenv` read the table does not carry.

Then a tabled `m` whose key matches a member's key is that member, and the conjunct holds.

**Evidence.**

* `amend4/p1_keying.lean` (all `[propext, Classical.choice, Quot.sound]`):
  `fixvarMap_get?_of_nodup` — a `BlockKeyed` pair reads back each of its own pairs;
  `fixvarMap_ids_subset` — hence every `BlockKeyed` representation's identifiers are the
  installed pair's; `bridgeInv_ids_reserved` — **`FixvarsAllReserved`, proved** from
  `BridgeInv.fixvars`, landing as `BridgeInv.fixvars_ids_subset`; `blockKeyed_append_absurd` —
  the pair `erasesLBMode_block_refuted` runs on is not `BlockKeyed`, so the refutation no longer
  reaches the conjunct; `step4_content` — `visitConst_refines`'s conclusion **is** the keyed
  conjunct.
* The unrestricted form, measured (`refute4/r1_kername.lean`, re-run at this checkpoint):
  `blocks scanned = 104827; kername-separation FAILS on 37374; Nodup FAILS on 0`, and
  `refute4/r1b.lean` reports 142 of 199 true mutual blocks. Both counts are of *invented*
  colliders: the probe synthesises a name with the same key and never asks whether the
  environment declares it.
* The restricted form, measured (`amend4/m_env.lean`, `m_rungs.lean`, `m_{arith,sieve,quicksort,binarytrees,fannkuch}.lean`):
  over the whole elaboration environment, **227,840 constants and 227,840 distinct keys — zero
  collision classes**; over the eleven committed tables (six rungs, five corpus programs),
  `toKername` is injective on the declaration names, on the inductive names and on their union,
  in all 33 checks, with 0 witnesses; and **0 of the 223 true mutual blocks in the environment
  has a member tabled by any of the eleven programs**. Every block those tables install a fixvar
  map for is a singleton (55 of them, §6), and no block has an untabled member.

So the fourth conjunct is a **decidable input condition that no measured program violates**, not
a scope restriction the design cannot see. `doc/trust.md` gains no class-E F-KERNAME row;
`doc/coverage.md` gains a restriction row beside N19/N21, decided by the checker and reported as
`SupportError.kernameCollision`. The *shipping* half of the finding is unchanged and is filed as
what it is: `toKername` is not injective, so two Lean constants can share one λ□ key and the
second shadows the first in the emitted environment — U4R.3 files it in
`doc/rework/03-DEV-FIX.md` as **F-KERNAME**, with the environment measurement above as its
measure and no fix on `dev/verify`.

`erasesLBMode_block_refuted` is not deleted: restated at the unkeyed conjunct it is the reason
the four conditions are there, and `toKername_not_injective` beside it is the reason the fourth
is not a formality. Both stay in `LeanToLambdaBox/VisitExprRefines/Step/Env.lean` with that role
in their docstrings.

`BridgeInv.fixvars` names a `BlockKeyed` pair:

```lean
  fixvars : ctx.fixvars = none ∨
    ∃ nms ids, BlockKeyed tbl ctx nms ids ∧ ids.Nodup ∧ ∀ x ∈ ids, gen.Reserves x ∧ x ∉ Δ.fvars
```

so `BridgeInv` gains the `tbl` index too. Its two new conjuncts are established where the reader
is built, not here: `nms.Nodup` follows from `EraserAsks.block_keys_distinct` (§3) at `Erasure.visitMutual`'s
`names.map remove_unsafe_rec`, by `List.Nodup.of_map` on `toKername`, and the separation is the two input-side facts above.

## 2. The inductive registry in `BridgeInv`

`Erasure.visitConstructor`, `visitProj` and `visitCases` read the emitted node's `InductiveId`
and the field masks out of `ErasureState.inductives`, and at a registry hit
(`Erasure.run_register_inductive_hit_ok`) the run reports whatever the state holds. `SpecEnv`
does not constrain that: `SpecEnv.inds` reads the registry's **domain** only
(`(s.inductives.get? n).isSome → IndCovered env Γspec n`), and `SpecContent.blocks` is about
`Γspec`'s entry at `iid.mutualBlockName` given an `IndInfo` — it says the specification
environment covers the block, never that the identifier the state holds is the model's. So the
identifier and the mask shape stay a `BridgeInv` field and the coverage stays `SpecEnv`'s.

```lean
structure BridgeInv (env : VEnv) (Us : List Name) (tbl : SourceTable) (cfg₀ : ErasureConfig)
    (gen : NameGenerator) (ctx : ErasureContext) (s : ErasureState) (Δ : VLCtx) : Prop where
  mlc : ∃ m : MLCtx, m.WF env Us ∧ m.lctx = ctx.lctx ∧ m.vlctx = Δ
  lparams : ctx.lparams <+: Us
  cfg : ctx.config = cfg₀
  kfresh : ∀ fv ∈ Δ.fvars, kernelNGen.Reserves fv
  reserved : ∀ fv ∈ Δ.fvars, gen.Reserves fv
  fixvars : ctx.fixvars = none ∨
    ∃ nms ids, BlockKeyed tbl ctx nms ids ∧ ids.Nodup ∧ ∀ x ∈ ids, gen.Reserves x ∧ x ∉ Δ.fvars
  canon : CanonicalConstants s
  /-- Every registry entry names the block identifier the model declares for that name, and
      its masks retain every field. -/
  indcanon : IndRegistryModelled env s
```

`IndRegistryModelled` (definition unchanged) moves from
`LeanToLambdaBox/VisitExprRefines/Step/Passes.lean` to `LeanToLambdaBox/Bridge.lean`, beside the
invariant that carries it.

The invariant is not preserved by `Erasure.RunConcl`: a sub-run may register an inductive, and
`RunConcl` bounds only growth. `RunConcl` cannot carry the clause either —
`LeanToLambdaBox/ErasureRun.lean` is model-free by construction and `IndRegistryModelled`
mentions `VEnv`. So the motives' shared conclusion carries it:

```lean
def RunRefines (env : VEnv) (Us : List Name) (tbl : SourceTable) (ctx : ErasureContext)
    (Δ : VLCtx) (s s' : ErasureState) (gen gen' : NameGenerator) (e : Expr) (t : LBTerm) : Prop :=
  RunConcl s s' ∧ IndRegistryModelled env s' ∧ gen ≤ gen' ∧
    ∀ Γspec, SpecEnv env tbl.body? s' Γspec → ErasesLBMode tbl ctx env Us Γspec Δ e t

theorem BridgeInv.mono_state (h : BridgeInv env Us tbl cfg gen ctx s Δ) (hrc : RunConcl s s')
    (hind : IndRegistryModelled env s') : BridgeInv env Us tbl cfg gen ctx s' Δ
```

`RunRefinesAlt` gains the same conjunct, and `Motive5`/`Motive6` — whose conclusions are the
registration facts rather than a `RunRefines` — gain `IndRegistryModelled env s'` beside
`RunConcl s s'`. With the field, `Motive3Reg`/`Motive10Reg` and `Step3Reg`/`Step10Reg` are
deleted: steps 3 and 10 conclude the induction's own interfaces.

`RegisterModels` is then **proved**, not assumed, as
`Erasure.run_register_inductive_models` in `LeanToLambdaBox/ErasureRun.lean`
(`ConfigPinned.remove_irrel_constr_args = false` sends the cold branch's mask to
`Array.replicate ci.numFields .keep`, and `ConfigPinned.extern = .preferLogical` kills its
`addAxiom` arm) together with `ErasureSpec.block_adequate` for the model half.

## 3. Two bundles: `ErasureSpec` for the primitives, `EraserAsks` for this repository's code

W4 put eight step premises into `ErasureSpec` and said of all of them that they are "about a
primitive of the Lean API". Four are not. `oracle_informative` is about `Erasure.isErasable`
(`Erasure.lean:177`), a repository composite of `LeanToLambdaBox.isErasable` (`Relevance.lean:52`)
and `Erasure.isErasableMeta` (`Erasure.lean:151`); `transforms_sound` and
`prim_monotone.transform` quantify over `preparePasses`, one of whose three functions is
`Erasure.replaceUnsafeRecNames` (`Erasure.lean:538`), and the first of the two is a specification
of the eraser's own preprocessing; `LookupAdequate.declInfo`'s `Nodup` clause reads
`Erasure.remove_unsafe_rec` (`Erasure.lean:520`) off the primitive's answer. Calling an assumption
about the code under verification a fact about a Lean primitive is the one mistake this document
cannot make, so the four move to a bundle of their own.

**`ErasureSpec` — class D, primitives only.** Every clause is about `Lean.Environment`,
`Lean.getCasesInfo?`, `Lean.Compiler.LCNF.getCtorArity?`, `Lean.Compiler.LCNF.getDeclInfo?`,
`Lean.getEnv`, `Lean.logInfo`, `Lean.Meta.isInstance`, `Lean.Meta.inferType`, or the model's
connection to the elaboration environment. Three clauses of `LookupAdequate` are strengthened:

```lean
  /-- `getDeclInfo?` answers for a name `lenv` knows, at the compiler block that name belongs
      to. The membership is **guarded**: `getDeclInfo?` prefers the `_unsafe_rec` twin
      (`LCNF/ToDecl.lean:100-102`), so at `n = f._unsafe_rec` the answer's block is `f`'s and
      does not contain `n` — measured false for 3,376 names of this environment. The guard is
      discharged at the call site, where the visited name comes out of a term
      `Erasure.replaceUnsafeRecNames` has already stripped. -/
  declInfo : ∀ (n : Name) (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State)
    (w : Void IO.RealWorld) (r : Option ConstantInfo) (w₁ : Void IO.RealWorld),
    Lean.Compiler.LCNF.getDeclInfo? n cctx ref w = .ok r w₁ →
    gw w ≤ gw w₁ ∧ ∀ ci, r = some ci → lenv.find? n ≠ none ∧
      (Lean.Compiler.isUnsafeRecName? n = none → n ∈ ci.all.map Erasure.remove_unsafe_rec)
  /-- `getCtorArity?` answers exactly for the constructors `lenv` declares, at their
      parameter-plus-field arity, and for no other name. -/
  ctorArity : ∀ (n : Name) … (r : Option Nat) …,
    Lean.Compiler.LCNF.getCtorArity? n cctx ref w = .ok r w₁ →
    gw w ≤ gw w₁ ∧
    (∀ a, r = some a → ∃ cv : ConstructorVal, lenv.find? n = some (.ctorInfo cv) ∧
      a = cv.numParams + cv.numFields) ∧
    (r = none → ∀ cv : ConstructorVal, lenv.find? n ≠ some (.ctorInfo cv))
  /-- `getCasesInfo?` answers exactly for the `casesOn` constants, at metadata that agrees
      with the block `lenv` declares. -/
  casesInfo : ∀ (n : Name) … (r : Option Lean.CasesInfo) …,
    Lean.getCasesInfo? n cctx ref w = .ok r w₁ →
    gw w ≤ gw w₁ ∧
    (∀ ci, r = some ci → isCasesOnName n = true ∧ ci.declName = n ∧
      ∀ iv : InductiveVal, lenv.find? n.getPrefix = some (.inductInfo iv) →
        CasesInfoAgreesK lenv ci iv) ∧
    (r = none → isCasesOnName n = false)
```

The `Nodup` half of W4's `declInfo` is **gone from here**: it is false about `getDeclInfo?`, and
the honest version is `EraserAsks.block_keys_distinct` below.

`ErasureSpec` is stated at `(lenv, env, Us, gw)` and holds no `SourceTable`, so the table-side
reading of the metadata is not a field: `CasesInfoAgreesK` is the kernel-side twin, and
`CasesInfoAgrees` (the table-side structure of
`LeanToLambdaBox/VisitExprRefines/Motives.lean`) follows from it through
`Witness.ReifiedInduct.Pinned`, by `CasesInfoAgrees.of_pinned` in
`LeanToLambdaBox/Supported.lean`.

```lean
/-- The kernel-side field-count list of a declared inductive: one entry per constructor, read
off its `ConstructorVal`, which is where the block's arithmetic lives. -/
def KernelFields (lenv : Environment) (iv : InductiveVal) (nfs : List Nat) : Prop :=
  nfs.length = iv.ctors.length ∧
    ∀ (j : Nat) (cn : Name), iv.ctors[j]? = some cn →
      ∃ cv : ConstructorVal, lenv.find? cn = some (.ctorInfo cv) ∧ nfs[j]? = some cv.numFields ∧
        cv.induct = iv.name ∧ cv.cidx = j ∧ cv.numParams = iv.numParams

/-- The elaborator's `Lean.CasesInfo` against the block `lenv` declares. -/
structure CasesInfoAgreesK (lenv : Environment) (ci : Lean.CasesInfo)
    (iv : InductiveVal) : Prop where
  discrPos : ci.discrPos = iv.numParams + 1 + iv.numIndices
  arity : ci.arity = iv.numParams + 1 + iv.numIndices + 1 + iv.ctors.length
  altsRange : ci.altsRange.lower = ci.discrPos + 1 ∧ ci.altsRange.upper = ci.arity
  numAlts : ci.altNumParams.size = iv.ctors.length
  numFields : ∀ (j : Nat) (a : Lean.CasesAltInfo) (cn : Name) (cv : ConstructorVal),
    ci.altNumParams[j]? = some a → iv.ctors[j]? = some cn →
    lenv.find? cn = some (.ctorInfo cv) → altNumFields a = cv.numFields

/-- The `CoreM`/`MetaM` calls the erasure makes for their effect alone. -/
structure PrimMonotone (gw : Void IO.RealWorld → NameGenerator) : Prop where
  getEnv : ∀ (s : ErasureState) (ctx : ErasureContext) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) (le : Environment)
    (s₁ : ErasureState) (w₁ : Void IO.RealWorld),
    (getEnv : EraseM Environment) s ctx cctx ref w = .ok (le, s₁) w₁ → gw w ≤ gw w₁
  logInfo : ∀ (m : MessageData) …, (logInfo m : EraseM Unit) … = .ok (u, s₁) w₁ → gw w ≤ gw w₁
  isInstance : ∀ (nm : Name) …,
    (liftM (Lean.Meta.isInstance nm) : EraseM Bool) … = .ok (b, s₁) w₁ → gw w ≤ gw w₁
  /-- `Lean.Meta.inferType`: the generator bound, and the agreement between the inferred
      Π-telescope and the subject's λ-telescope `Erasure.lambdaOrIntroToArity` peels. -/
  inferType : ∀ (e : Expr) …,
    Erasure.liftMetaM (Lean.Meta.inferType e) s ctx cctx ref w = .ok (ty, s₁) w₁ →
    gw w ≤ gw w₁ ∧ ForallMatchesLam ty e

/-- The kernel's inductive blocks and the model's agree: `decl_adequate`'s block-level
sibling, at the identifier `Erasure.register_inductive` mints. -/
structure BlockAdequate (lenv : Environment) (env : VEnv) : Prop where
  fwd : ∀ (n m : Name) (iv ivm : InductiveVal) (i : Nat) (nfs : List Nat),
    lenv.find? n = some (.inductInfo iv) → iv.all[i]? = some m →
    lenv.find? m = some (.inductInfo ivm) → KernelFields lenv ivm nfs →
    IndInfo env m ⟨indBlockKername iv.all, i⟩ iv.numParams nfs
  bwd : ∀ (I : Name) (np : Nat) (nfs : List Nat), IndArity env I np nfs →
    ∃ iv : InductiveVal, lenv.find? I = some (.inductInfo iv) ∧ iv.name = I ∧
      iv.numParams = np ∧ KernelFields lenv iv nfs
  ctor : ∀ (c : Name) (cv : ConstructorVal), lenv.find? c = some (.ctorInfo cv) →
    CtorOf env c cv.induct cv.cidx
  ctorBwd : ∀ (c I : Name) (k : Nat), CtorOf env c I k →
    ∃ cv : ConstructorVal, lenv.find? c = some (.ctorInfo cv) ∧ cv.induct = I ∧ cv.cidx = k
  /-- The `casesOn` constant of a declared inductive is declared in the model, at the
      segmentation the block fixes. -/
  casesOn : ∀ (c I : Name) (iv : InductiveVal), isCasesOnName c = true → c.getPrefix = I →
    lenv.find? I = some (.inductInfo iv) →
    ∃ dp nm ci, env.constants c = some ci ∧ ConstOrigin env c ∧ CasesOnShape env c I dp nm
```

and two new `ErasureSpec` fields:

```lean
  /-- The `CoreM`/`MetaM` calls the erasure makes for their effect alone. Class **D**. -/
  prim_monotone : PrimMonotone gw
  /-- The kernel's blocks, constructors and eliminators, in the model. Class **D**. -/
  block_adequate : BlockAdequate lenv env
```

**`EraserAsks` — class C, this repository's own preprocessing and oracle.** One home, beside
`ErasureSpec` in `LeanToLambdaBox/ErasureSpec.lean`; one new standing binder `E`, visible in
every statement that reads it, and one `doc/trust.md` row per field naming an owner, a wave and
what would retire it. Class **C** and not **D** because these are not facts mechanised outside
Lean about an opaque primitive: they are properties of code in this repository, and the honest
end state for each is a proof, not a permanent binder.

```lean
/-- What the correctness statement assumes about the eraser's **own** preprocessing and
relevance oracle. Not primitives: `Erasure.replaceUnsafeRecNames`, `Erasure.prepare_erasure`,
`Erasure.isErasable` and `Erasure.remove_unsafe_rec` are all defined in this repository, and
each field below is therefore an obligation with an owner rather than a specification of an
input. The symmetric bundle for lean4lean is `UpstreamAsks`. -/
structure EraserAsks (lenv : Environment) (env : VEnv) (Us : List Name)
    (gw : Void IO.RealWorld → NameGenerator) : Prop where
  /-- The four `prepare_erasure` calls only advance the generator. Owner: this repository;
      retired by unfolding `Lean.Core.transform`'s generator discipline at the three passes. -/
  passes_monotone : ∀ (f : Expr → CoreM Expr), f ∈ preparePasses → ∀ (e : Expr) …,
    (liftM (f e) : EraseM Expr) s ctx cctx ref w = .ok (e', s₁) w₁ → gw w ≤ gw w₁
  /-- Each pass preserves the source evaluation of the subject **under an arbitrary application
      spine** (§11: the spine is why this is not the pass's own statement). Owner: this
      repository; the δ-expansion half is about `Lean.Compiler.LCNF.macroInline`, the
      `_unsafe_rec` half about `Erasure.replaceUnsafeRecNames`. -/
  passes_sound : ∀ (f : Expr → CoreM Expr), f ∈ preparePasses → ∀ (e e' : Expr) …,
    (liftM (f e) : EraseM Expr) s ctx cctx ref w = .ok (e', s₁) w₁ →
    ∀ (args : List Expr) bo Us' fl Δ v,
      SEval env bo Us' fl Δ (mkApps e args) v → SEval env bo Us' fl Δ (mkApps e' args) v
  /-- A `false` verdict means the **pure kernel run** did not answer `true`. Near-definitional:
      `Erasure.isErasable`'s `| .ok b => return b` arm, modulo the `getEnv`/`getLCtx` reads. -/
  oracle_false_refl : ∀ (e : Expr) … (s₁ : ErasureState) (w₁ : Void IO.RealWorld),
    Erasure.liftMetaM (Erasure.isErasable ctx.lparams e) s ctx cctx ref w = .ok (false, s₁) w₁ →
    ctx.lparams = Us →
    M.run lenv.toKernelEnv .safe ctx.lctx ctx.lparams {}
      (RecM.run (LeanToLambdaBox.isErasable e)) ≠ .ok true
  /-- At an inductive-type head the pure kernel run answers `true`. The oracle's completeness,
      at the one shape the fragment cannot exclude, reduced to the kernel arm. -/
  kernel_ind_head_true : ∀ (lctx : LocalContext) (m : MLCtx) (e : Expr) (c : Name)
      (us : List Level) (ve : VExpr) (iid : InductiveId) (np : Nat) (nfs : List Nat),
    m.WF env Us → m.lctx = lctx → (∀ fv ∈ m.vlctx.fvars, kernelNGen.Reserves fv) →
    e.getAppFn = .const c us → IndInfo env c iid np nfs → TrExprS env Us m.vlctx e ve →
    M.run lenv.toKernelEnv .safe lctx Us {} (RecM.run (LeanToLambdaBox.isErasable e)) = .ok true
  /-- The λ□ keys of a block's members are distinct. `Erasure.visitMutual` builds
      `fixvarMap (ci.all.map remove_unsafe_rec) ids` and `mkDef` reads it back by name, so a
      collapse here is a miscompilation, not a proof gap. -/
  block_keys_distinct : ∀ (n : Name) … (ci : ConstantInfo) (w₁ : Void IO.RealWorld),
    Lean.Compiler.LCNF.getDeclInfo? n cctx ref w = .ok (some ci) w₁ →
    ((ci.all.map Erasure.remove_unsafe_rec).map toKername).Nodup
```

**What is proved from them, rather than assumed.** W4's `oracle_informative` is not a field: it
is a theorem of the two oracle clauses.

```lean
/-- **The type-former exclusion, derived.** `Motive4`/`Motive11`/`Motive12`'s premise. -/
theorem EraserAsks.oracle_informative (E : EraserAsks lenv env Us gw) …
    (hor : Erasure.liftMetaM (Erasure.isErasable ctx.lparams e) s ctx cctx ref w
      = .ok (false, s₁) w₁) (hlp : ctx.lparams = Us) (hinv : BridgeInv env Us tbl cfg (gw w) ctx s Δ)
    (htr : TrExprS env Us Δ e ve) :
    ∀ c us, e.getAppFn = .const c us → ∀ iid np nfs, ¬ IndInfo env c iid np nfs
```

`amend4/q1_route.lean` proves exactly this composition, `[propext, Classical.choice, Quot.sound]`;
`BridgeInv.mlc` supplies the `MLCtx` the second clause asks for, and the freshness conjunct is
`BridgeInv.kfresh`. The model side is a **theorem of the tree**, three lines from lemmas that
already exist (`amend4/q1_indspine.lean`):

```lean
theorem erasable_indSpine (henv : env.WF) (hΔ : VLCtx.WF env Us.length Δ)
    (hi : IndInfo env c iid np nfs) (htr : TrExprS env Us Δ (mkApps (.const c us) args) ve) :
    Erasable env Us.length Δ.toCtx ve
```

— `trExprS_spine_head`, `erasable_mkApps` and `Erases.indInfo_erasable`, no `UpstreamAsks`.

**Why the W4 clause could not stay as it was.** Stated about `Erasure.isErasable`, it is **false**
about the Lean API (`amend4/q1_refute.lean`): with `def DeepArity : Type 1 := Nat → Nat → Nat →
Nat → Type` marked `@[irreducible]` and `inductive Bar : DeepArity`, the kernel arm throws
(`Expr.Data.approxDepth` is **8 bits**, so `isArityCheck`'s fuel is `approxDepth + 1 ≤ 256`, and
here it is 1 against a five-step telescope) and `isErasableMeta` answers `false` because `Meta.whnf`
will not unfold an `@[irreducible]` alias. The oracle returns `false` at an inductive head. That
environment has no model — lean4lean's `TrIndType.numIndices` and `VInductDecl.WF.universes` force
a modelled inductive's type to be a syntactic arity — so the clause is *true but unproved* inside
`ErasureSpec`; but the symmetric field a reader would expect, "false ⇒ not erasable", is **false
even in a modelled environment** (`amend4/q1_counterexample.lean`, a definition at an irreducible
arity alias), so it is not offered. Measured on the other side: over the **2,940** inductive type
formers reachable from `LeanToLambdaBox.Erasure`, the pure kernel run answers `.ok true` for every
one — 0 throws, 0 `false` (`amend4/q1_measure.lean`).

`kernel_ind_head_true` therefore has a named obstacle and a named refutation: it is refuted at an
arity of ≥ 256 binders by the 8-bit cap, and discharging it needs three executable-shape lemmas
lean4lean does not have — `inferType` on a `.const`-headed spine returns the instantiated declared
telescope, `whnf` is the identity on a syntactic `.forallE`, and the fuel covers the telescope.
The cap is a **new finding, raised not fixed**: U4R.1 files **F-DEPTH** in
`doc/rework/03-DEV-FIX.md` with the measurement above. `Relevance.lean` is verification-authored,
so changing the fuel to the reduced telescope's own bound is in scope for a later wave under plan
rule N5's scheduled exception; W4b does not take it.

**Why the `Nodup` clause is a repository-side condition and not a Lean fact.**
`Erasure.remove_unsafe_rec` strips one literal `"_unsafe_rec"` component, so it is not injective,
and the clause fails exactly when a block holds both `n` and `n._unsafe_rec`. That block is
**legal Lean** (`amend4/m12_unsafe_mutual.lean`, elaborates with no error):

```lean
mutual
  unsafe def u : Nat → Nat             | 0 => 0 | n+1 => u._unsafe_rec n
  unsafe def u._unsafe_rec : Nat → Nat | 0 => 1 | n+1 => u n
end
-- getDeclInfo? u → all = [u, u._unsafe_rec], mapped = [u, u], fixvarMap size 1
```

and the eraser **silently miscompiles** it (`amend4/m13_erase_collide.lean` against the control
`m14`): two `ConstantDecl`s under one kername, two identically named `FixDef`s, and both members'
recursive calls bound to the same fix variable — `u 3` evaluates to a self-loop instead of `1`.
U4R.1 files that as **F-UNSAFEREC**, with the one-line guard it proposes and does not apply
(`unless (fixvarnames.map toKername).Nodup do throw …` after `Erasure.lean:906`), which would
turn `block_keys_distinct` into a run-recovered fact and retire the field. Measured meanwhile:
of **228,937** `getDeclInfo?` answers in this environment (219,838 of them carrying a non-empty
`all`), **0** have a non-`Nodup` mapped block and **0** contain both a name and its
`_unsafe_rec` twin; of the 1,495 true mutual blocks it sees — all `ConstantInfo` kinds, where §1's 223 counts `defnInfo` heads in the rung environment — 0 fail. W4's "0 failures over 104,827
blocks" counted `defnInfo` heads only — the corrected scale is above. A measurement over one
environment is not a proof, and the clause is stated at the **kername** level because that is
what `LowerBlock.hnd` and `RegInvShape'.keys` consume and because `toKername` is itself
non-injective (§1).

**What this retires.** Of the seventeen step premises:

| Premise | Fate |
|---|---|
| `CoreCallsMonotone`, `GetEnvMonotone` | `ErasureSpec.prim_monotone.getEnv`/`.logInfo`/`.isInstance` |
| `InferTypeMonotone`, `InferLamAdequate` | `ErasureSpec.prim_monotone.inferType` (one clause, both readings) |
| `PrepareRunConcl` | state half **proved** from `run_prepare_erasure_ok` under `ConfigPinned`; generator half is `EraserAsks.passes_monotone` |
| `DeclBlockMember` | `LookupAdequate.declInfo`, at its guard |
| `CasesInfoAdequate` | `LookupAdequate.casesInfo` + `CasesInfoAgrees.of_pinned` |
| `CtorArityAdequate` | `LookupAdequate.ctorArity` + `block_adequate.ctor` + `Witness.ReifiedInduct.Pinned` |
| `CtorAdequate`, `CtorDeclModelled`, `IndDeclModelled` | **proved** from `block_adequate` |
| `RegisterModels` | **proved** (§2) |
| `NonConstHeadSupported`, `ProjSupported` | **proved** (§5) |
| `FixvarsAllReserved` | **proved** (§1) |
| `SpecEnvAbstracts` | **proved** (§4) |
| `VisitExprRunConcl` | **proved** from `visitExpr_shape_all` once `LeanToLambdaBox/Bridge.lean` imports `LeanToLambdaBox.ColdStartRun` (§7) |

No step of W4b carries a named `Prop` premise beyond `ErasureSpec`, `EraserAsks`,
`SourceTableAdequate`, `TableBlocks`, `TableSafe`, `ConfigPinned`, `CompilerBodies` and
`UpstreamAsks`, which are the wave's standing binders — three more than W4 named, and the three
are the price of not calling an assumption about this repository's code a fact about Lean. That
is the acceptance test G4R runs by `grep`.

## 4. `Lower` commutes with abstraction

`Erasure.mkLambda`, `mkLetIn` and `mkAlt` close with `abstract x = toBvar x 0`, and
`Erases.uninstantiate` closes the erasure image with the same operator, so the binder steps need
the pass factor to follow. `Lower` is a congruence at twelve of its fourteen arms; at `fixConst`
and `fixBody` the target is built from `Γ`'s own declared bodies and abstracting a variable that
occurs in one of them would demand a block the declaration does not declare.

The side condition is free-variable-freedom of the declared bodies, and — this is what makes the
lemma unconditional in `x` — `closeFix` removes the block's own identifiers, so a `.fix` node the
pass builds has no free variable at all:

```lean
/-- The clause a specification environment must satisfy for the pass to commute with
abstraction: its declared bodies mention no free variable. -/
def FVarFreeBodies (Γ : GlobalDeclarations) : Prop :=
  ∀ (kn : Kername) (b : LBTerm) (x : FVarId), DefnDecl Γ kn b → ¬ hasFVar x b

theorem Lower.noFVar {Γ : GlobalDeclarations} (hfv : FVarFreeBodies Γ) {x : FVarId}
    {s t : LBTerm} (h : Lower Γ s t) : ¬ hasFVar x s → ¬ hasFVar x t

theorem Lower.abstract {Γ : GlobalDeclarations} (hfv : FVarFreeBodies Γ) {s t : LBTerm}
    (h : Lower Γ s t) (x : FVarId) : ∀ lvl, Lower Γ (toBvar x lvl s) (toBvar x lvl t)

theorem LowerAlt.abstract {Γ : GlobalDeclarations} (hfv : FVarFreeBodies Γ) {nf : Nat}
    {m : LBTerm} {alt : List BinderName × LBTerm} (h : LowerAlt Γ nf m alt) (x : FVarId) :
    ∀ lvl, LowerAlt Γ nf (toBvar x lvl m) (alt.1, toBvar x (lvl + alt.1.length) alt.2)
```

**Evidence: all three are proved**, not projected (`amend4/p6_lower_abstract.lean`, 423 lines,
`#print axioms` `[propext, Quot.sound]` on each — no `Classical.choice`, no `sorryAx`). What the
probe settles beyond elaboration:

* Every arm closes. `Lower.noFVar` is `Lower.rec` with `motive_2 := fun _nf m alt _ => ¬ hasFVar
  x m → ¬ hasFVar x alt.2`; the congruence arms are one-liners, `elimApp` goes through the tree's
  own `hasFVar_mkApps`, and **both fix arms** are `fixNode_not_hasFVar` fed by `hdecl` and the
  induction hypothesis.
* `Lower.abstract` is `Lower.shift_comm`'s induction with three differences: `bvar` is trivial
  (no cutoff split), `fvar y` splits on `y == x`, and the fix arms use `toBvar_fixNode` where
  `shift_comm` used `LBClosed.shift_eq`. **Neither fix arm uses its induction hypothesis** — both
  call `Lower.noFVar` on the block's own `hlow`, so `noFVar` is proved first and standalone.
* `LowerAlt.abstract` is that `motive_2`, obtained by `induction nf generalizing m alt` +
  `cases h` rather than by re-running the fourteen arms.
* **No level side condition.** `Lower.shift_comm` needs `c ≤ lvl` and `hΓ : ClosedBodies Γ`;
  `Lower.abstract` needs neither, because `toBvar` never reads or rewrites an existing de Bruijn
  index.
* **The hypothesis is necessary, machine-checked** (`amend4/p7_necessity.lean`):
  `noFVar_needs_fvarFree` and `abstract_needs_fvarFree` refute both statements with
  `ClosedBodies Γ` *granted*, on a one-member block `kn ↦ λx. .fvar y`. `LBClosed`'s fvar clause
  is `| .fvar _, _ => True`, so `ClosedBodies` — and therefore `LBWfSpec` — says nothing about
  free variables. Both refutations land beside `LowerFixFixture`, which is where the tree keeps
  the reason a premise is not a formality.

The pieces the tree does not have and the arm that refuted the W4 premise are `amend4/p2_abstract.lean`'s,
now reused verbatim inside the probe: `hasFVar_toBvar_of` and its three list companions,
`closeFixFold_not_hasFVar`, `closeFix_not_hasFVar`, `constToFVar_not_hasFVar`,
`closeConstAt_not_hasFVar`, `fixNode_not_hasFVar`, `toBvar_fixNode` — **the arm that refuted
`LowerAbstracts`, discharged** — and `toBvar_mkApps`.

The side condition is supplied by one new clause on the predicate the motives hold, beside the
`ClosedBodies` clause the registration invariant already carries:

```lean
structure SpecEnv (env : VEnv) (bo : Name → Option Expr) (s : ErasureState)
    (Γspec : GlobalDeclarations) : Prop where
  spec : SpecContent env bo Γspec
  consts : ∀ n : Name, (s.constants.get? n).isSome →
    (LBTerm.envLookup Γspec (toKername n)).isSome
  inds : ∀ n : Name, (s.inductives.get? n).isSome → IndCovered env Γspec n
  /-- The specification bodies mention no free variable, which is what makes the pass commute
      with abstraction (`Lower.abstract`) — the clause the bridge's binder steps consume. -/
  fvarFree : FVarFreeBodies Γspec
```

`RegInvShape'` (`LeanToLambdaBox/ColdStartShape.lean`) gains the matching field `specFVarFree`,
threaded by its constructors exactly as `specClosed` is, and `RegInvShape'.specEnv` supplies the
new `SpecEnv` clause from it.

It is a clause and not a theorem because `SpecContent` has no coverage clause: its four content
clauses are conditional on an entry being present, and an entry at a kername that is neither a
tabled constant's, nor a body-less non-eliminator's, nor a covered block's or eliminator's may
hold anything. **But it is not an assumption without a payer.** Every entry a run registers is
an erasure image at the empty context, and the erasure relation emits an `.fvar` only through
`Erases.fvar`, guarded by `Δ.find? (.inr x) = some …`, whose only context extensions are
`.vlam`/`.vlet` conses — so at `Δ = []` the arm cannot fire. W4b therefore lands the discharge
beside the clause:

```lean
theorem Erases.noFVar {env : VEnv} {Us : List Name} {e : Expr} {t : LBTerm} {x : FVarId}
    (h : Erases env Us [] e t) : ¬ hasFVar x t
```

a twelve-arm induction (≈30 lines, unprobed) which turns `SpecContent.defns`' `Erases env Us []
b b₀` into `FVarFreeBodies` at every producer. What stays open is the same thing that was already
open: nothing in W4b **inhabits** `RegInvShape'` at a run's final state, so the new field is
carried, not discharged, exactly as `specClosed` is. The rung consequence is one line and it is
stated in `doc/trust.md`: `hbridge` gains no field, `SpecEnv` gains one clause, and the W5
supplier that inhabits `RegInvShape'` pays it with `Erases.noFVar`.

## 5. Steps 3, 10 and 17, and the fragment repairs they rest on

`LeanToLambdaBox/Supported.lean` takes two repairs, each visible in `supportedGo` and re-measured
on the corpus:

```lean
  /-- Metadata is transparent to the erasure, at a term read on its own: `Expr.getAppFn` does
      not see through `.mdata`, so a metadata-wrapped head is outside the fragment. -/
  | mdata {d : MData} {b : Expr} (h : SupportedTm env tbl b []) :
      SupportedTm env tbl (.mdata d b) []
  /-- A projection: the structure is tabled and informative, its block has one constructor of
      `nf` fields, and the field index is in range. -/
  | proj {S : Name} {i : Nat} {b : Expr} {args : List Expr} {I : ReifiedInduct} {np nf : Nat}
      (hind : tbl.ind? S = some I) (hinf : InformativeInd env S)
      (harity : IndArity env S np [nf]) (hi : i < nf)
      (hb : SupportedTm env tbl b []) :
      SupportedTm env tbl (.proj S i b) args
```

The checker's `mdata` arm reports a new `SupportError` at a non-empty spine, and its `proj` arm
decides the table-side half (one reified constructor, `i < numFields`); `supportedB_sound`
transports it to the model side through `ErasureSpec.block_adequate.fwd` and
`Witness.ReifiedInduct.Pinned`. Three consequences:

* `Supported.head : Supported env tbl e → (∀ c us, e.getAppFn ≠ .const c us) →
  SupportedTm env tbl e.getAppFn []` is a theorem — `NonConstHeadSupported` retired.
* `Supported.projInfo : SupportedTm env tbl e [] → ProjInfo env e` is a theorem, by
  `IndArity.indInfo` (`amend4/p3_indinfo.lean`, `[propext, Classical.choice, Quot.sound]`,
  landing in `LeanToLambdaBox/Erases.lean` beside `IndInfo.arity`). It retires `ProjSupported`
  and supplies `ErasesLB.cases`'s `hppi` for the dropped prefix — U4.4's route 2 is consumed,
  confirmed: the projection arm is what carries it.
* `KnownHead` becomes the model's three-way classification —
  `indType` carries `∃ iid np nfs, IndInfo env c iid np nfs`, `ctor` carries
  `∃ I k, CtorOf env c I k`, `defn` carries `ConstOrigin env c` — each discharged in
  `supportedB_sound` from `block_adequate` and the table pin. That is what gives step 4 the
  `ConstOrigin` `Erases.const` asks for, once the other two columns are excluded.

**A third checker arm, from §1.** `supportedB` gains `kernameSepB tbl`, run once on the table
rather than per node:

```lean
/-- The tabled names have pairwise-distinct λ□ keys. `toKername` is not injective
(`toKername_not_injective`), so two tabled constants can print as one kername and the second
shadows the first in the emitted environment; the fragment excludes that input.
Reported as `SupportError.kernameCollision`. -/
def kernameSepB (tbl : SourceTable) : Bool :=
  ((tbl.decls.map Prod.fst ++ tbl.inds.map Prod.fst).map toKername).eraseDups.length ==
    (tbl.decls.length + tbl.inds.length)
```

read back as one more clause of `Supported`, beside `term` and `bodies`:

```lean
  /-- **F-KERNAME**, input side: no two tabled names share a λ□ key. -/
  kernames : ∀ m m' : Name, (tbl.decl? m).isSome → (tbl.decl? m').isSome →
    toKername m = toKername m' → m = m'
```

decided in `supportedB` beside `peanoReadyB` — the precedent for a table-wide decidable
condition read as a hypothesis of a rule — and transported by `supportedB_sound`. Measured green
on all eleven committed tables, 33 checks, 0 witnesses (§1).

**Step 4's two exclusions.** The `ctor` column is excluded by the run: `Erasure.visitConstApp`
reaches `visitConst` only after `getCtorArity?` answered `none`, whose new negative clause
contradicts `Witness.ReifiedInduct.Pinned`'s constructor pin. The `indType` column is excluded
by `EraserAsks.oracle_informative` — a **theorem** of the two oracle clauses (§3) — at the gate
`Erasure.visitExpr` ran before dispatching: the head of the visited spine is the head of the term
the oracle answered `false` on. `Motive11`, `Motive12` and `Motive4` therefore carry one further
premise, threaded from step 1: `∀ iid np nfs, ¬ IndInfo env e.getAppFn-name iid np nfs`. What
survives of the column after both exclusions is the `defn` column, which is where step 4 reads
`tbl.decl? n = some d` — the tabled fact §1's separation conjunct is consumed at.

**Step 3** (`visitConstructor`) and **step 10** (`visitProj`) are U4.4's proofs at
`Step3Reg`/`Step10Reg` with the registry premise now read off `BridgeInv.indcanon`, plus
`GetEnvMonotone` → `prim_monotone.getEnv`, `IndDeclModelled`/`CtorDeclModelled` →
`block_adequate`, `RegisterModels` → §2's run lemma. The mask shape comes from the invariant, as
U4.4 measured it must: `ConfigPinned.remove_irrel_constr_args = false` fixes only the cold
branch, and `Erasure.run_register_inductive_cold_ok` exposes the constructor argument **counts**
and not the mask.

**Step 17** (`visitCases`) is the wave's one genuinely new proof. Its six open facts and their
suppliers:

| Fact | Supplier |
|---|---|
| `hppi : ∀ a ∈ args.take dp, ProjInfo env a` | `Supported.projInfo` (above) |
| `hclass` (`consts_classified`) | `UpstreamAsks env`, the wave's standing binder |
| `ElimDecl Γspec (toKername con) iid np dp nfs` | `SpecEnv.inds` → `IndCovered.elims`, whose `CasesOnShape`/`ConstOrigin`/`env.constants` inputs are `block_adequate.casesOn` |
| the exhibited `iid` is the run's | `IndInfo.inj` under `UpstreamAsks`, with `BridgeInv.indcanon` naming the run's |
| `CasesInfoAgrees.numAlts` | the new field of `CasesInfoAgreesK`, transported by `CasesInfoAgrees.of_pinned` |
| per-constructor field counts against the table | `KernelFields` inside `CasesInfoAgreesK`, same transport |

`CasesHead.notMachine` is deleted: `ConfigPinned.nat = .peano` already sends `Nat`'s and `Int`'s
eliminators down `Erasure.visitCases`' generic arm, so the field asks the head classification for
what the configuration settles. The seven loop lemmas U4.4 recovered are the plumbing; the
matcher they are stated against is `visitCasesBody`'s own, not `Erasure.visitCases`'.

## 6. Step 6, the block, and λ-headedness — N22 moves to the input side

The block/ambient split stands as U4.1 delivered it: `Erasure.visitMutual : Name → EraseM Unit`
returns no term, so `Motive6` concludes registration, and the mode predicate — a property of the
reader — is what carries the block reading into every term-producing motive. Step 6 consumes
`Motive1`'s approximation conjunct and the run's own conclusion; with §3 it carries no named
premise beyond the wave's standing binders.

**Where the block comes from.** `Erasure.visitMutual` (`Erasure.lean:859-919`) takes its
non-recursive exit when `single_decl && !(name_occurs name (ci.value! (allowOpaque := true)))`,
and otherwise mints one identifier per member of `ci.all`, installs `fixvarMap (ci.all.map
remove_unsafe_rec) ids`, and registers `.fix defs i` for each. That gate is a pure function of
the elaboration environment, and W4b names it:

```lean
/-- The block `Erasure.visitMutual` installs a fixvar map for at `n`, and `none` when it takes
its non-recursive exit. Mirrors `Erasure.lean:885` at `compilerInfo?`, which is
`Lean.Compiler.LCNF.getDeclInfo?` read off the ambient environment (`compilerInfo?_eq`, `rfl`). -/
def fixBlock? (lenv : Environment) (n : Name) : Option (List Name) :=
  match compilerInfo? lenv n, (compilerInfo? lenv n).bind (·.value? (allowOpaque := true)) with
  | some ci, some v =>
    if ci.all.length == 1 && !Erasure.name_occurs n v then none
    else some (ci.all.map Erasure.remove_unsafe_rec)
  | _, _ => none
```

**N22 becomes an input-side condition, in two halves.** W4's justification for leaving it on the
emitted program was that "the fragment's reachability does not see a member the program never
names", and that is false: `ci.all` is the compiler's SCC, so in a true mutual block every member
is named by another member's prepared body and is reachable. The condition is stated at the input
instead, as a new class-**D** binder beside `htbl` and `hsafe` — the same shape as `TableSafe`,
and for the same reason: the block is a `lenv` read the reified table does not carry.

```lean
/-- The blocks the run installs, against the table it is checked against. Class **D**,
mechanised by `lake exe reify --blocks`, which reads `fixBlock?` off the live environment. -/
structure TableBlocks (lenv : Environment) (env : VEnv) (tbl : SourceTable) : Prop where
  /-- Every member of an installed block is tabled. What §1's separation conjunct needs. -/
  members : ∀ (n : Name) (nms : List Name), (tbl.decl? n).isSome → fixBlock? lenv n = some nms →
    ∀ m ∈ nms, (tbl.decl? m).isSome
  /-- **N22, first half**: and its tabled body is λ-headed. -/
  lamHeaded : ∀ (n : Name) (nms : List Name), (tbl.decl? n).isSome → fixBlock? lenv n = some nms →
    ∀ (m : Name) (b : Expr), m ∈ nms → tbl.body? m = some b → b.isLambda = true
  /-- **N22, second half**: and no member is erasable, so none erases to `□`. A theorem-visible
      model-side conjunct, stated as the negation the oracle's soundness contradicts — the
      precedent is `SupportedTm.proj`'s `InformativeInd`. -/
  informative : ∀ (n : Name) (nms : List Name), (tbl.decl? n).isSome → fixBlock? lenv n = some nms →
    ∀ (m : Name) (b : Expr) (vb : VExpr), m ∈ nms → tbl.body? m = some b →
      TrExprS env [] [] b vb → ¬ Erasable env 0 [] vb
```

**How the two halves reach `LowerBlock.hfl`.** `SourceTableAdequate.body?_prepared` says the
tabled body is, up to `Expr.AlphaEq`, what `prepare_erasure` computes from the value the run
erases, so `lamHeaded` gives the run a λ-headed subject at each member; `Erasure.visitExpr`'s
first act is the oracle gate, and a `true` verdict there would give `Erasable env 0 [] vb`
through `ErasureSpec.oracle_sound_of_run`, which `informative` refutes — so the gate falls
through to `visitLambda` and the emitted member body is a `.lambda`; `run_mkDef_isLambda` and
`isLambda_foldl_toBvar` (§10) carry that through `mkDef`'s `toBvar` fold. W4b lands the composite
as `visitMutual_lowerBlock_hfl` in `LeanToLambdaBox/ColdStartShape.lean`, beside
`RegInvShape'.recConst`, the one premise in the tree that asks for a `LowerBlock`. The
output-side route — `FixLambda.of_onProgram` off `ErasureBridge.wf` — is retired for this
purpose: it read the condition off the very bundle `hbridge` still assumes. The unit reports
whether `FixLambda.of_onProgram` retains another consumer or is deleted.

**Why the first half is not decided by `supportedB`.** The refutation round expected
λ-headedness to be `rfl`-decidable on the prepared table. Half of it is: `ReifiedDecl.body?` is a
column and `((tbl.body? m).map Expr.isLambda) = some true` is `rfl`-decidable **at a given member
list**. The block itself is not: `ReifiedDecl` is `{levelParams, type, body?}` — only
`ReifiedInduct` carries an `all` field — and the run's gate reads the *unprepared* compiler
value, which the table does not hold either. A table-side proxy (`n ∈ constNames (tbl.body? n)`)
is neither an over- nor an under-approximation of `name_occurs n v`, and under-approximating it
would silently skip a block. So the block stays a `lenv` read, in a class-**D** binder checked
outside the kernel, and only the separation conjunct of §1 — which is about tabled names alone —
becomes a `supportedB` arm. Adding a column `all`/`fixBlock` to `ReifiedDecl` would move
`members` and `lamHeaded` into the checker at the cost of the reifier, the `--check` comparison
and a new pin clause; it is not taken in W4b, and §14 records the trade.

**Measured** (`amend4/m_*.lean`, eleven committed tables — six rungs, five corpus programs):
55 blocks install a fixvar map (G6 1, Arith 4, Sieve 10, Quicksort 15, BinaryTrees 10,
Fannkuch 15); **all 55 are singletons**, every member is tabled, and **all 55 tabled bodies are
λ-headed** — as are the prepared bodies re-derived from the environment. `blocksWithUntabledMember
= 0` and `noCompilerInfo = 0` on all eleven. The earlier corpus figure "50 of 50" counted the four
non-Arith programs only; with Arith and G6 it is 55 of 55. A *blanket* clause — every tabled body
λ-headed — would be **false on every table**: the non-λ bodies are the non-recursive instance
constants (`instAddNat`, `Nat.instDiv`, `instDecidableEqNat`, …) and the rung subjects themselves
(`spikeZero` is a `.const`, `spikeLet` a `.letE`). That is why the gate is in the statement.

The corpus exercises no multi-member block: the environment holds 223 true mutual `defnInfo`
blocks and **none of them has a member tabled by any of the eleven programs**. The block
machinery is therefore correct-by-construction over `ci.all` but measured only at self-recursive
singletons; `doc/coverage.md`'s N22 row says so.

`run_mkDef_box_not_lambda` stays where it is, restated as what it is: the reason the second half
of N22 is a conjunct and not a formality — a member the oracle erases breaks `hfl`.

## 7. `ConfigPinned`, and the import graph the capstone needs

`LeanToLambdaBox/Bridge.lean` imports `LeanToLambdaBox/Capstone.lean` for `ConfigPinned` alone,
which forbids the capstone from ever seeing the bridge. `ConfigPinned` moves to
`LeanToLambdaBox/ErasureSpec.lean` — the module that already collects what the correctness
statement assumes about its inputs, and the one module below both `Supported.lean` and
`Capstone.lean`. `Capstone.lean` keeps using it unchanged.

`Bridge.lean`'s import line becomes

```lean
import LeanToLambdaBox.ErasesLB
import LeanToLambdaBox.SpecEnv
import LeanToLambdaBox.ColdStartRun
import Lean4Lean.Verify.LocalContext
```

checked: `Bridge.lean`'s body elaborates unchanged against exactly these four
(`amend4/p4_bridge_imports.lean`). `SpecEnv` brings `ErasureSpec`, `ConfigPinned`, `Supported`
and `ErasesEnv`; `ErasesLB` brings the composite and `LowerFix`; `ColdStartRun` brings `visitExpr_shape_all` (which discharges `VisitExprRunConcl`),
`erase_run_ok`, `run_prepare_erasure_ok` and `run_rec_exit_decomp` to every step file and to the
capstone. No cycle: nothing in that closure imports `Capstone.lean`.

`Capstone.lean` then imports `LeanToLambdaBox.VisitExprRefines` and discharges the erasure half
of its own bundle. `Green.lean` is unchanged in its imports.

## 8. The axiom footprint, predicted rather than discovered

The 33-name cluster T8 inherits enters through step 1 → `ErasureSpec.oracle_sound_of_run` →
`Oracle.kernel_isErasable_sound`. That entry point is a **theorem of the tree today**, so the
cluster is measurable before T8 closes, and W4b measures it: `test/Ledger.lean` gains

```lean
#print axioms LeanToLambdaBox.ErasureSpec.oracle_sound_of_run
```

whose row is the 33 names. Measured at this checkpoint (`amend4/a1_oracle_axioms.out`): three
standard (`propext`, `Classical.choice`, `Quot.sound`), one `sorryAx`, two lean4lean pointer
axioms (`Lean4Lean.ptrEqConstantInfo_eq`, `ptrEqExpr_eq`), twenty-five Lean/Std
implementation-model axioms (fourteen `Lean.Expr.*_eq`, five `Lean.Level.*`, six
`PersistentArray`/`PersistentHashMap`/`Syntax`/`Std.TreeMap`), and two `_native.bv_decide` LRAT
names.

**The row measures axiom names, and nothing else, and `scripts/ledger.sh` is not touched.** The
script runs `test/Ledger.lean` and diffs the output against `test/ledger.expected`; it
normalises nothing today and W4b adds no normalisation. One of the two LRAT names prints with an
inaccessible marker — `Lean.Expr.mkData_flags._native.bv_decide.ax_1_12✝`, while
`Lean.Expr.Data.looseBVarRange_le._native.bv_decide.ax_1_7` prints without one — and the `✝` is
a private-name elision, not a hygiene counter: both spellings are stable across rebuilds, so a
normalisation would be defensive rather than load-bearing, and it would hide a changed
certificate index under an unchanged parent. What the row genuinely cannot see is the
*content* behind those two names: `#print axioms` prints the certificate's name and never its
LRAT proof, so a swapped certificate is invisible to this row — with or without normalisation.
`doc/trust.md` §(a3) says both things: that the cluster **is** measured, by that row, and that
what is measured is the name set.

When the capstone's erasure half lands (§11), `shipping_erase_correct_firstorder` and the six
`green_G*` rows gain the same 33 names. That is the predicted diff, and G4R's acceptance is that
the observed diff is exactly it — no fourth family, and in particular no `sorryAx` beyond the one
the cluster already carries.

## 9. The dead-declaration closure

`lake exe hygiene --dead` is file-granular: a file is live iff it is in the import closure of
`LeanToLambdaBox/Green.lean` ∪ `LeanToLambdaBox/Capstone.lean`. Measured at the W4 checkpoint:
454 declarations outside it, of which 282 are in `Bridge.lean`, `VisitExprRefines.lean`,
`VisitExprRefines/Motives.lean`, the three `VisitExprRefines/Step/*.lean`, `ColdStartRun.lean`
and `ColdStartInduction.lean`. §7 puts all eight modules inside the closure, so the count drops
to 172 — the prediction G4R checks. The residue is the tooling (`Tools/*.lean`), the benchmark
roots and the `ErasesCorrect/` arms that only the aggregator reaches.

## 10. Homes

| Declaration | Home |
|---|---|
| `run_mkDef_isLambda`, `isLambda_foldl_toBvar` | `LeanToLambdaBox/ErasureRun.lean`, beside `run_mkDef_ok` |
| `gdecls_mono_foldl_recConstStep`, `mem_gdecls_foldl_recConstStep`, `mem_gdecls_recConstState`, `stateLe_mem_gdecls`, `envLookup_of_mem_of_keys` | `LeanToLambdaBox/ColdStartShape.lean`, beside `nonrecConstState_gdecls` |
| `filter_replicate_keep_of_size`, `filterMap_zip_replicate` | `LeanToLambdaBox/ColdStartShape.lean`, merged with `filter_replicate_keep`/`list_filterMap_zip_keep`, which every bridge file now imports |
| `pass_core_bind`, `pass_getConstInfo_core` | `LeanToLambdaBox/ErasureRun.lean`, beside `run_liftCoreM_ok` |
| `ErasesLB.lit`, `ErasesLB.proj` and their `ErasesLBFix` twins | `LeanToLambdaBox/ErasesLB.lean`, the module docstring's count updated to eight |
| `test/ErasesLBCheck.lean`, `test/erasesLB.expected` | the same unit as the four intros above (U4R.8): the fixture enumerates every introduction lemma of the composite and CI runs it (`scripts/erasesLB.sh`, `build.yml:45`), so the four `#check`/`#print axioms` lines and the regenerated fixture land in the commit that moves them. Neither file is gate-owned — `test/ledger.expected` is (plan N3a), `test/erasesLB.expected` is not |
| `Supported.subterm`, `Reaches.mono` | `LeanToLambdaBox/Supported.lean` |
| `IndRegistryModelled` | `LeanToLambdaBox/Bridge.lean` (§2) |
| `IndArity.indInfo` | `LeanToLambdaBox/Erases.lean` |
| `altNumFields`, `ForallMatchesLam` | `LeanToLambdaBox/ErasureSpec.lean`, where the clauses that read them live |
| `CasesInfoAgrees`, `CasesInfoAgrees.of_pinned` | `LeanToLambdaBox/Supported.lean` — the transport needs the table and `lenv` at once |
| `prepare_sound` | `LeanToLambdaBox/ColdStartRun.lean`, beside `run_prepare_erasure_ok`, consuming `EraserAsks.passes_sound` |
| `EraserAsks`, `EraserAsks.oracle_informative`, `preparePasses` | `LeanToLambdaBox/ErasureSpec.lean`, beside `ErasureSpec` (§3) |
| `erasable_indSpine` | `LeanToLambdaBox/ErasesTotal.lean`, beside `Erases.indInfo_erasable`, which it composes |
| `fixBlock?` | `LeanToLambdaBox/Witness/SourceTable.lean`, beside `compilerInfo?`, whose reading of the environment it mirrors |
| `TableBlocks`, `kernameSepB`, `Supported.kernames` | `LeanToLambdaBox/Supported.lean`, beside `TableSafe` — the other binder that reads what the table does not carry |
| `Erases.noFVar` | `LeanToLambdaBox/ErasesAbstract.lean` if the occurrence lemmas land there, else `LeanToLambdaBox/Erases.lean`; the unit reports which |
| the five `LocalContext` lookup lemmas | deleted with the binder steps' name plumbing unless step 17 consumes them; the unit reports which |

## 11. What the capstone can discharge, and what it cannot

T8 is about `Erasure.visitExpr`, whose input is the **prepared** term:
`erase_run_ok` splits the run into `prepare_erasure e … = .ok (pe, {}) wp` and
`visitExpr pe {} { «config» := cfg } … = .ok (t, sf) wt`. `ErasureBridge.erases` is stated at
`e`, and the two cannot be identified — `Lean.Compiler.LCNF.macroInline` replaces a constant by
its body, and the erasure of the result is not an erasure of the original. So the syntactic
conjunct moves to the prepared term and the observable conjunct stays where the deliverable is:

```lean
structure ErasureBridge (env : VEnv) (bo : Name → Option Expr)
    (pe : Expr) (Γspec Γ : GlobalDeclarations) (t t₀ : LBTerm) : Prop where
  erasesEnv : ErasesEnv env bo Γspec t₀
  lowerEnv : LowerEnv Γspec Γ
  wfSpec : LBWfSpec Γspec
  wf : LBWfPeregrine Γ t
  simulate : …                                                    -- unchanged
  firstorder : …                                                  -- unchanged
```

with the two fields T8 supplies **gone from the structure** and proved instead:

```lean
/-- **The erasure half of the capstone's bundle, discharged.** The entry reader carries no
fixvar map and the entry state is empty, so `BridgeInv` holds there by construction, and T8
puts the emitted term in the composite at every specification environment of the final
state. -/
theorem erasure_bridge_of_run
    (P : ErasureSpec lenv env [] gw) (E : EraserAsks lenv env gw)
    (htbl : SourceTableAdequate lenv tbl) (hblk : TableBlocks lenv env tbl)
    (hcfg : ConfigPinned cfg) (hcb : CompilerBodies lenv env tbl.body?)
    (hsup : Supported env tbl pe) (hwt : TrExprS env [] [] pe ve)
    (hprep : Erasure.prepare_erasure e {} { «config» := cfg } cctx ref w = .ok (pe, {}) wp)
    (hvis : Erasure.visitExpr pe {} { «config» := cfg } cctx ref wp = .ok (t, sf) wt)
    (Γspec : GlobalDeclarations) (hspec : SpecEnv env tbl.body? sf Γspec) :
    ∃ t₀, Erases env [] [] pe t₀ ∧ Lower Γspec t₀ t
```

**The transport the W4 text was short by.** `shipping_erase_correct_firstorder`'s observable
clause quantifies over `SEval env tbl.body? [] fullFlags [] (mkApps e args) v`, while the run
applies `prepare_erasure` to `e` **alone**. The passes are whole-tree `Lean.Core.transform`
walks, so `f (mkApps e args) ≠ mkApps (f e) args` and a pass-soundness clause stated at the term
the pass ran on does not reach the spine. The missing step is a head congruence, and rather than
state it as a separate lemma with no prover, W4b folds it into the obligation itself — the
clause is spine-indexed:

```lean
  /-- Class **C**, `EraserAsks` (§3): each pass `Erasure.prepare_erasure` runs preserves the
      source evaluation of the subject **under an arbitrary application spine**. The spine is
      quantified because the capstone reads the observable at `mkApps e args` and the pass is a
      whole-tree walk; the clause says nothing about how the pass acts on `args`. -/
  passes_sound : ∀ (f : Expr → CoreM Expr), f ∈ preparePasses → ∀ (e e' : Expr) …,
    (liftM (f e) : EraseM Expr) s ctx cctx ref w = .ok (e', s₁) w₁ →
    ∀ (args : List Expr) bo Us' fl Δ v,
      SEval env bo Us' fl Δ (mkApps e args) v → SEval env bo Us' fl Δ (mkApps e' args) v
```

`prepare_sound` is then the composition over the four calls `run_prepare_erasure_ok` exposes
(`replaceUnsafeRecNames`, `macroInline`, `inlineMatchers`, `macroInline` again — three functions,
four calls, the `csimp` branch closed by `ConfigPinned.csimp`):

```lean
theorem prepare_sound (E : EraserAsks lenv env gw) (hcs : ctx.config.csimp = false)
    (hp : Erasure.prepare_erasure e s ctx cctx ref w = .ok (pe, s₁) w₁) :
    ∀ (args : List Expr) bo Us' fl Δ v,
      SEval env bo Us' fl Δ (mkApps e args) v → SEval env bo Us' fl Δ (mkApps pe args) v
```

**The rungs, and the term their premises are about.** `shipping_erase_correct_firstorder` keeps
its statement except that the `Erases` conjunct reads `pe`, the existential binds it together
with the run equation that produced it, and `hsup`/`hwt` are asked of `pe`. The W4 text claimed
that costs the rungs nothing "since the rungs already check the prepared subject". That is
false: all six rung subjects are **raw constants** — `eG1 = .const ``spikeZero []`
(`Green.lean:68`, and 288, 375, 475, 567, 810 for the others) — and `supportedB` and
`trExprS_const_of_table` run on that constant; only the table's *body* column is prepared
(`Witness/SourceTable.lean:293`). So each rung gains exactly one premise:

```lean
    (hprep : Erasure.prepare_erasure eG1 {} { «config» := spikeConfig } cctx ref w
      = .ok (eG1, {}) w)
```

at which `pe` is the rung's own subject and `hsup`/`hwt` are the checked terms the rung already
passes, unchanged. That is the honest and the cheap option, and it is cheaper than the
alternative it replaces: transporting the fragment and the typing across the passes
(`Supported env tbl e → Supported env tbl pe`) is a *stronger* statement about `macroInline`
than anything in `EraserAsks`, and false in general — inlining can put a shape the fragment
excludes into the term.

`hprep` is class **D** and mechanised the way `hrun` and `htbl` are: `lake exe reify` gains a
`--prepared MOD NAME…` verb that runs `Erasure.run (prepare_erasure (.const n [])) reifyConfig`
against the live environment and reports whether the result is the subject itself. That verb is
the natural home — `reify` already runs `prepare_erasure` on every tabled body and already runs
the interpreter over an imported module. Prediction, from what the passes are: identity at all
six, since none of the six subjects is `@[macro_inline]`, a matcher or an `_unsafe_rec`
companion.

The remaining premises of `erasure_bridge_of_run` at a rung are `P`, `E`, `htbl`, `hblk`,
`hcfg`, `hcb` — the rung's binders — plus `Γspec` with `SpecEnv`, which `SpecEnv.exists` produces
from the registration invariant. **That invariant is not W4b's**: `RegInvShape'` at the final
state is the registration workstream, and with it go `erasesEnv`, `lowerEnv`, `wfSpec` and the
environment half of `wf`. So W4b's honest outcome is:

* `hbridge`'s two erasure fields are discharged by a proved term, and the structure loses them;
* the six remaining fields are one binder, whose supplier is named per field;
* the rungs pass a proved term for the erasure half and a binder for the environment half, and
  carry three new named binders — `E : EraserAsks`, `hblk : TableBlocks`, `hprep` — each with a
  `doc/trust.md` row saying what mechanises it.

That is what G4R measures, and `doc/trust.md`'s `hbridge` row says exactly that.

## 12. W4b — the units

| Unit | Files owned | Depends | Est. | What lands |
|---|---|---|---|---|
| **U4R.1 the two bundles** | `LeanToLambdaBox/ErasureSpec.lean`, `LeanToLambdaBox/ErasesTotal.lean` (one theorem), `LeanToLambdaBox/Capstone.lean` (the `ConfigPinned` relocation only), `doc/rework/03-DEV-FIX.md` | — | 550 | §3: the strengthened `LookupAdequate`, `prim_monotone`, `block_adequate`, the `EraserAsks` bundle and `EraserAsks.oracle_informative` **proved**; `ConfigPinned` at its new home; F-DEPTH, F-UNSAFEREC and F-KERNAME filed |
| **U4R.2 abstraction** | `LeanToLambdaBox/Abstract.lean`, `LeanToLambdaBox/FixMetatheory.lean`, `LeanToLambdaBox/Lower.lean`, `LeanToLambdaBox/SpecEnv.lean`, `LeanToLambdaBox/ColdStartShape.lean` | U4R.1, U4R.3 (for `visitMutual_lowerBlock_hfl` only) | 550 | §4 — the three pass laws, the two necessity refutations, `SpecEnv.fvarFree` and `Erases.noFVar`; §10's `ColdStartShape` relocations; §6's `visitMutual_lowerBlock_hfl` |
| **U4R.3 the fragment and the table's checks** | `LeanToLambdaBox/Supported.lean`, `LeanToLambdaBox/Erases.lean` (one theorem), `LeanToLambdaBox/Witness/SourceTable.lean` (one definition, `fixBlock?`), `Tools/Reify.lean` | U4R.1 | 550 | §5's two `SupportedTm` repairs, `Supported.head`, `Supported.projInfo`, `KnownHead`'s model columns, `CasesInfoAgrees.of_pinned`, `IndArity.indInfo`; §1's `kernameSepB` arm and `Supported.kernames`; §6's `fixBlock?` and `TableBlocks`; the `reify --blocks` and `reify --prepared` verbs |
| **U4R.4 the invariant** | `LeanToLambdaBox/Bridge.lean`, `LeanToLambdaBox/VisitExprRefines/Motives.lean`, `LeanToLambdaBox/VisitExprRefines.lean`, and the three `LeanToLambdaBox/VisitExprRefines/Step/*.lean` **for the `tbl` parameter and the `BlockKeyed` premise only** (co-owned with U4R.6/U4R.7/U4R.8, which own every proof in them) | U4R.1 | 550 | §1's keyed modes, §2's registry field and `RunRefines` conjunct, §7's import line; the mechanical re-parameterisation that keeps the tree building |
| **U4R.5 the registry run** | `LeanToLambdaBox/ErasureRun.lean` | U4R.1, U4R.4 | 350 | `run_register_inductive_models`, `run_mkDef_isLambda`, `isLambda_foldl_toBvar`, §10's `ErasureRun` relocations |
| **U4R.6 env steps** | `LeanToLambdaBox/VisitExprRefines/Step/Env.lean` | U4R.1, U4R.3, U4R.4, U4R.5 | 400 | steps 4, 5, 6 with no named premise beyond the standing binders; the install site's `BlockKeyed` |
| **U4R.7 mechanical steps** | `LeanToLambdaBox/VisitExprRefines/Step/Mechanical.lean` | U4R.1–U4R.5 | 400 | steps 1, 7, 8, 9, 11, 12, 18; the seven relocated declarations deleted |
| **U4R.8 pass steps** | `LeanToLambdaBox/VisitExprRefines/Step/Passes.lean`, `LeanToLambdaBox/ErasesLB.lean`, `test/ErasesLBCheck.lean`, `test/erasesLB.expected` | U4R.1–U4R.5 | 950 | steps 2, 3, 10, 13, 14, 15, 16 at the induction's own interfaces, and **step 17**; §10's four `ErasesLB` intros relocated and the fixture regenerated |
| **U4R.9 the capstone** | `LeanToLambdaBox/Capstone.lean`, `LeanToLambdaBox/Green.lean`, `LeanToLambdaBox/ColdStartRun.lean`, `test/Ledger.lean`, `doc/trust.md` | U4R.1–U4R.8 | 500 | §11 — `ErasureBridge` without its two erasure fields, `erasure_bridge_of_run`, `prepare_sound`, the six rungs' `hprep`; §8's ledger row; the trust rows |
| **G4R gate** | `.github/workflows/build.yml`, `doc/coverage.md`, `test/ledger.expected` (plan N3a) | U4R.1–U4R.9 | 250 | §13's measurements, and the CI lines for `reify --blocks` and `--prepared` |

5,050 lines, up from W4b's first estimate of 3,900: §3's second bundle and its derivation, §4's
probe-measured size, §6's `TableBlocks` and the two `reify` verbs, and §11's per-rung premise are
the four places the refutation round added work.

Serial path: **U4R.1 → U4R.4 → U4R.5 → U4R.8 → U4R.9 → G4R** (3,150 lines). U4R.3 runs beside
U4R.4 from the start and gates U4R.2's last lemma; U4R.6 and U4R.7 run beside U4R.8, which is the
wave's long pole and whose own two halves are ordered (steps 2/13–16 first, then 3, 10 and 17).

**The tree builds at every unit.** W4b's first plan accepted a red window for the three definition
changes; it is not necessary and it is not taken. `ErasureSpec` is constructed nowhere (it is a
binder at every use) so U4R.1's new fields and clauses break no consumer — the three existing
readers take `.1` of the strengthened conjunctions; `Supported` is constructed only by
`supportedB_sound`, in U4R.3's own file; and `BlockKeyed`'s `tbl` index is threaded through the
three step files by U4R.4 itself under plan rule N1's co-ownership clause. So `lake build` and
`lake exe green-check --all` 6/6 are acceptance tests of **every** unit, not only of the gate.

## 13. G4R's acceptance

Machine-checkable, each measured by one command:

1. `lake build` green, `sorry`-free; `lake exe green-check --all` 6/6; `lake exe reify --check`
   on the self-test and the six rung tables green, and `SelfTest.staleTable` still rejected.
2. `#print axioms LeanToLambdaBox.visitExpr_refines_erasesLB` and `_erasesLBFix` with **all
   eighteen steps supplied**: the 33-name cluster of §8 and nothing else.
3. `grep -n "^def .* : Prop$" LeanToLambdaBox/VisitExprRefines/Step/*.lean` matches nothing —
   no step of the wave carries a named premise beyond the eight standing binders
   (`ErasureSpec`, `EraserAsks`, `SourceTableAdequate`, `TableBlocks`, `TableSafe`,
   `ConfigPinned`, `CompilerBodies`, `UpstreamAsks`).
4. `LeanToLambdaBox/Capstone.lean` declares no `erases`/`lower` field, and
   `erasure_bridge_of_run` is proved; `grep -c hbridge LeanToLambdaBox/Capstone.lean` counts the
   six-field binder only.
5. `git diff LeanToLambdaBox/Green.lean` touches only the erasure argument of the six rungs —
   each now a proved term — and the six new `hprep` binders.
6. `bash scripts/ledger.sh` green against a fixture that carries the
   `ErasureSpec.oracle_sound_of_run` row, and whose `shipping_erase_correct_firstorder` and
   `green_G*` rows show exactly the predicted 33 names. `git diff --stat scripts/ledger.sh` is
   empty: the row measures axiom names and the script normalises nothing (§8).
7. `lake exe hygiene --dead` reports 172, down 282 from the checkpoint.
8. `lake exe hygiene --dup --schedule --tables --cites --all` all exit 0.
9. `lake exe reify --blocks` and `lake exe reify --prepared` green on the six rung tables and
   subjects, both wired into `build.yml`: these are what mechanise `TableBlocks` and `hprep`.
10. `doc/trust.md` carries: the rewritten `hbridge` row; the class-**D** row for §3's
    `ErasureSpec` clauses; a class-**C** row per `EraserAsks` field and per `TableBlocks` clause,
    each naming an owner, a wave and what retires it; and §(a3) measured. **No class-E row for
    F-KERNAME.** `doc/coverage.md` carries the N22 row at its input-side reading with the 55/55
    measurement, the kername-separation restriction row, and the two fragment rows U4R.3's
    repairs imply.
11. `doc/rework/03-DEV-FIX.md` carries F-DEPTH, F-UNSAFEREC and F-KERNAME, each with the command
    that measures it and its output, and no wave depends on any of them landing.

## 14. Refutation round

W4b as first written was put through a refutation round; this section records the seven findings,
the decision each took and the evidence for it. Everything above reads as current fact — the
amendments are folded in, not appended. Probes are under `refute4/` (the refuter's) and
`amend4/` (this round's).

### F-A — `BlockKeyed`'s kername conjunct is false for most real blocks — accepted, and the count reread

**Decision: restrict the fourth conjunct to the tabled names, and make the restriction checked
rather than assumed (§1).** `∀ m : Name, toKername m ∈ nms.map toKername → m ∈ nms` is false
because `toKername` collapses `.num k` onto `.str k.repr` and has escape fixed points — 37,374 of
104,827 declaration blocks admit a collider (`refute4/r1_kername.lean`, re-run at this checkpoint
and reproduced exactly). The correction the amendment round adds: **every one of those colliders
is invented**. The probe synthesises a name with the same key and never asks whether the
environment declares it; measured over the environment itself, **227,840 constants have 227,840
distinct keys**, and no block — including the 223 true mutual blocks — has a real collider
(`amend4/m_env.lean`). So the conjunct is not "false at 71% of mutual blocks"; it is false as a
statement about all `Name`s and true of every declaration that exists. Restricted to the tabled
names it is decidable (`kernameSepB`, §5), green on all eleven committed tables in 33 checks with
0 witnesses, and supplied at the install site together with `TableBlocks.members`. The one
consumption site — `Step/Env.lean:615`, `hsep` applied to the visited constant — is served
because `Motive4` carries `tbl.decl? n = some d`. **The class-E F-KERNAME row is retired**: the
verification side is a checker arm with a coverage row, and the shipping side (two Lean constants,
one λ□ key, the second shadowing the first) is filed in `doc/rework/03-DEV-FIX.md`.

### F-B — three §3 clauses are about this repository's code — accepted, and it is worse than that

**Decision: a second bundle, `EraserAsks`, class C, one home, five fields, with the oracle clause
proved from two weaker ones (§3).** The finding is right about all four clauses. Two things the
probes add:

* `oracle_informative` as stated is **false about the Lean API** — `amend4/q1_refute.lean` exhibits
  an inductive at an `@[irreducible]` arity alias where the oracle answers `false`, by two
  independent mechanisms (`Expr.Data.approxDepth` is 8 bits, so `isArityCheck`'s fuel is ≤ 256 and
  here 1; and `Meta.whnf` will not unfold the alias). It is saved only by `env_connect`, which
  excludes that environment. So it is not kept as a field: it is **derived** from
  `oracle_false_refl` (near-definitional) and `kernel_ind_head_true` (true in modelled
  environments up to the fuel cap, measured `.ok true` at 2,940 of 2,940 inductive type formers),
  with the model half — `erasable_indSpine` — now a three-line theorem. The 8-bit cap is filed as
  **F-DEPTH**.
* the `Nodup` clause is **false about `getDeclInfo?`**, refuted by a legal declaration
  (`amend4/m12_unsafe_mutual.lean`: a `mutual` block holding `u` and `u._unsafe_rec`), which the
  eraser then **silently miscompiles** — one kername for two declarations, two identically named
  `FixDef`s, both recursive calls bound to one fix variable (`amend4/m13_erase_collide.lean`).
  Filed as **F-UNSAFEREC**; the clause survives as `EraserAsks.block_keys_distinct` at the
  kername level, with the one-line `visitMutual` guard that would retire it named and not applied.
  The measurement's scale is corrected: 228,937 `getDeclInfo?` answers, 219,838 with a non-empty
  block, 0 failures — not 104,827 blocks.
* the same probe found `LookupAdequate.declInfo`'s membership clause false for 3,376 names (every
  `_unsafe_rec` name), so it is now stated with the guard that makes it true.

### F-C — §11's transport is short by a congruence, and its rung claim is false — accepted

**Decision: fold the congruence into the obligation, and give each rung one premise (§11).**
Confirmed against the code: all six rung subjects are raw constants (`Green.lean:68, 288, 375,
475, 567, 810`), `supportedB`/`trExprS_const_of_table` run on them, and only the table's body
column is prepared (`Witness/SourceTable.lean:293`) — so "the rungs already check the prepared
subject" was false. Confirmed also that the passes are not compositional at application heads:
`amend4/probe1.lean` and `probe2.lean` isolate `macroInline` as the culprit
(`replaceUnsafeRecNames` and `inlineMatchers` are compositional on the shapes tested), so
`f (mkApps e args) ≠ mkApps (f e) args` is measured, not conjectured. Rather than state a head
congruence with no prover, `EraserAsks.passes_sound` is spine-indexed, which is the same fact in
the form the capstone consumes; `prepare_sound` composes it over the four calls
`run_prepare_erasure_ok` exposes. Each rung takes `hprep : prepare_erasure eGn … = .ok (eGn, {})
w`, class **D**, mechanised by a new `reify --prepared` verb — honest and cheap, where the
alternative (transporting `Supported` and `TrExprS` across the passes) is a stronger statement
about `macroInline` and false in general.

### F-D — the justification for keeping N22 output-side is refuted — accepted, decidability corrected

**Decision: adopt the input-side condition, in two halves, as a class-D binder with a
theorem-visible model conjunct (§6).** The refuted argument is indeed refuted: `ci.all` is the
compiler SCC, so a block member is reachable from any other. The correction: half 1 is **not**
`rfl`-decidable on the prepared table as the finding assumes. `ReifiedDecl` is `{levelParams,
type, body?}` — no block column — and the run's fix-block gate reads the *unprepared* compiler
value (`Erasure.lean:885`), which the table does not hold either; a table-side proxy is neither
an over- nor an under-approximation. So the λ-headedness is read off `tbl.body?` (which *is* a
column) at a block that `fixBlock? lenv n` names, and the pair is a `TableBlocks` binder beside
`TableSafe`, mechanised by `reify --blocks`. Half 2 is the theorem-visible conjunct the finding
asks for, with `InformativeInd` as its precedent and `ErasureSpec.oracle_sound_of_run` as the
theorem that spends it. Re-measured: 55 blocks install a fixvar map across the eleven tables
(Arith 4, as claimed), **all singletons, all λ-headed, no untabled member**; the earlier "50 of
50" omitted Arith and G6. A blanket clause would be false on every table.

### F-E — the ledger rationale is wrong — accepted

**Decision: no normalisation, and say what the row measures (§8).** `scripts/ledger.sh` runs
`test/Ledger.lean` and diffs; it normalises nothing today and W4b adds nothing. Re-measured at
this checkpoint (`amend4/a1_oracle_axioms.out`): 33 names, of which **one** — not two — prints
with the `✝` inaccessible marker. The row measures axiom **names**; the LRAT certificate contents
behind the two `_native.bv_decide` names are never printed and are therefore not measured, which
the section now says.

### F-F — two files no unit owns — accepted

**Decision: `LeanToLambdaBox/ErasesLB.lean`, `test/ErasesLBCheck.lean` and
`test/erasesLB.expected` are U4R.8's**, the unit that moves the four intros into the composite's
module (§10, §12). The fixture enumerates every introduction lemma and CI runs it
(`scripts/erasesLB.sh`, `build.yml:45`), so the `#check` lines and the regenerated fixture land in
the same commit. `test/ledger.expected` stays gate-owned (plan N3a) and is removed from U4R.9's
file list, where W4b's first plan had wrongly put it.

### F-G — §4's headline lemmas are unprobed — accepted, and now probed

**Decision: prove them, and assign the clause's discharge (§4).** `amend4/p6_lower_abstract.lean`
proves `Lower.noFVar`, `Lower.abstract` and `LowerAlt.abstract` outright, every arm, at
`[propext, Quot.sound]`; `amend4/p7_necessity.lean` refutes both statements with `ClosedBodies`
granted, so `FVarFreeBodies` is not a convenience. Two facts the probe adds to the design: the
fix arms do **not** use their induction hypothesis — they call `noFVar`, so it is proved first and
standalone — and no level side condition is needed, unlike `Lower.shift_comm`. `SpecEnv.fvarFree`
is **not** deferred: U4R.2 lands `Erases.noFVar`, which turns `SpecContent.defns`' erasure witness
into the clause at every producer. What remains open is what was already open — nothing in W4b
inhabits `RegInvShape'` at a final state — and the rung consequence is stated in `doc/trust.md`:
`hbridge` gains no field, `SpecEnv` gains one clause, and W5's supplier pays it.

## 15. Delivery findings

The nine units and the gate ran against the decisions of §§1-14. Every unit's own report carries
at least one finding against what this document printed at the time it started — most of them
against §3's step-premise retirement table and §11's capstone route, the two sections whose
promises were hardest to keep at a green tree. None retires a decision above; each narrows a
signature or a status this document's text must now match, the same convention as
`05-REPAIRS-W3.md` §17. §§0-14 above are already transcribed against the delivered shapes where
the narrowing is small; this table is the index, and it is also where the **headline shortfall**
is recorded once, rather than once per unit: `Step4`, `VisitExprRunConcl`, `DeclInfoAtHead`,
`hall`, `hseg` and `hctab` (BD6-BD13) are the six obligations `erasure_bridge_of_run` and every
rung still carry; a follow-up to this gate closes them, outside this document.

| # | Unit | §/design text | What is true | Delivered as | Evidence |
|---|------|-------------------|--------------|---------------|----------|
| **BD1** | U4R.1 | §10's home table puts `erasable_indSpine` in `LeanToLambdaBox/ErasesTotal.lean` | `SourceEval.lean` (which defines `mkApps`) imports `ErasesTotal.lean`, so the statement cannot even be *typed* there, and the design's three-line route (`trExprS_spine_head` + `erasable_mkApps`) needs `ErasesCorrect/Steps.lean`, whose closure would close a cycle | Proved self-containedly in `ErasureSpec.lean`, by strong induction on `args.length` through `List.eq_nil_or_concat`/`mkApps_append`, using only `Erases.indInfo_erasable`/`Erasable.app`; `ErasesTotal.lean` is byte-identical to the checkpoint | `ErasureSpec.lean:389` |
| **BD2** | U4R.1 | §3 prints `BlockAdequate`'s fifth field as `casesOn` | Lean has already declared `LeanToLambdaBox.BlockAdequate.casesOn`, the structure's own auto-generated eliminator — the name collides with the kernel, not with another definition | Landed as `casesOnDecl`, statement byte-identical apart from the bound-variable rename `ci → vc` | `ErasureSpec.lean` (`BlockAdequate`) |
| **BD3** | U4R.3 | §5's "Step 4's two exclusions" paragraph implies `KnownHead.defn` carries `ConstOrigin env c`, discharged via `block_adequate.ctorBwd` "against the pin" | Two independent reasons it cannot: (i) the only producer of `ConstOrigin` from `env.constants` is in `Origin.lean`, which *imports* `Supported.lean`, so the fact is unreachable at `KnownHead`'s declaration site; (ii) the reifier pushes constructors into the **decls** column (`Witness/SourceTable.lean:283`), so `tbl.decl? c = some d` is satisfied by a constructor and the pin records no kind — the design's own discharge is false regardless of import order | `KnownHead.defn` unchanged (`tbl.decl? c = some d`, `env.contains c`); the two exclusions moved to the **run** side, composed at step 4 from `constOrigin_of_constants` plus the negative `lookup_adequate.ctorArity`/`oracle_informative` clauses BD4/BD9 supply | `Supported.lean`; `Origin.lean:612` |
| **BD4** | U4R.3 | The pin (`Witness.ReifiedInduct.Pinned`) was believed to already supply `BlockAdequate.fwd`'s `KernelFields` | It supplies none of the four facts `fwd` reads: `cv.induct = n` is the table key, not `iv.name`; `cv.cidx` is the table's own index, not the constructor's position in `iv.ctors`; `cv.numParams` is unrelated to `iv.numParams`; and nothing says `n ∈ iv.all`. `iv.name = n` in particular is `Lean.Environment.find?` name coherence, which `decl_adequate`'s own docstring already names as outside `env_connect`'s reach | The pin strengthened with exactly the four missing kernel-indexing invariants (`iv.name = n`, `n ∈ I.all`, `c.cidx = j`, `c.numParams = I.numParams`); `reify --check` green on all eight committed tables at the new checker arm | `Witness/SourceTable.lean` (`ReifiedInduct.Pinned`, `checkInd`) |
| **BD5** | U4R.3 | Acceptance predicts "the two new `SupportError` arms" | A third is forced: the checker must reject a `.proj` head with zero or two constructors, or an out-of-range field index, and no existing arm (`propElimIntoData` is about relevance, `unknownConst` about tabling) says it | Three arms land: `mdataSpine`, `projField`, `kernameCollision`; `doc/coverage.md` owes three fragment rows, not two | `Supported.lean` |
| **BD6** | U4R.4 | §5's "Step 4's two exclusions" paragraph implies **both** land in this wave's `Motive4` repair | The type-former exclusion's only possible supplier, `EraserAsks.oracle_informative`, needs `hlp : ctx.lparams = Us`; `BridgeInv.lparams` gives only the prefix `ctx.lparams <+: Us`, and step 1 already splits on that very disequality for an unrelated reason (a dependency erased at its own level scope) — there is no reader at which the premise could be discharged, so adding it to `Motive4` would strand step 1 red | `Motive4` **unchanged** (head classified by `KnownHead` alone); `Step4` **refuted** as `Motive4` stands (a nullary tabled constructor, e.g. `Nat.zero`, satisfies every premise while the run emits a `.const` no `Erases ⨟ Lower` rule relates to a constructor head); `step4_of_exclusions` — the same statement with both exclusions as explicit premises — is proved instead, and is what the follow-up closes `Step4` from | `VisitExprRefines/Motives.lean:122-127`; `Step/Env.lean:654` |
| **BD7** | U4R.6 | The design (and this gate's own §6) states `VisitExprRunConcl` "becomes `visitExpr_shape_all`'s run half" | `visitExpr_shape_all`'s conclusion is `NoFix t ∧ LBClosed t 0 ∧ NoBlock t` — an output-shape fact with **no state relation and no generator bound at all**; its `Q`-generic form (`visitExpr_output_shape`) cannot be instantiated at a binary/world-indexed predicate either (`RunClosed.prep` needs `ctx.config.csimp = false` transparently, which a unary state predicate cannot carry) | `VisitExprRunConcl` stands as a genuine open class-**C** premise; its retirement needs a **fresh** eighteen-motive world-indexed induction, whose exit rules (`run_inline_tail_ok'`, `run_nonrec_exit_ok'`, `run_rec_exit_ok'`, `run_rec_exit_siblings_chained`) are written but not yet composed into one theorem — this is what the follow-up (and, transitively, W5's U5.1) build on | `ErasureRun.lean:2905-2924,2932-3355` |
| **BD8** | U4R.6 | §3's step-6 paragraph says `DeclBlockMember` "becomes `P.lookup_adequate.declInfo` at its guard" | `declInfo` has no `r = none` arm (unlike its two siblings `ctorArity`/`casesInfo`, which BD9's unit gave one each), and nothing in the standing binders derives `isUnsafeRecName? n = none` from `KnownHead`/`TableSafe`/`SourceTableAdequate` — a *safe* declaration may still be spelled `f._unsafe_rec` | A new named premise, `DeclInfoAtHead`, replaces `DeclBlockMember`, with the block-membership consequence proved *from* it; recommended fix (a `getEnv`-pinning `ErasureSpec` clause plus the missing `r = none` arm) is filed for the follow-up | `Step/Env.lean:84` |
| **BD9** | U4R.7 | §3/§5 imply step 12's saturated-arity case closes from `KnownHead.defn` + `ConstOrigin` + `UpstreamAsks.consts_classified` | Even with BD3's route granted, `ConstOrigin` does not by itself exclude `CtorOf` at a name the table's decls column also records (the reifier pushes constructors there too, BD3) | `hctab`, an explicit table-adequacy hypothesis, survives on `step_visitConstApp`; recommended as a third `SourceTableAdequate` clause, measured true on 24/24 constructor entries across every committed table | `VisitExprRefines/Step/Mechanical.lean` |
| **BD10** | U4R.7 | The design's step-1 paragraph says step 1 "applies `EraserAsks.oracle_informative` … and hands the resulting exclusion to `Motive11`" | It cannot: `Step1`'s own interface never took an `EraserAsks` argument, and even granting one, `oracle_informative` needs `hlp : ctx.lparams = Us`, which is BD6's same unreachable hypothesis | Step 1 produces no exclusion; the type-former exclusion is exactly where BD6 leaves it, and closing one closes the other | `VisitExprRefines/Motives.lean:796-809`, `Step/Mechanical.lean:373-377` |
| **BD11** | U4R.8 | §12's unit table assigns steps 3, 10, 17 to this unit with no residual noted | Step 3 (`visitConstructor`) cannot derive `indinfo.name ∈ indinfo.all` from `BlockAdequate` alone — `fwd` is vacuous at `iv.all = []`, and U4R.5's own report had already flagged this exact fact as refuted for `RegisterModels`' second conjunct | `hall`, an inline hypothesis on `step_visitConstructor`; the one-clause fix `BlockAdequate.selfMem` is filed, and it is the cheapest of the six residuals to close | `VisitExprRefines/Step/Passes.lean` |
| **BD12** | U4R.8 | §3's supplier table says `CtorDeclModelled` is "proved from `block_adequate`" | Its second conjunct also needs `UpstreamAsks`' block-uniqueness ask (ask 2) to place a *given* constructor at its kernel position — `KernelFields` is quantified over positions, not over a named constructor | Proved as designed at no extra binder cost (`A : UpstreamAsks env` was already standing); the text is corrected to "from `block_adequate` and ask 2" | `Step/Passes.lean:347,371` |
| **BD13** | U4R.8 | §5's supplier table names `CasesInfoAgrees.numAlts` (transported by `.of_pinned`) for step 17's `ForInStep.done` refutation | `CasesInfoAgrees` (as U4R.3 landed it) has no `numAlts` field at all, and a **second**, undesigned gap exists beside it: no clause relates the elaborator's `discrPos` to the model's `dp` | One inline hypothesis, `hseg`, bundles both gaps on `step_visitCases`; a two-clause fix (`CasesInfoAgrees.numAlts` plus a `discrPos`-agreement clause) is filed | `ErasureSpec.lean:95` (`CasesInfoAgreesK`); `Supported.lean` (`CasesInfoAgrees`) |
| **BD14** | U4R.9 | §11 prints `hbridge` as a plain existential, `∃ Σ⁺ t₀ pe, ErasureBridge …` | Not statable that way once `erases`/`lower` leave the structure: `Erases` is not deterministic outside the first-order fragment, so no equation joins an independently-bound `t₀` to the one the run actually produces | `hbridge` is Π-shaped — quantifying the final state and its run equation, concluding an existential `SpecEnv` and an inner `∀ t₀, … → ErasureBridge …` — strictly weaker than the binder it replaces, and the shape W5's U5.2 discharges | `Capstone.lean:182-186` |
| **BD15** | U4R.9 | §(d)/acceptance 4 predict each rung gains **three** new binders (`E`, `hblk`, `hprep`) | Ten land: the three plus the six residuals (BD6-BD13) plus `A : UpstreamAsks env`, which the design already sanctions as standing but had not counted here | Delivered as measured; `hall`/`hseg`/`hctab` stay inline `∀`-clauses rather than named `Capstone`-level binders, since the step files that need them cannot import `Capstone.lean` | `git diff --stat Green.lean` = 187 lines; `Green.lean:204-232` |
| **BD16** | U4R.9 | §(e)/acceptance 9a ask the class-**C** step-premise row to be **deleted**, "since no step carries one" | Six still do (BD6-BD13) | The row is **rewritten** to name `Step4`/`VisitExprRunConcl` and point at four class-**D** rows (`hdih`, `hctab`, `hall`, `hseg`) rather than deleted | `doc/trust.md` |
| **BD17** | G4R | §9 predicts `--dead` at 172, down 282 (the eight bridge/cold-start modules) | Measured 182, down 272: the eight held 278 declarations at HEAD, not 282 — the extra 4 are `IotaBridge.lean`'s, caught by the `"Bridge.lean"` substring match but not one of the eight and still outside the closure — and the residue is 176 + 6, the 6 being `Tools/Reify.lean`'s own growth from the wave's `--blocks`/`--prepared` verbs | Reported as measured (182/272), with both corrections named rather than the prediction silently adjusted after the fact | `scratchpad/g4r/dead.{head,now}.txt` |
| **BD18** | G4R | (no design text — a tool defect found while writing the coverage row) | `Tools/Hygiene.lean`'s `coverageExceptions` reads **every** backticked `.lean` token in `doc/coverage.md`'s exception section as an exemption, prose included, with no requirement that it sit in a table row; a first draft of the dead-declaration-budget paragraph inside that section silently weakened `--dead` from 182 to 159 | Paragraph moved **above** the exceptions heading, into its own section, restoring 182; the `Tools/Hygiene.lean` fix itself (read only a table row's first cell, matching `--schedule`'s own convention) is filed, not applied — that file is not gate-owned | `doc/coverage.md` ("The dead-declaration budget" vs. "Exceptions to the no-dead-code rule") |
| **BD19** | G4R | Acceptance 7b asks `lake exe hygiene --cites --all` to exit 0 | It never has: 38/94 missing tree-wide, all in `doc/rework/` planning and design prose, byte-identical (the 38) to the W4 checkpoint's set; none is in code, `doc/trust.md` or `doc/coverage.md`, all three of which are 0-missing | Left red tree-wide (not this gate's documents to fix); 94 is down from 96, the two fixed being `doc/coverage.md`'s own. **Inherited by W5's U5.5**, which deletes the largest single contributor (the three superseded candidate designs, 57 of the 94) | `scratchpad/g4r/cites{,all}.{head,now}.txt` |
| **BD20** | G4R (and U4R.6, U4R.7, U4R.9 independently) | This document's own §13.3 and several unit specs write `grep -n "^def .* : Prop$" LeanToLambdaBox/VisitExprRefines/Step/*.lean`, expecting an empty match once premises retire | The pattern is vacuous at **every** checkpoint: every premise is spelled `def N (args) : Prop :=`, and the trailing `:=` defeats the `$` anchor. It "passed" at the W4 checkpoint with four premises still standing, so it measured nothing there either | The honest spelling, `grep -nE "^def [A-Za-z0-9_']+ "` (no `$`), reads **2** today (`DeclInfoAtHead`, `VisitExprRunConcl`, both `Step/Env.lean`) against 4/5 at earlier checkpoints — a real reduction, just not the one the grep as written could have shown | multiple unit reports (U4R.6 obstruction 4, U4R.7, U4R.9's "two acceptance texts") |
| **BD21** | U4R.2 | §10's home table assigns five `Mechanical.lean` lemmas (`gdecls_mono_foldl_recConstStep` and four siblings) and a filter-lemma merge to `ColdStartShape.lean`, "from `Step/Mechanical.lean` (U4R.7 deletes them there)" | Jointly unsatisfiable by one unit: `Mechanical.lean` transitively imports `ColdStartShape.lean` (a hard duplicate-declaration build error, not a `--dup` warning), this unit's file list does not include `Mechanical.lean` (rule N1), and the filter lemmas' actual home is `ColdStartInduction.lean`, not `ColdStartShape.lean`, as §10 has it | **Not landed.** All seven declarations stay where they are; U4R.7 was told (and confirmed) not to delete them with nothing to delete into. The clean fix needs one follow-up unit co-owning all three files | U4R.2 obstruction 1; U4R.7 obstruction 3 |
| **BD22** | U4R.2 | §6 puts the N22 input-side composite (`visitMutual_lowerBlock_hfl`) in `ColdStartShape.lean` | Impossible independently of BD21: its two connecting lemmas (`run_visitMutual_decomp`, `run_rec_exit_siblings`) live in `ColdStartRun.lean`, which sits **above** `ColdStartShape.lean` in the import graph, and U4R.5 had not yet relocated `run_mkDef_isLambda`/`isLambda_foldl_toBvar` when this unit ran, so they too were unreachable | **Not landed.** The output-side route (`FixLambda.of_onProgram` via `visitMutual_block_hfl`) stays the only live one; the recommended home for the input-side composite is `ColdStartRun.lean`, after the `mkDef` relocation — every other ingredient (`TableBlocks`, `Witness.fixBlock?`, `ErasureSpec.oracle_sound_of_run`) is already reachable there | U4R.2 obstruction 4; U4R.7's confirmation that `FixLambda.of_onProgram` keeps a second, independent consumer |
| **BD23** | U4R.5 | The design implies `run_register_inductive_models` needs no hypothesis beyond `ErasureSpec`/`ConfigPinned` | `IndRegistryModelled`'s per-member `IndInfo` reading is only available at a **head** declaration (`block_adequate.fwd` reads `iv.name`/`iv.numParams` off it), while the run only ever looks up **members** — closing the gap needs `inf.all = indinfo.all`, a kernel coherence fact no `ErasureSpec` clause states | One extra hypothesis, `hdecl : lenv.find? hd = some (.inductInfo indinfo)`, naming the one declaration whose `InductiveVal` *is* `indinfo` — a hypothesis discharged at every call site from the `getConstInfo` that already produced it, not a new standing binder | `Bridge.lean:230` |

**What this table does not re-litigate.** Genuine build-mechanics deviations with no reader-facing
consequence — namespace clashes forced by Lean (`BlockAdequate.casesOnDecl`, BD2), file-ownership
corrections forced by the import graph with no content lost (several units' "obstruction 2/3"-style
entries not listed above), and measurement corrections that changed a number but not a verdict
(the environment's constant count, re-measured at three different modules across three units) —
are in the unit reports themselves and are not repeated here; this table is reserved for
deviations that change what a **document** must now say.
