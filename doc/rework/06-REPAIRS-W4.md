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
| F1 | `ErasesLBMode`'s block conjunct is unsatisfiable at a constant target, so `Motive4` is false and step 4 is refuted (`erasesLBMode_block_refuted`, U4.2 obstruction 1) | the conjunct is keyed by `BlockKeyed` — length, `Nodup`, kername separation — and `BridgeInv.fixvars` names a `BlockKeyed` pair (§1) |
| F2 | The block conjunct quantifies over representations whose `ids` may hold a freshly opened binder, so `FixvarsAllReserved` is false as stated (U4.3 obstruction 4) | the same keying; `BridgeInv.fixvars_ids_subset` **proves** the premise (§1) |
| F3 | The inductive registry is in no invariant, so motives 3, 10, 17 are unprovable (U4.4 obstruction 1) | `BridgeInv.indcanon : IndRegistryModelled env s`, and `RunRefines` carries the invariant forward (§2) |
| F4 | Eight step premises are `ErasureSpec`-field-shaped facts about primitives (U4.2, U4.3, U4.4; `doc/trust.md`'s step-premise row) | `ErasureSpec` gains `prim_monotone`, `block_adequate`, `oracle_informative`, `transforms_sound`, and `LookupAdequate`'s three weak clauses are strengthened (§3) |
| F5 | Six premises are model-side readings `decl_adequate` does not classify (same row) | all six are **proved** from `block_adequate` and the strengthened lookups, or from the repaired fragment (§3, §5) |
| F6 | `SpecEnv` does not imply that `Lower` commutes with abstraction; the `fixConst`/`fixBody` arms cannot be replayed (U4.3 obstruction 3) | `Lower.abstract` under `FVarFreeBodies Γ`, a new `SpecEnv` clause; `LowerAbstracts`/`SpecEnvAbstracts` retired (§4) |
| F7 | `SupportedTm.mdata` passes a spine through, so `NonConstHeadSupported` is not derivable (U4.3 obstruction 1) | the `mdata` rule is restricted to the empty spine; the premise becomes `Supported.head` (§5) |
| F8 | `SupportedTm.proj` misses the model arity and the field bound (U4.3 obstruction 2, U4.4 route 2) | the rule carries both; `ProjSupported` retired and `Supported.projInfo` supplies step 17's `hppi` (§5) |
| F9 | Step 17 is not written and needs six facts with no supplier (U4.4 obstruction 2) | each of the six is assigned a supplier in §5; the step is U4R.7 |
| F10 | `Motive4`'s premises do not exclude a constructor or type-former head, and `ConstOrigin` is not derivable from `KnownHead` (U4.2 obstruction 2) | `KnownHead` becomes the model's three-way classification; the constructor column is excluded by the run, the type-former column by `oracle_informative` (§3, §5) |
| F11 | λ-headedness is not a run invariant: a block member erased to `.box` breaks `LowerBlock.hfl` (U4.3b obstruction 2) | N22 stays a scope restriction on the **emitted** program, with its refutation named and its supply chain composed (§6) |
| F12 | `ConfigPinned` in `LeanToLambdaBox/Capstone.lean` makes the bridge unreachable from the capstone (G4 obstruction 5) | it moves to `LeanToLambdaBox/ErasureSpec.lean`; `LeanToLambdaBox/Bridge.lean` imports `SpecEnv` and `ColdStartRun` instead (§7) |
| F13 | T8's closed footprint is 33 axioms, 29 of them predicted by no ledger row (G4 obstruction 2) | the cluster is measured **now**, at `ErasureSpec.oracle_sound_of_run`, by a ledger row and a `doc/trust.md` class-D row (§8) |
| F14 | 282 declarations of the bridge and cold-start modules are outside the `Green.lean` ∪ `Capstone.lean` closure (G4 obstruction 4) | the closure consumes them once §7 lands; measured prediction 454 → 172 (§9) |
| F15 | Seven declarations are homed in a step file for want of an owner, and `prepare_sound` has no home (U4.3b obstruction 4, U4.5 obstruction 1) | homes assigned in §10 |
| F16 | The capstone's `erases` conjunct is at the source term while T8 is about the **prepared** term, and no relation carries one to the other (this round) | the syntactic conjunct moves to `pe`, the observable conjunct stays at `e`, and `prepare_sound` transports the evaluation (§3, §11) |

## 1. The fixvar mode, keyed

`fixvarMap nms ids = Std.HashMap.ofList (nms.zip ids)` loses information twice: `List.zip`
truncates, and a repeated name is overwritten. Reading the block conjunct at *every* pair whose
zip rebuilds the reader's map is therefore not "the block", and two W4 units hit it from
opposite sides — the appended pair refutes step 4, the duplicated pair admits an `ids` holding a
freshly opened binder.

```lean
/-- The conditions under which a pair of index lists faithfully describes the map the reader
carries: `Erasure.visitMutual` installs one pair, and the zip admits many others. -/
def BlockKeyed (ctx : ErasureContext) (nms : List Name) (ids : List FVarId) : Prop :=
  ctx.fixvars = some (fixvarMap nms ids) ∧ nms.length = ids.length ∧ nms.Nodup ∧
    ∀ m : Name, toKername m ∈ nms.map toKername → m ∈ nms

def ErasesLBMode (ctx : ErasureContext) (env : VEnv) (Us : List Name)
    (Γspec : GlobalDeclarations) (Δ : VLCtx) (e : Expr) (t : LBTerm) : Prop :=
  (ctx.fixvars = none → ErasesLB env Us Γspec Δ e t) ∧
  (∀ nms ids, BlockKeyed ctx nms ids →
    ErasesLBFix env Us Γspec (nms.map toKername) ids Δ e t)

def ErasesLBAltMode (ctx : ErasureContext) (env : VEnv) (Us : List Name)
    (Γspec : GlobalDeclarations) (Δ : VLCtx) (nf : Nat) (m : Expr)
    (alt : List BinderName × LBTerm) : Prop :=
  (ctx.fixvars = none → ErasesLBAlt env Us Γspec Δ nf m alt) ∧
  (∀ nms ids, BlockKeyed ctx nms ids →
    ErasesLBFixAlt env Us Γspec (nms.map toKername) ids Δ nf m alt)
```

`ErasesLBMode.block` takes `BlockKeyed ctx nms ids` in place of the bare map equation, and so do
`ErasesLBMode.lam`, `.letE`, `.congr_fixvars` and `ErasesLBAltMode.mk`
(`LeanToLambdaBox/VisitExprRefines/Step/Mechanical.lean`) — the congruences carry the three
conditions transparently, which is why the repair costs the other thirteen steps nothing.

Three conditions, not the two G4's repair order names. The third, `nms.Nodup`, is what F2 needs:
without it `fixvarMap [a, a] [x, y] = fixvarMap [a] [y]`, and the conjunct is read at an `ids`
containing an arbitrary `x`.

**Evidence** (`amend4/p1_keying.lean`, all `[propext, Classical.choice, Quot.sound]`):

* `fixvarMap_get?_of_nodup` — a `BlockKeyed` pair reads back each of its own pairs.
* `fixvarMap_ids_subset` — hence every `BlockKeyed` representation's identifiers are the
  installed pair's.
* `bridgeInv_ids_reserved` — **`FixvarsAllReserved`, proved** from `BridgeInv.fixvars`; it lands
  as `BridgeInv.fixvars_ids_subset`.
* `blockKeyed_append_absurd` — the pair `erasesLBMode_block_refuted` runs on is not
  `BlockKeyed`, so the refutation no longer reaches the conjunct.
* `step4_content` — `visitConst_refines`'s conclusion **is** the keyed conjunct: the two
  conditions it takes are `BlockKeyed`'s second and fourth. Step 4 is one `exact` after §3
  supplies the head's `ConstOrigin`.

`erasesLBMode_block_refuted` is not deleted: restated at the unkeyed conjunct it is the reason
the three conditions are there, and `toKername_not_injective` beside it is the reason the fourth
is not a formality. Both stay in `LeanToLambdaBox/VisitExprRefines/Step/Env.lean` with that role
in their docstrings.

`BridgeInv.fixvars` names a `BlockKeyed` pair:

```lean
  fixvars : ctx.fixvars = none ∨
    ∃ nms ids, BlockKeyed ctx nms ids ∧ ids.Nodup ∧ ∀ x ∈ ids, gen.Reserves x ∧ x ∉ Δ.fvars
```

Its two new conjuncts are established where the reader is built, not here: `nms.Nodup` is
`LookupAdequate.declInfo`'s new clause (§3) at `Erasure.visitMutual`'s `names.map
remove_unsafe_rec`, and the kername separation is finding **F-KERNAME** — `toKername` is not
injective, so it is a scope restriction on the block's names, with a `doc/trust.md` class-E row.

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
structure BridgeInv (env : VEnv) (Us : List Name) (cfg₀ : ErasureConfig) (gen : NameGenerator)
    (ctx : ErasureContext) (s : ErasureState) (Δ : VLCtx) : Prop where
  mlc : ∃ m : MLCtx, m.WF env Us ∧ m.lctx = ctx.lctx ∧ m.vlctx = Δ
  lparams : ctx.lparams <+: Us
  cfg : ctx.config = cfg₀
  kfresh : ∀ fv ∈ Δ.fvars, kernelNGen.Reserves fv
  reserved : ∀ fv ∈ Δ.fvars, gen.Reserves fv
  fixvars : ctx.fixvars = none ∨
    ∃ nms ids, BlockKeyed ctx nms ids ∧ ids.Nodup ∧ ∀ x ∈ ids, gen.Reserves x ∧ x ∉ Δ.fvars
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
    ∀ Γspec, SpecEnv env tbl.body? s' Γspec → ErasesLBMode ctx env Us Γspec Δ e t

theorem BridgeInv.mono_state (h : BridgeInv env Us cfg gen ctx s Δ) (hrc : RunConcl s s')
    (hind : IndRegistryModelled env s') : BridgeInv env Us cfg gen ctx s' Δ
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

## 3. `ErasureSpec` — the primitives the steps call

Every clause below is class **D** and is a statement about a primitive of the Lean API —
`Lean.Environment`, `Lean.getCasesInfo?`, `Lean.Compiler.LCNF.getCtorArity?`,
`Lean.Compiler.LCNF.getDeclInfo?`, `Lean.getEnv`, `Lean.logInfo`, `Lean.Meta.isInstance`,
`Lean.Meta.inferType`, `Lean.Core.transform`, `Lean.Compiler.LCNF.macroInline`,
`Lean.Compiler.LCNF.inlineMatchers`, `Erasure.isErasable` — and about the model's connection to
the elaboration environment. No clause is a specification of this repository's own code.

Three clauses of `LookupAdequate` are strengthened:

```lean
  /-- `getDeclInfo?` answers for a name `lenv` knows, at the compiler block that name belongs
      to, whose members are distinct after `Erasure.remove_unsafe_rec`. -/
  declInfo : ∀ (n : Name) (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State)
    (w : Void IO.RealWorld) (r : Option ConstantInfo) (w₁ : Void IO.RealWorld),
    Lean.Compiler.LCNF.getDeclInfo? n cctx ref w = .ok r w₁ →
    gw w ≤ gw w₁ ∧ ∀ ci, r = some ci → lenv.find? n ≠ none ∧
      n ∈ ci.all.map Erasure.remove_unsafe_rec ∧ (ci.all.map Erasure.remove_unsafe_rec).Nodup
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
  /-- The three transforms `Erasure.prepare_erasure` runs with the `csimp` gate off. -/
  transform : ∀ (f : Expr → CoreM Expr), f ∈ preparePasses → ∀ (e : Expr) …,
    (liftM (f e) : EraseM Expr) s ctx cctx ref w = .ok (e', s₁) w₁ → gw w ≤ gw w₁

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

and three new `ErasureSpec` fields:

```lean
  /-- The primitives the erasure calls for their effect alone. Class **D**. -/
  prim_monotone : PrimMonotone gw
  /-- The kernel's blocks, constructors and eliminators, in the model. Class **D**. -/
  block_adequate : BlockAdequate lenv env
  /-- A `false` verdict of the relevance oracle is not returned at a type former. The
      oracle's **completeness**, at the one shape the fragment cannot exclude: an inductive
      type name is an argument of almost every spine, so `Erasure.visitExpr` is called on it
      and the emitted `.const` has no `Erases` reading — only `Erases.box` covers a type, and
      only a `true` verdict reaches it. Class **D**. -/
  oracle_informative : ∀ (e : Expr) (s : ErasureState) (ctx : ErasureContext)
    (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld)
    (s₁ : ErasureState) (w₁ : Void IO.RealWorld),
    Erasure.liftMetaM (Erasure.isErasable ctx.lparams e) s ctx cctx ref w = .ok (false, s₁) w₁ →
    ∀ c us, e.getAppFn = .const c us → ∀ iid np nfs, ¬ IndInfo env c iid np nfs
  /-- The transforms `Erasure.prepare_erasure` runs preserve the source evaluation, which is
      what `prepare_sound` composes and what carries the capstone's observable conjunct from
      the subject to the term the erasure walks. Class **D**. -/
  transforms_sound : ∀ (f : Expr → CoreM Expr), f ∈ preparePasses → ∀ (e e' : Expr) …,
    (liftM (f e) : EraseM Expr) s ctx cctx ref w = .ok (e', s₁) w₁ →
    ∀ bo Us' fl Δ v, SEval env bo Us' fl Δ e v → SEval env bo Us' fl Δ e' v
```

`preparePasses : List (Expr → CoreM Expr) := [Erasure.replaceUnsafeRecNames,
Lean.Compiler.LCNF.macroInline, Lean.Compiler.LCNF.inlineMatchers]` is defined beside them, so
the two clauses quantify over the three calls `Erasure.prepare_erasure` makes rather than
naming a repository function.

**What this retires.** Of the seventeen step premises:

| Premise | Fate |
|---|---|
| `CoreCallsMonotone`, `GetEnvMonotone` | `prim_monotone.getEnv`/`.logInfo`/`.isInstance` |
| `InferTypeMonotone`, `InferLamAdequate` | `prim_monotone.inferType` (one clause, both readings) |
| `PrepareRunConcl` | state half **proved** from `run_prepare_erasure_ok` under `ConfigPinned`; generator half is `prim_monotone.transform` |
| `DeclBlockMember` | `LookupAdequate.declInfo` |
| `CasesInfoAdequate` | `LookupAdequate.casesInfo` + `CasesInfoAgrees.of_pinned` |
| `CtorArityAdequate` | `LookupAdequate.ctorArity` + `block_adequate.ctor` + `Witness.ReifiedInduct.Pinned` |
| `CtorAdequate`, `CtorDeclModelled`, `IndDeclModelled` | **proved** from `block_adequate` |
| `RegisterModels` | **proved** (§2) |
| `NonConstHeadSupported`, `ProjSupported` | **proved** (§5) |
| `FixvarsAllReserved` | **proved** (§1) |
| `SpecEnvAbstracts` | **proved** (§4) |
| `VisitExprRunConcl` | **proved** from `visitExpr_shape_all` once `LeanToLambdaBox/Bridge.lean` imports `LeanToLambdaBox.ColdStartRun` (§7) |

No step of W4b carries a named `Prop` premise beyond `ErasureSpec`, `SourceTableAdequate`,
`TableSafe`, `ConfigPinned`, `CompilerBodies` and `UpstreamAsks`, which are the wave's standing
binders. That is the acceptance test G4R runs by `grep`.

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
abstraction: its declared bodies are erasure images at the empty context. -/
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

`Lower.abstract` is `Lower.shift_comm`'s induction with `LowerAlt.abstract` as `motive_2`;
`ClosedBodies` is not among its premises, since `toBvar` reads no de Bruijn index.

**Evidence** (`amend4/p2_abstract.lean`, all within `[propext, Quot.sound]`) — the pieces the
tree does not have and the arm that refuted the premise:

* `hasFVar_toBvar_of` and its three list companions — `toBvar y` introduces no free variable.
* `closeFixFold_not_hasFVar`, `closeFix_not_hasFVar` — `closeFix` removes every identifier of
  its list and introduces none.
* `constToFVar_not_hasFVar` — `ConstToFVar` introduces only the block's identifiers.
* `closeConstAt_not_hasFVar` — hence the block closure of a free-variable-free body is free of
  **every** variable, the block's own included.
* `fixNode_not_hasFVar`, `toBvar_fixNode` — **the arm that refuted `LowerAbstracts`,
  discharged**: `toBvar` is the identity on the `.fix` node, so both fix arms replay unchanged.
* `toBvar_mkApps` — the spine law the `elimApp` arm needs.

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

`RegInvShape'` (`LeanToLambdaBox/ColdStartShape.lean`) gains the matching field
`specFVarFree`, threaded by its constructors exactly as `specClosed` is, and
`RegInvShape'.specEnv` supplies the new `SpecEnv` clause from it.

It is a clause and not a theorem because `SpecContent` has no coverage clause: its four
content clauses are conditional on an entry being present, and an entry at a kername that is
neither a tabled constant's, nor a body-less non-eliminator's, nor a covered block's or
eliminator's may hold anything. A `SpecContent.only` clause would derive `fvarFree` from
`defns`; it is not taken, because every consumer of the environment holds a `SpecEnv` and the
one-field form costs one line at each of the two producers.

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

**Step 4's two exclusions.** The `ctor` column is excluded by the run: `Erasure.visitConstApp`
reaches `visitConst` only after `getCtorArity?` answered `none`, whose new negative clause
contradicts `Witness.ReifiedInduct.Pinned`'s constructor pin. The `indType` column is excluded
by `ErasureSpec.oracle_informative` at the gate `Erasure.visitExpr` ran before dispatching — the
head of the visited spine is the head of the term the oracle answered `false` on. `Motive11`,
`Motive12` and `Motive4` therefore carry one further premise, threaded from step 1:
`∀ iid np nfs, ¬ IndInfo env e.getAppFn-name iid np nfs`.

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

## 6. Step 6, the block, and λ-headedness

The block/ambient split stands as U4.1 delivered it: `Erasure.visitMutual : Name → EraseM Unit`
returns no term, so `Motive6` concludes registration, and the mode predicate — a property of the
reader — is what carries the block reading into every term-producing motive. Step 6 consumes
`Motive1`'s approximation conjunct and the run's own conclusion; with §3 it carries no named
premise at all.

`LowerBlock.hfl` is supplied by U4.3b's chain, composed once
`LeanToLambdaBox/Bridge.lean` imports `LeanToLambdaBox.ColdStartRun` (§7): `run_rec_exit_decomp`
gives the block state, `mem_gdecls_recConstState` and `stateLe_mem_gdecls` carry the member entry
to the final state, and `visitMutual_block_hfl` reads `LBWfPeregrine.fixLambda` there through
`FixLambda.of_onProgram`. W4b lands the composite as `visitMutual_lowerBlock_hfl` in
`LeanToLambdaBox/ColdStartShape.lean`, beside `RegInvShape'.recConst`, the one premise in the
tree that asks for a `LowerBlock`.

λ-headedness is **not** a run invariant, and W4b does not pretend otherwise:
`run_mkDef_isLambda` reduces `hfl` to per-member λ-headedness of the erased bodies and
`run_mkDef_box_not_lambda` refutes it at a member the oracle erases. It also cannot be moved into
`supportedB`: `Erasure.visitMutual` walks `ci.all`, the fragment's reachability does not see a
member the program never names, and a member whose body is a manifest non-λ — an alias inside a
mutual block — passes every input-side condition the checker can decide. So it stays what it is:
restriction **N22**, a scope condition on the *emitted* program, discharged at the capstone
through `ErasureBridge.wf`'s `LBWfPeregrine.fixLambda`, whose own discharge does not route back
through `hfl`. W4b makes it visible: `doc/trust.md`'s N22 row names `run_mkDef_box_not_lambda`
and says the condition is decided on the output, and `doc/coverage.md`'s N22 row carries the
measurement.

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

whose row is the 33 names. Two of them are `bv_decide` LRAT certificates whose printed spelling
carries an inaccessible marker (`Lean.Expr.mkData_flags._native.bv_decide.ax_1_12✝`), so
`scripts/ledger.sh` normalises `._native.bv_decide.ax_<n>_<m>` occurrences to a stable token
before the diff, and the normalisation is documented in the script's own header. `doc/trust.md`
§(a3) then says the cluster **is** measured, by that row, and drops the sentence that no row
measures it; the file:line table stays.

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
| `Supported.subterm`, `Reaches.mono` | `LeanToLambdaBox/Supported.lean` |
| `IndRegistryModelled` | `LeanToLambdaBox/Bridge.lean` (§2) |
| `IndArity.indInfo` | `LeanToLambdaBox/Erases.lean` |
| `altNumFields`, `ForallMatchesLam` | `LeanToLambdaBox/ErasureSpec.lean`, where the clauses that read them live |
| `CasesInfoAgrees`, `CasesInfoAgrees.of_pinned` | `LeanToLambdaBox/Supported.lean` — the transport needs the table and `lenv` at once |
| `prepare_sound` | `LeanToLambdaBox/ColdStartRun.lean`, beside `run_prepare_erasure_ok`, consuming `ErasureSpec.transforms_sound` |
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
    (P : ErasureSpec lenv env [] gw) (htbl : SourceTableAdequate lenv tbl)
    (hcfg : ConfigPinned cfg) (hcb : CompilerBodies lenv env tbl.body?)
    (hsup : Supported env tbl pe) (hwt : TrExprS env [] [] pe ve)
    (hprep : Erasure.prepare_erasure e {} { «config» := cfg } cctx ref w = .ok (pe, {}) wp)
    (hvis : Erasure.visitExpr pe {} { «config» := cfg } cctx ref wp = .ok (t, sf) wt)
    (Γspec : GlobalDeclarations) (hspec : SpecEnv env tbl.body? sf Γspec) :
    ∃ t₀, Erases env [] [] pe t₀ ∧ Lower Γspec t₀ t
```

`shipping_erase_correct_firstorder` keeps its statement except that the `Erases` conjunct reads
`pe` and the existential binds it, together with the run equation that produced it; its
observable clause still quantifies over `SEval env tbl.body? [] fullFlags [] (mkApps e args) v`,
transported to `pe` by `prepare_sound`. `hsup` and `hwt` are asked of `pe`, which is what the
rungs already check: `supportedB` runs on the reified table's prepared bodies.

The remaining four premises of `erasure_bridge_of_run` at a rung are `P`, `htbl`, `hcfg`, `hcb` —
already the rung's binders — plus `Γspec` with `SpecEnv`, which `SpecEnv.exists` produces from
the registration invariant. **That invariant is not W4b's**: `RegInvShape'` at the final state is
the registration workstream, and with it go `erasesEnv`, `lowerEnv`, `wfSpec` and the environment
half of `wf`. So W4b's honest outcome is:

* `hbridge`'s two erasure fields are discharged by a proved term, and the structure loses them;
* the six remaining fields are one binder, whose supplier is named per field;
* the rungs pass a proved term for the erasure half and a binder for the environment half.

That is what G4R measures, and `doc/trust.md`'s `hbridge` row says exactly that.

## 12. W4b — the units

| Unit | Files owned | Depends | Est. | What lands |
|---|---|---|---|---|
| **U4R.1 the spec** | `LeanToLambdaBox/ErasureSpec.lean`, `LeanToLambdaBox/Capstone.lean` (the `ConfigPinned` relocation only) | — | 400 | §3's clauses, `ConfigPinned` at its new home |
| **U4R.2 abstraction** | `LeanToLambdaBox/Abstract.lean`, `LeanToLambdaBox/FixMetatheory.lean`, `LeanToLambdaBox/Lower.lean`, `LeanToLambdaBox/SpecEnv.lean`, `LeanToLambdaBox/ColdStartShape.lean` | — | 450 | §4, plus §10's `ColdStartShape` relocations and §6's `visitMutual_lowerBlock_hfl` |
| **U4R.3 the fragment** | `LeanToLambdaBox/Supported.lean`, `LeanToLambdaBox/Erases.lean` | U4R.1 | 400 | §5's two rules, `Supported.head`, `Supported.projInfo`, `KnownHead`'s model columns, `CasesInfoAgrees.of_pinned`, `IndArity.indInfo` |
| **U4R.4 the invariant** | `LeanToLambdaBox/Bridge.lean`, `LeanToLambdaBox/VisitExprRefines/Motives.lean`, `LeanToLambdaBox/VisitExprRefines.lean`, `LeanToLambdaBox/VisitExprRefines/Step/Passes.lean` (the `IndRegistryModelled` definition only) | U4R.1 | 450 | §1, §2, §7's import line; the motives' new premise and conjunct |
| **U4R.5 the registry run** | `LeanToLambdaBox/ErasureRun.lean` | U4R.1, U4R.4 | 350 | `run_register_inductive_models`, §10's `ErasureRun` relocations |
| **U4R.6 env steps** | `LeanToLambdaBox/VisitExprRefines/Step/Env.lean` | U4R.1, U4R.3, U4R.4 | 300 | steps 4, 5, 6 with no named premise |
| **U4R.7 mechanical steps** | `LeanToLambdaBox/VisitExprRefines/Step/Mechanical.lean` | U4R.1–U4R.5 | 400 | steps 1, 7, 8, 9, 11, 12, 18 with no named premise; the seven relocated declarations deleted |
| **U4R.8 pass steps** | `LeanToLambdaBox/VisitExprRefines/Step/Passes.lean` | U4R.1–U4R.5 | 900 | steps 2, 3, 10, 13, 14, 15, 16 at the induction's own interfaces, and **step 17** |
| **U4R.9 the capstone** | `LeanToLambdaBox/Capstone.lean`, `LeanToLambdaBox/Green.lean`, `LeanToLambdaBox/ColdStartRun.lean`, `test/Ledger.lean`, `test/ledger.expected`, `doc/trust.md` | U4R.1–U4R.8 | 450 | §11, `prepare_sound`, §8's ledger row and trust rows |
| **G4R gate** | `.github/workflows/build.yml`, `scripts/ledger.sh`, `doc/coverage.md` | U4R.1–U4R.9 | 200 | §13's measurements |

Serial path: **U4R.1 → U4R.4 → U4R.5 → U4R.8 → U4R.9 → G4R** (2,750 of the 3,900 lines).
U4R.2 runs beside U4R.1 from the start; U4R.3 beside U4R.4; U4R.6 and U4R.7 beside U4R.8.
U4R.8 is the wave's long pole and its own two halves are ordered (steps 2/13–16 first, then 3,
10 and 17), so it starts as soon as U4R.5 lands.

## 13. G4R's acceptance

Machine-checkable, each measured by one command:

1. `lake build` green, `sorry`-free; `lake exe green-check --all` 6/6; `lake exe reify --check`
   on the self-test and the six rung tables green.
2. `#print axioms LeanToLambdaBox.visitExpr_refines_erasesLB` and `_erasesLBFix` with **all
   eighteen steps supplied**: the 33-name cluster of §8 and nothing else.
3. `grep -n "^def .* : Prop$" LeanToLambdaBox/VisitExprRefines/Step/*.lean` matches nothing —
   no step of the wave carries a named premise beyond the standing binders.
4. `LeanToLambdaBox/Capstone.lean` declares no `erases`/`lower` field, and
   `erasure_bridge_of_run` is proved; `grep -c hbridge LeanToLambdaBox/Capstone.lean` counts the
   six-field binder only.
5. `git diff LeanToLambdaBox/Green.lean` touches only the erasure argument of the six rungs, each
   of which is now a proved term.
6. `bash scripts/ledger.sh` green against a fixture that carries the
   `ErasureSpec.oracle_sound_of_run` row, and whose `shipping_erase_correct_firstorder` and
   `green_G*` rows show exactly the predicted 33 names.
7. `lake exe hygiene --dead` reports 172, down 282 from the checkpoint.
8. `lake exe hygiene --dup --schedule --tables --cites --all` all exit 0.
9. `doc/trust.md` carries: the rewritten `hbridge` row (six fields, each with its supplier), the
   class-D row for §3's clauses, the class-E rows for F-KERNAME and N22, and §(a3) measured.
