# 12 — W9, the remaining route to `hbridge`

`doc/rework/11-REPAIRS-W8.md` planned nine units. Wave 4 landed W1–W4, W6, W8 and W9 and left
`hbridge` a binder: nothing produces `RegAcc` at a run of the shipping eraser, so
`bridgeEnv_of_regContent` — the theorem that composes the binder's payload — has zero consumers
(`doc/rework/07-STATUS.md` §4, `scratch/round7/W4-refute.md` §4). What is left is W5a/W5b/W5c
and W7. This document specifies them, decides the two questions wave 4 left undecided, and says
what stands afterwards.

Every statement §2 displays elaborates at this toolchain against the tree at `f65c86f`; the
probe is `scratch/round7/w9_sigs.lean` (`w9_sigs.out`, exit 0, fifteen `sorry`-stubs and two
`Decidable` instances that close without one). Scratch probes are untracked. No unit waits on a
shipping merge: `dev/fix` is merged and the four shipping files are frozen for this wave.

## 1. Two decisions

### 1.1 The realizer entries: excluded, not invented (§2.2)

F-QUOT and F-EQREC give `Erasure.visitMutual` two registering exits that emit a **bodied** entry
at a **body-less** name: `Erasure.addRealizer` at `Erasure.quotRealizer qv.kind` for a quotient
primitive, and at `Erasure.recursorRealizer`'s synthesized eliminator for a propositional
singleton's recursor (`Erasure.lean:1240-1246`). Neither body is an erasure image, so
`RegContent.defns` has no trigger to read and the accumulator would have to invent `b₀ := t`.

`11-REPAIRS-W8.md`'s successor plan proposed to admit them as specification entries of the
`ElimDecl` kind — a key whose body the compilation scheme fixes, `Lower` the identity there,
with `SpecContent` gaining the matching clause. **That is the wrong half of the analogy, and
this wave declines it.** `ElimDecl` is the specification reading of a key the pass *consumes*:
the eraser emits no `casesOn` key, `Lower.const` refuses it through `RuntimeKey`, and
`Lower.elimApp` turns its occurrences into `.case` nodes. A realizer key is the opposite — it is
emitted, and its occurrences stay `.const` nodes that `Lower.const` must accept — so admitting it
as a `RuntimeKey` breaks `Lower.const` at exactly those occurrences, and admitting it as a new
`SpecContent` clause costs an exclusion on `SpecContent.axioms` at a class nothing else excludes.

Against MetaRocq the reading is plain. Rocq has no such constants, and the reason is structural
rather than accidental: `erase_constant_body` (`../metarocq/erasure/theories/Extract.v:264`)
relates an emitted body to *the source body it erased*, and a constant with no body is emitted
body-less — `erases_constant_body`'s `None`/`None` arm. The eraser never invents computational
content. Lean's two realizers do, which is a departure from the specification's shape, not a
case it forgets to cover. The honest treatment is therefore not to widen the specification until
the departure fits inside it, but to say where the departure lives: **outside the verified
fragment**. `Supported` refuses a quotient primitive by name (`PlainHead.notQuotPrim`) and a
recursor of a tabled inductive at the head (`SupportedTm.const`'s `hrec`, restriction N21 — a
recursor spine has no source evaluation at all), so no supported subject reaches either exit.
§2.2 proves that, at the cost of one decidable table property and two class-**D** readings of
`Lean.Environment.find?`, and the two realizer arms of the step become refutations rather than
obligations. A side effect is that `Erasure.recursorRealizer`'s own call to
`Erasure.register_inductive` (`Erasure.lean:415`) goes with them: F-W8-6's fourth registration
site is unreachable inside the fragment, so W5a is owed at steps 3, 10 and 17 only.

Two corrections to the record while this is decided. First, `Lower` **does** have a `.case`
congruence (`Lower.lean:384`, the eleventh of fifteen arms), so `scratch/round7/W5-report.md`
§4's "Lower has no `.case` congruence" is wrong at HEAD: `Lower Γ t t` at a realizer body is
available from a reflexivity lemma on the fix-free, runtime-key-free fragment, the realizer
bodies naming no constant at all. The obstruction was never that the fact is unprovable but that
`RegInvShape'.addRealizer` declines to *assume* it (`ColdStartShape.lean:419-425`), which is a
different and correct complaint. Second, what keeps `SpecContent.axioms` from contradicting a
realizer entry today is that `ConstOrigin env n` fails at a recursor or a quotient constant,
`VDeclDefines` being `False` at `.induct` and `.quot` (`Erases.lean:159-166`). That is a
load-bearing fact of the model which nothing states; after §2.2 nothing needs it.

### 1.2 The tabled-`casesOn` dependency: measured, not guarded (§2.1)

`SpecContent.defns` carries no `isCasesOnName` guard where `SpecContent.axioms` does
(`ErasesEnv.lean:218`, `:222`). `scratch/round7/W4-refute.md` §1.1 records that G5–G8 are
consistent only because `Nat.casesOn` is tabled *without* a compiler body, and that nothing in
the tree says so: a table regeneration that gave it one would silently make five rungs vacuous.

**The guard is not available, and the sibling clause is not the precedent it looks like.**
`ErasesEnv.runtimeKey_isCasesOn` (`ErasesCorrect/Steps.lean:921`) derives *both* halves of "a
runtime key belongs to a body-less `casesOn`" from the unguarded `defns`: the `bo c = some b`
branch is refuted by `erases_ne_elimBody` at the entry `IndCovered.elims` declares, and it is
that refutation that yields `bo c = none`. The ι arm spends that conjunct (`:1077`). A guard on
`defns` deletes the branch and with it the conclusion, so the obligation reappears one level up
as a premise whose only content is that the excluded case does not occur — which rule (2)
forbids. The unguarded clause is also not unsound: the contradiction is a *theorem*, so a tabled
`casesOn` with a body makes a rung's hypotheses unsatisfiable, i.e. vacuous, never false.

Vacuity is what the ladder measures with `decide`, so the fact belongs in the measured column
beside `Green.noCasesOnKeys`, as a decidable per-table property — a class-**C** checked term
under rule (2), and the reading the code actually relies on. §2.1 lands it.

## 2. The units

Gates assume the battery of `doc/rework/07-STATUS.md` §6 stays green, that `lake exe hygiene
--dead` stays at its 339 budget, and that the measured **33-name** footprint of
`shipping_erase_correct_firstorder` and of `green_G1`…`green_G8` does not grow. "R" needs real
reasoning, "M" is mechanical.

| id | title | kind | depends |
|---|---|---|---|
| W9-H | the tabled-`casesOn` dependency, and three bookkeeping fixes | M | — |
| W9-A | the realizer exits, closed by exclusion | R | W9-H |
| W9-B | W5a — the `register_inductive` prefix, produced from a run | R, large | W9-H |
| W9-C | W5b — the block exit at a growing environment | R | W9-B |
| W9-D | W5c — the accumulator conjunct, in its own induction | R, large | W9-A, W9-B, W9-C |
| W9-E | W7 — `erasure_bridge_env`, and the binder discharged | R | W9-D |

### 2.1 W9-H — the hidden assumption, measured; and three stale readings

```lean
/-- No tabled `casesOn` name carries a compiler body. `SpecContent.defns` has no
`isCasesOnName` guard where `.axioms` has one and must not have one —
`ErasesEnv.runtimeKey_isCasesOn` derives `bo c = none` at a runtime key from the unguarded
clause and the ι arm spends it (`ErasesCorrect/Steps.lean:1077`) — so what a guard would
assume is measured here instead: a tabled `casesOn` with a body makes a rung's hypotheses
unsatisfiable through `erases_ne_elimBody` at the entry `IndCovered.elims` declares. -/
def NoTabledCasesOnBody (tbl : SourceTable) : Prop :=
  ∀ c ∈ tbl.decls.map Prod.fst, isCasesOnName c = true → (tbl.body? c).isNone = true

instance : Decidable (NoTabledCasesOnBody tbl)

theorem noTabledCasesOnBodies :
    NoTabledCasesOnBody g5Table ∧ NoTabledCasesOnBody g6Table ∧
    NoTabledCasesOnBody g7Table ∧ NoTabledCasesOnBody g8Table := by decide +kernel
```

`Green.g7_natCasesOn_tabled` keeps its statement — it is the non-vacuity evidence that the new
measurement has a subject — and gains a sentence saying which of the two facts the rungs' own
consistency needs. The supporting lemma, stated so the measurement's force is visible:

```lean
theorem runtimeKey_bodyless (H : SpecContent env bo lp Γspec) (hco : ConstOrigin env m)
    (hsome : (LBTerm.envLookup Γspec (toKername m)).isSome)
    (hrk : RuntimeKey Γspec (toKername m)) :
    isCasesOnName m = true ∧ bo m = none
```

— `ErasesEnv.runtimeKey_isCasesOn` read at `SpecContent` rather than at a program, which is
where W9-B's prefix needs it. `SpecContent.runtimeKey_isCasesOn`
(`VisitExprRefines/Step/Env.lean:821`) is the half of this that exists; the unit strengthens it
to both conjuncts or records that the existing one suffices.

Three stale readings, all measured in `scratch/round7/W4-refute.md` §5.3/§5.6:

* `LeanToLambdaBox/ErasesEnv.lean:48` and `LeanToLambdaBox/Erasability.lean:425` cite
  `ErasureSpec.arity_of_propositionalInd_false`; the declaration is
  `LeanToLambdaBox.arity_of_propositionalInd_false` (`ErasureSpec.lean:639`, no `ErasureSpec.`
  prefix). `lake exe hygiene --cites` checks cited *files*, not cited *declarations*, so the
  battery does not catch it.
* `Tools/Coverage.lean:276` lists `"hargReach"` in `audited` and `:670` heads a column with it,
  where the binder is `hbody` since W7/U9; `:735`'s hardcoded sentence still asserts "G8 alone
  binds `hargReach`", contradicting the regenerated table beside it.
* `Tools/Coverage.lean:717` says the `nbTerm` column is `g<i>_noBodylessRefs`' "only remaining
  reader" without saying that it reads `env.find?` alone — an existence census, not a content
  check.

*Files.* `LeanToLambdaBox/Green.lean` (the two definitions and the measurement, beside
`noCasesOnKeys`, `:1380`), `LeanToLambdaBox/ErasesEnv.lean` (`:48`),
`LeanToLambdaBox/Erasability.lean` (`:425`), `Tools/Coverage.lean` (`:276`, `:670`, `:717`,
`:735`).

*Consumers.* `noTabledCasesOnBodies` is read by W9-B, at the prefix's `defns` obligation at a
member's `casesOn` key; `runtimeKey_bodyless` by the same. The `Coverage.lean` edits are read by
`doc/coverage.md`, regenerated in the same commit.

*Gate.* `lake exe coverage --check` green after one regeneration; `#check` on the two corrected
citation targets in the unit's probe; `lake exe green-check --all` 8/8; `scripts/ledger.sh`
unchanged. `decide +kernel` at a rung adds no axiom name.

*Confidence.* High. Both definitions are decidable at HEAD — the probe's two `instance`
declarations close without a `sorry` — and `NoTabledCasesOnBody` is a list-quantified
`Option.isNone` test over a literal table, the same shape `Green.noCasesOnKeys` decides today.
The risk is elaboration time on `g7Table`/`g8Table`, which carry 30 and 30 declarations; the
fallback is a per-rung split of the conjunction.

*Probe.* `scratch/round7/w9_sigs.lean` §H (`noTabledCasesOnBodies`, `runtimeKey_bodyless`, the
two instances).

### 2.2 W9-A — the realizer exits, closed by exclusion

```lean
/-- The recursor suffix `Supported.isRecursorName` reads, without the table lookup. -/
def recSuffix (c : Name) : Bool :=
  match lastComponent c with
  | some s => s == "rec" || s == "recOn" || s == "brecOn" || s == "below" || s == "ndrec"
  | none => false

/-- Every tabled name with a recursor suffix has its inductive type tabled — the gap between
`isRecursorName tbl c = false` and "`c` is no recursor". Decidable at a table. -/
def TableRecPrefixed (tbl : SourceTable) : Prop :=
  ∀ c ∈ tbl.decls.map Prod.fst, recSuffix c = true → (tbl.ind? c.getPrefix).isSome = true

theorem tableRecPrefixed_rungs :        -- eight conjuncts, `by decide +kernel`
    TableRecPrefixed g1Table ∧ … ∧ TableRecPrefixed g8Table

/-- Two readings of one named Lean primitive: the kernel's quotient primitives are the four
`Erasure` already names, and a recursor is declared under a recursor suffix. Class **D**. -/
structure SchemeNames (lenv : Lean.Environment) : Prop where
  quot : ∀ (c : Name) (qv : QuotVal), lenv.find? c = some (.quotInfo qv) →
    quotPrimNames.contains c = true
  recr : ∀ (c : Name) (rv : RecursorVal), lenv.find? c = some (.recInfo rv) →
    recSuffix c = true

/-- **The two realizer exits are unreachable inside the fragment.** -/
theorem no_realizer_exit_compiler (hS : SchemeNames lenv) (hrp : TableRecPrefixed tbl)
    (hsup : Supported env tbl (.const n [])) (htab : (tbl.decl? n).isSome)
    (hci : compilerInfo? lenv n = some ci) :
    (∀ qv : QuotVal, ci ≠ .quotInfo qv) ∧ (∀ rv : RecursorVal, ci ≠ .recInfo rv)
```

The proof is the two exclusions `Supported` already carries, read back. `SupportedTm.const` at
`args = []` gives `PlainHead.notQuotPrim` — `quotPrimNames.contains n = false`, which
`SchemeNames.quot` contradicts at a `.quotInfo` — and `hrec : isRecursorName tbl n = false`,
which with `TableRecPrefixed` and `htab` gives `recSuffix n = false`, which `SchemeNames.recr`
contradicts at a `.recInfo`. `compilerInfo?` answers either `lenv.find? n` or the
`_unsafe_rec` companion's, and a companion is a `.defnInfo`, which is the one further step
`no_realizer_exit_compiler` takes over `no_realizer_exit`.

`SchemeNames` is a new class-**D** bundle of two fields, both properties of
`Lean.Environment.find?` alone, admissible under rule (2) and of a kind with
`BlockAdequate.selfName`. It is taken beside `P`, not inside it: `ErasureSpec` is per level
scope and these two fields mention no scope. Unlike W6's two fields it lands **with** its
reader — `StepAcc6` (W9-D) — which is what `scratch/round7/W4-refute.md` §7 item 2 asks.

*Files.* `LeanToLambdaBox/Supported.lean` (`recSuffix` factored out of `isRecursorName`, whose
statement and name are unchanged), `LeanToLambdaBox/ErasureSpec.lean` (`SchemeNames`),
`LeanToLambdaBox/VisitExprRefines/Step/Env.lean` (`TableRecPrefixed`, the two theorems, beside
`run_visitMutual_registers`), `LeanToLambdaBox/Green.lean` (the eight-rung measurement).

*Consumers.* W9-D's `StepAcc6`, at the `ci.value? = none` branch's three exits
(`VisitExprRefines/Step/Env.lean:505-556`): two are refuted here and the third, `addAxiom`, is
`regInv_addAxiom_step`, landed at W5.

*Gate.* `no_realizer_exit_compiler` closes; the eight-rung `decide +kernel` closes;
`grep -n "recursorRealizer" LeanToLambdaBox/VisitExprRefines/` finds only the refutation site;
`scripts/ledger.sh` unchanged; `scripts/fixes.sh` green — the shipping realizers are untouched
and `test/fixes/F-QUOT.lean`, `F-EQREC.lean` keep measuring them.

*Confidence.* Medium-high. The two `SchemeNames` fields are true of Lean's kernel — `addQuot`
adds exactly `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` as `.quotInfo`, and a `.recInfo` is
added under `I.rec` — and neither is refutable inside the tree, which is also their weakness:
nothing constructs a `SchemeNames`, so they are assumptions in the same sense
`scratch/round7/W4-refute.md` §4.3 names. The residue to state at the clause: if `Quot.sound`
is a `.quotInfo` at this toolchain, `quot` is false as printed and must read the four names
`Erasure`'s own `quotRealizer` dispatches on. The unit measures that before landing the field.

*Probe.* `scratch/round7/w9_sigs.lean` §A (five declarations, all elaborating; the two
`Decidable` instances close).

### 2.3 W9-B — W5a, the `register_inductive` prefix produced from a run

```lean
/-- The F-KERNAME clause the prefix's `defns`/`axioms` need: `toKername` is not injective
(`toKername_not_injective`), so a prefix entry answers for every source name at its key. No
tabled name maps to the block key the run mints or to a member's `casesOn` key. -/
def BlockKeysFresh (tbl : SourceTable) (indinfo : InductiveVal) : Prop :=
  ∀ c ∈ tbl.decls.map Prod.fst,
    toKername c ≠ mutualBlockKn indinfo ∧
      ∀ I ∈ indinfo.all, toKername c ≠ toKername (Name.str I "casesOn")

/-- What the prefix one `Erasure.register_inductive` conses is: `SpecEntryOk`'s treatment
lifted to a prefix (F-W8-4), quantified over *every* member of the block, since
`Erasure.register_inductive` inserts every member of `indinfo.all` into the registry
(`Erasure.lean:324`, `:364`). MetaRocq's `erases_global_ind` (`Extract.v:290-293`) plus the
`casesOn` declarations λ□ prunes. -/
structure IndPrefixOf (env : VEnv) (bo : Name → Option Expr) (lp : Name → List Name)
    (indinfo : InductiveVal) (pre : GlobalDeclarations) : Prop where
  covered : ∀ I ∈ indinfo.all, IndCovered env pre I
  content : SpecContent env bo lp pre
  entries : ∀ p ∈ pre, (∃ mib : MutualInductiveBody, p.2 = .inductiveDecl mib) ∨
    ∃ (body : LBTerm) (iid : InductiveId) (np dp : Nat) (nfs : List Nat),
      p.2 = .constantDecl ⟨some body⟩ ∧ ElimBody iid np dp nfs body

/-- **The registration step, at a run**: `regInv_registerInd_step`'s thirteen premises
produced rather than assumed. -/
theorem regInv_registerInd_run (P : ∀ Us, ErasureSpec lenv env Us gw)
    (htbl : SourceTableAdequate lenv tbl) (hcfg : ConfigPinned ctx.config)
    (hkey : BlockKeysFresh tbl indinfo) (hcas : NoTabledCasesOnBody tbl)
    (A : RegAcc env tbl.body? tbl.levels? Γ s)
    (hfind : lenv.find? indinfo.name = some (.inductInfo indinfo))
    (hmiss : s.inductives.get? indinfo.name = none)
    (hrun : Erasure.register_inductive indinfo s ctx cctx ref w = .ok (r, s₁) w₁) :
    ∃ pre : GlobalDeclarations, IndPrefixOf env tbl.body? tbl.levels? indinfo pre ∧
      SpecGrow Γ (pre ++ Γ) ∧ RegAcc env tbl.body? tbl.levels? (pre ++ Γ) s₁
```

`pre` is existential, not computed: the block body and the per-member field counts are chosen
from the model data `ErasureSpec.BlockAdequate` supplies, and `KernelFields` fixes them as a
function of `lenv` and the `InductiveVal` (`ErasureSpec.lean:81`), so no choice principle beyond
`Classical.choice` enters. The prefix is the block entry at `mutualBlockKn indinfo` together
with one `(toKername (I ++ "casesOn"), .constantDecl ⟨some (mkElimBody iid np dp nfs)⟩)` per
informative member, at `dp = numParams + 1 + numIndices`.

What each field is paid with:

| obligation | source |
|---|---|
| `covered`'s `.block` | `BlockAdequate.fwd` at each `I ∈ indinfo.all`, whose fourth premise `KernelFields` is `BlockAdequate.fields` (W6) and whose `lenv.find? I` is `BlockAdequate.selfName` (W6) |
| `covered`'s `IndBodyOf` | the emitted bodies, through `run_register_inductive_cold_entries`' constructor-argument report, at `ctx.config.remove_irrel_constr_args = false` from `ConfigPinned` |
| `covered`'s `IndFlagSound` | `ErasureSpec.propositionalInd_of_arity` (`:610`) — the sound half, which is the half the field asks for. W9's refuted converse is **not** needed, and this is the field's first consumer |
| `covered`'s `.elims` | `BlockAdequate.casesOnDecl` at each informative member, together with the prefix's own eliminator entry and the block entry beside it, which is `ElimDecl`'s second lookup |
| `content.defns` | `BlockKeysFresh` at a block key, and at an eliminator key `NoTabledCasesOnBody` with `toKername_id_of_isCasesOnName` (W9-H) |
| `content.axioms` | `isCasesOnName c = false` excludes the eliminator keys; `BlockKeysFresh` the block key |
| `content.blocks`/`.elims` | `covered`, at each member |
| the five state-facing conditions `hkeys`, `haxpre`, `hblk`, `hnewc`, `hnewi` | `run_register_inductive_cold_ok` (`ErasureRun.lean:2051`): `IndKernameFresh` gives `hkeys`, `BodylessExt` gives `haxpre`, `registerIndState` gives `hblk`, and the registry report gives `hnewc`/`hnewi` |
| `SpecKeysEmitted pre s₁` | the block key is emitted; the eliminator keys are `RuntimeKey`s of `pre`, so the `consts` clause exempts them |
| `ClosedBodies pre`, `FVarFreeBodies pre` | `mkElimBody`'s own closedness, and a block entry carries no body |

**`ConfigPinned` is a premise**, and F-W8-5 is why: `Erasure.register_inductive` calls
`Erasure.addAxiom` at an `@[extern]` constructor when `cfg.extern = .preferAxiom`
(`Erasure.lean:349-351`), emitting body-less entries at constructor keys the prefix does not
declare, and `ConfigPinned` pins `extern = .preferLogical` (`ErasureSpec.lean:45`). It is
carried by every other unit of this wave, so it costs nothing new. It is also what
`run_register_inductive_cold_entries` needs for `remove_irrel_constr_args`.

**`BlockKeysFresh` is not decidable at a rung as printed**, because `lenv` — and with it
`indinfo` — is universally quantified at every rung. It is decidable at a *table* and one
concrete block, which is the reading `Green.noCasesOnKeys` has at the emitted environment; the
per-rung route is `Supported.indInfo_of_tabled` through `SourceTableAdequate.inds`, which makes
the registered block a tabled one and the check a `decide` over `tbl.inds`. The unit lands the
table-side half and records the block-side half as a premise if that route does not close; a
premise excluding a *named collision* is not the guard rule (2) forbids, F-KERNAME being a
measured property of `toKername` and not a counterexample of this clause.

*Files.* `LeanToLambdaBox/ErasesEnv.lean` (`IndPrefixOf` beside `IndCovered`, `:193`),
`LeanToLambdaBox/ColdStartShape.lean` (`BlockKeysFresh` and the step, beside
`regInv_registerInd_step`, `:1289`), `LeanToLambdaBox/Green.lean` (the per-rung measurement).

*Consumers.* W9-D's `StepAcc3`, `StepAcc10`, `StepAcc17` — `Erasure.visitConstructor`,
`Erasure.visitProj`, `Erasure.visitCases`. Step 6's fourth site is gone with W9-A.
`regInv_registerInd_step`, `SpecContent.append`, `SpecKeysEmitted.append`,
`RegContent.register_inductive_run` and `ErasureSpec.propositionalInd_of_arity` all get their
first consumer here.

*Gate.* `regInv_registerInd_run` closes; `lake exe hygiene --dead` does not grow (both files are
inside the closure); `scripts/ledger.sh` — the new row is `[propext, Classical.choice,
Quot.sound]` or the ladder's 33, any other name a finding; `lake exe green-check --all`.

*Confidence.* This is the wave's largest obligation and the one wave 4 declined twice. Every
ingredient is landed — `regInv_registerInd_step` (W3), `SpecContent.append` (W3), the two
`run_register_inductive_cold_*` decompositions, `BlockAdequate`'s eight fields (W6) — and the
risk is the `IndBodyOf` bridge between `run_register_inductive_cold_entries`' constructor-mask
report and `IndCovered.block`'s `oib.ctors.map (·.nargs) = nfs`, which no theorem crosses today.
`pass_kernelFields_at` is the intended bridge.

*Probe.* `scratch/round7/w9_sigs.lean` §B (three declarations).

### 2.4 W9-C — W5b, the block exit at a growing environment

The non-recursive exit is landed (`regInv_constCons_step`, W5) and the body-less exit is
landed (`regInv_addAxiom_step`, W5). What is left is the block exit, and it is not a fold of
`regInv_constCons_step`: member `i`'s `Lower` fact is `Lower.fixEta_of_block`, whose
`LowerBlock.hdecl` needs *every* member declared, so the specification environment must gain
the whole prefix **before** the state fold — as `RegInvShape'.recConst`
(`ColdStartShape.lean:500`) already has it. The two missing halves are the `RegContent` and
`SpecKeysEmitted` analogues:

```lean
theorem RegContent.recConst (C : RegContent env bo lp (pre ++ Γ) s)
    (hblk : LowerBlock (pre ++ Γ) kns bs bs' ids defs)
    (hbo : ∀ (c : Name) (b : Expr) (j : Nat), bo c = some b → kns[j]? = some (toKername c) →
      j < bs.length → Erases env (lp c) [] b bs[j]!)
    (hidx : ∀ p ∈ names.zipIdx, kns[p.2]? = some (toKername p.1))
    (hfs : ∀ c ∈ names, ∀ q ∈ s.gdecls, q.1 ≠ toKername c)
    (hnd : (names.map toKername).Nodup) :
    RegContent env bo lp (pre ++ Γ) (recConstState names defs s)

theorem SpecKeysEmitted.recConst (K : SpecKeysEmitted Γ s)
    (Kpre : SpecKeysEmitted pre (recConstState names defs s)) (hg : SpecGrow Γ (pre ++ Γ)) :
    SpecKeysEmitted (pre ++ Γ) (recConstState names defs s)

/-- **`visitMutual`'s block exit, declaring what it registers.** -/
theorem regInv_recConst_step (A : RegAcc env bo lp Γ s)
    (hpre : SpecContent env bo lp pre) (hfresh : ∀ p ∈ pre, ∀ q ∈ Γ, p.1 ≠ q.1)
    (hcl : ClosedBodies pre) (hfv : FVarFreeBodies pre)
    (hdenv : ConstsDeclaredEnv (pre ++ Γ))
    (hkpre : SpecKeysEmitted pre (recConstState names defs s))
    (hblk : LowerBlock (pre ++ Γ) kns bs bs' ids defs)
    (hbo : ∀ (c : Name) (b : Expr) (j : Nat), bo c = some b → kns[j]? = some (toKername c) →
      j < bs.length → Erases env (lp c) [] b bs[j]!)
    (hidx : ∀ p ∈ names.zipIdx, kns[p.2]? = some (toKername p.1))
    (hfs : ∀ c ∈ names, ∀ q ∈ s.gdecls, q.1 ≠ toKername c)
    (hnd : (names.map toKername).Nodup) :
    SpecGrow Γ (pre ++ Γ) ∧ RegAcc env bo lp (pre ++ Γ) (recConstState names defs s)
```

`pre` here is the block's own member entries, each `(toKername c, .constantDecl ⟨some bs[j]!⟩)`
at the erasure `hbo` names; `hbo` is what `StepAcc6` reads off the member sub-runs through
`visitMutual_member_erases_block` (W4). `SpecGrow.of_fresh` needs no eliminator-side condition
here: `notElimBody_etaFix` is about the emitted side and the prefix entries are erasure images,
so `erases_ne_elimBody` is the fact that applies (F-W8-3).

`RegInvShape'` is already paid: `H.specGrow` at the appended environment followed by
`RegInvShape'.recConst`. The step's shape is deliberately `regInv_registerInd_step`'s — prefix,
freshness, closedness, then the accumulator at the appended environment — so that `StepAcc6` has
one composition to make at all three of its exits.

*Files.* `LeanToLambdaBox/ColdStartShape.lean` (the three theorems, beside
`regInv_constCons_step`, `:1238`).

*Consumers.* W9-D's `StepAcc6`, block branch.

*Gate.* the three theorems close; `scripts/ledger.sh` — three names, no `sorryAx`; `lake build`.

*Confidence.* High on shape, medium on `hbo`'s arithmetic. `RegInvShape'.recConst` is the
precedent and its fold lemma (`regInvShape'_foldl_recConstStep`, `:463`) already threads
freshness and `Nodup` exactly this way; the risk is the index bookkeeping between `names.zipIdx`,
`kns` and `bs`, which the `RegContent` half reads at a second list the shape half does not.

*Probe.* `scratch/round7/w9_sigs.lean` §C (three declarations).

### 2.5 W9-D — W5c, the accumulator conjunct, in its own induction

`scratch/round7/W5-report.md` §2 mechanised that the accumulator cannot be *fused* into
`RunRefines`' fourth conjunct (`w5_probe.lean`, `runRefines_fused_not_composable`), and
restated it as an independent fifth conjunct of the relation. **This wave takes one step
further: the conjunct mentions no term, no `Lower` and no `SpecEnv`, so it does not belong in
the relation at all.** It goes in its own bundle of eighteen motives, proved by a second
instance of `Erasure.visitExpr.mutual_fixpoint_induct` that consumes the first bundle's
conclusion. `RunRefines`, `RunRefinesAlt`, `HeadRefines`, `Motive1`…`Motive18` and all eighteen
step lemmas are then **unchanged**, which is what makes the change stageable and what keeps T8's
footprint fixed.

```lean
/-- The accumulator along a sub-run: an extension of the specification environment carrying
the triple from the entry state to the exit state. No term occurs. -/
def AccGrows (env : VEnv) (tbl : SourceTable) (s s' : ErasureState) : Prop :=
  ∀ Γ₀, RegAcc env tbl.body? tbl.levels? Γ₀ s →
    ∃ Γ₁, SpecGrow Γ₀ Γ₁ ∧ RegAcc env tbl.body? tbl.levels? Γ₁ s'

theorem AccGrows.trans (h : AccGrows env tbl s s') (h' : AccGrows env tbl s' s₂) :
    AccGrows env tbl s s₂

/-- **The aggregation.** `11-REPAIRS-W8.md` §2.5's printed statement, at `RegAcc`. -/
theorem visitExpr_regInv_all (P : ∀ Us, ErasureSpec lenv env Us gw)
    (E : EraserAsks lenv env gw) (U : UpstreamAsks env)
    (htbl : SourceTableAdequate lenv tbl) (hsafe : TableSafe lenv tbl)
    (hblk : TableBlocks lenv env tbl) (hcb : CompilerBodies lenv env tbl.body?)
    (hcfg : ConfigPinned ctx.config) (hsup : Supported env tbl e)
    (hS : SchemeNames lenv) (hrp : TableRecPrefixed tbl) (hcas : NoTabledCasesOnBody tbl)
    (hvis : Erasure.visitExpr e s ctx cctx ref w = .ok (t, s') w') :
    AccGrows env tbl s s'
```

`MotiveAccᵢ f` is `(∀ …, AccGrows env tbl s s') ∧ f ⊑ Erasure.visitXxx`, one per member, with
the premises of `Motiveᵢ` dropped except those the registering exits read (`BridgeInv`,
`Supported`, `(tbl.decl? n).isSome` at members 5 and 6). `StepAccᵢ` is the matching interface and
`motives_of_steps_acc` the second induction; its admissibility obligations are the same
`admissible_and_le` toolkit the first uses.

**What each step owes.**

| steps | what they do | who pays |
|---|---|---|
| 1, 2, 7, 8, 9, 11, 12, 13, 14, 15, 16, 18 — `visitExpr`, `visitLiteral`, `visitAppArgs`, `visitLet`, `visitLambda`, `visitApp`, `visitConstApp`, the four η walkers, `visitAlt` | compose sub-runs | pass-through: `AccGrows.trans` and nothing else |
| 4, 5 — `visitConst`, `get_constant_kername` | register through `visitMutual` | pass-through: `MotiveAcc6`'s growth, `AccGrows.trans` on the hit/miss split |
| 3, 10, 17 — `visitConstructor`, `visitProj`, `visitCases` | call `register_inductive` | **growth**: `regInv_registerInd_run` (W9-B), at the already-registered branch `SpecGrow.refl` |
| 6 — `visitMutual` | three registering exits | **growth**: `regInv_constCons_step` and `regInv_addAxiom_step` (landed, W5) at the non-recursive and body-less exits, `regInv_recConst_step` (W9-C) at the block exit, and the two realizer exits refuted by `no_realizer_exit_compiler` (W9-A). `hlow`/`hbo` come from `visitMutual_member_erases`/`_block` (W4), which is where `bridgeInv_member`, `visitMutual_block_mode` and `blockKeyed_install` get their trunk |

`StepAcc6` reads `Motive1 Erasure.visitExpr` — the first bundle's conclusion — as a hypothesis,
transporting its own sub-run along `f ⊑ Erasure.visitExpr` to the shipping function first. That
is the whole of the interaction between the two inductions, and it is why the second one can be
stated and proved in a commit of its own.

**Staging, three commits, each green.**

1. `AccGrows`, `AccGrows.trans`, the eighteen `MotiveAccᵢ`, the eighteen `StepAccᵢ` interfaces
   and `motives_of_steps_acc` with the eighteen steps as hypotheses. Nothing outside the new
   file is touched; `lake build` is green and the battery is unmoved.
2. The eighteen step lemmas: the twelve pass-throughs and steps 4/5 first (one file), then
   3/10/17, then 6. Each group closes against the fixed interfaces.
3. `visitExpr_regInv_all`, the aggregator, beside `visitExpr_refines_erasesLB`.

The merge into one bundle is **not** a later stage and is not planned: the two motives share no
premise, and fusing them is what `w5_probe.lean` refuted.

*Files.* `LeanToLambdaBox/VisitExprRefines/MotivesAcc.lean` (new — the relation, the eighteen
motives and the eighteen interfaces), `LeanToLambdaBox/VisitExprRefines/StepAcc/*.lean` (new —
the eighteen steps, split as the existing `Step/{Mechanical,Passes,Env}.lean` are),
`LeanToLambdaBox/VisitExprRefines.lean` (the second `motives_of_steps` and the aggregator).

*Consumers.* W9-E.

*Gate.* `lake build`; `scripts/erasesLB.sh` green with T8's footprint unchanged — the first
bundle is untouched, so any movement there is a finding; `lake exe hygiene --dead` at 339 (the
new files are inside `Capstone.lean`'s closure only once W9-E lands, so commits 1 and 2 raise
the budget by the count of their declarations and the unit says so in the same commit);
`scripts/ledger.sh` — `visitExpr_regInv_all` at `[propext, Classical.choice, Quot.sound]`.

*Confidence.* Medium-high on the plan, medium on the size. The twelve pass-throughs are four
lines each by construction, the dependency on W9-B and W9-C is stated rather than assumed, and
the separate-bundle shape removes the all-or-nothing obstruction `W5-report.md` §3 measured. The
risk is `StepAcc6`'s block branch, which must run the accumulator through the member sub-runs to
reach the environment `LowerBlock.hdecl` is read at — the ordering `W5-report.md` §2 describes,
and the only step where the two inductions' data meet.

*Probe.* `scratch/round7/w9_sigs.lean` §D (`AccGrows`, `AccGrows.trans`, `visitExpr_regInv_all`;
the relation-level `RunRefinesAcc`/`RunRefinesAltAcc` are displayed there for comparison and are
**not** taken).

### 2.6 W9-E — W7, `erasure_bridge_env` and the binder discharged

```lean
/-- F-W8-7's repair: the side condition at the images that lower to the emitted term.
`ErasuresDeclared` quantified over *every* erasure image is false at the entry term —
`erasuresDeclared_false_at_app` (`scratch/round7/q_w8.lean`), at a boxed constant argument —
so the clause reads the witness the composition actually destructs. -/
def ErasuresDeclaredAt (env : VEnv) (Us : List Name) (Γ : GlobalDeclarations) (Δ : VLCtx)
    (e : Expr) (t : LBTerm) : Prop :=
  ∀ t₀, Erases env Us Δ e t₀ → Lower Γ t₀ t → ConstsDeclared Γ t₀

/-- Every constant of a specification term is declared, given it of the term's `Lower` image:
the `const` arm keeps the key, and the two arms that remove one — `fixConst` at a block member
and `elimApp` at an eliminator — carry its declaration themselves. -/
theorem Lower.constsDeclared_source (h : Lower Γ u v) (ht : ConstsDeclared Γ v) :
    ConstsDeclared Γ u

/-- Every constant the emitted term names is a registered constant's canonical kername. -/
theorem visitExpr_emitted_consts (P : ∀ Us, ErasureSpec lenv env Us gw)
    (hcfg : ConfigPinned ctx.config)
    (hvis : Erasure.visitExpr e s ctx cctx ref w = .ok (t, s') w') :
    ∀ kn ∈ constRefs t, ∃ c : Name, kn = toKername c ∧ (s'.constants.get? c).isSome

theorem bridgeEnv_of_regContentAt (A : RegAcc env bo lp Γspec sf) (hk : RegKeyed env sf)
    (hde : ErasuresDeclaredAt env [] Γspec [] pe t)
    (htab : ∀ c b, bo c = some b → ConstOrigin env c) (hlvl : TabledLevels env bo lp) :
    SpecEnv env bo lp sf Γspec ∧
      ∀ t₀ : LBTerm, Erases env [] [] pe t₀ → Lower Γspec t₀ t →
        ErasureBridge env bo lp Γspec sf.gdecls t₀

/-- **`hbridge`'s shape exactly** (`Capstone.lean:206-210`), at a run of the shipping
`Erasure.visitExpr` from the empty state: `visitExpr_regInv_all` at `RegAcc.coldStart`,
`regKeyed_of_run` at `regKeyed_empty`, then `bridgeEnv_of_regContentAt`. -/
theorem erasure_bridge_env (P : ∀ Us, ErasureSpec lenv env Us gw)
    (E : EraserAsks lenv env gw) (U : UpstreamAsks env)
    (htbl : SourceTableAdequate lenv tbl) (hsafe : TableSafe lenv tbl)
    (hblk : TableBlocks lenv env tbl) (hcb : CompilerBodies lenv env tbl.body?)
    (hcfg : ConfigPinned cfg) (hsup : Supported env tbl pe)
    (hS : SchemeNames lenv) (hrp : TableRecPrefixed tbl) (hcas : NoTabledCasesOnBody tbl) :
    ∀ (sf : ErasureState) (wt : Void IO.RealWorld),
      Erasure.visitExpr pe {} { «config» := cfg } cctx ref wp = .ok (t, sf) wt →
      ∃ Γspec : GlobalDeclarations, SpecEnv env tbl.body? tbl.levels? sf Γspec ∧
        ∀ t₀ : LBTerm, Erases env [] [] pe t₀ → Lower Γspec t₀ t →
          ErasureBridge env tbl.body? tbl.levels? Γspec sf.gdecls t₀
```

`ErasuresDeclared` is **restated in place** — it has exactly one consumer
(`scratch/round7/W4-refute.md` §4.1) — with `erasuresDeclared_false_at_app` recorded in its
docstring and kept as a `test/Vacuity.lean` regression; `bridgeEnv_of_regContent` becomes
`bridgeEnv_of_regContentAt`, weaker by the `Lower` premise it now takes, which is the premise
`hbridge` carries anyway (U9.3's "`Lower` is not spent" is what W8 §2.2 declined and F-W8-7
refutes). The restricted side condition is then discharged, not assumed:
`visitExpr_emitted_consts` with `RegInvShape'.consts` gives `ConstsDeclared Γspec t` at the
emitted term, and `Lower.constsDeclared_source` carries it back to every image that lowers to it.

`hbridge` then leaves `shipping_erase_correct_firstorder` (`Capstone.lean:206-210`) and all eight
rungs (`Green.lean:226`, `:379`, `:480`, `:601`, `:854`, `:975`, `:1572`, `:1633`), replaced at
each by `P`, `hS`, `hrp`, `hcas` and the run equation the rung already has. `hbody` stays at G8.

*Files.* `LeanToLambdaBox/ErasesLB.lean` (`ErasuresDeclared` restated, `:478`),
`LeanToLambdaBox/Lower.lean` (`Lower.constsDeclared_source`),
`LeanToLambdaBox/VisitExprRefines/Step/Passes.lean` (`visitExpr_emitted_consts`),
`LeanToLambdaBox/Capstone.lean` (`bridgeEnv_of_regContentAt`, `erasure_bridge_env`, the
capstone's binder list), `LeanToLambdaBox/Green.lean` (the eight rungs' binder lists),
`test/ledger.expected` (one new row), `doc/trust.md` (the `hbridge` row retired; `SchemeNames`
added as class **D**).

*Consumers.* `shipping_erase_correct_firstorder` and the eight rungs, which is the first time
anything below `bridgeEnv_of_regContent` reaches one.

*Gate.* `grep -rn "\bhbridge\b" LeanToLambdaBox/` empty. `scripts/ledger.sh` — **the 33-name
cluster of `shipping_erase_correct_firstorder` and `green_G1`…`green_G8` must not grow**, and
relocating a binder into a proved term is exactly where it could: `bridgeEnv_of_regContent` and
`bridgeEnv_of_regInv` are at three names today and `visitExpr_regInv_all` inherits whatever the
second induction carries. Any growth is a finding, not a bookkeeping update; the expected file
may gain the `erasure_bridge_env` row and nothing else. Also `lake exe green-check --all` 8/8,
`bash scripts/fixes.sh`, `lake exe hygiene --dead` back at 339 once the W9-D files enter the
closure.

*Confidence.* Mechanical once W9-D lands, except for `visitExpr_emitted_consts`, which is a
further run induction and is the one statement here with no precedent in the tree. Its fallback
is to take it as a clause of `RunClosedW`'s shape half, where `visitExpr_shapeW` already reports
the emitted term's shape at each registering exit.

*Probe.* `scratch/round7/w9_sigs.lean` §E (five declarations).

## 3. What stays open after W9

W9 discharges one class-**C** binder and gives seven zero-consumer components their trunk. It
does not make the capstone unconditional. `doc/rework/07-STATUS.md` §4 is the standing census,
and these rows survive:

* **C — this repository's own code.** `E : EraserAsks`, four fields, `kernel_ind_head_true`
  bounded by F-DEPTH's residue. `hbody` at G8: every erasure of `benchArith`'s tabled body
  reaches `Nat`'s block — strengthened by W7/U9, satisfiable, not refutable, not closed here.
  `BlockKeysFresh` at a run, if W9-B's tabled-block route does not close it.
* **D — Lean's `Meta`/`Core` primitives.** `P : ∀ Us, ErasureSpec lenv env Us gw`, seven fields,
  `block_adequate` now eight; `htbl`, `hsafe`, `hblk`, `hprep`, `hrun`; and **two new fields**,
  `SchemeNames.quot` and `.recr`. Nothing in the tree constructs any of them, so they are
  assumptions in the sense `scratch/round7/W4-refute.md` §4.3 names — with the difference that
  these land with their reader.
* **U — upstream lean4lean.** `A : UpstreamAsks`, four fields; `hcb : CompilerBodies` at G2–G8,
  blocked on `TrProj`, entirely unproven at the pin; the sixteen inherited `sorryAx` roots and
  the 29-name executable-checker cluster.
* **R — scope.** `hsup : Supported`, and this wave leans on it harder: §1.1 makes the realizer
  exits a *coverage* statement, so the shipping eraser's F-QUOT/F-EQREC paths are verified by
  nothing and `doc/coverage.md`'s realizer census is the only place they are measured. `hev`,
  constructed at G5 alone. `TableSafe.noMaxLevels`. The first-order shape of the observable.
* **The α gap** (`ReifiedDecl.Prepared` pins a tabled body only up to `Expr.AlphaEq`; five of
  G7/G8's bodies match only up to binder names) — W4's transport is what covers it and W9-C is
  the first unit to spend it at a block.
* **`Lower` is not a function** at a block member (`W2-refute.md` R3/R4), a recorded cost of
  F-ETA; nothing assumes it is.
* **Coverage.** Sieve, BinaryTrees, Quicksort and Fannkuch stay outside the fragment at
  F-EQREC, F-SPARSE and `etaContractedMinor`; discharging `hbridge` moves no coverage row.
* **F-PRODUCT**, `auto_inline_typeclass_dispatch` — the one shipping finding not meant to be
  fixed, off by default, class **E** in `doc/trust.md`.

One item from `scratch/round7/W4-refute.md` §7 is **not** carried: item 3, "reprice W6". W9-A and
W9-D give `regKeyed_of_run` and `BlockAdequate`'s two new fields their reader, so they stay.
Item 5, `ErasureSpec.propositionalInd_of_arity`, gets its first consumer at W9-B.
