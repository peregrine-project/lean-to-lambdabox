# 04 — Wave-2 amendment: one relation, one simulation, at the emitted environment

Amends `01-DESIGN.md` (§3 decisions, §4 signatures, §5 theorems) and `02-PLAN.md` (W2 remainder,
W3) after Wave 2 machine-refuted both halves of the design's composition strategy, and after two
refuters machine-refuted the first cut of this amendment. Every claim below is grounded in a
delivered refutation, in the code at `dev/verify`, or in a measurement named with its command.
`00-REFERENCE-SPEC.md` amendments A17–A22 are requested in §10.

**Revision note.** §§3–6 differ from the first cut in four load-bearing ways: `CtorDecl` and the
constructor disjunct of `RuntimeKey` are **deleted** (they made the composite uninhabitable on all
five programs); `SEval`'s value arms are keyed on `CtorOf`/`IndInfo` — `[S Fig. 12]`'s
`value_head` — which **removes** the `axiom_free` premise instead of adding one; both η arms of
`Lower` are **deleted** and N19 becomes a fragment restriction rather than a re-keying; and the ι
arm's spine split is pinned by source-theory data (`CasesOnShape`) rather than asserted.

---

## 1. What Wave 2 settled

| # | Design text | Verdict | Evidence |
|---|---|---|---|
| W2-R1 | T5 (`erases_correct`) at `Σ⁺`, ι arm | **false**: `SEval.ctorVal` makes a constructor constant its own value, the ten-rule `Erases` relates that value only to `.const kn` or `.box`, and `Σ⁺` gives the kername the body `.construct iid k []`, which `WcbvEval` unfolds eagerly | `erases_correct_needs_tabled_ctor`, `erases_const_ne_construct` (`ErasesCorrect.lean:808`) |
| W2-R2 | T5's five hypotheses | **false** at a declared, untabled constant: the target is stuck at a body-less declaration | `erases_correct_needs_tabled` |
| W2-R3 | `hΣ : ErasesEnv env bo Σ⁺ t` delivers the δ arm's premise | **false**: program-keyed, and `decls` runs the direction opposite to the arm's | `erasesEnv_not_deltaAgrees` |
| W2-R4 | T6 (`lower_correct`) over all 17 arms | **false** at `elimEta` with an `ElimBody`-shaped head, at `Σ⁺ = Σ = []`, with every design guard proved in the same statement | `lower_correct_needs_elimBody_head` |
| W2-R5 | `LowerNoEta` as a guard | **vacuous**: it forces `cstrArity Σ iid k = 0` for every declared constructor, so it is false on every environment reaching `Nat.succ` | `lowerNoEta_forces_nullary_ctors`, `lowerNoEta_fails` |
| W2-R6 | `elimApp` inside a `WcbvEval` induction | out of reach: at a saturated eliminator spine the derivation's top rule is `beta` at the last minor, whose IH sees neither the discriminant's evaluation nor the selected minor's application | U2.1 obstruction 2 |

W2-R1 to W2-R3 say the simulation cannot be proved at `Σ⁺`; W2-R4 to W2-R6 say it cannot be
transported from `Σ⁺` to `Σ` along `Lower`. Together they retire the two-simulation architecture,
not a lemma in it.

What stands and is carried unchanged: the composite `ErasesLB` and its seventeen introduction
lemmas (U2.2), the βζδ+lit fragment of the simulation and its supporting metatheory (U2.3:
`Erases.defeqDFC_wt`, `erases_subst_let`, the `WcbvEval` spine kit), `LowerFix.constToFix` (U1.7),
one `SEval` with subject reduction (U1.4), `IotaBridge` (target-side, `sorryAx`-free), `Fuel.lean`,
T9 with its single `hbridge` binder (`Capstone.lean`), `green_G1`.

---

## 2. What the amendment's own refuters settled

Ten findings at severity ≥ medium. Each is answered below by a change, not by an excuse; the two
that are *not* changes are marked.

| # | Finding | Disposition |
|---|---|---|
| **A-F1** | The eleventh rule makes `Unit.unit`'s `Σ⁺` body a `.construct`, hence a `CtorDecl`, hence a `RuntimeKey`, and `Lower.target_const` (proved) then forbids the node the eraser emits at its every use site — 2/11/9/16/20 sites in the five programs. The composite becomes uninhabitable, which the ten-rule relation was not | **`CtorDecl` and `RuntimeKey`'s constructor disjunct are deleted** (§7). `Unit.unit` is a *definition* whose compiler body is `PUnit.unit`; with `ctorApp`/`ctorEta` gone, `CtorDecl` has no consumer left. `ErasesDecl.ctor` is deleted with it — it requires `CtorOf`, so it never could justify that entry (§8). Machine-checked: `scratchpad/amend/r1_unit.lean` |
| **A-F2** | `AxiomFree Σ t` and the `constRefs` extension are jointly unsatisfiable: a block kername resolves to an `.inductiveDecl`, never to a bodied `.constantDecl`. G1 itself fails `AxiomFree` once blocks are tracked; and `AxiomFree` has no `Decidable` instance as printed | **`AxiomFree` is deleted, not repaired** (§5, §8). Keying `SEval`'s value arms on `CtorOf`/`IndInfo` makes a body-less plain constant have *no source value*, exactly as PCUIC's `value_head` does, so W2-R2's counterexample has no `hev` and the premise has no work to do. The `constRefs` extension lands unopposed. Machine-checked: `scratchpad/amend2/r1_axiomfree.lean` |
| **A-F3** | A18's fidelity claim is wrong: MetaRocq's `erases_correct` has **five** hypotheses and `axiom_free` is not among them; the extra premise papers over `SEval.ctorVal`, a rule PCUIC's `value_head` does not have | **Accepted in full**; it is the repair of A-F2. A18 now reads "MetaRocq's five plus `LowerEnv`" — seven binders, six premises — and the departure is removed at its source rather than compensated |
| **A-F4** | Step 4's inversion is false as written: a constructor-headed value's composite image admits `mkApps (mkLambdas ns …) cargs'` (`ctorEta`) and `mkApps (.fix defs j) cargs'` (`fixBody`) besides `.box` and the constructor spine | **Both are closed, by deletion and by a named premise** (§6 step 4): the η arms are gone, so the first shape is not in the relation; the second is excluded by `BlockBodiesLambda Σ⁺`, now a clause of `LowerEnv` (§8) rather than an unbound assumption |
| **A-F5** | `SEval.iota`'s `hmins`/`hpres` have no counterpart in PCUIC's `eval_iota`; they narrow the source relation and must be declared a coverage restriction | **Accepted and declared: restriction N20** (§5). Kept, because the boxed-prefix case genuinely needs them (§6 step 2) — the delta is forced by Lean spelling elimination as an application spine, where `Erases.box` can sit at a proper prefix, while Rocq's `tCase` is one node. Measured mitigation: Lean's match compiler thunks nullary branches (`Nat.pred`'s zero branch in `Arith.ast` is `tLambda "_" …` applied to `tConst Unit.unit`), so the `match` fragment is unaffected; direct `casesOn`/`rec` uses with an unthunked diverging minor are outside |
| **B-F1** | The two printed changes to axiom-freedom are jointly false on the existing green rung G1 | same as A-F2: `AxiomFree` deleted |
| **B-F2** | T5's premise list cannot support the `Lower` metatheory it consumes: `Lower.subst_comm` needs `ClosedBodies Σ⁺` and the whole `Lower.source_*` kit needs `BlockBodiesLambda Σ⁺`; neither is a binder and no clause supplies them | **`LowerEnv` gains `specClosed : ClosedBodies Σ⁺` and `specBlocks : BlockBodiesLambda Σ⁺`** (§8), and A18 prints them: the pass layer's environment well-formedness is what `LowerEnv` carries, the way `wf Σ` carries the source's. Binder count unchanged; the premise count is stated honestly as "MetaRocq's five, plus `LowerEnv` with four environment clauses" |
| **B-F3** | The ι arm's head step is asserted: nothing ties the source ι split to the target's `dp`/`nfs` (R3, never consumed); `ElimDecl` implies `DefnDecl`, so `fixConst` is *not* excluded by disjointness; the only existing carrier of the split is `supportedHead`, which criterion 6 forbids | **Three changes** (§5, §6 step 3, §7): `SEval.iota` gains `hsh : CasesOnShape env con I pre.length minors.length` and `hct : CtorOf env ctor I cidx` — the source theory's own segmentation, read off the inductive declaration, as Rocq reads it off `tCase`'s syntax; `ErasesDecl.elim` gains the same `CasesOnShape` at the target's `dp`/`nfs.length`; and `Lower.fixConst` gains `¬ RuntimeKey Γ kn`. The agreement lemma is `CasesOnShape.inj`, from upstream ask 2 |
| **B-F4** | W2's second half is not executable as four units on disjoint files, and it breaks the standing green obligation by construction; the deletion table puts `LowerCorrect.lean`'s demolition in W3 while naming a W2 unit as its deleter | **W2's second half is re-cut into five units** (§11): `U2.9` (demolition and relocation) is scheduled **first**, `U2.7` owns `Lower.lean`, `LowerFix.lean`, `LowerCorrect.lean` **and** `ErasesLB.lean`, and the deletion table's `LowerCorrect` row moves to W2 |
| **B-F5** | Relocations and one named prerequisite have no owning unit; the `WcbvEval` closedness-preservation lemma does not exist anywhere | **`U2.9` owns them** (§11), including `Closed.lean` and `Semantics/Metatheory.lean`. (`Semantics/Metatheory.lean` exists and already proves `eval_to_value`; the missing lemma is only the `LBClosed` one) |
| **B-F6** | U3.1's acceptance is unreachable inside its dependencies — a cycle between the aggregator and its two arm units | **Accepted**: U3.1 is restated as W4's U4.1 is, with the ι/proj/δ steps as **explicit hypotheses** of the aggregator; G3 instantiates them (§11) |
| **B-F7** | The eleventh rule's negative premises make `consts_origin` load-bearing at every `.const` introduction, while R4 still calls it inconsequential | **The premise is turned positive**: `Erases.const` takes `ConstOrigin env c` — the defining declaration *exhibited*, symmetric to `CtorOf` and `IndInfo` (§4). Introduction is then a fixture fact, needing no upstream lemma, which is what keeps `green_G1` green through W2. The *exclusion* direction moves to upstream ask 2, consumed as a theorem by T7 and by §6 step 3 only (R4 refreshed) |
| **B-F8** | `ErasableAxioms`/`AxiomRealizer` is carried although nothing consumes it, and the design does not say which premise T9 carries | **Both are deleted, and T9 drops `hax`** (§8). With the value arms keyed, an axiom-reaching run simply has no `SEval` derivation — PCUIC's own answer. The `Eq.rec`/`False.rec` rows become a `doc/coverage.md` row (F-EQREC), which is what they always were |
| **B-F9** | `hne : ∀ I, ¬ CasesOnOf env I …` imports a name registry into the source-side value relation | **Dissolved**: with `ctorVal` keyed on `CtorOf`, a `casesOn` spine is not a value for a structural reason, so `hne` *and* `hpat` are deleted (§5) |
| **B-F10** | §4's elaboration evidence did not test the printed statement | **Re-probed**: `scratchpad/amend/p3_w2rev.lean` elaborates `ConstOrigin`, `CasesOnShape`, `RuntimeKey'` and the amended `erases_correct` (seven binders, no `hax`) against the tree as it stands; `lake env lean`, exit 0 |
| **B-F11** | U3.2's 900 lines is optimistic against the 6,823-line retired ι group and the 2,561-line `LowerCorrect.lean` | **Re-priced to 1,600** and split: `U3.2` (ι) and `U3.2b` (proj) (§11). The spine-inversion work it cited is smaller than it was, because the η arms are gone and the app-congruence reading at an `ElimDecl` head is now *impossible* rather than a case (§6 step 3) |

Two findings are recorded as **not fatal and not changed**: the correction that 982/982
`tConstruct` nodes carry an **empty argument list** (not that all are under a `tApp`) is adopted
verbatim in the wording of §4 and §8; and the observation that `Erases`'s non-determinism admits
several images of one term is intended — the theorem is proved for every derivation, which is what
makes the relation a specification.

---

## 3. The decision, in eight lines

1. **`Erases` distinguishes the three readings of `Expr.const`** — constructor, inductive type
   name, plain constant — as Rocq's syntax does with `tConstruct`, `tInd`, `tConst`. Eleven rules
   (§4).
2. **`SEval`'s values are `[S Fig. 12]`'s `value_head`**: a constructor spine and an
   inductive-type-name spine are values, sorts and Π-types are values, and nothing else
   constant-headed is. A body-less plain constant has no value, so no axiom-freedom premise is
   needed anywhere (§5).
3. **One load-bearing simulation**, on the composite `Erases ⨟ Lower`, **at the emitted `Σ`**,
   proved by one induction on `SEval` with each arm a named step lemma (§6).
4. **`Σ⁺` survives as the pass layer's metadata environment**; its *evaluation* theory goes (§9).
5. **`Lower` is fourteen arms**: `ctorApp` becomes `Erases.ctor`, both η arms are deleted (their
   coverage is restriction **N19**, shipping finding **F-ETA2**), `ElimHeadOf` is deleted,
   `ElimDecl` carries its block, `fixConst` is guarded (§7).
6. **The environment relation carries what the arms consume**: `erases_deps`' δ clause, the
   eliminator's source-side segmentation, and the pass layer's environment well-formedness (§8).
7. **Two upstream asks, both already filed**, replace `IotaRelevant`: `IsDefEqU.const_arity_inv`
   and `WF'.consts_origin`. Both are consumed as *theorems*; no rung carries a binder (§9).
8. **The fragment declares what it excludes**: N19 (no under-applied constructor or eliminator
   occurrence) and N20 (every ι spine's dropped prefix and unselected minors have values), each
   decided or measured per program, each paired with a shipping finding where one exists.

---

## 4. `Erases` — the three readings of `Expr.const`

```lean
  /-- `[S Fig. 18]`'s `tConstruct` congruence at the bare head: a constructor constant erases to
      its λ□ constructor node, and its arguments arrive through `app` — applied form, so
      `.construct` carries no arguments (§3.1 Q5; measured: 982/982 `tConstruct` nodes in
      `VerifyBench/ast/*.ast` carry an empty argument list). -/
  | ctor  {Δ c us I iid k np nfs} (hc : CtorOf env c I k) (hi : IndInfo env I iid np nfs) :
          Erases env Us Δ (.const c us) (.construct iid k [])
  /-- Rocq's `tConst`: a constant declared as a *definition*, an opaque constant or an axiom.
      `ConstOrigin` exhibits the declaration, exactly as `CtorOf` and `IndInfo` do for the other
      two readings — a positive premise, so every introduction site (the rungs, T8's bridge) can
      discharge it from the declaration list it already has. Rocq needs no premise here because it
      writes the three readings as three nodes. -/
  | const {Δ c us ci} (hc : env.constants c = some ci) (ho : ConstOrigin env c) :
          Erases env Us Δ (.const c us) (.const (toKername c))
```

```lean
/-- Does this declaration introduce `c` as a plain constant? -/
def VDeclDefines : VDecl → Name → Prop
  | .axiom cv, c => cv.name = c   | .def dv, c => dv.name = c
  | .opaque dv, c => dv.name = c  | .example dv, c => dv.name = c
  | .mutualDef dvs, c => ∃ dv ∈ dvs, dv.name = c
  | .quot, _ => False             | .induct _, _ => False

/-- The third reading of `Expr.const`, read off a declaration list of `VEnv.WF'` below `env` —
the same reading `CtorOf` (`ErasesEnv.lean:77`) and `IndInfo` (`Erases.lean:44`) take. -/
def ConstOrigin (env : VEnv) (c : Name) : Prop :=
  ∃ ds env₀ d, VEnv.WF' ds env₀ ∧ d ∈ ds ∧ env₀ ≤ env ∧ VDeclDefines d c
```

Both elaborate against the tree (`scratchpad/amend/p3_w2rev.lean`, exit 0). The other nine rules
are unchanged; `.case` and `.fix` remain absent (criterion 2 survives for them, A17).

Consequences, each checked against the code:

* **An inductive type name has no image but `.box`.** `Nat` as a term is `env.constants`-declared,
  so the ten-rule `const` sent it to `.const (toKername Nat)` — a kername the eraser emits only as
  an `.inductiveDecl`, on which `WcbvEval.delta` is stuck. `ConstOrigin` excludes it by the same
  mechanism that excludes constructors. MetaRocq has no `erases` rule for `tInd` for the same
  reason: a type is erasable.
* **Uniqueness (T7) needs no origin theorem at a first-order value.** At `.const c us` with
  `CtorOf env c I k` in hand, a competing `const` derivation supplies `ConstOrigin env c`, and
  upstream ask 2's `constOrigin_not_ctorOf` closes it. The same corollary is the *only* thing §6
  step 3 needs, so the ask has exactly two consumers.
* **`ErasesDecl.ctor` is deleted** (§8): it requires `CtorOf`, and the one constructor-bodied
  declaration in the five programs — `Unit.unit ↦ tConstruct PUnit 0` — is a *definition* whose
  compiler body is `PUnit.unit`, justified by `ErasesDecl.defn` through the new `ctor` rule. The
  only path that would emit a genuine constructor declaration is `visitConstructor`'s
  `isExtern ∧ extern == .preferAxiom` branch (`Erasure.lean:739`), which is out of fragment and is
  named as such in `doc/coverage.md`.
* **`erases_const_ne_construct` and `erases_correct_needs_tabled_ctor` are deleted**: the first is
  refuted by the new rule, the second is the refutation this amendment answers.

---

## 5. `SEval` — `[S Fig. 12]`'s `value_head`, and call-by-value ι

```lean
  /-- `value_head_cstr`: a constructor spine is a value once its arguments are. Keyed on the
      source theory's classification, not on the compiler table and not on a name test. -/
  | ctorVal {Δ cn us I k args argsv} (hc : CtorOf env cn I k)
      (hlen : argsv.length = args.length)
      (hargs : ∀ i, i < args.length → SEval env bo Us fl Δ args[i]! argsv[i]!) :
      SEval env bo Us fl Δ (mkApps (.const cn us) args) (mkApps (.const cn us) argsv)
  /-- `value_head_ind`: an inductive type name applied to arguments is a value. Not optional —
      `deltaC` and `ctorVal` evaluate their arguments, and a polymorphic call's type argument is
      exactly this shape (`@List.length Nat xs`). -/
  | indVal {Δ cn us iid np nfs args argsv} (hi : IndInfo env cn iid np nfs)
      (hlen : argsv.length = args.length)
      (hargs : ∀ i, i < args.length → SEval env bo Us fl Δ args[i]! argsv[i]!) :
      SEval env bo Us fl Δ (mkApps (.const cn us) args) (mkApps (.const cn us) argsv)
  /-- Types are values: weak evaluation does not enter a binder, and both shapes erase to `.box`. -/
  | sort {Δ u} : SEval env bo Us fl Δ (.sort u) (.sort u)
  | forallE {Δ n ty b bi} : SEval env bo Us fl Δ (.forallE n ty b bi) (.forallE n ty b bi)
  /-- ι, call-by-value in the **whole** spine, and split where the source theory splits it.
      `hsh` and `hct` are the data Rocq's `tCase` carries in its syntax: how many arguments
      precede the major premise, how many minors follow it, and which minor the matched
      constructor selects. Without them nothing ties this derivation's split to the `.case` node
      the eraser emits (B-F3). `hpres`/`hmins` are restriction **N20**. -/
  | iota {Δ con us I pre prev disc minors minorsv ctor cus cargs np cidx r} (hfl : fl.iota)
      (hsh : CasesOnShape env con I pre.length minors.length)
      (hct : CtorOf env ctor I cidx)
      (hpre : prev.length = pre.length)
      (hpres : ∀ i, i < pre.length → SEval env bo Us fl Δ pre[i]! prev[i]!)
      (hdiscr : SEval env bo Us fl Δ disc (mkApps (.const ctor cus) cargs))
      (hmin : minorsv.length = minors.length)
      (hmins : ∀ i, i < minors.length → SEval env bo Us fl Δ minors[i]! minorsv[i]!)
      (hidx : cidx < minors.length)
      (hdef : StepDefeq env Us Δ (mkApps (.const con us) (pre ++ disc :: minors))
        (mkApps minors[cidx]! (cargs.drop np)))
      (hcont : SEval env bo Us fl Δ (mkApps minors[cidx]! (cargs.drop np)) r) :
      SEval env bo Us fl Δ (mkApps (.const con us) (pre ++ disc :: minors)) r
```

```lean
/-- The `casesOn` of `I`, at the segmentation `I`'s own block fixes: `dp` arguments before the
major premise (parameters, motive, indices), then one minor per constructor. Read off the
inductive declaration, as `CtorOf`/`IndInfo` are. -/
def CasesOnShape (env : VEnv) (c I : Name) (dp nm : Nat) : Prop :=
  isCasesOnName c = true ∧ c.getPrefix = I ∧
  ∃ ds env₀ decl t, VEnv.WF' ds env₀ ∧ VDecl.induct decl ∈ ds ∧ env₀ ≤ env ∧
    t ∈ decl.types ∧ t.name = I ∧
    dp = decl.nparams + 1 + (t.type.piArity - decl.nparams) ∧ nm = t.ctors.length
```

`ctorVal` loses `hnb`, `hpat` and `hne`: with the classification premise, a `casesOn` spine is not
a value because `casesOn` is not a constructor — a structural reason, not a name test (B-F9).
`SEval.mono`, `SEval.le` and `SEval.defeq` re-prove arm by arm; the two new value arms are
`TrExprS`-reflexive and the ι case of `defeq` spends `hdef` and the `hcont` IH, which the new
premises do not touch.

**What it costs, declared.**

* **N20** — every ι spine's dropped prefix and unselected minors have values. PCUIC's `eval_iota`
  evaluates neither, because Rocq's `tCase` is one node; Lean spells elimination as an application
  spine, so `Erases.box` can sit at a proper prefix of it and the target's `app_box` evaluates the
  arguments it discards (`Semantics/Eval.lean:97`, MetaRocq's `eval_box` likewise). §6 step 2 is
  the only consumer. Decidable sufficient condition for a rung: every prefix argument and every
  minor is already a syntactic value (a λ, a literal, a sort, a Π, or a constructor spine).
  Measured: Lean's match compiler thunks nullary branches, so the `match` fragment is unaffected;
  a hand-written `Nat.casesOn n a f` with an unthunked diverging `a` is outside.
* **What it does not cost.** A body-less plain constant now has no value at all. That is not a new
  restriction — it is PCUIC's treatment of an axiom, and it is what deletes `AxiomFree` (A-F2).

---

## 6. The load-bearing simulation

One theorem, one induction, at the emitted environment. `ErasesCorrect.lean` owns the statement,
the aggregator and the structural arms; `ErasesCorrect/Iota.lean`, `ErasesCorrect/Proj.lean` and
`ErasesCorrect/Delta.lean` own the hard arms as step lemmas taking the induction hypothesis as a
parameter — the shape W4 already uses for its eighteen motives, and what lets the units work on
disjoint files.

```lean
/-- **The forward simulation.** `[S §7.3]`'s `erases_correct`, transposed to Lean and stated of
the composite at the *emitted* environment. Proved by one induction on `hev`, each arm a step
lemma of `ErasesCorrect/`. -/
theorem erases_correct
    {env : VEnv} {bo : Name → Option Expr} {Us : List Name} {fl : SEvalFlags}
    {Γspec Γ : GlobalDeclarations} {e v : Expr} {ve : VExpr} {t₀ t : LBTerm}
    (henv  : env.WF)
    (hwt   : TrExprS env Us [] e ve)
    (hev   : SEval env bo Us fl [] e v)
    (her   : Erases env Us [] e t₀)
    (hlow  : Lower Γspec t₀ t)
    (hspec : ErasesEnv env bo Γspec t₀)
    (henvL : LowerEnv Γspec Γ) :
    ∃ v₀ v', Erases env Us [] v v₀ ∧ Lower Γspec v₀ v' ∧ WcbvEval Γ eraseFlags t v'
```

Seven binders carrying six premises — `her`+`hlow` is `ErasesLB env Us Γspec [] e t` unfolded so
that `hspec` can name the middle term; the folded form is the corollary `erases_correct_lb`.
**Exactly MetaRocq's five**, plus one: `henv` = `wf Σ`; `hwt` = `welltyped`; `hev` = the
evaluation; `her`/`hlow` = `erases` (the composite is the design's own T6 addition); `hspec` =
`erases_deps`; and `henvL` = `LowerEnv`, which MetaRocq has no analogue of because it has no pass
layer, and which carries the pass layer's environment well-formedness as clauses
(`specClosed : ClosedBodies Γspec`, `specBlocks : BlockBodiesLambda Γspec`, §8) rather than as
extra binders. No `axiom_free`. None is named `Supported`, `Relevant`, `Iota*`, `*Consistent` or
`*Hyps` (criterion 6, as amended by A18). The statement elaborates against the tree as it stands
(`scratchpad/amend/p3_w2rev.lean`, `lake env lean`, exit 0).

**What becomes a lemma of it, and what is retired.**

| Wave-2 deliverable | Fate |
|---|---|
| `erases_correct_tabled` / `_ctx` (U2.3) | the β/ζ/δ/lit/box arms **become the step lemmas**; the statement is retired (its `TabledConstants` guard is answered by §5's value arms, not replaced by a premise) |
| `Erases.defeqDFC_wt`, `erases_subst_let`, the four `InstLet` helpers (U2.3) | kept, moved to `ErasesAbstract.lean` (U2.9) |
| `WcbvEval.{head_value_of_mkApps, app_congr, mkApps_congr, mkApps_box}` (U2.3) | kept, moved to `Semantics/Metatheory.lean` (U2.9), which already holds `eval_to_value`/`value_final` |
| `erases_mkApps_inv`, `erasable_mkApps` (U2.3) | kept — they are the ι arm's entire case split (steps 1–2) |
| `DeltaAgrees` (U2.3) | retired; its content becomes `ErasesEnv`'s `defns` clause (§8) |
| `lower_correct_plain`, `lowerFix_correct_plain`, `LowerPlain` and its three guards (U2.1) | **retired**: nothing transports along `Lower` any more. The inversion kit, the spine toolkit, `constToFix`, `subst_comm`, `substList_comm`, `fixUnfold` survive **on `Lower` itself** |
| `lower_correct_deltaChain`, `lowerFix_correct_atom` (W1) | retired as statements (both evaluate at `Σ⁺`); `LowerBlock.lambda_of_fixLambda` and `Lower.fixBody` carry their content into the δ arm |
| `LowerNoEta`, `BlockBodiesPlain`, `BlockDefsLambda`, `LowerEnvPlain`, `DeltaChain` | deleted (W2-R5) |
| `EtaSpine` and `lambda_of_fixLambda`'s `hη` premise | deleted — with both η arms gone the conclusion is unconditional (U1.7-b's counterexample is no longer in the relation) |
| `ElimHeadOf`, `mkElimBody_iota_fwd/_bwd`, `wcbvEval_mkLambdas_fwd`, the `mkElimBodyRec` unfolding | deleted — `Σ⁺` is never evaluated. `ElimBody`'s *shape* and its inversion stay |
| `AxiomFree`, `ErasableAxioms`, `AxiomRealizer`, `axiomRealizerNames`/`axiomRealizerB` | deleted (A-F2, B-F8); the `Eq.rec`/`False.rec` rows become `doc/coverage.md`'s F-EQREC row |
| `IotaBridge` | kept and **consumed by the ι arm** exactly as written (step 6) |
| `ErasureBridge.simulate` + `.lowerCorrect` (`Capstone.lean`) | **merge into one field**, `simulate`, whose shape is `erases_correct`'s; T9's proof loses one `obtain` |

**The ι arm, in six steps.** Subject `e = mkApps (.const con us) (pre ++ disc :: minors)`, source
rule `SEval.iota`.

1. **Case split.** `erases_mkApps_inv` (`ErasesCorrect.lean:245`) splits `Erases e t₀` into (a) a
   head erasure with pointwise argument erasures, or (b) a **boxed proper prefix**,
   `t₀ = mkApps .box ts` with the prefix erasable. There is no third case.
2. **Case (b) — the boxed prefix, answered honestly.** `Erases.box` can box a proper prefix of an
   ι redex: if the motive lands in `Prop` or in a sort, `mkApps (.const con us) pre` is a proof or
   a type-former. The whole redex is then erasable — `erasable_mkApps` (`ErasesCorrect.lean:256`)
   iterates the proved `Erasable.app` (`Erasability.lean:179`) along the spine — so the source
   value is erasable too (`SEval.defeq` supplies the translation and the defeq; `Erasable` is
   defeq-invariant) and **both sides box**. The target folds by `WcbvEval.mkApps_box`, whose
   `app_box` **evaluates the arguments it discards**; the values come from the IHs at
   `hpres`/`hmins`/`hdiscr`, and this is the only place they are used (N20). No relevance premise
   appears: the box rule's own `Erasable` witness is the guard, and it is `[S Fig. 18]`'s.
3. **Case (a) — the head.** The head rule is `Erases.const` (the `ctor` reading is refuted by
   `constOrigin_not_ctorOf`, upstream ask 2, from `hsh`'s `casesOn` origin; the box reading is case
   (b) at prefix length 0), so the middle head is `.const (toKername con)`. Now invert `Lower` at
   `mkApps (.const kn) args₀` with `ElimDecl Γspec kn iid np dp nfs`:
   * the **`app`-congruence reading is impossible**, because it would need `Lower Γspec (.const kn) h'`
     and `.const kn` has no image at all: `Lower.const` demands `¬ RuntimeKey`, which `ElimDecl`
     refutes, `fixConst` now demands the same (§7), `ctorApp`/`ctorEta`/`elimEta` no longer exist;
   * so the derivation is **`elimApp`**, and its own split satisfies `pre'.length = dp`,
     `minors'.length = nfs.length`. With `hsh` and `ErasesDecl.elim`'s `CasesOnShape` at the same
     `(con, I)`, `CasesOnShape.inj` gives `pre.length = dp` and `minors.length = nfs.length`, so
     the two spine decompositions coincide and `extra = []`.
   A `.rec`-headed or otherwise unemitted head is excluded by `ErasesEnv`'s `deps` clause, not by a
   new premise.
4. **The discriminant.** The IH at `hdiscr` gives `WcbvEval Γ disc' dv'` with the constructor value
   related to `dv'`. The value's erasure is `mkApps (.construct iid' k []) cargs₀` — the `const`
   reading is refuted by `hct` against `constOrigin_not_ctorOf`, and the `.box` reading by
   `not_erasable_of_informative` (`ErasesDecl.elim`'s `hinf : InformativeInd env I` plus upstream
   ask 6). Its `Lower` image is `mkApps (.construct iid' k []) cargs'`: the congruence arms, plus
   `fixBody` at a `.construct` source, which `specBlocks : BlockBodiesLambda Γspec` refutes (A-F4).
   The same upstream lemma gives saturation, hence `(cargs'.drop np).length = nfs[k]`, and
   `constOrigin`/`IndInfo` injectivity gives `iid' = iid`.
5. **The node's environment facts.** `isPropositionalInductive Γ iid = false` and
   `constructorArity Γ iid k = some (np + nfs[k])` come from `ErasesDecl.ind`'s `IndBodyOf`
   (`ErasesEnv.lean:93`, which already pins `propositional = false`) transported by
   `LowerEnv.inds`; the block is in scope because `ElimDecl` carries it (§7) and because
   reachability tracks blocks (§8).
6. **The branch.** The source continues at `mkApps minors[cidx]! (cargs.drop np)`, whose composite
   image is `mkApps (mkLambdas names body') fields'` — `LowerAlt` peels exactly the λ-telescope
   whose binder count is `nfs[k]`. Apply the IH at `hcont` **to that target**, then rewrite to the
   ι reduct with `wcbvEval_mkApps_mkLambdas_substList` (`IotaBridge.lean`: a β-chain of field
   applications *is* `iota_red`), side conditions from `value_mkApps_construct_args` and the
   closedness kit (`specClosed`, plus U2.9's `WcbvEval.lbClosed`). `WcbvEval.iota` assembles.

No step inverts `ElimBody`, evaluates `Σ⁺`, or needs a spine-generalised motive: the IH is taken at
the *un-contracted* branch application, which is where U2.1's obstruction 2 disappears.

**The proj arm** is steps 4 and 5 with `WcbvEval.proj`: the same discrimination lemma, the same
`propositional = false` fact, and nothing else. It is its own unit (U3.2b) because its `TrProj`
obligation runs through the part of lean4lean's `Verify` layer that is entirely unproven
(`doc/trust.md`).

**The δ arm, including recursion.** `SEval.deltaC` evaluates its arguments, so the IHs give their
target values. `ErasesEnv.defns` supplies `Erases (b.instantiateLevelParams ups us) b₀` for the
tabled body and `LowerEnv.defs`/`defsTotal` supply the emitted body. Two target shapes:
`Lower.const` (δ at `Γ`, then `wcbvEval_mkApps_head_congr` and `WcbvEval.mkApps_congr` replace head
and arguments), and `Lower.fixConst` (empty spine: `fix_atom` + `Lower.fixBody` +
`LowerBlock.lambda_of_fixLambda`; non-empty: `fix_guarded` at `principalArgIdx = 0` plus
`LowerFix.constToFix`/`Lower.fixUnfold`).

---

## 7. `Lower` — fourteen arms

* **`ctorApp` deleted.** Its content is `Erases.ctor` + `Erases.app` + `Lower.construct`.
* **`CtorDecl` deleted, and `RuntimeKey` becomes eliminator-only** (A-F1):
  ```lean
  def RuntimeKey (Γ : GlobalDeclarations) (kn : Kername) : Prop :=
    ∃ iid np dp nfs, ElimDecl Γ kn iid np dp nfs
  ```
  Every surviving `CtorDecl` consumer was `ctorApp`/`ctorEta`-derived. Keeping the constructor
  disjunct would make `Lower.const` — and hence the composite — **uninhabitable at every use site
  of `Unit.unit`**, measured 2/11/9/16/20 times in the five programs
  (`scratchpad/amend/r1_unit.lean`: `runtimeKey_kUnit`, `no_lower_to_kUnit`).
* **Both η arms deleted.** `ctorEta` and `elimEta` are the arms W2-R4/R5 and U1.7-b all fired
  through, and re-keying them to the bare head does not save them: `Lower` is compositional, so an
  η-expanded head still composes under `app` into `mkApps (mkLambdas ns body) args'`, a β-redex
  the ι and ctorVal arms would each have to collapse, with no bound on nesting. What they cover is
  restriction **N19** — no under-applied constructor or eliminator occurrence — a decidable
  conjunct of `Supported` (U3.8), and shipping finding **F-ETA2**. Note that N19 costs nothing for
  *constructors* once F-ETA2 is repaired: applied-form λ□ evaluates a partially applied
  constructor spine natively (`Value.construct_app_val`, `Semantics/Values.lean:104`), so the
  eraser's η path is a wart rather than a necessity. For eliminators it is a real restriction, and
  the contingency if a tracked program needs it is named in §12.
* **`elimApp` re-keyed** to a `.const kn` head with `ElimDecl` (U2.1's obstruction-1 repair);
  **`ElimHeadOf` is deleted** — its second disjunct existed only for the δ chain inside
  `lower_correct` at `Σ⁺`, and it is what made W2-R4 unguardable.
* **`fixConst` gains `(hnk : ¬ RuntimeKey Γ kn)`** (B-F3). `ElimDecl` implies `DefnDecl`, so
  nothing else excludes a `.fix` image at an eliminator constant, and step 3's head inversion
  needs it.
* **`ElimDecl` carries its block**, so the `.case` node's arity data is in scope on the target:
  ```lean
  def ElimDecl (Γ) (kn) (iid) (np dp) (nfs) : Prop :=
    (∃ body, envLookup Γ kn = some (.constantDecl ⟨some body⟩) ∧ ElimBody iid np dp nfs body) ∧
    (∃ mib, envLookup Γ iid.mutualBlockName = some (.inductiveDecl mib) ∧ IndBodyOf iid np nfs mib)
  ```
* Everything else — the eleven congruence arms, `fixBody`, `LowerAlt(s)`, `LowerBlock`,
  `ConstToFVar`/`CloseConstAt` — is unchanged. Arms: eleven congruence + `elimApp` + `fixConst` +
  `fixBody` = **fourteen**.

---

## 8. The environment relation

`ErasesEnv` is `[S §7.4]`'s `erases_deps` and gains the clause the design's version dropped: the δ
arm's own premise, in the δ arm's own direction (W2-R3).

```lean
  | mk {Γspec t} (keys) (decls) (deps)
       (defns : ∀ c b, bo c = some b → ReachableFrom Γspec t (toKername c) →
          ∃ b₀, envLookup Γspec (toKername c) = some (.constantDecl ⟨some b₀⟩) ∧
                ∀ Us' ups us, Erases env Us' [] (b.instantiateLevelParams ups us) b₀) :
       ErasesEnv env bo Γspec t
```

* **`ErasesDecl.ctor` is deleted** (§4). **`ErasesDecl.elim` gains the source-side segmentation**,
  which is what pins the `.case` node's shape to the kernel's ι rule (B-F3):
  ```lean
  | elim {I c kn iid np dp nfs body} (hi : IndInfo env I iid np nfs) (he : CasesOnOf' env I c kn)
         (hinf : InformativeInd env I) (hsh : CasesOnShape env c I dp nfs.length)
         (hb : ElimBody iid np dp nfs body) :
         ErasesDecl env bo kn (.constantDecl ⟨some body⟩)
  ```
  (`CasesOnOf'` is `CasesOnOf` with the constant `c` exposed rather than existential.)
* **`LowerEnv` gains the pass layer's environment well-formedness** (B-F2): `specClosed :
  ClosedBodies Γspec` — the law `Lower.subst_comm` consumes at every β/ζ/ι step — and
  `specBlocks : BlockBodiesLambda Γspec` — what the whole `Lower.source_*` inversion kit takes,
  and what step 4 uses to exclude a `.fix` image of a constructor value. Both are facts about `Γspec`;
  `LowerEnv` is where facts about `Γspec`-to-`Γ` live, and U3.6 derives them from the run's records
  along with the rest.
* **Reachability tracks inductive blocks.** `constRefs` (`Output.lean:225`) collects only `.const`
  kernames, so nothing forces the emitted `Γ` to declare the block a `.construct`, `.case` or
  `.proj` node reads — and `constructorArity`/`isPropositionalInductive`, which steps 4–5 consult,
  read exactly those declarations. The three cases are added; `ReachableFrom` stays decidable and
  the rungs' `rfl`-computed closures are re-measured at the gate. This is now consistent, because
  `AxiomFree` — which demanded a *bodied constant* at every reachable kername — is deleted (A-F2).
* **`LowerEnv.defsTotal` loses its `fix` disjunct**; the eraser declares every definition,
  recursive ones with a `.fix` body (measured: `Arith.ast` has 4 `tFix` and 27 `ConstantDecl`,
  every `tFix` inside one).
* `SpecEnv`, `EnvAgree`, `PrunedFor` are unchanged. `SpecEnv.exists` stays W3's.

---

## 9. The two upstream asks — and why neither is `IotaRelevant`

Both are already filed in `doc/upstream-asks.md`; the amendment changes their status, not their
content.

1. **`IsDefEqU.const_arity_inv`** (ask 6, new at the design gate) — an application headed by an
   inductive type constant is defeq to neither a sort nor a Π. Home:
   `Lean4Lean/Theory/Typing/Injectivity.lean`, whose docstring is "A bunch of important structural
   theorems which we can't prove :(" and whose three existing declarations are `sorry` and already
   inherited here through `Erasable.app`. Consumers: `not_erasable_of_informative` (step 4), the
   proj arm, T7's `firstorder_no_box`, and the no-over-application fact the `ctorVal` arm needs.
2. **`VEnv.WF'.consts_origin`** (ask 2, filed, **now load-bearing**) — a name declared as a plain
   constant in one `WF'` list below `env` is not a constructor and not an inductive type name in
   another, and the block declaring a given type former is unique. Corollaries consumed here:
   `constOrigin_not_ctorOf`, `constOrigin_not_indInfo`, `IndInfo.inj`, `CtorOf.inj`,
   `CasesOnShape.inj`. They land in a new `LeanToLambdaBox/Origin.lean` at the pin bump and are
   consumed by T7 and by §6 steps 3–4 — nowhere else. R4 is refreshed accordingly: it is no longer
   "best-effort", but it is also not needed before W3, because §4's positive `ConstOrigin` premise
   keeps every *introduction* site (the rungs, T8) free of it.

Neither is a hypothesis of the simulation. `IotaRelevant` was quantified over every `Δ` and every
spine, constructed nowhere, and deleted exactly the falsifying derivations; these are theorems of
the kernel theory, true in the intended model, consumed as lemmas, with no rung and no capstone
carrying a binder. If the fork refuses either, the fallback is **not** a premise: the affected arms
are blocked, `doc/trust.md` says so, and the deliverable stops where it stops.

---

## 10. Amendments requested of `00-REFERENCE-SPEC.md`

| # | Spec text | Amendment | Forced by |
|---|---|---|---|
| A17 | §7 criteria 1-2 ("exactly ten rules"; "no rule produces `.construct`, `.case` or `.fix`") | eleven rules; the prohibition stands for `.case` and `.fix` and is lifted for `.construct` **at the bare head**, which is `[S Fig. 18]`'s own `tConstruct` congruence — Lean spells `tConstruct`, `tInd` and `tConst` all as `Expr.const`, and the relation must distinguish them | W2-R1; T7 uniqueness |
| A18 | §7 criterion 6 ("exactly five hypotheses") | exactly MetaRocq's five (`wf`, `welltyped`, evaluation, `erases`, `erases_deps`) **plus `LowerEnv`**, which MetaRocq has no analogue of because it has no pass layer, and which carries the pass layer's environment well-formedness (`ClosedBodies`, `BlockBodiesLambda`) as clauses, not as binders. No `axiom_free`: `SEval`'s value arms are `value_head`, so a body-less constant has no source value | A-F2, A-F3, B-F2 |
| A19 | §2 T5's conclusion at `Σ⁺` | the simulation is stated at the **emitted** `Σ`; `Σ⁺` indexes the pass relation only | W2-R1, W2-R4, W2-R6 |
| A20 | §2 T4's `SEval` value and ι rules | values are `[S Fig. 12]`'s `value_head` — constructor spines, inductive-type-name spines, sorts, Π-types — and ι is call-by-value in the whole spine (**N20**) and split where the source theory splits it (`CasesOnShape`) | §5; A-F5, B-F3 |
| A21 | §2 T6's `elimInline` row ("η-expanding under-applied heads") | η-expansion is **not covered**: both η arms are deleted, their coverage is restriction **N19**, decided by `supportedB`, and shipping finding **F-ETA2** | §7; B-F4 |
| A22 | §2 T3's `ErasesDecl` arm list | `ctor` is deleted (no `.ast` in the fragment declares a genuine constructor constant; the one constructor-bodied entry is a definition) and `elim` gains the eliminator's source-side segmentation `CasesOnShape`, which is what makes the emitted `.case` node's shape a *fact about the source theory* rather than an assumption | A-F1, B-F3 |

---

## 11. Schedule consequences

W2's second half becomes five units and the gate; W3 becomes eight units and the gate. The unit
specs are in `02-PLAN.md` §2; the four structural changes are:

1. **`U2.9` is scheduled first** and owns the demolition and the relocations: `ErasesCorrect.lean`
   (retire `erases_correct_tabled`/`_ctx` and the refutations, relocate what survives),
   `Semantics/Metatheory.lean` (receive the `WcbvEval` kit), `Closed.lean` (land
   `WcbvEval.lbClosed`, which exists nowhere today — B-F5), `ErasesAbstract.lean` (receive the
   `InstLet` family). Every later unit has less to re-prove.
2. **`U2.7` owns the whole pass cluster** — `Lower.lean`, `LowerFix.lean`, `LowerCorrect.lean`,
   `ErasesLB.lean` — because a rule change to `Lower` breaks all four and `Green.lean`'s import
   closure contains them (B-F4). The deletion table's `LowerCorrect` row moves from W3 to W2.
3. **`U3.1` states the aggregator with the ι/proj/δ steps as explicit hypotheses**, as W4's `U4.1`
   does, so its acceptance is reachable before `U3.2`/`U3.2b`/`U3.3` land; **G3** instantiates them
   and is where `erases_correct` first stands with no hypothesis beyond its seven binders (B-F6).
4. **`U3.8` owns the fragment**: `Supported.lean`'s N19 conjunct and its soundness, and
   `doc/coverage.md`'s N19/N20 verdicts per program. It runs early in W3, because a failed N19
   verdict is what would force the η arms back (§12).

---

## 12. Risks this amendment adds

1. **The upstream discrimination lemma may not land** (`01-DESIGN.md` R14). U3.4 is scheduled first
   in W3; the ι/proj arms, T7 and the `ctorVal` arm's no-over-application fact are the consumers.
2. **`WF'.consts_origin` may not land** (R4, refreshed; `01-DESIGN.md` R18). Only T7 and §6 step 3
   consume it, and the positive `ConstOrigin` premise keeps W2's rungs green without it. Fallback:
   both are blocked and the trust ledger says so.
3. **N19 may fail on a tracked program** (`01-DESIGN.md` R15). `supportedB` decides it at U3.8,
   *before* the ι arm is proved. If it fails, the contingency is a single new arm — `elimEta` with
   its saturated body forced to be an `elimApp` image, so it cannot nest — plus one collapse lemma
   ("an η-expanded eliminator applied to a full spine evaluates to what the `.case` image
   evaluates to", proved through `wcbvEval_mkApps_mkLambdas_substList` and `Lower.substList_comm`).
   That is ≈300 lines and one extra case in two step lemmas; it is not a change to any theorem
   statement.
4. **N20 may be uninhabitable on a rung** (`01-DESIGN.md` R16). Each rung's own `hev` derivation is
   the test; the decidable sufficient condition of §5 is what the rung checks.
5. **`CasesOnShape` may not match how `pats`/`casesOn` are actually shaped at the pin**
   (`01-DESIGN.md` R17, new). It is read off the *inductive declaration*, not off the pattern
   table, precisely to avoid depending on `pats`' population; the `_fires` witness on the G5
   rung's `Nat.casesOn` is the test, and it is due at U2.6, before anything consumes it.
6. **`ErasesEnv.defns` is discharged concretely only through the `instantiateLevelParams` axiom
   cluster** (U2.3 obstruction O4). Confined to U3.3 and the rungs' environment witnesses; it needs
   its own `doc/trust.md` row.
7. **Reachability threading** is a fuelled-fold argument where MetaRocq's `erases_deps` is an
   inductive. Fallback: state the `deps`/`defns` clauses inductively and keep the fold as their
   decision procedure — one extra soundness lemma, no change to any theorem statement.
