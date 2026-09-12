# 04 — Wave-2 amendment: one relation, one simulation, at the emitted environment

Amends `01-DESIGN.md` (§3 decisions, §4 signatures, §5 theorems) and `02-PLAN.md` (W2 remainder,
W3) after Wave 2 machine-refuted both halves of the design's composition strategy, and after two
rounds of refutation of this amendment itself. Every claim below is grounded in a delivered
refutation, in the code at `dev/verify`, or in a measurement named with its command.
`00-REFERENCE-SPEC.md` amendments A17–A24 are requested in §10. §2 answers the first round, §13
the second; both are folded into §§3–12, which read as current fact.

**What the document says, in six lines.** `Erases` distinguishes the three readings of
`Expr.const` (eleven rules). `SEval`'s values are `[S Fig. 12]`'s `value_head`, arity bound
included, so no axiom-freedom premise is needed at T5. One simulation, on the composite, at the
emitted `Σ`, by one induction with three step lemmas. `Lower` is fourteen arms: both η arms,
`CtorDecl` and `ElimHeadOf` are gone. The fragment declares four restrictions — N19, N20, N21 and
the standing N18 — each decided or measured per program. Two upstream asks, both filed as numbered
asks, are consumed as theorems and by nothing else.

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
one `SEval` with subject reduction (U1.4), `IotaBridge` (target-side, `sorryAx`-free), T9 with its
single `hbridge` binder (`Capstone.lean`), `green_G1`. `Fuel.lean` is **not** on this list: it has
zero references tree-wide and no module imports it, so it is deleted rather than carried (§6).

---

## 2. What the amendment's own refuters settled

Ten findings at severity ≥ medium. Each is answered below by a change, not by an excuse; the two
that are *not* changes are marked.

| # | Finding | Disposition |
|---|---|---|
| **A-F1** | The eleventh rule makes `Unit.unit`'s `Σ⁺` body a `.construct`, hence a `CtorDecl`, hence a `RuntimeKey`, and `Lower.target_const` (proved) then forbids the node the eraser emits at its every use site — 2/11/9/16/20 sites in the five programs. The composite becomes uninhabitable, which the ten-rule relation was not | **`CtorDecl` and `RuntimeKey`'s constructor disjunct are deleted** (§7). `Unit.unit` is a *definition* whose compiler body is `PUnit.unit`; with `ctorApp`/`ctorEta` gone, `CtorDecl` has no consumer left. `ErasesDecl.ctor` is deleted with it — it requires `CtorOf`, so it never could justify that entry (§8). Machine-checked: `scratchpad/amend/r1_unit.lean` |
| **A-F2** | `AxiomFree Σ t` and the `constRefs` extension are jointly unsatisfiable: a block kername resolves to an `.inductiveDecl`, never to a bodied `.constantDecl`. G1 itself fails `AxiomFree` once blocks are tracked; and `AxiomFree` has no `Decidable` instance as printed | **`AxiomFree` is not landed** — it was a proposal of the first cut and has zero occurrences in the tree, so "deleted" overstates it (§5, §8). Keying `SEval`'s value arms on `CtorOf`/`IndInfo` makes a body-less plain constant have *no source value*, exactly as PCUIC's `value_head` does, so W2-R2's counterexample has no `hev` and the premise has no work to do. The `constRefs` extension lands unopposed. Machine-checked: `scratchpad/amend2/r1_axiomfree.lean` |
| **A-F3** | A18's fidelity claim is wrong: MetaRocq's `erases_correct` has **five** hypotheses and `axiom_free` is not among them; the extra premise papers over `SEval.ctorVal`, a rule PCUIC's `value_head` does not have | **Accepted in full**; it is the repair of A-F2. A18 now reads "MetaRocq's five plus `LowerEnv`" — seven binders, six premises — and the departure is removed at its source rather than compensated |
| **A-F4** | Step 4's inversion is false as written: a constructor-headed value's composite image admits `mkApps (mkLambdas ns …) cargs'` (`ctorEta`) and `mkApps (.fix defs j) cargs'` (`fixBody`) besides `.box` and the constructor spine | **Both are closed, by deletion and by a named premise** (§6 step 4): the η arms are gone, so the first shape is not in the relation; the second is excluded by `BlockBodiesLambda Σ⁺`, now a clause of `LowerEnv` (§8) rather than an unbound assumption |
| **A-F5** | `SEval.iota`'s `hmins`/`hpres` have no counterpart in PCUIC's `eval_iota`; they narrow the source relation and must be declared a coverage restriction | **Accepted and declared: restriction N20** (§5). Kept, because the boxed-prefix case genuinely needs them (§6 step 2) — the delta is forced by Lean spelling elimination as an application spine, where `Erases.box` can sit at a proper prefix, while Rocq's `tCase` is one node. The "measured mitigation" the first cut attached to this row was **false** and is deleted: the match compiler thunks nullary branches into *applications*, so the `match` fragment is precisely the affected one (§5, §13 F3) |
| **B-F1** | The two printed changes to axiom-freedom are jointly false on the existing green rung G1 | same as A-F2: `AxiomFree` deleted |
| **B-F2** | T5's premise list cannot support the `Lower` metatheory it consumes: `Lower.subst_comm` needs `ClosedBodies Σ⁺` and the whole `Lower.source_*` kit needs `BlockBodiesLambda Σ⁺`; neither is a binder and no clause supplies them | **`LowerEnv` gains `specClosed : ClosedBodies Σ⁺` and `specBlocks : BlockBodiesLambda Σ⁺`** (§8), and A18 prints them: the pass layer's environment well-formedness is what `LowerEnv` carries, the way `wf Σ` carries the source's. Binder count unchanged; the premise count is stated honestly as "MetaRocq's five, plus `LowerEnv` with four environment clauses" |
| **B-F3** | The ι arm's head step is asserted: nothing ties the source ι split to the target's `dp`/`nfs` (R3, never consumed); `ElimDecl` implies `DefnDecl`, so `fixConst` is *not* excluded by disjointness; the only existing carrier of the split is `supportedHead`, which criterion 6 forbids | **Three changes** (§5, §6 step 3, §7): `SEval.iota` gains `hsh : CasesOnShape env con I pre.length minors.length` and `hct : CtorOf env ctor I cidx` — the source theory's own segmentation, read off the inductive declaration, as Rocq reads it off `tCase`'s syntax; `ErasesDecl.elim` gains the same `CasesOnShape` at the target's `dp`/`nfs.length`; and `Lower.fixConst` gains `¬ RuntimeKey Γ kn`. The agreement lemma is `CasesOnShape.inj`, from upstream ask 2 |
| **B-F4** | W2's second half is not executable as four units on disjoint files, and it breaks the standing green obligation by construction; the deletion table puts `LowerCorrect.lean`'s demolition in W3 while naming a W2 unit as its deleter | **W2's second half is re-cut into six units** (§11): `U2.9` (demolition and relocation) is scheduled **first**, `U2.7` owns `Lower.lean`, `LowerFix.lean`, `LowerCorrect.lean` **and** `ErasesLB.lean`, and the deletion table's `LowerCorrect` row moves to W2 |
| **B-F5** | Relocations and one named prerequisite have no owning unit; the `WcbvEval` closedness-preservation lemma does not exist anywhere | **`U2.9` owns them** (§11), including `Closed.lean` and `Semantics/Metatheory.lean`. (`Semantics/Metatheory.lean` exists and already proves `eval_to_value`; the missing lemma is only the `LBClosed` one) |
| **B-F6** | U3.1's acceptance is unreachable inside its dependencies — a cycle between the aggregator and its two arm units | **Accepted**: U3.1 is restated as W4's U4.1 is, with the ι/proj/δ steps as **explicit hypotheses** of the aggregator; G3 instantiates them (§11) |
| **B-F7** | The eleventh rule's negative premises make `consts_origin` load-bearing at every `.const` introduction, while R4 still calls it inconsequential | **The premise is turned positive**: `Erases.const` takes `ConstOrigin env c` — the defining declaration *exhibited*, symmetric to `CtorOf` and `IndInfo` (§4). Introduction is then a fixture fact, needing no upstream lemma, which is what keeps `green_G1` green through W2. The *exclusion* direction moves to upstream ask 2, consumed as a theorem by T7 and by §6 step 3 only (R4 refreshed) |
| **B-F8** | `ErasableAxioms`/`AxiomRealizer` is carried although nothing consumes it, and the design does not say which premise T9 carries | **Both are deleted; T9 carries `NoBodylessRefs` in their place** (§8). `ErasableAxioms`' realizer whitelist *permitted* `Eq.rec`, so it was not `axiom_free`'s analogue; the decidable body-less-reference condition is. T5 carries no analogue — with the value arms keyed, an axiom-reaching run has no `SEval` derivation, PCUIC's own answer. The `Eq.rec`/`False.rec` rows become a `doc/coverage.md` row (F-EQREC), which is what they always were |
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
2. **`SEval`'s values are `[S Fig. 12]`'s `value_head`**: a constructor spine **under its arity**
   and an inductive-type-name spine are values, sorts and Π-types are values, and nothing else
   constant-headed is. A body-less plain constant has no value, so T5 needs no axiom-freedom
   premise; T9 keeps a decidable one, because a rung whose run reaches a body-less constant would
   otherwise be vacuously green (§5, §8).
3. **One load-bearing simulation**, on the composite `Erases ⨟ Lower`, **at the emitted `Σ`**,
   proved by one induction on `SEval` with each arm a named step lemma (§6).
4. **`Σ⁺` survives as the pass layer's metadata environment**; its *evaluation* theory goes (§9).
5. **`Lower` is fourteen arms**: `ctorApp` becomes `Erases.ctor`, both η arms are deleted (their
   coverage is restriction **N19**, shipping finding **F-ETA2**), `ElimHeadOf` is deleted,
   `ElimDecl` carries its block, `fixConst` is guarded (§7).
6. **The environment relation carries what the arms consume**: `erases_deps`' δ clause, the
   eliminator's source-side segmentation, and the pass layer's environment well-formedness (§8).
7. **Two upstream asks, filed as numbered asks 2 and 6**, replace `IotaRelevant`:
   `WF'.consts_origin` and `IsDefEqU.const_arity_inv`. Both are consumed as *theorems*; no rung
   carries a binder (§9).
8. **The fragment declares what it excludes**: N19 (no under-applied constructor or eliminator
   occurrence), N20 (every ι spine's dropped prefix, unselected minors and extra arguments have
   values) and N21 (ι fires only at `casesOn`-named heads; recursors are outside, and δ does not
   unfold an eliminator) — each decided or measured per program, each paired with a shipping
   finding where one exists (§5).

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

## 5. `SEval` — `[S Fig. 12]`'s `value_head`, call-by-value ι, and the eliminator dispatch

```lean
  /-- `value_head_cstr`: a constructor spine is a value once its arguments are **and the spine
      is within the constructor's arity**. Keyed on the source theory's classification, not on
      the compiler table and not on a name test. `harity` is `[S Fig. 12]`'s own
      `nargs ≤ cstr_arity`, read off `IndInfo`'s parameter count and field counts; without it the
      arm claims a value for an over-applied constructor spine, on which the target is stuck
      (`WcbvEval.construct_app` fires only while `args.length < ar`, `Semantics/Eval.lean:130-136`).
      It is also what makes T5's `ctorVal` arm provable without an upstream lemma. -/
  | ctorVal {Δ cn us I iid k np nfs args argsv} (hc : CtorOf env cn I k)
      (hi : IndInfo env I iid np nfs) (harity : args.length ≤ np + nfs[k]!)
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
  /-- ι, call-by-value in the **whole** spine, split where the source theory splits it, and
      **absorbing over-application** as `visitCases` does (`Erasure.lean:828-832` applies the
      arguments beyond `casesInfo.arity` outside the emitted `.case` node, and `Lower.elimApp`'s
      `extra` is the same list). `hsh` and `hct` are the data Rocq's `tCase` carries in its
      syntax: how many arguments precede the major premise, how many minors follow it, and which
      minor the matched constructor selects; `hsh` also makes the split unique, through
      `CasesOnShape.inj`. `ho` fixes the head's *reading*: `CasesOnShape` constrains only `con`'s
      name and `I`'s declaration, so without it the head may still erase by `Erases.ctor`
      (machine-checked: `scratchpad/refute2/step3.lean`, `casesOnShape_name_only`).
      `hpres`/`hmins`/`hxs` are restriction **N20**. -/
  | iota {Δ con us I pre prev disc minors minorsv extra extrav ctor cus cargs np cidx r}
      (hfl : fl.iota)
      (hsh : CasesOnShape env con I pre.length minors.length)
      (ho : ConstOrigin env con)
      (hct : CtorOf env ctor I cidx)
      (hpre : prev.length = pre.length)
      (hpres : ∀ i, i < pre.length → SEval env bo Us fl Δ pre[i]! prev[i]!)
      (hdiscr : SEval env bo Us fl Δ disc (mkApps (.const ctor cus) cargs))
      (hmin : minorsv.length = minors.length)
      (hmins : ∀ i, i < minors.length → SEval env bo Us fl Δ minors[i]! minorsv[i]!)
      (hxlen : extrav.length = extra.length)
      (hxs : ∀ i, i < extra.length → SEval env bo Us fl Δ extra[i]! extrav[i]!)
      (hidx : cidx < minors.length)
      (hdef : StepDefeq env Us Δ (mkApps (.const con us) (pre ++ disc :: minors ++ extra))
        (mkApps minors[cidx]! (cargs.drop np ++ extra)))
      (hcont : SEval env bo Us fl Δ (mkApps minors[cidx]! (cargs.drop np ++ extra)) r) :
      SEval env bo Us fl Δ (mkApps (.const con us) (pre ++ disc :: minors ++ extra)) r
  /-- δ on a compiler body, with the eliminator dispatch the eraser performs mirrored in the
      source semantics: `hnd` keeps δ off an eliminator head. The source semantics quantifies
      over an abstract body table `bo`, so without `hnd` a saturated `casesOn` spine could have
      a **second** derivation that unfolds the eliminator's own body, and T5's δ arm would owe a
      proof relating that unfolding to the emitted `.case` node: exactly the `ElimBody`
      evaluation theory §7 retires. The other arms are unchanged. -/
  | deltaC {Δ c us ups args argsv b b' v} (hfl : fl.delta)
      (hb : bo c = some b) (hnd : ∀ I dp nm, ¬ CasesOnShape env c I dp nm)
      (hinst : b' = b.instantiateLevelParams ups us) …
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

`ctorVal` loses `hnb` (the tree's rule carries only that one; `hpat`/`hne` were the first cut's
proposal and never landed — `SourceEval.lean:181-185`): with the classification premise, a
`casesOn` spine is not a value because `casesOn` is not a constructor — a structural reason, not a
name test (B-F9). `SEval.mono`, `SEval.le` and `SEval.defeq` re-prove arm by arm; the two new value
arms are `TrExprS`-reflexive and the ι case of `defeq` spends `hdef` and the `hcont` IH, which the
new premises do not touch.

**What it costs, declared.**

* **N20** — every ι spine's dropped prefix, every unselected minor and every extra argument has a
  value. PCUIC's `eval_iota` evaluates none of them, because Rocq's `tCase` is one node; Lean
  spells elimination as an application spine, so `Erases.box` can sit at a proper prefix of it and
  the target's `app_box` evaluates the arguments it discards (`Semantics/Eval.lean:97`, MetaRocq's
  `eval_box` likewise). §6 step 2 is the only consumer.

  **It is a cost, not a formality, and the `match` fragment is exactly where it bites.** The
  earlier claim that Lean's match compiler thunks nullary branches into λs is **false**: the
  compiler thunks them into *applications*. Measured on the emitted output — every nullary
  alternative of every `tCase` in `VerifyBench/ast/*.ast` — the branch head is `tApp` (5 in
  `Arith`, 16 `BinaryTrees`, 29 `Fannkuch`, 23 `Quicksort`, 26 `Sieve`), `tCase` or `tRel`, and
  **never** `tLambda`; `Arith.ast`'s `Nat` zero-branch is literally
  `(tApp (tRel 1) (tConst Unit.unit))`. So the source minor at a nullary constructor is the thunk
  application `hᵢ ()`, which is not a syntactic value, and the decidable sufficient condition
  below fails on every tracked program (measured non-value minors per total ι spine: Arith 3/3,
  BinaryTrees 16/19, Sieve 25/26, Quicksort 28/40, Fannkuch 2/2; prefix arguments 0/0 everywhere,
  so `hpres` stays cheap). `hmins` therefore needs an `SEval` derivation **per unselected branch,
  per ι step** — eager evaluation of code the program never selects.

  That is a cost, not a vacuity: Lean's type theory is total, so every well-typed closed term
  normalises and each unselected branch does have a value; partial and `unsafe` bodies are already
  outside the fragment, because `SEval` reads the compiler-body table and N8 is what admits them.
  What the restriction really deletes is the derivations where the source converges and eager
  minor evaluation would not — a possibility total programs do not have, and that is why N20 is
  inhabitable on all five while remaining a declared exclusion. The decidable sufficient condition
  (every prefix argument, minor and extra argument already a syntactic value: a λ, a literal, a
  sort, a Π, or a constructor spine within its arity) is kept as a *cheap* check, and
  `doc/coverage.md` records that it fails on all five and that the semantic obligation is what the
  rungs discharge instead. Risk **R16** is raised to medium accordingly.
* **N21** — ι fires only at a `casesOn`-named head that `CasesOnShape` classifies, and δ does not
  unfold such a head. Two consequences, both declared:
  * **recursors are outside the fragment.** `reify%` tables a `.recInfo` constant body-less
    (`Witness/SourceTable.lean:211`), so `deltaC` cannot fire at `Nat.rec`/`Acc.rec`; the value
    arms do not apply (a recursor is neither a constructor nor a type former); and `hsh` excludes
    it from ι. A spine headed by a recursor therefore has **no `SEval` derivation at all**, so a
    program reaching one makes its rung vacuously green. `supportedHead` currently lets recursors
    through (`Supported.lean:163-169, 239`: `isRecursorName tbl c then .ok ()`), which is the
    fragment predicate disagreeing with the source semantics. U3.8 makes `supportedB` reject a
    recursor head and records the verdict per program.
  * **δ does not unfold an eliminator.** `hnd` above. This is the source-side counterpart of the
    eraser dispatching `casesOn` (`Erasure.lean:768`) rather than visiting its body, and it is
    what keeps the δ arm free of the `ElimBody` evaluation theory.
* **What it does not cost.** A body-less plain constant has no value at all. That is not a new
  restriction — it is PCUIC's treatment of an axiom, and it is what keeps `axiom_free` out of T5.
  It does **not** discharge T9: see §8's `NoBodylessRefs`.

---

## 6. The load-bearing simulation

One theorem, one induction, at the emitted environment, in **five** modules whose import order is
acyclic — which the first cut's three were not, because the aggregator both supplied the arms'
spine-inversion kit and consumed their results:

```
  ErasesCorrect/Steps.lean     erases_mkApps_inv, erasable_mkApps, the box helpers,
        │                      Simulates, StepIota / StepProj / StepDelta    (U3.1)
  ErasesCorrect.lean           erases_correct_of_steps + the ten structural arms   (U3.1)
        ├── ErasesCorrect/Iota.lean    step_iota    (U3.2)
        ├── ErasesCorrect/Proj.lean    step_proj    (U3.2b)
        └── ErasesCorrect/Delta.lean   step_delta   (U3.3)
  ErasesCorrect/Close.lean     erases_correct, erases_correct_lb                    (G3)
```

The arm files import `Steps.lean` only; `Close.lean` imports all four. Nothing edits a module it
also imports, so every unit's acceptance — including U3.1's `grep "sorry" ErasesCorrect.lean`
empty — is reachable inside its own dependencies, and no unit states a theorem it leaves to
another to instantiate. The step-lemma interface is printed in `01-DESIGN.md` §5.

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

`Simulates` names the induction's motive, so the arm files and the aggregator state the same
thing:

```lean
/-- The simulation's claim at one source node: for every composite image of `e` that the
environment relation answers, an image of `v` and a target evaluation reaching it. -/
def Simulates (env : VEnv) (bo : Name → Option Expr) (Us : List Name)
    (Γspec Γ : GlobalDeclarations) (e v : Expr) : Prop :=
  ∀ {ve : VExpr} {t₀ t : LBTerm},
    TrExprS env Us [] e ve → Erases env Us [] e t₀ → Lower Γspec t₀ t →
    ErasesEnv env bo Γspec t₀ →
    ∃ v₀ v', Erases env Us [] v v₀ ∧ Lower Γspec v₀ v' ∧ WcbvEval Γ eraseFlags t v'
```

**What becomes a lemma of it, and what is retired.**

| Wave-2 deliverable | Fate |
|---|---|
| `erases_correct_tabled` / `_ctx` (U2.3) | the β/ζ/δ/lit/box arms **become the step lemmas**; the statement is retired (its `TabledConstants` guard is answered by §5's value arms, not replaced by a premise) |
| `Erases.defeqDFC_wt`, `erases_subst_let`, the four `InstLet` helpers (U2.3) | kept, moved to `ErasesAbstract.lean` (U2.9) |
| `WcbvEval.{head_value_of_mkApps, app_congr, mkApps_congr, mkApps_box}` (U2.3) | kept, moved to `Semantics/Metatheory.lean` (U2.9), which already holds `eval_to_value`/`value_final` |
| `erases_mkApps_inv`, `erasable_mkApps`, `erases_correct_box`/`_boxSpine` (U2.3, kept by U2.9) | kept, moved **below** the aggregator into `ErasesCorrect/Steps.lean` at U3.1 — they are the ι arm's entire case split (steps 1–2), and the arm files must reach them without importing the aggregator |
| `DeltaAgrees` (U2.3) | retired; its content becomes `ErasesEnv`'s `defns` clause (§8) |
| `lower_correct_plain`, `lowerFix_correct_plain`, `LowerPlain` and its three guards (U2.1) | **retired**: nothing transports along `Lower` any more. The inversion kit, the spine toolkit, `constToFix`, `subst_comm`, `substList_comm`, `fixUnfold` survive **on `Lower` itself** |
| `lower_correct_deltaChain`, `lowerFix_correct_atom` (W1) | retired as statements (both evaluate at `Σ⁺`); `LowerBlock.lambda_of_fixLambda` and `Lower.fixBody` carry their content into the δ arm |
| `LowerNoEta`, `BlockBodiesPlain`, `BlockDefsLambda`, `LowerEnvPlain`, `DeltaChain` | deleted (W2-R5) |
| `EtaSpine` and `lambda_of_fixLambda`'s `hη` premise | deleted — with both η arms gone the conclusion is unconditional (U1.7-b's counterexample is no longer in the relation) |
| `ElimHeadOf`; `ElimBody.lean`'s evaluation theory | deleted — `Σ⁺` is never evaluated. **`mkElimBodyRec` stays**: it is `ElimBody.recur`'s right-hand side (`ElimBody.lean:108,120`), feeds `mkElimBodyRec_closed`/`ElimBody.closed` and is destructed by the two inversion lemmas that survive (`LowerFix.lean:875,885`). What goes is enumerated in §11 and priced there, not in a cell that names four declarations and a round number |
| `mkCtorBody`, `mkCtorBody_closed`, `mkCtorBody_beta` | deleted — `01-DESIGN.md` §7.3 keeps them "only as long as `ErasesDecl.ctor`'s one emitted instance needs it", and that arm is deleted (§8). Zero references outside `ElimBody.lean`; `mkCtorBody_beta`'s proof goes through `wcbvEval_mkLambdas_fwd`, itself retired |
| `Fuel.lean` | **deleted**, not carried: 101 lines, zero references tree-wide, and no module imports it. The first cut carried it in §1's "stands unchanged" list and `01-DESIGN.md` §7.3 priced it at 250; both are corrected. U2.4's deliverable is retired with it |
| `PrunedFor` (`ErasesEnv.lean:329`), `EnvAgree` with its five lemmas, the planned `WcbvEval.congr_env`/`LowerEnv.congr_env` | deleted — one occurrence each (their own definitions), no consumer, and U3.6's acceptance for `congr_env` was that it elaborates |
| `LowerCorrect.lean` | **deleted as a file** (U2.7). Its simulation half goes; `BlockBodiesLambda`, the `Lower.source_*`/`target_*` inversion kit, the spine toolkit and the `NoBox` family (`:37-203`, consumed by `Capstone.lean:126,177` and `Green.lean:198`) move to `Lower.lean`; `LowerFixFixture.constToFix_needs_freshness` moves to `LowerFix.lean`; its copy of the `ElimBody` head inversion (`:2229-2251`) duplicates `LowerFix.lean:871-885` and goes |
| `AxiomFree`, `ErasableAxioms`, `AxiomRealizer`, `axiomRealizerNames`/`axiomRealizerB` | deleted (A-F2, B-F8); the `Eq.rec`/`False.rec` rows become `doc/coverage.md`'s F-EQREC row |
| `IotaBridge` | kept and **consumed by the ι arm** exactly as written (step 6) |
| `ErasureBridge.simulate` + `.lowerCorrect` (`Capstone.lean`) | **merge into one field**, `simulate`, whose shape is `erases_correct`'s; T9's proof loses one `obtain` |

**The ι arm, in six steps.** Subject
`e = mkApps (.const con us) (pre ++ disc :: minors ++ extra)`, source rule `SEval.iota`.

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
3. **Case (a) — the head.** The head rule is `Erases.const`: the `ctor` reading is refuted by
   `constOrigin_not_ctorOf` (upstream ask 2) applied to the ι rule's **own `ho : ConstOrigin env
   con`** — not to `hsh`, which constrains only `con`'s name and `I`'s declaration and transports
   to any name with the same `isCasesOnName` verdict and prefix (`casesOnShape_name_only`,
   machine-checked); the box reading is case (b) at prefix length 0. So the middle head is
   `.const (toKername con)`. Now invert `Lower` at `mkApps (.const kn) args₀` with
   `ElimDecl Γspec kn iid np dp nfs`:
   * the **`app`-congruence reading is impossible**, because it would need
     `Lower Γspec (.const kn) h'`, and `Lower.source_const` — proved by induction on the `Lower`
     derivation, under `specBlocks : BlockBodiesLambda Γspec` — gives a `.const kn` source exactly
     two images: `Lower.const`'s, which demands `¬ RuntimeKey`, and `Lower.fixConst`'s, which now
     demands the same (§7). `ElimDecl` refutes both. The third arm whose source is unconstrained,
     `Lower.fixBody` (`Lower.lean:228-239` constrains it only by `hj : bs[j]? = some b`), is what
     makes this an induction rather than a three-arm syntactic check: it is excluded because
     `specBlocks` forces `isLambda (.const kn) = true`, which is false. `hnk` on `fixConst` is
     necessary, not sufficient;
   * so the derivation is **`elimApp`**, and its own split satisfies `pre'.length = dp`,
     `minors'.length = nfs.length`. With `hsh` and `ErasesDecl.elim`'s `CasesOnShape` at the same
     `(con, I)`, `CasesOnShape.inj` gives `pre.length = dp` and `minors.length = nfs.length`, so
     the two spine decompositions coincide and the two `extra` lists correspond pointwise (`hxlen`
     against `elimApp`'s `hxlen`/`hx`). Over-application is **covered, not excluded**: the eraser
     applies the arguments past `casesInfo.arity` outside the emitted node
     (`Erasure.lean:828-832`) and `elimApp` mirrors that, and it fires — Quicksort has three
     over-applied `casesOn` spines (`PSigma.casesOn` 6>5, `Nat.casesOn` 5>4, `Nat.le.casesOn`
     8>6), which the `.ast` hides because the extra arguments are absorbed.
   A `.rec`-headed head is outside the fragment by N21; an otherwise unemitted head is excluded by
   `ErasesEnv`'s `deps` clause, not by a new premise.
4. **The discriminant.** The IH at `hdiscr` gives `WcbvEval Γ disc' dv'` with the constructor value
   related to `dv'`. The value's erasure is `mkApps (.construct iid' k []) cargs₀` — the `const`
   reading is refuted by `hct` against `constOrigin_not_ctorOf`, and the `.box` reading by
   `not_erasable_of_informative` (`ErasesDecl.elim`'s `hinf : InformativeInd env I` plus upstream
   ask 6). Its `Lower` image is `mkApps (.construct iid' k []) cargs'`: the congruence arms, plus
   `fixBody` at a `.construct` source, which `specBlocks : BlockBodiesLambda Γspec` refutes (A-F4).
   Saturation — `(cargs'.drop np).length = nfs[k]` — comes from the source value itself: `hdiscr`'s
   `SEval.ctorVal` carries `harity : cargs.length ≤ np + nfs[k]!` (§5) and the discriminant is
   typed at `I` applied to its indices, so the spine is exactly saturated. `IndInfo.inj` gives
   `iid' = iid`.
5. **The node's environment facts.** `isPropositionalInductive Γ iid = false` and
   `constructorArity Γ iid k = some (np + nfs[k])` come from `ErasesDecl.ind`'s `IndBodyOf`
   (`ErasesEnv.lean:93`, which already pins `propositional = false`) transported by
   `LowerEnv.inds`; the block is in scope because `ElimDecl` carries it (§7) and because
   reachability tracks blocks (§8).
6. **The branch, and the extra arguments.** The source continues at
   `mkApps minors[cidx]! (cargs.drop np ++ extra)`, whose composite image is
   `mkApps (mkLambdas names body') (fields' ++ extra')` — `LowerAlt` peels exactly the λ-telescope
   whose binder count is `nfs[k]`. Apply the IH at `hcont` **to that target**; at `extra = []`
   rewrite to the ι reduct with `wcbvEval_mkApps_mkLambdas_substList` (`IotaBridge.lean`: a
   β-chain of field applications *is* `iota_red`), side conditions from
   `value_mkApps_construct_args` and the closedness kit (`specClosed`, plus U2.9's
   `WcbvEval.lbClosed`), and let `WcbvEval.iota` assemble. At `extra ≠ []` the same rewrite runs
   under `wcbvEval_mkApps_head_congr` (`IotaBridge.lean:40-44`, already the δ arm's tool): it
   replaces the spine head `mkApps (mkLambdas names body') fields'` by the `.case` node, which has
   the same evaluations, leaving `extra'` untouched. Over-application therefore costs one existing
   lemma and no new premise.

No step inverts `ElimBody`, evaluates `Σ⁺`, or needs a spine-generalised motive: the IH is taken at
the *un-contracted* branch application, which is where U2.1's obstruction 2 disappears.

**The β arm owes one case to the same over-application.** `Lower.elimApp`'s source is
`mkApps hd (pre ++ disc :: minors ++ extra)` (`Lower.lean:188-200`), which at `extra ≠ []` is an
`.app` node, so the β arm's `Lower` inversion at `.app f a` has three readings, not one:
`app`-congruence (the main case); `fixBody`, excluded by `specBlocks`; and `elimApp`, split
further —
* **`extra ≠ []`**: re-associate. `elimApp` at `extra.dropLast` relates `f` to
  `mkApps (.case …) extra'.dropLast`, and its `hx` at the last index relates `a` to
  `extra'.getLast`, so the reading collapses into `app`-congruence and the arm proceeds unchanged.
  This is the only content of the case and it is one list lemma.
* **`extra = []`**: the source `.app f a` *is* the saturated eliminator spine and `f` is an
  eliminator spine one minor short. The β rule's own `hf : SEval env bo Us fl [] f (.lam …)` is
  then uninhabited, by `SEval.no_elimSpine_value` (U3.1, in `ErasesCorrect/Steps.lean`): at an
  under-applied `casesOn` spine no arm applies — `deltaC` is blocked by `hnd` (§5), `ctorVal` and
  `indVal` by `ConstOrigin env c` through ask 2, `iota` by `CasesOnShape.inj` against the
  under-application, and `beta` by induction on the spine length. Its two premises,
  `CasesOnShape env c I dp nm` and `ConstOrigin env c`, are `ErasesDecl.elim`'s `hsh` and its new
  `hco` (§8), reached from `elimApp`'s `ElimDecl` through `hspec`'s `decls` clause.

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
* **`elimApp` keeps its `extra`.** It is what `visitCases` emits (`Erasure.lean:828-832`), it
  fires on a tracked program (three spines in Quicksort), and `SEval.iota` is generalised to match
  it rather than the other way round (§5). The one consequence is the β arm's re-association case
  (§6).
* Everything else — the eleven congruence arms, `fixBody`, `LowerAlt(s)`, `LowerBlock`,
  `ConstToFVar`/`CloseConstAt` — is unchanged. Arms: eleven congruence + `elimApp` + `fixConst` +
  `fixBody` = **fourteen**.
* **`LowerCorrect.lean` is deleted as a file**, by U2.7, in this wave. Of its 2,561 lines the
  simulation half goes; `BlockBodiesLambda`, the `Lower.source_*` inversion kit, the spine toolkit
  and the **`NoBox` family** (`NoBox`/`NoBoxArgs`/`NoBoxAlts`/`NoBoxDefs` and
  `noBox_lower_needs_noFix`, `:37-203`) move to `Lower.lean`, which is where `Capstone.lean` and
  `Green.lean` already reach them through their import closure;
  `LowerFixFixture.constToFix_needs_freshness` moves to `LowerFix.lean`. Nothing is left, so no
  residue is unowned.

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
         (hco : ConstOrigin env c) (hb : ElimBody iid np dp nfs body) :
         ErasesDecl env bo kn (.constantDecl ⟨some body⟩)
  ```
  (`CasesOnOf'` is `CasesOnOf` with the constant `c` exposed rather than existential.) `hco` is the
  same positive fact `Erases.const` takes — a `casesOn` constant is declared as a definition — and
  it is what T5's β arm reaches through `hspec` to discharge `SEval.no_elimSpine_value` (§6).
* **`LowerEnv` gains the pass layer's environment well-formedness** (B-F2): `specClosed :
  ClosedBodies Γspec` — the law `Lower.subst_comm` consumes at every β/ζ/ι step — and
  `specBlocks : BlockBodiesLambda Γspec` — what the whole `Lower.source_*` inversion kit takes,
  and what step 4 uses to exclude a `.fix` image of a constructor value. Both are facts about `Γspec`;
  `LowerEnv` is where facts about `Γspec`-to-`Γ` live, and U3.6 derives them from the run's records
  along with the rest.
* **T9 keeps a decidable body-less-reference condition; T5 does not.** `ErasableAxioms`
  (`Output.lean:315-320`) is deleted because its `AxiomRealizer` whitelist *permitted* `Eq.rec` and
  `False.rec` while nothing realizes them, and the first cut's proposed `AxiomFree` is not landed
  (A-F2). What replaces it at T9 — and only at T9 — is the honest analogue of
  `erase_correct_firstorder`'s `axiom_free Σ` (`refs/metacoq-erasure.md:600`):

  ```lean
  /-- No constant reachable from `t` in the emitted environment is declared without a body.
  Decidable; false exactly where the target is stuck at a `delta` step. -/
  def NoBodylessRefs (Γ : GlobalDeclarations) (t : LBTerm) : Prop :=
    ∀ kn, ReachableFrom Γ t kn → isBodylessConst (LBTerm.envLookup Γ kn) = false
  ```

  Without it a rung whose run reaches a body-less constant is **vacuously** green and nothing flags
  it: measured, `Fannkuch.ast` emits `Eq.rec` as `(ConstantDecl (constant_body None))`, so a
  Fannkuch rung's `hev` is uninhabitable. With it, the Fannkuch rung is outside T9's domain, by a
  premise that is `by decide +kernel` on the rung's own environment, and `doc/coverage.md` carries
  the row with **F-EQREC** as its shipping finding. T5 still carries no such premise: the value
  arms already deny a body-less constant a source value, which is PCUIC's answer, and the
  condition belongs where MetaRocq puts it.
* **Reachability tracks inductive blocks.** `constRefs` (`Output.lean:225`) collects only `.const`
  kernames, so nothing forces the emitted `Γ` to declare the block a `.construct`, `.case` or
  `.proj` node reads — and `constructorArity`/`isPropositionalInductive`, which steps 4–5 consult,
  read exactly those declarations. The three cases are added; `ReachableFrom` stays decidable and
  the rungs' `rfl`-computed closures are re-measured at the gate. This is now consistent, because
  `AxiomFree` — which demanded a *bodied constant* at every reachable kername — is deleted (A-F2).
* **`LowerEnv.defsTotal` loses its `fix` disjunct**; the eraser declares every definition,
  recursive ones with a `.fix` body (measured: `Arith.ast` has 4 `tFix` and 27 `ConstantDecl`,
  every `tFix` inside one).
* **`EnvAgree` (with `.rfl'`/`.symm`/`.trans`/`.isProp`/`.ctorArity`), the planned
  `WcbvEval.congr_env`/`LowerEnv.congr_env`, and `PrunedFor` (`ErasesEnv.lean:329`) are deleted**:
  zero consumers tree-wide, and `PrunedFor`'s only occurrence is its own definition. `IotaInert`
  (`ErasesEnv.lean:72`) goes with them — `SourceEval.lean` no longer mentions it. `SpecEnv` is
  unchanged and `SpecEnv.exists` stays W3's.

---

## 9. The two upstream asks — and why neither is `IotaRelevant`

Both are now **filed as numbered asks** in `doc/upstream-asks.md`, each with a Lean statement.
The first was not: the first cut called it "ask 6" while item 6 of that file was the
*"Reported, not asked"* section and the lemma appeared nowhere in it. That is corrected, and the
file's own framing ("items 1-5 are asks") with it.

1. **`IsDefEqU.const_arity_inv`** (ask 6) — an application headed by an inductive **type former**
   is defeq to neither a sort nor a Π; the Lean statement is in `doc/upstream-asks.md`. Home:
   `Lean4Lean/Theory/Typing/Injectivity.lean`, whose docstring is "A bunch of important structural
   theorems which we can't prove :(" and whose three existing declarations are `sorry` and already
   inherited here through `Erasable.app`. **Three** consumers, all through
   `not_erasable_of_informative`: T5's ι arm (step 4), T5's proj arm, T7's `firstorder_no_box`.
   Not four: the `ctorVal` arm's no-over-application fact is now `harity`, `[S Fig. 12]`'s own
   `nargs ≤ cstr_arity` carried by the value rule (§5), so the arm needs no kernel lemma.
   Expected to land the way its three siblings stand — as a `sorry` — and its `sorryAx` root then
   inherits into T5's ι and proj arms and into T7. `doc/trust.md` says so; §12 prices the refusal.
2. **`VEnv.WF'.consts_origin`** (ask 2, filed, **now load-bearing**) — a name declared as a plain
   constant in one `WF'` list below `env` is not a constructor and not an inductive type name in
   another, and the block declaring a given type former is unique. Corollaries consumed here:
   `constOrigin_not_ctorOf`, `constOrigin_not_indInfo`, `IndInfo.inj`, `CtorOf.inj`,
   `CasesOnShape.inj`. They land in a new `LeanToLambdaBox/Origin.lean` at the pin bump and are
   consumed by T7, by §6 steps 3–4, and by `SEval.no_elimSpine_value` — nowhere else. R4 is
   refreshed accordingly: it is no longer "best-effort", but it is also not needed before W3,
   because §4's positive `ConstOrigin` premise keeps every *introduction* site (the rungs, T8) free
   of it. `WF'.defeqOwn` (ask 1) lands with the same pin bump; U3.4 owns all three.

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
| A20 | §2 T4's `SEval` value and ι rules | values are `[S Fig. 12]`'s `value_head` — constructor spines **within the constructor's arity**, inductive-type-name spines, sorts, Π-types — and ι is call-by-value in the whole spine (**N20**), split where the source theory splits it (`CasesOnShape`), reading its head as a plain constant (`ConstOrigin`), and absorbing over-application as the eraser does | §5; A-F5, B-F3, second round F1/F2/F3 |
| A21 | §2 T6's `elimInline` row ("η-expanding under-applied heads") | η-expansion is **not covered**: both η arms are deleted, their coverage is restriction **N19**, decided by `supportedB`, and shipping finding **F-ETA2** | §7; B-F4 |
| A22 | §2 T3's `ErasesDecl` arm list | `ctor` is deleted (no `.ast` in the fragment declares a genuine constructor constant; the one constructor-bodied entry is a definition) and `elim` gains the eliminator's source-side segmentation `CasesOnShape` **and its origin `ConstOrigin`**, which is what makes the emitted `.case` node's shape a *fact about the source theory* rather than an assumption, and what discharges T5's β arm at a saturated eliminator spine | A-F1, B-F3, second round F6 |
| A23 | §5 N-list | add **N19** (no under-applied constructor or eliminator occurrence), **N20** (call-by-value ι) and **N21** (ι only at `casesOn`-named heads: recursors are outside the fragment and `supportedB` must reject them; δ does not unfold an eliminator) | §5, §7; A21, second round F3 |
| A24 | §2 T9's premise list | `ErasableAxioms` is replaced by the decidable `NoBodylessRefs Γ t` — `erase_correct_firstorder`'s `axiom_free` analogue, with no realizer whitelist. T5 carries no analogue: its value arms deny a body-less constant a source value | second round F4; `Fannkuch.ast`'s body-less `Eq.rec` |

---

## 11. Schedule consequences

W2's second half becomes six units and the gate; W3 becomes eight units and the gate. The unit
specs are in `02-PLAN.md` §2; the six structural changes are:

1. **`U2.9` is scheduled first** and owns the demolition and the relocations: `ErasesCorrect.lean`
   (retire `erases_correct_tabled`/`_ctx` and the refutations, relocate what survives),
   `Semantics/Metatheory.lean` (receive the `WcbvEval` kit), `Closed.lean` (land
   `WcbvEval.lbClosed`, which exists nowhere today — B-F5), `ErasesAbstract.lean` (receive the
   `InstLet` family). Every later unit has less to re-prove.
2. **`U2.7` owns the whole pass cluster** — `Lower.lean`, `LowerFix.lean`, `LowerCorrect.lean`,
   `ErasesLB.lean` — because a rule change to `Lower` breaks all four and `Green.lean`'s import
   closure contains them (B-F4). The deletion table's `LowerCorrect` row moves from W3 to W2.
3. **`U2.10` owns `ElimBody.lean`**, which no unit owned while `02-PLAN.md` scheduled a partial
   deletion from it under U3.1 — a unit that owns only `ErasesCorrect.lean`. The row's
   `mkElimBodyRec` entry is struck (it is `ElimBody.recur`'s right-hand side), and what the
   retirement actually deletes is enumerated: the de-Bruijn/evaluation kit `LBTerm.shift_zero`,
   `LBTerm.subst_spine`, `LBTerm.substList_mkApps`, `substTele` with its nine lemmas,
   `elimAltsSub` with its two, `substList_reverse_fields`, `eval_self`, `EvalArgs` with its six,
   `wcbvEval_{app_inv, mkApps_inv, beta_step, mkApps_head_swap, app_arg_swap, mkApps_args_swap,
   case_inv, mkLambdas_fwd, mkLambdas_bwd}`, `mkCtorBody` with `mkCtorBody_closed` and
   `mkCtorBody_beta`, `mkElimBody_iota_fwd`/`_bwd`, and the `*_iota_fires` fixture block —
   **≈740 lines** (`ElimBody.lean` 953 → ≈215), not the ≈600 the first cut named for four
   declarations. What stays: `fieldArgs`, `elimAlts`, `mkElimBody`, `mkElimBodyRec`, the closedness
   chain up to `ElimBody.closed`, and criterion 7's three checked `ElimBody` instances
   (`natCasesOn_elimBody`, `boolCasesOn_elimBody`, `decCasesOn_elimBody`).
4. **`U3.1` states the aggregator with the ι/proj/δ steps as explicit hypotheses**, as W4's `U4.1`
   does, and the module graph is split so that its acceptance is reachable *inside its own
   dependencies*: `ErasesCorrect/Steps.lean` below the arms, `ErasesCorrect/Close.lean` above them,
   owned by **G3**, where `erases_correct` first stands with no hypothesis beyond its seven binders
   (B-F6, and the second round's F1). Nothing is "stated and left".
5. **`U3.8` owns the fragment**: `Supported.lean`'s N19 conjunct, its **N21** recursor rejection,
   both soundness lemmas, and `doc/coverage.md`'s N19/N20/N21 verdicts per program. It runs early
   in W3, because a failed N19 verdict is what would force the η arms back (§12).
6. **Documentation and fixtures that the rule changes falsify are in the changing units' file
   lists**, not left to be discovered at a gate: `doc/rules-Erases.md` in U2.5 (its
   `erases_tConstruct` row currently asserts the opposite of A17, and `Hygiene.checkTables` fails
   on an `Erases` arm absent from the table), `doc/rules-Lower.md` in U2.7 (it documents `ctorApp`,
   `ctorEta`, `elimEta`, `ElimHeadOf`, `CtorDecl`, `EtaSpine` and `lambda_of_fixLambda`'s `hη`),
   `test/Ledger.lean` in U2.7 (its `#print axioms` rows name `lower_correct_deltaChain` and
   `lowerFix_correct_atom`, both deleted there), and `doc/trust.md` in U2.8.

---

## 12. Risks this amendment adds

1. **The upstream discrimination lemma may not land** (`01-DESIGN.md` R14). U3.4 is scheduled first
   in W3; the ι/proj arms, T7 and the `ctorVal` arm's no-over-application fact are the consumers.
2. **`WF'.consts_origin` may not land** (`01-DESIGN.md` R4, refreshed). T7, §6 step 3 and
   `SEval.no_elimSpine_value` consume it, and the positive `ConstOrigin` premise keeps W2's rungs
   green without it. Fallback:
   both are blocked and the trust ledger says so.
3. **N19 may fail on a tracked program** (`01-DESIGN.md` R15). `supportedB` decides it at U3.8,
   *before* the ι arm is proved. If it fails, the contingency is a single new arm — `elimEta` with
   its saturated body forced to be an `elimApp` image, so it cannot nest — plus one collapse lemma
   ("an η-expanded eliminator applied to a full spine evaluates to what the `.case` image
   evaluates to", proved through `wcbvEval_mkApps_mkLambdas_substList` and `Lower.substList_comm`).
   That is ≈300 lines and one extra case in two step lemmas; it is not a change to any theorem
   statement.
4. **N20's per-branch obligation is larger than the decidable check suggests** (`01-DESIGN.md`
   R16, raised to **medium**). The decidable sufficient condition fails on all five programs, for
   the measured reason in §5: the match compiler's nullary branches are thunk *applications*, not
   λs. Each rung's `hev` derivation must therefore evaluate every unselected branch of the whole
   run, which is buildable (Lean is total) but is proof volume proportional to the program, not to
   its trace. **Trigger:** G3's `green_G5` is the first rung that builds one; if its `hev` is more
   than a few hundred lines, the rungs stay small and `doc/coverage.md` says which programs carry a
   constructed `hev` and which carry it as a binder.
5. **`CasesOnShape` may not match how `pats`/`casesOn` are actually shaped at the pin**
   (`01-DESIGN.md` R17, new). It is read off the *inductive declaration*, not off the pattern
   table, precisely to avoid depending on `pats`' population; the `_fires` witness on the G5
   rung's `Nat.casesOn` is the test, and it is due at U2.6, before anything consumes it.
6. **A tracked program reaches a recursor, so N21 empties its rung** (`01-DESIGN.md` R20, new).
   U3.8 decides it with `supportedB` in the same unit that lands the rejection, before the ι arm is
   written. The compiler bodies N8 admits are what keeps `brecOn`/`Nat.rec` out of the five
   programs' prepared bodies; if a program reaches one anyway, it leaves the fragment and
   `doc/coverage.md` records which construct took it out.
7. **`ErasesEnv.defns` is discharged concretely only through the `instantiateLevelParams` axiom
   cluster** (U2.3 obstruction O4). Confined to U3.3 and the rungs' environment witnesses; it needs
   its own `doc/trust.md` row.
8. **T5's β arm cannot route `SEval.no_elimSpine_value`'s premises** from `hspec` (`01-DESIGN.md`
   R19, new). The case arises only at `Lower.elimApp`'s `extra = []` reading, where the source
   `.app f a` is a saturated eliminator spine; U3.1 owns it at ≈150 lines. Fallback: an explicit
   side condition on a `StepBeta` interface, discharged at `Close.lean` from the rung's
   environment — one hypothesis on a step interface, no change to `erases_correct`'s statement.
9. **Reachability threading** is a fuelled-fold argument where MetaRocq's `erases_deps` is an
   inductive. Fallback: state the `deps`/`defns` clauses inductively and keep the fold as their
   decision procedure — one extra soundness lemma, no change to any theorem statement.

---

## 13. Second refutation round

Two refuters re-read this amendment. Fifteen findings — nine main, six in the dead-code addendum.
Both verdicts are *sound-with-amendment*; every finding is answered below by a change or by a
correction of the finding, and each answer names the evidence that settled it. The changes are
folded into §§1–12, which read as current fact.

### Fidelity and soundness

| # | Finding | Verdict | What changed, and on what evidence |
|---|---|---|---|
| **F1** | `IsDefEqU.const_arity_inv` is not filed and nothing states it; §9's "both are already filed" is false; and `ctorVal` drops `value_head_cstr`'s `nargs ≤ cstr_arity` while A20 claims `value_head` fidelity | **accepted** | `doc/upstream-asks.md` has six asks now, the sixth being `IsDefEqU.const_arity_inv` with a full Lean statement; the file's framing line and ask 2's status line are corrected with it. Its consumers drop from four to three, because `SEval.ctorVal` regains the arity bound as `harity : args.length ≤ np + nfs[k]!`, read off `IndInfo` (§5) — which is both the fidelity repair and the cheaper way to give T5's `ctorVal` arm its no-over-application fact. Verified: `refs/metacoq-erasure.md:147-150` prints `nargs ≤ cstr_arity` in `value_head_cstr`; `Semantics/Eval.lean:130-136` makes `construct_app` fire only while `args.length < ar`, so the target is stuck exactly where the bound is violated; `grep const_arity_inv doc/upstream-asks.md` was empty |
| **F2** | §6 step 3's exclusion of the `Erases.ctor` head reading does not follow: `CasesOnShape` says nothing about `con`'s declaration | **accepted** | `SEval.iota` gains `ho : ConstOrigin env con` (§5), and step 3 spends `ho`, not `hsh` (§6). Verified: the refuter's `casesOnShape_name_only` (`scratchpad/refute2/step3.lean`, exit 0) transports `CasesOnShape` to any name with the same `isCasesOnName` verdict and prefix; `VInductDecl.consts` (`Theory/Inductive.lean:307-311`) holds type formers, constructors and recursors, and no `casesOn` |
| **F3** | `hsh` narrows ι to `casesOn`-named heads while `supportedHead` lets recursors through, so a recursor-reaching program has no `SEval` derivation and its rung is vacuously green | **accepted, and extended** | Declared as **N21** (§5), with `supportedB` rejecting recursor heads at U3.8. Verified: `Supported.lean:239` is `else if isRecursorName tbl c then .ok ()`. The extension is ours: `reify%` tables a `.recInfo` body-less and, like a constructor, leaves a `casesOn`-like head body-less too (`Witness/SourceTable.lean:121-132`), but the source semantics quantifies over an abstract body table `bo` — so at a saturated `casesOn` spine `deltaC` could still be a *second* available rule, unfolding the eliminator's own body, which T5's δ arm cannot relate to the emitted `.case` node without the `ElimBody` evaluation theory §7 retires. `SEval.deltaC` therefore gains `hnd`, the source-side mirror of the eraser's own dispatch |
| **F4** | Dropping `hax` from T9 departs from `erase_correct_firstorder`, which takes `axiom_free Σ`, and trades a checkable premise for undetectable vacuity — measured, `Fannkuch.ast` emits `Eq.rec` body-less | **accepted** | T9 carries the decidable `NoBodylessRefs Γ t` (§8), landed by U2.8 in `Output.lean`, swapped into `shipping_erase_correct_firstorder` by G2, discharged `by decide +kernel` per rung. The rung it flags is **Fannkuch**, whose `doc/coverage.md` row cites F-EQREC. T5 keeps no analogue: MetaRocq puts `axiom_free` on `erase_correct_firstorder`, not on `erases_correct` (`refs/metacoq-erasure.md:552, 600`) |
| **F5** | "`.const kn` has no image at all" is false as a case check: `Lower.fixBody` constrains its source only by `hj`, so `.const kn` is an admissible source; the conclusion survives by a derivation induction, and `hnk` is necessary, not sufficient | **accepted** | §6 step 3 now argues through `Lower.source_const` — proved by induction on the `Lower` derivation, under `specBlocks` — and names `fixBody` as the third arm, excluded because `BlockBodiesLambda` forces `isLambda (.const kn) = true`. Verified: `Lower.lean:228-239`'s `hj : bs[j]? = some b`; `LowerCorrect.lean:403-406`'s `BlockBodiesLambda` is exactly `isLambda bs[j]! = true` |
| **F6** | The β arm must invert `Lower.elimApp` with `extra ≠ []`; belongs in a unit's spec | **accepted** | §6 ends with the β arm's three readings and their disposition; the `extra ≠ []` case is a re-association into `app`-congruence, the `extra = []` case is discharged by `SEval.no_elimSpine_value`, and both are in U3.1's spec. The premises that lemma needs are `ErasesDecl.elim`'s `hsh` and its new `hco` (§8) |

### Principledness and feasibility

| # | Finding | Verdict | What changed, and on what evidence |
|---|---|---|---|
| **F1** | W3's file graph is circular: `ErasesCorrect/Iota.lean` must import `ErasesCorrect.lean`, and G3 edits `ErasesCorrect.lean` to instantiate with `Iota.lean`'s lemma. Lean rejects; no unit owns a fix; and U3.1's "stated and left" contradicts its own `sorry`-free acceptance | **accepted** | Five modules, printed in §6: `ErasesCorrect/Steps.lean` below the arms (the spine inversion kit, the box helpers, `Simulates`, `StepIota`/`StepProj`/`StepDelta`), the aggregator, the three arm files, and `ErasesCorrect/Close.lean` above them, owned by G3. "Stated and left" is deleted from U3.1; the three step signatures are printed in `01-DESIGN.md` §5, which is where the refuter correctly observed the normative document said nothing |
| **F2** | Over-applied eliminators are an undeclared restriction and they fire: Quicksort has three such spines, and `SEval.iota`'s subject excludes them | **accepted, generalised rather than restricted** | `SEval.iota`'s subject becomes `pre ++ disc :: minors ++ extra`, matching `Lower.elimApp`, which already carries `extra` because `visitCases` applies the arguments past `casesInfo.arity` outside the node (`Erasure.lean:828-832`). Sound for the same reason the un-generalised rule is: the step carries the kernel's own `hdef` at the applied instance, and `hsh` still makes the split unique through `CasesOnShape.inj`. It costs one existing lemma on the target — `wcbvEval_mkApps_head_congr` (`IotaBridge.lean:40-44`), already the δ arm's tool — so no **N19b** is declared and Quicksort stays in the fragment |
| **F3** | N20's decidable check fails on every tracked program and its "measured mitigation" is false: the match compiler's nullary branches are thunk *applications* | **accepted** | §5 restates N20 honestly, with the measurement re-run here: across all five `.ast` files no nullary alternative has a `tLambda` head, `Arith.ast`'s `Nat` zero-branch is `(tApp (tRel 1) (tConst Unit.unit))`, and the per-branch obligation is semantic. The false mitigation is deleted from §5, from `01-DESIGN.md` R16 and from U3.8's spec; R16 is raised to medium. The honest framing is added: Lean's totality makes `hmins` a *cost* — every well-typed closed term normalises, so each unselected branch has a value — and partial/`unsafe` bodies are already outside, since `SEval` reads the compiler-body table N8 admits |
| **F4** | The green ladder does not test the amendment; G2's headline claim about `green_G1` is false; and `hev` is a `Green.lean` binder A14's class-**D** list does not name, hence class-**C** and uninhabited | **accepted** | G2's acceptance no longer claims `green_G1` exercises the new rules — it takes `hbridge` as a binder (`Green.lean:185`) and constructs no `Erases`/`Lower`/`SEval` — and names U2.5's two `_fires` witnesses (`Erases.ctor` at a fixture constructor, `Erases.const` with `ConstOrigin` exhibited) and U2.6's five as the wave's real test. `hev` (`Green.lean:186`) is added to A14's ledger as **class C, uninhabited at G1–G4**, with G3's `green_G5` the first rung that constructs one; `test/ledger.expected` and `doc/trust.md` carry the row until then |
| **F5 / G** | `mkElimBodyRec` is scheduled for deletion under a unit that does not own `ElimBody.lean`, and it is `ElimBody.recur`'s own shape with live consumers | **accepted** | `mkElimBodyRec` stays. `ElimBody.lean` gets an owning unit, **U2.10**, and the retirement row is enumerated declaration by declaration and re-priced at ≈740 lines (§11). Verified: `ElimBody.lean:108,120` (the `recur` right-hand side), `:157,162` (closedness), `LowerFix.lean:875,885` and `LowerCorrect.lean:2235,2251` (the two inversions) |
| **F6** | U2.5 moves `CtorOf` out of `ErasesEnv.lean` without co-owning it, while requiring `hygiene --dup` to exit 0 | **accepted** | `ErasesEnv.lean` is in U2.5's file list, co-owned with U2.8 which runs after it; U2.5's edit there is the removal of `CtorOf` and of the dead `IotaInert` |
| **F7** | The upstream ask is mis-filed; `WF'.defeqOwn` is omitted; and "consumed as theorems" oversells, since `Injectivity.lean`'s three siblings are `sorry` at the pin | **accepted** | Answered with fidelity F1 for the filing. §9 now says plainly that ask 6 is expected to land as a `sorry` whose root inherits into T5's ι and proj arms and into T7, and U3.4's acceptance already records the inherited roots. `WF'.defeqOwn` is named in §9 as ask 1, landing with the same pin bump |
| **F8** | U2.6 says `ctorVal` loses `hnb`/`hpat`/`hne`, but the rule carries only `hnb`, so the grep acceptance is vacuous | **accepted** | §5 and U2.6 say `ctorVal` loses `hnb`, the one side condition the tree's rule carries (`SourceEval.lean:181-185`); `hpat`/`hne` were the first cut's proposal and never landed. U2.6's grep acceptance is replaced by one that can fail: the refutation witness `untabled_const_not_value` and the four `_fires` witnesses |
| **F9** | Undeclared edges U2.8→U2.6 and U3.5→U3.2 | **accepted** | Both are in `02-PLAN.md` §2 and in the unit specs. U2.8 needs `CasesOnShape`, which U2.6 defines in `SourceEval.lean`; U3.5 needs `not_erasable_of_informative`, which U3.2 proves. W2's second half is six serial stages and W3's arm chain is five |
| **H** | `Hygiene.cellFiles` drops possessive tokens, so all three partial-deletion rows escape the check `02-PLAN.md` says enforces them — measured `--schedule: 7 rows, 45 files, 0 inversions` | **accepted** | `Tools/Hygiene.lean:144-166` is confirmed: `backticked` marks a token followed by `'s` as a part-of-file citation and `cellFiles` drops it. The tool is not this document's to change, so the three rows are restated with **bare backticked filenames**: `LowerCorrect.lean` becomes a whole-file deletion (§7), `ElimBody.lean` gets its own row under U2.10, and `CheckerAdequacy.lean`'s row names the file. The tool defect is recorded for the gate as a `doc/rework/03-DEV-FIX.md` row: until it parses possessives, a partial-deletion row must name its file bare or go unchecked |
| **I** | Dead code is carried against the design's own standard: `Fuel.lean`, `PrunedFor`, `EnvAgree`/`congr_env`, `mkCtorBody`/`mkCtorBody_beta` | **accepted in full** | All deleted, each with an owning unit (§6, §8, §11). Verified: `Fuel.lean` 101 lines, no `LeanToLambdaBox.Fuel` import and no reference (the tree's other `Fuel` tokens are `FuelConfig` and `SupportError.outOfFuel`); `PrunedFor` one occurrence, its definition; `EnvAgree` and `≐` zero uses outside `ErasesEnv.lean`, and `congr_env` does not exist yet; `mkCtorBody`, `mkCtorBody_closed`, `mkCtorBody_beta` zero references outside `ElimBody.lean`, and `01-DESIGN.md` §7.3's own rule retires them with `ErasesDecl.ctor`. `AxiomFree` has zero occurrences, so A-F2's "deleted" is corrected to "not landed" |
| **J** | Unowned casualties (`test/Ledger.lean`, `doc/trust.md`, `doc/rules-Erases.md`, `doc/rules-Lower.md`), `NoBox`'s home, `LowerCorrect.lean`'s residue, and two estimates | **accepted** | The four documents are in the changing units' file lists (§11 item 6). `NoBox` and its family move to `Lower.lean` with the rest of the surviving pass metatheory, and `LowerCorrect.lean` is deleted as a file, so nothing is residual (§7). U2.7 is re-priced from 1,100 to **1,900** — it owns a 5,551-line cluster whose `Lower.source_*` kit is re-proved against fourteen arms and which absorbs ≈740 relocated lines — and `01-DESIGN.md` §7.3's `Lower.lean` row from 850 to **1,850**, the file being 1,106 today and the designated recipient of the relocation |

**One finding is corrected rather than accepted.** The claim that an over-applied eliminator "has
no source derivation at all" is too strong for the rule as it stood: `mkApps f (as ++ [a])` is
`.app (mkApps f as) a`, so `SEval.beta` can fire at the outermost application whenever the branch's
value is a λ, with the un-generalised ι inside. The finding's *conclusion* stands and is acted on.
Under the un-generalised rule an over-applied spine is simulated only when a branch happens to
return a function, and §6 step 3's derivation of `extra = []` is unsound in exactly the cases where
it is not. Generalising removes both. It does not remove the β arm's `elimApp` inversion (fidelity
F6): the β route survives generalisation, and §6's reading (iii-a) is what handles it.

---

## 14. Wave-2 delivery findings

The units that built §§4–8's amended architecture (U2.5–U2.10, G2) each carry a machine-checked
finding against what this document or `01-DESIGN.md` printed. Folded into `01-DESIGN.md` §2.4,
which §4/§5's signatures are now transcribed against; recorded here, append-only, as this wave's
own record of what its own delivery found.

| # | Text as printed here or in `01-DESIGN.md` | What delivery found | Landed instead | Unit |
|---|---|---|---|---|
| **D1** | §8's `LowerEnv` (`01-DESIGN.md` §4.8) prints `specBlocks : BlockBodiesLambda Σ⁺` as one of nine clauses, unremarked | **Unsatisfiable at every specification environment the five programs produce**: `BlockBodiesLambda Σ⁺` quantifies over every `LowerBlock` over `Σ⁺`, and a single declared non-λ body (`Unit.unit`'s shape, present once per file in all five programs, and in G1's own `Σ⁺`) is a one-member block that refutes it | Landed verbatim, REFUTED as printed: `LowerEnv Σ⁺ Σ` is uninhabited on every realistic `Σ⁺`. No repair landed; the obligation is stated for U3.1/U3.2/U3.3 in `01-DESIGN.md` §2.4/§4.8 | U2.8 |
| **D2** | §5's `SEval.le` (`01-DESIGN.md` §4.3) prints an unconditional `env ≤ env' → SEval env … → SEval env' …` | **False**: `deltaC`'s `hnd` is negative in `env`, and `CasesOnShape` is monotone the wrong way for it | Gains a premise `hcs`; no consumer exists tree-wide | U2.6 |
| **D3** | §8's `SpecEnv.erasesEnv` (via `01-DESIGN.md` §4.8) prints one premise, `hdeps` | `SpecEnv`'s fields never mention `bo`, so `ErasesEnv`'s `defns` clause cannot be derived from `hdeps` alone | Gains a second premise `hdefns`; U3.6 discharges it from the run's registry | U2.8 |
| **D4** | §4's `Erases.exists_of_trExprS_of_projInfo` (`01-DESIGN.md` §4.2) prints four binders | The three-way classification of `Expr.const` needs an explicit totality hypothesis not derivable from `env.WF` alone at the pin | Gains a fifth binder `hclass`; U3.4's `Origin.lean`/`UpstreamAsks` discharges it once the pin moves | U2.5 |
| **D5** | §8's `patHead`/`PatOf`/`IotaInert` (`01-DESIGN.md` §4.8) print as one live cluster | `IotaInert` is deleted with the value arms' re-keying (its ι-freedom conjunct is subsumed by N21); `patHead`/`PatOf` are then consumer-free | `IotaInert` deleted; `patHead`/`PatOf` left for U3.6 to delete with `ErasesEnv.lean` | U2.5, U2.8 |
| **D6** | `CasesOnShape` (§5, `01-DESIGN.md` §4.3) is introduced with no import-cost note | Names `isCasesOnName`, which lives in `Supported.lean`; `SourceEval.lean` therefore imports the whole shipping-code closure a wave early (a layering defect, no cycle) | Landed as is; relocation of `isCasesOnName`/`lastComponent` to a leaf module scheduled for U3.8 | U2.6 |

Also landed and filed to `doc/upstream-asks.md` for consolidation (not load-bearing): three
general facts about lean4lean's `VEnv.WF'`/`VInductDecl.WF` — `IsArity.piBody_sort`,
`CtorOf.constant_ctorResult`, `CtorOf.not_indInfo` — proved in `SourceEval.lean` for want of a
dedicated home, sorryAx-free at the pin. Natural home is `Origin.lean` alongside U2.5's
`wf'_induct_origin`/`IndInfo.constant_isArity`.

**One policy note, for §9 above.** §9 states that neither upstream ask is a hypothesis of the
simulation and that a refusal stops the wave rather than being replaced by a premise. That stance
assumed this repository could act on the fork directly. It cannot: editing lean4lean is a separate
agent's work, so U3.4 (`02-PLAN.md` §2, W3) now only *files* the two load-bearing asks and, until
the fork accepts them, every consumer takes the asked fact as the named, class-**C**,
`doc/trust.md`-tracked hypothesis `UpstreamAsks env` (`LeanToLambdaBox/Upstream.lean`) rather than
assuming the pin has already moved. This is not `IotaRelevant`'s premise reborn: the two asks are
unweakened and unrestated, the binder is discharged with no change of shape once the fork accepts
them, and a refusal is still recorded as blocking in `doc/trust.md`, not silently absorbed. See
`01-DESIGN.md` §8.3 and `02-PLAN.md`'s W3 section for the mechanism this section does not restate.
