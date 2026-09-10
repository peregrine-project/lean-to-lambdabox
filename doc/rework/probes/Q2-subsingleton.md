# Q2 — the subsingleton / large-elimination criterion in lean4lean @ 20ec229

**Probe date** 2026-09-10. **Pin** `.lake/packages/lean4lean` = `20ec229f1a8c6358f3b3852c4e27d2be523d1b87`.
**Artefacts** `doc/rework/probes/Q2-probe.lean` (338 lines, compiles under `lake env lean`, **one**
`sorry`). Method: read `Theory/Inductive.lean`, `Theory/VDecl.lean`, `Theory/Typing/{InductiveLemmas,
InductiveParams,EnvLemmas,Env,Pattern,Basic}.lean`, `Verify/Environment/{Basic,Lemmas}.lean`,
`Tests/{ShapeDecide,IotaShape}.lean`, `Inductive/Add.lean`; MetaRocq `PCUICElimination.v`,
`Extract.v`, `EWcbvEval.v`; then build the fixture.

---

## 0. Verdict in five lines

1. **Yes, there is an upstream definition** — `VInductDecl.LargeElim` (`Theory/Inductive.lean:226`),
   wired into `VInductDecl.WF.universes`, hence into `VEnv.WF` through `VDecl.WF.induct`. It has a
   decidable syntactic half (`LargeElimShape`) and is validated against the real kernel in
   `Tests/IotaShape.lean`. It is used by **nothing** outside `Theory/Inductive.lean` and the tests.
2. **The derivation from `env.WF` is missing exactly one lemma**, and it is the constants-keyed twin
   of a lemma upstream already has for ι rules (`WF'.pats_origin`, `InductiveParams.lean:93`).
   That twin is **kernel-generic**: it belongs upstream (N15).
3. **The pinned excuse in this repo is false, and now measurably so.** A **pats-carrying `VEnv.WF`
   is constructible today**: `Q2-probe.lean` builds one for a concrete inductive with an ι rule.
   21 of the 22 `VInductDecl.WF` clauses are discharged; the single residue is list bookkeeping.
4. **The reference spec is wrong about `Acc.rec`.** `00-REFERENCE-SPEC.md:213–221` asserts that
   Lean's large-elimination criterion is "verbatim `[L §3.3]`'s … one constructor whose arguments
   are all logical". **It is not.** Lean's criterion admits a second kind of field —
   `VExpr.FieldInIndices` — that is *data*, not a proof. `Acc.intro`'s field `x : α` is one.
   `[S §7.1]` amendment (2) / MetaRocq `eval_iota_sing` (which substitutes `tBox` for **every**
   branch binder) is therefore **unsound for Lean's `Acc.rec`** as stated.
5. Consequence: T3's `ElimBody` needs a **two-class** field treatment, and T1's `iota_sing` needs a
   Lean-specific generalisation (or `Acc` moves to a named restriction). This is the real content of
   Q2 and it is bigger than "assemble the ingredients".

---

## 1. (a) The upstream definition and how it connects to the kernel facts

### 1.1 The definition

`Theory/Inductive.lean:226` (docstring: "thesis §2.6.2, the kernel's `isLargeEliminator`"):

```lean
def VInductDecl.LargeElim (env : VEnv) (decl : VInductDecl) (ℓ : VLevel) : Prop :=
  ℓ.IsNeverZero ∨                                        -- (0) never Prop
  (∃ t, decl.types = [t] ∧ t.ctors = []) ∨               -- (1) empty
  (∃ t c, decl.types = [t] ∧ t.ctors = [c] ∧             -- (2) singleton
    ∀ i < c.type.piArity - decl.nparams, ∃ F, c.type.piBinders[decl.nparams + i]? = some F ∧
      (env.HasType decl.uvars (c.type.fieldCtx decl.nparams i) F (.sort .zero)   -- field is a proof
        ∨ c.type.FieldInIndices decl.nparams i))                                -- OR index-determined
```

with the decidable syntactic shadow

```lean
def VInductDecl.LargeElimShape (decl) : Prop :=
  decl.types.length = 1 ∧ ∀ t ∈ decl.types, t.ctors.length ≤ 1
theorem VInductDecl.LargeElim.shape : decl.LargeElim env ℓ → ¬ ℓ.IsNeverZero → decl.LargeElimShape
```

and the supporting syntactic predicate (`Theory/Inductive.lean:107`)

```lean
def VExpr.FieldInIndices (ty : VExpr) (np i : Nat) : Prop :=
  VExpr.bvar (ty.piArity - np - 1 - i) ∈ ty.piBody.getAppArgs.drop np
```

This mirrors the executable kernel exactly: `Lean4Lean/Inductive/Add.lean:258 isLargeEliminator`
returns `true` when `stats.isNotZero`, or the block is a single type with `[]` or `[ctor]` ctors,
in which case it collects the non-parameter fields whose sort is **not** always zero (`toCheck`)
and returns `toCheck.all type.getAppArgs.contains` — "every data field occurs among the result's
arguments". `FieldInIndices` is that `getAppArgs.contains` test; the `HasType … (.sort .zero)`
disjunct is the `sortLevel!.isAlwaysZero` test.

### 1.2 The connection to `VEnv.WF`

Two clauses of `VInductDecl.WF` (`Theory/Inductive.lean:351–366`) carry it:

```lean
universes : ∀ envT, decl.addTypes env = some envT → ∃ ℓ,
    (∀ t ∈ decl.types, t.type.piBody = .sort ℓ ∧ decl.nparams ≤ t.type.piArity) ∧
    (… every field is typed at some u with imax u ℓ ≤ ℓ …) ∧
    ((∃ r ∈ decl.recs, r.uvars = decl.uvars + 1) → decl.LargeElim envT ℓ)

recs_elim : ∀ r ∈ decl.recs, (r.uvars = decl.uvars ∨ r.uvars = decl.uvars + 1) ∧
    ∀ i < r.numMotives, ∃ A, r.type.piBinders[r.numParams + i]? = some A ∧
      A.piBody = .sort (if r.uvars = decl.uvars + 1 then .param 0 else .zero)
```

So the **trigger** is `r.uvars = decl.uvars + 1` — "the recursor has one extra universe parameter",
i.e. it eliminates into `Sort (param 0)` rather than into `Prop`. And `VDecl.WF.induct`
(`Theory/Typing/Env.lean:44`) puts `decl.WF env` into the `VEnv.WF'` chain, so `env.WF` really does
contain this fact — behind an inversion.

**Kernel-side link.** `TrConstant` (`Verify/Environment/Basic.lean:21`) fixes
`ci.levelParams.length = ci'.uvars`, and `AddInduct.recs : Forall₂ (TrRecursor …) rvals decl.recs`
ties each `Lean.RecursorVal` to its `VRecursor`. Hence the trigger reads, on the Lean side, exactly:

> `rval.levelParams.length = ival.levelParams.length + 1`

which is what `Lean.RecursorVal` records for a large eliminator. No new kernel predicate is needed
to *detect* the situation from a `Lean.Environment`.

### 1.3 What is *not* connected

`grep -rn "LargeElim" Lean4Lean` outside `Theory/Inductive.lean` returns **only**
`Tests/ShapeDecide.lean:77` (a `Decidable` instance for `LargeElimShape`) and `Tests/IotaShape.lean`
(a meta-level checker). There is **no theorem** of the form `env.WF → … → decl.LargeElim …`, and no
statement relating `LargeElim` to `Lean.InductiveVal`/`RecursorVal`. The ingredients exist; the
assembly does not, exactly as the review said.

`Tests/IotaShape.lean:569–578` is nevertheless a valuable calibration table, run against the real
kernel (`largeElimClause I` returns `(clause, residual-fields-needing-a-typing-check)`):

| `I` | clause | residual |
|---|---|---|
| `Nat` | 0 (never Prop) | — |
| `False` | 1 (no constructor) | — |
| `Eq` | 2 (one constructor) | `[]` |
| `And` | 2 | `[0, 1]` (both fields are proofs) |
| `Acc` | 2 | `[1]` — **field 0 is index-determined, not a proof** |
| `Or` | *none* — two constructors, correctly rejected | — |

---

## 2. (b) Stating and deriving Fig. 18's side condition for a Lean `rec` application

### 2.1 What Fig. 18 actually asks for

MetaRocq (`PCUIC/PCUICElimination.v:45`):

```coq
Definition Subsingleton Σ ind :=
  forall mdecl idecl, declared_inductive Σ ind mdecl idecl ->
  forall Γ args u n Σ', wf_ext Σ' -> strictly_extends_decls Σ Σ' ->
    Is_proof Σ' Γ (mkApps (tConstruct ind n u) args) ->
      #|ind_ctors idecl| <= 1 /\ squash (All (Is_proof Σ' Γ) (skipn (ind_npars mdecl) args)).
```

It is **semantic**, **conditional on the constructor application being a proof** (hence vacuous for
computational inductives), and it says two things: *≤ 1 constructor*, and *every non-parameter
argument is itself a proof*. It is what licenses `EWcbvEval.eval_iota_sing`
(`Erasure/EWcbvEval.v:162`), which evaluates the single branch under
`substl (repeat tBox #|n|) f` — **every** branch binder becomes `□`.

MetaRocq **derives** it, it does not assume it: `elim_restriction_works_kelim`
(`PCUICElimination.v:589`) proves `Subsingleton Σ ind` from `wf_ext Σ`, `declared_inductive`, and
the kernel's elimination flag `ind_kelim idecl ∉ {IntoPropSProp, IntoSProp}`, via
`Is_proof_mkApps_tConstruct` (whose engine is `check_ind_sorts_is_propositional`, read off the
inductive's own `on_inductive` well-formedness data). That is the template to copy.

### 2.2 The Lean statement

Two predicates, both on the environment, neither on a term:

```lean
/-- The declaration that introduced `I`, recovered from `env.WF`. -/
structure InductOrigin (env : VEnv) (I : Name) : Prop where
  decl  : VInductDecl
  env₀  : VEnv
  wf    : decl.WF env₀
  add   : env₀.addInduct decl = some env₁
  le    : env₁ ≤ env
  mem   : ∃ t ∈ decl.types, t.name = I

/-- Fig. 18's side condition, transposed: `I` is a Prop-valued inductive whose recursor was
    admitted for large elimination, so it has at most one constructor and every non-parameter
    field of it is either a proof or determined by the result's indices. -/
def SubsingletonElim (env : VEnv) (I : Name) : Prop :=
  ∃ (decl : VInductDecl) (t : VInductiveType) (ℓ : VLevel),
    decl.types = [t] ∧ t.name = I ∧ ¬ ℓ.IsNeverZero ∧
    (t.ctors = [] ∨ ∃ c, t.ctors = [c] ∧
      ∀ i < c.type.piArity - decl.nparams, ∃ F, c.type.piBinders[decl.nparams + i]? = some F ∧
        (Proof:  env.HasType decl.uvars (c.type.fieldCtx decl.nparams i) F (.sort .zero))
        ∨ (Index: c.type.FieldInIndices decl.nparams i))
```

### 2.3 The derivation chain, link by link

Given `henv : env.WF` and a recursor name `R` with `env.constants R = some ci` and
`ci.uvars = decl.uvars + 1`:

| # | step | status at 20ec229 |
|---|---|---|
| L1 | `env.WF → ∃ ds, env.WF' ds` | **definition** (`Env.lean:52`) |
| L2 | `WF' ds env → env.constants n = some ci → ∃ decl … (VDecl.induct decl :: ds₀) <:+ ds ∧ decl.WF env₀ ∧ env₀.addInduct decl = some env₁ ∧ env₁ ≤ env ∧ n names a type/ctor/rec of decl` | **MISSING** — but the ι-keyed twin `WF'.pats_origin` (`InductiveParams.lean:93`) exists and its proof is 25 lines; the constants-keyed version needs `VDecl.WF.constants_eq_or_induct` (mirroring `pats_eq_or_induct'`, `InductiveParams.lean:71`) plus `addInduct_constants_origin` (whose pieces `addConst_foldlM_constants_inv` :391, `addTypesCtorsRecs_eq` :410 are already there) |
| L3 | `decl.WF env₀ → recs_elim` gives the extra-universe trigger from `ci.uvars` | **present** |
| L4 | `decl.WF env₀ → universes` gives `ℓ` and `LargeElim envT ℓ` | **present** |
| L5 | `LargeElim.shape` gives ≤ 1 type former, ≤ 1 constructor when `¬ℓ.IsNeverZero` | **present** (`Inductive.lean:242`) |
| L6 | transport the field typings from `envT` to `env` | **present** (`HasType.mono`, `addInduct_le`, `WFPrefix.le`) |
| L7 | *use* it: turn "field is a proof" into "the erased minor may take `□` there", and "field is index-determined" into "the erased minor takes the recursor's index argument there" | **PIPELINE**, and see §4 |

So: **one missing upstream lemma (L2)** plus **one new pipeline theorem (L7)**.

---

## 3. (c) Where each half belongs, and the minimal asks

### 3.1 Kernel-generic — send upstream (N15)

**Ask 1 (the load-bearing one). `VEnv.WF'.consts_origin`.** The constants-keyed twin of the existing
`WF'.pats_origin`:

```lean
theorem VEnv.WF'.consts_origin {ds env} (H : env.WF' ds) {n ci} (h : env.constants n = some ci) :
    (∃ ci', VDecl.WF … )  -- axiom / def / opaque / mutualDef / quot case
  ∨ (∃ (decl : VInductDecl) (ds₀) (env₀ env₁),
        (VDecl.induct decl :: ds₀) <:+ ds ∧ env₀.WF' ds₀ ∧ decl.WF env₀ ∧
        env₀.addInduct decl = some env₁ ∧ env₁ ≤ env ∧
        (n, ci) ∈ decl.consts)
```

Justification to upstream: it is the exact analogue of a lemma they already wrote for `pats`, it
mentions nothing about erasure, and it is the only way any client can use `VInductDecl.WF` at all —
today `decl.WF` is reachable only if you built the environment yourself. It is also a prerequisite
for `patsStrong` (their own open obligation), whose proof needs "the redex's recursor comes from a
well-formed block".

**Ask 2 (small, cheap). A normal form for ι-reduct holes.** `Pattern.RHS.Generic` /
`Pattern.RHS.Uses` for `SimplePattern.iotaRHS'` has no simp normal form; upstream already has the
countP lemmas (`iotaPaths_countP_isLeft/isRight`, `Pattern.lean:548,556`) but not

```lean
theorem SimplePattern.iotaRHS'_Uses {r c k nind cnp nf rhs hc} {x} :
    (iotaRHS' r c k nind cnp nf rhs hc).Uses x ↔ x ∈ iotaPaths r c k nind cnp nf
theorem SimplePattern.iotaRHS'_Generic {…} (h1 : ∀ i < k, m2 (.inl (varN_pathOf _ i _)) = .bvar …) … :
    (iotaRHS' …).Generic m2 (k + nf)
```

This is the *only* thing that stopped the probe below from being `sorry`-free. It is pure list
bookkeeping about their own definition.

**Ask 3 (optional, states the criterion for clients).**
`VInductDecl.WF.largeElim_of_rec : decl.WF env → r ∈ decl.recs → r.uvars = decl.uvars + 1 →
∃ ℓ, decl.LargeElim envT ℓ` — a one-line packaging of `universes` that saves every client the
`addTypes` plumbing. Nice to have, not load-bearing.

### 3.2 Pipeline-specific — stays here

* Turning `SubsingletonElim` into the shape of the **emitted λ□ recursor body** (T3 `ElimBody`).
* The classification of fields into *proof* / *index-determined* and what each erases to (§4).
* Any statement mentioning `LBTerm`, `Erases`, `□`, or `WcbvEval`.

---

## 4. The finding that changes the design: Lean's criterion is **not** Coq's

`00-REFERENCE-SPEC.md:213–221` says the criterion is "verbatim `[L §3.3]`'s 'zero constructor
(empty inductive)' or 'one constructor whose arguments are all logical'", and concludes that
`Acc.rec` is inside the fragment. **The second disjunct of `LargeElim` clause (2) refutes this.**

Lean admits large elimination for a `Prop` whose single constructor has fields that are **not**
proofs, provided each such field **occurs among the indices of the constructor's result type**
(`FieldInIndices`). The kernel's own code (`Inductive/Add.lean:265–275`) is explicit: it collects
the fields whose sort is not always zero and requires `type.getAppArgs.contains` each of them.

`Acc` is the case that matters, and `Tests/IotaShape.lean:578` measures it:
`largeElimClause ``Acc = some (2, [1])` — field `0` (`x : α`) is index-determined, field `1` (`h`)
is the proof. Compare Coq, where `Acc`'s `x` is a **parameter** of the inductive, so `Acc_intro` has
exactly one field, a proof, and Letouzey's "all arguments logical" holds. The difference is a
Lean-vs-Coq difference in where `x` lives, and it is invisible until you read `FieldInIndices`.

Concretely, Lean's ι rule is

```
Acc.rec motive m a (Acc.intro x h)  ↦  m x h (fun y hy => Acc.rec motive m y (h y hy))
```

Under erasure `Acc.intro x h : Acc r a` is a proof, so the discriminee erases to `□`. MetaRocq's
`eval_iota_sing` would then run the single branch with `substl (repeat tBox 3)` — boxing `x`. But
`x` is *data*: `WellFounded.fix`'s minor is `fun x h ih => F x (fun y hy => ih y hy)` and `F x` is a
real computation. **Boxing `x` produces a wrong program.**

The repair is available and is exactly what `FieldInIndices` licenses: at any well-typed redex the
index-determined field is definitionally equal to the corresponding *index argument of the
recursor* (`a` above), which is **not** erased — it sits in the recursor's spine. So the erased
recursor body must substitute, per field:

| field class | what the erased branch receives |
|---|---|
| proof (`HasType … (.sort .zero)`) | `□` |
| index-determined (`FieldInIndices`) | the recursor's index argument at the matching position |

This turns T1's amendment (2) from MetaRocq's `iota_sing` into a Lean-specific rule
`iota_sing_idx`, and gives T3's `ElimBody` a second obligation. Deriving the definitional equality
"field = index argument at the redex" needs **injectivity of the type former** applied to
`CtorResult`'s `bvarsDesc np ++ idx` — i.e. it lands squarely on lean4lean's `Injectivity.lean`
sorries and on `patsStrong`'s own stated residual ("proving it needs inversion of the redex's
typing and injectivity of the block's type formers", `EnvLemmas.lean:328–333`). That is the honest
trust picture, and it is the same seam §1 of the spec already declares.

### Options for the design

1. **Full**: add `iota_sing_idx` to T1 and the two-class field treatment to T3; `Acc.rec` is in the
   fragment, at trust class **B** (inherits `Injectivity`/`patsStrong`).
2. **Narrow (recommended for the first cut)**: define the criterion as
   `SubsingletonElim ∧ every non-parameter field is a proof` — i.e. drop the `FieldInIndices`
   disjunct — which is decidable from `LargeElim`'s first disjunct plus the typing clause, covers
   `False.rec`, `Eq.rec`, `And.rec`, `Iff.rec`, `Decidable`'s elimination, and puts **`Acc.rec` /
   `WellFounded.fix` on the restriction list N-something** with a one-line ledger row. Note that
   Lean's own code generator refuses `Acc.rec` too, so this restriction costs nothing that the
   shipping pipeline delivers today.
3. Do (2) now and (1) as a named follow-up; the criterion's statement is the same object either way.

Either way, **`00-REFERENCE-SPEC.md:213–221` and the T3 trust-class row must be amended**: the
sentence "at most one constructor, all of whose non-parameter arguments are propositions — which is
verbatim `[L §3.3]`" is false of Lean, and the `Acc.rec` claim depends on which option is taken.

---

## 5. (d) Can a pats-carrying `VEnv.WF` be constructed today? — **Yes.**

The standing claim in this repo (`IotaDischarge.lean:74`, `ProjPattern.lean:72`,
`ErasesCorrectIota.lean:728,1029`, `FirstOrderShippingIota.lean:102,339`, `SourceEvalData.lean:345`,
`SubjectReductionIota.lean:61,71`, `ColdStart.lean:1871`, `VisitExprRefines.lean:4554`) is that
`VEnv.WF` is *unconstructible* for a `pats`-carrying environment because `VEnv.Ordered` has no
`addPat` clause and `addInduct_WF` is `sorry`. Measured at the pin:

* `Theory/Typing/Lemmas.lean:265` — `| pat : Ordered env → env.PatWF p r → Ordered (env.addPat p r)`.
* `Theory/Typing/InductiveLemmas.lean:229` — `theorem addInduct_WF … : Ordered env'`, proved.
* And neither is even **needed**: `VEnv.WF env := ∃ ds, VEnv.WF' ds env`, and `VEnv.WF'.decl` takes
  `VDecl.WF.induct : decl.WF env → env.addInduct decl = some env' → VDecl.WF env (.induct decl) env'`
  directly. `Ordered` is a *consequence* (`VEnv.WF.ordered`, `EnvLemmas.lean:87`), not a premise.

### The probe

`doc/rework/probes/Q2-probe.lean` — 338 lines, one `sorry`. Fixture: a `Type`-valued unit-like block
`Q2U : Sort 1`, `Q2u : Q2U`, `Q2U.rec.{u} : ∀ (C : Q2U → Sort u), C Q2u → ∀ t, C t` with the single
rule `Q2U.rec C m Q2u ↦ m`, i.e. `uvars = 0`, `nparams = 0`, one recursor at `uvars = 1`, one ι rule.
It ends with

```lean
theorem c_wf : declU.WF VEnv.empty                        -- all 22 clauses
theorem c_env_wf     : ∃ env, VEnv.addInduct .empty declU = some env ∧ env.WF
theorem c_env_pats   : ∃ env, … ∧ env.WF ∧ ∃ p r, env.pats p r   -- the ι rule really is registered
```

Clause-by-clause cost:

| clause | how it closed |
|---|---|
| `types_uvars`, `ctors_uvars`, `rec_params`, `ctors_params` | `rfl` |
| `ctors_result`, `ctors_positive`, `rec_shape`, `rec_counts`, `rules_nodup`, `rules_ctor`, `recs_over_block`, `types_have_rec`, `rules_total`, `rule_shape`, `recs_elim` | **`by decide`**, using the `Decidable` instances of `Tests/ShapeDecide.lean` (which had to be inlined — the `Tests` modules are not in the built `.olean` set for this consumer) |
| `types_wf`, `ctors_wf`, `recs_wf` | ordinary `HasType` derivations, ~35 lines total, from `HasType.{sort,const,bvar,app,lam,forallE}`; **no `Ordered` needed** — `HasType.const` is stated at an arbitrary `Γ`, so no weakening is needed for constants |
| `universes` | `ℓ := .succ .zero`; `LargeElim` by the `IsNeverZero` disjunct; the field clause is vacuous (nullary constructor) |
| `rules_wf` (`VEnv.PatTyped`) | **the substantive one**, ~45 lines. Generic redex `Q2U.rec.{u} (bvar 1) (bvar 0) Q2u` at `Γ = [MT, CT]`, matched with `Pattern.matches_varN_const`; both `HasType` halves (redex and reduct, at the common type `(bvar 1) Q2u`) close by `HasType.app` chains with **`VExpr.inst` computing by `rfl`**; the reduct equation closes by `SimplePattern.iotaRHS'_apply`. The residual `sorry` is the `Pattern.RHS.Generic` conjunct only — see Ask 2. |

Two mechanical gotchas worth recording for whoever redoes this:

* `Pattern.Matches.app` keeps only the **left** subpattern's level list (`Pattern.lean:139–141`), so a
  recursor at `uvars = n+1` firing on a constructor at `uvars = n` matches fine. The naive worry
  ("`Matches.const` forces one `ls` for both constants") is wrong.
* Fixing `m2` as `Sum.elim g nofun` *before* giving the `Matches` derivation makes elaboration fail
  on the `Empty`-eliminator function; supply the `Matches` term first and let `m2` be inferred.

### What this means

* The nine "unconstructible" docstrings are false and should be deleted (the review's TA-01/DOC-01).
* Every ι-round guard in the current tree that was parked on that excuse — `iotaConsistent_of_shape`,
  `SEvalDataι_defeq`, the ι capstone's non-vacuity witness — **can be instantiated end to end now**,
  at a cost of roughly the 200 lines above plus Ask 2, and that is the cheapest available answer to
  the review's P1/GA-03 ("premises never jointly inhabited").
* For the rework, a fixture of this shape is the right non-vacuity guard for T3: build one Prop-valued
  singleton (e.g. `True`-like, then `And`-like) and one index-determined one (`Acc`-like), and
  discharge `SubsingletonElim` on each. The `Type`-valued fixture above is the warm-up; the
  Prop-valued one additionally exercises `LargeElim` clause (2)'s typing disjunct — which the
  `IsNeverZero` shortcut skipped here.

---

## 6. Answers, condensed

* **(a)** Yes: `VInductDecl.LargeElim` + `LargeElimShape` + `LargeElim.shape`, triggered from
  `VInductDecl.WF.universes` by `r.uvars = decl.uvars + 1` and reachable from `VEnv.WF` through
  `VDecl.WF.induct`. Decidable syntactic half in `Tests/ShapeDecide.lean`; validated against the
  real kernel in `Tests/IotaShape.lean`. Zero downstream consumers.
* **(b)** State it as `SubsingletonElim env I` (§2.2), an environment predicate, not a term side
  condition. Derive it by: `env.WF` → declaration-origin inversion (**the one missing lemma**) →
  `recs_elim` → `universes` → `LargeElim.shape` → `HasType.mono`. Everything but the inversion exists.
* **(c)** The inversion is kernel-generic → **upstream** (Ask 1), with Ask 2 (ι-reduct `Generic`
  normal form) and Ask 3 (packaging) alongside. The λ□-side consequence — what the erased recursor
  body puts in each field position — is **pipeline**.
* **(d)** A pats-carrying `VEnv.WF` **is** constructible at 20ec229; `Q2-probe.lean` builds one.
  `patsStrong`, `Injectivity`, `UniqueTyping:174` and the proj sorries are **not** in the way of
  *constructing* such an environment — they are in the way of *reasoning* with the strong system
  (`VEnv.WF.orderedStrong`) over it, which is a different and later obligation. A rework that
  consumes pats-carrying environments therefore inherits the sorry cone only where it uses
  `IsDefEq.strong`/uniqueness — i.e. in T2's `box` witness and T7's uniqueness, exactly the two
  places the spec already declares as class **B**. Constructing fixtures, proving `ErasesDecl`, and
  every `by decide` clause above are class **A**.
