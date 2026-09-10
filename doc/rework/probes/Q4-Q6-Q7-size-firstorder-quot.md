# Probe — Q4 (AST size), Q6 (first-order inductives), Q7 (`Quot`)

Answers to `00-REFERENCE-SPEC.md` §8 questions Q4, Q6 and Q7. Every number below is
measured, and the command that measured it is named. Measurement date 2026-09-10, at
`dev/verify` HEAD `d5a10f3`, Lean `v4.33.0-rc2`, lean4lean `6fd8a1d`, MetaRocq `1.5.1+9.1`
(opam switch `peregrine`).

**Headline.** Q4: the eliminator-declaration design costs **+4.5% to +13.6%** of `.ast`
bytes before pruning and **0%** after, provided `LBCompile.env` prunes; recommend adopting
it, with one required change to T8's statement. Q6: `FirstOrderInd` **cannot** be defined
over `VEnv` alone (`VEnv` stores no inductive declarations), and MetaRocq's `firstorder_ind`
**cannot be adopted verbatim** — as shipped it evaluates to `false` on `nat`. Q7: no
benchmark touches `Quot`; lean4lean models the `Quot.lift` ι-rule but **not** `Quot.ind`'s;
the shipping eraser emits `Quot.lift` as a **body-less axiom**, so a quotient program erases
to a stuck term. Recommend an explicit scope restriction.

---

## Method

```
cd /home/barabba/Documents/Research/Projects/Peregrine/lean-to-lambdabox
lake build VerifyBench            # exit 0; rewrites VerifyBench/ast/*.ast
```

The five `.ast` files were then parsed with a standalone S-expression reader
(`scratchpad/astan.py`, `scratchpad/cases.py`) that reproduces `peregrine-tool`'s
`PAst` grammar: `(Untyped <env> (Some <term>))`, env entries `(<kername> <decl>)`,
`decl ::= (ConstantDecl (constant_body (Some|None …))) | (InductiveDecl …)`.
Node counts are over the whole file (environment plus main term).

MetaRocq's `firstorder_ind` was evaluated directly with `coqc` on quoted PCUIC programs
(`scratchpad/fo2.v`, `fo3.v`, `fo4.v`). The proposed Lean definition was elaborated against
the pinned lean4lean (`scratchpad/probe/q6.lean`, `lake env lean`, clean).

---

## Q4 — Do the emitted eliminator declarations blow up the deliverable?

### Q4.1 What is in the five `.ast` files today

| Program | bytes | decls | inductives | constants | `tApp` | `tBox` | `tCase` | `tConstruct` | `tFix` | `tProj` | `tLambda` | `tLetIn` | `tRel` |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| Arith | 14,113 | 39 | 12 | 27 | 155 | 49 | 5 | 42 | 4 | 10 | 75 | 10 | 72 |
| Sieve | 28,207 | 54 | 13 | 41 | 305 | 96 | 28 | 58 | 10 | 8 | 142 | 43 | 203 |
| BinaryTrees | 29,680 | 59 | 17 | 42 | 369 | 111 | 20 | 84 | 10 | 9 | 123 | 36 | 178 |
| Fannkuch | 39,861 | 63 | 14 | 49 | 488 | 146 | 38 | 101 | 15 | 6 | 197 | 59 | 315 |
| Quicksort | 66,374 | 55 | 15 | 40 | 945 | 99 | 27 | 697 | 11 | 9 | 137 | 44 | 201 |

**Recursors, `casesOn`s, matchers: zero, in all five.** The shipping eraser inlines every
eliminator at the use site; the only `*.rec` name anywhere is Fannkuch's `Eq.rec`, and it is
emitted as a **body-less axiom** (`(ConstantDecl (constant_body None))`, 73 bytes), not a
recursor declaration. So today's `Σ` is entirely: type-class structures, their projection
functions, their instances, and ordinary definitions.

| Program | structure-projection functions (single-`tProj` bodies) | typeclass instances (`inst*`) | recursors | `casesOn` | matchers |
|---|---|---|---|---|---|
| Arith | 10 | 10 | 0 (`Eq.rec`: n/a) | 0 | 0 |
| Sieve | 8 | 10 | 0 | 0 | 0 |
| BinaryTrees | 9 | 11 | 0 | 0 | 0 |
| Fannkuch | 6 | 9 | 1 — `Eq.rec`, **as an axiom** | 0 | 0 |
| Quicksort | 9 | 10 | 0 | 0 | 0 |

The projection functions are exactly the class-method constants (`Add.add`, `HAdd.hAdd`,
`OfNat.ofNat`, `Max.max`, `BEq.beq`, `Append.append`, `Pow.pow`, `NatPow.pow`, …) — the
`tProj` column of `VerifyBench/STATUS.md`, seen from the declaration side. Each is 147–478
bytes. The instances are 151–989 bytes each.

### Q4.2 Which inductives are eliminated, and how often

`tCase` occurrences keyed by inductive, with the alternative counts:

| Program | eliminated inductives (occurrences) | distinct | alt counts |
|---|---|---|---|
| Arith | `Nat` (5) | 1 | 2 |
| Sieve | `Nat` (13), `Bool` (7), `Decidable` (4), `List` (4) | 4 | 2 |
| BinaryTrees | `Nat` (10), `Bool` (3), `Decidable` (3), `Prod` (2), `Tree` (1), `List` (1) | 6 | 1–2 |
| Fannkuch | `Nat` (14), `List` (10), `Decidable` (6), `Bool` (4), `Option` (2), `Prod` (2) | 6 | 1–2 |
| Quicksort | `Nat` (11), `List` (6), `Decidable` (4), `Bool` (4), `Prod` (2) | 5 | 1–2 |

Six distinct eliminated inductives is the ceiling across the whole benchmark suite, and the
union over all five is only seven: `Nat`, `Bool`, `List`, `Prod`, `Option`, `Decidable`,
`Tree`. This is the number that governs the cost, and it is small and *bounded by the
program's data vocabulary*, not by its size — which is the whole reason the answer to Q4 is
favourable.

### Q4.3 What "emit the declaration, then inline it" costs

Under T3 the runtime library gains, per eliminated inductive `I`, two declarations:
`I.rec` (T3 `recr`, an `ElimBody`) and `I.casesOn` (T3 `defn`, since `casesOn` is an
ordinary definition in terms of `rec`). Matchers do not appear: `prepare_erasure` inlines
them at the Lean level, which the current output confirms (the `_alt._@…` `tLetIn` pairs
around every `tCase` are exactly that inlining, and there are zero `match_*` constants).

Synthetic bodies for each, written in the printer's own concrete syntax with short binder
names, serialised and measured:

| Declaration | bytes | shape |
|---|---|---|
| `Bool.rec` / `Bool.casesOn` | 220 / 220 | 4 λ, 1 `tCase`, 2 alts |
| `Nat.casesOn` / `Nat.rec` | 247 / 317 | `rec` adds a `tFix` |
| `Option.*` | 279 / 279 | 5 λ |
| `Tree.casesOn` / `Tree.rec` | 284 / 387 | `rec` adds a `tFix`, 2 recursive calls |
| `Prod.*` | 291 / 291 | 5 λ, 1 alt |
| `List.casesOn` / `List.rec` | 305 / 376 | `rec` adds a `tFix` |
| `Decidable.*` | 315 / 315 | 5 λ |

Adding both per eliminated inductive, plus the environment-entry and kername overhead:

| Program | current bytes | eliminator decls added | growth | `tCase` shell bytes today | shell share |
|---|---|---|---|---|---|
| Arith | 14,113 | 640 | **+4.5%** | 573 | 4.1% |
| Quicksort | 66,374 | 3,295 | **+5.0%** | 3,686 | 5.6% |
| Sieve | 28,207 | 2,635 | **+9.3%** | 3,296 | 11.7% |
| Fannkuch | 39,861 | 3,935 | **+9.9%** | 5,264 | 13.2% |
| BinaryTrees | 29,680 | 4,044 | **+13.6%** | 6,662 | 22.4% |

"`tCase` shell" is each `tCase` node's own bytes less its discriminant and alternative
bodies — the header plus the alternatives' binder-name lists. It is the only thing the pass
layer can move.

**Three readings of the table.**

1. **Emit + inline + prune ⇒ +0%.** `elimInline` re-expands every saturated eliminator
   application into a `.case`, restoring today's term byte-for-byte (the alternative bodies
   never move; only the head does). The eliminator declarations are then referenced by
   nothing. If `LBCompile.env` drops unreferenced declarations, the deliverable is *exactly*
   today's file. This is the design's natural end state and it costs nothing.
2. **Emit + inline, no pruning ⇒ +4.5% to +13.6%,** median **+9.3%**. Even this worst case
   is well inside the noise of the 2–4× Lean-vs-Rocq gap the collaborators measure `[Z 11]`,
   and it is *bounded*: it scales with the number of distinct data types (≤ 7 here), not
   with program size. Quicksort — the largest file — takes the second-smallest hit precisely
   because its bulk is elsewhere.
3. **Emit and do *not* inline is worse, not better.** Replacing each `tCase` by a
   `casesOn` application costs a `tConst` head, a boxed motive, an `tApp` spine and one
   `tLambda` per field binder: estimated 455 / 1,921 / 2,571 / 2,627 / 3,766 bytes for
   Arith / BinaryTrees / Sieve / Quicksort / Fannkuch, i.e. **0.7–0.8×** the shell it
   removes — a saving of 1–4% of the file, against a 4.5–13.6% cost for the declarations.
   Net growth. Not inlining also forfeits peregrine's `tCase` and hands the middle-end a
   higher-order dispatch it would have to re-discover. Reject.

### Q4.4 What actually drives `.ast` size — and it is not eliminators

Measured shares of each file:

| Program | `Nat.succ` constructor nodes | share | hygienic binder names (`_@.…_hyg.n`) | share |
|---|---|---|---|---|
| Arith | 969 B (19 nodes) | 6.9% | 1,288 B | 9.1% |
| Sieve | 459 B (9) | 1.6% | 4,279 B | 15.2% |
| BinaryTrees | 1,530 B (30) | 5.2% | 3,531 B | 11.9% |
| Fannkuch | 765 B (15) | 1.9% | 6,668 B | 16.7% |
| **Quicksort** | **32,538 B (638)** | **49.0%** | 4,597 B | 6.9% |

Half of the largest file is a unary numeral tower (`42`, `49`, `12`, `214` under
`nat := .peano`), and 7–17% of every file is hygienic binder names the printer emits
verbatim. Both dwarf the eliminator-declaration cost. This is worth recording because it is
the honest framing of `[Z 11]`: the size gap is a `.peano` and a name-printing
phenomenon, and the N14 non-goal should say so rather than leave the reader to infer that
the verification design is implicated.

### Q4.5 Recommendation

**Adopt T3's runtime-library design and freeze it.** The measured cost is +9.3% median in
the un-pruned case and zero in the pruned one, against a structural benefit the spec
already argues for: it is what lets `Erases` keep ten congruence rules and produce no
`.construct`/`.case`/`.fix` (T2.4), which is the correction that removes the epicycle.
Concretely:

1. **Give `LBCompile.env` a pruning clause** and state it: `LBCompile.env Σ⁺` keeps exactly
   the declarations reachable from `LBCompile.term Σ⁺ t`. One extra `LBPass` field
   (`env`'s existing slot suffices); its `correct` obligation is that dropping unreachable
   declarations preserves `WcbvEval`, which is a standard and cheap λ□-side lemma.
2. **T8's conclusion needs an augmented environment, and today's does not have one.**
   `visitExpr_refines_erases` reads `t = LBCompile.term s'.gdecls t₀`. But `s'.gdecls` is
   what the run registered, and the run registers **no eliminators** (§Q4.1, measured);
   `elimInline` cannot δ-expand `I.rec` out of an environment that does not contain it.
   The statement must therefore be
   `∃ Σ⁺ t₀, ErasesEnv env Σ⁺ t₀ ∧ Erases env Us Δ e t₀ ∧ t = LBCompile.term Σ⁺ t₀ ∧ s'.gdecls = LBCompile.env Σ⁺`
   — the run's output environment is the *pruned* image of the specification's, not the
   specification's itself. This is a load-bearing correction to §2's T8 and to acceptance
   criterion 12; it should go into the spec before the design is frozen.
3. **Record the size measurement in the N14 ledger row** with the `.peano`/hygiene split
   above, so the non-goal is a measured statement rather than a disclaimer.

---

## Q6 — Is `FirstOrderInd` equivalent to `[L Def. 14]` / `[L Def. 6]`, and what does it take?

### Q6.1 The blocking structural fact: `VEnv` has no inductive declarations

```
.lake/packages/lean4lean/Lean4Lean/Theory/VEnv.lean:17-23
@[ext] structure VEnv where
  constants : Name → Option VConstant     -- a type only; no body, no ctor list
  defeqs    : VDefEq → Prop
  pats      : (p : Pattern) → p.RHS × p.Check → Prop
```

`VEnv.addInduct` (`Theory/Inductive.lean:316`) *consumes* a `VInductDecl` and leaves behind
only the constants' types plus the ι rules in `pats`. Nothing in `VEnv` records that `I` is
an inductive, what its constructors are, or how many parameters it has.

**Consequence.** The spec's signature `FirstOrderInd (env : VEnv) (I : Name) : Prop` (T7,
§2) **cannot be written as stated**. Two repairs, both available at the pinned rev:

* *(recommended)* quantify over the declaration list that `VEnv.WF` already provides:
  `VEnv.WF env = ∃ ds, VEnv.WF' ds env` (`Theory/Typing/Env.lean:47-52`), so
  `HasInduct env decl := ∃ ds, VEnv.WF' ds env ∧ VDecl.induct decl ∈ ds` is a legitimate
  `Prop` over `VEnv` alone. `FirstOrderInd` is then existential over `decl`.
* *(rejected)* add inductive data to `VEnv`. That is kernel theory and goes upstream by N15;
  it is also not needed.

### Q6.2 The definition

Elaborated clean against the pinned lean4lean
(`scratchpad/probe/q6.lean`, `lake env lean`, no errors, `#print axioms` = `[propext, Quot.sound]`):

```lean
/-- `decl` is one of the inductive blocks `env` was built from. -/
def VEnv.HasInduct (env : VEnv) (decl : VInductDecl) : Prop :=
  ∃ ds, VEnv.WF' ds env ∧ VDecl.induct decl ∈ ds

/-- A field / parameter / index type is first-order for a block with `n` type formers,
occurring under `k` binders: an *unapplied* reference to a known-first-order constant, or
an *unapplied* de Bruijn reference into the block's own type formers.
Mirrors MetaRocq `firstorder_type` (`PCUICFirstorder.v:43`). -/
def FOType (fo : Name → Prop) (n k : Nat) : VExpr → Prop
  | .const I _ => fo I
  | .bvar i    => k ≤ i ∧ i < n + k
  | _          => False

structure VInductDecl.FirstOrder (env : VEnv) (fo : Name → Prop) (decl : VInductDecl) : Prop where
  mono        : decl.uvars = 0
  informative : ∀ t ∈ decl.types, ∃ ℓ, t.type.piBody = .sort ℓ ∧ ℓ.IsNeverZero
  noIndices   : ∀ t ∈ decl.types, t.type.piArity = decl.nparams
  fields      : ∀ t ∈ decl.types, ∀ c ∈ t.ctors, ∀ i < c.type.piArity,
                  ∃ A, c.type.piBinders[i]? = some A ∧ FOType fo decl.types.length i A

def FirstOrderInd (env : VEnv) (fo : Name → Prop) (I : Name) : Prop :=
  ∃ decl, VEnv.HasInduct env decl ∧ VInductDecl.FirstOrder env fo decl ∧
    ∃ t ∈ decl.types, t.name = I
```

Every accessor used (`piBody`, `piArity`, `piBinders`, `VLevel.IsNeverZero`,
`VInductDecl.types/uvars/nparams`, `VInductiveType.ctors/name`) exists at the pin:
`Theory/VExpr.lean:1090-1102`, `Theory/VLevel.lean:109`, `Theory/VDecl.lean:14-16,54-58`.

`fo : Name → Prop` is the stratification MetaRocq's `firstorder_env` builds by recursion
over the declaration list; here it is a parameter, closed by well-founded recursion over
`ds` or supplied concretely (for the benchmarks, `fo = (· = ``Nat)` suffices — see Q6.4).

### Q6.3 The finding that changes the plan: MetaRocq's `firstorder_ind` is `false` on `nat`

The spec says (T7) "`FirstOrderInd` is `[S §7.3]` verbatim". **It must not be.** Computed
with `coqc` at the installed MetaRocq (`scratchpad/fo2.v`, `fo3.v`):

```
firstorder_env (⟦list nat⟧)  =  [(…,"nat", false); (…,"list", false)]
firstorder_env (⟦Tree⟧)      =  [(…,"Tree", false)]
```

`firstorder_ind` is **`false` on `nat`, on `bool`, and on every `Set`-sorted inductive.**
Isolating the two conjuncts of `firstorder_oneind` (`PCUICFirstorder.v:58-59`) for `nat`
and for a hand-written `Tree` (`fo3.v`):

```
nat  : (forallb firstorder_con ctors, negb (Sort.is_level (ind_sort o))) = (true, false)
Tree : (forallb firstorder_con ctors, negb (Sort.is_level (ind_sort o))) = (true, false)
                                        with ind_sort = sType {(Level.lzero, 0)}
```

The structural conjunct passes. The sort conjunct fails, because
`Sort.is_level` (`Common/Universes.v:1510`) is `true` for *any single level* — including
`Set` — so `negb (…)` is false for every data type. The conjunct's evident intent, visible
in its only consumer `firstorder_ind_propositional` (`PCUICFirstorder.v:141`), is
"not propositional"; the test that expresses that is `Sort.is_propositional`, not
`Sort.is_level`. **This is an upstream MetaRocq defect and should be reported there.** It
also means every downstream theorem guarded by `firstorder_ind` in this MetaRocq build is
vacuously guarded.

Two further limits of the definition, which are *by design* and survive the fix:

* `firstorder_con` checks `cstr_args ++ ind_params` alike, and `firstorder_type` rejects
  `tSort`. So any **type-parametric** inductive fails: measured `false` for `list`, `prod`
  and `option`, and `true` for `nat` and for a parameterless `Tree` (`fo4.v`).
* `firstorder_type` requires the inductive occurrence to be **unapplied** (`args = []`),
  so `List Nat` is not a first-order *type* under it either.

A third effect is a *consequence* of the sort bug and disappears with it: `TN` with a
constructor `tl : nat → TN` measures `false`, because the field type `nat` is looked up in
`Σb`, where the bug has stored `false`.

### Q6.4 Hand-check against the requested types

`FirstOrderInd` above, with `fo` the stratified closure, at the pinned Lean toolchain:

Measured metadata (`scratchpad/probe/q6b.lean`, `run_cmd` over `Lean.getEnv`):

```
Nat       levelParams=0 numParams=0 numIndices=0 ctors=[Nat.zero, Nat.succ]           type=Type
Bool      levelParams=0 numParams=0 numIndices=0 ctors=[Bool.false, Bool.true]        type=Type
Tree      levelParams=0 numParams=0 numIndices=0 ctors=[Tree.leaf, Tree.node]         type=Type
List      levelParams=1 numParams=1 numIndices=0 ctors=[List.nil, List.cons]          type=Type.{u} -> Type.{u}
Option    levelParams=1 numParams=1 numIndices=0 ctors=[Option.none, Option.some]     type=Type.{u} -> Type.{u}
Prod      levelParams=2 numParams=2 numIndices=0 ctors=[Prod.mk]                      type=Type.{u} -> Type.{v} -> Sort.{max (succ u) (succ v)}
Decidable levelParams=0 numParams=1 numIndices=0 ctors=[Decidable.isFalse, .isTrue]   type=Prop -> Type
```

| Type | `mono` | `informative` | `noIndices` | `fields` | verdict | MetaRocq `firstorder_ind` (as shipped / bug-fixed) |
|---|---|---|---|---|---|---|
| `Nat` | ✓ (0) | ✓ (`Type`) | ✓ (0 = 0) | ✓ — `zero` nullary; `succ`'s one field is the block's own former | **true** | false / **true** |
| `Bool` | ✓ (0) | ✓ | ✓ | ✓ — both ctors nullary | **true** | false / **true** |
| `Tree` (BinaryTrees) | ✓ (0) | ✓ | ✓ | ✓ — `leaf` nullary; `node`'s two fields are the block's own former | **true** | false / **true** |
| `List` | ✗ — `levelParams = 1` | ✓ | ✓ (1 = 1) | ✗ — the parameter binder is `Type u`, a `.sort` | **false** | false / **false** |
| `Option` | ✗ — `levelParams = 1` | ✓ | ✓ | ✗ — same | **false** | false / false |
| `Prod` | ✗ — `levelParams = 2` | ✓ | ✓ (2 = 2) | ✗ — two `.sort` parameters | **false** | false / false |
| `Decidable` | ✓ (0) | ✓ (result `Type`) | ✓ (1 = 1) | ✗ — the parameter binder is `Prop`, a `.sort`; both ctors' fields are `Prop`-typed | **false** | false / false |
| `List Nat`, `Nat × Nat` | — | — | — | — | **not in the domain**: the predicate is on the *declaration*, not on an instantiation | false / false |

Note that `noIndices` as stated (`piArity = nparams`) is satisfied by all seven — it excludes
*indices*, not parameters. The parametric types are excluded by `mono` and by `fields`, which
is the same pair of reasons MetaRocq's `firstorder_con` excludes them.

**Return types of the five benchmark programs** — read off the sources
(`VerifyBench/{Arith,Sieve,Quicksort,BinaryTrees,Fannkuch}.lean`):

| Program | erased subject | result type | `FirstOrderInd`? |
|---|---|---|---|
| Arith | `benchArith : Nat → Nat` | `Nat` | **yes** |
| Sieve | `countPrimes : Nat → Nat` | `Nat` | **yes** |
| Quicksort | `quicksortBench : Nat → Nat` | `Nat` | **yes** |
| BinaryTrees | `binaryTreesSimple : Nat → Nat` | `Nat` | **yes** |
| Fannkuch | `runBenchmark` (via `fannkuch : Nat → Nat`) | `Nat` | **yes** |

`binaryTreesMain : Nat → Nat × List Nat × Nat` exists in the source but is **not** the
erased subject; `binaryTreesSimple` is. So **`Nat` alone discharges T7 for all five
programs**, and `T10`'s `FirstOrderInd env ``Nat` is the whole requirement.

**Consequence for acceptance criterion 8.** As written it demands `decide = true` on
`List Nat` and `Nat × Nat`. Neither the paper's predicate nor the definition above covers a
polymorphic inductive, and no benchmark needs it. Either (a) **narrow criterion 8** to
`Nat`, `Bool` and `Tree` — which is faithful, sufficient, and what `[L Def. 14]`'s "usual
data types like `bool`, `nat`, or `Z`" says — or (b) **generalise the predicate** to admit
a parameter whose *instantiation* is first-order (`fo`-headed rather than `.sort`-typed),
which is a genuine strengthening beyond both papers and should be costed separately. **(a)
is the recommendation**; adopting (b) silently under the name "verbatim `[S §7.3]`" would
repeat the mis-citation this rework exists to remove.

### Q6.5 Relation to `[L Def. 6]` and `[L Def. 14]`

* **`[L Def. 14]` (data-type)**: *"an inductive type `D` whose constructors expect only
  arguments of type `D` or of type another data-type"*. This is `VInductDecl.FirstOrder`'s
  `fields` clause **exactly** — the two disjuncts of `FOType` are Letouzey's two, and the
  induction over the stratification `fo` is his "another data-type". `mono` and `noIndices`
  are implicit in Def. 14's setting (Letouzey's data-types are parameterless) and must be
  stated explicitly here. **Verdict: `fields` ≡ Def. 14; the definition as a whole is
  Def. 14 plus two explicit hygiene clauses.**
* **`[L Def. 6]` (logic-free)**: *"a type `T` such that for all closed normal `t : T`,
  `E(t) = t`"*. This is **semantic, not syntactic** — a property of the type's closed
  normal inhabitants. It is **not** what `FirstOrderInd` defines; it is what
  `firstorder_no_box` (T7) must **prove** about a `FirstOrderInd` type. The `informative`
  clause (`IsNeverZero`, no `Prop`) is the syntactic sufficient condition, and the proof
  obligation is: a value of a `FirstOrderInd` type is a constructor spine all of whose
  arguments are again of `FirstOrderInd` type, hence none is `Erasable`, hence `Erases`
  produces no `.box` — which is precisely `informativeType_not_erasable`
  (`FirstOrder.lean:103-155`), the ~55 lines §4.1 already schedules for reuse.
  **Verdict: Def. 6 ≠ `FirstOrderInd`; Def. 6 is `firstorder_no_box`'s conclusion, and
  `FirstOrderInd ⇒ Def. 6` is the theorem.** The fidelity table (§3.5, row `[L Def. 6]/[L
  Def. 14]`) currently conflates them under one counterpart and should be split into two
  rows.
* **`[S §7.3]` `firstorder_ind`**: ≡ Def. 14 modulo the sort conjunct, which as shipped is
  wrong (Q6.3). **Cite it as the origin; do not claim to transcribe it.**

### Q6.6 What a decidable checker needs

Criteria 8 and 13 require `by decide`. `FirstOrderInd` over `VEnv` is **not** decidable —
`HasInduct` is existential over the declaration list, and `informative` quantifies over
level valuations (`IsNeverZero a := ∀ ls, a.eval ls ≠ 0`). The decidable checker must
therefore live on the **`Lean.Environment`** side and be connected by `PrimSpec`:

```lean
def firstOrderIndB (env : Lean.Environment) (fuel : Nat) (I : Name) : Bool
```

Its ingredients, all available from `Lean.InductiveVal` without any `MetaM`:

1. `iv.levelParams == []` — `mono`. Decidable on `List Name`.
2. `iv.numIndices == 0` and `iv.numParams == 0` — `noIndices` and the parameterless
   restriction. Both are `Nat` fields.
3. **not `Prop`-valued**: `iv.isRec`-independent; read the sort at the end of `iv.type`'s
   Π-telescope and require it not to be `Sort 0`. Purely syntactic on `Expr`; no
   `inferType`, no `whnf` — the type former's type is already a telescope of sorts.
4. For each `c ∈ iv.ctors`, walk `(getConstInfo c).type`'s Π-binders past `numParams` and
   require each binder type to be either `.const J _` with `firstOrderIndB env fuel' J`, or
   `.const K _` with `K ∈ iv.all` (the block's own formers — Lean uses constants, not de
   Bruijn indices, where PCUIC uses `tRel`, and this is the one representational deviation
   from `firstorder_type` that must be documented).
5. **Termination**: `fuel`, decremented at the recursive call, exactly as
   `firstorder_env'`'s recursion over a *shorter* declaration list. A `fuel` of
   `env.constants.size` is always enough. The alternative — memoise into a
   `NameMap Bool` mirroring `firstorder_env` — is closer to the paper and worth preferring
   if the proof of adequacy is easier over a table than over fuel.
6. **The adequacy lemma**, which is what makes the `decide` meaningful:
   `firstOrderIndB lenv fuel I = true → FirstOrderInd env fo I`, under
   `PrimSpec.env_connect lenv env`. It needs one new `PrimSpec` obligation beside
   `lookup_adequate`: that `getConstInfo I` returning an `inductInfo` with constructors
   `cs` and `numParams`/`numIndices`/`levelParams` corresponds to a `VInductDecl` in
   `env`'s declaration list with matching `types`/`ctors`/`nparams`/`uvars`. This is a
   **fifth `PrimSpec` field**, class **D**, and the spec's four-field list (T8) should be
   amended to five rather than have it smuggled in.

Cost estimate: the checker and its `Decidable` instance are ~60 lines; the adequacy lemma
is the real work and is bounded by how much of `TrEnv`'s inductive case is already proved
upstream.

---

## Q7 — `Quot`

### Q7.1 Do the benchmarks touch it?

**No.** Measured:

```
grep -c Quot VerifyBench/ast/*.ast        →  0 in all five
grep -n 'Quot\|Quotient\|Setoid' VerifyBench/*.lean  →  no matches
```

Neither the erased environments nor the Lean sources mention `Quot`, `Quot.mk`, `Quot.lift`,
`Quot.ind`, `Quotient` or `Setoid`. This is consistent with `STATUS.md`'s inductive
inventory (`Nat`, `List`, `Prod`, `Option`, `Bool`, `Decidable`, `PUnit`, `Tree`, plus the
class structures) and with the axiom inventory (only Fannkuch's `Eq.rec`). Note that
`Quot.sound` *does* appear in every `#print axioms` line of this development — but as an
axiom of **the metatheory's own proofs**, not of any erased program, and it is `Prop`-valued
so `ErasableAxioms` (T9) absorbs it.

### Q7.2 Does lean4lean model the `Quot` ι-rule?

**Yes for `Quot.lift`; no for `Quot.ind`.** At the pinned rev:

```
.lake/packages/lean4lean/Lean4Lean/Theory/Quot.lean:11
  def quotDefEq := vdefeq(α r β f c a => @Quot.lift α r β f c (Quot.mk r a) ≡ f a)

.lake/packages/lean4lean/Lean4Lean/Theory/Quot.lean:16-21
  def VEnv.addQuot (env : VEnv) : Option VEnv := do
    let env ← env.addConst ``Quot     quotConst
    let env ← env.addConst ``Quot.mk  quotMkConst
    let env ← env.addConst ``Quot.lift quotLiftConst
    let env ← env.addConst ``Quot.ind  quotIndConst
    env.addDefEq quotDefEq
```

Three facts that matter for the design:

1. **The rule is a `VDefEq`, not a `pats` entry.** It reaches `IsDefEq` through the
   environment's `defeqs` field, *not* through the ι-reduction registry that
   `VEnv.addRecRule` populates for inductives. So T4's `SEval` cannot get quotient
   reduction from whatever mechanism it uses for `iota`; it would need its own rule keyed
   on `quotDefEq`, or an appeal to `SEval.defeq`.
2. **`Quot.ind` has no computation rule in the model,** although lean4lean's *executable*
   checker implements one (`Lean4Lean/Quot.lean:106-120`, `quotReduceRec` handles both
   `Quot.lift` at `mkPos = 5` and `Quot.ind` at `mkPos = 4`). Theory and implementation
   diverge here. Since `Quot.ind`'s motive is `Prop`-valued this is sound to omit for
   typing, but it is a fidelity gap: **kernel theory, so N15 sends it upstream** as a
   lean4lean note, not a row of this repository's ledger.
3. The `Verify` side is complete for what the theory has:
   `Verify/Environment/Basic.lean:86-118` (`AddQuot1`/`AddQuot`),
   `Verify/Environment/Quot.lean` (`addQuot.WF`, `T1_tr`…`T4_tr`), reaching `TrEnv'.quot`.
   So a `Quot`-containing `Lean.Environment` *does* translate; the gap is purely in the
   reduction behaviour of `Quot.ind`.

### Q7.3 What does the shipping eraser do with `Quot`?

It emits the quotient primitives as **body-less axioms**, which makes a quotient program
**stuck**, not wrong. Traced:

* `Quot.mk`, `Quot.lift`, `Quot.ind` are `ConstantInfo.quotInfo`. `visitConstApp`
  (`Erasure.lean:672-690`) asks `getCasesInfo?` (no) then `getCtorArity?` (no — a
  `quotInfo` of kind `.ctor` is not a `ctorInfo`), so it falls through to the general
  constant path.
* `visitMutual` (`Erasure.lean:873-877`) then matches
  `ci.value? (allowOpaque := true)`, which is `none` for a `quotInfo`, and takes
  `| .none, _, _ => … return ← addAxiom name`.
* `addAxiom` (`Erasure.lean:184-187`) registers `(kn, .constantDecl ⟨.none⟩)`.

So `Quot.lift f h (Quot.mk r a)` erases to an application whose head is an axiom. Under
λ□'s `WcbvEval` an axiom is a `.const` with no body: it is a `Value`/`atom`, and the
application never reduces. The eraser exits 0 and writes a well-formed `.ast` that
`peregrine validate` accepts and that computes nothing. This is the **same failure class**
as the sparse-`casesOn` finding in `VerifyBench/STATUS.md` — silently wrong output rather
than an error — and it should be recorded next to it. It is *not*, however, a soundness
break for the verification: a stuck term simply falsifies the capstone's `WcbvEval`
conclusion rather than proving a false one, and the scope restriction below keeps it out.

### Q7.4 Does `[L Def. 14]`'s "closed inductive term reduces to a constructor" survive quotients?

**Partly, and not in a way worth relying on.** `Quot α r` is not an inductive: it has no
`ctors` field, no ι rules in `pats`, and `VInductDecl.FirstOrder` cannot even be stated
about it (`HasInduct` finds no `VDecl.induct` for it — it arrives through `VDecl.quot`).
A closed value of type `Quot α r` *is* headed by `Quot.mk`, which is constructor-*like*
(`AddQuot1 ``Quot.mk .ctor`), so Letouzey's premise holds informally. But:

* `Quot.mk` erases to an **axiom**, not to a `.construct` (Q7.3), so the erased value is not
  a constructor block and `firstorder_no_box`'s "the answer is a constructor spine" is
  false of it.
* `Quot.sound` is `Prop`-valued and boxes harmlessly; `Quot.lift`'s ι-rule would have to be
  reproduced on the λ□ side by an `ElimBody`-style obligation of its own — which T3 already
  anticipates with `ErasesDecl.quot` (`ElimBody env .quot body`), but which has no
  `pats`-registry counterpart on the source side to be checked against (Q7.2.1).

So Def. 14 does not extend to quotients for free; supporting `Quot` means defining
`Quot α r`'s first-orderness *ad hoc* and giving `Quot.mk`/`Quot.lift` a λ□ realisation
(`Quot.mk` ↦ identity, `Quot.lift f h` ↦ `f`, the standard erasure) with its own
correctness lemma against `quotDefEq`.

### Q7.5 Recommendation

**Explicit scope restriction, not support.** Add to §5 as **N16**:

> | N16 | `Quot`/`Quotient` primitives | a conjunct of the decidable `Supported env e` over `e` **and its dependency closure**: no `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`, `Quot.sound` occurs in a *computationally relevant* position | The shipping eraser emits them as body-less axioms (`Erasure.lean:873-877`), so a quotient program erases to a stuck term; lean4lean models `Quot.lift`'s ι-rule as a `VDefEq` (`Theory/Quot.lean:11`) but not `Quot.ind`'s; and `[L Def. 14]` does not extend to a non-inductive type former. No VerifyBench program touches any of them (measured, Q7.1) |

Three riders:

1. **`Quot.sound` must not be excluded** — it is `Prop`-typed, hence `Erasable`, hence
   boxed, and it is in the closure of realistic Lean programs. `ErasableAxioms` (T9) covers
   it. `Supported`'s exclusion must be of *relevant* occurrences only, or it will
   re-create the 0/5 coverage problem N9 and `ErasableAxioms` exist to fix.
2. **Delete `ErasesDecl.quot` from T3** (§2, the `quot` rule of `ErasesDecl`) or mark it
   class **E**. As the spec stands it promises an `ElimBody env .quot body` obligation that
   nothing constructs, nothing consumes, and no `pats` entry validates. Carrying it as an
   unused rule of the environment relation is precisely the dead-rule pattern §4.3 deletes
   elsewhere.
3. **Raise the `Quot.ind` theory/implementation divergence upstream** (lean4lean note, not
   a ledger row here, per N15): `quotReduceRec` reduces `Quot.ind`, `quotDefEq` does not
   model it.

---

## Findings to raise (not fixed here)

| # | Where | Finding |
|---|---|---|
| F1 | MetaRocq `PCUIC/PCUICFirstorder.v:59` | `firstorder_oneind`'s `negb (Sort.is_level (ind_sort ind))` conjunct is `false` for every `Set`/`Type`-sorted inductive, so `firstorder_ind` is `false` on `nat`, `bool` and every data type; the intended test is propositionality. Verified by `vm_compute` at `1.5.1+9.1`. Every theorem guarded by `firstorder_ind` is vacuously guarded. Report upstream |
| F2 | `LeanToLambdaBox/Erasure.lean:873-877` (shipping) | `Quot.mk`/`Quot.lift`/`Quot.ind` reach the `ci.value? = none` arm and are emitted as body-less axioms. The erased program is stuck, exits 0 and passes `peregrine validate`. Same failure class as the sparse-`casesOn` finding. **Raise, do not patch** |
| F3 | lean4lean `Theory/Quot.lean:11` vs `Lean4Lean/Quot.lean:106` | The theory models only `Quot.lift`'s ι-rule; the executable checker reduces `Quot.ind` too. Kernel theory — upstream by N15 |
| F4 | `00-REFERENCE-SPEC.md` §2 T7 | `FirstOrderInd (env : VEnv) (I : Name)` is unwritable as stated: `VEnv` stores no inductive declarations (`Theory/VEnv.lean:17-23`). Use `VEnv.WF`'s declaration list (Q6.2) |
| F5 | `00-REFERENCE-SPEC.md` §2 T8 | The conclusion `t = LBCompile.term s'.gdecls t₀` cannot hold under T3's design: the run registers no eliminator declarations (measured, 0 in all five `.ast`), so `elimInline` has nothing to δ-expand. Needs the augmented-environment form of Q4.5(2) |
| F6 | `00-REFERENCE-SPEC.md` §7 criterion 8 | `List Nat` and `Nat × Nat` are outside both `[S §7.3]`'s and `[L Def. 14]`'s predicates and outside the definition of Q6.2, and no benchmark needs them (all five return `Nat`). Narrow the criterion to `Nat`, `Bool`, `Tree` |
| F7 | `00-REFERENCE-SPEC.md` §3.5 | `[L Def. 6]` (logic-free) and `[L Def. 14]` (data-type) share one fidelity row. They are different objects: Def. 14 is `FirstOrderInd`'s `fields` clause; Def. 6 is `firstorder_no_box`'s *conclusion*. Split the row |
| F8 | `00-REFERENCE-SPEC.md` §2 T8 | `PrimSpec` needs a fifth field — inductive-declaration adequacy (`getConstInfo I : inductInfo` ↔ a `VInductDecl` in `env`'s list) — for `firstOrderIndB`'s adequacy lemma. Amend the four-field list |

## Artefacts

* `scratchpad/astan.py`, `scratchpad/cases.py` — the `.ast` S-expression reader and counters
* `scratchpad/ast.json` — per-declaration node counts for all five programs
* `scratchpad/fo2.v`, `fo3.v`, `fo4.v` — the MetaRocq `firstorder_ind` computations (F1)
* `scratchpad/probe/q6.lean` — the `FirstOrderInd` definition, elaborated clean at the pin
* `scratchpad/probe/q6b.lean` — the inductive metadata behind the Q6.4 table
