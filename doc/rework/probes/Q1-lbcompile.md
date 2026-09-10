# Q1 — Can the Lean-specific compilation steps be factored as λ□→λ□ passes that reproduce `visitExpr` exactly?

**Probe date.** 2026-09-10. **Subject.** `LeanToLambdaBox/Erasure.lean` at `dev/verify`
(d5a10f3 + working tree), Lean 4.33.0-rc2.
**Method.** `lake build VerifyBench.Arith VerifyBench.BinaryTrees` (exit 0; all five
`VerifyBench/ast/*.ast` regenerated, Quicksort included, no panic this run), then structural
analysis of the five emitted `.ast` files against the eraser's source and against
`Semantics/{Eval,Substitution}.lean`'s target conventions.

---

## 0. Answer in one paragraph

**Yes, but not against `Σ`.** Every Lean-specific step is a *deterministic* function of the source
term plus data that is **static per constant** — a constructor's `(iid, cidx, npars, nfields)`,
a `casesOn`-like constant's `CasesInfo`, an inductive's `(iid, npars)`, a declaration's mutual-block
name list. None of it depends on the erasure run's state, on fresh names, or on anything the
`Erases` relation would have to guess. But three of those items are **not present in the environment
the shipping eraser emits**: the eraser never registers a `casesOn` constant, never registers a
constructor constant, and emits recursors as **axioms** rather than as T3 `recr` declarations
(measured: zero `casesOn`/`rec`/ctor `ConstantDecl`s across all five `.ast` files; `Eq.rec` appears
as a `constant_body None` axiom in `Fannkuch.ast`). So a pass whose only inputs are `(Σ, t₀)` —
T8's literal `LBCompile.term s'.gdecls t₀` — **cannot see** the information it needs. Parameterise
the passes by a **compile table `E`** (a pure function of the `Lean.Environment`, specified in
`PrimSpec` exactly as `lookup_adequate` already specifies its queries) and exact functional
equality is attainable for the whole chain, **modulo two fragment conditions that `Supported` must
carry anyway**: every `casesOn` minor is a syntactic λ, and every `casesOn`-like head is plain
(not sparse, not a per-constructor eliminator). Binder *order* is never an obstruction — both
conventions (`mkAlt`, `mkDef`) are MetaCoq-exact and constant. Binder *names* are the only real
one, and they are exactly what the two fragment conditions buy back.

---

## 1. What the eraser actually emits (measured)

| file | fix defs (block sizes) | `.case` | `.construct` | axioms | `casesOn`/`rec` decls |
|---|---|---|---|---|---|
| `Arith.ast` | 4 (all singleton) | 5 | 42 | 0 | 0 |
| `BinaryTrees.ast` | 10 (all singleton) | 20 | 84 | 0 | 0 |
| `Fannkuch.ast` | 15 (all singleton) | 38 | 101 | 1 (`Eq.rec`) | 0 |
| `Quicksort.ast` | 11 (all singleton) | 27 | 697 | 0 | 0 |
| `Sieve.ast` | 10 (all singleton) | 28 | 58 | 0 | 0 |

Four facts this fixes for the design:

1. **No mutual fix block is exercised.** 50 emitted `FixDef`s, every one a singleton. The
   mutual-block *ordering* question below is real but unexercised by the benchmark suite.
2. **Every emitted fix def actually references its fix variable** (checked by a free-index-0 scan
   under the fix binders, all five files). So `visitMutual`'s source-side recursion test
   `name_occurs` and a λ□-side self-reference test *agree* on the whole corpus.
3. **Recursors are axioms, not `ElimBody` declarations.** `Fannkuch.ast` carries
   `((MPdot (MPfile ()) "Eq") "rec") (ConstantDecl (constant_body None))`, and `Eq.ndrec` is a
   *definition* listed in `Fannkuch.ast.inlinings`. The shipping path for a recursor is
   `get_constant_kername → visitMutual → getDeclInfo?.value? = none → addAxiom`, i.e. T3's
   `ErasesDecl.ax`, **never** T3's `recr`.
4. **Constructor parameters are kept and boxed** — `(tApp (tApp (tApp (tConstruct (inductive List 0) 1 ()) tBox) hd) tl)`.
   This is an empirical answer to the spec's **Q5**: the Lean frontend does *not* drop parameters;
   `visitConstructor` builds `param_args ++ filter argmask field_args ++ extra_args`.

---

## 2. Step by step

Each row states: the information the step consumes; whether that information is recoverable from
`(Σ, t₀)` — the emitted `GlobalDeclarations` plus the pruned λ□ term — alone; and the verdict
**(a)** functional pass, **(b)** relational pass only, **(c)** must stay a case of the erasure
relation.

### 2.1 Constructor blocking + argmask — `ctorInline` — **(a)**

`visitConstructor` (`Erasure.lean:731`) needs `ci.cidx`, `ci.induct`, `ci.numParams`,
`ci.numFields`, and `register_inductive`'s `(iid, argmasks)`. At the pinned config
(`remove_irrel_constr_args = false`, N4) the argmask is `Array.replicate numFields .keep`, `filter`
is the identity, and the output is exactly `mkApps (.construct iid cidx []) (all erased args)`.

* Recoverable from `Σ`? **Only if T3 emits ctor declarations.** Under `ErasesDecl.ctor` the
  constant `c` has body `.construct iid k []`, so `ctorInline` is *literally δ on that declaration*,
  and `iid`/`cidx`/arity all come from `Σ` (`npars` from the mutual body, `nargs` from the
  `OneInductiveBody` ctor record). Under the *shipping* `Σ` there is no such declaration, so the
  pass needs the table (§3).
* Order/shape: applied form throughout, `[]` block args, extra arguments applied uniformly. Exact.
* `extern`-tagged constructors take the `addAxiom` branch only at `extern = .preferAxiom`, excluded
  by `hcfg` (N2).

### 2.2 `casesOn` → `.case` — `elimInline` — **(a) relative to a table; (b) against `Σ` alone**

`visitCases` (`Erasure.lean:768`) consumes a `CasesInfo`: `declName`, `arity`, `discrPos`,
`altsRange`, `altNumParams : Array CasesAltInfo`, plus `getConstInfo typeName` and
`register_inductive`. Motive and parameters are **dropped by position** (never visited);
`args[discrPos]` becomes the discriminant; `altsRange` selects the minors; over-application
(`args[arity:]`) is applied **outside** the `.case` node.

* `CasesInfo` is computed by Lean core (`Lean/Meta/CasesInfo.lean:56`) from the *type* of the
  `casesOn`-like constant by `forallTelescope` + `inferType`. It is a **pure function of the
  declaration**, so it is table-able — but it is **not in `Σ`**: the eraser never calls
  `get_constant_kername` on a `casesOn` head, so no `casesOn` declaration is ever emitted (measured:
  zero across five files).
* The spec's route — `elimInline` as δβ through the erased `casesOn` body, which itself δ's into
  `I.rec`'s `ElimBody` — would supply everything from `Σ`. It is coherent, but it describes an
  environment the shipping eraser does not produce (§1.3), so the *equality* in T8 cannot be taken
  at `s'.gdecls`.
* **Over-application placement is exact** either way: δβ of a saturated-plus-`k` application leaves
  the extra arguments applied to the result, which is what `visitCases`'s trailing loop builds.
* **Alt bodies differ from naïve δβ.** `visitAlt` *strips* λs off the minor
  (`lambdaOrIntroToArity`) and hands `mkAlt` the body; δβ through a recursor body would instead
  produce `(names, minor f₁ … f_j)` — a β-redex per alt. `elimInline` must therefore β-normalise the
  alt spine it creates. `IotaBridge.lean`'s lemma ("a β-chain of field applications *is* `iota_red`")
  is exactly the correctness content of that extra step, so the asset is already the right one.
* **Coverage holes visible here, both of which `Supported` must carry:**
  - *sparse `casesOn`* (`CasesAltInfo.default n`): the three-way `for … in altsRange, altNumParams, argmasks`
    zip pairs a catch-all alt with a constructor's argmask and truncates at the shortest list —
    the known `_sparseCasesOn_` miscompile.
  - *per-constructor eliminators* (`hasSideCondition` in `getCasesInfo?`): `altsRange` starts at
    `discrPos + 2`, so the side-condition argument is **dropped unvisited**, and the emitted `.case`
    has one alternative for an inductive with several constructors — a malformed λ□ `.case`.

### 2.3 `Nat` literals at `nat := .peano` — **(a), exactly**

`visitLiteral` (`:605`) maps `0 ↦ visitConstructor Nat.zero #[]` and
`n+1 ↦ visitConstructor Nat.succ #[.lit n]`. Under the spec this is `Erases.lit` (kernel unfolding
to `.app (.const Nat.succ) …`) followed by `ctorInline`. Nothing but the ctor table is consumed; no
binder names, no types, no `inferType`. **Exact functional match.** (`.machine` is excluded by
`hcfg`, N3; the `strVal` and >63-bit arms are panic sites.)

### 2.4 Structure projections — **(c), and already exact**

`visitProj` (`:634`) emits `.proj ⟨iid, indinfo.numParams, argmasks[0][:i].count .keep⟩`. At N4 the
field index is `i` verbatim. This is `Erases.proj` as specified — a rule of the relation, no pass —
and it matches the shipping output exactly. Only `(iid, npars)` is consulted, which T2.1 already
places in the environment translation.

### 2.5 Mutual / structural recursion → `.fix` — `fixIntro` — **(a) for singletons; (b) for genuine mutual blocks**

`visitMutual` (`:859`) decides recursive vs not by `name_occurs name ci.value!` on the **source**
`Expr`, allocates one fresh fvar per member of `ci.all`, erases each body with `fixvars` set (so
self-references become `.fvar`, `visitConst` `:660`), then `mkDef` abstracts them.

* **Binder order is deterministic and MetaCoq-exact, not `Σ`-dependent.** `mkDef` (`:273`) runs
  `for (n,i) in fixvarnames.reverse.zipIdx`, so the *last* block member gets `bvar 0`; `defs` is in
  `fixvarnames` order and constant `n_j` is emitted as `.fix defs j`. That is precisely
  `Substitution.lean:220`'s `fixSubst` (`index i ↦ fix l (n-1-i)`, MetaCoq's `fix_subst`). **The
  `mkDef` docstring's "may be wrong" is answerable: it is right.** Likewise `principalArgIdx := 0`
  is constant.
* **Singleton blocks** (100% of the corpus, 50/50 defs): `fixIntro` = "if the erased body of
  `ConstantDecl c` mentions `.const c`, abstract that occurrence and wrap in `.fix [⟨name, ·⟩] 0`".
  Fully functional on λ□; the `FixDef.name` is `(remove_unsafe_rec n).toString`, recoverable from
  the kername for ASCII names (`toKername`/`cleanIdent` is not injective in general → table).
* **Genuine mutual blocks**: the *order* of `defs` is `ci.all` from
  `Compiler.LCNF.getDeclInfo?` — an external datum. The δ-dependency graph over `Σ` identifies the
  SCC but not an order within it, and a different order yields different `bvar` indices and
  different `.fix … i` selectors. **Not recoverable from `Σ`**; needs the table (or the block list
  as a pass parameter). Unexercised by the benchmarks.
* **One divergence source worth a `Supported` conjunct.** `name_occurs` (`:526`) is computed on the
  *unerased* source and counts occurrences that erasure boxes away (it descends `.app`'s argument,
  `.proj`'s subject and `.letE`'s value). It can therefore classify a definition as recursive whose
  λ□ body has no self-reference, producing a `.fix` with an unused fix binder where a λ□-only
  `fixIntro` produces a plain `ConstantDecl`. Measured: **does not occur** in any of the five
  programs. The cheap fix is a decidable per-declaration side condition ("`name_occurs` agrees with
  λ□ self-reference"), checkable exactly the way this probe checked it.
* Also note `visitMutual` erases the **LCNF body** (`getDeclInfo?.value!`) in the nonrecursive
  branch but the **kernel body** (`getConstInfo n |>.value!`) for each member of a recursive block.
  N8 must cover both.

### 2.6 `Eq.rec` / `False.rec` / `@[extern]` remaps — **(c), and the spec needs a correction**

There is no remap pass in the eraser. A recursor reaches `visitMutual`, has no compiler value, and
is emitted by `addAxiom` as `ConstantDecl (constant_body None)`; the actual realizer is supplied
downstream by peregrine's `.attr` channel. Same for `@[extern]` at `extern = .preferAxiom`.

Consequence for the spec: **T3's `recr` class has no shipping counterpart.** `Acc.rec`, `Eq.rec`,
`False.rec` are, on the shipping path, `ErasesDecl.ax` occurrences whose correctness is an
`AxiomSpec` row (T9's `ErasableAxioms`), not an `ElimBody` obligation. T3 should either (i) state
`recr` as the *specification* the relational Σ uses and add an `ax`-with-`AxiomSpec` alternative
that the shipping run actually inhabits, or (ii) drop `recr` for recursors reached as constants and
keep `ElimBody` only where a `casesOn`-like constant is inlined. **This also removes Q2's urgency
from the critical path**: the subsingleton criterion is needed for `recr`, and the shipping eraser
never builds a `recr` body.

### 2.7 η-expansion to arity — **(a) relative to a table, on the fragment; (b) otherwise**

Three sites: `visitCasesEtaGo` (`:705`), `visitCtorEtaGo` (`:722`), and `visitAlt`'s
`lambdaOrIntroToArity` (`:842`, `:358`). All three route through `lambdaMonocularOrIntro` (`:334`),
which **always takes the binder name from the ∀-binder of the type**, never from the source λ
(the code's own comment: "It might be better to get it from the lambda binder").

* *Arity* is recoverable: ctor arity `= numParams + numFields = npars + nargs` (Lean core's
  `getCtorArity?` is exactly that), `casesInfo.arity` is static per constant.
* *Names* are `Meta.inferType`-derived, i.e. **not in `Σ` and not in `t₀`**. Two regimes:
  - **η-expansion of an under-applied `casesOn`/ctor head.** `inferType` of a partially applied
    constant is that constant's type instantiated, and instantiation does not rename, so the names
    are the **declaration's** ∀-binder names — *static per constant*, hence table-able and exact.
  - **`visitAlt` on a minor.** If the minor is a syntactic λ, `Meta.inferType` reproduces the λ's
    own binder names, which `Erases.lam` already carries into `t₀` — so the pass reads them off the
    minor's own `.lambda` nodes and is **exact**. If the minor is *not* a λ (η-contracted, e.g.
    `Option.casesOn o none Some`), the name comes from whatever function's type produced it — not
    static, not in `t₀`. **This is the only genuinely non-reconstructible datum in the whole chain,
    and it is already outside the fragment** (`Bridge.lean:198-200` says so — modulo that
    docstring's separately-recorded falsehood about sparse `casesOn`).
* Observed instances: `(tLambda (nNamed "c") (tLambda (nNamed "cs") (tApp … (tConstruct (inductive List 0) 1 ()) …)))`
  in `Fannkuch.ast` — names `c`/`cs` from the source pattern `| c :: cs, 0 => …`, i.e. the λ regime;
  and `(nNamed "n._@.Init.Prelude.2075127268._hygCtx._hyg.64")` in `Arith.ast`'s `Nat` case — a
  `Nat.casesOn`-type binder name, i.e. the static regime.
* One small mismatch to fix in T2: `fvar_to_name` (`:245`) maps a non-ASCII-graphic name to
  `.anon`. `Erases.lam`/`letE` as written in the spec carry `n` unfiltered. Either the relation
  applies the same filter or the passes do; it is a deterministic function of the name either way.

### 2.8 `_unsafe_rec` stripping, `macroInline`, `inlineMatchers` — **(c), source-side, not a λ□ pass**

`prepare_erasure` (`:556`) runs `replaceUnsafeRecNames`, `macroInline`, `inlineMatchers`,
`macroInline` again (and `csimp`, excluded by N1) on the **source `Expr`**, once before the
top-level term and once per registered declaration body. Matcher inlining is δβ *on Lean terms*;
it changes which constants exist in the closure and introduces the `_alt._@…` `let`-bindings visible
in every `.ast`. It cannot be a λ□ pass, and it is not a rule of `Erases` either. The theorem's
subject must be `prepare_erasure e` (with N8's kernel-typeability hypothesis carrying the
`_unsafe_rec` swap), or a source-level δ-simulation must be added. Recommend the former: it is
free, and `SEval.defeq` already provides the justification vocabulary.

### 2.9 `.inlinings` — not a term transform

`s.inlinings` is a `List Kername` side channel (`@[inline]` names, plus the
`auto_inline_typeclass_dispatch` heuristic that N5 disables). Measured payloads are small
(`Arith`: 1 entry; `Fannkuch`: 7). N11's ledger row plus the cheap true statement is the right
treatment; nothing here affects the term equality.

### 2.10 Binder-order conventions — deterministic, and *not* functions of `Σ`

Both conventions are constants of the eraser, independent of any environment:

* `mkAlt` (`:259`): names in source order, `xs.reverse.zipIdx` abstraction, so the **last** field
  binder is `bvar 0`. This matches `Semantics/Eval.lean:141-151`'s `iota_red`
  (`substList ((args.drop np).reverse) body`), which is MetaCoq's. The docstring's "the other way
  around led to segfaults" is answerable: it is the MetaCoq convention.
* `mkDef` (`:273`): as §2.5. Matches `fixSubst`.

Verified against `BinaryTrees.ast`: a `Prod` alt with binders `[fst, snd]` and body
`(tApp (tApp (tApp (tRel 4) (tRel 3)) (tRel 1)) (tRel 0))` — `fst ↦ 1`, `snd ↦ 0`.

---

## 3. Verdict, and what it forces in the design

**Verdict: (a) for the whole chain, against a compile table, on a fragment.** Concretely:

1. **Re-parameterise the passes.** `LBPass.term : GlobalDeclarations → LBTerm → LBTerm` cannot
   express `elimInline` or `fixIntro`, because the shipping `Σ` contains no `casesOn`, no ctor and
   no recursor declarations. Replace `Σ` with a **compile table**

   ```lean
   structure CompileTable where
     ctor  : Kername → Option (InductiveId × Nat × Nat × Nat)   -- iid, cidx, npars, nfields
     cases : Kername → Option CasesShape                        -- arity, discrPos, altsRange, per-alt nfields, binder names
     ind   : Kername → Option (InductiveId × Nat)
     block : Kername → Option (List Kername)                    -- the mutual block, in ci.all order
   ```

   Every field is a **pure function of the `Lean.Environment`**, so its adequacy belongs in
   `PrimSpec.lookup_adequate` — no new trust, one new obligation shape. This keeps T6's passes
   class **A** (they still mention neither `Expr` nor lean4lean) and keeps `LBPass.correct`
   unchanged, since the table is inert for evaluation.

2. **Split `LBCompile`.** The spec uses `LBCompile` in two incompatible roles: T8 factors the
   eraser's output through it, T9 applies it *to* the eraser's output. `optimize` is not on the
   shipping path at all. Define

   ```lean
   def LBLower : LBPass := fixIntro ∘ elimInline ∘ ctorInline   -- T8's factor
   ```

   and keep `optimize` as the separate flag-discharging pass T9 composes afterwards. Then T8 reads
   `∃ t₀, Erases env Us Δ (prepare e) t₀ ∧ t = LBLower.term E t₀`, and T9's conclusion evaluates
   `optimize.term (LBLower.env …) t` at `targetFlags`. This removes an idempotence obligation
   nobody has stated.

3. **Two conjuncts `Supported` must carry**, both already forced by the coverage record:
   - every `casesOn`-like head is *plain* — no `CasesAltInfo.default` (sparse) and no
     `hasSideCondition` (per-constructor eliminator);
   - every minor in a `casesOn` application is a syntactic λ chain of the alt's field arity.

   With these, `elimInline` and `visitAlt` agree on **binder names**, and the equality is genuine
   term equality, not equality-up-to-names.

4. **A third, cheap conjunct** for `fixIntro`: `name_occurs` agrees with λ□ self-reference on each
   registered declaration (true on 50/50 emitted fix defs). Without it, `fixIntro` is only
   relational for a definition whose sole self-reference is erased.

5. **Correct T3.** Recursors reached as constants are `ax` + `AxiomSpec`, not `recr`/`ElimBody`
   (§2.6). This is measured, not conjectural (`Eq.rec` in `Fannkuch.ast`). Q2 leaves the critical
   path as a consequence.

6. **State the subject as `prepare_erasure e`** (§2.8).

**Where it degrades to (b).** Genuine mutual blocks if the design refuses the `block` table field;
η-contracted minors and non-plain `casesOn` if the design refuses the `Supported` conjuncts. Both
are *choices*, not obstructions — and neither is exercised by the five benchmark programs, so the
non-vacuity target T10 is reachable at full exactness.

**Where it stays (c).** `Erases.proj` (already a rule, already exact), `ErasesDecl.ax` for
recursors and `@[extern]`, and everything in `prepare_erasure`.

---

## 4. Side findings for other open questions

* **Q5 (parameters in constructor applications).** Answered empirically: the frontend **keeps**
  them, boxed (§1.4). `ErasesDecl.ctor` should not drop parameters, and `LBWfPeregrine` must state
  the applied-with-parameters form that peregrine's `dearg_ctors` expects.
* **Q4 (do emitted eliminator declarations blow up the deliverable?).** Moot on the shipping path:
  no eliminator declarations are emitted at all (§1.3). If T3's relational Σ emits them, they are
  removed again by `LBLower.env`'s dead-declaration pruning and never reach `.ast`.
* **`mkDef` / `mkAlt` docstrings.** Both conventions are MetaCoq-correct (§2.10). The two hedging
  comments can be replaced with the `fixSubst` / `iota_red` cross-references.
