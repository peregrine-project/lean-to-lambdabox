# Reference spec for the Lean → λ□ rework

**Status.** Contract for the design phase. Normative. Where this document and any other
document in the repository disagree, this one wins until it is amended.

**Sources.** Sozeau, Forster, Lennon-Bertrand, Nielsen, Tabareau, Winterhalter, *Correct and
Complete Type Checking and Certified Erasure for Coq, in Coq*, J. ACM 72(1):8, 2025 — §7 and its
dependencies (cited `[S §x]`, figures `[S Fig. n]`). Letouzey, *A New Extraction for Coq*,
TYPES 2002 (cited `[L Def. n]`, `[L Thm n]`). Dima, *Compiling Lean programs with Rocq's
extraction pipeline*, MPRI report 2025 — the design document of the subject, not of the
specification (cited `[R §x]`). The Zulip thread *Peregrine Project > lean frontend*,
2026-01/02 — the consumer contract (cited `[Z n]`). Per-source analyses in
`doc/rework/refs/{metacoq-erasure,letouzey-extraction,lean-extraction-report,zulip-discussion,fit-analysis}.md`.

**Reader.** MetaRocq-literate. `EAst`, `EWcbvEval`, `erases`, `erases_deps`, `erase`,
`erases_erase`, `erases_correct`, `firstorder_ind`, `optimize` are used without gloss. What is
glossed is Lean: `Lean.Expr`, `casesOn`/`rec`, `Expr.proj`, `Expr.lit`, `Expr.mdata`,
`@[extern]`, `@[csimp]`, and lean4lean's `VEnv`/`VExpr`/`VLCtx`/`TrExprS`/`HasType`/`IsDefEq`.

**Companion documents.** This spec is normative; the numbered documents beside it are the wave
log that measures progress against it — `doc/rework/07-STATUS.md` is the current snapshot, and
the most recent waves are:

- `08-REPAIRS-W5.md` — W6, the closing round: reduces `hbridge` from `ErasureBridge`'s five
  original fields to two (`erasesEnv`, `lowerEnv`) and states the registration-invariant repair
  that would discharge them.
- `09-REPAIRS-W7.md` — W7: finds `ErasesEnv.defns` unsatisfiable at a universe-polymorphic tabled
  body (five of eight rungs vacuous under it) and plans the nine-unit repair, U1–U9, meant to
  close `hbridge`.
- `10-MERGE-FIXES.md` — the `dev/fix` merge: ten shipping fixes merged from `dev/fix`, and the
  eight-cluster (M1–M8) repair of the proofs they broke.
- `11-REPAIRS-W8.md` — W8: records that U9's composition of `hbridge` is unsatisfiable at the
  rungs, and specifies the nine units (W1–W9) that would discharge the binder, two of them
  waiting on the shipping fixes F-DEPLCTX and F-ARITYLET. Both fixes landed and W1–W9 landed in
  part (round 7 wave 4, `doc/rework/07-STATUS.md` §1/§4, `scratch/round7/W4-refute.md`):
  `hbridge` is still a binder — the registration invariant `RegAcc` still has no producer at a
  run of the shipping eraser (W5a/b/c, re-planned and not landed) — and `hargReach` is retired
  in favour of a stronger, source-side binder, `hbody` (W7/U9).
- `12-REPAIRS-W9.md` — W9: the complete remaining route to `hbridge`, in six units (W9-H, W9-A,
  W9-B, W9-C, W9-D, W9-E) with typechecked statements. It decides the two questions wave 4 left
  open — F-QUOT/F-EQREC's realizer exits are *excluded* by the fragment rather than admitted as
  specification entries, and the tabled-`casesOn` dependency is *measured* rather than guarded —
  and threads the accumulator through a second bundle of motives instead of rewriting
  `RunRefines`.

---

## 1. Objective

*The Lean-to-λ□ transpilation is verified* means: for the shipping entry point
`Erasure.erase e cfg` — the function `#erase` calls — run from the empty erasure state at a
stated configuration, if the run succeeds with output program `(Σ, t)`, then (a) `t` is the
image of `e` under an erasure relation `Erases` that is `[S Fig. 18]` transposed to `Lean.Expr`
— a strict congruence over the source syntax plus the single non-deterministic rule
`isErasable Γ e → e ⇝E □` — composed with a finite list of named λ□→λ□ passes each carrying its
own `optimize_correct` theorem `[S §7.4]`; (b) `Σ` is the dependency-selective erasure
`erases_deps` of the Lean environment declarations the run registered `[S §7.4]`, in the
applied-constructor form peregrine's first pass requires `[Z T1]`; and (c) whenever the source
term evaluates to a value `v` under the one source-evaluation relation, `t` big-step evaluates
under λ□'s `WcbvEval` — MetaRocq `EWcbvEval` with the three box amendments — to an erasure of
`v`, which on a first-order result type is *the* erasure of `v`, box-free, so the observable
answer is preserved `[S §7.3]`, `[L Thm 15]`. Every typing, definitional-equality and
term-translation fact used on the source side is lean4lean's and only lean4lean's: `VEnv`,
`VExpr`, `HasType`, `IsDefEq`, and the `TrExprS` translation from `Lean.Expr` into `VExpr`,
whose trust boundary this development inherits verbatim and never re-derives — that boundary is
today lean4lean's `sorryAx` cluster (`Injectivity.lean:12,21,34`, `UniqueTyping.lean:174`,
`ChurchRosser.lean:1193,1212`, `EnvLemmas.lean:334 VEnv.WF.patsStrong`), reaching this
development through `TrExprS.uniq` and `VEnv.IsDefEq.uniqU`; the paper needs a metatheorem in
exactly that place (`[S §7.2]`'s unique-sort-quality principle), so this is the right seam, and
it is the only inherited one. Everything else the theorem depends on is either proved here, or
a named, enumerated, theorem-visible hypothesis.

---

## 2. The theorem stack

Eleven items. Nine are the brief's; two are additions, each flagged with its justification.
Every item states its **paper origin**, its **intended Lean statement shape** (subject,
hypotheses, conclusion), and its **trust class**.

**Trust classes.**

| Class | Meaning |
|---|---|
| **A** | Proved here, `sorryAx`-free: `#print axioms` yields at most `propext`, `Quot.sound`, `Classical.choice`. |
| **B** | Proved here, modulo lean4lean's inherited `sorryAx` cluster (§1). No other axiom. |
| **C** | A theorem-visible hypothesis: a `Prop` in the statement's binder list, discharged per program in T10. |
| **D** | The one assumed interface: specifications of external `MetaM`/`CoreM` primitives this development cannot execute. Never an `axiom`; a structure field. |
| **E** | Out of scope, carried as one row of the ledger (T11) with a one-line statement of what is not covered. |

### T1 — λ□ syntax and weak call-by-value evaluation

*Origin.* `[S Fig. 16]`, `[S §7.1]` amendments (1)(2)(3), `[S §7.4]` `WcbvFlags`;
`[L §2.3]` Def. 5 (`(□ u) →□ □`), Def. 8 (singleton ι, boxed fixpoint guard), Def. 9 (weak
compatibility). Canonical implementation reference: MetaRocq `EWcbvEval`; canonical on-disk
reference: `peregrine-tool/theories/PAst.v` and `peregrine-tool/doc/format.md`.

*Shape.*

```lean
inductive LBTerm                                  -- EAst.term + .fvar + .prim; no tCoFix
inductive WcbvEval (Σ : GlobalDeclarations) (fl : WcbvFlags) : LBTerm → LBTerm → Prop
structure WcbvFlags where
  with_prop_case, with_guarded_fix, with_constructor_as_block : Bool

theorem eval_deterministic : WcbvEval Σ fl t v → WcbvEval Σ fl t v' → v = v'
theorem eval_value         : WcbvEval Σ fl t v → Value Σ fl v
theorem value_final        : Value Σ fl v → WcbvEval Σ fl v v
```

The three amendments are `app_box` (1), `iota_sing` (2, gated on `with_prop_case`), and the
fixpoint rule (3). `.fvar` is a documented extension of `[S Fig. 16]`, forced by the eraser's
locally-nameless representation `[R §4.7]`; `.prim` is MetaRocq's later `tPrim`; branches carry
`List BinderName`, matching `[S Fig. 18]` and `peregrine-tool`'s grammar rather than
`[S Fig. 16]`'s bare arity. `tCoFix` is absent and must stay absent: Lean has no coinduction.

*Flag discipline, fixed once here and never re-decided per lemma.* Erasure (T2, T3, T5) is
stated at

```lean
def eraseFlags : WcbvFlags := ⟨with_prop_case := true, with_guarded_fix := true,
                               with_constructor_as_block := false⟩
```

`with_prop_case := true` because rule (2) is what makes subsingleton elimination —
`Acc.rec`, `Eq.rec`, `And.rec`, `Decidable`'s elimination — evaluate `[S §7.1]`, `[L §3.3]`;
excluding it excludes the main Lean use case. `with_constructor_as_block := false` because
applied form is peregrine's *required* input `[Z T1, Z2]`, not a defect to be bridged. The
`optimize` pass (T6) discharges `with_prop_case`, landing the deliverable at
`⟨false, true, false⟩`. Block form is peregrine's own verified pass and is not modelled here.

*Trust class.* **A**.

### T2 — the erasure relation `Erases`

*Origin.* `[S Fig. 18]` (`Σ; Γ ⊢ t ⇝E t'`), `[L Def. 10]` (`(Γ,t) ◄ (Γ₀,t₀)`), `[L Def. 3]`
clause (□).

*Shape.* `Erases` is lean4lean's `TrExprS` with the target `VExpr` replaced by `LBTerm`,
`TrExprS.sort` and `TrExprS.forallE` absorbed into `box`, and `box` added. That is the whole
definition, and stating it that way is the external anchor the current relation lacks.

```lean
inductive Erases (env : VEnv) (Us : List Name) : VLCtx → Expr → LBTerm → Prop
  | box   : TrExprS env Us Δ e ve → Erasable env Us.length Δ.toCtx ve → Erases Δ e .box
  | bvar  : Δ.find? (.inl i) = some (e', A) → Erases Δ (.bvar i) (.bvar i)
  | fvar  : Δ.find? (.inr x) = some (e', A) → Erases Δ (.fvar x) (.fvar x)
  | const : env.constants c = some ci → Erases Δ (.const c us) (.const (kername c))
  | app   : Erases Δ f f' → Erases Δ a a' → Erases Δ (.app f a) (.app f' a')
  | lam   : TrExprS env Us Δ ty ty' → Erases ((none, .vlam ty') :: Δ) b b' →
            Erases Δ (.lam n ty b bi) (.lambda n b')
  | letE  : TrExprS env Us Δ ty ty' → TrExprS env Us Δ v val' → Erases Δ v v' →
            Erases ((none, .vlet ty' val') :: Δ) b b' →
            Erases Δ (.letE n ty v b nd) (.letIn n v' b')
  | proj  : Erases Δ e e' → Erases Δ (.proj S i e) (.proj ⟨iid, np, i⟩ e')
  | lit   : env.ContainsLits l → Erases Δ l.toConstructor t → Erases Δ (.lit l) t
  | mdata : Erases Δ e t → Erases Δ (.mdata d e) t
```

Ten rules. Non-negotiable properties, each a checkable acceptance criterion (§7):

1. **The index is `(env : VEnv, Us, Δ : VLCtx)` and nothing else.** No `ErasureCtx`, no
   registry column, no field of the eraser's state. "`e` erases to `t`" must be a
   run-independent statement `[L R3]`, `[S R3]`. The `kername`/`InductiveId` translation is a
   parameter of the environment relation (T3), consulted there, not a twelve-column index here.
2. **Exactly one non-deterministic rule** (`box`), with a genuine `Erasable` witness. `Erasable`
   keeps `[S §7.2]`'s two disjuncts separate — `A : Prop` (a proof) or `IsArityUpTo A` (a type
   former, `[L Def. 1]`'s type scheme) — because `[L Lemma 2]`'s stability facts are proved
   separately for them.
3. **No side condition anywhere at term level.** `[S Fig. 18]`'s single side condition
   (`Subsingleton Σ ci.(ci_ind)` on `erases_tCase`) has no term-level home in Lean because
   `Lean.Expr` has no case node; it moves to T3, where it is the side condition of the
   *recursor declaration's* erasure, and where it is *derived* from the kernel's
   large-elimination criterion rather than assumed `[L R4]`.
4. **No rule produces `.construct`, `.case` or `.fix`.** `Lean.Expr` has no constructor, match
   or fixpoint node, so under the congruence discipline of both papers these three λ□ nodes may
   not be produced by the erasure relation at all. They are produced by T3 (inside erased
   *declaration bodies*) and by T6 (passes). This is the single structural correction the
   rework makes, and it is what removes the epicycle.
5. **`Erases.const` is uniform over the classification of `c`.** Definitions, theorems,
   axioms, constructors, recursors and quotient primitives all erase to `.const (kername c)`.
   The classification is the environment's business (T3).
6. `mdata` is transparent with an identity target `[S §4.6 of the analysis]`; `lit` is the
   kernel unfolding, mirroring `TrExprS.lit` exactly; `const` drops universe levels, mirroring
   `erases_tConst`.

*Metatheory required with it* (`[S §7.3]` "global weakening, weakening and substitutivity";
`[L Lemma 16]`): `erases_shift`, `erases_subst`, `Erases.abstract` / `Erases.uninstantiate`
(the fvar↔de Bruijn transport the locally-nameless setting forces and no paper needs),
`Erases.thin_vlet`, context uniformity, prefix/level weakening. `erases_subst` rests on
`Erasable`'s stability kit (`.inst`, `.weakN`, `.defeq`), which is `[L Lemma 2]`.

*Deliverable shipped with the definition:* the rule-by-rule table of §3 below, tracked next to
`Erases.lean`, covering every rule of `[S Fig. 18]` and every rule of `Erases`, with every
deviation named. `[S R11]`.

*Trust class.* **B** (the `box` rule's witness is `TrExprS` + `HasType`).

### T3 — global-environment erasure `ErasesEnv` / `erases_deps`

*Origin.* `[L Def. 3]`'s four context rules (`nil`, `def`, `ax`, `ind`) and `[L R13]`;
`[S §7.4]`'s `erases_deps Σ Σ' t'` — "recursively and selectively … considering only the
dependencies of the erased term `t'`, in a bottom-up fashion … models `Recursive Extraction`".
The pointwise `Σ ⇝E Σ'` of `[S §7.3]` is the definition the paper explicitly does *not* use and
must not appear here.

*Shape.* Two layers: what one Lean declaration erases to, and the dependency-closed relation.

```lean
inductive ErasesDecl (env : VEnv) : Name → GlobalDecl → Prop
  | defn  : env.constants c = some ⟨_, some body⟩ → Erases env ci.levelParams [] body b' →
            ErasesDecl c (.constantDecl ⟨some b'⟩)
  | ax    : env.constants c = some ⟨_, none⟩ → ErasesDecl c (.constantDecl ⟨none⟩)
  | ind   : ErasesDecl I (.inductiveDecl ⟨npars, ctors, projs⟩)
  | ctor  : ErasesDecl c (.constantDecl ⟨some (.construct iid k [])⟩)
  | recr  : ElimBody env I body → ErasesDecl I.rec (.constantDecl ⟨some body⟩)
  | quot  : ElimBody env .quot body → ErasesDecl q (.constantDecl ⟨some body⟩)

inductive ErasesEnv (env : VEnv) : GlobalDeclarations → LBTerm → Prop   -- erases_deps
```

`ErasesEnv Σ t` is the bottom-up, dependency-selective predicate: every `kername` occurring in
`t` has a declaration in `Σ` produced by `ErasesDecl`, and recursively for the bodies of those
declarations. It is the *only* environment relation in the development.

*The two Lean-specific declaration classes, and the obligation each carries.* Coq's `tConstruct`,
`tCase` and `tFix` are term formers; Lean's constructors and eliminators are *constants*. Under
the congruence discipline (T2.4) they therefore become λ□ *declarations* — a runtime library,
emitted once per declaration rather than reconstructed at each occurrence:

* `ctor` — the constructor constant `c`, the `k`-th of inductive `I`, erases to the declaration
  body `.construct iid k []`. In applied form (T1) its arguments arrive by `.app`, so the body
  is arity-free and no η-expansion is needed here. This is exactly `[L §2.4]`'s situation, where
  constructors are context variables in `Γ_C` and `E` preserves the spine; applied-vs-block is a
  non-question for the relation and a downstream pass for peregrine `[Z T1]`.
* `recr` — the recursor `I.rec` erases to a λ□ body built from `.case` (and `.fix`, for a
  recursive `I`), carrying the obligation **`ElimBody`**: the body's λ□ evaluation reproduces the
  kernel's ι-rule for `I.rec` at every constructor. Three consequences worth stating:
  - This is where `[S Fig. 18]`'s `Subsingleton` side condition lives, and it is *derived*: for
    a `Prop`-valued `I` eliminating into `Type`, Lean's kernel admits `I.rec` only under the
    large-elimination criterion — at most one constructor, all of whose non-parameter arguments
    are propositions — which is verbatim `[L §3.3]`'s "zero constructor (empty inductive)" or
    "one constructor whose arguments are all logical". At such an `I` the emitted body is the
    single branch applied to boxes, and its correctness is precisely rule (2) of T1. So `Acc.rec`,
    `Eq.rec`, `False.rec`, `And.rec`, `Iff.rec` and `Decidable`'s elimination are **inside** the
    fragment, not excluded by a `nonProp` conjunct. Deriving the criterion inside lean4lean's
    `VEnv` model is the rework's one research item (§8, Q2).
  - `casesOn` is not a kernel primitive; it is an ordinary definition in terms of `rec`, so it
    needs no special class — `ErasesDecl.defn` covers it, and its body's `.case` node arrives
    through `recr` by δ. Auxiliary matchers likewise `[R §4.2]`.
  - Structural recursion elaborated to `brecOn`/`rec` is therefore *already* covered; recursion
    that reaches the eraser as top-level self-reference (`_unsafe_rec`, `[R §4.1]`) is a
    declaration-level phenomenon handled by the `fixIntro` pass (T6), never by a term rule.

*Trust class.* **B**, except `ElimBody` at a `Prop`-valued inductive, which is **B** conditional
on the derived subsingleton criterion (Q2) and **C** until that lands.

### T4 — source evaluation and subject reduction

*Origin.* `[S §5.6]` (`Σ ⊢ t ⇓ v`, weak call-by-value big-step), `[S §5.4]` (subject reduction,
used to keep `isErasable` premises alive across a step), `[L Def. 9]` (`→_rw`), `[L Lemma 2]`.
Requirement `[S R2]`, `[L R8]`: exactly one relation.

*Shape.*

```lean
structure SEvalFlags where beta, delta, zeta, iota, proj, lit : Bool
inductive SEval (env : VEnv) (Us : List Name) (fl : SEvalFlags) : VLCtx → Expr → Expr → Prop

theorem SEval.mono   : fl ≤ fl' → SEval env Us fl Δ e v → SEval env Us fl' Δ e v
theorem SEval.defeq  : env.WF → TrExprS env Us Δ e ve → SEval env Us fl Δ e v →
                       ∃ vv, TrExprS env Us Δ v vv ∧ env.IsDefEq Us.length Δ.toCtx ve vv
```

One relation, parameterised by which reductions are enabled — **not** eight relations. A
fragment is a hypothesis on the derivation or a value of `fl`, with `SEval.mono` as the
inclusion lemma. `zeta` must be enabled at the capstone: today neither capstone flavour can
evaluate a `let`, which is a coverage bug, not a design choice. `SEval.defeq` is `[S §5.4]`'s
role — it is what re-establishes the `Erasable` premise after a step, and it is the only thing
the box arm of T5 needs from the source side.

`[S §5.6]`'s `progress`, `[S §5.5]`'s normalization axiom and `[S]`'s `wcbv_standardization`
have no lean4lean counterpart and are **not** built (§5, N7). The capstone is therefore stated
in the paper's own conditional form: source evaluation is a hypothesis.

*Trust class.* **B**.

### T5 — `erases_correct`, the forward simulation

*Origin.* `[S §7.3]` `erases_correct`; `[L Thm 13]`.

*Shape.* One theorem. Hypotheses exactly `[S §7.3]`'s, transposed.

```lean
theorem erases_correct
    (henv : env.WF) (hwt : TrExprS env Us [] e ve)
    (hev  : SEval env Us fl [] e v)
    (her  : Erases env Us [] e t)
    (hΣ   : ErasesEnv env Σ t) :
    ∃ v', Erases env Us [] v v' ∧ WcbvEval Σ eraseFlags t v'
```

The value's erasure is **existentially quantified** and is generally *not* the erasure function
applied to `v`; that is the entire reason a relation exists (`[S §7.3]`'s counterexample,
`[L Ex. 4]`). No hypothesis
outside the five above. Nothing named `Relevant`, `Supported`, `IotaRelevant`, `SEnvConsistent`,
`RecEnvConsistent` or `hnfv` may appear in the statement `[S R5]`.

*Proof structure, which is the papers' and is already right in the tree:* induction on `hev`,
inversion on `her` at each step, each case splitting into "erased structurally" and "erased to
`□`"; the box arms consume T1's rules (1)(2)(3); β consumes `erases_subst`; δ consumes
`ErasesEnv`; the `Erasable` premise is carried across steps by `SEval.defeq`.

*Trust class.* **B**.

### T6 — the pass layer (**addition**)

*Justification for the addition.* `[S §7.4]` makes this the paper's own architectural rule:
"*this direct expansion of cases considerably complicates the correctness proof of erasure … We
decide not to include it into the erasure function, and instead define it as a second pass*",
and `[L §4]` separates a 900-line proved core from 700 unproved lines of optimisation. Without
a pass layer, every Lean-specific compilation step has nowhere to live except inside the
relation, which is exactly the defect being repaired. `[S R9]`, `[L R1]`, `[R R9]`.

*Shape.* Each pass is a record; correctness is `optimize_correct`'s shape, flag-discharging
where applicable, `wf`+`closed` as the only hypotheses (no typing — these are λ□→λ□).

```lean
structure LBPass where
  term    : GlobalDeclarations → LBTerm → LBTerm
  env     : GlobalDeclarations → GlobalDeclarations
  flIn flOut : WcbvFlags
  correct : LBWf Σ → LBClosed t → WcbvEval Σ flIn t v →
            WcbvEval (env Σ) flOut (term Σ t) (term Σ v)
```

The named passes, in composition order:

| Pass | What it does | Hardest lemma | Status |
|---|---|---|---|
| `ctorInline` | δβ on constructor constants: `.const c` applied ⇝ `.construct iid k []` applied | δ + β preservation | new, small |
| `elimInline` | δβ on recursor/`casesOn` constants: saturated application ⇝ `.case`, η-expanding under-applied heads | `IotaBridge`: a β-chain of field applications *is* MetaRocq's `iota_red` | lemma in hand |
| `fixIntro` | a self- or mutually-recursive `ConstantDecl` body ⇝ `.fix` | `closeFix_substList_fixSubst`: static fix-closing inverts dynamic fix-unfolding | lemma in hand |
| `optimize` | `[S §7.4]` Prop-case expansion; discharges `with_prop_case` | `LBOptimize_correct` | **already proved, currently dead** |
| `natLower` | peano tower ⇝ `.prim`; a data refinement, not an erasure | unary↔i63 refinement, overflow side condition | **out of scope**, §5 N3 |

```lean
def LBCompile : LBPass := optimize ∘ fixIntro ∘ elimInline ∘ ctorInline
```

`LBCompile.correct` is then a composition, and it is what carries a T5 conclusion at
`eraseFlags` down to the deliverable at `targetFlags`.

*Trust class.* **A** — every pass is target-side, mentions neither lean4lean nor `Expr`, and is
independently checkable. Each pass ships with a non-vacuity guard (a concrete `Σ`, `t`, `v` for
which its hypotheses hold and the conclusion is not `WcbvEval`-trivial), following
`Optimize.lean:1066` and `Semantics/Metatheory.lean:417`.

### T7 — first-order values and uniqueness

*Origin.* `[S §7.3]` `firstorder_ind` and `firstorder_erases_deterministic`; `[L Def. 6]`
(logic-free), `[L Def. 14]` (data-type), `[L Thm 15]`.

*Shape.*

```lean
def FirstOrderInd (env : VEnv) (I : Name) : Prop   -- syntactic, decidable, on the declaration
theorem firstorder_erases_deterministic
    (hfo : FirstOrderInd env I)
    (hwt : TrExprS env Us [] v vv) (hty : env.HasType Us.length [] vv (mkApps (.const I us) args))
    (hval : SEval env Us fl [] v v)                 -- `v` evaluates to itself: `v` is a value
    (h₁ : Erases env Us [] v t₁) (h₂ : Erases env Us [] v t₂) : t₁ = t₂
theorem firstorder_no_box : ... → Erases env Us [] v t → NoBox t
```

`FirstOrderInd` is `[S §7.3]` verbatim: all parameters, indices and constructor argument types
are syntactically headed by first-order inductives. It must be *decidable and mechanically
checkable on a benchmark* — `Nat`, `Bool`, `List Nat`, `Nat × Nat`, `Option`, a user `Tree` —
which the current value-indexed `FirstOrderValue` is not. `firstorder_no_box` is `[L Thm 15]`'s
conclusion (`E(t₀) = t₀`, so no `□` survives in the answer) and is what makes the capstone
observational rather than merely simulative; it is cheap once uniqueness is in place.

*Trust class.* **B** (uniqueness runs through `TrExprS.uniq` / `IsDefEq.uniqU`).

### T8 — `erases_erase`: the shipping eraser refines the relation

*Origin.* `[S §7.2]` `erases_erase` (one lemma); `[L Lemma 11]`; and `[S §7.4]`'s own sanction
for the factored form: "*If efficiency becomes a concern, we can always inline these passes
again in a new erasure function and prove that it yields the same result as first running the
erasure function as defined in this article and then the propagation pass.*" The shipping
`visitExpr` **is** that inlined eraser: it emits `.construct`, `.case` and `.fix` directly. The
theorem therefore factors it, and this resolves the design phase's first open question in the
direction that does not edit shipping code (per the repository's standing rule: raise
implementation issues, never silently patch them).

*Shape.* One lemma, one induction over the real `partial_fixpoint` family.

```lean
theorem visitExpr_refines_erases
    (P    : PrimSpec)                            -- the single interface, class D
    (hcfg : cfg.csimp = false ∧ cfg.nat = .peano ∧
            cfg.remove_irrel_constr_args = false ∧ cfg.extern = .preferLogical)
    (hwt  : TrExprS env Us Δ e ve)
    (hsup : Supported env e)                     -- syntactic, decidable, on `e` and its closure
    (hrun : ((visitExpr e).run cfg s).ok (t, s')) :
    ∃ t₀, Erases env Us Δ e t₀ ∧ t = LBCompile.term s'.gdecls t₀
```

*`PrimSpec` — the one bundle, replacing seven.* `[S §6.2]`'s `abs_env_struct`/`abs_env_prop` is
the model: one carrier, a squashed connection relation, `abs_env_irr` (the specification
environment is unique), lookup as the only query. Its fields are **specifications of external
primitives only** — things this development cannot execute and must assume about the Lean
runtime — and nothing else:

1. `env_connect` — the `Lean.Environment` the run reads is in relation with `env : VEnv`, and
   that relation is functional (`abs_env_irr`).
2. `lookup_adequate` — `getConstInfo`, `getCasesInfo?`, `getCtorArity?`, `getDeclInfo?` agree
   with `env_connect`.
3. `fresh_names` — `mkFreshFVarId` returns identifiers absent from the ambient context.
4. `oracle_sound` — `Erasure.isErasable lparams e = true → Erasable env …`.

Field 4 is **discharged, not assumed**, on the shipping path: `Relevance.isErasable` →
`RelevanceCheck.isErasable.WF` → `CheckerAdequacy.kernel_isErasable_sound` →
`OracleDischarge.ResidualHyps.toBridgeHyps`. This is the development's only trust *reduction*
and it must be inside the capstone's import closure, which today it is not. Only the soundness
half is needed `[S §7.2]`; completeness needs the `CumulProp`/sort-quality apparatus and is
**not to be built** — Lean has no `Prop ≤ Type`, so `[S]`'s `prop_sub_type := false`
requirement is automatically satisfied and the apparatus is unnecessary.

*`Supported` — the fragment predicate.* No paper counterpart, and a legitimate device only if
it is **syntactic and decidable on `e` and its dependency closure** `[R R16]`, checkable by
running it on a real program. It must make every currently-known coverage hole *visible in the
predicate a reader audits* — in particular the sparse-`casesOn` shape (`_sparseCasesOn_`,
`doc/rework/03-DEV-FIX.md`, F-SPARSE) on which the shipping eraser silently emits a wrong program: that
exclusion may not live in a hypothesis bundle in another file.

*Panics.* `.ok` does not exclude a panicked run: a `panic!` succeeds at `EraseM` and returns
`default : LBTerm = .box`. The theorem must therefore either carry `¬ run.panicked` or *refute*
each of the 16 panic sites from its hypotheses. Two are refutable outright and must be:
`Expr.sort u` and `Expr.forallE ..` are always `Erasable` for a well-typed term (a sort's type
is an arity; a `forallE`'s type is a sort, hence an arity), so the oracle fires first and the
`unreachable!` arm is unreachable — a lemma, not a tolerated arm. The residue is enumerated in
the ledger with the premise that excludes each `[R R13]`, `[Z 8]`.

*Trust class.* **B**, with `PrimSpec` fields 1–3 at **D** and field 4 at **B**.

### T9 — the cold-start capstone

*Origin.* `[S §7.3]` `erase_correct_firstorder`, by composition; `[L Thm 15]`; `[Z 3]` for the
output boundary.

*Shape.* Subject: `Erasure.erase`, the function `#erase` calls, run from the empty state. `Σ`,
`t`, the registration records, closedness and the applied-constructor invariant are all
**produced by the run**, never assumed — this technique is the current tree's durable
contribution and must survive.

```lean
theorem shipping_erase_correct_firstorder
    (P : PrimSpec) (hcfg : ...)                          -- as T8
    (hwt : TrExprS env [] [] e ve)
    (hsup : Supported env e)
    (hax : ErasableAxioms env e)                          -- see below
    (hfo : FirstOrderInd env I)
    (hty : env.HasType 0 [] ve (mkApps (.const I us) args))
    (hrun : (Erasure.erase e cfg).ok (.untyped Σ (some t), inls)) :
      ErasesEnv env Σ t
    ∧ LBWfPeregrine Σ t                                   -- peregrine's input precondition
    ∧ ∀ v, SEval env [] fl [] e v →
        ∃ tv, Erases env [] [] v tv ∧ NoBox tv ∧
              WcbvEval (LBCompile.env Σ) targetFlags (LBCompile.term Σ t) tv
```

*`ErasableAxioms` replaces `axiom_free`.* `[S §5.6]`'s `axiom_free Σ` is unusable in Lean:
`propext`, `Quot.sound` and `Classical.choice` are in the dependency closure of essentially
every realistic program, which is precisely why the current capstones cover 0/5 benchmarks. The
generalisation, which `[S §9]` itself gestures at ("axioms which do not block call-by-value
evaluation"): every axiom in the *erased* closure is either `Prop`-typed — hence `Erasable`,
hence boxed, hence never a stuck head in a relevant position (`propext`, `Quot.sound`) — or
named in an enumerated `AxiomSpec` with its assumed realizer behaviour (`@[extern]`, `Eq.rec`,
`[R §4.2]`, `[Z 4]`). `Classical.choice` is neither, and is excluded by dependency tracking,
which `ErasesEnv` gives for free. This is the single change that moves benchmark coverage off
zero.

*`LBWfPeregrine`* is one predicate on the emitted program matching what `peregrine validate`
checks — including applied-constructor form and the parameter convention — so that composition
with the verified middle-end is a statement rather than a hope `[Z 3]`.

*Composition, mirroring `[S §7.3]`:* T8 puts the output in `Erases ; LBCompile`; T5 simulates
the source evaluation into λ□ at `eraseFlags`; T6 carries it to `targetFlags`; T7 identifies the
value's erasure uniquely and shows it box-free.

*Trust class.* **B** + the class-**C** hypotheses `hcfg`, `hsup`, `hax`, `hfo`, `hev`.

### T10 — non-vacuity, as a theorem

*Origin.* `[S R8]`, `[L R12]`, `[R R15]`, `[Z 6]`. Not a paper theorem; a paper *standard*
(`[L §4]` reports >6,000 lines of extracted benchmark code).

*Shape.* For at least `VerifyBench/Arith.lean`'s `benchArith`, a checked term inhabiting every
hypothesis of T9 simultaneously, in the repository, elaborated by `lake build`:

```lean
example : Supported env (expr_of benchArith) := by decide
example : ErasableAxioms env (expr_of benchArith) := by decide
example : FirstOrderInd env ``Nat := by decide
theorem arith_covered : <the full conclusion of T9, instantiated> := ...
```

plus a per-program coverage table for all five VerifyBench programs, stating for each what is
covered and what is not, in the honest style of `doc/coverage.md`. Arith is
the minimum because it is the smallest and needs no `match`: its residue is 10 typeclass
projections, 4 single-definition `fix` blocks and a 19-node peano tower — i.e. exactly the
typeclass-dictionary layer the collaborators care about `[Z 6]`. A hypothesis no benchmark
satisfies is the wrong hypothesis `[S R8]`.

*Trust class.* **A** for the discharges; the theorem's own class is T9's.

### T11 — the trust ledger, measured in CI (**addition**)

*Justification for the addition.* `[S §1]`'s "trusted theory base" paragraph and `[S §5.5]`'s
single `normalization` axiom are the model: one bundle, stated once, with a one-line
justification per element of why it is a theory-level rather than a code-level assumption
`[S R10]`. Making it *measured* rather than *narrated* is the repair for a ledger that
currently exists in three prose copies and is wrong three ways about its own contents.

*Shape.* One file, one table, one CI job.

```lean
-- test/Ledger.lean, run in CI, diffed against a committed fixture
#print axioms LeanToLambdaBox.shipping_erase_correct_firstorder
#print axioms LeanToLambdaBox.visitExpr_refines_erases
#print axioms LeanToLambdaBox.erases_correct
#print axioms LeanToLambdaBox.LBCompile_correct
```

The ledger's rows: (a) lean4lean's inherited `sorryAx` cluster, by `file:line` measured *at the
pinned rev*, with the note that `VEnv.WF.patsStrong` is fork-authored and not inherited;
(b) `PrimSpec`'s three assumed fields (class **D**); (c) the class-**C** hypotheses; (d) the
class-**E** rows (§5). No prose copy of the ledger may exist anywhere else in the repository.

*Trust class.* **A** (it is a measurement).

---

## 3. Fidelity table

Paper object → required Lean counterpart → adaptation. `—` means "no counterpart, deliberately".

### 3.1 Target language and semantics

| Paper | Lean counterpart | Adaptation |
|---|---|---|
| `[S Fig. 16]` `E.term` | `LBTerm` | `+ .fvar` (locally nameless, `[R §4.7]`); `+ .prim` (MetaRocq's later `tPrim`); branches carry `List BinderName` per `[S Fig. 18]` and peregrine's grammar; **no `tCoFix`** — Lean has no coinduction |
| `[S §7.1]` `⇓` | `WcbvEval` | rule-for-rule against `EWcbvEval`, with the in-code correspondence table kept |
| amendment (1) `□ a ⇓ □` | `WcbvEval.app_box` | = `[L Def. 5]` |
| amendment (2) singleton case on `□` | `WcbvEval.iota_sing`, gated `with_prop_case` | = `[L Def. 8]` clause 2. **Load-bearing for Lean**: it is what makes `Acc.rec`/`Eq.rec`/`WellFounded.fix` run |
| amendment (3) fix on a boxed guard | `WcbvEval` fixpoint rule, unfolding on argument count | faithful to `EWcbvEval.eval_fix`; *a fortiori* covers `[L Def. 8]`'s "`□` or constructor" guard |
| `[S §7.4]` `WcbvFlags`, `disable_prop_cases` | `WcbvFlags`, `optimize` | flag chain fixed in T1: `eraseFlags` → `targetFlags` |
| `[S Fig. 12]` `value`/`value_head`/`atom` | `Value`, `atomValue` | faithful |
| block vs applied constructors | `with_constructor_as_block := false` | **applied form is primary** `[Z T1, Z2]`; block is peregrine's verified pass, not modelled |

### 3.2 Erasability

| Paper | Lean counterpart | Adaptation |
|---|---|---|
| `[S §7.2]` `isErasable Σ Γ t` | `Erasable env U Γ e` | two disjuncts kept separate: `A : Sort 0` (proof) or `IsArityUpTo A` (type former = `[L Def. 1]` type scheme) |
| `[S fn. 13]` `isArity` | `IsArity` / `IsArityUpTo` | taken **up to defeq**, which is more faithful than a syntactic test |
| `[L Lemma 2]` stability | `IsArity.inst/.liftN`, `IsArityUpTo.inst/.weakN/.defeq`, `Erasable.weakN/.inst/.defeq` | complete; the pivot of `erases_subst` |
| `[S §3.5]` `prop_sub_type := false` | — | **vacuous**: Lean has no `Prop ≤ Type` |
| `[S §7.2]` `CumulProp` / sort-quality | — | **not needed and not to be built**: only oracle *soundness* is required (T8) |
| `[S §6.4]` retyping | lean4lean `inferType` | upstream's |
| definitional proof irrelevance | used, not re-proved | Lean's `Prop` is definitionally proof-irrelevant `[R fn. 4]`, which makes the box case *cheaper* than in Coq. Exploit it |

### 3.3 The erasure relation, rule by rule against `[S Fig. 18]`

| `[S Fig. 18]` rule | Lean counterpart | Note |
|---|---|---|
| `erases_box` | `Erases.box` | the one non-deterministic rule; `TrExprS` witness + `Erasable` |
| `erases_tRel` | `Erases.bvar` **and** `Erases.fvar` | locally-nameless split; `fvar` has no paper counterpart and is forced by the eraser's representation. The `toBvar` transport metatheory is likewise Lean-only |
| `erases_tLambda` | `Erases.lam` | extends the `VLCtx` exactly as `TrExprS.lam` does |
| `erases_tLetIn` | `Erases.letE` | ζ must be enabled in **both** semantics (T4, T1). `letE.nonDep` is ignored |
| `erases_tApp` | `Erases.app` | |
| `erases_tConst` | `Erases.const` | drops universe levels, as the paper drops `u`. Uniform over the classification of `c` (T2.5) |
| `erases_tProj` | `Erases.proj` | Lean structure projections; keyed on the source `Expr.proj S i e` and the environment. Deliberately carries no `TrExprS` premise: `TrProj` pins params/field types only up to defeq (`TrProj.uniq` gives `IsDefEqU`, not equality) |
| `erases_tConstruct` | **— (T3 `ErasesDecl.ctor`)** | `Lean.Expr` has no constructor node; constructors are `.const` heads. One declaration, not two term rules |
| `erases_tCase` + `Subsingleton` | **— (T3 `ErasesDecl.recr`)** | `Lean.Expr` has no case node. The Subsingleton criterion becomes the side condition of the recursor declaration's erasure at a `Prop`-valued inductive, **derived** from Lean's large-elimination rule, not assumed `[L R4]` |
| `erases_tFix` | **— (T3 `ErasesDecl.recr`, T6 `fixIntro`)** | `Lean.Expr` has no fixpoint node. Structural recursion arrives as recursor applications; top-level recursion is a *declaration-level* phenomenon `[R §4.1]` |
| `erases_tCoFix` | **—** | no coinduction in Lean |
| — | `Erases.mdata` | transparent congruence with identity target; no paper counterpart, harmless |
| — | `Erases.lit` | "a literal is its kernel unfolding", mirroring `TrExprS.lit`; machine `Nat` is a separate refinement (§5 N3) |
| `[S §7.3]` weakening/substitutivity | `erases_shift`, `erases_subst`, `Erases.abstract`, `Erases.uninstantiate`, `Erases.thin_vlet`, uniformity | = `[L Lemma 16]` |
| `[L Def. 10]` `(Γ,t) ◄ (Γ₀,t₀)` | the conjunction (`TrExprS` + `Erases`) | `(◄₁)` = `TrExprS`/`HasType`; `(◄₂)` = the congruence shape of `Erases`; `(◄₃)` = `box`'s `Erasable` premise; `(◄₄)` = T3's `ElimBody` side condition — **discharged, not assumed** |

### 3.4 The function, the oracle, the environment

| Paper | Lean counterpart | Adaptation |
|---|---|---|
| `[S Fig. 17]` `E` | `Erasure.visitExpr` family (shipping; **not editable**) | not pruning-only: η-expands to arity, splits `casesOn` spines, builds literal towers. Hence T8's factored conclusion |
| `[S §7.2]` `erases_erase` | T8 `visitExpr_refines_erases` | one lemma, one induction over the real `partial_fixpoint` family; conclusion factored through `LBCompile` per `[S §7.4]` |
| `[S §7.2]` `is_erasableb` | `Erasure.isErasable` + `Relevance`/`RelevanceCheck`/`CheckerAdequacy`/`OracleDischarge` | soundness discharged; completeness not built |
| `[S §6.2]` `abs_env_struct`/`abs_env_prop` | `PrimSpec` (T8) | one interface, four named obligations; squashed connection + `abs_env_irr` |
| `[S §6.2]` `abs_pop_decls` | — | not needed: the Lean eraser builds the output environment incrementally |
| `[S §7.4]` `erases_deps` | T3 `ErasesEnv` | adopted directly; `#erase` already walks the dependency closure bottom-up |
| `[S §7.3]` pointwise `Σ ⇝E Σ'` | — | the definition the paper explicitly does not use; must not exist |
| `[L Def. 3]` context rules nil/def/ax/ind | T3 `ErasesDecl` | + the two Lean classes `ctor` and `recr` |
| `[S §5.6]` `axiom_free Σ` | `ErasableAxioms` (T9) | generalised; the naive form is uninhabited in Lean |
| `[R §4.1]` `prepare_erasure` | stated per transformation | `replaceUnsafeRecNames` (δ + a declaration swap), `macroInline` (δ), `inlineMatchers` (δ), `csimp` (**excluded**, §5 N1) |

### 3.5 The capstone

| Paper | Lean counterpart | Adaptation |
|---|---|---|
| `[S §7.3]` `erases_correct` | T5 | five hypotheses, existentially quantified value erasure |
| `[S §7.3]` `firstorder_ind` | T7 `FirstOrderInd` | syntactic on the *declaration*, decidable, checkable on the benchmarks |
| `[S §7.3]` `firstorder_erases_deterministic` | T7 | hypothesis "`v` evaluates to itself" mirrored as `SEval … v v` |
| `[S §7.3]` `erase_correct_firstorder` | T9 | by composition |
| `[S §7.4]` `optimize`/`optimize_correct` | T6 `optimize` | already proved; wire it in as the template for every pass |
| `[L Thm 15]` no residual `□`, syntactic equality | T7 `firstorder_no_box` + T9's conclusion | what makes the result observational |
| `[L Def. 6]` logic-free / `[L Def. 14]` data-type | `FirstOrderInd` | Def. 14 ≈ `firstorder_ind`; record the equivalence or the gap explicitly (§8, Q6) |
| `[L Thm 12]` target step ⇒ ≥1 source steps | **—** | §5 N7: needs source strong normalization, which lean4lean does not have |
| `[S §5.5]` normalization axiom, `[S §5.6]` progress, `wcbv_standardization` | **—** | §5 N7: the capstone stays in `[S]`'s own conditional form |

### 3.6 Lean-specific adaptations, stated once

* **`casesOn` vs `match`.** `Lean.Expr` has no `match`. Source `match` compiles to auxiliary
  matcher constants, which compile to `casesOn`, which is a definition in terms of `rec`.
  `prepare_erasure` inlines matchers `[R §4.1]`; the fragment must be closed under matcher
  unfolding. In the specification, only `rec` is primitive (T3 `recr`); `casesOn` and matchers
  are ordinary definitions (T3 `defn`).
* **Structural recursion via recursors.** Covered by T3 `recr` (a `.fix` inside the erased
  recursor body). Recursion that reaches the eraser as top-level self-reference — because the
  eraser takes the *compiler-facing* `_unsafe_rec` body, not the kernel's recursor-elaborated
  body `[R §4.1, fn. 11]` — is handled by T6 `fixIntro`. The mismatch between the two bodies is
  a stated hypothesis, §5 N8.
* **Projections.** `Expr.proj` ↦ `LBTerm.proj` via `TrProj`. Field indices are exact only at an
  all-`keep` argmask, which §5 N4 pins by configuration.
* **Literals.** `Expr.lit (.natVal n)` erases as its kernel unfolding (T2 `lit`), giving the
  peano tower through `ErasesDecl.ctor`. `strVal` is outside the fragment. Machine `Nat` is a
  data refinement, §5 N3.
* **Universe levels.** `Erases.const` drops `us`, mirroring `erases_tConst`. Polymorphism is
  carried by `Us` and by level instantiation on the relation; the capstone's subject may be
  monomorphic (§5 N9) but its *dependencies* may not be restricted — every typeclass method the
  benchmarks touch is universe-polymorphic.
* **`let`/ζ.** `Expr.letE` ↦ `LBTerm.letIn`; ζ enabled in both semantics. Non-negotiable: a
  capstone that cannot evaluate a `let` covers no real program.
* **`mdata`.** Transparent congruence.
* **`Expr.sort` / `Expr.forallE` / `Expr.mvar`.** `sort` and `forallE` are always `Erasable`
  (T8) — a lemma, which refutes two of the eraser's `unreachable!` arms. `mvar` is excluded by
  `TrExprS`, which cannot translate one; `#erase` runs `instantiateMVars` first.
* **`csimp` and `@[extern]`.** Out of scope by theorem-visible hypothesis, §5 N1 and N2.

---

## 4. Reuse

Line counts at `dev/verify` HEAD. "Condition" is what must be true for the asset to be carried.

### 4.1 Carried unchanged

| Asset | File(s) | Lines | Condition |
|---|---|---|---|
| λ□ semantics: flags, values, `WcbvEval`, env queries, substitution, metatheory | `Semantics/{Flags,Values,Eval,Env,Substitution,Metatheory}.lean` | 1,225 | `Flags.lean:19-24`'s header rewritten (it asserts block form; the capstones run applied) |
| de Bruijn / closedness kit | `Closed.lean` | 871 | none |
| `toBvar` metatheory + the `Basic.lean` de-partialization it rests on | `Abstract.lean`, `Basic.lean` | 659 | none |
| `closeFix`/`substFix` inverse | `FixMetatheory.lean`, `FixUnfold.lean` | 1,184 | re-aimed at T6 `fixIntro` instead of an `Erases` rule |
| ι reversal (β-chain of field applications = `iota_red`) | `IotaBridge.lean` | 207 | re-aimed at T6 `elimInline` |
| `Erasable` + stability kit | `Erasability.lean` | 230 | none |
| verified relevance oracle and its discharge | `Relevance.lean`, `RelevanceCheck.lean`, `CheckerAdequacy.lean`, `OracleDischarge.lean` | 495 | **must** enter the capstone's import closure (T8 field 4) |
| `optimize` and `optimize_correct` | `Optimize.lean` | 1,090 | wired in as T6's `optimize` and as the template for every other pass |
| first-order non-erasability | `FirstOrder.lean:103-155` | ~55 | re-indexed onto `FirstOrderInd` |
| the coverage artefact | `VerifyBench/*` + `STATUS.md` | 520 | becomes T10's acceptance test |
| shipping-side edits enabling induction (de-partialized `toBvar` family, nine `@[partial_fixpoint_monotone]` lemmas, `visitCasesEta`/`visitCtorEta`) | `Erasure.lean:364-500`, `Basic.lean` | ~380 diff | none. The `isErasable` kernel reroute (`Erasure.lean:151-187`) is a *separate, behaviour-changing* edit and is not part of this asset |

### 4.2 Re-anchored — statements change, proof skeletons and lemma inventories do not

| Asset | File(s) | Lines | Condition |
|---|---|---|---|
| run algebra for `EraseM` (75 run lemmas) | `ErasureRun.lean` | 3,234 | independent of which relation the bridge concludes; survives intact |
| the 18-motive fixpoint induction over the real `visitExpr` | `VisitExprRefines.lean` | 4,641 | all eighteen motives' `Erases` conjuncts restated against T2 and T8's factored conclusion. Realistic reuse 55–65%: scaffolding, admissibility, the `⊑` conjunct, binder/telescope lemmas, run plumbing |
| `Erases` transport metatheory | `Erases.lean` (transport half), `ErasesAbstract.lean`, `ErasesStrengthen.lean`, `ErasesUniform.lean` | ~2,300 | per-rule inductions: surviving rules' arms transfer verbatim; deleted rules take their arms with them |
| subject reduction as defeq | `SubjectReduction{,Full,Iota}.lean` | 1,414 (~1,050 after de-duplication) | one source relation (T4); the β arm written once, not three times |
| environment erasure discharged from registration records | `EnvErasure{,Nonrec,Rec}.lean` | 1,640 | restated as the single `ErasesEnv` (T3), keeping the property that it is *derived from what the run registers* rather than assumed — better than the paper's presentation |
| cold-start technique (subject = `Erasure.erase`; `Σ`, `t`, records, closedness produced by the run) | `ColdStart{,Shape,Induction,Run,Delta}.lean` | 6,415 | the unconditional shape induction and the run decomposition are durable; most of the bulk is premise plumbing that T9 deletes |

### 4.3 Deleted

* **`Erases` rules with no `[S Fig. 18]` counterpart**: `ctor`, `ctor_head`, `cases`, `fix`,
  `const_fix`, `fixvar` — and their arms in every transport lemma and in the 18 motives. The
  content moves to T3 (declarations) and T6 (passes).
* **`ErasureCtx`** (`ErasureContext.lean`) as an index of the specification, all twelve columns,
  plus the thirteenth map bolted outside it and its coherence predicate. Registry facts belong
  in the T8 bridge, not in the relation `[L R3]`.
* **Seven of the eight source-evaluation relations** (`SEval`, `SEvalβ`, `SEvalβδ`, `SEvalβζδ`,
  `SEvalβζδι`, `SEvalData`, `SEvalDataC`, `SEvalDataι`) — one survives, flag-parameterised (T4).
  Two are dead, one is documented as incorrect, two are incomparable.
* **`ErasesEnvDelta`** (matches the pointwise environment erasure the paper does not use) and
  the five `Registered*` predicates plus three `RegisteredClosure*` structures it sits beside —
  one relation, one name (T3).
* **Four `*BridgeHyps` bundles** (`BridgeHyps`, `DataBridgeHyps`, `CasesBridgeHyps`,
  `ProjBridgeHyps`) plus `DeltaHyps`, `BlockHyps`, `RecBlockAgreement`, `RegBridgeHyps` — one
  `PrimSpec` (T8). One primitive is currently specced twice and `register_inductive` three times.
* **`IotaRelevant`, `IotaShape`** — constructed nowhere, at any `Γ`; premises that delete
  exactly the falsifying derivations. Deleted, not re-proved.
* **The ι and proj discharge *chains*** as chains (`IotaPattern`, `IotaDischarge`,
  `SubjectReductionIota`, `ProjPattern`, `ProjDischarge`), `RecBlockErasure`, and the
  `ErasesCorrectData`/`ErasesCorrectIota` simulations — everything keyed on the six deleted rules.
  `Erases.proj` itself survives; `IotaBridge.lean` survives and is re-aimed.
* **`eraseCore`** (`EraseCore.lean`) except the fuel/monotonicity lemmas `FirstOrder.lean`
  reuses — refuted as a bridge by its own addendum.
* **`FirstOrderValue` + `InformativeType`** as the observational domain — replaced by
  `FirstOrderInd` (T7); the *proof* content at `FirstOrder.lean:103-155` is kept.
* **Dead layers**: the three "museum" sections, the seven consumer-free top-level theorems, the
  `Export/EvalT.lean` `Type`-valued twin, `ShippingCorrect.lean` as a separate layer, the
  duplicate definitions the review machine-confirmed (`LBTerm.rec'` = `LBTerm.recData`, the four
  `*_eq_map` lemmas, `subst_shift_cancel` twice), the twenty-member Γ↔E agreement family, the
  eight copies of the four-line spine refutation.
* **All prose trust ledgers** (three copies) — replaced by T11's measured one.
* **~3,000–3,500 comment lines** of changelog: slice tags, commit hashes, dates, memory
  references, "used to"/"no longer"/"retired"/"re-pin" narration, and every claim the review
  measured false (`Flags.lean:19-24`; the seven "no `addPat` clause" sites; the eight
  "`addInduct_WF` is `sorry`" sites; the five stale oracle descriptions; `Supported.casesApp`'s
  sparse-`casesOn` sentence; the `ProjDischarge`/`ProjPattern` contradiction about `proj_defeq`).

---

## 5. Non-goals and scope restrictions

**Rule.** Every restriction below is a **theorem-visible hypothesis** — a binder in the
capstone's statement or a decidable predicate on the input — never a field hidden inside a
bundle, and never silence. A reader auditing coverage reads the statement and `Supported`, and
finds every hole there.

| # | Restriction | Form in the statement | Why |
|---|---|---|---|
| N1 | `@[csimp]` replacement | `hcsimp : cfg.csimp = false` | only *propositional* equality is available, and the shipping code's own comment warns the result may be ill-typed; a defeq-based simulation cannot justify it `[R C4, R6]` |
| N2 | `@[extern]` axiomatisation | `hextern : cfg.extern = .preferLogical`, or `AxiomSpec Σ` enumerated per axiom | footnote 13 of `[R]` concedes a mismatched realizer is "a source of unsoundness"; the realizers (`axioms.ml`, Zarith, Baker's-trick arrays) are verified by nobody `[Z 4]` |
| N3 | machine `Nat`/`Int` | `hnat : cfg.nat = .peano` | a data refinement (unary ↔ i63) with an overflow side condition and a silent `Int`/`Nat` cast, not an erasure rule `[R C7, R8]`. Stated as a future T6 pass, not as an omission |
| N4 | constructor argmask pruning | `hprune : cfg.remove_irrel_constr_args = false` | `[L §4]` "removing dummy arguments" is explicitly outside Letouzey's proved core; the alternative is the masked-erasure invariant `[R R12]`, which is deferred |
| N5 | typeclass-dispatch auto-inlining | `hinline : cfg.auto_inline_typeclass_dispatch = false` | unverified product code; the `.inlinings` channel is a directive to peregrine `[Z 5, Z 9]` |
| N6 | `IO`, `Task`, `String`, `UInt*`, `Float`, `@[implemented_by]`, computed fields | conjuncts of the decidable `Supported env e` over `e` **and its dependency closure** | `[R §6.2]`; must be decidable and checked on real programs `[R R16]` |
| N7 | termination transfer and progress: `[L Thm 12]`, `[S §5.6]` `progress`, `[S §5.5]` normalization, `wcbv_standardization` | the capstone is conditional on `SEval env Us fl [] e v` | lean4lean has no progress, canonicity or normalization result. `[S]` proves its own capstone modulo an axiom; mirroring its conditional form is the honest option, and a decidable benchmark side-check replaces the missing half `[S §4.5 option 1]` |
| N8 | the eraser's input is the compiler-facing body, not the kernel-checked one (`_unsafe_rec`) | `hbody : the erased declaration body is kernel-typeable` — an explicit hypothesis, or a restriction to declarations where the two coincide | `[R §4.1, fn. 11]`. The two bodies are propositionally equal by the equation lemmas, not definitionally. Do not paper over it |
| N9 | universe-polymorphic *subjects* | `hUs : Us = []` at the capstone (subject only) | dependencies must **not** be restricted: every typeclass method the benchmarks touch is polymorphic. Restricting the dependency side is what kept coverage at zero |
| N10 | `.ast` serialisation | conclusion stops at `Program`; **one** ledger row naming `Serialize.to_sexpr` and peregrine's `theories/serialization/` Sound/Complete proofs as the counterpart that exists on the other side | `[Z 1]`. Silence is not an option; either constrain the bytes or say plainly that they are uncovered |
| N11 | `.ast.inlinings`, `.mli`, and the rest of `#erase` around the verified `erase` call | one ledger row; plus the cheap true statement for `.inlinings` if taken: every listed kername occurs as a `ConstantDecl` with `Some body` in the same file | `[R R14]`, `[Z 5]` |
| N12 | panicked runs | `hnp : ¬ run.panicked`, **or** a per-site refutation table (two sites refuted by lemma, T8) | a `panic!` succeeds at `EraseM` and returns `.box`; `.ok` alone does not exclude a wrong program `[R R13]`, `[Z 8]` |
| N13 | typed λ□ᵀ | the conclusion names `.untyped` | no consumer asks for λ□ᵀ from Lean and the typed pipeline inlines before erasure `[Z 7]` |
| N14 | AST size, specialisation, performance | stated as a non-goal in the README and the ledger | `[Z 11]`: nobody may read a correctness theorem as a claim about the 2–4× size gap |
| N15 | Lean kernel theory | not stated here at all; it lives in lean4lean | the discrimination rule. Any lemma about `VEnv`/`VExpr`/`HasType`/`IsDefEq` that is not about erasure goes upstream, including the subsingleton criterion of T3 if it turns out to be kernel-generic |

---

## 6. Documentation and code-quality policy

**Docstrings.**

1. A docstring states **the current fact only**. No "used to", "rewritten at `<hash>`", "was
   previously", strikethrough, commit hash, date, slice tag, round name, or reference to an
   agent memory store or an untracked handoff document. History goes in the commit message.
2. **One fact, one home.** A claim about upstream state lives once, in the T11 ledger, with the
   `file:line` and the command that measured it. It is never restated in a second file.
3. **Length budget**: field or lemma docstring ≤ 8 lines; module header ≤ 40 lines. Anything
   longer is a status document and belongs in `doc/`, tracked, not in a docstring.
4. **Every backticked identifier must resolve; every cited document must exist in the
   repository.** Enforced by CI grep.
5. A docstring says what the object *is* and, where it is not obvious, *why the hypothesis is
   not slack* — with a counterexample where one exists. The tree's best current docstrings
   (`IotaBridge.lean:96-111`, `Semantics/Values.lean:79`, `Semantics/Eval.lean:29`) are the model.

**Code.**

6. **No dead code.** Every declaration is in the capstone's transitive import closure, or is
   named in a short, tracked list of deliberate exceptions with a reason. "Kept because it was
   once true" is not a reason; git remembers.
7. **No duplicate definitions.** Before adding a definition, search for a definitionally equal
   one. The known duplicates (§4.3) are deleted, not documented.
8. **No forked relations.** Growth is by parameterisation, not by copying a relation and adding
   a rule. If a signature must stay stable for a consumer, that is a wrapper, not a second proof.
9. **Kernel lemmas go upstream.** Anything about `VEnv`/`VExpr`/`HasType`/`IsDefEq`/`TrExprS`
   that is not about erasure is lean4lean's; this repository holds no `Lean4Lean`-namespace
   declarations.
10. **One trust ledger** (T11), measured in CI, never narrated in prose.
11. **Non-vacuity guards.** Every relation and every pass ships a concrete inhabitant witnessing
    that its hypotheses are satisfiable and its conclusion non-trivial, in the style of
    `Semantics/Metatheory.lean:417` and `Optimize.lean:1066`.
12. **No `native_decide`**; `set_option` only with a comment saying why; no `@[simp]` on foreign
    namespaces. (The tree is already clean here; keep it.)

---

## 7. Acceptance criteria

The checklist the final review runs. Each item is mechanical or has a named artefact.

**Structure**

1. `Erases` has exactly ten rules and its signature mentions `VEnv`, `List Name`, `VLCtx`,
   `Expr`, `LBTerm` and nothing else. `grep -n "ErasureCtx" LeanToLambdaBox/Erases.lean` is empty.
2. No rule of `Erases` produces `.construct`, `.case` or `.fix`.
3. The rule-by-rule table of §3.3 is tracked next to `Erases.lean`, covers every rule of
   `[S Fig. 18]` and every rule of `Erases`, and names every deviation.
4. Exactly one `inductive SEval*` in the tree; exactly one environment relation; exactly one
   hypothesis bundle (`PrimSpec`); exactly one trust ledger.
5. Every L4 pass has an `optimize_correct`-shaped theorem and a non-vacuity guard, and
   `LBCompile.correct` composes them.

**Content**

6. T5's statement has exactly five hypotheses and none of them is named `Supported`, `Relevant`,
   `Iota*`, `*Consistent` or `*Hyps`.
7. `[S Fig. 18]`'s `Subsingleton` condition appears exactly once, in T3, and is **derived** from
   the environment rather than assumed — or, if not yet derived, is a single named class-**C**
   hypothesis with a ledger row, and `Acc.rec`/`Eq.rec`/`And.rec`/`Decidable` are demonstrably
   inside the fragment either way.
8. `FirstOrderInd` is decidable and `decide`s to `true` on `Nat`, `Bool`, `List Nat`, `Nat × Nat`
   and `VerifyBench/Src/BinaryTrees.lean`'s `Tree`.
9. `OracleDischarge` is in the capstone's transitive import closure, and the capstone's
   `oracle_sound` obligation is discharged rather than assumed.
10. `Erases.sort_erasable` and `Erases.forallE_erasable` exist, so two of the eraser's sixteen
    `panic!`/`unreachable!` sites are refuted; the other fourteen are enumerated in one table
    with the premise excluding each.
11. `Supported` is decidable and `decide`s on the five VerifyBench programs; the
    sparse-`casesOn` shape is visible *in `Supported`*.
12. The capstone's conclusion contains `LBWfPeregrine`, matching what `peregrine validate`
    checks, including applied-constructor form.

**Non-vacuity**

13. `T10`'s `arith_covered` elaborates under `lake build`, with every hypothesis of T9
    simultaneously inhabited by a checked term.
14. A per-program coverage table for all five VerifyBench programs is tracked, stating what each
    program's erasure is and is not covered by, and the number is not zero.

**Trust**

15. `#print axioms` on T5, T6, T8 and T9 matches a committed fixture, checked in CI. T6's passes
    print class **A** (no `sorryAx`).
16. Every `sorryAx` root is named with `file:line` **in the pinned lean4lean**, measured by the
    CI job, and fork-authored holes are distinguished from inherited ones.
17. No `sorry` and no `axiom` in this repository. `PrimSpec` is a structure, and every
    class-**C** hypothesis is a binder in a stated theorem.

**Hygiene**

18. Comment fraction below 20%; zero occurrences of slice tags, commit hashes, dates, memory
    references, or "used to"/"no longer"/"retired" narration in docstrings (CI grep).
19. Every backticked identifier in a docstring resolves; every cited document exists (CI grep).
20. Zero declarations outside the capstone's import closure except a short tracked exception list.
21. No `Lean4Lean`-namespace declaration in this repository.

**Delivery**

22. The verified eraser is on the branch consumers pin, CI builds it, and the pinned lean4lean
    rev in the committed `lakefile.toml` is the one every measurement was taken at `[Z 10]`.

---

## 8. Open questions the design phase must answer

**Q1 — Does `LBCompile` reproduce `visitExpr` exactly?** T8's factored conclusion requires a
function on λ□ whose output matches the shipping eraser's, including binder order in `mkAlt`
(whose own comment records "the other way around led to segfaults"), binding order in `mkDef`
("may be wrong"), over-application placement outside the `.case` node, and η-expansion driven by
`inferType` rather than by the environment's arity table. If exact equality is not attainable,
T8's conclusion weakens to membership in the composite *relation* — which is still `[S §7.2]`'s
posture (graph ⊆ relation) but loses the "same result" reading of `[S §7.4]`. Decide early; it
shapes the 18 motives.

**Q2 — Where does Lean's subsingleton/large-elimination criterion get derived?** T3's `ElimBody`
at a `Prop`-valued inductive needs it. The upstream ingredients exist at the pinned rev
(`Ordered.pat`, a proved `addInduct_WF`) but have never been assembled. If the criterion is
kernel-generic, N15 sends it to lean4lean. This is the rework's single research item; everything
else is engineering.

**Q3 — `_unsafe_rec`: hypothesis or restriction?** N8 offers both. Which declarations in the
five benchmark programs actually have a compiler body differing from the kernel body, and what
does the equation-lemma transport cost?

**Q4 — Do the emitted eliminator declarations blow up the deliverable?** T3's runtime-library
design emits a λ□ definition per recursor; T6's `elimInline` removes it again at use sites. The
collaborators already measure Lean's ASTs at 2–4× Rocq's `[Z]`. Confirm the passes restore
parity before the design is frozen.

**Q5 — Parameters in constructor applications.** Raised on Zulip and never answered: does
peregrine's `dearg_ctors`/`dearg_consts` remove them, or is the frontend expected to? The answer
decides whether `ErasesDecl.ctor` drops parameters and on what typing evidence.

**Q6 — Is `FirstOrderInd` equivalent to `[L Def. 14]` (data-type) and `[L Def. 6]`
(logic-free)?** Settle before reusing the vocabulary; `[L Thm 15]`'s conclusion needs both.

**Q7 — `Quot`.** `Quot.mk`/`lift`/`ind` are kernel primitives with an ι-rule and no PCUIC
analogue. T3 gives them a declaration class; confirm the ι-rule is in T4's `SEval` and that
`[L Def. 14]`'s "closed inductive term reduces to a constructor" survives quotients.

**Q8 — Should `Erases` be compared to MetaRocq's `erases` mechanically?** §3.3's table is the
minimum and is required. A transport into `rocq/` reaching the *relation* (today it reaches only
`LBTerm` and `WcbvEval`) would be stronger. Scope it or drop it explicitly.
