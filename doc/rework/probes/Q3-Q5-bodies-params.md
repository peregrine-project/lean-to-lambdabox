# Q3 / Q5 — compiler bodies vs kernel bodies; parameters in constructor applications

**Probe report for the design phase.** Answers `00-REFERENCE-SPEC.md` §8 Q3 and Q5.
Everything below is measured at `dev/verify` HEAD `d5a10f3`, Lean `v4.33.0-rc2`,
lean4lean rev `20ec229`, peregrine-tool at `/home/barabba/Documents/Research/Projects/Peregrine/peregrine-tool`,
MetaRocq 1.5.1+9.1 under `~/.opam/peregrine`. Commands to reproduce are in §5.

---

## 0. Summary

**Q3.** Every one of the five VerifyBench programs erases compiler bodies that the kernel
never checked in that form. 32 declaration names across the suite carry a
`._unsafe_rec` compiler body; **all of them are type-correct at the declared type** (so
`TrExprS` reaches them and `HasType` holds), and **none is definitionally equal
to the kernel body**, nor to the constant it defines. Two of them (`countFlipsAux`,
`fannkuchLoop`, both `partial def`) have **no kernel body at all** — their kernel-facing
constant is an `opaque` whose value is `Inhabited.default`, added to lean4lean's `VEnv`
with a type and *no* defining equation. `Arith`, the T10 minimum, is affected: `Nat.add`,
`Nat.mul`, `Nat.sub`, `Nat.pow` are all `_unsafe_rec`.

Consequence: `ErasesDecl.defn` as written in T3 (§2, "`env.constants c = some ⟨_, some body⟩ →
Erases … body b'`") is **false on every benchmark**. N8 must be resolved as an *environment
extension*, not as a restriction: the theorem's source side runs at `envC`, obtained from
`env` by one `VEnv.addDefEq` per rewritten declaration, whose `WF` obligation is exactly the
type-correctness fact measured here and is decidable per program. The kernel-body/compiler-body
gap becomes one named ledger row (equation lemmas, propositional, not transported).

**Q5.** **peregrine drops the parameters; the frontend must keep them.** MetaRocq's
`remove_params_optimization` is the second pass of `verified_lambdabox_pipeline`, which
peregrine's `untyped_transform_pipeline` runs verbatim. `dearg_ctors`/`dearg_consts` are a
*different* mechanism living in the **typed** (`ExAst`) pipeline and never run on untyped
Lean output. The frontend already does the right thing, exactly: in all five programs, every
constructor occurrence is applied to exactly `ind_npars + cstr_nargs` arguments —
MetaRocq's `EAst.cstr_arity` — with `tConstruct … ()` (empty block payload). 0 under-applied
occurrences out of 982. `peregrine validate` accepts all five `.ast` files, but it checks
strictly less than the pipeline's precondition: it omits η-expandedness, and
`run_untyped_transforms`' precondition obligation is `Admitted` in peregrine
(`theories/erasure/Transforms.v:375`). `LBWfPeregrine` must therefore be
`wf_eprogram all_env_flags` **plus** `EEtaExpandedFix.expanded_eprogram`, not just what
`validate` checks.

---

## 1. Q3 — `_unsafe_rec`, compiler bodies, kernel bodies

### 1.1 How `#erase` obtains a declaration body

`Erasure.visitMutual` (`LeanToLambdaBox/Erasure.lean:859-918`) opens with

```lean
let ci := (← Compiler.LCNF.getDeclInfo? name).get!
let names := ci.all                       -- possibly these are ._unsafe_rec
```

and Lean's `getDeclInfo?` (`Lean/Compiler/LCNF/ToDecl.lean:100-102`) is

```lean
def getDeclInfo? (declName : Name) : CoreM (Option ConstantInfo) := do
  return (← getEnv).find? (mkUnsafeRecName declName) <|> (← getEnv).find? declName
```

so **whenever `foo._unsafe_rec` exists it wins**, and with it its `all`, its `levelParams`
and its `value?`. The value is then passed through `prepare_erasure`
(`Erasure.lean:556-576`), whose first step `replaceUnsafeRecNames` rewrites every nested
`bar._unsafe_rec` occurrence back to `bar`. So the erased term never *mentions* an
`_unsafe_rec` name — but it is the `_unsafe_rec` *body*.

`foo._unsafe_rec` is created by `Lean.Elab.addAndCompilePartialRec`
(`Lean/Elab/PreDefinition/Basic.lean:280-294`) at `safety := .partial`, called from
structural recursion (`Structural/Main.lean:198`), well-founded recursion (`WF/Main.lean:83`),
`partial_fixpoint` (`PartialFixpoint/Main.lean:218`) and `partial def` (`Main.lean:36`).
Its body is the *top-level self-recursive* one, with self-references rewritten to
`foo._unsafe_rec`.

`visitMutual` then classifies with `name_occurs name (ci.value!)`, which compares against
`remove_unsafe_rec n'` (`Erasure.lean:522-528`) — so a rewritten self-reference *is* detected,
`nonrecursive := false`, and the declaration is emitted as `⟨.fix defs i⟩`. This is why
`Nat.add` appears in `Arith.ast` as `(tFix ((def (nNamed "Nat.add") …)))`.

### 1.2 Which declarations are affected (measured)

Erased-declaration sets extracted from the five `.ast` files; per-name facts queried from the
live `Lean.Environment` (probe `q3.lean`, `q3qs.lean`).

| Program | erased `ConstantDecl`s | with `_unsafe_rec` | of which `partial def` (no kernel body) | `@[extern]` | `@[implemented_by]` |
|---|---|---|---|---|---|
| Arith | 27 | **4** (`Nat.add`, `Nat.mul`, `Nat.sub`, `Nat.pow`) | 0 | 5 (logical body preferred) | 0 |
| Sieve | 41 | 10 | 0 | 7 | 0 |
| Quicksort | 40 | 11 | 0 | 7 | 0 |
| BinaryTrees | 42 | 10 | 0 | 8 | 0 |
| Fannkuch | 49 | 15 | **2** (`countFlipsAux`, `fannkuchLoop`) | 6 | 0 |

Union across the suite: **32 distinct names / 33 declarations** with an `_unsafe_rec`
compiler body (`divmod` is declared once in `Sieve.lean` and once in `Quicksort.lean`).
30 elaborated by **structural recursion**, 1 by **well-founded recursion** (`findI`),
2 by **`partial def`**.
`@[implemented_by]` does not occur anywhere in the five dependency closures — the shipping
eraser ignores it by design (`Erasure.lean:676-679`), and this probe confirms that costs
nothing on the benchmarks. `Eq.rec` is erased as a λ□ **axiom** (a `recInfo` has no value);
that is N2/`ErasableAxioms` territory, not N8.

### 1.3 The three facts a correctness theorem has to live with

Probes `q3b.lean` (28 declarations, group A) and `q3qs.lean` (Quicksort's 11) compute
`body := replaceUnsafeRecNames (foo._unsafe_rec).value!` and ask Lean three questions.
Results are **uniform across all 33 declarations, no exceptions**:

| Question | Answer |
|---|---|
| `inferType body` defeq the declared type? | **true**, all 33 |
| `isDefEq body (kernel body of foo)`? | **false**, all 31 that have one |
| `isDefEq body (.const foo)`? | **false**, all 33 |

*(`isDefEq` measured at `maxHeartbeats 100000`. The negative answers are not timeouts: the
recursive occurrence sits under a binder, so both sides are stuck — `fun n m => Nat.rec …`
against `fun n m => match m with … Nat.add n m'` cannot be joined without reducing on the
variable `m`.)*

**F1 — the compiler body is kernel-typeable.** This is the good news and it is the pivot of
the whole answer (the group-A probe reports `URbodyTypeOk=true` for all 28; the Quicksort
probe `tyOk=true` for all 11). `TrExprS env lvls [] body vbody` is available and `env.HasType lvls [] vbody
(type of foo)` holds. Nothing in the erasure relation, in `Erasable`, or in `Erases.box`'s
witness has to be weakened. N8's "`hbody : the erased declaration body is kernel-typeable`"
is *true*, and it is **decidable** — it is exactly what running lean4lean's checker on
`(body, type)` establishes, so it can be discharged per program rather than assumed
(class C → class B for the benchmark instantiation in T10).

**F2 — it is not defeq to the kernel body.** So no `IsDefEq`-based argument can silently
substitute one for the other. The two are related by the *equation lemmas*, which are
propositional (`foo.eq_def`, `foo.eq_1`, …). lean4lean's `VEnv`/`IsDefEq` has no notion of
propositional equality to transport across, and `SEval.defeq` (T4) concludes `IsDefEq`, not
`Eq`. **The transport that N8 alludes to is not available in this development at any price.**

**F3 — for `partial def` there is nothing to transport to.** `countFlipsAux` and
`fannkuchLoop` reach the kernel as `opaqueInfo`, value

```
fun (perm : List Nat) (count : Nat) => let inst := Inhabited.mk Nat count; Inhabited.default Nat inst
```

i.e. a junk inhabitant. lean4lean's `TrEnv'.opaque` (`Verify/Environment/Basic.lean:571-577`)
adds such a constant with `VEnv.addConst` **only** — no `addDefEq`. So in `env` these two
constants have a type and *no defining equation*: δ can never unfold them, and no `SEval`
derivation can compute with them. Their erased λ□ declarations are the real recursive bodies.

*(Note also `TrEnv'.ignore` at `Verify/Environment/Basic.lean:537-540`: any `ci` with
`¬ safety ≤ ci.safety` is dropped. At `safety := .safe` that is every `.partial` and
`.unsafe` declaration, so every `foo._unsafe_rec` constant is **absent from the `VEnv`**.
`replaceUnsafeRecNames` is what saves the eraser here: the emitted term mentions only safe
names, which are present. Had it not run, `Erases.const`'s premise `env.constants c = some ci`
would be unsatisfiable.)*

### 1.4 What a correctness theorem can therefore say

Three options; the recommendation is (B).

**(A) Restrict to declarations where the two bodies coincide.** N8's second alternative.
Measured cost: excludes 33 declarations, including `Nat.add`/`mul`/`sub`/`pow`. **Arith covers
zero**, and Arith is T10's stated minimum. Dead on arrival — this is the same mistake that
kept the current tree's coverage at 0/5 (`axiom_free`, §T9).

**(B) State the theorem at the compiler environment `envC`.** Define, once,

```lean
/-- `env` extended with the defining equation the compiler actually uses. -/
def VEnv.addCompilerDefn (env : VEnv) (n : Nat) (c : Name) (us) (body ty : VExpr) : VEnv :=
  env.addDefEq ⟨n, .const c (levelParams), body, ty⟩
```

and let `envC` be `env` extended this way for each `_unsafe_rec`-carrying constant in the
run's dependency closure. `VEnv.addDefEq` (`Theory/VEnv.lean:37`) takes any `VDefEq`; its
`WF` obligation is that both sides are typed at `ty` in the current environment — which is
exactly **F1**, measured true, and which for `partial def` is *the only* way to give the
constant a body at all (F3). The capstone's hypotheses gain

```lean
    (hcomp : CompilerEnv env envC e)   -- decidable per program: run lean4lean's checker
```

and `T3`'s `ErasesDecl.defn` reads its body off `envC.defeqs`, not off `env.constants`.
T4's δ rule unfolds `envC`'s equations, so `SEval` is a semantics *for the program the
compiler compiles* — which is the honest subject, and is what `[R §4.1]` says the
implementation chose. `Erasable`, `Erases`, `TrExprS` and the relevance oracle are all
unchanged: they are `env`-indexed and `env ≤ envC`, so every stability lemma lifts by
`VEnv.LE`.

What is *not* covered, and becomes exactly one ledger row (class **E**):

> `envC` and `env` agree only propositionally. For every `_unsafe_rec` declaration `foo`,
> `foo`'s compiler body and its kernel body are related by Lean's equation lemmas
> (`foo.eq_def`), which are `Prop`-level and are not transported here. A program whose
> observable answer differs between the two bodies is outside the theorem. For `partial def`
> there is no kernel body and the gap is total.

This is one row, it is true, it is checkable, and it costs no coverage.

**(C) Two-body relation inside `ErasesDecl`.** Carry both bodies and a hypothesis
`∀ closed args, foo args ≡ compilerBody args`. Rejected: the hypothesis is not expressible
against lean4lean's `IsDefEq` (F2), and stating it as a `Prop`-level equality drags Lean's
`Eq` and the equation-lemma machinery into a development whose whole discipline is that the
source side is lean4lean's and only lean4lean's.

### 1.5 Consequences for the spec

| Item | Change forced |
|---|---|
| **N8** | Resolves to *hypothesis*, in form (B). Reword: "the eraser's input is the compiler-facing body; the theorem is stated at `envC`, the kernel environment extended by the compiler's defining equations, whose well-formedness is `TrExprS` + `HasType` on each compiler body and is **decidable and discharged per program**". Drop the "or a restriction to declarations where the two coincide" alternative — measured to cover 0/5. |
| **T3** | `ErasesDecl.defn`'s premise must read a `VDefEq` off `envC.defeqs`, not `env.constants c = some ⟨_, some body⟩`. That notation is anyway wrong at the pinned rev: `VEnv.constants : Name → Option VConstant` carries only `uvars`/`type`; bodies live in `defeqs : VDefEq → Prop` (`Theory/VEnv.lean:6-21`). Fix the spec's shape. |
| **T3** | Needs a **`partial`/`opaque` declaration class**. `TrEnv'.opaque` gives a constant with no defeq; `ErasesDecl.ax` would emit a λ□ axiom, but the eraser emits a `.fix` definition. Under (B) this is uniform with the rest — the opaque constant gets its compiler equation in `envC` — but the spec must say so, or Fannkuch is out. |
| **T4** | `SEval`'s δ rule is at `envC`. `SEval.defeq` still concludes `envC.IsDefEq`; `Erasable`/`IsArityUpTo` stability lifts along `env ≤ envC` by the existing `.mono` lemmas. |
| **T9** | One more class-**C** binder, `hcomp`, decidable, discharged in T10. |
| **T11** | One class-**E** row (§1.4). |
| **T10** | The Arith discharge must *include* `hcomp` for `Nat.add`/`mul`/`sub`/`pow`. It is four `TrExprS`+`HasType` checks; measured to hold. |
| **`Supported`** | Should *report*, not exclude: a decidable predicate `HasCompilerBody` over the dependency closure, so a reader auditing coverage sees them. Excluding them is option (A). |

---

## 2. Q5 — parameters in constructor applications, applied vs block form

### 2.1 Who drops the parameters

**peregrine does.** `theories/erasure/Transforms.v:147-157`:

```coq
Program Definition untyped_transform_pipeline … :
   (* Standard evaluation, with cases on prop, guarded fixpoints, applied constructors *)
   (eval_eprogram_mapping EWcbvEval.default_wcbv_flags)
   (* Target evaluation, … constructors as block *)
   (EProgram.eval_eprogram final_wcbv_flags) :=
  rebuild_wf_env_transform_mapping true true ▷
  verified_lambdabox_pipeline_mapping ▷ …
```

and `verified_lambdabox_pipeline` (MetaRocq `ErasurePlugin/Erasure.v:163-188`) is, in order:

1. `guarded_to_unguarded_fix`
2. **`remove_params_optimization`** — *"Remove all constructor parameters"*
3. `rebuild_wf_env_transform` at `ERemoveParams.switch_no_params all_env_flags`
4. `remove_match_on_box_trans`
5. `rebuild_wf_env_transform`
6. `inline_projections_optimization`
7. `rebuild_wf_env_transform`
8. `constructors_as_blocks_transformation`

`remove_params_optimization` (`ETransform.v:739-746`) carries
`{wcon : EWcbvEval.with_constructor_as_block = false}` — **applied form is a typing-level
requirement of the pass, not a tolerated input**. It consumes `ind_npars` leading arguments
of every constructor application and sets `ind_npars := 0` in the declarations. This settles
`[Z]`'s unanswered question and confirms `[Z T1, Z2]` and T1's `with_constructor_as_block := false`.

**`dearg_ctors`/`dearg_consts` are a different mechanism and are irrelevant here.**
They configure `dearging_transform` (`Transforms.v:180-190`), which lives in
`typed_transform_pipeline` and operates on **`ExAst`** (typed λ□ᵀ), removing *logically
irrelevant* arguments using type information — ConCert's dearging, not parameter stripping.
An `Untyped` `.ast` — which is all the Lean frontend produces (N13) — goes to
`run_untyped_transforms` and never touches them. The `Eval`/`AST` backends set
`dearg_ctors_c := Compatible false` anyway (`theories/backends/{EvalBackend,ASTBackend}.v`).

### 2.2 What the frontend emits (measured, all five programs)

The exceptionless law, over every `tConstruct` occurrence in all five `.ast` files:

> **spine length = `ind_npars` + `cstr_nargs`**, block payload `()` (empty).

which is precisely MetaRocq's `EAst.cstr_arity mdecl cdecl := ind_npars + cstr_nargs`
(`Erasure/EAst.v:204`). Saturated occurrences / under-applied occurrences:

| Program | saturated | under-applied | `tFix` nodes |
|---|---|---|---|
| Arith | 42 | **0** | 4 |
| Sieve | 58 | **0** | 10 |
| Quicksort | 697 | **0** | 11 |
| BinaryTrees | 84 | **0** | 10 |
| Fannkuch | 101 | **0** | 15 |

Worked example, `Sieve.ast`:

```
(mutual_inductive_body Finite 1
  ((one_inductive_body "List" false IntoAny
     ((constructor_body "List.nil" 0) (constructor_body "List.cons" 2)) ())))
```

`ind_npars = 1`; `cstr_nargs` counts **fields only** (`cons` is 2, not 3). Applications carry
`1 + 2 = 3` arguments, the first being the erased type parameter:
`(tApp (tApp (tApp (tConstruct (inductive List 0) 1 ()) tBox) hd) tl)`.

The frontend code that produces this, and the two configuration knobs that would break it:

* `register_inductive` (`Erasure.lean:192-243`): `npars := indinfo.numParams`,
  `nargs := Array.count .keep argmask` where the mask has `ci.numFields` entries. At
  `remove_irrel_constr_args := false` (N4) the mask is all-`keep`, so `nargs = numFields`.
* `visitConstructor` (`Erasure.lean:731-760`): emits
  `.construct indid cidx []` applied to `param_args ++ filter argmask field_args ++ extra_args`.
  Parameters are **never** filtered — only fields are.
* `visitCtorEta` via `getCtorArity?` (`Erasure.lean:681`), and Lean's
  `getCtorArity? = numParams + numFields` (`Lean/Compiler/LCNF/Util.lean:33-35`). So the
  frontend's η-expansion target *is* MetaRocq's `cstr_arity`. This is not a coincidence to be
  relied on silently — it is the invariant `LBWfPeregrine` must state.

**So the frontend must NOT drop parameters, and must not be "fixed" to.** Dropping them would
(a) violate `isEtaExp_app`, whose condition is `n ≥ cstr_arity mind cdecl` including `npars`,
and (b) make `remove_params` strip real fields, silently producing garbage.

`ErasesDecl.ctor` in T3 is therefore right as written — `.construct iid k []`, arity-free,
arguments arriving by `.app` — and the *number* of those `.app`s is a property of the
`Erases.app` congruence plus the source term's own saturation, not something the relation
imposes. What must be imposed, in `LBWfPeregrine`, is η-saturation at `cstr_arity`.

### 2.3 What `peregrine validate` actually checks

`peregrine validate FILE` runs `Pipeline.peregrine_validate` (`theories/Pipeline.v:245-248`)
= `parse_ast ;; get_config ;; check_wf`. `check_wf` on an `Untyped` program is
`@check_wf_program EWellformed.all_env_flags` (`Pipeline.v:59-70`), i.e. `theories/CheckWf.v`'s
checker at

```coq
all_env_flags = {| has_axioms := true; term_switches := all_term_flags;
                   has_cstr_params := true; cstr_as_blocks := false |}
```

(`MetaRocq/Erasure/EWellformed.v:90-94`). Note `agda_eflags`/`agda_typed_eflags`
(`CheckWf.v:24-67`, with `has_cstr_params := false; cstr_as_blocks := true`) are **not** used
by the CLI — grep finds no consumer. Under `all_env_flags` the checker enforces:

* closedness (`tRel i < k`), every `tConst` resolves, axioms allowed;
* `tConstruct ind c block_args`: the constructor exists **and `block_args = []`**
  (`cstr_as_blocks = false` branch, `CheckWf.v:123-131`) — the applied-form check.
  It does **not** check the spine length;
* `tCase`: `wf_brs Σ ind #|brs|` — branch count equals constructor count;
* `tFix`: index in range, **every `dbody` is a lambda**;
* inductives: `has_cstr_params || ind_npars == 0` — vacuously true here, so **non-zero
  `ind_npars` is accepted**; and `#|ind_projs| = cstr_nargs` for single-constructor types;
* global env: no duplicate kernames, decls well-formed in the preceding prefix.

Measured, all five accepted:

```
$ dune exec peregrine -- validate …/VerifyBench/ast/Arith.ast
Validating AST:
AST is valid
```
and likewise `Sieve`, `Quicksort`, `BinaryTrees`, `Fannkuch`.

**Two cautions the design must record.**

1. **`validate` is strictly weaker than the pipeline's precondition.** The first pass,
   `rebuild_wf_env_transform_mapping true true`, has
   `pre p := wf_eprogram efl p /\ (with_exp -> preserves_expansion with_fix p)` with
   `with_exp = with_fix = true`, i.e. `EEtaExpandedFix.expanded_eprogram p`
   (`ETransform.v:702-716`) — η-expandedness of **constructors and fixpoints**. `check_wf`
   checks none of it. And peregrine's own discharge is
   `theories/erasure/Transforms.v:372-375`:

   ```coq
   Program Definition run_untyped_transforms econf ind_reorder impl_box impl_lazy_force p :=
     run (untyped_transform_pipeline econf impl_box impl_lazy_force) (ind_reorder, p) _.
   Final Obligation.
   Admitted. (* assumed for now, check_wf should ensure this *)
   ```

   The comment is not true of `check_wf` as written. This is the seam where the frontend's
   theorem meets the middle-end's, and it is open on **both** sides today. Raise it upstream
   (repository rule: report, do not patch).

2. **`validate` accepts a wrong program.** `Quicksort.ast` is the one the eraser panics on
   (`doc/rework/03-DEV-FIX.md`, F-SPARSE: `visitCases` hits `unreachable!` on `_sparseCasesOn_`, returns
   `default = .box`, and the `cons` branch of the top-level match erases to `tBox`), and it
   validates clean. `LBWfPeregrine` is a *format* precondition, not a correctness statement,
   and the capstone must not be read as if it were.

### 2.4 The exact `LBWfPeregrine` predicate

The conclusion of T9 should carry, on the emitted `(Σ, t)`:

```lean
structure LBWfPeregrine (Σ : GlobalDeclarations) (t : LBTerm) : Prop where
  -- (a) what `peregrine validate` checks: EWellformed at all_env_flags
  fresh      : (Σ.map Prod.fst).Nodup
  declsWf    : ∀ (kn, d) ∈ Σ, LBWfDecl (declsBefore Σ kn) d
  closed     : LBClosed 0 t
  constsOk   : ∀ kn ∈ t.consts, ∃ d, Σ.lookupConstant kn = some d
  ctorApplied: ∀ occurrence of `.construct iid k blk` in Σ, t → blk = []      -- cstr_as_blocks = false
  ctorDecl   : ∀ occurrence of `.construct iid k _`, iid resolves in Σ and k < #ctors
  casesExh   : ∀ `.case (iid, np) _ brs`, brs.length = #ctors of iid in Σ
  fixLambda  : ∀ `.fix defs i`, i < defs.length ∧ ∀ d ∈ defs, d.body.isLambda
  projDecl   : ∀ `.proj ⟨iid, np, i⟩ _`, the projection resolves in Σ
  -- (b) what the pipeline additionally requires and `validate` does NOT check
  etaCtors   : ∀ occurrence of `.construct iid k []` at spine length n,
                 n ≥ Σ.cstrArity iid k                       -- = ind_npars + cstr_nargs
  etaFix     : LBExpandedFix Σ t                              -- EEtaExpandedFix.expanded
```

Design notes, each load-bearing:

* `etaCtors` uses **`cstrArity = ind_npars + cstr_nargs`**, mirroring `EAst.cstr_arity`. Both
  numbers must be read off `Σ`'s own `InductiveDecl`, so that the predicate is checkable on
  the emitted program alone, with no reference to Lean.
* Keep `ind_npars` **unconstrained** (the `has_cstr_params = true` posture). A predicate that
  demanded `ind_npars = 0` would describe peregrine's *output*, not its input.
* `ctorApplied` and `etaCtors` together are `[Z 3]`'s "constructor-form invariant", and they
  are exactly what makes composition with `remove_params` a statement rather than a hope.
* `etaFix` is the honest half. `visitMutual` carries the code's own
  `-- TODO: eta-expand fixpoints? (I think this must be done, unsure how far)`
  (`Erasure.lean:911`), and this probe did **not** verify `EEtaExpandedFix.expanded` on the
  five programs — only the constructor half (measured, clean) and `dbody.isLambda`
  (implied by `validate` passing). **Open sub-question for the design phase: check
  `expanded_eprogram` on the five `.ast` files before committing T9's conclusion to
  `etaFix`.** If it fails, the honest move is a ledger row plus an upstream report, not a
  weaker predicate that quietly matches what the frontend happens to emit.
* Do **not** put the block-form condition in. Block form is peregrine's pass 8's *output*
  (T1's `with_constructor_as_block := false` is right).

### 2.5 Consequences for the spec

| Item | Change forced |
|---|---|
| **Q5** | **Answered: peregrine drops parameters (`remove_params_optimization`); the frontend keeps them and must.** `dearg_*` is the typed pipeline and is not involved. |
| **T3 `ErasesDecl.ctor`** | Confirmed correct as written. It must **not** drop parameters, and needs no typing evidence to justify keeping them — the parameters arrive through `Erases.app` like any other argument, and are boxed by `Erases.box` because a type parameter is `Erasable`. §2.6 of the spec ("Lean-specific adaptations") should say this in one line. |
| **T1** | `with_constructor_as_block := false` confirmed by `remove_params_optimization`'s `wcon` instance argument, not merely by a Zulip remark. |
| **T9 / criterion 12** | `LBWfPeregrine` = §2.4. Criterion 12's "matching what `peregrine validate` checks" is **too weak** — `validate` omits η. Reword to "matching `untyped_transform_pipeline`'s precondition", and note that peregrine's own discharge of it is `Admitted`. |
| **N4** | Confirmed load-bearing for the *arity* bookkeeping, not just for pruning soundness: at `remove_irrel_constr_args := true` the emitted `cstr_nargs` shrinks while `visitCtorEta` still expands to `numParams + numFields`, and `Erasure.lean:638` re-indexes projection field indices. Keep it pinned false. |
| **T11** | Ledger row: "peregrine's `run_untyped_transforms` precondition obligation is `Admitted` (`peregrine-tool theories/erasure/Transforms.v:375`); `peregrine validate` checks `EWellformed` but not η-expandedness. `LBWfPeregrine` states the stronger predicate on our side; the middle-end does not yet consume it." |

---

## 3. Cross-cutting: what this means for T10's coverage table

* **Arith** — 4 compiler bodies (`Nat.add`/`mul`/`sub`/`pow`), all structural, all
  type-correct, none defeq to the kernel body. Under §1.4(B) it is coverable; under (A) it is
  not. Constructor form is clean (42/42 saturated). This is the T10 minimum and it *hinges*
  on Q3 resolving as (B).
* **Sieve, Quicksort, BinaryTrees** — same shape, 10/11/10 compiler bodies, all structural.
  Quicksort is separately blocked by the `_sparseCasesOn_` panic (`doc/rework/03-DEV-FIX.md`),
  which `Supported` must make visible (criterion 11).
* **Fannkuch** — 15 compiler bodies; additionally needs `findI` (well-founded recursion: kernel body is
  `WellFounded.fix`, compiler body is top-level recursion) and the two `partial def`s with no
  kernel body at all. It is the program that *forces* option (B); it also emits `Eq.rec` as a
  λ□ axiom, which is `ErasableAxioms`/N2 work.

---

## 4. Recommended edits to `00-REFERENCE-SPEC.md`

1. §8 Q3 → **answered**, resolution (B); replace the question with a pointer here.
2. §8 Q5 → **answered**; replace with the one-line rule "peregrine strips parameters; the
   frontend emits `cstr_arity`-saturated applied constructors".
3. §5 N8 → rewrite as the `envC` hypothesis; delete the "or restrict" alternative.
4. §2 T3 → fix the `env.constants c = some ⟨_, some body⟩` notation (bodies live in
   `VEnv.defeqs`); read bodies off `envC`; add the `opaque`/`partial` declaration class.
5. §2 T9 → add `hcomp`; define `LBWfPeregrine` per §2.4.
6. §7 criterion 12 → strengthen from "what `validate` checks" to "the pipeline's precondition".
7. §2 T11 → two new rows (§1.4's propositional-agreement row; §2.5's peregrine-`Admitted` row).

---

## 5. Reproduction

```bash
cd /home/barabba/Documents/Research/Projects/Peregrine/lean-to-lambdabox
lake build VerifyBench                       # writes VerifyBench/ast/*.ast (Quicksort panics, still writes)
lake env lean <scratchpad>/probe/q3.lean     # per-declaration: _unsafe_rec / safety / extern / implemented_by / structural|wf
lake env lean <scratchpad>/probe/q3qs.lean   # same, for Quicksort (imported separately: `divmod`/`modulo` clash with Sieve)
lake env lean <scratchpad>/probe/q3b.lean    # type-correctness and defeq of the 28 compiler bodies
lake env lean <scratchpad>/probe/q3c.lean    # the opaque value of the two `partial def`s

cd /home/barabba/Documents/Research/Projects/Peregrine/peregrine-tool
dune exec peregrine -- validate ../lean-to-lambdabox/VerifyBench/ast/Arith.ast   # → "AST is valid"
```

Constructor-form measurement: parse each `.ast` (S-expression), read `ind_npars` and
`cstr_nargs` from the `InductiveDecl`s, and compare every `tConstruct` spine length against
`ind_npars + cstr_nargs`. Script kept at
`<scratchpad>/ctorcheck.py` and `<scratchpad>/astparse.py`.

Primary sources consulted: `Lean/Compiler/LCNF/ToDecl.lean:100`,
`Lean/Elab/PreDefinition/Basic.lean:280`, `Lean/Compiler/LCNF/Util.lean:33`,
`Lean/Declaration.lean:453,463`; lean4lean `Theory/VEnv.lean:6-45`,
`Verify/Environment/Basic.lean:20-33,535-584`; peregrine-tool `theories/Pipeline.v:59-70,245`,
`theories/CheckWf.v:24-186`, `theories/erasure/Transforms.v:147-157,180-190,372-375`;
MetaRocq `ErasurePlugin/Erasure.v:163-195`, `ErasurePlugin/ETransform.v:702-746`,
`Erasure/EWellformed.v:70-100`, `Erasure/EAst.v:204`, `Erasure/EEtaExpanded.v:557`,
`Erasure/EEtaExpandedFix.v:187`.
