# Reference analysis — *Compiling Lean programs with Rocq's extraction pipeline*

**Document.** Simon Dima, "Compiling Lean programs with Rocq's extraction pipeline", MPRI internship
report, 2025-10-01, advised by Yannick Forster (Cambium, Inria Paris). 33 pages / 1641 text lines.
Source text used: `…/scratchpad/refs/lean_extraction_report.txt`.

**Why it matters for the rework.** This is the *design document of the object under verification*.
It is the only document that states, in the authors' own words, what the shipping eraser
(`LeanToLambdaBox/Erasure.lean`, `visitExpr` family, `#erase`) is supposed to do and why. It contains
**no theorem, no proof, and no formal semantics** — its "correctness argument" is an analogy to
Letouzey (2004) / MetaRocq erasure plus a handful of prose justifications, several of which are
explicitly flagged by the author as unsound or approximate. Every design point recorded below is
therefore a **proof obligation or a scoping decision** the rework must either discharge or exclude
by an explicitly stated, checkable side condition.

Throughout, `[R §x]` cites the report, `[E:n]` cites `LeanToLambdaBox/Erasure.lean` line `n` on
`dev/verify` (read here for grounding only — not edited).

---

## 1. Summary

The report describes a **bridge**, not a verified pass: Lean's fully-elaborated `Expr` (taken *at the
point where it would be handed to the Lean compiler*, not the kernel) is translated by a `MetaM`/`CoreM`
traversal into MetaRocq's untyped λ□ term language, serialized as S-expressions, and handed to the
`lbox`/`peregrine` tool, which reuses Rocq's *verified* λ□ → Malfunction backend. The claimed benefit
is that everything downstream of λ□ is already verified; the frontend itself is not, and the report
never claims it is.

The erasure criterion is Letouzey's: **a subterm is replaced by `□` exactly when its type is a
proposition (a proof) or a type former (`_ → … → Type`)** [R §4.1]. Everything else is translated
structurally, with four families of complication that the report itself enumerates:

1. **Representation mismatch.** Lean encodes constructors, pattern matching and (for the kernel)
   recursion as *constants*; λ□ has primitive `construct`, `case`, `fix`. Hence arity-aware
   application traversal, η-expansion of under-applied constructors/`casesOn`, over-application
   handling, and conversion of match arms from functions to open terms with λ□-side binders.
2. **Strictness.** λ□/Malfunction is call-by-value; `cond`, `ite`, `dite` and Lean's auxiliary
   matchers must be **inlined before erasure** (`@[macro_inline]`, `inlineMatchers`) or both branches
   are evaluated. `@[csimp]` lemmas are additionally applied to obtain tail-recursive implementations.
3. **Recursion source.** Definitions are taken from the *compiler-facing*, top-level-recursive bodies
   (`_unsafe_rec` suffix stripped), **not** from the kernel's recursor-elaborated bodies; mutual
   blocks become λ□ `fix`.
4. **Runtime realism.** `@[extern]` constants (and some constructors) become λ□ **axioms** realized by
   a hand-written `axioms.ml`; `Nat`/`Int` are lowered to machine/Zarith integers with `casesOn`
   rewritten into zero-tests and subtraction; `Eq.rec` is an axiom realized as the identity; `Array` is
   realized by one of three OCaml persistent-array implementations; irrelevant constructor fields are
   pruned (with unboxing left to a patched `lbox` flag).

The evaluation (10 benchmark programs, 19 variants, 10 pipeline configurations) concludes the OCaml
route is ~2.5× slower (geometric mean) than the Lean compiler, with `unionfind` (monadic, no inlining
in λ□) 10× worse and `even` faster. Known limitations: no `IO`, no `Task`, no fixed-width integers, no
`String` literals, small benchmark suite with little proof content.

**Stated verification objective: none.** The word "verified" in the report always refers to Rocq's
pipeline downstream of λ□ [R §3.3], never to this frontend. The rework's objective (a correctness
theorem for the Lean→λ□ step) is therefore *not inherited from this document* — the document supplies
only the object and its intended meaning.

---

## 2. Formal objects

The report has no formal development. The objects below are transcribed from its listings and prose;
where the shipping code makes the design point precise, the code's form is given alongside and marked
`[E:n]`.

### 2.1 Source language — `Lean.Expr` (Listing 1, [R §3.2])

Transcribed verbatim (the report's own simplification; "some constructors and arguments have been
omitted for brevity"):

```lean
inductive Expr where
  | lit (l : Literal)                                  | bvar (deBruijnIndex : Nat)
  | sort (u : Level)                                   | fvar (fvarId : FVarId)
  | const (declName : Name)                            | app (fn : Expr) (arg : Expr)
  | proj (typeName : Name) (idx : Nat) (struct : Expr)
  | lam (binderName : Name) (binderType : Expr) (body : Expr)
  | forallE (binderName : Name) (binderType : Expr) (body : Expr)
  | letE (declName : Name) (type : Expr) (value : Expr) (body : Expr)
```

Omitted in the listing but load-bearing in the real type: `mdata`, `mvar`, universe-level arguments on
`const`, `binderInfo`, and `letE`'s `nonDep` flag. The shipping eraser sees all of these
(`mdata` ignored, `mvar`/`bvar`/`sort`/`forallE` `unreachable!` [E:597–602]).

Facts about `Expr` the report states and the rework must respect:

* **Locally nameless** (McBride–McKinna): bound occurrences are de Bruijn indices, free occurrences are
  `fvar` identifiers; the binder API converts between them. λ□ is given the same treatment here
  (see 2.2).
* `Expr` "does not explicitly represent constructors, pattern matching nor recursion, but rather
  encodes them using the constructs presented above": constructors and `casesOn` are `.const`s;
  complex matching is compiled to **auxiliary matcher functions** which are themselves defined via
  `casesOn`.
* `Nat.casesOn : (P: Nat -> Type) -> (P 0) -> ((m: Nat) -> P (m+1)) -> n -> P n` — quoted in the
  report as the shape of the eliminators the eraser must recognize.
* **Two elaborations of recursion.** "during regular elaboration, term-level local recursion using the
  `let rec` syntax is lifted to recursion between top-level functions. Mutually dependent top-level
  definitions are grouped in mutual blocks … definitions are sent to the compiler in this form after
  type-checking without further processing. The terms sent to the kernel undergo an additional
  elaboration step in which recursion between top-level functions is eliminated and replaced with
  recursors". **The eraser consumes the first form, the kernel validates the second.**
  Footnote 11: "With one exception discussed below, we assume that recursors do not appear in terms
  prior to recursion elaboration."

### 2.2 Target language — λ□ as ported to Lean (Listing 2, [R §3.3])

Transcribed verbatim:

```lean
inductive LBTerm where
| const: Kername -> LBTerm                               | box: LBTerm
| app: LBTerm -> LBTerm -> LBTerm                        | prim: PrimVal -> LBTerm
| proj: ProjectionInfo -> LBTerm -> LBTerm               | bvar: Nat -> LBTerm
| lambda: BinderName -> LBTerm -> LBTerm                 | fvar: FVarId -> LBTerm
| letIn: BinderName -> LBTerm -> LBTerm -> LBTerm
| construct: InductiveId -> Nat -> List LBTerm -> LBTerm
| case: (InductiveId × Nat) -> LBTerm -> List (List BinderName × LBTerm) -> LBTerm
| fix: List (@FixDef LBTerm) -> Nat -> LBTerm

inductive GlobalDecl where
| inductiveDecl (body: MutualInductiveBody)              | constantDecl (body: ConstantBody)

abbrev Program: Type := (List (Kername × GlobalDecl)) × LBTerm
```

Caption, verbatim: "Abstract syntax for λ□ expressions and programs, **as ported to Lean for this
project**. The constructor `.fvar` is an implementation detail **not included in the original
definition in MetaRocq**."

Prose facts:

* A program = global environment (list of declarations: definitions or inductive declarations) + term.
* "Although λ□ is untyped, information regarding **how many constructors an inductive type has and how
  many arguments they each take** must be kept for the translation to Malfunction." (Hence `nargs`
  per constructor and `npars`; hence pruning must adjust them, see 2.5.)
* "Since λ□ represents terms after erasure, there are no constructors representing the sorts `Prop`
  and `Type` or the dependent function type. Instead, **all erased information is replaced by a special
  term `□`**." Footnote 8: "Propositional content **cannot be removed entirely** by erasure when
  targeting a strict language such as Malfunction." (This is the justification for `□` existing as a
  *value* rather than as a deletion — the whole reason the target semantics needs `□ x → □`.)
* `fix` "introduce[s] multiple local function definitions at once, each of them available within the
  bodies of the others, then select[s] one."
* Footnote 9, quoted because it bounds what any end-to-end theorem can say: "Details related to Rocq's
  dependent type system and OCaml's support for mutability **limit the correctness theorem for verified
  extraction to first-order interfaces**, through which extracted code can safely interact with
  arbitrary OCaml code."

### 2.3 The erasure procedure (`EraseM`, `visitExpr` family) [R §4.1]

**Monad and context.** "the erasure procedure must be able to read from Lean's global environment and
produce a λ□ global environment … These effects are supported using a dedicated monad, `EraseM` …
Additionally, `EraseM` manages a **local context, mapping the identifiers of variables to their type
and optional value (for let-bound variables). This allows the type of subterms featuring free variables
to be determined, which is used to determine whether they can be erased.**"

Shipping form: `abbrev EraseM := StateT ErasureState <| ReaderT ErasureContext CoreM` [E:139], with
`ErasureState := { inductives : HashMap Name (InductiveId × InductiveArgMasks), constants : HashMap
Name Kername, gdecls : GlobalDeclarations, inlinings : List Kername }` [E:28–33] and
`ErasureContext := { lctx, fixvars : Option (HashMap Name FVarId), lparams : List Name, config }`
[E:121–131].

**The core rule, transcribed** [R §4.1]:

> "the general process of converting an `Expr` to a λ□ term is straightforward: **terms whose type is
> either of the form `_ -> ... -> Type` (indicating that the term is a type former) or whose type is a
> proposition are directly converted to `.box`**, and non-erasable terms are destructured into
> component `Expr`s using the appropriate helper function. These are then recursively erased into
> `LBTerm`s and reassembled using the matching construction function."

Shipping form [E:590–592]: `if ← isErasable lparams e then return .box` **before** the syntactic
match; the oracle is `isProp (inferType e) ∨ isTypeFormerType (inferType e)` [E:151–160], now routed
through a lean4lean kernel check with a silent `Meta`-based fallback [E:177–182].

**Application traversal and η-expansion** [R §4.1], verbatim:

> "In order to handle partial applications of constructors or `casesOn`, which are allowed in Lean but
> not in λ□, it is necessary to know how many arguments a constant is applied to when processing it.
> This requires special traversal of binary function applications in the expression tree. For example,
> the expression `a b c`, represented as `.app (.app a b) c`, will be considered as `a` applied to the
> two arguments `b` and `c`, instead of recursing immediately to process `.app a b` and `c` separately.
> If `a` is a constructor taking three arguments, then it is underapplied in this example, which is
> resolved by adding additional arguments via **η-expansion**, e.g. handling the expression `a b c` as
> `fun d => a b c d`. Once all arguments are present, constructors and `casesOn` functions are
> translated using the `.construct` resp. `.cases` constructors of `LBTerm`, with some **additional care
> required for match arms, which are passed as functions in `Expr` and as open terms whose free
> variables are bound by the `.cases` syntax in λ□**."

Shipping form: `visitApp` dispatches on `e.getAppFn` being a `.const` [E:649–655]; `visitConstApp`
tests `getCasesInfo?` then `getCtorArity?` [E:672–692]; `visitCasesEtaGo` / `visitCtorEtaGo`
η-expand to arity by walking the *type* with `forallMonocular` [E:705–729]; `visitAlt` uses
`lambdaOrIntroToArity` to introduce exactly `numFields` binders (η-expanding an arm that is not a
literal lambda) and `mkAlt` abstracts them in **reverse order** [E:259–264, 842–845].

**Environment construction** [R §4.1], verbatim:

> "Whenever the erasure procedure encounters a term constructing or deconstructing a value of an
> inductive type **for the first time**, it adds the corresponding inductive type declaration to the λ□
> global environment managed by `EraseM`. Similarly, instances of `Expr`'s `.const` constructor which do
> not require any special treatment are normal references to top-level constant declarations. Upon
> encountering a constant name for the first time, the erasure procedure looks up its declaration in
> Lean's global environment, performs erasure on the definition body, then adds a declaration with the
> name and erased definition to the λ□ global environment. **Mutually recursive definitions present in
> `Expr` are handled by processing all declarations in a mutual block together, using `EraseM` to
> remember the names of the functions being defined, and creating independent λ□ declarations, each
> representing the auxiliary definitions at the term level using the `.fix` constructor of `LBTerm`.**
> Once a constant has been added to the λ□ global environment, it is referred to using the `LBTerm`
> constructor `.const`."

Shipping form: `get_constant_kername` → `visitMutual` [E:847–919]. Within a mutual block, each member
of `ci.all` becomes a fresh `FVarId` (`fixvars`), constants in the block erase to `.fvar` [E:660–664],
and **each** name gets its own top-level declaration `⟨.fix defs i⟩` sharing the same `defs` list
[E:904–918]. A single non-recursive declaration (detected by `name_occurs`) becomes a plain
`constantDecl` [E:885–892].

**Preprocessing** [R §4.1], verbatim:

> "Lean resolves this by marking `cond` and similar functions with the `@[macro_inline]` attribute,
> which indicates that their definition should be **unfolded at every call site before compilation**. We
> handle this as part of a **preprocessing pass run on expressions before erasure**. Besides
> `@[macro_inline]` functions, this pass also **inlines auxiliary matcher functions** produced by Lean's
> pattern matching elaboration and **appends the suffix `_unsafe_rec` to the names of recursive
> functions in order to access their original definitions, which use toplevel recursion, instead of the
> result of Lean's recursor elaboration.** Finally, the preprocessing step applies Lean lemmas tagged
> `@[csimp]`, which direct Lean's compiler to replace the logical definition of a function with an
> equivalent implementation. This is crucial for performance, as many common functions have
> tail-recursive implementations provided by csimp lemmas."

Shipping form `prepare_erasure` [E:556–576], in order: `replaceUnsafeRecNames`, `macroInline`,
`inlineMatchers`, `macroInline` (again, for `ite`/`dite` exposed by matcher inlining), then, if
`config.csimp`, a whole-tree `Compiler.CSimp.replaceConstant?` transform. Its docstring carries the
warning that no theorem in the current tree answers: **"This may make the expression ill-typed if some
dependent type relies on the implementation of functions affected by csimp."**

**The motivating counterexample** for inlining, transcribed [R §4.1]:

```lean
def cond (α : Type) (c : Bool) (x y : α) : α :=
  match c with
  | .true => x
  | .false => y
```

> "Using the `cond` function naïvely in programs can introduce nontermination because Lean is a strict
> language: evaluating the function call `cond .true a b` will always fully evaluate `a` and `b`."

**Entry point** [R §4.1]: the command `#erase <term> to <path>` elaborates the term, erases it,
serializes to the S-expression syntax expected by `lbox`, and writes the file. Example given:

```lean
import Erasure
def val_at_false (f: Bool -> Nat): Nat := f .false
#erase val_at_false to "out.ast"
```

### 2.4 Axioms, `@[extern]`, arithmetic [R §4.2]

* "`@[extern]` … directs the compiler to use a C definition to implement a given function. Function
  declarations tagged `@[extern]` **may optionally have a definition written in Lean, in which case the
  Lean definition is used by the type checker and the external C definition is used by the compiler**."
  Footnote 13, verbatim: **"This is a source of unsoundness if the external implementation of the
  function does not match the logical definition."**
* Rule implemented: "the erasure procedure **adds a declaration without a body, called an axiom, to the
  λ□ environment upon encountering a constant declaration which either has no associated value or is
  marked with the `@[extern]` attribute**." Shipping: `addAxiom` [E:184–187], driven by `visitMutual`'s
  `match ci.value?, isExtern, config.extern` [E:873–883]; `register_inductive` also axiomatizes
  `@[extern]` *constructors* [E:203–205].
* Axioms become references to an OCaml module `Axioms` in the Malfunction output; `axioms.ml` supplies
  Zarith implementations (`Nat`, `Int`), `Eq.rec`, and the `Array` API.
* **`Nat`/`Int` lowering**, verbatim: "Since Zarith represents small integers identically to OCaml's
  native 63-bit signed integers, which also underly the primitive integers available in λ□, **literals
  of type `Nat` found in an `Expr` can be transformed directly into a λ□ primitive integer provided they
  do not overflow this size bound. The constructors `.zero` and `.succ` are replaced by the literal `0`
  and the function `fun n => n + 1`, and the case analysis performed by `Nat.casesOn` is replaced by an
  expression of the form `if n == 0 then … else …(n-1)`, explicitly testing whether a number is zero and
  subtracting one to obtain the predecessor if not.**"
  Shipping form [E:605–615, 742–753, 768–815]: literal `n ≤ 2^63−1` → `.prim ⟨.primInt, n⟩`, else
  `panic!`; `Nat.zero`→`0`; `Nat.succ x` → `Nat.add x 1`; `Nat.casesOn` → `let n := discr in
  case Bool (Nat.beq n 0) [succ-arm[n − 1], zero-arm]`; `Int.casesOn` → `let n := discr in
  case Bool (Nat.ble 0 n) [negsucc-arm(Int.neg (Nat.succ n)), ofNat-arm n]`. The code's own comments
  admit two things no current theorem covers: the constructed term is **deliberately ill-typed**
  ("`visitExpr` assumes expressions are well-typed, which wouldn't be the case naïvely as `(n-1).succ`
  is not defeq to `n`") and Int/Nat are **silently cast** ("In effect, we can silently cast between Int
  and Nat").
* Footnote 15, verbatim: "**`Eq.rec` is used by Lean's match elaborator for type casts within match
  arms, and becomes the identity at runtime**."

### 2.5 Constructor pruning and unboxing [R §4.4]

* Lean's guarantee being imitated: "trivial wrappers are inductive types with exactly one constructor,
  which itself has **only one computationally relevant argument and any number of irrelevant
  arguments**" (example `Fin n` = `val : Nat` + `isLT : val < n`).
* Split into two steps, verbatim: "In **constructor pruning**, which is done as part of the erasure from
  `Expr` to λ□, **all computationally irrelevant arguments of constructors are removed. This affects the
  inductive type declarations added to the λ□ global environment, every application of a constructor,
  and every match arm.** Pruning must be done as part of erasure and cannot be performed later in the
  pipeline, as a λ□ program no longer retains information about the types of constructor arguments,
  which is necessary in order to remove irrelevant arguments. Next, **unboxing** consists in recognizing
  inductive types with a single one-argument constructor and removing occurrences of the constructor
  and case analysis. This is done in λ□ … we chose to simply **patch the lbox tool** in order to set a
  flag enabling unboxing in MetaRocq's translation of λ□ to Malfunction."
* Consequence recorded: the OCaml realizations in `axioms.ml` must change shape with pruning
  (`Decidable P` loses its propositional field and becomes `Bool`-like), i.e. **the axiom model is
  configuration-dependent**.
* Shipping form: `ConstructorArgMask := Array (erase|keep)` per constructor, computed by
  `Meta.forallBoundedTelescope` + `isErasable` over the *fields only* (params excluded) [E:208–221];
  `nargs` in the emitted λ□ constructor = count of `keep` [E:222]; applications filter the field slice
  and keep params and extra args [E:755–758]; alternatives filter their binder list [E:842–845];
  **projections are re-indexed** by counting kept fields below `i` [E:634–640] and are generated only
  when the inductive is a single, non-recursive, single-constructor block [E:226–236].
  Off by default in the shipping config (`remove_irrel_constr_args := false` [E:70]).

### 2.6 Configuration space (shipping; the report describes it as the benchmark matrix [R §5.2])

| Knob | Values | Report's reference setting |
|---|---|---|
| `extern` | `preferLogical` / `preferAxiom` | `preferAxiom` (arithmetic via Zarith) |
| `nat` | `peano` / `machine` | `machine` |
| `csimp` | on/off | on |
| `remove_irrel_constr_args` (pruning) | on/off | on (+ unboxing in `lbox`) |
| `Array` realization | Baker's trick / Sek / unsafe Dynarray | Baker's trick |
| OCaml opt | noflambda / -O0 / -O2 / -O3 | Flambda `-O2` |
| axiom inlining | on/off | on |

Shipping defaults differ from the report's reference configuration: `remove_irrel_constr_args := false`
and an extra post-erasure `auto_inline_typeclass_dispatch := false` knob [E:64–85] that did not exist
at report time (it emits a `.inlinings` attributes file consumed by peregrine).

### 2.7 Benchmark programs (the coverage target) [R §5.3, App. B]

10 programs / 19 variants: `even`, `iflazy`, `list_sum_{foldl,foldr,rev}`,
`triangle_{acc,foldl,rec}`, `binarytrees`, `const_fold`, `deriv`,
`rbmap_{std,mono,raw,beans}`, `qsort`, `qsort_fin`, `qsort_single`, `unionfind`.
All are `Nat → Nat`; I/O is in an OCaml/Lean wrapper; adaptations from *Counting Immutable Beans*
removed I/O, replaced fixed-width ints by `Nat`, and replaced `Task` by synchronous code.
`rbmap_std` carries a bundled well-formedness proof; `qsort_fin` exercises `Fin`; `unionfind`
exercises monads and arrays.

---

## 3. Theorems and proof structure

**There are none.** The document proves nothing and states no lemma. For the rework this is the single
most important fact about it: the object's specification has to come from elsewhere (Letouzey 2004;
Sozeau et al., J. ACM 2025 §7.3–7.4; MetaRocq's `erases`, `erases_global`, `erases_correct`,
`erase`/`erases_erase`, `optimize`), and this report supplies only the *object* plus a set of informal
justifications.

The informal correctness arguments actually made, and what each one owes a formal proof:

| # | Claim in the report (verbatim or close) | Where | What must replace it |
|---|---|---|---|
| C1 | "**Since the type system forbids any computational value from depending on the value of a proof, all logical content can be removed from a program and replaced with uninformative dummy values**, which is known as proof erasure." | §3.1 | The box-soundness case of a forward simulation: erasing a proof/type-former to `□` preserves observable behaviour. In MetaRocq this is `Is_Type_or_Proof`/`isErasable` + the `eval_box` case of `erases_correct`. Note Lean-specific strengthening: **Lean's `Prop` is definitionally proof-irrelevant** (footnote 4 says so explicitly, contrasting Rocq's `Prop`), which should make this *easier* here than in MetaRocq. |
| C2 | "the transformation from `Expr` into λ□ … **corresponds to the type and proof erasure step in Rocq's verified extraction pipeline**"; "**adapting the erasure algorithm introduced by Letouzey (2004) to Lean expressions**" | §4.1, Contribution | A rule-by-rule correspondence between the rework's erasure relation and MetaRocq's `erases` (Fig. 18 of Sozeau et al.), with every deviation named. This is exactly the anchor the current `Erases` lacks. |
| C3 | Inlining `@[macro_inline]`/matchers is needed "**because otherwise both arms of the conditional will be strictly evaluated**" [E:564] and "can introduce nontermination". | §4.1 | A statement of what the source semantics is. Under Lean's *kernel* conversion this rewriting is δ+β and hence sound; the *reason* it is needed is that the target is CBV. A correct theorem must therefore relate a **non-CBV source** (Lean defeq / weak-head evaluation) to a **CBV target**, or restrict to terminating programs. Either way the preprocessing pass is inside the verified subject, not before it. |
| C4 | csimp replacement is by a lemma "which direct[s] Lean's compiler to replace the logical definition of a function with an **equivalent** implementation" | §4.1 | Only *propositional* equality (`@[csimp] theorem f_eq : f = f'`) is available, and the code warns the result may be **ill-typed**. A defeq-based simulation cannot justify this. Either exclude (`cfg.csimp = false`) or prove a separate observational-equivalence step parameterised by the csimp lemma set. |
| C5 | `@[extern]` axioms are sound if the OCaml realization matches the logical definition (footnote 13 concedes it is "a source of unsoundness" otherwise). | §4.2 | An explicit **axiom-interpretation hypothesis**: for each emitted axiom `a` with logical body `b`, the realizer denotes `⟦b⟧`. Combined with footnote 9's **first-order interface** restriction this is exactly the shape of hypothesis the capstones need — and it must be stated once, not per-benchmark. |
| C6 | `Eq.rec` "becomes the identity at runtime" (footnote 15). | §4.2 | A lemma: on well-typed Lean terms, `Eq.rec` applied to a proof is observationally the identity on its major argument. In an erasure setting this follows from erasing the proof to `□` and the ι-rule for `Eq`, but only if `Eq.rec` is *not* axiomatized away; as shipped it *is* axiomatized, so it falls under C5. |
| C7 | Machine `Nat`/`Int`: literals ↔ i63 primitives, `succ` ↔ `+1`, `casesOn` ↔ zero-test/predecessor. | §4.2 | A **data refinement**, not an erasure rule: a relation between unary `Nat` values and integer primitives, preserved by each rewritten operation, plus the overflow side condition (`n ≤ 2^63 − 1` at literal sites) and the Int/Nat cast. Cannot be expressed by a syntactic `Erases`-style relation alone. |
| C8 | Pruning is sound because the removed fields are computationally irrelevant. | §4.4 | The masked-erasure invariant: masks agree with `isErasable` on fields; every construction, every alternative binder list, every projection index, and the declared `nargs` are re-indexed consistently; and no kept field's value depends on a pruned one. |
| C9 | Unboxing is sound (delegated to MetaRocq's λ□→Malfunction flag). | §4.4 | Out of scope for the frontend theorem, but the composition claim ("the rest is verified") is only true if the flag's obligations are met by the *emitted* environment (single-constructor, single-field, correct `nargs`). |
| C10 | "the fact that the type checker accepts the implementation guarantees that it conforms to the provided specification"; kernel/elaborator separation reduces the trusted base. | §2, §3.1 | Well-typedness is the **hypothesis** of any erasure theorem. But see the grounding hazard in §4.1 below: the eraser's input is not the term the kernel checked. |

**Proof structure implied (not carried out).** The report's own decomposition suggests the only
defensible pipeline shape:

```
Expr (kernel-checked declaration)
  ──(K) recursion-elaboration mismatch: compiler body vs recursor body ──▶ Expr'
  ──(P) prepare_erasure: δ(macro_inline) + matcher inlining + _unsafe_rec + csimp ──▶ Expr''
  ──(E) erasure proper: box / structural / ctor-casesOn-fix reconstruction, η, masks ──▶ λ□ term + env
  ──(N) Nat/Int lowering + axiom emission (configuration-dependent) ──▶ λ□ term + env + axioms
  ──(S) serialization to .ast ──▶ file
  ──(verified downstream) λ□ → Malfunction → OCaml
```

Steps K, P, N and S are all inside the shipping `#erase` and all are *outside* what the report's
"corresponds to MetaRocq erasure" claim covers. Only E is Letouzey-shaped.

---

## 4. Lean-specific adaptations

Points where Lean forces a departure from the Rocq/MetaRocq story, as this document states them.

### 4.1 The eraser's input is not the kernel's term (the grounding hazard)

The report is explicit [R §3.2, §4.1, footnote 11]: definitions reach the compiler in
**top-level-recursive** form; the kernel sees the **recursor-elaborated** form; the eraser takes the
compiler form and even rewrites names to `_unsafe_rec` variants to *get* it. Consequences for a proof
grounded in lean4lean (whose subject is the kernel's `VExpr`/`TrExprS`/`HasType`):

* The body being erased may not be a kernel declaration at all (`_unsafe_rec` definitions are added
  with `unsafe` safety and are not checked by the kernel).
* Structural recursion is therefore **not** modelled by recursors in the erased subject; it is a
  top-level self/mutual reference translated to λ□ `fix`. The Lean side has *no* fixpoint construct, so
  the source relation for a `fix`-producing rule is a *declaration-level* recursion, not a term
  former — a genuine asymmetry with MetaRocq, where `tFix` erases to `tFix`.
* Any well-typedness hypothesis must be about a term the kernel accepted; if the erased body is the
  compiler body, the hypothesis has to be *transported* across the equation-compiler's output
  (the compiler body and the recursor body are propositionally equal by the equation lemmas, not
  definitionally).
* Footnote 11's "we assume that recursors do not appear in terms prior to recursion elaboration" is an
  **unchecked assumption of the implementation** and must become an explicit, checkable side condition
  (`Supported`-style) or a proved fact — with the acknowledged exception `Eq.rec`.

### 4.2 `casesOn`, matchers, recursors

* Lean has no primitive `match` in `Expr`: `match` → auxiliary matcher constants → `casesOn`.
  The eraser inlines matchers (so the fragment must be closed under matcher unfolding) and treats
  `casesOn` as λ□ `case`. **Recursors other than `casesOn` are unsupported** (`Nat.rec`, `brecOn`,
  `Eq.rec` beyond the axiom, `False.rec`, `Acc.rec` for well-founded definitions).
  Well-founded recursion in particular is not discussed by the report at all; the `_unsafe_rec` trick
  is what avoids it.
* λ□ `case` binds fields in the alternative; Lean passes minor premises as functions. The conversion is
  an **η-expansion of the minors to their field arity** ([E:842–845]) and is silently *not* the identity
  when a minor is η-contracted (`Option.casesOn o none Some`).
* `casesOn` may be **over-applied** (the motive returns a function); the extra arguments are applied to
  the whole `case` node [E:832–834]. Under CBV this reorders evaluation relative to the source.
* `casesOn` may be **under-applied**: η-expansion to arity via the *type* [E:705–712], i.e. the eraser
  reads types to build terms — the correctness argument therefore depends on `inferType`.

### 4.3 Constructors: applied form, not blocks

The shipping eraser emits `.construct iid k []` **applied through `.app`** [E:759–760] ("Instead of
making this a 'real' use of `.construct`, in the stage of λbox I am targeting constructor application
is function application"), while `agda2lambox` and CertiRocq expect fully-applied blocks. The report's
η-expansion discussion covers arity but not this representation choice. A correctness theorem must fix
which λ□ dialect (applied vs block) its semantics is about, and the composition with peregrine's
block-conversion pass must be stated.

### 4.4 Proof irrelevance and universes

Footnote 4, verbatim: "The need to evaluate propositions depends on the specifics of a proof
assistant's underlying type theory. **In Lean, all propositions are proof-irrelevant**; Rocq's universe
`SProp` is proof-irrelevant, but the more commonly used `Prop` is not." This is a *simplification* for
the Lean erasure proof (any two proofs of the same Prop are convertible, so `□`-collapse is easier),
and it should be used, not ignored. Conversely, Lean's `Prop` supports **large elimination only for
subsingleton-eliminating inductives** — MetaRocq's `erases` has a dedicated rule for singleton
elimination on propositional inductives; excluding propositional inductives by a `nonProp` side
condition (as the current tree does) is a *fragment restriction*, and the report gives no ground for it.

### 4.5 Literals and primitives

`Expr.lit` covers `natVal` and `strVal`. The shipping eraser **panics on string literals** [E:614] and
on `Nat` literals ≥ 2^63 in `machine` mode [E:613]. In `peano` mode a literal `n+1` is expanded to
`Nat.succ (lit n)` [E:607–608], i.e. literal handling is *recursive* and unary — Θ(n) work at erasure
time. λ□'s `prim` carries `PrimVal`; the mapping `Nat literal ↦ i63 prim` is the only primitive used.

### 4.6 `let`

`letE` erases to `letIn` unconditionally; the report's code comments record the deliberate omission of
LCNF's optimization of dropping erasable let-bindings [E:626–630]. λ□'s `letIn` is a ζ-redex under
CBV; the source's `let` is a definitional δ/ζ. `letE`'s `nonDep` flag is ignored [E:291].

### 4.7 `mdata`, `fvar`, and the locally nameless port

`mdata` is transparently skipped [E:597]. λ□ was **extended with `fvar`** for this project (Listing 2
caption) so both languages can be locally nameless; abstraction happens at `mkLambda`/`mkLetIn`/`mkAlt`/
`mkDef`. Two code comments flag unresolved binder-order concerns: `mkAlt` — "The order of variables
here is what it is because the other way around led to segfaults" [E:258]; `mkDef` — "Check binding
order here as well, may be wrong" [E:272]. **A correctness theorem must pin the binder order and it is
the kind of bug the report's own author suspected.**

### 4.8 Unsupported by design [R §6.2]

`IO` and all side effects; `Task`/async; fixed-width integer types (`UInt8`…`UInt64`); `String`;
`@[implemented_by]` and computed fields (explicitly dropped, [E:676–679]); Lean's `@[inline]`/`@[always_inline]`
(λ□ has no inlining concept — the acknowledged cause of the 10× `unionfind` regression); structure
projection functions are left to Malfunction rather than β-reduced [E:683–689].

---

## 5. Requirements for the rework

Requirements are stated so that "the rework follows this document" is checkable. R-numbers are cited
from the structured return.

**R1 — Name the subject precisely.** The theorem's subject must be `Erasure.erase e cfg` (or
`eraseElab`'s verified core) as the report defines it: elaborated `Expr` in, `Program × List Kername`
out — *including* `prepare_erasure`. A theorem about a de-partialized model, or about a `visitExpr`
whose preprocessing is assumed away, does not verify the object this document describes.

**R2 — State the configuration.** Every theorem must carry the configuration it holds for, with
`extern`, `nat`, `csimp`, `remove_irrel_constr_args`, `auto_inline_typeclass_dispatch` all fixed.
Recommended layering: (a) *core* configuration `⟨preferLogical, peano, csimp := false, prune := false,
autoinline := false⟩` — the fragment where a Letouzey-style theorem is meaningful and unconditional;
(b) *pruning* layer; (c) *axiom* layer (`preferAxiom`) under an explicit realizer hypothesis;
(d) *machine-arith* layer under a data-refinement relation. The report's own reference configuration is
(d) + (b) + csimp — i.e. the fastest configuration is the least verifiable; say so.

**R3 — Anchor the erasure relation externally.** The specification relation must be presented as a
port of MetaRocq's `erases` (Sozeau et al. Fig. 18), rule for rule, with a tracked table in the repo
and every deviation named and justified: the Lean-side `ctor`/`cases`/`fix` rules (no MetaRocq
analogue in that shape), `proj`, `lit`, and the treatment of propositional inductives / singleton
elimination. It must **not** be indexed by the eraser's own registry without a well-formedness
predicate relating that registry to the Lean environment.

**R4 — Cover the box rule with Lean's proof irrelevance.** `Erasable e ↔ isProp (typeof e) ∨
isTypeFormer (typeof e)` must be the *definition*, matched to `isErasable`'s two disjuncts [E:151–160],
and the box-soundness case must exploit Lean's definitional proof irrelevance rather than reproving
MetaRocq's harder `Prop`-relevant argument.

**R5 — Put preprocessing inside the theorem.** `replaceUnsafeRecNames`, `macroInline`,
`inlineMatchers`, and (if enabled) csimp must each have a stated semantic effect:
δ-unfolding of a marked constant, unfolding of a matcher to its `casesOn` body, substitution of one
declaration body by another. The `_unsafe_rec` swap is the deepest of these: it changes *which
declaration* is erased and must be related to the kernel-checked declaration (equation lemmas), or the
theorem must be stated about the compiler-facing declaration with that stated as a hypothesis.

**R6 — Treat csimp as an observational, not definitional, step.** Default posture: `cfg.csimp = false`
in the core theorem, with a separately-stated extension whose hypothesis is "for every applied csimp
lemma `f = f'`, `f` and `f'` are observationally equivalent at the erased type", and an explicit
acknowledgement of the ill-typedness warning in [E:554].

**R7 — Model axioms once, as an interface.** One `AxiomModel` parameter: a map from emitted kernames
without bodies to λ□-observable behaviours, plus the hypothesis that each realizer agrees with the
logical body (where one exists). Every `@[extern]` decision [E:873–883] and every axiomatized
constructor [E:203–205] must be an instance of that model. Footnote 9's first-order restriction is the
right shape for the agreement statement; footnote 13 is the honest statement of what is being assumed.

**R8 — Machine `Nat`/`Int` is a refinement, not an erasure.** If it is in scope, it needs its own
relation (unary value ↔ i63/Zarith integer), preserved by `zero`, `succ`, `casesOn`-lowering,
`Nat.beq`, `Nat.sub`, `Nat.ble`, `Int.neg`; the literal overflow bound must appear as a side condition;
and the Int/Nat cast [E:794–801] must be justified or excluded. If it is out of scope, the theorem must
say `cfg.nat = .peano` and the shipping default (`.machine`) must be flagged as unverified.

**R9 — η-expansion, over-application and match arms must be rules, not hypotheses.** The three shape
transformations the report highlights — under-applied ctor/`casesOn` η-expansion to arity, over-applied
`casesOn` extra arguments applied outside the `case`, and minors-as-functions → alternatives-as-open-
terms — must each be a case of the erasure relation with its own simulation argument (η under CBV is
not free: `fun d => a b c d` is a value where `a b c` may not be; applying extra args after a `case`
reorders evaluation).

**R10 — Fix the λ□ dialect and the constructor form.** Declare whether the target semantics is over
applied constructors (what the eraser emits) or blocks (what CertiRocq/peregrine expect), and state the
composition with the block-conversion pass. Keep the `fvar` extension — and its abstraction functions —
inside the formal syntax, since the shipping eraser depends on it.

**R11 — Environment erasure must be a theorem about the *whole* program.** Mutual blocks → one shared
`defs` list replicated under each name [E:904–918]; first-encounter registration; `register_inductive`'s
`npars`, per-constructor `nargs`, and projection list [E:192–243]. The λ□ environment must be shown
well-formed (MetaRocq's `wf_glob`) and δ-consistent with the Lean environment — MetaRocq's
`erases_global` / `erases_deps` is the model.

**R12 — Pruning as a masked erasure.** If in scope: masks come from `isErasable` on fields only;
constructor `nargs`, applications, alternatives, and **projection indices** [E:634–640] are re-indexed
by the same mask; the `axioms.ml` shape-dependence [R §4.4] must be recorded as part of the axiom
model. If out of scope, state `cfg.remove_irrel_constr_args = false`.

**R13 — Panics are part of the specification.** The report's design has 16 `panic!`/`unreachable!`
sites; `unreachable!` at `sort`/`forallE`/`mvar`/`bvar` [E:602] is a *claim* that these are always
erasable or impossible, and string literals / oversized `Nat` literals / non-inductive lookups are real
partiality. A `.ok` result must be shown to exclude a panicked run, or the theorem must say explicitly
that it does not.

**R14 — Close the chain to the deliverable.** The report's artifact is a **file**: S-expression
serialization, the `.inlinings` attributes file, and the `.mli`. A theorem about `erase` alone does not
verify `#erase`. Either include the (verified-elsewhere) serializer in the chain, or state the boundary.

**R15 — Non-vacuity against the report's own benchmarks.** The document's claim is that "nontrivial pure
programs written in idiomatic Lean" — union-find, `Array.qsort`, red-black trees — go through. The
rework's hypotheses must be *inhabited* on at least the simple end of that list (`even`, `iflazy`,
`triangle_acc`, `list_sum_foldl`) and the coverage gap must be reported honestly for the rest. A
capstone whose hypotheses no benchmark program satisfies does not verify this object.

**R16 — Restrict honestly rather than premise-away.** Every exclusion (no `IO`, no `Task`, no
fixed-width ints, no strings, no well-founded recursion / `Acc.rec`, no recursors beyond `casesOn`
and axiomatized `Eq.rec`, no `@[implemented_by]`, no inlining directives) should be a *syntactic,
decidable* fragment predicate over the input `Expr` and its dependency closure — checkable on a real
program — not a `Prop` hypothesis about the eraser's internal state.

---

## 6. Open questions

1. **Which Lean term is the theorem's subject?** The kernel-checked declaration or the compiler-facing
   `_unsafe_rec` body? The report chooses the latter for the implementation and says nothing about the
   relation between them. Any lean4lean-grounded proof must answer this first; it may require the
   equation lemmas, or a hypothesis that the compiler body is kernel-typeable.
2. **What is the source semantics?** The report never defines one. Lean's kernel gives conversion
   (defeq), not an evaluation order; the target is CBV. MetaRocq's `simple_erases_correct` is stated
   over PCUIC's weak call-by-value `⇓`. Does the rework state its theorem over a Lean-side CBV
   evaluator (which then must be justified against defeq), or over defeq/whnf directly?
3. **Is `prepare_erasure` semantics-preserving on the fragment?** `macroInline` and `inlineMatchers`
   are δ; csimp is not. Is there a fragment on which the composite is provably defeq-preserving?
4. **How much does proof irrelevance actually buy?** Lean's definitional proof irrelevance should
   simplify the box case relative to MetaRocq. Has anyone checked that lean4lean's `IsDefEq` exposes
   it in a usable form?
5. **Propositional inductives / singleton elimination.** MetaRocq's `erases` has a rule; the current
   tree excludes them with a `nonProp` conjunct and the report is silent. Is the exclusion necessary,
   or an artifact? (`Decidable`, `And`, `Iff`, `Exists`-eliminations show up in real Lean code, and
   `Decidable` is central to `if`.)
6. **Well-founded recursion.** `_unsafe_rec` sidesteps `WellFounded.fix`/`Acc.rec`, but what happens
   when a definition has *only* a well-founded compiled body? The report does not say; this is a
   coverage question for the benchmark suite (`qsort` uses `Array.qsort`, whose termination is
   non-structural).
7. **Over-application and evaluation order.** Applying `casesOn`'s extra arguments outside the `case`
   node changes when they are evaluated under CBV. Is that observable in the presence of `panic`/
   nontermination, or is it neutral on the fragment?
8. **Axiom realizers.** Is there any intention to verify `axioms.ml` (Zarith arithmetic, Baker's-trick
   arrays, `Eq.rec = id`), or is it a permanent trust boundary? Footnote 13 says the mismatch is
   "a source of unsoundness"; footnote 9's first-order restriction says how far a theorem can reach.
9. **Configuration ↔ axiom shape.** `axioms.ml` must change when pruning is toggled [R §4.4]. Does the
   axiom model become configuration-indexed, and is that consistent across the three `Array`
   implementations?
10. **Dialect.** Applied constructors vs. blocks: which λ□ semantics is canonical for the rework, and
    where does the conversion get proved?
11. **Serialization.** Is the `.ast` writer inside the chain (peregrine has soundness/completeness
    proofs for the *parser*, in Rocq) or an acknowledged gap?
12. **`auto_inline_typeclass_dispatch`.** Post-dates the report; it emits a *directive* to peregrine
    (`.inlinings`) that changes the downstream program. Is it in scope, and if so what is the
    obligation — that inlining a `trivial alias`/instance is observationally neutral?

---

### Appendix: quantitative claims (for citation, not for verification)

* Geometric-mean slowdown vs. the Lean compiler, reference configuration: **2.5×** (`lean` column
  0.40 relative to reference = 1.00, Table 1).
* Flambda matters most: `-O0` 3.73×, no-Flambda 1.71× vs `-O2`; `-O3` ≈ `-O2` (0.98).
  `triangle_rec` at `-O0` is 629× — deep stack + per-call allocation.
* Pruning + unboxing: modest, biggest on `iflazy` (1.74× without both), `qsort_fin` (1.25×).
* Arrays: unsafe Dynarray ≈ 0.30–0.50× of Baker's trick on qsort; Sek 4.6–6.4× slower.
* Worst case `unionfind`: 79 ms (Lean) vs 926 ms (reference) ≈ 12×, attributed to the absence of
  inlining annotations in λ□/Malfunction.
* Machine: Intel i5-7200U, 16 GB, isolated core, hyperfine; OCaml 5.3.0; Lean 4.22.0.
