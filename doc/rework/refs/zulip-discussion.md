# Reference note: the Zulip thread *Peregrine Project > lean frontend*, and `references/inlining_diagnosis.md`

**Sources.**

* `references/lean_frontend_discussion.html` → plain-text extract at
  `…/scratchpad/refs/lean_frontend_discussion.txt` (23,706 chars). Zulip channel
  *Peregrine Project*, topic *lean frontend*, 2026-01-31 … 2026-02-19.
  Participants: **Bas Spitters**, **Yannick Forster**, **Simon Dima** (author of the
  Lean frontend; MSc thesis), **Eske Nielsen** (peregrine-tool middle-end/backends),
  **Matthieu Sozeau**. The channel's other subscribers (incl. the owner of this repo,
  Alessandro Sosso, and Lucas Escot, Orestis Melkonian, Karl Palmskog) do not post in
  the topic.
* `references/inlining_diagnosis.md` (2026-05-26, 2.6 KB) — this repo's written answer
  to one bug raised in that thread.
* Cross-checked against `peregrine-tool/doc/format.md` (the canonical on-disk format)
  for the objects the thread names only informally.

**Status of this source.** It is the only *collaborator-facing* document in the
reference set: no mathematics, no theorem, no erasure rule. Its value for the rework is
that it is the record of **what the consumers of this frontend actually ask of it** —
an interface contract, a bug list, and a (near-total) silence about verification that is
itself a finding. Everything below is either quoted from the thread or marked as
inference.

---

## Summary

Between 31 Jan and 19 Feb 2026 the Peregrine collaborators put the Lean frontend
through its first real integration with `peregrine-tool` (benchmarks for a paper
deadline, Fri 13:00 CET). Four things came out of it.

1. **Interface conformance.** The frontend's `.ast` was *not* accepted by the
   middle-end as it stood. Yannick Forster, 10 Feb: *"The problem here is that the lean
   frontend does not do constructors as blocks"*, and *"parameters are still
   present"*. The resolution was **not** to change the frontend: Eske Nielsen answered
   that peregrine already owns the pass and that it is **mandatory**, precisely for a
   *proof-architecture* reason — *"the correctness proofs of all the earlier passes
   assume no constructor as blocks, and later passes assume constructor as blocks."*
   So applied-form constructors are the **required** input form of the verified
   middle-end, not a defect of the Lean frontend. (Eske's PR
   `peregrine-project/lean-to-lambdabox#1` plus tests in Peregrine CI made the frontend
   produce "valid ast files".)
2. **The inlinings side-channel.** Yannick's opening question for the whole thread was
   whether the frontend *"deals correctly with inlining"*; the answer on 3 Feb was no.
   The fix agreed on is a **second output file** next to the `.ast`: a list of kernames
   the frontend asks the middle-end to inline, consumed as
   `peregrine compile prog.ast cfg --attributes=prog.ast.inlinings`. Yannick pushed the
   two commits that print the inlining list (stdout, then file); Eske confirmed *"It
   should be enough"*. A hard requirement fell out on 17 Feb: **the file must always be
   written, even when empty** (peregrine errors out on a missing `--attributes`
   target). Eske: *"the frontend should always create the file even if there are no
   inlinings."*
3. **Axioms/externs and target reach.** Bas Spitters asked whether Lean *"can only
   target malfunction"*, because the AST *"uses external Zarith axioms"*. Simon Dima:
   the AST *"uses lambdabox axioms for Lean axioms and extern functions, so one would
   have to link the generated program with an implementation of those axioms"* — i.e.
   the frontend's output is **open**, and its meaning is parametric in an assumed
   implementation of every `@[extern]`/axiom constant. Lean's IO primitives are simply
   unsupported (so the peregrine-tool PR#43 Lean benchmarks were rejected by the
   frontend).
4. **AST quality is a first-class deliverable, not just correctness.** Eske, 19 Feb:
   Lean's ASTs are *"2-4x the size of Rocq and Agda asts"*, because of stdlib
   typeclasses; *"just compiling the constant 5 results in 5 definitions and the
   constant appear[s] twice in the AST"*; *"It is a bit absurd that we need 5 functions
   and 2 inductive types just to add two natural numbers"*; and *"This probably also
   explains why Lean is generally a bit slower than the other frontends."* Simon's
   diagnosis: Lean's own compiler **specializes** typeclass instances, which inlining
   only approximates; the real fix is specialization of `A → [inst] → B` to `A → B` per
   instance. Empirically, inlining the typeclass wrappers for `add/sub/mul/pow` plus
   `betared` plus `unbox` erased BinaryTrees' 10% Lean-vs-Agda/Rocq overhead.

**On verification: the thread contains no verification expectation at all.** Nobody
asks whether the Lean frontend is verified, what it would mean, or how it would compose
with the verified middle-end. The single verification-relevant sentence in 24k chars is
Eske's pass-ordering statement in (1) — and that is about *peregrine's* proofs, not this
repo's. The rework should read this as: **the collaborators' operative notion of a good
frontend is "the bytes it writes satisfy the middle-end's input contract and the
programs run fast"**. Any correctness theorem this repo produces has to be phrased so it
speaks to that contract, or it will be invisible to the people on the other side of the
pipe.

---

## Formal objects

None of these is defined mathematically in the source; they are named there and defined
in `peregrine-tool/doc/format.md`. Transcriptions below are byte-faithful where the
source gives bytes.

### O1. The `.ast` file — the actual contract

`peregrine-tool/doc/format.md`: *"The peregrine middle end takes two input files: 1. a
λ□ program formatted as S-expressions, and 2. a pipeline configuration formatted as
S-expressions."* Top-level:

```
(Untyped (...env...) (Some (...term...)))
(Typed   (...env...) None)
```

from `PAst`:

```coq
Inductive PAst :=
| Untyped : untyped_env -> option EAst.term -> PAst
| Typed   : typed_env   -> option EAst.term -> PAst.
```

The Lean frontend emits the `Untyped` variant. This file — not `LBTerm`, not the
in-memory `Program` — is what the collaborators consume.

### O2. Constructor form: applied vs block

Grammar (format.md:115): `(tConstruct <inductive> <nat> (<term> ...))`. The trailing
list is the **block** payload. The thread's facts:

* Yannick (10 Feb): *"the lean frontend does not do constructors as blocks"*; *"and
  parameters are still present"*.
* Eske (10 Feb): *"We already have the passes in Peregrine. The constructor as blocks
  pass is not optional."* … *"Yes the pass is performed in Peregrine."* …
  *"whenever one calls peregrine the pass is run"* (confirming Yannick's paraphrase).
* Eske's reason, verbatim: *"The constructor as block pass is currently mandatory
  because the correctness proofs of all the earlier passes assume no constructor as
  blocks, and later passes assume constructor as blocks."*

Reading: the middle-end's pipeline has a **representation invariant with a phase
boundary**. Input to peregrine must be **applied form** — `tConstruct i k ()` under
`tApp` spine, arguments (including inductive **parameters**) supplied by application.
Contrast agda2lambox, which eta-expands to fully applied blocks (CLAUDE.md). The Lean
frontend's "wrong" behaviour is in fact the required one; what is *not* settled in the
thread is whether leaving **parameters** in the spine is also fine (Yannick raised it as
a second complaint, and it was never answered).

### O3. `attributes_config` — the `.ast.inlinings` file

format.md: the payload accepted via `--attributes` is the 5-element mergeable subset of
`config`:

```
(attributes_config
  <inlinings>
  <constant_remappings>
  <inductive_remappings>
  <inductives_mapping>
  <custom_attributes>)
```

with `inlinings` *"a list of `kername`s; constants in this list are inlined by the
typed-erasure pass"*, merged onto the main config by `merge_attributes_config`. The
Lean frontend writes only the `inlinings` field. Observed CLI (Yannick, 17 Feb,
verbatim modulo the extract's spacing):

```
peregrine compile build/58084347/even.ast unbox.config --attributes=build/58084347/even.ast.inlinings
```

and the failure when the file is absent:

```
peregrine: option '--attributes': invalid element in list ('build/58084347/even.ast.inlinings'):
no 'build/58084347/even.ast.inlinings' file or directory
```

### O4. kername encoding, as emitted by this frontend

From `references/inlining_diagnosis.md`, the byte-exact strings at the three places a
kername can appear:

| Location | String |
|---|---|
| Call site (`tConst`) | `(tConst ((MPfile ()) "instDecidableEqNat"))` |
| Declaration header | `(((MPfile ()) "instDecidableEqNat") (ConstantDecl ...))` |
| Inlinings entry | `((MPfile ()) "instDecidableEqNat")` |

and a full declaration:

```
(((MPfile ()) "instDecidableEqNat")
 (ConstantDecl
  (constant_body
   (Some (tConst ((MPdot (MPfile ()) "Nat") "decEq"))))))
```

Two facts worth carrying into the rework: the frontend emits an **empty module path**
`(MPfile ())` with the Lean name flattened into the ident (namespaced names become
`(MPdot (MPfile ()) "Nat") "decEq"`), and a `cleanIdent` rewrite exists for non-ASCII
identifiers (not exercised here). Kername identity across the three sites is what makes
the inlinings channel work at all, and the diagnosis establishes it holds **by string
equality**.

### O5. λ□ axioms for Lean axioms and `@[extern]`

Simon (3 Feb): *"The generated AST uses lambdabox axioms for Lean axioms and extern
functions, so one would have to link the generated program with an implementation of
those axioms."* Concretely a `ConstantDecl` with `constant_body = None` (the diagnosis
notes `Nat.decEq` *"is itself an `@[extern]` axiom declaration, with no body, so the
rest of the chain stops there"*). Bas: the Zarith-backed ones *"will not work for the
Peregrine C backend"*; Simon: Zarith is *"a thin wrapper around GMP, so it should be
relatively easy to write a C implementation of the needed arithmetic functions."*

### O6. The optional pipeline passes the benchmarks toggle

Named in the thread: **inlining** (Eske: *"Inlining is done at the lambdabox level at
the end of the pipeline, before the backend is called"*), **betared** (*"its trivial to
perform. It's just a matter of enabling it in the config file"*), **unbox**
(`unbox.config`). format.md's `erasure_phases` record:

```
(erasure_phases <implement_box> <implement_lazy> <cofix_to_laxy> <betared> <unboxing> <dearg_ctors> <dearg_consts>)
```

each `Required` / `Incompatible` / `(Compatible <default>)` per backend. Eske also
notes inlining does **not** delete the inlined definition (*"Inlined definitions are
also not removed"*), leaving dead code for the backend compiler.

### O7. Typed λ□ᵀ and inlining

Eske (3 Feb) on where inlining annotations can be honoured: *"We have that in the
`ast-format` branch, it only works for untyped extraction since the typed erasure
pipeline does inlining before erasure."* The Lean frontend produces untyped λ□ only;
nothing in the thread asks it for λ□ᵀ.

### O8. `.mli` generation / `to_ml_type`

Simon: *"The mli printing currently only has the base types Nat, Unit, Bool and the
formers List and `->`, other types should trigger the panic in `to_ml_type` in
Erasure.lean."* Eske hit it on most examples (he had redeclared base types to avoid
linking) and asked *"Maybe this could be warnings instead of panic?"*; Yannick: *"yes!
(I pushed the trivial fix)"*. This is a side-deliverable of `#erase` living entirely
outside any correctness statement.

---

## Theorems and proof structure

**There are none.** The source states no theorem and sketches no proof. Two statements
in it are nevertheless *proof-shaped* and load-bearing for the rework:

**T1 (Eske Nielsen, 10 Feb — informal, about peregrine's proofs, quoted verbatim).**
> "The constructor as block pass is currently mandatory because the correctness proofs
> of all the earlier passes assume no constructor as blocks, and later passes assume
> constructor as blocks."

*Shape:* a representation invariant split by phase. For the frontend this reads as an
**output obligation**, i.e. the frontend's correctness theorem should conclude with a
program in the precondition of peregrine's first pass (applied-constructor form,
well-formed environment), so that this repo's theorem and peregrine's verified pipeline
compose rather than merely coexist.

**T2 (`references/inlining_diagnosis.md`, 2026-05-26 — a negative result, this repo's
own).** For `binarytrees`, `instDecidableEqNat` is listed in `.inlinings`, is a trivial
alias `instDecidableEqNat := Nat.decEq`, and its kername matches byte-for-byte at call
site, declaration header and inlinings entry — yet the Malfunction output still defines
and calls it. Conclusion, verbatim: *"The bug is **not** in `lean-to-lambdabox`. … The
discrepancy lies in `peregrine`'s inlining pass, which fails to apply the
user-supplied inlining attribute on at least this shape of declaration."* Three
candidate causes are offered (phase ordering; a shape filter that requires a `tLambda`
body and skips `tConst` aliases; an allow-list excluding externally-bodied constants),
with the recommendation to file the issue upstream with `bt.ast`, `bt.ast.inlinings`
and the Malfunction output. *Status in the thread:* unresolved at the time of writing;
Yannick's response was *"Time to implement peregrine --debug :)"*.

---

## Lean-specific adaptations (as the collaborators experience them)

* **Typeclass dictionary code dominates.** Eske: ASTs *"2-4x the size of Rocq and Agda
  asts"*; *"just compiling the constant 5 results in 5 definitions and the constant
  appear[s] twice in the AST"*; *"we need 5 functions and 2 inductive types just to add
  two natural numbers, and only one of the functions performs computation the rest are
  just binding the right typeclass instance."* Simon: the Lean compiler *"pretty
  aggressively specializes typeclass instances"*, so the native pipeline never pays
  this; the λ□ pipeline does. Simon's account of the correct fix, verbatim: *"one would
  have to automatically detect functions with a type like `A -> [typeclass] -> B` that
  only recurse with the same typeclass and then generate a new version with type
  `A -> B` for each specific value of [typeclass] that appears in the code"* — i.e.
  **specialization, not inlining**; the two are conflated in the current
  `auto_inline_typeclass_dispatch` shortcut. The pragmatic middle ground Eske measured:
  inline `instHAdd`/`instOfNatNat`-style wrappers for `add/sub/mul/pow`, then `betared`
  + `unbox` → BinaryTrees' 10% overhead vs Agda/Rocq disappears.
* **Externs / axioms / Zarith.** Machine arithmetic arrives as bodiless λ□ constants;
  the OCaml backend links Zarith, the C backend has nothing. Zarith's `Z.erem` etc. are
  external C stubs and cannot be OCaml-inlined (Eske hit
  `Warning 55 [inlining-impossible]: Cannot inline: Function information unavailable` on
  `(Z.erem [@inlined]) n m`); Simon: *"normally the axiom files shouldn't have inlining
  annots on those"*.
* **IO primitives unsupported** (Simon, 3 Feb) — which is why the Lean programs in
  peregrine-tool PR#43 could not be run through the frontend.
* **Applied constructors + surviving parameters** (O2) — a Lean-side representation
  choice with a middle-end consequence.
* **Deep recursion.** `ulimit -s unlimited` is needed to run the benchmarks (Simon,
  from his MSc thesis; Yannick concurs; Eske saw stack overflows on macOS).
* **Panics as a UX default.** `to_ml_type` panics on unsupported types (O8) — patched
  to a warning. Relevant to the rework because a panicking `#erase` run still writes an
  `.ast`.
* **Build/toolchain friction is real and cross-repo**: opam local-vs-named switches
  (Yannick vs Matthieu, 11 Feb), a Makefile that needed rewriting from
  "one opam switch per lbox version" to "one peregrine **config file** per
  configuration" (Simon, 11 Feb; done by Eske, 12 Feb), and a two-day window where
  "frontend from today + tool from today" broke while the crossed pairs worked
  (Yannick's 13 Feb status report).

---

## Requirements for the rework

Numbered so they can be cited. Each is checkable.

**Z1 — The theorem must reach the file.** The deliverable the collaborators consume is
the `.ast` byte stream (O1), not an `LBTerm`. The rework's capstone must either
constrain the serialized S-expression (peregrine-tool has Sound/Complete proofs for
exactly this grammar in `theories/serialization/`, so a Lean-side round-trip /
injectivity statement against the transcribed grammar is the natural target), or state
in one explicit ledger row that serialization is uncovered. Silence is not an option:
the current development's crown theorem stops at `p = .untyped E (some t)` and never
mentions `Serialize.to_sexpr`.

**Z2 — Emit, and prove, the applied-constructor form.** Per T1, applied form is the
*required* input to peregrine, so the rework's erasure relation must target applied form
(`.construct i k []` under an application spine) as the **primary** shape, not as a
"representation gap" to be bridged to an idealized block form. Block form belongs
downstream, in a pass peregrine has already verified. This inverts the current design
and removes a whole epicycle.

**Z3 — State the output as peregrine's precondition.** The frontend's theorem should
conclude with an explicit well-formedness predicate on the emitted environment — the
one `peregrine validate` checks — so that composition with the verified middle-end is a
statement, not a hope. Include the constructor-form invariant of Z2 and the parameter
question of O2.

**Z4 — Axioms are an enumerated assumption, not a silence.** Every `@[extern]`/axiom
constant becomes a bodiless λ□ declaration (O5). The correctness statement must be
relative to an explicit, enumerated per-axiom specification (what a linked C/OCaml
implementation is assumed to compute), and the enumeration must be visible in the
capstone's premise ledger. This is the formal content of the Bas/Simon exchange.

**Z5 — The `.ast.inlinings` file is part of the deliverable.** The rework must (a)
guarantee the file is always written, even empty (the 17 Feb bug), and (b) say what
listing a kername *means*. The cheap true statement is available: peregrine inlines a
listed constant by substituting its own body, so the annotation is δ-preserving for any
list of constants that are declared with bodies in the emitted environment — i.e. the
frontend's obligation is only that every listed kername occurs as a `ConstantDecl` with
`Some body` in the same file. Prove that; scope the rest out loudly.

**Z6 — Target the programs the collaborators actually run.** The named benchmark
programs in the thread are `even` (the "counting beans" family), `unionfind`,
`triangle_rec`, `binarytrees`, plus the quicksort/`VerifyBench` set this repo tracks.
Their content is *exactly* the typeclass-dictionary layer: structure projections,
`casesOn`, applied constructors, `Nat` literals, `instDecidableEqNat`/`instHAdd`
aliases. A rework fragment that does not cover that layer covers none of the programs
the project is judged on. Coverage should be reported per program, as a table.

**Z7 — Untyped λ□ only, said once.** No collaborator asks for λ□ᵀ from Lean, and
typed-pipeline inlining happens before erasure (O7). Scope the rework to `Untyped` and
record it as a deliberate scope line rather than an omission.

**Z8 — Panicking runs must be excluded from the theorem, or the file must not be
written.** `to_ml_type` (O8) and the eraser's other panic sites succeed at the monad
level; a panicking `#erase` still writes an `.ast`. Any "if the run returns `.ok`"
hypothesis must either exclude panics or the capstone must say plainly that it does
not. The collaborators' experience (Eske hitting panics *"on most examples that I have
tried"*) makes this the failure mode they will actually meet.

**Z9 — Keep unverified product features out of, or explicitly inside, the ledger.**
The `.inlinings` emission and `auto_inline_typeclass_dispatch` (this repo's answer to
the 19 Feb typeclass discussion) are unverified product code that arrived on the
verification branch. The rework should either model them or list them, by name, as
out-of-fragment shipping behaviour.

**Z10 — The verified eraser must be the one people pin.** peregrine-tool's CI tests the
Lean frontend and consumers pin this repo **by git rev**; whatever the rework proves
must land on the branch those pins follow, or the proof is about code nobody runs.

**Z11 — Performance/AST-size is a stated non-goal of the proof but a stated goal of the
project.** Record explicitly that the rework does not certify the specialization /
inlining story of §"Lean-specific adaptations", so nobody reads a correctness theorem as
a claim about the 2–4× size gap.

---

## Open questions

1. **Parameters in constructor applications.** Yannick raised *"and parameters are still
   present"* alongside the blocks complaint, and it was never answered. Does peregrine's
   `dearg_ctors`/`dearg_consts` remove them, or is the frontend expected to? The answer
   decides whether the rework's erasure relation should drop parameters (and if so, on
   what typing evidence).
2. **What exactly is peregrine's input precondition** (Z3)? Is there a single
   `EWellformed`-style predicate with a flag record (`with_constructor_as_block = false`
   etc.) that the frontend can be proved to satisfy, and is it the same predicate
   `peregrine validate` runs?
3. **Is the `instDecidableEqNat` inlining bug (T2) fixed upstream?** The diagnosis
   recommends filing it; the thread ends unresolved. If it is a shape filter on
   `tConst` aliases, the frontend's `isTrivialAlias` auto-inlining is emitting exactly
   the shape peregrine drops.
4. **Whose trust story covers the axiom implementations** (Z4)? The C/OCaml
   implementations of Lean's `@[extern]` arithmetic are handwritten and linked; nobody
   in the thread claims them, and no repo verifies them.
5. **Is `(MPfile ())` — an empty module path — legal and unambiguous** per the format
   spec (O4)? Two Lean constants with the same flattened ident from different modules
   would collide.
6. **Should specialization (Simon's `A → [inst] → B ↦ A → B`) live in the frontend or in
   the middle-end?** If in the frontend, it is a program transformation that would need
   its own correctness proof in the rework's scope; if in the middle-end, it is
   peregrine's obligation and the frontend only has to not obstruct it.
7. **What does "verified frontend" mean to these collaborators?** The thread never asks.
   Before the rework fixes its capstone statement, it is worth putting Z1–Z5 to them as
   a one-page contract and getting the answer on the record — that is the missing
   external referee the review complains about, on the interface side.
