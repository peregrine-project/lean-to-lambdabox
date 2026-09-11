# `Erases` against `[S Fig. 18]`

`Erases` (`01-DESIGN.md` §4.2) is Sozeau et al.'s erasure relation transposed to `Lean.Expr`:
lean4lean's `TrExprS` with the target `VExpr` replaced by `LBTerm`, `sort` and `forallE`
absorbed into the box rule, and `box` added. It has **eleven** rules and no registry, and its
arm list is pinned by a `#guard` in `LeanToLambdaBox/Erases.lean`. Rocq writes a constructor
`tConstruct`, an inductive type name `tInd` and everything else `tConst`; Lean writes all
three `Expr.const`, so `ctor` and `const` carry the premise that says which — `CtorOf` and
`ConstOrigin`, each exhibiting the declaration it reads. This table is the transport, rule by
rule; `lake exe hygiene --tables` checks that every arm of the Lean inductive appears below.

`[S]` is Sozeau, Forster, Lennon-Bertrand, Nielsen, Tabareau, Winterhalter, *Correct and
Complete Type Checking and Certified Erasure for Coq, in Coq* (J. ACM 2025); `[L]` is
Letouzey's thesis; `[R]` is the Lean extraction report. The fidelity table this refines is
`doc/rework/00-REFERENCE-SPEC.md` §3.3.

## Fig. 18 → `Erases`

| `[S Fig. 18]` rule | `Erases` rule | Deviation |
|---|---|---|
| `erases_box` | `box` | The one non-deterministic rule. Premises are a `TrExprS` witness and `Erasable`; no negative side condition anywhere else, mirroring MetaRocq `Extract.v:88-141`, so a structurally erased type former is also a legal image |
| `erases_tRel` | `bvar` **and** `fvar` | Locally-nameless split `[R §4.7]`: the eraser instantiates binders with free variables, so the relation needs both. `fvar` has no paper counterpart. Both keep the `Δ.find?` premise — without it the relation admits out-of-scope indices and `erases_subst`, `LBClosed` and first-orderness break |
| `erases_tLambda` | `lam` | Extends the `VLCtx` exactly as `TrExprS.lam` does, and records the **source** binder name. The ASCII-graphic filter of `fvar_to_name` (`LeanToLambdaBox/Erasure.lean:245-252`) is a printer constraint and lives in `LBWfPeregrine.asciiNames`, not here |
| `erases_tLetIn` | `letE` | ζ must be enabled in both semantics. `letE.nonDep` is ignored; the binder name is the source's |
| `erases_tApp` | `app` | None |
| `erases_tConst` | `const` | Drops universe levels, as the paper drops `u`. Takes no `Kername` parameter and no registry premise: `toKername` (`LeanToLambdaBox/Basic.lean:34`) is a function, which is what lets the bridge's name and constant invariants collapse into `CanonicalConstants`. The second premise, `ConstOrigin env c`, is Rocq's node distinction, not a guard on derivations: it exhibits the declaration — an axiom, a definition, an opaque constant or a member of a mutual block — that makes `c` this reading. It is **positive**, so an introduction site discharges it from the declaration list it already has; the exclusion direction (that a constructor or a type name has no such declaration) is a theorem of the kernel theory, consumed by uniqueness and by the ι arm's head step |
| `erases_tProj` | `proj` | Keyed on the source `Expr.proj S i e` and on `IndInfo`, the environment predicate declared alongside the relation: it reads the block off a declaration list of `VEnv.WF'` below `env`, and gives it λ□ coordinates through `indBlockKername` (the eraser's block kername) and `ctorFieldCounts` (Π-binders beyond the parameters). The premise `IndInfo env S iid np [nf]` is the single-constructor gate, and `hi : i < nf` the field-index bound. Deliberately **no** `TrExprS` premise: `TrProj.uniq` yields `IsDefEqU`, not equality, so a term premise would pin parameters the kernel only fixes up to defeq |
| `erases_tConstruct` | `ctor` | `Lean.Expr` has no constructor node: a constructor is a `.const` head, and `CtorOf env c I k` is the premise that reads it as one, off a declaration list of `VEnv.WF'` below `env`. The node is at the **bare head** — arguments arrive through `app`, so `.construct` carries an empty argument list (measured: 982/982 `tConstruct` nodes in `VerifyBench/ast/*.ast` carry one); `iid` and `k` are functions of the block, exactly as `toKername` is of the name. `IndInfo` supplies the block coordinates and is derivable from `CtorOf` alone (`CtorOf.indInfo`) |
| — | an inductive type name | No rule: a type former is `Erasable`, so `box` is its only image (`Erases.indInfo_erasable`). This is why the `const` rule cannot be premise-free — the ten-rule relation sent `Nat` as a term to `.const (toKername Nat)`, a kername the eraser emits only as an `.inductiveDecl`, on which the target's `delta` is stuck |
| `erases_tCase` + `Subsingleton` | — | `Lean.Expr` has no case node. `.case` is introduced by `Lower.elimApp`. The `Subsingleton` criterion has no subject on emitted output: every emitted inductive is declared non-propositional (F-PROP), so the prop-gated rules are inert and such programs are outside the fragment |
| `erases_tFix` | — | `Lean.Expr` has no fixpoint node; top-level recursion is a declaration-level phenomenon `[R §4.1]`. `.fix` is introduced by `Lower.fixConst` / `Lower.fixBody` |
| `erases_tCoFix` | — | Lean has no coinduction |
| — | `mdata` | Transparent congruence with an identity target; no paper counterpart, harmless |
| — | `lit` | "A literal is its kernel unfolding", mirroring `TrExprS.lit`. Machine `Nat` is a separate refinement and is excluded from the fragment |
| `[S Fig. 18]` sort and `∀` premises | absorbed into `box` | `Erases.sort_erasable` and `Erases.forallE_erasable` prove that a `.sort` and a `.forallE` are `Erasable`, so the box rule covers them and `Erasure.lean:602`'s `unreachable!` for those heads is unreachable (`doc/panics.md`) |
| `[S §7.3]` weakening and substitutivity, `[L Lemma 16]` | `erases_shift`, `erases_subst`, `Erases.abstract`, `Erases.uninstantiateN`, `Erases.thin_vlet`, `erases_weakFV*`, `erases_uniform_*`, `Erases.mono` | Statements carried, with the `ErasureCtx` index dropped. Every arm transports: `ctor` and `const` carry environment premises only, and `CtorOf`, `IndInfo` and `ConstOrigin` are monotone in `env` by the `env₀ ≤ env` conjunct each of them exhibits |

## Inversion

One lemma per source head, each a `cases` on the relation. Every head admits `box`, so each
reads as a disjunction with `ErasesBox env Us Δ e t` — "`e` has a translation that is
`Erasable`, and the image is `LBTerm.box`". `Erases.sort_inv` and `Erases.forallE_inv` have
that alternative alone, which is the shape `doc/panics.md` consumes.

`Erases.bvar_inv`, `Erases.fvar_inv`, `Erases.const_inv`, `Erases.app_inv`, `Erases.lam_inv`,
`Erases.letE_inv`, `Erases.proj_inv`, `Erases.lit_inv`, `Erases.mdata_inv`.

`Erases.const_inv` has **three** alternatives, one per reading of `Expr.const`: the box
witness, the `ctor` image with `CtorOf`/`IndInfo` exhibited, and the `const` image with the
constant lookup and `ConstOrigin`. Nothing there excludes two of the three — that is the
kernel theory's business — so a consumer that knows its reading supplies the corresponding
premise and discards the others. `Erases.ctor_inv` is keyed on the **target** instead: a
`.construct` image is the `ctor` rule's, so its argument list is empty and its block data is
exhibited; the source is not pinned there, because `lit` and `mdata` pass an image through.

`IndInfo` comes with `IndInfo.of_wf'` (introduction from a declaration list) and
`IndInfo.mono` (the block data survives environment extension, which is what `Erases.mono`
needs at the `proj` arm). `CtorOf` and `ConstOrigin` come with `.mono` for the same reason,
`CtorOf.indInfo` (a constructor's block is its type's), and `ConstOrigin.of_axiom` (the
one-axiom introduction). Both readings are exhibited on a hand-built one-inductive,
one-definition `VEnv.WF'` fixture: `erases_ctor_fires` and `erases_const_fires`.

## What the transport does not claim

* No Rocq-side counterpart of this relation exists or is planned: `grep -rn Erases rocq/` is
  empty, and a second formalisation kept in sync across repositories is out of scope. This
  table and `doc/rules-Lower.md` are the anchor instead, and the decision is a class-**E**
  row in `doc/trust.md`.
* The relation is not claimed to be the image of the eraser. That is the bridge's statement
  (`visitExpr_refines_erasesLB`), and its residual assumptions are named in `doc/trust.md`.
* `Erases` produces no `.case` and no `.fix` node. Those two compilation steps — an
  eliminator application and top-level recursion, neither of them a `Lean.Expr` node — live in
  `Lower`. The `.construct` node is not among them: it is `[S Fig. 18]`'s own `tConstruct`
  congruence at the bare head, and the pass layer introduces no constructor node of its own.
