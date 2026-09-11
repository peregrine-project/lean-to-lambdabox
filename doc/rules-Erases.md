# `Erases` against `[S Fig. 18]`

`Erases` (`01-DESIGN.md` §4.2) is Sozeau et al.'s erasure relation transposed to `Lean.Expr`:
lean4lean's `TrExprS` with the target `VExpr` replaced by `LBTerm`, `sort` and `forallE`
absorbed into the box rule, and `box` added. It has **ten** rules, no side condition and no
registry, and its arm list is pinned by a `#guard` in `LeanToLambdaBox/Erases.lean`. This
table is the transport, rule by rule; `lake exe hygiene --tables` checks that every arm of the
Lean inductive appears below.

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
| `erases_tConst` | `const` | Drops universe levels, as the paper drops `u`. Takes no `Kername` parameter and no registry premise: `toKername` (`LeanToLambdaBox/Basic.lean:34`) is a function, which is what lets the bridge's name and constant invariants collapse into `CanonicalConstants` |
| `erases_tProj` | `proj` | Keyed on the source `Expr.proj S i e` and on `IndInfo`, the environment predicate declared alongside the relation: it reads the block off a declaration list of `VEnv.WF'` below `env`, and gives it λ□ coordinates through `indBlockKername` (the eraser's block kername) and `ctorFieldCounts` (Π-binders beyond the parameters). The premise `IndInfo env S iid np [nf]` is the single-constructor gate, and `hi : i < nf` the field-index bound. Deliberately **no** `TrExprS` premise: `TrProj.uniq` yields `IsDefEqU`, not equality, so a term premise would pin parameters the kernel only fixes up to defeq |
| `erases_tConstruct` | — | `Lean.Expr` has no constructor node; constructors are `.const` heads. The λ□ `.construct` node is introduced by `Lower.ctorApp` / `Lower.ctorEta` (`doc/rules-Lower.md`), not by `Erases` |
| `erases_tCase` + `Subsingleton` | — | `Lean.Expr` has no case node. `.case` is introduced by `Lower.elimApp` / `Lower.elimEta`. The `Subsingleton` criterion has no subject on emitted output: every emitted inductive is declared non-propositional (F-PROP), so the prop-gated rules are inert and such programs are outside the fragment |
| `erases_tFix` | — | `Lean.Expr` has no fixpoint node; top-level recursion is a declaration-level phenomenon `[R §4.1]`. `.fix` is introduced by `Lower.fixConst` / `Lower.fixBody` |
| `erases_tCoFix` | — | Lean has no coinduction |
| — | `mdata` | Transparent congruence with an identity target; no paper counterpart, harmless |
| — | `lit` | "A literal is its kernel unfolding", mirroring `TrExprS.lit`. Machine `Nat` is a separate refinement and is excluded from the fragment |
| `[S Fig. 18]` sort and `∀` premises | absorbed into `box` | `Erases.sort_erasable` and `Erases.forallE_erasable` prove that a `.sort` and a `.forallE` are `Erasable`, so the box rule covers them and `Erasure.lean:602`'s `unreachable!` for those heads is unreachable (`doc/panics.md`) |
| `[S §7.3]` weakening and substitutivity, `[L Lemma 16]` | `erases_shift`, `erases_subst`, `Erases.abstract`, `Erases.uninstantiateN`, `Erases.thin_vlet`, `erases_weakFV*`, `erases_uniform_*` | Statements carried, with the `ErasureCtx` index dropped. Nine of the relation's fifteen former arms survive per lemma, six die with the rules that left, and `mdata` adds one |

## Inversion

One lemma per source head, each a `cases` on the relation. Every head admits `box`, so each
reads as a disjunction with `ErasesBox env Us Δ e t` — "`e` has a translation that is
`Erasable`, and the image is `LBTerm.box`". `Erases.sort_inv` and `Erases.forallE_inv` have
that alternative alone, which is the shape `doc/panics.md` consumes.

`Erases.bvar_inv`, `Erases.fvar_inv`, `Erases.const_inv`, `Erases.app_inv`, `Erases.lam_inv`,
`Erases.letE_inv`, `Erases.proj_inv`, `Erases.lit_inv`, `Erases.mdata_inv`.

`IndInfo` comes with `IndInfo.of_wf'` (introduction from a declaration list) and
`IndInfo.mono` (the block data survives environment extension, which is what `Erases.mono`
needs at the `proj` arm).

## What the transport does not claim

* No Rocq-side counterpart of this relation exists or is planned: `grep -rn Erases rocq/` is
  empty, and a second formalisation kept in sync across repositories is out of scope. This
  table and `doc/rules-Lower.md` are the anchor instead, and the decision is a class-**E**
  row in `doc/trust.md`.
* The relation is not claimed to be the image of the eraser. That is the bridge's statement
  (`visitExpr_refines_erasesLB`), and its residual assumptions are named in `doc/trust.md`.
* `Erases` produces no `.construct`, `.case` or `.fix` node. The four Lean-specific
  compilation steps that a congruence over `Lean.Expr` cannot state live in `Lower`.
