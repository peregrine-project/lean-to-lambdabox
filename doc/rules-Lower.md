# `Lower` and `LowerFix` against `iota_red`, `fixSubst` and `optimize`

`Lower` (`01-DESIGN.md` §4.4) is the λ□ → λ□ pass relation that carries the four Lean-specific
compilation steps `Erases` cannot state: constructor introduction, eliminator-to-`case`
translation, the two η-expansions, and the block-level fixpoint. It is indexed by the
specification environment `Σ⁺ : GlobalDeclarations` **and nothing else** — no source term, no
`VEnv`, no relevance verdict, no run state (`lake exe hygiene --anti-epicycle` enforces this;
`FVarId` is λ□'s own fvar syntax and is not on the banned list).

Seventeen arms: eleven congruence, four redex, two recursion. `lake exe hygiene --tables`
checks that every arm appears below. The right-hand column names the object each arm is
answerable to: a MetaRocq rule (`EWcbvEval`'s `iota_red`, `fixSubst`), the shipping eraser's
own site, or the pass template `optimize` (`LeanToLambdaBox/Optimize.lean`), whose statement
shape `LBPassR` reuses.

## Congruence (11)

| Arm | Relates | Anchor and deviation |
|---|---|---|
| `box` | `.box` to `.box` | `optimize`'s box arm; □ is preserved, never introduced, by a pass |
| `bvar` | `.bvar i` to itself | de Bruijn indices are untouched: passes do not renumber |
| `fvar` | `.fvar x` to itself | λ□'s locally-nameless residue; the fix arms are what bind these |
| `prim` | `.prim p` to itself | MetaRocq's `tPrim`; no primitive is rewritten |
| `const` | `.const kn` to `.const kn`, with `¬ RuntimeKey Σ⁺ kn` | The guard is load-bearing: without it a constructor or eliminator constant that the pass prunes strands the target with a dangling key. Deliberately non-deterministic at a block member, where `fixConst` also applies |
| `lambda` | under the binder | Binder **names** are free: `WcbvEval` reads only their number (`LeanToLambdaBox/Semantics/Eval.lean:143-153,171`) |
| `letIn` | value and body | ζ in the target semantics; names free as above |
| `app` | head and argument | |
| `proj` | the projected term | The projection triple is preserved |
| `construct` | arguments pointwise | Block form: the node's own argument list. List premises are the indexed form (`hlen` plus `∀ i, i < …`), since `List.Forall₂` as a premise is a nested-inductive occurrence the kernel rejects |
| `case` | discriminant and branches, arities preserved | `iota_red` reads the branch's binder **count**, so `hn` pins each alternative's arity and nothing else. Written `«case»`: `case` is a keyword |

## Redex (4) — where the eraser's compilation steps live

| Arm | Source → target | Anchor and deviation |
|---|---|---|
| `ctorApp` | `mkApps (.const kn) args` → `mkApps (.construct iid k []) args'` | `visitConstructor` (`LeanToLambdaBox/Erasure.lean:731-761`) after `visitCtorEtaGo`'s saturation test (`:722-728`, `args.size ≥ arity`). `hsat` is that test, and it is what discharges `LBWfPeregrine.etaCtorsEnv`; it also makes this arm and `ctorEta` disjoint on `args.length`. Applied form, so no arity is stored in the node and inductive parameters are kept |
| `ctorEta` | an under-applied constructor → `mkLambdas ns (…)` | `visitCtorEtaGo` (`LeanToLambdaBox/Erasure.lean:722-728`) pushes fresh binders into the spine and wraps the result in `mkLambdas`; `shift ns.length 0` moves the already-lowered prefix under them. `hns : ns ≠ []` keeps it disjoint from `ctorApp` |
| `elimApp` | `mkApps hd (pre ++ disc :: minors ++ extra)` → `mkApps (.case (iid, np) disc' alts) extra'` | `visitCases` (`LeanToLambdaBox/Erasure.lean:768-835`), whose over-application rides outside the node (`args[casesInfo.arity:]`, `:832`). The `dp` arguments before the discriminant — parameters, motive, and for `rec` the minors' prefix — are **dropped**, which is sound for a forward simulation and is what MetaRocq's own expansion does. The head is `ElimHeadOf`: `.const kn` pre-δ, or an `ElimBody` shape post-δ, the disjunct `lower_correct`'s δ case needs for its intermediate configurations |
| `elimEta` | an under-applied eliminator → `mkLambdas ns (…)` | `visitCasesEtaGo` (`LeanToLambdaBox/Erasure.lean:705-712`), the same shape as `ctorEta` |

Branch peeling is a separate relation: `LowerAlt Σ⁺ nf m alt` turns a minor's λ-chain into an
alternative's binder list — arm `done` at arity zero, arm `lam` peeling one binder — and
`LowerAlts` is its pointwise lift over the block's field arities. Only the *number* of
binders is pinned, because that is all `iota_red` reads.

## Recursion (2) — `fixSubst`

| Arm | Relates | Anchor and deviation |
|---|---|---|
| `fixConst` | `.const kn` to `.fix defs j`, for `kn` the block's *j*-th member | The call site: `visitMutual` registers each member as the whole block's `.fix` node (`LeanToLambdaBox/Erasure.lean:904-918`) |
| `fixBody` | the member's specification body to the same `.fix defs j` | The value side, and the arm the δ step needs: after the specification environment unfolds `kn`, the source configuration is the plain body while the target is the `.fix`. Its absence is what makes a functional pass, and a one-sided fix relation, false |

Both arms read their premises through `LowerBlock` (the fields are inlined into each arm:
the kernel rejects the structure as a nested premise). Two fields answer machine-checked
refutations:

* `hrarg : ∀ d ∈ defs, d.principalArgIdx = 0`. Without it the correctness statement is
  false — at `principalArgIdx = 1` the source evaluates to `□` while the target is a stuck
  spine. It is a fact about the emitter: `mkDef` never sets the field and the default is `0`
  (`LeanToLambdaBox/Basic.lean:67`), whose comment "this doesn't matter computationally" is
  false under this `WcbvEval`; `FixUnfoldChain` already carries the same premise
  (`LeanToLambdaBox/FixUnfold.lean:803`).
* a **block-shared** `ids`. Per-member existential names cannot feed
  `closeFix_substList_fixSubst` (`LeanToLambdaBox/FixUnfold.lean:748`), whose freshness
  clause is against every `.fix defs j`, and `ClosedEnv` cannot supply it because
  `LBClosed (.fvar _) k` is `True` (`LeanToLambdaBox/Closed.lean:40`). `visitMutual` mints
  one `ids` list per block (`LeanToLambdaBox/Erasure.lean:905`), so the shared form is what
  the emitter does.

There is **no** `fix` congruence arm: the specification environment declares no `.fix` (block
members hold their plain bodies) and `visitExpr_shape_all` proves `NoFix` for the subject
term unconditionally, so the source side of `Lower` never contains one. Adding the arm would
be dead code.

## The fixpoint closure — `LowerFix`

| Object | What it is | Anchor |
|---|---|---|
| `ConstToFVar kns ids` | replaces `.const kns[j]` by `.fvar ids[j]`; does not descend under a `.fix`, there being none to descend under | the λ□-only residue of the retired source-indexed fix-variable rule |
| `CloseConstAt kns ids t u` | `∃ t', ConstToFVar kns ids t t' ∧ u = closeFix ids 0 t'` | phrased through the existing `closeFix` so `closeFix_substList_fixSubst` applies verbatim and no `Kername`-keyed twin of `FixUnfold`'s theorems is needed |
| `Lower.constToFix` | a fix unfolding (`WcbvEval.fix_guarded`'s `substList (fixSubst defs)`) puts `.fix defs i` where the lowered body has the sibling `.const knᵢ`; the result is still `Lower`-related to the same body | `fixSubst`; this is the transport that makes the fix arms usable |
| `LowerFix Σ⁺ kns bs defs` | `∃ bs' ids, LowerBlock …`, the declaration-level statement for `LowerEnv` | tolerates an unused fix binder: `visitMutual` decides recursiveness by `name_occurs` on the **source** body (`LeanToLambdaBox/Erasure.lean:885`), so erasure can remove the only self-reference and leave the binder unused |
| `ErasesLBFix` | `∃ t₀ t₁, Erases … t₀ ∧ Lower Σ⁺ t₀ t₁ ∧ ConstToFVar kns ids t₁ t` | the block-body motive: inside `visitMutual`'s block branch the eraser rewrites a source `.const` to `.fvar id` (`visitConst`, `LeanToLambdaBox/Erasure.lean:660-664`), a pair no two-factor composite can state |

## Against `optimize`

`optimize` (`[S §7.4]`, `LeanToLambdaBox/Optimize.lean`) is the tree's worked example of a
verified λ□ → λ□ pass, and `Lower` is stated in its shape: a relation between two λ□ terms
over one environment, with a simulation theorem and a non-vacuity guard per arm. The
differences are named, not silent: `optimize` is a function and `Lower` is a relation,
because the eraser's constructor and `casesOn` handling is not a function of the λ□ term
alone; and `optimize` preserves the environment, whereas `Lower`'s redex arms read it
(`CtorDecl`, `ElimDecl`, `DefnDecl`).
