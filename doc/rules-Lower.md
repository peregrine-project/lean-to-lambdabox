# `Lower` and `LowerFix` against `iota_red`, `fixSubst` and `optimize`

`Lower` (`01-DESIGN.md` §4.4) is the λ□ → λ□ pass relation that carries the Lean-specific
compilation steps `Erases` cannot state: the eliminator-to-`case` translation and the
block-level fixpoint. It is indexed by the specification environment `Γ` **and nothing else**
— no source term, no `VEnv`, no relevance verdict, no run state (`lake exe hygiene
--anti-epicycle` enforces this; `FVarId` is λ□'s own fvar syntax and is not on the banned
list). The code writes the environment `Γ`: `Σ` is a reserved token in Lean.

Fifteen arms: eleven congruence, one redex, three recursion. `lake exe hygiene --tables`
checks that every arm appears below. The **counterpart** column names the MetaRocq object the
arm is answerable to — `iota_red` or `fixSubst` of `EWcbvEval`, the pass template `optimize`
(`LeanToLambdaBox/Optimize.lean`, `[S §7.4]`, whose statement shape `Lower` reuses), or `none`
for the arms that exist because the Lean eraser compiles something MetaRocq's λ□ does not.
The last column names the eraser site and every deviation.

## Congruence (11)

| Arm | Relates | Counterpart | Anchor and deviation |
|---|---|---|---|
| `box` | `.box` to `.box` | `optimize` | □ is preserved, never introduced, by a pass |
| `bvar` | `.bvar i` to itself | `optimize` | de Bruijn indices are untouched: passes do not renumber |
| `fvar` | `.fvar x` to itself | `optimize` | λ□'s locally-nameless residue; the fix arms are what bind these |
| `prim` | `.prim p` to itself | `optimize` | MetaRocq's `tPrim`; no primitive is rewritten |
| `const` | `.const kn` to `.const kn`, with `¬ RuntimeKey Γ kn` | `optimize` | The guard is load-bearing: without it an eliminator constant that the pass prunes strands the target with a dangling key. Deliberately non-deterministic at a block member, where `fixConst` also applies |
| `lambda` | under the binder | `optimize` | Binder **names** are free: `WcbvEval` reads only their number (`LeanToLambdaBox/Semantics/Eval.lean:143-153,171`) |
| `letIn` | value and body | `optimize` | ζ in the target semantics; names free as above |
| `app` | head and argument | `optimize` | Also the arm that carries a constructor's arguments: the head is a `.construct` node already, because `Erases.ctor` emitted it |
| `proj` | the projected term | `optimize` | The projection triple is preserved |
| `construct` | arguments pointwise | `optimize` | Block form: the node's own argument list. List premises are the indexed form (`hlen` plus `∀ i, i < …`), since `List.Forall₂` as a premise is a nested-inductive occurrence the kernel rejects |
| `case` | discriminant and branches, arities preserved | `iota_red` | `iota_red` reads the branch's binder **count**, so `hn` pins each alternative's arity and nothing else. Written `«case»`: `case` is a keyword |

## Redex (1) — where the eraser's `casesOn` compilation lives

| Arm | Source → target | Counterpart | Anchor and deviation |
|---|---|---|---|
| `elimApp` | `mkApps (.const kn) (pre ++ disc :: minors ++ extra)` → `mkApps (.case (iid, np) disc' alts) extra'` | `iota_red` | `visitCases` (`LeanToLambdaBox/Erasure.lean:768-835`), whose over-application rides outside the node (`args[casesInfo.arity:]`, `:832`). The `dp` arguments before the discriminant — parameters, motive, and for `rec` the minors' prefix — are **dropped**, which is sound for a forward simulation and is what MetaRocq's own expansion does. The head is a bare `.const kn` with `ElimDecl Γ kn iid np dp nfs`, which exhibits both the eliminator's body **and** `iid`'s inductive block, so the emitted node's arity data is in scope on the target. **Deviation:** the arm carries `LowerAlts`' three conjuncts inlined (`hmlen`, `halen`, `hmin`), because `LowerAlts` is defined after the mutual block and cannot occur in it; `Lower.elimApp'` is the packaged form |

There is **no** `ctorApp` arm: a constructor constant erases to `.construct iid k []` by
`Erases.ctor` and its arguments arrive through `Erases.app`, so the pass meets the node
already built and the `construct`/`app` congruence arms relate it. There is no `ctorEta` and
no `elimEta` either. `Lower` is compositional, so an η-expanded head composes under `app`
into `mkApps (mkLambdas ns body) args'` — a β-redex target with no bound on nesting, which
every spine-inverting arm of the simulation would have to collapse. What the two arms covered
is the coverage restriction **N19** (no under-applied constructor or eliminator occurrence), a
decidable conjunct of `Supported`, and the shipping finding **F-ETA2** in
`doc/rework/03-DEV-FIX.md`. For constructors N19 costs nothing once F-ETA2 is repaired: applied-form
λ□ evaluates a partially applied constructor spine natively
(`Value.construct_app_val`, `LeanToLambdaBox/Semantics/Values.lean:104`). For eliminators it is
a real restriction.

There is likewise no `ElimHeadOf`: its second disjunct — an `ElimBody` *shape* as a head —
existed only for the δ chain inside a simulation run at the specification environment, and it
is what made that simulation refutable at every environment. Both eliminator readings are now
one `.const kn` head with `ElimDecl`.

Branch peeling is a separate relation: `LowerAlt Γ nf m alt` turns a minor's λ-chain into an
alternative's binder list — arm `done` at arity zero, arm `lam` peeling one binder — and
`LowerAlts` is its pointwise lift over the block's field arities. Only the *number* of
binders is pinned, because that is all `iota_red` reads.

## Recursion (3) — `fixSubst`

| Arm | Relates | Counterpart | Anchor and deviation |
|---|---|---|---|
| `fixConst` | `.const kn` to `.fix defs j`, for `kn` the block's *j*-th member, with `¬ RuntimeKey Γ kn` | `fixSubst` | The call site: `visitMutual` registers each member as the whole block's `.fix` node (`LeanToLambdaBox/Erasure.lean:904-918`). `hnk` is the same guard `const` carries and is load-bearing for the *inversion*: `ElimDecl` implies `DefnDecl`, so without it nothing keeps a `.fix` image off an eliminator constant and `Lower.source_const` cannot refute an eliminator head |
| `fixBody` | the member's specification body to the same `.fix defs j` | `fixSubst` | The value side, and the arm the δ step needs: after the specification environment unfolds `kn`, the source configuration is the plain body while the target is the `.fix`. Its absence is what makes a functional pass, and a one-sided fix relation, false. Its source is constrained **only** by `hj : bs[j]? = some b`, so the arm's own `hfl` is what excludes it at a non-λ source |
| `fixEta` | the member's specification body to `.lambda n (.app (.fix defs j) (.bvar 0))`, at a free binder name | `fixSubst` | What `visitMutual` registers for a member (`Erasure.etaExpandFix`, `LeanToLambdaBox/Erasure.lean:478`), and MetaRocq's `eta_fixpoint` (`../metarocq/template-rocq/theories/EtaExpand.v:72`) at `1 + rarg = 1`, the only shape `LowerBlock.hrarg` admits. The binder name is **free**, not `.anon`: `ConstToFVar.lambda` renames binders, so a pinned name falsifies `Lower.constToFix` (`LowerFix.lean`'s `lowerfix_fixEta_renamed`). `Lower.fixEta'` is the `.anon` instance, `LBTerm.etaFix defs j` |

`fixBody` and `fixEta` fire on the **same** source at the same block and the same premises, so
a block member's body has two images and `Lower` is not a function of its source. That is a
property of the pass, not a defect: `LowerFixFixture.lower_not_functional` checks it, the
`const`/`fixConst` pair is the same phenomenon at the member's constant, and no consumer reads
`Lower` as functional — the inversion kit (`Lower.source_*`) is keyed on the target's shape,
and takes the `fixEta` case at the two places the target is a λ (`Lower.source_isLambda`,
`Lower.source_lambda`).

The three arms read their premises through `LowerBlock` (the fields are inlined into each arm:
the kernel rejects the structure as a nested premise; `Lower.fixConst'` and `Lower.fixBody'`
are the packaged forms). Three fields answer machine-checked refutations:

* `hrarg : ∀ d ∈ defs, d.principalArgIdx = 0`. Without it the correctness statement is
  false — at `principalArgIdx = 1` the source evaluates to `□` while the target is a stuck
  spine. It is a fact about the emitter: `mkDef` never sets the field and the default is `0`
  (`LeanToLambdaBox/Basic.lean:67`), whose comment "this doesn't matter computationally" is
  false under this `WcbvEval`; `FixUnfoldChain` already carries the same premise
  (`LeanToLambdaBox/FixUnfold.lean:803`).
* `hfl : ∀ i, i < defs.length → isLambda (defs[i]!).body = true`, the λ-headedness of the
  **emitted** definitions. It is `LBWfPeregrine.fixLambda`'s clause
  (`LeanToLambdaBox/Output.lean`) at this block: `visitMutual` erases each member's compiler
  value and closes it with `mkDef` (`LeanToLambdaBox/Erasure.lean`), and λ□'s own `tFix`
  well-formedness rejects anything else. The **source** side is not asserted a second time —
  it is `LowerBlock.lambda_of_fixLambda`, a theorem reading this field. Keyed on the block
  rather than on the environment, because a condition quantified over every `LowerBlock` over
  `Γ` is refuted by one declared non-λ body: `LowerCtorBodyFixture.lowerBlock_needs_lambda_bodies`
  is that one-member block, `Unit.unit`'s `.construct` shape, which every one of the five
  programs declares. Restriction **N22** in `doc/coverage.md`.
* a **block-shared** `ids`. Per-member existential names cannot feed
  `closeFix_substList_fixSubst` (`LeanToLambdaBox/FixUnfold.lean:744`), whose freshness
  clause is against every `.fix defs j`, and closedness cannot supply it because
  `LBClosed (.fvar _) k` is `True` (`LeanToLambdaBox/Closed.lean:35`). `visitMutual` mints
  one `ids` list per block (`LeanToLambdaBox/Erasure.lean:905`), so the shared form is what
  the emitter does.

There is **no** `fix` congruence arm: the specification environment declares no `.fix` — a
block's members hold their plain bodies, and the `.fix` node is what `fixConst`/`fixBody`
introduce on the target side — so the source side of `Lower` never contains one. Adding the
arm would be dead code. There is likewise no `CtorHeadOf` (a post-δ constructor value is
already related by `app` and `construct`), no `CtorDecl` at all (its only consumers were the
two deleted constructor arms, and keeping it inside `RuntimeKey` made `Lower.const` — hence
the composite — uninhabitable at every use site of a definition whose compiler body is a bare
constructor), and no `DefnDeclFix` premise on `const`.

## The fixpoint closure — `Lower.lean` and `LowerFix`

`ConstToFVar` and `CloseConstAt` are defined in `LeanToLambdaBox/Lower.lean`: `LowerBlock`'s
`hcl` field mentions `CloseConstAt`, and the two fix arms inline that field, so they precede
`Lower` itself, and so are the two `hfl` transports, which the inversion kit there consumes.
`LowerFix.lean` holds the rest of the closure, and repairs one statement of `01-DESIGN.md`
that is false as written; its fixture theorem is the refutation. `LowerBlock` tolerates an
unused fix binder: `visitMutual` decides recursiveness by `name_occurs` on the **source**
body (`LeanToLambdaBox/Erasure.lean:885`), so erasure can remove the only self-reference and
leave the binder unused.

| Object | What it is | Anchor |
|---|---|---|
| `ConstToFVar kns ids` | replaces `.const kns[j]` by `.fvar ids[j]`; a `.fix` node maps to itself — no block member is declared as a `.fix`, and a nested one belongs to another block, whose members are none of `kns` | the λ□-only residue of the retired source-indexed fix-variable rule |
| `CloseConstAt kns ids t u` | `∃ t', ConstToFVar kns ids t t' ∧ u = closeFix ids 0 t'` | phrased through the existing `closeFix` so `closeFix_substList_fixSubst` applies verbatim and no `Kername`-keyed twin of `FixUnfold`'s theorems is needed |
| `Lower.constToFix` | a fix unfolding (`WcbvEval.fix_guarded`'s `substList (fixSubst defs)`) puts `.fix defs i` where the lowered body has the sibling `.const knᵢ`; the result is still `Lower`-related to the same body | `fixSubst`; the transport that makes the fix arms usable. **Deviation:** it takes `hfv` — the fixvars do not already occur in `t` — in place of the design's inert `LBClosed t 0`, which `LowerFixFixture.constToFix_needs_freshness` refutes; at the call site `hfv` is `LowerBlock.hfresh` |
| `Lower.fixUnfold` | a member's unfolded definition is a λ still related to its specification body, off `LowerBlock.hfl` and with no premise of its own | what the target does where the source δ-steps into a recursive body. The transport the simulation's β and δ arms actually spend is `Lower.appReady` (`LeanToLambdaBox/ErasesCorrect/Steps.lean`), which takes no premise either; `hfl` is what makes its `fixBody` sub-case a projection |
| `Lower.fixBody_of_block`, `Lower.fixEta_of_block` | the two body-source fix arms at the granularity a declaration is stated at: from `LowerBlock`, `kns[j]? = some kn` and `DefnDecl Γ kn b`, the member's body relates to `.fix defs j` and to `LBTerm.etaFix defs j` | what `LowerEnv.defs` is discharged by at a registered block member (`ColdStartShape.lean`), and what the δ step's head reading spends. They replace the `LowerFix` predicate — `∃ bs' ids, LowerBlock …` — whose only consumer was `LowerEnv.defs`' η disjunct, deleted because it collapses into the `Lower` disjunct through `fixEta_of_block` |
| `ErasesLBFix` | `∃ t₀ t₁, Erases … t₀ ∧ Lower Γ t₀ t₁ ∧ ConstToFVar kns ids t₁ t` | the block-body motive: inside `visitMutual`'s block branch the eraser rewrites a source `.const` to `.fvar id` (`visitConst`, `LeanToLambdaBox/Erasure.lean:660-664`), a pair no two-factor composite can state |

## Against `optimize`

`optimize` (`[S §7.4]`, `LeanToLambdaBox/Optimize.lean`) is the tree's worked example of a
verified λ□ → λ□ pass, and `Lower` is stated in its shape: a relation between two λ□ terms
over one environment, with a simulation theorem and a non-vacuity guard per arm. The
differences are named, not silent: `optimize` is a function and `Lower` is a relation,
because the eraser's `casesOn` handling is not a function of the λ□ term alone; and
`optimize` preserves the environment, whereas `Lower`'s redex and recursion arms read it
(`ElimDecl`, `DefnDecl`).

## What `Lower.lean` proves about the relation

`ClosedBodies Γ` — every constant `Γ` declares has a closed body — is the one environment-side
premise these carry; it is a fact about the specification environment (`LBWfSpec`'s second
conjunct, `LeanToLambdaBox/ErasesEnv.lean`), and the two fix arms need it: the source
side of `fixBody` is a declared body, and a block's emitted `.fix` is `closeFix` of one.
Closedness of the two eliminator shapes needs no premise at all — `ElimBody.closed` proves it
in `LeanToLambdaBox/ElimBody.lean`, which `Lower.lean` imports.

The source-side inversion kit carries **no** environment-side guard beside it: `Lower.fixBody`'s
source is unconstrained by syntax, and what rules the `.fix` image out at every source shape but
a λ is the derivation's own `LowerBlock.hfl`, through `LowerBlock.lambda_of_fixLambda`.

| Theorem | Statement | Used for |
|---|---|---|
| `Lower.closed` | `ClosedBodies Γ → Lower Γ s t → ∀ k, LBClosed s k → LBClosed t k` | the pass invents no index; feeds the two commutation laws |
| `Lower.shift_comm` | `ClosedBodies Γ → Lower Γ s t → ∀ d c, Lower Γ (shift d c s) (shift d c t)` | `subst_comm`'s `bvar` case |
| `Lower.subst_comm` | `ClosedBodies Γ → Lower Γ a a' → Lower Γ s t → ∀ d, Lower Γ (subst a d s) (subst a' d t)` | the β, ζ and ι steps of a forward simulation |
| `Lower.substList_comm` | the same law over a whole substitution list | the ι step's branch application |
| `Lower.mkApps` | spine congruence from head and arguments | over-application, and the value side of a constructor spine |
| `Lower.target_box`/`_bvar`/`_fvar`/`_prim`/`_const`/`_construct`/`_fix` | what a target of that shape can come from | inversion at a value; `target_fix` returns the whole `LowerBlock` |
| `Lower.source_box`/`_bvar`/`_fvar`/`_prim`/`_letIn`/`_proj`/`_construct`/`_case`/`_fix`/`_lambda`/`_const`/`_construct_nil` | what a source of that shape can go to, with no premise: the `fixBody` reading is excluded from the derivation | the simulation's per-node inversion. `source_const` gives **two** images, both under `¬ RuntimeKey Γ kn`, which is what lets an `ElimDecl` at `kn` refute both |
| `Lower.notFix_of_block`/`.ne_fix_of_block` | only a constant or a λ has a `.fix` image, premise-free | what the whole `source_*` kit runs on |
| `isLambda_toBvar`/`isLambda_closeFix`/`ConstToFVar.isLambda_eq` | `toBvar`, `closeFix` and the block rewriting are faithful on the head constructor | the two halves of the `hfl` transport |
| `Lower.source_isLambda`, `LowerBlock.targetLambda_of_fixLambda`/`.lambda_of_fixLambda` | `hfl` read at the lowered bodies, and at the specification bodies | `lambda` is the only arm with a λ-headed target, so `Lower.source_isLambda` is total and neither transport takes a premise |
| `ElimDecl.uniq` | two eliminator declarations at one key agree on `(iid, np, dp, nfs)` | `LBTerm.envLookup` is a function and the two `ElimBody` shapes are injective and distinct; the ι arm's under-application bound reads it |
| `Lower.concat`/`.drop_reverse` | pointwise relation through `++ [x]`, `drop` and `reverse` | the spine bookkeeping of the ι and β steps |
| `LowerAlt.arity` | `LowerAlt Γ nf m alt → alt.1.length = nf` | the binder count `iota_red` reads |
| `NoBox` and its family | box-freedom of a λ□ term, with `NoBox_shift` | the capstone's box-free conclusion; `LowerFix.noBox_lower_needs_noFix` shows the naive transport along `Lower` false |

`#print axioms Lower` is `[propext]`; the two commutation laws add `Quot.sound` through the
`List` lemmas their indexed premises go by.
