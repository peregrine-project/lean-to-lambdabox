# `Lower` and `LowerFix` against `iota_red`, `fixSubst` and `optimize`

`Lower` (`01-DESIGN.md` §4.4) is the λ□ → λ□ pass relation that carries the four Lean-specific
compilation steps `Erases` cannot state: constructor introduction, eliminator-to-`case`
translation, the two η-expansions, and the block-level fixpoint. It is indexed by the
specification environment `Γ` **and nothing else** — no source term, no `VEnv`, no relevance
verdict, no run state (`lake exe hygiene --anti-epicycle` enforces this; `FVarId` is λ□'s own
fvar syntax and is not on the banned list). The code writes the environment `Γ`: `Σ` is a
reserved token in Lean.

Seventeen arms: eleven congruence, four redex, two recursion. `lake exe hygiene --tables`
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
| `const` | `.const kn` to `.const kn`, with `¬ RuntimeKey Γ kn` | `optimize` | The guard is load-bearing: without it a constructor or eliminator constant that the pass prunes strands the target with a dangling key. Deliberately non-deterministic at a block member, where `fixConst` also applies |
| `lambda` | under the binder | `optimize` | Binder **names** are free: `WcbvEval` reads only their number (`LeanToLambdaBox/Semantics/Eval.lean:143-153,171`) |
| `letIn` | value and body | `optimize` | ζ in the target semantics; names free as above |
| `app` | head and argument | `optimize` | |
| `proj` | the projected term | `optimize` | The projection triple is preserved |
| `construct` | arguments pointwise | `optimize` | Block form: the node's own argument list. List premises are the indexed form (`hlen` plus `∀ i, i < …`), since `List.Forall₂` as a premise is a nested-inductive occurrence the kernel rejects |
| `case` | discriminant and branches, arities preserved | `iota_red` | `iota_red` reads the branch's binder **count**, so `hn` pins each alternative's arity and nothing else. Written `«case»`: `case` is a keyword |

## Redex (4) — where the eraser's compilation steps live

| Arm | Source → target | Counterpart | Anchor and deviation |
|---|---|---|---|
| `ctorApp` | `mkApps (.const kn) args` → `mkApps (.construct iid k []) args'` | `none` | `visitConstructor` (`LeanToLambdaBox/Erasure.lean:731-761`) after `visitCtorEtaGo`'s saturation test (`:722-728`, `args.size ≥ arity`). `hsat` is that test, and it is what discharges `LBWfPeregrine.etaCtorsEnv`; it also makes this arm and `ctorEta` disjoint on `args.length`. Applied form, so no arity is stored in the node and inductive parameters are kept. No MetaRocq rule builds this node — it is what `iota_red` later destructs |
| `ctorEta` | an under-applied constructor → `mkLambdas ns (…)` | `none` | `visitCtorEtaGo` (`LeanToLambdaBox/Erasure.lean:722-728`) pushes fresh binders into the spine and wraps the result in `mkLambdas`; `shift ns.length 0` moves the already-lowered prefix under them, and `bvarsDesc ns.length` applies them outermost first. `hns : ns ≠ []` keeps it disjoint from `ctorApp` |
| `elimApp` | `mkApps hd (pre ++ disc :: minors ++ extra)` → `mkApps (.case (iid, np) disc' alts) extra'` | `iota_red` | `visitCases` (`LeanToLambdaBox/Erasure.lean:768-835`), whose over-application rides outside the node (`args[casesInfo.arity:]`, `:832`). The `dp` arguments before the discriminant — parameters, motive, and for `rec` the minors' prefix — are **dropped**, which is sound for a forward simulation and is what MetaRocq's own expansion does. The head is `ElimHeadOf`: `.const kn` pre-δ, or an `ElimBody` shape post-δ, the disjunct `lower_correct`'s δ case needs for its intermediate configurations. **Deviation:** the arm carries `LowerAlts`' three conjuncts inlined (`hmlen`, `halen`, `hmin`), because `LowerAlts` is defined after the mutual block and cannot occur in it; `Lower.elimApp'` is the packaged form |
| `elimEta` | an under-applied eliminator → `mkLambdas ns body` | `none` | `visitCasesEtaGo` (`LeanToLambdaBox/Erasure.lean:705-712`). `hns : ns ≠ []` and `hund` pin the under-application; the premise is `Lower` on the *saturated* spine — the lowered prefix shifted under the new binders, then `bvarsDesc ns.length` — so the case node the eraser builds is whatever `elimApp` builds for that spine, and the arm does not duplicate `elimApp`'s data |

Branch peeling is a separate relation: `LowerAlt Γ nf m alt` turns a minor's λ-chain into an
alternative's binder list — arm `done` at arity zero, arm `lam` peeling one binder — and
`LowerAlts` is its pointwise lift over the block's field arities. Only the *number* of
binders is pinned, because that is all `iota_red` reads.

## Recursion (2) — `fixSubst`

| Arm | Relates | Counterpart | Anchor and deviation |
|---|---|---|---|
| `fixConst` | `.const kn` to `.fix defs j`, for `kn` the block's *j*-th member | `fixSubst` | The call site: `visitMutual` registers each member as the whole block's `.fix` node (`LeanToLambdaBox/Erasure.lean:904-918`) |
| `fixBody` | the member's specification body to the same `.fix defs j` | `fixSubst` | The value side, and the arm the δ step needs: after the specification environment unfolds `kn`, the source configuration is the plain body while the target is the `.fix`. Its absence is what makes a functional pass, and a one-sided fix relation, false |

Both arms read their premises through `LowerBlock` (the fields are inlined into each arm:
the kernel rejects the structure as a nested premise; `Lower.fixConst'` and `Lower.fixBody'`
are the packaged forms). Two fields answer machine-checked refutations:

* `hrarg : ∀ d ∈ defs, d.principalArgIdx = 0`. Without it the correctness statement is
  false — at `principalArgIdx = 1` the source evaluates to `□` while the target is a stuck
  spine. It is a fact about the emitter: `mkDef` never sets the field and the default is `0`
  (`LeanToLambdaBox/Basic.lean:67`), whose comment "this doesn't matter computationally" is
  false under this `WcbvEval`; `FixUnfoldChain` already carries the same premise
  (`LeanToLambdaBox/FixUnfold.lean:803`).
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
already related by `app` and `construct`) and no `DefnDeclFix` premise on `const`.

## The fixpoint closure — `Lower.lean` and `LowerFix`

`ConstToFVar` and `CloseConstAt` are defined in `LeanToLambdaBox/Lower.lean`: `LowerBlock`'s
`hcl` field mentions `CloseConstAt`, and the two fix arms inline that field, so they precede
`Lower` itself. `LowerFix.lean` holds the rest of the closure, and repairs two statements of
`01-DESIGN.md` that are false as written; its two fixture theorems are the refutations.

| Object | What it is | Anchor |
|---|---|---|
| `ConstToFVar kns ids` | replaces `.const kns[j]` by `.fvar ids[j]`; a `.fix` node maps to itself — no block member is declared as a `.fix`, and a nested one belongs to another block, whose members are none of `kns` | the λ□-only residue of the retired source-indexed fix-variable rule |
| `CloseConstAt kns ids t u` | `∃ t', ConstToFVar kns ids t t' ∧ u = closeFix ids 0 t'` | phrased through the existing `closeFix` so `closeFix_substList_fixSubst` applies verbatim and no `Kername`-keyed twin of `FixUnfold`'s theorems is needed |
| `Lower.constToFix` | a fix unfolding (`WcbvEval.fix_guarded`'s `substList (fixSubst defs)`) puts `.fix defs i` where the lowered body has the sibling `.const knᵢ`; the result is still `Lower`-related to the same body | `fixSubst`; the transport that makes the fix arms usable. **Deviation:** it takes `hfv` — the fixvars do not already occur in `t` — in place of the design's inert `LBClosed t 0`, which `LowerFixFixture.constToFix_needs_freshness` refutes; at the call site `hfv` is `LowerBlock.hfresh` |
| `LowerBlock.lambda_of_fixLambda` | λ-headedness of the emitted `defs` transported to the specification bodies | **Deviation:** it takes `hη` — no member body is an under-applied constructor or eliminator spine (`EtaSpine`) — which `LowerFixFixture.lambda_of_fixLambda_needs_noEta` shows is required, since the two η arms turn a spine into a lambda. `LowerBlock.targetLambda_of_fixLambda` is the unconditional half |
| `LowerFix Γ kns bs defs` | `∃ bs' ids, LowerBlock …`, the declaration-level statement for `LowerEnv` | tolerates an unused fix binder: `visitMutual` decides recursiveness by `name_occurs` on the **source** body (`LeanToLambdaBox/Erasure.lean:885`), so erasure can remove the only self-reference and leave the binder unused |
| `ErasesLBFix` | `∃ t₀ t₁, Erases … t₀ ∧ Lower Γ t₀ t₁ ∧ ConstToFVar kns ids t₁ t` | the block-body motive: inside `visitMutual`'s block branch the eraser rewrites a source `.const` to `.fvar id` (`visitConst`, `LeanToLambdaBox/Erasure.lean:660-664`), a pair no two-factor composite can state |

## Against `optimize`

`optimize` (`[S §7.4]`, `LeanToLambdaBox/Optimize.lean`) is the tree's worked example of a
verified λ□ → λ□ pass, and `Lower` is stated in its shape: a relation between two λ□ terms
over one environment, with a simulation theorem and a non-vacuity guard per arm. The
differences are named, not silent: `optimize` is a function and `Lower` is a relation,
because the eraser's constructor and `casesOn` handling is not a function of the λ□ term
alone; and `optimize` preserves the environment, whereas `Lower`'s redex arms read it
(`CtorDecl`, `ElimDecl`, `DefnDecl`).

## What `Lower.lean` proves about the relation

`ClosedBodies Γ` — every constant `Γ` declares has a closed body — is the one environment-side
premise these carry; it is a fact about the specification environment (`LBWfSpec`'s second
conjunct, `LeanToLambdaBox/ErasesEnv.lean:275`), and the two fix arms need it: the source
side of `fixBody` is a declared body, and a block's emitted `.fix` is `closeFix` of one. Closedness of the two
eliminator shapes needs no premise at all — `ElimBody.closed` proves it in
`LeanToLambdaBox/ElimBody.lean`, which `Lower.lean` imports.

| Theorem | Statement | Used for |
|---|---|---|
| `Lower.closed` | `ClosedBodies Γ → Lower Γ s t → ∀ k, LBClosed s k → LBClosed t k` | the pass invents no index; feeds the two commutation laws |
| `Lower.shift_comm` | `ClosedBodies Γ → Lower Γ s t → ∀ d c, Lower Γ (shift d c s) (shift d c t)` | the `ctorEta`/`elimEta` arms of a simulation, and `subst_comm`'s `bvar` case |
| `Lower.subst_comm` | `ClosedBodies Γ → Lower Γ a a' → Lower Γ s t → ∀ d, Lower Γ (subst a d s) (subst a' d t)` | the β, ζ and ι steps of a forward simulation |
| `Lower.mkApps` | spine congruence from head and arguments | over-application, and the value side of a constructor spine |
| `Lower.target_box`/`_bvar`/`_fvar`/`_prim`/`_const`/`_construct`/`_fix` | what a target of that shape can come from | inversion at a value; `target_fix` returns the whole `LowerBlock` |
| `ElimHeadOf.shift_eq`/`.subst_eq` | an eliminator head is fixed by both operations | the two η arms of the commutation laws |
| `LowerAlt.arity` | `LowerAlt Γ nf m alt → alt.1.length = nf` | the binder count `iota_red` reads |
| `cstrArity_eq_of_constructorArity` | `constructorArity Γ iid k = some a → cstrArity Γ iid k = a` | reading `ctorApp.hsat` against `LBWfPeregrine.etaCtorsEnv`, which is keyed on `constructorArity` |

`#print axioms Lower` is `[propext]`; the two commutation laws add `Quot.sound` through the
`List` lemmas their indexed premises go by.
