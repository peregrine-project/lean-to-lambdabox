# Upstream asks

What this development needs from, or has found in, the projects it sits on: lean4lean
(the fork this repository pins), MetaRocq, and peregrine. Items 1-5 are **asks**: lemmas or
fixes whose natural home is upstream, either because they are kernel-generic — a fact about
`VEnv`/`VExpr`/`HasType`/`IsDefEq`/`TrExprS` and not about erasure — or because the defect
is upstream's. Item 6 is **reported, not asked**: findings about consumers this repository
does not depend on fixing.

Paths under `.lake/packages/lean4lean/Lean4Lean/` are given relative to that directory.

## Asks — lean4lean

1. **`VEnv.WF'.defeqOwn`** — a `WF'` environment grants each constant at most one defining
   equation: the `defeqs` twin of `WF'.pats_origin` (`Theory/Typing/InductiveParams.lean:93`).
   This is the fact that settled whether the δ layer needs a second environment of compiler
   bodies, and the answer was no. The proof is written (about 130 lines, no frontend
   dependency; it was produced as a design-gate probe, `doc/rework/01-DESIGN.md` §8.3) and it
   belongs upstream, not here.

2. **`VEnv.WF'.consts_origin`**, the constants-keyed twin of `WF'.pats_origin`, together with
   a generic `iotaRHS'` — the missing link in the `largeElim_of_wf` argument. Filed now; it
   becomes load-bearing only after `F-PROP` lands, since until then no emitted inductive is
   propositional and the singleton machinery has no subject.

3. **The seven kernel-generic declarations in `LeanToLambdaBox/CheckerAdequacy.lean`** —
   `VContext.ofMLCtx` with its three `@[simp]` projections, `VState.WF.initial`, `M.WF.run'`,
   and `kernelNGen`. They are about the checker, not about erasure; this repository's
   acceptance criteria forbid a `Lean4Lean`-namespace declaration here, and the oracle
   discharge needs them. They move to the fork with the pin bump (U3.1).

4. **A `TrEnv'` inversion on the `induct`/`AddInduct` clause** yielding
   `InductiveVal ↔ VInductDecl`, in the shape of `TrEnv.structure_rec`
   (`Verify/Environment/Lemmas.lean:644`) and `TrEnv'.pats_iota'` (`:674`). It would turn the
   `ind_adequate` field of this development's specification bundle from an assumed field into
   a theorem. Related and larger: the `inductDecl` case of `addDecl.WF`
   (`Verify/Environment.lean:208`) is `sorry` at the pinned revision — the lemma that would
   let the environment connection itself be derived rather than assumed.

5. **The `Quot.ind` divergence** between the theory (`Theory/Quot.lean:11` and its
   neighbours) and the executable checker.

## Reported, not asked

6. Three findings about downstream consumers, recorded because theorems here are stated
   against them:

   * **MetaRocq's shipped `firstorder_ind` is `false` on `nat`.** The sort conjunct of
     `PCUICFirstorder.v:59` is not in `[S §7.3]`'s prose; it makes every theorem guarded by
     the predicate vacuously guarded. Reproduced three ways by `vm_compute`. This repository
     therefore cites the code as the origin of its own `FirstOrderInd` and does **not**
     transcribe it, and says so in `doc/rules-Erases.md`'s posture and in `doc/trust.md`.
   * **peregrine's `run_untyped_transforms` precondition obligation is `Admitted`**
     (`Transforms.v:375`), so the pass that consumes this frontend's output carries no proof
     of the precondition it requires.
   * **`peregrine validate` is `parse_ast ;; get_config ;; check_wf` only**
     (`Pipeline.v:245-248`, `CheckWf.v:182-183`) — no expandedness check. That is what makes
     `F-ETA` undetectable downstream, and why an `.ast` produced by a panicking run still
     validates (`doc/panics.md`).
