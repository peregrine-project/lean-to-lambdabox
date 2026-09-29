# Divergence register

This register lists every place where the verification code, or the statements it proves, diverge
from the references of spec §3.1–§3.2 — Letouzey, "A New Extraction for Coq" (§3.1), and Sozeau et
al., "Correct and Complete Type Checking and Certified Erasure for Coq, in Coq" (§3.2), including
its MetaRocq sources. The verification effort follows these references as closely as the
differences between Lean's kernel/`lean4lean`'s model and Rocq/PCUIC/MetaRocq allow; every place it
does not, for any reason, is recorded here.

Each entry has an id `DV-<n>` and exactly these fields:

- **Our artifact:** file and declaration on the `verification` branch that carries the divergence.
- **Reference artifact:** the paper section/figure/theorem (§3.1 or §3.2) and the MetaRocq
  `file:identifier` it corresponds to.
- **What differs:** the concrete difference between our artifact and the reference artifact.
- **Why it is forced:** the concrete reason the divergence is necessary — a difference between
  Lean's kernel and CIC, a gap in what `lean4lean` `master` provides, a scope boundary from §2 of
  the spec, or similar. This field must name a real constraint; "it was simpler" or "we chose to"
  is not a forcing reason.
- **What was considered instead:** the alternative(s) that would have kept the divergence from
  existing, and why each was rejected.

An entry without a forcing reason is a defect, not a divergence: it must be removed and the
statement or definition restated to match the reference instead.

Entries are headed `### DV-<n>`. They cite declarations by full name in backquotes (ours as
`EraseProof.<name>`, lean4lean's as `Lean4Lean.<name>`), our files by their path in the repository
(`proof/...`), lean4lean `master` sources by path and line (`Lean4Lean/...lean:<line>`), and
MetaRocq sources by path relative to the MetaRocq repository and line. Check C9 of
`proof/scripts/check.sh` fails if a cited `EraseProof.*` or `Lean4Lean.*` name is not a
declaration, a cited file or line does not exist, an entry's fields differ from the list above, or
an entry's artifact field cites no declaration of `EraseProof`.

The blueprint renders this register.

## Entries

### DV-2

- **Our artifact:** `proof/EraseProof/Typing/Basic.lean`, `EraseProof.TrS`, the translation of
  Lean terms into lean4lean's model.
- **Reference artifact:** MetaRocq's translation of Template terms into PCUIC terms, `trans`
  (`template-pcuic/theories/TemplateToPCUIC.v:63`; the MetaCoq paper's "certified type-preserving
  translation from Coq's syntax to PCUIC's syntax", §9), which erasure (§7) consumes; the
  translation `EraseProof.TrS` follows is lean4lean's `Lean4Lean.TrExprS`
  (`Lean4Lean/Verify/Typing/Expr.lean:75`).
- **What differs:** `EraseProof.TrS` has the rules of `Lean4Lean.TrExprS` except `lit` and `proj`:
  literals (`Expr.lit`) and projections (`Expr.proj`) have no translation, so terms containing
  them are outside the fragment. Like `Lean4Lean.TrExprS` and unlike `trans`, it is a relation
  (its image is unique: `EraseProof.TrS.det`).
- **Why it is forced:** the lemmas of `Lean4Lean.TrExprS` handle `proj` with `sorry` proofs
  (`Lean4Lean/Verify/Typing/Lemmas.lean:642,723,727,893,938,1240,1509`); reusing them puts
  projection sorries into a fragment without projections. The `lit` rule translates a literal
  through constructors of `Nat` and `String` (`Lean4Lean.VEnv.ContainsLits`,
  `Lean4Lean/Verify/Typing/Expr.lean:70`), which are inductive types, absent from the model (DV-6).
  Secondarily, projections are translated through `Lean4Lean.TrProj`, a `sorry` definition
  (`Lean4Lean/Verify/Typing/Expr.lean:68`), which every hypothesis stated with
  `Lean4Lean.TrExprS` would mention.
- **What was considered instead:** `Lean4Lean.TrExprS` with a side condition excluding
  projections and literals: the hypotheses would still mention `Lean4Lean.TrProj`, and its lemmas
  would reach the `sorry` proofs of the `proj` cases.

### DV-5

- **Our artifact:** `proof/EraseProof/Typing/Basic.lean`: all typing in `EraseProof` is
  lean4lean's typing judgment `Lean4Lean.VEnv.IsDefEq` (through `Lean4Lean.VEnv.HasType`,
  `Lean4Lean.VEnv.IsType`, `Lean4Lean.VExpr.WF`), as in the premises of `EraseProof.TrS` and the
  conclusion of `EraseProof.TrS.wf`.
- **Reference artifact:** PCUIC typing, MetaCoq paper §3.3 (cumulativity) and §3.5 (typing,
  Fig. 21), MetaRocq `pcuic/theories/PCUICTyping.v:198` `typing` with `type_Cumul` (`:294`), on
  which erasure (§7) is stated; Letouzey §3.1 (CIC).
- **What differs:** the judgment has definitional proof irrelevance (`proofIrrel`,
  `Lean4Lean/Theory/Typing/Basic.lean:51`) and η for functions (`eta`, `:48`; PCUIC has no η,
  MetaCoq paper §2.4); it has no cumulativity (conversion only, `defeqDF`, `:44`); levels have
  the operator `imax` (`Lean4Lean/Theory/VLevel.lean:12`), in which the sort of a Π-type is
  stated (`forallEDF`, `Lean4Lean/Theory/Typing/Basic.lean:40`), and are compared up to evaluation
  (`Lean4Lean.VLevel.Equiv`, `Lean4Lean/Theory/VLevel.lean:58`, in `sortDF`,
  `Lean4Lean/Theory/Typing/Basic.lean:22`).
- **Why it is forced:** the eraser's inputs are Lean terms, typed by Lean's kernel; the spec (§2)
  requires lean4lean `master` as the model of that kernel, and it models Lean's theory, not PCUIC.
- **What was considered instead:** none: PCUIC typing does not type Lean terms (it has
  cumulativity, and neither definitional proof irrelevance nor `imax`), so no judgment closer to
  the reference types the eraser's inputs.

### DV-6

- **Our artifact:** the fragment: the source terms `EraseProof.TrS` translates
  (`proof/EraseProof/Typing/Basic.lean`).
- **Reference artifact:** MetaRocq's erasure relation `erases` in full
  (`erasure/theories/Extract.v:88`; MetaCoq paper §7.3, Fig. 18), with its rules
  `erases_tConstruct` (`:106`), `erases_tCase` (`:109`), `erases_tProj` (`:118`), `erases_tFix`
  (`:122`), `erases_tCoFix` (`:129`), `erases_tPrim` (`:137`), and PCUIC's weak call-by-value
  evaluation `eval` (`pcuic/theories/PCUICWcbvEval.v:231`) with its ι-rules; Letouzey Def. 3 (all
  cases of 𝓔, fixpoints) and Def. 8 (ι).
- **What differs:** no constructors, case analysis, projections, source fixpoints, cofixpoints,
  primitive values or evars, and no ι-reduction: `EraseProof.TrS` has no rule for `Expr.proj`,
  `Expr.lit` or `Expr.mvar`, and Lean's `Expr` has no node for constructors, case analysis,
  fixpoints or cofixpoints (in Lean these are constants of inductive declarations, which
  `EraseProof.TrS` translates only as constants of the model's environment).
- **Why it is forced:** lean4lean `master` has no inductive types: `Lean4Lean.VInductDecl.WF` and
  `Lean4Lean.VEnv.addInduct` are `sorry` definitions (`Lean4Lean/Theory/Inductive.lean:5,7`), so
  the model has no constructors, recursors or ι-reduction; projections are translated through the
  `sorry` definition `Lean4Lean.TrProj` (`Lean4Lean/Verify/Typing/Expr.lean:68`); literals are
  values of the inductive types `Nat` and `String` (DV-2); the kernel's terms have no
  metavariables.
- **What was considered instead:** axiomatized inductive types (types, constructors and recursors
  as constants, ι as definitional equalities) in an ordered environment: the rule
  `Lean4Lean.VEnv.Ordered.defeq` (`Lean4Lean/Theory/Typing/Lemmas.lean:258`) admits any
  well-typed definitional equality, such as `Sort 0 ≡ (Sort 0 → Sort 0)`, so the injectivity of
  Π-types that the simulation proof needs fails there; master proves that injectivity
  (`Lean4Lean.VEnv.IsDefEqU.forallE_inv`, `Lean4Lean/Theory/Typing/Injectivity.lean:23`) only
  under `Lean4Lean.VEnv.WF`, whose inductive part is the `sorry` definition above.
