# Divergence register

This register lists every place where the verification code on the `ml/verification` branch
(`proof/`, library `EraseProof`), or the statements it proves, diverge from the references —
Letouzey, "A New Extraction for Coq" (TYPES 2002), and Sozeau et al., "Correct and Complete Type
Checking and Certified Erasure for Coq, in Coq" (J. ACM 2025), including its MetaRocq sources at
commit `4b201296` (branch 9.1). The verification follows these references as closely as the
differences between Lean's kernel, as Metalean (`github.com/intgrah/metalean`, commit `9407ba4`)
models it, and Rocq/PCUIC/MetaRocq allow; every place it does not, for any reason, is recorded
here. Entries land with the artifact that diverges.

Each entry has an id `DV-<n>` and exactly these fields:

- **Our artifact:** file and declaration on the `ml/verification` branch that carries the
  divergence.
- **Reference artifact:** the paper section/figure/theorem and the MetaRocq `file:identifier` it
  corresponds to.
- **What differs:** the concrete difference between our artifact and the reference artifact.
- **Why it is forced:** the concrete reason the divergence is necessary — a difference between
  Lean's kernel and CIC, a gap in what Metalean provides, a scope boundary of the verified
  fragment, or similar. This field must name a real constraint; "it was simpler" or "we chose to"
  is not a forcing reason.
- **What was considered instead:** the alternative(s) that would have kept the divergence from
  existing, and why each was rejected.

An entry without a forcing reason is a defect, not a divergence: it must be removed and the
statement or definition restated to match the reference instead. Differences of representation
alone (a judgment in `Prop` where MetaRocq's lives in `Type`, explicit flags, bundled helpers) get
no entry.

## Entries
