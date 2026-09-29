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

The blueprint renders this register.

## Entries

The register has no entries: the library `EraseProof` (`proof/`) has no declarations.
