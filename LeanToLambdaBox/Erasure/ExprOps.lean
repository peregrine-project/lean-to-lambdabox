import Lean

/-!
# Structural counterparts of cached or `@[extern]` operations on `Expr` and `Level`

Lean's `Level.hasMVar` reads a field cached in the level's data. The definition here computes the
same answer by structural recursion, so that it unfolds in proofs and in kernel reduction.

The definitions are copied from lean4lean (`https://github.com/digama0/lean4lean`, commit
`8223d223ed98661882e95d9d6a7126df7097cd76`, file `Lean4Lean/Verify/Axioms.lean`), which is
distributed under the Apache License 2.0.
-/

namespace Lean.Level

/-- Whether the level contains a universe metavariable, by structural recursion. Copied from
lean4lean `Lean4Lean/Verify/Axioms.lean:281` (`Lean.Level.hasMVar'`). -/
def hasMVar' : Level → Bool
  | .mvar .. => true
  | .zero | .param .. => false
  | .succ l => l.hasMVar'
  | .max l₁ l₂ | .imax l₁ l₂ => l₁.hasMVar' || l₂.hasMVar'

end Lean.Level
