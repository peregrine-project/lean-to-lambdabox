import Lean

/-!
# Structural counterparts of cached or `@[extern]` operations on `Expr` and `Level`

Lean's `Level.hasMVar` reads a field cached in the level's data, and `Expr.liftLooseBVars` and
`Expr.instantiate1` are `@[extern]` functions implemented in C++. The definitions here compute
the same results by structural recursion, so that they unfold in proofs and in kernel reduction.

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

namespace Lean.Expr

/-- Add `d` to every loose bound variable of index at least `s`, by structural recursion. Copied
from lean4lean `Lean4Lean/Verify/Axioms.lean:365` (`Lean.Expr.liftLooseBVars'`). -/
def liftLooseBVars' (e : @& Expr) (s d : @& Nat) : Expr :=
  match e with
  | .bvar i => .bvar (if i < s then i else i + d)
  | .mdata m e => .mdata m (liftLooseBVars' e s d)
  | .proj n i e => .proj n i (liftLooseBVars' e s d)
  | .app f a => .app (liftLooseBVars' f s d) (liftLooseBVars' a s d)
  | .lam n t b bi => .lam n (liftLooseBVars' t s d) (liftLooseBVars' b (s+1) d) bi
  | .forallE n t b bi => .forallE n (liftLooseBVars' t s d) (liftLooseBVars' b (s+1) d) bi
  | .letE n t v b bi =>
    .letE n (liftLooseBVars' t s d) (liftLooseBVars' v s d) (liftLooseBVars' b (s+1) d) bi
  | e@(.const ..)
  | e@(.sort _)
  | e@(.fvar _)
  | e@(.mvar _)
  | e@(.lit _) => e

/-- Substitute `subst` for the loose bound variable `d` (lifted by `d`) and lower the loose bound
variables above it, by structural recursion. Copied from lean4lean
`Lean4Lean/Verify/Axioms.lean:404` (`Lean.Expr.instantiate1'`). -/
def instantiate1' (e : Expr) (subst : Expr) (d := 0) : Expr :=
  match e with
  | .bvar i => if i < d then e else if i = d then subst.liftLooseBVars' 0 d else .bvar (i - 1)
  | .mdata m e => .mdata m (instantiate1' e subst d)
  | .proj s i e => .proj s i (instantiate1' e subst d)
  | .app f a => .app (instantiate1' f subst d) (instantiate1' a subst d)
  | .lam n t b bi => .lam n (instantiate1' t subst d) (instantiate1' b subst (d+1)) bi
  | .forallE n t b bi => .forallE n (instantiate1' t subst d) (instantiate1' b subst (d+1)) bi
  | .letE n t v b bi =>
    .letE n (instantiate1' t subst d) (instantiate1' v subst d) (instantiate1' b subst (d+1)) bi
  | .const ..
  | .sort _
  | .fvar _
  | .mvar _
  | .lit _ => e

end Lean.Expr
