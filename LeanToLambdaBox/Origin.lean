import LeanToLambdaBox.Upstream

/-!
# The origin corollaries, conditional on the upstream ask

`Erases` reads `Expr.const` three ways — a constructor (`CtorOf`), an inductive type name
(`IndInfo`), a plain constant (`ConstOrigin`) — and each reading exhibits a declaration list of
`VEnv.WF'` below `env`. Introduction sites need only the positive reading they already have. The
*exclusion* and *uniqueness* directions are a fact about `VEnv.WF'` and not about erasure, filed
as `doc/upstream-asks.md` item 2; until the pin moves they are the `constsOrigin` field of
`UpstreamAsks`, and this module unpacks that field into the six named facts the tree consumes.

Every declaration here therefore takes `(A : UpstreamAsks env)` explicitly. Once the fork holds
`VEnv.WF'.consts_origin` the binder is discharged by the pin bump and no statement below changes
shape.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

variable {env : VEnv} {c I I' : Name} {k k' dp nm dp' nm' np np' : Nat}
  {iid iid' : InductiveId} {nfs nfs' : List Nat}

/-- A name declared as a plain constant is not a constructor. -/
theorem constOrigin_not_ctorOf (A : UpstreamAsks env) (h : ConstOrigin env c) :
    ∀ I k, ¬ CtorOf env c I k :=
  (A.constsOrigin.2.2.2.2.2 c h).1

/-- A name declared as a plain constant is not an inductive type name. -/
theorem constOrigin_not_indInfo (A : UpstreamAsks env) (h : ConstOrigin env c) :
    ∀ iid np nfs, ¬ IndInfo env c iid np nfs :=
  (A.constsOrigin.2.2.2.2.2 c h).2

/-- The block declaring a given type former is unique, so its λ□ coordinates are. -/
theorem IndInfo.inj (A : UpstreamAsks env) (h : IndInfo env I iid np nfs)
    (h' : IndInfo env I iid' np' nfs') : iid = iid' ∧ np = np' ∧ nfs = nfs' :=
  A.constsOrigin.2.2.1 I iid np nfs iid' np' nfs' h h'

/-- A constructor belongs to one type at one index. -/
theorem CtorOf.inj (A : UpstreamAsks env) (h : CtorOf env c I k) (h' : CtorOf env c I' k') :
    I = I' ∧ k = k' :=
  A.constsOrigin.2.1 c I k I' k' h h'

/-- The segmentation an eliminator's own block fixes is unique. -/
theorem CasesOnShape.inj (A : UpstreamAsks env) (h : CasesOnShape env c I dp nm)
    (h' : CasesOnShape env c I dp' nm') : dp = dp' ∧ nm = nm' :=
  A.constsOrigin.2.2.2.1 c I dp nm dp' nm' h h'

/-- Totality of the three readings: a declared constant is a constructor, an inductive type name
or a plain constant. This is `Erases.exists_of_trExprS_of_projInfo`'s `hclass`. -/
theorem consts_classified (A : UpstreamAsks env) (_hwf : env.WF) : ∀ c ci,
    env.constants c = some ci →
    (∃ I k, CtorOf env c I k) ∨ (∃ iid np nfs, IndInfo env c iid np nfs) ∨ ConstOrigin env c :=
  A.constsOrigin.2.2.2.2.1

end LeanToLambdaBox
