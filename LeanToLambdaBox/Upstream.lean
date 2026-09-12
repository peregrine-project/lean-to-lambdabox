import LeanToLambdaBox.SourceEval

/-!
# The load-bearing upstream asks, as one named premise

`doc/upstream-asks.md` files six asks against the lean4lean fork this repository pins. Two of
them — item 2 (`VEnv.WF'.consts_origin`) and item 6 (`VEnv.IsDefEqU.const_arity_inv`) — are
consumed by Wave 3 theorems and cannot be discharged here, because editing the fork is not this
repository's work. This module packages exactly those two as one structure, so every consumer
takes an identical, auditable class-**C** premise instead of a private one, and so that the pin
bump discharges all of them at once.

`doc/trust.md` carries the row: what the two fields assume, which theorems take them, and the
discharge condition. The measured ledger cannot: `#print axioms` reports the footprint of a
proved term and never a hypothesis.

`LeanToLambdaBox/Origin.lean` unpacks `constsOrigin` into the five corollaries and the totality
direction this tree consumes; `constArityInv` is consumed by `not_erasable_of_informative`.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-- The two load-bearing upstream asks (`doc/upstream-asks.md` items 2, 6) this development
cannot discharge without the lean4lean fork changing, packaged as one structure so every
consumer takes an identical, auditable class-**C** premise instead of a private one. Ask 1
(`defeqOwn`) and ask 3 (the seven kernel-generic declarations) have no consumer here and are not
fields — they are `doc/upstream-asks.md`'s to track. Discharged by the pin bump: a value of this
structure is then built from the fork's own `Lean4Lean.VEnv.WF'.consts_origin` and
`Lean4Lean.VEnv.IsDefEqU.const_arity_inv` with no change to any consumer's statement shape — only
the binder becomes derivable rather than assumed. -/
structure UpstreamAsks (env : VEnv) : Prop where
  /-- Ask 2 — the constants-keyed twin of `WF'.pats_origin`: a name declared as a plain constant
  in one `WF'` list below `env` is not a constructor and not an inductive type name in another,
  and the block declaring a given type former is unique. Stated as the corollaries and the
  totality direction this tree consumes, since ask 2's own upstream statement is not yet filed at
  the pin `Origin.lean` would need to restate it against. The last conjunct is the exclusion the
  prose names; the first, `CtorOf → ¬ IndInfo`, is redundant — `CtorOf.not_indInfo` proves it
  here — and is kept so the field grants everything ask 2 was filed for. -/
  constsOrigin :
    (∀ c I k, CtorOf env c I k → ∀ iid np nfs, ¬ IndInfo env c iid np nfs) ∧
    (∀ c I k I' k', CtorOf env c I k → CtorOf env c I' k' → I = I' ∧ k = k') ∧
    (∀ I iid np nfs iid' np' nfs', IndInfo env I iid np nfs → IndInfo env I iid' np' nfs' →
      iid = iid' ∧ np = np' ∧ nfs = nfs') ∧
    (∀ c I dp nm dp' nm', CasesOnShape env c I dp nm → CasesOnShape env c I dp' nm' →
      dp = dp' ∧ nm = nm') ∧
    (∀ c ci, env.constants c = some ci →
      (∃ I k, CtorOf env c I k) ∨ (∃ iid np nfs, IndInfo env c iid np nfs) ∨
      ConstOrigin env c) ∧
    (∀ c, ConstOrigin env c →
      (∀ I k, ¬ CtorOf env c I k) ∧ (∀ iid np nfs, ¬ IndInfo env c iid np nfs))
  /-- Ask 6, `doc/upstream-asks.md`'s statement with its ambient environment read off this
  structure's parameter — an application headed by an inductive type former is definitionally
  equal to neither a sort nor a Π. -/
  constArityInv : ∀ {ds U Γ} (_henv : env.WF' ds) (_hΓ : OnCtx Γ (env.IsType U))
    {decl : VInductDecl} {t : VInductiveType} {us : List VLevel} {args : List VExpr}
    (_hdecl : VDecl.induct decl ∈ ds) (_htype : t ∈ decl.types)
    (_hty : ∃ V, env.HasType U Γ (VExpr.mkApps (.const t.name us) args) V),
    (∀ u, ¬ env.IsDefEqU U Γ (VExpr.mkApps (.const t.name us) args) (.sort u)) ∧
    (∀ A B, ¬ env.IsDefEqU U Γ (VExpr.mkApps (.const t.name us) args) (.forallE A B))

end LeanToLambdaBox
