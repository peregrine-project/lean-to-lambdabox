import LeanToLambdaBox.SourceEval

/-!
# The load-bearing upstream asks, as one named premise

`doc/upstream-asks.md` files ten numbered items against the lean4lean fork this repository
pins, of which eight are asks. Four are consumed by Wave 3 theorems and cannot be discharged
here, because editing the fork is not this repository's work:

* item 2 (`VEnv.WF'.consts_origin`) — the field `constsOrigin`, unpacked by `Origin.lean`;
* item 6 (`VEnv.IsDefEqU.const_arity_inv`) — the field `constArityInv`, consumed by
  `not_erasable_of_informative`;
* item 9 (`HasType.mkApps_inv`) — the field `mkAppsInv`, home at or below
  `Theory/Typing/UniqueTyping.lean`, consumed by `indSpine_not_prop`, `elim_major`,
  `ctor_saturated` and `fOFields_of_asks`;
* item 10 (`IsDefEqU.indSpine_inj`) — the field `indSpineInj`, home
  `Theory/Typing/Injectivity.lean`, consumed by `ctor_saturated` and `fOFields_of_asks`.

This module packages exactly those four as one structure, so every consumer takes an identical,
auditable class-**C** premise instead of a private one, and so that the pin bump discharges all
of them at once.

`doc/trust.md` carries the row: what the four fields assume, which theorems take them, and the
discharge condition. The measured ledger cannot: `#print axioms` reports the footprint of a
proved term and never a hypothesis.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-- The block `decl` is declared by a well-formed declaration list **below** `env`. Every
consumer exhibits its block in this form — `IndInfo`, `IndArity`, `CtorOf` and `CasesOnShape`
each bound their declaration list by `env₀ ≤ env` rather than by `env` itself — so it is the
form ask 2's uniqueness conjunct is stated in. `FirstOrderInd`'s `HasInduct env decl` is the
special case `env₀ = env`. -/
def IndBlockBelow (env : VEnv) (decl : VInductDecl) : Prop :=
  ∃ (ds : List VDecl) (env₀ : VEnv), VEnv.WF' ds env₀ ∧ env₀ ≤ env ∧ VDecl.induct decl ∈ ds

/-- Peeling a spine's typing, argument by argument: the head's type is definitionally a Π
whose domain types the first argument, and the instantiated codomain peels the rest. -/
def Peel (env : VEnv) (U : Nat) (Γ : List VExpr) : VExpr → List VExpr → VExpr → Prop
  | T, [],      V => env.IsDefEqU U Γ T V
  | T, a :: as, V => ∃ A B, env.IsDefEqU U Γ T (.forallE A B) ∧ env.HasType U Γ a A ∧
                       Peel env U Γ (B.inst a) as V

/-- The four load-bearing upstream asks (`doc/upstream-asks.md` items 2, 6, 9, 10) this
development cannot discharge without the lean4lean fork changing, packaged as one structure so
every consumer takes an identical, auditable class-**C** premise instead of a private one. Ask 1
(`defeqOwn`) and ask 3 (the seven kernel-generic declarations) have no consumer here and are not
fields — they are `doc/upstream-asks.md`'s to track. Discharged by the pin bump: a value of this
structure is then built from the fork's own theorems with no change to any consumer's statement
shape — only the binder becomes derivable rather than assumed. -/
structure UpstreamAsks (env : VEnv) : Prop where
  /-- Ask 2 — the constants-keyed twin of `WF'.pats_origin`: a name declared as a plain constant
  in one `WF'` list below `env` is not a constructor and not an inductive type name in another,
  and the block declaring a given type former is unique. Stated as the corollaries and the
  totality direction this tree consumes, since ask 2's own upstream statement is not yet filed at
  the pin `Origin.lean` would need to restate it against. The first conjunct, `CtorOf → ¬
  IndInfo`, is redundant — `CtorOf.not_indInfo` proves it here — and is kept so the field grants
  everything ask 2 was filed for. The last two conjuncts are the declaration-level halves of the
  uniqueness the prose claims: a block below `env` that declares `I` is matched by a block of
  `env`'s own declaration list, and two blocks below `env` declaring `I` are the same block. -/
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
      (∀ I k, ¬ CtorOf env c I k) ∧ (∀ iid np nfs, ¬ IndInfo env c iid np nfs)) ∧
    (∀ I iid np nfs, IndInfo env I iid np nfs → IndDeclOf env I) ∧
    (∀ (I : Name) (decl decl' : VInductDecl), IndBlockBelow env decl → IndBlockBelow env decl' →
      (∃ t ∈ decl.types, t.name = I) → (∃ t ∈ decl'.types, t.name = I) → decl = decl')
  /-- Ask 6, `doc/upstream-asks.md`'s statement with its ambient environment read off this
  structure's parameter — an application headed by an inductive type former is definitionally
  equal to neither a sort nor a Π. -/
  constArityInv : ∀ {ds U Γ} (_henv : env.WF' ds) (_hΓ : OnCtx Γ (env.IsType U))
    {decl : VInductDecl} {t : VInductiveType} {us : List VLevel} {args : List VExpr}
    (_hdecl : VDecl.induct decl ∈ ds) (_htype : t ∈ decl.types)
    (_hty : ∃ V, env.HasType U Γ (VExpr.mkApps (.const t.name us) args) V),
    (∀ u, ¬ env.IsDefEqU U Γ (VExpr.mkApps (.const t.name us) args) (.sort u)) ∧
    (∀ A B, ¬ env.IsDefEqU U Γ (VExpr.mkApps (.const t.name us) args) (.forallE A B))
  /-- Ask 9 — spine typing inversion, with `OrderedStrong` explicit so that the ask is
  `sorryAx`-free exactly as `HasType.app_inv` is. -/
  mkAppsInv : ∀ {U Γ}, VEnv.OrderedStrong env → OnCtx Γ (env.IsType U) →
    ∀ (args : List VExpr) {f V}, env.HasType U Γ (VExpr.mkApps f args) V →
    ∃ T, env.HasType U Γ f T ∧ Peel env U Γ T args V
  /-- Ask 10 — two definitionally equal spines headed by **inductively declared** type formers
  have the same head. The `IndDeclOf` premises are load-bearing: without them a `VDecl.def`
  refutes the statement. -/
  indSpineInj : ∀ {U Γ} {I J : Name} {us vs : List VLevel} {iargs jargs : List VExpr},
    OnCtx Γ (env.IsType U) → IndDeclOf env I → IndDeclOf env J →
    env.IsDefEqU U Γ (VExpr.mkApps (.const I us) iargs) (VExpr.mkApps (.const J vs) jargs) →
    I = J

end LeanToLambdaBox
