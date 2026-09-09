import Lean4Lean.Verify.Environment.Lemmas
import Lean4Lean.Verify.Typing.Lemmas

/-!
# The ι pattern interface: matching a recursor redex and computing its reduct

The pinned `barabbs/lean4lean` ι fork models ι-reduction as a *schematic rule*:
`VEnv.pats` is a registry of `(Pattern, Pattern.RHS × Pattern.Check)` pairs and
`VEnv.IsDefEq.pat` (wrapped as `TrEnv.iota_defeq`) turns a registered rule, matched
against a well-typed redex, into a definitional equality. `VEnv.addRecRule`
registers, per recursor rule, the pattern `SimplePattern.iota` and the reduct
`SimplePattern.iotaRHS`.

Consuming that interface needed three things the fork did **not** provide. The
`6fd8a1d` re-pin brought two of them upstream — the fork adopted this file's
`matches_varN_const` essentially verbatim and factored the reduct calculation through
a new `iotaRHS'` — so what this file still provides is the composition and the
`TrExprS` side:

* **`matches_iota`** — the ι redex `Pattern.Matches` introduction, composing two
  upstream `Pattern.matches_varN_const`es through `Matches.app` into
  `(rec a₀ … a_{M-1}) (ctor b₀ … b_{N-1})`. `matches_varN_const` itself is
  **upstream's** now (`Theory/Typing/Pattern.lean`); the copy this file carried, and
  the `varN_pathOf` orientation lemmas and `range`-`pmap` plumbing that supported it,
  are deleted.
* **`iotaRHS_apply`** — the reduct *calculation*, now a restatement of upstream's
  `SimplePattern.iotaRHS'_apply` at `iotaRHS`'s telescope split. Applied to a matcher,
  `SimplePattern.iotaRHS` yields exactly
  `VExpr.mkApps (rhs.instL m1) (as.take (np+nm+nmin) ++ bs.drop cnp)`.
  The two slices are **not** symmetric and are the easiest thing in this development
  to get backwards: the rec-side holes are `range (np+nm+nmin)` over a spine of
  length `np+nm+nmin+nind`, i.e. a `take` that drops the **indices** (which sit
  *between* the minors and the major premise); the ctor-side holes are `range nf` at
  paths `cnp+j`, i.e. a `drop cnp` that keeps the **fields**. Getting either backwards
  silently produces a well-typed but wrong reduct, which is why `iotaRHS_apply` is
  stated with explicit `take`/`drop` and why the guard in `IotaDischarge.lean`
  exercises a shape with `np > 0` *and* `nind > 0` (with `np = nind = 0` both slices
  degenerate and a wrong convention still looks right).
  ⚠️ The ctor-side offset is the **constructor's** own `numParams` (`cnp`), not the
  recursor's `np`: `VRecRule` gained a `ctorParams` field at `6fd8a1d`, and the two
  differ for the auxiliary recursors of nested inductives.
* **`TrExprS.mkApps_inv`** — full spine inversion for `TrExprS`
  (`TrExprS_spine_head` in `SubjectReductionFull.lean` returns only the head).

On top of those, `PatsIotaSpec` names the fork's *strengthened* rule-lookup lemma —
discharged for any translated environment by `PatsIotaSpec.of_trEnv` — and
`iota_defeq_spine` is the payoff: on a translated exact-arity
recursor-applied-to-constructor redex, the ι rule **fires**.
-/

namespace Lean4Lean

open Lean

/-! ## `Matches` introduction for constant spines — **now upstream's**

`Pattern.matches_varN_const` (a `q.varN k` pattern matched against a `k`-ary constant
spine, with each hole pinned to `m2 (varN_pathOf k i h) = args[i]`) used to be *defined
here*, together with the two `varN_pathOf` orientation lemmas and the
`range`-`pmap` ↔ `take`/`drop` plumbing its proof and `iotaRHS_apply`'s needed. At
`6fd8a1d` upstream declared it under the **same qualified name**
(`Lean4Lean.Pattern.matches_varN_const`, `Theory/Typing/Pattern.lean`), adopting this
file's statement essentially verbatim — an "already declared" build error, not a type
error — so the copy and its support are deleted and the uses below resolve upstream.
Upstream's `SimplePattern.iotaRHS'_apply` subsumes the plumbing.

Also deleted with them: `Pattern.RHS.apply_foldl` (upstream ships
`Pattern.RHS.apply_foldl_var`) and the local snoc lemma for `VExpr.mkApps`, whose
upstream counterpart `VExpr.mkApps_concat` was itself removed at `6fd8a1d` when the
projection builders' lift/inst family was re-derived from `subst`. -/

/-- **The ι redex builder.** `(SimplePattern.iota r M c N).toPattern` matches exactly
`(r a₀ … a_{M-1}) (c b₀ … b_{N-1})`, at the *recursor's* level list (`Matches.app`
keeps only the left branch's levels — so `rhs.instL m1` below instantiates with the
recursor spine's universes, not the constructor's). -/
theorem Pattern.matches_iota {recName cName : Name} {ls ls' : List VLevel}
    (M N : Nat) (as bs : List VExpr) (has : as.length = M) (hbs : bs.length = N) :
    ∃ m2, ((SimplePattern.iota recName M cName N).toPattern).Matches
            (.app (VExpr.mkApps (.const recName ls) as) (VExpr.mkApps (.const cName ls') bs))
            ls m2 ∧
          (∀ i (h : i < M), m2 (.inl (Pattern.varN_pathOf M i h)) = as[i]'(has ▸ h)) ∧
          (∀ j (h : j < N), m2 (.inr (Pattern.varN_pathOf N j h)) = bs[j]'(hbs ▸ h)) := by
  obtain ⟨m2a, hma, hvala⟩ := Pattern.matches_varN_const (c := recName) (ls := ls) M as has
  obtain ⟨m2b, hmb, hvalb⟩ := Pattern.matches_varN_const (c := cName) (ls := ls') N bs hbs
  exact ⟨Sum.elim m2a m2b, hma.app hmb, hvala, hvalb⟩

/-! ## The reduct calculation -/

/-- **The registered ι reduct, computed.** Applying `SimplePattern.iotaRHS` to a
matcher gives the rule template (level-instantiated at the *recursor's* universes)
applied to

* the recursor spine's **parameters, motives and minors** — `as.take (np+nm+nmin)`,
  dropping the `nind` indices, which sit between the minors and the major premise;
* the constructor spine's **fields** — `bs.drop cnp`, dropping *the constructor's own*
  parameters,

in that order and *not* reversed. This is exactly `inductiveReduceRec`'s slicing and
exactly the argument list the source-side ι reduct
`(cargs.drop cnp).foldl Expr.app minors[cidx]` wants.

`cnp` is the **constructor's** `numParams`, which `VRecRule.ctorParams` records since
`6fd8a1d`; it coincides with the recursor's `np` for ordinary inductives and differs
for the auxiliary recursors of nested ones. `VEnv.addRecRule` keys the registered
pattern on `cnp + nfields`, so nothing here may read `np` on the constructor side.

Since `6fd8a1d` this is upstream's `SimplePattern.iotaRHS'_apply` read at `iotaRHS`'s
telescope split (`iotaRHS` is by definition `iotaRHS'` at `k := np+nm+nmin`), so the
`range`-`pmap` computation this file used to carry is gone. -/
theorem SimplePattern.iotaRHS_apply {r c : Name} {np nm nmin nind cnp nf : Nat}
    {rhs : VExpr} {hc : rhs.Closed} {m1 : List VLevel}
    {m2 : (SimplePattern.iota r (np+nm+nmin+nind) c (cnp+nf)).toPattern.Path → VExpr}
    {as bs : List VExpr}
    (has : as.length = np+nm+nmin+nind) (hbs : bs.length = cnp+nf)
    (hma : ∀ i (h : i < np+nm+nmin+nind),
      m2 (.inl (Pattern.varN_pathOf (np+nm+nmin+nind) i h)) = as[i]'(has ▸ h))
    (hmb : ∀ j (h : j < cnp+nf),
      m2 (.inr (Pattern.varN_pathOf (cnp+nf) j h)) = bs[j]'(hbs ▸ h)) :
    (SimplePattern.iotaRHS r c np nm nmin nind cnp nf rhs hc).apply m1 m2
      = VExpr.mkApps (rhs.instL m1) (as.take (np+nm+nmin) ++ bs.drop cnp) :=
  SimplePattern.iotaRHS'_apply r c (np+nm+nmin) nind cnp nf rhs hc m1 m2 has hbs hma hmb

/-! ## `TrExprS` spine inversion -/

/-- **Full spine inversion.** A translated application spine decomposes into a
translated head, translated arguments, and a `VExpr.mkApps`. (`TrExprS_spine_head`
in `SubjectReductionFull.lean` gives only the head.) -/
theorem TrExprS.mkApps_inv {env : VEnv} {Us : List Name} {Δ : VLCtx} :
    ∀ {args : List Expr} {head : Expr} {ve : VExpr},
      TrExprS env Us Δ (args.foldl Expr.app head) ve →
      ∃ hve args', TrExprS env Us Δ head hve ∧
        List.Forall₂ (TrExprS env Us Δ) args args' ∧ ve = VExpr.mkApps hve args'
  | [], _, _, htr => ⟨_, [], htr, .nil, rfl⟩
  | _ :: as, head, ve, htr => by
    obtain ⟨hve, args', htrHead, hall, rfl⟩ :=
      TrExprS.mkApps_inv (args := as) (head := .app head _) htr
    cases htrHead with
    | @app f' A B a' _ _ _ hTf hTa htrf htra =>
      exact ⟨f', a' :: args', htrf, .cons htra hall, rfl⟩

/-- A translated constant is a constant, at the translation of its level list. -/
theorem TrExprS.const_inv {env : VEnv} {Us : List Name} {Δ : VLCtx} {c us ve}
    (h : TrExprS env Us Δ (.const c us) ve) :
    ∃ us', us.mapM (VLevel.ofLevel Us) = some us' ∧ ve = .const c us' := by
  cases h with | const _ h2 _ => exact ⟨_, h2, rfl⟩

/-! ## `TrExprS` spine *construction* — via application generation

The converse of `mkApps_inv`. Building a `TrExprS.app` node needs its two `HasType`
fields, and for the ι *reduct* no app node of the input supplies them: the reduct
spine is not a subterm of the redex, and is well-typed only because the ι rule fired.

They are recovered by **application generation**,
`Lean4Lean.VEnv.HasType.app_inv` (`Theory/Typing/Strong.lean`), which is a proved
theorem at the current pin — `Strong.lean`'s `IsDefEq.strong` /
`IsDefEqStrong.hasType'` layering exists exactly for this. Its premises are
`env.OrderedStrong` and `OnCtx Γ (env.IsType U)`, i.e. `henv.orderedStrong` and
`hΔ.toCtx`, which every call site here already has. Its sorry-frontier is a *subset*
of the one `VEnv.IsDefEq.uniqU` already carries — and `uniqU` is called throughout the
committed development (including `trExprS_beta_step`) — so this costs no new
sorry-carrying declaration.

⚠️ At `6fd8a1d` the premise **strengthened** from `env.Ordered` to
`env.OrderedStrong` (`Ordered` + `OnTypes (EnvStrong env)` + `PatsStrongOn`): the ι
redesign restated ι subject reduction over well-formed *prefixes*, so the strong
developments now carry it as a field rather than re-deriving it. The two lemmas below
take `OrderedStrong` for the same reason. The route from `VEnv.WF` is
`VEnv.WF.orderedStrong`, which is where the single consolidated ι obligation
`VEnv.WF.patsStrong` enters — the same obligation `IsDefEq.strong` was already
carrying under 15 scattered markers, now named once. A bare `Ordered` no longer
suffices; there is a `CoeOut` the other way. -/

/-- Every prefix of a well-typed application spine is well-typed. -/
theorem VExpr.WF.mkApps_head {env : VEnv} (henv : env.OrderedStrong) {U : Nat}
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ (args : List VExpr) {f : VExpr},
      VExpr.WF env U Γ (VExpr.mkApps f args) → VExpr.WF env U Γ f
  | [], _, h => h
  | a :: as, f, h => by
    have h1 : VExpr.WF env U Γ (VExpr.mkApps (.app f a) as) := h
    obtain ⟨A, B, hf, _⟩ := (VExpr.WF.mkApps_head henv hΓ as h1).app_inv henv hΓ
    exact ⟨_, hf⟩

/-- **`TrExprS` for an application spine, from the spine's well-typedness.** Each
`TrExprS.app` node's `HasType` fields are recovered by application generation, so no
app node of the *input* has to supply them. Converse of `TrExprS.mkApps_inv`. -/
theorem TrExprS.mkApps {env : VEnv} (henv : env.OrderedStrong) {Us : List Name}
    {Δ : VLCtx} (hΓ : OnCtx Δ.toCtx (env.IsType Us.length))
    {args : List Expr} {args' : List VExpr}
    (hall : List.Forall₂ (TrExprS env Us Δ) args args') :
    ∀ {head : Expr} {hve : VExpr},
      TrExprS env Us Δ head hve →
      VExpr.WF env Us.length Δ.toCtx (VExpr.mkApps hve args') →
      TrExprS env Us Δ (args.foldl Expr.app head) (VExpr.mkApps hve args') := by
  induction hall with
  | nil => exact fun htr _ => htr
  | @cons a a' as as' hta hall ih =>
    intro head hve htr hwf
    have hwf' : VExpr.WF env Us.length Δ.toCtx (VExpr.mkApps (.app hve a') as') := hwf
    obtain ⟨A, B, hf, ha⟩ := (VExpr.WF.mkApps_head henv hΓ _ hwf').app_inv henv hΓ
    exact ih (.app hf ha htr hta) hwf

/-- The right endpoint of a definitional equality is well-typed. -/
theorem VEnv.IsDefEqU.wf_r {env : VEnv} {U Γ e1 e2}
    (h : env.IsDefEqU U Γ e1 e2) : VExpr.WF env U Γ e2 :=
  let ⟨_, h⟩ := h; ⟨_, h.symm.trans h⟩

/-- The left endpoint of a definitional equality is well-typed. -/
theorem VEnv.IsDefEqU.wf_l {env : VEnv} {U Γ e1 e2}
    (h : env.IsDefEqU U Γ e1 e2) : VExpr.WF env U Γ e1 :=
  let ⟨_, h⟩ := h; ⟨_, h.trans h.symm⟩

/-- **Replacing the head of a `VExpr` application spine by a definitionally equal
one.** The per-node `HasType` side conditions of `appDF` come from application
generation on the (well-typed) right-hand spine. -/
theorem VEnv.IsDefEqU.mkApps_congr_head {env : VEnv} (henv : env.WF) {U : Nat}
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ (args : List VExpr) {f g : VExpr},
      env.IsDefEqU U Γ f g → VExpr.WF env U Γ (VExpr.mkApps g args) →
      env.IsDefEqU U Γ (VExpr.mkApps f args) (VExpr.mkApps g args)
  | [], _, _, hd, _ => hd
  | a :: as, f, g, hd, hwf => by
    have hwf' : VExpr.WF env U Γ (VExpr.mkApps (.app g a) as) := hwf
    obtain ⟨A, B, hg, ha⟩ :=
      (VExpr.WF.mkApps_head henv.orderedStrong hΓ _ hwf').app_inv henv.orderedStrong hΓ
    have hfg : env.IsDefEq U Γ f g (.forallE A B) :=
      (VEnv.IsDefEqU.of_l henv hΓ hd.symm hg).symm
    have hstep : env.IsDefEqU U Γ (.app f a) (.app g a) := ⟨_, .appDF hfg ha⟩
    exact VEnv.IsDefEqU.mkApps_congr_head henv hΓ as hstep hwf'

/-! ## Transporting the fork-supplied rule template into the ambient context

`PatsIotaSpec` hands back `TrExprS venv rval.levelParams [] rule.rhs rhs` — the kernel
rule's template translated at the *declaration's own* level parameters and the *empty*
local context. The ι chain needs it at the redex's `Us`/`Δ`. `instL_weak` does both
moves: `TrExprS.instL` at `Δ = []` (whose `VLCtx.instL` is again `[]`), then `weak_nil`.

`weak_nil` is needed because lean4lean's `FVLift.from_nil` only reaches `NoBV`
contexts and `BVLift` only reaches all-`none` ones; a *mixed* `Δ` is reached by
peeling one entry at a time, using `BVLift.skip`/`FVLift.skip_fvar` at each step. Both
lifts are the identity here: the reduct is `Closed` (`ClosedN.liftN_eq`) and the
template has no loose bvars (`Expr.liftLooseBVars_eq_self`). -/

/-- A translation at the empty local context holds at any well-formed context, when
the source has no loose bvars and the target is closed. -/
theorem TrExprS.weak_nil {env : VEnv} (henv : env.Ordered) {Us : List Name}
    {e : Expr} {e' : VExpr} (hsrc : e.looseBVarRange' = 0) (hc : e'.Closed) :
    ∀ {Δ : VLCtx}, VLCtx.WF env Us.length Δ → TrExprS env Us [] e e' → TrExprS env Us Δ e e'
  | [], _, H => H
  | (none, d) :: Δ, hΔ, H => by
    have ih := TrExprS.weak_nil henv hsrc hc (Δ := Δ) hΔ.1 H
    have W : VLCtx.BVLift Δ ((none, d) :: Δ) (0+1) 0 (0+d.depth) 0 := .skip d .refl
    have h2 := TrExprS.weakBV henv W ih
    rwa [Expr.liftLooseBVars_eq_self (by omega), hc.liftN_eq (Nat.le_refl 0)] at h2
  | (some fv, d) :: Δ, hΔ, H => by
    have ih := TrExprS.weak_nil henv hsrc hc (Δ := Δ) hΔ.1 H
    have W : VLCtx.FVLift Δ ((some fv, d) :: Δ) 0 (0+d.depth) 0 := .skip_fvar fv d .refl
    have h2 := TrExprS.weakFV henv W hΔ ih
    rwa [hc.liftN_eq (Nat.le_refl 0)] at h2

/-- Level-instantiate a closed-context translation and transport it to `Δ`. The result
is only *definitionally equal* to `e'.instL ls'` — `TrExprS.instL` returns a `TrExpr`,
since level instantiation re-derives sort/const levels — which is why the caller
composes it with `IsDefEqU.mkApps_congr_head`. -/
theorem TrExprS.instL_weak {env : VEnv} (henv : env.WF) {Us ps : List Name}
    {ls : List Level} {ls' : List VLevel} {Δ : VLCtx}
    (hΔ : VLCtx.WF env Us.length Δ)
    (Hls : ls.mapM (VLevel.ofLevel Us) = some ls') (hlen : ps.length = ls.length)
    {e : Expr} {e' : VExpr}
    (hsrc : (e.instantiateLevelParams ps ls).looseBVarRange' = 0)
    (H : TrExprS env ps [] e e') :
    ∃ e₂, TrExprS env Us Δ (e.instantiateLevelParams ps ls) e₂ ∧
      env.IsDefEqU Us.length Δ.toCtx e₂ (e'.instL ls') := by
  obtain ⟨e₂, htr, hd⟩ := TrExprS.instL (Δ := []) henv trivial Hls hlen H
  have hwf : VExpr.WF env Us.length (VLCtx.toCtx []) e₂ := htr.wf henv.ordered (by trivial)
  have hc : e₂.Closed := hwf.closedN henv.ordered trivial
  exact ⟨e₂, TrExprS.weak_nil henv.ordered hsrc hc hΔ htr, hd.weak0 henv⟩

/-- `Forall₂` survives `take` (slices the recursor spine at `np + nmot + nmin`). -/
theorem forall2_take {α β} {R : α → β → Prop} :
    ∀ (n : Nat) {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
      List.Forall₂ R (l₁.take n) (l₂.take n)
  | 0, _, _, _ => .nil
  | _+1, _, _, .nil => .nil
  | n+1, _, _, .cons h hs => .cons h (forall2_take n hs)

/-- `Forall₂` survives `drop` (slices the constructor spine at `np`). -/
theorem forall2_drop {α β} {R : α → β → Prop} :
    ∀ (n : Nat) {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
      List.Forall₂ R (l₁.drop n) (l₂.drop n)
  | 0, _, _, h => h
  | _+1, _, _, .nil => .nil
  | n+1, _, _, .cons _ h => forall2_drop n h

/-- Concatenation of `Forall₂`s. -/
theorem forall2_append {α β} {R : α → β → Prop} {l₁ l₂ r₁ r₂}
    (h1 : List.Forall₂ R l₁ l₂) (h2 : List.Forall₂ R r₁ r₂) :
    List.Forall₂ R (l₁ ++ r₁) (l₂ ++ r₂) :=
  (List.Forall₂.append_of_left (Lean4Lean.List.Forall₂.length_eq h1)).2 ⟨h1, h2⟩

/-- `Forall₂` survives `getElem` at a common index. -/
theorem forall2_getElem {α β} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ (i : Nat)
      (h₁ : i < l₁.length) (h₂ : i < l₂.length), R (l₁[i]) (l₂[i])
  | _, _, .cons h _, 0, _, _ => h
  | _, _, .cons _ hs, i+1, h₁, h₂ => forall2_getElem hs i (by simpa using h₁) (by simpa using h₂)

end Lean4Lean

namespace LeanToLambdaBox

open Lean Lean4Lean

/-! ## The named upstream spec

`TrEnv.pats_iota` (`Verify/Environment/Lemmas.lean`) concludes `∃ r, venv.pats P r`
with the rule payload `r` **existentially bound**, so `TrEnv.iota_defeq`'s `Realizes`
premise cannot be instantiated and the reduct cannot be matched against anything. The
fork's own proof does know the witness — its `induct` case ends in
`exact ⟨_, VEnv.addInduct_pat …⟩`, and `addInduct_pat` names the pair
`(SimplePattern.iotaRHS …, .true)` — so naming it is a pure statement strengthening
of already-proved content.

`PatsIotaSpec` states that strengthened lemma **verbatim as it landed on the fork's
`iota` branch**, as a hypothesis structure in the repo's `BridgeHyps` /
`DataBridgeHyps` / `ResidualHyps` idiom. It bundles three fixes:

* **the witness is named** (`SimplePattern.iotaRHS …, .true`), so `iota_defeq` can be
  instantiated at `chk := []`, `hR := trivial`, `hall := nofun`;
* **the motives/minors/indices split is kernel-pinned.** `AddInduct.rec_find` relates
  only `getMajorIdx` (the *sum*) and `numParams`, but `iotaRHS` splits the rec-side
  holes at `np+nm+nmin`, so two model recursors with the same total and a different
  split register different reducts under the same pattern;
* **the reduct is tied to the kernel rule** (`TrExprS venv rval.levelParams []
  rule.rhs rhs`). Nothing in `AddInduct.rec_find` relates `ru.rhs` to `rule.rhs`, and
  the "a pattern determines its reduct" fact that would recover it
  (`VEnv.toParams.pat_uniq`) is not only `sorry` upstream but *documented as false*.

**Discharge.** This is not an axiom and not a `sorry`, and as of the `1a1ebe8` pin it
is not an open obligation either: `PatsIotaSpec.of_trEnv` (below) builds the structure
from any `TrEnv` in one line, off the fork's `TrEnv.pats_iota'`. The structure stays as
the *interface* the ι capstone consumes — same precedent as `ErasesEnvCtor`, which
remains a premise of `erases_correct_data` even though it is provable — so a consumer
that has a `TrEnv` in hand supplies it with `.of_trEnv`, and one that reasons about a
bare `VEnv` still needs nothing more than the field.

The discharge is what fixes `kenv`'s type. It is a `Lean.Kernel.Environment` — the
type `TrEnv` and `Kernel.Environment.find?` are stated at, and the one the rest of this
development already uses for the modelled environment (`ResidualHyps`,
`CheckerAdequacy`, `ShippingCorrect`). An elaborator `Lean.Environment` would not do:
`Environment.find?` consults the async-constant table, so it is not the kernel lookup
and is not related to `(·.toKernelEnv.find?)` by any provable equation. The same
retyping applies to `IotaShape` and every `_of_shape` consumer, `kenv` being a pure
parameter that both premises only ever use through `find?`.

**Safety.** `TrEnv'.induct` fires only at `.safe`, and the lookup needs
`hsafe : safety ≤ (recInfo rval).safety`; anything built at another safety level
silently has no ι rules (`DefinitionSafety.le_safe` discharges it for safe
declarations). -/
structure PatsIotaSpec (safety : DefinitionSafety) (kenv : Lean.Kernel.Environment)
    (venv : VEnv) : Prop where
  /-- The ι rule of a recursor rule resolvable in `kenv` is registered in `venv.pats`,
  **with its payload named**: the reduct is `SimplePattern.iotaRHS` over a closed
  translation `rhs` of the *kernel* rule's template `rule.rhs`, at the kernel's own
  `numParams`/`numMotives`/`numMinors`/`numIndices` split, and the side-condition
  check is the trivial one.

  Since `6fd8a1d` it also **returns the constructor**, tied to the kernel by
  `kenv.find? cName = some (.ctorInfo cval)`, and keys the pattern's constructor-side
  arity on `cval.numParams` rather than the recursor's `rval.numParams` — the two
  differ for the auxiliary recursors of nested inductives, and `VEnv.addRecRule` keys
  on the constructor's. This is the ctor↔pattern agreement the projection round used
  to certify by hand as `ProjCtorAgree`. -/
  pats_iota' : ∀ {recName cName : Name} {rval : RecursorVal} {rule : RecursorRule},
    kenv.find? recName = some (.recInfo rval) →
    rval.rules.find? (·.ctor == cName) = some rule →
    safety ≤ (Lean.ConstantInfo.recInfo rval).safety →
    ∃ (cval : ConstructorVal) (rhs : VExpr) (hc : rhs.Closed),
      kenv.find? cName = some (.ctorInfo cval) ∧
      TrExprS venv rval.levelParams [] rule.rhs rhs ∧
      venv.pats
        (SimplePattern.iota recName
          (rval.numParams + rval.numMotives + rval.numMinors + rval.numIndices) cName
          (cval.numParams + rule.nfields)).toPattern
        (SimplePattern.iotaRHS recName cName rval.numParams rval.numMotives rval.numMinors
          rval.numIndices cval.numParams rule.nfields rhs hc, .true)

/-- **`PatsIotaSpec` is discharged for translated environments.** Any `TrEnv` — the
relation saying `venv` is the model of the kernel environment `kenv` — satisfies the
spec, by the fork's `TrEnv.pats_iota'`. The field is that lemma's statement verbatim,
so the proof is the eta-expansion.

This closes the one upstream item the ι capstone was carrying. It does **not** remove
the structure from the capstone signatures: those stay stated over an ambient `VEnv`
with `PatsIotaSpec` as an explicit premise, and a `TrEnv`-holding caller discharges it
here. Its axiom set is `pats_iota'`'s, which since the `fee3ada` re-pin (2026-08-27) is
**sorryAx-free**: it is lean4lean's `PersistentHashMap` `ConstMap` modelling axioms and
nothing else. [This used to read "`sorryAx` via the `TrProj` placeholder carried in
`TrExprS`". `TrProj` has a real definition now, so mentioning `TrExprS` costs nothing,
and `TrEnv.pats_iota'` measures clean. The claim that it "never picked up
`Aligned.addInduct` because it routes through `TrEnv'.constMap_wf`, not `map_wf`" is
**obsolete at `6fd8a1d`, in the good direction**: `constMap_wf` was *deleted* precisely
because `Aligned.addInduct` is now **proved**, and `pats_iota'` routes through
`TrEnv'.map_wf`, which is clean. The routing rule the previous round recorded is
inverted; the measurement is unchanged.] -/
theorem PatsIotaSpec.of_trEnv {safety : DefinitionSafety} {kenv : Lean.Kernel.Environment}
    {venv : VEnv} (H : TrEnv safety kenv venv) : PatsIotaSpec safety kenv venv :=
  ⟨fun hrec hrule hsafe => TrEnv.pats_iota' H hrec hrule hsafe⟩

/-! ## The ι step: the rule fires on a translated redex -/

/-- **The ι rule fires.** Given the named spec, a translated **exact-arity** redex
`rec a₀ … a_{M-1} (ctor b₀ … b_{N-1})` — with `M = np+nm+nmin+nind` and
`N = cnp+nfields`, the only shape `SimplePattern.iota` matches — is definitionally
equal to the kernel rule's template applied to the recursor's
parameters/motives/minors and the constructor's fields.

The constructor-side arity `cnp` is the **constructor's own** `numParams`, and the
caller must say so by resolving the constructor in `kenv` (`hctor`) — the shape
upstream's `TrEnv.iota_rec` also moved to at `6fd8a1d`, when `VRecRule` gained
`ctorParams` and `VEnv.addRecRule` started keying the registered pattern on it. For an
ordinary inductive `cnp` is the recursor's `rval.numParams`; the two part company for
the auxiliary recursors of nested inductives, and the registry follows the constructor.
So `hctor` is not bookkeeping: it is what says *which* arity the pattern in `venv.pats`
was keyed at, and without it the redex and the registered rule need not have the same
constructor-side arity at all.

Everything on the right-hand side is *named*: `rhs` is the translation of
`rule.rhs`, and the argument lists are the translations of the source spines'
arguments. The `hty` premise of `iota_defeq` comes from `TrExprS.wf`; the
`Realizes`/side-condition premises are discharged at `chk := []` because the
registered check is the literal `Pattern.Check.true`. -/
theorem iota_defeq_spine {safety : DefinitionSafety} {kenv : Lean.Kernel.Environment}
    {venv : VEnv} (hspec : PatsIotaSpec safety kenv venv) (henv : venv.WF)
    {Us : List Name} {Δ : VLCtx} (hΔ : VLCtx.WF venv Us.length Δ)
    {recName cName : Name} {rval : RecursorVal} {rule : RecursorRule}
    {cnp : Nat}
    (hrec : kenv.find? recName = some (.recInfo rval))
    (hrule : rval.rules.find? (·.ctor == cName) = some rule)
    (hsafe : safety ≤ (Lean.ConstantInfo.recInfo rval).safety)
    (hctor : ∃ cval : ConstructorVal,
      kenv.find? cName = some (.ctorInfo cval) ∧ cval.numParams = cnp)
    {recArgs ctorArgs : List Expr} {rus cus : List Level} {ve : VExpr}
    (hras : recArgs.length =
      rval.numParams + rval.numMotives + rval.numMinors + rval.numIndices)
    (hcas : ctorArgs.length = cnp + rule.nfields)
    (htr : TrExprS venv Us Δ
      (.app (recArgs.foldl Expr.app (.const recName rus))
            (ctorArgs.foldl Expr.app (.const cName cus))) ve) :
    ∃ (rhs : VExpr) (_ : rhs.Closed) (rus' : List VLevel) (recArgs' ctorArgs' : List VExpr),
      TrExprS venv rval.levelParams [] rule.rhs rhs ∧
      rus.mapM (VLevel.ofLevel Us) = some rus' ∧
      List.Forall₂ (TrExprS venv Us Δ) recArgs recArgs' ∧
      List.Forall₂ (TrExprS venv Us Δ) ctorArgs ctorArgs' ∧
      venv.IsDefEqU Us.length Δ.toCtx ve
        (VExpr.mkApps (rhs.instL rus')
          (recArgs'.take (rval.numParams + rval.numMotives + rval.numMinors)
            ++ ctorArgs'.drop cnp)) := by
  obtain ⟨A, hty⟩ := htr.wf henv.ordered hΔ
  obtain ⟨cvalC, hctorC, hcnpC⟩ := hctor
  obtain ⟨cval, rhs, hc, hctor', htrRhs, hpats⟩ := hspec.pats_iota' hrec hrule hsafe
  -- `kenv.find?` is a function, so the constructor the spec resolves is the caller's,
  -- and the pattern in `venv.pats` really is keyed at `cnp`.
  obtain rfl : cval.numParams = cnp := by
    rw [hctorC] at hctor'
    exact (Lean.ConstantInfo.ctorInfo.inj (Option.some.inj hctor')) ▸ hcnpC
  cases htr with
  | @app f' A₀ B a' _ _ _ hTf hTa htrf htra =>
    obtain ⟨hve1, recArgs', htrRecHead, hall1, rfl⟩ := TrExprS.mkApps_inv htrf
    obtain ⟨hve2, ctorArgs', htrCtorHead, hall2, rfl⟩ := TrExprS.mkApps_inv htra
    obtain ⟨rus', hmapM, rfl⟩ := htrRecHead.const_inv
    obtain ⟨cus', _, rfl⟩ := htrCtorHead.const_inv
    have hras' : recArgs'.length =
        rval.numParams + rval.numMotives + rval.numMinors + rval.numIndices := by
      rw [← Lean4Lean.List.Forall₂.length_eq hall1]; exact hras
    have hcas' : ctorArgs'.length = cval.numParams + rule.nfields := by
      rw [← Lean4Lean.List.Forall₂.length_eq hall2]; exact hcas
    obtain ⟨m2, hm, hva, hvb⟩ :=
      Pattern.matches_iota (recName := recName) (cName := cName) (ls := rus') (ls' := cus')
        _ _ recArgs' ctorArgs' hras' hcas'
    refine ⟨rhs, hc, rus', recArgs', ctorArgs', htrRhs, hmapM, hall1, hall2, ?_⟩
    have := TrEnv.iota_defeq (chk := []) hpats hm hty trivial nofun
    rwa [SimplePattern.iotaRHS_apply hras' hcas' hva hvb] at this

end LeanToLambdaBox
