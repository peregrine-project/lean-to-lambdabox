import LeanToLambdaBox.ColdStartShape
import LeanToLambdaBox.ErasesAlpha
import LeanToLambdaBox.OutputShape

/-!
# The induction over the erasure family

Three facts the registration path needs are facts about the *results* of the eighteen
mutually recursive members of `Erasure.visitExpr`: the stored body is de Bruijn closed
(`ColdStartShape.RegInvShape'`'s constant cons), fix-free and in applied form (`Output.lean`).
Three more are facts about how a run moves: the state grows canonically, the name generator
only advances, and a modelled inductive registry stays modelled. One induction through
`Erasure.visitExpr.mutual_fixpoint_induct` gives all of them — `visitExpr_shapeW` — and
`visitExpr_shape` is its world-blind instance.

## Shape of the statement

The induction is in Hoare form over a predicate of the state **and the world token**, because
`visitMutual` — the one member that writes the state — is handled inside the induction, where
the step goal is about the fixpoint's abstract `visitExpr` argument rather than the real one,
and because a state-only predicate expresses neither a relation between two states nor a
generator bound. `RunClosedW Cfg P` collects the sixteen closure facts: one per ambient
primitive the family calls, one per place it writes the state, one per registration exit.
`ShapeCW` is the per-call conclusion — "`P` survives and the produced term is fix-free, de
Bruijn closed and in applied form" — under a condition `Cfg` on the reader's configuration.

`Cfg` is what a state-only interface cannot carry, and it is why `RunClosed` is inhabited only
at `fun _ => True`: `Erasure.prepare_erasure`'s `@[csimp]` branch runs `Lean.Core.transform` at
`EraseM`, whose state effect no `liftM` lemma reaches, so the clause crossing the preparation
pass is readable only at a pinned configuration. The condition sits *after* the run equation in
every motive, the shape `eraseM_admissible_ok₁`-`₅` recognise.

Three motives deviate from `ShapeCW`: motive 7 (`visitAppArgs`) additionally **takes** the
accumulator seed's three output conjuncts, motive 18 (`visitAlt`) concludes
`LBClosed r.2 r.1.length`, and motives 5/6 return no term, so `P` surviving is all they say.

## Two matcher lemmas

`visitCases` and `visitConstructor` each dispatch on a two-discriminant match whose patterns
are `Name` literals, which `split` cannot take apart at a hypothesis whose subject is the match
*applied* to the monad's five arguments. `visitCases_match_tri` and
`visitConstructor_match_quad` do the case analysis once. If either shipping match is edited the
matcher index moves, and the failure mode is a build error.
-/

namespace LeanToLambdaBox

open Lean Erasure

/-! ## The two name-pattern matchers -/

/-- **`visitCases`' `(typeName, config.nat)` dispatch is a trichotomy.** Stated against the
elaborator-generated matcher `Erasure.visitCases.match_17`; see the module docstring for why
`split` is unusable at the call site. The two special arms report their `Config.Nat`
discriminant, which is what tells a caller that they are the machine-numeral arms. -/
theorem visitCases_match_tri {α : Sort u} (nm : Name) (cn : Erasure.Config.Nat)
    (A B : Unit → α) (G : Name → Erasure.Config.Nat → α) :
    (cn = .machine ∧ Erasure.visitCases.match_17 (motive := fun _ _ => α) nm cn A B G = A ()) ∨
    (cn = .machine ∧ Erasure.visitCases.match_17 (motive := fun _ _ => α) nm cn A B G = B ()) ∨
    Erasure.visitCases.match_17 (motive := fun _ _ => α) nm cn A B G = G nm cn := by
  unfold Erasure.visitCases.match_17
  cases nm with
  | anonymous => exact Or.inr (Or.inr rfl)
  | num p n => exact Or.inr (Or.inr rfl)
  | str p str =>
    cases p with
    | num p2 n2 => exact Or.inr (Or.inr rfl)
    | str p2 s2 => exact Or.inr (Or.inr rfl)
    | anonymous =>
      by_cases h1 : str = "Nat"
      · subst h1
        cases cn with
        | machine => exact Or.inl ⟨rfl, rfl⟩
        | peano => exact Or.inr (Or.inr rfl)
      · by_cases h2 : str = "Int"
        · subst h2
          cases cn with
          | machine => exact Or.inr (Or.inl ⟨rfl, rfl⟩)
          | peano => exact Or.inr (Or.inr rfl)
        · refine Or.inr (Or.inr ?_)
          show (dite (str = "Nat") _ _) = _
          rw [dif_neg h1]
          show (dite (str = "Int") _ _) = _
          rw [dif_neg h2]

/-- **`visitConstructor`'s `(config.nat, ctorname)` dispatch is a four-way case.** The two
machine-`Nat` arms (`Nat.zero`/`Nat.succ`) are *live* here — unlike in the ι bridge, where
the supported fragment excludes them — so both are proved, not refuted. -/
theorem visitConstructor_match_quad {α : Sort u} (cn : Erasure.Config.Nat) (nm : Name)
    (A B : Unit → α) (C D : Name → α) :
    Erasure.visitConstructor.match_1 (motive := fun _ _ => α) cn nm A B C D = A () ∨
    Erasure.visitConstructor.match_1 (motive := fun _ _ => α) cn nm A B C D = B () ∨
    Erasure.visitConstructor.match_1 (motive := fun _ _ => α) cn nm A B C D = C nm ∨
    Erasure.visitConstructor.match_1 (motive := fun _ _ => α) cn nm A B C D = D nm := by
  split
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

/-! ## The interface: what a state predicate must be closed under -/

/-- **The six closure facts the shape induction needs of a state predicate**, one per place
the erasure family touches `ErasureState`: the `inlinings` cons, the two registration
primitives in *run* form (so that `addAxiom`'s panic fall-through and
`register_inductive`'s state-changing cold branch are covered), `prepare_erasure`, and
`visitMutual`'s two registering exits. `nrc` consumes the output-shape facts, which is why
they are proved by the same induction that uses them. -/
structure RunClosed (Q : ErasureState → Prop) : Prop where
  inl : ∀ {s : ErasureState} {kn : Kername},
    Q s → Q { s with inlinings := kn :: s.inlinings }
  ax : ∀ {m : Name} {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
      {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld} {u : Unit}
      {s' : ErasureState} {w' : Void IO.RealWorld},
    addAxiom m s ctx cctx ref w = .ok (u, s') w' → Q s → Q s'
  reg : ∀ {ii : InductiveVal} {s : ErasureState} {ctx : ErasureContext}
      {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
      {r : InductiveId × InductiveArgMasks} {s' : ErasureState} {w' : Void IO.RealWorld},
    register_inductive ii s ctx cctx ref w = .ok (r, s') w' → Q s → Q s'
  prep : ∀ {e : Expr} {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
      {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld} {pe : Expr}
      {s' : ErasureState} {w' : Void IO.RealWorld},
    prepare_erasure e s ctx cctx ref w = .ok (pe, s') w' → Q s → Q s'
  nrc : ∀ {n : Name} {t : LBTerm} {s : ErasureState},
    Q s → NoFix t → LBClosed t 0 → NoBlock t → Q (nonrecConstState n t s)
  /-- `Erasure.addRealizer`'s cons (F-QUOT, F-EQREC), at the shape of the realizer body.
      The premises are `nrc`'s because the delta is: `addRealizerState` writes the entry
      `nonrecConstState` writes. -/
  rlz : ∀ {n : Name} {t : LBTerm} {s : ErasureState},
    Q s → NoFix t → LBClosed t 0 → NoBlock t → Q (addRealizerState n t s)
  /-- The recursive block cons, **given the closedness and applied form of the block being
  stored**. Both are false of an arbitrary `defs` (`.fix [{body := .bvar 5}] 0` is not
  closed), so the induction derives them per call from the block's own shape:
  `Erasure.run_rec_exit_ok` reports each body as a `mkDef` closure of a `visitExpr` output
  over the block's names, and `rec_block_closed`/`rec_block_noBlock` do the rest. -/
  rc : ∀ {names : List Name} {defs : List (@FixDef LBTerm)} {s : ErasureState},
    Q s → (∀ j : Nat, LBClosed (.fix defs j) 0) → (∀ j : Nat, NoBlock (.fix defs j)) →
      Q (recConstState names defs s)

/-- The per-call conclusion: from `Q` at entry, `Q` at exit **and** the produced λ□ term is
fix-free, de Bruijn closed, and in applied form.

`NoBlock` is not a boxing condition — it forbids exactly one node,
`.construct _ _ (_ :: _)` — and the eraser has exactly one `.construct` construction site
(`Erasure.visitConstructor`), nullary by design, so the induction concludes it rather than
taking it as a premise. -/
def ShapeC (Q : ErasureState → Prop) (s s' : ErasureState) (t : LBTerm) : Prop :=
  Q s → Q s' ∧ NoFix t ∧ LBClosed t 0 ∧ NoBlock t

/-- **The recursive exit's block is closed.** The bridge between what
`Erasure.run_rec_exit_ok` hands the `rc` closure — per definition, "my body is the
`mkDef` closure of a closed erasure output over the block's names" — and what
`ColdStartShape.RegInvShape'`'s `closed` field needs of the stored node. `hfix` is the shipping code's
`fixvarnames := names.map remove_unsafe_rec`, i.e. `List.length_map`. -/
theorem rec_block_closed {names fixnames : List Name} {defs : List (@FixDef LBTerm)}
    (hfix : fixnames.length = names.length) (hlen : defs.length = names.length)
    (hbodies : ∀ d ∈ defs, ∃ (t : LBTerm) (fv : Name → FVarId), LBClosed t 0 ∧
      d.body = fixnames.reverse.zipIdx.foldl (fun b p => toBvar (fv p.1) p.2 b) t)
    (j : Nat) : LBClosed (.fix defs j) 0 := by
  refine lbClosed_fix_of_bodies (k := fixnames.length) (hlen.trans hfix.symm) ?_ j
  intro d hd
  obtain ⟨t, fv, hcl, hbody⟩ := hbodies d hd
  rw [hbody]
  exact lbClosed_foldl_zipIdx_map fv fixnames hcl

/-- **The recursive exit's block is in applied form.** `rec_block_closed`'s sibling for the
third output conjunct, and strictly simpler: `NoBlock (.fix defs j)` is
`∀ d ∈ defs, NoBlock d.body` at every index, so there is no binder arithmetic — only the
`mkDef` fold, which `noBlock_foldl_zipIdx_map` discharges. -/
theorem rec_block_noBlock {fixnames : List Name} {defs : List (@FixDef LBTerm)}
    (hbodies : ∀ d ∈ defs, ∃ (t : LBTerm) (fv : Name → FVarId), NoBlock t ∧
      d.body = fixnames.reverse.zipIdx.foldl (fun b p => toBvar (fv p.1) p.2 b) t)
    (j : Nat) : NoBlock (.fix defs j) := by
  rw [NoBlock_fix]
  intro d hd
  obtain ⟨t, fv, hnb, hbody⟩ := hbodies d hd
  rw [hbody]
  exact noBlock_foldl_zipIdx_map fv fixnames hnb

/-- Split the paired per-definition report `Erasure.run_rec_exit_ok` hands the `rc` closure
— it is stated at the *abstract* output predicate `Cl`, which the induction instantiates at
`fun t => LBClosed t 0 ∧ NoBlock t` — into the shape `rec_block_closed` wants. Pure
projection; it exists so the two block-level lemmas each keep their single-fact statement.
-/
theorem rec_bodies_closed {fixnames : List Name} {defs : List (@FixDef LBTerm)}
    (h : ∀ d ∈ defs, ∃ (t : LBTerm) (fv : Name → FVarId), (LBClosed t 0 ∧ NoBlock t) ∧
      d.body = fixnames.reverse.zipIdx.foldl (fun b p => toBvar (fv p.1) p.2 b) t) :
    ∀ d ∈ defs, ∃ (t : LBTerm) (fv : Name → FVarId), LBClosed t 0 ∧
      d.body = fixnames.reverse.zipIdx.foldl (fun b p => toBvar (fv p.1) p.2 b) t :=
  fun d hd => let ⟨t, fv, hc, hb⟩ := h d hd; ⟨t, fv, hc.1, hb⟩

/-- The other half of `rec_bodies_closed`'s split, for `rec_block_noBlock`. -/
theorem rec_bodies_noBlock {fixnames : List Name} {defs : List (@FixDef LBTerm)}
    (h : ∀ d ∈ defs, ∃ (t : LBTerm) (fv : Name → FVarId), (LBClosed t 0 ∧ NoBlock t) ∧
      d.body = fixnames.reverse.zipIdx.foldl (fun b p => toBvar (fv p.1) p.2 b) t) :
    ∀ d ∈ defs, ∃ (t : LBTerm) (fv : Name → FVarId), NoBlock t ∧
      d.body = fixnames.reverse.zipIdx.foldl (fun b p => toBvar (fv p.1) p.2 b) t :=
  fun d hd => let ⟨t, fv, hc, hb⟩ := h d hd; ⟨t, fv, hc.2, hb⟩


/-! ## The world-indexed interface

`RunClosed` propagates a predicate of the erasure **state** alone, and two facts the
registration path needs are not of that shape: `Erasure.RunConcl s s₁` relates two states and
a generator bound `gw w ≤ gw w₁` reads the world token. `RunClosedW` is the same interface at
a predicate of the state *and* the world. Two differences are forced by the index.

* Every state-transparent primitive the family calls — the relevance oracle,
  `Lean.Meta.inferType`, the four environment queries, `Lean.logInfo`,
  `Lean.Meta.isInstance`, `Lean.mkFreshFVarId` — leaves the state alone but **advances the
  world**, so each takes its own clause. They are one-for-one the calls
  `ErasureSpec.prim_monotone`, `ErasureSpec.lookup_adequate` and `ErasureSpec.fresh_names`
  specify.
* `prep` and `reg` read the reader's configuration — `Erasure.prepare_erasure`'s `@[csimp]`
  branch runs `Lean.Core.transform` at `EraseM`, whose state effect is out of reach of the
  `liftM` lemmas, and `Erasure.register_inductive`'s cold branch computes a pruning mask —
  so `Cfg` is a condition on the reader that the induction carries as a premise on every
  member. That premise is what a state-only predicate cannot hold, and it is why
  `RunClosed` is inhabited only at `fun _ => True`.
-/

/-- **The closure facts a world-indexed state predicate must satisfy**, at readers whose
configuration satisfies `Cfg`: one clause per ambient primitive the eighteen-member family
calls, one per place it writes the state, and one per registration exit. -/
structure RunClosedW (Cfg : ErasureConfig → Prop)
    (P : ErasureState → Void IO.RealWorld → Prop) : Prop where
  /-- The relevance oracle, at the reader's own level scope, which is where the erasability
      gate calls it. -/
  oracle : ∀ {e : Expr} {b : Bool} {s s' : ErasureState} {ctx : ErasureContext}
      {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
      {w w' : Void IO.RealWorld},
    liftMetaM (Erasure.isErasable ctx.lparams e) s ctx cctx ref w = .ok (b, s') w' →
    P s w → P s' w'
  /-- `Lean.Meta.inferType`. -/
  inferType : ∀ {e ty : Expr} {s s' : ErasureState} {ctx : ErasureContext}
      {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
      {w w' : Void IO.RealWorld},
    liftMetaM (Lean.Meta.inferType e) s ctx cctx ref w = .ok (ty, s') w' → P s w → P s' w'
  /-- The `Lean.MetaM` computations the family lifts besides the oracle and `inferType`: two
      proof tests under a bounded telescope, `Erasure.firstNonProofField`'s on a
      constructor's fields (`Erasure.lean:305-309`) and `Erasure.visitCases`' on the
      catch-all's hypotheses (`Erasure.lean:1150-1153`). Neither lambda is named, so the
      clause reads them through `PrimGenMono`, the class of computations built from
      `Lean.Meta.isProof` and the two telescopes; each call site discharges it by
      composition. -/
  metaM : ∀ {α : Type} {x : Lean.MetaM α} {a : α} {s s' : ErasureState} {ctx : ErasureContext}
      {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
      {w w' : Void IO.RealWorld},
    PrimGenMono x → liftMetaM x s ctx cctx ref w = .ok (a, s') w' → P s w → P s' w'
  /-- `Lean.getConstInfo`. -/
  constInfo : ∀ {n : Name} {ci : ConstantInfo} {s s' : ErasureState} {ctx : ErasureContext}
      {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
      {w w' : Void IO.RealWorld},
    (getConstInfo n : EraseM ConstantInfo) s ctx cctx ref w = .ok (ci, s') w' →
    P s w → P s' w'
  /-- `Lean.getEnv`. -/
  getEnv : ∀ {le : Environment} {s s' : ErasureState} {ctx : ErasureContext}
      {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
      {w w' : Void IO.RealWorld},
    (getEnv : EraseM Environment) s ctx cctx ref w = .ok (le, s') w' → P s w → P s' w'
  /-- `Lean.logInfo`. -/
  logInfo : ∀ {msg : MessageData} {u : Unit} {s s' : ErasureState} {ctx : ErasureContext}
      {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
      {w w' : Void IO.RealWorld},
    (logInfo msg : EraseM Unit) s ctx cctx ref w = .ok (u, s') w' → P s w → P s' w'
  /-- `Lean.Meta.isInstance`. -/
  isInstance : ∀ {n : Name} {b : Bool} {s s' : ErasureState} {ctx : ErasureContext}
      {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
      {w w' : Void IO.RealWorld},
    (liftM (Lean.Meta.isInstance n) : EraseM Bool) s ctx cctx ref w = .ok (b, s') w' →
    P s w → P s' w'
  /-- `Lean.mkFreshFVarId`. -/
  fresh : ∀ {x : FVarId} {s s' : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
      {ref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld},
    (mkFreshFVarId : EraseM FVarId) s ctx cctx ref w = .ok (x, s') w' → P s w → P s' w'
  /-- `Lean.Compiler.LCNF.getDeclInfo?`. -/
  declInfo : ∀ {n : Name} {r : Option ConstantInfo} {s s' : ErasureState}
      {ctx : ErasureContext} {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
      {w w' : Void IO.RealWorld},
    (liftM (Lean.Compiler.LCNF.getDeclInfo? n) : EraseM (Option ConstantInfo))
      s ctx cctx ref w = .ok (r, s') w' → P s w → P s' w'
  /-- `Lean.Compiler.LCNF.getCtorArity?`. -/
  ctorArity : ∀ {n : Name} {r : Option Nat} {s s' : ErasureState} {ctx : ErasureContext}
      {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
      {w w' : Void IO.RealWorld},
    (liftM (Lean.Compiler.LCNF.getCtorArity? n) : EraseM (Option Nat))
      s ctx cctx ref w = .ok (r, s') w' → P s w → P s' w'
  /-- `Lean.getCasesInfo?`. -/
  casesInfo : ∀ {n : Name} {r : Option Lean.CasesInfo} {s s' : ErasureState}
      {ctx : ErasureContext} {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
      {w w' : Void IO.RealWorld},
    (liftM (Lean.getCasesInfo? n) : EraseM (Option Lean.CasesInfo))
      s ctx cctx ref w = .ok (r, s') w' → P s w → P s' w'
  /-- The `@[inline]` bookkeeping cons. -/
  inl : ∀ {s : ErasureState} {w : Void IO.RealWorld} {kn : Kername},
    P s w → P { s with inlinings := kn :: s.inlinings } w
  /-- `Erasure.addAxiom`, in run form, so that its `panic!` fall-through is covered. -/
  ax : ∀ {m : Name} {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
      {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld} {u : Unit}
      {s' : ErasureState} {w' : Void IO.RealWorld},
    addAxiom m s ctx cctx ref w = .ok (u, s') w' → P s w → P s' w'
  /-- `Erasure.register_inductive`, in run form, at a reader `Cfg` describes, with the
      provenance of the `Lean.InductiveVal` it is called at: either a `Lean.getConstInfo` run
      returned it, or the call is one of `Erasure.visitCases`' two machine-numeral arms, which
      read `Bool`'s block through `Lean.ConstantInfo.inductiveVal!` instead. A consumer that
      pins `nat = .peano` refutes the second disjunct and reads the first through
      `ErasureSpec.lookup_adequate`, which is what a model-side registry invariant needs. -/
  reg : ∀ {ii : InductiveVal} {s : ErasureState} {ctx : ErasureContext}
      {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
      {r : InductiveId × InductiveArgMasks} {s' : ErasureState} {w' : Void IO.RealWorld},
    ((∃ (hd : Name) (sa sb : ErasureState) (wa wb : Void IO.RealWorld),
        (getConstInfo hd : EraseM ConstantInfo) sa ctx cctx ref wa
          = .ok (.inductInfo ii, sb) wb) ∨ ctx.config.nat = .machine) →
    Cfg ctx.config → register_inductive ii s ctx cctx ref w = .ok (r, s') w' →
    P s w → P s' w'
  /-- `Erasure.prepare_erasure`, at a reader `Cfg` describes. -/
  prep : ∀ {e : Expr} {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
      {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld} {pe : Expr}
      {s' : ErasureState} {w' : Void IO.RealWorld},
    Cfg ctx.config → prepare_erasure e s ctx cctx ref w = .ok (pe, s') w' →
    P s w → P s' w'
  /-- `Erasure.visitMutual`'s non-recursive exit, given the shape of the body stored. -/
  nrc : ∀ {n : Name} {t : LBTerm} {s : ErasureState} {w : Void IO.RealWorld},
    P s w → NoFix t → LBClosed t 0 → NoBlock t → P (nonrecConstState n t s) w
  /-- `Erasure.addRealizer`'s cons at the two realizer exits (F-QUOT, F-EQREC), given the
      shape of the realizer body — `quotRealizer_shape` and `run_recursorRealizer_okW`
      supply it where the clause is spent. -/
  rlz : ∀ {n : Name} {t : LBTerm} {s : ErasureState} {w : Void IO.RealWorld},
    P s w → NoFix t → LBClosed t 0 → NoBlock t → P (addRealizerState n t s) w
  /-- `Erasure.visitMutual`'s block exit, given the closedness and applied form of the block
      being stored. -/
  rc : ∀ {names : List Name} {defs : List (@FixDef LBTerm)} {s : ErasureState}
      {w : Void IO.RealWorld},
    P s w → (∀ j : Nat, LBClosed (.fix defs j) 0) → (∀ j : Nat, NoBlock (.fix defs j)) →
      P (recConstState names defs s) w

/-- The per-call conclusion of the world-indexed induction: at a reader `Cfg` describes, `P`
survives the run and the produced λ□ term is fix-free, de Bruijn closed and in applied form.
`ShapeC`'s twin; the configuration premise sits *after* the run equation so that the motive
keeps the shape `eraseM_admissible_ok₁`-`₅` recognise. -/
def ShapeCW (Cfg : ErasureConfig → Prop) (P : ErasureState → Void IO.RealWorld → Prop)
    (ctx : ErasureContext) (s : ErasureState) (w : Void IO.RealWorld) (s' : ErasureState)
    (w' : Void IO.RealWorld) (t : LBTerm) : Prop :=
  P s w → Cfg ctx.config → P s' w' ∧ NoFix t ∧ LBClosed t 0 ∧ NoBlock t

/-- **A state predicate is a world-indexed one that ignores the world.** The ten primitive
clauses are the state-transparency lemmas of `ErasureRun.lean`; the six remaining ones are
`RunClosed`'s own, `Cfg` unread. This is what makes `visitExpr_shape` a corollary of the
world-indexed induction rather than a second one. -/
theorem runClosedW_of_runClosed {Cfg : ErasureConfig → Prop} {Q : ErasureState → Prop}
    (H : RunClosed Q) : RunClosedW Cfg (fun s _ => Q s) where
  oracle h hQ := by rw [run_liftMetaM_state _ _ _ _ _ h]; exact hQ
  inferType h hQ := by rw [run_liftMetaM_state _ _ _ _ _ h]; exact hQ
  metaM _ h hQ := by rw [run_liftMetaM_state _ _ _ _ _ h]; exact hQ
  constInfo h hQ := by rw [run_getConstInfo_state _ _ _ _ _ h]; exact hQ
  getEnv h hQ := by rw [run_getEnv_state _ _ _ _ _ h]; exact hQ
  logInfo h hQ := by rw [run_logInfo_state _ _ _ _ _ h]; exact hQ
  isInstance h hQ := by rw [run_liftCoreM_state _ _ _ _ _ h]; exact hQ
  fresh h hQ := by rw [run_mkFreshFVarId_state _ _ _ _ _ h]; exact hQ
  declInfo h hQ := by rw [run_liftCoreM_state _ _ _ _ _ h]; exact hQ
  ctorArity h hQ := by rw [run_liftCoreM_state _ _ _ _ _ h]; exact hQ
  casesInfo h hQ := by rw [run_liftCoreM_state _ _ _ _ _ h]; exact hQ
  inl hQ := H.inl hQ
  ax h hQ := H.ax h hQ
  reg _ _ h hQ := H.reg h hQ
  prep _ h hQ := H.prep h hQ
  nrc hQ hnf hcl hnb := H.nrc hQ hnf hcl hnb
  rlz hQ hnf hcl hnb := H.rlz hQ hnf hcl hnb
  rc hQ hcl hnb := H.rc hQ hcl hnb

/-! ## The binder helpers, world-indexed

`ErasureRun.lean`'s binder-helper run lemmas hand the continuation back at an
*unconstrained* reader and drop the `Lean.mkFreshFVarId` run that advanced the world. A
world-indexed induction needs both: the reader, because `RunClosedW`'s two configuration
clauses are read at it, and the fresh run, because the world moved. The five lemmas below
are the same decompositions reporting exactly those two facts — the reader's configuration
is the caller's, and `P` survives to the continuation's entry.
-/

section BinderW

variable {α : Type} {P : ErasureState → Void IO.RealWorld → Prop}
  {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}

/-- `Erasure.withLocalDecl`, with the continuation's reader and world reported. -/
theorem run_withLocalDecl_okW (hfr : ∀ {x : FVarId} {sa sb : ErasureState} {c : ErasureContext}
        {wa wb : Void IO.RealWorld},
      (mkFreshFVarId : EraseM FVarId) sa c cctx ref wa = .ok (x, sb) wb → P sa wa → P sb wb)
     {nm : Name} {ty : Expr} {bi : BinderInfo}
    {k : FVarId → EraseM α} {s : ErasureState} {ctx : ErasureContext}
    {w : Void IO.RealWorld} {r : α} {s' : ErasureState} {w' : Void IO.RealWorld} (hP : P s w)
    (hrun : withLocalDecl nm ty bi k s ctx cctx ref w = .ok (r, s') w') :
    ∃ (x : FVarId) (ctx' : ErasureContext) (w₀ : Void IO.RealWorld),
      ctx'.config = ctx.config ∧ P s w₀ ∧ k x s ctx' cctx ref w₀ = .ok (r, s') w' := by
  unfold withLocalDecl at hrun
  rw [run_bind_ok] at hrun
  obtain ⟨x, sx, wx, hfv, hk⟩ := hrun
  have hz := run_mkFreshFVarId_state _ _ cctx ref _ hfv
  subst hz
  rw [run_withReader] at hk
  refine ⟨x, _, _, ?_, hfr hfv hP, hk⟩
  rfl

/-- `Erasure.withLocalDef`, likewise. -/
theorem run_withLocalDef_okW (hfr : ∀ {x : FVarId} {sa sb : ErasureState} {c : ErasureContext}
        {wa wb : Void IO.RealWorld},
      (mkFreshFVarId : EraseM FVarId) sa c cctx ref wa = .ok (x, sb) wb → P sa wa → P sb wb)
     {nm : Name} {ty val : Expr} {nd : Bool}
    {k : FVarId → EraseM α} {s : ErasureState} {ctx : ErasureContext}
    {w : Void IO.RealWorld} {r : α} {s' : ErasureState} {w' : Void IO.RealWorld} (hP : P s w)
    (hrun : withLocalDef nm ty val nd k s ctx cctx ref w = .ok (r, s') w') :
    ∃ (x : FVarId) (ctx' : ErasureContext) (w₀ : Void IO.RealWorld),
      ctx'.config = ctx.config ∧ P s w₀ ∧ k x s ctx' cctx ref w₀ = .ok (r, s') w' := by
  unfold withLocalDef at hrun
  rw [run_bind_ok] at hrun
  obtain ⟨x, sx, wx, hfv, hk⟩ := hrun
  have hz := run_mkFreshFVarId_state _ _ cctx ref _ hfv
  subst hz
  rw [run_withReader] at hk
  refine ⟨x, _, _, ?_, hfr hfv hP, hk⟩
  rfl

/-- `Erasure.lambdaMonocular`: the panic fall-through, or the continuation under one binder.
-/
theorem run_lambdaMonocular_okW [Inhabited α]
    (hfr : ∀ {x : FVarId} {sa sb : ErasureState} {c : ErasureContext}
        {wa wb : Void IO.RealWorld},
      (mkFreshFVarId : EraseM FVarId) sa c cctx ref wa = .ok (x, sb) wb → P sa wa → P sb wb)
     {e : Expr}
    {k : FVarId → Expr → EraseM α} {s : ErasureState} {ctx : ErasureContext}
    {w : Void IO.RealWorld} {r : α} {s' : ErasureState} {w' : Void IO.RealWorld} (hP : P s w)
    (hrun : lambdaMonocular e k s ctx cctx ref w = .ok (r, s') w') :
    (r = default ∧ s' = s ∧ w' = w) ∨
    ∃ (x : FVarId) (b : Expr) (ctx' : ErasureContext) (w₀ : Void IO.RealWorld),
      ctx'.config = ctx.config ∧ P s w₀ ∧ k x b s ctx' cctx ref w₀ = .ok (r, s') w' := by
  unfold lambdaMonocular at hrun
  split at hrun
  · obtain ⟨x, ctx', w₀, hcf, hP₀, hk⟩ := run_withLocalDecl_okW hfr hP hrun
    exact Or.inr ⟨x, _, ctx', w₀, hcf, hP₀, hk⟩
  · rw [run_panicWithPosWithDecl] at hrun
    cases hrun
    exact Or.inl ⟨rfl, rfl, rfl⟩

/-- `Erasure.letMonocular`, likewise. -/
theorem run_letMonocular_okW [Inhabited α]
    (hfr : ∀ {x : FVarId} {sa sb : ErasureState} {c : ErasureContext}
        {wa wb : Void IO.RealWorld},
      (mkFreshFVarId : EraseM FVarId) sa c cctx ref wa = .ok (x, sb) wb → P sa wa → P sb wb)
     {e : Expr}
    {k : FVarId → Expr → Expr → EraseM α} {s : ErasureState} {ctx : ErasureContext}
    {w : Void IO.RealWorld} {r : α} {s' : ErasureState} {w' : Void IO.RealWorld} (hP : P s w)
    (hrun : letMonocular e k s ctx cctx ref w = .ok (r, s') w') :
    (r = default ∧ s' = s ∧ w' = w) ∨
    ∃ (x : FVarId) (v b : Expr) (ctx' : ErasureContext) (w₀ : Void IO.RealWorld),
      ctx'.config = ctx.config ∧ P s w₀ ∧ k x v b s ctx' cctx ref w₀ = .ok (r, s') w' := by
  unfold letMonocular at hrun
  split at hrun
  · obtain ⟨x, ctx', w₀, hcf, hP₀, hk⟩ := run_withLocalDef_okW hfr hP hrun
    exact Or.inr ⟨x, _, _, ctx', w₀, hcf, hP₀, hk⟩
  · rw [run_panicWithPosWithDecl] at hrun
    cases hrun
    exact Or.inl ⟨rfl, rfl, rfl⟩

/-- `Erasure.forallMonocular`, likewise. -/
theorem run_forallMonocular_okW [Inhabited α]
    (hfr : ∀ {x : FVarId} {sa sb : ErasureState} {c : ErasureContext}
        {wa wb : Void IO.RealWorld},
      (mkFreshFVarId : EraseM FVarId) sa c cctx ref wa = .ok (x, sb) wb → P sa wa → P sb wb)
     {ty : Expr}
    {k : FVarId → Expr → EraseM α} {s : ErasureState} {ctx : ErasureContext}
    {w : Void IO.RealWorld} {r : α} {s' : ErasureState} {w' : Void IO.RealWorld} (hP : P s w)
    (hrun : forallMonocular ty k s ctx cctx ref w = .ok (r, s') w') :
    (r = default ∧ s' = s ∧ w' = w) ∨
    ∃ (x : FVarId) (bt : Expr) (ctx' : ErasureContext) (w₀ : Void IO.RealWorld),
      ctx'.config = ctx.config ∧ P s w₀ ∧ k x bt s ctx' cctx ref w₀ = .ok (r, s') w' := by
  unfold forallMonocular at hrun
  split at hrun
  · obtain ⟨x, ctx', w₀, hcf, hP₀, hk⟩ := run_withLocalDecl_okW hfr hP hrun
    exact Or.inr ⟨x, _, ctx', w₀, hcf, hP₀, hk⟩
  · rw [run_panicWithPosWithDecl] at hrun
    cases hrun
    exact Or.inl ⟨rfl, rfl, rfl⟩

/-- `Erasure.lambdaMonocularOrIntro`: one `forallMonocular` binder, then a continuation on
the λ-body or on the η-expansion. -/
theorem run_lambdaMonocularOrIntro_okW [Inhabited α]
    (hfr : ∀ {x : FVarId} {sa sb : ErasureState} {c : ErasureContext}
        {wa wb : Void IO.RealWorld},
      (mkFreshFVarId : EraseM FVarId) sa c cctx ref wa = .ok (x, sb) wb → P sa wa → P sb wb)
     {e ty : Expr}
    {k : Expr → Expr → FVarId → EraseM α} {s : ErasureState} {ctx : ErasureContext}
    {w : Void IO.RealWorld} {r : α} {s' : ErasureState} {w' : Void IO.RealWorld} (hP : P s w)
    (hrun : lambdaMonocularOrIntro e ty k s ctx cctx ref w = .ok (r, s') w') :
    (r = default ∧ s' = s ∧ w' = w) ∨
    ∃ (e' bt : Expr) (x : FVarId) (ctx' : ErasureContext) (w₀ : Void IO.RealWorld),
      ctx'.config = ctx.config ∧ P s w₀ ∧ k e' bt x s ctx' cctx ref w₀ = .ok (r, s') w' := by
  unfold lambdaMonocularOrIntro at hrun
  rcases run_forallMonocular_okW hfr hP hrun with ⟨h1, h2, h3⟩ | ⟨x, bt, ctx', w₀, hcf, hP₀, hk⟩
  · exact Or.inl ⟨h1, h2, h3⟩
  · split at hk
    · exact Or.inr ⟨_, bt, x, ctx', w₀, hcf, hP₀, hk⟩
    · exact Or.inr ⟨_, bt, x, ctx', w₀, hcf, hP₀, hk⟩

/-- `Erasure.lambdaOrIntroToArity`: the panic fall-through — which returns at the world the
binders opened so far, so `P` is reported there rather than at the entry — or the
continuation on exactly `arity` fresh identifiers. -/
theorem run_lambdaOrIntroToArity_okW [Inhabited α]
    (hfr : ∀ {x : FVarId} {sa sb : ErasureState} {c : ErasureContext}
        {wa wb : Void IO.RealWorld},
      (mkFreshFVarId : EraseM FVarId) sa c cctx ref wa = .ok (x, sb) wb → P sa wa → P sb wb)
     :
    ∀ (arity : Nat) {e ty : Expr} {k : Expr → List FVarId → EraseM α} {s : ErasureState}
      {ctx : ErasureContext} {w : Void IO.RealWorld} {r : α} {s' : ErasureState}
      {w' : Void IO.RealWorld}, P s w →
      lambdaOrIntroToArity e ty arity k s ctx cctx ref w = .ok (r, s') w' →
      (r = default ∧ s' = s ∧ P s' w') ∨
      ∃ (e' : Expr) (xs : List FVarId) (ctx' : ErasureContext) (w₀ : Void IO.RealWorld),
        xs.length = arity ∧ ctx'.config = ctx.config ∧ P s w₀ ∧
          k e' xs s ctx' cctx ref w₀ = .ok (r, s') w'
  | 0, e, ty, k, s, ctx, w, r, s', w', hP, hrun =>
    Or.inr ⟨e, [], ctx, w, rfl, rfl, hP, hrun⟩
  | m + 1, e, ty, k, s, ctx, w, r, s', w', hP, hrun => by
    unfold lambdaOrIntroToArity at hrun
    rcases run_lambdaMonocularOrIntro_okW hfr hP hrun with
      ⟨h1, h2, h3⟩ | ⟨e', bt, x, ctx', w₀, hcf, hP₀, hk⟩
    · subst h2; subst h3; exact Or.inl ⟨h1, rfl, hP⟩
    · rcases run_lambdaOrIntroToArity_okW hfr m hP₀ hk with
        ⟨h1, h2, h3⟩ | ⟨e'', xs, ctx'', w₁, hlen, hcf', hP₁, hk'⟩
      · exact Or.inl ⟨h1, h2, h3⟩
      · exact Or.inr ⟨e'', x :: xs, ctx'', w₁, by simp [hlen], hcf'.trans hcf, hP₁, hk'⟩

end BinderW

/-! ## The two realizer bodies

`F-QUOT` and `F-EQREC` gave `Erasure.visitMutual`'s body-less arm two exits that register a
*body*: `Erasure.quotRealizer`'s, written down, and `Erasure.recursorRealizer`'s, synthesized
from the eliminated inductive. Neither is a `Erasure.visitExpr` output, so neither is covered
by the induction's own motives, and both enter the emitted environment — so the three output
conjuncts are owed of them separately. `Erasure.firstNonProofField` is stepped here too: it
is on the path of both `recursorRealizer` and `Erasure.visitCases`' propositional check.
-/

section Realizers

variable {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}

/-- `Erasure.mkAnonLambdas` at a successor: one binder around the rest. -/
theorem mkAnonLambdas_succ (n : Nat) (b : LBTerm) :
    mkAnonLambdas (n + 1) b = .lambda .anon (mkAnonLambdas n b) := by
  simp only [mkAnonLambdas, List.range_succ, List.foldl_append, List.foldl_cons,
    List.foldl_nil]

theorem noFix_mkAnonLambdas : ∀ (n : Nat) {b : LBTerm}, NoFix b → NoFix (mkAnonLambdas n b)
  | 0, _, h => h
  | n + 1, _, h => by
      rw [mkAnonLambdas_succ, NoFix_lambda]; exact noFix_mkAnonLambdas n h

theorem noBlock_mkAnonLambdas :
    ∀ (n : Nat) {b : LBTerm}, NoBlock b → NoBlock (mkAnonLambdas n b)
  | 0, _, h => h
  | n + 1, _, h => by
      rw [mkAnonLambdas_succ, NoBlock_lambda]; exact noBlock_mkAnonLambdas n h

theorem lbClosed_mkAnonLambdas : ∀ (n : Nat) {b : LBTerm} {k : Nat},
    LBClosed b (k + n) → LBClosed (mkAnonLambdas n b) k
  | 0, _, _, h => h
  | n + 1, b, k, h => by
      rw [mkAnonLambdas_succ, LBClosed_lambda]
      refine lbClosed_mkAnonLambdas n (b := b) (k := k + 1) ?_
      rwa [show k + 1 + n = k + (n + 1) by omega]

/-- A spine of de Bruijn indices below the bound keeps the term it is applied to closed.
The shape `Erasure.etaExpandFix` builds its applied core in. -/
theorem lbClosed_foldr_app {k : Nat} :
    ∀ (l : List Nat), (∀ m ∈ l, m < k) → ∀ t : LBTerm, LBClosed t k →
      LBClosed (l.foldr (fun m u => LBTerm.app u (.bvar m)) t) k
  | [], _, _, h => h
  | m :: rest, hm, t, h => by
      refine ⟨lbClosed_foldr_app rest (fun x hx => hm x (List.mem_cons_of_mem _ hx)) t h, ?_⟩
      exact hm m List.mem_cons_self

/-- **The η-expanded fixpoint a block registration writes is closed** (F-ETA). Its binders
are exactly the indices its own spine supplies, so no bound on `principalArgIdx` is needed —
unlike `Erasure.etaExpandFix_eq`, which pins the wrapper's shape. -/
theorem lbClosed_etaExpandFix {defs : List (@FixDef LBTerm)} {j : Nat}
    (h : ∀ m, LBClosed (LBTerm.fix defs j) m) : LBClosed (etaExpandFix defs j) 0 := by
  unfold etaExpandFix
  refine lbClosed_mkAnonLambdas _ (lbClosed_foldr_app _ (fun m hm => ?_) _ (h _))
  simpa using hm

/-- **The quotient realizer's shape.** Each of the four bodies is `□` or an anonymous
λ-telescope over indices it binds itself. -/
theorem quotRealizer_shape (k : QuotKind) :
    NoFix (quotRealizer k) ∧ LBClosed (quotRealizer k) 0 ∧ NoBlock (quotRealizer k) := by
  cases k with
  | type => exact ⟨NoFix_box, trivial, NoBlock_box⟩
  | ind => exact ⟨NoFix_box, trivial, NoBlock_box⟩
  | ctor =>
      exact ⟨noFix_mkAnonLambdas 3 (by simp), lbClosed_mkAnonLambdas 3 (by simp),
        noBlock_mkAnonLambdas 3 (by simp)⟩
  | lift =>
      exact ⟨noFix_mkAnonLambdas 6 (by simp), lbClosed_mkAnonLambdas 6 (by simp),
        noBlock_mkAnonLambdas 6 (by simp)⟩

/-- A left fold over an argument mask that only ever applies the accumulated term to another
one keeps the three output conjuncts, provided each step's argument has them. This is the
shape `Erasure.recursorRealizer`'s alternative body is built in. -/
theorem shape_foldl_app {β : Type} {k : Nat} (f : Nat × LBTerm → β → Nat × LBTerm)
    (hf : ∀ (p : Nat × LBTerm) (b : β), NoFix p.2 → LBClosed p.2 k → NoBlock p.2 →
      NoFix (f p b).2 ∧ LBClosed (f p b).2 k ∧ NoBlock (f p b).2)
    (as : Array β) (p : Nat × LBTerm)
    (h : NoFix p.2 ∧ LBClosed p.2 k ∧ NoBlock p.2) :
    NoFix (as.foldl f p).2 ∧ LBClosed (as.foldl f p).2 k ∧ NoBlock (as.foldl f p).2 :=
  Array.foldl_induction (motive := fun _ q => NoFix q.2 ∧ LBClosed q.2 k ∧ NoBlock q.2) h
    (fun _ q hq => hf q _ hq.1 hq.2.1 hq.2.2)

/-- **`Erasure.firstNonProofField`, stepped.** The proof test walks the constructors with
`Lean.getConstInfo` and one lifted `Lean.MetaM` computation per constructor, and writes
nothing, so a predicate closed under the family's steps crosses it. -/
theorem run_firstNonProofField_okW {Cfg : ErasureConfig → Prop}
    {P : ErasureState → Void IO.RealWorld → Prop} (H : RunClosedW Cfg P)
    {ind : InductiveVal} {r : Option (Name × Nat)} {s s₁ : ErasureState}
    {ctx : ErasureContext} {w w₁ : Void IO.RealWorld}
    (hrun : firstNonProofField ind s ctx cctx ref w = .ok (r, s₁) w₁) (hP : P s w) :
    P s₁ w₁ := by
  unfold firstNonProofField at hrun
  simp only [] at hrun
  rw [run_bind_ok] at hrun
  obtain ⟨acc, s₂, w₂, hloop, htail⟩ := hrun
  have hP₂ : P s₂ w₂ := by
    refine run_list_forIn_ok ctx cctx ref
      (P := fun _ s' w' => P s' w') _ _ _ _ _ hP ?_ _ _ _ hloop
    intro c _ a sa wa st sb wb hPa hb
    rw [run_bind_ok] at hb
    obtain ⟨ci, sc, wc, hci, hb⟩ := hb
    obtain rfl := run_getConstInfo_state _ _ cctx ref _ hci
    replace hPa := H.constInfo hci hPa
    cases ci
    case ctorInfo cv =>
      simp only [] at hb
      rw [run_bind_ok] at hb
      obtain ⟨found, sd, wd, hmeta, hb⟩ := hb
      replace hPa := H.metaM
        (PrimGenMono.forallBoundedTelescope _ _ _ _ _ fun _ _ => primGenMono_proofScan _)
        hmeta hPa
      cases found <;>
        (simp only [] at hb; rw [run_pure] at hb; cases hb; exact hPa)
    all_goals
      (simp only [] at hb
       rw [run_bind_ok] at hb
       obtain ⟨a0, s0, w0, hthr, -⟩ := hb
       exact absurd hthr (run_throwError_ne_ok _ ctx cctx ref _ _ _ _ _))
  obtain ⟨found, u⟩ := acc
  cases found <;>
    (simp only [] at htail; rw [run_pure] at htail; cases htail; exact hP₂)

/-- **`Erasure.recursorRealizer`, stepped.** Its only state- and world-touching calls are
`Lean.getConstInfo`, `Erasure.firstNonProofField` and the one `Erasure.register_inductive`
on the inductive the first of them returned; and when it returns a body, that body is
fix-free, de Bruijn closed and in applied form. Closedness rests on the arity's own `+ 1`:
the discriminee is the major premise's index `0`, and an alternative's minor-premise index
`numIndices + 1 + nargs` sits below `arity + nargs` because `numMotives` and `numMinors`
contribute at least the motive the first guard has tested for. -/
theorem run_recursorRealizer_okW {Cfg : ErasureConfig → Prop}
    {P : ErasureState → Void IO.RealWorld → Prop} (H : RunClosedW Cfg P)
    {rv : RecursorVal} {o : Option LBTerm} {s s₁ : ErasureState} {ctx : ErasureContext}
    {w w₁ : Void IO.RealWorld} (hcfg : Cfg ctx.config)
    (hrun : recursorRealizer rv s ctx cctx ref w = .ok (o, s₁) w₁) (hP : P s w) :
    P s₁ w₁ ∧ ∀ t, o = some t → NoFix t ∧ LBClosed t 0 ∧ NoBlock t := by
  have hnone : ∀ {s' : ErasureState} {w' : Void IO.RealWorld},
      (pure none : EraseM (Option LBTerm)) s' ctx cctx ref w' = .ok (o, s₁) w₁ →
      P s' w' → P s₁ w₁ ∧ ∀ t, o = some t → NoFix t ∧ LBClosed t 0 ∧ NoBlock t := by
    intro s' w' h hP'
    rw [run_pure] at h
    cases h
    exact ⟨hP', by simp⟩
  unfold recursorRealizer at hrun
  cases hall : rv.all with
  | nil => rw [hall] at hrun; simp only [] at hrun; exact hnone hrun hP
  | cons ind_name rest =>
  cases rest with
  | cons _ _ => rw [hall] at hrun; simp only [] at hrun; exact hnone hrun hP
  | nil =>
  rw [hall] at hrun
  simp only [] at hrun
  rw [run_bind_ok] at hrun
  obtain ⟨ci, s₂, w₂, hci, hrun⟩ := hrun
  obtain rfl := run_getConstInfo_state _ _ cctx ref _ hci
  replace hP := H.constInfo hci hP
  cases ci
  case' inductInfo ind =>
    simp only [] at hrun
    split at hrun
    case isFalse => exact hnone hrun hP
    case isTrue hg1 =>
    split at hrun
    case isFalse => exact hnone hrun hP
    case isTrue =>
    rw [run_bind_ok] at hrun
    obtain ⟨fnp, s₃, w₃, hfnp, hrun⟩ := hrun
    replace hP := run_firstNonProofField_okW H hfnp hP
    split at hrun
    case isTrue => exact hnone hrun hP
    case isFalse =>
    rw [run_bind_ok] at hrun
    obtain ⟨rr, s₄, w₄, hreg, hrun⟩ := hrun
    replace hP := H.reg (.inl ⟨ind_name, _, _, _, _, hci⟩) hcfg hreg hP
    obtain ⟨indid, argmasks⟩ := rr
    simp only [] at hrun
    rw [run_bind_ok] at hrun
    obtain ⟨alts, s₅, w₅, halts, hp⟩ := hrun
    -- the motive count the first guard tested, which puts the minor premise in scope
    have hmot : rv.numMotives = 1 := by
      simp only [Bool.and_eq_true, beq_iff_eq] at hg1
      exact hg1.2
    have hkey : P s₅ w₅ ∧ ∀ a ∈ alts, NoFix a.2 ∧
        LBClosed a.2 (rv.numParams + rv.numMotives + rv.numMinors + rv.numIndices + 1
          + a.1.length) ∧ NoBlock a.2 := by
      refine run_list_mapM_ok ctx cctx ref
        (P := fun (_ : List Name) (outs : List (List BinderName × LBTerm)) s' w' =>
          P s' w' ∧ ∀ a ∈ outs, NoFix a.2 ∧
            LBClosed a.2 (rv.numParams + rv.numMotives + rv.numMinors + rv.numIndices + 1
              + a.1.length) ∧ NoBlock a.2)
        ⟨hP, by intro a ha; simp at ha⟩ ?_ halts
      intro pre c post outs sa wa b sb wb _ hPa hb
      obtain ⟨hPa', hall'⟩ := hPa
      rw [run_bind_ok] at hb
      obtain ⟨cci, sc, wc, hcci, hb⟩ := hb
      obtain rfl := run_getConstInfo_state _ _ cctx ref _ hcci
      replace hPa' := H.constInfo hcci hPa'
      cases cci
      case ctorInfo cv =>
        simp only [] at hb
        rw [run_pure] at hb
        cases hb
        refine ⟨hPa', ?_⟩
        intro a ha
        rcases List.mem_append.mp ha with ha' | ha'
        · exact hall' a ha'
        · simp only [List.mem_singleton] at ha'
          subst ha'
          simp only [List.length_replicate]
          refine shape_foldl_app _ ?_ _ _ ⟨NoFix_bvar _, ?_, NoBlock_bvar _⟩
          · intro p r hnf hcl hnb
            obtain ⟨kept, u⟩ := p
            cases r with
            | keep =>
                refine ⟨⟨hnf, NoFix_bvar _⟩, ⟨hcl, ?_⟩, ⟨hnb, NoBlock_bvar _⟩⟩
                simp only [LBClosed_bvar]
                omega
            | erase => exact ⟨⟨hnf, NoFix_box⟩, ⟨hcl, trivial⟩, ⟨hnb, NoBlock_box⟩⟩
          · simp only [LBClosed_bvar]
            omega
      all_goals
        (simp only [] at hb
         exact absurd hb (run_throwError_ne_ok _ ctx cctx ref _ _ _ _ _))
    obtain ⟨hPfin, hallfin⟩ := hkey
    rw [run_pure] at hp
    cases hp
    refine ⟨hPfin, ?_⟩
    intro t ht
    cases ht
    refine ⟨noFix_mkAnonLambdas _ ?_, lbClosed_mkAnonLambdas _ ?_,
      noBlock_mkAnonLambdas _ ?_⟩
    · rw [NoFix_case]
      exact ⟨NoFix_bvar 0, fun a ha => (hallfin a ha).1⟩
    · rw [LBClosed_case, LBClosedAlts_iff]
      refine ⟨?_, fun a ha => ?_⟩
      · simp only [LBClosed_bvar]
        omega
      · rw [Nat.zero_add]
        exact (hallfin a ha).2.1
    · rw [NoBlock_case]
      exact ⟨NoBlock_bvar 0, fun a ha => (hallfin a ha).2.2⟩
  all_goals (simp only [] at hrun; exact hnone hrun hP)

/-- A term applied to a `□` per hypothesis keeps the three output conjuncts. The shape
`Erasure.visitCases` gives the catch-all alternative it erases once and reuses (F-SPARSE). -/
theorem shape_foldl_box {k : Nat} : ∀ (l : List Nat) (b : LBTerm),
    NoFix b → LBClosed b k → NoBlock b →
    NoFix (l.foldl (fun t _ => LBTerm.app t .box) b) ∧
      LBClosed (l.foldl (fun t _ => LBTerm.app t .box) b) k ∧
      NoBlock (l.foldl (fun t _ => LBTerm.app t .box) b)
  | [], _, h1, h2, h3 => ⟨h1, h2, h3⟩
  | _ :: rest, _, h1, h2, h3 =>
      shape_foldl_box rest _ ⟨h1, NoFix_box⟩ ⟨h2, trivial⟩ ⟨h3, NoBlock_box⟩

/-- **`Erasure.etaArgIsValue`, stepped.** One lifted relevance test and a pure disjunction.
The test is the relevance oracle, so the step is `RunClosedW.oracle`, which reads it at the
reader's own level scope — the scope both call sites hand it (`Erasure.lean:974`,
`Erasure.lean:998`). -/
theorem run_etaArgIsValue_okW {Cfg : ErasureConfig → Prop}
    {P : ErasureState → Void IO.RealWorld → Prop} (H : RunClosedW Cfg P)
    {lp : List Name} {a : Expr} {b : Bool} {s s₁ : ErasureState} {ctx : ErasureContext}
    {w w₁ : Void IO.RealWorld} (hlp : lp = ctx.lparams)
    (hrun : etaArgIsValue lp a s ctx cctx ref w = .ok (b, s₁) w₁) (hP : P s w) : P s₁ w₁ := by
  subst hlp
  unfold etaArgIsValue at hrun
  rw [run_bind_ok] at hrun
  obtain ⟨b0, s0, w0, hm, hp⟩ := hrun
  replace hP := H.oracle hm hP
  rw [run_pure] at hp
  cases hp
  exact hP

/-- **`Erasure.withEtaPrefixLets`, stepped** (F-ETA2). The η prefix binds each argument it
has already erased in a `let` outside the new binders, so the result is the continuation's
under one `.letIn` per entry: the three output conjuncts are the continuation's and the
entries' own. The continuation runs at a reader the binders extended, whose configuration is
the caller's, which is why `hk` quantifies it. -/
theorem run_withEtaPrefixLets_okW {Cfg : ErasureConfig → Prop}
    {P : ErasureState → Void IO.RealWorld → Prop} (H : RunClosedW Cfg P)
    {k : Array Expr → EraseM LBTerm}
    (hk : ∀ (args' : Array Expr) (ctx' : ErasureContext) (sa sb : ErasureState)
        (wa wb : Void IO.RealWorld) (t : LBTerm),
      Cfg ctx'.config → k args' sa ctx' cctx ref wa = .ok (t, sb) wb →
      P sa wa → P sb wb ∧ NoFix t ∧ LBClosed t 0 ∧ NoBlock t) :
    ∀ (bs : List (Nat × Expr × LBTerm)) (args : Array Expr) (s : ErasureState)
      (ctx : ErasureContext) (w : Void IO.RealWorld) (t : LBTerm) (s' : ErasureState)
      (w' : Void IO.RealWorld),
      (∀ b ∈ bs, NoFix b.2.2 ∧ LBClosed b.2.2 0 ∧ NoBlock b.2.2) →
      Cfg ctx.config → P s w →
      withEtaPrefixLets bs args k s ctx cctx ref w = .ok (t, s') w' →
      P s' w' ∧ NoFix t ∧ LBClosed t 0 ∧ NoBlock t
  | [], args, s, ctx, w, t, s', w', _, hcfg, hP, hrun => hk args ctx s s' w w' t hcfg hrun hP
  | b :: rest, args, s, ctx, w, t, s', w', hbs, hcfg, hP, hrun => by
      obtain ⟨i, ty, v⟩ := b
      rw [withEtaPrefixLets] at hrun
      obtain ⟨x, ctx', w₀, hcf, hP', hk'⟩ :=
        run_withLocalDecl_okW (fun h hq => H.fresh h hq) hP hrun
      have hcfg' : Cfg ctx'.config := by rw [hcf]; exact hcfg
      rw [run_bind_ok] at hk'
      obtain ⟨body, sb, wb, hbody, hm⟩ := hk'
      obtain ⟨hPb, hnf, hcl, hnb⟩ :=
        run_withEtaPrefixLets_okW H hk rest _ _ _ _ _ _ _
          (fun q hq => hbs q (List.mem_cons_of_mem _ hq)) hcfg' hP' hbody
      obtain ⟨hs, hw, nm, rfl⟩ := run_mkLetIn_ok hm
      subst hs
      subst hw
      obtain ⟨hnfv, hclv, hnbv⟩ := hbs (i, ty, v) List.mem_cons_self
      exact ⟨hPb, ⟨hnfv, noFix_toBvar x 0 hnf⟩, ⟨hclv, lbClosed_toBvar x 0 hcl⟩,
        ⟨hnbv, noBlock_toBvar x 0 hnb⟩⟩

end Realizers

/-! ## The registration exits, world-indexed and configuration-aware

`ErasureRun.lean`'s world-indexed exit rules quantify the reader of the body erasure
universally, which is one reader too many here: the two clauses `RunClosedW` conditions on
the configuration are read at exactly that reader. The two rules below are the same
decompositions with the reader's configuration tracked through `Erasure.visitMutual`'s own
`withReader` updates, which change the local context, the fixvar map and the level scope and
leave `config` alone — the hypotheses `hf`/`hg`, discharged by `rfl` at the call sites.
-/

section ExitsW

variable {Cfg : ErasureConfig → Prop} {P : ErasureState → Void IO.RealWorld → Prop}
  {n : Name} {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}

/-- **The non-recursive exit, world-indexed.** `run_nonrec_exit_ok'` with the body erasure's
reader pinned to the caller's configuration. -/
theorem run_nonrec_exit_okW {vE : Expr → EraseM LBTerm} {f : ErasureContext → ErasureContext}
    {e : Expr} {b1 b2 : ErasureContext → LBTerm → Bool} {msg1 msg2 : MessageData}
    {s : ErasureState} {ctx : ErasureContext} {w : Void IO.RealWorld}
    {u : Unit} {s₁ : ErasureState} {w₁ : Void IO.RealWorld}
    (hrun : (do
        let t ← withReader f (do let pe ← prepare_erasure e; vE pe)
        checkKernameFresh n (toKername n)
        modify (fun s => { s with
          constants := s.constants.insert n (toKername n),
          gdecls := (toKername n, .constantDecl ⟨some t⟩) :: s.gdecls })
        let c ← read
        if b1 c t = true then do
          let isInst ← liftM (Lean.Meta.isInstance n)
          if isInst = true then do
            logInfo msg1
            modify (fun s => { s with inlinings := toKername n :: s.inlinings })
          else if b2 c t = true then do
            logInfo msg2
            modify (fun s => { s with inlinings := toKername n :: s.inlinings })
          else pure ()
        else pure () : EraseM Unit) s ctx cctx ref w = .ok (u, s₁) w₁)
    (hcfg : Cfg ctx.config) (hP : P s w)
    (hinl : ∀ {s' : ErasureState} {w' : Void IO.RealWorld} {kn : Kername},
      P s' w' → P { s' with inlinings := kn :: s'.inlinings } w')
    (hlog : ∀ {m : MessageData} {u' : Unit} {s' s'' : ErasureState} {ctx' : ErasureContext}
        {w' w'' : Void IO.RealWorld},
      (logInfo m : EraseM Unit) s' ctx' cctx ref w' = .ok (u', s'') w'' → P s' w' → P s'' w'')
    (hinst : ∀ {m : Name} {b : Bool} {s' s'' : ErasureState} {ctx' : ErasureContext}
        {w' w'' : Void IO.RealWorld},
      (liftM (Lean.Meta.isInstance m) : EraseM Bool) s' ctx' cctx ref w' = .ok (b, s'') w'' →
        P s' w' → P s'' w'')
    (hprep : ∀ {v pe : Expr} {sa sb : ErasureState} {ctx' : ErasureContext}
        {wa wb : Void IO.RealWorld},
      Cfg ctx'.config → prepare_erasure v sa ctx' cctx ref wa = .ok (pe, sb) wb →
      P sa wa → P sb wb)
    (hvE : ∀ {pe : Expr} {sb sc : ErasureState} {ctx' : ErasureContext}
        {wb wc : Void IO.RealWorld} {t : LBTerm},
      Cfg ctx'.config → vE pe sb ctx' cctx ref wb = .ok (t, sc) wc →
      P sb wb → P sc wc ∧ NoFix t ∧ LBClosed t 0 ∧ NoBlock t)
    (hnr : ∀ {s' : ErasureState} {w' : Void IO.RealWorld} {t : LBTerm},
      P s' w' → NoFix t → LBClosed t 0 → NoBlock t → P (nonrecConstState n t s') w')
    (hf : ∀ c : ErasureContext, (f c).config = c.config) : P s₁ w₁ := by
  have hcf : Cfg (f ctx).config := by rw [hf]; exact hcfg
  rw [run_bind_ok] at hrun
  obtain ⟨t, st, wt, hvis, hrun⟩ := hrun
  rw [run_withReader, run_bind_ok] at hvis
  obtain ⟨pe, sp, wp, hpr, hvis⟩ := hvis
  obtain ⟨hP', hnf, hcl, hnb⟩ := hvE hcf hvis (hprep hcf hpr hP)
  rw [run_bind_ok] at hrun
  obtain ⟨ug, sg, wg, hguard, hrun⟩ := hrun
  obtain ⟨hsg, hwg, -⟩ := run_checkKernameFresh_ok hguard
  subst sg
  subst wg
  rw [run_bind_ok] at hrun
  obtain ⟨u2, sm, wm, hmod, hrun⟩ := hrun
  rw [run_modify] at hmod
  cases hmod
  replace hP' := hnr hP' hnf hcl hnb
  rw [run_bind_ok] at hrun
  obtain ⟨c2, sc, wc, hread, hrun⟩ := hrun
  rw [run_read] at hread
  cases hread
  exact run_inline_tail_ok' hinl hlog hinst hP' hrun

/-- **The block exit, world-indexed.** `run_rec_exit_ok'` with the same reader pinning, at
the two `withReader` updates the block loop makes. -/
theorem run_rec_exit_okW {vE : Expr → EraseM LBTerm} {names fixnames : List Name}
    {f : List FVarId → ErasureContext → ErasureContext}
    {g : ConstantInfo → ErasureContext → ErasureContext} {val : ConstantInfo → Expr}
    {msg : MessageData}
    {s : ErasureState} {ctx : ErasureContext} {w : Void IO.RealWorld}
    {u : Unit} {s₁ : ErasureState} {w₁ : Void IO.RealWorld}
    (hrun : (do
        let ids ← names.mapM (fun _ => mkFreshFVarId)
        unless (fixnames.map toKername).Nodup do
          throwError msg
        withReader (f ids) (do
          let defs ← names.mapM (fun m => do
            let ci ← getConstInfo m
            let t ← withReader (g ci) (do let pe ← prepare_erasure (val ci); vE pe)
            mkDef (remove_unsafe_rec m) fixnames t)
          for p in fixnames.zipIdx do
            checkKernameFresh p.1 (toKername p.1)
            modify (fun s => { s with
              constants := s.constants.insert p.1 (toKername p.1),
              gdecls := (toKername p.1,
                .constantDecl ⟨some (etaExpandFix defs p.2)⟩) :: s.gdecls })
          pure ()) : EraseM Unit) s ctx cctx ref w = .ok (u, s₁) w₁)
    (hcfg : Cfg ctx.config) (hP : P s w)
    (hfresh : ∀ {x : FVarId} {s' s'' : ErasureState} {ctx' : ErasureContext}
        {w' w'' : Void IO.RealWorld},
      (mkFreshFVarId : EraseM FVarId) s' ctx' cctx ref w' = .ok (x, s'') w'' →
        P s' w' → P s'' w'')
    (hci : ∀ {m : Name} {ci : ConstantInfo} {s' s'' : ErasureState} {ctx' : ErasureContext}
        {w' w'' : Void IO.RealWorld},
      (getConstInfo m : EraseM ConstantInfo) s' ctx' cctx ref w' = .ok (ci, s'') w'' →
        P s' w' → P s'' w'')
    (hprep : ∀ {v pe : Expr} {sa sb : ErasureState} {ctx' : ErasureContext}
        {wa wb : Void IO.RealWorld},
      Cfg ctx'.config → prepare_erasure v sa ctx' cctx ref wa = .ok (pe, sb) wb →
      P sa wa → P sb wb)
    (hvE : ∀ {pe : Expr} {sb sc : ErasureState} {ctx' : ErasureContext}
        {wb wc : Void IO.RealWorld} {t : LBTerm},
      Cfg ctx'.config → vE pe sb ctx' cctx ref wb = .ok (t, sc) wc →
      P sb wb → P sc wc ∧ NoFix t ∧ LBClosed t 0 ∧ NoBlock t)
    (hrec : ∀ {s' : ErasureState} {w' : Void IO.RealWorld} {defs : List (@FixDef LBTerm)},
      P s' w' → defs.length = names.length →
      (∀ d ∈ defs, ∃ (t : LBTerm) (fv : Name → FVarId), (LBClosed t 0 ∧ NoBlock t) ∧
        d.body = fixnames.reverse.zipIdx.foldl (fun b p => toBvar (fv p.1) p.2 b) t) →
      P (recConstState fixnames defs s') w')
    (hf : ∀ (ids : List FVarId) (c : ErasureContext), (f ids c).config = c.config)
    (hg : ∀ (ci : ConstantInfo) (c : ErasureContext), (g ci c).config = c.config) :
    P s₁ w₁ := by
  rw [run_bind_ok] at hrun
  obtain ⟨ids, sid, wid, hids, hrun⟩ := hrun
  replace hP := run_list_mapM_ok _ cctx ref
    (P := fun (_ : List Name) (_ : List FVarId) (s' : ErasureState)
        (w' : Void IO.RealWorld) => P s' w')
    hP
    (fun _ _ _ _ _ _ _ _ _ _ hPa hb => hfresh hb hPa)
    hids
  split at hrun
  case isFalse =>
    rw [run_bind_ok] at hrun
    obtain ⟨a0, s0, w0, hthr, -⟩ := hrun
    exact absurd hthr (run_throwError_ne_ok _ ctx cctx ref _ _ _ _ _)
  dsimp only [] at hrun
  rw [run_withReader, run_bind_ok] at hrun
  obtain ⟨defs, sd, wd, hdefs, hrun⟩ := hrun
  have hcf : Cfg (f ids ctx).config := by rw [hf]; exact hcfg
  replace hP := run_list_mapM_ok _ cctx ref
    (P := fun (pre : List Name) (outs : List (@FixDef LBTerm)) (s' : ErasureState)
        (w' : Void IO.RealWorld) => P s' w' ∧ outs.length = pre.length ∧
      ∀ d ∈ outs, ∃ (t : LBTerm) (fv : Name → FVarId), (LBClosed t 0 ∧ NoBlock t) ∧
        d.body = fixnames.reverse.zipIdx.foldl (fun b p => toBvar (fv p.1) p.2 b) t)
    ⟨hP, rfl, by simp⟩
    (fun pre x post outs _ _ b _ _ _ hPa hb => by
      obtain ⟨hPa', hlena, hbodies⟩ := hPa
      rw [run_bind_ok] at hb
      obtain ⟨ci, s2, w2, hci', hb⟩ := hb
      replace hPa' := hci hci' hPa'
      rw [run_bind_ok] at hb
      obtain ⟨t2, s4, w4, hvis2, hb⟩ := hb
      rw [run_withReader, run_bind_ok] at hvis2
      obtain ⟨pe2, s3, w3, hpr2, hvis2⟩ := hvis2
      have hcg : Cfg (g ci (f ids ctx)).config := by rw [hg]; exact hcf
      obtain ⟨hP4, -, hcl4⟩ := hvE hcg hvis2 (hprep hcg hpr2 hPa')
      obtain ⟨-, hbody, hs5, hw5⟩ := run_mkDef_ok hb
      subst hs5
      subst hw5
      refine ⟨hP4, by simp [hlena], ?_⟩
      intro d hd
      rcases List.mem_append.mp hd with hd' | hd'
      · exact hbodies d hd'
      · simp only [List.mem_singleton] at hd'
        subst hd'
        exact ⟨t2, fun nm => (f ids ctx).fixvars.get![nm]!, hcl4, hbody⟩)
    hdefs
  rw [run_bind_ok] at hrun
  obtain ⟨u4, sf, wf, hloop, hrun⟩ := hrun
  obtain ⟨hsf, hwf, -⟩ := run_checkFresh_modify_forIn_ok hloop
  subst hsf
  subst hwf
  rw [run_pure] at hrun
  cases hrun
  exact hrec hP.1 hP.2.1 hP.2.2

end ExitsW

/-! ## The world-indexed induction -/

set_option maxHeartbeats 4000000 in
/-- **The world-indexed output-shape induction, all eighteen motives.** From
`RunClosedW Cfg P`: at a reader whose configuration satisfies `Cfg`, every successful run of a
member of the erasure family carries `P` from its entry state and world to its exit state and
world, and every one that returns a λ□ term returns a fix-free, de Bruijn closed term in
applied form. `visitExpr_shape` is its `Cfg`-free, world-blind instance. -/
theorem visitExpr_shapeW {Cfg : ErasureConfig → Prop}
    {P : ErasureState → Void IO.RealWorld → Prop} (H : RunClosedW Cfg P) :
    (∀ e s ctx cctx ref w t s' w', visitExpr e s ctx cctx ref w = .ok (t, s') w' →
      ShapeCW Cfg P ctx s w s' w' t) ∧
    (∀ l s ctx cctx ref w t s' w', visitLiteral l s ctx cctx ref w = .ok (t, s') w' →
      ShapeCW Cfg P ctx s w s' w' t) ∧
    (∀ cn args s ctx cctx ref w t s' w',
      visitConstructor cn args s ctx cctx ref w = .ok (t, s') w' → ShapeCW Cfg P ctx s w s' w' t) ∧
    (∀ e s ctx cctx ref w t s' w', visitConst e s ctx cctx ref w = .ok (t, s') w' →
      ShapeCW Cfg P ctx s w s' w' t) ∧
    (∀ n s ctx cctx ref w r s' w',
      get_constant_kername n s ctx cctx ref w = .ok (r, s') w' → P s w → Cfg ctx.config → P s' w') ∧
    (∀ n s ctx cctx ref w r s' w', visitMutual n s ctx cctx ref w = .ok (r, s') w' →
      P s w → Cfg ctx.config → P s' w') ∧
    (∀ t0 args s ctx cctx ref w t s' w',
      visitAppArgs t0 args s ctx cctx ref w = .ok (t, s') w' →
      NoFix t0 → LBClosed t0 0 → NoBlock t0 → ShapeCW Cfg P ctx s w s' w' t) ∧
    (∀ e s ctx cctx ref w t s' w', visitLet e s ctx cctx ref w = .ok (t, s') w' →
      ShapeCW Cfg P ctx s w s' w' t) ∧
    (∀ e s ctx cctx ref w t s' w', visitLambda e s ctx cctx ref w = .ok (t, s') w' →
      ShapeCW Cfg P ctx s w s' w' t) ∧
    (∀ tn i e s ctx cctx ref w t s' w',
      visitProj tn i e s ctx cctx ref w = .ok (t, s') w' → ShapeCW Cfg P ctx s w s' w' t) ∧
    (∀ e s ctx cctx ref w t s' w', visitApp e s ctx cctx ref w = .ok (t, s') w' →
      ShapeCW Cfg P ctx s w s' w' t) ∧
    (∀ e s ctx cctx ref w t s' w', visitConstApp e s ctx cctx ref w = .ok (t, s') w' →
      ShapeCW Cfg P ctx s w s' w' t) ∧
    (∀ cn ar e s ctx cctx ref w t s' w',
      visitCtorEta cn ar e s ctx cctx ref w = .ok (t, s') w' → ShapeCW Cfg P ctx s w s' w' t) ∧
    (∀ cn ar ty fe args s ctx cctx ref w t s' w',
      visitCtorEtaGo cn ar ty fe args s ctx cctx ref w = .ok (t, s') w' →
      ShapeCW Cfg P ctx s w s' w' t) ∧
    (∀ ci e s ctx cctx ref w t s' w',
      visitCasesEta ci e s ctx cctx ref w = .ok (t, s') w' → ShapeCW Cfg P ctx s w s' w' t) ∧
    (∀ ci ty fe args s ctx cctx ref w t s' w',
      visitCasesEtaGo ci ty fe args s ctx cctx ref w = .ok (t, s') w' →
      ShapeCW Cfg P ctx s w s' w' t) ∧
    (∀ ci args s ctx cctx ref w t s' w',
      visitCases ci args s ctx cctx ref w = .ok (t, s') w' → ShapeCW Cfg P ctx s w s' w' t) ∧
    (∀ nf mask e s ctx cctx ref w r s' w',
      visitAlt nf mask e s ctx cctx ref w = .ok (r, s') w' →
      P s w → Cfg ctx.config → P s' w' ∧ NoFix r.2 ∧ LBClosed r.2 r.1.length ∧ NoBlock r.2) := by
  apply visitExpr.mutual_fixpoint_induct
    (motive_1 := fun f => ∀ e s ctx cctx ref w t s' w',
      f e s ctx cctx ref w = .ok (t, s') w' → ShapeCW Cfg P ctx s w s' w' t)
    (motive_2 := fun f => ∀ l s ctx cctx ref w t s' w',
      f l s ctx cctx ref w = .ok (t, s') w' → ShapeCW Cfg P ctx s w s' w' t)
    (motive_3 := fun f => ∀ cn args s ctx cctx ref w t s' w',
      f cn args s ctx cctx ref w = .ok (t, s') w' → ShapeCW Cfg P ctx s w s' w' t)
    (motive_4 := fun f => ∀ e s ctx cctx ref w t s' w',
      f e s ctx cctx ref w = .ok (t, s') w' → ShapeCW Cfg P ctx s w s' w' t)
    (motive_5 := fun f => ∀ n s ctx cctx ref w r s' w',
      f n s ctx cctx ref w = .ok (r, s') w' → P s w → Cfg ctx.config → P s' w')
    (motive_6 := fun f => ∀ n s ctx cctx ref w r s' w',
      f n s ctx cctx ref w = .ok (r, s') w' → P s w → Cfg ctx.config → P s' w')
    (motive_7 := fun f => ∀ t0 args s ctx cctx ref w t s' w',
      f t0 args s ctx cctx ref w = .ok (t, s') w' → NoFix t0 → LBClosed t0 0 → NoBlock t0 →
      ShapeCW Cfg P ctx s w s' w' t)
    (motive_8 := fun f => ∀ e s ctx cctx ref w t s' w',
      f e s ctx cctx ref w = .ok (t, s') w' → ShapeCW Cfg P ctx s w s' w' t)
    (motive_9 := fun f => ∀ e s ctx cctx ref w t s' w',
      f e s ctx cctx ref w = .ok (t, s') w' → ShapeCW Cfg P ctx s w s' w' t)
    (motive_10 := fun f => ∀ tn i e s ctx cctx ref w t s' w',
      f tn i e s ctx cctx ref w = .ok (t, s') w' → ShapeCW Cfg P ctx s w s' w' t)
    (motive_11 := fun f => ∀ e s ctx cctx ref w t s' w',
      f e s ctx cctx ref w = .ok (t, s') w' → ShapeCW Cfg P ctx s w s' w' t)
    (motive_12 := fun f => ∀ e s ctx cctx ref w t s' w',
      f e s ctx cctx ref w = .ok (t, s') w' → ShapeCW Cfg P ctx s w s' w' t)
    (motive_13 := fun f => ∀ cn ar e s ctx cctx ref w t s' w',
      f cn ar e s ctx cctx ref w = .ok (t, s') w' → ShapeCW Cfg P ctx s w s' w' t)
    (motive_14 := fun f => ∀ cn ar ty fe args s ctx cctx ref w t s' w',
      f cn ar ty fe args s ctx cctx ref w = .ok (t, s') w' → ShapeCW Cfg P ctx s w s' w' t)
    (motive_15 := fun f => ∀ ci e s ctx cctx ref w t s' w',
      f ci e s ctx cctx ref w = .ok (t, s') w' → ShapeCW Cfg P ctx s w s' w' t)
    (motive_16 := fun f => ∀ ci ty fe args s ctx cctx ref w t s' w',
      f ci ty fe args s ctx cctx ref w = .ok (t, s') w' → ShapeCW Cfg P ctx s w s' w' t)
    (motive_17 := fun f => ∀ ci args s ctx cctx ref w t s' w',
      f ci args s ctx cctx ref w = .ok (t, s') w' → ShapeCW Cfg P ctx s w s' w' t)
    (motive_18 := fun f => ∀ nf mask e s ctx cctx ref w r s' w',
      f nf mask e s ctx cctx ref w = .ok (r, s') w' →
      P s w → Cfg ctx.config → P s' w' ∧ NoFix r.2 ∧ LBClosed r.2 r.1.length ∧ NoBlock r.2)
  · exact eraseM_admissible_ok₁ _
  · exact eraseM_admissible_ok₁ _
  · exact eraseM_admissible_ok₂ _
  · exact eraseM_admissible_ok₁ _
  · exact eraseM_admissible_ok₁ _
  · exact eraseM_admissible_ok₁ _
  · exact eraseM_admissible_ok₂ _
  · exact eraseM_admissible_ok₁ _
  · exact eraseM_admissible_ok₁ _
  · exact eraseM_admissible_ok₃ _
  · exact eraseM_admissible_ok₁ _
  · exact eraseM_admissible_ok₁ _
  · exact eraseM_admissible_ok₃ _
  · exact eraseM_admissible_ok₅ _
  · exact eraseM_admissible_ok₂ _
  · exact eraseM_admissible_ok₄ _
  · exact eraseM_admissible_ok₂ _
  · exact eraseM_admissible_ok₃ _
  -- Step 1: visitExpr
  · intro vE vLit vLet vLam vProj vApp ih1 ih2 ih8 ih9 ih10 ih11
    intro e s ctx cctx ref w t s' w' hrun hP hcfg
    simp only [] at hrun
    rw [run_read_bind, run_bind_ok] at hrun
    obtain ⟨c, s₁, w₁, horc, hk⟩ := hrun
    have hs₁ : s₁ = s := run_liftMetaM_state _ _ _ _ _ horc
    subst hs₁
    replace hP := H.oracle horc hP
    by_cases hc : c = true
    · rw [if_pos hc] at hk
      rw [run_pure] at hk
      cases hk
      exact ⟨hP, noFix_default, lbClosed_default 0, noBlock_default⟩
    · rw [if_neg hc] at hk
      cases e <;> (try simp only [] at hk)
      case app f a => exact ih11 _ _ _ _ _ _ _ _ _ hk hP hcfg
      case const nm us => exact ih11 _ _ _ _ _ _ _ _ _ hk hP hcfg
      case proj tn i b => exact ih10 _ _ _ _ _ _ _ _ _ _ _ hk hP hcfg
      case mdata d b => exact ih1 _ _ _ _ _ _ _ _ _ hk hP hcfg
      case lam bn ty bd bi => exact ih9 _ _ _ _ _ _ _ _ _ hk hP hcfg
      case letE bn ty v bd nd => exact ih8 _ _ _ _ _ _ _ _ _ hk hP hcfg
      case lit l => exact ih2 _ _ _ _ _ _ _ _ _ hk hP hcfg
      case fvar x =>
        rw [run_pure] at hk
        cases hk
        exact ⟨hP, NoFix_fvar _, by simp, trivial⟩
      all_goals
        (rw [run_panicWithPosWithDecl] at hk
         cases hk
         exact ⟨hP, noFix_default, lbClosed_default 0, noBlock_default⟩)
  -- Step 2: visitLiteral
  · intro vCtor ih3
    intro l s ctx cctx ref w t s' w' hrun hP hcfg
    simp only [] at hrun
    rw [run_read_bind] at hrun
    cases hn : ctx.config.nat with
    | peano =>
      rw [hn] at hrun
      cases l with
      | natVal n =>
        cases n with
        | zero =>
          simp only [] at hrun
          exact ih3 _ _ _ _ _ _ _ _ _ _ hrun hP hcfg
        | succ m =>
          simp only [] at hrun
          exact ih3 _ _ _ _ _ _ _ _ _ _ hrun hP hcfg
      | strVal ss =>
        simp only [] at hrun
        rw [run_panicWithPosWithDecl] at hrun
        cases hrun
        exact ⟨hP, noFix_default, lbClosed_default 0, noBlock_default⟩
    | machine =>
      rw [hn] at hrun
      cases l with
      | natVal n =>
        simp only [] at hrun
        split at hrun
        · rw [run_pure] at hrun
          cases hrun
          exact ⟨hP, NoFix_prim _, by simp, trivial⟩
        · rw [run_panicWithPosWithDecl] at hrun
          cases hrun
          exact ⟨hP, noFix_default, lbClosed_default 0, noBlock_default⟩
      | strVal ss =>
        simp only [] at hrun
        rw [run_panicWithPosWithDecl] at hrun
        cases hrun
        exact ⟨hP, noFix_default, lbClosed_default 0, noBlock_default⟩
  -- Step 3: visitConstructor
  · intro vLit vConst vAA ih2 ih4 ih7
    intro cn args s ctx cctx ref w t s' w' hrun hP hcfg
    simp only [] at hrun
    rw [run_bind_ok] at hrun
    obtain ⟨ci, s₁, w₁, hgc, hrun⟩ := hrun
    have h1 := run_getConstInfo_state _ _ cctx ref _ hgc
    subst h1
    replace hP := H.constInfo hgc hP
    cases ci
    case ctorInfo info =>
      simp only [] at hrun
      rw [run_bind_ok] at hrun
      obtain ⟨ci2, s₂, w₂, hgc2, hrun⟩ := hrun
      have h2 := run_getConstInfo_state _ _ cctx ref _ hgc2
      subst h2
      replace hP := H.constInfo hgc2 hP
      cases ci2
      case inductInfo indinfo =>
        simp only [] at hrun
        rw [run_bind_ok] at hrun
        obtain ⟨rr, s₃, w₃, hreg, hrun⟩ := hrun
        have hP3 := H.reg (Or.inl ⟨_, _, _, _, _, hgc2⟩) hcfg hreg hP
        obtain ⟨indid, argmasks⟩ := rr
        simp only [] at hrun
        rw [run_bind_ok] at hrun
        obtain ⟨env, s₄, w₄, henv, hrun⟩ := hrun
        have h4 := run_getEnv_state _ _ cctx ref _ henv
        subst h4
        replace hP3 := H.getEnv henv hP3
        rw [run_bind_ok] at hrun
        obtain ⟨c0, s₅, w₅, hrd, hrun⟩ := hrun
        rw [run_read] at hrd
        cases hrd
        split at hrun
        · exact ih7 _ _ _ _ _ _ _ _ _ _ hrun (NoFix_const _) (by simp) trivial hP3 hcfg
        · rw [run_bind_ok] at hrun
          obtain ⟨c1, s₆, w₆, hrd2, hrun⟩ := hrun
          rw [run_read] at hrd2
          cases hrd2
          rcases visitConstructor_match_quad (α := EraseM LBTerm) _ _ _ _ _ _
            with hm | hm | hm | hm <;> rw [hm] at hrun <;> (try simp only [] at hrun)
          · -- machine / Nat.zero
            split at hrun
            · exact ih2 _ _ _ _ _ _ _ _ _ hrun hP3 hcfg
            · rw [run_bind_ok] at hrun
              obtain ⟨up, s₇, w₇, hp, hrun⟩ := hrun
              rw [run_panic] at hp
              cases hp
              exact ih2 _ _ _ _ _ _ _ _ _ hrun hP3 hcfg
          · -- machine / Nat.succ
            have hsucc : ∀ {sX : ErasureState} {wX : Void IO.RealWorld},
                P sX wX →
                (do let nat_add ← vConst (Expr.const ``Nat.add [])
                    vAA nat_add #[args[0]!, Expr.lit (Literal.natVal 1)] : EraseM LBTerm)
                  sX ctx cctx ref wX = .ok (t, s') w' →
                P s' w' ∧ NoFix t ∧ LBClosed t 0 ∧ NoBlock t := by
              intro sX wX hPX hh
              rw [run_bind_ok] at hh
              obtain ⟨na, sY, wY, hna, hh⟩ := hh
              obtain ⟨hPY, hnfa, hcla, hnba⟩ := ih4 _ _ _ _ _ _ _ _ _ hna hPX hcfg
              exact ih7 _ _ _ _ _ _ _ _ _ _ hh hnfa hcla hnba hPY hcfg
            split at hrun
            · exact hsucc hP3 hrun
            · rw [run_bind_ok] at hrun
              obtain ⟨up, s₇, w₇, hp, hrun⟩ := hrun
              rw [run_panic] at hp
              cases hp
              exact hsucc hP3 hrun
          · exact ih7 _ _ _ _ _ _ _ _ _ _ hrun (NoFix_construct _ _ _) (by simp [LBClosedArgs])
              (NoBlock_construct_nil _ _) hP3 hcfg
          · exact ih7 _ _ _ _ _ _ _ _ _ _ hrun (NoFix_construct _ _ _) (by simp [LBClosedArgs])
              (NoBlock_construct_nil _ _) hP3 hcfg
      all_goals
        (simp only [] at hrun
         rw [run_panicWithPosWithDecl] at hrun
         cases hrun
         exact ⟨hP, noFix_default, lbClosed_default 0, noBlock_default⟩)
    all_goals
      (simp only [] at hrun
       rw [run_panicWithPosWithDecl] at hrun
       cases hrun
       exact ⟨hP, noFix_default, lbClosed_default 0, noBlock_default⟩)
  -- Step 4: visitConst
  · intro gck ih5
    intro e s ctx cctx ref w t s' w' hrun hP hcfg
    simp only [] at hrun
    cases e <;> (try simp only [] at hrun)
    case const nm us =>
      rw [run_bind_ok] at hrun
      obtain ⟨c, s₁, w₁, hrd, hk⟩ := hrun
      rw [run_read] at hrd
      cases hrd
      cases hopt : ctx.fixvars.bind (fun hmap => hmap[nm]?) with
      | some id =>
        rw [hopt] at hk
        simp only [] at hk
        rw [run_pure] at hk
        cases hk
        exact ⟨hP, NoFix_fvar _, by simp, trivial⟩
      | none =>
        rw [hopt] at hk
        simp only [] at hk
        rw [run_bind_ok] at hk
        obtain ⟨kn, s₂, w₂, hgck, hp⟩ := hk
        rw [run_pure] at hp
        cases hp
        exact ⟨ih5 _ _ _ _ _ _ _ _ _ hgck hP hcfg, NoFix_const _, by simp, trivial⟩
    all_goals
      (rw [run_panicWithPosWithDecl] at hrun
       cases hrun
       exact ⟨hP, noFix_default, lbClosed_default 0, noBlock_default⟩)
  -- Step 5: get_constant_kername
  · intro vMut ih6
    intro n s ctx cctx ref w r s' w' hrun hP hcfg
    simp only [] at hrun
    rw [run_bind_ok] at hrun
    obtain ⟨s₀, s₁, w₁, hget, hk⟩ := hrun
    rw [run_get] at hget
    cases hget
    cases hcs : s.constants.get? n with
    | some kn =>
      rw [hcs] at hk
      simp only [] at hk
      rw [run_pure] at hk
      cases hk
      exact hP
    | none =>
      rw [hcs] at hk
      simp only [] at hk
      rw [run_bind_ok] at hk
      obtain ⟨uu, s₂, w₂, hvm, hk2⟩ := hk
      rw [run_bind_ok] at hk2
      obtain ⟨s₃, s₄, w₄, hget2, hp⟩ := hk2
      rw [run_get] at hget2
      cases hget2
      rw [run_pure] at hp
      cases hp
      exact ih6 _ _ _ _ _ _ _ _ _ hvm hP hcfg
  -- Step 6: visitMutual
  · intro vE ih1
    intro n s ctx cctx ref w u s₁ w₁ hrun hP hcfg
    have hvE : ∀ {pe : Expr} {sb sc : ErasureState} {ctx' : ErasureContext}
        {wb wc : Void IO.RealWorld} {tt : LBTerm},
        Cfg ctx'.config → vE pe sb ctx' cctx ref wb = .ok (tt, sc) wc →
        P sb wb → P sc wc ∧ NoFix tt ∧ LBClosed tt 0 ∧ NoBlock tt :=
      fun hc h hp => ih1 _ _ _ _ _ _ _ _ _ h hp hc
    simp only [] at hrun
    rw [run_bind_ok] at hrun
    obtain ⟨di, sa, wa, hdi, hrun⟩ := hrun
    have hsa := run_liftCoreM_state (x := (Compiler.LCNF.getDeclInfo? n : CoreM _))
      _ _ cctx ref _ hdi
    subst hsa
    replace hP := H.declInfo hdi hP
    rw [run_bind_ok] at hrun
    obtain ⟨env0, sb, wb, henv0, hrun⟩ := hrun
    have hsb := run_getEnv_state _ _ cctx ref _ henv0
    subst hsb
    replace hP := H.getEnv henv0 hP
    clear hdi henv0
    split at hrun
    case isTrue =>
      refine run_inline_prefix_ok' ?_ ?_ ?_ hP hrun
      · exact fun hq => H.inl hq
      · exact fun h hq => H.logInfo h hq
      intro s' w' u' s'' w'' hP' hm
      rw [run_bind_ok] at hm
      obtain ⟨env2, se, we, henv2, hm⟩ := hm
      have hz := run_getEnv_state _ _ cctx ref _ henv2
      subst hz
      replace hP' := H.getEnv henv2 hP'
      rw [run_bind_ok] at hm
      obtain ⟨c1, sr, wr, hread, hm⟩ := hm
      rw [run_read] at hread
      cases hread
      cases hval : di.get!.value? (allowOpaque := true) with
      | none =>
        simp only [hval] at hm
        -- F-QUOT and F-EQREC: the quotient realizer, the synthesized eliminator body, then
        -- the axiom fall-through.
        cases hci : di.get!
        case quotInfo qv =>
          rw [hci] at hm
          simp only [] at hm
          rw [run_bind_ok] at hm
          obtain ⟨u3, s3, w3, hlog, hm⟩ := hm
          have hz2 := run_logInfo_state _ _ cctx ref _ hlog
          subst hz2
          replace hP' := H.logInfo hlog hP'
          obtain ⟨hstR, hwR, -⟩ := run_addRealizer_ok hm
          subst hstR
          subst hwR
          obtain ⟨hnfq, hclq, hnbq⟩ := quotRealizer_shape qv.kind
          exact H.rlz hP' hnfq hclq hnbq
        case recInfo rv =>
          rw [hci] at hm
          simp only [] at hm
          rw [run_bind_ok] at hm
          obtain ⟨ro, so, wo, hrr, hm⟩ := hm
          obtain ⟨hPo, hshape⟩ := run_recursorRealizer_okW H hcfg hrr hP'
          cases ro with
          | some tr =>
            simp only [] at hm
            rw [run_bind_ok] at hm
            obtain ⟨u3, s3, w3, hlog, hm⟩ := hm
            have hz2 := run_logInfo_state _ _ cctx ref _ hlog
            subst hz2
            replace hPo := H.logInfo hlog hPo
            obtain ⟨hstR, hwR, -⟩ := run_addRealizer_ok hm
            subst hstR
            subst hwR
            obtain ⟨hnfr, hclr, hnbr⟩ := hshape tr rfl
            exact H.rlz hPo hnfr hclr hnbr
          | none =>
            simp only [] at hm
            rw [run_bind_ok] at hm
            obtain ⟨u3, s3, w3, hlog, hm⟩ := hm
            have hz2 := run_logInfo_state _ _ cctx ref _ hlog
            subst hz2
            replace hPo := H.logInfo hlog hPo
            exact H.ax hm hPo
        all_goals
          rw [hci] at hm
          simp only [] at hm
          rw [run_bind_ok] at hm
          obtain ⟨u3, s3, w3, hlog, hm⟩ := hm
          have hz2 := run_logInfo_state _ _ cctx ref _ hlog
          subst hz2
          replace hP' := H.logInfo hlog hP'
          exact H.ax hm hP'
      | some v =>
        cases hext : isExtern env2 n <;>
          cases hcfgx : ctx.config.extern <;>
            simp only [hval, hext, hcfgx] at hm
        all_goals
          try
            (rw [run_bind_ok] at hm
             obtain ⟨u3, s3, w3, hlog, hm⟩ := hm
             have hz2 := run_logInfo_state _ _ cctx ref _ hlog
             subst hz2
             replace hP' := H.logInfo hlog hP')
        all_goals
          first
            | exact H.ax hm hP'
            | (split at hm
               case isTrue =>
                 exact run_nonrec_exit_okW hm hcfg hP' (fun hq => H.inl hq)
                   (fun h hq => H.logInfo h hq) (fun h hq => H.isInstance h hq)
                   (fun hc h hq => H.prep hc h hq) hvE
                   (fun hq hnf hcl hnb => H.nrc hq hnf hcl hnb) (fun _ => rfl)
               case isFalse =>
                 refine run_rec_exit_okW hm hcfg hP' (fun h hq => H.fresh h hq)
                   (fun h hq => H.constInfo h hq) (fun hc h hq => H.prep hc h hq) hvE ?_
                   (fun _ _ => rfl) (fun _ _ => rfl)
                 intro sR wR defsR hqR hlenR hbodiesR
                 exact H.rc hqR
                   (rec_block_closed (by simp) hlenR (rec_bodies_closed hbodiesR))
                   (rec_block_noBlock (rec_bodies_noBlock hbodiesR)))
    case isFalse =>
      split at hrun
      case isTrue =>
        exact run_nonrec_exit_okW hrun hcfg hP (fun hq => H.inl hq)
          (fun h hq => H.logInfo h hq) (fun h hq => H.isInstance h hq)
          (fun hc h hq => H.prep hc h hq) hvE
          (fun hq hnf hcl hnb => H.nrc hq hnf hcl hnb) (fun _ => rfl)
      case isFalse =>
        refine run_rec_exit_okW hrun hcfg hP (fun h hq => H.fresh h hq)
          (fun h hq => H.constInfo h hq) (fun hc h hq => H.prep hc h hq) hvE ?_
          (fun _ _ => rfl) (fun _ _ => rfl)
        intro sR wR defsR hqR hlenR hbodiesR
        exact H.rc hqR
          (rec_block_closed (by simp) hlenR (rec_bodies_closed hbodiesR))
          (rec_block_noBlock (rec_bodies_noBlock hbodiesR))
  -- Step 7: visitAppArgs
  · intro vE ih1
    intro t0 args s ctx cctx ref w t s' w' hrun hnf0 hcl0 hnb0 hP hcfg
    simp only [] at hrun
    exact run_array_foldlM_ok ctx cctx ref
      (P := fun _ acc s₂ w₂ => P s₂ w₂ ∧ NoFix acc ∧ LBClosed acc 0 ∧ NoBlock acc)
      ⟨hP, hnf0, hcl0, hnb0⟩
      (fun pre x post acc s₁ w₁ acc' s₂ w₂ _ hacc hg => by
        obtain ⟨hPa, hnfa, hcla, hnba⟩ := hacc
        rw [run_bind_ok] at hg
        obtain ⟨u, s₃, w₃, hv, hp⟩ := hg
        rw [run_pure] at hp
        cases hp
        obtain ⟨hP3, hnf3, hcl3, hnb3⟩ := ih1 _ _ _ _ _ _ _ _ _ hv hPa hcfg
        exact ⟨hP3, ⟨hnfa, hnf3⟩, ⟨hcla, hcl3⟩, ⟨hnba, hnb3⟩⟩)
      hrun
  -- Step 8: visitLet
  · intro vE ih1
    intro e s ctx cctx ref w t s' w' hrun hP hcfg
    simp only [] at hrun
    rcases run_letMonocular_okW (fun h hq => H.fresh h hq) hP hrun with
      ⟨rfl, rfl, rfl⟩ | ⟨x, v, b, ctx', w₀, hcf, hP₀, hk⟩
    · exact ⟨hP, noFix_default, lbClosed_default 0, noBlock_default⟩
    · have hcfg' : Cfg ctx'.config := by rw [hcf]; exact hcfg
      rw [run_bind_ok] at hk
      obtain ⟨tv, s₁, w₁, hvv, hk2⟩ := hk
      obtain ⟨hP1, hnfv, hclv, hnbv⟩ := ih1 _ _ _ _ _ _ _ _ _ hvv hP₀ hcfg'
      rw [run_bind_ok] at hk2
      obtain ⟨tb, s₂, w₂, hvb, hm⟩ := hk2
      obtain ⟨hP2, hnfb, hclb, hnbb⟩ := ih1 _ _ _ _ _ _ _ _ _ hvb hP1 hcfg'
      obtain ⟨hs, hw, nm, rfl⟩ := run_mkLetIn_ok hm
      subst hs
      subst hw
      exact ⟨hP2, ⟨hnfv, noFix_toBvar x 0 hnfb⟩, ⟨hclv, lbClosed_toBvar x 0 hclb⟩,
        ⟨hnbv, noBlock_toBvar x 0 hnbb⟩⟩
  -- Step 9: visitLambda
  · intro vE ih1
    intro e s ctx cctx ref w t s' w' hrun hP hcfg
    simp only [] at hrun
    rcases run_lambdaMonocular_okW (fun h hq => H.fresh h hq) hP hrun with
      ⟨rfl, rfl, rfl⟩ | ⟨x, b, ctx', w₀, hcf, hP₀, hk⟩
    · exact ⟨hP, noFix_default, lbClosed_default 0, noBlock_default⟩
    · have hcfg' : Cfg ctx'.config := by rw [hcf]; exact hcfg
      rw [run_bind_ok] at hk
      obtain ⟨tb, s₁, w₁, hvb, hm⟩ := hk
      obtain ⟨hP1, hnfb, hclb, hnbb⟩ := ih1 _ _ _ _ _ _ _ _ _ hvb hP₀ hcfg'
      obtain ⟨hs, hw, nm, rfl⟩ := run_mkLambda_ok hm
      subst hs
      subst hw
      exact ⟨hP1, noFix_toBvar x 0 hnfb, lbClosed_toBvar x 0 hclb, noBlock_toBvar x 0 hnbb⟩
  -- Step 10: visitProj
  · intro vE ih1
    intro tn i e s ctx cctx ref w t s' w' hrun hP hcfg
    simp only [] at hrun
    rw [run_bind_ok] at hrun
    obtain ⟨ci, s₁, w₁, hgc, hk⟩ := hrun
    have hs₁ := run_getConstInfo_state _ _ cctx ref _ hgc
    subst hs₁
    replace hP := H.constInfo hgc hP
    cases ci <;> (try simp only [] at hk)
    case inductInfo indinfo =>
      rw [run_bind_ok] at hk
      obtain ⟨rr, s₂, w₂, hreg, hk2⟩ := hk
      have hP2 := H.reg (Or.inl ⟨_, _, _, _, _, hgc⟩) hcfg hreg hP
      obtain ⟨indid, argmasks⟩ := rr
      simp only [] at hk2
      rw [run_bind_ok] at hk2
      obtain ⟨te, s₃, w₃, hve, hp⟩ := hk2
      rw [run_pure] at hp
      cases hp
      -- `NoFix`/`NoBlock` recurse at `.proj`, so both components are the sub-run's own.
      obtain ⟨hP3, hnf3, hcl, hnb3⟩ := ih1 _ _ _ _ _ _ _ _ _ hve hP2 hcfg
      exact ⟨hP3, (NoFix_proj _ _).mpr hnf3, hcl, (NoBlock_proj _ _).mpr hnb3⟩
    all_goals
      (rw [run_panicWithPosWithDecl] at hk
       cases hk
       exact ⟨hP, noFix_default, lbClosed_default 0, noBlock_default⟩)
  -- Step 11: visitApp
  · intro vE vAA vCA ih1 ih7 ih12
    intro e s ctx cctx ref w t s' w' hrun hP hcfg
    simp only [] at hrun
    cases hfn : e.getAppFn
    case const cn us =>
      rw [hfn] at hrun
      simp only [] at hrun
      exact ih12 _ _ _ _ _ _ _ _ _ hrun hP hcfg
    all_goals
      (rw [hfn] at hrun
       simp only [] at hrun
       rw [expr_withApp_eq] at hrun
       rw [run_bind_ok] at hrun
       obtain ⟨tf, s₁, w₁, hvf, hk⟩ := hrun
       obtain ⟨hP1, hnff, hclf, hnbf⟩ := ih1 _ _ _ _ _ _ _ _ _ hvf hP hcfg
       exact ih7 _ _ _ _ _ _ _ _ _ _ hk hnff hclf hnbf hP1 hcfg)
  -- Step 12: visitConstApp
  · intro vC vAA vCtE vCsE ih4 ih7 ih13 ih15
    intro e s ctx cctx ref w t s' w' hrun hP hcfg
    simp only [] at hrun
    rw [expr_withApp_eq] at hrun
    cases hfn : e.getAppFn
    case const cn us =>
      rw [hfn] at hrun
      simp only [] at hrun
      rw [run_bind_ok] at hrun
      obtain ⟨o, s₁, w₁, hcs, hk⟩ := hrun
      replace hP := H.casesInfo hcs hP
      rw [run_liftCoreM_ok] at hcs
      obtain ⟨-, rfl⟩ := hcs
      cases o with
      | some cinf =>
        simp only [] at hk
        exact ih15 _ _ _ _ _ _ _ _ _ _ hk hP hcfg
      | none =>
        simp only [] at hk
        rw [run_bind_ok] at hk
        obtain ⟨o2, s₂, w₂, hca, hk2⟩ := hk
        replace hP := H.ctorArity hca hP
        rw [run_liftCoreM_ok] at hca
        obtain ⟨-, rfl⟩ := hca
        cases o2 with
        | some ar =>
          simp only [] at hk2
          exact ih13 _ _ _ _ _ _ _ _ _ _ _ hk2 hP hcfg
        | none =>
          simp only [] at hk2
          rw [run_bind_ok] at hk2
          obtain ⟨tc, s₃, w₃, hvc, hk3⟩ := hk2
          obtain ⟨hP3, hnfc, hclc, hnbc⟩ := ih4 _ _ _ _ _ _ _ _ _ hvc hP hcfg
          exact ih7 _ _ _ _ _ _ _ _ _ _ hk3 hnfc hclc hnbc hP3 hcfg
    all_goals
      (rw [hfn] at hrun
       simp only [] at hrun
       rw [run_panicWithPosWithDecl] at hrun
       cases hrun
       exact ⟨hP, noFix_default, lbClosed_default 0, noBlock_default⟩)
  -- Step 13: visitCtorEta
  · intro vCtorEtaGo ih14
    intro cn ar e s ctx cctx ref w t s' w' hrun hP hcfg
    simp only [] at hrun
    rw [run_bind_ok] at hrun
    obtain ⟨type, s₁, w₁, hinfer, hk⟩ := hrun
    have hs₁ : s₁ = s := run_liftMetaM_state _ _ _ _ _ hinfer
    subst hs₁
    replace hP := H.inferType hinfer hP
    rw [expr_withApp_eq] at hk
    exact ih14 _ _ _ _ _ _ _ _ _ _ _ _ _ hk hP hcfg
  -- Step 14: visitCtorEtaGo
  · intro vE vConstructor vCtorEtaGo ih1 ih3 ih14
    intro cn ar ty fe args s ctx cctx ref w t s' w' hrun hP hcfg
    have hvE : ∀ {pe : Expr} {sb sc : ErasureState} {ctx' : ErasureContext}
        {wb wc : Void IO.RealWorld} {tt : LBTerm},
        Cfg ctx'.config → vE pe sb ctx' cctx ref wb = .ok (tt, sc) wc →
        P sb wb → P sc wc ∧ NoFix tt ∧ LBClosed tt 0 ∧ NoBlock tt :=
      fun hc h hp => ih1 _ _ _ _ _ _ _ _ _ h hp hc
    dsimp only at hrun
    split at hrun
    · exact ih3 _ _ _ _ _ _ _ _ _ _ hrun hP hcfg
    · rw [run_bind_ok] at hrun
      obtain ⟨bs, sb, wb, hfold, hrun⟩ := hrun
      have hbs : P sb wb ∧ ∀ q ∈ bs, NoFix q.2.2 ∧ LBClosed q.2.2 0 ∧ NoBlock q.2.2 := by
        refine run_array_foldlM_ok ctx cctx ref
          (P := fun _ (acc : Array (Nat × Expr × LBTerm)) sx wx =>
            P sx wx ∧ ∀ q ∈ acc, NoFix q.2.2 ∧ LBClosed q.2.2 0 ∧ NoBlock q.2.2)
          ⟨hP, by intro q hq; simp at hq⟩ ?_ hfold
        intro pre a post acc sa wa acc' sc wc _ hacc hg
        obtain ⟨hPa, hall⟩ := hacc
        rw [run_bind_ok] at hg
        obtain ⟨c0, sr, wr, hread, hg⟩ := hg
        rw [run_read] at hread
        cases hread
        rw [run_bind_ok] at hg
        obtain ⟨bv, s1, w1, hev, hg⟩ := hg
        replace hPa := run_etaArgIsValue_okW H rfl hev hPa
        split at hg
        · rw [run_pure] at hg
          cases hg
          exact ⟨hPa, hall⟩
        · rw [run_bind_ok] at hg
          obtain ⟨tyv, s2, w2, hty, hg⟩ := hg
          replace hPa := H.inferType hty hPa
          rw [run_bind_ok] at hg
          obtain ⟨vv, s3, w3, hv, hg⟩ := hg
          obtain ⟨hP3, hnf, hcl, hnb⟩ := hvE hcfg hv hPa
          rw [run_pure] at hg
          cases hg
          refine ⟨hP3, ?_⟩
          intro q hq
          rcases Array.mem_or_eq_of_mem_push hq with hq' | rfl
          · exact hall q hq'
          · exact ⟨hnf, hcl, hnb⟩
      obtain ⟨hPb, hbs'⟩ := hbs
      refine run_withEtaPrefixLets_okW H ?_ bs.toList _ _ _ _ _ _ _
        (fun q hq => hbs' q (Array.mem_toList_iff.mp hq)) hcfg hPb hrun
      intro args' ctx₀ sa sc wa wc tt hcfg₀ hk hPa
      rcases run_forallMonocular_okW (fun h hq => H.fresh h hq) hPa hk with
        ⟨rfl, rfl, rfl⟩ | ⟨x, bt, ctx', w₀, hcf, hP₀, hk'⟩
      · exact ⟨hPa, noFix_default, lbClosed_default 0, noBlock_default⟩
      · have hcfg' : Cfg ctx'.config := by rw [hcf]; exact hcfg₀
        rw [run_bind_ok] at hk'
        obtain ⟨res, s₁, w₁, hgo, hm⟩ := hk'
        obtain ⟨hP1, hnf, hcl, hnb⟩ := ih14 _ _ _ _ _ _ _ _ _ _ _ _ _ hgo hP₀ hcfg'
        obtain ⟨hs, hw, nm, rfl⟩ := run_mkLambda_ok hm
        subst hs
        subst hw
        exact ⟨hP1, noFix_toBvar x 0 hnf, lbClosed_toBvar x 0 hcl, noBlock_toBvar x 0 hnb⟩
  -- Step 15: visitCasesEta
  · intro vCasesEtaGo ih16
    intro cinf e s ctx cctx ref w t s' w' hrun hP hcfg
    simp only [] at hrun
    rw [run_bind_ok] at hrun
    obtain ⟨type, s₁, w₁, hinfer, hk⟩ := hrun
    have hs₁ : s₁ = s := run_liftMetaM_state _ _ _ _ _ hinfer
    subst hs₁
    replace hP := H.inferType hinfer hP
    rw [expr_withApp_eq] at hk
    exact ih16 _ _ _ _ _ _ _ _ _ _ _ _ hk hP hcfg
  -- Step 16: visitCasesEtaGo
  · intro vE vCasesEtaGo vCases ih1 ih16 ih17
    intro cinf ty fe args s ctx cctx ref w t s' w' hrun hP hcfg
    have hvE : ∀ {pe : Expr} {sb sc : ErasureState} {ctx' : ErasureContext}
        {wb wc : Void IO.RealWorld} {tt : LBTerm},
        Cfg ctx'.config → vE pe sb ctx' cctx ref wb = .ok (tt, sc) wc →
        P sb wb → P sc wc ∧ NoFix tt ∧ LBClosed tt 0 ∧ NoBlock tt :=
      fun hc h hp => ih1 _ _ _ _ _ _ _ _ _ h hp hc
    dsimp only at hrun
    split at hrun
    · exact ih17 _ _ _ _ _ _ _ _ _ _ hrun hP hcfg
    · rw [run_bind_ok] at hrun
      obtain ⟨bs, sb, wb, hfold, hrun⟩ := hrun
      have hbs : P sb wb ∧ ∀ q ∈ bs, NoFix q.2.2 ∧ LBClosed q.2.2 0 ∧ NoBlock q.2.2 := by
        refine run_array_foldlM_ok ctx cctx ref
          (P := fun _ (acc : Array (Nat × Expr × LBTerm)) sx wx =>
            P sx wx ∧ ∀ q ∈ acc, NoFix q.2.2 ∧ LBClosed q.2.2 0 ∧ NoBlock q.2.2)
          ⟨hP, by intro q hq; simp at hq⟩ ?_ hfold
        intro pre a post acc sa wa acc' sc wc _ hacc hg
        obtain ⟨hPa, hall⟩ := hacc
        split at hg
        · rw [run_pure] at hg
          cases hg
          exact ⟨hPa, hall⟩
        rw [run_bind_ok] at hg
        obtain ⟨c0, sr, wr, hread, hg⟩ := hg
        rw [run_read] at hread
        cases hread
        rw [run_bind_ok] at hg
        obtain ⟨bv, s1, w1, hev, hg⟩ := hg
        replace hPa := run_etaArgIsValue_okW H rfl hev hPa
        split at hg
        · rw [run_pure] at hg
          cases hg
          exact ⟨hPa, hall⟩
        · rw [run_bind_ok] at hg
          obtain ⟨tyv, s2, w2, hty, hg⟩ := hg
          replace hPa := H.inferType hty hPa
          rw [run_bind_ok] at hg
          obtain ⟨vv, s3, w3, hv, hg⟩ := hg
          obtain ⟨hP3, hnf, hcl, hnb⟩ := hvE hcfg hv hPa
          rw [run_pure] at hg
          cases hg
          refine ⟨hP3, ?_⟩
          intro q hq
          rcases Array.mem_or_eq_of_mem_push hq with hq' | rfl
          · exact hall q hq'
          · exact ⟨hnf, hcl, hnb⟩
      obtain ⟨hPb, hbs'⟩ := hbs
      refine run_withEtaPrefixLets_okW H ?_ bs.toList _ _ _ _ _ _ _
        (fun q hq => hbs' q (Array.mem_toList_iff.mp hq)) hcfg hPb hrun
      intro args' ctx₀ sa sc wa wc tt hcfg₀ hk hPa
      rcases run_forallMonocular_okW (fun h hq => H.fresh h hq) hPa hk with
        ⟨rfl, rfl, rfl⟩ | ⟨x, bt, ctx', w₀, hcf, hP₀, hk'⟩
      · exact ⟨hPa, noFix_default, lbClosed_default 0, noBlock_default⟩
      · have hcfg' : Cfg ctx'.config := by rw [hcf]; exact hcfg₀
        rw [run_bind_ok] at hk'
        obtain ⟨res, s₁, w₁, hgo, hm⟩ := hk'
        obtain ⟨hP1, hnf, hcl, hnb⟩ := ih16 _ _ _ _ _ _ _ _ _ _ _ _ hgo hP₀ hcfg'
        obtain ⟨hs, hw, nm, rfl⟩ := run_mkLambda_ok hm
        subst hs
        subst hw
        exact ⟨hP1, noFix_toBvar x 0 hnf, lbClosed_toBvar x 0 hcl, noBlock_toBvar x 0 hnb⟩
  -- Step 17: visitCases
  · intro vE vAlt ih1 ih18
    intro cinf args s ctx cctx ref w t s' w' hrun hP hcfg
    simp only [] at hrun
    rw [run_bind_ok] at hrun
    obtain ⟨discr_nt, s₁, w₁, hdisc, hrun⟩ := hrun
    obtain ⟨hP1, hnfd, hcld, hnbd⟩ := ih1 _ _ _ _ _ _ _ _ _ hdisc hP hcfg
    rw [run_bind_ok] at hrun
    obtain ⟨c0, s₂, w₂, hrd, hrun⟩ := hrun
    rw [run_read] at hrd
    cases hrd
    rw [run_bind_ok] at hrun
    obtain ⟨ret, s₃, w₃, hmatch, htail⟩ := hrun
    have hret : P s₃ w₃ ∧ NoFix ret ∧ LBClosed ret 0 ∧ NoBlock ret := by
      rcases visitCases_match_tri (α := EraseM LBTerm) _ _ _ _ _ with
        ⟨hmach, hm⟩ | ⟨hmach, hm⟩ | hm <;> rw [hm] at hmatch
      · -- machine `Nat`
        rw [run_bind_ok] at hmatch
        obtain ⟨zero_nt, sA, wA, hzero, hmatch⟩ := hmatch
        obtain ⟨hPA, hnfz, hclz, hnbz⟩ := ih1 _ _ _ _ _ _ _ _ _ hzero hP1 hcfg
        rw [run_bind_ok] at hmatch
        obtain ⟨bci, sB, wB, hbci, hmatch⟩ := hmatch
        have hsB := run_getConstInfo_state _ _ cctx ref _ hbci
        subst hsB
        replace hPA := H.constInfo hbci hPA
        rw [run_bind_ok] at hmatch
        obtain ⟨rr, sC, wC, hreg, hmatch⟩ := hmatch
        have hPC := H.reg (Or.inr hmach) hcfg hreg hPA
        obtain ⟨bool_indid, bm⟩ := rr
        simp only [] at hmatch
        obtain ⟨x, ctx', w₀, hcf, hPC', hk⟩ :=
          run_withLocalDecl_okW (fun h hq => H.fresh h hq) hPC hmatch
        have hcfg' : Cfg ctx'.config := by rw [hcf]; exact hcfg
        rw [run_bind_ok] at hk
        obtain ⟨gtz_nt, sD, wD, hgtz, hk⟩ := hk
        obtain ⟨hPD, hnfg, hclg, hnbg⟩ := ih1 _ _ _ _ _ _ _ _ _ hgtz hPC' hcfg'
        rw [run_bind_ok] at hk
        obtain ⟨cond, sE, wE, hcond, hk⟩ := hk
        obtain ⟨hPE, hnfc, hclc, hnbc⟩ := ih1 _ _ _ _ _ _ _ _ _ hcond hPD hcfg'
        rw [run_bind_ok] at hk
        obtain ⟨a1, sF, wF, ha1, hk⟩ := hk
        obtain ⟨hsF, hwF, hlen1, hb1⟩ := run_mkAlt_ok ha1
        subst hsF
        subst hwF
        rw [run_bind_ok] at hk
        obtain ⟨a2, sG, wG, ha2, hk⟩ := hk
        obtain ⟨hsG, hwG, hlen2, hb2⟩ := run_mkAlt_ok ha2
        subst hsG
        subst hwG
        obtain ⟨hsH, hwH, nm, rfl⟩ := run_mkLetIn_ok hk
        subst hsH
        subst hwH
        simp only [List.length_nil, List.reverse_nil, List.zipIdx_nil,
          List.foldl_nil] at hlen1 hlen2 hb1 hb2
        refine ⟨hPE, ?_, ?_, ?_⟩
        · refine ⟨hnfd, noFix_toBvar x 0 ?_⟩
          rw [NoFix_case]
          refine ⟨hnfc, ?_⟩
          intro a ha
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl
          · rw [hb1]; exact hnfg
          · rw [hb2]; exact hnfz
        · refine ⟨hcld, lbClosed_toBvar x 0 ?_⟩
          rw [LBClosed_case]
          refine ⟨hclc, ?_⟩
          rw [LBClosedAlts_iff]
          intro a ha
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl
          · rw [hb1, hlen1]; exact hclg
          · rw [hb2, hlen2]; exact hclz
        · refine ⟨hnbd, noBlock_toBvar x 0 ?_⟩
          rw [NoBlock_case]
          refine ⟨hnbc, ?_⟩
          intro a ha
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl
          · rw [hb1]; exact hnbg
          · rw [hb2]; exact hnbz
      · -- machine `Int`
        rw [run_bind_ok] at hmatch
        obtain ⟨bci, sB, wB, hbci, hmatch⟩ := hmatch
        have hsB := run_getConstInfo_state _ _ cctx ref _ hbci
        subst hsB
        replace hP1 := H.constInfo hbci hP1
        rw [run_bind_ok] at hmatch
        obtain ⟨rr, sC, wC, hreg, hmatch⟩ := hmatch
        have hPC := H.reg (Or.inr hmach) hcfg hreg hP1
        obtain ⟨bool_indid, bm⟩ := rr
        simp only [] at hmatch
        obtain ⟨x, ctx', w₀, hcf, hPC', hk⟩ :=
          run_withLocalDecl_okW (fun h hq => H.fresh h hq) hPC hmatch
        have hcfg' : Cfg ctx'.config := by rw [hcf]; exact hcfg
        rw [run_bind_ok] at hk
        obtain ⟨ofn, sD, wD, hofn, hk⟩ := hk
        obtain ⟨hPD, hnfo, hclo, hnbo⟩ := ih1 _ _ _ _ _ _ _ _ _ hofn hPC' hcfg'
        rw [run_bind_ok] at hk
        obtain ⟨neg, sE, wE, hneg, hk⟩ := hk
        obtain ⟨hPE, hnfn, hcln, hnbn⟩ := ih1 _ _ _ _ _ _ _ _ _ hneg hPD hcfg'
        rw [run_bind_ok] at hk
        obtain ⟨ineg, sF, wF, hineg, hk⟩ := hk
        obtain ⟨hPF, hnfin, hclin, hnbin⟩ := ih1 _ _ _ _ _ _ _ _ _ hineg hPE hcfg'
        rw [run_bind_ok] at hk
        obtain ⟨nsucc, sG, wG, hnsucc, hk⟩ := hk
        obtain ⟨hPG, hnfs, hcls, hnbs⟩ := ih1 _ _ _ _ _ _ _ _ _ hnsucc hPF hcfg'
        rw [run_bind_ok] at hk
        obtain ⟨cond, sH, wH, hcond, hk⟩ := hk
        obtain ⟨hPH, hnfc, hclc, hnbc⟩ := ih1 _ _ _ _ _ _ _ _ _ hcond hPG hcfg'
        rw [run_bind_ok] at hk
        obtain ⟨a1, sI, wI, ha1, hk⟩ := hk
        obtain ⟨hsI, hwI, hlen1, hb1⟩ := run_mkAlt_ok ha1
        subst hsI
        subst hwI
        rw [run_bind_ok] at hk
        obtain ⟨a2, sJ, wJ, ha2, hk⟩ := hk
        obtain ⟨hsJ, hwJ, hlen2, hb2⟩ := run_mkAlt_ok ha2
        subst hsJ
        subst hwJ
        obtain ⟨hsK, hwK, nm, rfl⟩ := run_mkLetIn_ok hk
        subst hsK
        subst hwK
        simp only [List.length_nil, List.reverse_nil, List.zipIdx_nil,
          List.foldl_nil] at hlen1 hlen2 hb1 hb2
        refine ⟨hPH, ?_, ?_, ?_⟩
        · refine ⟨hnfd, noFix_toBvar x 0 ?_⟩
          rw [NoFix_case]
          refine ⟨hnfc, ?_⟩
          intro a ha
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl
          · rw [hb1]; exact ⟨hnfn, hnfin, hnfs, NoFix_fvar _⟩
          · rw [hb2]; exact ⟨hnfo, NoFix_fvar _⟩
        · refine ⟨hcld, lbClosed_toBvar x 0 ?_⟩
          rw [LBClosed_case]
          refine ⟨hclc, ?_⟩
          rw [LBClosedAlts_iff]
          intro a ha
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl
          · rw [hb1, hlen1]; exact ⟨hcln, hclin, hcls, trivial⟩
          · rw [hb2, hlen2]; exact ⟨hclo, trivial⟩
        · refine ⟨hnbd, noBlock_toBvar x 0 ?_⟩
          rw [NoBlock_case]
          refine ⟨hnbc, ?_⟩
          intro a ha
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl
          · rw [hb1]; exact ⟨hnbn, hnbin, hnbs, trivial⟩
          · rw [hb2]; exact ⟨hnbo, trivial⟩
      · -- the general arm
        rw [run_bind_ok] at hmatch
        obtain ⟨cinfo, sA, wA, hgci, hmatch⟩ := hmatch
        have hsA := run_getConstInfo_state _ _ cctx ref _ hgci
        subst hsA
        replace hP1 := H.constInfo hgci hP1
        cases cinfo
        case inductInfo indVal =>
          simp only [] at hmatch
          rw [run_bind_ok] at hmatch
          obtain ⟨cfg2, sR, wR, hrd2, hmatch⟩ := hmatch
          rw [run_read] at hrd2
          cases hrd2
          -- The three refusals, each an `if` whose throwing half the toolkit kills.
          -- `split` is unusable on them: its internal `simp` runs out of steps on a
          -- hypothesis this size, so each condition is decided by hand and the branch
          -- selected with `if_pos`/`if_neg`.
          split at hmatch
          all_goals (simp only [Bool.true_and, Bool.false_and] at hmatch)
          all_goals
            (first
              | rw [if_neg (fun h => Bool.noConfusion h)] at hmatch
              | (by_cases hmi : (cinf.indName == `Nat || cinf.indName == `Int) = true
                 case pos =>
                   rw [if_pos hmi] at hmatch
                   rw [run_bind_ok] at hmatch
                   obtain ⟨a0, s0, w0, hthr, -⟩ := hmatch
                   exact absurd hthr (run_throwError_ne_ok _ ctx cctx ref _ _ _ _ _)
                 rw [if_neg hmi] at hmatch))
          all_goals
            (by_cases har : (cinf.altsRange.lower == cinf.discrPos + 1) = true
             case neg =>
               rw [if_neg har] at hmatch
               rw [run_bind_ok] at hmatch
               obtain ⟨a0, s0, w0, hthr, -⟩ := hmatch
               exact absurd hthr (run_throwError_ne_ok _ ctx cctx ref _ _ _ _ _)
             rw [if_pos har] at hmatch)
          all_goals (by_cases hpa : isPropositionalArity indVal.type = true)
          all_goals (first | rw [if_pos hpa] at hmatch | rw [if_neg hpa] at hmatch)
          all_goals
            (try (rw [run_bind_ok] at hmatch
                  obtain ⟨fnp, sF, wF, hfnp, hmatch⟩ := hmatch
                  replace hP1 := run_firstNonProofField_okW H hfnp hP1
                  cases fnp <;> (try simp only [] at hmatch)))
          all_goals
            (try (rw [run_bind_ok] at hmatch
                  obtain ⟨a0, s0, w0, hthr, -⟩ := hmatch
                  exact absurd hthr (run_throwError_ne_ok _ ctx cctx ref _ _ _ _ _)))
          all_goals
            rw [run_bind_ok] at hmatch
            obtain ⟨rr, sB, wB, hreg, hmatch⟩ := hmatch
            replace hP1 := H.reg (Or.inl ⟨_, _, _, _, _, hgci⟩) hcfg hreg hP1
            split at hmatch
            case isFalse =>
              rw [run_bind_ok] at hmatch
              obtain ⟨a0, s0, w0, hthr, -⟩ := hmatch
              exact absurd hthr (run_throwError_ne_ok _ ctx cctx ref _ _ _ _ _)
            case isTrue =>
            split at hmatch
            · -- every constructor has its own alternative: no catch-all is built
              rw [run_bind_ok] at hmatch
              obtain ⟨dflt, sD, wD, hdf, hmatch⟩ := hmatch
              rw [run_pure] at hdf
              cases hdf
              have hPst := hP1
              rw [run_bind_ok] at hmatch
              obtain ⟨accfin, sC, wC, hloop, hp⟩ := hmatch
              have hall : P sC wC ∧ ∀ a ∈ accfin,
                  NoFix a.2 ∧ LBClosed a.2 a.1.length ∧ NoBlock a.2 := by
                refine run_array_forIn_ok ctx cctx ref
                  (P := fun acc sX (wX : Void IO.RealWorld) => P sX wX ∧ ∀ a ∈ acc,
                    NoFix a.2 ∧ LBClosed a.2 a.1.length ∧ NoBlock a.2)
                  _ _ _ _ _ ⟨hPst, by intro a ha; simp at ha⟩ ?_ _ _ _ hloop
                intro x _ acc sX wX st sY wY hacc hb
                obtain ⟨hPX, hallX⟩ := hacc
                obtain ⟨alt?, cidx⟩ := x
                cases alt?
                case some j =>
                  simp only [] at hb
                  rw [run_bind_ok] at hb
                  obtain ⟨alt, sZ, wZ, halt, hp2⟩ := hb
                  obtain ⟨hPZ, hnfa, hcla, hnba⟩ := ih18 _ _ _ _ _ _ _ _ _ _ _ halt hPX hcfg
                  rw [run_pure] at hp2
                  cases hp2
                  refine ⟨hPZ, ?_⟩
                  intro a ha
                  rcases Array.mem_or_eq_of_mem_push ha with ha' | rfl
                  · exact hallX a ha'
                  · exact ⟨hnfa, hcla, hnba⟩
                case none =>
                  simp only [] at hb
                  rw [run_bind_ok] at hb
                  obtain ⟨a0, s0, w0, hthr, -⟩ := hb
                  exact absurd hthr (run_throwError_ne_ok _ ctx cctx ref _ _ _ _ _)
              obtain ⟨hPfin, hallfin⟩ := hall
              rw [run_pure] at hp
              cases hp
              refine ⟨hPfin, ?_, ?_, ?_⟩
              · rw [NoFix_case]
                exact ⟨hnfd, fun a ha => (hallfin a (Array.mem_toList_iff.mp ha)).1⟩
              · rw [LBClosed_case, LBClosedAlts_iff]
                refine ⟨hcld, fun a ha => ?_⟩
                rw [Nat.zero_add]
                exact (hallfin a (Array.mem_toList_iff.mp ha)).2.1
              · rw [NoBlock_case]
                exact ⟨hnbd, fun a ha => (hallfin a (Array.mem_toList_iff.mp ha)).2.2⟩
            · -- the catch-all, erased once and applied to a `□` per hypothesis
              cases hfi : cinf.altNumParams.findIdx?
                  (fun altInfo =>
                    Erasure.visitCases.match_7 (motive := fun _ => Bool) altInfo
                      (fun _ => true) (fun _ _ => false))
              case none =>
                simp only [hfi] at hmatch
                rw [run_bind_ok] at hmatch
                obtain ⟨a0, s0, w0, hthr, -⟩ := hmatch
                exact absurd hthr (run_throwError_ne_ok _ ctx cctx ref _ _ _ _ _)
              case some j =>
              simp only [hfi] at hmatch
              split at hmatch
              case isFalse =>
                rw [run_bind_ok] at hmatch
                obtain ⟨a0, s0, w0, hthr, -⟩ := hmatch
                exact absurd hthr (run_throwError_ne_ok _ ctx cctx ref _ _ _ _ _)
              case isTrue =>
              rw [run_bind_ok] at hmatch
              obtain ⟨bd, sE, wE, hbd, hmatch⟩ := hmatch
              obtain ⟨hPE, hnfb, hclb, hnbb⟩ := ih1 _ _ _ _ _ _ _ _ _ hbd hP1 hcfg
              split at hmatch
              case isTrue =>
                rw [run_bind_ok] at hmatch
                obtain ⟨a0, s0, w0, hthr, -⟩ := hmatch
                exact absurd hthr (run_throwError_ne_ok _ ctx cctx ref _ _ _ _ _)
              case isFalse =>
              rw [run_bind_ok] at hmatch
              obtain ⟨bh, sG, wG, hbh, hmatch⟩ := hmatch
              replace hPE := H.metaM
                (PrimGenMono.lambdaBoundedTelescope _ _ _ _ fun _ _ => primGenMono_proofScan _)
                hbh hPE
              cases bh
              case some i =>
                simp only [] at hmatch
                rw [run_bind_ok] at hmatch
                obtain ⟨a0, s0, w0, hthr, -⟩ := hmatch
                exact absurd hthr (run_throwError_ne_ok _ ctx cctx ref _ _ _ _ _)
              case none =>
              simp only [] at hmatch
              rw [run_bind_ok] at hmatch
              obtain ⟨dflt, sD, wD, hdf, hmatch⟩ := hmatch
              rw [run_pure] at hdf
              cases hdf
              have hPst := hPE
              rw [run_bind_ok] at hmatch
              obtain ⟨accfin, sC, wC, hloop, hp⟩ := hmatch
              have hall : P sC wC ∧ ∀ a ∈ accfin,
                  NoFix a.2 ∧ LBClosed a.2 a.1.length ∧ NoBlock a.2 := by
                refine run_array_forIn_ok ctx cctx ref
                  (P := fun acc sX (wX : Void IO.RealWorld) => P sX wX ∧ ∀ a ∈ acc,
                    NoFix a.2 ∧ LBClosed a.2 a.1.length ∧ NoBlock a.2)
                  _ _ _ _ _ ⟨hPst, by intro a ha; simp at ha⟩ ?_ _ _ _ hloop
                intro x _ acc sX wX st sY wY hacc hb
                obtain ⟨hPX, hallX⟩ := hacc
                obtain ⟨alt?, cidx⟩ := x
                cases alt?
                case some j =>
                  simp only [] at hb
                  rw [run_bind_ok] at hb
                  obtain ⟨alt, sZ, wZ, halt, hp2⟩ := hb
                  obtain ⟨hPZ, hnfa, hcla, hnba⟩ := ih18 _ _ _ _ _ _ _ _ _ _ _ halt hPX hcfg
                  rw [run_pure] at hp2
                  cases hp2
                  refine ⟨hPZ, ?_⟩
                  intro a ha
                  rcases Array.mem_or_eq_of_mem_push ha with ha' | rfl
                  · exact hallX a ha'
                  · exact ⟨hnfa, hcla, hnba⟩
                case none =>
                  simp only [] at hb
                  rw [run_pure] at hb
                  cases hb
                  refine ⟨hPX, ?_⟩
                  intro a ha
                  rcases Array.mem_or_eq_of_mem_push ha with ha' | rfl
                  · exact hallX a ha'
                  · obtain ⟨hnf2, hcl2, hnb2⟩ := shape_foldl_box _ _ hnfb hclb hnbb
                    exact ⟨hnf2, hcl2.mono (Nat.zero_le _), hnb2⟩
              obtain ⟨hPfin, hallfin⟩ := hall
              rw [run_pure] at hp
              cases hp
              refine ⟨hPfin, ?_, ?_, ?_⟩
              · rw [NoFix_case]
                exact ⟨hnfd, fun a ha => (hallfin a (Array.mem_toList_iff.mp ha)).1⟩
              · rw [LBClosed_case, LBClosedAlts_iff]
                refine ⟨hcld, fun a ha => ?_⟩
                rw [Nat.zero_add]
                exact (hallfin a (Array.mem_toList_iff.mp ha)).2.1
              · rw [NoBlock_case]
                exact ⟨hnbd, fun a ha => (hallfin a (Array.mem_toList_iff.mp ha)).2.2⟩
        all_goals
          (simp only [] at hmatch
           exact absurd hmatch (run_throwError_ne_ok _ ctx cctx ref _ _ _ _ _))
    obtain ⟨hP3, hnfr, hclr, hnbr⟩ := hret
    rw [run_bind_ok] at htail
    obtain ⟨tfin, s₄, w₄, hloop2, hp2⟩ := htail
    rw [run_pure] at hp2
    cases hp2
    exact run_array_forIn_ok ctx cctx ref
      (P := fun acc sX (wX : Void IO.RealWorld) =>
        P sX wX ∧ NoFix acc ∧ LBClosed acc 0 ∧ NoBlock acc)
      _ _ _ _ _ ⟨hP3, hnfr, hclr, hnbr⟩
      (fun a _ acc sX wX st sY wY hacc hb => by
        obtain ⟨hPX, hnfa, hcla, hnba⟩ := hacc
        rw [run_bind_ok] at hb
        obtain ⟨tx, sZ, wZ, hvx, hp3⟩ := hb
        rw [run_pure] at hp3
        cases hp3
        obtain ⟨hPZ, hnfx, hclx, hnbx⟩ := ih1 _ _ _ _ _ _ _ _ _ hvx hPX hcfg
        exact ⟨hPZ, ⟨hnfa, hnfx⟩, ⟨hcla, hclx⟩, ⟨hnba, hnbx⟩⟩)
      _ _ _ hloop2
  -- Step 18: visitAlt
  · intro vE ih1
    intro nf mask e s ctx cctx ref w r s' w' hrun hP hcfg
    simp only [] at hrun
    rw [run_bind_ok] at hrun
    obtain ⟨ty, s₁, w₁, hinfer, hk⟩ := hrun
    have hs₁ : s₁ = s := run_liftMetaM_state _ _ _ _ _ hinfer
    subst hs₁
    replace hP := H.inferType hinfer hP
    rcases run_lambdaOrIntroToArity_okW (fun h hq => H.fresh h hq) nf hP hk with
      ⟨rfl, rfl, hPd⟩ | ⟨e', xs, ctx', w₀, hlen, hcf, hP₀, hK⟩
    · exact ⟨hPd, trivial, trivial, trivial⟩
    · have hcfg' : Cfg ctx'.config := by rw [hcf]; exact hcfg
      rw [run_bind_ok] at hK
      obtain ⟨tb, s₂, w₂, hvb, hm⟩ := hK
      obtain ⟨hP2, hnfb, hclb, hnbb⟩ := ih1 _ _ _ _ _ _ _ _ _ hvb hP₀ hcfg'
      obtain ⟨hs, hw, hlen2, hbody⟩ := run_mkAlt_ok hm
      subst hs
      subst hw
      refine ⟨hP2, ?_, ?_, ?_⟩
      · rw [hbody]; exact noFix_foldl_toBvar _ hnfb
      · rw [hbody, hlen2]; exact lbClosed_foldl_zipIdx _ hclb
      · rw [hbody]; exact noBlock_foldl_toBvar _ hnbb

/-! ## The state-only induction, recovered

`RunClosed Q` is the world-blind interface: `runClosedW_of_runClosed` reads it as a
`RunClosedW` at the trivial configuration condition and a predicate that ignores the world,
and the eighteen conjuncts follow by feeding each of them `trivial`. There is one induction
over the erasure family in this file, not two.
-/

/-- **The output-shape induction, all eighteen motives.** From `RunClosed Q`: every
successful run of a member of the erasure family preserves `Q`, and every one that returns
a λ□ term returns a fix-free, de Bruijn closed term in applied form. -/
theorem visitExpr_shape {Q : ErasureState → Prop} (H : RunClosed Q) :
    (∀ e s ctx cctx ref w t s' w', visitExpr e s ctx cctx ref w = .ok (t, s') w' →
      ShapeC Q s s' t) ∧
    (∀ l s ctx cctx ref w t s' w', visitLiteral l s ctx cctx ref w = .ok (t, s') w' →
      ShapeC Q s s' t) ∧
    (∀ cn args s ctx cctx ref w t s' w',
      visitConstructor cn args s ctx cctx ref w = .ok (t, s') w' → ShapeC Q s s' t) ∧
    (∀ e s ctx cctx ref w t s' w', visitConst e s ctx cctx ref w = .ok (t, s') w' →
      ShapeC Q s s' t) ∧
    (∀ n s ctx cctx ref w r s' w',
      get_constant_kername n s ctx cctx ref w = .ok (r, s') w' → Q s → Q s') ∧
    (∀ n s ctx cctx ref w r s' w', visitMutual n s ctx cctx ref w = .ok (r, s') w' →
      Q s → Q s') ∧
    (∀ t0 args s ctx cctx ref w t s' w',
      visitAppArgs t0 args s ctx cctx ref w = .ok (t, s') w' →
      NoFix t0 → LBClosed t0 0 → NoBlock t0 → ShapeC Q s s' t) ∧
    (∀ e s ctx cctx ref w t s' w', visitLet e s ctx cctx ref w = .ok (t, s') w' →
      ShapeC Q s s' t) ∧
    (∀ e s ctx cctx ref w t s' w', visitLambda e s ctx cctx ref w = .ok (t, s') w' →
      ShapeC Q s s' t) ∧
    (∀ tn i e s ctx cctx ref w t s' w',
      visitProj tn i e s ctx cctx ref w = .ok (t, s') w' → ShapeC Q s s' t) ∧
    (∀ e s ctx cctx ref w t s' w', visitApp e s ctx cctx ref w = .ok (t, s') w' →
      ShapeC Q s s' t) ∧
    (∀ e s ctx cctx ref w t s' w', visitConstApp e s ctx cctx ref w = .ok (t, s') w' →
      ShapeC Q s s' t) ∧
    (∀ cn ar e s ctx cctx ref w t s' w',
      visitCtorEta cn ar e s ctx cctx ref w = .ok (t, s') w' → ShapeC Q s s' t) ∧
    (∀ cn ar ty fe args s ctx cctx ref w t s' w',
      visitCtorEtaGo cn ar ty fe args s ctx cctx ref w = .ok (t, s') w' →
      ShapeC Q s s' t) ∧
    (∀ ci e s ctx cctx ref w t s' w',
      visitCasesEta ci e s ctx cctx ref w = .ok (t, s') w' → ShapeC Q s s' t) ∧
    (∀ ci ty fe args s ctx cctx ref w t s' w',
      visitCasesEtaGo ci ty fe args s ctx cctx ref w = .ok (t, s') w' →
      ShapeC Q s s' t) ∧
    (∀ ci args s ctx cctx ref w t s' w',
      visitCases ci args s ctx cctx ref w = .ok (t, s') w' → ShapeC Q s s' t) ∧
    (∀ nf mask e s ctx cctx ref w r s' w',
      visitAlt nf mask e s ctx cctx ref w = .ok (r, s') w' →
      Q s → Q s' ∧ NoFix r.2 ∧ LBClosed r.2 r.1.length ∧ NoBlock r.2) :=
  let K := visitExpr_shapeW (Cfg := fun _ => True) (runClosedW_of_runClosed H)
  ⟨fun a b c d e f g h i hr hq => K.1 a b c d e f g h i hr hq trivial,
   fun a b c d e f g h i hr hq => K.2.1 a b c d e f g h i hr hq trivial,
   fun a b c d e f g h i j hr hq => K.2.2.1 a b c d e f g h i j hr hq trivial,
   fun a b c d e f g h i hr hq => K.2.2.2.1 a b c d e f g h i hr hq trivial,
   fun a b c d e f g h i hr hq => K.2.2.2.2.1 a b c d e f g h i hr hq trivial,
   fun a b c d e f g h i hr hq => K.2.2.2.2.2.1 a b c d e f g h i hr hq trivial,
   fun a b c d e f g h i j hr h1 h2 h3 hq =>
     K.2.2.2.2.2.2.1 a b c d e f g h i j hr h1 h2 h3 hq trivial,
   fun a b c d e f g h i hr hq => K.2.2.2.2.2.2.2.1 a b c d e f g h i hr hq trivial,
   fun a b c d e f g h i hr hq => K.2.2.2.2.2.2.2.2.1 a b c d e f g h i hr hq trivial,
   fun a b c d e f g h i j k hr hq =>
     K.2.2.2.2.2.2.2.2.2.1 a b c d e f g h i j k hr hq trivial,
   fun a b c d e f g h i hr hq => K.2.2.2.2.2.2.2.2.2.2.1 a b c d e f g h i hr hq trivial,
   fun a b c d e f g h i hr hq => K.2.2.2.2.2.2.2.2.2.2.2.1 a b c d e f g h i hr hq trivial,
   fun a b c d e f g h i j k hr hq =>
     K.2.2.2.2.2.2.2.2.2.2.2.2.1 a b c d e f g h i j k hr hq trivial,
   fun a b c d e f g h i j k l m hr hq =>
     K.2.2.2.2.2.2.2.2.2.2.2.2.2.1 a b c d e f g h i j k l m hr hq trivial,
   fun a b c d e f g h i j hr hq =>
     K.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 a b c d e f g h i j hr hq trivial,
   fun a b c d e f g h i j k l hr hq =>
     K.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 a b c d e f g h i j k l hr hq trivial,
   fun a b c d e f g h i j hr hq =>
     K.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 a b c d e f g h i j hr hq trivial,
   fun a b c d e f g h i j k hr hq =>
     K.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 a b c d e f g h i j k hr hq trivial⟩

/-! ## The output shape, unconditionally

`RunClosed` is satisfied outright at the trivial predicate — every field's conclusion is
`True` — so instantiating the induction there discards the state half and leaves the output
half standing with **no hypotheses**. That instance is simultaneously the non-vacuity guard
for `RunClosed`: the class is inhabited, so `visitExpr_shape` is not true merely because
its premise is unsatisfiable. -/

/-- Non-vacuity: the trivial predicate is `RunClosed`. -/
theorem runClosed_true : RunClosed (fun _ => True) where
  inl := fun _ => trivial
  ax := fun _ _ => trivial
  reg := fun _ _ => trivial
  prep := fun _ _ => trivial
  nrc := fun _ _ _ _ => trivial
  rlz := fun _ _ _ _ => trivial
  rc := fun _ _ _ => trivial

/-- **The output shape of the shipping eraser, in full.** Every successful run of
`Erasure.visitExpr` returns a term that contains no `.fix`, has no loose de Bruijn index,
and is in applied form. No hypotheses: not on the state, not on the source expression, not
on the configuration, and the panic arms are discharged rather than excluded. -/
theorem visitExpr_shape_all {e : Expr} {s : ErasureState} {ctx : ErasureContext}
    {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
    {t : LBTerm} {s' : ErasureState} {w' : Void IO.RealWorld}
    (hrun : visitExpr e s ctx cctx ref w = .ok (t, s') w') :
    NoFix t ∧ LBClosed t 0 ∧ NoBlock t :=
  ((visitExpr_shape runClosed_true).1 _ _ _ _ _ _ _ _ _ hrun trivial).2

/-- The two conjuncts the registry argument asks for, as a thin wrapper on
`visitExpr_shape_all`: they are what `ColdStartShape.RegInvShape'.constCons` needs of the
body being stored at `visitMutual`'s non-recursive constant cons. -/
theorem visitExpr_noFix_closed {e : Expr} {s : ErasureState} {ctx : ErasureContext}
    {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
    {t : LBTerm} {s' : ErasureState} {w' : Void IO.RealWorld}
    (hrun : visitExpr e s ctx cctx ref w = .ok (t, s') w') :
    NoFix t ∧ LBClosed t 0 :=
  let h := visitExpr_shape_all hrun
  ⟨h.1, h.2.1⟩

/-- **Applied form of every `visitExpr` output**, on its own: the conjunct `Output.lean`'s
well-formedness predicate reads. -/
theorem visitExpr_noBlock {e : Expr} {s : ErasureState} {ctx : ErasureContext}
    {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
    {t : LBTerm} {s' : ErasureState} {w' : Void IO.RealWorld}
    (hrun : visitExpr e s ctx cctx ref w = .ok (t, s') w') : NoBlock t :=
  (visitExpr_shape_all hrun).2.2

/-- The `Q`-generic form: the output-shape half of the induction at an arbitrary
`RunClosed` predicate. -/
theorem visitExpr_output_shape {Q : ErasureState → Prop} (H : RunClosed Q) {e : Expr}
    {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
    {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld} {t : LBTerm}
    {s' : ErasureState} {w' : Void IO.RealWorld}
    (hrun : visitExpr e s ctx cctx ref w = .ok (t, s') w') (hQ : Q s) :
    Q s' ∧ NoFix t ∧ LBClosed t 0 ∧ NoBlock t :=
  (visitExpr_shape H).1 _ _ _ _ _ _ _ _ _ hrun hQ
/-! ## What the world-indexed induction yields at a run

The two conjuncts of the term walk's run conclusion that are theorems of the erasure's own
run algebra — the state grew canonically, and the name generator only advanced — are
`RunClosedW` instances, so the induction discharges them at every successful
`Erasure.visitExpr` run. Both instances take one hypothesis about
`Erasure.prepare_erasure`, `hprep`: it is *proved* — `ColdStartRun.run_prepare_erasure_state`
and `Step.run_prepare_erasure_concl` are its two halves — but `ColdStartRun.lean` imports this
module, so the fact cannot be cited here and is a parameter instead. Its `Cfg` premise is what
carries `csimp = false` to the `@[csimp]` branch, whose `Lean.Core.transform` walk at `EraseM`
is the one step of the preparation pass no `liftM` lemma reaches.

The third conjunct of the run conclusion — that a modelled inductive registry stays modelled —
is a further instance, at `IndRegistryModelled`, which is declared in `Bridge.lean`, below this
module; it is built there from `RunClosedW` and `run_register_inductive_models`.
-/

/-- Two world-indexed predicates closed under the erasure's steps are closed jointly. It is
what composes the state half and the generator half of a run conclusion into one predicate. -/
theorem RunClosedW.and {Cfg : ErasureConfig → Prop}
    {P P' : ErasureState → Void IO.RealWorld → Prop}
    (H : RunClosedW Cfg P) (H' : RunClosedW Cfg P') :
    RunClosedW Cfg (fun s w => P s w ∧ P' s w) where
  oracle h hq := ⟨H.oracle h hq.1, H'.oracle h hq.2⟩
  inferType h hq := ⟨H.inferType h hq.1, H'.inferType h hq.2⟩
  metaM hc h hq := ⟨H.metaM hc h hq.1, H'.metaM hc h hq.2⟩
  constInfo h hq := ⟨H.constInfo h hq.1, H'.constInfo h hq.2⟩
  getEnv h hq := ⟨H.getEnv h hq.1, H'.getEnv h hq.2⟩
  logInfo h hq := ⟨H.logInfo h hq.1, H'.logInfo h hq.2⟩
  isInstance h hq := ⟨H.isInstance h hq.1, H'.isInstance h hq.2⟩
  fresh h hq := ⟨H.fresh h hq.1, H'.fresh h hq.2⟩
  declInfo h hq := ⟨H.declInfo h hq.1, H'.declInfo h hq.2⟩
  ctorArity h hq := ⟨H.ctorArity h hq.1, H'.ctorArity h hq.2⟩
  casesInfo h hq := ⟨H.casesInfo h hq.1, H'.casesInfo h hq.2⟩
  inl hq := ⟨H.inl hq.1, H'.inl hq.2⟩
  ax h hq := ⟨H.ax h hq.1, H'.ax h hq.2⟩
  reg hp hc h hq := ⟨H.reg hp hc h hq.1, H'.reg hp hc h hq.2⟩
  prep hc h hq := ⟨H.prep hc h hq.1, H'.prep hc h hq.2⟩
  nrc hq hnf hcl hnb := ⟨H.nrc hq.1 hnf hcl hnb, H'.nrc hq.2 hnf hcl hnb⟩
  rlz hq hnf hcl hnb := ⟨H.rlz hq.1 hnf hcl hnb, H'.rlz hq.2 hnf hcl hnb⟩
  rc hq hcl hnb := ⟨H.rc hq.1 hcl hnb, H'.rc hq.2 hcl hnb⟩

/-- **The state half.** "The state has only grown canonically since `s₀`" is closed under
every step of the erasure family: the ambient primitives leave the state alone, and each of
the four writers is a `RunConcl` step already proved in `ErasureRun.lean`. Nothing about the
configuration is read except by `hprep`. -/
theorem runClosedW_runConcl {Cfg : ErasureConfig → Prop} (s₀ : ErasureState)
    (hprep : ∀ {e : Expr} {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
        {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld} {pe : Expr}
        {s₁ : ErasureState} {w₁ : Void IO.RealWorld},
      Cfg ctx.config → prepare_erasure e s ctx cctx ref w = .ok (pe, s₁) w₁ → s₁ = s) :
    RunClosedW Cfg (fun s _ => RunConcl s₀ s) where
  oracle h hq := by rw [run_liftMetaM_state _ _ _ _ _ h]; exact hq
  inferType h hq := by rw [run_liftMetaM_state _ _ _ _ _ h]; exact hq
  metaM _ h hq := by rw [run_liftMetaM_state _ _ _ _ _ h]; exact hq
  constInfo h hq := by rw [run_getConstInfo_state _ _ _ _ _ h]; exact hq
  getEnv h hq := by rw [run_getEnv_state _ _ _ _ _ h]; exact hq
  logInfo h hq := by rw [run_logInfo_state _ _ _ _ _ h]; exact hq
  isInstance h hq := by rw [run_liftCoreM_state _ _ _ _ _ h]; exact hq
  fresh h hq := by rw [run_mkFreshFVarId_state _ _ _ _ _ h]; exact hq
  declInfo h hq := by rw [run_liftCoreM_state _ _ _ _ _ h]; exact hq
  ctorArity h hq := by rw [run_liftCoreM_state _ _ _ _ _ h]; exact hq
  casesInfo h hq := by rw [run_liftCoreM_state _ _ _ _ _ h]; exact hq
  inl hq := hq.trans (runConcl_inlinings _ _)
  ax h hq := by rw [(run_addAxiom_ok h).1]; exact hq.trans (runConcl_addAxiomState _ _)
  reg _ _ h hq := hq.trans (run_register_inductive_runConcl h)
  prep hc h hq := by rw [hprep hc h]; exact hq
  nrc hq _ _ _ := hq.trans (runConcl_nonrecConstState _ _ _)
  rlz hq _ _ _ := hq.trans (runConcl_addRealizerState _ _ _)
  rc hq _ _ := hq.trans (runConcl_recConstState _ _ _)

/-- **The generator half.** "The generator has only advanced since `w₀`" is closed under every
step: each ambient primitive's bound is the `ErasureSpec` clause that specifies it and the four
writers leave the world alone. `hreg` and `hprep` are the two bounds this module cannot cite —
`Bridge.run_register_inductive_gen` and `Step.run_prepare_erasure_concl`, both proved, both
declared below it. -/
theorem runClosedW_gen {lenv : Environment} {env : Lean4Lean.VEnv} {Us : List Name}
    {gw : Void IO.RealWorld → NameGenerator} (S : ErasureSpec lenv env Us gw)
    (w₀ : Void IO.RealWorld)
    (hprep : ∀ {e : Expr} {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
        {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld} {pe : Expr}
        {s₁ : ErasureState} {w₁ : Void IO.RealWorld},
      ConfigPinned ctx.config → prepare_erasure e s ctx cctx ref w = .ok (pe, s₁) w₁ →
      gw w ≤ gw w₁)
    (hreg : ∀ {ii : InductiveVal} {s : ErasureState} {ctx : ErasureContext}
        {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
        {r : InductiveId × InductiveArgMasks} {s₁ : ErasureState} {w₁ : Void IO.RealWorld},
      ConfigPinned ctx.config → register_inductive ii s ctx cctx ref w = .ok (r, s₁) w₁ →
      gw w ≤ gw w₁) :
    RunClosedW ConfigPinned (fun _ w => gw w₀ ≤ gw w) where
  oracle h hq := NameGenerator.LE.trans hq (S.oracle_refl _ _ _ _ _ _ _ _ _ h).1
  inferType h hq := NameGenerator.LE.trans hq (S.prim_monotone.inferType _ _ _ _ _ _ _ _ _ h).1
  metaM hc h hq :=
    NameGenerator.LE.trans hq (S.prim_monotone.liftMetaM (hc gw S.prim_monotone) h)
  constInfo h hq := NameGenerator.LE.trans hq
    (S.lookup_adequate.constInfo _ _ _ _ _ _ (pass_getConstInfo_core h)).1
  getEnv h hq := NameGenerator.LE.trans hq (S.prim_monotone.getEnv _ _ _ _ _ _ _ _ h)
  logInfo h hq := NameGenerator.LE.trans hq (S.prim_monotone.logInfo _ _ _ _ _ _ _ _ _ h)
  isInstance h hq := NameGenerator.LE.trans hq (S.prim_monotone.isInstance _ _ _ _ _ _ _ _ _ h)
  fresh h hq := NameGenerator.LE.trans hq (S.fresh_names _ _ _ _ _ _ _ _ h).2.2.1
  declInfo h hq :=
    NameGenerator.LE.trans hq
      (S.lookup_adequate.declInfo _ _ _ _ _ _ ((run_liftCoreM_ok _ _ _ _ _).mp h).1).1
  ctorArity h hq :=
    NameGenerator.LE.trans hq
      (S.lookup_adequate.ctorArity _ _ _ _ _ _ ((run_liftCoreM_ok _ _ _ _ _).mp h).1).1
  casesInfo h hq :=
    NameGenerator.LE.trans hq
      (S.lookup_adequate.casesInfo _ _ _ _ _ _ ((run_liftCoreM_ok _ _ _ _ _).mp h).1).1
  inl hq := hq
  ax h hq := by rw [(run_addAxiom_ok h).2.1]; exact hq
  reg _ hc h hq := NameGenerator.LE.trans hq (hreg hc h)
  prep hc h hq := NameGenerator.LE.trans hq (hprep hc h)
  nrc hq _ _ _ := hq
  rlz hq _ _ _ := hq
  rc hq _ _ := hq

/-- **Two of the three conjuncts of the term walk's run conclusion, at a real run.** The state
grew canonically and the generator only advanced; `hprep` and `hreg` are the two facts this
module cannot cite — both proved below it — and `ConfigPinned` is what carries `csimp = false`
to the preparation pass. The registry conjunct is added where `IndRegistryModelled` is
declared. -/
theorem visitExpr_runConcl_gen {lenv : Environment} {env : Lean4Lean.VEnv} {Us : List Name}
    {gw : Void IO.RealWorld → NameGenerator} (S : ErasureSpec lenv env Us gw)
    (hprep : ∀ {e : Expr} {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
        {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld} {pe : Expr}
        {s₁ : ErasureState} {w₁ : Void IO.RealWorld},
      ConfigPinned ctx.config → prepare_erasure e s ctx cctx ref w = .ok (pe, s₁) w₁ →
      s₁ = s ∧ gw w ≤ gw w₁)
    (hreg : ∀ {ii : InductiveVal} {s : ErasureState} {ctx : ErasureContext}
        {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
        {r : InductiveId × InductiveArgMasks} {s₁ : ErasureState} {w₁ : Void IO.RealWorld},
      ConfigPinned ctx.config → register_inductive ii s ctx cctx ref w = .ok (r, s₁) w₁ →
      gw w ≤ gw w₁)
    {e : Expr} {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
    {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld} {t : LBTerm}
    {s₁ : ErasureState} {w₁ : Void IO.RealWorld} (hcfg : ConfigPinned ctx.config)
    (hrun : visitExpr e s ctx cctx ref w = .ok (t, s₁) w₁) :
    RunConcl s s₁ ∧ gw w ≤ gw w₁ :=
  ((visitExpr_shapeW ((runClosedW_runConcl (Cfg := ConfigPinned) s
      (fun hc h => (hprep hc h).1)).and
    (runClosedW_gen S w (fun hc h => (hprep hc h).2) hreg))).1
      _ _ _ _ _ _ _ _ _ hrun ⟨RunConcl.rfl' s, NameGenerator.LE.rfl⟩ hcfg).1

/-! ## The emitted bodies are closed

`ClosedBodies` of the emitted environment is the one clause of `ColdStartShape.RegInvShape'`
that mentions no specification environment, so it is a fact about the run alone and a
`RunClosedW` instance. It is the environment half of `LBWfPeregrine`'s `closed` conjunct: the
term half is `visitExpr_shape_all`'s. The clauses that *do* mention a specification
environment — everything relating an emitted body to a `Lower` image — are not run facts and
are not here.
-/

/-- A body-less entry declares no body, so it cannot break closedness. -/
theorem closedBodies_cons_none {Γ : GlobalDeclarations} {kn : Kername} (h : ClosedBodies Γ) :
    ClosedBodies ((kn, .constantDecl ⟨none⟩) :: Γ) :=
  closedBodies_cons h (by simp)

/-- A block entry declares no body either. -/
theorem closedBodies_cons_ind {Γ : GlobalDeclarations} {kn : Kername}
    {mib : MutualInductiveBody} (h : ClosedBodies Γ) :
    ClosedBodies ((kn, .inductiveDecl mib) :: Γ) :=
  closedBodies_cons h (by simp)

/-- Consing a closed body keeps every body closed. -/
theorem closedBodies_cons_some {Γ : GlobalDeclarations} {kn : Kername} {t : LBTerm}
    (hcl : LBClosed t 0) (h : ClosedBodies Γ) :
    ClosedBodies ((kn, .constantDecl ⟨some t⟩) :: Γ) :=
  closedBodies_cons h (fun b hb => by
    obtain rfl : t = b := by simpa using hb
    exact hcl)

/-- The body-less prefix `Erasure.register_inductive`'s cold branch prepends. -/
theorem closedBodies_axiomPrefix :
    ∀ (pre Γ : GlobalDeclarations),
      (∀ p ∈ pre, p.2 = GlobalDecl.constantDecl ⟨none⟩) → ClosedBodies Γ →
      ClosedBodies (pre ++ Γ)
  | [], _, _, h => by simpa using h
  | p :: rest, Γ, hpre, h => by
      obtain ⟨k, d⟩ := p
      have hd : d = GlobalDecl.constantDecl ⟨none⟩ := hpre _ List.mem_cons_self
      subst hd
      exact closedBodies_cons_none
        (closedBodies_axiomPrefix rest Γ (fun q hq => hpre q (List.mem_cons_of_mem _ hq)) h)

/-- The block registration loop stores one η-expanded `.fix` node per member (F-ETA). -/
theorem closedBodies_foldl_recConstStep {defs : List (@FixDef LBTerm)}
    (hcl : ∀ j : Nat, LBClosed (.fix defs j) 0) :
    ∀ (L : List (Name × Nat)) (s : ErasureState), ClosedBodies s.gdecls →
      ClosedBodies (L.foldl (recConstStep defs) s).gdecls
  | [], _, h => h
  | p :: rest, s, h => by
      refine closedBodies_foldl_recConstStep hcl rest _ ?_
      show ClosedBodies (nonrecConstState p.1 (etaExpandFix defs p.2) s).gdecls
      rw [nonrecConstState_gdecls]
      exact closedBodies_cons_some
        (lbClosed_etaExpandFix (fun m => (hcl p.2).mono (Nat.zero_le m))) h

theorem closedBodies_recConstState {names : List Name} {defs : List (@FixDef LBTerm)}
    {s : ErasureState} (hcl : ∀ j : Nat, LBClosed (.fix defs j) 0)
    (h : ClosedBodies s.gdecls) : ClosedBodies (recConstState names defs s).gdecls := by
  rw [recConstState_eq]
  exact closedBodies_foldl_recConstStep hcl names.zipIdx s h

/-- **Closedness of the emitted bodies is closed under every step of the erasure family.**
The ambient primitives and the preparation pass leave `gdecls` alone; `Erasure.addAxiom` and
`Erasure.register_inductive` only add body-less and block entries; and the two `visitMutual`
exits store exactly the terms whose closedness the induction proves. -/
theorem runClosedW_closedBodies {Cfg : ErasureConfig → Prop}
    (hprep : ∀ {e : Expr} {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
        {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld} {pe : Expr}
        {s₁ : ErasureState} {w₁ : Void IO.RealWorld},
      Cfg ctx.config → prepare_erasure e s ctx cctx ref w = .ok (pe, s₁) w₁ → s₁ = s) :
    RunClosedW Cfg (fun s _ => ClosedBodies s.gdecls) where
  oracle h hq := by rw [run_liftMetaM_state _ _ _ _ _ h]; exact hq
  inferType h hq := by rw [run_liftMetaM_state _ _ _ _ _ h]; exact hq
  metaM _ h hq := by rw [run_liftMetaM_state _ _ _ _ _ h]; exact hq
  constInfo h hq := by rw [run_getConstInfo_state _ _ _ _ _ h]; exact hq
  getEnv h hq := by rw [run_getEnv_state _ _ _ _ _ h]; exact hq
  logInfo h hq := by rw [run_logInfo_state _ _ _ _ _ h]; exact hq
  isInstance h hq := by rw [run_liftCoreM_state _ _ _ _ _ h]; exact hq
  fresh h hq := by rw [run_mkFreshFVarId_state _ _ _ _ _ h]; exact hq
  declInfo h hq := by rw [run_liftCoreM_state _ _ _ _ _ h]; exact hq
  ctorArity h hq := by rw [run_liftCoreM_state _ _ _ _ _ h]; exact hq
  casesInfo h hq := by rw [run_liftCoreM_state _ _ _ _ _ h]; exact hq
  inl hq := hq
  ax h hq := by
    rw [(run_addAxiom_ok h).1, addAxiomState_gdecls]
    exact closedBodies_cons_none hq
  rlz hq _ hcl _ := by
    rw [addRealizerState_gdecls]; exact closedBodies_cons_some hcl hq
  reg := by
    intro ii s₀ ctx cctx ref w r s₁ w₁ _ _ h hq
    cases hi : s₀.inductives.get? ii.name with
    | some rc0 => rw [(run_register_inductive_hit_ok hi h).2.1]; exact hq
    | none =>
      obtain ⟨-, bodies, sM, rfl, -, -, hce, -, -⟩ :=
        run_register_inductive_cold_ok (Ci := fun _ _ => True)
          (fun _ _ _ _ _ _ _ => trivial) hi h
      obtain ⟨pre, hpre, hshape⟩ := hce.gdeclsAx
      show ClosedBodies ((mutualBlockKn ii, _) :: sM.gdecls)
      refine closedBodies_cons_ind ?_
      rw [hpre]
      exact closedBodies_axiomPrefix pre _ (fun q hq' => (hshape q hq').1) hq
  prep hc h hq := by rw [hprep hc h]; exact hq
  nrc hq _ hcl _ := by rw [nonrecConstState_gdecls]; exact closedBodies_cons_some hcl hq
  rc hq hcl _ := closedBodies_recConstState hcl hq

/-- **The emitted environment of a run has closed bodies.** The environment half of
`Output.LBWfPeregrine`'s closedness conjunct, from a cold entry (`ClosedBodies` of the empty
`gdecls` is vacuous) or from any state that already had it. -/
theorem visitExpr_closedBodies {Cfg : ErasureConfig → Prop}
    (hprep : ∀ {e : Expr} {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
        {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld} {pe : Expr}
        {s₁ : ErasureState} {w₁ : Void IO.RealWorld},
      Cfg ctx.config → prepare_erasure e s ctx cctx ref w = .ok (pe, s₁) w₁ → s₁ = s)
    {e : Expr} {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
    {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld} {t : LBTerm}
    {s₁ : ErasureState} {w₁ : Void IO.RealWorld} (hcfg : Cfg ctx.config)
    (hcl : ClosedBodies s.gdecls)
    (hrun : visitExpr e s ctx cctx ref w = .ok (t, s₁) w₁) : ClosedBodies s₁.gdecls :=
  ((visitExpr_shapeW (runClosedW_closedBodies hprep)).1
    _ _ _ _ _ _ _ _ _ hrun hcl hcfg).1

/-- The empty state emits nothing, so the cold entry satisfies the invariant. -/
theorem closedBodies_empty : ClosedBodies ({} : ErasureState).gdecls := by
  intro kn b hb
  simp [DefnDecl, LBTerm.envLookup] at hb

/-! ## Constructor saturation

`Output.lean`'s saturation invariant asks that every constructor spine of the emitted
program carry at least `ind_npars + cstr_nargs` arguments. The eraser has exactly one
`.construct` construction site (`Erasure.visitConstructor`), reached from a `.const`-headed
application only through `visitCtorEta`/`visitCtorEtaGo`, whose own guard is
`args.size ≥ arity`. `visitExpr_ctorSat` is that guard read as a run invariant: at a
constructor occurrence the run visits saturated, the emitted term is the constructor node
applied to exactly as many arguments as the source occurrence had.

The premises are the run's own queries, in the shape `ErasureSpec` states them — the
`getCasesInfo?`/`getCtorArity?` answers for the name, the configuration's two relevant
fields, and `MaskKeeps`, which says the run reports a total argument mask for this
constructor. The conclusion's `default` disjunct is the panic arms: `Erasure.visitConstructor`
panics when the environment does not answer with a constructor, and a panic succeeds.
-/

variable {ctx : ErasureContext} {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}

/-- Every `visitAppArgs` run returns its seed applied to one argument per source argument.
The one place the erasure builds an application spine, so the one place a spine's length is
fixed. -/
theorem run_visitAppArgs_mkApps {f : LBTerm} {as : Array Expr} {s : ErasureState}
    {w : Void IO.RealWorld} {t : LBTerm} {s' : ErasureState} {w' : Void IO.RealWorld}
    (hrun : visitAppArgs f as s ctx cctx ref w = .ok (t, s') w') :
    ∃ ts : List LBTerm, t = LBTerm.mkApps f ts ∧ ts.length = as.size := by
  unfold visitAppArgs at hrun
  have h := run_array_foldlM_ok (as := as) (init := f) ctx cctx ref
    (fun pre acc _ _ => ∃ ts : List LBTerm, acc = LBTerm.mkApps f ts ∧ ts.length = pre.length)
    ⟨[], rfl, rfl⟩ ?step hrun
  · obtain ⟨ts, ht, hlen⟩ := h
    exact ⟨ts, ht, by simpa using hlen⟩
  case step =>
    intro pre x post acc s₁ w₁ acc' s₂ w₂ _ hP hg
    obtain ⟨ts, rfl, hlen⟩ := hP
    rw [run_bind_ok] at hg
    obtain ⟨a, s₃, w₃, _, hp⟩ := hg
    rw [run_pure] at hp
    cases hp
    exact ⟨ts ++ [a], (LBTerm.mkApps_concat f ts a).symm, by simp [hlen]⟩

/-- A mask of `.keep`s selects the prefix of the array it is zipped against. -/
theorem list_filterMap_zip_keep {α : Type} : ∀ (n : Nat) (l : List α),
    (List.zip (List.replicate n ConstructorArgRelevance.keep) l).filterMap
      (fun p => match p.1 with | .erase => none | .keep => some p.2) = l.take n
  | 0, l => by simp
  | (n+1), [] => by simp
  | (n+1), a :: l => by
      simp [List.replicate, List.zip]
      exact list_filterMap_zip_keep n l

/-- `Erasure.filter` under a total mask is truncation at the mask's length: no field is
dropped, and the fields beyond the mask are not reached. -/
theorem filter_replicate_keep {α : Type} (n : Nat) (arr : Array α) :
    Erasure.filter (Array.replicate n .keep) arr = arr.take n := by
  unfold Erasure.filter
  apply Array.ext'
  simp only [Array.toList_filterMap, Array.toList_zip, Array.toList_replicate]
  rw [show (arr.take n).toList = arr.toList.take n from by simp]
  exact list_filterMap_zip_keep n arr.toList

/-- The length of an in-range slice. -/
theorem slice_size_toSubarray {α : Type} (as : Array α) {a b : Nat} (hb : b ≤ as.size)
    (hab : a ≤ b) : Std.Slice.size (as.toSubarray a b) = b - a := by
  unfold Array.toSubarray
  rw [dif_pos hb, dif_pos hab]
  rfl

/-- The length of the tail slice, which the eraser takes with the default stop index. -/
theorem slice_size_toSubarray_tail {α : Type} (as : Array α) {a : Nat} :
    Std.Slice.size (as.toSubarray a as.size) = as.size - a := by
  unfold Array.toSubarray
  rw [dif_pos (Nat.le_refl _)]
  by_cases h : a ≤ as.size
  · rw [dif_pos h]; rfl
  · rw [dif_neg h]
    show as.size - as.size = as.size - a
    omega

/-- The argument mask the run reports for `c` keeps every field of it.
`Erasure.register_inductive` computes `Array.replicate ci.numFields .keep` for each
constructor when `remove_irrel_constr_args` is off; a state that already holds the block
reports its cached masks instead, so the property is on the run's own three queries rather
than on the configuration alone. A consumer that instead relates the site's mask to the
emitted declaration needs no totality: the declared field count is `Array.count .keep` of
that same mask (`Erasure.register_inductive`'s own `nargs`), so the dropped fields cancel. -/
def MaskKeeps (s : ErasureState) (ctx : ErasureContext) (c : Name) : Prop :=
  ∀ (cctx : Core.Context) (ref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld)
    (cv : ConstructorVal) (s₁ : ErasureState) (w₁ : Void IO.RealWorld) (iv : InductiveVal)
    (s₂ : ErasureState) (w₂ : Void IO.RealWorld) (iid : InductiveId)
    (masks : InductiveArgMasks) (s₃ : ErasureState) (w₃ : Void IO.RealWorld),
    (getConstInfo c : EraseM ConstantInfo) s ctx cctx ref w = .ok (.ctorInfo cv, s₁) w₁ →
    (getConstInfo cv.induct : EraseM ConstantInfo) s₁ ctx cctx ref w₁
      = .ok (.inductInfo iv, s₂) w₂ →
    register_inductive iv s₂ ctx cctx ref w₂ = .ok ((iid, masks), s₃) w₃ →
    masks[cv.cidx]! = Array.replicate cv.numFields .keep

/-- The saturation conclusion: the run panicked, or it emitted the constructor node of the
constructor the environment reports for `c`, applied to one argument per source argument
whenever the occurrence carried at least the constructor's own parameters and fields. -/
def CtorSatConcl (ctx : ErasureContext) (cctx : Core.Context)
    (ref : ST.Ref IO.RealWorld Core.State) (c : Name) (s : ErasureState) (n : Nat)
    (t : LBTerm) : Prop :=
  t = default ∨ ∃ (cv : ConstructorVal) (iid : InductiveId) (ts : List LBTerm)
    (s₁ : ErasureState) (w₀ w₁ : Void IO.RealWorld),
    (getConstInfo c : EraseM ConstantInfo) s ctx cctx ref w₀ = .ok (.ctorInfo cv, s₁) w₁ ∧
    t = LBTerm.mkApps (.construct iid cv.cidx []) ts ∧
    (cv.numParams + cv.numFields ≤ n → ts.length = n)

/-- **The construction site.** `Erasure.visitConstructor` emits the constructor node applied
to the parameters, the mask-selected fields and the over-application tail; under a total
mask those three slices recompose the argument array, so the spine has exactly `args.size`
arguments. The `@[extern]` exit is excluded by the configuration, and the machine-`Nat`
exits by `nat = .peano`. -/
theorem visitConstructor_ctorSat {c : Name} {args : Array Expr} {s : ErasureState}
    {w : Void IO.RealWorld} {t : LBTerm} {s' : ErasureState} {w' : Void IO.RealWorld}
    (hnat : ctx.config.nat = .peano) (hext : ctx.config.extern = .preferLogical)
    (hmask : MaskKeeps s ctx c)
    (hrun : visitConstructor c args s ctx cctx ref w = .ok (t, s') w') :
    CtorSatConcl ctx cctx ref c s args.size t := by
  unfold visitConstructor at hrun
  rw [run_bind_ok] at hrun
  obtain ⟨ci, s₁, w₁, hci, hrun⟩ := hrun
  simp only [] at hrun
  cases ci with
  | ctorInfo cv =>
    simp only [] at hrun
    rw [run_bind_ok] at hrun
    obtain ⟨ii, s₂, w₂, hii, hrun⟩ := hrun
    cases ii with
    | inductInfo iv =>
      simp only [] at hrun
      rw [run_bind_ok] at hrun
      obtain ⟨r, s₃, w₃, hreg, hrun⟩ := hrun
      obtain ⟨iid, masks⟩ := r
      simp only [] at hrun
      rw [run_bind_ok] at hrun
      obtain ⟨envr, s₄, w₄, henv, hrun⟩ := hrun
      obtain rfl := run_getEnv_state _ _ cctx ref _ henv
      rw [run_read_bind, hext] at hrun
      rw [show (Config.Extern.preferLogical == Config.Extern.preferAxiom) = false from rfl,
        Bool.and_false, if_neg (by simp)] at hrun
      rw [run_read_bind, hnat] at hrun
      simp only [] at hrun
      right
      obtain ⟨ts, rfl, hlen⟩ := run_visitAppArgs_mkApps hrun
      refine ⟨cv, iid, ts, s₁, w, w₁, hci, rfl, ?_⟩
      intro hsat
      rw [hlen, hmask cctx ref w cv s₁ w₁ iv s₂ w₂ iid masks _ w₃ hci hii hreg,
        filter_replicate_keep]
      simp only [Array.size_append, Subarray.copy_eq_toArray, Std.Slice.size_toArray_eq_size,
        Array.take_eq_extract, Array.size_extract, Nat.sub_zero]
      rw [slice_size_toSubarray _ (by omega) (Nat.zero_le _),
        slice_size_toSubarray _ (by omega) (by omega), slice_size_toSubarray_tail]
      omega
    | _ =>
      all_goals (simp only [] at hrun
                 rw [run_panicWithPosWithDecl] at hrun; cases hrun; exact Or.inl rfl)
  | _ =>
    all_goals (simp only [] at hrun
               rw [run_panicWithPosWithDecl] at hrun; cases hrun; exact Or.inl rfl)

/-- **The dispatch.** A `.const`-headed application whose head the environment answers for
as a constructor of arity `arity`, visited at `arity` arguments or more, reaches
`Erasure.visitConstructor` at exactly its own argument array: the `casesOn` exit is excluded
by `hnc`, the plain-constant exit by `hca`, and the η exit by `hsat`. -/
theorem visitApp_ctorSat {e : Expr} {c : Name} {us : List Level} {arity : Nat}
    {s : ErasureState} {w : Void IO.RealWorld} {t : LBTerm} {s' : ErasureState}
    {w' : Void IO.RealWorld}
    (hnat : ctx.config.nat = .peano) (hext : ctx.config.extern = .preferLogical)
    (hmask : MaskKeeps s ctx c)
    (hfn : e.getAppFn = .const c us)
    (hnc : ∀ (w : Void IO.RealWorld) r w₁,
      (Lean.getCasesInfo? c : CoreM (Option CasesInfo)) cctx ref w = .ok r w₁ → r = none)
    (hca : ∀ (w : Void IO.RealWorld) r w₁,
      (Lean.Compiler.LCNF.getCtorArity? c : CoreM (Option Nat)) cctx ref w = .ok r w₁ →
        r = some arity)
    (hsat : arity ≤ e.getAppArgs.size)
    (hrun : visitApp e s ctx cctx ref w = .ok (t, s') w') :
    CtorSatConcl ctx cctx ref c s e.getAppArgs.size t := by
  unfold visitApp at hrun
  rw [hfn] at hrun
  simp only [] at hrun
  unfold visitConstApp at hrun
  rw [expr_withApp_eq, hfn] at hrun
  simp only [] at hrun
  rw [run_bind_ok] at hrun
  obtain ⟨ci, s₁, w₁, hci, hrun⟩ := hrun
  obtain ⟨hcore, rfl⟩ := (run_liftCoreM_ok _ _ cctx ref _).mp hci
  rw [hnc _ _ _ hcore] at hrun
  simp only [] at hrun
  rw [run_bind_ok] at hrun
  obtain ⟨ar, s₂, w₂, har, hrun⟩ := hrun
  obtain ⟨hcore2, rfl⟩ := (run_liftCoreM_ok _ _ cctx ref _).mp har
  rw [hca _ _ _ hcore2] at hrun
  simp only [] at hrun
  unfold visitCtorEta at hrun
  rw [run_bind_ok] at hrun
  obtain ⟨ty, s₃, w₃, hty, hrun⟩ := hrun
  obtain rfl := run_liftMetaM_state (x := Meta.inferType e) _ _ cctx ref _ hty
  rw [expr_withApp_eq, hfn] at hrun
  unfold visitCtorEtaGo at hrun
  rw [if_pos hsat] at hrun
  exact visitConstructor_ctorSat hnat hext hmask hrun

/-- **The run-side saturation lemma.** A constructor occurrence the run visits at its own
arity or more is emitted as the constructor node applied to exactly as many arguments as the
occurrence carried — the invariant `Output.lean`'s `etaCtors` clauses read, established on
the run rather than observed on an output. The `default` disjunct is the erasability gate
and the panic arms, neither of which emits a constructor spine. -/
theorem visitExpr_ctorSat {e : Expr} {c : Name} {us : List Level} {arity : Nat}
    {s : ErasureState} {w : Void IO.RealWorld} {t : LBTerm} {s' : ErasureState}
    {w' : Void IO.RealWorld}
    (hnat : ctx.config.nat = .peano) (hext : ctx.config.extern = .preferLogical)
    (hmask : MaskKeeps s ctx c)
    (hfn : e.getAppFn = .const c us)
    (hnc : ∀ (w : Void IO.RealWorld) r w₁,
      (Lean.getCasesInfo? c : CoreM (Option CasesInfo)) cctx ref w = .ok r w₁ → r = none)
    (hca : ∀ (w : Void IO.RealWorld) r w₁,
      (Lean.Compiler.LCNF.getCtorArity? c : CoreM (Option Nat)) cctx ref w = .ok r w₁ →
        r = some arity)
    (hsat : arity ≤ e.getAppArgs.size)
    (hrun : visitExpr e s ctx cctx ref w = .ok (t, s') w') :
    CtorSatConcl ctx cctx ref c s e.getAppArgs.size t := by
  unfold visitExpr at hrun
  rw [run_read_bind, run_bind_ok] at hrun
  obtain ⟨b, sb, wb, hb, hrun⟩ := hrun
  obtain rfl := run_liftMetaM_state (x := Erasure.isErasable ctx.lparams e) _ _ cctx ref _ hb
  cases b with
  | true => rw [if_pos rfl, run_pure] at hrun; cases hrun; exact Or.inl rfl
  | false =>
    simp only [Bool.false_eq_true, if_false] at hrun
    cases e with
    | app f a =>
      exact visitApp_ctorSat hnat hext hmask hfn hnc hca hsat (by simpa only [] using hrun)
    | const n l =>
      exact visitApp_ctorSat hnat hext hmask hfn hnc hca hsat (by simpa only [] using hrun)
    | _ => simp [Expr.getAppFn] at hfn

/-- Non-vacuity of the saturated disjunct at a two-argument constructor: the emitted
argument array of a constructor with no parameters and two fields has exactly the two
arguments, and the spine it heads is not the `default` the other disjunct reports. -/
theorem ctorSat_fires (args : Array Expr) (h : args.size = 2) (iid : InductiveId) (k : Nat)
    (x y : LBTerm) :
    (Std.Slice.toArray (args.toSubarray 0 0) ++
        Erasure.filter (Array.replicate 2 .keep)
          ((args.toSubarray 0 2 : Subarray Expr) : Array Expr) ++
        Std.Slice.toArray (args.toSubarray 2)).size = 2 ∧
      LBTerm.mkApps (.construct iid k []) [x, y] ≠ default := by
  constructor
  · rw [filter_replicate_keep]
    simp only [Array.size_append, Subarray.copy_eq_toArray, Std.Slice.size_toArray_eq_size,
      Array.take_eq_extract, Array.size_extract, Nat.sub_zero]
    rw [slice_size_toSubarray _ (by omega) (Nat.zero_le _),
      slice_size_toSubarray _ (by omega) (by omega), slice_size_toSubarray_tail]
    omega
  · simp only [LBTerm.mkApps]
    intro hc
    exact LBTerm.noConfusion hc

end LeanToLambdaBox
