import EraseProof.Spec
import ConLeche.Verify.Subst
import ConLeche.Verify.Rules.Bridge
import ConLeche.Verify.Inductives.RecCheckScope

/-!
# con-leche's reading of the source semantics' operations

`toCL?` commutes with the operations on Lean terms the source semantics uses
(`EraseProof.SrcEval`): the shipping `Expr.liftLooseBVars'` and `Expr.instantiate1'`
(`LeanToLambdaBox/Erasure/ExprOps.lean`) and the oracle's level instantiation `Erasure.Pure.instLevels`
(`LeanToLambdaBox/Erasure/Pure.lean`), each read as con-leche's own operation; and the readings of
the terms con-leche types are closed: no loose bound variable, no free variable.
-/

open Lean Erasure

namespace EraseProof

/-- `toCL?` reads `liftLooseBVars'` as con-leche's `liftLooseBVars`
(`CL ConLeche/Kernel/ExprOps.lean:677 liftLooseBVars`). Reference: `lift` (`MR P/PCUICAst.v:244`). -/
theorem toCL?_liftLooseBVars' (s d : Nat) : ∀ e : Lean.Expr,
    toCL? (e.liftLooseBVars' s d) = (toCL? e).map (ConLeche.Expr.liftLooseBVars d s ·) := by
  intro e
  induction e generalizing s with
  | bvar i =>
    simp only [Expr.liftLooseBVars', toCL?, Option.map_some, ConLeche.Expr.liftLooseBVars]
    by_cases h : i < s
    · rw [ite_eq_left h, ite_eq_right (by omega)]
    · rw [ite_eq_right h, ite_eq_left (by omega)]
  | app f a ihf iha =>
    simp only [Expr.liftLooseBVars', toCL?, ihf, iha]
    cases toCL? f <;> cases toCL? a <;> rfl
  | lam _ t b _ iht ihb | forallE _ t b _ iht ihb =>
    simp only [Expr.liftLooseBVars', toCL?, iht, ihb]
    cases toCL? t <;> cases toCL? b <;> rfl
  | letE _ t v b _ iht ihv ihb =>
    simp only [Expr.liftLooseBVars', toCL?, iht, ihv, ihb]
    cases toCL? t <;> cases toCL? v <;> cases toCL? b <;> rfl
  | mdata _ e ih => simpa only [Expr.liftLooseBVars', toCL?] using ih s
  | proj _ _ e ih =>
    simp only [Expr.liftLooseBVars', toCL?, ih]
    cases toCL? e <;> rfl
  | lit l => cases l <;> rfl
  | sort u =>
    simp only [Expr.liftLooseBVars', toCL?]
    cases Level.toCL u <;> rfl
  | const c us =>
    simp only [Expr.liftLooseBVars', toCL?]
    cases us.mapM Level.toCL <;> rfl
  | fvar _ | mvar _ => rfl

/-- `toCL?` reads `instantiate1'`, which lifts the substituted term past the binders it crosses, as
con-leche's capture-avoiding `instantiate1Lift` (`CL ConLeche/Kernel/ExprOps.lean:697
instantiate1Lift`). Reference: `subst1` (`MR P/PCUICAst.v:307`). -/
theorem toCL?_instantiate1' {a : Lean.Expr} {ca : ConLeche.Expr} (ha : toCL? a = some ca) :
    ∀ (e : Lean.Expr) (k : Nat),
      toCL? (e.instantiate1' a k) = (toCL? e).map (ConLeche.Expr.instantiate1Lift · ca k) := by
  intro e
  induction e with
  | bvar i =>
    intro k
    simp only [Expr.instantiate1', toCL?, Option.map_some, ConLeche.Expr.instantiate1Lift]
    by_cases h1 : i < k
    · rw [ite_eq_left h1, ite_eq_right (by omega), ite_eq_right (by omega)]; rfl
    · by_cases h2 : i = k
      · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_left h2, toCL?_liftLooseBVars', ha]; rfl
      · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h2, ite_eq_left (by omega)]; rfl
  | app f a' ihf iha =>
    intro k
    simp only [Expr.instantiate1', toCL?, ihf, iha]
    cases toCL? f <;> cases toCL? a' <;> rfl
  | lam _ t b _ iht ihb | forallE _ t b _ iht ihb =>
    intro k
    simp only [Expr.instantiate1', toCL?, iht, ihb]
    cases toCL? t <;> cases toCL? b <;> rfl
  | letE _ t v b _ iht ihv ihb =>
    intro k
    simp only [Expr.instantiate1', toCL?, iht, ihv, ihb]
    cases toCL? t <;> cases toCL? v <;> cases toCL? b <;> rfl
  | mdata _ e ih => intro k; simpa only [Expr.instantiate1', toCL?] using ih k
  | proj _ _ e ih =>
    intro k
    simp only [Expr.instantiate1', toCL?, ih]
    cases toCL? e <;> rfl
  | lit l => intro k; cases l <;> rfl
  | sort u =>
    intro k
    simp only [Expr.instantiate1', toCL?]
    cases Level.toCL u <;> rfl
  | const c us =>
    intro k
    simp only [Expr.instantiate1', toCL?]
    cases us.mapM Level.toCL <;> rfl
  | fvar _ | mvar _ => intro k; rfl

/-- At a closed argument, `toCL?` reads `instantiate1'` as con-leche's `instantiate1`
(`CL ConLeche/Kernel/ExprOps.lean:27 instantiate1`), the substitution of the β- and ζ-steps of
con-leche's reduction and denotation (`CL ConLeche/Verify/Denote/Inst.lean:332 denote_beta`).
Reference: `subst1` (`MR P/PCUICAst.v:307`). -/
theorem toCL?_instantiate1'_closed {a : Lean.Expr} {ca : ConLeche.Expr} (ha : toCL? a = some ca)
    (hca : ca.looseBVarsBounded 0 = true) (e : Lean.Expr) (k : Nat) :
    toCL? (e.instantiate1' a k) = (toCL? e).map (ConLeche.Expr.instantiate1 · ca k) := by
  rw [toCL?_instantiate1' ha]
  simp only [ConLeche.Expr.instantiate1Lift_eq_instantiate1 hca]

/-- `Name.toCL` is injective (`CL ConLeche/Kernel/Name.lean:218 ofLeanName`: componentwise). -/
theorem Name.toCL_injective : Function.Injective Name.toCL := by
  intro a
  induction a with
  | anonymous => intro b h; cases b <;> first | rfl | cases h
  | str p s ih =>
    intro b h
    cases b with
    | str q t =>
      simp only [Name.toCL, ConLeche.Name.ofLeanName, ConLeche.Name.str.injEq] at h
      rw [ih h.1, h.2]
    | _ => cases h
  | num p n ih =>
    intro b h
    cases b with
    | num q m =>
      simp only [Name.toCL, ConLeche.Name.ofLeanName, ConLeche.Name.num.injEq] at h
      rw [ih h.1, h.2]
    | _ => cases h

/-- `Level.toCL` reads the oracle's level instantiation as con-leche's `Level.subst`
(`CL ConLeche/Kernel/Level.lean:33 subst`): both take the first parameter of the list with the
level's name. Reference: `subst_instance_level` (`MR common/theories/Universes.v:2485`). -/
theorem Level.toCL_instLevel {us : List Lean.Level} {us' : List ConLeche.Level}
    (ps : List Name) (hus : us.mapM Level.toCL = some us') : ∀ l : Lean.Level,
    Level.toCL (Pure.instLevel ps us l) = (Level.toCL l).map (ConLeche.Level.subst (ps.map Name.toCL) us') := by
  intro l
  induction l with
  | zero => rfl
  | succ u ih =>
    simp only [Pure.instLevel, Level.toCL, ih]
    cases Level.toCL u <;> rfl
  | max u v ihu ihv | imax u v ihu ihv =>
    simp only [Pure.instLevel, Level.toCL, ihu, ihv]
    cases Level.toCL u <;> cases Level.toCL v <;> rfl
  | mvar _ => rfl
  | param n =>
    simp only [Pure.instLevel, Level.toCL, Option.map_some, ConLeche.Level.subst]
    induction ps generalizing us us' with
    | nil => rfl
    | cons p ps ih =>
      cases us with
      | nil =>
        cases hus
        cases h : ps.map Name.toCL <;> rfl
      | cons u us =>
        simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def,
          Option.bind_eq_some_iff, Option.some.injEq] at hus
        obtain ⟨u', hu', us'', hus'', rfl⟩ := hus
        simp only [List.zip_cons_cons, List.find?_cons, List.map_cons,
          ConLeche.Level.subst.go]
        by_cases h : p = n
        · subst h
          simp [hu']
        · have h' : Name.toCL p ≠ Name.toCL n := fun e => h (Name.toCL_injective e)
          rw [ite_eq_right h']
          simp only [show (p == n) = false from beq_false_of_ne h]
          exact ih hus''

/-- `toCL?` reads the oracle's universe instantiation `Pure.instLevels`, the δ-rule's
(`EraseProof.SrcEval.delta`), as con-leche's `instantiateLevelParams`
(`CL ConLeche/Kernel/Level.lean:234 Expr.instantiateLevelParams`), the instantiation of con-leche's
unfolding. Reference: `subst_instance_constr` (`MR P/PCUICAst.v:404`). -/
theorem toCL?_instLevels {us : List Lean.Level} {us' : List ConLeche.Level}
    (ps : List Name) (hus : us.mapM Level.toCL = some us') : ∀ e : Lean.Expr,
    toCL? (Pure.instLevels ps us e) =
      (toCL? e).map (ConLeche.Expr.instantiateLevelParams (ps.map Name.toCL) us' ·) := by
  intro e
  induction e with
  | app f a ihf iha =>
    simp only [Pure.instLevels, toCL?, ihf, iha]
    cases toCL? f <;> cases toCL? a <;> rfl
  | lam _ t b _ iht ihb | forallE _ t b _ iht ihb =>
    simp only [Pure.instLevels, toCL?, iht, ihb]
    cases toCL? t <;> cases toCL? b <;> rfl
  | letE _ t v b _ iht ihv ihb =>
    simp only [Pure.instLevels, toCL?, iht, ihv, ihb]
    cases toCL? t <;> cases toCL? v <;> cases toCL? b <;> rfl
  | mdata _ e ih => simpa only [Pure.instLevels, toCL?] using ih
  | proj _ _ e ih =>
    simp only [Pure.instLevels, toCL?, ih]
    cases toCL? e <;> rfl
  | sort u =>
    simp only [Pure.instLevels, toCL?, Level.toCL_instLevel ps hus]
    cases Level.toCL u <;> rfl
  | const c ls =>
    have hls : ∀ ls : List Lean.Level, (ls.map (Pure.instLevel ps us)).mapM Level.toCL =
        (ls.mapM Level.toCL).map (·.map (ConLeche.Level.subst (ps.map Name.toCL) us')) := by
      intro ls
      induction ls with
      | nil => rfl
      | cons l ls ih =>
        simp only [List.map_cons, List.mapM_cons, Level.toCL_instLevel ps hus, ih]
        cases Level.toCL l <;> cases ls.mapM Level.toCL <;> rfl
    simp only [Pure.instLevels, toCL?, hls]
    cases ls.mapM Level.toCL <;> rfl
  | lit l => cases l <;> rfl
  | bvar _ | fvar _ | mvar _ => rfl

/-- A reading has no free variable (`CL ConLeche/Kernel/ExprOps.lean:60 hasFvar`): `toCL?` reads
no `fvar` (`CL ConLeche/Frontend/Olean/Spec.lean:43`). -/
theorem toCL?_hasFvar : ∀ {e : Lean.Expr} {c : ConLeche.Expr}, toCL? e = some c → c.hasFvar = false
  | .bvar _, _, h | .sort _, _, h | .const .., _, h | .lit (.natVal _), _, h
  | .lit (.strVal _), _, h => by
    simp only [toCL?, Option.map_eq_map, Option.map_eq_some_iff, Option.some.injEq] at h
    first | (cases h; rfl) | (obtain ⟨_, -, rfl⟩ := h; rfl)
  | .app f a, _, h | .lam _ f a _, _, h | .forallE _ f a _, _, h => by
    simp only [toCL?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨_, hf, _, ha, rfl⟩ := h
    simp [ConLeche.Expr.hasFvar, toCL?_hasFvar hf, toCL?_hasFvar ha]
  | .letE _ t v b _, _, h => by
    simp only [toCL?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨_, ht, _, hv, _, hb, rfl⟩ := h
    simp [ConLeche.Expr.hasFvar, toCL?_hasFvar ht, toCL?_hasFvar hv, toCL?_hasFvar hb]
  | .mdata _ e, _, h => toCL?_hasFvar (e := e) h
  | .proj .., _, h => by
    simp only [toCL?, Option.map_eq_map, Option.map_eq_some_iff] at h
    obtain ⟨_, hp, rfl⟩ := h
    simp [ConLeche.Expr.hasFvar, toCL?_hasFvar hp]
  | .fvar _, _, h | .mvar _, _, h => nomatch h

/-- The reading of a term con-leche's full-grade inference types has no loose bound variable: the
inference throws at one (`CL ConLeche/Verify/Inductives/RecCheckScope.lean:292
infer_full_bvarClosed`, on the derivation of `CL ConLeche/Verify/Rules/Bridge.lean:67
inferTypeCore_bridge`). Reference: `closedn 0 t` of a term typed in the empty context
(`MR P/Typing/PCUICClosedTyp.v:351 subject_closed`). -/
theorem CLTyped.closed {env : ConLeche.Env} {t : Lean.Expr} {c : ConLeche.Expr}
    (h : CLTyped env t) (hc : toCL? t = some c) : c.looseBVarsBounded 0 = true := by
  obtain ⟨c', F, T, hc', hinf⟩ := h
  rw [hc] at hc'
  cases hc'
  exact ConLeche.infer_full_bvarClosed (ConLeche.Rules.inferTypeCore_bridge hinf)

end EraseProof
