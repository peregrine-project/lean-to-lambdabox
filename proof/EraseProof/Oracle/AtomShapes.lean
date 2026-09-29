import EraseProof.Atoms
import EraseProof.Oracle.Agree

/-!
# Shapes of atom spines under the oracle's weak-head reduction

Inductive forms of the syntactic shapes that the oracle meets on an atom spine: arities
(`ArityShape`, the inductive form of `arityShape`), application spines of a constant occurrence
(`ConstSpine`) and evident propositions (`PropShape`, the inductive form of `EvidentProp`). The
shapes survive the oracle's substitutions (`Expr.instantiate1'` and `Erasure.Pure.instLevels`),
and `Erasure.Pure.whnf` keeps them: an arity or an evident proposition reduces to one of the same
shape without top-level `mdata`, and a spine whose head is `DeltaFree` is in weak-head normal
form. No lemma takes a typing hypothesis.
-/

open Lean Erasure

namespace EraseProof

/-! ## Shapes -/

/-- `ArityShape T n u`: `T` is the syntactic arity `Π x₁…xₙ, Sort u` (`mdata` transparent), the
inductive form of `arityShape`. Reference: `isArity` (`MR P/PCUICTyping.v:29`). -/
inductive ArityShape : Expr → Nat → Level → Prop
  | sort : ArityShape (.sort u) 0 u
  | forallE : ArityShape b n u → ArityShape (.forallE nm t b bi) (n + 1) u
  | mdata : ArityShape e n u → ArityShape (.mdata m e) n u

/-- `ConstSpine h vs k e`: `e` is the application spine `h.{vs} a₁ … aₖ` of a constant occurrence.
Reference: `mkApps (tConst h vs) args` (`MR P/PCUICAst.v:221 mkApps`). -/
inductive ConstSpine (h : Name) (vs : List Level) : Nat → Expr → Prop
  | const : ConstSpine h vs 0 (.const h vs)
  | app : ConstSpine h vs k f → ConstSpine h vs (k + 1) (.app f a)

/-- `PropShape D e`: `e` is an evident proposition over the declarations `D`, the inductive form of
`EvidentProp`: `Π x₁…xₘ, h.{vs} a₁…aₖ` with a `DeltaFree` head whose declared type is a syntactic
arity of `k` binders ending in `Sort u`, and `u` at the occurrence levels `vs` evidently zero.
Reference: `isPropositional` (`MR P/PCUICFirstorder.v:109`), DV-11. -/
inductive PropShape (D : List ConstantInfo) : Expr → Prop
  | forallE : PropShape D b → PropShape D (.forallE nm t b bi)
  | mdata : PropShape D e → PropShape D (.mdata m e)
  | tail : findDecl D h = some ci → DeltaFree ci = true → arityShape ci.type = some (k, u) →
      EvidentZero (Pure.instLevel ci.levelParams vs u) = true → ConstSpine h vs k e →
      PropShape D e

/-! ## From the Boolean definitions -/

/-- `arityShape` answers only on arities. Reference: `destArity` (`MR P/PCUICAst.v:486`), whose
answer is an arity. -/
theorem ArityShape.of_arityShape : ∀ {T : Expr} {n u}, arityShape T = some (n, u) →
    ArityShape T n u
  | .sort _, n, u, h => by
    simp only [arityShape, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact .sort
  | .forallE _ _ b _, n, u, h => by
    simp only [arityShape, Option.map_eq_some_iff] at h
    obtain ⟨⟨n', u'⟩, h1, h2⟩ := h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    exact .forallE (of_arityShape h1)
  | .mdata _ e, n, u, h => by
    simp only [arityShape] at h; exact .mdata (of_arityShape h)
  | .bvar _, _, _, h | .fvar _, _, _, h | .mvar _, _, _, h | .const .., _, _, h
  | .app .., _, _, h | .lam .., _, _, h | .letE .., _, _, h | .lit _, _, _, h
  | .proj .., _, _, h => by simp [arityShape] at h

/-- A term whose head is a constant occurrence is the spine of that occurrence over its arguments.
Reference: `mkApps_decompose_app` (`MR P/utils/PCUICAstUtils.v:166`). -/
theorem ConstSpine.of_getAppFn : ∀ {e : Expr} {h us}, e.getAppFn = .const h us →
    ConstSpine h us e.getAppNumArgs e
  | .const _ _, h, us, H => by
    simp only [Expr.getAppFn, Expr.const.injEq] at H; obtain ⟨rfl, rfl⟩ := H; exact .const
  | .app f a, h, us, H => by
    simp only [Expr.getAppFn] at H
    have hnum : (Expr.app f a).getAppNumArgs = f.getAppNumArgs + 1 := by
      simp [Expr.getAppNumArgs_eq, Expr.getAppArgsRevList]
    rw [hnum]; exact .app (of_getAppFn H)
  | .bvar _, _, _, H | .fvar _, _, _, H | .mvar _, _, _, H | .sort _, _, _, H | .lam .., _, _, H
  | .forallE .., _, _, H | .letE .., _, _, H | .lit _, _, _, H | .mdata .., _, _, H
  | .proj .., _, _, H => by simp [Expr.getAppFn] at H

/-- The spine case of `PropShape.of_evidentProp`: a term that is neither a Π nor `mdata` and that
`EvidentProp` accepts is an evident-proposition spine. Reference: as `PropShape.of_evidentProp`. -/
theorem PropShape.of_evidentProp_tail {D : List ConstantInfo} {e : Expr}
    (hnf : ∀ n t b bi, e = Expr.forallE n t b bi → False)
    (hnm : ∀ m x, e = Expr.mdata m x → False) (H : EvidentProp D e = true) : PropShape D e := by
  rw [EvidentProp.eq_3 D e hnf hnm] at H
  split at H
  next h us hfn =>
    split at H
    next ci hci =>
      simp only [Bool.and_eq_true] at H
      obtain ⟨hdf, H⟩ := H
      split at H
      next n u hsh =>
        simp only [Bool.and_eq_true, beq_iff_eq] at H
        obtain ⟨rfl, hz⟩ := H
        exact .tail hci hdf hsh hz (ConstSpine.of_getAppFn hfn)
      next => cases H
    next => cases H
  next => cases H

/-- `EvidentProp` answers only on evident propositions. Reference: `isPropositional`
(`MR P/PCUICFirstorder.v:109`), DV-11. -/
theorem PropShape.of_evidentProp {D : List ConstantInfo} (T : Expr) (H : EvidentProp D T = true) :
    PropShape D T := by
  induction T with
  | forallE n t b bi _ ihb => simp only [EvidentProp] at H; exact .forallE (ihb H)
  | mdata m e ih => simp only [EvidentProp] at H; exact .mdata (ih H)
  | _ => exact of_evidentProp_tail (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h) H

/-! ## Levels -/

/-- Evident zeroness survives universe instantiation. Reference: `is_propositional_subst_instance`
(`MR P/PCUICElimination.v:278`), DV-4. -/
theorem EvidentZero.instLevel {ps : List Name} {us : List Level} :
    ∀ {u : Level}, EvidentZero u = true → EvidentZero (Pure.instLevel ps us u) = true
  | .zero, _ => rfl
  | .max a b, h => by
    simp only [EvidentZero, Bool.and_eq_true, Pure.instLevel] at h ⊢
    exact ⟨EvidentZero.instLevel h.1, EvidentZero.instLevel h.2⟩
  | .imax a b, h => by
    simp only [EvidentZero, Pure.instLevel] at h ⊢; exact EvidentZero.instLevel h
  | .succ _, h | .param _, h | .mvar _, h => by simp [EvidentZero] at h

/-- Looking a name up in the parameters zipped with mapped levels maps the found level.
Reference: none (list lemma). -/
theorem find?_zip_map {g : Level → Level} {n : Name} :
    ∀ (qs : List Name) (vs : List Level),
      (qs.zip (vs.map g)).find? (·.1 == n) =
        ((qs.zip vs).find? (·.1 == n)).map fun p => (p.1, g p.2)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | q :: qs, v :: vs => by
    simp only [List.map_cons, List.zip_cons_cons, List.find?_cons]
    cases (q == n) with
    | true => rfl
    | false => exact find?_zip_map qs vs

/-- Evident zeroness of a level at an occurrence `h.{vs}` survives a further instantiation of the
occurrence's levels `vs`. Reference: `is_propositional_subst_instance`
(`MR P/PCUICElimination.v:278`) with `subst_instance_level_two`
(`MR P/Conversion/PCUICUnivSubstitutionConv.v:282`), DV-4. -/
theorem EvidentZero.instLevel_map {qs ps : List Name} {vs us : List Level} :
    ∀ {u : Level}, EvidentZero (Pure.instLevel qs vs u) = true →
      EvidentZero (Pure.instLevel qs (vs.map (Pure.instLevel ps us)) u) = true
  | .zero, _ => rfl
  | .max a b, h => by
    simp only [EvidentZero, Bool.and_eq_true, Pure.instLevel] at h ⊢
    exact ⟨EvidentZero.instLevel_map h.1, EvidentZero.instLevel_map h.2⟩
  | .imax a b, h => by
    simp only [EvidentZero, Pure.instLevel] at h ⊢; exact EvidentZero.instLevel_map h
  | .succ _, h | .mvar _, h => by simp [EvidentZero, Pure.instLevel] at h
  | .param n, h => by
    simp only [Pure.instLevel] at h ⊢
    rw [find?_zip_map]
    cases hf : (qs.zip vs).find? (·.1 == n) with
    | none => rw [hf] at h; simp [EvidentZero] at h
    | some p => rw [hf] at h; exact EvidentZero.instLevel h

/-! ## Stability under instantiation -/

/-- Substitution keeps a syntactic arity. Reference: `isArity_subst`
(`MR P/PCUICClassification.v:33`). -/
theorem ArityShape.inst (H : ArityShape T n u) : ∀ {d}, ArityShape (T.instantiate1' a d) n u := by
  induction H with
  | sort => intro d; exact .sort
  | forallE _ ih => intro d; exact .forallE ih
  | mdata _ ih => intro d; exact .mdata ih

/-- Substitution keeps a constant's spine. Reference: `subst_mkApps`
(`MR P/Syntax/PCUICLiftSubst.v:251`). -/
theorem ConstSpine.inst (H : ConstSpine h vs k T) :
    ∀ {d}, ConstSpine h vs k (T.instantiate1' a d) := by
  induction H with
  | const => intro d; exact .const
  | app _ ih => intro d; exact .app ih

/-- Substitution keeps an evident proposition. Reference: `isPropositional` reads only the
inductive's declaration (`MR P/PCUICFirstorder.v:109`), with `subst_mkApps`
(`MR P/Syntax/PCUICLiftSubst.v:251`). -/
theorem PropShape.inst (H : PropShape D T) : ∀ {d}, PropShape D (T.instantiate1' a d) := by
  induction H with
  | forallE _ ih => intro d; exact .forallE ih
  | mdata _ ih => intro d; exact .mdata ih
  | tail h1 h2 h3 h4 h5 => intro d; exact .tail h1 h2 h3 h4 h5.inst

/-- Universe instantiation keeps a syntactic arity and instantiates its final level. Reference:
`isArity_subst_instance` (`MR P/Typing/PCUICUnivSubstitutionTyp.v:537`). -/
theorem ArityShape.instLevels (H : ArityShape T n u) :
    ArityShape (Pure.instLevels ps us T) n (Pure.instLevel ps us u) := by
  induction H with
  | sort => exact .sort
  | forallE _ ih => exact .forallE ih
  | mdata _ ih => exact .mdata ih

/-- Universe instantiation keeps a constant's spine and instantiates the occurrence's levels.
Reference: `subst_instance_mkApps` (`MR P/Syntax/PCUICUnivSubst.v:36`). -/
theorem ConstSpine.instLevels (H : ConstSpine h vs k T) :
    ConstSpine h (vs.map (Pure.instLevel ps us)) k (Pure.instLevels ps us T) := by
  induction H with
  | const => exact .const
  | app _ ih => exact .app ih

/-- Universe instantiation keeps an evident proposition. Reference: `is_propositional_subst_instance`
(`MR P/PCUICElimination.v:278`) with `subst_instance_mkApps` (`MR P/Syntax/PCUICUnivSubst.v:36`),
DV-11. -/
theorem PropShape.instLevels (H : PropShape D T) : PropShape D (Pure.instLevels ps us T) := by
  induction H with
  | forallE _ ih => exact .forallE ih
  | mdata _ ih => exact .mdata ih
  | tail h1 h2 h3 h4 h5 => exact .tail h1 h2 h3 (EvidentZero.instLevel_map h4) h5.instLevels

/-! ## Inversions -/

/-- A constant's spine is not `mdata`. Reference: none (PCUIC has no `mdata`). -/
theorem ConstSpine.ne_mdata (H : ConstSpine h vs k T) : ∀ m e, T ≠ .mdata m e := by
  cases H <;> intro m e h <;> cases h

/-- A constant's spine is not a λ. Reference: `mkApps_discr`
(`MR P/utils/PCUICAstUtils.v:219`). -/
theorem ConstSpine.ne_lam (H : ConstSpine h vs k T) : ∀ n t b bi, T ≠ .lam n t b bi := by
  cases H <;> intro n t b bi h <;> cases h

/-- A constant's spine is not a Π. Reference: `mkApps_discr`
(`MR P/utils/PCUICAstUtils.v:219`). -/
theorem ConstSpine.ne_forallE (H : ConstSpine h vs k T) : ∀ n t b bi, T ≠ .forallE n t b bi := by
  cases H <;> intro n t b bi h <;> cases h

/-! ## `whnf` -/

/-- A failure is not a success. Reference: none. -/
theorem Except.throw_ne_ok {α} {e : EraseError} {a : α} :
    (throw e : Except EraseError α) ≠ .ok a := by
  simp [throw, throwThe, MonadExceptOf.throw]

/-- A sort is in weak-head normal form. Reference: `whnf_sort` (`MR P/PCUICNormal.v:109`). -/
theorem Pure.whnf_sort {cx : Pure.Ctx} {ls : List Local} {f u} :
    Pure.whnf cx (f + 1) ls (.sort u) = .ok (.sort u) := rfl

/-- A Π is in weak-head normal form. Reference: `whnf_prod` (`MR P/PCUICNormal.v:110`). -/
theorem Pure.whnf_forallE {cx : Pure.Ctx} {ls : List Local} {f nm t b bi} :
    Pure.whnf cx (f + 1) ls (.forallE nm t b bi) = .ok (.forallE nm t b bi) := rfl

/-- `whnf` looks through `mdata`. Reference: none (PCUIC has no `mdata`). -/
theorem Pure.whnf_mdata {cx : Pure.Ctx} {ls : List Local} {f m e} :
    Pure.whnf cx (f + 1) ls (.mdata m e) = Pure.whnf cx f ls e := rfl

/-- A `DeltaFree` constant is in weak-head normal form. Reference: `whne_const`
(`MR P/PCUICNormal.v:66`), a constant without a body. -/
theorem Pure.whnf_const_deltaFree {cx : Pure.Ctx} {ls : List Local} {f h us} {ci : ConstantInfo}
    (hf : findConst cx.decls h = some ci) (hd : DeltaFree ci = true) :
    Pure.whnf cx (f + 1) ls (.const h us) = .ok (.const h us) := by
  rw [Pure.whnf, hf]; cases ci <;> simp [DeltaFree] at hd <;> rfl

/-- `whnf` of a syntactic arity is an arity with the same binder count and final level, without
top-level `mdata`. Reference: `whnf_sort`, `whnf_prod` (`MR P/PCUICNormal.v:109,110`). -/
theorem Pure.whnf_arityShape {cx : Pure.Ctx} {ls : List Local} :
    ∀ {f T w n u}, ArityShape T n u → Pure.whnf cx f ls T = .ok w →
      ArityShape w n u ∧ ∀ m e, w ≠ .mdata m e
  | 0, _, _, _, _, _, h => absurd h (by rw [Pure.whnf]; exact Except.throw_ne_ok)
  | f + 1, _, w, _, _, .sort, h => by
    rw [Pure.whnf_sort] at h; cases h; exact ⟨.sort, fun _ _ h => by cases h⟩
  | f + 1, _, w, _, _, .forallE H, h => by
    rw [Pure.whnf_forallE] at h; cases h; exact ⟨.forallE H, fun _ _ h => by cases h⟩
  | f + 1, _, w, _, _, .mdata H, h => by
    rw [Pure.whnf_mdata] at h; exact whnf_arityShape H h

/-- `whnf` of a spine whose head is `DeltaFree` returns it unchanged. Reference: `whne_mkApps`
(`MR P/PCUICNormal.v:121`) over `whne_const` (`:66`). -/
theorem Pure.whnf_constSpine {cx : Pure.Ctx} {ls : List Local} {h : Name} {ci : ConstantInfo}
    (hf : findConst cx.decls h = some ci) (hd : DeltaFree ci = true) :
    ∀ {f T w vs k}, ConstSpine h vs k T → Pure.whnf cx f ls T = .ok w → w = T
  | 0, _, _, _, _, _, H => absurd H (by rw [Pure.whnf]; exact Except.throw_ne_ok)
  | f + 1, _, w, _, _, .const, H => by
    rw [Pure.whnf_const_deltaFree hf hd] at H; cases H; rfl
  | f + 1, _, w, _, _, .app (f := g) (a := a) hg, H => by
    rw [Pure.whnf] at H
    obtain ⟨g', h1, h2⟩ := Except.ok_of_bind H
    have := whnf_constSpine hf hd hg h1; subst this
    split at h2
    · exact absurd rfl (hg.ne_lam _ _ _ _)
    · cases h2; rfl

/-- `whnf` of an evident proposition is an evident proposition without top-level `mdata`.
Reference: `whnf_prod` (`MR P/PCUICNormal.v:110`), `whne_mkApps` (`:121`). -/
theorem Pure.whnf_propShape {cx : Pure.Ctx} {ls : List Local} :
    ∀ {f T w}, PropShape cx.decls T → Pure.whnf cx f ls T = .ok w →
      PropShape cx.decls w ∧ ∀ m e, w ≠ .mdata m e
  | 0, _, _, _, h => absurd h (by rw [Pure.whnf]; exact Except.throw_ne_ok)
  | f + 1, _, w, .forallE H, h => by
    rw [Pure.whnf_forallE] at h; cases h; exact ⟨.forallE H, fun _ _ h => by cases h⟩
  | f + 1, _, w, .mdata H, h => by
    rw [Pure.whnf_mdata] at h; exact whnf_propShape H h
  | f + 1, _, w, .tail h1 h2 h3 h4 h5, h => by
    have := Pure.whnf_constSpine h1 h2 h5 h; subst this
    exact ⟨.tail h1 h2 h3 h4 h5, h5.ne_mdata⟩

end EraseProof
