import EraseProof.Oracle.AtomShapes
import EraseProof.Source.Eval

/-!
# The oracle on atom spines

`Pure.isErasable_atom`: on an application spine `c.{us} a₁ … aₖ` whose head `c` is an atom
(`EvalEnv.isAtom`), the shipping oracle `Erasure.Pure.isErasable` answers `true` or fails, never
`false`, for every list of locals and without a typing hypothesis. The proof follows the oracle on
the shapes of `EraseProof.Oracle.AtomShapes`: the inferred type of a spine over an evident type
former is a syntactic arity, which `Erasure.Pure.isArity` accepts; the inferred type of a spine over
a proof of an evident proposition is an evident proposition, whose inferred sort is a syntactic
sort with an evidently-zero level, which `Erasure.Pure.alwaysZero` accepts
(`Pure.alwaysZero_eq`). Every reduction of the oracle uses the kernel's δ; the heads are
`DeltaFree`, so no δ step fires.
-/

open Lean Erasure

namespace EraseProof

/-! ## `inferType` on spines -/

/-- `inferType` of a constant occurrence is its declared type at the occurrence's levels.
Reference: the `tConst` case of `infer` (`MR S/PCUICSafeRetyping.v:329`), rule `type_Const`
(`MR P/PCUICTyping.v:232`). -/
theorem Pure.inferType_const {cx : Pure.Ctx} {ls : List Local} {f Γ c us S} {ci : ConstantInfo}
    (hf : findConst cx.decls c = some ci)
    (H : Pure.inferType cx (f + 1) ls Γ (.const c us) = .ok S) :
    S = Pure.instLevels ci.levelParams us ci.type := by
  rw [Pure.inferType, hf] at H
  by_cases hl : (us.length == ci.levelParams.length) = true
  · simp only [hl, if_true, pure, Except.pure, Except.ok.injEq] at H; exact H.symm
  · simp only [hl] at H; exact absurd H Except.throw_ne_ok

/-- The inferred type of a spine `h.{vs} a₁ … aₖ` over a constant whose declared type is the
syntactic arity `Π x₁…xₙ, Sort u0` is a syntactic arity of `n - k` binders ending in `u0` at the
occurrence levels `vs`. Reference: `type_mkApps_arity` (`MR P/PCUICValidity.v:420`), with
`isArity_subst_instance` (`MR P/Typing/PCUICUnivSubstitutionTyp.v:537`) and `isArity_subst`
(`MR P/PCUICClassification.v:33`). -/
theorem Pure.inferType_constSpine_arity {cx : Pure.Ctx} {ls : List Local} {h : Name}
    {ci : ConstantInfo} {n : Nat} {u0 : Level}
    (hf : findConst cx.decls h = some ci) (ha : arityShape ci.type = some (n, u0)) :
    ∀ {f Γ T S vs k}, ConstSpine h vs k T → Pure.inferType cx f ls Γ T = .ok S →
      ∃ m, ArityShape S m (Pure.instLevel ci.levelParams vs u0) ∧ m + k = n
  | 0, _, _, _, _, _, _, H => absurd H (by rw [Pure.inferType]; exact Except.throw_ne_ok)
  | f + 1, Γ, _, S, _, _, .const, H => by
    rw [Pure.inferType_const hf H]
    exact ⟨n, (ArityShape.of_arityShape ha).instLevels, by omega⟩
  | f + 1, Γ, _, S, _, _, .app (f := g) (a := a) hg, H => by
    rw [Pure.inferType] at H
    obtain ⟨Tg, h1, H⟩ := Except.ok_of_bind H
    obtain ⟨w, h2, H⟩ := Except.ok_of_bind H
    obtain ⟨m, has, hm⟩ := inferType_constSpine_arity hf ha hg h1
    obtain ⟨has', -⟩ := Pure.whnf_arityShape has h2
    split at H
    · cases H
      cases has' with
      | forallE hB => exact ⟨_, hB.inst, by omega⟩
    · exact absurd H Except.throw_ne_ok

/-- The inferred type of a spine over a constant whose declared type is an evident proposition is
an evident proposition. Reference: the `tApp` and `tConst` cases of `infer`
(`MR S/PCUICSafeRetyping.v:324,329`); `isPropositional` reads only the declaration
(`MR P/PCUICFirstorder.v:109`), DV-11. -/
theorem Pure.inferType_constSpine_prop {cx : Pure.Ctx} {ls : List Local} {c : Name}
    {ci : ConstantInfo} (hf : findConst cx.decls c = some ci) (hp : PropShape cx.decls ci.type) :
    ∀ {f Γ T S us k}, ConstSpine c us k T → Pure.inferType cx f ls Γ T = .ok S →
      PropShape cx.decls S
  | 0, _, _, _, _, _, _, H => absurd H (by rw [Pure.inferType]; exact Except.throw_ne_ok)
  | f + 1, Γ, _, S, _, _, .const, H => by
    rw [Pure.inferType_const hf H]; exact hp.instLevels
  | f + 1, Γ, _, S, _, _, .app (f := g) (a := a) hg, H => by
    rw [Pure.inferType] at H
    obtain ⟨Tg, h1, H⟩ := Except.ok_of_bind H
    obtain ⟨w, h2, H⟩ := Except.ok_of_bind H
    obtain ⟨hw, -⟩ := Pure.whnf_propShape (inferType_constSpine_prop hf hp hg h1) h2
    split at H
    · cases H
      cases hw with
      | forallE hB => exact hB.inst
      | tail _ _ _ _ h5 => exact absurd rfl (h5.ne_forallE _ _ _ _)
    · exact absurd H Except.throw_ne_ok

/-- The inferred type of an evident proposition is a sort whose level is evidently zero.
Reference: the `tProd` case of `infer` (`MR S/PCUICSafeRetyping.v:308`), with
`isPropositionalArity` (`MR P/PCUICFirstorder.v:103`), DV-4, DV-11. -/
theorem Pure.inferType_propShape {cx : Pure.Ctx} {ls : List Local} :
    ∀ {f Γ T S}, PropShape cx.decls T → Pure.inferType cx f ls Γ T = .ok S →
      ∃ lvl, ArityShape S 0 lvl ∧ EvidentZero lvl = true
  | f, Γ, _, S, .tail h1 h2 h3 h4 h5, H => by
    obtain ⟨m, has, hm⟩ := Pure.inferType_constSpine_arity h1 h3 h5 H
    exact ⟨_, by rwa [show m = 0 by omega] at has, h4⟩
  | 0, _, _, _, .forallE _, H | 0, _, _, _, .mdata _, H =>
    absurd H (by rw [Pure.inferType]; exact Except.throw_ne_ok)
  | f + 1, Γ, _, S, .mdata H', H => by
    rw [Pure.inferType] at H; exact inferType_propShape H' H
  | f + 1, Γ, _, S, .forallE (b := b) (t := t) H', H => by
    rw [Pure.inferType] at H
    obtain ⟨Tt, -, H⟩ := Except.ok_of_bind H
    obtain ⟨w1, -, H⟩ := Except.ok_of_bind H
    split at H
    · obtain ⟨Tb, h3, H⟩ := Except.ok_of_bind H
      obtain ⟨w2, h4, H⟩ := Except.ok_of_bind H
      obtain ⟨lvl, has, hz⟩ := inferType_propShape H' h3
      obtain ⟨has', hnm⟩ := Pure.whnf_arityShape has h4
      split at H
      · cases H
        cases has' with
        | sort => exact ⟨_, .sort, by simpa [EvidentZero] using hz⟩
      · cases has' with
        | sort => rename_i hns; exact absurd rfl (hns _)
        | mdata => exact absurd rfl (hnm _ _)
    · exact absurd H Except.throw_ne_ok

/-! ## `isArity` -/

/-- `isArity` never answers `false` on a syntactic arity. Reference: `is_arity`
(`MR E/ErasureFunction.v:784`), the `false` direction of `is_arityP` (`:826`). -/
theorem Pure.isArity_arityShape {cx : Pure.Ctx} {ls : List Local} :
    ∀ {f T b n u}, ArityShape T n u → Pure.isArity cx f ls T = .ok b → b = true
  | 0, _, _, _, _, _, h => absurd h (by rw [Pure.isArity]; exact Except.throw_ne_ok)
  | f + 1, T, b, n, u, H, h => by
    rw [Pure.isArity] at h
    obtain ⟨w, h1, h⟩ := Except.ok_of_bind h
    obtain ⟨hw, hnm⟩ := Pure.whnf_arityShape H h1
    split at h
    · cases h; rfl
    · cases hw with
      | forallE hB => exact isArity_arityShape hB h
    · next _ hns hnf =>
      cases hw with
      | sort => exact absurd rfl (hns _)
      | forallE => exact absurd rfl (hnf _ _ _ _)
      | mdata => exact absurd rfl (hnm _ _)

/-! ## The atom lemma -/

/-- An atom spine is a constant's spine with an atom head. Reference: `mkApps_decompose_app`
(`MR P/utils/PCUICAstUtils.v:166`) on the values `mkApps (tInd …) args` of
`MR P/PCUICWcbvEval.v:500 value`, DV-11. -/
theorem AtomSpine.constSpine {σ : EvalEnv} {e : Expr} (H : AtomSpine σ e) :
    ∃ c us k, σ.isAtom c = true ∧ ConstSpine c us k e := by
  induction H with
  | const ha => exact ⟨_, _, 0, ha, .const⟩
  | app _ ih =>
    obtain ⟨c, us, k, ha, hs⟩ := ih
    exact ⟨c, us, k + 1, ha, .app hs⟩

/-- The oracle's level test is the specification's. Reference: none (pins `Pure.alwaysZero` to
`EvidentZero`, DV-4, DV-11). -/
theorem Pure.alwaysZero_eq : Pure.alwaysZero = EvidentZero := by
  funext u
  induction u with
  | max a b iha ihb => simp only [Pure.alwaysZero, EvidentZero, iha, ihb]
  | imax a b _ ihb => simp only [Pure.alwaysZero, EvidentZero, ihb]
  | zero | succ _ _ | param _ | mvar _ => rfl

section
variable {σ : EvalEnv}

/-- On an atom spine the oracle never answers `false` (it may fail): the eraser boxes atoms, for
every list of locals, with no typing hypothesis. Reference: none directly; it plays the part
of `isErasable` on `tInd` and on propositional constructors (`MR E/Extract.v:106`); DV-11. -/
theorem Pure.isErasable_atom (hcx : cx.decls = σ.decls) (hsp : AtomSpine σ e)
    (h : Pure.isErasable cx fuel ls e = .ok b) : b = true := by
  obtain ⟨c, us, k, ha, hs⟩ := hsp.constSpine
  simp only [EvalEnv.isAtom] at ha
  split at ha
  · rename_i ci hci
    have hf : findConst cx.decls c = some ci := by rw [hcx]; exact hci
    simp only [Bool.and_eq_true, Bool.or_eq_true] at ha
    obtain ⟨-, hty⟩ := ha
    simp only [Pure.isErasable] at h
    obtain ⟨T, h1, h⟩ := Except.ok_of_bind h
    obtain ⟨ba, h2, h⟩ := Except.ok_of_bind h
    rcases hty with hA | hB
    · -- an evident type former: `isArity` answers `true`
      obtain ⟨⟨n, u⟩, hn⟩ := Option.isSome_iff_exists.1 hA
      obtain ⟨m, has, -⟩ := Pure.inferType_constSpine_arity hf hn hs h1
      have := Pure.isArity_arityShape has h2; subst this
      cases h; rfl
    · -- a proof of an evident proposition: the sort test answers `true`
      have hp : PropShape cx.decls ci.type := hcx ▸ PropShape.of_evidentProp _ hB
      have hT := Pure.inferType_constSpine_prop hf hp hs h1
      split at h
      · cases h; rfl
      · obtain ⟨S, h3, h⟩ := Except.ok_of_bind h
        obtain ⟨w, h4, h⟩ := Except.ok_of_bind h
        obtain ⟨lvl, has, hz⟩ := Pure.inferType_propShape hT h3
        obtain ⟨has', hnm⟩ := Pure.whnf_arityShape has h4
        split at h
        · cases h
          cases has' with
          | sort => rw [Pure.alwaysZero_eq]; exact hz
        · cases has' with
          | sort => rename_i hns; exact absurd rfl (hns _)
          | mdata => exact absurd rfl (hnm _ _)
  · cases ha

end

end EraseProof
