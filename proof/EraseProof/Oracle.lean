import EraseProof.Oracle.Infer
import EraseProof.Erasability.Eval

/-!
# Soundness of the erasability oracle

`Pure.isErasable_sound`: when the shipping oracle `Erasure.Pure.isErasable` answers "erasable" on
a translated term, the term's image in lean4lean's model is erasable (`ErasableS`). The proof
follows the oracle: `Pure.inferType_sound` gives a type of the term, `Pure.isArity_sound` turns a
positive arity test into a convertible arity, and otherwise `Pure.inferType_sound`,
`Pure.whnf_sound` and `Pure.alwaysZero_sound` turn the sort test into a proposition sort.
-/

open Lean Lean4Lean Erasure

namespace EraseProof

section
variable {venv : VEnv} {P : List ConstantInfo}

/-- `isArity` answers `true` only on types convertible to an arity. Reference: `is_arityP`
(`MR E/ErasureFunction.v:826`), `true` direction. -/
theorem Pure.isArity_sound (henv : ProgEnv P venv) (hsub : SubEnv cx.decls P)
    (hloc : LocalsOK venv Us ls Δ₀) (hΓ : OracleCtx venv Us Γ Δ₀ Δ)
    (hT : TrS venv Us Δ T T') (hs : venv.HasType Us.length Δ.toCtx T' (.sort u))
    (h : Pure.isArity cx fuel ls T = .ok true) :
    ∃ A, IsArity A ∧ venv.IsDefEq Us.length Δ.toCtx T' A (.sort u) := by
  have hwf := henv.wf
  have h₀ := hloc.wf.1
  induction fuel generalizing Γ Δ T T' u with
  | zero => simp [Pure.isArity, throw, throwThe, MonadExceptOf.throw] at h
  | succ f ih =>
    have hctx : OnCtx Δ.toCtx (venv.IsType Us.length) := (hΓ.wf h₀).1.toCtx
    simp only [Pure.isArity] at h
    obtain ⟨W, h1, h2⟩ := Except.ok_of_bind h
    have ⟨W', tW, dW⟩ := Pure.whnf_sound henv hsub hloc hΓ hT hs h1
    split at h2
    · cases tW with
      | sort _ => exact ⟨.sort _, trivial, dW⟩
    · cases tW with
      | forallE hA hB tA tB =>
        have ⟨_, hA'⟩ := hA
        have ⟨_, hB'⟩ := hB
        have ⟨A₁, har, dB⟩ := ih (OracleCtx.cons hΓ tA hA) tB hB' h2
        have d2 : venv.IsDefEqU Us.length Δ.toCtx _ _ := ⟨_, VEnv.IsDefEq.forallEDF hA' dB⟩
        exact ⟨.forallE _ A₁, har, (VEnv.IsDefEqU.trans hwf hctx ⟨_, dW⟩ d2).of_l hwf hctx hs⟩
    · cases h2

/-- `alwaysZero` recognises levels equivalent to zero. Reference: `Sort.is_propositional`
(`MR common/theories/Universes.v:1528`), soundness. -/
theorem Pure.alwaysZero_sound (h : Pure.alwaysZero u = true)
    (hu : VLevel.ofLevel Us u = some u') : u' ≈ .zero := by
  induction u generalizing u' with
  | zero => simp [VLevel.ofLevel] at hu; subst hu; rfl
  | max a b iha ihb =>
    simp only [Pure.alwaysZero, Bool.and_eq_true] at h
    simp only [VLevel.ofLevel, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hu
    obtain ⟨a', h1, b', h2, rfl⟩ := hu
    exact (VLevel.max_congr (iha h.1 h1) (ihb h.2 h2)).trans VLevel.max_self
  | imax a b _ ihb =>
    simp only [Pure.alwaysZero] at h
    simp only [VLevel.ofLevel, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hu
    obtain ⟨a', h1, b', h2, rfl⟩ := hu
    exact VLevel.imax_eq_zero.2 (ihb h h2)
  | succ | param | mvar => simp [Pure.alwaysZero] at h

/-- The oracle is sound: "erasable" means erasable. Reference: `is_erasableP`
(`MR E/ErasureFunction.v:915`), `true` direction; MC §7.2. -/
theorem Pure.isErasable_sound (henv : ProgEnv P venv) (hsub : SubEnv cx.decls P)
    (hloc : LocalsOK venv Us ls Δ) (he : TrS venv Us Δ e e')
    (h : Pure.isErasable cx fuel ls e = .ok true) : ErasableS venv Us Δ e := by
  have hord := henv.ordered
  have hctx : OnCtx Δ.toCtx (venv.IsType Us.length) := hloc.wf.1.toCtx
  simp only [Pure.isErasable] at h
  obtain ⟨T, h1, h⟩ := Except.ok_of_bind h
  have ⟨T', tT, heT⟩ := Pure.inferType_sound henv hsub hloc .nil he h1
  have ⟨u, hTu⟩ := heT.isType hord hctx
  obtain ⟨b, h2, h⟩ := Except.ok_of_bind h
  cases b with
  | true =>
    have ⟨A, har, dA⟩ := Pure.isArity_sound henv hsub hloc .nil tT hTu h2
    exact ⟨e', he, A, dA.defeq heT, .inl har⟩
  | false =>
    simp only [Bool.false_eq_true, if_false] at h
    obtain ⟨S, h3, h⟩ := Except.ok_of_bind h
    obtain ⟨W, h4, h⟩ := Except.ok_of_bind h
    have ⟨S', tS, hTS⟩ := Pure.inferType_sound henv hsub hloc .nil tT h3
    have ⟨_, hSv⟩ := hTS.isType hord hctx
    have ⟨_, tW, dW⟩ := Pure.whnf_sound henv hsub hloc .nil tS hSv h4
    split at h
    · cases tW with
      | sort hl =>
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact ⟨e', he, T', heT, .inr ⟨_, dW.defeq hTS, Pure.alwaysZero_sound h hl⟩⟩
    · simp [pure, Except.pure] at h

end

end EraseProof
