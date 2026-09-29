import EraseProof.Oracle.Whnf

/-!
# Soundness of the oracle's type inference

`Pure.inferType_sound`: a successful run of `Erasure.Pure.inferType` on a translated term returns a
translated type of the term's image in lean4lean's model. The contexts are those of
`Pure.whnf_sound`: the traversal's locals (`LocalsOK`) under the de Bruijn entries of the binders
the oracle entered (`OracleCtx`), whose types the oracle keeps in its list `Γ`.

The proof is a fuel induction: `bvar` by `OracleCtx.find_bvar` (`TrS.weakBV`), `fvar` by
`LocalsOK.find_type`, `const` by `ProgEnv.lookup` and `TrS.instLevels`, `app` by `Pure.whnf_sound`
on the function's type with lean4lean's `IsDefEq.uniqU` and `IsDefEqU.forallE_inv`, `forallE` by
`Pure.whnf_sound` on the two sorts, `letE` by `TrS.inst_let`; `lam` and `mdata` are structural.
-/

open Lean Lean4Lean Erasure

namespace EraseProof

section
variable {venv : VEnv} {P : List ConstantInfo}

/-- The type of a traversal local translates to the type of its variable's entry. Reference: the
type `decl_type` read by `nth_error Γ` in `type_Rel` (`MR pcuic/theories/PCUICTyping.v:199`). -/
theorem LocalsOK.find_type (henv : venv.Ordered) (hloc : LocalsOK venv Us ls Δ)
    (hl : Pure.findLocal ls x = some l) :
    ∃ e₀ A₀, Δ.find? (.inr x) = some (e₀, A₀) ∧ TrS venv Us Δ l.type A₀ := by
  have hwf := hloc.wf.1
  induction hloc generalizing l with
  | nil => cases hl
  | @lam ls A' l0 Δ _ _ _ htA _ ih =>
    simp only [Pure.findLocal, List.find?_cons] at hl
    cases hb : l0.fvarId == x with
    | true =>
      rw [hb] at hl; cases hl
      refine ⟨.bvar 0, A'.lift, ?_, ?_⟩
      · simp [VLCtx.find?, VLCtx.next, hb, VLocalDecl.value, VLocalDecl.type]
      · simpa [VLocalDecl.depth] using htA.weakFV henv (.skip_fvar _ (.vlam A') .refl) hwf
    | false =>
      rw [hb] at hl
      have ⟨e₀, A₀, h1, h2⟩ := ih hl hwf.1
      refine ⟨e₀.liftN 1, A₀.liftN 1, ?_, ?_⟩
      · simp [VLCtx.find?, VLCtx.next, hb, h1, VLocalDecl.depth]
      · simpa [VLocalDecl.depth] using h2.weakFV henv (.skip_fvar _ (.vlam A') .refl) hwf
  | @letE ls val T' v' l0 Δ _ _ _ htT _ _ ih =>
    simp only [Pure.findLocal, List.find?_cons] at hl
    cases hb : l0.fvarId == x with
    | true =>
      rw [hb] at hl; cases hl
      refine ⟨v', T', ?_, ?_⟩
      · simp [VLCtx.find?, VLCtx.next, hb, VLocalDecl.value, VLocalDecl.type]
      · simpa [VLocalDecl.depth] using htT.weakFV henv (.skip_fvar _ (.vlet T' v') .refl) hwf
    | false =>
      rw [hb] at hl
      have ⟨e₀, A₀, h1, h2⟩ := ih hl hwf.1
      refine ⟨e₀, A₀, ?_, ?_⟩
      · simp [VLCtx.find?, VLCtx.next, hb, h1, VLocalDecl.depth]
      · simpa [VLocalDecl.depth] using h2.weakFV henv (.skip_fvar _ (.vlet T' v') .refl) hwf

/-- The type the oracle keeps for its `i`-th binder, lifted over the `i + 1` binders entered
after it, translates to the type of the de Bruijn entry `i`. Reference: `type_Rel`
(`MR pcuic/theories/PCUICTyping.v:199`), the type `lift0 (S n) (decl_type decl)`. -/
theorem OracleCtx.find_bvar (henv : venv.Ordered) (hΓ : OracleCtx venv Us Γ Δ₀ Δ) :
    ∀ {i A e T}, Γ[i]? = some A → Δ.find? (.inl i) = some (e, T) →
      TrS venv Us Δ (A.liftLooseBVars' 0 (i + 1)) T := by
  induction hΓ with
  | nil => intro i A e T h; simp at h
  | @cons Γ Δ₀ Δ A0 A0' _ tA _ ih =>
    intro i A e T hA hf
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hA
      subst hA
      simp [VLCtx.find?, VLCtx.next, VLocalDecl.value, VLocalDecl.type] at hf
      obtain ⟨rfl, rfl⟩ := hf
      simpa [VLocalDecl.depth] using tA.weakBV henv (.skip (.vlam A0') .refl)
    | succ i =>
      simp only [List.getElem?_cons_succ] at hA
      simp [VLCtx.find?, VLCtx.next, bind] at hf
      obtain ⟨e0, T0, hf, rfl, rfl⟩ := hf
      have := (ih hA hf).weakBV henv (.skip (.vlam A0') .refl)
      simpa [VLocalDecl.depth, Expr.liftLooseBVars_add] using this

/-- `inferType` computes a type. Reference: the specification carried by `type_of_typing`
(`MR S/PCUICSafeRetyping.v:806`). -/
theorem Pure.inferType_sound (henv : ProgEnv P venv) (hsub : SubEnv cx.decls P)
    (hloc : LocalsOK venv Us ls Δ₀) (hΓ : OracleCtx venv Us Γ Δ₀ Δ)
    (he : TrS venv Us Δ e e') (h : Pure.inferType cx fuel ls Γ e = .ok T) :
    ∃ T', TrS venv Us Δ T T' ∧ venv.HasType Us.length Δ.toCtx e' T' := by
  have hord := henv.ordered
  have hwf := henv.wf
  have ⟨h₀, hnb⟩ := hloc.wf
  induction fuel generalizing Γ Δ e e' T with
  | zero => simp [Pure.inferType, throw, throwThe, MonadExceptOf.throw] at h
  | succ f ih =>
    have hΔ := (hΓ.wf h₀).1
    have hctx : OnCtx Δ.toCtx (venv.IsType Us.length) := hΔ.toCtx
    cases he with
    | bvar hf =>
      simp only [Pure.inferType] at h
      split at h
      · rename_i A hA
        cases h
        exact ⟨_, hΓ.find_bvar hord hA hf, hΔ.find?_wf hord hf⟩
      · simp [throw, throwThe, MonadExceptOf.throw] at h
    | fvar hf =>
      simp only [Pure.inferType] at h
      split at h
      · rename_i l hl
        cases h
        have ⟨e₀, A₀, h1, h2⟩ := LocalsOK.find_type hord hloc hl
        have hc : Closed l.type := by simpa [hnb] using h2.closed
        have tT := hΓ.weak hord h₀ hc h2
        have h1' := VLCtx.BVLift.find? (hΓ.wf h₀).2 h1
        simp only [VLCtx.liftVar] at h1'
        rw [hf] at h1'
        cases h1'
        exact ⟨_, tT, hΔ.find?_wf hord hf⟩
      · simp [throw, throwThe, MonadExceptOf.throw] at h
    | sort hu =>
      simp only [Pure.inferType, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨_, .sort (by simp [VLevel.ofLevel, hu]), .sort (.of_ofLevel hu)⟩
    | @const c ci0 us' _ us hc0 hus hlen =>
      simp only [Pure.inferType] at h
      split at h
      · rename_i ci hci
        split at h
        · rename_i hl
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          have hl : us.length = ci.levelParams.length := by simpa using hl
          have hname : ci.name = c :=
            beq_iff_eq.1 (List.find?_some (p := fun x : ConstantInfo => x.name == c) hci)
          have hP := hsub _ (List.mem_of_find?_eq_some hci)
          rw [hname] at hP
          have ⟨ci', hc', _, tty⟩ := henv.lookup hP
          rw [hc'] at hc0
          cases hc0
          have t1 := tty.instLevels hus hl
          have t2 := TrS.weak_nil hord hloc hΓ (t1 : TrS venv Us [] _ _)
          exact ⟨_, t2, .const hc' (.of_mapM_ofLevel hus)
            ((List.mapM_eq_some.1 hus).length_eq.symm.trans hlen)⟩
        · simp [throw, throwThe, MonadExceptOf.throw] at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
    | app hg ha tg ta =>
      simp only [Pure.inferType] at h
      obtain ⟨Tg, h1, h⟩ := Except.ok_of_bind h
      obtain ⟨W, h2, h⟩ := Except.ok_of_bind h
      split at h
      · cases h
        have ⟨Tg', tTg, hgT⟩ := ih hΓ tg h1
        have ⟨_, hTg⟩ := hgT.isType hord hctx
        have ⟨W', tW, dW⟩ := Pure.whnf_sound henv hsub hloc hΓ tTg hTg h2
        cases tW with
        | forallE _ _ _ tB =>
          have hg' := dW.defeq hgT
          have ⟨⟨_, dA⟩, _⟩ := (hg.uniqU hwf hctx hg').forallE_inv hwf hctx
          have ha' := dA.defeq ha
          exact ⟨_, tB.inst hord ha' ta, hg'.app ha'⟩
      · simp [throw, throwThe, MonadExceptOf.throw] at h
    | lam hty tty tb =>
      simp only [Pure.inferType] at h
      obtain ⟨B, h1, h⟩ := Except.ok_of_bind h
      cases h
      have hΓ' := OracleCtx.cons hΓ tty hty
      have ⟨B', tB, hbB⟩ := ih hΓ' tb h1
      have ⟨_, hu⟩ := hty
      exact ⟨_, .forallE hty (hbB.isType hord (hΓ'.wf h₀).1.toCtx) tty tB, hu.lam hbB⟩
    | forallE hty _ tty tb =>
      simp only [Pure.inferType] at h
      obtain ⟨Tt, h1, h⟩ := Except.ok_of_bind h
      obtain ⟨w1, h2, h⟩ := Except.ok_of_bind h
      split at h
      · obtain ⟨Tb, h3, h⟩ := Except.ok_of_bind h
        obtain ⟨w2, h4, h⟩ := Except.ok_of_bind h
        split at h
        · cases h
          have hΓ' := OracleCtx.cons hΓ tty hty
          have ⟨Tt', tTt, htT⟩ := ih hΓ tty h1
          have ⟨_, hTt⟩ := htT.isType hord hctx
          have ⟨_, tW1, dW1⟩ := Pure.whnf_sound henv hsub hloc hΓ tTt hTt h2
          have ⟨Tb', tTb, hbT⟩ := ih hΓ' tb h3
          have ⟨_, hTb⟩ := hbT.isType hord (hΓ'.wf h₀).1.toCtx
          have ⟨_, tW2, dW2⟩ := Pure.whnf_sound henv hsub hloc hΓ' tTb hTb h4
          cases tW1 with
          | sort hu =>
            cases tW2 with
            | sort hv =>
              exact ⟨_, .sort (by simp [VLevel.ofLevel, hu, hv]),
                (dW1.defeq htT).forallE (dW2.defeq hbT)⟩
        · simp [throw, throwThe, MonadExceptOf.throw] at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
    | letE _ _ tv tb =>
      simp only [Pure.inferType] at h
      exact ih hΓ (tb.inst_let hord tv) h
    | mdata te =>
      simp only [Pure.inferType] at h
      exact ih hΓ te h

end

end EraseProof
