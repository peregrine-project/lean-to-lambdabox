import LeanToLambdaBox.Erases
import Lean4Lean.Verify.Typing.Lemmas
import LeanToLambdaBox.Abstract

/-!
# de Bruijn transport for `Erases`

The three moves that relate an `Erases` derivation at one `VLCtx` to one at a context
obtained by de Bruijn surgery, mirroring lean4lean's `TrExprS.weakBV`, `TrExprS.instN` and
`TrExprS.abstract`:

* `erases_shift` — weakening by bvar entries (`Expr.liftLooseBVars'` / `LBTerm.shift`);
* `erases_subst` — instantiation of a bvar entry (`Expr.instantiate1'` / `LBTerm.subst`);
* `erases_subst_let` — the same at a `.vlet` entry (`VLCtx.InstLet`), with
  `Erases.defeqDFC_wt` for the defeq swap of the entry's recorded value;
* `Erases.abstract` and `Erases.uninstantiateN` — closing a free variable back into a de
  Bruijn binder (`Expr.abstract1` / `toBvar`).

`Expr.abstract1` shifts loose bvars at or above the insertion level; `toBvar` does not. The
two agree only on terms with no such loose bvar, which is why `Erases.abstract` carries a
`Closed` premise.

The last two sections transport `Erases` along a **level instantiation**: the source and the
`VLCtx` are instantiated and the λ□ target is unchanged, since λ□ carries no levels. It is
strict — an equation, not lean4lean's `≈` — on `max`-free levels, which is what
`NoMaxLevels` names. `Erases.instL` is the positional form, at a substitution of the scope
the derivation is read at; `Erases.substParams_of_trExprS` is the by-name form the δ arm
meets, where the substitution is arbitrary and what confines it is a translation of the
instantiated term — `erases_subst_instance`'s typing premise
(`../metarocq/erasure/theories/ErasureProperties.v:383`).
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-! ## Weakening by bvar entries -/

/--
Erasure commutes with de Bruijn weakening: lifting the source by `Expr.liftLooseBVars'`
matches lifting the target by `LBTerm.shift`, under a `VLCtx.BVLift`.

`box`/`lam`/`letE` reuse `TrExprS.weakBV` and `Erasable.weakN`; `bvar`/`fvar` re-establish
their lookup premise with `VLCtx.BVLift.find?`, whose `VLCtx.liftVar` is the index
convention both sides already use.
-/
theorem erases_shift {env : VEnv} (henv : env.Ordered) {Us : List Name}
    {Δ Δ' : VLCtx} {dn dk n k : Nat}
    (W : VLCtx.BVLift Δ Δ' dn dk n k)
    {e : Expr} {t : LBTerm} (h : Erases env Us Δ e t) :
    Erases env Us Δ' (e.liftLooseBVars' dk dn) (LBTerm.shift dn dk t) := by
  induction h generalizing Δ' dk k with
  | box htr her => exact .box (htr.weakBV henv W) (her.weakN henv W.toCtx)
  | lit hcl _ ih =>
    refine .lit hcl (Expr.liftLooseBVars_eq_self ?_ ▸ ih W :)
    exact Closed.toConstructor.looseBVarRange_le
  | @bvar _ i _ _ hf =>
    have hfind := W.find? hf
    simp only [Expr.liftLooseBVars', LBTerm.shift]
    by_cases hlt : i < dk
    · rw [if_pos hlt, if_neg (by omega : ¬ i ≥ dk)]
      exact .bvar (by simpa [VLCtx.liftVar, hlt] using hfind)
    · rw [if_neg hlt, if_pos (by omega : i ≥ dk)]
      exact .bvar (by simpa [VLCtx.liftVar, hlt] using hfind)
  | fvar hf => exact .fvar (by simpa [VLCtx.liftVar] using W.find? hf)
  | ctor hc hi => exact .ctor hc hi
  | const hc ho => exact .const hc ho
  | app _ _ ihf iha => exact .app (ihf W) (iha W)
  | lam hty _ ihb => exact .lam (hty.weakBV henv W) (ihb (W.cons _))
  | letE hty hval _ _ ihv ihb =>
    exact .letE (hty.weakBV henv W) (hval.weakBV henv W) (ihv W) (ihb (W.cons _))
  | proj hs hinf hi _ ihd => exact .proj hs hinf hi (ihd W)
  | mdata _ ih => exact .mdata (ih W)

/-! ## Instantiation of a bvar entry -/

/-- A `VLCtx.InstN` witness yields the de Bruijn weakening of the substitutee's context
`Δ₀` into the instantiated context `Δ`, which gained `dk` binders. It lifts the
substitutee's erasure in the `bvar i = dk` case of `erases_subst`. -/
theorem instN_toBVLift {Δ₀ Δ₁ Δ : VLCtx} {e₀' A₀ : VExpr} {dk k : Nat}
    (W : VLCtx.InstN Δ₀ e₀' A₀ dk k Δ₁ Δ) : VLCtx.BVLift Δ₀ Δ dk 0 k 0 := by
  induction W with
  | zero => exact .refl
  | @succ _ k _ _ d _ ih => cases d <;> exact ih.skip _

/-- A bvar below the instantiated one keeps its index and stays bound. Only existence is
claimed, which is all `Erases.bvar` asks for. -/
theorem instN_find?_lt {Δ₀ Δ₁ Δ : VLCtx} {e₀' A₀ : VExpr} {dk k : Nat}
    (W : VLCtx.InstN Δ₀ e₀' A₀ dk k Δ₁ Δ) :
    ∀ {i : Nat}, i < dk → (∃ p, Δ₁.find? (.inl i) = some p) →
      ∃ p, Δ.find? (.inl i) = some p := by
  induction W with
  | zero => intro i h; omega
  | @succ dk k Γ Γ' d _ ih =>
    rintro (_ | i) hlt ⟨p, H⟩
    · exact ⟨_, rfl⟩
    · simp only [VLCtx.find?, VLCtx.next, Option.bind_eq_bind] at H
      have hsome : ∃ p, Γ.find? (.inl i) = some p := by
        cases hf : Γ.find? (.inl i) with
        | none => rw [hf] at H; simp at H
        | some q => exact ⟨q, rfl⟩
      obtain ⟨⟨qe, qA⟩, h₂⟩ := ih (by omega) hsome
      exact ⟨(qe.liftN (d.inst e₀' k).depth, qA.liftN (d.inst e₀' k).depth),
        by simp [VLCtx.find?, VLCtx.next, h₂]⟩

/-- A bvar above the instantiated one drops by one and stays bound: the entry it pointed
past is the one instantiation removes. -/
theorem instN_find?_gt {Δ₀ Δ₁ Δ : VLCtx} {e₀' A₀ : VExpr} {dk k : Nat}
    (W : VLCtx.InstN Δ₀ e₀' A₀ dk k Δ₁ Δ) :
    ∀ {i : Nat}, dk < i → (∃ p, Δ₁.find? (.inl i) = some p) →
      ∃ p, Δ.find? (.inl (i - 1)) = some p := by
  induction W with
  | zero =>
    rintro (_ | i) hgt ⟨p, H⟩
    · omega
    · simp only [VLCtx.find?, VLCtx.next, Option.bind_eq_bind] at H
      cases hf : Δ₀.find? (.inl i) with
      | none => rw [hf] at H; simp at H
      | some q => exact ⟨q, hf⟩
  | @succ dk k Γ Γ' d _ ih =>
    rintro (_ | i) hgt ⟨p, H⟩
    · omega
    · simp only [VLCtx.find?, VLCtx.next, Option.bind_eq_bind] at H
      have hsome : ∃ p, Γ.find? (.inl i) = some p := by
        cases hf : Γ.find? (.inl i) with
        | none => rw [hf] at H; simp at H
        | some q => exact ⟨q, rfl⟩
      obtain ⟨⟨qe, qA⟩, h₂⟩ := ih (by omega) hsome
      obtain _ | m := i
      · omega
      · simp only [Nat.add_sub_cancel] at h₂ ⊢
        exact ⟨(qe.liftN (d.inst e₀' k).depth, qA.liftN (d.inst e₀' k).depth),
          by simp [VLCtx.find?, VLCtx.next, h₂]⟩

/-- A free variable's lookup survives instantiation of a bvar entry: `VLCtx.InstN` touches
no fvar-tagged entry. -/
theorem instN_find?_fvar {Δ₀ Δ₁ Δ : VLCtx} {e₀' A₀ : VExpr} {dk k : Nat}
    (W : VLCtx.InstN Δ₀ e₀' A₀ dk k Δ₁ Δ) :
    ∀ {x : FVarId}, (∃ p, Δ₁.find? (.inr x) = some p) →
      ∃ p, Δ.find? (.inr x) = some p := by
  induction W with
  | zero =>
    rintro x ⟨p, H⟩
    simp only [VLCtx.find?, VLCtx.next, Option.bind_eq_bind] at H
    cases hf : Δ₀.find? (.inr x) with
    | none => rw [hf] at H; simp at H
    | some q => exact ⟨q, rfl⟩
  | @succ dk k Γ Γ' d _ ih =>
    rintro x ⟨p, H⟩
    simp only [VLCtx.find?, VLCtx.next, Option.bind_eq_bind] at H
    have hsome : ∃ p, Γ.find? (.inr x) = some p := by
      cases hf : Γ.find? (.inr x) with
      | none => rw [hf] at H; simp at H
      | some q => exact ⟨q, rfl⟩
    obtain ⟨⟨qe, qA⟩, h₂⟩ := ih hsome
    exact ⟨(qe.liftN (d.inst e₀' k).depth, qA.liftN (d.inst e₀' k).depth),
      by simp [VLCtx.find?, VLCtx.next, h₂]⟩

/--
Erasure commutes with substitution: source `Expr.instantiate1'` matches target
`LBTerm.subst` under a `VLCtx.InstN`.

`box`/`lam`/`letE` discharge their lean4lean premises with `TrExprS.instN` and
`Erasable.inst`; the `bvar i = dk` case is the substitutee's own derivation, lifted by
`erases_shift` along `instN_toBVLift`.
-/
theorem erases_subst {env : VEnv} (henv : env.Ordered) {Us : List Name}
    {Δ₀ : VLCtx} {e₀ : Expr} {e₀' A₀ : VExpr} {s' : LBTerm}
    (ht₀ : TrExprS env Us Δ₀ e₀ e₀')
    (t₀ : env.HasType Us.length Δ₀.toCtx e₀' A₀)
    (h₀ : Erases env Us Δ₀ e₀ s')
    {Δ₁ Δ : VLCtx} {dk k : Nat} (W : VLCtx.InstN Δ₀ e₀' A₀ dk k Δ₁ Δ)
    {e : Expr} {t : LBTerm} (h : Erases env Us Δ₁ e t) :
    Erases env Us Δ (e.instantiate1' e₀ dk) (LBTerm.subst s' dk t) := by
  induction h generalizing Δ dk k with
  | box htr her => exact .box (TrExprS.instN henv ht₀ t₀ W htr) (her.inst henv W.toCtx t₀)
  | lit hcl _ ih =>
    refine .lit hcl (Expr.instantiate1'_eq_self ?_ ▸ ih W :)
    exact Closed.toConstructor.looseBVarRange_le
  | @bvar _ i _ _ hf =>
    simp only [Expr.instantiate1', LBTerm.subst]
    split <;> rename_i hlt
    · obtain ⟨⟨_, _⟩, h⟩ := instN_find?_lt W hlt ⟨_, hf⟩
      exact .bvar h
    · split <;> rename_i heq
      · exact heq ▸ erases_shift henv (instN_toBVLift W) h₀
      · obtain ⟨⟨_, _⟩, h⟩ := instN_find?_gt W (by omega) ⟨_, hf⟩
        exact .bvar h
  | fvar hf => obtain ⟨⟨_, _⟩, h⟩ := instN_find?_fvar W ⟨_, hf⟩; exact .fvar h
  | ctor hc hi => exact .ctor hc hi
  | const hc ho => exact .const hc ho
  | app _ _ ihf iha => exact .app (ihf W) (iha W)
  | lam hty _ ihb =>
    exact .lam (TrExprS.instN henv ht₀ t₀ W hty) (ihb (W.succ (d := .vlam _)))
  | letE hty hval _ _ ihv ihb =>
    exact .letE (TrExprS.instN henv ht₀ t₀ W hty) (TrExprS.instN henv ht₀ t₀ W hval)
      (ihv W) (ihb (W.succ (d := .vlet ..)))
  | proj hs hinf hi _ ihd => exact .proj hs hinf hi (ihd W)
  | mdata _ ih => exact .mdata (ih W)

/-! ## Instantiation of a let entry, and transport along a definitionally equal context

Two further moves on a `.vlet` entry, which `erases_subst`'s `VLCtx.InstN` does not reach:
swapping the entry's recorded value for a definitionally equal one, and instantiating the
entry away. The second is `erases_subst` with `VLCtx.InstLet` in place of `VLCtx.InstN`, so
the four lookup helpers below mirror the `instN_*` ones exactly. -/

/--
Erasure transports along a definitionally equal context, given a translation of the source
term in the source context.

The `box` arm moves its witnesses with `TrExprS.defeqDFC'`, `Erasable.defeqDFC` and
`Erasable.defeq`; the binder arms need a `VLocalDecl.IsDefEq` for the entry they cons, which
is typed at a sort and so needs the binder type's `IsType` — data `Erases.lam` does not
carry and the translation does.
-/
theorem Erases.defeqDFC_wt {env : VEnv} (henv : env.WF) {Us : List Name} :
    ∀ {Δ₁ : VLCtx} {e : Expr} {t : LBTerm}, Erases env Us Δ₁ e t →
      ∀ {Δ₂ : VLCtx}, VLCtx.IsDefEq env Us.length Δ₁ Δ₂ → VLCtx.WF env Us.length Δ₁ →
        ∀ {ve : VExpr}, TrExprS env Us Δ₁ e ve → Erases env Us Δ₂ e t := by
  intro Δ₁ e t her
  induction her with
  | box htrb herb =>
      intro Δ₂ hΔ hWF ve htr
      obtain ⟨w, htrw, hdw⟩ := TrExprS.defeqDFC' henv hΔ htrb
      have her₂ : Erasable env Us.length Δ₂.toCtx _ :=
        Erasable.defeqDFC henv.ordered hΔ.defeqCtx herb
      exact .box htrw (Erasable.defeq henv (hΔ.symm henv).wf.toCtx (VEnv.IsDefEqU.symm hdw) her₂)
  | bvar hf =>
      intro Δ₂ hΔ hWF ve htr
      obtain ⟨_, _, h₂⟩ := hΔ.find?_defeqDFC hf
      exact .bvar h₂
  | fvar hf =>
      intro Δ₂ hΔ hWF ve htr
      obtain ⟨_, _, h₂⟩ := hΔ.find?_defeqDFC hf
      exact .fvar h₂
  | ctor hc hi => intro Δ₂ hΔ hWF ve htr; exact .ctor hc hi
  | const hc ho => intro Δ₂ hΔ hWF ve htr; exact .const hc ho
  | app _ _ ihf iha =>
      intro Δ₂ hΔ hWF ve htr
      cases htr with
      | app _ _ s1 s2 => exact .app (ihf hΔ hWF s1) (iha hΔ hWF s2)
  | lam hty hb ihb =>
      intro Δ₂ hΔ hWF ve htr
      cases htr with
      | lam h1 s1 s2 =>
          have hΓ₁ := hWF.toCtx
          obtain ⟨u, h1'⟩ := h1
          have hdty := VEnv.IsDefEqU.of_l henv hΓ₁
            (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hWF) s1 hty) h1'
          have hWF' : VLCtx.WF env Us.length ((none, .vlam _) :: _) :=
            ⟨hWF, nofun, ⟨u, hdty.hasType.2⟩⟩
          obtain ⟨bv', s2'⟩ :=
            s2.defeqDFC henv
              (VLCtx.IsDefEq.cons (.refl henv.ordered hWF) (ofv := none) nofun (.vlam hdty))
          obtain ⟨ty₂, htrty₂, _⟩ := TrExprS.defeqDFC' henv hΔ hty
          have hdty₂ := VEnv.IsDefEqU.of_l henv hΓ₁
            (TrExprS.uniq henv hΔ hty htrty₂) hdty.hasType.2
          exact .lam htrty₂ (ihb (hΔ.cons nofun (.vlam hdty₂)) hWF' s2')
  | letE hty hval hv hb ihv ihb =>
      intro Δ₂ hΔ hWF ve htr
      cases htr with
      | letE h1 s1 s2 s3 =>
          have hΓ₁ := hWF.toCtx
          obtain ⟨u, h0⟩ := h1.isType henv hΓ₁
          have hdty := VEnv.IsDefEqU.of_l henv hΓ₁
            (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hWF) s1 hty) h0
          have hdval := VEnv.IsDefEqU.of_l henv hΓ₁
            (TrExprS.uniq henv (VLCtx.IsDefEq.refl henv.ordered hWF) s2 hval) h1
          have hvalT := (hdval.hasType.2).defeqU_r henv hΓ₁ ⟨_, hdty⟩
          have hWF' : VLCtx.WF env Us.length ((none, .vlet _ _) :: _) := ⟨hWF, nofun, hvalT⟩
          obtain ⟨bv', s3'⟩ :=
            s3.defeqDFC henv
              (VLCtx.IsDefEq.cons (.refl henv.ordered hWF) (ofv := none) nofun
                (.vlet hdval hdty))
          obtain ⟨ty₂, htrty₂, _⟩ := TrExprS.defeqDFC' henv hΔ hty
          obtain ⟨val₂, htrval₂, _⟩ := TrExprS.defeqDFC' henv hΔ hval
          have hdty₂ := VEnv.IsDefEqU.of_l henv hΓ₁
            (TrExprS.uniq henv hΔ hty htrty₂) hdty.hasType.2
          have hdval₂ := VEnv.IsDefEqU.of_l henv hΓ₁
            (TrExprS.uniq henv hΔ hval htrval₂) hvalT
          exact .letE htrty₂ htrval₂ (ihv hΔ hWF hval)
            (ihb (hΔ.cons nofun (.vlet hdval₂ hdty₂)) hWF' s3')
  | proj hs hinf hi _ ihd =>
      intro Δ₂ hΔ hWF ve htr
      cases htr with
      | proj s1 _ => exact .proj hs hinf hi (ihd hΔ hWF s1)
  | lit hcl _ ih =>
      intro Δ₂ hΔ hWF ve htr
      cases htr with
      | lit _ s1 => exact .lit hcl (ih hΔ hWF s1)
  | mdata _ ih =>
      intro Δ₂ hΔ hWF ve htr
      cases htr with
      | mdata s1 => exact .mdata (ih hΔ hWF s1)

/-- A `VLCtx.InstLet` witness yields the de Bruijn weakening of the substitutee's context
`Δ₀` into the context the let entry is removed from, which carries `dk` binders above it. -/
theorem instLet_toBVLift {Δ₀ Δ₁ Δ : VLCtx} {e₀' A₀ : VExpr} {dk k : Nat}
    (W : VLCtx.InstLet Δ₀ e₀' A₀ dk k Δ₁ Δ) : VLCtx.BVLift Δ₀ Δ dk 0 k 0 := by
  induction W with
  | zero => exact .refl
  | succ _ ih => exact ih.skip _

/-- A bvar below the let keeps its index and stays bound. Only existence is claimed, which
is all `Erases.bvar` asks for. -/
theorem instLet_find?_lt {Δ₀ Δ₁ Δ : VLCtx} {e₀' A₀ : VExpr} {dk k : Nat}
    (W : VLCtx.InstLet Δ₀ e₀' A₀ dk k Δ₁ Δ) :
    ∀ {i : Nat}, i < dk → (∃ p, Δ₁.find? (.inl i) = some p) →
      ∃ p, Δ.find? (.inl i) = some p := by
  induction W with
  | zero => intro i h; omega
  | @succ dk k Γ Γ' d _ ih =>
    rintro (_ | i) hlt ⟨p, H⟩
    · exact ⟨_, rfl⟩
    · simp only [VLCtx.find?, VLCtx.next, Option.bind_eq_bind] at H
      have hsome : ∃ p, Γ.find? (.inl i) = some p := by
        cases hf : Γ.find? (.inl i) with
        | none => rw [hf] at H; simp at H
        | some q => exact ⟨q, rfl⟩
      obtain ⟨⟨qe, qA⟩, h₂⟩ := ih (by omega) hsome
      exact ⟨(qe.liftN d.depth, qA.liftN d.depth), by simp [VLCtx.find?, VLCtx.next, h₂]⟩

/-- A bvar above the let drops by one and stays bound: the entry it pointed past is the one
instantiation removes. -/
theorem instLet_find?_gt {Δ₀ Δ₁ Δ : VLCtx} {e₀' A₀ : VExpr} {dk k : Nat}
    (W : VLCtx.InstLet Δ₀ e₀' A₀ dk k Δ₁ Δ) :
    ∀ {i : Nat}, dk < i → (∃ p, Δ₁.find? (.inl i) = some p) →
      ∃ p, Δ.find? (.inl (i - 1)) = some p := by
  induction W with
  | zero =>
    rintro (_ | i) hgt ⟨p, H⟩
    · omega
    · simp only [VLCtx.find?, VLCtx.next, Option.bind_eq_bind] at H
      cases hf : Δ₀.find? (.inl i) with
      | none => rw [hf] at H; simp at H
      | some q => exact ⟨q, hf⟩
  | @succ dk k Γ Γ' d _ ih =>
    rintro (_ | i) hgt ⟨p, H⟩
    · omega
    · simp only [VLCtx.find?, VLCtx.next, Option.bind_eq_bind] at H
      have hsome : ∃ p, Γ.find? (.inl i) = some p := by
        cases hf : Γ.find? (.inl i) with
        | none => rw [hf] at H; simp at H
        | some q => exact ⟨q, rfl⟩
      obtain ⟨⟨qe, qA⟩, h₂⟩ := ih (by omega) hsome
      obtain _ | m := i
      · omega
      · simp only [Nat.add_sub_cancel] at h₂ ⊢
        exact ⟨(qe.liftN d.depth, qA.liftN d.depth), by simp [VLCtx.find?, VLCtx.next, h₂]⟩

/-- A free variable's lookup survives instantiation of a let entry: `VLCtx.InstLet` touches
no fvar-tagged entry. -/
theorem instLet_find?_fvar {Δ₀ Δ₁ Δ : VLCtx} {e₀' A₀ : VExpr} {dk k : Nat}
    (W : VLCtx.InstLet Δ₀ e₀' A₀ dk k Δ₁ Δ) :
    ∀ {x : FVarId}, (∃ p, Δ₁.find? (.inr x) = some p) →
      ∃ p, Δ.find? (.inr x) = some p := by
  induction W with
  | zero =>
    rintro x ⟨p, H⟩
    simp only [VLCtx.find?, VLCtx.next, Option.bind_eq_bind] at H
    cases hf : Δ₀.find? (.inr x) with
    | none => rw [hf] at H; simp at H
    | some q => exact ⟨q, rfl⟩
  | @succ dk k Γ Γ' d _ ih =>
    rintro x ⟨p, H⟩
    simp only [VLCtx.find?, VLCtx.next, Option.bind_eq_bind] at H
    have hsome : ∃ p, Γ.find? (.inr x) = some p := by
      cases hf : Γ.find? (.inr x) with
      | none => rw [hf] at H; simp at H
      | some q => exact ⟨q, rfl⟩
    obtain ⟨⟨qe, qA⟩, h₂⟩ := ih hsome
    exact ⟨(qe.liftN d.depth, qA.liftN d.depth), by simp [VLCtx.find?, VLCtx.next, h₂]⟩

/--
Erasure commutes with instantiating a `.vlet` entry away: source `Expr.instantiate1'` matches
target `LBTerm.subst` under a `VLCtx.InstLet`, when the substitutee's translation is the
entry's recorded value.

`box`, `lam` and `letE` discharge their lean4lean premises with `TrExprS.instN_let`; the
`Erasable` witness needs no move at all, since a `.vlet` entry contributes nothing to the
pure typing context. The `bvar i = dk` case is the substitutee's own derivation, lifted by
`erases_shift` along `instLet_toBVLift`.
-/
theorem erases_subst_let {env : VEnv} (henv : env.Ordered) {Us : List Name}
    {Δ₀ : VLCtx} {e₀ : Expr} {e₀' A₀ : VExpr} {s' : LBTerm}
    (ht₀ : TrExprS env Us Δ₀ e₀ e₀')
    (h₀ : Erases env Us Δ₀ e₀ s')
    {Δ₁ Δ : VLCtx} {dk k : Nat} (W : VLCtx.InstLet Δ₀ e₀' A₀ dk k Δ₁ Δ)
    {e : Expr} {t : LBTerm} (h : Erases env Us Δ₁ e t) :
    Erases env Us Δ (e.instantiate1' e₀ dk) (LBTerm.subst s' dk t) := by
  induction h generalizing Δ dk k with
  | box htr her => exact .box (TrExprS.instN_let henv ht₀ W htr) (W.toCtx ▸ her)
  | lit hcl _ ih =>
    refine .lit hcl (Expr.instantiate1'_eq_self ?_ ▸ ih W :)
    exact Closed.toConstructor.looseBVarRange_le
  | @bvar _ i _ _ hf =>
    simp only [Expr.instantiate1', LBTerm.subst]
    split <;> rename_i hlt
    · obtain ⟨⟨_, _⟩, h⟩ := instLet_find?_lt W hlt ⟨_, hf⟩
      exact .bvar h
    · split <;> rename_i heq
      · exact heq ▸ erases_shift henv (instLet_toBVLift W) h₀
      · obtain ⟨⟨_, _⟩, h⟩ := instLet_find?_gt W (by omega) ⟨_, hf⟩
        exact .bvar h
  | fvar hf => obtain ⟨⟨_, _⟩, h⟩ := instLet_find?_fvar W ⟨_, hf⟩; exact .fvar h
  | ctor hc hi => exact .ctor hc hi
  | const hc ho => exact .const hc ho
  | app _ _ ihf iha => exact .app (ihf W) (iha W)
  | lam hty _ ihb =>
    exact .lam (TrExprS.instN_let henv ht₀ W hty) (ihb (W.succ (d := .vlam _)))
  | letE hty hval _ _ ihv ihb =>
    exact .letE (TrExprS.instN_let henv ht₀ W hty) (TrExprS.instN_let henv ht₀ W hval)
      (ihv W) (ihb (W.succ (d := .vlet ..)))
  | proj hs hinf hi _ ihd => exact .proj hs hinf hi (ihd W)
  | mdata _ ih => exact .mdata (ih W)

/-! ## Closing a free variable -/

/-- `BEq` on `FVarId` is symmetric. `Expr.abstract1` tests `v₀ == y` while `toBvar` tests
`y == v₀`, and core ships no `LawfulBEq FVarId`. -/
theorem fvarId_beq_comm (x y : FVarId) : (x == y) = (y == x) := by
  cases hxy : (x == y) <;> cases hyx : (y == x) <;> try rfl
  · exact absurd (fvarId_beq_iff_eq.mpr (fvarId_beq_iff_eq.mp hyx).symm) (by simp [hxy])
  · exact absurd (fvarId_beq_iff_eq.mpr (fvarId_beq_iff_eq.mp hxy).symm) (by simp [hyx])

/-- Opening a binder body with a free variable eats one level of closedness. It turns the
closedness of the un-instantiated body — the form `Erases.uninstantiateN` receives — into
the premise `Erases.abstract` needs. -/
theorem closed_instantiate1'_fvar {v₀ : FVarId} {e : Expr} {k : Nat}
    (h : Closed e (k + 1)) : Closed (Expr.instantiate1' e (.fvar v₀) k) k := by
  induction e generalizing k with simp_all [Expr.instantiate1', Closed]
  | bvar i =>
    split
    · exact ‹i < k›
    · split
      · exact True.intro
      · exfalso; omega

/-- The abstracted context binds the index the closed-over variable becomes: after
`VLCtx.Abstract` the entry at `dk` is a de Bruijn binder. -/
theorem abstract_find?_dk {Δ₀ Δ₁ Δ : VLCtx} {v₀ : FVarId} {d₀ : VLocalDecl} {dk k : Nat}
    (W : VLCtx.Abstract Δ₀ v₀ d₀ dk k Δ₁ Δ) :
    ∃ e' A, Δ.find? (.inl dk) = some (e', A) := by
  induction W with
  | zero => exact ⟨_, _, rfl⟩
  | @succ dk k Γ Γ' d _ ih =>
    obtain ⟨e', A, h⟩ := ih
    exact ⟨e'.liftN d.depth, A.liftN d.depth, by simp [VLCtx.find?, VLCtx.next, h]⟩

/--
Erasure commutes with fvar→de-Bruijn closing: if `e` erases to `t` in a context whose entry
`dk` is the fvar `v₀`, and `e` has no loose bvar at or above `dk`, then closing both sides
over `v₀` at level `dk` preserves erasure, in the context with that entry flipped to a de
Bruijn binder.

`box` transports its witnesses via `TrExprS.abstract` and `VLCtx.Abstract.toCtx`; `bvar` and
the `y ≠ v₀` half of `fvar` re-read their lookup through `VLCtx.Abstract.find?`, and the
`y = v₀` half through `abstract_find?_dk`.
-/
theorem Erases.abstract {env : VEnv} {Us : List Name}
    {Δ₀ : VLCtx} {v₀ : FVarId} {d₀ : VLocalDecl} {dk k : Nat} {Δ₁ Δ : VLCtx}
    (W : VLCtx.Abstract Δ₀ v₀ d₀ dk k Δ₁ Δ)
    {e : Expr} {t : LBTerm} (hc : Closed e dk) (H : Erases env Us Δ₁ e t) :
    Erases env Us Δ (e.abstract1 v₀ dk) (toBvar v₀ dk t) := by
  induction H generalizing Δ dk k with
  | box htr her => exact .box (htr.abstract W) (W.toCtx ▸ her)
  | lit hcl _ ih =>
    exact .lit hcl
      (FVarsIn.toConstructor.abstract_eq_self Closed.toConstructor ▸ ih W Closed.toConstructor)
  | @bvar _ i _ _ hf =>
    have hi : i < dk := hc
    simp only [Expr.abstract1, if_pos hi, toBvar]
    exact .bvar (by rw [W.find? (v := .inl i) nofun]; simpa [hi] using hf)
  | @fvar _ y _ _ hf =>
    simp only [Expr.abstract1, toBvar, fvarId_beq_comm v₀ y]
    cases hyx : (y == v₀)
    · simp only [Bool.false_eq_true, if_false]
      have hne : (Sum.inr y : Nat ⊕ FVarId) ≠ .inr v₀ := fun h =>
        absurd (fvarId_beq_iff_eq.mpr (Sum.inr.inj h)) (by simp [hyx])
      exact .fvar (by rw [W.find? hne]; exact hf)
    · simp only [if_true]
      obtain ⟨_, _, h⟩ := abstract_find?_dk W
      exact .bvar h
  | ctor hc' hi => exact .ctor hc' hi
  | const hc' ho => exact .const hc' ho
  | app _ _ ihf iha => exact .app (ihf W hc.1) (iha W hc.2)
  | lam hty _ ihb => exact .lam (hty.abstract W) (ihb W.succ hc.2)
  | letE hty hval _ _ ihv ihb =>
    exact .letE (hty.abstract W) (hval.abstract W) (ihv W hc.2.1) (ihb W.succ hc.2.2)
  | proj hs hinf hi _ ihd => exact .proj hs hinf hi (ihd W hc)
  | mdata _ ih => exact .mdata (ih W hc)

/-- If the body opened with a fresh `v₀` erases to `t`, then the un-opened body erases to
`toBvar v₀ dk t`, in the context with the fvar entry flipped to a de Bruijn one. `sc` is
`v₀`'s freshness for `e`, and `hc` allows exactly the one loose bvar being re-bound. -/
theorem Erases.uninstantiateN {env : VEnv} {Us : List Name}
    {Δ₀ : VLCtx} {v₀ : FVarId} {d₀ : VLocalDecl} {dk k : Nat} {Δ₁ Δ : VLCtx}
    (W : VLCtx.Abstract Δ₀ v₀ d₀ dk k Δ₁ Δ)
    {e : Expr} {t : LBTerm}
    (H : Erases env Us Δ₁ (Expr.instantiate1' e (.fvar v₀) dk) t)
    (sc : FVarsIn (· ≠ v₀) e) (hc : Closed e (dk + 1)) :
    Erases env Us Δ e (toBvar v₀ dk t) := by
  have h := Erases.abstract W (closed_instantiate1'_fvar hc) H
  rwa [sc.abstract_instantiate1] at h

/-- The `dk = 0` corollary: open a binder body with a fresh `v₀`, erase, close with
`toBvar v₀ 0`, which is `abstract v₀`. -/
theorem Erases.uninstantiate {env : VEnv} {Us : List Name}
    {v₀ : FVarId} {deps : List FVarId} {d : VLocalDecl} {Δ : VLCtx}
    {e : Expr} {t : LBTerm}
    (H : Erases env Us ((some (v₀, deps), d) :: Δ) (e.instantiate1' (.fvar v₀)) t)
    (sc : FVarsIn (· ≠ v₀) e) (hc : Closed e 1) :
    Erases env Us ((none, d) :: Δ) e (toBvar v₀ 0 t) :=
  H.uninstantiateN .zero sc hc

/-- The closing really re-binds the variable: the opened body `.bvar 0 ↦ .fvar v₀` erases
back to `.bvar 0`. -/
example (env : VEnv) (Us : List Name) (Δ : VLCtx)
    (v₀ : FVarId) (deps : List FVarId) (ty : VExpr) :
    Erases env Us ((none, .vlam ty) :: Δ) (.bvar 0) (.bvar 0) := by
  have H : Erases env Us ((some (v₀, deps), .vlam ty) :: Δ)
      ((Expr.bvar 0).instantiate1' (.fvar v₀)) (.fvar v₀) :=
    .fvar (e' := (VLocalDecl.vlam ty).value) (A := (VLocalDecl.vlam ty).type)
      (by simp [VLCtx.find?, VLCtx.next])
  have h := H.uninstantiate (sc := True.intro) (hc := Nat.zero_lt_one)
  simpa [toBvar, fvarId_beq_iff_eq.mpr (rfl : v₀ = v₀)] using h

/-! ## Level instantiation

`Level.substParams'` calls Lean's normalising smart constructors `mkLevelMax'` and
`mkLevelIMax'`, so level substitution is only `≈`-loose at a `max`/`imax` node.
`NoMaxLevel` excludes exactly those nodes, and on that fragment the transport is an
equation. -/

/-- A level built from `zero`, `succ`, `param` and `mvar` alone. On these
`Level.substParams'` performs no normalisation. -/
def NoMaxLevel : Level → Prop
  | .zero => True
  | .param _ => True
  | .mvar _ => True
  | .succ u => NoMaxLevel u
  | .max _ _ => False
  | .imax _ _ => False

/-- Positional lookup through a successful `mapM (VLevel.ofLevel Us)`. -/
theorem mapM_ofLevel_getElem? {Us : List Name} {ls : List Level} {ls' : List VLevel}
    (Hls : ls.mapM (VLevel.ofLevel Us) = some ls') {n : Nat} {l : Level}
    (h : ls[n]? = some l) : ∃ v, ls'[n]? = some v ∧ VLevel.ofLevel Us l = some v := by
  rw [List.mapM_eq_some] at Hls
  induction Hls generalizing n with
  | nil => simp at h
  | cons hd _ ih =>
    cases n with
    | zero => simp at h; subst h; exact ⟨_, rfl, hd⟩
    | succ n => simpa using ih (by simpa using h)

/-- Level substitution is strict on `max`-free levels: the strict twin of upstream's
`substParams_wf`, whose conclusion is only `≈`. -/
theorem substParams_strict {Us ps : List Name} {ls : List Level} {ls' : List VLevel}
    (Hls : ls.mapM (VLevel.ofLevel Us) = some ls') (eq : ps.length = ls.length)
    {F : Name → Level}
    (eqF : (fun x => ((List.idxOf? x ps).bind fun i => ls[i]?).getD (Level.param x)) = F) :
    ∀ (red : Bool) {u : Level}, NoMaxLevel u → ∀ {u' : VLevel},
      VLevel.ofLevel ps u = some u' →
      VLevel.ofLevel Us (u.substParams' F red) = some (u'.inst ls') := by
  intro red u
  induction u generalizing red with
  | zero => intro _ u' H; simp [VLevel.ofLevel] at H; subst H; rfl
  | succ u ih =>
    intro hnm u' H
    simp [VLevel.ofLevel, bind] at H
    obtain ⟨a, ha, rfl⟩ := H
    simp [Level.substParams', VLevel.ofLevel, VLevel.inst, ih _ hnm ha]
  | max _ _ => intro hnm; exact hnm.elim
  | imax _ _ => intro hnm; exact hnm.elim
  | mvar => intro _ u' H; simp [VLevel.ofLevel] at H
  | param x =>
    intro _ u' H
    simp [VLevel.ofLevel] at H
    obtain ⟨hlt, rfl⟩ := H
    subst eqF
    have hidx : List.idxOf? x ps = some (List.idxOf x ps) := by
      have h := List.idxOf_eq_getD_idxOf? x ps
      cases hc : List.idxOf? x ps with
      | none => rw [hc] at h; simp at h; omega
      | some i => rw [hc] at h; simp at h; rw [h]
    have hlt' : List.idxOf x ps < ls.length := eq ▸ hlt
    have hget : ls[List.idxOf x ps]? = some ls[List.idxOf x ps] := by simp [hlt']
    obtain ⟨v, hv, hofl⟩ := mapM_ofLevel_getElem? Hls hget
    simp [Level.substParams', VLevel.inst, hidx, hget, hv, hofl]

/-- The spine form, for `TrExprS.const`'s level list. -/
theorem substParams_strict_list {Us ps : List Name} {ls : List Level} {ls' : List VLevel}
    (Hls : ls.mapM (VLevel.ofLevel Us) = some ls') (eq : ps.length = ls.length)
    {F : Name → Level}
    (eqF : (fun x => ((List.idxOf? x ps).bind fun i => ls[i]?).getD (Level.param x)) = F)
    (red : Bool) {us : List Level} {us' : List VLevel}
    (H : us.mapM (VLevel.ofLevel ps) = some us') :
    (∀ u ∈ us, NoMaxLevel u) →
      (us.map (Level.substParams' F red)).mapM (VLevel.ofLevel Us)
        = some (us'.map (·.inst ls')) := by
  rw [List.mapM_eq_some] at H
  rw [List.mapM_eq_some]
  induction H with
  | nil => exact fun _ => by simp
  | @cons a b l1 l2 h _ ih =>
    intro hnm
    simp only [List.map_cons]
    exact .cons (substParams_strict Hls eq eqF red (hnm a (by simp)) h)
      (ih (fun u hu => hnm u (by simp [hu])))

/-- Every level an `Expr` mentions — in its `sort` and `const` nodes — is `max`-free. -/
def NoMaxLevels : Expr → Prop
  | .sort u => NoMaxLevel u
  | .const _ us => ∀ u ∈ us, NoMaxLevel u
  | .app f a => NoMaxLevels f ∧ NoMaxLevels a
  | .lam _ t b _ => NoMaxLevels t ∧ NoMaxLevels b
  | .forallE _ t b _ => NoMaxLevels t ∧ NoMaxLevels b
  | .letE _ t v b _ => NoMaxLevels t ∧ NoMaxLevels v ∧ NoMaxLevels b
  | .mdata _ e => NoMaxLevels e
  | .proj _ _ e => NoMaxLevels e
  | .bvar _ => True
  | .fvar _ => True
  | .mvar _ => True
  | .lit _ => True

/-- A literal's constructor form mentions only `[]` and `[.zero]`, so it is in the
fragment. This is what the `lit` rules' sub-derivation needs. -/
theorem noMaxLevels_toConstructor {l : Literal} : NoMaxLevels (Literal.toConstructor l) := by
  cases l with
  | natVal n =>
    cases n <;>
      simp [Literal.toConstructor, Expr.natLitToConstructor, NoMaxLevels, Expr.natZero,
        Expr.natSucc]
  | strVal s =>
    simp only [Literal.toConstructor, Expr.strLitToConstructor]
    refine ⟨by simp [NoMaxLevels], ?_⟩
    induction s.toList <;> simp_all [NoMaxLevels, NoMaxLevel]

/--
The strict `TrExprS.instL`, in the `Expr.instantiateLevelParamsCore'` form its `Erases`
consumer meets it in.

Unlike upstream's `TrExprS.instL` — which concludes `TrExpr` — this needs neither
`VEnv.WF env` nor `VLCtx.WF`: with a strict level transport every arm is the raw `TrExprS`
constructor applied to `instL`-transported side premises.
-/
theorem TrExprS.instL_core {env : VEnv} {Us ps : List Name} {ls : List Level}
    {ls' : List VLevel} {Δ : VLCtx} {e : Expr} {e' : VExpr} {F : Name → Level}
    (Hls : ls.mapM (VLevel.ofLevel Us) = some ls') (eq : ps.length = ls.length)
    (eqF : (fun x => ((List.idxOf? x ps).bind fun i => ls[i]?).getD (Level.param x)) = F)
    (red : Bool)
    (H : TrExprS env ps Δ e e') : NoMaxLevels e →
    TrExprS env Us (Δ.instL ls') (Expr.instantiateLevelParamsCore' red F e) (e'.instL ls') := by
  have Hls' := VLevel.WF.of_mapM_ofLevel Hls
  induction H with
  | bvar h1 => exact fun _ => .bvar (VLCtx.find?_instL h1)
  | fvar h1 => exact fun _ => .fvar (VLCtx.find?_instL h1)
  | sort h1 => intro hnm; exact .sort (substParams_strict Hls eq eqF red hnm h1)
  | const h1 h2 h3 =>
    intro hnm
    exact .const h1 (substParams_strict_list Hls eq eqF red h2 hnm) (by simp [h3])
  | app h1 h2 _ _ ih1 ih2 =>
    intro hnm
    exact .app (VLCtx.instL_toCtx _ ▸ h1.instL Hls') (VLCtx.instL_toCtx _ ▸ h2.instL Hls')
      (ih1 hnm.1) (ih2 hnm.2)
  | lam h1 _ _ ih1 ih2 =>
    intro hnm
    exact .lam (VLCtx.instL_toCtx _ ▸ h1.instL Hls') (ih1 hnm.1) (ih2 hnm.2)
  | forallE h1 h2 _ _ ih1 ih2 =>
    intro hnm
    exact .forallE (VLCtx.instL_toCtx _ ▸ h1.instL Hls')
      (VLCtx.instL_toCtx _ ▸ h2.instL Hls') (ih1 hnm.1) (ih2 hnm.2)
  | letE h1 _ _ _ ih1 ih2 ih3 =>
    intro hnm
    exact .letE (VLCtx.instL_toCtx _ ▸ h1.instL Hls') (ih1 hnm.1) (ih2 hnm.2.1) (ih3 hnm.2.2)
  | lit h1 _ ih =>
    intro _
    refine .lit h1 (Expr.instantiateLevelParamsCore_eq_self ?_ ▸ ih ?_ :)
    · exact Literal.toConstructor_hasLevelParam
    · exact noMaxLevels_toConstructor
  | mdata _ ih => exact fun hnm => .mdata (ih hnm)
  | proj _ h2 ih =>
    intro hnm
    exact .proj (ih hnm) (VLCtx.instL_toCtx _ ▸ h2.instL Hls')

/-- The user-facing form, at `Expr.instantiateLevelParams`. -/
theorem TrExprS.instL_strict {env : VEnv} {Us ps : List Name} {ls : List Level}
    {ls' : List VLevel} {Δ : VLCtx} {e : Expr} {e' : VExpr}
    (Hls : ls.mapM (VLevel.ofLevel Us) = some ls') (eq : ps.length = ls.length)
    (H : TrExprS env ps Δ e e') (hnm : NoMaxLevels e) :
    TrExprS env Us (Δ.instL ls') (e.instantiateLevelParams ps ls) (e'.instL ls') := by
  rw [Expr.instantiateLevelParams_eq]
  exact TrExprS.instL_core Hls eq rfl _ H hnm

/-- `IsArityUpTo` transports along a level instantiation, its defeq witness by
`VEnv.IsDefEqU.instL` and its syntactic arity by `IsArity.instL`. -/
theorem IsArityUpTo.instL {env : VEnv} {U U' : Nat} {ls : List VLevel}
    (hls : ∀ l ∈ ls, l.WF U') {Γ : List VExpr} {A : VExpr}
    (h : IsArityUpTo env U Γ A) :
    IsArityUpTo env U' (Γ.map (VExpr.instL ls)) (A.instL ls) :=
  let ⟨A', hd, har⟩ := h
  ⟨A'.instL ls, VEnv.IsDefEqU.instL hls hd, har.instL⟩

/-- The `box` arm's obligation under instantiation: `Erasable` unfolds to a `HasType` and a
`HasType`-or-`IsArityUpTo` disjunct, and `instL` transports each. The `.sort .zero` of the
propositional disjunct is instantiation-invariant. -/
theorem Erasable.instL {env : VEnv} {U U' : Nat} {ls : List VLevel}
    (hls : ∀ l ∈ ls, l.WF U') {Γ : List VExpr} {e : VExpr}
    (h : Erasable env U Γ e) : Erasable env U' (Γ.map (VExpr.instL ls)) (e.instL ls) :=
  let ⟨A, hA, hd⟩ := h
  ⟨A.instL ls, VEnv.HasType.instL hls hA,
    hd.imp (fun h => VEnv.HasType.instL hls h) (fun h => IsArityUpTo.instL hls h)⟩

/--
Erasure transports along a level instantiation, on the `max`-free fragment.

The λ□ target is **unchanged** — λ□ carries no levels — while the source and the `VLCtx`
are instantiated. The binder arms need no composition: `TrExprS.instL_core` sends
`Erases.lam`'s witness `ty'` to `ty'.instL ls'`, which is the head of the instantiated
context the body's induction hypothesis is stated at.
-/
theorem Erases.instL_core {env : VEnv} {Us ps : List Name} {ls : List Level}
    {ls' : List VLevel} {Δ : VLCtx} {e : Expr} {t : LBTerm} {F : Name → Level}
    (Hls : ls.mapM (VLevel.ofLevel Us) = some ls') (eq : ps.length = ls.length)
    (eqF : (fun x => ((List.idxOf? x ps).bind fun i => ls[i]?).getD (Level.param x)) = F)
    (red : Bool) (H : Erases env ps Δ e t) : NoMaxLevels e →
    Erases env Us (Δ.instL ls') (Expr.instantiateLevelParamsCore' red F e) t := by
  have Hls' := VLevel.WF.of_mapM_ofLevel Hls
  induction H with
  | box htr her =>
    intro hnm
    exact .box (TrExprS.instL_core Hls eq eqF red htr hnm)
      (VLCtx.instL_toCtx _ ▸ Erasable.instL Hls' her)
  | lit hcl _ ih =>
    intro _
    exact .lit hcl (Expr.instantiateLevelParamsCore_eq_self
      Literal.toConstructor_hasLevelParam ▸ ih noMaxLevels_toConstructor :)
  | bvar hf => intro _; exact .bvar (VLCtx.find?_instL hf)
  | fvar hf => intro _; exact .fvar (VLCtx.find?_instL hf)
  | ctor hc hi => intro _; exact .ctor hc hi
  | const hc ho => intro _; exact .const hc ho
  | app _ _ ihf iha => intro hnm; exact .app (ihf hnm.1) (iha hnm.2)
  | lam hty _ ihb =>
    intro hnm; exact .lam (TrExprS.instL_core Hls eq eqF red hty hnm.1) (ihb hnm.2)
  | letE hty hval _ _ ihv ihb =>
    intro hnm
    exact .letE (TrExprS.instL_core Hls eq eqF red hty hnm.1)
      (TrExprS.instL_core Hls eq eqF red hval hnm.2.1) (ihv hnm.2.1) (ihb hnm.2.2)
  | proj hs hinf hi _ ihd => intro hnm; exact .proj hs hinf hi (ihd hnm)
  | mdata _ ih => intro hnm; exact .mdata (ih hnm)

/-- The user-facing form, at `Expr.instantiateLevelParams`. -/
theorem Erases.instL {env : VEnv} {Us ps : List Name} {ls : List Level}
    {ls' : List VLevel} {Δ : VLCtx} {e : Expr} {t : LBTerm}
    (Hls : ls.mapM (VLevel.ofLevel Us) = some ls') (eq : ps.length = ls.length)
    (H : Erases env ps Δ e t) (hnm : NoMaxLevels e) :
    Erases env Us (Δ.instL ls') (e.instantiateLevelParams ps ls) t := by
  rw [Expr.instantiateLevelParams_eq]
  exact Erases.instL_core Hls eq rfl _ H hnm

/-- A `{u}`-polymorphic λ, erased at `Us = [u]`, is an `Erases` derivation at `Us = []`
once its level parameter is instantiated at `0` — same target, no residue. -/
theorem erases_instL_closed (env : VEnv) (nm : Name) (bi : BinderInfo) :
    Erases env [] [] (.lam nm (.sort .zero) (.bvar 0) bi)
      (.lambda (.named nm.toString) (.bvar 0)) := by
  have h := Erases.instL (env := env) (Us := []) (ps := [`u]) (ls := [Level.zero])
    (ls' := [VLevel.zero]) (Δ := [])
    (e := .lam nm (.sort (.param `u)) (.bvar 0) bi)
    (t := .lambda (.named nm.toString) (.bvar 0)) rfl rfl
    (.lam (ty' := .sort (.param 0)) (.sort rfl)
      (.bvar (e' := (VLocalDecl.vlam (.sort (.param 0))).value)
        (A := (VLocalDecl.vlam (.sort (.param 0))).type) rfl))
    (⟨trivial, trivial⟩ : NoMaxLevels (.lam nm (.sort (.param `u)) (.bvar 0) bi))
  simpa [Expr.instantiateLevelParams_eq, Expr.instantiateLevelParamsCore',
    Level.substParams', VLCtx.instL] using h

/-! ## Level instantiation by name

`Expr.instantiateLevelParams` substitutes *by name*, against a parameter list that need not
be the scope a derivation was read at — `SEval.deltaC` binds it as a variable of the rule. The
positional transport above therefore does not apply on the nose, and it cannot be made to: a
name the substitution touches but the reading scope does not know has no `VLevel`.

What rules such a substitution out is a translation of the **instantiated** term, which is
`erases_subst_instance`'s `Σ ;;; Γ |- t : T` premise (`ErasureProperties.v:383`). Together
with a translation of the term at its own scope — the same premise on the uninstantiated side
— it pins the substitution on every parameter the term mentions, and the positional form
covers the rest by substituting `0` there. `Erases.const` and `Erases.ctor` leave a constant's
level arguments unconstrained, so the uninstantiated translation is what pays for them.
-/

/-- `p` occurs as a parameter of the level `l`. -/
def LevelParamIn (p : Name) : Level → Prop
  | .zero => False
  | .mvar _ => False
  | .param q => p = q
  | .succ u => LevelParamIn p u
  | .max a b => LevelParamIn p a ∨ LevelParamIn p b
  | .imax a b => LevelParamIn p a ∨ LevelParamIn p b

/-- `p` occurs as a level parameter of some `sort` or `const` node of `e`. -/
def ExprParamIn (p : Name) : Expr → Prop
  | .sort u => LevelParamIn p u
  | .const _ us => ∃ u ∈ us, LevelParamIn p u
  | .app f a => ExprParamIn p f ∨ ExprParamIn p a
  | .lam _ t b _ => ExprParamIn p t ∨ ExprParamIn p b
  | .forallE _ t b _ => ExprParamIn p t ∨ ExprParamIn p b
  | .letE _ t v b _ => ExprParamIn p t ∨ ExprParamIn p v ∨ ExprParamIn p b
  | .mdata _ e => ExprParamIn p e
  | .proj _ _ e => ExprParamIn p e
  | .bvar _ => False
  | .fvar _ => False
  | .mvar _ => False
  | .lit _ => False

/-- A level the reading scope translates mentions only that scope's parameters. -/
theorem mem_of_levelParamIn {Us : List Name} {p : Name} :
    ∀ {l : Level} {v : VLevel}, VLevel.ofLevel Us l = some v → LevelParamIn p l → p ∈ Us := by
  intro l
  induction l with
  | zero => intro _ _ h; exact h.elim
  | mvar => intro _ _ h; exact h.elim
  | param q =>
    intro v hv hp
    subst hp
    simp [VLevel.ofLevel] at hv
    exact List.idxOf_lt_length_iff.mp hv.1
  | succ u ih =>
    intro v hv hp
    simp [VLevel.ofLevel, bind] at hv
    obtain ⟨a, ha, -⟩ := hv
    exact ih ha hp
  | max a b iha ihb =>
    intro v hv hp
    simp [VLevel.ofLevel, bind] at hv
    obtain ⟨x, hx, y, hy, -⟩ := hv
    exact hp.elim (iha hx) (ihb hy)
  | imax a b iha ihb =>
    intro v hv hp
    simp [VLevel.ofLevel, bind] at hv
    obtain ⟨x, hx, y, hy, -⟩ := hv
    exact hp.elim (iha hx) (ihb hy)

/-- A term the reading scope translates mentions only that scope's level parameters. This is
what `Erases` alone does not give: its `const` and `ctor` arms drop the level arguments. -/
theorem mem_of_exprParamIn {env : VEnv} {Us : List Name} {p : Name} :
    ∀ {Δ : VLCtx} {e : Expr} {v : VExpr}, TrExprS env Us Δ e v → ExprParamIn p e → p ∈ Us := by
  intro Δ e v h
  induction h with
  | bvar => intro h; exact h.elim
  | fvar => intro h; exact h.elim
  | sort h1 => exact mem_of_levelParamIn h1
  | const _ h2 _ =>
    rintro ⟨u, hu, hp⟩
    obtain ⟨n, hn⟩ := List.getElem?_of_mem hu
    obtain ⟨v, -, hv⟩ := mapM_ofLevel_getElem? h2 hn
    exact mem_of_levelParamIn hv hp
  | app _ _ _ _ ihf iha => intro h; exact h.elim ihf iha
  | lam _ _ _ ihty ihb => intro h; exact h.elim ihty ihb
  | forallE _ _ _ _ ihty ihb => intro h; exact h.elim ihty ihb
  | letE _ _ _ _ ihty ihv ihb => intro h; exact h.elim ihty (fun h => h.elim ihv ihb)
  | lit => intro h; exact h.elim
  | mdata _ ih => exact ih
  | proj _ _ ih => exact ih

/-- The substitution's image at a mentioned parameter is known to the reading scope of the
substituted level. `max`-free because `Level.substParams'` normalises at a `max` node. -/
theorem ofLevel_subst_of_levelParamIn {Us : List Name} {F : Name → Level} {p : Name} :
    ∀ {l : Level} {red : Bool} {v : VLevel},
      VLevel.ofLevel Us (Level.substParams' F red l) = some v → NoMaxLevel l →
      LevelParamIn p l → ∃ w, VLevel.ofLevel Us (F p) = some w := by
  intro l
  induction l with
  | zero => intro _ _ _ _ h; exact h.elim
  | mvar => intro _ _ _ _ h; exact h.elim
  | param q => intro red v hv _ hp; subst hp; exact ⟨v, hv⟩
  | succ u ih =>
    intro red v hv hnm hp
    rw [Level.substParams'] at hv
    simp [VLevel.ofLevel, bind] at hv
    obtain ⟨a, ha, -⟩ := hv
    exact ih ha hnm hp
  | max a b => intro _ _ _ h; exact h.elim
  | imax a b => intro _ _ _ h; exact h.elim

/-- The same at a term: a translation of the instantiated term knows the substitution's
image at every parameter the term mentions. -/
theorem ofLevel_subst_of_exprParamIn {env : VEnv} {Us : List Name} {F : Name → Level}
    {p : Name} {red : Bool} :
    ∀ {e : Expr} {Δ : VLCtx} {v : VExpr},
      TrExprS env Us Δ (Expr.instantiateLevelParamsCore' red F e) v → NoMaxLevels e →
      ExprParamIn p e → ∃ w, VLevel.ofLevel Us (F p) = some w := by
  intro e
  induction e with
  | bvar => intro _ _ _ _ h; exact h.elim
  | fvar => intro _ _ _ _ h; exact h.elim
  | mvar => intro _ _ _ _ h; exact h.elim
  | lit => intro _ _ _ _ h; exact h.elim
  | sort u =>
    intro Δ v htr hnm hp
    rw [Expr.instantiateLevelParamsCore'] at htr
    cases htr with | sort h1 => exact ofLevel_subst_of_levelParamIn h1 hnm hp
  | const c us =>
    intro Δ v htr hnm hp
    rw [Expr.instantiateLevelParamsCore'] at htr
    cases htr with
    | const _ h2 _ =>
      obtain ⟨u, hu, hpu⟩ := hp
      obtain ⟨n, hn⟩ := List.getElem?_of_mem hu
      have hn' : (us.map (Level.substParams' F red))[n]? = some (Level.substParams' F red u) := by
        rw [List.getElem?_map, hn]; rfl
      obtain ⟨w, -, hw⟩ := mapM_ofLevel_getElem? h2 hn'
      exact ofLevel_subst_of_levelParamIn hw (hnm u hu) hpu
  | app f a ihf iha =>
    intro Δ v htr hnm hp
    rw [Expr.instantiateLevelParamsCore'] at htr
    cases htr with
    | app _ _ htrf htra => exact hp.elim (fun h => ihf htrf hnm.1 h) (fun h => iha htra hnm.2 h)
  | lam n t b bi ihty ihb =>
    intro Δ v htr hnm hp
    rw [Expr.instantiateLevelParamsCore'] at htr
    cases htr with
    | lam _ htrty htrb => exact hp.elim (fun h => ihty htrty hnm.1 h) (fun h => ihb htrb hnm.2 h)
  | forallE n t b bi ihty ihb =>
    intro Δ v htr hnm hp
    rw [Expr.instantiateLevelParamsCore'] at htr
    cases htr with
    | forallE _ _ htrty htrb =>
      exact hp.elim (fun h => ihty htrty hnm.1 h) (fun h => ihb htrb hnm.2 h)
  | letE n t val b nd ihty ihv ihb =>
    intro Δ v htr hnm hp
    rw [Expr.instantiateLevelParamsCore'] at htr
    cases htr with
    | letE _ htrty htrv htrb =>
      exact hp.elim (fun h => ihty htrty hnm.1 h)
        (fun h => h.elim (fun h => ihv htrv hnm.2.1 h) (fun h => ihb htrb hnm.2.2 h))
  | mdata d e ih =>
    intro Δ v htr hnm hp
    rw [Expr.instantiateLevelParamsCore'] at htr
    cases htr with | mdata htr' => exact ih htr' hnm hp
  | proj S i e ih =>
    intro Δ v htr hnm hp
    rw [Expr.instantiateLevelParamsCore'] at htr
    cases htr with | proj htr' _ => exact ih htr' hnm hp

/-- Level substitution reads its argument only at the parameters the level mentions. The
`red` flag is a function of the level alone, so it is shared. -/
theorem substParams_congr {F G : Name → Level} :
    ∀ {l : Level} {red : Bool}, (∀ p, LevelParamIn p l → F p = G p) →
      Level.substParams' F red l = Level.substParams' G red l := by
  intro l
  induction l with
  | zero => intro _ _; rfl
  | mvar => intro _ _; rfl
  | param q => intro red h; exact h q rfl
  | succ u ih => intro red h; rw [Level.substParams', Level.substParams', ih h]
  | max a b iha ihb =>
    intro red h
    rw [Level.substParams', Level.substParams', iha (fun p hp => h p (.inl hp)),
      ihb (fun p hp => h p (.inr hp))]
  | imax a b iha ihb =>
    intro red h
    rw [Level.substParams', Level.substParams', iha (fun p hp => h p (.inl hp)),
      ihb (fun p hp => h p (.inr hp))]

/-- The term-level congruence of `substParams_congr`. -/
theorem instantiateLevelParamsCore'_congr {F G : Name → Level} {red : Bool} :
    ∀ {e : Expr}, (∀ p, ExprParamIn p e → F p = G p) →
      Expr.instantiateLevelParamsCore' red F e = Expr.instantiateLevelParamsCore' red G e := by
  intro e
  induction e with
  | bvar => intro _; rfl
  | fvar => intro _; rfl
  | mvar => intro _; rfl
  | lit => intro _; rfl
  | sort u =>
    intro h
    rw [Expr.instantiateLevelParamsCore', Expr.instantiateLevelParamsCore', substParams_congr h]
  | const c us =>
    intro h
    rw [Expr.instantiateLevelParamsCore', Expr.instantiateLevelParamsCore']
    refine congrArg _ (List.map_congr_left (fun u hu => substParams_congr ?_))
    exact fun p hp => h p ⟨u, hu, hp⟩
  | app f a ihf iha =>
    intro h
    rw [Expr.instantiateLevelParamsCore', Expr.instantiateLevelParamsCore',
      ihf (fun p hp => h p (.inl hp)), iha (fun p hp => h p (.inr hp))]
  | lam n t b bi ihty ihb =>
    intro h
    rw [Expr.instantiateLevelParamsCore', Expr.instantiateLevelParamsCore',
      ihty (fun p hp => h p (.inl hp)), ihb (fun p hp => h p (.inr hp))]
  | forallE n t b bi ihty ihb =>
    intro h
    rw [Expr.instantiateLevelParamsCore', Expr.instantiateLevelParamsCore',
      ihty (fun p hp => h p (.inl hp)), ihb (fun p hp => h p (.inr hp))]
  | letE n t val b nd ihty ihv ihb =>
    intro h
    rw [Expr.instantiateLevelParamsCore', Expr.instantiateLevelParamsCore',
      ihty (fun p hp => h p (.inl hp)), ihv (fun p hp => h p (.inr (.inl hp))),
      ihb (fun p hp => h p (.inr (.inr hp)))]
  | mdata d e ih =>
    intro h
    rw [Expr.instantiateLevelParamsCore', Expr.instantiateLevelParamsCore', ih h]
  | proj S i e ih =>
    intro h
    rw [Expr.instantiateLevelParamsCore', Expr.instantiateLevelParamsCore', ih h]

/-- A positional lookup at a name's own index. -/
theorem idxOf?_map_getD {α : Type _} {ps : List Name} {p : Name} (hp : p ∈ ps)
    (g : Name → α) (d : α) :
    ((List.idxOf? p ps).bind fun i => (ps.map g)[i]?).getD d = g p := by
  have hlt : List.idxOf p ps < ps.length := List.idxOf_lt_length_iff.mpr hp
  have hidx : List.idxOf? p ps = some (List.idxOf p ps) := by
    have hg := List.idxOf_eq_getD_idxOf? p ps
    cases hc : List.idxOf? p ps with
    | none => rw [hc] at hg; simp at hg; omega
    | some i => rw [hc] at hg; simp at hg; rw [hg]
  rw [hidx]
  show ((List.map g ps)[List.idxOf p ps]?).getD d = g p
  rw [List.getElem?_map, List.getElem?_eq_getElem hlt, List.getElem_idxOf hlt]
  rfl

/-- The positional substitution `substParams_of_trExprS` runs on: the by-name image where the
reading scope knows it, and `0` elsewhere, so the list translates outright. -/
theorem mapM_ofLevel_ite (Us : List Name) (F : Name → Level) :
    ∀ ps : List Name,
      (ps.map fun p => if (VLevel.ofLevel Us (F p)).isSome then F p else .zero).mapM
          (VLevel.ofLevel Us)
        = some (ps.map fun p => (VLevel.ofLevel Us (F p)).getD .zero)
  | [] => rfl
  | p :: ps => by
      simp only [List.map_cons, List.mapM_cons, mapM_ofLevel_ite Us F ps]
      cases hp : VLevel.ofLevel Us (F p) <;> simp [hp, VLevel.ofLevel]

/--
**Erasure transports along a by-name level substitution.** `erases_subst_instance`
(`../metarocq/erasure/theories/ErasureProperties.v:383`): the λ□ image is unchanged, and the
two translations are that lemma's typing premises — `hb` at the scope the derivation is read
at, `htr` at the scope it is transported to. `F` itself is arbitrary: where it sends a
parameter `b` mentions, `htr` says the target scope knows the image; where it sends one `b`
does not mention, nothing is claimed and the positional witness substitutes `0`.
-/
theorem Erases.substParams_of_trExprS {env : VEnv} {ps Us : List Name} {F : Name → Level}
    {red : Bool} {b : Expr} {b₀ : LBTerm} {vb v : VExpr}
    (h : Erases env ps [] b b₀) (hnm : NoMaxLevels b) (hb : TrExprS env ps [] b vb)
    (htr : TrExprS env Us [] (Expr.instantiateLevelParamsCore' red F b) v) :
    Erases env Us [] (Expr.instantiateLevelParamsCore' red F b) b₀ := by
  have key := Erases.instL_core (env := env) (Us := Us) (ps := ps)
    (ls := ps.map fun p => if (VLevel.ofLevel Us (F p)).isSome then F p else .zero)
    (ls' := ps.map fun p => (VLevel.ofLevel Us (F p)).getD .zero) (Δ := [])
    (mapM_ofLevel_ite Us F ps) (by simp) rfl red h hnm
  have hagree : ∀ p, ExprParamIn p b →
      ((List.idxOf? p ps).bind fun i =>
        (ps.map fun q => if (VLevel.ofLevel Us (F q)).isSome then F q else .zero)[i]?).getD
          (.param p) = F p := by
    intro p hp
    have hsome : (VLevel.ofLevel Us (F p)).isSome := by
      obtain ⟨w, hw⟩ := ofLevel_subst_of_exprParamIn htr hnm hp
      rw [hw]; rfl
    rw [idxOf?_map_getD (mem_of_exprParamIn hb hp), if_pos hsome]
  rw [instantiateLevelParamsCore'_congr hagree] at key
  rwa [show VLCtx.instL [] (ps.map fun p => (VLevel.ofLevel Us (F p)).getD .zero)
    = ([] : VLCtx) from rfl] at key

/-- The user-facing form of `Erases.substParams_of_trExprS`, at `Expr.instantiateLevelParams`
and an arbitrary parameter list — `SEval.deltaC`'s `ups`, which is a variable of that rule. -/
theorem Erases.instantiateLevelParams_of_trExprS {env : VEnv} {ps Us ups : List Name}
    {us : List Level} {b : Expr} {b₀ : LBTerm} {vb v : VExpr}
    (h : Erases env ps [] b b₀) (hnm : NoMaxLevels b) (hb : TrExprS env ps [] b vb)
    (htr : TrExprS env Us [] (b.instantiateLevelParams ups us) v) :
    Erases env Us [] (b.instantiateLevelParams ups us) b₀ := by
  rw [Expr.instantiateLevelParams_eq] at htr ⊢
  exact Erases.substParams_of_trExprS h hnm hb htr

/-- The positional reading at the empty local context: `Erases.instL` with `hus` in the role
of `consistent_instance_ext` (`ErasureProperties.v:412`). -/
theorem Erases.instantiateLevelParams {env : VEnv} {ps Us : List Name} {us : List Level}
    {us' : List VLevel} {b : Expr} {b₀ : LBTerm}
    (hus : us.mapM (VLevel.ofLevel Us) = some us') (hlen : ps.length = us.length)
    (h : Erases env ps [] b b₀) (hnm : NoMaxLevels b) :
    Erases env Us [] (b.instantiateLevelParams ps us) b₀ := by
  have := Erases.instL (Us := Us) (ps := ps) (ls := us) (ls' := us') (Δ := []) hus hlen h hnm
  rwa [show VLCtx.instL [] us' = ([] : VLCtx) from rfl] at this

end LeanToLambdaBox
