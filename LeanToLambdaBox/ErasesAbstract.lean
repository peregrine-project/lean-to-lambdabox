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
* `Erases.abstract` and `Erases.uninstantiateN` — closing a free variable back into a de
  Bruijn binder (`Expr.abstract1` / `toBvar`).

`Expr.abstract1` shifts loose bvars at or above the insertion level; `toBvar` does not. The
two agree only on terms with no such loose bvar, which is why `Erases.abstract` carries a
`Closed` premise.

The last section transports `Erases` along a **level instantiation**: the source and the
`VLCtx` are instantiated and the λ□ target is unchanged, since λ□ carries no levels. It is
strict — an equation, not lean4lean's `≈` — on `max`-free levels, which is what
`NoMaxLevels` names.
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
  | const hc => exact .const hc
  | app _ _ ihf iha => exact .app (ihf W) (iha W)
  | lam hty _ ihb => exact .lam (hty.weakBV henv W) (ihb (W.cons _))
  | letE hty hval _ _ ihv ihb =>
    exact .letE (hty.weakBV henv W) (hval.weakBV henv W) (ihv W) (ihb (W.cons _))
  | proj hs hi _ ihd => exact .proj hs hi (ihd W)
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
  | const hc => exact .const hc
  | app _ _ ihf iha => exact .app (ihf W) (iha W)
  | lam hty _ ihb =>
    exact .lam (TrExprS.instN henv ht₀ t₀ W hty) (ihb (W.succ (d := .vlam _)))
  | letE hty hval _ _ ihv ihb =>
    exact .letE (TrExprS.instN henv ht₀ t₀ W hty) (TrExprS.instN henv ht₀ t₀ W hval)
      (ihv W) (ihb (W.succ (d := .vlet ..)))
  | proj hs hi _ ihd => exact .proj hs hi (ihd W)
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
  | const hc' => exact .const hc'
  | app _ _ ihf iha => exact .app (ihf W hc.1) (iha W hc.2)
  | lam hty _ ihb => exact .lam (hty.abstract W) (ihb W.succ hc.2)
  | letE hty hval _ _ ihv ihb =>
    exact .letE (hty.abstract W) (hval.abstract W) (ihv W hc.2.1) (ihb W.succ hc.2.2)
  | proj hs hi _ ihd => exact .proj hs hi (ihd W hc)
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

/-- `IsArity` is a spine of `forallE`s ending in a `sort`; `instL` fixes both
constructors. -/
theorem IsArity.instL {ls : List VLevel} : ∀ {A : VExpr}, IsArity A → IsArity (A.instL ls)
  | _, .sort _ => .sort _
  | _, .forallE _ _ h => .forallE _ _ (IsArity.instL h)

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
  | const hc => intro _; exact .const hc
  | app _ _ ihf iha => intro hnm; exact .app (ihf hnm.1) (iha hnm.2)
  | lam hty _ ihb =>
    intro hnm; exact .lam (TrExprS.instL_core Hls eq eqF red hty hnm.1) (ihb hnm.2)
  | letE hty hval _ _ ihv ihb =>
    intro hnm
    exact .letE (TrExprS.instL_core Hls eq eqF red hty hnm.1)
      (TrExprS.instL_core Hls eq eqF red hval hnm.2.1) (ihv hnm.2.1) (ihb hnm.2.2)
  | proj hs hi _ ihd => intro hnm; exact .proj hs hi (ihd hnm)
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

end LeanToLambdaBox
