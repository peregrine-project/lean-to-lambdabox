import LeanToLambdaBox.ErasesAbstract
import LeanToLambdaBox.Closed

/-!
# fvar-entry transport for `Erases`

Three moves on the fvar-tagged entries of a `VLCtx`, none of which touches the source `Expr`
or the target `LBTerm`:

* **thinning** — `Erases.thin_vlet` drops an unused fvar-tagged `.vlet` entry
  (`ThinVLet`), which is what lets a let-value erased under an opened binder be read at the
  outer context;
* **weakening** — `erases_weakFV` adds fvar entries along a `VLCtx.FVLift`, on the fvar-only
  well-formedness `VLCtx.FVWF`;
* **unrestricted weakening** — `erases_weak_any` moves a closed, fvar-free source with an
  `LBClosed` target from the empty context to *any* context, with no context hypothesis.

`VLCtx.FVWF` rather than `VLCtx.WF` is forced: the binder arms descend to
`(none, .vlam ty') :: Δ'`, whose `VLCtx.WF` needs `env.IsType Us.length Δ'.toCtx ty'`, and
`Erases.lam` carries only a `TrExprS` for the binder type. `VLCtx.FVWF` is all lean4lean's
`find?`/`weakFV` proofs consume, and it conses freely under a `(none, _)` entry — hence the
`_fvwf` re-proofs below. The `_nofvars` chain drops the context hypothesis outright, paid
for by fvar-freeness of the source: `VLCtx.FVLift'.find?`'s only use of nodup is to refute a
shadowing fvar, in a branch an fvar-free source never reaches.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-! ## Thinning an unused let entry -/

/--
Context surgery for let-value thinning: `Δ₁` is `Δ` with the fvar-tagged let entry
`(some (x, deps), .vlet A e₀)` inserted below a prefix of bvar-tagged (`none`) entries —
the contexts reachable from `(some (x, deps), .vlet A e₀) :: Δ` by the binder rules of
`Erases` and `TrExprS`, which cons only `none`-tagged entries.
-/
inductive ThinVLet (x : FVarId) (deps : List FVarId) (A e₀ : VExpr) :
    VLCtx → VLCtx → Prop where
  | zero : ThinVLet x deps A e₀ ((some (x, deps), .vlet A e₀) :: Δ) Δ
  | succ : ThinVLet x deps A e₀ Δ₁ Δ →
      ThinVLet x deps A e₀ ((none, d) :: Δ₁) ((none, d) :: Δ)

/-- Dropping a `.vlet` entry leaves the pure typing context untouched, since `VLCtx.toCtx`
skips `.vlet` entries. -/
protected theorem ThinVLet.toCtx {x : FVarId} {deps : List FVarId} {A e₀ : VExpr}
    {Δ₁ Δ : VLCtx} (W : ThinVLet x deps A e₀ Δ₁ Δ) :
    Δ₁.toCtx = Δ.toCtx := by
  induction W with
  | zero => rfl
  | @succ _ _ d _ ih =>
    match d with
    | .vlam ty => exact congrArg (ty :: ·) ih
    | .vlet _ _ => exact ih

/-- Dropping the entry removes exactly `x` from the fvar list: the surgery's `succ` steps
cons only `none`-tagged entries, which contribute no fvar. -/
protected theorem ThinVLet.fvars_eq {x : FVarId} {deps : List FVarId} {A e₀ : VExpr}
    {Δ₁ Δ : VLCtx} (W : ThinVLet x deps A e₀ Δ₁ Δ) : Δ₁.fvars = x :: Δ.fvars := by
  induction W with
  | zero => rfl
  | succ _ ih => exact ih

/-- `VLCtx.find?` is unchanged by dropping the unused entry, for every variable other than
the dropped fvar: the fvar tag passes bvar lookups through unshifted, and the `.vlet`'s
`VLocalDecl.depth` of `0` makes the result's lift a no-op. -/
protected theorem ThinVLet.find? {x : FVarId} {deps : List FVarId} {A e₀ : VExpr}
    {Δ₁ Δ : VLCtx} (W : ThinVLet x deps A e₀ Δ₁ Δ)
    {v : Nat ⊕ FVarId} (hv : v ≠ .inr x) :
    Δ₁.find? v = Δ.find? v := by
  induction W generalizing v with
  | @zero Δ₀ =>
    have hnext : VLCtx.next (some (x, deps)) v = some v := by
      obtain i | fv := v
      · rfl
      · have hne : (x == fv) = false := beq_eq_false_iff_ne.2 fun h => hv (by rw [h])
        simp [VLCtx.next, hne]
    simp only [VLCtx.find?, hnext, VLocalDecl.depth]
    cases h : VLCtx.find? Δ₀ v with
    | none => rfl
    | some p => obtain ⟨e', A'⟩ := p; simp
  | succ _ ih =>
    obtain (_ | i) | fv := v
    · rfl
    · simp only [VLCtx.find?, VLCtx.next]
      rw [ih (v := .inl i) (by nofun)]
    · simp only [VLCtx.find?, VLCtx.next]
      rw [ih (v := .inr fv) hv]

/-- Thinning for lean4lean's translation, with the **same** `VExpr` witness: nothing
shifts, since `ThinVLet.find?` is an equality and `ThinVLet.toCtx` transports the typing
side premises verbatim. This discharges the lean4lean premises of `Erases.thin_vlet`. -/
theorem TrExprS.thin_vlet {env : VEnv} {Us : List Name}
    {x : FVarId} {deps : List FVarId} {A e₀ : VExpr} {Δ₁ Δ : VLCtx}
    (W : ThinVLet x deps A e₀ Δ₁ Δ)
    {e : Expr} {e' : VExpr} (H : TrExprS env Us Δ₁ e e')
    (hx : FVarsIn (· ≠ x) e) :
    TrExprS env Us Δ e e' := by
  induction H generalizing Δ with
  | @bvar _ _ _ i h1 => exact .bvar (W.find? (v := .inl i) (by nofun) ▸ h1)
  | @fvar _ _ _ fv h1 =>
    exact .fvar (W.find? (v := .inr fv) (fun h => hx (Sum.inr.inj h)) ▸ h1)
  | sort h1 => exact .sort h1
  | const h1 h2 h3 => exact .const h1 h2 h3
  | app h1 h2 _ _ ih1 ih2 =>
    exact .app (W.toCtx ▸ h1) (W.toCtx ▸ h2) (ih1 W hx.1) (ih2 W hx.2)
  | lam h1 _ _ ih1 ih2 => exact .lam (W.toCtx ▸ h1) (ih1 W hx.1) (ih2 W.succ hx.2)
  | forallE h1 h2 _ _ ih1 ih2 =>
    exact .forallE (W.toCtx ▸ h1) (W.toCtx ▸ h2) (ih1 W hx.1) (ih2 W.succ hx.2)
  | letE h1 _ _ _ ih1 ih2 ih3 =>
    exact .letE (W.toCtx ▸ h1) (ih1 W hx.1) (ih2 W hx.2.1) (ih3 W.succ hx.2.2)
  | lit h1 _ ih => exact .lit h1 (ih W .toConstructor)
  | mdata _ ih => exact .mdata (ih W hx)
  | proj _ h2 ih => exact .proj (ih W hx) (W.toCtx ▸ h2)

/--
Let-value thinning for `Erases`, at depth: a derivation at a context containing an unused
fvar-tagged `.vlet` entry also holds with that entry dropped — same source, same target.

No well-formedness or closedness premise is needed: every lean4lean side premise transports
on the nose via `TrExprS.thin_vlet` and `ThinVLet.toCtx`, and the lookup premises of
`Erases.bvar` and `Erases.fvar` by `ThinVLet.find?`.
-/
theorem Erases.thin_vlet {env : VEnv} {Us : List Name}
    {x : FVarId} {deps : List FVarId} {A e₀ : VExpr} {Δ₁ Δ : VLCtx}
    (W : ThinVLet x deps A e₀ Δ₁ Δ)
    {e : Expr} {t : LBTerm} (H : Erases env Us Δ₁ e t)
    (sc : FVarsIn (· ≠ x) e) :
    Erases env Us Δ e t := by
  induction H generalizing Δ with
  | box htr her => exact .box (TrExprS.thin_vlet W htr sc) (W.toCtx ▸ her)
  | lit hcl _ ih => exact .lit hcl (ih W .toConstructor)
  | @bvar _ i _ _ hf => exact .bvar (W.find? (v := .inl i) (by nofun) ▸ hf)
  | @fvar _ y _ _ hf =>
    exact .fvar (W.find? (v := .inr y) (fun h => sc (Sum.inr.inj h)) ▸ hf)
  | ctor hc hi => exact .ctor hc hi
  | const hc ho => exact .const hc ho
  | app _ _ ihf iha => exact .app (ihf W sc.1) (iha W sc.2)
  | lam hty _ ihb => exact .lam (TrExprS.thin_vlet W hty sc.1) (ihb W.succ sc.2)
  | letE hty hval _ _ ihv ihb =>
    exact .letE (TrExprS.thin_vlet W hty sc.1) (TrExprS.thin_vlet W hval sc.2.1)
      (ihv W sc.2.1) (ihb W.succ sc.2.2)
  | proj hs hi _ ihd => exact .proj hs hi (ihd W sc)
  | mdata _ ih => exact .mdata (ih W sc)

/-- Let-value thinning at depth zero: a let-value erased under the freshly opened binder
`x` is read at the outer context, since the value cannot mention `x`. -/
theorem Erases.strengthen_vlet {env : VEnv} {Us : List Name}
    {x : FVarId} {deps : List FVarId} {A e₀ : VExpr} {Δ : VLCtx}
    {e : Expr} {t : LBTerm}
    (H : Erases env Us ((some (x, deps), .vlet A e₀) :: Δ) e t)
    (sc : FVarsIn (· ≠ x) e) :
    Erases env Us Δ e t :=
  H.thin_vlet .zero sc

/-- Thinning fires on a real derivation: a bound variable read past the dropped let entry
is read the same way at the outer context, with source and target unchanged. -/
example (env : VEnv) (Us : List Name) (x : FVarId) (deps : List FVarId) (A B e₀ : VExpr) :
    Erases env Us [(none, .vlam A)] (.bvar 0) (.bvar 0) :=
  have H : Erases env Us ((some (x, deps), .vlet B e₀) :: [(none, .vlam A)])
      (.bvar 0) (.bvar 0) :=
    .bvar (e' := (VLocalDecl.vlam A).value.liftN (VLocalDecl.vlet B e₀).depth)
      (A := (VLocalDecl.vlam A).type.liftN (VLocalDecl.vlet B e₀).depth) rfl
  H.strengthen_vlet trivial

/-! ## fvar weakening -/

/-- The nodup half of lean4lean's `VLCtx.WF.fvars_nodup`, from the fvar-only `VLCtx.FVWF`.
It is one of exactly two things `VLCtx.FVLift'.find?` asks of its well-formedness premise,
the other being the tail. -/
theorem VLCtx.FVWF.fvars_nodup : ∀ {Δ : VLCtx}, Δ.FVWF → Δ.fvars.Nodup
  | [], _ => .nil
  | (none, _) :: Δ, ⟨hΔ, _⟩ => VLCtx.FVWF.fvars_nodup (Δ := Δ) hΔ
  | (some (fv, _), _) :: Δ, ⟨hΔ, h⟩ => by
    suffices fv ∉ VLCtx.fvars Δ from
      (VLCtx.FVWF.fvars_nodup hΔ).cons (fun _ h (e : fv = _) => this (e ▸ h))
    exact (h _ _ rfl).1

/-- lean4lean's `VLCtx.FVLift'.find?` on the `FVWF`-only premise: the original proof
touches its well-formedness hypothesis only through the tail and `fvars` nodup, both of
which `VLCtx.FVWF` supplies. -/
protected theorem VLCtx.FVLift'.find?_fvwf {Δ Δ' : VLCtx} {dk : Nat} {n : Lift} {k : Nat}
    {v : Nat ⊕ FVarId} {e A : VExpr}
    (W : VLCtx.FVLift' Δ Δ' dk n k) (hΔ' : Δ'.FVWF)
    (H : VLCtx.find? Δ v = some (e, A)) :
    VLCtx.find? Δ' v = some (e.lift' (n.consN k), A.lift' (n.consN k)) := by
  induction W generalizing v e A with
  | refl => simp [H]
  | skip_fvar fv' _ W ih =>
    let (fv', deps) := fv'; simp [VLCtx.find?]
    cases v with simp [VLCtx.next]
    | inl =>
      refine ⟨_, _, ih hΔ'.1 H, ?_⟩
      simp [← VExpr.lift'_consN_skipN, ← VExpr.lift'_comp, Lift.comp_skipN]
    | inr fv =>
      cases eq : fv' == fv <;> simp
      · refine ⟨_, _, ih hΔ'.1 H, ?_⟩
        simp [← VExpr.lift'_consN_skipN, ← VExpr.lift'_comp, Lift.comp_skipN]
      · refine ((List.pairwise_cons.1 (VLCtx.FVWF.fvars_nodup hΔ')).1 fv' ?_ rfl).elim
        exact W.fvars_sublist.subset ((beq_iff_eq ..).1 eq ▸ VLCtx.find?_eq_some.1 ⟨_, H⟩)
  | cons_fvar fv' d _ W ih =>
    let (fv', deps) := fv'; revert H; simp [VLCtx.find?]
    obtain i | fv := v <;> simp [VLCtx.next] <;>
      [skip; cases eq : fv' == fv <;> simp] <;>
      [(rintro _ _ H rfl rfl; refine ⟨_, _, ih hΔ'.1 H, ?_⟩);
       (rintro _ _ H rfl rfl; refine ⟨_, _, ih (v := .inr fv) hΔ'.1 H, ?_⟩);
       rintro rfl rfl] <;>
      open VLocalDecl in
      cases d <;> simp [value, type, depth, lift', VExpr.lift,
        ← VExpr.lift'_consN_skipN, ← VExpr.lift'_comp]
  | cons_bvar d _ ih =>
    simp [VLCtx.find?] at H ⊢
    obtain ⟨_|i⟩ | fv := v <;> simp [VLCtx.next] at H ⊢ <;>
      [(obtain ⟨rfl, rfl⟩ := H);
       (obtain ⟨e, A, H, rfl, rfl⟩ := H
        refine ⟨_, _, ih (v := .inl i) hΔ'.1 H, ?_⟩);
       (obtain ⟨e, A, H, rfl, rfl⟩ := H
        refine ⟨_, _, ih (v := .inr fv) hΔ'.1 H, ?_⟩)] <;>
      open VLocalDecl in
      cases d <;> simp [value, type, depth, lift', VExpr.lift,
        ← VExpr.lift'_consN_skipN, ← VExpr.lift'_comp]

/-- The `VLCtx.FVLift` form of `VLCtx.FVLift'.find?_fvwf`. -/
protected theorem VLCtx.FVLift.find?_fvwf {Δ Δ' : VLCtx} {dk n k : Nat}
    {v : Nat ⊕ FVarId} {e A : VExpr}
    (W : VLCtx.FVLift Δ Δ' dk n k) (hΔ' : Δ'.FVWF)
    (H : VLCtx.find? Δ v = some (e, A)) :
    VLCtx.find? Δ' v = some (e.liftN n k, A.liftN n k) := by
  simpa [VExpr.lift'_consN_skipN] using VLCtx.FVLift'.find?_fvwf W.toFVLift' hΔ' H

/-- lean4lean's `TrExprS.weakFV'` on the `FVWF`-only premise: `find?` is discharged by
`VLCtx.FVLift'.find?_fvwf`, and the binder arms extend the context with an `FVWF` cons,
which needs nothing about the binder type. -/
theorem TrExprS.weakFV'_fvwf {env : VEnv} (henv : env.Ordered) {Us : List Name}
    {Δ Δ' : VLCtx} {dk : Nat} {n : Lift} {k : Nat}
    (W : VLCtx.FVLift' Δ Δ' dk n k) (hΔ' : Δ'.FVWF)
    {e : Expr} {e' : VExpr} (H : TrExprS env Us Δ e e') :
    TrExprS env Us Δ' e (e'.lift' (n.consN k)) := by
  induction H generalizing Δ' dk k with
  | bvar h1 => exact .bvar (VLCtx.FVLift'.find?_fvwf W hΔ' h1)
  | fvar h1 => exact .fvar (VLCtx.FVLift'.find?_fvwf W hΔ' h1)
  | sort h1 => exact .sort h1
  | const h1 h2 h3 => exact .const h1 h2 h3
  | app h1 h2 _ _ ih1 ih2 =>
    exact .app (h1.weak' henv W.toCtx) (h2.weak' henv W.toCtx) (ih1 W hΔ') (ih2 W hΔ')
  | lam h1 _ _ ih1 ih2 =>
    exact .lam (h1.weak' henv W.toCtx) (ih1 W hΔ') (ih2 (W.cons_bvar _) ⟨hΔ', nofun⟩)
  | forallE h1 h2 _ _ ih1 ih2 =>
    exact .forallE (h1.weak' henv W.toCtx) (h2.weak' henv W.toCtx.cons)
      (ih1 W hΔ') (ih2 (W.cons_bvar _) ⟨hΔ', nofun⟩)
  | letE h1 _ _ _ ih1 ih2 ih3 =>
    exact .letE (h1.weak' henv W.toCtx) (ih1 W hΔ') (ih2 W hΔ')
      (ih3 (W.cons_bvar _) ⟨hΔ', nofun⟩)
  | lit h1 _ ih => exact .lit h1 (ih W hΔ')
  | mdata _ ih => exact .mdata (ih W hΔ')
  | proj _ h2 ih => exact .proj (ih W hΔ') (h2.weak' henv W.toCtx)

/-- The `VLCtx.FVLift` form of `TrExprS.weakFV'_fvwf`, which is the shape the `box`, `lam`
and `letE` arms of `erases_weakFV` consume. -/
theorem TrExprS.weakFV_fvwf {env : VEnv} (henv : env.Ordered) {Us : List Name}
    {Δ Δ' : VLCtx} {dk n k : Nat}
    (W : VLCtx.FVLift Δ Δ' dk n k) (hΔ' : Δ'.FVWF)
    {e : Expr} {e' : VExpr} (H : TrExprS env Us Δ e e') :
    TrExprS env Us Δ' e (e'.liftN n k) := by
  simpa [VExpr.lift'_consN_skipN] using TrExprS.weakFV'_fvwf henv W.toFVLift' hΔ' H

/--
fvar weakening for `Erases`: a derivation replays verbatim at any fvar-extension of its
`VLCtx`.

Source and target are untouched — a `VLCtx.FVLift` inserts fvar-tagged entries and re-lifts
the hidden `VExpr` witnesses, and neither language's de Bruijn indices see fvar entries.
-/
theorem erases_weakFV {env : VEnv} (henv : env.Ordered) {Us : List Name}
    {Δ Δ' : VLCtx} {dk n k : Nat}
    (W : VLCtx.FVLift Δ Δ' dk n k) (hΔ' : Δ'.FVWF)
    {e : Expr} {t : LBTerm} (h : Erases env Us Δ e t) :
    Erases env Us Δ' e t := by
  induction h generalizing Δ' dk k with
  | box htr her => exact .box (TrExprS.weakFV_fvwf henv W hΔ' htr) (her.weakN henv W.toCtx)
  | lit hcl _ ih => exact .lit hcl (ih W hΔ')
  | bvar hf => exact .bvar (VLCtx.FVLift.find?_fvwf W hΔ' hf)
  | fvar hf => exact .fvar (VLCtx.FVLift.find?_fvwf W hΔ' hf)
  | ctor hc hi => exact .ctor hc hi
  | const hc ho => exact .const hc ho
  | app _ _ ihf iha => exact .app (ihf W hΔ') (iha W hΔ')
  | lam hty _ ihb =>
    exact .lam (TrExprS.weakFV_fvwf henv W hΔ' hty) (ihb (W.cons_bvar _) ⟨hΔ', nofun⟩)
  | letE hty hval _ _ ihv ihb =>
    exact .letE (TrExprS.weakFV_fvwf henv W hΔ' hty) (TrExprS.weakFV_fvwf henv W hΔ' hval)
      (ihv W hΔ') (ihb (W.cons_bvar _) ⟨hΔ', nofun⟩)
  | proj hs hi _ ihd => exact .proj hs hi (ihd W hΔ')
  | mdata _ ih => exact .mdata (ih W hΔ')

/-! ## Unrestricted weakening for closed, fvar-free terms -/

/-- `VLCtx.find?` transports along a `VLCtx.FVLift'` for **bvar** lookups with no hypothesis
on the target context: the `skip_fvar` and `cons_fvar` cases need `fvars` nodup only in
their `.inr` branch, to refute a shadowing fvar, and `.inl` lookups never reach it. -/
protected theorem VLCtx.FVLift'.find?_inl {Δ Δ' : VLCtx} {dk : Nat} {n : Lift} {k : Nat}
    {i : Nat} {e A : VExpr}
    (W : VLCtx.FVLift' Δ Δ' dk n k) (H : VLCtx.find? Δ (.inl i) = some (e, A)) :
    VLCtx.find? Δ' (.inl i) = some (e.lift' (n.consN k), A.lift' (n.consN k)) := by
  induction W generalizing i e A with
  | refl => simp [H]
  | skip_fvar fv' _ _ ih =>
    let (fv', deps) := fv'; simp [VLCtx.find?, VLCtx.next]
    refine ⟨_, _, ih H, ?_⟩
    simp [← VExpr.lift'_consN_skipN, ← VExpr.lift'_comp, Lift.comp_skipN]
  | cons_fvar fv' d _ _ ih =>
    let (fv', deps) := fv'; revert H; simp [VLCtx.find?, VLCtx.next]
    rintro _ _ H rfl rfl
    refine ⟨_, _, ih H, ?_⟩
    open VLocalDecl in
    cases d <;> simp [depth, ← VExpr.lift'_consN_skipN, ← VExpr.lift'_comp]
  | cons_bvar d _ ih =>
    simp [VLCtx.find?] at H ⊢
    obtain _ | i := i <;> simp [VLCtx.next] at H ⊢ <;>
      [(obtain ⟨rfl, rfl⟩ := H);
       (obtain ⟨e, A, H, rfl, rfl⟩ := H
        refine ⟨_, _, ih H, ?_⟩)] <;>
      open VLocalDecl in
      cases d <;> simp [value, type, depth, lift', VExpr.lift,
        ← VExpr.lift'_consN_skipN, ← VExpr.lift'_comp]

/-- The `VLCtx.FVLift` form of `VLCtx.FVLift'.find?_inl`. -/
protected theorem VLCtx.FVLift.find?_inl {Δ Δ' : VLCtx} {dk n k : Nat}
    {i : Nat} {e A : VExpr}
    (W : VLCtx.FVLift Δ Δ' dk n k) (H : VLCtx.find? Δ (.inl i) = some (e, A)) :
    VLCtx.find? Δ' (.inl i) = some (e.liftN n k, A.liftN n k) := by
  simpa [VExpr.lift'_consN_skipN] using VLCtx.FVLift'.find?_inl W.toFVLift' H

/-- lean4lean's `TrExprS.weakFV'` with the target-context well-formedness premise removed
entirely, paid for by fvar-freeness of the source: `bvar` goes through
`VLCtx.FVLift'.find?_inl`, and `fvar` is impossible. -/
theorem TrExprS.weakFV'_nofvars {env : VEnv} (henv : env.Ordered) {Us : List Name}
    {Δ Δ' : VLCtx} {dk : Nat} {n : Lift} {k : Nat}
    (W : VLCtx.FVLift' Δ Δ' dk n k)
    {e : Expr} {e' : VExpr} (H : TrExprS env Us Δ e e')
    (hfvf : FVarsIn (fun _ => False) e) :
    TrExprS env Us Δ' e (e'.lift' (n.consN k)) := by
  induction H generalizing Δ' dk k with
  | bvar h1 => exact .bvar (VLCtx.FVLift'.find?_inl W h1)
  | fvar _ => exact (hfvf : False).elim
  | sort h1 => exact .sort h1
  | const h1 h2 h3 => exact .const h1 h2 h3
  | app h1 h2 _ _ ih1 ih2 =>
    exact .app (h1.weak' henv W.toCtx) (h2.weak' henv W.toCtx) (ih1 W hfvf.1) (ih2 W hfvf.2)
  | lam h1 _ _ ih1 ih2 =>
    exact .lam (h1.weak' henv W.toCtx) (ih1 W hfvf.1) (ih2 (W.cons_bvar _) hfvf.2)
  | forallE h1 h2 _ _ ih1 ih2 =>
    exact .forallE (h1.weak' henv W.toCtx) (h2.weak' henv W.toCtx.cons)
      (ih1 W hfvf.1) (ih2 (W.cons_bvar _) hfvf.2)
  | letE h1 _ _ _ ih1 ih2 ih3 =>
    exact .letE (h1.weak' henv W.toCtx) (ih1 W hfvf.1) (ih2 W hfvf.2.1)
      (ih3 (W.cons_bvar _) hfvf.2.2)
  | lit h1 _ ih => exact .lit h1 (ih W FVarsIn.toConstructor)
  | mdata _ ih => exact .mdata (ih W hfvf)
  | proj _ h2 ih => exact .proj (ih W hfvf) (h2.weak' henv W.toCtx)

/-- The `VLCtx.FVLift` form of `TrExprS.weakFV'_nofvars`. -/
theorem TrExprS.weakFV_nofvars {env : VEnv} (henv : env.Ordered) {Us : List Name}
    {Δ Δ' : VLCtx} {dk n k : Nat}
    (W : VLCtx.FVLift Δ Δ' dk n k)
    {e : Expr} {e' : VExpr} (H : TrExprS env Us Δ e e')
    (hfvf : FVarsIn (fun _ => False) e) :
    TrExprS env Us Δ' e (e'.liftN n k) := by
  simpa [VExpr.lift'_consN_skipN] using TrExprS.weakFV'_nofvars henv W.toFVLift' H hfvf

/--
fvar weakening for an fvar-free source, with no well-formedness premise on the target
context: an fvar-free source never performs an `.inr` lookup, so the branch that needs
`fvars` nodup is unreachable and `Erases.fvar` cannot fire.
-/
theorem erases_weakFV_nofvars {env : VEnv} (henv : env.Ordered) {Us : List Name}
    {Δ Δ' : VLCtx} {dk n k : Nat}
    (W : VLCtx.FVLift Δ Δ' dk n k)
    {e : Expr} {t : LBTerm} (h : Erases env Us Δ e t)
    (hfvf : FVarsIn (fun _ => False) e) :
    Erases env Us Δ' e t := by
  induction h generalizing Δ' dk k with
  | box htr her => exact .box (TrExprS.weakFV_nofvars henv W htr hfvf) (her.weakN henv W.toCtx)
  | lit hcl _ ih => exact .lit hcl (ih W FVarsIn.toConstructor)
  | bvar hf => exact .bvar (VLCtx.FVLift.find?_inl W hf)
  | fvar _ => exact (hfvf : False).elim
  | ctor hc hi => exact .ctor hc hi
  | const hc ho => exact .const hc ho
  | app _ _ ihf iha => exact .app (ihf W hfvf.1) (iha W hfvf.2)
  | lam hty _ ihb =>
    exact .lam (TrExprS.weakFV_nofvars henv W hty hfvf.1) (ihb (W.cons_bvar _) hfvf.2)
  | letE hty hval _ _ ihv ihb =>
    exact .letE (TrExprS.weakFV_nofvars henv W hty hfvf.1)
      (TrExprS.weakFV_nofvars henv W hval hfvf.2.1) (ihv W hfvf.2.1)
      (ihb (W.cons_bvar _) hfvf.2.2)
  | proj hs hi _ ihd => exact .proj hs hi (ihd W hfvf)
  | mdata _ ih => exact .mdata (ih W hfvf)

/--
Weakening to an arbitrary `VLCtx`: for a closed, fvar-free source erasing to an `LBClosed`
target, a derivation at the empty context holds at *every* context.

The induction adds one entry at a time. A bvar entry goes through `erases_shift`, whose two
lifts `hcl` and `hlb` make the identity; an fvar entry — possibly shadowing — goes through
`erases_weakFV_nofvars`, which asks nothing of the context.
-/
theorem erases_weak_any {env : VEnv} (henv : env.Ordered) {Us : List Name}
    {e : Expr} {t : LBTerm}
    (hcl : Closed e 0) (hfvf : FVarsIn (fun _ => False) e) (hlb : LBClosed t 0)
    (h : Erases env Us [] e t) (Δ : VLCtx) :
    Erases env Us Δ e t := by
  induction Δ with
  | nil => exact h
  | cons hd Δ₀ ih =>
    obtain ⟨_ | fvd, d⟩ := hd
    · have hs := erases_shift henv (VLCtx.BVLift.skip d .refl) ih
      rwa [Expr.liftLooseBVars_eq_self (Nat.le_of_eq hcl.looseBVarRange_zero),
        LBClosed.shift_eq hlb (Nat.zero_le 0) 1] at hs
    · exact erases_weakFV_nofvars henv (VLCtx.FVLift.skip_fvar fvd d .refl) ih hfvf

/-- Unrestricted weakening fires: a closed, fvar-free λ derivation at the empty context is
replayed at a context carrying both a bvar entry and an fvar entry. -/
example (env : VEnv) (henv : env.Ordered) (Us : List Name)
    (x : FVarId) (A B : VExpr) (nm : Name) (bi : BinderInfo) :
    Erases env Us [(none, .vlam B), (some (x, []), .vlam A)]
      (.lam nm (.sort .zero) (.bvar 0) bi) (.lambda (.named nm.toString) (.bvar 0)) :=
  have H : Erases env Us [] (.lam nm (.sort .zero) (.bvar 0) bi)
      (.lambda (.named nm.toString) (.bvar 0)) :=
    .lam (ty' := .sort .zero) (.sort rfl)
      (.bvar (e' := (VLocalDecl.vlam (VExpr.sort .zero)).value)
        (A := (VLocalDecl.vlam (VExpr.sort .zero)).type) rfl)
  have hcl : Closed (.lam nm (.sort .zero) (.bvar 0) bi) 0 := ⟨trivial, Nat.zero_lt_one⟩
  have hfvf : FVarsIn (fun _ => False) (.lam nm (.sort .zero) (.bvar 0) bi) := ⟨rfl, trivial⟩
  have hlb : LBClosed (.lambda (.named nm.toString) (.bvar 0)) 0 := Nat.zero_lt_one
  erases_weak_any henv hcl hfvf hlb H _

end LeanToLambdaBox
