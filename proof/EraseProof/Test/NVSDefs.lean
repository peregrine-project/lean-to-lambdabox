import EraseProof.Test.NVSBlocks

/-!
# NV-S: the Metalean definitions on `N`

The Metalean forms of `N.casesOn`, `N.below`, `N.brecOn.go` and `N.brecOn` (`Test/NVSData.lean`)
and the typing of their values at their types, in any well-formed environment whose heads hold
`PUnit`'s, `PProd`'s and `N`'s blocks and the earlier definitions. `N.below motive t` unfolds
(δ, two β, the recursor's ι) to `PUnit` on `N.z` and to `PProd (motive n) (N.below motive n)` on
`N.s n` (`belowZ_defeq`, `belowS_defeq`, by `Metalean.WHRedS.defeq`). For `Test/NVSModel.lean`.
-/

open Lean Metalean

namespace EraseProof.Test.NVS

open EraseProof.Test.NV1 (typed_of_eq var_of_get app_typed const_typed fin0_eq lu)
open EraseProof.Test.NVR (nSig nBlock mN mZ mS mN_typed mZ_typed mS_typed indN_typed recAllowedN
  appMotN_typed motN_typed)

/-- `max 1 l`. -/
abbrev m1 {ℓ : Nat} (l : Level ℓ) : Level ℓ := .max (.succ .zero) l

/-- `N → Sort l`. -/
abbrev motNM {ζ : Sigs} (η : Head ζ (.inductive nSig)) {ℓ n : Nat} (l : Level ℓ) : Expr ζ ℓ n :=
  EraseProof.Test.NVR.motN η l

section Defs
variable {ζ : Sigs} (ηPU : Head ζ (.inductive puSig)) (ηPP : Head ζ (.inductive ppSig))
  (ηN : Head ζ (.inductive nSig))

/-! ## `N.casesOn` -/

/-- `{motive : N → Sort u} → (t : N) → motive N.z → ((n : N) → motive (N.s n)) → motive t` -/
def casesOnTyM : Expr ζ 1 0 :=
  .forallE (motNM ηN lu) (.forallE (mN ηN) (.forallE (.app #0 (mZ ηN))
    (.forallE (.forallE (mN ηN) (.app #0 (mS ηN #3))) (.app #0 #1))))

/-- The minor premises `z` and `fun n n_ih => s n` of `N.casesOn`'s recursor. -/
def minsCO : (t : Fin 1) → Fin (nSig.nctors t) → Expr ζ 1 4 :=
  fun _ c => if c.val = 0 then #2 else .lam (mN ηN) (.lam (.app #0 #4) (.app #3 #4))

/-- `fun {motive} t z s => @N.rec motive z (fun n n_ih => s n) t` -/
def casesOnValM : Expr ζ 1 0 :=
  .lam (motNM ηN lu) (.lam (mN ηN) (.lam (.app #0 (mZ ηN))
    (.lam (.forallE (mN ηN) (.app #0 (mS ηN #3)))
      (.recr ηN 0 Fin.elim0 lu Fin.elim0 (fun _ => #0) (minsCO ηN) Fin.elim0 #1))))

/-! ## `N.below` -/

/-- `max 1 u` at the level parameter `u`. -/
abbrev m1M : Level 1 := m1 lu

/-- `{motive : N → Sort u} → N → Sort (max 1 u)` -/
def belowTyM : Expr ζ 1 0 := .forallE (motNM ηN lu) (.forallE (mN ηN) (.sort m1M))

/-- The minor premises `PUnit` and `fun n n_ih => PProd (motive n) n_ih` of `N.below`'s recursor. -/
def minsBl : (t : Fin 1) → Fin (nSig.nctors t) → Expr ζ 1 2 :=
  fun _ c => if c.val = 0 then mPU ηPU m1M
    else .lam (mN ηN) (.lam (.sort m1M) (mPP ηPP lu m1M (.app #0 #2) #3))

/-- `fun {motive} t => @N.rec.{max 1 u + 1} (fun t => Sort (max 1 u)) PUnit
(fun n n_ih => PProd (motive n) n_ih) t` -/
def belowValM : Expr ζ 1 0 :=
  .lam (motNM ηN lu) (.lam (mN ηN)
    (.recr ηN 0 Fin.elim0 (.succ m1M) Fin.elim0 (fun _ => .lam (mN ηN) (.sort m1M))
      (minsBl ηPU ηPP ηN) Fin.elim0 #1))

end Defs

/-- The motive `fun m => N` of `add`'s structural recursion. -/
def motNL {ζ : Sigs} (ηN : Head ζ (.inductive nSig)) {ℓ n : Nat} : Expr ζ ℓ n :=
  .lam (mN ηN) (mN ηN)

/-- One more weak-head step. -/
theorem whredS_step {ζ : Sigs} {E : Env ζ} {ℓ n : Nat} {a b c : Expr ζ ℓ n} (h : WHRedS E a b)
    (h' : WHRed E b c) : WHRedS E a c :=
  Relation.ReflTransGen.tail h h'

/-- Rewrite both sides and the type of a definitional equality. -/
theorem defeq_rw {ζ : Sigs} {E : Env ζ} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} {e₁ e₂ t e₁' e₂' t' : Expr ζ ℓ n}
    (h : E[Γ] ⊢ e₁ ≡ e₂ : t) (h₁ : e₁ = e₁') (h₂ : e₂ = e₂') (ht : t = t') :
    E[Γ] ⊢ e₁' ≡ e₂' : t' :=
  h₁ ▸ h₂ ▸ ht ▸ h

/-! Level instantiation in its unfolded form (`Level.inst`), as `Expr.instL` produces it. -/
theorem rinst_zero {ℓ ℓ' : Nat} (σ : Param ℓ → Level ℓ') : Level.inst σ .zero = .zero :=
  Level.inst_zero σ
theorem rinst_param {ℓ ℓ' : Nat} (σ : Param ℓ → Level ℓ') (p : Param ℓ) :
    Level.inst σ (.param p) = σ p := Level.inst_param σ p
theorem rinst_succ {ℓ ℓ' : Nat} (σ : Param ℓ → Level ℓ') (u : Level ℓ) :
    Level.inst σ u.succ = (Level.inst σ u).succ := Level.inst_succ σ u
theorem rinst_max {ℓ ℓ' : Nat} (σ : Param ℓ → Level ℓ') (u v : Level ℓ) :
    Level.inst σ (u.max v) = (Level.inst σ u).max (Level.inst σ v) := Level.inst_max σ u v
theorem rinst_imax {ℓ ℓ' : Nat} (σ : Param ℓ → Level ℓ') (u v : Level ℓ) :
    Level.inst σ (u.imax v) = (Level.inst σ u).imax (Level.inst σ v) := Level.inst_imax σ u v

/-- `N.below.{l} mo a`. -/
def belowM {ζ : Sigs} (ηBl : Head ζ (.const .def 1)) {ℓ n : Nat} (l : Level ℓ)
    (mo a : Expr ζ ℓ n) : Expr ζ ℓ n :=
  .app (.app (.const ηBl ![l]) mo) a

/-- Compute substitutions, renamings, weakenings and the recursor's ι on the terms of `N`, `PUnit`
and `PProd`. -/
syntax (name := _rsx) "rsx" ("[" ident,* "]")? (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| rsx $[$loc]?) => `(tactic| rsx [Ctx.get] $[$loc]?)
  | `(tactic| rsx [$ts,*] $[$loc]?) => `(tactic| simp [$[$ts:ident],*, Frame.plug,
      Expr.rename, Expr.inst, Expr.subst, Subst.lift, Subst.extend_apply, Ren.lift, Ren.wkFrom,
      Subst.precomp, Ren.comp, minsBl, mPU, mPP, mPPmk, mPUu, mN, mZ, mS, motNM,
      EraseProof.Test.NVR.motN, belowValM, belowTyM, fin0_eq, Inductive.iotaRhs,
      Inductive.iotaIHs, Ctor.iotaIH, RecField.iotaIH, Expr.apps_succ, Ctx.lam,
      RecField.instantiatedTelescope, RecField.instantiatedIndices, Expr.applyBound,
      Expr.wkClosed, Expr.wk, Expr.wkFrom, Expr.wkN, Expr.instL, rinst_zero, rinst_param,
      rinst_succ, rinst_max, rinst_imax, m1, funext_iff, Fin.forall_fin_one, Fin.forall_fin_two,
      Subst.rename, Subst.id, motNL, Subst.comp, belowM, Ctx.get] $[$loc]?)

/-- Close an equation of Metalean terms that differ in small `Fin` functions. -/
macro "rfin" : tactic => `(tactic| repeat' (first
    | (rsx; done)
    | with_reducible rfl
    | (funext t c; fin_cases t; fin_cases c <;> rsx)
    | (funext t; fin_cases t <;> rsx)
    | (funext i; exact i.elim0)
    | congr 1))

section Below
variable {ζ : Sigs} {E : Env ζ} {ηPU : Head ζ (.inductive puSig)} {ηPP : Head ζ (.inductive ppSig)}
  {ηN : Head ζ (.inductive nSig)} {ηBl : Head ζ (.const .def 1)} {ℓ : Nat}

/-- `N.below.{l}`'s type `(motive : N → Sort l) → N → Sort (max 1 l)`. -/
def belowTyL (ηN : Head ζ (.inductive nSig)) {n : Nat} (l : Level ℓ) : Expr ζ ℓ n :=
  .forallE (motNM ηN l) (.forallE (mN ηN) (.sort (m1 l)))

theorem belowTy_wk {n : Nat} (l : Level ℓ) :
    ((belowTyM ηN){![l]}).wkClosed (n := n) = belowTyL ηN l := by
  have h : ((belowTyM ηN){![l]} : Expr ζ ℓ 0) = belowTyL ηN l := by
    simp [belowTyM, belowTyL, motNM, EraseProof.Test.NVR.motN, mN]
  rw [h]
  exact Expr.wkClosed_of_rename (f := fun n => belowTyL ηN l) (fun ρ => by
    simp [belowTyL, motNM, EraseProof.Test.NVR.motN, mN, Expr.rename]) n

theorem belowM_typed (hE : EnvWF E) (ht : (E.get ηBl).constType = belowTyM ηN) {n : Nat}
    {Γ : Ctx ζ ℓ 0 n} {l : Level ℓ} {mo a : Expr ζ ℓ n} (hmo : E[Γ] ⊢ mo : motNM ηN l)
    (ha : E[Γ] ⊢ a : mN ηN) : E[Γ] ⊢ belowM ηBl l mo a : .sort (m1 l) := by
  have h0 : E[Γ] ⊢ .const ηBl ![l] : belowTyL ηN l :=
    const_typed hE ηBl ![l] (by rw [ht]; exact belowTy_wk l)
  have h1 := app_typed h0 hmo
  have h1' : E[Γ] ⊢ .app (.const ηBl ![l]) mo : .forallE (mN ηN) (.sort (m1 l)) :=
    typed_of_eq h1 (by simp [belowTyL, Expr.inst, Expr.subst, mN])
  exact typed_of_eq (app_typed h1' ha) (by simp [Expr.inst, Expr.subst])

/-- The recursor `N.below.{l} mo a` unfolds to (δ and two β). -/
def belowRec (ηPU : Head ζ (.inductive puSig)) (ηPP : Head ζ (.inductive ppSig))
    (ηN : Head ζ (.inductive nSig)) {n : Nat} (l : Level ℓ) (mo a : Expr ζ ℓ n) : Expr ζ ℓ n :=
  .recr ηN 0 Fin.elim0 (.succ (m1 l)) Fin.elim0 (fun _ => .lam (mN ηN) (.sort (m1 l)))
    (fun _ c => if c.val = 0 then mPU ηPU (m1 l) else .lam (mN ηN) (.lam (.sort (m1 l))
      (mPP ηPP l (m1 l) (.app (mo.wkN 2) (.var ⟨n, by omega⟩)) (.var ⟨n + 1, by omega⟩))))
    Fin.elim0 a

theorem ppLevel_m1 (l : Level ℓ) : ppLevel l (m1 l) = m1 l := Level.ext fun ν => by simp

variable (hE : EnvWF E) (hn : (E.get ηN).block = nBlock) (hpp : (E.get ηPP).block = ppBlock)
  (ht : (E.get ηBl).constType = belowTyM ηN) (hv : (E.get ηBl).defValue = belowValM ηPU ηPP ηN)
include hE ht hv

/-- `N.below motive n` unfolds to its recursor, under `motive _ _ n _ _` (`N.brecOn.go`). -/
theorem belowRed_var {Γ : Ctx ζ ℓ 0 5} (hΓ : E[Γ] ⊢ ok) {l : Level ℓ}
    (hmo : E[Γ] ⊢ #0 : motNM ηN l) (ha : E[Γ] ⊢ #3 : mN ηN) :
    E[Γ] ⊢ belowM ηBl l #0 #3 ≡ belowRec ηPU ηPP ηN l #0 #3 : .sort (m1 l) := by
  have h1 : E ⊢ belowM ηBl l (#0 : Expr ζ ℓ 5) #3 ⤳*
      .app (.app ((E.get ηBl).defValue{![l]}.wkClosed) #0) #3 :=
    .single (.frame (K := .app _) (.frame (K := .app _) .delta))
  rw [hv] at h1
  have h2 := whredS_step h1 (.frame (K := .app _) .beta); rsx at h2
  have h3 := whredS_step h2 .beta; rsx at h3
  exact defeq_rw (WHRedS.defeq hE hΓ h3 (belowM_typed hE ht hmo ha)) (by rsx)
    (by simp only [belowRec]; rsx) (by rsx)

/-- `N.below (fun m => N) k` unfolds to its recursor, under `n m f k _` (`add._f`). -/
theorem belowRed_motNL {Γ : Ctx ζ ℓ 0 5} (hΓ : E[Γ] ⊢ ok) {l : Level ℓ}
    (hmo : E[Γ] ⊢ motNL ηN : motNM ηN l) (ha : E[Γ] ⊢ #3 : mN ηN) :
    E[Γ] ⊢ belowM ηBl l (motNL ηN) #3 ≡ belowRec ηPU ηPP ηN l (motNL ηN) #3 : .sort (m1 l) := by
  have h1 : E ⊢ belowM ηBl l (motNL ηN : Expr ζ ℓ 5) #3 ⤳*
      .app (.app ((E.get ηBl).defValue{![l]}.wkClosed) (motNL ηN)) #3 :=
    .single (.frame (K := .app _) (.frame (K := .app _) .delta))
  rw [hv] at h1
  have h2 := whredS_step h1 (.frame (K := .app _) .beta); rsx at h2
  have h3 := whredS_step h2 .beta; rsx at h3
  exact defeq_rw (WHRedS.defeq hE hΓ h3 (belowM_typed hE ht hmo ha)) (by rsx)
    (by simp only [belowRec]; rsx) (by rsx)

include hn in
/-- `N.below motive (N.s n)` unfolds to `PProd (motive n) (N.below motive n)`'s recursor form. -/
theorem belowS_var {Γ : Ctx ζ ℓ 0 5} (hΓ : E[Γ] ⊢ ok) {l : Level ℓ}
    (hmo : E[Γ] ⊢ #0 : motNM ηN l) (ha : E[Γ] ⊢ #3 : mN ηN) :
    E[Γ] ⊢ belowM ηBl l #0 (mS ηN #3) ≡
      mPP ηPP l (m1 l) (.app #0 #3) (belowRec ηPU ηPP ηN l #0 #3) : .sort (m1 l) := by
  have h1 : E ⊢ belowM ηBl l (#0 : Expr ζ ℓ 5) (mS ηN #3) ⤳*
      .app (.app ((E.get ηBl).defValue{![l]}.wkClosed) #0) (mS ηN #3) :=
    .single (.frame (K := .app _) (.frame (K := .app _) .delta))
  rw [hv] at h1
  have h2 := whredS_step h1 (.frame (K := .app _) .beta); rsx at h2
  have h3 := whredS_step h2 .beta; rsx at h3
  have h4 := whredS_step h3 .iota; rw [hn] at h4; rsx at h4
  have h5 := whredS_step h4 (.frame (K := .app _) .beta); rsx at h5
  have h6 := whredS_step h5 .beta; rsx at h6
  exact defeq_rw (WHRedS.defeq hE hΓ h6 (belowM_typed hE ht hmo (mS_typed hn ha))) (by rsx)
    (by simp only [belowRec]; rsx) (by rsx)

include hn in
theorem belowS_motNL {Γ : Ctx ζ ℓ 0 5} (hΓ : E[Γ] ⊢ ok) {l : Level ℓ}
    (hmo : E[Γ] ⊢ motNL ηN : motNM ηN l) (ha : E[Γ] ⊢ #3 : mN ηN) :
    E[Γ] ⊢ belowM ηBl l (motNL ηN) (mS ηN #3) ≡
      mPP ηPP l (m1 l) (.app (motNL ηN) #3) (belowRec ηPU ηPP ηN l (motNL ηN) #3) :
        .sort (m1 l) := by
  have h1 : E ⊢ belowM ηBl l (motNL ηN : Expr ζ ℓ 5) (mS ηN #3) ⤳*
      .app (.app ((E.get ηBl).defValue{![l]}.wkClosed) (motNL ηN)) (mS ηN #3) :=
    .single (.frame (K := .app _) (.frame (K := .app _) .delta))
  rw [hv] at h1
  have h2 := whredS_step h1 (.frame (K := .app _) .beta); rsx at h2
  have h3 := whredS_step h2 .beta; rsx at h3
  have h4 := whredS_step h3 .iota; rw [hn] at h4; rsx at h4
  have h5 := whredS_step h4 (.frame (K := .app _) .beta); rsx at h5
  have h6 := whredS_step h5 .beta; rsx at h6
  exact defeq_rw (WHRedS.defeq hE hΓ h6 (belowM_typed hE ht hmo (mS_typed hn ha)))
    (by rsx) (by simp only [belowRec]; rsx) (by rsx)

include hn in
/-- `N.below motive N.z` unfolds to `PUnit`, under `motive t F_1` (`N.brecOn.go`). -/
theorem belowZ_var {Γ : Ctx ζ ℓ 0 3} (hΓ : E[Γ] ⊢ ok) {l : Level ℓ}
    (hmo : E[Γ] ⊢ #0 : motNM ηN l) :
    E[Γ] ⊢ belowM ηBl l #0 (mZ ηN) ≡ mPU ηPU (m1 l) : .sort (m1 l) := by
  have h1 : E ⊢ belowM ηBl l (#0 : Expr ζ ℓ 3) (mZ ηN) ⤳*
      .app (.app ((E.get ηBl).defValue{![l]}.wkClosed) #0) (mZ ηN) :=
    .single (.frame (K := .app _) (.frame (K := .app _) .delta))
  rw [hv] at h1
  have h2 := whredS_step h1 (.frame (K := .app _) .beta); rsx at h2
  have h3 := whredS_step h2 .beta; rsx at h3
  have h4 := whredS_step h3 .iota; rw [hn] at h4; rsx at h4
  exact defeq_rw (WHRedS.defeq hE hΓ h4 (belowM_typed hE ht hmo (mZ_typed hn))) (by rsx)
    (by rsx) (by rsx)

include hn hpp in
/-- `N.below motive (N.s n) ≡ PProd (motive n) (N.below motive n)`, under `motive _ _ n _`. -/
theorem belowS_defeq_var {Γ : Ctx ζ ℓ 0 5} (hΓ : E[Γ] ⊢ ok) {l : Level ℓ}
    (hmo : E[Γ] ⊢ #0 : motNM ηN l) (ha : E[Γ] ⊢ #3 : mN ηN) :
    E[Γ] ⊢ belowM ηBl l #0 (mS ηN #3) ≡ mPP ηPP l (m1 l) (.app #0 #3) (belowM ηBl l #0 #3) :
      .sort (m1 l) := by
  have h := mPP_defeq hpp (appMotN_typed hn hmo ha) (belowRed_var hE ht hv hΓ hmo ha).symm
  rw [ppLevel_m1] at h
  exact (belowS_var hE hn ht hv hΓ hmo ha).trans h

include hn hpp in
/-- `N.below (fun m => N) (N.s k) ≡ PProd ((fun m => N) k) (N.below (fun m => N) k)`. -/
theorem belowS_defeq_motNL {Γ : Ctx ζ ℓ 0 5} (hΓ : E[Γ] ⊢ ok) {l : Level ℓ}
    (hmo : E[Γ] ⊢ motNL ηN : motNM ηN l) (ha : E[Γ] ⊢ #3 : mN ηN) :
    E[Γ] ⊢ belowM ηBl l (motNL ηN) (mS ηN #3) ≡
      mPP ηPP l (m1 l) (.app (motNL ηN) #3) (belowM ηBl l (motNL ηN) #3) : .sort (m1 l) := by
  have h := mPP_defeq hpp (appMotN_typed hn hmo ha) (belowRed_motNL hE ht hv hΓ hmo ha).symm
  rw [ppLevel_m1] at h
  exact (belowS_motNL hE hn ht hv hΓ hmo ha).trans h

end Below

end EraseProof.Test.NVS

namespace EraseProof.Test.NVS

open EraseProof.Test.NV1 (typed_of_eq var_of_get app_typed const_typed fin0_eq lu)
open EraseProof.Test.NVR (nSig nBlock mN mZ mS mN_typed mZ_typed mS_typed indN_typed recAllowedN
  appMotN_typed motN_typed)

/-- β on a λ at its type. -/
theorem beta_defeq {ζ : Sigs} {E : Env ζ} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} {t a : Expr ζ ℓ n}
    {e' T' : Expr ζ ℓ (n + 1)} {l₁ l₂ : Level ℓ} (ht : E[Γ] ⊢ t : .sort l₁)
    (hT' : E[Γ.snoc t] ⊢ T' : .sort l₂) (he' : E[Γ.snoc t] ⊢ e' : T') (ha : E[Γ] ⊢ a : t) :
    E[Γ] ⊢ .app (.lam t e') a ≡ e'.inst a : T'.inst a :=
  .beta ht hT' he' ha (hT'.inst_congr ha) (he'.inst_congr ha)

section CasesOnTyped
variable {ζ : Sigs} {E : Env ζ} {ηN : Head ζ (.inductive nSig)}

/-- `N.casesOn`'s binder context `motive t z s`. -/
def ΓCO (ηN : Head ζ (.inductive nSig)) : Ctx ζ 1 0 4 :=
  #t[motNM ηN lu, mN ηN, .app #0 (mZ ηN), .forallE (mN ηN) (.app #0 (mS ηN #3))]

theorem ΓCO_wf (hn : (E.get ηN).block = nBlock) : E[ΓCO ηN] ⊢ ok := by
  have h1 : E[(#t[motNM ηN lu] : Ctx ζ 1 0 1)] ⊢ ok := .snoc .nil ⟨_, motN_typed hn⟩
  have h2 : E[(#t[motNM ηN lu, mN ηN] : Ctx ζ 1 0 2)] ⊢ ok := .snoc h1 ⟨_, mN_typed hn⟩
  have hm2 : E[(#t[motNM ηN lu, mN ηN] : Ctx ζ 1 0 2)] ⊢ #0 : motNM ηN lu :=
    var_of_get h2 ⟨0, by decide⟩ (by rsx)
  have h3 : E[(#t[motNM ηN lu, mN ηN, .app #0 (mZ ηN)] : Ctx ζ 1 0 3)] ⊢ ok :=
    .snoc h2 ⟨_, appMotN_typed hn hm2 (mZ_typed hn)⟩
  have h4 : E[(#t[motNM ηN lu, mN ηN, .app #0 (mZ ηN), mN ηN] : Ctx ζ 1 0 4)] ⊢ ok :=
    .snoc h3 ⟨_, mN_typed hn⟩
  have hm4 : E[(#t[motNM ηN lu, mN ηN, .app #0 (mZ ηN), mN ηN] : Ctx ζ 1 0 4)] ⊢ #0 :
      motNM ηN lu := var_of_get h4 ⟨0, by decide⟩ (by rsx)
  have hv4 : E[(#t[motNM ηN lu, mN ηN, .app #0 (mZ ηN), mN ηN] : Ctx ζ 1 0 4)] ⊢ #3 :
      mN ηN := var_of_get h4 ⟨3, by decide⟩ (by rsx)
  have hs4 := appMotN_typed hn hm4 (mS_typed hn hv4)
  exact .snoc h3 ⟨_, .forallEDF (mN_typed hn) hs4 hs4⟩

theorem casesOnValM_typed (hn : (E.get ηN).block = nBlock) :
    E[.nil] ⊢ casesOnValM ηN : casesOnTyM ηN := by
  have hΓ := ΓCO_wf hn
  have hm : E[ΓCO ηN] ⊢ #0 : motNM ηN lu := var_of_get hΓ ⟨0, by decide⟩ (by rsx [ΓCO])
  have hbody : E[ΓCO ηN] ⊢ .recr ηN 0 Fin.elim0 lu Fin.elim0 (fun _ => #0) (minsCO ηN)
      Fin.elim0 #1 : .app #0 #1 := by
    have h := Defeq.recrDF (E := E) (Γ := ΓCO ηN) (η := ηN) (s := 0) (ls := Fin.elim0)
      (l := lu) (ps₁ := Fin.elim0) (ps₂ := Fin.elim0) (ms₁ := fun _ => #0) (ms₂ := fun _ => #0)
      (mins₁ := minsCO ηN) (mins₂ := minsCO ηN) (is₁ := Fin.elim0) (is₂ := Fin.elim0)
      (maj₁ := #1) (maj₂ := #1) (recAllowedN hn) (fun p => Fin.elim0 p) ?_ ?_
      (fun i => Fin.elim0 i) ?_ ?_
    · exact h
    · intro s; fin_cases s; rw [hn]; exact typed_of_eq hm (by rsimp [motNM, EraseProof.Test.NVR.motN])
    · intro s c; fin_cases s; fin_cases c <;> rw [hn]
      · exact typed_of_eq (var_of_get (T := .app #0 (mZ ηN)) hΓ ⟨2, by decide⟩ (by rsx [ΓCO]))
          (by rsimp [minsCO])
      · have h5 : E[(ΓCO ηN).snoc (mN ηN)] ⊢ ok := .snoc hΓ ⟨_, mN_typed hn⟩
        have hm5 : E[(ΓCO ηN).snoc (mN ηN)] ⊢ #0 : motNM ηN lu :=
          var_of_get h5 ⟨0, by decide⟩ (by rsx [ΓCO])
        have hv5 : E[(ΓCO ηN).snoc (mN ηN)] ⊢ #4 : mN ηN := var_of_get h5 ⟨4, by decide⟩ (by rsx)
        have hih := appMotN_typed hn hm5 hv5
        have h6 : E[((ΓCO ηN).snoc (mN ηN)).snoc (.app #0 #4)] ⊢ ok := .snoc h5 ⟨_, hih⟩
        have hs6 : E[((ΓCO ηN).snoc (mN ηN)).snoc (.app #0 #4)] ⊢ #3 :
            .forallE (mN ηN) (.app #0 (mS ηN #6)) := var_of_get h6 ⟨3, by decide⟩ (by rsx [ΓCO])
        have hb6 := typed_of_eq (app_typed hs6 (var_of_get (T := mN ηN) h6 ⟨4, by decide⟩ (by rsx)))
          (T' := .app #0 (mS ηN #4)) (by rsx)
        have hm6 : E[((ΓCO ηN).snoc (mN ηN)).snoc (.app #0 #4)] ⊢ #0 : motNM ηN lu :=
          var_of_get h6 ⟨0, by decide⟩ (by rsx [ΓCO])
        have hr6 := appMotN_typed hn hm6 (mS_typed hn (var_of_get h6 ⟨4, by decide⟩ (by rsx)))
        have hin : E[(ΓCO ηN).snoc (mN ηN)] ⊢ .lam (.app #0 #4) (.app #3 #4) :
            .forallE (.app #0 #4) (.app #0 (mS ηN #4)) := .lamDF hih hr6 hr6 hb6 hb6
        have hr5 := appMotN_typed hn hm5 (mS_typed hn hv5)
        exact typed_of_eq (.lamDF (mN_typed hn) (.forallEDF hih hr6 hr6) (.forallEDF hih hr6 hr6)
          hin hin) (by rsimp [minsCO])
    · exact var_of_get hΓ ⟨1, by decide⟩ (by rsx [ΓCO])
    · exact appMotN_typed hn hm (var_of_get hΓ ⟨1, by decide⟩ (by rsx [ΓCO]))
  exact Ctx.lam_congr (Γ := .nil) (Δ := ΓCO ηN) hΓ hbody

theorem casesOnTyM_isType (hn : (E.get ηN).block = nBlock) : E[.nil] ⊢ casesOnTyM ηN typ :=
  (casesOnValM_typed hn).regular

end CasesOnTyped

section BelowTyped
variable {ζ : Sigs} {E : Env ζ} {ηPU : Head ζ (.inductive puSig)} {ηPP : Head ζ (.inductive ppSig)}
  {ηN : Head ζ (.inductive nSig)}

/-- `(fun t => Sort (max 1 u)) a ≡ Sort (max 1 u)`. -/
theorem motBl_beta (hn : (E.get ηN).block = nBlock) {n : Nat} {Γ : Ctx ζ 1 0 n}
    {a : Expr ζ 1 n} (ha : E[Γ] ⊢ a : mN ηN) :
    E[Γ] ⊢ .app (.lam (mN ηN) (.sort m1M)) a ≡ .sort m1M : .sort (.succ m1M) :=
  defeq_rw (beta_defeq (mN_typed hn) .sortDF .sortDF ha) rfl (by rsx) (by rsx)

theorem belowValM_typed (hn : (E.get ηN).block = nBlock) (hpu : (E.get ηPU).block = puBlock)
    (hpp : (E.get ηPP).block = ppBlock) :
    E[.nil] ⊢ belowValM ηPU ηPP ηN : belowTyM ηN := by
  have h1 : E[(#t[motNM ηN lu] : Ctx ζ 1 0 1)] ⊢ ok := .snoc .nil ⟨_, motN_typed hn⟩
  have hΓ : E[(#t[motNM ηN lu, mN ηN] : Ctx ζ 1 0 2)] ⊢ ok := .snoc h1 ⟨_, mN_typed hn⟩
  have hmotL : E[(#t[motNM ηN lu, mN ηN] : Ctx ζ 1 0 2)] ⊢ .lam (mN ηN) (.sort m1M) :
      .forallE (mN ηN) (.sort (.succ m1M)) :=
    .lamDF (mN_typed hn) .sortDF .sortDF .sortDF .sortDF
  have hbody : E[(#t[motNM ηN lu, mN ηN] : Ctx ζ 1 0 2)] ⊢
      .recr ηN 0 Fin.elim0 (.succ m1M) Fin.elim0 (fun _ => .lam (mN ηN) (.sort m1M))
        (minsBl ηPU ηPP ηN) Fin.elim0 #1 : .app (.lam (mN ηN) (.sort m1M)) #1 := by
    have h := Defeq.recrDF (E := E) (Γ := #t[motNM ηN lu, mN ηN]) (η := ηN) (s := 0)
      (ls := Fin.elim0) (l := .succ m1M) (ps₁ := Fin.elim0) (ps₂ := Fin.elim0)
      (ms₁ := fun _ => .lam (mN ηN) (.sort m1M)) (ms₂ := fun _ => .lam (mN ηN) (.sort m1M))
      (mins₁ := minsBl ηPU ηPP ηN) (mins₂ := minsBl ηPU ηPP ηN) (is₁ := Fin.elim0)
      (is₂ := Fin.elim0) (maj₁ := #1) (maj₂ := #1) (recAllowedN hn) (fun p => Fin.elim0 p) ?_ ?_
      (fun i => Fin.elim0 i) ?_ ?_
    · exact h
    · intro s; fin_cases s; rw [hn]; exact typed_of_eq hmotL (by rsimp)
    · intro s c; fin_cases s; fin_cases c <;> rw [hn]
      · exact typed_of_eq (.defeqDF (motBl_beta hn (mZ_typed hn)).symm (mPU_typed hpu))
          (by rsimp [minsBl])
      · have h3 : E[(#t[motNM ηN lu, mN ηN, mN ηN] : Ctx ζ 1 0 3)] ⊢ ok :=
          .snoc hΓ ⟨_, mN_typed hn⟩
        have hv3 : E[(#t[motNM ηN lu, mN ηN, mN ηN] : Ctx ζ 1 0 3)] ⊢ #2 : mN ηN :=
          var_of_get h3 ⟨2, by decide⟩ (by rsx)
        have hβ3 := motBl_beta hn hv3
        have hβ3' := motBl_beta hn (mS_typed hn hv3)
        have h4 : E[(#t[motNM ηN lu, mN ηN, mN ηN, .sort m1M] : Ctx ζ 1 0 4)] ⊢ ok :=
          .snoc h3 ⟨_, .sortDF⟩
        have h4' : E[(#t[motNM ηN lu, mN ηN, mN ηN, .app (.lam (mN ηN) (.sort m1M)) #2] :
            Ctx ζ 1 0 4)] ⊢ ok := .snoc h3 ⟨_, hβ3.left⟩
        have hP : E[(#t[motNM ηN lu, mN ηN, mN ηN, .sort m1M] : Ctx ζ 1 0 4)] ⊢
            mPP ηPP lu m1M (.app #0 #2) #3 : .sort m1M := by
          have := mPP_typed hpp
            (appMotN_typed hn (var_of_get (T := motNM ηN lu) h4 ⟨0, by decide⟩ (by rsx))
              (var_of_get h4 ⟨2, by decide⟩ (by rsx)))
            (var_of_get (T := .sort m1M) h4 ⟨3, by decide⟩ (by rsx))
          rwa [ppLevel_m1] at this
        have hin : E[(#t[motNM ηN lu, mN ηN, mN ηN] : Ctx ζ 1 0 3)] ⊢
            .lam (.sort m1M) (mPP ηPP lu m1M (.app #0 #2) #3) :
              .forallE (.sort m1M) (.sort m1M) := .lamDF .sortDF .sortDF .sortDF hP hP
        have hinTy : E[(#t[motNM ηN lu, mN ηN, mN ηN] : Ctx ζ 1 0 3)] ⊢
            .forallE (.app (.lam (mN ηN) (.sort m1M)) #2)
              (.app (.lam (mN ηN) (.sort m1M)) (mS ηN #2)) ≡
            .forallE (.sort m1M) (.sort m1M) : .sort (.imax (.succ m1M) (.succ m1M)) :=
          .forallEDF hβ3 (motBl_beta hn (mS_typed hn (var_of_get h4' ⟨2, by decide⟩ (by rsx))))
            (motBl_beta hn (mS_typed hn (var_of_get h4 ⟨2, by decide⟩ (by rsx))))
        have hmin : E[(#t[motNM ηN lu, mN ηN] : Ctx ζ 1 0 2)] ⊢
            .lam (mN ηN) (.lam (.sort m1M) (mPP ηPP lu m1M (.app #0 #2) #3)) :
              .forallE (mN ηN) (.forallE (.sort m1M) (.sort m1M)) :=
          .lamDF (mN_typed hn) hinTy.right hinTy.right hin hin
        have hTy : E[(#t[motNM ηN lu, mN ηN] : Ctx ζ 1 0 2)] ⊢
            .forallE (mN ηN) (.forallE (.app (.lam (mN ηN) (.sort m1M)) #2)
              (.app (.lam (mN ηN) (.sort m1M)) (mS ηN #2))) ≡
            .forallE (mN ηN) (.forallE (.sort m1M) (.sort m1M)) : _ :=
          .forallEDF (mN_typed hn) hinTy hinTy
        exact typed_of_eq (.defeqDF hTy.symm hmin) (by rsimp [minsBl])
    · exact var_of_get hΓ ⟨1, by decide⟩ (by rsx)
    · exact .appDF (mN_typed hn) .sortDF hmotL (var_of_get hΓ ⟨1, by decide⟩ (by rsx)) .sortDF
  have hbody' := Defeq.defeqDF (motBl_beta hn (var_of_get hΓ ⟨1, by decide⟩ (by rsx))) hbody
  exact Ctx.lam_congr (Γ := .nil) (Δ := #t[motNM ηN lu, mN ηN]) hΓ hbody'

theorem belowTyM_isType (hn : (E.get ηN).block = nBlock) (hpu : (E.get ηPU).block = puBlock)
    (hpp : (E.get ηPP).block = ppBlock) : E[.nil] ⊢ belowTyM ηN typ :=
  (belowValM_typed (ηPU := ηPU) (ηPP := ηPP) hn hpu hpp).regular

end BelowTyped

/-! ## `N.brecOn.go` and `N.brecOn` -/

section GoDefs
variable {ζ : Sigs} (ηPU : Head ζ (.inductive puSig)) (ηPP : Head ζ (.inductive ppSig))
  (ηN : Head ζ (.inductive nSig)) (ηBl : Head ζ (.const .def 1))

/-- `(t : N) → N.below motive t → motive t`, under `motive t`. -/
def F1TyM : Expr ζ 1 2 := .forallE (mN ηN) (.forallE (belowM ηBl lu #0 #2) (.app #0 #2))

/-- `PProd (motive a) (N.below motive a)`, the motive `mo`. -/
def pairM {n : Nat} (mo a : Expr ζ 1 n) : Expr ζ 1 n :=
  mPP ηPP lu m1M (.app mo a) (belowM ηBl lu mo a)

/-- The motive `fun t => PProd (motive t) (N.below motive t)` of `N.brecOn.go`'s recursor, at depth
`n + 1` (the motive the variable `0`). -/
def motGo {n : Nat} : Expr ζ 1 (n + 1) :=
  .lam (mN ηN) (pairM ηPP ηBl (.var ⟨0, by omega⟩) (.var (Fin.last (n + 1))))

/-- `{motive : N → Sort u} → (t : N) → (F_1 : (t : N) → N.below motive t → motive t) →
PProd (motive t) (N.below motive t)` -/
def goTyM : Expr ζ 1 0 :=
  .forallE (motNM ηN lu) (.forallE (mN ηN) (.forallE (F1TyM ηN ηBl) (pairM ηPP ηBl #0 #1)))

/-- The minor premises `⟨F_1 N.z PUnit.unit, PUnit.unit⟩` and
`fun n n_ih => ⟨F_1 (N.s n) n_ih, n_ih⟩` of `N.brecOn.go`'s recursor. -/
def minsGo : (t : Fin 1) → Fin (nSig.nctors t) → Expr ζ 1 3 :=
  fun _ c => if c.val = 0 then
    mPPmk ηPP lu m1M (.app #0 (mZ ηN)) (mPU ηPU m1M) (.app (.app #2 (mZ ηN)) (mPUu ηPU m1M))
      (mPUu ηPU m1M)
  else .lam (mN ηN) (.lam (pairM ηPP ηBl #0 #3)
    (mPPmk ηPP lu m1M (.app #0 (mS ηN #3)) (pairM ηPP ηBl #0 #3) (.app (.app #2 (mS ηN #3)) #4)
      #4))

/-- `fun {motive} t F_1 => @N.rec.{max 1 u} (fun t => PProd (motive t) (N.below motive t))
⟨F_1 N.z PUnit.unit, PUnit.unit⟩ (fun n n_ih => ⟨F_1 (N.s n) n_ih, n_ih⟩) t` -/
def goValM : Expr ζ 1 0 :=
  .lam (motNM ηN lu) (.lam (mN ηN) (.lam (F1TyM ηN ηBl)
    (.recr ηN 0 Fin.elim0 m1M Fin.elim0 (fun _ => motGo ηPP ηN ηBl) (minsGo ηPU ηPP ηN ηBl)
      Fin.elim0 #1)))

end GoDefs

section GoTyped
variable {ζ : Sigs} {E : Env ζ} {ηPU : Head ζ (.inductive puSig)} {ηPP : Head ζ (.inductive ppSig)}
  {ηN : Head ζ (.inductive nSig)} {ηBl : Head ζ (.const .def 1)}
  (hE : EnvWF E) (hn : (E.get ηN).block = nBlock) (hpu : (E.get ηPU).block = puBlock)
  (hpp : (E.get ηPP).block = ppBlock) (ht : (E.get ηBl).constType = belowTyM ηN)
  (hv : (E.get ηBl).defValue = belowValM ηPU ηPP ηN)

include hE hn hpp ht in
theorem pairM_typed {n : Nat} {Γ : Ctx ζ 1 0 n} {mo a : Expr ζ 1 n}
    (hmo : E[Γ] ⊢ mo : motNM ηN lu) (ha : E[Γ] ⊢ a : mN ηN) :
    E[Γ] ⊢ pairM ηPP ηBl mo a : .sort m1M := by
  have h := mPP_typed hpp (appMotN_typed hn hmo ha) (belowM_typed hE ht hmo ha)
  rwa [ppLevel_m1] at h

include hE hn hpp ht in
/-- `(fun t => PProd (motive t) (N.below motive t)) a ≡ PProd (motive a) (N.below motive a)`. -/
theorem motGo_beta {n : Nat} {Γ : Ctx ζ 1 0 (n + 1)} (hΓ : E[Γ] ⊢ ok) {a : Expr ζ 1 (n + 1)}
    (hmo : E[Γ] ⊢ .var ⟨0, by omega⟩ : motNM ηN lu) (ha : E[Γ] ⊢ a : mN ηN) :
    E[Γ] ⊢ .app (motGo ηPP ηN ηBl) a ≡ pairM ηPP ηBl (.var ⟨0, by omega⟩) a : .sort m1M := by
  have hΓ' : E[Γ.snoc (mN ηN)] ⊢ ok := .snoc hΓ ⟨_, mN_typed hn⟩
  have hmo' : E[Γ.snoc (mN ηN)] ⊢ .var ⟨0, by omega⟩ : motNM ηN lu := by
    have h := hmo.wk (mN ηN)
    exact defeq_rw h (by rsx) (by rsx) (by rsx)
  have hv : E[Γ.snoc (mN ηN)] ⊢ .var (Fin.last (n + 1)) : mN ηN :=
    var_of_get hΓ' _ (by rw [Ctx.get_last]; rsx)
  exact defeq_rw (beta_defeq (mN_typed hn) .sortDF (pairM_typed hE hn hpp ht hmo' hv) ha) rfl
    (by rsx [pairM]) (by rsx)

/-- `N.brecOn.go`'s and `N.brecOn`'s binder context `motive t F_1`. -/
def ΓG (ηN : Head ζ (.inductive nSig)) (ηBl : Head ζ (.const .def 1)) : Ctx ζ 1 0 3 :=
  #t[motNM ηN lu, mN ηN, F1TyM ηN ηBl]

include hE hn ht in
theorem ΓG_wf : E[ΓG ηN ηBl] ⊢ ok := by
  have h1 : E[(#t[motNM ηN lu] : Ctx ζ 1 0 1)] ⊢ ok := .snoc .nil ⟨_, motN_typed hn⟩
  have h2 : E[(#t[motNM ηN lu, mN ηN] : Ctx ζ 1 0 2)] ⊢ ok := .snoc h1 ⟨_, mN_typed hn⟩
  have h3 : E[(#t[motNM ηN lu, mN ηN, mN ηN] : Ctx ζ 1 0 3)] ⊢ ok := .snoc h2 ⟨_, mN_typed hn⟩
  have hm3 : E[(#t[motNM ηN lu, mN ηN, mN ηN] : Ctx ζ 1 0 3)] ⊢ #0 : motNM ηN lu :=
    var_of_get h3 ⟨0, by decide⟩ (by rsx)
  have hv3 : E[(#t[motNM ηN lu, mN ηN, mN ηN] : Ctx ζ 1 0 3)] ⊢ #2 : mN ηN :=
    var_of_get h3 ⟨2, by decide⟩ (by rsx)
  have hb3 := belowM_typed hE ht hm3 hv3
  have h4 : E[(#t[motNM ηN lu, mN ηN, mN ηN, belowM ηBl lu #0 #2] : Ctx ζ 1 0 4)] ⊢ ok :=
    .snoc h3 ⟨_, hb3⟩
  have hr4 := appMotN_typed hn (var_of_get (T := motNM ηN lu) h4 ⟨0, by decide⟩ (by rsx))
    (var_of_get h4 ⟨2, by decide⟩ (by rsx))
  have hF : E[(#t[motNM ηN lu, mN ηN] : Ctx ζ 1 0 2)] ⊢ F1TyM ηN ηBl : _ :=
    .forallEDF (mN_typed hn) (.forallEDF hb3 hr4 hr4) (.forallEDF hb3 hr4 hr4)
  exact .snoc h2 ⟨_, hF⟩

include hE hn hpu hpp ht hv in
theorem goValM_typed : E[.nil] ⊢ goValM ηPU ηPP ηN ηBl : goTyM ηPP ηN ηBl := by
  have hΓ := ΓG_wf hE hn ht (ηBl := ηBl)
  have hm : E[ΓG ηN ηBl] ⊢ #0 : motNM ηN lu := var_of_get hΓ ⟨0, by decide⟩ (by rsx [ΓG])
  have ht1 : E[ΓG ηN ηBl] ⊢ #1 : mN ηN := var_of_get hΓ ⟨1, by decide⟩ (by rsx [ΓG])
  have hF : E[ΓG ηN ηBl] ⊢ #2 : .forallE (mN ηN) (.forallE (belowM ηBl lu #0 #3) (.app #0 #3)) :=
    var_of_get hΓ ⟨2, by decide⟩ (by rsx [ΓG, F1TyM])
  -- the motive
  have h4 : E[(ΓG ηN ηBl).snoc (mN ηN)] ⊢ ok := .snoc hΓ ⟨_, mN_typed hn⟩
  have hm4 : E[(ΓG ηN ηBl).snoc (mN ηN)] ⊢ #0 : motNM ηN lu :=
    var_of_get h4 ⟨0, by decide⟩ (by rsx [ΓG])
  have hv4 : E[(ΓG ηN ηBl).snoc (mN ηN)] ⊢ #3 : mN ηN := var_of_get h4 ⟨3, by decide⟩ (by rsx)
  have hP4 := pairM_typed hE hn hpp ht hm4 hv4
  have hmot : E[ΓG ηN ηBl] ⊢ motGo ηPP ηN ηBl : .forallE (mN ηN) (.sort m1M) :=
    .lamDF (mN_typed hn) .sortDF .sortDF hP4 hP4
  have hbody : E[ΓG ηN ηBl] ⊢ .recr ηN 0 Fin.elim0 m1M Fin.elim0 (fun _ => motGo ηPP ηN ηBl)
      (minsGo ηPU ηPP ηN ηBl) Fin.elim0 #1 : .app (motGo ηPP ηN ηBl) #1 := by
    have h := Defeq.recrDF (E := E) (Γ := ΓG ηN ηBl) (η := ηN) (s := 0) (ls := Fin.elim0)
      (l := m1M) (ps₁ := Fin.elim0) (ps₂ := Fin.elim0) (ms₁ := fun _ => motGo ηPP ηN ηBl)
      (ms₂ := fun _ => motGo ηPP ηN ηBl) (mins₁ := minsGo ηPU ηPP ηN ηBl)
      (mins₂ := minsGo ηPU ηPP ηN ηBl) (is₁ := Fin.elim0) (is₂ := Fin.elim0) (maj₁ := #1)
      (maj₂ := #1) (recAllowedN hn) (fun p => Fin.elim0 p) ?_ ?_ (fun i => Fin.elim0 i) ?_ ?_
    · exact h
    · intro s; fin_cases s; rw [hn]; exact typed_of_eq hmot (by rsimp)
    · intro s c; fin_cases s; fin_cases c <;> rw [hn]
      · -- `⟨F_1 N.z PUnit.unit, PUnit.unit⟩ : motive' N.z`
        have hZ := belowZ_var hE hn ht hv hΓ hm
        have hu : E[ΓG ηN ηBl] ⊢ mPUu ηPU m1M : belowM ηBl lu #0 (mZ ηN) :=
          .defeqDF hZ.symm (mPUu_typed hpu)
        have hF1 := typed_of_eq (app_typed hF (mZ_typed hn))
          (T' := .forallE (belowM ηBl lu #0 (mZ ηN)) (.app #0 (mZ ηN))) (by rsx)
        have hFz := typed_of_eq (app_typed hF1 hu) (T' := .app #0 (mZ ηN)) (by rsx)
        have hmk := mPPmk_typed hpp (appMotN_typed hn hm (mZ_typed hn)) (mPU_typed (l := m1M) hpu)
          hFz (mPUu_typed hpu)
        have hTy : E[ΓG ηN ηBl] ⊢ .app (motGo ηPP ηN ηBl) (mZ ηN) ≡
            mPP ηPP lu m1M (.app #0 (mZ ηN)) (mPU ηPU m1M) : .sort m1M := by
          have h := mPP_defeq hpp (appMotN_typed hn hm (mZ_typed hn)) hZ
          rw [ppLevel_m1] at h
          exact (motGo_beta hE hn hpp ht hΓ hm (mZ_typed hn)).trans h
        exact typed_of_eq (.defeqDF hTy.symm hmk) (by rsimp [minsGo, motGo])
      · -- `fun n n_ih => ⟨F_1 (N.s n) n_ih, n_ih⟩ : (n : N) → motive' n → motive' (N.s n)`
        have hP4' : E[(ΓG ηN ηBl).snoc (mN ηN)] ⊢ pairM ηPP ηBl #0 #3 : .sort m1M := hP4
        have hβ4 := motGo_beta hE hn hpp ht h4 hm4 hv4
        have hctx : ∀ {A : Expr ζ 1 4}, E[(ΓG ηN ηBl).snoc (mN ηN)] ⊢ A : .sort m1M →
            E[((ΓG ηN ηBl).snoc (mN ηN)).snoc A] ⊢ .app (motGo ηPP ηN ηBl) (mS ηN #3) ≡
              mPP ηPP lu m1M (.app #0 (mS ηN #3)) (pairM ηPP ηBl #0 #3) : .sort m1M := by
          intro A hA
          have h5 : E[((ΓG ηN ηBl).snoc (mN ηN)).snoc A] ⊢ ok := .snoc h4 ⟨_, hA⟩
          have hm5 : E[((ΓG ηN ηBl).snoc (mN ηN)).snoc A] ⊢ #0 : motNM ηN lu :=
            var_of_get h5 ⟨0, by decide⟩ (by rsx [ΓG])
          have hv5 : E[((ΓG ηN ηBl).snoc (mN ηN)).snoc A] ⊢ #3 : mN ηN :=
            var_of_get h5 ⟨3, by decide⟩ (by rsx)
          have hS := belowS_defeq_var hE hn hpp ht hv h5 hm5 hv5
          have h := mPP_defeq hpp (appMotN_typed hn hm5 (mS_typed hn hv5)) hS
          rw [ppLevel_m1] at h
          exact (motGo_beta hE hn hpp ht h5 hm5 (mS_typed hn hv5)).trans h
        have h5 : E[((ΓG ηN ηBl).snoc (mN ηN)).snoc (pairM ηPP ηBl #0 #3)] ⊢ ok :=
          .snoc h4 ⟨_, hP4'⟩
        have hm5 : E[((ΓG ηN ηBl).snoc (mN ηN)).snoc (pairM ηPP ηBl #0 #3)] ⊢ #0 :
            motNM ηN lu := var_of_get h5 ⟨0, by decide⟩ (by rsx [ΓG])
        have hv5 : E[((ΓG ηN ηBl).snoc (mN ηN)).snoc (pairM ηPP ηBl #0 #3)] ⊢ #3 : mN ηN :=
          var_of_get h5 ⟨3, by decide⟩ (by rsx)
        have hih : E[((ΓG ηN ηBl).snoc (mN ηN)).snoc (pairM ηPP ηBl #0 #3)] ⊢ #4 :
            pairM ηPP ηBl #0 #3 := var_of_get h5 ⟨4, by decide⟩ (by rsx [pairM])
        have hS := belowS_defeq_var hE hn hpp ht hv h5 hm5 hv5
        have hF5 : E[((ΓG ηN ηBl).snoc (mN ηN)).snoc (pairM ηPP ηBl #0 #3)] ⊢ #2 :
            .forallE (mN ηN) (.forallE (belowM ηBl lu #0 #5) (.app #0 #5)) :=
          var_of_get h5 ⟨2, by decide⟩ (by rsx [ΓG, F1TyM])
        have hF1 := typed_of_eq (app_typed hF5 (mS_typed hn hv5))
          (T' := .forallE (belowM ηBl lu #0 (mS ηN #3)) (.app #0 (mS ηN #3))) (by rsx)
        have hFs := typed_of_eq (app_typed hF1 (.defeqDF hS.symm (typed_of_eq hih (by rsx [pairM]))))
          (T' := .app #0 (mS ηN #3)) (by rsx)
        have hmk := mPPmk_typed hpp (appMotN_typed hn hm5 (mS_typed hn hv5)) (pairM_typed hE hn hpp ht hm5 hv5)
          hFs hih
        have hr5 := mPP_typed hpp (appMotN_typed hn hm5 (mS_typed hn hv5))
          (pairM_typed hE hn hpp ht hm5 hv5)
        rw [ppLevel_m1] at hr5
        have hin : E[(ΓG ηN ηBl).snoc (mN ηN)] ⊢
            .lam (pairM ηPP ηBl #0 #3) (mPPmk ηPP lu m1M (.app #0 (mS ηN #3))
              (pairM ηPP ηBl #0 #3) (.app (.app #2 (mS ηN #3)) #4) #4) :
            .forallE (pairM ηPP ηBl #0 #3) (mPP ηPP lu m1M (.app #0 (mS ηN #3))
              (pairM ηPP ηBl #0 #3)) :=
          .lamDF hP4' hr5 hr5 hmk hmk
        have hinTy : E[(ΓG ηN ηBl).snoc (mN ηN)] ⊢
            .forallE (.app (motGo ηPP ηN ηBl) #3) (.app (motGo ηPP ηN ηBl) (mS ηN #3)) ≡
            .forallE (pairM ηPP ηBl #0 #3) (mPP ηPP lu m1M (.app #0 (mS ηN #3))
              (pairM ηPP ηBl #0 #3)) : .sort (.imax m1M m1M) :=
          .forallEDF hβ4 (hctx hβ4.left) (hctx hP4')
        have hTy : E[ΓG ηN ηBl] ⊢
            .forallE (mN ηN) (.forallE (.app (motGo ηPP ηN ηBl) #3)
              (.app (motGo ηPP ηN ηBl) (mS ηN #3))) ≡
            .forallE (mN ηN) (.forallE (pairM ηPP ηBl #0 #3) (mPP ηPP lu m1M
              (.app #0 (mS ηN #3)) (pairM ηPP ηBl #0 #3))) : _ :=
          .forallEDF (mN_typed hn) hinTy hinTy
        exact typed_of_eq (.defeqDF hTy.symm (.lamDF (mN_typed hn) hinTy.right hinTy.right hin hin))
          (by rsimp [minsGo, motGo, pairM, belowM, mPP, Expr.rename, Ren.wkFrom, Ren.comp])
    · exact ht1
    · exact .appDF (mN_typed hn) .sortDF hmot ht1 .sortDF
  have hbody' := Defeq.defeqDF (motGo_beta hE hn hpp ht hΓ hm ht1) hbody
  exact Ctx.lam_congr (Γ := .nil) (Δ := ΓG ηN ηBl) hΓ hbody'

include hE hn hpu hpp ht hv in
theorem goTyM_isType : E[.nil] ⊢ goTyM ηPP ηN ηBl typ :=
  (goValM_typed hE hn hpu hpp ht hv).regular

end GoTyped

section BrecOn
variable {ζ : Sigs} (ηPP : Head ζ (.inductive ppSig)) (ηN : Head ζ (.inductive nSig))
  (ηBl : Head ζ (.const .def 1)) (ηGo : Head ζ (.const .def 1))

/-- `{motive : N → Sort u} → (t : N) → (F_1 : (t : N) → N.below motive t → motive t) → motive t` -/
def brecOnTyM : Expr ζ 1 0 :=
  .forallE (motNM ηN lu) (.forallE (mN ηN) (.forallE (F1TyM ηN ηBl) (.app #0 #1)))

/-- `N.brecOn.go motive t F_1`. -/
def goApp : Expr ζ 1 3 := .app (.app (.app (.const ηGo ![lu]) #0) #1) #2

/-- The first projection `maj.1` of `maj : PProd (motive t) (N.below motive t)`, as Metalean's
structure projection (`Inductive.IsStructure.projTerm`) computes it: the recursor of `PProd` into
`motive t` whose minor returns the first field. -/
def projFstM (maj : Expr ζ 1 3) : Expr ζ 1 3 :=
  .recr ηPP 0 ![lu, m1M] lu ![.app #0 #1, belowM ηBl lu #0 #1]
    (fun _ => .lam (mPP ηPP lu m1M (.app #0 #1) (belowM ηBl lu #0 #1)) (.app #0 #1))
    (fun _ _ => .lam (.app #0 #1) (.lam (belowM ηBl lu #0 #1) #3)) Fin.elim0 maj

/-- `fun {motive} t F_1 => (N.brecOn.go motive t F_1).1` -/
def brecOnValM : Expr ζ 1 0 :=
  .lam (motNM ηN lu) (.lam (mN ηN) (.lam (F1TyM ηN ηBl) (projFstM ηPP ηBl (goApp ηGo))))

end BrecOn

theorem projTerm_eqFst {ζ : Sigs} {ηPP : Head ζ (.inductive ppSig)} {ηBl : Head ζ (.const .def 1)}
    {I : Inductive ζ ppSig} (h : I.IsStructure 0 0) (hI : I = ppBlock) (maj : Expr ζ 1 3) :
    h.projTerm ηPP ![lu, m1M] ![.app #0 #1, belowM ηBl lu #0 #1] ⟨0, by decide⟩ maj =
      projFstM ηPP ηBl maj := by
  subst hI
  rw [Inductive.IsStructure.projTerm_eq_recr]
  simp only [projFstM]
  congr 1
  case e_ms =>
    funext t; fin_cases t
    delta Inductive.IsStructure.projectionMotives
    rsx [Inductive.IsStructure.projTypeWith, Inductive.motiveTele, Inductive.indexTele, Ctx.substN]
  case e_mins =>
    funext t c; fin_cases t; fin_cases c
    delta Inductive.IsStructure.projectionCases
    rsx [Inductive.caseTele, CtorSig.caseOrdinary,
      CtorSig.fieldOrdinary, Ctor.fieldTele, Ctor.ordinaryFieldTele, Ctor.ordinaryTeleAux,
      Ctor.ihTele, Ctx.ofTypes, Ctor.recursiveFieldTeleAux, Expr.boundVars,
      Ctor.ordinaryFieldTeleAux, Tele.foldr, Ctx.substN, Subst.liftN]

theorem projType_eqFst {ζ : Sigs} {ηPP : Head ζ (.inductive ppSig)} {ηBl : Head ζ (.const .def 1)}
    {I : Inductive ζ ppSig} (h : I.IsStructure 0 0) (hI : I = ppBlock) (maj : Expr ζ 1 3) :
    h.projType ηPP ![lu, m1M] ![.app #0 #1, belowM ηBl lu #0 #1] ⟨0, by decide⟩ maj =
      .app #0 #1 := by
  subst hI
  rw [Inductive.IsStructure.projType, Inductive.IsStructure.projection]
  simp only [Inductive.IsStructure.projTypeWith]
  rsx

section BrecOnTyped
variable {ζ : Sigs} {E : Env ζ} {ηPU : Head ζ (.inductive puSig)} {ηPP : Head ζ (.inductive ppSig)}
  {ηN : Head ζ (.inductive nSig)} {ηBl : Head ζ (.const .def 1)} {ηGo : Head ζ (.const .def 1)}
  (hE : EnvWF E) (hn : (E.get ηN).block = nBlock) (hpp : (E.get ηPP).block = ppBlock)
  (ht : (E.get ηBl).constType = belowTyM ηN) (hgt : (E.get ηGo).constType = goTyM ηPP ηN ηBl)
include hE hn hpp ht hgt

/-- `N.brecOn.go motive t F_1 : PProd (motive t) (N.below motive t)`. -/
theorem goApp_typed : E[ΓG ηN ηBl] ⊢ goApp ηGo : pairM ηPP ηBl #0 #1 := by
  have hΓ := ΓG_wf hE hn ht (ηBl := ηBl)
  have hm : E[ΓG ηN ηBl] ⊢ #0 : motNM ηN lu := var_of_get hΓ ⟨0, by decide⟩ (by rsx [ΓG])
  have ht1 : E[ΓG ηN ηBl] ⊢ #1 : mN ηN := var_of_get hΓ ⟨1, by decide⟩ (by rsx [ΓG])
  have hF : E[ΓG ηN ηBl] ⊢ #2 : .forallE (mN ηN) (.forallE (belowM ηBl lu #0 #3) (.app #0 #3)) :=
    var_of_get hΓ ⟨2, by decide⟩ (by rsx [ΓG, F1TyM])
  have h0 : E[ΓG ηN ηBl] ⊢ .const ηGo ![lu] :
      .forallE (motNM ηN lu) (.forallE (mN ηN) (.forallE
        (.forallE (mN ηN) (.forallE (belowM ηBl lu #3 #5) (.app #3 #5))) (pairM ηPP ηBl #3 #4))) :=
    const_typed hE ηGo ![lu] (by rw [hgt]; rsx [goTyM, F1TyM, pairM])
  have h1 := typed_of_eq (app_typed h0 hm) (T' := .forallE (mN ηN) (.forallE
    (.forallE (mN ηN) (.forallE (belowM ηBl lu #0 #4) (.app #0 #4))) (pairM ηPP ηBl #0 #3)))
    (by rsx [pairM])
  have h2 := typed_of_eq (app_typed h1 ht1) (T' := .forallE
    (.forallE (mN ηN) (.forallE (belowM ηBl lu #0 #3) (.app #0 #3))) (pairM ηPP ηBl #0 #1))
    (by rsx [pairM])
  exact typed_of_eq (app_typed h2 hF) (by rsx [pairM])

theorem brecOnValM_typed : E[.nil] ⊢ brecOnValM ηPP ηN ηBl ηGo : brecOnTyM ηN ηBl := by
  have hΓ := ΓG_wf hE hn ht (ηBl := ηBl)
  have hm : E[ΓG ηN ηBl] ⊢ #0 : motNM ηN lu := var_of_get hΓ ⟨0, by decide⟩ (by rsx [ΓG])
  have ht1 : E[ΓG ηN ηBl] ⊢ #1 : mN ηN := var_of_get hΓ ⟨1, by decide⟩ (by rsx [ΓG])
  have hst : (E.get ηPP).block.IsStructure 0 0 := hpp ▸ ppStruct
  have hB : InductiveWF E (E.get ηPP).block := (hE.entryWF ηPP).block
  have hps := ppParams hpp (appMotN_typed hn hm ht1) (belowM_typed hE ht hm ht1)
  have hmaj : E[ΓG ηN ηBl] ⊢ goApp ηGo : .ind ηPP 0 ![lu, m1M]
      ![.app #0 #1, belowM ηBl lu #0 #1] hst.indices := by
    have h := goApp_typed hE hn hpp ht hgt (ηGo := ηGo)
    rw [← hst.indices_eq Fin.elim0]
    exact h
  have h := hst.projTerm_hasType hB ⟨0, by decide⟩ hΓ hps hmaj
  rw [projTerm_eqFst hst hpp, projType_eqFst hst hpp] at h
  exact Ctx.lam_congr (Γ := .nil) (Δ := ΓG ηN ηBl) hΓ h

theorem brecOnTyM_isType : E[.nil] ⊢ brecOnTyM ηN ηBl typ :=
  (brecOnValM_typed hE hn hpp ht hgt (ηGo := ηGo)).regular

end BrecOnTyped

end EraseProof.Test.NVS
