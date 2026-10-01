import EraseProof.Target
import EraseProof.Typing.Basic
import EraseProof.Erasability.Eval
import EraseProof.Source.Restrict

/-!
# The erasure relation

`Erases` relates a Lean term of the fragment, under a lean4lean context, to a λ□ term: MetaRocq's
`erases` (`MR E/Extract.v:88`) on the fragment's term constructors. Its parameters are the atom
constants `ac`, which erase only to `□`, and the admissible targets `rc` of recursive constants,
which the λ□ environment stores as fixpoints (`RecIn`). This module proves its basic properties:
the erasure of a translated term has no loose index beyond the context (`Erases.closed`); the
relation is monotone in `rc` (`Erases.mono_rc`), and `RecIn` survives fresh growth of the λ□
environment (`RecIn.ext`); it reads `ac` only at the term's constants (`Erases.congr_ac`); and an
erasure of an application is `□` or an application of erasures (`Erases.app_inv`).
-/

open Lean Lean4Lean Erasure

namespace EraseProof

/-- `lenv'` adds declarations with fresh kernames in front of `lenv` (how the traversal's state
grows). Reference: `extends_prefix` (`MR E/EGlobalEnv.v:189`) with every added kername
`fresh_global` (`:191`) in `lenv`, a freshness that MetaRocq keeps in `wf_glob`
(`MR E/EWellformed.v:223`); as `MR E/EDeps.v:492 erases_deps_cons` uses it. -/
def LenvExt (lenv lenv' : GlobalDeclarations) : Prop :=
  ∃ new, lenv' = new ++ lenv ∧ ∀ kn ∈ new.map (·.1), lenv.find? (·.1 == kn) = none

/-- Admissible targets of a recursive constant: the fixpoint the λ□ environment stores for it.
Reference: none (Lean's environment-level recursion, DV-7). -/
def RecIn (lenv : GlobalDeclarations) (c : Name) (t : LBTerm) : Prop :=
  ∃ defs i, t = .fix defs i ∧ lookupConst lenv (toKername c) = some ⟨some (.fix defs i)⟩

/-- The erasure relation on the fragment. `ac` marks the atom constants, which erase only to `□`
(like `tInd`, which has no rule, and constructors of propositional inductives); `rc` gives the
admissible targets of recursive constants. Reference: `MR E/Extract.v:88 erases`; MC §7.3,
Fig. 18; Let. Def. 3 and Def. 10 (◀, weak closed case). -/
inductive Erases (venv : VEnv) (Us : List Name) (ac : Name → Bool) (rc : Name → LBTerm → Prop) :
    VLCtx → Expr → LBTerm → Prop
  /-- `erases_tRel` (`MR E/Extract.v:89`). -/
  | bvar : Erases venv Us ac rc Δ (.bvar i) (.bvar i)
  /-- `erases_tVar` (`MR E/Extract.v:90`), for the traversal's free variables (DV-13). -/
  | fvar : Erases venv Us ac rc Δ (.fvar x) (.fvar x)
  /-- `erases_tLambda` (`MR E/Extract.v:93`); Let. Def. 3 (lam). -/
  | lam : TrS venv Us Δ A A' → Erases venv Us ac rc ((none, .vlam A') :: Δ) b b' →
      Erases venv Us ac rc Δ (.lam n A b bi) (.lambda (binderNameOf n) b')
  /-- `erases_tLetIn` (`MR E/Extract.v:96`); Let. Def. 3 (let). -/
  | letE : TrS venv Us Δ T T' → TrS venv Us Δ v v₀ → Erases venv Us ac rc Δ v v' →
      Erases venv Us ac rc ((none, .vlet T' v₀) :: Δ) b b' →
      Erases venv Us ac rc Δ (.letE n T v b nd) (.letIn (binderNameOf n) v' b')
  /-- `erases_tApp` (`MR E/Extract.v:101`); Let. Def. 3 (app). -/
  | app : Erases venv Us ac rc Δ f f' → Erases venv Us ac rc Δ a a' →
      Erases venv Us ac rc Δ (.app f a) (.app f' a')
  /-- `erases_tConst` (`MR E/Extract.v:104`), for non-atoms (DV-11). -/
  | const : ac c = false → Erases venv Us ac rc Δ (.const c us) (.const (toKername c))
  /-- A recursive constant erases to its stored `tFix` (DV-7). -/
  | constRec : ac c = false → rc c t → Erases venv Us ac rc Δ (.const c us) t
  /-- Metadata is transparent (Lean syntax). -/
  | mdata : Erases venv Us ac rc Δ e e' → Erases venv Us ac rc Δ (.mdata d e) e'
  /-- `erases_box` (`MR E/Extract.v:140`); Let. Def. 3 (□). -/
  | box : ErasableS venv Us Δ e → Erases venv Us ac rc Δ e .box

/-- The targets of `rc` are closed (so substitution leaves them unchanged). Reference: `closed_env`
(`MR E/EGlobalEnv.v:181`) for the stored fixpoints. -/
def RcClosed (rc : Name → LBTerm → Prop) : Prop := ∀ c t, rc c t → closedn 0 t = true

/-- The derived `==` on module paths implies equality. Reference: `modpath_eq_dec`
(`MR common/theories/Kernames.v:232`), which decides the equality that `==` tests. -/
theorem ModPath.eq_of_beq : ∀ {a b : ModPath}, (a == b) = true → a = b
  | .MPfile d₁, .MPfile d₂, h => by
    have h' : (d₁ == d₂) = true := h
    rw [beq_iff_eq.1 h']
  | .MPdot m₁ i₁, .MPdot m₂ i₂, h => by
    have h' : (m₁ == m₂ && i₁ == i₂) = true := h
    rw [Bool.and_eq_true] at h'
    rw [ModPath.eq_of_beq h'.1, beq_iff_eq.1 h'.2]
  | .MPfile _, .MPdot .., h | .MPdot .., .MPfile _, h => nomatch h

/-- The derived `==` on kernames, which `lookupConst` uses, implies equality. Reference:
`reflect_kername` (`MR common/theories/Kernames.v:325`), the equality test of `lookup_env`. -/
theorem Kername.eq_of_beq {a b : Kername} (h : (a == b) = true) : a = b := by
  obtain ⟨m₁, i₁⟩ := a
  obtain ⟨m₂, i₂⟩ := b
  have h' : (m₁ == m₂ && i₁ == i₂) = true := h
  rw [Bool.and_eq_true] at h'
  rw [ModPath.eq_of_beq h'.1, beq_iff_eq.1 h'.2]

section
variable {venv : VEnv} {lenv : GlobalDeclarations}

/-- A translated term's erasure has no loose index beyond the context's de Bruijn entries.
Reference: `erases_closed` (`MR E/ErasureProperties.v:428`). -/
theorem Erases.closed (hrc : RcClosed rc) (he : TrS venv Us Δ e e')
    (h : Erases venv Us ac rc Δ e r) : closedn Δ.bvars r = true := by
  induction h generalizing e' with
  | bvar =>
    cases he with
    | bvar h1 =>
      simp only [closedn, decide_eq_true_eq]
      have key : ∀ (Δ : VLCtx) i x, Δ.find? (.inl i) = some x → i < Δ.bvars := by
        intro Δ
        induction Δ with
        | nil => intro i x h; cases h
        | cons d Δ ih =>
          intro i x h
          match d, i with
          | (none, _), 0 => exact Nat.succ_pos _
          | (none, _), _ + 1 =>
            simp only [VLCtx.find?, VLCtx.next, bind, Option.bind_eq_some_iff] at h
            obtain ⟨_, h, _⟩ := h
            exact Nat.succ_lt_succ (ih _ _ h)
          | (some _, _), _ =>
            simp only [VLCtx.find?, VLCtx.next, bind, Option.bind_eq_some_iff] at h
            obtain ⟨_, h, _⟩ := h
            exact ih _ _ h
      exact key _ _ _ h1
  | fvar | const | box => rfl
  | lam hA _ ih =>
    cases he with
    | lam _ hA' hb =>
      cases TrS.det hA hA'
      exact ih hb
  | letE hT hv _ _ ihv ihb =>
    cases he with
    | letE _ hT' hv' hb =>
      cases TrS.det hT hT'
      cases TrS.det hv hv'
      simp only [closedn, ihv hv', Bool.true_and]
      exact ihb hb
  | app _ _ ihf iha =>
    cases he with
    | app _ _ hf ha => simp only [closedn, ihf hf, iha ha, Bool.and_self]
  | constRec _ hr => exact closedn_mono _ (Nat.zero_le _) (hrc _ _ hr)
  | mdata _ ih => cases he with | mdata he => exact ih he

/-- Monotonicity in the admissible targets of recursive constants (used, with `RecIn.ext`, as the
λ□ environment grows). Reference: none (DV-7); the role of `erases_extends`
(`MR E/ESubstitution.v:73`). -/
theorem Erases.mono_rc (hle : ∀ c t, rc c t → rc' c t) (h : Erases venv Us ac rc Δ e t) :
    Erases venv Us ac rc' Δ e t := by
  induction h with
  | bvar => exact .bvar
  | fvar => exact .fvar
  | lam hA _ ih => exact .lam hA ih
  | letE hT hv _ _ ihv ihb => exact .letE hT hv ihv ihb
  | app _ _ ihf iha => exact .app ihf iha
  | const hc => exact .const hc
  | constRec hc hr => exact .constRec hc (hle _ _ hr)
  | mdata _ ih => exact .mdata ih
  | box hb => exact .box hb

/-- A fixpoint stored for a constant stays stored when the environment grows freshly. Reference:
`erases_deps_cons` (`MR E/EDeps.v:492`), for `RecIn` (DV-7). -/
theorem RecIn.ext (hx : LenvExt lenv lenv') (h : RecIn lenv c t) : RecIn lenv' c t := by
  obtain ⟨new, rfl, hfresh⟩ := hx
  obtain ⟨defs, i, rfl, hl⟩ := h
  refine ⟨defs, i, rfl, ?_⟩
  have hnew : new.find? (·.1 == toKername c) = none := by
    rw [List.find?_eq_none]
    intro y hy hyk
    have hnone := hfresh (toKername c)
      (List.mem_map.2 ⟨y, hy, Kername.eq_of_beq hyk⟩)
    simp only [lookupConst, hnone] at hl
    cases hl
  unfold lookupConst at hl ⊢
  rw [List.find?_append, hnew, Option.none_or]
  exact hl

/-- The relation reads `ac` only at the constants of the source term. Reference: none (DV-11). -/
theorem Erases.congr_ac (hac : ConstsIn (fun c => ac c = ac' c) e)
    (h : Erases venv Us ac rc Δ e t) : Erases venv Us ac' rc Δ e t := by
  induction h with
  | bvar => exact .bvar
  | fvar => exact .fvar
  | lam hA _ ih => exact .lam hA (ih hac.2)
  | letE hT hv _ _ ihv ihb => exact .letE hT hv (ihv hac.2.1) (ihb hac.2.2)
  | app _ _ ihf iha => exact .app (ihf hac.1) (iha hac.2)
  | const hc => exact .const (Eq.trans (Eq.symm hac) hc)
  | constRec hc hr => exact .constRec (Eq.trans (Eq.symm hac) hc) hr
  | mdata _ ih => exact .mdata (ih hac)
  | box hb => exact .box hb

/-- An erasure of an application is `□` or an application of erasures. Reference:
`erases_mkApps_inv` (`MR E/ErasureProperties.v:105`), fragment. -/
theorem Erases.app_inv (h : Erases venv Us ac rc Δ (.app f a) t) :
    (t = .box ∧ ErasableS venv Us Δ (.app f a)) ∨
    ∃ tf ta, t = .app tf ta ∧ Erases venv Us ac rc Δ f tf ∧ Erases venv Us ac rc Δ a ta := by
  cases h with
  | app hf ha => exact .inr ⟨_, _, rfl, hf, ha⟩
  | box hb => exact .inl ⟨rfl, hb⟩

end

end EraseProof
