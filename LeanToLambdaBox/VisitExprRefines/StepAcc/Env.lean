import LeanToLambdaBox.VisitExprRefines.MotivesAcc

/-!
# The environment-facing steps of the accumulator induction

`doc/rework/12-REPAIRS-W9.md` §2.5 at the three members `Step/Env.lean` discharges. Two of
them — `Erasure.visitConst` and `Erasure.get_constant_kername` — are pass-throughs: their own
bodies read the reader and the registry and write nothing, and the registration they reach is
`Erasure.visitMutual`'s, one member down. The third, `Erasure.visitMutual` itself, is where
the accumulator grows at three exits; it is not here (`scratch/round7/W9-D-report.md` §3).
-/

namespace LeanToLambdaBox

open Lean Lean4Lean Erasure Witness Lean.Order

set_option synthInstance.maxSize 4000

section Steps

variable {lenv : Environment} {env : VEnv} {tbl : SourceTable} {cfg : ErasureConfig}
  {gw : Void IO.RealWorld → NameGenerator}

/-! ## Step 5 — `Erasure.get_constant_kername` -/

/-- **Step 5.** The hit branch reads the registry and returns, leaving the state alone; the
miss branch is one `Erasure.visitMutual` sub-run followed by a read-back. `step5`'s branch
split verbatim, at the accumulator conclusion. -/
theorem stepAcc_getConstantKername : StepAcc5 lenv env tbl cfg gw := by
  intro _P _A _htbl _hcfg _hcb _M vMut m6
  refine ⟨?_, bodyLe5 m6.2⟩
  intro n s ctx cctx ref w kn s' w' hrun Us Δ hinv hsup htab
  unfold getConstantKernameBody at hrun
  rw [run_bind_ok] at hrun
  obtain ⟨s₀, sa, wa, hget, hk⟩ := hrun
  rw [run_get] at hget
  cases hget
  cases hc : s.constants.get? n with
  | some kn₀ =>
      rw [hc] at hk
      simp only [] at hk
      rw [run_pure] at hk
      cases hk
      exact AccGrows.rfl' _
  | none =>
      rw [hc] at hk
      simp only [] at hk
      rw [run_bind_ok] at hk
      obtain ⟨uu, sb, wb, hvm, hk2⟩ := hk
      rw [run_bind_ok] at hk2
      obtain ⟨sc, sd, wd, hget2, hp⟩ := hk2
      rw [run_get] at hget2
      cases hget2
      rw [run_pure] at hp
      cases hp
      exact m6.1 _ _ _ _ _ _ _ _ _ hvm _ Δ hinv hsup htab

/-! ## Step 4 — `Erasure.visitConst` -/

/-- **Step 4.** The block branch returns the member's fix variable without touching the
state; the plain branch is one `Erasure.get_constant_kername` sub-run. `Motive4`'s two
exclusions put the head in the `defn` column of `KnownHead`, which is where the table
membership the sub-run asks for comes from — the accumulator needs no `ConstOrigin`, so
`visitConst_refines`' model premises do not appear. -/
theorem stepAcc_visitConst : StepAcc4 lenv env tbl cfg gw := by
  intro _P _A _htbl _hcfg _hcb _M vGck m5
  refine ⟨?_, bodyLe4 m5.2⟩
  intro e s ctx cctx ref w t s' w' hrun Us Δ nm us hinv he _hplain _hcas hkn hsup hnc hni
  subst he
  have htab : (tbl.decl? nm).isSome := by
    cases hkn with
    | indType _ hm => obtain ⟨iid, np, nfs, h⟩ := hm; exact absurd h (hni iid np nfs)
    | ctor _ hm => obtain ⟨I, k, h⟩ := hm; exact absurd h (hnc I k)
    | defn hd _ => rw [hd]; simp
  have hsupc : Supported env tbl (.const nm []) :=
    hsup.subterm (by simp [constNames]) (by
      cases hsup.term with
      | const hp hc hr hs hk => exact .const hp hc hr (by simpa [CtorSaturated] using hs) hk
      | casesApp _ _ _ _ harity => simp at harity)
  simp only [visitConstBody] at hrun
  rw [run_bind_ok] at hrun
  obtain ⟨c, s₁, w₁, hrd, hk⟩ := hrun
  rw [run_read] at hrd
  cases hrd
  cases hopt : ctx.fixvars.bind (fun hmap => hmap[nm]?) with
  | some id =>
      rw [hopt] at hk
      simp only [] at hk
      rw [run_pure] at hk
      cases hk
      exact AccGrows.rfl' _
  | none =>
      rw [hopt] at hk
      simp only [] at hk
      rw [run_bind_ok] at hk
      obtain ⟨kn, s₂, w₂, hgck, hp⟩ := hk
      rw [run_pure] at hp
      cases hp
      exact m5.1 _ _ _ _ _ _ _ _ _ hgck _ Δ hinv hsupc htab

end Steps

end LeanToLambdaBox
