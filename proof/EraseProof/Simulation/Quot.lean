import EraseProof.Simulation.Cases

/-!
# The quotient cases of the relation-level simulation

`SrcEval.quotMk` evaluates the element of `Quot.mk α r a`, whose erasure is the element's
(`Erases.quotMk`). `SrcEval.quotLift` is the quotient ι as β: `f` evaluates to `fun x => b` and
`q` to `Quot.mk α' r' a`, and the source continues with `b` at `a`; the erasure `f' q'`
(`Erases.quotLift`) evaluates `f'` to the erasure of the λ, a λ□ λ, and `q'` to an erasure of
`Quot.mk α' r' a`, which is an erasure of `a`, and λ□'s β substitutes it into the erased body
(`Erases.inst`, `a` closed by the rule's certificate). Adapted from `ML-V Simulation/Quot.lean`:
no `□` alternative (an unmarked spine erases by its head's rule only) and no typed translation.
Reference: the `eval_beta` case of `erases_correct` (`MR E/ErasureCorrectness.v:62`); PCUIC has no
quotients (DV-29).
-/

open Lean Erasure

namespace EraseProof

namespace SimCases

variable {σ : EvalEnv} {lenv : GlobalDeclarations}

/-- An erasure of `Quot.mk α r a` without extra arguments is an erasure of `a` (`Erases.quotMk`). -/
theorem quotMk_inv {Γ : List CtxBinder} {c : Name} {us : List Level} {qv : QuotVal}
    {α r a : Expr} {tb : LBTerm} (hc : findDecl σ.decls c = some (.quotInfo qv))
    (hk : qv.kind = .ctor) (h : Erases noCert σ Γ (mkAppN (.const c us) [α, r, a].toArray) tb) :
    Erases noCert σ Γ a tb := by
  rcases Erases.quot_inv hc (by rw [hk]; rfl) h with
    ⟨_, _, _, extra, _, extra', -, hl, ha, hlex, -, rfl⟩ | ⟨_, _, _, _, _, _, _, _, _, _, hk₂, -⟩
  · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hl
    obtain ⟨-, -, rfl, rfl⟩ := hl
    obtain rfl : extra' = [] := List.eq_nil_of_length_eq_zero hlex.symm
    exact ha
  · rw [hk] at hk₂; cases hk₂

/-- The `quotMk` case of `erases_correct`: the erasure of `Quot.mk α r a` is an erasure of `a`
(`quotMk_inv`), which evaluates to an erasure of the element's value. Adapted from
`ML-V Simulation/Quot.lean:53`, without the `□` alternative. Reference: the `eval_construct` case
of `erases_correct` (`MR E/ErasureCorrectness.v:1148`); DV-29. -/
theorem erases_correct_quotMk {c : Name} {us : List Level} {qv : QuotVal} {α r a a' : Expr}
    (hc : findDecl σ.decls c = some (.quotInfo qv)) (hk : qv.kind = .ctor)
    (iha : ErasesSim σ lenv a a') :
    ErasesSim σ lenv (mkAppN (.const c us) [α, r, a].toArray)
      (mkAppN (.const c us) [α, r, a'].toArray) := by
  intro tb her hdeps
  obtain ⟨vb, hvb, hevb⟩ := iha (quotMk_inv hc hk her) hdeps
  have := Erases.quotMk (cert := noCert) (Γ := []) (us := us) (α := α) (r := r) (extra := [])
    (extra' := []) hc hk hvb rfl (fun _ _ _ h => by simp at h)
  rw [List.append_nil] at this
  exact ⟨vb, this, hevb⟩

/-- The `quotLift` case of `erases_correct`: the erasure of `Quot.lift α r β f h q` is `f' q'`
(`Erases.quot_inv`); `f'` evaluates to an erasure of the λ that `f` evaluates to, a λ□ λ
(`lam_inv`), `q'` to an erasure of `Quot.mk α' r' a`, an erasure of the element `a`
(`quotMk_inv`), and λ□'s β substitutes it into the erased body (`Erases.inst`; `a` has no loose
bound variable, by the rule's certificate), an erasure of the body at `a`. Adapted from
`ML-V Simulation/Quot.lean:92`, without the `□` alternatives and the typed translation.
Reference: the `eval_beta` case of `erases_correct` (`MR E/ErasureCorrectness.v:62`); DV-29. -/
theorem erases_correct_quotLift {env : ConLeche.Env} {c c' : Name} {us us' : List Level}
    {qv qv' : QuotVal} {α r β f h q α' r' a b v A : Expr} {x : Name} {bi : BinderInfo}
    (hc : findDecl σ.decls c = some (.quotInfo qv)) (hk : qv.kind = .lift)
    (hc' : findDecl σ.decls c' = some (.quotInfo qv')) (hk' : qv'.kind = .ctor)
    (hok : CLOk env (mkAppN (.const c us)
      [α, r, β, .lam x A b bi, h, mkAppN (.const c' us') [α', r', a].toArray].toArray))
    (ihf : ErasesSim σ lenv f (.lam x A b bi))
    (ihq : ErasesSim σ lenv q (mkAppN (.const c' us') [α', r', a].toArray))
    (ihb : ErasesSim σ lenv (b.instantiate1' a) v) :
    ErasesSim σ lenv (mkAppN (.const c us) [α, r, β, f, h, q].toArray) v := by
  intro tb her hdeps
  rcases Erases.quot_inv hc (by rw [hk]; rfl) her with
    ⟨_, _, _, _, _, _, hk₂, -⟩ | ⟨_, _, _, _, _, _, extra, f', q', extra', -, hl, herf, herq, hlex, -, rfl⟩
  · rw [hk] at hk₂; cases hk₂
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at hl
  obtain ⟨-, -, -, rfl, -, rfl, rfl⟩ := hl
  obtain rfl : extra' = [] := List.eq_nil_of_length_eq_zero hlex.symm
  have hla : AbsFV.LBV 0 a := AbsFV.LBV_mkAppN.1
    (AbsFV.LBV_mkAppN.1 hok.lbv (mkAppN (.const c' us') [α', r', a].toArray) (by simp)) a (by simp)
  change ErasesDeps noCert σ lenv (.app f' q') at hdeps
  cases hdeps with
  | app hdf hdq =>
  obtain ⟨vf, hvf, hevf⟩ := ihf herf hdf
  obtain ⟨vq, hvq, hevq⟩ := ihq herq hdq
  obtain ⟨b', rfl, hb'⟩ := lam_inv hvf
  cases ErasesDeps.eval hdf hevf with
  | lambda hdb =>
  obtain ⟨res, hres, hevres⟩ := ihb (Erases.inst hb' (quotMk_inv hc' hk' hvq) hla)
    (ErasesDeps.csubst (ErasesDeps.eval hdq hevq) hdb)
  exact ⟨res, hres, .beta hevf hevq hevres⟩

end SimCases

end EraseProof
