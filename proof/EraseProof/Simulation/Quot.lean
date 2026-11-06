import EraseProof.Simulation.Iota

/-!
# The quotient cases of the simulation

`SrcEval.quotMk` evaluates the element of `Quot.mk α r a`, whose erasure is the element's
(`Erases.quotMk`). `SrcEval.quotLift` is the quotient ι as β: `f` evaluates to `fun x => b` and
`q` to `Quot.mk α' r' a`, and the source continues with `b` at `a`; the erasure `f' q'`
(`Erases.quotLift`) evaluates `f'` to the erasure of the λ and `q'` to an erasure of
`Quot.mk α' r' a`, which is an erasure of `a` (or `□`, and then `a` is a proof,
`IsErasable.quotMk_inv`), and λ□'s β substitutes it into the erased body (`Erases.inst`). The
typed translation of the body at `a` comes from Metalean's quotient ι (`WHRed.quotIota_defeq`).
Reference: the `eval_beta` case of `erases_correct` (`MR E/ErasureCorrectness.v:62`); PCUIC has
no quotients (DV-27).
-/

open Lean Erasure
open Metalean (Defeq EnvWF TypeEq WHRed)

namespace EraseProof

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P : List ConstantInfo}
  {σ : EvalEnv} {lps : List Name} {lenv : GlobalDeclarations}

/-- The element of a `Quot.mk` value is a value. -/
theorem srcValue_quotMk_arg {c : Name} {us : List Level} {qv : QuotVal} {α r a : Expr}
    (hc : findDecl σ.decls c = some (.quotInfo qv))
    (h : SrcValue σ (mkAppN (.const c us) [α, r, a].toArray)) : SrcValue σ a := by
  have hfn := SrcDefeq.getAppFn_mkAppN_const c us [α, r, a]
  generalize hx : mkAppN (.const c us) [α, r, a].toArray = x at h hfn
  cases h with
  | quotMk _ _ ha =>
    obtain ⟨-, -, h3⟩ := SimIota.mkAppN_inj hx
    simp only [List.cons.injEq, and_true] at h3
    obtain ⟨rfl, rfl, rfl⟩ := h3
    exact ha
  | ctor hc' =>
    obtain ⟨rfl, -, -⟩ := SimIota.mkAppN_inj hx
    rw [hc] at hc'; cases hc'
  | spine hs =>
    obtain ⟨c', us', hfn', hat⟩ := RelInst.atomSpine_head hs
    rw [hfn] at hfn'; cases hfn'
    simp [EvalEnv.isAtom, hc, OwnRules] at hat
  | propProj hp =>
    obtain ⟨S, i, e₀, hfn'⟩ := RelInst.propProj_head hp
    rw [hfn] at hfn'; cases hfn'
  | lam | sort | forallE | lit => simp [Expr.getAppFn] at hfn

/-- The `quotMk` case of `erases_correct`: the erasure of `Quot.mk α r a` is `□` or an erasure of
`a`, which evaluates to an erasure of the element's value. Reference: the `eval_construct` case
of `erases_correct` (`MR E/ErasureCorrectness.v:1148`); DV-27. -/
theorem erases_correct_quotMk (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv σ.decls P)
    {c : Name} {us : List Level} {qv : QuotVal} {α r a a' : Expr}
    (hc : findDecl σ.decls c = some (.quotInfo qv)) (hk : qv.kind = .ctor) (ha : SrcEval σ a a')
    (iha : ErasesSim E B lps σ lenv a a') :
    ErasesSim E B lps σ lenv (mkAppN (.const c us) [α, r, a].toArray)
      (mkAppN (.const c us) [α, r, a'].toArray) := by
  intro t tb he ⟨T, ht⟩ her hdeps
  have hev : SrcEval σ (mkAppN (.const c us) [α, r, a].toArray)
      (mkAppN (.const c us) [α, r, a'].toArray) := .quotMk hc hk ha
  rcases Erases.quot_inv hc (by rw [hk]; rfl) (by simp) her with ⟨rfl, hbx⟩ |
    ⟨_, _, a₁, extra, a'', extra', -, hl₁, ha'', hlex, -, rfl⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, hk₂, -⟩
  · exact erases_correct_box henv hE hsub he ht hbx hev
  · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hl₁
    obtain ⟨-, -, rfl, rfl⟩ := hl₁
    obtain rfl : extra' = [] := List.eq_nil_of_length_eq_zero (by simpa using hlex.symm)
    obtain ⟨η, hB⟩ := henv.lookup_quot (SrcDefeq.findDecl_sub hsub hc)
    rw [hk] at hB
    simp only [quotKindOf] at hB
    obtain ⟨as', hlen, hargs, hsat⟩ := TrM.special_inv hB rfl he
    cases hsat with
    | quotEta _ hlt => simp [quotArity] at hlen hlt; omega
    | @quotMk _ α₀ r₀ a₀ rest _ u hu =>
    obtain rfl : rest = [] := by simpa using hlen
    have ha₀ : TrM E B lps .nil [] a a₀ := hargs 2 a a₀ rfl rfl
    have ht' : E[.nil] ⊢ Metalean.Expr.quotMk η u α₀ r₀ a₀ : T := ht
    obtain ⟨_, _, _, -, -, haT, -⟩ := ht'.quotMk_prem
    obtain ⟨vb, hvb, hevb⟩ := iha ha₀ ⟨_, haT.right⟩ ha'' hdeps
    exact ⟨vb, .quotMk (extra := []) (extra' := []) hc hk hvb rfl (fun _ _ _ h => by simp at h),
      hevb⟩
  · rw [hk] at hk₂; cases hk₂

/-- The `quotLift` case of `erases_correct`: the erasure of `Quot.lift α r β f h q` is `□` or
`f' q'`; `f'` evaluates to an erasure of the λ that `f` evaluates to, `q'` to an erasure of the
element `a` of `q`'s value (`□` when the quotient is a proposition, `IsErasable.quotMk_inv`), and
λ□'s β substitutes it into the erased body (`Erases.inst`), an erasure of the body at `a`, whose
typed translation is reached by the quotient ι (`WHRed.quotIota_defeq`) and β. If the λ erases to
`□`, the body at `a` is erasable, and so is the value. Reference: the `eval_beta` case of
`erases_correct` (`MR E/ErasureCorrectness.v:62`); DV-27. -/
theorem erases_correct_quotLift (henv : ProgEnv P ζ E B) (hE : EnvWF E)
    (hsub : SubEnv σ.decls P) {c c' : Name} {us us' : List Level} {qv qv' : QuotVal}
    {α r β f h q α' r' a b v A : Expr} {x : Name} {bi : BinderInfo}
    (hc : findDecl σ.decls c = some (.quotInfo qv)) (hk : qv.kind = .lift)
    (hf : SrcEval σ f (.lam x A b bi))
    (hq : SrcEval σ q (mkAppN (.const c' us') [α', r', a].toArray))
    (hc' : findDecl σ.decls c' = some (.quotInfo qv')) (hk' : qv'.kind = .ctor)
    (hb : SrcEval σ (b.instantiate1' a) v)
    (ihf : ErasesSim E B lps σ lenv f (.lam x A b bi))
    (ihq : ErasesSim E B lps σ lenv q (mkAppN (.const c' us') [α', r', a].toArray))
    (ihb : ErasesSim E B lps σ lenv (b.instantiate1' a) v) :
    ErasesSim E B lps σ lenv (mkAppN (.const c us) [α, r, β, f, h, q].toArray) v := by
  intro t tb he ⟨T, ht⟩ her hdeps
  have hok := SrcDefeq.nil_ok (E := E) (lps := lps)
  have hord := henv.metaOrderOK
  have hev : SrcEval σ (mkAppN (.const c us) [α, r, β, f, h, q].toArray) v :=
    .quotLift hc hk hf hq hc' hk' hb
  obtain ⟨η, hB⟩ := henv.lookup_quot (SrcDefeq.findDecl_sub hsub hc)
  obtain ⟨η', hB'⟩ := henv.lookup_quot (SrcDefeq.findDecl_sub hsub hc')
  rw [hk] at hB
  rw [hk'] at hB'
  simp only [quotKindOf] at hB hB'
  obtain rfl := henv.quot_head_unique hB hB'
  rcases Erases.quot_inv hc (by rw [hk]; rfl) (by simp) her with ⟨rfl, hbx⟩ |
    ⟨_, _, _, _, _, _, hk₂, -⟩ |
    ⟨_, _, _, f₁, _, q₁, extra, f', q', extra', -, hl₁, herf, herq, hlex, -, rfl⟩
  · exact erases_correct_box henv hE hsub he ht hbx hev
  · rw [hk] at hk₂; cases hk₂
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at hl₁
  obtain ⟨-, -, -, rfl, -, rfl, rfl⟩ := hl₁
  obtain rfl : extra' = [] := List.eq_nil_of_length_eq_zero (by simpa using hlex.symm)
  have hdeps' : ErasesDeps E B σ lenv (.app f' q') := hdeps
  -- the translation of the spine
  obtain ⟨as', hlen, hargs, hsat⟩ := TrM.special_inv hB rfl he
  cases hsat with
  | quotEta _ hlt => simp [quotArity] at hlen hlt; omega
  | @quotLift _ α₀ r₀ β₀ f₀ h₀ q₀ rest _ u w hu =>
  obtain rfl : rest = [] := by simpa using hlen
  have hf₀ : TrM E B lps .nil [] f f₀ := hargs 3 f f₀ rfl rfl
  have hq₀ : TrM E B lps .nil [] q q₀ := hargs 5 q q₀ rfl rfl
  have ht' : E[.nil] ⊢ Metalean.Expr.quotLift η u w α₀ r₀ β₀ f₀ h₀ q₀ : T := ht
  obtain ⟨_, _, _, _, _, _, -, -, -, hfT, -, hqT, -⟩ := ht'.quotLift_prem
  cases hdeps' with
  | app hdf hdq =>
  -- the λ□ values of the head and of the quotient argument
  obtain ⟨vf, hvf, hevf⟩ := ihf hf₀ ⟨_, hfT.right⟩ herf hdf
  obtain ⟨vq, hvq, hevq⟩ := ihq hq₀ ⟨_, hqT.right⟩ herq hdq
  -- the typed translations of the values: the λ, and `Quot.mk` of the element
  obtain ⟨tl, htl, hdl⟩ := SrcEval.defeq henv hE hsub hf₀ hfT.right hf
  obtain ⟨tq, htq, hdq'⟩ := SrcEval.defeq henv hE hsub hq₀ hqT.right hq
  obtain ⟨bs', hlen', hargs', hsat'⟩ := TrM.special_inv hB' rfl htq
  cases hsat' with
  | quotEta _ hlt => simp [quotArity] at hlen' hlt; omega
  | @quotMk _ α₁ r₁ a₀ rest' _ u' hu' =>
  obtain rfl : rest' = [] := by simpa using hlen'
  have ha₀ : TrM E B lps .nil [] a a₀ := hargs' 2 a a₀ rfl rfl
  have h1 : E[.nil] ⊢ Metalean.Expr.quotLift η u w α₀ r₀ β₀ f₀ h₀ q₀ ≡
      .quotLift η u w α₀ r₀ β₀ tl h₀ (.quotMk η u' α₁ r₁ a₀) : T :=
    DCong.defeq hE not_false (.quotLift .refl .refl .refl (.leaf hdl) .refl (.leaf hdq')) hok
      (DCong.CtxConv.refl hok) ht'
  have h2 := WHRed.quotIota_defeq hE hok h1.right
  obtain ⟨A₀, b₀, rfl, hA₀, hb₀⟩ := SimCases.trM_lam_inv htl
  obtain ⟨X, Y, hl, hta', -⟩ := h2.right.app_inv
  obtain ⟨T₀, hb₀T, hπ⟩ := hl.lam_inv hok
  have htaA : E[.nil] ⊢ a₀ : A₀ := (TypeEq.forallE_inj hE hok hπ).1.conv hta'
  obtain ⟨u₀, hA₀u⟩ := htaA.regular
  obtain ⟨tb', htb', hdb'⟩ := TrM.inst hE hok hord hb₀ ha₀ htaA hb₀T
  -- the element's erasure, which `q'` evaluates to
  have hval : SrcValue σ a := srcValue_quotMk_arg hc' (SrcEval.value hq)
  obtain ⟨va, hva, rfl⟩ : ∃ va, Erases E B lps σ .nil [] a va ∧ vq = va := by
    rcases Erases.quot_inv hc' (by rw [hk']; rfl) (by simp) hvq with ⟨rfl, hbx⟩ |
      ⟨_, _, a₁, extra₁, a', extra₁', -, hl₂, ha', hlex₂, -, rfl⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, hk₂, -⟩
    · refine ⟨.box, .box ?_, rfl⟩
      obtain ⟨w₀, hw, hwE⟩ := hbx
      obtain ⟨bs₂, hl₂, hargs₂, hsat₂⟩ := TrM.special_inv hB' rfl hw
      cases hsat₂ with
      | quotEta _ hlt => simp [quotArity] at hl₂ hlt; omega
      | @quotMk _ _ _ a₂ rest₂ _ _ _ =>
        obtain rfl : rest₂ = [] := by simpa using hl₂
        exact ⟨a₂, hargs₂ 2 a a₂ rfl rfl, IsErasable.quotMk_inv hE hok hwE⟩
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hl₂
      obtain ⟨-, -, rfl, rfl⟩ := hl₂
      obtain rfl : extra₁' = [] := List.eq_nil_of_length_eq_zero (by simpa using hlex₂.symm)
      exact ⟨_, ha', rfl⟩
    · rw [hk'] at hk₂; cases hk₂
  generalize hlv : Expr.lam x A b bi = lv at hvf
  cases hvf with
  | lam hA'' hAt hbody =>
    cases hlv
    obtain ⟨l, hl''⟩ := hAt
    have hAA : E[.nil] ⊢ A₀ ≡ _ : .sort u₀ := SimCases.trM_defeq hE hA₀ hA'' hA₀u hl''
    have hb₀T'' := Defeq.snocConv hAA hb₀T
    have hokA : E[Metalean.Ctx.nil.snoc _] ⊢ ok := .snoc hok ⟨l, hl''⟩
    have htb'' := InstPre.PreTr.recover hord (InstPre.PreTr.ofTrM hb₀) (InstPre.Thin.id _) hokA
      ⟨T₀, by rw [Metalean.Expr.rename_id]; exact hb₀T''⟩
    have hsubst := Erases.inst henv hE hok hsub hval hbody htb'' hb₀T'' hva ha₀
      (Defeq.defeqDF hAA htaA) (SimCases.closed0 ha₀ hva)
    have hdl' := ErasesDeps.eval hdf hevf
    cases hdl' with
    | lambda hdb =>
    obtain ⟨res, hres, hevres⟩ := ihb htb' ⟨_, hdb'.left⟩ hsubst
      (ErasesDeps.csubst (ErasesDeps.eval hdq hevq) hdb)
    exact ⟨res, hres, .beta hevf hevq hevres⟩
  | box hbx =>
    subst hlv
    obtain ⟨t₁, htr₁, U, ht₁, hU⟩ := hbx
    have hlam : IsErasable E .nil (.lam A₀ b₀) :=
      RelInst.IsErasable.of_defeq (SimCases.trM_defeq hE htr₁ htl ht₁ hl) hU
    obtain ⟨W, hW, hWe⟩ := IsErasable.inst hE htaA (IsErasable.lam_inv hE hok hlam)
    have hEb : IsErasable E .nil tb' :=
      RelInst.IsErasable.of_defeq (Defeq.retype hE hok hdb'.symm hW) hWe
    exact ⟨.box, .box (ErasableS.eval henv hE hsub htb' hdb'.left hb ⟨tb', htb', hEb⟩),
      .box hevf hevq⟩
  | ctor | cases | casesReduced | eta | quotMk | quotLift =>
    exact absurd hlv (CasesWhred.ne_mkAppN_const fun _ _ h => by cases h)
  | bvar | fvar | letE | app | const | proj | litZero | litSucc | mdata => cases hlv

end

end EraseProof
