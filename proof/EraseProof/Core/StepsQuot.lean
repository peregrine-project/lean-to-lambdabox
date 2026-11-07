import EraseProof.Core.StepsCtor

/-!
# The quotient step

`StepsB.quot`: an application or a constant whose head is `Quot.mk` or `Quot.lift` (a quotient
constant with `quotEvalArity`). `visitConstApp` η-expands the spine to the arity (3, resp. 6;
`withAppEta_spec`, the declared types being `Π`-telescopes by `QuotShape`) and erases `Quot.mk α r a`
as the element and `Quot.lift α r β f h q` as `f q`, each applied to the arguments beyond the
arity (`Erases.quotMk`, `Erases.quotLift`).

Reference: none in MetaRocq (PCUIC has no quotients); Lean's code generator
(`Lean/Compiler/LCNF/ToLCNF.lean`, `visitQuotLift`; `ToMono.lean`); DV-29.
-/

open Lean Erasure
open Metalean (Defeq)

namespace EraseProof

namespace Steps

open TravFrame

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P decls : List ConstantInfo}
  {view : EnvView} {cfg : ErasureConfig}

/-- An erasure of an argument of a saturated spine, in a context without bound locals, is
closed. -/
theorem closed_of_arg {lps : List Name} {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
    {Δ : MLCtx ζ lps.length n} {S : Name → Prop} {tc : TravCtx} {ps : PureState} {as : List Expr}
    (hctx : CtxOK E B lps Γ Δ cfg tc ps)
    (hargs : ∀ a ∈ as, (∀ d, nameOccurs d a = true → S d) ∧ MachineFree cfg a ∧
      NatPlain cfg a ∧ RecFree decls a ∧ ∃ a', TrM E B lps Γ Δ a a' ∧ ∃ A, E[Γ] ⊢ a' : A)
    {x : Expr} {x' : LBTerm} (hx : x ∈ as)
    (h : Erases E B lps (evalEnvOf view cfg decls) Γ Δ x x') : closedn 0 x' = true := by
  obtain ⟨-, -, -, -, y, hy, -⟩ := hargs x hx
  have := Erases.closed hy h
  rwa [countP_none hctx.nobv] at this

/-- The erasures of the arguments beyond the arity, pointwise erasures of arguments of the spine,
are closed. -/
theorem closed_of_args {lps : List Name} {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
    {Δ : MLCtx ζ lps.length n} {S : Name → Prop} {tc : TravCtx} {ps : PureState}
    {as rest : List Expr} {rest' : List LBTerm} (hctx : CtxOK E B lps Γ Δ cfg tc ps)
    (hargs : ∀ a ∈ as, (∀ d, nameOccurs d a = true → S d) ∧ MachineFree cfg a ∧
      NatPlain cfg a ∧ RecFree decls a ∧ ∃ a', TrM E B lps Γ Δ a a' ∧ ∃ A, E[Γ] ⊢ a' : A)
    (hsub : ∀ x ∈ rest, x ∈ as) (hlen : rest.length = rest'.length)
    (hers : ∀ (i : Nat) a a', rest[i]? = some a → rest'[i]? = some a' →
      Erases E B lps (evalEnvOf view cfg decls) Γ Δ a a') :
    ∀ a' ∈ rest', closedn 0 a' = true := by
  intro a' ha'
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 ha'
  have hk' : k < rest.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.1 hk).1
  exact closed_of_arg hctx hargs (hsub _ (List.getElem_mem hk'))
    (hers k _ _ (List.getElem?_eq_getElem hk') hk)

/-- `visitApp fuel e` at the pure backend on a spine whose head is `Quot.mk` or `Quot.lift`, from
`visitExpr` and `visitMutual` at the fuels up to `fuel` (`ih`): the spine is η-expanded to the
arity (`withAppEta_spec`), and the saturated spine is erased by `Erases.quotMk` (the element
applied to the arguments beyond the arity) or `Erases.quotLift` (the function applied to the
quotient and the arguments beyond the arity). Reference: `visitConstApp`
(`LeanToLambdaBox/Erasure.lean:948`); DV-29. -/
theorem visitApp_quot (hG : CoreEnv E B P decls view cfg) {fuel : Nat}
    (ih : StepIH E B view cfg decls fuel) {e : Expr} {c : Name} {us : List Level} {qv : QuotVal}
    (hfn : e.getAppFn = .const c us) (hci : casesInfo? decls c = none)
    (hca : ctorArity? decls c = none) (hqv : findDecl decls c = some (.quotInfo qv))
    (hqs : (quotEvalArity qv.kind).isSome)
    {lps : List Name} {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n}
    {S : Name → Prop} {t : Metalean.Expr ζ lps.length n} {st st' : ErasureState} {tc : TravCtx}
    {ps ps' : PureState} {r : LBTerm}
    (hctx : CtxOK E B lps Γ Δ cfg tc ps) (hsc : ScopeOK decls S)
    (hocc : ∀ d, nameOccurs d e = true → S d) (hmf : MachineFree cfg e) (hnp : NatPlain cfg e)
    (hrf : RecFree decls e) (hok : StateOK E B (evalEnvOf view cfg decls) st)
    (he : TrM E B lps Γ Δ e t) (ht : ∃ T, E[Γ] ⊢ t : T)
    (hrun : (visitApp (m := PureM) fuel e).runPure st tc ⟨decls, view⟩ ps =
      .ok ((r, st'), ps')) :
    Erases E B lps (evalEnvOf view cfg decls) Γ Δ e r ∧
      ErasesDeps E B (evalEnvOf view cfg decls) st'.gdecls r ∧
      Grows E B (evalEnvOf view cfg decls) S st st' ps ps' := by
  -- the spine
  have hsp : mkAppN (.const c us) (spineArgs e).toArray = e := by rw [← hfn]; exact mkAppN_spine e
  have hQ : ∀ {Q : Expr → Prop}, (∀ f a, Q (.app f a) → Q f ∧ Q a) → Q e →
      Q e.getAppFn ∧ ∀ a ∈ spineArgs e, Q a := fun hQ' h =>
    foldl_pred hQ' (by rw [← mkAppN_toArray, mkAppN_spine]; exact h)
  obtain ⟨-, hoccA⟩ := hQ (Q := fun x => ∀ d, nameOccurs d x = true → S d)
    (fun f a h => ⟨fun d hd => h d (by simp [nameOccurs, hd]),
      fun d hd => h d (by simp [nameOccurs, hd])⟩) hocc
  obtain ⟨-, hmfA⟩ := hQ (Q := MachineFree cfg) (fun _ _ h => h) hmf
  obtain ⟨-, hnpA⟩ := hQ (Q := NatPlain cfg) (fun _ _ h => h) hnp
  obtain ⟨-, hrfA⟩ := hQ (Q := RecFree decls) (fun _ _ h => h) hrf
  have hcP := SrcDefeq.findDecl_sub (σ := evalEnvOf view cfg decls) hG.sub hqv
  obtain ⟨η, hB⟩ := hG.prog.lookup_quot hcP
  have htyped := TrM.quot_args_typed hB (by rw [hsp]; exact he) ht
  have hargs : ∀ a ∈ spineArgs e, (∀ d, nameOccurs d a = true → S d) ∧ MachineFree cfg a ∧
      NatPlain cfg a ∧ RecFree decls a ∧ ∃ a', TrM E B lps Γ Δ a a' ∧ ∃ A, E[Γ] ⊢ a' : A :=
    fun a ha => ⟨hoccA a ha, hmfA a ha, hnpA a ha, hrfA a ha, htyped a ha⟩
  have hshape := ProgEnv.quot_shape hG.prog hcP
  cases fuel with
  | zero => rw [visitApp] at hrun; cases hrun
  | succ f1 =>
  rw [visitApp] at hrun
  split at hrun
  swap
  · rename_i hne; exact absurd hfn (hne c us)
  cases f1 with
  | zero => rw [visitConstApp] at hrun; cases hrun
  | succ f2 =>
  rw [visitConstApp, withApp_eq] at hrun
  split at hrun
  swap
  · rename_i hne; exact absurd hfn (hne c us)
  rename_i c' us' hc'
  rw [hfn] at hc'
  cases hc'
  rw [runPure_bind, show (liftM (Backend.casesInfo? (m := PureM) c) :
      EraseT PureM (Option CasesInfo)).runPure st tc ⟨decls, view⟩ ps = .ok ((none, st), ps) by
    show Except.ok ((casesInfo? decls c, st), ps) = _; rw [hci], ok_bind'] at hrun
  dsimp only at hrun
  rw [runPure_bind, show (liftM (Backend.ctorArity? (m := PureM) c) :
      EraseT PureM (Option Nat)).runPure st tc ⟨decls, view⟩ ps = .ok ((none, st), ps) by
    show Except.ok ((ctorArity? decls c, st), ps) = _; rw [hca], ok_bind'] at hrun
  dsimp only at hrun
  rw [runPure_bind, show (liftM (Backend.findConst? (m := PureM) c) :
      EraseT PureM (Option ConstantInfo)).runPure st tc ⟨decls, view⟩ ps =
        .ok ((some (.quotInfo qv), st), ps) by
    show Except.ok ((findConst decls c, st), ps) = _
    rw [show findConst decls c = findDecl decls c from rfl, hqv], ok_bind'] at hrun
  dsimp only at hrun
  have ihf : ∀ e, ExprSpec E B view cfg decls f2 e := fun e => ih.expr f2 (by omega) e
  obtain ⟨cval, kind⟩ := qv
  cases kind with
  | type => simp [quotEvalArity] at hqs
  | ind => simp [quotEvalArity] at hqs
  | ctor =>
    simp only at hrun
    obtain ⟨body, hpk⟩ : ∃ body, peelForalls 3 cval.type = some body := by
      rcases hshape with ⟨-, hk, -⟩ | ⟨-, -, hp⟩ | ⟨-, hk, -⟩ | ⟨-, hk⟩
      · cases hk
      · exact Option.isSome_iff_exists.1 hp
      · cases hk
      · cases hk
    refine withAppEta_spec (ci := .quotInfo ⟨cval, .ctor⟩) hG hqv
      (by simp [specialArity, evalEnvOf, hqv, quotEvalArity]) hpk ?_ hfn hctx hsc hargs hok he ht
      hrun
    intro lps' n' Γ' Δ' S' st₁ st₁' tc' ps₁ ps₁' r' as hctx' hsc' hargs' hlen' hok' hrun'
    beta_reduce at hrun'
    obtain ⟨x0, x1, x2, rest, rfl⟩ : ∃ x0 x1 x2 rest, as = x0 :: x1 :: x2 :: rest := by
      rcases as with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, rest⟩⟩⟩
      all_goals first | exact ⟨_, _, _, _, rfl⟩ | (simp at hlen')
    rw [runPure_bind] at hrun'
    obtain ⟨⟨⟨a, sa⟩, pa⟩, hg, hrun'⟩ := OracleWhnf.ok_of_bind hrun'
    obtain ⟨ha, rfl, rfl⟩ := getOrFail_run hg
    simp only [List.getElem?_toArray, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq] at ha
    subst ha
    rw [runPure_bind] at hrun'
    obtain ⟨⟨⟨tf, st₂⟩, ps₂⟩, hf, hrun'⟩ := OracleWhnf.ok_of_bind hrun'
    obtain ⟨h0, h1, h2, h3, x', hx, X, hX⟩ := hargs' x2 (.tail _ (.tail _ (.head _)))
    have ⟨herf, hdf, hgf⟩ := ihf x2 hctx' hsc' h0 h1 h2 h3 hok' hx ⟨X, hX⟩ hf
    rw [show (List.toArray (x0 :: x1 :: x2 :: rest)).extract 3 = rest.toArray by simp] at hrun'
    cases f2 with
    | zero => rw [visitAppArgs] at hrun'; cases hrun'
    | succ i =>
    have hsub : ∀ b ∈ rest, b ∈ x0 :: x1 :: x2 :: rest := fun b hb => .tail _ (.tail _ (.tail _ hb))
    obtain ⟨as', rfl, hlen, hers, hdeps, hgr⟩ := visitAppArgs_list
      (fun e => ih.expr i (by omega) e) (hctx'.mono hgf.next) hsc'
      (fun b hb => hargs' b (hsub b hb)) hgf.inv hrun'
    refine ⟨Erases.quotMk (α := x0) (r := x1) (extra := rest) hqv rfl herf hlen hers,
      deps_mkApps_intro (ErasesDeps.ext hgr.ext hdf) hdeps, hgf.trans hgr, ?_⟩
    rw [AbsFV.closedn_mkApps]
    exact ⟨closed_of_arg hctx' hargs' (.tail _ (.tail _ (.head _))) herf,
      closed_of_args (hctx'.mono hgf.next) hargs' hsub hlen hers⟩
  | lift =>
    simp only at hrun
    obtain ⟨body, hpk⟩ : ∃ body, peelForalls 6 cval.type = some body := by
      rcases hshape with ⟨-, hk, -⟩ | ⟨-, hk, -⟩ | ⟨-, -, hp⟩ | ⟨-, hk⟩
      · cases hk
      · cases hk
      · exact Option.isSome_iff_exists.1 hp
      · cases hk
    refine withAppEta_spec (ci := .quotInfo ⟨cval, .lift⟩) hG hqv
      (by simp [specialArity, evalEnvOf, hqv, quotEvalArity]) hpk ?_ hfn hctx hsc hargs hok he ht
      hrun
    intro lps' n' Γ' Δ' S' st₁ st₁' tc' ps₁ ps₁' r' as hctx' hsc' hargs' hlen' hok' hrun'
    beta_reduce at hrun'
    obtain ⟨x0, x1, x2, x3, x4, x5, rest, rfl⟩ : ∃ x0 x1 x2 x3 x4 x5 rest,
        as = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: rest := by
      rcases as with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, _ | ⟨x5, rest⟩⟩⟩⟩⟩⟩
      all_goals first | exact ⟨_, _, _, _, _, _, _, rfl⟩ | (simp at hlen')
    rw [runPure_bind] at hrun'
    obtain ⟨⟨⟨a, sa⟩, pa⟩, hg, hrun'⟩ := OracleWhnf.ok_of_bind hrun'
    obtain ⟨ha, rfl, rfl⟩ := getOrFail_run hg
    simp only [List.getElem?_toArray, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq] at ha
    subst ha
    rw [runPure_bind] at hrun'
    obtain ⟨⟨⟨tf, st₂⟩, ps₂⟩, hf, hrun'⟩ := OracleWhnf.ok_of_bind hrun'
    obtain ⟨h0, h1, h2, h3, x', hx, X, hX⟩ := hargs' x3 (.tail _ (.tail _ (.tail _ (.head _))))
    have ⟨herf, hdf, hgf⟩ := ihf x3 hctx' hsc' h0 h1 h2 h3 hok' hx ⟨X, hX⟩ hf
    rw [show (List.toArray (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: rest)).extract 5 =
      (x5 :: rest).toArray by simp] at hrun'
    cases f2 with
    | zero => rw [visitAppArgs] at hrun'; cases hrun'
    | succ i =>
    have hsub : ∀ b ∈ x5 :: rest, b ∈ x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: rest :=
      fun b hb => .tail _ (.tail _ (.tail _ (.tail _ (.tail _ hb))))
    obtain ⟨as', rfl, hlen, hers, hdeps, hgr⟩ := visitAppArgs_list
      (fun e => ih.expr i (by omega) e) (hctx'.mono hgf.next) hsc'
      (fun b hb => hargs' b (hsub b hb)) hgf.inv hrun'
    obtain ⟨q', rest', rfl⟩ : ∃ q' rest', as' = q' :: rest' := by
      rcases as' with _ | ⟨q', rest'⟩
      · simp at hlen
      · exact ⟨_, _, rfl⟩
    refine ⟨Erases.quotLift (α := x0) (r := x1) (β := x2) (h := x4) (extra := rest) hqv rfl herf
      (hers 0 _ _ rfl rfl) (by simpa using hlen) (fun i a a' h1 h2 => hers (i + 1) a a' h1 h2),
      deps_mkApps_intro (ErasesDeps.ext hgr.ext hdf) hdeps, hgf.trans hgr, ?_⟩
    rw [AbsFV.closedn_mkApps]
    exact ⟨closed_of_arg hctx' hargs' (.tail _ (.tail _ (.tail _ (.head _)))) herf,
      closed_of_args (hctx'.mono hgf.next) hargs' hsub hlen hers⟩

/-- The `quot` step (`StepsB.quot`): an application or a constant whose head is `Quot.mk` or
`Quot.lift`, through `visitApp_quot`; when the oracle erases the spine, `Erases.box`. Reference:
DV-29. -/
theorem stepsB_quot {fuel : Nat} {e : Expr} {c : Name} {us : List Level} {qv : QuotVal}
    (hG : CoreEnv E B P decls view cfg) (ih : StepIH E B view cfg decls fuel)
    (hfn : e.getAppFn = .const c us) (hci : casesInfo? decls c = none)
    (hca : ctorArity? decls c = none) (hqv : findDecl decls c = some (.quotInfo qv))
    (hqs : (quotEvalArity qv.kind).isSome) :
    ExprSpec E B view cfg decls (fuel + 1) e := by
  intro lps n Γ Δ S t st tc ps r st' ps' hctx hsc hocc hmf hnp hrf hok he ht hrun
  cases e with
  | app f a =>
    rw [visitExpr] at hrun
    rcases oracle_run hrun with ⟨hor, rfl, rfl, rfl⟩ | ⟨-, hrun⟩
    · exact visitExpr_box hG hctx hok he ht hor
    exact visitApp_quot hG ih hfn hci hca hqv hqs hctx hsc hocc hmf hnp hrf hok he ht hrun
  | const c' us' =>
    rw [visitExpr] at hrun
    rcases oracle_run hrun with ⟨hor, rfl, rfl, rfl⟩ | ⟨-, hrun⟩
    · exact visitExpr_box hG hctx hok he ht hor
    exact visitApp_quot hG ih hfn hci hca hqv hqs hctx hsc hocc hmf hnp hrf hok he ht hrun
  | _ => simp [Expr.getAppFn] at hfn

end
end Steps

end EraseProof
