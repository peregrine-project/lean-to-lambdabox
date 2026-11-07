import EraseProof.Relation.Extend

/-!
# Restricting evaluation to a dependency-closed sub-environment

An evaluation in the program `P` of a term whose constants lie in a dependency-closed
sub-environment `decls` is an evaluation in `decls`, and the constants of its result lie in
`decls` (`SrcEval.restrict`). Every rule reads, about a constant or the structure of a projection
of the term, only what `decls` and `P` agree on (`Extend`), and the terms it moves into the result
come from the term or from a value or a type that `decls` reads (`DepClosed`).
-/

open Lean Erasure

namespace EraseProof

namespace Restrict

open Extend

variable {D P : List ConstantInfo} {a : ConstantInfo → Bool}

/-- The head constant of a term whose constants lie in `D` is in `D`. -/
theorem head_mem {x : Expr} {c : Name} {us : List Level}
    (hx : ConstsIn (fun c => (findDecl D c).isSome) x) (h : x.getAppFn = .const c us) :
    (findDecl D c).isSome := by
  have := ConstsIn_getAppFn hx
  rw [h] at this
  exact this

/-- Short spines agree on terms whose constants lie in the sub-environment. -/
theorem shortSpine_iff (hsub : SubEnv D P) (hcl : DepClosed D) {x : Expr}
    (hx : ConstsIn (fun c => (findDecl D c).isSome) x) :
    ShortSpine ⟨D, a⟩ x ↔ ShortSpine ⟨P, a⟩ x := by
  constructor
  · rintro ⟨c, us, ar, hfn, hs, hn⟩
    exact ⟨c, us, ar, hfn, (specialArity_agree hsub hcl (head_mem hx hfn)).symm.trans hs, hn⟩
  · rintro ⟨c, us, ar, hfn, hs, hn⟩
    exact ⟨c, us, ar, hfn, (specialArity_agree hsub hcl (head_mem hx hfn)).trans hs, hn⟩

/-- Atom spines of the program are atom spines of the sub-environment. -/
theorem AtomSpine.restrict (hsub : SubEnv D P) (hcl : DepClosed D) {x : Expr}
    (h : AtomSpine ⟨P, a⟩ x) (hx : ConstsIn (fun c => (findDecl D c).isSome) x) :
    AtomSpine ⟨D, a⟩ x := by
  induction h with
  | const ha => exact .const ((isAtom_agree hsub hcl hx).trans ha)
  | app _ ih => exact .app (ih hx.1)

/-- `Prop` inductives agree on the sub-environment's names. -/
theorem propInd_agree (hsub : SubEnv D P) {S : Name} (hS : (findDecl D S).isSome) :
    EvalEnv.propInd ⟨D, a⟩ S = EvalEnv.propInd ⟨P, a⟩ S := by
  unfold EvalEnv.propInd
  dsimp only
  rw [findDecl_agree hsub hS]

/-- Neutral proofs of the program are neutral proofs of the sub-environment. -/
theorem PropProj.restrict (hsub : SubEnv D P) (hcl : DepClosed D) {x : Expr}
    (h : PropProj ⟨P, a⟩ x) (hx : ConstsIn (fun c => (findDecl D c).isSome) x) :
    PropProj ⟨D, a⟩ x := by
  induction h with
  | proj hS hA =>
    exact .proj ((propInd_agree hsub hx.1).trans hS) (AtomSpine.restrict hsub hcl hA hx.2)
  | projProj hS _ ih => exact .projProj ((propInd_agree hsub hx.1).trans hS) (ih hx.2)
  | app _ ih => exact .app (ih hx.1)

/-- A constructor value of the program is one of the sub-environment, and its fields' constants
lie in the sub-environment. -/
theorem CtorValue.restrict (hsub : SubEnv D P) {T : Name} {m : Expr} {i : Nat} {fs : List Expr}
    (h : CtorValue ⟨P, a⟩ T m i fs) (hm : ConstsIn (fun c => (findDecl D c).isSome) m) :
    CtorValue ⟨D, a⟩ T m i fs ∧ ∀ x ∈ fs, ConstsIn (fun c => (findDecl D c).isSome) x := by
  obtain ⟨C, us, cv, ps, hC, h1, h2, h3, h4, rfl⟩ := h
  have ⟨hCD, has⟩ := ConstsIn_mkAppN.1 hm
  exact ⟨⟨C, us, cv, ps, (findDecl_agree hsub hCD).trans hC, h1, h2, h3, h4, rfl⟩,
    fun x hx => has x (List.mem_append_right _ hx)⟩

/-- The statement of a spine whose constants lie in the sub-environment is the same. -/
theorem spineType?_agree (hsub : SubEnv D P) {x : Expr}
    (hx : ConstsIn (fun c => (findDecl D c).isSome) x) :
    EvalEnv.spineType? ⟨D, a⟩ x = EvalEnv.spineType? ⟨P, a⟩ x := by
  unfold EvalEnv.spineType?
  split
  next h us hfn => dsimp only; rw [findDecl_agree hsub (head_mem hx hfn)]
  next => rfl

/-- Heads that block `appCong` in the sub-environment block it in the program. -/
theorem BlocksCong_sub (hsub : SubEnv D P) (hcl : DepClosed D) {x : Expr}
    (hx : ConstsIn (fun c => (findDecl D c).isSome) x) (h : BlocksCong ⟨D, a⟩ x) :
    BlocksCong ⟨P, a⟩ x := by
  have key : ((∃ c us cv, x.getAppFn = .const c us ∧ findDecl D c = some (.ctorInfo cv)) ∨
      (∃ c us iv, x.getAppFn = .const c us ∧ EvalEnv.casesOn? ⟨D, a⟩ c = some iv) ∨
      (∃ c us qv, x.getAppFn = .const c us ∧ findDecl D c = some (.quotInfo qv))) →
      (∃ c us cv, x.getAppFn = .const c us ∧ findDecl P c = some (.ctorInfo cv)) ∨
      (∃ c us iv, x.getAppFn = .const c us ∧ EvalEnv.casesOn? ⟨P, a⟩ c = some iv) ∨
      (∃ c us qv, x.getAppFn = .const c us ∧ findDecl P c = some (.quotInfo qv)) := by
    rintro (⟨c, us, cv, hfn, hcv⟩ | ⟨c, us, iv, hfn, hco⟩ | ⟨c, us, qv, hfn, hqv⟩)
    · exact .inl ⟨c, us, cv, hfn, findDecl_sub hsub hcv⟩
    · exact .inr (.inl ⟨c, us, iv, hfn,
        (casesOn?_agree hsub hcl (head_mem hx hfn) a a).symm.trans hco⟩)
    · exact .inr (.inr ⟨c, us, qv, hfn, findDecl_sub hsub hqv⟩)
  cases x with
  | lam | sort | forallE | lit => trivial
  | bvar | fvar | mvar | const | app | letE | mdata | proj => exact key h

/-- The inductive of a recognized `casesOn` is a declaration of the environment. -/
theorem casesOn?_mem {σ : EvalEnv} {c : Name} {iv : InductiveVal} (h : σ.casesOn? c = some iv) :
    ConstantInfo.inductInfo iv ∈ σ.decls := by
  unfold EvalEnv.casesOn? at h
  split at h
  next ci _ =>
    split at h
    next iv' hf => cases h; exact (findDecl_eq_some hf).1
    next => cases h
  next => cases h

/-- The constants of a δ-unfolding in the sub-environment lie in it. -/
theorem unfold?_consts (hcl : DepClosed D) {c : Name} {ci : ConstantInfo} {body : Expr}
    (h : EvalEnv.unfold? ⟨D, a⟩ c = some (ci, body)) :
    ConstsIn (fun c => (findDecl D c).isSome) body := by
  unfold EvalEnv.unfold? at h
  split at h
  next d hd =>
    split at h
    next => cases h
    next hno =>
      cases h
      refine (hcl _ (findDecl_eq_some hd).1).1 _ (.inr (.inl ⟨d, rfl, rfl, ?_⟩))
      have hn : d.name = c := (findDecl_eq_some hd).2
      rw [hn]
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, Option.isSome_eq_false_iff] at hno
      exact hno.2
  next => cases h

/-- The η-expansions of a spine of the sub-environment agree. -/
theorem etaSpine?_agree (hsub : SubEnv D P) (hcl : DepClosed D) {c : Name} {us : List Level}
    {as : List Expr} (hc : (findDecl D c).isSome) :
    EvalEnv.etaSpine? ⟨D, a⟩ c us as = EvalEnv.etaSpine? ⟨P, a⟩ c us as := by
  unfold EvalEnv.etaSpine?
  dsimp only
  rw [findDecl_agree hsub hc, specialArity_agree hsub hcl hc]

/-- The constructors of the inductive of a recognized `casesOn` of the sub-environment lie in it. -/
theorem ctor_mem_of_casesOn? (hcl : DepClosed D) {c n : Name} {iv : InductiveVal}
    (h : EvalEnv.casesOn? ⟨D, a⟩ c = some iv) (hn : n ∈ iv.ctors) : (findDecl D n).isSome :=
  (hcl _ (casesOn?_mem h)).2.2.1 iv rfl n hn

/-- A `mapM` into `Option` that succeeds with `f` succeeds with the same results with any `g`
that agrees with `f` on the list where `f` succeeds. -/
theorem mapM_restrict {α β : Type} {f g : α → Option β} :
    ∀ {l : List α} {r : List β}, (∀ x ∈ l, ∀ y, f x = some y → g x = some y) →
      l.mapM f = some r → l.mapM g = some r
  | [], _, _, h => h
  | x :: l, r, hfg, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h ⊢
    obtain ⟨y, hy, ys, hys, rfl⟩ := h
    exact ⟨y, hfg x (.head _) y hy, ys, mapM_restrict (fun z hz => hfg z (.tail _ hz)) hys, rfl⟩

/-- A result of a successful `mapM` is the image of an element. -/
theorem mem_mapM {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM f = some r → ∀ y ∈ r, ∃ x ∈ l, f x = some y
  | [], r, h, y, hy => by simp at h; subst h; cases hy
  | x :: l, r, h, y, hy => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨z, hz, zs, hzs, rfl⟩ := h
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨x, .head _, hz⟩
    · obtain ⟨x', hx', h'⟩ := mem_mapM hzs y hy
      exact ⟨x', .tail _ hx', h'⟩

/-- The block of a recursor of the sub-environment, read in the program, is read the same in the
sub-environment: its inductives and their constructors lie in it (`DepClosed`). -/
theorem recBlock?_restrict (hsub : SubEnv D P) (hcl : DepClosed D) {c : Name} {rv : RecursorVal}
    (hr : findDecl D c = some (.recInfo rv)) {r}
    (h : EvalEnv.recBlock? ⟨P, a⟩ rv = some r) : EvalEnv.recBlock? ⟨D, a⟩ rv = some r := by
  obtain ⟨-, -, -, -, hrall⟩ := hcl _ (findDecl_eq_some hr).1
  have hall := hrall rv rfl
  unfold EvalEnv.recBlock? at h ⊢
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h ⊢
  obtain ⟨ivs, hivs, cvs, hcvs, rfl⟩ := h
  refine ⟨ivs, mapM_restrict (fun t ht y hy => ?_) hivs, cvs,
    mapM_restrict (fun x hx y hy => ?_) hcvs, rfl⟩
  · unfold EvalEnv.indOf? at hy ⊢
    rw [findDecl_agree hsub (hall t ht)]; exact hy
  · obtain ⟨iv, hiv, hx'⟩ := List.mem_flatMap.1 hx
    obtain ⟨t, ht, hti⟩ := mem_mapM hivs iv hiv
    have hiv' : findDecl P t = some (.inductInfo iv) := by
      revert hti
      unfold EvalEnv.indOf?
      cases findDecl P t with
      | none => intro h; cases h
      | some ci => cases ci <;> intro h <;> simp at h; subst h; rfl
    rw [← findDecl_agree hsub (hall t ht)] at hiv'
    obtain ⟨-, -, hctors, -, -⟩ := hcl _ (findDecl_eq_some hiv').1
    unfold EvalEnv.ctorOf? at hy ⊢
    rw [findDecl_agree hsub (hctors iv rfl x hx')]
    exact hy

end Restrict

open Restrict Extend in
/-- Evaluation in the program restricts to a dependency-closed sub-environment that contains the
constants of the term, and the result's constants lie in it. Reference: weakening of the global
environment for evaluation (`MR E/EWcbvEval.v`, `eval_weakening`), read in the restricting
direction. -/
theorem SrcEval.restrict {decls P : List ConstantInfo} {e v : Expr} {view : EnvView}
    {cfg : ErasureConfig} (hsub : SubEnv decls P)
    (hcl : DepClosed decls) (hc : ConstsIn (fun c => (findDecl decls c).isSome) e)
    (hev : SrcEval (evalEnvOf view cfg P) e v) :
    SrcEval (evalEnvOf view cfg decls) e v ∧ ConstsIn (fun c => (findDecl decls c).isSome) v := by
  have mem : ∀ {l : List Expr} {i : Nat} {x : Expr}, l[i]? = some x → x ∈ l :=
    fun h => List.mem_of_getElem? h
  have agreeCases : ∀ {c : Name} {iv : InductiveVal}, (findDecl decls c).isSome →
      (evalEnvOf view cfg P).casesOn? c = some iv →
      EvalEnv.casesOn? ⟨decls, axiomatized view cfg⟩ c = some iv := fun hcD hco =>
    (casesOn?_agree hsub hcl hcD (axiomatized view cfg) (axiomatized view cfg)).trans hco
  revert hc
  induction hev with
  | beta hns _ _ _ ihf iha ihb =>
    intro hc
    obtain ⟨ef, hlam⟩ := ihf hc.1
    obtain ⟨ea, ha'⟩ := iha hc.2
    obtain ⟨eb, hv⟩ := ihb (ConstsIn_instantiate1' ha' hlam.2)
    exact ⟨.beta (fun hs => hns ((shortSpine_iff hsub hcl hc).1 hs)) ef ea eb, hv⟩
  | zeta _ _ ihv ihb =>
    intro hc
    obtain ⟨ev, hv'⟩ := ihv hc.2.1
    obtain ⟨eb, hv⟩ := ihb (ConstsIn_instantiate1' hv' hc.2.2)
    exact ⟨.zeta ev eb, hv⟩
  | delta hu _ ih =>
    intro hc
    have hu' := (unfold?_agree (a := axiomatized view cfg) hsub hcl hc).trans hu
    obtain ⟨eb, hv⟩ := ih (ConstsIn_instLevels (unfold?_consts hcl hu'))
    exact ⟨.delta hu' eb, hv⟩
  | constAtom ha =>
    intro hc
    exact ⟨.constAtom ((isAtom_agree (a := axiomatized view cfg) hsub hcl hc).trans ha), hc⟩
  | eta he =>
    intro hc
    have he' := (etaSpine?_agree (a := axiomatized view cfg) hsub hcl
      (ConstsIn_mkAppN.1 hc).1).trans he
    exact ⟨.eta he', (etaSpine?_sub hsub hcl he' hc).2⟩
  | @ctor c cv us as vs hcv hl hlv _ ih =>
    intro hc
    have ⟨hcD, has⟩ := ConstsIn_mkAppN.1 hc
    refine ⟨.ctor ((findDecl_agree hsub hcD).trans hcv) hl hlv
      fun i x w hx hw => (ih i x w hx hw (has x (mem hx))).1, ConstsIn_mkAppN.2 ⟨hcD, ?_⟩⟩
    intro w hw
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
    have hx : as[i]? = some as[i] := List.getElem?_eq_getElem (by omega)
    exact (ih i _ _ hx (List.getElem?_eq_getElem hi) (has _ (mem hx))).2
  | casesIota hco hlen hm _ hcv halt _ ihm iha =>
    intro hc
    have ⟨hcD, has⟩ := ConstsIn_mkAppN.1 hc
    obtain ⟨em, hmv⟩ := ihm (has _ (mem hm))
    obtain ⟨hcv', hfs⟩ := CtorValue.restrict hsub hcv hmv
    obtain ⟨ea, hv⟩ := iha (ConstsIn_mkAppN.2 ⟨has _ (mem halt), hfs⟩)
    exact ⟨.casesIota (agreeCases hcD hco) hlen hm em hcv' halt ea, hv⟩
  | casesLitZero hco hN hlen hm _ halt _ ihm iha =>
    intro hc
    have ⟨hcD, has⟩ := ConstsIn_mkAppN.1 hc
    obtain ⟨ea, hv⟩ := iha (has _ (mem halt))
    exact ⟨.casesLitZero (agreeCases hcD hco) hN hlen hm (ihm (has _ (mem hm))).1 halt ea, hv⟩
  | casesLitSucc hco hN hlen hm _ halt _ ihm iha =>
    intro hc
    have ⟨hcD, has⟩ := ConstsIn_mkAppN.1 hc
    obtain ⟨ea, hv⟩ := iha ⟨has _ (mem halt), trivial⟩
    exact ⟨.casesLitSucc (agreeCases hcD hco) hN hlen hm (ihm (has _ (mem hm))).1 halt ea, hv⟩
  | casesProof hco hlen hm _ hat hsl hez hct hcn hnf hst hps hpi halt _ ihm iha =>
    intro hc
    have ⟨hcD, has⟩ := ConstsIn_mkAppN.1 hc
    have hco' := agreeCases hcD hco
    obtain ⟨em, hmv⟩ := ihm (has _ (mem hm))
    obtain ⟨ea, hv⟩ := iha (has _ (mem halt))
    have hcnD := ctor_mem_of_casesOn? hcl hco' (hct ▸ List.mem_singleton_self _)
    exact ⟨.casesProof hco' hlen hm em (AtomSpine.restrict hsub hcl hat hmv) hsl hez hct
      ((findDecl_agree hsub hcnD).trans hcn) hnf ((spineType?_agree hsub hmv).trans hst) hps hpi
      halt ea, hv⟩
  | quotMk hcq hk _ ih =>
    intro hc
    have ⟨hcD, has⟩ := ConstsIn_mkAppN.1 hc
    obtain ⟨ea, ha'⟩ := ih (has _ (by simp))
    refine ⟨.quotMk ((findDecl_agree hsub hcD).trans hcq) hk ea, ConstsIn_mkAppN.2 ⟨hcD, ?_⟩⟩
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact has _ (by simp)
    · exact has _ (by simp)
    · exact ha'
  | quotLift hcq hk _ _ hcq' hk' _ ihf ihq ihb =>
    intro hc
    have ⟨hcD, has⟩ := ConstsIn_mkAppN.1 hc
    obtain ⟨ef, hfC⟩ := ihf (has _ (by simp))
    obtain ⟨eq, hqC⟩ := ihq (has _ (by simp))
    have ⟨hcD', has'⟩ := ConstsIn_mkAppN.1 hqC
    obtain ⟨eb, hv⟩ := ihb (ConstsIn_instantiate1' (has' _ (by simp)) hfC.2)
    exact ⟨.quotLift ((findDecl_agree hsub hcD).trans hcq) hk ef eq
      ((findDecl_agree hsub hcD').trans hcq') hk' eb, hv⟩
  | @recIota c rv T iv cvs motives minors maj mj k mi mk us v ps ms mins mvs fs rfs hcr hall hcT
      hblk hni hshape hihs hps hms hmins hlm _ _ hcv hmi hmk hrfs _ ihmin ihmaj ihb =>
    intro hc
    have ⟨hcD, has⟩ := ConstsIn_mkAppN.1 hc
    have hcr' := (findDecl_agree hsub hcD).trans hcr
    have hmv : ∀ i m mv, mins[i]? = some m → mvs[i]? = some mv →
        SrcEval (evalEnvOf view cfg decls) m mv ∧ ConstsIn (fun c => (findDecl decls c).isSome) mv :=
      fun i m mv h1 h2 => ihmin i m mv h1 h2 (has m (by simp [mem h1]))
    obtain ⟨em, hmjC⟩ := ihmaj (has _ (by simp))
    obtain ⟨hcv', hfs⟩ := CtorValue.restrict hsub hcv hmjC
    have hmvC : ∀ x ∈ mvs, ConstsIn (fun c => (findDecl decls c).isSome) x := fun x hx => by
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      obtain ⟨m, hm⟩ : ∃ m, mins[i]? = some m := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      exact (hmv i m _ hm (List.getElem?_eq_getElem hi)).2
    have hK : ConstsIn (fun c => (findDecl decls c).isSome) (mkAppN mk (fs ++ rfs.map fun f =>
        mkAppN (.const c us) (ps ++ ms ++ mvs ++ [f]).toArray).toArray) := by
      refine ConstsIn_mkAppN.2 ⟨hmvC _ (List.mem_of_getElem? hmk), fun x hx => ?_⟩
      rcases List.mem_append.1 hx with hx | hx
      · exact hfs x hx
      · obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hx
        refine ConstsIn_mkAppN.2 ⟨hcD, fun y hy => ?_⟩
        rcases List.mem_append.1 hy with hy | hy
        · rcases List.mem_append.1 hy with hy | hy
          · exact has y (List.mem_append_left _ (List.mem_append_left _ hy))
          · exact hmvC y hy
        · rw [List.mem_singleton.1 hy]
          obtain ⟨h, -, hh⟩ := mem_mapM hrfs f hf
          exact hfs f (List.mem_of_getElem? hh)
    obtain ⟨eb, hv⟩ := ihb hK
    exact ⟨.recIota hcr' hall hcT (recBlock?_restrict hsub hcl hcr' hblk) hni hshape hihs hps
      hms hmins hlm (fun i m mv h1 h2 => (hmv i m mv h1 h2).1) em hcv' hmi hmk hrfs eb, hv⟩
  | proj _ hcv hfs ihm =>
    intro hc
    obtain ⟨em, hmv⟩ := ihm hc.2
    obtain ⟨hcv', hfsC⟩ := CtorValue.restrict hsub hcv hmv
    exact ⟨.proj em hcv' hfs, hfsC _ (mem hfs)⟩
  | projProp hS _ hm ihm =>
    intro hc
    obtain ⟨em, hmv⟩ := ihm hc.2
    refine ⟨.projProp ((propInd_agree hsub hc.1).trans hS) em ?_, hc.1, hmv⟩
    rcases hm with hm | hm
    · exact .inl (AtomSpine.restrict hsub hcl hm hmv)
    · exact .inr (PropProj.restrict hsub hcl hm hmv)
  | lit => intro hc; exact ⟨.lit, hc⟩
  | appCong hns _ hb _ ihf iha =>
    intro hc
    obtain ⟨ef, hf'⟩ := ihf hc.1
    obtain ⟨ea, ha'⟩ := iha hc.2
    exact ⟨.appCong (fun hs => hns ((shortSpine_iff hsub hcl hc).1 hs)) ef
      (fun hb' => hb (BlocksCong_sub hsub hcl hf' hb')) ea, hf', ha'⟩
  | mdata _ ih =>
    intro hc
    obtain ⟨e1, hv⟩ := ih hc
    exact ⟨.mdata e1, hv⟩
  | atom h => intro hc; exact ⟨.atom h, hc⟩

end EraseProof
