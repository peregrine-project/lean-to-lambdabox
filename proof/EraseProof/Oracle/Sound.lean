import EraseProof.Oracle.InferProj
import EraseProof.Oracle.Atom
import EraseProof.Erasable.Atom

/-!
# Soundness of the oracle's type inference and erasability test

`Pure.inferType_sound`: `OracleInfer.inferOK` at the empty oracle context, with the projection
cases: a structure projection by `OracleInfer.infer_projStruct`; a proof projection
(`TrM.projProof`, an inductive that is not a structure) never reaches the oracle's answer, since the
oracle types a projection only when the recursor of the projected inductive has a universe
parameter for the motive, which `IndBlock.recr` and `RecrLevels` tie to large elimination, and a
large-eliminating inductive with the premises of `TrM.projProof` is a structure.

`Pure.isErasable_sound`: the oracle's `true` is sound, on a spine headed by a theorem (a proof),
when the inferred type is an arity (`Pure.isArity_sound`), and when the sort of the inferred type
is always zero (`Pure.alwaysZero`, a proposition).

`Pure.typeLevel_sound`: the oracle's level of a term's type is a level of that type.
`TrLevel.isNeverZero_iff`: `Level.isNeverZero` decides, on translated levels, whether the level is
non-zero under every assignment.
-/

open Lean Erasure
open Metalean (Defeq TypeEq EnvWF)

namespace EraseProof

namespace OracleSound

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {lps : List Name}
  {P : List ConstantInfo} {cx : Pure.Ctx}

/-- The levels a recursor's image reads: the motive's level comes first exactly when the block is
large-eliminating (`RecrLevels`), and the rest are the block's levels. -/
private theorem satTr_recr_levels {ι : Metalean.IndSig} {η : Metalean.Head ζ (.inductive ι)}
    {s : Fin ι.nsorts} {os : List (List (List Nat))} {us : List Level} {n : Nat}
    {args : List (Metalean.Expr ζ lps.length n)} {t : Metalean.Expr ζ lps.length n}
    (h : SatTr E lps (.recr η s os) us args t) :
    ∃ l us' ls, RecrLevels (E.get η).block lps us l us' ∧ TrLevels lps us' ι.nlevels = some ls := by
  cases h with
  | recrSat _ _ _ _ hRL hls => exact ⟨_, _, _, hRL, hls⟩
  | recrEta _ hRL hls => exact ⟨_, _, _, hRL, hls⟩

/-- The levels of a recursor constant's image (`satTr_recr_levels` on the empty spine). -/
private theorem recr_const_levels {lps' : List Name} {c : Name} {us : List Level}
    {ι : Metalean.IndSig} {η : Metalean.Head ζ (.inductive ι)} {s : Fin ι.nsorts}
    {os : List (List (List Nat))} {n : Nat} {Γ : Metalean.Ctx ζ lps'.length 0 n}
    {Δ : MLCtx ζ lps'.length n} {t : Metalean.Expr ζ lps'.length n}
    (hb : B c = some (.recr η s os)) (h : TrM E B lps' Γ Δ (.const c us) t) :
    ∃ l us' ls, RecrLevels (E.get η).block lps' us l us' ∧
      TrLevels lps' us' ι.nlevels = some ls := by
  generalize hx : Expr.const c us = x at h
  cases h with
  | const hc _ => cases hx; rw [hb] at hc; cases hc
  | special hb' _ _ _ hsat =>
    obtain ⟨-, rfl, rfl⟩ := SrcDefeq.spine_const hx.symm
    rw [hb] at hb'; cases hb'
    exact satTr_recr_levels hsat
  | _ => cases hx

/-- A one-constructor, index-free, non-recursive inductive of the program that is not a structure
has a recursor with exactly the inductive's universe parameters: the recursor's image reads its
levels by `RecrLevels`, which gives the motive a level of its own only for a large-eliminating
block, and such a block would be a structure. -/
private theorem recr_levels_of_not_structure (henv : ProgEnv P ζ E B) (hE : EnvWF E)
    (hsub : SubEnv cx.decls P) {S : Name} {ι : Metalean.IndSig}
    {η : Metalean.Head ζ (.inductive ι)} {s : Fin ι.nsorts} {c : Fin (ι.nctors s)}
    (hBS : B S = some (.ind η s)) (hs : ∀ t : Fin ι.nsorts, t = s)
    (hc : ∀ d : Fin (ι.nctors s), d = c) (hi : ι.nindices s = 0)
    (hnr : (ι.ctors s c).nrecFields = 0) (hnst : ¬ (E.get η).block.IsStructure s c)
    {I : InductiveVal} {R : RecursorVal} (hfS : findConst cx.decls S = some (.inductInfo I))
    (hfR : findConst cx.decls (mkRecName S) = some (.recInfo R)) :
    R.levelParams.length = I.levelParams.length := by
  have hPI := OracleWhnf.findConst_sub hsub hfS
  have hPR := OracleWhnf.findConst_sub hsub hfR
  obtain ⟨lps₀, Is, Cs, Rs, orders, ⟨_, _, _, _, hIB⟩, -, hfd, hrec, hindB, -⟩ :=
    CasesWhred.ProgEnv.block henv η
  have hT : S = (Is s).name := hindB _ _ hBS
  have hII : I = Is s := by
    have h1 : findDecl P (Is s).name = some (.inductInfo (Is s)) :=
      hfd (.inductInfo (Is s)) (by simp [IndBlock.decls, List.mem_ofFn])
    rw [← hT, hPI] at h1
    cases h1; rfl
  subst hII
  obtain ⟨-, hlpI, -⟩ := hIB.ind s
  have hBR : B (mkRecName S) = some (.recr η s
      (List.ofFn fun t => List.ofFn fun c => orders t c)) := by
    rw [hT, ← (hIB.recr s).1]; exact hrec s
  obtain ⟨_, -, _, _, -, htr, -⟩ := henv.lookup hE hPR
  have hname : R.name = mkRecName S := (findDecl_eq_some hPR).2
  obtain ⟨l, us', ls, hRL, hls⟩ :=
    recr_const_levels (by rw [hname]; exact hBR : B R.name = some _) htr
  obtain ⟨hk, -⟩ := TrLevels_get hls
  rw [hlpI, hIB.levels]
  rcases hRL with ⟨hL, -⟩ | ⟨-, rfl, -⟩
  · exact (hnst ⟨hs, hc, by rw [hi]; infer_instance, by rw [hnr]; infer_instance, hL s⟩).elim
  · have hlp : (ConstantInfo.recInfo R).levelParams = R.levelParams := rfl
    simpa [hlp] using hk

/-- In the `TrM.projProof` case the oracle fails: the projected inductive is not a structure, so
its recursor has no universe parameter for the motive, and the oracle throws. -/
theorem infer_projProof_ne (henv : ProgEnv P ζ E B) (hE : EnvWF E)
    (hsub : SubEnv cx.decls P) {S : Name} {ι : Metalean.IndSig}
    {η : Metalean.Head ζ (.inductive ι)} {s : Fin ι.nsorts} {c : Fin (ι.nctors s)}
    (hBS : B S = some (.ind η s)) (hs : ∀ t : Fin ι.nsorts, t = s)
    (hc : ∀ d : Fin (ι.nctors s), d = c) (hi : ι.nindices s = 0)
    (hnr : (ι.ctors s c).nrecFields = 0) (hnst : ¬ (E.get η).block.IsStructure s c)
    {f : Nat} {ls : List Local} {Γo : List Expr} {i : Nat} {e A : Expr} :
    Pure.inferType cx (f + 1) ls Γo (.proj S i e) ≠ .ok A := by
  intro h
  simp only [Pure.inferType] at h
  obtain ⟨Ts, -, h⟩ := OracleWhnf.ok_of_bind h
  obtain ⟨W, -, h⟩ := OracleWhnf.ok_of_bind h
  generalize spine W = p at h
  obtain ⟨hd, args⟩ := p
  cases hd with
  | const S' us =>
    simp only at h
    split at h
    · rename_i I R hSS hfS hfR
      obtain rfl : S' = S := beq_iff_eq.mp hSS
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
      · rename_i hne
        exact hne (beq_iff_eq.mpr
          (recr_levels_of_not_structure henv hE hsub hBS hs hc hi hnr hnst hfS hfR))
    · simp [throw, throwThe, MonadExceptOf.throw] at h
  | _ => simp [throw, throwThe, MonadExceptOf.throw] at h

/-- `inferOK`'s projection premise: a structure projection by `infer_projStruct`, a proof
projection by `infer_projProof_ne`. -/
private theorem infer_proj (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv cx.decls P)
    {ls : List Local} (f : Nat) (ih : OracleInfer.InferOK E B lps cx ls f) {n : Nat}
    {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n} {Γo : List Expr} {S : Name}
    {i : Nat} {e A : Expr} {t U : Metalean.Expr ζ lps.length n} (hΓ : E[Γ] ⊢ ok)
    (hloc : LocalsOK E B lps Γ Δ ls) (hΓo : OracleInfer.OracleCtx (E := E) (B := B) Γ Δ Γo)
    (he : TrM E B lps Γ Δ (.proj S i e) t) (ht : E[Γ] ⊢ t : U)
    (h : Pure.inferType cx (f + 1) ls Γo (.proj S i e) = .ok A) :
    ∃ A', TrM E B lps Γ Δ A A' ∧ E[Γ] ⊢ t : A' := by
  generalize hx : Expr.proj S i e = x at he
  cases he with
  | projStruct hst hi hBS he' hty =>
    cases hx
    exact OracleInfer.infer_projStruct henv hE hsub ih hΓ hloc hΓo hst hi hBS he' hty ht h
  | projProof hi hBS hs hc hnr _ hnst =>
    cases hx
    exact absurd h (infer_projProof_ne henv hE hsub hBS hs hc hi hnr hnst)
  | special => exact absurd hx (CasesWhred.ne_mkAppN_const fun _ _ h => by cases h)
  | _ => cases hx


/-- The oracle's answer: a spine headed by a theorem, or the steps after the theorem test (the
inferred type, the arity test, and otherwise the sort test). -/
theorem isErasable_cases {fuel : Nat} {ls : List Local} {e : Expr} {b : Bool}
    (h : Pure.isErasable cx fuel ls e = .ok b) :
    (∃ c us v, (spine e).1 = .const c us ∧ findConst cx.decls c = some (.thmInfo v)) ∨
    ∃ T ba, Pure.inferType cx fuel ls [] e = .ok T ∧ Pure.isArity cx fuel ls T = .ok ba ∧
      (ba = true → b = true) ∧
      (ba = false → ∃ S w, Pure.inferType cx fuel ls [] T = .ok S ∧
        Pure.whnf cx fuel ls S = .ok w ∧
        ((∃ u, w = .sort u ∧ b = Pure.alwaysZero u) ∨ ((∀ u, w ≠ .sort u) ∧ b = false))) := by
  by_cases hth : ∃ c us v, (spine e).1 = .const c us ∧ findConst cx.decls c = some (.thmInfo v)
  · exact .inl hth
  refine .inr ?_
  unfold Pure.isErasable at h
  simp only at h
  split at h
  split at h
  · exact (hth ⟨_, _, _, by rw [‹spine e = _›], ‹findConst _ _ = _›⟩).elim
  all_goals
    obtain ⟨T, h1, h⟩ := OracleWhnf.ok_of_bind h
    obtain ⟨ba, h2, h⟩ := OracleWhnf.ok_of_bind h
    refine ⟨T, ba, h1, h2, fun hb => ?_, fun hb => ?_⟩
    · subst hb; simpa [pure, Except.pure] using h.symm
    · subst hb
      simp only [Bool.false_eq_true, ite_false] at h
      obtain ⟨S, h3, h⟩ := OracleWhnf.ok_of_bind h
      obtain ⟨w, h4, h⟩ := OracleWhnf.ok_of_bind h
      refine ⟨S, w, h3, h4, ?_⟩
      split at h
      · exact .inl ⟨_, rfl, by simpa [pure, Except.pure] using h.symm⟩
      · rename_i hns
        exact .inr ⟨fun u hu => hns u hu, by simpa [pure, Except.pure] using h.symm⟩

/-- A spine headed by a theorem is erasable: the theorem's statement translates to a proposition
(`ErasableAtom.lookup_thm`), so the head's image is a proof, and so is every application of it. -/
private theorem isErasable_thm (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv cx.decls P)
    {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n} (hΓ : E[Γ] ⊢ ok)
    {e : Expr} {c : Name} {us : List Level} {ci : ConstantInfo}
    (hsp : (spine e).1 = .const c us) (hf : findConst cx.decls c = some ci)
    (hthm : ∃ v, ci = .thmInfo v)
    {t U : Metalean.Expr ζ lps.length n} (he : TrM E B lps Γ Δ e t) (ht : E[Γ] ⊢ t : U) :
    IsErasable E Γ t := by
  have hcP := OracleWhnf.findConst_sub hsub hf
  have hnd := henv.levelParams_nodup (findDecl_eq_some hcP).1
  have hname : ci.name = c := (findDecl_eq_some hcP).2
  obtain ⟨b, hb, Tc, tc, hTc, htc, htcT⟩ := henv.lookup hE hcP
  have hs : b.isSpecial = false := by
    cases hs' : b.isSpecial
    · rfl
    · obtain ⟨v, rfl⟩ := hthm
      rcases SrcDefeq.special_kind henv hb hs' hcP with ⟨_, h'⟩ | ⟨_, h'⟩ | ⟨_, h'⟩ | ⟨_, h'⟩ <;>
        cases h'
  have hns : ¬ SpecialHead B (.const c us) := by
    rintro ⟨c', us', b', hfn', hb', hs'⟩
    cases hfn'
    rw [hb] at hb'
    cases hb'; rw [hs] at hs'; cases hs'
  rw [← CasesShape.spine_mkAppN e, hsp] at he
  obtain ⟨h', as', hh, -, rfl⟩ := CasesWhred.trM_spine_inv hns _ he
  cases b with
  | const η =>
    rw [hname] at htc
    obtain ⟨ls, rfl, hls⟩ := SrcDefeq.trM_const_inv' hb hh
    obtain ⟨ls₀, rfl, hls₀⟩ := SrcDefeq.trM_const_inv' hb htc
    obtain ⟨hk, hls₀'⟩ := SrcDefeq.trLevels_params_nodup hnd hls₀
    obtain ⟨ls', -, hls'⟩ := SrcDefeq.trLevels_cast hls hk
    have hlseq : ls₀{ls'} = ls := by
      funext i
      show (ls₀ i){ls'} = ls i
      rw [hls₀' i]
      show ls' (Fin.cast hk i) = ls i
      rw [hls']
      rfl
    obtain ⟨_, hreg⟩ := htcT.regular
    obtain ⟨v, rfl⟩ := hthm
    obtain ⟨T₀, hT₀, hT₀p⟩ := ErasableAtom.lookup_thm henv hcP
    have hd := DCong.defeq₂ hE (hT₀.dcong hTc (LocCong.refl [])) SrcDefeq.nil_ok
      SrcDefeq.nil_ok (DCong.CtxConv.refl SrcDefeq.nil_ok) ⟨_, hreg⟩ hT₀p
    have h1 : E[.nil] ⊢ (Metalean.Expr.const η ls₀){ls'} : Tc{ls'} := by
      simpa using Metalean.Defeq.instLevel ls' htcT
    have h2₀ : E[(.nil : Metalean.Ctx ζ (ConstantInfo.thmInfo v).levelParams.length 0 0)] ⊢
        Tc : .prop := hd.right
    have h2 : E[.nil] ⊢ Tc{ls'} : .prop := by
      simpa using Metalean.Defeq.instLevel ls' h2₀
    rw [show (Metalean.Expr.const η ls₀){ls'} = Metalean.Expr.const η ls from by
      rw [← hlseq]; rfl] at h1
    have hc : IsErasable E Γ (Metalean.Expr.const η ls) :=
      ⟨Tc{ls'}.wkClosed, by simpa using Metalean.Defeq.wkClosed (Γ := Γ) h1,
        .inr (by simpa using Metalean.Defeq.wkClosed (Γ := Γ) h2)⟩
    exact ErasableAtom.IsErasable.appList hE hΓ as' hc ht
  | _ => cases hs

end

end OracleSound

open OracleSound in
/-- The oracle's type is a type: the image of the term is typed at a translation of the oracle's
answer. The traversal's locals have no bound entry (`hnb`). Reference: `type_of_typing`
(`MR S/PCUICSafeRetyping.v:806`). -/
theorem Pure.inferType_sound {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ}
    {P : List ConstantInfo} {lps : List Name} {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
    {Δ : MLCtx ζ lps.length n} {cx : Pure.Ctx} {fuel : Nat} {ls : List Local} {e A : Expr}
    {t : Metalean.Expr ζ lps.length n}
    (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv cx.decls P)
    (hΓ : E[Γ] ⊢ ok) (hloc : LocalsOK E B lps Γ Δ ls) (hnb : ∀ i, Δ.findB i = none)
    (he : TrM E B lps Γ Δ e t)
    (ht : ∃ U, E[Γ] ⊢ t : U) (h : Pure.inferType cx fuel ls [] e = .ok A) :
    ∃ A', TrM E B lps Γ Δ A A' ∧ E[Γ] ⊢ t : A' := by
  have hcl : ∀ l ∈ ls, l.type.liftLooseBVars' 0 1 = l.type ∧
      ∀ v, l.value? = some v → v.liftLooseBVars' 0 1 = v := by
    intro l hl
    obtain ⟨T, t, hT, -, -, hv⟩ := hloc l hl
    exact ⟨OracleArity.TrM.lift_eq hT fun i _ => hnb i,
      fun v h' => OracleArity.TrM.lift_eq (hv v h') fun i _ => hnb i⟩
  obtain ⟨U, hU⟩ := ht
  exact OracleInfer.inferOK henv hE hsub hcl (fun f ih => infer_proj henv hE hsub f ih) fuel
    hΓ hloc (fun _ _ h => by simp at h) he hU h

open OracleSound in
/-- The oracle's `true` is sound: the term's image is a type former or a proof. A spine headed by a
theorem is a proof; an inferred type that is an arity makes the term a type former
(`Pure.isArity_sound`); an inferred type whose sort is always zero (`Pure.alwaysZero`, through
`SrcProof.evidentZero_tr`) is a proposition. The traversal's locals have no bound entry (`hnb`).
Reference: `is_erasableb` soundness (`MR E/ErasureFunction.v:894`); port of `L4 Oracle.lean:69`. -/
theorem Pure.isErasable_sound {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ}
    {P : List ConstantInfo} {lps : List Name} {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
    {Δ : MLCtx ζ lps.length n} {cx : Pure.Ctx} {fuel : Nat} {ls : List Local} {e : Expr}
    {t : Metalean.Expr ζ lps.length n}
    (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv cx.decls P)
    (hΓ : E[Γ] ⊢ ok) (hloc : LocalsOK E B lps Γ Δ ls) (hnb : ∀ i, Δ.findB i = none)
    (he : TrM E B lps Γ Δ e t)
    (ht : ∃ T, E[Γ] ⊢ t : T) (h : Pure.isErasable cx fuel ls e = .ok true) :
    ErasableS E B lps Γ Δ e := by
  obtain ⟨U, hU⟩ := ht
  refine ⟨t, he, ?_⟩
  rcases isErasable_cases h with ⟨c, us, v, hsp, hf⟩ | ⟨T, ba, h1, h2, -, hno⟩
  · exact isErasable_thm henv hE hsub hΓ hsp hf ⟨v, rfl⟩ he hU
  obtain ⟨A', hA', htA'⟩ := Pure.inferType_sound henv hE hsub hΓ hloc hnb he ⟨U, hU⟩ h1
  refine ⟨A', htA', ?_⟩
  cases ba
  · obtain ⟨S, w, h3, h4, hw⟩ := hno rfl
    rcases hw with ⟨u, rfl, hz⟩ | ⟨-, hz⟩
    · obtain ⟨_, hA's⟩ := htA'.regular
      obtain ⟨S', hS', hA'S'⟩ := Pure.inferType_sound henv hE hsub hΓ hloc hnb hA' ⟨_, hA's⟩ h3
      obtain ⟨l, hl, hA'l⟩ := OracleInfer.sort_step henv hE hsub hΓ hloc hA'S' hS' h4
      rw [OracleAtom.alwaysZero_eq] at hz
      rw [SrcProof.evidentZero_tr hz.symm hl] at hA'l
      exact .inr hA'l
    · cases hz
  · exact .inl (Pure.isArity_sound henv hE hsub hΓ hloc hnb hA' htA'.regular h2)

/-- The oracle's level of a typed term's type is a level of that type: the image of the term is
typed at a type of the translated sort. Reference: `sort_of_type` (`MR S/PCUICSafeReduce.v:1853`)
of the term's type, as `MR E/ErasureFunction.v:894 is_erasableb` computes it. -/
theorem Pure.typeLevel_sound {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ}
    {P : List ConstantInfo} {lps : List Name} {n : Nat} {Γ : Metalean.Ctx ζ lps.length 0 n}
    {Δ : MLCtx ζ lps.length n} {cx : Pure.Ctx} {fuel : Nat} {ls : List Local} {e : Expr}
    {u : Level} {t : Metalean.Expr ζ lps.length n}
    (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv cx.decls P)
    (hΓ : E[Γ] ⊢ ok) (hloc : LocalsOK E B lps Γ Δ ls) (hnb : ∀ i, Δ.findB i = none)
    (he : TrM E B lps Γ Δ e t) (ht : ∃ T, E[Γ] ⊢ t : T)
    (h : Pure.typeLevel cx fuel ls e = .ok u) :
    ∃ l T, TrLevel lps u = some l ∧ E[Γ] ⊢ t : T ∧ E[Γ] ⊢ T : .sort l := by
  simp only [Pure.typeLevel] at h
  obtain ⟨A, h1, h⟩ := OracleWhnf.ok_of_bind h
  obtain ⟨S, h2, h⟩ := OracleWhnf.ok_of_bind h
  obtain ⟨w, h3, h⟩ := OracleWhnf.ok_of_bind h
  cases w with
  | sort v =>
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨A', hA', htA'⟩ := Pure.inferType_sound henv hE hsub hΓ hloc hnb he ht h1
    obtain ⟨_, hA's⟩ := htA'.regular
    obtain ⟨S', hS', hA'S'⟩ :=
      Pure.inferType_sound henv hE hsub hΓ hloc hnb hA' ⟨_, hA's⟩ h2
    obtain ⟨l, hl, hA'l⟩ := OracleInfer.sort_step henv hE hsub hΓ hloc hA'S' hS' h3
    exact ⟨l, A', hl, htA', hA'l⟩
  | _ => simp [throw, throwThe, MonadExceptOf.throw] at h

namespace OracleSound

/-- A never-zero level translates to a level that is non-zero under every assignment. -/
private theorem eval_ne_zero {lps : List Name} :
    ∀ {u : Level} {l : Metalean.Level lps.length}, TrLevel lps u = some l →
      u.isNeverZero = true → ∀ ν, l.eval ν ≠ 0
  | .zero, _, _, hz => by simp [Level.isNeverZero] at hz
  | .succ a, l, h, _ => by
    simp only [TrLevel, Option.map_eq_some_iff] at h
    obtain ⟨a', -, rfl⟩ := h
    intro ν; simp
  | .max a b, l, h, hz => by
    simp only [TrLevel, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨a', ha, b', hb, rfl⟩ := h
    simp only [Level.isNeverZero, Bool.or_eq_true] at hz
    intro ν
    simp only [Metalean.Level.eval_max]
    unfold Nat.max
    rcases hz with hz | hz
    · have := eval_ne_zero ha hz ν; omega
    · have := eval_ne_zero hb hz ν; omega
  | .imax a b, l, h, hz => by
    simp only [TrLevel, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨a', ha, b', hb, rfl⟩ := h
    simp only [Level.isNeverZero] at hz
    intro ν
    have := eval_ne_zero hb hz ν
    simp only [Metalean.Level.eval_imax, Nat.imax_eq_max this]
    unfold Nat.max
    omega
  | .param _, _, _, hz => by simp [Level.isNeverZero] at hz
  | .mvar _, _, h, _ => by cases h

/-- A level that is not never-zero translates to a level that is zero when every parameter is. -/
private theorem eval_zero_of_not {lps : List Name} :
    ∀ {u : Level} {l : Metalean.Level lps.length}, TrLevel lps u = some l →
      u.isNeverZero = false → l.eval (fun _ => 0) = 0
  | .zero, l, h, _ => by cases h; rfl
  | .succ _, _, _, hz => by simp [Level.isNeverZero] at hz
  | .max a b, l, h, hz => by
    simp only [TrLevel, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨a', ha, b', hb, rfl⟩ := h
    simp only [Level.isNeverZero, Bool.or_eq_false_iff] at hz
    simp [eval_zero_of_not ha hz.1, eval_zero_of_not hb hz.2]
  | .imax a b, l, h, hz => by
    simp only [TrLevel, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨a', ha, b', hb, rfl⟩ := h
    simp only [Level.isNeverZero] at hz
    simp [eval_zero_of_not hb hz]
  | .param _, l, h, _ => by
    simp only [TrLevel, Option.map_eq_some_iff] at h
    obtain ⟨p, -, rfl⟩ := h
    rfl
  | .mvar _, _, h, _ => by cases h

end OracleSound

open OracleSound in
/-- `Level.isNeverZero` is complete for translated levels: a level is never zero exactly when its
translation is non-zero under every assignment of the universe parameters (a level that is not
syntactically never zero is zero when every parameter is). Reference: none (`Level.isNeverZero`,
Lean's kernel; `Metalean.Level.eval`, `ML Level/Quot/Basic.lean:48`). -/
theorem TrLevel.isNeverZero_iff {lps : List Name} {u : Level} {l : Metalean.Level lps.length}
    (h : TrLevel lps u = some l) : u.isNeverZero = true ↔ ∀ ν, l.eval ν ≠ 0 := by
  refine ⟨eval_ne_zero h, fun hne => ?_⟩
  cases hz : u.isNeverZero
  · exact absurd (eval_zero_of_not h hz) (hne _)
  · rfl

end EraseProof
