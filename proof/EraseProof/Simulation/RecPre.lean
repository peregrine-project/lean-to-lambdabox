import EraseProof.Simulation.Ind
import EraseProof.Simulation.RecEval
import EraseProof.Relation.FixSubst
import EraseProof.Oracle.Whnf

/-!
# The `deltaRec` case of the simulation

A definition by structural recursion that the configuration erases through its compiled
pre-definition `pre` evaluates, applied to `lamArity pre` arguments, by `SrcEval.deltaRec`: the
arguments evaluate to `vs`, and `pre` at the constant's levels applied to `vs` evaluates to the
value. The spine's erasure is `□` (then the value is erasable), or the erasure of the constant (its
λ□ constant, whose declaration is the fixpoint `F` of `ErasesDecl`, or `F` itself by
`Erases.constFix`) applied to erasures of the arguments. λ□ unfolds `F` at the first argument
(`eval_fix`, recursive-argument index 0), which substitutes `F` for the fix variable of the body.
The body erases `pre` at the constant's levels with the recursive calls erased to the fix variable,
so the substituted body erases `pre` with the recursive calls erased to `F` (`Erases.fixSubst`;
the calls are all at the constant's levels, `ConstAt`), and the β-steps that follow are those of
the source. Reference: the `eval_fix` case of `erases_correct` (`MR E/ErasureCorrectness.v:579`);
DV-7.
-/

open Lean Erasure
open Metalean (Defeq EnvWF TypeEq WHRed)

namespace EraseProof

namespace SimRecPre

variable {ζ : Metalean.Sigs}

/-! ## Translations to a constant node -/

/-- `e` is no Metalean constant node. -/
def NotConst {ℓ n : Nat} (e : Metalean.Expr ζ ℓ n) : Prop :=
  ∀ (kind : Metalean.ConstKind) (nl : Nat) (η : Metalean.Head ζ (.const kind nl))
    (ls : Fin nl → Metalean.Level ℓ), e ≠ .const η ls

/-- A λ is no constant node. -/
theorem notConst_lam {ℓ n : Nat} (A : Metalean.Expr ζ ℓ n) (b : Metalean.Expr ζ ℓ (n + 1)) :
    NotConst (.lam A b) := fun _ _ _ _ h => by cases h

/-- λs over a body that is no constant node are no constant node. -/
theorem notConst_ctxLam {ℓ : Nat} : ∀ {a b : Nat} (Θ : Metalean.Ctx ζ ℓ a b)
    (body : Metalean.Expr ζ ℓ b), NotConst body → NotConst (Θ.lam body)
  | _, _, .nil, _, h => h
  | _, _, .snoc Θ A, body, _ => notConst_ctxLam Θ (.lam A body) (notConst_lam A body)

/-- At least one λ is no constant node. -/
theorem notConst_ctxLam_pos {ℓ : Nat} : ∀ {a b : Nat} (Θ : Metalean.Ctx ζ ℓ a b)
    (body : Metalean.Expr ζ ℓ b), a < b → NotConst (Θ.lam body)
  | _, _, .nil, _, h => absurd h (Nat.lt_irrefl _)
  | _, _, .snoc Θ A, body, _ => notConst_ctxLam Θ (.lam A body) (notConst_lam A body)

/-- Weakening keeps a term that is no constant node so. -/
theorem notConst_wk {ℓ n : Nat} {e : Metalean.Expr ζ ℓ n} (h : NotConst e) : NotConst e.wk := by
  intro kind nl η ls he
  cases e <;> simp [Metalean.Expr.wk, Metalean.Expr.wkFrom, Metalean.Expr.rename] at he
  exact h _ _ _ _ rfl

/-- Weakening a closed term keeps it no constant node. -/
theorem notConst_wkClosed {ℓ : Nat} {e : Metalean.Expr ζ ℓ 0} (h : NotConst e) :
    ∀ {n : Nat}, NotConst (e.wkClosed (n := n))
  | 0 => h
  | n + 1 => notConst_wk (notConst_wkClosed h (n := n))

/-- An application spine of a head that is no constant node is no constant node. -/
theorem notConst_appList {ℓ n : Nat} : ∀ {X : Metalean.Expr ζ ℓ n}
    (rest : List (Metalean.Expr ζ ℓ n)), NotConst X → NotConst (X.appList rest)
  | _, [], h => h
  | _, _ :: rest, _ => by
    rw [Metalean.Expr.appList_cons]
    exact notConst_appList rest fun _ _ _ _ h => by cases h

variable {E : Metalean.Env ζ} {B : Binds ζ} {lps : List Name}

/-- The η-term of a quotient constant (`quotTerm`, `ML Frontend/Translate.lean:197`) is a λ. -/
theorem quotTerm_notConst {ℓ : Nat} {η : Metalean.Head ζ .quot}
    {eqHead : Metalean.Head ζ (.inductive Metalean.Eq.sig)} {kind : Metalean.Export.QuotKind}
    {ls : List (Metalean.Level ℓ)} {t₀ : Metalean.Expr ζ ℓ 0}
    (h : Metalean.Frontend.quotTerm η eqHead kind ls = .ok t₀) : NotConst t₀ := by
  match kind, ls, h with
  | .type, [_], h => cases h; exact notConst_ctxLam_pos _ _ (by omega)
  | .ctor, [_], h => cases h; exact notConst_ctxLam_pos _ _ (by omega)
  | .lift, [_, _], h => cases h; exact notConst_ctxLam_pos _ _ (by omega)
  | .ind, [_], h => cases h; exact notConst_ctxLam_pos _ _ (by omega)

/-- A saturating binding applied to no argument translates to no constant node: an inductive,
constructor or recursor node, or the η-term of one (`indTerm`, `ctorTerm`, `recrTerm`,
`quotTerm`, `ML Frontend/Translate.lean:103-197`), a λ-telescope over such a node. -/
theorem SatTr.nil_notConst {n : Nat} {b : MBinding ζ} {us : List Level}
    {t : Metalean.Expr ζ lps.length n} (h : SatTr E lps b us [] t) : NotConst t := by
  generalize hargs : ([] : List (Metalean.Expr ζ lps.length n)) = args at h
  cases h with
  | indSat ps is rest => exact notConst_appList rest fun _ _ _ _ h => by cases h
  | indEta =>
    rw [← hargs]
    exact notConst_wkClosed (notConst_ctxLam _ _ fun _ _ _ _ h => by cases h)
  | ctorSat ps fs rest => exact notConst_appList rest fun _ _ _ _ h => by cases h
  | ctorEta _ hlt hc =>
    subst hargs
    obtain ⟨Θ, body, rfl⟩ := OracleWhnf.ctorTerm_shape hc
    exact notConst_wkClosed (notConst_ctxLam_pos Θ body (by simpa using hlt))
  | recrSat mo A rest => exact notConst_appList rest fun _ _ _ _ h => by cases h
  | recrEta mo _ _ _ _ hr =>
    subst hargs
    unfold Metalean.Frontend.recrTerm at hr
    obtain ⟨cs, -, hr⟩ := OracleWhnf.ok_of_bind hr
    dsimp only at hr
    split at hr
    · cases hr
      exact notConst_wkClosed (notConst_ctxLam _ _ (notConst_lam _ _))
    · cases hr
  | quotType | quotMk | quotLift | quotInd => cases hargs
  | quotEta _ _ hq => subst hargs; exact notConst_wkClosed (quotTerm_notConst hq)

/-- Only the constant bound to a Metalean constant translates to it: a constant node is the
translation of a constant only through the constant's own binding (`TrM.const`), since the
η-terms of saturating bindings are no constant nodes, and bindings to constants are injective
(`ProgEnv.const_inj`). -/
theorem TrM.const_head {P : List ConstantInfo} (henv : ProgEnv P ζ E B) {n : Nat}
    {Γ : Metalean.Ctx ζ lps.length 0 n} {Δ : MLCtx ζ lps.length n} {c₀ c : Name}
    {us : List Level} {kind : Metalean.ConstKind} {nl : Nat} {η : Metalean.Head ζ (.const kind nl)}
    {ls : Fin nl → Metalean.Level lps.length} (hB : B c₀ = some (.const η))
    (h : TrM E B lps Γ Δ (.const c us) (.const η ls)) : c = c₀ := by
  generalize hx : Expr.const c us = e at h
  generalize ht : Metalean.Expr.const η ls = t at h
  cases h with
  | const hB' _ =>
    cases hx
    cases ht
    exact henv.const_inj hB' hB
  | special _ _ hlen _ hsat =>
    obtain ⟨rfl, -, -⟩ := SrcDefeq.spine_const hx.symm
    obtain rfl := List.eq_nil_of_length_eq_zero hlen.symm
    exact (SatTr.nil_notConst hsat _ _ _ _ ht.symm).elim
  | _ => cases hx

/-! ## Levels -/

/-- The instances of distinct level parameters at as many levels are the levels. -/
theorem map_param_instLevel {ps : List Name} {us : List Level} (hnd : ps.Nodup)
    (hl : us.length = ps.length) : (ps.map Level.param).map (Pure.instLevel ps us) = us := by
  refine List.ext_getElem (by simp [hl]) fun i h1 h2 => ?_
  have hi : i < ps.length := by simpa using h1
  have hidx : ps.finIdxOf? ps[i] = some ⟨i, hi⟩ := by
    rw [List.finIdxOf?_eq_some_iff]
    refine ⟨rfl, fun j hj h => ?_⟩
    have := (List.Nodup.getElem_inj_iff hnd).1 h
    simp [Fin.lt_def] at hj
    omega
  simp only [List.getElem_map, Pure.instLevel, find_zip_of_finIdxOf hl hidx]

/-- A term whose occurrences of `c₀` are at distinct level parameters `ps`, instantiated at as many
levels `us`, has its occurrences of `c₀` at `us`. -/
theorem ConstAt_instLevels {c₀ : Name} {ps : List Name} {us : List Level} (hnd : ps.Nodup)
    (hl : us.length = ps.length) :
    ∀ {e : Expr}, ConstAt c₀ (ps.map .param) e → ConstAt c₀ us (Pure.instLevels ps us e)
  | .const _ _, h => fun hc => by rw [h hc]; exact map_param_instLevel hnd hl
  | .app f a, h => ⟨ConstAt_instLevels hnd hl (e := f) h.1, ConstAt_instLevels hnd hl (e := a) h.2⟩
  | .lam _ t b _, h | .forallE _ t b _, h =>
    ⟨ConstAt_instLevels hnd hl (e := t) h.1, ConstAt_instLevels hnd hl (e := b) h.2⟩
  | .letE _ t v b _, h => ⟨ConstAt_instLevels hnd hl (e := t) h.1,
    ConstAt_instLevels hnd hl (e := v) h.2.1, ConstAt_instLevels hnd hl (e := b) h.2.2⟩
  | .mdata _ e, h | .proj _ _ e, h => ConstAt_instLevels hnd hl (e := e) h
  | .bvar _, _ | .fvar _, _ | .mvar _, _ | .sort _, _ | .lit _, _ => trivial

/-! ## Spines of a definition -/

/-- A spine with one more argument. -/
theorem mkAppN_snoc' (f : Expr) (as : List Expr) (a : Expr) :
    mkAppN f (as ++ [a]).toArray = .app (mkAppN f as.toArray) a := by
  rw [mkAppN_eq_foldl, mkAppN_eq_foldl, List.foldl_append]; rfl

/-- A spine of a spine. -/
theorem mkAppN_mkAppN (f : Expr) (l₁ l₂ : List Expr) :
    mkAppN (mkAppN f l₁.toArray) l₂.toArray = mkAppN f (l₁ ++ l₂).toArray := by
  rw [mkAppN_eq_foldl, mkAppN_eq_foldl, mkAppN_eq_foldl, List.foldl_append]

/-- The first argument of a spine. -/
theorem mkAppN_cons' (f a : Expr) (as : List Expr) :
    mkAppN f (a :: as).toArray = mkAppN (.app f a) as.toArray := by
  rw [mkAppN_eq_foldl, mkAppN_eq_foldl]; rfl

/-- A spine of a definition has no saturating head. -/
theorem spine_not_special {c : Name} {us : List Level} (hns : ¬ SpecialHead B (.const c us))
    (l : List Expr) : ¬ SpecialHead B (mkAppN (.const c us) l.toArray) :=
  fun ⟨c', us', b, hfn, hb, hs⟩ => hns ⟨c', us', b, by
    rw [SrcDefeq.getAppFn_mkAppN_const] at hfn; simpa [Expr.getAppFn] using hfn, hb, hs⟩

/-- A typed translation of a spine of a constant without saturating binding translates the
constant and, typed, every argument. -/
theorem spine_tr (hE : EnvWF E) {c : Name} {us : List Level} (hns : ¬ SpecialHead B (.const c us)) :
    ∀ (as : List Expr) {t T : Metalean.Expr ζ lps.length 0},
      TrM E B lps .nil [] (mkAppN (.const c us) as.toArray) t → E[.nil] ⊢ t : T →
      (∃ t₀, TrM E B lps .nil [] (.const c us) t₀) ∧
        ∀ (i : Nat) a, as[i]? = some a → ∃ a₀ A, TrM E B lps .nil [] a a₀ ∧ E[.nil] ⊢ a₀ : A := by
  intro as
  induction as using List.reverseRecOn with
  | nil => intro t T he _; exact ⟨⟨t, he⟩, fun i a h => by simp at h⟩
  | append_singleton as a ih =>
    intro t T he ht
    rw [mkAppN_snoc'] at he
    obtain ⟨f', a', hf', ha', rfl, ⟨F, hF⟩, ⟨A, hA⟩⟩ :=
      TrM.wf_app hE SrcDefeq.nil_ok (spine_not_special hns as) he ht
    obtain ⟨hh, hargs⟩ := ih hf' hF
    refine ⟨hh, fun i x hx => ?_⟩
    rcases Nat.lt_or_ge i as.length with hi | hi
    · rw [List.getElem?_append_left hi] at hx
      exact hargs i x hx
    · rw [List.getElem?_append_right hi] at hx
      obtain ⟨h0, rfl⟩ : i - as.length = 0 ∧ a = x := by
        rcases h : i - as.length with _ | k
        · rw [h] at hx; simpa using hx
        · rw [h] at hx; simp at hx
      exact ⟨a', A, ha', hA⟩

/-- An erasure of a definition that is not a recognized `casesOn`, at the closed level: `□`, the λ□
constant, or its fixpoint (`Erases.constFix`) with the fixpoint's data. -/
theorem head_inv {σ : EvalEnv} {c : Name} {us : List Level} {d : DefinitionVal} {pre : Expr}
    (hc : findDecl σ.decls c = some (.defnInfo d)) (hco : σ.casesOn? c = none)
    (hrp : σ.recPre? (.defnInfo d) = some pre) {hd : LBTerm}
    (h : Erases E B lps σ .nil [] (.const c us) hd) :
    (hd = .box ∧ ErasableS E B lps .nil [] (.const c us)) ∨ hd = .const (toKername c) ∨
    ∃ (x : FVarId) (b : LBTerm) (t : Metalean.Expr ζ lps.length 0),
      hd = .fix [⟨fixDefName c, toBvar x 0 b, 0⟩] 0 ∧
      ConstAt c (d.levelParams.map .param) pre ∧
      (∃ p : Metalean.Expr ζ d.levelParams.length 0, TrM E B d.levelParams .nil [] pre p) ∧
      TrM E B lps .nil [] (.const c us) t ∧
      Erases E B lps σ .nil [(some x, .vfix t)] (Pure.instLevels d.levelParams us pre) b ∧
      closedn 1 (toBvar x 0 b) = true ∧ ∀ y, hasFVar y (toBvar x 0 b) = false := by
  generalize hx : Expr.const c us = e at h
  cases h with
  | const => cases hx; exact .inr (.inl rfl)
  | box hb => subst hx; exact .inl ⟨rfl, hb⟩
  | fixVar _ _ hF => simp [MLCtx.findFix] at hF
  | constFix hci _ _ _ _ hrp' hca hp ht hb hcl hfv =>
    cases hx
    rw [hc] at hci; cases hci
    rw [hrp] at hrp'; cases hrp'
    exact .inr (.inr ⟨_, _, _, rfl, hca, hp, ht, hb, hcl, hfv⟩)
  | ctor hc' | quotMk hc' | quotLift hc' | recLet hc' | recFix hc' =>
    obtain ⟨-, rfl, -⟩ := SrcDefeq.spine_const hx.symm
    rw [hc] at hc'; cases hc'
  | cases hc' | casesReduced hc' =>
    obtain ⟨-, rfl, -⟩ := SrcDefeq.spine_const hx.symm
    rw [hco] at hc'; cases hc'
  | eta heta =>
    obtain ⟨-, rfl, -⟩ := SrcDefeq.spine_const hx.symm
    obtain ⟨ar, har, -⟩ := SimCases.etaSpine?_lt heta
    rw [SimCases.specialArity_defn hc rfl hco] at har; cases har
  | bvar | fvar | lam | letE | app | proj | litZero | litSucc | mdata => cases hx

/-- An erasure of a spine of a definition that is not a recognized `casesOn`, at the closed level:
an erasure of the constant, other than `□`, applied to erasures of the arguments, or `□` applied
to erasures of the arguments after an erasable prefix. Reference: `erases_mkApps_inv`
(`MR E/ErasureProperties.v:105`). -/
theorem spine_inv {σ : EvalEnv} {c : Name} {us : List Level} {d : DefinitionVal} {pre : Expr}
    (hc : findDecl σ.decls c = some (.defnInfo d)) (hco : σ.casesOn? c = none)
    (hrp : σ.recPre? (.defnInfo d) = some pre) :
    ∀ (as : List Expr) {tb : LBTerm}, Erases E B lps σ .nil [] (mkAppN (.const c us) as.toArray) tb →
      (∃ hd as'', tb = mkApps hd as'' ∧ hd ≠ .box ∧ Erases E B lps σ .nil [] (.const c us) hd ∧
        List.Forall₂ (Erases E B lps σ .nil []) as as'') ∨
      (∃ k as'', k ≤ as.length ∧ tb = mkApps .box as'' ∧
        ErasableS E B lps .nil [] (mkAppN (.const c us) (as.take k).toArray) ∧
        List.Forall₂ (Erases E B lps σ .nil []) (as.drop k) as'') := by
  have hsa := SimCases.specialArity_defn hc rfl hco
  intro as
  induction as using List.reverseRecOn with
  | nil =>
    intro tb h
    rcases head_inv hc hco hrp h with ⟨rfl, hb⟩ | rfl | ⟨x, b, t, rfl, -⟩
    · exact .inr ⟨0, [], Nat.le_refl _, rfl, hb, .nil⟩
    · exact .inl ⟨_, [], rfl, (fun h => by cases h), h, .nil⟩
    · exact .inl ⟨_, [], rfl, (fun h => by cases h), h, .nil⟩
  | append_singleton as a ih =>
    intro tb h
    rw [mkAppN_snoc'] at h
    have hns : ¬ ShortSpine σ (.app (mkAppN (.const c us) as.toArray) a) := by
      rintro ⟨c', us', ar, hfn, har, -⟩
      rw [show (Expr.app (mkAppN (.const c us) as.toArray) a).getAppFn = .const c us from
        SrcDefeq.getAppFn_mkAppN_const c us as] at hfn
      cases hfn
      rw [hsa] at har; cases har
    have hnc : ∀ c' us' cv, (mkAppN (.const c us) as.toArray).getAppFn = .const c' us' →
        findDecl σ.decls c' ≠ some (.ctorInfo cv) := by
      intro c' us' cv hfn hcv
      rw [SrcDefeq.getAppFn_mkAppN_const] at hfn
      cases hfn
      rw [hc] at hcv; cases hcv
    rcases SimCases.app_inv hns hnc h with ⟨rfl, hb⟩ | ⟨tf, ta, rfl, hf, ha⟩
    · refine .inr ⟨as.length + 1, [], by simp, rfl, ?_, by simp⟩
      rw [List.take_of_length_le (by simp), mkAppN_snoc']
      exact hb
    rcases ih hf with ⟨hd, as'', rfl, hnb, hhd, hall⟩ | ⟨k, as'', hk, rfl, hpe, hall⟩
    · exact .inl ⟨hd, as'' ++ [ta], (SimCases.mkApps_snoc _ _ _).symm, hnb, hhd,
        List.rel_append hall (.cons ha .nil)⟩
    · refine .inr ⟨k, as'' ++ [ta], by simp; omega, (SimCases.mkApps_snoc _ _ _).symm, ?_, ?_⟩
      · rwa [List.take_append_of_le_length hk]
      · rw [List.drop_append_of_le_length hk]
        exact List.rel_append hall (.cons ha .nil)

/-- A typed spine of an erasable term, with no saturating head, is erasable. -/
theorem erasable_spine (hE : EnvWF E) {f : Expr}
    (hns : ∀ l : List Expr, ¬ SpecialHead B (mkAppN f l.toArray))
    (hf : ErasableS E B lps .nil [] f) :
    ∀ (l : List Expr) {t T : Metalean.Expr ζ lps.length 0},
      TrM E B lps .nil [] (mkAppN f l.toArray) t → E[.nil] ⊢ t : T →
      ErasableS E B lps .nil [] (mkAppN f l.toArray) := by
  intro l
  induction l using List.reverseRecOn with
  | nil => intro _ _ _ _; exact hf
  | append_singleton l a ih =>
    intro t T he ht
    rw [mkAppN_snoc'] at he ⊢
    obtain ⟨f', a', hf', ha', rfl, ⟨F, hF⟩, -⟩ :=
      TrM.wf_app hE SrcDefeq.nil_ok (hns l) he ht
    obtain ⟨w, hw, W, hwW, hWA⟩ := ih hf' hF
    have hEf : IsErasable E .nil f' :=
      RelInst.IsErasable.of_defeq (SimCases.trM_defeq hE hw hf' hwW hF) hWA
    exact ⟨_, he, IsErasable.app hE SrcDefeq.nil_ok hEf ht⟩

/-! ## λ□ -/

/-- `□` applied to evaluating arguments evaluates to `□`. -/
theorem eval_box_spine {lenv : GlobalDeclarations} :
    ∀ (l : List LBTerm), (∀ a ∈ l, ∃ r, LBEval defaultFlags lenv a r) →
      LBEval defaultFlags lenv (mkApps .box l) .box := by
  intro l
  induction l using List.reverseRecOn with
  | nil => intro _; exact .atom rfl
  | append_singleton l x ih =>
    intro h
    rw [SimCases.mkApps_snoc]
    obtain ⟨r, hr⟩ := h x (by simp)
    exact .box (ih fun a ha => h a (by simp [ha])) hr

/-- An erasure of a term headed by no constant, applied to erasures of arguments, erases the
application. -/
theorem erases_apps {σ : EvalEnv} {ws : List Expr} {avs : List LBTerm}
    (hall : List.Forall₂ (Erases E B lps σ .nil []) ws avs) :
    ∀ {f : Expr} {f' : LBTerm}, (∀ c us, f.getAppFn ≠ .const c us) →
      Erases E B lps σ .nil [] f f' →
      Erases E B lps σ .nil [] (mkAppN f ws.toArray) (mkApps f' avs) := by
  induction hall with
  | nil => intro _ _ _ h; exact h
  | @cons w a ws avs hw _ ih =>
    intro f f' hfn h
    rw [mkAppN_cons']
    exact ih (f := .app f w) (fun c us h' => hfn c us (by simpa [Expr.getAppFn] using h'))
      (.app (by rintro ⟨c, us, h', -⟩; exact hfn c us h') h hw)

/-- A term with leading λs is a λ. -/
theorem lam_of_lamArity {e : Expr} (h : 0 < lamArity e) : ∃ n A b bi, e = .lam n A b bi := by
  cases e with
  | lam n A b bi => exact ⟨n, A, b, bi, rfl⟩
  | _ => simp [lamArity] at h

/-- The locals with one fix-variable local `x` are the empty locals with `x` added. -/
theorem drop_single {ℓ n : Nat} (x : FVarId) (d : MLDecl ζ ℓ n) :
    MLCtx.Drop x [(some x, d)] [] := by
  refine ⟨fun i t h => by simp [MLCtx.findB] at h, fun y t hy h => ?_, fun y t hy h => ?_⟩
  · have hb : (x == y) = false := by
      cases h' : x == y
      · rfl
      · exact absurd ((fvarId_beq_iff x y).mp h').symm hy
    simp [MLCtx.findF, hb] at h
  · have hb : (x == y) = false := by
      cases h' : x == y
      · rfl
      · exact absurd ((fvarId_beq_iff x y).mp h').symm hy
    simp [MLCtx.findFix, hb] at h

/-- The empty locals with the local `x` added. -/
theorem drop_nil {ℓ n : Nat} (x : FVarId) (d : MLDecl ζ ℓ n) :
    MLCtx.Drop x ([] : MLCtx ζ ℓ n) [(some x, d)] :=
  ⟨fun i t h => by simp [MLCtx.findB] at h, fun y t _ h => by simp [MLCtx.findF] at h,
    fun y t _ h => by simp [MLCtx.findFix] at h⟩

/-! ## The unfolding -/

/-- The unfolding of the fixpoint `F` of a definition with a compiled pre-definition: given the
body's erasure at the constant's levels `us`, with the fix variable `x` standing for the
constant's translation, and a λ□ head that evaluates to `F`, the head applied to erasures of the
arguments evaluates to an erasure of the value of the pre-definition applied to the arguments'
values. `eval_fix` at the first argument substitutes `F` for the fix variable (`Erases.fixSubst`,
`Erases.constFix` at `us` for the recursive calls), and the induction hypothesis of the
pre-definition's evaluation concludes. Reference: the `eval_fix` case of `erases_correct`
(`MR E/ErasureCorrectness.v:579`); DV-7. -/
theorem unfold_sim {P : List ConstantInfo} {σ : EvalEnv} {lenv : GlobalDeclarations}
    (henv : ProgEnv P ζ E B) (hE : EnvWF E) (hsub : SubEnv σ.decls P)
    {c : Name} {d : DefinitionVal} {us : List Level} {pre v : Expr} {as vs : List Expr}
    {as'' : List LBTerm} {x : FVarId} {b : LBTerm} {t₁ : Metalean.Expr ζ lps.length 0}
    {hd : LBTerm}
    (hc : findDecl σ.decls c = some (.defnInfo d)) (hco : σ.casesOn? c = none)
    (hat : σ.isAtom c = false) (hax : σ.axiomatized (.defnInfo d) = false)
    (hrp : σ.recPre? (.defnInfo d) = some pre) (hpos : 0 < lamArity pre)
    (hca : ConstAt c (d.levelParams.map .param) pre)
    (hp : ∃ p : Metalean.Expr ζ d.levelParams.length 0, TrM E B d.levelParams .nil [] pre p)
    (ht₁ : TrM E B lps .nil [] (.const c us) t₁)
    (hbody : Erases E B lps σ .nil [(some x, .vfix t₁)] (Pure.instLevels d.levelParams us pre) b)
    (hcl : closedn 1 (toBvar x 0 b) = true) (hfv : ∀ y, hasFVar y (toBvar x 0 b) = false)
    (hhd : LBEval defaultFlags lenv hd (.fix [⟨fixDefName c, toBvar x 0 b, 0⟩] 0))
    (hdF : ErasesDeps E B σ lenv (.fix [⟨fixDefName c, toBvar x 0 b, 0⟩] 0))
    (hne : as ≠ []) (hlen' : as.length = vs.length) (hlen'' : as.length = as''.length)
    (harg : ∀ (i : Nat) a w a', as[i]? = some a → vs[i]? = some w → as''[i]? = some a' →
      ∃ z, Erases E B lps σ .nil [] w z ∧ LBEval defaultFlags lenv a' z)
    (hdas : ∀ a' ∈ as'', ErasesDeps E B σ lenv a')
    {t₃ T₃ : Metalean.Expr ζ lps.length 0}
    (ht₃ : TrM E B lps .nil [] (mkAppN (Pure.instLevels d.levelParams us pre) vs.toArray) t₃)
    (hT₃ : E[.nil] ⊢ t₃ : T₃)
    (ihb : ErasesSim E B lps σ lenv (mkAppN (Pure.instLevels d.levelParams us pre) vs.toArray) v) :
    ∃ vb, Erases E B lps σ .nil [] v vb ∧ LBEval defaultFlags lenv (mkApps hd as'') vb := by
  obtain ⟨η, hB, -⟩ := henv.lookup_def (SrcDefeq.findDecl_sub hsub hc)
  obtain ⟨ls₁, rfl, hls⟩ := SrcDefeq.trM_const_inv' hB ht₁
  obtain ⟨p, hpT⟩ := hp
  have hmem := (findDecl_eq_some (SrcDefeq.findDecl_sub hsub hc)).1
  have hnd : d.levelParams.Nodup := henv.levelParams_nodup hmem
  have hlu : us.length = d.levelParams.length :=
    RelLevels.TrM.lvlOK henv hE hsub ht₁ _ hc (.inr (.inl ⟨_, rfl⟩))
  -- the body with the fixpoint substituted for the fix variable
  set F : LBTerm := .fix [⟨fixDefName c, toBvar x 0 b, 0⟩] 0 with hFdef
  have hcF : ∀ {n : Nat} (Γ : Metalean.Ctx ζ lps.length 0 n) (Δ : MLCtx ζ lps.length n),
      Erases E B lps σ Γ Δ (.const c us) F := fun _ _ =>
    .constFix hc rfl hco hat hax hrp hca ⟨p, hpT⟩ (.const hB hls) hbody hcl hfv
  have hfvpre : FVarsIn (fun _ => False) pre :=
    AbsFV.FVarsIn.mono (fun _ h => by simp [MLCtx.findF] at h) hpT.fvarsIn
  have he' : FVarsIn (· ≠ x) (Pure.instLevels d.levelParams us pre) :=
    AbsFV.FVarsIn_instLevels _ _ (AbsFV.FVarsIn.mono (fun _ h => h.elim) hfvpre)
  have htp : TrM E B lps .nil [(some x, .vfix (.const η ls₁))]
      (Pure.instLevels d.levelParams us pre) (p{ls₁}) := by
    have := TrM.instL hls hpT
    exact TrM.dropF (by simpa [MLCtx.instL] using this) (drop_nil x _) he'
  have hcl0 : closedn 0 b = true := by simpa using Erases.closed htp hbody
  have hFcl : closedn 0 F = true := by simp [hFdef, closedn, closednD, hcl]
  have hx : MLCtx.findFix ([(some x, .vfix (.const η ls₁))] : MLCtx ζ lps.length 0) x =
      some (.const η ls₁) := by
    simp [MLCtx.findFix, MLDecl.fixVal?, (fvarId_beq_iff x x).mpr rfl]
  have hsubst := Erases.fixSubst hFcl (fun c ci h => (AbsFV.closed_types henv hsub c ci h).2)
    (fun Γ Δ c' us' h => TrM.const_head henv hB h) hcF hbody hx (drop_single x _)
    he' (ConstAt_instLevels hnd hlu hca) hcl0
  -- the arguments' values
  have hstep : ∀ i, i < as.length → ∃ z, ∀ a w a', as[i]? = some a → vs[i]? = some w →
      as''[i]? = some a' → Erases E B lps σ .nil [] w z ∧ LBEval defaultFlags lenv a' z := by
    intro i hi
    have ha : as[i]? = some as[i] := List.getElem?_eq_getElem hi
    have hw : vs[i]? = some vs[i] := List.getElem?_eq_getElem (by omega)
    have ha' : as''[i]? = some as''[i] := List.getElem?_eq_getElem (by omega)
    obtain ⟨z, hz⟩ := harg i _ _ _ ha hw ha'
    refine ⟨z, fun a w a' h1 h2 h3 => ?_⟩
    rw [ha] at h1; rw [hw] at h2; rw [ha'] at h3
    cases h1; cases h2; cases h3
    exact hz
  obtain ⟨avs, havs, havsR⟩ := SimInd.choose_list hstep
  have hget : ∀ (i : Nat) z, avs[i]? = some z → ∃ w a', vs[i]? = some w ∧ as''[i]? = some a' ∧
      Erases E B lps σ .nil [] w z ∧ LBEval defaultFlags lenv a' z := by
    intro i z hz
    have hi : i < as.length := by rw [← havs]; exact (List.getElem?_eq_some_iff.mp hz).1
    exact ⟨vs[i], as''[i], List.getElem?_eq_getElem (by omega),
      List.getElem?_eq_getElem (by omega),
      havsR i z hz _ _ _ (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem (by omega))
        (List.getElem?_eq_getElem (by omega))⟩
  have hvs : List.Forall₂ (Erases E B lps σ .nil []) vs avs :=
    CasesWhred.forall₂_of_getElem? (by omega) fun i w z hw hz => by
      obtain ⟨w', a', hw', -, he, -⟩ := hget i z hz
      rw [hw] at hw'; cases hw'; exact he
  have hev : List.Forall₂ (fun a' z => LBEval defaultFlags lenv a' z ∧ LBFixed z) as'' avs :=
    CasesWhred.forall₂_of_getElem? (by omega) fun i a' z ha' hz => by
      obtain ⟨-, a'', -, ha'', -, hev⟩ := hget i z hz
      rw [ha'] at ha''; cases ha''; exact ⟨hev, RecEval.LBEval.fixed hev⟩
  -- the erasure of the unfolded spine and its dependencies
  obtain ⟨nm, A, bd, bi, hlam⟩ := lam_of_lamArity hpos
  have hfn : ∀ c' us', (Pure.instLevels d.levelParams us pre).getAppFn ≠ .const c' us' := by
    intro c' us' h
    rw [hlam] at h
    cases h
  have herb := erases_apps hvs hfn hsubst
  have hdbody : ErasesDeps E B σ lenv (toBvar x 0 b) := by
    have hdF' : ErasesDeps E B σ lenv (.fix [⟨fixDefName c, toBvar x 0 b, 0⟩] 0) := hdF
    cases hdF' with
    | fix h => exact h _ (List.mem_singleton_self _)
  have hdeps : ErasesDeps E B σ lenv (mkApps (csubst F 0 (toBvar x 0 b)) avs) := by
    refine ErasesDeps.mkApps_iff.2 ⟨ErasesDeps.csubst hdF hdbody, fun z hz => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hz
    obtain ⟨-, a', -, ha', -, hev⟩ := hget i _ (List.getElem?_eq_getElem hi)
    exact ErasesDeps.eval (hdas a' (List.mem_of_getElem? ha')) hev
  obtain ⟨vb, hvb, hevb⟩ := ihb ht₃ ⟨T₃, hT₃⟩ herb hdeps
  refine ⟨vb, hvb, ?_⟩
  -- λ□: `eval_fix` at the first argument, then the arguments replaced by their values
  obtain ⟨av₁, rest, rfl⟩ : ∃ av₁ rest, avs = av₁ :: rest := by
    cases avs with
    | nil => cases as with
      | nil => exact absurd rfl hne
      | cons => simp at havs
    | cons av₁ rest => exact ⟨av₁, rest, rfl⟩
  obtain ⟨a₁, rest'', rfl, -⟩ : ∃ a₁ rest'', as'' = a₁ :: rest'' ∧ True := by
    cases as'' with
    | nil => cases hev
    | cons a₁ rest'' => exact ⟨a₁, rest'', rfl, trivial⟩
  obtain ⟨⟨hev₁, -⟩, -⟩ := List.forall₂_cons.1 hev
  have hfix : ∀ f', LBEval defaultFlags lenv (.app (csubst F 0 (toBvar x 0 b)) av₁) f' →
      LBEval defaultFlags lenv (.app hd av₁) f' := fun f' h =>
    LBEval.fix (argsv := []) rfl hhd (RecEval.LBEval.self hev₁) rfl h
  have h1 := RecEval.eval_mkApps_head hfix rest vb hevb
  exact RecEval.eval_args_replace hev [] vb h1

end SimRecPre

open SimRecPre

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {P : List ConstantInfo}
  {σ : EvalEnv} {lps : List Name} {lenv : GlobalDeclarations}

/-- The `deltaRec` case of `erases_correct`: a definition erased through its compiled
pre-definition, applied to as many arguments as the pre-definition has leading λs. The spine
erases to `□` after an erasable prefix (then the spine and its value are erasable), or to the
erasure of the constant applied to erasures of the arguments: the λ□ constant, whose declaration
is the fixpoint of `ErasesDecl`, instantiated at the constant's levels (`Erases.instL_gen`), or
the fixpoint itself (`Erases.constFix`); `SimRecPre.unfold_sim` unfolds it. The pre-definition's
application has a typed translation by the conversion premise. Reference: the `eval_fix` case of
`erases_correct` (`MR E/ErasureCorrectness.v:579`); DV-7. -/
theorem erases_correct_deltaRec (henv : ProgEnv P ζ E B) (hE : EnvWF E)
    (hsub : SubEnv σ.decls P) (hinj : KernameInj σ.decls) {c : Name} {ci : ConstantInfo}
    {us : List Level} {pre v : Expr} {as vs : List Expr}
    (hc : findDecl σ.decls c = some ci) (hdef : ci.isDefinition = true)
    (hco : σ.casesOn? c = none) (hat : σ.isAtom c = false) (hax : σ.axiomatized ci = false)
    (hrp : σ.recPre? ci = some pre) (hpos : 0 < lamArity pre) (hlen : as.length = lamArity pre)
    (hlen' : as.length = vs.length)
    (hev : ∀ (i : Nat) a w, as[i]? = some a → vs[i]? = some w → SrcEval σ (SrcConv E B lps) a w)
    (hconv : SrcConv E B lps (mkAppN (.const c us) vs.toArray)
      (mkAppN (Pure.instLevels ci.levelParams us pre) vs.toArray))
    (hb : SrcEval σ (SrcConv E B lps)
      (mkAppN (Pure.instLevels ci.levelParams us pre) vs.toArray) v)
    (ih : ∀ (i : Nat) a w, as[i]? = some a → vs[i]? = some w → ErasesSim E B lps σ lenv a w)
    (ihb : ErasesSim E B lps σ lenv (mkAppN (Pure.instLevels ci.levelParams us pre) vs.toArray) v) :
    ErasesSim E B lps σ lenv (mkAppN (.const c us) as.toArray) v := by
  intro t tb he ⟨T, ht⟩ her hdeps
  obtain ⟨d, rfl⟩ : ∃ d, ci = .defnInfo d := by
    cases ci <;> first | exact ⟨_, rfl⟩ | cases hdef
  obtain ⟨η, hB, -⟩ := henv.lookup_def (SrcDefeq.findDecl_sub hsub hc)
  have hns : ¬ SpecialHead B (.const c us) := fun ⟨_, _, _, hfn, hb', hs⟩ => by
    cases hfn; rw [hB] at hb'; cases hb'; cases hs
  have hsrc : SrcEval σ (SrcConv E B lps) (mkAppN (.const c us) as.toArray) v :=
    .deltaRec hc hdef hco hat hax hrp hpos hlen hlen' hev hconv hb
  have hne : as ≠ [] := fun h => by subst h; simp at hlen; omega
  obtain ⟨⟨th, hth⟩, hargs⟩ := spine_tr hE hns as he ht
  -- every erasure of an argument evaluates to an erasure of its value
  have harg : ∀ (i : Nat) a w a', as[i]? = some a → vs[i]? = some w →
      Erases E B lps σ .nil [] a a' → ErasesDeps E B σ lenv a' →
      ∃ z, Erases E B lps σ .nil [] w z ∧ LBEval defaultFlags lenv a' z := by
    intro i a w a' ha hw hea hda
    obtain ⟨a₀, A, ha₀, hA⟩ := hargs i a ha
    exact ih i a w ha hw ha₀ ⟨A, hA⟩ hea hda
  rcases spine_inv hc hco hrp as her with ⟨hd, as'', rfl, hnb, hhd, hall⟩ |
    ⟨k, as'', hk, rfl, hpe, hall⟩
  · obtain ⟨hdh, hdas⟩ := ErasesDeps.mkApps_iff.1 hdeps
    -- the typed translation of the pre-definition's application
    have hS : List.Forall₂ (SrcDefeq.Sound E B lps) as vs :=
      CasesWhred.forall₂_of_getElem? hlen' fun i a w h1 h2 => by
        intro t T he ht
        exact SrcEval.defeq henv hE hsub he ht (hev i a w h1 h2)
    obtain ⟨t₂, ht₂, hd₂⟩ := SrcDefeq.apps_sound hE hS hns (fun he ht => ⟨_, he, ht⟩) he ht
    obtain ⟨t₃, ht₃, hd₃⟩ := hconv ht₂ hd₂.right
    have hlen'' : as.length = as''.length := hall.length_eq
    have harg' : ∀ (i : Nat) a w a', as[i]? = some a → vs[i]? = some w → as''[i]? = some a' →
        ∃ z, Erases E B lps σ .nil [] w z ∧ LBEval defaultFlags lenv a' z :=
      fun i a w a' ha hw ha' => harg i a w a' ha hw (forall₂_getElem? hall i a a' ha ha')
        (hdas a' (List.mem_of_getElem? ha'))
    rcases head_inv hc hco hrp hhd with ⟨rfl, -⟩ | rfl | ⟨x, b, t₁, rfl, hca, hp, ht₁, hbody, hcl, hfv⟩
    · exact absurd rfl hnb
    · -- the λ□ constant: its declaration is the fixpoint, at the definition's level parameters
      generalize hk : toKername c = kn at hdh
      cases hdh with
      | @const c' ci' cb hfd₂ hl hdecl hbody =>
      cases hinj c c' (by rw [hc]; rfl) (by rw [hfd₂]; rfl) hk
      rw [hc] at hfd₂
      cases hfd₂
      simp only [ErasesDecl, ConstantInfo.value?] at hdecl
      rcases hdecl with ⟨hax', -⟩ | ⟨-, hrp', -⟩ |
        ⟨-, pre', x, b₀, t₀, hrp', hcb, hca, hp, ht₀, hb₀, hcl, hfv⟩
      · rw [hax] at hax'; cases hax'
      · rw [hrp] at hrp'; cases hrp'
      rw [hrp] at hrp'; cases hrp'
      obtain ⟨ls, rfl, hls⟩ := SrcDefeq.trM_const_inv' hB hth
      obtain ⟨p, hpT⟩ := hp
      have hnd : d.levelParams.Nodup :=
        henv.levelParams_nodup (findDecl_eq_some (SrcDefeq.findDecl_sub hsub hc)).1
      have hlu : us.length = d.levelParams.length :=
        RelLevels.TrM.lvlOK henv hE hsub hth _ hc (.inr (.inl ⟨_, rfl⟩))
      have hname : (ConstantInfo.defnInfo d).name = c := (findDecl_eq_some hc).2
      rw [hname] at hca ht₀ hcb
      obtain ⟨t₀', rfl⟩ : ∃ t₀' : Metalean.Expr ζ d.levelParams.length 0, t₀' = t₀ := ⟨t₀, rfl⟩
      have ht₁ : TrM E B lps .nil [] (.const c us) (t₀'{ls}) := by
        have := TrM.instL hls ht₀
        simpa [MLCtx.instL, Pure.instLevels, ConstantInfo.levelParams, ConstantInfo.toConstantVal,
          map_param_instLevel hnd hlu] using this
      have hb₁ := RelLevels.Erases.instL_gen henv hE hsub hls hb₀
        (RelLevels.TrM.lvlOK henv hE hsub hpT)
      have hb₁' : Erases E B lps σ .nil [(some x, .vfix (t₀'{ls}))]
          (Pure.instLevels d.levelParams us pre) b₀ := hb₁
      exact unfold_sim henv hE hsub hc hco hat hax hrp hpos hca ⟨p, hpT⟩ ht₁ hb₁'
        hcl hfv (.delta hl hcb (.atom rfl)) (hbody _ hcb) hne hlen' hlen'' harg' hdas ht₃
        hd₃.right ihb
    · exact unfold_sim henv hE hsub hc hco hat hax hrp hpos hca hp ht₁ hbody hcl hfv (.atom rfl)
        hdh hne hlen' hlen'' harg' hdas ht₃ hd₃.right ihb
  · -- `□` after an erasable prefix: the spine is erasable, and so is its value
    have hwhole : ErasableS E B lps .nil [] (mkAppN (.const c us) as.toArray) := by
      have h := erasable_spine hE (f := mkAppN (.const c us) (as.take k).toArray)
        (fun l => by rw [mkAppN_mkAppN]; exact spine_not_special hns _) hpe (as.drop k)
        (t := t) (T := T) (by rw [mkAppN_mkAppN, List.take_append_drop]; exact he) ht
      rwa [mkAppN_mkAppN, List.take_append_drop] at h
    have hdas := (ErasesDeps.mkApps_iff.1 hdeps).2
    refine ⟨.box, .box (ErasableS.eval henv hE hsub he ht hsrc hwhole), eval_box_spine _ ?_⟩
    intro a' ha'
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha'
    have hj' : j < (as.drop k).length := by rw [hall.length_eq]; exact hj
    have ha : as[k + j]? = some (as.drop k)[j] := by
      rw [← List.getElem?_drop]; exact List.getElem?_eq_getElem hj'
    have hkj : k + j < vs.length := by simp at hj'; omega
    have hw : vs[k + j]? = some vs[k + j] := List.getElem?_eq_getElem hkj
    obtain ⟨z, -, hz⟩ := harg (k + j) _ _ _ ha hw
      (forall₂_getElem? hall j _ _ (List.getElem?_eq_getElem hj') (List.getElem?_eq_getElem hj))
      (hdas _ ha')
    exact ⟨z, hz⟩

end

end EraseProof
