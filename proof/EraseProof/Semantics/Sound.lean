import EraseProof.Semantics.DecodeAt
import EraseProof.Source.MarkRead
import EraseProof.Source.Decls
import EraseProof.Bridge.CLAccept
import EraseProof.Statements

/-!
# The meaning of source evaluation

`srcEval_sound`: a source evaluation of the marked input preserves meaning in every con-leche
model. The proof is an induction on the evaluation, each rule closed by its step lemma
(`EraseProof.Semantics.Cases`, `Iota`, `Rec`, `Frozen`), the stored records each step reads decoded
from con-leche's acceptance of the program (`EraseProof.Semantics.DecodeAt`), and the passage to
`Sound` at the end (`Sound.of_semSim`). Its side condition is that the subject reads with every
constant stored (`Resolved`): δ unfolds only a stored, hence safe, definition.
-/

open Lean Erasure

namespace EraseProof

universe w

/-- `t` reads through its marks with its constants stored: the reading of `unmark t` exists, and
its constants, projection structures and literal support constants are stored in `env`
(`clResolves`). It holds of the marked input, which con-leche types, and of every subject a rule
of `SrcEval` continues with: a subterm, a stored value, or a part of the redex the rule's
certificate types. Reference: none (DV-33). -/
def Resolved (env : ConLeche.Env) (t : Expr) : Prop :=
  ∃ c, toCL? (unmark t) = some c ∧ clResolves env c = true

namespace Resolve

variable {env : ConLeche.Env}

/-- Substituting a term whose constants are stored keeps them stored. -/
theorem clResolves_inst {v : ConLeche.Expr} (hv : clResolves env v = true) :
    ∀ (e : ConLeche.Expr) (k : Nat), clResolves env e = true →
      clResolves env (e.instantiate1 v k) = true := by
  intro e
  induction e with
  | bvar i =>
    intro k _
    simp only [ConLeche.Expr.instantiate1]
    split
    · exact hv
    · split <;> rfl
  | fvar _ _ | sort _ => intro _ _; rfl
  | const _ _ | lit _ => intro _ h; exact h
  | app f a ihf iha =>
    intro k h
    simp only [ConLeche.Expr.instantiate1, clResolves, Bool.and_eq_true] at h ⊢
    exact ⟨ihf k h.1, iha k h.2⟩
  | lam t b iht ihb | forallE t b iht ihb =>
    intro k h
    simp only [ConLeche.Expr.instantiate1, clResolves, Bool.and_eq_true] at h ⊢
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | letE t u b iht ihu ihb =>
    intro k h
    simp only [ConLeche.Expr.instantiate1, clResolves, Bool.and_eq_true] at h ⊢
    exact ⟨⟨iht k h.1.1, ihu k h.1.2⟩, ihb (k + 1) h.2⟩
  | proj s i e ih =>
    intro k h
    simp only [ConLeche.Expr.instantiate1, clResolves, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, ih k h.2⟩

/-- Instantiating level parameters keeps every constant. -/
theorem clResolves_instLP (ks : List ConLeche.Name) (us : List ConLeche.Level) (e : ConLeche.Expr) :
    clResolves env (e.instantiateLevelParams ks us) = clResolves env e := by
  induction e <;> simp_all [ConLeche.Expr.instantiateLevelParams, clResolves]

/-- A term con-leche types reads closed with its constants stored (`CLTyped.closed`,
`infer_clResolves`). -/
theorem typed_read {t : Expr} (h : CLTyped env t) :
    ∃ c, toCL? t = some c ∧ c.looseBVarsBounded 0 = true ∧ clResolves env c = true := by
  obtain ⟨c, F, T, hc, hi⟩ := h
  exact ⟨c, hc, CLTyped.closed ⟨c, F, T, hc, hi⟩ hc,
    infer_clResolves (ConLeche.Rules.inferTypeCore_bridge hi) rfl⟩

/-- A term a run-time certificate types is resolved (its second run, on `unmark t`). -/
theorem of_ok {t : Expr} (h : CLOk env t) : Resolved env t :=
  let ⟨c, hc, _, hr⟩ := typed_read h.2
  ⟨c, hc, hr⟩

/-- A frozen subterm is resolved as the subterm. -/
theorem erase {s : Expr} : Resolved env (markErase s) ↔ Resolved env s := Iff.rfl

/-- A reduced discriminant is resolved as the discriminant. -/
theorem reduced {s : Expr} : Resolved env (markReduced s) ↔ Resolved env s := Iff.rfl

/-- An application is resolved iff its function and argument are. -/
theorem app {f a : Expr} : Resolved env (.app f a) ↔ Resolved env f ∧ Resolved env a := by
  constructor
  · rintro ⟨c, hc, hr⟩
    obtain ⟨cf, ca, hcf, hca, rfl⟩ := SemCases.toCL?_unmark_app hc
    simp only [clResolves, Bool.and_eq_true] at hr
    exact ⟨⟨cf, hcf, hr.1⟩, ⟨ca, hca, hr.2⟩⟩
  · rintro ⟨⟨cf, hcf, hrf⟩, ⟨ca, hca, hra⟩⟩
    exact ⟨.app cf ca, by simp [unmark, toCL?, hcf, hca], by simp [clResolves, hrf, hra]⟩

/-- A spine is resolved iff its head and arguments are. -/
theorem foldl : ∀ {as : List Expr} {f : Expr},
    Resolved env (as.foldl .app f) ↔ Resolved env f ∧ ∀ a ∈ as, Resolved env a
  | [], _ => by simp
  | a :: as, f => by
    rw [List.foldl_cons, foldl, app]
    simp only [List.mem_cons, forall_eq_or_imp, and_assoc]

/-- `foldl` at `mkAppN`. -/
theorem appN {f : Expr} {as : List Expr} :
    Resolved env (mkAppN f as.toArray) ↔ Resolved env f ∧ ∀ a ∈ as, Resolved env a := by
  rw [mkAppN_toArray]; exact foldl

/-- A projection is resolved iff its structure is stored and its subject resolved. -/
theorem proj {S : Name} {i : Nat} {e : Expr} :
    Resolved env (.proj S i e) ↔ (env.find? (Name.toCL S)).isSome = true ∧ Resolved env e := by
  constructor
  · rintro ⟨c, hc, hr⟩
    simp only [unmark, toCL?, Option.map_eq_map, Option.map_eq_some_iff] at hc
    obtain ⟨ce, hce, rfl⟩ := hc
    simp only [clResolves, Bool.and_eq_true] at hr
    exact ⟨hr.1, ce, hce, hr.2⟩
  · rintro ⟨hS, ce, hce, hr⟩
    exact ⟨.proj (Name.toCL S) i ce, by simp [unmark, toCL?, hce], by simp [clResolves, hS, hr]⟩

/-- A resolved constant is stored. -/
theorem const {c : Name} {us : List Level} (h : Resolved env (.const c us)) :
    (env.find? (Name.toCL c)).isSome = true := by
  obtain ⟨cc, hc, hr⟩ := h
  simp only [unmark, toCL?, Option.map_eq_map, Option.map_eq_some_iff] at hc
  obtain ⟨_, -, rfl⟩ := hc
  exact hr

/-- The head constant of a resolved spine is stored. -/
theorem head {c : Name} {us : List Level} {as : List Expr}
    (h : Resolved env (mkAppN (.const c us) as.toArray)) : (env.find? (Name.toCL c)).isSome = true :=
  const (appN.mp h).1

/-- η-contraction keeps a reading with its constants stored. -/
theorem etaContract_read {x : Expr} {c : ConLeche.Expr} (hx : toCL? x = some c)
    (hr : clResolves env c = true) :
    ∃ c', toCL? (etaContract x) = some c' ∧ clResolves env c' = true := by
  unfold etaContract
  split
  · rename_i f _
    split
    · exact ⟨c, hx, hr⟩
    · rename_i hno
      simp only [toCL?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        Option.some.injEq] at hx
      obtain ⟨cA, -, cb, ⟨cf, hcf, ca, -, rfl⟩, rfl⟩ := hx
      simp only [clResolves, Bool.and_eq_true] at hr
      rw [SemCases.inst_absent (.bvar 0) (.sort .zero) f 0 (by simpa using hno),
        toCL?_instantiate1'_closed (ca := .sort .zero) rfl rfl f 0, hcf]
      exact ⟨_, rfl, clResolves_inst rfl cf 0 hr.2.1⟩
  · exact ⟨c, hx, hr⟩

/-- The three readings of a metadata node through `unmark`. -/
theorem unmark_mdata (d : MData) (e : Expr) : unmark (.mdata d e) = unmark e ∨
    unmark (.mdata d e) = etaContract (unmark e) ∨ unmark (.mdata d e) = .mdata d (unmark e) := by
  simp only [unmark]; split <;> simp

/-- A term whose reading has its constants stored is resolved: `unmark` drops marks and
η-contracts, which keeps every constant. -/
theorem of_read : ∀ {t : Expr} {c : ConLeche.Expr}, toCL? t = some c → clResolves env c = true →
    Resolved env t
  | .bvar _, c, h, hr | .sort _, c, h, hr | .const .., c, h, hr | .lit _, c, h, hr =>
    ⟨c, by simpa [unmark] using h, hr⟩
  | .fvar _, _, h, _ | .mvar _, _, h, _ => by simp [toCL?] at h
  | .app f a, c, h, hr => by
    simp only [toCL?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨cf, hf, ca, ha, rfl⟩ := h
    simp only [clResolves, Bool.and_eq_true] at hr
    exact app.mpr ⟨of_read hf hr.1, of_read ha hr.2⟩
  | .lam _ t b _, c, h, hr => by
    simp only [toCL?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨ct, ht, cb, hb, rfl⟩ := h
    simp only [clResolves, Bool.and_eq_true] at hr
    obtain ⟨ct', ht', hrt⟩ := of_read ht hr.1
    obtain ⟨cb', hb', hrb⟩ := of_read hb hr.2
    exact ⟨.lam ct' cb', by simp [unmark, toCL?, ht', hb'], by simp [clResolves, hrt, hrb]⟩
  | .forallE _ t b _, c, h, hr => by
    simp only [toCL?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨ct, ht, cb, hb, rfl⟩ := h
    simp only [clResolves, Bool.and_eq_true] at hr
    obtain ⟨ct', ht', hrt⟩ := of_read ht hr.1
    obtain ⟨cb', hb', hrb⟩ := of_read hb hr.2
    exact ⟨.forallE ct' cb', by simp [unmark, toCL?, ht', hb'], by simp [clResolves, hrt, hrb]⟩
  | .letE _ t u b _, c, h, hr => by
    simp only [toCL?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨ct, ht, cu, hu, cb, hb, rfl⟩ := h
    simp only [clResolves, Bool.and_eq_true] at hr
    obtain ⟨ct', ht', hrt⟩ := of_read ht hr.1.1
    obtain ⟨cu', hu', hru⟩ := of_read hu hr.1.2
    obtain ⟨cb', hb', hrb⟩ := of_read hb hr.2
    exact ⟨.letE ct' cu' cb', by simp [unmark, toCL?, ht', hu', hb'],
      by simp [clResolves, hrt, hru, hrb]⟩
  | .proj s _ e, c, h, hr => by
    simp only [toCL?, Option.map_eq_map, Option.map_eq_some_iff] at h
    obtain ⟨ce, hce, rfl⟩ := h
    simp only [clResolves, Bool.and_eq_true] at hr
    exact proj.mpr ⟨hr.1, of_read hce hr.2⟩
  | .mdata d e, c, h, hr => by
    obtain ⟨c', hc', hr'⟩ := of_read (t := e) h hr
    rcases unmark_mdata d e with hu | hu | hu <;> unfold Resolved <;> rw [hu]
    · exact ⟨c', hc', hr'⟩
    · exact etaContract_read hc' hr'
    · exact ⟨c', hc', hr'⟩

/-- The body of a binder instantiated at a closed term, both read with their constants stored, is
resolved. -/
theorem inst {b a : Expr} {cb ca : ConLeche.Expr} (hb : toCL? b = some cb)
    (hrb : clResolves env cb = true) (ha : toCL? a = some ca) (hca : ca.looseBVarsBounded 0 = true)
    (hra : clResolves env ca = true) : Resolved env (b.instantiate1' a) :=
  of_read (by rw [toCL?_instantiate1'_closed ha hca, hb]; rfl) (clResolves_inst hra cb 0 hrb)

/-- The constructor form of a resolved recursor major is resolved: a Nat literal's support
constants are stored. -/
theorem natLitCtor {m : Expr} (h : Resolved env m) : Resolved env (EraseProof.natLitCtor m) := by
  rcases Decls.natLitCtor_cases m with ⟨k, rfl⟩ | he
  · obtain ⟨c, hc, hr⟩ := h
    simp only [unmark, toCL?, Option.some.injEq] at hc
    subst hc
    simp only [clResolves, ConLeche.natLitStored, Bool.and_eq_true] at hr
    match k with
    | 0 => exact ⟨_, rfl, hr.1.2⟩
    | k + 1 =>
      exact app.mpr ⟨⟨_, rfl, hr.2⟩, ⟨_, rfl, by simp [clResolves, ConLeche.natLitStored, hr]⟩⟩
  · rw [he]; exact h

/-- A spine con-leche types, read: its head and its arguments read closed with their constants
stored. -/
theorem read_spine : ∀ {as : List Expr} {f : Expr} {c : ConLeche.Expr},
    toCL? (as.foldl .app f) = some c → c.looseBVarsBounded 0 = true → clResolves env c = true →
    (∃ cf, toCL? f = some cf ∧ cf.looseBVarsBounded 0 = true ∧ clResolves env cf = true) ∧
      ∀ a ∈ as, ∃ ca, toCL? a = some ca ∧ ca.looseBVarsBounded 0 = true ∧ clResolves env ca = true
  | [], _, c, h, hb, hr => ⟨⟨c, h, hb, hr⟩, by simp⟩
  | a :: as, f, c, h, hb, hr => by
    obtain ⟨⟨cfa, hfa, hbfa, hrfa⟩, has⟩ := read_spine (as := as) (f := .app f a) h hb hr
    simp only [toCL?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at hfa
    obtain ⟨cf, hcf, ca, hca, rfl⟩ := hfa
    simp only [ConLeche.Expr.looseBVarsBounded, clResolves, Bool.and_eq_true] at hbfa hrfa
    refine ⟨⟨cf, hcf, hbfa.1, hrfa.1⟩, ?_⟩
    simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨⟨ca, hca, hbfa.2, hrfa.2⟩, has⟩

/-- The body of a λ read closed with its constants stored, instantiated at a closed term read with
its constants stored, is resolved. -/
theorem lamInst {n : Name} {A b a : Expr} {bi : BinderInfo} {cl ca : ConLeche.Expr}
    (hl : toCL? (.lam n A b bi) = some cl) (hrl : clResolves env cl = true)
    (ha : toCL? a = some ca) (hca : ca.looseBVarsBounded 0 = true)
    (hra : clResolves env ca = true) : Resolved env (b.instantiate1' a) := by
  simp only [toCL?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.some.injEq] at hl
  obtain ⟨cA, -, cb, hb, rfl⟩ := hl
  simp only [clResolves, Bool.and_eq_true] at hrl
  exact inst hb hrl.2 ha hca hra

/-- The β contractum of a redex con-leche types is resolved; the λ may be `eta`-marked
(`toCL?` is transparent to marks). -/
theorem beta {F a b A : Expr} {n : Name} {bi : BinderInfo}
    (hF : toCL? F = toCL? (.lam n A b bi)) (h : CLTyped env (.app F a)) :
    Resolved env (b.instantiate1' a) := by
  obtain ⟨c, hc, hb, hr⟩ := typed_read h
  obtain ⟨⟨cf, hcf, -, hrf⟩, has⟩ := read_spine (as := [a]) (f := F) hc hb hr
  obtain ⟨ca, hca, hba, hra⟩ := has a (by simp)
  exact lamInst (hF ▸ hcf) hrf hca hba hra

end Resolve

/-! ## The program's records behind the closure's -/

namespace Lookup

variable {D P : List ConstantInfo}

/-- A declaration of a sub-environment is the program's. -/
theorem findDecl_sub (hs : SubEnv D P) {c : Name} {ci : ConstantInfo} (h : findDecl D c = some ci) :
    findDecl P c = some ci := by
  obtain ⟨hm, rfl⟩ := findDecl_mem h
  exact hs ci hm

/-- `ctorAlts` succeeds alike in the program. -/
theorem ctorAlts_sub (hs : SubEnv D P) : ∀ {cs : List Name} {as : List CasesAltInfo},
    ctorAlts D cs = some as → ctorAlts P cs = some as
  | [], _, h => h
  | c :: cs, as, h => by
    simp only [ctorAlts] at h ⊢
    cases hc : findConst D c with
    | none => simp [hc] at h
    | some ci =>
      cases ha : ctorAlts D cs with
      | none => simp [hc, ha] at h
      | some as' =>
        rw [hc, ha] at h
        rw [show findConst P c = some ci from findDecl_sub hs hc, ctorAlts_sub hs ha]
        exact h

/-- `blockCtorCount` succeeds alike in the program. -/
theorem blockCtorCount_sub (hs : SubEnv D P) : ∀ {ts : List Name} {k : Nat},
    blockCtorCount D ts = some k → blockCtorCount P ts = some k
  | [], _, h => h
  | t :: ts, k, h => by
    simp only [blockCtorCount] at h ⊢
    cases hc : findConst D t with
    | none => simp [hc] at h
    | some ci =>
      cases ha : blockCtorCount D ts with
      | none => simp [hc, ha] at h
      | some k' =>
        rw [hc, ha] at h
        rw [show findConst P t = some ci from findDecl_sub hs hc, blockCtorCount_sub hs ha]
        exact h

/-- The recognizer answers alike in the program: what it reads of a sub-environment when it
answers is the program's. -/
theorem casesInfo?_sub (hs : SubEnv D P) {n : Name} {ci : CasesInfo} (h : casesInfo? D n = some ci) :
    casesInfo? P n = some ci := by
  unfold casesInfo? at h ⊢
  split at h
  next T =>
    split at h
    next d I R hd hI hR =>
      rw [show findConst P _ = _ from findDecl_sub hs hd, show findConst P T = _ from findDecl_sub hs hI,
        show findConst P (mkRecName T) = _ from findDecl_sub hs hR]
      dsimp only at h ⊢
      split at h
      next j body alts before hj hb ha hbe =>
        rw [hj, hb, ctorAlts_sub hs ha, blockCtorCount_sub hs hbe]
        exact h
      next => cases h
    next => cases h
  next => cases h

/-- A recognized `casesOn` of a sub-environment is the program's. -/
theorem casesOnOf?_sub (hs : SubEnv D P) {c : Name} {iv : InductiveVal}
    (h : casesOnOf? D c = some iv) : casesOnOf? P c = some iv := by
  unfold casesOnOf? at h ⊢
  split at h
  · rename_i ci hci
    split at h
    · rename_i iv' hiv'
      rw [casesInfo?_sub hs hci]
      dsimp only
      rw [findDecl_sub hs hiv']
      exact h
    · cases h
  · cases h

/-- `mapM` in `Option` under a function that answers alike where the first answers. -/
theorem mapM_sub {α β : Type} {f g : α → Option β} (hfg : ∀ x y, f x = some y → g x = some y) :
    ∀ {l : List α} {r : List β}, l.mapM f = some r → l.mapM g = some r
  | [], _, h => h
  | x :: l, r, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h ⊢
    obtain ⟨y, hy, ys, hys, rfl⟩ := h
    exact ⟨y, hfg x y hy, ys, mapM_sub hfg hys, rfl⟩

/-- A recursor's block read in a sub-environment is the program's. -/
theorem recBlockOf?_sub (hs : SubEnv D P) {rv : RecursorVal}
    {r : List InductiveVal × List ConstructorVal} (h : recBlockOf? D rv = some r) :
    recBlockOf? P rv = some r := by
  simp only [recBlockOf?, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h ⊢
  obtain ⟨ivs, hivs, cvs, hcvs, rfl⟩ := h
  refine ⟨ivs, mapM_sub (fun x y hx => ?_) hivs, cvs, mapM_sub (fun x y hx => ?_) hcvs, rfl⟩
  · split at hx
    · rename_i iv hiv; rw [findDecl_sub hs hiv]; exact hx
    · cases hx
  · split at hx
    · rename_i cv hcv; rw [findDecl_sub hs hcv]; exact hx
    · cases hx

/-- What δ unfolds: a definition, its value. -/
theorem unfold?_spec {σ : EvalEnv} {c : Name} {ci : ConstantInfo} {body : Expr}
    (h : σ.unfold? c = some (ci, body)) :
    ∃ dv, findDecl σ.decls c = some (.defnInfo dv) ∧ ci = .defnInfo dv ∧ body = dv.value := by
  unfold EvalEnv.unfold? at h
  split at h
  · rename_i dv hdv
    split at h
    · cases h
    · cases h; exact ⟨dv, hdv, rfl, rfl⟩
  · cases h

end Lookup

/-- **A definition con-leche stores is safe**: the stored constant at its name was installed by a
record of `P` (`foldlM_checkDecl_run`) under a name that record declares (`checkDecl_names`); that
name is the definition's own (`declOf?_names`: a block's records name no definition), and
`declOf?` writes no record for an unsafe or partial definition. The converse of
`ConLecheAccepts.find?_defn`. Reference: `CL ConLeche/Kernel/CheckDecl.lean:178 checkDeclsPure`. -/
theorem ConLecheAccepts.defn_safe {P : List ConstantInfo} {env : ConLeche.Env}
    (h : ConLecheAccepts P env) {c : Name} {v : DefinitionVal}
    (hv : findDecl P c = some (.defnInfo v)) (hs : (env.find? (Name.toCL c)).isSome = true) :
    v.safety = .safe := by
  obtain ⟨ds, hds, hf, -⟩ := h
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hs
  have hxn : x.name = Name.toCL c := by simpa using List.find?_some hx
  obtain ⟨-, hrun, hcs⟩ := foldlM_checkDecl_run ds hf
  rcases hcs x (List.mem_of_find?_eq_some hx) with h0 | ⟨d, hd, hxd⟩
  · exact absurd h0 (by simp [ConLeche.Env.empty])
  obtain ⟨e, e', hstep, -⟩ := hrun d hd
  obtain ⟨ci, hci, L, hL, hdL⟩ := DeclsOf?.mem_rev hds hd
  obtain ⟨ci', hci', he, hk⟩ := declOf?_names hci hL hdL _ (checkDecl_names hstep x hxd)
  have hc' : findDecl P c = some ci' := by
    rw [hxn] at he; rw [Name.toCL_injective he]; exact findDecl_self (DeclsOf?.nodup hds) hci'
  rw [hv, Option.some.injEq] at hc'
  subst hc'
  rcases hk with rfl | hk
  · cases hsv : v.safety <;> simp_all [declOf?]
  · exact absurd rfl (hk v)

/-- **Every constructor of an accepted program is listed by its inductive** at its index, with
its parameter count: `declOf?` asks its inductive to list it, `blockShapeOK` (`blockOf?_shape`)
gives its index and parameter count. Reference: `declared_constructor`
(`MR common/theories/EnvironmentTyping.v:36`). -/
theorem ConLecheAccepts.ctorsListed {P : List ConstantInfo} {env : ConLeche.Env}
    (h : ConLecheAccepts P env) : CtorsListed P := by
  intro c cv hc
  obtain ⟨hmem, hn⟩ := findDecl_mem hc
  have hn : cv.name = c := hn
  obtain ⟨ds, hds, -⟩ := id h
  obtain ⟨L, hL, -⟩ := DeclsOf?.mem hds hmem
  simp only [declOf?] at hL
  split at hL
  · rename_i t ht
    split at hL
    · rename_i hcont
      have ht0 : findDecl P cv.induct = some (.inductInfo t) := ht
      have htn : t.name = cv.induct := (findDecl_mem ht0).2
      have ht' : findConst P t.name = some (.inductInfo t) := by rw [htn]; exact ht
      obtain ⟨Hn, H, hH, hhead, -, htm⟩ := h.head (findDecl_mem ht0).1
      obtain ⟨blk, p, hbH, -, -⟩ := h.block hH hhead (h.ind_safe (findDecl_mem hH).1)
      obtain ⟨-, hpar, hctors, -⟩ := (Decode.blockOf?_shape hbH).2 t.name htm t ht'
      obtain ⟨j, hj⟩ := List.getElem?_of_mem (show cv.name ∈ t.ctors by simpa using hcont)
      obtain ⟨-, hcidx, hnp, -⟩ := hctors j cv.name hj cv (by rw [hn]; exact hc)
      exact ⟨t, ht0, by rw [hcidx, hj, hn], hpar.trans hnp.symm⟩
    · cases hL
  · cases hL

/-- **The program's `Nat` is con-leche's pinned one**: the record of `Nat`'s block passes
con-leche's reserved-names check (`CL ConLeche/Kernel/Basis.lean:144 basisNamesOk`), so it is the
pin `CL ConLeche/Kernel/Basis/Nat.lean:68 natBasis` and its install stores the pins
(`CL ConLeche/Verify/BasisBlock.lean:308 blockInstall_pinned`): the former lists `Nat.zero` and
`Nat.succ`, in that order, with no parameter and no field, resp. one field. Reference: none
(DV-30). -/
theorem ConLecheAccepts.natCtors {P : List ConstantInfo} {env : ConLeche.Env}
    (h : ConLecheAccepts P env) {iv : InductiveVal}
    (hiv : findDecl P ``Nat = some (.inductInfo iv)) :
    (∃ z, findDecl P ``Nat.zero = some (.ctorInfo z) ∧ z.induct = ``Nat ∧ z.cidx = 0 ∧
      z.numParams = 0 ∧ z.numFields = 0) ∧
    ∃ s, findDecl P ``Nat.succ = some (.ctorInfo s) ∧ s.induct = ``Nat ∧ s.cidx = 1 ∧
      s.numParams = 0 ∧ s.numFields = 1 := by
  have hivn : iv.name = ``Nat := (findDecl_mem hiv).2
  have hiv' : findConst P ``Nat = some (.inductInfo iv) := hiv
  obtain ⟨Hn, H, hH, hhead, -, hNm⟩ := h.head (findDecl_mem hiv).1
  rw [hivn] at hNm
  obtain ⟨block, p, hb, hdf, hst, -⟩ := h.blockPins hH hhead
  have hHn : H.name = Hn := (findDecl_mem hH).2
  have hhn : H.all.head? = some H.name := by rw [hHn]; exact hhead
  have hdecl : declOf? P (.inductInfo H) = some [.indDecl block H.numParams] := by
    simp [declOf?, h.ind_safe (findDecl_mem hH).1, hhn, hb]
  obtain ⟨⟨e, e', hrun⟩, -⟩ := h.stored (findDecl_mem hH).1 hdecl
  have hnames := (ConLeche.Semantics.checkDeclRun_ofEnvFactsK hrun).1
  obtain ⟨block', he, -, hfwd⟩ := blockOf?_spec hb
  cases he
  obtain ⟨t, ht, ⟨cvN, hcvN, hNb⟩, hctN⟩ := hfwd ``Nat hNm
  rw [hiv', Option.some.injEq, ConstantInfo.inductInfo.injEq] at ht
  subst ht
  have hNname : ConLeche.natName ∈ block.map (·.name) := by
    obtain ⟨ty, -, rfl⟩ := cvOf?_eq_some hcvN
    refine List.mem_map.mpr ⟨_, hNb, ?_⟩
    show Name.toCL iv.name = _
    rw [hivn]; rfl
  have hk : ConLeche.basisNameHit block = some .natK := by
    cases hk : ConLeche.basisNameHit block with
    | none =>
      simp only [ConLeche.basisNamesOk, hk, List.all_eq_true] at hnames
      obtain ⟨b, hbm, hbn⟩ := List.mem_map.mp hNname
      have := hnames b hbm
      rw [hbn] at this
      exact absurd this (by decide)
    | some kind =>
      have hkn : kind.decls.map (·.name) = block.map (·.name) := by
        simpa using List.find?_some hk
      have hkm := List.mem_of_find?_eq_some hk
      rw [← hkn] at hNname
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hkm
      rcases hkm with rfl | rfl | rfl | rfl <;> first | rfl | (revert hNname; decide)
  have hok : ConLeche.pinListOk block ConLeche.natBasis = true := by
    simpa [ConLeche.basisNamesOk, hk, ConLeche.BasisKind.decls] using hnames
  have hC := (ConLeche.blockInstall_pinned hk hok hdf).1
  have hkn : ConLeche.natBasis.map (·.name) = block.map (·.name) := by
    simpa [ConLeche.BasisKind.decls] using List.find?_some hk
  obtain ⟨b1, b2, b3, b4, rfl⟩ : ∃ b1 b2 b3 b4, block = [b1, b2, b3, b4] := by
    have hl := congrArg List.length hkn
    simp [ConLeche.natBasis] at hl
    match block, hl with
    | [b1, b2, b3, b4], _ => exact ⟨b1, b2, b3, b4, rfl⟩
  have hfind : ∀ c ∈ ConLeche.BasisKind.natK.storedAt [b1, b2, b3, b4],
      env.find? c.name = some c := fun c hc => hst c (hC ▸ hc)
  simp only [ConLeche.BasisKind.storedAt, ConLeche.BasisKind.installed, List.zipWith_cons_cons,
    List.zipWith_nil_left, List.mem_cons, forall_eq_or_imp] at hfind
  obtain ⟨hfN, hfZ, hfS, -⟩ := hfind
  have hfN : env.find? ConLeche.natName = some (.indInfo _
      { all := [ConLeche.natName], ctors := [ConLeche.natZeroName, ConLeche.natSuccName],
        neverZero := true }) := hfN
  have hfZ : env.find? ConLeche.natZeroName = some (.ctorInfo _ 0 0 ConLeche.natName) := hfZ
  have hfS : env.find? ConLeche.natSuccName = some (.ctorInfo _ 0 1 ConLeche.natName) := hfS
  obtain ⟨-, -, hbs⟩ := h.blockStored hH hhead
  obtain ⟨⟨cvt, caps, -, hfT, -, hcc⟩, hctor⟩ := hbs ``Nat hNm iv hiv'
  rw [show Name.toCL ``Nat = ConLeche.natName from rfl, hfN] at hfT
  simp only [Option.some.injEq, ConLeche.ConstantInfo.indInfo.injEq] at hfT
  have hctors : iv.ctors = [``Nat.zero, ``Nat.succ] := by
    have hm : iv.ctors.map Name.toCL = [``Nat.zero, ``Nat.succ].map Name.toCL := by
      rw [← hcc, ← hfT.2]; rfl
    exact (List.map_inj_right fun _ _ h => Name.toCL_injective h).mp hm
  obtain ⟨-, -, hshape, -⟩ := (Decode.blockOf?_shape hb).2 ``Nat hNm iv hiv'
  obtain ⟨z, hz, -⟩ := hctN ``Nat.zero (by rw [hctors]; simp)
  obtain ⟨s, hs, -⟩ := hctN ``Nat.succ (by rw [hctors]; simp)
  obtain ⟨hzi, hzc, -⟩ := hshape 0 _ (by rw [hctors]; rfl) z hz
  obtain ⟨hsi, hsc, -⟩ := hshape 1 _ (by rw [hctors]; rfl) s hs
  obtain ⟨_, -, hzf⟩ := hctor ``Nat.zero (by rw [hctors]; simp) z hz
  obtain ⟨_, -, hsf⟩ := hctor ``Nat.succ (by rw [hctors]; simp) s hs
  rw [show Name.toCL ``Nat.zero = ConLeche.natZeroName from rfl, hfZ] at hzf
  rw [show Name.toCL ``Nat.succ = ConLeche.natSuccName from rfl, hfS] at hsf
  simp only [Option.some.injEq, ConLeche.ConstantInfo.ctorInfo.injEq] at hzf hsf
  exact ⟨⟨z, hz, hzi.trans hivn, hzc, hzf.2.1.symm, hzf.2.2.1.symm⟩,
    s, hs, hsi.trans hivn, hsc, hsf.2.1.symm, hsf.2.2.1.symm⟩

/-- A projection con-leche types has a stored table at its field (`CL ConLeche/Rules/Rel.lean:667
Infer.proj`, on the derivation of `CL ConLeche/Verify/Rules/Bridge.lean:67 inferTypeCore_bridge`). -/
theorem findProj_of_typed {env : ConLeche.Env} {S : Name} {i : Nat} {m : Expr}
    (h : CLTyped env (.proj S i m)) : ∃ entry, env.findProj? (Name.toCL S) i = some entry := by
  obtain ⟨c, F, T, hc, hi⟩ := h
  simp only [toCL?, Option.map_eq_map, Option.map_eq_some_iff] at hc
  obtain ⟨cm, -, rfl⟩ := hc
  match ConLeche.Rules.inferTypeCore_bridge hi with
  | .proj _ _ _ hfp _ _ _ => exact ⟨_, hfp⟩

/-- An inductive of an accepted program is stored (`ConLecheAccepts.blockStored`). -/
theorem ConLecheAccepts.ind_stored {P : List ConstantInfo} {env : ConLeche.Env}
    (h : ConLecheAccepts P env) {T : Name} {iv : InductiveVal}
    (hT : findDecl P T = some (.inductInfo iv)) : (env.find? (Name.toCL T)).isSome = true := by
  obtain ⟨Hn, H, hH, hhead, -, hm⟩ := h.head (findDecl_mem hT).1
  obtain ⟨-, -, hst⟩ := h.blockStored hH hhead
  have hTn : iv.name = T := (findDecl_mem hT).2
  obtain ⟨⟨cvT, caps, -, hf, -⟩, -⟩ := hst T (hTn ▸ hm) iv hT
  rw [hf]; rfl

/-- The quotient's ι case split at the evaluation rule's level (`SrcEval.quotLift`), read as the
step lemma asks it: at the reading of every level list (`CL ConLeche/Verify/Rules/RedBridge.lean:285
iotaCaseAt_bridge`). -/
theorem quotCase {env : ConLeche.Env} {us : List Level}
    (h : ∃ l F, us.head?.bind Level.toCL = some l ∧
      ConLeche.iotaCaseAt (ConLeche.pureFns .verified false env F).whnf env.find? false
        (Name.toCL ``Quot) [l] = .ok false) :
    ∀ usL, us.mapM Level.toCL = some usL →
      ConLeche.Rules.IotaCaseS env false ConLeche.quotName (usL.take 1) false := by
  intro usL hus
  obtain ⟨l, F, hl, hF⟩ := h
  cases us with
  | nil => simp at hl
  | cons u us₀ =>
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hus
    obtain ⟨l', hl', _, -, rfl⟩ := hus
    simp only [List.head?_cons, Option.bind_some, hl', Option.some.injEq] at hl
    subst hl
    exact ConLeche.Rules.iotaCaseAt_bridge (ConLeche.Rules.bridge env F).2.1 hF

/-! ## The induction -/

/-- **A source evaluation keeps meaning, from a resolved subject**: induction on `SrcEval`, each
rule closed by its step lemma (`SemCases.srcEval_sound_*`), the stored records it reads decoded
from con-leche's acceptance of `P` (`ConLecheAccepts.casesIotaAt`, `casesFrozenAt`, `projAt`,
`recIotaAt`, `find?_defn`, `find?_quot`) at the program's records behind the closure's
(`Lookup`), each certificate graded (`CLOk.gradedU`), and every continuation resolved: a subterm,
a part of a certified redex, or a stored value (δ, whose constant is then stored, hence a safe
definition, `ConLecheAccepts.defn_safe`). Reference: the induction of subject reduction
(`MR P/PCUICSR.v`), on con-leche's model (DV-33, DV-34). -/
theorem semSim_of_srcEval {P : List ConstantInfo} {env : ConLeche.Env} {σ : EvalEnv}
    (hacc : ConLecheAccepts P env) (hsub : SubEnv σ.decls P) (hd : NoMarkKeysDecls σ.decls = true)
    {t v : Expr} (hev : SrcEval env σ t v) : Resolved env t → SemSim.{w} env t v := by
  have hcl := hacc.ctorsListed
  have hsafe : ∀ {c : Name} {us : List Level} {as : List Expr},
      Resolved env (mkAppN (.const c us) as.toArray) →
      ∀ dv, findDecl P c = some (.defnInfo dv) → dv.safety = .safe :=
    fun h _ hdv => hacc.defn_safe hdv (Resolve.head h)
  have mem? : ∀ {as : List Expr} {i : Nat} {a : Expr}, as[i]? = some a → a ∈ as :=
    List.mem_of_getElem?
  induction hev with
  | beta _ _ _ hok _ ihf iha ihb =>
    intro hres
    obtain ⟨rf, ra⟩ := Resolve.app.mp hres
    exact SemCases.srcEval_sound_beta (CLOk.gradedU hok) (ihf rf) (iha ra)
      (ihb (Resolve.beta (n := .anonymous) (bi := .default) rfl hok.1))
  | etaBeta _ _ _ hok _ ihf iha ihb =>
    intro hres
    obtain ⟨rf, ra⟩ := Resolve.app.mp hres
    exact SemCases.srcEval_sound_etaBeta (CLOk.gradedU hok) (ihf rf) (iha ra)
      (ihb (Resolve.beta (n := .anonymous) (bi := .default) rfl hok.1))
  | zeta _ hok hok' _ ihv ihb =>
    intro hres
    obtain ⟨c, hc, hr⟩ := hres
    simp only [unmark, toCL?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at hc
    obtain ⟨_, -, cv, hcv, _, -, rfl⟩ := hc
    simp only [clResolves, Bool.and_eq_true] at hr
    obtain ⟨c', hc', hb', hr'⟩ := Resolve.typed_read hok'.1
    simp only [toCL?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at hc'
    obtain ⟨_, -, cv', hcv', cb, hcb, rfl⟩ := hc'
    simp only [clResolves, ConLeche.Expr.looseBVarsBounded, Bool.and_eq_true] at hr' hb'
    exact SemCases.srcEval_sound_zeta (CLOk.gradedU hok') (SemCases.zeta_hpt hok.2 hok'.2)
      (ihv ⟨cv, hcv, hr.1.2⟩) (ihb (Resolve.inst hcb hr'.2 hcv' hb'.1.2 hr'.1.2))
  | delta hu hm _ ih =>
    intro hres
    obtain ⟨dv, hdv, rfl, rfl⟩ := Lookup.unfold?_spec hu
    have hdvP := Lookup.findDecl_sub hsub hdv
    obtain ⟨cv, value, hcv, hval, hfind⟩ :=
      hacc.find?_defn hdvP (hacc.defn_safe hdvP (Resolve.const hres))
    obtain ⟨ty, -, rfl⟩ := cvOf?_eq_some hcv
    obtain ⟨-, -, hvr, hvb⟩ := ((ConLecheAccepts.accepted.{0} hacc).wf.consts _
      (List.mem_of_find?_eq_some hfind)).2.2.2.2.1 _ _ _ rfl
    obtain ⟨hread, hη⟩ := markOf_read hd ((MarkRead.decl_clean hd hdv).2 _ rfl) hm
    refine SemCases.srcEval_sound_delta ⟨_, value, _, hfind, rfl, hval, hvb⟩ hread hη (ih ?_)
    obtain ⟨cc, hcc, -⟩ := hres
    simp only [unmark, toCL?, Option.map_eq_map, Option.map_eq_some_iff] at hcc
    obtain ⟨us', hus, -⟩ := hcc
    refine ⟨value.instantiateLevelParams (dv.levelParams.map Name.toCL) us', ?_, ?_⟩
    · rw [unmark_instLevels, toCL?_instLevels _ hus, hread, hval]; rfl
    · rw [Resolve.clResolves_instLP]; exact clResolves_of_constsResolve hvr
  | constAtom _ | atom _ | etaLam | frozen _ | lit _ => exact fun _ => SemCases.srcEval_sound_value _
  | ctor _ _ hlen _ hok ih =>
    intro hres
    exact SemCases.srcEval_sound_ctor hlen (CLOk.gradedU hok) fun i a v ha hv =>
      ih i a v ha hv ((Resolve.appN.mp hres).2 a (mem? ha))
  | casesIota hc hlen hm _ hcv hok hnc halt _ ihm ihb =>
    intro hres
    obtain ⟨C, usC, cv, ps, hC, hCT, rfl, hps, hfs, rfl⟩ := hcv
    have ras := (Resolve.appN.mp hres).2
    have hat := hacc.casesIotaAt hcl (Lookup.casesOnOf?_sub hsub hc) (hsafe hres)
      (Lookup.findDecl_sub hsub hC) hCT (getAppFn_mkAppN_const _ _ _) hnc
    rw [← hlen, ← hps, ← hfs] at hat
    refine SemCases.srcEval_sound_casesIota hat hm halt rfl (CLOk.gradedU hok) (ihm (ras _ (mem? hm)))
      (ihb (Resolve.appN.mpr ⟨ras _ (mem? halt), fun f hf => ?_⟩))
    have rmv := (Resolve.appN.mp (Resolve.of_ok hok)).2 _
      (List.mem_set (List.getElem?_eq_some_iff.mp hm).1 _)
    exact (Resolve.appN.mp rmv).2 f (List.mem_append_right _ hf)
  | casesLitZero hc hNat hlen hm _ hok hnc halt _ ihm ihb =>
    intro hres
    have ras := (Resolve.appN.mp hres).2
    have hivP := Decls.casesOnOf?_ind (Lookup.casesOnOf?_sub hsub hc)
    rw [hNat] at hivP
    obtain ⟨⟨z, hz, hzT, hz0, hzp, hzf⟩, -⟩ := hacc.natCtors hivP
    have hat := hacc.casesIotaAt hcl (Lookup.casesOnOf?_sub hsub hc) (hsafe hres) hz
      (hzT.trans hNat.symm) rfl hnc
    rw [← hlen, hz0, hzp, hzf] at hat
    exact SemCases.srcEval_sound_casesLitZero hat hm halt (CLOk.gradedU hok)
      (ihm (ras _ (mem? hm))) (ihb (ras _ (mem? halt)))
  | casesLitSucc hc hNat hlen hm _ hok hnc halt _ ihm ihb =>
    intro hres
    have ras := (Resolve.appN.mp hres).2
    have hivP := Decls.casesOnOf?_ind (Lookup.casesOnOf?_sub hsub hc)
    rw [hNat] at hivP
    obtain ⟨-, s, hs, hsT, hs1, hsp, hsf⟩ := hacc.natCtors hivP
    have hat := hacc.casesIotaAt hcl (Lookup.casesOnOf?_sub hsub hc) (hsafe hres) hs
      (hsT.trans hNat.symm) rfl hnc
    rw [← hlen, hs1, hsp, hsf] at hat
    refine SemCases.srcEval_sound_casesLitSucc hat hm halt (CLOk.gradedU hok)
      (ihm (ras _ (mem? hm))) (ihb (Resolve.app.mpr ⟨ras _ (mem? halt), ?_⟩))
    obtain ⟨_, hl, hr⟩ := (Resolve.appN.mp (Resolve.of_ok hok)).2 _
      (List.mem_set (List.getElem?_eq_some_iff.mp hm).1 _)
    simp only [unmark, toCL?, Option.some.injEq] at hl
    subst hl
    exact ⟨_, rfl, by simpa [clResolves] using hr⟩
  | casesFrozen hc hlen hcn hC hm hpf hz hpos halt _ ihb =>
    intro hres
    have ras := (Resolve.appN.mp hres).2
    have hcP := Lookup.casesOnOf?_sub hsub hc
    have hat := hacc.casesFrozenAt hcP (hsafe hres) hcn (Lookup.findDecl_sub hsub hC) hz
      fun h => (hpos h).1
    rw [← hlen] at hat
    refine SemCases.srcEval_sound_casesFrozen hat hm halt hpf (fun h => (hpos h).2)
      (ihb (Resolve.appN.mpr ⟨ras _ (mem? halt), fun x hx => ?_⟩))
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
    exact Resolve.erase.mpr (Resolve.proj.mpr ⟨hacc.ind_stored (Decls.casesOnOf?_ind hcP),
      Resolve.reduced.mp (ras _ (mem? hm))⟩)
  | quotMk _ _ _ hok ih =>
    intro hres
    exact SemCases.srcEval_sound_quotMk (CLOk.gradedU hok) (ih ((Resolve.appN.mp hres).2 _ (by simp)))
  | quotLift hc hk _ _ hc' hk' hok hcase _ ihf ihq ihb =>
    intro hres
    have ras := (Resolve.appN.mp hres).2
    obtain ⟨cvL, -, hpinL, hfL⟩ := hacc.find?_quot (Lookup.findDecl_sub hsub hc)
    obtain ⟨cvM, -, -, hfM⟩ := hacc.find?_quot (Lookup.findDecl_sub hsub hc')
    rw [hk] at hpinL hfL
    rw [hk'] at hfM
    obtain ⟨cr, hcr, hbr, hrr⟩ := Resolve.typed_read hok.1
    rw [mkAppN_toArray] at hcr
    obtain ⟨-, has⟩ := Resolve.read_spine hcr hbr hrr
    obtain ⟨cl, hcl', -, hrl⟩ := has _ (List.mem_of_getElem? (i := 3) rfl)
    obtain ⟨cq, hcq, hbq, hrq⟩ := has _ (List.mem_of_getElem? (i := 5) rfl)
    rw [mkAppN_toArray] at hcq
    obtain ⟨ca, hca, hba, hra⟩ := (Resolve.read_spine hcq hbq hrq).2 _
      (List.mem_of_getElem? (i := 2) rfl)
    exact SemCases.srcEval_sound_quotLift ⟨cvL, cvM, hfL, hpinL, hfM⟩ (quotCase hcase)
      (CLOk.gradedU hok) (ihf (ras _ (List.mem_of_getElem? (i := 3) rfl)))
      (ihq (ras _ (List.mem_of_getElem? (i := 5) rfl)))
      (ihb (Resolve.lamInst hcl' hrl hca hba hra))
  | recIota hr hall hcT hblk hidx hshape hbind hps hms hmins hlen _ _ hcv hmi hmk hok hnc hrfs hihl _
      hok' _ ihmin ihmaj ihih ihb =>
    intro hres
    subst hcT
    obtain ⟨C, usC, cv, ps', hC, hCT, hcidx, hps', hfs, hmv⟩ := hcv
    have hat := hacc.recIotaAt hcl (Lookup.findDecl_sub hsub hr) hall
      (Lookup.recBlockOf?_sub hsub hblk) hidx hshape hbind (Lookup.findDecl_sub hsub hC) hCT
      (by rw [hcidx]; exact hmi) (by rw [hmv]; exact getAppFn_mkAppN_const _ _ _) hnc
    rw [← hps, ← hms, ← hmins, hlen, hcidx, ← hps', ← hfs] at hat
    obtain ⟨rh, ras⟩ := Resolve.appN.mp hres
    have rok := (Resolve.appN.mp (Resolve.of_ok hok)).2
    have rfs := (Resolve.appN.mp (hmv ▸ Resolve.natLitCtor (rok _ (by simp)))).2
    refine SemCases.srcEval_sound_recIota hat hlen hmk hmv (by rw [List.mapM_map]; exact hrfs) hihl
      (CLOk.gradedU hok) (CLOk.gradedU hok')
      (fun i m mv hm hmv' => ihmin i m mv hm hmv' (ras _ (by simp [mem? hm])))
      (ihmaj (ras _ (by simp))) (fun i f w hf hw => ihih i f w hf hw ?_) (ihb (Resolve.of_ok hok'))
    obtain ⟨x, -, hx⟩ := Decls.mem_mapM hrfs f (mem? hf)
    refine Resolve.appN.mpr ⟨rh, fun a ha => ?_⟩
    simp only [List.mem_append, List.mem_singleton] at ha
    rcases ha with ((ha | ha) | ha) | rfl
    · exact ras a (by simp [ha])
    · exact ras a (by simp [ha])
    · exact rok a (by simp [ha])
    · exact rfs _ (List.mem_append_right _ (mem? hx))
  | proj _ hcv ha hok ih =>
    intro hres
    obtain ⟨C, usC, cv, ps, hC, hCT, hc0, hps, hfs, rfl⟩ := hcv
    obtain ⟨entry, hfp⟩ := findProj_of_typed hok.1
    have hat := hacc.projAt hcl (Lookup.findDecl_sub hsub hC) hCT hc0 hfp
    rw [← hps, ← hfs] at hat
    exact SemCases.srcEval_sound_proj hat rfl ha (ih (Resolve.proj.mp hres).2)
  | projFrozen _ _ _ ih =>
    intro hres
    exact SemCases.srcEval_sound_projFrozen (ih (Resolve.proj.mp hres).2)
  | appCong _ _ _ _ hok ihf iha =>
    intro hres
    obtain ⟨rf, ra⟩ := Resolve.app.mp hres
    exact SemCases.srcEval_sound_appCong (CLOk.gradedU hok) (ihf rf) (iha ra)
  | frozenApp _ _ _ he ht ihf iha =>
    intro hres
    obtain ⟨rf, ra⟩ := Resolve.app.mp hres
    obtain ⟨c, F, T, hc, hi, -⟩ := he
    exact SemCases.srcEval_sound_frozenApp (CLOk.gradedU ⟨⟨c, F, T, hc, hi⟩, ht⟩) (ihf rf) (iha ra)

/-- **The marked source evaluation preserves meaning** (`srcEval_sound_statement`): the marked
input reads as `e` with its `eta` marks on λs (`markOf_read`) and is resolved, since con-leche
types `e` (`Resolve.typed_read`); the induction `semSim_of_srcEval` gives the invariant, and
`Sound.of_semSim` its meaning. Reference: subject reduction (`MR P/PCUICSR.v`) replaced by
con-leche's model; MC §7.3; DV-33, DV-34. -/
theorem srcEval_sound : srcEval_sound_statement.{w} := by
  intro P decls env view cfg e ê v hacc hsub hty hclean hd hmark hev
  obtain ⟨hread, hη⟩ := markOf_read hd hclean hmark
  obtain ⟨c, hc, -, hr⟩ := Resolve.typed_read hty
  exact Sound.of_semSim hty hread hη (semSim_of_srcEval hacc hsub hd hev ⟨c, hread.trans hc, hr⟩)

end EraseProof
