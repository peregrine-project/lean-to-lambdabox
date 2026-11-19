import EraseProof.Relation.Basic

/-!
# The pure oracle under a renaming of free variables

`renFV ρ` renames every free variable `x` to `ρ x`. Over declarations without free variables
(`ClosedDecls`), the parts of the pure oracle (`Erasure.Pure.whnf`, `instForalls`, `instProjs`,
`inferType`, `isArity`, `typeLevel`, `isErasable`) commute with a renaming: on a term whose free
variables lie in a set `S` closed under the locals' types and values (`LocalsSupport`), a run over
locals that are the renamed locals on `S` (`LocalsRen`) gives the renamed result, and every result
has its free variables in `S`. With `ρ` the identity this is the frame lemma of
`ML-V Oracle/Agree.lean` (two lists of locals that agree on `S`), whose proofs these follow; the
renaming needs no injectivity, since the oracle reads a free variable only through its local.
-/

open Lean Erasure

namespace EraseProof

/-- Rename every free variable `x` to `ρ x`. Reference: none. -/
def renFV (ρ : FVarId → FVarId) : Expr → Expr
  | .fvar x => .fvar (ρ x)
  | .app f a => .app (renFV ρ f) (renFV ρ a)
  | .lam n t b bi => .lam n (renFV ρ t) (renFV ρ b) bi
  | .forallE n t b bi => .forallE n (renFV ρ t) (renFV ρ b) bi
  | .letE n t v b nd => .letE n (renFV ρ t) (renFV ρ v) (renFV ρ b) nd
  | .mdata m e => .mdata m (renFV ρ e)
  | .proj s i e => .proj s i (renFV ρ e)
  | e@(.bvar _) | e@(.sort _) | e@(.const ..) | e@(.lit _) | e@(.mvar _) => e

/-- A local renamed: its variable, its type and its value. Reference: none. -/
def renLocal (ρ : FVarId → FVarId) (l : Local) : Local :=
  ⟨ρ l.fvarId, l.userName, renFV ρ l.type, l.value?.map (renFV ρ)⟩

/-- `S` is closed under the locals: the type and the value of the local of a variable of `S` have
their free variables in `S`. Port of `ML-V Oracle/Agree.lean:28`. -/
def LocalsSupport (S : FVarId → Prop) (ls : List Local) : Prop :=
  ∀ x, S x → ∀ l, Pure.findLocal ls x = some l →
    FVarsIn S l.type ∧ ∀ v, l.value? = some v → FVarsIn S v

/-- On `S`, the locals `ls₂` are the locals `ls₁` renamed by `ρ`. Adapted from
`ML-V Oracle/Agree.lean:33 LocalsAgree` (the case `ρ = id`). -/
def LocalsRen (ρ : FVarId → FVarId) (S : FVarId → Prop) (ls₁ ls₂ : List Local) : Prop :=
  ∀ x, S x → Pure.findLocal ls₂ (ρ x) = (Pure.findLocal ls₁ x).map (renLocal ρ)

namespace OracleRen

/-! ## Free variables (port of `ML-V Oracle/Agree.lean:37-95`) -/

theorem fvarsIn_mono {p q : FVarId → Prop} (hpq : ∀ x, p x → q x) :
    ∀ {e : Expr}, FVarsIn p e → FVarsIn q e
  | .fvar x, h => hpq x h
  | .app f a, h => ⟨fvarsIn_mono hpq (e := f) h.1, fvarsIn_mono hpq (e := a) h.2⟩
  | .lam _ t b _, h | .forallE _ t b _, h =>
    ⟨fvarsIn_mono hpq (e := t) h.1, fvarsIn_mono hpq (e := b) h.2⟩
  | .letE _ t v b _, h =>
    ⟨fvarsIn_mono hpq (e := t) h.1, fvarsIn_mono hpq (e := v) h.2.1, fvarsIn_mono hpq (e := b) h.2.2⟩
  | .mdata _ e, h | .proj _ _ e, h => fvarsIn_mono hpq (e := e) h
  | .bvar _, _ | .sort _, _ | .const .., _ | .lit _, _ | .mvar _, _ => trivial

theorem fvarsIn_false {p : FVarId → Prop} {e : Expr} (h : FVarsIn (fun _ => False) e) : FVarsIn p e :=
  fvarsIn_mono (fun _ h => h.elim) h

theorem fvarsIn_of_hasFVar {p : FVarId → Prop} : ∀ {e : Expr}, HasFVar e = false → FVarsIn p e
  | .fvar _, h => nomatch h
  | .app f a, h => by
    simp only [HasFVar, Bool.or_eq_false_iff] at h
    exact ⟨fvarsIn_of_hasFVar h.1, fvarsIn_of_hasFVar h.2⟩
  | .lam _ t b _, h | .forallE _ t b _, h => by
    simp only [HasFVar, Bool.or_eq_false_iff] at h
    exact ⟨fvarsIn_of_hasFVar h.1, fvarsIn_of_hasFVar h.2⟩
  | .letE _ t v b _, h => by
    simp only [HasFVar, Bool.or_eq_false_iff] at h
    exact ⟨fvarsIn_of_hasFVar h.1.1, fvarsIn_of_hasFVar h.1.2, fvarsIn_of_hasFVar h.2⟩
  | .mdata _ e, h | .proj _ _ e, h => fvarsIn_of_hasFVar (e := e) h
  | .bvar _, _ | .sort _, _ | .const .., _ | .lit _, _ | .mvar _, _ => trivial

theorem fvarsIn_instLevels {p : FVarId → Prop} (ps : List Name) (us : List Level) :
    ∀ {e : Expr}, FVarsIn p e → FVarsIn p (Pure.instLevels ps us e)
  | .app f a, h => ⟨fvarsIn_instLevels ps us (e := f) h.1, fvarsIn_instLevels ps us (e := a) h.2⟩
  | .lam _ t b _, h | .forallE _ t b _, h =>
    ⟨fvarsIn_instLevels ps us (e := t) h.1, fvarsIn_instLevels ps us (e := b) h.2⟩
  | .letE _ t v b _, h => ⟨fvarsIn_instLevels ps us (e := t) h.1,
    fvarsIn_instLevels ps us (e := v) h.2.1, fvarsIn_instLevels ps us (e := b) h.2.2⟩
  | .mdata _ e, h | .proj _ _ e, h => fvarsIn_instLevels ps us (e := e) h
  | .fvar _, h => h
  | .bvar _, _ | .sort _, _ | .const .., _ | .lit _, _ | .mvar _, _ => trivial

theorem fvarsIn_lift {p : FVarId → Prop} : ∀ {e : Expr} {s d : Nat}, FVarsIn p e →
    FVarsIn p (e.liftLooseBVars' s d) := by
  intro e
  induction e <;> intro s d h <;> simp_all [Expr.liftLooseBVars', FVarsIn]

theorem fvarsIn_inst {p : FVarId → Prop} {a : Expr} (ha : FVarsIn p a) :
    ∀ {b : Expr} {d : Nat}, FVarsIn p b → FVarsIn p (b.instantiate1' a d) := by
  intro b
  induction b with
  | bvar i =>
    intro d _
    simp only [Expr.instantiate1']
    split
    · trivial
    · split
      · exact fvarsIn_lift ha
      · trivial
  | _ => intro d h; simp_all [Expr.instantiate1', FVarsIn]

theorem fvarsIn_foldl {p : FVarId → Prop} : ∀ {as : List Expr} {f : Expr},
    FVarsIn p (as.foldl .app f) ↔ FVarsIn p f ∧ ∀ a ∈ as, FVarsIn p a
  | [], f => by simp
  | a :: as, f => by
    rw [List.foldl_cons, fvarsIn_foldl]
    simp only [FVarsIn, List.mem_cons, forall_eq_or_imp, and_assoc]

/-- The arguments of `spine` have their free variables where the term has. Port of
`ML-V Oracle/Agree.lean:86`. -/
theorem spine_snd {p : FVarId → Prop} : ∀ {e : Expr}, FVarsIn p e → ∀ a ∈ (spine e).2, FVarsIn p a
  | .app f x, h => by
    simp only [spine, List.mem_append, List.mem_singleton]
    rintro a (ha | rfl)
    · exact spine_snd h.1 a ha
    · exact h.2
  | .bvar _, _ | .fvar _, _ | .mvar _, _ | .sort _, _ | .const .., _ | .lam .., _ | .forallE .., _
  | .letE .., _ | .lit _, _ | .mdata .., _ | .proj .., _ => by simp [spine]

/-- The type and the value of a declaration of a closed closure have no free variable. -/
theorem closed_find {decls : List ConstantInfo} {c : Name} {ci : ConstantInfo}
    (hcl : ClosedDecls decls = true) (h : findConst decls c = some ci) :
    FVarsIn (fun _ => False) ci.type ∧ ∀ v, ci.value? true = some v → FVarsIn (fun _ => False) v := by
  have hm := List.mem_of_find?_eq_some h
  have := List.all_eq_true.mp hcl ci hm
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
  refine ⟨fvarsIn_of_hasFVar this.1, fun v hv => ?_⟩
  rw [hv] at this
  simpa [Option.all] using fvarsIn_of_hasFVar (p := fun _ => False) (by simpa [Option.all] using this.2)

/-! ## Renaming -/

theorem renFV_lift (ρ : FVarId → FVarId) : ∀ (e : Expr) (s d : Nat),
    renFV ρ (e.liftLooseBVars' s d) = (renFV ρ e).liftLooseBVars' s d := by
  intro e
  induction e <;> intro s d <;> simp_all [Expr.liftLooseBVars', renFV]

theorem renFV_inst (ρ : FVarId → FVarId) (a : Expr) : ∀ (b : Expr) (d : Nat),
    renFV ρ (b.instantiate1' a d) = (renFV ρ b).instantiate1' (renFV ρ a) d := by
  intro b
  induction b with
  | bvar i =>
    intro d
    simp only [Expr.instantiate1', renFV]
    by_cases h1 : i < d
    · simp [h1, renFV]
    · by_cases h2 : i = d
      · simp [h2, renFV_lift]
      · simp [h1, h2, renFV]
  | _ => intro d; simp_all [Expr.instantiate1', renFV]

theorem renFV_closed (ρ : FVarId → FVarId) : ∀ {e : Expr}, FVarsIn (fun _ => False) e → renFV ρ e = e
  | .fvar _, h => h.elim
  | .app f a, h => by rw [renFV, renFV_closed ρ h.1, renFV_closed ρ h.2]
  | .lam _ t b _, h => by rw [renFV, renFV_closed ρ h.1, renFV_closed ρ h.2]
  | .forallE _ t b _, h => by rw [renFV, renFV_closed ρ h.1, renFV_closed ρ h.2]
  | .letE _ t v b _, h => by rw [renFV, renFV_closed ρ h.1, renFV_closed ρ h.2.1, renFV_closed ρ h.2.2]
  | .mdata _ e, h => by rw [renFV, renFV_closed ρ (e := e) h]
  | .proj _ _ e, h => by rw [renFV, renFV_closed ρ (e := e) h]
  | .bvar _, _ | .sort _, _ | .const .., _ | .lit _, _ | .mvar _, _ => rfl

theorem renFV_foldl (ρ : FVarId → FVarId) : ∀ (as : List Expr) (f : Expr),
    renFV ρ (as.foldl .app f) = (as.map (renFV ρ)).foldl .app (renFV ρ f)
  | [], _ => rfl
  | a :: as, f => by simp only [List.foldl_cons, List.map_cons, renFV_foldl ρ as]; rfl

theorem renFV_mkAppN (ρ : FVarId → FVarId) (f : Expr) (as : List Expr) :
    renFV ρ (mkAppN f as.toArray) = mkAppN (renFV ρ f) (as.map (renFV ρ)).toArray := by
  rw [mkAppN_toArray, mkAppN_toArray, renFV_foldl]

theorem spine_ren (ρ : FVarId → FVarId) : ∀ e : Expr,
    spine (renFV ρ e) = (renFV ρ (spine e).1, (spine e).2.map (renFV ρ))
  | .app f a => by
    simp only [renFV, spine]
    rw [spine_ren ρ f]
    simp
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const .. | .lam .. | .forallE .. | .letE .. | .lit _
  | .mdata .. | .proj .. => rfl

theorem renFV_eq_lam {ρ : FVarId → FVarId} {e t b : Expr} {n : Name} {bi : BinderInfo}
    (h : renFV ρ e = .lam n t b bi) : ∃ t' b', e = .lam n t' b' bi := by
  cases e <;> simp [renFV] at h
  exact ⟨_, _, by rw [h.1, h.2.2.2]⟩

/-- `mapM` in `Option` of a mapped function. Copy of `ML-V Oracle/Whnf.lean:134`. -/
theorem list_mapM_map {α β γ : Type} (g : α → Option β) (k : β → γ) :
    ∀ (l : List α), (l.mapM fun x => (g x).map k) = (l.mapM g).map (List.map k)
  | [] => rfl
  | x :: l => by
    simp only [List.mapM_cons, list_mapM_map g k l]
    cases g x <;> cases l.mapM g <;> rfl

theorem iotaApp?_ren (ρ : FVarId → FVarId) (decls : List ConstantInfo) (e : Expr) :
    Pure.iotaApp? decls (renFV ρ e) =
      (Pure.iotaApp? decls e).map fun p => (p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.map (renFV ρ)) := by
  unfold Pure.iotaApp?
  rw [spine_ren]
  obtain ⟨hd, args⟩ := spine e
  cases hd <;> try rfl
  rename_i r us
  simp only [renFV]
  cases findConst decls r with
  | none => rfl
  | some ci =>
    cases ci <;> try rfl
    rename_i rv
    simp only
    cases Pure.iotaMinors? decls rv with
    | none => rfl
    | some minors => simp [guard, List.length_map]; split <;> rfl

theorem ihs_ren (ρ : FVarId → FVarId) (r : Name) (us : List Level) (pre fs : List Expr) :
    ∀ l : List RecIH,
    (l.mapM fun h => (fs.map (renFV ρ))[h.field]?.map fun f =>
      mkAppN (.const r us) (pre.map (renFV ρ) ++ [f]).toArray) =
    (l.mapM fun h => fs[h.field]?.map fun f => mkAppN (.const r us) (pre ++ [f]).toArray).map
      (List.map (renFV ρ))
  | [] => rfl
  | h :: l => by
    rw [List.mapM_cons, List.mapM_cons, ihs_ren ρ r us pre fs l, List.getElem?_map]
    cases fs[h.field]? with
    | none => rfl
    | some f =>
      cases List.mapM (fun h => fs[h.field]?.map fun f => mkAppN (.const r us) (pre ++ [f]).toArray) l with
      | none => rfl
      | some m => simp [renFV_mkAppN, renFV]

theorem iotaRhs?_ren (ρ : FVarId → FVarId) (decls : List ConstantInfo) (r : Name) (us : List Level)
    (rv : RecursorVal) (minors : List RecMinor) (args : List Expr) (t : Expr) :
    Pure.iotaRhs? decls r us rv minors (args.map (renFV ρ)) (renFV ρ t) =
      (Pure.iotaRhs? decls r us rv minors args t).map (renFV ρ) := by
  unfold Pure.iotaRhs?
  rw [spine_ren]
  obtain ⟨hd, cargs⟩ := spine t
  cases hd <;> try rfl
  rename_i c uc
  simp only [renFV]
  cases findConst decls c with
  | none => rfl
  | some ci =>
    cases ci <;> try rfl
    rename_i cv
    simp only [List.length_map]
    by_cases g : (rv.all == [cv.induct] && cargs.length == cv.numParams + cv.numFields) = true
    · simp only [g, guard, ite_true, Option.pure_def, Option.bind_eq_bind, Option.bind_some]
      cases minors[cv.cidx]? with
      | none => rfl
      | some mi =>
        simp only [Option.bind_some, ← List.map_take, ← List.map_drop]
        rw [ihs_ren]
        simp only [List.getElem?_map]
        cases ((args.take (rv.numParams + rv.numMotives + rv.numMinors)).drop
          (rv.numParams + rv.numMotives))[cv.cidx]? with
        | none => rfl
        | some mk =>
          simp only [Option.map_some, Option.bind_some]
          cases List.mapM (fun h => (cargs.drop cv.numParams)[h.field]?.map fun f => mkAppN (.const r us)
                (args.take (rv.numParams + rv.numMotives + rv.numMinors) ++ [f]).toArray) mi.ihs with
          | none => rfl
          | some ihs => simp [renFV_mkAppN]
    · simp only [Bool.not_eq_true] at g
      simp [g, guard, failure]

/-! ## `Except` -/

theorem throw_ne_ok {α : Type} {e : EraseError} {a : α} :
    (throw e : Except EraseError α) ≠ .ok a := by
  simp [throw, throwThe, MonadExceptOf.throw]

/-- A bind of related runs whose continuations are related on the results is related. Adapted from
`ML-V Oracle/Agree.lean:143 bind_agree`. -/
theorem bind_ren {ε α α' β β' : Type} {x₁ : Except ε α} {x₂ : Except ε α'} {g : α → α'} {h : β → β'}
    {k₁ : α → Except ε β} {k₂ : α' → Except ε β'} (P : α → Prop) (Q : β → Prop)
    (hx : x₂ = x₁.map g ∧ ∀ a, x₁ = .ok a → P a)
    (hk : ∀ a, P a → k₂ (g a) = (k₁ a).map h ∧ ∀ b, k₁ a = .ok b → Q b) :
    (x₂ >>= k₂) = (x₁ >>= k₁).map h ∧ ∀ b, (x₁ >>= k₁) = .ok b → Q b := by
  obtain ⟨rfl, hP⟩ := hx
  rcases x₁ with e | a
  · exact ⟨rfl, fun b h => nomatch h⟩
  · exact hk a (hP a rfl)

/-- `bind_ren` for continuations with equal results. -/
theorem bind_ren_eq {ε α α' β : Type} {x₁ : Except ε α} {x₂ : Except ε α'} {g : α → α'}
    {k₁ : α → Except ε β} {k₂ : α' → Except ε β} (P : α → Prop)
    (hx : x₂ = x₁.map g ∧ ∀ a, x₁ = .ok a → P a) (hk : ∀ a, P a → k₂ (g a) = k₁ a) :
    (x₂ >>= k₂) = (x₁ >>= k₁) := by
  obtain ⟨rfl, hP⟩ := hx
  rcases x₁ with e | a
  · rfl
  · exact hk a (hP a rfl)

theorem bind_congr_ok {ε α β : Type} {x y : Except ε α} {k₁ k₂ : α → Except ε β} (hxy : x = y)
    (hk : ∀ a, y = .ok a → k₁ a = k₂ a) : (x >>= k₁) = (y >>= k₂) := by
  subst hxy
  match x, hk with
  | .error _, _ => rfl
  | .ok a, hk => exact hk a rfl

/-! ## What the ι-rule reads (port of `ML-V Oracle/Whnf.lean:142-195`) -/

theorem iotaRhs?_spec {decls : List ConstantInfo} {r : Name} {us : List Level} {rv : RecursorVal}
    {minors : List RecMinor} {args : List Expr} {t e : Expr}
    (h : Pure.iotaRhs? decls r us rv minors args t = some e) :
    ∃ C uC cargs cv mi mk rfs, spine t = (.const C uC, cargs) ∧
      findConst decls C = some (.ctorInfo cv) ∧
      minors[cv.cidx]? = some mi ∧
      ((args.take (rv.numParams + rv.numMotives + rv.numMinors)).drop
        (rv.numParams + rv.numMotives))[cv.cidx]? = some mk ∧
      (mi.ihs.mapM fun h => (cargs.drop cv.numParams)[h.field]?) = some rfs ∧
      e = mkAppN mk (cargs.drop cv.numParams ++ rfs.map fun f => mkAppN (.const r us)
        (args.take (rv.numParams + rv.numMotives + rv.numMinors) ++ [f]).toArray).toArray := by
  unfold Pure.iotaRhs? at h
  split at h
  · rename_i C uC cargs hsp
    split at h
    · rename_i cv hC
      by_cases g1 : (rv.all == [cv.induct] && cargs.length == cv.numParams + cv.numFields) = true
      · simp only [g1, guard, ite_true, pure, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨_, -, mi, hmi, mk, hmk, ihs, hihs, he⟩ := h
        rw [list_mapM_map] at hihs
        obtain ⟨rfs, hrfs, rfl⟩ := Option.map_eq_some_iff.mp hihs
        exact ⟨C, uC, cargs, cv, mi, mk, rfs, hsp, hC, hmi, hmk, hrfs, (Option.some.inj he).symm⟩
      · simp [g1, guard, failure] at h
    · cases h
  · cases h

theorem iotaApp?_spine {decls : List ConstantInfo} {e : Expr} {r : Name} {us : List Level}
    {rv : RecursorVal} {minors : List RecMinor} {args : List Expr}
    (h : Pure.iotaApp? decls e = some (r, us, rv, minors, args)) : spine e = (.const r us, args) := by
  unfold Pure.iotaApp? at h
  split at h
  · rename_i r' us' args' hsp
    split at h
    · rename_i rv' _
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨_, -, h⟩ := h
      by_cases g : (args'.length == rv'.numParams + rv'.numMotives + rv'.numMinors + 1) = true
      · simp only [g, guard, ite_true, pure] at h
        obtain ⟨_, -, h⟩ := h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, -, -, rfl⟩ := h
        exact hsp
      · simp [g, guard, failure] at h
    · cases h
  · cases h

/-- The members of a successful `mapM` are images of members of the list. Port of
`ML-V Oracle/Agree.lean:107`. -/
theorem mem_of_mapM {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM f = some r → ∀ y ∈ r, ∃ x ∈ l, f x = some y
  | [], r, h, y, hy => by simp at h; subst h; cases hy
  | x :: l, r, h, y, hy => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨z, hz, zs, hzs, rfl⟩ := h
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨x, List.mem_cons_self .., hz⟩
    · obtain ⟨x', hx', h'⟩ := mem_of_mapM hzs y hy
      exact ⟨x', List.mem_cons_of_mem _ hx', h'⟩

/-- The term that the ι-rule of `Erasure.Pure.whnf` builds has its free variables where the
application and the major premise's normal form have them. Port of `ML-V Oracle/Agree.lean:122`. -/
theorem iotaRhs_fvarsIn {S : FVarId → Prop} {decls : List ConstantInfo} {X wa e : Expr} {r : Name}
    {us : List Level} {rv : RecursorVal} {minors : List RecMinor} {args : List Expr}
    (hsp : spine X = (.const r us, args)) (hX : FVarsIn S X) (hwa : FVarsIn S wa)
    (he : Pure.iotaRhs? decls r us rv minors args wa = some e) : FVarsIn S e := by
  obtain ⟨C, uC, cargs, cv, mi, mk, rfs, hspw, -, -, hmk, hrfs, rfl⟩ := iotaRhs?_spec he
  have hargs : ∀ a ∈ args, FVarsIn S a := by
    have := spine_snd hX; rw [hsp] at this; exact this
  have hcargs : ∀ a ∈ cargs, FVarsIn S a := by
    have := spine_snd hwa; rw [hspw] at this; exact this
  have hfs : ∀ a ∈ cargs.drop cv.numParams, FVarsIn S a :=
    fun a ha => hcargs a (List.mem_of_mem_drop ha)
  rw [mkAppN_toArray, fvarsIn_foldl]
  refine ⟨hargs mk (List.mem_of_mem_take (List.mem_of_mem_drop (List.mem_of_getElem? hmk))),
    fun a ha => ?_⟩
  rcases List.mem_append.mp ha with ha | ha
  · exact hfs a ha
  · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp ha
    rw [mkAppN_toArray, fvarsIn_foldl]
    refine ⟨trivial, fun b hb => ?_⟩
    rcases List.mem_append.mp hb with hb | hb
    · exact hargs b (List.mem_of_mem_take hb)
    · rw [List.mem_singleton] at hb
      rw [hb]
      obtain ⟨h, -, hh⟩ := mem_of_mapM hrfs f hf
      exact hfs _ (List.mem_of_getElem? hh)

theorem renFV_id : ∀ e : Expr, renFV id e = e := by
  intro e; induction e <;> simp_all [renFV]

/-- The identity renames the locals into themselves, on every set. -/
theorem localsRen_id {S : FVarId → Prop} {ls : List Local} : LocalsRen id S ls ls := by
  intro x _
  have : renLocal id = id := funext fun l => by
    simp only [renLocal, funext renFV_id, Option.map_id']; rfl
  rw [this, Option.map_id]; rfl

theorem fvarsIn_mkAppN {p : FVarId → Prop} {f : Expr} {as : List Expr} :
    FVarsIn p (mkAppN f as.toArray) ↔ FVarsIn p f ∧ ∀ a ∈ as, FVarsIn p a := by
  rw [mkAppN_toArray, fvarsIn_foldl]

/-- Abstracting `x` removes it from the free variables. -/
theorem fvarsIn_absFV {p : FVarId → Prop} {x : FVarId} : ∀ {e : Expr} {d : Nat},
    FVarsIn (fun y => p y ∨ y = x) e → FVarsIn p (absFV x d e) := by
  intro e
  induction e with
  | fvar y =>
    intro d h
    simp only [absFV]
    split
    · trivial
    · rename_i hy
      exact h.resolve_right fun h' => hy ((fvarId_beq_iff _ _).2 h')
  | _ => intro d h; simp_all [absFV, FVarsIn]

/-- A local whose type and value are in `S'` added to locals supported by `S`, for `S ⊆ S' ⊆ S ∪ {x}`. -/
theorem localsSupport_cons {S S' : FVarId → Prop} {ls : List Local} {x : FVarId} {n : Name}
    {T : Expr} {val : Option Expr} (hS : LocalsSupport S ls) (hT : FVarsIn S' T)
    (hv : ∀ v, val = some v → FVarsIn S' v) (h1 : ∀ y, S y → S' y) (h2 : ∀ y, S' y → y = x ∨ S y) :
    LocalsSupport S' (⟨x, n, T, val⟩ :: ls) := by
  intro y hy l hl
  simp only [Pure.findLocal, List.find?_cons] at hl
  split at hl
  · cases hl; exact ⟨hT, hv⟩
  · rename_i hne
    rcases h2 y hy with rfl | hy'
    · rw [(fvarId_beq_iff _ _).2 rfl] at hne; cases hne
    · have := hS y hy' l hl
      exact ⟨fvarsIn_mono h1 this.1, fun v hv' => fvarsIn_mono h1 (this.2 v hv')⟩

/-- Opening a binder with `x` puts `x` among the free variables. -/
theorem fvarsIn_open {p : FVarId → Prop} {x : FVarId} {b : Expr} (hb : FVarsIn p b) :
    FVarsIn (fun y => p y ∨ y = x) (b.instantiate1' (.fvar x)) :=
  fvarsIn_inst (p := fun y => p y ∨ y = x) (a := .fvar x) (Or.inr rfl)
    (fvarsIn_mono (fun _ => .inl) hb)

/-- A local `x` of a type in `S` added to locals supported by `S`: supported by `S ∪ {x}`. -/
theorem localsSupport_open {S : FVarId → Prop} {ls : List Local} {x : FVarId} {n : Name}
    {T : Expr} {val : Option Expr} (hS : LocalsSupport S ls) (hT : FVarsIn S T)
    (hv : ∀ v, val = some v → FVarsIn S v) :
    LocalsSupport (fun y => S y ∨ y = x) (⟨x, n, T, val⟩ :: ls) :=
  localsSupport_cons hS (fvarsIn_mono (fun _ => .inl) hT)
    (fun v h => fvarsIn_mono (fun _ => .inl) (hv v h)) (fun _ => .inl) fun _ h => h.symm

/-! ## The oracle's parts -/

section
variable {S : FVarId → Prop} {ρ : FVarId → FVarId} {cx : Pure.Ctx} {ls₁ ls₂ : List Local}
variable (hcl : ClosedDecls cx.decls = true) (hS : LocalsSupport S ls₁) (hag : LocalsRen ρ S ls₁ ls₂)
include hcl hS hag

/-- `Erasure.Pure.whnf` commutes with the renaming, and its results are in `S`. Adapted from
`ML-V Oracle/Agree.lean:157 whnf_agree`. -/
theorem whnf_ren : ∀ (f : Nat) (e : Expr), FVarsIn S e →
    Pure.whnf cx f ls₂ (renFV ρ e) = (Pure.whnf cx f ls₁ e).map (renFV ρ) ∧
      ∀ w, Pure.whnf cx f ls₁ e = .ok w → FVarsIn S w
  | 0, e, _ => ⟨rfl, fun w h => absurd h throw_ne_ok⟩
  | f + 1, .app g a, ⟨hg, ha⟩ => by
    have ia := whnf_ren f a ha
    simp only [renFV, Pure.whnf]
    refine bind_ren (fun w => FVarsIn S w) _ (whnf_ren f g hg) fun g' hg' => ?_
    split
    · rename_i n t b bi heq
      obtain ⟨t', b', rfl⟩ := renFV_eq_lam heq
      simp only [renFV, Expr.lam.injEq] at heq
      obtain ⟨-, -, rfl, -⟩ := heq
      dsimp only
      rw [← renFV_inst]
      exact whnf_ren f _ (fvarsIn_inst ha hg'.2)
    · rename_i hl₂
      have hl : ∀ n t b bi, g' ≠ .lam n t b bi := fun n t b bi h => by
        subst h; exact hl₂ _ _ _ _ rfl
      rw [show Expr.app (renFV ρ g') (renFV ρ a) = renFV ρ (.app g' a) from rfl, iotaApp?_ren]
      cases hia : Pure.iotaApp? cx.decls (.app g' a) with
      | none =>
        simp only [Option.map_none]
        cases g'
        case lam => exact absurd rfl (hl _ _ _ _)
        all_goals rw [hia]; exact ⟨rfl, fun w h => by cases h; exact ⟨hg', ha⟩⟩
      | some p =>
        obtain ⟨r, us, rv, minors, args⟩ := p
        have hsp := iotaApp?_spine hia
        simp only [Option.map_some]
        cases g'
        case lam => exact absurd rfl (hl _ _ _ _)
        all_goals
          rw [hia]; dsimp only
          refine bind_ren (fun w => FVarsIn S w) _ ia fun wa hwa => ?_
          rw [iotaRhs?_ren]
          cases hre : Pure.iotaRhs? cx.decls r us rv minors args wa with
          | none => exact ⟨rfl, fun w h => by cases h; exact ⟨hg', ha⟩⟩
          | some e => exact whnf_ren f e (iotaRhs_fvarsIn hsp ⟨hg', ha⟩ hwa hre)
  | f + 1, .letE _ _ v b _, ⟨_, hv, hb⟩ => by
    simp only [renFV, Pure.whnf]
    rw [← renFV_inst]
    exact whnf_ren f _ (fvarsIn_inst hv hb)
  | f + 1, .mdata _ e, h => by
    simp only [renFV, Pure.whnf]; exact whnf_ren f e h
  | f + 1, .fvar x, h => by
    have hx : S x := h
    simp only [renFV, Pure.whnf]
    rw [hag x hx]
    cases hl : Pure.findLocal ls₁ x with
    | none => exact ⟨rfl, fun w hw => by cases hw; exact hx⟩
    | some l =>
      obtain ⟨id, nm, ty, val⟩ := l
      cases val with
      | none => exact ⟨rfl, fun w hw => by cases hw; exact hx⟩
      | some v => exact whnf_ren f v ((hS x hx _ hl).2 v rfl)
  | f + 1, .const c us, h => by
    simp only [renFV, Pure.whnf]
    cases hc : findConst cx.decls c with
    | none => exact ⟨rfl, fun w hw => by cases hw; exact h⟩
    | some ci =>
      cases ci with
      | defnInfo v =>
        dsimp only
        split
        · exact ⟨rfl, fun w hw => by cases hw; exact h⟩
        · have hval : FVarsIn (fun _ => False) (Pure.instLevels v.levelParams us v.value) :=
            fvarsIn_instLevels _ _ ((closed_find hcl hc).2 _ rfl)
          have := whnf_ren f _ (fvarsIn_false (p := S) hval)
          rwa [renFV_closed ρ hval] at this
      | _ => exact ⟨rfl, fun w hw => by cases hw; exact h⟩
  | f + 1, .proj S' i s, h => by
    have hs : FVarsIn S s := h
    simp only [renFV, Pure.whnf]
    refine bind_ren (fun w => FVarsIn S w) _ (whnf_ren f s hs) fun ws hws => ?_
    rw [spine_ren]
    have hargs : ∀ a ∈ (spine ws).2, FVarsIn S a := spine_snd hws
    generalize spine ws = p at hargs ⊢
    obtain ⟨hd, args⟩ := p
    cases hd
    case const c u =>
      simp only [renFV]
      cases hc : findConst cx.decls c with
      | none => exact ⟨rfl, fun w hw => by cases hw; exact hs⟩
      | some ci =>
        cases ci with
        | ctorInfo cv =>
          simp only [List.getElem?_map]
          cases ha : args[cv.numParams + i]? with
          | none => exact ⟨rfl, fun w hw => by cases hw; exact hs⟩
          | some a => exact whnf_ren f a (hargs a (List.mem_of_getElem? ha))
        | _ => exact ⟨rfl, fun w hw => by cases hw; exact hs⟩
    all_goals exact ⟨rfl, fun w hw => by cases hw; exact hs⟩
  | f + 1, .bvar _, h | f + 1, .sort _, h | f + 1, .lam .., h | f + 1, .forallE .., h
  | f + 1, .lit _, h | f + 1, .mvar _, h =>
    ⟨rfl, fun w hw => by cases hw; exact h⟩

/-- `Erasure.Pure.instForalls` commutes with the renaming. Adapted from
`ML-V Oracle/Agree.lean:270 instForalls_agree`. -/
theorem instForalls_ren (f : Nat) : ∀ (r : Expr) (as : List Expr), FVarsIn S r →
    (∀ a ∈ as, FVarsIn S a) →
    Pure.instForalls cx f ls₂ (renFV ρ r) (as.map (renFV ρ)) =
        (Pure.instForalls cx f ls₁ r as).map (renFV ρ) ∧
      ∀ w, Pure.instForalls cx f ls₁ r as = .ok w → FVarsIn S w
  | r, [], hr, _ => ⟨rfl, fun w h => by cases h; exact hr⟩
  | r, a :: as, hr, has => by
    have ha := has a (List.mem_cons_self ..)
    have has' : ∀ a ∈ as, FVarsIn S a := fun a h => has a (List.mem_cons_of_mem _ h)
    simp only [List.map_cons, Pure.instForalls]
    refine bind_ren (fun w => FVarsIn S w) _ (whnf_ren hcl hS hag f r hr) fun w hw => ?_
    cases w with
    | forallE n t b bi =>
      simp only [renFV]
      rw [← renFV_inst]
      exact instForalls_ren f _ as (fvarsIn_inst ha hw.2) has'
    | _ => exact ⟨rfl, fun _ h => absurd h throw_ne_ok⟩

/-- `Erasure.Pure.instProjs` commutes with the renaming. Adapted from
`ML-V Oracle/Agree.lean:289 instProjs_agree`. -/
theorem instProjs_ren (f : Nat) (S' : Name) {s : Expr} (hs : FVarsIn S s) :
    ∀ (k j : Nat) (r : Expr), FVarsIn S r →
      Pure.instProjs cx f ls₂ S' (renFV ρ s) k j (renFV ρ r) =
          (Pure.instProjs cx f ls₁ S' s k j r).map (renFV ρ) ∧
        ∀ w, Pure.instProjs cx f ls₁ S' s k j r = .ok w → FVarsIn S w
  | 0, _, r, hr => ⟨rfl, fun w h => by cases h; exact hr⟩
  | k + 1, j, r, hr => by
    simp only [Pure.instProjs]
    refine bind_ren (fun w => FVarsIn S w) _ (whnf_ren hcl hS hag f r hr) fun w hw => ?_
    cases w with
    | forallE n t b bi =>
      simp only [renFV]
      have := instProjs_ren f S' hs k (j + 1) (b.instantiate1' (.proj S' j s))
        (fvarsIn_inst (a := .proj S' j s) hs hw.2)
      rw [renFV_inst] at this
      exact this
    | _ => exact ⟨rfl, fun _ h => absurd h throw_ne_ok⟩

/-- `Erasure.Pure.inferType` commutes with the renaming of the term, the binder types and the
locals, and its results are in `S`. Adapted from `ML-V Oracle/Agree.lean:307 inferType_agree`. -/
theorem inferType_ren : ∀ (f : Nat) (Γ : List Expr) (e : Expr), FVarsIn S e →
    (∀ A ∈ Γ, FVarsIn S A) →
    Pure.inferType cx f ls₂ (Γ.map (renFV ρ)) (renFV ρ e) =
        (Pure.inferType cx f ls₁ Γ e).map (renFV ρ) ∧
      ∀ T, Pure.inferType cx f ls₁ Γ e = .ok T → FVarsIn S T
  | 0, _, e, _, _ => ⟨rfl, fun w h => absurd h throw_ne_ok⟩
  | f + 1, Γ, .bvar i, _, hΓ => by
    simp only [renFV, Pure.inferType, List.getElem?_map]
    cases hA : Γ[i]? with
    | none => exact ⟨rfl, fun T hT => absurd hT throw_ne_ok⟩
    | some A =>
      refine ⟨by simp only [Option.map_some]; rw [← renFV_lift]; rfl, fun T hT => ?_⟩
      cases hT
      exact fvarsIn_lift (hΓ A (List.mem_of_getElem? hA))
  | f + 1, Γ, .fvar x, h, _ => by
    have hx : S x := h
    simp only [renFV, Pure.inferType]
    rw [hag x hx]
    cases hl : Pure.findLocal ls₁ x with
    | none => exact ⟨rfl, fun T hT => absurd hT throw_ne_ok⟩
    | some l => exact ⟨rfl, fun T hT => by cases hT; exact (hS x hx l hl).1⟩
  | f + 1, Γ, .sort u, h, _ => ⟨rfl, fun T hT => by cases hT; trivial⟩
  | f + 1, Γ, .lit (.natVal _), _, _ => ⟨rfl, fun T hT => by cases hT; trivial⟩
  | f + 1, Γ, .lit (.strVal _), _, _ => ⟨rfl, fun T hT => absurd hT throw_ne_ok⟩
  | f + 1, Γ, .mvar _, _, _ => ⟨rfl, fun T hT => absurd hT throw_ne_ok⟩
  | f + 1, Γ, .const c us, h, _ => by
    simp only [renFV, Pure.inferType]
    cases hc : findConst cx.decls c with
    | none => exact ⟨rfl, fun T hT => absurd hT throw_ne_ok⟩
    | some ci =>
      have hty := fvarsIn_instLevels ci.levelParams us (closed_find hcl hc).1
      dsimp only
      split
      · refine ⟨?_, fun T hT => by cases hT; exact fvarsIn_false hty⟩
        show pure _ = pure (renFV ρ _)
        rw [renFV_closed ρ hty]
      · exact ⟨rfl, fun T hT => absurd hT throw_ne_ok⟩
  | f + 1, Γ, .app g a, ⟨hg, ha⟩, hΓ => by
    simp only [renFV, Pure.inferType]
    refine bind_ren (fun T => FVarsIn S T) _ (inferType_ren f Γ g hg hΓ) fun Tg hTg => ?_
    refine bind_ren (fun w => FVarsIn S w) _ (whnf_ren hcl hS hag f Tg hTg) fun w hw => ?_
    cases w with
    | forallE n t B bi =>
      simp only [renFV]
      exact ⟨by rw [← renFV_inst]; rfl, fun T h => by cases h; exact fvarsIn_inst ha hw.2⟩
    | _ => exact ⟨rfl, fun _ h => absurd h throw_ne_ok⟩
  | f + 1, Γ, .lam n t b bi, ⟨ht, hb⟩, hΓ => by
    have hΓ' : ∀ A ∈ t :: Γ, FVarsIn S A := by
      intro A hA; exact (List.mem_cons.1 hA).elim (fun h => h ▸ ht) (hΓ A)
    simp only [renFV, Pure.inferType]
    refine bind_ren (fun T => FVarsIn S T) _ (inferType_ren f (t :: Γ) b hb hΓ') fun B hB => ?_
    exact ⟨rfl, fun T h => by cases h; exact ⟨ht, hB⟩⟩
  | f + 1, Γ, .forallE n t b bi, ⟨ht, hb⟩, hΓ => by
    have hΓ' : ∀ A ∈ t :: Γ, FVarsIn S A := by
      intro A hA; exact (List.mem_cons.1 hA).elim (fun h => h ▸ ht) (hΓ A)
    simp only [renFV, Pure.inferType]
    refine bind_ren (fun T => FVarsIn S T) _ (inferType_ren f Γ t ht hΓ) fun Tt hTt => ?_
    refine bind_ren (fun _ => True) _ ⟨(whnf_ren hcl hS hag f Tt hTt).1, fun _ _ => trivial⟩
      fun w1 _ => ?_
    cases w1 with
    | sort u =>
      simp only [renFV]
      refine bind_ren (fun T => FVarsIn S T) _ (inferType_ren f (t :: Γ) b hb hΓ') fun Tb hTb => ?_
      refine bind_ren (fun _ => True) _ ⟨(whnf_ren hcl hS hag f Tb hTb).1, fun _ _ => trivial⟩
        fun w2 _ => ?_
      cases w2 with
      | sort v => exact ⟨rfl, fun T h => by cases h; trivial⟩
      | _ => exact ⟨rfl, fun _ h => absurd h throw_ne_ok⟩
    | _ => exact ⟨rfl, fun _ h => absurd h throw_ne_ok⟩
  | f + 1, Γ, .letE _ _ v b _, ⟨_, hv, hb⟩, hΓ => by
    simp only [renFV, Pure.inferType]
    rw [← renFV_inst]
    exact inferType_ren f Γ _ (fvarsIn_inst hv hb) hΓ
  | f + 1, Γ, .mdata _ e, h, hΓ => by
    simp only [renFV, Pure.inferType]; exact inferType_ren f Γ e h hΓ
  | f + 1, Γ, .proj S' i s, h, hΓ => by
    have hs : FVarsIn S s := h
    have thr : ∀ (e : EraseError), (throw e : Except EraseError Expr) =
        (throw e : Except EraseError Expr).map (renFV ρ) ∧
        ∀ b, (throw e : Except EraseError Expr) = .ok b → FVarsIn S b :=
      fun e => ⟨rfl, fun b h => absurd h throw_ne_ok⟩
    simp only [renFV, Pure.inferType]
    refine bind_ren (fun T => FVarsIn S T) _ (inferType_ren f Γ s h hΓ) fun T hT => ?_
    refine bind_ren (fun w => FVarsIn S w) _ (whnf_ren hcl hS hag f T hT) fun ws hw => ?_
    rw [spine_ren]
    have hargs : ∀ a ∈ (spine ws).2, FVarsIn S a := spine_snd hw
    generalize spine ws = p at hargs ⊢
    obtain ⟨hd, args⟩ := p
    cases hd
    case const S'' us =>
      simp only [renFV, List.length_map]
      split
      · next I R hSS hfS hfR =>
        split
        · exact ⟨rfl, fun _ h => nomatch h⟩
        split
        · next c hct hlen =>
          split
          · next _ cv hci =>
            split
            rotate_left
            · exact ⟨rfl, fun _ h => nomatch h⟩
            have hty := fvarsIn_instLevels (ConstantInfo.ctorInfo cv).levelParams us
              (closed_find (c := c) (ci := .ctorInfo cv) hcl (by first | assumption | simp_all)).1
            have hIF := instForalls_ren hcl hS hag f _ (args.take I.numParams) (fvarsIn_false hty)
              (fun a ha => hargs a (List.mem_of_mem_take ha))
            rw [renFV_closed ρ hty, List.map_take] at hIF
            refine bind_ren (fun r => FVarsIn S r) _ hIF fun r hr => ?_
            refine bind_ren (fun x => FVarsIn S x) _ (instProjs_ren hcl hS hag f S' hs i 0 r hr)
              fun x hx => ?_
            refine bind_ren (fun w => FVarsIn S w) _ (whnf_ren hcl hS hag f x hx) fun w hw' => ?_
            cases w with
            | forallE n d b bi => exact ⟨rfl, fun _ h' => by cases h'; exact hw'.1⟩
            | _ => exact thr _
          · exact thr _
        · exact thr _
      · exact thr _
    all_goals exact thr _

/-- `Erasure.Pure.isArity` is invariant under the renaming. Adapted from
`ML-V Oracle/Agree.lean:431 isArity_agree`. -/
theorem isArity_ren : ∀ (f : Nat) (T : Expr), FVarsIn S T →
    Pure.isArity cx f ls₂ (renFV ρ T) = Pure.isArity cx f ls₁ T
  | 0, _, _ => rfl
  | f + 1, T, h => by
    simp only [Pure.isArity]
    refine bind_ren_eq (fun w => FVarsIn S w) (whnf_ren hcl hS hag f T h) fun w hw => ?_
    cases w with
    | forallE n t B bi => simp only [renFV]; exact isArity_ren f B hw.2
    | _ => rfl

end

end OracleRen

open OracleRen

section
variable {S : FVarId → Prop} {ρ : FVarId → FVarId} {cx : Pure.Ctx} {ls₁ ls₂ : List Local}
variable (hcl : ClosedDecls cx.decls = true) (hS : LocalsSupport S ls₁) (hag : LocalsRen ρ S ls₁ ls₂)
include hcl hS hag

/-- The sort level the oracle computes for a term (`Erasure.Pure.typeLevel`) is invariant under a
renaming of the free variables of the term and the locals, over a closed closure. Reference: none
(DV-32). -/
theorem Pure.typeLevel_ren (fuel : Nat) (e : Expr) (he : FVarsIn S e) :
    Pure.typeLevel cx fuel ls₂ (renFV ρ e) = Pure.typeLevel cx fuel ls₁ e := by
  simp only [Pure.typeLevel]
  refine bind_ren_eq (fun T => FVarsIn S T) (inferType_ren hcl hS hag fuel [] e he (by simp))
    fun T hT => ?_
  refine bind_ren_eq (fun T => FVarsIn S T) (inferType_ren hcl hS hag fuel [] T hT (by simp))
    fun U hU => ?_
  refine bind_ren_eq (fun _ => True) ⟨(whnf_ren hcl hS hag fuel U hU).1, fun _ _ => trivial⟩
    fun w _ => ?_
  cases w <;> rfl

/-- The pure erasability oracle (`Erasure.Pure.isErasable`) is invariant under a renaming of the
free variables of the term and the locals, over a closed closure; the renaming may identify
variables outside `S`. With `ρ = id` this is the frame lemma `Pure.isErasable_agree` of
`ML-V Oracle/Agree.lean:458`. Reference: none (DV-13, DV-32). -/
theorem Pure.isErasable_ren (fuel : Nat) (e : Expr) (he : FVarsIn S e) :
    Pure.isErasable cx fuel ls₂ (renFV ρ e) = Pure.isErasable cx fuel ls₁ e := by
  unfold Pure.isErasable
  simp only [spine_ren]
  generalize spine e = p
  obtain ⟨hd, args⟩ := p
  cases hd <;> simp only [renFV]
  all_goals try (split; rfl)
  all_goals
    refine bind_ren_eq (fun T => FVarsIn S T) (inferType_ren hcl hS hag fuel [] e he (by simp))
      fun T hT => ?_
    rw [isArity_ren hcl hS hag fuel T hT]
    refine bind_congr_ok rfl fun b _ => ?_
    split
    · rfl
    · refine bind_ren_eq (fun T => FVarsIn S T) (inferType_ren hcl hS hag fuel [] T hT (by simp))
        fun U hU => ?_
      refine bind_ren_eq (fun _ => True) ⟨(whnf_ren hcl hS hag fuel U hU).1, fun _ _ => trivial⟩
        fun w _ => ?_
      cases w <;> rfl

end

/-- `forallView?` on a term that is not syntactically a `Π`. -/
theorem OracleRen.forallView?_of_not {decls : List ConstantInfo} {ls : List Local} {T : Expr}
    (h : ∀ y D C bi, T ≠ .forallE y D C bi) :
    forallView? decls ls T = match Pure.whnf ⟨decls⟩ oracleFuel ls T with
      | .ok (.forallE y D C bi) => some (y, D, C, bi)
      | _ => none := by
  unfold forallView?
  split
  · exact absurd rfl (h _ _ _ _)
  · rfl

/-- The leading `Π` that `forallView?` reads commutes with the renaming, and its domain and body
are in `S`. Reference: none. -/
theorem forallView?_ren {S : FVarId → Prop} {ρ : FVarId → FVarId} {decls : List ConstantInfo}
    {ls₁ ls₂ : List Local} (hcl : ClosedDecls decls = true) (hS : LocalsSupport S ls₁)
    (hag : LocalsRen ρ S ls₁ ls₂) (T : Expr) (hT : FVarsIn S T) :
    forallView? decls ls₂ (renFV ρ T) =
        (forallView? decls ls₁ T).map (fun v => (v.1, renFV ρ v.2.1, renFV ρ v.2.2.1, v.2.2.2)) ∧
      ∀ y D C bi, forallView? decls ls₁ T = some (y, D, C, bi) → FVarsIn S D ∧ FVarsIn S C := by
  by_cases hf : ∃ y D C bi, T = .forallE y D C bi
  · obtain ⟨y, D, C, bi, rfl⟩ := hf
    exact ⟨rfl, fun y' D' C' bi' h => by cases h; exact hT⟩
  have hf₁ : ∀ y D C bi, T ≠ .forallE y D C bi := fun y D C bi h => hf ⟨_, _, _, _, h⟩
  have hf₂ : ∀ y D C bi, renFV ρ T ≠ .forallE y D C bi := by
    intro y D C bi h; apply hf; cases T <;> simp [renFV] at h; exact ⟨_, _, _, _, rfl⟩
  rw [forallView?_of_not hf₁, forallView?_of_not hf₂]
  have ⟨iw, fw⟩ := whnf_ren (cx := ⟨decls⟩) hcl hS hag oracleFuel T hT
  rw [iw]
  cases hw : Pure.whnf ⟨decls⟩ oracleFuel ls₁ T with
  | error e => exact ⟨rfl, fun _ _ _ _ h => nomatch h⟩
  | ok w =>
    have hw' := fw w hw
    cases w with
    | forallE y D C bi => exact ⟨rfl, fun _ _ _ _ h => by cases h; exact hw'⟩
    | _ => exact ⟨rfl, fun _ _ _ _ h => nomatch h⟩

/-! ## Free variables of a marking -/

theorem OracleRen.fvarsIn_list {S : FVarId → Prop} {as âs : List Expr} (hlen : as.length = âs.length)
    (has : ∀ a ∈ as, FVarsIn S a)
    (h : ∀ (i : Nat) a â, as[i]? = some a → âs[i]? = some â → FVarsIn S a → FVarsIn S â) :
    ∀ â ∈ âs, FVarsIn S â := by
  intro â hâ
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hâ
  exact h i as[i] _ (List.getElem?_eq_getElem (hlen ▸ hi)) (List.getElem?_eq_getElem hi)
    (has _ (List.getElem_mem _))

section
variable {decls : List ConstantInfo} {cfg : ErasureConfig} (hcl : ClosedDecls decls = true)
include hcl

theorem OracleRen.fvarsIn_oracle_ty {S : FVarId → Prop} {ls : List Local} {e T : Expr}
    (hS : LocalsSupport S ls) (he : FVarsIn S e)
    (h : Pure.inferType ⟨decls⟩ oracleFuel ls [] e = .ok T) : FVarsIn S T :=
  (inferType_ren (cx := ⟨decls⟩) hcl hS localsRen_id oracleFuel [] e he (by simp)).2 T h

theorem OracleRen.fvarsIn_view {S : FVarId → Prop} {ls : List Local} {T D C : Expr} {y : Name}
    {bi : BinderInfo} (hS : LocalsSupport S ls) (hT : FVarsIn S T)
    (h : forallView? decls ls T = some (y, D, C, bi)) : FVarsIn S D ∧ FVarsIn S C :=
  (forallView?_ren hcl hS localsRen_id T hT).2 y D C bi h

mutual
/-- A marking has its free variables where the term and the locals have them, over a closed
closure: the η-domains that `MarkOf` writes come from the oracle's types (`inferType`,
`forallView?`), which stay within the locals' support. Reference: none. -/
theorem MarkOf.fvarsIn {ls : List Local} {e ê : Expr} :
    MarkOf decls cfg ls e ê → ∀ {S : FVarId → Prop}, LocalsSupport S ls → FVarsIn S e → FVarsIn S ê
  | .erase _, _, _, he => he
  | .fvar _, _, _, he => he
  | .mdata _ h, _, hS, he => MarkOf.fvarsIn h hS he
  | .lam _ _ h, _, hS, he =>
    ⟨he.1, fvarsIn_absFV (MarkOf.fvarsIn h (localsSupport_open hS he.1 (by simp))
      (fvarsIn_open he.2))⟩
  | .letE _ _ hv hb, _, hS, he =>
    ⟨he.1, MarkOf.fvarsIn hv (localsSupport_cons hS he.1 (fun v h => by cases h; exact he.2.1)
        (fun _ h => h) fun _ h => .inr h) he.2.1,
      fvarsIn_absFV (MarkOf.fvarsIn hb
        (localsSupport_open hS he.1 fun v h => by cases h; exact he.2.1) (fvarsIn_open he.2.2))⟩
  | .proj _ _ h, _, hS, he => MarkOf.fvarsIn h hS he
  | .litZero .., _, _, he | .litSucc .., _, _, he => he
  | .app _ _ _ _ hf hlen hargs, _, hS, he => by
    rw [fvarsIn_mkAppN] at he ⊢
    exact ⟨MarkOf.fvarsIn hf hS he.1,
      fvarsIn_list hlen he.2 fun i a â ha hâ => MarkOf.fvarsIn (hargs i a â ha hâ) hS⟩
  | .constApp _ _ hlen hargs, _, hS, he => by
    rw [fvarsIn_mkAppN] at he ⊢
    exact ⟨trivial, fvarsIn_list hlen he.2 fun i a â ha hâ => MarkOf.fvarsIn (hargs i a â ha hâ) hS⟩
  | .special _ _ hT h, _, hS, he => by
    have he' := (fvarsIn_mkAppN.1 he).2
    exact MarkEta.fvarsIn h hS (fvarsIn_oracle_ty hcl hS he hT) he'

theorem MarkEta.fvarsIn {ls : List Local} {ar : Nat} {T : Expr} {c : Name} {us : List Level}
    {as : List Expr} {ê : Expr} :
    MarkEta decls cfg ls ar T c us as ê → ∀ {S : FVarId → Prop}, LocalsSupport S ls →
      FVarsIn S T → (∀ a ∈ as, FVarsIn S a) → FVarsIn S ê
  | .sat _ h, _, hS, _, has => MarkSat.fvarsIn h hS has
  | .intro _ hv _ h, _, hS, hT, has => by
    have ⟨hD, hC⟩ := fvarsIn_view hcl hS hT hv
    refine ⟨hD, fvarsIn_absFV (MarkEta.fvarsIn h (localsSupport_open hS hD (by simp))
      (fvarsIn_open hC) ?_)⟩
    simp only [List.forall_mem_append, List.forall_mem_singleton]
    exact ⟨fun a ha => fvarsIn_mono (fun _ => .inl) (has a ha), Or.inr rfl⟩

theorem MarkSat.fvarsIn {ls : List Local} {c : Name} {us : List Level} {as : List Expr} {ê : Expr} :
    MarkSat decls cfg ls c us as ê → ∀ {S : FVarId → Prop}, LocalsSupport S ls →
      (∀ a ∈ as, FVarsIn S a) → FVarsIn S ê
  | .casesProp .., _, _, has => fvarsIn_mkAppN.2 ⟨trivial, has⟩
  | .casesReduced _ _ _ _ _ _ _ _ _ halt hlen hextra, _, hS, has => by
    refine fvarsIn_mkAppN.2 ⟨trivial, ?_⟩
    simp only [List.forall_mem_append, List.forall_mem_singleton] at has ⊢
    exact ⟨⟨⟨has.1.1.1, has.1.1.2⟩, MarkOf.fvarsIn halt hS has.1.2⟩,
      fvarsIn_list hlen has.2 fun i a â ha hâ => MarkOf.fvarsIn (hextra i a â ha hâ) hS⟩
  | .cases _ _ _ _ hac _ _ hd hlen hctors htys halts hlen' hextra, _, hS, has => by
    refine fvarsIn_mkAppN.2 ⟨trivial, ?_⟩
    simp only [List.forall_mem_append, List.forall_mem_singleton] at has ⊢
    refine ⟨⟨⟨has.1.1.1, MarkOf.fvarsIn hd hS has.1.1.2⟩, fvarsIn_list hlen has.1.2
      fun i a â ha hâ hfa => ?_⟩,
      fvarsIn_list hlen' has.2 fun i a â ha hâ => MarkOf.fvarsIn (hextra i a â ha hâ) hS⟩
    obtain ⟨T, hT⟩ := htys i a ha
    have hi := hac ▸ (List.getElem?_eq_some_iff.1 ha).1
    obtain ⟨cv, hcv⟩ := hctors i _ (List.getElem?_eq_getElem hi)
    exact MarkAlt.fvarsIn (halts i _ cv a â T (List.getElem?_eq_getElem hi) hcv ha hâ hT) hS hfa
      (fvarsIn_oracle_ty hcl hS hfa hT)
  | .ctor _ _ hlen hargs, _, hS, has =>
    fvarsIn_mkAppN.2 ⟨trivial, fvarsIn_list hlen has fun i a â ha hâ =>
      MarkOf.fvarsIn (hargs i a â ha hâ) hS⟩
  | .quotMk _ _ _ _ ha hlen hextra, _, hS, has => by
    refine fvarsIn_mkAppN.2 ⟨trivial, ?_⟩
    simp only [List.forall_mem_append, List.forall_mem_cons] at has ⊢
    exact ⟨⟨has.1.1, has.1.2.1, MarkOf.fvarsIn ha hS has.1.2.2.1, fun _ h => nomatch h⟩,
      fvarsIn_list hlen has.2 fun i a â ha hâ => MarkOf.fvarsIn (hextra i a â ha hâ) hS⟩
  | .quotLift _ _ _ _ hf hq hlen hextra, _, hS, has => by
    refine fvarsIn_mkAppN.2 ⟨trivial, ?_⟩
    simp only [List.forall_mem_append, List.forall_mem_cons] at has ⊢
    exact ⟨⟨has.1.1, has.1.2.1, has.1.2.2.1, MarkOf.fvarsIn hf hS has.1.2.2.2.1,
      has.1.2.2.2.2.1, MarkOf.fvarsIn hq hS has.1.2.2.2.2.2.1, fun _ h => nomatch h⟩,
      fvarsIn_list hlen has.2 fun i a â ha hâ => MarkOf.fvarsIn (hextra i a â ha hâ) hS⟩
  | .recr _ _ _ _ _ _ _ _ _ _ _ hlm hmins hli his hmaj hle hextra, _, hS, has => by
    refine fvarsIn_mkAppN.2 ⟨trivial, ?_⟩
    simp only [List.forall_mem_append, List.forall_mem_singleton] at has ⊢
    exact ⟨⟨⟨⟨⟨has.1.1.1.1.1, has.1.1.1.1.2⟩,
      fvarsIn_list hlm has.1.1.1.2 fun i a â ha hâ => MarkOf.fvarsIn (hmins i a â ha hâ) hS⟩,
      fvarsIn_list hli has.1.1.2 fun i a â ha hâ => MarkOf.fvarsIn (his i a â ha hâ) hS⟩,
      MarkOf.fvarsIn hmaj hS has.1.2⟩,
      fvarsIn_list hle has.2 fun i a â ha hâ => MarkOf.fvarsIn (hextra i a â ha hâ) hS⟩

theorem MarkAlt.fvarsIn {ls : List Local} {k : Nat} {e T ê : Expr} :
    MarkAlt decls cfg ls k e T ê → ∀ {S : FVarId → Prop}, LocalsSupport S ls →
      FVarsIn S e → FVarsIn S T → FVarsIn S ê
  | .done h, _, hS, he, _ => MarkOf.fvarsIn h hS he
  | .lam hv _ h, _, hS, he, hT => by
    have ⟨hD, hC⟩ := fvarsIn_view hcl hS hT hv
    exact ⟨he.1, fvarsIn_absFV (MarkAlt.fvarsIn h (localsSupport_open hS hD (by simp))
      (fvarsIn_open he.2) (fvarsIn_open hC))⟩
  | .intro _ hv _ h, _, hS, he, hT => by
    have ⟨hD, hC⟩ := fvarsIn_view hcl hS hT hv
    exact ⟨hD, fvarsIn_absFV (MarkAlt.fvarsIn h (localsSupport_open hS hD (by simp))
      ⟨fvarsIn_mono (fun _ => .inl) he, Or.inr rfl⟩ (fvarsIn_open hC))⟩
end

end

end EraseProof
