import EraseProof.Core.Steps
import EraseProof.Bridge.CLNames

/-!
# No value that `visitMutual` erases mentions its own declaration

`visitMutual` takes its fix branch on a declaration whose block has more than one member or whose
value mentions its own name (`Erasure.isRecursiveDecl`), and erases a value within a scope of the
constants it reaches (`ScopeOK`). On a closure that is part of a program con-leche accepts, the
order of con-leche's fold (`CL ConLeche/Kernel/CheckDecl.lean:178 checkDeclsPure`) settles both: it
checks each definition and opaque at the environment of the records before it, which must not bind
its name (`CL ConLeche/Kernel/CheckerBase.lean:104 checkConstantVal`) and must resolve every
constant of its value (`CL ConLeche/Semantics/DeclRun.lean:74 ValueFrontRun`). The constants of the
closure that this environment binds are a scope of the value without its own constant; a
definition or opaque of the closure is alone in its block by the fragment test (`PhaseIDecl`).
The field `CoreEnv.value` (`coreEnv_value`).
-/

open Lean Erasure

namespace EraseProof

namespace NonRec

/-- A constant that occurs in `e` for the traversal (`nameOccurs`) is a constant of `e`. Positive
form of `ML-V Core/NonRec.lean:66 nameOccurs_false`. -/
theorem nameOccurs_mem {p : Name → Prop} {d : Name} :
    ∀ {e : Expr}, ConstsIn p e → nameOccurs d e = true → p d
  | .const c _, h, ho => by
    simp only [nameOccurs, beq_iff_eq] at ho
    subst ho
    exact h
  | .lam _ _ b _, h, ho => nameOccurs_mem (e := b) h.2 ho
  | .mdata _ e, h, ho => nameOccurs_mem (e := e) h ho
  | .proj _ _ e, h, ho => nameOccurs_mem (e := e) h.2 ho
  | .app f a, h, ho => by
    simp only [nameOccurs, Bool.or_eq_true] at ho
    exact ho.elim (nameOccurs_mem h.1) (nameOccurs_mem h.2)
  | .letE _ _ v b _, h, ho => by
    simp only [nameOccurs, Bool.or_eq_true] at ho
    exact ho.elim (nameOccurs_mem h.2.1) (nameOccurs_mem h.2.2)
  | .bvar _, _, ho | .fvar _, _, ho | .mvar _, _, ho | .sort _, _, ho | .forallE .., _, ho
  | .lit _, _, ho => by simp [nameOccurs] at ho

/-! ## The order of con-leche's fold -/

/-- A successful fold over `A ++ B` folds `A`, then `B`. -/
theorem foldlM_append_ok {α σ ε : Type} {f : σ → α → Except ε σ} {e r : σ} {A B : List α}
    (h : (A ++ B).foldlM f e = .ok r) : ∃ m, A.foldlM f e = .ok m ∧ B.foldlM f m = .ok r := by
  rw [List.foldlM_append] at h
  exact RegisterInd.ok_of_bind h

/-- A successful fold over `x :: B` takes one step, then folds `B`. -/
theorem foldlM_cons_ok {α σ ε : Type} {f : σ → α → Except ε σ} {e r : σ} {x : α} {B : List α}
    (h : (x :: B).foldlM f e = .ok r) : ∃ m, f e x = .ok m ∧ B.foldlM f m = .ok r := by
  rw [List.foldlM_cons] at h
  exact RegisterInd.ok_of_bind h

/-- One accepted step of the fold keeps every bound name. -/
theorem step_mono {F : Nat} {pins : List ConLeche.NatOpPinSet} {e e' : ConLeche.Env}
    {d : ConLeche.Declaration}
    (h : ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pins e d = .ok e') :
    ∀ n, (e.find? n).isSome = true → (e'.find? n).isSome = true := by
  obtain ⟨rfl, hfr⟩ := checkDecl_pushes h
  intro n hn
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hn
  rw [find?_pushDelta_old hfr hc]
  rfl

/-- A record that con-leche checks with a value: a definition's or an opaque's. -/
def ValRec (y : ConLeche.Declaration) (cv : ConLeche.ConstantVal) (w : ConLeche.Expr) : Prop :=
  (∃ hint, y = .defnDecl cv w hint) ∨ y = .opaqueDecl cv w

/-- The front checks of an accepted definition or opaque: its name is unbound before the step
(`CL ConLeche/Kernel/CheckerBase.lean:104 checkConstantVal`) and its value resolves at the step
(`CL ConLeche/Semantics/DeclRun.lean:74 ValueFrontRun`). -/
theorem front_value {F : Nat} {pins : List ConLeche.NatOpPinSet} {e e' : ConLeche.Env}
    {y : ConLeche.Declaration} {cv : ConLeche.ConstantVal} {w : ConLeche.Expr} (hy : ValRec y cv w)
    (h : ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pins e y = .ok e') :
    e.find? cv.name = none ∧ w.constsResolve e = true := by
  rcases hy with ⟨hint, rfl⟩ | rfl
  · exact ⟨(checkDecl_pushes h).2 _ (List.mem_singleton_self _), (front_defn h).2⟩
  · exact ⟨(checkDecl_pushes h).2 _ (List.mem_singleton_self _), (front_opaque h).2⟩

/-- **A value whose name a step's environment binds resolves at it**: in a successful fold over
`A ++ x :: B`, a definition or opaque record `y` whose name the environment `E` of `x`'s step binds
is in `A`, checked at an environment whose names `E` binds; at `x` or in `B` it would be checked
at an environment that binds its name already. -/
theorem fold_order {F : Nat} {pins : List ConLeche.NatOpPinSet} {A B : List ConLeche.Declaration}
    {e₀ E E' env : ConLeche.Env} {x y : ConLeche.Declaration} {cv : ConLeche.ConstantVal}
    {w : ConLeche.Expr}
    (hA : A.foldlM (ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pins) e₀ = .ok E)
    (hx : ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pins E x = .ok E')
    (hB : B.foldlM (ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pins) E' =
      .ok env)
    (hy : y ∈ A ++ x :: B) (hyv : ValRec y cv w) (hb : (E.find? cv.name).isSome = true) :
    w.constsResolve E = true := by
  rcases List.mem_append.mp hy with hyA | hyx
  · obtain ⟨A₁, A₂, rfl⟩ := List.append_of_mem hyA
    obtain ⟨Ey, -, h₂⟩ := foldlM_append_ok hA
    obtain ⟨Ey', hy', h₃⟩ := foldlM_cons_ok h₂
    exact ConLeche.Expr.constsResolve_of_find
      (fun n hn => (foldlM_checkDecl_run A₂ h₃).1 n (step_mono hy' n hn)) (front_value hyv hy').2
  · exfalso
    rcases List.mem_cons.mp hyx with rfl | hyB
    · rw [(front_value hyv hx).1] at hb
      cases hb
    · obtain ⟨B₁, B₂, rfl⟩ := List.append_of_mem hyB
      obtain ⟨Ey, h₁, h₂⟩ := foldlM_append_ok hB
      obtain ⟨Ey', hy', -⟩ := foldlM_cons_ok h₂
      have hb' := (foldlM_checkDecl_run B₁ h₁).1 _ (step_mono hx _ hb)
      rw [(front_value hyv hy').1] at hb'
      cases hb'

/-! ## The program's definitions and opaques -/

variable {view : EnvView} {cfg : ErasureConfig} {decls : List ConstantInfo}

/-- A definition or opaque of `P` in the first-phase fragment (`PhaseIDecl`: safe) has its value
in a record of `DeclsOf? P`, under its translated name. -/
theorem valRec_of {P : List ConstantInfo} {ds : List ConLeche.Declaration}
    (hds : DeclsOf? P = some ds) {ci : ConstantInfo} (hci : ci ∈ P) {v : Expr}
    (hv : ci.value? (allowOpaque := true) = some v) (hthm : IsThm ci = false)
    (hph : PhaseIDecl view cfg decls ci) :
    ∃ y cv w, y ∈ ds ∧ cv.name = Name.toCL ci.name ∧ toCL? v = some w ∧ ValRec y cv w := by
  obtain ⟨L, hL, hLds⟩ := DeclsOf?.mem hds hci
  cases ci with
  | defnInfo d =>
    cases hv
    have hs := hph.1
    cases hcv : cvOf? d.toConstantVal with
    | none => simp [declOf?, hs, hcv] at hL
    | some cv =>
    cases hval : toCL? d.value with
    | none => simp [declOf?, hs, hcv, hval] at hL
    | some w =>
    simp [declOf?, hs, hcv, hval] at hL
    subst hL
    obtain ⟨ty, -, rfl⟩ := cvOf?_eq_some hcv
    exact ⟨_, _, w, hLds _ (List.mem_singleton_self _), rfl, rfl, .inl ⟨_, rfl⟩⟩
  | opaqueInfo o =>
    cases hv
    have hs := hph.1
    cases hcv : cvOf? o.toConstantVal with
    | none => simp [declOf?, hs, hcv] at hL
    | some cv =>
    cases hval : toCL? o.value with
    | none => simp [declOf?, hs, hcv, hval] at hL
    | some w =>
    simp [declOf?, hs, hcv, hval] at hL
    subst hL
    obtain ⟨ty, -, rfl⟩ := cvOf?_eq_some hcv
    exact ⟨_, _, w, hLds _ (List.mem_singleton_self _), rfl, rfl, .inr rfl⟩
  | thmInfo _ => cases hthm
  | _ => cases hv

/-- A definition or opaque in the first-phase fragment is alone in its block. -/
theorem phase_all {ci : ConstantInfo} {v : Expr} (hph : PhaseIDecl view cfg decls ci)
    (hv : ci.value? (allowOpaque := true) = some v) (hthm : IsThm ci = false) :
    ci.all.length = 1 := by
  cases ci with
  | defnInfo d => show d.all.length = 1; rw [hph.2.1]; rfl
  | opaqueInfo o => show o.all.length = 1; rw [hph.2.1]; rfl
  | thmInfo _ => cases hthm
  | _ => cases hv

end NonRec

open NonRec in
/-- **con-leche checks a value before its constant**: for a definition or opaque `ci` of `P` in
the first-phase fragment, the environment `E` of the fold's step at its record does not bind its
name, binds every constant of its value, and binds every constant of the value of each other such
definition or opaque whose name it binds. Replaces the induction on `ML-V Core/NonRec.lean:81
ProgEnv.scoped`. Reference: `fresh_global` (`MR common/theories/EnvironmentTyping.v:1738`) in
`on_global_decls` (`MR common/theories/EnvironmentTyping.v:1749`), which types a declaration in
the environment of the earlier ones. -/
theorem ConLecheAccepts.valueEnv {view : EnvView} {cfg : ErasureConfig}
    {decls P : List ConstantInfo} {env : ConLeche.Env} (h : ConLecheAccepts P env)
    {ci : ConstantInfo} (hci : ci ∈ P) {v : Expr} (hv : ci.value? (allowOpaque := true) = some v)
    (hthm : IsThm ci = false) (hph : PhaseIDecl view cfg decls ci) :
    ∃ E : ConLeche.Env, E.find? (Name.toCL ci.name) = none ∧
      ConstsIn (fun n => (E.find? (Name.toCL n)).isSome = true) v ∧
      ∀ ci' ∈ P, ∀ v', ci'.value? (allowOpaque := true) = some v' → IsThm ci' = false →
        PhaseIDecl view cfg decls ci' → (E.find? (Name.toCL ci'.name)).isSome = true →
        ConstsIn (fun n => (E.find? (Name.toCL n)).isSome = true) v' := by
  obtain ⟨ds, hds, hf, -⟩ := h
  have conv : ∀ {x : Expr} {w : ConLeche.Expr} {E : ConLeche.Env}, toCL? x = some w →
      w.constsResolve E = true → ConstsIn (fun n => (E.find? (Name.toCL n)).isSome = true) x :=
    fun hx hr => (constsIn_of_clResolves hx (clResolves_of_constsResolve hr)).1
  obtain ⟨y, cv, w, hy, hcvn, hw, hyv⟩ := valRec_of hds hci hv hthm hph
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hy
  have hf' : (A ++ y :: B).foldlM
      (ConLeche.checkDecl .verified (ConLeche.fueledOps .verified ConLeche.checkFuel) [])
      ConLeche.Env.empty = .ok env := hf
  obtain ⟨E, hA, hrest⟩ := foldlM_append_ok hf'
  obtain ⟨E', hyE, hB⟩ := foldlM_cons_ok hrest
  obtain ⟨hfr, hres⟩ := front_value hyv hyE
  refine ⟨E, hcvn ▸ hfr, conv hw hres, fun ci' hci' v' hv' hthm' hph' hb => ?_⟩
  obtain ⟨y', cv', w', hy', hcvn', hw', hyv'⟩ := valRec_of hds hci' hv' hthm' hph'
  exact conv hw' (fold_order hA hyE hB hy' hyv' (hcvn' ▸ hb))

open NonRec in
/-- **The field `CoreEnv.value`**: on a closure that is part of a program con-leche accepts
(`SubEnv`), closed under what the traversal reads (`DepClosed`) and in the first-phase fragment
(`PhaseIDecl`), the value of a definition or opaque that `visitMutual` erases (not a theorem, not
a recognized `casesOn`) is of a one-member block and has a scope without its own constant: the
constants of the closure that con-leche's fold binds when it checks the value
(`ConLecheAccepts.valueEnv`). So `visitMutual` takes its non-recursive branch
(`Erasure.isRecursiveDecl` is false). Port of `ML-V Core/NonRec.lean:126 isRecursiveDecl_false`,
with con-leche's fold in place of Metalean's environment. Reference: `erase_global_deps_fresh`
(`MR E/ErasureFunctionProperties.v:1206`), from `fresh_global`
(`MR common/theories/EnvironmentTyping.v:1738`). -/
theorem coreEnv_value {P decls : List ConstantInfo} {env : ConLeche.Env} {view : EnvView}
    {cfg : ErasureConfig} (hacc : ConLecheAccepts P env) (hsub : SubEnv decls P)
    (hdep : DepClosed decls) (hph : ∀ ci ∈ decls, PhaseIDecl view cfg decls ci) :
    ∀ c ci v, findDecl decls c = some ci → ci.value? (allowOpaque := true) = some v →
      IsThm ci = false → casesInfo? decls c = none →
      ci.all.length = 1 ∧ ∃ Sc, Steps.ScopeOK decls Sc ∧ (∀ d, nameOccurs d v = true → Sc d) ∧ ¬ Sc c := by
  intro c ci v hci hv hthm hcs
  obtain ⟨hmem, rfl⟩ := findDecl_mem hci
  have inP : ∀ {di : ConstantInfo}, di ∈ decls → di ∈ P := fun hdi => (findDecl_mem (hsub _ hdi)).1
  -- the constants of a value the traversal reads are in the closure
  have read : ∀ {di : ConstantInfo} {vd : Expr}, di ∈ decls →
      di.value? (allowOpaque := true) = some vd → IsThm di = false →
      casesInfo? decls di.name = none → ConstsIn (fun n => (findDecl decls n).isSome = true) vd := by
    intro di vd hdi hvd hthd hcsd
    refine (hdep di hdi).1 vd ?_
    cases di with
    | defnInfo dv =>
      cases hvd
      have hcs' : casesInfo? decls dv.name = none := hcsd
      exact .inr (.inl ⟨dv, rfl, rfl, by simp [casesOnOf?, hcs']⟩)
    | opaqueInfo o => cases hvd; exact .inr (.inr ⟨o, rfl, rfl⟩)
    | thmInfo _ => cases hthd
    | _ => cases hvd
  obtain ⟨E, hfr, hin, hcl⟩ := hacc.valueEnv (inP hmem) hv hthm (hph ci hmem)
  refine ⟨phase_all (hph ci hmem) hv hthm,
    fun d => (findDecl decls d).isSome = true ∧ (E.find? (Name.toCL d)).isSome = true, ?_,
    fun d hd => ⟨nameOccurs_mem (read hmem hv hthm hcs) hd, nameOccurs_mem hin hd⟩, ?_⟩
  · rintro d ⟨hd, hdE⟩
    obtain ⟨di, hdi⟩ := Option.isSome_iff_exists.mp hd
    obtain ⟨hdim, rfl⟩ := findDecl_mem hdi
    exact ⟨di, hdi, fun vd hvd hthd hcsd d' hd' => ⟨nameOccurs_mem (read hdim hvd hthd hcsd) hd',
      nameOccurs_mem (hcl di (inP hdim) vd hvd hthd (hph di hdim) hdE) hd'⟩⟩
  · rintro ⟨-, h⟩
    rw [hfr] at h
    cases h

end EraseProof
