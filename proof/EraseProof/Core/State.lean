import EraseProof.Relation.Deps
import EraseProof.Core.Collect

/-!
# The traversal's state invariant

The shipping traversal (`Erasure.visitExpr` and the functions it calls) keeps in its state
(`Erasure.ErasureState`) the constants it has registered, each with its kername, and the λ□
environment `gdecls` it emits. `StateOK` is the invariant of that state on the pure path: every
registered constant has its own kername, is a declaration of the closure, and its entry erases its
declaration (`ErasesDecl`) with erased dependencies; every entry belongs to a registered constant;
every stored body is closed. It is the invariant of MetaRocq's `erase_global_deps`
(`MR E/ErasureFunction.v:1602`): `includes_deps` (`MR E/ErasureFunctionProperties.v:41`) of the
registered constants.

The registration lemmas: an unregistered constant's kername is fresh (`StateOK.fresh`, from
`KernameInj`); registering constants whose entries are erased keeps `StateOK` and grows the λ□
environment freshly (`StateOK.grow`, `StateOK.register`), which is the `erase_constant_body` step
(`MR E/ErasureFunction.v:1309`) for a definition (`StateOK.registerDef`) and for an axiom
(`addAxiom_ok`); `get_constant_kername` returns a registered constant's kername
(`get_constant_kername_ok`), whose `tConst` has erased dependencies (`StateOK.kername`). Facts
about an earlier λ□ environment transfer along `LenvExt` by `RecIn.ext`, `Erases.mono_rc` and
`ErasesDeps.ext`.
-/

open Lean Lean4Lean Erasure

namespace EraseProof

section
variable {venv : VEnv} {σ : EvalEnv} {lenv lenv' lenv'' : GlobalDeclarations}

/-! ## The invariant -/

/-- The traversal's state invariant over the model `venv` and the evaluation environment `σ`: every
registered constant `c` has the kername `toKername c`, is a declaration of `σ`, and its entry erases
its declaration (`ErasesDecl`) with erased dependencies; every entry of the λ□ environment belongs
to a registered constant; every stored body is closed. Reference: `includes_deps` with
`global_erased_with_deps` (`MR E/ErasureFunctionProperties.v:41,30`), the invariant of
`erase_global_deps` (`MR E/ErasureFunction.v:1602`); `closed_env` (`MR E/EGlobalEnv.v:181`). -/
structure StateOK (venv : VEnv) (σ : EvalEnv) (st : ErasureState) : Prop where
  /-- A registered constant: its kername, its declaration, its erased entry and dependencies. -/
  registered : ∀ c kn, st.constants[c]? = some kn → kn = toKername c ∧
    ∃ ci cb, findDecl σ.decls c = some ci ∧ lookupConst st.gdecls kn = some cb ∧
      ErasesDecl venv σ st.gdecls ci cb ∧
      ∀ b, cb.cst_body = some b → ErasesDeps venv σ st.gdecls b
  /-- Every entry of the λ□ environment belongs to a registered constant. -/
  entries : ∀ d ∈ st.gdecls, ∃ c : Name, st.constants[c]? = some d.1
  /-- Every stored body is closed. -/
  closed : LenvClosed st.gdecls

/-! ## Growth of the λ□ environment -/

/-- The λ□ environment extends itself. Reference: `extends_prefix` (`MR E/EGlobalEnv.v:189`) with
the empty prefix. -/
theorem LenvExt.refl : LenvExt lenv lenv :=
  ⟨[], rfl, fun _ h => nomatch h⟩

/-- Fresh growth composes. Reference: `extends_prefix` (`MR E/EGlobalEnv.v:189`), whose prefixes
concatenate. -/
theorem LenvExt.trans (h₁ : LenvExt lenv lenv') (h₂ : LenvExt lenv' lenv'') :
    LenvExt lenv lenv'' := by
  obtain ⟨new₁, rfl, hf₁⟩ := h₁
  obtain ⟨new₂, rfl, hf₂⟩ := h₂
  refine ⟨new₂ ++ new₁, (List.append_assoc ..).symm, fun kn hkn => ?_⟩
  rw [List.map_append, List.mem_append] at hkn
  rcases hkn with hkn | hkn
  · have h := hf₂ kn hkn
    rw [List.find?_append, Option.or_eq_none_iff] at h
    exact h.2
  · exact hf₁ kn hkn

/-- A constant that `lookupConst` finds is an entry of the environment. Reference:
`declared_constant` (`MR E/EGlobalEnv.v:24`), through `lookup_env` (`:16`). -/
theorem lookupConst_mem (h : lookupConst lenv kn = some cb) :
    (kn, GlobalDecl.constantDecl cb) ∈ lenv := by
  unfold lookupConst at h
  split at h
  · rename_i k _ hf
    cases h
    have hp := List.find?_some hf
    have hk : k = kn := Kername.eq_of_beq hp
    subst hk
    exact List.mem_of_find?_eq_some hf
  · cases h

/-- The entry just added is found. Reference: the head case of `lookup_env`
(`MR E/EGlobalEnv.v:16`). -/
theorem lookupConst_cons_self :
    lookupConst ((kn, GlobalDecl.constantDecl cb) :: lenv) kn = some cb := by
  simp [lookupConst, List.find?, kername_beq_self]

/-! ## Closedness of an erased closed term -/

/-- The erasure of a term without free variables has none, when the targets of recursive
constants have none. Reference: none (the traversal's free variables, DV-13; MetaRocq's `erase`
is de Bruijn). -/
theorem Erases.hasFVar_eq_false {Us : List Name} {ac : Name → Bool} {rc : Name → LBTerm → Prop}
    {Δ : VLCtx} {e : Expr} {t : LBTerm} (hrc : ∀ c t, rc c t → hasFVar x t = false)
    (hcl : FVarsIn (fun _ => False) e) (h : Erases venv Us ac rc Δ e t) : hasFVar x t = false := by
  induction h with
  | bvar | const | box => rfl
  | fvar => exact hcl.elim
  | lam _ _ ih => exact ih hcl.2
  | letE _ _ _ _ ihv ihb =>
    simp only [hasFVar, ihv hcl.2.1, ihb hcl.2.2, Bool.or_self]
  | app _ _ ihf iha => simp only [hasFVar, ihf hcl.1, iha hcl.2, Bool.or_self]
  | constRec _ hr => exact hrc _ _ hr
  | mdata _ ih => exact ih hcl

/-! ## Registration -/

/-- The empty state satisfies the invariant (the traversal starts from it). Reference: the `[]`
case of `erase_global_deps` (`MR E/ErasureFunction.v:1602`). -/
theorem StateOK.empty : StateOK venv σ {} where
  registered c kn h := by simp at h
  entries _ h := nomatch h
  closed _ _ _ h := nomatch h

/-- The invariant reads only the registered constants and the λ□ environment. Reference: none. -/
theorem StateOK.congr {st st' : ErasureState} (hok : StateOK venv σ st)
    (hc : st'.constants = st.constants) (hg : st'.gdecls = st.gdecls) : StateOK venv σ st' := by
  obtain ⟨h₁, h₂, h₃⟩ := hok
  exact ⟨hc ▸ hg ▸ h₁, hc ▸ hg ▸ h₂, hg ▸ h₃⟩

/-- A registered constant's kername is its own, and its `tConst` has erased dependencies.
Reference: `erase_global_erases_deps` (`MR E/ErasureFunctionProperties.v:172`), its `tConst`
case. -/
theorem StateOK.kername {st : ErasureState} (hok : StateOK venv σ st)
    (h : st.constants[c]? = some kn) :
    kn = toKername c ∧ ErasesDeps venv σ st.gdecls (.const kn) := by
  obtain ⟨rfl, _, _, hf, hl, hd, hb⟩ := hok.registered c kn h
  exact ⟨rfl, .const hf hl hd hb⟩

/-- An unregistered constant of the closure has a fresh kername (from `KernameInj`). Reference:
`fresh_global` (`MR E/EGlobalEnv.v:191`). -/
theorem StateOK.fresh {st : ErasureState} (hok : StateOK venv σ st)
    (hinj : KernameInj σ.decls) (hc : (findDecl σ.decls c).isSome)
    (hnew : st.constants[c]? = none) : st.gdecls.find? (·.1 == toKername c) = none := by
  rw [List.find?_eq_none]
  intro d hd hdk
  obtain ⟨c', hc'⟩ := hok.entries d hd
  obtain ⟨hk, _, _, hf, -⟩ := hok.registered c' d.1 hc'
  have heq : c = c' :=
    hinj c c' hc (by rw [hf]; rfl) ((Kername.eq_of_beq hdk).symm.trans hk)
  rw [← heq, hnew] at hc'
  cases hc'

/-- Stored fixpoints are erased blocks: `BlocksErased` follows from the invariant. Reference:
`globals_erased_with_deps` (`MR E/EDeps.v:594`), for `tFix` bodies (DV-7). -/
theorem StateOK.blocksErased {st : ErasureState} (hok : StateOK venv σ st)
    (hinj : KernameInj σ.decls) : BlocksErased venv σ st.gdecls := by
  intro c ci defs i hc hl
  obtain ⟨c', hc'⟩ := hok.entries _ (lookupConst_mem hl)
  obtain ⟨hk, ci', cb', hf', hl', hd', hb'⟩ := hok.registered c' _ hc'
  have heq : c = c' := hinj c c' (by rw [hc]; rfl) (by rw [hf']; rfl) hk
  subst heq
  rw [hc] at hf'
  cases hf'
  rw [hl] at hl'
  cases hl'
  refine ⟨hd', fun d hd => ?_⟩
  cases hb' _ rfl with
  | fix h => exact h d hd

/-- Registering constants whose entries erase their declarations keeps the invariant: if the
registered constants stay registered, the λ□ environment grows by entries `new` of newly registered
constants, and each newly registered constant has its own kername and an entry that erases its
declaration with erased dependencies and a closed body, then `StateOK` holds after, and the
environment grows by fresh kernames. Reference: the `ConstantDecl` step of `erase_global_deps` (`MR
E/ErasureFunction.v:1602`), with `erases_deps_cons` (`MR E/EDeps.v:492`). -/
theorem StateOK.grow {st st' : ErasureState} {new : GlobalDeclarations}
    (hok : StateOK venv σ st) (hinj : KernameInj σ.decls)
    (hg : st'.gdecls = new ++ st.gdecls)
    (hkeep : ∀ (c : Name) kn, st.constants[c]? = some kn → st'.constants[c]? = some kn)
    (hnew : ∀ d ∈ new, ∃ c : Name, st.constants[c]? = none ∧ st'.constants[c]? = some d.1)
    (hreg : ∀ (c : Name) kn, st.constants[c]? = none → st'.constants[c]? = some kn →
      kn = toKername c ∧
      ∃ ci cb, findDecl σ.decls c = some ci ∧ lookupConst st'.gdecls kn = some cb ∧
        ErasesDecl venv σ st'.gdecls ci cb ∧ ∀ b, cb.cst_body = some b →
          ErasesDeps venv σ st'.gdecls b ∧ closedn 0 b = true ∧ ∀ x, hasFVar x b = false) :
    StateOK venv σ st' ∧ LenvExt st.gdecls st'.gdecls := by
  have hx : LenvExt st.gdecls st'.gdecls := by
    refine ⟨new, hg, fun kn hkn => ?_⟩
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hkn
    obtain ⟨c, hc0, hc1⟩ := hnew d hd
    obtain ⟨hk, _, _, hf, -⟩ := hreg c _ hc0 hc1
    rw [hk]
    exact hok.fresh hinj (by rw [hf]; rfl) hc0
  have hentries : ∀ d ∈ st'.gdecls, ∃ c : Name, st'.constants[c]? = some d.1 := by
    intro d hd
    rw [hg, List.mem_append] at hd
    rcases hd with hd | hd
    · obtain ⟨c, -, hc⟩ := hnew d hd
      exact ⟨c, hc⟩
    · obtain ⟨c, hc⟩ := hok.entries d hd
      exact ⟨c, hkeep _ _ hc⟩
  refine ⟨⟨fun c kn h => ?_, hentries, fun kn cb b hl hb => ?_⟩, hx⟩
  · cases hc0 : st.constants[c]? with
    | none =>
      obtain ⟨hk, ci, cb, hf, hl, hd, hb⟩ := hreg c kn hc0 h
      exact ⟨hk, ci, cb, hf, hl, hd, fun b h' => (hb b h').1⟩
    | some kn' =>
      have h' := hkeep c kn' hc0
      rw [h] at h'
      cases h'
      obtain ⟨hk, ci, cb, hf, hl, hd, hb⟩ := hok.registered c kn hc0
      exact ⟨hk, ci, cb, hf, lookupConst_ext hx hl, hd.ext hx, fun b h' => (hb b h').ext hx⟩
  · obtain ⟨c, hc⟩ := hentries _ (lookupConst_mem hl)
    cases hc0 : st.constants[c]? with
    | none =>
      obtain ⟨-, _, cb', -, hl', -, hb'⟩ := hreg c kn hc0 hc
      rw [hl] at hl'
      cases hl'
      exact (hb' b hb).2
    | some kn' =>
      have h' := hkeep c kn' hc0
      rw [hc] at h'
      cases h'
      obtain ⟨-, _, cb', -, hl', -⟩ := hok.registered c kn hc0
      rw [lookupConst_ext hx hl', Option.some.injEq] at hl
      subst hl
      exact hok.closed kn cb' b hl' hb

/-- Registering an unregistered constant of the closure with an entry that erases its declaration,
with erased dependencies and a closed body in the environment before the entry (only older
dependencies), keeps the invariant; the λ□ environment grows by the fresh entry. This is the state
update of `visitMutual` and `addAxiom`. Reference: the `ConstantDecl` step of `erase_global_deps`
(`MR E/ErasureFunction.v:1602`), with `erases_deps_cons` (`MR E/EDeps.v:492`). -/
theorem StateOK.register {st : ErasureState} (hok : StateOK venv σ st)
    (hinj : KernameInj σ.decls) (hc : findDecl σ.decls c = some ci)
    (hnew : st.constants[c]? = none) (hd : ErasesDecl venv σ st.gdecls ci cb)
    (hb : ∀ b, cb.cst_body = some b →
      ErasesDeps venv σ st.gdecls b ∧ closedn 0 b = true ∧ ∀ x, hasFVar x b = false) :
    StateOK venv σ
      { st with
        constants := st.constants.insert c (toKername c)
        gdecls := (toKername c, .constantDecl cb) :: st.gdecls } ∧
    LenvExt st.gdecls ((toKername c, .constantDecl cb) :: st.gdecls) := by
  have hx : LenvExt st.gdecls ((toKername c, .constantDecl cb) :: st.gdecls) := by
    refine ⟨[(toKername c, .constantDecl cb)], rfl, fun kn hkn => ?_⟩
    rw [List.map_cons, List.map_nil, List.mem_singleton] at hkn
    rw [hkn]
    exact hok.fresh hinj (by rw [hc]; rfl) hnew
  refine hok.grow (new := [(toKername c, .constantDecl cb)]) hinj rfl ?_ ?_ ?_
  · intro c' kn h
    show (st.constants.insert c (toKername c))[c']? = some kn
    rw [Std.HashMap.getElem?_insert]
    split
    · rename_i hcc
      rw [← beq_iff_eq.1 hcc, hnew] at h
      cases h
    · exact h
  · intro d hd
    rw [List.mem_singleton] at hd
    subst hd
    exact ⟨c, hnew, Std.HashMap.getElem?_insert_self⟩
  · intro c' kn h0 h1
    change (st.constants.insert c (toKername c))[c']? = some kn at h1
    rw [Std.HashMap.getElem?_insert] at h1
    split at h1
    · rename_i hcc
      cases beq_iff_eq.1 hcc
      cases h1
      exact ⟨rfl, ci, cb, hc, lookupConst_cons_self, hd.ext hx,
        fun b h => ⟨(hb b h).1.ext hx, (hb b h).2⟩⟩
    · rw [h0] at h1
      cases h1

/-- The `erase_constant_body` step for a definition: registering an unregistered, non-remapped,
non-recursive constant of the closure with an erasure `t` of its value, whose dependencies are
erased, keeps the invariant; the λ□ environment grows by the fresh entry. `t` is closed, since the
value is typed in the empty context and has no free variables (`ClosedDecls`). Reference:
`erase_constant_body` (`MR E/ErasureFunction.v:1309`), `erases_deps_cons` (`MR E/EDeps.v:492`). -/
theorem StateOK.registerDef {st : ErasureState} {v : Expr} {v' : VExpr} {t : LBTerm}
    (hok : StateOK venv σ st) (hinj : KernameInj σ.decls) (hcld : ClosedDecls σ.decls)
    (hc : findDecl σ.decls c = some ci) (hnew : st.constants[c]? = none)
    (hax : σ.axiomatized ci = false) (hrec : RecursiveDecl ci = false)
    (hv : ci.value? (allowOpaque := true) = some v) (he : TrS venv ci.levelParams [] v v')
    (her : Erases venv ci.levelParams σ.isAtom (RecIn st.gdecls) [] v t)
    (hdeps : ErasesDeps venv σ st.gdecls t) :
    StateOK venv σ
      { st with
        constants := st.constants.insert c (toKername c)
        gdecls := (toKername c, .constantDecl ⟨some t⟩) :: st.gdecls } ∧
    LenvExt st.gdecls ((toKername c, .constantDecl ⟨some t⟩) :: st.gdecls) := by
  have hd : ErasesDecl venv σ st.gdecls ci ⟨some t⟩ := by
    unfold ErasesDecl
    rw [hv]
    exact .inr (.inr ⟨hax, hrec, t, rfl, her⟩)
  refine hok.register hinj hc hnew hd fun b hb => ?_
  cases hb
  refine ⟨hdeps, Erases.closed ?_ he her, fun x => Erases.hasFVar_eq_false ?_
    ((hcld ci (List.mem_of_find?_eq_some hc)).2 v hv) her⟩
  · rintro c' _ ⟨defs, i, rfl, hl⟩
    exact (hok.closed _ _ _ hl rfl).1
  · rintro c' _ ⟨defs, i, rfl, hl⟩
    exact (hok.closed _ _ _ hl rfl).2 x

/-- `addAxiom` at the pure backend, on an unregistered constant of the closure that has no value or
is remapped: it registers the constant with an empty body, and the invariant holds after it; the λ□
environment grows by the fresh entry. Reference: the `None` case of `erase_constant_body`
(`MR E/ErasureFunction.v:1309`); the remapped case of `erases_constant_body` (DV-12). -/
theorem addAxiom_ok {st : ErasureState} {tc : TravCtx} {pc : PureCtx} {ps : PureState}
    (hok : StateOK venv σ st) (hinj : KernameInj σ.decls) (hc : findDecl σ.decls c = some ci)
    (hnew : st.constants[c]? = none)
    (hax : ci.value? (allowOpaque := true) = none ∨ σ.axiomatized ci = true) :
    ∃ st', (addAxiom (m := PureM) c).runPure st tc pc ps = .ok (((), st'), ps) ∧
      st'.constants = st.constants.insert c (toKername c) ∧
      StateOK venv σ st' ∧ LenvExt st.gdecls st'.gdecls := by
  have hd : ErasesDecl venv σ st.gdecls ci ⟨none⟩ := by
    unfold ErasesDecl
    split
    · rfl
    · rename_i hv
      rcases hax with hax | hax
      · rw [hax] at hv
        cases hv
      · exact .inl ⟨hax, rfl⟩
  have hmem : ¬ c ∈ st.constants := by
    rw [Std.HashMap.mem_iff_isSome_getElem?, hnew]
    exact Bool.false_ne_true
  refine ⟨_, ?_, rfl, hok.register hinj hc hnew hd fun b hb => nomatch hb⟩
  simp only [EraseT.runPure, addAxiom, Std.HashMap.contains_iff_mem, StateT.run_bind,
    StateT.run_get, pure_bind, hmem, ↓reduceIte, StateT.run_modify, ReaderT.run_pure,
    StateT.run_pure]
  rfl

/-- `get_constant_kername` at the pure backend: a registered constant's kername is returned
without changing the state; otherwise `visitMutual` runs and the result is what it registered for
the constant. Reference: the `tConst` case of `erase` (`MR E/ErasureFunction.v:989`), which keeps
the kername, and `erase_global_deps` (`MR E/ErasureFunction.v:1602`), which erases the
constant's declaration. -/
theorem get_constant_kername_ok {st st' : ErasureState} {tc : TravCtx} {pc : PureCtx}
    {ps ps' : PureState} {fuel : Nat} {n : Name} {kn : Kername}
    (h : (get_constant_kername (m := PureM) (fuel + 1) n).runPure st tc pc ps =
      .ok ((kn, st'), ps')) :
    ((st.constants[n]? = some kn ∧ st' = st ∧ ps' = ps) ∨
      (st.constants[n]? = none ∧
        (visitMutual (m := PureM) fuel n).runPure st tc pc ps = .ok (((), st'), ps'))) ∧
    ∀ k, st'.constants[n]? = some k → k = kn := by
  rw [EraseT.runPure, get_constant_kername.eq_2] at h
  cases hc : st.constants[n]? with
  | some k =>
    simp only [Std.HashMap.get?_eq_getElem?, bind_pure_comp, StateT.run_bind, StateT.run_get,
      pure_bind, hc, StateT.run_pure, ReaderT.run_pure] at h
    have h' : Except.ok (ε := EraseError) ((k, st), ps) = .ok ((kn, st'), ps') := h
    cases h'
    refine ⟨.inl ⟨rfl, rfl, rfl⟩, fun k' hk => ?_⟩
    rw [hc] at hk
    cases hk
    rfl
  | none =>
    simp only [Std.HashMap.get?_eq_getElem?, bind_pure_comp, StateT.run_bind, StateT.run_get,
      pure_bind, hc, StateT.run_map, map_pure, ReaderT.run_map] at h
    cases hr : (visitMutual (m := PureM) fuel n).runPure st tc pc ps with
    | error err =>
      rw [EraseT.runPure] at hr
      rw [hr] at h
      cases h
    | ok r =>
      obtain ⟨⟨⟨⟩, st''⟩, ps''⟩ := r
      rw [EraseT.runPure] at hr
      rw [hr] at h
      cases h
      refine ⟨.inr ⟨rfl, rfl⟩, fun k hk => ?_⟩
      rw [Std.HashMap.getElem!_eq_get!_getElem?, hk]
      rfl

end

end EraseProof
