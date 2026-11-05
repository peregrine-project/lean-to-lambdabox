import EraseProof.Relation.Deps
import EraseProof.Bridge.ProgEnv

/-!
# The traversal's state invariant

The shipping traversal (`Erasure.visitExpr` and the functions it calls) keeps in its state
(`Erasure.ErasureState`) the constants it has registered, each with its kername, the inductive
types it has registered, each with its λ□ inductive and the argument masks of its constructors,
and the λ□ environment `gdecls` it emits. `StateOK` is the invariant of that state on the pure
path: every registered constant has its own kername, is a declaration of the closure, and its entry
erases its declaration (`ErasesDecl`) with erased dependencies; every registered inductive type has
its λ□ inductive (`IndIdOf`), its block erased (`ErasesInd`) and the masks that keep every field;
every entry of `gdecls` belongs to a registered constant or to the block of a registered inductive
type; every stored body is closed. It is the invariant of MetaRocq's `erase_global_deps`
(`MR E/ErasureFunction.v:1602`): `includes_deps` (`MR E/ErasureFunctionProperties.v:41`) of the
registered constants and inductives.

The registration lemmas: an unregistered constant's kername is fresh (`StateOK.fresh`, from
`KernameInj` and `BlockNamesInj`); registering a constant whose entry is erased keeps `StateOK`
and grows the λ□ environment freshly (`StateOK.register`), which is the `erase_constant_body` step
(`MR E/ErasureFunction.v:1309`) for an axiom (`addAxiom_ok`); `get_constant_kername` returns a
registered constant's kername (`get_constant_kername_ok`), whose `tConst` has erased dependencies
(`StateOK.kername`). Port of `L4 Core/State.lean`, with the inductive types that lean4lean's
fragment did not have.
-/

open Lean Erasure

namespace EraseProof

/-- The λ□ environment `lenv'` extends `lenv` by entries with fresh kernames. Reference:
`extends_prefix` (`MR E/EGlobalEnv.v:189`) with `fresh_global` (`MR E/EGlobalEnv.v:191`). -/
def LenvExt (lenv lenv' : GlobalDeclarations) : Prop :=
  ∃ new, lenv' = new ++ lenv ∧ ∀ kn ∈ new.map (·.1), lenv.find? (·.1 == kn) = none

/-- The argument masks that the pure backend registers for an inductive: every field of every
constructor is kept (`Erasure.PureM`'s `argMask`, `remove_irrel_constr_args = false`). -/
def KeepMasks (σ : EvalEnv) (iv : InductiveVal) (masks : InductiveArgMasks) : Prop :=
  masks.length = iv.ctors.length ∧ ∀ (k : Nat) cn cv, iv.ctors[k]? = some cn →
    findDecl σ.decls cn = some (.ctorInfo cv) → masks[k]? = some (Array.replicate cv.numFields .keep)

/-- The traversal's state invariant over the Metalean environment `E` (table `B`) and the
evaluation environment `σ`: every registered constant `c` has the kername `toKername c`, is a
declaration of `σ`, and its entry erases its declaration (`ErasesDecl`) with erased dependencies;
every registered inductive type `T` has its λ□ inductive, its block erased in the λ□ environment
(`ErasesInd`), and masks that keep every field; every entry of the λ□ environment belongs to a
registered constant or is the block of a registered inductive type; every stored body is closed.
Reference: `includes_deps` with `global_erased_with_deps`
(`MR E/ErasureFunctionProperties.v:41,30`), the invariant of `erase_global_deps`
(`MR E/ErasureFunction.v:1602`); `closed_env` (`MR E/EGlobalEnv.v:181`). -/
structure StateOK {ζ : Metalean.Sigs} (E : Metalean.Env ζ) (B : Binds ζ) (σ : EvalEnv)
    (st : ErasureState) : Prop where
  /-- A registered constant: its kername, its declaration (held by the λ□ environment as a
  constant), its erased entry and dependencies. -/
  registered : ∀ c kn, st.constants[c]? = some kn → kn = toKername c ∧
    ∃ ci cb, findDecl σ.decls c = some ci ∧ EmitsConst ci = true ∧
      lookupConst st.gdecls kn = some cb ∧
      ErasesDecl E B σ ci cb ∧ ∀ b, cb.cst_body = some b → ErasesDeps E B σ st.gdecls b
  /-- A registered inductive type: its λ□ inductive, its erased block, its masks. -/
  inductives : ∀ (T : Name) (r : InductiveId × InductiveArgMasks), st.inductives[T]? = some r → IndIdOf σ T = some r.1 ∧
    ErasesInd E B σ st.gdecls T ∧ ∃ iv, findDecl σ.decls T = some (.inductInfo iv) ∧ KeepMasks σ iv r.2
  /-- Every entry of the λ□ environment belongs to a registered constant or inductive type. -/
  entries : ∀ d ∈ st.gdecls, (∃ c : Name, st.constants[c]? = some d.1) ∨
    ∃ (T : Name) (r : InductiveId × InductiveArgMasks), st.inductives[T]? = some r ∧
      r.1.mutualBlockName = d.1
  /-- Blocks are registered whole: with an inductive type, every type of its block. -/
  whole : ∀ (T : Name) (r : InductiveId × InductiveArgMasks), st.inductives[T]? = some r →
    ∀ iv, findDecl σ.decls T = some (.inductInfo iv) → ∀ n ∈ iv.all, ∃ r', st.inductives[n]? = some r'
  /-- Every stored body is closed. -/
  closed : LenvClosed st.gdecls

namespace StateLemmas

variable {lenv lenv' lenv'' : GlobalDeclarations}

theorem modPath_eq_of_beq : ∀ {a b : ModPath}, (a == b) = true → a = b
  | .MPfile d₁, .MPfile d₂, h => by
    have h' : (d₁ == d₂) = true := h
    rw [beq_iff_eq.1 h']
  | .MPdot m₁ i₁, .MPdot m₂ i₂, h => by
    have h' : (m₁ == m₂ && i₁ == i₂) = true := h
    rw [Bool.and_eq_true] at h'
    rw [modPath_eq_of_beq h'.1, beq_iff_eq.1 h'.2]
  | .MPfile _, .MPdot .., h | .MPdot .., .MPfile _, h => nomatch h

theorem kername_eq_of_beq {a b : Kername} (h : (a == b) = true) : a = b := by
  obtain ⟨m₁, i₁⟩ := a
  obtain ⟨m₂, i₂⟩ := b
  have h' : (m₁ == m₂ && i₁ == i₂) = true := h
  rw [Bool.and_eq_true] at h'
  rw [modPath_eq_of_beq h'.1, beq_iff_eq.1 h'.2]

theorem modPath_beq_self : ∀ a : ModPath, (a == a) = true
  | .MPfile d => show (d == d) = true from beq_self_eq_true d
  | .MPdot m i => show (m == m && i == i) = true by
      rw [modPath_beq_self m, beq_self_eq_true i]; rfl

theorem kername_beq_self (a : Kername) : (a == a) = true := by
  obtain ⟨m, i⟩ := a
  show (m == m && i == i) = true
  rw [modPath_beq_self m, beq_self_eq_true i]; rfl

theorem find?_ext {kn : Kername} {d : Kername × GlobalDecl} (hx : LenvExt lenv lenv')
    (h : lenv.find? (·.1 == kn) = some d) : lenv'.find? (·.1 == kn) = some d := by
  obtain ⟨new, rfl, hfresh⟩ := hx
  have hnew : new.find? (·.1 == kn) = none := by
    rw [List.find?_eq_none]
    intro y hy hyk
    have hnone := hfresh y.1 (List.mem_map.2 ⟨y, hy, rfl⟩)
    rw [kername_eq_of_beq hyk, h] at hnone
    cases hnone
  rw [List.find?_append, hnew, Option.none_or]
  exact h

theorem lookupConst_ext {kn : Kername} {cb : ConstantBody} (hx : LenvExt lenv lenv')
    (h : lookupConst lenv kn = some cb) : lookupConst lenv' kn = some cb := by
  unfold lookupConst at h ⊢
  split at h
  · rename_i d heq
    rw [find?_ext hx heq]
    exact h
  · cases h

theorem lookupInd_ext {ind : InductiveId} {r : MutualInductiveBody × OneInductiveBody}
    (hx : LenvExt lenv lenv') (h : lookupInd lenv ind = some r) : lookupInd lenv' ind = some r := by
  unfold lookupInd at h ⊢
  split at h
  · rename_i d heq
    rw [find?_ext hx heq]
    exact h
  · cases h

variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {σ : EvalEnv}

theorem ErasesInd.ext {T : Name} (hx : LenvExt lenv lenv') (h : ErasesInd E B σ lenv T) :
    ErasesInd E B σ lenv' T := by
  obtain ⟨iv, hiv, hall⟩ := h
  refine ⟨iv, hiv, fun j n hj => ?_⟩
  obtain ⟨iv', mib, ob, h1, hl, h3⟩ := hall j n hj
  exact ⟨iv', mib, ob, h1, lookupInd_ext hx hl, h3⟩

theorem lookupConst_cons_self {kn : Kername} {cb : ConstantBody} :
    lookupConst ((kn, GlobalDecl.constantDecl cb) :: lenv) kn = some cb := by
  simp [lookupConst, List.find?, kername_beq_self]

end StateLemmas

open StateLemmas

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {σ : EvalEnv}

/-- The empty state satisfies the invariant (the traversal starts from it). Reference: the `[]`
case of `erase_global_deps` (`MR E/ErasureFunction.v:1602`). -/
theorem StateOK.empty : StateOK E B σ {} where
  registered c kn h := by simp at h
  inductives T r h := by simp at h
  entries _ h := nomatch h
  whole T r h := by simp at h
  closed _ _ _ h := nomatch h

/-- A registered constant's kername is its own, and its `tConst` has erased dependencies.
Reference: `erase_global_erases_deps` (`MR E/ErasureFunctionProperties.v:172`), its `tConst`
case. -/
theorem StateOK.kername {st : ErasureState} {c : Name} {kn : Kername} (hok : StateOK E B σ st)
    (h : st.constants[c]? = some kn) :
    kn = toKername c ∧ ErasesDeps E B σ st.gdecls (.const kn) := by
  obtain ⟨rfl, _, _, hf, -, hl, hd, hb⟩ := hok.registered c kn h
  exact ⟨rfl, .const hf hl hd hb⟩

/-- An unregistered constant of the closure that the λ□ environment holds as a constant
(`EmitsConst`) has a fresh kername, from `KernameInj` and `BlockNamesInj`. Reference:
`fresh_global` (`MR E/EGlobalEnv.v:191`). -/
theorem StateOK.fresh {st : ErasureState} {c : Name} {ci : ConstantInfo} (hok : StateOK E B σ st)
    (hinj : KernameInj σ.decls) (hbn : BlockNamesInj σ.decls) (hc : findDecl σ.decls c = some ci)
    (hem : EmitsConst ci = true) (hnew : st.constants[c]? = none) :
    st.gdecls.find? (·.1 == toKername c) = none := by
  rw [List.find?_eq_none]
  intro d hd hdk
  have hdk' := (kername_eq_of_beq hdk)
  rcases hok.entries d hd with ⟨c', hc'⟩ | ⟨T, r, hT, hname⟩
  · obtain ⟨hk, _, _, hf, -⟩ := hok.registered c' d.1 hc'
    have heq : c = c' :=
      hinj c c' (by rw [hc]; rfl) (by rw [hf]; rfl) (hdk'.symm.trans hk)
    rw [← heq, hnew] at hc'
    cases hc'
  · obtain ⟨hid, -, iv, hiv, -⟩ := hok.inductives T r hT
    unfold IndIdOf at hid
    rw [hiv] at hid
    obtain ⟨j, -, hj⟩ := Option.map_eq_some_iff.1 hid
    have hb : r.1.mutualBlockName = blockKername iv := by rw [← hj]
    have hmem : ci ∈ σ.decls ∧ ci.name = c := findDecl_eq_some hc
    refine (hbn iv iv ⟨_, (findDecl_eq_some hiv).1, rfl⟩ ⟨_, (findDecl_eq_some hiv).1, rfl⟩).2 ci
      hmem.1 hem ?_
    rw [hmem.2, ← hdk', ← hname, hb]
    rfl

end

theorem StateLemmas.lookupConst_cons {k kn : Kername} {d : GlobalDecl} {l : GlobalDeclarations}
    {cb : ConstantBody} (h : lookupConst ((k, d) :: l) kn = some cb) :
    (k = kn ∧ d = .constantDecl cb) ∨ (k ≠ kn ∧ lookupConst l kn = some cb) := by
  unfold lookupConst at h
  rw [List.find?_cons] at h
  by_cases hk : (k == kn) = true
  · rw [hk] at h
    cases d with
    | constantDecl cb' => cases h; exact .inl ⟨kername_eq_of_beq hk, rfl⟩
    | inductiveDecl _ => cases h
  · rw [Bool.not_eq_true] at hk
    rw [hk] at h
    refine .inr ⟨fun he => ?_, h⟩
    rw [he, kername_beq_self] at hk
    cases hk

section
variable {ζ : Metalean.Sigs} {E : Metalean.Env ζ} {B : Binds ζ} {σ : EvalEnv}

/-- Registering an unregistered constant of the closure, held by the λ□ environment as a constant,
with an entry that erases its declaration, with erased dependencies and a closed body in the
environment before the entry, keeps the invariant; the λ□ environment grows by the fresh entry. This
is the state update of `visitMutual` and `addAxiom`. Reference: the `ConstantDecl` step of
`erase_global_deps` (`MR E/ErasureFunction.v:1602`), with `erases_deps_cons`
(`MR E/EDeps.v:492`). -/
theorem StateOK.register {st : ErasureState} {c : Name} {ci : ConstantInfo} {cb : ConstantBody}
    (hok : StateOK E B σ st) (hinj : KernameInj σ.decls) (hbn : BlockNamesInj σ.decls)
    (hc : findDecl σ.decls c = some ci) (hem : EmitsConst ci = true)
    (hnew : st.constants[c]? = none) (hd : ErasesDecl E B σ ci cb)
    (hb : ∀ b, cb.cst_body = some b →
      ErasesDeps E B σ st.gdecls b ∧ closedn 0 b = true ∧ ∀ x, hasFVar x b = false) :
    StateOK E B σ
      { st with
        constants := st.constants.insert c (toKername c)
        gdecls := (toKername c, .constantDecl cb) :: st.gdecls } ∧
    LenvExt st.gdecls ((toKername c, .constantDecl cb) :: st.gdecls) := by
  have hx : LenvExt st.gdecls ((toKername c, .constantDecl cb) :: st.gdecls) := by
    refine ⟨[(toKername c, .constantDecl cb)], rfl, fun kn hkn => ?_⟩
    rw [List.map_cons, List.map_nil, List.mem_singleton] at hkn
    rw [hkn]
    exact hok.fresh hinj hbn hc hem hnew
  have hins : ∀ c' kn, (st.constants.insert c (toKername c))[c']? = some kn →
      (c = c' ∧ kn = toKername c) ∨ st.constants[c']? = some kn := by
    intro c' kn h
    rw [Std.HashMap.getElem?_insert] at h
    split at h
    · rename_i hcc
      cases h
      exact .inl ⟨beq_iff_eq.1 hcc, rfl⟩
    · exact .inr h
  refine ⟨⟨fun c' kn h => ?_, fun T r h => ?_, fun d hd => ?_, hok.whole,
    fun kn cb' b hl hb' => ?_⟩, hx⟩
  · rcases hins c' kn h with ⟨rfl, rfl⟩ | h
    · exact ⟨rfl, ci, cb, hc, hem, lookupConst_cons_self, hd,
        fun b h => (hb b h).1.ext hx⟩
    · obtain ⟨hk, ci', cb', hf, hem', hl, hd', hb''⟩ := hok.registered c' kn h
      exact ⟨hk, ci', cb', hf, hem', lookupConst_ext hx hl, hd', fun b h => (hb'' b h).ext hx⟩
  · obtain ⟨h1, h2, h3⟩ := hok.inductives T r h
    exact ⟨h1, StateLemmas.ErasesInd.ext hx h2, h3⟩
  · rcases List.mem_cons.1 hd with rfl | hd
    · exact .inl ⟨c, Std.HashMap.getElem?_insert_self⟩
    · rcases hok.entries d hd with ⟨c', hc'⟩ | h
      · refine .inl ⟨c', ?_⟩
        show (st.constants.insert c (toKername c))[c']? = some d.1
        rw [Std.HashMap.getElem?_insert]
        split
        · rename_i hcc
          rw [← beq_iff_eq.1 hcc, hnew] at hc'
          cases hc'
        · exact hc'
      · exact .inr h
  · rcases StateLemmas.lookupConst_cons hl with ⟨rfl, hcd⟩ | ⟨-, hl'⟩
    · cases hcd
      exact (hb b hb').2
    · exact hok.closed kn cb' b hl' hb'

/-- `addAxiom` at the pure backend, on an unregistered constant of the closure that has no value or
is remapped and that the λ□ environment holds as a constant: it registers the constant with an
empty body, and the invariant holds after it; the λ□ environment grows by the fresh entry.
Reference: the `None` case of `erase_constant_body` (`MR E/ErasureFunction.v:1309`); the remapped
case of `erases_constant_body` (DV-12). -/
theorem addAxiom_ok {st : ErasureState} {tc : TravCtx} {pc : PureCtx} {ps : PureState} {c : Name}
    {ci : ConstantInfo} (hok : StateOK E B σ st) (hinj : KernameInj σ.decls)
    (hbn : BlockNamesInj σ.decls) (hc : findDecl σ.decls c = some ci) (hem : EmitsConst ci = true)
    (hnew : st.constants[c]? = none)
    (hax : ci.value? (allowOpaque := true) = none ∨ σ.axiomatized ci = true) :
    ∃ st', (addAxiom (m := PureM) c).runPure st tc pc ps = .ok (((), st'), ps) ∧
      st'.constants = st.constants.insert c (toKername c) ∧
      StateOK E B σ st' ∧ LenvExt st.gdecls st'.gdecls := by
  have hd : ErasesDecl E B σ ci ⟨none⟩ := by
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
  refine ⟨_, ?_, rfl, hok.register hinj hbn hc hem hnew hd fun b hb => nomatch hb⟩
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
  rw [get_constant_kername.eq_2] at h
  cases hc : st.constants[n]? with
  | some k =>
    have e : (get_constant_kername (m := PureM) (fuel + 1) n).runPure st tc pc ps =
        .ok ((k, st), ps) := by
      rw [get_constant_kername.eq_2]
      show (match st.constants.get? n with
        | some kn => (pure kn : EraseT PureM Kername)
        | _ => _).runPure st tc pc ps = _
      rw [Std.HashMap.get?_eq_getElem?, hc]
      rfl
    rw [← get_constant_kername.eq_2, e] at h
    cases h
    refine ⟨.inl ⟨rfl, rfl, rfl⟩, fun k' hk => ?_⟩
    rw [hc] at hk
    cases hk
    rfl
  | none =>
    simp only [EraseT.runPure, StateT.run_bind, StateT.run_get, pure_bind,
      Std.HashMap.get?_eq_getElem?, hc, ReaderT.run_bind, StateT.run_bind] at h
    simp only [EraseT.runPure, reduceCtorEq, false_and, true_and, false_or]
    rcases hr : ((((visitMutual (m := PureM) fuel n).run st).run tc).run pc).run ps with
      err | ⟨⟨⟨⟩, st''⟩, ps''⟩
    · rw [hr] at h; cases h
    · rw [hr] at h
      simp only [bind, Except.bind] at h
      cases hk : st''.constants[n]? with
      | none =>
        rw [hk] at h
        cases h
      | some k =>
        rw [hk] at h
        cases h
        exact ⟨rfl, fun k' hk' => by rw [hk] at hk'; cases hk'; rfl⟩
end

end EraseProof
