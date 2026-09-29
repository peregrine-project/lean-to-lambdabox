import EraseProof.Env

/-!
# Bridge tests: `TrS` and `ProgEnv` against lean4lean's `TrExprS` and `TrEnv'`

Tests, off the path of the final theorem: the translation `TrS` is a sub-relation of lean4lean's
`TrExprS` (DV-2), and a program environment `ProgEnv` is an instance of lean4lean's `TrEnv'` at
safety `.unsafe` (DV-3). Both lean4lean relations mention `TrProj := sorry`
(`Lean4Lean/Verify/Typing/Expr.lean:68`), so these tests carry `sorryAx` through it.

The constant map of `ProgEnv.toTrEnv'` is built by insertions into the stage-1 hash map of an
`SMap` (`Std.HashMap`), so no lemma about `PersistentHashMap` is needed; the lemmas this takes are
in namespace `EraseProof.Test.Bridge`.
-/

open Lean Lean4Lean

namespace EraseProof.Test

section
variable {venv : VEnv} {P : List ConstantInfo}

/-- Test (proved): the bridge `TrS` is a sub-relation of lean4lean's `TrExprS`
(`l4l Verify/Typing/Expr.lean:75`), DV-2. Reference: none in MetaRocq. -/
theorem TrS.toTrExprS (h : TrS venv Us Δ e e') : TrExprS venv Us Δ e e' := by
  induction h with
  | bvar h => exact .bvar h
  | fvar h => exact .fvar h
  | sort h => exact .sort h
  | const h1 h2 h3 => exact .const h1 h2 h3
  | app h1 h2 _ _ ih1 ih2 => exact .app h1 h2 ih1 ih2
  | lam h1 _ _ ih1 ih2 => exact .lam h1 ih1 ih2
  | forallE h1 h2 _ _ ih1 ih2 => exact .forallE h1 h2 ih1 ih2
  | letE h1 _ _ _ ih1 ih2 ih3 => exact .letE h1 ih1 ih2 ih3
  | mdata _ ih => exact .mdata ih

namespace Bridge

/-- Every declaration is visible at safety `.unsafe`. -/
theorem unsafe_le (s : DefinitionSafety) : DefinitionSafety.«unsafe» ≤ s := by
  cases s <;> decide

/-- `TrConst` gives lean4lean's `TrConstant` (`l4l Verify/Environment/Basic.lean:18`) at safety
`.unsafe`. -/
theorem TrConst.toTrConstant (h : TrConst venv ci ci') : TrConstant .«unsafe» venv ci ci' :=
  ⟨unsafe_le _, h.1, TrS.toTrExprS h.2⟩

/-- `TrDef` with the value translated in the same environment gives lean4lean's `TrDefVal`
(`l4l Verify/Environment/Basic.lean:27`) at safety `.unsafe`. -/
theorem TrDef.toTrDefVal (h : TrDef venv venv ci ci') : TrDefVal .«unsafe» venv ci ci' :=
  ⟨⟨TrConst.toTrConstant h.1, h.2.1⟩, TrS.toTrExprS h.2.2⟩

/-- A name absent from an environment is absent from every smaller one. -/
theorem constants_none_of_le {venv' : VEnv} (hle : venv ≤ venv') (h : venv'.constants n = none) :
    venv.constants n = none := by
  cases h' : venv.constants n with
  | none => rfl
  | some a => rw [hle.constants h'] at h; cases h

/-- `VEnv.addConst` adds only fresh names (`l4l Theory/VEnv.lean:27`). -/
theorem fresh_of_addConst {venv' : VEnv} (h : venv.addConst n ci = some venv') :
    venv.constants n = none := by
  unfold VEnv.addConst at h
  split at h
  · cases h
  · assumption

/-- `VEnv.addConsts` adds only fresh names. -/
theorem addConsts_fresh :
    ∀ {env env' : VEnv} {cis : List VDefVal}, env.addConsts cis = some env' →
      ∀ ci ∈ cis, env.constants ci.name = none
  | _, _, [], _, _, hc => nomatch hc
  | _, _, _ :: _, e, ci, hc => by
    simp [VEnv.addConsts, Option.bind_eq_some_iff] at e
    obtain ⟨_, h1, h2⟩ := e
    cases hc with
    | head => exact fresh_of_addConst h1
    | tail _ hc => exact constants_none_of_le (VEnv.addConst_le h1) (addConsts_fresh h2 ci hc)

/-- Inserting a block of definitions into a hash map leaves the other names unchanged. -/
theorem foldl_insert_of_forall_ne {vs : List DefinitionVal} (h : ∀ v ∈ vs, v.name ≠ n)
    (m : Std.HashMap Name ConstantInfo) :
    (vs.foldl (fun m v => m.insert v.name (.defnInfo v)) m)[n]? = m[n]? := by
  induction vs generalizing m with
  | nil => rfl
  | cons v vs ih =>
    rw [List.foldl_cons, ih (fun w hw => h w (.tail _ hw)), Std.HashMap.getElem?_insert]
    simp [h v (.head _)]

/-- Inserting a block of definitions with distinct names into a hash map maps each name to its
definition. -/
theorem foldl_insert_of_mem {vs : List DefinitionVal} (hnd : (vs.map (·.name)).Nodup)
    (hv : v ∈ vs) (m : Std.HashMap Name ConstantInfo) :
    (vs.foldl (fun m v => m.insert v.name (.defnInfo v)) m)[v.name]? = some (.defnInfo v) := by
  induction vs generalizing m with
  | nil => cases hv
  | cons w vs ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.foldl_cons]
    cases hv with
    | head =>
      rw [foldl_insert_of_forall_ne (fun u hu he => hnd.1 (List.mem_map.2 ⟨u, hu, he⟩)),
        Std.HashMap.getElem?_insert_self]
    | tail _ hv => exact ih hnd.2 hv _

/-- lean4lean's `insertDefs` (`l4l Verify/Environment/Basic.lean:115`) on a stage-1 `SMap` inserts
into its hash map. -/
theorem insertDefs_hashMap (m : Std.HashMap Name ConstantInfo) (vs : List DefinitionVal) :
    insertDefs ({ map₁ := m } : SMap Name ConstantInfo) vs =
      { map₁ := vs.foldl (fun m v => m.insert v.name (.defnInfo v)) m } := by
  induction vs generalizing m with
  | nil => rfl
  | cons v vs ih => exact ih _

/-- One declaration step of `ProgEnv.toTrEnv'_hashMap`: inserting `ci` under the name `n` that the
environment step `venv ≤ venv'` adds keeps every earlier declaration and gives absent names no
entry. -/
theorem insert_step {cs : List ConstantInfo} {venv' : VEnv} {m : Std.HashMap Name ConstantInfo}
    (hP : ∀ d ∈ cs, m[d.name]? = some d) (hfr : ∀ k, venv.constants k = none → m[k]? = none)
    (hn : ci.name = n) (hle : venv ≤ venv') (hself : venv'.constants n = some c)
    (hfresh : m[n]? = none) :
    (∀ d ∈ ci :: cs, (m.insert n ci)[d.name]? = some d) ∧
      ∀ k, venv'.constants k = none → (m.insert n ci)[k]? = none := by
  refine ⟨fun d hd => ?_, fun k hk => ?_⟩
  · cases hd with
    | head => rw [hn, Std.HashMap.getElem?_insert_self]
    | tail _ hd =>
      have hne : n ≠ d.name := fun he => by rw [he, hP d hd] at hfresh; cases hfresh
      rw [Std.HashMap.getElem?_insert]
      simp [hne, hP d hd]
  · have hne : n ≠ k := fun he => by rw [he, hk] at hself; cases hself
    rw [Std.HashMap.getElem?_insert]
    simp [hne, hfr k (constants_none_of_le hle hk)]

/-- `ProgEnv.toTrEnv'` with the constant map a stage-1 `SMap`: its hash map has every
declaration of `P` under its name and no entry for a name absent from the model. -/
theorem ProgEnv.toTrEnv'_hashMap (h : ProgEnv P venv) :
    ∃ m : Std.HashMap Name ConstantInfo,
      TrEnv' .«unsafe» ({ map₁ := m } : SMap Name ConstantInfo) false venv ∧
      (∀ ci ∈ P, m[ci.name]? = some ci) ∧ ∀ n, venv.constants n = none → m[n]? = none := by
  induction h with
  | nil => exact ⟨∅, .empty, (fun _ h => nomatch h), fun _ _ => Std.HashMap.getElem?_empty⟩
  | @«axiom» _ _ v _ _ _ htr hwf hadd ih =>
    obtain ⟨m, hT, hP, hfr⟩ := ih
    have hfresh := hfr _ (fresh_of_addConst hadd)
    exact ⟨m.insert v.name (.axiomInfo v),
      .«axiom» (C := { map₁ := m }) (TrConst.toTrConstant htr) hfresh hwf hadd hT,
      insert_step hP hfr rfl (VEnv.addConst_le hadd) (VEnv.addConst_self hadd) hfresh⟩
  | @defn _ _ v _ _ _ _ htr hwf hadd ih =>
    obtain ⟨m, hT, hP, hfr⟩ := ih
    have hfresh := hfr _ (fresh_of_addConst hadd)
    exact ⟨m.insert v.name (.defnInfo v),
      .defn (C := { map₁ := m }) (TrDef.toTrDefVal htr) hfresh hwf hadd hT,
      insert_step hP hfr rfl ((VEnv.addConst_le hadd).trans VEnv.addDefEq_le)
        (VEnv.addDefEq_le.constants (VEnv.addConst_self hadd)) hfresh⟩
  | @thm _ _ v _ _ _ _ htr hwf hty hadd ih =>
    obtain ⟨m, hT, hP, hfr⟩ := ih
    have hfresh := hfr _ (fresh_of_addConst hadd)
    exact ⟨m.insert v.name (.thmInfo v),
      .thm (C := { map₁ := m }) (TrDef.toTrDefVal htr) hfresh hwf hty hadd hT,
      insert_step hP hfr rfl (VEnv.addConst_le hadd) (VEnv.addConst_self hadd) hfresh⟩
  | @«opaque» _ _ v _ _ _ _ htr hwf hadd ih =>
    obtain ⟨m, hT, hP, hfr⟩ := ih
    have hfresh := hfr _ (fresh_of_addConst hadd)
    exact ⟨m.insert v.name (.opaqueInfo v),
      .«opaque» (C := { map₁ := m }) (TrDef.toTrDefVal htr) hfresh hwf hadd hT,
      insert_step hP hfr rfl (VEnv.addConst_le hadd) (VEnv.addConst_self hadd) hfresh⟩
  | @block _ _ venv' vs cis' _ hnd _ htr hwf0 hadd hwf ih =>
    obtain ⟨m, hT, hP, hfr⟩ := ih
    have hname : ∀ v ∈ vs, ∃ ci' ∈ cis', v.name = ci'.name := fun v hv =>
      have ⟨ci', hci', h⟩ := forall₂_exists_of_mem_left htr hv
      ⟨ci', hci', h.2.1⟩
    have hfresh : ∀ v ∈ vs, m[v.name]? = none := fun v hv =>
      have ⟨ci', hci', he⟩ := hname v hv
      hfr _ (he ▸ addConsts_fresh hadd ci' hci')
    refine ⟨vs.foldl (fun m v => m.insert v.name (.defnInfo v)) m, ?_, fun d hd => ?_,
      fun k hk => ?_⟩
    · rw [← insertDefs_hashMap]
      exact .mutualDef (C := { map₁ := m })
        (htr.imp fun _ _ h => ⟨⟨TrConst.toTrConstant h.1, h.2.1⟩, TrS.toTrExprS h.2.2⟩)
        hnd hfresh hwf0 hadd hwf hT
    · rcases List.mem_append.1 hd with hd | hd
      · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hd
        exact foldl_insert_of_mem hnd (List.mem_reverse.1 hv) m
      · rw [foldl_insert_of_forall_ne fun v hv he => by
          have := hfresh v hv; rw [he, hP d hd] at this; cases this]
        exact hP d hd
    · have hk' : venv'.constants k = none := constants_none_of_le VEnv.addDefEqs_le hk
      rw [foldl_insert_of_forall_ne fun v hv he => by
        have ⟨ci', hci', hn⟩ := hname v hv
        rw [← he, hn, VEnv.addConsts_constants hadd ci' hci'] at hk'; cases hk']
      exact hfr k (constants_none_of_le (VEnv.addConsts_le hadd) hk')

end Bridge

/-- Test: `ProgEnv` is an instance of lean4lean's `TrEnv'` at `.unsafe`
(`l4l Verify/Environment/Basic.lean:128`), DV-3. Reference: none in MetaRocq. -/
theorem ProgEnv.toTrEnv' (h : ProgEnv P venv) :
    ∃ C : ConstMap, TrEnv' .«unsafe» C false venv ∧ ∀ ci ∈ P, C.find? ci.name = some ci :=
  have ⟨m, hT, hP, _⟩ := Bridge.ProgEnv.toTrEnv'_hashMap h
  ⟨{ map₁ := m }, hT, hP⟩

end

end EraseProof.Test
