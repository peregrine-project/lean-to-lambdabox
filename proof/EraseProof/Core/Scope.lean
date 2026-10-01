import EraseProof.Core.Collect

/-!
# The scope of the final theorem and the routing of `#erase`

`InScope view e` says that `e` is well typed, through `TrS`, in the model of some program `P`
(`ProgEnv`) that the view agrees with (`ViewAgrees`). On such an input the shipping
`Erasure.collectDeps view e` never answers `outOfFragment`, so `#erase` takes the verified path
(`collectDeps_not_outOfFragment`), and the closure it computes is a sub-environment of `P`
(`collectDeps_sub`). Both follow from one invariant of `closure`: the names of its work list are
names of `P`, and its accumulator is a sub-environment of `P`. A name of `P` is found by the view
under its own name, and the dependencies of a member of `P` (`declDeps`) are again names of `P`,
because its type and value translate in a model whose constants are names of `P`.
-/

open Lean Lean4Lean Erasure

namespace EraseProof

/-- The view `#erase` reads agrees with `P` on `P`'s names. Reference:
`Σ ∼_ext X` (`abstract_env_ext_rel`, hypothesis of `MR E/ErasureFunctionProperties.v:657
erase_correct`). -/
def ViewAgrees (view : EnvView) (P : List ConstantInfo) : Prop :=
  ∀ ci ∈ P, view.find? ci.name = some ci

/-- The inputs the final theorem covers: `e` is well typed in master's model of
some inductive-free, well-formed environment that the view agrees with. Reference: the
hypotheses `wf_ext Σ`, `Σ ∼_ext X`, `welltyped Σ [] t` of `MR E/ErasureFunctionProperties.v:657
erase_correct`. -/
def InScope (view : EnvView) (e : Expr) : Prop :=
  ∃ P venv Us e', ProgEnv P venv ∧ ViewAgrees view P ∧ TrS venv Us [] e e'

section
variable {venv : VEnv} {P decls : List ConstantInfo}

/-! ## The fragment scan on translated terms -/

/-- `exprConsts` succeeds on a translated term without free variables and level metavariables,
and lists constants of the model. Reference: `term_global_deps` (`MR E/EAstUtils.v:406`), on the
source side; a typed constant is declared (rule `type_Const`, `MR P/PCUICTyping.v:232`). -/
theorem exprConsts_of_trS_fvarsIn (h : TrS venv Us Δ e e') (hfv : FVarsIn (fun _ => False) e) :
    ∃ cs, exprConsts e = .ok cs ∧ ∀ c ∈ cs, (venv.constants c).isSome := by
  induction h with
  | bvar => exact ⟨[], rfl, nofun⟩
  | fvar => exact hfv.elim
  | sort =>
    simp only [FVarsIn] at hfv
    rw [exprConsts.eq_4, if_neg (by simp [hfv])]
    exact ⟨[], rfl, nofun⟩
  | const h1 =>
    simp only [FVarsIn] at hfv
    rw [exprConsts.eq_5, if_neg (by simpa [List.any_eq_true] using hfv)]
    refine ⟨[_], rfl, fun d hd => ?_⟩
    rw [List.mem_singleton.mp hd, h1]
    rfl
  | app _ _ _ _ ih1 ih2 =>
    obtain ⟨xs, h1, hx⟩ := ih1 hfv.1
    obtain ⟨ys, h2, hy⟩ := ih2 hfv.2
    rw [exprConsts.eq_6, h1, h2]
    exact ⟨xs ++ ys, rfl, fun c hc => (List.mem_append.mp hc).elim (hx c) (hy c)⟩
  | lam _ _ _ ih1 ih2 | forallE _ _ _ _ ih1 ih2 =>
    obtain ⟨xs, h1, hx⟩ := ih1 hfv.1
    obtain ⟨ys, h2, hy⟩ := ih2 hfv.2
    first | rw [exprConsts.eq_7, h1, h2] | rw [exprConsts.eq_8, h1, h2]
    exact ⟨xs ++ ys, rfl, fun c hc => (List.mem_append.mp hc).elim (hx c) (hy c)⟩
  | letE _ _ _ _ ih1 ih2 ih3 =>
    obtain ⟨xs, h1, hx⟩ := ih1 hfv.1
    obtain ⟨ys, h2, hy⟩ := ih2 hfv.2.1
    obtain ⟨zs, h3, hz⟩ := ih3 hfv.2.2
    rw [exprConsts.eq_9, h1, h2, h3]
    refine ⟨xs ++ ys ++ zs, rfl, fun c hc => ?_⟩
    rcases List.mem_append.mp hc with hc | hc
    · exact (List.mem_append.mp hc).elim (hx c) (hy c)
    · exact hz c hc
  | mdata _ ih =>
    rw [exprConsts.eq_11]
    exact ih hfv

/-- `exprConsts` succeeds on a term translated in the empty context, and lists constants of the
model. Reference: as `exprConsts_of_trS_fvarsIn`; closed well-typed terms (`subject_closed`,
`MR pcuic/theories/Typing/PCUICClosedTyp.v:351`). -/
theorem exprConsts_of_trS (h : TrS venv Us [] e e') :
    ∃ cs, exprConsts e = .ok cs ∧ ∀ c ∈ cs, (venv.constants c).isSome :=
  exprConsts_of_trS_fvarsIn h (h.fvarsIn.mono fun _ h => by simp [VLCtx.fvars] at h)

/-! ## The constants of a program's model -/

/-- Adding defining equations adds no constant. Reference: none (lean4lean `VEnv.addDefEqs`). -/
theorem addDefEqs_constants : ∀ {venv : VEnv} {cis : List VDefVal},
    (venv.addDefEqs cis).constants = venv.constants
  | _, [] => rfl
  | venv, ci :: _ => addDefEqs_constants (venv := venv.addDefEq ci.toDefEq)

/-- A constant of a block's environment is a constant of the environment before the block or a
member of the block. Reference: none (lean4lean `VEnv.addConsts`). -/
theorem addConsts_constants_mem {venv venv' : VEnv} : ∀ {cis : List VDefVal},
    venv.addConsts cis = some venv' → (venv'.constants c).isSome →
    (venv.constants c).isSome ∨ c ∈ cis.map (·.name)
  | [], h, hc => by cases h; exact .inl hc
  | ci :: cis, h, hc => by
    simp only [VEnv.addConsts, List.foldlM_cons, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at h
    obtain ⟨venv₁, h1, h2⟩ := h
    rcases addConsts_constants_mem h2 hc with hc | hc
    · rw [VEnv.addConst_constants_eq h1] at hc
      dsimp only at hc
      split at hc
      · rename_i hn
        subst hn
        exact .inr (List.mem_map_of_mem (.head _))
      · exact .inl hc
    · exact .inr (List.mem_cons_of_mem _ hc)

/-- A block's model constants and its members have the same names. Reference: none. -/
theorem forall₂_trDef_names {venv venv' : VEnv} {vs : List DefinitionVal} {cis' : List VDefVal}
    (h : List.Forall₂ (fun v ci' => TrDef venv venv' (.defnInfo v) ci') vs cis') :
    cis'.map (·.name) = vs.map (·.name) := by
  induction h with
  | nil => rfl
  | cons hr _ ih =>
    simp only [List.map_cons, ih, List.cons.injEq, and_true]
    exact hr.2.1.symm

/-- A name of a block member is a name of the program that adds the block. Reference: none. -/
theorem mem_block_names {vs : List DefinitionVal} {cs : List ConstantInfo} {c : Name}
    (h : c ∈ vs.map (·.name)) : c ∈ (vs.reverse.map ConstantInfo.defnInfo ++ cs).map (·.name) := by
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp h
  exact List.mem_map.mpr ⟨.defnInfo v, List.mem_append_left _
    (List.mem_map.mpr ⟨v, List.mem_reverse.mpr hv, rfl⟩), rfl⟩

/-- Every constant of a program's model is the name of a declaration of the program. Reference:
none (`lookup_env` of a declared constant, `MR common/theories/Environment.v:483`). -/
theorem ProgEnv.constants_mem (h : ProgEnv P venv) (hc : (venv.constants c).isSome) :
    c ∈ P.map (·.name) := by
  induction h with
  | nil => simp [VEnv.empty] at hc
  | «axiom» _ _ _ h2 ih | thm _ _ _ _ _ h2 ih | «opaque» _ _ _ _ h2 ih
  | defn _ _ _ _ h2 ih =>
    try dsimp only [VEnv.addDefEq] at hc
    rw [VEnv.addConst_constants_eq h2] at hc
    dsimp only at hc
    split at hc
    · rename_i hn
      subst hn
      exact List.mem_map_of_mem (.head _)
    · exact List.mem_cons_of_mem _ (ih hc)
  | block _ _ _ htr _ h2 _ ih =>
    rw [addDefEqs_constants] at hc
    rcases addConsts_constants_mem h2 hc with hc | hc
    · rw [List.map_append]
      exact List.mem_append_right _ (ih hc)
    · exact mem_block_names (forall₂_trDef_names htr ▸ hc)

/-! ## The dependencies of a program's declarations -/

/-- `declDeps` succeeds on every declaration of a program, and its dependencies are names of the
program. Reference: the closure property of `MR E/ErasureFunction.v:1602 erase_global_deps` on a
well-formed environment (`wf_ext Σ`, MC §3.6). -/
theorem ProgEnv.declDeps_mem (h : ProgEnv P venv) (hci : ci ∈ P) :
    ∃ ds, declDeps ci = .ok ds ∧ ∀ n ∈ ds, n ∈ P.map (·.name) := by
  induction h generalizing ci with
  | nil => nomatch hci
  | «axiom» hP htr _ _ ih =>
    rcases List.mem_cons.mp hci with rfl | hci
    · obtain ⟨xs, hx, hxin⟩ := exprConsts_of_trS htr.2
      exact ⟨xs, hx, fun n hn => List.mem_cons_of_mem _ (hP.constants_mem (hxin n hn))⟩
    · obtain ⟨ds, hds, hin⟩ := ih hci
      exact ⟨ds, hds, fun n hn => List.mem_cons_of_mem _ (hin n hn)⟩
  | @defn _ _ v _ _ hP hall htr _ _ ih | @thm _ _ v _ _ hP hall htr _ _ _ ih
  | @«opaque» _ _ v _ _ hP hall htr _ _ ih =>
    rcases List.mem_cons.mp hci with rfl | hci
    · obtain ⟨xs, hx, hxin⟩ := exprConsts_of_trS htr.1.2
      obtain ⟨ys, hy, hyin⟩ := exprConsts_of_trS htr.2.2
      have hx' : exprConsts v.type = .ok xs := hx
      have hy' : exprConsts v.value = .ok ys := hy
      refine ⟨xs ++ ys ++ [v.name], ?_, fun n hn => ?_⟩
      · first | rw [declDeps.eq_2] | rw [declDeps.eq_3] | rw [declDeps.eq_4]
        rw [hx', hy', hall]
        rfl
      · rcases List.mem_append.mp hn with hn | hn
        · rcases List.mem_append.mp hn with hn | hn
          · exact List.mem_cons_of_mem _ (hP.constants_mem (hxin n hn))
          · exact List.mem_cons_of_mem _ (hP.constants_mem (hyin n hn))
        · rw [List.mem_singleton.mp hn]
          exact List.mem_cons_self ..
    · obtain ⟨ds, hds, hin⟩ := ih hci
      exact ⟨ds, hds, fun n hn => List.mem_cons_of_mem _ (hin n hn)⟩
  | @block cs venv venv' vs cis' hP _ hall htr _ h2 _ ih =>
    rcases List.mem_append.mp hci with hci | hci
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hci
      have hv := List.mem_reverse.mp hv
      obtain ⟨ci', -, htr'⟩ := forall₂_exists_of_mem_left htr hv
      obtain ⟨xs, hx, hxin⟩ := exprConsts_of_trS htr'.1.2
      obtain ⟨ys, hy, hyin⟩ := exprConsts_of_trS htr'.2.2
      have hold : ∀ n, (venv.constants n).isSome →
          n ∈ (vs.reverse.map ConstantInfo.defnInfo ++ cs).map (·.name) := fun n hn => by
        rw [List.map_append]
        exact List.mem_append_right _ (hP.constants_mem hn)
      have hx' : exprConsts v.type = .ok xs := hx
      have hy' : exprConsts v.value = .ok ys := hy
      refine ⟨xs ++ ys ++ vs.map (·.name), ?_, fun n hn => ?_⟩
      · rw [declDeps.eq_2, hx', hy', hall v hv]
        rfl
      · rcases List.mem_append.mp hn with hn | hn
        · rcases List.mem_append.mp hn with hn | hn
          · exact hold n (hxin n hn)
          · rcases addConsts_constants_mem h2 (hyin n hn) with hn | hn
            · exact hold n hn
            · exact mem_block_names (forall₂_trDef_names htr ▸ hn)
        · exact mem_block_names hn
    · obtain ⟨ds, hds, hin⟩ := ih hci
      refine ⟨ds, hds, fun n hn => ?_⟩
      rw [List.map_append]
      exact List.mem_append_right _ (hin n hn)

/-! ## The closure -/

/-- On a view that agrees with a program, a run of `closure` whose work list holds names of the
program and whose accumulator is a sub-environment of it never leaves the fragment and returns a
sub-environment of the program. Reference: `erase_global_deps` (`MR E/ErasureFunction.v:1602`)
keeps declarations of `Σ`. -/
theorem closure_sub {view : EnvView} (hview : ViewAgrees view P)
    (hdeps : ∀ ci ∈ P, ∃ ds, declDeps ci = .ok ds ∧ ∀ n ∈ ds, n ∈ P.map (·.name)) :
    ∀ {f : Nat} {todo : List Name} {acc : List ConstantInfo},
      (∀ n ∈ todo, n ∈ P.map (·.name)) → SubEnv acc P →
      (∀ res, closure view f todo acc = .ok res → SubEnv res P) ∧
        ∀ w, closure view f todo acc ≠ .error (.outOfFragment w)
  | 0, _, _, _, _ => by
    rw [closure.eq_1]
    exact ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩
  | _+1, [], acc, _, hacc => by
    rw [closure.eq_2]
    exact ⟨fun _ h => (by cases h; exact hacc), fun _ h => (by cases h)⟩
  | f+1, n :: todo, acc, htodo, hacc => by
    rw [closure.eq_3]
    split
    · exact closure_sub hview hdeps (fun m hm => htodo m (List.mem_cons_of_mem _ hm)) hacc
    · have hn := findDecl_isSome_iff.mpr (htodo n (List.mem_cons_self ..))
      obtain ⟨ci, hfd⟩ := Option.isSome_iff_exists.mp hn
      have hname : ci.name = n :=
        beq_iff_eq.mp (List.find?_some (p := fun x : ConstantInfo => x.name == n) hfd)
      have hmem : ci ∈ P := List.mem_of_find?_eq_some hfd
      have hfind : view.find? n = some ci := hname ▸ hview ci hmem
      obtain ⟨ds, hds, hdsP⟩ := hdeps ci hmem
      rw [hfind]
      simp only [hname, bne_self_eq_false, Bool.false_eq_true, ite_false, hds]
      refine closure_sub hview hdeps (fun m hm => ?_) (fun cj hcj => ?_)
      · rcases List.mem_append.mp hm with hm | hm
        · exact hdsP m hm
        · exact htodo m (List.mem_cons_of_mem _ hm)
      · rcases List.mem_cons.mp hcj with rfl | hcj
        · rw [hname]; exact hfd
        · exact hacc cj hcj

/-- On an in-scope input, `collectDeps` never leaves the fragment and returns a sub-environment of
the program. Reference: none directly (DV-3). -/
theorem collectDeps_scope {view : EnvView} (henv : ProgEnv P venv) (hview : ViewAgrees view P)
    (he : TrS venv Us [] e e') :
    (∀ decls, collectDeps view e = .ok decls → SubEnv decls P) ∧
      ∀ w, collectDeps view e ≠ .error (.outOfFragment w) := by
  obtain ⟨cs, hcs, hcsP⟩ := exprConsts_of_trS he
  have hcl := closure_sub hview (fun _ hci => henv.declDeps_mem hci) (f := collectFuel)
    (fun c hc => henv.constants_mem (hcsP c hc)) (acc := []) nofun
  refine ⟨fun decls h => ?_, fun w h => ?_⟩ <;> rw [collectDeps.eq_1, hcs] at h <;>
    simp only [bind, Except.bind] at h <;> split at h
  · cases h
  · rename_i res hres
    split at h
    · cases h
    · cases h
      exact hcl.1 _ hres
  · rename_i err hres
    cases h
    exact hcl.2 w hres
  · split at h <;> cases h

/-- On an in-scope input, the computed closure is a sub-environment of `P`. Reference: none
directly (DV-3). -/
theorem collectDeps_sub {view : EnvView} (henv : ProgEnv P venv) (hview : ViewAgrees view P)
    (he : TrS venv Us [] e e') (h : collectDeps view e = .ok decls) : SubEnv decls P :=
  (collectDeps_scope henv hview he).1 decls h

/-- Routing is justified by master alone: an in-scope input is never sent to the `Meta` path.
Reference: none (the shipping entry point's `Erasure.route`). -/
theorem collectDeps_not_outOfFragment {view : EnvView} (h : InScope view e) :
    ∀ w, collectDeps view e ≠ .error (.outOfFragment w) :=
  let ⟨_, _, _, _, henv, hview, he⟩ := h
  (collectDeps_scope henv hview he).2

end

end EraseProof
