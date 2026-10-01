import EraseProof.Core.Scope
import EraseProof.Core.Frame

/-!
# The order of a program's declarations, and the traversal's scopes

A program's model is built one declaration at a time (`EraseProof.ProgEnv`), and a declaration's
value is translated in the model before it, extended by its own block. So a value mentions only its
own block and declarations of a suffix of the program (`ProgEnv.value_suffix`), and the program's
names are distinct (`ProgEnv.nodup`). The traversal registers a constant only when a value it
erases mentions it in a value position (`EraseProof.OccursV`), so what it may register while
erasing a term is bounded by a scope (`ScopeOK`): a set of declarations of the closure `decls` that
is closed under block members and under the constants in value positions of values. A value has a
scope that holds no member of its own block (`CoreEnv.valueScope`); this is what keeps the
traversal from registering a constant while it erases the constant's own value.
-/

open Lean Lean4Lean Erasure

namespace EraseProof

section
variable {venv : VEnv} {P decls : List ConstantInfo}

/-- The constants of a translated term are constants of the model. Reference: rule `type_Const`
(`MR P/PCUICTyping.v:232`), whose constant is declared. -/
theorem TrS.constsIn {Us : List Name} {Δ : VLCtx} {e : Expr} {e' : VExpr}
    (h : TrS venv Us Δ e e') : ConstsIn (fun c => (venv.constants c).isSome) e := by
  induction h with
  | const h1 => simp [ConstsIn, h1]
  | bvar | fvar | sort => trivial
  | app _ _ _ _ ih1 ih2 | lam _ _ _ ih1 ih2 | forallE _ _ _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | letE _ _ _ _ ih1 ih2 ih3 => exact ⟨ih1, ih2, ih3⟩
  | mdata _ ih => exact ih

/-- A constant in a value position (`OccursV`) satisfies what every constant of the term satisfies.
Reference: none (the structural predicates `ConstsIn`, `OccursV`). -/
theorem ConstsIn.occursV {p : Name → Prop} {d : Name} :
    ∀ {e : Expr}, ConstsIn p e → OccursV d e = true → p d
  | .const c _, h, ho => by
    simp only [OccursV, beq_iff_eq] at ho
    subst ho; exact h
  | .app f a, h, ho | .letE _ _ f a _, h, ho => by
    simp only [OccursV, Bool.or_eq_true] at ho
    first
    | exact ho.elim (ConstsIn.occursV h.1) (ConstsIn.occursV h.2)
    | exact ho.elim (ConstsIn.occursV h.2.1) (ConstsIn.occursV h.2.2)
  | .lam _ _ b _, h, ho => ConstsIn.occursV h.2 ho
  | .mdata _ b, h, ho | .proj _ _ b, h, ho => ConstsIn.occursV (e := b) h ho
  | .bvar _, _, ho | .fvar _, _, ho | .mvar _, _, ho | .sort _, _, ho | .forallE .., _, ho
  | .lit _, _, ho => by simp [OccursV] at ho

/-- The names a block adds are fresh in the environment it extends. Reference: none (lean4lean
`VEnv.addConsts`, `l4l Theory/Typing/Env.lean:11`). -/
theorem addConsts_fresh {env env' : VEnv} : ∀ {cis : List VDefVal},
    env.addConsts cis = some env' → ∀ ci ∈ cis, env.constants ci.name = none
  | [], _, _, hc => nomatch hc
  | ci :: cis, h, c, hc => by
    simp only [VEnv.addConsts, List.foldlM_cons, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at h
    obtain ⟨env₁, h1, h2⟩ := h
    cases hc with
    | head => unfold VEnv.addConst at h1; split at h1 <;> simp_all
    | tail _ hc =>
      have := addConsts_fresh h2 c hc
      rw [VEnv.addConst_constants_eq h1] at this
      simp only at this
      split at this
      · cases this
      · exact this

/-- A name that `addConst` adds was fresh. Reference: none (lean4lean `VEnv.addConst`,
`l4l Theory/VEnv.lean:27`). -/
theorem addConst_fresh {env env' : VEnv} {n : Name} {ci : VConstant}
    (h : env.addConst n ci = some env') : env.constants n = none := by
  unfold VEnv.addConst at h; split at h <;> simp_all

/-- Every name of a program is a constant of its model. Reference: `lookup_env`
(`MR common/theories/Environment.v:483`) of a declared constant. -/
theorem ProgEnv.mem_constants (h : ProgEnv P venv) {c : Name} (hc : c ∈ P.map (·.name)) :
    (venv.constants c).isSome := by
  have hs : (findDecl P c).isSome := by
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    rw [findDecl, List.find?_isSome]
    exact ⟨d, hd, by simp⟩
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.1 hs
  obtain ⟨_, h1, _⟩ := h.lookup hci
  simp [h1]

/-- The names of a program are distinct: each declaration's name is fresh when it is added.
Reference: `fresh_global` (`MR common/theories/EnvironmentTyping.v:1738`), the `kn_fresh` premise
of `on_global_decls` (`:1743`). -/
theorem ProgEnv.nodup (h : ProgEnv P venv) : (P.map (·.name)).Nodup := by
  induction h with
  | nil => exact .nil
  | «axiom» hP _ _ h2 ih | thm hP _ _ _ _ h2 ih | «opaque» hP _ _ _ h2 ih
  | defn hP _ _ _ h2 ih =>
    refine List.nodup_cons.2 ⟨fun hmem => ?_, ih⟩
    have := hP.mem_constants hmem
    dsimp only [ConstantInfo.name, ConstantInfo.toConstantVal] at this
    rw [addConst_fresh h2] at this
    cases this
  | @block cs venv venv' vs cis' hP hnd _ htr _ h2 _ ih =>
    rw [List.map_append, List.nodup_append]
    refine ⟨?_, ih, fun a ha b hb hab => ?_⟩
    · rw [List.map_map, List.map_reverse]
      exact List.nodup_reverse.2 hnd
    · subst hab
      rw [List.map_map, List.map_reverse, List.mem_reverse] at ha
      have ha' : a ∈ vs.map (·.name) := ha
      rw [← forall₂_trDef_names htr] at ha'
      obtain ⟨ci', hci', rfl⟩ := List.mem_map.1 ha'
      have := hP.mem_constants hb
      rw [addConsts_fresh h2 ci' hci'] at this
      cases this

/-- The members of a declaration's block are names of the program. Reference: none (Lean's
`ConstantInfo.all`; a mutual block is added whole, DV-3). -/
theorem ProgEnv.all_mem (h : ProgEnv P venv) {ci : ConstantInfo} (hci : ci ∈ P) :
    ∀ n ∈ ci.all, n ∈ P.map (·.name) := by
  induction h with
  | nil => cases hci
  | «axiom» _ _ _ _ ih =>
    rcases List.mem_cons.1 hci with rfl | hci
    · intro n hn
      simp only [ConstantInfo.all, List.mem_singleton] at hn
      subst hn
      exact List.mem_map_of_mem (.head _)
    · exact fun n hn => List.mem_cons_of_mem _ (ih hci n hn)
  | defn _ hall _ _ _ ih | thm _ hall _ _ _ _ ih | «opaque» _ hall _ _ _ ih =>
    rcases List.mem_cons.1 hci with rfl | hci
    · intro n hn
      simp only [ConstantInfo.all, hall, List.mem_singleton] at hn
      subst hn
      exact List.mem_map_of_mem (.head _)
    · exact fun n hn => List.mem_cons_of_mem _ (ih hci n hn)
  | block _ _ hall _ _ _ _ ih =>
    rcases List.mem_append.1 hci with hb | hc
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hb
      intro n hn
      simp only [ConstantInfo.all, hall w (List.mem_reverse.1 hw)] at hn
      exact mem_block_names hn
    · intro n hn
      rw [List.map_append]
      exact List.mem_append_right _ (ih hc n hn)

/-- A declaration's name is a member of its block. Reference: none (Lean's `ConstantInfo.all`,
DV-3). -/
theorem ProgEnv.name_mem_all (h : ProgEnv P venv) {ci : ConstantInfo} (hci : ci ∈ P) :
    ci.name ∈ ci.all := by
  induction h with
  | nil => cases hci
  | «axiom» _ _ _ _ ih =>
    rcases List.mem_cons.1 hci with rfl | hci
    · exact .head _
    · exact ih hci
  | defn _ hall _ _ _ ih | thm _ hall _ _ _ _ ih | «opaque» _ hall _ _ _ ih =>
    rcases List.mem_cons.1 hci with rfl | hci
    · simp only [ConstantInfo.all, hall]; exact .head _
    · exact ih hci
  | block _ _ hall _ _ _ _ ih =>
    rcases List.mem_append.1 hci with hb | hc
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hb
      simp only [ConstantInfo.all, hall w (List.mem_reverse.1 hw)]
      exact List.mem_map_of_mem (List.mem_reverse.1 hw)
    · exact ih hc

/-- A declaration of a program without a value is an axiom, alone in its block. Reference: the
`cst_body = None` case of `on_constant_decl` (`MR common/theories/EnvironmentTyping.v:1722`),
DV-3. -/
theorem ProgEnv.all_of_value?_none (h : ProgEnv P venv) {ci : ConstantInfo} (hci : ci ∈ P)
    (hv : ci.value? (allowOpaque := true) = none) : ci.all = [ci.name] := by
  induction h with
  | nil => cases hci
  | «axiom» _ _ _ _ ih =>
    rcases List.mem_cons.1 hci with rfl | hci
    · rfl
    · exact ih hci
  | defn _ _ _ _ _ ih | thm _ _ _ _ _ _ ih | «opaque» _ _ _ _ _ ih =>
    rcases List.mem_cons.1 hci with rfl | hci
    · simp [ConstantInfo.value?] at hv
    · exact ih hci
  | block _ _ _ _ _ _ _ ih =>
    rcases List.mem_append.1 hci with hb | hc
    · obtain ⟨w, -, rfl⟩ := List.mem_map.1 hb
      simp [ConstantInfo.value?] at hv
    · exact ih hc

/-- The value of a declaration of a program mentions only its own block and the names of a
suffix of the program that is itself a program and has no member of the block. Reference: the
well-foundedness of `on_global_env` (`MR common/theories/EnvironmentTyping.v`), whose declarations
are typed in the environment before them. -/
theorem ProgEnv.value_suffix (h : ProgEnv P venv) {ci : ConstantInfo} (hci : ci ∈ P) {v : Expr}
    (hv : ci.value? (allowOpaque := true) = some v) :
    ∃ post venvp, (∃ pre, P = pre ++ post) ∧ ProgEnv post venvp ∧
      (∀ n ∈ ci.all, n ∉ post.map (·.name)) ∧
      ConstsIn (fun c => c ∈ ci.all ∨ c ∈ post.map (·.name)) v := by
  have hval : ci.value! (allowOpaque := true) = v := by rw [value!_eq, hv]; rfl
  induction h with
  | nil => cases hci
  | «axiom» _ _ _ _ ih =>
    rcases List.mem_cons.1 hci with rfl | hci
    · simp [ConstantInfo.value?] at hv
    · have ⟨post, venvp, ⟨pre, hpre⟩, h1, h2, h3⟩ := ih hci
      exact ⟨post, venvp, ⟨_ :: pre, by rw [hpre]; rfl⟩, h1, h2, h3⟩
  | defn hcs hall htr _ h2 ih | thm hcs hall htr _ _ h2 ih | «opaque» hcs hall htr _ h2 ih =>
    rcases List.mem_cons.1 hci with rfl | hci
    · refine ⟨_, _, ⟨[_], rfl⟩, hcs, fun n hn hmem => ?_, ?_⟩
      · simp only [ConstantInfo.all, hall, List.mem_singleton] at hn
        subst hn
        have := hcs.mem_constants hmem
        rw [addConst_fresh h2] at this
        cases this
      · have ht := htr.2.2
        rw [hval] at ht
        exact ConstsIn.mono (fun c hc => .inr (hcs.constants_mem hc)) (TrS.constsIn ht)
    · have ⟨post, venvp, ⟨pre, hpre⟩, h1, h2, h3⟩ := ih hci
      exact ⟨post, venvp, ⟨_ :: pre, by rw [hpre]; rfl⟩, h1, h2, h3⟩
  | block hcs _ hall htr _ h2 _ ih =>
    rcases List.mem_append.1 hci with hb | hc
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hb
      have hw := List.mem_reverse.1 hw
      have hall0 : (ConstantInfo.defnInfo w).all = _ := hall w hw
      refine ⟨_, _, ⟨_, rfl⟩, hcs, fun n hn hmem => ?_, ?_⟩
      · rw [hall0, ← forall₂_trDef_names htr] at hn
        obtain ⟨ci', hci', rfl⟩ := List.mem_map.1 hn
        have := hcs.mem_constants hmem
        rw [addConsts_fresh h2 ci' hci'] at this
        cases this
      · obtain ⟨_, _, hr⟩ := forall₂_exists_of_mem_left htr hw
        have ht := hr.2.2
        rw [hval] at ht
        refine ConstsIn.mono (fun c hc => ?_) (TrS.constsIn ht)
        rcases addConsts_constants_mem h2 hc with hc | hc
        · exact .inr (hcs.constants_mem hc)
        · rw [forall₂_trDef_names htr, ← hall0] at hc
          exact .inl hc
    · have ⟨post, venvp, ⟨pre, hpre⟩, h1, h2, h3⟩ := ih hc
      exact ⟨post, venvp, ⟨_ ++ pre, by rw [hpre, List.append_assoc]⟩, h1, h2, h3⟩


/-- The value of a declaration of a program translates in the program's model, at the declaration's
level parameters. Reference: the `cst_body` typing of `on_global_env`
(`MR common/theories/EnvironmentTyping.v:1749`), weakened to the whole environment
(`MR pcuic/theories/PCUICWeakeningEnv.v:295 weakening_env_declared_constant`). -/
theorem ProgEnv.value_tr (h : ProgEnv P venv) {ci : ConstantInfo} (hci : ci ∈ P) {v : Expr}
    (hv : ci.value? (allowOpaque := true) = some v) :
    ∃ v', TrS venv ci.levelParams [] v v' := by
  have hval : ci.value! (allowOpaque := true) = v := by rw [value!_eq, hv]; rfl
  induction h with
  | nil => cases hci
  | «axiom» _ _ _ h2 ih =>
    cases hci with
    | head => simp [ConstantInfo.value?] at hv
    | tail _ hci => have ⟨v', h⟩ := ih hci; exact ⟨v', h.mono (VEnv.addConst_le h2)⟩
  | @defn _ _ _ venv' ci' _ _ htr _ h2 ih =>
    have hle : _ ≤ venv'.addDefEq ci'.toDefEq := (VEnv.addConst_le h2).trans VEnv.addDefEq_le
    cases hci with
    | head => exact ⟨_, (hval ▸ htr.2.2).mono hle⟩
    | tail _ hci => have ⟨v', h⟩ := ih hci; exact ⟨v', h.mono hle⟩
  | thm _ _ htr _ _ h2 ih | «opaque» _ _ htr _ h2 ih =>
    have hle := VEnv.addConst_le h2
    cases hci with
    | head => exact ⟨_, (hval ▸ htr.2.2).mono hle⟩
    | tail _ hci => have ⟨v', h⟩ := ih hci; exact ⟨v', h.mono hle⟩
  | block _ _ _ htr _ h2 _ ih =>
    rcases List.mem_append.1 hci with hb | hc
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hb
      obtain ⟨ci', -, htr'⟩ := forall₂_exists_of_mem_left htr (List.mem_reverse.1 hw)
      exact ⟨_, (hval ▸ htr'.2.2).mono VEnv.addDefEqs_le⟩
    · have ⟨v', h⟩ := ih hc
      exact ⟨v', h.mono ((VEnv.addConsts_le h2).trans VEnv.addDefEqs_le)⟩

/-- A declaration found in a program is in the suffix that has its name, since the program's
names are distinct. Reference: `lookup_env_extends_NoDup` (`MR common/theories/Environment.v:653`).
-/
theorem findDecl_mem_suffix {pre post : List ConstantInfo} {d : Name} {cd : ConstantInfo}
    (hnd : ((pre ++ post).map (·.name)).Nodup) (h : findDecl (pre ++ post) d = some cd)
    (hd : d ∈ post.map (·.name)) : cd ∈ post := by
  unfold findDecl at h
  rw [List.find?_append] at h
  cases hp : pre.find? (·.name == d) with
  | some x =>
    have hx := List.mem_of_find?_eq_some hp
    have hxn : x.name = d := by simpa using List.find?_some hp
    rw [List.map_append] at hnd
    exact absurd hd ((List.nodup_append.1 hnd).2.2 _ (hxn ▸ List.mem_map_of_mem hx) _ · rfl)
  | none =>
    rw [hp, Option.none_or] at h
    exact List.mem_of_find?_eq_some h

/-- The facts a run of the pure path rests on: the program `P` has the model `venv` (`prog`), and
the declarations `decls` it reads are a sub-environment of `P` (`sub`) with distinct kernames
(`inj`), closed types and values (`closed`), closed under dependencies (`deps`). Reference: `wf_ext
Σ` and `Σ ∼_ext X` of `erases_erase` (`MR E/ErasureFunction.v:1228`), and the closure that
`erase_global_deps` (`MR E/ErasureFunction.v:1602`) computes. -/
structure CoreEnv (venv : VEnv) (P decls : List ConstantInfo) : Prop where
  prog : ProgEnv P venv
  sub : SubEnv decls P
  inj : KernameInj decls
  closed : ClosedDecls decls
  deps : DepClosed decls

/-- A scope of the traversal: a set of constants declared in `decls`, closed under the members of
their blocks and under the constants in value positions (`OccursV`) of their values, the positions
the traversal erases. Reference: the dependencies `term_global_deps` (`MR E/EAstUtils.v:406`) that
`erase_global_deps` (`MR E/ErasureFunction.v:1602`) follows, transitively. -/
def ScopeOK (decls : List ConstantInfo) (S : Name → Prop) : Prop :=
  ∀ c, S c → ∃ ci, findDecl decls c = some ci ∧ (∀ n ∈ ci.all, S n) ∧
    ∀ v, ci.value? (allowOpaque := true) = some v → ∀ d, OccursV d v = true → S d

/-- The value of a declaration of `decls` has a scope that holds no member of the declaration's
own block: its value positions mention only the block and that scope. This is what keeps the
traversal from registering a constant while it erases its own value. Reference:
`erase_global_deps_fresh` (`MR E/ErasureFunctionProperties.v:1206`), where the declarations are
erased in the order of the environment. -/
theorem CoreEnv.valueScope (hG : CoreEnv venv P decls) {c : Name} {ci : ConstantInfo}
    (hci : findDecl decls c = some ci) {v : Expr} (hv : ci.value? (allowOpaque := true) = some v) :
    ∃ S', ScopeOK decls S' ∧ (∀ d, OccursV d v = true → d ∈ ci.all ∨ S' d) ∧
      ∀ n ∈ ci.all, ¬ S' n := by
  have hci' : ci ∈ decls := List.mem_of_find?_eq_some hci
  have hciP : ci ∈ P := List.mem_of_find?_eq_some (hG.sub ci hci')
  obtain ⟨post, venvp, ⟨pre, rfl⟩, hpost, hdisj, hcs⟩ := hG.prog.value_suffix hciP hv
  refine ⟨fun d => (findDecl decls d).isSome ∧ d ∈ post.map (·.name), ?_, fun d hd => ?_,
    fun n hn h => hdisj n hn h.2⟩
  · rintro d ⟨hds, hdp⟩
    obtain ⟨cd, hcd⟩ := Option.isSome_iff_exists.1 hds
    have hcdpost : cd ∈ post :=
      findDecl_mem_suffix hG.prog.nodup (SubEnv.findDecl_of_some hG.sub hcd) hdp
    have hdep := hG.deps cd (List.mem_of_find?_eq_some hcd)
    refine ⟨cd, hcd, fun n hn => ⟨hdep.2.2 n hn, hpost.all_mem hcdpost n hn⟩,
      fun w hw e he => ⟨(hdep.2.1 w hw).occursV he, ?_⟩⟩
    obtain ⟨post', _, ⟨pre', rfl⟩, _, _, hcs'⟩ := hpost.value_suffix hcdpost hw
    rcases hcs'.occursV he with h | h
    · exact hpost.all_mem hcdpost e h
    · rw [List.map_append]
      exact List.mem_append_right _ h
  · have h2 : (findDecl decls d).isSome := ((hG.deps ci hci').2.1 v hv).occursV hd
    rcases hcs.occursV hd with h | h
    · exact .inl h
    · exact .inr ⟨h2, h⟩

end

end EraseProof
