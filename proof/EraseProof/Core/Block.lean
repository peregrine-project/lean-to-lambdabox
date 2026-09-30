import EraseProof.Core.Steps
import EraseProof.Core.CloseFix

/-!
# The recursive-block step of the shipping core's correctness

`Erasure.visitMutual` erases a recursive declaration (`EraseProof.RecursiveDecl`) together with the
members of its block (`ConstantInfo.all`): it allocates one fresh free variable per member (the fix
variables), erases every member's value with the members' occurrences sent to their fix variables,
closes each erased value over the fix variables with `mkDef`'s loop (`EraseProof.closeFix`), and
registers member `j` as `tFix defs j`. This module proves that step of `erasePure_erases`
(`visitMutual_rec_step`), closing step 2 of the traversal's correctness: a member's erasure `r`
is closed and mentions the fix variables only through the admissible targets `rcBlock`;
`closeFix_substl` turns the stored body, instantiated as `cunfold_fix` does, into
`substFVars (fixTargets ids defs) r`, and `Erases.substRc` turns the targets into the registered
fixpoints (`RecIn`), which is `ErasesBlock`'s premise.

Reference: the `tFix` case of `erases_erase` (`MR E/ErasureFunction.v:1228`) with rule
`erases_tFix` (`MR E/Extract.v:122`), for Lean's environment-level recursion (DV-7), whose blocks
the traversal closes with free variables (DV-13); the `ConstantDecl` step of `erase_global_deps`
(`MR E/ErasureFunction.v:1602`).
-/

open Lean Lean4Lean Erasure

namespace EraseProof

section
variable {venv : VEnv} {P decls : List ConstantInfo}

/-! ## The blocks of a program -/

/-- The members of a block are distinct. Reference: none (Lean's `ConstantInfo.all`, DV-3); the
distinct names that `on_global_decls` (`MR common/theories/EnvironmentTyping.v:1743`) asks of
every name. -/
theorem ProgEnv.all_nodup (h : ProgEnv P venv) {ci : ConstantInfo} (hci : ci ∈ P) :
    ci.all.Nodup := by
  induction h with
  | nil => cases hci
  | «axiom» _ _ _ _ ih =>
    rcases List.mem_cons.1 hci with rfl | hci
    · simp [ConstantInfo.all]
    · exact ih hci
  | defn _ hall _ _ _ ih | thm _ hall _ _ _ _ ih | «opaque» _ hall _ _ _ ih =>
    rcases List.mem_cons.1 hci with rfl | hci
    · simp [ConstantInfo.all, hall]
    · exact ih hci
  | block _ hnd hall _ _ _ _ ih =>
    rcases List.mem_append.1 hci with hb | hc
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hb
      simp only [ConstantInfo.all, hall w (List.mem_reverse.1 hw)]
      exact hnd
    · exact ih hc

/-- Every member of a block has the block's `all`. Reference: none (Lean's `ConstantInfo.all`,
DV-3). -/
theorem ProgEnv.all_eq (h : ProgEnv P venv) :
    ∀ {ci ci' : ConstantInfo} {n : Name}, ci ∈ P → n ∈ ci.all → findDecl P n = some ci' →
      ci'.all = ci.all := by
  have hnd := h.nodup
  induction h with
  | nil => intro _ _ _ hci; cases hci
  | «axiom» hcs _ _ _ ih =>
    intro ci ci' n hci hn hf
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.1 hci with rfl | hci
    · simp only [ConstantInfo.all, List.mem_singleton] at hn
      subst hn
      rw [findDecl_cons, if_pos rfl] at hf
      cases hf; rfl
    · have hnP := hcs.all_mem hci n hn
      rw [findDecl_cons, if_neg (by rintro rfl; exact hnd.1 hnP)] at hf
      exact ih hnd.2 hci hn hf
  | defn hcs hall _ _ _ ih | thm hcs hall _ _ _ _ ih | «opaque» hcs hall _ _ _ ih =>
    intro ci ci' n hci hn hf
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.1 hci with rfl | hci
    · simp only [ConstantInfo.all, hall, List.mem_singleton] at hn
      subst hn
      simp only [findDecl_cons, ConstantInfo.name, ConstantInfo.toConstantVal, ↓reduceIte] at hf
      cases hf; rfl
    · have hnP := hcs.all_mem hci n hn
      rw [findDecl_cons, if_neg (by rintro rfl; exact hnd.1 hnP)] at hf
      exact ih hnd.2 hci hn hf
  | block hcs _ hall _ _ _ _ ih =>
    intro ci ci' n hci hn hf
    rw [List.map_append, List.nodup_append] at hnd
    unfold findDecl at hf
    rw [List.find?_append] at hf
    rcases List.mem_append.1 hci with hb | hc
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hb
      have hallw := hall w (List.mem_reverse.1 hw)
      simp only [ConstantInfo.all, hallw] at hn ⊢
      cases hfb : List.find? (fun c => c.name == n) (List.map ConstantInfo.defnInfo _) with
      | some x =>
        rw [hfb, Option.some_or] at hf
        cases hf
        obtain ⟨w', hw', rfl⟩ := List.mem_map.1 (List.mem_of_find?_eq_some hfb)
        exact hall w' (List.mem_reverse.1 hw')
      | none =>
        obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hn
        have := List.find?_eq_none.1 hfb (.defnInfo u)
          (List.mem_map.2 ⟨u, List.mem_reverse.2 hu, rfl⟩)
        exact absurd (beq_self_eq_true u.name) this
    · have hnP := hcs.all_mem hc n hn
      cases hfb : List.find? (fun c => c.name == n) (List.map ConstantInfo.defnInfo _) with
      | some x =>
        have hx := List.mem_of_find?_eq_some hfb
        have hxn : x.name = n := by simpa using List.find?_some hfb
        exact absurd hnP (hnd.2.2 _ (List.mem_map.2 ⟨x, hx, hxn⟩) n · rfl)
      | none =>
        rw [hfb, Option.none_or] at hf
        exact ih hnd.2.1 hc hn hf

variable {view : EnvView} {cfg : ErasureConfig}

/-- Every member of the block of a recursive, non-remapped declaration with a value is a
declaration of the closure with the same block and a value, and is itself recursive and not
remapped: the eraser compiles the whole block to one fixpoint. Reference: none (DV-7). -/
theorem CoreEnv.member (hG : CoreEnv venv P decls) {c : Name} {ci : ConstantInfo} {v : Expr}
    (hci : findDecl decls c = some ci) (hv : ci.value? (allowOpaque := true) = some v)
    (hax : axiomatized view cfg ci = false) (hrec : RecursiveDecl ci = true) {n : Name}
    (hn : n ∈ ci.all) :
    ∃ cn w, findDecl decls n = some cn ∧ cn.all = ci.all ∧
      cn.value? (allowOpaque := true) = some w ∧ axiomatized view cfg cn = false ∧
      RecursiveDecl cn = true := by
  have hci' : ci ∈ decls := List.mem_of_find?_eq_some hci
  have hciP : ci ∈ P := List.mem_of_find?_eq_some (hG.sub ci hci')
  obtain ⟨cn, hcn⟩ := Option.isSome_iff_exists.1 ((hG.deps ci hci').2.2 n hn)
  have hall : cn.all = ci.all :=
    hG.prog.all_eq hciP hn (SubEnv.findDecl_of_some hG.sub hcn)
  by_cases hlen : ci.all.length = 1
  · have hname : ci.name = c := by simpa using List.find?_some hci
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.1 hlen
    have hmem := hG.prog.name_mem_all hciP
    rw [ha, List.mem_singleton] at hmem hn
    rw [hn, ← hmem, hname, hci] at hcn
    cases hcn
    exact ⟨ci, v, by rw [hn, ← hmem, hname, hci], rfl, hv, hax, hrec⟩
  · have hcnP : cn ∈ P :=
      List.mem_of_find?_eq_some (SubEnv.findDecl_of_some hG.sub hcn)
    cases hw : cn.value? (allowOpaque := true) with
    | none =>
      have := hG.prog.all_of_value?_none hcnP hw
      rw [hall] at this
      exact absurd (by rw [this]; rfl) hlen
    | some w =>
      refine ⟨cn, w, hcn, hall, hw, ?_, ?_⟩
      · simp [axiomatized, hall, hlen]
      · simp [RecursiveDecl, hall, hlen]

end

/-! ## The fix variables -/

/-- The `m` free variables that the pure backend's `freshFVarId` allocates from the counter value
`p`, in order: the fix variables of an `m`-member block. Reference: none (DV-13). -/
def freshIds (p : Nat) : Nat → List FVarId
  | 0 => []
  | m + 1 => pureFVar p :: freshIds (p + 1) m

/-- `freshIds p m` has `m` variables. Reference: none. -/
theorem freshIds_length : ∀ (p m : Nat), (freshIds p m).length = m
  | _, 0 => rfl
  | p, m + 1 => by simp only [freshIds, List.length_cons, freshIds_length (p + 1) m]

/-- The variables of `freshIds p m` are those of the counter values `p, …, p+m-1`. Reference:
none. -/
theorem mem_freshIds : ∀ {p m : Nat} {x : FVarId}, x ∈ freshIds p m →
    ∃ k, p ≤ k ∧ k < p + m ∧ x = pureFVar k
  | _, 0, _, h => nomatch h
  | p, m + 1, x, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨p, Nat.le_refl _, by omega, rfl⟩
    · obtain ⟨k, h1, h2, rfl⟩ := mem_freshIds h
      exact ⟨k, by omega, by omega, rfl⟩

/-- The fix variables of a block are distinct. Reference: none. -/
theorem freshIds_nodup : ∀ (p m : Nat), (freshIds p m).Nodup
  | _, 0 => .nil
  | p, m + 1 => List.nodup_cons.2 ⟨fun h => by
      obtain ⟨k, h1, -, hk⟩ := mem_freshIds h
      have := pureFVar_inj hk
      omega, freshIds_nodup (p + 1) m⟩

/-- `visitMutual`'s allocation of one fix variable per member at the pure backend: the variables
`freshIds`, with the counter advanced by the number of members. Reference: none (DV-13). -/
theorem freshIds_run {β : Type} {pc : PureCtx} {tc : TravCtx} {st : ErasureState} :
    ∀ (l : List β) (ps : PureState),
      (l.mapM (fun _ => (liftM (Backend.freshFVarId (m := PureM)) : EraseT PureM FVarId))).runPure
        st tc pc ps = .ok ((freshIds ps.next l.length, st), ⟨ps.next + l.length⟩)
  | [], _ => rfl
  | _ :: l, ps => by
    rw [List.mapM_cons, runPure_bind, fresh_run, Except.ok_bind']
    dsimp only
    rw [runPure_bind, freshIds_run l ⟨ps.next + 1⟩]
    dsimp only
    rw [List.length_cons, show ps.next + (l.length + 1) = ps.next + 1 + l.length by omega]
    rfl

/-- The admissible targets of recursive constants inside a block: member `names[j]` erases to its
fix variable `ids[j]`. Reference: none (DV-7, DV-13). -/
def rcBlock (names : List Name) (ids : List FVarId) : Name → LBTerm → Prop :=
  fun c t => ∃ (j : Nat) (x : FVarId), names[j]? = some c ∧ ids[j]? = some x ∧ t = .fvar x

/-- With distinct names, the keys of `names.zip ids` are pairwise distinct. Reference: none. -/
theorem pairwise_zip {names : List Name} {ids : List FVarId} (hnd : names.Nodup) :
    (names.zip ids).Pairwise (fun a b => (a.1 == b.1) = false) := by
  induction names generalizing ids with
  | nil => simp
  | cons c cs ih =>
    cases ids with
    | nil => simp
    | cons x xs =>
      have ⟨hc, hcs⟩ := List.nodup_cons.1 hnd
      simp only [List.zip_cons_cons, List.pairwise_cons]
      refine ⟨fun p hp => ?_, ih hcs⟩
      have : p.1 ∈ cs := (List.of_mem_zip hp).1
      exact beq_false_of_ne fun h => hc (h ▸ this)

/-- The block's reader context (`visitMutual`'s `fixvars := HashMap.ofList (names.zip ids)`) sends
each member to its fix variable, a target of `rcBlock`: `CtxOK.fixvars`. Reference: none (DV-7,
DV-13). -/
theorem fixvars_rcBlock {names : List Name} {ids : List FVarId} (hnd : names.Nodup)
    (hlen : names.length = ids.length) :
    ∀ c x, (some (Std.HashMap.ofList (names.zip ids))).bind (fun m => m[c]?) = some x →
      rcBlock names ids c (.fvar x) := by
  intro c x h
  simp only [Option.bind_some] at h
  by_cases hc : c ∈ names
  · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hc
    have hj' : j < ids.length := hlen ▸ hj
    rw [Std.HashMap.getElem?_ofList_of_mem (k := names[j]) (v := ids[j]) (by simp)
      (pairwise_zip hnd) (List.mem_iff_getElem.2 ⟨j, by simp; omega, by simp⟩)] at h
    cases h
    exact ⟨j, ids[j], by simp [hj], by simp [hj'], rfl⟩
  · rw [Std.HashMap.getElem?_ofList_of_contains_eq_false] at h
    · cases h
    · rw [List.map_fst_zip (by omega)]
      simpa using hc

/-- The block's reader context has a fix variable for every member. Reference: none. -/
theorem fixvars_isSome {names : List Name} {ids : List FVarId} (hnd : names.Nodup)
    (hlen : names.length = ids.length) {c : Name} (hc : c ∈ names) :
    ((some (Std.HashMap.ofList (names.zip ids))).bind (fun m => m[c]?)).isSome := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hc
  simp only [Option.bind_some]
  rw [Std.HashMap.getElem?_ofList_of_mem (k := names[j]) (v := ids[j]) (by simp)
    (pairwise_zip hnd) (List.mem_iff_getElem.2 ⟨j, by simp; omega, by simp⟩)]
  rfl

/-- With distinct names, the fix variables `mkDef` looks up in the block's reader context are
`ids`. Reference: none. -/
theorem ofList_zip_getElem! {names : List Name} {ids : List FVarId} (hnd : names.Nodup)
    (hlen : names.length = ids.length) :
    names.map (fun c => (Std.HashMap.ofList (names.zip ids))[c]!) = ids := by
  apply List.ext_getElem (by simp [hlen])
  intro j h1 h2
  simp only [List.getElem_map]
  refine Std.HashMap.getElem!_ofList_of_mem (k := names[j]) (by simp) (pairwise_zip hnd) ?_
  rw [List.mem_iff_getElem]
  exact ⟨j, by simp [hlen]; omega, by simp⟩

/-- The targets of `rcBlock` are closed. Reference: none. -/
theorem rcBlock_closed {names : List Name} {ids : List FVarId} : RcClosed (rcBlock names ids) := by
  rintro c t ⟨j, x, -, -, rfl⟩; rfl

/-- The position of a variable in a list without repetitions. Reference: none. -/
theorem idxOf?_of_nodup {l : List FVarId} (hnd : l.Nodup) {j : Nat} {x : FVarId}
    (hx : l[j]? = some x) : l.idxOf? x = some j := by
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 hx
  rw [List.idxOf?_eq_some_iff]
  refine ⟨hj, rfl, fun k hk h => ?_⟩
  exact List.pairwise_iff_getElem.1 hnd k j (by omega) hj hk h

/-- `Erases.substRc`'s premise for the fix variables' replacement `fixTargets ids defs`: once
every member `names[j]` is stored as `tFix defs j`, each target of `rcBlock` becomes a stored
fixpoint (`RecIn`). Reference: none (DV-7, DV-13). -/
theorem rcBlock_hrc {names : List Name} {ids : List FVarId} {defs : List (@FixDef LBTerm)}
    {lenv : GlobalDeclarations} (hids : ids.Nodup)
    (hreg : ∀ j c, names[j]? = some c →
      lookupConst lenv (toKername c) = some ⟨some (.fix defs j)⟩) :
    ∀ c t, rcBlock names ids c t → RecIn lenv c (substFVars (fixTargets ids defs) t) := by
  rintro c t ⟨j, x, hc, hx, rfl⟩
  refine ⟨defs, j, ?_, hreg j c hc⟩
  simp only [substFVars, fixTargets, idxOf?_of_nodup hids hx, Option.map_some, Option.getD_some]

/-! ## `mkDef` -/

/-- A `for` loop whose body only yields, with a pure update `g` of the loop state, is `foldl g`.
Reference: none. -/
theorem forIn_run {α β : Type} {pc : PureCtx} {st : ErasureState} {ps : PureState} {tc : TravCtx}
    {f : α → β → EraseT PureM (ForInStep β)} {g : β → α → β}
    (hf : ∀ a b, (f a b).runPure st tc pc ps = .ok ((.yield (g b a), st), ps)) :
    ∀ (l : List α) (b : β), (forIn l b f).runPure st tc pc ps = .ok ((l.foldl g b, st), ps)
  | [], b => rfl
  | a :: l, b => by
    rw [List.forIn_cons, runPure_bind, hf]
    exact forIn_run hf l (g b a)

/-- `mkDef` at the pure backend: the definition named `fixDefName n`, with principal argument `0`,
whose body is closed over the fix variables it looks up by `closeFix`. Reference: none (DV-13);
`erases_tFix` (`MR E/Extract.v:122`) builds `tFix` bodies de Bruijn. -/
theorem mkDef_run {pc : PureCtx} {st : ErasureState} {ps : PureState} {tc : TravCtx}
    (n : Name) (names : List Name) (t : LBTerm) {M : Std.HashMap Name FVarId}
    (hm : tc.fixvars = some M) :
    (mkDef (m := PureM) n names t).runPure st tc pc ps =
      .ok ((⟨fixDefName n, closeFix (names.map (M[·]!)) t, 0⟩, st), ps) := by
  unfold Erasure.mkDef
  rw [runPure_bind, forIn_run (g := fun b (p : Name × Nat) => toBvar M[p.1]! p.2 b)]
  · simp only [closeFix, ← List.map_reverse, List.zipIdx_map, List.foldl_map]
    rfl
  · rintro ⟨c, i⟩ b
    simp only [runPure_read_bind, hm, Option.get!_some]
    rfl

/-! ## The stored block: free variables and dependencies -/

mutual
/-- A free variable of `toBvars F d t` is a free variable of `t` that `F` does not abstract.
Reference: none (DV-13). -/
theorem hasFVar_toBvars (y : FVarId) (F : FVarId → Option Nat) :
    ∀ (t : LBTerm) (d : Nat), hasFVar y (toBvars F d t) = true → hasFVar y t = true ∧ F y = none
  | .box, _, h | .const _, _, h | .prim _, _, h | .bvar _, _, h => by
    simp [toBvars, hasFVar] at h
  | .fvar z, d, h => by
    simp only [toBvars] at h
    cases hz : F z with
    | some k => simp [hz, hasFVar] at h
    | none =>
      simp only [hz, hasFVar, beq_iff_eq] at h
      subst h
      exact ⟨by simp [hasFVar], hz⟩
  | .lambda _ b, d, h => by
    simp only [toBvars, hasFVar] at h ⊢; exact hasFVar_toBvars y F b _ h
  | .letIn _ b b', d, h => by
    simp only [toBvars, hasFVar, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact ⟨.inl (hasFVar_toBvars y F b _ h).1, (hasFVar_toBvars y F b _ h).2⟩
    · exact ⟨.inr (hasFVar_toBvars y F b' _ h).1, (hasFVar_toBvars y F b' _ h).2⟩
  | .app u v, d, h => by
    simp only [toBvars, hasFVar, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact ⟨.inl (hasFVar_toBvars y F u _ h).1, (hasFVar_toBvars y F u _ h).2⟩
    · exact ⟨.inr (hasFVar_toBvars y F v _ h).1, (hasFVar_toBvars y F v _ h).2⟩
  | .construct _ _ args, d, h => by
    simp only [toBvars, hasFVar] at h ⊢; exact hasFVarL_toBvarsL y F args _ h
  | .case _ c brs, d, h => by
    simp only [toBvars, hasFVar, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact ⟨.inl (hasFVar_toBvars y F c _ h).1, (hasFVar_toBvars y F c _ h).2⟩
    · exact ⟨.inr (hasFVarB_toBvarsB y F brs _ h).1, (hasFVarB_toBvarsB y F brs _ h).2⟩
  | .proj _ c, d, h => by
    simp only [toBvars, hasFVar] at h ⊢; exact hasFVar_toBvars y F c _ h
  | .fix defs _, d, h => by
    simp only [toBvars, hasFVar] at h ⊢; exact hasFVarD_toBvarsD y F defs _ h
/-- `hasFVar_toBvars` on argument lists. -/
theorem hasFVarL_toBvarsL (y : FVarId) (F : FVarId → Option Nat) :
    ∀ (as : List LBTerm) (d : Nat), hasFVarL y (toBvarsL F d as) = true →
      hasFVarL y as = true ∧ F y = none
  | [], _, h => by simp [toBvarsL, hasFVarL] at h
  | a :: as, d, h => by
    simp only [toBvarsL, hasFVarL, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact ⟨.inl (hasFVar_toBvars y F a _ h).1, (hasFVar_toBvars y F a _ h).2⟩
    · exact ⟨.inr (hasFVarL_toBvarsL y F as _ h).1, (hasFVarL_toBvarsL y F as _ h).2⟩
/-- `hasFVar_toBvars` on case branches. -/
theorem hasFVarB_toBvarsB (y : FVarId) (F : FVarId → Option Nat) :
    ∀ (bs : List (List BinderName × LBTerm)) (d : Nat), hasFVarB y (toBvarsB F d bs) = true →
      hasFVarB y bs = true ∧ F y = none
  | [], _, h => by simp [toBvarsB, hasFVarB] at h
  | (_, b) :: bs, d, h => by
    simp only [toBvarsB, hasFVarB, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact ⟨.inl (hasFVar_toBvars y F b _ h).1, (hasFVar_toBvars y F b _ h).2⟩
    · exact ⟨.inr (hasFVarB_toBvarsB y F bs _ h).1, (hasFVarB_toBvarsB y F bs _ h).2⟩
/-- `hasFVar_toBvars` on fixpoint bodies. -/
theorem hasFVarD_toBvarsD (y : FVarId) (F : FVarId → Option Nat) :
    ∀ (ds : List (@FixDef LBTerm)) (d : Nat), hasFVarD y (toBvarsD F d ds) = true →
      hasFVarD y ds = true ∧ F y = none
  | [], _, h => by simp [toBvarsD, hasFVarD] at h
  | ⟨_, b, _⟩ :: ds, d, h => by
    simp only [toBvarsD, hasFVarD, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact ⟨.inl (hasFVar_toBvars y F b _ h).1, (hasFVar_toBvars y F b _ h).2⟩
    · exact ⟨.inr (hasFVarD_toBvarsD y F ds _ h).1, (hasFVarD_toBvarsD y F ds _ h).2⟩
end

/-- A body closed by `mkDef`'s loop has no free variable when every free variable of the erased
body is a fix variable. Reference: none (DV-13); `closed_env` (`MR E/EGlobalEnv.v:181`). -/
theorem closeFix_hasFVar {r : LBTerm} {xs : List FVarId} (hxs : xs.Nodup)
    (hfv : ∀ y, hasFVar y r = true → y ∈ xs) (y : FVarId) : hasFVar y (closeFix xs r) = false := by
  rw [closeFix_eq_toBvars]
  cases h : hasFVar y (toBvars (closeFixIdx xs) 0 r) with
  | false => rfl
  | true =>
    obtain ⟨h1, h2⟩ := hasFVar_toBvars y (closeFixIdx xs) r 0 h
    rw [closeFixIdx_eq hxs, Option.map_eq_none_iff, List.idxOf?_eq_none_iff] at h2
    exact absurd (hfv y h1) h2

/-- A body of `toBvarsD F d ds` is the abstraction of a body of `ds`. Reference: none. -/
theorem mem_toBvarsD {F : FVarId → Option Nat} {d : Nat} :
    ∀ {ds : List (@FixDef LBTerm)} {e : @FixDef LBTerm},
      e ∈ toBvarsD F d ds → ∃ e₀ ∈ ds, e.body = toBvars F d e₀.body
  | [], _, h => nomatch h
  | ⟨_, b, _⟩ :: ds, e, h => by
    simp only [toBvarsD, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨_, .head _, rfl⟩
    · obtain ⟨e₀, he₀, hb⟩ := mem_toBvarsD h
      exact ⟨e₀, .tail _ he₀, hb⟩

section
variable {venv : VEnv} {σ : EvalEnv} {lenv : GlobalDeclarations}

/-- Abstracting free variables keeps the erased dependencies, which do not see variables.
Reference: `erases_deps_lift` (`MR E/EDeps.v:44`), for the traversal's abstraction (DV-13). -/
theorem ErasesDeps.toBvars {t : LBTerm} (h : ErasesDeps venv σ lenv t) :
    ∀ F d, ErasesDeps venv σ lenv (EraseProof.toBvars F d t) := by
  induction h with
  | box => intros; exact .box
  | bvar => intros; exact .bvar
  | fvar =>
    intro F d
    simp only [EraseProof.toBvars]
    split
    · exact .bvar
    · exact .fvar
  | lambda _ ih => intro F d; exact .lambda (ih _ _)
  | letIn _ _ ihv ihb => intro F d; exact .letIn (ihv _ _) (ihb _ _)
  | app _ _ ihf iha => intro F d; exact .app (ihf _ _) (iha _ _)
  | const hc hl hd hb _ => intros; exact .const hc hl hd hb
  | fix _ ih =>
    intro F d
    refine .fix fun e he => ?_
    obtain ⟨e₀, he₀, hb⟩ := mem_toBvarsD he
    rw [hb]
    exact ih e₀ he₀ _ _

/-- `mkDef`'s loop keeps the erased dependencies. Reference: `erases_deps_lift`
(`MR E/EDeps.v:44`), for the traversal's abstraction (DV-13). -/
theorem ErasesDeps.closeFix {t : LBTerm} (h : ErasesDeps venv σ lenv t) (xs : List FVarId) :
    ErasesDeps venv σ lenv (EraseProof.closeFix xs t) := by
  rw [closeFix_eq_toBvars]
  exact h.toBvars _ _

end

/-! ## Registering the block -/

/-- The fixpoint bodies of a block are closed under `k` when each is. Reference: none (the
`tFix` case of `closedn`, `MR E/ELiftSubst.v:90`). -/
theorem closednD_of_forall {k : Nat} :
    ∀ {ds : List (@FixDef LBTerm)}, (∀ d ∈ ds, closedn k d.body = true) → closednD k ds = true
  | [], _ => rfl
  | ⟨_, b, _⟩ :: ds, h => by
    simp only [closednD, Bool.and_eq_true]
    exact ⟨h _ (.head _), closednD_of_forall fun d hd => h d (.tail _ hd)⟩

/-- The fixpoint bodies of a block do not mention `x` when none does. Reference: none. -/
theorem hasFVarD_of_forall {x : FVarId} :
    ∀ {ds : List (@FixDef LBTerm)}, (∀ d ∈ ds, hasFVar x d.body = false) → hasFVarD x ds = false
  | [], _ => rfl
  | ⟨_, b, _⟩ :: ds, h => by
    simp only [hasFVarD, Bool.or_eq_false_iff]
    exact ⟨h _ (.head _), hasFVarD_of_forall fun d hd => h d (.tail _ hd)⟩

/-- The registered constants after inserting, for every pair of `L`, its name with its own
kername. Reference: none. -/
theorem foldl_insert_getElem? {c : Name} :
    ∀ (L : List (Name × Nat)) (M : Std.HashMap Name Kername),
      (L.foldl (fun M x => M.insert x.1 (toKername x.1)) M)[c]? =
        if c ∈ L.map (·.1) then some (toKername c) else M[c]?
  | [], M => by simp
  | x :: L, M => by
    rw [List.foldl_cons, foldl_insert_getElem? L, Std.HashMap.getElem?_insert]
    by_cases h : c ∈ L.map (·.1)
    · simp [h]
    · by_cases hx : x.1 = c
      · subst hx; simp
      · have : (x.1 == c) = false := by simpa using hx
        simp [h, this, Ne.symm hx]

/-- In a list of entries with distinct kernames, the search for an entry's kername finds it.
Reference: `lookup_env` (`MR E/EGlobalEnv.v:16`) on an environment with fresh names. -/
theorem find?_of_nodup {k : Kername} {g : GlobalDecl} :
    ∀ {l : GlobalDeclarations}, (l.map (·.1)).Nodup → (k, g) ∈ l → l.find? (·.1 == k) = some (k, g)
  | [], _, h => nomatch h
  | (k', g') :: l, hnd, h => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.find?_cons]
    cases hb : (k' == k) with
    | true =>
      have hk := Kername.eq_of_beq hb
      subst hk
      rcases List.mem_cons.1 h with h | h
      · rw [h]
      · exact absurd (List.mem_map.2 ⟨_, h, rfl⟩) hnd.1
    | false =>
      rcases List.mem_cons.1 h with h | h
      · cases h
        rw [kername_beq_self] at hb
        cases hb
      · exact find?_of_nodup hnd.2 h

/-- A `for` loop whose body registers the name of its pair `(n, i)` with `tFix defs i`, as
`visitMutual`'s last loop does, registers every pair of the list and pushes their entries in
order. Reference: the `ConstantDecl` step of `erase_global_deps` (`MR E/ErasureFunction.v:1602`),
once per member of the block (DV-7). -/
theorem forIn_register {pc : PureCtx} {tc : TravCtx} {defs : List (@FixDef LBTerm)}
    {B : Name × Nat → PUnit → EraseT PureM (ForInStep PUnit)}
    (hB : ∀ x u {st ps r st' ps'}, (B x u).runPure st tc pc ps = .ok ((r, st'), ps') →
      r = .yield PUnit.unit ∧ st'.constants = st.constants.insert x.1 (toKername x.1) ∧
      st'.gdecls = (toKername x.1, .constantDecl ⟨some (.fix defs x.2)⟩) :: st.gdecls ∧ ps' = ps) :
    ∀ (L : List (Name × Nat)) {st ps u u' st' ps'},
      (forIn L u B).runPure st tc pc ps = .ok ((u', st'), ps') →
      st'.constants = L.foldl (fun M x => M.insert x.1 (toKername x.1)) st.constants ∧
      st'.gdecls = (L.map fun x => (toKername x.1,
        GlobalDecl.constantDecl ⟨some (.fix defs x.2)⟩)).reverse ++ st.gdecls ∧ ps' = ps
  | [], st, ps, u, u', st', ps', h => by
    cases h
    exact ⟨rfl, rfl, rfl⟩
  | x :: L, st, ps, u, u', st', ps', h => by
    rw [List.forIn_cons, runPure_bind] at h
    replace h := Except.ok_of_bind h
    obtain ⟨⟨⟨r, st₁⟩, ps₁⟩, h1, h⟩ := h
    obtain ⟨rfl, hc1, hg1, rfl⟩ := hB x u h1
    obtain ⟨hc, hg, rfl⟩ := forIn_register hB L h
    refine ⟨by rw [hc, hc1]; rfl, ?_, rfl⟩
    rw [hg, hg1, List.map_cons, List.reverse_cons, List.append_assoc]
    rfl

/-- A `List.mapM` at the pure backend whose step, from a state with `StateOK` and an invariant
`Inv`, grows within `S`, keeps `Inv` and relates each element to its result by `Q` (stable
under growth of the λ□ environment): the whole run grows, keeps `Inv`, and relates every
element to its result. Reference: none; the fold of `erase_global_deps`
(`MR E/ErasureFunction.v:1602`) over a block's members. -/
theorem mapM_run {σ : EvalEnv} {S : Name → Prop} {pc : PureCtx} {tc : TravCtx} {α β : Type}
    {f : α → EraseT PureM β} {Inv : ErasureState → PureState → Prop}
    {Q : α → β → GlobalDeclarations → Prop}
    (hQ : ∀ {a b lenv lenv'}, LenvExt lenv lenv' → Q a b lenv → Q a b lenv') :
    ∀ (l : List α), (∀ a ∈ l, ∀ {st ps b st' ps'}, StateOK venv σ st → Inv st ps →
      (f a).runPure st tc pc ps = .ok ((b, st'), ps') →
      Grows venv σ S st st' ps ps' ∧ Inv st' ps' ∧ Q a b st'.gdecls) →
    ∀ {st ps bs st' ps'}, StateOK venv σ st → Inv st ps →
      (l.mapM f).runPure st tc pc ps = .ok ((bs, st'), ps') →
      Grows venv σ S st st' ps ps' ∧ Inv st' ps' ∧ bs.length = l.length ∧
        ∀ (j : Nat) (a : α), l[j]? = some a → ∃ b, bs[j]? = some b ∧ Q a b st'.gdecls
  | [], _, st, ps, bs, st', ps', hok, hinv, h => by
    cases h
    exact ⟨.refl hok, hinv, rfl, fun j a h => nomatch h⟩
  | a :: l, hf, st, ps, bs, st', ps', hok, hinv, h => by
    rw [List.mapM_cons, runPure_bind] at h
    replace h := Except.ok_of_bind h
    obtain ⟨⟨⟨b, st₁⟩, ps₁⟩, h1, h⟩ := h
    rw [runPure_bind] at h
    replace h := Except.ok_of_bind h
    obtain ⟨⟨⟨bs', st₂⟩, ps₂⟩, h2, h⟩ := h
    cases h
    obtain ⟨hg1, hinv1, hq1⟩ := hf a (.head _) hok hinv h1
    obtain ⟨hg2, hinv2, hlen, hq2⟩ :=
      mapM_run (S := S) (Inv := Inv) (Q := Q) hQ l
        (fun a' ha' {_ _ _ _ _} hs hi hr => hf a' (.tail _ ha') hs hi hr) hg1.ok hinv1 h2
    refine ⟨hg1.trans hg2, hinv2, by simp [hlen], fun j a' ha' => ?_⟩
    cases j with
    | zero =>
      cases ha'
      exact ⟨b, rfl, hQ hg2.ext hq1⟩
    | succ j => exact hq2 j a' ha'

variable {view : EnvView} {cfg : ErasureConfig}

/-- A member of the block of an unregistered recursive constant `c` is unregistered: a registered
member would carry its block (`ErasesDecl`, `ErasesBlock`), whose entry for `c` contradicts the
freshness of `c`'s kername (`StateOK.fresh`). Reference: none (DV-7); blocks are added whole to
the environment (`erase_global_deps`, `MR E/ErasureFunction.v:1602`). -/
theorem StateOK.block_unregistered {st : ErasureState}
    (hok : StateOK venv (evalEnvOf view cfg decls) st) (hinj : KernameInj decls)
    {c n : Name} {cn : ConstantInfo} {w : Expr} (hc : (findDecl decls c).isSome)
    (hcn : st.constants[c]? = none) (hfn : findDecl decls n = some cn) (hcall : c ∈ cn.all)
    (hw : cn.value? (allowOpaque := true) = some w) (hax : axiomatized view cfg cn = false)
    (hrec : RecursiveDecl cn = true) : st.constants[n]? = none := by
  cases hk : st.constants[n]? with
  | none => rfl
  | some kn =>
    exfalso
    obtain ⟨-, ci', cb, hf', -, hd, -⟩ := hok.registered n kn hk
    have hf'' : findDecl decls n = some ci' := hf'
    rw [hfn] at hf''
    cases hf''
    unfold ErasesDecl at hd
    rw [hw] at hd
    rcases hd with ⟨hax', -⟩ | ⟨-, -, defs, i, -, -, hbl⟩ | ⟨-, hrec', -⟩
    · exact absurd hax' (by simp [evalEnvOf, hax])
    · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hcall
      obtain ⟨_, _, _, _, _, _, _, _, _, hlc⟩ := hbl.2 j c hj
      have hfr := hok.fresh (σ := evalEnvOf view cfg decls) hinj hc hcn
      unfold lookupConst at hlc
      rw [hfr] at hlc
      cases hlc
    · rw [hrec] at hrec'
      cases hrec'

/-- What `visitMutual` has computed for member `n` of a block whose members are `names` and whose
fix variables are `ids`: `n` is a declaration of the closure with a translated value `w`, the
definition `d` closes an erasure `r` of `w` (with the fix variables as the members' targets,
`rcBlock`) by `mkDef`'s loop, and `r`'s dependencies are erased in `lenv`. Reference: the premise
of `erases_tFix` (`MR E/Extract.v:122`) before the block is closed (DV-7, DV-13). -/
def BodyOK (venv : VEnv) (σ : EvalEnv) (names : List Name) (ids : List FVarId)
    (n : Name) (d : @FixDef LBTerm) (lenv : GlobalDeclarations) : Prop :=
  ∃ cn w w' r, findDecl σ.decls n = some cn ∧ cn.value? (allowOpaque := true) = some w ∧
    TrS venv cn.levelParams [] w w' ∧ d = ⟨fixDefName n, closeFix ids r, 0⟩ ∧
    Erases venv cn.levelParams σ.isAtom (rcBlock names ids) [] w r ∧ ErasesDeps venv σ lenv r

/-- `BodyOK` survives fresh growth of the λ□ environment. Reference: `erases_deps_cons`
(`MR E/EDeps.v:492`). -/
theorem BodyOK.ext {σ : EvalEnv} {names : List Name} {ids : List FVarId} {n : Name}
    {d : @FixDef LBTerm} {lenv lenv' : GlobalDeclarations} (hx : LenvExt lenv lenv')
    (h : BodyOK venv σ names ids n d lenv) : BodyOK venv σ names ids n d lenv' := by
  obtain ⟨cn, w, w', r, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨cn, w, w', r, h1, h2, h3, h4, h5, h6.ext hx⟩


/-- A list without repetitions stays so under a map that is injective on it. Reference: none. -/
theorem nodup_map_of_inj {α β : Type} {f : α → β} : ∀ {l : List α}, l.Nodup →
    (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → (l.map f).Nodup
  | [], _, _ => .nil
  | a :: l, h, hf => by
    rw [List.nodup_cons] at h
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_map_of_inj h.2 fun x hx y hy => hf x (.tail _ hx) y (.tail _ hy)⟩
    obtain ⟨b, hb, hfb⟩ := List.mem_map.1 hm
    exact h.1 (hf b (.tail _ hb) a (.head _) hfb ▸ hb)

/-- The close of `visitMutual` on a recursive block (closing step 2 of the traversal's
correctness), from what its runs give: the members' values were erased into `defs` (`BodyOK`,
growing within `S` from the bookkeeping state `sb`, which has the registered constants and the
λ□ environment of `st`, and leaving the members unregistered), and the last loop registered each
member `names[j]` as `tFix defs j`. Each member's erasure `r` is closed and mentions only the fix
variables, so its closed body `closeFix ids r` is closed under the block's binders and has no
free variable; instantiated as `cunfold_fix` does, it is `substFVars (fixTargets ids defs) r`
(`closeFix_substl`), an erasure with the registered fixpoints as targets (`Erases.substRc`). So
the block is erased (`ErasesBlock`), every member's entry erases its declaration, the invariant
holds after the registration (`StateOK.grow`), and the whole run grows within `S` and registers
`c`. Reference: `erases_tFix` (`MR E/Extract.v:122`) and the `ConstantDecl` step of
`erase_global_deps` (`MR E/ErasureFunction.v:1602`), for Lean's environment-level recursion (DV-7)
closed with free variables (DV-13). -/
theorem block_finish (hG : CoreEnv venv P decls) {c : Name} {ci : ConstantInfo} {v : Expr}
    (hci : findDecl decls c = some ci) (hv : ci.value? (allowOpaque := true) = some v)
    (hax : axiomatized view cfg ci = false) (hrec : RecursiveDecl ci = true)
    {S : Name → Prop} (hsc : ScopeOK decls S) (hc : S c)
    {st sb st₁ st₂ : ErasureState} {ps ps₁ : PureState} {defs : List (@FixDef LBTerm)}
    (hcb : sb.constants = st.constants) (hgb : sb.gdecls = st.gdecls)
    (hbod : Grows venv (evalEnvOf view cfg decls) S sb st₁ ⟨ps.next + ci.all.length⟩ ps₁)
    (hun : ∀ n ∈ ci.all, st₁.constants[n]? = none)
    (hlen : defs.length = ci.all.length)
    (hdefs : ∀ (j : Nat) (n : Name), ci.all[j]? = some n → ∃ d, defs[j]? = some d ∧
      BodyOK venv (evalEnvOf view cfg decls) ci.all (freshIds ps.next ci.all.length) n d
        st₁.gdecls)
    (hc₂ : st₂.constants =
      ci.all.zipIdx.foldl (fun M x => M.insert x.1 (toKername x.1)) st₁.constants)
    (hg₂ : st₂.gdecls = (ci.all.zipIdx.map fun x => (toKername x.1,
        GlobalDecl.constantDecl ⟨some (.fix defs x.2)⟩)).reverse ++ st₁.gdecls) :
    Grows venv (evalEnvOf view cfg decls) S st st₂ ps ps₁ ∧ ∃ kn, st₂.constants[c]? = some kn := by
  have hci' : ci ∈ decls := List.mem_of_find?_eq_some hci
  have hciP : ci ∈ P := List.mem_of_find?_eq_some (hG.sub ci hci')
  have hname : ci.name = c := by simpa using List.find?_some hci
  have hnd : ci.all.Nodup := hG.prog.all_nodup hciP
  have hcall : c ∈ ci.all := hname ▸ hG.prog.name_mem_all hciP
  have hdep : ∀ n ∈ ci.all, (findDecl decls n).isSome := (hG.deps ci hci').2.2
  generalize hids : freshIds ps.next ci.all.length = ids at hdefs
  have hidsnd : ids.Nodup := hids ▸ freshIds_nodup _ _
  have hidslen : ids.length = defs.length := by rw [← hids, freshIds_length, hlen]
  -- the new entries: one per member, with distinct fresh kernames
  have hmap : ci.all.zipIdx.map Prod.fst = ci.all := List.zipIdx_map_fst 0 ci.all
  have hkeysEq : ((ci.all.zipIdx.map fun x => (toKername x.1,
      GlobalDecl.constantDecl ⟨some (.fix defs x.2)⟩)).reverse).map (·.1) =
      (ci.all.map toKername).reverse := by
    rw [List.map_reverse, List.map_map]
    congr 1
    rw [show ((·.1) ∘ fun x : Name × Nat => (toKername x.1,
      GlobalDecl.constantDecl ⟨some (.fix defs x.2)⟩)) = toKername ∘ Prod.fst from rfl,
      ← List.map_map, hmap]
  have hkeys : (((ci.all.zipIdx.map fun x => (toKername x.1,
      GlobalDecl.constantDecl ⟨some (.fix defs x.2)⟩)).reverse).map (·.1)).Nodup := by
    rw [hkeysEq, List.nodup_reverse]
    exact nodup_map_of_inj hnd fun a ha b hb h => hG.inj a b (hdep a ha) (hdep b hb) h
  have hmemNew : ∀ (j : Nat) (n : Name), ci.all[j]? = some n →
      (toKername n, GlobalDecl.constantDecl ⟨some (.fix defs j)⟩) ∈
        (ci.all.zipIdx.map fun x => (toKername x.1,
          GlobalDecl.constantDecl ⟨some (.fix defs x.2)⟩)).reverse :=
    fun j n hn => List.mem_reverse.2 (List.mem_map.2
      ⟨(n, j), List.mem_zipIdx_iff_getElem?.2 hn, rfl⟩)
  have hlook : ∀ (j : Nat) (n : Name), ci.all[j]? = some n →
      lookupConst st₂.gdecls (toKername n) = some ⟨some (.fix defs j)⟩ := by
    intro j n hn
    unfold lookupConst
    rw [hg₂, List.find?_append, find?_of_nodup hkeys (hmemNew j n hn)]
    rfl
  have hx : LenvExt st₁.gdecls st₂.gdecls := by
    refine ⟨_, hg₂, fun kn hkn => ?_⟩
    rw [hkeysEq, List.mem_reverse] at hkn
    obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hkn
    exact hbod.ok.fresh hG.inj (hdep n hn) (hun n hn)
  -- each member: its erasure is closed and mentions only the fix variables
  have hbody : ∀ (j : Nat) (n : Name), ci.all[j]? = some n → ∃ cn w r,
      findDecl decls n = some cn ∧ cn.value? (allowOpaque := true) = some w ∧
      defs[j]? = some ⟨fixDefName n, closeFix ids r, 0⟩ ∧
      Erases venv cn.levelParams (evalEnvOf view cfg decls).isAtom (rcBlock ci.all ids) [] w r ∧
      ErasesDeps venv (evalEnvOf view cfg decls) st₁.gdecls r ∧ closedn 0 r = true ∧
      (∀ y, hasFVar y r = true → y ∈ ids) ∧ FVarsIn (fun _ => False) w := by
    intro j n hn
    obtain ⟨d, hd, cn, w, w', r, hcn, hw, htr, rfl, her, hdeps⟩ := hdefs j n hn
    have hwcl : FVarsIn (fun _ => False) w :=
      (hG.closed cn (List.mem_of_find?_eq_some hcn)).2 w hw
    refine ⟨cn, w, r, hcn, hw, hd, her, hdeps, Erases.closed rcBlock_closed htr her,
      fun y hy => ?_, hwcl⟩
    refine Classical.byContradiction fun hyn => ?_
    have := Erases.hasFVar_eq_false (x := y) (fun c t ht => ?_) hwcl her
    · rw [hy] at this; cases this
    · obtain ⟨j', x, -, hx', rfl⟩ := ht
      simp only [hasFVar, beq_eq_false_iff_ne]
      rintro rfl
      exact hyn (List.mem_of_getElem? hx')
  have hdefsMem : ∀ d ∈ defs, ∃ (j : Nat) (n : Name), ci.all[j]? = some n ∧
      defs[j]? = some d := by
    intro d hd
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hd
    have hjl : j < ci.all.length := by
      rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hj).1
    exact ⟨j, ci.all[j], List.getElem?_eq_getElem hjl, hj⟩
  have hdefsC : ∀ d ∈ defs, closedn defs.length d.body = true := by
    intro d hd
    obtain ⟨j, n, hn, hj⟩ := hdefsMem d hd
    obtain ⟨cn, w, r, -, -, hd', -, -, hr, -, -⟩ := hbody j n hn
    rw [hj] at hd'
    cases hd'
    rw [← hidslen]
    exact closeFix_closed hr
  have hdefsF : ∀ d ∈ defs, (∀ x, hasFVar x d.body = false) ∧
      ErasesDeps venv (evalEnvOf view cfg decls) st₂.gdecls d.body := by
    intro d hd
    obtain ⟨j, n, hn, hj⟩ := hdefsMem d hd
    obtain ⟨cn, w, r, -, -, hd', -, hdeps, -, hfv, -⟩ := hbody j n hn
    rw [hj] at hd'
    cases hd'
    exact ⟨closeFix_hasFVar hidsnd hfv, (hdeps.ext hx).closeFix ids⟩
  -- the block is erased in the final environment
  have hblock : ErasesBlock venv (evalEnvOf view cfg decls) st₂.gdecls ci.all defs := by
    refine ⟨hlen.symm, fun j n hn => ?_⟩
    obtain ⟨cn, w, r, hcn, hw, hd, her, -, hr, -, hwcl⟩ := hbody j n hn
    refine ⟨cn, w, _, hcn, hw, hd, rfl, rfl, ?_, hlook j n hn⟩
    show Erases venv cn.levelParams _ _ [] w (substl (fixSubst defs) (closeFix ids r))
    rw [closeFix_substl hr hidsnd hidslen hdefsC]
    exact Erases.substRc (hwcl.mono fun _ h => h.elim) (rcBlock_hrc hidsnd hlook) her
  -- the registration keeps the invariant
  have hlookC : ∀ c' : Name, st₂.constants[c']? =
      if c' ∈ ci.all then some (toKername c') else st₁.constants[c']? := by
    intro c'
    rw [hc₂, foldl_insert_getElem?, hmap]
  obtain ⟨hok₂, -⟩ := StateOK.grow (σ := evalEnvOf view cfg decls) hbod.ok hG.inj hg₂
    (fun c' kn h => by
      rw [hlookC]
      split
      · rename_i hc'
        rw [hun c' hc'] at h; cases h
      · exact h)
    (fun d hd => by
      obtain ⟨⟨n, j⟩, hnj, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hd)
      have hn : n ∈ ci.all := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.1 hnj)
      exact ⟨n, hun n hn, by rw [hlookC, if_pos hn]⟩)
    (fun c' kn h0 h1 => by
      rw [hlookC] at h1
      split at h1
      · rename_i hc'
        cases h1
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hc'
        obtain ⟨cn, w, hcn, hcnall, hw, hax', hrec'⟩ := hG.member hci hv hax hrec hc'
        have hcname : cn.name = c' := by simpa using List.find?_some hcn
        refine ⟨rfl, cn, ⟨some (.fix defs j)⟩, hcn, hlook j c' hj, ?_, fun b hb => ?_⟩
        · unfold ErasesDecl
          rw [hw]
          exact .inr (.inl ⟨hax', hrec', defs, j, rfl, by rw [hcnall, hcname]; exact hj,
            by rw [hcnall]; exact hblock⟩)
        · cases hb
          refine ⟨.fix fun d hd => (hdefsF d hd).2, ?_, fun x => ?_⟩
          · simp only [closedn, Nat.zero_add]
            exact closednD_of_forall hdefsC
          · simp only [hasFVar]
            exact hasFVarD_of_forall fun d hd => (hdefsF d hd).1 x
      · rw [h0] at h1; cases h1)
  refine ⟨⟨hok₂, ?_, ?_, fun c' kn h0 h1 => ?_⟩, toKername c, by rw [hlookC, if_pos hcall]⟩
  · rw [← hgb]
    exact hbod.ext.trans hx
  · have := hbod.next
    dsimp only at this
    omega
  · rw [hlookC] at h1
    split at h1
    · rename_i hc'
      obtain ⟨ci₀, hci₀, hS, -⟩ := hsc c hc
      rw [hci] at hci₀
      cases hci₀
      exact hS c' hc'
    · exact hbod.scope c' kn (by rw [hcb]; exact h0) h1


/-! ## The runs of `visitMutual` on a recursive block -/

/-- `Erasure.getConst` at the pure backend returns the declaration found in the closure, without
changing the states. Reference: `lookup_env` (`MR common/theories/Environment.v:483`). -/
theorem getConst_run {pc : PureCtx} {tc : TravCtx} {st : ErasureState} {ps : PureState} {n : Name}
    {cn : ConstantInfo} (h : findDecl pc.decls n = some cn) :
    (getConst (m := PureM) n).runPure st tc pc ps = .ok ((cn, st), ps) := by
  unfold getConst
  rw [runPure_bind, runPure_liftM]
  have : ((Backend.findConst? (m := PureM) n).run pc).run ps = .ok (some cn, ps) := by
    show Except.ok (findConst pc.decls n, ps) = _; rw [show findConst pc.decls n = _ from h]
  rw [this]
  rfl

/-- The pure backend's `prepare` returns its term (S-F). Reference: none. -/
theorem prepare_run {pc : PureCtx} {tc : TravCtx} {st : ErasureState} {ps : PureState}
    {cfg' : ErasureConfig} {e : Expr} :
    (liftM (Backend.prepare (m := PureM) cfg' e) : EraseT PureM Expr).runPure st tc pc ps =
      .ok ((e, st), ps) := rfl

/-- At the pure backend, `visitMutual` does not rename the members (`remove_unsafe_rec` is the
identity). Reference: none (S-F). -/
theorem map_remove_unsafe_rec : ∀ (l : List Name), l.map (remove_unsafe_rec (m := PureM)) = l
  | [] => rfl
  | n :: l => by rw [List.map_cons, map_remove_unsafe_rec l]; rfl

/-- The erasure of one member's value inside the block (`visitMutual`'s `visitExpr fuel w`, from
`visitExpr` at the fuels up to `fuel`, `ih`): the value is visited under the caller's locals and
the block's fix variables, which is the run under no locals (`visit_agree`, the value is closed);
there, with the members' targets `rcBlock` (their fix variables, allocated below the counter),
the run erases the value in the empty context, grows within the scope `S`, and, run in a scope
that holds no member of the block (`CoreEnv.valueScope`), leaves every member unregistered.
Reference: the `tFix` case of `erases_erase` (`MR E/ErasureFunction.v:1228`), whose bodies are
erased in the context of the block's binders (`MR E/Extract.v:122 erases_tFix`), here fix
variables (DV-7, DV-13). -/
theorem body_step (hG : CoreEnv venv P decls) {fuel : Nat}
    (ih : ∀ m ≤ fuel, ∀ e, ExprSpec venv view cfg decls m e)
    {names : List Name} {ids : List FVarId} (hnd : names.Nodup) (hlen : names.length = ids.length)
    {p₁ : Nat} (hids : ∀ x ∈ ids, ∃ k, k < p₁ ∧ x = pureFVar k)
    {S : Name → Prop} (hsc : ScopeOK decls S) (hS : ∀ n ∈ names, S n)
    {n : Name} {cn : ConstantInfo} {w : Expr} (hn : n ∈ names) (hcn : findDecl decls n = some cn)
    (hcall : cn.all = names) (hw : cn.value? (allowOpaque := true) = some w)
    {tc : TravCtx} (hfix : tc.fixvars = some (Std.HashMap.ofList (names.zip ids)))
    (hcfg : tc.config = cfg) {st st' : ErasureState} {ps ps' : PureState} {t : LBTerm}
    (hok : StateOK venv (evalEnvOf view cfg decls) st)
    (hun : ∀ n' ∈ names, st.constants[n']? = none) (hp : p₁ ≤ ps.next)
    (h : (visitExpr (m := PureM) fuel w).runPure st tc ⟨decls, view⟩ ps = .ok ((t, st'), ps')) :
    Grows venv (evalEnvOf view cfg decls) S st st' ps ps' ∧
      (∀ n' ∈ names, st'.constants[n']? = none) ∧ (∃ w', TrS venv cn.levelParams [] w w') ∧
      Erases venv cn.levelParams (evalEnvOf view cfg decls).isAtom (rcBlock names ids) [] w t ∧
      ErasesDeps venv (evalEnvOf view cfg decls) st'.gdecls t := by
  have hcn' : cn ∈ decls := List.mem_of_find?_eq_some hcn
  have hcnP : cn ∈ P := List.mem_of_find?_eq_some (hG.sub cn hcn')
  have hwcl : FVarsIn (fun _ => False) w := (hG.closed cn hcn').2 w hw
  obtain ⟨w', htr⟩ := hG.prog.value_tr hcnP hw
  have h' : (visitExpr (m := PureM) fuel w).runPure st { tc with locals := [] } ⟨decls, view⟩ ps =
      .ok ((t, st'), ps') := by
    rw [← h]
    exact (visit_agree (S := fun _ => False) (pc := ⟨decls, view⟩) (tc := tc) (ls₁ := tc.locals)
      (ls₂ := []) hG.closed (fun _ h => h.elim) (fun _ h => h.elim) hwcl).symm
  have hctx : CtxOK venv cn.levelParams (rcBlock names ids) cfg { tc with locals := [] } [] ps := by
    refine ⟨.nil, (fun _ _ h => nomatch h), fun c t ht => ?_,
      fun c x hx => fixvars_rcBlock hnd hlen c x (by rw [← hfix]; exact hx), hcfg⟩
    obtain ⟨j, x, -, hx, rfl⟩ := ht
    obtain ⟨k, hk, rfl⟩ := hids x (List.mem_of_getElem? hx)
    refine ⟨rfl, fun k' hk' => ?_⟩
    simp only [hasFVar, beq_eq_false_iff_ne]
    intro heq
    have := pureFVar_inj heq
    omega
  have ⟨her, hdeps, hgr⟩ := ih fuel (Nat.le_refl _) w hctx hsc
    (fun d hd => .inl (by
      obtain ⟨cn₀, hcn₀, -, hval⟩ := hsc n (hS n hn)
      rw [hcn] at hcn₀
      cases hcn₀
      exact hval w hw d hd)) hok htr h'
  obtain ⟨S', hsc', hvS', hcS'⟩ := hG.valueScope hcn hw
  obtain ⟨-, -, hgr'⟩ := ih fuel (Nat.le_refl _) w hctx hsc'
    (fun d hd => (hvS' d hd).elim
      (fun hm => .inr (by
        show (tc.fixvars.bind fun m => m[d]?).isSome
        rw [hfix]
        exact fixvars_isSome hnd hlen (hcall ▸ hm)))
      .inl) hok htr h'
  refine ⟨hgr, fun n' hn' => ?_, ⟨w', htr⟩, her, hdeps⟩
  cases h1 : st'.constants[n']? with
  | none => rfl
  | some kn => exact absurd (hgr'.scope n' kn (hun n' hn') h1) (hcS' n' (hcall ▸ hn'))

/-- `visitMutual`'s recursive branch at the pure backend, from the state `sb` its bookkeeping
leaves (the registered constants and λ□ environment of `st`), on a recursive, non-remapped
declaration `ci` of `c` with a value: the allocation of the fix variables (`freshIds_run`), the
erasure of every member's value (`body_step`, over `mapM_run`), `mkDef` (`mkDef_run`, the loop
`closeFix` of the fix variables), and the registration loop, whose body `B` registers member
`names[j]` as `tFix defs j` and otherwise keeps the state (`forIn_register`); `block_finish`
closes. Reference: the `tFix` case of `erases_erase` (`MR E/ErasureFunction.v:1228`) and the
`ConstantDecl` step of `erase_global_deps` (`MR E/ErasureFunction.v:1602`) (DV-7, DV-13). -/
theorem visitMutual_block_run (hG : CoreEnv venv P decls) {fuel : Nat}
    (ih : ∀ m ≤ fuel, ∀ e, ExprSpec venv view cfg decls m e) {c : Name} {ci : ConstantInfo}
    {v : Expr} (hci : findDecl decls c = some ci) (hv : ci.value? (allowOpaque := true) = some v)
    (hax : axiomatized view cfg ci = false) (hrec : RecursiveDecl ci = true)
    {S : Name → Prop} (hsc : ScopeOK decls S) (hc : S c)
    {st sb st' : ErasureState} {tc : TravCtx} {ps ps' : PureState}
    (hcfg : tc.config = cfg) (hok : StateOK venv (evalEnvOf view cfg decls) st)
    (hnew : st.constants[c]? = none)
    (hcb : sb.constants = st.constants) (hgb : sb.gdecls = st.gdecls)
    {B : List (@FixDef LBTerm) → Name × Nat → PUnit → EraseT PureM (ForInStep PUnit)}
    (hB : ∀ defs x u {st₀ : ErasureState} {tc₀ : TravCtx} {ps₀ : PureState}
      {r : ForInStep PUnit} {st₀' : ErasureState} {ps₀' : PureState},
      (B defs x u).runPure st₀ tc₀ ⟨decls, view⟩ ps₀ = .ok ((r, st₀'), ps₀') →
      r = .yield PUnit.unit ∧ st₀'.constants = st₀.constants.insert x.1 (toKername x.1) ∧
      st₀'.gdecls = (toKername x.1, .constantDecl ⟨some (.fix defs x.2)⟩) :: st₀.gdecls ∧
      ps₀' = ps₀)
    (hrun : (do
        let ids ← ci.all.mapM (fun _ =>
          (liftM (Backend.freshFVarId (m := PureM)) : EraseT PureM FVarId))
        withReader (fun env => { env with fixvars := some (Std.HashMap.ofList
            ((ci.all.map (remove_unsafe_rec (m := PureM))).zip ids)) }) do
          let defs ← ci.all.mapM (fun n => do
            let ci₁ ← getConst (m := PureM) n
            let cx ← read
            let e ← (liftM (Backend.prepare (m := PureM) cx.config
              (ci₁.value! (allowOpaque := true))) : EraseT PureM Expr)
            let t ← visitExpr (m := PureM) fuel e
            mkDef (m := PureM) (remove_unsafe_rec (m := PureM) n)
              (ci.all.map (remove_unsafe_rec (m := PureM))) t)
          forIn (ci.all.map (remove_unsafe_rec (m := PureM))).zipIdx PUnit.unit (B defs)
          pure () : EraseT PureM Unit).runPure sb tc ⟨decls, view⟩ ps = .ok (((), st'), ps')) :
    Grows venv (evalEnvOf view cfg decls) S st st' ps ps' ∧ ∃ kn, st'.constants[c]? = some kn := by
  have hci' : ci ∈ decls := List.mem_of_find?_eq_some hci
  have hciP : ci ∈ P := List.mem_of_find?_eq_some (hG.sub ci hci')
  have hname : ci.name = c := by simpa using List.find?_some hci
  have hnd : ci.all.Nodup := hG.prog.all_nodup hciP
  have hS : ∀ n ∈ ci.all, S n := by
    obtain ⟨ci₀, hci₀, hS, -⟩ := hsc c hc
    rw [hci] at hci₀
    cases hci₀
    exact hS
  rw [map_remove_unsafe_rec] at hrun
  rw [runPure_bind, freshIds_run, Except.ok_bind'] at hrun
  dsimp only at hrun
  rw [runPure_withReader, runPure_bind] at hrun
  replace hrun := Except.ok_of_bind hrun
  obtain ⟨⟨⟨defs, st₁⟩, ps₁⟩, hdefs, hrun⟩ := hrun
  rw [runPure_bind] at hrun
  replace hrun := Except.ok_of_bind hrun
  obtain ⟨⟨⟨u, st₂⟩, ps₂⟩, hloop, hrun⟩ := hrun
  cases hrun
  obtain ⟨hc₂, hg₂, rfl⟩ :=
    forIn_register (fun x u {_ _ _ _ _} h => hB defs x u h) _ hloop
  have hlenids : ci.all.length = (freshIds ps.next ci.all.length).length :=
    (freshIds_length _ _).symm
  have hun0 : ∀ n ∈ ci.all, sb.constants[n]? = none := by
    intro n hn
    obtain ⟨cn, w, hcn, hcall, hw, hax', hrec'⟩ := hG.member hci hv hax hrec hn
    rw [hcb]
    exact hok.block_unregistered hG.inj (by rw [hci]; rfl) hnew hcn
      (by rw [hcall, ← hname]; exact hG.prog.name_mem_all hciP) hw hax' hrec'
  obtain ⟨hgr, ⟨hun, -⟩, hlen, hQ⟩ := mapM_run (σ := evalEnvOf view cfg decls) (S := S)
    (Inv := fun s p => (∀ n ∈ ci.all, s.constants[n]? = none) ∧
      ps.next + ci.all.length ≤ p.next)
    (Q := fun n d lenv => BodyOK venv (evalEnvOf view cfg decls) ci.all
      (freshIds ps.next ci.all.length) n d lenv)
    (fun hx h => h.ext hx) ci.all
    (fun n hn {s p d s' p'} hs hinv h => by
      obtain ⟨hu, hp⟩ := hinv
      obtain ⟨cn, w, hcn, hcall, hw, -, -⟩ := hG.member hci hv hax hrec hn
      rw [runPure_bind, getConst_run hcn, Except.ok_bind'] at h
      dsimp only at h
      rw [runPure_read_bind, runPure_bind, prepare_run, Except.ok_bind'] at h
      dsimp only at h
      rw [runPure_bind] at h
      replace h := Except.ok_of_bind h
      obtain ⟨⟨⟨t, s₁⟩, p₁⟩, hvis, h⟩ := h
      rw [mkDef_run _ _ _ rfl, ofList_zip_getElem! hnd hlenids] at h
      cases h
      have hval : cn.value! (allowOpaque := true) = w := by rw [value!_eq, hw]; rfl
      rw [hval] at hvis
      obtain ⟨hgr, hun', ⟨w', htr⟩, her, hdeps⟩ := body_step hG ih hnd hlenids
        (fun x hx => by
          obtain ⟨k, -, hk, rfl⟩ := mem_freshIds hx
          exact ⟨k, hk, rfl⟩)
        hsc hS hn hcn hcall hw (tc := { tc with fixvars := some (Std.HashMap.ofList
          (ci.all.zip (freshIds ps.next ci.all.length))) }) rfl hcfg hs hu hp hvis
      exact ⟨hgr, ⟨hun', Nat.le_trans hp hgr.next⟩, cn, w, w', t, hcn, hw, htr, rfl, her, hdeps⟩)
    (hok.congr hcb hgb) ⟨hun0, Nat.le_refl _⟩ hdefs
  exact block_finish hG hci hv hax hrec hsc hc hcb hgb hgr hun hlen hQ hc₂ hg₂


/-- At the pure backend, `visitMutual`'s test `!(single_decl && !name_occurs name value)` on a
declaration `ci` is the shipping `Erasure.isRecursiveDecl ci` (the regression test
`tests/regress/pure_backend.lean` checks the same). Reference: none (DV-7). -/
theorem visitMutual_test (ci : ConstantInfo) :
    (!(ci.all.length == 1 &&
      !name_occurs (m := PureM) ci.name (ci.value! (allowOpaque := true)))) =
      isRecursiveDecl ci := by
  rw [name_occurs_eq, isRecursiveDecl, bne]
  cases ci.all.length == 1 <;> cases nameOccurs ci.name (ci.value! (allowOpaque := true)) <;> rfl

/-- The recursive `const` step of `erasePure_erases`, from `visitExpr` at the fuels up to `fuel`
(`ih`): `visitMutual` on a declaration that is a recursive (`RecursiveDecl`, which is
`visitMutual`'s own test by `visitMutual_test` and `isRecursiveDecl_eq`), non-remapped definition
with a value. After the bookkeeping of a single declaration (`@[inline]`, the `@[extern]` test,
which keeps it since it is not remapped), `visitMutual` erases the whole block
(`visitMutual_block_run`): every member's value, with the members' occurrences sent to fresh fix
variables, closed by `mkDef`, and every member registered as `tFix defs j` of the erased block
(`ErasesBlock`); the run grows within the scope and registers `c`. Reference: the `tFix` case of
`erases_erase` (`MR E/ErasureFunction.v:1228`), rule `erases_tFix` (`MR E/Extract.v:122`), and
the `ConstantDecl` step of `erase_global_deps` (`MR E/ErasureFunction.v:1602`), for Lean's
environment-level recursion (DV-7) closed with free variables (DV-13). -/
theorem visitMutual_rec_step (hG : CoreEnv venv P decls) {fuel : Nat}
    (ih : ∀ m ≤ fuel, ∀ e, ExprSpec venv view cfg decls m e) {c : Name} {ci : ConstantInfo}
    {v : Expr} (hci : findDecl decls c = some ci) (hv : ci.value? (allowOpaque := true) = some v)
    (hax : axiomatized view cfg ci = false) (hrec : RecursiveDecl ci = true) :
    MutualSpec venv view cfg decls (fuel + 1) c := by
  intro S st tc ps st' ps' hsc hc hcfg hok hnew hrun
  have hname : ci.name = c := by simpa using List.find?_some hci
  -- `visitMutual`'s test: the declaration is recursive
  have htest : (ci.all.length == 1 &&
      !name_occurs (m := PureM) c (ci.value! (allowOpaque := true))) = false := by
    have h := visitMutual_test ci
    rw [isRecursiveDecl_eq, hrec, hname] at h
    cases hb : (ci.all.length == 1 &&
      !name_occurs (m := PureM) c (ci.value! (allowOpaque := true)))
    · rfl
    · rw [hb] at h; cases h
  rw [visitMutual, runPure_bind] at hrun
  rw [show (liftM (Backend.declInfo? (m := PureM) c) : EraseT PureM _).runPure st tc
    ⟨decls, view⟩ ps = .ok ((some ci, st), ps) by
      show Except.ok ((findConst decls c, st), ps) = _; rw [show findConst decls c = _ from hci],
    Except.ok_bind'] at hrun
  dsimp only at hrun
  rw [runPure_bind, show (liftM (Backend.inlineAttr? (m := PureM) c) : EraseT PureM _).runPure st
    tc ⟨decls, view⟩ ps = .ok ((view.inlineAttr? c, st), ps) from rfl, Except.ok_bind'] at hrun
  dsimp only at hrun
  rw [runPure_bind, show (liftM (Backend.inlineAttr? (m := PureM) c) : EraseT PureM _).runPure st
    tc ⟨decls, view⟩ ps = .ok ((view.inlineAttr? c, st), ps) from rfl, Except.ok_bind'] at hrun
  dsimp only at hrun
  by_cases hall : ci.all.length = 1
  · -- a single declaration: its bookkeeping, then the block of one member
    have hocc : name_occurs (m := PureM) c (ci.value! (allowOpaque := true)) = true := by
      rw [hall] at htest
      simpa using htest
    simp only [Option.get!_some, hall, beq_self_eq_true, Bool.true_and, ↓reduceIte] at hrun
    -- the `@[inline]` bookkeeping before the value touches only `inlinings`
    rcases hia : view.inlineAttr? c with _ | ⟨_ | _ | _ | _ | _⟩ <;>
      simp only [hia, ↓reduceIte, Bool.false_eq_true] at hrun
    all_goals first
      | (rw [runPure_bind] at hrun
         replace hrun := Except.ok_of_bind hrun
         obtain ⟨⟨⟨_, sa⟩, pa⟩, h1, hrun⟩ := hrun
         obtain ⟨ca, ga, hpa⟩ := KeepsCG.run (KeepsCG.log _) h1
         subst pa
         rw [runPure_bind] at hrun
         replace hrun := Except.ok_of_bind hrun
         obtain ⟨⟨⟨_, sb⟩, pb⟩, h2, hrun⟩ := hrun
         obtain ⟨cb, gb, hpb⟩ := KeepsCG.run (KeepsCG.modify fun _ => ⟨rfl, rfl⟩) h2
         subst pb
         have hcb : sb.constants = st.constants := cb.trans ca
         have hgb : sb.gdecls = st.gdecls := gb.trans ga
         clear ca ga cb gb h1 h2)
      | (obtain ⟨sb, hsb⟩ : ∃ sb, sb = st := ⟨st, rfl⟩
         rw [← hsb] at hrun
         have hcb : sb.constants = st.constants := by rw [hsb]
         have hgb : sb.gdecls = st.gdecls := by rw [hsb]
         clear hsb)
    -- the value and the `@[extern]` test
    all_goals
      rw [runPure_bind] at hrun
      replace hrun := Except.ok_of_bind hrun
      obtain ⟨⟨⟨_, sc⟩, pc'⟩, h1, hrun⟩ := hrun
      cases h1
      rw [runPure_read_bind, hcfg] at hrun
      dsimp only at hrun
    -- `cfg.1` is the configuration's `extern` policy
    all_goals
      rcases hv' : ci.value? (allowOpaque := true) with _ | v' <;> cases hie : view.isExtern c <;>
        cases hext : cfg.1 <;> simp only [hv', hie, hext] at hrun
    all_goals first
      | (rw [hv] at hv'; cases hv'; done)
      | (exfalso; revert hax; rw [axiomatized, hall, hname, hie, hext]; decide)
      | skip
    -- after the log of `@[extern]` with `preferLogical`
    all_goals first
      | (rw [runPure_bind] at hrun
         replace hrun := Except.ok_of_bind hrun
         obtain ⟨⟨⟨_, sd⟩, pd⟩, h1, hrun⟩ := hrun
         obtain ⟨cd, gd, hpd⟩ := KeepsCG.run (KeepsCG.log _) h1
         subst pd
         replace hcb := cd.trans hcb
         replace hgb := gd.trans hgb
         clear cd gd h1)
      | skip
    all_goals
      simp only [hocc, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hrun
      refine visitMutual_block_run hG ih hci hv hax hrec hsc hc hcfg hok hnew hcb hgb
        (fun defs x u st₀ tc₀ ps₀ r st₀' ps₀' h => ?_) hrun
      rw [runPure_bind] at h
      replace h := Except.ok_of_bind h
      obtain ⟨⟨⟨_, s₁⟩, p₁⟩, h1, h⟩ := h
      cases h1
      -- the `@[inline]` size bookkeeping of the registration loop touches only `inlinedSizes`
      cases h
      exact ⟨rfl, rfl, rfl, rfl⟩
  · -- a block of several members: no bookkeeping
    have hl : (ci.all.length == 1) = false := by simpa using hall
    simp only [Option.get!_some, hl, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hrun
    refine visitMutual_block_run hG ih hci hv hax hrec hsc hc hcfg hok hnew (sb := st) rfl rfl
      (fun defs x u st₀ tc₀ ps₀ r st₀' ps₀' h => ?_) hrun
    rw [runPure_bind] at h
    replace h := Except.ok_of_bind h
    obtain ⟨⟨⟨_, s₁⟩, p₁⟩, h1, h⟩ := h
    cases h1
    cases h
    exact ⟨rfl, rfl, rfl, rfl⟩


end EraseProof
