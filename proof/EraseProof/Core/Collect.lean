import EraseProof.Source.Restrict
import EraseProof.Oracle.Agree

/-!
# What `collectDeps` guarantees

`collectDeps_spec`: a successful run of the shipping `Erasure.collectDeps view e` returns
declarations that the view knows under their own names, with distinct names and distinct kernames,
closed under the dependencies of their members (`DepClosed`), with closed types and values
(`ClosedDecls`), and containing every constant of `e`. The proof reads the checks of the shipping
code: `exprConsts` succeeds only on terms without free variables, metavariables or level
metavariables and lists their constants; `closure` expands a name only when no accumulated
declaration has it and the view's declaration carries it, and a run that does not exhaust its fuel
has expanded every name of its work list; `findCollision` answers `none` only on declarations with
distinct kernames.
-/

open Lean Lean4Lean Erasure

namespace EraseProof

/-! ## Kernames -/

/-- The derived `BEq` of `ModPath` is reflexive. Reference: none (`reflect_kername`,
`MR common/theories/Kernames.v:325`, is Rocq's decidable equality of kernames). -/
theorem modPath_beq_self : ∀ m : ModPath, instBEqModPath.beq m m = true
  | .MPfile dp => by rw [instBEqModPath.beq.eq_1]; exact beq_self_eq_true dp
  | .MPdot mp id => by
    rw [instBEqModPath.beq.eq_2, modPath_beq_self mp, beq_self_eq_true id]; rfl

/-- The derived `BEq` of `Kername`, the one `findCollision` uses, is reflexive. Reference: none
(`reflect_kername`, `MR common/theories/Kernames.v:325`). -/
theorem kername_beq_self (k : Kername) : (k == k) = true := by
  obtain ⟨mp, id⟩ := k
  show instBEqKername.beq _ _ = true
  simp only [instBEqKername.beq]
  show (instBEqModPath.beq mp mp && id == id) = true
  rw [modPath_beq_self, beq_self_eq_true id]; rfl

/-- When `findCollision` finds no collision, two declarations of the list with the same kername
have the same name. Reference: none (the collision check of `collectDeps`, DV-14). -/
theorem findCollision_eq_none : ∀ {decls : List ConstantInfo}, findCollision decls = none →
    ∀ a ∈ decls, ∀ b ∈ decls, toKername a.name = toKername b.name → a.name = b.name
  | [], _, _, ha, _, _, _ => nomatch ha
  | ci :: cs, h, a, ha, b, hb, hk => by
    rw [findCollision.eq_2] at h
    split at h
    · cases h
    · rename_i hfind
      have hne : ∀ d ∈ cs, toKername d.name ≠ toKername ci.name := fun d hd hdk =>
        List.find?_eq_none.mp hfind d hd (by rw [hdk]; exact kername_beq_self _)
      rcases List.mem_cons.mp ha with ha | ha <;> rcases List.mem_cons.mp hb with hb | hb
      · rw [ha, hb]
      · rw [ha] at hk; exact absurd hk.symm (hne b hb)
      · rw [hb] at hk; exact absurd hk (hne a ha)
      · exact findCollision_eq_none h a ha b hb hk

/-- `findDecl` finds a name exactly when some declaration of the list has it. Reference: none (a
property of `findDecl`, i.e. `lookup_env`, `MR common/theories/Environment.v:483`). -/
theorem findDecl_isSome_iff {decls : List ConstantInfo} {c : Name} :
    (findDecl decls c).isSome ↔ c ∈ decls.map (·.name) := by
  simp only [findDecl, List.find?_isSome, beq_iff_eq, List.mem_map]

/-- Declarations whose kernames `findCollision` finds distinct satisfy `KernameInj`. Reference:
none (DV-14). -/
theorem KernameInj.of_findCollision {decls : List ConstantInfo} (h : findCollision decls = none) :
    KernameInj decls := by
  intro c₁ c₂ h₁ h₂ hk
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (findDecl_isSome_iff.mp h₁)
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp (findDecl_isSome_iff.mp h₂)
  exact findCollision_eq_none h a ha b hb hk

/-! ## The fragment scan -/

/-- A successful `exprConsts` lists every constant of the term, and the term has no free variable,
metavariable or level metavariable. Reference: `term_global_deps` (`MR E/EAstUtils.v:406`), on
the source side; closed PCUIC terms (DV-13). -/
theorem exprConsts_ok {e : Expr} {cs : List Name} (h : exprConsts e = .ok cs) :
    ConstsIn (· ∈ cs) e ∧ FVarsIn (fun _ => False) e := by
  induction e generalizing cs with
  | bvar => exact ⟨trivial, trivial⟩
  | fvar | mvar | lit | proj => nomatch h
  | sort u =>
    rw [exprConsts.eq_4] at h
    split at h
    · cases h
    · rename_i hu
      exact ⟨trivial, by simpa [FVarsIn] using hu⟩
  | const c us =>
    rw [exprConsts.eq_5] at h
    split at h
    · cases h
    · rename_i hus
      cases h
      refine ⟨List.mem_singleton_self c, fun u hu => ?_⟩
      simp only [List.any_eq_true, not_exists, not_and, Bool.not_eq_true] at hus
      exact hus u hu
  | app f a ihf iha =>
    rw [exprConsts.eq_6] at h
    obtain ⟨xs, hf, h⟩ := Except.ok_of_bind h
    obtain ⟨ys, ha, h⟩ := Except.ok_of_bind h
    cases h
    have ihf := ihf hf
    have iha := iha ha
    exact ⟨⟨ihf.1.mono fun _ h => List.mem_append_left _ h,
      iha.1.mono fun _ h => List.mem_append_right _ h⟩, ihf.2, iha.2⟩
  | lam _ t b _ iht ihb | forallE _ t b _ iht ihb =>
    first | rw [exprConsts.eq_7] at h | rw [exprConsts.eq_8] at h
    obtain ⟨xs, ht, h⟩ := Except.ok_of_bind h
    obtain ⟨ys, hb, h⟩ := Except.ok_of_bind h
    cases h
    have iht := iht ht
    have ihb := ihb hb
    exact ⟨⟨iht.1.mono fun _ h => List.mem_append_left _ h,
      ihb.1.mono fun _ h => List.mem_append_right _ h⟩, iht.2, ihb.2⟩
  | letE _ t v b _ iht ihv ihb =>
    rw [exprConsts.eq_9] at h
    obtain ⟨xs, ht, h⟩ := Except.ok_of_bind h
    obtain ⟨ys, hv, h⟩ := Except.ok_of_bind h
    obtain ⟨zs, hb, h⟩ := Except.ok_of_bind h
    cases h
    have iht := iht ht
    have ihv := ihv hv
    have ihb := ihb hb
    exact ⟨⟨iht.1.mono fun _ h => by simp [h], ihv.1.mono fun _ h => by simp [h],
      ihb.1.mono fun _ h => by simp [h]⟩, iht.2, ihv.2, ihb.2⟩
  | mdata _ e ih =>
    rw [exprConsts.eq_11] at h
    exact ih h

/-- A successful `declDeps` lists every constant of the declaration's type and value and every
member of its block except possibly itself, and the type and value are closed. Reference: the
dependencies `MR E/ErasureFunction.v:1602 erase_global_deps` follows. -/
theorem declDeps_ok {ci : ConstantInfo} {ds : List Name} (h : declDeps ci = .ok ds) :
    (ConstsIn (· ∈ ds) ci.type ∧ FVarsIn (fun _ => False) ci.type) ∧
    (∀ v, ci.value? (allowOpaque := true) = some v →
      ConstsIn (· ∈ ds) v ∧ FVarsIn (fun _ => False) v) ∧
    ∀ n ∈ ci.all, n ∈ ds ∨ n = ci.name := by
  cases ci with
  | axiomInfo v =>
    rw [declDeps.eq_1] at h
    refine ⟨exprConsts_ok h, fun _ hv => by simp [ConstantInfo.value?] at hv, fun n hn => ?_⟩
    exact Or.inr (by simpa [ConstantInfo.all] using hn)
  | defnInfo v | thmInfo v | opaqueInfo v =>
    obtain ⟨xs, ht, h⟩ := Except.ok_of_bind h
    obtain ⟨ys, hv, h⟩ := Except.ok_of_bind h
    cases h
    have iht := exprConsts_ok ht
    have ihv := exprConsts_ok hv
    refine ⟨⟨iht.1.mono fun _ h => by simp [h], iht.2⟩, fun w hw => ?_,
      fun n hn => .inl (by simp_all [ConstantInfo.all])⟩
    simp only [ConstantInfo.value?, ite_true, Option.some.injEq] at hw
    subst hw
    exact ⟨ihv.1.mono fun _ h => by simp [h], ihv.2⟩
  | quotInfo _ | inductInfo _ | ctorInfo _ | recInfo _ => nomatch h

/-! ## The closure -/

/-- What a successful run of `closure` returns: the accumulator extended by new declarations,
containing every name of the work list; each new declaration is the view's declaration of its own
name and has its dependencies (`declDeps`) in the result; and names stay distinct. Reference: the
closure property of `MR E/ErasureFunction.v:1602 erase_global_deps`. -/
theorem closure_ok {view : EnvView} : ∀ {f : Nat} {todo : List Name} {acc res : List ConstantInfo},
    closure view f todo acc = .ok res →
    ∃ new, res = new ++ acc ∧ (∀ n ∈ todo, n ∈ res.map (·.name)) ∧
      (∀ ci ∈ new, view.find? ci.name = some ci ∧
        ∃ ds, declDeps ci = .ok ds ∧ ∀ n ∈ ds, n ∈ res.map (·.name)) ∧
      ((acc.map (·.name)).Nodup → (res.map (·.name)).Nodup)
  | 0, _, _, _, h => by rw [closure.eq_1] at h; cases h
  | _+1, [], acc, res, h => by
    rw [closure.eq_2] at h
    cases h
    exact ⟨[], rfl, nofun, nofun, id⟩
  | f+1, n :: todo, acc, res, h => by
    rw [closure.eq_3] at h
    split at h
    · rename_i hany
      obtain ⟨new, rfl, htodo, hnew, hnd⟩ := closure_ok h
      refine ⟨new, rfl, fun m hm => ?_, hnew, hnd⟩
      rcases List.mem_cons.mp hm with rfl | hm
      · obtain ⟨a, ha, han⟩ := List.any_eq_true.mp hany
        exact List.mem_map.mpr ⟨a, List.mem_append_right _ ha, beq_iff_eq.mp han⟩
      · exact htodo m hm
    · rename_i hany
      split at h
      · cases h
      · rename_i ci hfind
        split at h
        · cases h
        · rename_i hname
          simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hname
          subst hname
          obtain ⟨ds, hds, h⟩ := Except.ok_of_bind h
          obtain ⟨new, rfl, htodo, hnew, hnd⟩ := closure_ok h
          have hci : ci.name ∈ (new ++ ci :: acc).map (·.name) := by simp
          refine ⟨new ++ [ci], by simp, fun m hm => ?_, fun cj hcj => ?_, fun hacc => hnd ?_⟩
          · rcases List.mem_cons.mp hm with rfl | hm
            · exact hci
            · exact htodo m (List.mem_append_right _ hm)
          · rcases List.mem_append.mp hcj with hcj | hcj
            · exact hnew cj hcj
            · rw [List.mem_singleton.mp hcj]
              exact ⟨hfind, ds, hds, fun m hm => htodo m (List.mem_append_left _ hm)⟩
          · refine List.nodup_cons.mpr ⟨fun hmem => hany ?_, hacc⟩
            obtain ⟨a, ha, han⟩ := List.mem_map.mp hmem
            exact List.any_eq_true.mpr ⟨a, ha, beq_iff_eq.mpr han⟩

section
variable {decls : List ConstantInfo}

/-- What `collectDeps` guarantees about the environment it returns, for every view. Reference:
the closure and naming properties of `erase_global_deps` (`MR E/ErasureFunction.v:1602`) that
`erase_correct` (`MR E/ErasureFunctionProperties.v:657`) relies on; DV-3, DV-14. -/
theorem collectDeps_spec {view : EnvView} (h : collectDeps view e = .ok decls) :
    KernameInj decls ∧ (∀ ci ∈ decls, view.find? ci.name = some ci) ∧
    (decls.map (·.name)).Nodup ∧ DepClosed decls ∧ ClosedDecls decls ∧
    ConstsIn (fun c => (findDecl decls c).isSome) e := by
  have key : ∃ cs, exprConsts e = .ok cs ∧ closure view collectFuel cs [] = .ok decls ∧
      findCollision decls = none := by
    rw [collectDeps.eq_1] at h
    obtain ⟨cs, hcs, h⟩ := Except.ok_of_bind h
    obtain ⟨res, hres, h⟩ := Except.ok_of_bind h
    split at h
    · cases h
    · rename_i hcol
      cases h
      exact ⟨cs, hcs, hres, hcol⟩
  obtain ⟨cs, hcs, hres, hcol⟩ := key
  obtain ⟨new, hnew, htodo, hdeps, hnd⟩ := closure_ok hres
  rw [List.append_nil] at hnew
  subst new
  have hin : ∀ {ds : List Name}, (∀ n ∈ ds, n ∈ decls.map (·.name)) →
      ∀ c, c ∈ ds → (findDecl decls c).isSome := fun hds c hc =>
    findDecl_isSome_iff.mpr (hds c hc)
  refine ⟨KernameInj.of_findCollision hcol, fun ci hci => (hdeps ci hci).1, hnd List.nodup_nil,
    fun ci hci => ?_, fun ci hci => ?_, (exprConsts_ok hcs).1.mono (hin htodo)⟩
  · obtain ⟨-, ds, hds, hdsin⟩ := hdeps ci hci
    obtain ⟨ht, hv, hall⟩ := declDeps_ok hds
    refine ⟨ht.1.mono (hin hdsin), fun v hvv => (hv v hvv).1.mono (hin hdsin), fun n hn => ?_⟩
    rcases hall n hn with hn | rfl
    · exact hin hdsin n hn
    · exact findDecl_isSome_iff.mpr (List.mem_map_of_mem hci)
  · obtain ⟨-, ds, hds, -⟩ := hdeps ci hci
    obtain ⟨ht, hv, -⟩ := declDeps_ok hds
    exact ⟨ht.2, fun v hvv => (hv v hvv).2⟩

end

end EraseProof
