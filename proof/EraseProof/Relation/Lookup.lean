import EraseProof.Spec

/-!
# Erased declarations in the λ□ environment

What `ErasesDeps` gives the simulation's δ, constructor and case steps: the λ□ body at the kername
of a constant that δ unfolds, which erases every marking of the constant's value
(`ErasesDeps.delta`); the erased block of the inductive of a λ□ constructor
(`ErasesDeps.construct_ind`, through `indIdOf_inj`); the block entry of an erased inductive with
its parameter count and `propositional` flag (`ErasesInd.indIsPropAndPars`), and with the field
count of each constructor (`ErasesInd.lookupCtor`). What the traversal needs of it: it survives the
abstraction of a free variable (`ErasesDeps.toBvar`) and fresh growth of the λ□ environment
(`ErasesDeps.ext`). Every lemma holds for every certificate predicate. Adapted from
`ML-V Relation/Deps.lean:24-96`, `ML-V Simulation/Ind.lean:150-486`,
`ML-V Simulation/Cases.lean:724` and `ML-V Core/Steps.lean:457-522`: the inductives' facts come
from `ErasesInd` alone, so the lookups take the constructor's position in its inductive as a
premise instead of reading it from the program's environment.
-/

open Lean Erasure

namespace EraseProof

section
variable {cert : BoxCert} {σ : EvalEnv} {lenv lenv' : GlobalDeclarations}

/-! ## Fresh growth of the λ□ environment -/

/-- The derived `==` on module paths implies equality. Copy of `ML-V Relation/Deps.lean:24`.
Reference: `modpath_eq_dec` (`MR common/theories/Kernames.v:232`). -/
private theorem modPath_eq_of_beq : ∀ {a b : ModPath}, (a == b) = true → a = b
  | .MPfile d₁, .MPfile d₂, h => by
    have h' : (d₁ == d₂) = true := h
    rw [beq_iff_eq.1 h']
  | .MPdot m₁ i₁, .MPdot m₂ i₂, h => by
    have h' : (m₁ == m₂ && i₁ == i₂) = true := h
    rw [Bool.and_eq_true] at h'
    rw [modPath_eq_of_beq h'.1, beq_iff_eq.1 h'.2]
  | .MPfile _, .MPdot .., h | .MPdot .., .MPfile _, h => nomatch h

/-- The derived `==` on kernames implies equality. Copy of `ML-V Relation/Deps.lean:37`.
Reference: `reflect_kername` (`MR common/theories/Kernames.v:325`). -/
private theorem kername_eq_of_beq {a b : Kername} (h : (a == b) = true) : a = b := by
  obtain ⟨m₁, i₁⟩ := a
  obtain ⟨m₂, i₂⟩ := b
  have h' : (m₁ == m₂ && i₁ == i₂) = true := h
  rw [Bool.and_eq_true] at h'
  rw [modPath_eq_of_beq h'.1, beq_iff_eq.1 h'.2]

/-- A kername found in `lenv` is found, with the same declaration, after fresh growth. Copy of
`ML-V Relation/Deps.lean:41`. -/
private theorem find?_ext {kn : Kername} {d : Kername × GlobalDecl}
    (hx : ∃ new, lenv' = new ++ lenv ∧ ∀ kn ∈ new.map (·.1), lenv.find? (·.1 == kn) = none)
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

/-- `ErasesInd` survives fresh growth of the λ□ environment. Copy of
`ML-V Relation/Deps.lean:56`. -/
theorem ErasesInd.ext
    (hx : ∃ new, lenv' = new ++ lenv ∧ ∀ kn ∈ new.map (·.1), lenv.find? (·.1 == kn) = none)
    (h : ErasesInd σ lenv T) : ErasesInd σ lenv' T := by
  obtain ⟨iv, hiv, hall⟩ := h
  refine ⟨iv, hiv, fun j n hj => ?_⟩
  obtain ⟨iv', mib, ob, h1, hl, h3⟩ := hall j n hj
  refine ⟨iv', mib, ob, h1, ?_, h3⟩
  unfold lookupInd at hl ⊢
  split at hl
  · rename_i d heq
    rw [find?_ext hx heq]
    exact hl
  · cases hl

/-- `ErasesDeps` is stable under fresh growth of the λ□ environment. Copy of
`ML-V Relation/Deps.lean:72`. Reference: `erases_deps_cons` (`MR E/EDeps.v:492`). -/
theorem ErasesDeps.ext (hx : ∃ new, lenv' = new ++ lenv ∧
      ∀ kn ∈ new.map (·.1), lenv.find? (·.1 == kn) = none)
    (h : ErasesDeps cert σ lenv tb) : ErasesDeps cert σ lenv' tb := by
  induction h with
  | box => exact .box
  | bvar => exact .bvar
  | fvar => exact .fvar
  | lambda _ ih => exact .lambda ih
  | letIn _ _ ihv ihb => exact .letIn ihv ihb
  | app _ _ ihf iha => exact .app ihf iha
  | const hc hl hd _ ih =>
    refine .const hc ?_ hd ih
    unfold lookupConst at hl ⊢
    split at hl
    · rename_i d heq
      rw [find?_ext hx heq]
      exact hl
    · cases hl
  | construct hi hind _ ih => exact .construct hi (ErasesInd.ext hx hind) ih
  | case hi hind _ _ ihd ihb => exact .case hi (ErasesInd.ext hx hind) ihd ihb
  | proj hi hind _ ihd => exact .proj hi (ErasesInd.ext hx hind) ihd
  | fix _ ih => exact .fix ih

/-! ## The traversal's abstraction -/

/-- An element of `toBvarList x k as` is the abstraction of an element of `as`. Copy of
`ML-V Core/Steps.lean:457`. -/
theorem mem_toBvarList {x : FVarId} {k : Nat} : ∀ {as : List LBTerm} {a' : LBTerm},
    a' ∈ toBvarList x k as → ∃ a ∈ as, a' = toBvar x k a
  | [], _, h => nomatch h
  | a :: as, a', h => by
    simp only [toBvarList, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨a, .head _, rfl⟩
    · obtain ⟨b, hb, rfl⟩ := mem_toBvarList h
      exact ⟨b, .tail _ hb, rfl⟩

/-- A branch body of `toBvarAlts x k bs` is the abstraction of a branch body of `bs`. Copy of
`ML-V Core/Steps.lean:467`. -/
theorem mem_toBvarAlts {x : FVarId} {k : Nat} : ∀ {bs : List (List BinderName × LBTerm)}
    {b' : List BinderName × LBTerm}, b' ∈ toBvarAlts x k bs →
      ∃ b ∈ bs, b'.2 = toBvar x (k + b.1.length) b.2
  | [], _, h => nomatch h
  | (ns, t) :: bs, b', h => by
    simp only [toBvarAlts, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨_, .head _, rfl⟩
    · obtain ⟨b, hb, he⟩ := mem_toBvarAlts h
      exact ⟨b, .tail _ hb, he⟩

/-- A body of `toBvarDefs x k ds` is the abstraction of a body of `ds`. Copy of
`ML-V Core/Steps.lean:479`. -/
theorem mem_toBvarDefs {x : FVarId} {k : Nat} : ∀ {ds : List (@FixDef LBTerm)}
    {d' : @FixDef LBTerm}, d' ∈ toBvarDefs x k ds → ∃ d ∈ ds, d'.body = toBvar x k d.body
  | [], _, h => nomatch h
  | d :: ds, d', h => by
    simp only [toBvarDefs, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨_, .head _, rfl⟩
    · obtain ⟨b, hb, he⟩ := mem_toBvarDefs h
      exact ⟨b, .tail _ hb, he⟩

/-- Replacing a free variable by a bound one keeps the erased dependencies, which do not see
variables. Copy of `ML-V Core/Steps.lean:491`. Reference: `erases_deps_lift` (`MR E/EDeps.v:44`),
for the traversal's abstraction (DV-13). -/
theorem ErasesDeps.toBvar {t : LBTerm} {x : FVarId} (h : ErasesDeps cert σ lenv t) :
    ∀ k, ErasesDeps cert σ lenv (_root_.toBvar x k t) := by
  induction h with
  | box => intro; exact .box
  | bvar => intro; exact .bvar
  | fvar =>
    intro k
    simp only [_root_.toBvar]
    split
    · exact .bvar
    · exact .fvar
  | lambda _ ih => intro k; exact .lambda (ih _)
  | letIn _ _ ihv ihb => intro k; exact .letIn (ihv _) (ihb _)
  | app _ _ ihf iha => intro k; exact .app (ihf _) (iha _)
  | const hc hl hd hb _ => intro; exact .const hc hl hd hb
  | construct hi hind _ ih =>
    intro k
    refine .construct hi hind fun a' ha' => ?_
    obtain ⟨a, ha, rfl⟩ := mem_toBvarList ha'
    exact ih a ha k
  | case hi hind _ _ ihd ihb =>
    intro k
    refine .case hi hind (ihd k) fun b' hb' => ?_
    obtain ⟨b, hb, he⟩ := mem_toBvarAlts hb'
    rw [he]
    exact ihb b hb _
  | proj hi hind _ ih => intro k; exact .proj hi hind (ih k)
  | fix _ ih =>
    intro k
    simp only [_root_.toBvar]
    refine .fix fun d' hd' => ?_
    obtain ⟨d, hd, he⟩ := mem_toBvarDefs hd'
    rw [he]
    exact ih d hd _

/-! ## Lookups -/

/-- The position of a name found by `idxOf?`. Copy of `ML-V Simulation/Ind.lean:151`. -/
theorem getElem?_of_idxOf? {l : List Name} {x : Name} {j : Nat} (h : l.idxOf? x = some j) :
    l[j]? = some x := by
  rw [List.idxOf?_eq_some_iff] at h
  obtain ⟨h1, h2, -⟩ := h
  simp [h1, h2]

/-- The λ□ inductive of a Lean inductive determines it when the block names of `σ` do not
collide. Copy of `ML-V Simulation/Ind.lean:159`. -/
theorem indIdOf_inj (hbinj : BlockNamesInj σ.decls) {T T' : Name} {iid : InductiveId}
    (h₁ : IndIdOf σ T = some iid) (h₂ : IndIdOf σ T' = some iid) : T = T' := by
  unfold IndIdOf at h₁ h₂
  split at h₁
  · rename_i iv hiv
    split at h₂
    · rename_i iv' hiv'
      obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h₁
      obtain ⟨j', hj', he⟩ := Option.map_eq_some_iff.mp h₂
      simp only [InductiveId.mk.injEq] at he
      obtain ⟨hk, rfl⟩ := he
      have hall := (hbinj iv' iv ⟨_, List.mem_of_find?_eq_some hiv', rfl⟩
        ⟨_, List.mem_of_find?_eq_some hiv, rfl⟩).1 hk
      have h1 := getElem?_of_idxOf? hj
      have h2 := getElem?_of_idxOf? hj'
      rw [hall, h1] at h2
      exact Option.some.inj h2
    · cases h₂
  · cases h₁

/-- The erased block of the inductive of a λ□ constructor that the erased dependencies reach.
Copy of `ML-V Simulation/Ind.lean:254`. Reference: `erases_deps_tConstruct`
(`MR E/Extract.v:330`). -/
theorem ErasesDeps.construct_ind (hbinj : BlockNamesInj σ.decls) {T : Name} {iid : InductiveId}
    {c : Nat} {args : List LBTerm} (hid : IndIdOf σ T = some iid)
    (h : ErasesDeps cert σ lenv (.construct iid c args)) : ErasesInd σ lenv T := by
  cases h with
  | construct hid' hind => rw [indIdOf_inj hbinj hid' hid] at hind; exact hind

/-- The λ□ `propositional` flag and parameter count of an erased inductive: the flag is set
exactly for an inductive declared in `Prop`. Adapted from `ML-V Simulation/Ind.lean:473`.
Reference: `constructor_isprop_pars_decl` (`MR E/EGlobalEnv.v:169`). -/
theorem ErasesInd.indIsPropAndPars {T : Name} {iid : InductiveId} {iv : InductiveVal}
    (hid : IndIdOf σ T = some iid) (hind : ErasesInd σ lenv T)
    (hiv : findDecl σ.decls T = some (.inductInfo iv)) :
    ∃ b, indIsPropAndPars lenv iid = some (b, iv.numParams) ∧ (b = true ↔ σ.propInd T = true) := by
  obtain ⟨iv', hiv', hall⟩ := hind
  rw [hiv] at hiv'
  cases hiv'
  have hid' := hid
  unfold IndIdOf at hid'
  rw [hiv] at hid'
  obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp hid'
  obtain ⟨iv', mib, ob, -, hl, hnp, -, -, hprop⟩ := hall j _ (getElem?_of_idxOf? hj)
  refine ⟨ob.propositional, ?_, hprop⟩
  simp [EraseProof.indIsPropAndPars, hl, hnp]

/-- The `k`-th constructor `C` of an erased inductive `T`: its block entry has the inductive's
parameter count and `C`'s field count, and is propositional exactly when `T` is declared in
`Prop`. Adapted from `ML-V Simulation/Ind.lean:218 lookupCtor_of` and `:445 lookupCtor_ind`, with
the position of `C` in `T`'s constructors as a premise. Reference: `lookup_constructor`
(`MR E/EGlobalEnv.v:81`). -/
theorem ErasesInd.lookupCtor {T C : Name} {iid : InductiveId} {iv : InductiveVal} {k : Nat}
    (hid : IndIdOf σ T = some iid) (hind : ErasesInd σ lenv T)
    (hiv : findDecl σ.decls T = some (.inductInfo iv)) (hk : iv.ctors[k]? = some C) :
    ∃ mib ob cb cv, lookupCtor lenv iid k = some (mib, ob, cb) ∧
      findDecl σ.decls C = some (.ctorInfo cv) ∧ mib.npars = iv.numParams ∧
      cb.nargs = cv.numFields ∧ (ob.propositional = true ↔ σ.propInd T = true) := by
  obtain ⟨iv', hiv', hall⟩ := hind
  rw [hiv] at hiv'
  cases hiv'
  have hid' := hid
  unfold IndIdOf at hid'
  rw [hiv] at hid'
  obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp hid'
  obtain ⟨iv', mib, ob, hiv', hl, hnp, -, hctors, hprop⟩ := hall j _ (getElem?_of_idxOf? hj)
  rw [hiv] at hiv'
  cases hiv'
  obtain ⟨cv, cb, hc, hcb, hnargs⟩ := hctors _ _ hk
  refine ⟨mib, ob, cb, cv, ?_, hc, hnp, hnargs, hprop⟩
  simp [EraseProof.lookupCtor, hl, hcb]

/-- The λ□ declaration at the kername of a constant that δ unfolds (`EvalEnv.unfold?`), when the
erased dependencies reach that kername: it is the constant's own (`KernameInj`), its body has
erased dependencies and erases every marking of the constant's value (`ErasesDecl`; the
constant is not remapped). Adapted from `ML-V Simulation/Cases.lean:724 erases_correct_delta`.
Reference: `erases_deps_tConst` (`MR E/Extract.v:324`), the `eval_delta` case of `erases_correct`
(`MR E/ErasureCorrectness.v:152`). -/
theorem ErasesDeps.delta {c : Name} {ci : ConstantInfo} {body : Expr} (hinj : KernameInj σ.decls)
    (hu : σ.unfold? c = some (ci, body)) (h : ErasesDeps cert σ lenv (.const (toKername c))) :
    ∃ cb b', lookupConst lenv (toKername c) = some cb ∧ cb.cst_body = some b' ∧
      ErasesDeps cert σ lenv b' ∧ ∀ bM, MarkOf σ.decls σ.cfg [] body bM → Erases cert σ [] bM b' := by
  unfold EvalEnv.unfold? at hu
  split at hu
  · rename_i v hfd
    split at hu
    · cases hu
    · rename_i hax
      cases hu
      have hax' : σ.axiomatized (.defnInfo v) = false :=
        Bool.eq_false_iff.2 fun h => hax (by simp [h])
      generalize hk : toKername c = kn at h
      cases h with
      | @const c' ci' cb hfd' hl hd hbody =>
        obtain rfl := hinj c c' (by rw [hfd]; rfl) (by rw [hfd']; rfl) hk
        rw [hfd] at hfd'
        cases hfd'
        simp only [ErasesDecl, ConstantInfo.value?] at hd
        rcases hd with ⟨hax'', -⟩ | ⟨-, -, b', hcb, herb⟩
        · rw [hax'] at hax''; cases hax''
        · exact ⟨cb, b', hl, hcb, hbody b' hcb, herb⟩
  · cases hu

end

end EraseProof
