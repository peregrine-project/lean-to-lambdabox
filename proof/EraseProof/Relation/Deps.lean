import EraseProof.Relation.Basic

/-!
# Erased dependencies

`ErasesDeps σ lenv t`: every constant that the λ□ term `t` mentions, transitively, is the kername
of a declaration of `σ.decls` whose λ□ body in `lenv` erases its Lean body (`ErasesDecl`):
MetaRocq's `erases_deps` (`MR E/Extract.v:306`) on the fragment's λ□ constructors, indexed by the
source constant. A recursive declaration's body is a `tFix` of its block (`ErasesBlock`), and
`BlocksErased` says that every fixpoint stored for a program constant is such a block. This module
proves that `ErasesDeps` survives fresh growth of the λ□ environment (`ErasesDeps.ext`, MR
`erases_deps_cons`), closed substitution (`ErasesDeps.csubst`) and λ□ evaluation
(`ErasesDeps.eval`, MR `erases_deps_eval`).
-/

open Lean Lean4Lean Erasure

namespace EraseProof

/-- A recursive block as the eraser emits it: member `j` unfolds (`cunfold_fix`, `rarg = 0`) to an
erasure of its Lean value. Reference: `MR E/Extract.v:122 erases_tFix`, for Lean's
environment-level recursion, without its `isLambda` premises (DV-7, DV-8); Let. Def. 3 (fix). -/
def ErasesBlock (venv : VEnv) (σ : EvalEnv) (lenv : GlobalDeclarations) (names : List Name)
    (defs : List (@FixDef LBTerm)) : Prop :=
  names.length = defs.length ∧ ∀ j n, names[j]? = some n →
    ∃ ci v d, findDecl σ.decls n = some ci ∧ ci.value? (allowOpaque := true) = some v ∧
      defs[j]? = some d ∧ d.name = fixDefName n ∧ d.principalArgIdx = 0 ∧
      Erases venv ci.levelParams σ.isAtom (RecIn lenv) [] v (substl (fixSubst defs) d.body) ∧
      lookupConst lenv (toKername n) = some ⟨some (.fix defs j)⟩

/-- A constant's λ□ body erases its Lean body, per what the eraser emits: axioms and remapped
externs have none (DV-12), recursive constants a `tFix` of their block (DV-7), others an erasure.
Reference: `MR E/Extract.v:264 erases_constant_body`; Let. Def. 3 (def, ax). -/
def ErasesDecl (venv : VEnv) (σ : EvalEnv) (lenv : GlobalDeclarations) (ci : ConstantInfo)
    (cb : ConstantBody) : Prop :=
  match ci.value? (allowOpaque := true) with
  | none => cb.cst_body = none
  | some v =>
    (σ.axiomatized ci = true ∧ cb.cst_body = none) ∨
    (σ.axiomatized ci = false ∧ RecursiveDecl ci = true ∧ ∃ defs i,
      cb.cst_body = some (.fix defs i) ∧ ci.all[i]? = some ci.name ∧
      ErasesBlock venv σ lenv ci.all defs) ∨
    (σ.axiomatized ci = false ∧ RecursiveDecl ci = false ∧ ∃ b', cb.cst_body = some b' ∧
      Erases venv ci.levelParams σ.isAtom (RecIn lenv) [] v b')

/-- The λ□ environment contains erasures of the erased term's dependencies, transitively, on the
fragment's λ□ constructors; indexed by the source constant (DV-14). Reference:
`MR E/Extract.v:306 erases_deps`; MC §7.4 (p. 8:64). -/
inductive ErasesDeps (venv : VEnv) (σ : EvalEnv) (lenv : GlobalDeclarations) : LBTerm → Prop
  /-- `erases_deps_tBox` (`MR E/Extract.v:307`). -/
  | box : ErasesDeps venv σ lenv .box
  /-- `erases_deps_tRel` (`:308`). -/
  | bvar : ErasesDeps venv σ lenv (.bvar i)
  /-- `erases_deps_tVar` (`:309`). -/
  | fvar : ErasesDeps venv σ lenv (.fvar x)
  /-- `erases_deps_tLambda` (`:313`). -/
  | lambda : ErasesDeps venv σ lenv b → ErasesDeps venv σ lenv (.lambda na b)
  /-- `erases_deps_tLetIn` (`:316`). -/
  | letIn : ErasesDeps venv σ lenv v → ErasesDeps venv σ lenv b →
      ErasesDeps venv σ lenv (.letIn na v b)
  /-- `erases_deps_tApp` (`:320`). -/
  | app : ErasesDeps venv σ lenv f → ErasesDeps venv σ lenv a → ErasesDeps venv σ lenv (.app f a)
  /-- `erases_deps_tConst` (`:324`), indexed by the source constant `c` (DV-14). -/
  | const : findDecl σ.decls c = some ci → lookupConst lenv (toKername c) = some cb →
      ErasesDecl venv σ lenv ci cb → (∀ b, cb.cst_body = some b → ErasesDeps venv σ lenv b) →
      ErasesDeps venv σ lenv (.const (toKername c))
  /-- `erases_deps_tFix` (`:352`). -/
  | fix : (∀ d ∈ defs, ErasesDeps venv σ lenv d.body) → ErasesDeps venv σ lenv (.fix defs i)
  /-- `erases_deps_tPrimInt` (`:358`); `LBTerm.prim` holds machine integers only (DV-16). -/
  | prim : ErasesDeps venv σ lenv (.prim p)

/-- Fixpoints stored for program constants are erased blocks. Reference: the part of
`MR E/EDeps.v:594 globals_erased_with_deps` that `erases_deps` cannot carry (DV-7). -/
def BlocksErased (venv : VEnv) (σ : EvalEnv) (lenv : GlobalDeclarations) : Prop :=
  ∀ c ci defs i, findDecl σ.decls c = some ci →
    lookupConst lenv (toKername c) = some ⟨some (.fix defs i)⟩ →
    ErasesDecl venv σ lenv ci ⟨some (.fix defs i)⟩ ∧ ∀ d ∈ defs, ErasesDeps venv σ lenv d.body

section
variable {venv : VEnv} {σ : EvalEnv} {lenv : GlobalDeclarations}

/-! ## Fresh growth of the λ□ environment -/

/-- A constant found in `lenv` is found, with the same body, after fresh growth. Reference: the
`declared_constant` step of `erases_deps_cons` (`MR E/EDeps.v:492`). -/
theorem lookupConst_ext (hx : LenvExt lenv lenv') (h : lookupConst lenv kn = some cb) :
    lookupConst lenv' kn = some cb := by
  obtain ⟨new, rfl, hfresh⟩ := hx
  have hnew : new.find? (·.1 == kn) = none := by
    rw [List.find?_eq_none]
    intro y hy hyk
    have hnone := hfresh kn (List.mem_map.2 ⟨y, hy, Kername.eq_of_beq hyk⟩)
    simp only [lookupConst, hnone] at h
    cases h
  unfold lookupConst at h ⊢
  rw [List.find?_append, hnew, Option.none_or]
  exact h

/-- `ErasesBlock` survives fresh growth of the λ□ environment. Reference: the `erases_tFix` case
of `erases_extends` (`MR E/ESubstitution.v:73`), as `erases_deps_cons` (`MR E/EDeps.v:492`) uses
it. -/
theorem ErasesBlock.ext (hx : LenvExt lenv lenv') (h : ErasesBlock venv σ lenv names defs) :
    ErasesBlock venv σ lenv' names defs := by
  obtain ⟨hlen, hj⟩ := h
  refine ⟨hlen, fun j n hn => ?_⟩
  obtain ⟨ci, v, d, hci, hv, hd, hname, hidx, her, hl⟩ := hj j n hn
  exact ⟨ci, v, d, hci, hv, hd, hname, hidx, Erases.mono_rc (fun _ _ => RecIn.ext hx) her,
    lookupConst_ext hx hl⟩

/-- `ErasesDecl` survives fresh growth of the λ□ environment. Reference: the
`erases_constant_body` step of `erases_deps_cons` (`MR E/EDeps.v:492`). -/
theorem ErasesDecl.ext (hx : LenvExt lenv lenv') (h : ErasesDecl venv σ lenv ci cb) :
    ErasesDecl venv σ lenv' ci cb := by
  unfold ErasesDecl at h ⊢
  generalize ci.value? (allowOpaque := true) = ov at h ⊢
  cases ov with
  | none => exact h
  | some v =>
    rcases h with h | ⟨ha, hr, defs, i, hb, hi, hbl⟩ | ⟨ha, hr, b', hb, her⟩
    · exact .inl h
    · exact .inr (.inl ⟨ha, hr, defs, i, hb, hi, hbl.ext hx⟩)
    · exact .inr (.inr ⟨ha, hr, b', hb, Erases.mono_rc (fun _ _ => RecIn.ext hx) her⟩)

/-- `ErasesDeps` is stable under fresh growth of the λ□ environment. Reference: `erases_deps_cons`
(`MR E/EDeps.v:492`). -/
theorem ErasesDeps.ext (hx : LenvExt lenv lenv') (h : ErasesDeps venv σ lenv t) :
    ErasesDeps venv σ lenv' t := by
  induction h with
  | box => exact .box
  | bvar => exact .bvar
  | fvar => exact .fvar
  | lambda _ ih => exact .lambda ih
  | letIn _ _ ihv ihb => exact .letIn ihv ihb
  | app _ _ ihf iha => exact .app ihf iha
  | const hc hl hd _ ih => exact .const hc (lookupConst_ext hx hl) (hd.ext hx) ih
  | fix _ ih => exact .fix ih
  | prim => exact .prim

/-! ## Substitution -/

/-- A body of `csubstD t k ds` is the substitution of a body of `ds`. Reference: the `tFix` case
of `csubst` (`MR E/ECSubst.v:14`), which maps `csubst` over the bodies. -/
theorem mem_csubstD {t : LBTerm} {k : Nat} : ∀ {ds : List (@FixDef LBTerm)} {d : @FixDef LBTerm},
    d ∈ csubstD t k ds → ∃ d' ∈ ds, d.body = EraseProof.csubst t k d'.body
  | [], _, h => nomatch h
  | ⟨_, _, _⟩ :: _, _, h => by
    simp only [csubstD, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨_, List.mem_cons_self, rfl⟩
    · obtain ⟨d', hd', he⟩ := mem_csubstD h
      exact ⟨d', List.mem_cons_of_mem _ hd', he⟩

/-- Dependencies are preserved by substitution. Reference: `erases_deps_subst`
(`MR E/EDeps.v:94`). -/
theorem ErasesDeps.csubst (ha : ErasesDeps venv σ lenv a) (hb : ErasesDeps venv σ lenv b) :
    ErasesDeps venv σ lenv (csubst a k b) := by
  induction hb generalizing k with
  | box => exact .box
  | bvar =>
    simp only [EraseProof.csubst]
    split
    · exact ha
    · split <;> exact .bvar
  | fvar => exact .fvar
  | lambda _ ih => exact .lambda ih
  | letIn _ _ ihv ihb => exact .letIn ihv ihb
  | app _ _ ihf iha => exact .app ihf iha
  | const hc hl hd hbody => exact .const hc hl hd hbody
  | fix _ ih =>
    refine .fix fun d hd => ?_
    obtain ⟨d', hd', he⟩ := mem_csubstD hd
    rw [he]
    exact ih d' hd'
  | prim => exact .prim

/-- Substituting terms with erased dependencies. Reference: `erases_deps_substl`
(`MR E/EDeps.v:208`). -/
theorem ErasesDeps.substl : ∀ {ts : List LBTerm} {b : LBTerm},
    (∀ t ∈ ts, ErasesDeps venv σ lenv t) → ErasesDeps venv σ lenv b →
      ErasesDeps venv σ lenv (EraseProof.substl ts b)
  | [], _, _, hb => hb
  | t :: _, _, hts, hb => by
    simp only [EraseProof.substl, List.foldl_cons]
    exact ErasesDeps.substl (fun u hu => hts u (List.mem_cons_of_mem _ hu))
      (ErasesDeps.csubst (hts t List.mem_cons_self) hb)

/-- An application spine has erased dependencies iff its head and arguments have. Reference:
`erases_deps_mkApps` (`MR E/EDeps.v:17`) and `erases_deps_mkApps_inv` (`:31`). -/
theorem ErasesDeps.mkApps_iff : ∀ {f : LBTerm} {args : List LBTerm},
    ErasesDeps venv σ lenv (mkApps f args) ↔
      ErasesDeps venv σ lenv f ∧ ∀ a ∈ args, ErasesDeps venv σ lenv a
  | _, [] => by simp [mkApps]
  | _, a :: as => by
    rw [mkApps, ErasesDeps.mkApps_iff]
    constructor
    · rintro ⟨hfa, has⟩
      cases hfa with
      | app hf ha =>
        exact ⟨hf, fun b hb => (List.mem_cons.1 hb).elim (fun h => h ▸ ha) (has b)⟩
    · rintro ⟨hf, has⟩
      exact ⟨.app hf (has a List.mem_cons_self), fun b hb => has b (List.mem_cons_of_mem _ hb)⟩

/-- Unfolding a fixpoint whose bodies have erased dependencies. Reference:
`erases_deps_cunfold_fix` (`MR E/EDeps.v:245`), with `Forall_erases_deps_fix_subst` (`:223`). -/
theorem ErasesDeps.cunfoldFix (hd : ∀ d ∈ defs, ErasesDeps venv σ lenv d.body)
    (hu : EraseProof.cunfoldFix defs i = some (n, fn)) : ErasesDeps venv σ lenv fn := by
  simp only [EraseProof.cunfoldFix, Option.map_eq_some_iff, Prod.mk.injEq] at hu
  obtain ⟨d, hdi, -, rfl⟩ := hu
  refine ErasesDeps.substl ?_ (hd d (List.mem_of_getElem? hdi))
  intro t ht
  simp only [fixSubst, List.mem_map, List.mem_reverse, List.mem_range] at ht
  obtain ⟨j, -, rfl⟩ := ht
  exact .fix hd

/-! ## Evaluation -/

/-- Dependencies are preserved by λ□ evaluation. Reference: `erases_deps_eval`
(`MR E/EDeps.v:275`). -/
theorem ErasesDeps.eval (h : ErasesDeps venv σ lenv t)
    (hev : LBEval defaultFlags lenv t v) : ErasesDeps venv σ lenv v := by
  induction hev with
  | box => exact .box
  | beta _ _ _ ih1 ih2 ih3 =>
    cases h with
    | app hf ha =>
      cases ih1 hf with
      | lambda hbody => exact ih3 (ErasesDeps.csubst (ih2 ha) hbody)
  | zeta _ _ ih1 ih2 =>
    cases h with
    | letIn hv hbody => exact ih2 (ErasesDeps.csubst (ih1 hv) hbody)
  | iota => cases h
  | iotaSing => cases h
  | fix _ _ _ hu _ ih1 ih2 ih3 =>
    cases h with
    | app hf ha =>
      obtain ⟨hfix, hargs⟩ := ErasesDeps.mkApps_iff.1 (ih1 hf)
      cases hfix with
      | fix hdefs =>
        exact ih3 (.app (ErasesDeps.mkApps_iff.2 ⟨ErasesDeps.cunfoldFix hdefs hu, hargs⟩)
          (ih2 ha))
  | fixValue _ _ _ _ _ ih1 ih2 =>
    cases h with
    | app hf ha => exact .app (ih1 hf) (ih2 ha)
  | fix' _ _ hu _ _ ih1 ih2 ih3 =>
    cases h with
    | app hf ha =>
      cases ih1 hf with
      | fix hdefs => exact ih3 (.app (ErasesDeps.cunfoldFix hdefs hu) (ih2 ha))
  | delta hc hbody _ ih =>
    cases h with
    | const _ hl _ hdeps =>
      rw [hl] at hc
      cases hc
      exact ih (hdeps _ hbody)
  | proj => cases h
  | projProp => cases h
  | construct _ _ _ _ _ ih1 _ =>
    cases h with
    | app hf _ =>
      obtain ⟨hc, -⟩ := ErasesDeps.mkApps_iff.1 (ih1 hf)
      cases hc
  | appCong _ _ _ ih1 ih2 =>
    cases h with
    | app hf ha => exact .app (ih1 hf) (ih2 ha)
  | prim => exact h
  | atom => exact h

end

end EraseProof
