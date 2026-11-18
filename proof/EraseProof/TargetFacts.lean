import EraseProof.Target

/-!
# Facts about λ□ evaluation

The induction principle of `LBEval` with a usable hypothesis for the nested premise of
`constructBlock` (`LBEval.ind`), the inversion of evaluation results headed by `□`
(`LBEval.eq_box_of_headOf`), the evaluation of a result to itself (`LBEval.idem`), and `iota_red`
field by field on closed fields (`substl_cons_closed`).
-/

open Lean

namespace EraseProof

/-- Induction on `LBEval` whose hypothesis for the nested premise of `constructBlock` is a
`List.Forall₂` of the motive. Reference: `eval_rect` (`MR E/EWcbvEval.v:395`), whose hypothesis for
`eval_construct_block` is `All2_over`. -/
theorem LBEval.ind {fl : WcbvFlags} {lenv : GlobalDeclarations}
    {motive : (t v : LBTerm) → LBEval fl lenv t v → Prop}
    (box : ∀ {a t t' : LBTerm} (h₁ : LBEval fl lenv a .box) (h₂ : LBEval fl lenv t t'),
      motive a .box h₁ → motive t t' h₂ → motive (.app a t) .box (.box h₁ h₂))
    (beta : ∀ {f : LBTerm} {na : BinderName} {b a a' res : LBTerm}
      (h₁ : LBEval fl lenv f (.lambda na b)) (h₂ : LBEval fl lenv a a')
      (h₃ : LBEval fl lenv (csubst a' 0 b) res),
      motive f _ h₁ → motive a a' h₂ → motive _ res h₃ → motive (.app f a) res (.beta h₁ h₂ h₃))
    (zeta : ∀ {b0 b0' b1 res : LBTerm} {na : BinderName} (h₁ : LBEval fl lenv b0 b0')
      (h₂ : LBEval fl lenv (csubst b0' 0 b1) res),
      motive b0 b0' h₁ → motive _ res h₂ → motive (.letIn na b0 b1) res (.zeta h₁ h₂))
    (iota : ∀ {discr : LBTerm} {ind : InductiveId} {c : Nat} {args : List LBTerm} {pars : Nat}
      {cdecl : ConstructorBody} {brs : List (List BinderName × LBTerm)}
      {br : List BinderName × LBTerm} {res : LBTerm}
      (h₁ : fl.with_constructor_as_block = false)
      (h₂ : LBEval fl lenv discr (mkApps (.construct ind c []) args))
      (h₃ : ctorIsPropParsDecl lenv ind c = some (false, pars, cdecl)) (h₄ : brs[c]? = some br)
      (h₅ : args.length = pars + cdecl.nargs) (h₆ : (args.drop pars).length = br.1.length)
      (h₇ : LBEval fl lenv (iotaRed pars args br) res),
      motive discr _ h₂ → motive _ res h₇ →
      motive (.case (ind, pars) discr brs) res (.iota h₁ h₂ h₃ h₄ h₅ h₆ h₇))
    (iotaBlock : ∀ {discr : LBTerm} {ind : InductiveId} {c : Nat} {args : List LBTerm}
      {pars : Nat} {cdecl : ConstructorBody} {brs : List (List BinderName × LBTerm)}
      {br : List BinderName × LBTerm} {res : LBTerm}
      (h₁ : fl.with_constructor_as_block = true) (h₂ : LBEval fl lenv discr (.construct ind c args))
      (h₃ : ctorIsPropParsDecl lenv ind c = some (false, pars, cdecl)) (h₄ : brs[c]? = some br)
      (h₅ : args.length = pars + cdecl.nargs) (h₆ : (args.drop pars).length = br.1.length)
      (h₇ : LBEval fl lenv (iotaRed pars args br) res),
      motive discr _ h₂ → motive _ res h₇ →
      motive (.case (ind, pars) discr brs) res (.iotaBlock h₁ h₂ h₃ h₄ h₅ h₆ h₇))
    (iotaSing : ∀ {discr : LBTerm} {ind : InductiveId} {pars : Nat}
      {brs : List (List BinderName × LBTerm)} {n : List BinderName} {f res : LBTerm}
      (h₁ : fl.with_prop_case = true)
      (h₂ : LBEval fl lenv discr .box) (h₃ : indIsPropAndPars lenv ind = some (true, pars))
      (h₄ : brs = [(n, f)]) (h₅ : LBEval fl lenv (substl (List.replicate n.length .box) f) res),
      motive discr .box h₂ → motive _ res h₅ →
      motive (.case (ind, pars) discr brs) res (.iotaSing h₁ h₂ h₃ h₄ h₅))
    (fix : ∀ {f : LBTerm} {mfix : List (@FixDef LBTerm)} {idx : Nat} {argsv : List LBTerm}
      {a av fn res : LBTerm} (h₁ : fl.with_guarded_fix = true)
      (h₂ : LBEval fl lenv f (mkApps (.fix mfix idx) argsv)) (h₃ : LBEval fl lenv a av)
      (h₄ : cunfoldFix mfix idx = some (argsv.length, fn))
      (h₅ : LBEval fl lenv (.app (mkApps fn argsv) av) res),
      motive f _ h₂ → motive a av h₃ → motive _ res h₅ →
      motive (.app f a) res (.fix h₁ h₂ h₃ h₄ h₅))
    (fixValue : ∀ {f : LBTerm} {mfix : List (@FixDef LBTerm)} {idx : Nat} {argsv : List LBTerm}
      {a av : LBTerm} {narg : Nat} {fn : LBTerm} (h₁ : fl.with_guarded_fix = true)
      (h₂ : LBEval fl lenv f (mkApps (.fix mfix idx) argsv)) (h₃ : LBEval fl lenv a av)
      (h₄ : cunfoldFix mfix idx = some (narg, fn)) (h₅ : argsv.length < narg),
      motive f _ h₂ → motive a av h₃ →
      motive (.app f a) (.app (mkApps (.fix mfix idx) argsv) av) (.fixValue h₁ h₂ h₃ h₄ h₅))
    (fix' : ∀ {f : LBTerm} {mfix : List (@FixDef LBTerm)} {idx narg : Nat} {fn a av res : LBTerm}
      (h₁ : fl.with_guarded_fix = false)
      (h₂ : LBEval fl lenv f (.fix mfix idx)) (h₃ : cunfoldFix mfix idx = some (narg, fn))
      (h₄ : LBEval fl lenv a av) (h₅ : LBEval fl lenv (.app fn av) res),
      motive f _ h₂ → motive a av h₄ → motive _ res h₅ →
      motive (.app f a) res (.fix' h₁ h₂ h₃ h₄ h₅))
    (delta : ∀ {c : Kername} {decl : ConstantBody} {body res : LBTerm}
      (h₁ : lookupConst lenv c = some decl)
      (h₂ : decl.cst_body = some body) (h₃ : LBEval fl lenv body res),
      motive body res h₃ → motive (.const c) res (.delta h₁ h₂ h₃))
    (proj : ∀ {discr : LBTerm} {args : List LBTerm} {cdecl : ConstructorBody} {a res : LBTerm}
      {p : ProjectionInfo} (h₁ : fl.with_constructor_as_block = false)
      (h₂ : LBEval fl lenv discr (mkApps (.construct p.indType 0 []) args))
      (h₃ : ctorIsPropParsDecl lenv p.indType 0 = some (false, p.paramCount, cdecl))
      (h₄ : args.length = p.paramCount + cdecl.nargs)
      (h₅ : args[p.paramCount + p.fieldIdx]? = some a) (h₆ : LBEval fl lenv a res),
      motive discr _ h₂ → motive a res h₆ → motive (.proj p discr) res (.proj h₁ h₂ h₃ h₄ h₅ h₆))
    (projBlock : ∀ {discr : LBTerm} {args : List LBTerm} {cdecl : ConstructorBody}
      {a res : LBTerm} {p : ProjectionInfo} (h₁ : fl.with_constructor_as_block = true)
      (h₂ : LBEval fl lenv discr (.construct p.indType 0 args))
      (h₃ : ctorIsPropParsDecl lenv p.indType 0 = some (false, p.paramCount, cdecl))
      (h₄ : args.length = p.paramCount + cdecl.nargs)
      (h₅ : args[p.paramCount + p.fieldIdx]? = some a) (h₆ : LBEval fl lenv a res),
      motive discr _ h₂ → motive a res h₆ →
      motive (.proj p discr) res (.projBlock h₁ h₂ h₃ h₄ h₅ h₆))
    (projProp : ∀ {discr : LBTerm} {p : ProjectionInfo} (h₁ : fl.with_prop_case = true)
      (h₂ : LBEval fl lenv discr .box)
      (h₃ : indIsPropAndPars lenv p.indType = some (true, p.paramCount)),
      motive discr .box h₂ → motive (.proj p discr) .box (.projProp h₁ h₂ h₃))
    (construct : ∀ {ind : InductiveId} {c : Nat} {mdecl : MutualInductiveBody}
      {idecl : OneInductiveBody} {cdecl : ConstructorBody} {f : LBTerm} {args : List LBTerm}
      {a a' : LBTerm}
      (h₁ : fl.with_constructor_as_block = false)
      (h₂ : lookupCtor lenv ind c = some (mdecl, idecl, cdecl))
      (h₃ : LBEval fl lenv f (mkApps (.construct ind c []) args))
      (h₄ : args.length < mdecl.npars + cdecl.nargs) (h₅ : LBEval fl lenv a a'),
      motive f _ h₃ → motive a a' h₅ →
      motive (.app f a) (.app (mkApps (.construct ind c []) args) a') (.construct h₁ h₂ h₃ h₄ h₅))
    (constructBlock : ∀ {ind : InductiveId} {c : Nat} {mdecl : MutualInductiveBody}
      {idecl : OneInductiveBody} {cdecl : ConstructorBody} {args args' : List LBTerm}
      (h₁ : fl.with_constructor_as_block = true)
      (h₂ : lookupCtor lenv ind c = some (mdecl, idecl, cdecl))
      (h₃ : args.length = mdecl.npars + cdecl.nargs)
      (h₄ : List.Forall₂ (LBEval fl lenv) args args'),
      List.Forall₂ (fun a a' => ∃ h : LBEval fl lenv a a', motive a a' h) args args' →
      motive (.construct ind c args) (.construct ind c args') (.constructBlock h₁ h₂ h₃ h₄))
    (appCong : ∀ {f f' a a' : LBTerm} (h₁ : LBEval fl lenv f f')
      (h₂ : (isLambdaT f' || (if fl.with_guarded_fix then isFixApp f' else isFixT f') ||
        isBoxT f' || isConstructApp f' || isPrimApp f') = false) (h₃ : LBEval fl lenv a a'),
      motive f f' h₁ → motive a a' h₃ → motive (.app f a) (.app f' a') (.appCong h₁ h₂ h₃))
    (prim : ∀ {p : PrimVal}, motive (.prim p) (.prim p) .prim)
    (atom : ∀ {t : LBTerm} (h : lbAtom fl lenv t = true), motive t t (.atom h))
    {t v : LBTerm} (h : LBEval fl lenv t v) : motive t v h :=
  LBEval.rec (motive_2 := fun args args' _ =>
      List.Forall₂ (fun a a' => ∃ h : LBEval fl lenv a a', motive a a' h) args args')
    box beta zeta iota iotaBlock iotaSing fix fixValue fix' delta proj projBlock projProp construct
    (fun h₁ h₂ h₃ h₄ ih => constructBlock h₁ h₂ h₃ h₄ ih) appCong prim atom
    .nil (fun h _ ih ihs => .cons ⟨h, ih⟩ ihs) h

/-- The head of `mkApps f args` is the head of `f`. Reference: `head_mkApps`
(`MR E/EAstUtils.v:57`). -/
theorem headOf_mkApps : ∀ {f : LBTerm} {args : List LBTerm}, headOf (mkApps f args) = headOf f
  | _, [] => rfl
  | f, a :: as => headOf_mkApps (f := .app f a) (args := as)

/-- A λ□ evaluation result headed by `□` is `□`. Reference: `eval_to_mkApps_tBox_inv`
(`MR E/EWcbvEval.v:985`), with `headOf` in place of `mkApps`. -/
theorem LBEval.eq_box_of_headOf {fl : WcbvFlags} {lenv : GlobalDeclarations} {s t : LBTerm}
    (hev : LBEval fl lenv s t) (hh : headOf t = .box) : t = .box := by
  induction hev using LBEval.ind with
  | box => rfl
  | beta _ _ _ _ _ ih => exact ih hh
  | zeta _ _ _ ih => exact ih hh
  | iota _ _ _ _ _ _ _ _ ih => exact ih hh
  | iotaBlock _ _ _ _ _ _ _ _ ih => exact ih hh
  | iotaSing _ _ _ _ _ _ ih => exact ih hh
  | fix _ _ _ _ _ _ _ ih => exact ih hh
  | fixValue => simp only [headOf, headOf_mkApps] at hh; cases hh
  | fix' _ _ _ _ _ _ _ ih => exact ih hh
  | delta _ _ _ ih => exact ih hh
  | proj _ _ _ _ _ _ _ ih => exact ih hh
  | projBlock _ _ _ _ _ _ _ ih => exact ih hh
  | projProp => rfl
  | construct => simp only [headOf, headOf_mkApps] at hh; cases hh
  | constructBlock => cases hh
  | @appCong _ f' _ _ _ hb _ ihf =>
    have hf : f' = .box := ihf hh
    subst hf
    simp [isBoxT] at hb
  | prim => cases hh
  | atom ha =>
    rename_i t
    cases t with
    | box => rfl
    | app => simp [lbAtom] at ha
    | _ => cases hh

/-- An evaluation result evaluates to itself. Reference: `eval_to_value` (`MR E/EWcbvEval.v:771`)
and `value_final` (`MR E/EWcbvEval.v:1129`). -/
theorem LBEval.idem {fl : WcbvFlags} {lenv : GlobalDeclarations} {s t : LBTerm}
    (hev : LBEval fl lenv s t) : LBEval fl lenv t t := by
  induction hev using LBEval.ind with
  | box => exact .atom rfl
  | beta _ _ _ _ _ ih => exact ih
  | zeta _ _ _ ih => exact ih
  | iota _ _ _ _ _ _ _ _ ih => exact ih
  | iotaBlock _ _ _ _ _ _ _ _ ih => exact ih
  | iotaSing _ _ _ _ _ _ ih => exact ih
  | fix _ _ _ _ _ _ _ ih => exact ih
  | fixValue h₁ _ _ h₄ h₅ ihf iha => exact .fixValue h₁ ihf iha h₄ h₅
  | fix' _ _ _ _ _ _ _ ih => exact ih
  | delta _ _ _ ih => exact ih
  | proj _ _ _ _ _ _ _ ih => exact ih
  | projBlock _ _ _ _ _ _ _ ih => exact ih
  | projProp => exact .atom rfl
  | construct h₁ h₂ _ h₄ _ ihf iha => exact .construct h₁ h₂ ihf h₄ iha
  | constructBlock h₁ h₂ h₃ h₄ ih =>
    have hl : ∀ {xs ys : List LBTerm}, List.Forall₂ (LBEval fl lenv) xs ys → xs.length = ys.length := by
      intro xs ys h
      induction h with
      | nil => rfl
      | cons _ _ ih' => simp [ih']
    refine .constructBlock h₁ h₂ (hl h₄ ▸ h₃) ?_
    clear h₃ h₄ hl
    induction ih with
    | nil => exact .nil
    | cons h _ ih' => exact .cons h.2 ih'
  | appCong _ h₂ _ ihf iha => exact .appCong ihf h₂ iha
  | prim => exact .prim
  | atom ha => exact .atom ha

/-! ## Closed substitutions -/

namespace TargetSubst

mutual
/-- `csubst` below the closedness bound is the identity. -/
theorem csubst_closedn (f : LBTerm) : ∀ (t : LBTerm) (k j : Nat), closedn k t = true → k ≤ j →
    csubst f j t = t
  | .box, _, _, _, _ => rfl
  | .bvar m, k, j, h, hkj => by
    simp only [closedn, decide_eq_true_eq] at h
    simp only [csubst]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  | .fvar _, _, _, _, _ => rfl
  | .lambda na b, k, j, h, hkj => by
    simp only [closedn] at h
    simp only [csubst, csubst_closedn f b (k + 1) (j + 1) h (by omega)]
  | .letIn na b b', k, j, h, hkj => by
    simp only [closedn, Bool.and_eq_true] at h
    simp only [csubst, csubst_closedn f b k j h.1 hkj, csubst_closedn f b' (k + 1) (j + 1) h.2 (by omega)]
  | .app u v, k, j, h, hkj => by
    simp only [closedn, Bool.and_eq_true] at h
    simp only [csubst, csubst_closedn f u k j h.1 hkj, csubst_closedn f v k j h.2 hkj]
  | .const _, _, _, _, _ => rfl
  | .construct i c args, k, j, h, hkj => by
    simp only [closedn] at h
    simp only [csubst, csubstL_closedn f args k j h hkj]
  | .case ip c brs, k, j, h, hkj => by
    simp only [closedn, Bool.and_eq_true] at h
    simp only [csubst, csubst_closedn f c k j h.1 hkj, csubstB_closedn f brs k j h.2 hkj]
  | .proj p c, k, j, h, hkj => by
    simp only [closedn] at h
    simp only [csubst, csubst_closedn f c k j h hkj]
  | .fix defs i, k, j, h, hkj => by
    simp only [closedn] at h
    simp only [csubst, csubstD_closedn f defs (k + defs.length) (j + defs.length) h (by omega)]
  | .prim _, _, _, _, _ => rfl
theorem csubstL_closedn (f : LBTerm) : ∀ (as : List LBTerm) (k j : Nat), closednL k as = true →
    k ≤ j → csubstL f j as = as
  | [], _, _, _, _ => rfl
  | a :: as, k, j, h, hkj => by
    simp only [closednL, Bool.and_eq_true] at h
    simp only [csubstL, csubst_closedn f a k j h.1 hkj, csubstL_closedn f as k j h.2 hkj]
theorem csubstB_closedn (f : LBTerm) : ∀ (bs : List (List BinderName × LBTerm)) (k j : Nat),
    closednB k bs = true → k ≤ j → csubstB f j bs = bs
  | [], _, _, _, _ => rfl
  | (ns, b) :: bs, k, j, h, hkj => by
    simp only [closednB, Bool.and_eq_true] at h
    simp only [csubstB, csubst_closedn f b (k + ns.length) (j + ns.length) h.1 (by omega),
      csubstB_closedn f bs k j h.2 hkj]
theorem csubstD_closedn (f : LBTerm) : ∀ (ds : List (@FixDef LBTerm)) (k j : Nat),
    closednD k ds = true → k ≤ j → csubstD f j ds = ds
  | [], _, _, _, _ => rfl
  | ⟨nm, b, r⟩ :: ds, k, j, h, hkj => by
    simp only [closednD, Bool.and_eq_true] at h
    simp only [csubstD, csubst_closedn f b k j h.1 hkj, csubstD_closedn f ds k j h.2 hkj]
end

theorem length_csubstD (f : LBTerm) (k : Nat) : ∀ ds : List (@FixDef LBTerm),
    (csubstD f k ds).length = ds.length
  | [] => rfl
  | ⟨_, _, _⟩ :: ds => by simp [csubstD, length_csubstD f k ds]

mutual
/-- Closed substitutions at two indices commute. -/
theorem csubst_comm {f g : LBTerm} (hf : closedn 0 f = true) (hg : closedn 0 g = true) :
    ∀ (t : LBTerm) (j n : Nat), j ≤ n →
      csubst f n (csubst g j t) = csubst g j (csubst f (n + 1) t)
  | .box, _, _, _ => rfl
  | .bvar m, j, n, h => by
    have cf : ∀ i, csubst g i f = f := fun i => csubst_closedn g f 0 i hf (Nat.zero_le _)
    have cg : ∀ i, csubst f i g = g := fun i => csubst_closedn f g 0 i hg (Nat.zero_le _)
    simp only [csubst]
    rcases Nat.lt_trichotomy j m with h1 | rfl | h1
    · rcases Nat.lt_trichotomy (n + 1) m with h2 | rfl | h2
      · rw [ite_eq_right (by omega), ite_eq_left h1, ite_eq_right (by omega), ite_eq_left h2]
        simp only [csubst]
        rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
      · rw [ite_eq_right (by omega), ite_eq_left h1, ite_eq_left rfl, cf]
        simp only [csubst]
        rw [ite_eq_left (by omega)]
      · rw [ite_eq_right (by omega), ite_eq_left h1, ite_eq_right (by omega), ite_eq_right (by omega)]
        simp only [csubst]
        rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h1]
    · rw [ite_eq_left rfl, cg, ite_eq_right (by omega), ite_eq_right (by omega)]
      simp [csubst]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      simp only [csubst]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  | .fvar _, _, _, _ => rfl
  | .lambda na b, j, n, h => by
    simp only [csubst, csubst_comm hf hg b (j + 1) (n + 1) (by omega)]
  | .letIn na b b', j, n, h => by
    simp only [csubst, csubst_comm hf hg b j n h, csubst_comm hf hg b' (j + 1) (n + 1) (by omega)]
  | .app u v, j, n, h => by
    simp only [csubst, csubst_comm hf hg u j n h, csubst_comm hf hg v j n h]
  | .const _, _, _, _ => rfl
  | .construct i c args, j, n, h => by
    simp only [csubst, csubstL_comm hf hg args j n h]
  | .case ip c brs, j, n, h => by
    simp only [csubst, csubst_comm hf hg c j n h, csubstB_comm hf hg brs j n h]
  | .proj p c, j, n, h => by
    simp only [csubst, csubst_comm hf hg c j n h]
  | .fix defs i, j, n, h => by
    simp only [csubst, length_csubstD]
    rw [csubstD_comm hf hg defs (j + defs.length) (n + defs.length) (by omega),
      show n + defs.length + 1 = n + 1 + defs.length by omega]
  | .prim _, _, _, _ => rfl
theorem csubstL_comm {f g : LBTerm} (hf : closedn 0 f = true) (hg : closedn 0 g = true) :
    ∀ (as : List LBTerm) (j n : Nat), j ≤ n →
      csubstL f n (csubstL g j as) = csubstL g j (csubstL f (n + 1) as)
  | [], _, _, _ => rfl
  | a :: as, j, n, h => by
    simp only [csubstL, csubst_comm hf hg a j n h, csubstL_comm hf hg as j n h]
theorem csubstB_comm {f g : LBTerm} (hf : closedn 0 f = true) (hg : closedn 0 g = true) :
    ∀ (bs : List (List BinderName × LBTerm)) (j n : Nat), j ≤ n →
      csubstB f n (csubstB g j bs) = csubstB g j (csubstB f (n + 1) bs)
  | [], _, _, _ => rfl
  | (ns, b) :: bs, j, n, h => by
    simp only [csubstB, csubstB_comm hf hg bs j n h,
      csubst_comm hf hg b (j + ns.length) (n + ns.length) (by omega),
      show n + ns.length + 1 = n + 1 + ns.length by omega]
theorem csubstD_comm {f g : LBTerm} (hf : closedn 0 f = true) (hg : closedn 0 g = true) :
    ∀ (ds : List (@FixDef LBTerm)) (j n : Nat), j ≤ n →
      csubstD f n (csubstD g j ds) = csubstD g j (csubstD f (n + 1) ds)
  | [], _, _, _ => rfl
  | ⟨nm, b, r⟩ :: ds, j, n, h => by
    simp only [csubstD, csubst_comm hf hg b j n h, csubstD_comm hf hg ds j n h]
end

/-- A closed term substituted at index `|gs|` below the closed terms `gs`. -/
theorem csubst_substl {f : LBTerm} (hf : closedn 0 f = true) :
    ∀ (gs : List LBTerm) (t : LBTerm), (∀ g ∈ gs, closedn 0 g = true) →
      csubst f 0 (substl gs t) = substl gs (csubst f gs.length t)
  | [], _, _ => rfl
  | g :: gs, t, hgs => by
    have hg := hgs g List.mem_cons_self
    have hgs' : ∀ g' ∈ gs, closedn 0 g' = true := fun g' h => hgs g' (List.mem_cons_of_mem _ h)
    show csubst f 0 (substl gs (csubst g 0 t)) = substl gs (csubst g 0 (csubst f (gs.length + 1) t))
    rw [csubst_substl hf gs _ hgs', csubst_comm hf hg t 0 gs.length (Nat.zero_le _)]

end TargetSubst

open TargetSubst

/-- The fields of `iota_red` substituted one by one: `substl` of the reversed fields substitutes the
first field at the index of the last binder, below the remaining fields, when the fields are
closed. Reference: `substl` (`MR E/ECSubst.v:46`) and `iota_red` (`MR E/EGlobalEnv.v:281`), with
`closed_subst` (`MR E/ECSubst.v`). -/
theorem substl_cons_closed {f t : LBTerm} {fs : List LBTerm} (hf : closedn 0 f = true)
    (hfs : ∀ g ∈ fs, closedn 0 g = true) :
    substl (f :: fs).reverse t = substl fs.reverse (csubst f fs.length t) := by
  rw [List.reverse_cons, substl, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [← List.length_reverse (as := fs)]
  exact csubst_substl hf fs.reverse t fun g hg => hfs g (List.mem_reverse.mp hg)

end EraseProof
