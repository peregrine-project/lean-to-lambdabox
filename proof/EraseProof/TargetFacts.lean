import EraseProof.Target

/-!
# Facts about λ□ evaluation

The induction principle of `LBEval` with a usable hypothesis for the nested premise of
`constructBlock` (`LBEval.ind`), and the inversion of evaluation results headed by `□`
(`LBEval.eq_box_of_headOf`).
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

end EraseProof
