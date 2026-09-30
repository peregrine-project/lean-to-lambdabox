import LeanToLambdaBox.Basic

/-!
# The target: λ□ on the shipping `LBTerm`

MetaRocq's weak call-by-value evaluation of λ□ (`MR E/EWcbvEval.v:119 eval`), transcribed onto the
shipping AST `LBTerm` (`LeanToLambdaBox/Basic.lean`), with the substitution, closedness and
environment-lookup functions it uses.
-/

open Lean

namespace EraseProof

/-- Reference: `MR E/EWcbvEval.v:34 WcbvFlags`. -/
structure WcbvFlags where
  with_prop_case : Bool
  with_guarded_fix : Bool
  with_constructor_as_block : Bool

/-- The flags of `erases_correct`. Reference: `MR E/EWcbvEval.v:69 default_wcbv_flags`. -/
def defaultFlags : WcbvFlags := ⟨true, true, false⟩

mutual
/-- Closed substitution of `t` for index `k`. Reference: `MR E/ECSubst.v:14 csubst`. -/
def csubst (t : LBTerm) (k : Nat) : LBTerm → LBTerm
  | .box => .box
  | .bvar n => if k = n then t else if k < n then .bvar (n - 1) else .bvar n
  | .fvar x => .fvar x
  | .lambda na b => .lambda na (csubst t (k + 1) b)
  | .letIn na b b' => .letIn na (csubst t k b) (csubst t (k + 1) b')
  | .app u v => .app (csubst t k u) (csubst t k v)
  | .const kn => .const kn
  | .construct i n args => .construct i n (csubstL t k args)
  | .case ip c brs => .case ip (csubst t k c) (csubstB t k brs)
  | .proj p c => .proj p (csubst t k c)
  | .fix defs i => .fix (csubstD t (k + defs.length) defs) i
  | .prim p => .prim p
/-- `csubst` on argument lists (part of `MR E/ECSubst.v:14 csubst`). -/
def csubstL (t : LBTerm) (k : Nat) : List LBTerm → List LBTerm
  | [] => []
  | a :: as => csubst t k a :: csubstL t k as
/-- `csubst` on case branches (part of `MR E/ECSubst.v:14 csubst`). -/
def csubstB (t : LBTerm) (k : Nat) :
    List (List BinderName × LBTerm) → List (List BinderName × LBTerm)
  | [] => []
  | (ns, b) :: bs => (ns, csubst t (k + ns.length) b) :: csubstB t k bs
/-- `csubst` on fixpoint bodies (part of `MR E/ECSubst.v:14 csubst`). -/
def csubstD (t : LBTerm) (k : Nat) : List (@FixDef LBTerm) → List (@FixDef LBTerm)
  | [] => []
  | ⟨nm, b, r⟩ :: ds => ⟨nm, csubst t k b, r⟩ :: csubstD t k ds
end

mutual
/-- Every loose bound variable is below `k`. Reference: `MR E/ELiftSubst.v:90 closedn`. -/
def closedn (k : Nat) : LBTerm → Bool
  | .box | .fvar _ | .const _ | .prim _ => true
  | .bvar n => n < k
  | .lambda _ b => closedn (k + 1) b
  | .letIn _ b b' => closedn k b && closedn (k + 1) b'
  | .app u v => closedn k u && closedn k v
  | .construct _ _ args => closednL k args
  | .case _ c brs => closedn k c && closednB k brs
  | .proj _ c => closedn k c
  | .fix defs _ => closednD (k + defs.length) defs
/-- `closedn` on argument lists (part of `MR E/ELiftSubst.v:90 closedn`). -/
def closednL (k : Nat) : List LBTerm → Bool
  | [] => true
  | a :: as => closedn k a && closednL k as
/-- `closedn` on case branches (part of `MR E/ELiftSubst.v:90 closedn`). -/
def closednB (k : Nat) : List (List BinderName × LBTerm) → Bool
  | [] => true
  | (ns, b) :: bs => closedn (k + ns.length) b && closednB k bs
/-- `closedn` on fixpoint bodies (part of `MR E/ELiftSubst.v:90 closedn`). -/
def closednD (k : Nat) : List (@FixDef LBTerm) → Bool
  | [] => true
  | ⟨_, b, _⟩ :: ds => closedn k b && closednD k ds
end

mutual
/-- `x` occurs free. Reference: none (`LBTerm.fvar` has no MetaRocq counterpart, DV-13, DV-16). -/
def hasFVar (x : FVarId) : LBTerm → Bool
  | .box | .bvar _ | .const _ | .prim _ => false
  | .fvar y => x == y
  | .lambda _ b => hasFVar x b
  | .letIn _ b b' => hasFVar x b || hasFVar x b'
  | .app u v => hasFVar x u || hasFVar x v
  | .construct _ _ args => hasFVarL x args
  | .case _ c brs => hasFVar x c || hasFVarB x brs
  | .proj _ c => hasFVar x c
  | .fix defs _ => hasFVarD x defs
/-- `hasFVar` on argument lists (part of `hasFVar`; no MetaRocq counterpart). -/
def hasFVarL (x : FVarId) : List LBTerm → Bool
  | [] => false
  | a :: as => hasFVar x a || hasFVarL x as
/-- `hasFVar` on case branches (part of `hasFVar`; no MetaRocq counterpart). -/
def hasFVarB (x : FVarId) : List (List BinderName × LBTerm) → Bool
  | [] => false
  | (_, b) :: bs => hasFVar x b || hasFVarB x bs
/-- `hasFVar` on fixpoint bodies (part of `hasFVar`; no MetaRocq counterpart). -/
def hasFVarD (x : FVarId) : List (@FixDef LBTerm) → Bool
  | [] => false
  | ⟨_, b, _⟩ :: ds => hasFVar x b || hasFVarD x ds
end

/-- Reference: `MR E/EAst.v:51 mkApps`. -/
def mkApps (t : LBTerm) : List LBTerm → LBTerm
  | [] => t
  | a :: as => mkApps (.app t a) as

/-- Reference: `MR E/ECSubst.v:46 substl`. -/
def substl (ts : List LBTerm) (b : LBTerm) : LBTerm := ts.foldl (fun b t => csubst t 0 b) b

/-- `[tFix l (n-1); …; tFix l 0]`. Reference: `MR E/EGlobalEnv.v:210 fix_subst`. -/
def fixSubst (defs : List (@FixDef LBTerm)) : List LBTerm :=
  (List.range defs.length).reverse.map (fun i => .fix defs i)

/-- Reference: `MR E/EGlobalEnv.v:238 cunfold_fix`. -/
def cunfoldFix (defs : List (@FixDef LBTerm)) (i : Nat) : Option (Nat × LBTerm) :=
  (defs[i]?).map fun d => (d.principalArgIdx, substl (fixSubst defs) d.body)

/-- Reference: `MR E/EGlobalEnv.v:54 lookup_constant` (with `lookup_env`, `:16`). -/
def lookupConst (lenv : GlobalDeclarations) (kn : Kername) : Option ConstantBody :=
  match lenv.find? (·.1 == kn) with
  | some (_, .constantDecl cb) => some cb
  | _ => none

/-- Every stored body is closed and has no free variable. Reference: `MR E/EGlobalEnv.v:181
closed_env`, plus the absence of `fvar` (DV-13). -/
def LenvClosed (lenv : GlobalDeclarations) : Prop :=
  ∀ kn cb b, lookupConst lenv kn = some cb → cb.cst_body = some b →
    closedn 0 b = true ∧ ∀ x, hasFVar x b = false

/-- Reference: `MR E/EGlobalEnv.v:68 lookup_inductive`. -/
def lookupInd (lenv : GlobalDeclarations) (ind : InductiveId) :
    Option (MutualInductiveBody × OneInductiveBody) :=
  match lenv.find? (·.1 == ind.mutualBlockName) with
  | some (_, .inductiveDecl mib) => (mib.bodies[ind.idx]?).map (mib, ·)
  | _ => none

/-- Reference: `MR E/EGlobalEnv.v:81 lookup_constructor`. -/
def lookupCtor (lenv : GlobalDeclarations) (ind : InductiveId) (c : Nat) :
    Option (MutualInductiveBody × OneInductiveBody × ConstructorBody) := do
  let (mib, oib) ← lookupInd lenv ind
  let cb ← oib.ctors[c]?
  pure (mib, oib, cb)

/-- Reference: `MR E/EGlobalEnv.v:169 constructor_isprop_pars_decl`. -/
def ctorIsPropParsDecl (lenv : GlobalDeclarations) (ind : InductiveId) (c : Nat) :
    Option (Bool × Nat × ConstructorBody) :=
  (lookupCtor lenv ind c).map fun (mib, oib, cb) => (oib.propositional, mib.npars, cb)

/-- Reference: `MR E/EGlobalEnv.v:164 inductive_isprop_and_pars`. -/
def indIsPropAndPars (lenv : GlobalDeclarations) (ind : InductiveId) : Option (Bool × Nat) :=
  (lookupInd lenv ind).map fun (mib, oib) => (oib.propositional, mib.npars)

/-- Reference: `MR E/EGlobalEnv.v:281 iota_red`. -/
def iotaRed (pars : Nat) (args : List LBTerm) (br : List BinderName × LBTerm) : LBTerm :=
  substl (args.drop pars).reverse br.2

/-- Reference: `MR E/EAstUtils.v:18 head`. -/
def headOf : LBTerm → LBTerm | .app f _ => headOf f | t => t
/-- Reference: `MR E/EAst.v:65 isLambda`. -/
def isLambdaT : LBTerm → Bool | .lambda .. => true | _ => false
/-- Reference: `MR E/EAstUtils.v:309 isBox`. -/
def isBoxT : LBTerm → Bool | .box => true | _ => false
/-- Reference: `MR E/EAstUtils.v:284 isFix`. -/
def isFixT : LBTerm → Bool | .fix .. => true | _ => false
/-- Reference: `MR E/EAstUtils.v:327 isFixApp`. -/
def isFixApp (t : LBTerm) : Bool := isFixT (headOf t)
/-- Reference: `MR E/EAstUtils.v:328 isConstructApp`. -/
def isConstructApp (t : LBTerm) : Bool := match headOf t with | .construct .. => true | _ => false
/-- Reference: `MR E/EAstUtils.v:329 isPrimApp`. -/
def isPrimApp (t : LBTerm) : Bool := match headOf t with | .prim .. => true | _ => false

/-- Reference: `MR E/EWcbvEval.v:36 atom` (no `tCoFix`, `tLazy` in `LBTerm`, DV-16). -/
def lbAtom (fl : WcbvFlags) (lenv : GlobalDeclarations) : LBTerm → Bool
  | .box | .lambda .. | .fix .. => true
  | .construct ind c [] => !fl.with_constructor_as_block && (lookupCtor lenv ind c).isSome
  | _ => false

/-- λ□ big-step weak call-by-value evaluation: every rule whose term constructor exists in
`LBTerm` (DV-16). Reference: `MR E/EWcbvEval.v:119 eval`; MC §7.1 (Fig. 16 and the three
amendments, p. 8:60); Let. CIC□ with Def. 5 (□-reduction). -/
inductive LBEval (fl : WcbvFlags) (lenv : GlobalDeclarations) : LBTerm → LBTerm → Prop
  /-- `eval_box` (`MR E/EWcbvEval.v:121`). -/
  | box : LBEval fl lenv a .box → LBEval fl lenv t t' → LBEval fl lenv (.app a t) .box
  /-- `eval_beta` (`:127`). -/
  | beta : LBEval fl lenv f (.lambda na b) → LBEval fl lenv a a' →
      LBEval fl lenv (csubst a' 0 b) res → LBEval fl lenv (.app f a) res
  /-- `eval_zeta` (`:134`). -/
  | zeta : LBEval fl lenv b0 b0' → LBEval fl lenv (csubst b0' 0 b1) res →
      LBEval fl lenv (.letIn na b0 b1) res
  /-- `eval_iota` (`:140`). -/
  | iota : fl.with_constructor_as_block = false →
      LBEval fl lenv discr (mkApps (.construct ind c []) args) →
      ctorIsPropParsDecl lenv ind c = some (false, pars, cdecl) →
      brs[c]? = some br → args.length = pars + cdecl.nargs →
      (args.drop pars).length = br.1.length →
      LBEval fl lenv (iotaRed pars args br) res → LBEval fl lenv (.case (ind, pars) discr brs) res
  /-- `eval_iota_sing` (`:162`). -/
  | iotaSing : fl.with_prop_case = true → LBEval fl lenv discr .box →
      indIsPropAndPars lenv ind = some (true, pars) → brs = [(n, f)] →
      LBEval fl lenv (substl (List.replicate n.length .box) f) res →
      LBEval fl lenv (.case (ind, pars) discr brs) res
  /-- `eval_fix` (`:171`). -/
  | fix : fl.with_guarded_fix = true →
      LBEval fl lenv f (mkApps (.fix mfix idx) argsv) → LBEval fl lenv a av →
      cunfoldFix mfix idx = some (argsv.length, fn) →
      LBEval fl lenv (.app (mkApps fn argsv) av) res → LBEval fl lenv (.app f a) res
  /-- `eval_fix_value` (`:180`). -/
  | fixValue : fl.with_guarded_fix = true →
      LBEval fl lenv f (mkApps (.fix mfix idx) argsv) → LBEval fl lenv a av →
      cunfoldFix mfix idx = some (narg, fn) → argsv.length < narg →
      LBEval fl lenv (.app f a) (.app (mkApps (.fix mfix idx) argsv) av)
  /-- `eval_fix'` (`:189`). -/
  | fix' : fl.with_guarded_fix = false → LBEval fl lenv f (.fix mfix idx) →
      cunfoldFix mfix idx = some (narg, fn) → LBEval fl lenv a av →
      LBEval fl lenv (.app fn av) res → LBEval fl lenv (.app f a) res
  /-- `eval_delta` (`:212`). -/
  | delta : lookupConst lenv c = some decl → decl.cst_body = some body →
      LBEval fl lenv body res → LBEval fl lenv (.const c) res
  /-- `eval_proj` (`:218`). -/
  | proj : fl.with_constructor_as_block = false →
      LBEval fl lenv discr (mkApps (.construct p.indType 0 []) args) →
      ctorIsPropParsDecl lenv p.indType 0 = some (false, p.paramCount, cdecl) →
      args.length = p.paramCount + cdecl.nargs → args[p.paramCount + p.fieldIdx]? = some a →
      LBEval fl lenv a res → LBEval fl lenv (.proj p discr) res
  /-- `eval_proj_prop` (`:238`). -/
  | projProp : fl.with_prop_case = true → LBEval fl lenv discr .box →
      indIsPropAndPars lenv p.indType = some (true, p.paramCount) →
      LBEval fl lenv (.proj p discr) .box
  /-- `eval_construct` (`:245`). -/
  | construct : fl.with_constructor_as_block = false →
      lookupCtor lenv ind c = some (mdecl, idecl, cdecl) →
      LBEval fl lenv f (mkApps (.construct ind c []) args) →
      args.length < mdecl.npars + cdecl.nargs → LBEval fl lenv a a' →
      LBEval fl lenv (.app f a) (.app (mkApps (.construct ind c []) args) a')
  /-- `eval_app_cong` (`:262`). -/
  | appCong : LBEval fl lenv f f' →
      (isLambdaT f' || (if fl.with_guarded_fix then isFixApp f' else isFixT f') || isBoxT f' ||
        isConstructApp f' || isPrimApp f') = false →
      LBEval fl lenv a a' → LBEval fl lenv (.app f a) (.app f' a')
  /-- `eval_prim` (`:275`), `primInt` only. -/
  | prim : LBEval fl lenv (.prim p) (.prim p)
  /-- `eval_atom` (`:285`). -/
  | atom : lbAtom fl lenv t = true → LBEval fl lenv t t

/-! ## Closedness is preserved by evaluation -/

mutual
/-- `closedn` is monotone in the bound. Reference: `closed_upwards` (`MR E/ELiftSubst.v:487`). -/
theorem closedn_mono : ∀ (b : LBTerm) {k k' : Nat}, k ≤ k' → closedn k b = true →
    closedn k' b = true
  | .box, _, _, _, _ | .fvar _, _, _, _, _ | .const _, _, _, _, _ | .prim _, _, _, _, _ => rfl
  | .bvar _, _, _, hk, h => by simp only [closedn, decide_eq_true_eq] at h ⊢; omega
  | .lambda _ b, _, _, hk, h => closedn_mono b (Nat.add_le_add_right hk 1) h
  | .letIn _ b b', _, _, hk, h => by
    simp only [closedn, Bool.and_eq_true] at h ⊢
    exact ⟨closedn_mono b hk h.1, closedn_mono b' (Nat.add_le_add_right hk 1) h.2⟩
  | .app u v, _, _, hk, h => by
    simp only [closedn, Bool.and_eq_true] at h ⊢
    exact ⟨closedn_mono u hk h.1, closedn_mono v hk h.2⟩
  | .construct _ _ args, _, _, hk, h => closednL_mono args hk h
  | .case _ c brs, _, _, hk, h => by
    simp only [closedn, Bool.and_eq_true] at h ⊢
    exact ⟨closedn_mono c hk h.1, closednB_mono brs hk h.2⟩
  | .proj _ c, _, _, hk, h => closedn_mono c hk h
  | .fix defs _, _, _, hk, h => closednD_mono defs (Nat.add_le_add_right hk _) h
/-- `closednL` is monotone in the bound (part of `closedn_mono`). -/
theorem closednL_mono : ∀ (as : List LBTerm) {k k' : Nat}, k ≤ k' → closednL k as = true →
    closednL k' as = true
  | [], _, _, _, _ => rfl
  | a :: as, _, _, hk, h => by
    simp only [closednL, Bool.and_eq_true] at h ⊢
    exact ⟨closedn_mono a hk h.1, closednL_mono as hk h.2⟩
/-- `closednB` is monotone in the bound (part of `closedn_mono`). -/
theorem closednB_mono : ∀ (bs : List (List BinderName × LBTerm)) {k k' : Nat}, k ≤ k' →
    closednB k bs = true → closednB k' bs = true
  | [], _, _, _, _ => rfl
  | (_, b) :: bs, _, _, hk, h => by
    simp only [closednB, Bool.and_eq_true] at h ⊢
    exact ⟨closedn_mono b (Nat.add_le_add_right hk _) h.1, closednB_mono bs hk h.2⟩
/-- `closednD` is monotone in the bound (part of `closedn_mono`). -/
theorem closednD_mono : ∀ (ds : List (@FixDef LBTerm)) {k k' : Nat}, k ≤ k' →
    closednD k ds = true → closednD k' ds = true
  | [], _, _, _, _ => rfl
  | ⟨_, b, _⟩ :: ds, _, _, hk, h => by
    simp only [closednD, Bool.and_eq_true] at h ⊢
    exact ⟨closedn_mono b hk h.1, closednD_mono ds hk h.2⟩
end

/-- `csubstD` keeps the number of fixpoint bodies. -/
theorem csubstD_length (t : LBTerm) (k : Nat) :
    ∀ ds : List (@FixDef LBTerm), (csubstD t k ds).length = ds.length
  | [] => rfl
  | ⟨_, _, _⟩ :: ds => by simp only [csubstD, List.length_cons, csubstD_length t k ds]

end EraseProof
