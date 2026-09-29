import LeanToLambdaBox.Basic

/-!
# The target: λ□ on the shipping `LBTerm`

MetaRocq's weak call-by-value evaluation of λ□ (`MR E/EWcbvEval.v:119 eval`), transcribed onto the
shipping AST `LBTerm` (`LeanToLambdaBox/Basic.lean`), with the substitution, closedness and
environment-lookup functions it uses. `LBEval.closed`: evaluation of a closed term in an
environment of closed bodies gives a closed value (`MR E/EWcbvEval.v:1636 eval_closed`).
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

mutual
/-- Substituting a closed term for index `k ≤ m` lowers the bound by one. Reference:
`closed_csubst` (`MR E/ECSubst.v:127`, the case `k = 0`), proved there through `closed_subst`
(`:51`) and `closedn_subst` (`MR E/ELiftSubst.v:649`). -/
theorem closedn_csubst (t : LBTerm) (ht : closedn 0 t = true) :
    ∀ (b : LBTerm) {k m : Nat}, k ≤ m → closedn (m + 1) b = true →
      closedn m (csubst t k b) = true
  | .box, _, _, _, _ | .fvar _, _, _, _, _ | .const _, _, _, _, _ | .prim _, _, _, _, _ => rfl
  | .bvar n, k, m, hk, h => by
    simp only [closedn, decide_eq_true_eq] at h
    simp only [csubst]
    split
    · exact closedn_mono t (Nat.zero_le _) ht
    · split <;> simp only [closedn, decide_eq_true_eq] <;> omega
  | .lambda _ b, _, _, hk, h => closedn_csubst t ht b (Nat.add_le_add_right hk 1) h
  | .letIn _ b b', _, _, hk, h => by
    simp only [closedn, csubst, Bool.and_eq_true] at h ⊢
    exact ⟨closedn_csubst t ht b hk h.1,
      closedn_csubst t ht b' (Nat.add_le_add_right hk 1) h.2⟩
  | .app u v, _, _, hk, h => by
    simp only [closedn, csubst, Bool.and_eq_true] at h ⊢
    exact ⟨closedn_csubst t ht u hk h.1, closedn_csubst t ht v hk h.2⟩
  | .construct _ _ args, _, _, hk, h => closednL_csubst t ht args hk h
  | .case _ c brs, _, _, hk, h => by
    simp only [closedn, csubst, Bool.and_eq_true] at h ⊢
    exact ⟨closedn_csubst t ht c hk h.1, closednB_csubst t ht brs hk h.2⟩
  | .proj _ c, _, _, hk, h => closedn_csubst t ht c hk h
  | .fix defs _, _, m, hk, h => by
    simp only [closedn, csubst, csubstD_length] at h ⊢
    rw [Nat.add_right_comm] at h
    exact closednD_csubst t ht defs (Nat.add_le_add_right hk _) h
/-- `closedn_csubst` on argument lists. -/
theorem closednL_csubst (t : LBTerm) (ht : closedn 0 t = true) :
    ∀ (as : List LBTerm) {k m : Nat}, k ≤ m → closednL (m + 1) as = true →
      closednL m (csubstL t k as) = true
  | [], _, _, _, _ => rfl
  | a :: as, _, _, hk, h => by
    simp only [closednL, csubstL, Bool.and_eq_true] at h ⊢
    exact ⟨closedn_csubst t ht a hk h.1, closednL_csubst t ht as hk h.2⟩
/-- `closedn_csubst` on case branches. -/
theorem closednB_csubst (t : LBTerm) (ht : closedn 0 t = true) :
    ∀ (bs : List (List BinderName × LBTerm)) {k m : Nat}, k ≤ m → closednB (m + 1) bs = true →
      closednB m (csubstB t k bs) = true
  | [], _, _, _, _ => rfl
  | (_, b) :: bs, _, _, hk, h => by
    simp only [closednB, csubstB, Bool.and_eq_true] at h ⊢
    rw [Nat.add_right_comm] at h
    exact ⟨closedn_csubst t ht b (Nat.add_le_add_right hk _) h.1,
      closednB_csubst t ht bs hk h.2⟩
/-- `closedn_csubst` on fixpoint bodies. -/
theorem closednD_csubst (t : LBTerm) (ht : closedn 0 t = true) :
    ∀ (ds : List (@FixDef LBTerm)) {k m : Nat}, k ≤ m → closednD (m + 1) ds = true →
      closednD m (csubstD t k ds) = true
  | [], _, _, _, _ => rfl
  | ⟨_, b, _⟩ :: ds, _, _, hk, h => by
    simp only [closednD, csubstD, Bool.and_eq_true] at h ⊢
    exact ⟨closedn_csubst t ht b hk h.1, closednD_csubst t ht ds hk h.2⟩
end

/-- An application spine is closed iff its head and arguments are. Reference: `closedn_mkApps`
(`MR E/EWcbvEval.v:1556`). -/
theorem closedn_mkApps {k : Nat} : ∀ {f : LBTerm} {args : List LBTerm},
    closedn k (mkApps f args) = true ↔ closedn k f = true ∧ ∀ a ∈ args, closedn k a = true
  | _, [] => by simp [mkApps]
  | _, a :: as => by
    simp only [mkApps, closedn_mkApps, closedn, Bool.and_eq_true, List.mem_cons,
      forall_eq_or_imp, and_assoc]

/-- Substituting closed terms for the `ts.length` innermost indices. Reference: `closed_substl`
(`MR E/ECSubst.v:147`). -/
theorem closedn_substl {k : Nat} : ∀ {ts : List LBTerm} {b : LBTerm},
    (∀ t ∈ ts, closedn 0 t = true) → closedn (k + ts.length) b = true →
      closedn k (substl ts b) = true
  | [], _, _, hb => hb
  | t :: ts, b, hts, hb => by
    simp only [substl, List.foldl_cons] at hb ⊢
    refine closedn_substl (fun u hu => hts u (List.mem_cons_of_mem _ hu)) ?_
    rw [List.length_cons, ← Nat.add_assoc] at hb
    exact closedn_csubst t (hts t List.mem_cons_self) b (Nat.zero_le _) hb

/-- A branch of a closed case is closed under its binders. Reference: `nth_error_forallb`
(`MR utils/theories/All_Forall.v:379`), as `eval_closed` uses it. -/
theorem closednB_getElem? {k : Nat} : ∀ {bs : List (List BinderName × LBTerm)} {c : Nat}
    {br : List BinderName × LBTerm}, closednB k bs = true → bs[c]? = some br →
      closedn (k + br.1.length) br.2 = true
  | [], _, _, _, h => nomatch h
  | (_, _) :: _, 0, _, h, hc => by
    simp only [closednB, Bool.and_eq_true] at h
    cases hc; exact h.1
  | _ :: _, _ + 1, _, h, hc => by
    simp only [closednB, Bool.and_eq_true] at h
    exact closednB_getElem? h.2 hc

/-- A body of a closed fixpoint is closed under the fixpoint's binders. Reference:
`nth_error_forallb` (`MR utils/theories/All_Forall.v:379`), as `closed_cunfold_fix` uses it. -/
theorem closednD_getElem? {k : Nat} : ∀ {ds : List (@FixDef LBTerm)} {i : Nat}
    {d : @FixDef LBTerm}, closednD k ds = true → ds[i]? = some d → closedn k d.body = true
  | [], _, _, _, h => nomatch h
  | ⟨_, _, _⟩ :: _, 0, _, h, hi => by
    simp only [closednD, Bool.and_eq_true] at h
    cases hi; exact h.1
  | ⟨_, _, _⟩ :: _, _ + 1, _, h, hi => by
    simp only [closednD, Bool.and_eq_true] at h
    exact closednD_getElem? h.2 hi

/-- Unfolding a closed fixpoint gives a closed term. Reference: `closed_cunfold_fix`
(`MR E/EWcbvEval.v:1584`), with `closed_fix_subst` (`:1562`). -/
theorem closedn_cunfoldFix (h : closedn 0 (.fix defs i) = true)
    (hu : cunfoldFix defs i = some (n, fn)) : closedn 0 fn = true := by
  simp only [cunfoldFix, Option.map_eq_some_iff, Prod.mk.injEq] at hu
  obtain ⟨d, hd, -, rfl⟩ := hu
  simp only [closedn, Nat.zero_add] at h
  refine closedn_substl ?_ ?_
  · intro t ht
    simp only [fixSubst, List.mem_map, List.mem_reverse, List.mem_range] at ht
    obtain ⟨j, -, rfl⟩ := ht
    simpa [closedn] using h
  · simpa [fixSubst] using closednD_getElem? h hd

section
variable {lenv : GlobalDeclarations}

/-- λ□ evaluation of a closed term in a closed environment gives a closed value. Reference:
`eval_closed` (`MR E/EWcbvEval.v:1636`). -/
theorem LBEval.closed (hl : LenvClosed lenv) (ht : closedn 0 t = true)
    (h : LBEval fl lenv t v) : closedn 0 v = true := by
  induction h with
  | box _ _ => rfl
  | beta _ _ _ ih1 ih2 ih3 =>
    simp only [closedn, Bool.and_eq_true] at ht
    exact ih3 (closedn_csubst _ (ih2 ht.2) _ (Nat.zero_le _) (ih1 ht.1))
  | zeta _ _ ih1 ih2 =>
    simp only [closedn, Bool.and_eq_true] at ht
    exact ih2 (closedn_csubst _ (ih1 ht.1) _ (Nat.zero_le _) ht.2)
  | iota _ _ _ hbr _ hdrop _ ih1 ih2 =>
    simp only [closedn, Bool.and_eq_true] at ht
    have hargs := (closedn_mkApps.1 (ih1 ht.1)).2
    refine ih2 (closedn_substl (fun a ha => hargs a ?_) ?_)
    · exact List.mem_of_mem_drop (List.mem_reverse.1 ha)
    · rw [List.length_reverse, hdrop]
      exact closednB_getElem? ht.2 hbr
  | iotaSing _ _ _ hbrs _ _ ih2 =>
    simp only [closedn, Bool.and_eq_true] at ht
    subst hbrs
    refine ih2 (closedn_substl (fun a ha => ?_) ?_)
    · rw [List.eq_of_mem_replicate ha]; rfl
    · rw [List.length_replicate]; simpa [closednB] using ht.2
  | fix _ _ _ hu _ ih1 ih2 ih3 =>
    simp only [closedn, Bool.and_eq_true] at ht
    have ⟨hfix, hargs⟩ := closedn_mkApps.1 (ih1 ht.1)
    apply ih3
    simp only [closedn, Bool.and_eq_true]
    exact ⟨closedn_mkApps.2 ⟨closedn_cunfoldFix hfix hu, hargs⟩, ih2 ht.2⟩
  | fixValue _ _ _ _ _ ih1 ih2 =>
    simp only [closedn, Bool.and_eq_true] at ht ⊢
    exact ⟨ih1 ht.1, ih2 ht.2⟩
  | fix' _ _ hu _ _ ih1 ih2 ih3 =>
    simp only [closedn, Bool.and_eq_true] at ht
    apply ih3
    simp only [closedn, Bool.and_eq_true]
    exact ⟨closedn_cunfoldFix (ih1 ht.1) hu, ih2 ht.2⟩
  | delta hc hb _ ih => exact ih (hl _ _ _ hc hb).1
  | proj _ _ _ _ hget _ ih1 ih2 =>
    exact ih2 ((closedn_mkApps.1 (ih1 ht)).2 _ (List.mem_of_getElem? hget))
  | projProp => rfl
  | construct _ _ _ _ _ ih1 ih2 =>
    simp only [closedn, Bool.and_eq_true] at ht ⊢
    exact ⟨ih1 ht.1, ih2 ht.2⟩
  | appCong _ _ _ ih1 ih2 =>
    simp only [closedn, Bool.and_eq_true] at ht ⊢
    exact ⟨ih1 ht.1, ih2 ht.2⟩
  | prim => exact ht
  | atom => exact ht

end

end EraseProof
