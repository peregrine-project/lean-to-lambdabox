import EraseProof.Core.RegisterInd
import EraseProof.Oracle.Rename
import EraseProof.Relation.Abstract

/-!
# Steps of the shipping core's correctness

`erasePure_erases` is proved by induction on the fuel of the shipping traversal
(`Erasure.visitExpr` and the functions it calls, `LeanToLambdaBox/Erasure.lean`) run at the pure
backend `Erasure.PureM`. Its statement at one fuel is `ExprSpec`: a successful run of `visitExpr`
on a term returns an erasure (`Erases noCert`) of every marking (`MarkOf`) of it, closed, with
erased λ□ dependencies (`ErasesDeps`), and the run keeps the state invariant `StateOK`, grows the
λ□ environment freshly and registers only constants of a scope (`Grows`, `ScopeOK`).

The marking opens a binder with any fresh variable, the traversal with the next variable of the
pure backend's counter (`pureFVar`). `ExprSpec` therefore relates a marking under the locals `ls`
to a run on the renamed term under the traversal's locals (`RenOK`: the renaming `ρ` sends the
locals `ls` to the traversal's locals on the scope `S` of the term); the oracle's answers agree
(`Pure.isErasable_ren`), so the traversal returns `□` exactly where the marking has an `erase` mark
(`visitExpr_box`). With `ρ` the identity and no locals this is the statement of `erasePure_erases`;
with no marking locals and any traversal locals it is the erasure of a closed value under the
caller's locals, which `visitMutual` performs.

This module proves the steps of the cases of `visitExpr` that are not applications, constants,
projections or literals: the oracle's `□` (`visitExpr_box`), a free variable, the terms
`visitExpr` rejects, metadata, a λ and a `let`.

Reference: `erases_erase` (`MR E/ErasureFunction.v:1228`), case by case over `erase`
(`MR E/ErasureFunction.v:989`); adapted from `ML-V Core/Steps.lean`, whose typing premises are
replaced by the marking.
-/

open Lean Erasure

namespace EraseProof

namespace Steps

open RegisterInd OracleRen

/-! ## Closed λ□ terms under the traversal's abstraction (copy of `ML-V Core/Steps.lean:535`) -/

mutual
/-- Turning a free variable into the bound variable `k` keeps a term closed one level up. -/
theorem closedn_toBvar (x : FVarId) : ∀ (t : LBTerm) (k : Nat), closedn k t = true →
    closedn (k + 1) (toBvar x k t) = true
  | .box, _, _ => rfl
  | .bvar i, k, h => by simp only [toBvar, closedn, decide_eq_true_eq] at h ⊢; omega
  | .fvar y, k, _ => by
    simp only [toBvar]
    split
    · simp [closedn]
    · rfl
  | .lambda _ b, k, h => closedn_toBvar x b (k + 1) h
  | .letIn _ v b, k, h => by
    simp only [toBvar, closedn, Bool.and_eq_true] at h ⊢
    exact ⟨closedn_toBvar x v k h.1, closedn_toBvar x b (k + 1) h.2⟩
  | .app a b, k, h => by
    simp only [toBvar, closedn, Bool.and_eq_true] at h ⊢
    exact ⟨closedn_toBvar x a k h.1, closedn_toBvar x b k h.2⟩
  | .const _, _, _ => rfl
  | .construct _ _ args, k, h => closednL_toBvarList x args k h
  | .case (_, _) d alts, k, h => by
    simp only [toBvar, closedn, Bool.and_eq_true] at h ⊢
    exact ⟨closedn_toBvar x d k h.1, closednB_toBvarAlts x alts k h.2⟩
  | .proj _ e, k, h => closedn_toBvar x e k h
  | .fix defs _, k, h => by
    simp only [toBvar, closedn] at h ⊢
    rw [TargetLift.length_toBvarDefs, show k + 1 + defs.length = k + defs.length + 1 by omega]
    exact closednD_toBvarDefs x defs (k + defs.length) h
  | .prim _, _, _ => rfl

theorem closednL_toBvarList (x : FVarId) : ∀ (as : List LBTerm) (k : Nat),
    closednL k as = true → closednL (k + 1) (toBvarList x k as) = true
  | [], _, _ => rfl
  | a :: as, k, h => by
    simp only [toBvarList, closednL, Bool.and_eq_true] at h ⊢
    exact ⟨closedn_toBvar x a k h.1, closednL_toBvarList x as k h.2⟩

theorem closednB_toBvarAlts (x : FVarId) : ∀ (bs : List (List BinderName × LBTerm)) (k : Nat),
    closednB k bs = true → closednB (k + 1) (toBvarAlts x k bs) = true
  | [], _, _ => rfl
  | (ns, b) :: bs, k, h => by
    simp only [toBvarAlts, closednB, Bool.and_eq_true] at h ⊢
    refine ⟨?_, closednB_toBvarAlts x bs k h.2⟩
    rw [show k + 1 + ns.length = k + ns.length + 1 by omega]
    exact closedn_toBvar x b (k + ns.length) h.1

theorem closednD_toBvarDefs (x : FVarId) : ∀ (ds : List (@FixDef LBTerm)) (k : Nat),
    closednD k ds = true → closednD (k + 1) (toBvarDefs x k ds) = true
  | [], _, _ => rfl
  | ⟨_, b, _⟩ :: ds, k, h => by
    simp only [toBvarDefs, closednD, Bool.and_eq_true] at h ⊢
    exact ⟨closedn_toBvar x b k h.1, closednD_toBvarDefs x ds k h.2⟩
end

/-! ## Opening a binder keeps the syntactic invariants -/

/-- Opening a binder with a free variable keeps the constants. Copy of
`ML-V Core/Steps.lean:1108`. -/
theorem ConstsIn_inst_fvar {p : Name → Prop} {x : FVarId} :
    ∀ {b : Expr} {k : Nat}, ConstsIn p b → ConstsIn p (b.instantiate1' (.fvar x) k)
  | .bvar i, k, _ => by
    simp only [Expr.instantiate1']
    split
    · trivial
    · split <;> trivial
  | .app f a, _, h => ⟨ConstsIn_inst_fvar (b := f) h.1, ConstsIn_inst_fvar (b := a) h.2⟩
  | .lam _ t b _, _, h | .forallE _ t b _, _, h =>
    ⟨ConstsIn_inst_fvar (b := t) h.1, ConstsIn_inst_fvar (b := b) h.2⟩
  | .letE _ t v b _, _, h =>
    ⟨ConstsIn_inst_fvar (b := t) h.1, ConstsIn_inst_fvar (b := v) h.2.1,
      ConstsIn_inst_fvar (b := b) h.2.2⟩
  | .mdata _ e, _, h => ConstsIn_inst_fvar (b := e) h
  | .proj _ _ e, _, h => ⟨h.1, ConstsIn_inst_fvar (b := e) h.2⟩
  | .const .., _, h => h
  | .sort _, _, _ | .fvar _, _, _ | .mvar _, _, _ | .lit _, _, _ => trivial

/-- Opening a binder with a free variable keeps the occurrences the traversal reads. Adapted from
`ML-V Core/Steps.lean:699 occursAt_inst_fvar`. -/
theorem nameOccurs_inst_fvar {c : Name} {x : FVarId} :
    ∀ (b : Expr) (k : Nat), nameOccurs c (b.instantiate1' (.fvar x) k) = nameOccurs c b
  | .bvar i, k => by
    simp only [Expr.instantiate1']
    split
    · rfl
    · split <;> rfl
  | .app f a, k => by
    simp only [Expr.instantiate1', nameOccurs, nameOccurs_inst_fvar f, nameOccurs_inst_fvar a]
  | .lam _ _ b _, k => by simp only [Expr.instantiate1', nameOccurs, nameOccurs_inst_fvar b]
  | .letE _ _ v b _, k => by
    simp only [Expr.instantiate1', nameOccurs, nameOccurs_inst_fvar v, nameOccurs_inst_fvar b]
  | .mdata _ e, k => by simp only [Expr.instantiate1', nameOccurs, nameOccurs_inst_fvar e]
  | .proj _ _ e, k => by simp only [Expr.instantiate1', nameOccurs, nameOccurs_inst_fvar e]
  | .forallE .., _ | .const .., _ | .sort _, _ | .fvar _, _ | .mvar _, _ | .lit _, _ => rfl

/-- Under `nat := .machine`, `e` has no Nat literal and none of the machine-integer constants that
`Erasure.exprConsts` excludes under that configuration (`PlainExpr`'s clause, with free variables
admitted): the traversal erases them to primitive integers (`visitLiteral`, `visitConstructor`,
`visitCasesOn`), which the erasure relation does not model. Adapted from
`ML-V Core/Steps.lean:755 NatPlain` and `ML-V Core/Frame.lean:42 MachineFree`. Reference: none. -/
def NatPlain (cfg : ErasureConfig) : Expr → Prop
  | .lit (.natVal _) => cfg.nat = .peano
  | .const c _ => cfg.nat = .machine → c ∉ [``Nat.zero, ``Nat.succ, ``Int.ofNat, ``Int.negSucc,
      ``Nat.casesOn, ``Int.casesOn]
  | .app f a => NatPlain cfg f ∧ NatPlain cfg a
  | .lam _ t b _ | .forallE _ t b _ => NatPlain cfg t ∧ NatPlain cfg b
  | .letE _ t v b _ => NatPlain cfg t ∧ NatPlain cfg v ∧ NatPlain cfg b
  | .mdata _ e | .proj _ _ e => NatPlain cfg e
  | _ => True

/-- `NatPlain` survives opening a binder with a free variable. -/
theorem NatPlain.inst_fvar {cfg : ErasureConfig} {x : FVarId} :
    ∀ {b : Expr} {d : Nat}, NatPlain cfg b → NatPlain cfg (b.instantiate1' (.fvar x) d) := by
  intro b
  induction b with
  | bvar i =>
    intro d _
    simp only [Expr.instantiate1']
    split
    · trivial
    · split <;> trivial
  | _ => intro d h; simp_all [Expr.instantiate1', NatPlain]

/-! ## The renaming of the traversal's fresh variables -/

/-- The free variable that the pure backend's `freshFVarId` allocates at the counter value `k`.
Copy of `ML-V Core/Steps.lean:740`. Reference: none (DV-13). -/
abbrev pureFVar (k : Nat) : FVarId := ⟨.num `_pure k⟩

/-- `ρ` with `x` sent to `x'`. Reference: none. -/
def renExt (ρ : FVarId → FVarId) (x x' : FVarId) : FVarId → FVarId :=
  fun y => if y == x then x' else ρ y

theorem renExt_self (ρ : FVarId → FVarId) (x x' : FVarId) : renExt ρ x x' x = x' := by
  simp [renExt, (fvarId_beq_iff x x).2 rfl]

theorem renExt_ne {ρ : FVarId → FVarId} {x x' y : FVarId} (h : y ≠ x) : renExt ρ x x' y = ρ y := by
  simp [renExt, Bool.eq_false_iff.mpr fun e => h ((fvarId_beq_iff _ _).1 e)]

/-- Renamings that agree on the free variables of a term agree on the term. -/
theorem renFV_congr {p : FVarId → Prop} {ρ ρ' : FVarId → FVarId} (h : ∀ y, p y → ρ y = ρ' y) :
    ∀ {e : Expr}, FVarsIn p e → renFV ρ e = renFV ρ' e
  | .fvar y, hy => by rw [renFV, renFV, h y hy]
  | .app f a, he => by rw [renFV, renFV, renFV_congr h he.1, renFV_congr h he.2]
  | .lam _ t b _, he | .forallE _ t b _, he => by
    rw [renFV, renFV, renFV_congr h he.1, renFV_congr h he.2]
  | .letE _ t v b _, he => by
    rw [renFV, renFV, renFV_congr h he.1, renFV_congr h he.2.1, renFV_congr h he.2.2]
  | .mdata _ e, he | .proj _ _ e, he => by rw [renFV, renFV, renFV_congr h (e := e) he]
  | .bvar _, _ | .sort _, _ | .const .., _ | .lit _, _ | .mvar _, _ => rfl

/-- Closing the marking's binder `x` and renaming is closing the renamed binder `x'` after
renaming `x` to `x'`, when no other variable of the term is renamed to `x'`. -/
theorem absFV_renExt {S : FVarId → Prop} {ρ : FVarId → FVarId} {x x' : FVarId}
    (hx : ∀ y, S y → ρ y ≠ x') :
    ∀ {e : Expr} {d : Nat}, FVarsIn (fun y => S y ∨ y = x) e →
      absFV x' d (renFV (renExt ρ x x') e) = renFV ρ (absFV x d e) := by
  intro e
  induction e with
  | fvar y =>
    intro d hy
    by_cases hyx : y = x
    · subst hyx
      simp [renFV, renExt_self, absFV, (fvarId_beq_iff x' x').2 rfl, (fvarId_beq_iff y y).2 rfl]
    · have hρ : ρ y ≠ x' := hx y (hy.resolve_right hyx)
      have h1 : (ρ y == x') = false := Bool.eq_false_iff.mpr fun h => hρ ((fvarId_beq_iff _ _).1 h)
      have h2 : (y == x) = false := Bool.eq_false_iff.mpr fun h => hyx ((fvarId_beq_iff _ _).1 h)
      simp [renFV, renExt_ne hyx, absFV, h1, h2]
  | bvar i => intro d _; simp only [renFV, absFV]
  | _ => intro d h; simp_all [renFV, absFV, FVarsIn]

/-- The marking's locals `ls` and the traversal's locals `ls'`, on the scope `S` of the visited
term: `S` is closed under `ls` (`LocalsSupport`) and consists of variables of `ls`, `ρ` renames `ls`
into `ls'` on `S` (`LocalsRen`), and no variable of `S` is renamed to a variable that the counter
allocates from `k` on. Reference: none (DV-13). -/
structure RenOK (ρ : FVarId → FVarId) (S : FVarId → Prop) (ls ls' : List Local) (k : Nat) :
    Prop where
  supp : LocalsSupport S ls
  ren : LocalsRen ρ S ls ls'
  dom : ∀ y, S y → (Pure.findLocal ls y).isSome
  fresh : ∀ y, S y → ∀ k', k ≤ k' → ρ y ≠ pureFVar k'

theorem pureFVar_inj {k k' : Nat} (h : pureFVar k = pureFVar k') : k = k' := by
  cases h; rfl

/-- The counter's later values keep `RenOK`. -/
theorem RenOK.mono {ρ : FVarId → FVarId} {S : FVarId → Prop} {ls ls' : List Local} {k k₁ : Nat}
    (h : RenOK ρ S ls ls' k) (hk : k ≤ k₁) : RenOK ρ S ls ls' k₁ :=
  ⟨h.supp, h.ren, h.dom, fun y hy k' hk' => h.fresh y hy k' (Nat.le_trans hk hk')⟩

/-- A variable fresh for the locals is not in the scope. -/
theorem RenOK.not_mem {ρ : FVarId → FVarId} {S : FVarId → Prop} {ls ls' : List Local} {k : Nat}
    {x : FVarId} {es : List Expr} (h : RenOK ρ S ls ls' k) (hx : Fresh x ls es) : ¬ S x := by
  intro hS
  obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 (h.dom x hS)
  have hl' : ls.find? (·.fvarId == x) = some l := hl
  have hm := List.mem_of_find?_eq_some hl'
  have hp := List.find?_some hl'
  have hlx := (fvarId_beq_iff _ _).1 hp
  exact (hx.1 l hm).1 hlx

/-- Opening the marking's binder with a fresh `x` and the traversal's binder with the next
variable of the counter keeps `RenOK`, with `x` renamed to that variable and the counter
advanced. -/
theorem RenOK.push {ρ : FVarId → FVarId} {S : FVarId → Prop} {ls ls' : List Local} {k : Nat}
    {x : FVarId} {es : List Expr} {n : Name} {T : Expr} {val : Option Expr}
    (h : RenOK ρ S ls ls' k) (hx : Fresh x ls es) (hT : FVarsIn S T)
    (hv : ∀ v, val = some v → FVarsIn S v) :
    RenOK (renExt ρ x (pureFVar k)) (fun y => S y ∨ y = x) (⟨x, n, T, val⟩ :: ls)
      (⟨pureFVar k, n, renFV ρ T, val.map (renFV ρ)⟩ :: ls') (k + 1) := by
  have hxS := h.not_mem hx
  have hagree : ∀ y, S y → renExt ρ x (pureFVar k) y = ρ y := fun y hy =>
    renExt_ne fun e => hxS (e ▸ hy)
  have hrl : ∀ {l : Local}, FVarsIn S l.type → (∀ v, l.value? = some v → FVarsIn S v) →
      S l.fvarId → renLocal (renExt ρ x (pureFVar k)) l = renLocal ρ l := by
    intro l hlt hlv hly
    obtain ⟨y, nm, t, v⟩ := l
    simp only [renLocal, hagree y hly, renFV_congr hagree hlt]
    congr 1
    cases v with
    | none => rfl
    | some v => simp only [Option.map_some, renFV_congr hagree (hlv v rfl)]
  have hself : ∀ z : FVarId, (z == z) = true := fun z => (fvarId_beq_iff z z).2 rfl
  refine ⟨localsSupport_open h.supp hT hv, fun y hy => ?_, fun y hy => ?_, fun y hy k' hk' => ?_⟩
  · rcases hy with hy | rfl
    · have hyx : y ≠ x := fun e => hxS (e ▸ hy)
      have hne : (pureFVar k == ρ y) = false := Bool.eq_false_iff.mpr fun e =>
        h.fresh y hy k (Nat.le_refl _) ((fvarId_beq_iff _ _).1 e).symm
      have hne' : (x == y) = false := Bool.eq_false_iff.mpr fun e =>
        hyx ((fvarId_beq_iff _ _).1 e).symm
      simp only [Pure.findLocal, List.find?_cons, hagree y hy, hne, hne']
      rw [← Pure.findLocal, ← Pure.findLocal, h.ren y hy]
      cases hl : Pure.findLocal ls y with
      | none => rfl
      | some l =>
        have hp := List.find?_some (show ls.find? (·.fvarId == y) = some l from hl)
        have hly : l.fvarId = y := (fvarId_beq_iff _ _).1 hp
        have ⟨hlt, hlv⟩ := h.supp y hy l hl
        simp only [Option.map_some, hrl hlt hlv (hly ▸ hy)]
    · simp only [Pure.findLocal, List.find?_cons, renExt_self, hself, Option.map_some,
        renLocal, renFV_congr hagree hT]
      congr 2
      cases val with
      | none => rfl
      | some v => simp only [Option.map_some, renFV_congr hagree (hv v rfl)]
  · rcases hy with hy | rfl
    · have hne' : (x == y) = false := Bool.eq_false_iff.mpr fun e =>
        hxS (((fvarId_beq_iff _ _).1 e) ▸ hy)
      simp only [Pure.findLocal, List.find?_cons, hne']
      exact h.dom y hy
    · simp [Pure.findLocal, hself]
  · rcases hy with hy | rfl
    · rw [hagree y hy]
      exact h.fresh y hy k' (Nat.le_of_succ_le hk')
    · rw [renExt_self]
      intro e
      have := pureFVar_inj e
      omega

/-! ## The invariants and the statement at one fuel -/

/-- The traversal's context invariant at the pure backend: the configuration is `cfg`, and no fix
variable is bound (`visitMutual` erases a value with `fixvars := none`). Adapted from
`ML-V Core/Steps.lean:825 CtxOK`, without the typing of the locals. Reference: the context of
`erases_erase` (`MR E/ErasureFunction.v:1228`); DV-7. -/
structure CtxOK (cfg : ErasureConfig) (tc : TravCtx) : Prop where
  config : tc.config = cfg
  fixvars : tc.fixvars = none

/-- What a run of the traversal from the states `st`, `ps` to `st'`, `ps'` guarantees: the state
invariant holds after it (`StateOK`), the λ□ environment grows by fresh kernames (`LenvExt`), the
counter does not decrease, and every constant it registers is in the scope `Sc`. Copy of
`ML-V Core/Steps.lean:853` at `noCert`. Reference: `includes_deps`
(`MR E/ErasureFunctionProperties.v:41`), the invariant of `erase_global_deps`
(`MR E/ErasureFunction.v:1602`), and `erase_global_deps_fresh`
(`MR E/ErasureFunctionProperties.v:1206`). -/
structure Grows (σ : EvalEnv) (Sc : Name → Prop) (st st' : ErasureState) (ps ps' : PureState) :
    Prop where
  inv : StateOK noCert σ st'
  ext : LenvExt st.gdecls st'.gdecls
  next : ps.next ≤ ps'.next
  scope : ∀ c kn, st.constants[c]? = none → st'.constants[c]? = some kn → Sc c

/-- A scope of the traversal: a set of constants declared in `decls`, closed under the constants
that occur (`nameOccurs`, the positions the traversal erases) in the values that `visitMutual`
erases (of declarations that are neither theorems, which the oracle boxes, nor recognized `casesOn`
constants, which `visitCases` erases). Adapted from `ML-V Core/Steps.lean:867`, without compiled
pre-definitions (DV-35). Reference: the dependencies `term_global_deps` (`MR E/EAstUtils.v:406`)
that `erase_global_deps` (`MR E/ErasureFunction.v:1602`) follows, transitively. -/
def ScopeOK (decls : List ConstantInfo) (Sc : Name → Prop) : Prop :=
  ∀ c, Sc c → ∃ ci, findDecl decls c = some ci ∧
    ∀ v, ci.value? (allowOpaque := true) = some v → IsThm ci = false → casesInfo? decls c = none →
      ∀ d, nameOccurs d v = true → Sc d

/-- The correctness of `visitExpr fuel` at the pure backend over the closure `decls`, on a term `e`
with a marking `ê` under the locals `ls`: run on `e` renamed by `ρ`, under traversal locals that
`ρ` relates to `ls` on the scope `S` of `e` (`RenOK`), from a state with `StateOK`, on a term whose
constants occur in a scope `Sc`, `NatPlain` and reading recursors only in the fragment's shape
(`RecShaped`), a successful run returns a closed erasure of the renamed marking whose λ□
dependencies are erased in the final environment, and it `Grows` within `Sc`. Adapted from
`ML-V Core/Steps.lean:882`, with the marking in place of the typed translation. Reference:
`erases_erase` (`MR E/ErasureFunction.v:1228`) with `erase_global_erases_deps`
(`MR E/ErasureFunctionProperties.v:172`). -/
def ExprSpec (view : EnvView) (cfg : ErasureConfig) (decls : List ConstantInfo) (fuel : Nat)
    (e : Expr) : Prop :=
  ∀ ⦃ρ : FVarId → FVarId⦄ ⦃S : FVarId → Prop⦄ ⦃ls : List Local⦄ ⦃Sc : Name → Prop⦄ ⦃ê : Expr⦄
    ⦃st : ErasureState⦄ ⦃tc : TravCtx⦄ ⦃ps : PureState⦄ ⦃r : LBTerm⦄ ⦃st' : ErasureState⦄
    ⦃ps' : PureState⦄,
    CtxOK cfg tc → RenOK ρ S ls tc.locals ps.next → FVarsIn S e → ScopeOK decls Sc →
    (∀ d, nameOccurs d e = true → Sc d) → NatPlain cfg e → RecShaped cfg decls e →
    StateOK noCert (evalEnvOf view cfg decls) st → MarkOf decls cfg ls e ê →
    (visitExpr (m := PureM) fuel (renFV ρ e)).runPure st tc ⟨decls, view⟩ ps = .ok ((r, st'), ps') →
    Erases noCert (evalEnvOf view cfg decls) [] (renFV ρ ê) r ∧ closedn 0 r = true ∧
      ErasesDeps noCert (evalEnvOf view cfg decls) st'.gdecls r ∧
      Grows (evalEnvOf view cfg decls) Sc st st' ps ps'

section
variable {σ : EvalEnv} {Sc : Name → Prop}

/-- Copy of `ML-V Core/Steps.lean:926`. -/
theorem LenvExt.refl {lenv : GlobalDeclarations} : LenvExt lenv lenv :=
  ⟨[], rfl, fun _ h => nomatch h⟩

/-- Copy of `ML-V Core/Steps.lean:929`. -/
theorem LenvExt.trans {l₁ l₂ l₃ : GlobalDeclarations} (h₁ : LenvExt l₁ l₂) (h₂ : LenvExt l₂ l₃) :
    LenvExt l₁ l₃ := by
  obtain ⟨n₁, rfl, f₁⟩ := h₁
  obtain ⟨n₂, rfl, f₂⟩ := h₂
  refine ⟨n₂ ++ n₁, by simp, fun kn hkn => ?_⟩
  rw [List.map_append, List.mem_append] at hkn
  rcases hkn with hkn | hkn
  · have := f₂ kn hkn
    rw [List.find?_append, Option.or_eq_none_iff] at this
    exact this.2
  · exact f₁ kn hkn

/-- A run that changes neither state grows. Copy of `ML-V Core/Steps.lean:942`. -/
theorem Grows.refl {st : ErasureState} {ps : PureState} (hok : StateOK noCert σ st) :
    Grows σ Sc st st ps ps :=
  ⟨hok, LenvExt.refl, Nat.le_refl _, fun _ _ h h' => by rw [h] at h'; cases h'⟩

/-- Consecutive runs grow. Copy of `ML-V Core/Steps.lean:947`. -/
theorem Grows.trans {st st₁ st₂ : ErasureState} {ps ps₁ ps₂ : PureState}
    (h₁ : Grows σ Sc st st₁ ps ps₁) (h₂ : Grows σ Sc st₁ st₂ ps₁ ps₂) :
    Grows σ Sc st st₂ ps ps₂ := by
  refine ⟨h₂.inv, LenvExt.trans h₁.ext h₂.ext, Nat.le_trans h₁.next h₂.next, fun c kn h h' => ?_⟩
  cases h1 : st₁.constants[c]? with
  | none => exact h₂.scope c kn h1 h'
  | some kn₁ => exact h₁.scope c kn₁ h h1

end

/-! ## Inversions of the marking -/

section
variable {decls : List ConstantInfo} {cfg : ErasureConfig} {ls : List Local}

/-- An application spine with arguments is no term whose head is not an application. -/
theorem ne_mkAppN {e f : Expr} {as : List Expr} (he : e.isApp = false) (has : as ≠ []) :
    e ≠ mkAppN f as.toArray := by
  rcases eq_nil_or_snoc as with rfl | ⟨as', a, rfl⟩
  · exact absurd rfl has
  · rw [mkAppN_snoc]
    intro h
    rw [h] at he
    cases he

/-- A constant spine is no term whose head is itself and not a constant. -/
theorem ne_mkAppN_const {e : Expr} {c : Name} {us : List Level} {as : List Expr}
    (he : e.getAppFn = e) (hc : ∀ c us, e ≠ .const c us) : e ≠ mkAppN (.const c us) as.toArray :=
  fun h => hc c us (he.symm.trans ((congrArg Expr.getAppFn h).trans (getAppFn_mkAppN_const c us as)))

/-- The oracle's answers on the marking's term and on the renamed term agree. -/
theorem oracle_agree {ρ : FVarId → FVarId} {S : FVarId → Prop} {ls' : List Local} {k : Nat}
    {e : Expr} {b : Bool} (hcl : ClosedDecls decls = true) (hR : RenOK ρ S ls ls' k)
    (he : FVarsIn S e) (h : Pure.isErasable ⟨decls⟩ oracleFuel ls' (renFV ρ e) = .ok b) :
    oracle decls ls e = .ok b :=
  (Pure.isErasable_ren hcl hR.supp hR.ren _ e he).symm.trans h

/-- Where the oracle answers `true` the marking is the `erase` mark. -/
theorem MarkOf.erase_of_true {e ê : Expr} (h : MarkOf decls cfg ls e ê)
    (hor : oracle decls ls e = .ok true) : ê = markErase e := by
  cases h with
  | erase => rfl
  | fvar h₁ | mdata h₁ _ | lam h₁ _ _ | letE h₁ _ _ _ | proj h₁ _ _ | litZero h₁ _
  | litSucc h₁ _ _ _ | app h₁ _ _ _ _ _ _ | constApp h₁ _ _ _ | special h₁ _ _ _ =>
    rw [h₁] at hor; cases hor

/-- A marking of a free variable that the oracle keeps is the variable. -/
theorem MarkOf.fvar_inv {x : FVarId} {ê : Expr} (h : MarkOf decls cfg ls (.fvar x) ê)
    (hf : oracle decls ls (.fvar x) = .ok false) : ê = .fvar x := by
  generalize hx : Expr.fvar x = e at h hf
  cases h with
  | erase h₁ => rw [h₁] at hf; cases hf
  | fvar => cases hx; rfl
  | app _ hne => exact absurd hx (ne_mkAppN rfl hne)
  | constApp | special => exact absurd hx (ne_mkAppN_const rfl nofun)
  | _ => cases hx

/-- A marking of metadata that the oracle keeps is a marking of the term under it. -/
theorem MarkOf.mdata_inv {m : MData} {e ê : Expr} (h : MarkOf decls cfg ls (.mdata m e) ê)
    (hf : oracle decls ls (.mdata m e) = .ok false) : MarkOf decls cfg ls e ê := by
  generalize hx : Expr.mdata m e = e' at h hf
  cases h with
  | erase h₁ => rw [h₁] at hf; cases hf
  | mdata _ h₂ => cases hx; exact h₂
  | app _ hne => exact absurd hx (ne_mkAppN rfl hne)
  | constApp | special => exact absurd hx (ne_mkAppN_const rfl nofun)
  | _ => cases hx

/-- A marking of a λ that the oracle keeps marks the body opened with a fresh variable. -/
theorem MarkOf.lam_inv {n : Name} {A b ê : Expr} {bi : BinderInfo}
    (h : MarkOf decls cfg ls (.lam n A b bi) ê) (hf : oracle decls ls (.lam n A b bi) = .ok false) :
    ∃ x bM, Fresh x ls [b] ∧ MarkOf decls cfg (⟨x, n, A, none⟩ :: ls) (b.instantiate1' (.fvar x)) bM ∧
      ê = .lam n A (absFV x 0 bM) bi := by
  generalize hx : Expr.lam n A b bi = e at h hf
  cases h with
  | erase h₁ => rw [h₁] at hf; cases hf
  | lam _ h₂ h₃ => cases hx; exact ⟨_, _, h₂, h₃, rfl⟩
  | app _ hne => exact absurd hx (ne_mkAppN rfl hne)
  | constApp | special => exact absurd hx (ne_mkAppN_const rfl nofun)
  | _ => cases hx

/-- A marking of a `let` that the oracle keeps marks the value and the body opened with a fresh
variable, both under the `let`'s local. -/
theorem MarkOf.letE_inv {n : Name} {T v b ê : Expr} {nd : Bool}
    (h : MarkOf decls cfg ls (.letE n T v b nd) ê)
    (hf : oracle decls ls (.letE n T v b nd) = .ok false) :
    ∃ x vM bM, Fresh x ls [v, b] ∧ MarkOf decls cfg (⟨x, n, T, some v⟩ :: ls) v vM ∧
      MarkOf decls cfg (⟨x, n, T, some v⟩ :: ls) (b.instantiate1' (.fvar x)) bM ∧
      ê = .letE n T vM (absFV x 0 bM) nd := by
  generalize hx : Expr.letE n T v b nd = e at h hf
  cases h with
  | erase h₁ => rw [h₁] at hf; cases hf
  | letE _ h₂ h₃ h₄ => cases hx; exact ⟨_, _, _, h₂, h₃, h₄, rfl⟩
  | app _ hne => exact absurd hx (ne_mkAppN rfl hne)
  | constApp | special => exact absurd hx (ne_mkAppN_const rfl nofun)
  | _ => cases hx

end

/-! ## Runs of the traversal's helpers (copies of `ML-V Core/Steps.lean:743-1103`) -/

section
variable {pc : PureCtx}

/-- `Except`'s bind on a success. -/
theorem ok_bind' {ε α β : Type} {a : α} {f : α → Except ε β} :
    ((Except.ok a : Except ε α) >>= f) = f a := rfl

/-- The pure backend's `freshFVarId` returns `pureFVar` of the counter and increments it. -/
theorem fresh_run {tc : TravCtx} {st : ErasureState} {ps : PureState} :
    (liftM (Backend.freshFVarId (m := PureM)) : EraseT PureM FVarId).runPure st tc pc ps =
      .ok ((pureFVar ps.next, st), ⟨ps.next + 1⟩) := rfl

theorem runPure_withReader {α : Type} {tc : TravCtx} {st : ErasureState} {ps : PureState}
    (f : TravCtx → TravCtx) (x : EraseT PureM α) :
    (withReader f x).runPure st tc pc ps = x.runPure st (f tc) pc ps := rfl

/-- The pure oracle as the backend runs it. Copy of `ML-V Core/Frame.lean:350`. -/
theorem isErasable_run (lctx : LocalContext) (ls : List Local) (e : Expr) (ps : PureState) :
    ((Backend.isErasable (m := PureM) lctx ls e).run pc).run ps =
      (Pure.isErasable ⟨pc.decls⟩ oracleFuel ls e).map (·, ps) := by
  change (((match Pure.isErasable ⟨pc.decls⟩ oracleFuel ls e with
    | .ok t => (Pure.pure t : PureM Bool) | .error err => throw err).run pc).run ps) = _
  cases Pure.isErasable ⟨pc.decls⟩ oracleFuel ls e <;> rfl

/-- A successful run of the oracle call that starts each unfolding of `Erasure.visitExpr` either
answered `true` and returned `□` without changing the states, or answered `false` and ran the
branch `K`. Reference: `is_erasableb` at the start of `erase` (`MR E/ErasureFunction.v:992`). -/
theorem oracle_run {e : Expr} {K : EraseT PureM LBTerm} {tc : TravCtx} {st st' : ErasureState}
    {ps ps' : PureState} {r : LBTerm}
    (h : (read >>= fun c₁ => read >>= fun c₂ =>
        (liftM (Backend.isErasable (m := PureM) c₁.lctx c₂.locals e) : EraseT PureM Bool) >>=
          fun b => if b = true then Pure.pure LBTerm.box else K).runPure st tc pc ps =
      .ok ((r, st'), ps')) :
    (Pure.isErasable ⟨pc.decls⟩ oracleFuel tc.locals e = .ok true ∧ r = .box ∧ st' = st ∧
      ps' = ps) ∨
    (Pure.isErasable ⟨pc.decls⟩ oracleFuel tc.locals e = .ok false ∧
      K.runPure st tc pc ps = .ok ((r, st'), ps')) := by
  rw [runPure_read_bind, runPure_read_bind, runPure_bind, runPure_liftM, isErasable_run] at h
  cases hor : Pure.isErasable ⟨pc.decls⟩ oracleFuel tc.locals e with
  | error err => rw [hor] at h; cases h
  | «ok» b =>
    rw [hor] at h
    cases b with
    | true => cases h; exact .inl ⟨rfl, rfl, rfl, rfl⟩
    | false => exact .inr ⟨rfl, h⟩

/-- `fvar_to_name x` is the λ□ name of the local found for `x`. -/
theorem fvar_to_name_run {tc : TravCtx} {st : ErasureState} {ps : PureState} {x : FVarId}
    {l : Local} (hf : tc.locals.find? (·.fvarId == x) = some l) :
    (fvar_to_name (m := PureM) x).runPure st tc pc ps =
      .ok ((binderNameOf l.userName, st), ps) := by
  unfold fvar_to_name
  have hr : (read : EraseT PureM TravCtx).runPure st tc pc ps = .ok ((tc, st), ps) := rfl
  rw [runPure_bind, hr, ok_bind']
  dsimp only
  simp only [getOrFail, hf]
  rfl

/-- `mkLambda x body` closes `body` over `x` with the traversal's `abstract`, under the λ□ name of
the local found for `x`. Reference: the `tLambda` case of `erase` (`MR E/ErasureFunction.v:1003`);
DV-13. -/
theorem mkLambda_run {tc : TravCtx} {st : ErasureState} {ps : PureState} {x : FVarId} {l : Local}
    {ls : List Local} {body : LBTerm} (hl : tc.locals = l :: ls) (hx : l.fvarId = x) :
    (Erasure.mkLambda (m := PureM) x body).runPure st tc pc ps =
      .ok ((.lambda (binderNameOf l.userName) (_root_.abstract x body), st), ps) := by
  have hf : tc.locals.find? (·.fvarId == x) = some l := by
    rw [hl, List.find?_cons, hx, (fvarId_beq_iff x x).mpr rfl]
  unfold Erasure.mkLambda
  rw [runPure_bind, fvar_to_name_run hf]
  rfl

/-- `mkLetIn x val body` closes `body` over `x` with the traversal's `abstract`, under the λ□ name
of the local found for `x`. Reference: the `tLetIn` case of `erase`
(`MR E/ErasureFunction.v:1005`); DV-13. -/
theorem mkLetIn_run {tc : TravCtx} {st : ErasureState} {ps : PureState} {x : FVarId} {l : Local}
    {ls : List Local} {val body : LBTerm} (hl : tc.locals = l :: ls) (hx : l.fvarId = x) :
    (mkLetIn (m := PureM) x val body).runPure st tc pc ps =
      .ok ((.letIn (binderNameOf l.userName) val (_root_.abstract x body), st), ps) := by
  have hf : tc.locals.find? (·.fvarId == x) = some l := by
    rw [hl, List.find?_cons, hx, (fvarId_beq_iff x x).mpr rfl]
  unfold Erasure.mkLetIn
  rw [runPure_bind, fvar_to_name_run hf]
  rfl

end

/-! ## The steps of `visitExpr` without applications, constants, projections and literals -/

section
variable {decls : List ConstantInfo} {view : EnvView} {cfg : ErasureConfig}

/-- The `box` step, shared by every case of `visitExpr`: where the oracle answers `true` on the
renamed term under the traversal's locals, it answers `true` on the term under the marking's
locals (`Pure.isErasable_ren`), so the marking is the `erase` mark (`MarkOf.erase_of_true`), which
`□` erases (`Erases.box` at `noCert`). Reference: the `is_erasableb` case of `erases_erase`
(`MR E/ErasureFunction.v:1228`), rule `erases_box` (`MR E/Extract.v:140`); justified by the mark,
not by the oracle's soundness (DV-32). -/
theorem visitExpr_box {ρ : FVarId → FVarId} {S : FVarId → Prop} {ls : List Local}
    {Sc : Name → Prop} {tc : TravCtx} {ps : PureState} {st : ErasureState} {e ê : Expr}
    (hcl : ClosedDecls decls = true) (hR : RenOK ρ S ls tc.locals ps.next) (he : FVarsIn S e)
    (hok : StateOK noCert (evalEnvOf view cfg decls) st) (hm : MarkOf decls cfg ls e ê)
    (hor : Pure.isErasable ⟨decls⟩ oracleFuel tc.locals (renFV ρ e) = .ok true) :
    Erases noCert (evalEnvOf view cfg decls) [] (renFV ρ ê) .box ∧ closedn 0 .box = true ∧
      ErasesDeps noCert (evalEnvOf view cfg decls) st.gdecls .box ∧
      Grows (evalEnvOf view cfg decls) Sc st st ps ps := by
  rw [MarkOf.erase_of_true hm (oracle_agree hcl hR he hor)]
  exact ⟨.box trivial, rfl, .box, .refl hok⟩

/-- The `fvar` step: a free variable the oracle keeps erases to its renamed self. Reference: the
`tVar` case of `erases_erase` (`MR E/ErasureFunction.v:1228`), rule `erases_tVar`
(`MR E/Extract.v:90`); DV-13. -/
theorem visitExpr_fvar_step (hcl : ClosedDecls decls = true) {fuel : Nat} {x : FVarId} :
    ExprSpec view cfg decls (fuel + 1) (.fvar x) := by
  intro ρ S ls Sc ê st tc ps r st' ps' _ hR he _ _ _ _ hok hm hrun
  simp only [renFV] at hrun
  rw [visitExpr] at hrun
  rcases oracle_run hrun with ⟨hor, rfl, rfl, rfl⟩ | ⟨hor, hrun⟩
  · exact visitExpr_box hcl hR he hok hm hor
  rw [MarkOf.fvar_inv hm (oracle_agree (e := .fvar x) hcl hR he hor)]
  cases hrun
  exact ⟨.fvar, rfl, .fvar, .refl hok⟩

/-- The steps on the terms `visitExpr` rejects after the oracle (a bound variable, a sort, a Π, a
metavariable): only the oracle's `□` returns. Reference: the `tSort` and `tProd` cases of `erase`
(`MR E/ErasureFunction.v:998`, `:1002`), unreachable after `is_erasableb`. -/
theorem visitExpr_fail_step (hcl : ClosedDecls decls = true) {fuel : Nat} {e : Expr}
    (hk : (e.isBVar || e.isSort || e.isForall || e.isMVar) = true) :
    ExprSpec view cfg decls (fuel + 1) e := by
  intro ρ S ls Sc ê st tc ps r st' ps' _ hR he _ _ _ _ hok hm hrun
  cases e <;> simp [Expr.isBVar, Expr.isSort, Expr.isForall, Expr.isMVar] at hk <;>
  · simp only [renFV] at hrun
    rw [visitExpr] at hrun
    rcases oracle_run hrun with ⟨hor, rfl, rfl, rfl⟩ | ⟨-, hrun⟩
    · exact visitExpr_box hcl hR he hok hm hor
    · cases hrun

/-- The `mdata` step, from `visitExpr` at `fuel`: metadata is transparent. Reference: none (PCUIC
has no metadata). -/
theorem visitExpr_mdata_step (hcl : ClosedDecls decls = true) {fuel : Nat}
    (ih : ∀ e, ExprSpec view cfg decls fuel e) {m : MData} {e : Expr} :
    ExprSpec view cfg decls (fuel + 1) (.mdata m e) := by
  intro ρ S ls Sc ê st tc ps r st' ps' hctx hR he hsc hocc hnp hrs hok hm hrun
  simp only [renFV] at hrun
  rw [visitExpr] at hrun
  rcases oracle_run hrun with ⟨hor, rfl, rfl, rfl⟩ | ⟨hor, hrun⟩
  · exact visitExpr_box hcl hR he hok hm hor
  exact ih e hctx hR he hsc hocc hnp hrs hok
    (MarkOf.mdata_inv hm (oracle_agree (e := .mdata m e) hcl hR he hor)) hrun

/-- The `lam` step, from `visitExpr` at the fuels up to `fuel`: the body is opened with the next
variable of the counter, to which the marking's fresh variable is renamed (`RenOK.push`), erased,
and closed again by the traversal's `abstract` (`Erases.abstract`, `absFV_renExt`). Reference: the
`tLambda` case of `erases_erase` (`MR E/ErasureFunction.v:1228`), rule `erases_tLambda`
(`MR E/Extract.v:93`); DV-13. -/
theorem visitExpr_lam_step (hcl : ClosedDecls decls = true) {fuel : Nat}
    (ih : ∀ m ≤ fuel, ∀ e, ExprSpec view cfg decls m e) {n : Name} {A b : Expr}
    {bi : BinderInfo} :
    ExprSpec view cfg decls (fuel + 1) (.lam n A b bi) := by
  intro ρ S ls Sc ê st tc ps r st' ps' hctx hR he hsc hocc hnp hrs hok hm hrun
  simp only [renFV] at hrun
  rw [visitExpr] at hrun
  rcases oracle_run hrun with ⟨hor, rfl, rfl, rfl⟩ | ⟨hor, hrun⟩
  · exact visitExpr_box hcl hR he hok hm hor
  obtain ⟨x, bM, hx, hbM, rfl⟩ := MarkOf.lam_inv hm (oracle_agree (e := .lam n A b bi) hcl hR he hor)
  cases fuel with
  | zero => rw [visitLambda] at hrun; cases hrun
  | succ k =>
  rw [visitLambda] at hrun
  simp only [lambdaMonocular, withLocalDecl] at hrun
  rw [runPure_bind, fresh_run, ok_bind'] at hrun
  dsimp only at hrun
  rw [runPure_withReader, runPure_bind] at hrun
  obtain ⟨⟨⟨r₀, st₁⟩, ps₁⟩, hbody, hrun⟩ := ok_of_bind hrun
  dsimp only at hrun
  rw [mkLambda_run (l := ⟨pureFVar ps.next, n, renFV ρ A, none⟩) rfl rfl] at hrun
  cases hrun
  have hR' := hR.push (n := n) (val := none) hx he.1 (fun _ h => nomatch h)
  have hb' := fvarsIn_open (x := x) he.2
  have hxb : FVarsIn (· ≠ x) b := hx.2 b (List.mem_singleton_self b)
  have hren : renFV (renExt ρ x (pureFVar ps.next)) (b.instantiate1' (.fvar x)) =
      (renFV ρ b).instantiate1' (.fvar (pureFVar ps.next)) := by
    rw [renFV_inst, renFV_congr (p := (· ≠ x)) (fun y hy => renExt_ne hy) hxb]
    simp only [renFV, renExt_self]
  rw [show Backend.instantiate1 (m := PureM) (renFV ρ b) (.fvar (pureFVar ps.next)) =
    renFV (renExt ρ x (pureFVar ps.next)) (b.instantiate1' (.fvar x)) from hren.symm] at hbody
  have ⟨her, hc0, hdeps, hgr⟩ := ih k (Nat.le_succ _) _ (by exact ⟨hctx.config, hctx.fixvars⟩)
    hR' hb' hsc (fun d hd => hocc d (by rw [nameOccurs_inst_fvar] at hd; exact hd))
    (NatPlain.inst_fvar hnp.2) (ConstsIn_inst_fvar hrs.2) hok hbM hbody
  have habs := absFV_renExt (d := 0) (fun y hy => hR.fresh y hy ps.next (Nat.le_refl _))
    (MarkOf.fvarsIn hcl hbM hR'.supp hb')
  refine ⟨.lam ?_, closedn_toBvar _ r₀ 0 hc0, .lambda (ErasesDeps.toBvar hdeps 0),
    ⟨hgr.inv, hgr.ext, Nat.le_trans (Nat.le_succ _) hgr.next, hgr.scope⟩⟩
  rw [← habs]
  exact Erases.abstract hc0 her

/-- The `letE` step, from `visitExpr` at the fuels up to `fuel`: the value and the body are visited
under the `let`'s local, opened with the next variable of the counter, to which the marking's
fresh variable is renamed (`RenOK.push`); the value does not mention it; the body is closed again
by the traversal's `abstract` (`Erases.abstract`, `absFV_renExt`). Reference: the `tLetIn` case of
`erases_erase` (`MR E/ErasureFunction.v:1228`), rule `erases_tLetIn` (`MR E/Extract.v:96`);
DV-13. -/
theorem visitExpr_letE_step (hcl : ClosedDecls decls = true) {fuel : Nat}
    (ih : ∀ m ≤ fuel, ∀ e, ExprSpec view cfg decls m e) {n : Name} {T v b : Expr} {nd : Bool} :
    ExprSpec view cfg decls (fuel + 1) (.letE n T v b nd) := by
  intro ρ S ls Sc ê st tc ps r st' ps' hctx hR he hsc hocc hnp hrs hok hm hrun
  simp only [renFV] at hrun
  rw [visitExpr] at hrun
  rcases oracle_run hrun with ⟨hor, rfl, rfl, rfl⟩ | ⟨hor, hrun⟩
  · exact visitExpr_box hcl hR he hok hm hor
  obtain ⟨x, vM, bM, hx, hvM, hbM, rfl⟩ :=
    MarkOf.letE_inv hm (oracle_agree (e := .letE n T v b nd) hcl hR he hor)
  cases fuel with
  | zero => rw [visitLet] at hrun; cases hrun
  | succ k =>
  rw [visitLet] at hrun
  simp only [letMonocular, withLocalDef] at hrun
  rw [runPure_bind, fresh_run, ok_bind'] at hrun
  dsimp only at hrun
  rw [runPure_withReader, runPure_bind] at hrun
  obtain ⟨⟨⟨tv, st₁⟩, ps₁⟩, hval, hrun⟩ := ok_of_bind hrun
  dsimp only at hrun
  rw [runPure_bind] at hrun
  obtain ⟨⟨⟨tb, st₂⟩, ps₂⟩, hbody, hrun⟩ := ok_of_bind hrun
  dsimp only at hrun
  rw [mkLetIn_run (l := ⟨pureFVar ps.next, n, renFV ρ T, some (renFV ρ v)⟩) rfl rfl] at hrun
  cases hrun
  have hR' := hR.push (n := n) (val := some v) hx he.1 (fun w h => by cases h; exact he.2.1)
  have hxS := hR.not_mem hx
  have hagree : ∀ y, S y → renExt ρ x (pureFVar ps.next) y = ρ y := fun y hy =>
    renExt_ne fun e => hxS (e ▸ hy)
  have hv' : FVarsIn (fun y => S y ∨ y = x) v := fvarsIn_mono (fun _ => .inl) he.2.1
  have hb' := fvarsIn_open (x := x) he.2.2
  have hxb : FVarsIn (· ≠ x) b := hx.2 b (by simp)
  have hrenv : renFV (renExt ρ x (pureFVar ps.next)) v = renFV ρ v := renFV_congr hagree he.2.1
  have hrenb : renFV (renExt ρ x (pureFVar ps.next)) (b.instantiate1' (.fvar x)) =
      (renFV ρ b).instantiate1' (.fvar (pureFVar ps.next)) := by
    rw [renFV_inst, renFV_congr (p := (· ≠ x)) (fun y hy => renExt_ne hy) hxb]
    simp only [renFV, renExt_self]
  rw [show visitExpr (m := PureM) k (renFV ρ v) =
    visitExpr k (renFV (renExt ρ x (pureFVar ps.next)) v) by rw [hrenv]] at hval
  rw [show Backend.instantiate1 (m := PureM) (renFV ρ b) (.fvar (pureFVar ps.next)) =
    renFV (renExt ρ x (pureFVar ps.next)) (b.instantiate1' (.fvar x)) from hrenb.symm] at hbody
  have ⟨herv, hcv, hdepsv, hgrv⟩ := ih k (Nat.le_succ _) _ (by exact ⟨hctx.config, hctx.fixvars⟩)
    hR' hv' hsc (fun d hd => hocc d (by simp [nameOccurs, hd])) hnp.2.1 hrs.2.1 hok hvM hval
  have ⟨herb, hcb, hdepsb, hgrb⟩ := ih k (Nat.le_succ _) _ (by exact ⟨hctx.config, hctx.fixvars⟩)
    (hR'.mono hgrv.next) hb' hsc
    (fun d hd => hocc d (by rw [nameOccurs_inst_fvar] at hd; simp [nameOccurs, hd]))
    (NatPlain.inst_fvar hnp.2.2) (ConstsIn_inst_fvar hrs.2.2) hgrv.inv hbM hbody
  -- the value's marking does not mention the `let`'s variable
  have hvS : FVarsIn S vM := MarkOf.fvarsIn hcl hvM
    (localsSupport_cons hR.supp he.1 (fun w h => by cases h; exact he.2.1) (fun _ h => h)
      fun _ h => .inr h) he.2.1
  have habs := absFV_renExt (d := 0) (fun y hy => hR.fresh y hy ps.next (Nat.le_refl _))
    (MarkOf.fvarsIn hcl hbM hR'.supp hb')
  refine ⟨.letE ?_ ?_, ?_, .letIn (ErasesDeps.ext hgrb.ext hdepsv) (ErasesDeps.toBvar hdepsb 0),
    Grows.trans ⟨hgrv.inv, hgrv.ext, Nat.le_trans (Nat.le_succ _) hgrv.next, hgrv.scope⟩ hgrb⟩
  · rw [← renFV_congr hagree hvS]; exact herv
  · rw [← habs]; exact Erases.abstract hcb herb
  · simp only [closedn, Bool.and_eq_true]
    exact ⟨hcv, closedn_toBvar _ tb 0 hcb⟩

end

end Steps

end EraseProof
