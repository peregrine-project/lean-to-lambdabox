import EraseProof.Source.Eval
import EraseProof.Env.Unfold

/-!
# Restricting evaluation to a dependency-closed sub-environment

The final theorem evaluates over the program `P`; the eraser's facts range over the closure
`decls ⊆ P` that `collectDeps` computes. `SrcEval.restrict` moves an evaluation over `P` to one over
`decls` when the evaluated term's constants lie in `decls` and `decls` is closed under the
dependencies of its members. Then every lookup that evaluation makes (`findDecl`,
`EvalEnv.unfold?`, `EvalEnv.isAtom`) gives the same answer in both environments, and every term
that evaluation reaches has its constants in `decls`. The evaluation environment of a program is `evalEnvOf`,
whose remapped constants are the shipping eraser's own `Erasure.axiomatized`. `DepClosed` and
`KernameInj` state two properties of the closure that `collectDeps` checks: it is closed under the
dependencies of its members, and its declarations have distinct kernames.
-/

open Lean Lean4Lean Erasure

namespace EraseProof

/-- Structural: every constant of `e` satisfies `p`. Reference: `term_global_deps`
(`MR E/EAstUtils.v:406`), source side. -/
def ConstsIn (p : Name → Prop) : Expr → Prop
  | .const c _ => p c
  | .app f a => ConstsIn p f ∧ ConstsIn p a
  | .lam _ t b _ | .forallE _ t b _ => ConstsIn p t ∧ ConstsIn p b
  | .letE _ t v b _ => ConstsIn p t ∧ ConstsIn p v ∧ ConstsIn p b
  | .mdata _ e | .proj _ _ e => ConstsIn p e
  | _ => True

/-- `decls` is closed under the dependencies of its members: types, values and block members.
Reference: the closure property of `MR E/ErasureFunction.v:1602 erase_global_deps`. -/
def DepClosed (decls : List ConstantInfo) : Prop :=
  ∀ ci ∈ decls, ConstsIn (fun c => (findDecl decls c).isSome) ci.type ∧
    (∀ v, ci.value? (allowOpaque := true) = some v →
      ConstsIn (fun c => (findDecl decls c).isSome) v) ∧
    ∀ n ∈ ci.all, (findDecl decls n).isSome

/-- Kernames of the program's constants are distinct (the collision check of `collectDeps`).
Reference: none; in `MR E/Extract.v:324 erases_deps_tConst` source and target share the same
`kn` (DV-14). -/
def KernameInj (decls : List ConstantInfo) : Prop :=
  ∀ c₁ c₂, (findDecl decls c₁).isSome → (findDecl decls c₂).isSome →
    toKername c₁ = toKername c₂ → c₁ = c₂

/-- The evaluation environment of `P` under the configuration's remapping. Reference: as
`EvalEnv` (DV-12). -/
def evalEnvOf (view : EnvView) (cfg : ErasureConfig) (P : List ConstantInfo) : EvalEnv :=
  ⟨P, axiomatized view cfg⟩

section
variable {p q : Name → Prop}

/-- `ConstsIn` is monotone in the predicate. Reference: none (a property of the structural
predicate `ConstsIn`). -/
theorem ConstsIn.mono (hpq : ∀ c, p c → q c) {e : Expr} (h : ConstsIn p e) : ConstsIn q e := by
  induction e with
  | const c => exact hpq c h
  | app _ _ ihf iha => exact ⟨ihf h.1, iha h.2⟩
  | lam _ _ _ _ iht ihb | forallE _ _ _ _ iht ihb => exact ⟨iht h.1, ihb h.2⟩
  | letE _ _ _ _ _ iht ihv ihb => exact ⟨iht h.1, ihv h.2.1, ihb h.2.2⟩
  | mdata _ _ ih | proj _ _ _ ih => exact ih h
  | bvar | fvar | mvar | sort | lit => trivial

/-- Lifting loose bound variables keeps the constants. Reference: none (a property of the
structural predicate `ConstsIn`). -/
theorem ConstsIn.liftLooseBVars' {e : Expr} (h : ConstsIn p e) :
    ConstsIn p (e.liftLooseBVars' s d) := by
  induction e generalizing s with
  | const c => exact h
  | app _ _ ihf iha => exact ⟨ihf h.1, iha h.2⟩
  | lam _ _ _ _ iht ihb | forallE _ _ _ _ iht ihb => exact ⟨iht h.1, ihb h.2⟩
  | letE _ _ _ _ _ iht ihv ihb => exact ⟨iht h.1, ihv h.2.1, ihb h.2.2⟩
  | mdata _ _ ih | proj _ _ _ ih => exact ih h
  | bvar | fvar | mvar | sort | lit => trivial

/-- Instantiating a bound variable with a term whose constants satisfy `p` keeps the constants
within `p`. Reference: none (a property of the structural predicate `ConstsIn`). -/
theorem ConstsIn.instantiate1' {e s : Expr} (he : ConstsIn p e) (hs : ConstsIn p s) :
    ConstsIn p (e.instantiate1' s d) := by
  induction e generalizing d with
  | bvar i =>
    simp only [Expr.instantiate1']
    split
    · trivial
    · split
      · exact hs.liftLooseBVars'
      · trivial
  | const c => exact he
  | app _ _ ihf iha => exact ⟨ihf he.1, iha he.2⟩
  | lam _ _ _ _ iht ihb | forallE _ _ _ _ iht ihb => exact ⟨iht he.1, ihb he.2⟩
  | letE _ _ _ _ _ iht ihv ihb => exact ⟨iht he.1, ihv he.2.1, ihb he.2.2⟩
  | mdata _ _ ih | proj _ _ _ ih => exact ih he
  | fvar | mvar | sort | lit => trivial

/-- Universe instantiation (`Erasure.Pure.instLevels`) keeps the constants. Reference: none (a
property of the structural predicate `ConstsIn`). -/
theorem ConstsIn.instLevels {e : Expr} (h : ConstsIn p e) :
    ConstsIn p (Pure.instLevels ps us e) := by
  induction e with
  | const c => exact h
  | app _ _ ihf iha => exact ⟨ihf h.1, iha h.2⟩
  | lam _ _ _ _ iht ihb | forallE _ _ _ _ iht ihb => exact ⟨iht h.1, ihb h.2⟩
  | letE _ _ _ _ _ iht ihv ihb => exact ⟨iht h.1, ihv h.2.1, ihb h.2.2⟩
  | mdata _ _ ih | proj _ _ _ ih => exact ih h
  | bvar | fvar | mvar | sort | lit => trivial

/-- The head constant of an application spine satisfies `p`. Reference: none (a property of the
structural predicate `ConstsIn`). -/
theorem ConstsIn.getAppFn {e : Expr} (h : ConstsIn p e) (hh : e.getAppFn = .const c us) :
    p c := by
  induction e with
  | const c' => cases hh; exact h
  | app f _ ihf _ => exact ihf h.1 hh
  | _ => cases hh

end

/-- `EvidentProp` reads the environment only at the constants of the type: two environments that
agree there give the same answer. Reference: none (DV-11). -/
theorem EvidentProp.congr {d₁ d₂ : List ConstantInfo} {e : Expr}
    (h : ConstsIn (fun c => findDecl d₁ c = findDecl d₂ c) e) :
    EvidentProp d₁ e = EvidentProp d₂ e := by
  induction e with
  | forallE _ _ _ _ _ ihb => simp only [EvidentProp]; exact ihb h.2
  | mdata _ _ ih => simp only [EvidentProp]; exact ih h
  | _ =>
    simp only [EvidentProp]
    split
    · next hh => rw [h.getAppFn hh]
    · rfl

section
variable {P decls : List ConstantInfo}

/-- The first declaration of a name in a sub-environment is the first one in the environment.
Reference: `lookup_env_extends_NoDup` (`MR common/theories/Environment.v:653`). -/
theorem SubEnv.findDecl_of_some (hsub : SubEnv decls P) (h : findDecl decls c = some ci) :
    findDecl P c = some ci := by
  have hmem := List.mem_of_find?_eq_some h
  have hname : ci.name = c := by simpa using List.find?_some h
  rw [← hname]
  exact hsub ci hmem

/-- On a name declared in a sub-environment, lookups in it and in the environment agree.
Reference: `lookup_env_extends_NoDup` (`MR common/theories/Environment.v:653`). -/
theorem SubEnv.findDecl_eq (hsub : SubEnv decls P) (hc : (findDecl decls c).isSome) :
    findDecl decls c = findDecl P c := by
  obtain ⟨ci, h⟩ := Option.isSome_iff_exists.mp hc
  rw [h, hsub.findDecl_of_some h]

/-- An unfolded constant's value is its declaration's value. Reference: `cst_body decl = Some body`
in `eval_delta` (`MR P/PCUICWcbvEval.v:247`). -/
theorem EvalEnv.unfold?_value? {σ : EvalEnv} (hu : σ.unfold? c = some (ci, b)) :
    ci.value? (allowOpaque := true) = some b := by
  unfold EvalEnv.unfold? at hu
  split at hu
  · split at hu
    · cases hu
    · cases hu; rfl
  · split at hu
    · cases hu
    · cases hu; rfl
  · cases hu

/-- The value of a constant that evaluation over a dependency-closed `decls` unfolds has its
constants in `decls`. Reference: the closure property of `MR E/ErasureFunction.v:1602
erase_global_deps` (bodies of the closure's constants). -/
theorem DepClosed.unfold? {view : EnvView} {cfg : ErasureConfig} (hcl : DepClosed decls)
    (hu : (evalEnvOf view cfg decls).unfold? c = some (ci, b)) :
    ConstsIn (fun c => (findDecl decls c).isSome) b :=
  (hcl ci (List.mem_of_find?_eq_some (EvalEnv.unfold?_some hu).1)).2.1 b
    (EvalEnv.unfold?_value? hu)

/-- On a name declared in a sub-environment, the δ rule's lookup gives the same answer over the
sub-environment and over the environment. Reference: the λ□ counterpart
`weakening_env_declared_constant` (`MR E/EExtends.v:10`), for the premise of `eval_delta`
(`MR P/PCUICWcbvEval.v:247`). -/
theorem evalEnvOf_unfold? {view : EnvView} {cfg : ErasureConfig} (hsub : SubEnv decls P)
    (hc : (findDecl decls c).isSome) :
    (evalEnvOf view cfg decls).unfold? c = (evalEnvOf view cfg P).unfold? c := by
  simp only [EvalEnv.unfold?, evalEnvOf]
  rw [hsub.findDecl_eq hc]
  rfl

/-- On a name declared in a dependency-closed sub-environment, the atom test gives the same answer
over the sub-environment and over the environment. Reference: none (DV-11). -/
theorem evalEnvOf_isAtom {view : EnvView} {cfg : ErasureConfig} (hsub : SubEnv decls P)
    (hcl : DepClosed decls) (hc : (findDecl decls c).isSome) :
    (evalEnvOf view cfg decls).isAtom c = (evalEnvOf view cfg P).isAtom c := by
  obtain ⟨ci, h⟩ := Option.isSome_iff_exists.mp hc
  have hty : ConstsIn (fun c => findDecl decls c = findDecl P c) ci.type :=
    (hcl ci (List.mem_of_find?_eq_some h)).1.mono fun _ => hsub.findDecl_eq
  simp only [EvalEnv.isAtom]
  rw [evalEnvOf_unfold? hsub hc]
  simp only [evalEnvOf]
  rw [h, hsub.findDecl_of_some h]
  dsimp only
  rw [EvidentProp.congr hty]

/-- On a term whose constants are declared in a sub-environment, the side condition of `appCong`
holds over the sub-environment exactly when it holds over the environment. Reference: the side
condition of `eval_app_cong` (`MR P/PCUICWcbvEval.v:311`), which reads only the term. -/
theorem evalEnvOf_blocksCong {view : EnvView} {cfg : ErasureConfig} (hsub : SubEnv decls P)
    (hf : ConstsIn (fun c => (findDecl decls c).isSome) f) :
    BlocksCong (evalEnvOf view cfg decls) f ↔ BlocksCong (evalEnvOf view cfg P) f := by
  cases f with
  | const c _ => simp only [BlocksCong]; rw [evalEnvOf_unfold? hsub hf]
  | _ => exact Iff.rfl

/-- Evaluation over `P` of a term whose constants lie in a dependency-closed sub-environment stays
in it. Reference: none on the PCUIC side (MetaRocq evaluates in `Σ` throughout); the λ□ analogue of
an environment change is `weakening_eval_env` (`MR E/EWcbvEval.v:1516`); DV-3. -/
theorem SrcEval.restrict {view : EnvView} {cfg : ErasureConfig} (hsub : SubEnv decls P)
    (hcl : DepClosed decls) (hc : ConstsIn (fun c => (findDecl decls c).isSome) e)
    (hev : SrcEval (evalEnvOf view cfg P) e v) :
    SrcEval (evalEnvOf view cfg decls) e v ∧ ConstsIn (fun c => (findDecl decls c).isSome) v := by
  induction hev with
  | beta _ _ _ ihf iha ihb =>
    obtain ⟨ef, _, hb⟩ := ihf hc.1
    obtain ⟨ea, ha⟩ := iha hc.2
    obtain ⟨eb, hv⟩ := ihb (hb.instantiate1' ha)
    exact ⟨.beta ef ea eb, hv⟩
  | zeta _ _ ihv ihb =>
    obtain ⟨ev, hv⟩ := ihv hc.2.1
    obtain ⟨eb, hr⟩ := ihb (hc.2.2.instantiate1' hv)
    exact ⟨.zeta ev eb, hr⟩
  | delta hu hr hl _ ih =>
    rw [← evalEnvOf_unfold? hsub hc] at hu
    obtain ⟨eb, hv⟩ := ih (hcl.unfold? hu).instLevels
    exact ⟨.delta hu hr hl eb, hv⟩
  | fixAtom hu hr hl =>
    rw [← evalEnvOf_unfold? hsub hc] at hu
    exact ⟨.fixAtom hu hr hl, hc⟩
  | fixApp _ hu hr _ _ ihf iha ihb =>
    obtain ⟨ef, hcf⟩ := ihf hc.1
    rw [← evalEnvOf_unfold? hsub hcf] at hu
    obtain ⟨ea, ha⟩ := iha hc.2
    obtain ⟨eb, hv⟩ := ihb ⟨(hcl.unfold? hu).instLevels, ha⟩
    exact ⟨.fixApp ef hu hr ea eb, hv⟩
  | constAtom hd ha hl =>
    have hd' : findDecl decls _ = some _ := (hsub.findDecl_eq hc).trans hd
    exact ⟨.constAtom hd' ((evalEnvOf_isAtom hsub hcl hc).trans ha) hl, hc⟩
  | appCong _ hb _ ihf iha =>
    obtain ⟨ef, hf⟩ := ihf hc.1
    obtain ⟨ea, ha⟩ := iha hc.2
    exact ⟨.appCong ef (mt (evalEnvOf_blocksCong hsub hf).1 hb) ea, hf, ha⟩
  | mdata _ ih =>
    obtain ⟨ev, hv⟩ := ih hc
    exact ⟨.mdata ev, hv⟩
  | atom h => exact ⟨.atom h, hc⟩

end

end EraseProof
