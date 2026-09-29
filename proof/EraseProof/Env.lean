import EraseProof.Typing.Basic
import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Verify.Environment.Lemmas

/-!
# Programs and their environment in lean4lean's model

A program's declarations are a newest-first list of `ConstantInfo`s. `ProgEnv P venv` relates such
a list to its model `venv` in lean4lean, one kernel step per declaration, and this module proves
that the model is ordered and well-formed and that every declaration of the list has its
translated type in the model.
-/

open Lean Lean4Lean

namespace EraseProof

/-- First declaration named `c`. Reference: `lookup_env`
(`MR common/theories/Environment.v:483`). -/
def findDecl (decls : List ConstantInfo) (c : Name) : Option ConstantInfo :=
  decls.find? (·.name == c)

/-- The type part of lean4lean `TrConstant` (`l4l Verify/Environment/Basic.lean:18`), with `TrS`.
Reference: `on_global_env` typing of a declaration's type (MC §3.6). -/
def TrConst (venv : VEnv) (ci : ConstantInfo) (ci' : VConstant) : Prop :=
  ci.levelParams.length = ci'.uvars ∧ TrS venv ci.levelParams [] ci.type ci'.type

/-- lean4lean `TrDefVal` (`l4l Verify/Environment/Basic.lean:27`), with `TrS`; the value is
translated in `venvV` (the block's environment for mutual blocks). Reference: MC §3.6. -/
def TrDef (venv venvV : VEnv) (ci : ConstantInfo) (ci' : VDefVal) : Prop :=
  TrConst venv ci ci'.toVConstant ∧ ci.name = ci'.name ∧
  TrS venvV ci.levelParams [] (ci.value! (allowOpaque := true)) ci'.value

/-- The program's environment in master's model: lean4lean `TrEnv'`
(`l4l Verify/Environment/Basic.lean:128`) at safety `.unsafe`, over a newest-first list, with
`TrS`; rules `axiom` (`:134`), `defn` (`:140`), `thm` (`:157`), `opaque` (`:164`), `block`
(= `mutualDef`, `:147`); no `ignore`/`quot`/`induct`; `all` as the kernel sets it (DV-3).
Reference: `wf_ext Σ` (`MR P/PCUICTyping.v:507`), MC §3.6. -/
inductive ProgEnv : List ConstantInfo → VEnv → Prop
  | nil : ProgEnv [] .empty
  | «axiom» {ci' : VConstant} :
      ProgEnv cs venv → TrConst venv (.axiomInfo v) ci' → ci'.WF venv →
      venv.addConst v.name ci' = some venv' → ProgEnv (.axiomInfo v :: cs) venv'
  | defn {ci' : VDefVal} :
      ProgEnv cs venv → v.all = [v.name] → TrDef venv venv (.defnInfo v) ci' → ci'.WF venv →
      venv.addConst v.name ci'.toVConstant = some venv' →
      ProgEnv (.defnInfo v :: cs) (venv'.addDefEq ci'.toDefEq)
  | thm {ci' : VDefVal} :
      ProgEnv cs venv → v.all = [v.name] → TrDef venv venv (.thmInfo v) ci' → ci'.WF venv →
      venv.HasType ci'.uvars [] ci'.type (.sort .zero) →
      venv.addConst v.name ci'.toVConstant = some venv' → ProgEnv (.thmInfo v :: cs) venv'
  | «opaque» {ci' : VDefVal} :
      ProgEnv cs venv → v.all = [v.name] → TrDef venv venv (.opaqueInfo v) ci' → ci'.WF venv →
      venv.addConst v.name ci'.toVConstant = some venv' → ProgEnv (.opaqueInfo v :: cs) venv'
  | block {vs : List DefinitionVal} {cis' : List VDefVal} :
      ProgEnv cs venv → (vs.map (·.name)).Nodup → (∀ v ∈ vs, v.all = vs.map (·.name)) →
      List.Forall₂ (fun v ci' => TrDef venv venv' (.defnInfo v) ci') vs cis' →
      (∀ ci' ∈ cis', ci'.toVConstant.WF venv) →
      venv.addConsts cis' = some venv' → (∀ ci' ∈ cis', ci'.WF venv') →
      ProgEnv (vs.reverse.map .defnInfo ++ cs) (venv'.addDefEqs cis')

section
variable {venv : VEnv} {P : List ConstantInfo}

/-- The defining equation of a definition added under its own name is well-formed, as in the
`def` case of lean4lean `VEnv.WF.ordered` (`l4l Theory/Typing/EnvLemmas.lean:87`). -/
theorem toDefEq_wf {venv' : VEnv} {ci' : VDefVal} (h1 : ci'.WF venv)
    (h2 : venv.addConst ci'.name ci'.toVConstant = some venv') : ci'.toDefEq.WF venv' := by
  refine ⟨?_, h1.mono (VEnv.addConst_le h2)⟩
  simp only [VDefVal.toDefEq]
  rw [← (h1.levelWF ⟨⟩).2.2.instL_id]
  exact .const (VEnv.addConst_self h2) VLevel.id_WF (by simp)

/-- `ProgEnv` gives lean4lean's `Ordered` (`l4l Theory/Typing/Lemmas.lean:253`) by its own
induction, without `VEnv.WF.ordered` (`l4l Theory/Typing/EnvLemmas.lean:87`, which reaches the
sorry L3). Reference: the `wf Σ` part of `wf_ext Σ` (MC §3.6). -/
theorem ProgEnv.ordered (h : ProgEnv P venv) : venv.Ordered := by
  induction h with
  | nil => exact .empty
  | «axiom» _ _ h1 h2 ih => exact .const ih h1 h2
  | defn _ _ htr h1 h2 ih =>
    have hn := htr.2.1
    dsimp only [ConstantInfo.name, ConstantInfo.toConstantVal] at hn
    rw [hn] at h2
    exact .defeq (.const ih (h1.isType ih ⟨⟩) h2) (toDefEq_wf h1 h2)
  | thm _ _ _ _ h1 h2 ih => exact .const ih ⟨_, h1⟩ h2
  | «opaque» _ _ _ h1 h2 ih => exact .const ih (h1.isType ih ⟨⟩) h2
  | block _ _ _ _ h1 h2 h3 ih =>
    exact VEnv.addDefEqs_ordered (VEnv.addConsts_ordered ih h1 h2)
      (VEnv.addConsts_constants h2) h3

/-- `ProgEnv` gives `VEnv.WF` (`l4l Theory/Typing/Env.lean:52`). Reference: lean4lean
`TrEnv'.wf` (`l4l Verify/Environment/Basic.lean:184`); `wf_ext Σ` (MC §3.6). -/
theorem ProgEnv.wf (h : ProgEnv P venv) : venv.WF := by
  induction h with
  | nil => exact ⟨_, .empty⟩
  | «axiom» _ _ h1 h2 ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl <| .«axiom» (ci := ⟨_, _⟩) h1 h2⟩
  | defn _ _ htr h1 h2 ih =>
    have ⟨_, H⟩ := ih
    have hn := htr.2.1
    dsimp only [ConstantInfo.name, ConstantInfo.toConstantVal] at hn
    rw [hn] at h2
    exact ⟨_, H.decl <| .def h1 h2⟩
  | thm _ _ htr h1 h2 h3 ih =>
    have ⟨_, H⟩ := ih
    have hn := htr.2.1
    dsimp only [ConstantInfo.name, ConstantInfo.toConstantVal] at hn
    rw [hn] at h3
    exact ⟨_, (H.decl (.example h1)).decl (.«axiom» (ci := ⟨_, _⟩) ⟨_, h2⟩ h3)⟩
  | «opaque» _ _ htr h1 h2 ih =>
    have ⟨_, H⟩ := ih
    have hn := htr.2.1
    dsimp only [ConstantInfo.name, ConstantInfo.toConstantVal] at hn
    rw [hn] at h2
    exact ⟨_, H.decl <| .«opaque» h1 h2⟩
  | block _ _ _ _ h1 h2 h3 ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl <| .mutualDef h1 h2 h3⟩

/-- `TrConst` is monotone in the environment (by `TrS.mono`). Reference: global weakening
(`MR pcuic/theories/PCUICWeakeningEnv.v:295 weakening_env_declared_constant`). -/
theorem TrConst.mono {venv' : VEnv} (hle : venv ≤ venv') (h : TrConst venv ci ci') :
    TrConst venv' ci ci' :=
  ⟨h.1, h.2.mono hle⟩

/-- `findDecl` on a cons: the head if it has the name, otherwise the tail's answer. -/
theorem findDecl_cons : findDecl (d :: ds) c = if d.name = c then some d else findDecl ds c := by
  simp only [findDecl, List.find?_cons]
  split <;> simp_all

/-- A member of the left list of `List.Forall₂ R` is related to a member of the right list. -/
theorem forall₂_exists_of_mem_left {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) (ha : a ∈ l₁) : ∃ b ∈ l₂, R a b := by
  induction h with
  | nil => cases ha
  | cons hr _ ih =>
    cases ha with
    | head => exact ⟨_, .head _, hr⟩
    | tail _ ha => have ⟨b, hb, h⟩ := ih ha; exact ⟨b, .tail _ hb, h⟩

/-- A declaration of `P` has its translated type in the model. Reference: `lookup_on_global_env`
(`MR common/theories/EnvironmentTyping.v:2205`). -/
theorem ProgEnv.lookup (h : ProgEnv P venv) (hc : findDecl P c = some ci) :
    ∃ ci', venv.constants c = some ci' ∧ TrConst venv ci ci' := by
  induction h generalizing ci with
  | nil => simp [findDecl] at hc
  | «axiom» _ htr _ h2 ih =>
    have hle := VEnv.addConst_le h2
    rw [findDecl_cons] at hc
    split at hc
    · cases hc; subst c
      exact ⟨_, VEnv.addConst_self h2, htr.mono hle⟩
    · have ⟨ci', h1, h2⟩ := ih hc
      exact ⟨ci', hle.constants h1, h2.mono hle⟩
  | @defn _ _ _ venv' ci' _ _ htr _ h2 ih =>
    have hle : _ ≤ venv'.addDefEq ci'.toDefEq := (VEnv.addConst_le h2).trans VEnv.addDefEq_le
    rw [findDecl_cons] at hc
    split at hc
    · cases hc; subst c
      exact ⟨_, VEnv.addDefEq_le.constants (VEnv.addConst_self h2), htr.1.mono hle⟩
    · have ⟨ci', h1, h2⟩ := ih hc
      exact ⟨ci', hle.constants h1, h2.mono hle⟩
  | thm _ _ htr _ _ h2 ih | «opaque» _ _ htr _ h2 ih =>
    have hle := VEnv.addConst_le h2
    rw [findDecl_cons] at hc
    split at hc
    · cases hc; subst c
      exact ⟨_, VEnv.addConst_self h2, htr.1.mono hle⟩
    · have ⟨ci', h1, h2⟩ := ih hc
      exact ⟨ci', hle.constants h1, h2.mono hle⟩
  | @block _ _ venv' vs cis' _ _ _ htr _ h2 _ ih =>
    have hle : _ ≤ venv'.addDefEqs cis' := (VEnv.addConsts_le h2).trans VEnv.addDefEqs_le
    simp only [findDecl, List.find?_append] at hc
    cases hb : (vs.reverse.map ConstantInfo.defnInfo).find? (·.name == c) with
    | none =>
      rw [hb, Option.none_or] at hc
      have ⟨ci', h1, h2⟩ := ih hc
      exact ⟨ci', hle.constants h1, h2.mono hle⟩
    | some d =>
      rw [hb, Option.some_or] at hc
      injection hc with hc
      subst hc
      have hn : d.name = c :=
        beq_iff_eq.1 (List.find?_some (p := fun x : ConstantInfo => x.name == c) hb)
      have ⟨v, hv, hd⟩ : ∃ v ∈ vs, ConstantInfo.defnInfo v = d := by
        simpa using List.mem_of_find?_eq_some hb
      subst hd hn
      have ⟨ci', hci', htr'⟩ := forall₂_exists_of_mem_left htr hv
      have hname : v.name = ci'.name := htr'.2.1
      refine ⟨_, ?_, htr'.1.mono hle⟩
      rw [show (ConstantInfo.defnInfo v).name = ci'.name from hname]
      exact VEnv.addDefEqs_le.constants (VEnv.addConsts_constants h2 _ hci')
end

end EraseProof
