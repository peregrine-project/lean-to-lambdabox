import Lean4Lean.Theory.Inductive
import Lean4Lean.Theory.Typing.InductiveParams
import Lean4Lean.Theory.Typing.EnvLemmas


/-!
Executable decision procedures for the syntactic predicates of `VInductDecl.WF`.

The shape, positivity and result-type predicates of `Lean4Lean.Theory.Inductive` are stated
as propositions and used as such in the theory; only the tests run them, on the translation
of the kernel's own recursor, constructor and ι-rule data. The `Decidable` instances that
make them executable therefore live here rather than beside the definitions, as do the ones
for the head-constructor tests of `Theory/VExpr.lean` that they are built out of.
-/

namespace Lean4Lean

deriving instance DecidableEq for VLevel
deriving instance DecidableEq for VExpr

namespace VExpr

instance {e f : VExpr} {pre : List VExpr} : Decidable (∃ rest, e = f.mkApps (pre ++ rest)) :=
  decidable_of_iff _ eq_mkApps_append_iff.symm

instance {e f : VExpr} {pre : List VExpr} {n : Nat} :
    Decidable (∃ rest, rest.length = n ∧ e = f.mkApps (pre ++ rest)) :=
  decidable_of_iff _ eq_mkApps_append_length_iff.symm

instance {α : Type _} {o : Option α} {P : α → Prop} [DecidablePred P] :
    Decidable (∃ a, o = some a ∧ P a) :=
  match o with
  | none => isFalse (by rintro ⟨_, h, _⟩; cases h)
  | some a =>
    decidable_of_iff (P a) ⟨fun h => ⟨a, rfl, h⟩, fun ⟨_, h, hp⟩ => Option.some.inj h ▸ hp⟩

instance {e : VExpr} : Decidable (∃ u, e = .sort u) := decidable_of_iff _ isSort_iff
instance {e : VExpr} : Decidable (∃ k, e = .bvar k) := decidable_of_iff _ isBvar_iff
instance {e : VExpr} : Decidable (∃ I us, e = .const I us) := decidable_of_iff _ isConst_iff

instance {ty : VExpr} : Decidable ty.RecHeaded := decidable_of_iff _ isBvar_iff
instance {ty : VExpr} : Decidable ty.CtorHeaded := decidable_of_iff _ isConst_iff

instance {cs : List Name} {e : VExpr} : Decidable (e.MentionsConst cs) :=
  decidable_of_iff _ mentionsConst_iff

instance {ty : VExpr} {T : Name} {np nf nind : Nat} : Decidable (ty.CtorResult T np nf nind) :=
  decidable_of_iff _ CtorResult_iff.symm

instance {A : VExpr} {T : Name} {np nm nmin nind : Nat} :
    Decidable (A.MajorApp T np nm nmin nind) := decidable_of_iff _ MajorApp_iff.symm

instance {fs : List Name} {np d : Nat} {e : VExpr} : Decidable (e.ValidIndApp fs np d) :=
  decidable_of_iff _ ValidIndApp_iff.symm

instance {fs : List Name} {np d : Nat} {ty : VExpr} : Decidable (ty.FieldPositive fs np d) := by
  unfold FieldPositive; infer_instance

instance {fs : List Name} {np : Nat} {ty : VExpr} : Decidable (ty.CtorPositive fs np) := by
  unfold CtorPositive; infer_instance

instance {ty : VExpr} {np i : Nat} : Decidable (ty.FieldInIndices np i) := by
  unfold FieldInIndices; infer_instance

instance {A : VExpr} : Decidable A.MotiveShape := by unfold MotiveShape; infer_instance
instance {A : VExpr} {i nm : Nat} : Decidable (A.MinorHeaded i nm) := by
  unfold MinorHeaded; infer_instance
instance {A : VExpr} {c : Name} : Decidable (A.MinorFor c) := by
  unfold MinorFor; infer_instance
instance {ty : VExpr} {np nm nmin nind : Nat} : Decidable (ty.RecShape np nm nmin nind) := by
  unfold RecShape; infer_instance
instance {ty : VExpr} {arity : Nat} : Decidable (ty.CtorShape arity) := by
  unfold CtorShape; infer_instance
instance {rhs : VExpr} {np nm nmin nf nrec j : Nat} :
    Decidable (rhs.RuleShape np nm nmin nf nrec j) := by
  unfold RuleShape; infer_instance

end VExpr

instance {decl : VInductDecl} : Decidable decl.LargeElimShape := by
  unfold VInductDecl.LargeElimShape; infer_instance


namespace Q2Probe
open Lean4Lean VExpr

def Un : Name := `Q2U
def un : Name := `Q2u
def Rn : Name := `Q2U.rec

def Uc : VExpr := .const Un []
def uc : VExpr := .const un []
def CT : VExpr := .forallE Uc (.sort (.param 0))
def MT : VExpr := .app (.bvar 0) uc
def RT : VExpr := .forallE CT (.forallE MT (.forallE Uc (.app (.bvar 2) (.bvar 0))))
def rhs0 : VExpr := .lam CT (.lam MT (.bvar 0))

def uV : VConstVal := { name := un, uvars := 0, type := Uc }
def UT : VInductiveType := { name := Un, uvars := 0, type := .sort (.succ .zero), ctors := [uV] }
def ru0 : VRecRule := { ctor := un, ctorParams := 0, nfields := 0, rhs := rhs0 }
def RV : VRecursor :=
  { name := Rn, uvars := 1, type := RT, all := [Un], numParams := 0, numMotives := 1,
    numMinors := 1, numIndices := 0, k := false, rules := [ru0] }

def declU : VInductDecl where
  uvars := 0; nparams := 0; types := [UT]; recs := [RV]

-- syntactic clauses, decided
theorem s_recshape : RT.RecShape 0 1 1 0 := by decide
theorem s_ctorresult : uV.type.CtorResult Un 0 0 0 := by decide
theorem s_ctorpos : uV.type.CtorPositive [Un] 0 := by decide
theorem s_ruleshape :
    rhs0.RuleShape 0 1 1 0 0 0 := by decide

/-! ### stage environments and lookups -/

theorem hUn : ∀ envT, declU.addTypes .empty = some envT →
    envT.constants Un = some ⟨0, .sort (.succ .zero)⟩ := by
  intro envT h
  have := VEnv.addTypes_find (decl := declU) h (t := UT) (by simp [declU])
  simpa [UT, VConstVal.toVConstant, VInductiveType.toVConstVal] using this

theorem hlevel0 : ∀ l ∈ ([] : List VLevel), l.WF 0 := by simp
theorem hp0 : (VLevel.param 0).WF 1 := by simp [VLevel.WF]

/-- `types_wf`. -/
theorem c_types_wf : ∀ t ∈ declU.types, t.toVConstVal.toVConstant.WF VEnv.empty := by
  intro t ht
  simp [declU] at ht; subst ht
  exact ⟨_, VEnv.HasType.sort (l := .succ .zero) (by simp [VLevel.WF])⟩

/-- `ctors_wf`. -/
theorem c_ctors_wf : ∀ envT, declU.addTypes .empty = some envT →
    ∀ t ∈ declU.types, ∀ c ∈ t.ctors, c.toVConstant.WF envT := by
  intro envT h t ht c hc
  simp [declU] at ht; subst ht; simp [UT] at hc; subst hc
  exact ⟨_, VEnv.HasType.const (hUn _ h) hlevel0 rfl⟩


/-! ### recs_wf -/

theorem hUnC : ∀ envC, declU.addTypesCtors .empty = some envC →
    envC.constants Un = some ⟨0, .sort (.succ .zero)⟩ ∧
    envC.constants un = some ⟨0, Uc⟩ := by
  intro envC h
  rw [VInductDecl.addTypesCtors] at h
  obtain ⟨envT, hT, hC⟩ := Option.bind_eq_some_iff.1 h
  have h1 := VEnv.addTypes_find (decl := declU) hT (t := UT) (by simp [declU])
  have h2 := VEnv.addCtors_find (decl := declU) hC (t := UT) (by simp [declU]) (c := uV) (by simp [UT])
  refine ⟨(VEnv.addCtors_le hC).constants ?_, ?_⟩
  · simpa [UT, VConstVal.toVConstant, VInductiveType.toVConstVal] using h1
  · simpa [uV, VConstVal.toVConstant] using h2

theorem c_recs_wf : ∀ envC, declU.addTypesCtors .empty = some envC →
    ∀ r ∈ declU.recs, r.toVConstVal.toVConstant.WF envC := by
  intro envC h r hr
  simp [declU] at hr; subst hr
  obtain ⟨hU, hu⟩ := hUnC _ h
  have tU : ∀ Γ, envC.HasType 1 Γ Uc (.sort (.succ .zero)) := fun Γ => by
    have := VEnv.HasType.const (Γ := Γ) (U := 1) (ls := []) hU (by simp) rfl
    simpa [Uc, VExpr.instL, VLevel.inst] using this
  have tu : ∀ Γ, envC.HasType 1 Γ uc Uc := fun Γ => by
    have := VEnv.HasType.const (Γ := Γ) (U := 1) (ls := []) hu (by simp) rfl
    simpa [uc, Uc, VExpr.instL, VLevel.inst] using this
  have tCT : ∀ Γ, envC.HasType 1 Γ CT (.sort (.imax (.succ .zero) (.succ (.param 0)))) :=
    fun Γ => VEnv.HasType.forallE (tU Γ) (VEnv.HasType.sort hp0)
  have tMT : envC.HasType 1 [CT] MT (.sort (.param 0)) := by
    have hb : envC.HasType 1 [CT] (.bvar 0) CT := by
      have := VEnv.HasType.bvar (env := envC) (U := 1) (Γ := [CT]) (Lookup.zero)
      simpa [CT, Uc, VExpr.lift, VExpr.liftN] using this
    have := VEnv.HasType.app hb (tu [CT])
    simpa [MT, CT, VExpr.inst] using this
  have hb2 : envC.HasType 1 [Uc, MT, CT] (.bvar 2) CT := by
    have := VEnv.HasType.bvar (env := envC) (U := 1) (Γ := [Uc, MT, CT])
      (Lookup.succ (Lookup.succ Lookup.zero))
    simpa [CT, Uc, VExpr.lift, VExpr.liftN] using this
  have hb0 : envC.HasType 1 [Uc, MT, CT] (.bvar 0) Uc := by
    have := VEnv.HasType.bvar (env := envC) (U := 1) (Γ := [Uc, MT, CT]) Lookup.zero
    simpa [Uc, VExpr.lift, VExpr.liftN] using this
  have tbody : envC.HasType 1 [Uc, MT, CT] (.app (.bvar 2) (.bvar 0)) (.sort (.param 0)) := by
    have := VEnv.HasType.app (A := Uc) (B := .sort (.param 0)) (by simpa [CT] using hb2) hb0
    simpa [VExpr.inst] using this
  exact ⟨_, VEnv.HasType.forallE (tCT []) (VEnv.HasType.forallE tMT
    (VEnv.HasType.forallE (tU _) tbody))⟩


/-! ### rules_wf : PatTyped -/

theorem hUnR : ∀ envR, declU.addTypesCtorsRecs .empty = some envR →
    envR.constants Un = some ⟨0, .sort (.succ .zero)⟩ ∧
    envR.constants un = some ⟨0, Uc⟩ ∧ envR.constants Rn = some ⟨1, RT⟩ := by
  intro envR h
  rw [VInductDecl.addTypesCtorsRecs] at h
  obtain ⟨envC, hC, hR⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨h1, h2⟩ := hUnC _ hC
  have h3 := VEnv.addRecs_find (decl := declU) hR (r := RV) (by simp [declU])
  exact ⟨(VEnv.addRecs_le hR).constants h1, (VEnv.addRecs_le hR).constants h2,
    by simpa [RV, VConstVal.toVConstant, VRecursor.toVConstVal] using h3⟩

theorem c_rules_wf : ∀ envR, declU.addTypesCtorsRecs .empty = some envR →
    ∀ r ∈ declU.recs, ∀ ru ∈ r.rules, ∀ hc : ru.rhs.Closed,
      envR.PatTyped
        (SimplePattern.iota r.name r.getMajorIdx ru.ctor (ru.ctorParams + ru.nfields)).toPattern
        (SimplePattern.iotaRHS r.name ru.ctor r.numParams r.numMotives r.numMinors
          r.numIndices ru.ctorParams ru.nfields ru.rhs hc, .true) := by
  intro envR h r hr ru hru hc
  simp [declU] at hr; subst hr; simp [RV] at hru; subst hru
  obtain ⟨hU, hu, hR⟩ := hUnR _ h
  obtain ⟨g, hg, hgeq⟩ :=
    Pattern.matches_varN_const (c := Rn) (ls := [VLevel.param 0]) 2 [.bvar 1, .bvar 0] rfl
  have tU : ∀ Γ, envR.HasType 1 Γ Uc (.sort (.succ .zero)) := fun Γ => by
    have := VEnv.HasType.const (Γ := Γ) (U := 1) (ls := []) hU (by simp) rfl
    simpa [Uc, VExpr.instL, VLevel.inst] using this
  have tu : ∀ Γ, envR.HasType 1 Γ uc Uc := fun Γ => by
    have := VEnv.HasType.const (Γ := Γ) (U := 1) (ls := []) hu (by simp) rfl
    simpa [uc, Uc, VExpr.instL, VLevel.inst] using this
  have tCT : ∀ Γ, envR.HasType 1 Γ CT (.sort (.imax (.succ .zero) (.succ (.param 0)))) :=
    fun Γ => VEnv.HasType.forallE (tU Γ) (VEnv.HasType.sort hp0)
  have tMT : ∀ Γ, envR.HasType 1 (CT :: Γ) MT (.sort (.param 0)) := fun Γ => by
    have hb : envR.HasType 1 (CT :: Γ) (.bvar 0) CT := by
      have := VEnv.HasType.bvar (env := envR) (U := 1) (Γ := CT :: Γ) Lookup.zero
      simpa [CT, Uc, VExpr.lift, VExpr.liftN] using this
    have := VEnv.HasType.app hb (tu _)
    simpa [MT, CT, VExpr.inst] using this
  have tRn : envR.HasType 1 [MT, CT] (.const Rn [.param 0]) RT := by
    have := VEnv.HasType.const (Γ := [MT, CT]) (U := 1) (ls := [VLevel.param 0]) hR
      (by simp [VLevel.WF]) rfl
    simpa [RT, CT, MT, Uc, uc, VExpr.instL, VLevel.inst] using this
  have hb1 : envR.HasType 1 [MT, CT] (.bvar 1) CT := by
    have := VEnv.HasType.bvar (env := envR) (U := 1) (Γ := [MT, CT]) (Lookup.succ Lookup.zero)
    simpa [CT, Uc, VExpr.lift, VExpr.liftN] using this
  have hb0 : envR.HasType 1 [MT, CT] (.bvar 0) (.app (.bvar 1) uc) := by
    have := VEnv.HasType.bvar (env := envR) (U := 1) (Γ := [MT, CT]) Lookup.zero
    simpa [MT, uc, VExpr.lift, VExpr.liftN] using this
  show envR.PatTyped (SimplePattern.iota Rn 2 un 0).toPattern
    (SimplePattern.iotaRHS Rn un 0 1 1 0 0 0 rhs0 hc, .true)
  refine ⟨1, [MT, CT],
    .app ((VExpr.const Rn [VLevel.param 0]).mkApps [.bvar 1, .bvar 0]) (.const un []),
    _, .app (.bvar 1) uc,
    Pattern.Matches.app (a := Pattern.const un) hg (Pattern.Matches.const (c := un) (ls := [])),
    ?_, ?_, ?_⟩
  · -- `Pattern.RHS.Generic`: pure list bookkeeping over `SimplePattern.iotaPaths`.
    -- `iotaPaths Rn un 2 0 0 0` reduces to `[Sum.inl (some none), Sum.inl none]` and
    -- `g` sends them to `bvar 1`, `bvar 0`; what is missing is a normal form for
    -- `(iotaRHS' ...).Uses` (simp does not push through the `List.map`/`List.foldl`
    -- that builds the reduct).  No typing, no kernel theory.  UPSTREAM ASK #2.
    sorry
  · have t2 : envR.HasType 1 [MT, CT] (.app (.const Rn [.param 0]) (.bvar 1))
        (.forallE (.app (.bvar 1) uc) (.forallE Uc (.app (.bvar 3) (.bvar 0)))) :=
      VEnv.HasType.app (show envR.HasType 1 [MT, CT] (.const Rn [.param 0])
        (.forallE CT (.forallE MT (.forallE Uc (.app (.bvar 2) (.bvar 0))))) from tRn) hb1
    have t3 : envR.HasType 1 [MT, CT] (.app (.app (.const Rn [.param 0]) (.bvar 1)) (.bvar 0))
        (.forallE Uc (.app (.bvar 2) (.bvar 0))) := VEnv.HasType.app t2 hb0
    exact VEnv.HasType.app t3 (tu [MT, CT])
  · have heq : Pattern.RHS.apply (p := (SimplePattern.iota Rn 2 un 0).toPattern)
        (VLevel.params 1) (Sum.elim g nofun) (SimplePattern.iotaRHS' Rn un 2 0 0 0 rhs0 hc)
        = rhs0.mkApps [.bvar 1, .bvar 0] := by
      have key := SimplePattern.iotaRHS'_apply Rn un 2 0 0 0 rhs0 hc (VLevel.params 1)
        (Sum.elim g nofun) (recArgs := [.bvar 1, .bvar 0]) (ctorArgs := []) rfl rfl
        (fun i hi => by simpa using hgeq i hi) (fun i hi => by simp at hi)
      have hri : rhs0.instL (VLevel.params 1) = rhs0 := by
        simp [rhs0, CT, MT, Uc, uc, VExpr.instL, VLevel.inst, VLevel.params]
      rw [hri] at key
      exact key
    show envR.HasType 1 [MT, CT] (Pattern.RHS.apply
      (p := (SimplePattern.iota Rn 2 un 0).toPattern) (VLevel.params 1)
      (Sum.elim g nofun) (SimplePattern.iotaRHS' Rn un 2 0 0 0 rhs0 hc)) (.app (.bvar 1) uc)
    rw [heq]
    · have tr : envR.HasType 1 [MT, CT] rhs0 (.forallE CT (.forallE MT (.app (.bvar 1) uc))) := by
        refine VEnv.HasType.lam (tCT _) (VEnv.HasType.lam (tMT _) ?_)
        have := VEnv.HasType.bvar (env := envR) (U := 1) (Γ := [MT, CT, MT, CT]) Lookup.zero
        simpa [MT, uc, VExpr.lift, VExpr.liftN] using this
      have s2 : envR.HasType 1 [MT, CT] (.app rhs0 (.bvar 1))
          (.forallE (.app (.bvar 1) uc) (.app (.bvar 2) uc)) := VEnv.HasType.app tr hb1
      exact VEnv.HasType.app s2 hb0


/-! ### the remaining clauses, all syntactic -/

theorem c_wf : declU.WF VEnv.empty where
  types_wf := c_types_wf
  ctors_wf := c_ctors_wf
  recs_wf := c_recs_wf
  types_uvars := by intro t ht; simp [declU] at ht; subst ht; rfl
  ctors_uvars := by
    intro t ht c hc; simp [declU] at ht; subst ht; simp [UT] at hc; subst hc; rfl
  universes := by
    intro envT _
    refine ⟨.succ .zero, ?_, ?_, fun _ => Or.inl (by intro ls; simp [VLevel.eval])⟩
    · intro t ht; simp [declU] at ht; subst ht; exact ⟨rfl, by simp [UT, declU, VExpr.piArity]⟩
    · intro t ht c hc i hi; simp [declU] at ht; subst ht; simp [UT] at hc; subst hc
      simp [uV, Uc, VExpr.piArity] at hi
  recs_elim := by
    intro r hr; simp [declU] at hr; subst hr
    exact ⟨Or.inr rfl, by decide⟩
  rec_params := by intro r hr; simp [declU] at hr; subst hr; rfl
  ctors_params := by
    intro t ht c hc; simp [declU] at ht; subst ht; simp [UT] at hc; subst hc; rfl
  ctors_result := by
    intro t ht c hc; simp [declU] at ht; subst ht; simp [UT] at hc; subst hc
    exact ⟨0, by decide⟩
  ctors_positive := by
    intro t ht c hc; simp [declU] at ht; subst ht; simp [UT] at hc; subst hc; decide
  recs_over_block := by
    intro r hr; simp [declU] at hr; subst hr; exact ⟨UT, by simp [declU], by decide⟩
  rec_counts := by
    intro r hr; simp [declU] at hr; subst hr
    refine ⟨rfl, rfl, ?_⟩
    intro t ht _; simp [declU] at ht; subst ht; decide
  rec_shape := by intro r hr; simp [declU] at hr; subst hr; decide
  rules_nodup := by intro r hr; simp [declU] at hr; subst hr; decide
  rules_ctor := by
    intro r hr ru hru; simp [declU] at hr; subst hr; simp [RV] at hru; subst hru
    exact ⟨UT, by simp [declU], by decide, uV, by simp [UT], rfl, rfl, by decide⟩
  types_have_rec := by
    intro t ht; simp [declU] at ht; subst ht; exact ⟨RV, by simp [declU], by decide⟩
  rules_total := by
    intro r hr t ht _ c hc; simp [declU] at hr; subst hr
    simp [declU] at ht; subst ht; simp [UT] at hc; subst hc
    exact ⟨ru0, by simp [RV], rfl⟩
  rule_shape := by
    intro r hr ru hru; simp [declU] at hr; subst hr; simp [RV] at hru; subst hru
    exact ⟨0, by decide, MT, by decide, by decide, by decide, by decide⟩
  rules_wf := c_rules_wf

/-- **A pats-carrying `VEnv.WF`.** -/
theorem c_env_wf : ∃ env, VEnv.addInduct .empty declU = some env ∧ env.WF := by
  obtain ⟨env, hadd⟩ : ∃ env, VEnv.addInduct .empty declU = some env := ⟨_, rfl⟩
  exact ⟨env, hadd, ⟨[.induct declU], .decl (.induct c_wf hadd) .empty⟩⟩

/-- and it really carries an ι rule. -/
theorem c_env_pats : ∃ env, VEnv.addInduct .empty declU = some env ∧ env.WF ∧
    ∃ p r, env.pats p r := by
  obtain ⟨env, hadd, hwf⟩ := c_env_wf
  exact ⟨env, hadd, hwf, _, _,
    VEnv.addInduct_pat (r := RV) (by simp [declU]) (ru := ru0) (by simp [RV]) (by decide) hadd⟩

end Q2Probe
