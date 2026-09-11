import LeanToLambdaBox.LowerFix
import LeanToLambdaBox.Output
import LeanToLambdaBox.Supported

/-!
# `ErasesEnv` — the dependency-selective environment erasure

`ErasesEnv env bo Γspec t` relates a source environment to the **specification** λ□
environment `Γspec` a program `t` is read against: its keys are distinct, every
declaration it holds is justified by `ErasesDecl`, and every kername `t` reaches through
`Γspec` is present. It is `erases_deps` of Sozeau et al.: bottom-up and selective, not a
pointwise image of the whole source environment.

`ErasesDecl` has one arm per kind of entry the eraser emits — a definition whose body is
the compiler's, an inert axiom, an inductive block, a constructor constant, and a
`casesOn` eliminator. `LowerEnv Γspec Γ` relates the specification environment to the
emitted one, and `EnvAgree` is the equivalence the emitted environment is pinned up to:
every consumer of a `GlobalDeclarations` reads it through `LBTerm.envLookup`.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-! ## Kername equality

`Kername.beq` is the comparison `LBTerm.envLookup` uses; these are its reflexivity and
its adequacy, which a concrete environment's lookups are computed with.
-/

theorem ModPath.eq_of_beq : ∀ {mp mp' : ModPath}, ModPath.beq mp mp' = true → mp = mp'
  | .MPfile _, .MPfile _, h => by simp [ModPath.beq] at h; simp [h]
  | .MPdot mp _, .MPdot mp' _, h => by
      simp [ModPath.beq] at h
      rw [ModPath.eq_of_beq h.1, h.2]
  | .MPfile _, .MPdot _ _, h | .MPdot _ _, .MPfile _, h => by simp [ModPath.beq] at h

theorem ModPath.beq_self : ∀ mp : ModPath, ModPath.beq mp mp = true
  | .MPfile _ => by simp [ModPath.beq]
  | .MPdot mp _ => by simp [ModPath.beq, ModPath.beq_self mp]

theorem Kername.eq_of_beq {k k' : Kername} (h : Kername.beq k k' = true) : k = k' := by
  simp only [Kername.beq, Bool.and_eq_true] at h
  obtain ⟨hmp, hid⟩ := h
  cases k; cases k'
  simp_all only [Kername.mk.injEq]
  exact ⟨ModPath.eq_of_beq hmp, by simpa using hid⟩

theorem Kername.beq_self (k : Kername) : Kername.beq k k = true := by
  simp [Kername.beq, ModPath.beq_self]

theorem Kername.beq_iff {k k' : Kername} : Kername.beq k k' = true ↔ k = k' :=
  ⟨Kername.eq_of_beq, fun h => h ▸ Kername.beq_self k⟩

/-! ## Source-side declaration facts

What `ErasesDecl` reads off the source environment. A `VEnv` stores constants, defeqs and
ι patterns; a declaration *block* lives in the `VEnv.WF'` declaration list, which is why
the inductive-shaped facts go through `IndInfo`.
-/

/-- The head constant of an ι pattern. -/
def patHead : Pattern → Name
  | .const c => c
  | .app f _ => patHead f
  | .var f => patHead f

/-- `p` is one of `env`'s ι patterns. -/
def PatOf (env : VEnv) (p : Pattern) : Prop := ∃ r, env.pats p r

/-- No ι rule of `env` is keyed on `c`: unfolding `c` is the only way a source
derivation can make progress at it. -/
def IotaInert (env : VEnv) (c : Name) : Prop := ∀ p, PatOf env p → patHead p ≠ c

/-- `c` is the `k`-th constructor of the inductive type `I`, read off a declaration list
of `VEnv.WF'` below `env` — the same reading `IndInfo` takes. -/
def CtorOf (env : VEnv) (c I : Name) (k : Nat) : Prop :=
  ∃ (ds : List VDecl) (env₀ : VEnv) (decl : VInductDecl) (t : VInductiveType)
    (ctor : VConstVal),
    VEnv.WF' ds env₀ ∧ VDecl.induct decl ∈ ds ∧ env₀ ≤ env ∧
    t ∈ decl.types ∧ t.name = I ∧ t.ctors[k]? = some ctor ∧ ctor.name = c

/-- `kn` is the λ□ kername of `I`'s `casesOn` eliminator: a constant of `env` named
`I.casesOn`. Sparse `casesOn` constants are named after the enclosing function, are
mistranslated by the eraser and are excluded from the fragment, so they are not here. -/
def CasesOnOf (env : VEnv) (I : Name) (kn : Kername) : Prop :=
  ∃ (c : Name) (ci : VConstant), env.constants c = some ci ∧ isCasesOnName c = true ∧
    c.getPrefix = I ∧ kn = toKername c

/-- The λ□ inductive body the eraser emits for the block of `iid`, at the resolution the
target semantics reads it: `constructorArity` reads `npars` and the per-constructor field
counts, `isPropositionalInductive` reads `propositional`. -/
def IndBodyOf (iid : InductiveId) (np : Nat) (nfs : List Nat)
    (mib : MutualInductiveBody) : Prop :=
  mib.npars = np ∧ ∃ oib, mib.bodies[iid.idx]? = some oib ∧
    oib.propositional = false ∧ oib.ctors.map (·.nargs) = nfs

/-! ## `ErasesDecl` -/

/--
One entry of the specification environment, justified by the source environment.

`bo` is the **compiler** body table, the one `SEval.deltaC` reads, so a `defn` entry and
the source δ rule unfold the same term. `Us` is existential because the parameter names a
declaration is erased at are not recoverable from a `VEnv`, which records only their
number; that number is pinned by `huv`.
-/
inductive ErasesDecl (env : VEnv) (bo : Name → Option Expr) : Kername → GlobalDecl → Prop
  /-- A definition erases its compiler body at a level scope of the declared width. -/
  | defn {c body b₀ Us ci} (hc : env.constants c = some ci) (huv : Us.length = ci.uvars)
      (hd : bo c = some body) (hb : Erases env Us [] body b₀) :
      ErasesDecl env bo (toKername c) (.constantDecl ⟨some b₀⟩)
  /-- An inert constant: no compiler body **and** no ι rule keyed on it. Without the
      second premise an applied recursor would be declared body-less while the source
      still ι-steps and the target is stuck. -/
  | ax {c ci} (h : env.constants c = some ci) (hno : bo c = none)
      (hpat : IotaInert env c) :
      ErasesDecl env bo (toKername c) (.constantDecl ⟨none⟩)
  /-- An inductive block, keyed on the block kername `IndInfo` pins. -/
  | ind {I iid np nfs mib} (h : IndInfo env I iid np nfs) (hm : IndBodyOf iid np nfs mib) :
      ErasesDecl env bo iid.mutualBlockName (.inductiveDecl mib)
  /-- A constructor constant, whose body is the empty constructor block the pass
      saturates. -/
  | ctor {c I iid k np nfs} (h : CtorOf env c I k) (hi : IndInfo env I iid np nfs) :
      ErasesDecl env bo (toKername c) (.constantDecl ⟨some (.construct iid k [])⟩)
  /-- A `casesOn` eliminator of an **informative** inductive. An eliminator of a
      non-informative one has no entry: its emitted `.case` is stuck on every value a run
      produces, so declaring it would claim a correctness it does not have. -/
  | elim {I kn iid np dp nfs body} (hi : IndInfo env I iid np nfs) (he : CasesOnOf env I kn)
      (hinf : InformativeInd env I) (hb : ElimBody iid np dp nfs body) :
      ErasesDecl env bo kn (.constantDecl ⟨some body⟩)

/-! ## `ErasesEnv` -/

/--
The specification environment of a program, `erases_deps` of Sozeau et al.

Three clauses, written out rather than elided: the keys are distinct, so a shadowing
entry cannot retarget a lookup; every declaration the environment answers with is
justified by `ErasesDecl`; and every kername `t` reaches is answered at all.
-/
inductive ErasesEnv (env : VEnv) (bo : Name → Option Expr) :
    GlobalDeclarations → LBTerm → Prop
  /-- The only clause: the three conditions, at one environment and one program. -/
  | mk {Γspec : GlobalDeclarations} {t : LBTerm}
      (keys : (Γspec.map Prod.fst).Nodup)
      (decls : ∀ kn d, LBTerm.envLookup Γspec kn = some d → ErasesDecl env bo kn d)
      (deps : ∀ kn, ReachableFrom Γspec t kn → (LBTerm.envLookup Γspec kn).isSome) :
      ErasesEnv env bo Γspec t

/-- The keys of a specification environment are distinct. -/
theorem ErasesEnv.keys {env : VEnv} {bo : Name → Option Expr} {Γspec : GlobalDeclarations}
    {t : LBTerm} (h : ErasesEnv env bo Γspec t) : (Γspec.map Prod.fst).Nodup := by
  cases h with | mk k _ _ => exact k

/-- Every declaration a specification environment answers with is `ErasesDecl`-justified. -/
theorem ErasesEnv.decls {env : VEnv} {bo : Name → Option Expr} {Γspec : GlobalDeclarations}
    {t : LBTerm} (h : ErasesEnv env bo Γspec t) :
    ∀ kn d, LBTerm.envLookup Γspec kn = some d → ErasesDecl env bo kn d := by
  cases h with | mk _ d _ => exact d

/-- Every kername the program reaches is declared. -/
theorem ErasesEnv.deps {env : VEnv} {bo : Name → Option Expr} {Γspec : GlobalDeclarations}
    {t : LBTerm} (h : ErasesEnv env bo Γspec t) :
    ∀ kn, ReachableFrom Γspec t kn → (LBTerm.envLookup Γspec kn).isSome := by
  cases h with | mk _ _ d => exact d

/-! ## Lookup plumbing

`LBTerm.envLookup` answers with the first `Kername.beq`-matching entry, so a lookup that
succeeds exhibits a member of the list, and a literal environment is decided key by key.
-/

/-- A successful lookup exhibits the entry it answered with. -/
theorem envLookup_mem : ∀ {Γ : GlobalDeclarations} {kn : Kername} {d : GlobalDecl},
    LBTerm.envLookup Γ kn = some d → (kn, d) ∈ Γ
  | [], _, _, h => by simp [LBTerm.envLookup] at h
  | (k, e) :: rest, kn, d, h => by
      rw [LBTerm.envLookup] at h
      split at h
      · rename_i hb
        cases h
        rw [← Kername.eq_of_beq hb]
        exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (envLookup_mem h)

/-- The hit branch of a lookup. -/
theorem envLookup_cons_self {k : Kername} {d : GlobalDecl} {rest : GlobalDeclarations} :
    LBTerm.envLookup ((k, d) :: rest) k = some d := by
  rw [LBTerm.envLookup, if_pos (Kername.beq_self k)]

/-- The miss branch of a lookup. -/
theorem envLookup_cons_ne {k kn : Kername} {d : GlobalDecl} {rest : GlobalDeclarations}
    (h : k ≠ kn) : LBTerm.envLookup ((k, d) :: rest) kn = LBTerm.envLookup rest kn := by
  rw [LBTerm.envLookup, if_neg]
  exact fun hb => h (Kername.eq_of_beq hb)

/-! ## `EnvAgree` — the equivalence the emitted environment is pinned up to -/

/-- Two environments answer every lookup alike, and both have distinct keys. Every
consumer of a `GlobalDeclarations` — `WcbvEval`, `constructorArity`,
`isPropositionalInductive` — reads it only through `LBTerm.envLookup`, so this, and not
list equality, is the equivalence a conclusion about an emitted environment is stated up
to. -/
def EnvAgree (Γ Γ' : GlobalDeclarations) : Prop :=
  (∀ kn, LBTerm.envLookup Γ kn = LBTerm.envLookup Γ' kn) ∧
    (Γ.map Prod.fst).Nodup ∧ (Γ'.map Prod.fst).Nodup

@[inherit_doc] scoped infix:50 " ≐ " => EnvAgree

/-- Agreement is reflexive on an environment with distinct keys. -/
theorem EnvAgree.rfl' {Γ : GlobalDeclarations} (h : (Γ.map Prod.fst).Nodup) : Γ ≐ Γ :=
  ⟨fun _ => rfl, h, h⟩

/-- Agreement is symmetric. -/
theorem EnvAgree.symm {Γ Γ' : GlobalDeclarations} (h : Γ ≐ Γ') : Γ' ≐ Γ :=
  ⟨fun kn => (h.1 kn).symm, h.2.2, h.2.1⟩

/-- Agreement is transitive. -/
theorem EnvAgree.trans {Γ Γ' Γ'' : GlobalDeclarations} (h : Γ ≐ Γ') (h' : Γ' ≐ Γ'') :
    Γ ≐ Γ'' :=
  ⟨fun kn => (h.1 kn).trans (h'.1 kn), h.2.1, h'.2.2⟩

/-- Agreeing environments call the same inductives propositional. -/
theorem EnvAgree.isProp {Γ Γ' : GlobalDeclarations} (h : Γ ≐ Γ')
    (iid : InductiveId) :
    isPropositionalInductive Γ iid = isPropositionalInductive Γ' iid := by
  unfold isPropositionalInductive; rw [h.1]

/-- Agreeing environments give the same constructor arities. -/
theorem EnvAgree.ctorArity {Γ Γ' : GlobalDeclarations} (h : Γ ≐ Γ')
    (iid : InductiveId) (k : Nat) :
    constructorArity Γ iid k = constructorArity Γ' iid k := by
  unfold constructorArity; rw [h.1]

/-- Evaluation only reads the environment through `LBTerm.envLookup`, so it transports
along `EnvAgree`. -/
theorem WcbvEval.congr_env {Γ Γ' : GlobalDeclarations} (h : Γ ≐ Γ') {fl : WcbvFlags}
    {t v : LBTerm} (hev : WcbvEval Γ fl t v) : WcbvEval Γ' fl t v := by
  induction hev with
  | box => exact .box
  | lam n b => exact .lam n b
  | fvar x => exact .fvar x
  | prim p => exact .prim p
  | fix_atom defs i => exact .fix_atom defs i
  | beta _ _ _ ih1 ih2 ih3 => exact .beta ih1 ih2 ih3
  | app_box _ _ ih1 ih2 => exact .app_box ih1 ih2
  | zeta _ _ ih1 ih2 => exact .zeta ih1 ih2
  | delta hl _ ih => exact .delta (by rw [← h.1]; exact hl) ih
  | construct hb hl _ ih => exact .construct hb hl ih
  | construct_atom hb ha => exact .construct_atom hb (by rw [← h.ctorArity]; exact ha)
  | construct_app hb _ ha hlt _ ih1 ih2 =>
      exact .construct_app hb ih1 (by rw [← h.ctorArity]; exact ha) hlt ih2
  | iota hb hp _ halt hlen _ ih1 ih2 =>
      exact .iota hb (by rw [← h.isProp]; exact hp) ih1 halt hlen ih2
  | iota_block hb hp _ halt hlen _ ih1 ih2 =>
      exact .iota_block hb (by rw [← h.isProp]; exact hp) ih1 halt hlen ih2
  | iota_sing hpc hp _ _ ih1 ih2 =>
      exact .iota_sing hpc (by rw [← h.isProp]; exact hp) ih1 ih2
  | proj hb hp _ hget _ ih1 ih2 =>
      exact .proj hb (by rw [← h.isProp]; exact hp) ih1 hget ih2
  | proj_block hb hp _ hget _ ih1 ih2 =>
      exact .proj_block hb (by rw [← h.isProp]; exact hp) ih1 hget ih2
  | proj_prop hpc hp _ ih =>
      exact .proj_prop hpc (by rw [← h.isProp]; exact hp) ih
  | fix_guarded hg _ _ hdef hidx _ ih1 ih2 ih3 => exact .fix_guarded hg ih1 ih2 hdef hidx ih3
  | fix_stuck hg _ _ hdef hlt ih1 ih2 => exact .fix_stuck hg ih1 ih2 hdef hlt
  | fix_unguarded hg _ hdef _ _ ih1 ih2 ih3 => exact .fix_unguarded hg ih1 hdef ih2 ih3
  | app_cong _ hstuck _ ih1 ih2 => exact .app_cong ih1 hstuck ih2

/-! ## The two environment-level predicates a pass is stated against -/

/-- Well-formedness of a **specification** environment: distinct keys and closed bodies.
`ClosedBodies` is the closedness the pass relation's `shift`/`subst` commutations run on. -/
def LBWfSpec (Γspec : GlobalDeclarations) : Prop :=
  (Γspec.map Prod.fst).Nodup ∧ ClosedBodies Γspec

/--
The emitted environment is the lowered, pruned image of the specification environment.

`defs` relates the two bodies of a key both environments declare — either directly, or
through the block the key belongs to. `defsTotal` is its totality: without it a plain
definition pruned out of `Γ` satisfies `defs` vacuously while the target is stuck at its
`.const`. `sub` is the pruning direction: `Γ` answers no key `Γspec` does not.
-/
structure LowerEnv (Γspec Γ : GlobalDeclarations) : Prop where
  /-- The emitted environment has distinct keys. -/
  keys : (Γ.map Prod.fst).Nodup
  /-- A body declared by both is a `Lower` image, or one member of a lowered block. -/
  defs : ∀ kn b₀ b, DefnDecl Γspec kn b₀ → DefnDecl Γ kn b →
    Lower Γspec b₀ b ∨ ∃ kns bs defs j, LowerFix Γspec kns bs defs ∧
      kns[j]? = some kn ∧ b = .fix defs j
  /-- Every definition that is not a runtime key survives the pruning, as a definition or
      as a member of a lowered block. -/
  defsTotal : ∀ kn b₀, DefnDecl Γspec kn b₀ → ¬ RuntimeKey Γspec kn →
    (∃ b, DefnDecl Γ kn b) ∨
      (∃ (kns : List Kername) (bs : List LBTerm) (defs : List (@FixDef LBTerm)) (j : Nat),
        LowerFix Γspec kns bs defs ∧ kns[j]? = some kn)
  /-- A body-less constant stays body-less, or is pruned. -/
  axioms : ∀ kn, LBTerm.envLookup Γspec kn = some (.constantDecl ⟨none⟩) →
    LBTerm.envLookup Γ kn = some (.constantDecl ⟨none⟩) ∨ LBTerm.envLookup Γ kn = none
  /-- Inductive blocks are carried over unchanged: the target's `constructorArity` and
      `isPropositionalInductive` read the specification's numbers. -/
  inds : ∀ kn d, LBTerm.envLookup Γspec kn = some (.inductiveDecl d) →
    LBTerm.envLookup Γ kn = some (.inductiveDecl d)
  /-- Pruning only removes: every key the emitted environment answers is a key of the
      specification environment. -/
  sub : ∀ kn, LBTerm.envLookup Γ kn ≠ none → LBTerm.envLookup Γspec kn ≠ none
  /-- The emitted bodies are closed. -/
  closed : ClosedBodies Γ

/-- A pass conclusion is stated up to `EnvAgree` on the emitted environment, and
`LowerEnv` is stable under it: nothing in it reads `Γ` except through a lookup. -/
theorem LowerEnv.congr_env {Γspec Γ Γ' : GlobalDeclarations} (h : Γ ≐ Γ')
    (H : LowerEnv Γspec Γ) : LowerEnv Γspec Γ' where
  keys := h.2.2
  defs kn b₀ b h₀ hb := H.defs kn b₀ b h₀ (by rw [DefnDecl, h.1]; exact hb)
  defsTotal kn b₀ h₀ hr := by
    rcases H.defsTotal kn b₀ h₀ hr with ⟨b, hb⟩ | hfix
    · exact .inl ⟨b, by rw [DefnDecl, ← h.1]; exact hb⟩
    · exact .inr hfix
  axioms kn hk := by rw [← h.1]; exact H.axioms kn hk
  inds kn d hk := by rw [← h.1]; exact H.inds kn d hk
  sub kn hk := H.sub kn (by rw [h.1]; exact hk)
  closed kn b hb := H.closed kn b (by rw [DefnDecl, h.1]; exact hb)

/-- The emitted environment carries no entry the program cannot reach — the size claim
pruning makes, stated where a program is in scope. -/
def PrunedFor (Γ : GlobalDeclarations) (t : LBTerm) : Prop :=
  ∀ kn, LBTerm.envLookup Γ kn ≠ none → ReachableFrom Γ t kn

/-! ## Decidable kername equality

`Kername.beq` decides equality, which is what makes a literal environment's keys and
reachability closure computable.
-/

instance : DecidableEq Kername := fun k k' =>
  decidable_of_iff (Kername.beq k k' = true) Kername.beq_iff

/-! ## Non-vacuity of `LowerEnv`

The seven fields are jointly satisfiable on the smallest environment carrying a real
`Lower` step.
-/

/-- One definition with a closed body, kept by the pruning. -/
def boxEnv : GlobalDeclarations := [(rootKername "box", .constantDecl ⟨some .box⟩)]

/-- `boxEnv` is its own lowered image, with every `LowerEnv` field discharged. -/
theorem lowerEnv_boxEnv : LowerEnv boxEnv boxEnv where
  keys := by decide
  defs := by
    intro kn b₀ b h₀ hb
    rw [DefnDecl, boxEnv, LBTerm.envLookup] at h₀ hb
    split at hb
    · split at h₀
      · cases hb; cases h₀; exact .inl .box
      · rename_i hpos hneg; exact absurd hpos hneg
    · simp [LBTerm.envLookup] at hb
  defsTotal := fun _ b₀ h₀ _ => .inl ⟨b₀, h₀⟩
  axioms := by
    intro kn hk
    rw [boxEnv, LBTerm.envLookup] at hk
    split at hk
    · exact absurd hk (by simp)
    · simp [LBTerm.envLookup] at hk
  inds := by
    intro kn d hk
    rw [boxEnv, LBTerm.envLookup] at hk
    split at hk
    · exact absurd hk (by simp)
    · simp [LBTerm.envLookup] at hk
  sub := fun _ hk => hk
  closed := by
    intro kn b hb
    rw [DefnDecl, boxEnv, LBTerm.envLookup] at hb
    split at hb
    · cases hb; trivial
    · simp [LBTerm.envLookup] at hb

/-! ## A four-entry specification environment

The fixture exercises every kind of entry a specification environment holds: an
inductive block, its constructor constant, its `casesOn` eliminator, a recursive
definition and an ι-inert axiom. Source-side facts — `IndInfo`, `CtorOf`, `CasesOnOf`,
`InformativeInd` and the definition's own `Erases` derivation — are hypotheses;
everything λ□-side is literal and computed.
-/

/-- The fixture's inductive type. -/
def demoInd : Name := `Demo.T

/-- The fixture's single, nullary constructor. -/
def demoCtor : Name := `Demo.T.mk

/-- The fixture's `casesOn` eliminator. -/
def demoCases : Name := `Demo.T.casesOn

/-- The fixture's recursive definition. -/
def demoDef : Name := `Demo.loop

/-- The fixture's ι-inert, body-less constant. -/
def demoAx : Name := `Demo.opaqueOp

/-- The fixture's λ□ inductive identifier: the block of `demoInd`, first type. -/
def demoIid : InductiveId := ⟨indBlockKername [demoInd], 0⟩

/-- The fixture's λ□ inductive body: no parameters, one nullary constructor, not
propositional. -/
def demoMib : MutualInductiveBody where
  npars := 0
  bodies := [{ name := "T", ctors := [{ name := "mk", nargs := 0 }], projs := [] }]

/-- The fixture's eliminator body: one dropped motive, one minor, no fields. -/
def demoElim : LBTerm := mkElimBody demoIid 0 1 [0]

/-- The fixture's definition body, as the specification environment holds it: a call to
the eliminator on a recursive call. The recursion is a `.const` here — `.fix` is what the
lowering makes of it. -/
def demoBody : LBTerm :=
  .lambda .anon (.app (.const (toKername demoCases))
    (.app (.const (toKername demoDef)) (.app (.const (toKername demoAx)) (.bvar 0))))

/-- The fixture's specification environment. -/
def demoEnv : GlobalDeclarations :=
  [(demoIid.mutualBlockName, .inductiveDecl demoMib),
   (toKername demoCtor, .constantDecl ⟨some (.construct demoIid 0 [])⟩),
   (toKername demoCases, .constantDecl ⟨some demoElim⟩),
   (toKername demoDef, .constantDecl ⟨some demoBody⟩),
   (toKername demoAx, .constantDecl ⟨none⟩)]

/-- The fixture's program: the recursive definition itself. -/
def demoProg : LBTerm := .const (toKername demoDef)

/-- The source-side facts the fixture's entries are justified by. Everything a
`VEnv` cannot be hand-built to exhibit without a full kernel declaration — the inductive
block, its constructor, its eliminator constant and the definition's own erasure — enters
here. -/
structure DemoSource (env : VEnv) (bo : Name → Option Expr) : Prop where
  /-- The block of `demoInd`, at no parameters and one nullary constructor. -/
  ind : IndInfo env demoInd demoIid 0 [0]
  /-- `demoCtor` is that block's constructor `0`. -/
  ctor : CtorOf env demoCtor demoInd 0
  /-- `demoCases` is its `casesOn` eliminator. -/
  cases : CasesOnOf env demoInd (toKername demoCases)
  /-- The block is informative, so the eliminator may be declared. -/
  informative : InformativeInd env demoInd
  /-- `demoDef` has a compiler body erasing to `demoBody`. -/
  defn : ∃ (ci : VConstant) (Us : List Name) (src : Expr),
    env.constants demoDef = some ci ∧ Us.length = ci.uvars ∧
      bo demoDef = some src ∧ Erases env Us [] src demoBody
  /-- `demoAx` is a constant with no compiler body and no ι rule keyed on it. -/
  ax : ∃ ci : VConstant, env.constants demoAx = some ci ∧ bo demoAx = none ∧
    IotaInert env demoAx

/-- The fixture's keys are distinct. -/
theorem demoEnv_keys : ((demoEnv.map Prod.fst).Nodup) := by decide

/-- Every entry of the fixture is justified, one per `ErasesDecl` arm. -/
theorem demoEnv_decls {env : VEnv} {bo : Name → Option Expr} (h : DemoSource env bo) :
    ∀ kn d, LBTerm.envLookup demoEnv kn = some d → ErasesDecl env bo kn d := by
  obtain ⟨hind, hctor, hcases, hinf, ⟨ci, Us, src, hc, huv, hbo, hb⟩,
    cia, hca, hnoa, hpata⟩ := h
  intro kn d hd
  have hmem := envLookup_mem hd
  simp only [demoEnv, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact .ind hind ⟨rfl, _, rfl, rfl, rfl⟩
  · exact .ctor hctor hind
  · exact .elim hind hcases hinf (body := demoElim) .cases
  · exact .defn hc huv hbo hb
  · exact .ax hca hnoa hpata

/-- The fixture's program reaches only declared kernames: the axiom, the eliminator and
the definition itself. -/
theorem demoEnv_deps :
    ∀ kn, ReachableFrom demoEnv demoProg kn → (LBTerm.envLookup demoEnv kn).isSome := by
  intro kn h
  have hr : reachRefs demoEnv demoProg demoEnv.length
      = [toKername demoAx, toKername demoCases, toKername demoDef] := rfl
  unfold ReachableFrom kernameElem at h
  rw [hr] at h
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true] at h
  rcases h with h | h | h <;> rw [Kername.eq_of_beq h] <;> decide

/-- The fixture is a specification environment for its own program. -/
theorem demoEnv_erasesEnv {env : VEnv} {bo : Name → Option Expr} (h : DemoSource env bo) :
    ErasesEnv env bo demoEnv demoProg :=
  .mk demoEnv_keys (demoEnv_decls h) demoEnv_deps

example {env : VEnv} {bo : Name → Option Expr} (h : DemoSource env bo) :
    ErasesEnv env bo demoEnv demoProg := demoEnv_erasesEnv h

end LeanToLambdaBox
