import LeanToLambdaBox.LowerFix
import LeanToLambdaBox.Output
import LeanToLambdaBox.SourceEval
import LeanToLambdaBox.Supported

/-!
# `ErasesEnv` — the dependency-selective environment erasure

`ErasesEnv env bo Γspec t` relates a source environment to the **specification** λ□
environment `Γspec` a program `t` is read against: its keys are distinct, every
declaration it holds is justified by `ErasesDecl`, every kername `t` reaches through
`Γspec` is present, and every compiler body a reached constant carries erases to the entry
`Γspec` holds for it. It is `erases_deps` of Sozeau et al.: bottom-up and selective, not a
pointwise image of the whole source environment.

`ErasesDecl` has one arm per kind of entry the eraser emits — a definition whose body is
the compiler's, an inert axiom, an inductive block, and a `casesOn` eliminator. There is no
constructor arm: a constructor constant is not declared, it is `Erases.ctor`'s node, and the
one constructor-bodied entry the five programs hold is a *definition*.

`LowerEnv Γspec Γ` relates the specification environment to the emitted one and carries the
pass layer's own environment well-formedness on `Γspec`, which the `Lower` metatheory the
simulation consumes needs.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-! ## Source-side declaration facts

What `ErasesDecl` reads off the source environment. A `VEnv` stores constants, defeqs and
ι patterns; a declaration *block* lives in the `VEnv.WF'` declaration list, which is why
the inductive-shaped facts go through `IndInfo`.
-/

/-- `c` is a `casesOn`-like constant of `I`, declared in `env`, at the λ□ kername `kn`.
Sparse `casesOn` constants are named after the enclosing function, are mistranslated by the
eraser and are excluded from the fragment, so they are not here. -/
def CasesOnOf' (env : VEnv) (I c : Name) (kn : Kername) : Prop :=
  ∃ ci : VConstant, env.constants c = some ci ∧ isCasesOnName c = true ∧
    c.getPrefix = I ∧ kn = toKername c

/-- `kn` is the λ□ kername of an eliminator of `I`, the constant left existential. -/
def CasesOnOf (env : VEnv) (I : Name) (kn : Kername) : Prop :=
  ∃ c : Name, CasesOnOf' env I c kn

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
  /-- An inert constant: declared, with no compiler body. A source derivation cannot step
      at it, so the body-less entry is faithful. -/
  | ax {c ci} (h : env.constants c = some ci) (hno : bo c = none) :
      ErasesDecl env bo (toKername c) (.constantDecl ⟨none⟩)
  /-- An inductive block, keyed on the block kername `IndInfo` pins. -/
  | ind {I iid np nfs mib} (h : IndInfo env I iid np nfs) (hm : IndBodyOf iid np nfs mib) :
      ErasesDecl env bo iid.mutualBlockName (.inductiveDecl mib)
  /-- A `casesOn` eliminator of an **informative** inductive. An eliminator of a
      non-informative one has no entry: its emitted `.case` is stuck on every value a run
      produces, so declaring it would claim a correctness it does not have. `hsh` is the
      eliminator's source-side segmentation, which makes the emitted node's shape a fact
      about the source theory rather than an assumption; `hco` is the constant's own
      reading, the positive fact `Erases.const` takes, and it is what a saturated
      eliminator spine is refuted as a value by. -/
  | elim {I c kn iid np dp nfs body} (hi : IndInfo env I iid np nfs)
      (he : CasesOnOf' env I c kn) (hinf : InformativeInd env I)
      (hsh : CasesOnShape env c I dp nfs.length) (hco : ConstOrigin env c)
      (hb : ElimBody iid np dp nfs body) :
      ErasesDecl env bo kn (.constantDecl ⟨some body⟩)

/-! ## `ErasesEnv` -/

/--
The specification environment of a program, `erases_deps` of Sozeau et al.

Four clauses, written out rather than elided: the keys are distinct, so a shadowing
entry cannot retarget a lookup; every declaration the environment answers with is
justified by `ErasesDecl`; every kername `t` reaches is answered at all; and every
compiler body a reached constant carries erases to the body the environment holds.
-/
inductive ErasesEnv (env : VEnv) (bo : Name → Option Expr) :
    GlobalDeclarations → LBTerm → Prop
  /-- The only clause: the four conditions, at one environment and one program. -/
  | mk {Γspec : GlobalDeclarations} {t : LBTerm}
      (keys : (Γspec.map Prod.fst).Nodup)
      (decls : ∀ kn d, LBTerm.envLookup Γspec kn = some d → ErasesDecl env bo kn d)
      (deps : ∀ kn, ReachableFrom Γspec t kn → (LBTerm.envLookup Γspec kn).isSome)
      -- `defns` is the δ arm's own premise, in the δ arm's own direction: `decls` runs
      -- the other way — entry implies justified — and at a tabled constant does not even
      -- say which arm justifies the entry, so it cannot supply this
      (defns : ∀ c b, bo c = some b → ReachableFrom Γspec t (toKername c) →
        ∃ b₀, LBTerm.envLookup Γspec (toKername c) = some (.constantDecl ⟨some b₀⟩) ∧
          ∀ Us' ups us, Erases env Us' [] (b.instantiateLevelParams ups us) b₀) :
      ErasesEnv env bo Γspec t

/-- The keys of a specification environment are distinct. -/
theorem ErasesEnv.keys {env : VEnv} {bo : Name → Option Expr} {Γspec : GlobalDeclarations}
    {t : LBTerm} (h : ErasesEnv env bo Γspec t) : (Γspec.map Prod.fst).Nodup := by
  cases h with | mk k _ _ _ => exact k

/-- Every declaration a specification environment answers with is `ErasesDecl`-justified. -/
theorem ErasesEnv.decls {env : VEnv} {bo : Name → Option Expr} {Γspec : GlobalDeclarations}
    {t : LBTerm} (h : ErasesEnv env bo Γspec t) :
    ∀ kn d, LBTerm.envLookup Γspec kn = some d → ErasesDecl env bo kn d := by
  cases h with | mk _ d _ _ => exact d

/-- Every kername the program reaches is declared. -/
theorem ErasesEnv.deps {env : VEnv} {bo : Name → Option Expr} {Γspec : GlobalDeclarations}
    {t : LBTerm} (h : ErasesEnv env bo Γspec t) :
    ∀ kn, ReachableFrom Γspec t kn → (LBTerm.envLookup Γspec kn).isSome := by
  cases h with | mk _ _ d _ => exact d

/-- Every compiler body a reached constant carries erases to the entry the environment
holds for it. -/
theorem ErasesEnv.defns {env : VEnv} {bo : Name → Option Expr} {Γspec : GlobalDeclarations}
    {t : LBTerm} (h : ErasesEnv env bo Γspec t) :
    ∀ c b, bo c = some b → ReachableFrom Γspec t (toKername c) →
      ∃ b₀, LBTerm.envLookup Γspec (toKername c) = some (.constantDecl ⟨some b₀⟩) ∧
        ∀ Us' ups us, Erases env Us' [] (b.instantiateLevelParams ups us) b₀ := by
  cases h with | mk _ _ _ d => exact d

/-! ## Lookup plumbing

`LBTerm.envLookup` answers with the first `Kername.beq`-matching entry, so a literal
environment is decided key by key; `envLookup_mem` is `Output.lean`'s.
-/

/-- The hit branch of a lookup. -/
theorem envLookup_cons_self {k : Kername} {d : GlobalDecl} {rest : GlobalDeclarations} :
    LBTerm.envLookup ((k, d) :: rest) k = some d := by
  rw [LBTerm.envLookup, if_pos (Kername.beq_self k)]

/-- The miss branch of a lookup. -/
theorem envLookup_cons_ne {k kn : Kername} {d : GlobalDecl} {rest : GlobalDeclarations}
    (h : k ≠ kn) : LBTerm.envLookup ((k, d) :: rest) kn = LBTerm.envLookup rest kn := by
  rw [LBTerm.envLookup, if_neg]
  exact fun hb => h (Kername.eq_of_beq hb)

/-! ## The two environment-level predicates a pass is stated against -/

/-- Well-formedness of a **specification** environment: distinct keys and closed bodies.
`ClosedBodies` is the closedness the pass relation's `shift`/`subst` commutations run on. -/
def LBWfSpec (Γspec : GlobalDeclarations) : Prop :=
  (Γspec.map Prod.fst).Nodup ∧ ClosedBodies Γspec

/-- The emitted environment is the lowered, pruned image of the specification environment,
which is itself well formed for the pass. `defs` relates two bodies of a key both declare;
`defsTotal` is its totality, without which a definition pruned out of `Γ` satisfies `defs`
vacuously while the target is stuck at its `.const`; `sub` is the pruning direction.
`specClosed` and `specBlocks` are what the `Lower` metatheory the simulation consumes needs
of `Γspec`, and they are clauses here because this is where facts about `Γspec` live. -/
structure LowerEnv (Γspec Γ : GlobalDeclarations) : Prop where
  /-- The emitted environment has distinct keys. -/
  keys : (Γ.map Prod.fst).Nodup
  /-- A body declared by both is a `Lower` image, or one member of a lowered block. -/
  defs : ∀ kn b₀ b, DefnDecl Γspec kn b₀ → DefnDecl Γ kn b →
    Lower Γspec b₀ b ∨ ∃ kns bs defs j, LowerFix Γspec kns bs defs ∧
      kns[j]? = some kn ∧ b = .fix defs j
  /-- Every definition that is not a runtime key survives the pruning as a definition.
      The eraser declares every definition, a recursive one with a `.fix` body, and
      `Lower.const` relates a block member to its own `.const`, so a weaker clause would
      strand that image. -/
  defsTotal : ∀ kn b₀, DefnDecl Γspec kn b₀ → ¬ RuntimeKey Γspec kn → ∃ b, DefnDecl Γ kn b
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
  /-- The specification bodies are closed: `Lower.subst_comm`'s hypothesis, spent at every
      β, ζ and ι step. -/
  specClosed : ClosedBodies Γspec
  /-- Every member body of every block the pass builds out of `Γspec` is a λ: what the
      `Lower.source_*` inversion kit takes, and what excludes a `.fix` image of a
      constructor value. -/
  specBlocks : BlockBodiesLambda Γspec

/-! ## Non-vacuity of `LowerEnv`

The nine fields are jointly satisfiable on the smallest environment carrying a real
`Lower` step. The body is a λ, which is what `specBlocks` asks of a block member.
-/

/-- One definition with a closed λ-body, kept by the pruning. -/
def idEnv : GlobalDeclarations :=
  [(rootKername "id", .constantDecl ⟨some (.lambda .anon (.bvar 0))⟩)]

/-- `idEnv` is its own lowered image, with every `LowerEnv` field discharged. -/
theorem lowerEnv_idEnv : LowerEnv idEnv idEnv where
  keys := by decide
  defs := by
    intro kn b₀ b h₀ hb
    rw [DefnDecl, idEnv, LBTerm.envLookup] at h₀ hb
    split at hb
    · split at h₀
      · cases hb; cases h₀; exact .inl (.lambda (.bvar 0))
      · rename_i hpos hneg; exact absurd hpos hneg
    · simp [LBTerm.envLookup] at hb
  defsTotal := fun _ b₀ h₀ _ => ⟨b₀, h₀⟩
  axioms := by
    intro kn hk
    rw [idEnv, LBTerm.envLookup] at hk
    split at hk
    · exact absurd hk (by simp)
    · simp [LBTerm.envLookup] at hk
  inds := by
    intro kn d hk
    rw [idEnv, LBTerm.envLookup] at hk
    split at hk
    · exact absurd hk (by simp)
    · simp [LBTerm.envLookup] at hk
  sub := fun _ hk => hk
  closed := by
    intro kn b hb
    rw [DefnDecl, idEnv, LBTerm.envLookup] at hb
    split at hb
    · cases hb; exact Nat.zero_lt_one
    · simp [LBTerm.envLookup] at hb
  specClosed := by
    intro kn b hb
    rw [DefnDecl, idEnv, LBTerm.envLookup] at hb
    split at hb
    · cases hb; exact Nat.zero_lt_one
    · simp [LBTerm.envLookup] at hb
  specBlocks := by
    intro kns bs bs' ids defs hblock j hj
    have hd := hblock.hdecl j hj
    rw [DefnDecl, idEnv, LBTerm.envLookup] at hd
    split at hd
    · have hbs : bs[j]! = LBTerm.lambda .anon (.bvar 0) := by simpa using hd.symm
      rw [hbs]; rfl
    · simp [LBTerm.envLookup] at hd

/-! ## What `specBlocks` costs

`BlockBodiesLambda` reads *every* declared body as a possible block member, so the clause
is false of any specification environment holding a definition whose body is not a λ. The
five programs all hold one — `Unit.unit ↦ .construct PUnit 0`, and every nullary definition
besides — so no such environment has a `LowerEnv` image. The repair, if the simulation
needs one, is `BlockBodiesLambda`'s own, in `Lower.lean`.
-/

/-- The block of the one-entry counterexample environment. -/
def ctorBodyIid : InductiveId := ⟨rootKername "U", 0⟩

/-- One definition whose body is a nullary constructor node — `Unit.unit`'s shape in every
one of the five programs' specification environments. -/
def ctorBodyEnv : GlobalDeclarations :=
  [(rootKername "u", .constantDecl ⟨some (.construct ctorBodyIid 0 [])⟩)]

/-- That single definition is a one-member block of the pass: every `LowerBlock` field is
discharged, with the constructor node as the member body. -/
theorem ctorBodyEnv_block :
    LowerBlock ctorBodyEnv [rootKername "u"] [.construct ctorBodyIid 0 []]
      [.construct ctorBodyIid 0 []] [⟨`x⟩]
      [{ name := .anon, body := closeFix [⟨`x⟩] 0 (.construct ctorBodyIid 0 []),
         principalArgIdx := 0 }] where
  hb := rfl
  hb' := rfl
  hd := rfl
  hnd := by simp
  hids := by simp
  hilen := rfl
  hfresh := by
    intro x hx i hi
    have : i = 0 := by simp at hi; omega
    subst this
    simp [hasFVarArgs]
  hrarg := by intro d hd; simp at hd; subst hd; rfl
  hdecl := by
    intro i hi
    have : i = 0 := by simp at hi; omega
    subst this; rfl
  hlow := by
    intro i hi
    have : i = 0 := by simp at hi; omega
    subst this
    exact .construct rfl (by intro j hj; simp at hj)
  hcl := by
    intro i hi
    have : i = 0 := by simp at hi; omega
    subst this
    exact ⟨.construct ctorBodyIid 0 [], .construct rfl (by intro j hj; simp at hj), rfl⟩

/-- A constructor-bodied definition refutes `BlockBodiesLambda`. -/
theorem not_blockBodiesLambda_ctorBodyEnv : ¬ BlockBodiesLambda ctorBodyEnv := by
  intro h
  have := h _ _ _ _ _ ctorBodyEnv_block 0 (by simp)
  simp [isLambda] at this

/-- **What the clause excludes.** A specification environment declaring a constructor-bodied
definition has no `LowerEnv` image at all, for any emitted environment. -/
theorem lowerEnv_needs_lambda_bodies {Γ : GlobalDeclarations} : ¬ LowerEnv ctorBodyEnv Γ :=
  fun h => not_blockBodiesLambda_ctorBodyEnv h.specBlocks

/-! ## A four-entry specification environment

The fixture exercises every kind of entry a specification environment holds: an
inductive block, its constructor constant, its `casesOn` eliminator, a recursive
definition and a body-less axiom. Source-side facts — `IndInfo`, `CtorOf`, `CasesOnOf`,
`InformativeInd` and the definition's own `Erases` derivation — are hypotheses;
everything λ□-side is literal and computed.
-/

/-- The fixture's inductive type. -/
def demoInd : Name := `DemoT

/-- The fixture's single, nullary constructor. -/
def demoCtor : Name := `DemoT.mk

/-- The fixture's `casesOn` eliminator. -/
def demoCases : Name := `DemoT.casesOn

/-- The fixture's recursive definition. -/
def demoDef : Name := `Demo.loop

/-- The fixture's body-less constant. -/
def demoAx : Name := `Demo.opaqueOp

/-- The fixture's λ□ inductive identifier: the block of `demoInd`, first type. The block
kername is spelled as the literal `indBlockKername [demoInd]` evaluates to, because
`Name.toString` does not reduce definitionally and reachability through a `.case` node now
computes with the block kername. -/
def demoIid : InductiveId := ⟨rootKername "DemoT", 0⟩

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
block, the constructor the fixture's definition unfolds to, the eliminator constant and the
definition's own erasure — enters here. -/
structure DemoSource (env : VEnv) (bo : Name → Option Expr) : Prop where
  /-- The block of `demoInd`, at no parameters and one nullary constructor. -/
  ind : IndInfo env demoInd demoIid 0 [0]
  /-- `demoCtor` is a *definition* whose compiler body is a constructor constant of the
      block, as `Unit.unit`'s is `PUnit.unit`: the entry is justified by `defn` through
      `Erases.ctor`, which is why `ErasesDecl` needs no constructor arm. -/
  ctorDefn : ∃ (ci : VConstant) (Us : List Name) (c : Name) (us : List Level),
    env.constants demoCtor = some ci ∧ Us.length = ci.uvars ∧
      bo demoCtor = some (.const c us) ∧ CtorOf env c demoInd 0
  /-- `demoCases` is `demoInd`'s `casesOn` eliminator. -/
  cases : CasesOnOf' env demoInd demoCases (toKername demoCases)
  /-- The block is informative, so the eliminator may be declared. -/
  informative : InformativeInd env demoInd
  /-- The eliminator's source-side segmentation: one dropped argument before the major
      premise, one minor. It is what pins the emitted `.case` node's shape. -/
  casesShape : CasesOnShape env demoCases demoInd 1 1
  /-- The eliminator constant is declared as a definition. -/
  casesOrigin : ConstOrigin env demoCases
  /-- `demoDef` has a compiler body erasing to `demoBody`. -/
  defn : ∃ (ci : VConstant) (Us : List Name) (src : Expr),
    env.constants demoDef = some ci ∧ Us.length = ci.uvars ∧
      bo demoDef = some src ∧ Erases env Us [] src demoBody
  /-- `demoDef`'s compiler body erases to the same entry at every level scope and
      instantiation: `ErasesEnv.defns`, the δ arm's own premise. -/
  defnStable : ∀ c b, bo c = some b → toKername c = toKername demoDef →
    ∀ Us' ups us, Erases env Us' [] (b.instantiateLevelParams ups us) demoBody
  /-- `demoAx` is a constant with no compiler body. -/
  ax : ∃ ci : VConstant, env.constants demoAx = some ci ∧ bo demoAx = none
  /-- No constant carrying a compiler body is named by the block's, the eliminator's or the
      axiom's kername. `toKername` is not injective, so this is a fact about kernames. -/
  inert : ∀ c b, bo c = some b → toKername c ≠ toKername demoCases ∧
    toKername c ≠ toKername demoAx ∧ toKername c ≠ demoIid.mutualBlockName

/-- The fixture's keys are distinct. -/
theorem demoEnv_keys : ((demoEnv.map Prod.fst).Nodup) := by decide

/-- Every entry of the fixture is justified, one per `ErasesDecl` arm. -/
theorem demoEnv_decls {env : VEnv} {bo : Name → Option Expr} (h : DemoSource env bo) :
    ∀ kn d, LBTerm.envLookup demoEnv kn = some d → ErasesDecl env bo kn d := by
  obtain ⟨hind, ⟨cic, Usc, cn, us, hcc, huvc, hboc, hctor⟩, hcases, hinf, hsh, hco,
    ⟨ci, Us, src, hc, huv, hbo, hb⟩, _, ⟨cia, hca, hnoa⟩, _⟩ := h
  intro kn d hd
  have hmem := envLookup_mem hd
  simp only [demoEnv, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact .ind hind ⟨rfl, _, rfl, rfl, rfl⟩
  · exact .defn hcc huvc hboc (.ctor hctor hind)
  · exact .elim hind hcases hinf hsh hco (body := demoElim) .cases
  · exact .defn hc huv hbo hb
  · exact .ax hca hnoa

/-- The fixture's program reaches only declared kernames: the axiom, the block the
eliminator's `.case` node reads, the eliminator and the definition itself. -/
theorem demoEnv_deps :
    ∀ kn, ReachableFrom demoEnv demoProg kn → (LBTerm.envLookup demoEnv kn).isSome := by
  intro kn h
  have hr : reachRefs demoEnv demoProg demoEnv.length
      = [demoIid.mutualBlockName, toKername demoAx, toKername demoCases,
         toKername demoDef] := rfl
  unfold ReachableFrom kernameElem at h
  rw [hr] at h
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true] at h
  rcases h with h | h | h | h <;> rw [Kername.eq_of_beq h] <;> decide

/-- Every compiler body the fixture's program reaches erases to the entry the fixture
holds: only `demoDef`'s kername is both reached and bodied. -/
theorem demoEnv_defns {env : VEnv} {bo : Name → Option Expr} (h : DemoSource env bo) :
    ∀ c b, bo c = some b → ReachableFrom demoEnv demoProg (toKername c) →
      ∃ b₀, LBTerm.envLookup demoEnv (toKername c) = some (.constantDecl ⟨some b₀⟩) ∧
        ∀ Us' ups us, Erases env Us' [] (b.instantiateLevelParams ups us) b₀ := by
  intro c b hbo hr
  obtain ⟨hnc, hna, hnb⟩ := h.inert c b hbo
  have hlist : reachRefs demoEnv demoProg demoEnv.length
      = [demoIid.mutualBlockName, toKername demoAx, toKername demoCases,
         toKername demoDef] := rfl
  unfold ReachableFrom kernameElem at hr
  rw [hlist] at hr
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true] at hr
  rcases hr with hk | hk | hk | hk
  · exact absurd (Kername.eq_of_beq hk) hnb
  · exact absurd (Kername.eq_of_beq hk) hna
  · exact absurd (Kername.eq_of_beq hk) hnc
  · refine ⟨demoBody, ?_, h.defnStable c b hbo (Kername.eq_of_beq hk)⟩
    rw [Kername.eq_of_beq hk]
    rfl

/-- The fixture is a specification environment for its own program. -/
theorem demoEnv_erasesEnv {env : VEnv} {bo : Name → Option Expr} (h : DemoSource env bo) :
    ErasesEnv env bo demoEnv demoProg :=
  .mk demoEnv_keys (demoEnv_decls h) demoEnv_deps (demoEnv_defns h)

example {env : VEnv} {bo : Name → Option Expr} (h : DemoSource env bo) :
    ErasesEnv env bo demoEnv demoProg := demoEnv_erasesEnv h

end LeanToLambdaBox
