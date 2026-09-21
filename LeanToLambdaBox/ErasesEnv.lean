import LeanToLambdaBox.LowerFix
import LeanToLambdaBox.Output
import LeanToLambdaBox.SourceEval
import LeanToLambdaBox.Supported

/-!
# `ErasesEnv` — the dependency-selective environment erasure

`ErasesEnv env bo lp Γspec t` relates a source environment to the **specification** λ□
environment `Γspec` a program `t` is read against. It is `erases_deps` of Sozeau et al.:
bottom-up, selective, and stated in `erases_deps`' own direction — every clause reads *the
source declares X → the target declares X' → X' is the erasure of X*, per kind of
declaration. There is no clause running the other way, from an entry to a justification:
the arms of the simulation hold a source declaration and ask what the environment holds
for it.

Seven clauses. `keys` is `wf Σ'`'s `fresh_global` half, so a shadowing entry cannot
retarget `Lower`; `deps` is the dependency closure; `tabled`, `defns`, `axioms`, `blocks`
and `elims` are the per-kind readings. There is no constructor clause: a constructor
constant has no entry, and what a constructor value's arity is read off is the **block**,
which `blocks` gives at the block kername a `.construct` node already reaches.

`IndCovered` is the same content at one type former, and `SpecContent` bundles the five
`Γspec`-only clauses with the entry's presence in place of the program's reachability —
which is what makes them fixed for a run and is how the registry supplies them.

`LowerEnv Γspec Γ` relates the specification environment to the emitted one and carries the
pass layer's own environment well-formedness on `Γspec`, which the `Lower` metatheory the
simulation consumes needs.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-! ## The emitted propositional flag, against the model -/

/-- **The flag `iid`'s registered body carries is sound against the model**: a body the
eraser marks propositional belongs to an inductive whose declared arity ends in `Prop` at
every valuation. MetaRocq's `erases_one_inductive_body` states the flag as an equality,
`ind_propositional = isPropositionalArity ind_type`
(`../metarocq/erasure/theories/Extract.v:276`); this is the half of that equality a consumer
spends, through `propositional_false_of_informative`, and the half
`ErasureSpec.propositionalInd_of_arity` proves. The converse is refuted by an arity whose
result sort sits under a `let` (`doc/rework/03-DEV-FIX.md`, F-ARITYLET).

It is no clause of `IndBodyOf`, which carries no model environment:
`Erasure.register_inductive` computes the flag on every inductive it registers —
`Erasure.recursorRealizer` reaches it at `Eq`/`And`/`False` — so `= false` is not a fact
about emitted output. -/
def IndFlagSound (env : VEnv) (I : Name) (iid : InductiveId)
    (mib : MutualInductiveBody) : Prop :=
  ∀ oib, mib.bodies[iid.idx]? = some oib → oib.propositional = true → PropositionalInd env I

/-- **The `= false` the ι and projection arms read.** An informative inductive is not
propositional (`propositional_false_of_informative`), so its registered body carries the flag
unset — which is what `WcbvEval.iota` and `WcbvEval.proj` test
(`Semantics/Eval.lean:147`, `:183`). -/
theorem IndFlagSound.notPropositional {env : VEnv} {I : Name} {iid : InductiveId}
    {mib : MutualInductiveBody} {oib : OneInductiveBody} (h : IndFlagSound env I iid mib)
    (hoib : mib.bodies[iid.idx]? = some oib) (hinf : InformativeInd env I) :
    oib.propositional = false :=
  propositional_false_of_informative (h oib hoib) hinf

/-! ## `ErasesEnv` -/

/--
The specification environment of a program, `erases_deps` of Sozeau et al.

`bo` is the **compiler** body table, the one `SEval.deltaC` reads, so `defns` and the source
δ rule unfold the same term; `lp` is the level column beside it, the scope a tabled body is
erased at — `erases_constant_body (Σ, cst_universes cb)`, `Extract.v:264`.
-/
inductive ErasesEnv (env : VEnv) (bo : Name → Option Expr) (lp : Name → List Name) :
    GlobalDeclarations → LBTerm → Prop
  /-- The only clause: the seven conditions, at one environment and one program. -/
  | mk {Γspec : GlobalDeclarations} {t : LBTerm}
      (keys : (Γspec.map Prod.fst).Nodup)
      (deps : ∀ kn, ReachableFrom Γspec t kn → (LBTerm.envLookup Γspec kn).isSome)
      (tabled : ∀ c b, bo c = some b → ConstOrigin env c)
      (defns : ∀ c b, bo c = some b → ReachableFrom Γspec t (toKername c) →
        ∃ b₀, LBTerm.envLookup Γspec (toKername c) = some (.constantDecl ⟨some b₀⟩) ∧
          Erases env (lp c) [] b b₀)
      (axioms : ∀ c, bo c = none → ConstOrigin env c → isCasesOnName c = false →
        ReachableFrom Γspec t (toKername c) →
        LBTerm.envLookup Γspec (toKername c) = some (.constantDecl ⟨none⟩))
      (blocks : ∀ {I : Name} {iid : InductiveId} {np : Nat} {nfs : List Nat},
        IndInfo env I iid np nfs → ReachableFrom Γspec t iid.mutualBlockName →
        IndDeclOf env I ∧ ∃ mib,
          LBTerm.envLookup Γspec iid.mutualBlockName = some (.inductiveDecl mib) ∧
          IndBodyOf iid np nfs mib ∧ IndFlagSound env I iid mib)
      (elims : ∀ {c I : Name} {dp nm : Nat},
        CasesOnShape env c I dp nm → InformativeInd env I → ConstOrigin env c →
        ReachableFrom Γspec t (toKername c) →
        ∃ iid np nfs, ElimDecl Γspec (toKername c) iid np dp nfs ∧
          IndInfo env I iid np nfs ∧ nfs.length = nm) :
      ErasesEnv env bo lp Γspec t

variable {env : VEnv} {bo : Name → Option Expr} {lp : Name → List Name}
  {Γspec : GlobalDeclarations} {t : LBTerm}

/-- The keys of a specification environment are distinct. -/
theorem ErasesEnv.keys (h : ErasesEnv env bo lp Γspec t) : (Γspec.map Prod.fst).Nodup := by
  cases h with | mk k _ _ _ _ _ _ => exact k

/-- Every kername the program reaches is declared. -/
theorem ErasesEnv.deps (h : ErasesEnv env bo lp Γspec t) :
    ∀ kn, ReachableFrom Γspec t kn → (LBTerm.envLookup Γspec kn).isSome := by
  cases h with | mk _ d _ _ _ _ _ => exact d

/-- `erases_deps`' `declared_constant Σ kn cb`: a constant the compiler table defines is a
plain constant of `env`. No reachability trigger — the reading it refutes is at a constant
the erasure emits no key for, so there is no occurrence to trigger on. -/
theorem ErasesEnv.tabled (h : ErasesEnv env bo lp Γspec t) :
    ∀ c b, bo c = some b → ConstOrigin env c := by
  cases h with | mk _ _ d _ _ _ _ => exact d

/-- Every compiler body a reached constant carries erases, **at the declaration's own level
scope**, to the entry the environment holds for it: the δ arm's own premise, in the δ arm's own
direction. The instantiated reading the δ rule unfolds at is derived where it is spent, by
`Erases.instantiateLevelParams_of_stepDefeq`, as `erases_subst_instance_decl` is in
`../metarocq/erasure/theories/ErasureCorrectness.v:176`. -/
theorem ErasesEnv.defns (h : ErasesEnv env bo lp Γspec t) :
    ∀ c b, bo c = some b → ReachableFrom Γspec t (toKername c) →
      ∃ b₀, LBTerm.envLookup Γspec (toKername c) = some (.constantDecl ⟨some b₀⟩) ∧
        Erases env (lp c) [] b b₀ := by
  cases h with | mk _ _ _ d _ _ _ => exact d

/-- A reached key whose constant has no compiler body — and is not an eliminator, whose
entry is the `ElimBody` — is declared body-less. Without it the environment may hold
`⟨some junk⟩` where the source cannot step and the target δ-unfolds. -/
theorem ErasesEnv.axioms (h : ErasesEnv env bo lp Γspec t) :
    ∀ c, bo c = none → ConstOrigin env c → isCasesOnName c = false →
      ReachableFrom Γspec t (toKername c) →
      LBTerm.envLookup Γspec (toKername c) = some (.constantDecl ⟨none⟩) := by
  cases h with | mk _ _ _ _ d _ _ => exact d

/-- `erases_deps`' `tConstruct`/`tCase`/`tProj` clause: `declared_inductive Σ` — the
`IndDeclOf` conjunct, which `IndInfo` does not give, since it exhibits a block below `env` —
and `declared_inductive Σ'` with the arity data the target reads, beside `IndFlagSound`, the
propositional flag's equation against the model. -/
theorem ErasesEnv.blocks (h : ErasesEnv env bo lp Γspec t) {I : Name} {iid : InductiveId}
    {np : Nat} {nfs : List Nat} (hi : IndInfo env I iid np nfs)
    (hr : ReachableFrom Γspec t iid.mutualBlockName) :
    IndDeclOf env I ∧ ∃ mib,
      LBTerm.envLookup Γspec iid.mutualBlockName = some (.inductiveDecl mib) ∧
      IndBodyOf iid np nfs mib ∧ IndFlagSound env I iid mib := by
  cases h with | mk _ _ _ _ _ d _ => exact d hi hr

/-- The `tCase` clause at the Lean eliminator **constant** the pass consumes: at a reached
`casesOn` of a relevant inductive the entry is that eliminator's. Relevance is a hypothesis,
not a conclusion — the registry declares no eliminator of a non-informative inductive, and
`SEval.iota`'s own `hinf` is what supplies it at the arm. -/
theorem ErasesEnv.elims (h : ErasesEnv env bo lp Γspec t) {c I : Name} {dp nm : Nat}
    (hsh : CasesOnShape env c I dp nm) (hinf : InformativeInd env I)
    (hco : ConstOrigin env c) (hr : ReachableFrom Γspec t (toKername c)) :
    ∃ iid np nfs, ElimDecl Γspec (toKername c) iid np dp nfs ∧
      IndInfo env I iid np nfs ∧ nfs.length = nm := by
  cases h with | mk _ _ _ _ _ _ d => exact d hsh hinf hco hr

/-! ## Coverage of one inductive, and the `Γspec`-only clauses

A reached key carrying an eliminator's declaration belongs to a `casesOn` constant with no
compiler body. That is `defns` and `axioms` together — no erasure image is an `ElimBody`,
and a body-less non-eliminator's entry is `⟨none⟩` — and it is a theorem, not a clause:
`ErasesEnv.runtimeKey_isCasesOn`, in `ErasesCorrect/Steps.lean`, where `erases_ne_elimBody`
is in scope.
-/

/-- `Γspec` covers the inductive `n`: it declares `n`'s block, with the numbers the target
semantics reads, and — when `n` is informative — its `casesOn` eliminator. These are
`ErasesEnv`'s two inductive clauses at one name, which is the granularity a registration
step establishes. -/
structure IndCovered (env : VEnv) (Γspec : GlobalDeclarations) (n : Name) : Prop where
  /-- The block declaration, at the block kername `IndInfo` names, together with `n`'s own
      declaration in `env` and the propositional flag's equation against the model. -/
  block : ∀ iid np nfs, IndInfo env n iid np nfs →
    IndDeclOf env n ∧ ∃ mib,
      LBTerm.envLookup Γspec iid.mutualBlockName = some (.inductiveDecl mib) ∧
      IndBodyOf iid np nfs mib ∧ IndFlagSound env n iid mib
  /-- The eliminator of an informative `n` is declared, at the segmentation `n`'s block
      fixes. `isCasesOnName c` and `c.getPrefix = n` pin one name, so this quantifier ranges
      over one constant. -/
  elims : ∀ c dp nm, CasesOnShape env c n dp nm → InformativeInd env n → ConstOrigin env c →
    ∃ iid np nfs, ElimDecl Γspec (toKername c) iid np dp nfs ∧ IndInfo env n iid np nfs ∧
      nfs.length = nm

/-- **What a specification environment's entries say about the source.** `ErasesEnv`'s five
source-facing clauses with the entry's presence in place of the program's reachability,
which `deps` turns the one into the other. Program-independent, hence fixed for a run and
maintainable by the registration path. `tabled` is not here: it mentions no `Γspec`. -/
structure SpecContent (env : VEnv) (bo : Name → Option Expr) (lp : Name → List Name)
    (Γspec : GlobalDeclarations) : Prop where
  /-- The keys are distinct. -/
  keys : (Γspec.map Prod.fst).Nodup
  /-- A declared, tabled constant's entry is an erasure of its compiler body, at the
      declaration's own level scope — the scope the eraser erases that body at, and the one
      `ErasesEnv.defns` reads. -/
  defns : ∀ c b, bo c = some b → (LBTerm.envLookup Γspec (toKername c)).isSome →
    ∃ b₀, LBTerm.envLookup Γspec (toKername c) = some (.constantDecl ⟨some b₀⟩) ∧
      Erases env (lp c) [] b b₀
  /-- A declared, body-less, non-eliminator constant's entry is body-less. -/
  axioms : ∀ c, bo c = none → ConstOrigin env c → isCasesOnName c = false →
    (LBTerm.envLookup Γspec (toKername c)).isSome →
    LBTerm.envLookup Γspec (toKername c) = some (.constantDecl ⟨none⟩)
  /-- A declared block key belongs to a covered inductive. -/
  blocks : ∀ (I : Name) (iid : InductiveId) (np : Nat) (nfs : List Nat),
    IndInfo env I iid np nfs → (LBTerm.envLookup Γspec iid.mutualBlockName).isSome →
    IndCovered env Γspec I
  /-- A declared eliminator key belongs to a covered inductive. -/
  elims : ∀ (c I : Name) (dp nm : Nat), CasesOnShape env c I dp nm →
    (LBTerm.envLookup Γspec (toKername c)).isSome → IndCovered env Γspec I

/-- **A specification environment's content, read at a program.** The clauses whose trigger
is the program's reachability get it through `deps`; `htab` is a premise because it mentions
no `Γspec` and so is no fact about the environment at all. -/
theorem SpecContent.erasesEnv (H : SpecContent env bo lp Γspec) {t : LBTerm}
    (hdeps : ∀ kn, ReachableFrom Γspec t kn → (LBTerm.envLookup Γspec kn).isSome)
    (htab : ∀ c b, bo c = some b → ConstOrigin env c) :
    ErasesEnv env bo lp Γspec t :=
  .mk H.keys hdeps htab (fun c b hbo hr => H.defns c b hbo (hdeps _ hr))
    (fun c hbo hco hnc hr => H.axioms c hbo hco hnc (hdeps _ hr))
    (fun hi hr => (H.blocks _ _ _ _ hi (hdeps _ hr)).block _ _ _ hi)
    (fun hsh hinf hco hr => (H.elims _ _ _ _ hsh (hdeps _ hr)).elims _ _ _ hsh hinf hco)

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
`specClosed` is what the `Lower` metatheory the simulation consumes needs of `Γspec`, and it
is a clause here because this is where facts about `Γspec` live. The λ-headedness the
`Lower.source_*` inversion kit needs is `LowerBlock.hfl`, keyed on the blocks the pass
builds, so it is no clause of this structure. -/
structure LowerEnv (Γspec Γ : GlobalDeclarations) : Prop where
  /-- The emitted environment has distinct keys. -/
  keys : (Γ.map Prod.fst).Nodup
  /-- A body declared by both is a `Lower` image, or the η-expansion of one lowered block's
      node: `Erasure.visitMutual` registers `Erasure.etaExpandFix defs j`
      (`Erasure.lean:1276`), not `.fix defs j`, and at `principalArgIdx = 0` that is
      `LBTerm.etaFix defs j` (F-ETA). The second disjunct exists because the registration
      side produces the block shape rather than a `Lower` derivation;
      `Lower.fixEta_of_block` is the converter. -/
  defs : ∀ kn b₀ b, DefnDecl Γspec kn b₀ → DefnDecl Γ kn b →
    Lower Γspec b₀ b ∨ ∃ kns bs defs j, LowerFix Γspec kns bs defs ∧
      kns[j]? = some kn ∧ b = LBTerm.etaFix defs j
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

/-! ## Non-vacuity of `LowerEnv`

The eight fields are jointly satisfiable on the smallest environment carrying a real
`Lower` step.
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

/-! ## A four-entry specification environment

The fixture exercises every kind of entry a specification environment holds: an inductive
block, its `casesOn` eliminator, a recursive definition and a body-less axiom, with the
block and the eliminator together, which is what `blocks` and `elims` are read at. Everything
λ□-side is literal and computed; the source-side readings are `DemoSource`'s hypotheses.
-/

/-- The fixture's inductive type. -/
def demoInd : Name := `DemoT

/-- The fixture's `casesOn` eliminator. -/
def demoCases : Name := `DemoT.casesOn

/-- The fixture's recursive definition. -/
def demoDef : Name := `Demo.loop

/-- The fixture's body-less constant. -/
def demoAx : Name := `Demo.opaqueOp

/-- The fixture's λ□ inductive identifier: the block of `demoInd`, first type. The block
kername is spelled as the literal `indBlockKername [demoInd]` evaluates to, because
`Name.toString` does not reduce definitionally, and reachability through a `.case` node
computes with the block kername. -/
def demoIid : InductiveId := ⟨rootKername "DemoT", 0⟩

/-- The fixture's λ□ inductive body: no parameters, one nullary constructor, not
propositional. -/
def demoMib : MutualInductiveBody where
  npars := 0
  bodies :=
    [{ name := "T", propositional := false, ctors := [{ name := "mk", nargs := 0 }],
       projs := [] }]

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
   (toKername demoCases, .constantDecl ⟨some demoElim⟩),
   (toKername demoDef, .constantDecl ⟨some demoBody⟩),
   (toKername demoAx, .constantDecl ⟨none⟩)]

/-- The fixture's program: the recursive definition itself. -/
def demoProg : LBTerm := .const (toKername demoDef)

/-- The source-side facts the fixture's entries are read against. Everything a `VEnv`
cannot be hand-built to exhibit without a full kernel declaration enters here: which
constants the compiler table defines, the fixture's own block and eliminator, and the
identification of a kername with the name it belongs to, since `toKername` is not
injective. -/
structure DemoSource (env : VEnv) (bo : Name → Option Expr) (lp : Name → List Name) :
    Prop where
  /-- Every constant the compiler table defines is a plain constant of `env`. -/
  tabled : ∀ c b, bo c = some b → ConstOrigin env c
  /-- No constant carrying a compiler body is named by the block's, the eliminator's or the
      axiom's kername. -/
  inert : ∀ c b, bo c = some b → toKername c ≠ toKername demoCases ∧
    toKername c ≠ toKername demoAx ∧ toKername c ≠ demoIid.mutualBlockName
  /-- A body-less, non-eliminator constant is named by none of the other three keys. -/
  axKey : ∀ c, bo c = none → ConstOrigin env c → isCasesOnName c = false →
    toKername c ≠ demoIid.mutualBlockName ∧ toKername c ≠ toKername demoCases ∧
    toKername c ≠ toKername demoDef
  /-- `demoDef`'s compiler body erases to the entry the fixture holds, at its own level
      scope. -/
  defnBody : ∀ c b, bo c = some b → toKername c = toKername demoDef →
    Erases env (lp c) [] b demoBody
  /-- The block of `demoInd`, at no parameters and one nullary constructor. -/
  ind : IndInfo env demoInd demoIid 0 [0]
  /-- `demoInd` is declared by a block of `env`'s own declaration list: upstream ask 2's
      declaration-level conjunct at the fixture. -/
  indDecl : IndDeclOf env demoInd
  /-- Every block reading of `demoInd` is the fixture's own: ask 2's block uniqueness, which
      `IndCovered.block`'s unconditional quantifier needs. -/
  indUniq : ∀ iid np nfs, IndInfo env demoInd iid np nfs → iid = demoIid ∧ np = 0 ∧ nfs = [0]
  /-- The `casesOn` of `demoInd` is `demoCases`, at one dropped argument and one minor. -/
  elimUniq : ∀ (c : Name) (dp nm : Nat), CasesOnShape env c demoInd dp nm →
    toKername c = toKername demoCases ∧ dp = 1 ∧ nm = 1
  /-- A block whose kername the fixture declares is `demoInd`'s. -/
  blockKeyIs : ∀ (I : Name) (iid : InductiveId) (np : Nat) (nfs : List Nat),
    IndInfo env I iid np nfs → (LBTerm.envLookup demoEnv iid.mutualBlockName).isSome →
    I = demoInd
  /-- An eliminator whose kername the fixture declares is `demoInd`'s. -/
  elimKeyIs : ∀ (c I : Name) (dp nm : Nat), CasesOnShape env c I dp nm →
    (LBTerm.envLookup demoEnv (toKername c)).isSome → I = demoInd

/-- The fixture's keys are distinct. -/
theorem demoEnv_keys : ((demoEnv.map Prod.fst).Nodup) := by decide

/-- A key the fixture answers is one of its four. -/
theorem demoEnv_key_cases {kn : Kername} (h : (LBTerm.envLookup demoEnv kn).isSome) :
    kn = demoIid.mutualBlockName ∨ kn = toKername demoCases ∨ kn = toKername demoDef ∨
      kn = toKername demoAx := by
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp h
  have hmem := envLookup_mem hd
  simp only [demoEnv, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
  rcases hmem with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr (.inl rfl))
  · exact .inr (.inr (.inr rfl))

/-- The fixture covers its own inductive: the block entry is `demoMib` and the eliminator
entry is the `casesOn` body, both at the numbers the source side reads. -/
theorem demoEnv_indCovered {env : VEnv} {bo : Name → Option Expr} {lp : Name → List Name}
    (h : DemoSource env bo lp) :
    IndCovered env demoEnv demoInd where
  block iid np nfs hi := by
    obtain ⟨rfl, rfl, rfl⟩ := h.indUniq iid np nfs hi
    refine ⟨h.indDecl, demoMib, rfl, ⟨rfl, _, rfl, rfl⟩, fun oib hoib hp => ?_⟩
    injection hoib with hoib
    subst hoib
    exact absurd hp (by decide)
  elims c dp nm hsh _ _ := by
    obtain ⟨hkn, rfl, rfl⟩ := h.elimUniq c dp nm hsh
    refine ⟨demoIid, 0, [0], ?_, h.ind, rfl⟩
    rw [hkn]
    exact ⟨⟨demoElim, rfl, .cases⟩, demoMib, rfl, ⟨rfl, _, rfl, rfl⟩, _, rfl, rfl⟩

/-- The fixture's entries, in the readings `ErasesEnv` consumes. -/
theorem demoEnv_specContent {env : VEnv} {bo : Name → Option Expr} {lp : Name → List Name}
    (h : DemoSource env bo lp) : SpecContent env bo lp demoEnv where
  keys := demoEnv_keys
  defns c b hbo hd := by
    obtain ⟨hnc, hna, hnb⟩ := h.inert c b hbo
    rcases demoEnv_key_cases hd with hk | hk | hk | hk
    · exact absurd hk hnb
    · exact absurd hk hnc
    · exact ⟨demoBody, by rw [hk]; rfl, h.defnBody c b hbo hk⟩
    · exact absurd hk hna
  axioms c hbo hco hnc hd := by
    obtain ⟨hnb, hncas, hndef⟩ := h.axKey c hbo hco hnc
    rcases demoEnv_key_cases hd with hk | hk | hk | hk
    · exact absurd hk hnb
    · exact absurd hk hncas
    · exact absurd hk hndef
    · rw [hk]; rfl
  blocks I iid np nfs hi hd := by
    rw [h.blockKeyIs I iid np nfs hi hd]; exact demoEnv_indCovered h
  elims c I dp nm hsh hd := by
    rw [h.elimKeyIs c I dp nm hsh hd]; exact demoEnv_indCovered h

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

/-- The fixture is a specification environment for its own program. -/
theorem demoEnv_erasesEnv {env : VEnv} {bo : Name → Option Expr} {lp : Name → List Name}
    (h : DemoSource env bo lp) : ErasesEnv env bo lp demoEnv demoProg :=
  (demoEnv_specContent h).erasesEnv demoEnv_deps h.tabled

end LeanToLambdaBox
