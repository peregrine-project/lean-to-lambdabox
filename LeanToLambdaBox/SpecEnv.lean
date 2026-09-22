import LeanToLambdaBox.ColdStartShape

/-!
# `SpecEnv` — the specification environment of a run state

`SpecEnv env bo lp s Γspec` says `Γspec` is a specification environment adequate for the
erasure state `s`: its entries say of the source what `SpecContent` asks, every constant `s`
registered is declared in it, and every inductive `s` registered is covered.

The state occurs only through the *domain* of the two registries, so the predicate is
antitone in it: `SpecEnv.mono` re-reads one environment at every smaller state a run
passes through. That is what lets sibling sub-runs be threaded under one universally
quantified `Γspec` instead of merging environments.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean Erasure

/--
`Γspec` is a specification environment for the run state `s`.

`spec` is what `ErasesEnv` reads; `consts` and `inds` are the coverage the state demands.
An eliminator entry is demanded only for an informative inductive — the emitted `.case` of a
non-informative one is stuck on every value a run produces, so relevance is a hypothesis of
`IndCovered.elims` and of `ErasesEnv.elims` alike.
-/
structure SpecEnv (env : VEnv) (bo : Name → Option Expr) (lp : Name → List Name)
    (s : ErasureState) (Γspec : GlobalDeclarations) : Prop where
  /-- What the entries of `Γspec` say about the source. -/
  spec : SpecContent env bo lp Γspec
  /-- Every registered constant is declared, at its canonical kername. -/
  consts : ∀ n : Name, (s.constants.get? n).isSome →
    (LBTerm.envLookup Γspec (toKername n)).isSome
  /-- Every registered inductive is covered. -/
  inds : ∀ n : Name, (s.inductives.get? n).isSome → IndCovered env Γspec n
  /-- The specification bodies mention no free variable, which is what makes the pass commute
      with abstraction (`Lower.abstract`) — the clause the bridge's binder steps consume. -/
  fvarFree : FVarFreeBodies Γspec

/-- `SpecEnv` is antitone in the run state: an environment adequate for a state is
adequate for every state below it. The proof is `StateLe`'s two domain clauses. -/
theorem SpecEnv.mono {env : VEnv} {bo : Name → Option Expr} {lp : Name → List Name}
    {s₁ s : ErasureState} {Γspec : GlobalDeclarations} (h : StateLe s₁ s)
    (H : SpecEnv env bo lp s Γspec) :
    SpecEnv env bo lp s₁ Γspec where
  spec := H.spec
  consts n hn := H.consts n (h.consts hn)
  inds n hn := H.inds n (h.inds hn)
  fvarFree := H.fvarFree

/-- A specification environment of a state is a specification environment of any program
whose reachable kernames it declares, whose compiler table defines only plain constants, and
whose tabled bodies translate at their own level scope. Those three clauses are the ones the
state does not record — the first mentions a program, the other two mention no `Γspec` at
all — so they are premises. -/
theorem SpecEnv.erasesEnv {env : VEnv} {bo : Name → Option Expr} {lp : Name → List Name}
    {s : ErasureState} {Γspec : GlobalDeclarations} (H : SpecEnv env bo lp s Γspec)
    {t : LBTerm}
    (hdeps : ∀ kn, ReachableFrom Γspec t kn → (LBTerm.envLookup Γspec kn).isSome)
    (htab : ∀ c b, bo c = some b → ConstOrigin env c)
    (hlvl : ∀ c b, bo c = some b → NoMaxLevels b ∧ ∃ vb, TrExprS env (lp c) [] b vb) :
    ErasesEnv env bo lp Γspec t :=
  H.spec.erasesEnv hdeps htab hlvl

/-- The four-entry fixture declares two bodies, the eliminator's and the definition's, and
neither mentions a free variable. -/
theorem fvarFree_demoEnv : FVarFreeBodies demoEnv := by
  have helim : ∀ x : FVarId, ¬ hasFVar x demoElim := by
    intro x
    show ¬ hasFVar x (mkElimBody demoIid 0 1 [0])
    rw [mkElimBody]
    simp [mkLambdas, elimAlts, hasFVarAlts_iff, fieldArgs]
  intro kn b x hd
  have hmem := envLookup_mem hd
  simp only [demoEnv, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
  rcases hmem with ⟨-, hb⟩ | ⟨-, hb⟩ | ⟨-, hb⟩ | ⟨-, hb⟩
  · exact absurd hb (by simp)
  · injection hb with hb; injection hb with hb
    rw [Option.some.inj hb]; exact helim x
  · injection hb with hb; injection hb with hb
    rw [Option.some.inj hb]; simp [demoBody]
  · injection hb with hb; injection hb with hb
    exact absurd hb (by simp)

/-- The four-entry fixture is a specification environment for the initial state, whose
registries are empty. Read with `SpecEnv.mono`, it is one for every state below any state
it is read at. -/
theorem demoEnv_specEnv {env : VEnv} {bo : Name → Option Expr} {lp : Name → List Name}
    (h : DemoSource env bo lp) : SpecEnv env bo lp {} demoEnv where
  spec := demoEnv_specContent h
  consts n hn := by simp at hn
  inds n hn := by simp at hn
  fvarFree := fvarFree_demoEnv

/-! ## The specification environment of a run

`RegInvShape'` (`ColdStartShape.lean`) is what the registration path maintains. Read at the
final state it *is* a `SpecEnv`, and — once the run has registered everything the
specification environment declares — a `LowerEnv` too, with every clause derived.
-/

/-- The run has registered everything the specification environment declares: every
non-runtime-key definition is some registered constant's, and every block is some registered
inductive's. This is what turns `RegInvShape'`'s registry-scoped clauses into `LowerEnv`'s
unscoped ones; without it a pruned-away definition satisfies the scoped clause vacuously. -/
structure RegSaturated (env : VEnv) (Γspec : GlobalDeclarations) (s : ErasureState) : Prop where
  /-- Every declared definition that is not a runtime key was registered. -/
  consts : ∀ kn b₀, DefnDecl Γspec kn b₀ → ¬ RuntimeKey Γspec kn →
    ∃ n : Name, toKername n = kn ∧ (s.constants.get? n).isSome
  /-- Every declared block is a registered inductive's. -/
  inds : ∀ kn d, LBTerm.envLookup Γspec kn = some (.inductiveDecl d) →
    ∃ (n : Name) (iid : InductiveId) (np : Nat) (nfs : List Nat),
      (s.inductives.get? n).isSome ∧ IndInfo env n iid np nfs ∧ kn = iid.mutualBlockName

/-- The invariant, read as a specification environment: the three fields are exactly the
invariant's specification-side ones. -/
theorem RegInvShape'.specEnv {env : VEnv} {bo : Name → Option Expr} {lp : Name → List Name}
    {Γspec : GlobalDeclarations} {s : ErasureState} (H : RegInvShape' env bo lp Γspec s) :
    SpecEnv env bo lp s Γspec where
  spec := H.spec
  consts := H.consts
  inds := H.inds
  fvarFree := H.specFVarFree

/-- **A run has a specification environment.** It is the one its own registration invariant
was maintained against — derived from what the run registered, not posited. -/
theorem SpecEnv.exists {env : VEnv} {bo : Name → Option Expr} {lp : Name → List Name}
    {s : ErasureState} (H : ∃ Γspec, RegInvShape' env bo lp Γspec s) :
    ∃ Γspec, SpecEnv env bo lp s Γspec :=
  let ⟨Γspec, H⟩ := H; ⟨Γspec, H.specEnv⟩

/-- **The emitted environment is the lowered image, derived.** All eight of `LowerEnv`'s
clauses come from the invariant and the saturation premises: the λ-headedness clause that
was refuted at every specification environment holding a non-λ body is gone, its content
being `LowerBlock.hfl`, a condition on the blocks the pass builds. -/
theorem RegInvShape'.lowerEnv {env : VEnv} {bo : Name → Option Expr} {lp : Name → List Name}
    {Γspec : GlobalDeclarations} {s : ErasureState} (H : RegInvShape' env bo lp Γspec s)
    (hsat : RegSaturated env Γspec s) :
    LowerEnv Γspec s.gdecls where
  keys := H.keys
  defs := H.defs
  defsTotal kn b₀ h₀ hrk := by
    obtain ⟨n, rfl, hn⟩ := hsat.consts kn b₀ h₀ hrk
    exact H.defsTotal n b₀ hn h₀ hrk
  axioms := H.axioms
  inds kn d hd := by
    obtain ⟨n, iid, np, nfs, hn, hind, rfl⟩ := hsat.inds kn d hd
    exact H.indsEmitted n hn iid np nfs hind d hd
  sub := H.sub
  closed := H.closed
  specClosed := H.specClosed

/-! ## The δ column of `ErasesEnv`, from the registry -/

/-- **The environment relation of a run.** `SpecEnv.erasesEnv`'s three premises: `hdeps` is
the program's own reachability, and `htab` and `hlvl` are the two clauses that mention no
specification environment, so no registry fact supplies them — at the bridge they are
`constOrigin_of_tabled` and `tabledLevels_of_table`. The δ column is the invariant's own
`SpecContent.defns`, which records the declaration's level scope, the scope `ErasesEnv.defns`
asks at. -/
theorem RegInvShape'.erasesEnv {env : VEnv} {bo : Name → Option Expr} {lp : Name → List Name}
    {Γspec : GlobalDeclarations} {s : ErasureState} (H : RegInvShape' env bo lp Γspec s)
    {t : LBTerm}
    (hdeps : ∀ kn, ReachableFrom Γspec t kn → (LBTerm.envLookup Γspec kn).isSome)
    (htab : ∀ c b, bo c = some b → ConstOrigin env c)
    (hlvl : ∀ c b, bo c = some b → NoMaxLevels b ∧ ∃ vb, TrExprS env (lp c) [] b vb) :
    ErasesEnv env bo lp Γspec t :=
  H.specEnv.erasesEnv hdeps htab hlvl

/-! ## A cold run, end to end -/

/-- The one-definition fixture's body is a closed λ over a de Bruijn index. -/
theorem fvarFree_idEnv : FVarFreeBodies idEnv := by
  intro kn b x hd
  rw [DefnDecl, idEnv, LBTerm.envLookup] at hd
  split at hd
  · injection hd with hd; injection hd with hd; injection hd with hd
    rw [← Option.some.inj hd]
    exact fun hc => hc
  · simp [LBTerm.envLookup] at hd

/-- **The derivation is not vacuous.** A run that starts at the empty state and registers one
λ-bodied definition satisfies the invariant and saturates its own specification environment, so
`LowerEnv` comes out with every clause derived. -/
theorem lowerEnv_of_cold_run {env : VEnv} {bo : Name → Option Expr} {lp : Name → List Name}
    (hspec : SpecContent env bo lp idEnv) :
    LowerEnv idEnv (nonrecConstState `id (.lambda .anon (.bvar 0)) {}).gdecls := by
  have H : RegInvShape' env bo lp idEnv
      (nonrecConstState `id (.lambda .anon (.bvar 0)) {}) :=
    (RegInvShape'.empty hspec lowerEnv_idEnv.specClosed fvarFree_idEnv).constCons
      (b₀ := .lambda .anon (.bvar 0)) rfl (.inl (.lambda (.bvar 0)))
      (lowerEnv_idEnv.closed (rootKername "id") _ rfl) (by simp)
  refine H.lowerEnv ⟨?_, ?_⟩
  · intro kn b₀ h₀ _
    refine ⟨`id, ?_, ?_⟩
    · rw [DefnDecl, idEnv, LBTerm.envLookup] at h₀
      split at h₀
      · rename_i hb; exact (Kername.eq_of_beq hb)
      · simp [LBTerm.envLookup] at h₀
    · exact constants_isSome_insert_self _ _ _
  · intro kn d hd
    rw [idEnv, LBTerm.envLookup] at hd
    split at hd
    · exact absurd hd (by simp)
    · simp [LBTerm.envLookup] at hd

/-! ## The eliminator entry, at the `natEnv` fixture -/

/-- The λ□ block of the `natEnv` fixture's `Nat`: no parameters, a nullary and a unary
constructor, not propositional. -/
def natSpecMib : MutualInductiveBody where
  npars := 0
  bodies := [{ name := "Nat",
               propositional := false,
               ctors := [{ name := "zero", nargs := 0 }, { name := "succ", nargs := 1 }],
               projs := [] }]

/-- The λ□ specification environment of the `natEnv` fixture: `Nat`'s block and the
`ElimBody` its `casesOn` constant is declared with. -/
def natSpecEnv : GlobalDeclarations :=
  [(NatWitness.natIid.mutualBlockName, .inductiveDecl natSpecMib),
   (toKername NatWitness.natC,
     .constantDecl ⟨some (mkElimBody NatWitness.natIid 0 1 [0, 1])⟩)]

/-- The block entry, at its own kername. -/
theorem natSpecEnv_block :
    LBTerm.envLookup natSpecEnv NatWitness.natIid.mutualBlockName
      = some (.inductiveDecl natSpecMib) := envLookup_cons_self

/-- The eliminator entry, one key past the block's. -/
theorem natSpecEnv_elim :
    LBTerm.envLookup natSpecEnv (toKername NatWitness.natC)
      = some (.constantDecl ⟨some (mkElimBody NatWitness.natIid 0 1 [0, 1])⟩) := by
  rw [natSpecEnv, envLookup_cons_ne (kername_ne_of_beq_false (by decide))]
  exact envLookup_cons_self

/-- **What `IndCovered.elims` returns, at the `natEnv` rung fixture.** The source side is read
off the fixture's own declaration list (`nat_indInfo`) and the λ□ side is the eliminator entry
`Lower.elimApp` reads, together with the block `ElimDecl` requires beside it. -/
theorem natEnv_elimCovered :
    ElimDecl natSpecEnv (toKername NatWitness.natC) NatWitness.natIid 0 1 [0, 1] ∧
      IndInfo NatWitness.natEnv NatWitness.natN NatWitness.natIid 0 [0, 1] ∧
      ([0, 1] : List Nat).length = 2 :=
  ⟨⟨⟨_, natSpecEnv_elim, .cases⟩, natSpecMib, natSpecEnv_block, ⟨rfl, _, rfl, rfl⟩,
      _, rfl, rfl⟩,
    NatWitness.nat_indInfo, rfl⟩

end LeanToLambdaBox
