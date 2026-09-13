import LeanToLambdaBox.ColdStartShape

/-!
# `SpecEnv` — the specification environment of a run state

`SpecEnv env bo s Γspec` says `Γspec` is a specification environment adequate for the
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
structure SpecEnv (env : VEnv) (bo : Name → Option Expr) (s : ErasureState)
    (Γspec : GlobalDeclarations) : Prop where
  /-- What the entries of `Γspec` say about the source. -/
  spec : SpecContent env bo Γspec
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
theorem SpecEnv.mono {env : VEnv} {bo : Name → Option Expr} {s₁ s : ErasureState}
    {Γspec : GlobalDeclarations} (h : StateLe s₁ s) (H : SpecEnv env bo s Γspec) :
    SpecEnv env bo s₁ Γspec where
  spec := H.spec
  consts n hn := H.consts n (h.consts hn)
  inds n hn := H.inds n (h.inds hn)
  fvarFree := H.fvarFree

/-- A specification environment of a state is a specification environment of any program
whose reachable kernames it declares, whose reached compiler bodies it holds erasures of at
every level scope, and whose compiler table defines only plain constants. Those three
clauses are the ones the state does not record — the first mentions a program, the second
strengthens `SpecContent.defns` past the one scope a run erases at, and the third mentions
no `Γspec` at all — so they are premises. -/
theorem SpecEnv.erasesEnv {env : VEnv} {bo : Name → Option Expr} {s : ErasureState}
    {Γspec : GlobalDeclarations} (H : SpecEnv env bo s Γspec) {t : LBTerm}
    (hdeps : ∀ kn, ReachableFrom Γspec t kn → (LBTerm.envLookup Γspec kn).isSome)
    (hdefns : ∀ c b, bo c = some b → ReachableFrom Γspec t (toKername c) →
      ∃ b₀, LBTerm.envLookup Γspec (toKername c) = some (.constantDecl ⟨some b₀⟩) ∧
        ∀ Us' ups us, Erases env Us' [] (b.instantiateLevelParams ups us) b₀)
    (htab : ∀ c b, bo c = some b → ConstOrigin env c) :
    ErasesEnv env bo Γspec t :=
  H.spec.erasesEnv hdeps hdefns htab

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
theorem demoEnv_specEnv {env : VEnv} {bo : Name → Option Expr} (h : DemoSource env bo) :
    SpecEnv env bo {} demoEnv where
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
theorem RegInvShape'.specEnv {env : VEnv} {bo : Name → Option Expr}
    {Γspec : GlobalDeclarations} {s : ErasureState} (H : RegInvShape' env bo Γspec s) :
    SpecEnv env bo s Γspec where
  spec := H.spec
  consts := H.consts
  inds := H.inds
  fvarFree := H.specFVarFree

/-- **A run has a specification environment.** It is the one its own registration invariant
was maintained against — derived from what the run registered, not posited. -/
theorem SpecEnv.exists {env : VEnv} {bo : Name → Option Expr} {s : ErasureState}
    (H : ∃ Γspec, RegInvShape' env bo Γspec s) : ∃ Γspec, SpecEnv env bo s Γspec :=
  let ⟨Γspec, H⟩ := H; ⟨Γspec, H.specEnv⟩

/-- **The emitted environment is the lowered image, derived.** All eight of `LowerEnv`'s
clauses come from the invariant and the saturation premises: the λ-headedness clause that
was refuted at every specification environment holding a non-λ body is gone, its content
being `LowerBlock.hfl`, a condition on the blocks the pass builds. -/
theorem RegInvShape'.lowerEnv {env : VEnv} {bo : Name → Option Expr}
    {Γspec : GlobalDeclarations} {s : ErasureState} (H : RegInvShape' env bo Γspec s)
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

/-- **`ErasesEnv.defns` from the run's records.** The reached key is declared (`hdeps`) and
`SpecContent.defns` reads its entry at the one level scope a run erases at; `hlp` is what
makes the clause's unguarded `∀ ups us` reachable from that — see `defns_needs_paramFree`. -/
theorem RegInvShape'.defns {env : VEnv} {bo : Name → Option Expr}
    {Γspec : GlobalDeclarations} {s : ErasureState} (H : RegInvShape' env bo Γspec s)
    {t : LBTerm}
    (hdeps : ∀ kn, ReachableFrom Γspec t kn → (LBTerm.envLookup Γspec kn).isSome)
    (hlp : ∀ c b, bo c = some b → b.hasLevelParam' = false ∧ NoMaxLevels b) :
    ∀ c b, bo c = some b → ReachableFrom Γspec t (toKername c) →
      ∃ b₀, LBTerm.envLookup Γspec (toKername c) = some (.constantDecl ⟨some b₀⟩) ∧
        ∀ Us' ups us, Erases env Us' [] (b.instantiateLevelParams ups us) b₀ := by
  intro c b hbo hr
  obtain ⟨b₀, Us, hd, hb⟩ := H.spec.defns c b hbo (hdeps _ hr)
  obtain ⟨hlpb, hnmb⟩ := hlp c b hbo
  refine ⟨b₀, hd, fun Us' ups us => ?_⟩
  rw [instantiateLevelParams_eq_self hlpb]
  exact erases_any_scope_of_paramFree hlpb hnmb hb Us'

/-- **The environment relation of a run.** `SpecEnv.erasesEnv`'s three premises: `hdeps` is
the program's own reachability, the δ column is `RegInvShape'.defns`, and `htab` is the one
clause that mentions no specification environment, so no registry fact supplies it — at the
bridge it is `constOrigin_of_tabled`. -/
theorem RegInvShape'.erasesEnv {env : VEnv} {bo : Name → Option Expr}
    {Γspec : GlobalDeclarations} {s : ErasureState} (H : RegInvShape' env bo Γspec s)
    {t : LBTerm}
    (hdeps : ∀ kn, ReachableFrom Γspec t kn → (LBTerm.envLookup Γspec kn).isSome)
    (hlp : ∀ c b, bo c = some b → b.hasLevelParam' = false ∧ NoMaxLevels b)
    (htab : ∀ c b, bo c = some b → ConstOrigin env c) :
    ErasesEnv env bo Γspec t :=
  H.specEnv.erasesEnv hdeps (H.defns hdeps hlp) htab

/-! ## What the level-scope quantifier costs -/

/-- **Why `defns` needs a level-parameter-free body.** The clause quantifies over *every*
instantiation, including one that sends a body's own parameter to a level the reading scope
does not know: no `Erases` derivation of the result exists, since the only arm at a sort is
`box` and its translation witness needs the level in scope. `RegInvShape'.defns` therefore
discharges the clause at parameter-free bodies and no further. -/
theorem defns_needs_paramFree {env : VEnv} {b₀ : LBTerm} (v : Name) :
    ¬ ∀ (Us' ups : List Name) (us : List Level),
        Erases env Us' [] ((Expr.sort (.param `u)).instantiateLevelParams ups us) b₀ := by
  intro h
  have hins : (Expr.sort (.param `u)).instantiateLevelParams [`u] [.param v]
      = .sort (.param v) := by
    rw [Expr.instantiateLevelParams_eq]
    simp [Expr.instantiateLevelParamsCore', Level.substParams']
  have hE := h [] [`u] [.param v]
  rw [hins] at hE
  cases hE with
  | box htr her => cases htr with | sort hl => simp [Lean4Lean.VLevel.ofLevel] at hl

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
theorem lowerEnv_of_cold_run {env : VEnv} {bo : Name → Option Expr}
    (hspec : SpecContent env bo idEnv) :
    LowerEnv idEnv (nonrecConstState `id (.lambda .anon (.bvar 0)) {}).gdecls := by
  have H : RegInvShape' env bo idEnv (nonrecConstState `id (.lambda .anon (.bvar 0)) {}) :=
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
  ⟨⟨⟨_, natSpecEnv_elim, .cases⟩, natSpecMib, natSpecEnv_block, rfl, _, rfl, rfl, rfl⟩,
    NatWitness.nat_indInfo, rfl⟩

end LeanToLambdaBox
