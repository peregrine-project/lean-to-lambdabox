import LeanToLambdaBox.ColdStartShape

/-!
# `SpecEnv` — the specification environment of a run state

`SpecEnv env bo s Γspec` says `Γspec` is a specification environment adequate for the
erasure state `s`: its entries are `ErasesDecl`-justified, every constant `s` registered
is declared in it, and every inductive `s` registered contributes its block, constructor
and eliminator entries.

The state occurs only through the *domain* of the two registries, so the predicate is
antitone in it: `SpecEnv.mono` re-reads one environment at every smaller state a run
passes through. That is what lets sibling sub-runs be threaded under one universally
quantified `Γspec` instead of merging environments.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean Erasure

/--
`Γspec` is a specification environment for the run state `s`.

`keys` and `decls` are `ErasesEnv`'s first two clauses; the last three are the coverage
the state demands. An eliminator entry is demanded only for an informative inductive —
`ErasesDecl.elim` declares no other, because the emitted `.case` of a non-informative one
is stuck on every value a run produces.
-/
structure SpecEnv (env : VEnv) (bo : Name → Option Expr) (s : ErasureState)
    (Γspec : GlobalDeclarations) : Prop where
  /-- The keys of `Γspec` are distinct. -/
  keys : (Γspec.map Prod.fst).Nodup
  /-- Every declaration `Γspec` answers with is `ErasesDecl`-justified. -/
  decls : ∀ kn d, LBTerm.envLookup Γspec kn = some d → ErasesDecl env bo kn d
  /-- Every registered constant is declared, at its canonical kername. -/
  consts : ∀ n : Name, (s.constants.get? n).isSome →
    (LBTerm.envLookup Γspec (toKername n)).isSome
  /-- Every registered inductive contributes its block declaration. -/
  inds : ∀ n : Name, (s.inductives.get? n).isSome →
    ∃ iid np nfs, IndInfo env n iid np nfs ∧
      (LBTerm.envLookup Γspec iid.mutualBlockName).isSome
  /-- Every constructor of a registered inductive is declared. -/
  ctors : ∀ n : Name, (s.inductives.get? n).isSome →
    ∀ c k, CtorOf env c n k → (LBTerm.envLookup Γspec (toKername c)).isSome
  /-- The `casesOn` eliminator of a registered informative inductive is declared. -/
  elims : ∀ n : Name, (s.inductives.get? n).isSome →
    ∀ kn, CasesOnOf env n kn → InformativeInd env n →
      (LBTerm.envLookup Γspec kn).isSome

/-- `SpecEnv` is antitone in the run state: an environment adequate for a state is
adequate for every state below it. The proof is `StateLe`'s two domain clauses. -/
theorem SpecEnv.mono {env : VEnv} {bo : Name → Option Expr} {s₁ s : ErasureState}
    {Γspec : GlobalDeclarations} (h : StateLe s₁ s) (H : SpecEnv env bo s Γspec) :
    SpecEnv env bo s₁ Γspec where
  keys := H.keys
  decls := H.decls
  consts n hn := H.consts n (h.consts hn)
  inds n hn := H.inds n (h.inds hn)
  ctors n hn := H.ctors n (h.inds hn)
  elims n hn := H.elims n (h.inds hn)

/-- A specification environment of a state is a specification environment of any program
whose reachable kernames it declares and whose reached compiler bodies it holds erasures
of. Those two clauses are the ones that mention a program, so they are premises: the state
records which constants a run consulted, not what a given program reaches. -/
theorem SpecEnv.erasesEnv {env : VEnv} {bo : Name → Option Expr} {s : ErasureState}
    {Γspec : GlobalDeclarations} (H : SpecEnv env bo s Γspec) {t : LBTerm}
    (hdeps : ∀ kn, ReachableFrom Γspec t kn → (LBTerm.envLookup Γspec kn).isSome)
    (hdefns : ∀ c b, bo c = some b → ReachableFrom Γspec t (toKername c) →
      ∃ b₀, LBTerm.envLookup Γspec (toKername c) = some (.constantDecl ⟨some b₀⟩) ∧
        ∀ Us' ups us, Erases env Us' [] (b.instantiateLevelParams ups us) b₀) :
    ErasesEnv env bo Γspec t :=
  .mk H.keys H.decls hdeps hdefns

/-- The four-entry fixture is a specification environment for the initial state, whose
registries are empty. Read with `SpecEnv.mono`, it is one for every state below any state
it is read at. -/
theorem demoEnv_specEnv {env : VEnv} {bo : Name → Option Expr} (h : DemoSource env bo) :
    SpecEnv env bo {} demoEnv where
  keys := demoEnv_keys
  decls := demoEnv_decls h
  consts n hn := by simp at hn
  inds n hn := by simp at hn
  ctors n hn := by simp at hn
  elims n hn := by simp at hn

/-! ## The specification environment of a run

`RegInvShape'` (`ColdStartShape.lean`) is what the registration path maintains. Read at the
final state it *is* a `SpecEnv`, and — once the run has registered everything the
specification environment declares — a `LowerEnv` too, with eight of nine clauses derived.
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

/-- The invariant, read as a specification environment: the six fields are exactly the
invariant's specification-side ones, with the inductive clauses unpacked from `IndCovered`. -/
theorem RegInvShape'.specEnv {env : VEnv} {bo : Name → Option Expr}
    {Γspec : GlobalDeclarations} {s : ErasureState} (H : RegInvShape' env bo Γspec s) :
    SpecEnv env bo s Γspec where
  keys := H.specKeys
  decls := H.specDecls
  consts := H.consts
  inds n hn := (H.inds n hn).block
  ctors n hn := (H.inds n hn).ctors
  elims n hn := (H.inds n hn).elims

/-- **A run has a specification environment.** It is the one its own registration invariant
was maintained against — derived from what the run registered, not posited. -/
theorem SpecEnv.exists {env : VEnv} {bo : Name → Option Expr} {s : ErasureState}
    (H : ∃ Γspec, RegInvShape' env bo Γspec s) : ∃ Γspec, SpecEnv env bo s Γspec :=
  let ⟨Γspec, H⟩ := H; ⟨Γspec, H.specEnv⟩

/-- **The emitted environment is the lowered image, derived.** Eight of `LowerEnv`'s nine
clauses come from the invariant and the saturation premises. The ninth, `specBlocks`, is an
explicit binder: it is refuted at every specification environment holding a non-λ body
(`lowerEnv_needs_lambda_bodies`), so no derivation can supply it — `regInvShape'_ctorBody`
exhibits the invariant holding where it fails. -/
theorem RegInvShape'.lowerEnv {env : VEnv} {bo : Name → Option Expr}
    {Γspec : GlobalDeclarations} {s : ErasureState} (H : RegInvShape' env bo Γspec s)
    (hsat : RegSaturated env Γspec s) (hblocks : BlockBodiesLambda Γspec) :
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
  specBlocks := hblocks

/-! ## The δ column of `ErasesEnv`, from the registry -/

/-- **`ErasesEnv.defns` from the run's records.** The reached key is declared (`hdeps`), its
declaration is `ErasesDecl`-justified by the invariant, and the justification is the `defn`
arm: the `ax` arm has no body, the `ind` and `elim` arms are excluded by the naming side
conditions `hblkname`/`hnc`, and `hkinj` identifies the justifying constant with `c`, since
`toKername` is not injective. `hlp` is what makes the clause's unguarded `∀ ups us` reachable
at all — see `defns_needs_paramFree`. -/
theorem RegInvShape'.defns {env : VEnv} {bo : Name → Option Expr}
    {Γspec : GlobalDeclarations} {s : ErasureState} (H : RegInvShape' env bo Γspec s)
    {t : LBTerm}
    (hdeps : ∀ kn, ReachableFrom Γspec t kn → (LBTerm.envLookup Γspec kn).isSome)
    (hkinj : ∀ c c' : Name, toKername c = toKername c' → c = c')
    (hlp : ∀ c b, bo c = some b → b.hasLevelParam' = false ∧ NoMaxLevels b)
    (hnc : ∀ c b, bo c = some b → isCasesOnName c = false)
    (hblkname : ∀ c b, bo c = some b → ∀ I iid np nfs, IndInfo env I iid np nfs →
      iid.mutualBlockName ≠ toKername c) :
    ∀ c b, bo c = some b → ReachableFrom Γspec t (toKername c) →
      ∃ b₀, LBTerm.envLookup Γspec (toKername c) = some (.constantDecl ⟨some b₀⟩) ∧
        ∀ Us' ups us, Erases env Us' [] (b.instantiateLevelParams ups us) b₀ := by
  intro c b hbo hr
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (hdeps _ hr)
  obtain ⟨kn, hkn, hd'⟩ : ∃ kn, kn = toKername c ∧ LBTerm.envLookup Γspec kn = some d :=
    ⟨_, rfl, hd⟩
  have hdec := H.specDecls kn d hd'
  cases hdec with
  | defn hc huv hbody hb =>
    rename_i c' body b₀ Us ci
    have hcc : c' = c := hkinj c' c hkn
    subst hcc
    rw [hbo] at hbody
    have hbb : body = b := (Option.some.inj hbody).symm
    subst hbb
    obtain ⟨hlpb, hnmb⟩ := hlp c' body hbo
    refine ⟨b₀, by rw [← hkn]; exact hd', fun Us' ups us => ?_⟩
    rw [instantiateLevelParams_eq_self hlpb]
    exact erases_any_scope_of_paramFree hlpb hnmb hb Us'
  | ax hcst hno =>
    rename_i c' ci
    rw [hkinj c' c hkn, hbo] at hno
    exact absurd hno (by simp)
  | ind hind hm =>
    rename_i I iid np nfs mib
    exact absurd hkn (hblkname c b hbo I iid np nfs hind)
  | elim hi he hinf hsh hco hbody =>
    rename_i I c' iid np dp nfs body
    obtain ⟨ci, hci, hcas, hpre, hknc⟩ := he
    subst hknc
    have hcc : c' = c := hkinj c' c hkn
    subst hcc
    rw [hnc c' b hbo] at hcas
    exact Bool.noConfusion hcas

/-- **The environment relation of a run.** `SpecEnv.erasesEnv`'s two program-facing premises:
`hdeps` is the program's own reachability, and the δ column is `RegInvShape'.defns`. -/
theorem RegInvShape'.erasesEnv {env : VEnv} {bo : Name → Option Expr}
    {Γspec : GlobalDeclarations} {s : ErasureState} (H : RegInvShape' env bo Γspec s)
    {t : LBTerm}
    (hdeps : ∀ kn, ReachableFrom Γspec t kn → (LBTerm.envLookup Γspec kn).isSome)
    (hkinj : ∀ c c' : Name, toKername c = toKername c' → c = c')
    (hlp : ∀ c b, bo c = some b → b.hasLevelParam' = false ∧ NoMaxLevels b)
    (hnc : ∀ c b, bo c = some b → isCasesOnName c = false)
    (hblkname : ∀ c b, bo c = some b → ∀ I iid np nfs, IndInfo env I iid np nfs →
      iid.mutualBlockName ≠ toKername c) :
    ErasesEnv env bo Γspec t :=
  H.specEnv.erasesEnv hdeps (H.defns hdeps hkinj hlp hnc hblkname)

/-! ## What the two refuted clauses cost -/

/-- **Finding W2b-F1, at the registry.** A run that has registered one constructor-bodied
definition — `Unit.unit`'s shape, present once per file in all five programs — satisfies every
clause of the invariant, and `BlockBodiesLambda` fails at its specification environment. So
`LowerEnv`'s ninth clause is not underived here but unavailable: the eight derived clauses hold
at a state where the ninth is false. -/
theorem regInvShape'_ctorBody {env : VEnv} {bo : Name → Option Expr}
    (hdecls : ∀ kn d, LBTerm.envLookup ctorBodyEnv kn = some d → ErasesDecl env bo kn d) :
    RegInvShape' env bo ctorBodyEnv
        (nonrecConstState `u (.construct ctorBodyIid 0 []) {}) ∧
      ¬ BlockBodiesLambda ctorBodyEnv := by
  have hclosed : ClosedBodies ctorBodyEnv := by
    intro kn b hb
    rw [DefnDecl, ctorBodyEnv, LBTerm.envLookup] at hb
    split at hb
    · cases hb; exact trivial
    · simp [LBTerm.envLookup] at hb
  refine ⟨(RegInvShape'.empty (by decide) hdecls hclosed).constCons
    (b₀ := .construct ctorBodyIid 0 []) rfl
    (.inl (.construct rfl (by intro j hj; simp at hj))) trivial (by simp),
    not_blockBodiesLambda_ctorBodyEnv⟩

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

/-- **The derivation is not vacuous.** A run that starts at the empty state and registers one
λ-bodied definition satisfies the invariant and saturates its own specification environment, so
`LowerEnv` comes out with all nine clauses — the ninth from the fixture's own λ-bodied entry,
which is exactly the shape `specBlocks` is true of and `regInvShape'_ctorBody` is not. -/
theorem lowerEnv_of_cold_run {env : VEnv} {bo : Name → Option Expr}
    (hdecls : ∀ kn d, LBTerm.envLookup idEnv kn = some d → ErasesDecl env bo kn d) :
    LowerEnv idEnv (nonrecConstState `id (.lambda .anon (.bvar 0)) {}).gdecls := by
  have H : RegInvShape' env bo idEnv (nonrecConstState `id (.lambda .anon (.bvar 0)) {}) :=
    (RegInvShape'.empty lowerEnv_idEnv.keys hdecls lowerEnv_idEnv.specClosed).constCons
      (b₀ := .lambda .anon (.bvar 0)) rfl (.inl (.lambda (.bvar 0)))
      (lowerEnv_idEnv.closed (rootKername "id") _ rfl) (by simp)
  refine H.lowerEnv ⟨?_, ?_⟩ lowerEnv_idEnv.specBlocks
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

/-- **`ErasesDecl.elim`'s two new fields, at the `natEnv` rung fixture.** `hsh` is the
eliminator's segmentation read off the fixture's own declaration list (`nat_casesOnShape`) and
`hco` is the eliminator constant's own reading (`nat_constOrigin_cas`); neither is assumed. -/
theorem natEnv_erasesDecl_elim {bo : Name → Option Expr} :
    ErasesDecl NatWitness.natEnv bo (toKername NatWitness.natC)
      (.constantDecl ⟨some (mkElimBody NatWitness.natIid 0 1 [0, 1])⟩) :=
  .elim NatWitness.nat_indInfo ⟨_, NatWitness.natEnv_C, rfl, rfl, rfl⟩
    ⟨⟨0, NatWitness.natSort⟩, rfl, .zero, by rfl⟩
    NatWitness.nat_casesOnShape NatWitness.nat_constOrigin_cas .cases

end LeanToLambdaBox
