import LeanToLambdaBox.Capstone

/-!
# The green ladder

One theorem per rung, each an instance of `shipping_erase_correct_firstorder` at a real
`#erase` run, whose conclusion ends in a **literal** λ□ answer — so it cannot be satisfied
by `□` or by a stuck term. The rung's data (the reified table, the emitted environment and
term) is committed here; `VerifyBench/Spikes/G1.lean` re-runs the frontend and writes the
`.ast` that `lake exe green-check G1` byte-diffs against the committed one.

`lenv` and `env` are universally quantified in every rung, so the ladder delivers
**conditional** non-vacuity: no computation can make it unconditional. What a rung does
deliver unconditionally is that the conditions are consistent with a literal answer, and
that every hypothesis a computation can settle — the configuration, the fragment check,
the reachable-axiom check, the target evaluation — is settled by one.
-/

/-- Rung G1's subject: a closed nullary definition whose value is a constructor.
Declared at the root so that its kername is `rootKername "spikeZero"`, which is what the
emitted environment below records. -/
def spikeZero : Nat := Nat.zero

namespace LeanToLambdaBox.Green

open Lean Lean4Lean Witness

/-! ## G1 — `spikeZero : Nat := Nat.zero` -/

/-- The configuration rung G1 is erased under: the one `ConfigPinned` describes. -/
def g1Config : Erasure.ErasureConfig :=
  { extern := .preferLogical, nat := .peano, csimp := false }

/-- The reified slice of the elaboration environment rung G1 reads, spliced by `reify%`
out of the environment this module elaborates in. -/
def g1Table : SourceTable := reify% spikeZero

/-- The source term `#erase spikeZero` elaborates. -/
def eG1 : Expr := .const ``spikeZero []

/-- `Nat`'s λ□ inductive identifier. -/
def natIid : InductiveId := ⟨rootKername "Nat", 0⟩

/-- `Nat`'s emitted inductive body: two constructors, no parameters, not propositional. -/
def natBody : MutualInductiveBody :=
  { npars := 0,
    bodies := [{ name := "Nat", propositional := false, kelim := .IntoAny,
                 ctors := [{ name := "Nat.zero", nargs := 0 },
                           { name := "Nat.succ", nargs := 1 }],
                 projs := [] }] }

/-- Rung G1's emitted environment, transcribed from `VerifyBench/ast/Spikes/G1.ast`. -/
def g1Env : GlobalDeclarations :=
  [ (rootKername "spikeZero", .constantDecl ⟨some (.construct natIid 0 [])⟩),
    (rootKername "Nat", .inductiveDecl natBody) ]

/-- Rung G1's emitted term. -/
def g1Term : LBTerm := .const (rootKername "spikeZero")

/-- Rung G1's answer: the λ□ peano numeral `0`. -/
def g1Answer : LBTerm := .construct natIid 0 []

/-! ### The hypotheses a computation settles -/

/-- The rung's configuration is the pinned one. -/
theorem g1_configPinned : ConfigPinned g1Config := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The subject is inside the supported fragment, decided on the reified table.
The verdict is computed by the kernel: `String.isPrefixOf`, which `isMatcherName` calls,
does not reduce in the elaborator. -/
theorem g1_supported : supportedB g1Table 8 eG1 = .ok () := by
  have h : (supportedB g1Table 8 eG1).isOk = true := by decide +kernel
  cases hx : supportedB g1Table 8 eG1 with
  | ok u => cases u; rfl
  | error err => rw [hx] at h; exact Bool.noConfusion h

/-- Every axiom the emitted program reaches has a realizer — vacuously, since it reaches
none. -/
theorem g1_erasableAxioms : ErasableAxioms g1Env g1Term := by decide +kernel

/-- The emitted program evaluates to the literal answer, by the certified evaluator. -/
theorem g1_eval : WcbvEval g1Env eraseFlags g1Term g1Answer :=
  lbEval_sound (n := 8) (by rfl)

/-! ### The compiler bodies, typed -/

/-- Every declaration `tbl` pins is safe in `lenv` — none is `unsafe` or `partial`.
`Witness.SourceTableAdequate` pins level parameters, types and the constructor split but
not the safety flag, and `ErasureSpec.decl_adequate` reads only safe declarations, so the
flag is named separately. Class **D** for the reason the table's own adequacy is: no term
denotes `lenv`. -/
def TableSafe (lenv : Lean.Environment) (tbl : SourceTable) : Prop :=
  ∀ (n : Name) (ci : ConstantInfo), (tbl.decl? n).isSome → lenv.find? n = some ci →
    DefinitionSafety.safe ≤ ci.safety

/-- The declaration column of rung G1's reified table: the subject and the two `Nat`
constructors, of which only the subject carries a body. -/
def g1Decls : List (Name × ReifiedDecl) :=
  [ (``Nat.succ, ⟨[], .forallE `n (.const ``Nat []) (.const ``Nat []) .default, none⟩),
    (``Nat.zero, ⟨[], .const ``Nat [], none⟩),
    (``spikeZero, ⟨[], .const ``Nat [], some (.const ``Nat.zero [])⟩) ]

/-- The reified table's declaration column is that literal. -/
theorem g1_decls_eq : g1Table.decls = g1Decls := rfl

/-- The subject is the one tabled name with a body, and its body is the constructor
constant `Nat.zero`. -/
theorem g1_body?_some {c : Name} {b : Expr} (h : g1Table.body? c = some b) :
    c = ``spikeZero ∧ b = .const ``Nat.zero [] := by
  rw [SourceTable.body?, SourceTable.decl?, g1_decls_eq, g1Decls] at h
  simp only [List.lookup] at h
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  split at h
  · rename_i hc
    exact ⟨eq_of_beq hc, by simpa using h.symm⟩
  · exact absurd h (by simp)

/-- The subject's tabled declaration is pinned: `lenv` knows `spikeZero` monomorphically,
at type `Nat`. -/
theorem g1_pinned_subject {lenv : Lean.Environment} (htbl : SourceTableAdequate lenv g1Table) :
    ∃ ci : ConstantInfo, lenv.find? ``spikeZero = some ci ∧ ci.levelParams = [] ∧
      ci.type = .const ``Nat [] :=
  (htbl.decls ``spikeZero _
    (mem_of_lookup (show g1Table.decls.lookup ``spikeZero
      = some ⟨[], .const ``Nat [], some (.const ``Nat.zero [])⟩ from rfl))).1

/-- `Nat.zero`'s tabled declaration is pinned: `lenv` knows it monomorphically, at type
`Nat`. -/
theorem g1_pinned_zero {lenv : Lean.Environment} (htbl : SourceTableAdequate lenv g1Table) :
    ∃ ci : ConstantInfo, lenv.find? ``Nat.zero = some ci ∧ ci.levelParams = [] ∧
      ci.type = .const ``Nat [] :=
  (htbl.decls ``Nat.zero _
    (mem_of_lookup (show g1Table.decls.lookup ``Nat.zero
      = some ⟨[], .const ``Nat [], none⟩ from rfl))).1

/-- **The rung's compiler bodies are typed.** `CompilerBodies` — `hcb` in the capstone — is
not assumed at this rung: the one tabled body is the constructor constant, and the pinned
table together with `ErasureSpec.decl_adequate` types it at the subject's declared type. -/
theorem g1_compilerBodies {lenv : Lean.Environment} {env : VEnv} {Us : List Name}
    {gw : Void IO.RealWorld → NameGenerator} (P : ErasureSpec lenv env Us gw)
    (htbl : SourceTableAdequate lenv g1Table) (hsafe : TableSafe lenv g1Table) :
    CompilerBodies lenv env g1Table.body? := by
  intro c b hb
  obtain ⟨rfl, rfl⟩ := g1_body?_some hb
  obtain ⟨ci, hci, hlp, hty⟩ := g1_pinned_subject htbl
  obtain ⟨ciz, hciz, hlpz, htyz⟩ := g1_pinned_zero htbl
  obtain ⟨⟨uvz, tyz⟩, hconstz, -, huv, htrty⟩ :=
    P.decl_adequate ``Nat.zero ciz hciz (hsafe ``Nat.zero ciz rfl hciz)
  rw [hlpz] at huv
  rw [hlpz, htyz] at htrty
  cases htrty with
  | const h1 h2 h3 =>
    rename_i us'
    have hus : us' = [] := by simpa using h2.symm
    subst hus
    refine ⟨ci, hci, .const ``Nat.zero [], .const ``Nat [], ?_, ?_, ?_⟩
    · rw [hlp]; exact .const hconstz rfl huv
    · rw [hlp, hty]; exact .const h1 rfl h3
    · rw [hlp]
      have hh := VEnv.IsDefEq.constDF (env := env) (Γ := []) (uvars := 0) (ls := []) (ls' := [])
        hconstz (by simp) (by simp) huv .nil
      simp only [VExpr.instL, List.map_nil] at hh
      exact hh

/-! ### The rung -/

set_option linter.unusedVariables false in
/--
**Rung G1 is green.** For the `#erase` run recorded in `VerifyBench/Spikes/G1.lean`, the
emitted program is the lowered image of a specification environment that erases
`spikeZero`, and the answer of the source evaluation is reproduced by the emitted program
as the literal λ□ numeral `0` — `.construct natIid 0 []`, not `□` and not a stuck term.

Named binders, per A14: `P`, `htbl`, `hwt`, `hsafe` and `hrun` are class **D** (an
elaboration environment, a table copied out of it, a translation witness, a safety flag it
does not pin, a monadic run); `hbridge` carries the results waves W2–W4 prove; `hfo` awaits
W3's first-order predicate. `hcfg`, `hsup`, `hax` and the capstone's `hcb` are discharged
here, and so is the target-side evaluation, which is what pins the answer to the literal.
-/
theorem green_G1
    {lenv : Lean.Environment} {env : VEnv} {gw : Void IO.RealWorld → NameGenerator}
    {ve vv : VExpr} {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
    {w w' : Void IO.RealWorld} {inls : List Kername} {fo : Name → Prop}
    {v : Expr} {us : List VLevel} {idx : List VExpr}
    (P : ErasureSpec lenv env [] gw)
    (htbl : SourceTableAdequate lenv g1Table)
    (hsafe : TableSafe lenv g1Table)
    (hwt : TrExprS env [] [] eG1 ve)
    (hrun : Erasure.erase eG1 g1Config cctx ref w
      = .ok (.untyped g1Env (some g1Term), inls) w')
    (hbridge : ∃ Γspec t₀, ErasureBridge env g1Table.body? fo eG1 Γspec g1Env g1Term t₀)
    (hev : SEval env g1Table.body? [] fullFlags [] eG1 v)
    (hvwt : TrExprS env [] [] v vv)
    (hty : env.HasType 0 [] vv (VExpr.mkApps (.const ``Nat us) idx))
    (hfo : fo ``Nat) :
    ∃ (Γspec : GlobalDeclarations) (t₀ tv₀ : LBTerm),
      Erases env [] [] eG1 t₀
      ∧ ErasesEnv env g1Table.body? Γspec t₀
      ∧ Lower Γspec t₀ g1Term
      ∧ LowerEnv Γspec g1Env
      ∧ LBWfPeregrine g1Env g1Term
      ∧ Erases env [] [] v tv₀
      ∧ Lower Γspec tv₀ (.construct natIid 0 [])
      ∧ NoBox (.construct natIid 0 [])
      ∧ (∀ tv', Erases env [] [] v tv' → tv' = tv₀)
      ∧ WcbvEval g1Env eraseFlags g1Term (.construct natIid 0 []) := by
  obtain ⟨Γspec, t₀, her, herΓ, hlow, hlowΓ, hwf, hobs⟩ :=
    shipping_erase_correct_firstorder P htbl g1_configPinned
      (g1_compilerBodies P htbl hsafe) hwt g1_supported hrun g1_erasableAxioms hbridge
  obtain ⟨tv₀, tv, herv, hlowv, hnb, huniq, hevtgt⟩ :=
    hobs [] [] ``Nat us idx v vv rfl (fun i hi => absurd hi (by simp)) hev hvwt hty hfo
  have htv : tv = g1Answer := eval_deterministic hevtgt g1_eval
  subst htv
  exact ⟨Γspec, t₀, tv₀, her, herΓ, hlow, hlowΓ, hwf, herv, hlowv, hnb, huniq, g1_eval⟩

end LeanToLambdaBox.Green
