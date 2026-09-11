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
the body-less-reference check, the target evaluation — is settled by one.
-/

/-- Rung G1's subject: a closed nullary definition whose value is a constructor.
Declared at the root so that its kername is `rootKername "spikeZero"`, which is what the
emitted environment below records. -/
def spikeZero : Nat := Nat.zero

/-- Rung G2's subject: a `Nat` literal under a constructor. Under `nat := .peano` the
literal becomes a peano tower, so the rung's answer is one. -/
def spikeLit : Nat := Nat.succ 3

/-- Rung G3's subject: a `let`, which both semantics contract by ζ. -/
def spikeLet : Nat := let x := 2; Nat.succ x

/-- Rung G4's subject: a structure projection out of a pair, whose type parameters are
erased. -/
def spikeProj : Nat := (Prod.mk 1 2).1

namespace LeanToLambdaBox.Green

open Lean Lean4Lean Witness

/-! ## G1 — `spikeZero : Nat := Nat.zero` -/

/-- The configuration every rung is erased under: the one `ConfigPinned` describes. -/
def spikeConfig : Erasure.ErasureConfig :=
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

/-- The rungs' configuration is the pinned one. -/
theorem spike_configPinned : ConfigPinned spikeConfig := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The subject is inside the supported fragment, decided on the reified table.
The verdict is computed by the kernel: `String.isPrefixOf`, which `isMatcherName` calls,
does not reduce in the elaborator. -/
theorem g1_supported : supportedB g1Table 8 eG1 = .ok () := by
  have h : (supportedB g1Table 8 eG1).isOk = true := by decide +kernel
  cases hx : supportedB g1Table 8 eG1 with
  | ok u => cases u; rfl
  | error err => rw [hx] at h; exact Bool.noConfusion h

/-- Every constant the emitted program reaches is declared with a body. -/
theorem g1_noBodylessRefs : NoBodylessRefs g1Env g1Term := by decide +kernel

/-- The emitted program evaluates to the literal answer, by the certified evaluator. -/
theorem g1_eval : WcbvEval g1Env eraseFlags g1Term g1Answer :=
  lbEval_sound (n := 8) (by rfl)

/-! ### The compiler bodies, typed -/

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
    P.decl_adequate ``Nat.zero ciz hciz (hsafe.decls ``Nat.zero ciz rfl hciz)
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
emitted program is the lowered image of a specification environment that erases `spikeZero`,
and the source evaluation's answer is reproduced as the literal λ□ numeral `0` —
`.construct natIid 0 []`, not `□` and not a stuck term. `hcfg`, `hsup`, `hnb`, the capstone's
`hcb` and the target-side evaluation are discharged here by checked terms; every remaining
binder is a `doc/trust.md` row, `hev` among them, uninhabited until `green_G5`.
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
    (hrun : Erasure.erase eG1 spikeConfig cctx ref w
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
    shipping_erase_correct_firstorder P htbl spike_configPinned
      (g1_compilerBodies P htbl hsafe) hwt (supportedB_sound P htbl hsafe g1_supported)
      hrun g1_noBodylessRefs hbridge
  obtain ⟨tv₀, tv, herv, hlowv, hnobox, huniq, hevtgt⟩ :=
    hobs [] [] ``Nat us idx v vv rfl (fun i hi => absurd hi (by simp)) hev hvwt hty hfo
  have htv : tv = g1Answer := eval_deterministic hevtgt g1_eval
  subst htv
  exact ⟨Γspec, t₀, tv₀, her, herΓ, hlow, hlowΓ, hwf, herv, hlowv, hnobox, huniq, g1_eval⟩
/-! ## The shapes rungs G2-G4 share -/

/-- The λ□ peano numeral: `Nat.zero` under `n` applications of `Nat.succ`, applied form.
This is what `nat := .peano` emits for a `Nat` literal, so it is what a rung's literal
answer is written in. -/
def peanoLB : Nat → LBTerm
  | 0 => .construct natIid 0 []
  | n + 1 => .app (.construct natIid 1 []) (peanoLB n)

/-- `OfNat`'s λ□ inductive identifier. A `Nat` literal in source syntax is
`@OfNat.ofNat Nat n (instOfNatNat n)`, so the class comes along with the numeral. -/
def ofNatIid : InductiveId := ⟨rootKername "OfNat", 0⟩

/-- The kername of the class projection `OfNat.ofNat`. -/
def ofNatKn : Kername := ⟨.MPdot (.MPfile []) "OfNat", "ofNat"⟩

/-- The kername of the `Nat` instance `instOfNatNat`. -/
def instOfNatNatKn : Kername := rootKername "instOfNatNat"

/-- `OfNat`'s emitted inductive body: two parameters, one constructor of one field, one
projection. -/
def ofNatBody : MutualInductiveBody :=
  { npars := 2,
    bodies := [{ name := "OfNat", propositional := false, kelim := .IntoAny,
                 ctors := [{ name := "OfNat.mk", nargs := 1 }],
                 projs := [{ name := "0" }] }] }

/-- The emitted image of the source literal `n : Nat`: the class projection applied to the
erased type, the peano numeral and the instance. -/
def litLB (n : Nat) : LBTerm :=
  .app (.app (.app (.const ofNatKn) .box) (peanoLB n))
    (.app (.const instOfNatNatKn) (peanoLB n))

/-- The emitted declaration of `OfNat.ofNat`: two erased binders, then the field
projection out of the instance. -/
def ofNatDecl : Kername × GlobalDecl :=
  (ofNatKn, .constantDecl ⟨some
    (.lambda .anon (.lambda (.named "x._@.Init.Prelude.1822880135._hygCtx._hyg.3")
      (.lambda (.named "self") (.proj ⟨ofNatIid, 2, 0⟩ (.bvar 0)))))⟩)

/-- The emitted declaration of `instOfNatNat`: the numeral packed into an `OfNat.mk`. -/
def instOfNatNatDecl : Kername × GlobalDecl :=
  (instOfNatNatKn, .constantDecl ⟨some
    (.lambda (.named "n")
      (.app (.app (.app (.construct ofNatIid 0 []) .box) (.bvar 0)) (.bvar 0)))⟩)

/-! ## G2 — `spikeLit : Nat := Nat.succ 3` -/

/-- The reified slice of the elaboration environment rung G2 reads, spliced by `reify%`
out of the environment this module elaborates in. -/
def g2Table : SourceTable := reify% spikeLit

/-- The source term `#erase spikeLit` elaborates. -/
def eG2 : Expr := .const ``spikeLit []

/-- Rung G2's emitted environment, transcribed from `VerifyBench/ast/Spikes/G2.ast`. -/
def g2Env : GlobalDeclarations :=
  [ (rootKername "spikeLit", .constantDecl ⟨some
      (.app (.construct natIid 1 []) (litLB 3))⟩),
    instOfNatNatDecl,
    ofNatDecl,
    (rootKername "OfNat", .inductiveDecl ofNatBody),
    (rootKername "Nat", .inductiveDecl natBody) ]

/-- Rung G2's emitted term. -/
def g2Term : LBTerm := .const (rootKername "spikeLit")

/-- Rung G2's answer: the λ□ peano numeral `4`. -/
def g2Answer : LBTerm := peanoLB 4

/-- The subject is inside the supported fragment, decided on the reified table.
The verdict is computed by the kernel: `String.isPrefixOf`, which `isMatcherName` calls,
does not reduce in the elaborator. -/
theorem g2_supported : supportedB g2Table 8 eG2 = .ok () := by
  have h : (supportedB g2Table 8 eG2).isOk = true := by decide +kernel
  cases hx : supportedB g2Table 8 eG2 with
  | ok u => cases u; rfl
  | error err => rw [hx] at h; exact Bool.noConfusion h

/-- Every constant the emitted program reaches is declared with a body. -/
theorem g2_noBodylessRefs : NoBodylessRefs g2Env g2Term := by decide +kernel

/-- The emitted program evaluates to the literal answer, by the certified evaluator. -/
theorem g2_eval : WcbvEval g2Env eraseFlags g2Term g2Answer :=
  lbEval_sound (n := 16) (by rfl)

set_option linter.unusedVariables false in
/--
**Rung G2 is green.** For the `#erase` run recorded in `VerifyBench/Spikes/G2.lean`, the
emitted program is the lowered image of a specification environment that erases `spikeLit`,
and the source evaluation's answer is reproduced as the literal λ□ peano numeral `4`, not
`□` and not a stuck term. The peano tower and the `OfNat` class tower a literal brings are
both in the emitted program.
`hcfg`, `hsup`, `hnb` and the target-side evaluation are discharged here by checked terms;
`hcb` and `hev` stay binders, per `doc/trust.md`'s class-**C** rows.
-/
theorem green_G2
    {lenv : Lean.Environment} {env : VEnv} {gw : Void IO.RealWorld → NameGenerator}
    {ve vv : VExpr} {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
    {w w' : Void IO.RealWorld} {inls : List Kername} {fo : Name → Prop}
    {v : Expr} {us : List VLevel} {idx : List VExpr}
    (P : ErasureSpec lenv env [] gw)
    (htbl : SourceTableAdequate lenv g2Table)
    (hsafe : TableSafe lenv g2Table)
    (hcb : CompilerBodies lenv env g2Table.body?)
    (hwt : TrExprS env [] [] eG2 ve)
    (hrun : Erasure.erase eG2 spikeConfig cctx ref w
      = .ok (.untyped g2Env (some g2Term), inls) w')
    (hbridge : ∃ Γspec t₀, ErasureBridge env g2Table.body? fo eG2 Γspec g2Env g2Term t₀)
    (hev : SEval env g2Table.body? [] fullFlags [] eG2 v)
    (hvwt : TrExprS env [] [] v vv)
    (hty : env.HasType 0 [] vv (VExpr.mkApps (.const ``Nat us) idx))
    (hfo : fo ``Nat) :
    ∃ (Γspec : GlobalDeclarations) (t₀ tv₀ : LBTerm),
      Erases env [] [] eG2 t₀
      ∧ ErasesEnv env g2Table.body? Γspec t₀
      ∧ Lower Γspec t₀ g2Term
      ∧ LowerEnv Γspec g2Env
      ∧ LBWfPeregrine g2Env g2Term
      ∧ Erases env [] [] v tv₀
      ∧ Lower Γspec tv₀ (peanoLB 4)
      ∧ NoBox (peanoLB 4)
      ∧ (∀ tv', Erases env [] [] v tv' → tv' = tv₀)
      ∧ WcbvEval g2Env eraseFlags g2Term (peanoLB 4) := by
  obtain ⟨Γspec, t₀, her, herΓ, hlow, hlowΓ, hwf, hobs⟩ :=
    shipping_erase_correct_firstorder P htbl spike_configPinned hcb hwt
      (supportedB_sound P htbl hsafe g2_supported) hrun g2_noBodylessRefs hbridge
  obtain ⟨tv₀, tv, herv, hlowv, hnobox, huniq, hevtgt⟩ :=
    hobs [] [] ``Nat us idx v vv rfl (fun i hi => absurd hi (by simp)) hev hvwt hty hfo
  have htv : tv = g2Answer := eval_deterministic hevtgt g2_eval
  subst htv
  exact ⟨Γspec, t₀, tv₀, her, herΓ, hlow, hlowΓ, hwf, herv, hlowv, hnobox, huniq, g2_eval⟩

/-! ## G3 — `spikeLet : Nat := let x := 2; Nat.succ x` -/

/-- The reified slice of the elaboration environment rung G3 reads, spliced by `reify%`
out of the environment this module elaborates in. -/
def g3Table : SourceTable := reify% spikeLet

/-- The source term `#erase spikeLet` elaborates. -/
def eG3 : Expr := .const ``spikeLet []

/-- Rung G3's emitted environment, transcribed from `VerifyBench/ast/Spikes/G3.ast`. -/
def g3Env : GlobalDeclarations :=
  [ (rootKername "spikeLet", .constantDecl ⟨some
      (.letIn (.named "x") (litLB 2) (.app (.construct natIid 1 []) (.bvar 0)))⟩),
    instOfNatNatDecl,
    (rootKername "Nat", .inductiveDecl natBody),
    ofNatDecl,
    (rootKername "OfNat", .inductiveDecl ofNatBody) ]

/-- Rung G3's emitted term. -/
def g3Term : LBTerm := .const (rootKername "spikeLet")

/-- Rung G3's answer: the λ□ peano numeral `3`. -/
def g3Answer : LBTerm := peanoLB 3

/-- The subject is inside the supported fragment, decided on the reified table.
The verdict is computed by the kernel: `String.isPrefixOf`, which `isMatcherName` calls,
does not reduce in the elaborator. -/
theorem g3_supported : supportedB g3Table 8 eG3 = .ok () := by
  have h : (supportedB g3Table 8 eG3).isOk = true := by decide +kernel
  cases hx : supportedB g3Table 8 eG3 with
  | ok u => cases u; rfl
  | error err => rw [hx] at h; exact Bool.noConfusion h

/-- Every constant the emitted program reaches is declared with a body. -/
theorem g3_noBodylessRefs : NoBodylessRefs g3Env g3Term := by decide +kernel

/-- The emitted program evaluates to the literal answer, by the certified evaluator. -/
theorem g3_eval : WcbvEval g3Env eraseFlags g3Term g3Answer :=
  lbEval_sound (n := 16) (by rfl)

set_option linter.unusedVariables false in
/--
**Rung G3 is green.** For the `#erase` run recorded in `VerifyBench/Spikes/G3.lean`, the
emitted program is the lowered image of a specification environment that erases `spikeLet`,
and the source evaluation's answer is reproduced as the literal λ□ peano numeral `3`, not
`□` and not a stuck term. The `let` is contracted by ζ on both sides.
`hcfg`, `hsup`, `hnb` and the target-side evaluation are discharged here by checked terms;
`hcb` and `hev` stay binders, per `doc/trust.md`'s class-**C** rows.
-/
theorem green_G3
    {lenv : Lean.Environment} {env : VEnv} {gw : Void IO.RealWorld → NameGenerator}
    {ve vv : VExpr} {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
    {w w' : Void IO.RealWorld} {inls : List Kername} {fo : Name → Prop}
    {v : Expr} {us : List VLevel} {idx : List VExpr}
    (P : ErasureSpec lenv env [] gw)
    (htbl : SourceTableAdequate lenv g3Table)
    (hsafe : TableSafe lenv g3Table)
    (hcb : CompilerBodies lenv env g3Table.body?)
    (hwt : TrExprS env [] [] eG3 ve)
    (hrun : Erasure.erase eG3 spikeConfig cctx ref w
      = .ok (.untyped g3Env (some g3Term), inls) w')
    (hbridge : ∃ Γspec t₀, ErasureBridge env g3Table.body? fo eG3 Γspec g3Env g3Term t₀)
    (hev : SEval env g3Table.body? [] fullFlags [] eG3 v)
    (hvwt : TrExprS env [] [] v vv)
    (hty : env.HasType 0 [] vv (VExpr.mkApps (.const ``Nat us) idx))
    (hfo : fo ``Nat) :
    ∃ (Γspec : GlobalDeclarations) (t₀ tv₀ : LBTerm),
      Erases env [] [] eG3 t₀
      ∧ ErasesEnv env g3Table.body? Γspec t₀
      ∧ Lower Γspec t₀ g3Term
      ∧ LowerEnv Γspec g3Env
      ∧ LBWfPeregrine g3Env g3Term
      ∧ Erases env [] [] v tv₀
      ∧ Lower Γspec tv₀ (peanoLB 3)
      ∧ NoBox (peanoLB 3)
      ∧ (∀ tv', Erases env [] [] v tv' → tv' = tv₀)
      ∧ WcbvEval g3Env eraseFlags g3Term (peanoLB 3) := by
  obtain ⟨Γspec, t₀, her, herΓ, hlow, hlowΓ, hwf, hobs⟩ :=
    shipping_erase_correct_firstorder P htbl spike_configPinned hcb hwt
      (supportedB_sound P htbl hsafe g3_supported) hrun g3_noBodylessRefs hbridge
  obtain ⟨tv₀, tv, herv, hlowv, hnobox, huniq, hevtgt⟩ :=
    hobs [] [] ``Nat us idx v vv rfl (fun i hi => absurd hi (by simp)) hev hvwt hty hfo
  have htv : tv = g3Answer := eval_deterministic hevtgt g3_eval
  subst htv
  exact ⟨Γspec, t₀, tv₀, her, herΓ, hlow, hlowΓ, hwf, herv, hlowv, hnobox, huniq, g3_eval⟩

/-- `Prod`'s λ□ inductive identifier. -/
def prodIid : InductiveId := ⟨rootKername "Prod", 0⟩

/-- The kername of the first projection `Prod.fst`. -/
def prodFstKn : Kername := ⟨.MPdot (.MPfile []) "Prod", "fst"⟩

/-- `Prod`'s emitted inductive body: two parameters, one constructor of two fields, two
projections. -/
def prodBody : MutualInductiveBody :=
  { npars := 2,
    bodies := [{ name := "Prod", propositional := false, kelim := .IntoAny,
                 ctors := [{ name := "Prod.mk", nargs := 2 }],
                 projs := [{ name := "0" }, { name := "1" }] }] }

/-! ## G4 — `spikeProj : Nat := (Prod.mk 1 2).1` -/

/-- The reified slice of the elaboration environment rung G4 reads, spliced by `reify%`
out of the environment this module elaborates in. -/
def g4Table : SourceTable := reify% spikeProj

/-- The source term `#erase spikeProj` elaborates. -/
def eG4 : Expr := .const ``spikeProj []

/-- Rung G4's emitted environment, transcribed from `VerifyBench/ast/Spikes/G4.ast`. -/
def g4Env : GlobalDeclarations :=
  [ (rootKername "spikeProj", .constantDecl ⟨some
      (.app (.app (.app (.const prodFstKn) .box) .box)
        (.app (.app (.app (.app (.construct prodIid 0 []) .box) .box) (litLB 1)) (litLB 2)))⟩),
    instOfNatNatDecl,
    (rootKername "Nat", .inductiveDecl natBody),
    ofNatDecl,
    (rootKername "OfNat", .inductiveDecl ofNatBody),
    (prodFstKn, .constantDecl ⟨some
      (.lambda .anon (.lambda .anon
        (.lambda (.named "self") (.proj ⟨prodIid, 2, 0⟩ (.bvar 0)))))⟩),
    (rootKername "Prod", .inductiveDecl prodBody) ]

/-- Rung G4's emitted term. -/
def g4Term : LBTerm := .const (rootKername "spikeProj")

/-- Rung G4's answer: the λ□ peano numeral `1`. -/
def g4Answer : LBTerm := peanoLB 1

/-- The subject is inside the supported fragment, decided on the reified table.
The verdict is computed by the kernel: `String.isPrefixOf`, which `isMatcherName` calls,
does not reduce in the elaborator. -/
theorem g4_supported : supportedB g4Table 8 eG4 = .ok () := by
  have h : (supportedB g4Table 8 eG4).isOk = true := by decide +kernel
  cases hx : supportedB g4Table 8 eG4 with
  | ok u => cases u; rfl
  | error err => rw [hx] at h; exact Bool.noConfusion h

/-- Every constant the emitted program reaches is declared with a body. -/
theorem g4_noBodylessRefs : NoBodylessRefs g4Env g4Term := by decide +kernel

/-- The emitted program evaluates to the literal answer, by the certified evaluator. -/
theorem g4_eval : WcbvEval g4Env eraseFlags g4Term g4Answer :=
  lbEval_sound (n := 16) (by rfl)

set_option linter.unusedVariables false in
/--
**Rung G4 is green.** For the `#erase` run recorded in `VerifyBench/Spikes/G4.lean`, the
emitted program is the lowered image of a specification environment that erases `spikeProj`,
and the source evaluation's answer is reproduced as the literal λ□ peano numeral `1`, not
`□` and not a stuck term. The projection is taken on both sides and the pair's two type
parameters are erased.
`hcfg`, `hsup`, `hnb` and the target-side evaluation are discharged here by checked terms;
`hcb` and `hev` stay binders, per `doc/trust.md`'s class-**C** rows.
-/
theorem green_G4
    {lenv : Lean.Environment} {env : VEnv} {gw : Void IO.RealWorld → NameGenerator}
    {ve vv : VExpr} {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
    {w w' : Void IO.RealWorld} {inls : List Kername} {fo : Name → Prop}
    {v : Expr} {us : List VLevel} {idx : List VExpr}
    (P : ErasureSpec lenv env [] gw)
    (htbl : SourceTableAdequate lenv g4Table)
    (hsafe : TableSafe lenv g4Table)
    (hcb : CompilerBodies lenv env g4Table.body?)
    (hwt : TrExprS env [] [] eG4 ve)
    (hrun : Erasure.erase eG4 spikeConfig cctx ref w
      = .ok (.untyped g4Env (some g4Term), inls) w')
    (hbridge : ∃ Γspec t₀, ErasureBridge env g4Table.body? fo eG4 Γspec g4Env g4Term t₀)
    (hev : SEval env g4Table.body? [] fullFlags [] eG4 v)
    (hvwt : TrExprS env [] [] v vv)
    (hty : env.HasType 0 [] vv (VExpr.mkApps (.const ``Nat us) idx))
    (hfo : fo ``Nat) :
    ∃ (Γspec : GlobalDeclarations) (t₀ tv₀ : LBTerm),
      Erases env [] [] eG4 t₀
      ∧ ErasesEnv env g4Table.body? Γspec t₀
      ∧ Lower Γspec t₀ g4Term
      ∧ LowerEnv Γspec g4Env
      ∧ LBWfPeregrine g4Env g4Term
      ∧ Erases env [] [] v tv₀
      ∧ Lower Γspec tv₀ (peanoLB 1)
      ∧ NoBox (peanoLB 1)
      ∧ (∀ tv', Erases env [] [] v tv' → tv' = tv₀)
      ∧ WcbvEval g4Env eraseFlags g4Term (peanoLB 1) := by
  obtain ⟨Γspec, t₀, her, herΓ, hlow, hlowΓ, hwf, hobs⟩ :=
    shipping_erase_correct_firstorder P htbl spike_configPinned hcb hwt
      (supportedB_sound P htbl hsafe g4_supported) hrun g4_noBodylessRefs hbridge
  obtain ⟨tv₀, tv, herv, hlowv, hnobox, huniq, hevtgt⟩ :=
    hobs [] [] ``Nat us idx v vv rfl (fun i hi => absurd hi (by simp)) hev hvwt hty hfo
  have htv : tv = g4Answer := eval_deterministic hevtgt g4_eval
  subst htv
  exact ⟨Γspec, t₀, tv₀, her, herΓ, hlow, hlowΓ, hwf, herv, hlowv, hnobox, huniq, g4_eval⟩

end LeanToLambdaBox.Green
