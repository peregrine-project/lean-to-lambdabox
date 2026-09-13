import LeanToLambdaBox.Capstone
import LeanToLambdaBox.Witness.TrWitness
import VerifyBench.Src.Arith

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

/-- Rung G5's subject: a `casesOn` applied to a constructor value — an ι redex on both
sides. The nullary branch is a thunk application, the shape Lean's `match` compiler gives a
nullary alternative, so the branch obligation the ι rule owes is the one a compiled `match`
owes. Spelled with `Nat.casesOn` rather than `match`, which puts the ι redex in the subject
instead of behind a matcher constant. -/
def spikeCase : Nat :=
  Nat.casesOn (motive := fun _x => Nat) (Nat.succ (Nat.succ Nat.zero))
    ((fun _u : Unit => Nat.zero) Unit.unit) (fun n => n)

/-- Rung G6's recursive constant: it erases to a `.fix` node, and its body is the same ι
redex on the argument, spelled with `Nat.casesOn` for the reason `spikeCase` is. -/
def spikeRec : Nat → Nat := fun n =>
  Nat.casesOn (motive := fun _x => Nat) n Nat.zero (fun m => Nat.succ (spikeRec m))

/-- Rung G6's subject: an application of a recursive constant, hence δ on a `.fix`. -/
def spikeFix : Nat := spikeRec (Nat.succ (Nat.succ Nat.zero))

/-- Rung G7's subject: the tracked benchmark program `benchArith` at `0`, a closed nullary
definition whose value is `2 ^ 3 = 8`. Its erasure pulls in the arithmetic typeclass tower —
ten projections, four `fix` blocks, five `.case` nodes — so it is the ladder's first rung at
the scale of a real program. -/
def arithClosed : Nat := benchArith 0

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
`.construct natIid 0 []`, not `□` and not a stuck term. `hcfg`, `hsup`, `hnb`, `hwt`, the capstone's
`hcb` and the target-side evaluation are discharged here by checked terms; every remaining
binder is a `doc/trust.md` row, `hev` among them, which `green_G5` is the first rung to
inhabit.
-/
theorem green_G1
    {lenv : Lean.Environment} {env : VEnv} {gw : Void IO.RealWorld → NameGenerator}
    {vv : VExpr} {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
    {w wp w' : Void IO.RealWorld} {inls : List Kername}
    {v : Expr} {us : List VLevel} {idx : List VExpr}
    (P : ErasureSpec lenv env [] gw)
    (htbl : SourceTableAdequate lenv g1Table)
    (hsafe : TableSafe lenv g1Table)
    (E : EraserAsks lenv env [] gw)
    (A : UpstreamAsks env)
    (hblk : TableBlocks lenv env g1Table)
    (hve : VisitExprRunConcl env gw)
    (hprep : Erasure.prepare_erasure eG1 {} { «config» := spikeConfig } cctx ref w
      = .ok (eG1, {}) wp)
    (hrun : Erasure.erase eG1 spikeConfig cctx ref w
      = .ok (.untyped g1Env (some g1Term), inls) w')
    (hbridge : ∀ (sf : Erasure.ErasureState) (wt : Void IO.RealWorld),
      Erasure.visitExpr eG1 {} { «config» := spikeConfig } cctx ref wp = .ok (g1Term, sf) wt →
      ∃ Γspec : GlobalDeclarations, SpecEnv env g1Table.body? sf Γspec ∧
        ∀ t₀ : LBTerm, Erases env [] [] eG1 t₀ → Lower Γspec t₀ g1Term →
          ErasureBridge env g1Table.body? Γspec g1Env g1Term t₀)
    (hev : SEval env g1Table.body? [] fullFlags [] eG1 v)
    (hvwt : TrExprS env [] [] v vv)
    (hty : env.HasType 0 [] vv (VExpr.mkApps (.const ``Nat us) idx))
    (hfo : FirstOrderInd env ``Nat) :
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
  obtain ⟨Γspec, t₀, -, her, herΓ, hlow, hlowΓ, hwf, hobs⟩ :=
    shipping_erase_correct_firstorder P E A htbl hsafe hblk spike_configPinned
      (g1_compilerBodies P htbl hsafe) hve
      (trExprS_const_of_table P htbl hsafe rfl)
      (supportedB_sound P htbl hsafe g1_supported)
      hprep hrun g1_noBodylessRefs hbridge
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

/-- The emitted inductive body of a single-field class: `npars` parameters, the constructor
`<name>.mk` of one field, and that field's projection. Every class a rung's closure declares
— `OfNat` here, the whole arithmetic tower at G7 — has this shape. -/
def classBody (name : String) (npars : Nat) : MutualInductiveBody :=
  { npars := npars,
    bodies := [{ name := name, propositional := false, kelim := .IntoAny,
                 ctors := [{ name := name ++ ".mk", nargs := 1 }],
                 projs := [{ name := "0" }] }] }

/-- `OfNat`'s emitted inductive body: two parameters, one constructor of one field, one
projection. -/
def ofNatBody : MutualInductiveBody := classBody "OfNat" 2

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
`hcfg`, `hsup`, `hnb`, `hwt` and the target-side evaluation are discharged here by checked
terms; `hcb` and `hev` stay binders, per `doc/trust.md`'s class-**C** rows.
-/
theorem green_G2
    {lenv : Lean.Environment} {env : VEnv} {gw : Void IO.RealWorld → NameGenerator}
    {vv : VExpr} {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
    {w wp w' : Void IO.RealWorld} {inls : List Kername}
    {v : Expr} {us : List VLevel} {idx : List VExpr}
    (P : ErasureSpec lenv env [] gw)
    (htbl : SourceTableAdequate lenv g2Table)
    (hsafe : TableSafe lenv g2Table)
    (E : EraserAsks lenv env [] gw)
    (A : UpstreamAsks env)
    (hblk : TableBlocks lenv env g2Table)
    (hve : VisitExprRunConcl env gw)
    (hcb : CompilerBodies lenv env g2Table.body?)
    (hprep : Erasure.prepare_erasure eG2 {} { «config» := spikeConfig } cctx ref w
      = .ok (eG2, {}) wp)
    (hrun : Erasure.erase eG2 spikeConfig cctx ref w
      = .ok (.untyped g2Env (some g2Term), inls) w')
    (hbridge : ∀ (sf : Erasure.ErasureState) (wt : Void IO.RealWorld),
      Erasure.visitExpr eG2 {} { «config» := spikeConfig } cctx ref wp = .ok (g2Term, sf) wt →
      ∃ Γspec : GlobalDeclarations, SpecEnv env g2Table.body? sf Γspec ∧
        ∀ t₀ : LBTerm, Erases env [] [] eG2 t₀ → Lower Γspec t₀ g2Term →
          ErasureBridge env g2Table.body? Γspec g2Env g2Term t₀)
    (hev : SEval env g2Table.body? [] fullFlags [] eG2 v)
    (hvwt : TrExprS env [] [] v vv)
    (hty : env.HasType 0 [] vv (VExpr.mkApps (.const ``Nat us) idx))
    (hfo : FirstOrderInd env ``Nat) :
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
  obtain ⟨Γspec, t₀, -, her, herΓ, hlow, hlowΓ, hwf, hobs⟩ :=
    shipping_erase_correct_firstorder P E A htbl hsafe hblk spike_configPinned hcb
      hve (trExprS_const_of_table P htbl hsafe rfl)
      (supportedB_sound P htbl hsafe g2_supported) hprep hrun g2_noBodylessRefs hbridge
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
`hcfg`, `hsup`, `hnb`, `hwt` and the target-side evaluation are discharged here by checked
terms; `hcb` and `hev` stay binders, per `doc/trust.md`'s class-**C** rows.
-/
theorem green_G3
    {lenv : Lean.Environment} {env : VEnv} {gw : Void IO.RealWorld → NameGenerator}
    {vv : VExpr} {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
    {w wp w' : Void IO.RealWorld} {inls : List Kername}
    {v : Expr} {us : List VLevel} {idx : List VExpr}
    (P : ErasureSpec lenv env [] gw)
    (htbl : SourceTableAdequate lenv g3Table)
    (hsafe : TableSafe lenv g3Table)
    (E : EraserAsks lenv env [] gw)
    (A : UpstreamAsks env)
    (hblk : TableBlocks lenv env g3Table)
    (hve : VisitExprRunConcl env gw)
    (hcb : CompilerBodies lenv env g3Table.body?)
    (hprep : Erasure.prepare_erasure eG3 {} { «config» := spikeConfig } cctx ref w
      = .ok (eG3, {}) wp)
    (hrun : Erasure.erase eG3 spikeConfig cctx ref w
      = .ok (.untyped g3Env (some g3Term), inls) w')
    (hbridge : ∀ (sf : Erasure.ErasureState) (wt : Void IO.RealWorld),
      Erasure.visitExpr eG3 {} { «config» := spikeConfig } cctx ref wp = .ok (g3Term, sf) wt →
      ∃ Γspec : GlobalDeclarations, SpecEnv env g3Table.body? sf Γspec ∧
        ∀ t₀ : LBTerm, Erases env [] [] eG3 t₀ → Lower Γspec t₀ g3Term →
          ErasureBridge env g3Table.body? Γspec g3Env g3Term t₀)
    (hev : SEval env g3Table.body? [] fullFlags [] eG3 v)
    (hvwt : TrExprS env [] [] v vv)
    (hty : env.HasType 0 [] vv (VExpr.mkApps (.const ``Nat us) idx))
    (hfo : FirstOrderInd env ``Nat) :
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
  obtain ⟨Γspec, t₀, -, her, herΓ, hlow, hlowΓ, hwf, hobs⟩ :=
    shipping_erase_correct_firstorder P E A htbl hsafe hblk spike_configPinned hcb
      hve (trExprS_const_of_table P htbl hsafe rfl)
      (supportedB_sound P htbl hsafe g3_supported) hprep hrun g3_noBodylessRefs hbridge
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
`hcfg`, `hsup`, `hnb`, `hwt` and the target-side evaluation are discharged here by checked
terms; `hcb` and `hev` stay binders, per `doc/trust.md`'s class-**C** rows.
-/
theorem green_G4
    {lenv : Lean.Environment} {env : VEnv} {gw : Void IO.RealWorld → NameGenerator}
    {vv : VExpr} {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
    {w wp w' : Void IO.RealWorld} {inls : List Kername}
    {v : Expr} {us : List VLevel} {idx : List VExpr}
    (P : ErasureSpec lenv env [] gw)
    (htbl : SourceTableAdequate lenv g4Table)
    (hsafe : TableSafe lenv g4Table)
    (E : EraserAsks lenv env [] gw)
    (A : UpstreamAsks env)
    (hblk : TableBlocks lenv env g4Table)
    (hve : VisitExprRunConcl env gw)
    (hcb : CompilerBodies lenv env g4Table.body?)
    (hprep : Erasure.prepare_erasure eG4 {} { «config» := spikeConfig } cctx ref w
      = .ok (eG4, {}) wp)
    (hrun : Erasure.erase eG4 spikeConfig cctx ref w
      = .ok (.untyped g4Env (some g4Term), inls) w')
    (hbridge : ∀ (sf : Erasure.ErasureState) (wt : Void IO.RealWorld),
      Erasure.visitExpr eG4 {} { «config» := spikeConfig } cctx ref wp = .ok (g4Term, sf) wt →
      ∃ Γspec : GlobalDeclarations, SpecEnv env g4Table.body? sf Γspec ∧
        ∀ t₀ : LBTerm, Erases env [] [] eG4 t₀ → Lower Γspec t₀ g4Term →
          ErasureBridge env g4Table.body? Γspec g4Env g4Term t₀)
    (hev : SEval env g4Table.body? [] fullFlags [] eG4 v)
    (hvwt : TrExprS env [] [] v vv)
    (hty : env.HasType 0 [] vv (VExpr.mkApps (.const ``Nat us) idx))
    (hfo : FirstOrderInd env ``Nat) :
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
  obtain ⟨Γspec, t₀, -, her, herΓ, hlow, hlowΓ, hwf, hobs⟩ :=
    shipping_erase_correct_firstorder P E A htbl hsafe hblk spike_configPinned hcb
      hve (trExprS_const_of_table P htbl hsafe rfl)
      (supportedB_sound P htbl hsafe g4_supported) hprep hrun g4_noBodylessRefs hbridge
  obtain ⟨tv₀, tv, herv, hlowv, hnobox, huniq, hevtgt⟩ :=
    hobs [] [] ``Nat us idx v vv rfl (fun i hi => absurd hi (by simp)) hev hvwt hty hfo
  have htv : tv = g4Answer := eval_deterministic hevtgt g4_eval
  subst htv
  exact ⟨Γspec, t₀, tv₀, her, herΓ, hlow, hlowΓ, hwf, herv, hlowv, hnobox, huniq, g4_eval⟩

/-! ## G5 — `spikeCase`, the first ι rung -/

/-- The reified slice of the elaboration environment rung G5 reads, spliced by `reify%`
out of the environment this module elaborates in. -/
def g5Table : SourceTable := reify% spikeCase

/-- The source term `#erase spikeCase` elaborates. -/
def eG5 : Expr := .const ``spikeCase []

/-- `PUnit`'s λ□ inductive identifier: the thunk's argument type. -/
def punitIid : InductiveId := ⟨rootKername "PUnit", 0⟩

/-- The kername of `Unit.unit`, the thunk's argument. -/
def unitUnitKn : Kername := ⟨.MPdot (.MPfile []) "Unit", "unit"⟩

/-- `PUnit`'s emitted inductive body: one nullary constructor, no parameters. -/
def punitBody : MutualInductiveBody :=
  { npars := 0,
    bodies := [{ name := "PUnit", propositional := false, kelim := .IntoAny,
                 ctors := [{ name := "PUnit.unit", nargs := 0 }],
                 projs := [] }] }

/-- Rung G5's emitted environment, transcribed from `VerifyBench/ast/Spikes/G5.ast`. -/
def g5Env : GlobalDeclarations :=
  [ (rootKername "spikeCase", .constantDecl ⟨some
      (.case (natIid, 0) (peanoLB 2)
        [([], .app (.lambda (.named "_u") (.construct natIid 0 [])) (.const unitUnitKn)),
         ([.named "n"], .bvar 0)])⟩),
    (unitUnitKn, .constantDecl ⟨some (.construct punitIid 0 [])⟩),
    (rootKername "PUnit", .inductiveDecl punitBody),
    (rootKername "Nat", .inductiveDecl natBody) ]

/-- Rung G5's emitted term. -/
def g5Term : LBTerm := .const (rootKername "spikeCase")

/-- Rung G5's answer: the λ□ peano numeral `1`. -/
def g5Answer : LBTerm := peanoLB 1

/-- The subject is inside the supported fragment, decided on the reified table.
The verdict is computed by the kernel: `String.isPrefixOf`, which `isMatcherName` calls,
does not reduce in the elaborator. -/
theorem g5_supported : supportedB g5Table 8 eG5 = .ok () := by
  have h : (supportedB g5Table 8 eG5).isOk = true := by decide +kernel
  cases hx : supportedB g5Table 8 eG5 with
  | ok u => cases u; rfl
  | error err => rw [hx] at h; exact Bool.noConfusion h

/-- Every constant the emitted program reaches is declared with a body. -/
theorem g5_noBodylessRefs : NoBodylessRefs g5Env g5Term := by decide +kernel

/-- The emitted program evaluates to the literal answer, by the certified evaluator. -/
theorem g5_eval : WcbvEval g5Env eraseFlags g5Term g5Answer :=
  lbEval_sound (n := 16) (by rfl)

/-! ### The source evaluation, constructed

`hev` is a hypothesis at every rung below this one. Here it is a term: the peano numerals
in constructor form, the δ step at the subject, the thunked nullary branch and the ι step
are each built, so the answer the rung reports is computed by the source semantics rather
than assumed of it. What the derivation still reads off `env` is `SpikeNatFacts` and three
`StepDefeq`s — the block data upstream ask 3 transports and the kernel's own reductions. -/

/-- A peano numeral in source constructor form. -/
def peanoSrc : Nat → Expr
  | 0 => .const ``Nat.zero []
  | n + 1 => .app (.const ``Nat.succ []) (peanoSrc n)

/-- The motive of rung G5's eliminator spine. -/
def g5Motive : Expr := .lam `_x (.const ``Nat []) (.const ``Nat []) .default

/-- The nullary branch, as a thunk applied to `Unit.unit`. -/
def g5Minor0 : Expr :=
  .app (.lam `_u (.const ``Unit []) (.const ``Nat.zero []) .default) (.const ``Unit.unit [])

/-- The successor branch. -/
def g5Minor1 : Expr := .lam `n (.const ``Nat []) (.bvar 0) .default

/-- The tabled body of rung G5's subject: the eliminator spine the ι rule splits. -/
def g5Body : Expr :=
  mkApps (.const ``Nat.casesOn [.succ .zero]) [g5Motive, peanoSrc 2, g5Minor0, g5Minor1]

/-- The tabled body of rung G5's subject is that spine. -/
theorem g5_body_eq : g5Table.body? ``spikeCase = some g5Body := rfl

/-- The tabled body of the thunk's argument is the constructor constant. -/
theorem g5_unit_body_eq :
    g5Table.body? ``Unit.unit = some (.const ``PUnit.unit [.succ .zero]) := rfl

/-- How `env` declares what rung G5's evaluation steps on at `Nat`: the type, its two
constructors, `Nat.casesOn` as a plain constant with the segmentation the ι rule splits at,
and that `Nat` eliminates into data. Each is a datum the reified table records for `lenv`,
read in the model; the transport is upstream ask 3's, so the bundle is a binder here rather
than a theorem. -/
structure SpikeNatFacts (env : VEnv) (ni : InductiveId) : Prop where
  /-- `Nat` is declared with no parameters and two constructors of zero and one field. -/
  natInd : IndInfo env ``Nat ni 0 [0, 1]
  /-- `Nat.zero` is `Nat`'s constructor 0. -/
  natZero : CtorOf env ``Nat.zero ``Nat 0
  /-- `Nat.succ` is `Nat`'s constructor 1. -/
  natSucc : CtorOf env ``Nat.succ ``Nat 1
  /-- `Nat.casesOn` takes one argument before the major premise and two minors. -/
  natCases : CasesOnShape env ``Nat.casesOn ``Nat 1 2
  /-- `Nat.casesOn` is declared as a plain constant, which is what the ι rule's `ho` is. -/
  natCasesOrigin : ConstOrigin env ``Nat.casesOn
  /-- `Nat` eliminates into data: its result sort is never zero, which is the ι rule's
      `hinf` and the restriction N18 the source relations model. -/
  natInf : InformativeInd env ``Nat

/-- **The `Nat` half of the bundle is satisfiable.** `SourceEval.lean`'s `NatWitness` builds a
pats-carrying `VEnv.WF'` declaring `Nat`, its constructors, its recursor and `Nat.casesOn`,
and every field is one of that fixture's own theorems. -/
theorem spikeNatFacts_natEnv : SpikeNatFacts NatWitness.natEnv NatWitness.natIid :=
  ⟨NatWitness.nat_indInfo, NatWitness.nat_ctorOf_zero, NatWitness.nat_ctorOf_succ,
    NatWitness.nat_casesOnShape, NatWitness.nat_constOrigin_cas,
    NatWitness.nat_informativeInd⟩

/-- How `env` declares the thunk's argument type: the second block rung G5's nullary branch
reaches. Separate from `SpikeNatFacts` because `NatWitness` declares one block, so the two
halves of the bundle are satisfiable at different fixtures. -/
structure SpikeUnitFacts (env : VEnv) (pi : InductiveId) : Prop where
  /-- `PUnit` is declared with no parameters and one nullary constructor. -/
  punitInd : IndInfo env ``PUnit pi 0 [0]
  /-- `PUnit.unit` is `PUnit`'s constructor 0. -/
  punitUnit : CtorOf env ``PUnit.unit ``PUnit 0

/-- Every peano numeral in constructor form is a value: each spine is within its
constructor's arity, so `SEval.ctorVal` applies at every level. -/
theorem peanoSrc_eval {env : VEnv} {ni : InductiveId} (F : SpikeNatFacts env ni)
    {bo : Name → Option Expr} {Us : List Name} {fl : SEvalFlags} :
    ∀ n, SEval env bo Us fl [] (peanoSrc n) (peanoSrc n)
  | 0 => .ctorVal (args := []) (argsv := []) F.natZero F.natInd (by decide) rfl
      (fun i hi => absurd hi (by simp))
  | n + 1 => .ctorVal (args := [peanoSrc n]) (argsv := [peanoSrc n]) F.natSucc F.natInd
      (by simp) rfl (fun i hi => by
        obtain rfl : i = 0 := by simp at hi; omega
        exact peanoSrc_eval F n)

/-- The subject is no eliminator, so δ on it is the only step available. -/
theorem not_casesOn_spikeCase {env : VEnv} :
    ∀ I dp nm, ¬ CasesOnShape env ``spikeCase I dp nm :=
  fun _ _ _ h => absurd h.1 (by decide)

/-- The thunk's argument is no eliminator either. -/
theorem not_casesOn_unitUnit {env : VEnv} :
    ∀ I dp nm, ¬ CasesOnShape env ``Unit.unit I dp nm :=
  fun _ _ _ h => absurd h.1 (by decide)

/-- **Rung G5's source evaluation, as a derivation.** δ at the subject, then ι at
`Nat.casesOn`: the discriminant is a constructor value, the selected branch is applied to
its field, and — the obligation the ι rule owes and a compiled `match` makes visible — the
*unselected* nullary branch is evaluated too, through its thunk and the δ step at
`Unit.unit` that thunk's argument needs. -/
theorem g5_seval {env : VEnv} {ni pi : InductiveId} (F : SpikeNatFacts env ni)
    (U : SpikeUnitFacts env pi)
    (hd : StepDefeq env [] [] eG5 g5Body)
    (hdu : StepDefeq env [] [] (.const ``Unit.unit []) (.const ``PUnit.unit [.succ .zero]))
    (hio : StepDefeq env [] [] g5Body (mkApps g5Minor1 [peanoSrc 1])) :
    SEval env g5Table.body? [] fullFlags [] eG5 (peanoSrc 1) := by
  have hunit : SEval env g5Table.body? [] fullFlags []
      (.const ``Unit.unit []) (.const ``PUnit.unit [.succ .zero]) :=
    .deltaC (c := ``Unit.unit) (us := []) (ups := []) (args := []) (argsv := [])
      (b := .const ``PUnit.unit [.succ .zero]) (b' := .const ``PUnit.unit [.succ .zero])
      rfl g5_unit_body_eq not_casesOn_unitUnit rfl rfl (fun i hi => absurd hi (by simp)) hdu
      (.ctorVal (args := []) (argsv := []) U.punitUnit U.punitInd (by decide) rfl
        (fun i hi => absurd hi (by simp)))
  have hmin0 : SEval env g5Table.body? [] fullFlags [] g5Minor0 (.const ``Nat.zero []) :=
    .beta rfl (.lam _ _ _ _) hunit (peanoSrc_eval F 0)
  have hcont : SEval env g5Table.body? [] fullFlags []
      (mkApps g5Minor1 [peanoSrc 1]) (peanoSrc 1) :=
    .beta rfl (.lam _ _ _ _) (peanoSrc_eval F 1) (peanoSrc_eval F 1)
  refine SEval.deltaC (c := ``spikeCase) (us := []) (ups := []) (args := []) (argsv := [])
    (b := g5Body) (b' := g5Body) rfl g5_body_eq not_casesOn_spikeCase rfl rfl
    (fun i hi => absurd hi (by simp)) hd ?_
  refine SEval.iota (con := ``Nat.casesOn) (I := ``Nat) (ctor := ``Nat.succ)
    (us := [.succ .zero]) (cus := []) (pre := [g5Motive]) (prev := [g5Motive])
    (minors := [g5Minor0, g5Minor1]) (minorsv := [.const ``Nat.zero [], g5Minor1])
    (extra := []) (extrav := []) (cargs := [peanoSrc 1]) (disc := peanoSrc 2)
    (np := 0) (cidx := 1) rfl F.natCases F.natCasesOrigin F.natSucc F.natInd.arity F.natInf
    rfl ?_ ?_ rfl ?_ rfl
    (fun i hi => absurd hi (by simp)) (by decide) hio hcont
  · intro i hi
    obtain rfl : i = 0 := by simp at hi; omega
    exact .lam _ _ _ _
  · exact peanoSrc_eval F 2
  · intro i hi
    rcases i with _ | _ | n
    · exact hmin0
    · exact .lam _ _ _ _
    · exact absurd hi (by simp)

set_option linter.unusedVariables false in
/--
**Rung G5 is green, and its source evaluation is not assumed.** For the `#erase` run
recorded in `VerifyBench/Spikes/G5.lean`, the emitted program is the lowered image of a
specification environment that erases `spikeCase`, and the answer the source semantics
computes — the peano numeral `1` — is reproduced as the literal λ□ numeral `1`, not `□` and
not a stuck term. This is the first rung whose `hev` is a derivation: `hcfg`, `hsup`, `hnb`,
`hwt`, the source evaluation and the target-side evaluation are all discharged here, and
what is left of the trust rows is `hcb`, the two value-side typings, and the block data
`SpikeNatFacts` and the three `StepDefeq`s carry.
-/
theorem green_G5
    {lenv : Lean.Environment} {env : VEnv} {gw : Void IO.RealWorld → NameGenerator}
    {vv : VExpr} {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
    {w wp w' : Void IO.RealWorld} {inls : List Kername} {ni pi : InductiveId}
    {us : List VLevel} {idx : List VExpr}
    (P : ErasureSpec lenv env [] gw)
    (htbl : SourceTableAdequate lenv g5Table)
    (hsafe : TableSafe lenv g5Table)
    (E : EraserAsks lenv env [] gw)
    (A : UpstreamAsks env)
    (hblk : TableBlocks lenv env g5Table)
    (hve : VisitExprRunConcl env gw)
    (hcb : CompilerBodies lenv env g5Table.body?)
    (hprep : Erasure.prepare_erasure eG5 {} { «config» := spikeConfig } cctx ref w
      = .ok (eG5, {}) wp)
    (hrun : Erasure.erase eG5 spikeConfig cctx ref w
      = .ok (.untyped g5Env (some g5Term), inls) w')
    (hbridge : ∀ (sf : Erasure.ErasureState) (wt : Void IO.RealWorld),
      Erasure.visitExpr eG5 {} { «config» := spikeConfig } cctx ref wp = .ok (g5Term, sf) wt →
      ∃ Γspec : GlobalDeclarations, SpecEnv env g5Table.body? sf Γspec ∧
        ∀ t₀ : LBTerm, Erases env [] [] eG5 t₀ → Lower Γspec t₀ g5Term →
          ErasureBridge env g5Table.body? Γspec g5Env g5Term t₀)
    (F : SpikeNatFacts env ni)
    (U : SpikeUnitFacts env pi)
    (hd : StepDefeq env [] [] eG5 g5Body)
    (hdu : StepDefeq env [] [] (.const ``Unit.unit []) (.const ``PUnit.unit [.succ .zero]))
    (hio : StepDefeq env [] [] g5Body (mkApps g5Minor1 [peanoSrc 1]))
    (hvwt : TrExprS env [] [] (peanoSrc 1) vv)
    (hty : env.HasType 0 [] vv (VExpr.mkApps (.const ``Nat us) idx))
    (hfo : FirstOrderInd env ``Nat) :
    ∃ (Γspec : GlobalDeclarations) (t₀ tv₀ : LBTerm),
      Erases env [] [] eG5 t₀
      ∧ ErasesEnv env g5Table.body? Γspec t₀
      ∧ Lower Γspec t₀ g5Term
      ∧ LowerEnv Γspec g5Env
      ∧ LBWfPeregrine g5Env g5Term
      ∧ Erases env [] [] (peanoSrc 1) tv₀
      ∧ Lower Γspec tv₀ (peanoLB 1)
      ∧ NoBox (peanoLB 1)
      ∧ (∀ tv', Erases env [] [] (peanoSrc 1) tv' → tv' = tv₀)
      ∧ WcbvEval g5Env eraseFlags g5Term (peanoLB 1) := by
  obtain ⟨Γspec, t₀, -, her, herΓ, hlow, hlowΓ, hwf, hobs⟩ :=
    shipping_erase_correct_firstorder P E A htbl hsafe hblk spike_configPinned hcb
      hve (trExprS_const_of_table P htbl hsafe rfl)
      (supportedB_sound P htbl hsafe g5_supported) hprep hrun g5_noBodylessRefs hbridge
  obtain ⟨tv₀, tv, herv, hlowv, hnobox, huniq, hevtgt⟩ :=
    hobs [] [] ``Nat us idx (peanoSrc 1) vv rfl (fun i hi => absurd hi (by simp))
      (g5_seval F U hd hdu hio) hvwt hty hfo
  have htv : tv = g5Answer := eval_deterministic hevtgt g5_eval
  subst htv
  exact ⟨Γspec, t₀, tv₀, her, herΓ, hlow, hlowΓ, hwf, herv, hlowv, hnobox, huniq, g5_eval⟩

/-! ## G6 — `spikeFix`, δ on a recursive constant -/

/-- The reified slice of the elaboration environment rung G6 reads, spliced by `reify%`
out of the environment this module elaborates in. -/
def g6Table : SourceTable := reify% spikeFix

/-- The source term `#erase spikeFix` elaborates. -/
def eG6 : Expr := .const ``spikeFix []

/-- The kername of the recursive constant rung G6 unfolds. -/
def spikeRecKn : Kername := rootKername "spikeRec"

/-- The emitted fixpoint of `spikeRec`: one member, recursive on its only argument, whose
body is the ι redex on it. -/
def spikeRecDef : @FixDef LBTerm :=
  { name := .named "spikeRec",
    body := .lambda (.named "n")
      (.case (natIid, 0) (.bvar 0)
        [([], .construct natIid 0 []),
         ([.named "m"], .app (.construct natIid 1 []) (.app (.bvar 2) (.bvar 0)))]),
    principalArgIdx := 0 }

/-- Rung G6's emitted environment, transcribed from `VerifyBench/ast/Spikes/G6.ast`. -/
def g6Env : GlobalDeclarations :=
  [ (rootKername "spikeFix", .constantDecl ⟨some (.app (.const spikeRecKn) (peanoLB 2))⟩),
    (spikeRecKn, .constantDecl ⟨some (.fix [spikeRecDef] 0)⟩),
    (rootKername "Nat", .inductiveDecl natBody) ]

/-- Rung G6's emitted term. -/
def g6Term : LBTerm := .const (rootKername "spikeFix")

/-- Rung G6's answer: the λ□ peano numeral `2`. -/
def g6Answer : LBTerm := peanoLB 2

/-- The subject is inside the supported fragment, decided on the reified table.
The verdict is computed by the kernel: `String.isPrefixOf`, which `isMatcherName` calls,
does not reduce in the elaborator. -/
theorem g6_supported : supportedB g6Table 8 eG6 = .ok () := by
  have h : (supportedB g6Table 8 eG6).isOk = true := by decide +kernel
  cases hx : supportedB g6Table 8 eG6 with
  | ok u => cases u; rfl
  | error err => rw [hx] at h; exact Bool.noConfusion h

/-- Every constant the emitted program reaches is declared with a body. -/
theorem g6_noBodylessRefs : NoBodylessRefs g6Env g6Term := by decide +kernel

/-- The emitted program evaluates to the literal answer, by the certified evaluator: two
`fix` unfoldings, each guarded by the ι step on its argument. -/
theorem g6_eval : WcbvEval g6Env eraseFlags g6Term g6Answer :=
  lbEval_sound (n := 24) (by rfl)

set_option linter.unusedVariables false in
/--
**Rung G6 is green.** For the `#erase` run recorded in `VerifyBench/Spikes/G6.lean`, the
emitted program is the lowered image of a specification environment that erases `spikeFix`,
and the source evaluation's answer is reproduced as the literal λ□ peano numeral `2`, not
`□` and not a stuck term. The constant the subject applies is recursive, so its emitted
body is a `.fix` node and the target run unfolds it twice under the guard.
`hcfg`, `hsup`, `hnb`, `hwt` and the target-side evaluation are discharged here by checked
terms; `hcb` and `hev` stay binders, per `doc/trust.md`'s class-**C** rows.
-/
theorem green_G6
    {lenv : Lean.Environment} {env : VEnv} {gw : Void IO.RealWorld → NameGenerator}
    {vv : VExpr} {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
    {w wp w' : Void IO.RealWorld} {inls : List Kername}
    {v : Expr} {us : List VLevel} {idx : List VExpr}
    (P : ErasureSpec lenv env [] gw)
    (htbl : SourceTableAdequate lenv g6Table)
    (hsafe : TableSafe lenv g6Table)
    (E : EraserAsks lenv env [] gw)
    (A : UpstreamAsks env)
    (hblk : TableBlocks lenv env g6Table)
    (hve : VisitExprRunConcl env gw)
    (hcb : CompilerBodies lenv env g6Table.body?)
    (hprep : Erasure.prepare_erasure eG6 {} { «config» := spikeConfig } cctx ref w
      = .ok (eG6, {}) wp)
    (hrun : Erasure.erase eG6 spikeConfig cctx ref w
      = .ok (.untyped g6Env (some g6Term), inls) w')
    (hbridge : ∀ (sf : Erasure.ErasureState) (wt : Void IO.RealWorld),
      Erasure.visitExpr eG6 {} { «config» := spikeConfig } cctx ref wp = .ok (g6Term, sf) wt →
      ∃ Γspec : GlobalDeclarations, SpecEnv env g6Table.body? sf Γspec ∧
        ∀ t₀ : LBTerm, Erases env [] [] eG6 t₀ → Lower Γspec t₀ g6Term →
          ErasureBridge env g6Table.body? Γspec g6Env g6Term t₀)
    (hev : SEval env g6Table.body? [] fullFlags [] eG6 v)
    (hvwt : TrExprS env [] [] v vv)
    (hty : env.HasType 0 [] vv (VExpr.mkApps (.const ``Nat us) idx))
    (hfo : FirstOrderInd env ``Nat) :
    ∃ (Γspec : GlobalDeclarations) (t₀ tv₀ : LBTerm),
      Erases env [] [] eG6 t₀
      ∧ ErasesEnv env g6Table.body? Γspec t₀
      ∧ Lower Γspec t₀ g6Term
      ∧ LowerEnv Γspec g6Env
      ∧ LBWfPeregrine g6Env g6Term
      ∧ Erases env [] [] v tv₀
      ∧ Lower Γspec tv₀ (peanoLB 2)
      ∧ NoBox (peanoLB 2)
      ∧ (∀ tv', Erases env [] [] v tv' → tv' = tv₀)
      ∧ WcbvEval g6Env eraseFlags g6Term (peanoLB 2) := by
  obtain ⟨Γspec, t₀, -, her, herΓ, hlow, hlowΓ, hwf, hobs⟩ :=
    shipping_erase_correct_firstorder P E A htbl hsafe hblk spike_configPinned hcb
      hve (trExprS_const_of_table P htbl hsafe rfl)
      (supportedB_sound P htbl hsafe g6_supported) hprep hrun g6_noBodylessRefs hbridge
  obtain ⟨tv₀, tv, herv, hlowv, hnobox, huniq, hevtgt⟩ :=
    hobs [] [] ``Nat us idx v vv rfl (fun i hi => absurd hi (by simp)) hev hvwt hty hfo
  have htv : tv = g6Answer := eval_deterministic hevtgt g6_eval
  subst htv
  exact ⟨Γspec, t₀, tv₀, her, herΓ, hlow, hlowΓ, hwf, herv, hlowv, hnobox, huniq, g6_eval⟩

/-! ## The arithmetic tower, shared by rungs G7 and G8

`arithClosed` and `benchArith` erase the same dependency closure — the `HPow`/`Pow`/`NatPow`,
`HMul`/`Mul`, `HSub`/`Sub` and `HAdd`/`Add` classes, their `Nat` instances, and the four
`Nat` operations — so the two rungs share one transcription. The rungs differ in their head
declaration and in the tag the matcher inliner writes into the ten emitted `let` binders,
which names the module the `#erase` ran in.
-/

/-- A kername in a one-segment module path, the shape every qualified name in the arithmetic
tower has. -/
def dotKername (mp id : String) : Kername := ⟨.MPdot (.MPfile []) mp, id⟩

/-- The λ□ inductive identifier of a class the tower declares: its own block, first body. -/
def classIid (name : String) : InductiveId := ⟨rootKername name, 0⟩

/-- `n` anonymous binders in front of a body: what an emitted class projection puts before
its `self` binder, one per class parameter whose argument the eraser boxes. -/
def boxLambdas : Nat → LBTerm → LBTerm
  | 0, t => t
  | n + 1, t => .lambda .anon (boxLambdas n t)

/-- The emitted declaration of a class's field projection: the class parameters bound
anonymously, then the field read out of the instance. -/
def classProjDecl (cls fld : String) (npars : Nat) : Kername × GlobalDecl :=
  (dotKername cls fld, .constantDecl ⟨some
    (boxLambdas npars (.lambda (.named "self") (.proj ⟨classIid cls, npars, 0⟩ (.bvar 0))))⟩)

/-- The emitted declaration of a `Nat` instance of a homogeneous class: the `Nat` operation
packed into the class constructor, the carrier erased. -/
def natInstDecl (inst cls op : String) : Kername × GlobalDecl :=
  (rootKername inst, .constantDecl ⟨some
    (.app (.app (.construct (classIid cls) 0 []) .box) (.const (dotKername "Nat" op)))⟩)

/-- The emitted declaration of a heterogeneous class's homogeneous bridge instance — the
`instHMul` shape. `ib` is the hygienic name the instance binder carries. -/
def homInstDecl (inst hcls cls fld ib : String) : Kername × GlobalDecl :=
  (rootKername inst, .constantDecl ⟨some
    (.lambda .anon (.lambda (.named ib)
      (LBTerm.mkApps (.construct (classIid hcls) 0 [])
        [.box, .box, .box,
         (.lambda (.named "a") (.lambda (.named "b")
           (LBTerm.mkApps (.const (dotKername cls fld))
             [.box, .bvar 2, .bvar 1, .bvar 0])))])))⟩)

/-- The binder name Lean's matcher inliner gives an emitted `let`. The tag is the macro scope
of the module the `#erase` ran in, so the same source program erased in two modules differs
exactly at these names. -/
def altBinder (tag n : String) : BinderName :=
  .named ("_alt._@." ++ tag ++ "._hygCtx._hyg." ++ n)

/-! ### The emitted bodies, transcribed -/

/-- The emitted fixpoint of `Nat.pow`: structural recursion on the exponent, the base
multiplied in at each step. The two `let`s hold the compiled `match`'s alternatives, the
nullary one thunked. -/
def natPowFix (tag : String) : @FixDef LBTerm :=
  { name := (.named "Nat.pow"),
    body := (.lambda (.named "m")
              (.lambda (.named "x._@.Init.Prelude.427477602._hygCtx._hyg.10")
                (.letIn (altBinder tag "11") (.lambda (.named "_") (litLB 1))
                  (.letIn (altBinder tag "12")
                    (.lambda (.named "n")
                      (.app
                        (.app (.const (dotKername "Nat" "mul"))
                          (.app (.app (.bvar 4) (.bvar 3)) (.bvar 0)))
                        (.bvar 3)))
                    (.case (natIid, 0) (.bvar 2)
                      [([], (.app (.bvar 1) (.const unitUnitKn))),
                       ([(.named "n._@.Init.Prelude.427477602._hygCtx._hyg.40")],
                        (.app (.bvar 1) (.bvar 0)))]))))),
    principalArgIdx := 0 }

/-- The emitted fixpoint of `Nat.mul`: structural recursion on the **second** argument,
adding the first at each step. -/
def natMulFix (tag : String) : @FixDef LBTerm :=
  { name := (.named "Nat.mul"),
    body := (.lambda (.named "x._@.Init.Prelude.2075127268._hygCtx._hyg.13")
              (.lambda (.named "x._@.Init.Prelude.2075127268._hygCtx._hyg.14")
                (.letIn (altBinder tag "13")
                  (.lambda (.named "x._@.Init.Prelude.2075127268._hygCtx._hyg.41") (litLB 0))
                  (.letIn (altBinder tag "14")
                    (.lambda (.named "a")
                      (.lambda (.named "b")
                        (.app
                          (.app (.const (dotKername "Nat" "add"))
                            (.app (.app (.bvar 5) (.bvar 1)) (.bvar 0)))
                          (.bvar 1))))
                    (.case (natIid, 0) (.bvar 2)
                      [([], (.app (.bvar 1) (.bvar 3))),
                       ([(.named "n._@.Init.Prelude.2075127268._hygCtx._hyg.64")],
                        (.app (.app (.bvar 1) (.bvar 4)) (.bvar 0)))]))))),
    principalArgIdx := 0 }

/-- The emitted fixpoint of `Nat.add`: structural recursion on the second argument, a
`Nat.succ` at each step. -/
def natAddFix (tag : String) : @FixDef LBTerm :=
  { name := (.named "Nat.add"),
    body := (.lambda (.named "x._@.Init.Prelude.2314059840._hygCtx._hyg.13")
              (.lambda (.named "x._@.Init.Prelude.2314059840._hygCtx._hyg.14")
                (.letIn (altBinder tag "15") (.lambda (.named "a") (.bvar 0))
                  (.letIn (altBinder tag "16")
                    (.lambda (.named "a")
                      (.lambda (.named "b")
                        (.app (.construct natIid 1 [])
                          (.app (.app (.bvar 5) (.bvar 1)) (.bvar 0)))))
                    (.case (natIid, 0) (.bvar 2)
                      [([], (.app (.bvar 1) (.bvar 3))),
                       ([(.named "n._@.Init.Prelude.2314059840._hygCtx._hyg.62")],
                        (.app (.app (.bvar 1) (.bvar 4)) (.bvar 0)))]))))),
    principalArgIdx := 0 }

/-- The emitted fixpoint of `Nat.sub`: structural recursion on the subtrahend, one
`Nat.pred` at each step. -/
def natSubFix (tag : String) : @FixDef LBTerm :=
  { name := (.named "Nat.sub"),
    body := (.lambda (.named "x._@.Init.Prelude.462884191._hygCtx._hyg.13")
              (.lambda (.named "x._@.Init.Prelude.462884191._hygCtx._hyg.14")
                (.letIn (altBinder tag "17") (.lambda (.named "a") (.bvar 0))
                  (.letIn (altBinder tag "18")
                    (.lambda (.named "a")
                      (.lambda (.named "b")
                        (.app (.const (dotKername "Nat" "pred"))
                          (.app (.app (.bvar 5) (.bvar 1)) (.bvar 0)))))
                    (.case (natIid, 0) (.bvar 2)
                      [([], (.app (.bvar 1) (.bvar 3))),
                       ([(.named "n._@.Init.Prelude.2075127268._hygCtx._hyg.64")],
                        (.app (.app (.bvar 1) (.bvar 4)) (.bvar 0)))]))))),
    principalArgIdx := 0 }

/-- The emitted body of `Nat.pred`: a compiled `match` on the argument, zero on the
nullary alternative and the field on the successor one. -/
def natPredBody (tag : String) : LBTerm :=
  (.lambda (.named "x._@.Init.Prelude.4130297703._hygCtx._hyg.8")
    (.letIn (altBinder tag "19") (.lambda (.named "_") (litLB 0))
      (.letIn (altBinder tag "20") (.lambda (.named "a") (.bvar 0))
        (.case (natIid, 0) (.bvar 2)
          [([], (.app (.bvar 1) (.const unitUnitKn))),
           ([(.named "n._@.Init.Prelude.427477602._hygCtx._hyg.40")],
            (.app (.bvar 1) (.bvar 0)))]))))

/-- The emitted body of `instPowNat`: the `NatPow` instance re-packed as a `Pow` instance,
the two carriers erased. -/
def instPowNatBody : LBTerm :=
  (.lambda .anon
    (.lambda (.named "inst._@.Init.Prelude.3231272351._hygCtx._hyg.5")
      (LBTerm.mkApps (.construct (classIid "Pow") 0 [])
        [.box, .box,
         (.lambda (.named "a")
           (.lambda (.named "n")
             (LBTerm.mkApps (.const (dotKername "NatPow" "pow"))
               [.box, (.bvar 2), (.bvar 1), (.bvar 0)])))])))

/-- The emitted body of `instHPow`: the `Pow` instance re-packed as an `HPow` instance.
Its argument count differs from the `instHMul` shape, so it is transcribed on its own. -/
def instHPowBody : LBTerm :=
  (.lambda .anon
    (.lambda .anon
      (.lambda (.named "inst._@.Init.Prelude.3805852345._hygCtx._hyg.9")
        (LBTerm.mkApps (.construct (classIid "HPow") 0 [])
          [.box, .box, .box,
           (.lambda (.named "a")
             (.lambda (.named "b")
               (LBTerm.mkApps (.const (dotKername "Pow" "pow"))
                 [.box, .box, (.bvar 2), (.bvar 1), (.bvar 0)])))]))))

/-- The emitted body of `benchArith`: the whole class tower of `2 ^ (((n * 3) - n) + 3)`,
every dictionary spelled out and every type argument erased. -/
def benchArithBody : LBTerm :=
  (.lambda (.named "n")
    (LBTerm.mkApps (.const (dotKername "HPow" "hPow"))
      [.box, .box, .box,
       (LBTerm.mkApps (.const (rootKername "instHPow"))
         [.box, .box,
          (.app (.app (.const (rootKername "instPowNat")) .box)
            (.const (rootKername "instNatPowNat")))]),
       (litLB 2),
       (LBTerm.mkApps (.const (dotKername "HAdd" "hAdd"))
         [.box, .box, .box,
          (.app (.app (.const (rootKername "instHAdd")) .box)
            (.const (rootKername "instAddNat"))),
          (LBTerm.mkApps (.const (dotKername "HSub" "hSub"))
            [.box, .box, .box,
             (.app (.app (.const (rootKername "instHSub")) .box)
               (.const (rootKername "instSubNat"))),
             (LBTerm.mkApps (.const (dotKername "HMul" "hMul"))
               [.box, .box, .box,
                (.app (.app (.const (rootKername "instHMul")) .box)
                  (.const (rootKername "instMulNat"))),
                (.bvar 0), (litLB 3)]),
             (.bvar 0)]),
          (litLB 3)])]))

/-- The emitted body of `arithClosed`: `benchArith` applied to the literal `0`. -/
def arithClosedBody : LBTerm :=
  (.app (.const (rootKername "benchArith")) (litLB 0))

/-! ### The tower -/

/-- Everything rungs G7 and G8 emit below their own head declaration, in the frontend's own
order. `tag` is the erasing module's macro scope, which the ten matcher-inlined `let` binders
carry. -/
def arithTower (tag : String) : GlobalDeclarations :=
  [
    (rootKername "benchArith", .constantDecl ⟨some benchArithBody⟩),
    natInstDecl "instMulNat" "Mul" "mul",
    homInstDecl "instHMul" "HMul" "Mul" "mul"
      "inst._@.Init.Prelude.3013044039._hygCtx._hyg.5",
    classProjDecl "Mul" "mul" 1,
    (rootKername "Mul", .inductiveDecl (classBody "Mul" 1)),
    classProjDecl "HMul" "hMul" 3,
    (rootKername "HMul", .inductiveDecl (classBody "HMul" 3)),
    natInstDecl "instSubNat" "Sub" "sub",
    (dotKername "Nat" "sub", .constantDecl ⟨some (.fix [natSubFix tag] 0)⟩),
    (dotKername "Nat" "pred", .constantDecl ⟨some (natPredBody tag)⟩),
    homInstDecl "instHSub" "HSub" "Sub" "sub"
      "inst._@.Init.Prelude.4034066273._hygCtx._hyg.5",
    classProjDecl "Sub" "sub" 1,
    (rootKername "Sub", .inductiveDecl (classBody "Sub" 1)),
    classProjDecl "HSub" "hSub" 3,
    (rootKername "HSub", .inductiveDecl (classBody "HSub" 3)),
    natInstDecl "instAddNat" "Add" "add",
    homInstDecl "instHAdd" "HAdd" "Add" "add"
      "inst._@.Init.Prelude.1910291827._hygCtx._hyg.5",
    classProjDecl "Add" "add" 1,
    (rootKername "Add", .inductiveDecl (classBody "Add" 1)),
    classProjDecl "HAdd" "hAdd" 3,
    (rootKername "HAdd", .inductiveDecl (classBody "HAdd" 3)),
    natInstDecl "instNatPowNat" "NatPow" "pow",
    (dotKername "Nat" "pow", .constantDecl ⟨some (.fix [natPowFix tag] 0)⟩),
    (unitUnitKn, .constantDecl ⟨some (.construct punitIid 0 [])⟩),
    (rootKername "PUnit", .inductiveDecl punitBody),
    (dotKername "Nat" "mul", .constantDecl ⟨some (.fix [natMulFix tag] 0)⟩),
    (dotKername "Nat" "add", .constantDecl ⟨some (.fix [natAddFix tag] 0)⟩),
    instOfNatNatDecl,
    (rootKername "Nat", .inductiveDecl natBody),
    ofNatDecl,
    (rootKername "OfNat", .inductiveDecl ofNatBody),
    (rootKername "instPowNat", .constantDecl ⟨some instPowNatBody⟩),
    classProjDecl "NatPow" "pow" 1,
    (rootKername "NatPow", .inductiveDecl (classBody "NatPow" 1)),
    (rootKername "instHPow", .constantDecl ⟨some instHPowBody⟩),
    classProjDecl "Pow" "pow" 2,
    (rootKername "Pow", .inductiveDecl (classBody "Pow" 2)),
    classProjDecl "HPow" "hPow" 3,
    (rootKername "HPow", .inductiveDecl (classBody "HPow" 3))
  ]

/-! ## G7 — `arithClosed : Nat := benchArith 0` -/

/-- The reified slice of the elaboration environment rung G7 reads, spliced by `reify%`
out of the environment this module elaborates in. -/
def g7Table : SourceTable := reify% arithClosed

/-- The source term `#erase arithClosed` elaborates. -/
def eG7 : Expr := .const ``arithClosed []

/-- The macro scope `VerifyBench/Spikes/G7.lean` writes into its emitted `let` binders. -/
def g7Tag : String := "VerifyBench.Spikes.G7.1490284936"

/-- Rung G7's emitted environment, transcribed from `VerifyBench/ast/Spikes/G7.ast`. -/
def g7Env : GlobalDeclarations :=
  (rootKername "arithClosed", .constantDecl ⟨some arithClosedBody⟩) :: arithTower g7Tag

/-- Rung G7's emitted term. -/
def g7Term : LBTerm := .const (rootKername "arithClosed")

/-- Rung G7's answer: the λ□ peano numeral `8`. -/
def g7Answer : LBTerm := peanoLB 8

/-! ## G8 — `benchArith : Nat → Nat`, the applied rung -/

/-- The reified slice of the elaboration environment rung G8 reads, spliced by `reify%`
out of the environment this module elaborates in. -/
def g8Table : SourceTable := reify% benchArith

/-- The source term `#erase benchArith` elaborates. -/
def eG8 : Expr := .const ``benchArith []

/-- The macro scope `VerifyBench/Spikes/G8.lean` writes into its emitted `let` binders. -/
def g8Tag : String := "VerifyBench.Spikes.G8.2455828205"

/-- Rung G8's emitted environment, transcribed from `VerifyBench/ast/Spikes/G8.ast`. -/
def g8Env : GlobalDeclarations := arithTower g8Tag

/-- Rung G8's emitted term. -/
def g8Term : LBTerm := .const (rootKername "benchArith")

/-- The source argument rung G8 applies its subject to: the constructor spelling of `0`. -/
def g8Arg : Expr := .const ``Nat.zero []

/-- Rung G8's answer: the λ□ peano numeral `8`. -/
def g8Answer : LBTerm := peanoLB 8

/-! ### The hypotheses a computation settles, at Arith's scale -/

/-- The subject is inside the supported fragment, decided on the reified table.
The verdict is computed by the kernel: `String.isPrefixOf`, which `isMatcherName` calls,
does not reduce in the elaborator. -/
theorem g7_supported : supportedB g7Table 8 eG7 = .ok () := by
  have h : (supportedB g7Table 8 eG7).isOk = true := by decide +kernel
  cases hx : supportedB g7Table 8 eG7 with
  | ok u => cases u; rfl
  | error err => rw [hx] at h; exact Bool.noConfusion h

/-- Every constant the emitted program reaches is declared with a body. Forty declarations
and a forty-round closure, so the kernel run is the ladder's longest. -/
theorem g7_noBodylessRefs : NoBodylessRefs g7Env g7Term := by decide +kernel

/-- The emitted program evaluates to the literal answer, by the certified evaluator: the
whole class tower unfolded, `Nat.pow` three times and `Nat.mul`/`Nat.add` under it. -/
theorem g7_eval : WcbvEval g7Env eraseFlags g7Term g7Answer :=
  lbEval_sound (n := 64) (by rfl)

/-- The subject is inside the supported fragment, decided on the reified table. -/
theorem g8_supported : supportedB g8Table 8 eG8 = .ok () := by
  have h : (supportedB g8Table 8 eG8).isOk = true := by decide +kernel
  cases hx : supportedB g8Table 8 eG8 with
  | ok u => cases u; rfl
  | error err => rw [hx] at h; exact Bool.noConfusion h

/-- Every constant the emitted program reaches is declared with a body. -/
theorem g8_noBodylessRefs : NoBodylessRefs g8Env g8Term := by decide +kernel

/-- The emitted program **applied to the λ□ numeral `0`** evaluates to the literal answer.
This is the applied rung's target-side computation: the subject is a function, so the
observation is made at a spine, not at the term alone. -/
theorem g8_eval : WcbvEval g8Env eraseFlags (.app g8Term (peanoLB 0)) g8Answer :=
  lbEval_sound (n := 64) (by rfl)

/-! ### The rungs -/

set_option linter.unusedVariables false in
/--
**Rung G7 is green.** For the `#erase` run recorded in `VerifyBench/Spikes/G7.lean`, the
emitted program is the lowered image of a specification environment that erases
`arithClosed`, and the source evaluation's answer is reproduced as the literal λ□ peano
numeral `8`, not `□` and not a stuck term. The subject is a tracked benchmark program: forty
emitted declarations, ten class projections, four `.fix` blocks and five `.case` nodes.
`hcfg`, `hsup`, `hnb`, `hwt` and the target-side evaluation are discharged here by checked
terms; `hcb` and `hev` stay binders, per `doc/trust.md`'s class-**C** rows.
-/
theorem green_G7
    {lenv : Lean.Environment} {env : VEnv} {gw : Void IO.RealWorld → NameGenerator}
    {vv : VExpr} {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
    {w wp w' : Void IO.RealWorld} {inls : List Kername}
    {v : Expr} {us : List VLevel} {idx : List VExpr}
    (P : ErasureSpec lenv env [] gw)
    (htbl : SourceTableAdequate lenv g7Table)
    (hsafe : TableSafe lenv g7Table)
    (E : EraserAsks lenv env [] gw)
    (A : UpstreamAsks env)
    (hblk : TableBlocks lenv env g7Table)
    (hve : VisitExprRunConcl env gw)
    (hcb : CompilerBodies lenv env g7Table.body?)
    (hprep : Erasure.prepare_erasure eG7 {} { «config» := spikeConfig } cctx ref w
      = .ok (eG7, {}) wp)
    (hrun : Erasure.erase eG7 spikeConfig cctx ref w
      = .ok (.untyped g7Env (some g7Term), inls) w')
    (hbridge : ∀ (sf : Erasure.ErasureState) (wt : Void IO.RealWorld),
      Erasure.visitExpr eG7 {} { «config» := spikeConfig } cctx ref wp = .ok (g7Term, sf) wt →
      ∃ Γspec : GlobalDeclarations, SpecEnv env g7Table.body? sf Γspec ∧
        ∀ t₀ : LBTerm, Erases env [] [] eG7 t₀ → Lower Γspec t₀ g7Term →
          ErasureBridge env g7Table.body? Γspec g7Env g7Term t₀)
    (hev : SEval env g7Table.body? [] fullFlags [] eG7 v)
    (hvwt : TrExprS env [] [] v vv)
    (hty : env.HasType 0 [] vv (VExpr.mkApps (.const ``Nat us) idx))
    (hfo : FirstOrderInd env ``Nat) :
    ∃ (Γspec : GlobalDeclarations) (t₀ tv₀ : LBTerm),
      Erases env [] [] eG7 t₀
      ∧ ErasesEnv env g7Table.body? Γspec t₀
      ∧ Lower Γspec t₀ g7Term
      ∧ LowerEnv Γspec g7Env
      ∧ LBWfPeregrine g7Env g7Term
      ∧ Erases env [] [] v tv₀
      ∧ Lower Γspec tv₀ (peanoLB 8)
      ∧ NoBox (peanoLB 8)
      ∧ (∀ tv', Erases env [] [] v tv' → tv' = tv₀)
      ∧ WcbvEval g7Env eraseFlags g7Term (peanoLB 8) := by
  obtain ⟨Γspec, t₀, -, her, herΓ, hlow, hlowΓ, hwf, hobs⟩ :=
    shipping_erase_correct_firstorder P E A htbl hsafe hblk spike_configPinned hcb
      hve (trExprS_const_of_table P htbl hsafe rfl)
      (supportedB_sound P htbl hsafe g7_supported) hprep hrun g7_noBodylessRefs hbridge
  obtain ⟨tv₀, tv, herv, hlowv, hnobox, huniq, hevtgt⟩ :=
    hobs [] [] ``Nat us idx v vv rfl (fun i hi => absurd hi (by simp)) hev hvwt hty hfo
  have htv : tv = g7Answer := eval_deterministic hevtgt g7_eval
  subst htv
  exact ⟨Γspec, t₀, tv₀, her, herΓ, hlow, hlowΓ, hwf, herv, hlowv, hnobox, huniq, g7_eval⟩

set_option linter.unusedVariables false in
/--
**Rung G8 is green, and it is the applied one.** For the `#erase` run recorded in
`VerifyBench/Spikes/G8.lean` the subject is function-typed, so the observation is made at a
spine: the emitted term applied to the λ□ numeral `0` evaluates to the literal peano numeral
`8`, the value the source semantics gives `benchArith Nat.zero`. The argument's own
`ErasesLB` premise is discharged here — a nullary constructor constant erases and lowers to
the empty constructor node — so the rung adds no binder for it beyond the block data
`SpikeNatFacts` carries. `hcfg`, `hsup`, `hnb`, `hwt`, the argument's erasure and the
target-side evaluation are discharged by checked terms; `hcb` and `hev` stay binders.
-/
theorem green_G8
    {lenv : Lean.Environment} {env : VEnv} {gw : Void IO.RealWorld → NameGenerator}
    {vv : VExpr} {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
    {w wp w' : Void IO.RealWorld} {inls : List Kername}
    {v : Expr} {us : List VLevel} {idx : List VExpr}
    (P : ErasureSpec lenv env [] gw)
    (htbl : SourceTableAdequate lenv g8Table)
    (hsafe : TableSafe lenv g8Table)
    (E : EraserAsks lenv env [] gw)
    (A : UpstreamAsks env)
    (hblk : TableBlocks lenv env g8Table)
    (hve : VisitExprRunConcl env gw)
    (hcb : CompilerBodies lenv env g8Table.body?)
    (F : SpikeNatFacts env natIid)
    (hprep : Erasure.prepare_erasure eG8 {} { «config» := spikeConfig } cctx ref w
      = .ok (eG8, {}) wp)
    (hrun : Erasure.erase eG8 spikeConfig cctx ref w
      = .ok (.untyped g8Env (some g8Term), inls) w')
    (hbridge : ∀ (sf : Erasure.ErasureState) (wt : Void IO.RealWorld),
      Erasure.visitExpr eG8 {} { «config» := spikeConfig } cctx ref wp = .ok (g8Term, sf) wt →
      ∃ Γspec : GlobalDeclarations, SpecEnv env g8Table.body? sf Γspec ∧
        ∀ t₀ : LBTerm, Erases env [] [] eG8 t₀ → Lower Γspec t₀ g8Term →
          ErasureBridge env g8Table.body? Γspec g8Env g8Term t₀)
    (hev : SEval env g8Table.body? [] fullFlags [] (mkApps eG8 [g8Arg]) v)
    (hvwt : TrExprS env [] [] v vv)
    (hty : env.HasType 0 [] vv (VExpr.mkApps (.const ``Nat us) idx))
    (hfo : FirstOrderInd env ``Nat) :
    ∃ (Γspec : GlobalDeclarations) (t₀ tv₀ : LBTerm),
      Erases env [] [] eG8 t₀
      ∧ ErasesEnv env g8Table.body? Γspec t₀
      ∧ Lower Γspec t₀ g8Term
      ∧ LowerEnv Γspec g8Env
      ∧ LBWfPeregrine g8Env g8Term
      ∧ Erases env [] [] v tv₀
      ∧ Lower Γspec tv₀ (peanoLB 8)
      ∧ NoBox (peanoLB 8)
      ∧ (∀ tv', Erases env [] [] v tv' → tv' = tv₀)
      ∧ WcbvEval g8Env eraseFlags (.app g8Term (peanoLB 0)) (peanoLB 8) := by
  obtain ⟨Γspec, t₀, -, her, herΓ, hlow, hlowΓ, hwf, hobs⟩ :=
    shipping_erase_correct_firstorder P E A htbl hsafe hblk spike_configPinned hcb
      hve (trExprS_const_of_table P htbl hsafe rfl)
      (supportedB_sound P htbl hsafe g8_supported) hprep hrun g8_noBodylessRefs hbridge
  obtain ⟨tv₀, tv, herv, hlowv, hnobox, huniq, hevtgt⟩ :=
    hobs [g8Arg] [peanoLB 0] ``Nat us idx v vv rfl
      (fun i hi => by
        obtain rfl : i = 0 := by simp at hi; omega
        exact ErasesLB.ctor_head F.natZero F.natInd)
      hev hvwt hty hfo
  have htv : tv = g8Answer := eval_deterministic hevtgt g8_eval
  subst htv
  exact ⟨Γspec, t₀, tv₀, her, herΓ, hlow, hlowΓ, hwf, herv, hlowv, hnobox, huniq, g8_eval⟩

end LeanToLambdaBox.Green
