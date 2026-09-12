import LeanToLambdaBox.ErasesCorrect.Steps
import LeanToLambdaBox.ErasesCorrect.Iota

/-!
# The projection arm of the simulation

`step_proj` is the arm of `erases_correct` at `SEval.proj`: a structure projection whose
discriminant reaches a constructor spine. Five steps:

* `Erases.proj_inv` splits the erasure into the box reading, closed by
  `erases_correct_boxLow`, and the `.proj` node, whose block data is `IndInfo`'s;
* `Lower.source_proj` reads the pass back at that node — a projection lowers to a
  projection with the same triple, so there is no spine to invert;
* the discriminant's induction hypothesis gives the target value, its boxed readings
  refuted by `not_erasable_of_informative` against the typing `TrProj` carries;
* the node's `propositional = false` comes from the reached block through
  `ErasesEnvFwd.blocks` and `LowerEnv.inds`;
* the field's induction hypothesis is taken at the selected argument, and `WcbvEval.proj`
  assembles. No arity is read: the field position is in range because the rule's own
  `np + i < cargs.length` is, and the erasure and the pass preserve lengths.

`step_proj_of_projSpec` is the arm under two named premises beyond U3.2's `IndSpineNotProp`
and U3.1's `ErasesEnvFwd`: `ProjSpec` carries the three facts `Erases.proj` and `SEval.proj`
do not state — that the projected structure is informative, that a value of it is
constructor-headed, and that the rule's parameter count is the block's.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-! ## What the arm reads beyond the two rules

`SEval.proj` leaves both the head of the discriminant's value and the dropped-argument
count `np` free, and `Erases.proj` emits a projection node for a structure of any sort.
The three clauses below are what the arm needs and neither rule supplies.
-/

/-- The facts about a projection site that `Erases.proj` and `SEval.proj` leave open. -/
structure ProjSpec (env : VEnv) (Us : List Name) (Γspec : GlobalDeclarations) : Prop where
  /-- A structure whose block the specification environment registers is informative and
      declared by `env`'s own list. The fragment boundary N18 read at a projection: the
      target has no rule for a projection of `□`. -/
  informative : ∀ {S : Name} {iid : InductiveId} {np nf : Nat},
    IndInfo env S iid np [nf] → (LBTerm.envLookup Γspec iid.mutualBlockName).isSome →
    InformativeInd env S ∧ IndDeclOf env S
  /-- A constant-headed value of a structure is headed by one of its constructors. -/
  ctorHead : ∀ {S ctor : Name} {iid : InductiveId} {np nf : Nat} {cus : List Level}
      {cargs : List Expr} {w : VExpr} {usS : List VLevel} {params : List VExpr},
    IndInfo env S iid np [nf] → TrExprS env Us [] (mkApps (.const ctor cus) cargs) w →
    env.HasType Us.length [] w (VExpr.mkApps (.const S usS) params) →
    ∃ k, CtorOf env ctor S k
  /-- The rule's dropped-argument count selects the field the block's parameter count
      selects. -/
  field : ∀ {S : Name} {i np nps nf : Nat} {iid : InductiveId} {disc : Expr}
      {cargs : List Expr},
    IndInfo env S iid nps [nf] → np + i < cargs.length →
    StepDefeq env Us [] (.proj S i disc) cargs[np + i]! →
    nps + i < cargs.length ∧ cargs[nps + i]! = cargs[np + i]!

/-! ## The arm -/

/-- **The projection arm, under the named premises.** The subject is the projection node,
the induction hypotheses come with the rule's own subderivations, and the target is the
emitted `.proj` node at the same triple. -/
theorem step_proj_of_projSpec {env : VEnv} {bo : Name → Option Expr} {Us : List Name}
    {fl : SEvalFlags} {Γspec Γ : GlobalDeclarations} (P : IndSpineNotProp env)
    (hfwd : ErasesEnvFwd env bo Us fl Γspec) (Sp : ProjSpec env Us Γspec) :
    StepProj env bo Us fl Γspec Γ := by
  intro A Sn ctor i np cus disc r cargs henv henvL hfl hdiscr ihdiscr hlt hdef hcont ihcont
    ve t₀ t hwt her hlow hspec
  have hΔ : VLCtx.WF env Us.length ([] : VLCtx) := trivial
  have hΓv := hΔ.toCtx
  have hblk : BlockBodiesLambda Γspec := henvL.specBlocks
  have hev : SEval env bo Us fl [] (.proj Sn i disc) r := .proj hfl hdiscr hlt hdef hcont
  rcases Erases.proj_inv her with hbox | ⟨iid, nps, nf, d, hs, -, herdisc, rfl⟩
  · exact erases_correct_boxLow henv hblk hwt hbox hlow hspec hev
  obtain ⟨e', rfl, hlowd⟩ := Lower.source_proj hblk hlow rfl
  obtain ⟨w, htrd, hproj⟩ : ∃ w, TrExprS env Us [] disc w ∧
      TrProj env Us.length (VLCtx.toCtx []) Sn i w ve := by
    cases hwt with | proj h1 h2 => exact ⟨_, h1, h2⟩
  obtain ⟨_, usS, _, params, _, _, hpc⟩ := hproj
  have hdep : (LBTerm.envLookup Γspec iid.mutualBlockName).isSome :=
    hspec.deps _ (reachableFrom_of_mem_constRefs (by simp [constRefs]))
  obtain ⟨hinf, hdec⟩ := Sp.informative hs hdep
  have hspecd : ErasesEnv env bo Γspec d := hspec.subterm (.proj .refl)
  obtain ⟨dv₀, dv', herdv, hlowdv, hEdisc, hspecdv⟩ := ihdiscr htrd herdisc hlowd hspecd
  obtain ⟨vv, htrvv, hdefvv⟩ := SEval.defeq henv hΔ htrd hdiscr
  have hvvty : env.HasType Us.length (VLCtx.toCtx []) vv
      (VExpr.mkApps (.const Sn usS) params) :=
    VEnv.HasType.defeqU_l henv hΓv hdefvv hpc.major_ty
  have hnotEr : ¬ Erasable env Us.length (VLCtx.toCtx []) vv :=
    not_erasable_of_informative henv A P hΓv hdec hinf hvvty
  obtain ⟨k0, hct⟩ := Sp.ctorHead hs htrvv hvvty
  rcases erases_mkApps_inv cargs herdv with
    ⟨cth, cargs₀, hcth, hcts, rfl⟩ | ⟨cpre, csuf, cts, hceq, hcbw, hcts, rfl⟩
  case inr =>
    exfalso
    obtain ⟨we, htrwe, herwe⟩ := hcbw
    rw [hceq, mkApps_append] at htrvv
    exact hnotEr (erasable_mkApps henv hΔ csuf htrvv htrwe herwe)
  rcases Erases.const_inv hcth with ⟨hcb, rfl⟩ | ⟨I', iid', k', np', nfs', hc', hi', rfl⟩ |
    ⟨-, ho', -⟩
  · exfalso
    obtain ⟨we, htrwe, herwe⟩ := hcb
    exact hnotEr (erasable_mkApps henv hΔ cargs htrvv htrwe herwe)
  case inr.inr => exact absurd hct (constOrigin_not_ctorOf A ho' Sn k0)
  obtain ⟨rfl, rfl⟩ := CtorOf.inj A hct hc'
  obtain ⟨rfl, rfl, rfl⟩ := IndInfo.inj A hs hi'
  obtain rfl : k0 = 0 := by
    have := CtorOf.lt_nfs A hct hs
    simpa using this
  obtain ⟨hd₂, cargs', rfl, hhd₂, hclen, hcpt⟩ :=
    Lower.source_mkApps hblk (fun _ _ => LBTerm.noConfusion) (fun _ => LBTerm.noConfusion)
      cargs₀ hlowdv
  obtain rfl : hd₂ = .construct iid 0 [] := by
    rcases Lower.source_construct_nil hhd₂ rfl with h | ⟨defs, j, h⟩
    · exact h
    · exact absurd h (Lower.ne_fix_of_block hblk hhd₂ (fun _ => LBTerm.noConfusion) rfl defs j)
  obtain ⟨mib, hmib, -, oib, hoib, hprop, -⟩ := hfwd.blocks hs hdep
  have hpropΓ : isPropositionalInductive Γ iid = false := by
    simp only [isPropositionalInductive, henvL.inds _ _ hmib, hoib, hprop]
  obtain ⟨hltP, hfield⟩ := Sp.field hs hlt hdef
  have hcargsLen : cargs₀.length = cargs.length := hcts.length_eq.symm
  have herfield : Erases env Us [] cargs[np + i]! cargs₀[nps + i]! := by
    rw [← hfield]; exact forall₂_getElem! hcts _ hltP
  have hlowfield : Lower Γspec cargs₀[nps + i]! cargs'[nps + i]! :=
    hcpt _ (by omega)
  have hspecfield : ErasesEnv env bo Γspec cargs₀[nps + i]! :=
    hspecdv.subterm (subTerm_mkApps_arg _ _ _ (Lower.getElem!_mem (by omega)))
  obtain ⟨_, _, -, htrfield, -⟩ := hdef
  obtain ⟨r₀, r', herr, hlowr, hEr, hspecr⟩ :=
    ihcont htrfield herfield hlowfield hspecfield
  have hlt' : nps + i < cargs'.length := by omega
  refine ⟨r₀, r', herr, hlowr, WcbvEval.proj rfl hpropΓ hEdisc ?_ hEr, hspecr⟩
  show cargs'[nps + i]? = some cargs'[nps + i]!
  rw [getElem!_pos cargs' (nps + i) hlt']
  exact List.getElem?_eq_getElem hlt'

/-! ## Non-vacuity

The arm's target side at a two-field structure: the constructor value the discriminant's
induction hypothesis returns, and the projection step the arm closes with, at both fields.
-/

namespace LowerProjFixture

/-- The fixture's block kername. -/
def blockKn : Kername := { mp := .MPfile [], id := "LP" }

/-- Its one inductive: one parameter and one constructor of two fields. -/
def iid : InductiveId := { mutualBlockName := blockKn, idx := 0 }

/-- The emitted body, non-propositional, with the constructor's field count. -/
def mib : MutualInductiveBody :=
  { npars := 1,
    bodies := [{ name := "LP", ctors := [{ name := "mk", nargs := 2 }], projs := [] }] }

/-- The emitted environment: the block alone. -/
def env : GlobalDeclarations := [(blockKn, .inductiveDecl mib)]

/-- The block is not propositional, which is what `WcbvEval.proj` reads. -/
theorem not_propositional : isPropositionalInductive env iid = false := rfl

/-- Its constructor takes the parameter and the two fields. -/
theorem arity_three : constructorArity env iid 0 = some 3 := rfl

/-- The structure value: the parameter boxed and two distinguishable fields. -/
def value : LBTerm :=
  LBTerm.mkApps (.construct iid 0 [])
    [.box, .lambda .anon (.bvar 0), .lambda (.named "y") .box]

/-- It is a value: an applied-form constructor spine within its arity. -/
theorem value_evals : WcbvEval env eraseFlags value value := by
  refine wcbvEval_mkApps_construct arity_three _ _ (by simp) rfl ?_
  intro i hi
  match i, hi with
  | 0, _ => exact .box
  | 1, _ => exact .lam ..
  | 2, _ => exact .lam ..

/-- **The projection step fires at the second field**, past the parameter: the node's
`paramCount + fieldIdx` picks the argument the source rule's `np + i` does. -/
theorem proj_second_fires :
    WcbvEval env eraseFlags (.proj ⟨iid, 1, 1⟩ value) (.lambda (.named "y") .box) :=
  .proj rfl not_propositional value_evals rfl (.lam ..)

/-- The same step at the first field, which the parameter count separates from the
parameter. -/
theorem proj_first_fires :
    WcbvEval env eraseFlags (.proj ⟨iid, 1, 0⟩ value) (.lambda .anon (.bvar 0)) :=
  .proj rfl not_propositional value_evals rfl (.lam ..)

end LowerProjFixture

end LeanToLambdaBox
