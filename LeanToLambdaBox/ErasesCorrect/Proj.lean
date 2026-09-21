import LeanToLambdaBox.ErasesCorrect.Steps
import LeanToLambdaBox.ErasesCorrect.Iota

/-!
# The projection arm of the simulation

`step_proj` is the arm of `erases_correct` at `SEval.proj`: a structure projection whose
discriminant reaches a constructor spine. It takes no premise beyond `StepProj`'s own
`UpstreamAsks env`. Five steps:

* `Erases.proj_inv` splits the erasure into the box reading, closed by
  `erases_correct_boxLow`, and the `.proj` node, whose block data is `IndInfo`'s and whose
  relevance is the rule's own `hinf`;
* `Lower.source_proj` reads the pass back at that node — a projection lowers to a
  projection with the same triple, so there is no spine to invert;
* the discriminant's induction hypothesis gives the target value, its boxed readings
  refuted by `not_erasable_of_informative` against the typing `TrProj` carries, whose
  `IndDeclOf` is `ErasesEnv.blocks`' first conjunct at the reached block kername;
* the node's `propositional = false` comes from that same clause's `IndFlagSound` against
  the rule's own `hinf` (`IndFlagSound.notPropositional`), carried into `Γ` by
  `LowerEnv.inds`;
* the field's induction hypothesis is taken at the selected argument, and `WcbvEval.proj`
  assembles. The prefix the node drops is the one `SEval.proj`'s `hnp` names, by
  `IndArity.inj`, and the value is constructor-headed by the rule's own `hct`, whose index
  `CtorOf.lt_nfs` forces to `0` at a single-constructor block.

The arm's `sorryAx` footprint is the ι arm's: the split was justified by the work, not by
the trust. `hwt : TrExprS env Us [] (.proj S i disc) ve` is inhabitable only through
`TrProj`, whose kernel adequacy (`inferProj.WF`, `inferProj.WF_struct`) is `sorry` at the
pin, so the arm is non-vacuous today only on hand-built witnesses.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-! ## The arm -/

/-- **The projection arm.** The subject is the projection node, the induction hypotheses
come with the rule's own subderivations, and the target is the emitted `.proj` node at the
same triple. -/
theorem step_proj {env : VEnv} {bo : Name → Option Expr} {lp : Name → List Name}
    {Us : List Name}
    {fl : SEvalFlags} {Γspec Γ : GlobalDeclarations} :
    StepProj env bo lp Us fl Γspec Γ := by
  intro A Sn ctor i np nfR cidx cus disc r cargs henv henvL hfl hct hnp hdiscr ihdiscr hlt
    hdef hcont ihcont ve t₀ t hwt her hlow hspec
  have hΔ : VLCtx.WF env Us.length ([] : VLCtx) := trivial
  have hΓv := hΔ.toCtx
  have hev : SEval env bo Us fl [] (.proj Sn i disc) r :=
    .proj hfl hct hnp hdiscr hlt hdef hcont
  rcases Erases.proj_inv her with hbox | ⟨iid, nps, nf, d, hs, hinf, -, herdisc, rfl⟩
  · exact erases_correct_boxLow henv hwt hbox hlow hspec hev
  obtain ⟨e', rfl, hlowd⟩ := Lower.source_proj hlow rfl
  obtain ⟨w, htrd, hproj⟩ : ∃ w, TrExprS env Us [] disc w ∧
      TrProj env Us.length (VLCtx.toCtx []) Sn i w ve := by
    cases hwt with | proj h1 h2 => exact ⟨_, h1, h2⟩
  obtain ⟨_, usS, _, params, _, _, hpc⟩ := hproj
  obtain ⟨hdec, mib, hmib, ⟨-, oib, hoib, -⟩, hflag⟩ :=
    hspec.blocks hs (reachableFrom_of_mem_constRefs (by simp [constRefs]))
  have hprop : oib.propositional = false := hflag.notPropositional hoib hinf
  have hspecd : ErasesEnv env bo lp Γspec d := hspec.subterm (.proj .refl)
  obtain ⟨dv₀, dv', herdv, hlowdv, hEdisc, hspecdv⟩ := ihdiscr htrd herdisc hlowd hspecd
  obtain ⟨vv, htrvv, hdefvv⟩ := SEval.defeq henv hΔ htrd hdiscr
  have hvvty : env.HasType Us.length (VLCtx.toCtx []) vv
      (VExpr.mkApps (.const Sn usS) params) :=
    VEnv.HasType.defeqU_l henv hΓv hdefvv hpc.major_ty
  have hnotEr : ¬ Erasable env Us.length (VLCtx.toCtx []) vv :=
    not_erasable_of_informative henv A hΓv hdec hinf hvvty
  obtain ⟨rfl, -⟩ := IndArity.inj A hnp hs.arity
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
  case inr.inr => exact absurd hct (constOrigin_not_ctorOf A ho' Sn cidx)
  obtain ⟨rfl, rfl⟩ := CtorOf.inj A hct hc'
  obtain ⟨rfl, rfl, rfl⟩ := IndInfo.inj A hs hi'
  obtain rfl : cidx = 0 := by
    have := CtorOf.lt_nfs A hct hs
    simpa using this
  obtain ⟨hd₂, cargs', rfl, hhd₂, hclen, hcpt⟩ :=
    Lower.source_mkApps (fun _ _ => LBTerm.noConfusion) (fun _ => LBTerm.noConfusion)
      cargs₀ hlowdv
  obtain rfl : hd₂ = .construct iid 0 [] := by
    rcases Lower.source_construct_nil hhd₂ rfl with h | ⟨defs, j, h⟩
    · exact h
    · exact absurd h (Lower.ne_fix_of_block hhd₂ (fun _ => LBTerm.noConfusion) rfl defs j)
  have hpropΓ : isPropositionalInductive Γ iid = false := by
    simp only [isPropositionalInductive, henvL.inds _ _ hmib, hoib, hprop]
  have hcargsLen : cargs₀.length = cargs.length := hcts.length_eq.symm
  have herfield : Erases env Us [] cargs[np + i]! cargs₀[np + i]! :=
    forall₂_getElem! hcts _ hlt
  have hlowfield : Lower Γspec cargs₀[np + i]! cargs'[np + i]! :=
    hcpt _ (by omega)
  have hspecfield : ErasesEnv env bo lp Γspec cargs₀[np + i]! :=
    hspecdv.subterm (subTerm_mkApps_arg _ _ _ (Lower.getElem!_mem (by omega)))
  obtain ⟨_, _, -, htrfield, -⟩ := hdef
  obtain ⟨r₀, r', herr, hlowr, hEr, hspecr⟩ :=
    ihcont htrfield herfield hlowfield hspecfield
  have hlt' : np + i < cargs'.length := by omega
  refine ⟨r₀, r', herr, hlowr, WcbvEval.proj rfl hpropΓ hEdisc ?_ hEr, hspecr⟩
  show cargs'[np + i]? = some cargs'[np + i]!
  rw [getElem!_pos cargs' (np + i) hlt']
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
    bodies :=
      [{ name := "LP", propositional := false, ctors := [{ name := "mk", nargs := 2 }],
         projs := [] }] }

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
