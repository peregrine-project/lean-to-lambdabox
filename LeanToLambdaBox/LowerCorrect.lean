import LeanToLambdaBox.LowerFix
import LeanToLambdaBox.ErasesEnv

/-!
# `lower_correct` at the δ / constructor / fix fragment

The forward simulation of the pass relation `Lower`, on the evaluation fragment a
constant-valued program exercises: a chain of δ-unfoldings whose end is a nullary
constructor node or a λ, and the fix arms that a block member's constant reaches.
`DeltaChain` is that fragment as a sub-relation of `WcbvEval`, `lower_correct_deltaChain`
the simulation on it, and `lowerFix_correct_atom` the block-member step of
`lowerFix_correct` at an empty argument spine.

Three guards are named rather than assumed away, each because the unrestricted statement
is false without it: `LowerNoEta` (`lower_correct_needs_ctorEta_guard` refutes the η arms),
`BlockBodiesLambda` (a block member's specification body must be its own value), and
`DefsSurvive` (the emitted environment answers the constants the specification declares).

`NoBox` and its transport along `Lower` live here too: the capstone asks box-freedom of the
*lowered* value while the first-order theorem proves it of the erasure, and the transport
needs a `NoFix` premise — `noBox_lower_needs_noFix` shows why.
-/

namespace LeanToLambdaBox

open Lean (Name FVarId)

/-! ## Box-freedom -/

mutual

/-- `t` contains no `□`. The box-freedom `[L Def. 6]`'s conclusion asserts of a
first-order answer. -/
def NoBox : LBTerm → Prop
  | .box => False
  | .bvar _ => True
  | .fvar _ => True
  | .const _ => True
  | .prim _ => True
  | .lambda _ b => NoBox b
  | .letIn _ v b => NoBox v ∧ NoBox b
  | .app f a => NoBox f ∧ NoBox a
  | .construct _ _ args => NoBoxArgs args
  | .case _ d alts => NoBox d ∧ NoBoxAlts alts
  | .proj _ e => NoBox e
  | .fix defs _ => NoBoxDefs defs

/-- `NoBox` over the arguments of a block-form constructor node. -/
def NoBoxArgs : List LBTerm → Prop
  | [] => True
  | t :: rest => NoBox t ∧ NoBoxArgs rest

/-- `NoBox` over `case` alternatives. -/
def NoBoxAlts : List (List BinderName × LBTerm) → Prop
  | [] => True
  | (_, b) :: rest => NoBox b ∧ NoBoxAlts rest

/-- `NoBox` over `fix` definitions. -/
def NoBoxDefs : List (@FixDef LBTerm) → Prop
  | [] => True
  | fd :: rest => NoBox fd.body ∧ NoBoxDefs rest
end

/-- `NoBoxArgs` in the natural per-element form. -/
theorem NoBoxArgs_iff (l : List LBTerm) : NoBoxArgs l ↔ ∀ a ∈ l, NoBox a := by
  induction l with
  | nil => simp [NoBoxArgs]
  | cons a rest ih => simp [NoBoxArgs, ih]

/-- `NoBoxAlts` in the natural per-element form. -/
theorem NoBoxAlts_iff (l : List (List BinderName × LBTerm)) :
    NoBoxAlts l ↔ ∀ a ∈ l, NoBox a.2 := by
  induction l with
  | nil => simp [NoBoxAlts]
  | cons a rest ih => obtain ⟨ns, b⟩ := a; simp [NoBoxAlts, ih]

@[simp] theorem NoBox_box : NoBox .box ↔ False := Iff.rfl
@[simp] theorem NoBox_bvar (i : Nat) : NoBox (.bvar i) := trivial
@[simp] theorem NoBox_fvar (x : FVarId) : NoBox (.fvar x) := trivial
@[simp] theorem NoBox_const (kn : Kername) : NoBox (.const kn) := trivial
@[simp] theorem NoBox_prim (p : PrimVal) : NoBox (.prim p) := trivial
@[simp] theorem NoBox_lambda (n : BinderName) (b : LBTerm) :
    NoBox (.lambda n b) ↔ NoBox b := Iff.rfl
@[simp] theorem NoBox_letIn (n : BinderName) (v b : LBTerm) :
    NoBox (.letIn n v b) ↔ NoBox v ∧ NoBox b := Iff.rfl
@[simp] theorem NoBox_app (f a : LBTerm) : NoBox (.app f a) ↔ NoBox f ∧ NoBox a := Iff.rfl
@[simp] theorem NoBox_proj (p : ProjectionInfo) (e : LBTerm) :
    NoBox (.proj p e) ↔ NoBox e := Iff.rfl
@[simp] theorem NoBox_construct (iid : InductiveId) (k : Nat) (args : List LBTerm) :
    NoBox (.construct iid k args) ↔ ∀ a ∈ args, NoBox a := by
  show NoBoxArgs args ↔ _; rw [NoBoxArgs_iff]
@[simp] theorem NoBox_case (ip : InductiveId × Nat) (d : LBTerm)
    (alts : List (List BinderName × LBTerm)) :
    NoBox (.case ip d alts) ↔ NoBox d ∧ ∀ a ∈ alts, NoBox a.2 := by
  show NoBox d ∧ NoBoxAlts alts ↔ _; rw [NoBoxAlts_iff]

/-- Box-freedom of a spine is box-freedom of its head and of every argument. -/
theorem NoBox_mkApps (f : LBTerm) (args : List LBTerm) :
    NoBox (LBTerm.mkApps f args) ↔ NoBox f ∧ ∀ a ∈ args, NoBox a := by
  induction args generalizing f with
  | nil => simp [LBTerm.mkApps]
  | cons a as ih =>
      rw [LBTerm.mkApps, ih]
      constructor
      · rintro ⟨⟨hf, ha⟩, has⟩
        exact ⟨hf, by intro x hx; rcases List.mem_cons.mp hx with rfl | hx; exacts [ha, has x hx]⟩
      · rintro ⟨hf, has⟩
        exact ⟨⟨hf, has a (by simp)⟩, fun x hx => has x (by simp [hx])⟩

/-- Box-freedom of a telescope is box-freedom of its body. -/
theorem NoBox_mkLambdas (ns : List BinderName) (b : LBTerm) :
    NoBox (mkLambdas ns b) ↔ NoBox b := by
  induction ns with
  | nil => rfl
  | cons n ns ih => rw [mkLambdas, NoBox_lambda, ih]

/-- Fix-freedom of a spine is fix-freedom of its head and of every argument. -/
theorem NoFix_mkApps (f : LBTerm) (args : List LBTerm) :
    NoFix (LBTerm.mkApps f args) ↔ NoFix f ∧ ∀ a ∈ args, NoFix a := by
  induction args generalizing f with
  | nil => simp [LBTerm.mkApps]
  | cons a as ih =>
      rw [LBTerm.mkApps, ih]
      constructor
      · rintro ⟨⟨hf, ha⟩, has⟩
        exact ⟨hf, by intro x hx; rcases List.mem_cons.mp hx with rfl | hx; exacts [ha, has x hx]⟩
      · rintro ⟨hf, has⟩
        exact ⟨⟨hf, has a (by simp)⟩, fun x hx => has x (by simp [hx])⟩

/-- Fix-freedom of a telescope is fix-freedom of its body. -/
theorem NoFix_mkLambdas (ns : List BinderName) (b : LBTerm) :
    NoFix (mkLambdas ns b) ↔ NoFix b := by
  induction ns with
  | nil => rfl
  | cons n ns ih => rw [mkLambdas, NoFix_lambda, ih]

/-- The de Bruijn indices an η-expansion applies are box-free. -/
theorem NoBox_bvarsDesc (n : Nat) : ∀ a ∈ bvarsDesc n, NoBox a := by
  intro a ha
  obtain ⟨i, _, rfl⟩ := bvarsDesc_mem ha
  trivial

/-- `NoBoxDefs` in the natural per-element form. -/
theorem NoBoxDefs_iff (l : List (@FixDef LBTerm)) : NoBoxDefs l ↔ ∀ d ∈ l, NoBox d.body := by
  induction l with
  | nil => simp [NoBoxDefs]
  | cons a rest ih => simp [NoBoxDefs, ih]

@[simp] theorem NoBox_fix (defs : List (@FixDef LBTerm)) (i : Nat) :
    NoBox (.fix defs i) ↔ ∀ d ∈ defs, NoBox d.body := by
  show NoBoxDefs defs ↔ _; rw [NoBoxDefs_iff]

/-- `shift` moves indices and introduces no box. -/
theorem NoBox_shift : ∀ (t : LBTerm) (d c : Nat), NoBox t → NoBox (LBTerm.shift d c t) := by
  intro t
  induction t using LBTerm.recData with
  | hbox => intro _ _ h; exact h.elim
  | hbvar i => intro d c _; simp only [LBTerm.shift]; split <;> trivial
  | hfvar | hconst | hprim => intro _ _ _; trivial
  | hlam n b ih => intro d c h; exact ih d (c + 1) h
  | hletIn n v b ihv ihb => intro d c h; exact ⟨ihv d c h.1, ihb d (c + 1) h.2⟩
  | happ f a ihf iha => intro d c h; exact ⟨ihf d c h.1, iha d c h.2⟩
  | hproj p e ih => intro d c h; exact ih d c h
  | hconstruct iid k args ih =>
      intro d c h
      rw [NoBox_construct] at h
      simp only [LBTerm.shift, NoBox_construct, LBTerm.shiftArgs_eq_map, List.mem_map]
      rintro a ⟨x, hx, rfl⟩
      exact ih x hx d c (h x hx)
  | hcase info discr alts ihd iha =>
      intro d c h
      rw [NoBox_case] at h
      simp only [LBTerm.shift, NoBox_case, LBTerm.shiftAlts_eq_map, List.mem_map]
      refine ⟨ihd d c h.1, ?_⟩
      rintro a ⟨x, hx, rfl⟩
      exact iha x hx d _ (h.2 x hx)
  | hfix defs i ih =>
      intro d c h
      rw [NoBox_fix] at h
      simp only [LBTerm.shift, NoBox_fix, LBTerm.shiftDefs_eq_map, List.mem_map]
      rintro a ⟨x, hx, rfl⟩
      exact ih x hx d _ (h x hx)

/-- The naive transport of box-freedom along `Lower` is false: `Lower.fixConst` relates
the box-free `.const kn` to the block's `.fix`, whose definitions carry the boxes of the
members' bodies. Any transport needs a premise excluding a `.fix` in the target. -/
theorem noBox_lower_needs_noFix :
    ¬ (∀ (Γ : GlobalDeclarations) (s t : LBTerm), Lower Γ s t → NoBox s → NoBox t) := by
  intro H
  exact H LowerFixFixture.specEnv (.const LowerFixFixture.kn₀)
    (.fix LowerFixFixture.defs 0)
    (Lower.fixConst' LowerFixFixture.lowerfix_nv (by rfl)) trivial |>.1

/-! ## Source-side inversion -/

/-- A spine that is a constant is that constant, applied to nothing. -/
theorem mkApps_eq_const {f : LBTerm} {args : List LBTerm} {kn : Kername}
    (h : LBTerm.mkApps f args = .const kn) : args = [] ∧ f = .const kn := by
  cases args with
  | nil => exact ⟨rfl, h⟩
  | cons a as =>
      obtain ⟨g, b, he⟩ := mkApps_cons_is_app f a as
      rw [he] at h; exact LBTerm.noConfusion h

/-- A spine that is a λ is that λ, applied to nothing. -/
theorem mkApps_eq_lambda {f : LBTerm} {args : List LBTerm} {n : BinderName} {b : LBTerm}
    (h : LBTerm.mkApps f args = .lambda n b) : args = [] ∧ f = .lambda n b := by
  cases args with
  | nil => exact ⟨rfl, h⟩
  | cons a as =>
      obtain ⟨g, c, he⟩ := mkApps_cons_is_app f a as
      rw [he] at h; exact LBTerm.noConfusion h

/-- A spine that is a constructor node is that node, applied to nothing. -/
theorem mkApps_eq_construct {f : LBTerm} {args : List LBTerm} {iid : InductiveId} {k : Nat}
    {as : List LBTerm} (h : LBTerm.mkApps f args = .construct iid k as) :
    args = [] ∧ f = .construct iid k as := by
  cases args with
  | nil => exact ⟨rfl, h⟩
  | cons a as' =>
      obtain ⟨g, c, he⟩ := mkApps_cons_is_app f a as'
      rw [he] at h; exact LBTerm.noConfusion h

/-- A non-empty spine is an application. -/
theorem mkApps_ne_nil_is_app {f : LBTerm} {args : List LBTerm} (h : args ≠ []) :
    ∃ g b, LBTerm.mkApps f args = .app g b := by
  cases args with
  | nil => exact absurd rfl h
  | cons a as => exact mkApps_cons_is_app f a as

/-- Both `ElimBody` shapes are a λ-telescope or a `.fix` node. -/
theorem elimBody_shape {iid : InductiveId} {np dp : Nat} {nfs : List Nat} {h : LBTerm}
    (he : ElimBody iid np dp nfs h) :
    (∃ n b, h = .lambda n b) ∨ ∃ defs j, h = .fix defs j := by
  cases he with
  | cases =>
      refine .inl ⟨.anon, mkLambdas (List.replicate (dp + nfs.length) .anon)
        (.case (iid, np) (.bvar nfs.length) (elimAlts nfs)), ?_⟩
      rw [mkElimBody]
      have : dp + 1 + nfs.length = (dp + nfs.length) + 1 := by omega
      rw [this, List.replicate_succ, mkLambdas]
  | recur => exact .inr ⟨_, 0, rfl⟩

/-- An eliminator head is never a constant unless the environment declares it one. -/
theorem elimHeadOf_const {Γ : GlobalDeclarations} {kn : Kername} {iid : InductiveId}
    {np dp : Nat} {nfs : List Nat} (h : ElimHeadOf Γ (.const kn) iid np dp nfs) :
    ElimDecl Γ kn iid np dp nfs := by
  rcases h with ⟨kn', he, hd⟩ | he
  · injection he with he; exact he ▸ hd
  · rcases elimBody_shape he with ⟨n, b, hb⟩ | ⟨defs, j, hb⟩ <;> exact LBTerm.noConfusion hb

/-- What a constant can lower to: itself, a nullary constructor node, either η-expansion,
or a block's `.fix` node. -/
theorem Lower.source_const {Γ : GlobalDeclarations} {s t : LBTerm} {kn : Kername}
    (h : Lower Γ s t) (hs : s = .const kn) :
    (t = .const kn ∧ ¬ RuntimeKey Γ kn)
    ∨ (∃ iid k, CtorDecl Γ kn iid k ∧ cstrArity Γ iid k = 0 ∧ t = .construct iid k [])
    ∨ (∃ iid k ns, CtorDecl Γ kn iid k ∧ ns ≠ [] ∧ ns.length = cstrArity Γ iid k ∧
        t = mkLambdas ns (LBTerm.mkApps (.construct iid k []) (bvarsDesc ns.length)))
    ∨ (∃ iid np dp nfs ns body, ElimDecl Γ kn iid np dp nfs ∧ ns ≠ [] ∧
        ns.length = dp + 1 + nfs.length ∧
        Lower Γ (LBTerm.mkApps (.const kn) (bvarsDesc ns.length)) body ∧ t = mkLambdas ns body)
    ∨ (∃ defs j, t = .fix defs j) := by
  cases h with
  | @const kn' hk =>
      have he : kn' = kn := by injection hs
      exact .inl ⟨by rw [he], by rw [← he]; exact hk⟩
  | box | bvar | fvar | prim | lambda | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion hs
  | @fixConst kn' kns bs bs' ids defs j => exact .inr (.inr (.inr (.inr ⟨defs, j, rfl⟩)))
  | @fixBody b kns bs bs' ids defs j => exact .inr (.inr (.inr (.inr ⟨defs, j, rfl⟩)))
  | @ctorApp kn' iid k args args' hc hsat hlen ha =>
      obtain ⟨rfl, he⟩ := mkApps_eq_const hs
      have hk : kn' = kn := by injection he
      subst hk
      have : args' = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst this
      exact .inr (.inl ⟨iid, k, hc, Nat.le_zero.mp (by simpa using hsat), rfl⟩)
  | @ctorEta kn' iid k args args' ns hc hns hund hlen ha =>
      obtain ⟨rfl, he⟩ := mkApps_eq_const hs
      have hk : kn' = kn := by injection he
      subst hk
      have : args' = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst this
      exact .inr (.inr (.inl ⟨iid, k, ns, hc, hns, by simpa using hund, by simp⟩))
  | @elimApp hd iid np dp nfs pre disc disc' minors alts extra extra' =>
      obtain ⟨g, b, he⟩ := mkApps_ne_nil_is_app (f := hd)
        (args := pre ++ disc :: minors ++ extra) (by cases pre <;> simp)
      rw [he] at hs; exact LBTerm.noConfusion hs
  | @elimEta hd iid np dp nfs args ns body hh hns hund hsat =>
      obtain ⟨rfl, he⟩ := mkApps_eq_const hs
      subst he
      refine .inr (.inr (.inr (.inl ⟨iid, np, dp, nfs, ns, body, elimHeadOf_const hh, hns,
        by simpa using hund, ?_, rfl⟩)))
      simpa using hsat

/-- What a nullary constructor node can lower to: itself, or a block's `.fix` node. -/
theorem Lower.source_construct_nil {Γ : GlobalDeclarations} {s t : LBTerm}
    {iid : InductiveId} {k : Nat} (h : Lower Γ s t) (hs : s = .construct iid k []) :
    t = .construct iid k [] ∨ ∃ defs j, t = .fix defs j := by
  cases h with
  | box | bvar | fvar | prim | const | lambda | letIn | app | proj | «case» =>
      exact LBTerm.noConfusion hs
  | @fixConst kn kns bs bs' ids defs j => exact .inr ⟨defs, j, rfl⟩
  | @fixBody b kns bs bs' ids defs j => exact .inr ⟨defs, j, rfl⟩
  | @construct iid' k' args args' hlen ha =>
      injection hs with hi hk hargs
      subst hi; subst hk; subst hargs
      have : args' = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst this; exact .inl rfl
  | @ctorApp kn iid' k' args args' =>
      obtain ⟨rfl, he⟩ := mkApps_eq_construct hs; exact LBTerm.noConfusion he
  | @ctorEta kn iid' k' args args' ns =>
      obtain ⟨rfl, he⟩ := mkApps_eq_construct hs; exact LBTerm.noConfusion he
  | @elimApp hd iid' np dp nfs pre disc disc' minors alts extra extra' =>
      obtain ⟨g, b, he⟩ := mkApps_ne_nil_is_app (f := hd)
        (args := pre ++ disc :: minors ++ extra) (by cases pre <;> simp)
      rw [he] at hs; exact LBTerm.noConfusion hs
  | @elimEta hd iid' np dp nfs args ns body hh =>
      obtain ⟨rfl, he⟩ := mkApps_eq_construct hs
      subst he
      rcases hh with ⟨kn, hk, _⟩ | hb
      · exact LBTerm.noConfusion hk
      · rcases elimBody_shape hb with ⟨n, c, hc⟩ | ⟨defs, j, hc⟩ <;> exact LBTerm.noConfusion hc

/-- What a λ can lower to: a λ, or a block's `.fix` node. -/
theorem Lower.source_lambda {Γ : GlobalDeclarations} {s t : LBTerm} {n : BinderName}
    {b : LBTerm} (h : Lower Γ s t) (hs : s = .lambda n b) :
    (∃ n' b', t = .lambda n' b') ∨ ∃ defs j, t = .fix defs j := by
  cases h with
  | box | bvar | fvar | prim | const | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion hs
  | @lambda n₀ n' b₀ b' => exact .inl ⟨n', b', rfl⟩
  | @fixConst kn kns bs bs' ids defs j => exact .inr ⟨defs, j, rfl⟩
  | @fixBody b₀ kns bs bs' ids defs j => exact .inr ⟨defs, j, rfl⟩
  | @ctorApp kn iid k args args' =>
      obtain ⟨rfl, he⟩ := mkApps_eq_lambda hs; exact LBTerm.noConfusion he
  | @ctorEta kn iid k args args' ns _ hns =>
      obtain ⟨n', c, he⟩ := mkLambdas_is_lambda hns _
      exact .inl ⟨n', c, he⟩
  | @elimApp hd iid np dp nfs pre disc disc' minors alts extra extra' =>
      obtain ⟨g, c, he⟩ := mkApps_ne_nil_is_app (f := hd)
        (args := pre ++ disc :: minors ++ extra) (by cases pre <;> simp)
      rw [he] at hs; exact LBTerm.noConfusion hs
  | @elimEta hd iid np dp nfs args ns body _ hns =>
      obtain ⟨n', c, he⟩ := mkLambdas_is_lambda hns _
      exact .inl ⟨n', c, he⟩

/-! ## The evaluation fragment -/

/-- The evaluation fragment a constant-valued program exercises: a chain of δ-unfoldings
whose end is a nullary constructor node or a λ. A sub-relation of `WcbvEval`
(`DeltaChain.toWcbvEval`), written as its own inductive so that the simulation below is an
induction over exactly these steps. -/
inductive DeltaChain (Γ : GlobalDeclarations) : LBTerm → LBTerm → Prop where
  /-- A declared nullary constructor node is its own value. -/
  | ctor {iid : InductiveId} {k ar : Nat} (har : constructorArity Γ iid k = some ar) :
      DeltaChain Γ (.construct iid k []) (.construct iid k [])
  /-- A λ is its own value. -/
  | lam (n : BinderName) (b : LBTerm) : DeltaChain Γ (.lambda n b) (.lambda n b)
  /-- δ: unfold a declared constant and continue in its body. -/
  | delta {kn : Kername} {body v : LBTerm} (hlk : DefnDecl Γ kn body)
      (hb : DeltaChain Γ body v) : DeltaChain Γ (.const kn) v

/-- The fragment is a sub-relation of the target semantics, at any applied-form flags. -/
theorem DeltaChain.toWcbvEval {Γ : GlobalDeclarations} {fl : WcbvFlags} {t v : LBTerm}
    (hb : fl.with_constructor_as_block = false) (h : DeltaChain Γ t v) : WcbvEval Γ fl t v := by
  induction h with
  | ctor har => exact .construct_atom hb har
  | lam n b => exact .lam n b
  | delta hlk _ ih => exact .delta hlk ih

/-- A constructor node's value is itself, and its inductive is declared. -/
theorem DeltaChain.construct_inv {Γ : GlobalDeclarations} {iid : InductiveId} {k : Nat}
    {v : LBTerm} (h : DeltaChain Γ (.construct iid k []) v) :
    v = .construct iid k [] ∧ ∃ ar, constructorArity Γ iid k = some ar := by
  cases h with | ctor har => exact ⟨rfl, _, har⟩

/-- A λ's value is itself. -/
theorem DeltaChain.lambda_inv {Γ : GlobalDeclarations} {n : BinderName} {b v : LBTerm}
    (h : DeltaChain Γ (.lambda n b) v) : v = .lambda n b := by
  cases h with | lam => rfl

/-! ## The guards -/

/-- No constant of `Γ` is η-expanded by the pass. Without it the simulation is false:
`lower_correct_needs_ctorEta_guard`. -/
def LowerNoEta (Γ : GlobalDeclarations) : Prop :=
  ∀ (kn : Kername) (n : BinderName) (b : LBTerm), ¬ Lower Γ (.const kn) (.lambda n b)

/-- Every member body of every block the pass builds out of `Γ` is a λ, hence its own
value. This is `LowerBlock.lambda_of_fixLambda`'s conclusion, taken as the premise the δ
step needs: the target `.fix` node is an atom, so the source body must be one too. -/
def BlockBodiesLambda (Γ : GlobalDeclarations) : Prop :=
  ∀ (kns : List Kername) (bs bs' : List LBTerm) (ids : List FVarId)
    (defs : List (@FixDef LBTerm)), LowerBlock Γ kns bs bs' ids defs →
    ∀ j, j < kns.length → isLambda bs[j]! = true

/-- Every specification definition that is not a runtime key is answered by the emitted
environment. `LowerEnv.defsTotal`'s second disjunct records that the constant is a block
member but not that the emitted environment declares it, and a δ step on an unanswered
constant is stuck. -/
def DefsSurvive (Γspec Γ : GlobalDeclarations) : Prop :=
  ∀ (kn : Kername) (b₀ : LBTerm), DefnDecl Γspec kn b₀ → ¬ RuntimeKey Γspec kn →
    ∃ b, DefnDecl Γ kn b

/-! ## Environment transport -/

/-- Two declarations of one constant carry the same body. -/
theorem DefnDecl.inj {Γ : GlobalDeclarations} {kn : Kername} {b b' : LBTerm}
    (h : DefnDecl Γ kn b) (h' : DefnDecl Γ kn b') : b = b' := by
  rw [DefnDecl] at h h'
  rw [h] at h'
  injection h' with h'; injection h' with h'; injection h' with h'
  exact Option.some.inj h'

/-- An in-range `getElem!` is the `getElem?`. -/
theorem getElem?_getElem! {α : Type} [Inhabited α] {l : List α} {i : Nat}
    (h : i < l.length) : l[i]? = some l[i]! := by
  rw [List.getElem?_eq_getElem h, getElem!_pos l i h]

/-- Constructor arities are read off the inductive block, which the emitted environment
carries over unchanged. -/
theorem LowerEnv.constructorArity {Γspec Γ : GlobalDeclarations} (hE : LowerEnv Γspec Γ)
    {iid : InductiveId} {k ar : Nat} (h : constructorArity Γspec iid k = some ar) :
    constructorArity Γ iid k = some ar := by
  unfold LeanToLambdaBox.constructorArity at h ⊢
  cases hl : LBTerm.envLookup Γspec iid.mutualBlockName with
  | none => rw [hl] at h; exact absurd h (by simp)
  | some d =>
      cases d with
      | constantDecl c => rw [hl] at h; exact absurd h (by simp)
      | inductiveDecl body => rw [hE.inds _ _ hl]; rw [hl] at h; exact h

/-- A `true` `isLambda` exhibits the λ. -/
theorem isLambda_eq_true {t : LBTerm} (h : isLambda t = true) : ∃ n b, t = .lambda n b := by
  cases t <;> simp [isLambda] at h ⊢

/-! ## The simulation -/

/-- **`lower_correct` on the δ / constructor / fix fragment.** A source evaluation that is
a δ-chain ending in a nullary constructor node or a λ is simulated by the emitted
environment, at the same flags, with the value still related.

The three guards are the fragment's, not bookkeeping: `hne` excludes the η arms, which are
genuinely unsound for a forward simulation (`lower_correct_needs_ctorEta_guard`); `hblk`
makes a block member's body its own value, which the `.fix` atom on the target demands; and
`hsurv` supplies the emitted declaration a δ step needs. -/
theorem lower_correct_deltaChain {Γspec Γ : GlobalDeclarations} (hE : LowerEnv Γspec Γ)
    (hsurv : DefsSurvive Γspec Γ) (hne : LowerNoEta Γspec) (hblk : BlockBodiesLambda Γspec)
    {t v : LBTerm} (hev : DeltaChain Γspec t v) :
    ∀ {t' : LBTerm}, Lower Γspec t t' →
      ∃ v', Lower Γspec v v' ∧ WcbvEval Γ eraseFlags t' v' := by
  induction hev with
  | @ctor iid k ar har =>
      intro t' h
      rcases Lower.source_construct_nil h rfl with rfl | ⟨defs, j, rfl⟩
      · exact ⟨_, h, .construct_atom rfl (hE.constructorArity har)⟩
      · exact ⟨_, h, .fix_atom defs j⟩
  | lam n b =>
      intro t' h
      rcases Lower.source_lambda h rfl with ⟨n', b', rfl⟩ | ⟨defs, j, rfl⟩
      · exact ⟨_, h, .lam n' b'⟩
      · exact ⟨_, h, .fix_atom defs j⟩
  | @delta kn body v hlk hb ih =>
      intro t' h
      rcases Lower.source_const h rfl with
        ⟨rfl, hnr⟩ | ⟨iid, k, hc, hsat, rfl⟩ | ⟨iid, k, ns, hc, hns, hlen, rfl⟩
        | ⟨iid, np, dp, nfs, ns, body', hd, hns, hlen, hlow, rfl⟩ | ⟨defs, j, rfl⟩
      · -- the constant survives as itself
        obtain ⟨b, hb'⟩ := hsurv kn body hlk hnr
        rcases hE.defs kn body b hlk hb' with hlow | ⟨kns, bs, defs, j, hfix, hj, rfl⟩
        · obtain ⟨v', hv', hev'⟩ := ih hlow
          exact ⟨v', hv', .delta hb' hev'⟩
        · obtain ⟨bs', ids, hblock⟩ := hfix
          obtain ⟨hjl, hkj⟩ := Lower.getElem!_of_getElem? hj
          have hdecl := hblock.hdecl j hjl
          rw [hkj] at hdecl
          have hbody : body = bs[j]! := hlk.inj hdecl
          obtain ⟨n₀, c₀, hlam⟩ := isLambda_eq_true (hblk _ _ _ _ _ hblock j hjl)
          have hjbs : j < bs.length := by rw [hblock.hb]; exact hjl
          have hv : v = bs[j]! := by
            have hd' : DeltaChain Γspec bs[j]! v := hbody ▸ hb
            rw [hlam] at hd' ⊢
            exact hd'.lambda_inv
          rw [hv]
          exact ⟨_, Lower.fixBody' hblock (getElem?_getElem! hjbs)
            (by rw [hblock.hd]; exact hjl), .delta hb' (.fix_atom _ _)⟩
      · -- a nullary constructor constant becomes the constructor node
        have hbody : body = .construct iid k [] := hlk.inj hc
        subst hbody
        obtain ⟨hv, ar, har⟩ := hb.construct_inv
        subst hv
        exact ⟨_, .construct rfl (fun i hi => absurd hi (by simp)),
          .construct_atom rfl (hE.constructorArity har)⟩
      · obtain ⟨n', c, he⟩ := mkLambdas_is_lambda hns _
        rw [he] at h; exact absurd h (hne kn n' c)
      · obtain ⟨n', c, he⟩ := mkLambdas_is_lambda hns _
        rw [he] at h; exact absurd h (hne kn n' c)
      · -- the constant is a block member: the target `.fix` is an atom
        obtain ⟨kns, bs, bs', ids, hblock, hcase⟩ := Lower.target_fix h rfl
        rcases hcase with ⟨kn', hkn, hj⟩ | ⟨hj, hjl⟩
        · injection hkn with hkn
          subst hkn
          obtain ⟨hjl, hkj⟩ := Lower.getElem!_of_getElem? hj
          have hdecl := hblock.hdecl j hjl
          rw [hkj] at hdecl
          have hbody : body = bs[j]! := hlk.inj hdecl
          obtain ⟨n₀, c₀, hlam⟩ := isLambda_eq_true (hblk _ _ _ _ _ hblock j hjl)
          have hjbs : j < bs.length := by rw [hblock.hb]; exact hjl
          have hv : v = bs[j]! := by
            have hd' : DeltaChain Γspec bs[j]! v := hbody ▸ hb
            rw [hlam] at hd' ⊢
            exact hd'.lambda_inv
          rw [hv]
          exact ⟨_, Lower.fixBody' hblock (getElem?_getElem! hjbs)
            (by rw [hblock.hd]; exact hjl), .fix_atom _ _⟩
        · obtain ⟨hjl', hkj⟩ := Lower.getElem!_of_getElem? hj
          have := hblk _ _ _ _ _ hblock j (by rw [hblock.hb] at hjl'; exact hjl')
          rw [hkj] at this
          exact absurd this (by simp [isLambda])

/-! ## The fix arm -/

/-- **`lowerFix_correct` at an empty argument spine.** A block member's constant, whose
target is the block's `.fix` node, is simulated: the source δ-unfolds to the member's
specification body, which is its own value because it is a λ, and the target `.fix` is an
atom. The two are related by `Lower.fixBody'` — the arm design finding F1 added.

`hlam` is `LowerBlock.lambda_of_fixLambda`'s conclusion. It is load-bearing rather than
bookkeeping: at an empty spine the source value is pinned to the member's body, and the
only value-side fix arm demands that body verbatim. -/
theorem lowerFix_correct_atom {Γspec Γ : GlobalDeclarations} {kns : List Kername}
    {bs bs' : List LBTerm} {ids : List FVarId} {defs : List (@FixDef LBTerm)} {j : Nat}
    {kn : Kername} {v : LBTerm} (hblock : LowerBlock Γspec kns bs bs' ids defs)
    (hlam : ∀ i, i < kns.length → isLambda bs[i]! = true) (hj : kns[j]? = some kn)
    (hev : WcbvEval Γspec eraseFlags (.const kn) v) :
    ∃ v', Lower Γspec v v' ∧ WcbvEval Γ eraseFlags (.fix defs j) v' := by
  obtain ⟨hjl, hkj⟩ := Lower.getElem!_of_getElem? hj
  have hdecl := hblock.hdecl j hjl
  rw [hkj] at hdecl
  have hjbs : j < bs.length := by rw [hblock.hb]; exact hjl
  obtain ⟨n₀, c₀, hb⟩ := isLambda_eq_true (hlam j hjl)
  cases hev with
  | delta hlk hbody =>
      have hbeq : bs[j]! = _ := hdecl.inj hlk
      rw [← hbeq, hb] at hbody
      cases hbody with
      | lam =>
          refine ⟨_, ?_, .fix_atom _ _⟩
          rw [← hb]
          exact Lower.fixBody' hblock (getElem?_getElem! hjbs) (by rw [hblock.hd]; exact hjl)

/-! ## Why the η guard is there -/

open LowerFixFixture.EtaCounterexample in
/-- **The unrestricted `lower_correct` is false at the `ctorEta` arm**, at every emitted
environment. An under-applied constructor constant δ-unfolds, on the specification side, to
the applied-form constructor node, which is a value; the pass sends the same constant to the
η-expanded λ, which is a value too; and no arm of `Lower` relates a constructor node to a λ.

The witness is a one-inductive environment with a single unary constructor. This is why
`lower_correct_deltaChain` takes `LowerNoEta`, and why an eraser-side guard on η-expanded
constants (finding F-ETA) is load-bearing rather than cosmetic. -/
theorem lower_correct_needs_ctorEta_guard (Γ : GlobalDeclarations) :
    Lower env (.const ctorKn) etaBody ∧
    WcbvEval env eraseFlags (.const ctorKn) (.construct iid 0 []) ∧
    ¬ ∃ v', Lower env (.construct iid 0 []) v' ∧ WcbvEval Γ eraseFlags etaBody v' := by
  refine ⟨lower_eta, .delta ctorDecl (.construct_atom rfl rfl), ?_⟩
  rintro ⟨v', hlow, hev⟩
  cases hev with
  | lam =>
      rcases Lower.source_construct_nil hlow rfl with he | ⟨defs, j, he⟩ <;>
        exact LBTerm.noConfusion he

end LeanToLambdaBox
