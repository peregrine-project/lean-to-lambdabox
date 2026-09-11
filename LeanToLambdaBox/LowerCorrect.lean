import LeanToLambdaBox.LowerFix
import LeanToLambdaBox.ErasesEnv

/-!
# `lower_correct` — the forward simulation of the pass relation `Lower`

Two fragments. `lower_correct_deltaChain` covers the evaluation fragment a constant-valued
program exercises — a chain of δ-unfoldings ending in a nullary constructor node or a λ,
written as `DeltaChain` — over all of `Lower`. `lower_correct_plain` covers *every*
evaluation rule that fires at `eraseFlags`, over the sub-relation `LowerPlain`: `Lower`
minus its three eliminator-shaped arms. The two guarded-`fix` rules are covered vacuously —
`LowerPlain.fixSpine_absurd` shows their source has no image in the fragment.

Those three arms are omitted for two different reasons. `ctorEta` and `elimEta` are
**refuted**: `lower_correct_needs_ctorEta_guard` and `lower_correct_needs_elimBody_head`
each exhibit a `Lower` pair whose source evaluates and whose value has no image the target
reaches. The second refutation holds at the *empty* specification environment with every
guard the design names satisfied, so no hypothesis on the environments repairs it —
`ElimHeadOf`'s second disjunct admits the runtime library's own eliminator body as a head
everywhere. `elimApp` is not refuted; it is out of reach of a structural induction on
`WcbvEval`, because the ι decomposition of an eliminator spine produces derivations that
are not premises of the rule the spine's own derivation ends with.

Guards. `LowerNoEta` pins every constructor constant's arity to `0`; `BlockBodiesLambda`,
`BlockBodiesPlain` and `BlockDefsLambda` are the three block facts a fix unfolding needs;
`DefsSurvive` and `LowerEnvPlain` are the environment's side of a δ step.

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


/-! ## Source-side inversion at every node shape

Four of the pass's arms are indexed by an application spine and two by a λ-telescope, so
inverting a derivation at a given *source* shape means ruling those out first. The `.fix`
target is ruled out wherever `BlockBodiesLambda` applies — a block member's specification
body is a λ, so no other source reaches a `.fix` except a member's own constant.
-/

/-- A spine whose value is not an application is its head, applied to nothing. -/
theorem mkApps_eq_of_ne_app {f u : LBTerm} {args : List LBTerm}
    (hu : ∀ g b, u ≠ .app g b) (h : LBTerm.mkApps f args = u) : args = [] ∧ f = u := by
  cases args with
  | nil => exact ⟨rfl, h⟩
  | cons a as =>
      obtain ⟨g, b, he⟩ := mkApps_cons_is_app f a as
      exact absurd (h.symm.trans he) (hu g b)

/-- Only a constant or a λ is lowered to a block's `.fix` node. -/
theorem Lower.notFix_of_block {Γ : GlobalDeclarations} (hblk : BlockBodiesLambda Γ)
    {s : LBTerm} {defs : List (@FixDef LBTerm)} {j : Nat} (h : Lower Γ s (.fix defs j)) :
    (∃ kn, s = .const kn) ∨ isLambda s = true := by
  obtain ⟨kns, bs, bs', ids, hblock, hcase⟩ := Lower.target_fix h rfl
  rcases hcase with ⟨kn, rfl, _⟩ | ⟨hj, hjl⟩
  · exact .inl ⟨kn, rfl⟩
  · obtain ⟨hjb, hjeq⟩ := Lower.getElem!_of_getElem? hj
    have := hblk _ _ _ _ _ hblock j (by rw [hblock.hb] at hjb; exact hjb)
    rw [hjeq] at this
    exact .inr this

/-- Under `BlockBodiesLambda`, a source that is neither a constant nor a λ has no `.fix`
image: the only two arms with a `.fix` target are the block member's constant and its own
specification body, which the guard pins to a λ. -/
theorem Lower.ne_fix_of_block {Γ : GlobalDeclarations} (hblk : BlockBodiesLambda Γ)
    {s t : LBTerm} (h : Lower Γ s t) (hc : ∀ kn, s ≠ .const kn) (hl : isLambda s = false)
    (defs : List (@FixDef LBTerm)) (j : Nat) : t ≠ .fix defs j := by
  intro ht
  subst ht
  rcases Lower.notFix_of_block hblk h with ⟨kn, hk⟩ | hlam
  · exact hc kn hk
  · rw [hl] at hlam; exact Bool.noConfusion hlam

/-- `□` is lowered to `□`. -/
theorem Lower.source_box {Γ : GlobalDeclarations} (hblk : BlockBodiesLambda Γ) {s t : LBTerm}
    (h : Lower Γ s t) (hs : s = .box) : t = .box := by
  have hnf := Lower.ne_fix_of_block hblk h (by rw [hs]; exact fun _ => LBTerm.noConfusion)
    (by rw [hs]; rfl)
  cases h with
  | box => rfl
  | bvar | fvar | prim | const | lambda | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion hs
  | fixConst | fixBody => exact absurd rfl (hnf _ _)
  | @ctorApp kn iid k args args' =>
      obtain ⟨rfl, he⟩ := mkApps_eq_of_ne_app (fun _ _ => LBTerm.noConfusion) hs
      exact LBTerm.noConfusion he
  | @ctorEta kn iid k args args' ns =>
      obtain ⟨rfl, he⟩ := mkApps_eq_of_ne_app (fun _ _ => LBTerm.noConfusion) hs
      exact LBTerm.noConfusion he
  | @elimApp hd iid np dp nfs pre disc disc' minors alts extra extra' =>
      obtain ⟨g, b, he⟩ := mkApps_ne_nil_is_app (f := hd)
        (args := pre ++ disc :: minors ++ extra) (by cases pre <;> simp)
      rw [he] at hs; exact LBTerm.noConfusion hs
  | @elimEta hd iid np dp nfs args ns body hh =>
      obtain ⟨rfl, he⟩ := mkApps_eq_of_ne_app (fun _ _ => LBTerm.noConfusion) hs
      subst he
      rcases hh with ⟨kn, hk, _⟩ | hb
      · exact LBTerm.noConfusion hk
      · rcases elimBody_shape hb with ⟨n, c, hc⟩ | ⟨defs, j, hc⟩ <;> exact LBTerm.noConfusion hc


/-- A de Bruijn index is lowered to itself. -/
theorem Lower.source_bvar {Γ : GlobalDeclarations} (hblk : BlockBodiesLambda Γ)
    {s t : LBTerm} {i : Nat} (h : Lower Γ s t) (hs : s = .bvar i) :
    t = .bvar i := by
  have hnf := Lower.ne_fix_of_block hblk h (by rw [hs]; exact fun _ => LBTerm.noConfusion)
    (by rw [hs]; rfl)
  cases h with
  | bvar j => exact hs ▸ rfl
  | box | fvar | prim | const | lambda | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion hs
  | fixConst | fixBody => exact absurd rfl (hnf _ _)
  | @ctorApp kn iid k args args' =>
      obtain ⟨rfl, he⟩ := mkApps_eq_of_ne_app (fun _ _ => LBTerm.noConfusion) hs
      exact LBTerm.noConfusion he
  | @ctorEta kn iid k args args' ns =>
      obtain ⟨rfl, he⟩ := mkApps_eq_of_ne_app (fun _ _ => LBTerm.noConfusion) hs
      exact LBTerm.noConfusion he
  | @elimApp hd iid np dp nfs pre disc disc' minors alts₀ extra extra' =>
      obtain ⟨g, b, he⟩ := mkApps_ne_nil_is_app (f := hd)
        (args := pre ++ disc :: minors ++ extra) (by cases pre <;> simp)
      rw [he] at hs; exact LBTerm.noConfusion hs
  | @elimEta hd iid np dp nfs args ns body hh =>
      obtain ⟨rfl, he⟩ := mkApps_eq_of_ne_app (fun _ _ => LBTerm.noConfusion) hs
      subst he
      rcases hh with ⟨kn, hk, _⟩ | hb
      · exact LBTerm.noConfusion hk
      · rcases elimBody_shape hb with ⟨n, c, hc⟩ | ⟨defs, j, hc⟩ <;> exact LBTerm.noConfusion hc

/-- A free variable is lowered to itself. -/
theorem Lower.source_fvar {Γ : GlobalDeclarations} (hblk : BlockBodiesLambda Γ)
    {s t : LBTerm} {x : FVarId} (h : Lower Γ s t) (hs : s = .fvar x) :
    t = .fvar x := by
  have hnf := Lower.ne_fix_of_block hblk h (by rw [hs]; exact fun _ => LBTerm.noConfusion)
    (by rw [hs]; rfl)
  cases h with
  | fvar y => exact hs ▸ rfl
  | box | bvar | prim | const | lambda | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion hs
  | fixConst | fixBody => exact absurd rfl (hnf _ _)
  | @ctorApp kn iid k args args' =>
      obtain ⟨rfl, he⟩ := mkApps_eq_of_ne_app (fun _ _ => LBTerm.noConfusion) hs
      exact LBTerm.noConfusion he
  | @ctorEta kn iid k args args' ns =>
      obtain ⟨rfl, he⟩ := mkApps_eq_of_ne_app (fun _ _ => LBTerm.noConfusion) hs
      exact LBTerm.noConfusion he
  | @elimApp hd iid np dp nfs pre disc disc' minors alts₀ extra extra' =>
      obtain ⟨g, b, he⟩ := mkApps_ne_nil_is_app (f := hd)
        (args := pre ++ disc :: minors ++ extra) (by cases pre <;> simp)
      rw [he] at hs; exact LBTerm.noConfusion hs
  | @elimEta hd iid np dp nfs args ns body hh =>
      obtain ⟨rfl, he⟩ := mkApps_eq_of_ne_app (fun _ _ => LBTerm.noConfusion) hs
      subst he
      rcases hh with ⟨kn, hk, _⟩ | hb
      · exact LBTerm.noConfusion hk
      · rcases elimBody_shape hb with ⟨n, c, hc⟩ | ⟨defs, j, hc⟩ <;> exact LBTerm.noConfusion hc

/-- A primitive is lowered to itself. -/
theorem Lower.source_prim {Γ : GlobalDeclarations} (hblk : BlockBodiesLambda Γ)
    {s t : LBTerm} {p : PrimVal} (h : Lower Γ s t) (hs : s = .prim p) :
    t = .prim p := by
  have hnf := Lower.ne_fix_of_block hblk h (by rw [hs]; exact fun _ => LBTerm.noConfusion)
    (by rw [hs]; rfl)
  cases h with
  | prim q => exact hs ▸ rfl
  | box | bvar | fvar | const | lambda | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion hs
  | fixConst | fixBody => exact absurd rfl (hnf _ _)
  | @ctorApp kn iid k args args' =>
      obtain ⟨rfl, he⟩ := mkApps_eq_of_ne_app (fun _ _ => LBTerm.noConfusion) hs
      exact LBTerm.noConfusion he
  | @ctorEta kn iid k args args' ns =>
      obtain ⟨rfl, he⟩ := mkApps_eq_of_ne_app (fun _ _ => LBTerm.noConfusion) hs
      exact LBTerm.noConfusion he
  | @elimApp hd iid np dp nfs pre disc disc' minors alts₀ extra extra' =>
      obtain ⟨g, b, he⟩ := mkApps_ne_nil_is_app (f := hd)
        (args := pre ++ disc :: minors ++ extra) (by cases pre <;> simp)
      rw [he] at hs; exact LBTerm.noConfusion hs
  | @elimEta hd iid np dp nfs args ns body hh =>
      obtain ⟨rfl, he⟩ := mkApps_eq_of_ne_app (fun _ _ => LBTerm.noConfusion) hs
      subst he
      rcases hh with ⟨kn, hk, _⟩ | hb
      · exact LBTerm.noConfusion hk
      · rcases elimBody_shape hb with ⟨n, c, hc⟩ | ⟨defs, j, hc⟩ <;> exact LBTerm.noConfusion hc

/-- A `let` is lowered to a `let`, value and body pointwise. -/
theorem Lower.source_letIn {Γ : GlobalDeclarations} (hblk : BlockBodiesLambda Γ)
    {s t : LBTerm} {n : BinderName} {v b : LBTerm} 
    (h : Lower Γ s t) (hs : s = .letIn n v b) :
    ∃ n' v' b', t = .letIn n' v' b' ∧ Lower Γ v v' ∧ Lower Γ b b' := by
  have hnf := Lower.ne_fix_of_block hblk h (by rw [hs]; exact fun _ => LBTerm.noConfusion)
    (by rw [hs]; rfl)
  cases h with
  | @letIn n₀ n' v₀ v' b₀ b' hv hb =>
      injection hs with _ hvv hbb
      subst hvv; subst hbb
      exact ⟨n', v', b', rfl, hv, hb⟩
  | box | bvar | fvar | prim | const | lambda | app | proj | construct | «case» =>
      exact LBTerm.noConfusion hs
  | fixConst | fixBody => exact absurd rfl (hnf _ _)
  | @ctorApp kn iid k args args' =>
      obtain ⟨rfl, he⟩ := mkApps_eq_of_ne_app (fun _ _ => LBTerm.noConfusion) hs
      exact LBTerm.noConfusion he
  | @ctorEta kn iid k args args' ns =>
      obtain ⟨rfl, he⟩ := mkApps_eq_of_ne_app (fun _ _ => LBTerm.noConfusion) hs
      exact LBTerm.noConfusion he
  | @elimApp hd iid np dp nfs pre disc disc' minors alts₀ extra extra' =>
      obtain ⟨g, b, he⟩ := mkApps_ne_nil_is_app (f := hd)
        (args := pre ++ disc :: minors ++ extra) (by cases pre <;> simp)
      rw [he] at hs; exact LBTerm.noConfusion hs
  | @elimEta hd iid np dp nfs args ns body hh =>
      obtain ⟨rfl, he⟩ := mkApps_eq_of_ne_app (fun _ _ => LBTerm.noConfusion) hs
      subst he
      rcases hh with ⟨kn, hk, _⟩ | hb
      · exact LBTerm.noConfusion hk
      · rcases elimBody_shape hb with ⟨n, c, hc⟩ | ⟨defs, j, hc⟩ <;> exact LBTerm.noConfusion hc

/-- A projection is lowered to the same projection of the lowered discriminant. -/
theorem Lower.source_proj {Γ : GlobalDeclarations} (hblk : BlockBodiesLambda Γ)
    {s t : LBTerm} {p : ProjectionInfo} {e : LBTerm} (h : Lower Γ s t) (hs : s = .proj p e) :
    ∃ e', t = .proj p e' ∧ Lower Γ e e' := by
  have hnf := Lower.ne_fix_of_block hblk h (by rw [hs]; exact fun _ => LBTerm.noConfusion)
    (by rw [hs]; rfl)
  cases h with
  | @proj p₀ e₀ e' he =>
      injection hs with hp hee
      subst hp; subst hee
      exact ⟨e', rfl, he⟩
  | box | bvar | fvar | prim | const | lambda | letIn | app | construct | «case» =>
      exact LBTerm.noConfusion hs
  | fixConst | fixBody => exact absurd rfl (hnf _ _)
  | @ctorApp kn iid k args args' =>
      obtain ⟨rfl, he⟩ := mkApps_eq_of_ne_app (fun _ _ => LBTerm.noConfusion) hs
      exact LBTerm.noConfusion he
  | @ctorEta kn iid k args args' ns =>
      obtain ⟨rfl, he⟩ := mkApps_eq_of_ne_app (fun _ _ => LBTerm.noConfusion) hs
      exact LBTerm.noConfusion he
  | @elimApp hd iid np dp nfs pre disc disc' minors alts₀ extra extra' =>
      obtain ⟨g, b, he⟩ := mkApps_ne_nil_is_app (f := hd)
        (args := pre ++ disc :: minors ++ extra) (by cases pre <;> simp)
      rw [he] at hs; exact LBTerm.noConfusion hs
  | @elimEta hd iid np dp nfs args ns body hh =>
      obtain ⟨rfl, he⟩ := mkApps_eq_of_ne_app (fun _ _ => LBTerm.noConfusion) hs
      subst he
      rcases hh with ⟨kn, hk, _⟩ | hb
      · exact LBTerm.noConfusion hk
      · rcases elimBody_shape hb with ⟨n, c, hc⟩ | ⟨defs, j, hc⟩ <;> exact LBTerm.noConfusion hc

/-- A constructor node is lowered argument by argument. -/
theorem Lower.source_construct {Γ : GlobalDeclarations} (hblk : BlockBodiesLambda Γ)
    {s t : LBTerm} {iid : InductiveId} {k : Nat} {args : List LBTerm} (h : Lower Γ s t) (hs : s = .construct iid k args) :
    ∃ args', t = .construct iid k args' ∧ args'.length = args.length ∧
      ∀ i, i < args.length → Lower Γ args[i]! args'[i]! := by
  have hnf := Lower.ne_fix_of_block hblk h (by rw [hs]; exact fun _ => LBTerm.noConfusion)
    (by rw [hs]; rfl)
  cases h with
  | @construct iid₀ k₀ args₀ args' hlen ha =>
      injection hs with hi hk hargs
      subst hi; subst hk; subst hargs
      exact ⟨args', rfl, hlen, ha⟩
  | box | bvar | fvar | prim | const | lambda | letIn | app | proj | «case» =>
      exact LBTerm.noConfusion hs
  | fixConst | fixBody => exact absurd rfl (hnf _ _)
  | @ctorApp kn iid k args args' =>
      obtain ⟨rfl, he⟩ := mkApps_eq_of_ne_app (fun _ _ => LBTerm.noConfusion) hs
      exact LBTerm.noConfusion he
  | @ctorEta kn iid k args args' ns =>
      obtain ⟨rfl, he⟩ := mkApps_eq_of_ne_app (fun _ _ => LBTerm.noConfusion) hs
      exact LBTerm.noConfusion he
  | @elimApp hd iid np dp nfs pre disc disc' minors alts₀ extra extra' =>
      obtain ⟨g, b, he⟩ := mkApps_ne_nil_is_app (f := hd)
        (args := pre ++ disc :: minors ++ extra) (by cases pre <;> simp)
      rw [he] at hs; exact LBTerm.noConfusion hs
  | @elimEta hd iid np dp nfs args ns body hh =>
      obtain ⟨rfl, he⟩ := mkApps_eq_of_ne_app (fun _ _ => LBTerm.noConfusion) hs
      subst he
      rcases hh with ⟨kn, hk, _⟩ | hb
      · exact LBTerm.noConfusion hk
      · rcases elimBody_shape hb with ⟨n, c, hc⟩ | ⟨defs, j, hc⟩ <;> exact LBTerm.noConfusion hc

/-- A `case` is lowered to a `case` with the same inductive, parameter count and branch arities. -/
theorem Lower.source_case {Γ : GlobalDeclarations} (hblk : BlockBodiesLambda Γ)
    {s t : LBTerm} {ip : InductiveId × Nat} {d : LBTerm} {alts : List (List BinderName × LBTerm)} (h : Lower Γ s t) (hs : s = .case ip d alts) :
    ∃ d' alts', t = .case ip d' alts' ∧ Lower Γ d d' ∧ alts'.length = alts.length ∧
      (∀ i, i < alts.length → (alts'[i]!).1.length = (alts[i]!).1.length) ∧
      ∀ i, i < alts.length → Lower Γ (alts[i]!).2 (alts'[i]!).2 := by
  have hnf := Lower.ne_fix_of_block hblk h (by rw [hs]; exact fun _ => LBTerm.noConfusion)
    (by rw [hs]; rfl)
  cases h with
  | @«case» ip₀ d₀ d' alts₀ alts' hd hlen hn hb =>
      injection hs with hi hdd hal
      subst hi; subst hdd; subst hal
      exact ⟨d', alts', rfl, hd, hlen, hn, hb⟩
  | box | bvar | fvar | prim | const | lambda | letIn | app | proj | construct =>
      exact LBTerm.noConfusion hs
  | fixConst | fixBody => exact absurd rfl (hnf _ _)
  | @ctorApp kn iid k args args' =>
      obtain ⟨rfl, he⟩ := mkApps_eq_of_ne_app (fun _ _ => LBTerm.noConfusion) hs
      exact LBTerm.noConfusion he
  | @ctorEta kn iid k args args' ns =>
      obtain ⟨rfl, he⟩ := mkApps_eq_of_ne_app (fun _ _ => LBTerm.noConfusion) hs
      exact LBTerm.noConfusion he
  | @elimApp hd iid np dp nfs pre disc disc' minors alts₀ extra extra' =>
      obtain ⟨g, b, he⟩ := mkApps_ne_nil_is_app (f := hd)
        (args := pre ++ disc :: minors ++ extra) (by cases pre <;> simp)
      rw [he] at hs; exact LBTerm.noConfusion hs
  | @elimEta hd iid np dp nfs args ns body hh =>
      obtain ⟨rfl, he⟩ := mkApps_eq_of_ne_app (fun _ _ => LBTerm.noConfusion) hs
      subst he
      rcases hh with ⟨kn, hk, _⟩ | hb
      · exact LBTerm.noConfusion hk
      · rcases elimBody_shape hb with ⟨n, c, hc⟩ | ⟨defs, j, hc⟩ <;> exact LBTerm.noConfusion hc


/-- A `.fix` in the source reaches only a λ: the relation has no `fix` congruence arm,
and of the two arms whose source can be a `.fix`, `fixBody` is excluded by the guard and
`elimEta` at the recursive eliminator shape has a telescope target. -/
theorem Lower.source_fix {Γ : GlobalDeclarations} (hblk : BlockBodiesLambda Γ)
    {s t : LBTerm} {defs₀ : List (@FixDef LBTerm)} {i : Nat}
    (h : Lower Γ s t) (hs : s = .fix defs₀ i) : isLambda t = true := by
  have hnf := Lower.ne_fix_of_block hblk h (by rw [hs]; exact fun _ => LBTerm.noConfusion)
    (by rw [hs]; rfl)
  cases h with
  | box | bvar | fvar | prim | const | lambda | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion hs
  | fixConst | fixBody => exact absurd rfl (hnf _ _)
  | @ctorApp kn iid k args args' =>
      obtain ⟨rfl, he⟩ := mkApps_eq_of_ne_app (fun _ _ => LBTerm.noConfusion) hs
      exact LBTerm.noConfusion he
  | @ctorEta kn iid k args args' ns =>
      obtain ⟨rfl, he⟩ := mkApps_eq_of_ne_app (fun _ _ => LBTerm.noConfusion) hs
      exact LBTerm.noConfusion he
  | @elimApp hd iid np dp nfs pre disc disc' minors alts₀ extra extra' =>
      obtain ⟨g, b, he⟩ := mkApps_ne_nil_is_app (f := hd)
        (args := pre ++ disc :: minors ++ extra) (by cases pre <;> simp)
      rw [he] at hs; exact LBTerm.noConfusion hs
  | @elimEta hd iid np dp nfs args ns body hh hns =>
      obtain ⟨n, c, he⟩ := mkLambdas_is_lambda hns body
      rw [he]; rfl


/-! ## What the η guard already excludes

`LowerNoEta` is stated at a bare constant, but it reaches every `ctorEta` redex: at a
positive constructor arity the arm sends the bare constant to a λ, so the guard forces
every declared constructor constant to be nullary, and then a constructor spine with
arguments is over-applied — stuck, by `ctorConst_spine_eval`.
-/

/-- Under the η guard every declared constructor constant has arity `0`. -/
theorem LowerNoEta.cstrArity_eq_zero {Γ : GlobalDeclarations} (hne : LowerNoEta Γ)
    {kn : Kername} {iid : InductiveId} {k : Nat} (hc : CtorDecl Γ kn iid k) :
    cstrArity Γ iid k = 0 := by
  by_contra hz
  obtain ⟨m, hm⟩ : ∃ m, cstrArity Γ iid k = m + 1 := ⟨cstrArity Γ iid k - 1, by omega⟩
  have hns : (List.replicate (m + 1) BinderName.anon) ≠ [] := by simp
  have h := Lower.ctorEta (Γ := Γ) (kn := kn) (iid := iid) (k := k) (args := [])
    (args' := []) (ns := List.replicate (m + 1) .anon) hc hns
    (by simp [hm]) rfl (by simp)
  rw [LBTerm.mkApps_nil] at h
  obtain ⟨n', b', he⟩ := mkLambdas_is_lambda hns _
  rw [he] at h
  exact hne kn n' b' h

/-- The value of an applied constructor constant is a constructor spine of at most the
constructor's arity: `construct_app` accumulates only below the arity and `app_cong`
excludes a constructor-headed head, so over-application is stuck. -/
theorem ctorConst_spine_eval {Γ : GlobalDeclarations} {fl : WcbvFlags}
    (hb : fl.with_constructor_as_block = false) {kn : Kername} {iid : InductiveId} {k : Nat}
    (hd : DefnDecl Γ kn (.construct iid k [])) :
    ∀ (n : Nat) {args : List LBTerm}, args.length = n → ∀ {w : LBTerm},
      WcbvEval Γ fl (LBTerm.mkApps (.const kn) args) w →
        ∃ ar vs, constructorArity Γ iid k = some ar ∧ args.length ≤ ar ∧
          vs.length = args.length ∧ w = LBTerm.mkApps (.construct iid k []) vs := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro args hn w hev
    rcases List.eq_nil_or_concat args with rfl | ⟨init, last, rfl⟩
    · rw [LBTerm.mkApps_nil] at hev
      cases hev with
      | delta hlk hbody =>
          rw [← hd.inj hlk] at hbody
          cases hbody with
          | construct hbl => rw [hb] at hbl; exact absurd hbl (by simp)
          | construct_atom _ har => exact ⟨_, [], har, by simp, rfl, by simp [LBTerm.mkApps]⟩
    · rw [List.concat_eq_append, LBTerm.mkApps_concat] at hev
      have hlt : init.length < n := by
        rw [← hn]; simp only [List.concat_eq_append, List.length_append, List.length_cons]; omega
      cases hev with
      | beta hf _ _ =>
          obtain ⟨ar, vs, _, _, _, he⟩ := ih init.length hlt rfl hf
          exact absurd (congrArg LBTerm.spineHead he) (by simp [LBTerm.spineHead_mkApps])
      | app_box hf _ =>
          obtain ⟨ar, vs, _, _, _, he⟩ := ih init.length hlt rfl hf
          exact absurd (congrArg LBTerm.spineHead he) (by simp [LBTerm.spineHead_mkApps])
      | @construct_app _ _ _ a' iid' c' args₀ ar' hf harity hlt' ha =>
          obtain ⟨ar, vs, har, hle, hvs, he⟩ := ih init.length hlt rfl hf
          obtain ⟨rfl, rfl, rfl⟩ := LBTerm.mkApps_construct_inj he
          rw [har] at harity
          have harr : ar' = ar := Option.some.inj harity.symm
          subst harr
          refine ⟨ar', args₀ ++ [a'], har, ?_, ?_, ?_⟩
          · simp only [List.concat_eq_append, List.length_append, List.length_cons,
              List.length_nil]
            omega
          · simp only [List.concat_eq_append, List.length_append, List.length_cons, hvs]
          · rw [← LBTerm.mkApps_concat]
      | fix_guarded _ hf _ _ _ _ =>
          obtain ⟨ar, vs, _, _, _, he⟩ := ih init.length hlt rfl hf
          exact absurd he.symm LBTerm.mkApps_construct_ne_fix
      | fix_stuck _ hf _ _ _ =>
          obtain ⟨ar, vs, _, _, _, he⟩ := ih init.length hlt rfl hf
          exact absurd he.symm LBTerm.mkApps_construct_ne_fix
      | fix_unguarded _ hf _ _ _ =>
          obtain ⟨ar, vs, _, _, _, he⟩ := ih init.length hlt rfl hf
          exact absurd (congrArg LBTerm.spineHead he) (by simp [LBTerm.spineHead_mkApps])
      | app_cong hf hstuck _ =>
          obtain ⟨ar, vs, _, _, _, he⟩ := ih init.length hlt rfl hf
          rw [he, isStuckApp_construct_spine] at hstuck
          exact absurd hstuck (by simp)



/-! ## The fragment the general simulation holds on

`Lower` has three arms whose source is an eliminator- or constructor-constant spine and
whose target is an η-expansion or a `case` node. Two of them are **refuted** below
(`lower_correct_needs_ctorEta_guard` for `ctorEta`, `lower_correct_needs_elimBody_head`
for `elimEta`), and the second refutation holds at *every* pair of environments, so no
hypothesis on `Γ` repairs the unrestricted statement. `LowerPlain` is `Lower` without
those three arms: the eleven congruence arms, `ctorApp`, and the two fix arms.
-/

/-- The fragment of the pass relation the forward simulation holds on: `Lower` minus
`ctorEta`, `elimApp` and `elimEta`. The two fix arms take `LowerBlock` as one premise —
a statement about `Lower`, not a nested occurrence of `LowerPlain` — so the block
interface is shared with `Lower` verbatim. -/
inductive LowerPlain (Γ : GlobalDeclarations) : LBTerm → LBTerm → Prop where
  | box : LowerPlain Γ .box .box
  | bvar (i : Nat) : LowerPlain Γ (.bvar i) (.bvar i)
  | fvar (x : FVarId) : LowerPlain Γ (.fvar x) (.fvar x)
  | prim (p : PrimVal) : LowerPlain Γ (.prim p) (.prim p)
  | const {kn : Kername} (h : ¬ RuntimeKey Γ kn) : LowerPlain Γ (.const kn) (.const kn)
  | lambda {n n' : BinderName} {b b' : LBTerm} (h : LowerPlain Γ b b') :
      LowerPlain Γ (.lambda n b) (.lambda n' b')
  | letIn {n n' : BinderName} {v v' b b' : LBTerm} (hv : LowerPlain Γ v v')
      (hb : LowerPlain Γ b b') : LowerPlain Γ (.letIn n v b) (.letIn n' v' b')
  | app {f f' a a' : LBTerm} (hf : LowerPlain Γ f f') (ha : LowerPlain Γ a a') :
      LowerPlain Γ (.app f a) (.app f' a')
  | proj {p : ProjectionInfo} {e e' : LBTerm} (h : LowerPlain Γ e e') :
      LowerPlain Γ (.proj p e) (.proj p e')
  | construct {iid : InductiveId} {k : Nat} {args args' : List LBTerm}
      (hlen : args'.length = args.length)
      (h : ∀ i, i < args.length → LowerPlain Γ args[i]! args'[i]!) :
      LowerPlain Γ (.construct iid k args) (.construct iid k args')
  | «case» {ip : InductiveId × Nat} {d d' : LBTerm}
      {alts alts' : List (List BinderName × LBTerm)}
      (hd : LowerPlain Γ d d') (hlen : alts'.length = alts.length)
      (hn : ∀ i, i < alts.length → (alts'[i]!).1.length = (alts[i]!).1.length)
      (hb : ∀ i, i < alts.length → LowerPlain Γ (alts[i]!).2 (alts'[i]!).2) :
      LowerPlain Γ (.case ip d alts) (.case ip d' alts')
  | ctorApp {kn : Kername} {iid : InductiveId} {k : Nat} {args args' : List LBTerm}
      (hc : CtorDecl Γ kn iid k) (hsat : args.length ≥ cstrArity Γ iid k)
      (hlen : args'.length = args.length)
      (ha : ∀ i, i < args.length → LowerPlain Γ args[i]! args'[i]!) :
      LowerPlain Γ (LBTerm.mkApps (.const kn) args) (LBTerm.mkApps (.construct iid k []) args')
  | fixConst {kn : Kername} {kns : List Kername} {bs bs' : List LBTerm} {ids : List FVarId}
      {defs : List (@FixDef LBTerm)} {j : Nat}
      (hblk : LowerBlock Γ kns bs bs' ids defs) (hj : kns[j]? = some kn) :
      LowerPlain Γ (.const kn) (.fix defs j)
  | fixBody {b : LBTerm} {kns : List Kername} {bs bs' : List LBTerm} {ids : List FVarId}
      {defs : List (@FixDef LBTerm)} {j : Nat}
      (hblk : LowerBlock Γ kns bs bs' ids defs) (hj : bs[j]? = some b)
      (hjl : j < defs.length) : LowerPlain Γ b (.fix defs j)

/-- The fragment is a sub-relation of the pass relation. -/
theorem LowerPlain.toLower {Γ : GlobalDeclarations} {s t : LBTerm} (h : LowerPlain Γ s t) :
    Lower Γ s t := by
  induction h with
  | box => exact .box
  | bvar i => exact .bvar i
  | fvar x => exact .fvar x
  | prim p => exact .prim p
  | const hk => exact .const hk
  | lambda _ ih => exact .lambda ih
  | letIn _ _ ihv ihb => exact .letIn ihv ihb
  | app _ _ ihf iha => exact .app ihf iha
  | proj _ ih => exact .proj ih
  | construct hlen _ ih => exact .construct hlen ih
  | «case» _ hlen hn _ ihd ihb => exact .case ihd hlen hn ihb
  | ctorApp hc hsat hlen _ ih => exact .ctorApp hc hsat hlen ih
  | fixConst hblk hj => exact Lower.fixConst' hblk hj
  | fixBody hblk hj hjl => exact Lower.fixBody' hblk hj hjl

/-- Spine congruence for the fragment. -/
theorem LowerPlain.mkApps {Γ : GlobalDeclarations} {f f' : LBTerm} (hf : LowerPlain Γ f f')
    {args args' : List LBTerm} (hlen : args'.length = args.length)
    (h : ∀ i, i < args.length → LowerPlain Γ args[i]! args'[i]!) :
    LowerPlain Γ (LBTerm.mkApps f args) (LBTerm.mkApps f' args') := by
  induction args generalizing f f' args' with
  | nil =>
      have : args' = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst this; exact hf
  | cons x xs ih =>
      obtain ⟨y, ys, rfl⟩ : ∃ y ys, args' = y :: ys := by
        rcases args' with _ | ⟨y, ys⟩
        · simp at hlen
        · exact ⟨y, ys, rfl⟩
      have hlen' : ys.length = xs.length := by simpa using hlen
      have hx : LowerPlain Γ x y := by
        have h0 := h 0 (by simp)
        rwa [getElem!_pos (x :: xs) 0 (by simp), getElem!_pos (y :: ys) 0 (by simp)] at h0
      refine ih (.app hf hx) hlen' ?_
      intro i hi
      have hi' := h (i + 1) (by simp only [List.length_cons]; omega)
      rwa [getElem!_pos (x :: xs) (i + 1) (by simp only [List.length_cons]; omega),
        getElem!_pos (y :: ys) (i + 1) (by simp only [List.length_cons]; omega),
        List.getElem_cons_succ, List.getElem_cons_succ,
        ← getElem!_pos xs i hi, ← getElem!_pos ys i (by omega)] at hi'


/-- The fragment commutes with `shift`, for `Lower.shift_comm`'s reason: no arm reads a de
Bruijn index, and both fix arms rest on closed declarations. -/
theorem LowerPlain.shift_comm {Γ : GlobalDeclarations} (hΓ : ClosedBodies Γ)
    {s t : LBTerm} (h : LowerPlain Γ s t) :
    ∀ d c, LowerPlain Γ (LBTerm.shift d c s) (LBTerm.shift d c t) := by
  induction h with
  | box => exact fun _ _ => .box
  | bvar i => intro d c; simp only [LBTerm.shift]; split <;> exact .bvar _
  | fvar x => exact fun _ _ => .fvar x
  | prim p => exact fun _ _ => .prim p
  | const hk => exact fun _ _ => .const hk
  | lambda _ ih => exact fun d c => .lambda (ih d (c + 1))
  | letIn _ _ ihv ihb => exact fun d c => .letIn (ihv d c) (ihb d (c + 1))
  | app _ _ ihf iha => exact fun d c => .app (ihf d c) (iha d c)
  | proj _ ih => exact fun d c => .proj (ih d c)
  | @construct iid ci args args' hlen _ ih =>
      intro d c
      simp only [LBTerm.shift, LBTerm.shiftArgs_eq_map]
      refine .construct (by simp [hlen]) ?_
      intro i hi
      rw [List.length_map] at hi
      rw [Lower.getElem!_map _ _ i hi, Lower.getElem!_map _ _ i (by omega)]
      exact ih i hi d c
  | @«case» ip dd dd' alts alts' _ hlen hn _ ihd ihb =>
      intro d c
      simp only [LBTerm.shift, LBTerm.shiftAlts_eq_map]
      refine .case (ihd d c) (by simp [hlen]) ?_ ?_
      · intro i hi
        rw [List.length_map] at hi
        rw [Lower.getElem!_map (fun x : List BinderName × LBTerm =>
              (x.1, LBTerm.shift d (c + x.1.length) x.2)) alts' i (by omega),
          Lower.getElem!_map (fun x : List BinderName × LBTerm =>
              (x.1, LBTerm.shift d (c + x.1.length) x.2)) alts i hi]
        exact hn i hi
      · intro i hi
        rw [List.length_map] at hi
        rw [Lower.getElem!_map (fun x : List BinderName × LBTerm =>
              (x.1, LBTerm.shift d (c + x.1.length) x.2)) alts' i (by omega),
          Lower.getElem!_map (fun x : List BinderName × LBTerm =>
              (x.1, LBTerm.shift d (c + x.1.length) x.2)) alts i hi]
        rw [hn i hi]
        exact ihb i hi d (c + (alts[i]!).1.length)
  | @ctorApp kn iid ci args args' hc hsat hlen _ ih =>
      intro d c
      rw [LBTerm.shift_mkApps, LBTerm.shift_mkApps]
      refine .ctorApp hc (by simpa using hsat) (by simp [hlen]) ?_
      intro i hi
      rw [List.length_map] at hi
      rw [Lower.getElem!_map _ _ i hi, Lower.getElem!_map _ _ i (by omega)]
      exact ih i hi d c
  | @fixConst kn kns bs bs' ids defs j hblk hj =>
      intro d c
      rw [show LBTerm.shift d c (LBTerm.const kn) = .const kn from rfl,
        (hblk.lbClosed_fix hΓ j).shift_eq (Nat.zero_le c) d]
      exact .fixConst hblk hj
  | @fixBody b kns bs bs' ids defs j hblk hj hjl =>
      intro d c
      obtain ⟨hjb, hjeq⟩ := Lower.getElem!_of_getElem? hj
      have hbcl : LBClosed b 0 := by
        have h0 := hΓ _ _ (hblk.hdecl j (by rw [← hblk.hb]; exact hjb))
        rwa [hjeq] at h0
      rw [hbcl.shift_eq (Nat.zero_le c) d, (hblk.lbClosed_fix hΓ j).shift_eq (Nat.zero_le c) d]
      exact .fixBody hblk hj hjl

/-- The fragment commutes with substitution, the substituted terms being related
themselves: the law the β, ζ and ι steps of the simulation consume. -/
theorem LowerPlain.subst_comm {Γ : GlobalDeclarations} (hΓ : ClosedBodies Γ)
    {a a' : LBTerm} (ha : LowerPlain Γ a a') {s t : LBTerm} (h : LowerPlain Γ s t) :
    ∀ d, LowerPlain Γ (LBTerm.subst a d s) (LBTerm.subst a' d t) := by
  induction h with
  | box => exact fun _ => .box
  | bvar i =>
      intro d
      simp only [LBTerm.subst]
      split
      · exact .bvar _
      · split
        · exact LowerPlain.shift_comm hΓ ha d 0
        · exact .bvar _
  | fvar x => exact fun _ => .fvar x
  | prim p => exact fun _ => .prim p
  | const hk => exact fun _ => .const hk
  | lambda _ ih => exact fun d => .lambda (ih (d + 1))
  | letIn _ _ ihv ihb => exact fun d => .letIn (ihv d) (ihb (d + 1))
  | app _ _ ihf iha => exact fun d => .app (ihf d) (iha d)
  | proj _ ih => exact fun d => .proj (ih d)
  | @construct iid ci args args' hlen _ ih =>
      intro d
      simp only [LBTerm.subst, LBTerm.substArgs_eq_map]
      refine .construct (by simp [hlen]) ?_
      intro i hi
      rw [List.length_map] at hi
      rw [Lower.getElem!_map _ _ i hi, Lower.getElem!_map _ _ i (by omega)]
      exact ih i hi d
  | @«case» ip dd dd' alts alts' _ hlen hn _ ihd ihb =>
      intro d
      simp only [LBTerm.subst, LBTerm.substAlts_eq_map]
      refine .case (ihd d) (by simp [hlen]) ?_ ?_
      · intro i hi
        rw [List.length_map] at hi
        rw [Lower.getElem!_map (fun x : List BinderName × LBTerm =>
              (x.1, LBTerm.subst a' (d + x.1.length) x.2)) alts' i (by omega),
          Lower.getElem!_map (fun x : List BinderName × LBTerm =>
              (x.1, LBTerm.subst a (d + x.1.length) x.2)) alts i hi]
        exact hn i hi
      · intro i hi
        rw [List.length_map] at hi
        rw [Lower.getElem!_map (fun x : List BinderName × LBTerm =>
              (x.1, LBTerm.subst a' (d + x.1.length) x.2)) alts' i (by omega),
          Lower.getElem!_map (fun x : List BinderName × LBTerm =>
              (x.1, LBTerm.subst a (d + x.1.length) x.2)) alts i hi]
        rw [hn i hi]
        exact ihb i hi (d + (alts[i]!).1.length)
  | @ctorApp kn iid ci args args' hc hsat hlen _ ih =>
      intro d
      rw [LBTerm.subst_mkApps, LBTerm.subst_mkApps]
      refine .ctorApp hc (by simpa using hsat) (by simp [hlen]) ?_
      intro i hi
      rw [List.length_map] at hi
      rw [Lower.getElem!_map _ _ i hi, Lower.getElem!_map _ _ i (by omega)]
      exact ih i hi d
  | @fixConst kn kns bs bs' ids defs j hblk hj =>
      intro d
      rw [show LBTerm.subst a d (LBTerm.const kn) = .const kn from rfl,
        (hblk.lbClosed_fix hΓ j).subst_eq (Nat.zero_le d) a']
      exact .fixConst hblk hj
  | @fixBody b kns bs bs' ids defs j hblk hj hjl =>
      intro d
      obtain ⟨hjb, hjeq⟩ := Lower.getElem!_of_getElem? hj
      have hbcl : LBClosed b 0 := by
        have h0 := hΓ _ _ (hblk.hdecl j (by rw [← hblk.hb]; exact hjb))
        rwa [hjeq] at h0
      rw [hbcl.subst_eq (Nat.zero_le d) a, (hblk.lbClosed_fix hΓ j).subst_eq (Nat.zero_le d) a']
      exact .fixBody hblk hj hjl

/-- The fragment commutes with a whole substitution list. -/
theorem LowerPlain.substList_comm {Γ : GlobalDeclarations} (hΓ : ClosedBodies Γ) :
    ∀ {l l' : List LBTerm}, l'.length = l.length →
      (∀ i, i < l.length → LowerPlain Γ l[i]! l'[i]!) →
      ∀ {s t : LBTerm}, LowerPlain Γ s t →
        LowerPlain Γ (LBTerm.substList l s) (LBTerm.substList l' t)
  | [], l', hlen, _, s, t, h => by
      obtain rfl : l' = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      exact h
  | x :: xs, l', hlen, hall, s, t, h => by
      obtain ⟨y, ys, rfl⟩ : ∃ y ys, l' = y :: ys := by
        rcases l' with _ | ⟨y, ys⟩
        · simp at hlen
        · exact ⟨y, ys, rfl⟩
      have hlen' : ys.length = xs.length := by simpa using hlen
      have hx : LowerPlain Γ x y := by
        have h0 := hall 0 (by simp)
        rwa [getElem!_pos (x :: xs) 0 (by simp), getElem!_pos (y :: ys) 0 (by simp)] at h0
      refine LowerPlain.substList_comm hΓ hlen' (fun i hi => ?_)
        (LowerPlain.subst_comm hΓ hx h 0)
      have hi' := hall (i + 1) (by simp only [List.length_cons]; omega)
      rwa [getElem!_pos (x :: xs) (i + 1) (by simp only [List.length_cons]; omega),
        getElem!_pos (y :: ys) (i + 1) (by simp only [List.length_cons]; omega),
        List.getElem_cons_succ, List.getElem_cons_succ,
        ← getElem!_pos xs i hi, ← getElem!_pos ys i (by omega)] at hi'


/-! ## The fragment's transport along a fix unfolding -/

/-- `Lower.constToFix` inside the fragment: a fix unfolding puts `.fix defs j` where the
lowered body carries the sibling `.const kns[j]`, and the result is still related. The
block premise is `LowerBlock` verbatim — it supplies closedness and freshness only, and the
induction runs on the `LowerPlain` derivation. -/
theorem LowerPlain.constToFix {Γ : GlobalDeclarations} {kns : List Kername}
    {bs bs' : List LBTerm} {ids : List FVarId} {defs : List (@FixDef LBTerm)} {s t t' : LBTerm}
    (hΓ : ClosedBodies Γ) (hblk : LowerBlock Γ kns bs bs' ids defs)
    (hfv : ∀ x ∈ ids, ¬ hasFVar x t) (h : LowerPlain Γ s t)
    (hct : ConstToFVar kns ids t t') :
    LowerPlain Γ s (substFix ids defs t') := by
  have hdcl : ∀ j, LBClosed (LBTerm.fix defs j) 0 := hblk.lbClosed_fix hΓ
  have hself : ∀ u : LBTerm, (∀ x ∈ ids, ¬ hasFVar x u) → substFix ids defs u = u := by
    intro u hu
    refine substFVarList_eq_self_of_not_hasFVar _ u (fun q hq => ?_)
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
    exact hu r.1 (List.fst_mem_of_mem_zipIdx hr)
  have hhit : ∀ (j : Nat) (x : FVarId), ids[j]? = some x →
      substFix ids defs (.fvar x) = .fix defs j := by
    intro j x hx
    obtain ⟨hj, hxe⟩ := Lower.getElem!_of_getElem? hx
    have hix : ids[j]'hj = x := by rw [← getElem!_pos ids j hj]; exact hxe
    rw [← hix]
    exact substFix_fvar_getElem hblk.hids hblk.not_hasFVar_fix j hj
  have main : ∀ (p q : LBTerm), LowerPlain Γ p q → (∀ x ∈ ids, ¬ hasFVar x q) →
      ∀ q', ConstToFVar kns ids q q' → LowerPlain Γ p (substFix ids defs q') := by
    intro p q hpq
    induction hpq with
    | box => intro _ q' hcw; cases hcw; rw [substFix_box]; exact .box
    | bvar i => intro _ q' hcw; cases hcw; rw [substFix_bvar]; exact .bvar i
    | fvar x => intro hnf q' hcw; cases hcw; rw [hself _ hnf]; exact .fvar x
    | prim pr => intro _ q' hcw; cases hcw; rw [substFix_prim]; exact .prim pr
    | @const kn hk =>
        intro _ q' hcw
        cases hcw with
        | @hit j _ x hkn hx => rw [hhit j x hx]; exact .fixConst hblk hkn
        | miss _ => rw [substFix_const]; exact .const hk
    | @lambda n n' b b' _ ih =>
        intro hnf q' hcw
        cases hcw with
        | @lambda _ n₂ _ b₂ h₀ =>
            rw [substFix_lambda]
            exact .lambda (ih (fun x hx => by simpa using hnf x hx) b₂ h₀)
    | @letIn n n' v v' b b' _ _ ihv ihb =>
        intro hnf q' hcw
        cases hcw with
        | @letIn _ n₂ _ v₂ _ b₂ hv₂ hb₂ =>
            rw [substFix_letIn]
            exact .letIn (ihv (fun x hx hc => hnf x hx (.inl hc)) v₂ hv₂)
              (ihb (fun x hx hc => hnf x hx (.inr hc)) b₂ hb₂)
    | @app f f' a a' _ _ ihf iha =>
        intro hnf q' hcw
        cases hcw with
        | @app _ f₂ _ a₂ hf₂ ha₂ =>
            rw [substFix_app]
            exact .app (ihf (fun x hx hc => hnf x hx (.inl hc)) f₂ hf₂)
              (iha (fun x hx hc => hnf x hx (.inr hc)) a₂ ha₂)
    | @proj pinfo e e' _ ih =>
        intro hnf q' hcw
        cases hcw with
        | @proj _ _ e₂ h₀ =>
            rw [substFix_proj]
            exact .proj (ih (fun x hx => by simpa using hnf x hx) e₂ h₀)
    | @construct iid k args args' hlen _ ih =>
        intro hnf q' hcw
        cases hcw with
        | @construct _ _ _ A₂ hlen₂ hpt₂ =>
            rw [substFix_construct]
            refine .construct (by simp [hlen₂, hlen]) (fun i hi => ?_)
            rw [Lower.getElem!_map (substFix ids defs) A₂ i (by omega)]
            refine ih i hi (fun x hx hc => hnf x hx ?_) A₂[i]! (hpt₂ i (by omega))
            rw [hasFVar_construct, hasFVarArgs_iff]
            exact ⟨_, Lower.getElem!_mem (by omega), hc⟩
    | @«case» ip d d' alts alts' _ hlen hn _ ihd ihb =>
        intro hnf q' hcw
        cases hcw with
        | @«case» _ _ D₂ _ A₂ hd₂ hlen₂ hn₂ hb₂ =>
            rw [substFix_case]
            refine .case (ihd (fun x hx hc => hnf x hx (.inl hc)) D₂ hd₂)
              (by simp [hlen₂, hlen]) (fun i hi => ?_) (fun i hi => ?_)
            · rw [Lower.getElem!_map (fun a : List BinderName × LBTerm =>
                (a.1, substFix ids defs a.2)) A₂ i (by omega)]
              exact (hn₂ i (by omega)).trans (hn i hi)
            · rw [Lower.getElem!_map (fun a : List BinderName × LBTerm =>
                (a.1, substFix ids defs a.2)) A₂ i (by omega)]
              refine ihb i hi (fun x hx hc => hnf x hx ?_) (A₂[i]!).2 (hb₂ i (by omega))
              rw [hasFVar_case, hasFVarAlts_iff]
              exact .inr ⟨_, Lower.getElem!_mem (by omega), hc⟩
    | @ctorApp kn iid k args args' hc hsat hlen _ ih =>
        intro hnf q' hcw
        obtain ⟨f₂, L₂, hf₂, hlen₂, hpt₂, rfl⟩ :=
          ConstToFVar.mkApps_inv args' (.construct iid k []) q' hcw
        cases hf₂ with
        | @construct _ _ _ A₀ hA₀ _ =>
            have hA : A₀ = [] := List.eq_nil_of_length_eq_zero (by simpa using hA₀)
            subst hA
            rw [substFix_mkApps, substFix_construct]
            simp only [List.map_nil]
            refine .ctorApp hc hsat (by simp [hlen₂, hlen]) (fun i hi => ?_)
            rw [Lower.getElem!_map (substFix ids defs) L₂ i (by omega)]
            refine ih i hi (fun x hx hcc => hnf x hx ?_) L₂[i]! (hpt₂ i (by omega))
            rw [hasFVar_mkApps]
            exact .inr ⟨_, Lower.getElem!_mem (by omega), hcc⟩
    | @fixConst kn kns₀ bs₀ bs₀' ids₀ defs₀ j hblk₀ hj =>
        intro hnf q' hcw
        cases hcw
        rw [hself _ hnf]
        exact .fixConst hblk₀ hj
    | @fixBody b kns₀ bs₀ bs₀' ids₀ defs₀ j hblk₀ hj hjl =>
        intro hnf q' hcw
        cases hcw
        rw [hself _ hnf]
        exact .fixBody hblk₀ hj hjl
  exact main s t h hfv t' hct


/-! ## The fragment's guards

Three block-level guards beyond `lower_correct_deltaChain`'s, each naming a fact about the
blocks the pass builds rather than a filter on programs.
-/

/-- Every member body of every block the pass builds out of `Γ` is related to its emitted
body **inside the fragment**. `LowerBlock.hlow` states this for `Lower`, which the two fix
arms of the fragment inherit verbatim; the simulation needs the fragment's own relation to
continue the induction after a fix unfolding. -/
def BlockBodiesPlain (Γ : GlobalDeclarations) : Prop :=
  ∀ (kns : List Kername) (bs bs' : List LBTerm) (ids : List FVarId)
    (defs : List (@FixDef LBTerm)), LowerBlock Γ kns bs bs' ids defs →
    ∀ i, i < kns.length → LowerPlain Γ bs[i]! bs'[i]!

/-- Every emitted definition of every block the pass builds out of `Γ` has a λ body —
`LBWfPeregrine.fixLambda`'s content. It is what keeps a fix unfolding from landing on
another block's `.fix` node, which the simulation has no measure to recurse on. -/
def BlockDefsLambda (Γ : GlobalDeclarations) : Prop :=
  ∀ (kns : List Kername) (bs bs' : List LBTerm) (ids : List FVarId)
    (defs : List (@FixDef LBTerm)), LowerBlock Γ kns bs bs' ids defs →
    ∀ j, j < defs.length → isLambda (defs[j]!).body = true

/-- `LowerEnv.defs` inside the fragment: a body the emitted environment declares is a
fragment image of the specification's, or one member of a lowered block. -/
def LowerEnvPlain (Γspec Γ : GlobalDeclarations) : Prop :=
  ∀ (kn : Kername) (b₀ b : LBTerm), DefnDecl Γspec kn b₀ → DefnDecl Γ kn b →
    LowerPlain Γspec b₀ b ∨ ∃ kns bs defs j, LowerFix Γspec kns bs defs ∧
      kns[j]? = some kn ∧ b = .fix defs j

/-- A constructor arity exhibits the inductive block it is read from. -/
theorem inductiveDecl_of_constructorArity {Γ : GlobalDeclarations} {iid : InductiveId}
    {k ar : Nat} (h : constructorArity Γ iid k = some ar) :
    ∃ body, LBTerm.envLookup Γ iid.mutualBlockName = some (.inductiveDecl body) := by
  unfold LeanToLambdaBox.constructorArity at h
  cases hl : LBTerm.envLookup Γ iid.mutualBlockName with
  | none => rw [hl] at h; exact absurd h (by simp)
  | some d =>
      cases d with
      | constantDecl c => rw [hl] at h; exact absurd h (by simp)
      | inductiveDecl body => exact ⟨body, rfl⟩

/-- Propositionality is read off the inductive block, which the emitted environment carries
over unchanged. The block has to be declared: `LowerEnv` says nothing about a key the
specification environment answers with a constant. -/
theorem LowerEnv.isPropositionalInductive {Γspec Γ : GlobalDeclarations}
    (hE : LowerEnv Γspec Γ) {iid : InductiveId} {k ar : Nat}
    (hd : LeanToLambdaBox.constructorArity Γspec iid k = some ar)
    (h : isPropositionalInductive Γspec iid = false) :
    isPropositionalInductive Γ iid = false := by
  obtain ⟨body, hl⟩ := inductiveDecl_of_constructorArity hd
  unfold LeanToLambdaBox.isPropositionalInductive at h ⊢
  rw [hE.inds _ _ hl]; rw [hl] at h; exact h

/-- A constructor-spine **value** exhibits the constructor's arity. -/
theorem constructorArity_of_value {Γ : GlobalDeclarations} {fl : WcbvFlags}
    (hb : fl.with_constructor_as_block = false) {iid : InductiveId} {k : Nat} :
    ∀ (n : Nat) (args : List LBTerm), args.length = n →
      Value Γ fl (LBTerm.mkApps (.construct iid k []) args) →
      ∃ ar, constructorArity Γ iid k = some ar := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro args hn hv
    rcases List.eq_nil_or_concat args with rfl | ⟨init, a, rfl⟩
    · cases hv with
      | atom h => exact absurd h (by simp [atomValue])
      | construct_block hbl => rw [hb] at hbl; exact absurd hbl (by simp)
      | construct_nil _ harity => exact ⟨_, harity⟩
    · rw [List.concat_eq_append, LBTerm.mkApps_concat] at hv
      cases hv with
      | atom h => exact absurd h (by simp [atomValue])
      | @construct_app_val _ hd _ iid' c' ar' args' _ hdeq harity =>
          obtain ⟨rfl, rfl, rfl⟩ := LBTerm.mkApps_construct_inj hdeq.symm
          exact ⟨ar', harity⟩
      | app_stuck _ hstuck _ =>
          rw [isStuckApp_construct_spine] at hstuck; exact absurd hstuck (by simp)
      | @fix_app_val _ hdf _ defs₀ i₀ rarg argsv _ hdeq =>
          exact absurd hdeq LBTerm.mkApps_construct_ne_fix

/-- A constructor-spine value of an evaluation exhibits the constructor's arity. -/
theorem constructorArity_of_eval {Γ : GlobalDeclarations} {fl : WcbvFlags}
    (hb : fl.with_constructor_as_block = false) {iid : InductiveId} {k : Nat}
    {d : LBTerm} {args : List LBTerm}
    (h : WcbvEval Γ fl d (LBTerm.mkApps (.construct iid k []) args)) :
    ∃ ar, constructorArity Γ iid k = some ar :=
  constructorArity_of_value hb args.length args rfl (eval_to_value h)

/-- Substituting does not change a λ head. -/
theorem isLambda_substList : ∀ (l : List LBTerm) {t : LBTerm}, isLambda t = true →
    isLambda (LBTerm.substList l t) = true
  | [], t, h => h
  | s :: l, t, h => by
      obtain ⟨n, b, rfl⟩ := isLambda_eq_true h
      exact isLambda_substList l (by rfl)

/-! ## Source-side inversion inside the fragment

The fragment has one spine-indexed arm, `ctorApp`, and two arms with a `.fix` target, so
each inversion rules out a `mkApps` source and — where the source is neither a constant nor
a λ — a `.fix` target.
-/

/-- A `.fix` in the target comes from one of the two fix arms. -/
theorem LowerPlain.target_fix {Γ : GlobalDeclarations} {s t : LBTerm}
    {defs : List (@FixDef LBTerm)} {j : Nat} (h : LowerPlain Γ s t) (ht : t = .fix defs j) :
    ∃ kns bs bs' ids, LowerBlock Γ kns bs bs' ids defs ∧
      ((∃ kn, s = .const kn ∧ kns[j]? = some kn) ∨ (bs[j]? = some s ∧ j < defs.length)) := by
  cases h with
  | box | bvar | fvar | prim | const | lambda | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion ht
  | @ctorApp kn iid k args args' =>
      obtain ⟨rfl, he⟩ := mkApps_eq_of_ne_app (fun _ _ => LBTerm.noConfusion) ht
      exact LBTerm.noConfusion he
  | @fixConst kn kns bs bs' ids defs₀ j₀ hblk hj =>
      injection ht with hd hj₀
      subst hd; subst hj₀
      exact ⟨kns, bs, bs', ids, hblk, .inl ⟨kn, rfl, hj⟩⟩
  | @fixBody b kns bs bs' ids defs₀ j₀ hblk hj hjl =>
      injection ht with hd hj₀
      subst hd; subst hj₀
      exact ⟨kns, bs, bs', ids, hblk, .inr ⟨hj, hjl⟩⟩

/-- Only a constant or a λ has a `.fix` image. -/
theorem LowerPlain.notFix_of_block {Γ : GlobalDeclarations} (hblk : BlockBodiesLambda Γ)
    {s : LBTerm} {defs : List (@FixDef LBTerm)} {j : Nat} (h : LowerPlain Γ s (.fix defs j)) :
    (∃ kn, s = .const kn) ∨ isLambda s = true := by
  obtain ⟨kns, bs, bs', ids, hblock, hcase⟩ := LowerPlain.target_fix h rfl
  rcases hcase with ⟨kn, rfl, _⟩ | ⟨hj, hjl⟩
  · exact .inl ⟨kn, rfl⟩
  · obtain ⟨hjb, hjeq⟩ := Lower.getElem!_of_getElem? hj
    have := hblk _ _ _ _ _ hblock j (by rw [hblock.hb] at hjb; exact hjb)
    rw [hjeq] at this
    exact .inr this

/-- A source that is neither a constant nor a λ has no `.fix` image. -/
theorem LowerPlain.ne_fix_of_block {Γ : GlobalDeclarations} (hblk : BlockBodiesLambda Γ)
    {s t : LBTerm} (h : LowerPlain Γ s t) (hc : ∀ kn, s ≠ .const kn) (hl : isLambda s = false)
    (defs : List (@FixDef LBTerm)) (j : Nat) : t ≠ .fix defs j := by
  intro ht
  subst ht
  rcases LowerPlain.notFix_of_block hblk h with ⟨kn, hk⟩ | hlam
  · exact hc kn hk
  · rw [hl] at hlam; exact Bool.noConfusion hlam

/-- `□` is lowered to `□`. -/
theorem LowerPlain.source_box {Γ : GlobalDeclarations} (hblk : BlockBodiesLambda Γ)
    {s t : LBTerm} (h : LowerPlain Γ s t) (hs : s = .box) : t = .box := by
  have hnf := LowerPlain.ne_fix_of_block hblk h (by rw [hs]; exact fun _ => LBTerm.noConfusion)
    (by rw [hs]; rfl)
  cases h with
  | box => rfl
  | bvar | fvar | prim | const | lambda | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion hs
  | fixConst | fixBody => exact absurd rfl (hnf _ _)
  | @ctorApp kn iid k args args' =>
      obtain ⟨rfl, he⟩ := mkApps_eq_of_ne_app (fun _ _ => LBTerm.noConfusion) hs
      exact LBTerm.noConfusion he

/-- A de Bruijn index is lowered to itself. -/
theorem LowerPlain.source_bvar {Γ : GlobalDeclarations} (hblk : BlockBodiesLambda Γ)
    {s t : LBTerm} {i : Nat} (h : LowerPlain Γ s t) (hs : s = .bvar i) : t = .bvar i := by
  have hnf := LowerPlain.ne_fix_of_block hblk h (by rw [hs]; exact fun _ => LBTerm.noConfusion)
    (by rw [hs]; rfl)
  cases h with
  | bvar j => exact hs ▸ rfl
  | box | fvar | prim | const | lambda | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion hs
  | fixConst | fixBody => exact absurd rfl (hnf _ _)
  | @ctorApp kn iid k args args' =>
      obtain ⟨rfl, he⟩ := mkApps_eq_of_ne_app (fun _ _ => LBTerm.noConfusion) hs
      exact LBTerm.noConfusion he

/-- A free variable is lowered to itself. -/
theorem LowerPlain.source_fvar {Γ : GlobalDeclarations} (hblk : BlockBodiesLambda Γ)
    {s t : LBTerm} {x : FVarId} (h : LowerPlain Γ s t) (hs : s = .fvar x) : t = .fvar x := by
  have hnf := LowerPlain.ne_fix_of_block hblk h (by rw [hs]; exact fun _ => LBTerm.noConfusion)
    (by rw [hs]; rfl)
  cases h with
  | fvar y => exact hs ▸ rfl
  | box | bvar | prim | const | lambda | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion hs
  | fixConst | fixBody => exact absurd rfl (hnf _ _)
  | @ctorApp kn iid k args args' =>
      obtain ⟨rfl, he⟩ := mkApps_eq_of_ne_app (fun _ _ => LBTerm.noConfusion) hs
      exact LBTerm.noConfusion he

/-- A primitive is lowered to itself. -/
theorem LowerPlain.source_prim {Γ : GlobalDeclarations} (hblk : BlockBodiesLambda Γ)
    {s t : LBTerm} {p : PrimVal} (h : LowerPlain Γ s t) (hs : s = .prim p) : t = .prim p := by
  have hnf := LowerPlain.ne_fix_of_block hblk h (by rw [hs]; exact fun _ => LBTerm.noConfusion)
    (by rw [hs]; rfl)
  cases h with
  | prim q => exact hs ▸ rfl
  | box | bvar | fvar | const | lambda | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion hs
  | fixConst | fixBody => exact absurd rfl (hnf _ _)
  | @ctorApp kn iid k args args' =>
      obtain ⟨rfl, he⟩ := mkApps_eq_of_ne_app (fun _ _ => LBTerm.noConfusion) hs
      exact LBTerm.noConfusion he

/-- A `let` is lowered to a `let`, value and body pointwise. -/
theorem LowerPlain.source_letIn {Γ : GlobalDeclarations} (hblk : BlockBodiesLambda Γ)
    {s t : LBTerm} {n : BinderName} {v b : LBTerm} (h : LowerPlain Γ s t)
    (hs : s = .letIn n v b) :
    ∃ n' v' b', t = .letIn n' v' b' ∧ LowerPlain Γ v v' ∧ LowerPlain Γ b b' := by
  have hnf := LowerPlain.ne_fix_of_block hblk h (by rw [hs]; exact fun _ => LBTerm.noConfusion)
    (by rw [hs]; rfl)
  cases h with
  | @letIn n₀ n' v₀ v' b₀ b' hv hb =>
      injection hs with _ hvv hbb
      subst hvv; subst hbb
      exact ⟨n', v', b', rfl, hv, hb⟩
  | box | bvar | fvar | prim | const | lambda | app | proj | construct | «case» =>
      exact LBTerm.noConfusion hs
  | fixConst | fixBody => exact absurd rfl (hnf _ _)
  | @ctorApp kn iid k args args' =>
      obtain ⟨rfl, he⟩ := mkApps_eq_of_ne_app (fun _ _ => LBTerm.noConfusion) hs
      exact LBTerm.noConfusion he

/-- A projection is lowered to the same projection of the lowered discriminant. -/
theorem LowerPlain.source_proj {Γ : GlobalDeclarations} (hblk : BlockBodiesLambda Γ)
    {s t : LBTerm} {p : ProjectionInfo} {e : LBTerm} (h : LowerPlain Γ s t)
    (hs : s = .proj p e) : ∃ e', t = .proj p e' ∧ LowerPlain Γ e e' := by
  have hnf := LowerPlain.ne_fix_of_block hblk h (by rw [hs]; exact fun _ => LBTerm.noConfusion)
    (by rw [hs]; rfl)
  cases h with
  | @proj p₀ e₀ e' he =>
      injection hs with hp hee
      subst hp; subst hee
      exact ⟨e', rfl, he⟩
  | box | bvar | fvar | prim | const | lambda | letIn | app | construct | «case» =>
      exact LBTerm.noConfusion hs
  | fixConst | fixBody => exact absurd rfl (hnf _ _)
  | @ctorApp kn iid k args args' =>
      obtain ⟨rfl, he⟩ := mkApps_eq_of_ne_app (fun _ _ => LBTerm.noConfusion) hs
      exact LBTerm.noConfusion he

/-- A constructor node is lowered argument by argument. -/
theorem LowerPlain.source_construct {Γ : GlobalDeclarations} (hblk : BlockBodiesLambda Γ)
    {s t : LBTerm} {iid : InductiveId} {k : Nat} {args : List LBTerm} (h : LowerPlain Γ s t)
    (hs : s = .construct iid k args) :
    ∃ args', t = .construct iid k args' ∧ args'.length = args.length ∧
      ∀ i, i < args.length → LowerPlain Γ args[i]! args'[i]! := by
  have hnf := LowerPlain.ne_fix_of_block hblk h (by rw [hs]; exact fun _ => LBTerm.noConfusion)
    (by rw [hs]; rfl)
  cases h with
  | @construct iid₀ k₀ args₀ args' hlen ha =>
      injection hs with hi hk hargs
      subst hi; subst hk; subst hargs
      exact ⟨args', rfl, hlen, ha⟩
  | box | bvar | fvar | prim | const | lambda | letIn | app | proj | «case» =>
      exact LBTerm.noConfusion hs
  | fixConst | fixBody => exact absurd rfl (hnf _ _)
  | @ctorApp kn iid k args args' =>
      obtain ⟨rfl, he⟩ := mkApps_eq_of_ne_app (fun _ _ => LBTerm.noConfusion) hs
      exact LBTerm.noConfusion he

/-- A `case` is lowered to a `case` with the same inductive, parameter count and branch
arities. -/
theorem LowerPlain.source_case {Γ : GlobalDeclarations} (hblk : BlockBodiesLambda Γ)
    {s t : LBTerm} {ip : InductiveId × Nat} {d : LBTerm}
    {alts : List (List BinderName × LBTerm)} (h : LowerPlain Γ s t) (hs : s = .case ip d alts) :
    ∃ d' alts', t = .case ip d' alts' ∧ LowerPlain Γ d d' ∧ alts'.length = alts.length ∧
      (∀ i, i < alts.length → (alts'[i]!).1.length = (alts[i]!).1.length) ∧
      ∀ i, i < alts.length → LowerPlain Γ (alts[i]!).2 (alts'[i]!).2 := by
  have hnf := LowerPlain.ne_fix_of_block hblk h (by rw [hs]; exact fun _ => LBTerm.noConfusion)
    (by rw [hs]; rfl)
  cases h with
  | @«case» ip₀ d₀ d' alts₀ alts' hd hlen hn hb =>
      injection hs with hi hdd hal
      subst hi; subst hdd; subst hal
      exact ⟨d', alts', rfl, hd, hlen, hn, hb⟩
  | box | bvar | fvar | prim | const | lambda | letIn | app | proj | construct =>
      exact LBTerm.noConfusion hs
  | fixConst | fixBody => exact absurd rfl (hnf _ _)
  | @ctorApp kn iid k args args' =>
      obtain ⟨rfl, he⟩ := mkApps_eq_of_ne_app (fun _ _ => LBTerm.noConfusion) hs
      exact LBTerm.noConfusion he

/-- A λ is lowered to a λ, body pointwise, or to a block's `.fix` node. -/
theorem LowerPlain.source_lambda {Γ : GlobalDeclarations} {s t : LBTerm} {n : BinderName}
    {b : LBTerm} (h : LowerPlain Γ s t) (hs : s = .lambda n b) :
    (∃ n' b', t = .lambda n' b' ∧ LowerPlain Γ b b')
    ∨ (∃ kns bs bs' ids defs j, LowerBlock Γ kns bs bs' ids defs ∧ bs[j]? = some s ∧
        j < defs.length ∧ t = .fix defs j) := by
  cases h with
  | box | bvar | fvar | prim | const | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion hs
  | @lambda n₀ n' b₀ b' hb =>
      injection hs with _ hbb
      subst hbb
      exact .inl ⟨n', b', rfl, hb⟩
  | @ctorApp kn iid k args args' =>
      obtain ⟨rfl, he⟩ := mkApps_eq_of_ne_app (fun _ _ => LBTerm.noConfusion) hs
      exact LBTerm.noConfusion he
  | @fixConst kn kns bs bs' ids defs j => exact LBTerm.noConfusion hs
  | @fixBody b₀ kns bs bs' ids defs j hblock hj hjl =>
      exact .inr ⟨kns, bs, bs', ids, defs, j, hblock, hj, hjl, rfl⟩

/-- A λ-headed target comes from a λ-headed source: the fragment has no η arm. -/
theorem LowerPlain.source_isLambda {Γ : GlobalDeclarations} {s t : LBTerm}
    (h : LowerPlain Γ s t) (ht : isLambda t = true) : isLambda s = true := by
  cases h with
  | box | bvar | fvar | prim | const | letIn | app | proj | construct | «case»
  | fixConst | fixBody => exact absurd ht (by simp [isLambda])
  | lambda => rfl
  | @ctorApp kn iid k args args' =>
      rcases mkApps_head_or_app (LBTerm.construct iid k []) args' with he | ⟨g, a, he⟩ <;>
        rw [he] at ht <;> exact absurd ht (by simp [isLambda])

/-- `BlockBodiesLambda` is derivable from the two block guards the fragment already
carries, so it is not an independent assumption inside the fragment. -/
theorem BlockBodiesLambda.of_plain {Γ : GlobalDeclarations} (hblkP : BlockBodiesPlain Γ)
    (hfl : BlockDefsLambda Γ) : BlockBodiesLambda Γ := by
  intro kns bs bs' ids defs hblock j hj
  exact (hblkP _ _ _ _ _ hblock j hj).source_isLambda
    (hblock.targetLambda_of_fixLambda (hfl _ _ _ _ _ hblock) j hj)


/-- An application is lowered by the congruence arm, or its source is a constructor
constant applied to a non-empty spine — which `LowerNoEta.ctorSpine_stuck` shows has no
value. -/
theorem LowerPlain.source_app {Γ : GlobalDeclarations} (hblk : BlockBodiesLambda Γ)
    {s t f a : LBTerm} (h : LowerPlain Γ s t) (hs : s = .app f a) :
    (∃ f' a', t = .app f' a' ∧ LowerPlain Γ f f' ∧ LowerPlain Γ a a')
    ∨ (∃ kn iid k args, CtorDecl Γ kn iid k ∧ s = LBTerm.mkApps (.const kn) args
        ∧ args ≠ []) := by
  have hnf := LowerPlain.ne_fix_of_block hblk h (by rw [hs]; exact fun _ => LBTerm.noConfusion)
    (by rw [hs]; rfl)
  cases h with
  | @app f₀ f' a₀ a' hf ha =>
      injection hs with hff haa
      subst hff; subst haa
      exact .inl ⟨f', a', rfl, hf, ha⟩
  | box | bvar | fvar | prim | const | lambda | letIn | proj | construct | «case» =>
      exact LBTerm.noConfusion hs
  | fixConst | fixBody => exact absurd rfl (hnf _ _)
  | @ctorApp kn iid k args args' hc hsat hlen ha =>
      refine .inr ⟨kn, iid, k, args, hc, rfl, ?_⟩
      rintro rfl
      exact LBTerm.noConfusion hs

/-- An applied constructor constant over-applies its own arity once the η guard has pinned
that arity to `0`, so it has no value: the `ctorApp` arm at a non-empty spine is vacuous. -/
theorem LowerNoEta.ctorSpine_stuck {Γ : GlobalDeclarations} (hne : LowerNoEta Γ)
    {kn : Kername} {iid : InductiveId} {k : Nat} (hc : CtorDecl Γ kn iid k)
    {args : List LBTerm} (hargs : args ≠ []) {v : LBTerm}
    (hev : WcbvEval Γ eraseFlags (LBTerm.mkApps (.const kn) args) v) : False := by
  obtain ⟨ar, vs, har, hle, -, -⟩ := ctorConst_spine_eval rfl hc args.length rfl hev
  have har0 : ar = 0 :=
    (cstrArity_eq_of_constructorArity har).symm.trans (hne.cstrArity_eq_zero hc)
  rw [har0] at hle
  exact hargs (List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hle))

/-! ## Spines -/

/-- `getElem!` at the last position of a one-element extension. -/
theorem getElem!_append_singleton {α : Type} [Inhabited α] (l : List α) (x : α) :
    (l ++ [x])[l.length]! = x := by
  rw [getElem!_pos (l ++ [x]) l.length (by simp)]
  simp

/-- Extending a pointwise-related pair of lists by one related pair. -/
theorem LowerPlain.concat {Γ : GlobalDeclarations} {l l' : List LBTerm} {x y : LBTerm}
    (hlen : l'.length = l.length) (h : ∀ i, i < l.length → LowerPlain Γ l[i]! l'[i]!)
    (hxy : LowerPlain Γ x y) :
    ∀ i, i < (l ++ [x]).length → LowerPlain Γ (l ++ [x])[i]! (l' ++ [y])[i]! := by
  intro i hi
  simp only [List.length_append, List.length_cons, List.length_nil] at hi
  have hleft : ∀ (m : List LBTerm) (z : LBTerm) (j : Nat), j < m.length →
      (m ++ [z])[j]! = m[j]! := by
    intro m z j hj
    rw [getElem!_pos (m ++ [z]) j (by simp; omega), getElem!_pos m j hj,
      List.getElem_append_left hj]
  rcases Nat.lt_or_ge i l.length with hlt | hge
  · rw [hleft l x i hlt, hleft l' y i (by omega)]
    exact h i hlt
  · have : i = l.length := by omega
    subst this
    rw [getElem!_append_singleton l x, ← hlen, getElem!_append_singleton l' y]
    exact hxy

/-- A constructor spine is lowered argument by argument. -/
theorem LowerPlain.source_ctorSpine {Γ : GlobalDeclarations} (hblk : BlockBodiesLambda Γ) :
    ∀ (n : Nat) (args : List LBTerm), args.length = n →
      ∀ {iid : InductiveId} {k : Nat} {t : LBTerm},
        LowerPlain Γ (LBTerm.mkApps (.construct iid k []) args) t →
        ∃ args', t = LBTerm.mkApps (.construct iid k []) args' ∧ args'.length = args.length ∧
          ∀ i, i < args.length → LowerPlain Γ args[i]! args'[i]! := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro args hn iid k t h
    rcases List.eq_nil_or_concat args with rfl | ⟨init, a, hcat⟩
    · obtain ⟨args', ht, hlen, -⟩ := LowerPlain.source_construct hblk h rfl
      obtain rfl : args' = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      exact ⟨[], ht, rfl, by simp⟩
    · rw [List.concat_eq_append] at hcat
      subst hcat
      rw [LBTerm.mkApps_concat] at h
      have hlt : init.length < n := by
        rw [← hn]; simp only [List.length_append, List.length_cons]; omega
      rcases LowerPlain.source_app hblk h rfl with
        ⟨f', a', rfl, hf, ha⟩ | ⟨kn, iid₀, k₀, args₀, -, hspine, -⟩
      · obtain ⟨init', hf', hlen', hpt⟩ := ih init.length hlt init rfl hf
        subst hf'
        exact ⟨init' ++ [a'], (LBTerm.mkApps_concat _ _ _).symm, by simp [hlen'],
          LowerPlain.concat hlen' hpt ha⟩
      · have hsh := congrArg LBTerm.spineHead hspine
        rw [← LBTerm.mkApps_concat] at hsh
        simp only [LBTerm.spineHead_mkApps] at hsh
        exact LBTerm.noConfusion hsh

/-- A free-variable spine is lowered to a free-variable spine. -/
theorem LowerPlain.source_fvarSpine {Γ : GlobalDeclarations} (hblk : BlockBodiesLambda Γ) :
    ∀ (n : Nat) (args : List LBTerm), args.length = n → ∀ {x : FVarId} {t : LBTerm},
      LowerPlain Γ (LBTerm.mkApps (.fvar x) args) t →
      ∃ args', t = LBTerm.mkApps (.fvar x) args' := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro args hn x t h
    rcases List.eq_nil_or_concat args with rfl | ⟨init, a, hcat⟩
    · exact ⟨[], LowerPlain.source_fvar hblk h rfl⟩
    · rw [List.concat_eq_append] at hcat
      subst hcat
      rw [LBTerm.mkApps_concat] at h
      have hlt : init.length < n := by
        rw [← hn]; simp only [List.length_append, List.length_cons]; omega
      rcases LowerPlain.source_app hblk h rfl with
        ⟨f', a', rfl, hf, -⟩ | ⟨kn, iid₀, k₀, args₀, -, hspine, -⟩
      · obtain ⟨init', rfl⟩ := ih init.length hlt init rfl hf
        exact ⟨init' ++ [a'], (LBTerm.mkApps_concat _ _ _).symm⟩
      · have hsh := congrArg LBTerm.spineHead hspine
        rw [← LBTerm.mkApps_concat] at hsh
        simp only [LBTerm.spineHead_mkApps] at hsh
        exact LBTerm.noConfusion hsh

/-- A `.fix` node has no image: the fragment has no `fix` congruence arm, and the only
source of a `.fix` target is a block member, which the block guard pins to a λ. -/
theorem LowerPlain.source_fix_absurd {Γ : GlobalDeclarations} (hblk : BlockBodiesLambda Γ)
    {s t : LBTerm} {defs : List (@FixDef LBTerm)} {i : Nat} (h : LowerPlain Γ s t)
    (hs : s = .fix defs i) : False := by
  cases h with
  | box | bvar | fvar | prim | const | lambda | letIn | app | proj | construct | «case»
  | fixConst => exact LBTerm.noConfusion hs
  | @ctorApp kn iid k args args' =>
      obtain ⟨rfl, he⟩ := mkApps_eq_of_ne_app (fun _ _ => LBTerm.noConfusion) hs
      exact LBTerm.noConfusion he
  | @fixBody b kns bs bs' ids defs₀ j hblock hj hjl =>
      obtain ⟨hjb, hjeq⟩ := Lower.getElem!_of_getElem? hj
      have hl := hblk _ _ _ _ _ hblock j (by rw [hblock.hb] at hjb; exact hjb)
      rw [hjeq, hs] at hl
      exact Bool.noConfusion hl

/-- A `fix` spine has no image at all: the fragment has no `fix` congruence arm, and the
only source of a `.fix` target is a block member, which the block guard pins to a λ. -/
theorem LowerPlain.fixSpine_absurd {Γ : GlobalDeclarations} (hblk : BlockBodiesLambda Γ) :
    ∀ (n : Nat) (args : List LBTerm), args.length = n →
      ∀ {defs : List (@FixDef LBTerm)} {i : Nat} {t : LBTerm},
        LowerPlain Γ (LBTerm.mkApps (.fix defs i) args) t → False := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro args hn defs i t h
    rcases List.eq_nil_or_concat args with rfl | ⟨init, a, hcat⟩
    · rw [LBTerm.mkApps_nil] at h
      exact LowerPlain.source_fix_absurd hblk h rfl
    · rw [List.concat_eq_append] at hcat
      subst hcat
      rw [LBTerm.mkApps_concat] at h
      have hlt : init.length < n := by
        rw [← hn]; simp only [List.length_append, List.length_cons]; omega
      rcases LowerPlain.source_app hblk h rfl with
        ⟨f', a', rfl, hf, -⟩ | ⟨kn, iid₀, k₀, args₀, -, hspine, -⟩
      · exact ih init.length hlt init rfl hf
      · have hsh := congrArg LBTerm.spineHead hspine
        rw [← LBTerm.mkApps_concat] at hsh
        simp only [LBTerm.spineHead_mkApps] at hsh
        exact LBTerm.noConfusion hsh


/-- What a constant is lowered to: itself, a nullary constructor node, or a block's `.fix`
node. The η disjuncts of `Lower.source_const` are absent — the fragment has no η arm. -/
theorem LowerPlain.source_const {Γ : GlobalDeclarations} (hblk : BlockBodiesLambda Γ)
    {s t : LBTerm} {kn : Kername} (h : LowerPlain Γ s t) (hs : s = .const kn) :
    (t = .const kn ∧ ¬ RuntimeKey Γ kn)
    ∨ (∃ iid k, CtorDecl Γ kn iid k ∧ cstrArity Γ iid k = 0 ∧ t = .construct iid k [])
    ∨ (∃ kns bs bs' ids defs j, LowerBlock Γ kns bs bs' ids defs ∧ kns[j]? = some kn ∧
        t = .fix defs j) := by
  cases h with
  | @const kn' hk =>
      have he : kn' = kn := by injection hs
      exact .inl ⟨by rw [he], by rw [← he]; exact hk⟩
  | box | bvar | fvar | prim | lambda | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion hs
  | @ctorApp kn' iid k args args' hc hsat hlen ha =>
      obtain ⟨rfl, he⟩ := mkApps_eq_const hs
      have hk : kn' = kn := by injection he
      subst hk
      have : args' = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst this
      exact .inr (.inl ⟨iid, k, hc, Nat.le_zero.mp (by simpa using hsat), rfl⟩)
  | @fixConst kn' kns bs bs' ids defs j hblock hj =>
      have he : kn' = kn := by injection hs
      subst he
      exact .inr (.inr ⟨kns, bs, bs', ids, defs, j, hblock, hj, rfl⟩)
  | @fixBody b kns bs bs' ids defs j hblock hj hjl =>
      obtain ⟨hjb, hjeq⟩ := Lower.getElem!_of_getElem? hj
      have hl := hblk _ _ _ _ _ hblock j (by rw [hblock.hb] at hjb; exact hjb)
      rw [hjeq, hs] at hl
      exact Bool.noConfusion hl

/-! ## Stuck heads -/

/-- A stuck value is a free-variable spine: every other value shape is a λ, a `□`, a
primitive, or a constructor- or `fix`-headed spine, all of which `isStuckApp` excludes. -/
theorem stuck_value_fvar_spine {Γ : GlobalDeclarations} {fl : WcbvFlags}
    (hg : fl.with_guarded_fix = true) {v : LBTerm} (hval : Value Γ fl v) :
    isStuckApp fl v = true →
      ∃ (x : FVarId) (args : List LBTerm), v = LBTerm.mkApps (.fvar x) args := by
  induction hval with
  | @atom u hu =>
      intro hst
      cases u with
      | fvar x => exact ⟨x, [], rfl⟩
      | box | lambda | prim | fix => exact absurd hst (by simp [isStuckApp, isLambda, isBox,
          isFixApp, isFix, isConstructApp, isPrimApp, isPrim, LBTerm.spineHead, hg])
      | bvar | const | letIn | app | construct | «case» | proj =>
          exact absurd hu (by simp [atomValue])
  | construct_block hbl _ =>
      intro hst
      exact absurd hst (by simp [isStuckApp, isConstructApp, isConstruct, LBTerm.spineHead])
  | construct_nil _ _ =>
      intro hst
      exact absurd hst (by simp [isStuckApp, isConstructApp, isConstruct, LBTerm.spineHead])
  | @construct_app_val _ hd a iid c ar args _ hdeq =>
      intro hst
      subst hdeq
      exact absurd hst (by simp [isStuckApp, isConstructApp, isConstruct, LBTerm.spineHead,
        LBTerm.spineHead_mkApps])
  | @app_stuck f a _ hstuck _ ihf =>
      intro _
      obtain ⟨x, args, rfl⟩ := ihf hstuck
      exact ⟨x, args ++ [a], (LBTerm.mkApps_concat _ _ _).symm⟩
  | @fix_app_val _ hd a defs i rarg argsv _ hdeq =>
      intro hst
      subst hdeq
      exact absurd hst (by simp [isStuckApp, isFixApp, isFix, LBTerm.spineHead,
        LBTerm.spineHead_mkApps, hg])

/-- A free-variable spine is stuck. -/
theorem isStuckApp_fvar_spine (fl : WcbvFlags) (x : FVarId) (args : List LBTerm) :
    isStuckApp fl (LBTerm.mkApps (.fvar x) args) = true := by
  have hsh : LBTerm.spineHead (LBTerm.mkApps (.fvar x) args) = .fvar x := by
    rw [LBTerm.spineHead_mkApps]; rfl
  rcases mkApps_head_or_app (LBTerm.fvar x) args with he | ⟨g, b, he⟩ <;>
    rw [he] <;> rw [he] at hsh <;>
    simp [isStuckApp, isLambda, isBox, isFixApp, isConstructApp, isPrimApp, isFix,
      isConstruct, isPrim, hsh]

/-- The fragment preserves stuckness: it maps a free-variable spine to a free-variable
spine, and those are exactly the stuck values. -/
theorem LowerPlain.isStuckApp_image {Γ : GlobalDeclarations} (hblk : BlockBodiesLambda Γ)
    {f v : LBTerm} (hval : Value Γ eraseFlags f) (hst : isStuckApp eraseFlags f = true)
    (h : LowerPlain Γ f v) : isStuckApp eraseFlags v = true := by
  obtain ⟨x, args, rfl⟩ := stuck_value_fvar_spine rfl hval hst
  obtain ⟨args', rfl⟩ := LowerPlain.source_fvarSpine hblk args.length args rfl h
  exact isStuckApp_fvar_spine _ _ _

/-! ## The block's unfolding -/

/-- **A block member's unfolded definition is a λ, still related to the member's
specification body.** This is what the target does where the source β-reduces: the emitted
`.fix` fires (`hrarg` pins the principal argument to `0`), and `LowerPlain.constToFix`
carries the relation across the substitution. `hfl` keeps the unfolding from landing on
another `.fix`, which the simulation has no measure to follow. -/
theorem LowerPlain.fixUnfold {Γ : GlobalDeclarations} (hΓ : ClosedBodies Γ)
    (hblkP : BlockBodiesPlain Γ) (hfl : BlockDefsLambda Γ) {kns : List Kername}
    {bs bs' : List LBTerm} {ids : List FVarId} {defs : List (@FixDef LBTerm)} {j : Nat}
    (hblock : LowerBlock Γ kns bs bs' ids defs) (hjl : j < defs.length) :
    ∃ n b, LBTerm.substList (LBTerm.fixSubst defs) (defs[j]!).body = .lambda n b ∧
      LowerPlain Γ bs[j]! (.lambda n b) := by
  have hjk : j < kns.length := by rw [← hblock.hd]; exact hjl
  obtain ⟨u, hct, heq⟩ := hblock.hcl j hjk
  have hbs' : LBClosed bs'[j]! 0 :=
    Lower.closed hΓ (hblock.hlow j hjk) 0 (hΓ _ _ (hblock.hdecl j hjk))
  have hu : LBClosed u 0 := hct.closed hbs'
  have hsub : LBTerm.substList (LBTerm.fixSubst defs) (defs[j]!).body = substFix ids defs u := by
    rw [heq]; exact hblock.substList_fixSubst hΓ hu
  have hlam : isLambda (LBTerm.substList (LBTerm.fixSubst defs) (defs[j]!).body) = true :=
    isLambda_substList _ (hfl _ _ _ _ _ hblock j hjl)
  obtain ⟨n, b, hnb⟩ := isLambda_eq_true hlam
  refine ⟨n, b, hnb, ?_⟩
  have hlow : LowerPlain Γ bs[j]! (substFix ids defs u) :=
    LowerPlain.constToFix hΓ hblock (fun x hx => hblock.hfresh x hx j hjk)
      (hblkP _ _ _ _ _ hblock j hjk) hct
  rw [← hsub, hnb] at hlow
  exact hlow

/-! ## Index bookkeeping for the ι and projection arms -/

/-- `getElem!` through `List.drop`. -/
theorem getElem!_drop {α : Type} [Inhabited α] (l : List α) (m i : Nat)
    (h : i < (l.drop m).length) : (l.drop m)[i]! = l[m + i]! := by
  have h' : m + i < l.length := by simp only [List.length_drop] at h; omega
  rw [getElem!_pos (l.drop m) i h, getElem!_pos l (m + i) h', List.getElem_drop]

/-- `getElem!` through `List.reverse`. -/
theorem getElem!_reverse {α : Type} [Inhabited α] (l : List α) (i : Nat)
    (h : i < l.length) : l.reverse[i]! = l[l.length - 1 - i]! := by
  have h' : i < l.reverse.length := by simpa using h
  rw [getElem!_pos l.reverse i h', getElem!_pos l (l.length - 1 - i) (by omega),
    List.getElem_reverse h']

/-- A pointwise-related pair of lists stays pointwise related under `drop` and `reverse` —
the two list operations the ι rule applies to a constructor's fields. -/
theorem LowerPlain.drop_reverse {Γ : GlobalDeclarations} {l l' : List LBTerm} (m : Nat)
    (hlen : l'.length = l.length) (h : ∀ i, i < l.length → LowerPlain Γ l[i]! l'[i]!) :
    ((l'.drop m).reverse).length = ((l.drop m).reverse).length ∧
      ∀ i, i < ((l.drop m).reverse).length →
        LowerPlain Γ ((l.drop m).reverse)[i]! ((l'.drop m).reverse)[i]! := by
  refine ⟨by simp [hlen], fun i hi => ?_⟩
  simp only [List.length_reverse, List.length_drop] at hi
  have hd : i < (l.drop m).length := by simp only [List.length_drop]; omega
  have hd' : i < (l'.drop m).length := by simp only [List.length_drop, hlen]; omega
  rw [getElem!_reverse _ i hd, getElem!_reverse _ i hd',
    getElem!_drop l m _ (by simp only [List.length_drop]; omega),
    getElem!_drop l' m _ (by simp only [List.length_drop, hlen]; omega)]
  have heq : (l'.drop m).length = (l.drop m).length := by simp [hlen]
  rw [heq]
  exact h _ (by simp only [List.length_drop] at *; omega)


/-! ## The simulation -/

/-- **The forward simulation of the pass, on the fragment `LowerPlain`.** Every rule of
`WcbvEval` that fires at `eraseFlags` is covered. `hne` pins every constructor constant's
arity to `0`, which makes an over-applied constructor spine stuck on both sides; `hblk`,
`hblkP` and `hfl` are the three block facts a fix unfolding needs — a member's
specification body is a λ, it is related to its emitted body inside the fragment, and the
emitted definition is a λ; `hEp` is `LowerEnv.defs` read in the fragment. The three arms
`LowerPlain` omits are discussed at the module header. -/
theorem lower_correct_plain {Γspec Γ : GlobalDeclarations} (hwf : LBWfSpec Γspec)
    (hE : LowerEnv Γspec Γ) (hEp : LowerEnvPlain Γspec Γ) (hsurv : DefsSurvive Γspec Γ)
    (hne : LowerNoEta Γspec) (hblk : BlockBodiesLambda Γspec)
    (hblkP : BlockBodiesPlain Γspec) (hfl : BlockDefsLambda Γspec)
    {t v : LBTerm} (hev : WcbvEval Γspec eraseFlags t v) :
    ∀ {t' : LBTerm}, LowerPlain Γspec t t' →
      ∃ v', LowerPlain Γspec v v' ∧ WcbvEval Γ eraseFlags t' v' := by
  have hΓ : ClosedBodies Γspec := hwf.2
  induction hev with
  | box =>
      intro t' h
      rw [LowerPlain.source_box hblk h rfl]
      exact ⟨.box, .box, .box⟩
  | lam n b =>
      intro t' h
      rcases LowerPlain.source_lambda h rfl with ⟨n', b', rfl, -⟩ | ⟨_, _, _, _, _, _, -, -, -, rfl⟩
      · exact ⟨_, h, .lam n' b'⟩
      · exact ⟨_, h, .fix_atom _ _⟩
  | fvar x =>
      intro t' h
      rw [LowerPlain.source_fvar hblk h rfl]
      exact ⟨_, .fvar x, .fvar x⟩
  | prim p =>
      intro t' h
      rw [LowerPlain.source_prim hblk h rfl]
      exact ⟨_, .prim p, .prim p⟩
  | fix_atom defs i =>
      intro t' h
      exact (LowerPlain.source_fix_absurd hblk h rfl).elim
  | @beta f a n b av r hf ha hb ihf iha ihb =>
      intro t' h
      rcases LowerPlain.source_app hblk h rfl with
        ⟨f', a', rfl, hlf, hla⟩ | ⟨kn, iid, k, args, hc, hsp, hargs⟩
      · obtain ⟨vf, hvf, hevf⟩ := ihf hlf
        obtain ⟨va, hva, heva⟩ := iha hla
        rcases LowerPlain.source_lambda hvf rfl with
          ⟨n₂, b₂, rfl, hb₂⟩ | ⟨kns, bs, bs', ids, defs, j, hblock, hj, hjl, rfl⟩
        · obtain ⟨vr, hvr, hevr⟩ := ihb (LowerPlain.subst_comm hΓ hva hb₂ 0)
          exact ⟨vr, hvr, .beta hevf heva hevr⟩
        · obtain ⟨n₃, b₃, hUeq, hU⟩ := LowerPlain.fixUnfold hΓ hblkP hfl hblock hjl
          obtain ⟨hjb, hjeq⟩ := Lower.getElem!_of_getElem? hj
          rw [hjeq] at hU
          rcases LowerPlain.source_lambda hU rfl with
            ⟨n₄, b₄, hlam, hb₄⟩ | ⟨_, _, _, _, _, _, -, -, -, hfx⟩
          · injection hlam with _ hbb
            subst hbb
            obtain ⟨vr, hvr, hevr⟩ := ihb (LowerPlain.subst_comm hΓ hva hb₄ 0)
            refine ⟨vr, hvr, .fix_guarded (argsv := []) rfl hevf heva
              (getElem?_getElem! hjl) (hblock.hrarg _ (Lower.getElem!_mem hjl)) ?_⟩
            rw [LBTerm.mkApps_nil, hUeq]
            exact .beta (.lam n₃ b₃) (eval_self heva) hevr
          · exact LBTerm.noConfusion hfx
      · exact (hne.ctorSpine_stuck hc hargs (hsp ▸ WcbvEval.beta hf ha hb)).elim
  | @app_box f a av hf ha ihf iha =>
      intro t' h
      rcases LowerPlain.source_app hblk h rfl with
        ⟨f', a', rfl, hlf, hla⟩ | ⟨kn, iid, k, args, hc, hsp, hargs⟩
      · obtain ⟨vf, hvf, hevf⟩ := ihf hlf
        obtain ⟨va, hva, heva⟩ := iha hla
        rw [LowerPlain.source_box hblk hvf rfl] at hevf
        exact ⟨.box, .box, .app_box hevf heva⟩
      · exact (hne.ctorSpine_stuck hc hargs (hsp ▸ WcbvEval.app_box hf ha)).elim
  | @zeta n v₀ b vv r hv hb ihv ihb =>
      intro t' h
      obtain ⟨n', v', b', rfl, hlv, hlb⟩ := LowerPlain.source_letIn hblk h rfl
      obtain ⟨vv', hvv, hevv⟩ := ihv hlv
      obtain ⟨vr, hvr, hevr⟩ := ihb (LowerPlain.subst_comm hΓ hvv hlb 0)
      exact ⟨vr, hvr, .zeta hevv hevr⟩
  | @delta kn body r hlk hbody ih =>
      intro t' h
      rcases LowerPlain.source_const hblk h rfl with
        ⟨rfl, hnr⟩ | ⟨iid, k, hc, hsat, rfl⟩ | ⟨kns, bs, bs', ids, defs, j, hblock, hj, rfl⟩
      · obtain ⟨b, hb'⟩ := hsurv kn body hlk hnr
        rcases hEp kn body b hlk hb' with hlow | ⟨kns, bs, defs, j, hfix, hj, rfl⟩
        · obtain ⟨v', hv', hev'⟩ := ih hlow
          exact ⟨v', hv', .delta hb' hev'⟩
        · obtain ⟨bs', ids, hblock⟩ := hfix
          obtain ⟨hjl, hkj⟩ := Lower.getElem!_of_getElem? hj
          have hdecl := hblock.hdecl j hjl
          rw [hkj] at hdecl
          have hbeq : body = bs[j]! := DefnDecl.inj hlk hdecl
          obtain ⟨n₀, c₀, hlam⟩ := isLambda_eq_true (hblk _ _ _ _ _ hblock j hjl)
          have hjbs : j < bs.length := by rw [hblock.hb]; exact hjl
          have hv : r = bs[j]! := by
            have hd' : WcbvEval Γspec eraseFlags bs[j]! r := hbeq ▸ hbody
            rw [hlam] at hd' ⊢
            cases hd' with | lam => rfl
          rw [hv]
          exact ⟨_, LowerPlain.fixBody hblock (getElem?_getElem! hjbs)
            (by rw [hblock.hd]; exact hjl), .delta hb' (.fix_atom _ _)⟩
      · have hbeq : body = .construct iid k [] := DefnDecl.inj hlk hc
        subst hbeq
        cases hbody with
        | construct hbl => exact absurd hbl (by decide)
        | construct_atom _ har =>
            exact ⟨_, .construct rfl (fun i hi => absurd hi (by simp)),
              .construct_atom rfl (hE.constructorArity har)⟩
      · obtain ⟨hjl, hkj⟩ := Lower.getElem!_of_getElem? hj
        have hdecl := hblock.hdecl j hjl
        rw [hkj] at hdecl
        have hbeq : body = bs[j]! := DefnDecl.inj hlk hdecl
        obtain ⟨n₀, c₀, hlam⟩ := isLambda_eq_true (hblk _ _ _ _ _ hblock j hjl)
        have hjbs : j < bs.length := by rw [hblock.hb]; exact hjl
        have hv : r = bs[j]! := by
          have hd' : WcbvEval Γspec eraseFlags bs[j]! r := hbeq ▸ hbody
          rw [hlam] at hd' ⊢
          cases hd' with | lam => rfl
        rw [hv]
        exact ⟨_, LowerPlain.fixBody hblock (getElem?_getElem! hjbs)
          (by rw [hblock.hd]; exact hjl), .fix_atom _ _⟩
  | construct hbl => intro t' h; exact absurd hbl (by decide)
  | @construct_atom _ iid c ar har =>
      intro t' h
      obtain ⟨args', rfl, hlen, -⟩ := LowerPlain.source_construct hblk h rfl
      obtain rfl : args' = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      exact ⟨_, .construct rfl (fun i hi => absurd hi (by simp)),
        .construct_atom rfl (hE.constructorArity har)⟩
  | @construct_app _ f a a' iid c args ar hf harity hlt ha ihf iha =>
      intro t' h
      rcases LowerPlain.source_app hblk h rfl with
        ⟨f', a₂, rfl, hlf, hla⟩ | ⟨kn, iid₀, k₀, args₀, hc, hsp, hargs⟩
      · obtain ⟨vf, hvf, hevf⟩ := ihf hlf
        obtain ⟨va, hva, heva⟩ := iha hla
        obtain ⟨args₂, rfl, hlen₂, hpt₂⟩ :=
          LowerPlain.source_ctorSpine hblk args.length args rfl hvf
        exact ⟨_, .app (LowerPlain.mkApps (.construct rfl (fun i hi => absurd hi (by simp)))
            hlen₂ hpt₂) hva,
          .construct_app rfl hevf (hE.constructorArity harity) (by rw [hlen₂]; exact hlt) heva⟩
      · exact (hne.ctorSpine_stuck hc hargs
          (hsp ▸ WcbvEval.construct_app rfl hf harity hlt ha)).elim
  | iota_block hbl => intro t' h; exact absurd hbl (by decide)
  | iota_sing hpc => intro t' h; exact absurd hpc (by decide)
  | proj_block hbl => intro t' h; exact absurd hbl (by decide)
  | proj_prop hpc => intro t' h; exact absurd hpc (by decide)
  | fix_unguarded hg => intro t' h; exact absurd hg (by decide)
  | @iota _ iid np k discr alts args names body r hprop hd hsel hlenb hbody ihd ihbody =>
      intro t' h
      obtain ⟨d', alts', rfl, hld, hlenA, hnA, hbA⟩ := LowerPlain.source_case hblk h rfl
      obtain ⟨dv, hdv, hevd⟩ := ihd hld
      obtain ⟨args₂, rfl, hlen₂, hpt₂⟩ :=
        LowerPlain.source_ctorSpine hblk args.length args rfl hdv
      obtain ⟨hkl, hkeq⟩ := Lower.getElem!_of_getElem? hsel
      have hbodyR : LowerPlain Γspec body (alts'[k]!).2 := by
        have := hbA k hkl
        rw [hkeq] at this
        exact this
      obtain ⟨hlenD, hptD⟩ := LowerPlain.drop_reverse np hlen₂ hpt₂
      obtain ⟨vr, hvr, hevr⟩ := ihbody (LowerPlain.substList_comm hΓ hlenD hptD hbodyR)
      obtain ⟨ar, har⟩ := constructorArity_of_eval (fl := eraseFlags) rfl hd
      have h3 : (alts'[k]!).1.length = names.length := by
        have hh := hnA k hkl; rw [hkeq] at hh; exact hh
      have h4 : (args₂.drop np).length = (args.drop np).length := by
        simp only [List.length_drop, hlen₂]
      exact ⟨vr, hvr, .iota rfl (hE.isPropositionalInductive har hprop) hevd
        (getElem?_getElem! (by rw [hlenA]; exact hkl)) (h4.trans (hlenb.trans h3.symm)) hevr⟩
  | @proj _ p discr args w r hprop hd hsel hw ihd ihw =>
      intro t' h
      obtain ⟨e', rfl, hle⟩ := LowerPlain.source_proj hblk h rfl
      obtain ⟨dv, hdv, hevd⟩ := ihd hle
      obtain ⟨args₂, rfl, hlen₂, hpt₂⟩ :=
        LowerPlain.source_ctorSpine hblk args.length args rfl hdv
      obtain ⟨hil, hieq⟩ := Lower.getElem!_of_getElem? hsel
      have hwR : LowerPlain Γspec w args₂[p.paramCount + p.fieldIdx]! := by
        have := hpt₂ _ hil
        rw [hieq] at this
        exact this
      obtain ⟨vr, hvr, hevr⟩ := ihw hwR
      obtain ⟨ar, har⟩ := constructorArity_of_eval (fl := eraseFlags) rfl hd
      exact ⟨vr, hvr, .proj rfl (hE.isPropositionalInductive har hprop) hevd
        (getElem?_getElem! (by rw [hlen₂]; exact hil)) hevr⟩
  | @fix_guarded _ f a av defs idx def_i argsv r hf ha hdef hidx hrest ihf iha ihrest =>
      intro t' h
      rcases LowerPlain.source_app hblk h rfl with
        ⟨f', a₂, rfl, hlf, -⟩ | ⟨kn, iid₀, k₀, args₀, hc, hsp, hargs⟩
      · obtain ⟨vf, hvf, -⟩ := ihf hlf
        exact (LowerPlain.fixSpine_absurd hblk argsv.length argsv rfl hvf).elim
      · exact (hne.ctorSpine_stuck hc hargs
          (hsp ▸ WcbvEval.fix_guarded rfl hf ha hdef hidx hrest)).elim
  | @fix_stuck _ f a av defs idx def_i argsv hf ha hdef hlt ihf iha =>
      intro t' h
      rcases LowerPlain.source_app hblk h rfl with
        ⟨f', a₂, rfl, hlf, -⟩ | ⟨kn, iid₀, k₀, args₀, hc, hsp, hargs⟩
      · obtain ⟨vf, hvf, -⟩ := ihf hlf
        exact (LowerPlain.fixSpine_absurd hblk argsv.length argsv rfl hvf).elim
      · exact (hne.ctorSpine_stuck hc hargs
          (hsp ▸ WcbvEval.fix_stuck rfl hf ha hdef hlt)).elim
  | @app_cong f a f' a' hf hstuck ha ihf iha =>
      intro t' h
      rcases LowerPlain.source_app hblk h rfl with
        ⟨g', a₂, rfl, hlf, hla⟩ | ⟨kn, iid₀, k₀, args₀, hc, hsp, hargs⟩
      · obtain ⟨vf, hvf, hevf⟩ := ihf hlf
        obtain ⟨va, hva, heva⟩ := iha hla
        exact ⟨_, .app hvf hva,
          .app_cong hevf (LowerPlain.isStuckApp_image hblk (eval_to_value hf) hstuck hvf) heva⟩
      · exact (hne.ctorSpine_stuck hc hargs (hsp ▸ WcbvEval.app_cong hf hstuck ha)).elim


/-- **`lowerFix_correct` at an arbitrary argument spine**, the generalisation of
`lowerFix_correct_atom`: a block member's constant applied to a spine is simulated by the
block's `.fix` node applied to the lowered spine. It is `lower_correct` at the pair
`Lower.fixConst` builds, so the block's λ-headedness is the global guard `hblk` rather than
a per-block premise (`LowerBlock.lambda_of_fixLambda` is how a caller discharges it). -/
theorem lowerFix_correct_plain {Γspec Γ : GlobalDeclarations} (hwf : LBWfSpec Γspec)
    (hE : LowerEnv Γspec Γ) (hEp : LowerEnvPlain Γspec Γ) (hsurv : DefsSurvive Γspec Γ)
    (hne : LowerNoEta Γspec) (hblk : BlockBodiesLambda Γspec)
    (hblkP : BlockBodiesPlain Γspec) (hfl : BlockDefsLambda Γspec)
    {kns : List Kername} {bs bs' : List LBTerm} {ids : List FVarId}
    {defs : List (@FixDef LBTerm)} {j : Nat} {kn : Kername} {args args' : List LBTerm}
    {v : LBTerm} (hblock : LowerBlock Γspec kns bs bs' ids defs) (hj : kns[j]? = some kn)
    (hlen : args'.length = args.length)
    (hpt : ∀ i, i < args.length → LowerPlain Γspec args[i]! args'[i]!)
    (hev : WcbvEval Γspec eraseFlags (LBTerm.mkApps (.const kn) args) v) :
    ∃ v', LowerPlain Γspec v v' ∧
      WcbvEval Γ eraseFlags (LBTerm.mkApps (.fix defs j) args') v' :=
  lower_correct_plain hwf hE hEp hsurv hne hblk hblkP hfl hev
    (LowerPlain.mkApps (.fixConst hblock hj) hlen hpt)

/-! ## Why the fragment stops where it does

`lower_correct_needs_ctorEta_guard` refutes the simulation at `Lower.ctorEta`.
`lower_correct_needs_elimBody_head` refutes it at `Lower.elimEta`, and does so at the
**empty** specification environment, so no hypothesis on `Γ` repairs it: `ElimHeadOf`'s
second disjunct admits the runtime library's own eliminator body as a head at every
environment. The third omitted arm, `elimApp`, is not refuted — it is out of reach of a
structural induction on `WcbvEval`, because the ι decomposition of an eliminator spine
(`mkElimBody_iota_fwd`) produces derivations that are not premises of the rule the spine's
own derivation ends with.
-/

/-- No eliminator body is a λ whose `case` scrutinises `□`: `mkElimBody`'s discriminant is
always the binder `.bvar nfs.length`, and `mkElimBodyRec` is a `.fix`. -/
theorem not_elimBody_box_disc {iid₀ : InductiveId} {np₀ dp₀ : Nat} {nfs₀ : List Nat}
    {iid : InductiveId} {np : Nat} {alts : List (List BinderName × LBTerm)} :
    ¬ ElimBody iid₀ np₀ dp₀ nfs₀ (.lambda .anon (.case (iid, np) .box alts)) := by
  intro hb
  have shape : ∀ (h : LBTerm), ElimBody iid₀ np₀ dp₀ nfs₀ h →
      h = mkElimBody iid₀ np₀ dp₀ nfs₀ ∨ h = mkElimBodyRec iid₀ np₀ dp₀ nfs₀ := by
    intro h hh; cases hh with
    | cases => exact .inl rfl
    | recur => exact .inr rfl
  rcases shape _ hb with he | he
  · rw [mkElimBody, show dp₀ + 1 + nfs₀.length = (dp₀ + nfs₀.length) + 1 by omega,
      List.replicate_succ, mkLambdas] at he
    injection he with _ he
    cases hm : dp₀ + nfs₀.length with
    | zero =>
        rw [hm, List.replicate_zero, mkLambdas] at he
        injection he with _ hdisc _
        exact LBTerm.noConfusion hdisc
    | succ m =>
        rw [hm, List.replicate_succ, mkLambdas] at he
        exact LBTerm.noConfusion he
  · rw [mkElimBodyRec] at he; exact LBTerm.noConfusion he

/-- No `Lower` pair relates a `case` node scrutinising `□`, under one binder, to an
application under one binder. -/
theorem lower_lambda_case_box_absurd {Γ : GlobalDeclarations} (hblk : BlockBodiesLambda Γ)
    {s t : LBTerm} {iid : InductiveId} {np : Nat} {alts : List (List BinderName × LBTerm)}
    {g a : LBTerm} (h : Lower Γ s t)
    (hs : s = .lambda .anon (.case (iid, np) .box alts))
    (ht : t = .lambda .anon (.app g a)) : False := by
  cases h with
  | box | bvar | fvar | prim | const | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion hs
  | @lambda n₀ n' b₀ b' hb =>
      injection hs with _ hb₀
      injection ht with _ hb'
      subst hb₀; subst hb'
      obtain ⟨d', alts', he, -, -, -, -⟩ := Lower.source_case hblk hb rfl
      exact LBTerm.noConfusion he
  | fixConst | fixBody => exact LBTerm.noConfusion ht
  | @ctorApp kn iid₀ k₀ args args' =>
      obtain ⟨rfl, he⟩ := mkApps_eq_lambda hs
      exact LBTerm.noConfusion he
  | @ctorEta kn iid₀ k₀ args args' ns₀ =>
      obtain ⟨rfl, he⟩ := mkApps_eq_lambda hs
      exact LBTerm.noConfusion he
  | @elimApp hd iid₀ np₀ dp₀ nfs₀ pre disc disc' minors alts₀ extra extra' =>
      obtain ⟨g₀, b₀, he⟩ := mkApps_ne_nil_is_app (f := hd)
        (args := pre ++ disc :: minors ++ extra) (by cases pre <;> simp)
      rw [he] at hs; exact LBTerm.noConfusion hs
  | @elimEta hd iid₀ np₀ dp₀ nfs₀ args₀ ns₀ body₀ hh =>
      obtain ⟨rfl, he⟩ := mkApps_eq_lambda hs
      subst he
      rcases hh with ⟨kn, hkn, -⟩ | hbdy
      · exact LBTerm.noConfusion hkn
      · exact not_elimBody_box_disc hbdy

/-- The empty environment declares nothing. -/
theorem envLookup_nil (kn : Kername) (d : GlobalDecl) : LBTerm.envLookup [] kn ≠ some d := by
  intro h; simp [LBTerm.envLookup] at h

/-- **The unrestricted `lower_correct` is false at the `elimEta` arm, at every pair of
environments.** The source is the runtime library's own `casesOn` body applied to one
argument: the pass η-expands it, the source β-reduces the argument's *value* into the
`case` node while the target keeps the unevaluated argument outside it, and no arm relates
a `case` node to an application. The first six conjuncts record that every guard the design
names holds at the empty environment, so the culprit is `ElimHeadOf`'s second disjunct,
which admits an `ElimBody` shape as a head anywhere; restricting `elimEta` to `ElimDecl`
heads removes it. -/
theorem lower_correct_needs_elimBody_head (Γ : GlobalDeclarations) (iid : InductiveId)
    (np : Nat) :
    LBWfSpec [] ∧ LowerEnv [] [] ∧ DefsSurvive [] [] ∧ LowerNoEta [] ∧
      BlockBodiesLambda [] ∧ LBClosed (.app (mkElimBody iid np 0 [1]) .box) 0 ∧
      Lower [] (.app (mkElimBody iid np 0 [1]) .box)
        (.lambda .anon (LBTerm.mkApps (mkElimBody iid np 0 [1]) [.box, .bvar 0])) ∧
      WcbvEval [] eraseFlags (.app (mkElimBody iid np 0 [1]) .box)
        (.lambda .anon (.case (iid, np) .box (elimAlts [1]))) ∧
      ¬ ∃ v', Lower [] (.lambda .anon (.case (iid, np) .box (elimAlts [1]))) v' ∧
        WcbvEval Γ eraseFlags
          (.lambda .anon (LBTerm.mkApps (mkElimBody iid np 0 [1]) [.box, .bvar 0])) v' := by
  have hnodecl : ∀ (kn : Kername) (b : LBTerm), ¬ DefnDecl [] kn b :=
    fun kn b h => envLookup_nil kn _ h
  have hblkNil : BlockBodiesLambda [] := by
    intro kns bs bs' ids defs hblock j hj
    exact absurd (hblock.hdecl j hj) (hnodecl _ _)
  have hneNil : LowerNoEta [] := by
    intro kn n b h
    rcases Lower.source_const h rfl with
      ⟨he, -⟩ | ⟨iid₀, k₀, hc, -, he⟩ | ⟨iid₀, k₀, ns₀, hc, -, -, -⟩
      | ⟨iid₀, np₀, dp₀, nfs₀, ns₀, body₀, hd₀, -, -, -, -⟩ | ⟨defs₀, j₀, he⟩
    · exact LBTerm.noConfusion he
    · exact LBTerm.noConfusion he
    · exact envLookup_nil kn _ hc
    · obtain ⟨b₀, hb₀, -⟩ := hd₀; exact envLookup_nil kn _ hb₀
    · exact LBTerm.noConfusion he
  refine ⟨⟨by simp, fun kn b h => absurd h (hnodecl _ _)⟩,
    { keys := by simp
      defs := fun kn b₀ b h _ => absurd h (hnodecl _ _)
      defsTotal := fun kn b₀ h _ => absurd h (hnodecl _ _)
      axioms := fun kn h => absurd h (envLookup_nil kn _)
      inds := fun kn d h => absurd h (envLookup_nil kn _)
      sub := fun kn h => absurd rfl h
      closed := fun kn b h => absurd h (hnodecl _ _) },
    fun kn b₀ h _ => absurd h (hnodecl _ _), hneNil, hblkNil,
    ⟨mkElimBody_closed iid np 0 [1], trivial⟩, ?_, ?_, ?_⟩
  · have hself : Lower [] (mkElimBody iid np 0 [1]) (mkElimBody iid np 0 [1]) := by
      refine .lambda (.lambda (.case (.bvar 1) rfl (fun i _ => rfl) (fun i hi => ?_)))
      obtain rfl : i = 0 := by simpa using hi
      exact .app (.bvar 1) (.bvar 0)
    exact @Lower.elimEta [] (mkElimBody iid np 0 [1]) iid np 0 [1] [.box] [.anon]
      (LBTerm.mkApps (mkElimBody iid np 0 [1]) [.box, .bvar 0]) (.inr .cases) (by simp)
      (by simp) (.app (.app hself .box) (.bvar 0))
  · exact .beta (.lam _ _) .box (.lam _ _)
  · rintro ⟨v', hlow, hev⟩
    cases hev with
    | lam => exact lower_lambda_case_box_absurd hblkNil hlow rfl rfl


/-! ## Non-vacuity

`PlainFixture` declares one inductive and no constants, so the three block guards hold
vacuously and every congruence and redex arm of the simulation fires on a closed program.
The two `fix` rules of `WcbvEval` are the exception: `LowerPlain.fixSpine_absurd` shows
their source has no image in the fragment, so they are provably unreachable rather than
merely unfired.
-/

namespace PlainFixture

/-- One inductive, two constructors: `mk` with a field, `nil` without. -/
def kn : Kername := { mp := .MPfile [], id := "LPI" }

def iid : InductiveId := { mutualBlockName := kn, idx := 0 }

def indBody : MutualInductiveBody :=
  { npars := 0,
    bodies := [{ name := "LPI", ctors := [{ name := "mk", nargs := 1 },
                                          { name := "nil", nargs := 0 }],
                 projs := [] }] }

def env : GlobalDeclarations := [(kn, .inductiveDecl indBody)]

theorem envLookup_eq (kn' : Kername) :
    LBTerm.envLookup env kn' = if Kername.beq kn kn' then some (.inductiveDecl indBody)
      else none := rfl

theorem arity_mk : constructorArity env iid 0 = some 1 := rfl
theorem arity_nil : constructorArity env iid 1 = some 0 := rfl
theorem notProp : isPropositionalInductive env iid = false := rfl

/-- No constant is declared, so no block has a member. -/
theorem noDefn (kn' : Kername) (b : LBTerm) : ¬ DefnDecl env kn' b := by
  intro h
  rw [DefnDecl, envLookup_eq] at h
  split at h
  · exact GlobalDecl.noConfusion (Option.some.inj h)
  · simp at h

theorem blockBodiesLambda : BlockBodiesLambda env :=
  fun _ _ _ _ _ hblock j hj => absurd (hblock.hdecl j hj) (noDefn _ _)

theorem blockBodiesPlain : BlockBodiesPlain env :=
  fun _ _ _ _ _ hblock i hi => absurd (hblock.hdecl i hi) (noDefn _ _)

theorem blockDefsLambda : BlockDefsLambda env :=
  fun _ _ _ _ _ hblock j hj =>
    absurd (hblock.hdecl j (by rw [← hblock.hd]; exact hj)) (noDefn _ _)

theorem noEta : LowerNoEta env := by
  intro kn' n b h
  rcases Lower.source_const h rfl with
    ⟨he, -⟩ | ⟨iid₀, k₀, hc, -, he⟩ | ⟨iid₀, k₀, ns₀, hc, -, -, -⟩
    | ⟨iid₀, np₀, dp₀, nfs₀, ns₀, body₀, hd₀, -, -, -, -⟩ | ⟨defs₀, j₀, he⟩
  · exact LBTerm.noConfusion he
  · exact LBTerm.noConfusion he
  · exact noDefn _ _ hc
  · obtain ⟨b₀, hb₀, -⟩ := hd₀; exact noDefn _ _ hb₀
  · exact LBTerm.noConfusion he

theorem wfSpec : LBWfSpec env := ⟨by simp [env], fun kn' b h => absurd h (noDefn _ _)⟩

theorem lowerEnv : LowerEnv env env where
  keys := by simp [env]
  defs := fun kn' b₀ b h _ => absurd h (noDefn _ _)
  defsTotal := fun kn' b₀ h _ => absurd h (noDefn _ _)
  axioms := fun _ h => .inl h
  inds := fun _ _ h => h
  sub := fun _ h => h
  closed := fun kn' b h => absurd h (noDefn _ _)

theorem lowerEnvPlain : LowerEnvPlain env env :=
  fun _ _ _ h _ => absurd h (noDefn _ _)

theorem defsSurvive : DefsSurvive env env :=
  fun _ _ h _ => absurd h (noDefn _ _)

/-- The same inductive, plus a constructor constant for the unary `mk`. -/
def cKn : Kername := { mp := .MPfile [], id := "LPImk" }

def envC : GlobalDeclarations :=
  (cKn, .constantDecl ⟨some (.construct iid 0 [])⟩) :: env

theorem ctorDecl_cKn : CtorDecl envC cKn iid 0 := rfl

theorem arity_mk_C : constructorArity envC iid 0 = some 1 := rfl

/-- The simulation, at this fixture's guards. -/
theorem sim {t v t' : LBTerm} (hev : WcbvEval env eraseFlags t v) (h : LowerPlain env t t') :
    ∃ v', LowerPlain env v v' ∧ WcbvEval env eraseFlags t' v' :=
  lower_correct_plain wfSpec lowerEnv lowerEnvPlain defsSurvive noEta blockBodiesLambda
    blockBodiesPlain blockDefsLambda hev h

/-- The `mk □` spine, evaluated. -/
theorem mk_box_eval :
    WcbvEval env eraseFlags (.app (.construct iid 0 []) .box)
      (LBTerm.mkApps (.construct iid 0 []) [.box]) :=
  .construct_app (args := []) rfl (.construct_atom rfl arity_mk) arity_mk (by decide) .box

/-- The `mk □` spine, lowered. -/
theorem mk_box_lower :
    LowerPlain env (.app (.construct iid 0 []) .box) (.app (.construct iid 0 []) .box) :=
  .app (.construct rfl (fun i hi => absurd hi (by simp))) .box

end PlainFixture

open PlainFixture in
/-- **The atom arms fire**: `□`, a λ and a free variable are their own values on both
sides. -/
theorem lower_correct_plain_fires_atoms (x : FVarId) :
    (∃ v', LowerPlain env .box v' ∧ WcbvEval env eraseFlags .box v') ∧
    (∃ v', LowerPlain env (.lambda .anon .box) v' ∧
      WcbvEval env eraseFlags (.lambda .anon .box) v') ∧
    (∃ v', LowerPlain env (.fvar x) v' ∧ WcbvEval env eraseFlags (.fvar x) v') :=
  ⟨sim (t := .box) (t' := .box) .box .box,
   sim (t := .lambda .anon .box) (t' := .lambda .anon .box) (.lam _ _) (.lambda .box),
   sim (t := .fvar x) (t' := .fvar x) (.fvar x) (.fvar x)⟩

open PlainFixture in
/-- **The β arm fires**: `(λ x. x) □ ⇓ □` on both sides. -/
theorem lower_correct_plain_fires_beta :
    ∃ v', LowerPlain env .box v' ∧
      WcbvEval env eraseFlags (.app (.lambda .anon (.bvar 0)) .box) v' :=
  sim (t := .app (.lambda .anon (.bvar 0)) .box) (v := .box)
    (t' := .app (.lambda .anon (.bvar 0)) .box)
    (.beta (.lam _ _) .box .box) (.app (.lambda (.bvar 0)) .box)

open PlainFixture in
/-- **The ζ arm fires**: `let x := □ in x ⇓ □` on both sides. -/
theorem lower_correct_plain_fires_zeta :
    ∃ v', LowerPlain env .box v' ∧
      WcbvEval env eraseFlags (.letIn .anon .box (.bvar 0)) v' :=
  sim (t := .letIn .anon .box (.bvar 0)) (v := .box) (t' := .letIn .anon .box (.bvar 0))
    (.zeta .box .box) (.letIn .box (.bvar 0))

open PlainFixture in
/-- **The nullary-constructor arm fires**: `nil` is its own value on both sides. -/
theorem lower_correct_plain_fires_construct_atom :
    ∃ v', LowerPlain env (.construct iid 1 []) v' ∧
      WcbvEval env eraseFlags (.construct iid 1 []) v' :=
  sim (t := .construct iid 1 []) (t' := .construct iid 1 [])
    (.construct_atom rfl arity_nil) (.construct rfl (fun i hi => absurd hi (by simp)))

open PlainFixture in
/-- **The constructor-application arm fires**: `mk □` accumulates one argument on both
sides. -/
theorem lower_correct_plain_fires_construct_app :
    ∃ v', LowerPlain env (.app (.construct iid 0 []) .box) v' ∧
      WcbvEval env eraseFlags (.app (.construct iid 0 []) .box) v' :=
  sim (t := .app (.construct iid 0 []) .box) (t' := .app (.construct iid 0 []) .box)
    mk_box_eval mk_box_lower

open PlainFixture in
/-- **The ι arm fires**: a `case` on `mk □` selects the first branch and substitutes the
field, on both sides. -/
theorem lower_correct_plain_fires_iota :
    ∃ v', LowerPlain env .box v' ∧
      WcbvEval env eraseFlags
        (.case (iid, 0) (.app (.construct iid 0 []) .box)
          [([.anon], .bvar 0), ([], .box)]) v' := by
  refine sim (t := .case (iid, 0) (.app (.construct iid 0 []) .box)
      [([.anon], .bvar 0), ([], .box)]) (v := .box)
    (t' := .case (iid, 0) (.app (.construct iid 0 []) .box)
      [([.anon], .bvar 0), ([], .box)])
    (.iota rfl notProp mk_box_eval rfl rfl .box) ?_
  refine .case mk_box_lower rfl (fun i hi => ?_) (fun i hi => ?_)
  · have hi' : i < 2 := by simpa using hi
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl
  · have hi' : i < 2 := by simpa using hi
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · exact .bvar 0
    · exact .box

open PlainFixture in
/-- **The projection arm fires**: projecting the field of `mk □` yields `□` on both
sides. -/
theorem lower_correct_plain_fires_proj :
    ∃ v', LowerPlain env .box v' ∧
      WcbvEval env eraseFlags
        (.proj { indType := iid, paramCount := 0, fieldIdx := 0 }
          (.app (.construct iid 0 []) .box)) v' :=
  sim (t := .proj { indType := iid, paramCount := 0, fieldIdx := 0 }
        (.app (.construct iid 0 []) .box)) (v := .box)
    (t' := .proj { indType := iid, paramCount := 0, fieldIdx := 0 }
        (.app (.construct iid 0 []) .box))
    (.proj rfl notProp mk_box_eval rfl .box) (.proj mk_box_lower)

open PlainFixture in
/-- **The stuck-application arm fires**: a free variable applied to `□` is a value on both
sides. -/
theorem lower_correct_plain_fires_app_cong (x : FVarId) :
    ∃ v', LowerPlain env (.app (.fvar x) .box) v' ∧
      WcbvEval env eraseFlags (.app (.fvar x) .box) v' :=
  sim (t := .app (.fvar x) .box) (v := .app (.fvar x) .box) (t' := .app (.fvar x) .box)
    (.app_cong (.fvar x) rfl .box) (.app (.fvar x) .box)


/-- **`LowerNoEta` pins every constructor constant's arity to `0`.** The guard is therefore
much stronger than "the pass does not η-expand": a specification environment that declares
a constructor constant of positive arity — which `ErasesDecl.ctor` does for every
constructor a program reaches, `Nat.succ` included — satisfies no `LowerNoEta`, so both
`lower_correct_deltaChain` and `lower_correct_plain` are vacuous there. -/
theorem lowerNoEta_forces_nullary_ctors {Γ : GlobalDeclarations} {kn : Kername}
    {iid : InductiveId} {k : Nat} (hc : CtorDecl Γ kn iid k) (hpos : 0 < cstrArity Γ iid k) :
    ¬ LowerNoEta Γ :=
  fun hne => absurd (hne.cstrArity_eq_zero hc) (by omega)

/-- The guard fails on a one-inductive environment with a unary constructor constant. -/
theorem lowerNoEta_fails : ¬ LowerNoEta PlainFixture.envC :=
  lowerNoEta_forces_nullary_ctors PlainFixture.ctorDecl_cKn
    (by rw [cstrArity_eq_of_constructorArity PlainFixture.arity_mk_C]; omega)

end LeanToLambdaBox
