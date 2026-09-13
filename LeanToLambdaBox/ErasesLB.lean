import LeanToLambdaBox.ErasesTotal
import LeanToLambdaBox.LowerFix
import LeanToLambdaBox.SourceEval

/-!
# `ErasesLB` — erasure composed with the pass

`Erases` is a congruence over `Lean.Expr`; the four Lean-specific compilation steps live in
`Lower`. Neither alone relates a source term to what the eraser emits for it. The composite
does, and this module carries it together with the introduction lemmas that replay the
compilation steps at source level.

* `ErasesLB Σ = Erases ⨟ Lower Σ`, with `ErasesLBAlt`/`ErasesLBAlts` for a `case`
  alternative and a block of them.
* Eight introduction lemmas — `box`, `app`, `ctor_head`, `ctor`, `lit`, `proj`, `cases`,
  `fix` — each taking the source-level data of one compilation step.
* Their `ErasesLBFix.*` twins, the same steps inside a mutual block, where the emitted term
  carries the block's fix variables (`LowerFix.lean`'s `ErasesLBFix = ErasesLB ⨟ ConstToFVar`),
  plus `ErasesLBFix.fixvar`, the block branch's own step, which has no `ErasesLB` counterpart.
* `erasesLB_of_spine`, which reads a spine premise written as `Erases` and `Lower` side by
  side as one `ErasesLB` premise.

`ErasesLB.cases` carries premises `doc/rework/01-DESIGN.md` §4.7 does not print; its
docstring says which and why.

The two `*_eta` twins are deleted with the pass's two η arms, and `ctor_head_needs_nullary`
with them: it showed the empty constructor node reachable from a constructor constant only
at arity zero, a fact about `Lower.ctorApp`. `ctor_head` and `ctor` are `Erases.ctor` plus
`Lower.construct`, at every arity.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-! ## The composites -/

/-- A source term erases to a λ□ term that the pass lowers to `t`: the relation the eraser's
output is a member of. -/
def ErasesLB (env : VEnv) (Us : List Name) (Γ : GlobalDeclarations) (Δ : VLCtx)
    (e : Expr) (t : LBTerm) : Prop :=
  ∃ t₀, Erases env Us Δ e t₀ ∧ Lower Γ t₀ t

/-- The same composite for one `case` alternative: a source minor function erases to a λ□
term whose λ-chain `LowerAlt` peels into `alt`'s binder list. -/
def ErasesLBAlt (env : VEnv) (Us : List Name) (Γ : GlobalDeclarations) (Δ : VLCtx)
    (nf : Nat) (m : Expr) (alt : List BinderName × LBTerm) : Prop :=
  ∃ m₀, Erases env Us Δ m m₀ ∧ LowerAlt Γ nf m₀ alt

/-- The pointwise lift of `ErasesLBAlt` over a block's field arities, the source twin of
`LowerAlts`. -/
def ErasesLBAlts (env : VEnv) (Us : List Name) (Γ : GlobalDeclarations) (Δ : VLCtx)
    (nfs : List Nat) (minors : List Expr)
    (alts : List (List BinderName × LBTerm)) : Prop :=
  minors.length = nfs.length ∧ alts.length = nfs.length ∧
    ∀ i, i < nfs.length → ErasesLBAlt env Us Γ Δ nfs[i]! minors[i]! alts[i]!

/-- One `case` alternative inside a mutual block: the alternative of `ErasesLBAlt` with the
block's constants already rewritten to its fix variables. Only the binder count of the
alternative is pinned, since the pass leaves the names free. -/
def ErasesLBFixAlt (env : VEnv) (Us : List Name) (Γ : GlobalDeclarations)
    (kns : List Kername) (ids : List FVarId) (Δ : VLCtx) (nf : Nat) (m : Expr)
    (alt : List BinderName × LBTerm) : Prop :=
  ∃ alt₁ : List BinderName × LBTerm, ErasesLBAlt env Us Γ Δ nf m alt₁ ∧
    alt.1.length = alt₁.1.length ∧ ConstToFVar kns ids alt₁.2 alt.2

/-- The pointwise lift of `ErasesLBFixAlt` over a block's field arities. -/
def ErasesLBFixAlts (env : VEnv) (Us : List Name) (Γ : GlobalDeclarations)
    (kns : List Kername) (ids : List FVarId) (Δ : VLCtx) (nfs : List Nat)
    (minors : List Expr) (alts : List (List BinderName × LBTerm)) : Prop :=
  minors.length = nfs.length ∧ alts.length = nfs.length ∧
    ∀ i, i < nfs.length → ErasesLBFixAlt env Us Γ kns ids Δ nfs[i]! minors[i]! alts[i]!

/-! ## Indexed-list plumbing -/

/-- A `getElem!` below the left summand reads the left summand. -/
theorem getElem!_append_left {α : Type} [Inhabited α] (l₁ l₂ : List α) {i : Nat}
    (h : i < l₁.length) : (l₁ ++ l₂)[i]! = l₁[i]! := by
  rw [getElem!_pos (l₁ ++ l₂) i (by simp; omega), getElem!_pos l₁ i h,
    List.getElem_append_left h]

/-- A `getElem!` past the left summand reads the right summand. -/
theorem getElem!_append_right {α : Type} [Inhabited α] (l₁ l₂ : List α) {i : Nat}
    (h : i < l₂.length) : (l₁ ++ l₂)[l₁.length + i]! = l₂[i]! := by
  rw [getElem!_pos (l₁ ++ l₂) (l₁.length + i) (by simp; omega), getElem!_pos l₂ i h,
    List.getElem_append_right (by omega)]
  congr 1
  omega

/-- An index-wise relation holding on both summands holds on the append. -/
theorem forall_index_append {α β : Type} [Inhabited α] [Inhabited β] {R : α → β → Prop}
    {l₁ l₂ : List α} {m₁ m₂ : List β} (hlen₁ : m₁.length = l₁.length)
    (hlen₂ : m₂.length = l₂.length)
    (h₁ : ∀ i, i < l₁.length → R l₁[i]! m₁[i]!)
    (h₂ : ∀ i, i < l₂.length → R l₂[i]! m₂[i]!) :
    ∀ i, i < (l₁ ++ l₂).length → R (l₁ ++ l₂)[i]! (m₁ ++ m₂)[i]! := by
  intro i hi
  rw [List.length_append] at hi
  by_cases hl : i < l₁.length
  · rw [getElem!_append_left l₁ l₂ hl, getElem!_append_left m₁ m₂ (by omega)]
    exact h₁ i hl
  · obtain ⟨j, rfl⟩ : ∃ j, i = l₁.length + j := ⟨i - l₁.length, by omega⟩
    rw [getElem!_append_right l₁ l₂ (by omega : j < l₂.length),
      show l₁.length + j = m₁.length + j by omega,
      getElem!_append_right m₁ m₂ (by omega : j < m₂.length)]
    exact h₂ j (by omega)

/-- An index-wise relation on a cons, from its head and its tail. -/
theorem forall_index_cons {α β : Type} [Inhabited α] [Inhabited β] {R : α → β → Prop}
    {a : α} {b : β} {l : List α} {m : List β} (h₀ : R a b)
    (h : ∀ i, i < l.length → R l[i]! m[i]!) :
    ∀ i, i < (a :: l).length → R (a :: l)[i]! (b :: m)[i]! := by
  intro i hi
  match i with
  | 0 => rwa [getElem!_pos (a :: l) 0 (by simp), getElem!_pos (b :: m) 0 (by simp)]
  | k + 1 =>
      have hk : k < l.length := by simpa using hi
      by_cases hm : k < m.length
      · rw [getElem!_pos (a :: l) (k + 1) (by simpa using hk),
          getElem!_pos (b :: m) (k + 1) (by simp; omega), List.getElem_cons_succ,
          List.getElem_cons_succ, ← getElem!_pos l k hk, ← getElem!_pos m k hm]
        exact h k hk
      · rw [getElem!_pos (a :: l) (k + 1) (by simpa using hk), List.getElem_cons_succ,
          ← getElem!_pos l k hk, getElem!_neg (b :: m) (k + 1) (by simp; omega),
          ← getElem!_neg m k (by omega)]
        exact h k hk

/-- `Erases` is a congruence over an application spine. -/
theorem Erases.mkApps {env : VEnv} {Us : List Name} {Δ : VLCtx} {f : Expr} {f' : LBTerm} :
    ∀ (args : List Expr) (args' : List LBTerm), Erases env Us Δ f f' →
      args'.length = args.length →
      (∀ i, i < args.length → Erases env Us Δ args[i]! args'[i]!) →
      Erases env Us Δ (mkApps f args) (LBTerm.mkApps f' args') := by
  intro args
  induction args generalizing f f' with
  | nil =>
      intro args' hf hlen _
      have : args' = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst this; exact hf
  | cons a as ih =>
      intro args' hf hlen h
      obtain ⟨b, bs, rfl⟩ : ∃ b bs, args' = b :: bs := by
        cases args' with
        | nil => simp at hlen
        | cons b bs => exact ⟨b, bs, rfl⟩
      have hlen' : bs.length = as.length := by simpa using hlen
      have ha : Erases env Us Δ a b := by
        have h0 := h 0 (by simp)
        rwa [getElem!_pos (a :: as) 0 (by simp), getElem!_pos (b :: bs) 0 (by simp)] at h0
      refine ih bs (.app hf ha) hlen' ?_
      intro i hi
      have hs := h (i + 1) (by simpa using hi)
      rwa [getElem!_pos (a :: as) (i + 1) (by simpa using hi), List.getElem_cons_succ,
        getElem!_pos (b :: bs) (i + 1) (by simp [hlen']; omega), List.getElem_cons_succ,
        ← getElem!_pos as i hi, ← getElem!_pos bs i (by omega)] at hs

/-- The middle list of a spine of composites: the erasure images the pass then lowers. -/
theorem ErasesLB.exists_mid {env : VEnv} {Us : List Name} {Γ : GlobalDeclarations}
    {Δ : VLCtx} {args : List Expr} {args' : List LBTerm}
    (ha : ∀ i, i < args.length → ErasesLB env Us Γ Δ args[i]! args'[i]!) :
    ∃ mid : List LBTerm, mid.length = args.length ∧
      (∀ i, i < args.length → Erases env Us Δ args[i]! mid[i]!) ∧
      (∀ i, i < args.length → Lower Γ mid[i]! args'[i]!) := by
  obtain ⟨mid, hlen, hpt⟩ :=
    exists_list_of_index args.length
      (fun i m => Erases env Us Δ args[i]! m ∧ Lower Γ m args'[i]!) ha
  exact ⟨mid, hlen, fun i hi => (hpt i hi).1, fun i hi => (hpt i hi).2⟩


/-! ## Introduction lemmas

One per compilation step, with the source-level data of the step. `Erases` supplies the
congruence factor and `Lower` the step itself.
-/

variable {env : VEnv} {Us : List Name} {Γ : GlobalDeclarations} {Δ : VLCtx}

/-- An irrelevant term composes to `LBTerm.box`: the pass is the identity there. -/
theorem ErasesLB.box {e : Expr} {ve : VExpr} (htr : TrExprS env Us Δ e ve)
    (her : Erasable env Us.length Δ.toCtx ve) : ErasesLB env Us Γ Δ e .box :=
  ⟨.box, .box htr her, .box⟩

/-- Application is a congruence in both factors. -/
theorem ErasesLB.app {f a : Expr} {f' a' : LBTerm} (hf : ErasesLB env Us Γ Δ f f')
    (ha : ErasesLB env Us Γ Δ a a') : ErasesLB env Us Γ Δ (.app f a) (.app f' a') :=
  let ⟨f₀, hf₀, hf₁⟩ := hf
  let ⟨a₀, ha₀, ha₁⟩ := ha
  ⟨.app f₀ a₀, .app hf₀ ha₀, .app hf₁ ha₁⟩

/-- A bare constructor constant composes to the empty constructor node: `Erases.ctor` is
the `tConstruct` congruence at the head, and the pass relates that node to itself. -/
theorem ErasesLB.ctor_head {cn I : Name} {us : List Level} {iid : InductiveId}
    {k np : Nat} {nfs : List Nat} (hc : CtorOf env cn I k)
    (hi : IndInfo env I iid np nfs) :
    ErasesLB env Us Γ Δ (.const cn us) (.construct iid k []) :=
  ⟨.construct iid k [], .ctor hc hi, .construct rfl (fun i hi => absurd hi (by simp))⟩

/-- A constructor spine composes to the applied constructor node, at any arity: the
arguments arrive through `Erases.app`, so the node carries none and the pass is the
`app`/`construct` congruence over the spine. -/
theorem ErasesLB.ctor {cn I : Name} {us : List Level} {iid : InductiveId}
    {k np : Nat} {nfs : List Nat} {args : List Expr} {args' : List LBTerm}
    (hc : CtorOf env cn I k) (hi : IndInfo env I iid np nfs)
    (hlen : args'.length = args.length)
    (ha : ∀ i, i < args.length → ErasesLB env Us Γ Δ args[i]! args'[i]!) :
    ErasesLB env Us Γ Δ (args.foldl Expr.app (.const cn us))
      (LBTerm.mkApps (.construct iid k []) args') := by
  obtain ⟨mid, hmlen, herm, hlowm⟩ := ErasesLB.exists_mid ha
  refine ⟨LBTerm.mkApps (.construct iid k []) mid, ?_, ?_⟩
  · rw [← mkApps_eq_foldl]
    exact Erases.mkApps args mid (.ctor hc hi) hmlen herm
  · exact Lower.mkApps (.construct rfl (fun i hi => absurd hi (by simp))) (by omega)
      (fun i hi => hlowm i (by omega))

/-- A literal composes to whatever its kernel unfolding composes to: the pass is the identity
at the source step, so the composite inherits `Erases.lit`. -/
theorem ErasesLB.lit {l : Literal} {t : LBTerm} (hcl : env.ContainsLits l)
    (h : ErasesLB env Us Γ Δ l.toConstructor t) : ErasesLB env Us Γ Δ (.lit l) t :=
  let ⟨t₀, h₀, h₁⟩ := h
  ⟨t₀, .lit hcl h₀, h₁⟩

/-- A projection composes to the projection node: `Erases.proj` reads the block data and the
relevance of the type former, and the pass is the `proj` congruence. -/
theorem ErasesLB.proj {S : Name} {i : Nat} {e : Expr} {t : LBTerm} {iid : InductiveId}
    {np nf : Nat} (hs : IndInfo env S iid np [nf]) (hinf : InformativeInd env S) (hi : i < nf)
    (hd : ErasesLB env Us Γ Δ e t) :
    ErasesLB env Us Γ Δ (.proj S i e) (.proj ⟨iid, np, i⟩ t) :=
  let ⟨t₀, h₀, h₁⟩ := hd
  ⟨.proj ⟨iid, np, i⟩ t₀, .proj hs hinf hi h₀, .proj h₁⟩

/-- A block member's constant composes to the block's `.fix` node. `hnk` is `Lower.fixConst`'s
own guard: a block member is a definition, never an eliminator key. -/
theorem ErasesLB.fix {cn : Name} {us : List Level} {ci : VConstant} {kns : List Kername}
    {bs bs' : List LBTerm} {ids : List FVarId} {defs : List (@FixDef LBTerm)} {j : Nat}
    (hblk : LowerBlock Γ kns bs bs' ids defs) (hnk : ¬ RuntimeKey Γ (toKername cn))
    (hj : kns[j]? = some (toKername cn)) (h : env.constants cn = some ci)
    (ho : ConstOrigin env cn) : ErasesLB env Us Γ Δ (.const cn us) (.fix defs j) :=
  ⟨.const (toKername cn), .const h ho, Lower.fixConst' hblk hnk hj⟩


/-- A saturated eliminator spine composes to a `.case` node: the `dp` arguments before the
discriminant are dropped, the minors become the alternatives, and `hlen` pins the spine to
the node's own arity. `hpre`, `hppi` and `hclass` are not in
`doc/rework/01-DESIGN.md` §4.7's printed signature: the dropped arguments still need an
erasure image, since `Erases` is a congruence over the whole spine, and
`Erases.exists_of_trExprS_of_projInfo` supplies one only under a `ProjInfo` side premise
and the classification of every declared constant. -/
theorem ErasesLB.cases {con : Name} {us : List Level} {ci : VConstant}
    {iid : InductiveId} {np dp : Nat} {nfs : List Nat} {args : List Expr}
    {disc : LBTerm} {alts : List (List BinderName × LBTerm)}
    (hE : ElimDecl Γ (toKername con) iid np dp nfs) (hcst : env.constants con = some ci)
    (hco : ConstOrigin env con) (henv : env.WF)
    (hclass : ∀ c ci, env.constants c = some ci → (∃ I k, CtorOf env c I k) ∨
      (∃ iid np nfs, IndInfo env c iid np nfs) ∨ ConstOrigin env c)
    (hΔ : VLCtx.WF env Us.length Δ)
    (hpre : ∀ a ∈ args.take dp, ∃ ve, TrExprS env Us Δ a ve)
    (hppi : ∀ a ∈ args.take dp, ProjInfo env a)
    (hlen : args.length = dp + 1 + nfs.length)
    (hd : ErasesLB env Us Γ Δ args[dp]! disc)
    (hm : ErasesLBAlts env Us Γ Δ nfs (args.drop (dp + 1)) alts) :
    ErasesLB env Us Γ Δ (args.foldl Expr.app (.const con us))
      (.case (iid, np) disc alts) := by
  obtain ⟨hmlen, halen, halts⟩ := hm
  obtain ⟨disc₀, hderase, hdlow⟩ := hd
  have hdp : dp < args.length := by omega
  have hprelen : (args.take dp).length = dp := by simp; omega
  have hsplit : args = args.take dp ++ args[dp]! :: args.drop (dp + 1) := by
    rw [getElem!_pos args dp hdp, ← List.drop_eq_getElem_cons hdp, List.take_append_drop]
  obtain ⟨pre₀, hplen, hperase⟩ :=
    exists_list_of_index (args.take dp).length
      (fun i b => Erases env Us Δ (args.take dp)[i]! b)
      (fun i hi => by
        obtain ⟨ve, hve⟩ := hpre _ (Lower.getElem!_mem hi)
        exact Erases.exists_of_trExprS_of_projInfo henv hclass hΔ
          (hppi _ (Lower.getElem!_mem hi)) hve)
  obtain ⟨minors₀, hnlen, hnpt⟩ :=
    exists_list_of_index (args.drop (dp + 1)).length
      (fun i b => Erases env Us Δ (args.drop (dp + 1))[i]! b ∧
        LowerAlt Γ nfs[i]! b alts[i]!)
      (fun i hi => halts i (by omega))
  refine ⟨LBTerm.mkApps (.const (toKername con)) (pre₀ ++ disc₀ :: minors₀), ?_, ?_⟩
  · have hspine := Erases.mkApps (f := Expr.const con us)
      (args.take dp ++ args[dp]! :: args.drop (dp + 1)) (pre₀ ++ disc₀ :: minors₀)
      (.const hcst hco) (by simp [hplen, hnlen])
      (forall_index_append hplen (by simp [hnlen]) hperase
        (forall_index_cons hderase (fun i hi => (hnpt i hi).1)))
    rw [← hsplit] at hspine
    rw [← mkApps_eq_foldl]
    exact hspine
  · have hstep : Lower Γ
        (LBTerm.mkApps (.const (toKername con)) (pre₀ ++ disc₀ :: minors₀ ++ []))
        (LBTerm.mkApps (.case (iid, np) disc alts) []) :=
      Lower.elimApp' (Γ := Γ) (kn := toKername con) (iid := iid) (np := np)
        (dp := dp) (nfs := nfs) (pre := pre₀) (disc := disc₀) (disc' := disc)
        (minors := minors₀) (alts := alts) (extra := []) (extra' := [])
        hE (by omega)
        ⟨by omega, halen, fun i hi => (hnpt i (by omega)).2⟩ hdlow rfl
        (fun i hi => absurd hi (by simp))
    simpa using hstep

/-! ## `ConstToFVar` as a congruence

The block rewriting commutes with the spine operator the composite's introduction lemmas
build their targets out of. `ConstToFVar.shift`, `.mkLambdas` and `.bvarsDesc` are deleted
with the two `*_eta` twins, the only consumers of a λ-telescope target. -/

/-- Block rewriting is a congruence over an application spine. -/
theorem ConstToFVar.mkApps {kns : List Kername} {ids : List FVarId} {f f' : LBTerm}
    (hf : ConstToFVar kns ids f f') {l l' : List LBTerm} (hlen : l'.length = l.length)
    (h : ∀ i, i < l.length → ConstToFVar kns ids l[i]! l'[i]!) :
    ConstToFVar kns ids (LBTerm.mkApps f l) (LBTerm.mkApps f' l') := by
  induction l generalizing f f' l' with
  | nil =>
      have : l' = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst this; exact hf
  | cons x xs ih =>
      obtain ⟨y, ys, rfl⟩ : ∃ y ys, l' = y :: ys := by
        rcases l' with _ | ⟨y, ys⟩
        · simp at hlen
        · exact ⟨y, ys, rfl⟩
      have hlen' : ys.length = xs.length := by simpa using hlen
      have hx : ConstToFVar kns ids x y := by
        have h0 := h 0 (by simp)
        rwa [getElem!_pos (x :: xs) 0 (by simp), getElem!_pos (y :: ys) 0 (by simp)] at h0
      refine ih (.app hf hx) hlen' ?_
      intro i hi
      have hi' := h (i + 1) (by simp only [List.length_cons]; omega)
      rwa [getElem!_pos (x :: xs) (i + 1) (by simp only [List.length_cons]; omega),
        getElem!_pos (y :: ys) (i + 1) (by simp only [List.length_cons]; omega),
        List.getElem_cons_succ, List.getElem_cons_succ,
        ← getElem!_pos xs i hi, ← getElem!_pos ys i (by omega)] at hi'

/-! ## The block twins

Inside a mutual block the eraser rewrites the block's own constants to its fix variables,
so each introduction lemma has a twin concluding `ErasesLBFix` (`LowerFix.lean`). The twins
are the composites post-composed with `ConstToFVar`, plus `fixvar`, the one step that has no
`ErasesLB` counterpart.
-/

variable {kns : List Kername} {ids : List FVarId}

/-- Post-composition: a composite whose image the block rewriting sends to `t`. -/
theorem ErasesLBFix.of_erasesLB {e : Expr} {t₁ t : LBTerm}
    (h : ErasesLB env Us Γ Δ e t₁) (hc : ConstToFVar kns ids t₁ t) :
    ErasesLBFix env Us Γ kns ids Δ e t :=
  let ⟨t₀, h₀, h₁⟩ := h
  ⟨t₀, t₁, h₀, h₁, hc⟩

/-- The two factors, read apart again. -/
theorem ErasesLBFix.exists_erasesLB {e : Expr} {t : LBTerm}
    (h : ErasesLBFix env Us Γ kns ids Δ e t) :
    ∃ t₁, ErasesLB env Us Γ Δ e t₁ ∧ ConstToFVar kns ids t₁ t :=
  let ⟨t₀, t₁, h₀, h₁, hc⟩ := h
  ⟨t₁, ⟨t₀, h₀, h₁⟩, hc⟩

/-- The middle list of a spine of block composites. -/
theorem ErasesLBFix.exists_mid {args : List Expr} {args' : List LBTerm}
    (ha : ∀ i, i < args.length → ErasesLBFix env Us Γ kns ids Δ args[i]! args'[i]!) :
    ∃ mid : List LBTerm, mid.length = args.length ∧
      (∀ i, i < args.length → ErasesLB env Us Γ Δ args[i]! mid[i]!) ∧
      (∀ i, i < args.length → ConstToFVar kns ids mid[i]! args'[i]!) := by
  obtain ⟨mid, hlen, hpt⟩ :=
    exists_list_of_index args.length
      (fun i m => ErasesLB env Us Γ Δ args[i]! m ∧ ConstToFVar kns ids m args'[i]!)
      (fun i hi => (ha i hi).exists_erasesLB)
  exact ⟨mid, hlen, fun i hi => (hpt i hi).1, fun i hi => (hpt i hi).2⟩

/-- A reference to one of the block's own names becomes that member's fix variable: the one
step of the block branch neither `Erases` nor `Lower` states. -/
theorem ErasesLBFix.fixvar {cn : Name} {us : List Level} {ci : VConstant} {j : Nat}
    {x : FVarId} (hkn : kns[j]? = some (toKername cn)) (hx : ids[j]? = some x)
    (hnr : ¬ RuntimeKey Γ (toKername cn)) (h : env.constants cn = some ci)
    (ho : ConstOrigin env cn) :
    ErasesLBFix env Us Γ kns ids Δ (.const cn us) (.fvar x) :=
  ⟨.const (toKername cn), .const (toKername cn), .const h ho, .const hnr, .hit hkn hx⟩

/-- `ErasesLB.box` inside a block. -/
theorem ErasesLBFix.box {e : Expr} {ve : VExpr} (htr : TrExprS env Us Δ e ve)
    (her : Erasable env Us.length Δ.toCtx ve) : ErasesLBFix env Us Γ kns ids Δ e .box :=
  .of_erasesLB (ErasesLB.box htr her) .box

/-- `ErasesLB.app` inside a block. -/
theorem ErasesLBFix.app {f a : Expr} {f' a' : LBTerm}
    (hf : ErasesLBFix env Us Γ kns ids Δ f f')
    (ha : ErasesLBFix env Us Γ kns ids Δ a a') :
    ErasesLBFix env Us Γ kns ids Δ (.app f a) (.app f' a') :=
  let ⟨_, hf₁, hfc⟩ := hf.exists_erasesLB
  let ⟨_, ha₁, hac⟩ := ha.exists_erasesLB
  .of_erasesLB (ErasesLB.app hf₁ ha₁) (.app hfc hac)

/-- `ErasesLB.ctor_head` inside a block. -/
theorem ErasesLBFix.ctor_head {cn I : Name} {us : List Level} {iid : InductiveId}
    {k np : Nat} {nfs : List Nat} (hc : CtorOf env cn I k)
    (hi : IndInfo env I iid np nfs) :
    ErasesLBFix env Us Γ kns ids Δ (.const cn us) (.construct iid k []) :=
  .of_erasesLB (ErasesLB.ctor_head hc hi)
    (.construct rfl (fun i hi => absurd hi (by simp)))

/-- `ErasesLB.ctor` inside a block. -/
theorem ErasesLBFix.ctor {cn I : Name} {us : List Level} {iid : InductiveId}
    {k np : Nat} {nfs : List Nat} {args : List Expr} {args' : List LBTerm}
    (hc : CtorOf env cn I k) (hi : IndInfo env I iid np nfs)
    (hlen : args'.length = args.length)
    (ha : ∀ i, i < args.length → ErasesLBFix env Us Γ kns ids Δ args[i]! args'[i]!) :
    ErasesLBFix env Us Γ kns ids Δ (args.foldl Expr.app (.const cn us))
      (LBTerm.mkApps (.construct iid k []) args') := by
  obtain ⟨mid, hmlen, hlb, hct⟩ := ErasesLBFix.exists_mid ha
  exact .of_erasesLB (ErasesLB.ctor hc hi hmlen hlb)
    (ConstToFVar.mkApps (.construct rfl (fun i hi => absurd hi (by simp)))
      (by omega) (fun i hi => hct i (by omega)))

/-- `ErasesLB.lit` inside a block. -/
theorem ErasesLBFix.lit {l : Literal} {t : LBTerm} (hcl : env.ContainsLits l)
    (h : ErasesLBFix env Us Γ kns ids Δ l.toConstructor t) :
    ErasesLBFix env Us Γ kns ids Δ (.lit l) t :=
  let ⟨_, h₁, hc⟩ := h.exists_erasesLB
  .of_erasesLB (ErasesLB.lit hcl h₁) hc

/-- `ErasesLB.proj` inside a block. -/
theorem ErasesLBFix.proj {S : Name} {i : Nat} {e : Expr} {t : LBTerm} {iid : InductiveId}
    {np nf : Nat} (hs : IndInfo env S iid np [nf]) (hinf : InformativeInd env S) (hi : i < nf)
    (hd : ErasesLBFix env Us Γ kns ids Δ e t) :
    ErasesLBFix env Us Γ kns ids Δ (.proj S i e) (.proj ⟨iid, np, i⟩ t) :=
  let ⟨_, h₁, hc⟩ := hd.exists_erasesLB
  .of_erasesLB (ErasesLB.proj hs hinf hi h₁) (.proj hc)

/-- `ErasesLB.cases` inside a block. -/
theorem ErasesLBFix.cases {con : Name} {us : List Level} {ci : VConstant}
    {iid : InductiveId} {np dp : Nat} {nfs : List Nat} {args : List Expr}
    {disc : LBTerm} {alts : List (List BinderName × LBTerm)}
    (hE : ElimDecl Γ (toKername con) iid np dp nfs) (hcst : env.constants con = some ci)
    (hco : ConstOrigin env con) (henv : env.WF)
    (hclass : ∀ c ci, env.constants c = some ci → (∃ I k, CtorOf env c I k) ∨
      (∃ iid np nfs, IndInfo env c iid np nfs) ∨ ConstOrigin env c)
    (hΔ : VLCtx.WF env Us.length Δ)
    (hpre : ∀ a ∈ args.take dp, ∃ ve, TrExprS env Us Δ a ve)
    (hppi : ∀ a ∈ args.take dp, ProjInfo env a)
    (hlen : args.length = dp + 1 + nfs.length)
    (hd : ErasesLBFix env Us Γ kns ids Δ args[dp]! disc)
    (hm : ErasesLBFixAlts env Us Γ kns ids Δ nfs (args.drop (dp + 1)) alts) :
    ErasesLBFix env Us Γ kns ids Δ (args.foldl Expr.app (.const con us))
      (.case (iid, np) disc alts) := by
  obtain ⟨hmlen, halen, halts⟩ := hm
  obtain ⟨disc₁, hdlb, hdct⟩ := hd.exists_erasesLB
  obtain ⟨alts₁, halen₁, hapt⟩ :=
    exists_list_of_index nfs.length
      (fun i a => ErasesLBAlt env Us Γ Δ nfs[i]! (args.drop (dp + 1))[i]! a ∧
        (alts[i]!).1.length = a.1.length ∧ ConstToFVar kns ids a.2 (alts[i]!).2)
      halts
  refine .of_erasesLB
    (ErasesLB.cases hE hcst hco henv hclass hΔ hpre hppi hlen hdlb
      ⟨hmlen, halen₁, fun i hi => (hapt i hi).1⟩) ?_
  exact .case hdct (by omega) (fun i hi => (hapt i (by omega)).2.1)
    (fun i hi => (hapt i (by omega)).2.2)

/-- `ErasesLB.fix` inside a block: the `.fix` node of an inner block, which the outer
block's rewriting leaves alone. -/
theorem ErasesLBFix.fix {cn : Name} {us : List Level} {ci : VConstant}
    {bkns : List Kername} {bs bs' : List LBTerm} {bids : List FVarId}
    {defs : List (@FixDef LBTerm)} {j : Nat}
    (hblk : LowerBlock Γ bkns bs bs' bids defs) (hnk : ¬ RuntimeKey Γ (toKername cn))
    (hj : bkns[j]? = some (toKername cn)) (h : env.constants cn = some ci)
    (ho : ConstOrigin env cn) :
    ErasesLBFix env Us Γ kns ids Δ (.const cn us) (.fix defs j) :=
  .of_erasesLB (ErasesLB.fix hblk hnk hj h ho) (.fix defs j)

/-! ## The spine premise, folded -/

set_option linter.unusedVariables false in
/-- A spine premise written as `Erases` and `Lower` side by side is the spine premise
written with the composite. `hlen` is the length equation `Lower.mkApps` consumes; it
constrains neither side. -/
theorem erasesLB_of_spine {args : List Expr} {targs : List LBTerm}
    (hlen : targs.length = args.length) :
    (∀ i, i < args.length → ∃ a₀, Erases env Us Δ args[i]! a₀ ∧ Lower Γ a₀ targs[i]!) ↔
      (∀ i, i < args.length → ErasesLB env Us Γ Δ args[i]! targs[i]!) :=
  Iff.rfl

end LeanToLambdaBox
