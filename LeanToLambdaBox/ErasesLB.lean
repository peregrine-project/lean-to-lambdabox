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
* Eight introduction lemmas — `box`, `app`, `ctor_head`, `ctor`, `ctor_eta`, `cases`,
  `cases_eta`, `fix` — each taking the source-level data of one compilation step.
* Their `ErasesLBFix.*` twins, the same steps inside a mutual block, where the emitted term
  carries the block's fix variables (`LowerFix.lean`'s `ErasesLBFix = ErasesLB ⨟ ConstToFVar`),
  plus `ErasesLBFix.fixvar`, the block branch's own step, which has no `ErasesLB` counterpart.
* `erasesLB_of_spine`, which reads a spine premise written as `Erases` and `Lower` side by
  side as one `ErasesLB` premise.

`ErasesLB.ctor_head` and `ErasesLB.cases` carry premises `doc/rework/01-DESIGN.md` §4.7 does
not print; their docstrings say which and why, and `ErasesLB.ctor_head_needs_nullary` shows
`ctor_head`'s added premise necessary.
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

/--
A bare constructor constant composes to the empty constructor node, provided the
constructor takes no argument.

`hnul` is not in `doc/rework/01-DESIGN.md` §4.7's printed signature and is load-bearing:
`Lower` sends a constructor constant of positive arity to an η-expanded λ, never to a
`.construct` node (`ErasesLB.ctor_head_needs_nullary`).
-/
theorem ErasesLB.ctor_head {cn : Name} {us : List Level} {ci : VConstant}
    {iid : InductiveId} {k : Nat} (hc : CtorDecl Γ (toKername cn) iid k)
    (hnul : cstrArity Γ iid k = 0) (h : env.constants cn = some ci) :
    ErasesLB env Us Γ Δ (.const cn us) (.construct iid k []) :=
  ⟨.const (toKername cn), .const h,
    Lower.ctorApp (args := []) (args' := []) hc (by simp [hnul]) rfl (fun i hi => absurd hi (by simp))⟩

/-- A saturated or over-applied constructor spine composes to the applied constructor
node. `hsat` is `Lower.ctorApp`'s own dispatch guard, and `hcst` is the erasure factor's:
the head is a declared constant. -/
theorem ErasesLB.ctor {cn : Name} {us : List Level} {ci : VConstant}
    {iid : InductiveId} {k : Nat} {args : List Expr} {args' : List LBTerm}
    (hc : CtorDecl Γ (toKername cn) iid k) (hcst : env.constants cn = some ci)
    (hsat : args.length ≥ cstrArity Γ iid k) (hlen : args'.length = args.length)
    (ha : ∀ i, i < args.length → ErasesLB env Us Γ Δ args[i]! args'[i]!) :
    ErasesLB env Us Γ Δ (args.foldl Expr.app (.const cn us))
      (LBTerm.mkApps (.construct iid k []) args') := by
  obtain ⟨mid, hmlen, herm, hlowm⟩ := ErasesLB.exists_mid ha
  refine ⟨LBTerm.mkApps (.const (toKername cn)) mid, ?_, ?_⟩
  · rw [← mkApps_eq_foldl]
    exact Erases.mkApps args mid (.const hcst) hmlen herm
  · exact Lower.ctorApp hc (by omega) (by omega) (fun i hi => hlowm i (by omega))

/-- An under-applied constructor spine composes to the η-expanded constructor node: `ns`
fresh binders saturate it, and `shift ns.length 0` moves the lowered prefix under them. -/
theorem ErasesLB.ctor_eta {cn : Name} {us : List Level} {ci : VConstant}
    {iid : InductiveId} {k : Nat} {args : List Expr} {args' : List LBTerm}
    {ns : List BinderName}
    (hc : CtorDecl Γ (toKername cn) iid k) (hcst : env.constants cn = some ci)
    (hns : ns ≠ []) (hund : args.length + ns.length = cstrArity Γ iid k)
    (hlen : args'.length = args.length)
    (ha : ∀ i, i < args.length → ErasesLB env Us Γ Δ args[i]! args'[i]!) :
    ErasesLB env Us Γ Δ (args.foldl Expr.app (.const cn us))
      (mkLambdas ns (LBTerm.mkApps (.construct iid k [])
        ((args'.map (LBTerm.shift ns.length 0)) ++ bvarsDesc ns.length))) := by
  obtain ⟨mid, hmlen, herm, hlowm⟩ := ErasesLB.exists_mid ha
  refine ⟨LBTerm.mkApps (.const (toKername cn)) mid, ?_, ?_⟩
  · rw [← mkApps_eq_foldl]
    exact Erases.mkApps args mid (.const hcst) hmlen herm
  · exact Lower.ctorEta hc hns (by omega) (by omega) (fun i hi => hlowm i (by omega))

/-- A block member's constant composes to the block's `.fix` node. -/
theorem ErasesLB.fix {cn : Name} {us : List Level} {ci : VConstant} {kns : List Kername}
    {bs bs' : List LBTerm} {ids : List FVarId} {defs : List (@FixDef LBTerm)} {j : Nat}
    (hblk : LowerBlock Γ kns bs bs' ids defs) (hj : kns[j]? = some (toKername cn))
    (h : env.constants cn = some ci) : ErasesLB env Us Γ Δ (.const cn us) (.fix defs j) :=
  ⟨.const (toKername cn), .const h, Lower.fixConst' hblk hj⟩


/--
A saturated eliminator spine composes to a `.case` node: the `dp` arguments before the
discriminant are dropped, and the minors become the alternatives.

`hpre` and `hppi` are not in `doc/rework/01-DESIGN.md` §4.7's printed signature in this
form: the dropped arguments still need an erasure image, since `Erases` is a congruence
over the whole spine, and `Erases.exists_of_trExprS_of_projInfo` supplies one only under a
`ProjInfo` side premise. `hlen` pins the spine to the node's own arity.
-/
theorem ErasesLB.cases {con : Name} {us : List Level} {ci : VConstant}
    {iid : InductiveId} {np dp : Nat} {nfs : List Nat} {args : List Expr}
    {disc : LBTerm} {alts : List (List BinderName × LBTerm)}
    (hE : ElimDecl Γ (toKername con) iid np dp nfs) (hcst : env.constants con = some ci)
    (henv : env.WF) (hΔ : VLCtx.WF env Us.length Δ)
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
        exact Erases.exists_of_trExprS_of_projInfo henv hΔ (hppi _ (Lower.getElem!_mem hi)) hve)
  obtain ⟨minors₀, hnlen, hnpt⟩ :=
    exists_list_of_index (args.drop (dp + 1)).length
      (fun i b => Erases env Us Δ (args.drop (dp + 1))[i]! b ∧
        LowerAlt Γ nfs[i]! b alts[i]!)
      (fun i hi => halts i (by omega))
  refine ⟨LBTerm.mkApps (.const (toKername con)) (pre₀ ++ disc₀ :: minors₀), ?_, ?_⟩
  · have hspine := Erases.mkApps (f := Expr.const con us)
      (args.take dp ++ args[dp]! :: args.drop (dp + 1)) (pre₀ ++ disc₀ :: minors₀)
      (.const hcst) (by simp [hplen, hnlen])
      (forall_index_append hplen (by simp [hnlen]) hperase
        (forall_index_cons hderase (fun i hi => (hnpt i hi).1)))
    rw [← hsplit] at hspine
    rw [← mkApps_eq_foldl]
    exact hspine
  · have hstep : Lower Γ
        (LBTerm.mkApps (.const (toKername con)) (pre₀ ++ disc₀ :: minors₀ ++ []))
        (LBTerm.mkApps (.case (iid, np) disc alts) []) :=
      Lower.elimApp' (Γ := Γ) (hd := .const (toKername con)) (iid := iid) (np := np)
        (dp := dp) (nfs := nfs) (pre := pre₀) (disc := disc₀) (disc' := disc)
        (minors := minors₀) (alts := alts) (extra := []) (extra' := [])
        (.inl ⟨_, rfl, hE⟩) (by omega)
        ⟨by omega, halen, fun i hi => (hnpt i (by omega)).2⟩ hdlow rfl
        (fun i hi => absurd hi (by simp))
    simpa using hstep

/-- An under-applied eliminator spine composes to the η-expanded `.case` node: `ns` fresh
binders saturate the spine, and `hsat` lowers the saturated spine. The spine's erasure
image `args₀` is explicit because the added binders have no source counterpart. -/
theorem ErasesLB.cases_eta {con : Name} {us : List Level} {ci : VConstant}
    {iid : InductiveId} {np dp : Nat} {nfs : List Nat} {args : List Expr}
    {args₀ : List LBTerm} {ns : List BinderName} {body : LBTerm}
    (hE : ElimDecl Γ (toKername con) iid np dp nfs) (hcst : env.constants con = some ci)
    (hns : ns ≠ []) (hund : args.length + ns.length = dp + 1 + nfs.length)
    (hlen : args₀.length = args.length)
    (ha : ∀ i, i < args.length → Erases env Us Δ args[i]! args₀[i]!)
    (hsat : Lower Γ (LBTerm.mkApps (.const (toKername con))
      ((args₀.map (LBTerm.shift ns.length 0)) ++ bvarsDesc ns.length)) body) :
    ErasesLB env Us Γ Δ (args.foldl Expr.app (.const con us)) (mkLambdas ns body) :=
  ⟨LBTerm.mkApps (.const (toKername con)) args₀,
    by rw [← mkApps_eq_foldl]; exact Erases.mkApps args args₀ (.const hcst) hlen ha,
    Lower.elimEta (.inl ⟨_, rfl, hE⟩) hns (by omega) hsat⟩


/-! ## Why `ctor_head` is nullary -/

/-- The empty constructor node is reachable from a constructor constant only at arity
zero: at any other arity the pass η-expands, and `Lower` relates no `.const` to a
`.construct` node otherwise. This is `ErasesLB.ctor_head`'s `hnul` shown necessary. -/
theorem ErasesLB.ctor_head_needs_nullary {cn : Name} {us : List Level}
    {iid : InductiveId} {k : Nat}
    (h : ErasesLB env Us Γ Δ (.const cn us) (.construct iid k [])) :
    CtorDecl Γ (toKername cn) iid k ∧ cstrArity Γ iid k = 0 := by
  obtain ⟨t₀, her, hlow⟩ := h
  rcases Erases.const_inv her with ⟨_, rfl⟩ | ⟨_, rfl⟩
  · rcases Lower.target_construct hlow rfl with ⟨_, hs, _⟩ | ⟨_, hs, _⟩ <;>
      exact LBTerm.noConfusion hs
  · rcases Lower.target_construct hlow rfl with ⟨_, hs, _⟩ | ⟨kn, hs, hc, _, hnul⟩
    · exact LBTerm.noConfusion hs
    · injection hs with hkn
      subst hkn
      exact ⟨hc, hnul⟩

/-! ## `ConstToFVar` as a congruence

The block rewriting commutes with the operators the η arms build their targets out of. -/

/-- Block rewriting commutes with `shift`: it reads no de Bruijn index, and a `.fix` node
maps to itself at every cutoff. -/
theorem ConstToFVar.shift {kns : List Kername} {ids : List FVarId} {t u : LBTerm}
    (h : ConstToFVar kns ids t u) :
    ∀ d c, ConstToFVar kns ids (LBTerm.shift d c t) (LBTerm.shift d c u) := by
  induction h with
  | box => exact fun _ _ => .box
  | bvar i => intro d c; simp only [LBTerm.shift]; split <;> exact .bvar _
  | fvar x => exact fun _ _ => .fvar x
  | prim p => exact fun _ _ => .prim p
  | hit hkn hx => exact fun _ _ => .hit hkn hx
  | miss hk => exact fun _ _ => .miss hk
  | lambda _ ih => exact fun d c => .lambda (ih d (c + 1))
  | letIn _ _ ihv ihb => exact fun d c => .letIn (ihv d c) (ihb d (c + 1))
  | app _ _ ihf iha => exact fun d c => .app (ihf d c) (iha d c)
  | proj _ ih => exact fun d c => .proj (ih d c)
  | @construct iid k args args' hlen _ ih =>
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
        rw [Lower.getElem!_map (fun a : List BinderName × LBTerm =>
              (a.1, LBTerm.shift d (c + a.1.length) a.2)) alts' i (by omega),
          Lower.getElem!_map (fun a : List BinderName × LBTerm =>
              (a.1, LBTerm.shift d (c + a.1.length) a.2)) alts i hi]
        exact hn i hi
      · intro i hi
        rw [List.length_map] at hi
        rw [Lower.getElem!_map (fun a : List BinderName × LBTerm =>
              (a.1, LBTerm.shift d (c + a.1.length) a.2)) alts' i (by omega),
          Lower.getElem!_map (fun a : List BinderName × LBTerm =>
              (a.1, LBTerm.shift d (c + a.1.length) a.2)) alts i hi]
        rw [hn i hi]
        exact ihb i hi d (c + (alts[i]!).1.length)
  | fix defs i => intro d c; simp only [LBTerm.shift]; exact .fix _ _

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

/-- Block rewriting is a congruence under a lambda telescope. -/
theorem ConstToFVar.mkLambdas {kns : List Kername} {ids : List FVarId}
    (ns : List BinderName) {b b' : LBTerm} (h : ConstToFVar kns ids b b') :
    ConstToFVar kns ids (mkLambdas ns b) (mkLambdas ns b') := by
  induction ns with
  | nil => exact h
  | cons n ns ih => exact .lambda ih

/-- An η-expansion's own arguments are de Bruijn indices, which block rewriting fixes. -/
theorem ConstToFVar.bvarsDesc {kns : List Kername} {ids : List FVarId} (n : Nat) :
    ∀ i, i < (bvarsDesc n).length →
      ConstToFVar kns ids (bvarsDesc n)[i]! (bvarsDesc n)[i]! := by
  intro i hi
  obtain ⟨m, _, hm⟩ := bvarsDesc_mem (Lower.getElem!_mem hi)
  rw [hm]; exact .bvar m


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
    (hnr : ¬ RuntimeKey Γ (toKername cn)) (h : env.constants cn = some ci) :
    ErasesLBFix env Us Γ kns ids Δ (.const cn us) (.fvar x) :=
  ⟨.const (toKername cn), .const (toKername cn), .const h, .const hnr, .hit hkn hx⟩

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
theorem ErasesLBFix.ctor_head {cn : Name} {us : List Level} {ci : VConstant}
    {iid : InductiveId} {k : Nat} (hc : CtorDecl Γ (toKername cn) iid k)
    (hnul : cstrArity Γ iid k = 0) (h : env.constants cn = some ci) :
    ErasesLBFix env Us Γ kns ids Δ (.const cn us) (.construct iid k []) :=
  .of_erasesLB (ErasesLB.ctor_head hc hnul h)
    (.construct rfl (fun i hi => absurd hi (by simp)))

/-- `ErasesLB.ctor` inside a block. -/
theorem ErasesLBFix.ctor {cn : Name} {us : List Level} {ci : VConstant}
    {iid : InductiveId} {k : Nat} {args : List Expr} {args' : List LBTerm}
    (hc : CtorDecl Γ (toKername cn) iid k) (hcst : env.constants cn = some ci)
    (hsat : args.length ≥ cstrArity Γ iid k) (hlen : args'.length = args.length)
    (ha : ∀ i, i < args.length → ErasesLBFix env Us Γ kns ids Δ args[i]! args'[i]!) :
    ErasesLBFix env Us Γ kns ids Δ (args.foldl Expr.app (.const cn us))
      (LBTerm.mkApps (.construct iid k []) args') := by
  obtain ⟨mid, hmlen, hlb, hct⟩ := ErasesLBFix.exists_mid ha
  exact .of_erasesLB (ErasesLB.ctor hc hcst hsat hmlen hlb)
    (ConstToFVar.mkApps (.construct rfl (fun i hi => absurd hi (by simp)))
      (by omega) (fun i hi => hct i (by omega)))

/-- `ErasesLB.ctor_eta` inside a block. -/
theorem ErasesLBFix.ctor_eta {cn : Name} {us : List Level} {ci : VConstant}
    {iid : InductiveId} {k : Nat} {args : List Expr} {args' : List LBTerm}
    {ns : List BinderName}
    (hc : CtorDecl Γ (toKername cn) iid k) (hcst : env.constants cn = some ci)
    (hns : ns ≠ []) (hund : args.length + ns.length = cstrArity Γ iid k)
    (hlen : args'.length = args.length)
    (ha : ∀ i, i < args.length → ErasesLBFix env Us Γ kns ids Δ args[i]! args'[i]!) :
    ErasesLBFix env Us Γ kns ids Δ (args.foldl Expr.app (.const cn us))
      (mkLambdas ns (LBTerm.mkApps (.construct iid k [])
        ((args'.map (LBTerm.shift ns.length 0)) ++ bvarsDesc ns.length))) := by
  obtain ⟨mid, hmlen, hlb, hct⟩ := ErasesLBFix.exists_mid ha
  refine .of_erasesLB (ErasesLB.ctor_eta hc hcst hns hund hmlen hlb)
    (ConstToFVar.mkLambdas ns (ConstToFVar.mkApps
      (.construct rfl (fun i hi => absurd hi (by simp))) (by simp; omega) ?_))
  refine forall_index_append (by simp; omega) (by simp) ?_ (ConstToFVar.bvarsDesc _)
  intro i hi
  rw [List.length_map] at hi
  rw [Lower.getElem!_map _ _ i hi, Lower.getElem!_map _ _ i (by omega)]
  exact ConstToFVar.shift (hct i (by omega)) _ _

/-- `ErasesLB.cases` inside a block. -/
theorem ErasesLBFix.cases {con : Name} {us : List Level} {ci : VConstant}
    {iid : InductiveId} {np dp : Nat} {nfs : List Nat} {args : List Expr}
    {disc : LBTerm} {alts : List (List BinderName × LBTerm)}
    (hE : ElimDecl Γ (toKername con) iid np dp nfs) (hcst : env.constants con = some ci)
    (henv : env.WF) (hΔ : VLCtx.WF env Us.length Δ)
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
    (ErasesLB.cases hE hcst henv hΔ hpre hppi hlen hdlb
      ⟨hmlen, halen₁, fun i hi => (hapt i hi).1⟩) ?_
  exact .case hdct (by omega) (fun i hi => (hapt i (by omega)).2.1)
    (fun i hi => (hapt i (by omega)).2.2)

/-- `ErasesLB.cases_eta` inside a block. -/
theorem ErasesLBFix.cases_eta {con : Name} {us : List Level} {ci : VConstant}
    {iid : InductiveId} {np dp : Nat} {nfs : List Nat} {args : List Expr}
    {args₀ : List LBTerm} {ns : List BinderName} {body body' : LBTerm}
    (hE : ElimDecl Γ (toKername con) iid np dp nfs) (hcst : env.constants con = some ci)
    (hns : ns ≠ []) (hund : args.length + ns.length = dp + 1 + nfs.length)
    (hlen : args₀.length = args.length)
    (ha : ∀ i, i < args.length → Erases env Us Δ args[i]! args₀[i]!)
    (hsat : Lower Γ (LBTerm.mkApps (.const (toKername con))
      ((args₀.map (LBTerm.shift ns.length 0)) ++ bvarsDesc ns.length)) body)
    (hct : ConstToFVar kns ids body body') :
    ErasesLBFix env Us Γ kns ids Δ (args.foldl Expr.app (.const con us))
      (mkLambdas ns body') :=
  .of_erasesLB (ErasesLB.cases_eta hE hcst hns hund hlen ha hsat)
    (ConstToFVar.mkLambdas ns hct)

/-- `ErasesLB.fix` inside a block: the `.fix` node of an inner block, which the outer
block's rewriting leaves alone. -/
theorem ErasesLBFix.fix {cn : Name} {us : List Level} {ci : VConstant}
    {bkns : List Kername} {bs bs' : List LBTerm} {bids : List FVarId}
    {defs : List (@FixDef LBTerm)} {j : Nat}
    (hblk : LowerBlock Γ bkns bs bs' bids defs) (hj : bkns[j]? = some (toKername cn))
    (h : env.constants cn = some ci) :
    ErasesLBFix env Us Γ kns ids Δ (.const cn us) (.fix defs j) :=
  .of_erasesLB (ErasesLB.fix hblk hj h) (.fix defs j)

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
