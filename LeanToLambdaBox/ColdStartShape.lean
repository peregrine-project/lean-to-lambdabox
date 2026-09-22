import LeanToLambdaBox.ErasesAbstract
import LeanToLambdaBox.ErasesEnv
import LeanToLambdaBox.ErasureRun

/-!
# The cold-start registry invariant

`RegInvShape' env bo lp Γspec s` is what a run of the erasure's *registration* path maintains
between a fixed specification environment `Γspec` and the state `s` it has built so far: the
specification environment is well formed and its entries say of the source what `SpecContent`
asks, everything the run has registered is covered by it, and the emitted `s.gdecls` is its
lowered, pruned image as far as the run has got.

`Γspec` does not grow with the state. The pass relation `Lower Γ` is not monotone in `Γ` — the
`fixConst` arm's `¬ RuntimeKey Γ` guard is negative, and declaring a block can turn a key into
a runtime key — so a specification environment built entry by entry alongside the run would
strand every `Lower` fact it had already recorded. Reading one fixed `Γspec` at every state is
the same universally-quantified, antitone reading `SpecEnv.mono` takes.

The state-facing clauses are *scoped* to what the run has registered: `defsTotal` and
`indsEmitted` quantify over the registries, not over `Γspec`, so they hold vacuously at the
empty state and collapse to `LowerEnv`'s unscoped clauses under the saturation premises
`SpecEnv.lean` names. Key *coverage* is maintainable at every registration site; key
*distinctness* is not maintainable unconditionally — every writer prepends and `envLookup` is
first-match-wins — so each step lemma takes the freshness it needs as a side condition.

`Γspec`'s own content is one field, `spec`, fixed for the run and copied by every step: it
is what `ErasesEnv`'s five source-facing clauses read, with the entry's presence in place of
the program's reachability.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean Erasure

/-! ## Lookup and registry plumbing across one registration step -/

/-- An established lookup survives a cons whose key is fresh for the list. -/
theorem envLookup_cons_of_fresh {E : GlobalDeclarations} {k kn : Kername} {d d' : GlobalDecl}
    (hfresh : ∀ q ∈ E, q.1 ≠ k) (h : LBTerm.envLookup E kn = some d') :
    LBTerm.envLookup ((k, d) :: E) kn = some d' :=
  (envLookup_cons_ne (fun hkn => hfresh _ (envLookup_mem h) hkn.symm)).trans h

/-- A lookup that missed the consed entry is a lookup of the tail. -/
theorem envLookup_of_cons_ne {E : GlobalDeclarations} {k kn : Kername} {d d' : GlobalDecl}
    (hne : k ≠ kn) (h : LBTerm.envLookup ((k, d) :: E) kn = some d') :
    LBTerm.envLookup E kn = some d' := by
  rwa [envLookup_cons_ne hne] at h

/-- A fresh key is not among the keys of the list. -/
theorem not_mem_keys_of_fresh {E : GlobalDeclarations} {k : Kername}
    (hfresh : ∀ q ∈ E, q.1 ≠ k) : k ∉ E.map Prod.fst := by
  intro hk
  obtain ⟨q, hq, hqk⟩ := List.mem_map.mp hk
  exact hfresh q hq hqk

/-- The key just inserted is known. -/
theorem constants_isSome_insert_self (mp : Std.HashMap Name Kername) (n : Name)
    (k : Kername) : ((mp.insert n k).get? n).isSome := by
  rw [Std.HashMap.get?_insert]; simp

/-- Insertion does not forget. -/
theorem constants_isSome_insert {mp : Std.HashMap Name Kername} {n m : Name} {k : Kername}
    (h : (mp.get? m).isSome) : ((mp.insert n k).get? m).isSome := by
  rw [Std.HashMap.get?_insert]
  split
  · simp
  · exact h

/-- An inserted key is the inserted name's or was known before. -/
theorem constants_insert_cases {mp : Std.HashMap Name Kername} {n m : Name} {k : Kername}
    (h : ((mp.insert n k).get? m).isSome) : m = n ∨ (mp.get? m).isSome := by
  rw [Std.HashMap.get?_insert] at h
  split at h
  · rename_i hb; refine .inl ?_; have : n = m := by simpa using hb
    exact this.symm
  · exact .inr h

/-! ## Coverage of one inductive

`IndCovered` is `ErasesEnv.lean`'s, beside the relation whose two inductive clauses it is.
-/

/-- The block `Γspec` holds for `n` is the block the run emitted. `LowerEnv.inds` at one
registered name: blocks are carried over unchanged, since the target reads the parameter count
and the field counts off them. -/
def IndEmitted (env : VEnv) (Γspec Γ : GlobalDeclarations) (n : Name) : Prop :=
  ∀ iid np nfs, IndInfo env n iid np nfs → ∀ d,
    LBTerm.envLookup Γspec iid.mutualBlockName = some (.inductiveDecl d) →
    LBTerm.envLookup Γ iid.mutualBlockName = some (.inductiveDecl d)

/-! ## The erasure image mentions no free variable

`SpecContent.defns` records each declared body as an erasure at the **empty** local context,
and `Erases` emits an `.fvar` only through `Erases.fvar`, whose lookup premise no empty
context answers. That is what pays `RegInvShape'.specFVarFree` wherever the invariant is
inhabited. -/

/-- The `.vlam`/`.vlet` extensions the binder arms take add no free variable to the context. -/
theorem VLCtx.find?_inr_cons_none {Δ : VLCtx} {d : VLocalDecl}
    (h : ∀ y : FVarId, Δ.find? (.inr y) = none) :
    ∀ y : FVarId, VLCtx.find? ((none, d) :: Δ) (.inr y) = none := by
  intro y
  simp [VLCtx.find?, VLCtx.next, h y]

/-- **The erasure image over a context binding no free variable has none either.** The `fvar`
arm is the only producer of an `.fvar` node and its lookup premise is unsatisfiable there. -/
theorem Erases.noFVar_of_noFVars {env : VEnv} {Us : List Name} {Δ : VLCtx} {e : Expr}
    {t : LBTerm} (h : Erases env Us Δ e t) :
    ∀ {x : FVarId}, (∀ y : FVarId, Δ.find? (.inr y) = none) → ¬ hasFVar x t := by
  induction h with
  | box | bvar => exact fun _ hc => hc.elim
  | @fvar Δ z e' A hz => exact fun hΔ _ => absurd hz (by rw [hΔ z]; simp)
  | ctor => exact fun _ hc => hc.elim
  | const => exact fun _ hc => hc.elim
  | app _ _ ihf iha =>
      intro x hΔ hc
      exact hc.elim (ihf hΔ) (iha hΔ)
  | lam _ _ ih => exact fun hΔ => ih (VLCtx.find?_inr_cons_none hΔ)
  | letE _ _ _ _ ihv ihb =>
      intro x hΔ hc
      exact hc.elim (ihv hΔ) (ihb (VLCtx.find?_inr_cons_none hΔ))
  | proj _ _ _ _ ih => exact fun hΔ => ih hΔ
  | lit _ _ ih => exact fun hΔ => ih hΔ
  | mdata _ ih => exact fun hΔ => ih hΔ

/-- **The erasure image at the empty context has no free variable.** This is what turns
`SpecContent.defns`' witness into `FVarFreeBodies` at a producer of the invariant. -/
theorem Erases.noFVar {env : VEnv} {Us : List Name} {e : Expr} {t : LBTerm} {x : FVarId}
    (h : Erases env Us [] e t) : ¬ hasFVar x t :=
  h.noFVar_of_noFVars (fun _ => rfl)

/-! ## The invariant -/

/--
What a registration run maintains between a fixed specification environment and its state.

The first two fields are `Γspec`'s own, fixed for the run; `consts` and `inds` are the
coverage the state demands; the rest is the emitted environment, scoped to what the run has
registered.
-/
structure RegInvShape' (env : VEnv) (bo : Name → Option Expr) (lp : Name → List Name)
    (Γspec : GlobalDeclarations) (s : ErasureState) : Prop where
  /-- What the specification environment's entries say about the source. -/
  spec : SpecContent env bo lp Γspec
  /-- The specification bodies are closed. -/
  specClosed : ClosedBodies Γspec
  /-- The specification bodies mention no free variable. Carried, not derived: the invariant
      fixes `Γspec` rather than building it, so the clause is discharged where the invariant
      is inhabited, by `Erases.noFVar` on `SpecContent.defns`' witness. It is what
      `Lower.abstract` consumes through `SpecEnv.fvarFree`. -/
  specFVarFree : FVarFreeBodies Γspec
  /-- Every registered constant is declared, at its canonical kername. -/
  consts : ∀ n : Name, (s.constants.get? n).isSome →
    (LBTerm.envLookup Γspec (toKername n)).isSome
  /-- Every registered inductive is covered. -/
  inds : ∀ n : Name, (s.inductives.get? n).isSome → IndCovered env Γspec n
  /-- The emitted keys are distinct. -/
  keys : (s.gdecls.map Prod.fst).Nodup
  /-- A body declared by both is a `Lower` image. `LowerEnv.defs`, scoped to the registry:
      the registration loop writes `Erasure.etaExpandFix defs j`, which at
      `principalArgIdx = 0` is `LBTerm.etaFix defs j` (F-ETA), and that is `Lower.fixEta` at
      the member. -/
  defs : ∀ kn b₀ b, DefnDecl Γspec kn b₀ → DefnDecl s.gdecls kn b → Lower Γspec b₀ b
  /-- Every registered constant that `Γspec` declares with a body, and that is not a runtime
      key, is emitted with a body. `LowerEnv.defsTotal`, scoped to the registry. -/
  defsTotal : ∀ (n : Name) (b₀ : LBTerm), (s.constants.get? n).isSome →
    DefnDecl Γspec (toKername n) b₀ → ¬ RuntimeKey Γspec (toKername n) →
    ∃ b, DefnDecl s.gdecls (toKername n) b
  /-- A body-less specification constant stays body-less, or is pruned. -/
  axioms : ∀ kn, LBTerm.envLookup Γspec kn = some (.constantDecl ⟨none⟩) →
    LBTerm.envLookup s.gdecls kn = some (.constantDecl ⟨none⟩) ∨
      LBTerm.envLookup s.gdecls kn = none
  /-- Every registered inductive's block is emitted unchanged. `LowerEnv.inds`, scoped. -/
  indsEmitted : ∀ n : Name, (s.inductives.get? n).isSome → IndEmitted env Γspec s.gdecls n
  /-- Pruning only removes. -/
  sub : ∀ kn, LBTerm.envLookup s.gdecls kn ≠ none → LBTerm.envLookup Γspec kn ≠ none
  /-- The emitted bodies are closed. -/
  closed : ClosedBodies s.gdecls

/-- The invariant at the initial state: the registries are empty and nothing is emitted, so
only `Γspec`'s own three clauses are left to hold. This is what makes a cold run possible. -/
theorem RegInvShape'.empty {env : VEnv} {bo : Name → Option Expr} {lp : Name → List Name}
    {Γspec : GlobalDeclarations} (hspec : SpecContent env bo lp Γspec)
    (hcl : ClosedBodies Γspec) (hfv : FVarFreeBodies Γspec) :
    RegInvShape' env bo lp Γspec {} where
  spec := hspec
  specClosed := hcl
  specFVarFree := hfv
  consts n hn := by simp at hn
  inds n hn := by simp at hn
  keys := by simp
  defs kn b₀ b _ hb := by simp [DefnDecl, LBTerm.envLookup] at hb
  defsTotal n b₀ hn := by simp at hn
  axioms kn _ := .inr rfl
  indsEmitted n hn := by simp at hn
  sub kn hk := by simp [LBTerm.envLookup] at hk
  closed kn b hb := by simp [DefnDecl, LBTerm.envLookup] at hb

/-! ## Preservation across the registration primitives -/

/-- The key of a consed entry, decided against a queried kername. -/
theorem kername_ne_of_beq_false {k kn : Kername} (h : Kername.beq k kn = false) : k ≠ kn :=
  fun hk => by rw [hk, Kername.beq_self] at h; exact Bool.noConfusion h

/-- The two state deltas, unfolded once, so the lookup lemmas can fire on them. -/
theorem addAxiomState_gdecls (n : Name) (s : ErasureState) :
    (addAxiomState n s).gdecls = (toKername n, .constantDecl ⟨none⟩) :: s.gdecls := rfl

theorem nonrecConstState_gdecls (n : Name) (t : LBTerm) (s : ErasureState) :
    (nonrecConstState n t s).gdecls = (toKername n, .constantDecl ⟨some t⟩) :: s.gdecls := rfl

theorem addRealizerState_gdecls (n : Name) (t : LBTerm) (s : ErasureState) :
    (addRealizerState n t s).gdecls = (toKername n, .constantDecl ⟨some t⟩) :: s.gdecls := rfl

/-- **`addAxiom`.** Registering a body-less constant preserves the invariant, provided the
specification environment declares it body-less too and its kername is fresh in the emitted
environment. This is the shape `Erasure.addAxiom` leaves behind (`run_addAxiom_ok`). -/
theorem RegInvShape'.addAxiom {env : VEnv} {bo : Name → Option Expr} {lp : Name → List Name}
    {Γspec : GlobalDeclarations} {s : ErasureState} {n : Name}
    (H : RegInvShape' env bo lp Γspec s)
    (hax : LBTerm.envLookup Γspec (toKername n) = some (.constantDecl ⟨none⟩))
    (hfresh : ∀ q ∈ s.gdecls, q.1 ≠ toKername n) :
    RegInvShape' env bo lp Γspec (addAxiomState n s) where
  spec := H.spec
  specClosed := H.specClosed
  specFVarFree := H.specFVarFree
  consts m hm := by
    rcases constants_insert_cases hm with rfl | hm'
    · rw [hax]; rfl
    · exact H.consts m hm'
  inds n' hn' := H.inds n' hn'
  keys := List.nodup_cons.mpr ⟨not_mem_keys_of_fresh hfresh, H.keys⟩
  defs kn b₀ b h₀ hb := by
    rw [DefnDecl, addAxiomState_gdecls] at hb
    cases hk : Kername.beq (toKername n) kn with
    | true =>
      rw [← Kername.eq_of_beq hk, envLookup_cons_self] at hb
      exact absurd hb (by simp)
    | false =>
      exact H.defs kn b₀ b h₀ (envLookup_of_cons_ne (kername_ne_of_beq_false hk) hb)
  defsTotal m b₀ hm h₀ hrk := by
    cases hk : Kername.beq (toKername n) (toKername m) with
    | true =>
      rw [DefnDecl, ← Kername.eq_of_beq hk, hax] at h₀
      exact absurd h₀ (by simp)
    | false =>
      have hne := kername_ne_of_beq_false hk
      rcases constants_insert_cases hm with rfl | hm'
      · exact absurd rfl hne
      · obtain ⟨b, hb⟩ := H.defsTotal m b₀ hm' h₀ hrk
        exact ⟨b, by rw [DefnDecl, addAxiomState_gdecls]; exact envLookup_cons_of_fresh hfresh hb⟩
  axioms kn hkn := by
    rw [addAxiomState_gdecls]
    cases hk : Kername.beq (toKername n) kn with
    | true => rw [← Kername.eq_of_beq hk]; exact .inl envLookup_cons_self
    | false =>
      have hne := kername_ne_of_beq_false hk
      rcases H.axioms kn hkn with h | h
      · exact .inl (envLookup_cons_of_fresh hfresh h)
      · exact .inr (by rw [envLookup_cons_ne hne]; exact h)
  indsEmitted n' hn' iid np nfs hi d hd := by
    rw [addAxiomState_gdecls]
    exact envLookup_cons_of_fresh hfresh (H.indsEmitted n' hn' iid np nfs hi d hd)
  sub kn hk := by
    rw [addAxiomState_gdecls] at hk
    cases hb : Kername.beq (toKername n) kn with
    | true => rw [← Kername.eq_of_beq hb, hax]; simp
    | false =>
      exact H.sub kn (by rwa [envLookup_cons_ne (kername_ne_of_beq_false hb)] at hk)
  closed kn b hb := by
    rw [DefnDecl, addAxiomState_gdecls] at hb
    cases hk : Kername.beq (toKername n) kn with
    | true =>
      rw [← Kername.eq_of_beq hk, envLookup_cons_self] at hb
      exact absurd hb (by simp)
    | false =>
      exact H.closed kn b (envLookup_of_cons_ne (kername_ne_of_beq_false hk) hb)

/-- **`visitMutual`'s non-recursive exit.** Registering a constant with an emitted body
preserves the invariant: the specification environment declares that constant with a body,
the emitted body is its `Lower` image, the emitted body is closed, and the kername is
fresh. The recursive exit reaches the same premise through `Lower.fixEta_of_block`. -/
theorem RegInvShape'.constCons {env : VEnv} {bo : Name → Option Expr} {lp : Name → List Name}
    {Γspec : GlobalDeclarations} {s : ErasureState} {n : Name} {t b₀ : LBTerm}
    (H : RegInvShape' env bo lp Γspec s) (hspec : DefnDecl Γspec (toKername n) b₀)
    (hlow : Lower Γspec b₀ t)
    (hcl : LBClosed t 0) (hfresh : ∀ q ∈ s.gdecls, q.1 ≠ toKername n) :
    RegInvShape' env bo lp Γspec (nonrecConstState n t s) where
  spec := H.spec
  specClosed := H.specClosed
  specFVarFree := H.specFVarFree
  consts m hm := by
    rcases constants_insert_cases hm with rfl | hm'
    · rw [DefnDecl] at hspec; rw [hspec]; rfl
    · exact H.consts m hm'
  inds n' hn' := H.inds n' hn'
  keys := List.nodup_cons.mpr ⟨not_mem_keys_of_fresh hfresh, H.keys⟩
  defs kn b₀' b h₀ hb := by
    rw [DefnDecl, nonrecConstState_gdecls] at hb
    cases hk : Kername.beq (toKername n) kn with
    | true =>
      have hkn := Kername.eq_of_beq hk
      subst hkn
      rw [envLookup_cons_self] at hb
      have hbt : b = t := by simpa using hb.symm
      rw [DefnDecl, hspec] at h₀
      have hb₀ : b₀' = b₀ := by simpa using h₀.symm
      subst hbt; subst hb₀
      exact hlow
    | false =>
      exact H.defs kn b₀' b h₀ (envLookup_of_cons_ne (kername_ne_of_beq_false hk) hb)
  defsTotal m b₀' hm h₀ hrk := by
    cases hk : Kername.beq (toKername n) (toKername m) with
    | true =>
      refine ⟨t, ?_⟩
      rw [DefnDecl, nonrecConstState_gdecls, ← Kername.eq_of_beq hk, envLookup_cons_self]
    | false =>
      have hne := kername_ne_of_beq_false hk
      rcases constants_insert_cases hm with rfl | hm'
      · exact absurd rfl hne
      · obtain ⟨b, hb⟩ := H.defsTotal m b₀' hm' h₀ hrk
        exact ⟨b, by rw [DefnDecl, nonrecConstState_gdecls]
                     exact envLookup_cons_of_fresh hfresh hb⟩
  axioms kn hkn := by
    rw [nonrecConstState_gdecls]
    cases hk : Kername.beq (toKername n) kn with
    | true =>
      rw [← Kername.eq_of_beq hk] at hkn
      rw [DefnDecl] at hspec
      rw [hspec] at hkn
      exact absurd hkn (by simp)
    | false =>
      have hne := kername_ne_of_beq_false hk
      rcases H.axioms kn hkn with h | h
      · exact .inl (envLookup_cons_of_fresh hfresh h)
      · exact .inr (by rw [envLookup_cons_ne hne]; exact h)
  indsEmitted n' hn' iid np nfs hi d hd := by
    rw [nonrecConstState_gdecls]
    exact envLookup_cons_of_fresh hfresh (H.indsEmitted n' hn' iid np nfs hi d hd)
  sub kn hk := by
    rw [nonrecConstState_gdecls] at hk
    cases hb : Kername.beq (toKername n) kn with
    | true =>
      rw [DefnDecl] at hspec
      rw [← Kername.eq_of_beq hb, hspec]
      simp
    | false =>
      exact H.sub kn (by rwa [envLookup_cons_ne (kername_ne_of_beq_false hb)] at hk)
  closed kn b hb := by
    rw [DefnDecl, nonrecConstState_gdecls] at hb
    cases hk : Kername.beq (toKername n) kn with
    | true =>
      rw [← Kername.eq_of_beq hk, envLookup_cons_self] at hb
      have : b = t := by simpa using hb.symm
      subst this; exact hcl
    | false =>
      exact H.closed kn b (envLookup_of_cons_ne (kername_ne_of_beq_false hk) hb)

/-- **`addRealizer`.** `Erasure.addRealizer` writes the entry `Erasure.addAxiom` writes with
`⟨some t⟩` in place of `⟨none⟩` (F-QUOT, F-EQREC), and `addRealizerState` is `nonrecConstState`
at that body, so the step is `RegInvShape'.constCons`. Where `RegInvShape'.addAxiom`'s
hypothesis is the body-less specification entry, this one's is a `DefnDecl`: the specification
environment declares the realized constant with a body the emitted one is an image of. The
emitted body is *not* assumed to be the declared one — that would ask `Lower Γspec t t` of the
two realizer shapes and say nothing the general clause does not. -/
theorem RegInvShape'.addRealizer {env : VEnv} {bo : Name → Option Expr}
    {lp : Name → List Name} {Γspec : GlobalDeclarations} {s : ErasureState} {n : Name}
    {t b₀ : LBTerm} (H : RegInvShape' env bo lp Γspec s)
    (hspec : DefnDecl Γspec (toKername n) b₀) (hlow : Lower Γspec b₀ t)
    (hcl : LBClosed t 0) (hfresh : ∀ q ∈ s.gdecls, q.1 ≠ toKername n) :
    RegInvShape' env bo lp Γspec (addRealizerState n t s) :=
  H.constCons hspec hlow hcl hfresh

/-- The member kernames of an indexed list are the kernames of its members. -/
theorem map_toKername_fst (l : List (Name × Nat)) :
    l.map (fun p => toKername p.1) = (l.map Prod.fst).map toKername := by
  induction l with
  | nil => rfl
  | cons a t ih => simpa using ih

/-- The η-expansion the registration loop writes is the closed shape `LBTerm.etaFix` at a
block whose members all carry `principalArgIdx = 0`, which `LowerBlock.hrarg` asserts.
`Erasure.etaExpandFix_eq` read at that field. -/
theorem LowerBlock.etaExpandFix_eq {Γ : GlobalDeclarations} {kns : List Kername}
    {bs bs' : List LBTerm} {ids : List FVarId} {defs : List (@FixDef LBTerm)}
    (hblk : LowerBlock Γ kns bs bs' ids defs) (j : Nat) :
    etaExpandFix defs j = LBTerm.etaFix defs j :=
  Erasure.etaExpandFix_eq hblk.hrarg

/-- The η-expansion of a block's node is closed, given closed specification bodies:
`LowerBlock.lbClosed_fix` under one binder the node's own `.bvar 0` fills. -/
theorem LowerBlock.lbClosed_etaFix {Γ : GlobalDeclarations} {kns : List Kername}
    {bs bs' : List LBTerm} {ids : List FVarId} {defs : List (@FixDef LBTerm)}
    (hΓ : ClosedBodies Γ) (hblk : LowerBlock Γ kns bs bs' ids defs) (j : Nat) :
    LBClosed (LBTerm.etaFix defs j) 0 :=
  LeanToLambdaBox.lbClosed_etaFix (fun k : Nat => (hblk.lbClosed_fix hΓ j).mono (Nat.zero_le k))

/-- **`visitMutual`'s recursive exit, one member at a time.** The fold `recConstState` runs
is `recConstStep`, which is `nonrecConstState` at an η-expanded `.fix` body, so
`Lower.fixEta_of_block` supplies every member's `defs` premise off the block and
`LowerBlock.lbClosed_etaFix` supplies its closedness. Freshness of a member's kername against
the entries the earlier members have consed is the block's `Nodup`. -/
theorem regInvShape'_foldl_recConstStep {env : VEnv} {bo : Name → Option Expr}
    {lp : Name → List Name}
    {Γspec : GlobalDeclarations} {kns : List Kername} {bs bs' : List LBTerm}
    {ids : List FVarId} {defs : List (@FixDef LBTerm)}
    (hblk : LowerBlock Γspec kns bs bs' ids defs) :
    ∀ (ps : List (Name × Nat)) (s : ErasureState), RegInvShape' env bo lp Γspec s →
      (∀ p ∈ ps, kns[p.2]? = some (toKername p.1)) →
      (∀ p ∈ ps, ∀ q ∈ s.gdecls, q.1 ≠ toKername p.1) →
      (ps.map (fun p => toKername p.1)).Nodup →
      RegInvShape' env bo lp Γspec (ps.foldl (recConstStep defs) s)
  | [], _, H, _, _, _ => H
  | p :: rest, s, H, hidx, hfresh, hnd => by
    have hj : kns[p.2]? = some (toKername p.1) := hidx p List.mem_cons_self
    have hlt : p.2 < kns.length := by
      rcases List.getElem?_eq_some_iff.mp hj with ⟨h, -⟩; exact h
    have hkey : kns[p.2]! = toKername p.1 := by
      rw [getElem!_pos kns p.2 hlt]
      exact Option.some.inj (by rw [← hj, List.getElem?_eq_getElem hlt])
    have hdecl : DefnDecl Γspec (toKername p.1) bs[p.2]! := by
      have := hblk.hdecl p.2 hlt; rwa [hkey] at this
    have H' : RegInvShape' env bo lp Γspec (recConstStep defs s p) :=
      H.constCons hdecl
        (hblk.etaExpandFix_eq p.2 ▸ Lower.fixEta_of_block hblk hj hdecl)
        (hblk.etaExpandFix_eq p.2 ▸ hblk.lbClosed_etaFix H.specClosed p.2)
        (hfresh p List.mem_cons_self)
    obtain ⟨hnh, hnt⟩ := List.nodup_cons.mp hnd
    refine regInvShape'_foldl_recConstStep hblk rest _ H'
      (fun r hr => hidx r (List.mem_cons_of_mem _ hr)) ?_ hnt
    intro r hr q hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · intro hcon
      exact hnh (List.mem_map.mpr ⟨r, hr, hcon.symm⟩)
    · exact hfresh r (List.mem_cons_of_mem _ hr) q hq'

/-- **`visitMutual`'s recursive exit.** A whole block is registered at once: every member is
declared in the specification environment with the body the block lowers, and the emitted
body is the η-expansion of the block's own `.fix` node at that member's index. -/
theorem RegInvShape'.recConst {env : VEnv} {bo : Name → Option Expr} {lp : Name → List Name}
    {Γspec : GlobalDeclarations} {s : ErasureState} {names : List Name}
    {kns : List Kername} {bs bs' : List LBTerm} {ids : List FVarId}
    {defs : List (@FixDef LBTerm)} (H : RegInvShape' env bo lp Γspec s)
    (hblk : LowerBlock Γspec kns bs bs' ids defs)
    (hidx : ∀ p ∈ names.zipIdx, kns[p.2]? = some (toKername p.1))
    (hfresh : ∀ n ∈ names, ∀ q ∈ s.gdecls, q.1 ≠ toKername n)
    (hnd : (names.map toKername).Nodup) :
    RegInvShape' env bo lp Γspec (recConstState names defs s) := by
  rw [recConstState_eq]
  refine regInvShape'_foldl_recConstStep hblk names.zipIdx s H hidx ?_ ?_
  · exact fun p hp => hfresh p.1 (List.fst_mem_of_mem_zipIdx hp)
  · rw [map_toKername_fst, List.zipIdx_map_fst]; exact hnd

/-- **One body-less entry.** `register_inductive`'s cold branch conses one such entry per
`@[extern]` constructor, through `addAxiom`, without the caller seeing the individual runs. -/
theorem RegInvShape'.axiomCons {env : VEnv} {bo : Name → Option Expr} {lp : Name → List Name}
    {Γspec : GlobalDeclarations} {s : ErasureState} {kn : Kername}
    (H : RegInvShape' env bo lp Γspec s)
    (hax : LBTerm.envLookup Γspec kn = some (.constantDecl ⟨none⟩))
    (hfresh : ∀ q ∈ s.gdecls, q.1 ≠ kn) :
    RegInvShape' env bo lp Γspec { s with gdecls := (kn, .constantDecl ⟨none⟩) :: s.gdecls } where
  spec := H.spec
  specClosed := H.specClosed
  specFVarFree := H.specFVarFree
  consts m hm := H.consts m hm
  inds n' hn' := H.inds n' hn'
  keys := List.nodup_cons.mpr ⟨not_mem_keys_of_fresh hfresh, H.keys⟩
  defs kn' b₀ b h₀ hb := by
    rw [DefnDecl] at hb
    cases hk : Kername.beq kn kn' with
    | true =>
      rw [← Kername.eq_of_beq hk, envLookup_cons_self] at hb
      exact absurd hb (by simp)
    | false => exact H.defs kn' b₀ b h₀ (envLookup_of_cons_ne (kername_ne_of_beq_false hk) hb)
  defsTotal m b₀ hm h₀ hrk := by
    obtain ⟨b, hb⟩ := H.defsTotal m b₀ hm h₀ hrk
    exact ⟨b, envLookup_cons_of_fresh hfresh hb⟩
  axioms kn' hkn := by
    cases hk : Kername.beq kn kn' with
    | true => rw [← Kername.eq_of_beq hk]; exact .inl envLookup_cons_self
    | false =>
      have hne := kername_ne_of_beq_false hk
      rcases H.axioms kn' hkn with h | h
      · exact .inl (envLookup_cons_of_fresh hfresh h)
      · exact .inr (by rw [envLookup_cons_ne hne]; exact h)
  indsEmitted n' hn' iid np nfs hi d hd :=
    envLookup_cons_of_fresh hfresh (H.indsEmitted n' hn' iid np nfs hi d hd)
  sub kn' hk := by
    cases hb : Kername.beq kn kn' with
    | true => rw [← Kername.eq_of_beq hb, hax]; simp
    | false => exact H.sub kn' (by rwa [envLookup_cons_ne (kername_ne_of_beq_false hb)] at hk)
  closed kn' b hb := by
    rw [DefnDecl] at hb
    cases hk : Kername.beq kn kn' with
    | true =>
      rw [← Kername.eq_of_beq hk, envLookup_cons_self] at hb
      exact absurd hb (by simp)
    | false => exact H.closed kn' b (envLookup_of_cons_ne (kername_ne_of_beq_false hk) hb)

/-- **A whole body-less prefix.** `ConstExt`'s `gdecls` clause hands back exactly this shape:
the state's declarations grew by a prefix of axiom entries. -/
theorem regInvShape'_axiomPrefix {env : VEnv} {bo : Name → Option Expr} {lp : Name → List Name}
    {Γspec : GlobalDeclarations} :
    ∀ (pre : GlobalDeclarations) (s : ErasureState), RegInvShape' env bo lp Γspec s →
      (∀ p ∈ pre, p.2 = GlobalDecl.constantDecl ⟨none⟩ ∧
        LBTerm.envLookup Γspec p.1 = some (.constantDecl ⟨none⟩)) →
      (pre.map Prod.fst).Nodup → (∀ p ∈ pre, ∀ q ∈ s.gdecls, q.1 ≠ p.1) →
      RegInvShape' env bo lp Γspec { s with gdecls := pre ++ s.gdecls }
  | [], s, H, _, _, _ => by simpa using H
  | p :: rest, s, H, hpre, hnd, hfp => by
    obtain ⟨k, d⟩ := p
    obtain ⟨hd, hax⟩ := hpre _ List.mem_cons_self
    obtain ⟨hnh, hnt⟩ := List.nodup_cons.mp hnd
    have IH := regInvShape'_axiomPrefix rest s H
      (fun q hq => hpre q (List.mem_cons_of_mem _ hq)) hnt
      (fun q hq => hfp q (List.mem_cons_of_mem _ hq))
    have hfresh : ∀ q ∈ rest ++ s.gdecls, q.1 ≠ k := by
      intro q hq
      rcases List.mem_append.mp hq with hq' | hq'
      · intro hcon; exact hnh (List.mem_map.mpr ⟨q, hq', hcon⟩)
      · exact hfp _ List.mem_cons_self q hq'
    have := IH.axiomCons hax hfresh
    rw [show d = GlobalDecl.constantDecl ⟨none⟩ from hd]
    exact this

/-- **The registries, read at a larger state.** The declarations and the inductive registry
are unchanged; a constant the extension added is either one the state already knew or one the
specification environment declares body-less, which is the only kind `addAxiom` adds. -/
theorem RegInvShape'.stateCongr {env : VEnv} {bo : Name → Option Expr} {lp : Name → List Name}
    {Γspec : GlobalDeclarations} {s s' : ErasureState} (H : RegInvShape' env bo lp Γspec s)
    (hg : s'.gdecls = s.gdecls) (hi : s'.inductives = s.inductives)
    (hc : ∀ n : Name, (s'.constants.get? n).isSome → (s.constants.get? n).isSome ∨
      LBTerm.envLookup Γspec (toKername n) = some (.constantDecl ⟨none⟩)) :
    RegInvShape' env bo lp Γspec s' where
  spec := H.spec
  specClosed := H.specClosed
  specFVarFree := H.specFVarFree
  consts m hm := by
    rcases hc m hm with h | h
    · exact H.consts m h
    · rw [h]; rfl
  inds n' hn' := H.inds n' (by rwa [hi] at hn')
  keys := by rw [hg]; exact H.keys
  defs kn b₀ b h₀ hb := H.defs kn b₀ b h₀ (by rwa [DefnDecl, hg] at hb)
  defsTotal m b₀ hm h₀ hrk := by
    rcases hc m hm with h | h
    · obtain ⟨b, hb⟩ := H.defsTotal m b₀ h h₀ hrk
      exact ⟨b, by rw [DefnDecl, hg]; exact hb⟩
    · rw [DefnDecl, h] at h₀; exact absurd h₀ (by simp)
  axioms kn hkn := by rw [hg]; exact H.axioms kn hkn
  indsEmitted n' hn' iid np nfs hind d hd := by
    rw [hg]
    exact H.indsEmitted n' (by rwa [hi] at hn') iid np nfs hind d hd
  sub kn hk := H.sub kn (by rwa [hg] at hk)
  closed kn b hb := H.closed kn b (by rwa [DefnDecl, hg] at hb)

/-- **The inductive registry, grown.** Every name the registry now knows is covered by the
specification environment and has its block emitted; the run's own records supply both at the
names `register_inductive` just registered. -/
theorem RegInvShape'.indsGrow {env : VEnv} {bo : Name → Option Expr} {lp : Name → List Name}
    {Γspec : GlobalDeclarations} {s s' : ErasureState} (H : RegInvShape' env bo lp Γspec s)
    (hg : s'.gdecls = s.gdecls) (hc : s'.constants = s.constants)
    (hnew : ∀ n : Name, (s'.inductives.get? n).isSome →
      IndCovered env Γspec n ∧ IndEmitted env Γspec s.gdecls n) :
    RegInvShape' env bo lp Γspec s' where
  spec := H.spec
  specClosed := H.specClosed
  specFVarFree := H.specFVarFree
  consts m hm := H.consts m (by rwa [hc] at hm)
  inds n' hn' := (hnew n' hn').1
  keys := by rw [hg]; exact H.keys
  defs kn b₀ b h₀ hb := H.defs kn b₀ b h₀ (by rwa [DefnDecl, hg] at hb)
  defsTotal m b₀ hm h₀ hrk := by
    obtain ⟨b, hb⟩ := H.defsTotal m b₀ (by rwa [hc] at hm) h₀ hrk
    exact ⟨b, by rw [DefnDecl, hg]; exact hb⟩
  axioms kn hkn := by rw [hg]; exact H.axioms kn hkn
  indsEmitted n' hn' iid np nfs hind d hd := by
    rw [hg]; exact (hnew n' hn').2 iid np nfs hind d hd
  sub kn hk := H.sub kn (by rwa [hg] at hk)
  closed kn b hb := H.closed kn b (by rwa [DefnDecl, hg] at hb)

/-- **The block entry.** `registerIndState` conses the block the run built; the specification
environment holds that same block, which is `LowerEnv.inds` at this key. -/
theorem RegInvShape'.blockCons {env : VEnv} {bo : Name → Option Expr} {lp : Name → List Name}
    {Γspec : GlobalDeclarations} {s : ErasureState} {kn : Kername}
    {mib : MutualInductiveBody} (H : RegInvShape' env bo lp Γspec s)
    (hspec : LBTerm.envLookup Γspec kn = some (.inductiveDecl mib))
    (hfresh : ∀ q ∈ s.gdecls, q.1 ≠ kn) :
    RegInvShape' env bo lp Γspec { s with gdecls := (kn, .inductiveDecl mib) :: s.gdecls } where
  spec := H.spec
  specClosed := H.specClosed
  specFVarFree := H.specFVarFree
  consts m hm := H.consts m hm
  inds n' hn' := H.inds n' hn'
  keys := List.nodup_cons.mpr ⟨not_mem_keys_of_fresh hfresh, H.keys⟩
  defs kn' b₀ b h₀ hb := by
    rw [DefnDecl] at hb
    cases hk : Kername.beq kn kn' with
    | true =>
      rw [← Kername.eq_of_beq hk, envLookup_cons_self] at hb
      exact absurd hb (by simp)
    | false => exact H.defs kn' b₀ b h₀ (envLookup_of_cons_ne (kername_ne_of_beq_false hk) hb)
  defsTotal m b₀ hm h₀ hrk := by
    obtain ⟨b, hb⟩ := H.defsTotal m b₀ hm h₀ hrk
    exact ⟨b, envLookup_cons_of_fresh hfresh hb⟩
  axioms kn' hkn := by
    cases hk : Kername.beq kn kn' with
    | true =>
      rw [← Kername.eq_of_beq hk] at hkn
      rw [hspec] at hkn; exact absurd hkn (by simp)
    | false =>
      have hne := kername_ne_of_beq_false hk
      rcases H.axioms kn' hkn with h | h
      · exact .inl (envLookup_cons_of_fresh hfresh h)
      · exact .inr (by rw [envLookup_cons_ne hne]; exact h)
  indsEmitted n' hn' iid np nfs hind d hd :=
    envLookup_cons_of_fresh hfresh (H.indsEmitted n' hn' iid np nfs hind d hd)
  sub kn' hk := by
    cases hb : Kername.beq kn kn' with
    | true => rw [← Kername.eq_of_beq hb, hspec]; simp
    | false => exact H.sub kn' (by rwa [envLookup_cons_ne (kername_ne_of_beq_false hb)] at hk)
  closed kn' b hb := by
    rw [DefnDecl] at hb
    cases hk : Kername.beq kn kn' with
    | true =>
      rw [← Kername.eq_of_beq hk, envLookup_cons_self] at hb
      exact absurd hb (by simp)
    | false => exact H.closed kn' b (envLookup_of_cons_ne (kername_ne_of_beq_false hk) hb)

/-! ## The invariant across the two registration runs -/

/-- **`addAxiom`, at the run.** `run_addAxiom_ok` reports the exact state delta, so the run
form is the delta form with no extra hypothesis. -/
theorem RegInvShape'.addAxiom_run {env : VEnv} {bo : Name → Option Expr} {lp : Name → List Name}
    {Γspec : GlobalDeclarations} {n : Name} {s : ErasureState} {ctx : ErasureContext}
    {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
    {u : Unit} {s₁ : ErasureState} {w₁ : Void IO.RealWorld}
    (H : RegInvShape' env bo lp Γspec s)
    (hrun : Erasure.addAxiom n s ctx cctx ref w = .ok (u, s₁) w₁)
    (hax : LBTerm.envLookup Γspec (toKername n) = some (.constantDecl ⟨none⟩))
    (hfresh : ∀ q ∈ s.gdecls, q.1 ≠ toKername n) :
    RegInvShape' env bo lp Γspec s₁ := by
  rw [(run_addAxiom_ok hrun).1]
  exact H.addAxiom hax hfresh

/-- **`register_inductive`, cold, at the run.** The intermediate state the cold branch builds
is not exposed by `run_register_inductive_cold_ok`, so every side condition is read off the
*final* state: the emitted keys are distinct, each body-less entry is declared body-less in
the specification environment, the emitted block is the one the specification environment
holds, and each registry entry is either one the run already had or a covered one. -/
theorem RegInvShape'.register_inductive_run {env : VEnv} {bo : Name → Option Expr}
    {lp : Name → List Name}
    {Γspec : GlobalDeclarations} {indinfo : InductiveVal} {s : ErasureState}
    {ctx : ErasureContext} {cctx : Core.Context} {ref : ST.Ref IO.RealWorld Core.State}
    {w : Void IO.RealWorld} {r : InductiveId × InductiveArgMasks} {s₁ : ErasureState}
    {w₁ : Void IO.RealWorld} (H : RegInvShape' env bo lp Γspec s)
    (hmiss : s.inductives.get? indinfo.name = none)
    (hrun : register_inductive indinfo s ctx cctx ref w = .ok (r, s₁) w₁)
    (hkeys : (s₁.gdecls.map Prod.fst).Nodup)
    (haxpre : ∀ p ∈ s₁.gdecls, p.2 = GlobalDecl.constantDecl ⟨none⟩ →
      LBTerm.envLookup Γspec p.1 = some (.constantDecl ⟨none⟩))
    (hblk : ∀ mib, LBTerm.envLookup s₁.gdecls (mutualBlockKn indinfo) = some (.inductiveDecl mib) →
      LBTerm.envLookup Γspec (mutualBlockKn indinfo) = some (.inductiveDecl mib))
    (hnewc : ∀ n : Name, (s₁.constants.get? n).isSome → (s.constants.get? n).isSome ∨
      LBTerm.envLookup Γspec (toKername n) = some (.constantDecl ⟨none⟩))
    (hnewi : ∀ n : Name, (s₁.inductives.get? n).isSome → (s.inductives.get? n).isSome ∨
      (IndCovered env Γspec n ∧ IndEmitted env Γspec s₁.gdecls n)) :
    RegInvShape' env bo lp Γspec s₁ := by
  obtain ⟨-, bodies, sM, rfl, -, -, hce, -, -⟩ :=
    run_register_inductive_cold_ok (Ci := fun _ _ => True)
      (fun _ _ _ _ _ _ _ => trivial) hmiss hrun
  obtain ⟨pre, hpre, hshape⟩ := hce.gdeclsAx
  have hgd : (registerIndState indinfo bodies sM).gdecls
      = (mutualBlockKn indinfo,
          GlobalDecl.inductiveDecl { npars := indinfo.numParams, bodies := bodies })
        :: (pre ++ s.gdecls) := by
    show (mutualBlockKn indinfo,
      GlobalDecl.inductiveDecl { npars := indinfo.numParams, bodies := bodies })
        :: sM.gdecls = _
    rw [hpre]
  rw [hgd, List.map_cons, List.nodup_cons, List.map_append, List.nodup_append] at hkeys
  obtain ⟨hbn, hndp, hnds, hdisj⟩ := hkeys
  -- the axiom prefix
  have hA : RegInvShape' env bo lp Γspec { s with gdecls := pre ++ s.gdecls } := by
    refine regInvShape'_axiomPrefix pre s H (fun p hp => ⟨(hshape p hp).1, ?_⟩) hndp ?_
    · refine haxpre p ?_ (hshape p hp).1
      rw [hgd]
      exact List.mem_cons_of_mem _ (List.mem_append_left _ hp)
    · intro p hp q hq hcon
      exact hdisj _ (List.mem_map.mpr ⟨p, hp, rfl⟩) _
        (List.mem_map.mpr ⟨q, hq, rfl⟩) hcon.symm
  -- the constants the extension added
  have hB : RegInvShape' env bo lp Γspec { sM with inductives := s.inductives } :=
    hA.stateCongr hpre rfl (fun n hn => hnewc n hn)
  -- the block entry
  have hfb : ∀ q ∈ ({ sM with inductives := s.inductives } : ErasureState).gdecls,
      q.1 ≠ mutualBlockKn indinfo := by
    intro q hq hcon
    have hmem : q.1 ∈ List.map Prod.fst (pre ++ s.gdecls) :=
      List.mem_map.mpr ⟨q, by rw [← hpre]; exact hq, rfl⟩
    rw [List.map_append] at hmem
    exact hbn (hcon ▸ hmem)
  have hC := hB.blockCons
    (mib := { npars := indinfo.numParams, bodies := bodies })
    (hblk _ (by rw [hgd]; exact envLookup_cons_self)) hfb
  -- the inductive registry
  refine hC.indsGrow rfl rfl (fun n hn => ?_)
  rcases hnewi n hn with hold | hnew
  · exact ⟨hC.inds n hold, hC.indsEmitted n hold⟩
  · exact hnew

/-! ## The specification environment as an output

`Γspec` above is fixed for the run. U6 makes it an accumulator, as `deps` is in MetaRocq's
`erase_global_deps` (`../metarocq/erasure/theories/EDeps.v:492`, `erases_deps_cons`): a step
may extend it by fresh keys, and `SpecGrow` is the extension the pass survives. What that
costs the invariant is one transport per clause, below, and what it buys is a registration
step that can *declare* what it registers instead of reading a declaration off an environment
chosen in advance.
-/

/-- Coverage of one inductive is read through lookups alone, so it survives any extension
that preserves them — `SpecGrow.lookup` at a growth, `envLookup_cons_of_fresh` at a cons. -/
theorem IndCovered.lookupMono {env : VEnv} {Γ Γ' : GlobalDeclarations} {n : Name}
    (hmono : ∀ (kn : Kername) (d : GlobalDecl), LBTerm.envLookup Γ kn = some d →
      LBTerm.envLookup Γ' kn = some d) (H : IndCovered env Γ n) : IndCovered env Γ' n where
  block iid np nfs hi :=
    let ⟨hdecl, mib, hmib, hbody, hflag⟩ := H.block iid np nfs hi
    ⟨hdecl, mib, hmono _ _ hmib, hbody, hflag⟩
  elims c dp nm hsh hinf hco :=
    let ⟨iid, np, nfs, ⟨⟨body, hb, he⟩, mib, hm, hbo, hnp⟩, hi, hnm⟩ :=
      H.elims c dp nm hsh hinf hco
    ⟨iid, np, nfs, ⟨⟨body, hmono _ _ hb, he⟩, mib, hmono _ _ hm, hbo, hnp⟩, hi, hnm⟩

/-- **What `SpecContent` asks of one new entry.** `toKername` is not injective (F-KERNAME),
so an entry keyed at `kn` answers for *every* source name mapping to `kn`: `defns` and
`axioms` are that entry's two readings, quantified over those names. `blocks` and `elims`
say the key is neither a modelled block's nor a modelled eliminator's, which is what keeps
`SpecContent`'s two inductive clauses from firing at it — the shape a constant registration
has, and not the shape an inductive registration has. -/
structure SpecEntryOk (env : VEnv) (bo : Name → Option Expr) (lp : Name → List Name)
    (kn : Kername) (d : GlobalDecl) : Prop where
  /-- No modelled inductive's block is keyed here. -/
  blocks : ∀ (I : Name) (iid : InductiveId) (np : Nat) (nfs : List Nat),
    IndInfo env I iid np nfs → iid.mutualBlockName ≠ kn
  /-- No modelled eliminator is keyed here. -/
  elims : ∀ (c I : Name) (dp nm : Nat), CasesOnShape env c I dp nm → toKername c ≠ kn
  /-- A tabled name keyed here has its body's erasure as the entry, at its own level scope. -/
  defns : ∀ (n : Name) (b : Expr), toKername n = kn → bo n = some b →
    ∃ b₀, d = .constantDecl ⟨some b₀⟩ ∧ Erases env (lp n) [] b b₀
  /-- A body-less non-eliminator name keyed here has a body-less entry. -/
  axioms : ∀ n : Name, toKername n = kn → bo n = none → ConstOrigin env n →
    isCasesOnName n = false → d = .constantDecl ⟨none⟩

/-- **One new specification entry.** The four clauses of `SpecEntryOk` are what the five
clauses of `SpecContent` ask at the consed key; at every other key the lookup is the old
one. -/
theorem SpecContent.cons {env : VEnv} {bo : Name → Option Expr} {lp : Name → List Name}
    {Γ : GlobalDeclarations} {kn : Kername} {d : GlobalDecl} (H : SpecContent env bo lp Γ)
    (hfresh : ∀ q ∈ Γ, q.1 ≠ kn) (hd : SpecEntryOk env bo lp kn d) :
    SpecContent env bo lp ((kn, d) :: Γ) where
  keys := List.nodup_cons.mpr ⟨not_mem_keys_of_fresh hfresh, H.keys⟩
  defns c b hbo hs := by
    cases hk : Kername.beq kn (toKername c) with
    | true =>
      obtain ⟨b₀, rfl, her⟩ := hd.defns c b (Kername.eq_of_beq hk).symm hbo
      exact ⟨b₀, by rw [← Kername.eq_of_beq hk]; exact envLookup_cons_self, her⟩
    | false =>
      have hne := kername_ne_of_beq_false hk
      obtain ⟨b₀, hl, her⟩ := H.defns c b hbo (by rwa [envLookup_cons_ne hne] at hs)
      exact ⟨b₀, envLookup_cons_of_fresh hfresh hl, her⟩
  axioms c hbo hco hnc hs := by
    cases hk : Kername.beq kn (toKername c) with
    | true =>
      rw [← Kername.eq_of_beq hk, envLookup_cons_self,
        hd.axioms c (Kername.eq_of_beq hk).symm hbo hco hnc]
    | false =>
      have hne := kername_ne_of_beq_false hk
      exact envLookup_cons_of_fresh hfresh
        (H.axioms c hbo hco hnc (by rwa [envLookup_cons_ne hne] at hs))
  blocks I iid np nfs hi hs :=
    (H.blocks I iid np nfs hi
        (by rwa [envLookup_cons_ne (hd.blocks I iid np nfs hi).symm] at hs)).lookupMono
      (fun _ _ => envLookup_cons_of_fresh hfresh)
  elims c I dp nm hsh hs :=
    (H.elims c I dp nm hsh
        (by rwa [envLookup_cons_ne (hd.elims c I dp nm hsh).symm] at hs)).lookupMono
      (fun _ _ => envLookup_cons_of_fresh hfresh)

/-- **The invariant along growth.** The three specification-side clauses are facts about the
grown environment and are premises; the six state-facing ones transport. `defs` is the clause
the growth is for: it re-derives every previously emitted body's `Lower` fact at the larger
environment, which is `Lower.specGrow` at a declared body and therefore `ConstsDeclaredEnv`.
`defsTotal` goes the easy way — its `¬ RuntimeKey` premise is the stronger one at `Γ'`. -/
theorem RegInvShape'.specGrow {env : VEnv} {bo : Name → Option Expr} {lp : Name → List Name}
    {Γ Γ' : GlobalDeclarations} {s : ErasureState} (H : RegInvShape' env bo lp Γ s)
    (hg : SpecGrow Γ Γ') (henv : ConstsDeclaredEnv Γ) (hspec : SpecContent env bo lp Γ')
    (hcl : ClosedBodies Γ') (hfv : FVarFreeBodies Γ') :
    RegInvShape' env bo lp Γ' s where
  spec := hspec
  specClosed := hcl
  specFVarFree := hfv
  consts n hn := hg.isSome (H.consts n hn)
  inds n hn := (H.inds n hn).lookupMono (fun _ _ => hg.lookup)
  keys := H.keys
  defs kn b₀ b h₀ hb := by
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1
      (Option.isSome_iff_ne_none.2 (H.sub kn (by rw [DefnDecl] at hb; rw [hb]; simp)))
    have hd' : DefnDecl Γ kn b₀ := by
      rw [DefnDecl, hd]
      exact (hg.lookup hd).symm.trans h₀
    exact Lower.specGrow hg henv (H.defs kn b₀ b hd' hb)
      (.of_constsDeclared hg (henv kn b₀ hd'))
  defsTotal n b₀ hn h₀ hrk := by
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 (H.consts n hn)
    have hd' : DefnDecl Γ (toKername n) b₀ := by
      rw [DefnDecl, hd]
      exact (hg.lookup hd).symm.trans h₀
    exact H.defsTotal n b₀ hn hd' fun hrk' => hrk (hrk'.specGrow hg)
  axioms kn hkn := by
    cases hq : LBTerm.envLookup Γ kn with
    | none => exact .inr (by by_contra hc; exact (H.sub kn hc) hq)
    | some d =>
      refine H.axioms kn ?_
      rw [hq, ← hkn, hg.lookup hq]
  indsEmitted n hn iid np nfs hi d hd := by
    obtain ⟨-, mib, hmib, -, -⟩ := (H.inds n hn).block iid np nfs hi
    obtain rfl : mib = d := by rw [hg.lookup hmib] at hd; injection Option.some.inj hd
    exact H.indsEmitted n hn iid np nfs hi mib hmib
  sub kn hk := by
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 (Option.isSome_iff_ne_none.2 (H.sub kn hk))
    rw [hg.lookup hd]; simp
  closed := H.closed

/-! ## The content clause

`RegInvShape'.defs` says the emitted body of a key is the `Lower` image of *the* body
`Γspec` declares there; `SpecContent.defns` says that body is *some* erasure of the compiler
body. `Erases` is not deterministic outside the first-order fragment, so the two readings do
not compose: `RegContent` is the single clause carrying both at one witness, which is the
determinism gap `doc/rework/08-REPAIRS-W5.md` §2.1 names. `declEnv` is the accumulator's
second clause, the δ column `Lower.specGrow` spends and `SpecGrow.of_fresh` pays with
`elimBlocksDeclared_of_constsDeclaredEnv`.
-/

/-- **One erasure witness, read both ways.** The emitted body of a tabled constant is the
`Lower` image of a body `Γspec` declares, and that same body is an erasure of the compiler
body at the declaration's own level scope (`../metarocq/erasure/theories/Extract.v:264`,
`erase_constant_body`, which erases at `cst_universes` in the empty context). The block
members are covered by the single `Lower` conjunct: the η-expansion the registration loop
writes is `Lower.fixEta` at the member (`Lower.fixEta_of_block`). -/
structure RegContent (env : VEnv) (bo : Name → Option Expr) (lp : Name → List Name)
    (Γspec : GlobalDeclarations) (s : ErasureState) : Prop where
  /-- Both readings of one witness, at every emitted body of a tabled name. -/
  defns : ∀ (n : Name) (b : Expr) (t : LBTerm), bo n = some b →
    DefnDecl s.gdecls (toKername n) t →
    ∃ b₀ : LBTerm, DefnDecl Γspec (toKername n) b₀ ∧ Erases env (lp n) [] b b₀ ∧
      Lower Γspec b₀ t
  /-- Every declared body's own references are declared. -/
  declEnv : ConstsDeclaredEnv Γspec

/-- The content clause at the initial state: nothing is emitted, so only the δ column is
left to hold. -/
theorem RegContent.empty {env : VEnv} {bo : Name → Option Expr} {lp : Name → List Name}
    {Γspec : GlobalDeclarations} (henv : ConstsDeclaredEnv Γspec) :
    RegContent env bo lp Γspec {} where
  defns n b t _ hb := by simp [DefnDecl, LBTerm.envLookup] at hb
  declEnv := henv

/-- **The content clause along growth.** The witness is transported by `SpecGrow.defnDecl`,
its erasure reading mentions no environment, and its `Lower` reading is `Lower.specGrow` at a
declared body. -/
theorem RegContent.specGrow {env : VEnv} {bo : Name → Option Expr} {lp : Name → List Name}
    {Γ Γ' : GlobalDeclarations} {s : ErasureState} (H : RegContent env bo lp Γ s)
    (hg : SpecGrow Γ Γ') (henv : ConstsDeclaredEnv Γ') : RegContent env bo lp Γ' s where
  defns n b t hbo hb :=
    let ⟨b₀, hd, her, hlow⟩ := H.defns n b t hbo hb
    ⟨b₀, hg.defnDecl hd, her,
      Lower.specGrow hg H.declEnv hlow (.of_constsDeclared hg (H.declEnv _ _ hd))⟩
  declEnv := henv

/-- The content clause reads the emitted declarations and nothing else of the state. -/
theorem RegContent.stateCongr {env : VEnv} {bo : Name → Option Expr} {lp : Name → List Name}
    {Γspec : GlobalDeclarations} {s s' : ErasureState} (H : RegContent env bo lp Γspec s)
    (hg : s'.gdecls = s.gdecls) : RegContent env bo lp Γspec s' where
  defns n b t hbo hb := H.defns n b t hbo (by rwa [DefnDecl, hg] at hb)
  declEnv := H.declEnv

/-- A body-less prefix declares no body, so a `DefnDecl` of the extended list is the tail's.
-/
theorem defnDecl_of_append_axioms : ∀ {pre Γ : GlobalDeclarations} {kn : Kername} {t : LBTerm},
    (∀ p ∈ pre, p.2 = GlobalDecl.constantDecl ⟨none⟩) → DefnDecl (pre ++ Γ) kn t →
    DefnDecl Γ kn t
  | [], _, _, _, _, h => h
  | (k, v) :: pre, Γ, kn, t, hpre, h => by
      rw [DefnDecl, List.cons_append, LBTerm.envLookup] at h
      split at h
      · have hv : v = GlobalDecl.constantDecl ⟨none⟩ := hpre (k, v) List.mem_cons_self
        rw [hv] at h
        exact absurd h (by simp)
      · exact defnDecl_of_append_axioms (fun p hp => hpre p (List.mem_cons_of_mem _ hp)) h

/-- **One new emitted entry.** The content is owed only where the entry carries a body and
the key is a tabled name's; the body-less and block conses discharge `hnew` vacuously. -/
theorem RegContent.gdeclsCons {env : VEnv} {bo : Name → Option Expr} {lp : Name → List Name}
    {Γ : GlobalDeclarations} {s s' : ErasureState} {k : Kername} {d : GlobalDecl}
    (H : RegContent env bo lp Γ s) (hg : s'.gdecls = (k, d) :: s.gdecls)
    (hnew : ∀ (n : Name) (b : Expr) (t : LBTerm), bo n = some b → toKername n = k →
      d = .constantDecl ⟨some t⟩ →
      ∃ b₀, DefnDecl Γ k b₀ ∧ Erases env (lp n) [] b b₀ ∧ Lower Γ b₀ t) :
    RegContent env bo lp Γ s' where
  defns n b t hbo hb := by
    rw [DefnDecl, hg, LBTerm.envLookup] at hb
    split at hb
    · rename_i hk
      obtain rfl : k = toKername n := Kername.eq_of_beq hk
      exact hnew n b t hbo rfl (Option.some.inj hb)
    · exact H.defns n b t hbo hb
  declEnv := H.declEnv

/-- **A whole body-less prefix**, the shape `ConstExt`'s `gdecls` clause hands back. -/
theorem RegContent.gdeclsPrefix {env : VEnv} {bo : Name → Option Expr} {lp : Name → List Name}
    {Γ : GlobalDeclarations} {s s' : ErasureState} {pre : GlobalDeclarations}
    (H : RegContent env bo lp Γ s) (hg : s'.gdecls = pre ++ s.gdecls)
    (hpre : ∀ p ∈ pre, p.2 = GlobalDecl.constantDecl ⟨none⟩) :
    RegContent env bo lp Γ s' where
  defns n b t hbo hb :=
    H.defns n b t hbo (defnDecl_of_append_axioms hpre (by rwa [DefnDecl, hg] at hb))
  declEnv := H.declEnv

/-- **The accumulator at the cold start.** Every clause of the empty specification
environment is vacuous — its lookups all miss — so a run beginning at the empty state begins
with both halves of the accumulator in hand, with no specification environment posited in
advance. That is what makes `Γspec` an output rather than an input. -/
theorem regInv_cold_start {env : VEnv} {bo : Name → Option Expr} {lp : Name → List Name} :
    RegInvShape' env bo lp [] {} ∧ RegContent env bo lp [] {} := by
  have hnil : ∀ (kn : Kername), ¬ (LBTerm.envLookup ([] : GlobalDeclarations) kn).isSome := by
    intro kn h; simp [LBTerm.envLookup] at h
  have hspec : SpecContent env bo lp [] :=
    { keys := by simp
      defns := fun _ _ _ hs => absurd hs (hnil _)
      axioms := fun _ _ _ _ hs => absurd hs (hnil _)
      blocks := fun _ _ _ _ _ hs => absurd hs (hnil _)
      elims := fun _ _ _ _ _ hs => absurd hs (hnil _) }
  refine ⟨RegInvShape'.empty hspec ?_ ?_, RegContent.empty ?_⟩
  · intro kn b hb; simp [DefnDecl, LBTerm.envLookup] at hb
  · intro kn b x hb; simp [DefnDecl, LBTerm.envLookup] at hb
  · intro kn b hb; simp [DefnDecl, LBTerm.envLookup] at hb

/-! ## Two registration steps at a growing specification environment

Each is the shape one step of the preservation theorem has: from the accumulator at the
entry state, an extension and the accumulator at the exit state. The specification entry is
*built* at the step, which is how the step pays `RegInvShape'.constCons`' `hspec` premise
without an environment fixed in advance.
-/

/-- **`addAxiom`, declaring what it registers.** The run conses a body-less emitted entry and
the specification environment gains the same entry. -/
theorem regInv_addAxiom_step {env : VEnv} {bo : Name → Option Expr} {lp : Name → List Name}
    {Γ : GlobalDeclarations} {s : ErasureState} {n : Name}
    (H : RegInvShape' env bo lp Γ s) (C : RegContent env bo lp Γ s)
    (hok : SpecEntryOk env bo lp (toKername n) (.constantDecl ⟨none⟩))
    (hfΓ : ∀ q ∈ Γ, q.1 ≠ toKername n) (hfs : ∀ q ∈ s.gdecls, q.1 ≠ toKername n) :
    ∃ Γ' : GlobalDeclarations, SpecGrow Γ Γ' ∧
      RegInvShape' env bo lp Γ' (addAxiomState n s) ∧
      RegContent env bo lp Γ' (addAxiomState n s) := by
  refine ⟨(toKername n, .constantDecl ⟨none⟩) :: Γ, ?_, ?_, ?_⟩
  · exact SpecGrow.of_fresh (pre := [(toKername n, .constantDecl ⟨none⟩)])
      (fun p hp q hq => by
        rcases List.mem_singleton.1 hp with rfl
        exact fun hc => hfΓ q hq hc.symm)
      (elimBlocksDeclared_of_constsDeclaredEnv C.declEnv)
  · refine (H.specGrow ?_ C.declEnv (H.spec.cons hfΓ hok)
      (closedBodies_cons H.specClosed (by simp))
      (fvarFreeBodies_cons H.specFVarFree (by simp))).addAxiom envLookup_cons_self hfs
    exact SpecGrow.of_fresh (pre := [(toKername n, .constantDecl ⟨none⟩)])
      (fun p hp q hq => by
        rcases List.mem_singleton.1 hp with rfl
        exact fun hc => hfΓ q hq hc.symm)
      (elimBlocksDeclared_of_constsDeclaredEnv C.declEnv)
  · refine (C.specGrow ?_ (constsDeclaredEnv_cons C.declEnv (by simp))).gdeclsCons
      (addAxiomState_gdecls n s) (by simp)
    exact SpecGrow.of_fresh (pre := [(toKername n, .constantDecl ⟨none⟩)])
      (fun p hp q hq => by
        rcases List.mem_singleton.1 hp with rfl
        exact fun hc => hfΓ q hq hc.symm)
      (elimBlocksDeclared_of_constsDeclaredEnv C.declEnv)

/-- **`visitMutual`'s non-recursive exit, declaring what it registers.** The specification
environment gains the erasure witness `hok` carries, and the emitted body is its `Lower`
image — the two readings `RegContent.defns` bundles, established at the step that creates
them. `hlow` and `hdecl` are read at the environment *before* the step, which is the shape a
sub-run's conclusion has. -/
theorem regInv_constCons_step {env : VEnv} {bo : Name → Option Expr} {lp : Name → List Name}
    {Γ : GlobalDeclarations} {s : ErasureState} {n : Name} {t b₀ : LBTerm}
    (H : RegInvShape' env bo lp Γ s) (C : RegContent env bo lp Γ s)
    (hok : SpecEntryOk env bo lp (toKername n) (.constantDecl ⟨some b₀⟩))
    (hlow : Lower Γ b₀ t) (hdecl : ConstsDeclared Γ b₀) (hcl₀ : LBClosed b₀ 0)
    (hfv₀ : ∀ x : FVarId, ¬ hasFVar x b₀) (hclt : LBClosed t 0)
    (hfΓ : ∀ q ∈ Γ, q.1 ≠ toKername n) (hfs : ∀ q ∈ s.gdecls, q.1 ≠ toKername n) :
    ∃ Γ' : GlobalDeclarations, SpecGrow Γ Γ' ∧
      RegInvShape' env bo lp Γ' (nonrecConstState n t s) ∧
      RegContent env bo lp Γ' (nonrecConstState n t s) := by
  have hg : SpecGrow Γ ((toKername n, .constantDecl ⟨some b₀⟩) :: Γ) :=
    SpecGrow.of_fresh (pre := [(toKername n, .constantDecl ⟨some b₀⟩)])
      (fun p hp q hq => by
        rcases List.mem_singleton.1 hp with rfl
        exact fun hc => hfΓ q hq hc.symm)
      (elimBlocksDeclared_of_constsDeclaredEnv C.declEnv)
  have hdecl' : ConstsDeclared ((toKername n, .constantDecl ⟨some b₀⟩) :: Γ) b₀ := hdecl.cons
  have hlow' : Lower ((toKername n, .constantDecl ⟨some b₀⟩) :: Γ) b₀ t :=
    Lower.specGrow hg C.declEnv hlow (.of_constsDeclared hg hdecl)
  refine ⟨(toKername n, .constantDecl ⟨some b₀⟩) :: Γ, hg, ?_, ?_⟩
  · exact (H.specGrow hg C.declEnv (H.spec.cons hfΓ hok)
      (closedBodies_cons H.specClosed (fun b hb => by
        obtain rfl : b₀ = b := by simpa using hb
        exact hcl₀))
      (fvarFreeBodies_cons H.specFVarFree (fun b x hb => by
        obtain rfl : b₀ = b := by simpa using hb
        exact hfv₀ x))).constCons envLookup_cons_self hlow' hclt hfs
  · refine (C.specGrow hg (constsDeclaredEnv_cons C.declEnv (fun b hb => by
      obtain rfl : b₀ = b := by simpa using hb
      exact hdecl'))).gdeclsCons (nonrecConstState_gdecls n t s) ?_
    intro m b t' hbo hkey hd
    obtain rfl : t = t' := by simpa using hd
    obtain ⟨b₀', heq, her⟩ := hok.defns m b hkey hbo
    obtain rfl : b₀ = b₀' := by simpa using heq
    exact ⟨b₀, envLookup_cons_self, her, hlow'⟩

/-! ## Saturation at the final state

`RegSaturated` (`SpecEnv.lean`) reads a *registered-name* fact off a *key*, the converse of
`RegInvShape'.consts`/`.inds`. `RegKeyed` is that converse for the emitted environment alone,
tagged by the entry's own shape rather than by mere presence: `A-hbridge.md`'s sketch triggers
on `LBTerm.envLookup s.gdecls kn ≠ none` and disjoins on registry membership with no shape
attached, which is unsatisfiable as a route to `RegSaturated.inds` — the "constant" disjunct
carries no fact ruling out a name `n` whose canonical kername coincides with a block's (both
`toKername` and `mutualBlockKn`'s `rootKername` are ad hoc string-based maps into one
`Kername` space with no stated injectivity or disjointness between them, and they do collide:
`toKername \`id = rootKername "id"`, by `decide`). Reading each disjunct off the shape it
produces closes that gap without assuming the collision away: a `.constantDecl`-shaped entry
answers `consts`, a `.inductiveDecl`-shaped one answers `inds`, and `GlobalDecl`'s two
constructors are disjoint whichever shape a given key's entry turns out to have. -/

/-- Every emitted key is a registered constant's canonical kername or a registered inductive's
block key, read off the shape the emitted entry itself carries. `env` is a parameter, which
`IndInfo` needs and `A-hbridge.md`'s sketch omits. -/
structure RegKeyed (env : VEnv) (s : ErasureState) : Prop where
  /-- A constant-shaped entry is some registered constant's canonical kername. -/
  consts : ∀ kn cb, (kn, GlobalDecl.constantDecl cb) ∈ s.gdecls →
    ∃ n : Name, kn = toKername n ∧ (s.constants.get? n).isSome
  /-- A block-shaped entry is some registered inductive's block key. -/
  inds : ∀ kn mib, (kn, GlobalDecl.inductiveDecl mib) ∈ s.gdecls →
    ∃ (n : Name) (iid : InductiveId) (np : Nat) (nfs : List Nat),
      (s.inductives.get? n).isSome ∧ IndInfo env n iid np nfs ∧ kn = iid.mutualBlockName

/-- **Preserved across a constant-only extension.** `ConstExt.gdecls` already records, for
every prefix entry, that it is `.constantDecl`-shaped and keyed at a registered constant's
kername (`08-REPAIRS-W5.md` §2.2); a prefix entry can therefore only ever *answer* `consts`,
never `inds`, which is what makes the `inds` case of a fresh key impossible rather than
merely unproved. -/
theorem ConstExt.regKeyed {env : VEnv} {s s' : ErasureState} (h : ConstExt s s')
    (hind : ∀ n : Name, (s.inductives.get? n).isSome → (s'.inductives.get? n).isSome)
    (H : RegKeyed env s) : RegKeyed env s' where
  consts kn cb hmem := by
    obtain ⟨pre, hpre, hshape⟩ := h.gdecls
    rw [hpre] at hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · obtain ⟨-, m, hkm, hms⟩ := hshape (kn, .constantDecl cb) hmem
      exact ⟨m, hkm, hms⟩
    · obtain ⟨n, hn, hns⟩ := H.consts kn cb hmem
      exact ⟨n, hn, h.dom hns⟩
  inds kn mib hmem := by
    obtain ⟨pre, hpre, hshape⟩ := h.gdecls
    rw [hpre] at hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact absurd (hshape (kn, .inductiveDecl mib) hmem).1 (by simp)
    · obtain ⟨n, iid, np, nfs, hns, hii, hkn⟩ := H.inds kn mib hmem
      exact ⟨n, iid, np, nfs, hind n hns, hii, hkn⟩

end LeanToLambdaBox
