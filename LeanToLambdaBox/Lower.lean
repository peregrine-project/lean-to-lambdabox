import LeanToLambdaBox.Closed
import LeanToLambdaBox.Abstract
import LeanToLambdaBox.FixMetatheory
import LeanToLambdaBox.Semantics.Env
import LeanToLambdaBox.ElimBody

/-!
# `Lower` — the term-level λ□ → λ□ pass relation

`Lower Γ t t'` relates a term over the *specification* environment `Γ` to the term the
shipping eraser emits for it. It carries the compilation steps the source-level erasure
relation cannot state: the eliminator-to-`case` translation and the block-level fixpoint.

Fourteen arms: eleven congruence, `elimApp`, `fixConst`, `fixBody`. The relation is indexed
by `Γ` and by nothing else — no source term, no typing context, no run state — which is what
keeps it a statement about λ□ alone; `doc/rules-Lower.md` carries the arm-by-arm anchors.

Constructor introduction is **not** here: a constructor constant erases to `.construct iid k
[]` by `Erases.ctor` and its arguments arrive through `Erases.app`, so the pass sees a
`.construct` node already and the `construct`/`app` congruence arms relate it. Neither
η-expansion is here either; what they covered is a coverage restriction of the fragment, and
the eraser-side finding is `F-ETA2` in `doc/rework/03-DEV-FIX.md`.

Block premises are inlined into the two fix arms (the kernel rejects a structure premise
that mentions the inductive) and packaged afterwards as `LowerBlock`, read through
`Lower.fixConst'`/`Lower.fixBody'`. List premises are in the indexed form `hlen` plus
`∀ i, i < …`, since `List.Forall₂` as a premise is a nested-inductive occurrence.

`ConstToFVar` and `CloseConstAt` are here because `LowerBlock.hcl` needs them; the rest of
the fixpoint closure is `LowerFix.lean`. Box-freedom (`NoBox`) and the source-side inversion
kit are here because they are facts about `Lower` and its targets.

Two refutations are deleted with their subjects. `lower_correct_needs_ctorEta_guard`
exhibited a `ctorEta` pair whose source evaluates to a value the target cannot reach;
`lower_correct_needs_elimBody_head` refuted the pass simulation at an `elimEta` derivation
with an `ElimBody`-shaped head, at the empty environment and with every design guard proved.
Both arms and `ElimHeadOf`'s second disjunct are deleted, so neither statement has a
subject.
-/

namespace LeanToLambdaBox

open Lean (Name FVarId)

/-! ## Environment queries -/

/-- The λ□ inductive body the eraser emits for the block of `iid`, at the resolution the
target semantics reads it: `constructorArity` reads `npars` and the per-constructor field
counts, `isPropositionalInductive` reads `propositional`. -/
def IndBodyOf (iid : InductiveId) (np : Nat) (nfs : List Nat)
    (mib : MutualInductiveBody) : Prop :=
  mib.npars = np ∧ ∃ oib, mib.bodies[iid.idx]? = some oib ∧
    oib.propositional = false ∧ oib.ctors.map (·.nargs) = nfs

/-- `kn` is declared in `Γ` as an eliminator constant, **together with its block**: its body
is one of the two canonical `ElimBody` shapes for `iid` at `np` parameters, `dp` dropped
arguments and field arities `nfs`, and `iid`'s block is declared with those same numbers.
The second conjunct is what puts the emitted `.case` node's arity data in scope on the
target, where `constructorArity` and `isPropositionalInductive` read it. -/
def ElimDecl (Γ : GlobalDeclarations) (kn : Kername) (iid : InductiveId) (np dp : Nat)
    (nfs : List Nat) : Prop :=
  (∃ body, LBTerm.envLookup Γ kn = some (.constantDecl ⟨some body⟩) ∧
    ElimBody iid np dp nfs body) ∧
  (∃ mib, LBTerm.envLookup Γ iid.mutualBlockName = some (.inductiveDecl mib) ∧
    IndBodyOf iid np nfs mib)

/-- `kn` is declared in `Γ` with body `b`. -/
def DefnDecl (Γ : GlobalDeclarations) (kn : Kername) (b : LBTerm) : Prop :=
  LBTerm.envLookup Γ kn = some (.constantDecl ⟨some b⟩)

/-- `kn` is a key the pass consumes rather than emits: an eliminator constant, whose
occurrences become `.case` nodes and whose declaration is pruned. It guards `const` and
`fixConst`, since a pruned key would leave the target with a dangling reference and
`ElimDecl` implies `DefnDecl`. A constructor constant is **not** a runtime key: the pass
never sees one, because `Erases.ctor` already emits the `.construct` node. -/
def RuntimeKey (Γ : GlobalDeclarations) (kn : Kername) : Prop :=
  ∃ iid np dp nfs, ElimDecl Γ kn iid np dp nfs

/-- Every constant declared in `Γ` has a closed body. The specification environment holds
top-level bodies, so this is a fact about it, and it is what makes the two fix arms
commute with `shift` and `subst`. -/
def ClosedBodies (Γ : GlobalDeclarations) : Prop :=
  ∀ kn b, DefnDecl Γ kn b → LBClosed b 0

/-! ## Spine and telescope helpers -/

/-- The `n` de Bruijn indices of a freshly pushed telescope, outermost first:
`bvarsDesc n = [.bvar (n-1), …, .bvar 0]`. `ElimBody.fieldArgs` is the same run, written by
recursion; `fieldArgs_eq` is the bridge. -/
def bvarsDesc (n : Nat) : List LBTerm := (List.range n).reverse.map LBTerm.bvar

/-! ## `ConstToFVar` — block constants as fix variables -/

/-- Replace `.const kns[j]` by `.fvar ids[j]`, a congruence everywhere else. A `.fix`
node maps to itself: the source side of `Lower` declares no block member as a `.fix`, and
a nested one comes from another block, whose members are none of `kns`. -/
inductive ConstToFVar (kns : List Kername) (ids : List FVarId) : LBTerm → LBTerm → Prop where
  | box : ConstToFVar kns ids .box .box
  | bvar (i : Nat) : ConstToFVar kns ids (.bvar i) (.bvar i)
  | fvar (x : FVarId) : ConstToFVar kns ids (.fvar x) (.fvar x)
  | prim (p : PrimVal) : ConstToFVar kns ids (.prim p) (.prim p)
  | hit {j : Nat} {kn : Kername} {x : FVarId} (hkn : kns[j]? = some kn) (hx : ids[j]? = some x) :
      ConstToFVar kns ids (.const kn) (.fvar x)
  | miss {kn : Kername} (h : kn ∉ kns) : ConstToFVar kns ids (.const kn) (.const kn)
  | lambda {n n' : BinderName} {b b' : LBTerm} (h : ConstToFVar kns ids b b') :
      ConstToFVar kns ids (.lambda n b) (.lambda n' b')
  | letIn {n n' : BinderName} {v v' b b' : LBTerm} (hv : ConstToFVar kns ids v v')
      (hb : ConstToFVar kns ids b b') :
      ConstToFVar kns ids (.letIn n v b) (.letIn n' v' b')
  | app {f f' a a' : LBTerm} (hf : ConstToFVar kns ids f f') (ha : ConstToFVar kns ids a a') :
      ConstToFVar kns ids (.app f a) (.app f' a')
  | proj {p : ProjectionInfo} {e e' : LBTerm} (h : ConstToFVar kns ids e e') :
      ConstToFVar kns ids (.proj p e) (.proj p e')
  | construct {iid : InductiveId} {k : Nat} {args args' : List LBTerm}
      (hlen : args'.length = args.length)
      (h : ∀ i, i < args.length → ConstToFVar kns ids args[i]! args'[i]!) :
      ConstToFVar kns ids (.construct iid k args) (.construct iid k args')
  | «case» {ip : InductiveId × Nat} {d d' : LBTerm}
      {alts alts' : List (List BinderName × LBTerm)}
      (hd : ConstToFVar kns ids d d')
      (hlen : alts'.length = alts.length)
      (hn : ∀ i, i < alts.length → (alts'[i]!).1.length = (alts[i]!).1.length)
      (hb : ∀ i, i < alts.length → ConstToFVar kns ids (alts[i]!).2 (alts'[i]!).2) :
      ConstToFVar kns ids (.case ip d alts) (.case ip d' alts')
  | fix (defs : List (@FixDef LBTerm)) (i : Nat) :
      ConstToFVar kns ids (.fix defs i) (.fix defs i)

/-- The block closure of one body: rewrite the block's constants to its fix variables,
then abstract those variables with `closeFix`, which is exactly `mkDef`'s fold. -/
def CloseConstAt (kns : List Kername) (ids : List FVarId) (t u : LBTerm) : Prop :=
  ∃ t', ConstToFVar kns ids t t' ∧ u = closeFix ids 0 t'

/-! ## The relation -/

mutual

/-- The pass relation, fourteen arms. `Lower Γ t t'` says `t'` is a λ□ term the eraser
may emit for the specification term `t` over `Γ`. Deliberately non-deterministic at a
block member, where `const` and `fixConst` both apply. -/
inductive Lower (Γ : GlobalDeclarations) : LBTerm → LBTerm → Prop where
  | box : Lower Γ .box .box
  | bvar (i : Nat) : Lower Γ (.bvar i) (.bvar i)
  | fvar (x : FVarId) : Lower Γ (.fvar x) (.fvar x)
  | prim (p : PrimVal) : Lower Γ (.prim p) (.prim p)
  /-- A constant that is not a runtime key survives. Non-deterministic at a block member,
      where `fixConst` relates the same constant to the block's `.fix` node. -/
  | const {kn : Kername} (h : ¬ RuntimeKey Γ kn) : Lower Γ (.const kn) (.const kn)
  | lambda {n n' : BinderName} {b b' : LBTerm} (h : Lower Γ b b') :
      Lower Γ (.lambda n b) (.lambda n' b')
  | letIn {n n' : BinderName} {v v' b b' : LBTerm} (hv : Lower Γ v v') (hb : Lower Γ b b') :
      Lower Γ (.letIn n v b) (.letIn n' v' b')
  | app {f f' a a' : LBTerm} (hf : Lower Γ f f') (ha : Lower Γ a a') :
      Lower Γ (.app f a) (.app f' a')
  | proj {p : ProjectionInfo} {e e' : LBTerm} (h : Lower Γ e e') :
      Lower Γ (.proj p e) (.proj p e')
  | construct {iid : InductiveId} {k : Nat} {args args' : List LBTerm}
      (hlen : args'.length = args.length)
      (h : ∀ i, i < args.length → Lower Γ args[i]! args'[i]!) :
      Lower Γ (.construct iid k args) (.construct iid k args')
  /-- Branch arities are preserved: `iota_red` reads an alternative's binder count. -/
  | «case» {ip : InductiveId × Nat} {d d' : LBTerm}
      {alts alts' : List (List BinderName × LBTerm)}
      (hd : Lower Γ d d')
      (hlen : alts'.length = alts.length)
      (hn : ∀ i, i < alts.length → (alts'[i]!).1.length = (alts[i]!).1.length)
      (hb : ∀ i, i < alts.length → Lower Γ (alts[i]!).2 (alts'[i]!).2) :
      Lower Γ (.case ip d alts) (.case ip d' alts')
  /-- A saturated eliminator application becomes a `.case` node. The `dp` arguments before
      the discriminant are dropped, the minors are peeled into alternatives, and any
      over-application rides outside the node. The head is a `.const kn` whose declaration
      `ElimDecl` exhibits together with `iid`'s block. -/
  | elimApp {kn : Kername} {iid : InductiveId} {np dp : Nat} {nfs : List Nat}
      {pre : List LBTerm} {disc disc' : LBTerm} {minors : List LBTerm}
      {alts : List (List BinderName × LBTerm)} {extra extra' : List LBTerm}
      (hh : ElimDecl Γ kn iid np dp nfs)
      (hlen : pre.length = dp)
      (hmlen : minors.length = nfs.length)
      (halen : alts.length = nfs.length)
      (hmin : ∀ i, i < nfs.length → LowerAlt Γ nfs[i]! minors[i]! alts[i]!)
      (hdisc : Lower Γ disc disc')
      (hxlen : extra'.length = extra.length)
      (hx : ∀ i, i < extra.length → Lower Γ extra[i]! extra'[i]!) :
      Lower Γ (LBTerm.mkApps (.const kn) (pre ++ disc :: minors ++ extra))
              (LBTerm.mkApps (.case (iid, np) disc' alts) extra')
  /-- A block member's constant relates to the block's `.fix` node: the call site.
      `hnk` is what keeps a `.fix` image off an eliminator constant — `ElimDecl` implies
      `DefnDecl`, so nothing else does. The remaining premises are `LowerBlock`'s fields,
      inlined; read them through `Lower.fixConst'`. -/
  | fixConst {kn : Kername} {kns : List Kername} {bs bs' : List LBTerm} {ids : List FVarId}
      {defs : List (@FixDef LBTerm)} {j : Nat}
      (hb : bs.length = kns.length) (hb' : bs'.length = kns.length)
      (hd : defs.length = kns.length) (hnd : kns.Nodup)
      (hids : ids.Nodup) (hilen : ids.length = kns.length)
      (hfresh : ∀ x ∈ ids, ∀ i, i < kns.length → ¬ hasFVar x bs'[i]!)
      (hrarg : ∀ d ∈ defs, d.principalArgIdx = 0)
      (hdecl : ∀ i, i < kns.length → DefnDecl Γ kns[i]! bs[i]!)
      (hlow : ∀ i, i < kns.length → Lower Γ bs[i]! bs'[i]!)
      (hcl : ∀ i, i < kns.length → CloseConstAt kns ids bs'[i]! (defs[i]!).body)
      (hnk : ¬ RuntimeKey Γ kn) (hj : kns[j]? = some kn) :
      Lower Γ (.const kn) (.fix defs j)
  /-- The member's specification body relates to the same `.fix` node: the value side,
      which the δ step needs once the environment has unfolded the constant. Read it
      through `Lower.fixBody'`. -/
  | fixBody {b : LBTerm} {kns : List Kername} {bs bs' : List LBTerm} {ids : List FVarId}
      {defs : List (@FixDef LBTerm)} {j : Nat}
      (hb : bs.length = kns.length) (hb' : bs'.length = kns.length)
      (hd : defs.length = kns.length) (hnd : kns.Nodup)
      (hids : ids.Nodup) (hilen : ids.length = kns.length)
      (hfresh : ∀ x ∈ ids, ∀ i, i < kns.length → ¬ hasFVar x bs'[i]!)
      (hrarg : ∀ d ∈ defs, d.principalArgIdx = 0)
      (hdecl : ∀ i, i < kns.length → DefnDecl Γ kns[i]! bs[i]!)
      (hlow : ∀ i, i < kns.length → Lower Γ bs[i]! bs'[i]!)
      (hcl : ∀ i, i < kns.length → CloseConstAt kns ids bs'[i]! (defs[i]!).body)
      (hj : bs[j]? = some b) (hjl : j < defs.length) :
      Lower Γ b (.fix defs j)

/-- Branch peeling: a minor's λ-chain becomes an alternative's binder list. Names are
free; only their number — the field arity `iota_red` reads — is pinned. -/
inductive LowerAlt (Γ : GlobalDeclarations) :
    Nat → LBTerm → (List BinderName × LBTerm) → Prop where
  | done {m b : LBTerm} (h : Lower Γ m b) : LowerAlt Γ 0 m ([], b)
  | lam {nf : Nat} {n n' : BinderName} {m : LBTerm} {alt : List BinderName × LBTerm}
      (h : LowerAlt Γ nf m alt) :
      LowerAlt Γ (nf + 1) (.lambda n m) (n' :: alt.1, alt.2)

end

/-- The pointwise lift of `LowerAlt` over a block's field arities. -/
def LowerAlts (Γ : GlobalDeclarations) (nfs : List Nat) (minors : List LBTerm)
    (alts : List (List BinderName × LBTerm)) : Prop :=
  minors.length = nfs.length ∧ alts.length = nfs.length ∧
    ∀ i, i < nfs.length → LowerAlt Γ nfs[i]! minors[i]! alts[i]!

/-- The premises the two fix arms share, packaged. `ids` is **block-shared** — one list
for the whole block, as `visitMutual` mints it — because the freshness clause the fix
unfolding needs is against every `.fix defs j`. `hrarg` pins the emitted principal
argument index to `0`, which is the only value `mkDef` produces. -/
structure LowerBlock (Γ : GlobalDeclarations) (kns : List Kername) (bs bs' : List LBTerm)
    (ids : List FVarId) (defs : List (@FixDef LBTerm)) : Prop where
  hb : bs.length = kns.length
  hb' : bs'.length = kns.length
  hd : defs.length = kns.length
  hnd : kns.Nodup
  hids : ids.Nodup
  hilen : ids.length = kns.length
  hfresh : ∀ x ∈ ids, ∀ i, i < kns.length → ¬ hasFVar x bs'[i]!
  hrarg : ∀ d ∈ defs, d.principalArgIdx = 0
  hdecl : ∀ i, i < kns.length → DefnDecl Γ kns[i]! bs[i]!
  hlow : ∀ i, i < kns.length → Lower Γ bs[i]! bs'[i]!
  hcl : ∀ i, i < kns.length → CloseConstAt kns ids bs'[i]! (defs[i]!).body

/-- `Lower.fixConst` read through `LowerBlock`. -/
theorem Lower.fixConst' {Γ : GlobalDeclarations} {kns : List Kername} {bs bs' : List LBTerm}
    {ids : List FVarId} {defs : List (@FixDef LBTerm)} {j : Nat} {kn : Kername}
    (h : LowerBlock Γ kns bs bs' ids defs) (hnk : ¬ RuntimeKey Γ kn)
    (hj : kns[j]? = some kn) :
    Lower Γ (.const kn) (.fix defs j) :=
  .fixConst h.hb h.hb' h.hd h.hnd h.hids h.hilen h.hfresh h.hrarg h.hdecl h.hlow h.hcl hnk hj

/-- `Lower.fixBody` read through `LowerBlock`. -/
theorem Lower.fixBody' {Γ : GlobalDeclarations} {kns : List Kername} {bs bs' : List LBTerm}
    {ids : List FVarId} {defs : List (@FixDef LBTerm)} {j : Nat} {b : LBTerm}
    (h : LowerBlock Γ kns bs bs' ids defs) (hj : bs[j]? = some b) (hjl : j < defs.length) :
    Lower Γ b (.fix defs j) :=
  .fixBody h.hb h.hb' h.hd h.hnd h.hids h.hilen h.hfresh h.hrarg h.hdecl h.hlow h.hcl hj hjl

/-- `Lower.elimApp` read through `LowerAlts`. -/
theorem Lower.elimApp' {Γ : GlobalDeclarations} {kn : Kername} {iid : InductiveId}
    {np dp : Nat} {nfs : List Nat} {pre : List LBTerm} {disc disc' : LBTerm}
    {minors : List LBTerm} {alts : List (List BinderName × LBTerm)} {extra extra' : List LBTerm}
    (hh : ElimDecl Γ kn iid np dp nfs) (hlen : pre.length = dp)
    (hmin : LowerAlts Γ nfs minors alts) (hdisc : Lower Γ disc disc')
    (hxlen : extra'.length = extra.length)
    (hx : ∀ i, i < extra.length → Lower Γ extra[i]! extra'[i]!) :
    Lower Γ (LBTerm.mkApps (.const kn) (pre ++ disc :: minors ++ extra))
            (LBTerm.mkApps (.case (iid, np) disc' alts) extra') :=
  .elimApp hh hlen hmin.1 hmin.2.1 hmin.2.2 hdisc hxlen hx


/-! ## Indexed-list plumbing

The list premises are indexed (`hlen` plus `∀ i, i < …`), so the proofs move between
`l[i]!` and `∈ l` constantly; these four lemmas are that move. -/

/-- A `getElem!` at a valid index is a member. -/
theorem Lower.getElem!_mem {α : Type} [Inhabited α] {l : List α} {i : Nat}
    (h : i < l.length) : l[i]! ∈ l := by
  rw [getElem!_pos l i h]; exact List.getElem_mem h

/-- A member is a `getElem!` at a valid index. -/
theorem Lower.mem_getElem! {α : Type} [Inhabited α] {l : List α} {a : α} (h : a ∈ l) :
    ∃ i, i < l.length ∧ l[i]! = a := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  exact ⟨i, hi, getElem!_pos l i hi⟩

/-- `getElem!` commutes with `List.map` at a valid index. -/
theorem Lower.getElem!_map {α β : Type} [Inhabited α] [Inhabited β] (f : α → β)
    (l : List α) (i : Nat) (h : i < l.length) : (l.map f)[i]! = f l[i]! := by
  rw [getElem!_pos (l.map f) i (by simpa using h), getElem!_pos l i h, List.getElem_map]

/-- An index-wise property of a mapped list, read as a membership property. -/
theorem Lower.forall_mem_map {α β : Type} [Inhabited α] [Inhabited β] {f : α → β}
    {l : List α} {P : β → Prop} (h : ∀ i, i < l.length → P (f l[i]!)) :
    ∀ b ∈ l.map f, P b := by
  intro b hb
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
  obtain ⟨i, hi, rfl⟩ := Lower.mem_getElem! ha
  exact h i hi

/-! ## Spine, telescope and `bvarsDesc` laws -/

/-- `shift` distributes over an application spine. -/
theorem LBTerm.shift_mkApps (d c : Nat) (f : LBTerm) (args : List LBTerm) :
    LBTerm.shift d c (LBTerm.mkApps f args)
      = LBTerm.mkApps (LBTerm.shift d c f) (args.map (LBTerm.shift d c)) := by
  induction args generalizing f with
  | nil => rfl
  | cons a as ih => simpa [LBTerm.mkApps, LBTerm.shift] using ih (.app f a)

/-- `subst` distributes over an application spine. -/
theorem LBTerm.subst_mkApps (s : LBTerm) (d : Nat) (f : LBTerm) (args : List LBTerm) :
    LBTerm.subst s d (LBTerm.mkApps f args)
      = LBTerm.mkApps (LBTerm.subst s d f) (args.map (LBTerm.subst s d)) := by
  induction args generalizing f with
  | nil => rfl
  | cons a as ih => simpa [LBTerm.mkApps, LBTerm.subst] using ih (.app f a)

/-- Two shifts with disjoint roles commute: pushing `n` binders in at `b` moves the outer
cutoff `c` up by `n`. -/
theorem LBTerm.shift_shift_comm (d n b c : Nat) (h : b ≤ c) (t : LBTerm) :
    LBTerm.shift d (c + n) (LBTerm.shift n b t) = LBTerm.shift n b (LBTerm.shift d c t) := by
  induction t using LBTerm.recData generalizing b c with
  | hbox | hfvar | hconst | hprim => rfl
  | hbvar i =>
      rw [LBTerm.shift_bvar n b i]
      by_cases hib : i ≥ b
      · rw [if_pos hib, LBTerm.shift_bvar, LBTerm.shift_bvar]
        by_cases hic : i ≥ c
        · rw [if_pos (by omega), if_pos hic, LBTerm.shift_bvar, if_pos (by omega)]
          exact congrArg LBTerm.bvar (by omega)
        · rw [if_neg (by omega), if_neg hic, LBTerm.shift_bvar, if_pos hib]
      · rw [if_neg hib, LBTerm.shift_bvar, LBTerm.shift_bvar, if_neg (by omega),
          if_neg (by omega), LBTerm.shift_bvar, if_neg hib]
  | hlam nm b' ih =>
      have e : c + n + 1 = (c + 1) + n := by omega
      simp only [LBTerm.shift, e, ih (b + 1) (c + 1) (by omega)]
  | hletIn nm v b' ihv ihb =>
      have e : c + n + 1 = (c + 1) + n := by omega
      simp only [LBTerm.shift, e, ihv b c h, ihb (b + 1) (c + 1) (by omega)]
  | happ f a ihf iha => simp only [LBTerm.shift, ihf b c h, iha b c h]
  | hproj p e ih => simp only [LBTerm.shift, ih b c h]
  | hconstruct iid ci args ih =>
      simp only [LBTerm.shift, LBTerm.shiftArgs_eq_map, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha; simp only [Function.comp]; exact ih a ha b c h
  | hcase info discr alts ihd iha =>
      simp only [LBTerm.shift, LBTerm.shiftAlts_eq_map, List.map_map, ihd b c h]
      congr 1
      apply List.map_congr_left
      intro a ha; simp only [Function.comp]
      have e : c + n + a.1.length = (c + a.1.length) + n := by omega
      rw [e, iha a ha (b + a.1.length) (c + a.1.length) (by omega)]
  | hfix defs i ih =>
      simp only [LBTerm.shift, LBTerm.shiftDefs_eq_map, List.map_map, List.length_map]
      congr 1
      apply List.map_congr_left
      intro a ha; simp only [Function.comp]
      have e : c + n + defs.length = (c + defs.length) + n := by omega
      rw [e, ih a ha (b + defs.length) (c + defs.length) (by omega)]

/-- `bvarsDesc n` has `n` entries. -/
@[simp] theorem bvarsDesc_length (n : Nat) : (bvarsDesc n).length = n := by
  simp [bvarsDesc]

/-- Every entry of `bvarsDesc n` is a de Bruijn index below `n`. -/
theorem bvarsDesc_mem {n : Nat} {t : LBTerm} (h : t ∈ bvarsDesc n) :
    ∃ i, i < n ∧ t = .bvar i := by
  simp only [bvarsDesc, List.mem_map, List.mem_reverse, List.mem_range] at h
  obtain ⟨i, hi, rfl⟩ := h
  exact ⟨i, hi, rfl⟩

/-- A telescope's own arguments are closed at its length. -/
theorem lbClosed_bvarsDesc {n : Nat} : ∀ t ∈ bvarsDesc n, LBClosed t n := by
  intro t ht
  obtain ⟨i, hi, rfl⟩ := bvarsDesc_mem ht
  simpa using hi

/-- Shifting above a telescope leaves its own arguments alone. -/
theorem shift_bvarsDesc {n c : Nat} (h : n ≤ c) (d : Nat) :
    (bvarsDesc n).map (LBTerm.shift d c) = bvarsDesc n := by
  refine List.map_congr_left ?_ |>.trans (List.map_id _)
  intro t ht
  obtain ⟨i, hi, rfl⟩ := bvarsDesc_mem ht
  simp only [id, LBTerm.shift]
  rw [if_neg (by omega)]

/-- Substituting above a telescope leaves its own arguments alone. -/
theorem subst_bvarsDesc {n d : Nat} (h : n ≤ d) (s : LBTerm) :
    (bvarsDesc n).map (LBTerm.subst s d) = bvarsDesc n := by
  refine List.map_congr_left ?_ |>.trans (List.map_id _)
  intro t ht
  obtain ⟨i, hi, rfl⟩ := bvarsDesc_mem ht
  simp only [id, LBTerm.subst]
  rw [if_pos (by omega)]

/-- `closeFix` at base `0` abstracts a closed body into one closed at the block's width. -/
theorem lbClosed_closeFix {t : LBTerm} (ids : List FVarId) (h : LBClosed t 0) :
    LBClosed (closeFix ids 0 t) ids.length := by
  rw [closeFix, closeFixFold_eq_foldl]
  exact lbClosed_foldl_zipIdx ids h

/-- Rewriting block constants to fix variables preserves closedness: both `.const` and
`.fvar` bind no index. -/
theorem ConstToFVar.closed {kns : List Kername} {ids : List FVarId} {t t' : LBTerm}
    (h : ConstToFVar kns ids t t') {k : Nat} (hc : LBClosed t k) : LBClosed t' k := by
  induction h generalizing k with
  | box | bvar | fvar | prim | hit | miss | fix => exact hc
  | lambda _ ih => exact ih hc
  | letIn _ _ ihv ihb => exact ⟨ihv hc.1, ihb hc.2⟩
  | app _ _ ihf iha => exact ⟨ihf hc.1, iha hc.2⟩
  | proj _ ih => exact ih hc
  | construct hlen _ ih =>
      rw [LBClosed_construct, LBClosedArgs_iff] at *
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Lower.mem_getElem! ha
      exact ih i (by omega) (hc _ (Lower.getElem!_mem (by omega)))
  | @«case» ip dd dd' alts alts' _ hlen hn _ ihd ihb =>
      rw [LBClosed_case, LBClosedAlts_iff] at *
      refine ⟨ihd hc.1, ?_⟩
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Lower.mem_getElem! ha
      have hi' : i < alts.length := by omega
      rw [hn i hi']
      exact ihb i hi' (hc.2 _ (Lower.getElem!_mem hi'))


/-! ## Closedness -/

/-- A block's `.fix` node is closed once every lowered body is: `hcl` writes each
definition body as `closeFix ids 0` of a `ConstToFVar` image, and `closeFix` at base `0`
closes exactly the block's own width. -/
theorem lbClosed_fix_of_block {kns : List Kername} {bs' : List LBTerm} {ids : List FVarId}
    {defs : List (@FixDef LBTerm)} {j : Nat}
    (hd : defs.length = kns.length) (hilen : ids.length = kns.length)
    (hcl : ∀ i, i < kns.length → CloseConstAt kns ids bs'[i]! (defs[i]!).body)
    (hbs : ∀ i, i < kns.length → LBClosed bs'[i]! 0) (k : Nat) :
    LBClosed (LBTerm.fix defs j) k := by
  rw [LBClosed_fix, LBClosedDefs_iff]
  intro fd hfd
  obtain ⟨i, hi, rfl⟩ := Lower.mem_getElem! hfd
  have hik : i < kns.length := by omega
  obtain ⟨t', hct, heq⟩ := hcl i hik
  rw [heq]
  exact (lbClosed_closeFix ids (hct.closed (hbs i hik))).mono (by omega)

/-- `Lower` preserves closedness at every bound, given closed specification bodies: the
two fix arms read their definitions off `Γ`, and nothing else in the relation invents an
index. -/
theorem Lower.closed {Γ : GlobalDeclarations} (hΓ : ClosedBodies Γ) {s t : LBTerm}
    (h : Lower Γ s t) : ∀ k, LBClosed s k → LBClosed t k := by
  induction h using Lower.rec
    (motive_2 := fun nf m alt _ => ∀ k, LBClosed m k → LBClosed alt.2 (k + alt.1.length)) with
  | box | bvar | fvar | prim | const => exact fun _ hc => hc
  | lambda _ ih => exact fun k hc => ih (k + 1) hc
  | letIn _ _ ihv ihb => exact fun k hc => ⟨ihv k hc.1, ihb (k + 1) hc.2⟩
  | app _ _ ihf iha => exact fun k hc => ⟨ihf k hc.1, iha k hc.2⟩
  | proj _ ih => exact fun k hc => ih k hc
  | @construct iid ci args args' hlen _ ih =>
      intro k hc
      rw [LBClosed_construct, LBClosedArgs_iff] at *
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Lower.mem_getElem! ha
      exact ih i (by omega) k (hc _ (Lower.getElem!_mem (by omega)))
  | @«case» ip dd dd' alts alts' _ hlen hn _ ihd ihb =>
      intro k hc
      rw [LBClosed_case, LBClosedAlts_iff] at *
      refine ⟨ihd k hc.1, ?_⟩
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Lower.mem_getElem! ha
      have hi' : i < alts.length := by omega
      rw [hn i hi']
      exact ihb i hi' _ (hc.2 _ (Lower.getElem!_mem hi'))
  | @elimApp kn iid np dp nfs pre disc disc' minors alts extra extra'
      _ hlen hmlen halen _ _ hxlen _ ihmin ihd ihx =>
      intro k hc
      have hargs := LBClosed.mkApps_inv hc
      have halts : LBClosedAlts alts k := by
        rw [LBClosedAlts_iff]
        intro a ha
        obtain ⟨i, hi, rfl⟩ := Lower.mem_getElem! ha
        have hi' : i < nfs.length := by omega
        have hm : minors[i]! ∈ minors := Lower.getElem!_mem (by omega)
        exact ihmin i hi' k (hargs _ (List.mem_append_left extra
          (List.mem_append_right pre (List.mem_cons_of_mem _ hm))))
      have hhead : LBClosed (LBTerm.case (iid, np) disc' alts) k :=
        ⟨ihd k (hargs disc (by simp)), halts⟩
      refine LBClosed.mkApps hhead ?_
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Lower.mem_getElem! ha
      have hm : extra[i]! ∈ extra := Lower.getElem!_mem (by omega)
      exact ihx i (by omega) k (hargs _ (List.mem_append_right _ hm))
  | @fixConst kn kns bs bs' ids defs j hb hb' hdl _ _ hilen _ _ hdecl _ hcl _ hj ih =>
      intro k _
      exact lbClosed_fix_of_block hdl hilen hcl
        (fun i hi => ih i hi 0 (hΓ _ _ (hdecl i hi))) k
  | @fixBody b kns bs bs' ids defs j hb hb' hdl _ _ hilen _ _ hdecl _ hcl hj hjl ih =>
      intro k _
      exact lbClosed_fix_of_block hdl hilen hcl
        (fun i hi => ih i hi 0 (hΓ _ _ (hdecl i hi))) k
  | done _ ih =>
      rename_i k hc
      simpa using ih k hc
  | @lam nf n n' m alt _ ih =>
      rename_i k hc
      have hb := ih (k + 1) hc
      simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb


/-! ## Commutation with the de Bruijn operations -/

/-- `getElem?` pins both the index and the `getElem!`. -/
theorem Lower.getElem!_of_getElem? {α : Type} [Inhabited α] {l : List α} {i : Nat} {a : α}
    (h : l[i]? = some a) : i < l.length ∧ l[i]! = a := by
  rcases Nat.lt_or_ge i l.length with hi | hi
  · refine ⟨hi, ?_⟩
    rw [getElem!_pos l i hi]
    rw [List.getElem?_eq_getElem hi] at h
    exact Option.some.inj h
  · rw [List.getElem?_eq_none hi] at h
    exact absurd h (by simp)

/-- Pushing a telescope's shift past an outer one, on a whole argument list. -/
theorem map_shift_shift_comm (d n c : Nat) (l : List LBTerm) :
    (l.map (LBTerm.shift n 0)).map (LBTerm.shift d (c + n))
      = (l.map (LBTerm.shift d c)).map (LBTerm.shift n 0) := by
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro a _
  simp only [Function.comp]
  exact LBTerm.shift_shift_comm d n 0 c (Nat.zero_le c) a

/-- `Lower` commutes with `shift`: the pass never reads a de Bruijn index, and its two
fix arms rest on declarations that are closed. -/
theorem Lower.shift_comm {Γ : GlobalDeclarations} (hΓ : ClosedBodies Γ)
    {s t : LBTerm} (h : Lower Γ s t) :
    ∀ d c, Lower Γ (LBTerm.shift d c s) (LBTerm.shift d c t) := by
  induction h using Lower.rec
    (motive_2 := fun nf m alt _ => ∀ d c,
      LowerAlt Γ nf (LBTerm.shift d c m) (alt.1, LBTerm.shift d (c + alt.1.length) alt.2)) with
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
  | @elimApp kn iid np dp nfs pre disc disc' minors alts extra extra'
      hh hlen hmlen halen _ _ hxlen _ ihmin ihd ihx =>
      intro d c
      rw [LBTerm.shift_mkApps, LBTerm.shift_mkApps]
      simp only [List.map_append, List.map_cons, LBTerm.shift, LBTerm.shiftAlts_eq_map]
      refine .elimApp hh (by simp [hlen]) (by simp [hmlen]) (by simp [halen]) ?_ (ihd d c)
        (by simp [hxlen]) ?_
      · intro i hi
        rw [Lower.getElem!_map _ _ i (by omega), Lower.getElem!_map _ _ i (by omega)]
        exact ihmin i hi d c
      · intro i hi
        rw [List.length_map] at hi
        rw [Lower.getElem!_map _ _ i hi, Lower.getElem!_map _ _ i (by omega)]
        exact ihx i hi d c
  | @fixConst kn kns bs bs' ids defs j hb hb' hdl hnd hids hilen hfresh hrarg hdecl hlow hcl
      hnk hj ih =>
      intro d c
      have hfx : LBClosed (LBTerm.fix defs j) 0 :=
        lbClosed_fix_of_block hdl hilen hcl
          (fun i hi => (Lower.closed hΓ (hlow i hi)) 0 (hΓ _ _ (hdecl i hi))) 0
      rw [show LBTerm.shift d c (LBTerm.const kn) = .const kn from rfl,
        hfx.shift_eq (Nat.zero_le c) d]
      exact .fixConst hb hb' hdl hnd hids hilen hfresh hrarg hdecl hlow hcl hnk hj
  | @fixBody b kns bs bs' ids defs j hb hb' hdl hnd hids hilen hfresh hrarg hdecl hlow hcl
      hj hjl ih =>
      intro d c
      obtain ⟨hjb, hjeq⟩ := Lower.getElem!_of_getElem? hj
      have hjk : j < kns.length := by omega
      have hbcl : LBClosed b 0 := by
        have := hΓ _ _ (hdecl j hjk)
        rwa [hjeq] at this
      have hfx : LBClosed (LBTerm.fix defs j) 0 :=
        lbClosed_fix_of_block hdl hilen hcl
          (fun i hi => (Lower.closed hΓ (hlow i hi)) 0 (hΓ _ _ (hdecl i hi))) 0
      rw [hbcl.shift_eq (Nat.zero_le c) d, hfx.shift_eq (Nat.zero_le c) d]
      exact .fixBody hb hb' hdl hnd hids hilen hfresh hrarg hdecl hlow hcl hj hjl
  | done _ ih =>
      rename_i d c
      simpa using LowerAlt.done (ih d c)
  | @lam nf n n' m alt _ ih =>
      rename_i d c
      have hih := ih d (c + 1)
      simp only [LBTerm.shift, List.length_cons]
      have e : c + (alt.1.length + 1) = (c + 1) + alt.1.length := by omega
      rw [e]
      exact .lam hih


/-- Pushing a telescope's shift past a substitution, on a whole argument list. -/
theorem map_subst_shift_comm (a : LBTerm) (d n : Nat) (l : List LBTerm) :
    (l.map (LBTerm.shift n 0)).map (LBTerm.subst a (d + n))
      = (l.map (LBTerm.subst a d)).map (LBTerm.shift n 0) := by
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro x _
  simp only [Function.comp]
  exact LBTerm.subst_shift_comm a 0 d n (d + n) (Nat.zero_le d) rfl x

/-- `Lower` commutes with substitution, the substituted terms being related themselves.
This is the law the β, ζ and ι steps of a forward simulation consume. -/
theorem Lower.subst_comm {Γ : GlobalDeclarations} (hΓ : ClosedBodies Γ)
    {a a' : LBTerm} (ha : Lower Γ a a') {s t : LBTerm} (h : Lower Γ s t) :
    ∀ d, Lower Γ (LBTerm.subst a d s) (LBTerm.subst a' d t) := by
  induction h using Lower.rec
    (motive_2 := fun nf m alt _ => ∀ d,
      LowerAlt Γ nf (LBTerm.subst a d m)
        (alt.1, LBTerm.subst a' (d + alt.1.length) alt.2)) with
  | box => exact fun _ => .box
  | bvar i =>
      intro d
      simp only [LBTerm.subst]
      split
      · exact .bvar _
      · split
        · exact Lower.shift_comm hΓ ha d 0
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
  | @elimApp kn iid np dp nfs pre disc disc' minors alts extra extra'
      hh hlen hmlen halen _ _ hxlen _ ihmin ihd ihx =>
      intro d
      rw [LBTerm.subst_mkApps, LBTerm.subst_mkApps]
      simp only [List.map_append, List.map_cons, LBTerm.subst, LBTerm.substAlts_eq_map]
      refine .elimApp hh (by simp [hlen]) (by simp [hmlen]) (by simp [halen]) ?_ (ihd d)
        (by simp [hxlen]) ?_
      · intro i hi
        rw [Lower.getElem!_map _ _ i (by omega), Lower.getElem!_map _ _ i (by omega)]
        exact ihmin i hi d
      · intro i hi
        rw [List.length_map] at hi
        rw [Lower.getElem!_map _ _ i hi, Lower.getElem!_map _ _ i (by omega)]
        exact ihx i hi d
  | @fixConst kn kns bs bs' ids defs j hb hb' hdl hnd hids hilen hfresh hrarg hdecl hlow hcl
      hnk hj ih =>
      intro d
      have hfx : LBClosed (LBTerm.fix defs j) 0 :=
        lbClosed_fix_of_block hdl hilen hcl
          (fun i hi => (Lower.closed hΓ (hlow i hi)) 0 (hΓ _ _ (hdecl i hi))) 0
      rw [show LBTerm.subst a d (LBTerm.const kn) = .const kn from rfl,
        hfx.subst_eq (Nat.zero_le d) a']
      exact .fixConst hb hb' hdl hnd hids hilen hfresh hrarg hdecl hlow hcl hnk hj
  | @fixBody b kns bs bs' ids defs j hb hb' hdl hnd hids hilen hfresh hrarg hdecl hlow hcl
      hj hjl ih =>
      intro d
      obtain ⟨hjb, hjeq⟩ := Lower.getElem!_of_getElem? hj
      have hjk : j < kns.length := by omega
      have hbcl : LBClosed b 0 := by
        have hb0 := hΓ _ _ (hdecl j hjk)
        rwa [hjeq] at hb0
      have hfx : LBClosed (LBTerm.fix defs j) 0 :=
        lbClosed_fix_of_block hdl hilen hcl
          (fun i hi => (Lower.closed hΓ (hlow i hi)) 0 (hΓ _ _ (hdecl i hi))) 0
      rw [hbcl.subst_eq (Nat.zero_le d) a, hfx.subst_eq (Nat.zero_le d) a']
      exact .fixBody hb hb' hdl hnd hids hilen hfresh hrarg hdecl hlow hcl hj hjl
  | done _ ih =>
      rename_i d
      simpa using LowerAlt.done (ih d)
  | @lam nf n n' m alt _ ih =>
      rename_i d
      have hih := ih (d + 1)
      simp only [LBTerm.subst, List.length_cons]
      have e : d + (alt.1.length + 1) = (d + 1) + alt.1.length := by omega
      rw [e]
      exact .lam hih


/-! ## Spine and telescope shapes -/

/-- A non-empty spine is an application. -/
theorem mkApps_cons_is_app (f x : LBTerm) (xs : List LBTerm) :
    ∃ g b, LBTerm.mkApps f (x :: xs) = .app g b := by
  induction xs generalizing f x with
  | nil => exact ⟨f, x, rfl⟩
  | cons y ys ih => exact ih (.app f x) y

/-- A spine is its own head or an application. -/
theorem mkApps_head_or_app (f : LBTerm) (args : List LBTerm) :
    LBTerm.mkApps f args = f ∨ ∃ g b, LBTerm.mkApps f args = .app g b := by
  rcases args with _ | ⟨x, xs⟩
  · exact .inl rfl
  · exact .inr (mkApps_cons_is_app f x xs)

/-- A non-empty telescope is a lambda. -/
theorem mkLambdas_is_lambda {ns : List BinderName} (h : ns ≠ []) (body : LBTerm) :
    ∃ n b, mkLambdas ns body = .lambda n b := by
  cases ns with
  | nil => exact absurd rfl h
  | cons n ns => exact ⟨n, mkLambdas ns body, rfl⟩

/-! ## Inversion -/

/-- `Lower` relates only `.box` to `.box`: no arm introduces or erases a box. -/
theorem Lower.target_box {Γ : GlobalDeclarations} {s t : LBTerm} (h : Lower Γ s t)
    (ht : t = .box) : s = .box := by
  cases h with
  | box => rfl
  | bvar | fvar | prim | const | lambda | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion ht
  | fixConst | fixBody => exact LBTerm.noConfusion ht
  | @elimApp kn iid np dp nfs pre disc disc' minors alts extra extra' =>
      rcases mkApps_head_or_app (LBTerm.case (iid, np) disc' alts) extra' with he | ⟨g, b, he⟩ <;>
        rw [he] at ht <;> exact LBTerm.noConfusion ht

/-- `Lower` relates only a de Bruijn index to itself: passes do not renumber. -/
theorem Lower.target_bvar {Γ : GlobalDeclarations} {s t : LBTerm} {i : Nat} (h : Lower Γ s t)
    (ht : t = .bvar i) : s = .bvar i := by
  cases h with
  | bvar j => exact ht ▸ rfl
  | box | fvar | prim | const | lambda | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion ht
  | fixConst | fixBody => exact LBTerm.noConfusion ht
  | @elimApp kn iid np dp nfs pre disc disc' minors alts extra extra' =>
      rcases mkApps_head_or_app (LBTerm.case (iid, np) disc' alts) extra' with he | ⟨g, b, he⟩ <;>
        rw [he] at ht <;> exact LBTerm.noConfusion ht

/-- `Lower` relates only a free variable to itself. -/
theorem Lower.target_fvar {Γ : GlobalDeclarations} {s t : LBTerm} {x : Lean.FVarId}
    (h : Lower Γ s t) (ht : t = .fvar x) : s = .fvar x := by
  cases h with
  | fvar y => exact ht ▸ rfl
  | box | bvar | prim | const | lambda | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion ht
  | fixConst | fixBody => exact LBTerm.noConfusion ht
  | @elimApp kn iid np dp nfs pre disc disc' minors alts extra extra' =>
      rcases mkApps_head_or_app (LBTerm.case (iid, np) disc' alts) extra' with he | ⟨g, b, he⟩ <;>
        rw [he] at ht <;> exact LBTerm.noConfusion ht

/-- `Lower` relates only a primitive to itself. -/
theorem Lower.target_prim {Γ : GlobalDeclarations} {s t : LBTerm} {p : PrimVal}
    (h : Lower Γ s t) (ht : t = .prim p) : s = .prim p := by
  cases h with
  | prim q => exact ht ▸ rfl
  | box | bvar | fvar | const | lambda | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion ht
  | fixConst | fixBody => exact LBTerm.noConfusion ht
  | @elimApp kn iid np dp nfs pre disc disc' minors alts extra extra' =>
      rcases mkApps_head_or_app (LBTerm.case (iid, np) disc' alts) extra' with he | ⟨g, b, he⟩ <;>
        rw [he] at ht <;> exact LBTerm.noConfusion ht

/-- A constant in the target comes from the same constant, and is not a runtime key. -/
theorem Lower.target_const {Γ : GlobalDeclarations} {s t : LBTerm} {kn : Kername}
    (h : Lower Γ s t) (ht : t = .const kn) : s = .const kn ∧ ¬ RuntimeKey Γ kn := by
  cases h with
  | @const kn' hk =>
      have he : kn' = kn := by injection ht
      exact ⟨by rw [he], by rw [← he]; exact hk⟩
  | box | bvar | fvar | prim | lambda | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion ht
  | fixConst | fixBody => exact LBTerm.noConfusion ht
  | @elimApp kn iid np dp nfs pre disc disc' minors alts extra extra' =>
      rcases mkApps_head_or_app (LBTerm.case (iid, np) disc' alts) extra' with he | ⟨g, b, he⟩ <;>
        rw [he] at ht <;> exact LBTerm.noConfusion ht

/-- A `.fix` in the target comes from one of the two fix arms, and carries a whole
`LowerBlock`: either the member's constant or its specification body. -/
theorem Lower.target_fix {Γ : GlobalDeclarations} {s t : LBTerm}
    {defs : List (@FixDef LBTerm)} {j : Nat} (h : Lower Γ s t) (ht : t = .fix defs j) :
    ∃ kns bs bs' ids, LowerBlock Γ kns bs bs' ids defs ∧
      ((∃ kn, s = .const kn ∧ kns[j]? = some kn) ∨ (bs[j]? = some s ∧ j < defs.length)) := by
  cases h with
  | box | bvar | fvar | prim | const | lambda | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion ht
  | @elimApp kn iid np dp nfs pre disc disc' minors alts extra extra' =>
      rcases mkApps_head_or_app (LBTerm.case (iid, np) disc' alts) extra' with he | ⟨g, b, he⟩ <;>
        rw [he] at ht <;> exact LBTerm.noConfusion ht
  | @fixConst kn kns bs bs' ids defs₀ j₀ hb hb' hdl hnd hids hilen hfresh hrarg hdecl hlow
      hcl hnk hj =>
      injection ht with hdefs hjj
      subst hdefs; subst hjj
      exact ⟨kns, bs, bs', ids, ⟨hb, hb', hdl, hnd, hids, hilen, hfresh, hrarg, hdecl, hlow, hcl⟩,
        .inl ⟨kn, rfl, hj⟩⟩
  | @fixBody b kns bs bs' ids defs₀ j₀ hb hb' hdl hnd hids hilen hfresh hrarg hdecl hlow
      hcl hj hjl =>
      injection ht with hdefs hjj
      subst hdefs; subst hjj
      exact ⟨kns, bs, bs', ids, ⟨hb, hb', hdl, hnd, hids, hilen, hfresh, hrarg, hdecl, hlow, hcl⟩,
        .inr ⟨hj, hjl⟩⟩

/-- A `LowerAlt` pins the alternative's binder count to the field arity, nothing else. -/
theorem LowerAlt.arity {Γ : GlobalDeclarations} {nf : Nat} {m : LBTerm}
    {alt : List BinderName × LBTerm} (h : LowerAlt Γ nf m alt) : alt.1.length = nf := by
  induction h using LowerAlt.rec (motive_1 := fun _ _ _ => True) with
  | done => rfl
  | lam _ ih => simpa using ih
  | box | bvar | fvar | prim | const | lambda | letIn | app | proj | construct | «case»
  | elimApp | fixConst | fixBody => trivial


/-- A constructor node in the target comes from the same node, argument by argument: with
constructor introduction moved to `Erases.ctor`, no arm builds one out of a constant. -/
theorem Lower.target_construct {Γ : GlobalDeclarations} {s t : LBTerm} {iid : InductiveId}
    {k : Nat} {args' : List LBTerm} (h : Lower Γ s t) (ht : t = .construct iid k args') :
    ∃ args, s = .construct iid k args ∧ args'.length = args.length ∧
      ∀ i, i < args.length → Lower Γ args[i]! args'[i]! := by
  cases h with
  | box | bvar | fvar | prim | const | lambda | letIn | app | proj | «case» =>
      exact LBTerm.noConfusion ht
  | fixConst | fixBody => exact LBTerm.noConfusion ht
  | @construct iid₀ k₀ args args₀ hlen hargs =>
      injection ht with hi hk hargs'
      subst hi; subst hk; subst hargs'
      exact ⟨args, rfl, hlen, hargs⟩
  | @elimApp kn iid np dp nfs pre disc disc' minors alts extra extra' =>
      rcases mkApps_head_or_app (LBTerm.case (iid, np) disc' alts) extra' with he | ⟨g, b, he⟩ <;>
        rw [he] at ht <;> exact LBTerm.noConfusion ht

/-- Spine congruence: `Lower` lifts from a head and its arguments to the whole
application spine. -/
theorem Lower.mkApps {Γ : GlobalDeclarations} {f f' : LBTerm} (hf : Lower Γ f f')
    {args args' : List LBTerm} (hlen : args'.length = args.length)
    (h : ∀ i, i < args.length → Lower Γ args[i]! args'[i]!) :
    Lower Γ (LBTerm.mkApps f args) (LBTerm.mkApps f' args') := by
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
      have hx : Lower Γ x y := by
        have h0 := h 0 (by simp)
        rwa [getElem!_pos (x :: xs) 0 (by simp), getElem!_pos (y :: ys) 0 (by simp)] at h0
      refine ih (.app hf hx) hlen' ?_
      intro i hi
      have hi' := h (i + 1) (by simp only [List.length_cons]; omega)
      rwa [getElem!_pos (x :: xs) (i + 1) (by simp only [List.length_cons]; omega),
        getElem!_pos (y :: ys) (i + 1) (by simp only [List.length_cons]; omega),
        List.getElem_cons_succ, List.getElem_cons_succ,
        ← getElem!_pos xs i hi, ← getElem!_pos ys i (by omega)] at hi'

/-! ## Box-freedom

`NoBox` is what the capstone asks of the *lowered* value while the first-order theorem
proves it of the erasure. Its transport along `Lower` needs a premise excluding a `.fix`
in the target: `LowerFix.lean`'s `noBox_lower_needs_noFix` is the counterexample without
one. -/

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
        refine ⟨hf, fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ha
        · exact has x hx
      · rintro ⟨hf, has⟩
        exact ⟨⟨hf, has a (by simp)⟩, fun x hx => has x (by simp [hx])⟩

/-- Box-freedom of a telescope is box-freedom of its body. -/
theorem NoBox_mkLambdas (ns : List BinderName) (b : LBTerm) :
    NoBox (mkLambdas ns b) ↔ NoBox b := by
  induction ns with
  | nil => rfl
  | cons n ns ih => rw [mkLambdas, NoBox_lambda, ih]

/-- A telescope's own argument run is box-free. -/
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

/-! ## Small list and shape helpers

The list premises are indexed, so the proofs move between `l[i]!` and `∈ l` constantly, and
a spine inversion needs `getElem!` through `drop`, `reverse` and a one-element append. -/

/-- The last entry of a one-element append. -/
theorem getElem!_append_singleton {α : Type} [Inhabited α] (l : List α) (x : α) :
    (l ++ [x])[l.length]! = x := by
  rw [getElem!_pos (l ++ [x]) l.length (by simp)]
  simp

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
theorem Lower.drop_reverse {Γ : GlobalDeclarations} {l l' : List LBTerm} (m : Nat)
    (hlen : l'.length = l.length) (h : ∀ i, i < l.length → Lower Γ l[i]! l'[i]!) :
    ((l'.drop m).reverse).length = ((l.drop m).reverse).length ∧
      ∀ i, i < ((l.drop m).reverse).length →
        Lower Γ ((l.drop m).reverse)[i]! ((l'.drop m).reverse)[i]! := by
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

/-- Extending a pointwise-related pair of lists by one related pair. -/
theorem Lower.concat {Γ : GlobalDeclarations} {l l' : List LBTerm} {x y : LBTerm}
    (hlen : l'.length = l.length) (h : ∀ i, i < l.length → Lower Γ l[i]! l'[i]!)
    (hxy : Lower Γ x y) :
    (l' ++ [y]).length = (l ++ [x]).length ∧
      ∀ i, i < (l ++ [x]).length → Lower Γ (l ++ [x])[i]! (l' ++ [y])[i]! := by
  refine ⟨by simp [hlen], fun i hi => ?_⟩
  simp only [List.length_append, List.length_cons, List.length_nil] at hi
  rcases Nat.lt_or_ge i l.length with hlt | hge
  · rw [getElem!_pos (l ++ [x]) i (by simp; omega), getElem!_pos (l' ++ [y]) i (by simp; omega),
      List.getElem_append_left hlt, List.getElem_append_left (by omega),
      ← getElem!_pos l i hlt, ← getElem!_pos l' i (by omega)]
    exact h i hlt
  · obtain rfl : i = l.length := by omega
    rw [getElem!_append_singleton l x, ← hlen, getElem!_append_singleton l' y]
    exact hxy

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

/-- A `true` `isLambda` exhibits the λ. -/
theorem isLambda_eq_true {t : LBTerm} (h : isLambda t = true) : ∃ n b, t = .lambda n b := by
  cases t <;> simp [isLambda] at h ⊢

/-- Substituting does not change a λ head. -/
theorem isLambda_substList : ∀ (l : List LBTerm) {t : LBTerm}, isLambda t = true →
    isLambda (LBTerm.substList l t) = true
  | [], t, h => h
  | s :: l, t, h => by
      obtain ⟨n, b, rfl⟩ := isLambda_eq_true h
      exact isLambda_substList l (by rfl)

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

/-- A spine whose value is not an application is its head, applied to nothing. -/
theorem mkApps_eq_of_ne_app {f u : LBTerm} {args : List LBTerm}
    (hu : ∀ g b, u ≠ .app g b) (h : LBTerm.mkApps f args = u) : args = [] ∧ f = u := by
  cases args with
  | nil => exact ⟨rfl, h⟩
  | cons a as =>
      obtain ⟨g, b, he⟩ := mkApps_cons_is_app f a as
      exact absurd (h.symm.trans he) (hu g b)

/-- `Lower` commutes with a whole substitution list. -/
theorem Lower.substList_comm {Γ : GlobalDeclarations} (hΓ : ClosedBodies Γ) :
    ∀ {l l' : List LBTerm}, l'.length = l.length →
      (∀ i, i < l.length → Lower Γ l[i]! l'[i]!) →
      ∀ {s t : LBTerm}, Lower Γ s t →
        Lower Γ (LBTerm.substList l s) (LBTerm.substList l' t)
  | [], l', hlen, _, s, t, h => by
      obtain rfl : l' = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      exact h
  | x :: xs, l', hlen, hall, s, t, h => by
      obtain ⟨y, ys, rfl⟩ : ∃ y ys, l' = y :: ys := by
        rcases l' with _ | ⟨y, ys⟩
        · simp at hlen
        · exact ⟨y, ys, rfl⟩
      have hlen' : ys.length = xs.length := by simpa using hlen
      have hx : Lower Γ x y := by
        have h0 := hall 0 (by simp)
        rwa [getElem!_pos (x :: xs) 0 (by simp), getElem!_pos (y :: ys) 0 (by simp)] at h0
      refine Lower.substList_comm hΓ hlen' (fun i hi => ?_) (Lower.subst_comm hΓ hx h 0)
      have hi' := hall (i + 1) (by simp only [List.length_cons]; omega)
      rwa [getElem!_pos (x :: xs) (i + 1) (by simp only [List.length_cons]; omega),
        getElem!_pos (y :: ys) (i + 1) (by simp only [List.length_cons]; omega),
        List.getElem_cons_succ, List.getElem_cons_succ,
        ← getElem!_pos xs i hi, ← getElem!_pos ys i (by omega)] at hi'

/-! ## Source-side inversion at every node shape

`elimApp` is indexed by an application spine and the two fix arms by a declaration, so
inverting a derivation at a given *source* shape means ruling those out first. The `.fix`
target is ruled out wherever `BlockBodiesLambda` applies — a block member's specification
body is a λ, so no source but a member's own constant reaches a `.fix`. -/

/-- Every member body of every block the pass builds out of `Γ` is a λ, hence its own
value. This is `LowerBlock.lambda_of_fixLambda`'s conclusion, taken as the premise the δ
step needs: the target `.fix` node is an atom, so the source body must be one too. -/
def BlockBodiesLambda (Γ : GlobalDeclarations) : Prop :=
  ∀ (kns : List Kername) (bs bs' : List LBTerm) (ids : List FVarId)
    (defs : List (@FixDef LBTerm)), LowerBlock Γ kns bs bs' ids defs →
    ∀ j, j < kns.length → isLambda bs[j]! = true

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
  | @elimApp kn iid np dp nfs pre disc disc' minors alts extra extra' =>
      obtain ⟨g, b, he⟩ := mkApps_ne_nil_is_app (f := LBTerm.const kn)
        (args := pre ++ disc :: minors ++ extra) (by cases pre <;> simp)
      rw [he] at hs; exact LBTerm.noConfusion hs

/-- A de Bruijn index is lowered to itself. -/
theorem Lower.source_bvar {Γ : GlobalDeclarations} (hblk : BlockBodiesLambda Γ)
    {s t : LBTerm} {i : Nat} (h : Lower Γ s t) (hs : s = .bvar i) : t = .bvar i := by
  have hnf := Lower.ne_fix_of_block hblk h (by rw [hs]; exact fun _ => LBTerm.noConfusion)
    (by rw [hs]; rfl)
  cases h with
  | bvar j => exact hs ▸ rfl
  | box | fvar | prim | const | lambda | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion hs
  | fixConst | fixBody => exact absurd rfl (hnf _ _)
  | @elimApp kn iid np dp nfs pre disc disc' minors alts extra extra' =>
      obtain ⟨g, b, he⟩ := mkApps_ne_nil_is_app (f := LBTerm.const kn)
        (args := pre ++ disc :: minors ++ extra) (by cases pre <;> simp)
      rw [he] at hs; exact LBTerm.noConfusion hs

/-- A free variable is lowered to itself. -/
theorem Lower.source_fvar {Γ : GlobalDeclarations} (hblk : BlockBodiesLambda Γ)
    {s t : LBTerm} {x : FVarId} (h : Lower Γ s t) (hs : s = .fvar x) : t = .fvar x := by
  have hnf := Lower.ne_fix_of_block hblk h (by rw [hs]; exact fun _ => LBTerm.noConfusion)
    (by rw [hs]; rfl)
  cases h with
  | fvar y => exact hs ▸ rfl
  | box | bvar | prim | const | lambda | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion hs
  | fixConst | fixBody => exact absurd rfl (hnf _ _)
  | @elimApp kn iid np dp nfs pre disc disc' minors alts extra extra' =>
      obtain ⟨g, b, he⟩ := mkApps_ne_nil_is_app (f := LBTerm.const kn)
        (args := pre ++ disc :: minors ++ extra) (by cases pre <;> simp)
      rw [he] at hs; exact LBTerm.noConfusion hs

/-- A primitive is lowered to itself. -/
theorem Lower.source_prim {Γ : GlobalDeclarations} (hblk : BlockBodiesLambda Γ)
    {s t : LBTerm} {p : PrimVal} (h : Lower Γ s t) (hs : s = .prim p) : t = .prim p := by
  have hnf := Lower.ne_fix_of_block hblk h (by rw [hs]; exact fun _ => LBTerm.noConfusion)
    (by rw [hs]; rfl)
  cases h with
  | prim q => exact hs ▸ rfl
  | box | bvar | fvar | const | lambda | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion hs
  | fixConst | fixBody => exact absurd rfl (hnf _ _)
  | @elimApp kn iid np dp nfs pre disc disc' minors alts extra extra' =>
      obtain ⟨g, b, he⟩ := mkApps_ne_nil_is_app (f := LBTerm.const kn)
        (args := pre ++ disc :: minors ++ extra) (by cases pre <;> simp)
      rw [he] at hs; exact LBTerm.noConfusion hs

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
  | @elimApp kn iid np dp nfs pre disc disc' minors alts extra extra' =>
      obtain ⟨g, c, he⟩ := mkApps_ne_nil_is_app (f := LBTerm.const kn)
        (args := pre ++ disc :: minors ++ extra) (by cases pre <;> simp)
      rw [he] at hs; exact LBTerm.noConfusion hs

/-- A projection is lowered to a projection with the same triple. -/
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
  | @elimApp kn iid np dp nfs pre disc disc' minors alts extra extra' =>
      obtain ⟨g, c, he⟩ := mkApps_ne_nil_is_app (f := LBTerm.const kn)
        (args := pre ++ disc :: minors ++ extra) (by cases pre <;> simp)
      rw [he] at hs; exact LBTerm.noConfusion hs

/-- A constructor node is lowered argument by argument. -/
theorem Lower.source_construct {Γ : GlobalDeclarations} (hblk : BlockBodiesLambda Γ)
    {s t : LBTerm} {iid : InductiveId} {k : Nat} {args : List LBTerm}
    (h : Lower Γ s t) (hs : s = .construct iid k args) :
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
  | @elimApp kn iid np dp nfs pre disc disc' minors alts₀ extra extra' =>
      obtain ⟨g, b, he⟩ := mkApps_ne_nil_is_app (f := LBTerm.const kn)
        (args := pre ++ disc :: minors ++ extra) (by cases pre <;> simp)
      rw [he] at hs; exact LBTerm.noConfusion hs

/-- A `case` is lowered to a `case` with the same inductive, parameter count and branch
arities. -/
theorem Lower.source_case {Γ : GlobalDeclarations} (hblk : BlockBodiesLambda Γ)
    {s t : LBTerm} {ip : InductiveId × Nat} {d : LBTerm}
    {alts : List (List BinderName × LBTerm)} (h : Lower Γ s t) (hs : s = .case ip d alts) :
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
  | @elimApp kn iid np dp nfs pre disc disc' minors alts₀ extra extra' =>
      obtain ⟨g, b, he⟩ := mkApps_ne_nil_is_app (f := LBTerm.const kn)
        (args := pre ++ disc :: minors ++ extra) (by cases pre <;> simp)
      rw [he] at hs; exact LBTerm.noConfusion hs

/-- A `.fix` in the source has no image at all: the relation has no `fix` congruence arm,
`fixConst`'s source is a constant, and `fixBody`'s is a member body the guard pins to a λ. -/
theorem Lower.source_fix {Γ : GlobalDeclarations} (hblk : BlockBodiesLambda Γ)
    {s t : LBTerm} {defs₀ : List (@FixDef LBTerm)} {i : Nat}
    (h : Lower Γ s t) (hs : s = .fix defs₀ i) : False := by
  have hnf := Lower.ne_fix_of_block hblk h (by rw [hs]; exact fun _ => LBTerm.noConfusion)
    (by rw [hs]; rfl)
  cases h with
  | box | bvar | fvar | prim | const | lambda | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion hs
  | fixConst | fixBody => exact absurd rfl (hnf _ _)
  | @elimApp kn iid np dp nfs pre disc disc' minors alts₀ extra extra' =>
      obtain ⟨g, b, he⟩ := mkApps_ne_nil_is_app (f := LBTerm.const kn)
        (args := pre ++ disc :: minors ++ extra) (by cases pre <;> simp)
      rw [he] at hs; exact LBTerm.noConfusion hs

/-- What a λ can lower to: a λ, or a block's `.fix` node. Stated without the guard, since a
member body that is a λ is exactly the `fixBody` source `BlockBodiesLambda` admits. -/
theorem Lower.source_lambda {Γ : GlobalDeclarations} {s t : LBTerm} {n : BinderName}
    {b : LBTerm} (h : Lower Γ s t) (hs : s = .lambda n b) :
    (∃ n' b', t = .lambda n' b') ∨ ∃ defs j, t = .fix defs j := by
  cases h with
  | box | bvar | fvar | prim | const | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion hs
  | @lambda n₀ n' b₀ b' => exact .inl ⟨n', b', rfl⟩
  | @fixConst kn kns bs bs' ids defs j => exact .inr ⟨defs, j, rfl⟩
  | @fixBody b₀ kns bs bs' ids defs j => exact .inr ⟨defs, j, rfl⟩
  | @elimApp kn iid np dp nfs pre disc disc' minors alts extra extra' =>
      obtain ⟨g, c, he⟩ := mkApps_ne_nil_is_app (f := LBTerm.const kn)
        (args := pre ++ disc :: minors ++ extra) (by cases pre <;> simp)
      rw [he] at hs; exact LBTerm.noConfusion hs

/-- **What a constant can lower to: two images, both under `¬ RuntimeKey`.** Itself, by
`const`, or a block's `.fix` node, by `fixConst`. The third arm whose source is
unconstrained is `fixBody`, and `BlockBodiesLambda` excludes it: it would force
`isLambda (.const kn) = true`. This is why the two images are read off the derivation and
not off the source's syntax, and it is what lets an `ElimDecl` at `kn` refute both. -/
theorem Lower.source_const {Γ : GlobalDeclarations} (hblk : BlockBodiesLambda Γ)
    {s t : LBTerm} {kn : Kername} (h : Lower Γ s t) (hs : s = .const kn) :
    ¬ RuntimeKey Γ kn ∧ (t = .const kn ∨ ∃ defs j, t = .fix defs j) := by
  cases h with
  | @const kn' hk =>
      have he : kn' = kn := by injection hs
      subst he
      exact ⟨hk, .inl rfl⟩
  | box | bvar | fvar | prim | lambda | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion hs
  | @elimApp kn' iid np dp nfs pre disc disc' minors alts extra extra' =>
      obtain ⟨g, b, he⟩ := mkApps_ne_nil_is_app (f := LBTerm.const kn')
        (args := pre ++ disc :: minors ++ extra) (by cases pre <;> simp)
      rw [he] at hs; exact LBTerm.noConfusion hs
  | @fixConst kn' kns bs bs' ids defs j _ _ _ _ _ _ _ _ _ _ _ hnk hj =>
      have he : kn' = kn := by injection hs
      subst he
      exact ⟨hnk, .inr ⟨defs, j, rfl⟩⟩
  | @fixBody b kns bs bs' ids defs j hb hb' hd hnd hids hilen hfresh hrarg hdecl hlow hcl
      hj hjl =>
      exfalso
      obtain ⟨hjb, hjeq⟩ := Lower.getElem!_of_getElem? hj
      have hlam := hblk kns bs bs' ids defs
        ⟨hb, hb', hd, hnd, hids, hilen, hfresh, hrarg, hdecl, hlow, hcl⟩ j (by omega)
      rw [hjeq, hs] at hlam
      simp [isLambda] at hlam

/-- What a nullary constructor node can lower to: itself, or a block's `.fix` node. Stated
without the guard; `BlockBodiesLambda` is what a consumer spends to drop the second. -/
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
  | @elimApp kn iid' np dp nfs pre disc disc' minors alts extra extra' =>
      obtain ⟨g, b, he⟩ := mkApps_ne_nil_is_app (f := LBTerm.const kn)
        (args := pre ++ disc :: minors ++ extra) (by cases pre <;> simp)
      rw [he] at hs; exact LBTerm.noConfusion hs

/-! ## Non-vacuity

One fixture per arm whose premises read the environment: `elimApp` at its `.const`-headed
key with a non-empty `extra`, and — in `LowerFix.lean`, where the block fixture lives —
`fixConst` under its `¬ RuntimeKey` guard. -/

namespace LowerElimFixture

/-- The fixture's inductive block. -/
def blockKn : Kername := { mp := .MPfile [], id := "LE" }
/-- Its `casesOn` eliminator constant. -/
def elimKn : Kername := { mp := .MPfile [], id := "LEcasesOn" }
/-- The block's one inductive: no parameters, two constructors of `0` and `1` fields. -/
def iid : InductiveId := { mutualBlockName := blockKn, idx := 0 }

/-- The emitted inductive body, non-propositional, with the two field counts. -/
def mib : MutualInductiveBody :=
  { npars := 0,
    bodies := [{ name := "LE", ctors := [{ name := "nil", nargs := 0 },
                                         { name := "one", nargs := 1 }], projs := [] }] }

/-- The block and its eliminator, whose body is the canonical non-recursive shape at one
dropped argument (the motive) and two minors. -/
def env : GlobalDeclarations :=
  [(blockKn, .inductiveDecl mib),
   (elimKn, .constantDecl ⟨some (mkElimBody iid 0 1 [0, 1])⟩)]

/-- Both conjuncts of `ElimDecl`: the eliminator's body and the block it dispatches on. -/
theorem elimDecl : ElimDecl env elimKn iid 0 1 [0, 1] :=
  ⟨⟨_, rfl, .cases⟩, ⟨mib, rfl, rfl, _, rfl, rfl, rfl⟩⟩

/-- Hence the eliminator constant is a runtime key, so neither `const` nor `fixConst`
relates it — which is what `Lower.source_const` turns into an inversion. -/
theorem runtimeKey_elimKn : RuntimeKey env elimKn := ⟨_, _, _, _, elimDecl⟩

/-- **`elimApp` fires at the new key, with `extra ≠ []`.** The eliminator spine — motive,
discriminant, two minors — applied to one argument past its arity becomes the `.case` node
applied to that argument. -/
theorem elimApp_fires :
    Lower env
      (LBTerm.mkApps (.const elimKn)
        ([.box] ++ .bvar 0 :: [.box, .lambda .anon (.bvar 0)] ++ [.bvar 1]))
      (LBTerm.mkApps (.case (iid, 0) (.bvar 0) [([], .box), ([.anon], .bvar 0)]) [.bvar 1]) := by
  refine .elimApp elimDecl rfl rfl rfl ?_ (.bvar 0) rfl ?_
  · intro i hi
    match i, hi with
    | 0, _ => exact .done .box
    | 1, _ => exact .lam (alt := ([], .bvar 0)) (.done (.bvar 0))
  · intro i hi
    match i, hi with
    | 0, _ => exact .bvar 1

end LowerElimFixture

end LeanToLambdaBox
