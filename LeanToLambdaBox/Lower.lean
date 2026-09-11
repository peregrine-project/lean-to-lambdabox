import LeanToLambdaBox.Closed
import LeanToLambdaBox.Abstract
import LeanToLambdaBox.FixMetatheory
import LeanToLambdaBox.Semantics.Env
import LeanToLambdaBox.ElimBody

/-!
# `Lower` — the term-level λ□ → λ□ pass relation

`Lower Γ t t'` relates a term over the *specification* environment `Γ` to the term the
shipping eraser emits for it. It carries the four compilation steps the source-level
erasure relation cannot state: constructor introduction, the eliminator-to-`case`
translation, the two η-expansions, and the block-level fixpoint.

Seventeen arms: eleven congruence, four redex (`ctorApp`, `ctorEta`, `elimApp`,
`elimEta`), two recursion (`fixConst`, `fixBody`). The relation is indexed by `Γ` and by
nothing else — no source term, no typing context, no run state — which is what keeps it a
statement about λ□ alone; `doc/rules-Lower.md` carries the arm-by-arm anchors.

Block premises are inlined into the two fix arms (the kernel rejects a structure premise
that mentions the inductive) and packaged afterwards as `LowerBlock`, read through
`Lower.fixConst'`/`Lower.fixBody'`. List premises are in the indexed form `hlen` plus
`∀ i, i < …`, since `List.Forall₂` as a premise is a nested-inductive occurrence.

`ConstToFVar` and `CloseConstAt` are here because `LowerBlock.hcl` needs them; the rest
of the fixpoint closure is `LowerFix.lean`.
-/

namespace LeanToLambdaBox

open Lean (Name FVarId)

/-! ## Environment queries -/

/-- Arity of constructor `k` of `iid`: parameters plus fields, MetaRocq's `cstr_arity`.
`0` when the inductive is absent from `Γ`, which no well-formed environment is. -/
def cstrArity (Γ : GlobalDeclarations) (iid : InductiveId) (k : Nat) : Nat :=
  (constructorArity Γ iid k).getD 0

/-- `constructorArity` and `cstrArity` agree wherever the inductive is declared: the
bridge between the redex arms' guards and the emitted-program saturation invariant. -/
theorem cstrArity_eq_of_constructorArity {Γ : GlobalDeclarations} {iid : InductiveId}
    {k a : Nat} (h : constructorArity Γ iid k = some a) : cstrArity Γ iid k = a := by
  simp [cstrArity, h]

/-- `kn` is declared in `Γ` as a constructor constant: its body is the empty constructor
block `.construct iid k []`, which the eraser's `visitConstructor` applies. -/
def CtorDecl (Γ : GlobalDeclarations) (kn : Kername) (iid : InductiveId) (k : Nat) : Prop :=
  LBTerm.envLookup Γ kn = some (.constantDecl ⟨some (.construct iid k [])⟩)

/-- `kn` is declared in `Γ` as an eliminator constant: its body is one of the two
canonical `ElimBody` shapes for `iid` at `np` parameters, `dp` dropped arguments and
field arities `nfs`. -/
def ElimDecl (Γ : GlobalDeclarations) (kn : Kername) (iid : InductiveId) (np dp : Nat)
    (nfs : List Nat) : Prop :=
  ∃ body, LBTerm.envLookup Γ kn = some (.constantDecl ⟨some body⟩) ∧ ElimBody iid np dp nfs body

/-- `kn` is declared in `Γ` with body `b`. -/
def DefnDecl (Γ : GlobalDeclarations) (kn : Kername) (b : LBTerm) : Prop :=
  LBTerm.envLookup Γ kn = some (.constantDecl ⟨some b⟩)

/-- `kn` is a key the pass consumes rather than emits: a constructor or an eliminator
constant. The `const` congruence arm is guarded by its negation, since a pruned key
would leave the target with a dangling reference. -/
def RuntimeKey (Γ : GlobalDeclarations) (kn : Kername) : Prop :=
  (∃ iid k, CtorDecl Γ kn iid k) ∨ (∃ iid np dp nfs, ElimDecl Γ kn iid np dp nfs)

/-- An eliminator head: `.const kn` before the environment unfolds it, or an `ElimBody`
shape after. The second disjunct relates the intermediate configurations of a source
derivation that has already taken the δ step, the partially applied ones included, which
are λ-headed values. It is not about a stuck discriminant: `WcbvEval` has no `.case`
congruence rule, so a `.case` whose discriminant has no value has none either. -/
def ElimHeadOf (Γ : GlobalDeclarations) (h : LBTerm) (iid : InductiveId) (np dp : Nat)
    (nfs : List Nat) : Prop :=
  (∃ kn, h = .const kn ∧ ElimDecl Γ kn iid np dp nfs) ∨ ElimBody iid np dp nfs h

/-- Every constant declared in `Γ` has a closed body. The specification environment holds
top-level bodies, so this is a fact about it, and it is what makes the two fix arms
commute with `shift` and `subst`. -/
def ClosedBodies (Γ : GlobalDeclarations) : Prop :=
  ∀ kn b, DefnDecl Γ kn b → LBClosed b 0

/-! ## Spine and telescope helpers -/

/-- The `n` de Bruijn indices of a freshly pushed telescope, outermost first:
`bvarsDesc n = [.bvar (n-1), …, .bvar 0]`. The arguments an η-expansion applies. -/
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

/-- The pass relation, seventeen arms. `Lower Γ t t'` says `t'` is a λ□ term the eraser
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
  /-- A saturated or over-applied constructor constant becomes the applied constructor
      node. `hsat` is the eraser's own dispatch guard, and it makes this arm disjoint
      from `ctorEta` on `args.length`. -/
  | ctorApp {kn : Kername} {iid : InductiveId} {k : Nat} {args args' : List LBTerm}
      (hc : CtorDecl Γ kn iid k)
      (hsat : args.length ≥ cstrArity Γ iid k)
      (hlen : args'.length = args.length)
      (ha : ∀ i, i < args.length → Lower Γ args[i]! args'[i]!) :
      Lower Γ (LBTerm.mkApps (.const kn) args) (LBTerm.mkApps (.construct iid k []) args')
  /-- An under-applied constructor constant is η-expanded: `ns` fresh binders are pushed
      into the spine, `shift ns.length 0` moves the lowered prefix under them. -/
  | ctorEta {kn : Kername} {iid : InductiveId} {k : Nat} {args args' : List LBTerm}
      {ns : List BinderName}
      (hc : CtorDecl Γ kn iid k) (hns : ns ≠ [])
      (hund : args.length + ns.length = cstrArity Γ iid k)
      (hlen : args'.length = args.length)
      (ha : ∀ i, i < args.length → Lower Γ args[i]! args'[i]!) :
      Lower Γ (LBTerm.mkApps (.const kn) args)
              (mkLambdas ns (LBTerm.mkApps (.construct iid k [])
                 ((args'.map (LBTerm.shift ns.length 0)) ++ bvarsDesc ns.length)))
  /-- A saturated eliminator application becomes a `.case` node. The `dp` arguments before
      the discriminant are dropped, the minors are peeled into alternatives, and any
      over-application rides outside the node. -/
  | elimApp {hd : LBTerm} {iid : InductiveId} {np dp : Nat} {nfs : List Nat}
      {pre : List LBTerm} {disc disc' : LBTerm} {minors : List LBTerm}
      {alts : List (List BinderName × LBTerm)} {extra extra' : List LBTerm}
      (hh : ElimHeadOf Γ hd iid np dp nfs)
      (hlen : pre.length = dp)
      (hmlen : minors.length = nfs.length)
      (halen : alts.length = nfs.length)
      (hmin : ∀ i, i < nfs.length → LowerAlt Γ nfs[i]! minors[i]! alts[i]!)
      (hdisc : Lower Γ disc disc')
      (hxlen : extra'.length = extra.length)
      (hx : ∀ i, i < extra.length → Lower Γ extra[i]! extra'[i]!) :
      Lower Γ (LBTerm.mkApps hd (pre ++ disc :: minors ++ extra))
              (LBTerm.mkApps (.case (iid, np) disc' alts) extra')
  /-- An under-applied eliminator is η-expanded: `ns` fresh binders saturate the spine,
      and the saturated spine is related by `elimApp`. -/
  | elimEta {hd : LBTerm} {iid : InductiveId} {np dp : Nat} {nfs : List Nat}
      {args : List LBTerm} {ns : List BinderName} {body : LBTerm}
      (hh : ElimHeadOf Γ hd iid np dp nfs) (hns : ns ≠ [])
      (hund : args.length + ns.length = dp + 1 + nfs.length)
      (hsat : Lower Γ (LBTerm.mkApps hd
                 ((args.map (LBTerm.shift ns.length 0)) ++ bvarsDesc ns.length)) body) :
      Lower Γ (LBTerm.mkApps hd args) (mkLambdas ns body)
  /-- A block member's constant relates to the block's `.fix` node: the call site.
      The premises are `LowerBlock`'s fields, inlined; read them through
      `Lower.fixConst'`. -/
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
      (hj : kns[j]? = some kn) :
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
    (h : LowerBlock Γ kns bs bs' ids defs) (hj : kns[j]? = some kn) :
    Lower Γ (.const kn) (.fix defs j) :=
  .fixConst h.hb h.hb' h.hd h.hnd h.hids h.hilen h.hfresh h.hrarg h.hdecl h.hlow h.hcl hj

/-- `Lower.fixBody` read through `LowerBlock`. -/
theorem Lower.fixBody' {Γ : GlobalDeclarations} {kns : List Kername} {bs bs' : List LBTerm}
    {ids : List FVarId} {defs : List (@FixDef LBTerm)} {j : Nat} {b : LBTerm}
    (h : LowerBlock Γ kns bs bs' ids defs) (hj : bs[j]? = some b) (hjl : j < defs.length) :
    Lower Γ b (.fix defs j) :=
  .fixBody h.hb h.hb' h.hd h.hnd h.hids h.hilen h.hfresh h.hrarg h.hdecl h.hlow h.hcl hj hjl

/-- `Lower.elimApp` read through `LowerAlts`. -/
theorem Lower.elimApp' {Γ : GlobalDeclarations} {hd : LBTerm} {iid : InductiveId}
    {np dp : Nat} {nfs : List Nat} {pre : List LBTerm} {disc disc' : LBTerm}
    {minors : List LBTerm} {alts : List (List BinderName × LBTerm)} {extra extra' : List LBTerm}
    (hh : ElimHeadOf Γ hd iid np dp nfs) (hlen : pre.length = dp)
    (hmin : LowerAlts Γ nfs minors alts) (hdisc : Lower Γ disc disc')
    (hxlen : extra'.length = extra.length)
    (hx : ∀ i, i < extra.length → Lower Γ extra[i]! extra'[i]!) :
    Lower Γ (LBTerm.mkApps hd (pre ++ disc :: minors ++ extra))
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
  | @ctorApp kn iid ci args args' _ _ hlen _ ih =>
      intro k hc
      have hargs := LBClosed.mkApps_inv hc
      refine LBClosed.mkApps (by trivial) ?_
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Lower.mem_getElem! ha
      exact ih i (by omega) k (hargs _ (Lower.getElem!_mem (by omega)))
  | @ctorEta kn iid ci args args' ns _ _ _ hlen _ ih =>
      intro k hc
      have hargs := LBClosed.mkApps_inv hc
      refine LBClosed.mkLambdas (LBClosed.mkApps (by trivial) ?_)
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
        obtain ⟨i, hi, rfl⟩ := Lower.mem_getElem! hy
        exact (ih i (by omega) k (hargs _ (Lower.getElem!_mem (by omega)))).shift ns.length 0
      · exact (lbClosed_bvarsDesc a ha).mono (by omega)
  | @elimApp hd iid np dp nfs pre disc disc' minors alts extra extra'
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
  | @elimEta hd iid np dp nfs args ns body _ _ _ _ ih =>
      intro k hc
      refine LBClosed.mkLambdas (ih (k + ns.length) ?_)
      have hhd := LBClosed.mkApps_head hc
      have hargs := LBClosed.mkApps_inv hc
      refine LBClosed.mkApps (hhd.mono (by omega)) ?_
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
        exact (hargs y hy).shift ns.length 0
      · exact (lbClosed_bvarsDesc a ha).mono (by omega)
  | @fixConst kn kns bs bs' ids defs j hb hb' hdl _ _ hilen _ _ hdecl _ hcl hj ih =>
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

/-- An eliminator head is fixed by `shift`: a `.const` has no index, and both `ElimBody`
shapes are closed (`ElimBody.closed`). -/
theorem ElimHeadOf.shift_eq {Γ : GlobalDeclarations} {hd : LBTerm} {iid : InductiveId}
    {np dp : Nat} {nfs : List Nat} (hh : ElimHeadOf Γ hd iid np dp nfs)
    (d c : Nat) : LBTerm.shift d c hd = hd := by
  rcases hh with ⟨kn, rfl, _⟩ | hb
  · rfl
  · exact hb.closed.shift_eq (Nat.zero_le c) d

/-- An eliminator head is fixed by `subst`, for the same reason as `shift_eq`. -/
theorem ElimHeadOf.subst_eq {Γ : GlobalDeclarations} {hd : LBTerm} {iid : InductiveId}
    {np dp : Nat} {nfs : List Nat} (hh : ElimHeadOf Γ hd iid np dp nfs)
    (s : LBTerm) (c : Nat) : LBTerm.subst s c hd = hd := by
  rcases hh with ⟨kn, rfl, _⟩ | hb
  · rfl
  · exact hb.closed.subst_eq (Nat.zero_le c) s

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
  | @ctorApp kn iid ci args args' hc hsat hlen _ ih =>
      intro d c
      rw [LBTerm.shift_mkApps, LBTerm.shift_mkApps]
      refine .ctorApp hc (by simpa using hsat) (by simp [hlen]) ?_
      intro i hi
      rw [List.length_map] at hi
      rw [Lower.getElem!_map _ _ i hi, Lower.getElem!_map _ _ i (by omega)]
      exact ih i hi d c
  | @ctorEta kn iid ci args args' ns hc hns hund hlen _ ih =>
      intro d c
      rw [LBTerm.shift_mkApps, shift_mkLambdas, LBTerm.shift_mkApps, List.map_append,
        map_shift_shift_comm, shift_bvarsDesc (Nat.le_add_left _ _)]
      refine .ctorEta hc hns (by simpa using hund) (by simp [hlen]) ?_
      intro i hi
      rw [List.length_map] at hi
      rw [Lower.getElem!_map _ _ i hi, Lower.getElem!_map _ _ i (by omega)]
      exact ih i hi d c
  | @elimApp hd iid np dp nfs pre disc disc' minors alts extra extra'
      hh hlen hmlen halen _ _ hxlen _ ihmin ihd ihx =>
      intro d c
      rw [LBTerm.shift_mkApps, LBTerm.shift_mkApps, hh.shift_eq d c]
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
  | @elimEta hd iid np dp nfs args ns body hh hns hund _ ih =>
      intro d c
      rw [LBTerm.shift_mkApps, hh.shift_eq d c, shift_mkLambdas]
      refine .elimEta hh hns (by simpa using hund) ?_
      have hih := ih d (c + ns.length)
      rwa [LBTerm.shift_mkApps, hh.shift_eq d (c + ns.length), List.map_append,
        map_shift_shift_comm, shift_bvarsDesc (Nat.le_add_left _ _)] at hih
  | @fixConst kn kns bs bs' ids defs j hb hb' hdl hnd hids hilen hfresh hrarg hdecl hlow hcl hj
      ih =>
      intro d c
      have hfx : LBClosed (LBTerm.fix defs j) 0 :=
        lbClosed_fix_of_block hdl hilen hcl
          (fun i hi => (Lower.closed hΓ (hlow i hi)) 0 (hΓ _ _ (hdecl i hi))) 0
      rw [show LBTerm.shift d c (LBTerm.const kn) = .const kn from rfl,
        hfx.shift_eq (Nat.zero_le c) d]
      exact .fixConst hb hb' hdl hnd hids hilen hfresh hrarg hdecl hlow hcl hj
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
  | @ctorApp kn iid ci args args' hc hsat hlen _ ih =>
      intro d
      rw [LBTerm.subst_mkApps, LBTerm.subst_mkApps]
      refine .ctorApp hc (by simpa using hsat) (by simp [hlen]) ?_
      intro i hi
      rw [List.length_map] at hi
      rw [Lower.getElem!_map _ _ i hi, Lower.getElem!_map _ _ i (by omega)]
      exact ih i hi d
  | @ctorEta kn iid ci args args' ns hc hns hund hlen _ ih =>
      intro d
      rw [LBTerm.subst_mkApps, subst_mkLambdas, LBTerm.subst_mkApps, List.map_append,
        map_subst_shift_comm, subst_bvarsDesc (Nat.le_add_left _ _)]
      refine .ctorEta hc hns (by simpa using hund) (by simp [hlen]) ?_
      intro i hi
      rw [List.length_map] at hi
      rw [Lower.getElem!_map _ _ i hi, Lower.getElem!_map _ _ i (by omega)]
      exact ih i hi d
  | @elimApp hd iid np dp nfs pre disc disc' minors alts extra extra'
      hh hlen hmlen halen _ _ hxlen _ ihmin ihd ihx =>
      intro d
      rw [LBTerm.subst_mkApps, LBTerm.subst_mkApps, hh.subst_eq a d]
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
  | @elimEta hd iid np dp nfs args ns body hh hns hund _ ih =>
      intro d
      rw [LBTerm.subst_mkApps, hh.subst_eq a d, subst_mkLambdas]
      refine .elimEta hh hns (by simpa using hund) ?_
      have hih := ih (d + ns.length)
      rwa [LBTerm.subst_mkApps, hh.subst_eq a (d + ns.length), List.map_append,
        map_subst_shift_comm, subst_bvarsDesc (Nat.le_add_left _ _)] at hih
  | @fixConst kn kns bs bs' ids defs j hb hb' hdl hnd hids hilen hfresh hrarg hdecl hlow hcl hj
      ih =>
      intro d
      have hfx : LBClosed (LBTerm.fix defs j) 0 :=
        lbClosed_fix_of_block hdl hilen hcl
          (fun i hi => (Lower.closed hΓ (hlow i hi)) 0 (hΓ _ _ (hdecl i hi))) 0
      rw [show LBTerm.subst a d (LBTerm.const kn) = .const kn from rfl,
        hfx.subst_eq (Nat.zero_le d) a']
      exact .fixConst hb hb' hdl hnd hids hilen hfresh hrarg hdecl hlow hcl hj
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
  | @ctorApp kn iid k args args' =>
      rcases mkApps_head_or_app (LBTerm.construct iid k []) args' with he | ⟨g, b, he⟩ <;>
        rw [he] at ht <;> exact LBTerm.noConfusion ht
  | @elimApp hd iid np dp nfs pre disc disc' minors alts extra extra' =>
      rcases mkApps_head_or_app (LBTerm.case (iid, np) disc' alts) extra' with he | ⟨g, b, he⟩ <;>
        rw [he] at ht <;> exact LBTerm.noConfusion ht
  | @ctorEta kn iid k args args' ns _ hns =>
      obtain ⟨n, b, he⟩ := mkLambdas_is_lambda hns _
      rw [he] at ht; exact LBTerm.noConfusion ht
  | @elimEta hd iid np dp nfs args ns body _ hns =>
      obtain ⟨n, b, he⟩ := mkLambdas_is_lambda hns _
      rw [he] at ht; exact LBTerm.noConfusion ht

/-- `Lower` relates only a de Bruijn index to itself: passes do not renumber. -/
theorem Lower.target_bvar {Γ : GlobalDeclarations} {s t : LBTerm} {i : Nat} (h : Lower Γ s t)
    (ht : t = .bvar i) : s = .bvar i := by
  cases h with
  | bvar j => exact ht ▸ rfl
  | box | fvar | prim | const | lambda | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion ht
  | fixConst | fixBody => exact LBTerm.noConfusion ht
  | @ctorApp kn iid k args args' =>
      rcases mkApps_head_or_app (LBTerm.construct iid k []) args' with he | ⟨g, b, he⟩ <;>
        rw [he] at ht <;> exact LBTerm.noConfusion ht
  | @elimApp hd iid np dp nfs pre disc disc' minors alts extra extra' =>
      rcases mkApps_head_or_app (LBTerm.case (iid, np) disc' alts) extra' with he | ⟨g, b, he⟩ <;>
        rw [he] at ht <;> exact LBTerm.noConfusion ht
  | @ctorEta kn iid k args args' ns _ hns =>
      obtain ⟨n, b, he⟩ := mkLambdas_is_lambda hns _
      rw [he] at ht; exact LBTerm.noConfusion ht
  | @elimEta hd iid np dp nfs args ns body _ hns =>
      obtain ⟨n, b, he⟩ := mkLambdas_is_lambda hns _
      rw [he] at ht; exact LBTerm.noConfusion ht

/-- `Lower` relates only a free variable to itself. -/
theorem Lower.target_fvar {Γ : GlobalDeclarations} {s t : LBTerm} {x : Lean.FVarId}
    (h : Lower Γ s t) (ht : t = .fvar x) : s = .fvar x := by
  cases h with
  | fvar y => exact ht ▸ rfl
  | box | bvar | prim | const | lambda | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion ht
  | fixConst | fixBody => exact LBTerm.noConfusion ht
  | @ctorApp kn iid k args args' =>
      rcases mkApps_head_or_app (LBTerm.construct iid k []) args' with he | ⟨g, b, he⟩ <;>
        rw [he] at ht <;> exact LBTerm.noConfusion ht
  | @elimApp hd iid np dp nfs pre disc disc' minors alts extra extra' =>
      rcases mkApps_head_or_app (LBTerm.case (iid, np) disc' alts) extra' with he | ⟨g, b, he⟩ <;>
        rw [he] at ht <;> exact LBTerm.noConfusion ht
  | @ctorEta kn iid k args args' ns _ hns =>
      obtain ⟨n, b, he⟩ := mkLambdas_is_lambda hns _
      rw [he] at ht; exact LBTerm.noConfusion ht
  | @elimEta hd iid np dp nfs args ns body _ hns =>
      obtain ⟨n, b, he⟩ := mkLambdas_is_lambda hns _
      rw [he] at ht; exact LBTerm.noConfusion ht

/-- `Lower` relates only a primitive to itself. -/
theorem Lower.target_prim {Γ : GlobalDeclarations} {s t : LBTerm} {p : PrimVal}
    (h : Lower Γ s t) (ht : t = .prim p) : s = .prim p := by
  cases h with
  | prim q => exact ht ▸ rfl
  | box | bvar | fvar | const | lambda | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion ht
  | fixConst | fixBody => exact LBTerm.noConfusion ht
  | @ctorApp kn iid k args args' =>
      rcases mkApps_head_or_app (LBTerm.construct iid k []) args' with he | ⟨g, b, he⟩ <;>
        rw [he] at ht <;> exact LBTerm.noConfusion ht
  | @elimApp hd iid np dp nfs pre disc disc' minors alts extra extra' =>
      rcases mkApps_head_or_app (LBTerm.case (iid, np) disc' alts) extra' with he | ⟨g, b, he⟩ <;>
        rw [he] at ht <;> exact LBTerm.noConfusion ht
  | @ctorEta kn iid k args args' ns _ hns =>
      obtain ⟨n, b, he⟩ := mkLambdas_is_lambda hns _
      rw [he] at ht; exact LBTerm.noConfusion ht
  | @elimEta hd iid np dp nfs args ns body _ hns =>
      obtain ⟨n, b, he⟩ := mkLambdas_is_lambda hns _
      rw [he] at ht; exact LBTerm.noConfusion ht

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
  | @ctorApp kn iid k args args' =>
      rcases mkApps_head_or_app (LBTerm.construct iid k []) args' with he | ⟨g, b, he⟩ <;>
        rw [he] at ht <;> exact LBTerm.noConfusion ht
  | @elimApp hd iid np dp nfs pre disc disc' minors alts extra extra' =>
      rcases mkApps_head_or_app (LBTerm.case (iid, np) disc' alts) extra' with he | ⟨g, b, he⟩ <;>
        rw [he] at ht <;> exact LBTerm.noConfusion ht
  | @ctorEta kn iid k args args' ns _ hns =>
      obtain ⟨n, b, he⟩ := mkLambdas_is_lambda hns _
      rw [he] at ht; exact LBTerm.noConfusion ht
  | @elimEta hd iid np dp nfs args ns body _ hns =>
      obtain ⟨n, b, he⟩ := mkLambdas_is_lambda hns _
      rw [he] at ht; exact LBTerm.noConfusion ht

/-- A `.fix` in the target comes from one of the two fix arms, and carries a whole
`LowerBlock`: either the member's constant or its specification body. -/
theorem Lower.target_fix {Γ : GlobalDeclarations} {s t : LBTerm}
    {defs : List (@FixDef LBTerm)} {j : Nat} (h : Lower Γ s t) (ht : t = .fix defs j) :
    ∃ kns bs bs' ids, LowerBlock Γ kns bs bs' ids defs ∧
      ((∃ kn, s = .const kn ∧ kns[j]? = some kn) ∨ (bs[j]? = some s ∧ j < defs.length)) := by
  cases h with
  | box | bvar | fvar | prim | const | lambda | letIn | app | proj | construct | «case» =>
      exact LBTerm.noConfusion ht
  | @ctorApp kn iid k args args' =>
      rcases mkApps_head_or_app (LBTerm.construct iid k []) args' with he | ⟨g, b, he⟩ <;>
        rw [he] at ht <;> exact LBTerm.noConfusion ht
  | @elimApp hd iid np dp nfs pre disc disc' minors alts extra extra' =>
      rcases mkApps_head_or_app (LBTerm.case (iid, np) disc' alts) extra' with he | ⟨g, b, he⟩ <;>
        rw [he] at ht <;> exact LBTerm.noConfusion ht
  | @ctorEta kn iid k args args' ns _ hns =>
      obtain ⟨n, b, he⟩ := mkLambdas_is_lambda hns _
      rw [he] at ht; exact LBTerm.noConfusion ht
  | @elimEta hd iid np dp nfs args ns body _ hns =>
      obtain ⟨n, b, he⟩ := mkLambdas_is_lambda hns _
      rw [he] at ht; exact LBTerm.noConfusion ht
  | @fixConst kn kns bs bs' ids defs₀ j₀ hb hb' hdl hnd hids hilen hfresh hrarg hdecl hlow
      hcl hj =>
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
  | ctorApp | ctorEta | elimApp | elimEta | fixConst | fixBody => trivial


/-- A constructor node in the target comes either from the same node, argument by
argument, or from a constructor constant the pass applied at zero arity. -/
theorem Lower.target_construct {Γ : GlobalDeclarations} {s t : LBTerm} {iid : InductiveId}
    {k : Nat} {args' : List LBTerm} (h : Lower Γ s t) (ht : t = .construct iid k args') :
    (∃ args, s = .construct iid k args ∧ args'.length = args.length ∧
        ∀ i, i < args.length → Lower Γ args[i]! args'[i]!)
      ∨ (∃ kn, s = .const kn ∧ CtorDecl Γ kn iid k ∧ args' = []
          ∧ cstrArity Γ iid k = 0) := by
  cases h with
  | box | bvar | fvar | prim | const | lambda | letIn | app | proj | «case» =>
      exact LBTerm.noConfusion ht
  | fixConst | fixBody => exact LBTerm.noConfusion ht
  | @construct iid₀ k₀ args args₀ hlen hargs =>
      injection ht with hi hk hargs'
      subst hi; subst hk; subst hargs'
      exact .inl ⟨args, rfl, hlen, hargs⟩
  | @elimApp hd iid np dp nfs pre disc disc' minors alts extra extra' =>
      rcases mkApps_head_or_app (LBTerm.case (iid, np) disc' alts) extra' with he | ⟨g, b, he⟩ <;>
        rw [he] at ht <;> exact LBTerm.noConfusion ht
  | @ctorEta kn iid k args args' ns _ hns =>
      obtain ⟨n, b, he⟩ := mkLambdas_is_lambda hns _
      rw [he] at ht; exact LBTerm.noConfusion ht
  | @elimEta hd iid np dp nfs args ns body _ hns =>
      obtain ⟨n, b, he⟩ := mkLambdas_is_lambda hns _
      rw [he] at ht; exact LBTerm.noConfusion ht
  | @ctorApp kn iid₀ k₀ args args₀ hc hsat hlen hargs =>
      have hnil : args₀ = [] := by
        have := congrArg LBTerm.spineArgs ht
        rwa [LBTerm.spineArgs_mkApps, LBTerm.spineArgs_construct, List.nil_append,
          LBTerm.spineArgs_construct] at this
      subst hnil
      rw [LBTerm.mkApps_nil] at ht
      injection ht with hi hk hargs'
      subst hi; subst hk
      have hargsnil : args = [] := by
        have : args.length = 0 := by simpa using hlen.symm
        simpa using this
      subst hargsnil
      simp only [List.length_nil] at hsat
      rw [LBTerm.mkApps_nil]
      exact .inr ⟨kn, rfl, hc, hargs'.symm, Nat.le_zero.mp hsat⟩

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

end LeanToLambdaBox
