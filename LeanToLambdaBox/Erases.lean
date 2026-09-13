import LeanToLambdaBox.Basic
import LeanToLambdaBox.Erasability
import LeanToLambdaBox.Semantics.Eval
import Lean4Lean.Verify.Typing.Expr

/-!
# `Erases` — the erasure relation over `Lean.Expr`

`Erases env Us Δ e t` relates a source term `e`, read in the local context `Δ` exactly as
lean4lean's `TrExprS` reads it, to a λ□ image `t`. It is the erasure relation of Sozeau et
al. transposed to `Lean.Expr`: `TrExprS` with the target `VExpr` replaced by `LBTerm`,
`Expr.sort` and `Expr.forallE` absorbed into the box rule, and a box rule added.

Eleven rules, no name registry; `doc/rules-Erases.md` is the rule-by-rule transport table,
and the `#guard` below pins the arm list to it. The relation is deliberately
non-deterministic at `box`: an irrelevant term relates both to its structural image and to
`LBTerm.box`.

Rocq writes a constructor `tConstruct`, an inductive type name `tInd` and everything else
`tConst`; Lean writes all three `Expr.const`, so the relation says which. `ctor` reads
`CtorOf`, a type name has no image but `box` — it is erasable — and `const` reads
`ConstOrigin`, the defining declaration exhibited. All three are read off a declaration list
of `VEnv.WF'` below `env`, and are declared here with `IndInfo`.

The two compilation steps a congruence over `Lean.Expr` cannot state — an eliminator
application and top-level recursion, neither of which is a `Lean.Expr` node — belong to the
pass layer (`doc/rules-Lower.md`), not here.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

/-! ## Irrelevance under level instantiation

`IsArity` is the syntactic half of `Erasable`. Both the transport lemmas
(`ErasesAbstract.lean`) and the type-name reading (`ErasesTotal.lean`) instantiate levels,
so the lemma sits here, above both.
-/

/-- `IsArity` is a spine of `forallE`s ending in a `sort`; `instL` fixes both
constructors. -/
theorem IsArity.instL {ls : List VLevel} : ∀ {A : VExpr}, IsArity A → IsArity (A.instL ls)
  | _, .sort _ => .sort _
  | _, .forallE _ _ h => .forallE _ _ (IsArity.instL h)

/-! ## Inductive block data in λ□ coordinates -/

/-- The λ□ kername the eraser mints for a mutual inductive block: the type formers' names,
as strings, joined, read as a root kername. -/
def indBlockKername (names : List Name) : Kername :=
  rootKername (String.join (names.map toString))

/-- The field count of each constructor of the type former `t` in a block with `np`
parameters: the constructor's Π-binders beyond the parameters. -/
def ctorFieldCounts (np : Nat) (t : VInductiveType) : List Nat :=
  t.ctors.map fun c => c.type.piArity - np

/--
`env`'s data for the inductive type `I`, in λ□ coordinates: a well-formed environment that
`env` extends declares a block of `np` parameters whose `iid.idx`-th type former is `I`,
`iid`'s block kername is `indBlockKername` of that block's names, and `nfs` lists the field
counts of `I`'s constructors.

A `VEnv` stores no declarations, so the block is read off a declaration list of
`VEnv.WF'`. The bound is an environment below `env` rather than `env` itself, which is what
makes `IndInfo.mono` hold.
-/
structure IndInfo (env : VEnv) (I : Name) (iid : InductiveId) (np : Nat) (nfs : List Nat) :
    Prop where
  block : ∃ (ds : List VDecl) (env₀ : VEnv) (decl : VInductDecl) (t : VInductiveType),
    VEnv.WF' ds env₀ ∧ VDecl.induct decl ∈ ds ∧ env₀ ≤ env ∧
    decl.types[iid.idx]? = some t ∧ t.name = I ∧
    iid.mutualBlockName = indBlockKername (decl.types.map (·.name)) ∧
    decl.nparams = np ∧ ctorFieldCounts np t = nfs

/-- Introduction: the block is declared in a well-formed environment below `env`. -/
theorem IndInfo.of_wf' {env env₀ : VEnv} {I : Name} {iid : InductiveId} {np : Nat}
    {nfs : List Nat} {ds : List VDecl} {decl : VInductDecl} {t : VInductiveType}
    (hds : VEnv.WF' ds env₀) (hd : VDecl.induct decl ∈ ds) (hle : env₀ ≤ env)
    (ht : decl.types[iid.idx]? = some t) (hname : t.name = I)
    (hkn : iid.mutualBlockName = indBlockKername (decl.types.map (·.name)))
    (hnp : decl.nparams = np) (hnfs : ctorFieldCounts np t = nfs) :
    IndInfo env I iid np nfs :=
  ⟨ds, env₀, decl, t, hds, hd, hle, ht, hname, hkn, hnp, hnfs⟩

/-- Block data survives environment extension. -/
theorem IndInfo.mono {env env' : VEnv} {I : Name} {iid : InductiveId} {np : Nat}
    {nfs : List Nat} (hle : env ≤ env') (h : IndInfo env I iid np nfs) :
    IndInfo env' I iid np nfs :=
  let ⟨ds, env₀, decl, t, hds, hd, hle₀, ht, hname, hkn, hnp, hnfs⟩ := h.block
  ⟨ds, env₀, decl, t, hds, hd, hle₀.trans hle, ht, hname, hkn, hnp, hnfs⟩

/-- `env`'s block data for `I` in **source** coordinates: the parameter count and the
per-constructor field counts, with no λ□ identifier. This is what a rule about `Lean.Expr`
evaluation may read; `IndInfo.arity` is the projection, so every site holding `IndInfo` holds
this. -/
def IndArity (env : VEnv) (I : Name) (np : Nat) (nfs : List Nat) : Prop :=
  ∃ (ds : List VDecl) (env₀ : VEnv) (decl : VInductDecl) (t : VInductiveType),
    VEnv.WF' ds env₀ ∧ VDecl.induct decl ∈ ds ∧ env₀ ≤ env ∧
    t ∈ decl.types ∧ t.name = I ∧ decl.nparams = np ∧ ctorFieldCounts np t = nfs

/-- The λ□ identifier is the only thing `IndInfo` has beyond `IndArity`. -/
theorem IndInfo.arity {env : VEnv} {I : Name} {iid : InductiveId} {np : Nat} {nfs : List Nat}
    (h : IndInfo env I iid np nfs) : IndArity env I np nfs :=
  let ⟨ds, env₀, decl, t, hds, hd, hle, ht, hname, _, hnp, hnfs⟩ := h.block
  ⟨ds, env₀, decl, t, hds, hd, hle, List.mem_of_getElem? ht, hname, hnp, hnfs⟩

/-- The converse of `IndInfo.arity`: source-coordinate block data names a position in its own
block, so it exhibits a λ□ identifier. The identifier is not unique data — it is read off the
block the witness already carries — which is why the arity form is the one a source-side rule
holds. -/
theorem IndArity.indInfo {env : VEnv} {I : Name} {np : Nat} {nfs : List Nat}
    (h : IndArity env I np nfs) : ∃ iid, IndInfo env I iid np nfs := by
  obtain ⟨ds, env₀, decl, t, hds, hd, hle, hmem, hname, hnp, hnfs⟩ := h
  obtain ⟨idx, hidx⟩ : ∃ idx : Nat, decl.types[idx]? = some t := List.getElem?_of_mem hmem
  refine ⟨⟨indBlockKername (decl.types.map (·.name)), idx⟩,
    ⟨ds, env₀, decl, t, hds, hd, hle, hidx, hname, ?_, hnp, hnfs⟩⟩
  rfl

/-- Source-coordinate block data survives environment extension. -/
theorem IndArity.mono {env env' : VEnv} {I : Name} {np : Nat} {nfs : List Nat}
    (hle : env ≤ env') (h : IndArity env I np nfs) : IndArity env' I np nfs :=
  let ⟨ds, env₀, decl, t, hds, hd, hle₀, ht, hname, hnp, hnfs⟩ := h
  ⟨ds, env₀, decl, t, hds, hd, hle₀.trans hle, ht, hname, hnp, hnfs⟩

/-- The type former `I` is declared by a block of `env`'s **own** declaration list, which is
the list upstream ask 6 reads. `IndInfo` exhibits a block below `env`, one extension short of
this, so this is not monotone in `env` and belongs on no rule. -/
def IndDeclOf (env : VEnv) (I : Name) : Prop :=
  ∃ (ds : List VDecl) (decl : VInductDecl) (t : VInductiveType),
    env.WF' ds ∧ VDecl.induct decl ∈ ds ∧ t ∈ decl.types ∧ t.name = I

/-! ## The three readings of `Expr.const`

A constructor, an inductive type name and a plain constant are one `Expr` node in Lean and
three nodes in Rocq. Each reading exhibits the declaration it comes from, off a declaration
list of `VEnv.WF'` below `env`: `CtorOf` and `IndInfo` read a block, `ConstOrigin` reads a
definition, an opaque constant or an axiom.
-/

/-- `c` is the `k`-th constructor of the inductive type `I`, read off a declaration list of
`VEnv.WF'` below `env` — the same reading `IndInfo` takes. -/
def CtorOf (env : VEnv) (c I : Name) (k : Nat) : Prop :=
  ∃ (ds : List VDecl) (env₀ : VEnv) (decl : VInductDecl) (t : VInductiveType)
    (ctor : VConstVal),
    VEnv.WF' ds env₀ ∧ VDecl.induct decl ∈ ds ∧ env₀ ≤ env ∧
    t ∈ decl.types ∧ t.name = I ∧ t.ctors[k]? = some ctor ∧ ctor.name = c

/-- Constructor data survives environment extension: the declaring list sits below `env`,
hence below any extension of it. -/
theorem CtorOf.mono {env env' : VEnv} {c I : Name} {k : Nat} (hle : env ≤ env')
    (h : CtorOf env c I k) : CtorOf env' c I k :=
  let ⟨ds, env₀, decl, t, ctor, hds, hd, hle₀, ht, hname, hk, hcn⟩ := h
  ⟨ds, env₀, decl, t, ctor, hds, hd, hle₀.trans hle, ht, hname, hk, hcn⟩

/-- Does this declaration introduce `c` as a plain constant? A block introduces type names
and constructors, and `quot` is outside the fragment, so neither defines one. -/
def VDeclDefines : VDecl → Name → Prop
  | .axiom cv, c => cv.name = c
  | .def dv, c => dv.name = c
  | .opaque dv, c => dv.name = c
  | .example dv, c => dv.name = c
  | .mutualDef dvs, c => ∃ dv ∈ dvs, dv.name = c
  | .quot, _ => False
  | .induct _, _ => False

/-- Rocq's `tConst` reading: `c` is declared as a definition, an opaque constant or an
axiom, the declaration exhibited off a list of `VEnv.WF'` below `env`. Positive, exactly as
`CtorOf` and `IndInfo` are, so an introduction site discharges it from the declaration list
it already has; the exclusion direction — that this reading rules the other two out — is a
theorem of the kernel theory, not a premise here. -/
def ConstOrigin (env : VEnv) (c : Name) : Prop :=
  ∃ (ds : List VDecl) (env₀ : VEnv) (d : VDecl),
    VEnv.WF' ds env₀ ∧ d ∈ ds ∧ env₀ ≤ env ∧ VDeclDefines d c

/-- A constant's origin survives environment extension. -/
theorem ConstOrigin.mono {env env' : VEnv} {c : Name} (hle : env ≤ env')
    (h : ConstOrigin env c) : ConstOrigin env' c :=
  let ⟨ds, env₀, d, hds, hd, hle₀, hdef⟩ := h
  ⟨ds, env₀, d, hds, hd, hle₀.trans hle, hdef⟩

/-- The two block readings agree: a constructor's own declaration is its type's block, so
the data `Erases.ctor` reads off it is available from `CtorOf` alone. -/
theorem CtorOf.indInfo {env : VEnv} {c I : Name} {k : Nat} (h : CtorOf env c I k) :
    ∃ iid np nfs, IndInfo env I iid np nfs := by
  obtain ⟨ds, env₀, decl, t, ctor, hds, hd, hle, hmem, hname, hk, hcn⟩ := h
  obtain ⟨idx, hidx⟩ : ∃ idx : Nat, decl.types[idx]? = some t := List.getElem?_of_mem hmem
  refine ⟨⟨indBlockKername (decl.types.map (·.name)), idx⟩, decl.nparams,
    ctorFieldCounts decl.nparams t,
    ⟨ds, env₀, decl, t, hds, hd, hle, hidx, hname, ?_, rfl, rfl⟩⟩
  rfl

/-- The source-coordinate half of `CtorOf.indInfo`: a constructor's own block supplies the
parameter and field counts its type former's rules read. -/
theorem CtorOf.indArity {env : VEnv} {c I : Name} {k : Nat} (h : CtorOf env c I k) :
    ∃ np nfs, IndArity env I np nfs :=
  let ⟨_iid, np, nfs, hi⟩ := h.indInfo
  ⟨np, nfs, hi.arity⟩

/-! ## The relation -/

/--
Erasure of a `Lean.Expr` to a λ□ term, in lean4lean's local context `Δ` under the universe
parameters `Us`.

`env`, `Us` are fixed; `Δ` is an index because the binder rules recurse under an extended
context, exactly as `TrExprS.lam` and `TrExprS.letE` do. The image of a term is not unique:
`box` competes with every structural rule.
-/
inductive Erases (env : VEnv) (Us : List Name) : VLCtx → Expr → LBTerm → Prop
  /-- An irrelevant term erases to `LBTerm.box`, witnessed by a lean4lean translation of the
      term together with an `Erasable` proof that its translation is a proof or a
      type-former. This is the only non-deterministic rule, and the only rule reachable from
      a `Expr.sort` or a `Expr.forallE` source. -/
  | box {Δ e ve} (htr : TrExprS env Us Δ e ve)
      (her : Erasable env Us.length Δ.toCtx ve) :
      Erases env Us Δ e .box
  /-- A bound variable keeps its index. The lookup premise is `TrExprS.bvar`'s: without it
      the relation admits indices that `Δ` does not bind. -/
  | bvar {Δ i e' A} (h : Δ.find? (.inl i) = some (e', A)) :
      Erases env Us Δ (.bvar i) (.bvar i)
  /-- A free variable keeps its identifier; both languages are locally nameless. The lookup
      premise is `TrExprS.fvar`'s. -/
  | fvar {Δ x e' A} (h : Δ.find? (.inr x) = some (e', A)) :
      Erases env Us Δ (.fvar x) (.fvar x)
  /-- `[S Fig. 18]`'s `tConstruct` congruence at the bare head: a constructor constant
      erases to its λ□ constructor node, and its arguments arrive through `app`, so the
      node carries none. `iid` and `k` are functions of the block, as `toKername` is of the
      name. -/
  | ctor {Δ c us I iid k np nfs} (hc : CtorOf env c I k) (hi : IndInfo env I iid np nfs) :
      Erases env Us Δ (.const c us) (.construct iid k [])
  /-- Rocq's `tConst`: a constant declared as a definition, an opaque constant or an axiom
      erases to its kername, universe levels dropped. The kername is the value of the
      function `toKername`, so the rule takes no kername parameter and consults no
      registry; `ConstOrigin` is the reading, and an inductive type name — which has no
      such declaration — keeps `box` as its only image. -/
  | const {Δ c us ci} (hc : env.constants c = some ci) (ho : ConstOrigin env c) :
      Erases env Us Δ (.const c us) (.const (toKername c))
  /-- Application is a congruence. -/
  | app {Δ f f' a a'} (hf : Erases env Us Δ f f') (ha : Erases env Us Δ a a') :
      Erases env Us Δ (.app f a) (.app f' a')
  /-- A λ-abstraction extends `Δ` as `TrExprS.lam` does and records the **source** binder
      name. The eraser's filter on non-ASCII names is a printer constraint, stated on the
      output boundary rather than here. -/
  | lam {Δ n ty bi b b'} {ty' : VExpr} (hty : TrExprS env Us Δ ty ty')
      (hb : Erases env Us ((none, .vlam ty') :: Δ) b b') :
      Erases env Us Δ (.lam n ty b bi) (.lambda (.named n.toString) b')
  /-- A `let` erases to a `let`: ζ is enabled in both semantics, the binder name is the
      source's, and `Expr.letE`'s non-dependence flag is ignored. -/
  | letE {Δ n ty nd v v' b b'} {ty' val' : VExpr}
      (hty : TrExprS env Us Δ ty ty') (hval : TrExprS env Us Δ v val')
      (hv : Erases env Us Δ v v')
      (hb : Erases env Us ((none, .vlet ty' val') :: Δ) b b') :
      Erases env Us Δ (.letE n ty v b nd) (.letIn (.named n.toString) v' b')
  /-- A structure projection erases the discriminant and reads its metadata off `IndInfo`:
      `S` is a block-level type former with `np` parameters and one constructor of `nf`
      fields. `hinf` is the relevance Fig. 18 gets from Rocq's typing, which forbids a
      projection out of `Prop`: without it the arm is refutable, since a boxed discriminant
      has no target step (`erases_proj_needs_informative`). It removes no program — a field of
      a propositional structure is a proof, and `box` is its rule — and it is semantic, since
      the successor shape would exclude `Prod`, which `box` does not cover. `IndDeclOf` is not
      here: it is not monotone in `env`. No `TrExprS` premise: `TrProj` pins only up to defeq. -/
  | proj {Δ S i e t iid np nf} (hs : IndInfo env S iid np [nf])
      (hinf : InformativeInd env S) (hi : i < nf)
      (hd : Erases env Us Δ e t) :
      Erases env Us Δ (.proj S i e) (.proj ⟨iid, np, i⟩ t)
  /-- A literal erases to whatever its one-step kernel unfolding erases to, mirroring
      `TrExprS.lit`. `hcl` is that rule's own premise. -/
  | lit {Δ l t} (hcl : env.ContainsLits l) (h : Erases env Us Δ l.toConstructor t) :
      Erases env Us Δ (.lit l) t
  /-- Metadata is transparent. -/
  | mdata {Δ d e t} (h : Erases env Us Δ e t) : Erases env Us Δ (.mdata d e) t

open Lean Elab Term in
/-- The constructor names of `Erases`, read off the environment as a `List Name`. -/
elab "erasesArms%" : term => do
  let .inductInfo iv ← getConstInfo ``Erases | throwError "`Erases` is not an inductive"
  return toExpr iv.ctors

#guard erasesArms% ==
  [``Erases.box, ``Erases.bvar, ``Erases.fvar, ``Erases.ctor, ``Erases.const,
   ``Erases.app, ``Erases.lam, ``Erases.letE, ``Erases.proj, ``Erases.lit,
   ``Erases.mdata]

/-! ## Inversion

One lemma per source head. Every head admits the box rule, so each reads as a disjunction
with the box witness; `Expr.sort` and `Expr.forallE` admit nothing else.
-/

variable {env : VEnv} {Us : List Name} {Δ : VLCtx} {t : LBTerm}

/-- The box alternative, shared by every inversion lemma: `e` has a translation that is
irrelevant, and the image is `LBTerm.box`. -/
def ErasesBox (env : VEnv) (Us : List Name) (Δ : VLCtx) (e : Expr) (t : LBTerm) : Prop :=
  (∃ ve, TrExprS env Us Δ e ve ∧ Erasable env Us.length Δ.toCtx ve) ∧ t = .box

theorem Erases.sort_inv {u : Level} (h : Erases env Us Δ (.sort u) t) :
    ErasesBox env Us Δ (.sort u) t := by
  cases h with | box htr her => exact ⟨⟨_, htr, her⟩, rfl⟩

theorem Erases.forallE_inv {n : Name} {ty b : Expr} {bi : BinderInfo}
    (h : Erases env Us Δ (.forallE n ty b bi) t) :
    ErasesBox env Us Δ (.forallE n ty b bi) t := by
  cases h with | box htr her => exact ⟨⟨_, htr, her⟩, rfl⟩

theorem Erases.bvar_inv {i : Nat} (h : Erases env Us Δ (.bvar i) t) :
    ErasesBox env Us Δ (.bvar i) t ∨
      ((∃ e' A, Δ.find? (.inl i) = some (e', A)) ∧ t = .bvar i) := by
  cases h with
  | box htr her => exact .inl ⟨⟨_, htr, her⟩, rfl⟩
  | bvar hf => exact .inr ⟨⟨_, _, hf⟩, rfl⟩

theorem Erases.fvar_inv {x : FVarId} (h : Erases env Us Δ (.fvar x) t) :
    ErasesBox env Us Δ (.fvar x) t ∨
      ((∃ e' A, Δ.find? (.inr x) = some (e', A)) ∧ t = .fvar x) := by
  cases h with
  | box htr her => exact .inl ⟨⟨_, htr, her⟩, rfl⟩
  | fvar hf => exact .inr ⟨⟨_, _, hf⟩, rfl⟩

/-- The `Expr.const` head has three readings, so its inversion has three alternatives: the
box rule, the `ctor` rule's constructor node, and the `const` rule's kername. Nothing here
excludes two of them at once — that is the kernel theory's business — so a consumer that
knows which reading it is at supplies `CtorOf`, `IndInfo` or `ConstOrigin` and discards the
others. -/
theorem Erases.const_inv {c : Name} {us : List Level} (h : Erases env Us Δ (.const c us) t) :
    ErasesBox env Us Δ (.const c us) t ∨
      (∃ I iid k np nfs, CtorOf env c I k ∧ IndInfo env I iid np nfs ∧
        t = .construct iid k []) ∨
      ((∃ ci, env.constants c = some ci) ∧ ConstOrigin env c ∧ t = .const (toKername c)) := by
  cases h with
  | box htr her => exact .inl ⟨⟨_, htr, her⟩, rfl⟩
  | ctor hc hi => exact .inr (.inl ⟨_, _, _, _, _, hc, hi, rfl⟩)
  | const hc ho => exact .inr (.inr ⟨⟨_, hc⟩, ho, rfl⟩)

/-- Inversion at a constructor **image**: `ctor` is the only rule that produces one, so the
node carries no arguments and its block data is exhibited. The source is not pinned — `lit`
and `mdata` pass an image through — which is why this lemma is keyed on the target where the
rest of the kit is keyed on the source head. -/
theorem Erases.ctor_inv {e : Expr} {iid : InductiveId} {k : Nat} {args : List LBTerm}
    (h : Erases env Us Δ e (.construct iid k args)) :
    args = [] ∧ ∃ c I np nfs, CtorOf env c I k ∧ IndInfo env I iid np nfs := by
  generalize ht : LBTerm.construct iid k args = t at h
  induction h with
  | ctor hc hi => cases ht; exact ⟨rfl, _, _, _, _, hc, hi⟩
  | lit _ _ ih => exact ih ht
  | mdata _ ih => exact ih ht
  | _ => cases ht

theorem Erases.app_inv {f a : Expr} (h : Erases env Us Δ (.app f a) t) :
    ErasesBox env Us Δ (.app f a) t ∨
      (∃ f' a', Erases env Us Δ f f' ∧ Erases env Us Δ a a' ∧ t = .app f' a') := by
  cases h with
  | box htr her => exact .inl ⟨⟨_, htr, her⟩, rfl⟩
  | app hf ha => exact .inr ⟨_, _, hf, ha, rfl⟩

theorem Erases.lam_inv {n : Name} {ty b : Expr} {bi : BinderInfo}
    (h : Erases env Us Δ (.lam n ty b bi) t) :
    ErasesBox env Us Δ (.lam n ty b bi) t ∨
      (∃ ty' b', TrExprS env Us Δ ty ty' ∧ Erases env Us ((none, .vlam ty') :: Δ) b b' ∧
        t = .lambda (.named n.toString) b') := by
  cases h with
  | box htr her => exact .inl ⟨⟨_, htr, her⟩, rfl⟩
  | lam hty hb => exact .inr ⟨_, _, hty, hb, rfl⟩

theorem Erases.letE_inv {n : Name} {ty v b : Expr} {nd : Bool}
    (h : Erases env Us Δ (.letE n ty v b nd) t) :
    ErasesBox env Us Δ (.letE n ty v b nd) t ∨
      (∃ ty' val' v' b', TrExprS env Us Δ ty ty' ∧ TrExprS env Us Δ v val' ∧
        Erases env Us Δ v v' ∧ Erases env Us ((none, .vlet ty' val') :: Δ) b b' ∧
        t = .letIn (.named n.toString) v' b') := by
  cases h with
  | box htr her => exact .inl ⟨⟨_, htr, her⟩, rfl⟩
  | letE hty hval hv hb => exact .inr ⟨_, _, _, _, hty, hval, hv, hb, rfl⟩

theorem Erases.proj_inv {S : Name} {i : Nat} {e : Expr} (h : Erases env Us Δ (.proj S i e) t) :
    ErasesBox env Us Δ (.proj S i e) t ∨
      (∃ iid np nf d, IndInfo env S iid np [nf] ∧ InformativeInd env S ∧ i < nf ∧
        Erases env Us Δ e d ∧ t = .proj ⟨iid, np, i⟩ d) := by
  cases h with
  | box htr her => exact .inl ⟨⟨_, htr, her⟩, rfl⟩
  | proj hs hinf hi hd => exact .inr ⟨_, _, _, _, hs, hinf, hi, hd, rfl⟩

theorem Erases.lit_inv {l : Literal} (h : Erases env Us Δ (.lit l) t) :
    ErasesBox env Us Δ (.lit l) t ∨
      (env.ContainsLits l ∧ Erases env Us Δ l.toConstructor t) := by
  cases h with
  | box htr her => exact .inl ⟨⟨_, htr, her⟩, rfl⟩
  | lit hcl hl => exact .inr ⟨hcl, hl⟩

theorem Erases.mdata_inv {d : MData} {e : Expr} (h : Erases env Us Δ (.mdata d e) t) :
    ErasesBox env Us Δ (.mdata d e) t ∨ Erases env Us Δ e t := by
  cases h with
  | box htr her => exact .inl ⟨⟨_, htr, her⟩, rfl⟩
  | mdata he => exact .inr he

/-! ## Inhabitation

The relation is inhabited, and so are its two `Expr.const` readings. The readings are
witnessed on a hand-built environment declaring one inductive block — a type former `T` in
`Prop` with a nullary constructor and its eliminator — and one definition, both read off the
`VEnv.WF'` list the environment is built from.
-/

/-- The relation is inhabited by a closed derivation that uses no box rule: metadata is
transparent, and a λ-binder's variable keeps its index. -/
example (env : VEnv) (Us : List Name) (d : MData) (n : Name) (bi : BinderInfo) :
    Erases env Us [] (.lam n (.sort .zero) (.mdata d (.bvar 0)) bi)
      (.lambda (.named n.toString) (.bvar 0)) :=
  .lam (.sort rfl) (.mdata (.bvar (e' := .bvar 0) (A := (VExpr.sort .zero).lift) rfl))

/-- Introduction from a one-axiom declaration list: a constant an environment declares at
the type of a closed axiom has that axiom's declaration as its origin. This is the cheapest
`ConstOrigin` introduction, and the shape a hand-built environment discharges the premise
with. -/
theorem ConstOrigin.of_axiom {env : VEnv} {c : Name} {A : VExpr}
    (hA : VEnv.IsType .empty 0 [] A) (hc : env.constants c = some ⟨0, A⟩) :
    ConstOrigin env c := by
  refine ⟨[.axiom ⟨⟨0, A⟩, c⟩], _, _, .decl (.axiom hA rfl) .empty, List.mem_cons_self .., ?_,
    rfl⟩
  refine ⟨fun {n a} h => ?_, fun h => h.elim, fun h => h.elim⟩
  simp only [VEnv.empty] at h
  split at h
  · rename_i heq; cases heq; cases h; exact hc
  · exact absurd h (by simp)

/-! ### A one-inductive, one-definition environment

`T : Prop` with the nullary constructor `mk` and the eliminator `rec` at one motive, one
minor and one ι rule, followed by the definition `d := mk`. Everything is literal, so the
staged extensions of `VEnv.addInduct` compute.
-/

/-- The fixture's type former. -/
def blkT : Name := `Blk.T
/-- The fixture's nullary constructor. -/
def blkMk : Name := `Blk.T.mk
/-- The fixture's eliminator. -/
def blkRec : Name := `Blk.T.rec
/-- The fixture's definition. -/
def blkDef : Name := `Blk.d

/-- The eliminator's motive premise, `C : T → Prop`. -/
def blkMotiveTy : VExpr := .forallE (.const blkT []) (.sort .zero)
/-- The eliminator's minor premise, `C mk`, under the motive binder. -/
def blkMinorTy : VExpr := .app (.bvar 0) (.const blkMk [])
/-- The eliminator's type, `∀ (C : T → Prop), C mk → ∀ z, C z`. -/
def blkRecTy : VExpr :=
  .forallE blkMotiveTy
    (.forallE blkMinorTy (.forallE (.const blkT []) (.app (.bvar 2) (.bvar 0))))
/-- The ι rule's reduct template: the minor, under the motive and minor binders. -/
def blkRuleRhs : VExpr := .lam blkMotiveTy (.lam blkMinorTy (.bvar 0))

/-- The constructor's declaration. -/
def blkCtorVal : VConstVal := { uvars := 0, type := .const blkT [], name := blkMk }
/-- The type former's declaration. -/
def blkTypeVal : VInductiveType :=
  { uvars := 0, type := .sort .zero, name := blkT, ctors := [blkCtorVal] }
/-- The eliminator's one ι rule, firing on the nullary constructor. -/
def blkRuleVal : VRecRule := { ctor := blkMk, ctorParams := 0, nfields := 0, rhs := blkRuleRhs }
/-- The eliminator's declaration. -/
def blkRecVal : VRecursor :=
  { uvars := 0, type := blkRecTy, name := blkRec, all := [blkT], numParams := 0,
    numMotives := 1, numMinors := 1, numIndices := 0, k := false, rules := [blkRuleVal] }
/-- The block: one type former, one constructor, one recursor, no parameters. -/
def blkDecl : VInductDecl := { uvars := 0, nparams := 0, types := [blkTypeVal], recs := [blkRecVal] }
/-- The definition that follows the block: `d : T := mk`. -/
def blkDefVal : VDefVal :=
  { uvars := 0, type := .const blkT [], value := .const blkMk [], name := blkDef }

/-- The environment after the type formers. -/
def blkEnvT : VEnv :=
  { VEnv.empty with constants := fun n => if blkT = n then some ⟨0, .sort .zero⟩ else none }
/-- The environment after the constructors. -/
def blkEnvC : VEnv :=
  { blkEnvT with
    constants := fun n => if blkMk = n then some ⟨0, .const blkT []⟩ else blkEnvT.constants n }
/-- The environment after the recursors. -/
def blkEnvR : VEnv :=
  { blkEnvC with
    constants := fun n => if blkRec = n then some ⟨0, blkRecTy⟩ else blkEnvC.constants n }

theorem blkDecl_addTypes : blkDecl.addTypes VEnv.empty = some blkEnvT := by
  simp [VInductDecl.addTypes, VEnv.addConst, VEnv.empty, blkDecl, blkTypeVal, blkEnvT]

theorem blkDecl_addCtors : blkDecl.addCtors blkEnvT = some blkEnvC := by
  simp [VInductDecl.addCtors, VEnv.addConst, blkDecl, blkTypeVal, blkCtorVal, blkEnvT, blkEnvC,
    blkT, blkMk]
  rfl

theorem blkDecl_addRecs : blkDecl.addRecs blkEnvC = some blkEnvR := by
  simp [VInductDecl.addRecs, VEnv.addConst, blkDecl, blkRecVal, blkEnvC, blkEnvR, blkEnvT,
    blkT, blkMk, blkRec]
  rfl

theorem blkDecl_addTypesCtorsRecs : blkDecl.addTypesCtorsRecs VEnv.empty = some blkEnvR := by
  simp [VInductDecl.addTypesCtorsRecs, VInductDecl.addTypesCtors, blkDecl_addTypes,
    blkDecl_addCtors, blkDecl_addRecs]

theorem blkEnvT_T : blkEnvT.constants blkT = some ⟨0, .sort .zero⟩ := by simp [blkEnvT]
theorem blkEnvC_T : blkEnvC.constants blkT = some ⟨0, .sort .zero⟩ := by
  simp [blkEnvC, blkEnvT, blkT, blkMk]
theorem blkEnvC_mk : blkEnvC.constants blkMk = some ⟨0, .const blkT []⟩ := by simp [blkEnvC]
theorem blkEnvR_T : blkEnvR.constants blkT = some ⟨0, .sort .zero⟩ := by
  simp [blkEnvR, blkEnvC, blkEnvT, blkT, blkMk, blkRec]
theorem blkEnvR_mk : blkEnvR.constants blkMk = some ⟨0, .const blkT []⟩ := by
  simp [blkEnvR, blkEnvC, blkT, blkMk, blkRec]
theorem blkEnvR_rec : blkEnvR.constants blkRec = some ⟨0, blkRecTy⟩ := by simp [blkEnvR]

/-- The type former is a `Prop`-valued constant once it is declared. -/
theorem blkT_ty {Γ : List VExpr} : VEnv.HasType blkEnvC 0 Γ (.const blkT []) (.sort .zero) :=
  VEnv.HasType.const blkEnvC_T nofun rfl

/-- The constructor inhabits the type former. -/
theorem blkMk_ty {Γ : List VExpr} :
    VEnv.HasType blkEnvC 0 Γ (.const blkMk []) (.const blkT []) :=
  VEnv.HasType.const blkEnvC_mk nofun rfl

theorem blkMotive_ty {Γ : List VExpr} :
    VEnv.HasType blkEnvC 0 Γ blkMotiveTy (.sort (.imax .zero (.succ .zero))) :=
  VEnv.HasType.forallE blkT_ty (VEnv.HasType.sort (l := .zero) trivial)

theorem blkMinor_ty : VEnv.HasType blkEnvC 0 [blkMotiveTy] blkMinorTy (.sort .zero) :=
  VEnv.HasType.app (B := .sort .zero) (VEnv.HasType.bvar .zero) blkMk_ty

/-- The eliminator's type is a type once the constructor is declared. -/
theorem blkRecTy_ty : VEnv.HasType blkEnvC 0 [] blkRecTy
    (.sort (.imax (.imax .zero (.succ .zero)) (.imax .zero (.imax .zero .zero)))) :=
  VEnv.HasType.forallE blkMotive_ty <|
    VEnv.HasType.forallE blkMinor_ty <|
      VEnv.HasType.forallE blkT_ty <|
        VEnv.HasType.app (B := .sort .zero) (VEnv.HasType.bvar (.succ (.succ .zero)))
          (VEnv.HasType.bvar .zero)

theorem blkT_tyR {Γ : List VExpr} : VEnv.HasType blkEnvR 0 Γ (.const blkT []) (.sort .zero) :=
  VEnv.HasType.const blkEnvR_T nofun rfl
theorem blkMk_tyR {Γ : List VExpr} :
    VEnv.HasType blkEnvR 0 Γ (.const blkMk []) (.const blkT []) :=
  VEnv.HasType.const blkEnvR_mk nofun rfl
theorem blkRec_tyR {Γ : List VExpr} : VEnv.HasType blkEnvR 0 Γ (.const blkRec []) blkRecTy :=
  VEnv.HasType.const blkEnvR_rec nofun rfl
theorem blkMotive_tyR {Γ : List VExpr} :
    VEnv.HasType blkEnvR 0 Γ blkMotiveTy (.sort (.imax .zero (.succ .zero))) :=
  VEnv.HasType.forallE blkT_tyR (VEnv.HasType.sort (l := .zero) trivial)
theorem blkMinor_tyR {Γ : List VExpr} :
    VEnv.HasType blkEnvR 0 (blkMotiveTy :: Γ) blkMinorTy (.sort .zero) :=
  VEnv.HasType.app (B := .sort .zero) (VEnv.HasType.bvar .zero) blkMk_tyR

open Pattern.RHS (fixed) in
/--
The ι rule is typed: at the generic redex `rec C h mk` over the context of the motive and
the minor, redex and reduct have the type `C mk`.

The match supplies the two holes, `SimplePattern.iotaRHS'_apply` computes the reduct as the
template applied to them, and both sides are typed by the same two applications.
-/
theorem blkDecl_patTyped (hc : blkRuleRhs.Closed) :
    blkEnvR.PatTyped (SimplePattern.iota blkRec 2 blkMk 0).toPattern
      (SimplePattern.iotaRHS blkRec blkMk 0 1 1 0 0 0 blkRuleRhs hc, .true) := by
  obtain ⟨g1, hm1, hg1⟩ :=
    Pattern.matches_varN_const (c := blkRec) (ls := []) 2 [.bvar 1, .bvar 0] rfl
  obtain ⟨g2, hm2, hg2⟩ := Pattern.matches_varN_const (c := blkMk) (ls := []) 0 [] rfl
  have happly : Pattern.RHS.apply (p := (SimplePattern.iota blkRec 2 blkMk 0).toPattern)
      (VLevel.params 0) (Sum.elim g1 g2)
      (SimplePattern.iotaRHS blkRec blkMk 0 1 1 0 0 0 blkRuleRhs hc)
      = .app (.app blkRuleRhs (.bvar 1)) (.bvar 0) :=
    SimplePattern.iotaRHS'_apply blkRec blkMk 2 0 0 0 blkRuleRhs hc []
      (Sum.elim g1 g2) (recArgs := [.bvar 1, .bvar 0]) (ctorArgs := []) rfl rfl hg1 hg2
  refine ⟨0, [blkMinorTy, blkMotiveTy], _, Sum.elim g1 g2, .app (.bvar 1) (.const blkMk []),
    hm1.app hm2, ?_, ?_, ?_⟩
  · have h0 : g1 (some none) = .bvar 1 := hg1 0 (by omega)
    have h1 : g1 none = .bvar 0 := hg1 1 (by omega)
    have hR : SimplePattern.iotaRHS blkRec blkMk 0 1 1 0 0 0 blkRuleRhs hc =
        ((fixed blkRuleRhs hc).app
          (Pattern.RHS.var (p := (SimplePattern.iota blkRec 2 blkMk 0).toPattern)
            (Sum.inl (some none)))).app
          (Pattern.RHS.var (p := (SimplePattern.iota blkRec 2 blkMk 0).toPattern)
            (Sum.inl none)) := rfl
    rw [show ((SimplePattern.iotaRHS blkRec blkMk 0 1 1 0 0 0 blkRuleRhs hc,
      Pattern.Check.true).fst) = _ from hR]
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      simp only [Pattern.RHS.Uses, false_or] at hx
      rcases hx with rfl | rfl
      · exact ⟨1, by simp, h0⟩
      · exact ⟨0, by simp, h1⟩
    · intro x y hx hy hxy
      simp only [Pattern.RHS.Uses, false_or] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · rfl
      · exact absurd ((h0.symm.trans hxy).trans h1) (by simp)
      · exact absurd ((h1.symm.trans hxy).trans h0) (by simp)
      · rfl
    · intro i hi
      simp only [List.length_cons, List.length_nil] at hi
      have hi2 : i = 0 ∨ i = 1 := by omega
      rcases hi2 with rfl | rfl
      · exact ⟨Sum.inl none, Or.inr rfl, h1⟩
      · exact ⟨Sum.inl (some none), Or.inl (Or.inr rfl), h0⟩
  · exact ((blkRec_tyR.app (VEnv.HasType.bvar (.succ .zero))).app
      (VEnv.HasType.bvar .zero)).app blkMk_tyR
  · rw [happly]
    exact ((VEnv.HasType.lam blkMotive_tyR (VEnv.HasType.lam blkMinor_tyR
      (VEnv.HasType.bvar .zero))).app (VEnv.HasType.bvar (.succ .zero))).app
      (VEnv.HasType.bvar .zero)

/-- The block is a well-formed declaration: the type former, the constructor and the
eliminator are typed at their stages, the syntactic clauses hold by computation, and the ι
rule is typed by `blkDecl_patTyped`. -/
theorem blkDecl_wf : blkDecl.WF VEnv.empty where
  types_wf := by
    intro t ht
    cases List.mem_singleton.1 ht
    exact ⟨.succ .zero, VEnv.HasType.sort (l := .zero) trivial⟩
  ctors_wf := by
    intro envT h t ht c hc
    rw [blkDecl_addTypes] at h; cases h
    cases List.mem_singleton.1 ht
    cases List.mem_singleton.1 hc
    exact ⟨.zero, VEnv.HasType.const (ci := ⟨0, .sort .zero⟩) blkEnvT_T nofun rfl⟩
  recs_wf := by
    intro envC h r hr
    rw [show blkDecl.addTypesCtors VEnv.empty = some blkEnvC by
      simp [VInductDecl.addTypesCtors, blkDecl_addTypes, blkDecl_addCtors]] at h
    cases h
    cases List.mem_singleton.1 hr
    exact ⟨_, blkRecTy_ty⟩
  types_uvars := by intro t ht; cases List.mem_singleton.1 ht; rfl
  ctors_uvars := by
    intro t ht c hc; cases List.mem_singleton.1 ht; cases List.mem_singleton.1 hc; rfl
  universes := by
    intro envT h
    refine ⟨.zero, ?_, ?_, ?_⟩
    · intro t ht; cases List.mem_singleton.1 ht; exact ⟨rfl, Nat.le_refl _⟩
    · intro t ht c hc i hi
      cases List.mem_singleton.1 ht; cases List.mem_singleton.1 hc
      simp [blkCtorVal, VExpr.piArity] at hi
    · rintro ⟨r, hr, hu⟩
      cases List.mem_singleton.1 hr
      exact absurd hu (by simp [blkRecVal])
  recs_elim := by
    intro r hr
    cases List.mem_singleton.1 hr
    refine ⟨.inl rfl, ?_⟩
    intro i hi
    have : i = 0 := by simpa [blkRecVal] using hi
    subst this
    exact ⟨blkMotiveTy, rfl, rfl⟩
  rec_params := by intro r hr; cases List.mem_singleton.1 hr; rfl
  ctors_params := by
    intro t ht c hc; cases List.mem_singleton.1 ht; cases List.mem_singleton.1 hc; rfl
  ctors_result := by
    intro t ht c hc
    cases List.mem_singleton.1 ht; cases List.mem_singleton.1 hc
    exact ⟨0, rfl, [], [], rfl, rfl⟩
  ctors_positive := by
    intro t ht c hc
    cases List.mem_singleton.1 ht; cases List.mem_singleton.1 hc
    exact ⟨nofun, by intro i hi; simp [blkCtorVal, VExpr.piArity] at hi⟩
  recs_over_block := by
    intro r hr; cases List.mem_singleton.1 hr
    exact ⟨blkTypeVal, List.mem_singleton_self _, rfl⟩
  rec_counts := by
    intro r hr; cases List.mem_singleton.1 hr
    refine ⟨rfl, rfl, ?_⟩
    intro t ht _; cases List.mem_singleton.1 ht; rfl
  rec_shape := by
    intro r hr; cases List.mem_singleton.1 hr
    refine ⟨rfl, ?_, ?_, 0, Nat.zero_lt_one, ⟨_, rfl, blkT, rfl, ⟨[], rfl⟩, _, rfl, rfl⟩, rfl⟩
    · intro i hi
      have : i = 0 := by simpa [blkRecVal] using hi
      subst this
      exact ⟨blkMotiveTy, rfl, ⟨.zero, rfl⟩, rfl⟩
    · intro i hi
      have : i = 0 := by simpa [blkRecVal] using hi
      subst this
      exact ⟨blkMinorTy, rfl, 0, Nat.zero_lt_one, rfl⟩
  rules_nodup := by
    intro r hr; cases List.mem_singleton.1 hr
    simp [blkRecVal, blkRuleVal]
  rules_ctor := by
    intro r hr ru hru
    cases List.mem_singleton.1 hr; cases List.mem_singleton.1 hru
    exact ⟨blkTypeVal, List.mem_singleton_self _, rfl, blkCtorVal, List.mem_singleton_self _,
      rfl, rfl, rfl, [], [], rfl, rfl⟩
  types_have_rec := by
    intro t ht; cases List.mem_singleton.1 ht
    exact ⟨blkRecVal, List.mem_singleton_self _, rfl⟩
  rules_total := by
    intro r hr t ht _ c hc
    cases List.mem_singleton.1 hr; cases List.mem_singleton.1 ht
    cases List.mem_singleton.1 hc
    exact ⟨blkRuleVal, List.mem_singleton_self _, rfl⟩
  rule_shape := by
    intro r hr ru hru
    cases List.mem_singleton.1 hr; cases List.mem_singleton.1 hru
    refine ⟨0, Nat.zero_lt_one, blkMinorTy, rfl, ⟨⟨_, rfl⟩, _, rfl, rfl⟩, Nat.zero_le _, rfl,
      [], rfl, rfl⟩
  rules_wf := by
    intro envR h r hr ru hru hc
    rw [blkDecl_addTypesCtorsRecs] at h
    cases h
    cases List.mem_singleton.1 hr
    cases List.mem_singleton.1 hru
    exact blkDecl_patTyped hc

/-- The environment the block alone produces. -/
def blkEnvB : VEnv := (VEnv.empty.addInduct blkDecl).getD .empty

theorem blkEnvB_eq : VEnv.empty.addInduct blkDecl = some blkEnvB := rfl
theorem blkEnvB_mk : blkEnvB.constants blkMk = some ⟨0, .const blkT []⟩ := rfl

/-- The fixture's environment: the block, then the definition `d := mk`. -/
def blkEnv : VEnv :=
  ((blkEnvB.addConst blkDef blkDefVal.toVConstant).getD .empty).addDefEq blkDefVal.toDefEq

/-- The fixture is well formed, at the declaration list the two readings are read off. -/
theorem blk_wf' : VEnv.WF' [.def blkDefVal, .induct blkDecl] blkEnv :=
  .decl (.def (VEnv.HasType.const blkEnvB_mk nofun rfl) rfl)
    (.decl (.induct blkDecl_wf blkEnvB_eq) .empty)

/-- The fixture's λ□ inductive identifier. -/
def blkIid : InductiveId := ⟨indBlockKername [blkT], 0⟩

theorem blk_ctorOf : CtorOf blkEnv blkMk blkT 0 :=
  ⟨_, _, blkDecl, blkTypeVal, blkCtorVal, blk_wf',
    List.mem_cons_of_mem _ (List.mem_cons_self ..), VEnv.LE.rfl,
    List.mem_cons_self .., rfl, rfl, rfl⟩

theorem blk_indInfo : IndInfo blkEnv blkT blkIid 0 [0] := by
  refine ⟨_, _, blkDecl, blkTypeVal, blk_wf',
    List.mem_cons_of_mem _ (List.mem_cons_self ..), VEnv.LE.rfl, rfl, rfl, ?_, rfl, rfl⟩
  rfl

theorem blk_constOrigin : ConstOrigin blkEnv blkDef :=
  ⟨_, _, .def blkDefVal, blk_wf', List.mem_cons_self .., VEnv.LE.rfl, rfl⟩

theorem blk_constants : blkEnv.constants blkDef = some ⟨0, .const blkT []⟩ := rfl

/-- **`Erases.ctor` fires**: the fixture's constructor erases to its λ□ constructor node,
with `CtorOf` and `IndInfo` exhibited from the fixture's own declaration list. -/
theorem erases_ctor_fires (Us : List Name) (Δ : VLCtx) (us : List Level) :
    Erases blkEnv Us Δ (.const blkMk us) (.construct blkIid 0 []) :=
  .ctor blk_ctorOf blk_indInfo

/-- **`Erases.const` fires**: the fixture's definition erases to its kername, with
`ConstOrigin` exhibited from the same declaration list. -/
theorem erases_const_fires (Us : List Name) (Δ : VLCtx) (us : List Level) :
    Erases blkEnv Us Δ (.const blkDef us) (.const (toKername blkDef)) :=
  .const blk_constants blk_constOrigin

/-! ### Why the `proj` rule needs its relevance premise

The fixture's type former is `Prop`-valued, so `InformativeInd blkEnv blkT` fails and the
`proj` rule does not fire at it — which is the point. Without the premise the rule would
fire, and the discriminant of a projection out of a propositional structure is a proof, whose
image the `box` rule may make `.box`. At `eraseFlags` that target term has **no** step: the
applied-form rule wants a constructor spine, the block rule is off, and the propositional rule
needs `with_prop_case`, which the erasure correctness statement does not enable. So the arm of
`erases_correct` would be refutable, not merely unprovable.
-/

/-- **A boxed discriminant is stuck.** No projection of `.box` evaluates at `eraseFlags`, in
any environment and at any projection. -/
theorem erases_proj_needs_informative (Γ : GlobalDeclarations) (p : ProjectionInfo) :
    ¬ ∃ v, WcbvEval Γ eraseFlags (.proj p .box) v := by
  have hbox : ∀ {w : LBTerm}, WcbvEval Γ eraseFlags .box w → w = .box := fun h => by
    cases h; rfl
  rintro ⟨v, h⟩
  cases h with
  | proj _ _ hdiscr _ _ =>
      have hsp := congrArg LBTerm.spineHead (hbox hdiscr)
      rw [LBTerm.spineHead_mkApps] at hsp
      simp [LBTerm.spineHead] at hsp
  | proj_block hb => exact absurd hb (by decide)
  | proj_prop hpc => exact absurd hpc (by decide)

end LeanToLambdaBox
