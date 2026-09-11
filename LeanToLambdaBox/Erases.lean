import LeanToLambdaBox.Basic
import LeanToLambdaBox.Erasability
import Lean4Lean.Verify.Typing.Expr

/-!
# `Erases` — the erasure relation over `Lean.Expr`

`Erases env Us Δ e t` relates a source term `e`, read in the local context `Δ` exactly as
lean4lean's `TrExprS` reads it, to a λ□ image `t`. It is the erasure relation of Sozeau et
al. transposed to `Lean.Expr`: `TrExprS` with the target `VExpr` replaced by `LBTerm`,
`Expr.sort` and `Expr.forallE` absorbed into the box rule, and a box rule added.

Ten rules, no side condition and no name registry; `doc/rules-Erases.md` is the rule-by-rule
transport table, and the `#guard` below pins the arm list to it. The relation is
deliberately non-deterministic at `box`: an irrelevant term relates both to its structural
image and to `LBTerm.box`.

The three compilation steps a congruence over `Lean.Expr` cannot state — a saturated
constructor application, an eliminator application, and top-level recursion, none of which
is a `Lean.Expr` node — belong to the pass layer (`doc/rules-Lower.md`), not here.

`IndInfo` is declared here because `Erases.proj` is its first consumer.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

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
  /-- A constant declared in `env` erases to its kername, universe levels dropped. The
      kername is the value of the function `toKername`, so the rule takes no kername
      parameter and consults no registry. -/
  | const {Δ c us ci} (h : env.constants c = some ci) :
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
      `S` is a block-level type former with `np` parameters and a single constructor of `nf`
      fields. There is no `TrExprS` premise: `TrProj` pins parameters only up to
      definitional equality, so a term premise would demand an equality that does not
      hold. -/
  | proj {Δ S i e t iid np nf} (hs : IndInfo env S iid np [nf]) (hi : i < nf)
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
  [``Erases.box, ``Erases.bvar, ``Erases.fvar, ``Erases.const, ``Erases.app,
   ``Erases.lam, ``Erases.letE, ``Erases.proj, ``Erases.lit, ``Erases.mdata]

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

theorem Erases.const_inv {c : Name} {us : List Level} (h : Erases env Us Δ (.const c us) t) :
    ErasesBox env Us Δ (.const c us) t ∨
      ((∃ ci, env.constants c = some ci) ∧ t = .const (toKername c)) := by
  cases h with
  | box htr her => exact .inl ⟨⟨_, htr, her⟩, rfl⟩
  | const hc => exact .inr ⟨⟨_, hc⟩, rfl⟩

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
      (∃ iid np nf d, IndInfo env S iid np [nf] ∧ i < nf ∧ Erases env Us Δ e d ∧
        t = .proj ⟨iid, np, i⟩ d) := by
  cases h with
  | box htr her => exact .inl ⟨⟨_, htr, her⟩, rfl⟩
  | proj hs hi hd => exact .inr ⟨_, _, _, _, hs, hi, hd, rfl⟩

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

/-! ## Inhabitation -/

/-- The relation is inhabited by a closed derivation that uses no box rule: metadata is
transparent, and a λ-binder's variable keeps its index. -/
example (env : VEnv) (Us : List Name) (d : MData) (n : Name) (bi : BinderInfo) :
    Erases env Us [] (.lam n (.sort .zero) (.mdata d (.bvar 0)) bi)
      (.lambda (.named n.toString) (.bvar 0)) :=
  .lam (.sort rfl) (.mdata (.bvar (e' := .bvar 0) (A := (VExpr.sort .zero).lift) rfl))

end LeanToLambdaBox
