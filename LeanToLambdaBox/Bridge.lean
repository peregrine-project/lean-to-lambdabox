import LeanToLambdaBox.Capstone
import Lean4Lean.Verify.LocalContext

/-!
# `BridgeInv` — the state-side contract of the `visitExpr` bridge

The invariant the bridge's induction carries: what the reader, the run state, the ambient
name generator and the modelled local context agree on at every point of a run.

* `fixvarMap` is the block-local map `Erasure.visitMutual` installs, and `BridgeInv.fixvars`
  reads it as the pair of indices `ErasesLBFix` is stated at.
* `ErasesLBMode` and `ErasesLBAltMode` are the refinement conclusion in either fixvar mode:
  outside a block the emitted term is `ErasesLB`'s image, inside one it is `ErasesLBFix`'s.
* `Supported.subterm` transports the fragment condition to a subterm, which is what the
  motives' recursive premises need.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean Erasure Witness
open Lean4Lean.TypeChecker (MLCtx kernelNGen)

/-! ## The block-local fixvar map -/

/-- The map `Erasure.visitMutual` installs while erasing a mutual block: each member's source
name — already `Erasure.remove_unsafe_rec`'d — mapped to the fresh identifier minted for it. -/
def fixvarMap (nms : List Name) (ids : List FVarId) : Std.HashMap Name FVarId :=
  Std.HashMap.ofList (nms.zip ids)

/-! ## The refinement conclusion, in either fixvar mode -/

/-- What a sub-run's emitted term is related to, read off the reader's fixvar mode. Outside a
mutual block the term is the composite's image; inside one the block's own constants have been
rewritten to its fix variables, which is the third factor `ErasesLBFix` adds. The block's
indices are the ones the reader's map is built from. -/
def ErasesLBMode (ctx : ErasureContext) (env : VEnv) (Us : List Name)
    (Γspec : GlobalDeclarations) (Δ : VLCtx) (e : Expr) (t : LBTerm) : Prop :=
  (ctx.fixvars = none → ErasesLB env Us Γspec Δ e t) ∧
  (∀ nms ids, ctx.fixvars = some (fixvarMap nms ids) →
    ErasesLBFix env Us Γspec (nms.map toKername) ids Δ e t)

/-- `ErasesLBMode` for one `case` alternative: what `Erasure.visitAlt` returns is related to
its source minor premise in whichever mode the reader is in. -/
def ErasesLBAltMode (ctx : ErasureContext) (env : VEnv) (Us : List Name)
    (Γspec : GlobalDeclarations) (Δ : VLCtx) (nf : Nat) (m : Expr)
    (alt : List BinderName × LBTerm) : Prop :=
  (ctx.fixvars = none → ErasesLBAlt env Us Γspec Δ nf m alt) ∧
  (∀ nms ids, ctx.fixvars = some (fixvarMap nms ids) →
    ErasesLBFixAlt env Us Γspec (nms.map toKername) ids Δ nf m alt)

/-- The ambient mode's reading, which is what `visitExpr_refines_erasesLB` returns. -/
theorem ErasesLBMode.ambient {ctx : ErasureContext} {env : VEnv} {Us : List Name}
    {Γspec : GlobalDeclarations} {Δ : VLCtx} {e : Expr} {t : LBTerm}
    (h : ErasesLBMode ctx env Us Γspec Δ e t) (hfx : ctx.fixvars = none) :
    ErasesLB env Us Γspec Δ e t := h.1 hfx

/-- The block mode's reading, which is what `visitExpr_refines_erasesLBFix` returns. -/
theorem ErasesLBMode.block {ctx : ErasureContext} {env : VEnv} {Us : List Name}
    {Γspec : GlobalDeclarations} {Δ : VLCtx} {e : Expr} {t : LBTerm} {nms : List Name}
    {ids : List FVarId} (h : ErasesLBMode ctx env Us Γspec Δ e t)
    (hfx : ctx.fixvars = some (fixvarMap nms ids)) :
    ErasesLBFix env Us Γspec (nms.map toKername) ids Δ e t := h.2 nms ids hfx

/-! ## The invariant -/

/-- The bridge invariant, carried through the eighteen-motive induction: what the reader, the
state, the generator and the modelled context agree on. The registry side is one field —
canonicity — because the specification environment is quantified in at the final state by
`SpecEnv` rather than fixed before the run; the fixvar side is one field because the mode and
the freshness discipline are properties of the same installed map. -/
structure BridgeInv (env : VEnv) (Us : List Name) (cfg₀ : ErasureConfig) (gen : NameGenerator)
    (ctx : ErasureContext) (s : ErasureState) (Δ : VLCtx) : Prop where
  /-- The reader's local context is modelled by `Δ`, witnessed by an ambient `MLCtx`. -/
  mlc : ∃ m : MLCtx, m.WF env Us ∧ m.lctx = ctx.lctx ∧ m.vlctx = Δ
  /-- The reader's level scope is a prefix of the ambient one: along a prefix no level index
      moves, so a sub-run's facts transport to `Us` on the nose. -/
  lparams : ctx.lparams <+: Us
  /-- The reader's configuration is the one the statement is made at. `Erasure.run` builds the
      only reader from scratch and no `withReader` in the erasure touches `config`. -/
  cfg : ctx.config = cfg₀
  /-- Every `Δ` variable is reserved by the kernel's fixed generator, which is the freshness
      premise the relevance oracle's soundness takes. -/
  kfresh : ∀ fv ∈ Δ.fvars, kernelNGen.Reserves fv
  /-- Every `Δ` variable is reserved by the ambient generator, so a freshly minted identifier
      is not one of them. -/
  reserved : ∀ fv ∈ Δ.fvars, gen.Reserves fv
  /-- The reader is either outside a mutual block, or inside one whose map is the block's own
      names against distinct identifiers, each reserved and none of them a `Δ` variable —
      `Erasure.visitMutual` mints them before any binder of the member bodies is opened. -/
  fixvars : ctx.fixvars = none ∨
    ∃ nms ids, ctx.fixvars = some (fixvarMap nms ids) ∧ nms.length = ids.length ∧
      ids.Nodup ∧ ∀ x ∈ ids, gen.Reserves x ∧ x ∉ Δ.fvars
  /-- Every registered kername is the canonical one. Every writer on the registration path
      inserts under `toKername`, so this is maintained, never assumed. -/
  canon : CanonicalConstants s

/-- The `TrLCtx` correspondence, re-derived from the `mlc` witness. -/
theorem BridgeInv.trlctx {env : VEnv} {Us : List Name} {cfg : ErasureConfig}
    {gen : NameGenerator} {ctx : ErasureContext} {s : ErasureState} {Δ : VLCtx}
    (h : BridgeInv env Us cfg gen ctx s Δ) : TrLCtx env Us ctx.lctx Δ := by
  obtain ⟨m, mwf, hlctx, hvlctx⟩ := h.mlc
  rw [← hlctx, ← hvlctx]; exact mwf.tr

/-- The modelled context is well formed — what the erasure relation's own lemmas take. -/
theorem BridgeInv.vlctx_wf {env : VEnv} {Us : List Name} {cfg : ErasureConfig}
    {gen : NameGenerator} {ctx : ErasureContext} {s : ErasureState} {Δ : VLCtx}
    (h : BridgeInv env Us cfg gen ctx s Δ) : VLCtx.WF env Us.length Δ :=
  h.trlctx.wf

/-- The modelled context has no de Bruijn entries: every entry the run conses is fvar-tagged
and the entry point is empty. -/
theorem BridgeInv.noBV {env : VEnv} {Us : List Name} {cfg : ErasureConfig}
    {gen : NameGenerator} {ctx : ErasureContext} {s : ErasureState} {Δ : VLCtx}
    (h : BridgeInv env Us cfg gen ctx s Δ) : Δ.NoBV := by
  obtain ⟨m, -, -, hvlctx⟩ := h.mlc
  rw [← hvlctx]; exact m.noBV

/-- The invariant is monotone in the generator: reservations survive advancement. -/
theorem BridgeInv.mono {env : VEnv} {Us : List Name} {cfg : ErasureConfig}
    {gen gen' : NameGenerator} {ctx : ErasureContext} {s : ErasureState} {Δ : VLCtx}
    (h : BridgeInv env Us cfg gen ctx s Δ) (hle : gen ≤ gen') :
    BridgeInv env Us cfg gen' ctx s Δ where
  mlc := h.mlc
  lparams := h.lparams
  cfg := h.cfg
  kfresh := h.kfresh
  reserved fv hfv := (h.reserved fv hfv).mono hle
  fixvars := by
    rcases h.fixvars with hn | ⟨nms, ids, hm, hlen, hnd, hfr⟩
    · exact .inl hn
    · exact .inr ⟨nms, ids, hm, hlen, hnd, fun x hx => ⟨((hfr x hx).1).mono hle, (hfr x hx).2⟩⟩
  canon := h.canon

/-- The invariant survives state growth: only canonicity reads the state, and
`Erasure.RunConcl.canon` is what preserves it. -/
theorem BridgeInv.mono_state {env : VEnv} {Us : List Name} {cfg : ErasureConfig}
    {gen : NameGenerator} {ctx : ErasureContext} {s s' : ErasureState} {Δ : VLCtx}
    (h : BridgeInv env Us cfg gen ctx s Δ) (hrc : RunConcl s s') :
    BridgeInv env Us cfg gen ctx s' Δ where
  mlc := h.mlc
  lparams := h.lparams
  cfg := h.cfg
  kfresh := h.kfresh
  reserved := h.reserved
  fixvars := h.fixvars
  canon := hrc.canon h.canon


/-! ## Extending the context across a binder

`Erasure.withLocalDecl` and `Erasure.withLocalDef` push a `mkLocalDecl`/`mkLetDecl` onto the
reader's local context; these carry the invariant across in lockstep. lean4lean has the
ingredients and not the assembled statement, so the two `TrLCtx` extensions come first.
-/

/-- The context correspondence, extended by a λ binder. -/
theorem TrLCtx.mkLocalDecl {env : VEnv} {Us : List Name} {lctx : LocalContext}
    {Δ : VLCtx} {x : FVarId} {n : Name} {ty : Expr} {ty' : VExpr} {bi : BinderInfo}
    (H : TrLCtx env Us lctx Δ) (hx : lctx.find? x = none)
    (hty : TrExprS env Us Δ ty ty') (hty' : env.IsType Us.length Δ.toCtx ty') :
    TrLCtx env Us (lctx.mkLocalDecl x n ty bi)
      ((some (x, ty.fvarsList), .vlam ty') :: Δ) :=
  ⟨H.1.mkLocalDecl hx, by
    rw [LocalContext.mkLocalDecl_toList]
    exact H.2.cons (.vlam hty hty')⟩

/-- The context correspondence, extended by a `let` binder. -/
theorem TrLCtx.mkLetDecl {env : VEnv} {Us : List Name} {lctx : LocalContext}
    {Δ : VLCtx} {x : FVarId} {n : Name} {ty val : Expr} {ty' val' : VExpr} {nd : Bool}
    (H : TrLCtx env Us lctx Δ) (hx : lctx.find? x = none)
    (hty : TrExprS env Us Δ ty ty') (hval : TrExprS env Us Δ val val')
    (hvt : env.HasType Us.length Δ.toCtx val' ty') :
    TrLCtx env Us (lctx.mkLetDecl x n ty val nd)
      ((some (x, ty.fvarsList ++ val.fvarsList), .vlet ty' val') :: Δ) :=
  ⟨H.1.mkLetDecl hx, by
    rw [LocalContext.mkLetDecl_toList]
    exact H.2.cons (.vlet hty hval hvt)⟩

/-- **The invariant across `Erasure.withLocalDecl`.** The new variable is fresh for the old
generator and reserved by the new one, which is what keeps it apart from a block's fix
variables and from every entry already in `Δ`. -/
theorem BridgeInv.mkLocalDecl {env : VEnv} {Us : List Name} {cfg₀ : ErasureConfig}
    {gen gen' : NameGenerator} {ctx : ErasureContext} {s : ErasureState} {Δ : VLCtx}
    {x : FVarId} {n : Name} {ty : Expr} {ty' : VExpr} {bi : BinderInfo}
    (hinv : BridgeInv env Us cfg₀ gen ctx s Δ)
    (hty : TrExprS env Us Δ ty ty') (hty' : env.IsType Us.length Δ.toCtx ty')
    (hx : x ∉ Δ.fvars) (hnres : ¬ gen.Reserves x)
    (hle : gen ≤ gen') (hres : gen'.Reserves x) (hkres : kernelNGen.Reserves x) :
    BridgeInv env Us cfg₀ gen' { ctx with lctx := ctx.lctx.mkLocalDecl x n ty bi } s
      ((some (x, ty.fvarsList), .vlam ty') :: Δ) where
  mlc := by
    obtain ⟨m, mwf, hlctx, hvlctx⟩ := hinv.mlc
    refine ⟨m.vlam x n ty ty' bi, ⟨mwf, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [hlctx]; exact hinv.trlctx.find?_eq_none.mpr hx
    · rw [hvlctx]; exact hty
    · rw [hvlctx]; exact hty'
    · show m.lctx.mkLocalDecl x n ty bi = _; rw [hlctx]
    · show (some (x, ty.fvarsList), VLocalDecl.vlam ty') :: m.vlctx = _; rw [hvlctx]
  lparams := hinv.lparams
  cfg := hinv.cfg
  kfresh := by
    intro fv hfv
    have hcase : fv = x ∨ fv ∈ Δ.fvars := by simpa using hfv
    rcases hcase with rfl | hfv'
    · exact hkres
    · exact hinv.kfresh fv hfv'
  reserved := by
    intro fv hfv
    have hcase : fv = x ∨ fv ∈ Δ.fvars := by simpa using hfv
    rcases hcase with rfl | hfv'
    · exact hres
    · exact (hinv.reserved fv hfv').mono hle
  fixvars := by
    rcases hinv.fixvars with hn | ⟨nms, ids, hm, hlen, hnd, hfr⟩
    · exact .inl hn
    · refine .inr ⟨nms, ids, hm, hlen, hnd, fun y hy => ?_⟩
      obtain ⟨hry, hΔy⟩ := hfr y hy
      refine ⟨hry.mono hle, fun hmem => ?_⟩
      have hcase : y = x ∨ y ∈ Δ.fvars := by simpa using hmem
      rcases hcase with rfl | hmem'
      · exact hnres hry
      · exact hΔy hmem'
  canon := hinv.canon

/-- **The invariant across `Erasure.withLocalDef`.** The shipping wrapper builds the let
declaration at the default `nonDep`, which is the one `MLCtx.vlet` records. -/
theorem BridgeInv.mkLetDecl {env : VEnv} {Us : List Name} {cfg₀ : ErasureConfig}
    {gen gen' : NameGenerator} {ctx : ErasureContext} {s : ErasureState} {Δ : VLCtx}
    {x : FVarId} {n : Name} {ty v : Expr} {ty' val' : VExpr}
    (hinv : BridgeInv env Us cfg₀ gen ctx s Δ)
    (hty : TrExprS env Us Δ ty ty') (hval : TrExprS env Us Δ v val')
    (hvt : env.HasType Us.length Δ.toCtx val' ty')
    (hx : x ∉ Δ.fvars) (hnres : ¬ gen.Reserves x)
    (hle : gen ≤ gen') (hres : gen'.Reserves x) (hkres : kernelNGen.Reserves x) :
    BridgeInv env Us cfg₀ gen' { ctx with lctx := ctx.lctx.mkLetDecl x n ty v } s
      ((some (x, ty.fvarsList ++ v.fvarsList), .vlet ty' val') :: Δ) where
  mlc := by
    obtain ⟨m, mwf, hlctx, hvlctx⟩ := hinv.mlc
    refine ⟨m.vlet x n ty v ty' val', ⟨mwf, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [hlctx]; exact hinv.trlctx.find?_eq_none.mpr hx
    · rw [hvlctx]; exact hty
    · rw [hvlctx]; exact hval
    · rw [hvlctx]; exact hvt
    · show m.lctx.mkLetDecl x n ty v = _; rw [hlctx]
    · show (some (x, ty.fvarsList ++ v.fvarsList), VLocalDecl.vlet ty' val') :: m.vlctx = _
      rw [hvlctx]
  lparams := hinv.lparams
  cfg := hinv.cfg
  kfresh := by
    intro fv hfv
    have hcase : fv = x ∨ fv ∈ Δ.fvars := by simpa using hfv
    rcases hcase with rfl | hfv'
    · exact hkres
    · exact hinv.kfresh fv hfv'
  reserved := by
    intro fv hfv
    have hcase : fv = x ∨ fv ∈ Δ.fvars := by simpa using hfv
    rcases hcase with rfl | hfv'
    · exact hres
    · exact (hinv.reserved fv hfv').mono hle
  fixvars := by
    rcases hinv.fixvars with hn | ⟨nms, ids, hm, hlen, hnd, hfr⟩
    · exact .inl hn
    · refine .inr ⟨nms, ids, hm, hlen, hnd, fun y hy => ?_⟩
      obtain ⟨hry, hΔy⟩ := hfr y hy
      refine ⟨hry.mono hle, fun hmem => ?_⟩
      have hcase : y = x ∨ y ∈ Δ.fvars := by simpa using hmem
      rcases hcase with rfl | hmem'
      · exact hnres hry
      · exact hΔy hmem'
  canon := hinv.canon


/-! ## Reading the binder just pushed

`Erasure.fvar_to_name` reads the opened binder's `userName` out of the reader's local context,
so the bridge needs the declaration `withLocalDecl`/`withLocalDef` just pushed, and needs the
outer binders' declarations to survive the inner pushes.
-/

/-- The λ declaration just pushed is what a lookup at its own identifier finds. -/
theorem LocalContext.find?_mkLocalDecl_self {lctx : LocalContext} {x : FVarId}
    (h1 : lctx.WF) (h2 : lctx.find? x = none)
    {n : Name} {ty : Expr} {bi : BinderInfo} :
    (lctx.mkLocalDecl x n ty bi).find? x =
      some (.cdecl lctx.decls.size x n ty bi .default) := by
  rw [(h1.mkLocalDecl h2).find?_eq_find?_toList, LocalContext.mkLocalDecl_toList]
  simp [List.find?, LocalDecl.fvarId]

/-- The `let` declaration just pushed is what a lookup at its own identifier finds. -/
theorem LocalContext.find?_mkLetDecl_self {lctx : LocalContext} {x : FVarId}
    (h1 : lctx.WF) (h2 : lctx.find? x = none)
    {n : Name} {ty val : Expr} {nd : Bool} :
    (lctx.mkLetDecl x n ty val nd).find? x =
      some (.ldecl lctx.decls.size x n ty val nd .default) := by
  rw [(h1.mkLetDecl h2).find?_eq_find?_toList, LocalContext.mkLetDecl_toList]
  simp [List.find?, LocalDecl.fvarId]
  rfl

/-- Looking up a different identifier is unaffected by pushing a declaration: what makes an
outer binder's name survive to the innermost context, where `Erasure.mkAlt` reads it. -/
theorem LocalContext.find?_mkLocalDecl_of_ne {lctx : LocalContext} {x y : FVarId}
    (h1 : lctx.WF) (h2 : lctx.find? x = none)
    {n : Name} {ty : Expr} {bi : BinderInfo} (hne : y ≠ x) :
    (lctx.mkLocalDecl x n ty bi).find? y = lctx.find? y := by
  rw [(h1.mkLocalDecl h2).find?_eq_find?_toList, Lean.LocalContext.mkLocalDecl_toList,
    h1.find?_eq_find?_toList]
  simp only [List.find?_cons, Lean.LocalDecl.fvarId]
  rw [show (y == x) = false from by
    simp only [Bool.eq_false_iff, ne_eq, fvarId_beq_iff_eq]; exact hne]

/-- The map `Erasure.fvar_to_name` reads is a function of `find?`, so it transports along it. -/
theorem LocalContext.fvarIdToDecl_find!_congr {l1 l2 : LocalContext} {y : FVarId}
    (h : l1.find? y = l2.find? y) : l1.fvarIdToDecl.find! y = l2.fvarIdToDecl.find! y := by
  rw [Lean.LocalContext.find?, Lean.LocalContext.find?] at h
  simp [PersistentHashMap.find!, h]

/-- …and it returns the declaration a successful lookup found. -/
theorem LocalContext.fvarIdToDecl_find!_of_find? {lctx : LocalContext}
    {x : FVarId} {d : LocalDecl} (h : lctx.find? x = some d) :
    lctx.fvarIdToDecl.find! x = d := by
  rw [LocalContext.find?] at h
  simp [PersistentHashMap.find!, h]

/-! ## The fragment condition at a subterm -/

/-- Reachability is monotone in the constants a term names, so it transports from a subterm to
its container. -/
theorem Reaches.mono {tbl : SourceTable} {e e' : Expr} {c : Name}
    (hsub : ∀ d ∈ constNames e', d ∈ constNames e) (h : Reaches tbl e' c) : Reaches tbl e c := by
  induction h with
  | root hc => exact .root (hsub _ hc)
  | body _ hb hd ih => exact .body ih hb hd

/-- **The fragment condition at a subterm.** The body clause is reachability-scoped, and a
subterm names no constant its container does not, so it transports with the shape condition
the caller inverts out of its own. -/
theorem Supported.subterm {env : VEnv} {tbl : SourceTable} {e e' : Expr}
    (h : Supported env tbl e) (hsub : ∀ d ∈ constNames e', d ∈ constNames e)
    (ht : SupportedTm env tbl e' []) : Supported env tbl e' where
  term := ht
  bodies c b hr hb := h.bodies c b (hr.mono hsub) hb

end LeanToLambdaBox
