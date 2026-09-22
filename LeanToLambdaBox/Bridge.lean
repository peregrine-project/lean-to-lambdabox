import LeanToLambdaBox.ColdStartRun
import LeanToLambdaBox.ErasesLB
import LeanToLambdaBox.SpecEnv
import Lean4Lean.Verify.LocalContext

/-!
# `BridgeInv` — the state-side contract of the `visitExpr` bridge

The invariant the bridge's induction carries: what the reader, the run state, the ambient
name generator, the inductive registry and the modelled local context agree on at every point
of a run.

* `fixvarMap` is the block-local map `Erasure.visitMutual` installs, and `BlockKeyed` names the
  index pairs that describe it faithfully — the pairs `ErasesLBFix` is read at.
* `ErasesLBMode` and `ErasesLBAltMode` are the refinement conclusion in either fixvar mode:
  outside a block the emitted term is `ErasesLB`'s image, inside one it is `ErasesLBFix`'s at a
  `BlockKeyed` pair.
* `IndRegistryModelled` is the registry's twin of `CanonicalConstants`, and `BridgeInv.indcanon`
  is where the emitted `.construct`, `.proj` and `.case` nodes read their identifiers.
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

/-- The map the block reader installs, read as a right-biased lookup in the zipped list. -/
theorem fixvarMap_getElem? (nms : List Name) (ids : List FVarId) (m : Name) :
    (fixvarMap nms ids)[m]? =
      List.findSome? (fun p => if p.1 == m then some p.2 else none) (nms.zip ids).reverse := by
  rw [fixvarMap,
    show (Std.HashMap.ofList (nms.zip ids))
        = (∅ : Std.HashMap Name FVarId).insertMany (nms.zip ids) from rfl,
    Std.HashMap.getElem?_insertMany_list]
  simp

/-- A hit in the reader's map is a hit at one index of both lists: the last pair the zipped
list holds for the key, which is the one `Std.HashMap.ofList` keeps. -/
theorem fixvarMap_get?_some {nms : List Name} {ids : List FVarId} {m : Name} {x : FVarId}
    (h : (fixvarMap nms ids)[m]? = some x) :
    ∃ j : Nat, nms[j]? = some m ∧ ids[j]? = some x := by
  rw [fixvarMap_getElem?] at h
  obtain ⟨l₁, a, l₂, hsplit, hfa, -⟩ := List.findSome?_eq_some_iff.mp h
  have hmem : a ∈ nms.zip ids := by
    rw [← List.mem_reverse, hsplit]; simp
  have ha : a.1 = m ∧ a.2 = x := by
    by_cases hb : a.1 == m
    · simp only [hb, if_pos] at hfa
      exact ⟨by simpa using hb, by simpa using hfa⟩
    · simp only [hb, Bool.false_eq_true, if_false] at hfa
      exact absurd hfa (by simp)
  obtain ⟨j, hj, hja⟩ := List.getElem_of_mem hmem
  have hjn : j < nms.length := by
    have := List.length_zip (l₁ := nms) (l₂ := ids); omega
  have hji : j < ids.length := by
    have := List.length_zip (l₁ := nms) (l₂ := ids); omega
  refine ⟨j, ?_, ?_⟩
  · rw [List.getElem?_eq_getElem hjn]
    congr 1
    rw [← ha.1, ← hja, List.getElem_zip]
  · rw [List.getElem?_eq_getElem hji]
    congr 1
    rw [← ha.2, ← hja, List.getElem_zip]

/-- A miss in the reader's map is a miss in the name list, provided the identifier list is long
enough that `List.zip` truncates none of it. -/
theorem fixvarMap_get?_none {nms : List Name} {ids : List FVarId} {m : Name}
    (hlen : nms.length ≤ ids.length) (h : (fixvarMap nms ids)[m]? = none) : m ∉ nms := by
  rw [fixvarMap_getElem?] at h
  intro hm
  obtain ⟨j, hj, hjm⟩ := List.getElem_of_mem hm
  have hjz : j < (nms.zip ids).length := by
    rw [List.length_zip]; omega
  have hmem : (m, ids[j]'(by omega)) ∈ nms.zip ids := by
    have : (nms.zip ids)[j] = (nms[j], ids[j]'(by omega)) := List.getElem_zip
    rw [hjm] at this
    exact this ▸ List.getElem_mem hjz
  have := List.findSome?_eq_none_iff.mp h (m, ids[j]'(by omega)) (by rwa [List.mem_reverse])
  simp at this

/-- Appending a name past the end of the identifier list does not change the reader's map. -/
theorem fixvarMap_append_left {nms : List Name} {ids : List FVarId} (c : Name)
    (hlen : ids.length ≤ nms.length) :
    fixvarMap (nms ++ [c]) ids = fixvarMap nms ids := by
  rw [fixvarMap, fixvarMap]
  congr 1
  induction nms generalizing ids with
  | nil =>
      have : ids = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst this; rfl
  | cons a as ih =>
      cases ids with
      | nil => rfl
      | cons x xs =>
          simp only [List.cons_append, List.zip_cons_cons]
          rw [ih (by simpa using hlen)]

/-- **A distinct-name pair reads back each of its own pairs.** With the two lists the same
length and the names distinct, the key at index `j` answers with the identifier at index `j`. -/
theorem fixvarMap_get?_of_nodup {nms : List Name} {ids : List FVarId} {j : Nat} {m : Name}
    {x : FVarId} (hlen : nms.length = ids.length) (hnd : nms.Nodup)
    (hj : nms[j]? = some m) (hx : ids[j]? = some x) :
    (fixvarMap nms ids)[m]? = some x := by
  rw [fixvarMap_getElem?]
  induction nms generalizing ids j with
  | nil => exact absurd hj (by simp)
  | cons a as ih =>
      obtain ⟨x₀, xs, rfl⟩ : ∃ x₀ xs, ids = x₀ :: xs := by
        cases ids with
        | nil => exact absurd hlen (by simp)
        | cons x₀ xs => exact ⟨x₀, xs, rfl⟩
      have hlen' : as.length = xs.length := by simpa using hlen
      rw [List.nodup_cons] at hnd
      rw [List.zip_cons_cons, List.reverse_cons, List.findSome?_append]
      cases j with
      | zero =>
          have ham : a = m := by simpa using hj
          have hx0 : x₀ = x := by simpa using hx
          have hnone : List.findSome?
              (fun p : Name × FVarId => if p.1 == m then some p.2 else none)
              (as.zip xs).reverse = none := by
            refine List.findSome?_eq_none_iff.mpr ?_
            intro p hp
            have hp1 : p.1 ∈ as := (List.of_mem_zip (List.mem_reverse.mp hp)).1
            have hne : ¬ (p.1 == m) = true := by
              simp only [beq_iff_eq]
              intro h
              exact hnd.1 (by rw [ham]; exact h ▸ hp1)
            simp only [hne, Bool.false_eq_true, if_false]
          rw [hnone]
          simp [ham, hx0]
      | succ j =>
          rw [ih hlen' hnd.2 (by simpa using hj) (by simpa using hx)]
          rfl

/-- **Every faithful pair's identifiers are the installed pair's.** Two pairs that assemble the
same reader map share their identifier lists, one direction sufficing because the invariant
names the pair the eraser installed. -/
theorem fixvarMap_ids_subset {nms nms' : List Name} {ids ids' : List FVarId}
    (hlen : nms.length = ids.length) (hnd : nms.Nodup)
    (heq : fixvarMap nms ids = fixvarMap nms' ids') : ∀ y ∈ ids, y ∈ ids' := by
  intro y hy
  obtain ⟨j, hj, hjy⟩ := List.getElem_of_mem hy
  have hjn : j < nms.length := by omega
  have hkey := fixvarMap_get?_of_nodup (j := j) (m := nms[j]) (x := y) hlen hnd
    (List.getElem?_eq_getElem hjn) (by rw [List.getElem?_eq_getElem hj, hjy])
  rw [heq] at hkey
  obtain ⟨j', -, hj'⟩ := fixvarMap_get?_some hkey
  exact List.mem_of_getElem? hj'

/-- The conditions under which a pair of index lists faithfully describes the reader's map:
`Erasure.visitMutual` installs one pair and the zip admits many others. The length condition
rules out the appended pair the block conjunct is refuted at
(`erasesLBMode_block_refuted`); `nms.Nodup` rules out the duplicated pair, whose `ids` may hold
a freshly opened binder — and it is a *conclusion of a successful run*
(`Erasure.run_rec_exit_nodup`, F-UNSAFEREC), not a standing claim about
`Lean.Compiler.LCNF.getDeclInfo?`, which is false. The fourth conjunct is a **separation**,
quantified over the *tabled*
names because that is where it is consumed — the miss branch of `Erasure.visitConst`.
Unrestricted it is false (`toKername_not_injective`); at the tabled names it is decided by
`kernameSepB`. -/
def BlockKeyed (tbl : SourceTable) (ctx : ErasureContext) (nms : List Name)
    (ids : List FVarId) : Prop :=
  ctx.fixvars = some (fixvarMap nms ids) ∧ nms.length = ids.length ∧ nms.Nodup ∧
    ∀ m : Name, (tbl.decl? m).isSome → toKername m ∈ nms.map toKername → m ∈ nms

/-! ## The refinement conclusion, in either fixvar mode -/

/-- What a sub-run's emitted term is related to, read off the reader's fixvar mode. Outside a
mutual block the term is the composite's image; inside one the block's own constants have been
rewritten to its fix variables, which is the third factor `ErasesLBFix` adds. The block's
indices are those of a `BlockKeyed` pair. -/
def ErasesLBMode (tbl : SourceTable) (ctx : ErasureContext) (env : VEnv) (Us : List Name)
    (Γspec : GlobalDeclarations) (Δ : VLCtx) (e : Expr) (t : LBTerm) : Prop :=
  (ctx.fixvars = none → ErasesLB env Us Γspec Δ e t) ∧
  (∀ nms ids, BlockKeyed tbl ctx nms ids →
    ErasesLBFix env Us Γspec (nms.map toKername) ids Δ e t)

/-- `ErasesLBMode` for one `case` alternative: what `Erasure.visitAlt` returns is related to
its source minor premise in whichever mode the reader is in. -/
def ErasesLBAltMode (tbl : SourceTable) (ctx : ErasureContext) (env : VEnv) (Us : List Name)
    (Γspec : GlobalDeclarations) (Δ : VLCtx) (nf : Nat) (m : Expr)
    (alt : List BinderName × LBTerm) : Prop :=
  (ctx.fixvars = none → ErasesLBAlt env Us Γspec Δ nf m alt) ∧
  (∀ nms ids, BlockKeyed tbl ctx nms ids →
    ErasesLBFixAlt env Us Γspec (nms.map toKername) ids Δ nf m alt)

/-- The ambient mode's reading, which is what `visitExpr_refines_erasesLB` returns. -/
theorem ErasesLBMode.ambient {tbl : SourceTable} {ctx : ErasureContext} {env : VEnv}
    {Us : List Name} {Γspec : GlobalDeclarations} {Δ : VLCtx} {e : Expr} {t : LBTerm}
    (h : ErasesLBMode tbl ctx env Us Γspec Δ e t) (hfx : ctx.fixvars = none) :
    ErasesLB env Us Γspec Δ e t := h.1 hfx

/-- The block mode's reading, which is what `visitExpr_refines_erasesLBFix` returns. -/
theorem ErasesLBMode.block {tbl : SourceTable} {ctx : ErasureContext} {env : VEnv}
    {Us : List Name} {Γspec : GlobalDeclarations} {Δ : VLCtx} {e : Expr} {t : LBTerm}
    {nms : List Name} {ids : List FVarId} (h : ErasesLBMode tbl ctx env Us Γspec Δ e t)
    (hbk : BlockKeyed tbl ctx nms ids) :
    ErasesLBFix env Us Γspec (nms.map toKername) ids Δ e t := h.2 nms ids hbk

/-! ## The inductive registry -/

/-- **The inductive registry is the model's.** Every entry names the block identifier the model
declares for that name, and — the configuration pinning constructor-argument pruning off — its
masks retain every field. True of the initial state, whose registry is empty. -/
def IndRegistryModelled (env : VEnv) (s : ErasureState) : Prop :=
  ∀ (n : Name) (r : InductiveId × InductiveArgMasks) (np : Nat) (nfs : List Nat),
    s.inductives.get? n = some r → IndArity env n np nfs →
    IndInfo env n r.1 np nfs ∧
      ∀ (j nf : Nat), nfs[j]? = some nf → r.2[j]? = some (Array.replicate nf .keep)

/-- The empty registry is modelled. -/
theorem indRegistryModelled_empty {env : VEnv} : IndRegistryModelled env {} := by
  intro n r np nfs h _
  exact absurd h (by simp)

/-- **A registration leaves the inductive registry modelled.** `Erasure.register_inductive`
mints `⟨indBlockKername indinfo.all, i⟩` for the `i`-th member of the block and, with
constructor-argument pruning pinned off, an all-`keep` mask per constructor;
`ErasureSpec.block_adequate` reads both into the model. Guarded by the invariant at the entry
state, so a hand-made registry holding a junk identifier fails the guard rather than the
conclusion. `hdecl` names the block the call is made at, which a caller holds from the
`Lean.getConstInfo` that produced `indinfo`. -/
theorem run_register_inductive_models {lenv : Environment} {env : VEnv} {Us : List Name}
    {gw : Void IO.RealWorld → NameGenerator} (P : ErasureSpec lenv env Us gw)
    {indinfo : InductiveVal} {hd : Name}
    (hdecl : lenv.find? hd = some (.inductInfo indinfo))
    {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
    {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
    {r : InductiveId × InductiveArgMasks} {s' : ErasureState} {w' : Void IO.RealWorld}
    (hcfg : ConfigPinned ctx.config) (hinv : IndRegistryModelled env s)
    (hrun : Erasure.register_inductive indinfo s ctx cctx ref w = .ok (r, s') w') :
    IndRegistryModelled env s' := by
  have hcl := (Erasure.run_register_inductive_entries
    (Ci := fun nm ci => lenv.find? nm = some ci)
    (fun nm ci s₀ s₂ w₀ w₂ h =>
      let k := P.lookup_adequate.constInfo nm cctx ref w₀ ci w₂ (Erasure.pass_getConstInfo_core h)
      ⟨k.2, k.1⟩)
    (fun le s₀ s₂ w₀ w₂ h => P.prim_monotone.getEnv s₀ ctx cctx ref w₀ le s₂ w₂ h)
    (fun msg u s₀ s₂ w₀ w₂ h => P.prim_monotone.logInfo msg s₀ ctx cctx ref w₀ u s₂ w₂ h)
    hcfg.2.2.2.1 hrun).2
  intro n rc np nfs hget hia
  rcases hcl n rc hget with hold | ⟨idx, inf, hidx, hCin, hid, hctors⟩
  · exact hinv n rc np nfs hold hia
  · obtain ⟨iv, hfind, hivname, hivnp, hkf⟩ := P.block_adequate.bwd n np nfs hia
    have hiv : iv = inf := by
      rw [hCin] at hfind
      injection hfind with h1
      injection h1 with h2
      exact h2.symm
    subst hiv
    have hI : IndInfo env n ⟨indBlockKername indinfo.all, idx⟩ indinfo.numParams nfs :=
      P.block_adequate.fwd hd n indinfo iv idx nfs hdecl hidx hfind hkf
    obtain ⟨iv2, hfind2, -, hivnp2, -⟩ :=
      P.block_adequate.bwd n indinfo.numParams nfs hI.arity
    have hiv2 : iv2 = iv := by
      rw [hfind] at hfind2
      injection hfind2 with h1
      injection h1 with h2
      exact h2.symm
    subst hiv2
    have hnp : np = indinfo.numParams := by rw [← hivnp, ← hivnp2]
    subst hnp
    refine ⟨hid ▸ hI, ?_⟩
    intro j nf hnf
    obtain ⟨hlen, hfields⟩ := hkf
    have hj : j < iv2.ctors.length := by
      rcases List.getElem?_eq_some_iff.mp hnf with ⟨hlt, -⟩
      omega
    obtain ⟨cn, hcn⟩ : ∃ cn, iv2.ctors[j]? = some cn := by
      cases hc : iv2.ctors[j]? with
      | none => exact absurd (List.getElem?_eq_none_iff.mp hc) (by omega)
      | some cn => exact ⟨cn, rfl⟩
    obtain ⟨cv, hcv, hnfj, -⟩ := hfields j cn hcn
    obtain ⟨ci', hCic, hmk⟩ := hctors j cn hcn
    have hci' : ci' = .ctorInfo cv := (Option.some.inj (hcv ▸ hCic)).symm
    have hnfeq : nf = cv.numFields := Option.some.inj (hnf ▸ hnfj)
    subst hnfeq
    exact hmk cv hci'

/-- **A registration only advances the name generator.** The three primitive calls its two
loops make are `Lean.getConstInfo`, `Lean.getEnv` and `Lean.logInfo`; `addAxiom` and the
registry writes leave the world token alone. With pruning pinned off the `MetaM` telescope arm
is not taken. -/
theorem run_register_inductive_gen {lenv : Environment} {env : VEnv} {Us : List Name}
    {gw : Void IO.RealWorld → NameGenerator} (P : ErasureSpec lenv env Us gw)
    {indinfo : InductiveVal} {s : ErasureState} {ctx : ErasureContext} {cctx : Core.Context}
    {ref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
    {r : InductiveId × InductiveArgMasks} {s' : ErasureState} {w' : Void IO.RealWorld}
    (hcfg : ConfigPinned ctx.config)
    (hrun : Erasure.register_inductive indinfo s ctx cctx ref w = .ok (r, s') w') :
    gw w ≤ gw w' :=
  (Erasure.run_register_inductive_entries (Ci := fun _ _ => True)
    (fun nm ci _s₀ _s₂ w₀ w₂ h =>
      ⟨trivial,
        (P.lookup_adequate.constInfo nm cctx ref w₀ ci w₂ (Erasure.pass_getConstInfo_core h)).1⟩)
    (fun le s₀ s₂ w₀ w₂ h => P.prim_monotone.getEnv s₀ ctx cctx ref w₀ le s₂ w₂ h)
    (fun msg u s₀ s₂ w₀ w₂ h => P.prim_monotone.logInfo msg s₀ ctx cctx ref w₀ u s₂ w₂ h)
    hcfg.2.2.2.1 hrun).1

/-! ## The invariant -/

/-- The bridge invariant, carried through the eighteen-motive induction: what the reader, the
state, the generator and the modelled context agree on. The two registry fields are
canonicity of the constant registry and modelling of the inductive one; the fixvar side is one
field because the mode and the freshness discipline are properties of the same installed map. -/
structure BridgeInv (env : VEnv) (Us : List Name) (tbl : SourceTable) (cfg₀ : ErasureConfig)
    (gen : NameGenerator) (ctx : ErasureContext) (s : ErasureState) (Δ : VLCtx) : Prop where
  /-- The reader's local context is modelled by `Δ`, witnessed by an ambient `MLCtx`. -/
  mlc : ∃ m : MLCtx, m.WF env Us ∧ m.lctx = ctx.lctx ∧ m.vlctx = Δ
  /-- The reader's level scope **is** the ambient one. The entry reader sets it to `Us` and
      the only `withReader` in the erasure that touches it is `Erasure.visitMutual`'s, which
      moves to a dependency's own `levelParams`; the invariant is not carried into that
      sub-run — `Motive6` reports registration alone — so equality holds throughout the term
      walk. It is what moves the reader's translation witness, held at `Us`, to the scope an
      oracle verdict was taken under, which is where `EraserAsks.oracle_informative` and
      `ErasureSpec.oracle_refl` conclude. -/
  lparams : ctx.lparams = Us
  /-- The reader's configuration is the one the statement is made at. `Erasure.run` builds the
      only reader from scratch and no `withReader` in the erasure touches `config`. -/
  cfg : ctx.config = cfg₀
  /-- Every `Δ` variable is reserved by the kernel's fixed generator, which is the freshness
      premise the relevance oracle's soundness takes. -/
  kfresh : ∀ fv ∈ Δ.fvars, kernelNGen.Reserves fv
  /-- Every `Δ` variable is reserved by the ambient generator, so a freshly minted identifier
      is not one of them. -/
  reserved : ∀ fv ∈ Δ.fvars, gen.Reserves fv
  /-- The reader is either outside a mutual block, or inside one whose map is described by a
      `BlockKeyed` pair against distinct identifiers, each reserved and none of them a `Δ`
      variable — `Erasure.visitMutual` mints them before any binder of the member bodies is
      opened. -/
  fixvars : ctx.fixvars = none ∨
    ∃ nms ids, BlockKeyed tbl ctx nms ids ∧ ids.Nodup ∧
      ∀ x ∈ ids, gen.Reserves x ∧ x ∉ Δ.fvars
  /-- Every registered kername is the canonical one. Every writer on the registration path
      inserts under `toKername`, so this is maintained, never assumed. -/
  canon : CanonicalConstants s
  /-- Every registry entry names the block identifier the model declares for that name, and
      its masks retain every field. -/
  indcanon : IndRegistryModelled env s

/-- The `TrLCtx` correspondence, re-derived from the `mlc` witness. -/
theorem BridgeInv.trlctx {env : VEnv} {Us : List Name} {tbl : SourceTable}
    {cfg : ErasureConfig} {gen : NameGenerator} {ctx : ErasureContext} {s : ErasureState}
    {Δ : VLCtx} (h : BridgeInv env Us tbl cfg gen ctx s Δ) : TrLCtx env Us ctx.lctx Δ := by
  obtain ⟨m, mwf, hlctx, hvlctx⟩ := h.mlc
  rw [← hlctx, ← hvlctx]; exact mwf.tr

/-- The modelled context is well formed — what the erasure relation's own lemmas take. -/
theorem BridgeInv.vlctx_wf {env : VEnv} {Us : List Name} {tbl : SourceTable}
    {cfg : ErasureConfig} {gen : NameGenerator} {ctx : ErasureContext} {s : ErasureState}
    {Δ : VLCtx} (h : BridgeInv env Us tbl cfg gen ctx s Δ) : VLCtx.WF env Us.length Δ :=
  h.trlctx.wf

/-- The modelled context has no de Bruijn entries: every entry the run conses is fvar-tagged
and the entry point is empty. -/
theorem BridgeInv.noBV {env : VEnv} {Us : List Name} {tbl : SourceTable} {cfg : ErasureConfig}
    {gen : NameGenerator} {ctx : ErasureContext} {s : ErasureState} {Δ : VLCtx}
    (h : BridgeInv env Us tbl cfg gen ctx s Δ) : Δ.NoBV := by
  obtain ⟨m, -, -, hvlctx⟩ := h.mlc
  rw [← hvlctx]; exact m.noBV

/-- **The block's identifiers, at every faithful pair.** A `BlockKeyed` pair's identifiers are
the installed pair's, so each is reserved by the ambient generator and none is a `Δ`
variable — the freshness the binder steps need of a fix variable. -/
theorem BridgeInv.fixvars_ids_subset {env : VEnv} {Us : List Name} {tbl : SourceTable}
    {cfg : ErasureConfig} {gen : NameGenerator} {ctx : ErasureContext} {s : ErasureState}
    {Δ : VLCtx} {nms : List Name} {ids : List FVarId}
    (h : BridgeInv env Us tbl cfg gen ctx s Δ) (hbk : BlockKeyed tbl ctx nms ids) :
    ∀ y ∈ ids, gen.Reserves y ∧ y ∉ Δ.fvars := by
  rcases h.fixvars with hn | ⟨nms', ids', hbk', -, hfr⟩
  · exact absurd (hn.symm.trans hbk.1) (by simp)
  · have heq : fixvarMap nms ids = fixvarMap nms' ids' := by
      have := hbk.1.symm.trans hbk'.1
      exact Option.some.inj this
    exact fun y hy => hfr y (fixvarMap_ids_subset hbk.2.1 hbk.2.2.1 heq y hy)

/-- The invariant is monotone in the generator: reservations survive advancement. -/
theorem BridgeInv.mono {env : VEnv} {Us : List Name} {tbl : SourceTable} {cfg : ErasureConfig}
    {gen gen' : NameGenerator} {ctx : ErasureContext} {s : ErasureState} {Δ : VLCtx}
    (h : BridgeInv env Us tbl cfg gen ctx s Δ) (hle : gen ≤ gen') :
    BridgeInv env Us tbl cfg gen' ctx s Δ where
  mlc := h.mlc
  lparams := h.lparams
  cfg := h.cfg
  kfresh := h.kfresh
  reserved fv hfv := (h.reserved fv hfv).mono hle
  fixvars := by
    rcases h.fixvars with hn | ⟨nms, ids, hbk, hnd, hfr⟩
    · exact .inl hn
    · exact .inr ⟨nms, ids, hbk, hnd, fun x hx => ⟨((hfr x hx).1).mono hle, (hfr x hx).2⟩⟩
  canon := h.canon
  indcanon := h.indcanon

/-- The invariant survives state growth: canonicity is preserved by `Erasure.RunConcl`, and the
registry model is what the sub-run reports, since `RunConcl` bounds the registry's growth
alone. -/
theorem BridgeInv.mono_state {env : VEnv} {Us : List Name} {tbl : SourceTable}
    {cfg : ErasureConfig} {gen : NameGenerator} {ctx : ErasureContext} {s s' : ErasureState}
    {Δ : VLCtx} (h : BridgeInv env Us tbl cfg gen ctx s Δ) (hrc : RunConcl s s')
    (hind : IndRegistryModelled env s') : BridgeInv env Us tbl cfg gen ctx s' Δ where
  mlc := h.mlc
  lparams := h.lparams
  cfg := h.cfg
  kfresh := h.kfresh
  reserved := h.reserved
  fixvars := h.fixvars
  canon := hrc.canon h.canon
  indcanon := hind




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
theorem BridgeInv.mkLocalDecl {env : VEnv} {Us : List Name} {tbl : SourceTable}
    {cfg₀ : ErasureConfig}
    {gen gen' : NameGenerator} {ctx : ErasureContext} {s : ErasureState} {Δ : VLCtx}
    {x : FVarId} {n : Name} {ty : Expr} {ty' : VExpr} {bi : BinderInfo}
    (hinv : BridgeInv env Us tbl cfg₀ gen ctx s Δ)
    (hty : TrExprS env Us Δ ty ty') (hty' : env.IsType Us.length Δ.toCtx ty')
    (hx : x ∉ Δ.fvars) (hnres : ¬ gen.Reserves x)
    (hle : gen ≤ gen') (hres : gen'.Reserves x) (hkres : kernelNGen.Reserves x) :
    BridgeInv env Us tbl cfg₀ gen' { ctx with lctx := ctx.lctx.mkLocalDecl x n ty bi } s
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
    rcases hinv.fixvars with hn | ⟨nms, ids, hbk, hnd, hfr⟩
    · exact .inl hn
    · refine .inr ⟨nms, ids, hbk, hnd, fun y hy => ?_⟩
      obtain ⟨hry, hΔy⟩ := hfr y hy
      refine ⟨hry.mono hle, fun hmem => ?_⟩
      have hcase : y = x ∨ y ∈ Δ.fvars := by simpa using hmem
      rcases hcase with rfl | hmem'
      · exact hnres hry
      · exact hΔy hmem'
  canon := hinv.canon
  indcanon := hinv.indcanon

/-- **The invariant across `Erasure.withLocalDef`.** The shipping wrapper builds the let
declaration at the default `nonDep`, which is the one `MLCtx.vlet` records. -/
theorem BridgeInv.mkLetDecl {env : VEnv} {Us : List Name} {tbl : SourceTable}
    {cfg₀ : ErasureConfig}
    {gen gen' : NameGenerator} {ctx : ErasureContext} {s : ErasureState} {Δ : VLCtx}
    {x : FVarId} {n : Name} {ty v : Expr} {ty' val' : VExpr}
    (hinv : BridgeInv env Us tbl cfg₀ gen ctx s Δ)
    (hty : TrExprS env Us Δ ty ty') (hval : TrExprS env Us Δ v val')
    (hvt : env.HasType Us.length Δ.toCtx val' ty')
    (hx : x ∉ Δ.fvars) (hnres : ¬ gen.Reserves x)
    (hle : gen ≤ gen') (hres : gen'.Reserves x) (hkres : kernelNGen.Reserves x) :
    BridgeInv env Us tbl cfg₀ gen' { ctx with lctx := ctx.lctx.mkLetDecl x n ty v } s
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
    rcases hinv.fixvars with hn | ⟨nms, ids, hbk, hnd, hfr⟩
    · exact .inl hn
    · refine .inr ⟨nms, ids, hbk, hnd, fun y hy => ?_⟩
      obtain ⟨hry, hΔy⟩ := hfr y hy
      refine ⟨hry.mono hle, fun hmem => ?_⟩
      have hcase : y = x ∨ y ∈ Δ.fvars := by simpa using hmem
      rcases hcase with rfl | hmem'
      · exact hnres hry
      · exact hΔy hmem'
  canon := hinv.canon
  indcanon := hinv.indcanon


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
  kernames := h.kernames

end LeanToLambdaBox
