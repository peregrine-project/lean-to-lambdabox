import LeanToLambdaBox.Erases
import Lean4Lean.Verify.Typing.Lemmas

/-!
# Totality and environment monotonicity of `Erases`

A source term lean4lean can read has a λ□ image, and an image survives environment extension.

* `Erases.mono` transports a derivation along `VEnv.LE`.
* `Erases.sort_erasable` and `Erases.forallE_erasable` supply the `box` rule's irrelevance
  witness for the two heads that have no structural rule: a sort and a Π-type are always
  type-formers, so their images are `LBTerm.box` and nothing else.
* `Erases.exists_of_trExprS_of_projInfo` is totality, under two side premises: `ProjInfo`,
  block data for every projection head of the source — `TrExprS.proj`'s own premise `TrProj`
  does not yield the `IndInfo` that `Erases.proj` demands — and `hclass`, which says which
  of the three readings a declared constant has.
* `IndInfo.constant_isArity` and `Erases.indInfo_erasable` are what the type-name reading
  costs: an inductive type former's declared type is an arity, so the term is erasable and
  `box` is its image.
-/

namespace LeanToLambdaBox

open Lean Lean4Lean

variable {env env' : VEnv} {Us : List Name} {Δ : VLCtx}

/-! ## Monotonicity -/

/-- Irrelevance survives environment extension: the type witness and both disjuncts are
monotone. -/
theorem Erasable.mono (hle : env ≤ env') {U : Nat} {Γ : List VExpr} {e : VExpr}
    (h : Erasable env U Γ e) : Erasable env' U Γ e := by
  obtain ⟨A, hA, hcase⟩ := h
  refine ⟨A, hA.mono hle, ?_⟩
  cases hcase with
  | inl hp => exact .inl (hp.mono hle)
  | inr ha => let ⟨A', hd, har⟩ := ha; exact .inr ⟨A', hd.mono hle, har⟩

/-- An erasure derivation survives environment extension. Each premise is monotone in its own
right: `TrExprS.mono` for the translations, `Erasable.mono` for the box witness,
`CtorOf.mono` and `IndInfo.mono` for `ctor`, `VEnv.LE.constants` and `ConstOrigin.mono` for
`const`, `IndInfo.mono` and `InformativeInd.mono` for `proj`, `VEnv.ContainsLits.mono` for
`lit`. -/
theorem Erases.mono (hle : env ≤ env') {e : Expr} {t : LBTerm} (h : Erases env Us Δ e t) :
    Erases env' Us Δ e t := by
  induction h with
  | box htr her => exact .box (htr.mono hle) (her.mono hle)
  | bvar hf => exact .bvar hf
  | fvar hf => exact .fvar hf
  | ctor hc hi => exact .ctor (hc.mono hle) (hi.mono hle)
  | const hc ho => exact .const (hle.constants hc) (ho.mono hle)
  | app _ _ ihf iha => exact .app ihf iha
  | lam hty _ ihb => exact .lam (hty.mono hle) ihb
  | letE hty hval _ _ ihv ihb => exact .letE (hty.mono hle) (hval.mono hle) ihv ihb
  | proj hs hinf hi _ ihd => exact .proj (hs.mono hle) (hinf.mono hle) hi ihd
  | lit hcl _ ih => exact .lit (hcl.mono hle) ih
  | mdata _ ih => exact .mdata ih

/-! ## The two heads with no structural rule -/

/-- A sort is a type-former: its type is the next sort up, which is an arity. The
environment premise is unused — the level is well-formed by `VLevel.WF.of_ofLevel`. -/
theorem Erases.sort_erasable (_henv : env.WF) {u : Level} {ve : VExpr}
    (h : TrExprS env Us Δ (.sort u) ve) : Erasable env Us.length Δ.toCtx ve := by
  cases h with
  | sort hu =>
    have hwf := VLevel.WF.of_ofLevel hu
    exact ⟨_, .sort hwf, .inr ⟨_, ⟨_, VEnv.HasType.sort (l := .succ _) hwf⟩, .sort _⟩⟩

/-- A Π-type is a type-former: its type is the sort `imax` of its parts' sorts, which is an
arity. The context premise supplies the levels' well-formedness, which the typing of the
parts alone does not. -/
theorem Erases.forallE_erasable (henv : env.WF) {n : Name} {A B : Expr} {bi : BinderInfo}
    {ve : VExpr} (hΔ : VLCtx.WF env Us.length Δ)
    (h : TrExprS env Us Δ (.forallE n A B bi) ve) :
    Erasable env Us.length Δ.toCtx ve := by
  cases h with
  | forallE hA hB _ _ =>
    obtain ⟨u, hu⟩ := hA
    obtain ⟨v, hv⟩ := hB
    have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
    have hΓ' : OnCtx (_ :: Δ.toCtx) (env.IsType Us.length) := ⟨hΓ, _, hu⟩
    have huwf : u.WF Us.length := hu.sort_r henv.ordered hΓ
    have hvwf : v.WF Us.length := hv.sort_r henv.ordered hΓ'
    exact ⟨_, hu.forallE hv,
      .inr ⟨_, ⟨_, VEnv.HasType.sort (l := .imax u v) ⟨huwf, hvwf⟩⟩, .sort _⟩⟩

/-! ## The type-name reading

An inductive type name is a type former, so `box` is its only image. Its declared type is
the block's own, and `VInductDecl.WF` says that type is a Π-telescope ending in a sort.
-/

/-- A block declared in a `VEnv.WF'` list was added by a well-formed declaration step, and
the environment it produced sits below the list's own. -/
theorem wf'_induct_origin {ds : List VDecl} {env : VEnv} (H : VEnv.WF' ds env)
    {decl : VInductDecl} (hd : VDecl.induct decl ∈ ds) :
    ∃ env₀ env₁, decl.WF env₀ ∧ env₀.addInduct decl = some env₁ ∧ env₁ ≤ env := by
  induction H with
  | empty => cases hd
  | decl hwf _ ih =>
    rcases List.mem_cons.1 hd with rfl | hd'
    · cases hwf with
      | induct hdecl hadd => exact ⟨_, _, hdecl, hadd, VEnv.LE.rfl⟩
    · obtain ⟨e₀, e₁, h1, h2, h3⟩ := ih hd'
      exact ⟨e₀, e₁, h1, h2, h3.trans hwf.le⟩

/-- A telescope whose Π-body is a sort is an arity. -/
theorem IsArity.of_piBody : ∀ {ty : VExpr} {u : VLevel}, ty.piBody = .sort u → IsArity ty
  | .sort _, _, h => by cases h; exact .sort _
  | .forallE _ B, _, h => .forallE _ _ (IsArity.of_piBody (ty := B) h)

/-- The declared type of an inductive type former is an arity: the block was added by
`addInduct`, which binds the former's name to the type `VInductDecl.WF.universes` requires
to end in a sort. -/
theorem IndInfo.constant_isArity {env : VEnv} {I : Name} {iid : InductiveId} {np : Nat}
    {nfs : List Nat} (h : IndInfo env I iid np nfs) :
    ∃ ci, env.constants I = some ci ∧ IsArity ci.type := by
  obtain ⟨ds, env₀, decl, t, hds, hd, hle, ht, hname, hkn, hnp, hnfs⟩ := h.block
  obtain ⟨e₀, e₁, hdecl, hadd, hle₁⟩ := wf'_induct_origin hds hd
  obtain ⟨envT, envC, envR, hT, hC, hR, hP⟩ := VEnv.addInduct_stages hadd
  have hmem : t ∈ decl.types := List.mem_of_getElem? ht
  obtain ⟨ℓ, hpi, -, -⟩ := hdecl.universes envT hT
  have hfold : decl.consts.foldlM (fun (e : VEnv) b => e.addConst b.1 b.2) e₀ = some envR := by
    rw [← VInductDecl.addTypesCtorsRecs_eq]
    unfold VInductDecl.addTypesCtorsRecs VInductDecl.addTypesCtors
    simp [hT, hC, hR]
  have hcmem : (t.name, t.toVConstVal.toVConstant) ∈ decl.consts :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hmem))
  have hfind := VEnv.addConst_foldlM_find (nm := Prod.fst) (ci := Prod.snd) hfold _ hcmem
  exact ⟨_, hname ▸ hle.constants (hle₁.constants ((VEnv.addRules_le hP).constants hfind)),
    IsArity.of_piBody (hpi t hmem).1⟩

/-- An inductive type name is erasable: its type is an arity, so the `box` rule is the only
rule that applies to it and it does apply. -/
theorem Erases.indInfo_erasable {env : VEnv} {Us : List Name} {Δ : VLCtx} (henv : env.WF)
    (hΔ : VLCtx.WF env Us.length Δ) {c : Name} {us : List Level} {iid : InductiveId}
    {np : Nat} {nfs : List Nat} {ve : VExpr} (hi : IndInfo env c iid np nfs)
    (h : TrExprS env Us Δ (.const c us) ve) : Erasable env Us.length Δ.toCtx ve := by
  obtain ⟨ci, hc, harity⟩ := hi.constant_isArity
  cases h with
  | const h1 h2 h3 =>
    cases hc.symm.trans h1
    have hty := VEnv.HasType.const (Γ := Δ.toCtx) h1 (VLevel.WF.of_mapM_ofLevel h2)
      ((List.mapM_eq_some.1 h2).length_eq.symm.trans h3)
    obtain ⟨u, hu⟩ := hty.isType henv.ordered hΔ.toCtx
    exact ⟨_, hty, .inr ⟨_, VEnv.IsDefEqU.refl ⟨_, hu⟩, harity.instL⟩⟩

/-! ## Totality -/

/--
Block data for every projection head of a source term.

`Erases.proj` demands an `IndInfo` and the relevance of the projection's type former, and
`TrExprS.proj`'s premise `TrProj` yields neither, so totality takes both as side premises.
Binder types are not traversed: they reach erasure only as `TrExprS` witnesses. A literal needs no premise — `Literal.toConstructor` is
projection-free (`ProjInfo.toConstructor`).
-/
inductive ProjInfo (env : VEnv) : Expr → Prop
  | bvar {i} : ProjInfo env (.bvar i)
  | fvar {x} : ProjInfo env (.fvar x)
  | sort {u} : ProjInfo env (.sort u)
  | const {c us} : ProjInfo env (.const c us)
  | lit {l} : ProjInfo env (.lit l)
  | forallE {n ty b bi} : ProjInfo env (.forallE n ty b bi)
  | app {f a} : ProjInfo env f → ProjInfo env a → ProjInfo env (.app f a)
  | lam {n ty b bi} : ProjInfo env b → ProjInfo env (.lam n ty b bi)
  | letE {n ty v b nd} : ProjInfo env v → ProjInfo env b → ProjInfo env (.letE n ty v b nd)
  | mdata {d e} : ProjInfo env e → ProjInfo env (.mdata d e)
  | proj {S i e} (hs : ∃ iid np nf, IndInfo env S iid np [nf] ∧ i < nf)
      (hinf : InformativeInd env S) (h : ProjInfo env e) :
      ProjInfo env (.proj S i e)

/-- A literal's kernel unfolding is built from constants, applications and literals, so it
carries no projection. -/
theorem ProjInfo.toConstructor {env : VEnv} (l : Literal) : ProjInfo env l.toConstructor := by
  cases l with
  | natVal n =>
    cases n with
    | zero => exact .const
    | succ n => exact .app .const .lit
  | strVal s =>
    refine .app .const ?_
    induction s.toList with
    | nil => exact .app .const .const
    | cons c cs ih => exact .app (.app (.app .const .const) (.app .const .lit)) ih

/--
Totality: a source term lean4lean can read, whose projection heads carry block data and
whose constants are classified, has a λ□ image. Every head takes its structural rule, except
a sort, a Π-type and an inductive type name, where the box rule fires. `hclass` is the
classification direction of the kernel-theory fact that a declared constant is a
constructor, a type name or a plain constant: a hypothesis of this lemma alone, never of
`Erases`.
-/
theorem Erases.exists_of_trExprS_of_projInfo (henv : env.WF)
    (hclass : ∀ c ci, env.constants c = some ci →
      (∃ I k, CtorOf env c I k) ∨ (∃ iid np nfs, IndInfo env c iid np nfs) ∨ ConstOrigin env c)
    {e : Expr} {ve : VExpr}
    (hΔ : VLCtx.WF env Us.length Δ) (hpi : ProjInfo env e) (h : TrExprS env Us Δ e ve) :
    ∃ t, Erases env Us Δ e t := by
  revert hΔ hpi
  induction h with
  | bvar hf => exact fun _ _ => ⟨_, .bvar hf⟩
  | fvar hf => exact fun _ _ => ⟨_, .fvar hf⟩
  | sort hu => exact fun _ _ => ⟨_, .box (.sort hu) (Erases.sort_erasable henv (.sort hu))⟩
  | const hc hus hlen =>
    refine fun hΔ _ => ?_
    rcases hclass _ _ hc with ⟨I, k, hct⟩ | ⟨iid, np, nfs, hii⟩ | ho
    · obtain ⟨iid, np, nfs, hi⟩ := hct.indInfo
      exact ⟨_, .ctor hct hi⟩
    · exact ⟨_, .box (.const hc hus hlen)
        (Erases.indInfo_erasable henv hΔ hii (.const hc hus hlen))⟩
    · exact ⟨_, .const hc ho⟩
  | app hf ha htf hta ihf iha =>
    intro hΔ hpi
    let .app hpf hpa := hpi
    let ⟨_, hef⟩ := ihf hΔ hpf
    let ⟨_, hea⟩ := iha hΔ hpa
    exact ⟨_, .app hef hea⟩
  | lam hty htr hbody ihty ihb =>
    intro hΔ hpi
    let .lam hpb := hpi
    let ⟨_, heb⟩ := ihb ⟨hΔ, nofun, hty⟩ hpb
    exact ⟨_, .lam htr heb⟩
  | @forallE _ _ _ _ _ n bi hty hbody htr hbtr ihty ihb =>
    intro hΔ _
    exact ⟨_, .box (.forallE hty hbody htr hbtr)
      (Erases.forallE_erasable (n := n) (bi := bi) henv hΔ (.forallE hty hbody htr hbtr))⟩
  | letE hval htr hvtr hbody ihty ihv ihb =>
    intro hΔ hpi
    let .letE hpv hpb := hpi
    let ⟨_, hev⟩ := ihv hΔ hpv
    let ⟨_, heb⟩ := ihb ⟨hΔ, nofun, hval⟩ hpb
    exact ⟨_, .letE htr hvtr hev heb⟩
  | lit hcl htr ih =>
    intro hΔ _
    let ⟨_, he⟩ := ih hΔ (ProjInfo.toConstructor _)
    exact ⟨_, .lit hcl he⟩
  | mdata htr ih =>
    intro hΔ hpi
    let .mdata hpe := hpi
    exact (ih hΔ hpe).imp fun _ he => .mdata he
  | proj htr hproj ih =>
    intro hΔ hpi
    let .proj ⟨iid, np, nf, hii, hlt⟩ hinf hpe := hpi
    let ⟨_, he⟩ := ih hΔ hpe
    exact ⟨_, .proj hii hinf hlt he⟩

end LeanToLambdaBox
