import LeanToLambdaBox.Erases
import Lean4Lean.Verify.Typing.Lemmas

/-!
# Totality and environment monotonicity of `Erases`

A source term lean4lean can read has a λ□ image, and an image survives environment extension.

* `Erases.mono` transports a derivation along `VEnv.LE`.
* `Erases.sort_erasable` and `Erases.forallE_erasable` supply the `box` rule's irrelevance
  witness for the two heads that have no structural rule: a sort and a Π-type are always
  type-formers, so their images are `LBTerm.box` and nothing else.
* `Erases.exists_of_trExprS_of_projInfo` is totality, under the side premise `ProjInfo`:
  block data for every projection head of the source. `TrExprS.proj`'s own premise `TrProj`
  does not yield the `IndInfo` that `Erases.proj` demands, so the caller supplies it.
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
`VEnv.LE.constants` for `const`, `IndInfo.mono` for `proj`, `VEnv.ContainsLits.mono` for
`lit`. -/
theorem Erases.mono (hle : env ≤ env') {e : Expr} {t : LBTerm} (h : Erases env Us Δ e t) :
    Erases env' Us Δ e t := by
  induction h with
  | box htr her => exact .box (htr.mono hle) (her.mono hle)
  | bvar hf => exact .bvar hf
  | fvar hf => exact .fvar hf
  | const hc => exact .const (hle.constants hc)
  | app _ _ ihf iha => exact .app ihf iha
  | lam hty _ ihb => exact .lam (hty.mono hle) ihb
  | letE hty hval _ _ ihv ihb => exact .letE (hty.mono hle) (hval.mono hle) ihv ihb
  | proj hs hi _ ihd => exact .proj (hs.mono hle) hi ihd
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

/-! ## Totality -/

/--
Block data for every projection head of a source term.

`Erases.proj` demands an `IndInfo`, and `TrExprS.proj`'s premise `TrProj` does not yield one,
so totality takes it as a side premise. Binder types are not traversed: they reach erasure
only as `TrExprS` witnesses. A literal needs no premise — `Literal.toConstructor` is
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
  | proj {S i e} (hs : ∃ iid np nf, IndInfo env S iid np [nf] ∧ i < nf) (h : ProjInfo env e) :
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
Totality: a source term lean4lean can read, whose projection heads carry block data, has a
λ□ image. The image is built by the structural rule of each head, except at a sort and at a
Π-type, where the box rule fires.
-/
theorem Erases.exists_of_trExprS_of_projInfo (henv : env.WF) {e : Expr} {ve : VExpr}
    (hΔ : VLCtx.WF env Us.length Δ) (hpi : ProjInfo env e) (h : TrExprS env Us Δ e ve) :
    ∃ t, Erases env Us Δ e t := by
  revert hΔ hpi
  induction h with
  | bvar hf => exact fun _ _ => ⟨_, .bvar hf⟩
  | fvar hf => exact fun _ _ => ⟨_, .fvar hf⟩
  | sort hu => exact fun _ _ => ⟨_, .box (.sort hu) (Erases.sort_erasable henv (.sort hu))⟩
  | const hc hus hlen => exact fun _ _ => ⟨_, .const hc⟩
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
    let .proj ⟨iid, np, nf, hii, hlt⟩ hpe := hpi
    let ⟨_, he⟩ := ih hΔ hpe
    exact ⟨_, .proj hii hlt he⟩

end LeanToLambdaBox
