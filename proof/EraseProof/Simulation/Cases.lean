import EraseProof.Source.Defeq
import EraseProof.Erasability.Eval
import EraseProof.Erasability.Inv
import EraseProof.Relation.Deps
import EraseProof.Relation.Subst
import EraseProof.Relation.Levels
import EraseProof.Relation.Atoms

/-!
# Cases of the relation-level simulation

`erases_correct` (`MR E/ErasureCorrectness.v:51`) is proved by induction on the source evaluation,
one case per rule of `SrcEval`. This module proves the cases of the rules `beta`, `zeta`, `delta`,
`constAtom`, `appCong`, `mdata` and `atom`, each as a theorem that takes the induction hypotheses
of the rule's premises as hypotheses. Every case first handles an erasure to `□` uniformly
(`erases_correct_box`): the value is erasable too (`ErasableS.eval`), so it erases to `□`, a λ□
value.
-/

open Lean Lean4Lean Erasure

namespace EraseProof

section
variable {venv : VEnv} {P : List ConstantInfo} {σ : EvalEnv} {lenv : GlobalDeclarations}

/-- The fixpoints stored in a closed λ□ environment are closed. Reference: `closed_env`
(`MR E/EGlobalEnv.v:181`), as the cases of `erases_correct` use it for `tFix` bodies. -/
theorem RecIn.rcClosed (hlc : LenvClosed lenv) : RcClosed (RecIn lenv) := by
  rintro c t ⟨defs, i, rfl, hl⟩
  exact (hlc _ _ _ hl rfl).1

/-- An unfoldable constant is not remapped. Reference: the premise `cst_body decl = Some body` of
`eval_delta` (`MR P/PCUICWcbvEval.v:247`), DV-12. -/
theorem EvalEnv.unfold?_axiomatized (hu : σ.unfold? c = some (ci, b)) :
    σ.axiomatized ci = false := by
  unfold EvalEnv.unfold? at hu
  split at hu
  · split at hu
    · cases hu
    · next h => cases hu; exact Bool.eq_false_iff.2 h
  · split at hu
    · cases hu
    · next h => cases hu; exact Bool.eq_false_iff.2 h
  · cases hu

/-- The image of an atom spine is erasable: its head is an atom constant (`ErasableS.atom`), and
an application of an erasable function is erasable (`IsErasable.app`). Reference: `Is_type_app`
(`MR E/EArities.v:480`) on `tInd`-headed spines. -/
theorem ErasableS.atomSpine (henv : ProgEnv P venv) (hsub : SubEnv σ.decls P)
    (hsp : AtomSpine σ e) (he : TrS venv Us [] e e') : IsErasable venv Us.length [] e' := by
  induction hsp generalizing e' with
  | const ha =>
    obtain ⟨e'', he'', hE⟩ := ErasableS.atom henv hsub ha he
    cases he.det he''
    exact hE
  | app _ ih =>
    cases he with
    | app hfT haT hf _ => exact IsErasable.app henv trivial (hfT.app haT) (ih hf)

/-- The uniform case of `erases_correct`, an erasure to `□`: the value of an erasable term is
erasable, so it erases to `□`, which λ□ evaluates to itself. Reference: the `erases_box` cases of
`erases_correct` (`MR E/ErasureCorrectness.v:58-1232`), through `Is_type_eval`
(`MR E/EArities.v:570`). -/
theorem erases_correct_box (henv : ProgEnv P venv) (hsub : SubEnv σ.decls P)
    (he : TrS venv Us [] e e') (hb : ErasableS venv Us [] e) (hev : SrcEval σ e v) :
    ∃ v', Erases venv Us σ.isAtom (RecIn lenv) [] v v' ∧ LBEval defaultFlags lenv .box v' :=
  ⟨.box, .box (ErasableS.eval henv hsub he hev hb), .atom rfl⟩

/-- The `beta` case of `erases_correct`: the function's erasure evaluates to `□`, and so does the
application, or to a λ, whose body with the argument's value substituted (`Erases.inst`) erases the
source's substituted body. Reference: the `eval_beta` case of `erases_correct`
(`MR E/ErasureCorrectness.v:62`); Let. Thm 13 (β). -/
theorem erases_correct_beta (henv : ProgEnv P venv) (hsub : SubEnv σ.decls P)
    (hlc : LenvClosed lenv)
    (ihf : ∀ {f₀ tf}, TrS venv Us [] f f₀ → Erases venv Us σ.isAtom (RecIn lenv) [] f tf →
      ErasesDeps venv σ lenv tf →
      ∃ v', Erases venv Us σ.isAtom (RecIn lenv) [] (.lam n A b bi) v' ∧
        LBEval defaultFlags lenv tf v')
    (iha : ∀ {a₀ ta}, TrS venv Us [] a a₀ → Erases venv Us σ.isAtom (RecIn lenv) [] a ta →
      ErasesDeps venv σ lenv ta →
      ∃ v', Erases venv Us σ.isAtom (RecIn lenv) [] a' v' ∧ LBEval defaultFlags lenv ta v')
    (ihb : ∀ {b₀ tb}, TrS venv Us [] (b.instantiate1' a') b₀ →
      Erases venv Us σ.isAtom (RecIn lenv) [] (b.instantiate1' a') tb →
      ErasesDeps venv σ lenv tb →
      ∃ v', Erases venv Us σ.isAtom (RecIn lenv) [] v v' ∧ LBEval defaultFlags lenv tb v')
    (hf : SrcEval σ f (.lam n A b bi)) (ha : SrcEval σ a a')
    (hb : SrcEval σ (b.instantiate1' a') v)
    (he : TrS venv Us [] (.app f a) e')
    (her : Erases venv Us σ.isAtom (RecIn lenv) [] (.app f a) t)
    (hdeps : ErasesDeps venv σ lenv t) :
    ∃ v', Erases venv Us σ.isAtom (RecIn lenv) [] v v' ∧ LBEval defaultFlags lenv t v' := by
  have hwf := henv.wf
  have hord := henv.ordered
  rcases Erases.app_inv her with ⟨rfl, hbx⟩ | ⟨tf, ta, rfl, herf, hera⟩
  · exact erases_correct_box henv hsub he hbx (.beta hf ha hb)
  cases he with
  | app hfT haT hft hat =>
  cases hdeps with
  | app hdf hda =>
  obtain ⟨vf, hvf, hevf⟩ := ihf hft herf hdf
  obtain ⟨va, hva, heva⟩ := iha hat hera hda
  obtain ⟨_, hlam, hdlam⟩ := SrcEval.defeq henv hsub hft hfT hf
  obtain ⟨a₁, ha₁, hda₁⟩ := SrcEval.defeq henv hsub hat haT ha
  cases hlam with
  | lam hA₁ hA hbT =>
  have ⟨_, ⟨_, hb₁⟩⟩ := VEnv.HasType.lam_inv hord trivial hdlam.hasType.2
  have ⟨_, hA₁'⟩ := hA₁
  have ⟨_, hpi⟩ := hdlam.hasType.2.uniq hwf trivial (.lamDF hA₁' hb₁)
  have ⟨⟨_, hdom⟩, _⟩ := VEnv.IsDefEqU.forallE_inv hwf trivial ⟨_, hpi⟩
  have hta₁ := VEnv.IsDefEq.defeqDF hdom hda₁.hasType.2
  have hbi := TrS.inst (Δ := []) hord hta₁ hbT ha₁
  cases hvf with
  | lam hA' hbody =>
    cases TrS.det hA hA'
    have hdb := ErasesDeps.eval hdf hevf
    cases hdb with
    | lambda hdb =>
    obtain ⟨res, hres, hevres⟩ := ihb hbi
      (Erases.inst henv (RecIn.rcClosed hlc) hbody hva ha₁ hta₁)
      (ErasesDeps.csubst (ErasesDeps.eval hda heva) hdb)
    exact ⟨res, hres, .beta hevf heva hevres⟩
  | box hbx =>
    obtain ⟨_, hlam', hE⟩ := hbx
    cases TrS.det (.lam hA₁ hA hbT) hlam'
    have hEb := IsErasable.lam_inv henv trivial hE
    exact ⟨.box, .box (ErasableS.eval henv hsub hbi hb ⟨_, hbi, IsErasable.inst hord hta₁ hEb⟩),
      .box hevf heva⟩

/-- The `zeta` case of `erases_correct`: the `let` value's erasure evaluates to an erasure of its
value, which substituted into the erased body (`Erases.inst_let`) erases the source's substituted
body. Reference: the `eval_zeta` case of `erases_correct` (`MR E/ErasureCorrectness.v:110`); Let.
Thm 13 (ζ). -/
theorem erases_correct_zeta (henv : ProgEnv P venv) (hsub : SubEnv σ.decls P)
    (hlc : LenvClosed lenv)
    (ihv : ∀ {v₀ tv}, TrS venv Us [] val v₀ → Erases venv Us σ.isAtom (RecIn lenv) [] val tv →
      ErasesDeps venv σ lenv tv →
      ∃ v', Erases venv Us σ.isAtom (RecIn lenv) [] val' v' ∧ LBEval defaultFlags lenv tv v')
    (ihb : ∀ {b₀ tb}, TrS venv Us [] (b.instantiate1' val') b₀ →
      Erases venv Us σ.isAtom (RecIn lenv) [] (b.instantiate1' val') tb →
      ErasesDeps venv σ lenv tb →
      ∃ v', Erases venv Us σ.isAtom (RecIn lenv) [] v v' ∧ LBEval defaultFlags lenv tb v')
    (hv : SrcEval σ val val') (hb : SrcEval σ (b.instantiate1' val') v)
    (he : TrS venv Us [] (.letE n T val b nd) e')
    (her : Erases venv Us σ.isAtom (RecIn lenv) [] (.letE n T val b nd) t)
    (hdeps : ErasesDeps venv σ lenv t) :
    ∃ v', Erases venv Us σ.isAtom (RecIn lenv) [] v v' ∧ LBEval defaultFlags lenv t v' := by
  cases her with
  | box hbx => exact erases_correct_box henv hsub he hbx (.zeta hv hb)
  | letE hT₂ hv₂ herv herb =>
  cases he with
  | letE hvT hT hvt hbt =>
  cases TrS.det hT hT₂
  cases TrS.det hvt hv₂
  cases hdeps with
  | letIn hdv hdb =>
  obtain ⟨tv', herv', hevv⟩ := ihv hvt herv hdv
  obtain ⟨a₁, hta, hdf⟩ := SrcEval.defeq henv hsub hvt hvT hv
  have ⟨_, hT'⟩ := hdf.isType henv.ordered trivial
  have hΔ : VLCtx.IsDefEq venv Us.length [(none, .vlet _ _)] [(none, .vlet _ a₁)] :=
    .cons .nil nofun (.vlet hdf hT')
  have ⟨_, hb₁⟩ := TrS.defeqDFC henv.wf hΔ hbt
  obtain ⟨res, hres, hevres⟩ := ihb (TrS.inst_let henv.ordered hb₁ hta)
    (Erases.inst_let henv (RecIn.rcClosed hlc) herb herv' hta hdf hbt)
    (ErasesDeps.csubst (ErasesDeps.eval hdv hevv) hdb)
  exact ⟨res, hres, .zeta hevv hevres⟩

/-- The `delta` case of `erases_correct`, for a non-recursive constant: the λ□ declaration found
at the constant's kername is its own (`KernameInj`), whose body erases the constant's value
(`ErasesDecl`), at the occurrence's levels too (`Erases.instLevels`); a `tFix` stored at that
kername is such a body as well (`BlocksErased`). Reference: the `eval_delta` case of
`erases_correct` (`MR E/ErasureCorrectness.v:152`); Let. Thm 13 (δ). -/
theorem erases_correct_delta (henv : ProgEnv P venv) (hsub : SubEnv σ.decls P)
    (hinj : KernameInj σ.decls) (hblocks : BlocksErased venv σ lenv)
    (ihb : ∀ {b₀ tb}, TrS venv Us [] (Pure.instLevels ci.levelParams us body) b₀ →
      Erases venv Us σ.isAtom (RecIn lenv) [] (Pure.instLevels ci.levelParams us body) tb →
      ErasesDeps venv σ lenv tb →
      ∃ v', Erases venv Us σ.isAtom (RecIn lenv) [] v v' ∧ LBEval defaultFlags lenv tb v')
    (hu : σ.unfold? c = some (ci, body)) (hr : RecursiveDecl ci = false)
    (hlen : us.length = ci.levelParams.length)
    (hb : SrcEval σ (Pure.instLevels ci.levelParams us body) v)
    (he : TrS venv Us [] (.const c us) e')
    (her : Erases venv Us σ.isAtom (RecIn lenv) [] (.const c us) t)
    (hdeps : ErasesDeps venv σ lenv t) :
    ∃ v', Erases venv Us σ.isAtom (RecIn lenv) [] v v' ∧ LBEval defaultFlags lenv t v' := by
  have hfd := (EvalEnv.unfold?_some hu).1
  have hax := EvalEnv.unfold?_axiomatized hu
  have ⟨_, hb₀, _⟩ := SrcEval.unfold_step henv hsub hu he
  obtain ⟨_, hus⟩ : ∃ us', us.mapM (VLevel.ofLevel Us) = some us' := by
    cases he with | const _ hus _ => exact ⟨_, hus⟩
  have key : ∀ cb, ErasesDecl venv σ lenv ci cb → ∃ b', cb.cst_body = some b' ∧
      Erases venv Us σ.isAtom (RecIn lenv) [] (Pure.instLevels ci.levelParams us body) b' := by
    intro cb hd
    unfold ErasesDecl at hd
    rw [EvalEnv.unfold?_value? hu] at hd
    rcases hd with ⟨hax', -⟩ | ⟨-, hr', -⟩ | ⟨-, -, b', hcb, herb⟩
    · rw [hax] at hax'; cases hax'
    · rw [hr] at hr'; cases hr'
    · have := Erases.instLevels henv hus hlen herb
      exact ⟨b', hcb, this⟩
  cases her with
  | box hbx => exact erases_correct_box henv hsub he hbx (.delta hu hr hlen hb)
  | const _ =>
    generalize hk : toKername c = kn at hdeps
    cases hdeps with
    | const hfd₂ hl hd hbody =>
    cases hinj _ _ (by rw [hfd]; rfl) (by rw [hfd₂]; rfl) hk
    rw [hfd] at hfd₂
    cases hfd₂
    obtain ⟨b', hcb, herb⟩ := key _ hd
    obtain ⟨res, hres, hevres⟩ := ihb hb₀ herb (hbody b' hcb)
    exact ⟨res, hres, .delta hl hcb hevres⟩
  | constRec _ hrc =>
    obtain ⟨defs, i, rfl, hl⟩ := hrc
    obtain ⟨hd, hdefs⟩ := hblocks c ci defs i hfd hl
    obtain ⟨b', hcb, herb⟩ := key _ hd
    cases hcb
    exact ihb hb₀ herb hdeps

/-- The `constAtom` case of `erases_correct`: an atom constant erases only to `□`, which λ□
evaluates to itself. Reference: the `eval_atom` case of `erases_correct` on `tInd`
(`MR E/ErasureCorrectness.v:1207`, `eval_atom` at `:1218`), which erases only by `erases_box`
(`MR E/Extract.v:140`); DV-11. -/
theorem erases_correct_constAtom (ha : σ.isAtom c = true)
    (her : Erases venv Us σ.isAtom (RecIn lenv) [] (.const c us) t) :
    ∃ v', Erases venv Us σ.isAtom (RecIn lenv) [] (.const c us) v' ∧
      LBEval defaultFlags lenv t v' := by
  cases her with
  | const hc => exact nomatch ha.symm.trans hc
  | constRec hc _ => exact nomatch ha.symm.trans hc
  | box hb => exact ⟨.box, .box hb, .atom rfl⟩

/-- The `appCong` case of `erases_correct`: the head's value is an atom spine (`SrcEval.value`),
whose erasure evaluates to `□` (`Erases.atomSpine_box`), so the application evaluates to `□`,
and the value, an atom spine too, is erasable (`ErasableS.atomSpine`). Reference: the
`eval_app_cong` case of `erases_correct` (`MR E/ErasureCorrectness.v:1127`, `eval_app_cong` at
`:1144`). -/
theorem erases_correct_appCong (henv : ProgEnv P venv) (hsub : SubEnv σ.decls P)
    (ihf : ∀ {f₀ tf}, TrS venv Us [] f f₀ → Erases venv Us σ.isAtom (RecIn lenv) [] f tf →
      ErasesDeps venv σ lenv tf →
      ∃ v', Erases venv Us σ.isAtom (RecIn lenv) [] f' v' ∧ LBEval defaultFlags lenv tf v')
    (iha : ∀ {a₀ ta}, TrS venv Us [] a a₀ → Erases venv Us σ.isAtom (RecIn lenv) [] a ta →
      ErasesDeps venv σ lenv ta →
      ∃ v', Erases venv Us σ.isAtom (RecIn lenv) [] a' v' ∧ LBEval defaultFlags lenv ta v')
    (hf : SrcEval σ f f') (hbc : ¬ BlocksCong σ f') (ha : SrcEval σ a a')
    (he : TrS venv Us [] (.app f a) e')
    (her : Erases venv Us σ.isAtom (RecIn lenv) [] (.app f a) t)
    (hdeps : ErasesDeps venv σ lenv t) :
    ∃ v', Erases venv Us σ.isAtom (RecIn lenv) [] (.app f' a') v' ∧
      LBEval defaultFlags lenv t v' := by
  have hev : SrcEval σ (.app f a) (.app f' a') := .appCong hf hbc ha
  rcases Erases.app_inv her with ⟨rfl, hbx⟩ | ⟨tf, ta, rfl, herf, hera⟩
  · exact erases_correct_box henv hsub he hbx hev
  have hsp : AtomSpine σ f' := by
    cases SrcEval.value hf with
    | spine h => exact h
    | lam => exact absurd trivial hbc
    | sort => exact absurd trivial hbc
    | forallE => exact absurd trivial hbc
    | fixConst hu hr => exact absurd ⟨_, _, hu, hr⟩ hbc
  cases he with
  | app hfT haT hft hat =>
  cases hdeps with
  | app hdf hda =>
  obtain ⟨vf, hvf, hevf⟩ := ihf hft herf hdf
  obtain ⟨_, -, heva⟩ := iha hat hera hda
  cases Erases.atomSpine_box hsp hvf hevf
  obtain ⟨w, hw, -⟩ := SrcEval.defeq henv hsub (.app hfT haT hft hat) (hfT.app haT) hev
  exact ⟨.box, .box ⟨w, hw, ErasableS.atomSpine henv hsub (.app hsp) hw⟩, .box hevf heva⟩

/-- The `mdata` case of `erases_correct`: metadata is transparent in the translation, the
relation and the source semantics. Reference: none (Lean syntax). -/
theorem erases_correct_mdata (henv : ProgEnv P venv) (hsub : SubEnv σ.decls P)
    (ih : ∀ {e₀ t₀}, TrS venv Us [] e e₀ → Erases venv Us σ.isAtom (RecIn lenv) [] e t₀ →
      ErasesDeps venv σ lenv t₀ →
      ∃ v', Erases venv Us σ.isAtom (RecIn lenv) [] v v' ∧ LBEval defaultFlags lenv t₀ v')
    (hev : SrcEval σ e v)
    (he : TrS venv Us [] (.mdata d e) e')
    (her : Erases venv Us σ.isAtom (RecIn lenv) [] (.mdata d e) t)
    (hdeps : ErasesDeps venv σ lenv t) :
    ∃ v', Erases venv Us σ.isAtom (RecIn lenv) [] v v' ∧ LBEval defaultFlags lenv t v' := by
  cases her with
  | box hbx => exact erases_correct_box henv hsub he hbx (.mdata hev)
  | mdata her =>
    cases he with
    | mdata he => exact ih he her hdeps

/-- The `atom` case of `erases_correct`: a λ, sort or Π erases to a λ or to `□`, both λ□ values.
Reference: the `eval_atom` case of `erases_correct` (`MR E/ErasureCorrectness.v:1179`,
`eval_atom` at `:1218`). -/
theorem erases_correct_atom (ha : SrcAtom e)
    (her : Erases venv Us σ.isAtom (RecIn lenv) [] e t) :
    ∃ v', Erases venv Us σ.isAtom (RecIn lenv) [] e v' ∧ LBEval defaultFlags lenv t v' := by
  refine ⟨t, her, .atom ?_⟩
  cases her with
  | lam | box => rfl
  | bvar | fvar | letE | app | const | constRec | mdata => exact ha.elim

end

end EraseProof
