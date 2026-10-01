import EraseProof.Simulation.Cases

/-!
# Recursion cases of the relation-level simulation

The cases of `erases_correct` (`MR E/ErasureCorrectness.v:51`) for the rules of `SrcEval` that
treat a recursive constant as a PCUIC `tFix` with `rarg = 0` (DV-7): `fixAtom`, where the constant
is a value, and `fixApp`, where the constant applied to an argument unfolds. A recursive constant
erases to `□`, to its `tConst`, which λ□ evaluates by `eval_delta` to the `tFix` stored as its
body, or to that `tFix` directly (`Erases.constRec`). An applied `tFix` unfolds by `eval_fix` with
no earlier arguments; `BlocksErased` gives the unfolded body as an erasure of the constant's value.
-/

open Lean Lean4Lean Erasure

namespace EraseProof

section
variable {venv : VEnv} {P : List ConstantInfo} {σ : EvalEnv} {lenv : GlobalDeclarations}

/-- λ□ values are never constants. Reference: `eval_to_value` (`MR E/EWcbvEval.v:771`), whose
`value` (`:332`) has no `tConst` case (`atom`, `:36`). -/
theorem LBEval.ne_const (h : LBEval fl lenv t v) : v ≠ .const kn := by
  induction h using LBEval.ind with
  | box | fixValue | projProp | construct | constructBlock | appCong | prim =>
    exact LBTerm.noConfusion
  | beta _ _ _ _ _ ih | zeta _ _ _ ih | iota _ _ _ _ _ _ _ _ ih | iotaBlock _ _ _ _ _ _ _ _ ih
  | iotaSing _ _ _ _ _ _ ih | fix _ _ _ _ _ _ _ ih | fix' _ _ _ _ _ _ _ ih | delta _ _ _ ih
  | proj _ _ _ _ _ _ _ ih | projBlock _ _ _ _ _ _ _ ih => exact ih
  | atom ha =>
    rintro rfl
    exact Bool.false_ne_true ha

/-- Erasability is closed under expansion along source evaluation: a typed term whose value is
erasable is erasable, since the model relates the two by a typed definitional equality
(`SrcEval.defeq`) and types are unique. Reference: `Is_type_eval_inv` (`MR E/EArities.v:584`),
with unique typing (`l4l Theory/Typing/UniqueTyping.lean:13`) in place of `common_typing`. -/
theorem ErasableS.eval_inv (henv : ProgEnv P venv) (hsub : SubEnv σ.decls P)
    (he : TrS venv Us [] e e') (hT : venv.HasType Us.length [] e' T) (hev : SrcEval σ e v)
    (h : ErasableS venv Us [] v) : ErasableS venv Us [] e := by
  obtain ⟨v'', hv'', T', hT', hE⟩ := h
  obtain ⟨v', hv, hd⟩ := SrcEval.defeq henv hsub he hT hev
  cases hv.det hv''
  obtain ⟨_, hTT'⟩ := VEnv.IsDefEq.uniq henv.wf trivial hd.hasType.2 hT'
  exact ⟨e', he, T', hTT'.defeq hd.hasType.1, hE⟩

/-- The `tFix` stored at the kername of a recursive, unfoldable constant unfolds (`cunfoldFix`,
`rarg = 0`) to an erasure of the constant's value at its own level parameters, whose dependencies
are erased. Reference: the `erases_tFix` premises on the unfolded body in the `eval_fix` case of
`erases_correct` (`MR E/ErasureCorrectness.v:579-748`), with `erases_deps_cunfold_fix`
(`MR E/EDeps.v:245`); DV-7. -/
theorem BlocksErased.unfold (hblocks : BlocksErased venv σ lenv)
    (hu : σ.unfold? c = some (ci, body)) (hr : RecursiveDecl ci = true)
    (hl : lookupConst lenv (toKername c) = some ⟨some (.fix defs i)⟩) :
    ∃ fn, cunfoldFix defs i = some (0, fn) ∧
      Erases venv ci.levelParams σ.isAtom (RecIn lenv) [] body fn ∧ ErasesDeps venv σ lenv fn := by
  have hfd := (EvalEnv.unfold?_some hu).1
  have hn : ci.name = c :=
    beq_iff_eq.1 (List.find?_some (p := fun x : ConstantInfo => x.name == c) hfd)
  obtain ⟨hd, hdeps⟩ := hblocks c ci defs i hfd hl
  unfold ErasesDecl at hd
  rw [EvalEnv.unfold?_value? hu] at hd
  rcases hd with ⟨hax, -⟩ | ⟨-, -, defs', i', hb, hi, -, hj⟩ | ⟨-, hr', -⟩
  · rw [EvalEnv.unfold?_axiomatized hu] at hax; cases hax
  · cases hb
    obtain ⟨ci', v, d, hfd', hv, hdi, -, hidx, her, -⟩ := hj i ci.name hi
    rw [hn, hfd] at hfd'
    cases hfd'
    rw [EvalEnv.unfold?_value? hu] at hv
    cases hv
    have hcu : cunfoldFix defs i = some (0, substl (fixSubst defs) d.body) := by
      simp [cunfoldFix, hdi, hidx]
    exact ⟨_, hcu, her, ErasesDeps.cunfoldFix hdeps hcu⟩
  · rw [hr] at hr'; cases hr'

/-- The `fixAtom` case of `erases_correct`: a recursive constant erases to `□`, to the `tFix`
stored as its body (`Erases.constRec`), both λ□ values, or to its `tConst`, which λ□ evaluates by
`eval_delta` to that `tFix`: the declaration found at the constant's kername is its own
(`KernameInj`), and its body is a `tFix` of its block (`ErasesDecl`). Reference: the `eval_delta`
case of `erases_correct` (`MR E/ErasureCorrectness.v:152`) to a `tFix` value, and its `eval_atom`
case (`:1218`); DV-7. -/
theorem erases_correct_fixAtom (hinj : KernameInj σ.decls)
    (hu : σ.unfold? c = some (ci, body)) (hr : RecursiveDecl ci = true)
    (her : Erases venv Us σ.isAtom (RecIn lenv) [] (.const c us) t)
    (hdeps : ErasesDeps venv σ lenv t) :
    ∃ v', Erases venv Us σ.isAtom (RecIn lenv) [] (.const c us) v' ∧
      LBEval defaultFlags lenv t v' := by
  cases her with
  | box hbx => exact ⟨.box, .box hbx, .atom rfl⟩
  | constRec hac hrc =>
    obtain ⟨defs, i, rfl, hl⟩ := hrc
    exact ⟨_, .constRec hac ⟨defs, i, rfl, hl⟩, .atom rfl⟩
  | const hac =>
    have hfd := (EvalEnv.unfold?_some hu).1
    generalize hk : toKername c = kn at hdeps
    cases hdeps with
    | @const _ _ cb hfd₂ hl hd _ =>
    cases hinj _ _ (by rw [hfd]; rfl) (by rw [hfd₂]; rfl) hk
    rw [hfd] at hfd₂
    cases hfd₂
    unfold ErasesDecl at hd
    rw [EvalEnv.unfold?_value? hu] at hd
    rcases hd with ⟨hax, -⟩ | ⟨-, -, defs, i, hb, -⟩ | ⟨-, hr', -⟩
    · rw [EvalEnv.unfold?_axiomatized hu] at hax; cases hax
    · obtain ⟨b⟩ := cb
      cases hb
      exact ⟨_, .constRec hac ⟨defs, i, rfl, hl⟩, .delta hl rfl (.atom rfl)⟩
    · rw [hr] at hr'; cases hr'

/-- The `fixApp` case of `erases_correct`: the head's erasure evaluates to an erasure of the
recursive constant, which is `□` (so the application evaluates to `□`, and the value is erasable)
or the `tFix` stored as the constant's body (a λ□ value is never a `tConst`). That `tFix` unfolds
with `rarg = 0` to an erasure of the constant's value (`BlocksErased`), at the occurrence's levels
too (`Erases.instLevels`), and λ□ evaluates the application by `eval_fix` with no earlier
arguments. Reference: the `eval_fix` case of `erases_correct` (`MR E/ErasureCorrectness.v:579`,
`eval_fix` at `:598`, `:620`, `:688`, `:737`); Let. Thm 13 (fix). -/
theorem erases_correct_fixApp (henv : ProgEnv P venv) (hsub : SubEnv σ.decls P)
    (hblocks : BlocksErased venv σ lenv)
    (ihf : ∀ {f₀ tf}, TrS venv Us [] f f₀ → Erases venv Us σ.isAtom (RecIn lenv) [] f tf →
      ErasesDeps venv σ lenv tf →
      ∃ v', Erases venv Us σ.isAtom (RecIn lenv) [] (.const c us) v' ∧
        LBEval defaultFlags lenv tf v')
    (iha : ∀ {a₀ ta}, TrS venv Us [] a a₀ → Erases venv Us σ.isAtom (RecIn lenv) [] a ta →
      ErasesDeps venv σ lenv ta →
      ∃ v', Erases venv Us σ.isAtom (RecIn lenv) [] a' v' ∧ LBEval defaultFlags lenv ta v')
    (ihb : ∀ {b₀ tb},
      TrS venv Us [] (.app (Pure.instLevels ci.levelParams us body) a') b₀ →
      Erases venv Us σ.isAtom (RecIn lenv) [] (.app (Pure.instLevels ci.levelParams us body) a')
        tb →
      ErasesDeps venv σ lenv tb →
      ∃ v', Erases venv Us σ.isAtom (RecIn lenv) [] v v' ∧ LBEval defaultFlags lenv tb v')
    (hf : SrcEval σ f (.const c us)) (hu : σ.unfold? c = some (ci, body))
    (hr : RecursiveDecl ci = true) (ha : SrcEval σ a a')
    (hb : SrcEval σ (.app (Pure.instLevels ci.levelParams us body) a') v)
    (he : TrS venv Us [] (.app f a) e')
    (her : Erases venv Us σ.isAtom (RecIn lenv) [] (.app f a) t)
    (hdeps : ErasesDeps venv σ lenv t) :
    ∃ v', Erases venv Us σ.isAtom (RecIn lenv) [] v v' ∧ LBEval defaultFlags lenv t v' := by
  have hev : SrcEval σ (.app f a) v := .fixApp hf hu hr ha hb
  rcases Erases.app_inv her with ⟨rfl, hbx⟩ | ⟨tf, ta, rfl, herf, hera⟩
  · exact erases_correct_box henv hsub he hbx hev
  have he₀ := he
  cases he with
  | app hfT haT hft hat =>
  cases hdeps with
  | app hdf hda =>
  obtain ⟨vf, hvf, hevf⟩ := ihf hft herf hdf
  obtain ⟨va, hva, heva⟩ := iha hat hera hda
  cases hvf with
  | box hbx =>
    obtain ⟨_, hf₀, hEf⟩ := ErasableS.eval_inv henv hsub hft hfT hf hbx
    cases hft.det hf₀
    have hEa : ErasableS venv Us [] (.app f a) :=
      ⟨_, he₀, IsErasable.app henv trivial (hfT.app haT) hEf⟩
    exact ⟨.box, .box (ErasableS.eval henv hsub he₀ hev hEa), .box hevf heva⟩
  | const _ => exact absurd rfl (LBEval.ne_const hevf)
  | constRec hac hrc =>
    obtain ⟨defs, i, rfl, hl⟩ := hrc
    obtain ⟨fn, hcu, herb, hdfn⟩ := hblocks.unfold hu hr hl
    obtain ⟨c₀, hc₀, hdc⟩ := SrcEval.defeq henv hsub hft hfT hf
    obtain ⟨a₁, ha₁, hda₁⟩ := SrcEval.defeq henv hsub hat haT ha
    obtain ⟨b₀, hb₀, hdb⟩ := SrcEval.unfold_step henv hsub hu hc₀
    have hfb := hdc.transU_l henv.wf trivial hdb
    obtain ⟨_, hus, hlen⟩ : ∃ us', us.mapM (VLevel.ofLevel Us) = some us' ∧
        us.length = ci.levelParams.length := by
      cases hc₀ with
      | const hc hus hlen =>
        obtain ⟨ci', htr, hc', -⟩ := henv.unfold hsub hu
        cases hc.symm.trans hc'
        exact ⟨_, hus, hlen.trans htr.1.1.symm⟩
    obtain ⟨res, hres, hevres⟩ := ihb (.app hfb.hasType.2 hda₁.hasType.2 hb₀ ha₁)
      (.app (Erases.instLevels henv hus hlen herb) hva)
      (.app hdfn (ErasesDeps.eval hda heva))
    exact ⟨res, hres, .fix (argsv := []) rfl hevf heva hcu hevres⟩

end

end EraseProof
