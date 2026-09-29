import EraseProof.Erasability
import EraseProof.Typing.Basic
import EraseProof.Typing.InstLevels
import EraseProof.Atoms
import EraseProof.Source.Defeq
import EraseProof.Source.Restrict

/-!
# Erasability of source terms

`ErasableS` lifts `IsErasable` to Lean terms through the translation `TrS`. This module proves
that it is stable under source evaluation (`ErasableS.eval`, by subject reduction
`SrcEval.defeq`), and that the atom constants of the source semantics are erasable at every use
levels (`ErasableS.atom`): an evident type former has an arity type, and an evident proof has a
propositional type. The second fact is read from the constant's declared type in the model, at the
constant's own level parameters, and transported to the use levels by universe instantiation.
-/

open Lean Lean4Lean Erasure

namespace EraseProof

/-- A source term is erasable when its model image is. Reference: `MR E/Extract.v:18 isErasable`
on the source syntax (DV-1). -/
def ErasableS (venv : VEnv) (Us : List Name) (Δ : VLCtx) (e : Expr) : Prop :=
  ∃ e', TrS venv Us Δ e e' ∧ IsErasable venv Us.length Δ.toCtx e'

/-- Model arities with their binder count and final level: `VArityShape T n w` says that `T` is
`Π x₁…xₙ, Sort w`. The model counterpart of `arityShape`. Reference: `destArity`
(`MR P/PCUICAst.v:486`), which `isPropositionalArity` (`MR P/PCUICFirstorder.v:103`) reads. -/
inductive VArityShape : VExpr → Nat → VLevel → Prop
  | sort : VArityShape (.sort w) 0 w
  | forallE : VArityShape B n w → VArityShape (.forallE A B) (n + 1) w

/-- An arity with a binder count is an arity. Reference: `isArity` (`MR P/PCUICTyping.v:29`). -/
theorem VArityShape.isArity (H : VArityShape T n w) : IsArity T := by
  induction H with
  | sort => trivial
  | forallE _ ih => exact ih

/-- Substitution keeps an arity's binder count and final level (sorts are closed). Reference:
`isArity_subst` (`MR P/PCUICClassification.v:33`). -/
theorem VArityShape.inst (H : VArityShape T n w) : VArityShape (T.inst a k) n w := by
  induction H generalizing k with
  | sort => exact .sort
  | forallE _ ih => exact .forallE ih

/-- Universe instantiation keeps an arity's binder count and instantiates its final level.
Reference: `isArity_subst_instance` (`MR P/Typing/PCUICUnivSubstitutionTyp.v:537`). -/
theorem VArityShape.instL (H : VArityShape T n w) :
    VArityShape (T.instL ls) n (w.inst ls) := by
  induction H with
  | sort => exact .sort
  | forallE _ ih => exact .forallE ih

section
variable {venv : VEnv} {P : List ConstantInfo} {σ : EvalEnv}

/-- The translation of a syntactic arity (`arityShape`) is a model arity with the same binder
count, whose final level translates the source's. Reference: none in MetaRocq (no translation). -/
theorem TrS.arityShape (H : TrS venv Us Δ T T') :
    ∀ {n u}, arityShape T = some (n, u) →
      ∃ w, VLevel.ofLevel Us u = some w ∧ VArityShape T' n w := by
  induction H with
  | sort h1 =>
    intro n u h
    simp only [EraseProof.arityShape, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, h1, .sort⟩
  | forallE _ _ _ _ _ ih =>
    intro n u h
    simp only [EraseProof.arityShape, Option.map_eq_some_iff] at h
    obtain ⟨⟨n', u'⟩, h1, h2⟩ := h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    obtain ⟨w, hw, hA⟩ := ih h1
    exact ⟨w, hw, .forallE hA⟩
  | mdata _ ih => intro n u h; exact ih h
  | bvar | fvar | const | app | lam | letE => intro n u h; simp [EraseProof.arityShape] at h

/-- An evidently zero level translates to a level equivalent to zero. Reference:
`Sort.is_propositional` (`MR common/theories/Universes.v:1528`), soundness. -/
theorem EvidentZero.sound : ∀ {u : Level} {u' : VLevel}, EvidentZero u = true →
    VLevel.ofLevel Us u = some u' → u' ≈ .zero
  | .zero, _, _, h => by simp [VLevel.ofLevel] at h; subst h; rfl
  | .max a b, _, hz, h => by
    simp only [EvidentZero, Bool.and_eq_true] at hz
    simp only [VLevel.ofLevel, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨a', h1, b', h2, rfl⟩ := h
    exact (VLevel.max_congr (EvidentZero.sound hz.1 h1) (EvidentZero.sound hz.2 h2)).trans
      VLevel.max_self
  | .imax a b, _, hz, h => by
    simp only [EvidentZero] at hz
    simp only [VLevel.ofLevel, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨a', h1, b', h2, rfl⟩ := h
    exact VLevel.imax_eq_zero.2 (EvidentZero.sound hz h2)
  | .succ _, _, hz, _ | .param _, _, hz, _ | .mvar _, _, hz, _ => by simp [EvidentZero] at hz

/-- The typed image of an application spine `h.{vs} a₁…aₖ` whose head's model type is an arity
with `k + m` binders ending in `Sort w` has an arity type with `m` binders ending in `Sort w`
instantiated by the image of `vs`. Reference: `type_mkApps` (`MR P/PCUICSpine.v:2391`), the
typing of an application spine, here of an atom head (DV-11). -/
theorem TrS.spine_type (henv : venv.WF) (hΓ : OnCtx Δ.toCtx (venv.IsType Us.length))
    {hci' : VConstant} (hh : venv.constants h = some hci') (har : VArityShape hci'.type n w) :
    ∀ {e e' m}, e.getAppFn = .const h vs → TrS venv Us Δ e e' → e.getAppNumArgs + m = n →
      ∃ vs', vs.mapM (VLevel.ofLevel Us) = some vs' ∧ vs.length = hci'.uvars ∧
        ∃ R, venv.HasType Us.length Δ.toCtx e' R ∧ VArityShape R m (w.inst vs') := by
  intro e
  induction e with
  | const c us =>
    intro e' m hfn H hm
    simp only [Expr.getAppFn, Expr.const.injEq] at hfn
    obtain ⟨rfl, rfl⟩ := hfn
    cases H with
    | const h1 h2 h3 =>
      rw [hh] at h1; cases h1
      have hm' : m = n := by
        simpa [Expr.getAppNumArgs_eq, Expr.getAppArgsRevList] using hm
      subst hm'
      refine ⟨_, h2, h3, _, .const hh (VLevel.WF.of_mapM_ofLevel h2)
        ((List.mapM_eq_some.1 h2).length_eq.symm.trans h3), har.instL⟩
  | app f a ihf _ =>
    intro e' m hfn H hm
    simp only [Expr.getAppFn] at hfn
    have hnum : (Expr.app f a).getAppNumArgs = f.getAppNumArgs + 1 := by
      simp [Expr.getAppNumArgs_eq, Expr.getAppArgsRevList]
    cases H with
    | app hf ha tf _ =>
      obtain ⟨vs', hvs, hlen, R, hR, hA⟩ := ihf (m := m + 1) hfn tf (by omega)
      cases hA with
      | forallE hA' =>
        have ⟨_, hd⟩ := hf.uniq henv hΓ hR
        have ⟨⟨_, hdom⟩, _⟩ := VEnv.IsDefEqU.forallE_inv henv hΓ ⟨_, hd⟩
        exact ⟨vs', hvs, hlen, _, hR.app (hdom.defeq ha), hA'.inst⟩
  | bvar | fvar | mvar | sort | lam | forallE | letE | lit | mdata | proj =>
    intro e' m hfn; simp [Expr.getAppFn] at hfn

/-- The tail case of `TrS.evidentProp_sort`: the image of an application spine `h.{vs} a₁…aₙ`
that `EvidentProp` accepts is a proposition. Reference: as `TrS.evidentProp_sort`. -/
theorem TrS.evidentProp_tail (henv : ProgEnv P venv) {decls : List ConstantInfo}
    (hsub : SubEnv decls P) (hΓ : OnCtx Δ.toCtx (venv.IsType Us.length))
    (H : TrS venv Us Δ T T') (hnf : ∀ n t b bi, T = .forallE n t b bi → False)
    (hnm : ∀ m x, T = .mdata m x → False) (hp : EvidentProp decls T = true) :
    ∃ u, venv.HasType Us.length Δ.toCtx T' (.sort u) ∧ u ≈ .zero := by
  rw [EvidentProp.eq_3 decls T hnf hnm] at hp
  split at hp
  next h vs hfn =>
    split at hp
    next hci hfd =>
      simp only [Bool.and_eq_true] at hp
      obtain ⟨-, hp⟩ := hp
      split at hp
      next n u hsh =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hp
        obtain ⟨hn, hz⟩ := hp
        obtain ⟨hci', hc', hl, htr⟩ := henv.lookup (hsub.findDecl_of_some hfd)
        obtain ⟨w, hw, har⟩ := htr.arityShape hsh
        obtain ⟨vs', hvs, hlen, R, hR, hA⟩ :=
          H.spine_type henv.wf hΓ hc' har hfn (m := 0) (by omega)
        cases hA
        exact ⟨_, hR, EvidentZero.sound hz (ofLevel_instLevel hvs (hlen.trans hl.symm) hw)⟩
      next => cases hp
    next => cases hp
  next => cases hp

/-- The image of an evident proposition (`EvidentProp`) is a proposition: its sort is equivalent
to zero. Reference: `isPropositional` (`MR P/PCUICFirstorder.v:109`), soundness, for the
fragment's evident propositions (DV-11). -/
theorem TrS.evidentProp_sort (henv : ProgEnv P venv) {decls : List ConstantInfo}
    (hsub : SubEnv decls P) :
    ∀ {T : Expr} {Δ T'}, OnCtx Δ.toCtx (venv.IsType Us.length) → TrS venv Us Δ T T' →
      EvidentProp decls T = true →
      ∃ u, venv.HasType Us.length Δ.toCtx T' (.sort u) ∧ u ≈ .zero := by
  intro T
  induction T with
  | forallE nm t b bi _ ihb =>
    intro Δ T' hΓ H hp
    simp only [EvidentProp] at hp
    cases H with
    | forallE h1 _ _ hb =>
      have ⟨_, h1'⟩ := h1
      have ⟨v, hv, hv0⟩ := ihb (Δ := (none, .vlam _) :: Δ) ⟨hΓ, h1⟩ hb hp
      exact ⟨_, h1'.forallE hv, VLevel.imax_eq_zero.2 hv0⟩
  | mdata m e ih =>
    intro Δ T' hΓ H hp
    simp only [EvidentProp] at hp
    cases H with
    | mdata H => exact ih hΓ H hp
  | _ =>
    intro Δ T' hΓ H hp
    exact H.evidentProp_tail henv hsub hΓ (fun _ _ _ _ h => by cases h)
      (fun _ _ h => by cases h) hp

/-- Erasability is stable under evaluation. Reference: `Is_type_eval` (`MR E/EArities.v:570`);
Let. Lemma 2 (subject reduction clause). -/
theorem ErasableS.eval (henv : ProgEnv P venv) (hsub : SubEnv σ.decls P)
    (he : TrS venv Us [] e e') (hev : SrcEval σ e v) (h : ErasableS venv Us [] e) :
    ErasableS venv Us [] v := by
  obtain ⟨e'', he'', T, hT, hT'⟩ := h
  cases he.det he''
  obtain ⟨v', hv, hd⟩ := SrcEval.defeq henv hsub he hT hev
  exact ⟨v', hv, T, hd.hasType.2, hT'⟩

/-- Atom constants are erasable at every use levels: an evident type former has an arity type, an
evident proof a propositional type. Reference: none directly; `tInd` has no `erases` rule and a
propositional constructor erases only by `erases_box` (`MR E/Extract.v:106,140`); DV-11. -/
theorem ErasableS.atom (henv : ProgEnv P venv) (hsub : SubEnv σ.decls P)
    (ha : σ.isAtom c = true) (he : TrS venv Us Δ (.const c us) e') :
    ErasableS venv Us Δ (.const c us) := by
  refine ⟨e', he, ?_⟩
  cases he with
  | const hc hus hlen =>
    unfold EvalEnv.isAtom at ha
    split at ha
    next ci hfd =>
      obtain ⟨ci', hc', hl, htr⟩ := henv.lookup (hsub.findDecl_of_some hfd)
      rw [hc] at hc'; cases hc'
      have hls := VLevel.WF.of_mapM_ofLevel hus
      refine ⟨_, .const hc hls ((List.mapM_eq_some.1 hus).length_eq.symm.trans hlen), ?_⟩
      simp only [Bool.and_eq_true, Bool.or_eq_true] at ha
      obtain ⟨-, har | hep⟩ := ha
      · obtain ⟨⟨n, u⟩, hsh⟩ := Option.isSome_iff_exists.1 har
        obtain ⟨w, -, hA⟩ := htr.arityShape hsh
        exact .inl hA.isArity.instL
      · obtain ⟨u, hu, hu0⟩ := htr.evidentProp_sort henv hsub (Δ := []) trivial hep
        exact .inr ⟨u.inst _, (hu.instL hls).weak0 henv.ordered, VLevel.inst_congr_l hu0⟩
    next => cases ha

end

end EraseProof
