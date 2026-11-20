import EraseProof.Semantics.Frozen
import EraseProof.Semantics.Decode
import EraseProof.Statements
import ConLeche.Model.Rules.RedSoundKit

/-!
# `Sound`'s antecedent has content

An input that con-leche types, applied to closed arguments, at a type whose whnf is a sort has a
denotation in every model, and it is not the proof point: the application is a member of a
universe, whose members are types, and the proof point applied is the proof point.
-/

open Lean Erasure
open ConLeche.Semantics ConLeche.SetModel ConLeche.SetTheory ConLeche.Verify ConLeche.Model
  ConLeche.Model.Rules

namespace EraseProof

universe w

/-- The head of a spine without loose bound variables has none. Reference: none. -/
theorem looseBVarsBounded_mkAppN_head : ∀ (as : List ConLeche.Expr) {f : ConLeche.Expr},
    (ConLeche.Expr.mkAppN f as).looseBVarsBounded 0 = true → f.looseBVarsBounded 0 = true
  | [], _, h => h
  | a :: as, f, h => by
    have h' := looseBVarsBounded_mkAppN_head as (f := .app f a) h
    simp only [ConLeche.Expr.looseBVarsBounded, Bool.and_eq_true] at h'
    exact h'.1

/-- `sound_nonvacuous`: the reading of the application is closed (`CLTyped.closed`,
`toCL?_hasFvar`) and a spine of the input's reading (`Decode.toCL?_foldl`,
`CL ConLeche/Verify/Denote/Lemmas.lean:161 denote_mkAppN_inv`); its interpretation is a member of
its inferred type (`CL ConLeche/Model/Rules/Sound.lean:188 infer_sound`), which is a type, so not
the point, and equals its whnf (`red_sound` on `CL ConLeche/Verify/Rules/Bridge.lean:59
whnf_bridge`), a sort; so the application is a type
(`CL ConLeche/SetTheory/Derive/Univ.lean:45 ne_pt_of_mem_univ`), and the input is not the point
(`CL ConLeche/Model/Rules/RedSoundKit.lean:761 interp_mkAppN_of_pt`). Reference: none (DV-34). -/
theorem sound_nonvacuous : sound_nonvacuous_statement.{w} := by
  intro P env e as c c₁ T W F _ hc hc₁ hinf hw hW V _ m φ ρ
  obtain ⟨u, rfl⟩ := hW
  have hfv₁ := toCL?_hasFvar hc₁
  have hb₁ := CLTyped.closed ⟨c₁, F, T, hc₁, hinf⟩ hc₁
  rw [mkAppN_toArray] at hc₁
  obtain ⟨cf, cas, hcf, -, rfl⟩ := Decode.toCL?_foldl as e hc₁
  rw [hc, Option.some.injEq] at hcf
  subst hcf
  have hnil := ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hfv₁
  have hnc : ∀ l, l ∉ (ConLeche.Expr.mkAppN c cas).fvarLeaves := fun l hl => by
    rw [hnil] at hl; cases hl
  obtain ⟨ea, hea, -⟩ := SemCases.infer0 m φ hinf hfv₁ hb₁
  have hin := Rules.RulesInputs.ofSem m φ
  obtain ⟨hfT, hsT, ta, hta, hcs⟩ := infer_sound hin (ConLeche.Rules.inferTypeCore_bridge hinf)
    ⟨ConLeche.Expr.WScoped.of_not_hasFvar hfv₁, hb₁, fun l hl => absurd hl (hnc l)⟩
    (SemCases.ctx0 m φ hnc).1 hea
  have hnT : ∀ l, l ∉ T.fvarLeaves := fun l hl => hnc l (hsT l hl)
  obtain ⟨-, -, wa, hwa, hsw⟩ :=
    red_sound hin (ConLeche.Rules.whnf_bridge hw) hfT (SemCases.ctx0 m φ hnT).1 hta
  simp only [denote, Option.some.injEq] at hwa
  subst hwa
  obtain ⟨-, hwta, hmem⟩ := hcs ρ (Sat_nil V ρ) ((SemCases.ctx0 m φ hnc).2 ρ)
  obtain ⟨-, heq⟩ := hsw ρ (Sat_nil V ρ) ((SemCases.ctx0 m φ hnT).2 ρ) hwta.1 hwta.2.ne_pt
  rw [heq, interp_sort] at hmem
  obtain ⟨fa, vs, hfa, -, rfl⟩ := denote_mkAppN_inv hea
  exact ⟨interp V ρ fa,
    (SemCases.denotes_iff m φ ρ hfa (toCL?_hasFvar hc) (looseBVarsBounded_mkAppN_head cas hb₁) _).mpr
      rfl,
    fun h => ne_pt_of_mem_univ hmem (interp_mkAppN_of_pt h vs)⟩

end EraseProof
