import EraseProof.Final
import EraseProof.Test.NVQModel
import EraseProof.Test.NVQRun

/-!
# NV-Q end to end

The remaining hypotheses of the final theorem on NV-Q (`Test/NVQData.lean`): the view agrees with
the program (`hview`), the fragment test accepts `e` (`hfrag`, the closure `D` of `hcollect`), and
`e` evaluates to `B.t` (`hev`: the quotient ι, `SrcEval.quotLift`, on `Quot.mk R (fun y => y)`,
whose element is a value, continues with the body of `fun x => x` at the element, `fun y => y`;
then a β-step on the argument `B.t`). `final` applies the final theorem `erase_correct` to all
eight hypotheses (`henv`, `hwf`, `he`, `hty` from `Test/NVQModel.lean`, `hrun` from
`Test/NVQRun.lean`): the program `p0` that `#erase` emits is an untyped λ□ program whose main term
evaluates to an erasure of `B.t`.
-/

open Lean Erasure Metalean

namespace EraseProof.Test.NVQ

open EraseProof.Test.NV1 (tB cT B_ind Bf_ctor Bt_ctor B_rec)
open EraseProof.Test.NVP (l1)

theorem mem_P {ci : ConstantInfo} (h : ci ∈ P) :
    ci = .axiomInfo hR_ax ∨ ci = .axiomInfo R_ax ∨ ci = .quotInfo QuotInd_val ∨
      ci = .quotInfo QuotLift_val ∨ ci = .quotInfo QuotMk_val ∨ ci = .quotInfo Quot_val ∨
      ci ∈ NVP.P := by
  simpa [P, qs] using h

/-- `hview`: the view `#erase` reads agrees with the program. -/
theorem hview : ViewAgrees view P := by
  intro ci h
  rcases mem_P h with rfl | rfl | rfl | rfl | rfl | rfl | h
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · simp only [NVP.P, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- `hfrag`: the fragment test accepts `e`, with the closure `D`. -/
theorem hfrag : collectDeps view cfg e = .ok D := hcollect

/-- A λ is a value. -/
theorem ev_lam {x : Name} {A b : Expr} {bi : BinderInfo} :
    SrcEval (evalEnvOf view cfg P) (.lam x A b bi) (.lam x A b bi) :=
  SrcEval.atom trivial

/-- `@Quot.lift … (fun x => x) hR (Quot.mk R (fun y => y))` evaluates to `fun y => y`, by the
quotient ι. -/
theorem ev_lift :
    SrcEval (evalEnvOf view cfg P)
      (mkAppN (.const `Quot.lift [l1, l1]) [tBB, cR, tBB, idF, .const `hR [], qm].toArray) idB :=
  SrcEval.quotLift (qv := QuotLift_val) (qv' := QuotMk_val) rfl rfl ev_lam
    (SrcEval.quotMk (qv := QuotMk_val) (α := tBB) (r := cR) rfl rfl ev_lam) rfl rfl ev_lam

/-- `B.t` is a value. -/
theorem ev_cT : SrcEval (evalEnvOf view cfg P) cT cT :=
  SrcEval.ctor (c := `B.t) (us := []) (as := []) (vs := []) rfl rfl rfl (fun _ _ _ h => nomatch h)

/-- `hev`: `e` evaluates to `B.t`. -/
theorem hev : SrcEval (evalEnvOf view cfg P) e cT := by
  refine SrcEval.beta (f := mkAppN (.const `Quot.lift [l1, l1]) [tBB, cR, tBB, idF, .const `hR [], qm].toArray)
    ?_ ev_lift ev_cT ev_cT
  rintro ⟨c, us, ar, hc, ha, hle⟩
  have hc' : c = `Quot.lift := by
    simp only [Expr.getAppFn, mkAppN, Array.foldl, List.foldl] at hc
    cases hc; rfl
  subst hc'
  have : ar = 6 := by
    simp only [specialArity, evalEnvOf] at ha
    have hf : findDecl P `Quot.lift = some (.quotInfo QuotLift_val) := rfl
    rw [hf] at ha
    simp [quotEvalArity, QuotLift_val] at ha
    exact ha.symm
  subst this
  revert hle
  decide

/-! ## A quotient type as an argument

The quotient type former `Quot` is an atom (DV-29), so a quotient type is a value and a program
that passes one as an argument evaluates: `@Quot (B → B) R` evaluates to itself (`ev_qT`), and the
variant of NV-Q's term whose quotient is passed through the identity at a type argument,
`Quot.lift (fun x => x) hR ((fun (T : Type) (q : T) => q) (@Quot (B → B) R)
(Quot.mk R (fun y => y))) B.t`, evaluates to `B.t` (`ev_eT`). -/

/-- `@Quot.{1} (B → B) R` -/
def qT : Expr := .app (.app (.const `Quot [l1]) tBB) cR

/-- No spine of `Quot` blocks application congruence. -/
theorem quot_not_blocksCong {x : Expr} (hx : x.getAppFn = .const `Quot [l1]) :
    ¬ BlocksCong (evalEnvOf view cfg P) x := by
  have hQ : findDecl P `Quot = some (.quotInfo Quot_val) := rfl
  have hcs : (evalEnvOf view cfg P).casesOn? `Quot = none := rfl
  have key : ¬ ((∃ c us cv, x.getAppFn = .const c us ∧ findDecl P c = some (.ctorInfo cv)) ∨
      (∃ c us iv, x.getAppFn = .const c us ∧ (evalEnvOf view cfg P).casesOn? c = some iv) ∨
      (∃ c us qv, x.getAppFn = .const c us ∧ findDecl P c = some (.quotInfo qv) ∧
        qv.kind = .ctor)) := by
    rintro (⟨c, us, cv, hc, hcv⟩ | ⟨c, us, iv, hc, hiv⟩ | ⟨c, us, qv, hc, hqv, hk⟩) <;>
      rw [hx] at hc <;> cases hc
    · rw [hQ] at hcv; cases hcv
    · rw [hcs] at hiv; cases hiv
    · rw [hQ] at hqv; cases hqv; cases hk
  cases x with
  | const => exact key
  | app => exact key
  | _ => simp [Expr.getAppFn] at hx

/-- No spine of `Quot` is a short spine: `Quot` has no arity. -/
theorem quot_not_short {x : Expr} (hx : x.getAppFn = .const `Quot [l1]) :
    ¬ ShortSpine (evalEnvOf view cfg P) x := by
  have hQ : findDecl P `Quot = some (.quotInfo Quot_val) := rfl
  rintro ⟨c, us, ar, hc, ha, -⟩
  rw [hx] at hc; cases hc
  simp [specialArity, evalEnvOf, hQ, quotEvalArity, Quot_val] at ha

/-- The quotient type `@Quot (B → B) R` is a value: `Quot` and `R` are atoms, `B → B` a Π. -/
theorem ev_qT : SrcEval (evalEnvOf view cfg P) qT qT :=
  SrcEval.appCong (quot_not_short rfl)
    (SrcEval.appCong (quot_not_short rfl) (SrcEval.constAtom rfl) (quot_not_blocksCong rfl)
      (SrcEval.atom trivial))
    (quot_not_blocksCong rfl) (SrcEval.constAtom rfl)

/-- `fun (T : Type) (q : T) => q` -/
def idT : Expr := .lam `T (.sort l1) (.lam `q (.bvar 0) (.bvar 0) .default) .default

/-- `idT (@Quot (B → B) R) (Quot.mk R (fun y => y))` -/
def qa : Expr := .app (.app idT qT) qm

/-- `Quot.mk R (fun y => y)` is a value. -/
theorem ev_qm : SrcEval (evalEnvOf view cfg P) qm qm :=
  SrcEval.quotMk (qv := QuotMk_val) (α := tBB) (r := cR) rfl rfl ev_lam

/-- `idT` at the quotient type evaluates to the identity on the quotient, and at `Quot.mk R (fun y
=> y)` to the latter: the quotient type is evaluated as a β-argument. -/
theorem ev_qa : SrcEval (evalEnvOf view cfg P) qa qm := by
  have h1 : SrcEval (evalEnvOf view cfg P) (.app idT qT) (.lam `q qT (.bvar 0) .default) :=
    SrcEval.beta (by rintro ⟨c, us, ar, hc, -⟩; simp [Expr.getAppFn, idT] at hc) ev_lam ev_qT
      ev_lam
  exact SrcEval.beta (by rintro ⟨c, us, ar, hc, -⟩; simp [Expr.getAppFn, idT] at hc) h1 ev_qm
    ev_qm

/-- NV-Q's term with the quotient passed through `idT`. -/
def eT : Expr :=
  mkAppN (.const `Quot.lift [l1, l1]) #[tBB, cR, tBB, idF, .const `hR [], qa, cT]

/-- The variant `eT` of NV-Q's term evaluates to `B.t`. -/
theorem ev_eT : SrcEval (evalEnvOf view cfg P) eT cT := by
  have hl : SrcEval (evalEnvOf view cfg P)
      (mkAppN (.const `Quot.lift [l1, l1]) [tBB, cR, tBB, idF, .const `hR [], qa].toArray) idB :=
    SrcEval.quotLift (qv := QuotLift_val) (qv' := QuotMk_val) rfl rfl ev_lam ev_qa rfl rfl ev_lam
  refine SrcEval.beta (f := mkAppN (.const `Quot.lift [l1, l1])
    [tBB, cR, tBB, idF, .const `hR [], qa].toArray) ?_ hl ev_cT ev_cT
  rintro ⟨c, us, ar, hc, ha, hle⟩
  have hc' : c = `Quot.lift := by
    simp only [Expr.getAppFn, mkAppN, Array.foldl, List.foldl] at hc
    cases hc; rfl
  subst hc'
  have : ar = 6 := by
    simp only [specialArity, evalEnvOf] at ha
    have hf : findDecl P `Quot.lift = some (.quotInfo QuotLift_val) := rfl
    rw [hf] at ha
    simp [quotEvalArity, QuotLift_val] at ha
    exact ha.symm
  subst this
  revert hle
  decide

/-- The final theorem on NV-Q: the program `#erase` emits for
`@Quot.lift (B → B) R (B → B) (fun x => x) hR (Quot.mk R (fun y => y)) B.t` is an untyped λ□
program whose main term evaluates to an erasure of `B.t`, and `B.t` translates to a term
definitionally equal to the input's at each of its types. -/
theorem final :
    ∃ lenv tb vb, p0 = .untyped lenv (some tb) ∧
      Erases EH BH [] (evalEnvOf view cfg P) .nil [] cT vb ∧ LBEval defaultFlags lenv tb vb ∧
      ∀ T, EH[.nil] ⊢ tE : T → ∃ t', TrM EH BH [] .nil [] cT t' ∧ EH[.nil] ⊢ tE ≡ t' : T :=
  erase_correct henv hwf hview he hty hfrag hrun hev

end EraseProof.Test.NVQ
