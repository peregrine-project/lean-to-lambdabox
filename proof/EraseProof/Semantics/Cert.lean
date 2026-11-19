import EraseProof.Semantics.Frozen
import EraseProof.Statements
import ConLeche.Model.Rules.RedSound
import ConLeche.Model.CtxOkKit
import ConLeche.Semantics.Frame

/-!
# The proof verdict of a certificate denotes the proof point

`CLCert` certifies a marked subterm `s` under its binders `Γ` through con-leche's inference on the
closed telescope `lamTele Γ s` and on `s` opened at the depth its binders reach (`openLams`). Its
proof verdict (`CLProof`) means that the telescope denotes the proof point in every model: the
opened subterm denotes the point under every valuation of its binders that satisfies their
domains, a λ whose body is the point on its whole domain is the point, and a `let` is read at its
value.
-/

open Lean Erasure
open ConLeche.Semantics ConLeche.SetModel ConLeche.SetTheory ConLeche.Verify ConLeche.Model
  ConLeche.Model.Rules

namespace EraseProof

universe w

variable {env : ConLeche.Env}

/-- A reading con-leche types as a proof (`CLProof`) at depth `d` denotes the proof point at every
valuation that satisfies its context and grades its leaves: `proof_pt` at depth `d`, with the
context of the subject (`CL ConLeche/Model/Rules/Motive.lean:174 InferSemFull`) carried to its
type and its type's type by their leaf inclusions. Reference: none (DV-32). -/
theorem proof_ptAt {V : Type w} [ConLeche.SetTheory V] (m : EnvModelM V env)
    (φ : ConLeche.Name → Nat) {F d : Nat} {c T : ConLeche.Expr}
    (h : ConLeche.inferTypeCore .verified false env F d c = .ok T) (hpr : CLProof env F d T)
    (hfc : Frame d c) {Δa : List ConLeche.Term.Term} {ea : ConLeche.Term.Term}
    (hC : CtxOkS m.base2 φ d Δa c) (hea : denote m.base2.acval env φ d c = some ea)
    (ρ : Nat → V) (hρ : Sat V Δa ρ) (hL : LeavesGr m.base2 φ d c ρ) : interp V ρ ea = pt := by
  obtain ⟨S, u, hS, hw, hz⟩ := hpr
  have hin := Rules.RulesInputs.ofSem m φ
  obtain ⟨hfT, hsT, ta, hta, hcs⟩ :=
    infer_sound hin (ConLeche.Rules.inferTypeCore_bridge h) hfc hC hea
  have hCT := hC.of_subset hsT
  obtain ⟨hfS, hsS, sa, hsa, hTs⟩ :=
    infer_sound hin (ConLeche.Rules.inferTypeCore_bridge hS) hfT hCT hta
  obtain ⟨-, -, ua, hua, hsu⟩ :=
    red_sound hin (ConLeche.Rules.whnf_bridge hw) hfS (hCT.of_subset hsS) hsa
  simp only [denote, Option.some.injEq] at hua
  subst hua
  have hLT := hL.of_subset hsT
  obtain ⟨-, -, hmem⟩ := hcs ρ hρ hL
  obtain ⟨-, hwsa, hTmem⟩ := hTs ρ hρ hLT
  obtain ⟨-, hseq⟩ := hsu ρ hρ (hLT.of_subset hsS) hwsa.1 hwsa.2.ne_pt
  rw [hseq, interp_sort, SemCases.eval_of_isAlwaysZero hz, univ_zero] at hTmem
  exact eq_pt_of_mem_univZero hTmem hmem

/-- Opening the binders of a graded reading as con-leche's inference does (`openLams`) down to a
subterm typed as a proof: the reading denotes the proof point. A λ is opened at a fresh variable
of its domain (`CL ConLeche/Model/CtxOkKit.lean:365 CtxOkS.openS`, `:471 LeavesGr.open`), whose
body is then the point at every member of the domain, so the λ is the point
(`CL ConLeche/SetModel/Ops.lean:304 lamV_eq_pt`); a `let` reads as its body at its value
(`CL ConLeche/Model/Rules/RedSound.lean:238 Red.zeta_soundU`). Reference: none (DV-32). -/
theorem openLams_pt {V : Type w} [ConLeche.SetTheory V] (m : EnvModelM V env)
    (φ : ConLeche.Name → Nat) {d' : Nat} {c' T : ConLeche.Expr}
    (h : ConLeche.inferTypeCore .verified false env ConLeche.checkFuel d' c' = .ok T)
    (hpr : CLProof env ConLeche.checkFuel d' T) :
    ∀ (k d : Nat) (t : ConLeche.Expr), openLams d k t = some (d', c') → Frame d t →
      ∀ {Δa : List ConLeche.Term.Term} {ta : ConLeche.Term.Term},
        CtxOkS m.base2 φ d Δa t → denote m.base2.acval env φ d t = some ta →
        ∀ ρ : Nat → V, Sat V Δa ρ → LeavesGr m.base2 φ d t ρ → WellDenoted V ρ ta →
          interp V ρ ta = pt
  | 0, d, t, hop => by
    intro hf _ _ hC hta ρ hρ hL _
    simp only [openLams, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop
    exact proof_ptAt m φ h hpr hf hC hta ρ hρ hL
  | k + 1, d, .lam A b, hop => by
    intro hf _ _ hC hta ρ hρ hL hwd
    obtain ⟨tyA, ba, htyA, hba, rfl⟩ := denote_lam_inv hta
    obtain ⟨hws, hb, hLb⟩ := hf
    simp only [ConLeche.Expr.WScoped] at hws
    simp only [ConLeche.Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    have hfo := frame_open2 hws.1 hb.1 hws.2 hb.2
      (fun l hl => hLb l (by simp [ConLeche.Expr.fvarLeaves, hl]))
      (fun l hl => hLb l (by simp [ConLeche.Expr.fvarLeaves, hl]))
    rw [WellDenoted_lam] at hwd
    rw [interp_lam]
    exact lamV_eq_pt fun x hx => openLams_pt m φ h hpr k (d + 1) _ hop hfo
      (CtxOkS.openS hC.lam_ty hC.lam_body htyA) hba (cons x ρ) (Sat_cons V hρ hx)
      (LeavesGr.open hC.lam_ty hC.lam_body hL.lam_ty hL.lam_body htyA ⟨hwd.1, hwd.2.1⟩)
      (hwd.2.2 x hx)
  | k + 1, d, .letE A v b, hop => by
    intro hf _ _ hC hta ρ hρ hL hwd
    obtain ⟨hfr, hsub, ta', hred, hsem⟩ :=
      Red.zeta_soundU (m := m.base2) (φ := φ) (ty := A) (v := v) (body := b) hf hC hta
    obtain ⟨hwd', heq⟩ := hsem ρ hρ hL hwd
    rw [heq]
    exact openLams_pt m φ h hpr k d _ hop hfr (hC.of_subset hsub) hred ρ hρ (hL.of_subset hsub)
      hwd'
  | _ + 1, _, .bvar _, hop | _ + 1, _, .fvar _ _, hop | _ + 1, _, .sort _, hop
  | _ + 1, _, .const _ _, hop | _ + 1, _, .app _ _, hop | _ + 1, _, .forallE _ _, hop
  | _ + 1, _, .lit _, hop | _ + 1, _, .proj _ _ _, hop => by simp [openLams] at hop

/-- `clCert_proof_pt`: the proof verdict of a certificate means a proof. The closed telescope is
typed at depth `0`, so its reading exists and is graded in every model (`SemCases.infer0`, with its
closedness from `CLTyped.closed` and `toCL?_hasFvar`); `openLams_pt` from the empty context. The
denotation is the reading's (`SemCases.denotes_iff`). Reference: none (DV-32). -/
theorem clCert_proof_pt : clCert_proof_pt_statement.{w} := by
  intro P env Γ s c c' T₀ T d _ hc h0 hop hT hpr V _ m φ ρ X hX
  have hfv := toCL?_hasFvar hc
  have hb := CLTyped.closed ⟨c, _, _, hc, h0⟩ hc
  obtain ⟨ea, hea, hwd⟩ := SemCases.infer0 m φ h0 hfv hb
  rw [SemCases.denotes_iff m φ ρ hea hfv hb] at hX
  subst hX
  have hnil := ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hfv
  have hnc : ∀ l, l ∉ c.fvarLeaves := fun l hl => by rw [hnil] at hl; cases hl
  exact openLams_pt m φ hT hpr _ 0 c hop
    ⟨ConLeche.Expr.WScoped.of_not_hasFvar hfv, hb, fun l hl => absurd hl (hnc l)⟩
    (SemCases.ctx0 m φ hnc).1 hea ρ (Sat_nil V ρ) ((SemCases.ctx0 m φ hnc).2 ρ) (hwd ρ)

end EraseProof
