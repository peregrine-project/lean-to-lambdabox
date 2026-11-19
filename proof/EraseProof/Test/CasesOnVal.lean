import EraseProof.Spec
import EraseProof.Test.NV1Run
import EraseProof.Test.NV2Data

/-!
# The marking of `B.casesOn`'s value

`B.casesOn`'s value `fun {motive} t f t_1 => @B.rec motive f t_1 t` is in the closures of NV-1 and
NV-2, so `hcert` asks con-leche to certify a marking of it. Over either closure it is its own
marking, without a mark: the oracle keeps its four λs and the `B.rec` spine, which the eraser does
not leave as a constant (`MarkSat.recr`), and the minor and major premises, free variables whose
types are neither arities nor propositions; the motive is not visited. By kernel evaluation of the
oracle (`krfl`, `Test/Run.lean`).
-/

open Lean Erasure EraseProof EraseProof.Test

namespace EraseProof.Test.NV1

/-- the free variables that open `B.casesOn`'s binders -/
def xc (i : Nat) : FVarId := ⟨.num `_pure i⟩

/-- the locals under `motive`, `t`, `f` and `t_1`, innermost first -/
def lc1 : List Local := [⟨xc 0, `motive, motTy, none⟩]
def lc2 : List Local := ⟨xc 1, `t, tB, none⟩ :: lc1
def lc3 : List Local := ⟨xc 2, `f, .app (.fvar (xc 0)) cF, none⟩ :: lc2
def lc4 : List Local := ⟨xc 3, `t, .app (.fvar (xc 0)) cT, none⟩ :: lc3

/-- `@B.rec.{u} motive f t_1 t` -/
def recApp (m f t₁ t : Expr) : Expr := .app (.app (.app (.app (.const `B.rec [.param `u]) m) f) t₁) t

/-- `B.casesOn`'s value under its first one, two and three binders, opened -/
def cb1 : Expr :=
  .lam `t tB (.lam `f (.app (.fvar (xc 0)) cF) (.lam `t (.app (.fvar (xc 0)) cT)
    (recApp (.fvar (xc 0)) (.bvar 1) (.bvar 0) (.bvar 2)) .default) .default) .default
def cb2 : Expr :=
  .lam `f (.app (.fvar (xc 0)) cF) (.lam `t (.app (.fvar (xc 0)) cT)
    (recApp (.fvar (xc 0)) (.bvar 1) (.bvar 0) (.fvar (xc 1))) .default) .default
def cb3 : Expr :=
  .lam `t (.app (.fvar (xc 0)) cT) (recApp (.fvar (xc 0)) (.fvar (xc 2)) (.bvar 0) (.fvar (xc 1))) .default

/-- A λ the oracle keeps, whose opened body is its own marking, is its own marking. -/
theorem mark_lam_self {decls : List ConstantInfo} {ls : List Local} {n : Name} {A b : Expr}
    {bi : BinderInfo} {x : FVarId} (ho : oracle decls ls (.lam n A b bi) = .ok false)
    (hx : Fresh x ls [b]) (hab : absFV x 0 (b.instantiate1' (.fvar x)) = b)
    (h : MarkOf decls cfg (⟨x, n, A, none⟩ :: ls) (b.instantiate1' (.fvar x))
      (b.instantiate1' (.fvar x))) :
    MarkOf decls cfg ls (.lam n A b bi) (.lam n A b bi) := by
  have := MarkOf.lam ho hx h
  rwa [hab] at this

section
variable {decls : List ConstantInfo} (hd : decls = D ∨ decls = NV2.D)
include hd

/-- The innermost λ of `B.casesOn`'s value, opened under `motive`, `t` and `f`, is its own marking:
its body is the `B.rec` spine (`MarkSat.recr`) on the opened variables. -/
theorem mark_cb3 : MarkOf decls cfg lc3 cb3 cb3 := by
  refine mark_lam_self (x := xc 3) (by rcases hd with rfl | rfl <;> krfl)
    (by simp [Fresh, FVarsIn, lc3, lc2, lc1, motTy, tB, cF, xc, recApp]) (by krfl) ?_
  show MarkOf decls cfg lc4
    (mkAppN (.const `B.rec [.param `u]) [.fvar (xc 0), .fvar (xc 2), .fvar (xc 3), .fvar (xc 1)].toArray)
    (mkAppN (.const `B.rec [.param `u]) [.fvar (xc 0), .fvar (xc 2), .fvar (xc 3), .fvar (xc 1)].toArray)
  refine MarkOf.special (ar := 4) (T := .app (.fvar (xc 0)) (.fvar (xc 1)))
    (by rcases hd with rfl | rfl <;> krfl) (by rcases hd with rfl | rfl <;> krfl)
    (by rcases hd with rfl | rfl <;> krfl) (MarkEta.sat (by decide) ?_)
  refine MarkSat.recr (r := B_rec) (ivs := [B_ind]) (cvs := [Bf_ctor, Bt_ctor]) (ps := [])
    (ms := [.fvar (xc 0)]) (mins := [.fvar (xc 2), .fvar (xc 3)]) (minsM := [.fvar (xc 2), .fvar (xc 3)])
    (is := []) (îs := []) (maj := .fvar (xc 1)) (majM := .fvar (xc 1)) (extra := []) (êxtra := [])
    (by rcases hd with rfl | rfl <;> krfl) (by rcases hd with rfl | rfl <;> krfl)
    (by rcases hd with rfl | rfl <;> krfl) (by rcases hd with rfl | rfl <;> krfl) (by krfl)
    (by krfl) rfl rfl rfl rfl ⟨.succ .zero, by rcases hd with rfl | rfl <;> krfl⟩ rfl ?_ rfl
    (by simp) (MarkOf.fvar (by rcases hd with rfl | rfl <;> krfl)) rfl (by simp)
  intro i x xM h1 h2
  rcases i with _ | _ | i <;> simp at h1 h2 <;> subst h1 h2
  all_goals exact MarkOf.fvar (by rcases hd with rfl | rfl <;> krfl)

/-- `B.casesOn`'s value under `motive` and `t`, opened, is its own marking. -/
theorem mark_cb2 : MarkOf decls cfg lc2 cb2 cb2 := by
  refine mark_lam_self (x := xc 2) (by rcases hd with rfl | rfl <;> krfl)
    (by simp [Fresh, FVarsIn, lc2, lc1, motTy, tB, cT, xc, recApp]) (by krfl) ?_
  exact mark_cb3 hd

/-- `B.casesOn`'s value under `motive`, opened, is its own marking. -/
theorem mark_cb1 : MarkOf decls cfg lc1 cb1 cb1 := by
  refine mark_lam_self (x := xc 1) (by rcases hd with rfl | rfl <;> krfl)
    (by simp [Fresh, FVarsIn, lc1, motTy, tB, cT, cF, xc, recApp]) (by krfl) ?_
  exact mark_cb2 hd

/-- `B.casesOn`'s value is its own marking over NV-1's and NV-2's closures. -/
theorem mark_casesOnVal : MarkOf decls cfg [] casesOnVal casesOnVal := by
  refine mark_lam_self (x := xc 0) (by rcases hd with rfl | rfl <;> krfl)
    (by simp [Fresh, FVarsIn, tB, cT, cF]) (by krfl) ?_
  exact mark_cb1 hd

end

end EraseProof.Test.NV1
