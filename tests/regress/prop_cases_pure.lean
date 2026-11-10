import LeanToLambdaBox

/-!
`visitCases` emits no `case` on an inductive with one constructor when the level of the
discriminant's type may be 0 (`Level.isNeverZero` fails: `Prop`, or a universe parameter); the level
comes from the backend's `typeLevel`, which the pure backend computes with the oracle (`Pure.typeLevel`:
the type of the type, after weak-head reduction with the kernel's δ). The test checks:
- `Pure.typeLevel` and `Meta.getLevel` of `Meta.inferType` give the same level on `PUnit.unit` at the
  levels `0`, `u`, `1` and `u + 1`, on proofs of `Eq`, `And` and `Idx`, on `B.t`, and on `myP`, whose
  type's type is `Prop` only after unfolding `MySort`;
- `visitCases` at the pure backend and at `CoreM` erase the same `casesOn` applications to the same
  λ□ terms, without a `case`: `PUnit.casesOn` at the levels `0` and `u` (the alternative itself),
  and `IdxF.casesOn` (the alternative over its index field `f`, which is replaced by the `casesOn`'s
  index argument, applied to □). Its discriminants are not erased. The pure results are written to
  `0.pure.ast`, `1.pure.ast`, `2.pure.ast`, which peregrine validates.
-/

-- peregrine: validate 0.pure.ast
-- peregrine: validate 1.pure.ast
-- peregrine: validate 2.pure.ast

open Lean Elab Command Erasure

namespace PCP
inductive B | f | t
inductive Idx : B → B → Prop | mk (b : B) : Idx .f b
inductive IdxF : B → (Nat → Nat) → Prop | mk (f : Nat → Nat) : IdxF .f f
def MySort : Type := Prop
def MyP : MySort := True
theorem myP : MyP := trivial
end PCP

/-- The declarations of the environment, as the pure backend reads them. -/
def allDecls : CoreM (List ConstantInfo) :=
  return (← getEnv).constants.fold (fun acc _ ci => ci :: acc) []

def u : Level := .param `u

def terms : List (String × Expr) :=
  [("PUnit.unit.{0}", .const ``PUnit.unit [.zero]),
   ("PUnit.unit.{u}", .const ``PUnit.unit [u]),
   ("PUnit.unit.{1}", .const ``PUnit.unit [.succ .zero]),
   ("PUnit.unit.{u + 1}", .const ``PUnit.unit [.succ u]),
   ("rfl", mkApp2 (.const ``Eq.refl [1]) (.const ``PCP.B []) (.const ``PCP.B.t [])),
   ("And.intro", mkApp4 (.const ``And.intro []) (.const ``True []) (.const ``True [])
      (.const ``True.intro []) (.const ``True.intro [])),
   ("Idx.mk", mkApp (.const ``PCP.Idx.mk []) (.const ``PCP.B.t [])),
   ("B.t", .const ``PCP.B.t []),
   ("myP", .const ``PCP.myP [])]

/-- `(term, pure level, Meta level)` for each term of `terms`. -/
def levels : CoreM (List (String × String × String)) := do
  let decls ← allDecls
  terms.mapM fun (n, e) => do
    let p := match Pure.typeLevel ⟨decls⟩ oracleFuel [] e with
      | .ok l => toString l
      | .error _ => "error"
    return (n, p, toString (← runMetaM {} do Meta.getLevel (← Meta.inferType e)))

/--
info: [("PUnit.unit.{0}", "0", "0"), ("PUnit.unit.{u}", "u", "u"), ("PUnit.unit.{1}", "1", "1"),
  ("PUnit.unit.{u + 1}", "u + 1", "u + 1"), ("rfl", "0", "0"), ("And.intro", "0", "0"), ("Idx.mk", "0", "0"),
  ("B.t", "1", "1"), ("myP", "0", "0")]
-/
#guard_msgs in
#eval levels

def natFun : Expr := .forallE `n (.const ``Nat []) (.const ``Nat []) .default
def idNat : Expr := .lam `n (.const ``Nat []) (.bvar 0) .default

/-- `casesOn` applications with the data motive `fun .. => Nat → Nat`. -/
def cases : List (String × Expr) :=
  [("PUnit.{0}", mkApp3 (.const ``PUnit.casesOn [1, .zero]) (.lam `x (.sort .zero) natFun .default)
      (.const ``PUnit.unit [.zero]) idNat),
   ("PUnit.{u}", mkApp3 (.const ``PUnit.casesOn [1, u]) (.lam `x (.sort u) natFun .default)
      (.const ``PUnit.unit [u]) idNat),
   ("IdxF", mkApp5 (.const ``PCP.IdxF.casesOn [1])
      (.lam `b (.const ``PCP.B []) (.lam `f natFun
        (.lam `h (mkApp2 (.const ``PCP.IdxF []) (.bvar 1) (.bvar 0)) natFun .default) .default) .default)
      (.const ``PCP.B.f []) idNat (mkApp (.const ``PCP.IdxF.mk []) idNat)
      (.lam `f natFun (.bvar 0) .default))]

/-- `visitCases` on `e` (a saturated `casesOn` application) at the backend `m`. -/
def visitCasesAt (m : Type → Type) [Monad m] [Backend m] (e : Expr) (ci : CasesInfo) :
    EraseT m LBTerm :=
  visitCases (m := m) travFuel ci e.getAppArgs

/-- `(name, pure result, CoreM result)` for each application of `cases`, as S-expressions; the pure
result is also written to `<i>.pure.ast` as a program without declarations, for the `i`-th. -/
def erased : CoreM (List (String × String × String)) := do
  let decls ← allDecls
  (cases.zipIdx).mapM fun ((n, e), i) => do
    let some ci ← getCasesInfo? e.getAppFn.constName! | throwError "not a casesOn"
    let p ← match (visitCasesAt PureM e ci).runPure {} { «config» := {} }
        ⟨decls, EnvView.ofEnvironment (← getEnv)⟩ {} with
      | .ok ((t, _), _) =>
        IO.FS.writeFile s!"{i}.pure.ast" (ASTType.untyped [] (some t) |> Serialize.to_sexpr |>.toString)
        pure (toString (Serialize.to_sexpr t))
      | .error _ => pure "error"
    let (c, _) ← run (visitCasesAt CoreM e ci) {}
    return (n, p, toString (Serialize.to_sexpr c))

/--
info: [("PUnit.{0}", "(tLambda (nNamed \"n\") (tRel 0))", "(tLambda (nNamed \"n\") (tRel 0))"),
  ("PUnit.{u}", "(tLambda (nNamed \"n\") (tRel 0))", "(tLambda (nNamed \"n\") (tRel 0))"),
  ("IdxF", "(tApp (tLambda (nNamed \"f\") (tLambda (nNamed \"n\") (tRel 0))) tBox)",
    "(tApp (tLambda (nNamed \"f\") (tLambda (nNamed \"n\") (tRel 0))) tBox)")]
-/
#guard_msgs in
#eval erased
