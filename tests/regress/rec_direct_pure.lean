import LeanToLambdaBox

/-!
The fixpoint of a recursor reduces its `case` itself (`direct`) only if the declared sort of the
major premise's inductive may be `Prop` and the oracle's level of the major premise's type may be
zero (register entry S-58). The input is ill-typed, so `#erase` cannot elaborate it; the test runs
`collectDeps` and `erasePure` on it and writes the output in the format of `#erase`:
`@RD.S.rec.{1} (fun _ => RD.S) (fun h => RD.S.mk h) True.intro`, where `RD.S : Type` has one
constructor with a field of type `True`, and the major premise is a proof of `True`, not an `RD.S`.
The program is in the fragment, and `recDirect.ast` has the fixpoint over a `case`.
-/

-- peregrine: validate recDirect.ast

open Lean Erasure

namespace RD
inductive S : Type
  | mk : True → S
end RD

/-- `@RD.S.rec.{1} (fun _ => RD.S) (fun h => RD.S.mk h) True.intro`. -/
def recDirect : Expr :=
  let S : Expr := .const ``RD.S []
  mkAppN (.const ``RD.S.rec [1])
    #[.lam `t S S .default, .lam `h (.const ``True []) (.app (.const ``RD.S.mk []) (.bvar 0)) .default,
      .const ``True.intro []]

#eval show CoreM Unit from do
  let view := EnvView.ofEnvironment (← getEnv)
  match collectDeps view {} recDirect >>= fun decls => erasePure view {} decls recDirect with
  | .ok (p, _) => IO.FS.writeFile "recDirect.ast" (p |> Serialize.to_sexpr |>.toString)
  | .error _ => throwError "recDirect: the pure path fails"
