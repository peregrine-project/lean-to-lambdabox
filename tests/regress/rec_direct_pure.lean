import LeanToLambdaBox

/-!
The fixpoint of a recursor reduces its `case` itself (`direct`) only if the declared sort of the
major premise's inductive may be `Prop` and the oracle's level of the major premise's type may be
zero (register entries S-58, S-59). The declared sort is read through `mdata`: in the second
program the type of `RD.M` is `mdata Type`, and the case is kept as for `RD.S`. The input is ill-typed, so `#erase` cannot elaborate it; the test runs
`collectDeps` and `erasePure` on it and writes the output in the format of `#erase`:
`@RD.S.rec.{1} (fun _ => RD.S) (fun h => RD.S.mk h) True.intro`, where `RD.S : Type` has one
constructor with a field of type `True`, and the major premise is a proof of `True`, not an `RD.S`.
The program is in the fragment, and `recDirect.ast` has the fixpoint over a `case`.
-/

-- peregrine: validate recDirect.ast
-- peregrine: validate recDirectMData.ast

open Lean Erasure

namespace RD
inductive S : Type
  | mk : True → S
inductive M : Type
  | mk : True → M
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

/-- `@RD.M.rec.{1} (fun _ => RD.M) (fun h => RD.M.mk h) True.intro`, with `mdata` on the type of
`RD.M`. -/
def recDirectMData : Expr :=
  let M : Expr := .const ``RD.M []
  mkAppN (.const ``RD.M.rec [1])
    #[.lam `t M M .default, .lam `h (.const ``True []) (.app (.const ``RD.M.mk []) (.bvar 0)) .default,
      .const ``True.intro []]

#eval show CoreM Unit from do
  let view := EnvView.ofEnvironment (← getEnv)
  let view := { view with find? := fun n => (view.find? n).map fun
    | .inductInfo iv => if iv.name == ``RD.M then .inductInfo { iv with type := .mdata {} iv.type } else .inductInfo iv
    | ci => ci }
  match collectDeps view {} recDirectMData >>= fun decls => erasePure view {} decls recDirectMData with
  | .ok (p, _) => IO.FS.writeFile "recDirectMData.ast" (p |> Serialize.to_sexpr |>.toString)
  | .error _ => throwError "recDirectMData: the pure path fails"
