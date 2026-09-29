import LeanToLambdaBox.Erasure
import LeanToLambdaBox.Erasure.Entry

/-!
# The `#erase` command

`#erase t [config c] [to "f"] [mli "g"]` elaborates `t`, erases it with `Erasure.eraseEntry` over
the elaboration environment, and writes the program to `f` and its attributes to `f.inlinings`
(or logs them), and the OCaml signature of `t`'s type to `g` (or logs it).
-/

open Lean

namespace Erasure

syntax (name := erasestx) "#erase" ppSpace term (ppSpace "config" term)? (ppSpace "to" ppSpace str)? (ppSpace "mli" ppSpace str)?: command

@[command_elab erasestx]
def eraseElab: Elab.Command.CommandElab
  | `(command| #erase $t:term $[config $cfg?:term]? $[to $path?:str]? $[mli $mli?:str]?) => Elab.Command.liftTermElabM do
    let e: Expr ← Elab.Term.elabTerm t (expectedType? := .none)
    Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let e ← Lean.instantiateMVars e

    let cfg: ErasureConfig ← match cfg? with
    | .none => pure {}
    | .some cfg => unsafe Elab.Term.evalTerm ErasureConfig (.const ``Erasure.ErasureConfig []) cfg

    let view := EnvView.ofEnvironment (← getEnv)
    let (p, inls) ← eraseEntry view cfg e
    let s: String := p |> Serialize.to_sexpr |>.toString
    -- logInfo s!"{repr p}"
    match path? with
    | .some path => do
        IO.FS.writeFile path.getString s
    | .none => logInfo s

    let c: AttributesConfig := { inlinings := inls, constRemappings := [], indRemappings := [], cstrReorders := [], customAttributes := [] }
    let c_s := c |> Serialize.to_sexpr |>.toString
    match path? with
    | .some path => do
        IO.FS.writeFile (path.getString ++ ".inlinings") c_s
    | .none => logInfo s

    let ty: Expr ← Meta.inferType e
    let mlistr ← gen_mli ty
    match mli? with
    | .none => logInfo mlistr
    | .some mlipath => IO.FS.writeFile mlipath.getString mlistr

  | _ => Elab.throwUnsupportedSyntax

end Erasure
