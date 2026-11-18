import LeanToLambdaBox

/-!
# NV-0: the program

    def nv0id.{u} (α : Sort u) (a : α) : α := a
    def nv0main : (α : Type) → α → α := nv0id ((α : Type) → α → α) (fun α a => a)
    #erase nv0main            -- the type argument of nv0id is erased (□)

The declarations as Lean v4.35.0 generates them (`tools/NVEmit.lean` checks them against the elaborator's):
`P = [nv0main, nv0id]`, the term `e`, the view `#erase` reads and the default configuration.
`Test/NV0Premises.lean` discharges the hypotheses of the final theorem on it.
-/

open Lean Erasure

namespace EraseProof.Test.NV0

/-! ## The program -/

/-- `(α : Type) → α → α` -/
def tT : Expr := .forallE `α (.sort 1) (.forallE `a (.bvar 0) (.bvar 1) .default) .default
/-- `fun (α : Sort s) (a : α) => a` -/
def idLam (s : Level) : Expr := .lam `α (.sort s) (.lam `a (.bvar 0) (.bvar 0) .default) .default
/-- `fun α a => a`, the argument of `nv0id` in `nv0main` -/
def idT : Expr := idLam 1

def id_def : DefinitionVal :=
  { name := `nv0id, levelParams := [`u],
    type := .forallE `α (.sort (.param `u)) (.forallE `a (.bvar 0) (.bvar 1) .default) .default,
    value := idLam (.param `u), hints := .regular 1, safety := .safe, all := [`nv0id] }

/-- `nv0main`'s value `nv0id.{2} T idT` -/
def mainVal : Expr := .app (.app (.const `nv0id [.succ (.succ .zero)]) tT) idT

def main_def : DefinitionVal :=
  { name := `nv0main, levelParams := [], type := tT, value := mainVal,
    hints := .regular 2, safety := .safe, all := [`nv0main] }

/-- The program, newest first. -/
def P : List ConstantInfo := [.defnInfo main_def, .defnInfo id_def]

/-- The erased term. -/
def e : Expr := .const `nv0main []

/-- The view `#erase` reads: `P` as a list, no attributes. -/
def view : EnvView where
  find? := Erasure.findConst P
  isExtern _ := false
  inlineAttr? _ := none
  implementedBy? _ := none

/-- The default configuration. -/
def cfg : ErasureConfig := {}

end EraseProof.Test.NV0
