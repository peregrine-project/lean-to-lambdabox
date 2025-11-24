import Batteries.CodeAction
-- Names for things, following MetaRocq's conventions.

abbrev Ident := String
abbrev DirPath := List String

/-- A name used to pretty-print bound variables and type variables. -/
inductive LocalName: Type where
  | named (s: Ident)
  | anon
  deriving Inhabited, Repr

inductive ModPath where
| MPfile  (dp : DirPath)
| MPdot   (mp : ModPath) (id : Ident)
-- MPBound is about functors (in the sense of ML module systems).
deriving Inhabited, Repr

structure Kername where
  mp: ModPath
  id: Ident
deriving Inhabited, Repr

-- TODO: clarify what exactly is legal in which position for `lbox` input.
/-- Remove special characters from a string potentially coming from Lean's very permissive grammar. -/
private def cleanIdent (s : String) : Ident :=
  let escapeChar (c : Char) : String :=
    if c.isAlphanum || c == '_' then toString c
    else "_u" ++ toString c.toNat
  ;
  s.toList.map escapeChar |> String.join

private def toLocalName (n: Lean.Name): Except String LocalName :=
  match n with
  | .anonymous => pure LocalName.anon
  | .str .anonymous str => pure <| .named (cleanIdent str)
  |  _ => pure LocalName.anon -- these cases can be produced by Lean's hygiene system

-- TODO: clarify what lambdabox module paths are used for in `lbox`. Do these names matter? Should there be a sensible dirpath instead of the empty one?
private def toModPath: Lean.Name -> ModPath
  | .str name s => .MPdot (toModPath name) (cleanIdent s)
  | .num name nb => .MPdot (toModPath name) (nb.repr)
  | .anonymous => .MPfile []

/-- Mostly ad hoc conversion function from `Name`s to MetaRocq kernames. -/
private def toKername (n: Lean.Name): Except String Kername :=
  match n with
  | .str name s =>  pure { mp := toModPath name, id := cleanIdent s }
  | .num name nb =>  pure { mp := toModPath name, id := nb.repr }
  | .anonymous => throw "Cannot convert empty name to kername." -- This should not happen.

private def rootKername (s: String): Kername :=
  { mp := .MPfile [], id := cleanIdent s }


-- Following MetaRocq's conventions.
@[irreducible, local semireducible] def TypeVarName: Type := LocalName
@[irreducible, local semireducible] def TypeAliasName: Type := Kername deriving Inhabited
@[irreducible, local semireducible] def GlobalName: Type := Kername deriving Inhabited
@[irreducible, local semireducible] def MutualInductiveName: Type := Kername deriving Inhabited
@[irreducible, local semireducible] def InductiveName: Type := Ident
@[irreducible, local semireducible] def ConstructorName: Type := Ident

namespace Lean.Name
@[irreducible] def toLocalName: Lean.Name -> Except String LocalName := _root_.toLocalName
@[irreducible] def toGlobalName: Lean.Name -> Except String GlobalName := toKername
@[irreducible] def toTypeAliasName: Lean.Name -> Except String TypeAliasName := toKername
@[irreducible] def toTypeVarName: Lean.Name -> Except String TypeVarName := toLocalName
end Lean.Name
