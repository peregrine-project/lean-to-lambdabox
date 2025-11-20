import LeanToLambdaBox.TypedML
import LeanToLambdaBox.Basic
import Batteries.CodeAction

structure NameContext (aliases: TypeAliasContext) (globals: GlobalValueContext) (inductives: InductiveContext) where
  aliases: aliases.Map TypeAliasName
  globals: globals.Map GlobalName
  inductives: inductives.Map MutualInductiveName

-- This Inhabited instance should only be necessary while there are still panics for unimplemented bits.
unseal TypeAliasContext.Map in
unseal GlobalValueContext in
unseal GlobalValueContext.Map in
unseal InductiveContext.Map in
instance: Inhabited (NameContext aliases globals inductives) where
  default := {
    aliases := show Vector _ _ from default,
    globals := show Vector _ _ from default,
    inductives := show Vector _ _ from default,
  }

def NameContext.empty: NameContext .empty .empty .empty where
  aliases := .empty
  globals := .empty
  inductives := .empty

unseal GlobalName in
def expressionToLambdaBox
  (e: TypedML.Expression cfg globals inductives locals)
  (names: NameContext aliases globals inductives)
  (hConstructors: cfg.constructors = .applied)
  : LBTerm
  :=
  match e with
  | .box => .box
  | .global id => .const (names.globals.get id)
  | .local id => (.bvar id.deBruijnIndex)
  | .constructorVal h cid => (show False by rewrite [hConstructors] at h; contradiction).elim
  | .constructorApp h cid args => panic! "constructors not yet implemented"
  | .app f x => .app (expressionToLambdaBox f names hConstructors) (expressionToLambdaBox x names hConstructors)
  | .lambda name ext body => .lambda name (expressionToLambdaBox body names hConstructors)

unseal ConstructorName in
def constructorDeclToLambdaBox (decl: TypedML.ConstructorDecl tvars aliases inductives arity): ConstructorBody :=
  {
    name := decl.name,
    args := panic! "constructors not yet implemented",
    originalArity := panic! "constructors not yet implemented",
  }

unseal InductiveName in
def oneInductiveDeclToLambdaBox (decl: TypedML.OneInductiveDecl tvars aliases inductives arities): OneInductiveBody :=
  { name := decl.name,
    typeVars := panic! "inductive types not yet implemented",
    ctors := decl.constructors.map (fun _ => constructorDeclToLambdaBox) |>.forget,
    projs := [],
  }

unseal MutualInductiveName in
def mutualInductiveDeclToLambdaBox (minds: TypedML.MutualInductiveDecl tvars aliases inductives arities): (Kername × Bool) × GlobalDecl :=
  -- assuming has_deps is always true
  ((minds.name, true), .inductiveDecl { bodies := minds.inductives.map (fun _ => oneInductiveDeclToLambdaBox) |>.forget, npars := minds.npars } )

def typeToLambdaBox : TypedML.TType tvars aliases inductives -> LBType
| .erased => .box
| .unrepresentable => .any
| .arrow dom codom => .arr (typeToLambdaBox dom) (typeToLambdaBox codom)
| .typeVar id => .var id.toIndex
| .typeFormerApp (.inductive _iid) _args => panic! "inductive types not yet implemented"
| .typeFormerApp (.alias _id) _args => panic! "type aliases not yet implemented"


unseal GlobalName in
def programToLambdaBox
  (p: TypedML.Program cfg aliases globals inductives)
  (hConstructors: cfg.constructors = .applied)
  : GlobalDeclarations × NameContext aliases globals inductives
  :=
  match p with
  | .empty => ([], .empty)
  | .valueDecl p name ext val t (tvars := tvars) =>
    let (decls, names) := programToLambdaBox p hConstructors;
    let value := expressionToLambdaBox val names hConstructors;
    -- TODO: use real names for type variables somewhere
    let decl := .constantDecl { body := .some value, type := (List.replicate tvars.size .anon , typeToLambdaBox t)};
    -- assuming has_deps is always true
    (((name, true), decl) :: decls, { names with globals := names.globals.extend name ext })
  | .typeAlias _p _name ext tvarnames t => panic! "type aliases not yet implemented"
  | .mutualInductiveDecl p ext minds =>
    let (decls, names) := programToLambdaBox p hConstructors;
    (mutualInductiveDeclToLambdaBox minds :: decls, { names with inductives := names.inductives.extend minds.name ext })
