import LeanToLambdaBox.TypedML
import LeanToLambdaBox.Basic
import Batteries.CodeAction

structure NameContext (aliases: TypeAliasContext) (globals: GlobalValueContext) (inductives: InductiveContext) where
  aliases: aliases.Map TypeAliasName
  globals: globals.Map GlobalName
  inductives: inductives.Map MutualInductiveName

def NameContext.empty: NameContext .empty .empty .empty where
  aliases := .empty
  globals := .empty
  inductives := .empty

unseal GlobalName in
def expressionToLambdaBox
  (e: TypedML.Expression cfg globals inductives locals)
  (names: NameContext aliases globals inductives)
  (hConstructors: cfg.constructors = .applied)
  : Except String LBTerm
  := do
  match e with
  | .box => return .box
  | .global id => return .const (names.globals.get id)
  | .local id => return (.bvar id.deBruijnIndex)
  | .constructorVal h cid => (show False by rewrite [hConstructors] at h; contradiction).elim
  | .constructorApp h cid args => throw "constructors not yet implemented"
  | .app f x => return .app (← expressionToLambdaBox f names hConstructors) (← expressionToLambdaBox x names hConstructors)
  | .lambda name ext body => return .lambda name (← expressionToLambdaBox body names hConstructors)

unseal ConstructorName in
def constructorDeclToLambdaBox (decl: TypedML.ConstructorDecl tvars formers arity): ConstructorBody :=
  {
    name := decl.name,
    nargs := arity,
  }

unseal InductiveName in
def oneInductiveDeclToLambdaBox (decl: TypedML.OneInductiveDecl tvars formers arities): OneInductiveBody :=
  { name := decl.name,
    ctors : List ConstructorBody := decl.constructors.map (fun _ => constructorDeclToLambdaBox) |>.forget,
    projs : List ProjectionBody := [],
  }

unseal MutualInductiveName in
def mutualInductiveDeclToLambdaBox (minds: TypedML.MutualInductiveDecl tvars formers arities): Kername × GlobalDecl :=
  (minds.name, .inductiveDecl { bodies := minds.inductives.map (fun _ => oneInductiveDeclToLambdaBox) |>.forget, npars := minds.npars } )

unseal GlobalName in
def programToLambdaBox
  (p: TypedML.Program cfg aliases globals inductives)
  (hConstructors: cfg.constructors = .applied)
  : Except String (GlobalDeclarations × NameContext aliases globals inductives)
  := do
  match p with
  | .empty => return ([], .empty)
  | .valueDecl p name ext val t =>
    let (decls, names) ← programToLambdaBox p hConstructors;
    let value ← expressionToLambdaBox val names hConstructors;
    return ((name, .constantDecl ⟨.some value⟩) :: decls, { names with globals := names.globals.extend name ext })
  | .typeAlias _p _name ext tvarnames t => throw "type aliases not yet implemented"
  | .mutualInductiveDecl p ext minds =>
    let (decls, names) ← programToLambdaBox p hConstructors;
    return ((mutualInductiveDeclToLambdaBox minds) :: decls, { names with inductives := names.inductives.extend minds.name ext })
