import LeanToLambdaBox.TypedML
import LeanToLambdaBox.Basic
import Batteries.CodeAction

def expressionToLambdaBox
  (e: TypedML.Expression cfg globals inductives locals)
  (hConstructors: cfg.constructors = .applied)
  : Except String LBTerm
  := do
  match e with
  | .box => return .box
  | .global id => throw "globals not yet implemented"
  | .local id => return (.bvar id.deBruijnIndex)
  | .constructorVal h cid => (show False by rewrite [hConstructors] at h; contradiction).elim
  | .constructorApp h cid args => throw "constructors not yet implemented"
  | .app f x => return .app (← expressionToLambdaBox f hConstructors) (← expressionToLambdaBox x hConstructors)
  | .lambda name ext body => return .lambda name (← expressionToLambdaBox body hConstructors)

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
  : Except String GlobalDeclarations
  := do
  match p with
  | .empty => return []
  | .valueDecl p name ext val t => return (name, .constantDecl ⟨.some (← expressionToLambdaBox val hConstructors)⟩) :: (← programToLambdaBox p hConstructors)
  | .typeAlias _p _name ext tvarnames t => throw "type aliases not yet implemented"
  | .mutualInductiveDecl p ext minds => return (mutualInductiveDeclToLambdaBox minds) :: (← programToLambdaBox p hConstructors)
