import LeanToLambdaBox.TypedML
import LeanToLambdaBox.Basic
import Batteries.CodeAction

structure NameContext (aliases: TypeAliasContext) (globals: GlobalValueContext) (inductives: InductiveContext) where
  aliases: aliases.Map TypeAliasName
  globals: globals.Map GlobalName
  -- thankfully, in λbox individual inductive types are identified by their index in a mutual block, otherwise this would have to be a dependent map
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

unseal TypeAliasName in
partial def typeToLambdaBox (names: NameContext aliases globals inductives): TypedML.TType tvars aliases inductives -> LBType
| .erased => .box
| .unrepresentable => .any
| .arrow dom codom => .arr (typeToLambdaBox names dom) (typeToLambdaBox names codom)
| .typeVar id => .var id.toIndex
| .typeFormerApp (.inductive _iid) _args => panic! "inductive types not yet implemented"
| .typeFormerApp (.alias id) args => args.toList.map (typeToLambdaBox names) |>.foldl (LBType.app) (LBType.const (names.aliases.get id))

unseal ConstructorName in
def constructorDeclToLambdaBox (names: NameContext aliases globals inductives) (decl: TypedML.ConstructorDecl tvars aliases inductives arity): ConstructorBody where
  name := decl.name
  args := decl.args.toList.map (fun argInfo => (argInfo.name, typeToLambdaBox names argInfo.type))
  originalArity := arity -- does MetaRocq expect this to include parameters or not?

unseal TypeVarName in
def typeVarInfoToLambdaBox (info: TypedML.TypeVarInfo): TypeVarInfo := { info with }

unseal InductiveName in
def oneInductiveDeclToLambdaBox (names: NameContext aliases globals inductives) (decl: TypedML.OneInductiveDecl aliases inductives spec): OneInductiveBody :=
  { name := decl.name,
    typeVars := decl.tvarinfo.toList.map typeVarInfoToLambdaBox
    ctors := decl.constructors.map (fun _ => constructorDeclToLambdaBox names) |>.forget,
    projs := [],
  }

unseal MutualInductiveName in
def mutualInductiveDeclToLambdaBox (names: NameContext aliases globals inductives) (minds: TypedML.MutualInductiveDecl aliases inductives spec): (Kername × Bool) × GlobalDecl :=
  -- assuming has_deps is always true
  ((minds.name, true), .inductiveDecl { bodies := minds.inductives.map (fun _ => oneInductiveDeclToLambdaBox names) |>.forget, npars := minds.npars } )

unseal GlobalName in
unseal TypeVarName in
unseal TypeAliasName in
def programToLambdaBox
  (p: TypedML.Program cfg aliases globals inductives)
  (hConstructors: cfg.constructors = .applied)
  : GlobalDeclarations × NameContext aliases globals inductives
  :=
  match p with
  | .empty => ([], .empty)
  | .valueDecl p name ext val tvarnames t =>
    let (decls, names) := programToLambdaBox p hConstructors;
    let value := expressionToLambdaBox val names hConstructors;
    let decl := .constantDecl { body := .some value, type := (tvarnames.toList , typeToLambdaBox names t)};
    -- assuming has_deps is always true
    (((name, true), decl) :: decls, { names with globals := names.globals.extend name ext })
  | .typeAlias p name ext tvarinfo t =>
    let (decls, names) := programToLambdaBox p hConstructors;
    let decl: GlobalDecl := .typeAliasDecl <| .some <| (tvarinfo.toList.map typeVarInfoToLambdaBox, typeToLambdaBox names t); 
    (((name, true), decl) :: decls, { names with aliases := names.aliases.extend name ext })
  | .mutualInductiveDecl p ext minds =>
    let (decls, names) := programToLambdaBox p hConstructors;
    let names := { names with inductives := names.inductives.extend minds.name ext };
    (mutualInductiveDeclToLambdaBox names minds :: decls, names)
