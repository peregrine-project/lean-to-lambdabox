module

public import LeanToLambdaBox.Config
public import LeanToLambdaBox.Contexts
public import LeanToLambdaBox.Utils

namespace TypedML

public inductive TType (tvars: TypeVarContext) (formers: TypeFormerContext): Type where
  | typeVar (id: tvars.Id)
  | typeFormerApp (id: formers.Id) (args: SizedList (TType tvars formers) (formers.arity id))
  | arrow (dom codom: TType tvars formers)

mutual
public inductive Expression (cfg: Config) (globals: GlobalValueContext) (inductives: InductiveContext): LocalValueContext -> Type where
  | public global (locals: LocalValueContext) (id: globals.Id): Expression cfg globals inductives locals
  | public local
      (locals: LocalValueContext)
      (varid: locals.Id)
    : Expression cfg globals inductives locals
  | public constructorVal
      (h: cfg.constructors = .value)
      (locals: LocalValueContext)
      (iid: inductives.InductiveId)
      (cid: inductives.ConstructorId iid)
    : Expression cfg globals inductives locals
  | public constructorApp
      (h: cfg.constructors = .applied)
      (locals: LocalValueContext)
      (iid: inductives.InductiveId)
      (cid: inductives.ConstructorId iid)
      (args: ExpressionSizedList cfg globals inductives locals (inductives.constructorArity cid))
    : Expression cfg globals inductives locals
  | public app
      (locals: LocalValueContext)
      (f x: Expression cfg globals inductives locals)
    : Expression cfg globals inductives locals
  | public lambda
      (locals bodylocals: LocalValueContext)
      (ext: bodylocals.extension locals)
      (body: Expression cfg globals inductives bodylocals)
    : Expression cfg globals inductives locals
/--
This is equivalent to `SizedList (Expression globals inductive locals) length`.
An explicit monomorphic mutual definition is necessary because of Lean's restrictions on nested inductive types.
-/
public inductive ExpressionSizedList (cfg: Config) (globals: GlobalValueContext) (inductives: InductiveContext): (locals: LocalValueContext) -> (length: Nat) -> Type where
  | nil (locals: LocalValueContext): ExpressionSizedList cfg globals inductives locals 0
  | cons
      (locals: LocalValueContext)
      (n: Nat)
      (e: Expression cfg globals inductives locals)
      (es: ExpressionSizedList cfg globals inductives locals n)
    : ExpressionSizedList cfg globals inductives locals (n+1)
end
namespace ExpressionSizedList
public def toSizedList {n} : ExpressionSizedList cfg globals inductives locals n -> SizedList (Expression cfg globals inductives locals) n 
| .nil _ => .nil
| .cons locals n a as => .cons n a (toSizedList as)
public def ofSizedList {n}: SizedList (Expression cfg globals inductives locals) n -> ExpressionSizedList cfg globals inductives locals n
| .nil => .nil locals
| .cons n a as => .cons locals n a (ofSizedList as)
end ExpressionSizedList

namespace LocalValueContext

mutual
-- Noncomputable because of pullback and weakenId
public noncomputable def weakenExpression (ext: ctx'.extension ctx): Expression cfg globals inductives ctx -> Expression cfg globals inductives ctx'
| .global ctx id => .global ctx' id
| .local ctx id => .local ctx' (ctx.weakenId ext id)
| .constructorVal h ctx iid cid => .constructorVal h ctx' iid cid
| .constructorApp h ctx iid cid args => .constructorApp h ctx' iid cid (weakenExpressions ext args) -- `ctx.weakenExpressions` doesn't work but this does??
| .app ctx f x => .app ctx' (weakenExpression ext f) (weakenExpression ext x)
| .lambda ctx bodylocals bext body =>
  let ⟨bodylocals', addprime, addb⟩ := ctx.pullback bodylocals ctx' bext ext;
  .lambda ctx' bodylocals' addb (weakenExpression addprime body)

/-- Here we do the mapping directly, instead of converting back and forth and using SizedList.map, so that the termination checker sees this is structural. -/
public noncomputable def weakenExpressions (ext: ctx'.extension ctx): ExpressionSizedList cfg globals inductives ctx n -> ExpressionSizedList cfg globals inductives ctx' n
  | .nil ctx => .nil ctx'
  | .cons ctx n e es => .cons ctx' n (weakenExpression ext e) (weakenExpressions ext es)
end

end LocalValueContext

public structure ConstructorDecl (tvars: TypeVarContext) (formers: TypeFormerContext) (arity: Nat): Type where
  argTypes: SizedList (TType tvars formers) arity

public structure OneInductiveDecl (tvars: TypeVarContext) (formers: TypeFormerContext) (spec: OneInductiveSpec) where
  constructors: DependentList Nat (ConstructorDecl tvars formers) spec

public structure MutualInductiveDecl (tvars: TypeVarContext) (formers: TypeFormerContext) (spec: MutualInductiveSpec) where
  inductives: DependentList (OneInductiveSpec) (OneInductiveDecl tvars formers) spec

/--
A program made up a sequence of type alias, global value, and inductive type declarations.
The indices are the contexts *provided* by this program.
(One could also define a Program by the contexts *in which* it is valid, like for types and expressions, but this is not what I chose.)
The dependent typing ensures that all names are well-scoped and all constructors and type formers are applied to the right number of arguments.
-/
public inductive Program (cfg: Config): TypeAliasContext -> GlobalValueContext -> InductiveContext -> Type where 
  | empty: Program cfg .empty .empty .empty
  | valueDecl
      (tvars: TypeVarContext)
      (aliases: TypeAliasContext)
      (globals newglobals: GlobalValueContext)
      (ext: newglobals.extension globals)
      (inductives: InductiveContext)
      (p: Program cfg aliases globals inductives)
      (val: Expression cfg globals inductives .empty)
      (type: TType tvars (.mk aliases inductives))
    : Program cfg aliases newglobals inductives 
  | typeAlias
      (tvars: TypeVarContext)
      (aliases newaliases: TypeAliasContext)
      (ext: newaliases.extension aliases)
      (globals: GlobalValueContext)
      (inductives: InductiveContext)
      (p: Program cfg aliases globals inductives)
      (t: TType tvars (.mk aliases inductives))
    : Program cfg newaliases globals inductives
  | mutualInductiveDecl
      (tvars: TypeVarContext)
      (aliases: TypeAliasContext)
      (globals: GlobalValueContext)
      (inductives newinductives: InductiveContext)
      (spec: MutualInductiveSpec)
      (ext: newinductives.multiExtension inductives spec)
      (p: Program cfg aliases globals inductives)
      (minds: MutualInductiveDecl tvars (.mk aliases newinductives) spec)
    : Program cfg aliases globals newinductives

public structure BundledProgram (cfg: Config): Type where
  aliases: TypeAliasContext
  globals: GlobalValueContext
  inductives: InductiveContext
  program: Program cfg aliases globals inductives

end TypedML
