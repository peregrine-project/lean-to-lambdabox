import LeanToLambdaBox.Config
import LeanToLambdaBox.Contexts
import LeanToLambdaBox.Utils

namespace TypedML

inductive TType (tvars: TypeVarContext) (formers: TypeFormerContext): Type where
  | typeVar (id: tvars.Id)
  | typeFormerApp (id: formers.Id) (args: SizedList (TType tvars formers) (formers.arity id))
  | arrow (dom codom: TType tvars formers)

mutual
inductive Expression (cfg: Config) (globals: GlobalValueContext) (inductives: InductiveContext): LocalValueContext -> Type where
  | public global (id: globals.Id): Expression cfg globals inductives locals
  | public local (varid: locals.Id): Expression cfg globals inductives locals
  | public constructorVal
      (h: cfg.constructors = .value)
      (cid: @inductives.ConstructorId mid iid)
    : Expression cfg globals inductives locals
  | public constructorApp
      (h: cfg.constructors = .applied)
      (cid: @inductives.ConstructorId mid iid)
      (args: ExpressionSizedList cfg globals inductives locals cid.arity)
    : Expression cfg globals inductives locals
  | public app (f x: Expression cfg globals inductives locals): Expression cfg globals inductives locals
  | public lambda
      (ext: locals.Extension bodylocals)
      (body: Expression cfg globals inductives bodylocals)
    : Expression cfg globals inductives locals

/--
This is equivalent to `SizedList (Expression globals inductive locals) length`.
An explicit monomorphic mutual definition is necessary because of Lean's restrictions on nested inductive types.
-/
inductive ExpressionSizedList (cfg: Config) (globals: GlobalValueContext) (inductives: InductiveContext): (locals: LocalValueContext) -> (length: Nat) -> Type where
  | nil: ExpressionSizedList cfg globals inductives locals 0
  | cons
      (n: Nat)
      (e: Expression cfg globals inductives locals)
      (es: ExpressionSizedList cfg globals inductives locals n)
    : ExpressionSizedList cfg globals inductives locals (n+1)
end

namespace ExpressionSizedList

def toSizedList: ExpressionSizedList cfg globals inductives locals n -> SizedList (Expression cfg globals inductives locals) n 
| .nil => .nil
| .cons n a as => .cons n a (toSizedList as)

def ofSizedList: SizedList (Expression cfg globals inductives locals) n -> ExpressionSizedList cfg globals inductives locals n
| .nil => .nil
| .cons n a as => .cons n a (ofSizedList as)

end ExpressionSizedList

structure ConstructorDecl (tvars: TypeVarContext) (formers: TypeFormerContext) (arity: Nat): Type where
  argTypes: SizedList (TType tvars formers) arity

structure OneInductiveDecl (tvars: TypeVarContext) (formers: TypeFormerContext) (arities: OneInductiveArities) where
  constructors: DependentList Nat (ConstructorDecl tvars formers) arities

structure MutualInductiveDecl (tvars: TypeVarContext) (formers: TypeFormerContext) (arities: MutualInductiveArities) where
  inductives: DependentList OneInductiveArities (OneInductiveDecl tvars formers) arities

/--
A program made up a sequence of type alias, global value, and inductive type declarations.
The indices are the contexts *provided* by this program.
(One could also define a Program by the contexts *in which* it is valid, like for types and expressions, but this is not what I chose.)
The dependent typing ensures that all names are well-scoped and all constructors and type formers are applied to the right number of arguments.
-/
inductive Program (cfg: Config): TypeAliasContext -> GlobalValueContext -> InductiveContext -> Type where 
  | empty: Program cfg .empty .empty .empty
  | valueDecl
      (p: Program cfg aliases globals inductives)
      (ext: globals.Extension newglobals)
      (val: Expression cfg globals inductives .empty)
      (t: TType tvars (.mk aliases inductives))
    : Program cfg aliases newglobals inductives 
  | typeAlias
      (p: Program cfg aliases globals inductives)
      (ext: aliases.Extension newaliases tvars.size)
      (t: TType tvars (.mk aliases inductives))
    : Program cfg newaliases globals inductives
  | mutualInductiveDecl
      (p: Program cfg aliases globals inductives)
      (ext: inductives.Extension newinductives { typeVarCount := tvars.size, arities })
      (minds: MutualInductiveDecl tvars (.mk aliases newinductives) arities)
    : Program cfg aliases globals newinductives

structure BundledProgram (cfg: Config): Type where
  aliases: TypeAliasContext
  globals: GlobalValueContext
  inductives: InductiveContext
  program: Program cfg aliases globals inductives

end TypedML

namespace LocalValueContext.Extension
open TypedML

mutual
def weakenExpression (ext: ctx.Extension ctx'): Expression cfg globals inductives ctx -> Expression cfg globals inductives ctx'
| .global id => .global id
| .local id => .local (ext.weakenId id)
| .constructorVal h cid => .constructorVal h cid
| .constructorApp h cid args => .constructorApp h cid (ext.weakenExpressions args)
| .app f x => .app (weakenExpression ext f) (weakenExpression ext x)
| .lambda bext body =>
  let ⟨_, ⟨addprime, addb⟩⟩ := bext.pullback ext;
  .lambda addb (weakenExpression addprime body)

/-- Here we do the mapping directly, instead of converting back and forth and using SizedList.map, so that the termination checker sees this is structural. -/
def weakenExpressions (ext: ctx.Extension ctx'): ExpressionSizedList cfg globals inductives ctx n -> ExpressionSizedList cfg globals inductives ctx' n
  | .nil => .nil
  | .cons n e es => .cons n (weakenExpression ext e) (weakenExpressions ext es)
end

end LocalValueContext.Extension

namespace ProgramContext.MultiExtension
open TypedML

mutual
def weakenExpression (ext: @MultiExtension pctx pctx'): Expression cfg pctx.globals pctx.inductives locals -> Expression cfg pctx'.globals pctx'.inductives locals
| .global id => .global (ext.globals.weakenId id)
| .local id => .local id
| .constructorVal h cid => .constructorVal h (ext.inductives.weakenConstructorId cid)
| .constructorApp h cid args =>
  .constructorApp h (ext.inductives.weakenConstructorId cid) (InductiveContext.MultiExtension.weakenConstructorId_arity.symm ▸ ext.weakenExpressions args)
| .app f x => .app (ext.weakenExpression f) (ext.weakenExpression x)
| .lambda bext body => .lambda bext (ext.weakenExpression body)

/-- Here we do the mapping directly, instead of converting back and forth and using SizedList.map, so that the termination checker sees this is structural. -/
def weakenExpressions (ext: @MultiExtension pctx pctx'): ExpressionSizedList cfg pctx.globals pctx.inductives locals n -> ExpressionSizedList cfg pctx'.globals pctx'.inductives locals n
  | .nil => .nil
  | .cons n e es => .cons n (ext.weakenExpression e) (ext.weakenExpressions es)
end
end ProgramContext.MultiExtension
