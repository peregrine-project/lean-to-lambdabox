import LeanToLambdaBox.Config
import LeanToLambdaBox.Contexts
import LeanToLambdaBox.Utils
import LeanToLambdaBox.Names

namespace TypedML

structure TypeVarInfo where
  name: TypeVarName
  isLogical: Bool
  isArity: Bool
  isSort: Bool

inductive TypeFormerId (aliases: TypeAliasContext) (inductives: InductiveContext): Type where
  | «alias» (id: aliases.Id)
  | «inductive» (id: inductives.InductiveId mid)

namespace TypeFormerId

def arity: TypeFormerId aliases inductives -> Nat
| .alias id => id.arity
| @TypeFormerId.inductive _ _ mid _ => mid.typeFormerArity

def weaken (aext: aliases.MultiExtension aliases') (iext: inductives.MultiExtension inductives'): TypeFormerId aliases inductives -> TypeFormerId aliases' inductives'
| .alias id => .alias (aext.weakenId id)
| .inductive id => .inductive (iext.weakenInductiveId id)

theorem weaken_arity: arity (i.weaken aext iext) = arity i :=
  match i with
  | .alias _ => TypeAliasContext.MultiExtension.weakenId_arity
  | .inductive _ => InductiveContext.MultiExtension.weakenMutualInductiveId_typeFormerArity

end TypeFormerId

inductive TType (tvars: TypeVarContext) (aliases: TypeAliasContext) (inductives: InductiveContext): Type where
  | typeVar (id: tvars.Id)
  | typeFormerApp (id: TypeFormerId aliases inductives) (args: SizedList (TType tvars aliases inductives) id.arity)
  | arrow (dom codom: TType tvars aliases inductives)
  /-- The type of data which is erased. -/
  | erased
  /-- Any type which is not representable. -/
  | unrepresentable

mutual
inductive Expression (cfg: Config) (globals: GlobalValueContext) (inductives: InductiveContext): LocalValueContext -> Type where
  | box: Expression cfg globals inductives locals
  | global (id: globals.Id): Expression cfg globals inductives locals
  | local (id: locals.Id): Expression cfg globals inductives locals
  | constructorVal
      (h: cfg.constructors = .value)
      (cid: @inductives.ConstructorId mid iid)
    : Expression cfg globals inductives locals
  | constructorApp
      (h: cfg.constructors = .applied)
      (cid: @inductives.ConstructorId mid iid)
      (args: ExpressionSizedList cfg globals inductives locals cid.arity)
    : Expression cfg globals inductives locals
  | app (f x: Expression cfg globals inductives locals): Expression cfg globals inductives locals
  | lambda
      (name: LocalName)
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

structure ConstructorDecl (tvars: TypeVarContext) (aliases: TypeAliasContext) (inductives: InductiveContext) (arity: Nat): Type where
  name: ConstructorName
  argTypes: SizedList (TType tvars aliases inductives) arity

structure OneInductiveDecl (tvars: TypeVarContext) (aliases: TypeAliasContext) (inductives: InductiveContext) (arities: OneInductiveArities) where
  name: InductiveName
  constructors: DependentList Nat (ConstructorDecl tvars aliases inductives) arities

structure MutualInductiveDecl (tvars: TypeVarContext) (aliases: TypeAliasContext) (inductives: InductiveContext) (arities: MutualInductiveArities) where
  name: MutualInductiveName
  npars: Nat
  inductives: DependentList OneInductiveArities (OneInductiveDecl tvars aliases inductives) arities

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
      (name: GlobalName)
      (ext: globals.Extension newglobals)
      (val: Expression cfg globals inductives .empty)
      (tvarnames: tvars.Map TypeVarName)
      (t: TType tvars aliases inductives)
    : Program cfg aliases newglobals inductives 
  /--
  Note: the order in which type variables were added to the type var context matters,
  since TType.typeFormerApp takes an ordered SizedList of arguments.
  -/
  | typeAlias
      (p: Program cfg aliases globals inductives)
      (name: TypeAliasName)
      (ext: aliases.Extension newaliases tvars.size)
      (tvarinfo: tvars.Map TypeVarInfo)
      (t: TType tvars aliases inductives)
    : Program cfg newaliases globals inductives
  | mutualInductiveDecl
      (p: Program cfg aliases globals inductives)
      (ext: inductives.Extension newinductives { typeVarCount := tvars.size, arities })
      (minds: MutualInductiveDecl tvars aliases newinductives arities)
    : Program cfg aliases globals newinductives

end TypedML

namespace LocalValueContext.Extension
open TypedML

mutual
def weakenExpression (ext: ctx.Extension ctx'): Expression cfg globals inductives ctx -> Expression cfg globals inductives ctx'
| .box => .box
| .global id => .global id
| .local id => .local (ext.weakenId id)
| .constructorVal h cid => .constructorVal h cid
| .constructorApp h cid args => .constructorApp h cid (ext.weakenExpressions args)
| .app f x => .app (weakenExpression ext f) (weakenExpression ext x)
| .lambda name bext body =>
  let ⟨_, ⟨addprime, addb⟩⟩ := bext.pullback ext;
  .lambda name addb (weakenExpression addprime body)

/-- Here we do the mapping directly, instead of converting back and forth and using SizedList.map, so that the termination checker sees this is structural. -/
def weakenExpressions (ext: ctx.Extension ctx'): ExpressionSizedList cfg globals inductives ctx n -> ExpressionSizedList cfg globals inductives ctx' n
  | .nil => .nil
  | .cons n e es => .cons n (weakenExpression ext e) (weakenExpressions ext es)
end

end LocalValueContext.Extension

namespace ProgramContext.MultiExtension
open TypedML

mutual
def weakenExpression (ext: MultiExtension pctx pctx'): Expression cfg pctx.globals pctx.inductives locals -> Expression cfg pctx'.globals pctx'.inductives locals
| .box => .box
| .global id => .global (ext.globals.weakenId id)
| .local id => .local id
| .constructorVal h cid => .constructorVal h (ext.inductives.weakenConstructorId cid)
| .constructorApp h cid args =>
  .constructorApp h (ext.inductives.weakenConstructorId cid) (InductiveContext.MultiExtension.weakenConstructorId_arity.symm ▸ ext.weakenExpressions args)
| .app f x => .app (ext.weakenExpression f) (ext.weakenExpression x)
| .lambda name bext body => .lambda name bext (ext.weakenExpression body)

/-- Here we do the mapping directly, instead of converting back and forth and using SizedList.map, so that the termination checker sees this is structural. -/
def weakenExpressions (ext: MultiExtension pctx pctx'): ExpressionSizedList cfg pctx.globals pctx.inductives locals n -> ExpressionSizedList cfg pctx'.globals pctx'.inductives locals n
| .nil => .nil
| .cons n e es => .cons n (ext.weakenExpression e) (ext.weakenExpressions es)
end

mutual
def weakenType (pext: MultiExtension pctx pctx') (text: tvars.MultiExtension tvars'): TType tvars pctx.aliases pctx.inductives -> TType tvars' pctx'.aliases pctx'.inductives
| .typeVar id => .typeVar (text.weakenId id)
| .typeFormerApp id args => .typeFormerApp (id.weaken pext.aliases pext.inductives) (TypeFormerId.weaken_arity.symm ▸ weakenTypes pext text args)
| .arrow dom codom => .arrow (pext.weakenType text dom) (pext.weakenType text codom)
| .erased => .erased
| .unrepresentable => .unrepresentable

def weakenTypes (pext: MultiExtension pctx pctx') (text: tvars.MultiExtension tvars'): SizedList (TType tvars pctx.aliases pctx.inductives) n -> SizedList (TType tvars' pctx'.aliases pctx'.inductives) n
| .nil => .nil
| .cons _ t ts => .cons _ (weakenType pext text t) (weakenTypes pext text ts)
end

end ProgramContext.MultiExtension
