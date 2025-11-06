namespace TypedML

axiom TypeVarContext: Type
axiom TypeVarContext.Id: TypeVarContext -> Type

axiom TypeAliasContext: Type
namespace TypeAliasContext
axiom empty: TypeAliasContext
axiom Id: TypeAliasContext -> Type
axiom arity (ctx: TypeAliasContext): ctx.Id -> Nat
axiom extension: TypeAliasContext -> TypeAliasContext -> Type
end TypeAliasContext

/-- A list of constructor arities. -/
def OneInductiveSpec := List Nat
def MutualInductiveSpec := List OneInductiveSpec

axiom InductiveContext: Type
namespace InductiveContext
axiom empty: InductiveContext
axiom InductiveId: InductiveContext -> Type
axiom inductiveArity (ctx: InductiveContext) (iid: ctx.InductiveId): Nat
axiom ConstructorId (ctx: InductiveContext) (iid: ctx.InductiveId): Type
axiom constructorArity (ctx: InductiveContext) (iid: ctx.InductiveId) (cid: ctx.ConstructorId iid): Nat
axiom multiExtension: InductiveContext -> InductiveContext -> MutualInductiveSpec -> Type
end InductiveContext

structure TypeFormerContext: Type where
  mk ::
  aliases: TypeAliasContext
  inductives: InductiveContext
namespace TypeFormerContext
inductive Id (ctx: TypeFormerContext): Type where
  | alias (id: ctx.aliases.Id)
  | inductive (id: ctx.inductives.InductiveId)
-- noncomputable only because TypeAliasContext.arity and InductiveContext.inductiveArity are axioms atm
noncomputable def arity (ctx: TypeFormerContext): ctx.Id -> Nat
| .alias id => ctx.aliases.arity id
| .inductive id => ctx.inductives.inductiveArity id
end TypeFormerContext

axiom GlobalValueContext: Type
namespace GlobalValueContext
axiom empty: GlobalValueContext
axiom Id: GlobalValueContext -> Type
axiom extension: GlobalValueContext -> GlobalValueContext -> Type
end GlobalValueContext

axiom LocalValueContext: Type
namespace LocalValueContext
axiom empty: LocalValueContext
axiom Id: LocalValueContext -> Type
axiom extension: LocalValueContext -> LocalValueContext -> Type
end LocalValueContext

inductive SizedList (α: Type): (length: Nat) -> Type where
  | nil: SizedList α 0
  | cons: forall n, α -> SizedList α n -> SizedList α (n+1)

inductive TType (tvars: TypeVarContext) (formers: TypeFormerContext): Type where
  | typeVar (id: tvars.Id)
  | typeFormerApp (id: formers.Id) (args: SizedList (TType tvars formers) (formers.arity id))
  | arrow (dom codom: TType tvars formers)

mutual
inductive Expression (globals: GlobalValueContext) (inductives: InductiveContext): LocalValueContext -> Type where
  | global (locals: LocalValueContext) (id: globals.Id): Expression globals inductives locals
  | local
      (locals: LocalValueContext)
      (varid: locals.Id)
    : Expression globals inductives locals
  | constructorApp
      (locals: LocalValueContext)
      (iid: inductives.InductiveId)
      (cid: inductives.ConstructorId iid)
      (args: ExpressionSizedList globals inductives locals (inductives.constructorArity iid cid))
    : Expression globals inductives locals
  | app
      (locals: LocalValueContext)
      (f x: Expression globals inductives locals)
    : Expression globals inductives locals
  | lambda
      (locals bodylocals: LocalValueContext)
      (ext: bodylocals.extension locals)
      (body: Expression globals inductives bodylocals)
    : Expression globals inductives locals
/--
This is equivalent to `SizedList (Expression globals inductive locals) length`.
An explicit monomorphic mutual definition is necessary because of Lean's restrictions on nested inductive types.
-/
inductive ExpressionSizedList (globals: GlobalValueContext) (inductives: InductiveContext): (locals: LocalValueContext) -> (length: Nat) -> Type where
  | nil (locals: LocalValueContext): ExpressionSizedList globals inductives locals 0
  | cons
      (locals: LocalValueContext)
      (n: Nat)
      (e: Expression globals inductives locals)
      (es: ExpressionSizedList globals inductives locals n)
    : ExpressionSizedList globals inductives locals (n+1)
end

inductive DependentList (α: Type) (f: α -> Type): (List α) -> Type where
  | unit: DependentList α f .nil
  | pair: forall (a: α) (as: List α), f a -> DependentList α f as -> DependentList α f (.cons a as)

structure ConstructorDecl (tvars: TypeVarContext) (formers: TypeFormerContext) (arity: Nat): Type where
  argTypes: SizedList (TType tvars formers) arity

structure OneInductiveDecl (tvars: TypeVarContext) (formers: TypeFormerContext) (spec: OneInductiveSpec) where
  constructors: DependentList Nat (ConstructorDecl tvars formers) spec

structure MutualInductiveDecl (tvars: TypeVarContext) (formers: TypeFormerContext) (spec: MutualInductiveSpec) where
  inductives: DependentList (List Nat) (OneInductiveDecl tvars formers) spec

/--
A program made up a sequence of type alias, global value, and inductive type declarations.
The indices are the contexts *provided* by this program.
(One could also define a Program by the contexts *in which* it is valid, like for types and expressions, but this is not what I chose.)
The dependent typing ensures that all names are well-scoped and all constructors and type formers are applied to the right number of arguments.
-/
inductive Program: TypeAliasContext -> GlobalValueContext -> InductiveContext -> Type where 
  | empty: Program .empty .empty .empty
  | valueDecl
      (tvars: TypeVarContext)
      (aliases: TypeAliasContext)
      (globals newglobals: GlobalValueContext)
      (ext: newglobals.extension globals)
      (inductives: InductiveContext)
      (p: Program aliases globals inductives)
      (val: Expression globals inductives .empty)
      (type: TType tvars (.mk aliases inductives))
    : Program aliases newglobals inductives 
  | typeAlias
      (tvars: TypeVarContext)
      (aliases newaliases: TypeAliasContext)
      (ext: newaliases.extension aliases)
      (globals: GlobalValueContext)
      (inductives: InductiveContext)
      (p: Program aliases globals inductives)
      (t: TType tvars (.mk aliases inductives))
    : Program newaliases globals inductives
  | mutualInductiveDecl
      (tvars: TypeVarContext)
      (aliases: TypeAliasContext)
      (globals: GlobalValueContext)
      (inductives newinductives: InductiveContext)
      (spec: MutualInductiveSpec)
      (ext: newinductives.multiExtension inductives spec)
      (p: Program aliases globals inductives)
      (minds: MutualInductiveDecl tvars (.mk aliases newinductives) spec)
    : Program aliases globals newinductives
end TypedML
