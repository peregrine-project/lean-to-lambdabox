module

public axiom TypeVarContext: Type
public axiom TypeVarContext.Id: TypeVarContext -> Type

public axiom TypeAliasContext: Type
namespace TypeAliasContext
public axiom empty: TypeAliasContext
public axiom Id: TypeAliasContext -> Type
public axiom arity (ctx: TypeAliasContext): ctx.Id -> Nat
public axiom extension: TypeAliasContext -> TypeAliasContext -> Type
end TypeAliasContext

/-- A list of constructor arities. -/
@[expose] public def OneInductiveSpec := List Nat
@[expose] public def MutualInductiveSpec := List OneInductiveSpec

public axiom InductiveContext: Type
namespace InductiveContext
public axiom empty: InductiveContext
public axiom InductiveId: InductiveContext -> Type
public axiom inductiveArity (ctx: InductiveContext) (iid: ctx.InductiveId): Nat
public axiom ConstructorId (ctx: InductiveContext) (iid: ctx.InductiveId): Type
public axiom constructorArity (ctx: InductiveContext) (iid: ctx.InductiveId) (cid: ctx.ConstructorId iid): Nat
public axiom multiExtension: InductiveContext -> InductiveContext -> MutualInductiveSpec -> Type
end InductiveContext

public structure TypeFormerContext: Type where
  public mk ::
  aliases: TypeAliasContext
  inductives: InductiveContext
namespace TypeFormerContext
public inductive Id (ctx: TypeFormerContext): Type where
  | private ialias (id: ctx.aliases.Id)
  | private iinductive (id: ctx.inductives.InductiveId)
-- noncomputable only because TypeAliasContext.arity and InductiveContext.inductiveArity are axioms atm
public noncomputable def arity (ctx: TypeFormerContext): ctx.Id -> Nat
| .ialias id => ctx.aliases.arity id
| .iinductive id => ctx.inductives.inductiveArity id
end TypeFormerContext

public axiom GlobalValueContext: Type
namespace GlobalValueContext
public axiom empty: GlobalValueContext
public axiom Id: GlobalValueContext -> Type
public axiom extension: GlobalValueContext -> GlobalValueContext -> Type
end GlobalValueContext

public axiom LocalValueContext: Type
namespace LocalValueContext
public axiom empty: LocalValueContext
public axiom Id: LocalValueContext -> Type
public axiom extension: LocalValueContext -> LocalValueContext -> Type
public axiom newId {ctx': LocalValueContext} (ext: ctx'.extension ctx): ctx'.Id
public axiom extend (ctx: LocalValueContext): (ctx': LocalValueContext) × (ctx'.extension ctx)
/--
If the concrete definition of LocalValueContext.Id is such that this can be replaced by a no-op in compiled code,
hopefully the compiler will recognize that.
-/
public axiom weakenId {ctx ctx': LocalValueContext}:  ctx'.extension ctx -> ctx.Id -> ctx'.Id
public axiom pullback (base a b: LocalValueContext) (extA: a.extension base) (extB: b.extension base): (top: LocalValueContext) × (top.extension a) × (top.extension b)
end LocalValueContext
