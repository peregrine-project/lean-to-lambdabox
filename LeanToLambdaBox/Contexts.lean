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
  | ialias (id: ctx.aliases.Id)
  | iinductive (id: ctx.inductives.InductiveId)
-- noncomputable only because TypeAliasContext.arity and InductiveContext.inductiveArity are axioms atm
noncomputable def arity (ctx: TypeFormerContext): ctx.Id -> Nat
| .ialias id => ctx.aliases.arity id
| .iinductive id => ctx.inductives.inductiveArity id
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
axiom newId {ctx': LocalValueContext} (ext: ctx'.extension ctx): ctx'.Id
axiom extend (ctx: LocalValueContext): (ctx': LocalValueContext) × (ctx'.extension ctx)
/--
If the concrete definition of LocalValueContext.Id is such that this can be replaced by a no-op in compiled code,
hopefully the compiler will recognize that.
-/
axiom weakenId {ctx ctx': LocalValueContext}:  ctx'.extension ctx -> ctx.Id -> ctx'.Id
axiom pullback (base a b: LocalValueContext) (extA: a.extension base) (extB: b.extension base): (top: LocalValueContext) × (top.extension a) × (top.extension b)
end LocalValueContext
