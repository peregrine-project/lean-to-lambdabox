module

abbrev GenericSizedContext := Nat
namespace GenericSizedContext
def empty: GenericSizedContext := 0
abbrev Id: GenericSizedContext -> Type := Fin
def extension (ctx' ctx: GenericSizedContext): Type := PLift (ctx' = ctx + 1)
def newId {ctx': GenericSizedContext} (ext: ctx'.extension ctx): ctx'.Id := ⟨ctx, ext.down ▸ Nat.lt_add_one ctx⟩
def extend (ctx: GenericSizedContext): (ctx': GenericSizedContext) × (ctx'.extension ctx) := ⟨ctx+1, PLift.up rfl⟩
def weakenId {ctx ctx': GenericSizedContext} (ext: ctx'.extension ctx): ctx.Id -> ctx'.Id := ext.down ▸ Fin.castSucc
def pullback
  (base a b: GenericSizedContext)
  (extA: a.extension base)
  (extB: b.extension base)
  : (top: GenericSizedContext) × (top.extension a) × (top.extension b)
  := ⟨a+1, PLift.up rfl, PLift.up ((extA.down ▸ extB.down) ▸ rfl)⟩ -- this is the most incomprehensible way I've ever proved n + 1 + 1 = n + 1 + 1
end GenericSizedContext

abbrev GenericArrayContext α := Array α
namespace GenericArrayContext
def empty: GenericArrayContext α := Array.empty
abbrev Id (ctx: GenericArrayContext α): Type := Fin (ctx.size)
def get (ctx: GenericArrayContext α) (id: ctx.Id): α := ctx[id]
def extension (ctx' ctx: GenericArrayContext α) (x: α): Type := PLift (ctx' = ctx.push x)
end GenericArrayContext

public def TypeVarContext: Type := GenericSizedContext
namespace TypeVarContext
public def Id: TypeVarContext -> Type := GenericSizedContext.Id
public def size: TypeVarContext -> Nat := id
end TypeVarContext

structure TypeAliasInfo where
  arity: Nat
public def TypeAliasContext: Type := GenericArrayContext TypeAliasInfo
namespace TypeAliasContext
public def empty: TypeAliasContext := GenericArrayContext.empty
public def Id: TypeAliasContext -> Type := GenericArrayContext.Id
public def arity (ctx: TypeAliasContext) (id: ctx.Id): Nat := ctx.get id |>.arity
/-- A witness of the fact that `ctx'` is an extension of `ctx` with an added type alias of arity `n`. -/
public def extension (ctx ctx': TypeAliasContext) (n: Nat): Type := GenericArrayContext.extension ctx ctx' { arity := n }
end TypeAliasContext

public abbrev ConstructorArity := Nat
/-- A list of constructor arities. -/
public abbrev OneInductiveArities := List ConstructorArity
public abbrev MutualInductiveArities := List OneInductiveArities
public structure MutualInductiveSpec where
  typeVarCount: Nat
  arities: MutualInductiveArities

public def InductiveContext: Type := GenericArrayContext MutualInductiveSpec
namespace InductiveContext
public def empty: InductiveContext := GenericArrayContext.empty
public def extension: (ctx' ctx: InductiveContext) -> (spec: MutualInductiveSpec) -> Type := GenericArrayContext.extension
public def MutualInductiveId: InductiveContext -> Type := GenericArrayContext.Id
namespace MutualInductiveId
public def typeFormerArity (mid: MutualInductiveId ctx): Nat := ctx.get mid |>.typeVarCount
abbrev inductiveArities (mid: MutualInductiveId ctx): List OneInductiveArities := ctx.get mid |>.arities
public def InductiveId (mid: MutualInductiveId ctx): Type := Fin (mid.inductiveArities.length)
namespace InductiveId
abbrev constructorArities (iid: @InductiveId ctx mid): List ConstructorArity := mid.inductiveArities |>.get iid
public def ConstructorId (iid: @InductiveId ctx mid): Type := Fin (iid.constructorArities.length)
namespace ConstructorId
public def arity (cid: @ConstructorId ctx mid iid): Nat := iid.constructorArities |>.get cid
end ConstructorId
end InductiveId
export InductiveId (ConstructorId)
end MutualInductiveId
export MutualInductiveId (InductiveId ConstructorId)
end InductiveContext

public structure TypeFormerContext: Type where
  public mk ::
  aliases: TypeAliasContext
  inductives: InductiveContext
namespace TypeFormerContext
public inductive Id (ctx: TypeFormerContext): Type where
  | private ialias (id: ctx.aliases.Id)
  | private iinductive (iid: ctx.inductives.InductiveId mid)
public def arity (ctx: TypeFormerContext): ctx.Id -> Nat
| .ialias id => ctx.aliases.arity id
| @Id.iinductive _ mid _ => mid.typeFormerArity
end TypeFormerContext

public def GlobalValueContext: Type := GenericSizedContext
namespace GlobalValueContext
public def empty: GlobalValueContext := GenericSizedContext.empty
public def Id: GlobalValueContext -> Type := GenericSizedContext.Id
public def extension: GlobalValueContext -> GlobalValueContext -> Type := GenericSizedContext.extension
end GlobalValueContext

public def LocalValueContext: Type := GenericSizedContext
namespace LocalValueContext
public def empty: LocalValueContext := GenericSizedContext.empty
public def Id: LocalValueContext -> Type := GenericSizedContext.Id
public def extension: LocalValueContext -> LocalValueContext -> Type := GenericSizedContext.extension
public def newId: {ctx': LocalValueContext} -> (ctx'.extension ctx) -> ctx'.Id := GenericSizedContext.newId
public def extend: (ctx: LocalValueContext) -> (ctx': LocalValueContext) × (ctx'.extension ctx) := GenericSizedContext.extend
/--
If the concrete definition of LocalValueContext.Id is such that this can be replaced by a no-op in compiled code,
hopefully the compiler will recognize that.
-/
public def weakenId: {ctx': LocalValueContext} -> (ctx'.extension ctx) -> ctx.Id -> ctx'.Id := GenericSizedContext.weakenId
public def pullback:
    (base a b: LocalValueContext) ->
    (extA: a.extension base) ->
    (extB: b.extension base) ->
  (top: LocalValueContext) × (top.extension a) × (top.extension b)
  := GenericSizedContext.pullback
end LocalValueContext
