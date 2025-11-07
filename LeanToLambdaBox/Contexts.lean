module

abbrev GenericSizedContext := Nat
namespace GenericSizedContext
def empty: GenericSizedContext := 0
def Id: GenericSizedContext -> Type := Fin
def Extension (ctx' ctx: GenericSizedContext): Prop := (ctx' = ctx + 1)
def extend (ctx: GenericSizedContext): { ctx': GenericSizedContext // ctx'.Extension ctx } := ⟨ctx+1, rfl⟩
namespace Extension
def newId (ext: @Extension ctx' ctx): ctx'.Id := ⟨ctx, ext ▸ Nat.lt_add_one ctx⟩
def weakenId (ext: @Extension ctx' ctx): ctx.Id -> ctx'.Id := ext ▸ Fin.castSucc
def pullback
  (extA: a.Extension base)
  (extB: b.Extension base)
  : { top: GenericSizedContext // top.Extension a ∧ top.Extension b }
  := ⟨a+1, rfl, (extA ▸ show _ = _ from extB) ▸ rfl⟩ -- this is the most codegolf way I've ever proved n + 1 + 1 = n + 1 + 1
end Extension
end GenericSizedContext

abbrev GenericArrayContext α := Array α
namespace GenericArrayContext
def empty: GenericArrayContext α := Array.empty
abbrev Id (ctx: GenericArrayContext α): Type := Fin (ctx.size)
namespace Id
def getInfo (id: @Id α ctx): α := ctx[id]
end Id
def Extension (ctx' ctx: GenericArrayContext α) (x: α): Prop := ctx' = ctx.push x
end GenericArrayContext

public def TypeVarContext: Type := GenericSizedContext
namespace TypeVarContext
public def Id: TypeVarContext -> Type := GenericSizedContext.Id
public def size: TypeVarContext -> Nat := id
end TypeVarContext

abbrev TypeAliasInfo := Nat
public def TypeAliasContext: Type := GenericArrayContext TypeAliasInfo
namespace TypeAliasContext
public def empty: TypeAliasContext := GenericArrayContext.empty
public def Id: TypeAliasContext -> Type := GenericArrayContext.Id
namespace Id
public def arity: (id: @Id ctx) -> Nat := GenericArrayContext.Id.getInfo
end Id
/-- A witness of the fact that `ctx'` is an extension of `ctx` with an added type alias of arity `n`. -/
public def Extension: (ctx ctx': TypeAliasContext) -> (n: Nat) -> Prop := GenericArrayContext.Extension
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
public def Extension: (ctx' ctx: InductiveContext) -> (spec: MutualInductiveSpec) -> Prop := GenericArrayContext.Extension
public def MutualInductiveId: InductiveContext -> Type := GenericArrayContext.Id
namespace MutualInductiveId
public def typeFormerArity (mid: MutualInductiveId ctx): Nat := mid.getInfo |>.typeVarCount
abbrev inductiveArities (mid: MutualInductiveId ctx): List OneInductiveArities := mid.getInfo |>.arities
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
| .ialias id => id.arity
| @Id.iinductive _ mid _ => mid.typeFormerArity
end TypeFormerContext

public def GlobalValueContext: Type := GenericSizedContext
namespace GlobalValueContext
public def empty: GlobalValueContext := GenericSizedContext.empty
public def Id: GlobalValueContext -> Type := GenericSizedContext.Id
public def Extension: GlobalValueContext -> GlobalValueContext -> Prop := GenericSizedContext.Extension
end GlobalValueContext

public def LocalValueContext: Type := GenericSizedContext
namespace LocalValueContext
public def empty: LocalValueContext := GenericSizedContext.empty
public def Id: LocalValueContext -> Type := GenericSizedContext.Id
public def Extension: LocalValueContext -> LocalValueContext -> Prop := GenericSizedContext.Extension
public def extend: (ctx: LocalValueContext) -> { ctx': LocalValueContext // ctx'.Extension ctx } := GenericSizedContext.extend
namespace Extension
public def newId: {ctx': LocalValueContext} -> (ctx'.Extension ctx) -> ctx'.Id := GenericSizedContext.Extension.newId
/--
If the concrete definition is such that this can be replaced by a no-op in compiled code; hopefully the compiler will recognize that.
-/
public def weakenId: {ctx': LocalValueContext} -> (ctx'.Extension ctx) -> ctx.Id -> ctx'.Id := GenericSizedContext.Extension.weakenId
public def pullback:
    (extA: a.Extension base) ->
    (extB: b.Extension base) ->
  { top: LocalValueContext // top.Extension a ∧ top.Extension b }
  := GenericSizedContext.Extension.pullback
end Extension
end LocalValueContext
