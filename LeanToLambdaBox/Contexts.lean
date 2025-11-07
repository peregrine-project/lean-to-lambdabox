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
-- TODO: this should take an x as an argument! Or should it?
def extension (ctx' ctx: GenericArrayContext α): Type := { x: α // ctx' = ctx.push x }
end GenericArrayContext

public def TypeVarContext: Type := GenericSizedContext
namespace TypeVarContext
public def Id: TypeVarContext -> Type := GenericSizedContext.Id
end TypeVarContext

structure TypeAliasInfo where
  arity: Nat
public def TypeAliasContext: Type := GenericArrayContext TypeAliasInfo
namespace TypeAliasContext
public def empty: TypeAliasContext := GenericArrayContext.empty
public def Id: TypeAliasContext -> Type := GenericArrayContext.Id
public def arity (ctx: TypeAliasContext) (id: ctx.Id): Nat := ctx.get id |>.arity
-- this should take an arity as an argument!
public def extension: TypeAliasContext -> TypeAliasContext -> Type := GenericArrayContext.extension
end TypeAliasContext

/-- A list of constructor arities. -/
public abbrev OneInductiveSpec := List Nat
@[expose] public def MutualInductiveSpec := List OneInductiveSpec

@[reducible] -- needed for the definition of constructorArity to typecheck
public def InductiveContext: Type := GenericArrayContext OneInductiveSpec
namespace InductiveContext
public def empty: InductiveContext := GenericArrayContext.empty
@[reducible] -- needed for the definition of constructorArity to typecheck
public def InductiveId: InductiveContext -> Type := GenericArrayContext.Id
public def inductiveArity (ctx: InductiveContext) (iid: ctx.InductiveId): Nat := ctx.get iid |>.length
public def ConstructorId (ctx: InductiveContext) (iid: ctx.InductiveId): Type := Fin (ctx.inductiveArity iid)
public def constructorArity (ctx: InductiveContext) {iid: ctx.InductiveId} (cid: ctx.ConstructorId iid): Nat := ctx[iid][cid.val]'cid.isLt

def extensionP (ctx' ctx: InductiveContext) (spec: OneInductiveSpec): Prop := ctx' = ctx.push spec
def multiExtensionP (ctx' ctx: InductiveContext) (mspec: MutualInductiveSpec): Prop :=
  match mspec with
  | [] => True
  | spec::t => exists imd: InductiveContext, imd.extensionP ctx spec ∧ ctx'.multiExtensionP imd t
public def multiExtension (ctx' ctx: InductiveContext) (mspec: MutualInductiveSpec): Type := PLift (ctx'.multiExtensionP ctx mspec)
end InductiveContext

public structure TypeFormerContext: Type where
  public mk ::
  aliases: TypeAliasContext
  inductives: InductiveContext
namespace TypeFormerContext
public inductive Id (ctx: TypeFormerContext): Type where
  | private ialias (id: ctx.aliases.Id)
  | private iinductive (id: ctx.inductives.InductiveId)
public def arity (ctx: TypeFormerContext): ctx.Id -> Nat
| .ialias id => ctx.aliases.arity id
| .iinductive id => ctx.inductives.inductiveArity id
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
