private abbrev GenericSizedContext := Nat
namespace GenericSizedContext
private def empty: GenericSizedContext := 0
private def Id: GenericSizedContext -> Type := Fin
private def Extension (ctx ctx': GenericSizedContext): Prop := (ctx' = ctx + 1)
private def extend (ctx: GenericSizedContext): { ctx': GenericSizedContext // ctx.Extension ctx' } := ⟨ctx+1, rfl⟩
namespace Extension
private def newId (ext: @Extension ctx ctx'): ctx'.Id := ⟨ctx, ext ▸ Nat.lt_add_one ctx⟩
private def weakenId (ext: @Extension ctx ctx'): ctx.Id -> ctx'.Id := ext ▸ Fin.castSucc
private def pullback
  (extA: @Extension base a)
  (extB: @Extension base b)
  : { top: GenericSizedContext // a.Extension top ∧ b.Extension top }
  := ⟨a+1, rfl, (extA ▸ show _ = _ from extB) ▸ rfl⟩ -- this is the most codegolf way I've ever proved n + 1 + 1 = n + 1 + 1
end Extension
private def MultiExtension (ctx ctx': GenericSizedContext): Prop := ctx ≤ ctx'
namespace MultiExtension
private def trivial: MultiExtension ctx ctx := Nat.le_refl _
end MultiExtension
end GenericSizedContext

private abbrev GenericArrayContext α := Array α
namespace GenericArrayContext
private def empty: GenericArrayContext α := Array.empty
private abbrev Id (ctx: GenericArrayContext α): Type := Fin (ctx.size)
namespace Id
private def getInfo (id: @Id α ctx): α := ctx[id]
end Id
private def Extension (ctx ctx': GenericArrayContext α) (x: α): Prop := ctx' = ctx.push x
private def MultiExtension (ctx ctx': GenericArrayContext α): Prop := ctx.toList.IsPrefix ctx'.toList
namespace MultiExtension
private def trivial: MultiExtension ctx ctx := ⟨[], List.append_nil _⟩
end MultiExtension
end GenericArrayContext

@[irreducible, local semireducible]
def TypeVarContext: Type := GenericSizedContext
namespace TypeVarContext
@[irreducible]
def Id: TypeVarContext -> Type := GenericSizedContext.Id
@[irreducible]
def size: TypeVarContext -> Nat := id
end TypeVarContext

@[irreducible, local semireducible]
def TypeAliasInfo := Nat
@[irreducible, local semireducible]
def TypeAliasContext: Type := GenericArrayContext TypeAliasInfo
namespace TypeAliasContext
@[irreducible]
def empty: TypeAliasContext := GenericArrayContext.empty
@[irreducible, local semireducible]
def Id: TypeAliasContext -> Type := GenericArrayContext.Id
namespace Id
@[irreducible]
def arity: (id: @Id ctx) -> Nat := GenericArrayContext.Id.getInfo
end Id
/-- A witness of the fact that `ctx'` is an extension of `ctx` with an added type alias of arity `n`. -/
@[irreducible]
def Extension: (ctx ctx': TypeAliasContext) -> (n: Nat) -> Prop := GenericArrayContext.Extension
@[irreducible, local semireducible]
def MultiExtension: (ctx ctx': TypeAliasContext) -> Prop := GenericArrayContext.MultiExtension
namespace MultiExtension
def trivial: MultiExtension ctx ctx := GenericArrayContext.MultiExtension.trivial
end MultiExtension
end TypeAliasContext

abbrev ConstructorArity := Nat
/-- A list of constructor arities. -/
abbrev OneInductiveArities := List ConstructorArity
abbrev MutualInductiveArities := List OneInductiveArities
structure MutualInductiveSpec where
  typeVarCount: Nat
  arities: MutualInductiveArities

@[irreducible, local semireducible]
def InductiveContext: Type := GenericArrayContext MutualInductiveSpec
namespace InductiveContext
@[irreducible]
def empty: InductiveContext := GenericArrayContext.empty
@[irreducible]
def Extension: (ctx ctx': InductiveContext) -> (spec: MutualInductiveSpec) -> Prop := GenericArrayContext.Extension
@[irreducible, local semireducible]
def MultiExtension: (ctx ctx': InductiveContext) -> Prop := GenericArrayContext.MultiExtension
namespace MultiExtension
@[irreducible]
def trivial: MultiExtension ctx ctx := GenericArrayContext.MultiExtension.trivial
end MultiExtension
@[irreducible, local semireducible]
def MutualInductiveId: InductiveContext -> Type := GenericArrayContext.Id
namespace MutualInductiveId
@[irreducible]
def typeFormerArity (mid: MutualInductiveId ctx): Nat := mid.getInfo |>.typeVarCount
@[irreducible]
def inductiveArities (mid: MutualInductiveId ctx): List OneInductiveArities := mid.getInfo |>.arities
@[irreducible, local semireducible]
def InductiveId (mid: MutualInductiveId ctx): Type := Fin (mid.inductiveArities.length)
namespace InductiveId
@[irreducible]
def constructorArities (iid: @InductiveId ctx mid): List ConstructorArity := mid.inductiveArities |>.get iid
@[irreducible, local semireducible]
def ConstructorId (iid: @InductiveId ctx mid): Type := Fin (iid.constructorArities.length)
namespace ConstructorId
@[irreducible]
public def arity (cid: @ConstructorId ctx mid iid): Nat := iid.constructorArities |>.get cid
end ConstructorId
end InductiveId
export InductiveId (ConstructorId)
end MutualInductiveId
export MutualInductiveId (InductiveId ConstructorId)
end InductiveContext

structure TypeFormerContext: Type where
  private mkPriv ::
  private aliases: TypeAliasContext
  private inductives: InductiveContext

namespace TypeFormerContext
@[irreducible]
def mk: TypeAliasContext -> InductiveContext -> TypeFormerContext := .mkPriv
inductive IdImpl (ctx: TypeFormerContext): Type where
  | ialias (id: ctx.aliases.Id)
  | iinductive (iid: ctx.inductives.InductiveId mid)
@[irreducible, local semireducible]
def Id: TypeFormerContext -> Type := IdImpl
@[irreducible]
def arity (ctx: TypeFormerContext): ctx.Id -> Nat
| .ialias id => id.arity
| @IdImpl.iinductive _ mid _ => mid.typeFormerArity
end TypeFormerContext

@[irreducible, local semireducible]
def GlobalValueContext: Type := GenericSizedContext
namespace GlobalValueContext
@[irreducible]
def empty: GlobalValueContext := GenericSizedContext.empty
@[irreducible]
def Id: GlobalValueContext -> Type := GenericSizedContext.Id
@[irreducible]
def Extension: (ctx ctx': GlobalValueContext) -> Prop := GenericSizedContext.Extension
@[irreducible, local semireducible]
def MultiExtension: (ctx ctx': GlobalValueContext)-> Prop := GenericSizedContext.MultiExtension
namespace MultiExtension
@[irreducible]
def trivial: MultiExtension ctx ctx := GenericSizedContext.MultiExtension.trivial
end MultiExtension
end GlobalValueContext

@[irreducible, local semireducible]
def LocalValueContext: Type := GenericSizedContext
namespace LocalValueContext
@[irreducible]
def empty: LocalValueContext := GenericSizedContext.empty
@[irreducible, local semireducible]
def Id: LocalValueContext -> Type := GenericSizedContext.Id
@[irreducible, local semireducible]
def Extension: (ctx ctx': LocalValueContext) -> Prop := GenericSizedContext.Extension
@[irreducible]
def extend: (ctx: LocalValueContext) -> { ctx': LocalValueContext // ctx.Extension ctx' } := GenericSizedContext.extend
namespace Extension
@[irreducible]
def newId: (@Extension ctx ctx') -> ctx'.Id := GenericSizedContext.Extension.newId
/--
The concrete definition is such that this can be replaced by a no-op in compiled code; hopefully the compiler will recognize that.
-/
@[irreducible]
def weakenId: (@Extension ctx ctx') -> ctx.Id -> ctx'.Id := GenericSizedContext.Extension.weakenId
@[irreducible]
def pullback:
    (extA: @Extension base a) ->
    (extB: @Extension base b) ->
  { top: LocalValueContext // a.Extension top ∧ b.Extension top }
  := GenericSizedContext.Extension.pullback
end Extension
end LocalValueContext
