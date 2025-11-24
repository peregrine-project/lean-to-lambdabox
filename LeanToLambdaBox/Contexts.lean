-- TODO: kill the boilerplate (or more likely change it into different boilerplate) using type classes?
private abbrev GenericSizedContext := Nat
namespace GenericSizedContext
private def empty: GenericSizedContext := 0
private def Id: GenericSizedContext -> Type := Fin
private def MultiExtension (ctx ctx': GenericSizedContext): Prop := ctx ≤ ctx'
namespace MultiExtension
private def trivial: MultiExtension ctx ctx := Nat.le_refl _
private def compose: (ext: MultiExtension ctx ctx') -> (ext': MultiExtension ctx' ctx'') -> MultiExtension ctx ctx'' := Nat.le_trans
private def weakenId: MultiExtension ctx ctx' -> ctx.Id -> ctx'.Id := Fin.castLE
end MultiExtension
private def Extension (ctx ctx': GenericSizedContext): Prop := (ctx' = ctx + 1)
private def extend (ctx: GenericSizedContext): { ctx': GenericSizedContext // ctx.Extension ctx' } := ⟨ctx+1, rfl⟩
namespace Extension
private def newId (ext: Extension ctx ctx'): ctx'.Id := ⟨ctx, ext ▸ Nat.lt_add_one ctx⟩
private def weakenId (ext: Extension ctx ctx'): ctx.Id -> ctx'.Id := ext ▸ Fin.castSucc
private def pullback
  (extA: Extension base a)
  (extB: Extension base b)
  : { top: GenericSizedContext // a.Extension top ∧ b.Extension top }
  := ⟨a+1, rfl, (extA ▸ show _ = _ from extB) ▸ rfl⟩ -- this is the most codegolf way I've ever proved n + 1 + 1 = n + 1 + 1
private def toMulti (ext: Extension ctx ctx'): MultiExtension ctx ctx' := ext ▸ Nat.le_succ _
end Extension

/-- Essentially a map from `ctx.Id` to `α`. -/
-- should this be used to define GenericArrayContext?
private def Map (ctx: GenericSizedContext) (α: Type): Type := Vector α ctx
namespace Map
private def empty: Map .empty α := #v[]
private def extend (m: Map ctx α) (a: α) (ext: Extension ctx ctx'): Map ctx' α := ext ▸ m.push a
private def get (m: Map ctx α) (i: ctx.Id): α := Vector.get m i
private def map: (α -> β) -> Map ctx α -> Map ctx β := Vector.map
end Map
end GenericSizedContext

private abbrev GenericArrayContext α := Array α
namespace GenericArrayContext
private def empty: GenericArrayContext α := Array.empty
private abbrev Id (ctx: GenericArrayContext α): Type := Fin (ctx.size)
namespace Id
private def getInfo (id: @Id α ctx): α := ctx[id]
end Id
private def MultiExtension (ctx ctx': GenericArrayContext α): Prop := ctx.toList.IsPrefix ctx'.toList
namespace MultiExtension
private def trivial: MultiExtension ctx ctx := ⟨[], List.append_nil _⟩
private def compose (ext: MultiExtension ctx ctx') (ext': MultiExtension ctx' ctx''): MultiExtension ctx ctx'' := by
  cases ext with | intro l h =>
  cases ext' with | intro l' h'=>
  exists l ++ l'
  rewrite [<-List.append_assoc, h, h']
  rfl

private def weakenId (ext: MultiExtension ctx ctx'): ctx.Id -> ctx'.Id :=
  Fin.castLE (by 
    show ctx.toList.length ≤ ctx'.toList.length
    cases ext with | intro _ h =>
    rewrite [<-h, List.length_append]
    apply Nat.le_add_right
  )

private theorem weakenId_getInfo: (@weakenId α ctx ctx' ext i).getInfo = i.getInfo := by
  cases ext with | intro _ h =>
  show ctx'.toList.get _  = _
  rewrite [List.get_of_eq h.symm]
  apply List.getElem_append_left

end MultiExtension
private def Extension (ctx ctx': GenericArrayContext α) (x: α): Prop := ctx' = ctx.push x
private def extend (ctx: GenericArrayContext α) (x: α): { ctx': GenericArrayContext α // ctx.Extension ctx' x } := ⟨ctx.push x, rfl⟩
namespace Extension
private def newId (ext: Extension ctx ctx' x): ctx'.Id := ⟨ctx.size, by rewrite [ext]; simp⟩
private def toMulti (ext: Extension ctx ctx' x): MultiExtension ctx ctx' := ⟨[x], by rewrite [ext]; simp⟩
end Extension

private def Map (ctx: GenericArrayContext α) (β: Type): Type := Vector β ctx.size
namespace Map
private def empty: @Map α .empty β := #v[]
private def extend (m: Map ctx β) (b: β) (ext: Extension ctx ctx' a): Map ctx' β := by
  unfold Map
  rewrite [ext]
  rewrite [Array.size_push a]
  exact m.push b
private def get (m: Map ctx α) (i: ctx.Id): α := Vector.get m i
end Map
end GenericArrayContext

@[irreducible, local semireducible]
def TypeVarContext: Type := GenericSizedContext
namespace TypeVarContext
@[irreducible, local semireducible]
def empty: TypeVarContext := GenericSizedContext.empty
@[irreducible, local semireducible]
def Id: TypeVarContext -> Type := GenericSizedContext.Id
-- `lbox` may expect this to be the other way around, check.
@[irreducible]
def Id.toIndex: Id ctx -> Nat := Fin.val
@[irreducible]
def size: TypeVarContext -> Nat := id
@[irreducible, local semireducible]
def MultiExtension: TypeVarContext -> TypeVarContext -> Prop := GenericSizedContext.MultiExtension
namespace MultiExtension
@[irreducible]
def trivial: MultiExtension ctx ctx := GenericSizedContext.MultiExtension.trivial
@[irreducible]
def compose: MultiExtension ctx ctx' -> MultiExtension ctx' ctx'' -> MultiExtension ctx ctx'' := GenericSizedContext.MultiExtension.compose
@[irreducible]
def weakenId: MultiExtension ctx ctx' -> ctx.Id -> ctx'.Id := GenericSizedContext.MultiExtension.weakenId
end MultiExtension
@[irreducible, local semireducible]
def Extension: TypeVarContext -> TypeVarContext -> Prop := GenericSizedContext.Extension
namespace Extension
@[irreducible]
def toMulti: Extension ctx ctx' -> MultiExtension ctx ctx' := GenericSizedContext.Extension.toMulti
@[irreducible]
def newId: Extension ctx ctx' -> ctx'.Id := GenericSizedContext.Extension.newId
@[irreducible]
def weakenId: Extension ctx ctx' -> ctx.Id -> ctx'.Id := GenericSizedContext.Extension.weakenId
end Extension
@[irreducible]
def extend: (ctx: TypeVarContext) -> { ctx': TypeVarContext // ctx.Extension ctx' } := GenericSizedContext.extend
@[irreducible, local semireducible]
def Map: TypeVarContext -> Type -> Type := GenericSizedContext.Map
namespace Map
@[irreducible]
def empty: Map .empty α := GenericSizedContext.Map.empty
@[irreducible]
def map: (α -> β) -> Map ctx α -> Map ctx β := GenericSizedContext.Map.map
@[irreducible]
def extend: (Map ctx α) -> α -> ctx.Extension ctx' -> Map ctx' α := GenericSizedContext.Map.extend
/--
This is defined only for TypeVarContext, and not for GenericSizedContext,
because it is actually quite special that we expose a canonical ordering of the identifiers in a context.
-/
@[irreducible]
def toList: Map ctx α -> List α := Vector.toList
end Map
end TypeVarContext

@[irreducible, local semireducible]
def TypeAliasInfo := Nat
@[irreducible, local semireducible]
def TypeAliasContext: Type := GenericArrayContext TypeAliasInfo
namespace TypeAliasContext
@[irreducible, local semireducible]
def empty: TypeAliasContext := GenericArrayContext.empty
@[irreducible, local semireducible]
def Id: TypeAliasContext -> Type := GenericArrayContext.Id
namespace Id
@[irreducible]
def arity: (id: @Id ctx) -> Nat := GenericArrayContext.Id.getInfo
end Id
@[irreducible, local semireducible]
def MultiExtension: (ctx ctx': TypeAliasContext) -> Prop := GenericArrayContext.MultiExtension
namespace MultiExtension
@[irreducible]
def trivial: MultiExtension ctx ctx := GenericArrayContext.MultiExtension.trivial
@[irreducible]
def compose: MultiExtension ctx ctx' -> MultiExtension ctx' ctx'' -> MultiExtension ctx ctx'' := GenericArrayContext.MultiExtension.compose
@[irreducible, local semireducible]
def weakenId: MultiExtension ctx ctx' -> ctx.Id -> ctx'.Id := GenericArrayContext.MultiExtension.weakenId
unseal Id.arity in
theorem weakenId_arity : (@weakenId ctx ctx' ext i).arity = i.arity := GenericArrayContext.MultiExtension.weakenId_getInfo
end MultiExtension
/-- A witness of the fact that `ctx'` is an extension of `ctx` with an added type alias of arity `n`. -/
@[irreducible, local semireducible]
def Extension: (ctx ctx': TypeAliasContext) -> (n: Nat) -> Prop := GenericArrayContext.Extension
namespace Extension
def newId: Extension ctx ctx' x -> ctx'.Id := GenericArrayContext.Extension.newId
def toMulti: Extension ctx ctx' n -> MultiExtension ctx ctx' := GenericArrayContext.Extension.toMulti
end Extension
@[irreducible]
def extend: (ctx: TypeAliasContext) -> (n: Nat) -> { ctx': TypeAliasContext // ctx.Extension ctx' n } := GenericArrayContext.extend
@[irreducible, local semireducible]
def Map: TypeAliasContext -> Type -> Type := GenericArrayContext.Map
namespace Map
@[irreducible]
def empty: Map .empty α := GenericArrayContext.Map.empty
@[irreducible]
def extend: Map ctx β -> β -> Extension ctx ctx' a -> Map ctx' β := GenericArrayContext.Map.extend
@[irreducible]
def get: Map ctx α -> ctx.Id -> α := GenericArrayContext.Map.get
end Map
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
@[irreducible, local semireducible]
def empty: InductiveContext := GenericArrayContext.empty
@[irreducible, local semireducible]
def MutualInductiveId: InductiveContext -> Type := GenericArrayContext.Id
namespace MutualInductiveId
@[irreducible]
def typeFormerArity (mid: MutualInductiveId ctx): Nat := mid.getInfo |>.typeVarCount
@[irreducible, local semireducible]
def inductiveArities (mid: MutualInductiveId ctx): List OneInductiveArities := mid.getInfo |>.arities
@[irreducible, local semireducible]
def InductiveId (mid: MutualInductiveId ctx): Type := Fin (mid.inductiveArities.length)
namespace InductiveId
@[irreducible, local semireducible]
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
@[irreducible, local semireducible]
def Extension: (ctx ctx': InductiveContext) -> (spec: MutualInductiveSpec) -> Prop := GenericArrayContext.Extension
@[irreducible, local semireducible]
def MultiExtension: (ctx ctx': InductiveContext) -> Prop := GenericArrayContext.MultiExtension
namespace MultiExtension
@[irreducible]
def trivial: MultiExtension ctx ctx := GenericArrayContext.MultiExtension.trivial
@[irreducible]
def compose: MultiExtension ctx ctx' -> MultiExtension ctx' ctx'' -> MultiExtension ctx ctx'' := GenericArrayContext.MultiExtension.compose

@[irreducible, local semireducible]
def weakenMutualInductiveId: MultiExtension ctx ctx' -> ctx.MutualInductiveId -> ctx'.MutualInductiveId := GenericArrayContext.MultiExtension.weakenId

unseal MutualInductiveId.inductiveArities
theorem weakenMutualInductiveId_inductiveArities : (@weakenMutualInductiveId ctx ctx' ext mid).inductiveArities = mid.inductiveArities :=
  congrArg MutualInductiveSpec.arities GenericArrayContext.MultiExtension.weakenId_getInfo

unseal MutualInductiveId.typeFormerArity
theorem weakenMutualInductiveId_typeFormerArity : (@weakenMutualInductiveId ctx ctx' ext mid).typeFormerArity = mid.typeFormerArity :=
  congrArg MutualInductiveSpec.typeVarCount GenericArrayContext.MultiExtension.weakenId_getInfo

unseal InductiveId
@[irreducible, local semireducible]
def weakenInductiveId (ext: MultiExtension ctx ctx') (iid: @InductiveId ctx mid): (ext.weakenMutualInductiveId mid).InductiveId :=
  Fin.cast (congrArg List.length weakenMutualInductiveId_inductiveArities).symm iid

unseal MutualInductiveId.InductiveId.constructorArities
theorem weakenInductiveId_constructorArities: (@weakenInductiveId ctx ctx' mid ext iid).constructorArities = iid.constructorArities :=
  List.get_of_eq weakenMutualInductiveId_inductiveArities _

unseal ConstructorId
@[irreducible, local semireducible]
def weakenConstructorId (ext: MultiExtension ctx ctx') (cid: @ConstructorId ctx mid iid): (ext.weakenInductiveId iid).ConstructorId :=
  Fin.cast (congrArg List.length weakenInductiveId_constructorArities).symm cid

unseal MutualInductiveId.InductiveId.ConstructorId.arity
theorem weakenConstructorId_arity: (@weakenConstructorId ctx ctx' mid iid ext cid).arity = cid.arity :=
  List.get_of_eq weakenInductiveId_constructorArities _

end MultiExtension
@[irreducible, local semireducible]
def Map: InductiveContext -> Type -> Type := GenericArrayContext.Map
namespace Map
@[irreducible]
def empty: Map .empty α := GenericArrayContext.Map.empty
@[irreducible]
def extend: Map ctx β -> β -> Extension ctx ctx' a -> Map ctx' β := GenericArrayContext.Map.extend
@[irreducible]
def get: Map ctx α -> ctx.Id -> α := GenericArrayContext.Map.get
end Map
end InductiveContext

@[irreducible, local semireducible]
def GlobalValueContext: Type := GenericSizedContext
namespace GlobalValueContext
@[irreducible, local semireducible]
def empty: GlobalValueContext := GenericSizedContext.empty
@[irreducible, local semireducible]
def Id: GlobalValueContext -> Type := GenericSizedContext.Id
@[irreducible, local semireducible]
def MultiExtension: (ctx ctx': GlobalValueContext)-> Prop := GenericSizedContext.MultiExtension
namespace MultiExtension
@[irreducible]
def trivial: MultiExtension ctx ctx := GenericSizedContext.MultiExtension.trivial
@[irreducible]
def compose: MultiExtension ctx ctx' -> MultiExtension ctx' ctx'' -> MultiExtension ctx ctx'' := GenericSizedContext.MultiExtension.compose
@[irreducible]
def weakenId: MultiExtension ctx ctx' -> ctx.Id -> ctx'.Id := GenericSizedContext.MultiExtension.weakenId
end MultiExtension
@[irreducible, local semireducible]
def Extension: (ctx ctx': GlobalValueContext) -> Prop := GenericSizedContext.Extension
namespace Extension
@[irreducible]
def toMulti: Extension ctx ctx' -> MultiExtension ctx ctx' := GenericSizedContext.Extension.toMulti
@[irreducible]
def newId: (Extension ctx ctx') -> ctx'.Id := GenericSizedContext.Extension.newId
end Extension
@[irreducible]
def extend: (ctx: GlobalValueContext) -> { ctx': GlobalValueContext // ctx.Extension ctx' } := GenericSizedContext.extend

@[irreducible, local semireducible]
def Map: GlobalValueContext -> Type -> Type := GenericSizedContext.Map
namespace Map
@[irreducible]
def empty: Map .empty α := GenericSizedContext.Map.empty
@[irreducible]
def extend: Map ctx α -> α -> Extension ctx ctx' -> Map ctx' α := GenericSizedContext.Map.extend
@[irreducible]
def get: Map ctx α -> ctx.Id -> α := GenericSizedContext.Map.get
end Map
end GlobalValueContext

@[irreducible, local semireducible]
def LocalValueContext: Type := GenericSizedContext
namespace LocalValueContext
@[irreducible]
def empty: LocalValueContext := GenericSizedContext.empty
@[irreducible, local semireducible]
def Id: LocalValueContext -> Type := GenericSizedContext.Id
namespace Id
@[irreducible]
def deBruijnIndex (i: Id locals): Nat := i.rev.val
end Id
@[irreducible, local semireducible]
def Extension: (ctx ctx': LocalValueContext) -> Prop := GenericSizedContext.Extension
@[irreducible]
def extend: (ctx: LocalValueContext) -> { ctx': LocalValueContext // ctx.Extension ctx' } := GenericSizedContext.extend
namespace Extension
@[irreducible]
def newId: (Extension ctx ctx') -> ctx'.Id := GenericSizedContext.Extension.newId
/--
The concrete definition is such that this can be replaced by a no-op in compiled code; hopefully the compiler will recognize that.
-/
@[irreducible]
def weakenId: (Extension ctx ctx') -> ctx.Id -> ctx'.Id := GenericSizedContext.Extension.weakenId
@[irreducible]
def pullback:
    (extA: Extension base a) ->
    (extB: Extension base b) ->
  { top: LocalValueContext // a.Extension top ∧ b.Extension top }
  := GenericSizedContext.Extension.pullback
end Extension
end LocalValueContext

structure ProgramContext where
  aliases: TypeAliasContext
  globals: GlobalValueContext
  inductives: InductiveContext

namespace ProgramContext

def empty: ProgramContext := { aliases := .empty, globals := .empty, inductives := .empty }

structure MultiExtension (ctx ctx': ProgramContext) where
  aliases: ctx.aliases.MultiExtension ctx'.aliases
  globals: ctx.globals.MultiExtension ctx'.globals
  inductives: ctx.inductives.MultiExtension ctx'.inductives

namespace MultiExtension

def trivial: MultiExtension ctx ctx where
  aliases := .trivial
  globals := .trivial
  inductives := .trivial

def compose (ext: MultiExtension ctx ctx') (ext': MultiExtension ctx' ctx''): MultiExtension ctx ctx'' where
  aliases := ext.aliases.compose ext'.aliases
  globals := ext.globals.compose ext'.globals
  inductives := ext.inductives.compose ext'.inductives

end MultiExtension
end ProgramContext
