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
private def compose: (ext: MultiExtension ctx ctx') -> (ext': MultiExtension ctx' ctx'') -> MultiExtension ctx ctx'' := Nat.le_trans
private def weakenId: MultiExtension ctx ctx' -> ctx.Id -> ctx'.Id := Fin.castLE
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
@[irreducible]
def trivial: MultiExtension ctx ctx := GenericArrayContext.MultiExtension.trivial
@[irreducible]
def compose: MultiExtension ctx ctx' -> MultiExtension ctx' ctx'' -> MultiExtension ctx ctx'' := GenericArrayContext.MultiExtension.compose
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
@[irreducible]
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
  congrArg (MutualInductiveSpec.arities) GenericArrayContext.MultiExtension.weakenId_getInfo

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
@[irreducible, local semireducible]
def Id: GlobalValueContext -> Type := GenericSizedContext.Id
@[irreducible]
def Extension: (ctx ctx': GlobalValueContext) -> Prop := GenericSizedContext.Extension
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
