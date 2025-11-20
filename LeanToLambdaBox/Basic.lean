import Lean
import LeanToLambdaBox.Names

open Lean (FVarId InductiveVal)

structure InductiveId where
  mutualBlockName: Kername
  /-- Which of the mutually inductive types defined in this block is used here? -/
  idx: Nat
  deriving Inhabited, Repr

structure ProjectionInfo where
  indType: InductiveId 
  paramCount: Nat
  fieldIdx: Nat
  deriving Inhabited, Repr

structure FixDef {term: Type} where
  name: LocalName
  /-- The body typically (necessarily?) starts with a certain number (at least rarg + 1) of lambda constructor applications, one for each argument. -/
  body: term
  /-- Principal/structural argument for recursion. -/
  principalArgIdx: Nat := 0 -- this doesn't matter computationally and is just needed in the proof of correctness, so it's safe to let this be 0
  deriving Inhabited, Repr

inductive PrimTag where
  | primInt
  /- Rocq has these, but I'm not supporting them for the moment.
  | primFloat
  | primArray
  -/
deriving Repr

/--
In MetaRocq they need to do something fancy to keep positivity because there everything is parametrized by the type of terms.
Since I don't handle arrays for now there's no need for that.
--/
abbrev PrimModel: PrimTag -> Type
  | .primInt => BitVec 63

abbrev PrimVal: Type := Σ t: PrimTag, PrimModel t

/--
Basically `term` as defined in `MetaRocq/Erasure/EAst.v`, with an extra constructor `.fvar` to mimic Lean's locally nameless representation.
-/
inductive LBTerm where
  | box: LBTerm
  /-- A bound variable, accessed as a de Bruijn index. -/
  | bvar: Nat -> LBTerm
  | fvar: FVarId -> LBTerm
  | lambda: LocalName -> LBTerm -> LBTerm
  | letIn: LocalName -> LBTerm -> LBTerm -> LBTerm
  | app: LBTerm -> LBTerm -> LBTerm
  /-- A constant living in the environment. -/
  | const: Kername -> LBTerm
  | construct: InductiveId -> Nat /- index of the constructor used -/ -> List LBTerm -> LBTerm
  | case: (InductiveId × Nat /- number of parameters -/) -> LBTerm -> List (List LocalName × LBTerm) -> LBTerm
  | proj: ProjectionInfo -> LBTerm -> LBTerm
  /-- Define some number of mutually inductive functions, then access one. -/
  | fix: List (@FixDef LBTerm) -> Nat /- index of the one mutually defined function we want to access -/ -> LBTerm
  | prim: PrimVal -> LBTerm
  deriving Inhabited, Repr

/-- This is actually structurally recursive, I think, Lean just has trouble seeing it because of the inductive nesting. -/
partial def toBvar (x: FVarId) (lvl: Nat) (e: LBTerm): LBTerm :=
  match e with
  | .box => .box
  | .bvar i => .bvar i
  | .fvar y => if y == x then .bvar lvl else .fvar y
  | .lambda name body => .lambda name (toBvar x (lvl + 1) body)
  | .letIn name val body => .letIn name (toBvar x lvl val) (toBvar x (lvl + 1) body)
  | .app a b => .app (toBvar x lvl a) (toBvar x lvl b)
  | .const kn => .const kn
  | .construct indid n args => .construct indid n (args.map <| toBvar x lvl)
  | .case (indid, n) discr alts => .case (indid, n) (toBvar x lvl discr) (alts.map fun (names, alt) => (names, toBvar x (lvl + names.length) alt))
  | .proj pinfo e => .proj pinfo (toBvar x lvl e)
  | .fix defs i =>
    let def_count := defs.length;
    .fix (defs.map fun nd => { nd with body := toBvar x (lvl + def_count) nd.body }) i
  | .prim p => .prim p

def abstract (x: FVarId) (e: LBTerm): LBTerm := toBvar x 0 e

inductive LBType where
| box
| any
| arr (dom codom: LBType)
| app (fn arg: LBType)
| var (i: Nat) -- index of type variable, think about whether this is forwards or backwards
| ind (iid: InductiveId)
| const (kn: Kername)
deriving Inhabited, Repr

structure ConstructorBody where
  name: Ident
  args: List (LocalName × LBType)
  originalArity: Nat -- apparently MetaRocq needs this for erases_one_inductive_body
deriving Inhabited, Repr

-- should be unused
structure ProjectionBody where
  name: Ident
  type: LBType
deriving Repr

inductive AllowedEliminations where
  | IntoSProp
  | IntoPropSProp
  | IntoSetPropSProp
  | IntoAny
deriving Inhabited, Repr

structure TypeVarInfo where
  name: LocalName -- why is this a LocalName and not an ident?
  isLogical: Bool
  isArity: Bool
  isSort: Bool
deriving Repr

structure OneInductiveBody where
  name: Ident
  /-- True iff the inductive lives in Prop. -/
  propositional: Bool := false -- I think, since erasure should remove anything which ends up in Prop
  kelim: AllowedEliminations := .IntoAny
  typeVars: List TypeVarInfo
  ctors: List ConstructorBody
  projs : List ProjectionBody -- This is mainly about giving user-visible names to projections, but `lbox` complains about wellformedness if this is empty.
deriving Inhabited, Repr

inductive RecursivityKind where
  | finite
  | cofinite -- Lean doesn't have primitive coinductive types, but including this here anyway to match the MetaCoq side.
  | bifinite
deriving Repr

structure MutualInductiveBody where
  finite : RecursivityKind := .finite
  /-- Number of parameters to this family of mutually inductive types. -/
  npars : Nat
  bodies : List OneInductiveBody
deriving Repr

structure ConstantBody where
  type: List LocalName × LBType
  body: Option LBTerm
deriving Repr

inductive GlobalDecl where
  | constantDecl (body: ConstantBody)
  | inductiveDecl (body: MutualInductiveBody)
  | typeAliasDecl (body: Option (List TypeVarInfo × LBType))
deriving Repr

-- The first declarations to be added to the context are the deepest/first-consed in the list.

-- comment from MetaRocq's ExAst.v: has_deps specifies whether the environment includes dependencies of this global
-- I think this means it should just always be .true
-- Watch out for the different associativity of × in Rocq and in Lean.
abbrev GlobalDeclarations := List ((Kername × Bool /- has_deps -/) × GlobalDecl)
abbrev Program: Type := GlobalDeclarations × LBTerm
