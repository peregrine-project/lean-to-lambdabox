import LeanToLambdaBox.Basic

open Lean

def InductDummyInfo: Type := sorry
def ConstDummyInfo: Type := sorry

inductive LBType where
  | typeVar (i: Nat)
  | induct (info: InductDummyInfo)
  | const (info: ConstDummyInfo)
  | app (l r: LBType)
  | arrow (l r: LBType)
  | box
  | any
deriving Inhabited

/- Type i and Prop are sorts. -/
def isSort (t: Expr): Bool :=
  match t with
  | .sort .. => true
  | _ => false

/-
An arity is a type of the form ∀ (ai, Ai)… , somesort.
It is the type of some kind of type former or predicate.
-/
def isArity (t: Expr): Bool :=
  match t with
  | .sort .. => true
  | .forallE _ _ body _ => isArity body
  | _ => sorry

/-
A logical type is an arity into Prop (ie the type of a kind of predicate)
or a proposition (ie itself an element of Prop).
Logical types are completely erased.
-/
def isLogical (t: Expr): Bool :=
  sorry

inductive RelKind where
  | typeVar (n: Nat)
  | induct (i: InductDummyInfo)
  | other
deriving Inhabited

def RelKind.toLBType: RelKind -> LBType
| .typeVar n => .typeVar n
| .induct i => .induct i
| .other => .any

structure EraseTypeState where
  /--
  .none if we are not allowed to produce type variables at this level, .some i if we can add type variables
  -/
  nextTypeVar: Option Nat

structure EraseTypeContext where
  varInfo: Std.HashMap FVarId RelKind

abbrev EraseTypeM := ReaderT EraseTypeContext <| StateT EraseTypeState <| MetaM

#check FVarIdMap
/-
Context for this function:
- MetaM context, for inferType and whnf and manipulating expressions
- erasure context: information about free variables (just their LBType?)
- whether to produce new type variables
- if yes, index of fresh type variable (state)
-/
unsafe def eraseType (t: Expr): EraseTypeM LBType := do
  let t' ← Meta.whnf t
  if isLogical t' then
    return .box
  match t' with
  | .fvar id => return (← read).varInfo[id]!.toLBType
  | .forallE name domain codomain binderinfo =>
    -- TODO: adapt Meta context
    -- let _ := Meta.forallBoundedTelescope  t' (.some 1)
    -- etc
    -- (define a forallMonocular?)
    if isLogical domain then
      let erasedCod ← eraseType codomain
      -- todo: add mapping of fvar to .other to eCtx
      return .arrow .box erasedCod
    if not (isArity domain) then
      -- this one in unadapted Meta + erasetype context
      let erasedDom ← eraseType domain
      -- todo: add mapping of fvar to .other to eCtx
      let erasedCod ← eraseType codomain
      return .arrow erasedDom erasedCod 
    -- now domain is a non-logical arity
    -- add a new type variable for this one
    -- add mapping of fvar to the new type var to erasure context
    let erasedCod ← eraseType codomain
    return .arrow .box erasedCod
  | .app l r => return sorry
  | .sort u => return .box
  | .const .. => return .const sorry -- or return .induct sorry!
  | _ => return .any -- TODO: understand which remaining cases are possible
