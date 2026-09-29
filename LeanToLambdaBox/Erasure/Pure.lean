import LeanToLambdaBox.Erasure
import LeanToLambdaBox.Erasure.Collect

/-!
# The pure erasability oracle and the pure backend's monad

`Erasure.Pure.isErasable` decides whether a term is erasable (a proof or a type former) over a list
of declarations, by infer-only retyping and weak-head reduction with the kernel's δ, with fuel.
`Erasure.PureM` is the monad of the backend without `Meta`, whose environment is the program's
closure (`collectDeps`), and `Erasure.PureM.*` are the backend operations that read it.
-/

open Lean

namespace Erasure

/-! ## The pure oracle (S-D, DESIGN.md Q6) -/

namespace Pure

/-- Level substitution without normalisation (kernel-reducible). Reference: PCUIC
`subst_instance` on levels (`MR common/theories/Universes.v:2480 UnivSubst`). -/
def instLevel (ps : List Name) (us : List Level) : Level → Level
  | .zero => .zero
  | .succ l => .succ (instLevel ps us l)
  | .max a b => .max (instLevel ps us a) (instLevel ps us b)
  | .imax a b => .imax (instLevel ps us a) (instLevel ps us b)
  | .param n => match (ps.zip us).find? (·.1 == n) with
    | some (_, u) => u
    | none => .param n
  | .mvar m => .mvar m

/-- Universe instantiation of a term, used by the oracle and by the source semantics' δ rule.
Reference: `subst_instance_constr` (`MR P/PCUICAst.v:404`); its model meaning is
`EraseProof.TrS.instLevels`. -/
def instLevels (ps : List Name) (us : List Level) : Expr → Expr
  | .sort u => .sort (instLevel ps us u)
  | .const c ls => .const c (ls.map (instLevel ps us))
  | .app f a => .app (instLevels ps us f) (instLevels ps us a)
  | .lam n t b bi => .lam n (instLevels ps us t) (instLevels ps us b) bi
  | .forallE n t b bi => .forallE n (instLevels ps us t) (instLevels ps us b) bi
  | .letE n t v b nd => .letE n (instLevels ps us t) (instLevels ps us v) (instLevels ps us b) nd
  | .mdata m e => .mdata m (instLevels ps us e)
  | .proj s i e => .proj s i (instLevels ps us e)
  | e => e

/-- What the oracle reads: the program's declarations. Every reduction of the oracle uses the
kernel's δ, which unfolds every definition and ignores the elaborator attribute `@[irreducible]`.
Reference: the abstract environment `X` passed to `MR E/ErasureFunction.v:894 is_erasableb`,
whose reductions unfold every constant with a body (`MR S/PCUICSafeReduce.v:1839 hnf` at
`RedFlags.default`, δ on: `MR P/PCUICNormal.v:26`). -/
structure Ctx where
  decls : List ConstantInfo

/-- Structural "zero under every assignment": `zero`; `max` of two; `imax` with a right one.
Reference: `Sort.is_propositional` in `MR E/ErasureFunction.v:894 is_erasableb` (Lean: level
`≈ 0`, no SProp; DV-4). -/
def alwaysZero : Level → Bool
  | .zero => true
  | .max a b => alwaysZero a && alwaysZero b
  | .imax _ b => alwaysZero b
  | _ => false

/-- Lookup of a traversal local. Reference: `nth_error Γ` on the PCUIC context (DV-13). -/
def findLocal (ls : List Local) (x : FVarId) : Option Local := ls.find? (·.fvarId == x)

/-- Weak-head normal form: head β (`instantiate1'`), ζ (`letE` and let-bound locals), δ of every
definition (the kernel's δ), `mdata`. Terms may have loose bound variables. Reference: `hnf`
(`MR S/PCUICSafeReduce.v:1839`, `RedFlags.default`), as `sort_of_type` uses `reduce_to_sort`
(`:1853`). -/
def whnf (cx : Ctx) : Nat → List Local → Expr → Except EraseError Expr
  | 0, _, _ => throw (.fuel "whnf")
  | f+1, ls, .app g a => do
    match ← whnf cx f ls g with
    | .lam _ _ b _ => whnf cx f ls (b.instantiate1' a)
    | g' => pure (.app g' a)
  | f+1, ls, .letE _ _ v b _ => whnf cx f ls (b.instantiate1' v)
  | f+1, ls, .mdata _ e => whnf cx f ls e
  | f+1, ls, .fvar x => match findLocal ls x with
    | some ⟨_, _, _, some v⟩ => whnf cx f ls v
    | _ => pure (.fvar x)
  | f+1, ls, e@(.const c us) => match findConst cx.decls c with
    | some (.defnInfo v) =>
      if us.length != v.levelParams.length then pure e
      else whnf cx f ls (instLevels v.levelParams us v.value)
    | _ => pure e
  | _+1, _, e => pure e

/-- Infer-only retyping. Binders are opened de Bruijn style: `Γ` holds the types of the binders
the oracle entered, the traversal's free variables are looked up in `ls`; no names are generated.
Where it needs a Π or a sort it reduces with `whnf`, as type inference in Lean's kernel and in
lean4lean's model does. Reference:
`type_of_typing` (`MR S/PCUICSafeRetyping.v:806`), as called by
`MR E/ErasureFunction.v:894 is_erasableb`. -/
def inferType (cx : Ctx) : Nat → List Local → List Expr → Expr → Except EraseError Expr
  | 0, _, _, _ => throw (.fuel "inferType")
  | _+1, _, Γ, .bvar i => match Γ[i]? with
    | some A => pure (A.liftLooseBVars' 0 (i + 1))
    | none => throw (.outOfFragment "loose bvar")
  | _+1, ls, _, .fvar x => match findLocal ls x with
    | some l => pure l.type
    | none => throw (.outOfFragment "unknown fvar")
  | _+1, _, _, .sort u => pure (.sort (.succ u))
  | _+1, _, _, .const c us => match findConst cx.decls c with
    | some ci =>
      if us.length == ci.levelParams.length then pure (instLevels ci.levelParams us ci.type)
      else throw (.failed "universe arity")
    | none => throw (.outOfFragment "unknown constant")
  | f+1, ls, Γ, .app g a => do
    match ← whnf cx f ls (← inferType cx f ls Γ g) with
    | .forallE _ _ B _ => pure (B.instantiate1' a)
    | _ => throw (.failed "not a function")
  | f+1, ls, Γ, .lam n t b bi => do
    let B ← inferType cx f ls (t :: Γ) b
    pure (.forallE n t B bi)
  | f+1, ls, Γ, .forallE _ t b _ => do
    let .sort u ← whnf cx f ls (← inferType cx f ls Γ t) | throw (.failed "not a type")
    let .sort v ← whnf cx f ls (← inferType cx f ls (t :: Γ) b) | throw (.failed "not a type")
    pure (.sort (.imax u v))
  | f+1, ls, Γ, .letE _ _ v b _ => inferType cx f ls Γ (b.instantiate1' v)
  | f+1, ls, Γ, .mdata _ e => inferType cx f ls Γ e
  | _+1, _, _, _ => throw (.outOfFragment "literal, projection or metavariable")

/-- Arity test after weak-head reduction. Reference: `is_arity` (`MR E/ErasureFunction.v:784`), PCUIC `isArity` (`MR P/PCUICTyping.v:29`). -/
def isArity (cx : Ctx) : Nat → List Local → Expr → Except EraseError Bool
  | 0, _, _ => throw (.fuel "isArity")
  | f+1, ls, T => do
    match ← whnf cx f ls T with
    | .sort _ => pure true
    | .forallE _ _ B _ => isArity cx f ls B
    | _ => pure false

/-- The pure erasability oracle: the type is an arity, or the type's sort is always zero. Every
reduction uses the kernel's δ. Fuel exhaustion is an error, never an answer.
Reference: `MR E/ErasureFunction.v:894 is_erasableb` (`type_of_typing`, `is_arity`,
`sort_of_type`, `Sort.is_propositional`); MC §7.2, Fig. 17. -/
def isErasable (cx : Ctx) (fuel : Nat) (ls : List Local) (e : Expr) :
    Except EraseError Bool := do
  let T ← inferType cx fuel ls [] e
  if ← isArity cx fuel ls T then return true
  match ← whnf cx fuel ls (← inferType cx fuel ls [] T) with
  | .sort u => return alwaysZero u
  | _ => return false

end Pure

/-- Fuel of one oracle call on the pure path (DESIGN.md Q6). Reference: none (DV-17). -/
def oracleFuel : Nat := 2 ^ 20

/-! ## The pure backend (S-D) -/

/-- What the pure backend reads (S-D): the program's closure and the trusted view. Reference: the
abstract environment `X` of `MR E/ErasureFunction.v:989 erase`. -/
structure PureCtx where
  decls : List ConstantInfo
  view : EnvView

/-- The pure backend's state (S-D): the counter that allocates fresh free variables. Reference:
none (MetaRocq's `erase` is de Bruijn, DV-13). -/
structure PureState where
  next : Nat := 0

/-- The pure backend (S-D). Reference: none (MetaRocq's `erase` is a pure Equations function). -/
abbrev PureM := ReaderT PureCtx (StateT PureState (Except EraseError))

/-- Run a traversal action at the pure backend. Reference: none. -/
def EraseT.runPure {α} (x : EraseT PureM α) (st : ErasureState) (tc : TravCtx) (pc : PureCtx)
    (ps : PureState) : Except EraseError ((α × ErasureState) × PureState) :=
  (((x.run st).run tc).run pc).run ps

namespace PureM

/-- S-D: `findConst? := findConst decls`. Reference: `lookup_env`
(`MR common/theories/Environment.v:483`). -/
def findConst? (c : Name) : PureM (Option ConstantInfo) := return findConst (← read).decls c

/-- S-D: fresh free variables from the counter `next`. Reference: none (DV-13). -/
def freshFVarId : PureM FVarId :=
  modifyGet fun s => (⟨.num `_pure s.next⟩, { s with next := s.next + 1 })

/-- S-D: `instantiate1 := Expr.instantiate1'` (lean4lean's pure model, `l4l
Verify/Axioms.lean:404`, a definition; avoids the `instantiate1_eq` axiom). Reference: none. -/
def instantiate1 (b a : Expr) : Expr := b.instantiate1' a

/-- S-D: the oracle, on the traversal's locals, with `oracleFuel`. Reference:
`MR E/ErasureFunction.v:894 is_erasableb`. -/
def isErasable (ls : List Local) (e : Expr) : PureM Bool := do
  let pc ← read
  match Pure.isErasable ⟨pc.decls⟩ oracleFuel ls e with
  | .ok b => pure b
  | .error err => throw err

/-- S-D: no `casesOn` on the pure path (the fragment has no inductives). Reference: none. -/
def casesInfo? (_ : Name) : PureM (Option Lean.CasesInfo) := pure none

/-- S-D: no constructors on the pure path. Reference: none. -/
def ctorArity? (_ : Name) : PureM (Option Nat) := pure none

end PureM

end Erasure
