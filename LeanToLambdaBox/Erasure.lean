import Lean.Compiler.LCNF.ToLCNF
import Lean.Meta

import LeanToLambdaBox.Basic
import LeanToLambdaBox.Printing
import Std.Data.HashMap
import LeanToLambdaBox.TypedML
import LeanToLambdaBox.Names
import LeanToLambdaBox.ToLambdaBox
import LeanToLambdaBox.Constructors
import Batteries.CodeAction

open Lean
open Lean.Compiler.LCNF

namespace Erasure

def initialConfig: Config := { constructors := .value }

structure ExprContext where
  lctx: LocalContext
  locals: LocalValueContext
  lookup: Std.HashMap FVarId locals.Id -- invariant: every fvarid in the localcontext is mapped to a value. Include as proof?

def ExprContext.empty: ExprContext where
  lctx := .empty
  locals := .empty
  lookup := ∅

def ExprContext.extend
  (ctx: ExprContext)
  (binderName: Name)
  (binderType: Expr)
  (binderInfo: BinderInfo)
  (body: Expr)
  : CoreM ({ ctx': ExprContext // ctx.locals.Extension ctx'.locals } × Expr)
  := do
  let fvarid ← mkFreshFVarId;
  let lctx := ctx.lctx.mkLocalDecl fvarid binderName binderType binderInfo;
  let ⟨locals, ext⟩ := ctx.locals.extend;
  let lookup: Std.HashMap FVarId locals.Id := ctx.lookup.map (fun _ => ext.weakenId) |>.insert fvarid ext.newId;
  return (⟨{ lctx, locals, lookup }, ext⟩, body.instantiate1 (.fvar fvarid))

/-- Information about an fvar in the context of conversion of a Lean Expr to a TypedML type. -/
inductive TypeFVarKind (tvars: TypeVarContext): Type where
  | lifted (id: tvars.Id)
  /--
  The binding of this fvar could not be lifted to a prenex type variable,
  either because it is not a type or an arity
  or because it is bound in a non-prenex position.
  -/
  | unrepresentable

def TypeFVarKind.toType: TypeFVarKind tvars -> TypedML.TType tvars aliases globals
| .lifted id => .typeVar id
| .unrepresentable => .unrepresentable

/--
Context used by `eraseType`.
Note that `eraseTypeToplevel` does not only read this but also adds new tvars and extends the lookup table.
-/
structure TypeContext where
  lctx: LocalContext
  tvars: TypeVarContext
  lookup: Std.HashMap FVarId (TypeFVarKind tvars)

def TypeContext.empty: TypeContext where
  lctx := .empty
  tvars := .empty
  lookup := ∅

-- This is very similar to ExprContext.extend. Generalize?
def TypeContext.extend
  (ctx: TypeContext)
  (binderName: Name)
  (binderType: Expr)
  (binderInfo: BinderInfo)
  (lift: Bool)
  (body: Expr)
  : CoreM ({ ctx': TypeContext // ctx.tvars.MultiExtension ctx'.tvars } × Expr)
  := do
  let fvarid ← mkFreshFVarId;
  let lctx := ctx.lctx.mkLocalDecl fvarid binderName binderType binderInfo;
  let body := body.instantiate1 (.fvar fvarid);
  if lift then 
    let ⟨tvars, ext⟩ := ctx.tvars.extend;
    let lookup :=
      ctx.lookup.map (fun _ => fun | .unrepresentable => .unrepresentable | .lifted id => .lifted (ext.weakenId id))
      |>.insert fvarid (if lift then .lifted ext.newId else .unrepresentable)
    ;
    return (⟨{ lctx, tvars, lookup }, ext.toMulti⟩, body)
  else
    return (⟨{ ctx with lctx }, .trivial⟩, body)

structure State (pctx: ProgramContext) where
  lookupGlobals: Std.HashMap Name pctx.globals.Id := ∅

def State.weaken (ext: pctx.MultiExtension pctx'): State pctx -> State pctx'
| ⟨m⟩ => ⟨m.map (fun _ gid => ext.globals.weakenId gid) ⟩

abbrev Expression := TypedML.Expression initialConfig
abbrev Program (pctx: ProgramContext) := TypedML.Program initialConfig pctx.aliases pctx.globals pctx.inductives

structure EraseExprResult (oldpctx: ProgramContext) (locals: LocalValueContext) where
  pctx: ProgramContext
  ext: oldpctx.MultiExtension pctx
  p: Program pctx
  s: State pctx
  e: Expression pctx.globals pctx.inductives locals

structure EraseTypeResult (oldpctx: ProgramContext) (oldtvars: TypeVarContext) where
  pctx: ProgramContext
  pext: oldpctx.MultiExtension pctx
  tvars: TypeVarContext
  text: oldtvars.MultiExtension tvars
  p: Program pctx
  t: TypedML.TType tvars pctx.aliases pctx.inductives

def easyNow (p: Program pctx) (s: State pctx) (e: Expression pctx.globals pctx.inductives locals): EraseExprResult pctx locals :=
  { pctx, ext := .trivial, p, s, e }

abbrev M := ExceptT String <| CoreM

def throw {α} := @throwThe String M _ α

def runMeta (lctx: LocalContext) (x: MetaM α) [Monad m] [MonadLiftT CoreM m]: m α := do return (← x.run { lctx }).fst

/--
Whether inhabitants of `t`, which is assumed to represent a type, can be erased.
`t` itself, being a type, can always be erased in a term.
-/
def isErasableType (t: Expr): MetaM Bool := do
    -- Erase evidence of propositions
    -- ToLCNF includes an explicit check for isLcProof, but I think the type information should be enough to erase those here.
    if (← Meta.isProp t) then
      return true
    -- Erase types and type formers
    if (← Meta.isTypeFormerType t) then
      return true
    return false

/-- Whether the term `e` can be erased inside a computationally meaningful expression. -/
def isErasable (e: Expr): MetaM Bool := do
    let type ← Meta.inferType e;
    isErasableType type

/-- Whether a bound variable of type `t` represents a type or type former that can be lifted to a prenex type variable. -/
def canLiftToTypeVar (t: Expr): Bool :=
  match t with
  | .forallE _ body .. => canLiftToTypeVar body
  | .sort u => not u.isAlwaysZero
  | _ => false

set_option linter.unusedVariables false in
mutual

-- partial because when going under lambdas we rewrite the body to guarantee the locally nameless invariant
partial def eraseExpr
  (e: Expr)
  (p: Program pctx)
  (s: State pctx)
  (ectx: ExprContext)
  : M (EraseExprResult pctx ectx.locals)
  := do
  if ← (runMeta ectx.lctx (isErasable e)) then
    return easyNow p s .box
  match e with
  | .sort u => throw "unexpected sort, should be erased"
  | .forallE binderName binderType body binderInfo => throw "unexpected forall, should be erased"
  | .mvar mvarId => throw "unexpected metavariable"
  | .bvar deBruijnIndex => throw "the locally nameless invariant should ensure we never see this"
  | .mdata _ expr => eraseExpr expr p s ectx
  | .lit _ => throw "literal not yet implemented"
  | .proj typeName idx struct => throw "projections not yet implemented"
  | .letE declName type value body nondep => throw "let not yet implemented"
  | .const declName us =>
    if Lean.isCasesOnRecursor (← getEnv) declName then
      throw "casesOn not yet implemented"
    else match ← getConstInfo declName with
    | .ctorInfo _ => throw "constructors not yet implemented"
    | .recInfo _ => throw "recursors not implemented"
    | .inductInfo _ => throw "unexpected inductive type, should be erased"
    | .thmInfo _ => throw "unexpected theorem, should be erased"
    | .quotInfo _ => throw "quotVal not (yet?) implemented"
    | .opaqueInfo _ => throw  "opaque constants not yet implemented"
    | .axiomInfo _ => throw  "axioms not yet implemented"
    | .defnInfo val =>
      let ⟨pctx, ext, p, s, gid⟩ ← getGlobal p s val;
      return { pctx, ext, p, s, e := .global gid } 
  | .app fn arg =>
    let fnres ← eraseExpr fn p s ectx;
    let argres ← eraseExpr arg fnres.p (fnres.s) ectx;
    return {
      pctx := argres.pctx,
      ext := fnres.ext.compose argres.ext,
      p := argres.p,
      s := argres.s,
      e := .app (argres.ext.weakenExpression fnres.e) argres.e
    }
  | .lam binderName binderType body binderInfo =>
    let (⟨bodyectx, ext⟩, body) ← ectx.extend binderName binderType binderInfo body;
    let bodyres ← eraseExpr body p s bodyectx;
    return { bodyres with e := .lambda (← binderName.toLocalName) ext bodyres.e }

  | .fvar fvarId =>
    let id: ectx.locals.Id ← Option.getDM (ectx.lookup[fvarId]?) (throw "did not find fvarid");
    let e := .local id;
    return easyNow p s e

where
  -- TODO: handle recursion (check val.all)
  getGlobal (p: Program pctx) (s: State pctx) (val: DefinitionVal): M ((pctx': ProgramContext) ×' pctx.MultiExtension pctx' ×' Program pctx' × State pctx' × pctx'.globals.Id) := do
    match s.lookupGlobals[val.name]? with
    | .some gid => return ⟨pctx, .trivial, p, s, gid⟩
    | .none =>
      let ⟨pctx', ext, tvars, p', t⟩ ← eraseType p val.type;
      let res ← eraseExpr val.value p' (s.weaken ext) .empty;
      let ⟨gctx'', gext'⟩ := res.pctx.globals.extend;
      let pctx'' := { res.pctx with globals := gctx'' };
      let p'': Program pctx'' := .valueDecl res.p (← val.name.toGlobalName) gext' res.e (res.ext.weakenType .trivial t);
      let gid := gext'.newId;
      let ext': res.pctx.MultiExtension pctx'' := { aliases := .trivial, inductives := .trivial, globals := gext'.toMulti };
      let s'' := { lookupGlobals := res.s.weaken ext'|>.lookupGlobals |>.insert val.name gid }
      return ⟨pctx'', (ext.compose res.ext).compose ext', p'', s'', gid⟩

  eraseType
    {pctx}
    (p: Program pctx)
    (t: Expr)
    : M (
      (pctx': ProgramContext)
      ×' pctx.MultiExtension pctx'
      ×' (tvars: TypeVarContext)
      × Program pctx'
      × TypedML.TType tvars pctx'.aliases pctx'.inductives
    )
    := do
    let res ← eraseTypeToplevel p .empty t;
    return ⟨res.pctx, res.pext, res.tvars, res.p, res.t⟩

  /-- Convert a Lean type to a TypedML type, lifting quantification over types and type formers to prenex type variables. -/
  eraseTypeToplevel {pctx} (p: Program pctx) (tctx: TypeContext) (t: Expr): M (EraseTypeResult pctx tctx.tvars) := do
    let t ← runMeta tctx.lctx (Meta.whnf t); -- TODO: think about which transparency setting is desired here and at other applications of whnf
    -- sanity check
    if ← runMeta tctx.lctx (isErasableType t) then throw "should not be erasing the type of an erasable term at toplevel"
    match t with
    | .forallE binderName binderType body binderInfo =>
      let ⟨pctx', pext, p', domain⟩ ← eraseTypeInner p tctx binderType;
      let lift := canLiftToTypeVar binderType;
      let (⟨tctx', text⟩, body) ← tctx.extend binderName binderType binderInfo lift body
      let codomainres ← eraseTypeToplevel p' tctx' body;
      let text := text.compose codomainres.text;
      return { codomainres with
        pext := pext.compose codomainres.pext,
        text,
        t := .arrow (codomainres.pext.weakenType text domain) codomainres.t
      }

    | _ =>
      let ⟨pctx, pext, p, t⟩ ← eraseTypeInner p tctx t;
      return { pctx, pext, p, tvars := tctx.tvars, text := .trivial, t }
    
  /-- Convert a Lean Type to a TypedML type without creating new type variables. -/
  eraseTypeInner
    {pctx}
    (p: Program pctx)
    (tctx: TypeContext)
    (t: Expr)
    : M (
      (pctx': ProgramContext)
      ×' pctx.MultiExtension pctx'
      ×' Program pctx'
      × TypedML.TType tctx.tvars pctx'.aliases pctx'.inductives
    )
    := do 
    let t ← runMeta tctx.lctx (Meta.whnf t);
    if ← runMeta tctx.lctx (isErasableType t) then
      return ⟨pctx, .trivial, p, .erased⟩
    -- Here, `t` is either an fvar, an application of a type former to some types, or a dependent arrow (forall).
    t.withApp (fun hd args => do
      match hd with
      | .bvar deBruijnIndex => throw "unexpected bvar, the locally nameless invariant should ensure we never see this"
      | .letE declName type value body nonDep => throw "unexpected let in whnf"
      | .proj typeName idx struct => throw "unexpected projection in whnf"
      | .sort u => throw "unexpected sort, should be erasable"
      | .app fn arg => throw "unexpected .app, should be consumed by withApp"
      | .lit l => throw "unexpected literal, expected type former"
      | .mvar mvarId => throw "unexpected metavariable"
      | .lam binderName binderType body binderInfo =>
        if args.isEmpty then
          throw "unexpected lambda, expected type"
        else
          throw "unexpected applied lambda in whnf"
      | .mdata data expr =>
        -- Instead of taking `expr` as head, reapply `expr` to all arguments then withApp down again to make sure we aren't missing applications.
        -- For example, if `t` was `.app (.mdata data (.app f a)) b`, `(hd, args)` should be `(f, #[a, b])` and not `(.app f a, #[b])`.
        eraseTypeInner p tctx (mkAppN expr args)
      | .fvar fvarId =>
        match tctx.lookup[fvarId]? with
        | .none => throw "unknown fvarId"
        | .some k => return ⟨pctx, .trivial, p, k.toType⟩
      | .const declName us =>
        if let .inductInfo val ← getConstInfo declName then
          throw "inductives not yet implemented"
        else
          throw "type aliases not yet implemented"
      | .forallE binderName binderType body binderInfo =>
        let ⟨pctx', pext, p', domain⟩ ← eraseTypeInner p tctx binderType;
        let fvarId ← mkFreshFVarId;
        let lctx' := tctx.lctx.mkLocalDecl fvarId binderName binderType binderInfo;
        let body := body.instantiate1 (.fvar fvarId)
        let ⟨pctx'', pext', p'', codomain⟩ ← eraseTypeInner p' { tctx with lctx := lctx' } body;
        return ⟨pctx'', pext.compose pext', p'', .arrow (pext'.weakenType .trivial domain) codomain⟩
    )
                                                     
end

/-
structure ErasureState: Type where
  aliases: TypeAliasContext
  globals: GlobalValueContext
  inductives: InductiveContext
  p: TypedML.Program initialConfig aliases globals inductives
  aliasesMap: Std.HashMap Name aliases.Id
  globalsMap: Std.HashMap Name globals.Id
  inductivesMap: Std.HashMap Name ((mid: inductives.MutualInductiveId) × mid.InductiveId)

def ErasureState.empty: ErasureState where
  aliases := .empty
  globals := .empty
  inductives := .empty
  p := .empty
  aliasesMap := ∅
  globalsMap := ∅
  inductivesMap := ∅

structure ErasureContext: Type where
  lctx: LocalContext := {}

abbrev EraseM := ReaderT ErasureContext <| StateT ErasureState CoreM
-/

/-
def run (x : EraseM α): CoreM α :=
  x |>.run {} |>.run

/-- Run an action of MetaM in EraseM using EraseM's local context of Lean types. -/
@[inline] def liftMetaM (x : MetaM α) : EraseM α := do
  x.run' { lctx := (← read).lctx }

def fvar_to_name (x: FVarId): EraseM BinderName := do
  let n := (← read).lctx.fvarIdToDecl |>.find! x |>.userName
  let s: String := n.toString
  -- check if s is ASCII graphic, otherwise the λbox parser will complain
  if s.all (fun c => 33 <= c.toNat ∧ c.toNat < 127) then
    return .named n.toString
  else
    return .anon

/-- Similar to Meta.withLocalDecl, but in EraseM.
    k will be passed some fresh FVarId and run in a context in which it is bound. -/
def withLocalDecl (n: Name) (type: Expr) (bi: BinderInfo) (k: FVarId -> EraseM α): EraseM α := do
  let fvarid <- mkFreshFVarId;
  withReader (fun ctx => { ctx with lctx := ctx.lctx.mkLocalDecl fvarid n type bi }) (k fvarid)

/-- Like Meta.withLetDecl. -/
def withLocalDef (n: Name) (type val: Expr) (nd: Bool) (k: FVarId -> EraseM α): EraseM α := do
  let fvarid <- mkFreshFVarId;
  withReader (fun ctx => { ctx with lctx := ctx.lctx.mkLetDecl fvarid n type val nd }) (k fvarid)

/--
A version of Meta.lambdaTelescope that
- unpacks exactly one layer of lambda-abstraction (ie does not telescope)
- works in EraseM instead of (any monad from which we can control) MetaM.
- yields an FVarId instead of an Expr for the bound variable
Panics if applied to something which is not of the form .lambda ..
-/
def lambdaMonocular {α} [Inhabited α] (e: Expr) (k: FVarId -> Expr -> EraseM α): EraseM α := do
  let .lam binderName type body bi := e | unreachable!
  withLocalDecl binderName type bi (fun fvarid => k fvarid <| body.instantiate1 (.fvar fvarid))

/--
Destructures a let-expression for handling by a continuation in an appropriate context.
The continuation gets an FVarId for the bound variable and bound value and body as expressions.
Panics if applied to an expression which is not of the form .letE ..
-/
def letMonocular {α} [Inhabited α] (e: Expr) (k: FVarId -> Expr -> Expr -> EraseM α): EraseM α := do
  let .letE binderName type val body nd := e | unreachable!
  withLocalDef binderName type val nd (fun fvarid => k fvarid val (body.instantiate1 (.fvar fvarid)))

/--
Destructures a type expression of the form `∀ a: A, B`,
running the continuation on the body B (with DB variable 0 suitably instantiated with some fvar `a`) and the bound fvar,
in a context with `a: A`.
Panics if applied to an expression which is not of the form .forallE ..
-/
def forallMonocular {α} [Inhabited α] (t: Expr) (k: FVarId -> Expr -> EraseM α) := do
  let Expr.forallE binderName type body bi := t | unreachable!
  withLocalDecl binderName type bi (fun fvarid => k fvarid <| body.instantiate1 <| .fvar fvarid)

/-- Remove the ._unsafe_rec suffix from a Name if it is present. -/
def remove_unsafe_rec (n: Name): Name := Compiler.isUnsafeRecName? n |>.getD n
      
/--
This is used to detect if a definition is recursive.
Occurrences of `name` in types may or may not be detected, but I don't think this matters in practice.
-/
def name_occurs (name: Name) (e: Expr): Bool :=
  match e with
  | .const n' .. => name == remove_unsafe_rec n'
  | .bvar .. | .fvar .. | .mvar .. | .sort .. | .forallE .. /- these are types, so ignoring -/ | .lit .. => .false
  | .lam _ _ e _ | .mdata _ e | .proj _ _ e => name_occurs name e
  | .app a b | .letE _ _ a b _ => name_occurs name a || name_occurs name b

/--
Replace nested occurrences of `unsafeRec` names with the safe ones.
Copied over from ToDecl.lean because it is private there.
I think this doesn't actually need to be in CoreM and could just use `Expr.replace`.
-/
def replaceUnsafeRecNames (value : Expr) : CoreM Expr :=
  Core.transform value fun e =>
    match e with
    | .const declName us =>
      if let some safeDeclName := Compiler.isUnsafeRecName? declName then
        return .done (.const safeDeclName us)
      else
        return .done e
    | _ => return .continue

/--
Honor @[macro_inline] directives, inline auxiliary matchers, remove _unsafe_rec suffixes and perform csimp replacements.
This is lifted from LCNF/ToDecl.lean .
It processes the whole expression tree, so the code here doesn't have to be at the start of visitExpr,
and it is sufficient to run it before entering the "toplevel" expression and the definition of a dependency in the environment.

This may make the expression ill-typed if some dependent type relies on the implementation of functions affected by csimp.
-/
def prepare_erasure (e: Expr): EraseM Expr := do
  let mut e := e
  e ← replaceUnsafeRecNames e
  e ← macroInline e
  e ← inlineMatchers e
  -- According to the comment in ToDecl.lean, inlined matchers might contain occurrences of `ite` and `dite`.
  -- I'm sort of assuming that inlining matchers doesn't expose arbitrary macro_inline stuff which might itself contain more matchers etc.
  -- Just `ite` and `dite` are fine, their bodies are just a Decidable.casesOn.
  -- It's important to inline them because otherwise both arms of the conditional will be strictly evaluated.
  e ← macroInline e
  -- not doing csimp replacements here, do them at the leaf level.
  pure e

/--
Copied over from toLCNF, then quite heavily pruned and modified.

This not only erases the expression but also gives a context with all necessary global declarations of inductive types and top-level constants.
-/
partial def erase (e : Expr): CoreM Program := do
  let p ← run (do visitExpr (← prepare_erasure e))
  return p

where
  /- Proofs (terms whose type is of type Prop) and type formers/predicates are all erased. -/
  visitExpr (e : Expr) : EraseM Program := do
    if (← liftMetaM <| isErasable e) then
      return .box
    match e with
    | .app ..      => visitApp e
    | .const ..    => visitApp e -- treat as an application to zero args to handle special constants
    | .proj s i e  => visitProj s i e
    | .mdata _ e   => visitExpr e -- metadata is ignored
    | .lam ..      => visitLambda e
    | .letE ..     => visitLet e
    | .lit l     => visitLiteral l
    | .fvar fvarId => pure (.fvar fvarId)
    | .forallE .. | .mvar .. | .bvar .. | .sort ..  => unreachable!

  visitLiteral (l: Literal): EraseM LBTerm := do
    match (← read).config.nat, l with
    | .peano, .natVal 0 => visitConstructor ``Nat.zero #[]
    | .peano, .natVal (n+1) => visitConstructor ``Nat.succ #[.lit (.natVal n)]
    | .machine, .natVal n =>
      if n <= BitVec.intMax 63 then
        pure <| .prim ⟨.primInt, n⟩ 
      else
        panic! "Nat literal not representable as a 63-bit signed integer."
    | _, .strVal _ => panic! "String literals not supported."

  /-
  The original in ToLCNF also handles eta-reduction of implicit lambdas introduced by the elaborator.
  This is beyond the scope of what I want to do here for the moment.
  -/
  visitLambda (e : Expr) : EraseM LBTerm :=
    lambdaMonocular e (fun fvarid body => do mkLambda fvarid (← visitExpr body))

  visitLet (e : Expr): EraseM LBTerm :=
    /-
    In the original ToLCNF, if the bound value is erasable then the let-binding is not generated,
    since all occurrences of the variable must be erased anyway.
    Keep this optimization?
    -/
    letMonocular e (fun fvarid val body => do mkLetIn fvarid (← visitExpr val) (← visitExpr body))

  visitProj (s : Name) (i : Nat) (e : Expr) : EraseM LBTerm := do
    let .inductInfo indinfo ← getConstInfo s | unreachable!
    let (indid, argmasks) ← register_inductive indinfo
    -- i is the index among all fields, but some are erased
    let fieldIdx := argmasks[0]![:i].toArray.count .keep
    let projinfo: ProjectionInfo := { indType := indid, paramCount := indinfo.numParams, fieldIdx }
    return .proj projinfo (← visitExpr e)

  /--
  When visiting expressions of the form f g, it is not sufficient to just recurse on f and g.
  visitApp will explore an expression "in depth" to get the leftmost applicand,
  then handle the case where it is a constant specially; otherwise, straightforward recursion is correct.
  Contrary to the original ToLCNF, I have removed CSimp.replaceConstants here and assume it will just be run once before erasure.
  -/
  visitApp (e : Expr) : EraseM LBTerm :=
    -- The applicand is a constant, check for special cases
    if let .const .. := e.getAppFn then
      visitConstApp e
    -- The applicand is not a constant, so we just normally recurse.
    else
      e.withApp fun f args => do visitAppArgs (← visitExpr f) args

  /-- A constant which is being defined in the current mutual block will be replaced with a free variable (to be bound by mkDef later).
  Other constants should previously have been added to the (λbox-side) context and will just be translated to Rocq kernames. -/
  visitConst (e: Expr): EraseM LBTerm := do
    let .const declName _ := e | unreachable!
    if let .some id := (← read).fixvars.bind (fun hmap => hmap[declName]?) then
      return .fvar id
    return .const (← get_constant_kername declName)
    
  /--
  Special handling of
  - casesOn (will be eta-expanded)
  - constructors (will be eta-expanded)
  -/
  visitConstApp (e: Expr): EraseM LBTerm :=
    e.withApp fun f args => do
      let .const declName _ := f | unreachable!
      if let some casesInfo ← getCasesInfo? declName then
        /-
        I have removed the check for whether there is an [implemented_by] annotation.
        This is only relevant for the implementation of computed fields, such as for hash consing in the `Expr` type.
        -/
        withAppEtaToMinArity e casesInfo.arity (fun _ args => visitCases casesInfo args)
      else if let some arity ← getCtorArity? declName then
        withAppEtaToMinArity e arity (fun _ args => visitConstructor declName args)
      /-
      Removed special check for automatically defined projection functions out of structures.
      In toLCNF these are inlined and β-reduced, unless the projection is out of a builtin type of the runtime.
      The definition seems to just be def spam.egg := fun s: spam => s.1,
      so after β-reduction this becomes a primitive projection.
      Left these to be inlined by Malfunction.
      -/
      else
        visitAppArgs (← visitConst f) args

  visitConstructor (ctorname: Name) (args: Array Expr): EraseM LBTerm := do
    let .ctorInfo info ← getConstInfo ctorname | unreachable!
    let cidx := info.cidx
    let .inductInfo indinfo ← getConstInfo info.induct | unreachable!
    let (indid, argmasks) ← register_inductive indinfo
    let argmask := argmasks[cidx]!

    if isExtern (← getEnv) ctorname && (← read).config.extern == .preferAxiom then
      -- Axiom has been added by register_inductive.
      return ← visitAppArgs (.const <| toKername ctorname) args

    match (← read).config.nat, ctorname with
    | .machine, ``Nat.zero =>
      unless args.size == 0 do
        panic s!"Nat.zero applied to {args.size} arguments."
      return ← visitLiteral (.natVal 0)
    | .machine, ``Nat.succ =>
      unless args.size == 1 do
        panic s!"Nat.succ applied to {args.size} arguments."
      let nat_add ← visitConst (.const ``Nat.add [])
      return ← visitAppArgs nat_add #[args[0]!, .lit (.natVal 1)]
    | .machine, _
    | .peano, _ => pure ()

    let param_args := args[:info.numParams]
    let field_args := args[info.numParams:info.numParams + info.numFields]
    let extra_args := args[info.numParams + info.numFields:]
    let filtered_args := param_args.toArray ++ (filter argmask field_args) ++ extra_args.toArray
    -- Instead of making this a "real" use of .construct, in the stage of λbox I am targeting constructor application is function application
    visitAppArgs (.construct indid cidx []) filtered_args

  /-- Normal application of a function to some arguments. -/
  visitAppArgs (f : LBTerm) (args : Array Expr) : EraseM LBTerm := do
      args.foldlM (fun e arg => do return LBTerm.app e (← visitExpr arg)) f

  visitCases (casesInfo : CasesInfo) (args: Array Expr) : EraseM LBTerm := do
    let discr_nt ← visitExpr args[casesInfo.discrPos]!
    let typeName := casesInfo.declName.getPrefix
    
    -- If we are using machine Nats then the inductive casesOn will not work.
    let mut ret: LBTerm ← (match typeName, (← read).config.nat with
    | ``Nat, .machine => do
      /-
      Compile this to "let n = discr in Bool.casesOn (Nat.beq n 0) (succ_case (n - 1)) zero_case".
      The let-binding is necessary to avoid double evaluation of the discriminee.
      I'm doing part of this this on LBTerms instead of constructing Exprs because visitExpr
      assumes expressions are well-typed, which wouldn't be the case naïvely as (n - 1).succ is not defeq to n.
      Using casts to make the dependent types typecheck would be an option now that Eq.rec is added to the axioms.
      -/
      let zero_arm := args[casesInfo.altsRange.lower]!
      let zero_nt ← visitExpr zero_arm
      let succ_arm := args[casesInfo.altsRange.lower + 1]! -- a function with one argument of type Nat
      let bool_indval := (← getConstInfo ``Bool).inductiveVal!
      let (bool_indid, _) ← register_inductive bool_indval
      withLocalDecl `n (.const ``Nat []) .default (fun n_fvar => do
        let gtz_arm := Expr.app succ_arm <| mkAppN (.const ``Nat.sub []) #[.fvar n_fvar, .lit (.natVal 1)] -- no longer takes an argument, n_fvar is free here
        let gtz_nt: LBTerm ← visitExpr gtz_arm
        let condition: LBTerm ← visitExpr <| mkAppN (.const ``Nat.beq []) #[.fvar n_fvar, .lit (.natVal 0)]
        let case_nt: LBTerm := .case (bool_indid, 0) condition [← mkAlt [] gtz_nt, ← mkAlt [] zero_nt]
        mkLetIn n_fvar discr_nt case_nt
      )
    | ``Int, .machine => do
      /-
      Compile this to "let n = discr in Bool.casesOn (Nat.ble 0 n) (negsucc_case (-(n+1))) (ofnat_case n)".
      The use of Nat.ble instead of using Int.decLE and Decidable.casesOn is possible because Int and Nat both become Z.t,
      and Nat.ble becomes Z.leq.
      We build `LBTerm`s directly instead of building expressions and using visitExpr because visitExpr assumes typability.
      In effect, we can silently cast between Int and Nat.
      -/
      let ofnat_fun := args[casesInfo.altsRange.lower]!
      let negsucc_fun := args[casesInfo.altsRange.lower + 1]!
      let bool_indval := (← getConstInfo ``Bool).inductiveVal!
      let (bool_indid, _) ← register_inductive bool_indval
      withLocalDecl `n (.const ``Nat []) .default (fun n_fvar => do
        let ofnat_nt: LBTerm := .app (← visitExpr ofnat_fun) (.fvar n_fvar)
        let negsucc_nt: LBTerm :=
          .app (← visitExpr negsucc_fun)
          <| .app (← visitExpr (.const ``Int.neg []))
          <| .app (← visitExpr (.const ``Nat.succ [])) (.fvar n_fvar)
        let condition: LBTerm ← visitExpr <| mkAppN (.const ``Nat.ble []) #[.lit (.natVal 0), .fvar n_fvar]
        let case_nt: LBTerm := .case (bool_indid, 0) condition [← mkAlt [] negsucc_nt, ← mkAlt [] ofnat_nt]
        mkLetIn n_fvar discr_nt case_nt
      )
    | _, _ => do
      let .inductInfo indVal ← getConstInfo typeName | unreachable!
      let (indid, argmasks) ← register_inductive indVal
      let mut alts := #[]
      for i in casesInfo.altsRange, numFields in casesInfo.altNumParams /- which should proobably be called altNumFields -/, argmask in argmasks do
        let alt ← visitAlt numFields argmask args[i]!
        alts := alts.push alt
      pure <| LBTerm.case (indid, indVal.numParams) discr_nt alts.toList
    )

    -- The casesOn function may be overapplied, so handle the extra arguments.
    for arg in args[casesInfo.arity:] do
      ret := .app ret (← visitExpr arg)
    return ret

  /--
  Visit a `matcher`/`casesOn` alternative.
  On the Lean side, e should be a function taking numFields arguments.
  For λbox, I think we only need the body, as the LBTerm.cases constructor handles the bindings.
  -/
  visitAlt (numFields : Nat) (argmask: ConstructorArgMask) (e : Expr) : EraseM (List BinderName × LBTerm) := do
    lambdaOrIntroToArity e (← liftMetaM <| Meta.inferType e) numFields fun e fvarids => do
      mkAlt (filter argmask fvarids.toArray).toList (← visitExpr e)

  get_constant_kername (n: Name): EraseM Kername := do
    if let .some kn := (← get).constants.get? n then
      return kn
    else
     visitMutual n
     return (← get).constants[n]!

  /--
  Add all the declarations in the Lean-side mutual block of `name` to the global_declarations,
  and add their mappings to kernames to the erasure state.
  -/
  visitMutual (name: Name): EraseM Unit := do
    -- Use original recursive definition, not the elaborated one with recursors, if available.
    let ci := (← Compiler.LCNF.getDeclInfo? name).get!
    let names := ci.all -- possibly these are ._unsafe_rec
    let single_decl := names.length == 1
    -- A single declaration may have to be output as an axiom.
    if single_decl then
      match ci.value? (allowOpaque := true), isExtern (← getEnv) name, (← read).config.extern with
      | .none, _, _ =>
        logInfo s!"No value found for name {name}, emitting axiom."
        return ← addAxiom name
      | .some _, false, _ => pure ()
      | .some _, true, .preferAxiom =>
        logInfo s!"Name {name} has a value but is tagged @[extern], emitting axiom."
        return ← addAxiom name
      | .some _, true, .preferLogical =>
        logInfo s!"Name {name} is tagged @[extern] but has a value, using value."
        pure ()

    let nonrecursive: Bool := single_decl && !(name_occurs name (ci.value! (allowOpaque := true)))
    if nonrecursive
    then -- translate into a single nonrecursive constant declaration
      let e: Expr := ci.value! (allowOpaque := true)
      let t ← withReader (fun env => { env with fixvars := .none }) do
        pure (← visitExpr (← prepare_erasure e))
      let kn := toKername name
      modify (fun s => { s with constants := s.constants.insert name kn, gdecls := s.gdecls.cons (kn, .constantDecl <| ⟨.some t⟩) })
    else -- translate into a mutual fixpoint declaration
      let ids ← names.mapM (fun _ => mkFreshFVarId)
      let fixvarnames := names.map remove_unsafe_rec
      withReader (fun env => { env with fixvars := fixvarnames |>.zip ids |> Std.HashMap.ofList |> .some }) do
        let defs: List FixDef ← names.mapM (fun n => do
          let ci ← getConstInfo n -- here n is directly from the above ci.all, possibly _unsafe_rec
          let e: Expr := ci.value! (allowOpaque := true)
          -- TODO: eta-expand fixpoints? (I think this must be done, unsure how far)
          let t: LBTerm ← visitExpr (← prepare_erasure e)
          mkDef (remove_unsafe_rec n) fixvarnames t
        )
        for (n, i) in fixvarnames.zipIdx do
          let kn := toKername n
          modify (fun s => { s with constants := s.constants.insert n kn, gdecls := s.gdecls.cons (kn, .constantDecl ⟨.some <| .fix defs i⟩) })

inductive MLType: Type where
  | arrow (a b: MLType)
  | Z
  | unit
  | bool
  | list (a: MLType)
deriving Inhabited

def MLType.toString: MLType -> String
  | arrow a b => s!"{toStringProtected a} -> {b.toString}"
  | Z => "Z.t"
  | unit => "unit"
  | bool => "bool"
  | list a => s!"{a.toString} list"
where
  toStringProtected: MLType -> String
  | arrow a b => s!"({toStringProtected a} -> {b.toString})"
  | Z => "Z.t"
  | unit => "unit"
  | bool => "bool"
  | list a => s!"{a.toString} list"

instance : ToString MLType := ⟨MLType.toString⟩

partial def to_ml_type (ty: Expr): MetaM MLType :=
  Meta.forallTelescopeReducing ty fun vars body => do
    let vartypes ← vars.mapM Meta.inferType
    let varmltypes ← vartypes.mapM to_ml_type
    let bodymltype ← match (← Meta.whnf body) with
    | .const `Nat _ => pure .Z
    | .const `Unit _ | .const `PUnit _ => pure .unit
    | .const `Bool _ => pure .bool
    | .app (.const `List _) a => do pure <| .list (← to_ml_type a)
    | t => panic! s!"failed to translate {t} into ML type"
    return varmltypes.foldr .arrow bodymltype

def gen_mli (ty: Expr): MetaM String := do return s!"val main: {← to_ml_type ty}"
-/

syntax (name := erasestx) "#erase" ppSpace term (ppSpace "to" ppSpace str)?: command

@[command_elab erasestx]
def eraseElab: Elab.Command.CommandElab
  | `(command| #erase $t:term $[to $path?:str]?) => Elab.Command.liftTermElabM do
    let e: Expr ← Elab.Term.elabTerm t (expectedType? := .none)
    Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let e ← Lean.instantiateMVars e

    let sOrError := do
      let res ← (@eraseExpr .empty e .empty {} .empty);
      let p := res.p;
      let e := res.e;
      let p' := Constructors.transformProgram p (hvalue := rfl);
      let e' := Constructors.transformExpression e (hvalue := rfl);
      let (decls, names) := programToLambdaBox p' rfl;
      let e := expressionToLambdaBox e' names rfl;
      let s: String := (decls, e) |> Serialize.to_sexpr |>.toString;
      return s

    match ← sOrError.run with
    | .ok s =>
      -- logInfo s!"{repr p}"
      match path? with
      | .some path =>
          IO.FS.writeFile path.getString s
      | .none => logInfo s
    | .error e => throwThe Exception (.error t (.ofFormatWithInfos ↑e))

  | _ => Elab.throwUnsupportedSyntax

end Erasure
