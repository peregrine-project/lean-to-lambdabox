import Lean.Compiler.LCNF.ToLCNF
import Lean.Meta

import LeanToLambdaBox.Basic
import LeanToLambdaBox.Printing
import LeanToLambdaBox.Relevance
import Std.Data

open Lean
open Lean.Compiler.LCNF

namespace Erasure

inductive ConstructorArgRelevance where
  | erase
  | keep
deriving Repr, BEq

/-- Used to reindex constructor arguments for removal of irrelevant fields. -/
abbrev ConstructorArgMask := Array ConstructorArgRelevance
abbrev InductiveArgMasks := List ConstructorArgMask

def filter (mask: ConstructorArgMask) (arr: Array α): Array α :=
  mask.zip arr |>.filterMap (fun (r, a) => match r with | .erase => .none | .keep => .some a)
/--
State carried by EraseM to handle constants and inductive types registered in the global environment.
-/
structure ErasureState: Type where
  inductives: Std.HashMap Name (InductiveId × InductiveArgMasks) := ∅
  constants: Std.HashMap Name Kername := ∅
  /-- This field is only updated, not read. -/
  gdecls: GlobalDeclarations := []
  inlinings: List Kername := []
  /-- The λbox key minted for each registered mutual inductive block, together with the
  block's member list (`InductiveVal.all`), so a second block whose members mint the same key —
  `rootKername` on `String.join` is not injective: `[AB, C]` and `[A, BC]` coincide — is caught
  instead of silently overwriting the first block's entry in `gdecls`. -/
  indBlocks: List (Kername × List Name) := []

namespace Config

/--
How to handle functions with the @[extern] attribute.
Notably, this includes `Nat.add` et al., but also some constructors such as those of `Int`.
-/
inductive Extern where
  /-- If a Lean definition is present, use that one. -/
  | preferLogical
  /-- Ignore any Lean definitions and always treat as an axiom to be provided OCaml-side. -/
  | preferAxiom
deriving BEq

/-- How to handle literals and constructors of `Nat`. -/
inductive Nat
  /-- Keep Nat as an inductive type and represent literals by using constructors. -/
  | peano
  /--
  Turn Nat literals into lambdabox primitive i63 (panic on overflow),
  translate .zero into literal 0 and .succ x into x + literal 1.
  For this to work, config.extern must be set to .preferAxiom, so that
  the usual functions on `Nat` (addition, multiplication etc) are treated as axioms
  (and implemented by Zarith functions linked with the .cmx file from extraction),
  instead of using the logical implementation in Lean.
  -/
  | machine

end Config

structure ErasureConfig: Type where
  extern: Config.Extern := .preferAxiom
  nat: Config.Nat := .machine
  /-- Whether to perform csimp replacements before erasure. -/
  csimp: Bool := true
  /-- Whether to remove irrelevant arguments from constructors. -/
  remove_irrel_constr_args: Bool := false
  /--
  Whether to detect typeclass-dispatch artifacts after erasure and mark them as inline,
  so Peregrine collapses chains like `HAdd.hAdd → instHAdd → instAddNat → Nat.add` into
  a direct call. Detection is structural (no name-matching):
  - `Lean.Meta.isInstance name` — anything declared with `instance`, OR
  - Trivial-alias shape on the erased body: a bare `const`/`proj`, or a single-ctor
    structure literal whose fields are shallow.

  Inlining is always skipped if the erased body contains a `LBTerm.fix`, since
  inlining recursion would unfold the recursive definition at every call site.

  Off by default: marking constants for inlining is a *directive* to Peregrine
  (everything marked will be inlined), so enable only after profiling shows it pays off.
  -/
  auto_inline_typeclass_dispatch: Bool := false

/-- Strip leading lambdas (typeclass-instance parameters), exposing the body. -/
partial def _root_.LBTerm.stripLambdas : LBTerm → LBTerm
  | .lambda _ b => b.stripLambdas
  | t => t

/--
True iff the term contains a `LBTerm.fix` subterm anywhere. Used to refuse
inlining of recursive definitions, which would unfold recursion at each call site.
-/
partial def _root_.LBTerm.containsFix : LBTerm → Bool
  | .box | .bvar _ | .fvar _ | .const _ | .prim _ => false
  | .lambda _ b => b.containsFix
  | .letIn _ v b => v.containsFix || b.containsFix
  | .app a b => a.containsFix || b.containsFix
  | .construct _ _ args => args.any (·.containsFix)
  | .case _ d alts => d.containsFix || alts.any (fun (_, b) => b.containsFix)
  | .proj _ e => e.containsFix
  | .fix _ _ => true

/--
True iff the term has a de Bruijn index that no binder of the term itself binds,
counting binders exactly as `toBvar` does.
-/
partial def _root_.LBTerm.hasLooseBVarFrom : Nat → LBTerm → Bool
  | _, .box | _, .fvar _ | _, .const _ | _, .prim _ => false
  | depth, .bvar i => depth <= i
  | depth, .lambda _ b => b.hasLooseBVarFrom (depth + 1)
  | depth, .letIn _ v b => v.hasLooseBVarFrom depth || b.hasLooseBVarFrom (depth + 1)
  | depth, .app a b => a.hasLooseBVarFrom depth || b.hasLooseBVarFrom depth
  | depth, .construct _ _ args => args.any (·.hasLooseBVarFrom depth)
  | depth, .case _ d alts =>
    d.hasLooseBVarFrom depth || alts.any (fun (names, b) => b.hasLooseBVarFrom (depth + names.length))
  | depth, .proj _ e => e.hasLooseBVarFrom depth
  | depth, .fix defs _ => defs.any (fun d => d.body.hasLooseBVarFrom (depth + defs.length))

/--
True iff the term has a free de Bruijn index. Erasure builds terms locally nameless —
an ambient variable is an `.fvar` until `abstract` turns it into an index — so this is
false for every term `visitExpr` returns, which is what lets `visitCases` place such a
term under the binders of an alternative without lifting it.
-/
def _root_.LBTerm.hasLooseBVar (t : LBTerm) : Bool := t.hasLooseBVarFrom 0

/--
True when the erased body, modulo a leading chain of lambdas, looks like a
typeclass-dispatch artifact:
- a bare `const` (alias such as `instDecidableEqNat := Nat.decEq`),
- a `proj` (alias to a field projection),
- a single-ctor structure literal (the usual `Foo.mk arg₁ … argₙ` shape produced
  by `instance : Foo := ⟨…⟩` after erasure).
-/
def _root_.LBTerm.isTrivialAlias (t : LBTerm) : Bool :=
  match t.stripLambdas with
  | .const _ => true
  | .proj _ _ => true
  | .construct _ 0 _ => true
  | _ => false

structure ErasureContext: Type where
  lctx: LocalContext := {}
  fixvars: Option (Std.HashMap Name FVarId) := .none
  /-- The declaration-level universe parameters of the definition currently being
      erased, threaded to the relevance oracle (`isErasable`) so lean4lean's
      kernel checker runs in the *declaration's* universe context (matching the
      ambient `MLCtx`/`Us` the bridge reasons about), rather than universe params
      re-collected from each subterm. Set per-declaration in `visitMutual`; the
      `#erase` entry point (`erase`) leaves it at the default `[]`. -/
  lparams: List Name := []
  config: ErasureConfig

/-- The monad in ToLCNF has caches, a local context and toAny as a set of fvars, all as mutable state for some reason.
    Here I just have a read-only local context, in order to be able to use MetaM's type inference, and keep the code complexity low.
    If this is much too slow, try caching stuff again.

    Above the local context there is also a state handling the global environment of the extracted program.
    -/
abbrev EraseM := StateT ErasureState <| ReaderT ErasureContext CoreM

def run (x : EraseM α) (config: ErasureConfig): CoreM (α × ErasureState) :=
  x |>.run {} |>.run { config }

/-- Run an action of MetaM in EraseM using EraseM's local context of Lean types. -/
@[inline] def liftMetaM (x : MetaM α) : EraseM α := do
  x.run' { lctx := (← read).lctx }

/-- Fallback relevance check via the Lean elaborator (the original implementation):
    erase proofs (`Meta.isProp`) and type-formers (`Meta.isTypeFormerType`). Used when
    the lean4lean kernel checker cannot run on a term. -/
def isErasableMeta (e : Expr) : MetaM Bool := do
    let type ← Meta.inferType e
    -- Erase evidence of propositions
    -- ToLCNF includes an explicit check for isLcProof, but I think the type information should be enough to erase those here.
    if (← Meta.isProp type) then
      return true
    -- Erase types and type formers
    if (← Meta.isTypeFormerType type) then
      return true
    return false

/-- Relevance decision: is `e` irrelevant (a proof or a type-former)?

    This routes the decision through the **lean4lean-verified** relevance check
    `LeanToLambdaBox.isErasable` (`isProp ∨ isArity` on lean4lean's kernel checker),
    whose soundness against the formal `Erasable` predicate is proved as
    `LeanToLambdaBox.isErasable.WF` (no axiom of ours). Universe parameters
    (`lparams`) are supplied by the caller — the declaration-level `levelParams`
    of the definition being erased (threaded through `ErasureContext.lparams`) —
    so the checker runs in the same universe context the verified bridge reasons
    about; the checker is run in the current local context. If lean4lean's checker
    cannot run (e.g. a construct it does not support), we fall back to the
    elaborator-based `isErasableMeta` so the transpiler never fails on that account.

    NB: relevance decisions can differ from the previous `Meta.*`-only implementation
    on edge cases; extracted output should be re-validated against the benchmarks. -/
def isErasable (lparams : List Name) (e : Expr) : MetaM Bool := do
    match Lean4Lean.TypeChecker.M.run (← getEnv).toKernelEnv (safety := .safe)
        (lctx := ← getLCtx) (lparams := lparams)
        (x := Lean4Lean.TypeChecker.RecM.run (LeanToLambdaBox.isErasable e)) with
    | .ok b => return b
    | .error _ => isErasableMeta e

/--
Refuse if `kn`, the λbox key just minted for `name`, is already registered under a different
Lean name — as a top-level constant, or (`register_inductive` mints keys the same way, on a
mutual block's member names rather than a single one) as a mutual inductive block. `toKername`
collapses `.num`/`.str` name components that differ before `cleanIdent`'s escaping, so two
distinct declarations can mint one key; without this check the second registration would
silently overwrite the first in `gdecls` and the printer would emit only the survivor.
-/
def checkKernameFresh (name: Name) (kn: Kername): EraseM Unit := do
  if let some (other, _) := (← get).constants.toList.find? (fun (n, k) => decide (k = kn) && decide (n ≠ name)) then
    throwError "Erasure.toKername: {other} and {name} both mint the λbox key {repr kn}."
  if let some (_, members) := (← get).indBlocks.find? (fun (k, _) => decide (k = kn)) then
    throwError "Erasure.toKername: the mutual inductive block {members} and {name} both mint the λbox key {repr kn}."

/--
The `register_inductive` counterpart to `checkKernameFresh`: refuse if `kn`, the λbox key just
minted for the mutual inductive block `names`, is already registered — as a *different* mutual
inductive block reaching the same key (same finding, symmetric: `[AB, C]` and `[A, BC]` mint one
key, and so do a constant key and a block key), or as a top-level constant's key.
-/
def checkIndKernameFresh (names: List Name) (kn: Kername): EraseM Unit := do
  if let some (_, other) := (← get).indBlocks.find? (fun (k, _) => decide (k = kn)) then
    if other ≠ names then
      throwError "Erasure.toKername: the mutual inductive blocks {other} and {names} both mint the λbox key {repr kn}."
  if let some (other, _) := (← get).constants.toList.find? (fun (_, k) => decide (k = kn)) then
    throwError "Erasure.toKername: {other} and the mutual inductive block {names} both mint the λbox key {repr kn}."

def addAxiom (name: Name): EraseM Unit := do
  if (← get).constants.contains name then panic! s!"Constant {name} is already defined, cannot add axiom."
  let kn := toKername name
  checkKernameFresh name kn
  modify (fun s => { s with constants := s.constants.insert name kn, gdecls := s.gdecls.cons (kn, .constantDecl ⟨.none⟩) })

/--
Register `name` under the λbox body `t`. Used where Lean gives a declaration no value but its
computational content is writable in λbox, so that the consumer gets a constant it can reduce
instead of an axiom it has to be handed a realizer for.
-/
def addRealizer (name: Name) (t: LBTerm): EraseM Unit := do
  if (← get).constants.contains name then panic! s!"Constant {name} is already defined, cannot add a realizer."
  let kn := toKername name
  checkKernameFresh name kn
  modify (fun s => { s with constants := s.constants.insert name kn, gdecls := s.gdecls.cons (kn, .constantDecl ⟨.some t⟩) })

/-- `n` anonymous λ-binders around `body`. -/
def mkAnonLambdas (n: Nat) (body: LBTerm): LBTerm :=
  (List.range n).foldl (fun t _ => LBTerm.lambda .anon t) body

/--
The λbox realizer of one of Lean's four quotient primitives, at the arity the kernel fixes for it.

A quotient carries no runtime representation beyond its representative, so `Quot.mk` is the
identity on it and `Quot.lift` applies the lifted function to it — which is also how Lean's own
code generator compiles them. `Quot` is a type former and `Quot.ind` is proof-valued, so both are
erased, and an erased constant's body is `□`.
-/
def quotRealizer: QuotKind → LBTerm
  -- `Quot`, arity 2, and `Quot.ind`, arity 5.
  | .type | .ind => .box
  -- `Quot.mk : {α} → (r : α → α → Prop) → α → Quot r`.
  | .ctor => mkAnonLambdas 3 (.bvar 0)
  -- `Quot.lift : {α} → {r} → {β} → (f : α → β) → (∀ a b, r a b → f a = f b) → Quot r → β`.
  | .lift => mkAnonLambdas 6 (.app (.bvar 2) (.bvar 0))

/--
The sort a Π-telescope ends in, read syntactically: MetaRocq's `destArity`
(`ErasureFunction.v:1325`), which likewise does not reduce.
-/
def arityResultSort: Expr → Option Level
  | .forallE _ _ b _ => arityResultSort b
  | .sort l => some l
  | _ => none

/--
Does an inductive declared with type `type` live in `Prop`? This is MetaRocq's
`isPropositionalArity` (`Extract.v:276`): the sort ending the declared arity is `Prop`, for every
instantiation of the declaration's universe parameters.
-/
def isPropositionalArity (type: Expr): Bool :=
  match arityResultSort type with
  | some l => l.isAlwaysZero
  | none => false

/--
The first field of a constructor of `ind` that is not a proof, as the constructor's name and the
field's index among the fields. Parameters are not fields, and a field is a proof exactly when its
type is a proposition.
-/
def firstNonProofField (ind: InductiveVal): EraseM (Option (Name × Nat)) := do
  for ctor_name in ind.ctors do
    let .ctorInfo ci ← getConstInfo ctor_name
      | throwError "Erasure: {ctor_name} is listed as a constructor of {ind.name} but is not one."
    let found ← liftMetaM <|
      Meta.forallBoundedTelescope ci.type (.some <| ci.numParams + ci.numFields) fun vars _ => do
        for (v, i) in vars[ci.numParams:].toArray.zipIdx do
          unless ← Meta.isProof v do return some i
        return none
    if let some i := found then return some (ctor_name, i)
  return none

/--
Get information about the inductive type, adding all its mutually-defined buddies to the context if necessary.
-/
def register_inductive (indinfo: InductiveVal): EraseM (InductiveId × InductiveArgMasks) := do
  if let .some iid := (← get).inductives.get? indinfo.name then
    return iid
  else
    let names := indinfo.all
    let mutualBlockName := indinfo.all |>.map toString |> String.join |> rootKername
    checkIndKernameFresh names mutualBlockName
    -- Iterate through all the inductive types in the mutual definition
    let ind_bodies: List OneInductiveBody ← names.zipIdx.mapM fun (ind_name, idx) => do
      let .inductInfo inf ← getConstInfo ind_name | unreachable!
      -- Iterate through all the constructors
      let (ind_ctors, ind_argmasks) := List.unzip (← inf.ctors.mapM fun ctor_name => do
        if isExtern (← getEnv) ctor_name && (← read).config.extern == .preferAxiom then
          logInfo "Constructor {ctor_name} of type {ind_name} is marked @[extern], emitting axiom."
          addAxiom ctor_name
        let .ctorInfo ci ← getConstInfo ctor_name | unreachable!
        -- Get an argmask to remember which fields are irrelevant.
        let argmask: ConstructorArgMask ← if (← read).config.remove_irrel_constr_args
        then
          liftMetaM <| Meta.forallBoundedTelescope ci.type (.some <| ci.numParams + ci.numFields) fun vars _ =>
            let fields := vars[ci.numParams:].toArray
            let fields := if fields.size != ci.numFields
            then panic! "unexpected field count"
            else fields
            do
            let mask: ConstructorArgMask ← fields.mapM fun v => do
              if ← isErasable ci.levelParams v then pure .erase else pure .keep
            if (mask.any (· == .erase)) then logInfo s!"Argmask for constructor {ctor_name}: {repr mask}"
            pure mask
        else
          pure <| Array.replicate ci.numFields .keep
        let nargs := Array.count .keep argmask
        pure ({ name := toString ctor_name, nargs }, argmask)
      )
      -- If the type is a structure, add definitions for projections.
      let is_struct := names.length == 1 && inf.ctors.length == 1 && !inf.isRec
      let projs: List ProjectionBody ←
        if is_struct then
          -- only generate projections for relevant fields
          let _ := Expr
          let num_fields := ind_argmasks[0]!.count .keep
          -- These dummy names aren't semantically important, so it doesn't actually matter whether the index refers to
          -- the field's position before or after removing irrelevant fields. Here, I chose the latter, because it was easier.
          pure (List.range num_fields |>.map toString |>.map ProjectionBody.mk)
        else
          pure []

      let ind_id: InductiveId := { mutualBlockName, idx }
      modify (fun s => { s with inductives := s.inductives.insert ind_name (ind_id, ind_argmasks)})
      -- `erase_one_inductive_body` (`ErasureFunction.v:1325-1338`) reads `ind_propositional` off
      -- the declared arity, and `erases_mutual_inductive_body` (`Extract.v:276`) states it as an
      -- equality, so it is not a flag the frontend may default.
      pure { name := toString ind_name, propositional := isPropositionalArity inf.type,
             ctors := ind_ctors, projs }
    let mutual_body := { npars := indinfo.numParams, bodies := ind_bodies }
    modify (fun s => { s with gdecls := s.gdecls.cons (mutualBlockName, .inductiveDecl mutual_body),
                              indBlocks := s.indBlocks.cons (mutualBlockName, names) })
    return (← get).inductives[indinfo.name]!

/--
The λbox body of the recursor of a propositional inductive with singleton elimination; `none` at
every other recursor, which keeps the body-less emission.

Rocq has no primitive `Eq.rec`: `eq_rect` is an ordinary constant whose body is a `match` on a
propositional singleton, and `remove_match_on_box` (`EOptimizePropDiscr.v:48`) collapses that one
alternative by substituting `□` for the fields it binds. So the realizer is an ordinary `.case`,
and the shape that may take it is the one whose fields the collapse may box: the eliminated
inductive is a single non-recursive `Prop` with at most one constructor, all of whose fields are
proofs. A `Prop` with a field that is *data* recovered from the result's indices (`Acc`) is refused
here for the same reason `visitCases` refuses it — boxing that field computes a wrong program.

The shape is read off the `RecursorVal` and the inductive it names, never off the constant's name.
At the recursor's calling convention — parameters, motives, minors, indices, major premise — the
body dispatches on the major premise and hands the constructor's fields to the single minor:

    Eq.rec    ↦  λ _ _ _ _ _ _. case (Eq, 2)    (bvar 0) [([], bvar 2)]
    And.rec   ↦  λ _ _ _ _ _.   case (And, 2)   (bvar 0) [([_,_], bvar 3 (bvar 1) (bvar 0))]
    False.rec ↦  λ _ _.         case (False, 0) (bvar 0) []

Under `remove_irrel_constr_args` the proof fields leave the alternative's binders, and the
realizer supplies them as `□` instead — which is what the source term erases them to either way.
-/
def recursorRealizer (rv: RecursorVal): EraseM (Option LBTerm) := do
  let [ind_name] := rv.all | return none
  let .inductInfo ind ← getConstInfo ind_name | return none
  unless isPropositionalArity ind.type && !ind.isRec && rv.numMotives == 1 do return none
  unless ind.ctors.length ≤ 1 && rv.numMinors == ind.ctors.length do return none
  if (← firstNonProofField ind).isSome then return none
  let (indid, argmasks) ← register_inductive ind
  let alts ← ind.ctors.mapM fun ctor_name => do
    let .ctorInfo ci ← getConstInfo ctor_name
      | throwError "Erasure.recursorRealizer: {ctor_name} is listed as a constructor of {ind_name} but is not one."
    let argmask := argmasks[ci.cidx]!
    let nargs := argmask.count .keep
    -- The minor sits past the indices, the major premise and the fields this alternative binds;
    -- `mkAlt`'s convention gives the first bound field the highest index, and an erased field is
    -- supplied as `□`, which is what the source term erases it to.
    let (_, body) := argmask.foldl (fun (kept, t) r =>
      match r with
      | .keep => (kept + 1, LBTerm.app t (.bvar (nargs - 1 - kept)))
      | .erase => (kept, LBTerm.app t .box))
      (0, LBTerm.bvar (rv.numIndices + 1 + nargs))
    return (List.replicate nargs BinderName.anon, body)
  let arity := rv.numParams + rv.numMotives + rv.numMinors + rv.numIndices + 1
  return some <| mkAnonLambdas arity (.case (indid, ind.numParams) (.bvar 0) alts)

def fvar_to_name (x: FVarId): EraseM BinderName := do
  let n := (← read).lctx.fvarIdToDecl |>.find! x |>.userName
  let s: String := n.toString
  -- check if s is ASCII graphic, otherwise the λbox parser will complain
  if s.all (fun (c : Char) => decide (33 <= c.toNat /\ c.toNat < 127)) then
    return .named n.toString
  else
    return .anon

def mkLambda (x: FVarId) (body: LBTerm): EraseM LBTerm := do return .lambda (← fvar_to_name x) (abstract x body)

def mkLetIn (x: FVarId) (val body: LBTerm): EraseM LBTerm := do return .letIn (← fvar_to_name x) val (abstract x body)

/-- The order of variables here is what it is because the other way around led to segfaults. -/
def mkAlt (xs: List FVarId) (body: LBTerm): EraseM (List BinderName × LBTerm) := do
  let mut body := body
  let names ← xs.mapM fvar_to_name
  for (fvarid, i) in xs.reverse.zipIdx do
    body := toBvar fvarid i body
  return (names, body)

/-
def mkCase (indInfo: InductiveVal) (discr: LBTerm) (alts: List (List ppname × LBTerm)): EraseM LBTerm := do
  let (indid, _) ←  register_inductive indInfo
  return .case (indid, indInfo.numParams) discr alts
-/

/-- Check binding order here as well, may be wrong. -/
def mkDef (name: Name) (fixvarnames: List Name) (body: LBTerm): EraseM (@FixDef LBTerm) := do
  let mut body := body
  for (n, i) in fixvarnames.reverse.zipIdx do
    body := toBvar ((← read).fixvars.get![n]!) i body
  return { name := .named name.toString, body }

/--
The fixpoint selecting member `i` of `defs`, η-expanded over the `principalArgIdx + 1`
arguments that member consumes before recursing: `fun x₀ … xₙ => (fix defs i) x₀ … xₙ`.

This is MetaRocq's `eta_fixpoint` (`template-rocq/theories/EtaExpand.v:72`), which Rocq
applies before erasure. `EEtaExpandedFix.expanded` — the precondition of
`guarded_to_unguarded_fix`, the first pass of peregrine's verified untyped pipeline —
admits a `.fix` node only under an argument spine longer than the selected member's
principal argument index, so a bare fixpoint registered as a constant body falsifies it.
Evaluation is unaffected: both terms are values and agree on every application.
-/
def etaExpandFix (defs: List (@FixDef LBTerm)) (i: Nat): LBTerm :=
  let arity := match defs[i]? with
    | .some d => d.principalArgIdx + 1
    | .none => 1
  -- The outermost binder is the first argument, so it carries the largest index.
  let applied: LBTerm := (List.range arity).foldr (fun k t => .app t (.bvar k)) (.fix defs i)
  (List.range arity).foldl (fun t _ => .lambda .anon t) applied

/-- Similar to Meta.withLocalDecl, but in EraseM.
    k will be passed some fresh FVarId and run in a context in which it is bound. -/
def withLocalDecl (n: Name) (type: Expr) (bi: BinderInfo) (k: FVarId -> EraseM α): EraseM α := do
  let fvarid <- mkFreshFVarId;
  withReader (fun ctx => { ctx with lctx := ctx.lctx.mkLocalDecl fvarid n type bi }) (k fvarid)

/-- Like Meta.withLetDecl. The `nd` (nonDep) flag is elaborator metadata that
lean4lean's `MLCtx` cannot represent, so it is dropped from the `mkLetDecl` call
(matching `MLCtx.vlet`'s `c.lctx.mkLetDecl id name ty val`, which uses the default
nonDep); the parameter is retained for signature stability. Behaviour is
byte-identical on the corpus — nonDep affects neither kernel type inference nor
the λ□ output. -/
def withLocalDef (n: Name) (type val: Expr) (_nd: Bool) (k: FVarId -> EraseM α): EraseM α := do
  let fvarid <- mkFreshFVarId;
  withReader (fun ctx => { ctx with lctx := ctx.lctx.mkLetDecl fvarid n type val }) (k fvarid)

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

/--
Given an expression `e` and its type, which is assumed to be of the form `∀ a:A, B`,
run a continuation `k` in a context where a fvar `a` has type `A`.
- if `e` is `fun a: A => body`, `k` will be run on the expression `body` directly.
- if `e` is not of this form, `k` will be run on the expression `.app e (.fvar a)`, behaving as if `e` had been eta-expanded to `fun a => e a`.
In both cases the second argument to `k` is `B`, the type of the first argument in the new context.
Assumes that `type` is the type of `e` in the context where it is called.
Panics if `type` is not a function type.
-/
def lambdaMonocularOrIntro {α} [Inhabited α] (e type: Expr) (k: Expr -> Expr -> FVarId -> EraseM α): EraseM α :=
  forallMonocular type fun fvarid bodytype => do
    if let .lam _ _ body _ := e then
      /-
      Here I use the binder name and info from the type-level forall binder we are under.
      It might be better to get it from the lambda binder.
      -/
      k (body.instantiate1 <| .fvar fvarid) bodytype fvarid
    else
      -- Here in any case I must use the binder name and info from the forall binder.
      k (.app e (.fvar fvarid)) bodytype fvarid

/--
Given an expression `e` and its type, which is assumed to start with at least `arity` `∀` quantifiers,
get the body of `e` after application to `arity` arguments.
For example, if `e` is `fun a b => asdf` with type `A -> B -> C -> D`, applying `lambdaOrIntroToArity 3`
will run the continuation in the context `a: A, b: B, c: C` on the expression `.app asdf (.fvar c)`
with the fvars `#[a, b, c]`.
I think I got the order of fvars right but thinking about continuations is hard.
Writing the code in this way is suboptimal; there is a first phase in which we only descend through lambdas
and a second phase in which we descend the remaining distance through the type by appending fvars,
but here we check whether there is a lambda to go under each time.
This is probably easily fixable using something like lambdaBoundedTelescope.
-/
def lambdaOrIntroToArity {α} [Inhabited α] (e type: Expr) (arity: Nat) (k: Expr -> List FVarId -> EraseM α): EraseM α :=
  match arity with
  | 0 => k e []
  | n+1 => lambdaMonocularOrIntro e type fun body bodytype fvarid =>
      lambdaOrIntroToArity body bodytype n (fun e fvarids => k e (.cons fvarid fvarids))

/--
Is `a`, an argument already supplied to an under-applied constructor or eliminator, a value
that η-expansion may leave where it stands? A variable and an erased argument (a `□`) are:
placing them under the new binders neither evaluates nor duplicates anything.
-/
def etaArgIsValue (lparams: List Name) (a: Expr): EraseM Bool := do
  return a.isFVar || (← liftMetaM <| isErasable lparams a)

/--
Bind the arguments an under-applied constructor or eliminator was already supplied with
*outside* the binders η-expansion is about to open, so that the expansion evaluates each of
them once instead of on every application of the expansion.

`bs` lists, for each argument to bind, its position in `args`, the type to bind it at and its
erased value. The continuation is run on `args` with a fresh variable in each bound position,
and its result is wrapped in one `let` per binding, the first of `bs` outermost:
`let a₁ := ⟦a₁⟧; … let aₖ := ⟦aₖ⟧; λ x⃗. C a₁ … aₖ x⃗`.
-/
def withEtaPrefixLets (bs: List (Nat × Expr × LBTerm)) (args: Array Expr)
    (k: Array Expr -> EraseM LBTerm): EraseM LBTerm :=
  match bs with
  | [] => k args
  | (i, ty, v) :: bs =>
    withLocalDecl (.mkSimple s!"a{i}") ty .default fun x => do
      mkLetIn x v (← withEtaPrefixLets bs (args.set! i (.fvar x)) k)

/-! ### Monotonicity lemmas for `partial_fixpoint` (verification infrastructure)

The erasure family below (`visitExpr` & co.) is defined with `partial_fixpoint`
rather than `partial def`, so that it has equational lemmas (`….eq_def`) and a
fixpoint-induction principle (`….mutual_fixpoint_induct`) to reason about —
Task A of the verification (see `PROJECT_STATUS_HANDOFF.md`). `partial_fixpoint`
must prove every definition monotone in its recursive calls; recursion flowing
through the continuation-passing helpers above (`withLocalDecl`,
`lambdaMonocular`, …) requires the `@[partial_fixpoint_monotone]` lemmas below.
These are proof-only artifacts: they change the compiled behaviour of nothing. -/

section Monotonicity
open Lean.Order

@[partial_fixpoint_monotone]
theorem withReader_mono {γ} [PartialOrder γ] {α} (f : ErasureContext → ErasureContext)
    (k : γ → EraseM α) (hmono : monotone k) :
    monotone (fun x => withReader f (k x)) := by
  change monotone (fun x (s : ErasureState) (ctx : ErasureContext) => k x s (f ctx))
  apply monotone_of_monotone_apply; intro s
  apply monotone_of_monotone_apply; intro ctx
  exact monotone_apply (f ctx) _ (monotone_apply s _ hmono)

@[partial_fixpoint_monotone]
theorem withLocalDecl_mono {γ} [PartialOrder γ] {α} (n : Name) (type : Expr) (bi : BinderInfo)
    (k : γ → FVarId → EraseM α) (hmono : monotone k) :
    monotone (fun x => Erasure.withLocalDecl n type bi (k x)) := by
  unfold Erasure.withLocalDecl
  monotonicity
  · apply monotone_const
  · apply monotone_of_monotone_apply; intro fvarid
    exact withReader_mono _ _ (monotone_apply fvarid _ hmono)

@[partial_fixpoint_monotone]
theorem withEtaPrefixLets_mono {γ} [PartialOrder γ] (bs : List (Nat × Expr × LBTerm))
    (args : Array Expr) (k : γ → Array Expr → EraseM LBTerm) (hmono : monotone k) :
    monotone (fun x => withEtaPrefixLets bs args (k x)) := by
  induction bs generalizing args with
  | nil => unfold withEtaPrefixLets; exact monotone_apply _ _ hmono
  | cons b bs ih =>
    obtain ⟨i, ty, v⟩ := b
    unfold withEtaPrefixLets
    apply withLocalDecl_mono
    apply monotone_of_monotone_apply; intro fvarid
    monotonicity
    · exact ih _
    · apply monotone_const

@[partial_fixpoint_monotone]
theorem withLocalDef_mono {γ} [PartialOrder γ] {α} (n : Name) (type val : Expr) (nd : Bool)
    (k : γ → FVarId → EraseM α) (hmono : monotone k) :
    monotone (fun x => Erasure.withLocalDef n type val nd (k x)) := by
  unfold Erasure.withLocalDef
  monotonicity
  · apply monotone_const
  · apply monotone_of_monotone_apply; intro fvarid
    exact withReader_mono _ _ (monotone_apply fvarid _ hmono)

@[partial_fixpoint_monotone]
theorem lambdaMonocular_mono {γ} [PartialOrder γ] {α} [Inhabited α] (e : Expr)
    (k : γ → FVarId → Expr → EraseM α) (hmono : monotone k) :
    monotone (fun x => lambdaMonocular e (k x)) := by
  unfold lambdaMonocular
  monotonicity
  all_goals first
    | apply monotone_const
    | (apply withLocalDecl_mono
       apply monotone_of_monotone_apply; intro fvarid
       exact monotone_apply _ _ (monotone_apply fvarid _ hmono))

@[partial_fixpoint_monotone]
theorem letMonocular_mono {γ} [PartialOrder γ] {α} [Inhabited α] (e : Expr)
    (k : γ → FVarId → Expr → Expr → EraseM α) (hmono : monotone k) :
    monotone (fun x => letMonocular e (k x)) := by
  unfold letMonocular
  monotonicity
  all_goals first
    | apply monotone_const
    | (apply withLocalDef_mono
       apply monotone_of_monotone_apply; intro fvarid
       exact monotone_apply _ _ (monotone_apply _ _ (monotone_apply fvarid _ hmono)))

@[partial_fixpoint_monotone]
theorem forallMonocular_mono {γ} [PartialOrder γ] {α} [Inhabited α] (t : Expr)
    (k : γ → FVarId → Expr → EraseM α) (hmono : monotone k) :
    monotone (fun x => forallMonocular t (k x)) := by
  unfold forallMonocular
  monotonicity
  all_goals first
    | apply monotone_const
    | (apply withLocalDecl_mono
       apply monotone_of_monotone_apply; intro fvarid
       exact monotone_apply _ _ (monotone_apply fvarid _ hmono))

@[partial_fixpoint_monotone]
theorem lambdaMonocularOrIntro_mono {γ} [PartialOrder γ] {α} [Inhabited α] (e type : Expr)
    (k : γ → Expr → Expr → FVarId → EraseM α) (hmono : monotone k) :
    monotone (fun x => lambdaMonocularOrIntro e type (k x)) := by
  unfold lambdaMonocularOrIntro
  apply forallMonocular_mono
  apply monotone_of_monotone_apply; intro fvarid
  apply monotone_of_monotone_apply; intro bodytype
  monotonicity
  all_goals exact monotone_apply _ _ (monotone_apply _ _ (monotone_apply _ _ hmono))

@[partial_fixpoint_monotone]
theorem lambdaOrIntroToArity_mono {γ} [PartialOrder γ] {α} [Inhabited α] (e type : Expr) (arity : Nat)
    (k : γ → Expr → List FVarId → EraseM α) (hmono : monotone k) :
    monotone (fun x => lambdaOrIntroToArity e type arity (k x)) := by
  induction arity generalizing e type k with
  | zero =>
    unfold lambdaOrIntroToArity
    exact monotone_apply _ _ (monotone_apply _ _ hmono)
  | succ n ih =>
    unfold lambdaOrIntroToArity
    apply lambdaMonocularOrIntro_mono
    apply monotone_of_monotone_apply; intro body
    apply monotone_of_monotone_apply; intro bodytype
    apply monotone_of_monotone_apply; intro fvarid
    apply ih
    apply monotone_of_monotone_apply; intro e'
    apply monotone_of_monotone_apply; intro fvarids
    exact monotone_apply _ _ (monotone_apply _ _ hmono)

open private Lean.Expr.getAppArgsAux from Lean.Expr in
/-- `Expr.withApp` computes `k e.getAppFn e.getAppArgs` in a single traversal.
Same statement and proof as lean4lean's `Lean4Lean.withApp_eq` (re-proved here so
the shipping build does not import lean4lean's heavy `Verify` layer). -/
theorem expr_withApp_eq {α} {e : Expr} {k : Expr → Array Expr → α} :
    e.withApp k = k e.getAppFn e.getAppArgs := loop
where
  loop {e arr n} : Expr.withAppAux k e arr n = k e.getAppFn (Lean.Expr.getAppArgsAux e arr n) := by
    unfold Expr.withAppAux Lean.Expr.getAppArgsAux
    split <;> [exact loop; simp [Expr.getAppFn]]

@[partial_fixpoint_monotone]
theorem expr_withApp_mono {γ} [PartialOrder γ] {β} [PartialOrder β] (e : Expr)
    (k : γ → Expr → Array Expr → β) (hmono : monotone k) :
    monotone (fun x => e.withApp (k x)) := by
  simp only [expr_withApp_eq]
  exact monotone_apply _ _ (monotone_apply _ _ hmono)

end Monotonicity

/--
Given an expression, deconstruct it into an application to at least arity arguments,
then build a LBTerm from it given the continuation.
This will eta-expand if necessary, and close the lambdas after running `k`.
For example: withAppEtaToMinArity "Nat.add 42" 2 k = mkLambda "y" (k "Nat.add" ["42", "y"])
Panics if the type of e does not start with at least arity .forallE constructors.

NB (verification): the erasure family below no longer calls this — `partial_fixpoint`
cannot handle a recursive call inside the *argument* of another recursive call
(nested recursion), which is what `withAppEtaToMinArity e arity (fun _ args =>
visitCases …)` would be. It is specialized as `visitCasesEta`/`visitCtorEta`
inside the mutual block, which additionally bind the supplied arguments outside the
binders they open (`withEtaPrefixLets`). Kept for API compatibility.
-/
partial def withAppEtaToMinArity (e: Expr) (arity: Nat) (k: Expr -> Array Expr -> EraseM LBTerm): EraseM LBTerm := do
  let type ← liftMetaM do Meta.inferType e
  e.withApp (fun f args => go type f args)
where
  -- Invariant: type is the type of f *args.
  go (type f: Expr) (args: Array Expr): EraseM LBTerm :=
    if args.size >= arity then
      k f args
    else
      forallMonocular type fun fvarid bodytype => do
        let res ← go bodytype f (args.push (.fvar fvarid))
        mkLambda fvarid res

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
  if (← read).config.csimp then
    -- This has to be done after _unsafe_rec name replacement.
    -- The whole-tree `Compiler.CSimp.replaceConstants` was removed in v4.29; replicate its
    -- behaviour by applying the single-node `replaceConstant?` at every subterm. A matched
    -- constant is replaced and not re-descended into (`.done`), matching `Expr.replace`.
    let env ← getEnv
    e ← Core.transform e (pre := fun sub => do
      match (← Compiler.CSimp.replaceConstant? env sub) with
      | some sub' => return .done sub'
      | none      => return .continue)
  pure e

/-!
The erasure family. This was a single `partial def erase … where visitExpr …`;
it is now a `mutual` block of total-by-`partial_fixpoint` definitions (Task A of
the verification): same code, same behaviour, but with equational lemmas and a
fixpoint-induction principle. The only two behaviour-preserving deviations,
forced by `partial_fixpoint`'s no-nested-recursion limitation and missing
`LawfulMonad` instances for the v4.29 `EST` monad, are documented inline:
`visitCasesEta`/`visitCtorEta` (specializations of `withAppEtaToMinArity`) and a
`.toArray` on the over-application `Subarray` loop in `visitCases`.
-/
mutual
  /- Proofs (terms whose type is of type Prop) and type formers/predicates are all erased. -/
  def visitExpr (e : Expr) : EraseM LBTerm := do
    if (← liftMetaM <| isErasable (← read).lparams e) then
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
  partial_fixpoint

  def visitLiteral (l: Literal): EraseM LBTerm := do
    match (← read).config.nat, l with
    | .peano, .natVal 0 => visitConstructor ``Nat.zero #[]
    | .peano, .natVal (n+1) => visitConstructor ``Nat.succ #[.lit (.natVal n)]
    | .machine, .natVal n =>
      if n <= BitVec.intMax 63 then
        pure <| .prim ⟨.primInt, n⟩
      else
        panic! "Nat literal not representable as a 63-bit signed integer."
    | _, .strVal _ => panic! "String literals not supported."
  partial_fixpoint

  /-
  The original in ToLCNF also handles eta-reduction of implicit lambdas introduced by the elaborator.
  This is beyond the scope of what I want to do here for the moment.
  -/
  def visitLambda (e : Expr) : EraseM LBTerm :=
    lambdaMonocular e (fun fvarid body => do mkLambda fvarid (← visitExpr body))
  partial_fixpoint

  def visitLet (e : Expr): EraseM LBTerm :=
    /-
    In the original ToLCNF, if the bound value is erasable then the let-binding is not generated,
    since all occurrences of the variable must be erased anyway.
    Keep this optimization?
    -/
    letMonocular e (fun fvarid val body => do mkLetIn fvarid (← visitExpr val) (← visitExpr body))
  partial_fixpoint

  def visitProj (s : Name) (i : Nat) (e : Expr) : EraseM LBTerm := do
    let .inductInfo indinfo ← getConstInfo s | unreachable!
    let (indid, argmasks) ← register_inductive indinfo
    -- i is the index among all fields, but some are erased
    let fieldIdx := argmasks[0]![:i].toArray.count .keep
    let projinfo: ProjectionInfo := { indType := indid, paramCount := indinfo.numParams, fieldIdx }
    return .proj projinfo (← visitExpr e)
  partial_fixpoint

  /--
  When visiting expressions of the form f g, it is not sufficient to just recurse on f and g.
  visitApp will explore an expression "in depth" to get the leftmost applicand,
  then handle the case where it is a constant specially; otherwise, straightforward recursion is correct.
  Contrary to the original ToLCNF, I have removed CSimp.replaceConstants here and assume it will just be run once before erasure.
  -/
  def visitApp (e : Expr) : EraseM LBTerm :=
    -- The applicand is a constant, check for special cases
    if let .const .. := e.getAppFn then
      visitConstApp e
    -- The applicand is not a constant, so we just normally recurse.
    else
      e.withApp fun f args => do visitAppArgs (← visitExpr f) args
  partial_fixpoint

  /-- A constant which is being defined in the current mutual block will be replaced with a free variable (to be bound by mkDef later).
  Other constants should previously have been added to the (λbox-side) context and will just be translated to Rocq kernames. -/
  def visitConst (e: Expr): EraseM LBTerm := do
    let .const declName _ := e | unreachable!
    if let .some id := (← read).fixvars.bind (fun hmap => hmap[declName]?) then
      return .fvar id
    return .const (← get_constant_kername declName)
  partial_fixpoint

  /--
  Special handling of
  - casesOn (will be eta-expanded)
  - constructors (will be eta-expanded)
  -/
  def visitConstApp (e: Expr): EraseM LBTerm :=
    e.withApp fun f args => do
      let .const declName _ := f | unreachable!
      if let some casesInfo ← getCasesInfo? declName then
        /-
        I have removed the check for whether there is an [implemented_by] annotation.
        This is only relevant for the implementation of computed fields, such as for hash consing in the `Expr` type.
        -/
        visitCasesEta casesInfo e
      else if let some arity ← getCtorArity? declName then
        visitCtorEta declName arity e
      /-
      Removed special check for automatically defined projection functions out of structures.
      In toLCNF these are inlined and β-reduced, unless the projection is out of a builtin type of the runtime.
      The definition seems to just be def spam.egg := fun s: spam => s.1,
      so after β-reduction this becomes a primitive projection.
      Left these to be inlined by Malfunction.
      -/
      else
        visitAppArgs (← visitConst f) args
  partial_fixpoint

  /-- `withAppEtaToMinArity` specialized to a `visitCases` continuation.
  (`partial_fixpoint` cannot handle nested recursion — a recursive call inside an
  *argument* of another recursive call — which is what passing a continuation
  mentioning `visitCases` to `withAppEtaToMinArity` would be. Specializing turns
  it into plain mutual recursion; the behaviour is the original's, except that the
  already-supplied discriminee is bound outside the binders the expansion opens — the
  already-supplied alternatives are left in place, since each is branch-guarded in the
  emitted `case` and binding one would force it unconditionally.) -/
  def visitCasesEta (casesInfo : CasesInfo) (e : Expr) : EraseM LBTerm := do
    let type ← liftMetaM do Meta.inferType e
    e.withApp (fun f args => visitCasesEtaGo casesInfo type f args)
  partial_fixpoint

  -- Invariant: type is the type of f *args.
  def visitCasesEtaGo (casesInfo : CasesInfo) (type f : Expr) (args : Array Expr) : EraseM LBTerm :=
    if args.size >= casesInfo.arity then
      visitCases casesInfo args
    else do
      -- Erase the discriminee already supplied and bind it outside the new binders: under
      -- them it would be evaluated afresh on every application of the expansion. Only the
      -- outermost round binds anything — every argument the recursion adds is a variable.
      -- `visitCases` reads the major premise and the alternatives and drops the parameters,
      -- the motive and the indices before the discriminee, which are therefore left where
      -- they are: binding one would evaluate an argument the emitted program does not.
      -- The alternatives *after* the discriminee are left alone for the same reason and one
      -- more: `visitCases` emits each of them inside its own branch of the `case`, reached
      -- only when its constructor is selected, so binding one here would evaluate a branch
      -- the emitted program does not — turning a value the source produces lazily into one
      -- the target forces unconditionally, which can non-terminate where the source does not.
      let bs ← args.zipIdx.foldlM (fun bs a => do
        if a.2 != casesInfo.discrPos then return bs
        if ← etaArgIsValue (← read).lparams a.1 then return bs
        else return bs.push (a.2, ← liftMetaM (Meta.inferType a.1), ← visitExpr a.1)) #[]
      withEtaPrefixLets bs.toList args fun args =>
        forallMonocular type fun fvarid bodytype => do
          let res ← visitCasesEtaGo casesInfo bodytype f (args.push (.fvar fvarid))
          mkLambda fvarid res
  partial_fixpoint

  /-- `withAppEtaToMinArity` specialized to a `visitConstructor` continuation
  (see `visitCasesEta`). -/
  def visitCtorEta (ctorname : Name) (arity : Nat) (e : Expr) : EraseM LBTerm := do
    let type ← liftMetaM do Meta.inferType e
    e.withApp (fun f args => visitCtorEtaGo ctorname arity type f args)
  partial_fixpoint

  -- Invariant: type is the type of f *args.
  def visitCtorEtaGo (ctorname : Name) (arity : Nat) (type f : Expr) (args : Array Expr) : EraseM LBTerm :=
    if args.size >= arity then
      visitConstructor ctorname args
    else do
      -- As in `visitCasesEtaGo`, the supplied arguments are bound outside the new binders —
      -- but here *all* of them, since a constructor's fields are all evaluated unconditionally
      -- in the emitted block, unlike a `case`'s branch-guarded alternatives.
      let bs ← args.zipIdx.foldlM (fun bs a => do
        if ← etaArgIsValue (← read).lparams a.1 then return bs
        else return bs.push (a.2, ← liftMetaM (Meta.inferType a.1), ← visitExpr a.1)) #[]
      withEtaPrefixLets bs.toList args fun args =>
        forallMonocular type fun fvarid bodytype => do
          let res ← visitCtorEtaGo ctorname arity bodytype f (args.push (.fvar fvarid))
          mkLambda fvarid res
  partial_fixpoint

  def visitConstructor (ctorname: Name) (args: Array Expr): EraseM LBTerm := do
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
  partial_fixpoint

  /-- Normal application of a function to some arguments. -/
  def visitAppArgs (f : LBTerm) (args : Array Expr) : EraseM LBTerm := do
      args.foldlM (fun e arg => do return LBTerm.app e (← visitExpr arg)) f
  partial_fixpoint

  def visitCases (casesInfo : CasesInfo) (args: Array Expr) : EraseM LBTerm := do
    let discr_nt ← visitExpr args[casesInfo.discrPos]!
    -- The declaration's own prefix, which the machine-`Nat`/`Int` arms below key on: those arms
    -- are for a plain `Nat.casesOn`/`Int.casesOn`. The inductive being eliminated is
    -- `casesInfo.indName` (see the general arm); for a `casesOn` auxiliary generated for a
    -- function the two differ, the prefix then being that function.
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
      -- `CasesInfo.indName` is read off the type of the major premise, so it names the
      -- inductive for a sparse `casesOn` auxiliary as well, whose `declName` prefix does not.
      let indName := casesInfo.indName
      let .inductInfo indVal ← getConstInfo indName
        | throwError "Erasure.visitCases: {casesInfo.declName} eliminates {indName}, which is not an inductive type."
      let machineInts := match (← read).config.nat with | .machine => true | .peano => false
      if machineInts && (indName == ``Nat || indName == ``Int) then
        throwError "Erasure.visitCases: {casesInfo.declName} eliminates {indName}, which machine-`Nat` mode represents as a primitive integer; only a plain `casesOn` can be compiled against that representation."
      unless casesInfo.altsRange.lower == casesInfo.discrPos + 1 do
        throwError "Erasure.visitCases: {casesInfo.declName} is a per-constructor elimination with a side condition, which λbox's `case` cannot express."
      -- A `case` on a propositional inductive is collapsed downstream — `remove_match_on_box`
      -- (`EOptimizePropDiscr.v:48`) and `eval_iota_sing` (`EWcbvEval.v:162`) — by substituting a
      -- box for *every* binder of the single alternative, which is sound only when every field
      -- bound there is a proof. Lean admits large elimination for a `Prop` whose non-proof fields
      -- are recovered from the result indices (`Acc.intro`'s `x`, which `Acc.casesOn` binds), so
      -- the shape is reachable and the collapse would box data. Refuse it on the shape rather
      -- than on the name: an `Acc` clone compiles in Lean just as `Acc` does.
      if isPropositionalArity indVal.type then
        if let some (ctor_name, field) ← firstNonProofField indVal then
          throwError "Erasure.visitCases: {casesInfo.declName} eliminates the propositional inductive {indName}, whose constructor {ctor_name} has a field (number {field}) that is not a proof; λbox collapses such an elimination by boxing every field of the alternative, which would lose that field's data."
      let (indid, argmasks) ← register_inductive indVal
      -- A λbox `case` has one alternative per constructor, in constructor order, binding that
      -- constructor's fields. Find the source alternative covering each constructor; a sparse
      -- `casesOn` leaves some uncovered and supplies a catch-all instead. (An entry of
      -- `altNumParams` names the constructor it eliminates, or is the catch-all, and carries
      -- the number of fields resp. hypotheses it binds.)
      let altIdx: Array (Option Nat) := indVal.ctors.toArray.map fun ctorName =>
        casesInfo.altNumParams.findIdx? fun altInfo =>
          match altInfo with | .ctor c _ => c == ctorName | .default _ => false
      let numCtorAlts := casesInfo.altNumParams.countP
        fun altInfo => match altInfo with | .ctor .. => true | .default _ => false
      unless (altIdx.filterMap id).size == numCtorAlts do
        throwError "Erasure.visitCases: the constructor alternatives of {casesInfo.declName} do not correspond one-to-one to the constructors of {indName}."
      -- The catch-all, erased once and applied to a box for each of its hypotheses: those are
      -- the proofs that the discriminee is none of the covered constructors. It does not bind
      -- the fields of the constructors it stands for, so the alternatives built from it bind
      -- them anonymously; the erased body is still locally nameless, so `abstract` shifts its
      -- variables past those binders. `hasLooseBVar` checks the premise of that argument.
      let dflt: Option LBTerm ←
        if altIdx.all (·.isSome) then pure .none
        else match casesInfo.altNumParams.findIdx? (fun altInfo => match altInfo with | .default _ => true | .ctor .. => false) with
        | .none =>
          throwError "Erasure.visitCases: {casesInfo.declName} covers only {numCtorAlts} of the {indVal.ctors.length} constructors of {indName} and has no catch-all alternative."
        | .some j => do
          unless numCtorAlts + 1 == casesInfo.altNumParams.size do
            throwError "Erasure.visitCases: {casesInfo.declName} has more than one catch-all alternative."
          let numHyps := match casesInfo.altNumParams[j]! with | .ctor _ n => n | .default n => n
          let body ← visitExpr args[casesInfo.altsRange.lower + j]!
          if body.hasLooseBVar then
            throwError "Erasure.visitCases: the catch-all of {casesInfo.declName} erased to a term with a free de Bruijn index, which cannot be moved under the binders of an alternative."
          logInfo s!"Expanding the catch-all of {casesInfo.declName} into {(altIdx.filter (·.isNone)).size} alternative(s)."
          pure <| .some <| (List.range numHyps).foldl (fun t _ => LBTerm.app t .box) body
      let mut alts := #[]
      for (alt?, cidx) in altIdx.zipIdx do
        let argmask := argmasks[cidx]!
        match alt? with
        | .some j =>
          let numFields := match casesInfo.altNumParams[j]! with | .ctor _ n => n | .default n => n
          alts := alts.push (← visitAlt numFields argmask args[casesInfo.altsRange.lower + j]!)
        | .none =>
          match dflt with
          | .some body => alts := alts.push (List.replicate (argmask.count .keep) .anon, body)
          | .none =>
            throwError "Erasure.visitCases: constructor {indVal.ctors[cidx]!} of {indName} is left without an alternative."
      pure <| LBTerm.case (indid, indVal.numParams) discr_nt alts.toList
    )

    -- The casesOn function may be overapplied, so handle the extra arguments.
    -- (`.toArray`: iterate the Array copy rather than the `Subarray` — same elements;
    -- v4.29's `Subarray` `ForIn` goes through the iterator framework, for which no
    -- `partial_fixpoint` monotonicity lemma is derivable without `LawfulMonad EST`.)
    for arg in (args[casesInfo.arity:]).toArray do
      ret := .app ret (← visitExpr arg)
    return ret
  partial_fixpoint

  /--
  Visit a `matcher`/`casesOn` alternative.
  On the Lean side, e should be a function taking numFields arguments.
  For λbox, I think we only need the body, as the LBTerm.cases constructor handles the bindings.
  -/
  def visitAlt (numFields : Nat) (argmask: ConstructorArgMask) (e : Expr) : EraseM (List BinderName × LBTerm) := do
    lambdaOrIntroToArity e (← liftMetaM <| Meta.inferType e) numFields fun e fvarids => do
      mkAlt (filter argmask fvarids.toArray).toList (← visitExpr e)
  partial_fixpoint

  def get_constant_kername (n: Name): EraseM Kername := do
    if let .some kn := (← get).constants.get? n then
      return kn
    else
     visitMutual n
     return (← get).constants[n]!
  partial_fixpoint

  /--
  Add all the declarations in the Lean-side mutual block of `name` to the global_declarations,
  and add their mappings to kernames to the erasure state.
  -/
  def visitMutual (name: Name): EraseM Unit := do
    -- Use original recursive definition, not the elaborated one with recursors, if available.
    let ci := (← Compiler.LCNF.getDeclInfo? name).get!
    let names := ci.all -- possibly these are ._unsafe_rec
    let single_decl := names.length == 1
    -- Lean's @[inline] attribute is name-based, so we can decide pre-erasure.
    let leanInline := single_decl && match Compiler.getInlineAttribute? (← getEnv) name with
      | .some .inline | .some .alwaysInline => true
      | _ => false
    -- A single declaration may have to be output as an axiom.
    if single_decl then
      if leanInline then
        logInfo s!"Name {name} is marked as inline."
        modify (fun s => { s with inlinings := s.inlinings.cons (toKername name) })
      match ci.value? (allowOpaque := true), isExtern (← getEnv) name, (← read).config.extern with
      | .none, _, _ =>
        if let .quotInfo qv := ci then
          logInfo s!"No value found for name {name}, emitting the quotient realizer."
          return ← addRealizer name (quotRealizer qv.kind)
        if let .recInfo rv := ci then
          if let some t := (← recursorRealizer rv) then
            logInfo s!"No value found for name {name}, synthesizing its eliminator body."
            return ← addRealizer name t
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
      let t ← withReader (fun env => { env with fixvars := .none, lparams := ci.levelParams }) do
        pure (← visitExpr (← prepare_erasure e))
      let kn := toKername name
      checkKernameFresh name kn
      modify (fun s => { s with constants := s.constants.insert name kn, gdecls := s.gdecls.cons (kn, .constantDecl <| ⟨.some t⟩) })
      -- Post-erasure: structurally detect typeclass-dispatch artifacts and mark them inline.
      -- Skipped if @[inline] already added this constant, or if the body contains a `fix`
      -- (inlining recursion would unfold the recursive definition at every call site).
      if (← read).config.auto_inline_typeclass_dispatch && !leanInline && !t.containsFix then
        let isInst ← Lean.Meta.isInstance name
        if isInst then
          logInfo s!"Auto-inlining typeclass instance {name}."
          modify (fun s => { s with inlinings := s.inlinings.cons kn })
        else if t.isTrivialAlias then
          logInfo s!"Auto-inlining trivial alias {name}."
          modify (fun s => { s with inlinings := s.inlinings.cons kn })
    else -- translate into a mutual fixpoint declaration
      let ids ← names.mapM (fun _ => mkFreshFVarId)
      let fixvarnames := names.map remove_unsafe_rec
      -- `remove_unsafe_rec` strips one literal `_unsafe_rec` component, so it is not
      -- injective: a block holding both `u` and `u._unsafe_rec` maps to `[u, u]` and would
      -- register two declarations under one λbox key. Refuse rather than let the second
      -- registration silently overwrite the first.
      unless (fixvarnames.map toKername).Nodup do
        throwError "Erasure.visitMutual: mutual block {names} maps to colliding λbox keys {fixvarnames}."
      withReader (fun env => { env with fixvars := fixvarnames |>.zip ids |> Std.HashMap.ofList |> .some }) do
        let defs: List FixDef ← names.mapM (fun n => do
          let ci ← getConstInfo n -- here n is directly from the above ci.all, possibly _unsafe_rec
          let e: Expr := ci.value! (allowOpaque := true)
          let t: LBTerm ← withReader (fun env => { env with lparams := ci.levelParams }) do
            visitExpr (← prepare_erasure e)
          mkDef (remove_unsafe_rec n) fixvarnames t
        )
        for (n, i) in fixvarnames.zipIdx do
          let kn := toKername n
          checkKernameFresh n kn
          modify (fun s => { s with constants := s.constants.insert n kn, gdecls := s.gdecls.cons (kn, .constantDecl ⟨.some <| etaExpandFix defs i⟩) })
  partial_fixpoint
end

/--
Copied over from toLCNF, then quite heavily pruned and modified.

This not only erases the expression but also gives a context with all necessary global declarations of inductive types and top-level constants.
-/
def erase (e : Expr) (config: ErasureConfig): CoreM (Program × List Kername) := do
  let (t, s) ← run (do visitExpr (← prepare_erasure e)) config
  return (.untyped s.gdecls (.some t), s.inlinings)

inductive MLType: Type where
  | arrow (a b: MLType)
  | Z
  | unit
  | bool
  | string
  | list (a: MLType)
  | option (a: MLType)
  | array (a: MLType)
  | prod (a b: MLType)
deriving Inhabited

partial def MLType.toString: MLType -> String
  | arrow a b => s!"{protArrow a} -> {b.toString}"
  | Z => "Z.t"
  | unit => "unit"
  | bool => "bool"
  | string => "string"
  | list a => s!"{protCtor a} list"
  | option a => s!"{protCtor a} option"
  | array a => s!"{protCtor a} LeanArray.array"
  | prod a b => s!"{protArrow a} * {protArrow b}"
where
  protArrow (t: MLType): String := match t with
    | arrow .. => s!"({t.toString})"
    | _ => t.toString
  protCtor (t: MLType): String := match t with
    | arrow .. | prod .. => s!"({t.toString})"
    | _ => t.toString

instance : ToString MLType := ⟨MLType.toString⟩

partial def to_ml_type (ty: Expr): MetaM MLType :=
  Meta.forallTelescopeReducing ty fun vars body => do
    let vartypes ← vars.mapM Meta.inferType
    let varmltypes ← vartypes.mapM to_ml_type
    let bodymltype ← match (← Meta.whnf body) with
    | .const `Nat _ => pure .Z
    | .const `Int _ => pure .Z
    | .const `Unit _ | .const `PUnit _ => pure .unit
    | .const `Bool _ => pure .bool
    | .const `String _ => pure .string
    | .app (.const `List _) a => pure <| .list (← to_ml_type a)
    | .app (.const `Option _) a => pure <| .option (← to_ml_type a)
    | .app (.const `Array _) a => pure <| .array (← to_ml_type a)
    | .app (.app (.const `Prod _) a) b => pure <| .prod (← to_ml_type a) (← to_ml_type b)
    | t => logWarning s!"failed to translate {t} into ML type, emitting unit instead." ; pure .unit
    return varmltypes.foldr .arrow bodymltype

def gen_mli (ty: Expr): MetaM String := do return s!"val main: {← to_ml_type ty}"

syntax (name := erasestx) "#erase" ppSpace term (ppSpace "config" term)? (ppSpace "to" ppSpace str)? (ppSpace "mli" ppSpace str)?: command

@[command_elab erasestx]
def eraseElab: Elab.Command.CommandElab
  | `(command| #erase $t:term $[config $cfg?:term]? $[to $path?:str]? $[mli $mli?:str]?) => Elab.Command.liftTermElabM do
    let e: Expr ← Elab.Term.elabTerm t (expectedType? := .none)
    Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let e ← Lean.instantiateMVars e

    let cfg: ErasureConfig ← match cfg? with
    | .none => pure {}
    | .some cfg => unsafe Elab.Term.evalTerm ErasureConfig (.const ``Erasure.ErasureConfig []) cfg

    let (p, inls) ← erase e cfg
    let s: String := p |> Serialize.to_sexpr |>.toString
    -- logInfo s!"{repr p}"
    match path? with
    | .some path => do
        IO.FS.writeFile path.getString s
    | .none => logInfo s

    let c: AttributesConfig := { inlinings := inls, constRemappings := [], indRemappings := [], cstrReorders := [], customAttributes := [] }
    let c_s := c |> Serialize.to_sexpr |>.toString
    match path? with
    | .some path => do
        IO.FS.writeFile (path.getString ++ ".inlinings") c_s
    | .none => logInfo s

    let ty: Expr ← Meta.inferType e
    let mlistr ← gen_mli ty
    match mli? with
    | .none => logInfo mlistr
    | .some mlipath => IO.FS.writeFile mlipath.getString mlistr

  | _ => Elab.throwUnsupportedSyntax

end Erasure
