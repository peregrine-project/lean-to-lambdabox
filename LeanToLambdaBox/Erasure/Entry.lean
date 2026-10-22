import LeanToLambdaBox.Erasure
import LeanToLambdaBox.Erasure.Collect
import LeanToLambdaBox.Erasure.Pure

/-!
# The entry point of `#erase`

`Erasure.eraseEntry view cfg e` is what `#erase` runs. `Erasure.route` decides the path from
the fragment test `collectDeps view cfg e`, which computes the program's closure as the pure
traversal reads it: a program in the fragment is erased by `erasePure` over its closure, a program
outside it by the `CoreM` backend (`Erasure.erase`), and every other error of `collectDeps` or of
`erasePure` is an error of `#erase`.
-/

open Lean

namespace Erasure

/-! ## The fragment test -/

/-- The constants of an expression, with `Nat` for a Nat literal, or the first exclusion: a free
variable, a metavariable, a level metavariable, a string literal, and under `nat := .machine` a Nat
literal or one of `Nat.zero`, `Nat.succ`, `Int.ofNat`, `Int.negSucc`, `Nat.casesOn`,
`Int.casesOn` (which the traversal turns into primitive integers). The structure name of a
projection is not a constant of the expression. Reference: `term_global_deps`
(`MR E/EAstUtils.v:406`), on the source side. -/
def exprConsts (cfg : ErasureConfig) : Expr → Except EraseError (List Name)
  | .bvar _ => pure []
  | .fvar _ => throw (.outOfFragment "free variable")
  | .mvar _ => throw (.outOfFragment "metavariable")
  | .sort u => if u.hasMVar' then throw (.outOfFragment "level metavariable") else pure []
  | .const c us =>
    if us.any (·.hasMVar') then throw (.outOfFragment "level metavariable")
    else match cfg.nat with
      | .machine =>
        if [``Nat.zero, ``Nat.succ, ``Int.ofNat, ``Int.negSucc, ``Nat.casesOn, ``Int.casesOn].contains c
        then throw (.outOfFragment s!"{c} under nat := .machine") else pure [c]
      | .peano => pure [c]
  | .app f a => return (← exprConsts cfg f) ++ (← exprConsts cfg a)
  | .lam _ t b _ | .forallE _ t b _ => return (← exprConsts cfg t) ++ (← exprConsts cfg b)
  | .letE _ t v b _ =>
    return (← exprConsts cfg t) ++ (← exprConsts cfg v) ++ (← exprConsts cfg b)
  | .lit (.natVal _) => match cfg.nat with
    | .machine => throw (.outOfFragment "Nat literal under nat := .machine")
    | .peano => pure [``Nat]
  | .lit (.strVal _) => throw (.outOfFragment "string literal")
  | .mdata _ e | .proj _ _ e => exprConsts cfg e

/-- The syntactic arity `Π x₁…xₙ, Sort u` of a type: `n` and `u`. Reference: `isArity`
(`MR P/PCUICTyping.v:29`). -/
def arityShape : Expr → Option (Nat × Level)
  | .sort u => some (0, u)
  | .forallE _ _ b _ => (arityShape b).map fun (n, u) => (n + 1, u)
  | .mdata _ e => arityShape e
  | _ => none

/-- The level is not zero under every assignment of its parameters `lps`: it is never zero when
every parameter is `1` (whether a level is zero depends only on which parameters are zero,
monotonically). Reference: none. -/
def mayBeNonZero (lps : List Name) (u : Level) : Bool :=
  (Pure.instLevel lps (lps.map fun _ => .succ .zero) u).isNeverZero

/-- The sort of an inductive type is written `Prop` or is never zero; otherwise `false` when it
may be both zero and not zero, and an exclusion when it is zero under every assignment without
being written `Prop` (the propositional flag of `register_inductive` reads the written sort) or
the type is not an arity. Reference: none. -/
def sortDecided (iv : InductiveVal) : Except EraseError Bool :=
  match arityShape iv.type with
  | some (_, .zero) => pure true
  | some (_, u) =>
    if u.isNeverZero then pure true
    else if mayBeNonZero iv.levelParams u then pure false
    else throw (.outOfFragment s!"inductive {iv.name} whose sort is Prop but not written Prop")
  | none => throw (.outOfFragment s!"inductive {iv.name} whose type is not an arity")

/-- The exclusions a declaration of the closure carries by itself: a quotient; a recursor (the
closure adds a recursor only as the companion of a recognized `casesOn`, never through
`closureStep`); an `unsafe` or `partial` definition, or a definition or an opaque with an
`_unsafe_rec` companion (a `partial def` is an opaque whose value is a dummy, compiled through its
companion); an `unsafe` opaque, axiom, inductive or constructor; an `implemented_by` target of a definition, an
opaque or an axiom; a nested inductive, or one whose sort is excluded by `sortDecided`; an
`@[extern]` constructor under `extern := .preferAxiom`. Reference: the declarations Metalean's
loader declines (`Metalean/Checker/Slow/Loader.lean:129-139`), and the eraser's remapping of
`@[extern]` constructors. -/
def declExclusion (view : EnvView) (cfg : ErasureConfig) : ConstantInfo → Except EraseError Unit
  | .quotInfo q => throw (.outOfFragment s!"quotient {q.name}")
  | .recInfo r => throw (.outOfFragment s!"recursor {r.name}")
  | .defnInfo d => do
    unless d.safety matches .safe do throw (.outOfFragment s!"unsafe or partial {d.name}")
    if (view.find? (Compiler.mkUnsafeRecName d.name)).isSome then
      throw (.outOfFragment s!"recursive definition {d.name}")
    if (view.implementedBy? d.name).isSome then
      throw (.outOfFragment s!"{d.name} has an implemented_by target")
  | .opaqueInfo o => do
    if o.isUnsafe then throw (.outOfFragment s!"unsafe {o.name}")
    if (view.find? (Compiler.mkUnsafeRecName o.name)).isSome then
      throw (.outOfFragment s!"partial definition {o.name}")
    if (view.implementedBy? o.name).isSome then
      throw (.outOfFragment s!"{o.name} has an implemented_by target")
  | .axiomInfo a => do
    if a.isUnsafe then throw (.outOfFragment s!"unsafe {a.name}")
    if (view.implementedBy? a.name).isSome then
      throw (.outOfFragment s!"{a.name} has an implemented_by target")
  | .thmInfo _ => pure ()
  | .inductInfo iv => do
    if iv.isUnsafe then throw (.outOfFragment s!"unsafe {iv.name}")
    if iv.numNested != 0 then throw (.outOfFragment s!"nested inductive {iv.name}")
    discard <| sortDecided iv
  | .ctorInfo cv => do
    if cv.isUnsafe then throw (.outOfFragment s!"unsafe {cv.name}")
    if cfg.extern == .preferAxiom && view.isExtern cv.name then
      throw (.outOfFragment s!"@[extern] constructor {cv.name}")

/-- Lookup through the view, only of a declaration of that name. -/
def viewFind (view : EnvView) (n : Name) : List ConstantInfo :=
  ((view.find? n).filter (·.name == n)).toList

/-- Whether the definition `ci` is a canonical `casesOn` (`casesInfo?`), over the declarations the
recognizer reads, looked up through the view: `ci`, `T`, `T.rec`, the constructors of `T` and the
members of `T.rec`'s block; then `T`, `T.rec` and `T`'s constructors. Reference: none. -/
def recognizeCasesOn (view : EnvView) (ci : ConstantInfo) :
    Option (InductiveVal × RecursorVal × List ConstantInfo) :=
  match ci.name with
  | .str T "casesOn" =>
    match viewFind view T, viewFind view (mkRecName T) with
    | [.inductInfo I], [.recInfo R] =>
      let ctors := I.ctors.flatMap (viewFind view)
      let ds := ci :: .inductInfo I :: .recInfo R :: ctors ++ R.all.flatMap (viewFind view)
      (casesInfo? ds ci.name).map fun _ => (I, R, ctors)
    | _, _ => none
  | _ => none

/-- Drop the names of the work list that the closure has, and stop with an exclusion at one that
is a recursor of the closure: the work list holds the constants of the read expressions and the
block members, constructors and inductives of the closure's declarations, so a recursor there is
read (the only recursors the closure keeps are the `T.rec` of recognized `T.casesOn`, whose value
the traversal does not read). Reference: none. -/
def dropKnown (acc : List ConstantInfo) : List Name → Except EraseError (List Name)
  | [] => pure []
  | n :: todo => match findConst acc n with
    | some (.recInfo _) => throw (.outOfFragment s!"recursor {n}")
    | some _ => dropKnown acc todo
    | none => pure (n :: todo)

/-- One declaration added to the closure: the names it makes the closure read, the companion
recursor if it is a recognized `T.casesOn`, and whether it is one. The read names: the constants
of its type; of its value if it is a definition that is not a recognized `casesOn`, or an opaque
(not of a theorem's value, which the traversal erases as a proof); its block members
(`ConstantInfo.all`); the constructors of an inductive; the inductive of a constructor; for a
recognized `T.casesOn`, `T` (its value is not read; a constructor field that is an index of the
constructor's type is an exclusion, since `visitAlt` substitutes such fields). Reference: the
dependencies `MR E/ErasureFunction.v:1602 erase_global_deps` follows. -/
def closureStep (view : EnvView) (cfg : ErasureConfig) (ci : ConstantInfo) :
    Except EraseError (List Name × Option ConstantInfo) := do
  declExclusion view cfg ci
  let ty ← exprConsts cfg ci.type
  match ci with
  | .defnInfo d => match recognizeCasesOn view ci with
    | some (I, R, ctors) =>
      for c in ctors do
        if let .ctorInfo cv := c then
          unless (indexFields cv.numParams cv.type).all (·.isNone) do
            throw (.outOfFragment s!"{ci.name} on a constructor with an index field")
      pure (ty ++ I.name :: d.all, some (.recInfo R))
    | none => return (ty ++ (← exprConsts cfg d.value) ++ d.all, none)
  | .thmInfo t => pure (ty ++ t.all, none)
  | .opaqueInfo o => return (ty ++ (← exprConsts cfg o.value) ++ o.all, none)
  | .inductInfo iv => pure (ty ++ iv.all ++ iv.ctors, none)
  | .ctorInfo cv => pure (ty ++ [cv.induct], none)
  | _ => pure (ty, none)

/-- Depth-first closure. `fuel` bounds the number of declarations added; names already in the
closure are dropped without fuel (`dropKnown`). The first exclusion stops the scan. A view that
answers `find? n` with a declaration of another name is rejected (a real `Environment` never does).
The second component lists the recognized `casesOn` of the closure. Reference:
`MR E/ErasureFunction.v:1602 erase_global_deps` (keeps what the term uses). -/
def closure (view : EnvView) (cfg : ErasureConfig) : Nat → List Name → List ConstantInfo →
    List Name → Except EraseError (List ConstantInfo × List Name)
  | 0, todo, acc, cases => do
    match ← dropKnown acc todo with
    | [] => pure (acc, cases)
    | _ => throw (.fuel "collectDeps")
  | f+1, todo, acc, cases => do
    match ← dropKnown acc todo with
    | [] => pure (acc, cases)
    | n :: todo => match view.find? n with
      | none => throw (.outOfFragment s!"unknown constant {n}")
      | some ci =>
        if ci.name != n then throw (.failed "view returned a declaration of another name")
        match ← closureStep view cfg ci with
        | (ns, none) => closure view cfg f (ns ++ todo) (ci :: acc) cases
        | (ns, some r) =>
          if (findConst acc r.name).isSome then
            closure view cfg f (ns ++ todo) (ci :: acc) (n :: cases)
          else
            closure view cfg f (ns ++ (← exprConsts cfg r.type) ++ todo) (r :: ci :: acc)
              (n :: cases)

/-- An inductive of the closure whose sort may be both zero and not zero, and that the traversal
may eliminate: its `casesOn` is recognized, or it has one constructor with a field (so it may be
projected). Reference: none. -/
def eliminatedUndecided (decls : List ConstantInfo) (cases : List Name) : Option Name :=
  decls.findSome? fun
    | .inductInfo iv =>
      let elim := cases.contains (.str iv.name "casesOn") || match iv.ctors with
        | [c] => match findConst decls c with
          | some (.ctorInfo cv) => 0 < cv.numFields
          | _ => false
        | _ => false
      if elim && sortDecided iv matches .ok false then some iv.name else none
    | _ => none

/-- Two λ□ global declarations of the closure with one kername that `findCollision` does not see:
an inductive block and another block with different members and the same block name
(`mutualBlockKername`), or an inductive block whose name is the kername of a definition, theorem,
opaque or axiom of the closure (an inductive's own name, constructors and recursor are not λ□
declarations). Reference: none (DV-14). -/
def findBlockCollision (decls : List ConstantInfo) : Option (Name × Name) :=
  let blocks := decls.filterMap fun | .inductInfo iv => some iv | _ => none
  blocks.findSome? fun iv₁ =>
    let k := mutualBlockKername iv₁.all
    match blocks.find? fun iv₂ => mutualBlockKername iv₂.all == k && iv₂.all != iv₁.all with
    | some iv₂ => some (iv₁.name, iv₂.name)
    | none => (decls.find? fun ci => (ci matches .defnInfo _ | .thmInfo _ | .opaqueInfo _ |
        .axiomInfo _) && toKername ci.name == k).map fun ci => (iv₁.name, ci.name)

/-- The fragment test: the program's closure as the pure traversal reads it, or the first
exclusion. The closure holds the constants of the term and, for each of its declarations, those
of its type; of its value if it is a definition that is not a recognized `casesOn` (`casesInfo?`),
or an opaque (not of theorems); its block members; the constructors of an inductive; the inductive
of a constructor; `Nat` for a Nat literal; for a recognized `T.casesOn`, `T` and `T.rec` (the
recognizer reads them; the value is not read, the recursor is not an exclusion).
`outOfFragment` exactly when the closure contains (`exprConsts`, `declExclusion`, `dropKnown`,
`closureStep`, `eliminatedUndecided`): a recursor other than the `T.rec` of a recognized
`T.casesOn`, or any recursor in a read expression; a quotient; a string literal; an
`unsafe`/`partial` constant, or one with an `_unsafe_rec` companion or an `implemented_by` target; a
nested or unsafe inductive; an `@[extern]` constructor under `extern := .preferAxiom`; under
`nat := .machine` a Nat literal, `Nat.zero`, `Nat.succ`, `Int.ofNat`, `Int.negSucc`, `Nat.casesOn`
or `Int.casesOn`; a recognized `casesOn` on an inductive with a constructor field that is an index
of the constructor's type (`indexFields`: `Acc`); an inductive whose sort may be both zero and not
zero that is cased on or has one constructor with a field; an inductive whose sort is zero under
every assignment but not written `Prop`; under `remove_irrel_constr_args`, any inductive type; a
free variable, a metavariable or a level metavariable; or a constant the view does not have.
The scan completes before the collision check, so `outOfFragment` takes precedence over
`nameCollision`, which is reported when two closure constants have one kername (`findCollision`)
or two λ□ declarations would (`findBlockCollision`). Reference: the environment `Σ'` that
`MR E/ErasureFunction.v:1602 erase_global_deps` keeps, computed on the source side (DV-3). -/
def collectDeps (view : EnvView) (cfg : ErasureConfig) (e : Expr) :
    Except EraseError (List ConstantInfo) := do
  let (decls, cases) ← closure view cfg collectFuel (← exprConsts cfg e) [] []
  if let some n := eliminatedUndecided decls cases then
    throw (.outOfFragment s!"cases or projection on {n}, whose sort may be Prop or not")
  if cfg.remove_irrel_constr_args then
    if let some (.inductInfo iv) := decls.find? (· matches .inductInfo _) then
      throw (.outOfFragment s!"inductive {iv.name} under remove_irrel_constr_args")
  match findCollision decls with
  | some (a, b) => throw (.nameCollision a b)
  | none => match findBlockCollision decls with
    | some (a, b) => throw (.nameCollision a b)
    | none => pure decls

/-- Where `#erase` sends an input. Reference: none. -/
inductive Route where
  | viaPure (r : Except EraseError (Program × List Kername))
  | viaMeta

/-- The routing decision: in-fragment programs take the pure path; `outOfFragment` goes to
the unchanged `Meta` path; every other `collectDeps` error is an error of `#erase`. Reference:
none. -/
def route (view : EnvView) (cfg : ErasureConfig) (e : Expr) : Route :=
  match collectDeps view cfg e with
  | .ok decls => .viaPure (erasePure view cfg decls e)
  | .error (.outOfFragment _) => .viaMeta
  | .error err => .viaPure (.error err)

/-- The text of an error of the pure path in the message of `#erase`. Reference: none. -/
def EraseError.describe : EraseError → String
  | .outOfFragment w => s!"outside the fragment: {w}"
  | .nameCollision a b => s!"the constants {a} and {b} have the same kername"
  | .fuel site => s!"out of fuel in {site}"
  | .failed msg => msg

/-- The `#erase` entry point. Reference: the erasure run of
`MR E/ErasureFunctionProperties.v:657 erase_correct`
(`erase … = t'`, `erase_global_deps … = Σ'`). -/
def eraseEntry (view : EnvView) (cfg : ErasureConfig) (e : Expr) :
    CoreM (Program × List Kername) :=
  match route view cfg e with
  | .viaPure (.ok r) => pure r
  | .viaPure (.error err) => throwError "erasure failed: {err.describe}"
  | .viaMeta => erase e cfg

end Erasure
