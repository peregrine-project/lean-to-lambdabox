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
projection is a constant of the expression, as the inductive of `tProj` is a global dependency in
`term_global_deps`. Reference: `term_global_deps` (`MR E/EAstUtils.v:406`, `tProj` at `:422`), on
the source side. -/
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
  | .mdata _ e => exprConsts cfg e
  | .proj S _ e => return S :: (← exprConsts cfg e)

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

/-- Lookup through the view, only of a declaration of that name. -/
def viewFind (view : EnvView) (n : Name) : List ConstantInfo :=
  ((view.find? n).filter (·.name == n)).toList

/-- Whether the recursor `r`, given the inductive types of its block and their constructors, has
the shape of the recursors in the fragment: its block is one inductive type without indices, which
eliminates into every sort (`r` has a universe parameter more than the inductive), and in each minor
premise (`recShape` of `r`'s type) the induction hypotheses take no arguments and are about the
last fields of the constructor, in order (the recursive fields come last and are not functions).
Reference: none. -/
def recShapeInFragment (r : RecursorVal) (ivs : List InductiveVal) (cvs : List ConstructorVal) :
    Bool :=
  match r.all, ivs with
  | [_], [iv] =>
    r.numIndices == 0 && r.levelParams.length != iv.levelParams.length &&
      match recShape r.numParams r.numMotives r.type (cvs.map (·.numFields)) with
      | some (_, minors) => minors.all fun mi =>
        mi.ihs.map (fun h => (h.field, h.binders)) ==
          (List.range' (mi.fields.length - mi.ihs.length) mi.ihs.length).map fun f => (f, [])
      | none => false
  | _, _ => false

/-- The exclusions a declaration of the closure carries by itself: a recursor that the
traversal keeps as a constant (`recStaysConstant`, over the inductive types of its block and their
constructors, looked up through the view: a nested block, `Nat` or `Int` under `nat := .machine`,
an inductive whose sort may be `Prop` with a constructor field that is an index), or that does not
have the shape `recShapeInFragment` admits (a mutual or indexed block, elimination only into
`Prop`, an induction hypothesis with arguments or before a non-recursive field); this is checked
only for a recursor the closure reads, not for one it adds as a companion; an `unsafe` or
`partial` definition, or a definition or an opaque with an `_unsafe_rec` companion (a `partial def` is an opaque whose value is a dummy, compiled through its
companion), except, under `structural := .kernel`, a definition by structural recursion
(`isStructuralRecursive`), which both paths erase through its kernel definition; a definition,
theorem or opaque of a mutual block (whose `all` is not the list of its own name alone); an
`unsafe` opaque, axiom, inductive or constructor; an `implemented_by` target of a definition, an
opaque or an axiom; a nested inductive, or one whose sort is excluded by `sortDecided`; an
`@[extern]` constructor under `extern := .preferAxiom`. Reference: the declarations Metalean's
loader declines (`Metalean/Checker/Slow/Loader.lean:129-139`), and the eraser's remapping of
`@[extern]` constructors. -/
def declExclusion (view : EnvView) (cfg : ErasureConfig) : ConstantInfo → Except EraseError Unit
  | .recInfo r => do
    let ivs := (r.all.flatMap (viewFind view)).filterMap fun | .inductInfo iv => some iv | _ => none
    let cvs := ((ivs.flatMap (·.ctors)).flatMap (viewFind view)).filterMap fun
      | .ctorInfo cv => some cv
      | _ => none
    if recStaysConstant cfg.nat r ivs cvs then
      throw (.outOfFragment s!"recursor {r.name}, which the eraser keeps as a constant")
    unless recShapeInFragment r ivs cvs do
      throw (.outOfFragment s!"recursor {r.name}, of a mutual or indexed block, eliminating only into Prop, or with an induction hypothesis that takes arguments or precedes a field")
  | .defnInfo d => do
    unless d.safety matches .safe do throw (.outOfFragment s!"unsafe or partial {d.name}")
    if (view.find? (Compiler.mkUnsafeRecName d.name)).isSome &&
        !(cfg.structural == .kernel && isStructuralRecursive (.defnInfo d)) then
      throw (.outOfFragment s!"recursive definition {d.name}")
    if (view.implementedBy? d.name).isSome then
      throw (.outOfFragment s!"{d.name} has an implemented_by target")
    unless d.all == [d.name] do throw (.outOfFragment s!"mutual block {d.all}")
  | .opaqueInfo o => do
    if o.isUnsafe then throw (.outOfFragment s!"unsafe {o.name}")
    if (view.find? (Compiler.mkUnsafeRecName o.name)).isSome then
      throw (.outOfFragment s!"partial definition {o.name}")
    if (view.implementedBy? o.name).isSome then
      throw (.outOfFragment s!"{o.name} has an implemented_by target")
    unless o.all == [o.name] do throw (.outOfFragment s!"mutual block {o.all}")
  | .axiomInfo a => do
    if a.isUnsafe then throw (.outOfFragment s!"unsafe {a.name}")
    if (view.implementedBy? a.name).isSome then
      throw (.outOfFragment s!"{a.name} has an implemented_by target")
  | .thmInfo t => unless t.all == [t.name] do throw (.outOfFragment s!"mutual block {t.all}")
  | .quotInfo _ => pure ()
  | .inductInfo iv => do
    if iv.isUnsafe then throw (.outOfFragment s!"unsafe {iv.name}")
    if iv.numNested != 0 then throw (.outOfFragment s!"nested inductive {iv.name}")
    discard <| sortDecided iv
  | .ctorInfo cv => do
    if cv.isUnsafe then throw (.outOfFragment s!"unsafe {cv.name}")
    if cfg.extern == .preferAxiom && view.isExtern cv.name then
      throw (.outOfFragment s!"@[extern] constructor {cv.name}")

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

/-- Drop the names of the work list that the closure has, and stop at one that is a recursor of
the closure that `declExclusion` excludes: the work list holds the constants of the read
expressions and the block members, constructors and inductives of the closure's declarations, so a
recursor there is read, and it may be in the closure as a companion (the `T.rec` of a recognized
`T.casesOn` or of an inductive `T` with one constructor), which `declExclusion` did not check.
Reference: none. -/
def dropKnown (view : EnvView) (cfg : ErasureConfig) (acc : List ConstantInfo) :
    List Name → Except EraseError (List Name)
  | [] => pure []
  | n :: todo => match findConst acc n with
    | some ci@(.recInfo _) => do declExclusion view cfg ci; dropKnown view cfg acc todo
    | some _ => dropKnown view cfg acc todo
    | none => pure (n :: todo)

/-- One declaration added to the closure: the names it makes the closure read, and the companion
recursor `T.rec` if it is a recognized `T.casesOn` or an inductive `T` with one constructor (the
oracle reads its universe parameters to type a projection of `T`). The read names: the constants
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
  | .inductInfo iv => pure (ty ++ iv.all ++ iv.ctors, match iv.ctors, viewFind view (mkRecName iv.name) with
    | [_], [r@(.recInfo _)] => some r
    | _, _ => none)
  | .ctorInfo cv => pure (ty ++ [cv.induct], none)
  | _ => pure (ty, none)

/-- Depth-first closure. `fuel` bounds the number of declarations added; names already in the
closure are dropped without fuel (`dropKnown`). The first exclusion stops the scan. A view that
answers `find? n` with a declaration of another name is rejected (a real `Environment` never does).
The second component lists the recognized `casesOn` of the closure (the definitions with a
companion). Reference:
`MR E/ErasureFunction.v:1602 erase_global_deps` (keeps what the term uses). -/
def closure (view : EnvView) (cfg : ErasureConfig) : Nat → List Name → List ConstantInfo →
    List Name → Except EraseError (List ConstantInfo × List Name)
  | 0, todo, acc, cases => do
    match ← dropKnown view cfg acc todo with
    | [] => pure (acc, cases)
    | _ => throw (.fuel "collectDeps")
  | f+1, todo, acc, cases => do
    match ← dropKnown view cfg acc todo with
    | [] => pure (acc, cases)
    | n :: todo => match view.find? n with
      | none => throw (.outOfFragment s!"unknown constant {n}")
      | some ci =>
        if ci.name != n then throw (.failed "view returned a declaration of another name")
        match ← closureStep view cfg ci with
        | (ns, none) => closure view cfg f (ns ++ todo) (ci :: acc) cases
        | (ns, some r) =>
          let cases := if ci matches .defnInfo _ then n :: cases else cases
          if (findConst acc r.name).isSome then
            closure view cfg f (ns ++ todo) (ci :: acc) cases
          else
            closure view cfg f (ns ++ (← exprConsts cfg r.type) ++ todo) (r :: ci :: acc) cases

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
of a constructor; the structure of a projection; `Nat` for a Nat literal; for a recognized `T.casesOn`, `T` and `T.rec` (the
recognizer reads them; the value is not read, the recursor is not an exclusion); for an inductive
`T` with one constructor, `T.rec` (the oracle reads it to type a projection; not an exclusion).
`outOfFragment` exactly when the closure contains (`exprConsts`, `declExclusion`, `dropKnown`,
`closureStep`, `eliminatedUndecided`): a recursor that a read expression or block names and that
the traversal keeps as a constant (`recStaysConstant`: a nested block, `Nat` or `Int` under
`nat := .machine`, an inductive whose sort may be `Prop` with a constructor field that is an index
of the constructor's type) or whose shape `recShapeInFragment` does not admit (a mutual or indexed
block, elimination only into `Prop`, an induction hypothesis that takes arguments or precedes a
field); a string literal; an
`unsafe`/`partial` constant, or one with an `_unsafe_rec` companion (except, under
`structural := .kernel`, a definition by structural recursion) or an `implemented_by` target; a
definition, theorem or opaque of a mutual block; a nested or unsafe inductive; an `@[extern]` constructor under `extern := .preferAxiom`; under
`nat := .machine` a Nat literal, `Nat.zero`, `Nat.succ`, `Int.ofNat`, `Int.negSucc`, `Nat.casesOn`
or `Int.casesOn`; a recognized `casesOn` on an inductive with a constructor field that is an index
of the constructor's type (`indexFields`: `Acc`); an inductive whose type is not syntactically an
arity `Π x₁…xₙ, Sort u` (`arityShape`, `sortDecided`); an inductive whose sort may be both zero and not
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

/-- A kername that two global declarations of the list have, if any (`seen`: the kernames before
the list). Reference: none (`toKername` and `mutualBlockKername` are not injective, DV-14). -/
def dupKername (ds : GlobalDeclarations) (seen : Std.HashSet Kername := {}) : Option Kername :=
  match ds with
  | [] => none
  | (k, _) :: ds => if seen.contains k then some k else dupKername ds (seen.insert k)

/-- The `#erase` entry point. On the `Meta` path, a program with two global declarations of one
kername is an error (on the pure path, `collectDeps` reports it). Reference: the erasure run of
`MR E/ErasureFunctionProperties.v:657 erase_correct`
(`erase … = t'`, `erase_global_deps … = Σ'`). -/
def eraseEntry (view : EnvView) (cfg : ErasureConfig) (e : Expr) :
    CoreM (Program × List Kername) :=
  match route view cfg e with
  | .viaPure (.ok r) => pure r
  | .viaPure (.error err) => throwError "erasure failed: {err.describe}"
  | .viaMeta => do
    let r@(.untyped ds _, _) ← erase e cfg
    if let some k := dupKername ds then
      throwError "erasure failed: two declarations of the program have the kername {Serialize.to_sexpr k}"
    pure r

end Erasure
