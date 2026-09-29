import LeanToLambdaBox

/-!
# The pure path next to the `Meta` path

`scripts/pure-harness.sh` elaborates a copy of each file of `tests/corpus/` that also imports this
module. The module adds a second elaborator for `#erase`, which Lean tries before the eraser's own.
For `#erase t [config c] to "f"` it elaborates `t` and `c` as `#erase` does and computes
`collectDeps (EnvView.ofEnvironment env) t`. If the closure is in the fragment, it also
- runs `erasePure` (the pure path) and `Erasure.erase` (the `Meta` path of `#erase`), and writes their
  outputs, in the format of `#erase`, to `f.pure` and `f.meta`, each with its `.inlinings`;
- runs the traversal again with the backend `CmpM`, whose operations are those of `PureM` and whose
  oracle also asks `Erasure.isErasable` (the `Meta` oracle) in the traversal's local context, and
  counts the calls and the calls where the two answers differ.

It writes what it found to `f.harness`. Then it declines the command (`throwUnsupportedSyntax`):
Lean restores the command state and runs the eraser's own elaborator, so `#erase` writes `f` and
reports its messages as without this module. Nothing is written for an `#erase` without `to`.
-/

open Lean Elab Command Erasure

namespace PureHarness

/-- An error of the pure path as text. -/
def showErr : EraseError → String
  | .outOfFragment w => s!"outOfFragment {w}"
  | .nameCollision a b => s!"nameCollision {a} {b}"
  | .fuel s => s!"fuel {s}"
  | .failed m => s!"failed {m}"

/-- A message on one line, runs of white space collapsed. -/
def oneLine (s : String) : String :=
  (s.foldl (fun (acc : String × Bool) c =>
    if c.isWhitespace then (acc.1, true)
    else ((if acc.2 && !acc.1.isEmpty then acc.1.push ' ' else acc.1).push c, false))
    ("", false)).1

/-- An answer of the pure oracle as text. -/
def showPure : Except EraseError Bool → String
  | .ok b => s!"ok {b}"
  | .error e => s!"error {showErr e}"

/-- An oracle call at which the pure oracle and the `Meta` oracle answer differently. -/
structure Diff where
  term : String
  pureAnswer : String
  metaAnswer : String

/-- What the harness backend records: the number of oracle calls and the calls that differ. -/
structure CmpState where
  calls : Nat := 0
  diffs : Array Diff := #[]

/-- The harness backend: `PureM` over `CoreM`, which runs `Meta`, with the record `CmpState`. -/
abbrev CmpM := ReaderT PureCtx (StateT PureState (ExceptT EraseError (StateT CmpState CoreM)))

/-- An action of `PureM` in `CmpM`: the same result, error and backend state. -/
def liftP {α} (x : PureM α) : CmpM α := fun pc ps => ExceptT.mk (pure ((x.run pc).run ps))

/-- The answer of the `Meta` oracle `Erasure.isErasable` in a local context, as text. -/
def metaAnswer (lctx : LocalContext) (e : Expr) : CoreM String := do
  try
    return s!"ok {← runMetaM lctx (Erasure.isErasable e)}"
  catch ex =>
    return s!"error {oneLine (← ex.toMessageData.toString)}"

/-- A term, pretty-printed in a local context, on one line. -/
def ppIn (lctx : LocalContext) (e : Expr) : CoreM String := do
  let f ← runMetaM lctx (Meta.ppExpr e)
  return oneLine (toString f)

/-- Every operation is the one of `PureM`, run in `CmpM`; the oracle also records the `Meta`
answer. -/
instance : Backend CmpM where
  findConst? n := liftP (Backend.findConst? n)
  unknownConstant n := liftP (Backend.unknownConstant n)
  declInfo? n := liftP (Backend.declInfo? n)
  unsafeRecBase? := Backend.unsafeRecBase? (m := PureM)
  freshFVarId := liftP (Backend.freshFVarId (m := PureM))
  instantiate1 := Backend.instantiate1 (m := PureM)
  isErasable lctx ls e := do
    let r := ((Backend.isErasable (m := PureM) lctx ls e).run (← readThe PureCtx)).run
      (← getThe PureState)
    let p := showPure (r.map (·.1))
    let m ← (metaAnswer lctx e : CoreM String)
    let t ← (ppIn lctx e : CoreM String)
    modifyThe CmpState fun s =>
      { calls := s.calls + 1, diffs := if p == m then s.diffs else s.diffs.push ⟨t, p, m⟩ }
    liftP (Backend.isErasable (m := PureM) lctx ls e)
  inferType lctx ls e := liftP (Backend.inferType lctx ls e)
  casesInfo? n := liftP (Backend.casesInfo? n)
  ctorArity? n := liftP (Backend.ctorArity? n)
  argMask lctx ci := liftP (Backend.argMask lctx ci)
  isExtern n := liftP (Backend.isExtern n)
  inlineAttr? n := liftP (Backend.inlineAttr? n)
  isInstance n := liftP (Backend.isInstance n)
  prepare cfg e := liftP (Backend.prepare cfg e)
  log s := liftP (Backend.log (m := PureM) s)
  outOfFuel site := liftP (Backend.outOfFuel site)

/-- The run of `erasePure`, with the backend `CmpM` in place of `PureM`. -/
def erasePureCmp (view : EnvView) (cfg : ErasureConfig) (decls : List ConstantInfo) (e : Expr) :
    CoreM (Except EraseError (Program × List Kername) × CmpState) := do
  let x : CmpM (LBTerm × ErasureState) :=
    ((visitExpr (m := CmpM) travFuel e).run {}).run { «config» := cfg }
  let (r, cs) ← (((x.run ⟨decls, view⟩).run {}).run).run {}
  return (r.map fun ((t, s), _) => (.untyped s.gdecls (some t), s.inlinings), cs)

/-- The program and the attributes file of an erasure, as `#erase` writes them. -/
def render (r : Program × List Kername) : String × String :=
  let c : AttributesConfig :=
    { inlinings := r.2, constRemappings := [], indRemappings := [], cstrReorders := [],
      customAttributes := [] }
  (r.1 |> Serialize.to_sexpr |>.toString, c |> Serialize.to_sexpr |>.toString)

/-- Write an erasure to `f` and `f.inlinings`. -/
def writeOut (f : String) (r : Program × List Kername) : IO Unit := do
  let (p, c) := render r
  IO.FS.writeFile f p
  IO.FS.writeFile (f ++ ".inlinings") c

/-- The harness on one `#erase t [config c] to "f"`: its record, as text. -/
def harness (t : Term) (cfg? : Option Term) (f : String) : TermElabM String := do
  let e ← Term.elabTerm t (expectedType? := none)
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let cfg : ErasureConfig ← match cfg? with
    | none => pure {}
    | some c => unsafe Term.evalTerm ErasureConfig (.const ``ErasureConfig []) c
  let view := EnvView.ofEnvironment (← getEnv)
  match collectDeps view e with
  | .error (.outOfFragment w) => return s!"collectDeps: outOfFragment {w}\n"
  | .error err => return s!"collectDeps: {showErr err}\n"
  | .ok decls =>
    let mut out := s!"collectDeps: ok\n"
    let pr := erasePure view cfg decls e
    match pr with
    | .ok r => writeOut (f ++ ".pure") r; out := out ++ "erasePure: ok\n"
    | .error err => out := out ++ s!"erasePure: error {showErr err}\n"
    try
      let r ← (erase e cfg : CoreM _)
      writeOut (f ++ ".meta") r
      out := out ++ "Meta: ok\n"
    catch ex =>
      out := out ++ s!"Meta: error {oneLine (← ex.toMessageData.toString)}\n"
    let (cr, cs) ← (erasePureCmp view cfg decls e : CoreM _)
    let same := match pr, cr with
      | .ok a, .ok b => render a == render b
      | .error a, .error b => showErr a == showErr b
      | _, _ => false
    out := out ++ s!"harness run equals erasePure: {same}\n"
    out := out ++ s!"oracle calls: {cs.calls}, differing from Meta: {cs.diffs.size}\n"
    for d in cs.diffs do
      out := out ++ s!"  {d.term} | pure {d.pureAnswer} | Meta {d.metaAnswer}\n"
    return out

/-- Runs `harness` on `#erase ... to "f"`, writes its record to `f.harness`, and declines the
command, so that the eraser's own elaborator runs it. -/
@[command_elab Erasure.erasestx]
def harnessElab : CommandElab
  | `(command| #erase $t:term $[config $cfg?:term]? $[to $path?:str]? $[mli $_mli?:str]?) => do
    if let some path := path? then
      let f := path.getString
      let record ← try liftTermElabM (harness t cfg? f)
        catch ex => pure s!"harness error: {oneLine (← ex.toMessageData.toString)}\n"
      IO.FS.writeFile (f ++ ".harness") record
    throwUnsupportedSyntax
  | _ => throwUnsupportedSyntax

end PureHarness
