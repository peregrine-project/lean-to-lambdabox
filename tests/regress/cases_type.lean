import LeanToLambdaBox

/-!
The pure recognizer `Erasure.casesInfo?` accepts a `T.casesOn` only if its declared type has at
least as many leading syntactic `Π`s as the recognized arity (register entry S-37). The test adds
three inductives `CT.A`, `CT.B`, `CT.C` (`| f | t`) to the kernel directly, so Lean generates no
`casesOn` for them, and then a `T.casesOn` definition with the canonical value
`fun motive t f t' => T.rec motive f t' t`, which the kernel accepts, at the types:
- `CT.A`: the `casesOn` type wrapped in `mdata`;
- `CT.B`: the alias `CT.CasesTyB`, a definition whose value is the `casesOn` type;
- `CT.C`: the `casesOn` type itself (control).
The test checks:
- the pure recognizer (`recognizeCasesOn` over the environment, which `collectDeps` uses) rejects
  `CT.A.casesOn` and `CT.B.casesOn` and accepts `CT.C.casesOn` and the `casesOn` of an elaborated
  inductive `CT.D`;
- `getCasesInfo?`, the recognizer of the `Meta` path, rejects all three hand-built `casesOn`
  (Lean did not mark them as `casesOn`), so on `CT.A` and `CT.B` both paths agree;
- `#erase` routes `CT.A.casesOn.{1}` and `CT.B.casesOn.{1}` (no argument) to the `Meta` path: the
  closure reads the value, which reads the recursor, so `collectDeps` excludes it;
- `useD`, which applies `CT.D.casesOn` to its motive only (in `pick`), takes the pure path, and its
  `#erase` output is pinned (`useD.ast`), which peregrine evaluates to `CT.D.f`.
-/

-- peregrine: validate useD.ast
-- peregrine: eval useD.ast

open Lean Erasure

/-- Add `T : Type | f | t` to the kernel, and `T.casesOn` with the canonical value at the type
`wrap ty`, where `ty` is the `casesOn` type. -/
def addCases (T : Name) (wrap : Expr → Expr) : CoreM Unit := do
  let ty : Expr := .const T []
  let ctor (c : Name) : Constructor := { name := T ++ c, type := ty }
  let ind : InductiveType := { name := T, type := .sort 1, ctors := [ctor `f, ctor `t] }
  addDecl (.inductDecl [] 0 [ind] false)
  let R ← getConstInfoRec (mkRecName T)
  let u := Level.param R.levelParams[0]!
  -- `(motive : T → Sort u) → (t : T) → motive T.f → motive T.t → motive t`, and the binders.
  let doms : List (Name × Expr) :=
    [(`motive, .forallE `t ty (.sort u) .default), (`t, ty),
     (`f, .app (.bvar 1) (.const (T ++ `f) [])), (`t', .app (.bvar 2) (.const (T ++ `t) []))]
  let casesTy := doms.foldr (fun (n, d) b => .forallE n d b .default) (.app (.bvar 3) (.bvar 2))
  let value := doms.foldr (fun (n, d) b => .lam n d b .default)
    (mkApp4 (.const R.name [u]) (.bvar 3) (.bvar 1) (.bvar 0) (.bvar 2))
  let lps := R.levelParams
  addDecl (.defnDecl { name := T ++ `casesOn, levelParams := lps, type := wrap casesTy, value,
                       hints := .abbrev, safety := .safe })

run_cmd Lean.Elab.Command.liftCoreM do
  addCases `CT.A (.mdata {})
  addCases `CT.C id
  let ty : Expr := .const `CT.B []
  let ctors : List Constructor := [{ name := `CT.B.f, type := ty }, { name := `CT.B.t, type := ty }]
  addDecl (.inductDecl [] 0 [{ name := `CT.B, type := .sort 1, ctors }] false)

namespace CT
def CasesTyB.{u} : Sort (imax (u+1) u) :=
  (motive : B → Sort u) → (x : B) → motive B.f → motive B.t → motive x
inductive D where
  | f | t
def pick : D → D → D → D := @D.casesOn (fun _ => D)
def useD : D := pick D.t D.t D.f
end CT

run_cmd Lean.Elab.Command.liftCoreM do
  let R ← getConstInfoRec `CT.B.rec
  let u := Level.param R.levelParams[0]!
  let v := (← getConstInfoDefn `CT.C.casesOn).value.replace fun
    | .const n us => some (.const (n.replacePrefix `CT.C `CT.B) us)
    | _ => none
  let lps := R.levelParams
  addDecl (.defnDecl { name := `CT.B.casesOn, levelParams := lps, type := .const `CT.CasesTyB [u],
                       value := v, hints := .abbrev, safety := .safe })

/-- Whether the pure recognizer and `getCasesInfo?` recognize `n`. -/
def recognized (n : Name) : CoreM Unit := do
  let env ← getEnv
  let pure := (recognizeCasesOn (EnvView.ofEnvironment env) (← getConstInfo n)).isSome
  let viaMeta := (← getCasesInfo? n).isSome
  logInfo s!"{n}: pure {pure}, Meta {viaMeta}"

/-- info: CT.A.casesOn: pure false, Meta false -/
#guard_msgs in #eval recognized `CT.A.casesOn
/-- info: CT.B.casesOn: pure false, Meta false -/
#guard_msgs in #eval recognized `CT.B.casesOn
/-- info: CT.C.casesOn: pure true, Meta false -/
#guard_msgs in #eval recognized `CT.C.casesOn
/-- info: CT.D.casesOn: pure true, Meta true -/
#guard_msgs in #eval recognized ``CT.D.casesOn

/-- The route of `#erase` on `T.casesOn.{1}`. -/
def routeOf (n : Name) : CoreM Unit := do
  match route (EnvView.ofEnvironment (← getEnv)) {} (.const n [.succ .zero]) with
  | .viaPure (.ok _) => logInfo "viaPure ok"
  | .viaPure (.error err) => logInfo s!"viaPure error ({err.describe})"
  | .viaMeta => logInfo "viaMeta"

/-- info: viaMeta -/
#guard_msgs in #eval routeOf `CT.A.casesOn
/-- info: viaMeta -/
#guard_msgs in #eval routeOf `CT.B.casesOn
/-- info: viaPure ok -/
#guard_msgs in #eval show CoreM Unit from do
  match route (EnvView.ofEnvironment (← getEnv)) {} (.const ``CT.useD []) with
  | .viaPure (.ok _) => logInfo "viaPure ok"
  | .viaPure (.error err) => logInfo s!"viaPure error ({err.describe})"
  | .viaMeta => logInfo "viaMeta"

#guard_msgs (drop warning, drop info) in
#erase CT.useD to "useD.ast"
