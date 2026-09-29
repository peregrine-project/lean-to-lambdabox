import LeanToLambdaBox

/-!
`#erase` runs `Erasure.eraseEntry` over the elaboration environment (register entry S-21).
`Erasure.route` sends a program whose closure (`collectDeps`) lies in the fragment to the pure path
(`erasePure`), a program outside it to the `Meta` path (`Erasure.erase`), and every other error of
`collectDeps` or `erasePure` to an error of `#erase`. The test checks, with the command `#route`
defined below, the route of each program and which path's output `eraseEntry` returns, and pins the
output of `#erase` on:
- programs in the fragment, which take the pure path: `useM := mfirst one one` with a
  `@[macro_inline]` `mfirst`, whose call the pure path keeps and the `Meta` path inlines;
  `pidHR := pid hR`, a proof whose type is a proposition only through an `@[irreducible]` alias,
  which the pure path erases to `□` and the `Meta` path keeps, and for which `#erase` logs no
  message about the axioms `R` and `hR`; `@pid.{1}`, with its universe given;
- programs outside the fragment, which take the `Meta` path: `useMN := mfirstN Nat.zero Nat.zero`
  (an inductive type; `#erase` inlines `mfirstN`), and `@pid` (a universe metavariable);
- the error of a program in the fragment whose closure has two constants with the same kername.
-/

-- peregrine: validate useM.ast
-- peregrine: eval useM.ast --anf=false
-- peregrine: validate pidHR.ast
-- peregrine: eval pidHR.ast --anf=false
-- peregrine: validate pid1.ast
-- peregrine: eval pid1.ast --anf=false
-- peregrine: validate useMN.ast

open Lean Elab Command Erasure

/-- A program as `#erase` writes it: the program and its attributes file. -/
def render (r : Program × List Kername) : String × String :=
  let c : AttributesConfig :=
    { inlinings := r.2, constRemappings := [], indRemappings := [], cstrReorders := [],
      customAttributes := [] }
  (r.1 |> Serialize.to_sexpr |>.toString, c |> Serialize.to_sexpr |>.toString)

/-- `#route t [config c]`: elaborate `t` and `c` as `#erase` does, and log the route of `t` over
the elaboration environment and whether the result of `eraseEntry` equals the pure path's
(`collectDeps`, `erasePure`) and the `Meta` path's (`erase`). The messages of these runs are
dropped. -/
syntax (name := routeCmd) "#route " term (" config " term)? : command

@[command_elab routeCmd]
def routeElab : CommandElab
  | `(command| #route $t:term $[config $cfg?:term]?) => liftTermElabM do
    let e ← Term.elabTerm t (expectedType? := none)
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let cfg : ErasureConfig ← match cfg? with
      | none => pure {}
      | some c => unsafe Term.evalTerm ErasureConfig (.const ``ErasureConfig []) c
    let view := EnvView.ofEnvironment (← getEnv)
    let r := match route view cfg e with
      | .viaPure (.ok _) => "viaPure ok"
      | .viaPure (.error err) => s!"viaPure error ({err.describe})"
      | .viaMeta => match collectDeps view e with
        | .error (.outOfFragment w) => s!"viaMeta ({w})"
        | _ => "viaMeta"
    let saved ← Core.getMessageLog
    let entry ← try pure (some (render (← (eraseEntry view cfg e : CoreM _)))) catch _ => pure none
    let pure? := match collectDeps view e >>= fun decls => erasePure view cfg decls e with
      | .ok p => some (render p)
      | .error _ => none
    let meta? ← try pure (some (render (← (erase e cfg : CoreM _)))) catch _ => pure none
    Core.setMessageLog saved
    let eq (a b : Option (String × String)) := match a, b with
      | some x, some y => x == y
      | _, _ => false
    logInfo m!"{r}; eraseEntry = pure: {eq entry pure?}; eraseEntry = Meta: {eq entry meta?}"
  | _ => throwUnsupportedSyntax

namespace ER
axiom A : Type
def CN := (A → A) → A → A
def one : CN := fun s z => s z

/-- `mfirst a b = a`, inlined by the `Meta` path before erasure. -/
@[macro_inline] def mfirst (a _b : CN) : CN := a
def useM : CN := mfirst one one

/-- The same outside the fragment (`Nat` is an inductive type). -/
@[macro_inline] def mfirstN (a _b : Nat) : Nat := a
def useMN : Nat := mfirstN Nat.zero Nat.zero

universe u
def pid {α : Sort u} (a : α) : α := a
def IProp : Type := Prop
axiom R : IProp
axiom hR : R
set_option linter.defProp false in
def pidHR : R := pid hR
attribute [irreducible] IProp

/-- `two'` has the kername of `two_u39`. -/
def two' : CN := fun s z => s (s z)
def «two_u39» : CN := fun s z => s z
def both : CN := fun s z => two' s («two_u39» s z)
end ER

/-- info: viaPure ok; eraseEntry = pure: true; eraseEntry = Meta: false -/
#guard_msgs in
#route ER.useM
/-- info: viaPure ok; eraseEntry = pure: true; eraseEntry = Meta: false -/
#guard_msgs in
#route ER.pidHR
/-- info: viaPure ok; eraseEntry = pure: true; eraseEntry = Meta: true -/
#guard_msgs in
#route @ER.pid.{1}
/-- info: viaMeta (inductive type); eraseEntry = pure: false; eraseEntry = Meta: true -/
#guard_msgs in
#route ER.useMN config {nat := .peano}
/-- info: viaMeta (level metavariable); eraseEntry = pure: false; eraseEntry = Meta: true -/
#guard_msgs in
#route @ER.pid
/--
info: viaPure error (the constants ER.two_u39 and ER.two' have the same kername); eraseEntry = pure: false; eraseEntry = Meta: false
-/
#guard_msgs in
#route ER.both

#guard_msgs (drop warning, drop info) in
#erase ER.useM to "useM.ast"
/--
warning: failed to translate ER.R into ML type, emitting unit instead.
---
info: val main: unit
-/
#guard_msgs in
#erase ER.pidHR to "pidHR.ast"
#guard_msgs (drop warning, drop info) in
#erase @ER.pid.{1} to "pid1.ast"
#guard_msgs (drop warning, drop info) in
#erase ER.useMN config {nat := .peano} to "useMN.ast"
#guard_msgs (drop warning, drop info) in
#erase @ER.pid to "pid.ast"
/-- error: erasure failed: the constants ER.two_u39 and ER.two' have the same kername -/
#guard_msgs (error) in
#erase ER.both to "both.ast"
