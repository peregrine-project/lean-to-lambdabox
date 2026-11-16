import LeanToLambdaBox

/-!
Under `structural := .unsafeRec` (the default), the pure path erases a definition by structural
recursion through its compiled pre-definition (register entry S-56): `Erasure.preDef?` is the value
of its `_unsafe_rec` companion with the companion's name renamed to the definition's
(`renameUnsafeRec`), `PureM.declInfo?` gives the definition with that value, `visitMutual` erases it
as a fixpoint, and the fragment test admits the definition and reads the constants of the
pre-definition. The test checks:
- `preDef?` on `Nat.add`: the renamed value of `Nat.add._unsafe_rec`, which mentions `Nat.add` and
  not the companion; `none` under `structural := .kernel`, on the well-founded `log2`, on the
  non-recursive `Nat.pred` and on the constructor `Nat.succ`; `PureM.declInfo?` gives `Nat.add`
  with its name, levels, type and block, and that value;
- under `{extern := .preferLogical, nat := .peano}`, `Nat.add 2 3`, `Nat.beq 2 3` and
  `[true, false, true].length` are in the fragment and take the pure path, whose output differs
  from the `Meta` path's (a matcher stays a constant); `erasePure` declares `Nat.add` as the
  fixpoint `tFix [⟨Nat.add, λ x. λ y. …, 0⟩] 0` and `Nat.add.match_1` as a constant; `#erase`
  writes `add.ast`, `beq.ast` and `length.ast`, which peregrine validates and evaluates to 5,
  `false` and 3;
- `Nat.add 2 3` under the same configuration with `remove_irrel_constr_args` is outside the
  fragment (which excludes every inductive type under that option) and takes the `Meta` path,
  which erases `Nat.add` through `Nat.add._unsafe_rec` as a fixpoint: `metaAdd.ast`, which
  peregrine validates and evaluates to 5;
- the well-founded `log2 8` is outside the fragment.
-/

-- peregrine: validate add.ast
-- peregrine: eval add.ast
-- peregrine: validate beq.ast
-- peregrine: eval beq.ast
-- peregrine: validate length.ast
-- peregrine: eval length.ast
-- peregrine: validate metaAdd.ast
-- peregrine: eval metaAdd.ast

open Lean Elab Command Erasure

namespace PUR
def log2 (n : Nat) : Nat := if n < 2 then 0 else 1 + log2 (n / 2)
termination_by n
decreasing_by omega
end PUR

/-- The configuration of the programs on the pure path. -/
def cfgL : ErasureConfig := { extern := .preferLogical, nat := .peano }

/-- `preDef?` of the declaration `n` of the elaboration environment, under `cfg`. -/
def preDefOf (cfg : ErasureConfig) (n : Name) : CoreM (Option Expr) := do
  let env ← getEnv
  return preDef? (EnvView.ofEnvironment env) cfg (env.find? n).get!

/-! ## The compiled pre-definition -/

/-- info: [true, true, false] -/
#guard_msgs in
#eval show CoreM _ from do
  let some (.defnInfo u) := (← getEnv).find? `Nat.add._unsafe_rec | throwError "no companion"
  let some pre ← preDefOf cfgL ``Nat.add | throwError "no pre-definition"
  return [pre == renameUnsafeRec u.value, nameOccurs ``Nat.add pre,
    nameOccurs `Nat.add._unsafe_rec pre]

/-- info: [false, false, false, false] -/
#guard_msgs in
#eval show CoreM _ from do
  return [(← preDefOf { cfgL with structural := .kernel } ``Nat.add).isSome,
    (← preDefOf cfgL ``PUR.log2).isSome, (← preDefOf cfgL ``Nat.pred).isSome,
    (← preDefOf cfgL ``Nat.succ).isSome]

/-- `Nat.add 2 3`, with the literals as `#erase` elaborates them. -/
def add23 : Expr :=
  let lit (n : Nat) : Expr :=
    mkApp3 (.const ``OfNat.ofNat [0]) (.const ``Nat []) (mkRawNatLit n)
      (mkApp (.const ``instOfNatNat []) (mkRawNatLit n))
  mkApp2 (.const ``Nat.add []) (lit 2) (lit 3)

/-- info: [true, true, true, true, true] -/
#guard_msgs in
#eval show CoreM _ from do
  let env ← getEnv
  let view := EnvView.ofEnvironment env
  let .ok decls := collectDeps view cfgL add23 | throwError "outside the fragment"
  let .ok (some ci, _) := ((PureM.declInfo? cfgL ``Nat.add).run ⟨decls, view⟩).run {}
    | throwError "no declaration"
  let k := (env.find? ``Nat.add).get!
  return [ci.name == k.name, ci.levelParams == k.levelParams, ci.type == k.type, ci.all == k.all,
    some ci.value! == (← preDefOf cfgL ``Nat.add)]

/-! ## Routes and outputs -/

/-- The route of the elaborated term `t` under `cfg`: the exclusion of the fragment test, or the
pure path's error, or whether the pure path's program equals the `Meta` path's. The messages of
the `Meta` run are dropped. -/
def routeOf (cfg : ErasureConfig) (t : TermElabM Syntax) : TermElabM String := do
  let e ← instantiateMVars (← Term.elabTerm (← t) none)
  let view := EnvView.ofEnvironment (← getEnv)
  match collectDeps view cfg e with
  | .error err => return err.describe
  | .ok decls => match erasePure view cfg decls e with
    | .error err => return s!"pure path: {err.describe}"
    | .ok (p, _) =>
      let saved ← Core.getMessageLog
      let (q, _) ← (erase e cfg : CoreM _)
      Core.setMessageLog saved
      return s!"pure path; equal to the Meta path: {(Serialize.to_sexpr p).toString ==
        (Serialize.to_sexpr q).toString}"

/--
info: ["pure path; equal to the Meta path: false", "pure path; equal to the Meta path: false",
  "pure path; equal to the Meta path: false", "outside the fragment: inductive OfNat under remove_irrel_constr_args",
  "outside the fragment: recursive definition PUR.log2"]
-/
#guard_msgs in
#eval show TermElabM _ from do
  return [← routeOf cfgL `(Nat.add 2 3), ← routeOf cfgL `(Nat.beq 2 3),
    ← routeOf cfgL `([true, false, true].length),
    ← routeOf { cfgL with remove_irrel_constr_args := true } `(Nat.add 2 3),
    ← routeOf cfgL `(PUR.log2 8)]

/-- The declarations of `Nat.add` and `Nat.add.match_1` in a program. -/
def addShape : Program → List String
  | .untyped ds _ =>
    [match ds.find? (·.1 == toKername ``Nat.add) with
      | some (_, .constantDecl ⟨some (.fix [d] 0)⟩) => match d.body with
        | .lambda _ (.lambda _ _) => s!"Nat.add: fix [{repr d.name}, λ λ _, {d.principalArgIdx}] 0"
        | _ => "Nat.add: fix whose body is not two λs"
      | _ => "Nat.add: not a fixpoint",
     match ds.find? (·.1 == toKername ``Nat.add.match_1) with
      | some (_, .constantDecl ⟨some _⟩) => "Nat.add.match_1: constant"
      | _ => "Nat.add.match_1: not a constant"]

/-- info: ["Nat.add: fix [BinderName.named \"Nat.add\", λ λ _, 0] 0", "Nat.add.match_1: constant"] -/
#guard_msgs in
#eval show CoreM _ from do
  let view := EnvView.ofEnvironment (← getEnv)
  match collectDeps view cfgL add23 >>= fun decls => erasePure view cfgL decls add23 with
  | .ok (p, _) => return addShape p
  | .error err => throwError err.describe

#guard_msgs (drop info, drop warning) in
#erase Nat.add 2 3 config {extern := .preferLogical, nat := .peano} to "add.ast"
#guard_msgs (drop info, drop warning) in
#erase Nat.beq 2 3 config {extern := .preferLogical, nat := .peano} to "beq.ast"
#guard_msgs (drop info, drop warning) in
#erase [true, false, true].length config {extern := .preferLogical, nat := .peano} to "length.ast"
#guard_msgs (drop info, drop warning) in
#erase Nat.add 2 3
  config {extern := .preferLogical, nat := .peano, remove_irrel_constr_args := true}
  to "metaAdd.ast"
