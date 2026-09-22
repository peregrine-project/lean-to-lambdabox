/-
Regression test for F-DEPTH.

`isArityCheck` used to fuel `isArityCheck.loop` from `ty.approxDepth.toNat + 1` —
`Lean.Expr.Data.approxDepth` is eight bits, so the fuel saturates at 256 however deep the
*reduced* telescope actually is, and it is **1** at a definitional alias (`approxDepth = 0`),
whatever telescope the alias unfolds to. Both shapes made the loop throw before reaching the
`.sort` at the end of the telescope; `Erasure.isErasable` then took the `.error` arm and fell
back to the elaborator's `isErasableMeta`, which does not unfold an `@[irreducible]` alias
either and answered `false` — an inductive **type former** judged relevant, the one shape the
erasure must not treat as data.

The test is the finding's own reproducer: `Bar`, an inductive whose arity is an
`@[irreducible]` alias `DeepArity` (a four-`Nat`-binder telescope, `approxDepth = 0`). It
checks both the raw kernel check (`LeanToLambdaBox.isErasable`, which used to report `error`
on `Bar` and must now report `ok true`) and the wrapper the eraser actually calls
(`Erasure.isErasable`, which used to fall through to `isErasableMeta` and answer `false` on
`Bar` and must now answer `true` straight from the kernel). A telescope of 300 plain `Sort 0`
binders (deeper than the old 256 cap, with no alias involved) is checked the same way, so the
fix is exercised at both the fuel-saturation point and the zero-depth-alias point the finding
raises.

This test calls the relevance oracle directly rather than erasing a whole program: `Bar` has no
constructors an ordinary source file could apply, so there is no well-typed program to run it
through `erase`, and no `.ast` for `scripts/fixes.sh` to hand to `peregrine`.
-/
import LeanToLambdaBox.Erasure

open Lean Erasure

-- Every declaration of a test lives in its own namespace, so that the suite's files share the
-- root namespace without colliding.
namespace FDepth

-- The finding's own alias reproducer: an inductive whose arity is hidden behind a
-- definitional alias made `@[irreducible]` after the `inductive` elaborates against it.
def DeepArity : Type 1 := Nat → Nat → Nat → Nat → Type
inductive Bar : DeepArity
attribute [irreducible] DeepArity

/-- `n`-deep telescope of `Sort 0` binders ending in `Sort 0`, built directly as an `Expr` (no
source declaration needed) — the finding's own `tele`. -/
def tele : Nat → Expr
  | 0     => .sort .zero
  | n + 1 => .forallE `x (.sort .zero) (tele n) .default

/-- Run the raw kernel relevance oracle (`isProp ∨ isArity` on `inferType e`) on a closed
`Expr` and report `ok <verdict>` or `error`. -/
def checkKernel (label : String) (e : Expr) : CoreM Unit := do
  let env ← getEnv
  match Lean4Lean.TypeChecker.M.run env.toKernelEnv (safety := .safe) (lctx := {}) (lparams := [])
      (x := Lean4Lean.TypeChecker.RecM.run (LeanToLambdaBox.isErasable e)) with
  | .ok b    => IO.println s!"F-DEPTH {label} kernel: ok {b}"
  | .error _ => IO.println s!"F-DEPTH {label} kernel: error"

/-- Run `isArityCheck` itself (not the full oracle, so a closed telescope can stand in
directly for a type, with no declaration to infer it from) and report `ok <verdict>` or
`error`. -/
def checkArity (label : String) (ty : Expr) : CoreM Unit := do
  let env ← getEnv
  match Lean4Lean.TypeChecker.M.run env.toKernelEnv (safety := .safe) (lctx := {}) (lparams := [])
      (x := Lean4Lean.TypeChecker.RecM.run (LeanToLambdaBox.isArityCheck ty)) with
  | .ok b    => IO.println s!"F-DEPTH {label} kernel: ok {b}"
  | .error _ => IO.println s!"F-DEPTH {label} kernel: error"

/-- Run the wrapper the shipping eraser actually calls (kernel, falling back to the elaborator
on error) and report its verdict. -/
def checkWrapper (label : String) (e : Expr) : MetaM Unit := do
  let b ← Erasure.isErasable [] e
  IO.println s!"F-DEPTH {label} wrapper: {b}"

#eval show CoreM Unit from do
  checkKernel "Bar" (mkConst ``Bar)
  checkArity "telescope300" (tele 300)

#eval show MetaM Unit from do
  checkWrapper "Bar" (mkConst ``Bar)

end FDepth
