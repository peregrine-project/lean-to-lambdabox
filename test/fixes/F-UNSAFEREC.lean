/-
Regression test for F-UNSAFEREC.

`Erasure.remove_unsafe_rec` strips one literal `_unsafe_rec` component off a declaration name,
so it is not injective. A `mutual unsafe def` block that legally declares both `u` and
`u._unsafe_rec` therefore maps to `[u, u]`: `visitMutual` used to name both `FixDef`s `u` and
register both declarations at the one λbox key `u`, with no error, so the emitted program had two
constants under one key and no way to read the one the printer did not keep last.

The test erases two programs: the colliding block above, which must now be refused, and an
ordinary two-member mutual block with no such collision, which must still erase to one
declaration per member with distinct keys, byte-identically to before this fix.

With `FIXES_AST_DIR` set, a program that erases successfully is also written there, so
`scripts/fixes.sh` can run it through `peregrine validate`/`eval`.
-/
import LeanToLambdaBox.Erasure

open Lean Erasure

-- Every declaration of a test lives in its own namespace, so that the suite's files share the
-- root namespace without colliding.
namespace FUnsafeRec

-- The finding's own reproducer: `bad._unsafe_rec` is not the compiler-synthesized auxiliary,
-- but a second `unsafe def` in the same block that happens to carry that name. (`mutual` takes
-- no leading doc comment, hence the plain `--`.)
mutual
  unsafe def bad : Nat → Nat
    | 0 => 0
    | n + 1 => bad._unsafe_rec n
  unsafe def bad._unsafe_rec : Nat → Nat
    | 0 => 1
    | n + 1 => bad n
end

-- An ordinary mutual block, no name collides after `remove_unsafe_rec`.
mutual
  def isEven : Nat → Bool
    | 0 => true
    | n + 1 => isOdd n
  def isOdd : Nat → Bool
    | 0 => false
    | n + 1 => isEven n
end

def evenTest : Nat := if isEven 10 then 1 else 0

/-- Erase `name`; report either the raised error or the declaration/key counts of the emitted
program (kernames printed, so the count is over their text form rather than needing `Kername`'s
own equality). -/
def check (label : String) (name : Name) : MetaM Unit := do
  try
    let (p, _) ← erase (.const name []) { extern := .preferLogical, nat := .peano, csimp := false }
    let .untyped gdecls _ := p
    let keyStrs := gdecls.map fun (kn, _) => (repr kn).pretty
    IO.println s!"F-UNSAFEREC {label}: ok declarations={keyStrs.length} distinct-keys={keyStrs.eraseDups.length}"
    if let some dir ← IO.getEnv "FIXES_AST_DIR" then
      IO.FS.writeFile s!"{dir}/{label}.ast" (Serialize.to_sexpr p).toString
  catch e =>
    -- Normalized to one line: `MessageData.toString` may pretty-print the name list of a
    -- large block across lines, which would make the raw message an unstable thing to pin
    -- an expected file to.
    let msg := (← e.toMessageData.toString).replace "\n" " "
    let mentionsCollision := !((msg.splitOn "colliding λbox keys").length == 1)
    IO.println s!"F-UNSAFEREC {label}: error mentions-colliding-keys={mentionsCollision} : {msg}"

#eval show MetaM Unit from do
  check "bad" ``bad
  check "even" ``evenTest

end FUnsafeRec
