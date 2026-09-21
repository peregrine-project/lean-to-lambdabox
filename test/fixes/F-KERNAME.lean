/-
Regression test for F-KERNAME.

`toKername` sends `.num p k` and `.str p k.repr` to the same λbox key — the finding's own
witness, `toKername (.num .anonymous 5) = toKername (.str .anonymous "5")`, holds by `rfl` — and
`cleanIdent`'s escape has fixed points besides. Two distinct Lean names can therefore mint one
key; before this fix the second registration silently overwrote the first entry of
`ErasureState.constants`/`gdecls`, so the emitted program kept only whichever declaration was
registered last, under no error.

The test exercises `checkKernameFresh` at its `addAxiom` site directly, with the finding's own
`.num`/`.str` witness pair, and separately erases an ordinary program with no such collision,
which must still succeed and stay unaffected by the guard.

With `FIXES_AST_DIR` set, the ordinary program's emitted `.ast` is written there, so
`scripts/fixes.sh` can run it through `peregrine validate`/`eval`.
-/
import LeanToLambdaBox.Erasure

open Lean Erasure

-- Every declaration of a test lives in its own namespace, so that the suite's files share the
-- root namespace without colliding.
namespace FKername

-- An ordinary mutual block, unaffected by the guard: none of its registered names collide.
mutual
  def isEven : Nat → Bool
    | 0 => true
    | n + 1 => isOdd n
  def isOdd : Nat → Bool
    | 0 => false
    | n + 1 => isEven n
end

def evenTest : Nat := if isEven 10 then 1 else 0

/-- Register the finding's own colliding pair through `addAxiom` directly and report whether the
second registration is refused. -/
def checkCollision : MetaM Unit := do
  try
    let ((), _) ← Erasure.run (do addAxiom (.num .anonymous 5); addAxiom (.str .anonymous "5")) {}
    IO.println "F-KERNAME collision: ok (not refused)"
  catch e =>
    -- Normalized to one line, for the same reason as F-UNSAFEREC's test.
    let msg := (← e.toMessageData.toString).replace "\n" " "
    let mentionsCollision := !((msg.splitOn "both mint the λbox key").length == 1)
    IO.println s!"F-KERNAME collision: error mentions-colliding-key={mentionsCollision} : {msg}"

/-- Erase an ordinary program with no colliding names end to end; the guard must not fire on
it. -/
def checkPlain : MetaM Unit := do
  let (p, _) ← erase (.const ``evenTest []) { extern := .preferLogical, nat := .peano, csimp := false }
  let .untyped gdecls _ := p
  IO.println s!"F-KERNAME plain: ok declarations={gdecls.length}"
  if let some dir ← IO.getEnv "FIXES_AST_DIR" then
    IO.FS.writeFile s!"{dir}/plain.ast" (Serialize.to_sexpr p).toString

#eval show MetaM Unit from do
  checkCollision
  checkPlain

end FKername
