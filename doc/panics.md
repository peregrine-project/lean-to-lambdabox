# The eraser's panic sites, and what excludes each

`LeanToLambdaBox/Erasure.lean` has sixteen panic sites: twelve `unreachable!` and four
`panic!`. Both compile to the same thing — a message on stderr and the `Inhabited` default
as the result — and `EraseM`'s default is `.box`, so a panic **does not stop the run**: it
can produce a wrong `.ast` and exit `0`. That is not hypothetical, it is the measured
`Quicksort` miscompile (`F-SPARSE`, `doc/rework/03-DEV-FIX.md`).

This table is how the development meets the obligation to account for them. There is no
`Panicked` predicate and no `¬ Panicked run` binder: the output-shape lemmas
(`LeanToLambdaBox/OutputShape.lean`) are panic-**tolerant** — they discharge the panic arms
rather than refute them — and each site below is excluded by a premise that is either proved
here or is a named conjunct of `Supported`, the decidable fragment predicate whose errors a
reader audits. A site excluded "by a call-site guard" is one whose `unreachable!` sits in a
destructuring `let` reached only under a matching syntactic head in the caller's own `match`.

| # | Site | Line | Kind | What excludes it |
|---|---|---|---|---|
| 1 | `addAxiom`, duplicate constant | `:185` | `panic!` | The registration invariant: a constant is added to `constants` once, and `RegInvShape'`'s coverage field is what states it |
| 2 | `register_inductive`, `getConstInfo ind_name` not `.inductInfo` | `:200` | `unreachable!` | `InductiveVal.all` lists inductives of the block — environment adequacy, `ErasureSpec.lookup_adequate` |
| 3 | `register_inductive`, `getConstInfo ctor_name` not `.ctorInfo` | `:206` | `unreachable!` | `InductiveVal.ctors` lists constructors — the same adequacy field |
| 4 | `register_inductive`, unexpected field count | `:213` | `panic!` | `Meta.forallBoundedTelescope ci.type (numParams + numFields)` returns that many binders because the constructor's type is well-typed with that arity; a kernel invariant, reached only under `remove_irrel_constr_args` (off by default, N4) |
| 5 | `lambdaMonocular` on a non-`.lam` | `:303` | `unreachable!` | Call-site guard: `visitLambda` dispatches on `.lam` |
| 6 | `letMonocular` on a non-`.letE` | `:312` | `unreachable!` | Call-site guard: `visitLet` dispatches on `.letE` |
| 7 | `forallMonocular` on a non-`.forallE` | `:322` | `unreachable!` | Call-site guard: the η loops peel a binder of a type they have just found to be a `∀` |
| 8 | `visitExpr`, the four inert heads | `:602` | `unreachable!` | Four heads, two of them closed **by theorem**: `Erases.sort_erasable` and `Erases.forallE_erasable` prove a `.sort` and a `.forallE` are `Erasable`, and `visitExpr` returns `.box` at `:591` before the match, so those heads never reach it. `.mvar` is excluded by `Supported.mvar`; `.bvar` by the locally-nameless invariant — every binder is instantiated with an `.fvar`, so the subject carries no loose index |
| 9 | `visitLiteral`, `Nat` literal over 63 bits | `:613` | `panic!` | `Supported.machineNat`: the fragment fixes `nat := .peano`, and this arm is `.machine`-only |
| 10 | `visitLiteral`, string literal | `:614` | `panic!` | `Supported.strLit` |
| 11 | `visitProj`, `getConstInfo s` not `.inductInfo` | `:635` | `unreachable!` | `Expr.proj S i e` names a structure: a kernel invariant of the well-typed subject, and `Erases.proj`'s `IndInfo` premise states it on the specification side |
| 12 | `visitConst` on a non-`.const` | `:661` | `unreachable!` | Call-site guard: `visitApp` reaches it with a `.const` head |
| 13 | `visitConstApp` on a non-`.const` head | `:674` | `unreachable!` | Call-site guard: `withApp`'s head is the one the caller matched |
| 14 | `visitConstructor`, `getConstInfo ctorname` not `.ctorInfo` | `:732` | `unreachable!` | The name comes from a `CasesInfo`/constructor dispatch — environment adequacy |
| 15 | `visitConstructor`, `getConstInfo info.induct` not `.inductInfo` | `:734` | `unreachable!` | `ConstructorVal.induct` names an inductive — environment adequacy |
| 16 | `visitCases`, `getConstInfo typeName` not `.inductInfo` | `:817` | `unreachable!` | `Supported.casesApp`'s **plain `CasesInfo`** conjunct. This is the one site reachable on a program the eraser otherwise accepts: `typeName` is recovered from the *name* (`casesInfo.declName.getPrefix`, `:770`), which is the enclosing function for a sparse `casesOn`. Reported as `SupportError.sparseCasesOn` and queued as **F-SPARSE** |

## Two sites outside the eraser

`LeanToLambdaBox/Basic.lean:39` panics on converting the anonymous `Name` to a kername, and
`LeanToLambdaBox/Printing.lean:84` has an `unreachable!` for a `.fvar` reaching the printer.
Neither is in the sixteen: the first is excluded by every caller passing a declaration name,
the second by `mkDef`'s `toBvar` closing the emitted term, which
`LeanToLambdaBox/OutputShape.lean`'s `noFix_toBvar`/`noBlock_toBvar` family already states.

## Why this is the whole obligation

Because no site aborts, none of them can be dismissed as "the run would have failed". Each
row above therefore carries a premise, and the premises are of exactly three kinds: a
theorem of this development (row 8's two heads), an invariant of the well-typed subject or
of the run (rows 1-7, 11-15), or a named conjunct of `Supported`, which is decidable and
whose error constructor a reader can see (rows 8-10, 16). The single row whose premise
excludes a program the eraser otherwise accepts is row 16, and it is a shipping bug, raised
and queued rather than patched.
