# Branch `dev/fix` — edits to executed eraser code

Every change that alters what the shipping eraser *executes* is made on `dev/fix`
(branched from `dev/verify`), one commit per finding, and merged into `dev/verify`
afterwards. Verification-only files (proofs, specifications, tools) never go through
`dev/fix`. This file is the single index: applied edits in the two tables below (`F-FUEL` is
verification-authored code, not shipping code, landed to reproduce a pre-reroute verdict),
and shipping findings reported to the owner but not edited here, each specified with its
site, the command that measures it, and that command's real output. A finding fixed on this
branch keeps its section below, marked *Fixed*. No wave depends on any of the unfixed
findings landing, and no unit applies one.

## Applied edits

| id | file | change | why | status |
|---|---|---|---|---|
| F-FUEL | `LeanToLambdaBox/Relevance.lean` | `isArityCheck.loop` throws on fuel exhaustion instead of returning `false` | The fuel is the depth of the *unreduced* type while the loop whnf-reduces, so a definitional alias for a ∀-telescope was judged relevant on the kernel branch (under-erasure); throwing routes such cases to `Erasure.isErasable`'s `.error` arm, i.e. to `isErasableMeta`, reproducing the pre-reroute verdict. `isArityCheck.WF` never mentions the fuel. | merged into `dev/verify` (9363fb9) |

### Shipping edits

One row per finding fixed on `dev/fix`, in landing order. Each commit carries the edit, its
regression test under `test/fixes/`, and its row here; `scripts/fixes.sh` runs every test and
diffs the marked lines of its output, and the `peregrine validate`/`eval` output of the
programs it emits, against the committed expectations. The *commit* column names the commit
by its subject, which `git log --grep` resolves — a hash written into the commit that carries
it would be the hash the commit had before that row was added.

| id | commit | files and functions | behaviour before | behaviour after | emitted bytes | test | verification obligations |
|---|---|---|---|---|---|---|---|
| F-SPARSE | `fix(F-SPARSE)` | `LeanToLambdaBox/Erasure.lean`: `visitCases`; new `LBTerm.hasLooseBVarFrom`/`LBTerm.hasLooseBVar` | A sparse `casesOn` panicked at the `unreachable!`, erased the whole elimination to `.box`, exited 0 and wrote a program `peregrine validate` accepts and `peregrine eval` either mis-evaluates or gets stuck on ("`Case: <15> branch not found`") | The inductive is read from `casesInfo.indName` and the catch-all is expanded into one alternative per uncovered constructor, in constructor order; the shapes that remain uncompilable (side-condition elimination, machine-`Nat`/`Int` discriminee, alternatives that do not match the constructors, a catch-all with a free index) `throwError`. No `unreachable!` and no path to a wrong `.ast` with exit 0 | yes — `Quicksort` only (65474 → 65686 bytes); `Arith`, `Sieve`, `BinaryTrees`, `Fannkuch` and rungs G1–G6 byte-identical | `test/fixes/F-SPARSE.lean` | `visitCases`'s body changed, so the `VisitExprRefines` step bodies that mirror it must be re-proved (no mutual member added or removed: the `partial_fixpoint` arity is unchanged). The fragment is unaffected — `Supported.supportedHead` still refuses `isSparseCasesOn`/`isMatcherName` heads, and `CasesOnShape` (`SourceEval.lean:163`) and `BlockAdequate.casesOnDecl` (`ErasureSpec.lean:202`) may keep `c.getPrefix = I`, which holds of every head they admit. Covering the expanded shape would need `indName` there plus an `Erases`/`Lower` arm for a catch-all alternative and an `ErasesCorrect/Iota.lean` case |

## Reported, not fixed

The repository's standing rule is *raise implementation issues, do not silently patch
them*. Each section below is a defect in `LeanToLambdaBox/{Erasure,Basic}.lean` that the
verification found, specified with the site, the command that measures it, and that
command's output. No wave depends on any of them landing, and no unit applies one.

Ordered as the design orders them (`doc/rework/01-DESIGN.md` §8.2): **F-PROP** first, because
three other rows are downstream of it. The last three rows — **F-DEPTH**, **F-UNSAFEREC**,
**F-KERNAME** — are `doc/rework/06-REPAIRS-W4.md` §3's findings, in the order that document
raises them; each bounds one class-**C** field of `EraserAsks`.

Every command below runs from the repository root. The `.ast` files are the five csimp-off
duplicates under `VerifyBench/ast/`, regenerated with `lake build VerifyBench`.

### F-PROP — every emitted inductive is declared non-propositional

*Site.* `register_inductive`, `LeanToLambdaBox/Erasure.lean:192-241`; the field's default,
`LeanToLambdaBox/Basic.lean:164`.

*Defect.* `OneInductiveBody.propositional` is never set. The `false` default carries the
author's own hedge ("I think, since erasure should remove anything which ends up in Prop"),
so every emitted inductive — including `Prop` ones — is declared non-propositional.
`isPropositionalInductive` is then identically `false` downstream: an emitted `.case` on a
`□` discriminee is **stuck** at every flag point, and peregrine's verified
`remove_match_on_box` (`EOptimizePropDiscr.v:35,57`) skips it.

*Measure.*

    grep -o 'one_inductive_body "[^"]*" [a-z]*' VerifyBench/ast/*.ast | sed 's/.* //' \
      | sort | uniq -c

    71 false

*Proposed edit.* Set the field from the source sort (`Meta.isProp` on the type former).

*Consequence until it lands.* `And`/`Iff`/`Acc` eliminations into data ship as stuck terms,
which is why the fragment excludes them (`Supported.propElimIntoData`).

### F-ETA — every emitted recursive body is a bare unapplied `.fix`

*Site.* `visitMutual`, `LeanToLambdaBox/Erasure.lean:859-919`; the eraser's own TODO sits at
`:911`.

*Defect.* The emitted body of a recursive declaration is `.fix defs i` with no λ-headedness
check — `nonrecursive := single_decl && !name_occurs …` (`:885`) is the only guard — so
MetaRocq's `EEtaExpandedFix.expanded_eprogram` is **false on all five programs**. That
predicate is not paperwork: `guarded_to_unguarded_fix` (`ETransform.v:666-682`) is the
identity on terms and its whole evaluation-preservation obligation is discharged from it, so
with the predicate false no verified semantics-preservation argument covers this frontend's
output past the target-side `WcbvEval`. peregrine's own discharge is `Admitted`
(`Transforms.v:375`) and `peregrine validate` checks no η, so nothing downstream detects it.

*Measure.*

    grep -o '(constant_body (Some (tFix' VerifyBench/ast/*.ast | sed 's/:.*//' | sort | uniq -c
    grep -o '(tFix' VerifyBench/ast/*.ast | wc -l

     4 VerifyBench/ast/Arith.ast
    10 VerifyBench/ast/BinaryTrees.ast
    15 VerifyBench/ast/Fannkuch.ast
    11 VerifyBench/ast/Quicksort.ast
    10 VerifyBench/ast/Sieve.ast
    50

50 `tFix` nodes, 50 of them the whole body of a constant: no emitted fixpoint is applied.

*Proposed edit.* Wrap the emitted body in `rarg+1` lambdas applied to their own binders —
the TODO at `:911`. Adequate here: all 50 `FixDef`s have `principalArgIdx = 0` and every
self-call is applied. Rocq avoids the problem by η-expanding before erasure
(`Template/EtaExpand`).

*Status in the verification.* The capstone's conclusion states `LBWfPeregrine`, which
deliberately does **not** claim fixpoint η; the stronger `PeregrinePre` is defined and *not*
concluded, and the difference is exactly this row.

### F-ETA2 — the η path re-erases supplied arguments, and constructors do not need it

*Site.* `visitCtorEtaGo`, `LeanToLambdaBox/Erasure.lean:722-728`; `visitCasesEtaGo`,
`:705-712`.

*Defect, two halves.*

First, both loops recurse with `args.push (.fvar fvarid)` **inside** `forallMonocular`'s
scope and only then call `visitConstructor`/`visitCases`. The arguments the call site already
supplied are therefore erased again under every new binder, and `mkLambda` abstracts them
back out: the eraser pays one erasure of the whole supplied prefix per missing argument, and
the emitted term is `λ x₁ … xₙ. C a₁ … aₖ x₁ … xₙ` where `C a₁ … aₖ` would do.

Second, and independently: **applied-form λ□ needs no constructor η at all.** At
`with_constructor_as_block = false`, which is what `eraseFlags` sets
(`LeanToLambdaBox/Semantics/Flags.lean:44`), a partially applied constructor spine is already
a value — `Value.construct_app_val` (`LeanToLambdaBox/Semantics/Values.lean:104`) builds
`mkApps (.construct iid c []) args` as a value for every `args.length < ar`, and
`WcbvEval.construct_app` (`LeanToLambdaBox/Semantics/Eval.lean:130-136`) is the rule that
reaches it. So `visitCtorEta`'s whole saturation loop buys nothing that the target semantics
does not already give, and it is the only reason an under-applied constructor occurrence is
not a plain spine.

*Measure.* Every emitted `tConstruct` node carries an empty argument list, so applied form is
what the eraser already emits everywhere:

    python3 - <<'EOF'
    import glob, re
    def nodes(s):
        out = []
        for m in re.finditer(r'\(tConstruct\b', s):
            i = m.start(); d = 0; j = i
            while True:
                if s[j] == '(': d += 1
                elif s[j] == ')':
                    d -= 1
                    if d == 0: break
                j += 1
            out.append(s[i:j+1])
        return out
    tot = empty = 0
    for f in sorted(glob.glob('VerifyBench/ast/*.ast')):
        ns = nodes(open(f).read())
        e = sum(1 for n in ns if n.rstrip()[:-1].rstrip().endswith('()'))
        print(f, len(ns), e); tot += len(ns); empty += e
    print('total', tot, 'empty-arg', empty)
    EOF

    VerifyBench/ast/Arith.ast 42 42
    VerifyBench/ast/BinaryTrees.ast 84 84
    VerifyBench/ast/Fannkuch.ast 101 101
    VerifyBench/ast/Quicksort.ast 697 697
    VerifyBench/ast/Sieve.ast 58 58
    total 982 empty-arg 982

*Proposed edit.* Delete `visitCtorEta`/`visitCtorEtaGo` and dispatch `visitConstructor`
directly at every arity. For `visitCasesEta` the loop is not removable — a `.case` node needs
its discriminant — but the recursion should erase the supplied prefix once, outside
`forallMonocular`, and reuse the result.

*Status in the verification.* `Lower` has no `ctorEta` and no `elimEta` arm: both are
compositional, so an η-expanded head still composes under `app` into
`mkApps (mkLambdas ns body) args'`, a β-redex target with no bound on nesting that every
spine-inverting arm of the simulation would have to collapse. What they covered is the
coverage restriction **N19** — no under-applied constructor or eliminator occurrence — which
`supportedB` decides per program. For constructors N19 costs nothing once this row is
repaired; for eliminators it is a real restriction, and `doc/coverage.md` carries the
per-program verdict.

### F-SPARSE — a sparse `casesOn` panics and writes a wrong program

*Site.* `visitCases`, `LeanToLambdaBox/Erasure.lean:770` (the name-based recovery) and
`:817` (the panic).

*Defect.* The inductive is recovered as `casesInfo.declName.getPrefix`. Since Lean v4.26,
`getCasesInfo?` also recognises sparse `casesOn` auxiliaries (`…_sparseCasesOn_1`), whose
prefix is the *enclosing function*, not the inductive. `getConstInfo` then fails the
`.inductInfo` pattern and the `unreachable!` fires — which, at `EraseM`, returns `.box` and
lets the run continue, exit `0`, and write an `.ast` that `peregrine validate` accepts.

*Measure.*

    lake env lean VerifyBench/Quicksort.lean > qs.log 2>&1 ; echo "exit $?" ; grep -m1 PANIC qs.log

    exit 0
    PANIC at Erasure.visitCases LeanToLambdaBox.Erasure:817:55: unreachable code has been reached

The run writes `VerifyBench/ast/Quicksort.ast` regardless. `Quicksort` is the one of the five
programs that hits it, through `quicksort_fuel`.

*Proposed edit.* Recover the inductive from `CasesInfo` rather than from the name, and
handle `CasesAltInfo.default`.

*Status in the verification.* Visible as `SupportError.sparseCasesOn`, the value
`supportedB` returns on this program, and as a named row in `doc/coverage.md`.

*Fixed* on `dev/fix` by `fix(F-SPARSE)` — see the shipping-edits table. The inductive comes
from `casesInfo.indName` and the catch-all is expanded into one alternative per uncovered
constructor; every shape that cannot be compiled soundly now throws. The fragment is
unchanged: `supportedHead` still refuses a sparse head, so `SupportError.sparseCasesOn` and
the `doc/coverage.md` row stand.

### F-ACC — a `Prop`-valued inductive with an index-determined field

*Site.* `visitCases`, `LeanToLambdaBox/Erasure.lean:768-835`, at an `Acc`-shaped inductive.

*Defect.* A consequence of F-PROP with a second stage. *Today* the emitted `.case` is stuck
at the environment (F-PROP). *If F-PROP alone is fixed*, `Acc`-shaped inductives then reduce
by `iota_sing`/`remove_match_on_box`, which box a field that is **data** — `Acc.intro`'s
`x : α`, measured as `largeElimClause ``Acc = some (2,[1])` — and compute a wrong program.

*Measure.*

    grep -c 'Acc\|WellFounded\|Quot' VerifyBench/ast/*.ast | sort

    VerifyBench/ast/Arith.ast:0
    VerifyBench/ast/BinaryTrees.ast:0
    VerifyBench/ast/Fannkuch.ast:0
    VerifyBench/ast/Quicksort.ast:0
    VerifyBench/ast/Sieve.ast:0

Latent: no benchmark reaches it.

*Proposed edit.* Any F-PROP fix must keep index-determined-field eliminations refused. The
refusal has to be **shape**-keyed, not name-keyed: `Acc.casesOn` does compile in Lean, so
refusing the name would not close the hole.

### F-QUOT and F-EQREC — body-less constants the consumer cannot realise

*Site.* `LeanToLambdaBox/Erasure.lean:873-876`, the `ci.value? = .none` arm of the
single-declaration branch.

*Defect.* A constant with no compiler value is emitted as a body-less axiom. Two families
reach it: `Quot` primitives (F-QUOT), and recursors reached as constants (F-EQREC) — `Eq.rec`
is emitted body-less in `Fannkuch`. The program is then stuck there unless peregrine's
`.attr`/`.ast.inlinings` channel supplies a realizer, which this frontend does not emit, and
`peregrine validate` still accepts the file.

*Measure.*

    grep -c '(constant_body None)' VerifyBench/ast/*.ast | sort

    VerifyBench/ast/Arith.ast:0
    VerifyBench/ast/BinaryTrees.ast:0
    VerifyBench/ast/Fannkuch.ast:1
    VerifyBench/ast/Quicksort.ast:0
    VerifyBench/ast/Sieve.ast:0

The one body-less declaration is `((MPdot (MPfile ()) "Eq") "rec")`, and `Fannkuch.ast`
applies it.

*Proposed edit.* Emit a realizer, or refuse. For `Eq.rec` the natural channel is the
remapping the backends already take (`.ast.inlinings`/`.attr`); someone must decide whether
the frontend should emit it.

*Status in the verification.* `Quot` in a computationally relevant position is outside the
fragment (`Supported.quotPrim`). `Eq.rec` is covered by an `AxiomRealizer` row — a class-**E**
assumption that the consumer supplies the realizer — and `Fannkuch`'s coverage row records
that its `hax` is false without one.

### F-PRODUCT — an unverified product feature added on the verification branch

*Site.* `auto_inline_typeclass_dispatch` and its helpers: the config flag at
`LeanToLambdaBox/Erasure.lean:85`, `LBTerm.stripLambdas`/`containsFix`/`isTrivialAlias` at
`:88-118`, and the dispatch at `:896-903`.

*Defect.* Not a miscompile: a product feature that rode in on the verification branch, so
"what the verification changed" is not a clean diff. It is off by default and the
verification never depends on it.

*Measure.*

    grep -n 'auto_inline_typeclass_dispatch' LeanToLambdaBox/Erasure.lean

    85:  auto_inline_typeclass_dispatch: Bool := false
    896:      if (← read).config.auto_inline_typeclass_dispatch && !leanInline && !t.containsFix then

*Proposed edit.* Re-home the feature through `dev/fix` (or `main`), so the verification diff
touches only verification files.

*Status in the verification.* The `.ast.inlinings` channel it drives is a class-**E** row in
`doc/trust.md`; nothing in the theorem stack mentions it.

### F-DEPTH — the relevance oracle's arity check has an 8-bit fuel

*Site.* `isArityCheck`, `LeanToLambdaBox/Relevance.lean:46`, whose fuel is
`ty.approxDepth.toNat + 1`; the loop it feeds is at `:32`.

*Defect.* `Lean.Expr.Data.approxDepth` is eight bits, so the fuel saturates at 256 however deep
the type is, and it is **1** at a definitional alias, whose `approxDepth` is 0. `isArityCheck`
then throws, `Erasure.isErasable` (`LeanToLambdaBox/Erasure.lean:177`) takes its `.error` arm,
and the verdict is the unverified `Erasure.isErasableMeta`'s — which will not unfold an
`@[irreducible]` alias either, so it answers `false`. The oracle therefore answers `false` at an
inductive **type former**, the one shape the erasure must not treat as data.

*Measure.*

    cat > /tmp/f-depth.lean <<'EOF'
    import LeanToLambdaBox.Relevance
    import LeanToLambdaBox.Erasure
    open Lean

    def tele : Nat → Expr
      | 0     => .sort .zero
      | n + 1 => .forallE `x (.sort .zero) (tele n) .default

    def DeepArity : Type 1 := Nat → Nat → Nat → Nat → Type
    inductive Bar : DeepArity
    attribute [irreducible] DeepArity

    #eval show CoreM Unit from do
      for k in [4, 100, 255, 300, 1000] do
        let d := (tele k).approxDepth
        IO.println s!"telescope of {k} binders: approxDepth = {d}, isArityCheck fuel = {d.toNat + 1}"
      let al := mkConst ``DeepArity
      IO.println s!"alias DeepArity:          approxDepth = {al.approxDepth}, isArityCheck fuel = {al.approxDepth.toNat + 1}"
      let env ← getEnv
      match Lean4Lean.TypeChecker.M.run env.toKernelEnv (safety := .safe) (lctx := {}) (lparams := [])
          (x := Lean4Lean.TypeChecker.RecM.run (LeanToLambdaBox.isErasable (mkConst ``Bar))) with
      | .ok b    => IO.println s!"kernel isErasable Bar   = ok {b}"
      | .error _ => IO.println s!"kernel isErasable Bar   = error (routes to isErasableMeta)"

    #eval show MetaM Unit from do
      IO.println s!"isErasableMeta Bar      = {← Erasure.isErasableMeta (mkConst ``Bar)}"
    EOF
    lake env lean /tmp/f-depth.lean

    telescope of 4 binders: approxDepth = 4, isArityCheck fuel = 5
    telescope of 100 binders: approxDepth = 100, isArityCheck fuel = 101
    telescope of 255 binders: approxDepth = 255, isArityCheck fuel = 256
    telescope of 300 binders: approxDepth = 255, isArityCheck fuel = 256
    telescope of 1000 binders: approxDepth = 255, isArityCheck fuel = 256
    alias DeepArity:          approxDepth = 0, isArityCheck fuel = 1
    kernel isErasable Bar   = error (routes to isErasableMeta)
    isErasableMeta Bar      = false

*Proposed edit.* Fuel the loop by the *reduced* telescope's own bound rather than by the
unreduced subject's `approxDepth` — count binders as `whnf` produces them, with a budget that
does not come from an eight-bit field. `LeanToLambdaBox/Relevance.lean` is verification-authored,
so this is in scope for a later wave under plan rule N5's scheduled exception; W4b does not take
it.

*Consequence until it lands.* `EraserAsks.kernel_ind_head_true` — "at an inductive head the pure
kernel run answers `true`" — is false in general, at a telescope of ≥ 256 binders or behind an
`@[irreducible]` alias. It is carried as a class-**C** field with this row as its bound, and
`EraserAsks.oracle_informative`, the type-former exclusion the bridge's constant step consumes,
is exactly as strong as it.

### F-UNSAFEREC — a `mutual unsafe def` block with an `_unsafe_rec` twin is miscompiled

*Site.* `visitMutual`, `LeanToLambdaBox/Erasure.lean:906` (`let fixvarnames := names.map
remove_unsafe_rec`) and `:916-918` (the registration loop); `remove_unsafe_rec` at `:520`.

*Defect.* `Erasure.remove_unsafe_rec` strips one literal `_unsafe_rec` component, so it is not
injective. A `mutual` block holding both `u` and `u._unsafe_rec` is legal Lean, and
`Lean.Compiler.LCNF.getDeclInfo?` reports both members in `ci.all`; the eraser maps that block to
`[u, u]`, builds `fixvarMap [u, u] ids` (whose second binding overwrites the first), names both
`FixDef`s `u`, and registers both declarations at the one kername `u`. The emitted program has
two constants under one key, two identically named fix variables, and both members' recursive
calls bound to whichever the map kept. No error is reported.

*Measure.*

    cat > /tmp/f-unsaferec.lean <<'EOF'
    import LeanToLambdaBox.Erasure
    open Lean LeanToLambdaBox

    mutual
      unsafe def u : Nat → Nat
        | 0 => 0
        | n + 1 => u._unsafe_rec n
      unsafe def u._unsafe_rec : Nat → Nat
        | 0 => 1
        | n + 1 => u n
    end

    def keyStr (k : Kername) : String := toString (repr k)

    #eval show CoreM Unit from do
      let some ci ← Lean.Compiler.LCNF.getDeclInfo? ``u | IO.println "getDeclInfo? u = none"
      let mapped := ci.all.map Erasure.remove_unsafe_rec
      IO.println s!"getDeclInfo? u : all = {ci.all}"
      IO.println s!"mapped by remove_unsafe_rec = {mapped}"
      IO.println s!"distinct keys = {(mapped.map (keyStr <| toKername ·)).eraseDups.length} of {mapped.length}"
      let (p, _) ← Erasure.erase (mkConst ``u) {}
      let keys := p.1.map (keyStr ·.1)
      IO.println s!"emitted declarations = {keys.length}, distinct keys = {keys.eraseDups.length}"
      for (kn, d) in p.1 do
        if kn.id == "u" then
          match d with
          | .constantDecl ⟨some (.fix defs i)⟩ =>
              IO.println s!"key u: fix at index {i}, defs named {defs.map (repr ·.name)}"
          | _ => IO.println "key u: not a bare fix"
    EOF
    lake env lean /tmp/f-unsaferec.lean

    Name Unit.unit is marked as inline.
    Name Nat.sub has a value but is tagged @[extern], emitting axiom.
    Name Nat.beq has a value but is tagged @[extern], emitting axiom.
    getDeclInfo? u : all = [u, u._unsafe_rec]
    mapped by remove_unsafe_rec = [u, u]
    distinct keys = 1 of 2
    emitted declarations = 10, distinct keys = 9
    key u: fix at index 1, defs named [BinderName.named "u", BinderName.named "u"]
    key u: fix at index 0, defs named [BinderName.named "u", BinderName.named "u"]

The first three lines are the eraser's own `logInfo` output on this program.

*Proposed edit.* One line after `LeanToLambdaBox/Erasure.lean:906`:

    unless (fixvarnames.map toKername).Nodup do
      throw <| .error .missing s!"mutual block {names} has colliding lambda-box keys"

Refusing is right rather than renaming: the two members are distinct declarations and the λ□
environment has no room for both under one key.

*Consequence until it lands.* `EraserAsks.block_keys_distinct` is a class-**C** field rather than
a fact the run recovers. With the guard the field becomes a consequence of the run's own
conclusion and the field goes.

### F-KERNAME — `toKername` is not injective

*Site.* `toKername`, `LeanToLambdaBox/Basic.lean:35`, through `cleanIdent` at `:24` and the
`.num` arm's `nb.repr`.

*Defect.* `toKername` sends `.num p k` and `.str p k.repr` to one kername, and `cleanIdent`'s
escape has fixed points, so two distinct Lean constants can carry one λ□ key. Registration is a
`gdecls.cons`, so the second such constant shadows the first in the emitted environment and the
program reads whichever the printer emits last. `toKername_not_injective`
(`LeanToLambdaBox/VisitExprRefines/Step/Env.lean:666`) is the witness pair.

*Measure.* The defect is latent rather than live: over the whole elaboration environment of this
repository, no two declared constants collide.

    cat > /tmp/f-kername.lean <<'EOF'
    import LeanToLambdaBox
    open Lean LeanToLambdaBox

    #eval show CoreM Unit from do
      let env ← getEnv
      let mut keys : Std.HashMap String Name := {}
      let mut n := 0
      let mut collisions : Array (Name × Name) := #[]
      for (nm, _) in env.constants.toList do
        if nm != .anonymous then
          n := n + 1
          let k := toString (repr (toKername nm))
          match keys[k]? with
          | some m => collisions := collisions.push (m, nm)
          | none   => keys := keys.insert k nm
      IO.println s!"constants = {n}, distinct keys = {keys.size}, collisions = {collisions.size}"

    example : toKername (.num .anonymous 5) = toKername (.str .anonymous "5") := rfl
    EOF
    lake env lean /tmp/f-kername.lean

    constants = 228987, distinct keys = 228987, collisions = 0

The `example` is the non-injectivity witness and it elaborates by `rfl`; the count is what says
no *declared* pair realises it here.

*Proposed edit.* Make the key injective — carry the `.num`/`.str` distinction and the escape
into the identifier — or refuse a collision at registration, which is the cheaper half and the
one that turns a silent shadowing into an error.

*Consequence until it lands.* The verification excludes colliding inputs rather than assuming
they cannot occur: kername separation over the tabled names is a decidable arm of the fragment
checker, reported as `SupportError.kernameCollision`, and `doc/coverage.md` carries the
restriction row. Nothing in the theorem stack assumes `toKername` injective.
