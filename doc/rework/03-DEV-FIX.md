# Branch `dev/fix` — edits to executed eraser code

Every change that alters what the shipping eraser *executes* is made on `dev/fix`
(branched from `dev/verify`), one commit per finding, and merged into `dev/verify`
afterwards. Verification-only files (proofs, specifications, tools) never go through
`dev/fix`. This file is the single index: applied edits in the first table (`F-FUEL` is
verification-authored code, not shipping code, landed to reproduce a pre-reroute verdict),
and shipping findings reported to the owner but not edited here, each specified with its
site, the command that measures it, and that command's real output. No wave depends on any
of the unfixed findings landing, and no unit applies one.

## Applied edits

| id | file | change | why | status |
|---|---|---|---|---|
| F-FUEL | `LeanToLambdaBox/Relevance.lean` | `isArityCheck.loop` throws on fuel exhaustion instead of returning `false` | The fuel is the depth of the *unreduced* type while the loop whnf-reduces, so a definitional alias for a ∀-telescope was judged relevant on the kernel branch (under-erasure); throwing routes such cases to `Erasure.isErasable`'s `.error` arm, i.e. to `isErasableMeta`, reproducing the pre-reroute verdict. `isArityCheck.WF` never mentions the fuel. | merged into `dev/verify` (9363fb9) |

## Reported, not fixed

The repository's standing rule is *raise implementation issues, do not silently patch
them*. Each section below is a defect in `LeanToLambdaBox/{Erasure,Basic}.lean` that the
verification found, specified with the site, the command that measures it, and that
command's output. No wave depends on any of them landing, and no unit applies one.

Ordered as the design orders them (`doc/rework/01-DESIGN.md` §8.2): **F-PROP** first, because
three other rows are downstream of it.

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
