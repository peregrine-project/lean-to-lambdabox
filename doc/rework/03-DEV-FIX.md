# Branch `dev/fix` — edits to executed eraser code

Every change that alters what the shipping eraser *executes* is made on `dev/fix`
(branched from `dev/verify`), one commit per finding, and merged into `dev/verify`
afterwards. This file is the index. Verification-only files (proofs, specifications,
tools) never go through `dev/fix`.

| id | file | change | why | status |
|---|---|---|---|---|
| F-FUEL | `LeanToLambdaBox/Relevance.lean` | `isArityCheck.loop` throws on fuel exhaustion instead of returning `false` | The fuel is the depth of the *unreduced* type while the loop whnf-reduces, so a definitional alias for a ∀-telescope was judged relevant on the kernel branch (under-erasure); throwing routes such cases to `Erasure.isErasable`'s `.error` arm, i.e. to `isErasableMeta`, reproducing the pre-reroute verdict. `isArityCheck.WF` never mentions the fuel. | on `dev/fix`, pending merge |

Shipping findings that are **not** edited here but reported to the owner (raise, do
not fix) are listed in `01-DESIGN.md` §8.2 (F-PROP, F-ETA, F-SPARSE, F-EQREC, F-QUOT,
F-ACC, F-PRODUCT).
