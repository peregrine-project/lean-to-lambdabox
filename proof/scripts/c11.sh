#!/usr/bin/env bash
# Check C11: peregrine validates and evaluates the programs the eraser emits.
#
# Usage: PEREGRINE=<peregrine binary> proof/scripts/c11.sh [--out DIR]
#
# For each program of the table below, `peregrine validate` must report a valid AST, and the value
# that `peregrine eval` (with the table's options) prints must be the table's value, the value of
# the Lean program (eval's output without its "Compiling:" and "Compiled successfully:" lines,
# whitespace collapsed; `--anf=false` prints □ as `(FIX 0)`). The programs:
# - NV-1's, NV-2's, NV-Q's, NV-R's, NV-S's, NV-QP's, NV-L's and NV-A's programs as the entry
#   point of #erase emits them (proof/tools/NVEmit.lean; check.sh's step nv1-emit writes them to
#   proof/.check/nv1/NV1.ast, NV2.ast, NVQ.ast, NVR.ast, NVS.ast, NVQP.ast and NVQPFT.ast for
#   NV-QP's two terms, `orU` on the two representatives of one class, NVL.ast and NVA.ast, which
#   must exist);
# - every output of the regression tests (tests/regress) written under `nat := .peano`, read from
#   tests/regress/expected/, which scripts/regress.sh requires to equal what the tests write;
# - the regression tests' outputs for the programs of NV-1, NV-P and NV-K (tests/regress/
#   entry_route.lean), written under the default configuration (`nat := .machine`).
# A program of the table marked `default` must name no `Nat` declaration, so that its output is
# the same under `nat := .peano`. The script also fails if a regression test writes an output with
# `#erase … nat := .peano … to "<file>"` that the table does not list (an `#erase` that fails, under
# `#guard_msgs`, writes no output and has no file in tests/regress/expected/).
#
# Logs go to DIR (default proof/.check/c11). Exit status 0 if every program passes, 1 otherwise.
set -euo pipefail

PROOF=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
ROOT=$(cd "$PROOF/.." && pwd)
out=$PROOF/.check/c11
case ${1:-} in
  --out) out=$2 ;;
  '') ;;
  *) echo "usage: PEREGRINE=<binary> $0 [--out DIR]" >&2; exit 2 ;;
esac
[ -x "${PEREGRINE:-}" ] || { echo "error: PEREGRINE=<peregrine binary> is not set or not executable" >&2; exit 2; }
mkdir -p "$out"

# <file, relative to the repository root> <nat: peano or default> <eval options, - for none> <value>
table=$(cat <<'EOF'
proof/.check/nv1/NV1.ast                              default -           constr B.t
proof/.check/nv1/NV2.ast                              default -           constr B.t
proof/.check/nv1/NVQ.ast                              default -           constr B.t
proof/.check/nv1/NVR.ast                              default -           constr B.t
proof/.check/nv1/NVS.ast                              default -           constr N.s constr N.s constr N.z
proof/.check/nv1/NVQP.ast                             default -           constr B.t
proof/.check/nv1/NVQPFT.ast                           default -           constr B.t
proof/.check/nv1/NVL.ast                              peano   -           constr B.t
proof/.check/nv1/NVA.ast                              peano   -           constr Nat.succ constr Nat.succ constr Nat.succ constr Nat.succ constr Nat.succ constr Nat.zero
tests/regress/expected/entry_route/nv1.ast            default -           constr ER.B.t
tests/regress/expected/entry_route/nvp.ast            default -           constr ER.B.t
tests/regress/expected/entry_route/nvk.ast            default -           constr ER.B.t
tests/regress/expected/entry_route/useMN.ast          peano   -           constr Nat.zero
tests/regress/expected/alt_type_pure/alias.ast        peano   -           constr ATP.B.t
tests/regress/expected/alt_type_pure/fam.ast          peano   -           constr ATP.B.t
tests/regress/expected/alt_type_pure/sel.ast          peano   -           constr ATP.B.t
tests/regress/expected/arity_type/t.ast               peano   -           constr Nat.succ constr Nat.succ constr Nat.succ constr Nat.succ constr Nat.succ constr Nat.zero
tests/regress/expected/prop_elim_pure/or.ast          peano   --anf=false (FIX 0)
tests/regress/expected/prop_elim_pure/ex.ast          peano   --anf=false (FIX 0)
tests/regress/expected/thm_atom_pure/use.ast          peano   --anf=false (FIX 0)
tests/regress/expected/thm_atom_pure/useF.ast         peano   --anf=false (FIX 0)
tests/regress/expected/pure_inductive/nv3.ast         peano   -           constr PI.B.f
tests/regress/expected/traversal_total/all.ast        peano   -           constr Nat.succ constr Nat.succ constr Nat.succ constr Nat.succ constr Nat.succ constr Nat.succ constr Nat.succ constr Nat.succ constr Nat.succ constr Nat.succ constr Nat.zero
tests/regress/expected/traversal_locals/all.ast       peano   -           constr Nat.succ constr Nat.succ constr Nat.succ constr Nat.succ constr Nat.succ constr Nat.succ constr Nat.succ constr Nat.succ constr Nat.succ constr Nat.succ constr Nat.succ constr Nat.zero
tests/regress/expected/quotient/useLift.ast           peano   -           constr QT.B.t
tests/regress/expected/quotient/useLift.meta.ast      peano   -           constr QT.B.t
tests/regress/expected/quotient/usePart.ast           peano   -           constr QT.B.f
tests/regress/expected/quotient/useOver.ast           peano   -           constr QT.B.t
tests/regress/expected/quotient/useQuotient.ast       peano   -           constr QT.B.f
tests/regress/expected/quotient/indPf.ast             peano   --anf=false (FIX 0)
tests/regress/expected/quotient_pair/useTF.ast        peano   -           constr QP.B.t
tests/regress/expected/quotient_pair/useFT.ast        peano   -           constr QP.B.t
tests/regress/expected/quotient_pair/useFF.ast        peano   -           constr QP.B.f
tests/regress/expected/recursor/useNat.ast            peano   -           constr Nat.succ constr Nat.succ constr Nat.succ constr Nat.succ constr Nat.succ constr Nat.succ constr Nat.zero
tests/regress/expected/recursor/useList.ast           peano   -           constr Nat.succ constr Nat.succ constr Nat.succ constr Nat.zero
tests/regress/expected/recursor/useTree.ast           peano   -           constr Nat.succ constr Nat.succ constr Nat.zero
tests/regress/expected/recursor/useList.meta.ast      peano   -           constr Nat.succ constr Nat.succ constr Nat.succ constr Nat.zero
tests/regress/expected/recursor/useAcc.ast            peano   -           constr Nat.zero
tests/regress/expected/recursor/useVec.ast            peano   -           constr RT.B.t
tests/regress/expected/recursor/useMutual.ast         peano   -           constr RT.B.t
tests/regress/expected/recursor/useCast.ast           peano   -           constr RT.B.t
tests/regress/expected/recursor/useAnd.ast            peano   -           constr RT.B.t
tests/regress/expected/recursor/useOver.ast           peano   -           constr RT.B.f
tests/regress/expected/recursor/propRec.ast           peano   --anf=false (FIX 0)
tests/regress/expected/structural/useAdd.ast          peano   -           constr Nat.succ constr Nat.succ constr Nat.succ constr Nat.succ constr Nat.succ constr Nat.zero
tests/regress/expected/structural/useAddDefault.ast   peano   -           constr Nat.succ constr Nat.succ constr Nat.succ constr Nat.succ constr Nat.succ constr Nat.zero
tests/regress/expected/structural/useAddNoCsimp.ast   peano   -           constr Nat.succ constr Nat.succ constr Nat.succ constr Nat.succ constr Nat.succ constr Nat.zero
tests/regress/expected/structural/useLength.ast       peano   -           constr Nat.succ constr Nat.succ constr Nat.succ constr Nat.zero
tests/regress/expected/structural/useMap.ast          peano   -           constr ST.B.t
tests/regress/expected/structural/useEv.ast           peano   -           constr Bool.false
tests/regress/expected/structural/usePairs.ast        peano   -           constr Nat.succ constr Nat.succ constr Nat.zero
tests/regress/expected/structural/usePairs2.ast       peano   -           constr Nat.succ constr Nat.succ constr Nat.zero
tests/regress/expected/structural/useGet.ast          peano   -           constr ST.B.t
tests/regress/expected/mutual_block/useEven.ast       peano   -           constr MB.LB.f
tests/regress/expected/mutual_block/useSingle.ast     peano   -           constr MB.LB.t
tests/regress/expected/peano_literal/small.ast        peano   -           constr Nat.succ constr Nat.succ constr Nat.succ constr Nat.zero
EOF
)

failed=0
fail() { echo "FAIL $1: $2"; failed=1; }

# Every `#erase … nat := .peano … to "<file>"` of a regression test is in the table.
while IFS=: read -r src line; do
  f=$(sed -E 's/.* to "([^"]+)".*/\1/' <<<"$line")
  p=tests/regress/expected/$(basename "$src" .lean)/$f
  [ -f "$ROOT/$p" ] || continue
  grep -q "^$p " <<<"$table" || fail "$p" "written under nat := .peano by $src but not in the table"
done < <(grep -H -E '^#erase .*nat := \.peano.* to "' "$ROOT"/tests/regress/*.lean || true)

n=0
while read -r file nat opts value; do
  n=$((n + 1))
  path=$ROOT/$file log=$out/$(tr / _ <<<"$file")
  [ -f "$path" ] || { fail "$file" "missing"; continue; }
  if [ "$nat" = default ] && grep -q '"Nat"' "$path"; then
    fail "$file" "emitted under the default configuration but names a Nat declaration"
  fi
  if ! "$PEREGRINE" validate "$path" >"$log.validate" 2>&1 || ! grep -q '^AST is valid$' "$log.validate"; then
    fail "$file" "peregrine validate: $(tail -n 1 "$log.validate")"
    continue
  fi
  [ "$opts" != - ] || opts=
  # shellcheck disable=SC2086
  if ! "$PEREGRINE" eval "$path" $opts >"$log.eval" 2>&1; then
    fail "$file" "peregrine eval failed: $(tail -n 1 "$log.eval")"
    continue
  fi
  got=$(grep -v -E '^(Compiling|Compiled successfully):' "$log.eval" | tr -s ' \n' ' ' | sed 's/^ //; s/ $//')
  if [ "$got" != "$value" ]; then
    fail "$file" "eval printed '$got', expected '$value'"
  else
    echo "ok   $file: $value"
  fi
done <<<"$table"

[ $failed = 0 ] || { echo "c11: failed"; exit 1; }
echo "c11: all $n programs valid, with their Lean values"
