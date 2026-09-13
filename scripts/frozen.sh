#!/usr/bin/env bash
# The five benchmark programs are frozen sources shared with the sibling `benchmarks`
# repository. This script pins them three ways:
#   * VerifyBench/Src/<P>.lean is byte-identical to test/frozen/<P>.lean.expected;
#   * VerifyBench/Src/<P>.lean is a library module — no `#erase`, no erasure import —
#     and VerifyBench/<P>.lean is only that import plus the `#erase` line;
#   * VerifyBench/Src/<P>.lean's definitions match ../benchmarks/frontend_bench/lean/<P>.lean
#     (skipped, with a notice, when the sibling checkout is absent, as it is in CI).
# Usage: scripts/frozen.sh
set -uo pipefail
root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$root" || exit 2

programs="Arith Sieve Quicksort BinaryTrees Fannkuch"
sibling="../benchmarks/frontend_bench/lean"
fails=0

# The definitions of a benchmark root: everything but the erasure import, the `#erase`
# line and the comment above it, with leading and trailing blank lines trimmed.
defs() {
  sed -e '/^import LeanToLambdaBox$/d' -e '/^-- Extract to LambdaBox AST$/d' -e '/^#erase /d' "$1" \
    | awk 'BEGIN{blank=0}
           {if ($0 ~ /^[ \t]*$/) {blank++} else {for(i=0;i<blank;i++) print ""; blank=0; print}}'
}

fail() { echo "  FAIL: $1"; fails=$((fails + 1)); }

for p in $programs; do
  src="VerifyBench/Src/$p.lean"
  rootmod="VerifyBench/$p.lean"
  frozen="test/frozen/$p.lean.expected"
  echo "== $p"

  for f in "$src" "$rootmod" "$frozen"; do
    [ -f "$f" ] || { fail "missing $f"; continue 2; }
  done

  if ! diff -u "$frozen" "$src"; then
    fail "$src differs from $frozen"
  fi

  if grep -qE '^import LeanToLambdaBox$|#erase ' "$src"; then
    fail "$src is a library module: it may not import the erasure library or run #erase"
  fi

  if ! grep -qxF "import VerifyBench.Src.$p" "$rootmod"; then
    fail "$rootmod does not import VerifyBench.Src.$p"
  fi
  if grep -qE '^(def|abbrev|inductive|structure|theorem|partial def|@\[)' "$rootmod"; then
    fail "$rootmod declares something: the definitions belong in $src"
  fi
  if ! grep -qE "^#erase .* to \"VerifyBench/ast/$p\.ast\"$" "$rootmod"; then
    fail "$rootmod has no #erase line writing VerifyBench/ast/$p.ast"
  fi
  if ! grep -qE '^#erase .*csimp := false' "$rootmod"; then
    fail "$rootmod's #erase line does not turn csimp off"
  fi

  if [ -f "$sibling/$p.lean" ]; then
    if ! diff -u <(defs "$sibling/$p.lean") <(tail -n +2 "$src"); then
      fail "$src's definitions differ from $sibling/$p.lean's"
    fi
  else
    echo "  (sibling $sibling/$p.lean absent — cross-repo check skipped)"
  fi
done

echo
if [ "$fails" -gt 0 ]; then
  echo "frozen: FAIL ($fails checks)"
  exit 1
fi
echo "frozen: OK ($(echo $programs | wc -w) programs)"
exit 0
