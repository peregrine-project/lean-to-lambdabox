#!/usr/bin/env bash
# The regression suite of the shipping fixes on `dev/fix`: one test per finding under
# `test/fixes/`, each importing `LeanToLambdaBox.Erasure` alone, so the suite runs against
# the shipping closure and not against the verification.
#
# For every `test/fixes/<ID>.lean`:
#   * elaborate it with `lake env lean`, with `FIXES_AST_DIR` pointing at a scratch
#     directory the test may write emitted programs into;
#   * compare the lines the test marks with its own id, plus any `PANIC` line and the exit
#     code, against `test/fixes/<ID>.expected`. Only marked lines are compared, so that one
#     fix's `logInfo` does not churn every other fix's expected file; a `PANIC` line is
#     always compared, since a panicking erasure is what these fixes are about.
#   * if `test/fixes/<ID>.peregrine.expected` exists, run every emitted `.ast` through
#     `peregrine validate` and `peregrine eval` and compare that too. Without the binary
#     this check is reported as skipped rather than failed; point `PEREGRINE` at it to run
#     it (default: `peregrine` on `PATH`, else the sibling `peregrine-tool` build).
#
# Usage: scripts/fixes.sh [ID…]   (no argument: every test)
# Exit code: 0 when every comparison matched.
set -uo pipefail
root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$root" || exit 2

peregrine=${PEREGRINE:-}
if [ -z "$peregrine" ]; then
  if command -v peregrine > /dev/null 2>&1; then
    peregrine=$(command -v peregrine)
  else
    peregrine="$root/../peregrine-tool/_build/default/bin/main.exe"
  fi
fi

tmp=$(mktemp -d) || exit 2
trap 'rm -rf "$tmp"' EXIT

if [ $# -gt 0 ]; then
  tests=()
  for id in "$@"; do tests+=("test/fixes/$id.lean"); done
else
  tests=()
  while IFS= read -r f; do tests+=("$f"); done < <(find test/fixes -maxdepth 1 -name '*.lean' | sort)
fi

if [ ${#tests[@]} -eq 0 ]; then
  echo "scripts/fixes.sh: no tests found under test/fixes/" >&2
  exit 2
fi

status=0
for t in "${tests[@]}"; do
  id=$(basename "$t" .lean)
  if [ ! -f "$t" ]; then
    echo "scripts/fixes.sh: no such test '$t'" >&2
    status=2
    continue
  fi
  mkdir -p "$tmp/$id"

  FIXES_AST_DIR="$tmp/$id" lake env lean "$t" > "$tmp/$id.raw" 2>&1
  rc=$?
  { grep -aE "^$id|PANIC" "$tmp/$id.raw"; echo "lean-exit=$rc"; } > "$tmp/$id.actual"
  if ! diff -u "test/fixes/$id.expected" "$tmp/$id.actual"; then
    echo "scripts/fixes.sh: $id: erasure output differs"
    status=1
  fi

  if [ -f "test/fixes/$id.peregrine.expected" ]; then
    if [ -x "$peregrine" ]; then
      for ast in "$tmp/$id"/*.ast; do
        [ -e "$ast" ] || continue
        echo "== $(basename "$ast") validate"
        "$peregrine" validate "$ast" 2>&1
        echo "== $(basename "$ast") eval"
        "$peregrine" eval "$ast" 2>&1
      done > "$tmp/$id.pactual"
      if ! diff -u "test/fixes/$id.peregrine.expected" "$tmp/$id.pactual"; then
        echo "scripts/fixes.sh: $id: peregrine output differs"
        status=1
      fi
    else
      echo "scripts/fixes.sh: $id: no peregrine binary at '$peregrine'; evaluation check skipped"
    fi
  fi
done

exit $status
