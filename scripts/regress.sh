#!/usr/bin/env bash
# Run the regression tests.
#
# Usage: scripts/regress.sh [--update] [TEST...]
#
# A test is a file tests/regress/<TEST>.lean that writes its outputs to relative paths, normally
# with `#erase ... to "<file>" [mli "<file>"]`. The script builds the package, elaborates each test
# in a fresh directory, and requires the files it writes to equal tests/regress/expected/<TEST>/
# byte for byte. A test also fails if Lean reports an error or prints a PANIC message.
#
# With PEREGRINE=<path to the peregrine binary> in the environment, the lines
#   -- peregrine: validate <file> [<option>...]
#   -- peregrine: eval <file> [<option>...]
# of a test are run in its output directory. Each must succeed and, if
# tests/regress/expected-peregrine/<TEST>/<file>.<verb> exists, print exactly that.
#
# --update rewrites the expected files of the selected tests (and, with PEREGRINE, their peregrine
# outputs) instead of comparing; review the resulting git diff.
set -euo pipefail
export LC_ALL=C

ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
TESTDIR=$ROOT/tests/regress
die() { echo "error: $*" >&2; exit 1; }

update=0
names=()
for a in "$@"; do
  case $a in
    --update) update=1 ;;
    -*) die "unknown option $a" ;;
    *) names+=("$(basename "$a" .lean)") ;;
  esac
done
if [ ${#names[@]} -eq 0 ]; then
  for f in "$TESTDIR"/*.lean; do names+=("$(basename "$f" .lean)"); done
fi
if [ -n "${PEREGRINE:-}" ]; then
  [ -x "$PEREGRINE" ] || die "PEREGRINE=$PEREGRINE is not executable"
  PEREGRINE=$(cd "$(dirname "$PEREGRINE")" && pwd)/$(basename "$PEREGRINE")
fi

tmp=$(mktemp -d)
(cd "$ROOT" && lake build) >"$tmp/build.log" 2>&1 || { tail -n 40 "$tmp/build.log"; die "lake build failed"; }

# One line per S-expression constructor, for readable diffs.
tokenize() { sed 's/(\([A-Za-z]\)/\n(\1/g' "$1"; echo; }

failed=()
fail() {
  echo "FAIL $1: $2"
  [[ " ${failed[*]-} " == *" $1 "* ]] || failed+=("$1")
}

for t in "${names[@]}"; do
  src=$TESTDIR/$t.lean out=$tmp/out/$t log=$tmp/$t.log exp=$TESTDIR/expected/$t
  [ -f "$src" ] || { fail "$t" "no file $src"; continue; }
  mkdir -p "$out"
  # The test file lies outside the working directory, so Lean names the main module `_stdin` and
  # hygienic names in the output do not depend on where the test runs.
  if ! (cd "$ROOT" && lake env sh -c 'cd "$1" && exec lean "$2"' sh "$out" "$src") >"$log" 2>&1; then
    fail "$t" "lean exited with an error"
    tail -n 20 "$log" | sed 's/^/    /'
    continue
  fi
  if grep -q PANIC "$log"; then
    fail "$t" "PANIC during elaboration"
    grep PANIC "$log" | head -n 5 | sed 's/^/    /'
  fi

  if [ $update -eq 1 ]; then
    rm -rf "$exp" && mkdir -p "$exp" && cp -R "$out"/. "$exp"/
  else
    if ! diff -rq "$exp" "$out" >"$tmp/diff" 2>&1; then
      fail "$t" "outputs differ from expected"
      sed 's/^/    /' "$tmp/diff"
      for f in "$exp"/*; do
        g=$out/$(basename "$f")
        [ -f "$g" ] && ! cmp -s "$f" "$g" || continue
        case $f in
          *.ast) diff -u <(tokenize "$f") <(tokenize "$g") ;;
          *) diff -u "$f" "$g" ;;
        esac | head -n 40 | sed 's/^/    /' || true
      done
    fi
  fi

  if [ -n "${PEREGRINE:-}" ]; then
    pexp=$TESTDIR/expected-peregrine/$t
    [ $update -eq 0 ] || rm -rf "$pexp"
    while read -r _ _ verb file opts; do
      res=$tmp/$t.$file.$verb
      # shellcheck disable=SC2086
      if ! (cd "$out" && "$PEREGRINE" "$verb" "$file" $opts) >"$res" 2>&1; then
        fail "$t" "peregrine $verb $file failed"
        head -n 10 "$res" | sed 's/^/    /'
      elif [ $update -eq 1 ]; then
        mkdir -p "$pexp" && cp "$res" "$pexp/$file.$verb"
      elif [ -f "$pexp/$file.$verb" ] && ! cmp -s "$res" "$pexp/$file.$verb"; then
        fail "$t" "peregrine $verb $file printed something else than expected"
        diff -u "$pexp/$file.$verb" "$res" | head -n 40 | sed 's/^/    /' || true
      fi
    done < <(grep '^-- peregrine: ' "$src" || true)
  fi

  [[ " ${failed[*]-} " == *" $t "* ]] || echo "ok   $t"
done

if [ ${#failed[@]} -gt 0 ]; then
  echo "${#failed[@]} of ${#names[@]} tests failed: ${failed[*]} (outputs kept in $tmp)"
  exit 1
fi
rm -rf "$tmp"
echo "all ${#names[@]} tests passed${PEREGRINE:+ (with peregrine checks)}"
