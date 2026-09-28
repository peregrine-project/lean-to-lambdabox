#!/usr/bin/env bash
# Run the shipping regression tests.
#
# Usage: scripts/regress.sh [--update] [TEST...]
#
# A test is a file tests/regress/<TEST>.lean that imports LeanToLambdaBox and writes its outputs with
# `#erase ... to "<file>" [mli "<file>"]` (relative paths). Each test is elaborated in a fresh
# directory, and the set of files it writes must equal tests/regress/expected/<TEST>/ byte for byte.
# A test also fails if Lean exits with an error, or if its output contains a PANIC message, unless
# the test contains the line `-- regress: allow-panic`.
#
# With PEREGRINE=<path to the peregrine binary> in the environment, the lines
#   -- peregrine: validate <file> [<option>...]
#   -- peregrine: eval <file> [<option>...]
# of a test are also run, in the test's output directory. Each must exit with status 0; if
# tests/regress/expected-peregrine/<TEST>/<file>.<verb> exists, the command's output (stdout and
# stderr) must equal it byte for byte. Without PEREGRINE these lines are skipped.
#
# --update rewrites the expected files of the selected tests (and, with PEREGRINE, their peregrine
# outputs) from the current checkout instead of comparing. Review the resulting git diff.
#
# Exit status: 0 if every selected test passes, 1 otherwise.
set -euo pipefail

source "$(dirname "${BASH_SOURCE[0]}")/common.sh"
export LC_ALL=C

update=0
names=()
for a in "$@"; do
  case $a in
    --update) update=1 ;;
    -h|--help) sed -n '2,23p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    -*) die "unknown option $a" ;;
    *) names+=("$(basename "$a" .lean)") ;;
  esac
done

TESTDIR=$ROOT/tests/regress
if [ ${#names[@]} -eq 0 ]; then
  while IFS= read -r f; do names+=("$(basename "$f" .lean)"); done \
    < <(find "$TESTDIR" -maxdepth 1 -name '*.lean' | sort)
fi
[ ${#names[@]} -gt 0 ] || die "no tests in $TESTDIR"
if [ -n "${PEREGRINE:-}" ]; then
  [ -x "$PEREGRINE" ] || die "PEREGRINE=$PEREGRINE is not executable"
  PEREGRINE=$(cd "$(dirname "$PEREGRINE")" && pwd)/$(basename "$PEREGRINE")
fi

tmp=$(mktemp -d)
echo "building the frontend"
build_frontend "$tmp/build.log"

failed=()
fail() {
  echo "FAIL $1: $2"
  [[ " ${failed[*]-} " == *" $1 "* ]] || failed+=("$1")
}

for t in "${names[@]}"; do
  src=$TESTDIR/$t.lean
  [ -f "$src" ] || { fail "$t" "no file $src"; continue; }
  out=$tmp/out/$t
  log=$tmp/log/$t.log
  mkdir -p "$out" "$(dirname "$log")"

  if ! run_lean "$out" "$src" "$log"; then
    fail "$t" "lean exited with an error (log: $log)"
    sed 's/^/    /' "$log" | tail -n 20
    continue
  fi
  if grep -q 'PANIC' "$log" && ! grep -q '^-- regress: allow-panic' "$src"; then
    fail "$t" "PANIC during elaboration (log: $log)"
    grep 'PANIC' "$log" | sed 's/^/    /' | head -n 5
  fi

  exp=$TESTDIR/expected/$t
  if [ $update -eq 1 ]; then
    rm -rf "$exp"
    mkdir -p "$exp"
    cp -R "$out"/. "$exp"/
    echo "updated expected/$t"
  else
    if [ ! -d "$exp" ]; then
      fail "$t" "no expected outputs (run scripts/regress.sh --update $t)"
    else
      (cd "$out" && find . -type f | sort) >"$tmp/got"
      (cd "$exp" && find . -type f | sort) >"$tmp/want"
      while IFS= read -r f; do fail "$t" "missing output ${f#./}"; done < <(comm -13 "$tmp/got" "$tmp/want")
      while IFS= read -r f; do fail "$t" "unexpected output ${f#./}"; done < <(comm -23 "$tmp/got" "$tmp/want")
      while IFS= read -r f; do
        if ! cmp -s "$out/$f" "$exp/$f"; then
          fail "$t" "output ${f#./} differs from expected"
          diff -u --label "expected/$t/${f#./}" --label "got/${f#./}" \
            <(tokenize "$exp/$f") <(tokenize "$out/$f") | head -n 40 | sed 's/^/    /' || true
        fi
      done < <(comm -12 "$tmp/got" "$tmp/want")
    fi
  fi

  # peregrine checks declared by the test
  if [ -n "${PEREGRINE:-}" ]; then
    pexp=$TESTDIR/expected-peregrine/$t
    [ $update -eq 0 ] || rm -rf "$pexp"
    while IFS= read -r line; do
      read -r -a words <<<"${line#-- peregrine:}"
      verb=${words[0]:-}
      file=${words[1]:-}
      case $verb in validate|eval) ;; *) fail "$t" "bad marker: $line"; continue ;; esac
      [ -n "$file" ] || { fail "$t" "bad marker: $line"; continue; }
      res=$tmp/peregrine/$t/$file.$verb
      mkdir -p "$(dirname "$res")"
      if ! (cd "$out" && "$PEREGRINE" "$verb" "$file" "${words[@]:2}") >"$res" 2>&1; then
        fail "$t" "peregrine $verb $file failed"
        sed 's/^/    /' "$res" | head -n 10
        continue
      fi
      if [ $update -eq 1 ]; then
        mkdir -p "$pexp"
        cp "$res" "$pexp/$file.$verb"
      elif [ -f "$pexp/$file.$verb" ] && ! cmp -s "$res" "$pexp/$file.$verb"; then
        fail "$t" "peregrine $verb $file output differs from expected"
        diff -u --label "expected-peregrine/$t/$file.$verb" --label "got" "$pexp/$file.$verb" "$res" \
          | head -n 40 | sed 's/^/    /' || true
      fi
    done < <(grep '^-- peregrine:' "$src" || true)
  fi

  [[ " ${failed[*]-} " == *" $t "* ]] || echo "ok   $t"
done

total=${#names[@]}
nfail=${#failed[@]}
if [ "$nfail" -gt 0 ]; then
  echo "$nfail of $total tests failed: ${failed[*]}"
  echo "outputs and logs kept in $tmp"
  exit 1
fi
rm -rf "$tmp"
if [ -z "${PEREGRINE:-}" ]; then
  echo "all $total tests passed (peregrine checks skipped: PEREGRINE is not set)"
else
  echo "all $total tests passed"
fi
