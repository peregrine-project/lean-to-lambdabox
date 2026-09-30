#!/usr/bin/env bash
# C11 of proof/scripts/check.sh: peregrine on the pure-path outputs of the in-fragment corpus.
#
# Usage: PEREGRINE=<peregrine binary> proof/scripts/c11.sh [--no-exclusions] [--out DIR]
#
# 1. Runs the shipping harness `scripts/pure-harness.sh --keep DIR/harness`. It elaborates every
#    tests/corpus/<Stem>.lean; for every `#erase ... to "<f>"` it keeps the file <f> that `#erase`
#    wrote and the pure path's output <f>.pure, and it checks its summary against
#    tests/harness/expected/pure-harness.txt. A differing summary fails C11, since the set of
#    in-fragment programs would then not be the committed one.
# 2. The in-fragment programs are the summary lines "<Stem>/<f>: pure ok; ...; #erase = pure...":
#    `collectDeps` puts the program in the fragment and `#erase` wrote the pure path's output. For
#    each, <f> must equal <f>.pure byte for byte, and `peregrine validate <f>` and
#    `peregrine eval <f> --anf=false` must exit with status 0, except these exclusions (DESIGN
#    Q13, PLAN section 3 S-21), each for a reason the theorem does not cover:
#      N_quoteNs.*    validate, eval  the printer does not escape `"` in a module-path component
#                                     (SHIPPING-CHANGES R-2), so peregrine cannot parse the file
#      sixOnAxioms.*  eval            the output declares axioms, and peregrine's evaluator rejects
#                                     every program with an axiom
#      ugOne.*        validate, eval  a recursive constant whose value is not a λ: peregrine's
#                                     well-formedness check rejects its tFix body (R-11; DV-8)
#    An excluded check that passes is reported as stale, without failing. --no-exclusions runs the
#    excluded checks as ordinary ones.
#
# Output: one line per check ("ok", "FAIL", "excluded", "EXCLUDED-BUT-PASSES") and a total line.
# DIR (default: a temporary directory, removed when C11 passes) must not exist or be empty; it keeps
# the harness outputs (DIR/harness) and the output of every peregrine run (DIR/peregrine).
#
# Exit status: 0 if the harness passes and every check that is not excluded passes, 1 otherwise,
# 2 on a usage error.
set -uo pipefail

ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
export LC_ALL=C

excl=1
out=
while [ $# -gt 0 ]; do
  case $1 in
    --no-exclusions) excl=0 ;;
    --out) shift; [ $# -gt 0 ] || { echo "error: --out needs a directory" >&2; exit 2; }; out=$1 ;;
    -h|--help) sed -n '2,30p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "error: unknown argument $1" >&2; exit 2 ;;
  esac
  shift
done
[ -n "${PEREGRINE:-}" ] && [ -x "$PEREGRINE" ] \
  || { echo "error: PEREGRINE is not set to an executable" >&2; exit 2; }
PEREGRINE=$(cd "$(dirname "$PEREGRINE")" && pwd)/$(basename "$PEREGRINE")

if [ -n "$out" ]; then
  mkdir -p "$out"
  OUT=$(cd "$out" && pwd)
  [ -z "$(ls -A "$OUT")" ] || { echo "error: $OUT is not empty" >&2; exit 2; }
  keep=1
else
  OUT=$(mktemp -d)
  keep=0
fi
mkdir -p "$OUT/peregrine" "$OUT/cwd"

# excluded VERB FILE: status 0 if the check VERB on FILE is excluded.
excluded() {
  [ $excl -eq 1 ] || return 1
  case $(basename "$2") in
    N_quoteNs.*) return 0 ;;
    ugOne.*) return 0 ;;
    sixOnAxioms.*) [ "$1" = eval ] && return 0 ;;
  esac
  return 1
}

# ---- 1. the harness ---------------------------------------------------------------------------
echo "running scripts/pure-harness.sh (log: $OUT/harness.log)"
if ! "$ROOT/scripts/pure-harness.sh" --keep "$OUT/harness" >"$OUT/harness.log" 2>&1; then
  tail -n 40 "$OUT/harness.log"
  echo "C11: FAIL: scripts/pure-harness.sh failed (outputs kept in $OUT)"
  exit 1
fi
SUMMARY=$OUT/harness/pure-harness.txt
[ -f "$SUMMARY" ] || { echo "C11: FAIL: no $SUMMARY"; exit 1; }

# ---- 2. peregrine -----------------------------------------------------------------------------
n=0; pass=0; fail=0; skip=0; stale=0; nprog=0
while IFS= read -r rel; do
  nprog=$((nprog + 1))
  f=$OUT/harness/out/$rel
  if [ ! -f "$f" ] || [ ! -f "$f.pure" ]; then
    echo "FAIL $rel: missing output"; fail=$((fail + 1)); continue
  fi
  if ! cmp -s "$f" "$f.pure"; then
    echo "FAIL $rel: the #erase output differs from the pure path's"; fail=$((fail + 1)); continue
  fi
  for verb in validate eval; do
    n=$((n + 1))
    if [ $verb = eval ]; then args=(eval "$f" --anf=false); else args=(validate "$f"); fi
    log=$OUT/peregrine/${rel//\//__}.$verb
    if (cd "$OUT/cwd" && "$PEREGRINE" "${args[@]}") >"$log" 2>&1; then ok=1; else ok=0; fi
    if excluded $verb "$f"; then
      skip=$((skip + 1))
      if [ $ok -eq 1 ]; then
        echo "EXCLUDED-BUT-PASSES $verb $rel"; stale=$((stale + 1))
      else
        echo "excluded $verb $rel ($(grep -v -x -e 'Validating AST:' -e 'Compiling:' \
          -e 'Could not compile:' -e 'Error validating AST:' "$log" | head -n 1 | cut -c1-100))"
      fi
    elif [ $ok -eq 1 ]; then
      pass=$((pass + 1)); echo "ok $verb $rel"
    else
      fail=$((fail + 1)); echo "FAIL $verb $rel"; sed 's/^/    /' "$log" | head -n 5
    fi
  done
done < <(sed -n 's/^\([^ :]*\): pure ok; .*; #erase = pure.*$/\1/p' "$SUMMARY")

if [ $nprog -eq 0 ]; then
  echo "FAIL: the harness summary lists no in-fragment program"; fail=$((fail + 1))
fi
echo "C11: $nprog in-fragment outputs, $n checks: $pass passed, $fail failed, $skip excluded" \
  "($stale excluded checks pass)"
if [ $fail -ne 0 ]; then
  echo "outputs kept in $OUT"
  exit 1
fi
[ $keep -eq 1 ] || rm -rf "$OUT"
exit 0
