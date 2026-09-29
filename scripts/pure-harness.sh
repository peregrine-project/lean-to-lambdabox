#!/usr/bin/env bash
# Run the pure path of the eraser next to its Meta path on the corpus examples.
#
# Usage: scripts/pure-harness.sh [--update] [--keep DIR]
#
# Builds the package and the harness module tests/harness/PureHarness.lean, then elaborates, for
# every file tests/corpus/<Stem>.lean, a copy that also imports the harness, with the root package on
# the load path and its output directory as working directory (as scripts/corpus.sh does). For every
# `#erase ... to "<f>"` the harness writes <f>.harness; if `collectDeps` puts the program in the
# fragment, it also writes the outputs of `erasePure` to <f>.pure and of the Meta path
# (`Erasure.erase`) to <f>.meta, each with its .inlinings, and counts the oracle calls of the pure
# run at which the Meta oracle answers differently (tests/harness/PureHarness.lean).
#
# The summary has one line per `#erase`, in the order of the files and of the output names:
#   <Stem>/<f>: out of the fragment: <what>
#   <Stem>/<f>: collectDeps: <error>
#   <Stem>/<f>: pure <ok|error ...>; Meta <ok|error ...>; <outputs>; #erase <ours>; oracle <n> calls, <k> differ
# where <outputs> compares <f>.pure with <f>.meta (both files, byte for byte: "identical",
# "differ", or "no pure output"/"no Meta output") and <ours> says which of them the file <f> that
# `#erase` wrote equals ("= pure and Meta", "= Meta", "= pure", "= neither", "no output"); each line
# is followed by the oracle calls that differ ("  oracle: <term> | pure <answer> | Meta <answer>").
# Totals follow. The summary is compared with tests/harness/expected/pure-harness.txt.
#
# --update rewrites the expected summary instead of comparing. --keep DIR keeps the outputs, the
# logs and the diffs of the outputs that differ in DIR (which must not exist or be empty).
#
# Exit status: 0 if the summary equals the expected one and every file elaborated, 1 otherwise.
set -euo pipefail

source "$(dirname "${BASH_SOURCE[0]}")/common.sh"
export LC_ALL=C

update=0
keep=
while [ $# -gt 0 ]; do
  case $1 in
    --update) update=1 ;;
    --keep) shift; [ $# -gt 0 ] || die "--keep needs a directory"; keep=$1 ;;
    -h|--help) sed -n '2,29p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) die "unknown argument $1" ;;
  esac
  shift
done

if [ -n "$keep" ]; then
  mkdir -p "$keep"
  tmp=$(cd "$keep" && pwd)
  [ -z "$(ls -A "$tmp")" ] || die "$tmp is not empty"
else
  tmp=$(mktemp -d)
fi
HDIR=$ROOT/tests/harness
EXPECTED=$HDIR/expected/pure-harness.txt
mkdir -p "$tmp/olean" "$tmp/src" "$tmp/out" "$tmp/log" "$tmp/diff"

echo "building the frontend"
build_frontend "$tmp/log/build.log"
echo "building the harness"
if ! (cd "$ROOT" && lake env sh -c \
        'LEAN_PATH="$1:$LEAN_PATH" exec "${LEAN:-lean}" --root="$2" -o "$1/PureHarness.olean" "$2/PureHarness.lean"' \
        sh "$tmp/olean" "$HDIR") >"$tmp/log/harness.log" 2>&1; then
  tail -n 40 "$tmp/log/harness.log" >&2
  die "the harness does not compile (log: $tmp/log/harness.log)"
fi

status=0
stems=()
while IFS= read -r f; do stems+=("$(basename "$f" .lean)"); done \
  < <(find "$ROOT/tests/corpus" -maxdepth 1 -name '*.lean' | sort)
for stem in "${stems[@]}"; do
  src=$tmp/src/$stem.lean
  out=$tmp/out/$stem
  mkdir -p "$out"
  # the copy imports the harness after the file's own imports
  awk 'BEGIN { done = 0 }
       !done && !/^import / { print "import PureHarness"; done = 1 }
       { print }
       END { if (!done) print "import PureHarness" }' "$ROOT/tests/corpus/$stem.lean" >"$src"
  echo "examples/$stem"
  if ! (cd "$ROOT" && lake env sh -c \
          'cd "$2" && LEAN_PATH="$1:$LEAN_PATH" exec "${LEAN:-lean}" "$3"' \
          sh "$tmp/olean" "$out" "$src") >"$tmp/log/$stem.log" 2>&1; then
    echo "FAIL $stem: lean exited with an error (log: $tmp/log/$stem.log)"
    tail -n 20 "$tmp/log/$stem.log" | sed 's/^/    /'
    status=1
  fi
done

# ---- summary ----------------------------------------------------------------------------------
summary=$tmp/pure-harness.txt
same() { [ -f "$1" ] && [ -f "$2" ] && cmp -s "$1" "$2" && cmp -s "$1.inlinings" "$2.inlinings"; }
{
  n=0; nin=0; nout=0; ncd=0; nid=0; ndiff=0; nnometa=0; nnopure=0; ncalls=0; ndcalls=0; nfail=0
  for stem in "${stems[@]}"; do
    out=$tmp/out/$stem
    while IFS= read -r h; do
      f=${h%.harness}
      name=$stem/$(basename "$f")
      n=$((n + 1))
      cd_line=$(sed -n 's/^collectDeps: //p' "$h")
      if grep -q '^harness error' "$h"; then
        echo "$name: $(cat "$h")"
        continue
      fi
      case $cd_line in
        "outOfFragment "*) nout=$((nout + 1)); echo "$name: out of the fragment: ${cd_line#outOfFragment }"; continue ;;
        ok) ;;
        *) ncd=$((ncd + 1)); echo "$name: collectDeps: $cd_line"; continue ;;
      esac
      nin=$((nin + 1))
      pure=$(sed -n 's/^erasePure: //p' "$h")
      meta=$(sed -n 's/^Meta: //p' "$h")
      if [ ! -f "$f.pure" ]; then outputs="no pure output"; nnopure=$((nnopure + 1))
      elif [ ! -f "$f.meta" ]; then outputs="no Meta output"; nnometa=$((nnometa + 1))
      elif same "$f.pure" "$f.meta"; then outputs="identical"; nid=$((nid + 1))
      else
        outputs="differ"; ndiff=$((ndiff + 1))
        mkdir -p "$tmp/diff/$stem"
        diff -u --label "$name.meta" --label "$name.pure" <(tokenize "$f.meta") <(tokenize "$f.pure") \
          >"$tmp/diff/$stem/$(basename "$f").diff" || true
      fi
      if [ ! -f "$f" ]; then ours="no output"
      elif same "$f" "$f.pure" && same "$f" "$f.meta"; then ours="= pure and Meta"
      elif same "$f" "$f.meta"; then ours="= Meta"
      elif same "$f" "$f.pure"; then ours="= pure"
      else ours="= neither"; fi
      calls=$(sed -n 's/^oracle calls: \([0-9]*\), differing from Meta: \([0-9]*\)$/\1 \2/p' "$h")
      c=${calls% *}; d=${calls#* }
      ncalls=$((ncalls + c)); ndcalls=$((ndcalls + d))
      nfail=$((nfail + $(grep -c '^  .* | pure error ' "$h" || true)))
      grep -q '^harness run equals erasePure: true$' "$h" || echo "$name: the harness run differs from erasePure"
      echo "$name: pure $pure; Meta $meta; outputs $outputs; #erase $ours; oracle $c calls, $d differ"
      sed -n 's/^  /  oracle: /p' "$h"
    done < <(find "$out" -maxdepth 1 -name '*.harness' | sort)
  done
  echo "totals: $n #erase, $nin in the fragment, $nout out of the fragment, $ncd collectDeps errors"
  echo "in the fragment: $nid identical, $ndiff differ, $nnometa without Meta output, $nnopure without pure output"
  echo "oracle: $ncalls calls, $ndcalls differ from Meta, $nfail failures of the pure oracle"
} >"$summary"

if [ $update -eq 1 ]; then
  mkdir -p "$(dirname "$EXPECTED")"
  cp "$summary" "$EXPECTED"
  echo "updated ${EXPECTED#$ROOT/}"
elif ! cmp -s "$summary" "$EXPECTED"; then
  echo "FAIL: the summary differs from ${EXPECTED#$ROOT/}"
  diff -u --label expected --label got "$EXPECTED" "$summary" | head -n 60 | sed 's/^/    /' || true
  status=1
fi
tail -n 3 "$summary"
if [ $status -ne 0 ]; then
  echo "outputs, logs and summary kept in $tmp"
  exit 1
fi
if [ -n "$keep" ]; then
  echo "outputs, logs and summary in $tmp"
else
  rm -rf "$tmp"
fi
echo "pure harness passed"
