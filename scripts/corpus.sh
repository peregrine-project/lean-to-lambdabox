#!/usr/bin/env bash
# Regenerate the fixed corpus of emitted λ□ programs from this checkout.
#
# Usage: scripts/corpus.sh OUTDIR
#
# OUTDIR must not exist or be empty. Layout of the result:
#   OUTDIR/benchmarks/prune/<test>.{ast,ast.inlinings,mli}    PRUNE_CONSTRUCTORS=1 (Makefile default)
#   OUTDIR/benchmarks/noprune/<test>.{ast,ast.inlinings,mli}  PRUNE_CONSTRUCTORS=0
#   OUTDIR/examples/<Stem>/<files>                            tests/corpus/<Stem>.lean
#   OUTDIR/_meta/                                             logs and run information (not corpus)
#
# Benchmarks are the `natio` entries of benchmarks/TESTS, erased through
# benchmarks/via_malfunction/Makefile exactly as the benchmark pipeline does it; the build
# directory is read back from `make -p`, and stale outputs are deleted first because the
# Makefile's .ast rule does not depend on the frontend sources.
# Examples are elaborated with the root package on the load path, with their output directory as
# working directory, so their relative `#erase ... to "<file>"` paths land there.
#
# Compare two corpora with scripts/corpus-diff.sh.
set -euo pipefail

source "$(dirname "${BASH_SOURCE[0]}")/common.sh"

[ $# -eq 1 ] || die "usage: scripts/corpus.sh OUTDIR"
mkdir -p "$1"
OUT=$(cd "$1" && pwd)
[ -z "$(ls -A "$OUT")" ] || die "$OUT is not empty"
META=$OUT/_meta
LOGS=$META/logs
mkdir -p "$LOGS"
export LC_ALL=C

echo "building the frontend"
build_frontend "$LOGS/build.log"

# ---- benchmarks -------------------------------------------------------------------------------
VM=$ROOT/benchmarks/via_malfunction
TESTS=()
while IFS= read -r t; do TESTS+=("$t"); done < <(awk -F: '$2=="natio"{print $1}' "$ROOT/benchmarks/TESTS")
[ ${#TESTS[@]} -gt 0 ] || die "no natio tests in benchmarks/TESTS"

for variant in prune:1 noprune:0; do
  name=${variant%%:*}
  prune=${variant##*:}
  db=$(mktemp)
  (cd "$VM" && env -u ERASURE_CONFIG make -p PRUNE_CONSTRUCTORS="$prune" >"$db" 2>&1) || true
  id=$(sed -n 's/^build := build\///p' "$db" | head -n 1)
  rm -f "$db"
  [ -n "$id" ] || die "could not read the build directory from make -p (PRUNE_CONSTRUCTORS=$prune)"
  echo "benchmarks/$name: build/$id (${#TESTS[@]} programs)"
  targets=()
  for t in "${TESTS[@]}"; do
    rm -f "$VM/build/$id/$t.lean" "$VM/build/$id/$t.ast" "$VM/build/$id/$t.ast.inlinings" "$VM/build/$id/$t.mli"
    targets+=("build/$id/$t.ast")
  done
  if ! (cd "$VM" && env -u ERASURE_CONFIG make PRUNE_CONSTRUCTORS="$prune" "${targets[@]}") \
         >"$LOGS/benchmarks-$name.log" 2>&1; then
    tail -n 40 "$LOGS/benchmarks-$name.log" >&2
    die "benchmark erasure failed (log: $LOGS/benchmarks-$name.log)"
  fi
  mkdir -p "$OUT/benchmarks/$name"
  for t in "${TESTS[@]}"; do
    for ext in ast ast.inlinings mli; do
      f=$VM/build/$id/$t.$ext
      [ -f "$f" ] || die "missing $f"
      cp "$f" "$OUT/benchmarks/$name/$t.$ext"
    done
  done
  echo "$name build/$id" >>"$META/benchmark-build-dirs"
done

# ---- own examples -----------------------------------------------------------------------------
EXAMPLES=()
while IFS= read -r f; do EXAMPLES+=("$f"); done < <(find "$ROOT/tests/corpus" -maxdepth 1 -name '*.lean' | sort)
for f in "${EXAMPLES[@]}"; do
  stem=$(basename "$f" .lean)
  d=$OUT/examples/$stem
  mkdir -p "$d"
  echo "examples/$stem"
  if ! run_lean "$d" "$f" "$LOGS/example-$stem.log"; then
    tail -n 40 "$LOGS/example-$stem.log" >&2
    die "elaborating $f failed (log: $LOGS/example-$stem.log)"
  fi
  [ -n "$(ls -A "$d")" ] || die "$f emitted no file"
done

# ---- run information (not part of the corpus) -------------------------------------------------
{
  echo "commit: $(git -C "$ROOT" rev-parse HEAD 2>/dev/null || echo unknown)"
  echo "dirty: $(git -C "$ROOT" status --porcelain 2>/dev/null | wc -l | tr -d ' ') paths"
  echo "toolchain: $(cat "$ROOT/lean-toolchain")"
  echo "lean: $(cd "$ROOT" && lake env sh -c '"${LEAN:-lean}" --version' 2>&1)"
} >"$META/info"
for log in "$LOGS"/*.log; do
  printf '%s %s\n' "$(grep -c 'PANIC' "$log" || true)" "$(basename "$log")"
done >"$META/panics"

nfiles=$(find "$OUT" -path "$META" -prune -o -type f -print | wc -l | tr -d ' ')
echo "corpus written to $OUT ($nfiles files; logs in _meta/logs, PANIC counts in _meta/panics)"
