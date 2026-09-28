# Helpers shared by scripts/corpus.sh and scripts/regress.sh. Source this file; do not run it.
#
# Everything goes through `lake` from PATH, so the toolchain is the one named by the checkout's
# `lean-toolchain` files (resolved by elan). Nothing here names a Lean version.

# Absolute path of the repository root (the parent of scripts/).
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)

# Print a message to stderr and exit.
die() {
  echo "error: $*" >&2
  exit 1
}

# build_frontend LOG: run `lake build` at the root, logging to LOG; fail with the log's tail.
build_frontend() {
  local log=$1
  if ! (cd "$ROOT" && lake build) >"$log" 2>&1; then
    tail -n 40 "$log" >&2
    die "lake build failed (full log: $log)"
  fi
}

# run_lean DIR FILE LOG: elaborate the Lean file FILE (absolute path) with the root package's
# LEAN_PATH, with DIR as working directory, so that relative `#erase ... to "<file>"` paths land
# in DIR. Output goes to LOG. Returns lean's exit status.
# Lean derives the main module name, which appears in hygienic binder names of the output, from
# FILE's path relative to the working directory, and uses `_stdin` when FILE lies outside it.
# Callers keep FILE outside DIR, so the emitted names do not depend on where DIR is.
run_lean() {
  local dir=$1 file=$2 log=$3
  (cd "$ROOT" && lake env sh -c 'cd "$1" && exec "${LEAN:-lean}" "$2"' sh "$dir" "$file") >"$log" 2>&1
}

# tokenize FILE: print an S-expression file with a line break before every "(" that opens a
# constructor (a "(" followed by a letter), for readable line-based diffs.
tokenize() {
  sed 's/(\([A-Za-z]\)/\
(\1/g' "$1"
  echo
}

# normalize_hygiene: read an emitted file on stdin and replace every hygienic name suffix by a fixed
# token, so that output of toolchains with different macro-scope encodings can be compared.
#   x._@.M._hyg.9                       -> x._@._hyg
#   x._@.M.46841144._hygCtx._hyg.2      -> x._@._hyg
#   hygienic kername ids: "_hyg") "384" -> "_hyg") "N"
normalize_hygiene() {
  sed -E \
    -e 's/\._@\.[^"]*_hyg(\.[0-9]+)+/._@._hyg/g' \
    -e 's/"_hyg"\) "[0-9]+"/"_hyg") "N"/g'
}
