#!/usr/bin/env bash
# Compare two corpora produced by scripts/corpus.sh.
#
# Usage: scripts/corpus-diff.sh [--normalize] [--summary] A B
#
#   --normalize  also compare the files after replacing hygienic name suffixes
#                (x._@.M._hyg.N, x._@.M.<hash>._hygCtx._hyg.N, hygienic kername ids) by a fixed
#                token; a file that differs only there is reported as "identical after
#                normalization", which separates toolchain-induced renamings from real changes.
#                Other name changes, such as `_private.<Module>.0.` prefixes, are not normalized.
#   --summary    print only the summary, not the per-file diffs.
#
# The summary lists the files present only in A, only in B, and present in both but differing.
# Per-file diffs are unified diffs of the files with a line break before every "(", taken after
# normalization when --normalize is given. Files under _meta/ (logs, run information) are ignored.
#
# Exit status: 0 if the corpora agree (byte for byte, or after normalization with --normalize),
# 1 if they differ, 2 on usage errors.
set -euo pipefail

source "$(dirname "${BASH_SOURCE[0]}")/common.sh"

normalize=0
summary_only=0
args=()
for a in "$@"; do
  case $a in
    --normalize) normalize=1 ;;
    --summary) summary_only=1 ;;
    -h|--help) sed -n '2,19p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    -*) echo "unknown option $a" >&2; exit 2 ;;
    *) args+=("$a") ;;
  esac
done
[ ${#args[@]} -eq 2 ] || { echo "usage: scripts/corpus-diff.sh [--normalize] [--summary] A B" >&2; exit 2; }
A=${args[0]}
B=${args[1]}
[ -d "$A" ] || { echo "not a directory: $A" >&2; exit 2; }
[ -d "$B" ] || { echo "not a directory: $B" >&2; exit 2; }
export LC_ALL=C

list() { (cd "$1" && find . -path ./_meta -prune -o -type f -print | sed 's|^\./||' | sort); }

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
list "$A" >"$tmp/a"
list "$B" >"$tmp/b"
comm -23 "$tmp/a" "$tmp/b" >"$tmp/only-a"
comm -13 "$tmp/a" "$tmp/b" >"$tmp/only-b"
: >"$tmp/same"; : >"$tmp/norm"; : >"$tmp/diff"
while IFS= read -r f; do
  if cmp -s "$A/$f" "$B/$f"; then
    echo "$f" >>"$tmp/same"
  elif [ $normalize -eq 1 ] && cmp -s <(normalize_hygiene <"$A/$f") <(normalize_hygiene <"$B/$f"); then
    echo "$f" >>"$tmp/norm"
  else
    echo "$f" >>"$tmp/diff"
  fi
done < <(comm -12 "$tmp/a" "$tmp/b")

count() { wc -l <"$1" | tr -d ' '; }
section() {
  local title=$1 file=$2
  [ -s "$file" ] || return 0
  echo "$title:"
  sed 's/^/  /' "$file"
}

echo "A: $A"
echo "B: $B"
echo "identical: $(count "$tmp/same")"
[ $normalize -eq 0 ] || echo "identical after normalization: $(count "$tmp/norm")"
echo "differing: $(count "$tmp/diff")"
echo "only in A: $(count "$tmp/only-a")"
echo "only in B: $(count "$tmp/only-b")"
section "only in A" "$tmp/only-a"
section "only in B" "$tmp/only-b"
section "identical after normalization" "$tmp/norm"
section "differing" "$tmp/diff"

if [ $summary_only -eq 0 ]; then
  while IFS= read -r f; do
    echo
    echo "=== $f"
    if [ $normalize -eq 1 ]; then
      normalize_hygiene <"$A/$f" >"$tmp/x"
      normalize_hygiene <"$B/$f" >"$tmp/y"
    else
      cp "$A/$f" "$tmp/x"
      cp "$B/$f" "$tmp/y"
    fi
    diff -u --label "A/$f" --label "B/$f" <(tokenize "$tmp/x") <(tokenize "$tmp/y") || true
  done <"$tmp/diff"
fi

if [ -s "$tmp/diff" ] || [ -s "$tmp/only-a" ] || [ -s "$tmp/only-b" ]; then
  exit 1
fi
exit 0
