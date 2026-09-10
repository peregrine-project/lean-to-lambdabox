#!/usr/bin/env bash
# Docstring and comment hygiene over LeanToLambdaBox/**/*.lean and VerifyBench/*.lean.
# Fails on memory-store references, handoff-document references, slice tags, git hashes
# in backticks, ISO dates, and history narration in comments. Reports the comment
# fraction per file and tree-wide without failing on it.
# Usage: scripts/hygiene.sh [--allow FILE]   (FILE lists repo-root-relative paths, one per
# line, whose findings are printed but do not fail the run)
set -uo pipefail
root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$root" || exit 2

allow_file=""
while [ $# -gt 0 ]; do
  case "$1" in
    --allow) allow_file="${2:-}"; shift 2 ;;
    --allow=*) allow_file="${1#--allow=}"; shift ;;
    -h|--help) sed -n '2,7p' "$0"; exit 0 ;;
    *) echo "scripts/hygiene.sh: unknown argument '$1'" >&2; exit 2 ;;
  esac
done
if [ -n "$allow_file" ] && [ ! -f "$allow_file" ]; then
  echo "scripts/hygiene.sh: allow file '$allow_file' not found" >&2
  exit 2
fi

tmp=$(mktemp -d) || exit 2
trap 'rm -rf "$tmp"' EXIT

find LeanToLambdaBox -name '*.lean' -print > "$tmp/files"
find VerifyBench -maxdepth 1 -name '*.lean' -print >> "$tmp/files"
sort -o "$tmp/files" "$tmp/files"

if [ ! -s "$tmp/files" ]; then
  echo "scripts/hygiene.sh: no .lean files found under LeanToLambdaBox/ or VerifyBench/" >&2
  exit 2
fi

# Comment view: one tab-separated record per line carrying comment text, plus one
# per-file record with the total and comment-or-blank line counts.
xargs -a "$tmp/files" awk '
  function flushfile() {
    if (fname != "") printf "F\t%s\t%d\t%d\n", fname, total, cmtlines
  }
  BEGIN { FS = "\n"; fname = ""; depth = 0 }
  FNR == 1 { flushfile(); fname = FILENAME; total = 0; cmtlines = 0; depth = 0 }
  {
    total++
    startdepth = depth
    line = $0
    cmt = ""
    i = 1; n = length(line); instr = 0
    while (i <= n) {
      two = substr(line, i, 2); c = substr(line, i, 1)
      if (depth > 0) {
        if (two == "-/") { depth--; i += 2; continue }
        if (two == "/-") { depth++; i += 2; continue }
        cmt = cmt c; i++; continue
      }
      if (instr) {
        if (c == "\\") { i += 2; continue }
        if (c == "\"") { instr = 0 }
        i++; continue
      }
      if (two == "--") { cmt = cmt substr(line, i); break }
      if (two == "/-") { depth++; i += 2; continue }
      if (c == "\"") { instr = 1; i++; continue }
      i++
    }
    trimmed = line
    sub(/^[ \t]+/, "", trimmed)
    if (trimmed == "" || substr(trimmed, 1, 2) == "--" || substr(trimmed, 1, 2) == "/-" || startdepth > 0)
      cmtlines++
    if (cmt ~ /[^ \t]/) printf "C\t%s\t%d\t%s\n", fname, FNR, cmt
  }
  END { flushfile() }
' > "$tmp/view"

grep -a "^C	" "$tmp/view" > "$tmp/comments" || true
grep -a "^F	" "$tmp/view" > "$tmp/counts" || true

# ── categories ────────────────────────────────────────────────────────────────
: > "$tmp/hits"

record() { # record CATEGORY < grep-output(path:line:text)
  awk -v cat="$1" -F: '{ printf "%s\t%s:%s\n", cat, $1, $2 }' >> "$tmp/hits"
}

xargs -a "$tmp/files" grep -HnF -e 'memory `' \
  2>/dev/null | record memory-ref

xargs -a "$tmp/files" grep -HnEi -e 'PROJECT_STATUS_HANDOFF' -e 'RECENT_WORK\.md' -e 'handoff' \
  2>/dev/null | record handoff-ref

xargs -a "$tmp/files" grep -HnE \
  -e 'Γ-U[0-9]' -e 'Γ-W[0-9]' -e 'proj-P[0-9]' -e 'δ-D[0-9]' -e 'δ-N' \
  -e 'slice S[0-9]' -e 'slice W[0-3]' -e 'slice L[1-4]' -e 'slice δ' \
  -e 'WS-[A-Z0-9]+' \
  2>/dev/null | record slice-tag

xargs -a "$tmp/files" grep -HnE \
  -e '`[^`]*\b[0-9a-f]{40}\b[^`]*`' -e '`[^`]*\b[0-9a-f]{7}\b[^`]*`' \
  2>/dev/null | record git-hash

xargs -a "$tmp/files" grep -HnE -e '20[0-9][0-9]-[01][0-9]-[0-3][0-9]' \
  2>/dev/null | record iso-date

grep -aE -e 'used to ' -e 'no longer' -e 'retired' -e 're-pin' -e '\[Corrected' \
  -e 'superseded' -e 'at the .* pin' "$tmp/comments" \
  | awk -F'\t' '{ printf "history-narration\t%s:%s\n", $2, $3 }' >> "$tmp/hits"

sort -u -o "$tmp/hits" "$tmp/hits"

# ── allow list ────────────────────────────────────────────────────────────────
: > "$tmp/allow"
if [ -n "$allow_file" ]; then
  grep -av -e '^[[:space:]]*#' -e '^[[:space:]]*$' "$allow_file" \
    | sed 's|^[[:space:]]*||; s|[[:space:]]*$||; s|^\./||' > "$tmp/allow"
fi

awk -F'\t' -v allowf="$tmp/allow" '
  BEGIN {
    while ((getline l < allowf) > 0) if (l != "") allowed[l] = 1
  }
  {
    path = $2; sub(/:[0-9]+$/, "", path)
    if (path in allowed) printf "%s\t%s\tallowed\n", $1, $2
    else printf "%s\t%s\tfail\n", $1, $2
  }
' "$tmp/hits" > "$tmp/marked"

echo "== offending lines"
if [ -s "$tmp/marked" ]; then
  awk -F'\t' '{ printf "%s: %s%s\n", $2, $1, ($3 == "allowed" ? " (allowed)" : "") }' "$tmp/marked" \
    | sort -t: -k1,1 -k2,2n
else
  echo "(none)"
fi

echo
echo "== summary by category"
fails=0
for cat in memory-ref handoff-ref slice-tag git-hash iso-date history-narration; do
  n=$(awk -F'\t' -v c="$cat" '$1 == c && $3 == "fail"' "$tmp/marked" | wc -l)
  a=$(awk -F'\t' -v c="$cat" '$1 == c && $3 == "allowed"' "$tmp/marked" | wc -l)
  printf "  %-18s %5d  (allowed: %d)\n" "$cat" "$n" "$a"
  fails=$((fails + n))
done
printf "  %-18s %5d\n" "TOTAL" "$fails"

echo
echo "== comment fraction (report only)"
awk -F'\t' '
  { path = $2; tot = $3 + 0; cmt = $4 + 0
    if (!(path in files)) nfiles++
    files[path] = 1; T[path] = tot; C[path] = cmt
    gt += tot; gc += cmt }
  END {
    for (p in files)
      printf "  %6.1f%%  %5d/%-5d  %s\n", (T[p] ? 100.0 * C[p] / T[p] : 0), C[p], T[p], p
    printf "TREE\t%6.1f%%  %d/%d lines over %d files\n", (gt ? 100.0 * gc / gt : 0), gc, gt, nfiles
  }
' "$tmp/counts" > "$tmp/frac"
grep -av '^TREE' "$tmp/frac" | sort -rn -k1
echo
grep -a '^TREE' "$tmp/frac" | sed 's/^TREE\t/  tree-wide: /'

echo
if [ "$fails" -gt 0 ]; then
  echo "hygiene: FAIL ($fails offending lines)"
  exit 1
fi
echo "hygiene: OK"
exit 0
