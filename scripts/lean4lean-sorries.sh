#!/usr/bin/env bash
# Lists every non-comment `sorry` in the pinned lean4lean, as `path:line: <decl>`,
# with the pinned rev on the first line, and diffs it against
# test/lean4lean-sorries.expected. `--write` regenerates the fixture instead.
# Exit code is the diff's: a re-pin or a new upstream hole makes it fail.
set -uo pipefail
root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$root" || exit 2

pkg=.lake/packages/lean4lean
fixture=test/lean4lean-sorries.expected

rev=$(awk '
  { s = s $0 }
  END {
    gsub(/[ \t\r\n]/, "", s)
    if (match(s, /\{[^{}]*"name":"lean4lean"[^{}]*\}/)) {
      blk = substr(s, RSTART, RLENGTH)
      if (match(blk, /"rev":"[0-9a-f]+"/))
        print substr(blk, RSTART + 7, RLENGTH - 8)
    }
  }' lake-manifest.json)

if [ -z "$rev" ]; then
  echo "scripts/lean4lean-sorries.sh: no lean4lean rev in lake-manifest.json" >&2
  exit 2
fi
if [ ! -d "$pkg/Lean4Lean" ]; then
  echo "scripts/lean4lean-sorries.sh: $pkg/Lean4Lean not found" >&2
  exit 2
fi

scan() {
  echo "lean4lean rev $rev"
  find "$pkg/Lean4Lean" -name '*.lean' \
    -not -path "$pkg/Lean4Lean/Experimental/*" \
    -not -path "$pkg/Lean4Lean/Tests/*" \
    -print0 \
  | sort -z \
  | xargs -0 -n1 awk '
  function strip(line,   i, n, c, two, out, instr) {
    out = ""; i = 1; n = length(line); instr = 0
    while (i <= n) {
      two = substr(line, i, 2); c = substr(line, i, 1)
      if (depth > 0) {
        if (two == "-/") { depth--; i += 2; continue }
        if (two == "/-") { depth++; i += 2; continue }
        i++; continue
      }
      if (instr) {
        if (c == "\\") { i += 2; continue }
        if (c == "\"") { instr = 0 }
        i++; continue
      }
      if (two == "--") { break }
      if (two == "/-") { depth++; i += 2; continue }
      if (c == "\"") { instr = 1; i++; continue }
      out = out c; i++
    }
    return out
  }
  function nsjoin(   i, s) {
    s = ""
    for (i = 1; i <= nsn; i++) if (ns[i] != "") s = (s == "" ? ns[i] : s "." ns[i])
    return s
  }
  BEGIN { depth = 0; nsn = 0; decl = "" }
  FNR == 1 { depth = 0; nsn = 0; decl = "" }
  {
    code = strip($0)
    if (code ~ /^[ \t]*namespace[ \t]+[^ \t]+/) {
      t = code; sub(/^[ \t]*namespace[ \t]+/, "", t); sub(/[ \t].*$/, "", t)
      ns[++nsn] = t
    } else if (code ~ /^[ \t]*section([ \t]|$)/) {
      ns[++nsn] = ""
    } else if (code ~ /^[ \t]*end([ \t]|$)/) {
      if (nsn > 0) nsn--
      decl = ""
    } else if (code ~ /^[ \t]*(@\[[^]]*\][ \t]*)?((private|protected|noncomputable|partial|unsafe|scoped|local|nonrec)[ \t]+)*(theorem|lemma|def|instance|abbrev|structure|inductive|opaque|example)[ \t]/) {
      t = code
      sub(/^[ \t]*(@\[[^]]*\][ \t]*)?/, "", t)
      while (t ~ /^(private|protected|noncomputable|partial|unsafe|scoped|local|nonrec)[ \t]/) sub(/^[^ \t]+[ \t]+/, "", t)
      kw = t; sub(/[ \t].*$/, "", kw)
      sub(/^[^ \t]+[ \t]+/, "", t)
      sub(/[ \t({\[:].*$/, "", t)
      if (kw == "example" || t == "") decl = kw
      else { p = nsjoin(); decl = (p == "" ? t : p "." t) }
    }
    if (code ~ /(^|[^A-Za-z0-9_'"'"'?!.])sorry([^A-Za-z0-9_'"'"'?!]|$)/) {
      printf "%s:%d: %s\n", FILENAME, FNR, (decl == "" ? "<unknown>" : decl)
    }
  }' \
  | sed "s|^$pkg/|.lake/packages/lean4lean/|" \
  | sort
}

if [ "${1:-}" = "--write" ]; then
  scan > "$fixture"
  echo "wrote $fixture"
  exit 0
fi

actual=$(mktemp) || exit 2
trap 'rm -f "$actual"' EXIT
scan > "$actual"
diff -u "$fixture" "$actual"
