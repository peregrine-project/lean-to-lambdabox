#!/usr/bin/env bash
# Run the checks of the proof package.
#
# Usage: proof/scripts/check.sh [--no-regress]
#
#   build     C1   `lake build` of the root package (the eraser and the lean4lean libraries) and of
#                  proof/ (library EraseProof, which builds its tests).
#   tokens    C2   no sorry, admit, axiom, opaque, native_decide, native, bv_decide, unsafe,
#                  implemented_by, extern (and the other tokens of scripts/scan_tokens.py) in
#                  proof/**/*.lean outside comments and strings.
#   report    C3-C7, C9, run by `lake env lean --run tools/Report.lean` in proof/: axiom
#                  footprints within propext, Classical.choice, Quot.sound, sorryAx (no
#                  Verify/Axioms.lean or native axiom); sorryAx only from lean4lean's L1-L8
#                  (tests: also TrProj);
#                  lean4lean's TrExprS/TrExpr/TrProj and the tests unreachable from non-test
#                  declarations; no leaves with respect to ROOTS.txt; footprints of roots and test
#                  theorems equal axioms.expected; every source file imported; the entries of
#                  doc/DIVERGENCES.md well-formed, citing existing declarations, files and lines.
#                  See the header of tools/Report.lean.
#   regress   C10  the shipping regression tests, scripts/regress.sh (skipped with --no-regress).
#
# Logs go to proof/.check/<step>.log; the report also writes proof/.check/footprints.txt and
# proof/.check/axioms.actual (what axioms.expected should contain).
#
# Exit status: 0 if every step passes, 1 otherwise. A failed build stops the script; the other
# steps all run.
set -euo pipefail

PROOF=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
ROOT=$(cd "$PROOF/.." && pwd)
LOG=$PROOF/.check

regress=1
for a in "$@"; do
  case $a in
    --no-regress) regress=0 ;;
    -h|--help) sed -n '2,25p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "error: unknown argument $a" >&2; exit 2 ;;
  esac
done

mkdir -p "$LOG"
failed=()

# run NAME COMMAND...: run COMMAND with output to $LOG/NAME.log; on failure print the log's tail
# and record NAME.
run() {
  local name=$1
  shift
  echo "== $name"
  if "$@" >"$LOG/$name.log" 2>&1; then
    return 0
  fi
  tail -n 60 "$LOG/$name.log"
  echo "FAIL $name (log: $LOG/$name.log)"
  failed+=("$name")
  return 1
}

build_root() ( cd "$ROOT" && lake build LeanToLambdaBox Lean4Lean Lean4Lean.Theory Lean4Lean.Verify )
build_proof() ( cd "$PROOF" && lake build )
report() ( cd "$PROOF" && lake env lean --run tools/Report.lean )

run build-root build_root || exit 1
run build-proof build_proof || exit 1
run tokens python3 "$PROOF/scripts/scan_tokens.py" "$PROOF" || true
if run report report; then cat "$LOG/report.log"; fi
if [ $regress = 1 ]; then
  run regress "$ROOT/scripts/regress.sh" || true
fi

if [ ${#failed[@]} -gt 0 ]; then
  echo "check.sh: failed: ${failed[*]}"
  exit 1
fi
echo "check.sh: all checks passed"
