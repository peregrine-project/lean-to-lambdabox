#!/usr/bin/env bash
# Runs test/ErasesLBCheck.lean and diffs its output against test/erasesLB.expected.
# Exit code is the diff's: 0 when the composite's introduction lemmas still have the
# statements and the axiom footprints the fixture records.
set -uo pipefail
root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$root" || exit 2

actual=$(mktemp) || exit 2
trap 'rm -f "$actual"' EXIT

lake env lean test/ErasesLBCheck.lean > "$actual" 2>&1

diff -u test/erasesLB.expected "$actual"
