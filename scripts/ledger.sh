#!/usr/bin/env bash
# Runs test/Ledger.lean and diffs its output against test/ledger.expected.
# Exit code is the diff's: 0 when the measured axiom footprints match the fixture.
set -uo pipefail
root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$root" || exit 2

actual=$(mktemp) || exit 2
trap 'rm -f "$actual"' EXIT

lake env lean test/Ledger.lean > "$actual" 2>&1

diff -u test/ledger.expected "$actual"
