#!/bin/bash
# Write proof/spec.pin (check C12b): the pin of the statement definitions listed in
# tools/Report.lean (`statements`), computed over the built library and the shipping code with the
# toolchain and dependency revisions of the root package. Run it after `lake build` in proof/,
# whenever a statement, a definition it reaches or a revision changes, and review the diff.
# Usage (from the repository root): _state-cl/bin/lcap proof/scripts/pin.sh   [OUT]  (default proof/spec.pin)
set -euo pipefail
cd "$(dirname "$0")/.."
OUT=${1:-spec.pin}
lake env lean --run tools/Report.lean --shipping .. --src . --out .check --write-pin "$OUT"
