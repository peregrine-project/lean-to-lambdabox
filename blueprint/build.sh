#!/usr/bin/env bash
# Build the blueprint. Usage, from anywhere:
#
#   blueprint/build.sh [web|pdf|all]      (default: all)
#
# 1. renders the registers and the pins into src/generated/ (scripts/render_registers.py);
# 2. web: `plastex` on src/web.tex into web/ (what `leanblueprint web` runs; writes lean_decls);
# 3. pdf: `latexmk` on src/print.tex into print/ (what `leanblueprint pdf` runs), if xelatex exists.
#
# Needs python3 and, on PATH, the `plastex` of a venv with leanblueprint installed; for the pdf,
# latexmk and xelatex. The census chapters (src/generated/census-*.tex) come from the Lean
# environment: scripts/audit.py --update rewrites them, and scripts/audit.py checks them.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
target=${1:-all}
case $target in web|pdf|all) ;; *) echo "usage: $0 [web|pdf|all]" >&2; exit 2;; esac

python3 "$here/scripts/render_registers.py"

if [[ $target == web || $target == all ]]; then
  command -v plastex >/dev/null || { echo "build.sh: plastex not on PATH (activate the leanblueprint venv)" >&2; exit 2; }
  mkdir -p "$here/web"
  (cd "$here/src" && plastex -c plastex.cfg web.tex)
  echo "build.sh: web version in blueprint/web/index.html"
fi

if [[ $target == pdf || $target == all ]]; then
  if command -v xelatex >/dev/null && command -v latexmk >/dev/null; then
    mkdir -p "$here/print"
    (cd "$here/src" && latexmk -output-directory=../print)
    echo "build.sh: pdf version in blueprint/print/print.pdf"
  elif [[ $target == pdf ]]; then
    echo "build.sh: xelatex or latexmk not found" >&2; exit 2
  else
    echo "build.sh: xelatex or latexmk not found, pdf skipped"
  fi
fi
