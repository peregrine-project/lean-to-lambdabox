#!/usr/bin/env bash
# Build the blueprint. Usage, from anywhere:
#
#   blueprint/build.sh [web|pdf|all]      (default: all)
#
# 1. renders the registers and the pins into src/generated/ (scripts/render_registers.py), and the
#    node kinds and their legends (scripts/kinds.py);
# 2. web: `plastex` on src/web.tex into web/ (what `leanblueprint web` runs; writes lean_decls; the
#    package scripts/bpkinds.py lays out the dependency graphs with scripts/kindgraph.py, and links
#    every Lean name, file and line to its source on GitHub at the commit HEAD, or $BP_COMMIT, or
#    $GITHUB_SHA in CI: scripts/leanlinks.py);
# 3. pdf: `latexmk` on src/print.tex into print/ (what `leanblueprint pdf` runs), if xelatex exists;
# 4. all, when both were built: copies print/print.pdf to web/blueprint.pdf, which the web version
#    links to. web/ is then the whole site that CI publishes (.github/workflows/blueprint.yml).
#
# Needs python3 and, on PATH, the `plastex` of a venv with leanblueprint installed; for the pdf,
# latexmk and xelatex. The census chapters (src/generated/census-*.tex) come from the Lean
# environment: scripts/audit.py --update rewrites them, and scripts/audit.py checks them.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
target=${1:-all}
pdf_built=0
case $target in web|pdf|all) ;; *) echo "usage: $0 [web|pdf|all]" >&2; exit 2;; esac

python3 "$here/scripts/render_registers.py"
python3 "$here/scripts/kinds.py"

if [[ $target == web || $target == all ]]; then
  command -v plastex >/dev/null || { echo "build.sh: plastex not on PATH (activate the leanblueprint venv)" >&2; exit 2; }
  mkdir -p "$here/web"
  rm -f "$here/web/blueprint.pdf"
  # The links point at a commit: the Lean files must not differ from it.
  if ! git -C "$here/.." diff --quiet HEAD -- . ':(exclude)blueprint'; then
    echo "build.sh: warning: the working tree differs from HEAD outside blueprint/; the links to the Lean sources point at HEAD" >&2
  fi
  (cd "$here/src" && plastex -c plastex.cfg web.tex)
  echo "build.sh: web version in blueprint/web/index.html"
fi

if [[ $target == pdf || $target == all ]]; then
  if command -v xelatex >/dev/null && command -v latexmk >/dev/null; then
    mkdir -p "$here/print"
    (cd "$here/src" && latexmk -output-directory=../print)
    pdf_built=1
    echo "build.sh: pdf version in blueprint/print/print.pdf"
  elif [[ $target == pdf ]]; then
    echo "build.sh: xelatex or latexmk not found" >&2; exit 2
  else
    echo "build.sh: xelatex or latexmk not found, pdf skipped"
  fi
fi

if [[ $target == all && $pdf_built == 1 ]]; then
  cp "$here/print/print.pdf" "$here/web/blueprint.pdf"
  echo "build.sh: site (web version and pdf) in blueprint/web/"
fi
