#!/usr/bin/env python3
"""Report forbidden tokens in the Lean files of the proof package (check C2).

Usage: scan_tokens.py DIR

Scans every `.lean` file under DIR (skipping `.lake` and `.check`) for the identifiers of
FORBIDDEN, outside comments, string literals and character literals. An identifier matches when
one of its dot-separated components equals a forbidden token. Prints one line per occurrence,
`file:line:col: token: source line`, and exits with 1 if there is any, else 0.
"""

import os
import re
import sys

FORBIDDEN = [
    # proofs left open
    "sorry", "admit",
    # new axioms and hidden bodies
    "axiom", "opaque",
    # native code in proofs (`native_decide`, `decide +native`, `bv_decide`) and its axioms
    "native_decide", "native", "bv_decide", "ofReduceBool", "ofReduceNat", "trustCompiler",
    # code outside the logic
    "unsafe", "implemented_by", "extern",
    # declarations the kernel does not check
    "skipKernelTC", "addDeclWithoutChecking",
]

IDENT = re.compile(r"[^\W\d][\w'!?]*(?:\.[^\W\d][\w'!?]*)*|«[^»]*»")


def strip(text):
    """Return TEXT with comments, string literals (except the code of interpolations such as
    `s!"..{e}.."`) and character literals replaced by spaces; line breaks are kept, so positions
    are preserved."""
    out = list(text)
    n = len(text)

    def blank(a, b):
        for k in range(a, min(b, n)):
            if out[k] != "\n":
                out[k] = " "

    def comment(i):  # text[i:i+2] == "/-"; returns the index after the matching "-/"
        depth, j = 0, i
        while j < n:
            if text.startswith("/-", j):
                depth, j = depth + 1, j + 2
            elif text.startswith("-/", j):
                depth, j = depth - 1, j + 2
                if depth == 0:
                    break
            else:
                j += 1
        blank(i, j)
        return j

    def string(i, interpolated):  # text[i] == '"'; returns the index after the closing quote
        j = i + 1
        while j < n and text[j] != '"':
            if text[j] == "\\":
                blank(j, j + 2)
                j += 2
            elif interpolated and text[j] == "{":
                j = code(j + 1, True)
            else:
                blank(j, j + 1)
                j += 1
        blank(i, i + 1)
        blank(j, j + 1)
        return j + 1

    def code(i, in_braces):  # returns the end of the text, or the index after the closing "}"
        depth = 0
        while i < n:
            c = text[i]
            prev = text[i - 1] if i > 0 else " "
            if text.startswith("/-", i):
                i = comment(i)
            elif text.startswith("--", i):
                j = text.find("\n", i)
                j = n if j < 0 else j
                blank(i, j)
                i = j
            elif c == "r" and re.match(r'r#*"', text[i:]) and not re.match(r"[\w'!?.]", prev):
                m = re.match(r'r(#*)"', text[i:])
                j = text.find('"' + m.group(1), i + len(m.group(0)))
                j = n if j < 0 else j + 1 + len(m.group(1))
                blank(i, j)
                i = j
            elif c == '"':
                i = string(i, prev == "!")
            elif c == "'" and not re.match(r"[\w'!?]", prev):
                m = re.match(r"'(\\.[^']*|[^\\'])'", text[i:])
                if m:
                    blank(i, i + len(m.group(0)))
                    i += len(m.group(0))
                else:
                    i += 1
            elif in_braces and c == "{":
                depth, i = depth + 1, i + 1
            elif in_braces and c == "}":
                if depth == 0:
                    return i + 1
                depth, i = depth - 1, i + 1
            else:
                i += 1
        return i

    code(0, False)
    return "".join(out)


def scan(path):
    with open(path, encoding="utf-8") as f:
        text = f.read()
    code = strip(text)
    lines = text.split("\n")
    hits = []
    for m in IDENT.finditer(code):
        parts = m.group(0).split(".")
        for tok in FORBIDDEN:
            if tok in parts:
                line = code.count("\n", 0, m.start()) + 1
                col = m.start() - (code.rfind("\n", 0, m.start()) + 1) + 1
                hits.append(f"{path}:{line}:{col}: {tok}: {lines[line - 1].strip()}")
    return hits


def main():
    if len(sys.argv) != 2:
        print(__doc__.strip(), file=sys.stderr)
        return 2
    hits = []
    for root, dirs, files in os.walk(sys.argv[1]):
        dirs[:] = sorted(d for d in dirs if d not in (".lake", ".check"))
        for name in sorted(files):
            if name.endswith(".lean"):
                hits += scan(os.path.join(root, name))
    for h in hits:
        print(h)
    return 1 if hits else 0


if __name__ == "__main__":
    sys.exit(main())
