#!/usr/bin/env python3
"""Remove the documentation links of the \\lean names from the web version of the blueprint.

    python3 blueprint/scripts/unlink_lean_decls.py [WEB_DIR]     (default: blueprint/web)

leanblueprint links every \\lean name to <dochome>/find/#doc/<name>, and <dochome> defaults to the
Mathlib documentation, which does not document this repository. The repository has no documentation
site (blueprint/README.md, "Links of Lean names"), so src/macros/web.tex sets \\dochome to DOCHOME, an
address under the reserved top-level domain .invalid, and this script, run by build.sh after
plasTeX, turns every link to DOCHOME into a <span> with the same class that carries the name as its
title. It exits with status 1 if a link to DOCHOME or to the Mathlib documentation remains in any
file of WEB_DIR. Running it twice changes nothing.
"""
import os, re, sys

DOCHOME = 'https://no-doc-site.invalid'
FORBIDDEN = (DOCHOME, 'mathlib4_docs')
ANCHOR = re.compile(r'<a\s([^>]*)>([^<]*)</a>')
HREF = re.compile(r'\s*href="' + re.escape(DOCHOME) + r'/find/#doc/([^"]*)"')


def unlink(m):
    attrs, text = ' ' + m.group(1), m.group(2)
    h = HREF.search(attrs)
    if h is None:
        return m.group(0)
    rest = HREF.sub('', attrs).rstrip()
    title = '' if h.group(1) == text.strip() else f' title="{h.group(1)}"'
    return f'<span{rest}{title}>{text}</span>'


def main(argv):
    web = argv[0] if argv else os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'web')
    if not os.path.isfile(os.path.join(web, 'index.html')):
        print(f'unlink_lean_decls: no {web}/index.html (build the web version first)', file=sys.stderr)
        return 2
    count, files, left = 0, 0, []
    for root, _, names in os.walk(web):
        for name in sorted(names):
            path = os.path.join(root, name)
            if not name.endswith(('.html', '.js', '.css', '.json', '.svg')):
                continue
            with open(path, encoding='utf-8') as f:
                text = f.read()
            n = sum(1 for m in ANCHOR.finditer(text) if HREF.search(' ' + m.group(1)))
            new = ANCHOR.sub(unlink, text)
            if n:
                with open(path, 'w', encoding='utf-8') as f:
                    f.write(new)
                count, files = count + n, files + 1
            left += [f'{os.path.relpath(path, web)}: {s}' for s in FORBIDDEN if s in new]
    print(f'unlink_lean_decls: unlinked {count} Lean name(s) in {files} file(s)')
    if left:
        print('unlink_lean_decls: documentation links remain:\n  ' + '\n  '.join(left), file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
