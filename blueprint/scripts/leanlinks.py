#!/usr/bin/env python3
"""Links of the blueprint to the Lean sources (README, section "Links to the Lean sources").

Every Lean name of the web version and of the pdf links to the lines of its declaration, and every
Lean file and source location to its file and line, on GitHub, at the revision the site documents:

  self       this repository (audit.toml [links] repository, or $BP_REPOSITORY_URL), at the commit
             the site is built from: $BP_COMMIT, else $GITHUB_SHA (CI), else `git rev-parse HEAD`;
  <package>  a package of lake-manifest.json (lean4lean, batteries), at its `url` and `rev`;
  lean4      Lean's own modules (Init, Std, Lean), audit.toml [links] lean4 at the tag of
             lean-toolchain, under src/.

A path belongs to the repository that audit.toml [links.roots] gives for its first component (or
for its root module file, `Lean4Lean.lean`); any other path belongs to this repository. A
declaration links to its declaration range, doc comment included, as the source links of doc-gen4
do: <file>#L<start>-L<end>, or <file>#L<start> for a declaration of one line.
src/generated/lean-locations.tsv, which `audit.py --update` writes from the Lean environment, gives
the repository, path and lines of every name the blueprint links; a path relative to the
repository's root (to src/lean/ of the toolchain for lean4).

scripts/bpkinds.py (the web version) and scripts/audit.py (its checks) use this module. For the
print version, which links the same URLs (macros/print.tex), build.sh runs

    python3 blueprint/scripts/leanlinks.py print-links OUT.tex

which writes the URL of every citation of the TeX sources (print_links).
"""
import json, os, re, subprocess, sys, tomllib

HERE = os.path.dirname(os.path.abspath(__file__))
BP = os.path.dirname(HERE)
REPO = os.path.dirname(BP)
LOCATIONS = os.path.join(BP, 'src', 'generated', 'lean-locations.tsv')
CONF = tomllib.load(open(os.path.join(BP, 'audit.toml'), 'rb'))['links']
SELF, LEAN4 = 'self', 'lean4'
GITHUB = 'https://github.com/'
# A citation of lines: 26, 7-13, 642,723,727.
LINES = re.compile(r'\d+(?:-\d+)?(?:,\d+(?:-\d+)?)*')


def commit():
    """The commit of this repository that the site documents."""
    for var in ('BP_COMMIT', 'GITHUB_SHA'):
        if os.environ.get(var):
            return os.environ[var]
    return subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=REPO, capture_output=True, text=True,
                          check=True).stdout.strip()


def toolchain_tag():
    """The tag of lean-toolchain (leanprover/lean4:v4.33.0-rc2 -> v4.33.0-rc2)."""
    line = open(os.path.join(REPO, 'lean-toolchain'), encoding='utf-8').read().strip()
    return line.split(':', 1)[1]


def packages():
    """name -> (GitHub URL, rev) of every package of lake-manifest.json."""
    manifest = json.load(open(os.path.join(REPO, 'lake-manifest.json'), encoding='utf-8'))
    out = {}
    for p in manifest['packages']:
        url = p.get('url', '').removesuffix('.git').rstrip('/')
        if not url.startswith(GITHUB):
            raise SystemExit(f'leanlinks: package {p["name"]} is not on GitHub ({url!r})')
        out[p['name']] = (url, p['rev'])
    return out


def bases():
    """repository -> (GitHub URL, revision) of every repository a link may point into."""
    out = {SELF: ((os.environ.get('BP_REPOSITORY_URL') or CONF['repository']).rstrip('/'), commit()),
           LEAN4: (CONF['lean4'].rstrip('/'), toolchain_tag())}
    for name, (url, rev) in packages().items():
        out[name] = (url, rev)
    for r in set(CONF['roots'].values()):
        if r not in out:
            raise SystemExit(f'leanlinks: [links.roots] names {r}, which is neither {LEAN4} nor a '
                             'package of lake-manifest.json')
    return out


def repo_of_path(path):
    """The repository of a path: [links.roots] of its first component, or of its root module
    file (Lean4Lean.lean), else this repository."""
    head = path.split('/', 1)[0]
    head = head.removesuffix('.lean') if '/' not in path else head
    return CONF['roots'].get(head, SELF)


class Links:
    """The URLs of the links: names (from lean-locations.tsv), files and lines."""

    def __init__(self, locations=LOCATIONS):
        self.bases = bases()
        self.decls = read_locations(locations)
        self.by_start = {(r, p, s): e for (r, p, s, e) in self.decls.values()}

    def blob(self, repo, path, tree=False):
        url, rev = self.bases[repo]
        sub = ('src/' if repo == LEAN4 else '') + path.rstrip('/')
        return f'{url}/{"tree" if tree else "blob"}/{rev}/{sub}'

    def decl(self, name):
        """(URL, where) of a name's declaration, where = path:start; None if it has no row."""
        row = self.decls.get(name)
        if row is None:
            return None
        repo, path, start, end = row
        return f'{self.blob(repo, path)}#{fragment(start, end)}', f'{path}:{start}'

    def file(self, path):
        """URL of a file, or of a directory when the path ends with a slash."""
        return self.blob(repo_of_path(path), path, tree=path.endswith('/'))

    def lines(self, path, spec):
        """[(text, URL)] for a citation of lines of a file: one link per number or range, a
        single line that starts a declaration linking to the whole declaration."""
        repo, base, out = repo_of_path(path), self.file(path), []
        for part in spec.split(','):
            a, _, b = part.partition('-')
            end = int(b) if b else self.by_start.get((repo, path, int(a)), int(a))
            out.append((part, f'{base}#{fragment(int(a), end)}'))
        return out


def fragment(start, end):
    """The fragment of a link to the lines start..end of a file: L7-L13, or L7 for one line."""
    return f'L{start}' if start == end else f'L{start}-L{end}'


def read_locations(path=LOCATIONS):
    """name -> (repository, path, start, end) from lean-locations.tsv."""
    out = {}
    if not os.path.exists(path):
        return out
    for line in open(path, encoding='utf-8'):
        if not line.strip() or line.startswith('#'):
            continue
        name, repo, p, start, end = line.rstrip('\n').split('\t')
        out[name] = (repo, p, int(start), int(end))
    return out


def write_locations(rows):
    """The text of lean-locations.tsv for rows name -> (repository, path, start, end)."""
    head = ('# Generated by blueprint/scripts/audit.py --update from the Lean environment. Do not '
            'edit.\n# name\trepository\tpath\tstart\tend: the declaration range of every Lean '
            'name the blueprint links\n# (scripts/leanlinks.py); the path is relative to the root '
            'of the repository (to src/lean/ of the toolchain for lean4).\n')
    return head + ''.join(f'{n}\t{r}\t{p}\t{s}\t{e}\n' for n, (r, p, s, e) in sorted(rows.items()))


def tex_arg(text):
    """The text of a path or line argument written in TeX: escapes and break hints removed."""
    text = re.sub(r'\\allowbreak\s*(\{\})?', '', text)
    text = re.sub(r'\\([_#&%$])\s?', r'\1', text)
    return re.sub(r'\s+', ' ', text).strip()


def print_links(links, cites):
    """The text of the table of URLs that the print version reads (macros/print.tex): \\bpdefurl
    {kind}{key}{URL} for every name of lean-locations.tsv (kind name), and for the citations cites,
    [(kind, value, lines)] as audit.citations gives them: the file of every \\leanfile,
    \\leanfiles, \\leanloc, \\leanlinesof and \\srcloc (kind file, key its path) and each line
    or range of the last four (kind lines, key path:lines), with the URLs of the web version."""
    rows = {('name', n): links.decl(n)[0] for n in links.decls}
    for kind, value, spec in cites:
        if kind == 'decl':
            continue
        rows[('file', value)] = links.file(value)
        if spec is not None:
            rows.update({('lines', f'{value}:{text}'): url for text, url in links.lines(value, spec)})
    for (kind, key), url in rows.items():
        if re.search(r'[{}\\\s]', key + url):
            raise SystemExit(f'leanlinks: the {kind} {key!r} or its URL {url!r} has a brace, a '
                             'backslash or a space')
    return ('% Generated by blueprint/scripts/leanlinks.py print-links (blueprint/build.sh pdf): the '
            'URLs of the citations\n% of the Lean sources, which the print version links '
            '(macros/print.tex). Do not edit.\n\\begingroup\n'
            '\\catcode`\\_=12 \\catcode`\\#=12 \\catcode`\\%=12 \\catcode`\\&=12 '
            '\\catcode`\\~=12 \\catcode`\\^=12 \\catcode`\\$=12\n'
            + ''.join(f'\\bpdefurl{{{kind}}}{{{key}}}{{{url}}}\n' for (kind, key), url in sorted(rows.items()))
            + '\\endgroup\n')


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] != 'print-links':
        raise SystemExit('usage: leanlinks.py print-links OUT.tex')
    sys.path.insert(0, HERE)
    import audit  # noqa: E402  (the citations of the TeX sources)
    cites = [(k, v, spec) for _, _, k, v, spec in audit.citations(audit.tex_texts())]
    os.makedirs(os.path.dirname(os.path.abspath(sys.argv[2])), exist_ok=True)
    with open(sys.argv[2], 'w', encoding='utf-8') as f:
        f.write(print_links(Links(), cites))
