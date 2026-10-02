#!/usr/bin/env python3
"""Mechanical audit of the blueprint against the Lean development and the registers.

Run from anywhere (it uses `lake` from PATH and the configuration blueprint/audit.toml):

    python3 blueprint/scripts/audit.py              # build, measure, check; exit 1 on a defect
    python3 blueprint/scripts/audit.py --no-build   # skip `lake build` (the targets are built)
    python3 blueprint/scripts/audit.py --update     # also rewrite the generated tables
    python3 blueprint/scripts/audit.py --print-imports   # print the expanded import list
    python3 blueprint/scripts/audit.py --check-lean-decls blueprint/lean_decls
        # check that the names plasTeX collected exist, except those of planned nodes
    python3 blueprint/scripts/audit.py --check-links blueprint/web
        # after build.sh web: check the links to the Lean sources of every page (check_links)

Checks, over the nodes (definition, lemma, proposition, theorem, corollary, imported) of
blueprint/src/chapters/*.tex and blueprint/src/generated/*.tex:

  * every node has a \\label, defined once, whose prefix matches its environment (def, lem, prop,
    thm, cor, imp) and which has no dot, prime or space;
  * every node carries a non-empty \\lean{...}, and no declaration is cited by two nodes;
  * every \\uses, and every \\ref of \\usedbystatements and \\usedbyproofs, resolves to a node; no
    node uses itself, and the \\uses graph is acyclic;
  * a proof environment follows its statement (never nested in it); a result node has one, a
    definition has none;
  * planned nodes (marked \\planned): none of their declarations exists (a declaration that exists
    is a defect: the node is no longer planned), and they carry no \\leanok, \\srcloc or
    \\inherited; a node that is not planned uses no planned node;
  * every declaration cited by a node that is not planned exists in the environment of the modules
    listed in audit.toml;
  * \\leanok in a statement iff the node is not planned, every cited declaration exists and its
    axioms are within the allowed set: the standard axioms of audit.toml, and sorryAx when every
    sorry source (a declaration of the closure whose own type or value uses sorryAx) is an
    inherited sorry source of audit.toml allowed for the node ("all"; "tests" for a test node;
    "module:M" for a node whose declarations all belong to the module M);
    \\leanok in the proof of a result node iff its statement has it;
  * \\inherited{...} lists exactly the labels of the inherited sorry sources the node's
    declarations depend on (absent when there are none);
  * \\srcloc{path}{line}, when present, is the file (relative to the repository root, or to the
    lean4lean package) and line of the node's first declaration;
  * coverage: every declaration a user wrote in the modules of `cover_prefix` (the verification
    library) is cited by a node that is not planned;
  * hygiene: no non-ASCII character outside \\lean{} and \\leandecl{}, no unescaped underscore in
    \\code{}, \\texttt{}, \\inherited{}, \\srcloc{} or the path of \\leanfile{}, \\leanfiles{},
    \\leanloc{}, \\leanlinesof{};
  * links to the Lean sources (scripts/leanlinks.py; README, "Links to the Lean sources"): every
    name that the web version links (location_rows) has a declaration range that holds it in the
    local source; every cited path and line exists (check_citations); no \\code or \\texttt of the
    chapters and generated tables cites a .lean file or a full declaration name; no \\dochome;
    generated/lean-locations.tsv is up to date;
  * present state only (STYLE.md section 1): no word of HISTORY_WORDS in the hand-written chapters
    and the generated tables, outside comments (the registers record changes and are exempt);
  * node kinds (scripts/kinds.py check): the names of a node share one layer, the module of every
    cited declaration has the layer of its name, the imported environment holds exactly the nodes
    of the lean4lean layer, exactly one node is the final theorem (a theorem environment), the
    final theorem depends on every milestone, the \\uses of the final theorem and of every
    milestone agree with the declarations they use directly (measured), and no node body carries
    a status word; the tables kinds.py writes are up to date;
  * the generated chapters are up to date: render_registers.py --check (registers, pins), and the
    tables this script writes with --update:
      generated/inherited-sorries.tex  the labelled lean4lean sorry sources, where they are, and the
                                       nodes that depend on each;
      generated/roots.tex              proof/ROOTS.txt: each root theorem must be cited by a
                                       formalized node, its planned consumer by a planned node
                                       that uses the root's node; a line whose unit is a plan
                                       decision (O-<n>) is a placeholder: its consumer's node must
                                       not use the root's node, and the table marks the row;
      generated/planned.tex            the planned nodes per chapter;
      generated/census-lean4lean.tex   the sorry sources and axioms of the inherited development;
      generated/census-shipping.tex    the partial, opaque, unsafe and monadic shipping code;
      generated/lean4lean-imports.tex  one imported node per lean4lean module that the proof
                                       library (outside its tests) or the shipping code uses
                                       directly: those declarations, the description of the
                                       module in audit.toml (checked: one entry per such module),
                                       \\leanok and \\inherited as measured, and the nodes whose
                                       declarations use them directly;
      generated/lean-locations.tsv     the repository, path and declaration range of every name
                                       the web version links (then the registers are rendered
                                       again, since they link the names it locates).

It reports the inherited trust: the census of the inherited development, and for every node the
inherited sorry sources and axioms it depends on; and the planned nodes, whose declarations are not
yet formalized. Output: blueprint/.audit/ (report.md, measure.json, the lake logs). Exit status 1
if a defect is found, 2 on a tool failure.
"""
import collections, glob, json, os, re, subprocess, sys, tomllib
from html.parser import HTMLParser

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
BP = os.path.join(REPO, 'blueprint')
OUT = os.path.join(BP, '.audit')
GEN = os.path.join(BP, 'src', 'generated')
CONF = tomllib.load(open(os.path.join(BP, 'audit.toml'), 'rb'))
STD = set(CONF['standard_axioms'])
INH = CONF['inherited_prefix']
SHIP = CONF['shipping_prefix']
COVER = CONF['cover_prefix']
TEST = CONF['test_prefix']
# Words that narrate history (STYLE.md section 1), matched as whole words, case-insensitively.
HISTORY_WORDS = ['previously', 'since the last version', 'was fixed', 'no longer', 'used to', 'now',
                 'yet']
# Generated chapters that render the registers, which record changes and are exempt.
REGISTERS = {'shipping-changes.tex', 'divergences.tex'}
ENV_DIR = os.path.join(REPO, CONF['env_dir'])
LABELS = {x['name']: x for x in CONF['inherited_sorry']}   # sorry source -> its entry
KINDS = ['definition', 'lemma', 'proposition', 'theorem', 'corollary', 'imported']
PREFIX = dict(definition='def', lemma='lem', proposition='prop', theorem='thm', corollary='cor',
              imported='imp')
RESULTS = {'lemma', 'proposition', 'theorem', 'corollary'}
MONADS = {'Lean.Meta.MetaM', 'Lean.Core.CoreM', 'Lean.Elab.Command.CommandElab',
          'Lean.Elab.Command.CommandElabM', 'Lean.Elab.Term.TermElabM', 'IO', 'EIO', 'BaseIO'}

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import render_registers  # noqa: E402
import kinds  # noqa: E402
import leanlinks  # noqa: E402


# ---------------------------------------------------------------- parsing the chapters

def args_of(macro, txt):
    """The comma-separated items of every \\macro{...} in txt (one level of braces inside)."""
    out = []
    for m in re.finditer(r'\\%s\{((?:[^{}]|\{[^{}]*\})*)\}' % macro, txt, re.S):
        out += [x.strip() for x in m.group(1).replace('\n', ' ').split(',') if x.strip()]
    return out


def refs_of(macro, txt):
    """The labels of the \\ref commands inside every \\macro{...} of txt."""
    out = []
    for m in re.finditer(r'\\%s\{((?:[^{}]|\{[^{}]*\})*)\}' % macro, txt, re.S):
        out += re.findall(r'\\ref\{([^}]*)\}', m.group(1))
    return out


def unescape(s):
    return s.replace('\\_', '_').replace('\\#', '#').replace('\\&', '&')


def tex_sources():
    return sorted(glob.glob(os.path.join(BP, 'src', 'chapters', '*.tex'))) + \
        sorted(glob.glob(os.path.join(GEN, '*.tex')))


def parse(defects):
    nodes = []
    node_re = re.compile(r'\\begin\{(%s)\}(.*?)\\end\{\1\}' % '|'.join(KINDS), re.S)
    proof_re = re.compile(r'\\begin\{proof\}(.*?)\\end\{proof\}', re.S)
    for path in tex_sources():
        name = os.path.relpath(path, os.path.join(BP, 'src'))
        raw = open(path, encoding='utf-8').read()
        # \lean{...} may span lines: blank its contents (and those of \leandecl{...}, a Lean name
        # too), keeping the line breaks
        masked = re.sub(r'\\lean(?:decl)?\{[^}]*\}', lambda m: re.sub(r'[^\n]', ' ', m.group(0)), raw)
        for i, line in enumerate(raw.split('\n'), 1):
            if any(ord(c) > 127 for c in masked.split('\n')[i - 1]):
                defects[name].append(f'L{i}: non-ASCII character outside \\lean{{}}')
            for m in re.finditer(r'\\(code|texttt|inherited|srcloc|leanfiles?|leanloc|leanlinesof)'
                                 r'\{((?:[^{}]|\{[^{}]*\})*)\}', line):
                bare = re.sub(r'\\ensuremath\{[^{}]*\}|(?<!\\)\$[^$]*\$', '', m.group(2))
                if re.search(r'(?<!\\)_', bare):
                    defects[name].append(f'L{i}: unescaped underscore in \\{m.group(1)}{{{m.group(2)[:50]}}}')
        txt = re.sub(r'(?<!\\)%.*', '', raw)
        events = sorted([(m.start(), 'node', m) for m in node_re.finditer(txt)] +
                        [(m.start(), 'proof', m) for m in proof_re.finditer(txt)], key=lambda e: e[0])
        last = None
        for pos, what, m in events:
            line = txt.count('\n', 0, pos) + 1
            if what == 'node':
                body = m.group(2)
                if '\\begin{proof}' in body:
                    defects[name].append(f'L{line}: proof nested inside a {m.group(1)} (it must follow it)')
                labels = re.findall(r'\\label\{([^}]*)\}', body)
                src = re.search(r'\\srcloc\{([^}]*)\}\{([^}]*)\}', body)
                title = re.match(r'\s*\[((?:[^\[\]{}]|\{(?:[^{}]|\{[^{}]*\})*\})*)\]', body)
                last = dict(file=name, line=line, kind=m.group(1), label=labels[0] if labels else None,
                            title=title.group(1) if title else '',
                            status_words=re.findall(r'\\st(?:Proved|Inherited|Shipping|Planned|Open)\b',
                                                    body),
                            used_by=refs_of('usedbystatements', body),
                            used_by_proof=refs_of('usedbyproofs', body),
                            lean=args_of('lean', body), leanok=bool(re.search(r'\\leanok\b', body)),
                            uses=args_of('uses', body),
                            inherited=[unescape(x) for x in args_of('inherited', body)],
                            has_inherited='\\inherited{' in body,
                            planned=bool(re.search(r'\\planned\b', body)),
                            srcloc=(unescape(src.group(1)), src.group(2).strip()) if src else None,
                            proof=False, proof_leanok=False, proof_uses=[])
                nodes.append(last)
                continue
            if last is None:
                defects[name].append(f'L{line}: proof environment with no node before it')
                continue
            if last['proof']:
                defects[name].append(f'L{line}: second proof after {last["label"]}')
                continue
            last.update(proof=True, proof_leanok=bool(re.search(r'\\leanok\b', m.group(1))),
                        proof_uses=args_of('uses', m.group(1)))
    return nodes


def cycles(graph):
    sys.setrecursionlimit(100000)
    index, low, stack, on, found, counter = {}, {}, [], set(), [], [0]

    def visit(v):
        index[v] = low[v] = counter[0]
        counter[0] += 1
        stack.append(v)
        on.add(v)
        for w in graph.get(v, ()):
            if w not in index:
                visit(w)
                low[v] = min(low[v], low[w])
            elif w in on:
                low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            comp = []
            while True:
                w = stack.pop()
                on.discard(w)
                comp.append(w)
                if w == v:
                    break
            if len(comp) > 1:
                found.append(comp)
    for v in list(graph):
        if v not in index:
            visit(v)
    return found


# ---------------------------------------------------------------- the Lean side

def package_roots():
    roots = [REPO, ENV_DIR]
    roots += sorted(glob.glob(os.path.join(REPO, '.lake', 'packages', '*')))
    return list(dict.fromkeys(roots))


def expand_imports():
    mods = []
    for spec in CONF['imports']:
        if not spec.endswith('.*'):
            mods.append(spec)
            continue
        base = spec[:-2]
        rel = base.replace('.', os.sep)
        found = False
        for root in package_roots():
            if os.path.exists(os.path.join(root, rel + '.lean')):
                mods.append(base)
                found = True
            d = os.path.join(root, rel)
            if os.path.isdir(d):
                for f in sorted(glob.glob(os.path.join(d, '**', '*.lean'), recursive=True)):
                    mods.append(os.path.relpath(f, root)[:-5].replace(os.sep, '.'))
                    found = True
            if found:
                break
        if not found:
            raise SystemExit(f'audit: import pattern {spec} matches no module')
    return list(dict.fromkeys(mods))


def run_lake(args, log, cwd=REPO, env=None):
    with open(os.path.join(OUT, log), 'w', encoding='utf-8') as f:
        r = subprocess.run(['lake'] + args, cwd=cwd, stdout=f, stderr=subprocess.STDOUT, text=True,
                           env=env)
    return r.returncode


def check_decls(names_file):
    """CheckDecls.lean check, in env_dir, on names_file (one name per line)."""
    os.makedirs(OUT, exist_ok=True)
    return run_lake(['env', 'lean', '--run', os.path.join(BP, 'CheckDecls.lean'), 'check',
                     os.path.abspath(names_file)] + expand_imports(), 'lake-checkdecls.log', ENV_DIR)


def measure(names, build, locate=()):
    """CheckDecls.lean measure on the names (and, for their locations only, the names locate),
    after `lake build` of the targets of audit.toml when build."""
    os.makedirs(OUT, exist_ok=True)
    if build:
        for i, b in enumerate(CONF['build']):
            log = f'lake-build-{i}.log'
            if run_lake(['build'] + b['targets'], log, os.path.join(REPO, b['dir'])) != 0:
                raise SystemExit(f'audit: lake build in {b["dir"]} failed, see blueprint/.audit/{log}')
    with open(os.path.join(OUT, 'names.txt'), 'w', encoding='utf-8') as f:
        f.write(''.join(n + '\n' for n in names))
    with open(os.path.join(OUT, 'locate.txt'), 'w', encoding='utf-8') as f:
        f.write(''.join(n + '\n' for n in sorted(set(locate))))
    env = dict(os.environ, BP_INHERITED_PREFIX=INH, BP_SHIPPING_PREFIX=SHIP, BP_COVER_PREFIX=COVER,
               BP_LOCATE=os.path.join(OUT, 'locate.txt'))
    out = os.path.join(OUT, 'measure.json')
    if run_lake(['env', 'lean', '--run', os.path.join(BP, 'CheckDecls.lean'), 'measure',
                 os.path.join(OUT, 'names.txt'), out] + expand_imports(),
                'lake-measure.log', ENV_DIR, env) != 0:
        raise SystemExit('audit: measuring failed, see blueprint/.audit/lake-measure.log')
    return json.load(open(out, encoding='utf-8'))


def module_path(module):
    """The source file of a module: relative to the repository root for the root and proof
    packages, relative to the package for the packages under .lake/packages."""
    rel = module.replace('.', '/') + '.lean'
    for root in package_roots():
        if os.path.exists(os.path.join(root, rel)):
            return os.path.relpath(os.path.join(root, rel), REPO) if root in (REPO, ENV_DIR) else rel
    return rel


# ---------------------------------------------------------------- generated tables

def tt(s):
    """Escaped code text, with break opportunities after dots, slashes and underscores."""
    return render_registers.esc(s, 'census', code=True).replace('.', r'.\allowbreak{}')


ALLOWED_TEXT = {'all': 'every node', 'tests': 'test nodes', 'none': 'no node'}


def allowed_text(allowed):
    """The column "Allowed for" of the inherited-sorry table."""
    if allowed.startswith('module:'):
        return f'the nodes of module \\code{{{tt(allowed[len("module:"):])}}}'
    return ALLOWED_TEXT[allowed]


def inherited_table(data, reach, defects):
    """The labelled lean4lean sorry sources of audit.toml: where they are, which nodes may depend
    on them, and how many do."""
    where = {c['name']: c for c in data['census'] if c['package'] == 'inherited' and c['sorry']}
    rows = []
    for x in CONF['inherited_sorry']:
        c = where.get(x['name'])
        if c is None:
            defects['audit.toml'].append(f'inherited_sorry {x["label"]}: {x["name"]} is not a sorry '
                                         'source of the environment')
            loc = '--'
        else:
            loc = f'\\leanloc{{{tt(module_path(c["module"]))}}}{{{c["line"]}}}'
        rows.append(f'{x["label"]} & \\leandecl{{{x["name"]}}}, {loc} & {render_registers.esc(x["what"], "audit.toml")} & '
                    f'{allowed_text(x["allowed"])} & {len(reach.get(x["label"], []))} \\\\')
    return ('% Generated by blueprint/scripts/audit.py --update from blueprint/audit.toml and the Lean '
            'environment. Do not edit.\n'
            + render_registers.table('lp{0.36\\linewidth}p{0.28\\linewidth}p{0.1\\linewidth}r',
                                     'Label & Declaration and location & What it is & Allowed for & Nodes',
                                     rows))


PLACEHOLDER = re.compile(r'O-\d+')


def roots_table(nodes, defects):
    """proof/ROOTS.txt (the no-leaves register of the proof package): each landed root theorem, the
    planned declaration that will use it, and the unit that lands it. A root must be cited by a
    formalized node, its consumer by a planned node (or be FINAL). A line whose unit is a decision
    of the plan (O-<n>) names a placeholder consumer: no planned statement uses the root, so the
    consumer's node must not use the root's node, and the row is marked."""
    owner = {d: n for n in nodes for d in n['lean']}
    rows = []
    path = os.path.join(REPO, CONF['roots_file'])
    for i, line in enumerate(open(path, encoding='utf-8'), 1):
        line = line.strip()
        if not line or line.startswith('#'):
            continue
        parts = line.split()
        decl, consumer, unit = parts[0], parts[1], (parts[2] if len(parts) > 2 else '')
        a, b = owner.get(decl), owner.get(consumer)
        where = f'{CONF["roots_file"]}:{i}'
        placeholder = bool(PLACEHOLDER.fullmatch(unit))
        uses = a is not None and b is not None and a['label'] in b['uses'] + b['proof_uses']
        if a is None or a['planned']:
            defects['roots'].append(f'{where}: root {decl} is cited by no formalized node')
        if consumer != 'FINAL' and (b is None or not b['planned']):
            defects['roots'].append(f'{where}: consumer {consumer} is cited by no planned node')
        elif placeholder and uses:
            defects['roots'].append(f'{where}: placeholder line ({unit}), but the node {b["label"]} of '
                                    f'the consumer uses the node {a["label"]} of the root: name its unit')
        elif not placeholder and a is not None and b is not None and not uses:
            defects['roots'].append(f'{where}: the node {b["label"]} of the consumer does not use the '
                                    f'node {a["label"]} of the root')
        ref = lambda n: f' (\\ref{{{n["label"]}}})' if n else ''
        # a declaration that exists links to its source (\leandecl); a planned one does not
        cite = lambda d, n: (f'\\leandecl{{{d}}}' if n is not None and not n['planned']
                             else f'\\code{{{tt(d)}}}')
        cons = ('none (\\code{FINAL}: the final theorem)' if consumer == 'FINAL'
                else f'{cite(consumer, b)}{ref(b)}')
        rows.append(f'{cite(decl, a)}{ref(a)} & {cons} & '
                    f'{tt(unit)}{" (placeholder)" if placeholder else ""} \\\\')
    return ('% Generated by blueprint/scripts/audit.py --update from ' + CONF['roots_file']
            + '. Do not edit.\n'
            + render_registers.table('p{0.37\\linewidth}p{0.37\\linewidth}p{0.18\\linewidth}',
                                     'Root theorem & Planned consumer & Unit', rows))


def planned_table(nodes):
    """The planned nodes (not yet formalized), per chapter."""
    by_file = collections.OrderedDict()
    for n in nodes:
        if n['planned']:
            by_file.setdefault(n['file'], []).append(n)
    order = [x + '.tex' for x in re.findall(r'\\input\{([^}]*)\}',
                                            open(os.path.join(BP, 'src', 'content.tex'), encoding='utf-8').read())]
    rows = []
    for f, ns in sorted(by_file.items(), key=lambda kv: order.index(kv[0]) if kv[0] in order else len(order)):
        m = re.search(r'\\label\{(chap:[^}]*)\}', open(os.path.join(BP, 'src', f), encoding='utf-8').read())
        chap = f'\\ref{{{m.group(1)}}}' if m else tt(f)
        defs = sum(1 for n in ns if n['kind'] == 'definition')
        rows.append(f'{chap} & {defs} & {len(ns) - defs} & ' + ', '.join(f'\\ref{{{n["label"]}}}' for n in ns)
                    + ' \\\\')
    head = '% Generated by blueprint/scripts/audit.py --update from the chapters. Do not edit.\n'
    if not rows:
        return head + 'No node is planned.\n'
    return head + render_registers.table('lrrp{0.62\\linewidth}', 'Chapter & Definitions & Results & Nodes',
                                         rows)


def census_lean4lean(data, reached):
    rows = [c for c in data['census'] if c['package'] == 'inherited']
    sorries = [c for c in rows if c['sorry']]
    axioms = [c for c in rows if c['axiom']]
    by_mod = collections.defaultdict(list)
    for a in axioms:
        by_mod[a['module']].append(a['name'])
    out = ['% Generated by blueprint/scripts/audit.py --update from the Lean environment. Do not edit.\n',
           f'\\begin{{itemize}}\n\\item \\lead{{Libraries}} the modules {tt(", ".join([m for m in CONF["imports"] if m.startswith(INH)]))} of '
           f'the pinned lean4lean ({len(sorries)} sorry sources, {len(axioms)} axioms).\n',
           '\\item \\lead{Sorry source} a declaration whose own type or value uses \\code{sorryAx}.\n',
           '\\item \\lead{Reached} the blueprint nodes depend on '
           + (', '.join(f'\\leandecl{{{x}}}' for x in reached) if reached else 'none of them') + '.\n'
           '\\end{itemize}\n\n',
           render_registers.table(
               'p{0.45\\linewidth}p{0.36\\linewidth}l', 'Sorry source & Location & Kind',
               [f'\\leandecl{{{c["name"]}}} & \\leanloc{{{tt(module_path(c["module"]))}}}{{{c["line"]}}} & '
                f'{tt(c["kind"])} \\\\' for c in sorries]),
           render_registers.table(
               'p{0.3\\linewidth}rp{0.55\\linewidth}', 'File & Axioms & Names',
               [f'\\leanfile{{{tt(module_path(mod))}}} & {len(by_mod[mod])} & '
                + ', '.join(f'\\leandecl{{{n}}}' for n in sorted(by_mod[mod])) + ' \\\\'
                for mod in sorted(by_mod)])]
    return ''.join(out)


def census_shipping(data):
    ship = data['shipping']
    shown = [s for s in ship if s['kind'] not in ('def', 'theorem', 'structure', 'inductive')
             or s['result'] in MONADS]
    shown.sort(key=lambda s: (s['module'], s['line'] if s['line'] is not None else 10**9, s['name']))
    own = [c for c in data['census'] if c['package'] == 'shipping']
    kinds = collections.Counter(s['kind'] for s in shown)
    out = ['% Generated by blueprint/scripts/audit.py --update from the Lean environment. Do not edit.\n',
           '\\begin{itemize}\n',
           f'\\item \\lead{{Rows}} the declarations of the modules \\code{{{tt(SHIP)}*}} that are '
           'partial, opaque or unsafe, or whose result type is a monad of the elaborator or of IO: '
           + ', '.join(f'{n} {tt(k)}' for k, n in sorted(kinds.items())) + '.\n',
           '\\item \\lead{Partial def} an opaque constant for the kernel: no proof can unfold it.\n',
           f'\\item \\lead{{Axioms and sorry}} {len(own)} declarations of these modules are axioms or '
           'use \\code{sorryAx}.\n',
           '\\end{itemize}\n\n']
    rows = []
    for s in shown:
        loc = (f'\\leanloc{{{tt(module_path(s["module"]))}}}{{{s["line"]}}}' if s['line'] is not None
               else f'\\leanfile{{{tt(module_path(s["module"]))}}}')
        result = (f'\\leandecl{{{s["result"]}}}' if s['result'] not in ('', 'Sort')
                  else f'\\code{{{tt(s["result"])}}}')
        rows.append(f'\\leandecl{{{s["name"]}}} & {tt(s["kind"])} & {result} & {loc} \\\\')
    out.append(render_registers.table('p{0.34\\linewidth}p{0.14\\linewidth}p{0.2\\linewidth}p{0.22\\linewidth}',
                                      'Declaration & Kind & Result & Location', rows))
    return ''.join(out)


KIND_WORDS = [('def', 'definition'), ('theorem', 'theorem'), ('inductive', 'inductive type'),
              ('structure', 'structure')]


def counted(n, word):
    return f'{n} {word}' + ('' if n == 1 else 's')


def wrapped(items, first, width=99, indent='    ', sep=', '):
    """items joined by sep, broken into lines of at most width characters; the first line follows
    a prefix of first characters, the others start with indent."""
    lines, cur = [], ''
    for x in items:
        part = (sep if cur else '') + x
        if cur and (first if not lines else len(indent)) + len(cur) + len(part) + 1 > width:
            lines.append(cur + sep.rstrip())
            cur = x
        else:
            cur += part
    lines.append(cur)
    return ('\n' + indent).join(lines)


def imported_uses(nodes, data):
    """The declarations of the inherited modules that the declarations of the proof library outside
    its tests, or of the shipping code, use directly (data['deps']): name -> {label: how} of the
    nodes whose declarations use it, how = 'statement' when a definition node or the type of a
    result's declaration uses it, 'proof' otherwise."""
    decls = data['decls']
    owner = {d: n for n in nodes for d in n['lean']}
    out = collections.defaultdict(dict)
    for user, targets in data['deps'].items():
        if user.startswith(TEST):
            continue
        n = owner.get(user)
        for t, where in targets:
            if not decls[t]['module'].startswith(INH):
                continue
            used = out[t]
            if n is None or n['planned'] or not n['label']:
                continue
            how = 'statement' if n['kind'] == 'definition' or where == 'type' else 'proof'
            if used.get(n['label']) != 'statement':
                used[n['label']] = how
    return out


def lean4lean_imports(nodes, data, defects):
    """generated/lean4lean-imports.tex: one imported node per lean4lean module whose declarations
    the proof library (outside its tests) or the shipping code uses directly, in the order of
    audit.toml's [lean4lean_modules]."""
    decls, names = data['decls'], data['names']
    uses = imported_uses(nodes, data)
    by_module = collections.defaultdict(list)
    for t in uses:
        by_module[decls[t]['module']].append(t)
    described = CONF.get('lean4lean_modules', {})
    for m in sorted(set(by_module) - set(described)):
        defects['audit.toml'].append(f'[lean4lean_modules]: no entry for {m}, whose declarations '
                                     f'{", ".join(sorted(by_module[m])[:3])} are used directly')
    for m in sorted(set(described) - set(by_module)):
        defects['audit.toml'].append(f'[lean4lean_modules]: {m} has an entry, but no declaration of '
                                     'it is used directly')
    order = {lab: i for i, lab in enumerate(kinds.document_order(nodes))}
    out = ['% Generated by blueprint/scripts/audit.py --update from blueprint/audit.toml and the Lean '
           'environment. Do not edit.\n']
    for m in [m for m in described if m in by_module] + sorted(set(by_module) - set(described)):
        ds = sorted(by_module[m], key=lambda t: (decls[t]['line'] or 0, t))
        fp = footprint(dict(lean=ds), names)
        if not fp['ok']:
            defects['generated/lean4lean-imports.tex'].append(
                f'{m}: its declarations used directly are outside the allowed set (missing '
                f'{fp["missing"]}, axioms {fp["bad_axioms"]}, sorry sources {fp["bad_sorry"]})')
        kinds_count = collections.Counter(decls[t]['kind'] for t in ds)
        words = [counted(kinds_count.pop(k), w) for k, w in KIND_WORDS if kinds_count.get(k)]
        words += [counted(c, k) for k, c in sorted(kinds_count.items())]
        users = collections.defaultdict(set)
        for t in ds:
            for lab, how in uses[t].items():
                users[lab].add(how)
        stmt = sorted((lab for lab, hows in users.items() if 'statement' in hows), key=order.get)
        proof = sorted((lab for lab, hows in users.items() if 'statement' not in hows), key=order.get)
        out.append(f'\n\\begin{{imported}}[\\code{{{m}}}]\n'
                   f'  \\label{{imp:{m.replace(".", "-")}}}\n'
                   f'  \\lean{{{wrapped(ds, 8)}}}\n'
                   + ('  \\leanok\n' if fp['ok'] else '')
                   + f'  \\srcloc{{{module_path(m)}}}{{{decls[ds[0]]["line"]}}}\n'
                   + (f'  \\inherited{{{", ".join(fp["inherited"])}}}\n' if fp['inherited'] else '')
                   + f'  \\lead{{In short}} {wrapped(described.get(m, "--").split(), 18, indent="  ", sep=" ")}\n'
                   f'  \\lead{{Used directly}} {counted(len(ds), "declaration")}: {", ".join(words)}.\n'
                   + (f'  \\usedbystatements{{{wrapped([f"\\ref{{{x}}}" for x in stmt], 20)}}}\n'
                      if stmt else '')
                   + (f'  \\usedbyproofs{{{wrapped([f"\\ref{{{x}}}" for x in proof], 16)}}}\n'
                      if proof else '')
                   + '\\end{imported}\n')
    return ''.join(out)


# ---------------------------------------------------------------- links to the Lean sources

ARG = r'\{((?:[^{}]|\{[^{}]*\})*)\}'


def strip_comments(text):
    return re.sub(r'(?<!\\)%.*', '', text)


def tex_texts():
    """The TeX sources (chapters and generated files), by path relative to blueprint/src."""
    return {os.path.relpath(p, os.path.join(BP, 'src')): open(p, encoding='utf-8').read()
            for p in tex_sources()}


def citations(texts):
    """What the TeX sources cite of the Lean sources: [(file, line, kind, value, lines)], kind
    'decl' (\\leandecl{name}), 'file' (\\leanfile{path}, each file of \\leanfiles{dir}{A, B}) or
    'lines' (\\srcloc, \\leanloc, \\leanlinesof: a path and lines)."""
    out = []
    for f, raw in sorted(texts.items()):
        txt = strip_comments(raw)
        at = lambda m: txt.count('\n', 0, m.start()) + 1
        for m in re.finditer(r'\\leandecl\{([^{}]*)\}', txt):
            out.append((f, at(m), 'decl', m.group(1).strip(), None))
        for m in re.finditer(r'\\leanfile' + ARG, txt):
            out.append((f, at(m), 'file', leanlinks.tex_arg(m.group(1)), None))
        for m in re.finditer(r'\\leanfiles' + ARG + r'\{([^{}]*)\}', txt):
            d = leanlinks.tex_arg(m.group(1))
            out += [(f, at(m), 'file', d + leanlinks.tex_arg(x) + '.lean', None)
                    for x in m.group(2).split(',')]
        for m in re.finditer(r'\\(?:srcloc|leanloc|leanlinesof)' + ARG + r'\{([^{}]*)\}', txt):
            out.append((f, at(m), 'lines', leanlinks.tex_arg(m.group(1)), m.group(2).strip()))
    return out


def link_names(nodes, texts):
    """The Lean names the web version links to their declarations: those of the nodes that are
    not planned, of \\leandecl outside the registers, and the labelled lean4lean sorries (the
    graphs draw them). The registers cite the names of render_registers.decl_candidates() that
    are declarations (location_rows)."""
    names = {d for n in nodes if not n['planned'] for d in n['lean']}
    names |= {v for f, _, k, v, _ in citations(texts)
              if k == 'decl' and os.path.basename(f) not in REGISTERS}
    return names | set(LABELS)


def local_root(repo, sysroot):
    """The local tree of a repository of leanlinks: this checkout, a package checkout under
    .lake/packages, or src/lean of the toolchain."""
    if repo == leanlinks.SELF:
        return REPO
    if repo == leanlinks.LEAN4:
        return os.path.join(sysroot, 'src', 'lean')
    return os.path.join(REPO, '.lake', 'packages', repo)


def module_source(module, sysroot):
    """(repository, path) of the source file of a module, or None."""
    rel = module.replace('.', '/') + '.lean'
    roots = [(leanlinks.SELF, REPO), (leanlinks.SELF, ENV_DIR)]
    roots += [(name, local_root(name, sysroot)) for name in leanlinks.packages()]
    roots.append((leanlinks.LEAN4, local_root(leanlinks.LEAN4, sysroot)))
    for repo, root in roots:
        if os.path.isfile(os.path.join(root, rel)):
            path = os.path.relpath(os.path.join(root, rel), local_root(repo, sysroot))
            return repo, path.replace(os.sep, '/')
    return None


_LINES = {}


def file_lines(path):
    if path not in _LINES:
        _LINES[path] = open(path, encoding='utf-8').read().split('\n')
    return _LINES[path]


def holds(name, lines, r):
    """Whether the declaration range r (CheckDecls.lean locationJson) of name holds it in a file
    of these lines: the text at the range of its name is the name of the declaration or of one it
    belongs to (a prefix of its name, as the axioms that bv_decide adds belong to their theorem),
    written as a suffix of the full name (`_root_.` dropped), or, for an instance whose name Lean
    chose (inst...), the keyword `instance` or the class of a `deriving` clause."""
    if r['sel_line'] != r['sel_end_line'] or not r['start'] <= r['sel_line'] <= r['end'] <= len(lines):
        return False
    t = lines[r['sel_line'] - 1][r['sel_col']:r['sel_end_col']].removeprefix('_root_.')
    parts = name.split('.')
    for k in range(len(parts), 0, -1):
        p, last = '.'.join(parts[:k]), parts[k - 1]
        if p == t or p.endswith('.' + t) or last.startswith('inst') and (t == 'instance' or bool(t) and t in last):
            return True
    return False


def location_rows(data, wanted, defects, optional=()):
    """The rows of lean-locations.tsv: name -> (repository, path, start, end), for the names
    wanted, and those of the names optional that are declarations with a declaration range, from
    the ranges that CheckDecls.lean measured; each checked against the local source: the file
    exists and the range holds the declaration (holds)."""
    rows, sysroot = {}, data['sysroot']
    for n in sorted(set(wanted) | set(optional)):
        loc = data['locations'].get(n)
        if n not in wanted and (loc is None or loc['ranges'] is None):
            continue
        if loc is None or loc['ranges'] is None:
            defects['links'].append(f'{n}: ' + ('not a declaration of the environment' if loc is None
                                                else 'Lean recorded no declaration range')
                                    + ', so it cannot link to its source')
            continue
        src = module_source(loc['module'], sysroot)
        if src is None:
            defects['links'].append(f'{n}: no source file of its module {loc["module"]}')
            continue
        repo, path = src
        if leanlinks.repo_of_path(path) != repo:
            defects['links'].append(f'{n}: {path} is a file of {repo}, but [links.roots] of '
                                    f'audit.toml gives {leanlinks.repo_of_path(path)}')
            continue
        r = loc['ranges']
        lines = file_lines(os.path.join(local_root(repo, sysroot), path))
        if not holds(n, lines, r):
            defects['links'].append(f'{n}: {path}:{r["start"]}-{r["end"]} does not hold the '
                                    f'declaration (Lean and the source tree disagree: rebuild)')
            continue
        rows[n] = (repo, path, r['start'], r['end'])
    return rows


def tracked_files(rev='HEAD'):
    out = subprocess.run(['git', 'ls-tree', '-r', '--name-only', rev], cwd=REPO, capture_output=True,
                         text=True, check=True).stdout
    return set(out.split('\n')) - {''}


def check_citations(texts, known, sysroot, defects):
    """Every path and line that the TeX sources cite (citations) is a file (or, ending with a
    slash, a directory) of its repository, tracked by git in this repository, and every line is
    one of the file; a \\code or \\texttt of the chapters and of the generated tables (not the
    registers, whose rendering decides it) cites no .lean file, and no full name of a declaration
    the blueprint knows (known), which \\leanfile, \\leanfiles and \\leandecl link; no \\dochome."""
    tracked = tracked_files()
    for f, line, kind, value, spec in citations(texts):
        if kind == 'decl':
            continue
        repo = leanlinks.repo_of_path(value)
        local = os.path.join(local_root(repo, sysroot), value)
        where = f'{f} L{line}: {value}'
        if value.endswith('/'):
            ok = os.path.isdir(local) and (repo != leanlinks.SELF or any(t.startswith(value) for t in tracked))
        else:
            ok = os.path.isfile(local) and (repo != leanlinks.SELF or value in tracked)
        if not ok:
            defects['links'].append(f'{where} is not a {"directory" if value.endswith("/") else "file"} '
                                    f'of {repo}' + (' tracked by git' if repo == leanlinks.SELF else ''))
            continue
        if spec is not None:
            if not leanlinks.LINES.fullmatch(spec):
                defects['links'].append(f'{where}: lines {spec!r} are not a list of lines and ranges')
                continue
            n = len(file_lines(local))
            for part in spec.split(','):
                a, _, b = part.partition('-')
                if not 1 <= int(a) <= int(b or a) <= n:
                    defects['links'].append(f'{where}: line {part} is not a line of the file ({n} lines)')
    for f, raw in sorted(texts.items()):
        if os.path.basename(f) in REGISTERS:
            continue
        txt = strip_comments(raw)
        for m in re.finditer(r'\\(code|texttt)' + ARG, txt):
            v = leanlinks.tex_arg(m.group(2))
            where = f'{f} L{txt.count(chr(10), 0, m.start()) + 1}'
            if re.search(r'\.lean\b', v):
                defects['links'].append(f'{where}: \\{m.group(1)}{{{v}}} cites a Lean file: write '
                                        '\\leanfile{path} or \\leanfiles{dir}{A, B}')
            elif '.' in v and v in known:
                defects['links'].append(f'{where}: \\{m.group(1)}{{{v}}} cites a declaration: write '
                                        f'\\leandecl{{{v}}}')
    for path in sorted(glob.glob(os.path.join(BP, 'src', '**', '*.tex'), recursive=True)):
        if '\\dochome' in strip_comments(open(path, encoding='utf-8').read()):
            defects['links'].append(f'{os.path.relpath(path, os.path.join(BP, "src"))}: \\dochome: the '
                                    'Lean names link to their sources (scripts/leanlinks.py), not to '
                                    'a documentation site')


def toolchain_prefix():
    """The toolchain directory of env_dir (`lean --print-prefix`) and its `lean --version`."""
    def lean(*args):
        r = subprocess.run(['lake', 'env', 'lean', *args], cwd=ENV_DIR, capture_output=True, text=True)
        if r.returncode != 0:
            raise SystemExit(f'audit: lake env lean {" ".join(args)} failed:\n{r.stdout}{r.stderr}')
        return r.stdout.strip()
    return lean('--print-prefix'), lean('--version')


class _Anchors(HTMLParser):
    """The <a> elements of a page and the elements that carry a Lean name (data-lean, or the
    class lean_decl), with their text."""

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.found, self.open = [], []

    def handle_starttag(self, tag, attrs):
        a = {k: v or '' for k, v in attrs}
        if tag == 'a' or 'data-lean' in a or 'lean_decl' in a.get('class', '').split():
            self.found.append(dict(tag=tag, attrs=a, line=self.getpos()[0], text=''))
            self.open.append((tag, self.found[-1]))

    def handle_endtag(self, tag):
        if self.open and self.open[-1][0] == tag:
            self.open.pop()

    def handle_data(self, data):
        for _, el in self.open:
            el['text'] += data


FORBIDDEN = ('no-doc-site.invalid', 'mathlib4_docs', '/find/#doc/')


def mentions(name, body):
    """Whether the text of a declaration range mentions the last component of the name or of a
    prefix of it (the declaration it belongs to, as for holds), or, for an instance whose name
    Lean chose, `instance` or `deriving`."""
    for last in reversed(name.split('.')):
        if last in body or last.startswith('inst') and ('instance' in body or 'deriving' in body):
            return True
    return False


def check_links(web):
    """After build.sh web: every Lean name, Lean file and source location of the web version is a
    link to its source, of the form leanlinks.py gives (README, "Links to the Lean sources"):
    a GitHub URL at the revision of its repository (this repository at the commit the site
    documents, a package at its rev of lake-manifest.json, Lean at the tag of lean-toolchain); the
    file exists at that revision (in git for this repository, in the package checkout or the
    toolchain of the same revision otherwise); its lines are lines of the file; a Lean name links
    to its row of lean-locations.tsv and the lines hold its name. No page links to the placeholder
    of a documentation site or to the Mathlib documentation. Every name of a node that is not
    planned is a link on its chapter page and on the graph of all nodes. Prints the links by
    repository and kind; exit status 1 on a defect."""
    links = leanlinks.Links()
    defects, count, names_linked = [], collections.Counter(), collections.defaultdict(set)
    sysroot, version = toolchain_prefix()
    tag = leanlinks.toolchain_tag()
    if tag.removeprefix('v') not in version:
        defects.append(f'the toolchain of {CONF["env_dir"]} is {version}, not {tag} of lean-toolchain')
    for name, (url, rev) in leanlinks.packages().items():
        r = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=local_root(name, sysroot),
                           capture_output=True, text=True)
        if r.stdout.strip() != rev:
            defects.append(f'.lake/packages/{name} is at {r.stdout.strip() or "?"}, not at {rev} of '
                           'lake-manifest.json')
    rev = links.bases[leanlinks.SELF][1]
    if not re.fullmatch(r'[0-9a-f]{40}', rev):
        defects.append(f'the commit of this repository, {rev!r}, is not a full commit id')
    tracked = tracked_files(rev)
    shown = {}

    def content(repo, path):
        if (repo, path) not in shown:
            if repo == leanlinks.SELF:
                r = subprocess.run(['git', 'show', f'{rev}:{path}'], cwd=REPO, capture_output=True,
                                   text=True)
                shown[(repo, path)] = r.stdout.split('\n') if r.returncode == 0 else None
            else:
                local = os.path.join(local_root(repo, sysroot), path)
                shown[(repo, path)] = file_lines(local) if os.path.isfile(local) else None
        return shown[(repo, path)]

    prefixes = sorted(((f'{url}/{how}/{r}/', repo, how) for repo, (url, r) in links.bases.items()
                       for how in ('blob', 'tree')), key=lambda x: -len(x[0]))
    planned = set()
    nodes = parse(collections.defaultdict(list))
    for n in nodes:
        if n['planned']:
            planned.update(n['lean'])
    self_paths = set()
    pages = sorted(f for f in os.listdir(web) if f.endswith('.html'))
    for page in pages:
        text = open(os.path.join(web, page), encoding='utf-8').read()
        for s in FORBIDDEN:
            if s in text:
                defects.append(f'{page}: contains {s}')
        scan = _Anchors()
        scan.feed(text)
        for el in scan.found:
            a, where = el['attrs'], f'{page}:{el["line"]}'
            name, classes = a.get('data-lean'), a.get('class', '').split()
            if el['tag'] != 'a' or 'href' not in a:
                shown_name = el['text'].strip()
                if not (name or 'lean_decl' in classes) or ('bp-planned-decl' in classes
                                                            and shown_name in planned):
                    continue
                defects.append(f'{where}: the Lean name {name or shown_name!r} is not a link')
                continue
            href = a['href']
            if not href.startswith('https://github.com/'):
                if name or 'lean_decl' in a.get('class', '').split():
                    defects.append(f'{where}: the Lean name {name!r} links to {href}, not to its source')
                continue
            m = next(((p, repo, how) for p, repo, how in prefixes if href.startswith(p)), None)
            if m is None:
                defects.append(f'{where}: {href} is not a link to a pinned revision of a repository '
                               'of the build (scripts/leanlinks.py)')
                continue
            p, repo, how = m
            rest, _, frag = href[len(p):].partition('#')
            path = rest
            if repo == leanlinks.LEAN4:
                if not rest.startswith('src/'):
                    defects.append(f'{where}: {href}: a path of Lean is under src/')
                    continue
                path = rest[len('src/'):]
            kind = 'declaration' if name else ('lines' if frag else ('directory' if how == 'tree' else 'file'))
            count[(repo, kind)] += 1
            if how == 'tree':
                ok = (any(t.startswith(path + '/') for t in tracked) if repo == leanlinks.SELF
                      else os.path.isdir(os.path.join(local_root(repo, sysroot), path)))
                if not ok or frag:
                    defects.append(f'{where}: {href} is not a directory of {repo} at that revision')
                continue
            lines = content(repo, path)
            if lines is None or (repo == leanlinks.SELF and path not in tracked):
                defects.append(f'{where}: {href}: {path} is not a file of {repo} at that revision')
                continue
            if repo == leanlinks.SELF:
                self_paths.add(path)
            span = None
            if frag:
                fm = re.fullmatch(r'L(\d+)(?:-L(\d+))?', frag)
                if not fm or not 1 <= int(fm.group(1)) <= int(fm.group(2) or fm.group(1)) <= len(lines):
                    defects.append(f'{where}: {href}: #{frag} is not a line or range of lines of the '
                                   f'file ({len(lines)} lines)')
                    continue
                span = (int(fm.group(1)), int(fm.group(2) or fm.group(1)))
            if name:
                names_linked[page].add(name)
                want = links.decl(name)
                if want is None or href != want[0]:
                    defects.append(f'{where}: {name} links to {href}, but lean-locations.tsv gives '
                                   f'{want[0] if want else "no row"}')
                    continue
                body = '\n'.join(lines[span[0] - 1:span[1]])
                if not mentions(name, body):
                    defects.append(f'{where}: lines {span[0]}-{span[1]} of {path} do not mention '
                                   f'{name} or a declaration it belongs to')
    if self_paths:
        r = subprocess.run(['git', 'diff', '--quiet', rev, '--'] + sorted(self_paths), cwd=REPO)
        if r.returncode != 0:
            defects.append(f'the working tree differs from {rev[:12]} in files the site links to; '
                           'lean-locations.tsv is measured on the working tree: commit, then '
                           'audit.py --update and build again')
    want = {d for n in nodes if not n['planned'] for d in n['lean']}
    chapters = set().union(*[v for k, v in names_linked.items() if k.startswith('chap-')] or [set()])
    for page, got in (('the chapter pages', chapters),
                      ('dep_graph_document.html', names_linked.get('dep_graph_document.html', set()))):
        missing = sorted(want - got)
        if missing:
            defects.append(f'{page}: {len(missing)} Lean names of nodes are not links, e.g. '
                           + ', '.join(missing[:5]))
    total = sum(count.values())
    print(f'audit: {total} links to Lean sources in {len(pages)} pages, at '
          + ', '.join(f'{r} {links.bases[r][1][:12]}' for r in links.bases))
    for repo in links.bases:
        row = {k: c for (r, k), c in count.items() if r == repo}
        if row:
            print(f'  {repo}: ' + ', '.join(f'{k} {c}' for k, c in sorted(row.items())))
    print(f'audit: {len(want)} Lean names of nodes, linked on the chapter pages and the graph of all '
          f'nodes; {len(defects)} link defects')
    for d in defects[:200]:
        print('  ' + d)
    return 1 if defects else 0


# ---------------------------------------------------------------- main

def is_test(node):
    return bool(node['lean']) and all(d.startswith(TEST) for d in node['lean'])


def footprint(node, names):
    """Axioms, sorry sources and the verdict of a node that is not planned."""
    missing = [d for d in node['lean'] if not names.get(d, {}).get('exists')]
    axioms = {a['name']: a for d in node['lean'] if d not in missing for a in names[d]['axioms']}
    sorries = {x['name']: x for d in node['lean'] if d not in missing for x in names[d]['sorry_sources']}
    allowed_for = {'all'} | ({'tests'} if is_test(node) else set())
    modules = {names[d]['module'] for d in node['lean'] if d not in missing}
    if len(modules) == 1 and not missing:
        allowed_for.add('module:' + modules.pop())
    bad_ax = sorted(a for a in axioms if a not in STD and a != 'sorryAx')
    bad_sorry = sorted(x for x in sorries
                       if x not in LABELS or LABELS[x]['allowed'] not in allowed_for)
    if 'sorryAx' in axioms and not sorries:
        bad_sorry.append('sorryAx (no sorry source found)')
    ok = bool(node['lean']) and not missing and not bad_ax and not bad_sorry
    inherited = sorted(LABELS[x]['label'] if x in LABELS else x for x in sorries
                       if sorries[x]['module'].startswith(INH))
    return dict(ok=ok, missing=missing, axioms=sorted(axioms), bad_axioms=bad_ax,
                bad_sorry=bad_sorry, inherited=inherited, sources=sorted(sorries))


def main(argv):
    if '--print-imports' in argv:
        print(' '.join(expand_imports()))
        return 0
    if '--check-links' in argv:
        i = argv.index('--check-links')
        return check_links(argv[i + 1] if i + 1 < len(argv) else os.path.join(BP, 'web'))
    defects = collections.defaultdict(list)
    os.makedirs(OUT, exist_ok=True)
    nodes = parse(defects)

    if '--check-lean-decls' in argv:
        i = argv.index('--check-lean-decls')
        src = argv[i + 1] if i + 1 < len(argv) else os.path.join(BP, 'lean_decls')
        planned = {d for n in nodes if n['planned'] for d in n['lean']}
        names = [l.strip() for l in open(src, encoding='utf-8') if l.strip()]
        kept = [d for d in names if d not in planned]
        path = os.path.join(OUT, 'lean_decls.existing')
        with open(path, 'w', encoding='utf-8') as fh:
            fh.write(''.join(d + '\n' for d in kept))
        r = check_decls(path)
        print(open(os.path.join(OUT, 'lake-checkdecls.log'), encoding='utf-8').read(), end='')
        print(f'audit: {len(names)} names collected, {len(names) - len(kept)} of planned nodes skipped')
        return 0 if r == 0 else 1

    update, build = '--update' in argv, '--no-build' not in argv
    labels = collections.Counter(n['label'] for n in nodes if n['label'])
    by_label = {n['label']: n for n in nodes if n['label']}
    for n in nodes:
        f, tag = n['file'], f'L{n["line"]} {n["label"]}'
        if not n['label']:
            defects[f].append(f'L{n["line"]} {n["kind"]}: no \\label')
            continue
        if labels[n['label']] > 1:
            defects[f].append(f'{tag}: label defined {labels[n["label"]]} times')
        if not n['label'].startswith(PREFIX[n['kind']] + ':'):
            defects[f].append(f'{tag}: label prefix does not match the environment {n["kind"]}')
        if re.search(r"[.'\s]", n['label']):
            defects[f].append(f'{tag}: label contains a dot, prime or space')
        if not n['lean']:
            defects[f].append(f'{tag}: no \\lean{{...}}')
        for u in n['used_by'] + n['used_by_proof']:
            if u not in labels:
                defects[f].append(f'{tag}: \\usedby... \\ref{{{u}}} does not resolve to a node')
        for u in n['uses'] + n['proof_uses']:
            if u not in labels:
                defects[f].append(f'{tag}: \\uses{{{u}}} does not resolve to a node')
            if u == n['label']:
                defects[f].append(f'{tag}: uses itself')
            if not n['planned'] and u in by_label and by_label[u]['planned']:
                defects[f].append(f'{tag}: a node that is not planned uses the planned node {u}')
        if n['kind'] in ('definition', 'imported') and n['proof']:
            defects[f].append(f'{tag}: a {n["kind"]} node carries a proof environment')
        if n['kind'] in RESULTS and not n['proof']:
            defects[f].append(f'{tag}: a result without a proof environment')
        if n['planned']:
            if n['leanok'] or n['proof_leanok']:
                defects[f].append(f'{tag}: a planned node carries \\leanok')
            if n['srcloc']:
                defects[f].append(f'{tag}: a planned node carries \\srcloc')
            if n['has_inherited']:
                defects[f].append(f'{tag}: a planned node carries \\inherited')
    owners = collections.defaultdict(list)
    for n in nodes:
        for d in n['lean']:
            owners[d].append(n)
    for d, ns in owners.items():
        if len(ns) > 1:
            defects[ns[0]['file']].append(f'{d} is cited by {len(ns)} nodes: ' + ', '.join(str(x['label']) for x in ns))
    graph = {n['label']: {u for u in n['uses'] + n['proof_uses'] if u in labels} for n in nodes if n['label']}
    for comp in cycles(graph):
        defects['(graph)'].append('\\uses cycle: ' + ', '.join(sorted(comp)))

    # generated chapters: registers and pins
    if render_registers.main(['--check']) != 0:
        defects['generated'].append('a register or pins chapter is stale: run blueprint/scripts/render_registers.py')

    data = measure(sorted(owners), build,
                   link_names(nodes, tex_texts()) | render_registers.decl_candidates())
    names = data['names']

    # the imported nodes: written first, since the other checks read them
    path = os.path.join(GEN, 'lean4lean-imports.tex')
    text = lean4lean_imports(nodes, data, defects)
    fresh = {'lean4lean-imports.tex': text}
    if not os.path.exists(path) or open(path, encoding='utf-8').read() != text:
        if update:
            with open(path, 'w', encoding='utf-8') as fh:
                fh.write(text)
            print('audit: wrote blueprint/src/generated/lean4lean-imports.tex; auditing again')
            return main([a for a in argv if a != '--no-build'] + ['--no-build'])
        defects['generated'].append('lean4lean-imports.tex is stale: run blueprint/scripts/audit.py '
                                    '--update')
    footprints = {}
    for n in nodes:
        f, tag = n['file'], f'L{n["line"]} {n["label"]}'
        if n['planned']:
            for d in n['lean']:
                if names.get(d, {}).get('exists'):
                    defects[f].append(f'{tag}: {d} exists, but the node is marked \\planned')
            footprints[n['label']] = dict(ok=False, planned=True, axioms=[], inherited=[])
            continue
        fp = footprint(n, names)
        footprints[n['label']] = fp
        for d in n['lean']:
            x = names.get(d, {})
            if x.get('exists') and not x.get('axioms_agree'):
                defects[f].append(f'{tag}: the measured axioms of {d} differ from #print axioms '
                                  f'({", ".join(x.get("lean_axioms", []))}): CheckDecls.lean closure defect')
        for d in fp['missing']:
            defects[f].append(f'{tag}: {d} is not a declaration of the environment (mark the node \\planned '
                              'if it is not formalized yet)')
        if n['leanok'] != fp['ok']:
            why = ('missing: ' + ', '.join(fp['missing']) if fp['missing'] else
                   'outside the allowed set: axioms ' + (', '.join(fp['bad_axioms']) or '-') + '; sorry sources '
                   + (', '.join(fp['bad_sorry']) or '-') if not fp['ok'] else 'nothing outside the allowed set')
            defects[f].append(f'{tag}: statement \\leanok={n["leanok"]}, but allowed={fp["ok"]} ({why})')
        if n['kind'] in RESULTS and n['proof'] and n['proof_leanok'] != fp['ok']:
            defects[f].append(f'{tag}: proof \\leanok={n["proof_leanok"]}, but allowed={fp["ok"]}')
        if fp['ok'] and sorted(n['inherited']) != fp['inherited']:
            defects[f].append(f'{tag}: \\inherited{{{", ".join(n["inherited"])}}} but measured '
                              f'{{{", ".join(fp["inherited"])}}}')
        if n['has_inherited'] and not fp['inherited']:
            defects[f].append(f'{tag}: \\inherited present, but the node inherits nothing')
        if n['srcloc'] and n['lean'] and not fp['missing']:
            first = names[n['lean'][0]]
            want = (module_path(first['module']), str(first['line']))
            if n['srcloc'] != want:
                defects[f].append(f'{tag}: \\srcloc{{{n["srcloc"][0]}}}{{{n["srcloc"][1]}}}, '
                                  f'but {n["lean"][0]} is at {want[0]}:{want[1]}')

    # node kinds
    for f, msg in kinds.check(nodes, names, data['deps']):
        defects[f].append(msg)
    for fname, text in kinds.generated(nodes):
        path = os.path.join(GEN, fname)
        if not os.path.exists(path) or open(path, encoding='utf-8').read() != text:
            defects['generated'].append(f'{fname} is stale: run blueprint/scripts/kinds.py')

    # present state only
    history = re.compile(r'\b(' + '|'.join(re.escape(w).replace('\\ ', r'\s+') for w in HISTORY_WORDS)
                         + r')\b', re.I)
    for path in tex_sources():
        if os.path.basename(path) in REGISTERS:
            continue
        name = os.path.relpath(path, os.path.join(BP, 'src'))
        for i, line in enumerate(open(path, encoding='utf-8'), 1):
            m = history.search(re.sub(r'(?<!\\)%.*', '', line))
            if m:
                defects[name].append(f'L{i}: "{m.group(0)}" narrates history (STYLE.md section 1)')

    # coverage of the verification library
    cited = {d for n in nodes if not n['planned'] for d in n['lean']}
    for c in data['covered']:
        if c['name'] not in cited:
            defects['coverage'].append(f'{c["name"]} ({module_path(c["module"])}:{c["line"]}, {c["kind"]}) '
                                       'is cited by no node')

    # generated tables
    reach = collections.defaultdict(list)
    for n in nodes:
        for x in footprints.get(n['label'], {}).get('inherited', []):
            reach[x].append(n['label'])
    reached = sorted({x for fp in footprints.values() for x in fp.get('sources', [])
                      if x in {c['name'] for c in data['census'] if c['package'] == 'inherited'}})
    for fname, text in (('inherited-sorries.tex', inherited_table(data, reach, defects)),
                        ('roots.tex', roots_table(nodes, defects)),
                        ('planned.tex', planned_table(nodes)),
                        ('census-lean4lean.tex', census_lean4lean(data, reached)),
                        ('census-shipping.tex', census_shipping(data))):
        fresh[fname] = text
        path = os.path.join(GEN, fname)
        old = open(path, encoding='utf-8').read() if os.path.exists(path) else None
        if old != text:
            if update:
                with open(path, 'w', encoding='utf-8') as fh:
                    fh.write(text)
                print(f'audit: wrote blueprint/src/generated/{fname}')
            else:
                defects['generated'].append(f'{fname} is stale: run blueprint/scripts/audit.py --update')

    # links to the Lean sources: the citations of the sources (with the tables as written above),
    # and the declaration range of every linked name
    texts = tex_texts()
    texts.update({os.path.join('generated', f): t for f, t in fresh.items()})
    check_citations(texts, set(data['locations']), data['sysroot'], defects)
    rows = location_rows(data, link_names(nodes, texts), defects, render_registers.decl_candidates())
    tsv = leanlinks.write_locations(rows)
    old = open(leanlinks.LOCATIONS, encoding='utf-8').read() if os.path.exists(leanlinks.LOCATIONS) else None
    if old != tsv:
        if update:
            with open(leanlinks.LOCATIONS, 'w', encoding='utf-8') as fh:
                fh.write(tsv)
            print('audit: wrote blueprint/src/generated/lean-locations.tsv; rendering the registers, '
                  'which cite the names it locates, and auditing again')
            render_registers.LOCATED.clear()
            if render_registers.main([]) != 0:
                raise SystemExit('audit: render_registers.py failed')
            return main([a for a in argv if a != '--no-build'] + ['--no-build'])
        else:
            defects['generated'].append('lean-locations.tsv is stale: run blueprint/scripts/audit.py '
                                        '--update')

    planned = [n for n in nodes if n['planned']]
    inh_rows = [c for c in data['census'] if c['package'] == 'inherited']
    total = sum(len(v) for v in defects.values())
    with open(os.path.join(OUT, 'report.md'), 'w', encoding='utf-8') as fh:
        fh.write(f'# Blueprint audit\n\n{len(nodes)} nodes ({len(nodes) - len(planned)} formalized, '
                 f'{len(planned)} planned), {len(owners)} Lean names cited, '
                 f'{len(data["covered"])} declarations of {COVER}*, {total} defects.\n\n'
                 f'Imports: {" ".join(data["modules"])}\n\n## Defects\n')
        if not total:
            fh.write('\nNone.\n')
        for f in sorted(defects):
            fh.write(f'\n### {f}\n' + ''.join(f'- {d}\n' for d in defects[f]))
        table = kinds.classify(nodes)
        fh.write('\n## Nodes\n\n| label | environment | kind, status | planned | leanok | axioms | inherited |\n'
                 '|---|---|---|---|---|---|---|\n')
        for n in nodes:
            fp = footprints.get(n['label'], {})
            fh.write(f"| {n['label']} | {n['kind']} | {', '.join(table.get(n['label'], ('', '')))} | "
                     f"{n['planned']} | {n['leanok']} | "
                     f"{', '.join(fp.get('axioms', []))} | {', '.join(fp.get('inherited', []))} |\n")
        fh.write('\n## Planned nodes (not yet formalized)\n\n' +
                 ''.join(f"- {n['label']}: {', '.join(n['lean'])}\n" for n in planned))
        fh.write('\n## Labelled inherited sorry sources\n\n| label | declaration | allowed for | nodes |\n'
                 '|---|---|---|---|\n' +
                 ''.join(f"| {x['label']} | {x['name']} | {x['allowed']} | {', '.join(reach.get(x['label'], []))} |\n"
                         for x in CONF['inherited_sorry']))
        fh.write(f'\n## Inherited trust ({INH})\n\nSorry sources ({sum(c["sorry"] for c in inh_rows)}) '
                 f'and axioms ({sum(c["axiom"] for c in inh_rows)}) of the inherited modules; '
                 'reached = some blueprint node depends on it.\n\n| declaration | kind | module:line | reached |\n'
                 '|---|---|---|---|\n')
        for c in inh_rows:
            fh.write(f"| {c['name']} | {'sorry source' if c['sorry'] else 'axiom'} ({c['kind']}) | "
                     f"{c['module']}:{c['line']} | {'yes' if c['name'] in reached else 'no'} |\n")
    print(f'audit: {len(nodes)} nodes ({len(nodes) - len(planned)} formalized, {len(planned)} planned '
          f'= not yet formalized), {len(owners)} Lean names cited, {total} defects '
          f'-> blueprint/.audit/report.md')
    kcount = collections.Counter(k for k, _ in kinds.classify(nodes).values())
    print('audit: kinds: ' + ', '.join(f'{k} {kcount[k]}' for k in kinds.KINDS if kcount[k]))
    by_repo = collections.Counter(r for r, _, _, _ in rows.values())
    print(f'audit: links to the Lean sources: {len(rows)} names, '
          + ', '.join(f'{c} in {r}' for r, c in sorted(by_repo.items())))
    print(f'audit: inherited trust ({INH}): {sum(c["sorry"] for c in inh_rows)} sorry sources, '
          f'{sum(c["axiom"] for c in inh_rows)} axioms; reached by blueprint nodes: '
          + (', '.join(f'{x} ({len(reach[x])} nodes)' for x in sorted(reach)) if reach else 'none'))
    for f in sorted(defects):
        for d in defects[f]:
            print(f'  {f}: {d}')
    return 1 if total else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
