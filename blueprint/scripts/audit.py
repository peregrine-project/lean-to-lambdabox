#!/usr/bin/env python3
"""Mechanical audit of the blueprint against the Lean development and the registers.

Run from anywhere (it uses `lake` from PATH and the configuration blueprint/audit.toml):

    python3 blueprint/scripts/audit.py              # build, measure, check; exit 1 on a defect
    python3 blueprint/scripts/audit.py --no-build   # skip `lake build` (the targets are built)
    python3 blueprint/scripts/audit.py --update     # also rewrite the generated census chapters
    python3 blueprint/scripts/audit.py --print-imports   # print the expanded import list

Checks, over the nodes (definition, lemma, proposition, theorem, corollary) of
blueprint/src/chapters/*.tex and blueprint/src/generated/*.tex:

  * every node has a \\label, defined once, whose prefix matches its environment (def, lem, prop,
    thm, cor) and which has no dot, prime or space;
  * every node carries a non-empty \\lean{...}, and no declaration is cited by two nodes;
  * every \\uses resolves to a node, no node uses itself, and the \\uses graph is acyclic;
  * a proof environment follows its statement (never nested in it); a result node has one, a
    definition has none;
  * every cited declaration exists in the environment of the modules listed in audit.toml;
  * \\leanok in a statement iff every cited declaration exists and its axioms are within the
    allowed set: the standard axioms of audit.toml, the axioms declared in the inherited
    development (module prefix `inherited_prefix`, lean4lean), and sorryAx when every sorry source
    (a declaration of the closure whose own type or value uses sorryAx) is in the inherited
    development; \\leanok in the proof of a result node iff its statement has it;
  * \\inherited{...} lists exactly the inherited sorry sources and axioms that the node's
    declarations depend on (absent when there are none);
  * \\srcloc{path}{line}, when present, is the file and line of the node's first declaration;
  * hygiene: no non-ASCII character outside \\lean{}, no unescaped underscore in \\code{},
    \\texttt{}, \\inherited{} or \\srcloc{};
  * the generated chapters are up to date: render_registers.py --check (registers, pins), and the
    two census chapters, which this script writes with --update:
      generated/census-lean4lean.tex   the sorry sources and axioms of the inherited development;
      generated/census-shipping.tex    the partial, opaque, unsafe and monadic shipping code.

It reports the inherited trust: the census of the inherited development, and for every node the
inherited sorry sources and axioms it depends on. Output: blueprint/.audit/ (report.md,
measure.json, the lake logs). Exit status 1 if a defect is found, 2 on a tool failure.
"""
import collections, glob, json, os, re, subprocess, sys, tomllib

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
BP = os.path.join(REPO, 'blueprint')
OUT = os.path.join(BP, '.audit')
GEN = os.path.join(BP, 'src', 'generated')
CONF = tomllib.load(open(os.path.join(BP, 'audit.toml'), 'rb'))
STD = set(CONF['standard_axioms'])
INH = CONF['inherited_prefix']
SHIP = CONF['shipping_prefix']
KINDS = ['definition', 'lemma', 'proposition', 'theorem', 'corollary']
PREFIX = dict(definition='def', lemma='lem', proposition='prop', theorem='thm', corollary='cor')
RESULTS = {'lemma', 'proposition', 'theorem', 'corollary'}
MONADS = {'Lean.Meta.MetaM', 'Lean.Core.CoreM', 'Erasure.EraseM', 'Lean.Elab.Command.CommandElab',
          'Lean.Elab.Command.CommandElabM', 'Lean.Elab.Term.TermElabM', 'IO', 'EIO', 'BaseIO'}

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import render_registers  # noqa: E402


# ---------------------------------------------------------------- parsing the chapters

def args_of(macro, txt):
    """The comma-separated items of every \\macro{...} in txt (one level of braces inside)."""
    out = []
    for m in re.finditer(r'\\%s\{((?:[^{}]|\{[^{}]*\})*)\}' % macro, txt, re.S):
        out += [x.strip() for x in m.group(1).replace('\n', ' ').split(',') if x.strip()]
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
        for i, line in enumerate(raw.split('\n'), 1):
            if any(ord(c) > 127 for c in re.sub(r'\\lean\{[^}]*\}', '', line)):
                defects[name].append(f'L{i}: non-ASCII character outside \\lean{{}}')
            for m in re.finditer(r'\\(code|texttt|inherited|srcloc)\{((?:[^{}]|\{[^{}]*\})*)\}', line):
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
                last = dict(file=name, line=line, kind=m.group(1), label=labels[0] if labels else None,
                            lean=args_of('lean', body), leanok=bool(re.search(r'\\leanok\b', body)),
                            uses=args_of('uses', body),
                            inherited=[unescape(x) for x in args_of('inherited', body)],
                            has_inherited='\\inherited{' in body,
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
    roots = [REPO]
    roots += sorted(glob.glob(os.path.join(REPO, '.lake', 'packages', '*')))
    return roots


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


def run_lake(args, log):
    with open(os.path.join(OUT, log), 'w', encoding='utf-8') as f:
        r = subprocess.run(['lake'] + args, cwd=REPO, stdout=f, stderr=subprocess.STDOUT, text=True)
    return r.returncode


def measure(names, build):
    os.makedirs(OUT, exist_ok=True)
    if build and run_lake(['build'] + CONF['build_targets'], 'lake-build.log') != 0:
        raise SystemExit('audit: lake build failed, see blueprint/.audit/lake-build.log')
    with open(os.path.join(OUT, 'names.txt'), 'w', encoding='utf-8') as f:
        f.write(''.join(n + '\n' for n in names))
    env = dict(os.environ, BP_INHERITED_PREFIX=INH, BP_SHIPPING_PREFIX=SHIP)
    out = os.path.join(OUT, 'measure.json')
    with open(os.path.join(OUT, 'lake-measure.log'), 'w', encoding='utf-8') as f:
        r = subprocess.run(['lake', 'env', 'lean', '--run', 'blueprint/CheckDecls.lean', 'measure',
                            os.path.join(OUT, 'names.txt'), out] + expand_imports(),
                           cwd=REPO, stdout=f, stderr=subprocess.STDOUT, text=True, env=env)
    if r.returncode != 0:
        raise SystemExit('audit: measuring failed, see blueprint/.audit/lake-measure.log')
    return json.load(open(out, encoding='utf-8'))


def module_path(module):
    rel = module.replace('.', '/') + '.lean'
    for root in package_roots():
        if os.path.exists(os.path.join(root, rel)):
            return rel
    return rel


# ---------------------------------------------------------------- generated census chapters

def tt(s):
    """Escaped code text, with break opportunities after dots, slashes and underscores."""
    return render_registers.esc(s, 'census', code=True).replace('.', r'.\allowbreak{}')


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
           + (', '.join(f'\\code{{{tt(x)}}}' for x in reached) if reached else 'none of them') + '.\n'
           '\\end{itemize}\n\n',
           render_registers.table(
               'p{0.45\\linewidth}p{0.36\\linewidth}l', 'Sorry source & Module & Kind',
               [f'\\code{{{tt(c["name"])}}} & \\code{{{tt(c["module"])}}}:{c["line"]} & {tt(c["kind"])} \\\\'
                for c in sorries]),
           render_registers.table(
               'p{0.3\\linewidth}rp{0.55\\linewidth}', 'Module & Axioms & Names',
               [f'\\code{{{tt(mod)}}} & {len(by_mod[mod])} & '
                + ', '.join(f'\\code{{{tt(n)}}}' for n in sorted(by_mod[mod])) + ' \\\\'
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
        loc = f'\\code{{{tt(module_path(s["module"]))}}}' + (f':{s["line"]}' if s['line'] is not None else '')
        rows.append(f'\\code{{{tt(s["name"])}}} & {tt(s["kind"])} & \\code{{{tt(s["result"])}}} & {loc} \\\\')
    out.append(render_registers.table('p{0.34\\linewidth}p{0.14\\linewidth}p{0.2\\linewidth}p{0.22\\linewidth}',
                                      'Declaration & Kind & Result & Location', rows))
    return ''.join(out)


# ---------------------------------------------------------------- main

def main(argv):
    if '--print-imports' in argv:
        print(' '.join(expand_imports()))
        return 0
    update, build = '--update' in argv, '--no-build' not in argv
    defects = collections.defaultdict(list)
    os.makedirs(OUT, exist_ok=True)

    nodes = parse(defects)
    labels = collections.Counter(n['label'] for n in nodes if n['label'])
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
        for u in n['uses'] + n['proof_uses']:
            if u not in labels:
                defects[f].append(f'{tag}: \\uses{{{u}}} does not resolve to a node')
            if u == n['label']:
                defects[f].append(f'{tag}: uses itself')
        if n['kind'] == 'definition' and n['proof']:
            defects[f].append(f'{tag}: a definition carries a proof environment')
        if n['kind'] in RESULTS and not n['proof']:
            defects[f].append(f'{tag}: a result without a proof environment')
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

    data = measure(sorted(owners), build)
    names = data['names']
    footprints = {}
    for n in nodes:
        f, tag = n['file'], f'L{n["line"]} {n["label"]}'
        missing = [d for d in n['lean'] if not names.get(d, {}).get('exists')]
        for d in missing:
            defects[f].append(f'{tag}: {d} is not a declaration of the environment')
        axioms = {a['name']: a for d in n['lean'] if d not in missing for a in names[d]['axioms']}
        sorries = {s['name']: s for d in n['lean'] if d not in missing for s in names[d]['sorry_sources']}
        bad_ax = sorted(a for a, v in axioms.items()
                        if a not in STD and a != 'sorryAx' and not v['module'].startswith(INH))
        bad_sorry = sorted(s for s, v in sorries.items() if not v['module'].startswith(INH))
        if 'sorryAx' in axioms and not sorries:
            bad_sorry.append('sorryAx (no sorry source found)')
        ok = bool(n['lean']) and not missing and not bad_ax and not bad_sorry
        inherited = sorted([x for x, v in sorries.items() if v['module'].startswith(INH)] +
                           [a for a, v in axioms.items() if v['module'].startswith(INH)])
        footprints[n['label']] = dict(ok=ok, axioms=sorted(axioms), bad_axioms=bad_ax,
                                      bad_sorry=bad_sorry, inherited=inherited)
        if n['leanok'] != ok:
            why = ('missing: ' + ', '.join(missing) if missing else
                   'outside the allowed set: axioms ' + (', '.join(bad_ax) or '-') + '; sorry sources '
                   + (', '.join(bad_sorry) or '-') if not ok else 'nothing outside the allowed set')
            defects[f].append(f'{tag}: statement \\leanok={n["leanok"]}, but allowed={ok} ({why})')
        if n['kind'] in RESULTS and n['proof'] and n['proof_leanok'] != ok:
            defects[f].append(f'{tag}: proof \\leanok={n["proof_leanok"]}, but allowed={ok}')
        if ok and sorted(n['inherited']) != inherited:
            defects[f].append(f'{tag}: \\inherited{{{", ".join(n["inherited"])}}} but measured '
                              f'{{{", ".join(inherited)}}}')
        if n['has_inherited'] and not inherited:
            defects[f].append(f'{tag}: \\inherited present, but the node inherits nothing')
        if n['srcloc'] and n['lean'] and not missing:
            first = names[n['lean'][0]]
            want = (module_path(first['module']), str(first['line']))
            if n['srcloc'] != want:
                defects[f].append(f'{tag}: \\srcloc{{{n["srcloc"][0]}}}{{{n["srcloc"][1]}}}, '
                                  f'but {n["lean"][0]} is at {want[0]}:{want[1]}')

    # generated chapters: censuses
    reached = sorted({x for fp in footprints.values() for x in fp['inherited']})
    for fname, text in (('census-lean4lean.tex', census_lean4lean(data, reached)),
                        ('census-shipping.tex', census_shipping(data))):
        path = os.path.join(GEN, fname)
        old = open(path, encoding='utf-8').read() if os.path.exists(path) else None
        if old != text:
            if update:
                with open(path, 'w', encoding='utf-8') as fh:
                    fh.write(text)
                print(f'audit: wrote blueprint/src/generated/{fname}')
            else:
                defects['generated'].append(f'{fname} is stale: run blueprint/scripts/audit.py --update')

    inh_rows = [c for c in data['census'] if c['package'] == 'inherited']
    total = sum(len(v) for v in defects.values())
    with open(os.path.join(OUT, 'report.md'), 'w', encoding='utf-8') as fh:
        fh.write(f'# Blueprint audit\n\n{len(nodes)} nodes, {len(owners)} Lean declarations, '
                 f'{total} defects.\n\nImports: {" ".join(data["modules"])}\n\n## Defects\n')
        if not total:
            fh.write('\nNone.\n')
        for f in sorted(defects):
            fh.write(f'\n### {f}\n' + ''.join(f'- {d}\n' for d in defects[f]))
        fh.write('\n## Nodes\n\n| label | kind | leanok | axioms | inherited |\n|---|---|---|---|---|\n')
        for n in nodes:
            fp = footprints.get(n['label'], {})
            fh.write(f"| {n['label']} | {n['kind']} | {n['leanok']} | {', '.join(fp.get('axioms', []))} | "
                     f"{', '.join(fp.get('inherited', []))} |\n")
        fh.write(f'\n## Inherited trust ({INH})\n\nSorry sources ({sum(c["sorry"] for c in inh_rows)}) '
                 f'and axioms ({sum(c["axiom"] for c in inh_rows)}) of the inherited modules; '
                 'reached = some blueprint node depends on it.\n\n| declaration | kind | module:line | reached |\n'
                 '|---|---|---|---|\n')
        for c in inh_rows:
            fh.write(f"| {c['name']} | {'sorry source' if c['sorry'] else 'axiom'} ({c['kind']}) | "
                     f"{c['module']}:{c['line']} | {'yes' if c['name'] in reached else 'no'} |\n")
    print(f'audit: {len(nodes)} nodes, {len(owners)} Lean declarations, {total} defects '
          f'-> blueprint/.audit/report.md')
    print(f'audit: inherited trust ({INH}): {sum(c["sorry"] for c in inh_rows)} sorry sources, '
          f'{sum(c["axiom"] for c in inh_rows)} axioms; reached by blueprint nodes: '
          + (', '.join(reached) if reached else 'none'))
    for f in sorted(defects):
        for d in defects[f]:
            print(f'  {f}: {d}')
    return 1 if total else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
