#!/usr/bin/env python3
"""Node kinds of the blueprint and their visual encoding: the one source of the colours, shapes,
badges and graph frames of the web version, the print version and the legends.

The derivation is mechanical (README, section "Node kinds and dependency graphs"), and
scripts/audit.py checks it (check()).

  layer   of a declaration, from its name: EraseProof.Test.* test, EraseProof.* proof,
          Lean4Lean.* and Lean.* lean4lean (lean4lean extends Lean's namespaces: Lean.Expr.
          instantiate1'), any other name shipping. The audit checks that the module of the
          declaration agrees (MODULE_LAYER) and that the names of a node share one layer.
  kind    final: the node of the declaration on the FINAL line of proof/ROOTS.txt;
          milestone: any other `theorem` environment of the proof layer (the audit checks that the
          final theorem depends on it);
          step: a result of the proof layer that the proof of the final theorem or of a milestone
          uses directly (its \\uses);
          definition, lemma: the other nodes of the proof layer, by environment;
          shipping, test, lean4lean: the nodes of those layers; the nodes of the lean4lean layer
          are the imported nodes that scripts/audit.py --update writes, one per lean4lean module
          that the proof library or the shipping code uses directly (the audit checks that the
          imported environment holds exactly them);
          lean4leansorry: in the graphs only, one node per labelled lean4lean sorry of audit.toml
          that some node lists in \\inherited.
          The audit checks the \\uses of the final theorem and of the milestones against the
          declarations they use directly, so that the step lemmas are those of the Lean proofs.
          The opener of every chapter with nodes prints them by kind with \\bpnodes{its label}
          (checked).
  status  planned (\\planned); inherits (\\inherited lists lean4lean sorries, which the audit
          measures); standard otherwise (within the standard axioms).
  block   the frame of a node in the full dependency graph (blocks()): one per chapter of the proof
          layer; one for the shipping code and one for the tests, framed inside by chapter or
          section; one for lean4lean, framed inside by library, with the sorries the nodes
          inherit.

Writes, from the chapters, proof/ROOTS.txt and blueprint/audit.toml:
  src/generated/kinds.tex           colours and badges of the kinds and statuses, and the kind of
                                    every node (preamble of both versions);
  src/generated/kinds-legend.tex    the legend tables of the introduction;
  src/generated/kinds-chapters.tex  the nodes of every chapter, by kind.

    python3 blueprint/scripts/kinds.py           # write them (build.sh runs this)
    python3 blueprint/scripts/kinds.py --check   # exit 1 if one is stale (the audit checks this)

scripts/kindgraph.py draws the graphs from this module; scripts/bpkinds.py, the plasTeX package of
the web version, adds the badges and the CSS (css()).
"""
import collections, os, re, sys, tomllib

HERE = os.path.dirname(os.path.abspath(__file__))
BP = os.path.dirname(HERE)
REPO = os.path.dirname(BP)
SRC = os.path.join(BP, 'src')
GEN = os.path.join(SRC, 'generated')
ROOTS = os.path.join(REPO, 'proof', 'ROOTS.txt')
AUDIT_TOML = os.path.join(BP, 'audit.toml')

# Layer of a declaration: from its name (first matching prefix), and from its module.
NAME_LAYER = [('EraseProof.Test.', 'test'), ('EraseProof.', 'proof'), ('Lean4Lean.', 'lean4lean'),
              ('Lean.', 'lean4lean')]
DEFAULT_LAYER = 'shipping'
MODULE_LAYER = [('EraseProof.Test', 'test'), ('EraseProof', 'proof'), ('Lean4Lean', 'lean4lean'),
                ('LeanToLambdaBox', 'shipping')]

# The kinds, in legend order. `fill`: the colour of the node and of its badge, under dark text.
# `line`: the border of the badge, the bar of the node box in the web version and the title of
# graph frames; contrast at least 4.5:1 on white. Hues of the Okabe-Ito palette (yellow, blue,
# orange, reddish purple, bluish green); the kinds of one hue differ in shape and lightness, so
# that no kind is told by colour alone. `peripheries`: 2 draws a double outline.
KINDS = collections.OrderedDict([
    ('final', dict(
        name='Final theorem', badge='FINAL THEOREM', layer='proof', shape='octagon', peripheries=2,
        fill='#F0C24B', line='#7A5A00', fontsize=24, graph='gold double octagon',
        short='the theorem about #erase',
        rule=r'cites the declaration on the line \code{FINAL} of \code{proof/ROOTS.txt}')),
    ('milestone', dict(
        name='Milestone theorem', badge='MILESTONE', layer='proof', shape='hexagon', peripheries=1,
        fill='#8FBCE6', line='#0B5394', fontsize=18, graph='blue hexagon',
        short='a headline theorem the final theorem rests on',
        rule=r'any other \code{theorem} environment; the audit checks that the final theorem '
             r'depends on it')),
    ('step', dict(
        name='Step lemma', badge='STEP LEMMA', layer='proof', shape='ellipse', peripheries=2,
        fill='#C4DBF2', line='#0B5394', fontsize=13, graph='blue double ellipse',
        short='a step of the proof of the final theorem or of a milestone',
        rule=r'a result that the proof of the final theorem or of a milestone uses directly: its '
             r'\code{\textbackslash uses}, which the audit checks against the Lean proof')),
    ('lemma', dict(
        name='Lemma', badge='LEMMA', layer='proof', shape='ellipse', peripheries=1,
        fill='#E6F0FA', line='#0B5394', fontsize=12, graph='pale blue ellipse',
        short='any other result of the proof library',
        rule=r'any other result about declarations of \code{EraseProof}')),
    ('definition', dict(
        name='Definition', badge='DEFINITION', layer='proof', shape='box', peripheries=1,
        fill='#E6F0FA', line='#0B5394', fontsize=12, graph='pale blue box',
        short='a definition of the proof library',
        rule=r'any other definition of \code{EraseProof}')),
    ('shipping', dict(
        name='Shipping code', badge='SHIPPING CODE', layer='shipping', shape='component',
        peripheries=1, fill='#F9D3AE', line='#9A4A00', fontsize=12,
        graph='orange tabbed box',
        short='the code the theorem is about: described, not verified',
        rule=r'declarations outside \code{EraseProof} and lean4lean: the modules '
             r'\code{LeanToLambdaBox*}, which the final theorem is about')),
    ('test', dict(
        name='Test', badge='TEST', layer='test', shape='note', peripheries=1,
        fill='#EBDDF0', line='#7B3F8C', fontsize=12, graph='violet note',
        short='a non-vacuity instance or another test',
        rule=r'declarations of \code{EraseProof.Test}: non-vacuity instances and other tests')),
    ('lean4lean', dict(
        name='lean4lean module', badge='LEAN4LEAN MODULE', layer='lean4lean', shape='folder',
        peripheries=1, fill='#CDEBDD', line='#0A6B4B', fontsize=12, graph='green folder',
        short='the declarations of a lean4lean module that the proof or the shipping code uses',
        rule=r'an \code{imported} node, written by the audit: the declarations of a lean4lean '
             r'module that the proof library or the shipping code uses directly '
             r'(Section~\ref{sec:trust-imported})')),
    ('lean4leansorry', dict(
        name='lean4lean sorry', badge='LEAN4LEAN SORRY', layer='lean4lean', shape='cylinder',
        peripheries=1, fill='#E8F5EE', line='#0A6B4B', fontsize=12, graph='pale green cylinder',
        short='a lean4lean sorry that nodes inherit (graphs only)',
        rule=r'a labelled lean4lean sorry that some node inherits '
             r'(Section~\ref{sec:trust-inherited}); in the graphs only')),
])

# The layers: the tint and line of the graph frames, and the names of the frames.
LAYERS = collections.OrderedDict([
    ('lean4lean', dict(name='lean4lean (imported)', tint='#EEF8F2', line='#0A6B4B')),
    ('shipping', dict(name='Shipping code (LeanToLambdaBox)', tint='#FFF5EB', line='#9A4A00')),
    ('proof', dict(name='Proof library (EraseProof)', tint='#F3F8FD', line='#0B5394')),
    ('test', dict(name='Tests (EraseProof.Test)', tint='#F8F2FA', line='#7B3F8C')),
])

# Status: the border of a node in the graphs. Thickness and dashes carry it, so it does not rely on
# colour; the headings of the text carry it as a badge.
STATUS = collections.OrderedDict([
    ('standard', dict(
        name='Within standard axioms', line='#333333', penwidth=1.2, style='filled', badge=None,
        graph='thin, dark',
        short='its declarations exist and depend on no lean4lean sorry',
        text=r'its declarations exist and depend on the standard axioms \code{propext}, '
             r'\code{Classical.choice} and \code{Quot.sound} only: on no lean4lean sorry')),
    ('inherits', dict(
        name='Inherits lean4lean sorries', line='#B2182B', penwidth=3.2, style='filled',
        badge='INHERITS', graph='thick, crimson',
        short='its declarations exist and also depend on lean4lean sorries (badge INHERITS)',
        text=r'its declarations exist and also depend on lean4lean sorries: the badge INHERITS '
             r'after its heading names them, and its body lists them under \emph{Inherited from '
             r'lean4lean}')),
    ('planned', dict(
        name='Planned', line='#333333', penwidth=1.4, style='filled,dashed', fill='#FFFFFF',
        badge='PLANNED', graph='dashed, white fill', short='not formalized (badge PLANNED)',
        text=r'not formalized: its declarations do not exist; badge \stPlanned{}')),
])

# The arrows of the graphs: (key, name, meaning, colour, dash for the legend swatch).
EDGES = [
    ('statement', 'dashed grey arrow', r'the statement (or definition) of the target uses the '
                                       r'source', '#8A8A8A', '4 3'),
    ('proof', 'solid grey arrow', r'the proof of the target uses the source', '#5E5E5E', ''),
    ('main', 'blue arrow', 'a use by the final theorem or a milestone (dashed: by the statement); '
                           'all of them are drawn', '#0B5394', ''),
    ('test', 'violet arrow', 'into a test (dashed: by the statement)', '#9E7BB5', ''),
    ('lean4lean', 'green arrow', 'from a lean4lean module: the target uses its declarations '
                                 'directly (dashed: in the statement)', '#0A6B4B', ''),
    ('sorry', 'dotted crimson arrow', 'the target inherits the lean4lean sorry', '#B2182B',
     '1.5 2.5'),
]
EDGE_COLOR = {k: c for k, _, _, c, _ in EDGES}
# What every arrow obeys: (name, meaning). The opacity of a faint arrow is CROSS_OPACITY.
EDGE_NOTES = [
    ('no arrow', 'when a path of other arrows implies it (transitive reduction), except a blue '
                 'arrow'),
    ('faint arrow', 'in the graph of all nodes, an arrow between two frames, except a blue arrow; a '
                    'click on a node draws its arrows in full'),
]
CROSS_OPACITY = '55'


def tex_key(kind):
    """The kind as TeX colour and macro names spell it (letters only)."""
    return kind.replace('4', 'four')


# ---------------------------------------------------------------- derivation

def layer_of_name(name):
    for prefix, layer in NAME_LAYER:
        if name.startswith(prefix):
            return layer
    return DEFAULT_LAYER


def layer_of_module(module):
    for prefix, layer in MODULE_LAYER:
        if module == prefix or module.startswith(prefix + '.'):
            return layer
    return None


def final_decls():
    """The declarations on the FINAL lines of proof/ROOTS.txt."""
    out = []
    for line in open(ROOTS, encoding='utf-8'):
        parts = line.split('#', 1)[0].split()
        if len(parts) >= 2 and parts[1] == 'FINAL':
            out.append(parts[0])
    return out


def node_layer(node):
    """The layer of a parsed node (scripts/audit.py parse), or None if its names disagree."""
    layers = {layer_of_name(d) for d in node['lean']}
    return layers.pop() if len(layers) == 1 else None


def classify(nodes):
    """label -> (kind, status), for the parsed nodes that have a label."""
    finals = set(final_decls())
    nodes = [n for n in nodes if n['label']]
    base = {}
    for n in nodes:
        layer = node_layer(n) or DEFAULT_LAYER
        if layer != 'proof':
            base[n['label']] = layer
        elif any(d in finals for d in n['lean']):
            base[n['label']] = 'final'
        elif n['kind'] == 'theorem':
            base[n['label']] = 'milestone'
        else:
            base[n['label']] = 'definition' if n['kind'] == 'definition' else 'lemma'
    steps = {u for n in nodes if base[n['label']] in ('final', 'milestone') for u in n['proof_uses']}
    out = {}
    for n in nodes:
        kind = base[n['label']]
        if kind == 'lemma' and n['label'] in steps:
            kind = 'step'
        status = 'planned' if n['planned'] else 'inherits' if n['inherited'] else 'standard'
        out[n['label']] = (kind, status)
    return out


def short_name(name):
    """The label of a node in the graphs: its first declaration without the namespace its kind
    implies."""
    for prefix in ('EraseProof.Test.', 'EraseProof.', 'Lean4Lean.VEnv.', 'Lean4Lean.',
                   'Erasure.'):
        if name.startswith(prefix):
            return name[len(prefix):]
    return name


def inherited_sorries(nodes):
    """The labelled lean4lean sorries of audit.toml that some node lists in \\inherited, in the
    order of audit.toml, with the labels of those nodes."""
    users = collections.defaultdict(list)
    for n in nodes:
        for x in n['inherited']:
            users[x].append(n['label'])
    conf = tomllib.load(open(AUDIT_TOML, 'rb'))
    return [dict(x, nodes=users[x['label']]) for x in conf['inherited_sorry'] if users[x['label']]]


def measured_uses(node, owner, deps):
    """(statement, all): the labels of the nodes whose declarations the declarations of node use
    directly (deps: the measure of the audit), in the statement (a definition, or the type of a
    result's declaration) and anywhere."""
    stmt, every = set(), set()
    for d in node['lean']:
        for t, where in deps.get(d, ()):
            m = owner.get(t)
            if m is None or m is node or not m['label']:
                continue
            every.add(m['label'])
            if where == 'type' or node['kind'] == 'definition':
                stmt.add(m['label'])
    return stmt, every


def check_main_uses(nodes, table, deps):
    """The \\uses of the final theorem and of every milestone, which make the step lemmas, against
    the measure: every node they name is used directly (a statement \\uses by the statement), and
    the results among the nodes used directly are exactly the results they name."""
    out = []
    owner = {d: n for n in nodes for d in n['lean']}
    by_label = {n['label']: n for n in nodes if n['label']}
    for lab, (k, s) in table.items():
        if k not in ('final', 'milestone'):
            continue
        n = by_label[lab]
        stmt, every = measured_uses(n, owner, deps)
        named = set(n['uses']) | set(n['proof_uses'])
        for u in sorted(set(n['uses']) - stmt):
            out.append((n['file'], f'{lab}: its statement \\uses {u}, whose declarations its '
                        'declarations do not use directly in their types'))
        for u in sorted(named - every - set(n['uses'])):
            out.append((n['file'], f'{lab}: its proof \\uses {u}, whose declarations its '
                        'declarations do not use directly'))
        results = {u for u in every if table.get(u, ('',))[0] not in ('definition', 'shipping',
                                                                       'lean4lean')}
        for u in sorted(results - named):
            out.append((n['file'], f'{lab}: its declarations use {u} directly, but its \\uses do '
                        'not name it'))
    return out


def check(nodes, names, measured=None):
    """Defects of the kind assignment, as (file, message): names is the measure of the audit
    (declaration -> dict with exists, module), measured the direct uses it measured (declaration
    -> [used declaration, 'type' or 'value']; data['deps'] of scripts/audit.py)."""
    out = []
    table = classify(nodes)
    by_label = {n['label']: n for n in nodes if n['label']}
    for n in nodes:
        if not n['label']:
            continue
        tag = f'L{n["line"]} {n["label"]}'
        layers = {d: layer_of_name(d) for d in n['lean']}
        if len(set(layers.values())) > 1:
            out.append((n['file'], f'{tag}: its declarations belong to several layers: '
                        + ', '.join(f'{d} ({layer})' for d, layer in layers.items())))
        for d, layer in layers.items():
            x = names.get(d, {})
            if x.get('exists') and layer_of_module(x['module']) != layer:
                out.append((n['file'], f'{tag}: {d} has the layer {layer} by its name, but its module '
                            f'{x["module"]} has the layer {layer_of_module(x["module"])}'))
        kind = table[n['label']][0]
        if (kind == 'lean4lean') != (n['kind'] == 'imported'):
            out.append((n['file'], f'{tag}: kind {kind} in a {n["kind"]} environment (the imported '
                        'environment holds exactly the nodes of the lean4lean layer)'))
        if n['status_words']:
            out.append((n['file'], f'{tag}: its body carries the status word '
                        f'{", ".join(sorted(set(n["status_words"])))}; the badges after the heading '
                        'give kind and status'))
    finals = [lab for lab, (k, s) in table.items() if k == 'final']
    if len(finals) != 1:
        out.append(('kinds', f'{len(finals)} final nodes (the FINAL line of proof/ROOTS.txt must be '
                    'cited by exactly one node): ' + ', '.join(finals)))
    for lab in finals:
        if by_label[lab]['kind'] != 'theorem':
            out.append((by_label[lab]['file'], f'{lab}: the final node is a {by_label[lab]["kind"]}, '
                        'not a theorem'))
    deps = collections.defaultdict(set)
    for n in nodes:
        if n['label']:
            deps[n['label']] = set(n['uses']) | set(n['proof_uses'])
    reach, todo = set(), list(finals)
    while todo:
        x = todo.pop()
        for u in deps.get(x, ()):
            if u not in reach:
                reach.add(u)
                todo.append(u)
    for lab, (k, s) in table.items():
        if k == 'milestone' and lab not in reach:
            out.append((by_label[lab]['file'], f'{lab}: a milestone (a theorem environment) that the '
                        'final theorem does not depend on'))
    if measured is not None:
        out += check_main_uses(nodes, table, measured)
    count = chapter_counts(nodes)
    for c in chapters():
        txt = re.sub(r'(?<!\\)%.*', '', open(os.path.join(SRC, c['file']), encoding='utf-8').read())
        cited = re.findall(r'\\bpnodes\{([^}]*)\}', txt)
        want = [c['label']] if count[c['label']] else []
        if cited != want:
            out.append((c['file'], f'\\bpnodes: cites {cited or "nothing"}; the opener of a chapter '
                        f'with nodes cites its own label once ({want or "none here"})'))
    return out


# ---------------------------------------------------------------- chapters and blocks

def tex_to_text(s):
    """Plain text of a short TeX title."""
    s = re.sub(r'\\texorpdfstring\{(?:[^{}]|\{[^{}]*\})*\}\{((?:[^{}]|\{[^{}]*\})*)\}', r'\1', s)
    s = re.sub(r'\\(code|emph|textbf|texttt)\{((?:[^{}]|\{[^{}]*\})*)\}', r'\2', s)
    s = s.replace('\\textbackslash ', '\\').replace('\\_', '_').replace('\\#', '#')
    s = s.replace('$', '').replace('~', ' ')
    return re.sub(r'\s+', ' ', s).strip()


def chapters():
    """The chapters of src/content.tex, in order: dicts with file (relative to src/), number,
    title, label, sections: (line, title, label) of the numbered sections, and inputs: (line, file)
    of the generated files the chapter inputs."""
    out, number = [], 0
    content = open(os.path.join(SRC, 'content.tex'), encoding='utf-8').read()
    for item in re.findall(r'^\\input\{([^}]*)\}', content, re.M):
        txt = open(os.path.join(SRC, item + '.tex'), encoding='utf-8').read()
        m = re.search(r'\\chapter\{((?:[^{}]|\{[^{}]*\})*)\}\s*\\label\{([^}]*)\}', txt)
        if not m:
            continue
        number += 1
        sections = []
        for s in re.finditer(r'^\\section\{((?:[^{}]|\{(?:[^{}]|\{[^{}]*\})*\})*)\}\s*\\label\{([^}]*)\}',
                             txt, re.M):
            sections.append((txt.count('\n', 0, s.start()) + 1, tex_to_text(s.group(1)), s.group(2)))
        inputs = [(txt.count('\n', 0, i.start()) + 1, i.group(1) + '.tex')
                  for i in re.finditer(r'^\\input\{(generated/[^}]*)\}', txt, re.M)]
        out.append(dict(file=item + '.tex', number=number, title=tex_to_text(m.group(1)),
                        label=m.group(2), sections=sections, inputs=inputs))
    return out


def chapter_of(nodes):
    """label -> the chapter (a dict of chapters()) of every labelled node: the chapter of its file,
    or of the chapter that inputs its generated file."""
    chaps = {}
    for c in chapters():
        chaps[c['file']] = c
        for _, f in c['inputs']:
            chaps.setdefault(f, c)
    return {n['label']: chaps.get(n['file']) for n in nodes if n['label']}


def document_order(nodes):
    """The labels of the labelled nodes in the order of the document: by chapter, then by line (a
    node of a generated file at the line of its \\input)."""
    where = {}
    for c in chapters():
        where[c['file']] = (c['number'], None)
        for line, f in c['inputs']:
            where.setdefault(f, (c['number'], line))

    def key(n):
        number, at = where.get(n['file'], (10 ** 6, None))
        return (number, at if at is not None else n['line'], n['line'])
    return [n['label'] for n in sorted((n for n in nodes if n['label']), key=key)]


def section_of(node, chapter):
    """(label, title) of the numbered section of the chapter that holds the node (for a node of a
    generated file, the section of its \\input)."""
    line = next((at for at, f in chapter['inputs'] if f == node['file']), node['line'])
    before = [s for s in chapter['sections'] if s[0] < line] or chapter['sections'][:1]
    return (before[-1][2], before[-1][1]) if before else (chapter['label'], chapter['title'])


def library(label):
    """The lean4lean library (Lean4Lean.Theory, ...) of an imported node, from its label
    (imp:Lean4Lean-Theory-VExpr)."""
    return '.'.join(label.split(':', 1)[1].split('-')[:2])


def blocks(nodes):
    """The blocks of the full graph, in document order: key -> dict(title, layer, link, frames),
    where frames is a list of dict(title or None, labels, link). link names the graph page that the
    title of the frame opens: the label of a chapter, 'lean4lean' (the graph of the lean4lean
    nodes), or None. One block per chapter of the proof layer;
    one for lean4lean, with a frame for the sorries the nodes inherit (labels 'lean4lean:<label>')
    and one per library of the imported nodes; one for the shipping code, framed by chapter; one
    for the tests, framed by section."""
    table = classify(nodes)
    chap = chapter_of(nodes)
    by = {n['label']: n for n in nodes if n['label']}
    out = collections.OrderedDict()
    sorries = inherited_sorries(nodes)
    out['lean4lean'] = dict(title=LAYERS['lean4lean']['name'], layer='lean4lean', link='lean4lean',
                            frames=[])
    if sorries:
        out['lean4lean']['frames'].append(dict(
            title='Sorries the nodes inherit', link='lean4lean',
            labels=['lean4lean:' + x['label'] for x in sorries]))
    frames = collections.defaultdict(collections.OrderedDict)
    for lab in document_order(nodes):
        n = by[lab]
        layer = KINDS[table[lab][0]]['layer']
        c = chap[lab]
        if layer == 'proof':
            key = c['label'] if c else n['file']
            if key not in out:
                out[key] = dict(title=f'{c["number"]}  {c["title"]}' if c else n['file'],
                                layer='proof', link=c['label'] if c else None,
                                frames=[dict(title=None, labels=[], link=None)])
            out[key]['frames'][0]['labels'].append(lab)
            continue
        if layer not in out:
            out[layer] = dict(title=LAYERS[layer]['name'], layer=layer, link=None, frames=[])
        if layer == 'lean4lean':
            sub = (library(lab), 'lean4lean')
        elif layer == 'test' and c and c['sections']:
            sub = (section_of(n, c)[1], c['label'])
        else:
            sub = ((f'{c["number"]}  {c["title"]}', c['label']) if c else (n['file'], None))
        frames[layer].setdefault(sub, []).append(lab)
    for layer, sub in frames.items():
        out[layer]['frames'] += [dict(title=title, labels=labs, link=link)
                                 for (title, link), labs in sub.items()]
        links = {fr['link'] for fr in out[layer]['frames']}
        if len(links) == 1:
            out[layer]['link'] = links.pop()
    if not out['lean4lean']['frames']:
        del out['lean4lean']
    return out


# ---------------------------------------------------------------- generated files

def kinds_tex(nodes):
    table = classify(nodes)
    out = ['% Generated by blueprint/scripts/kinds.py from the chapters, proof/ROOTS.txt and '
           'blueprint/audit.toml. Do not edit.\n',
           '% \\bpdefinekind{kind}{fill}{line}{badge}: the colours bpfill<kind>, bpline<kind> and '
           'the badge of a kind (macros/common.tex).\n']
    for k, d in KINDS.items():
        out.append(f'\\bpdefinekind{{{tex_key(k)}}}{{{d["fill"][1:]}}}{{{d["line"][1:]}}}'
                   f'{{{d["badge"]}}}\n')
    out.append('% \\bpdefinestatus{status}{line}: the colour bpstatus<status>.\n')
    for s, d in STATUS.items():
        out.append(f'\\bpdefinestatus{{{s}}}{{{d["line"][1:]}}}\n')
    out.append('% \\bpdefinenodes{chapter}{badges}: the nodes of a chapter by kind, which \\bpnodes{chapter} '
               'prints.\n')
    for label, cnt in chapter_counts(nodes).items():
        if cnt:
            out.append(f'\\bpdefinenodes{{{label}}}{{{badges(cnt)}}}\n')
    out.append('% \\bpsetkind{label}{kind}{status}{inherited sorries}: every node (the print version '
               'puts the badges after its heading).\n')
    for n in nodes:
        if n['label'] in table:
            kind, status = table[n['label']]
            out.append(f'\\bpsetkind{{{n["label"]}}}{{{tex_key(kind)}}}{{{status}}}'
                       f'{{{", ".join(n["inherited"])}}}\n')
    return ''.join(out)


def legend_tex(nodes):
    table = classify(nodes)
    count = collections.Counter(k for k, s in table.values())
    count['lean4leansorry'] = len(inherited_sorries(nodes))
    scount = collections.Counter(s for k, s in table.values())
    rows = [f'\\bpkind{{{tex_key(k)}}} & {d["graph"]} & {d["rule"]} & {count[k]} \\\\\n'
            for k, d in KINDS.items()]
    srows = [f'{d["name"]} & {d["graph"]} & {d["text"]} & {scount[s]} \\\\\n'
             for s, d in STATUS.items()]
    erows = [f'{name} & {text} \\\\\n' for _, name, text, _, _ in EDGES]
    erows += [f'{name} & {text} \\\\\n' for name, text in EDGE_NOTES]
    return ''.join([
        '% Generated by blueprint/scripts/kinds.py from blueprint/scripts/kinds.py and the chapters. '
        'Do not edit.\n',
        '\\begin{tabular}{p{0.2\\linewidth}p{0.2\\linewidth}p{0.44\\linewidth}r}\n'
        '\\toprule\nKind (badge) & Graph node & Derived from & Nodes \\\\\n\\midrule\n',
        *rows, '\\bottomrule\n\\end{tabular}\n\n',
        '\\begin{tabular}{p{0.2\\linewidth}p{0.2\\linewidth}p{0.44\\linewidth}r}\n'
        '\\toprule\nStatus & Graph border & Meaning & Nodes \\\\\n\\midrule\n',
        *srows, '\\bottomrule\n\\end{tabular}\n\n',
        '\\begin{tabular}{p{0.24\\linewidth}p{0.68\\linewidth}}\n'
        '\\toprule\nGraph arrow & Meaning \\\\\n\\midrule\n',
        *erows, '\\bottomrule\n\\end{tabular}\n'])


def chapter_counts(nodes):
    """chapter label -> Counter of the kinds of its nodes, for every chapter, in order."""
    table = classify(nodes)
    chap = chapter_of(nodes)
    count = collections.OrderedDict((c['label'], collections.Counter()) for c in chapters())
    for lab, (k, s) in table.items():
        c = chap[lab]
        if c:
            count[c['label']][k] += 1
    return count


def badges(count):
    """The badges of a Counter of kinds, each with its number, in the order of KINDS."""
    return ' '.join(f'\\bpkind{{{tex_key(k)}}}~{count[k]}' for k in KINDS if count[k])


def chapters_tex(nodes):
    """The nodes of every chapter that has nodes, by kind."""
    count = chapter_counts(nodes)
    rows = []
    for c in chapters():
        if count[c['label']]:
            rows.append(f'\\ref{{{c["label"]}}} & {badges(count[c["label"]])} \\\\\n')
    return ''.join([
        '% Generated by blueprint/scripts/kinds.py from the chapters. Do not edit.\n',
        '\\begin{tabular}{lp{0.8\\linewidth}}\n\\toprule\nChapter & Nodes by kind \\\\\n'
        '\\midrule\n', *rows, '\\bottomrule\n\\end{tabular}\n'])


def css():
    """The CSS of the kinds in the web version: badges, and the bar of node boxes."""
    out = ['/* Generated by blueprint/scripts/bpkinds.py from blueprint/scripts/kinds.py. */\n',
           '.bp-kind, .bp-status { display: inline-block; font: 600 .68rem/1.5 sans-serif; '
           'letter-spacing: .04em; padding: 0 .45rem; border: 1px solid; border-radius: .25rem; '
           'color: #1A1A1A; vertical-align: .12em; margin-left: .45rem; white-space: nowrap; }\n',
           '.bp-status { background: #FFFFFF; }\n']
    for k, d in KINDS.items():
        double = '; border-style: double; border-width: 3px' if d['peripheries'] > 1 else ''
        out.append(f'.bp-kind-{k} {{ background: {d["fill"]}; border-color: {d["line"]}{double}; }}\n')
        out.append(f'div[class*="_thmwrapper"]:has(> div[class*="_thmheading"] .bp-kind-{k}) > '
                   f'div[class*="_thmcontent"] {{ border-left: .3rem solid {d["line"]}; '
                   f'padding-left: .6rem; }}\n')
    for s, d in STATUS.items():
        out.append(f'.bp-status-{s} {{ border-color: {d["line"]}; color: {d["line"]}; '
                   + ('border-style: dashed; ' if 'dashed' in d['style'] else '') + '}\n')
    return ''.join(out)


def generated(nodes):
    return (('kinds.tex', kinds_tex(nodes)), ('kinds-legend.tex', legend_tex(nodes)),
            ('kinds-chapters.tex', chapters_tex(nodes)))


def main(argv):
    sys.path.insert(0, HERE)
    import audit  # noqa: E402  (the parser of the chapters)
    defects = collections.defaultdict(list)
    nodes = audit.parse(defects)
    stale = 0
    for fname, text in generated(nodes):
        path = os.path.join(GEN, fname)
        old = open(path, encoding='utf-8').read() if os.path.exists(path) else None
        if old == text:
            continue
        if '--check' in argv:
            print(f'kinds.py: src/generated/{fname} is stale: run blueprint/scripts/kinds.py')
            stale = 1
        else:
            with open(path, 'w', encoding='utf-8') as fh:
                fh.write(text)
            print(f'kinds.py: wrote blueprint/src/generated/{fname}')
    return stale


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
