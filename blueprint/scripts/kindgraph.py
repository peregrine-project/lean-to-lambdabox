#!/usr/bin/env python3
"""The dependency graphs of the web version, laid out at build time with the Graphviz library that
the pinned pygraphviz wheel bundles, and drawn as SVG (scripts/bpkinds.py puts them in the pages).

Three kinds of graph, all from the parsed chapters (scripts/audit.py parse) and the kinds
(scripts/kinds.py):

  full      every node. Block layout: each block of kinds.blocks() (a chapter of the proof library;
            the shipping code; the tests; the lean4lean sorries) is laid out by dot on its own,
            top to bottom; dot then arranges the blocks, as boxes of their size, along the
            dependencies between them; the arrows between blocks are routed last, around the
            nodes (Graphviz's "nop2" engine), and drawn faint.
  chapter   the nodes of one chapter (framed by section in the tests chapter), left to right
            between the nodes of other chapters that they use and those that use them, which are
            faded and labelled with their chapter's number. The nodes of lean4lean (the imported
            nodes of the trust chapter and the sorries) have a graph of their own, like a chapter.
  map       one box per chapter with its nodes by kind, and an arrow between two chapters labelled
            with the number of arrows of the full graph between them.

Every graph has the arrows of the \\uses commands (a statement use wins over a proof use of the
same pair), an arrow from each imported lean4lean module to the nodes its \\usedbystatements and
\\usedbyproofs name, an arrow from each lean4lean sorry to every node that lists it in
\\inherited, and none that a path of other arrows implies (transitive reduction), except the arrows
of a \\uses of the final theorem or of a milestone, which are all drawn.

    python3 blueprint/scripts/kindgraph.py OUTDIR    # writes the DOT, SVG and PNG of every graph
"""
import collections, html, os, re, sys, tempfile

import pygraphviz as P

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import kinds  # noqa: E402

FONT = 'Helvetica,Arial,sans-serif'
FULL_PAGE = 'dep_graph_document.html'
MAP_PAGE = 'dep_graph_chapters.html'
# ranksep and nodesep (inches) inside the blocks of the full graph.
BLOCK_SEP = ('0.42', '0.6')
BLOCK_PAD = 10
# The opacity of the fill of a node of another chapter in the graph of a chapter.
CONTEXT_ALPHA = '59'
# The columns of a frame of imported lean4lean nodes in the graph of all nodes.
GRID_COLUMNS = 4


def frame_name(link, key, i):
    """The name of the cluster of frame i of a block: it starts with the label of the chapter whose
    graph page the title of the frame opens (cluster_chap:pure__shipping1,
    cluster_lean4lean__lean4lean0), if any."""
    return f'cluster_{link}__{key}{i}' if link else f'cluster_{key}__{i}'


LEAN4LEAN = 'lean4lean'


def chapter_page(chapter_label):
    """The page of the graph of a chapter, from the chapter's label (chap:model), or of the nodes
    of lean4lean (LEAN4LEAN)."""
    return 'dep_graph_' + chapter_label.replace(':', '-') + '.html'


def reduce(edges, keep=lambda e: False):
    """The edges (s, t, ...) that no path of two or more other edges implies, and those that keep
    selects, in their order. Every edge counts for the paths."""
    succ = collections.defaultdict(list)
    for e in edges:
        succ[e[0]].append(e[1])
    memo = {}

    def reach(v):
        if v not in memo:
            out = set()
            for w in succ[v]:
                out.add(w)
                out |= reach(w)
            memo[v] = out
        return memo[v]
    return [e for e in edges
            if keep(e) or not any(e[1] in reach(w) for w in succ[e[0]] if w != e[1])]


def num(s):
    return [float(x) for x in s.split(',')]


def shift(pos, dx, dy):
    """A pos attribute (a point, or a spline with e,/s, endpoints) moved by (dx, dy)."""
    out = []
    for tok in pos.split():
        parts = tok.split(',')
        if parts[0] in ('e', 's'):
            out.append(f'{parts[0]},{float(parts[1]) + dx:.2f},{float(parts[2]) + dy:.2f}')
        else:
            out.append(f'{float(parts[0]) + dx:.2f},{float(parts[1]) + dy:.2f}')
    return ' '.join(out)


def shift_bb(bb, dx, dy):
    x0, y0, x1, y1 = num(bb)
    return f'{x0 + dx:.2f},{y0 + dy:.2f},{x1 + dx:.2f},{y1 + dy:.2f}'


def draw(g, prog):
    """The SVG of g laid out by prog. Graphviz's messages go to the standard error with the prefix
    "kindgraph:"; Fontconfig's are dropped. When nodes touch, Graphviz draws the arrows between
    frames straight instead of around the nodes: the build goes on, with a warning."""
    with tempfile.TemporaryFile() as err:
        saved = os.dup(2)
        os.dup2(err.fileno(), 2)
        try:
            data = g.draw(format='svg', prog=prog)
        finally:
            os.dup2(saved, 2)
            os.close(saved)
        err.seek(0)
        messages = err.read().decode('utf-8', 'replace')
    for line in messages.splitlines():
        if line.strip() and 'Fontconfig' not in line:
            print('kindgraph: Graphviz: ' + line.strip(), file=sys.stderr)
    if 'straight line edges' in messages:
        print('kindgraph: warning: nodes touch, so the arrows between frames of the graph of all '
              'nodes are straight; raise BLOCK_SEP', file=sys.stderr)
    return data


def svg_text(data):
    """The SVG that Graphviz writes, ready to inline in a page: no XML prolog, doctype or comment;
    the root fills its container and has no viewBox, so a unit of the drawing is a pixel until the
    page zooms the group that holds the drawing."""
    s = data.decode('utf-8') if isinstance(data, bytes) else data
    s = re.sub(r'<\?xml[^>]*\?>\s*', '', s)
    s = re.sub(r'<!DOCTYPE[^>]*>\s*', '', s)
    s = re.sub(r'<!--.*?-->\s*', '', s, flags=re.S)
    s = re.sub(r'<svg width="[^"]*" height="[^"]*"\s+viewBox="[^"]*"',
               '<svg class="bp-graph" width="100%" height="100%"', s, count=1)
    s = s.replace('<g id="graph0"', '<g class="bp-zoom"><g id="graph0"', 1)
    s = s.replace('</svg>', '</g></svg>', 1)
    return s.strip() + '\n'


class Graphs:
    """The graphs of the parsed nodes."""

    def __init__(self, nodes):
        self.nodes = [n for n in nodes if n['label']]
        self.by = {n['label']: n for n in self.nodes}
        self.table = kinds.classify(nodes)
        self.sorries = kinds.inherited_sorries(nodes)
        self.sorry = {'lean4lean:' + x['label']: x for x in self.sorries}
        self.blocks = kinds.blocks(nodes)
        self.block_of = {lab: key for key, b in self.blocks.items() for fr in b['frames']
                         for lab in fr['labels']}
        self.chapters = kinds.chapters()
        self.chapter_of = kinds.chapter_of(nodes)
        self.edges = self._edges()

    # ------------------------------------------------------------ nodes and edges

    def _edges(self):
        found = collections.OrderedDict()
        for n in self.nodes:
            for u in n['proof_uses']:
                found[(u, n['label'])] = 'proof'
            for u in n['uses']:
                found[(u, n['label'])] = 'statement'
            for u in n['used_by_proof']:
                found[(n['label'], u)] = 'proof'
            for u in n['used_by']:
                found[(n['label'], u)] = 'statement'
        for x in self.sorries:
            for lab in x['nodes']:
                found[('lean4lean:' + x['label'], lab)] = 'sorry'
        return reduce([(s, t, how) for (s, t), how in found.items()
                       if (s in self.by or s in self.sorry) and t in self.by], keep=self.is_main)

    def is_main(self, e):
        """An arrow of a \\uses of the final theorem or of a milestone."""
        return (e[2] in ('statement', 'proof') and self.kind(e[1]) in ('final', 'milestone')
                and self.kind(e[0]) not in ('lean4lean', 'lean4leansorry'))

    def kind(self, v):
        return 'lean4leansorry' if v in self.sorry else self.table[v][0]

    def group(self, v):
        """The graph page a node belongs to: LEAN4LEAN for the nodes of the lean4lean layer, else
        the label of its chapter (None if it has none)."""
        if kinds.KINDS[self.kind(v)]['layer'] == 'lean4lean':
            return LEAN4LEAN
        c = self.chapter_of.get(v)
        return c['label'] if c else None

    def status(self, v):
        return 'inherits' if v in self.sorry else self.table[v][1]

    def names(self, v):
        """The Lean names of a node, or the label and name of a lean4lean sorry."""
        if v in self.sorry:
            return [self.sorry[v]['label'], self.sorry[v]['name']]
        return list(self.by[v]['lean'])

    def module(self, v):
        """The lean4lean module of an imported node, from its label."""
        return v.split(':', 1)[1].replace('-', '.')

    def label(self, v):
        if v in self.sorry:
            x = self.sorry[v]
            short = kinds.short_name(x['name'])
            return x['label'] if short == x['label'] else f'{x["label"]}  {short}'
        if self.kind(v) == 'lean4lean':
            return kinds.short_name(self.module(v))
        return kinds.short_name(self.by[v]['lean'][0])

    def tooltip(self, v):
        k = kinds.KINDS[self.kind(v)]
        if v in self.sorry:
            x = self.sorry[v]
            return f'{k["name"]} {x["label"]}: {x["name"]}, {x["what"]}; {len(x["nodes"])} nodes inherit it'
        n = self.by[v]
        extra = f'; inherits {", ".join(n["inherited"])}' if n['inherited'] else ''
        if self.kind(v) == 'lean4lean':
            return f'{k["name"]} {self.module(v)}: {len(n["lean"])} declarations used directly' + extra
        title = kinds.tex_to_text(n['title'])
        return f'{k["name"]}: {n["lean"][0]}' + (f' ({title})' if title else '') + extra

    def node_attrs(self, v):
        kind, status = self.kind(v), self.status(v)
        k, s = kinds.KINDS[kind], kinds.STATUS[status]
        a = dict(label=self.label(v), shape=k['shape'], peripheries=str(k['peripheries']),
                 style=s['style'], fillcolor=s.get('fill', k['fill']), color=s['line'],
                 penwidth=str(s['penwidth']), fontsize=str(k['fontsize']), fontcolor='#1A1A1A',
                 fontname=FONT, tooltip=self.tooltip(v), **{'class': f'bp-k-{kind} bp-s-{status}'})
        if kind in ('final', 'milestone'):
            a['margin'] = '0.25,0.1'
        return a

    def edge_attrs(self, s, t, how, cross=False):
        tk = self.kind(t)
        main = self.is_main((s, t, how))
        if how == 'sorry':
            a = dict(style='dotted', color=kinds.EDGE_COLOR['sorry'], penwidth='1.4', arrowhead='empty')
        else:
            key = ('lean4lean' if self.kind(s) == 'lean4lean' else 'main' if main
                   else 'test' if tk == 'test' else how)
            a = dict(color=kinds.EDGE_COLOR[key], penwidth='1.6' if key == 'main' else '1')
            if how == 'statement':
                a['style'] = 'dashed'
        if cross and not main:
            a['color'] += kinds.CROSS_OPACITY
            a['penwidth'] = '0.8'
        a['class'] = f'bp-e-{how}' + (' bp-cross' if cross else '')
        return a

    def _graph(self, **attrs):
        g = P.AGraph(directed=True, strict=False, fontname=FONT, **attrs)
        g.node_attr.update(fontname=FONT, margin='0.09,0.04')
        g.edge_attr.update(arrowhead='vee', arrowsize='0.7')
        return g

    # ------------------------------------------------------------ the full graph

    def _block(self, key, b):
        """The layout of one block, by dot: an AGraph with positions, whose label is the block's
        title and whose clusters are its frames. A frame of imported nodes, which have no arrows
        between them, is a grid of GRID_COLUMNS columns below the frame of the sorries."""
        L = kinds.LAYERS[b['layer']]
        g = self._graph(rankdir='TB', newrank='true', ranksep=BLOCK_SEP[0], nodesep=BLOCK_SEP[1],
                        label=b['title'], labeljust='l', labelloc='t', fontsize='30',
                        fontcolor=L['line'])
        mine = set()
        for i, fr in enumerate(b['frames']):
            target = g if fr['title'] is None else g.add_subgraph(
                name=frame_name(fr['link'], key, i), label=fr['title'], style='rounded',
                color=L['line'], fontcolor=L['line'], fontsize='18', labeljust='l', margin='10')
            for v in fr['labels']:
                target.add_node(v, **self.node_attrs(v))
                mine.add(v)
            row = [v for v in fr['labels'] if v in self.sorry]
            if row:
                target.add_subgraph(row, name=f'rank_{key}{i}', rank='same')
                for a, c in zip(row, row[1:]):
                    target.add_edge(a, c, style='invis', weight='2')
        top = [v for fr in b['frames'] for v in fr['labels'] if v in self.sorry][:1]
        for fr in b['frames']:
            labs = [v for v in fr['labels'] if self.kind(v) == 'lean4lean']
            for i, v in enumerate(labs):
                if i + GRID_COLUMNS < len(labs):
                    g.add_edge(v, labs[i + GRID_COLUMNS], style='invis', weight='4')
                if top and i < GRID_COLUMNS:
                    g.add_edge(top[0], v, style='invis', weight='0')
        for s, t, how in self.edges:
            if s in mine and t in mine:
                g.add_edge(s, t, **self.edge_attrs(s, t, how))
        g.layout(prog='dot')
        return g

    def _arrangement(self, sizes):
        """Positions of the blocks: dot on one box per block, with an arrow from block A to block B
        when an arrow joins a node of A to a node of B, weighted by their number."""
        a = P.AGraph(directed=True, strict=True, rankdir='TB', ranksep='0.9', nodesep='0.6',
                     newrank='true')
        for key, (w, h) in sizes.items():
            a.add_node(key, shape='box', fixedsize='true', width=f'{w / 72 + 0.3:.3f}',
                       height=f'{h / 72 + 0.3:.3f}', label='')
        count = collections.Counter((self.block_of[s], self.block_of[t]) for s, t, _ in self.edges
                                    if self.block_of[s] != self.block_of[t])
        for (x, y), c in count.items():
            a.add_edge(x, y, weight=str(c))
        a.layout(prog='dot')
        return {key: num(a.get_node(key).attr['pos']) for key in sizes}

    def full(self):
        """The full graph (an AGraph ready for the nop2 engine) of every node."""
        laid = {key: self._block(key, b) for key, b in self.blocks.items()}
        # Every frame grows by BLOCK_PAD points on each side, and its title moves up by as much:
        # Graphviz draws the outer outline of a double node outside the box that dot gives it.
        bbs, p = {}, BLOCK_PAD
        for key, g in laid.items():
            bx0, by0, bx1, by1 = num(g.graph_attr['bb'])
            bbs[key] = (bx0 - p, by0 - p, bx1 + p, by1 + 2 * p)
            lx, ly = num(g.graph_attr['lp'])
            g.graph_attr['bb'] = '{},{},{},{}'.format(*bbs[key])
            g.graph_attr['lp'] = f'{lx},{ly + p}'
        centre = self._arrangement({key: (x1 - x0, y1 - y0) for key, (x0, y0, x1, y1) in bbs.items()})
        f = self._graph(splines='true', bgcolor='white', outputorder='edgesfirst', pad='0.3',
                        sep='0', esep='0')
        x0 = y0 = float('inf')
        x1 = y1 = -float('inf')
        for key, g in laid.items():
            b, (bx0, by0, bx1, by1) = self.blocks[key], bbs[key]
            dx, dy = centre[key][0] - (bx0 + bx1) / 2, centre[key][1] - (by0 + by1) / 2
            x0, y0 = min(x0, bx0 + dx), min(y0, by0 + dy)
            x1, y1 = max(x1, bx1 + dx), max(y1, by1 + dy)
            L = kinds.LAYERS[b['layer']]
            name = f'cluster_{key}' if b['link'] in (None, key) else f'cluster_{b["link"]}__{key}'
            cl = f.add_subgraph(name=name, label=b['title'],
                                bb=shift_bb(g.graph_attr['bb'], dx, dy),
                                lp=shift(g.graph_attr['lp'], dx, dy), style='filled,rounded',
                                fillcolor=L['tint'], color=L['line'], fontcolor=L['line'],
                                fontsize='30', penwidth='1.6', labeljust='l',
                                **{'class': f'bp-block bp-layer-{b["layer"]}'})
            for sub in g.subgraphs():
                cl.add_subgraph(name=sub.name, label=sub.graph_attr['label'],
                                bb=shift_bb(sub.graph_attr['bb'], dx, dy),
                                lp=shift(sub.graph_attr['lp'], dx, dy), style='rounded',
                                color=L['line'], fontcolor=L['line'], fontsize='18')
            for n in g.nodes():
                v = str(n)
                cl.add_node(v, pos=shift(n.attr['pos'], dx, dy), **self.node_attrs(v))
            for e in g.edges():
                s, t = str(e[0]), str(e[1])
                if e.attr.get('style') == 'invis':
                    continue
                how = next(h for a, b2, h in self.edges if a == s and b2 == t)
                f.add_edge(s, t, pos=shift(e.attr['pos'], dx, dy), **self.edge_attrs(s, t, how))
        for s, t, how in self.edges:
            if self.block_of[s] != self.block_of[t]:
                f.add_edge(s, t, **self.edge_attrs(s, t, how, cross=True))
        f.graph_attr['bb'] = f'{x0 - 10:.2f},{y0 - 10:.2f},{x1 + 10:.2f},{y1 + 10:.2f}'
        return f

    # ------------------------------------------------------------ the graph of a chapter

    def chapter(self, chapter_label):
        """The graph of a chapter (an AGraph for dot), or None if the chapter has no node. Left to
        right: the nodes of other chapters that its nodes use, its nodes (framed by section in the
        tests chapter, by layer in a chapter of several layers), the nodes of other chapters that
        use them. A node of another chapter is faded and its label starts with the number of its
        chapter."""
        chap = next((c for c in self.chapters if c['label'] == chapter_label),
                    dict(label=LEAN4LEAN, sections=[], inputs=[]))
        mine = [v for v in list(self.by) + list(self.sorry) if self.group(v) == chapter_label]
        if not mine:
            return None
        mine_set = set(mine)
        edges = [e for e in self.edges if e[0] in mine_set or e[1] in mine_set]
        g = self._graph(rankdir='LR', newrank='true', ranksep='0.55', nodesep='0.16',
                        bgcolor='white', pad='0.3')
        layers = {kinds.KINDS[self.kind(v)]['layer'] for v in mine}
        frames = collections.OrderedDict()
        frame_of = {lab: (fr['title'], 'lean4lean') for fr in self.blocks.get('lean4lean', {}).get(
            'frames', []) for lab in fr['labels']}
        for v in mine:
            layer = kinds.KINDS[self.kind(v)]['layer']
            if layer == 'lean4lean':
                key = frame_of.get(v)
            elif layer == 'test' and chap['sections']:
                key = (kinds.section_of(self.by[v], chap)[1], layer)
            elif len(layers) > 1:
                key = (kinds.LAYERS[layer]['name'], layer)
            else:
                key = None
            frames.setdefault(key, []).append(v)
        for i, (key, vs) in enumerate(frames.items()):
            L = kinds.LAYERS[key[1]] if key else None
            target = g if key is None else g.add_subgraph(
                name=f'cluster_section_{i}', label=key[0], style='filled,rounded', fillcolor=L['tint'],
                color=L['line'], fontcolor=L['line'], fontsize='16', labeljust='l')
            for v in vs:
                target.add_node(v, **self.node_attrs(v))
        others = []
        for s, t, _ in edges:
            others += [v for v in (s, t) if v not in mine_set and v not in others]
        for v in others:
            a = self.node_attrs(v)
            c = None if v in self.sorry else self.chapter_of[v]
            if self.group(v) == LEAN4LEAN:
                a['label'] = f'lean4lean: {a["label"]}'
            elif c:
                a['label'] = f'{c["number"]}: {a["label"]}'
            a['fillcolor'] += CONTEXT_ALPHA
            a['fontcolor'] = '#555555'
            a['class'] += ' bp-context'
            g.add_node(v, **a)
        # Invisible barriers: the inputs left of every node of the chapter, the outputs right of
        # it (a node that is both, between the two shipping chapters, stays free).
        inputs = {s for s, t, _ in edges if s not in mine_set}
        outputs = {t for s, t, _ in edges if t not in mine_set}
        g.add_node('bp-in', style='invis', shape='point', width='0', label='')
        g.add_node('bp-out', style='invis', shape='point', width='0', label='')
        for v in mine:
            g.add_edge('bp-in', v, style='invis', weight='0')
            g.add_edge(v, 'bp-out', style='invis', weight='0')
        for v in others:
            if v in inputs and v not in outputs:
                g.add_edge(v, 'bp-in', style='invis', weight='0')
            if v in outputs and v not in inputs:
                g.add_edge('bp-out', v, style='invis', weight='0')
        for s, t, how in edges:
            g.add_edge(s, t, **self.edge_attrs(s, t, how))
        return g

    # ------------------------------------------------------------ the chapter map

    def chapter_map(self):
        """One box per chapter that has nodes, and one for lean4lean (its imported modules and the
        sorries the nodes inherit); an arrow from A to B labelled with the number of arrows of the
        full graph from a node of A to a node of B."""
        g = self._graph(rankdir='TB', newrank='true', ranksep='0.55', nodesep='0.45',
                        bgcolor='white', pad='0.3')
        key_of = {v: ('lean4lean' if kinds.KINDS[self.kind(v)]['layer'] == 'lean4lean'
                      else self.chapter_of[v]['label'])
                  for v in list(self.by) + list(self.sorry)}
        count = collections.defaultdict(collections.Counter)
        for v, key in key_of.items():
            count[key][self.kind(v)] += 1
        if count['lean4lean']:
            L = kinds.LAYERS['lean4lean']
            g.add_node('lean4lean', shape='box', style='filled,rounded', fillcolor=L['tint'],
                       color=L['line'], penwidth='1.6', margin='0.15,0.1',
                       label=self._map_label(L['name'], count['lean4lean'], L['line']),
                       tooltip='Graph of lean4lean: the modules the proof and the shipping code use, '
                               'and the sorries the nodes inherit',
                       href=chapter_page(LEAN4LEAN))
        for c in self.chapters:
            if not count[c['label']]:
                continue
            layer = kinds.KINDS[next(k for k in count[c['label']])]['layer']
            L = kinds.LAYERS[layer]
            g.add_node(c['label'], shape='box', style='filled,rounded', fillcolor=L['tint'],
                       color=L['line'], penwidth='1.6', margin='0.15,0.1',
                       href=chapter_page(c['label']),
                       tooltip=f'Graph of chapter {c["number"]}  {c["title"]}',
                       label=self._map_label(f'{c["number"]}  {c["title"]}', count[c['label']],
                                             L['line']))
        arrows = collections.Counter((key_of[s], key_of[t]) for s, t, _ in self.edges
                                     if key_of[s] != key_of[t])
        top = max(arrows.values()) if arrows else 1
        for (x, y), c in arrows.items():
            g.add_edge(x, y, label=f' {c} ', fontsize='13', fontcolor='#444444',
                       penwidth=f'{1 + 3 * c / top:.2f}',
                       color=kinds.EDGE_COLOR['lean4lean'] if x == 'lean4lean' else '#6B6B6B',
                       weight=str(c), tooltip=f'{c} arrows of the full graph')
        return g

    @staticmethod
    def _map_label(title, count, line):
        cells = ''.join(
            f'<TD BGCOLOR="{kinds.KINDS[k]["fill"]}" BORDER="1" COLOR="{kinds.KINDS[k]["line"]}">'
            f'<FONT POINT-SIZE="12">{html.escape(kinds.KINDS[k]["name"])}: {count[k]}</FONT></TD>'
            for k in kinds.KINDS if count[k])
        return (f'<<TABLE BORDER="0" CELLBORDER="0" CELLSPACING="4" CELLPADDING="3">'
                f'<TR><TD ALIGN="LEFT" COLSPAN="{max(1, sum(1 for k in count if count[k]))}">'
                f'<FONT POINT-SIZE="20" COLOR="{line}">{html.escape(title)}</FONT></TD></TR>'
                f'<TR>{cells}</TR></TABLE>>')

    # ------------------------------------------------------------ drawing

    def svgs(self):
        """name -> (title, SVG) of every graph: 'document' (full), 'chapters' (map), and the
        label of every chapter that has nodes."""
        out = collections.OrderedDict()
        out['document'] = ('All nodes', svg_text(draw(self.full(), 'nop2')))
        out['chapters'] = ('Chapters', svg_text(draw(self.chapter_map(), 'dot')))
        for c in self.chapters:
            g = self.chapter(c['label'])
            if g is not None:
                out[c['label']] = (f'Chapter {c["number"]}: {c["title"]}',
                                   svg_text(draw(g, 'dot')))
        g = self.chapter(LEAN4LEAN)
        if g is not None:
            out[LEAN4LEAN] = (kinds.LAYERS['lean4lean']['name'], svg_text(draw(g, 'dot')))
        return out


def main(argv):
    if not argv:
        print(__doc__)
        return 2
    import audit  # noqa: E402
    out = argv[0]
    os.makedirs(out, exist_ok=True)
    graphs = Graphs(audit.parse(collections.defaultdict(list)))
    items = [('full', graphs.full(), 'nop2'), ('chapters', graphs.chapter_map(), 'dot')]
    items += [(c['label'].replace(':', '-'), graphs.chapter(c['label']), 'dot') for c in graphs.chapters]
    items.append((LEAN4LEAN, graphs.chapter(LEAN4LEAN), 'dot'))
    for name, g, prog in items:
        if g is None:
            continue
        g.write(os.path.join(out, name + '.dot'))
        g.draw(os.path.join(out, name + '.svg'), format='svg', prog=prog)
        g.draw(os.path.join(out, name + '.png'), format='png', prog=prog)
        print(f'kindgraph: {out}/{name}.svg, .png')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
