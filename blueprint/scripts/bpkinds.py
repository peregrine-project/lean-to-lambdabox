"""plasTeX package `bpkinds`: the node kinds (scripts/kinds.py) and the dependency graphs
(scripts/kindgraph.py) in the web version.

src/web.tex loads it after leanblueprint (\\usepackage{bpkinds}); plasTeX finds it through
`packages-dirs` in src/plastex.cfg. It uses the extension points of plastexdepgraph 0.0.5 and
leanblueprint 0.0.20 only, and patches no file of theirs:

* the graph pages: plastexdepgraph's document graph becomes a KindGraph, which hands the SVG of
  kindgraph.Graphs to the template blueprint/templates/dep_graph.html (option `tpl` of the
  blueprint package in src/web.tex); a pre-cleanup callback writes, with the same template, the
  chapter map (dep_graph_chapters.html) and one page per chapter (dep_graph_chap-<name>.html); the
  table of contents links to the chapter map;
* the legend of the graph pages (document.userdata['dep_graph']['legend']);
* in the heading of every node, a kind badge, a status badge when the node inherits lean4lean
  sorries or is planned (document.userdata['thm_header_extras_tpl']), and a link to the node in the
  graph of its chapter (thm_header_hidden_extras_tpl);
* \\bpkind{kind}, the badge of a kind, and \\bpnodes{chapter}, the badges of the nodes of a chapter
  with a link to its graph (the print version defines both in macros/print.tex);
* the CSS of the kinds, styles/bpkinds.css, written from kinds.css() at build time into
  blueprint/.build/bpkinds/ (with the template of \\bpkind and \\bpnodes), which plasTeX copies.

The graphs read the \\uses arrows from the chapters (scripts/audit.py parse), as the audit does; the
build stops if they differ from the arrows plasTeX collected.
"""
import collections, html, json, os, re, sys
from pathlib import Path

from jinja2 import Template
from plasTeX import Command
from plasTeX.Logging import getLogger
from plasTeX.PackageResource import PackageCss, PackagePreCleanupCB, PackageTemplateDir
from plastexdepgraph.Packages.depgraph import DepGraph

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import audit  # noqa: E402  (the parser of the chapters)
import kindgraph  # noqa: E402
import kinds  # noqa: E402

log = getLogger()
TEMPLATE = Path(HERE).parent / 'templates' / 'dep_graph.html'
# Where the build writes the generated CSS and template of this package (ignored by git).
BUILD_DIR = Path(HERE).parent / '.build' / 'bpkinds'

BADGE_TPL = Template("""
    {% if obj.userdata.bp_kind %}<span class="bp-kind bp-kind-{{ obj.userdata.bp_kind }}"
      title="{{ obj.userdata.bp_kind_title }}">{{ obj.userdata.bp_badge }}</span>{% endif %}
    {% if obj.userdata.bp_status_badge %}<span class="bp-status bp-status-{{ obj.userdata.bp_status }}"
      title="{{ obj.userdata.bp_status_title }}">{{ obj.userdata.bp_status_badge }}</span>{% endif %}
""")

GRAPH_LINK_TPL = Template("""
    {% if obj.userdata.bp_graph_page %}<a class="icon bp-graph-link"
      href="{{ obj.userdata.bp_graph_page }}#{{ obj.id }}"
      title="Show this node in the dependency graph of its chapter (or of lean4lean)">graph</a>{% endif %}
""")

BPKIND_TEMPLATE = ('name: bpkind\n<span class="bp-kind bp-kind-{{ obj.attributes.cls }}">'
                   '{{ obj.attributes.badge }}</span>\n\n'
                   'name: bpnodes\n{% for k, badge, n in obj.attributes.counts %}'
                   '<span class="bp-kind bp-kind-{{ k }}">{{ badge }}</span>&#160;{{ n }} '
                   '{% endfor %}{% for page, text in obj.attributes.pages %}<a class="bp-chapter-graph" '
                   'href="{{ page }}">{{ text }}</a> {% endfor %}\n')
STATE = {}          # set by ProcessOptions: 'counts' (kinds.chapter_counts)


class bpkind(Command):
    r"""\bpkind{key}: the badge of the kind whose TeX key (kinds.tex_key) is key."""
    args = 'kind:str'

    def invoke(self, tex):
        result = Command.invoke(self, tex)
        key = self.attributes['kind']
        kind = next((k for k in kinds.KINDS if kinds.tex_key(k) == key), None)
        if kind is None:
            log.error(f'bpkinds: \\bpkind of an unknown kind: {key}')
            kind = 'lemma'
        self.attributes['badge'] = kinds.KINDS[kind]['badge']
        self.attributes['cls'] = kind
        return result


class bpnodes(Command):
    r"""\bpnodes{chapter}: the badges of the nodes of a chapter with their numbers, and a link to
    the graph of the chapter."""
    args = 'chapter:str'

    def invoke(self, tex):
        result = Command.invoke(self, tex)
        label = self.attributes['chapter']
        count = STATE.get('counts', {}).get(label)
        if not count:
            log.error(f'bpkinds: \\bpnodes of a chapter without nodes: {label}')
            count = collections.Counter()
        self.attributes['counts'] = [(k, kinds.KINDS[k]['badge'], count[k]) for k in kinds.KINDS
                                     if count[k]]
        pages = []
        if count and any(kinds.KINDS[k]['layer'] != 'lean4lean' for k in count if count[k]):
            pages.append((kindgraph.chapter_page(label), 'graph of this chapter'))
        if count and any(kinds.KINDS[k]['layer'] == 'lean4lean' for k in count if count[k]):
            pages.append((kindgraph.chapter_page(kindgraph.LEAN4LEAN), 'graph of lean4lean'))
        self.attributes['pages'] = pages
        return result


class _Dot:
    """What plastexdepgraph does with the result of to_dot: reduce it and print it. The page draws
    the SVG of the graph instead, so there is nothing to print."""

    def tred(self):
        return self

    def to_string(self):
        return ''


class KindGraph(DepGraph):
    """A graph page: its nodes (plasTeX nodes: a click on a node shows the statement), title, file
    name, kind (full, map, chapter), SVG and the names its search field knows."""

    bp_title = ''
    bp_page = kindgraph.FULL_PAGE
    bp_kind = 'full'
    bp_svg = ''
    bp_search = '{}'

    def to_dot(self, shapes):
        return _Dot()


def swatch(shape, fill, line, penwidth=1.2, dashed=False, double=False):
    """A small inline SVG of a graph node, for the legend."""
    w, h, sw = 46, 22, max(1.0, penwidth * 0.8)
    dash = ' stroke-dasharray="4 2"' if dashed else ''
    a = f'fill="{fill}" stroke="{line}" stroke-width="{sw}"{dash}'
    if shape == 'ellipse':
        body = f'<ellipse cx="23" cy="11" rx="20" ry="8.5" {a}/>'
        if double:
            body = (f'<ellipse cx="23" cy="11" rx="21.5" ry="10" fill="none" stroke="{line}" '
                    f'stroke-width="1"/><ellipse cx="23" cy="11" rx="18" ry="6.8" {a}/>')
    elif shape == 'hexagon':
        body = f'<polygon points="3,11 11,2.5 35,2.5 43,11 35,19.5 11,19.5" {a}/>'
    elif shape == 'octagon':
        body = f'<polygon points="9,2.5 37,2.5 43,7 43,15 37,19.5 9,19.5 3,15 3,7" {a}/>'
        if double:
            body = (f'<polygon points="8,1 38,1 45,6.5 45,15.5 38,21 8,21 1,15.5 1,6.5" '
                    f'fill="none" stroke="{line}" stroke-width="1"/>'
                    f'<polygon points="10,4 36,4 41,8 41,14 36,18 10,18 5,14 5,8" {a}/>')
    elif shape == 'note':
        body = (f'<polygon points="4,2.5 36,2.5 42,8 42,19.5 4,19.5" {a}/>'
                f'<polyline points="36,2.5 36,8 42,8" fill="none" stroke="{line}" stroke-width="1"/>')
    elif shape == 'component':
        body = (f'<rect x="6" y="2.5" width="36" height="17" {a}/>'
                f'<rect x="3" y="5.5" width="6" height="3.5" fill="{fill}" stroke="{line}" '
                f'stroke-width="1"/><rect x="3" y="13" width="6" height="3.5" fill="{fill}" '
                f'stroke="{line}" stroke-width="1"/>')
    elif shape == 'folder':
        body = (f'<path d="M4,5 h13 l3,-2.5 h9 l3,2.5 h10 v14.5 h-38 z" {a}/>')
    elif shape == 'cylinder':
        body = f'<path d="M5,5 v12 a18,3 0 0 0 36,0 v-12 a18,3 0 0 0 -36,0 a18,3 0 0 0 36,0" {a}/>'
    else:
        body = f'<rect x="4" y="2.5" width="38" height="17" {a}/>'
    return (f'<svg class="bp-swatch" width="{w}" height="{h}" viewBox="0 0 {w} {h}" '
            f'aria-hidden="true">{body}</svg>')


def edge_swatch(color, dash=''):
    d = f' stroke-dasharray="{dash}"' if dash else ''
    return (f'<svg class="bp-swatch" width="46" height="22" viewBox="0 0 46 22" aria-hidden="true">'
            f'<line x1="3" y1="11" x2="36" y2="11" stroke="{color}" stroke-width="1.6"{d}/>'
            f'<polygon points="36,7 43,11 36,15" fill="{color}"/></svg>')


def tex_plain(s):
    """Plain text from the TeX strings of kinds.py."""
    return kinds.tex_to_text(s.replace(r'\stPlanned{}', 'PLANNED')
                             .replace(r'Section~\ref{sec:trust-inherited}', 'chapter Trust boundary'))


def border_swatch(line, penwidth, dashed=False):
    """A border sample for the legend of a status: the corner of a node's outline, with no fill,
    so that it matches no kind's swatch."""
    dash = ' stroke-dasharray="4 2"' if dashed else ''
    return (f'<svg class="bp-swatch" width="46" height="22" viewBox="0 0 46 22" aria-hidden="true">'
            f'<path d="M6,19 V6 Q6,4 8,4 H40" fill="none" stroke="{line}" '
            f'stroke-width="{max(1.0, penwidth * 0.9):.1f}"{dash}/></svg>')


def legend_items():
    """The legend of the graph pages: (swatch and name, meaning), as HTML."""
    items = []
    standard = kinds.STATUS['standard']
    for k, d in kinds.KINDS.items():
        items.append((swatch(d['shape'], d['fill'], standard['line'], double=d['peripheries'] > 1)
                      + html.escape(d['name']), html.escape(d['short'])))
    for s, d in kinds.STATUS.items():
        items.append((border_swatch(d['line'], d['penwidth'], 'dashed' in d['style'])
                      + html.escape(d['name']), html.escape(d['short'])))
    for key, name, text, color, dash in kinds.EDGES:
        items.append((edge_swatch(color, dash) + html.escape(name[0].upper() + name[1:]),
                      html.escape(text)))
    for name, text in kinds.EDGE_NOTES:
        items.append((html.escape(name[0].upper() + name[1:]), html.escape(text)))
    items.append(('Faded node', 'in the graph of a chapter or of lean4lean: a node outside it that '
                                'an arrow joins to it; its chapter number, or lean4lean, before '
                                'its name'))
    return items


def node_ids(svg):
    """The node names of a Graphviz SVG, in order."""
    return [html.unescape(t) for t in
            re.findall(r'<g id="node\d+" class="node[^"]*">\s*<title>([^<]*)</title>', svg)]


def ProcessOptions(options, document):
    parsed = audit.parse(collections.defaultdict(list))
    graphs = kindgraph.Graphs(parsed)
    STATE['counts'] = kinds.chapter_counts(parsed)
    page_of = {v: kindgraph.chapter_page(graphs.group(v)) for v in graphs.by if graphs.group(v)}

    css_dir = BUILD_DIR
    css_dir.mkdir(parents=True, exist_ok=True)
    (css_dir / 'bpkinds.css').write_text(kinds.css(), encoding='utf-8')
    (css_dir / 'bpkinds.jinja2s').write_text(BPKIND_TEMPLATE, encoding='utf-8')
    document.addPackageResource([PackageCss(path=css_dir / 'bpkinds.css'),
                                 PackageTemplateDir(path=css_dir)])
    document.userdata.setdefault('thm_header_extras_tpl', []).append(BADGE_TPL)
    document.userdata.setdefault('thm_header_hidden_extras_tpl', []).append(GRAPH_LINK_TPL)

    pages = []      # the graph pages, in the order of the navigation bar

    def search_json(ids, kind):
        """The names the find field knows, each with the node it focuses: on a graph of nodes,
        every Lean name of each node it draws (and the label of a lean4lean sorry); on the chapter
        map, the title of each chapter and every Lean name of its nodes, with the chapter's box."""
        names = {}
        if kind == 'map':
            box = {}
            for v in list(graphs.by) + list(graphs.sorry):
                layer = kinds.KINDS[graphs.kind(v)]['layer']
                box[v] = 'lean4lean' if layer == 'lean4lean' else graphs.chapter_of[v]['label']
            for c in graphs.chapters:
                if c['label'] in box.values():
                    names[f'{c["number"]} {c["title"]}'] = c['label']
            names['lean4lean'] = 'lean4lean'
            ids = list(box)
        for v in sorted(ids, key=lambda v: v in graphs.sorry):
            for n in graphs.names(v):
                names.setdefault(n, box[v] if kind == 'map' else v)
        return json.dumps(dict(sorted(names.items())))

    def annotate():
        """Kind, status and graph page on every node; the arrows plasTeX collected checked against
        the chapters; the SVG of every graph page."""
        labels = document.context.labels
        for v, (kind, status) in graphs.table.items():
            node = labels.get(v)
            if node is None:
                log.error(f'bpkinds: no plasTeX node has the label {v}')
                raise SystemExit(1)
            k = kinds.KINDS[kind]
            node.userdata.update(bp_kind=kind, bp_badge=k['badge'],
                                 bp_kind_title=f'{k["name"]}: {tex_plain(k["rule"])}',
                                 bp_status=status, bp_graph_page=page_of.get(v, ''))
            if status == 'inherits':
                node.userdata.update(
                    bp_status_badge='INHERITS ' + ', '.join(graphs.by[v]['inherited']),
                    bp_status_title='depends on these lean4lean sorries (chapter Trust boundary)')
            elif status == 'planned':
                node.userdata.update(bp_status_badge='PLANNED',
                                     bp_status_title='not formalized: the declarations do not exist')
        mine = {(u, n['label']) for n in graphs.nodes for u in n['uses'] + n['proof_uses']}
        for graph in document.userdata['dep_graph'].get('graphs', {}).values():
            graph.__class__ = KindGraph
            have = {(s.id, t.id) for s, t in graph.edges | graph.proof_edges
                    if s in graph.nodes and t in graph.nodes}
            if have != mine:
                log.error('bpkinds: the \\uses arrows plasTeX collected differ from those of the '
                          f'chapters, for example {sorted(have ^ mine)[:3]}')
                raise SystemExit(1)
        url = 'chap-trust.html#sec:trust-inherited' if any(
            c['label'] == 'chap:trust' for c in graphs.chapters) else ''
        document.userdata['bp_virtual_nodes'] = [
            dict(id='lean4lean:' + x['label'], label=x['label'], name=x['name'], what=x['what'],
                 count=len(x['nodes']), url=url) for x in graphs.sorries]
        for key, (title, svg) in graphs.svgs().items():
            if key == 'document':
                page, kind, number = kindgraph.FULL_PAGE, 'full', None
            elif key == 'chapters':
                page, kind, number = kindgraph.MAP_PAGE, 'map', None
            else:
                page, kind = kindgraph.chapter_page(key), 'chapter'
                number = next((c['number'] for c in graphs.chapters if c['label'] == key), None)
            ids = [v for v in node_ids(svg) if v in graphs.by or v in graphs.sorry]
            if kind == 'map':
                ids = [v for v in node_ids(svg)]
            short = next((f'{c["number"]}  {c["title"]}' for c in graphs.chapters
                          if c['label'] == key), title)
            pages.append(dict(key=key, title=title, short=short, page=page, kind=kind,
                              number=number, svg=svg, ids=ids))
        document.userdata['bp_graph_nav'] = [
            dict(page=p['page'], title=p['title'], short=p['short'], kind=p['kind'])
            for p in pages]
        full = next(p for p in pages if p['kind'] == 'full')
        for graph in document.userdata['dep_graph'].get('graphs', {}).values():
            graph.bp_title, graph.bp_page, graph.bp_svg = full['title'], full['page'], full['svg']
            graph.bp_search, graph.bp_kind = search_json(full['ids'], 'full'), 'full'
        document.rendererdata['html5']['extra_toc_items'].append(
            {'text': 'Dependency graph by chapter', 'url': kindgraph.MAP_PAGE})

    def legend():
        document.userdata['dep_graph']['legend'] = legend_items()

    def write_pages(document):
        """The chapter map and the chapter pages, with the template of the document graph."""
        tpl = Template(TEMPLATE.read_text(encoding='utf-8'))
        labels = document.context.labels
        files = []
        for p in pages:
            if p['kind'] == 'full':
                continue
            graph = KindGraph()
            graph.document = document
            graph.nodes = {labels[v] for v in p['ids'] if v in labels and v in graphs.by}
            graph.bp_title, graph.bp_page, graph.bp_svg = p['title'], p['page'], p['svg']
            graph.bp_search, graph.bp_kind = search_json(p['ids'], p['kind']), p['kind']
            tpl.stream(graph=graph, dot='', context=document.context, title=p['title'],
                       legend=document.userdata['dep_graph']['legend'],
                       extra_modal_links=document.userdata['dep_graph'].get(
                           'extra_modal_links_tpl', []),
                       document=document, config=document.config).dump(p['page'])
            files.append(p['page'])
        return files

    document.addPostParseCallbacks(120, annotate)
    document.addPostParseCallbacks(160, legend)
    document.addPackageResource([PackagePreCleanupCB(data=write_pages)])
