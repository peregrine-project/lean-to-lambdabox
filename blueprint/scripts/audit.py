#!/usr/bin/env python3
"""Mechanical audit of the blueprint against the Lean development.

Run from anywhere, after `lake build`:

    python3 blueprint/scripts/audit.py

Checks, over blueprint/src/chapters/*.tex:
  * every graph node (definition/lemma/proposition/theorem/corollary/assumption) has a
    \\label whose prefix matches its environment, defined once, free of dots and primes;
  * every \\uses label resolves, no node uses itself, and the \\uses graph is acyclic
    (a cycle makes `leanblueprint web` die with a RecursionError);
  * annotation policy: \\leanok in a statement iff \\lean is present; result nodes carry a
    proof with \\leanok; definition and assumption nodes carry no proof;
  * no Lean declaration is cited by two nodes;
  * every cited declaration exists, and the trust edges agree with `#print axioms`
    measured on every cited name: a result node uses asm:lean4lean-trust iff one of its
    declarations depends on sorryAx, and asm:lean-reflection-axioms iff one depends on an
    axiom other than propext / Classical.choice / Quot.sound / sorryAx;
  * source hygiene: non-ASCII characters outside \\lean{}, unescaped underscores in
    \\code / \\texttt.

Writes blueprint/.audit/report.md, index.md (label -> chapter, kind, declarations) and
axioms.json (the measured footprints). Exit status 1 if any defect is found.
"""
import collections, glob, json, os, re, subprocess, sys

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
OUT = os.path.join(REPO, 'blueprint', '.audit')
KINDS = ['definition', 'lemma', 'proposition', 'theorem', 'corollary', 'assumption']
PREFIX = dict(definition='def', lemma='lem', proposition='prop', theorem='thm',
              corollary='cor', assumption='asm')
STD = {'propext', 'Classical.choice', 'Quot.sound'}
TRUST, REFL = 'asm:lean4lean-trust', 'asm:lean-reflection-axioms'
node_re = re.compile(r'\\begin\{(%s)\}(.*?)\\end\{\1\}' % '|'.join(KINDS), re.S)
proof_re = re.compile(r'\\begin\{proof\}(.*?)\\end\{proof\}', re.S)


def items(macro, txt):
    out = []
    for m in re.finditer(r'\\%s\{([^}]*)\}' % macro, txt, re.S):
        out += [x.strip() for x in m.group(1).replace('\n', ' ').split(',') if x.strip()]
    return out


def parse():
    nodes, defects = [], collections.defaultdict(list)
    for path in sorted(glob.glob(os.path.join(REPO, 'blueprint/src/chapters/*.tex'))):
        ch = os.path.basename(path)
        raw = open(path, encoding='utf-8').read()
        for i, line in enumerate(raw.split('\n'), 1):
            bare = re.sub(r'\\lean\{[^}]*\}', '', line)
            if any(ord(c) > 127 for c in bare):
                defects[ch].append(f'L{i}: non-ASCII character outside \\lean{{}}')
            for m in re.finditer(r'\\(?:code|texttt)\{([^{}]*)\}', line):
                if re.search(r'(?<!\\)_', m.group(1)):
                    defects[ch].append(f'L{i}: unescaped underscore in {m.group(0)[:60]}')
        txt = re.sub(r'(?<!\\)%.*', '', raw)
        events = [(m.start(), 'node', m) for m in node_re.finditer(txt)]
        events += [(m.start(), 'proof', m) for m in proof_re.finditer(txt)]
        last = None
        for pos, what, m in sorted(events, key=lambda e: e[0]):
            line = txt.count('\n', 0, pos) + 1
            if what == 'node':
                body = m.group(2)
                labels = re.findall(r'\\label\{([^}]*)\}', body)
                last = dict(ch=ch, line=line, kind=m.group(1), label=labels[0] if labels else None,
                            lean=items('lean', body), leanok=bool(re.search(r'\\leanok\b', body)),
                            uses=items('uses', body), proof=False, proof_leanok=False, proof_uses=[])
                nodes.append(last)
                continue
            body = m.group(1)
            target = last
            proves = re.findall(r'\\proves\{([^}]*)\}', body)
            if proves:
                hit = [n for n in nodes if n['label'] == proves[0]]
                target = hit[0] if hit else None
            if target is None:
                defects[ch].append(f'L{line}: proof environment with no node to attach to')
                continue
            if target['proof']:
                defects[ch].append(f'L{line}: second proof attached to {target["label"]}')
            target.update(proof=True, proof_leanok=bool(re.search(r'\\leanok\b', body)),
                          proof_uses=items('uses', body))
    return nodes, defects


def measure(names):
    os.makedirs(OUT, exist_ok=True)
    probe = os.path.join(OUT, 'Probe.lean')
    with open(probe, 'w', encoding='utf-8') as f:
        f.write('import LeanToLambdaBox\nset_option maxHeartbeats 0\n')
        f.writelines(f'#print axioms {d}\n' for d in names)
    out = subprocess.run(['lake', 'env', 'lean', probe], cwd=REPO, capture_output=True, text=True).stdout
    ax = {}
    for m in re.finditer(r"^'(.*)' depends on axioms: \[([^\]]*)\]", out, re.M):
        ax[m.group(1)] = sorted(x.strip() for x in m.group(2).replace('\n', ' ').split(','))
    for m in re.finditer(r"^'(.*)' does not depend on any axioms", out, re.M):
        ax[m.group(1)] = []
    return ax


def cycles(graph):
    sys.setrecursionlimit(100000)
    index, low, stack, on, found, counter = {}, {}, [], set(), [], [0]

    def visit(v):
        index[v] = low[v] = counter[0]; counter[0] += 1; stack.append(v); on.add(v)
        for w in graph[v]:
            if w not in index:
                visit(w); low[v] = min(low[v], low[w])
            elif w in on:
                low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            comp = []
            while True:
                w = stack.pop(); on.discard(w); comp.append(w)
                if w == v:
                    break
            if len(comp) > 1:
                found.append(comp)
    for v in graph:
        if v not in index:
            visit(v)
    return found


def main():
    nodes, defects = parse()
    count = collections.Counter(n['label'] for n in nodes if n['label'])
    for n in nodes:
        ch, tag = n['ch'], f'L{n["line"]} {n["label"]}'
        if not n['label']:
            defects[ch].append(f'L{n["line"]} {n["kind"]}: node has no \\label'); continue
        if count[n['label']] > 1:
            defects[ch].append(f'{tag}: label defined {count[n["label"]]} times')
        if not n['label'].startswith(PREFIX[n['kind']] + ':'):
            defects[ch].append(f'{tag}: label prefix does not match environment {n["kind"]}')
        if re.search(r"[.'\s]", n['label']):
            defects[ch].append(f'{tag}: label contains a dot, prime or space')
        for u in n['uses'] + n['proof_uses']:
            if u not in count:
                defects[ch].append(f'{tag}: \\uses{{{u}}} does not resolve')
            if u == n['label']:
                defects[ch].append(f'{tag}: node uses itself')
        if bool(n['lean']) != n['leanok']:
            defects[ch].append(f'{tag}: statement \\leanok must be present iff \\lean is')
        if n['kind'] in ('definition', 'assumption'):
            if n['proof']:
                defects[ch].append(f'{tag}: {n["kind"]} node carries a proof environment')
        elif not n['proof']:
            defects[ch].append(f'{tag}: result node has no proof environment')
        elif bool(n['lean']) != n['proof_leanok']:
            defects[ch].append(f'{tag}: proof \\leanok must be present iff the node cites Lean')
    owners = collections.defaultdict(list)
    for n in nodes:
        for d in n['lean']:
            owners[d].append(n)
    for d, ns in owners.items():
        if len(ns) > 1:
            defects[ns[0]['ch']].append(f'{d} is cited by {len(ns)} nodes: ' + ', '.join(x['label'] for x in ns))
    graph = {n['label']: {u for u in n['uses'] + n['proof_uses'] if u in count} for n in nodes if n['label']}
    for comp in cycles(graph):
        defects['(graph)'].append('dependency cycle: ' + ' , '.join(sorted(comp)))
    ax = measure(sorted(owners))
    for n in nodes:
        ch, tag = n['ch'], f'L{n["line"]} {n["label"]}'
        for d in n['lean']:
            if d not in ax:
                defects[ch].append(f'{tag}: {d} is not a declaration of the environment')
        if n['kind'] in ('definition', 'assumption') or not n['lean']:
            continue
        fp = set().union(*[set(ax.get(d, [])) for d in n['lean']])
        used = set(n['uses'] + n['proof_uses'])
        if ('sorryAx' in fp) != (TRUST in used):
            defects[ch].append(f'{tag}: measured sorryAx={"sorryAx" in fp} but {TRUST} used={TRUST in used}')
        if bool(fp - STD - {'sorryAx'}) != (REFL in used):
            defects[ch].append(f'{tag}: measured non-standard axioms={bool(fp - STD - {"sorryAx"})} but {REFL} used={REFL in used}')
    total = sum(len(v) for v in defects.values())
    with open(os.path.join(OUT, 'report.md'), 'w') as f:
        f.write(f'# Blueprint audit: {len(nodes)} nodes, {len(owners)} Lean declarations, {total} defects\n')
        for ch in sorted(defects):
            f.write(f'\n## {ch}\n' + ''.join(f'- {d}\n' for d in defects[ch]))
    with open(os.path.join(OUT, 'index.md'), 'w', encoding='utf-8') as f:
        f.write('| label | chapter | kind | Lean declarations |\n|---|---|---|---|\n')
        f.writelines(f"| {n['label']} | {n['ch']} | {n['kind']} | {', '.join(n['lean'])} |\n" for n in nodes)
    json.dump(ax, open(os.path.join(OUT, 'axioms.json'), 'w'), indent=1, ensure_ascii=False)
    print(f'{len(nodes)} nodes, {len(owners)} Lean declarations, {total} defects -> blueprint/.audit/report.md')
    for ch in sorted(defects):
        for d in defects[ch]:
            print(f'  {ch}: {d}')
    return 1 if total else 0


if __name__ == '__main__':
    sys.exit(main())
