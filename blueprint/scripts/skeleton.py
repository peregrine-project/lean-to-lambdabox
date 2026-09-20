#!/usr/bin/env python3
"""skeleton.py CHAPTER.tex — compare the graph skeleton of the working file with the committed (HEAD) version.
The skeleton must be IDENTICAL after a readability rewrite: same nodes in the same order, same environment
kind, \\label, \\lean list, \\leanok flags, \\uses lists (statement and proof), and no \\label lost anywhere."""
import re, subprocess, sys, os
KINDS='definition|lemma|proposition|theorem|corollary|assumption'
node_re=re.compile(r'\\begin\{(%s)\}(.*?)\\end\{\1\}'%KINDS,re.S); proof_re=re.compile(r'\\begin\{proof\}(.*?)\\end\{proof\}',re.S)
def items(mac,t):
    out=[]
    for m in re.finditer(r'\\%s\{([^}]*)\}'%mac,t,re.S): out+=[x.strip() for x in m.group(1).replace('\n',' ').split(',') if x.strip()]
    return out
def skel(txt):
    txt=re.sub(r'(?<!\\)%.*','',txt)
    ev=[(m.start(),'n',m) for m in node_re.finditer(txt)]+[(m.start(),'p',m) for m in proof_re.finditer(txt)]
    nodes=[];last=None
    for pos,k,m in sorted(ev,key=lambda e:e[0]):
        if k=='n':
            b=m.group(2); nested='\\begin{proof}' in b
            lab=re.findall(r'\\label\{([^}]*)\}',b)
            last=dict(kind=m.group(1),label=lab[0] if lab else None,lean=items('lean',b),leanok=bool(re.search(r'\\leanok\b',b)),uses=sorted(items('uses',b)),proof=None,nested=nested); nodes.append(last)
        elif last is not None:
            b=m.group(1); last['proof']=dict(leanok=bool(re.search(r'\\leanok\b',b)),uses=sorted(items('uses',b)))
    labels=sorted(set(re.findall(r'\\label\{([^}]*)\}',txt)))
    return nodes,labels
path=sys.argv[1]; rel=os.path.relpath(path,subprocess.run(['git','rev-parse','--show-toplevel'],capture_output=True,text=True,cwd=os.path.dirname(os.path.abspath(path))).stdout.strip())
top=subprocess.run(['git','rev-parse','--show-toplevel'],capture_output=True,text=True,cwd=os.path.dirname(os.path.abspath(path))).stdout.strip()
ref=sys.argv[2] if len(sys.argv)>2 else 'HEAD'
old=subprocess.run(['git','show',f'{ref}:{rel}'],capture_output=True,text=True,cwd=top).stdout
new=open(path,encoding='utf-8').read()
on,ol=skel(old); nn,nl=skel(new); bad=0
if [n['label'] for n in on]!=[n['label'] for n in nn]:
    print('NODE SEQUENCE DIFFERS'); bad+=1
    print('  missing:',[l for l in [n['label'] for n in on] if l not in [x['label'] for x in nn]])
    print('  added  :',[l for l in [n['label'] for n in nn] if l not in [x['label'] for x in on]])
om={n['label']:n for n in on}
for n in nn:
    o=om.get(n['label'])
    if not o: continue
    for k in ('kind','lean','leanok','uses','proof'):
        if o[k]!=n[k]: print(f"{n['label']}: {k} changed\n   old={o[k]}\n   new={n[k]}"); bad+=1
    if n['nested']: print(f"{n['label']}: proof is NESTED inside the statement environment (must follow \\end{{{n['kind']}}})"); bad+=1
lost=[l for l in ol if l not in nl]
if lost: print('LABELS LOST:',lost); bad+=1
nonascii=[(i,l) for i,l in enumerate(new.split('\n'),1) if any(ord(c)>127 for c in re.sub(r'\\lean\{[^}]*\}','',l))]
for i,l in nonascii[:10]: print(f'L{i}: non-ASCII character'); bad+=1
for i,l in enumerate(new.split('\n'),1):
    for m in re.finditer(r'\\(?:code|texttt)\{([^{}]*)\}',l):
        if re.search(r'(?<!\\)_',m.group(1)): print(f'L{i}: unescaped underscore in {m.group(0)[:50]}'); bad+=1
if new.count('\\begin{')!=new.count('\\end{'): print('UNBALANCED begin/end:',new.count('\\begin{'),new.count('\\end{')); bad+=1
ow=len(old.split()); nw=len(new.split())
print(f'words: {ow} -> {nw} ({100*nw//max(ow,1)}%)   nodes: {len(on)} -> {len(nn)}   itemize/enumerate/description: {len(re.findall(r"begin.(itemize|enumerate|description)",new))}   tables: {new.count("begin{tabular}")}')
print('SKELETON OK' if not bad else f'SKELETON BROKEN: {bad} problem(s)')
sys.exit(1 if bad else 0)
