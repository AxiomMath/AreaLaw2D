#!/usr/bin/env python3
"""Compare the rendered dependency graph with the DAG of digest/00-overview.md §2.1.

Reads the graph of the built site (`_out/site/html-multi/-verso-data/blueprint-manifest.json`,
after `lake exe vbp build`) and the DAG's `X <- Y, Z` lines; prints every edge in one and not
the other, and every cycle of the rendered graph. Exit status 1 if there is any.
"""
import json, os, re, sys, collections

HERE = os.path.dirname(os.path.abspath(__file__))
BP = os.path.dirname(HERE)
ROOT = os.path.dirname(BP)
ID = r'D\d+\.\d+'


def ids(part):
    out = []
    part = re.sub(r'\[[^\]]*\]', '', part)
    for m in re.finditer(rf'({ID})(?:\s*\([^)]*\))?(?:\s*-\s*({ID}))?', part):
        a = m.group(1)
        if m.group(2):
            s, n = a[1:].split('.')
            s2, n2 = m.group(2)[1:].split('.')
            assert s == s2, part
            out += [f'D{s}.{k}' for k in range(int(n), int(n2) + 1)]
        else:
            out.append(a)
    return out


def dag_edges():
    ov = open(os.path.join(ROOT, 'digest/00-overview.md')).read()
    txt = ov.split('### 2.1 Dependency DAG', 1)[1].split('```', 2)[1]
    dag, last = set(), []
    for line in txt.split('\n'):
        line = line.split('#', 1)[0].rstrip()
        if not line.strip():
            continue
        if line.strip().startswith('+'):          # continuation of the previous head
            dag |= {(h, y) for h in last for y in ids(line)}
            continue
        if (':=' in line or '==' in line) and '<-' not in line:   # one node, two names
            continue
        line = re.sub(r'^\s*(internal(?: \([a-z]\))?|rough upper|sharp upper|lower|identity)\s*:', ' ', line)
        for seg in re.split(r'\s{2,}', line.strip()):
            if '<-' not in seg:
                continue
            chain = seg.split('<-')
            for i in range(len(chain) - 1):
                heads = ids(chain[i]) if i == 0 else ids(chain[i])[-1:]
                dag |= {(h, y) for h in heads for y in ids(chain[i + 1]) if y != h}
                if i == 0:
                    last = heads
    return dag


def rendered_edges():
    p = os.path.join(BP, '_out/site/html-multi/-verso-data/blueprint-manifest.json')
    g = json.load(open(p))['graphs'][0]
    lab = lambda s: s.strip('«»')
    nodes = {lab(n['label']) for n in g['nodes']}
    return nodes, {(lab(e['target']), lab(e['source'])) for e in g['edges']}


def cycles(edges):
    adj = collections.defaultdict(set)
    for x, y in edges:
        adj[x].add(y)
    color, stack, found = {}, [], []

    def dfs(u):
        color[u] = 1
        stack.append(u)
        for v in adj[u]:
            if color.get(v) == 1:
                found.append(stack[stack.index(v):] + [v])
            elif not color.get(v):
                dfs(v)
        stack.pop()
        color[u] = 2
    sys.setrecursionlimit(10000)
    for u in list(adj):
        if not color.get(u):
            dfs(u)
    return found


def main():
    nodes, bp = rendered_edges()
    dag = dag_edges()
    # a DAG edge to an anchor without a blueprint node (no Lean declaration) cannot be drawn
    dag_drawable = {(x, y) for x, y in dag if x in nodes and y in nodes}
    undrawable = sorted(dag - dag_drawable)
    only_dag = sorted(dag_drawable - bp)
    only_bp = sorted(bp - dag)
    cyc = cycles(bp)
    print(f'rendered graph: {len(nodes)} nodes, {len(bp)} edges; DAG §2.1: {len(dag)} edges')
    for x, y in undrawable:
        print(f'  DAG edge to an anchor without a node: {x} <- {y}')
    for x, y in only_dag:
        print(f'  in the DAG, not in the graph: {x} <- {y}')
    for x, y in only_bp:
        print(f'  in the graph, not in the DAG: {x} <- {y}')
    for c in cyc:
        print('  cycle: ' + ' <- '.join(c))
    ok = not (only_dag or only_bp or cyc)
    print('graph = DAG' if ok else 'graph != DAG')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
