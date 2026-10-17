"""Planning evidence for plan section 1 (Section 5 of the paper): Havlak LNF, multi-entry edges (MEE),
irreducible-loop counts, K_n / M_n, minimal non-MEE edges.

Written during planning (Claude Opus 5.5, 2026-10-17). This is evidence, not proof: the Lean rounds R3-R4
prove the general statements. Usage: py -I validation/planning/section5_bruteforce.py [nmax=5]

Enumerates every (CFG, DFS) pair on n nodes with nodes labelled in DFS preorder: an ordered DFS tree
(parent on the rightmost path), all tree edges, and any subset of the non-tree edges a DFS with that
tree permits (forward, back, and right-to-left cross edges; no self-loops).
"""
import random
import sys
from math import comb


def trees(n):
    """Parent arrays of ordered trees on n nodes in preorder labelling."""
    if n == 1:
        yield (None,)
        return

    def rec(v, par, rightmost):
        if v == n:
            yield tuple(par)
            return
        for idx, p in enumerate(rightmost):
            yield from rec(v + 1, par + [p], rightmost[:idx + 1] + [v])

    yield from rec(1, [None], [0])


def sizes(n, par):
    size = [1] * n
    for v in range(n - 1, 0, -1):
        size[par[v]] += size[v]
    return size


def havlak(n, par, edges):
    """Havlak (TOPLAS 1997) loop nesting forest. Returns (#irreducible loops, #MEE edges, kind of root)."""
    size = sizes(n, par)
    desc = lambda a, b: a <= b < a + size[a]          # b in the DFS subtree of a
    preds = [[] for _ in range(n)]
    for (x, y) in edges:
        preds[y].append(x)
    backp = [[x for x in preds[w] if desc(w, x)] for w in range(n)]
    nonbp = [set(x for x in preds[w] if not desc(w, x)) for w in range(n)]
    uf = list(range(n))

    def find(a):
        while uf[a] != a:
            a = uf[a]
        return a

    header = [None] * n
    kind = [None] * n
    for w in range(n - 1, -1, -1):
        P = set(find(v) for v in backp[w] if v != w)
        if w in backp[w]:
            kind[w] = 'self'
        if P:
            kind[w] = 'red'
        work = list(P)
        while work:
            x = work.pop()
            for y in list(nonbp[x]):
                y2 = find(y)
                if not desc(w, y2):
                    kind[w] = 'irr'
                    nonbp[w].add(y2)
                elif y2 not in P and y2 != w:
                    P.add(y2)
                    work.append(y2)
        for x in P:
            header[x] = w
            uf[x] = w

    def inloop(w, y):          # y in L*(w) \ {w}
        h = header[y]
        while h is not None:
            if h == w:
                return True
            h = header[h]
        return False

    hdrs = [w for w in range(n) if kind[w] in ('red', 'irr')]
    irr = sum(1 for w in range(n) if kind[w] == 'irr')
    # MEE edge: enters some loop L(w) at a node other than w from a non-descendant of w (Havlak's test)
    mee = sum(1 for (x, y) in edges if any(inloop(w, y) and not desc(w, x) for w in hdrs))
    return irr, mee, kind[0]


def allowed_edges(n, par):
    size = sizes(n, par)
    desc = lambda a, b: a <= b < a + size[a]
    tree = {(par[v], v) for v in range(1, n)}
    allowed = [(x, y) for x in range(n) for y in range(n)
               if x != y and (x, y) not in tree and (desc(x, y) or desc(y, x) or y < x)]
    return tree, allowed


def kn_mn(n):
    par = [None] + list(range(n - 1))
    kn = [(x, y) for x in range(n) for y in range(n) if x != y]
    mn = [(i, i + 1) for i in range(n - 1)] + [(n - 1, i) for i in range(n - 1)] + \
         [(i, j) for i in range(n - 2) for j in range(i + 2, n)]
    mn_noroot = [e for e in mn if e != (n - 1, 0)]
    a, b, c = havlak(n, par, kn), havlak(n, par, mn), havlak(n, par, mn_noroot)
    print(f"n={n}: K_n irr={a[0]} MEE={a[1]} |E|={len(kn)}; M_n irr={b[0]} MEE={b[1]} |E|={len(mn)} "
          f"(paper (n-1)(n+2)/2={(n - 1) * (n + 2) // 2}); M_n minus (v_n,v_1): irr={c[0]} MEE={c[1]} |E|={len(mn_noroot)}")


def exhaustive(n):
    best_irr = best_mee = root_irr = 0
    min_other = None
    for par in trees(n):
        tree, allowed = allowed_edges(n, par)
        for mask in range(1 << len(allowed)):
            edges = list(tree) + [allowed[i] for i in range(len(allowed)) if mask >> i & 1]
            irr, mee, k0 = havlak(n, par, edges)
            best_irr, best_mee = max(best_irr, irr), max(best_mee, mee)
            root_irr += k0 == 'irr'
            if mee == comb(n - 1, 2) and n >= 3:
                other = len(edges) - mee
                min_other = other if min_other is None else min(min_other, other)
    print(f"n={n} exhaustive: max irreducible loops={best_irr} (n-2={n - 2}); max MEE={best_mee} "
          f"(C(n-1,2)={comb(n - 1, 2)}); root loop irreducible in {root_irr} cases; "
          f"min non-MEE edges at max MEE={min_other} (2n-3={2 * n - 3}, M_n has {2 * (n - 1)})")


def sampled(n, per_tree, seed=1):
    rng = random.Random(seed)
    best_irr = best_mee = cnt = 0
    for par in trees(n):
        tree, allowed = allowed_edges(n, par)
        for _ in range(per_tree):
            p = rng.choice([0.3, 0.5, 0.7, 0.9, 1.0])
            edges = list(tree) + [e for e in allowed if rng.random() < p]
            irr, mee, k0 = havlak(n, par, edges)
            assert k0 != 'irr'
            best_irr, best_mee, cnt = max(best_irr, irr), max(best_mee, mee), cnt + 1
    print(f"n={n} sampled ({cnt}): max irreducible loops={best_irr} (n-2={n - 2}); "
          f"max MEE={best_mee} (C(n-1,2)={comb(n - 1, 2)})")


if __name__ == '__main__':
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    for n in range(3, 10):
        kn_mn(n)
    for n in range(2, nmax + 1):
        exhaustive(n)
    sampled(6, 3000)
    sampled(7, 400)
