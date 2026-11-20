#!/usr/bin/env python3
"""Independent brute-force referee for Track A canonical singleton sharpness.

For ell=3..8 generate a genuine K_ell-free ordered graph with ell-2
canonically visible distinct ordinary-L age changes in one numerical H
block. Enumerate ALL normalized integer clique vectors and admissible
supports at every cut. This does not replace a Lean proof.
"""
from itertools import combinations

def capacity(adj, pool):
    pool = tuple(pool)
    return max((len(S) for n in range(len(pool) + 1)
                for S in combinations(pool, n)
                if all(adj[x][y] and adj[y][x]
                       for x, y in combinations(S, 2))), default=0)

def graph_for(ell):
    b, d = ell - 3, ell - 2
    n = b + 1 + d
    a = [[False] * n for _ in range(n)]
    def link(i, j):
        assert i != j
        a[i][j] = a[j][i] = True
    for i, j in combinations(range(b + 1), 2):
        link(i, j)
    later = []
    for p in range(d):
        j = b + 1 + p
        later.append(j)
        link(b, j)
        for i in range(p):
            link(i, j)
    return a, b, later

def normalized_weights(d, ell):
    def rec(i, rem, prefix):
        if i == d:
            yield tuple(prefix)
        else:
            for x in range(rem + 1):
                prefix.append(x)
                yield from rec(i + 1, rem - x, prefix)
                prefix.pop()
    return list(rec(0, ell - 1, []))

def check(ell):
    a, b, later = graph_for(ell)
    d = ell - 2
    assert capacity(a, range(len(a))) == ell - 1, ell
    supports = [U for s in range(1, min(d, ell - 1) + 1)
                for U in combinations(range(d), s)]
    weights = normalized_weights(d, ell)
    raws, singles = [], []
    for g in range(ell - 1):
        raw = {}
        for U in supports:
            P = [i for i in range(b) if all(a[i][later[t]] for t in U)]
            S = [i for i in P if a[i][b]]
            p, c = capacity(a, P), capacity(a, S)
            eligible = all(a[b][later[t]] for t in U)
            raw[U] = ell - 1 - (p + int(eligible and c == p and p < g))
        feasible = [w for w in weights if all(
            sum(w[t] for t in U) <= raw[U] for U in supports)]
        assert feasible
        canonical_singletons = [max(w[t] for w in feasible) for t in range(d)]
        raw_singletons = [raw[(t,)] for t in range(d)]
        assert canonical_singletons == raw_singletons, (ell, g)
        for t in range(d):
            assert raw[(t,)] == ell - 1 - t - int(g > t), (ell, g, t)
        raws.append(raw)
        singles.append(canonical_singletons)
    assert [g for g in range(d) if raws[g] != raws[g+1]] == list(range(d))
    assert [g for g in range(d) if singles[g] != singles[g+1]] == list(range(d))
    return len(a), len(supports), len(weights), len(raws)

if __name__ == '__main__':
    for ell in range(3, 9):
        n, ns, nw, cuts = check(ell)
        print(f'ell={ell}: PASS n={n}, supports={ns}, weights={nw}, '
              f'cuts={cuts}, canonical_changes={ell-2}')
