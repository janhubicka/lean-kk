#!/usr/bin/env python3
"""Independent finite referee for Track A's K_ell-free partial-age sharpening.

Enumerates loopless undirected original graphs through five vertices, all
nonempty (one- or two-top) later support choices, and their physical single-jump
raw support arithmetic. Not a Lean kernel proof.
"""
from itertools import combinations

def capacity(adj, pool):
    pool = sorted(pool)
    return max((len(s) for r in range(len(pool) + 1)
                for s in combinations(pool, r)
                if all(adj[i][j] for i, j in combinations(s, 2))),
               default=0)

checked = equal_cap = checked_stability = 0
for n in range(2, 6):
    edge_list = list(combinations(range(n), 2))
    for mask in range(1 << len(edge_list)):
        adj = [[False] * n for _ in range(n)]
        for q, (i, j) in enumerate(edge_list):
            if (mask >> q) & 1:
                adj[i][j] = adj[j][i] = True
        for ell in range(2, min(n + 1, 6)):
            if capacity(adj, range(n)) >= ell:
                continue
            for b in range(n - 1):
                for size in (1, 2):
                    for tops in combinations(range(b + 1, n), size):
                        P = {i for i in range(b)
                             if all(adj[i][t] for t in tops)}
                        S = {i for i in P if adj[i][b]}
                        p, c = capacity(adj, P), capacity(adj, S)
                        eligible = all(adj[b][t] for t in tops)
                        checked += 1
                        if eligible and c == p:
                            assert p + 2 < ell, (n, mask, ell, b, tops, p)
                            equal_cap += 1
                        for g in range(max(0, ell - 2), ell + 2):
                            for h in range(g, ell + 2):
                                before = (ell - 1) - min(ell - 1,
                                    p + int(eligible and c == p and p < g))
                                after = (ell - 1) - min(ell - 1,
                                    p + int(eligible and c == p and p < h))
                                assert after == before, (
                                    n, mask, ell, b, tops, g, h, before, after)
                                checked_stability += 1
print(f"PASS: {checked} support instances, {equal_cap} "
      f"eligible equal-capacity instances, "
      f"{checked_stability} late-cut comparisons")

# Uniform sharpness: the original K_(ell-1) demonstrates a raw drop
# from generation ell-3 to ell-2 for every ell>=3.
for ell in range(3, 9):
    n = ell - 1
    adj = [[i != j for j in range(n)] for i in range(n)]
    b, t = ell - 3, ell - 2
    P = {i for i in range(b) if adj[i][t]}
    S = {i for i in P if adj[i][b]}
    p, c = capacity(adj, P), capacity(adj, S)
    assert p == c == ell - 3
    before = ell - 1 - (p + int(p < ell - 3))
    after = ell - 1 - (p + int(p < ell - 2))
    assert (before, after) == (2, 1), (ell, before, after)
print("PASS: sharp raw drop at ell-3 -> ell-2 for ell=3..8")
