#!/usr/bin/env python3
"""Exhaustively test the *finite graph combinatorics* of Track F rank drop.

No diagram, diary counter, published BRD theorem, or Henson oracle is used.
The existence of a vertex in a fixed infinite Henson enumeration is NOT tested.
"""
from itertools import combinations


def graph_edges(n, bits):
    return {(i, j) for k, (i, j) in enumerate(combinations(range(n), 2))
            if (bits >> k) & 1}


def is_clique(subset, edges):
    return all((min(i, j), max(i, j)) in edges
               for i, j in combinations(subset, 2))


def clique_capacity(subset, edges):
    for k in range(len(subset), -1, -1):
        if any(is_clique(s, edges) for s in combinations(subset, k)):
            return k
    raise AssertionError('empty set should be clique')


def verify(max_old=5, ells=range(3, 7)):
    tested = 0
    maximal_choices = 0
    rejected_rank_one = 0
    for ell in ells:
        for n in range(max_old + 1):
            for bits in range(1 << (n * (n - 1) // 2)):
                edges = graph_edges(n, bits)
                if clique_capacity(tuple(range(n)), edges) >= ell:
                    continue
                for mask in range(1 << n):
                    U = tuple(i for i in range(n) if (mask >> i) & 1)
                    cap = clique_capacity(U, edges)
                    if cap + 3 > ell:
                        rejected_rank_one += 1
                        continue
                    tested += 1
                    Cchoices = (tuple(s) for s in combinations(U, cap)
                                if is_clique(s, edges))
                    for C in Cchoices:
                        maximal_choices += 1
                        extended = edges | {(x, n) for x in C}
                        newU = tuple(U) + (n,)
                        assert clique_capacity(tuple(range(n + 1)), extended) < ell, (ell, n, bits, U, C)
                        assert clique_capacity(newU, extended) == cap + 1, (ell, n, bits, U, C)
                        assert clique_capacity(newU, extended) < ell - 1, (ell, n, bits, U, C)
    return tested, maximal_choices, rejected_rank_one


if __name__ == '__main__':
    cases, choices, excluded = verify()
    assert (cases, choices, excluded) == (76873, 121179, 35707), (cases, choices, excluded)
    print(f'PASS: {cases:,} old safe rank-positive types, '
          f'{choices:,} distinct maximal clique certificates; '
          f'{excluded:,} cases outside the rank>=2 hypothesis')
    # Boundary: an edge-neighbourhood in a K4-free prefix has cap=2,
    # hence extending its maximal clique gives a forbidden rank-zero type.
    edge = {(0, 1)}
    bad = edge | {(0, 2), (1, 2)}
    assert clique_capacity((0, 1), edge) == 2
    assert clique_capacity((0, 1, 2), bad) == 3
    print('PASS: omitted-rank-hypothesis counterexample for ell=4')
