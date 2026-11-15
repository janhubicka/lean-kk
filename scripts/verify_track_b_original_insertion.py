#!/usr/bin/env python3
"""Independent finite directed-graph audit of Track B's exact original insertion.

No imports from the diary generator, Lean or Mathlib. Tests ALL loop-free directed
edge tables of size <=3, ALL one- and two-sort columns, ALL fresh inserted
vertices/old pools and ALL nonempty sort supports, plus 12,000 random cases
of size <=6. No assertion of unbounded resolved-copy validity is made.
"""
from itertools import combinations
from random import Random


def capacity(E, vertices):
    V = tuple(sorted(vertices))
    return max(len(S) for n in range(len(V) + 1)
               for S in combinations(V, n)
               if all(E[x][y] and E[y][x] for x, y in combinations(S, 2)))


def common_pool(P, columns, U):
    return {p for p in P if all(columns[p][t] for t in U)}


def check_case(E, columns, d, P, v, U):
    assert v not in P and U and all(0 <= t < d for t in U)
    old = common_pool(P, columns, U)
    new = common_pool(P | {v}, columns, U)
    live = all(columns[v][t] for t in U)
    assert new == (old | {v} if live else old)
    mutual = {x for x in old if E[x][v] and E[v][x]}
    old_cap = capacity(E, old)
    new_cap = capacity(E, new)
    expected = max(old_cap, 1 + capacity(E, mutual)) if live else old_cap
    assert new_cap == expected
    assert new_cap >= old_cap
    for ell in (2, 3, 4, 5):
        old_raw = max(0, ell - 1 - old_cap)
        new_raw = max(0, ell - 1 - new_cap)
        assert new_raw <= old_raw
        if not live:
            assert old_raw == new_raw
        if live and 1 + capacity(E, mutual) <= old_cap:
            assert old_raw == new_raw
        if live and new_cap < ell:
            # For a physically forbidden-free prefix there is no clipping ambiguity.
            assert (old_raw == new_raw) == (1 + capacity(E, mutual) <= old_cap)


def all_tables(n):
    ordered = [(i, j) for i in range(n) for j in range(n) if i != j]
    for bits in range(1 << len(ordered)):
        E = [[False] * n for _ in range(n)]
        for ix, (i, j) in enumerate(ordered):
            E[i][j] = bool((bits >> ix) & 1)
        yield E


def all_columns(n, d):
    for bits in range(1 << (n * d)):
        yield [[bool((bits >> (p * d + t)) & 1) for t in range(d)] for p in range(n)]


def exhaustive():
    tested = 0
    for n in (1, 2, 3):
        for E in all_tables(n):
            for d in (1, 2):
                supports = [{t for t in range(d) if mask & (1 << t)}
                            for mask in range(1, 1 << d)]
                for columns in all_columns(n, d):
                    for v in range(n):
                        other = [x for x in range(n) if x != v]
                        for pmask in range(1 << len(other)):
                            P = {p for ix, p in enumerate(other) if pmask & (1 << ix)}
                            for U in supports:
                                check_case(E, columns, d, P, v, U)
                                tested += 1
    assert tested == 154446, tested
    return tested


def randomized():
    rng = Random(15026)
    tested = 0
    for n in range(1, 7):
        for _ in range(2000):
            E = [[False if i == j else bool(rng.getrandbits(1))
                  for j in range(n)] for i in range(n)]
            d = rng.randint(1, 4)
            columns = [[bool(rng.getrandbits(1)) for t in range(d)] for p in range(n)]
            v = rng.randrange(n)
            P = {p for p in range(n) if p != v and rng.getrandbits(1)}
            U = {t for t in range(d) if rng.getrandbits(1)}
            if not U:
                U.add(rng.randrange(d))
            check_case(E, columns, d, P, v, U)
            tested += 1
    assert tested == 12000, tested
    return tested


def regressions():
    # Positive future column can be neutral when the new original is old-isolated.
    n = 3
    all_positive = [[True] for _ in range(n)]
    empty = [[False] * n for _ in range(n)]
    assert capacity(empty, {0, 1}) == capacity(empty, {0, 1, 2}) == 1
    check_case(empty, all_positive, 1, {0, 1}, 2, {0})

    # Identical future columns, different true old-v links: age drops.
    attached = [[False] * n for _ in range(n)]
    attached[0][2] = attached[2][0] = True
    assert capacity(attached, {0, 1}) == 1
    assert capacity(attached, {0, 1, 2}) == 2
    check_case(attached, all_positive, 1, {0, 1}, 2, {0})

    # Without forbidden-clique-free safety, clipped raw ages cannot detect growth.
    clique4 = [[i != j for j in range(4)] for i in range(4)]
    assert capacity(clique4, {0, 1, 2}) == 3
    assert capacity(clique4, {0, 1, 2, 3}) == 4
    assert max(0, 3 - capacity(clique4, {0, 1, 2})) == \
           max(0, 3 - capacity(clique4, {0, 1, 2, 3})) == 0


if __name__ == '__main__':
    a = exhaustive()
    b = randomized()
    regressions()
    print(f'PASS: {a} exhaustive directed cases, {b} random cases, three K4 regressions')
