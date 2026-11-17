#!/usr/bin/env python3
"""Literal numerical-H K4-free counterexample: raw change without canonical change.

Genuine original graph on 7 vertices, height k=ell=4, current original
b=4 and two DISTINCT later original tops 5 and 6. The full numerical-H
binary L is evaluated on EVERY numbered old-prefix address, including
all odd dummy coordinates; the finite canonical age is computed by
enumerating ALL normalized integer 2-sort clique multiplicities.
"""

from itertools import combinations, product

N = 7
K = ELL = 4
B = 4
FUTURE = (5, 6)
EDGES = ((0, 3), (0, 5), (3, 5),
         (1, 2), (1, 6), (2, 6),
         (4, 5), (4, 6))
SUPPORTS = ((0,), (1,), (0, 1))


def original_graph():
    E = [[False] * N for _ in range(N)]
    for i, j in EDGES:
        E[i][j] = E[j][i] = True
    return E


def hpos(i, q):
    return 2 * ((K + 1) * i + q)


def real(z):
    if z % 2:
        return None
    return divmod(z // 2, K + 1)


def physical_edge(E, z, w):
    a, b = real(z), real(w)
    if a is None or b is None or a[0] == b[0]:
        return False
    if a[0] > b[0]:
        a, b = b, a
    return E[a[0]][b[0]] and (
        a[1] < b[1] or (a[1] == K and b[1] == K)
    )


def clique_capacity(E, pool):
    best = 0
    for size in range(1, len(pool) + 1):
        for subset in combinations(pool, size):
            if all(physical_edge(E, x, y) and physical_edge(E, y, x)
                   for x, y in combinations(subset, 2)):
                best = max(best, size)
    return best


def canonical_age(raw):
    all_vectors = (
        w for w in product(range(ELL), repeat=2)
        if sum(w) <= ELL - 1
    )
    feasible = tuple(
        w for w in all_vectors
        if all(sum(w[t] for t in U) <= raw[U] for U in SUPPORTS)
    )
    canonical = {
        U: max((sum(w[t] for t in U) for w in feasible), default=0)
        for U in SUPPORTS
    }
    return canonical, feasible


def main():
    E = original_graph()
    assert not any(
        all(E[i][j] for i, j in combinations(S, 2))
        for S in combinations(range(N), ELL)
    ), "the source graph must be K4-free"
    assert len(set(FUTURE)) == 2 and all(x > B for x in FUTURE)

    raws = []
    pools = []
    for g in (0, 1):
        prefix = range(hpos(B, g))
        pool_by_support = {}
        raw_by_support = {}
        for U in SUPPORTS:
            pool = tuple(
                z for z in prefix
                if all(physical_edge(E, z, hpos(FUTURE[t], K))
                       for t in U)
            )
            pool_by_support[U] = pool
            raw_by_support[U] = ELL - 1 - clique_capacity(E, pool)
        pools.append(pool_by_support)
        raws.append(raw_by_support)

    assert hpos(B, 0) == 40 and hpos(B, 1) == 42
    assert raws[0] == {(0,): 1, (1,): 1, (0, 1): 3}, raws[0]
    assert raws[1] == {(0,): 1, (1,): 1, (0, 1): 2}, raws[1]
    assert pools[0][(0, 1)] == ()
    assert pools[1][(0, 1)] == (hpos(B, 0),)
    assert all(z % 2 == 0 for g in pools for x in g.values() for z in x)

    before, feasible_before = canonical_age(raws[0])
    after, feasible_after = canonical_age(raws[1])
    expected = {(0,): 1, (1,): 1, (0, 1): 2}
    assert before == expected and after == expected
    expected_vectors = {(0, 0), (1, 0), (0, 1), (1, 1)}
    assert set(feasible_before) == expected_vectors
    assert set(feasible_after) == expected_vectors

    old_changed_bound = raws[0][(0, 1)]
    assert old_changed_bound == 3
    assert not any(
        sum(w[t] for t in (0, 1)) == old_changed_bound
        for w in feasible_before
    ), "the old raw event must have no globally feasible saturating vector"

    print(
        "PASS: K4-free source on 7 distinct original vertices; "
        "actual numeric-H cut [0,40)->[0,42) changes joint raw "
        "bound 3->2 but canonical age stays (1,1,2); "
        "the old feasible multiplicity family is unchanged"
    )


if __name__ == "__main__":
    main()
