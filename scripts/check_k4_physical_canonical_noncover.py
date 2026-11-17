#!/usr/bin/env python3
"""Five-vertex triangle-free original E, physical numerical-H canonical age NON-COVER.

Literal numerical-H binary-L generator on ALL numbered old-prefix
coordinates (including odd dummies), k=ell=4, b=1, three distinct
later top originals 2,3,4, partial cut g=0 -> g=1.

Checks K4-freeness, raw/canonical endpoint ages, the strict intermediate
genuine integer-witness age H, and seven full-support attaining normalized
clique-multiplicity vectors. This is an independent finite model referee,
not a Lean theorem nor an actual recursive chosen Henson schedule.
"""
from itertools import combinations, product

N = 5
K = ELL = 4
CURRENT = 1
FUTURE = (2, 3, 4)
EDGES = ((0, 2), (1, 2), (1, 3), (1, 4))
SUPPORTS = tuple(
    U for size in (1, 2, 3)
    for U in combinations(range(3), size)
)


def make_E():
    E = [[False] * N for _ in range(N)]
    for i, j in EDGES:
        E[i][j] = E[j][i] = True
    return E


def hpos(i, q):
    return 2 * ((K + 1) * i + q)


def decode(z):
    return None if z % 2 else divmod(z // 2, K + 1)


def physical_L(E, z, w):
    a, b = decode(z), decode(w)
    if a is None or b is None or a[0] == b[0]:
        return False
    if a[0] > b[0]:
        a, b = b, a
    return E[a[0]][b[0]] and (
        a[1] < b[1] or (a[1] == K and b[1] == K)
    )


def cap(E, old_pool):
    best = 0
    for size in range(1, len(old_pool) + 1):
        if any(
            all(physical_L(E, x, y) and physical_L(E, y, x)
                for x, y in combinations(clique, 2))
            for clique in combinations(old_pool, size)
        ):
            best = size
    return best


WEIGHTS = tuple(
    w for w in product(range(ELL), repeat=3)
    if sum(w) <= ELL - 1
)


def value(w, U):
    return sum(w[i] for i in U)


def canonical(raw):
    feasible = tuple(
        w for w in WEIGHTS
        if all(value(w, U) <= raw[U] for U in SUPPORTS)
    )
    age = {
        U: max((value(w, U) for w in feasible), default=0)
        for U in SUPPORTS
    }
    return age, feasible


def main():
    E = make_E()
    assert N == len(E) and len(EDGES) == N - 1
    assert not any(
        all(E[i][j] for i, j in combinations(clique, 2))
        for clique in combinations(range(N), ELL)
    ), "original graph must be K4-free"
    assert all(j > CURRENT for j in FUTURE)
    assert len(set(FUTURE)) == 3

    ages = []
    for g in (0, 1):
        raw = {}
        for U in SUPPORTS:
            selected = [hpos(FUTURE[t], K) for t in U]
            neighbours = tuple(
                z for z in range(hpos(CURRENT, g))
                if all(physical_L(E, z, w) for w in selected)
            )
            assert all(z % 2 == 0 for z in neighbours)
            raw[U] = ELL - 1 - cap(E, neighbours)
        ages.append(raw)

    old, new = ages
    assert hpos(CURRENT, 0) == 10 and hpos(CURRENT, 1) == 12
    expected_old = dict(zip(SUPPORTS, (2, 3, 3, 3, 3, 3, 3)))
    expected_new = dict(zip(SUPPORTS, (2, 2, 2, 2, 2, 2, 2)))
    assert old == expected_old, old
    assert new == expected_new, new

    canon_old, feasible_old = canonical(old)
    canon_new, feasible_new = canonical(new)
    assert canon_old == old and canon_new == new
    assert len(feasible_old) > len(feasible_new)

    intermediate = dict(zip(SUPPORTS, (2, 2, 2, 2, 2, 2, 3)))
    canon_mid, feasible_mid = canonical(intermediate)
    assert canon_mid == intermediate, (canon_mid, intermediate)
    assert all(new[U] <= intermediate[U] <= old[U] for U in SUPPORTS)
    assert any(new[U] < intermediate[U] for U in SUPPORTS)
    assert any(intermediate[U] < old[U] for U in SUPPORTS)

    witnesses = {
        (0,): (2, 0, 0),
        (1,): (0, 2, 0),
        (2,): (0, 0, 2),
        (0, 1): (1, 1, 0),
        (0, 2): (1, 0, 1),
        (1, 2): (0, 1, 1),
        (0, 1, 2): (1, 1, 1),
    }
    for U in SUPPORTS:
        w = witnesses[U]
        assert w in feasible_mid and value(w, U) == intermediate[U]

    print("PASS: 5-vertex K4-free tree; actual H partial cut [0,10)->[0,12);"
          " canonical ages (2,3,3,3,3,3,3) >"
          " (2,2,2,2,2,2,2) have strict genuine intermediate"
          " (2,2,2,2,2,2,3). Physical canonical change is NOT a cover.")


if __name__ == "__main__":
    main()
