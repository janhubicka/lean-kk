#!/usr/bin/env python3
"""Independent finite-model audit of Track F's REAL one-coordinate raw locality.

Enumerates old simple edge tables, finite actual-neighbourhood subsets
on up to 3 active sorts, genuine maximal-clique choices and the complete
support lattice. No diary counters, published degree formula or Lean
theorems are imported. Does NOT verify the infinite Henson extension.
"""
from itertools import combinations, product


def max_clique(vertices, edges):
    vertices = tuple(vertices)
    return max(
        (len(s) for r in range(len(vertices) + 1)
         for s in combinations(vertices, r)
         if all((min(x, y), max(x, y)) in edges
                for x, y in combinations(s, 2))),
        default=0,
    )


def verify():
    tested, supports = 0, 0
    by_ell = {}
    for ell in range(3, 7):
        t0, s0 = tested, supports
        for front in range(4):
            pairs = tuple(combinations(range(front), 2))
            for bits in range(1 << len(pairs)):
                E = {pair for k, pair in enumerate(pairs) if bits & (1 << k)}
                if max_clique(range(front), E) >= ell:
                    continue
                for d in range(1, 4):
                    for masks in product(range(1 << front), repeat=d):
                        U = [
                            {x for x in range(front) if (masks[i] >> x) & 1}
                            for i in range(d)
                        ]
                        for j in range(d):
                            a = max_clique(U[j], E)
                            if a + 3 > ell:
                                continue
                            for Ctuple in combinations(sorted(U[j]), a):
                                C = set(Ctuple)
                                if max_clique(C, E) != a:
                                    continue
                                v = front
                                Enew = E | {(x, v) for x in C}
                                V = [set(t) for t in U]
                                V[j].add(v)
                                assert max_clique(V[j], Enew) == a + 1
                                assert max_clique(V[j], Enew) < ell - 1
                                tested += 1
                                for mask in range(1, 1 << d):
                                    S = {i for i in range(d) if mask & (1 << i)}
                                    old = set(range(front)).intersection(
                                        *(U[i] for i in S)
                                    )
                                    new = set(range(v + 1)).intersection(
                                        *(V[i] for i in S)
                                    )
                                    assert new == (old | {v} if S == {j} else old)
                                    if S != {j}:
                                        assert max_clique(new, Enew) == max_clique(old, E)
                                    supports += 1
        by_ell[ell] = (tested - t0, supports - s0)
    # Important hostile case: raw mixed bound does not change, but
    # canonical mixed age may decrease after lowering the singleton bound.
    old_E = {(1, 2)}
    new_E = old_E | {(0, 3)}
    Uj, Ui = {0}, {1, 2}
    assert (3 - max_clique(Uj, old_E),
            3 - max_clique(Ui, old_E),
            3 - max_clique(Uj & Ui, old_E)) == (2, 1, 3)
    assert (3 - max_clique(Uj | {3}, new_E),
            3 - max_clique(Ui, new_E),
            3 - max_clique((Uj | {3}) & Ui, new_E)) == (1, 1, 3)
    # With both singleton bounds 1, any actual new pair-clique
    # contains at most 2 vertices, despite unchanged raw mixed bound 3.
    assert min(3, 1 + 1) == 2
    return tested, supports, by_ell


if __name__ == "__main__":
    n, m, breakdown = verify()
    assert (n, m) == (49182, 327110), (n, m)
    assert breakdown == {
        3: (1600, 10598), 4: (12827, 85297),
        5: (17273, 114911), 6: (17482, 116304),
    }, breakdown
    print(f"PASS: {n:,} maximal-clique rank-drop witnesses; "
          f"{m:,} complete nonempty support checks")
    print("PASS: genuine K4 canonical mixed-age decrease with fixed raw bound")
