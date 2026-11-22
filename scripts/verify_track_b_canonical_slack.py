#!/usr/bin/env python3
"""Independent finite referee for Track B's exact canonical critical-count slack.

This is a regression, NOT a substitute for the strict Lean axiom gate.
Tests complete raw and canonical age functions, positive mixed supports,
all intermediate real original cutoffs, the sharp K4 counterexample,
and a negative example showing why genuine old canonical positivity matters.
"""
from collections import Counter
from itertools import combinations, product
from random import Random


def supports(d, ell):
    return tuple(s for k in range(1, min(d, ell - 1) + 1)
                 for s in combinations(range(d), k))


def cap(edges, vertices):
    vertices = tuple(vertices)
    for k in range(len(vertices), -1, -1):
        for q in combinations(vertices, k):
            if all((min(x, y), max(x, y)) in edges
                   for x, y in combinations(q, 2)):
                return k
    return 0


def raw(edges, cols, ell, d, bound):
    return {s: max(0, ell - 1 - cap(
                edges, (p for p in range(bound)
                        if all(cols[p][t] for t in s))))
            for s in supports(d, ell)}


def canonical(b, ell, d):
    result = {s: 0 for s in supports(d, ell)}
    for w in product(range(ell), repeat=d):
        if sum(w) > ell - 1:
            continue
        if all(sum(w[t] for t in s) <= b[s] for s in result):
            for s in result:
                result[s] = max(result[s], sum(w[t] for t in s))
    return result


def critical_counts(edges, cols, ell, d, bound, length):
    result = {s: 0 for s in supports(d, ell)}
    for v in range(bound, bound + length):
        for s in result:
            old = [p for p in range(v) if all(cols[p][t] for t in s)]
            new = old + ([v] if all(cols[v][t] for t in s) else [])
            delta = cap(edges, new) - cap(edges, old)
            assert delta in (0, 1), (v, s, delta)
            result[s] += delta
    return result


def k_free(edges, ell, n):
    return not any(all((a, b) in edges for a, b in combinations(q, 2))
                   for q in combinations(range(n), ell))


def check_sharp_k4_example():
    edges = {(0, 1), (2, 3)}
    cols = [(1, 0), (1, 0), (0, 1), (0, 1), (1, 1)]
    names = supports(2, 4)
    b0 = raw(edges, cols, 4, 2, 4)
    b1 = raw(edges, cols, 4, 2, 5)
    p = canonical(b0, 4, 2)
    critical = critical_counts(edges, cols, 4, 2, 4, 1)
    assert k_free(edges, 4, 5)
    assert [b0[s] for s in names] == [1, 1, 3]
    assert [b1[s] for s in names] == [1, 1, 2]
    assert [p[s] for s in names] == [1, 1, 2]
    assert canonical(b1, 4, 2) == p
    assert [critical[s] for s in names] == [0, 0, 1]


def check_positivity_counterexample():
    # Old singleton raw/canonical bound zero; inserted vertex forms K3.
    # Canonical equality survives even though critical count exceeds raw slack.
    edges = {(0, 1), (0, 2), (1, 2)}
    cols = [(1,), (1,), (1,)]
    b0 = raw(edges, cols, 3, 1, 2)
    b1 = raw(edges, cols, 3, 1, 3)
    p = canonical(b0, 3, 1)
    n = critical_counts(edges, cols, 3, 1, 2, 1)
    assert p == canonical(b1, 3, 1) == {(0,): 0}
    assert b0 == b1 == {(0,): 0}
    assert n == {(0,): 1}
    assert n[(0,)] + p[(0,)] > b0[(0,)]


def random_referee(trials=12000, seed=20261122):
    rng = Random(seed)
    stats = Counter()
    for _ in range(trials):
        size = rng.randrange(2, 8)
        ell = rng.randrange(3, 6)
        d = rng.randrange(1, 4)
        edges = {(i, j) for i in range(size) for j in range(i + 1, size)
                 if rng.randrange(2)}
        if not k_free(edges, ell, size):
            continue
        cols = [tuple(rng.randrange(2) for _ in range(d))
                for _ in range(size)]
        b = rng.randrange(1, size)
        m = rng.randrange(0, size - b + 1)
        b0 = raw(edges, cols, ell, d, b)
        bf = raw(edges, cols, ell, d, b + m)
        p = canonical(b0, ell, d)
        q = canonical(bf, ell, d)
        count = critical_counts(edges, cols, ell, d, b, m)
        assert all(bf[s] == max(0, b0[s] - count[s]) for s in p)
        stats["raw_telescopes"] += 1
        if not all(1 <= p[s] <= ell - 1 for s in p):
            stats["nongenuine_old"] += 1
            continue
        neutral = (p == q)
        slack = all(count[s] + p[s] <= b0[s] for s in p)
        assert neutral == slack, (size, ell, d, b, m, b0, bf, p, q, count)
        stats["genuine_iff"] += 1
        if neutral:
            stats["neutral_final"] += 1
            for h in range(m + 1):
                assert canonical(raw(edges, cols, ell, d, b + h), ell, d) == p
                stats["intermediate_equal"] += 1
        else:
            stats["changed_final"] += 1
            assert any(b0[s] < count[s] + p[s] for s in p)
        for s in p:
            if neutral and b0[s] == p[s]:
                assert count[s] == 0
                stats["tight_zero"] += 1
        if neutral and any(count.values()):
            stats["critical_but_neutral"] += 1
    return stats


if __name__ == "__main__":
    check_sharp_k4_example()
    check_positivity_counterexample()
    stats = random_referee()
    assert stats["genuine_iff"] >= 2000
    print("PASS: K4-free raw-critical/canonical-neutral fixture")
    print("PASS: positivity is necessary outside genuine final K_ell-free context")
    print("PASS:", dict(stats))
