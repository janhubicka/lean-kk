#!/usr/bin/env python3
"""Independent finite referee for the nonfree controlled-pivot theorem.

Exhaust all K_ell-free graphs on P={0,1,2} and the SAME pivot v=3,
ell=2,3,4.  The old sort s=0 is forced to be the actual pivot type;
the other two complete passing columns are arbitrary.  Enumerate normalized
clique vectors directly to compute every raw and canonical support bound.

Only controlled-coding condition (2) is assumed.  Check all linked-pool
budgets and complete post-pivot canonical ages, including the oversized
support case and mixed positive/negative children of one repeated parent.
These are finite checks, not a substitute for Lean kernel verification.
"""

from __future__ import annotations

import argparse
from collections import Counter
from functools import lru_cache
from itertools import combinations, product
import json
from pathlib import Path


@lru_cache(maxsize=None)
def supports(d: int, ell: int) -> tuple[int, ...]:
    return tuple(s for s in range(1, 1 << d) if s.bit_count() <= ell - 1)


@lru_cache(maxsize=None)
def weights(d: int, ell: int) -> tuple[tuple[int, ...], ...]:
    return tuple(w for w in product(range(ell), repeat=d) if sum(w) <= ell - 1)


@lru_cache(maxsize=None)
def canonical(raw: tuple[int, ...], d: int, ell: int) -> tuple[int, ...]:
    domain = supports(d, ell)
    values = tuple(
        tuple(sum(w[t] for t in range(d) if s >> t & 1) for s in domain)
        for w in weights(d, ell)
    )
    feasible = tuple(a for a in values if all(x <= b for x, b in zip(a, raw)))
    assert feasible  # The all-zero vector satisfies every nonnegative raw bound.
    return tuple(max(a[i] for a in feasible) for i in range(len(domain)))


def clique_capacities(edges: set[tuple[int, int]], size: int = 4) -> tuple[int, ...]:
    cliques = tuple(
        s
        for s in range(1 << size)
        if all((i, j) in edges for i, j in combinations(range(size), 2)
               if s >> i & 1 and s >> j & 1)
    )
    return tuple(max(s.bit_count() for s in cliques if s & ~p == 0)
                 for p in range(1 << size))


def negative_fixtures() -> dict:
    """The two controlled conditions cannot be replaced by pair tests alone."""
    # At ell=3 each old singleton has value 1 and each pair has value 2.
    # Adjoining the pivot sort grows every eligible positive singleton, but
    # the full positive pair has value ell-1.  Coding both positive children
    # blocks their edge: the global positive-support cap is indispensable.
    ell = 3
    capacities = clique_capacities({(0, 3)})
    columns = ((1, 0, 0), (0, 1, 0), (0, 0, 1))

    def pool(t: int) -> int:
        return sum(1 << p for p, row in enumerate(columns)
                   if all(row[i] for i in range(3) if t >> i & 1))

    old_domain = supports(3, ell)
    age = dict(zip(old_domain, canonical(tuple(ell - 1 - capacities[pool(t)]
                                               for t in old_domain), 3, ell)))
    assert age[3] == age[2] + 1 and age[5] == age[4] + 1
    assert age[6] == 2  # Fails only the required positive-pair cap.
    new_age = canonical(tuple(ell - 1 - capacities[pool(u << 1) | 8]
                              for u in supports(2, ell)), 2, ell)
    assert new_age == (1, 1, 1)

    # The existing seven-old-original K4 obstruction: all three singleton
    # values are 1; every larger support has value 2.  Both pair tests and
    # the positive-support cap pass, but the joint insertion-growth test
    # at {a,b} fails and the true post-pivot pair value drops from 2 to 1.
    ell = 4
    capacities = clique_capacities({(1, 2), (3, 4), (5, 6), (0, 7), (1, 7), (2, 7)}, 8)
    columns = ((1, 1, 1), (1, 0, 0), (1, 0, 0),
               (0, 1, 0), (0, 1, 0), (0, 0, 1), (0, 0, 1))
    old_domain = supports(3, ell)
    age = dict(zip(old_domain, canonical(tuple(ell - 1 - capacities[pool(t)]
                                               for t in old_domain), 3, ell)))
    assert age[3] == age[2] + 1 and age[5] == age[4] + 1
    assert all(age[t] <= ell - 2 for t in (2, 4, 6))
    assert age[7] < age[6] + 1
    new_age = canonical(tuple(ell - 1 - capacities[pool(u << 1) | 128]
                              for u in supports(2, ell)), 2, ell)
    assert new_age == (1, 1, 1)
    return {
        "without_positive_support_cap": "rejected: K3 positive-pair age drops 2 to 1",
        "pair_tests_without_joint_growth": "rejected: K4 positive-pair age drops 2 to 1",
    }


def run() -> dict:
    counts: Counter[str] = Counter()
    per_ell: dict[str, dict[str, int]] = {}
    edgelist = tuple(combinations(range(4), 2))
    for ell in (2, 3, 4):
        local: Counter[str] = Counter()
        old_domain = supports(3, ell)
        for graphmask in range(1 << len(edgelist)):
            edges = {edge for k, edge in enumerate(edgelist) if graphmask >> k & 1}
            capacities = clique_capacities(edges)
            if capacities[15] >= ell:
                continue
            local["original_graphs"] += 1
            for code in range(64):
                columns = tuple(
                    (int((p, 3) in edges), (code >> (2 * p)) & 1,
                     (code >> (2 * p + 1)) & 1)
                    for p in range(3)
                )

                def pool(t: int) -> int:
                    return sum(1 << p for p in range(3)
                               if all(columns[p][i] for i in range(3) if t >> i & 1))

                raw = tuple(max(0, ell - 1 - capacities[pool(t)]) for t in old_domain)
                old_age = dict(zip(old_domain, canonical(raw, 3, ell)))
                if min(old_age.values()) < 1:
                    continue
                local["positive_physical_profiles"] += 1
                for xsmall in range(4):
                    positive = xsmall << 1  # Only sorts 1 and 2 can pass positively.
                    positive_supports = tuple(t for t in old_domain if t & ~positive == 0)
                    if any(old_age[t] > ell - 2 for t in positive_supports):
                        continue
                    if any(old_age[t | 1] != old_age[t] + 1 for t in positive_supports
                           if t.bit_count() < ell - 1):
                        continue
                    local["controlled_capacity_configurations"] += 1
                    fixture = (ell, graphmask, code, positive)
                    for t in positive_supports:
                        assert 1 + capacities[pool(t | 1)] + old_age[t] <= ell - 1, fixture
                        local["derived_linked_budgets"] += 1
                        if t.bit_count() == ell - 1:
                            local["oversized_insert_supports"] += 1

                    def check_map(pi: tuple[int, ...], beta: tuple[bool, ...]) -> None:
                        dnew = len(pi)
                        new_domain = supports(dnew, ell)
                        image = {
                            u: sum(1 << parent for parent in {pi[i] for i in range(dnew)
                                                             if u >> i & 1})
                            for u in new_domain
                        }
                        assert all(t in old_age for t in image.values())
                        newraw = tuple(
                            max(0, ell - 1 - capacities[
                                pool(image[u]) | (8 if all(beta[i] for i in range(dnew)
                                                           if u >> i & 1) else 0)])
                            for u in new_domain
                        )
                        new_age = canonical(newraw, dnew, ell)
                        assert new_age == tuple(old_age[image[u]] for u in new_domain), (
                            fixture, pi, beta, newraw, new_age, old_age)

                    check_map((1, 2), (bool(xsmall & 1), bool(xsmall & 2)))
                    local["exact_survivor_canonical_equalities"] += 1
                    # Parent 1 occurs twice, with one child forced negative.  The
                    # pivot's own sort also continues negatively; the proof needs
                    # s outside the POSITIVE parents, not outside every parent.
                    check_map((0, 1, 1, 2),
                              (False, bool(xsmall & 1), False, bool(xsmall & 2)))
                    local["exact_repeated_parent_canonical_equalities"] += 1
        per_ell[str(ell)] = dict(sorted(local.items()))
        counts.update(local)
    return {
        "date": "2026-11-21",
        "status": "PASS",
        "scope": "finite exhaustive referee; not Lean kernel verification",
        "original_vertices": [0, 1, 2, 3],
        "same_selected_pivot": 3,
        "old_sorts": [0, 1, 2],
        "pivot_old_sort": 0,
        "clique_parameters": [2, 3, 4],
        "hypotheses_checked": [
            "original graph including pivot is K_ell-free",
            "pivot old column equals its actual bilateral original edges",
            "old canonical age is positive on every admissible support",
            "controlled condition (2): positive support cap and admissible insertion growth",
        ],
        "unused_controlled_hypotheses": ["pivot singleton equals one", "maximum decomposition axiom"],
        "negative_fixtures": negative_fixtures(),
        "counts": dict(sorted(counts.items())),
        "per_ell": per_ell,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", type=Path, help="also save the exact result as JSON")
    args = parser.parse_args()
    result = run()
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(rendered, encoding="utf-8")
    print(rendered, end="")
