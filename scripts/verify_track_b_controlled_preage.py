#!/usr/bin/env python3
"""Independent finite referee for controlled pre-ages and finite normalization.

Exhaustive domains are recorded separately in the JSON result:
* every positive graph age on 0..3 survivor sorts, ell=2,3,4, and every
  passing subset satisfying the complete positive-support cap;
* every genuine ambient comparison age for 0..2 survivor sorts;
* every K_ell-free graph on 0..3 old originals plus one pivot, every complete
  survivor column on 0..2 sorts, and every passing subset;
* every K_ell-free old graph on 0..2 originals, every complete column on
  0..2 sorts, every genuine lower target, and every order of its supports.

The graph normalization checks build actual adjacency tables. Each order is
checked both with contiguous blocks and with a zero-column gap after each
nonempty block, adjacent to that entire block. The gap pattern is a specified
adversarial fixture, not an exhaustive enumeration of all ambient gaps.

No previous checker is imported or modified. This uses a fresh normalized
integer-vector enumerator and a recursive exact graph clique algorithm.
Finite checks are not Lean kernel verification or a global diary theorem.
"""

from __future__ import annotations

import argparse
from collections import Counter
from functools import lru_cache
from hashlib import sha256
from itertools import combinations, permutations, product
import json
from pathlib import Path
from typing import Iterable


def require(condition: bool, label: str, details: object = None) -> None:
    if not condition:
        raise AssertionError((label, details))


@lru_cache(maxsize=None)
def supports(d: int, ell: int) -> tuple[int, ...]:
    return tuple(mask for mask in range(1, 1 << d)
                 if mask.bit_count() <= ell - 1)


@lru_cache(maxsize=None)
def vectors_with_budget(d: int, budget: int) -> tuple[tuple[int, ...], ...]:
    if d == 0:
        return ((),)
    return tuple((first,) + tail for first in range(budget + 1)
                 for tail in vectors_with_budget(d - 1, budget - first))


def mass(w: tuple[int, ...], support: int) -> int:
    return sum(value for i, value in enumerate(w) if support & (1 << i))


@lru_cache(maxsize=None)
def profile_space(d: int, ell: int) -> tuple[
        tuple[tuple[int, ...], ...], tuple[tuple[int, ...], ...]]:
    vectors = vectors_with_budget(d, ell - 1)
    return vectors, tuple(tuple(mass(w, s) for s in supports(d, ell))
                          for w in vectors)


@lru_cache(maxsize=None)
def feasible_indices(table: tuple[int, ...], d: int, ell: int) -> tuple[int, ...]:
    _, values = profile_space(d, ell)
    return tuple(i for i, row in enumerate(values)
                 if all(a <= b for a, b in zip(row, table)))


@lru_cache(maxsize=None)
def canonical(table: tuple[int, ...], d: int, ell: int) -> tuple[int, ...]:
    require(len(table) == len(supports(d, ell)), "wrong table domain", (d, ell, table))
    _, values = profile_space(d, ell)
    feasible = feasible_indices(table, d, ell)
    require(bool(feasible), "zero vector missing", (d, ell, table))
    return tuple(max(values[i][k] for i in feasible) for k in range(len(table)))


@lru_cache(maxsize=None)
def genuine_ages(d: int, ell: int) -> tuple[tuple[int, ...], ...]:
    return tuple(table for table in product(range(1, ell), repeat=len(supports(d, ell)))
                 if canonical(table, d, ell) == table)


def respects(w: tuple[int, ...], table: tuple[int, ...], d: int, ell: int) -> bool:
    return all(mass(w, s) <= bound for s, bound in zip(supports(d, ell), table))


def positive_cap(r: tuple[int, ...], e: int, ell: int, x: int) -> bool:
    return all(value <= ell - 2 for s, value in zip(supports(e, ell), r)
               if s & ~x == 0)


def controlled_preage(r: tuple[int, ...], e: int, ell: int, x: int) -> tuple[int, ...]:
    rbar = {0: 0, **dict(zip(supports(e, ell), r))}
    pivot = 1 << e
    return tuple(rbar[t] if t & pivot == 0
                 else max(rbar[t & ~pivot], 1 + rbar[t & x])
                 for t in supports(e + 1, ell))


@lru_cache(maxsize=None)
def supported_witness(r: tuple[int, ...], e: int, ell: int, target: int) -> tuple[int, ...]:
    if target == 0:
        return (0,) * e
    expected = dict(zip(supports(e, ell), r))[target]
    vectors, _ = profile_space(e, ell)
    for i in feasible_indices(r, e, ell):
        w = vectors[i]
        if mass(w, target) == expected and all(value == 0 for j, value in enumerate(w)
                                               if target & (1 << j) == 0):
            return w
    raise AssertionError(("supported witness missing", e, ell, r, target))


def pointed_criterion(r: tuple[int, ...], p: tuple[int, ...], e: int,
                      ell: int, x: int) -> bool:
    rr = {0: 0, **dict(zip(supports(e, ell), r))}
    pp = dict(zip(supports(e + 1, ell), p))
    pivot = 1 << e
    survivor = all(value <= pp[s] for s, value in rr.items() if s)
    pointed = all(1 + rr[a] <= pp[a | pivot]
                  for a in range(1 << e)
                  if a & ~x == 0 and a.bit_count() < ell - 1)
    return survivor and pointed


class FiniteGraph:
    """Simple undirected labelled graph; capacities use exact vertex recursion."""

    def __init__(self, adjacency: Iterable[int] = ()) -> None:
        self.adj = list(adjacency)

    def append_vertex(self, neighbours: int = 0) -> int:
        v = len(self.adj)
        require(neighbours >> v == 0, "new vertex references a later vertex", (v, neighbours))
        for u in range(v):
            if neighbours & (1 << u):
                self.adj[u] |= 1 << v
        self.adj.append(neighbours)
        return v

    def capacity_function(self):
        adjacency = tuple(self.adj)

        @lru_cache(maxsize=None)
        def omega(mask: int) -> int:
            if not mask:
                return 0
            bit = mask & -mask
            v = bit.bit_length() - 1
            rest = mask ^ bit
            return max(omega(rest), 1 + omega(rest & adjacency[v]))

        return omega


def all_graphs(size: int) -> Iterable[tuple[int, FiniteGraph]]:
    edges = tuple(combinations(range(size), 2))
    for code in range(1 << len(edges)):
        graph = FiniteGraph([0] * size)
        for k, (u, v) in enumerate(edges):
            if code & (1 << k):
                graph.adj[u] |= 1 << v
                graph.adj[v] |= 1 << u
        yield code, graph


def raw_table(graph: FiniteGraph, rows: tuple[int, ...] | list[int],
              d: int, ell: int) -> tuple[int, ...]:
    require(len(rows) <= len(graph.adj), "column table exceeds graph")
    omega = graph.capacity_function()
    return tuple(max(0, ell - 1 - omega(sum(1 << v for v, row in enumerate(rows)
                                            if row & s == s)))
                 for s in supports(d, ell))


def constructor_and_criterion() -> dict:
    domains = []
    totals: Counter[str] = Counter()
    for ell in (2, 3, 4):
        for e in range(4):
            local: Counter[str] = Counter()
            ages = genuine_ages(e, ell)
            local["candidate_positive_tables"] = (ell - 1) ** len(supports(e, ell))
            local["genuine_survivor_ages"] = len(ages)
            for r in ages:
                for x in range(1 << e):
                    local["age_passing_pairs"] += 1
                    if not positive_cap(r, e, ell, x):
                        continue
                    local["eligible_constructors"] += 1
                    c = controlled_preage(r, e, ell, x)
                    require(canonical(c, e + 1, ell) == c and all(v >= 1 for v in c),
                            "constructor is not a genuine positive age", (ell, e, r, x, c))
                    cc = {0: 0, **dict(zip(supports(e + 1, ell), c))}
                    rr = {0: 0, **dict(zip(supports(e, ell), r))}
                    pivot = 1 << e
                    require(cc[pivot] == 1, "wrong pivot singleton")
                    for t in supports(e + 1, ell):
                        s = t & ~pivot
                        a = t & x
                        if t & pivot == 0 or rr[s] >= 1 + rr[a]:
                            witness = supported_witness(r, e, ell, s) + (0,)
                        else:
                            witness = supported_witness(r, e, ell, a) + (1,)
                        require(sum(witness) <= ell - 1 and mass(witness, t) == cc[t]
                                and respects(witness, c, e + 1, ell),
                                "explicit constructor witness failed", (ell, e, r, x, t, witness))
                        require(cc[t] == max(cc[t & ~pivot], cc[t & (x | pivot)]),
                                "controlled maximum identity failed", (ell, e, r, x, t))
                        local["supported_witnesses_and_maximum_identities"] += 1
                    for s in supports(e, ell):
                        require(cc[s] == rr[s], "survivor restriction changed")
                        if s & ~x == 0:
                            require(cc[s] <= ell - 2, "positive cap failed")
                            local["positive_support_caps"] += 1
                    for a in range(1 << e):
                        if a & ~x == 0 and a.bit_count() < ell - 1:
                            require(cc[a | pivot] == 1 + rr[a], "controlled growth failed")
                            local["growth_identities_including_empty"] += 1
                    if ell >= 3:
                        recovered = sum(1 << i for i in range(e)
                                        if cc[pivot | (1 << i)] == cc[1 << i] + 1)
                        require(recovered == x, "wrong recovered passing set")
                        local["pair_defined_passing_sets"] += 1
                    for w in vectors_with_budget(e, ell - 1):
                        old = w + (0,)
                        pointed = tuple(value if x & (1 << i) else 0
                                        for i, value in enumerate(w)) + (1,)
                        residual = (respects(old, c, e + 1, ell)
                                    and sum(pointed) <= ell - 1
                                    and respects(pointed, c, e + 1, ell))
                        require(residual == respects(w, r, e, ell),
                                "coding feasible-vector equivalence failed", (ell, e, r, x, w))
                        local["exact_residual_vector_tests"] += 1
                        if sum(pointed) > ell - 1:
                            local["pointed_normalization_rejections"] += 1
                    if e <= 2:
                        for p in genuine_ages(e + 1, ell):
                            below = all(a <= b for a, b in zip(c, p))
                            require(below == pointed_criterion(r, p, e, ell, x),
                                    "pointed lower-bound criterion failed", (ell, e, r, x, p))
                            local["minimality_iff_comparisons"] += 1
                            local["minimality_iff_true" if below else "minimality_iff_false"] += 1
                            pp = dict(zip(supports(e + 1, ell), p))
                            if not below and all(value <= pp[s] for s, value in rr.items() if s):
                                local["survivor_domination_without_pointed_domination"] += 1
            domains.append({"ell": ell, "survivor_sorts": e, "counts": dict(sorted(local.items()))})
            totals.update(local)
    return {
        "exhaustive_domain": {
            "ell": [2, 3, 4], "survivor_sorts": [0, 1, 2, 3],
            "age_enumeration": "all positive support tables retained exactly when canonical(table)=table",
            "passing_sets": "all subsets, filtered by the full positive-support cap",
            "ambient_comparisons": "all genuine ages on e+1 sorts, for e=0,1,2",
            "residual_vectors": "all nonnegative vectors of total at most ell-1",
        },
        "counts": dict(sorted(totals.items())), "per_domain": domains,
    }


def prospective_events() -> dict:
    domains = []
    totals: Counter[str] = Counter()
    for ell in (2, 3, 4):
        for old_size in range(4):
            pivot_vertex = old_size
            for e in range(3):
                local: Counter[str] = Counter()
                for graphcode, graph in all_graphs(old_size + 1):
                    local["labelled_graphs_enumerated"] += 1
                    if graph.capacity_function()((1 << (old_size + 1)) - 1) >= ell:
                        continue
                    local["legal_old_plus_pivot_graphs"] += 1
                    for columns in product(range(1 << e), repeat=old_size):
                        local["complete_old_column_tables"] += 1
                        old_rows = tuple(row | ((1 << e) if graph.adj[p] & (1 << pivot_vertex) else 0)
                                         for p, row in enumerate(columns))
                        old_raw = raw_table(graph, old_rows, e + 1, ell)
                        old_age = canonical(old_raw, e + 1, ell)
                        omega = graph.capacity_function()
                        ambient_domain = supports(e + 1, ell)
                        old_pools = {
                            u: sum(1 << p for p, row in enumerate(old_rows) if row & u == u)
                            for u in set(ambient_domain) | {u | (1 << e) for u in ambient_domain}
                        }
                        for x in range(1 << e):
                            local["prospective_events"] += 1
                            post_raw = raw_table(graph, columns + (x,), e, ell)
                            r = canonical(post_raw, e, ell)
                            ambient_raw = raw_table(graph, old_rows + (x,), e + 1, ell)
                            formula = tuple(max(0, ell - 1 - (
                                max(omega(old_pools[u]), 1 + omega(old_pools[u | (1 << e)]))
                                if u & ~x == 0 else omega(old_pools[u]))) for u in ambient_domain)
                            require(ambient_raw == formula, "explicit prospective raw formula failed",
                                    (ell, old_size, e, graphcode, columns, x))
                            ambient_age = dict(zip(ambient_domain, canonical(ambient_raw, e + 1, ell)))
                            require(tuple(ambient_age[u] for u in supports(e, ell)) == r,
                                    "ambient prospective canonical restriction failed")
                            local["exact_prospective_raw_formulas_and_survivor_restrictions"] += 1
                            if not all(value >= 1 for value in r):
                                local["events_with_dead_survivor"] += 1
                                continue
                            local["events_with_positive_survivors"] += 1
                            require(positive_cap(r, e, ell, x), "prospective positive cap failed")
                            c = controlled_preage(r, e, ell, x)
                            fixture = (ell, old_size, e, graphcode, columns, x)
                            require(all(a <= b for a, b in zip(c, old_raw)),
                                    "prospective controlled age not below old raw", fixture)
                            require(all(a <= b for a, b in zip(c, old_age)),
                                    "prospective controlled age not below old canonical", fixture)
                            require(pointed_criterion(r, old_age, e, ell, x),
                                    "prospective pointed criterion failed", fixture)
                            require(canonical(c, e + 1, ell) == c,
                                    "prospective constructor consistency failed", fixture)
                            local["controlled_age_below_raw_and_canonical"] += 1
                            if graph.adj[pivot_vertex]:
                                local["nonfree_pivot_events"] += 1
                            if old_raw != old_age:
                                local["noncanonical_old_raw_events"] += 1
                            if post_raw != r:
                                local["noncanonical_post_raw_events"] += 1
                domains.append({"ell": ell, "old_originals": old_size,
                                "survivor_sorts": e, "counts": dict(sorted(local.items()))})
                totals.update(local)
    return {
        "exhaustive_domain": {
            "ell": [2, 3, 4], "old_originals": [0, 1, 2, 3], "survivor_sorts": [0, 1, 2],
            "graphs": "all labelled simple graphs on old_size+1 vertices, filtered by K_ell-freeness",
            "pivot": "last vertex; pivot old column is exactly its full actual graph neighbourhood",
            "survivor_columns": "all Boolean columns on the entire old graph",
            "passing_sets": "all subsets of survivor sorts",
            "positive_survivors": "required for the positive graph-age conclusion; rejected cases counted",
        },
        "counts": dict(sorted(totals.items())), "per_domain": domains,
    }


def actual_normalization() -> dict:
    domains = []
    totals: Counter[str] = Counter()
    max_vertices = 0
    for ell in (2, 3, 4):
        for old_size in range(3):
            for d in range(3):
                local: Counter[str] = Counter()
                domain = supports(d, ell)
                for graphcode, old_graph in all_graphs(old_size):
                    local["labelled_old_graphs_enumerated"] += 1
                    if old_graph.capacity_function()((1 << old_size) - 1) >= ell:
                        continue
                    local["legal_old_graphs"] += 1
                    for old_rows in product(range(1 << d), repeat=old_size):
                        local["complete_old_column_tables"] += 1
                        old_raw = raw_table(old_graph, old_rows, d, ell)
                        old_age = canonical(old_raw, d, ell)
                        for target in genuine_ages(d, ell):
                            local["candidate_genuine_targets"] += 1
                            if not all(a <= b for a, b in zip(target, old_age)):
                                continue
                            local["lower_target_configurations"] += 1
                            values = dict(zip(domain, target))
                            for order in permutations(domain):
                                local["support_orders"] += 1
                                for with_gaps in (False, True):
                                    graph = FiniteGraph(old_graph.adj)
                                    rows = list(old_rows)
                                    for t in order:
                                        r = ell - 1 - values[t]
                                        if r == 0:
                                            local["zero_size_blocks_skipped"] += 1
                                            continue
                                        previous_raw = raw_table(graph, rows, d, ell)
                                        block = 0
                                        for _ in range(r):
                                            v = graph.append_vertex(block)
                                            block |= 1 << v
                                            rows.append(t)
                                        current_raw = raw_table(graph, rows, d, ell)
                                        expected = tuple(min(value, values[t]) if u & ~t == 0 else value
                                                         for u, value in zip(domain, previous_raw))
                                        require(current_raw == expected, "actual raw block update failed",
                                                (ell, old_size, d, graphcode, old_rows, target, order, t))
                                        require(all(a <= b for a, b in zip(target, current_raw)),
                                                "block destroyed target feasibility")
                                        local["actual_clique_blocks"] += 1
                                        if with_gaps:
                                            graph.append_vertex(block)
                                            rows.append(0)
                                            require(raw_table(graph, rows, d, ell) == current_raw,
                                                    "zero-column noisy gap changed the raw age")
                                            local["nonzero_edge_zero_column_gaps"] += 1
                                    final_raw = raw_table(graph, rows, d, ell)
                                    require(final_raw == target, "normalization raw equality failed",
                                            (ell, old_size, d, graphcode, old_rows, target, order, with_gaps))
                                    require(canonical(final_raw, d, ell) == target,
                                            "normalization canonical equality failed")
                                    require(graph.capacity_function()((1 << len(rows)) - 1) < ell,
                                            "normalization actual graph is not K_ell-free")
                                    mask = (1 << old_size) - 1
                                    require(tuple(a & mask for a in graph.adj[:old_size]) == tuple(old_graph.adj)
                                            and tuple(rows[:old_size]) == old_rows,
                                            "normalization altered the protected graph or columns")
                                    max_vertices = max(max_vertices, len(rows))
                                    local["actual_graph_normalizations"] += 1
                                    local["complete_raw_support_equalities"] += len(domain)
                domains.append({"ell": ell, "old_originals": old_size, "active_sorts": d,
                                "counts": dict(sorted(local.items()))})
                totals.update(local)
    return {
        "exhaustive_domain": {
            "ell": [2, 3, 4], "old_originals": [0, 1, 2], "active_sorts": [0, 1, 2],
            "graphs": "all labelled simple old graphs filtered by K_ell-freeness",
            "columns": "all Boolean columns on the complete old graph",
            "targets": "every genuine age below the exact old canonical age",
            "support_orders": "every permutation of all admissible nonempty supports",
            "gap_variants": ["no gaps", "one zero-column gap adjacent to the entire immediately preceding nonempty block"],
            "gap_limitation": "the specified noisy pattern is tested, not every possible ambient gap graph",
            "maximum_actual_graph_vertices": max_vertices,
        },
        "counts": dict(sorted(totals.items())), "per_domain": domains,
    }


def negative_fixtures() -> dict:
    # Survivor domination cannot replace a joint pointed inequality.
    ell, e, r, x = 3, 1, (1,), 1
    p = (1, 1, 1)
    c = controlled_preage(r, e, ell, x)
    require(canonical(p, 2, ell) == p and positive_cap(r, e, ell, x), "invalid fixture")
    require(c == (1, 1, 2) and not pointed_criterion(r, p, e, ell, x),
            "survivor-only fixture did not fail")

    # The same triangle obstruction kills the survivor in an actual legal event.
    graph = FiniteGraph()
    graph.append_vertex()
    graph.append_vertex(1)
    old_raw = raw_table(graph, (3,), 2, 3)
    post_raw = raw_table(graph, (1, 1), 1, 3)
    require(canonical(old_raw, 2, 3) == (1, 1, 1) and post_raw == (0,),
            "dead-survivor fixture did not fail")

    # Proper-support caps do not control a full ell-1 positive support.
    r_large = tuple(s.bit_count() for s in supports(3, 4))
    c_large = controlled_preage(r_large, 3, 4, 7)
    require(canonical(r_large, 3, 4) == r_large
            and canonical(c_large, 4, 4) == c_large
            and not positive_cap(r_large, 3, 4, 7), "invalid largest-support fixture")
    require(respects((1, 1, 1), r_large, 3, 4)
            and respects((1, 1, 1, 0), c_large, 4, 4)
            and sum((1, 1, 1, 1)) > 3, "pointed mass fixture did not fail")

    # Singleton caps do not even guarantee the constructor's upper bound.
    r_singletons = (2, 2, 3)
    c_singletons = controlled_preage(r_singletons, 2, 4, 3)
    require(canonical(r_singletons, 2, 4) == r_singletons
            and max(c_singletons) == 4, "singleton-cap fixture did not fail")
    return {
        "survivor_domination_without_pointed_test": {
            "ell": 3, "survivor_age": [1], "old_age_on_masks_1_2_3": [1, 1, 1],
            "controlled_preage_on_masks_1_2_3": list(c),
            "rejected_conclusion": "C <= P; failure at the joint pivot/survivor support",
        },
        "legal_pivot_can_kill_a_survivor": {
            "ell": 3, "old_vertices": [0], "pivot": 1, "edges": [[0, 1]],
            "old_pivot_and_survivor_columns": [[1, 1]], "positive_survivor_bit": 1,
            "old_canonical_age": [1, 1, 1], "post_singleton_age": 0,
            "rejected_conclusion": "all listed survivors remain positive",
        },
        "proper_support_cap_is_insufficient": {
            "ell": 4, "survivor_sorts": 3, "passing_set": "all three sorts",
            "survivor_age": "R(U)=|U|", "full_positive_support_value": 3,
            "rejected_conclusion": "constructor is controlled and coding preserves R",
        },
        "singleton_cap_is_insufficient": {
            "ell": 4, "survivor_age_on_masks_1_2_3": [2, 2, 3],
            "passing_set": "both sorts", "constructor_value_on_all_three_sorts": 4,
            "rejected_conclusion": "constructor values are at most ell-1",
        },
    }


def run() -> dict:
    return {
        "date": "2026-11-21", "status": "PASS",
        "scope": "independent finite exhaustive referee within the separately listed domains; not Lean kernel verification",
        "script_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        "constructor_and_minimality": constructor_and_criterion(),
        "prospective_full_column_events": prospective_events(),
        "actual_all_support_normalization": actual_normalization(),
        "negative_fixtures": negative_fixtures(),
        "not_checked": [
            "all ell, all finite sort counts, or all finite graph sizes",
            "a prescribed saturated-cover or infinite diary schedule",
            "numerical Henson left-density or existence beyond the enumerated finite graphs",
            "full parameter-closed Kpt history, corrected B3, or a common labelled inverse source",
        ],
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
