#!/usr/bin/env python3
"""Independent finite adversarial check of actual completed numeric-H old ages.

Exhaust all 64 undirected simple graphs on four originals, numeric
heights 0..3, old prefix lengths 0..3, all later top-original pairs
(including repetitions), and three nonempty two-sort supports.

This independently reconstructs the literal numeric H binary gate;
it does not import Lean source, theorem definitions, or a diary
enumerator. Every full-prefix old common-neighbourhood is checked
against exactly the real copies of the original common neighbours,
and their maximum clique capacities are checked independently.

This is 23,040 finite cases, not a substitute for the Lean proof or
an unbounded resolved-copy stage schedule.
"""

from __future__ import annotations

from itertools import combinations


def h_position(height: int, original: int, generation: int) -> int:
    return 2 * ((height + 1) * original + generation)


def max_clique_size(vertices: list[int], edge) -> int:
    best = 0

    def visit(size: int, candidates: list[int]) -> None:
        nonlocal best
        if size + len(candidates) <= best:
            return
        best = max(best, size)
        for index, vertex in enumerate(candidates):
            new_candidates = [
                later for later in candidates[index + 1:]
                if edge(vertex, later) and edge(later, vertex)
            ]
            visit(size + 1, new_candidates)

    visit(0, vertices)
    return best


def check() -> None:
    count = 0
    nontrivial = 0
    edge_pairs = list(combinations(range(4), 2))

    for graph_mask in range(1 << len(edge_pairs)):
        graph = [[False for _ in range(4)] for _ in range(4)]
        for bit, (u, v) in enumerate(edge_pairs):
            graph[u][v] = graph[v][u] = bool(graph_mask & (1 << bit))

        def original_edge(u: int, v: int) -> bool:
            return graph[u][v]

        for height in range(4):
            def decode(z: int) -> tuple[int, int] | None:
                if z % 2:
                    return None
                return divmod(z // 2, height + 1)

            def numeric_edge(z: int, w: int) -> bool:
                p, q = decode(z), decode(w)
                if p is None or q is None or p[0] == q[0]:
                    return False
                earlier, later = (p, q) if p[0] < q[0] else (q, p)
                gate = earlier[1] < later[1] or (
                    earlier[1] == height and later[1] == height)
                return original_edge(p[0], q[0]) and gate

            for bound in range(4):
                old = list(range(bound))
                prefix_end = h_position(height, bound, 0)
                for j0 in range(bound, 4):
                    for j1 in range(bound, 4):
                        future = (j0, j1)
                        for support_mask in (1, 2, 3):
                            original_pool = [
                                i for i in old
                                if all(
                                    not support_mask & (1 << t)
                                    or original_edge(i, name)
                                    for t, name in enumerate(future)
                                )
                            ]
                            numeric_pool = [
                                z for z in range(prefix_end)
                                if all(
                                    not support_mask & (1 << t)
                                    or numeric_edge(
                                        z, h_position(height, name, height))
                                    for t, name in enumerate(future)
                                )
                            ]
                            expected_pool = sorted(
                                h_position(height, i, generation)
                                for i in original_pool
                                for generation in range(height + 1)
                            )
                            if numeric_pool != expected_pool:
                                raise AssertionError(
                                    f"common pool failure: graph={graph_mask}, "
                                    f"k={height}, b={bound}, j={future}, "
                                    f"support={support_mask}"
                                )
                            old_capacity = max_clique_size(
                                original_pool, original_edge)
                            numeric_capacity = max_clique_size(
                                numeric_pool, numeric_edge)
                            if old_capacity != numeric_capacity:
                                raise AssertionError(
                                    f"capacity failure: graph={graph_mask}, "
                                    f"k={height}, b={bound}, j={future}, "
                                    f"support={support_mask}; "
                                    f"{old_capacity}!={numeric_capacity}"
                                )
                            count += 1
                            nontrivial += len(original_pool) >= 2

    assert count == 23040, count
    assert nontrivial == 1056, nontrivial
    print(f"PASS: {count} actual full-block old-pool/capacity cases "
          f"({nontrivial} common pools with >=2 originals)")


if __name__ == "__main__":
    check()
