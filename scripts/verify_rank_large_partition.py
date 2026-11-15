#!/usr/bin/env python3
"""Independent exhaustive small-tree test of the rank-large finite partition.

Rooted labelled trees of sizes 1..5, all antitone ranks 0,1,2,
and three-way vertex statuses (absent, colour A, colour B) are tested.
The checker does NOT import diary counters, manuscript enumerations,
or a published BRD characterization. It is a regression, not a proof.
"""

from itertools import product


def check() -> tuple[int, int]:
    checked, large_cases = 0, 0
    for n in range(1, 6):
        for parents in product(*(range(i) for i in range(1, n))):
            below = [[False] * n for _ in range(n)]
            for i in range(n):
                below[i][i] = True
                j = i
                while j > 0:
                    j = parents[j - 1]
                    below[j][i] = True
            for rank in product(range(3), repeat=n):
                if any(
                    below[i][j] and rank[j] > rank[i]
                    for i in range(n)
                    for j in range(n)
                ):
                    continue

                def large(S: set[int], k: int, u: int) -> bool:
                    if k == 0:
                        return all(
                            any(below[v][w] and w in S for w in range(n))
                            for v in range(n)
                            if below[u][v]
                        )
                    return all(
                        any(
                            below[v][w]
                            and rank[w] == k - 1
                            and large(S, k - 1, w)
                            for w in range(n)
                        )
                        for v in range(n)
                        if below[u][v] and rank[v] == k
                    )

                for u in range(n):
                    for colours in product(range(3), repeat=n):
                        S = {v for v in range(n) if colours[v]}
                        k = rank[u]
                        if large(S, k, u):
                            large_cases += 1
                            if not any(
                                below[u][v]
                                and rank[v] == k
                                and large(
                                    {w for w in S if colours[w] == j}, k, v
                                )
                                for v in range(n)
                                for j in (1, 2)
                            ):
                                raise AssertionError(
                                    (n, parents, rank, u, colours)
                                )
                        checked += 1
    return checked, large_cases


if __name__ == "__main__":
    result = check()
    assert result == (1506150, 380510), result
    print(f"PASS: {result[0]:,} instances, {result[1]:,} large antecedents")
