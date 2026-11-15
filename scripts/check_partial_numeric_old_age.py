#!/usr/bin/env python3
"""Independent literal partial numerical-H old-prefix capacity regression.

Exhaust all 64 simple graphs on four originals, heights 0..3,
partial prefixes cut at hPosition(k,b,g) for b=0..2 and 0<=g<=k,
pairs of strictly later future top originals, and all three
nonempty supports of two selected types. Reconstruct H binary-L
directly from the numerical generation gate, without importing
Lean, diary counters, or graph-age theorem definitions.

26,880 exact old common-pool/capacity cases; 7,296 have a qualifying
partial current original; 6,210 have a larger actual capacity than
the previous complete blocks alone. Does not prove the infinite
resolved-copy stage schedule or auxiliary E/B3 events.
"""

from itertools import combinations


def hpos(k, i, q):
    return 2 * ((k + 1) * i + q)


def maxclique(vertices, edge):
    """Exact maximum symmetric-directed clique by backtracking."""
    best = 0

    def walk(n, candidates):
        nonlocal best
        if n + len(candidates) <= best:
            return
        best = max(best, n)
        for ix, x in enumerate(candidates):
            nxt = [y for y in candidates[ix + 1:] if edge(x, y) and edge(y, x)]
            walk(n + 1, nxt)

    walk(0, vertices)
    return best


def main():
    count = 0
    partial_eligible = 0
    improved = 0
    for graphmask in range(64):
        E = [[False] * 4 for _ in range(4)]
        for bit, (i, j) in enumerate(combinations(range(4), 2)):
            E[i][j] = E[j][i] = bool(graphmask & (1 << bit))
        def original(x, y):
            return E[x][y]

        for k in range(4):
            def decode(z):
                if z % 2:
                    return None
                return divmod(z // 2, k + 1)

            def numeric(z, w):
                a, b = decode(z), decode(w)
                if a is None or b is None or a[0] == b[0]:
                    return False
                earlier, later = (a, b) if a[0] < b[0] else (b, a)
                gate = earlier[1] < later[1] or (
                    earlier[1] == k and later[1] == k)
                return E[a[0]][b[0]] and gate

            for b in range(3):
                for g in range(k + 1):
                    for j0 in range(b + 1, 4):
                        for j1 in range(b + 1, 4):
                            j = (j0, j1)
                            for support in ((0,), (1,), (0, 1)):
                                old = [i for i in range(b)
                                       if all(E[i][j[t]] for t in support)]
                                include_b = all(E[b][j[t]] for t in support)
                                actual = [
                                    z for z in range(hpos(k, b, g))
                                    if all(numeric(z, hpos(k, j[t], k))
                                           for t in support)
                                ]
                                exact = sorted(
                                    [hpos(k, i, q) for i in old
                                     for q in range(k + 1)] +
                                    ([hpos(k, b, q) for q in range(g)]
                                     if include_b else [])
                                )
                                if actual != exact:
                                    raise AssertionError(
                                        f"pool mismatch: graph={graphmask}, "
                                        f"k={k}, b={b}, g={g}, "
                                        f"future={j}, support={support}; "
                                        f"actual={actual}, exact={exact}"
                                    )

                                adjacent = [i for i in old if E[i][b]]
                                old_capacity = maxclique(old, original)
                                partial_capacity = (
                                    min(g, 1 + maxclique(adjacent, original))
                                    if include_b and g > 0 else 0
                                )
                                predicted = max(old_capacity, partial_capacity)
                                actual_capacity = maxclique(actual, numeric)
                                if actual_capacity != predicted:
                                    raise AssertionError(
                                        f"capacity mismatch: graph={graphmask}, "
                                        f"k={k}, b={b}, g={g}, future={j}, "
                                        f"support={support}; "
                                        f"actual={actual_capacity}, predicted={predicted}"
                                    )
                                count += 1
                                partial_eligible += bool(include_b and g)
                                improved += predicted > old_capacity

    assert (count, partial_eligible, improved) == (26880, 7296, 6210), (
        count, partial_eligible, improved)
    print("PASS: 26880 exact partial old-pool/capacity cases;"
          " 7296 eligible partial-current cases;"
          " 6210 genuine capacity increases")


if __name__ == "__main__":
    main()
