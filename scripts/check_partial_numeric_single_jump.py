#!/usr/bin/env python3
"""Adversarial independent exact one-jump numerical-H age interpreter.

Tests all 64 irreflexive symmetric 4-original Boolean graphs, k=0..3,
b=0..2, g=0..k, both later original top names (allow repetitions)
and all nonempty supports of two future sorts: 26,880 physical
capacity tests. It reconstructs the L generator directly from source
original E and its numeric generation gate, not any manuscript age
definition or Lean result. Additionally checks each fixed-support
cut profile has at most one up-jump of one, in exactly the predicted
location. A separate explicit ineligible-b case refutes the naive
unconditional max/min capacity identity.
"""

from itertools import combinations


def original_graph(mask):
    E = [[False] * 4 for _ in range(4)]
    for bit, (i, j) in enumerate(combinations(range(4), 2)):
        E[i][j] = E[j][i] = bool(mask & (1 << bit))
    return E


def hpos(k, i, q):
    return 2 * ((k + 1) * i + q)


def actual_binary(E, k, x, y):
    if x % 2 or y % 2:
        return False
    i, qi = divmod(x // 2, k + 1)
    j, qj = divmod(y // 2, k + 1)
    if i == j:
        return False
    if i > j:
        i, qi, j, qj = j, qj, i, qi
    return E[i][j] and (qi < qj or (qi == k and qj == k))


def max_clique(nodes, E):
    best = 0

    def search(count, pool):
        nonlocal best
        if count + len(pool) <= best:
            return
        best = max(best, count)
        for i, node in enumerate(pool):
            remaining = [
                v for v in pool[i + 1:]
                if E(node, v) and E(v, node)
            ]
            search(count + 1, remaining)

    search(0, nodes)
    return best


def support_state(E, k, b, future, support, g):
    P = [
        i for i in range(b)
        if all(E[i][future[t]] for t in support)
    ]
    S = [i for i in P if E[i][b]]
    p = max_clique(P, lambda i, j: E[i][j])
    c = max_clique(S, lambda i, j: E[i][j])
    eligible = all(E[b][future[t]] for t in support)
    selected_tops = [hpos(k, future[t], k) for t in support]
    actual_old = [
        z for z in range(hpos(k, b, g))
        if all(actual_binary(E, k, z, w) for w in selected_tops)
    ]
    physical = max_clique(actual_old, lambda x, y: actual_binary(E, k, x, y))
    normal_form = p + int(eligible and c == p and p < g)
    formula = max(p, min(g, 1 + c) if eligible else 0)
    if physical != normal_form or normal_form != formula:
        raise AssertionError(
            f"normal form mismatch mask={E} k={k} b={b} "
            f"g={g} future={future} support={support}; "
            f"physical={physical}, normal={normal_form}, max-min={formula}"
        )
    return physical, p, c, eligible


def main():
    count = 0
    jump_profiles = 0
    jump_events = 0
    for mask in range(64):
        E = original_graph(mask)
        for k in range(4):
            for b in range(3):
                for j0 in range(b + 1, 4):
                    for j1 in range(b + 1, 4):
                        for support in ((0,), (1,), (0, 1)):
                            caps = []
                            params = None
                            for g in range(k + 1):
                                x, p, c, eligible = support_state(
                                    E, k, b, (j0, j1), support, g
                                )
                                caps.append(x)
                                params = (p, c, eligible)
                                count += 1
                            jumps = [
                                g for g in range(k)
                                if caps[g + 1] > caps[g]
                            ]
                            if len(jumps) > 1:
                                raise AssertionError("more than one actual capacity jump")
                            if any(caps[g + 1] - caps[g] not in (0, 1) for g in range(k)):
                                raise AssertionError("capacity change not 0 or 1")
                            p, c, eligible = params
                            predicted_jumps = ([p] if
                                eligible and c == p and p < k else [])
                            if jumps != predicted_jumps:
                                raise AssertionError(
                                    f"bad jump location: {jumps}, "
                                    f"expected {predicted_jumps}, caps={caps}"
                                )
                            jump_profiles += 1
                            jump_events += len(jumps)

    # Three originals with E(0,1)=E(0,2)=1, E(1,2)=0.
    bad = [[False] * 4 for _ in range(4)]
    for i, j in ((0, 1), (0, 2)):
        bad[i][j] = bad[j][i] = True
    actual, p, c, eligible = support_state(bad, 2, 1, (2, 2), (0,), 2)
    unconditional = max(p, min(2, 1 + c))
    assert not eligible and (p, c, actual, unconditional) == (1, 1, 1, 2)

    assert count == 26880, count
    print(
        f"PASS: {count} exact physical one-jump cases, "
        f"{jump_profiles} fixed-support profiles, "
        f"{jump_events} exact one-unit jumps; "
        "ineligible current-original counterexample confirmed"
    )


if __name__ == "__main__":
    main()
