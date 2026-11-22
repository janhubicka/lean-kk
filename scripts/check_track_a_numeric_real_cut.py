#!/usr/bin/env python3
"""Independent true numbered-H one-CUT raw event regression (Track A).

Reconstructs the actual generated L bits for all 64 simple graphs
on four originals, heights k=1..3, current originals b=0..2,
all later named top pairs (including repetitions), all nonempty
one/two-sort supports, and admissible ell=2..5.

Checks raw ages at EACH of c, c+1 and c+2, where
c=hPosition(k,b,g). Real-step events are exactly the known
critical capacity formula; odd dummy adds no ordinary-L age.
"""
from check_partial_numeric_single_jump import (
    original_graph, hpos, actual_binary, max_clique
)


def raw_capacity(E, k, cut, tops):
    common = [
        z for z in range(cut)
        if all(actual_binary(E, k, z, v) for v in tops)
    ]
    return max_clique(common, lambda x, y: actual_binary(E, k, x, y))


def main():
    checks = real_changes = odd_changes = henson_checks = 0
    for mask in range(64):
        E = original_graph(mask)
        original_max = max_clique(range(4), lambda x, y: E[x][y])
        for k in range(1, 4):
            for b in range(3):
                for j0 in range(b + 1, 4):
                    for j1 in range(b + 1, 4):
                        named = (j0, j1)
                        for U in ((0,), (1,), (0, 1)):
                            P = [i for i in range(b)
                                 if all(E[i][named[t]] for t in U)]
                            S = [i for i in P if E[i][b]]
                            p = max_clique(P, lambda x, y: E[x][y])
                            linked = max_clique(S, lambda x, y: E[x][y])
                            eligible = all(E[b][named[t]] for t in U)
                            top_positions = [hpos(k, named[t], k) for t in U]
                            for g in range(k):
                                cut = hpos(k, b, g)
                                assert hpos(k, b, g+1) == cut + 2
                                caps = [raw_capacity(E, k, cut+delta, top_positions)
                                        for delta in (0, 1, 2)]
                                assert caps[1] == caps[2], (
                                    "odd dummy changed capacity",
                                    mask, k, b, named, U, g, caps)
                                for ell in range(2, 6):
                                    if len(U) >= ell:
                                        continue
                                    raw = [max(0, ell-1-v) for v in caps]
                                    observed = raw[1] < raw[0]
                                    predicted = (eligible and linked == p
                                                 and p == g and p < ell-1)
                                    assert observed == predicted, (
                                        "single numeric-cut raw iff failed",
                                        mask, k, b, named, U, g, ell,
                                        raw, p, linked, eligible)
                                    assert raw[1] == raw[2]
                                    if original_max < ell:
                                        assert observed == (
                                            eligible and linked == p and p == g
                                        ), ("Henson shortcut failed", mask, ell)
                                        henson_checks += 1
                                    checks += 1
                                    real_changes += int(observed)
                                    odd_changes += int(raw[2] < raw[1])

    assert (checks, real_changes, odd_changes) == (59136, 11652, 0), (
        checks, real_changes, odd_changes)
    print(f"PASS: {checks} literal numeric-cut raw checks, "
          f"{real_changes} real-step raw events, "
          f"{odd_changes} odd-step raw events, "
          f"{henson_checks} genuine K_ell-free shortcut checks")


if __name__ == "__main__":
    main()
