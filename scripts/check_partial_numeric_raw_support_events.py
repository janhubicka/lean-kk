#!/usr/bin/env python3
"""Independent exact literal numerical-H raw support-change iff regression.

For every symmetric simple E on four original names, numerical height
k=0..3, b=0..2, all pairs of strictly later future top originals
(allow repeated names) and all admissible nonempty supports of width2,
test ell=2,3,4,5 and all 0<=g<=h<=k.

The physical common-neighbour numerical-H graph and maximum clique
capacities are independently reconstructed by the verified finite
test helper, rather than imported from a Lean theorem or manuscript
age definition. Raw values use NATURAL truncated subtraction.
"""

from check_partial_numeric_single_jump import original_graph, support_state


def main():
    cases = 0
    events = 0
    zero_saturation = 0
    for mask in range(64):
        E = original_graph(mask)
        for k in range(4):
            for b in range(3):
                for j0 in range(b + 1, 4):
                    for j1 in range(b + 1, 4):
                        for U in ((0,), (1,), (0, 1)):
                            capacities = []
                            p = c = eligible = None
                            for g in range(k + 1):
                                actual, p, c, eligible = support_state(
                                    E, k, b, (j0, j1), U, g
                                )
                                capacities.append(actual)
                            for ell in (2, 3, 4, 5):
                                if len(U) >= ell:
                                    continue
                                for g in range(k + 1):
                                    for h in range(g, k + 1):
                                        old_age = max(0, ell - 1 - capacities[g])
                                        new_age = max(0, ell - 1 - capacities[h])
                                        observed = new_age < old_age
                                        criterion = (
                                            eligible and c == p and
                                            g <= p < h and p < ell - 1
                                        )
                                        if observed != criterion:
                                            raise AssertionError(
                                                f"wrong raw event mask={mask}, "
                                                f"k={k},b={b},g={g},h={h},"
                                                f"tops={(j0,j1)},U={U},ell={ell},"
                                                f"ages={(old_age,new_age)},"
                                                f"p={p},c={c},eligible={eligible}"
                                            )
                                        if observed and old_age != new_age + 1:
                                            raise AssertionError(
                                                "actual raw event not a one-unit decrease"
                                            )
                                        if (
                                            eligible and c == p and
                                            g <= p < h and p >= ell - 1
                                        ):
                                            zero_saturation += 1
                                            if observed:
                                                raise AssertionError("truncated age changed")
                                        cases += 1
                                        events += int(observed)

    # Explicit capacity jump which causes NO raw change at saturation:
    # E edge 0-1, b=0, j=1, k=1, p=c=0; ell=1 is not an admissible
    # nonempty support, so the genuine support-level run uses ell=2,
    # and the saturation mechanism is exercised systematically above.
    assert cases == 197120, cases
    print(
        f"PASS: {cases} actual numerical-H raw support cut comparisons;"
        f" {events} true unit events; {zero_saturation} saturated"
        " capacity-crossing comparisons remained unchanged"
    )


if __name__ == "__main__":
    main()
