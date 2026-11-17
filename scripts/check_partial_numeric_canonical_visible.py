#!/usr/bin/env python3
"""Independent bounded-clique-vector check of canonical-visible numerical-H events.

This is NOT an implementation of the Lean proof. It reconstructs the actual
numeric H binary generator through the separate model checker and independently
enumerates all normalized 2-sort integer clique vectors of total weight <=ell-1,
their full support inequality systems and canonical suprema.

Exhaust all 64 simple four-original E graphs, k=0..3, b=0..2,
all pairs of later given original tops (repetitions included), ell=2..5,
and all pairs of partial old cuts g<=h<=k. Verify that canonical
age difference is equivalent to loss of an old-feasible integer vector
and, more strongly, to an old-feasible vector that saturates an
eligibility-correct raw support which drops exactly one.

No claim about actual recursive original schedule or Kpt E/B3.
"""
from check_partial_numeric_single_jump import original_graph, support_state


def supports(ell):
    return ((0,), (1,), (0, 1)) if ell >= 3 else ((0,), (1,))


def witnesses(ell):
    return tuple((i, j) for i in range(ell) for j in range(ell)
                 if i + j <= ell - 1)


def support_sum(w, U):
    return sum(w[t] for t in U)


def canonical(raw, Uset, weights):
    feasible = tuple(w for w in weights
                     if all(support_sum(w, U) <= raw[U] for U in Uset))
    return tuple(max((support_sum(w, U) for w in feasible), default=0)
                 for U in Uset), feasible


def main():
    pairs = 0
    changes = 0
    certificates = 0
    redundant_raw_events = 0
    for mask in range(64):
        E = original_graph(mask)
        for k in range(4):
            for b in range(3):
                for j0 in range(b + 1, 4):
                    for j1 in range(b + 1, 4):
                        for ell in (2, 3, 4, 5):
                            Uset = supports(ell)
                            weights = witnesses(ell)
                            raw = []
                            originals = []
                            for g in range(k + 1):
                                ages = {}
                                info = {}
                                for U in Uset:
                                    cap, p, c, eligible = support_state(
                                        E, k, b, (j0, j1), U, g)
                                    ages[U] = max(0, ell - 1 - cap)
                                    info[U] = (p, c, eligible)
                                raw.append(ages)
                                originals.append(info)
                            canonical_ages = []
                            feasible_sets = []
                            for ages in raw:
                                a, w = canonical(ages, Uset, weights)
                                canonical_ages.append(a)
                                feasible_sets.append(set(w))
                            for g in range(k + 1):
                                for h in range(g, k + 1):
                                    changed = canonical_ages[h] != canonical_ages[g]
                                    lost = feasible_sets[g] - feasible_sets[h]
                                    if changed != bool(lost):
                                        raise AssertionError(
                                            f"feasible iff failed mask={mask},k={k},"
                                            f"b={b},ell={ell},g={g},h={h},"
                                            f"tops={(j0,j1)}; canonical="
                                            f"{canonical_ages[g],canonical_ages[h]}"
                                        )
                                    certified = False
                                    has_raw_event = False
                                    for U in Uset:
                                        if raw[h][U] >= raw[g][U]:
                                            continue
                                        has_raw_event = True
                                        p, c, eligible = originals[g][U]
                                        criterion = (
                                            eligible and c == p and
                                            g <= p < h and p < ell - 1
                                        )
                                        if not criterion:
                                            raise AssertionError("wrong physical raw criterion")
                                        for w in feasible_sets[g]:
                                            if support_sum(w, U) == raw[g][U]:
                                                certified = True
                                                break
                                    if changed != certified:
                                        raise AssertionError(
                                            f"saturating witness iff failed:"
                                            f" mask={mask},k={k},b={b},ell={ell},"
                                            f"g={g},h={h},tops={(j0,j1)},"
                                            f"changed={changed},certified={certified}"
                                        )
                                    pairs += 1
                                    changes += int(changed)
                                    certificates += int(certified)
                                    redundant_raw_events += int(
                                        has_raw_event and not changed)
    assert pairs > 0 and changes == certificates
    print(f"PASS: {pairs} original-graph/cut-pair/ell canonical"
          f" checks; {changes} genuine canonical-visible events;"
          f" {redundant_raw_events} raw-only redundant events")


if __name__ == "__main__":
    main()
