# A single physical numerical-H canonical age change need not be a cover

17 November 2026. Adversarial finite counterexample, English proof
and independent literal numerical-H regression. Companion to
`docs/k4_raw_event_canonical_redundancy_english_audit.md`.

## Five-vertex (K_4)-free original source

Let E be the **tree** on original vertices 0,1,2,3,4 with
exactly the four undirected edges

[
  02,quad 12,quad 13,quad 14.
]

It is (K_4)-free (in fact triangle-free). Take forbidden-clique
parameter (ell=4), numerical-H height (k=4), current original
(b=1), and **three distinct later top-original names**

[
  j(0)=2,qquad j(1)=3,qquad j(2)=4.
]

Compare the literal numbered old prefixes at (g=0) and (g=1)
(before generation 0 and before generation 1 of original 1).
Since (iota_4(i,q)=2(5i+q)), these are ([0,10)) and
([0,12)), **including all odd dummy coordinates**. The sole
new real coordinate is (iota_4(1,0)=10).

## The raw and canonical graph ages really change

For any nonempty future support U, the only earlier original
is 0. It is adjacent to later original 2 but not 3 or 4.
Therefore before the current-b generation 0 enters the prefix:

- at U={0}, the old common-neighbour numerical-H capacity
  is 1 (five copies of original 0, mutually nonadjacent);
- at every other nonempty support, the old common-neighbour
  capacity is zero.

At the next cut, the new b-generation 0 is adjacent in the
actual numerical-H ordinary binary L to **all three later
top-generation originals**, because the ORIGINAL edges 12,13,14
are positive. It joins every old common-neighbourhood, but
cannot join any earlier original copy at generation 0.
Thus the old capacity at support {0} stays 1, and at
each other support it grows to 1.

With (ell-1=3), write the integer graph-age values in the
support order

  ( {0}, {1}, {2},
    {0,1}, {0,2}, {1,2}, {0,1,2} ).

Both raw and canonical ages at the two cuts are respectively

[
  F_{mathrm{old}}=(2,3,3,3,3,3,3),
  qquad
  F_{mathrm{new}}=(2,2,2,2,2,2,2).
]

These are genuine integer-witness graph ages. The independent
regression enumerates **all** normalized weights
(w=(w_0,w_1,w_2)) with (w_0+w_1+w_2leq 3), verifies the
full inequality systems and the canonical suprema directly.

## A STRICT genuine age between them

Define the pointwise intermediate function

[
  H=(2,2,2,2,2,2,3).
]

Clearly
(F_{mathrm{new}} < H < F_{mathrm{old}}) pointwise, with strict
inequalities in at least one coordinate on each side.

Moreover H is a genuine integer-witness graph age:
every support T is attained by a normalized clique vector
respecting **all** of H's support constraints:

| Support T | H(T) | Globally feasible witness (w) |
|---|---:|---|
| {0} | 2 | (2,0,0) |
| {1} | 2 | (0,2,0) |
| {2} | 2 | (0,0,2) |
| {0,1} | 2 | (1,1,0) |
| {0,2} | 2 | (1,0,1) |
| {1,2} | 2 | (0,1,1) |
| {0,1,2} | 3 | (1,1,1) |

Every listed vector has total multiplicity <=3 and respects
the singleton bounds 2, pair bounds 2 and full bound 3.
Equivalently, computing `integerGraphAgeCanonical H` gives
exactly H.

**Conclusion:** The actual physical numerical-H canonical
ordinary-L ages change at one original-generation cut, but
the step is NOT an `AgeCover (IsIntegerGraphAge 3 4)` step,
because a genuine age H lies strictly between the endpoints.

## Why this does not refute the intended global construction

This is a (K_4)-free finite original source with three
distinct given later top names and (k=ell=4); no artificial
loops, repeated selected names, unphysical support shadow,
or missing odd dummy positions are used.

Nevertheless the example is not asserted to occur with
these exact ordinal labels in the fixed chosen left-dense
Henson enumeration or in the specialized resolved-copy
schedule. What it **disproves** is an unconditional deduction
from the verified ordinary-L numerical-H age theorem that
*every single physical canonical-age change must be one cover*.

A global selected-front cover schedule must therefore
**control which original columns and supports arise**, or
separate the simultaneous raw constraints into distinct
permitted cover operations; it cannot inherit coverhood from
the ordinary-L capacity formula alone. Full auxiliary
parameter-closed Kpt E/(B3) may introduce further events.
It is also independent of the labelled source-orbit/BRD proof.

The corresponding independent finite referee is
`scripts/check_k4_physical_canonical_noncover.py`,
which checks K4-freeness, the actual all-coordinate numerical-H
pools, raw and canonical ages, the intermediate age's
entire feasible weight family and the displayed seven
globally valid attaining witnesses. This is a finite model
check, not yet a standalone Lean formalization.
