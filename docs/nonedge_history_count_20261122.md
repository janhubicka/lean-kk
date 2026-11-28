# Non-edge finite histories: independent count and its precise scope

Date: 22 November 2026. This note precedes the Lean implementation.

## Statement to formalize

The finite transition system described below has exactly 24 complete histories.
It records one split and two independent coding events in the proposed
two-vertex normal form for the homogeneous universal K4-free graph. The
claim concerns the transition system itself. Identification of these
histories with unavoidable colours and complete successor-tree source
orbits remains a separate mathematical obligation.

## States are derived from integer clique feasibility

A two-sort capacity profile is a triple `(a,b,c)`, for the nonempty supports
`{left}`, `{right}`, and `{left,right}`. Each capacity is an integer from
1 to 3. A clique multiplicity pair `(x,y)` is feasible precisely when

    x <= a,   y <= b,   x + y <= c.

All three stated capacities are attained by feasible integer pairs if and
only if

    a <= c,   b <= c,   c <= a + b.

Necessity follows from the saturating witnesses. For sufficiency, the
singleton witnesses are `(a,0)` and `(0,b)`; the joint witness is
`(a,c-a)`. The inequalities ensure that subtraction is untruncated and
that `c-a <= b`. These conditions give the complete two-sort state space
without importing a proposed diary list or a previously computed count.

For canonical source profile `q`, pointwise comparison `q <= p` is
equivalent to inclusion of its feasible integer multiplicity pairs in
those of `p`. The forward implication follows by transitivity. For the
reverse implication, apply inclusion to the three saturating witnesses
of `q`. Thus the cover order is the literal feasible-class order.

There are 13 abstract canonical integer profiles. This is not a claim
that all 13 occur as distinct actual two-type fronts: for example,
`(3,3,3)` is abstractly canonical and unreachable below a legal split.
The full poset has 18 downward cover edges. Exactly 10 canonical
profiles lie below at least one split profile; the excluded profiles
are `(1,3,3)`, `(2,3,3)`, and `(3,3,3)`. All legal successor states are
canonical, so the use of a larger ambient finite type does not permit
noncanonical pair profiles in a history.

The upper bound three is the total size of a clique permitted in a
K4-free graph. The correspondence with an actual common-neighbour
profile in a Henson type tree is a separate interface; the elementary
integer-witness assertion does not itself assume or prove that every
such type occurs in every induced Henson subcopy.

## Literal transition rules

There are four kinds of machine states:

1. one unary rank before the split;
2. a canonical two-sort profile;
3. one unary rank after the first coding event;
4. the completed empty state.

A unary age change lowers its rank by exactly one. A two-sort age change
is a strict pointwise predecessor with no canonical profile strictly
between the two endpoints. This is checked against the complete finite
space, rather than an assumed list of allowed support changes.

The split from unary rank `r` gives `(r,min(r,2),r)`: the new right child
sees a fresh isolated marker and hence has clique capacity at most two,
while summing its two child weights recovers the parent constraint.

A left zero-code is permitted exactly when `a=1` and `c=b`; a right
zero-code is permitted exactly when `b=1` and `c=a`. The surviving unary
rank is respectively `b` or `a`. Left and right codes remain different
events even when they have the same successor rank. This preserves the
multiplicity of the two possible coding orders at `(1,1,1)`.

The last unary sort is coded only at rank one. No split occurs after the
first code. An early unary code before the required split cannot extend
to an accepted two-vertex history, so such dead transitions are omitted.

Assign each state its numbers of remaining split and coding events:
`(1,2)` before the split, `(0,2)` in a pair state, `(0,1)` after the
first code, and `(0,0)` when done. Each transition decreases these
inventories by exactly its event kind. Induction on an accepted event
list then proves that every initial accepted history contains exactly
one split and two coding events.

## Termination and exhaustive enumeration

Use the natural-number measure `3*r+1` before the split, `a+b+c` on a
two-sort profile, `r` after its first code, and zero on the completed
state. Every transition strictly lowers the measure. In particular the
initial state of rank three has measure ten, so every complete legal
event list has length at most ten.

The finite enumerator returns every accepting event list of length at
most its fuel. A general membership theorem must establish both
soundness and completeness. The strict measure theorem then removes the
fuel condition from the enumeration at fuel ten. Thus the final equality
counts all legal complete histories, not merely a bounded sample.

Kernel evaluation of the resulting finite set should give 24. The
three possible split ranks have unique preceding unary cover chains.
Their resulting pair states `(3,2,3)`, `(2,2,2)`, and `(1,1,1)` have
respectively 16, 6, and 2 complete continuations. Their sum is 24.

## Adversarial checks before implementation

- All three nonempty supports are retained. Pair capacity is not inferred
  from singleton capacities.
- Capacities are positive, so empty or impossible sorts are not silently
  accepted as live branches.
- Clique weights are natural numbers, not restricted to zero or one.
  Multiple clique vertices of one type are permitted by the definition.
- The joint witness explicitly checks natural-number subtraction.
- Every canonical profile is considered when testing covers, including
  profiles not reachable from the chosen split.
- Equality is not an age-change step; non-cover jumps are rejected.
- The maximal-rank split includes the right-child capacity drop.
- Coding rank one alone is insufficient; the joint survivor equality is
  also required.
- Left and right codes are separate events, even for identical successor
  states. No coordinate-permutation quotient is used.
- Complete event histories contain both coding events and the required
  split. A premature empty state is not a terminal success.
- The enumerator is accompanied by a mathematical length bound and a
  membership equivalence, so the chosen fuel is not an unproved cutoff.
- The Lean numerical proof must use kernel reduction, not `native_decide`,
  `sorry`, or a custom axiom.
- No assertion in this file establishes the Ramsey upper bound or
  unavoidability. The number 24 is not used as a definition of the history
  space.

## Implementation status

Implemented in `Kk/NonedgeHistoryCount.lean` and successfully compiled
with the repository's pinned Lean 4.35.0-rc3 toolchain:

```text
/home/agent/.elan/bin/lake build Kk.NonedgeHistoryCount
Build completed successfully (3137 jobs).
```

The only build warning recommends the newer Lean module-system syntax
for the Mathlib import. There are no proof errors or incomplete proofs.

The principal checked declarations are:

| Declaration in `Kk.NonedgeHistory` | Checked statement |
| --- | --- |
| `isProfile_iff_exactCapacities` | The arithmetic profile conditions are exactly saturation by integer clique multiplicities. |
| `below_iff_feasible_inclusion` | Pointwise order equals feasible-class inclusion for canonical source profiles. |
| `canonicalProfiles_card` | The abstract canonical profile poset has 13 elements. |
| `coverEdges_card` | Its complete downward Hasse relation has 18 edges. |
| `profilesBelowSplits_card` | Exactly 10 canonical profiles lie below a permitted split. |
| `splitProfile_feasible` | Splitting rank `r` is precisely the constraint `x+y <= r` and `y <= 2`. |
| `next_valid` | Every legal successor has a canonical pair profile when in the pair phase. |
| `next_measure` | Every legal transition strictly decreases the natural-number measure. |
| `initial_accepts_one_split_two_codes` | Every complete initial history has one split and two coding events. |
| `mem_histories_iff` | The fuel enumerator contains exactly the accepted lists within that length bound. |
| `mem_nonedgeHistories_iff` | At the proved initial bound, enumeration is equivalent to unbounded acceptance. |
| `history_card` | The type of all unbounded accepted initial histories has cardinality 24. |
| `split_capacity_three_card` | Continuations from `(3,2,3)` number 16. |
| `split_capacity_two_card` | Continuations from `(2,2,2)` number 6. |
| `split_capacity_one_card` | Continuations from `(1,1,1)` number 2. |

The type `History` is the subtype of all finite event lists satisfying
unbounded acceptance from the initial state. Its definition contains
neither the number 24 nor a fuel parameter. Its finite-type instance
comes from the proved soundness and completeness theorem.

All numerical statements use `by decide`, so the resulting proof terms
are checked by Lean's kernel. A transitive `#print axioms` audit of all
the declarations in this table (and the direct finite-set cardinality
theorem) reports exactly:

```text
[propext, Classical.choice, Quot.sound]
```

There is no `sorryAx`, custom mathematical axiom, or native evaluation
axiom in these dependency closures. These are Lean's usual foundational
axioms, not a claim that the development is axiom-free.

This completed finite proof does not bridge the custom two-sort
multiplicity model to every actual Henson type-tree record or to the
repository's general integer-age interface. In particular it establishes
neither canonization of arbitrary non-edge colourings by these histories
nor unavoidability of all 24 histories in every induced Henson subcopy.
Those global claims remain independent obligations for the BRD theorem.
