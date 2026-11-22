# Two-sort profile bridge: English proof before Lean

Date: 22 November 2026.

## Purpose

Connect the elementary capacity triples used in `NonedgeHistoryCount`
to the existing `IntegerGraphSupport 2 4`, `IntegerCliqueWeights 2 4`,
`IsIntegerGraphAge 2 4`, `AgeLe`, and `AgeCover` definitions. This is a
representation theorem for finite sorted clique ages. It does not
identify the histories with actual coding-tree records, prove
unavoidability, or prove a Ramsey upper bound.

## Exact support dictionary

There are exactly three nonempty supports on two sorts: `{0}`, `{1}`,
and `{0,1}`. They all have cardinality at most `4-1`. Map the capacity
triple `(a,b,c)` to the function with these three values respectively.
Extend it to all four subsets by assigning zero to the empty support.
No additional or omitted support is allowed.

For an arbitrary natural-number vector `(x,y)`, all support inequalities
are exactly

    x <= a, y <= b, x+y <= c.

The empty-support inequality is `0 <= 0`. In particular, since `c<=3`,
every feasible vector has total at most three and each coordinate below
four. It therefore gives a literal member of the repository's normalized
`IntegerCliqueWeights 2 4`. Conversely each such normalized member has
exactly the same support sums. Normalization loses no feasible vector.

## Canonicality and completeness

The existing `IsIntegerGraphAge` predicate requires positive capacities
at most three and an integer witness saturating every support while
respecting all bounds. The triple predicate requires

    a <= c, b <= c, c <= a+b.

The three witnesses `(a,0)`, `(0,b)`, and `(a,c-a)` prove sufficiency;
their total weights are at most three. Saturation of each support proves
necessity. Thus these two canonicality predicates are equivalent.

Conversely, any existing two-sort integer graph age has values in
`{1,2,3}` on each of the three supports. Subtract one from each value to
obtain the three `Fin 3` coordinates used by `Bounds`. Reconstructing the
age returns the original function on every support. Hence the elementary
state space is neither missing nor adding any abstract canonical ages.
The correspondence is injective because evaluating it on the three
supports recovers each coordinate.

## Orders and covers

Pointwise order on the generic age functions is exactly coordinatewise
order on the three capacities. Because every generic canonical age has
a corresponding triple, an arbitrary intermediate generic age in an
`AgeCover` test corresponds to an intermediate canonical triple, and
vice versa. Therefore the history machine's `Covers` predicate is exactly
the repository's `AgeCover (IsIntegerGraphAge 2 4)` predicate under this
map. This proves the full-poset comparison, not just one direction or a
comparison restricted to reachable profiles.

Finally, the generic canonicalizer fixes every mapped canonical profile
by its existing upper-bound and greatest-admissible-age properties.
There is no independently defined canonicalizer in this bridge.

## Adversarial checks

- Use all three nonempty supports, including the mixed support.
- Include empty support zero explicitly; it is outside the generic
  nonempty-support subtype but cannot impose an extra condition.
- Allow unbounded natural-number input weights and prove that feasibility
  itself implies the required normalization bound.
- Permit repeated labels in cliques; weights are not Boolean.
- Recover arbitrary existing age functions, not only mapped ones.
- Compare covers against the entire generic class of canonical ages.
- Preserve ordered left/right sort coordinates; do not quotient them.
- Prove canonicality without assuming a list of 13 states or the count24.
- Do not claim every abstract age is a distinct actual coding-tree front.
- Do not claim correspondence of split/cover/code histories with full
  successor-tree sources or with unavoidable colorings.

## Validation status

`Kk/NonedgeProfileBridge.lean` compiled successfully with pinned
Lean 4.35.0-rc3, using an explicit output path. The imported generic
`IntegerWitnessCanonical.lean` also compiled successfully. No proof
errors or changes to the existing generic age definitions were needed.

The following ten exported results were checked with `#print axioms`:

- `all_support_feasibility`
- `weights_feasible_iff`
- `feasible_iff_existing_weights`
- `toAge_is_age_iff`
- `toAge_boundsOfAge`
- `toAge_injective`
- `exists_unique_profile`
- `below_iff_ageLe`
- `covers_iff_ageCover`
- `canonical_fixed`

Every report contains only `propext`, `Classical.choice`, and
`Quot.sound`. There is no `sorryAx`, custom axiom, or `native_decide`
dependency. This closes the finite age-representation gap. Actual
history realization and the two infinite Ramsey obligations remain
outside this module.
