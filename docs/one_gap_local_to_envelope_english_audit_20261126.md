# From local ordinary conditions to the actual planned envelope

## Proof before implementation

Work in one forbidden-free finite ambient graph partial structure. Fix
the planned finite retained levels `I`, the seed set `X`, and a complete
pool `V` of ambient originals. Assume seeds lie below the top, their
levels lie in `I`, every pool original has its free endpoint in `I`,
and every retained positive-free-level original belongs to `V`.

At each omitted cut below the top specify a selected list, possibly empty.
Assume no selected ordinary split at that cut, every positive eligible
pool original belongs to the selected list, every eligible nonselected
original has zero old ordinary columns, and the entire canonical selected
old-column age is unchanged by restoring the cut. Singleton age equality
forces each positive selected type to have an old neighbour. That
neighbour distinguishes it from every nonselected zero-old-column type.
Together with selected no-split this proves full-pool column coherence.
Graph symmetry and loop/diagonal neutrality, with actual free-level
eligibility, then give complete dependent next-type fibre agreement,
including both auxiliary directions.

The closure normal form and fibre agreement exclude all cut-level
endpoints (and hence full closure meets), by
`OneGapStructuralExclusion`. The complete pool prescription is then
constructed by `OneGapPrescribedPool`; it covers every crossing, has
admissible targets, and satisfies the actual corrected B3 test. Thus
there is an actual monoid map skipping just this cut and taking every
crossing to its required next ancestor. The forced-retention descending
induction yields the full envelope invariant at stage zero. Its exact
level-range theorem says the represented levels are precisely `I`
together with the unchanged tail above the top.

The final theorem does not assume a full-type fibre certificate, an old
neighbour, a B3 witness, a no-meet conclusion, an admissible target, a
skipping map or an envelope. These are all derived along the preceding
proof chain.

## Boundary

This is a local-to-global construction theorem. Its explicit ordinary
column, endpoint, positive-source and canonical-age hypotheses must
still be established for every projected event of the countable
resolution. Neither that resolution nor the common source orbit nor
the lower Ramsey bound is asserted here. The list of selected labels
may vary with the cut and may contain repetitions. For an empty list,
positive-source classification excludes every positive crossing. Any
new forbidden clique through the cut would have an upper positive
vertex, which is impossible; this separately proves full B3 in that
case. The anchor `0` is retained so every skipped cut is positive.
