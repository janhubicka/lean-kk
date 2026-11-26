# Exact compression of one-gap retained coordinates

## Statement and proof, before Lean implementation

Let `f : Nat → Nat` be strictly increasing. Retain the anchor 0 and, for
each selected ordinary index `i`, the pair of coordinates `2 f(i)+1`
(the preceding isolated gap) and `2 f(i)+2` (the ordinary vertex). The
compressed enumeration is explicitly

* `e(0)=0`;
* `e(2i+1)=2f(i)+1`;
* `e(2i+2)=2f(i)+2`.

The map is strictly increasing: it is increasing inside a pair, and
strict increase of `f` separates distinct pairs. It preserves exactly
the meaningful positive even coordinates. Consequently the ordinary
table pulls back to the one-gap padding of the graph with edge
`G(f(i),f(j))`; all other entries are zero.

The auxiliary table also pulls back literally. At a dummy target both
tables are zero. At a meaningful target `v`, its preceding gap is
retained and `e(v-1)+1=e(v)`. Hence, using strict order preservation and
reflection,

`e(u)+1 < e(v)` if and only if `u < v-1`, if and only if `u+1<v`.

Thus the full finite code on the anchor and the first `n` retained
pairs, including both directed ordinary atoms, diagonal atoms and all
auxiliary atoms, is determined by the finite ordinary table on the
first `n` selected vertices. Two occurrences with equal such ordinary
tables have exactly equal compressed finite codes, even when the
selected absolute coordinates are different.

## Adversarial boundaries

The anchor is necessary to obtain this literal coordinate convention.
Every retained meaningful vertex must retain its immediate preceding
gap. Retaining a meaningful vertex without that gap would invalidate
the auxiliary-table identity. The finite result includes `n=0` and
does not require loop-freeness or symmetry of `G`: it is an identity of
the entire table. A neutral cap can be one of the selected vertices,
but its neutrality and position must be established separately in the
application.

This proves coordinate compression, not diary classification. It does
not assume or conclude that the macrodiary determines the selected
ordinary table, that every selected occurrence has the required
retained set, or that an actual envelope inverse source is this code.
Those application and shape-map recovery steps remain separate.
