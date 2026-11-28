# Chronological selected-only retention (28 November 2026)

## Checked baseline and repair

The preceding root CI run 46151590413 compiled the strengthened
ResolvedLiveRound, ResolvedEventTrace, ResolvedRoundEvents, the actual
event schedule, and the repaired ResolvedNeutralCap. The first and
only reported build failure was the missing direct import of
IntegerAgeCoverUnitDrop in IntegerAgeCoverRestriction. Add the import
and explicitly name the dependent cover's sort in the projected-age
proof. The complete strict audit for these new modules has not yet
passed. The 1607-report merged checkpoint (including the 24 count)
remains verified.

## English proof of the chronological bridge

At event k, let the future list be the requested original indices
whose coding event is strictly greater than k, in increasing order.
This list is independent of all keep flags. Each such original
belongs to the even live tail of the event's round: round indices
are monotone in global event indices, and the coding event of i
has round i. The actual prefix through the beginning of event k
maps bijectively onto its preOld set, by the checked chronological
enumeration. The end maps onto postOld: postOld at k is preOld at
k+1 by the prior-block characterization. Every ordinary edge on
this pool and every column to the fixed future list agrees with
the native event table. Therefore all canonical ages transport
exactly by the established induced-image theorem. Likewise old
column equality transports; a true cover's no-split property and
cover-or-equality restriction apply at the actual boundaries.

Keep an auxiliary event if its selected future age changes or
two previously equal selected columns become different during it.
This is precisely a whole-event test, using only the actual graph
and selected original indices. Code events are kept iff selected.
No future extra coding cap appears. We intentionally use an
explicit complete-column split test, not a proposed abstract
diary parser. The earlier coarse construction remains separate.

For an omitted auxiliary event, the full future-list ages agree
at its endpoints. Any intermediate old prefix lies between these
pools, so antitonicity gives equality at every member. Canonical
age pullback along the map from any sublist to the complete list
preserves these equalities (including repeated labels and empty
lists). Old-equivalent terminals at an intermediate prefix were
old-equivalent at the start, so the event's no-split test gives
the required equality of the new bit. At a meaningful omitted
coordinate the actual moving front consists of selected originals
strictly later than that coordinate. If it is in an auxiliary
event, each such original has a strictly later coding event:
monotonicity gives weak order, and the auxiliary event cannot
be the coding event. Thus the front maps into the fixed future
list. Use the unpadded argument and the verified one-gap transport.
At a coding cut use actual saturated coding neutrality.

Consequently the neutral-cap envelope has all of its hypotheses
derived for these retention flags. Select the last original using
sup(S). Every requested original's address is retained; the
actual representing pair with the neutral common cap lifts under
the one envelope map. Complete inverse-source recovery identifies
the source code with the ordinary retained graph through that
original. The artificial cap pair is strictly later, hence
truncation removes it. This gives common actual source codes
without extra cap-created history events.

## Scope and next step

The new retention criterion is explicit and selected-only, not
yet a theorem that its visible-event history is accepted by
NonedgeHistory.next. The cover restriction requires *distinct
occupied old classes*, not arbitrary terminal labels. The next
step is to construct their finite representatives, classify
markers as one selected split or singleton clipping, transport
saturated coding legality, and show the retained block's actual
positive mask and size are read from the projected transition.
This gives the sharp diary-to-source comparison and palette count;
the lower-bound realization remains independent.

No new numerical count has been asserted. No unchecked manuscript
validation marker is promoted. All new endpoints are candidates
pending the combined exact-head Lean build and strict audit. This
is deliberately one push rather than separate CI runs per repair.
