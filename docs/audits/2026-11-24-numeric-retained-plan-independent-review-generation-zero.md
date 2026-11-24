# Independent review: concrete retained Plan and odd-cut closure

24 November 2026. Reviewer: generation-zero task, independent of the author.
Reviewed `docs/numeric_retained_plan_english_20261124.md`, SHA-256
`b25b253b3a1f4289b6bcfc7077f83d61ff3a853a25134c2e443426c3d7aaa63b`.

The stated English construction and local implication are approved for
formalization. No new source or compiler result is claimed by this review.

The argument was checked against `HPositiveFreeLevelOdd.lean`,
`HExactE.lean`, and `Kk/TrackDOddPlanFreeClosure.lean` at the current pins.

1. For every actual finite original, f(v)<=v<N keeps f(v) inside the
   carrier. A positive f(v) is odd by the exact canonical free-level
   theorem; an odd target has an empty incoming E column and hence
   free level zero. The zero case follows from freeLevel_le at zero.
   Thus f(f(v))=0, including k=0, without an out-of-carrier assertion.
2. Plan is finite by its explicit construction and bounded by tau.
   Each of its four summands has its actual free cut in Plan: anchor,
   cap end and added free-cut names map to zero, while a kept original
   has its free cut explicitly added. The singleton cap root's free
   cut tau is also retained. No closure hypothesis is being restated
   as a definition without proof.
3. Positive free level excludes the anchor, cap-end and added-free-cut
   summands. A remaining address is a genuine kept original; equality
   of Fin N values identifies it with that original. The two canonical
   address presentations both carry generation <=k, so the bounded
   injectivity theorem derives the exact role and TOP-generation shape.
   This avoids the earlier unbounded-alias problem.
4. An omitted bounded real cut below tau cannot have retained-auxiliary
   role, since its own Fin N address would be kept. Likewise, selected
   coded TOP is not omitted. The stated omitted-base predicate is the
   exact remaining case split. A dummy cap's bounded presentation gives
   all bounded root presentations by the same injectivity theorem.
5. Every planned cap ancestor is represented by the singleton cap
   original, tau gives the actual top seed, and off-plan cuts have no
   initial seed endpoint. The existing odd-cut theorem then uses the
   actual descending Run.I(c+1) inclusion with the now derived root and
   Plan free-cut closures. This applies to the enlarged seed family,
   not an unchanged theorem about the smaller TOP-only family.

The strict truncation below tau is essential. All generations of a role
flagged auxiliary base belong to this plan only when their addresses lie
below tau; the construction must prove that further bound before claiming
whole-block retention without qualification. The document preserves this
caveat. Outgoing E at odd/free-cut coordinates may remain positive, and
nothing here incorrectly treats them as isolated in the full signature.

The existing odd theorem concludes absence from Run.I(0). A generic
exact-plan induction phrased with noninterestingness can convert that
conclusion using the ordinary algorithm's actual-stage interestingness
criterion and final-tail identity, with the required c<tau retained.
This is a routine implication, not an additional source assumption.

No finite reference-age neutrality, selected no-split, chosen B3 at the
remaining real cuts, infinite resolved-Q realization, or cross-occurrence
retained-code equality follows from Plan finiteness alone. These application
obligations remain separate as stated in the proposal.

The planned implementation's explicit adapter is also approved: if the
actual pre-cut closure at c were interesting, `interesting_step` would
insert c into Run.I(c). The final-tail identity then puts c in Run.I(0),
contradicting the established odd nonselection. Thus a wrapper may return
both nonselection and noninterestingness, retaining c<tau. This does not
alter the reviewed source English or introduce a new mathematical premise.
