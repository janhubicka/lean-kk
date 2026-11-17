# Track F — mixed occupancy in finite daughter-to-parent clique transfer

17 November 2026. **English-first correction and adversarial audit.**
The verified finite labelled clique-transfer theorem of merged PR #259
is correct, but its hypothesis that EVERY refined sort contains at most
one selected vertex is too strong for the richness induction:
we split the maximum-rank sorts, while unchanged lower-rank sorts
can still carry several vertices of the prescribed finite graph B.

This note repairs the missing generality before modifying Lean.

## General abstract lemma

Let D be the refined sort set, P the old parent sort set, and
pi : D -> P the sort-collapse map (which need not be injective).
Let B be a finite set of future vertices with refined label
sort : B -> D. Let oldRaw(T) and newRaw(S) be raw clique multiplicity
bounds for nonempty old supports T and refined supports S.

Assume:
- for every nonempty old support T, the **parent** count
  |{x in B : pi(sort x) in T}| is at most oldRaw(T);
- for every refined **singleton** {i}, the actual refined count
  |{x in B : sort x=i}| is at most newRaw({i});
- on EVERY refined support S of at least two distinct sorts,
  newRaw(S)=oldRaw(pi[S]).

**Conclusion:** B obeys every refined raw support bound.

Proof. On singleton supports this is precisely the second
hypothesis. For |S|>=2, the vertices whose refined labels lie
in S form a subset of the vertices whose collapsed parent labels
lie in pi[S]. Thus their number is at most the parent count,
which is bounded by oldRaw(pi[S])=newRaw(S). The image support
is nonempty even when pi identifies different daughters.

The existing integer canonicalizer preserves the feasible finite
labelled clique vectors, so the same B is feasible after
canonicalizing the refined raw bounds, provided its total clique
cardinality lies below ell. We do not claim that the *numerical*
canonical mixed support bounds remain unchanged.

## Application-ready split/untouched version

Fix a finite set N subset D of newly created daughter sorts.
Instead of assuming the general singleton bounds directly, assume:
1. for i in N, at most ONE B vertex is labelled i and
   1 <= newRaw({i}) (the daughter still has positive rank);
2. for i notin N, the old singleton parent bound is no greater
   than its new raw singleton bound:
   oldRaw({pi(i)}) <= newRaw({i}).

Then the general singleton bound follows: for i in N, it is
1 <= newRaw({i}); for i outside N, the count on i is bounded
by the count on the parent pi(i), which is bounded by
oldRaw({pi(i)}) <= newRaw({i}).

This matches the richness proof. It does NOT require
unchanged lower-rank sorts to carry at most one vertex.

## Counterexample to the overly restrictive application

Take two parent sorts p0,p1 and two refined sorts d0,d1 with
identity collapse pi. Refine only d0, leaving d1 untouched.
Let B have TWO vertices both labelled d1. If the old and
new singleton raw bounds at d1 are 2 and the parent mixed
bound admits B, B remains admissible: no new fresh marker
affects d1. Yet the PR #259 assumption "at most one selected
vertex in every refined sort" is false for d1.
Thus PR #259 cannot by itself be invoked on this legitimate
induction step; its mathematics is not incorrect, its scope
must be generalized as above.

## Hostile checks

1. The old parent bound must hold for EVERY nonempty support,
   not just the full old front.
2. The collapse map may identify several newly split daughters;
   use finite-set images without assuming injectivity.
3. Unchanged singleton bounds are allowed to be larger than 1;
   forcing their count to <=1 would silently discard valid B.
4. Newly split daughters require explicit rank >=1, not merely
   cardinality at most one.
5. The mixed raw age equality must be established from actual
   pairwise-disjoint fresh marker sets; the present counting lemma
   takes that geometric equality as a premise.
6. Canonicalization can lower mixed numerical values, but does
   not remove B when the whole raw feasible-vector system holds.
7. The finite result does NOT establish simultaneous rank-large
   existence for all source types or physical target realization.
8. The source/target rank-comparison direction from a future
   clique is independently verified in PR #275 but cannot be
   used without a genuine clique witness in the chosen fibre.

## Lean acceptance

Add general exact finite occupancy transfer and its split/untouched
corollary, with named standard-only axiom reports. Keep the old
#259 theorem unchanged: it remains a valid special case.
The olive manuscript should explicitly distinguish newly split
daughter sorts from unchanged sorts and cite this remaining
finite-gluing obligation until the new Lean gate passes.
No black-text or global BRD marker is promoted.