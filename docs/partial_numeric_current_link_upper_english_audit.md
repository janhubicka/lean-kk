# Track A — original-neighbour capacity of an actual partial-cut clique containing the current original

15 November 2026. English-first proof and adversarial review.

## Statement

Let k,b,g,M be genuine numerical-H parameters, with g<=k.
Let P be ANY finite set of original names (in the target
application P consists precisely of earlier U-neighbours).
Let s be a directed clique for the actual finite numerical-H
ordinary binary L table, lying in

    Copies_k(P) union {iota_k(b,q):q<g}.

Suppose s contains the current original b at an actual
generation m<g. Set
    S_b(P) = {i in P : E(i,b)=true}.

Then
    |s| <= 1 + cap_E(S_b(P)).

This is independent of the height bound |s|<=g proved
in the preceding generation-height module. Together they
give the desired **upper** min(g,1+cap_E(S_b(P))) in the case
where a clique actually contains the current original.

## Proof

Put v=iota_k(b,m) and t=s\{v}. A positive numerical-H
L atom cannot join two copies of the SAME original name,
regardless of E(b,b). Thus no other partial copy of b can
lie in s. Because the source pool is the union of all
complete real copies of P with the partial b copies,
every member of t lies in Copies_k(P).

The established real-copy projection theorem proves that
orig_k is injective on any directed numeric clique in
Copies_k(P), and the original-index image forms an E clique.
Apply it to t, a directed clique by restriction.

Each x=iota_k(i,q) in t is adjacent to v in numerical H,
so the positive-real-edge projection to original names
proves E(i,b)=true (in the correct directed orientation).
Therefore the entire original image orig_k(t) is contained
in S_b(P). Its cardinal is exactly |t| by decoder
injectivity, so

  |t| = |orig_k(t)| <= cap_E(S_b(P)).

Since v∈s, |s|=|t|+1, giving the required bound.

This proof neither assumes P is a clique nor uses |P|
in place of cap_E(P); it does not assume P is consecutive,
and avoids any premature top-generation equality.

## Hostile checks

1. The original indices in P may have gaps or include auxiliary
   originals; only their actual E edges matter.
2. A numeric directed clique requires all positive ordered
   L edges, so a duplicate current-original copy cannot
   appear alongside v.
3. Even E(b,b)=true cannot create a numerical-H same-original
   positive L edge: the generator demands two distinct
   original names.
4. No selected future types are assumed in the lemma;
   application to a support U uses the exact physical
   common-pool identity and substitutes P=P_U.
5. The bound uses a **directed original E clique capacity**,
   not a cardinality bound on S_b(P).
6. The image injectivity relies on the existing certified
   real-copy positive projection, not a new reindexing of E.
7. The original adjacency E(i,b) is obtained by projecting
   the actual ordered L edge x→v.
8. No symmetry hypothesis is needed for this particular
   ordered upper bound; symmetry is provided later when
   deriving the graph-specialized sharp equality.
9. s might be singleton {v}; then t is empty,
   cap_E(S_b(P))≥0 and the bound correctly gives |s|≤1.
10. P may be empty and b may not belong to P.
11. The entire considered pool is real, without odd dummies.
    In the U-common-neighbour application the odd dummies
    have already been removed by nonempty support.
12. The g<=k bound makes q<g a bounded real generation;
    the original-link upper bound itself is independent
    of a further strict generation counting estimate.
13. This does NOT prove a lower staircase witness of
    size min(g,1+cap_E(S_b(P))). That is a separate
    constructive obligation.
14. No actual recursively selected future original is
    constructed; P and s are given.
15. No full dependent Kpt E/(I1)--(I3)/(B3) comparison,
    labelled orbit or BRD is asserted.

## Lean plan

Implement an independent module
Kk/PartialNumericCurrentLinkUpper.lean. Restrict the clique
to s.erase(v), prove inclusion in the complete real copy
pool by the same-original no-edge theorem, reuse the
certified injective original decoder and projected
original clique, and apply directedClique_card_le_capacity
to the filtered original neighbour set. Close the
cardinality bound by Finset.card_erase_add_one.

Require exact-head direct build, strict qualified
standard-only named axioms and full Lake. Leave the
stack as DRAFT until source proofs are kernel-checked.
