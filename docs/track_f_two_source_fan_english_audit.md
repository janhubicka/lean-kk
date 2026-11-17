# Track F — two-source finite fans with disjoint fresh Henson markers

17 November 2026. **English proof and adversarial audit before Lean.**
This is a genuine two-source refinement of the merged finite-fan
theorem #255. It requires no published diary characterization and
does not assert simultaneous *graph-age* richness.

## Statement

Fix the ACTUAL chronological finite Henson one-type tree for an
ordinary edge table E. Let two source type nodes u,v have respective
positive zero-based ranks r+1 and s+1. Suppose S is (r+1)-large
above u and T is (s+1)-large above v.

For any prescribed finite k,l, choose:
- k rank-r descendants a_1,...,a_k above u, each carrying
  r-largeness of S, pairwise incompatible, with pairwise
  disjoint fresh positive-neighbour marker sets relative to u;
- l rank-s descendants b_1,...,b_l above v, each carrying
  s-largeness of T, pairwise incompatible, with pairwise
  disjoint fresh markers relative to v;
- with the CROSS-SOURCE property:
  (neighbours(a_i) \ neighbours(u)) is disjoint from
  (neighbours(b_j) \ neighbours(v)) for every i,j.

We do NOT claim these two families realize arbitrary edges
between coding vertices, or that their source-target target-prefix
fibres are compatible. The goal is exact temporal marker isolation.

## Construction

Apply the verified single-source finite-fan theorem #255 to S
above u, obtaining the first family F of k daughters. Let H be
larger than every daughter height in F and at least level(v).
Extend the *original* second type v by zeros to height H. This
preserves its rank s+1 and its T-largeness, by the verified
zero-padding and large-cone monotonicity theorems.

Apply the same verified finite-fan theorem to T above the
zero-padded v. Obtain l daughters b_j above height H,
rank s, T-large, with pairwise incompatible cones and
pairwise disjoint fresh markers relative to the zero-padded
v (equivalently relative to v, since their neighbourhood
sets are identical).

For a in F, every fresh positive marker of a lies below
level(a) < H. A daughter b_j extending the zero-padding
of v has the SAME old positive and negative bits as v
at every index below H. Therefore no marker of b_j
outside neighbours(v) can lie below H. This proves the
cross-family marker disjointness exactly.

## Hostile checks

1. We never assume u and v have the same rank. Each finite
   fan is chosen using its own rank and large set.
2. A first family may contain many daughters of the same
   parent; H is chosen above the MAXIMUM of their heights,
   not merely above the root u.
3. Root neighbourhoods may differ. The cross-family result
   compares NEW positive markers relative to each family's
   OWN root. Comparing to the other root would be invalid.
4. The second source v is zero-padded, not extended with
   arbitrary positive bits: preserving negative bits below
   H is essential for cross-family disjointness.
5. No assumption of source type compatibility is needed to
   prove marker disjointness. If the final application requires
   two distinct active sorts, the roots must also be shown
   distinct at the same original level, so their later types
   cannot collapse into one sort.
6. Temporal marker separation does not force future coding
   vertices in different cones to be adjacent or nonadjacent
   in any prescribed way. That belongs to the finite
   gluing/richness induction.
7. The theorem is only a TWO-source step; extension to an
   arbitrary finite front requires a further induction and
   is not claimed here.
8. The theorem uses actual one-type full prefix agreement,
   not an abstract preorder whose incomparable nodes might
   share later extensions.
9. No numerical diary count or lower BRD formula is used.

## Lean acceptance

Prove the general cross-root `fresh_markers_disjoint_of_later_zeroPad`
lemma and the two-source finite selection theorem by composing
the existing `rank_large_finite_fan` with zero padding.
Retain the member largeness and pairwise cross-marker conclusion
in their exact types. Run a dedicated exact-head Lean build and
strict named transitive-axiom gate. Black text and global BRD
validation marks must remain unchanged.