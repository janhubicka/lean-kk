# Track F — exact preservation of all source raw supports under private markers

19 November 2026. English proof and hostile audit FIRST. This supplies a concrete, independently checkable hypothesis for the original/refined source-age sandwich merged in PR #399.

## The statement

Let `u_i` and `w_i` be finite genuine Henson source one-types for an ACTUAL graph E, sharing common old level m and common refined level M, respectively. For every active i assume:

1. `u_i ≤ w_i` in the **chronological two-bit type preorder** (so all old positive/negative bits agree).
2. `rank(w_i)=rank(u_i)` (equal genuine singleton clique capacity).
3. Every original x≥m is a positive **fresh** old neighbour of at most one refined coordinate: for i≠j there is no x≥m in both N(w_i) and N(w_j).

Then for **every nonempty support** S of active coordinates, including singleton and all mixed supports:

    Raw_E,m((u_i), S) = Raw_E,M((w_i), S).

No target embedding, rank-largeness, Henson left-density, or diary assumption is needed for this purely finite source claim. The absence of shared fresh markers is a literal finite condition on the *completed* refined front; source refinement chronology is not assumed.

## Proof in English

**Singleton S={i}.** For an actual consistent Henson one-type t, its zero-based rank is `(ell−1−cliqueCapacity(N(t)))−1`, and consistency ensures `cliqueCapacity(N(t))<ell−1`. Thus equal ranks imply equal old-neighbour clique capacities (there is no truncated-subtraction ambiguity). The common-neighbour pool for the singleton support is exactly N(t), because all its neighbours lie below the respective type level. The raw singleton value `ell−1−capacity` is therefore unchanged.

**Mixed S with at least two sorts.** Choose distinct i,j∈S. If x is in the refined common neighbour pool, it is a neighbour of both w_i and w_j. The no-shared-fresh-markers assumption forbids x≥m. Hence x<m. The chronological extension condition gives, for every k∈S, `x∈N(w_k) ↔ x∈N(u_k)`; so x is in the old common pool. Conversely, for every x in the old common pool, x<m≤M and the same chronological old-bit equivalences put x into the refined common pool. Therefore the two genuine common-neighbour pools are **literally equal**; their actual finite directed clique capacities and raw ages agree.

This argument is independent of the size of S and works with arbitrary existing old overlaps or triangles. New fresh neighbours can have arbitrary mutual E-edges, and can increase the capacity of an individual neighbourhood only if rank decreases; equal-rank prevents that at singletons.

## Corollary for source/target transfer

Plugging the derived full raw-source equality into the verified PR #399 conditional sandwich gives exact support source↔target finite-class equivalence and, for every finite symmetric K_ell-free B, complete all-support canonical integer-age test equivalence. The target cutoff needs to contain images of the OLD positive source neighbours only. The refined roots provide the actual rank-large target fibres; they may contain new positive markers whose images under a nonmonotone embedding lie above the target cutoff.

## Adversarial audit

1. The new-neighbour condition is imposed on **every pair of distinct sorts**, not just adjacent sort indices. If the same new marker occurs in two coordinates, a mixed common pool can change even if both singleton ranks remain equal.
2. Fresh markers are measured relative to the common old level m, not relative to individual intermediate levels. All positive markers at or after m are covered.
3. Old→new is chronological type extension preserving all old **0 and 1** bits, not mere inclusion N(old)⊆N(new). For mixed pools, the converse direction uses negative-bit preservation.
4. Singleton rank equality alone does not preserve mixed raw ages; disjoint fresh markers are indispensable.
5. Conversely no shared fresh markers alone does not preserve singleton raw ages; rank equality is indispensable.
6. The monotonicity of `finiteHensonTypeRank` is not assumed to be injective outside the valid safe range; consistency bounds guarantee that truncation does not erase differences here.
7. Empty support is intentionally omitted from graph-age assertions, although its common pool may change from [0,m) to [0,M).
8. The common old and refined levels are explicit; without them, the prefix range used in raw support definitions could differ from the type level.
9. No numeric assumption that raw support functions are already canonical or positive graph ages is needed.
10. The proof works for any ell for which such genuine safe types exist, and uses actual directed clique capacity rather than cardinality of old common neighbours.
11. The theorem is finite and source-local; it does not prove the marker-disjointness condition can be maintained while refining all target-compatible fibres.
12. No target one-type construction, diary occurrence, coloured lower bound, or BRD count is asserted.
13. The mixed-pool proof requires two genuinely **distinct sort indices** in S; a graph B may still repeat a sort arbitrarily many times, which is handled by the independent source-richness theorem.
14. New source type levels may be very large and newly positive marker images may lie arbitrarily late in target order; the corollary avoids any bound on those images.
15. If d=0, no nonempty S exists and the equality is vacuous; proof must not choose an arbitrary Fin(0) index.
16. If d=1, every nonempty support is a singleton; disjointness is vacuous and the rank argument suffices.
17. All formulas have the exact standard `trackFCommonNeighbourPool` and `trackFCommonRawAge` definitions used in the previous Lean transfer, avoiding a new shadow or proxy age.
18. No frozen black manuscript text is changed; a validation note may cite the result only after exact-head Lean and named transitive-axiom gate pass.

## Gate

Formalize: (A) safe-type rank equality forces equal actual old-neighbour clique capacity; (B) pairwise-private fresh markers force literal equality of all mixed old-common-neighbour pools; (C) combined all-nonempty-support RAW profile equality; (D) source/target full canonical finite B criterion by invoking #399 with (C). Run full Lean and strict named standard-only axiom report before merging.