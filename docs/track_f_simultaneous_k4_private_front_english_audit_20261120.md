# Track F — simultaneous K4 compatible fronts with private fresh markers

20 November 2026. English proof and hostile audit written **before** Lean.

## Goal and normalization

For a finite family indexed by Fin(d), let u_i be genuine source Henson K4 one-types and v_i genuine target one-types. Let e be any injective induced embedding of the original directed ordinary-edge tables (NOT necessarily enumeration-preserving); assume the target satisfies the normalized K4 forbidden-family axiom. Suppose each pair is already singleton compatible:

    rank(v_i) = rank(u_i),
    A_i = sourceCodingFibre(Esrc,Etgt,e,v_i) is rank(u_i)-large above u_i.

Choose one target level L ≥ level(v_i) for all i. **The assertion to prove**: there are new target types t_i of EXACT level L and source types w_i at one COMMON source level M, such that u_i≤w_i, v_i≤t_i, rank(w_i)=rank(t_i)=rank(u_i), and A(t_i) remains rank(u_i)-large above w_i. Moreover the fresh positive-neighbour marker sets N(w_i)\N(u_i) are PAIRWISE DISJOINT even if roots u_i repeat or have different initial levels.

This is stronger than simply applying the already proved singleton continuation independently: independently selected source refinements can share new positive markers and change the mixed source graph-age.

## Proof

Proceed by induction on the finite set Q of already processed indices. Maintain source choices w_i and target choices t_i for i∈Q, with the compatibility properties above and pairwise-disjoint fresh marker sets. Values outside Q are irrelevant. Initially Q=∅ and no assertion is needed.

Suppose i∉Q. Choose an integer H at least level(u_i), and strictly larger than every level(w_j), j∈Q. Zero-pad the ORIGINAL source type u_i to level H, obtaining z_i=zeroPad(u_i,H). The complete old positive AND negative bits are unchanged, and rank(z_i)=rank(u_i). The abstract rank-largeness cone monotonicity theorem shows that A(v_i) is rank(u_i)-large above z_i; this uses the same original v_i and does NOT infer a new target fibre from thin air.

Apply the K4 exact-target-level compatible singleton continuation theorem (merged #321) to the pair (z_i,v_i), with target level L. Since rank(v_i)=rank(z_i), it provides w_i≥z_i and t_i≥v_i, t_i.level=L, rank(w_i)=rank(t_i)=rank(u_i), and the actual fibre A(t_i) remains rank(u_i)-large above w_i.

For each previously processed j, every fresh marker of w_j lies below level(w_j)<H (because both w_j and u_j are genuine finite types). Every fresh marker of w_i is at least H: below H, its positive bits equal those of z_i and hence of u_i, by the COMPLETE chronological extension z_i≤w_i. Therefore no fresh marker of w_i can coincide with any earlier fresh marker. This is exactly the previously Lean-verified `fresh_markers_disjoint_of_later_zeroPad` lemma used in private rank-zero descendants #358. Earlier choices w_j,t_j remain untouched. This completes the induction.

After processing all indices, let M be the maximum chosen source level, and zero-pad every chosen w_i to level M. Such padding preserves the exact positive-neighbour set, rank, the actual A(t_i) largeness by the same-rank cone monotonicity theorem, and pairwise marker disjointness. All t_i already have exact level L. This gives the desired simultaneous front.

## Consequence for the K4 synchronization lemma

If all original u_i have a common level m, then pairwise disjoint fresh marker sets imply the literal private-marker hypothesis of verified PR #400: a point x≥m in two refined positive-neighbour sets would lie in both fresh sets, because original neighbours have level<m. Thus every nonempty source raw support bound is preserved exactly (including triple supports).

Choose L BEFORE the induction greater than: all starting target levels; all images of original positive source neighbours; and, if source roots are pairwise distinct, all images e(a) for a<m. The latter is a single finite bound: L≥1+max{e(a):a<m}. There is NO need to bound images of the new markers chosen later.

The merged original/refined target sandwich #399 and canonical bridge #395/#400 now give equality of the COMPLETE finite sorted-graph classes (and complete all-support canonical K4 age acceptance tests) between original source front and the constructed target front. Distinct source roots remain distinguishable by an old source bit a<m; their new large source coding fibres contain genuine witnesses, and the verified target-bit separation lemma #325 forces t_i≠t_j once e(a)<L.

Thus the raw-graph-class component of the manuscript’s tuple synchronization lemma is provable, conditional on the EXISTING initial pairwise rank-compatible actual fibres. It is not necessary to transport separate old certificate cliques support by support.

## Hostile audit: mathematical boundaries

1. The singleton continuation theorem used is the **K4** exact-target-level theorem; the general K_ell version needs its own rank-equality input. We claim K4 only.
2. Target one-types v_i may start at distinct levels and may repeat. The single L is fixed in advance, with L≥all v_i levels. The proof NEVER changes L as new source markers appear.
3. A(v_i) is required to be genuinely rank-large above the original source u_i. It is NOT enough for v_i to have a nonempty abstract hypothetical source fibre.
4. Zero padding a source type at unchanged rank preserves largeness by the verified abstract Large.cone-mono lemma. This is essential: arbitrary same-rank refinements must also preserve source rank.
5. The source last-generation partial original index is NOT assumed to be monotone under e; no bound is placed on images of newly introduced source markers.
6. All fresh marker disjointness is relative to each coordinate’s OWN original u_i, not just a global old neighbourhood set.
7. Roots may be identical and labels may repeat. Choosing the next padded root beyond earlier chosen source levels still guarantees disjoint new markers.
8. The induction retains each previously selected target prefix and source refinement, never reuses a previous target fibre after changing its target type.
9. At final common source level M, padding changes neither old positive sets nor target type t_i. It only enlarges the source node domain with additional zero bits.
10. The marker disjointness proof uses actual source finite-type positive bits and COMPLETE old-bit equality on the zero-padded prefix, not mere inclusion of old sets.
11. The target rank equality is maintained at EXACT L, not just at some later level, using merged #321’s rank sandwich.
12. The existence of all finite source joint graph patterns uses verified all-ranks SOURCE richness; it is not a consequence of individual source cones intersecting.
13. For source profile equality, the ORIGINAL source roots must share level m and the final source types share M. The basic front theorem works without original common level; only the application imposes it.
14. The source/target raw numerical tables need not be equal. The verified source/target result identifies finite graph-class and full canonical test predicates instead.
15. Distinct target types require a source-bit separating witness for each distinct pair and target L beyond the image of that witness. This is automatic for distinct genuine types of common source level m, but the proof must spell out the use of genuine witness coding nodes.
16. Even if all target types are distinct, their LEXICOGRAPHIC order need not agree with source index order. The independent-history diary argument must use the actual target ordering, not silently identify the two.
17. The finite target tuple theorem does not by itself implement the cover, split and independent-code moves or prove full diary-history persistence.
18. It does not prove the global K4 big Ramsey lower bound, or any count of 24 level structures or independent triple diaries.
19. All Lean goals must use actual Henson one-types, inducedness on BOTH directed orientations, and the exact `sourceCodingFibre` definition.
20. No frozen manuscript black text is to be changed before the entire assembled theorem is checked. Existing TODOs may be updated when the exact-head compiler and standard-only axiom report are green.

## Lean plan

First formalize the finite-Q induction, private markers, exact common target L, and final common source M as one theorem. Reuse the verified #321 exact singleton and #283 `fresh_markers_disjoint_of_later_zeroPad` directly. Then add a thin corollary with common original source level m obtaining literal private-marker condition and all-support raw source profile equality from #400. Finally compose to a finite canonical graph-class theorem, and separately prove target-prefix distinctness using #325. The global diary statement must remain pending until those further stages are complete.