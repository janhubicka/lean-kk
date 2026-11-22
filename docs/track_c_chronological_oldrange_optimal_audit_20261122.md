# Track C: optimal chronological old-range E-free exception support

22 November 2026. English-first proof and adversarial audit. The proposed combined Lean theorem depends on the independently checked PR #485 (minimal bare original pool) and PR #489 (old-range filtering).

## Mathematical statement

Let A=finiteNumericH(K,k,N), B=finiteNumericH(L,k,M) satisfy the complete two-model physical old-block agreement, forbidden-family avoidance and chronological new-root hypotheses already used by Track C. Let U be a FINITE set of OLD physical originals whose full dependent Kpt prefix pool contains every actual old initial seed X. Assume a true physically exhaustive old normalized Kpt AlgorithmRun R on X, of height t, with an actual top seed.

Let w=hPosition(k,j,k) be the ONE true newly inserted B-original, with physical E free level T=hPosition(k,j-1,k)+1>=t. Put U'=Fin.castLE[U], W=U' union {w}, and Y=X union {O_w}. Let F be the set of complete stage-original free endpoints STRICTLY BELOW t:

    F = { c<t : exists v in hStageOriginals(L,k,M,W,R.I(0)),
                 B.freeLevel(v)=c }.

Then (a) Y is represented by the full dependent Kpt original-prefix pool over W, (b) |W|<=|U|+1, (c) |F|<=|U|+|SelectedOld(R)| with NO extra +1 and NO padded carrier M, and (d) every actual old-unselected ODD cut c<t outside F is fully candidate new-root no-novelty provided complete OLD Kpt prefix witnesses exist for all active source originals at c. The no-novelty conclusion includes I1 and same-node full old/upper L+/E crossing comparisons.

The theorem does NOT assert the required OLD prefix witnesses exist in the resolved diary, or quietness at exceptional/free-end or nonzero real cuts, or synchronization with the physically taller new run.

## English proof

The verified full old-original transport theorem carries X from A to the B-prefix pool of U', with negative ordinary L and directed auxiliary E intact. Adjoin the physical original O_w itself. This proves coverage by W=U' union {w} and |W|<=|U|+1.

The actual old top seed and chronological numerical construction imply t<=T=B.freeLevel(w). Apply PR #489's general old-range physical free-end theorem to root U', extra original w and actual old R. It bounds the complete filtered endpoint image by |U'|+|SelectedOld(R)|<=|U|+|SelectedOld(R)|, without assuming disjointness or E-free-level injectivity.

For c<t, c absent from filtered F means c absent from the entire final-stage E-free endpoint image. Verified actual-run selected-tail inclusion excludes all current-stage original free ends at c. Old-unselected c is old-boring by AlgorithmRun.interesting_step; exact chronology excludes a new-root terminal at c. With the separately supplied complete OLD Kpt prefix matches, apply finiteNumericH_old_boring_one_bare_odd_noNovelty_general to the SAME old R, W, Y and cut c.

## Hostile audit before Lean

1. U is a finite physical root-original set, not a graph shadow.
2. Literal X must lie in the full dependent old prefix pool over U.
3. K/L agree in all old ordinary binary, unary and diagonal fields, and the physical E encoding is preserved.
4. Both actual numerical-H+ finite ambient structures avoid the normalized forbidden family.
5. Bare Y has exactly ONE new root original; no closure or ancestor family is silently inserted.
6. Old U and new w live in distinct carriers until U is cast by Fin.castLE.
7. W is exactly U' union {w}; using the older larger existential physical pool can defeat the sharp bound.
8. The genuine stage may add selected dependent original parameters outside W.
9. The image U' has cardinal at most |U|, including the case of empty U.
10. w may overlap U'; use inequalities, not a false disjoint union.
11. F is the filtered image of the complete FINAL actual stage, not a selected-front age.
12. Old-range is STRICT c<t; using c<=t would allow w when T=t.
13. The old actual top seed, not a formal top marker, supplies t<=T.
14. Every genuinely selected old level, including t, is counted in SelectedOld(R).
15. Long gaps between selected levels do not affect the count.
16. E-free levels may coincide; cardinal images never require injectivity.
17. The filtered F uses the SAME R and W as the full no-novelty theorem.
18. For c<t, nonmembership in F is equivalent to nonmembership in the full final endpoint set.
19. True selected-tail monotonicity is essential for transporting final no-free-end to each old pre-cut stage.
20. Old-unselected means genuinely old-boring only by the AlgorithmRun recurrence, not by a proposed diary.
21. The new root free endpoint T is outside all c<t, so it has no terminal there.
22. Complete old Kpt source-prefix matching is STILL an explicit hypothesis at each active original; finite counting alone cannot prove it.
23. Odd no-novelty needs full directed E and negative ordinary L, not just zero ordinary graph column.
24. Exceptional odd E cuts, positive real L cuts, and K4 auxiliary q2/E events are NOT resolved.
25. A cut in F may still be harmless; F is a sufficient superset of potentially active endpoints, not an exact Bad-cut set.
26. This comparison is within one physical old run and one new bare seed, not across arbitrary diary occurrences.
27. New physically taller runs have other selected-level masks and need separate analysis.
28. Diary-uniform BRDs and the 24-orbit theorem require control of |U| and selected old event count from the abstract diary, and a common labelled inverse-source orbit.

## Lean implementation plan

After PRs #485 and #489 have passing exact-head CI and are integrated, prove the concrete full prefix cover for W=U'.image union {w} (either expose the exact W in the first small-root theorem or derive from verified old seed-pool lift). Define F using KptPhysicalOldRangeStageFreeEnds with U' and w. Use the generic old-range lemma and Finset.card_image_le for the bound. Derive no-stage-end outside F via the exact filtered membership iff, the true old run tail, and chronological new-root freeLevel equality. Finally apply the existing complete dependent odd no-novelty theorem. Register all qualified axiom reports; do not edit frozen black manuscript text.
