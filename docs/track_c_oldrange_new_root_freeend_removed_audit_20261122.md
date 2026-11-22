# Track C — old-range E-free exceptions do not charge the later new root

22 November 2026. English proof and 20 hostile checks written before the Lean module.

## Theorem

Fix a genuine finite numerical-H+ physical ambient (A=finiteNumericH(L,k,M)), any normalized forbidden family, a finite original root pool (U\subseteq Fin M), a distinguished *new* physical original (w\in Fin M), and a true OLD dependent Kpt AlgorithmRun (R) on old literal Kpt seeds (X) of height (t=oldTop). Assume only that the canonical physical auxiliary E-free endpoint of the new root is not below t:
[
 t\le A.freeLevel(w).
]

Define the actual complete old-final-stage original pool with the new bare root adjoined:
[
 S= hStageOriginals(L,k,M,U\cup\{w\},R.I(0)).
]
Let
[
 F_{old}=\{ c<t:\ ∃v\in S\ (A.freeLevel(v)=c)\}.
]
Then
[
 |F_{old}|\le |U|+|SelectedOld(R)|.
]
There is **no +1 for the new root**, because its endpoint is outside the old scan range.

This holds in arbitrary normalized signature db,du,dd. No assumption about Q, graph symmetry, zero ordinary L, or the diary is required. It is an old-range *exception-count* theorem, not no-novelty by itself.

## Proof

Write (S_0=hStageOriginals(L,k,M,U,R.I0)), with **only inherited roots**. Every original in S is either in U, the new root w, or a genuinely positive physical original with numerical coordinate in the true selected R.I0. If a free endpoint (c<t) has an original representative v in S, then v cannot be w, since freeLevel(w)≥t. Thus v belongs to S₀. So there is an injection-free *inclusion*
[
  F_{old}\subseteq\{A.freeLevel(v):v\in S_0\}.
]
Taking cardinalities, the image has cardinal at most |S₀|. Verified Track E E86 proves |S₀|≤|U|+|SelectedOld(R)|: it counts at most one physical coordinate per selected old level, and preserves the full stage restriction. Compose the bounds.

Additionally, the old-range exceptional set is a subset of the numerical range 0,…,t-1 by definition; its complement for any c<t is exactly the complement of the complete, unfiltered physical endpoint set. Therefore the previously verified no-stage-E-free-end implication for real R applies without altering its assumptions.

## Hostile audit

1. F_old is *filtered below t*. It is wrong to subtract one blindly from an unfiltered |F| bound: the new root endpoint could coincide with another endpoint or itself be the only root.
2. Root w may already lie in U; the proof must work without assuming disjointness.
3. The endpoint freeLevel(w)≥t is the sole reason its contribution vanishes in F_old; w may still be a true source original.
4. One cannot conclude no source events at c from no physical original E free endpoint alone; genuine I2/old-upper L+/E matching remains separate.
5. The included final stage uses U∪{w} and genuine selected R.I0, not an assumed diary Plan.
6. Actual positive selected originals may be outside both U and {w}, so they must be retained in S₀.
7. Cardinal control of S₀ reuses the verified E86 theorem; do NOT identify S₀ with U.
8. The selected set counts inclusive oldTop if selected; this is harmless even though F_old is strictly below oldTop.
9. The proof uses set inclusion, not injectivity of physical E-freeLevel (false in general).
10. Do not assume that the later original w is a literal new initial seed in the old AlgorithmRun R.
11. R must be an actual AlgorithmRun: the final selected-level cardinal API and stage-tail inclusion are verified for genuine R, not arbitrary masks.
12. U is the inherited *physical original* pool; the total arbitrary numerical carrier M is not used in the upper bound.
13. Finset union makes sense even when U is empty or w duplicates an existing root.
14. The generic theorem does not need forbidden family avoidance; it only needs R to exist in the corresponding dependent Kpt successor tree, not an admissible numerical-H source representation.
15. No symmetry of ordinary L or auxiliary E is assumed for this counting statement.
16. All actual selected positive-stage originals remain in the same full numerical-H+ ambient A.
17. The numeric cut filter uses strict c<t; c=t would include the new root in the equality case.
18. This bound is not diary-uniform until |U| and |SelectedOld(R)| are controlled by a fixed diary.
19. To connect to the physical chronological new root, one must derive freeLevel(w)=newTop≥oldTop from the *old real top seed* and exact physical H+ chronology, as previously verified.
20. No assertion about a physically taller new run, common inverse-source monoid orbit, corrected B3, or big Ramsey degrees is made.
21. The old-range exceptional set must be the filtered image of the **same** complete physical original stage used in the source proof, not a selected graph-shadow stage.
22. Add positive Lean validation marks only after exact-head Lake build and qualified, standard-only axiom gate.

## Implementation

Define `KptPhysicalOldRangeStageFreeEnds` as a finite filter of `KptPhysicalFinalStageFreeEnds`, and prove `kpt_physical_oldrange_freeends_card_le_roots_add_selected` by a physical finite stage inclusion and E86. Add a membership equivalence `c∈F_old ↔ c<t ∧ c∈F_total`, to let later Track C conclusions use the exact filtered F at c<t. Finish with exact-head Lean CI.

Next: combine with the minimal bare-root original pool `W=cast(U)∪{w}` from Track C PR #485 after its validation, obtaining the optimal **|F_old|≤|U|+|SelectedOld|** for the constructed physical chronological extension, and carry conditional full odd no-novelty outside F_old. Exceptional cuts, old-prefix witnesses, and physically taller run orbit remain open.
