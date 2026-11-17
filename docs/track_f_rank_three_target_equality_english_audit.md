# Track F — exact manuscript rank-three source/target rank matching, dependency plan

17 November 2026. English proof and adversarial dependency audit BEFORE attempting Lean. This note does NOT claim its two new Lean dependencies are verified yet.

## Dependencies under exact-head review

1. Source triangle-richness draft [#307](https://github.com/janhubicka/lean-kk/pull/307): for a source Henson one-type of zero-based Lean rank2, any rank2-Large set of ACTUAL coding nodes contains 3 genuine original vertices x<y<z forming a directed K3. The proof depends on ordered fresh-marker choices and the exact positive-insertion clique capacity recurrence. Do not use this as a verified input before its dedicated triangle gate passes.
2. Finite source-fibre clique-to-target-rank draft [#310](https://github.com/janhubicka/lean-kk/pull/310): if a genuine source clique C lies in the exact actual source coding-node target fibre of v under an injective INDUCED e, the target image e[C] is a genuine future clique completely joined to v.neighbours, and |C|≤finiteHensonTypeRank(v). Its exact-head gate is also pending.
3. Already VERIFIED and merged [#299](https://github.com/janhubicka/lean-kk/pull/299): from an initially rank2-Large exact fibre at source u and target v0, for every target bound B construct target vH extending v0 and source uH extending u with rank(uH)=rank(u)=2, fibre(vH) rank2-Large above uH and rank(vH)≤2.

## Result once the dependencies are Lean-certified

Under normalized target Henson avoidance and an arbitrary injective INDUCED source-to-target graph embedding e (NOT assumed order-preserving), every nonroot compatible source fibre of zero-based rank2 can be refined beyond any target cutoff B while preserving exact source and target rank2 and actual rank2 largeness.

Apply #299 to obtain uH,vH as above. By #307, there are 3 actual source coding nodes x,y,z in the new exact sourceCodingFibre(vH), forming a genuine K3. Let C={x.level,y.level,z.level}. Since x<y<z, |C|=3. Each source original in C has an ACTUAL coding-node fibre witness and e carries C to a target future K3 fully joined to vH.neighbours. By #310, 3≤manuscript target rank(vH), i.e. zero-based Lean rank(vH)≥2. With target rank(vH)≤2 from #299, conclude rank(vH)=2.

Thus manuscript singleton rank THREE same-rank continuation would be proved, complementing already verified rank1 and rank2 same-rank continuation, and the rank2→rank1 and rank3→rank2 drop theorems. For K4 Henson graphs, singleton ranks are only 1,2,3, so this would complete the SINGLE-SOURCE rank-match/transport mechanism at every possible singleton rank, under the explicit target and source hypotheses of the verified theorems.

## Hostile checks

1. Use source code vertices actually in the selected **new** target fibre (not in the old target fibre only). #307 applies to exactly this rank2-Large set.
2. The vertex *set* C of original source indices has cardinality 3 because x.level<y.level<z.level; hypothetical type nodes themselves cannot be used as target original clique elements.
3. e is injective and edge-induced, not order preserving; target image vertices may appear in any order, but all are beyond vH.level by exact sourceCodingFibre membership.
4. The old target neighbourhood is completely joined to the image triangle in BOTH orientations, because the fibre predicate retains both old columns.
5. The finite target rank bound is in manuscript one-based units; subtracting 1 to obtain zero-based Lean target rank requires exact valid K_(ell-1)-free target one-type safety.
6. The selected source type uH is hypothetical, whereas the clique witnesses are ACTUAL source coding nodes; this distinction is maintained in #307.
7. Full source-to-target TUPLE profile synchronization remains unproved even after singleton ranks match; no global lower big Ramsey degree or diary bijection follows immediately.
8. The underlying Henson source coding-node density upstream may depend on OnePointLeftDense; the conditional transport theorem itself assumes the rank-large actual fibre rather than asserting every arbitrary enumeration has it.

## Formalization next

Once #307 and #310 pass their exact-head named gates and merge, import them into a new rank2 same-rank target continuation module. Build the actual Finset Nat {x.level,y.level,z.level}, prove the three source-edge directions and `IsDirectedCliqueOn`, establish actual fibre witnesses for each index, invoke #310 and #299, and audit the final theorem under standard Lean axioms only. Keep black manuscript prose frozen and full multi-sort BRD lower bound pending.

**17 November acceptance update:** Full Lean and strict standard-only named axiom gates of #307 (actual rank3 triangle in any rank2-Large ACTUAL coding-node set) and #310 (all-size actual coding-fibre clique to target rank) have PASSED, and both PRs have merged to `lean-kk/main`. The following Lean file will now prove the promised singleton same-rank continuation at zero-based source/target rank2, by composition with already verified #299. All source and target types remain the exact actual finite Henson one-type structures; complete multi-sort graph-age synchronization and global BRDs are still pending.
