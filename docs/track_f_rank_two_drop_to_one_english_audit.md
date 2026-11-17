# Track F — manuscript rank-three to rank-two compatible drop

17 November 2026. **English proof and hostile audit BEFORE Lean.**

## Rank convention and goal

The source Henson type tree has ZERO-BASED Lean rank: rank 0 corresponds to manuscript singleton rank 1; rank 1 to manuscript rank 2; rank 2 to manuscript rank 3.

The new theorem is the rank 2 → rank 1 actual compatible source–target drop. Let Esrc and Etgt be ordinary graph edge tables for the same ell≥2, Etgt avoid the normalized forbidden family, and e:Nat→Nat be injective and graph-induced (but not required to preserve original enumeration order).

Given any genuine source type u of Lean rank2 and any genuine target type v0 whose ACTUAL source coding-node fibre A(v0) is rank2-large above u, and any requested target cutoff B, construct actual source uH and target vH such that u≤uH, v0≤vH, level(vH)≥B, rank(uH)=rank(vH)=1, and A(vH) is rank1-large above uH.

**This does not require target v0's rank to equal the source root rank.** In the intended manuscript application it will, but the conditional theorem is more general.

## Short proof

By the DEFINITION of recursive rank2 largeness, applying A(v0)'s largeness to the source node u itself (a same-rank extension of itself) produces some descendant w≥u of Lean rank1 on which the SAME target fibre A(v0) is rank1-large.

Now invoke the independently verified actual rank1 SAME-RANK continuation theorem `sourceCodingFibre_continue_equal_rank_one` from merged PR #302, on target v0, source w and cutoff B. It returns vH≥v0, uH≥w, target level at least B, exact source and target ranks 1, and the new ACTUAL target coding fibre rank1-large above uH.

Transitivity gives u≤uH. No new clique marker or target rank certificate is needed: the lower-rank same-rank theorem already packages the actual edge-richness, target future-clique rank bound, and source-old clique transfer.

This proves rank-drop for manuscript rank3 from same-rank for manuscript rank2 without a circle: #302 depends on one-source rank2 edge-richness, not on this rank3 drop.

## Hostile checks

1. Invoke rank2 largeness on the root u itself with rank(u)=2; no unjustified assumption that every extension has rank2.
2. The rank1 descendant w is a hypothetical source TYPE, not necessarily an actual coding vertex; the rank1-large fibre over w, however, consists of ACTUAL coding-node extensions by definition.
3. Target prefix level of v0 is unrelated to source type w. The injected enumeration map e is not assumed monotone.
4. Target rank equality is obtained from #302 at source rank1, not assumed in the rank2 largeness step.
5. The root source/target ranks may differ in the abstract conditional statement; the theorem explicitly claims only the LOWER-RANK types match after construction.
6. Manuscript rank3 needs an actual source triangle for SAME-RANK continuation; that remains unproved. Rank3→rank2 drop is easier because rank2 same-rank continuation suffices.
7. This result is not graph-age profile synchronization: ONE source coding-node fibre and singleton rank only.
8. The lower big Ramsey degree theorem still needs every diary history to persist in arbitrary induced copies; no such assertion is used or proved.

## Lean implementation

Import merged rank1 equality, use recursive `Large rank _ 2 u` once to obtain w, apply `sourceCodingFibre_continue_equal_rank_one`, compose extension relations. Exact-head Lean build and standard-only named axiom audit. Frozen black manuscript prose and global BRD marks unchanged.
