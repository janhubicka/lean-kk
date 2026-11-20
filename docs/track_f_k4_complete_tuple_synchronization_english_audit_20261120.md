# Track F — finish finite K4 tuple synchronization from genuine compatible fibres

20 November 2026. English proof and adversarial audit FIRST. The geometric private-target-front theorem is independently Lean verified in merged PR #403. Target old-bit separation is in PR #407 (dedicated build/axioms passed, full CI to be checked). Source private-marker raw profile preservation and original/refined source-target sandwich are merged #400/#399.

## Full statement

Let Es and Et be genuine source and normalized K4-free target ordinary graphs, and e:Nat→Nat injective induced on off-diagonal directed edges. Let u_i, i∈Fin(d), be pairwise DISTICT genuine source Henson one-types at one old level m, and let v_i be assigned genuine target one-types (not necessarily common-level nor distinct). Assume each pair is actually compatible:

   rank(v_i)=rank(u_i), and sourceCodingFibre(Et,e,v_i) is rank(u_i)-large above u_i.

For ANY target cutoff K, construct H≥K, M, new source types w_i all at source level M and target types t_i all at target level EXACT H such that:

1. w_i≥u_i, t_i≥v_i; source and target singleton ranks remain the original ranks, and the ACTUAL target fibre at t_i is rank-large above w_i.
2. w_i have pairwise-private fresh positive-neighbour markers relative to u_i; the full RAW source clique bounds on EVERY nonempty sort support are unchanged, including three-way supports.
3. t_i are pairwise distinct, without assuming the original v_i are distinct.
4. For EVERY finite symmetric K4-free abstract B on [0,N), every possibly repeated sort labelling σ:Nat→Fin(d), the complete source canonical integer-clique feasibility test (all cliques/all nonempty supports) is logically equivalent to the corresponding complete target test. Thus the complete finite sorted graph extension classes agree.

The target cutoff H can be chosen before any source refinement and need only exceed (a) all original target levels and (b) e([0,m)), not the target images of the fresh source markers chosen later.

## Proof

**Choose H.** Take H=max(K,sup_i(level(v_i)),1+sup_{a<m} e(a)). All terms are finite. Then H≥K and H≥every initial target level; every original source a<m has e(a)<H. No enumeration-order monotonicity is used.

**Construct the simultaneous compatible front.** Apply the verified K4 theorem `k4_private_exact_target_common_source_front` (#403) with this H. It gives w_i at a common source level M and t_i at EXACT H, preserving each rank and actual fibre largeness, with disjoint fresh sets N(w_i)\N(u_i).

**Preserve source entire raw profile.** Every old neighbour of u_i lies below m. Hence an x≥m in two final positive-neighbour sets would belong to both fresh sets, contradicting the verified pairwise disjointness. Thus the literal private-marker premise of `trackFCommonRawAge_eq_of_same_rank_private_markers` (#400) holds. Equal singleton ranks come from #403, as does full chronological old→new bit agreement. Therefore all raw source ages are preserved on every nonempty support, including all triple supports.

**Force distinct target types.** Since u_i are distinct true types sharing the same level m, every distinct i,j has an old source coordinate a<m at which their complete bits differ (PR #407, proved from field extensionality). Each rank-large A(t_i) has an ACTUAL source coding witness x_i extending w_i and thus u_i. The induced embedding sends the different source old bits at a to different target edges from e(a). But e(a)<H, so equal t_i and t_j would prescribe the same target old bit, contradiction. This is the independent verified `target_finite_family_injective_of_distinct_source_roots` application.

**Identify complete finite graph classes.** Take arbitrary finite symmetric K4-free B and labels σ. The literal source-profile equality above discharges the separate hRawSame hypothesis in the verified original/refined two-root age sandwich #399. It uses actual large refined fibres for the source→target direction (#380), and images of ONLY ORIGINAL old positive neighbours below H for target→old-source. Consequently exact-support finite-clique feasibility is equivalent between the original source u_i and target t_i. The verified exact↔full-support bridge and normalized integer canonicalizer #395/#400 then identify the complete canonical all-support constraints on every B-clique. This is equality of finite labelled sorted graph classes, NOT pointwise equality of redundant raw numeric bounds.

All conclusions hold simultaneously for every finite N, B, σ because w_i,t_i were chosen independently of B. Therefore this is a genuine finite-tuple synchronization lemma, rather than a conditional assertion about each separately chosen B.

## Adversarial audit

1. **Initial compatibility is essential.** We do not infer initial target fibre largeness for arbitrary target types; the root/root case is a separately checked starting configuration.
2. **Source roots are genuinely distinct** at the same old level m; otherwise target injectivity cannot follow from source old-bit separation.
3. **Target initial types may coincide or have different levels.** Only the new types are forced distinct at the same chosen H.
4. **K4 only.** Exact prescribed target level AND exact singleton rank are provided by #321 for K4. Do not state a general K_ell tuple theorem without a general singleton analogue.
5. **All source original neighbours** are below m by the source one-type validity field; this is used to turn fresh-set disjointness into the literal private-marker criterion of #400.
6. **Only original images must be below H.** Fresh marker images can be arbitrarily late under the nonmonotone induced embedding e. This avoids the former cutoff circularity.
7. **Genuine ACTUAL coding nodes**, not hypothetical source types, witness target old-bit separation and clique feasibility.
8. **The output common source level M may be beyond the entire target H in source numerical order.** There is no relationship or monotonicity requirement between M, H, or e.
9. **Source raw-profile equality** is literal on ALL nonempty sort supports, not just singleton/pair projections; this also handles a three-way support.
10. **Target RAW numeric equality is NOT concluded.** Equal complete finite extension classes do not force equality of every redundant target raw bound.
11. **Target canonical feasible test equality** is a predicate over all cliques and all admissible supports, not merely the exact-support inequality from PR #383.
12. **The K4-free condition on B** is separate from the actual target Henson avoidance condition and needed to normalize the bounded integer witness.
13. **No injectivity of σ.** Repeated abstract vertices of one sort are permitted; the all-ranks source richness theorem handles them.
14. **No source/target label-order coincidence.** New target types can have a different lexicographic order from source types. The actual diary argument must use the target order when recording splits.
15. **No full L+/E history transfer.** This theorem concerns ordinary graph-age data and actual coding-node fibres; Kpt auxiliary parameter-closed B3 histories remain independent.
16. **No claim every abstract diary is unavoidable.** The cover/split/code schedule and persistence must be constructed using these synchronized front steps.
17. **No global BRD lower bound** or 24-case diary count is derived by this lemma alone.
18. **No frozen black text edits.** Promote the synchronization validation marker only if the complete four-conclusion theorem passes exact-head full Lean and strict standard-axiom checks.

## Lean acceptance

One main theorem returns H,M,w,t, the compatible rank/large-fibre front, private markers, target type injectivity, literal all-support source raw equality, and a universally quantified finite symmetric K4-free B canonical-age test equivalence. Its proof should be a short explicit composition of #403, #407, #400 and #399, without introducing a new geometric axiom.