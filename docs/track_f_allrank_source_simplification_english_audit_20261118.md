# Track F — reuse the verified private raw-age bridge in the all-ranks source-richness proof

18 November 2026. English-first simplification and adversarial audit.

## Why replace the proof, but not the theorem

Merged [PR #367](https://github.com/janhubicka/lean-kk/pull/367) already proves **in Lean** that every finite graph satisfying all genuine source raw clique inequalities can be realized by original coding nodes in arbitrary-rank large Henson source fibres. Its exact-head one-theorem build and standard-axiom gate passed. Its proof includes a long independent derivation of the new positive-marker location, disjointness, common-neighbour collapse, singleton safety and all-support raw equality.

The independently checked [PR #364](https://github.com/janhubicka/lean-kk/pull/364) proves all those geometric facts in one reusable theorem, \`trackFPrivate_rank_zero_raw_transfer\`, from verified private rank-zero descendants [PR #358](https://github.com/janhubicka/lean-kk/pull/358). Therefore the geometric calculation in #367 is duplicated.

**Proposed edit:** Retain the exact public theorem declaration \`trackFAllRanks_realizes_all_feasible_sorted_source_graph\` and all its existing hypotheses and conclusions byte-for-byte. Rewrite only its proof, using the now-merged #364 bridge. There is no change to the manuscript's frozen black prose or to any global BRD marker.

## English proof

Fix the original finite source roots \(u_i\) at common level \(m\), coding sets \(S_i\) that are recursively large at their actual ranks, and finite prescribed graph \(B\) of \(N\) vertices with original sort map \(\sigma\). As in the existing proof, take \(\mathrm{Fin}(N+1)\) **private** sort indices. Map \(a\mapsto \pi(a)=\sigma(a)\), and choose \(\tau:\mathbb N\to\mathrm{Fin}(N+1)\) injective on \([0,N)\), so \(\pi\circ\tau=\sigma\) there. The extra dummy private index ensures the empty requested graph poses no type-level problem.

Apply \`trackFPrivate_rank_zero_raw_transfer\` to the roots \(u_{\pi(a)}\) and actual coding fibres \(S_{\pi(a)}\). It gives a common later level \(H\), genuine rank-zero private roots \(g_a\), and four exact certificates: their level is \(H\); each extends its original root and retains rank-zero largeness of the **same** coding set; every singleton private raw age is positive; every support \(Q\) of at least two private sorts has exactly the original parent-image *raw* age. The lemma already deals with noninjective \(\pi\), different original ranks, repeated original roots, all true old positive and negative bits, and fresh marker disjointness. There is no need to rebuild any of these calculations in the application.

Use verified finite graph transfer \`trackFPrivateSort_all_cliques_feasible\` from [PR #362](https://github.com/janhubicka/lean-kk/pull/362). Its hypotheses are precisely \(\tau\)'s injection on the requested vertices, \(\pi\tau=\sigma\), the positive singleton age, exact mixed raw equality, and the original clique inequalities. It gives all clique inequalities for \(B\) in the rank-zero private front. This correctly handles a two-private-sort clique whose parent support has only one sort.

The verified actual rank-zero finite realization theorem \`trackFRankZero_realizes_all_feasible_sorted_graph\` from [PR #355](https://github.com/janhubicka/lean-kk/pull/355) then selects strictly increasing **original source coding vertices** \(f(i)\in S_{\pi\tau(i)}=S_{\sigma(i)}\) inducing every directed edge and nonedge of \(B\). Its complete old-column conclusion holds below \(H\). Since \(m\le H\) and \(u_{\pi\tau(i)}\le g_{\tau(i)}\) is *complete prefix* extension, restriction to the original \(m\) yields precisely the old positive and negative source bits of \(u_{\sigma(i)}\). All five conclusions of the original theorem are unchanged.

## Adversarial equivalence checks

1. **Exact statement retained:** name, quantifier order, source model, actual coding requirement, full original column and induced-graph conclusion are unchanged; there is no new assumption.
2. **Private labels may share a parent.** The raw mixed-support equality is indexed by distinct private sorts and does **not** require \(\pi\) injective.
3. **Dummy sort for \(N=0\):** \(\mathrm{Fin}(N+1)\) is inhabited; the private-label injection and finite B inequalities are vacuous on an empty graph.
4. **Singleton raw age only:** canonicalized mixed ages can differ, so apply the exact RAW theorem and the verified all-clique feasibility transfer instead of numerical canonical equality.
5. **Coding membership:** the rank-zero daughter carries the SAME original \(S_{\pi(i)}\), not a newly postulated dense set.
6. **Chronology:** the target embedding need not preserve enumeration order; this source lemma asserts only increasing *selected source originals*, exactly as its original statement did.
7. **Non-root compatibility:** no source-to-target profile synchronization, diary-event persistence or global BRD result is inferred.
8. **Axiom check:** the rebuilt exact original theorem must be checked against only \`propext\`, \`Classical.choice\` and \`Quot.sound\`, independently of having been accepted under its old proof.

## Expected practical benefit

The proof is shorter, its geometry is separately reusable, and the single responsibility of the all-ranks theorem becomes composing three previously verified interfaces (#364, #362, #355). This also removes a misleading potential dead end: if the marker algorithm changes, the age-transfer theorem is the only point requiring repair.