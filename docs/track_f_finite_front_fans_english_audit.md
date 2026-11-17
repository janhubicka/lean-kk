# Track F — arbitrary finite-front rank-large daughter fans with all fresh markers disjoint

17 November 2026. English proof and adversarial audit committed BEFORE Lean. This is the finite-front source scheduling theorem suggested by the verified labelled-history fan extension [#322](https://github.com/janhubicka/lean-kk/pull/322). It is a geometric SOURCE-side combinatorial ingredient, not an assertion of complete mixed graph-age compatibility.

## Inputs

Fix actual graph table E and ell≥2. Let I=Fin d be an arbitrary FINITE set of active source sort labels. For EACH i∈I separately give: a consistent chronological Henson one-type root u_i of positive zero-based rank n_i+1, a set S_i of coding type nodes which is (n_i+1)-large above u_i, and an arbitrary finite target number k_i of lower-rank daughter cones. Ranks n_i, old roots and fibre sets S_i may DIFFER between i.

## Conclusion

For every sort i select a finite family F_i of exactly k_i descendants g≥u_i of rank n_i with S_i n_i-large above g. Within F_i the future cones are pairwise incompatible and their positive fresh marker sets `g.neighbours\u_i.neighbours` are pairwise disjoint. For ANY two distinct sorts i≠j, any g∈F_i and h∈F_j, the fresh positive marker sets are also DISJOINT. In particular no newly used old coordinate is positive for two distinct selected daughter sorts.

## Inductive proof

Induct on the finite SET Q⊆I of sorts already processed. Maintain a function F assigning a finite selected family to each i∈Q, with all internal and cross-sort requirements. For Q=empty choose all families empty.

When adding a fresh index i∉Q, build the LABELLED old finite history

    A = ⋃_{j∈Q} {(g,u_j):g∈F_j}.

Retain the root label u_j in each pair. This matters if the same finite type g is used under several old sorts with different roots; collapsing A to a set of bare nodes would lose marker obligations.

Apply verified `rank_large_new_fan_after_labelled_history` from PR #322 to the root u_i, rank n_i, S_i and target count k_i, using the labelled history A. It produces a new family F_i with its internal rank/largeness/incompatibility/marker requirements AND cross-disjointness with every old (g,u_j) pair. Update the choice function at i; all earlier F_j remain unchanged. The cross requirement holds in both orientations because `Finset.Disjoint` is symmetric.

Finite induction yields all F_i simultaneously. No time bound on the original roots is assumed: each new source root is zero-padded beyond ALL previous selected daughter levels before its own daughters are chosen. Its original positive and negative prefix remains exactly unchanged.

## Hostile audit

1. The induction MUST retain sort-index labels, not just a union of old type nodes: same old type may have different fresh marker sets relative to different old roots.
2. No assumption that all source roots have identical rank or the same fibre set. Source rank n_i and S_i vary independently.
3. The full recursive `Large` witness is kept for EACH daughter; merely selecting pairwise disjoint marker sets would be too weak for richness induction.
4. Pairwise incompatible future cones hold within a source fan. Cross-sort disjoint markers alone need not imply cross-sort cone incompatibility, nor is such incompatibility required here.
5. A selected daughter g is a genuine consistent hypothetical type; it need not itself be an actual coding original. If S_i is a set of actual coding nodes, its large cone later contains real coding originals.
6. A source with k_i=0 contributes no selected daughters, so all requirements remain vacuously valid; the finite induction should not assume k_i positive.
7. Different source roots may have overlapping OLD positive neighbours. The theorem only forbids overlap of newly introduced markers relative to their own roots, not overlap of original pre-existing old-neighbour sets.
8. This does NOT assert that selected actual coding originals from different cones realize prescribed binary edges or that the mixed common-neighbour graph-age constraints are feasible. It must be combined with verified physical clique-transfer and a further joint source/target fibre realization theorem.
9. No source-to-target induced embedding, diary history or BRD formula is assumed or proved here. Source-side fan selection and target-side compatibility are distinct tasks.

## Lean acceptance

Create a concrete finite request structure for each active sort, with explicit source root, rank n_i, fibre S_i, largeness certificate and requested k_i. Prove a finite-set induction with the labelled old-history A and verified #322 lemma. Expose an arbitrary finite FRONT theorem retaining all per-sort and cross-sort marker properties. Run targeted exact-head Lean and standard-only transitive-axiom gate. The manuscript's full tuple synchronization and exact independent BRDs stay pending.