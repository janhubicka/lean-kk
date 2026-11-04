# English-first proof and adversarial audit: deactivation cannot increase old-graph clique capacity

**4 November 2026.** The English argument and hostile audit in this note are committed BEFORE the Lean source.

## Exact mathematical statement

For an arbitrary fixed directed Boolean original-edge graph E and finite positive unreserved candidates U and live reserved witnesses R, put

  Link_E(U,R) = {x in U : exists y in R with E(x,y)=1}.

Suppose U1 is a SUBSET of U0 and R1 is a SUBSET of R0. Then

  Link_E(U1,R1) ⊆ Link_E(U0,R0).

**English proof.** Every x linked in the new pool lies in U1 and has an actual witness y∈R1 with E(x,y)=1. The inclusions place x in U0 and y in R0 without changing E, so x was already linked in the old pool. This handles genuine reserved-witness deactivation and loss of positive unreserved passing bits. No symmetry, Henson density, order, or K-freeness is needed.

Write cap_E(P) for the maximal directed clique cardinality in finite P. A directed clique in a subset P' of P is also a clique in P; thus cap_E(P')≤cap_E(P). It follows that

  |R1| + cap_E(Link_E(U1,R1))
  ≤ |R0| + cap_E(Link_E(U0,R0)).

Consequently, whenever the old sufficient mixed-pool budget is <q, the new one is <q. The generic PR #54 proof then certifies that the *new* pool R1∪Link_E(U1,R1) has no q-clique. This is a real monotone transfer of a **sufficient** capacity budget; it does not infer an exact pool equivalence from the budget.

## Stronger complete-neighbourhood deletion transfer

Let C0 and C1 be arbitrary old and next proposed passing columns, with possibly different prefix lengths N0,N1. If the finite set of ALL positive neighbours below N1 is a subset of the old positive neighbours below N0, and the old complete q-clique checker is negative, then the next checker is also negative. The proof is immediate but important: any hypothetical next neighbour q-clique, including all old selected originals and auxiliary parameters, is literally an old neighbour q-clique by the inclusion. No reserved blocks are omitted and no cross-block nonedge hypotheses are needed for this direct transfer.

This provides a precise special case of a selected-event induction where a new event only erases positive old-original adjacency obligations; no new clique checking is necessary after the old complete certificate.

## Hostile audit

1. **Both inclusions are essential.** U may shrink while an old reserved witness activates: E(2,1)=1 and R0={0}, R1={1} can make a NEW link. Likewise, R may shrink while a NEW unreserved positive candidate enters. Never infer monotonicity from just one inclusion.
2. **E is fixed.** The argument is about one unmodified Henson original graph, not independently chosen finite edge tables before/after a retroactive edit. If E itself changes, the inclusions do not preserve links without extra edge monotonicity.
3. **No numeric tag-matching assumption.** To apply to real changing block identifiers, the old/new live reserved sets must be compared by an actual geometric source matching. The abstract subset hypotheses do not construct such a match.
4. **No ignored enumeration gaps.** The next positive-neighbour subset condition quantifies over the COMPLETE old-prefix/gap table, not only selected labels. If a skipped index becomes a positive neighbour, the condition may fail and the theorem cannot be used.
5. **Capacity monotonicity is not B3 monotonicity.** A corrected-(B3) continuation quantifies over possible future vertices and assigned upper L+ source types; ordinary old-edge clique capacities do not compare those types. The numerical-H K4 cut-10/22 counterexample still applies.
6. **A forbidden old candidate may become safe after deletion.** The converse fails: if the old checker is true and the next is false, that is perfectly possible. For K4 a triangle of three old neighbours causes a forbidden extension; turning off any one passing bit makes the next column safe. Hence there is NO iff of old and new negative certificates.
7. **The abstract inequality is insufficient for a global diary.** The proposed canonical recursive schedule may add positive neighbours, activate reserved vertices, or have different full source-node assignments; therefore its per-stage subset conditions remain to be proved case by case. This theorem only disposes of deletion-only events.
8. **The old sufficient budget is not necessary.** A pool can be q-clique-free even if |R|+cap_E(Link_E(U,R))≥q; the verified safe K4 mixed-pool counterexample remains valid. Do not use failure of the old budget as evidence that the new extension is forbidden.

## Formalization plan

- Prove a finite filter membership inclusion theorem Link_E(U1,R1)⊆Link_E(U0,R0) for U1⊆U0 and R1⊆R0.
- Prove the strict budget transfer by the existing Lean checked finiteDirectedCliqueCapacity_mono theorem.
- Prove a negative new-pool certificate from the old strict budget.
- Prove complete q-neighbourhood negative certificate transfer using inclusion of the ACTUAL oldNeighbourSet sets, allowing different prefix lengths and columns.
- Add a K4 deletion regression showing the asymmetry of negative certificates and a genuine monotone-safe old-link example.
- Include every public theorem endpoint in strict named transitive-axiom tests. Only after full Lean build + standard-only reports pass should olive manuscript prose receive source-exact green markers; keep black prose unchanged.

