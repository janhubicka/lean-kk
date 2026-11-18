# Track F — derive exact one-point K_ell safety from finite sorted clique feasibility

18 November 2026. **English proof and hostile audit committed BEFORE Lean.** This removes the explicit old-neighbour safety assumption from the rank-zero one-vertex density construction (#340) when the prescribed finite labelled gluing obeys the TRUE source raw support inequalities. It is the finite graph-theoretic invariant needed at each step of the unverified multi-sort richness induction.

## Actual old prefix and selected past

Fix ell≥2, an ACTUAL directed Boolean source edge table E, finite old prefix [0,m), finite set of sorts Fin d and genuine old positive-neighbour sets U_i⊆[0,m). Previously selected ACTUAL original vertices form a finite set P of indices ≥m. Each c∈P has assigned source sort σ(c)∈Fin d and has its actual forward old-prefix column fixed by that source sort: E(p,c)=1 iff p∈U_{σ(c)} for EVERY p<m. This equality is a consequence of IsCodingNode(c) and chronological source type extension, but we keep it as the exact finite invariant used here.

Choose the sort j of the NEXT future vertex. Let Q⊆P be exactly those earlier originals to which the next vertex must be adjacent (in BOTH orientations in the eventual coding-node realization). Its proposed old-neighbourhood is U_j∪Q.

## Source clique-vector feasibility assumption

For every genuine directed clique D⊆Q in the ACTUAL old graph E, let S_D={j}∪σ[D] be the nonempty support of the selected new vertex and its neighbouring previously selected clique D. Suppose

    1+|D| ≤ ell−1−cap_E({p<m : p∈U_i for every i∈S_D}).

This is exactly the true SOURCE raw sorted clique inequality for the new vertex together with D. It is implied by the assumed K_ell-free gluing of a prescribed sorted finite graph B to the old prefix, once the already selected original source vertices realize its corresponding induced subgraph with the stated old columns. We deliberately require the exact finite support condition here rather than assuming the entire richness induction.

## Genuine safety theorem

**Claim:** The proposed neighbourhood U_j∪Q contains NO directed clique of size ell−1. Equivalently, the exact old-neighbour `finitePoolCliqueCheck E (ell-1) (U_j∪Q)` is FALSE.

Suppose otherwise that T⊆U_j∪Q is an actual directed clique of size ell−1. Since U_j consists of OLD original indices <m and Q consists of NEW earlier coding originals ≥m, they are disjoint. Decompose T into C=T∩U_j and D=T∩Q, both directed cliques, disjoint, with |C|+|D|=ell−1. The new vertex is prescribed to see D, and D⊆Q.

For every p∈C and c∈D, the actual clique T gives E(p,c)=1. Since c∈P and its actual old column agrees with U_{σ(c)}, we have p∈U_{σ(c)}. Also p∈U_j. Therefore C lies in the TRUE old common-neighbour pool of the support S_D={j}∪σ[D], hence |C|≤cap_E(commonPool(S_D)).

But the displayed source feasibility inequality gives 1+|D|≤ell−1−cap_E(commonPool(S_D)). Together these yield

    ell = |C|+|D|+1 ≤ cap(commonPool(S_D))+|D|+1 ≤ ell−1,

a contradiction. Thus U_j∪Q is a genuine admissible Henson one-point old neighbourhood.

## Actual coding vertex corollary

Assume also that the source type u_j has old-neighbourhood U_j, level m and ZERO-BASED rank0; its source coding-node set A_j is rank0-LARGE/DENSE above u_j and consists only of actual coding nodes. Fix a source cutoff front beyond all P. The verified one-vertex lemma PR #340 applies to the now-proved safety certificate: there is an ACTUAL coding original x∈A_j after front, with exactly the prescribed bidirectional edges to P (true precisely on Q), and its source rank remains0.

**Thus the bottom-rank richness induction's next-vertex step follows from concrete old coding columns plus the true finite sorted clique inequalities, without an extra safety axiom.**

## Hostile checks

1. The old source neighbour sets U_i must be entirely below m; selected earlier original vertices in P must all be ≥m. Without this OLD/NEW disjointness, |T|=|C|+|D| is unjustified.
2. Every old-to-past adjacency E(p,c) used in the proof must be a TRUE graph bit, not an abstract type-label assertion. The hColumn premise records precisely this.
3. The old-to-past column is needed for ALL old p<m, not just the old neighbours U_j of the new vertex. Without that, p∈U_{σ(c)} cannot be deduced from E(p,c)=1.
4. The feasibility inequality is required for EVERY directed clique D⊆Q, not just D=Q. Q itself need not be a clique.
5. The support S_D always contains j and has distinct sort labels via a Finset image, even if several old coding vertices have the same sort.
6. The full B gluing feasibility is NOT assumed to follow from separately large fibres; that remains the geometric induction hypothesis to discharge.
7. The true old common-neighbour pool uses intersection of actual U_i and true maximum DIRECTED clique capacity, not the number of old neighbours or canonical age.
8. Graph symmetry is not implicitly assumed; the directed clique hypothesis and actual forward columns suffice for this safety proof. Actual future coding realization supplies both edge orientations through IsCodingNode.
9. The new candidate vertex is hypothetical during the safety calculation; the actual vertex is chosen only afterward using the verified dense coding-fibre theorem.
10. The construction remains conditional on rank0 density of its chosen fibre, not arbitrary positive-rank largeness. Higher ranks must be reduced by the verified finite daughter-fan induction.
11. The theorem concerns one step; the finite induction must maintain the old-prefix column property and induced B edges for every already chosen original.
12. No numerical diary BRD count or full multi-sort source/target synchronization is asserted.

## Lean acceptance

Prove the exact graph safety implication from the displayed all-subclique raw inequalities. Then compose it with merged PR #340 to obtain a genuine new coding original with all prescribed past adjacency bits under the joint finite clique-feasibility hypotheses. Require exact-head full Lean and strict named standard-only axiom gate. The full arbitrary finite B induction and global BRD lower theorem remain pending.