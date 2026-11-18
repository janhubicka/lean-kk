# Track F — derive local one-point safety from a global finite labelled graph

18 November 2026. English proof and hostile audit **before Lean**. This directly connects the newly merged physical one-point safety theorem (#345) to the global source sorted clique feasibility hypothesis for a prescribed labelled finite graph B. It does not invoke published diary degree counts.

## Finite data

Let E be the actual old source ordinary graph. Let n be the number of **already selected** vertices and B:Nat×Nat→Bool the adjacency of the desired finite graph on abstract indices 0,...,n. The new vertex has abstract index n and source sort j=σ(n), where σ:Nat→Fin d is the sort labelling.

The actual already selected source original vertex at abstract index i<n is f(i)∈Nat. Assume:
- f is injective on [0,n) (it need not be globally injective);
- for all distinct i,k<n, E(f i,f k)=B(i,k), in both ordered directions;
- actual old-column sort(f i)=σ(i);
- B(i,n)=B(n,i) for every i<n (the prescribed graph is symmetric at the new vertex).

Define actual previously chosen originals P=f[[0,n)) and the positive old originals Q={f(i):i<n and B(i,n)=1}. The partial embedding gives the actual directed edges among members of P. Q need not itself be a clique.

Assume B has the **global old-source sorted raw clique feasibility property**: for each nonempty directed clique T⊆[0,n+1), the cardinality |T| is at most the actual source raw age

    ell-1-cap_E({p<m : every sort in σ[T] has p as positive old neighbour})

on the support σ[T]. This is exactly the finite labelled clique-vector condition for the prescribed B.

## Claim: every local positive clique satisfies the one-point inequality

Take ANY actual directed clique D⊆Q in E. Form its abstract preimage

    A={i<n: B(i,n)=1 and f(i)∈D}.

The image of A under f is EXACTLY D, because D⊆Q. Since f is injective on [0,n), |A|=|D|. Because f is induced on the already selected vertices, A is a directed clique of B. By the prescribed symmetry of B at n and positivity B(i,n)=1 for i∈A, the set T=A∪{n} is a directed clique of B, of size |D|+1.

Its sorted support is exactly σ[T]={σ(n)}∪sort[D] (sort maps ACTUAL selected originals to their source sort). The global B feasibility inequality for T therefore is

    |D|+1 ≤ trackFCommonRawAge(d,ell,m,E,U, {σ(n)}∪sort[D]).

This is precisely the local hypothesis of the **now-verified physical graph-safety lemma #345** for the next sorted source vertex. Thus no extra local clique-age assumption is needed: all local bounds follow from ONE global finite graph B feasibility predicate.

## Genuine old-neighbour safety corollary

Assume additionally each source root old-neighbour set U_i lies below m, all actually selected originals f(i) occur at indices≥m, and their complete forward old column is exactly U_(σ i) on every p<m. Apply the verified #345 one-point safety theorem with past=P, positive=Q, next sort j=σ(n). The result is:

    finitePoolCliqueCheck E (ell-1) (U_j ∪ Q) = false.

If the designated rank-zero source coding fibre S_j is dense, consists of actual coding nodes, and the future source cutoff lies beyond all P, the verified second #345 theorem gives a GENUINE later coding vertex x∈S_j with exact two-directed E edges to every old selected vertex in P according to B(i,n).

The remaining construction is the finite iteration: carry the partial embedding f and old-column invariant through each step, prove all selected old E edges match B, and verify the appropriate rank-zero dense fibres remain available. This note does not assume that induction is complete.

## Hostile checks

1. **Actual versus abstract cliques:** D is a clique among the chosen source ORIGINALS, while A is a clique in the prescribed finite B. The induced partial embedding hypothesis is essential to infer the latter.
2. **Symmetry at the newly selected vertex:** B(i,n)=1 gives the edge i→n, but we also need n→i to obtain the full directed clique T. Explicitly assume symmetry at n.
3. **Local injectivity:** |A|=|D| follows from f injective on the chosen initial segment. The map need not be defined injectively outside [0,n).
4. **Full sorted support:** when σ identifies two daughter labels, σ[T] is still a FINSET of sorts, so equality of support sets does not require sort injectivity.
5. **All clique subpatterns:** it is not enough to apply global B feasibility just to {n}∪all positive old vertices. The latter might not form a clique. Quantify over every actual clique D⊆Q.
6. **Old/selected separation:** the physical #345 lemma requires old U_i below m and selected actual originals at least m; otherwise the decomposition of a putative K_(ell-1) has overlapping old and past vertices.
7. **Old actual edge columns:** each previously selected coding original must have its exact old E column U_(σ i), not merely be labelled σ i by convention.
8. **No target embedding hypothesis:** the statement is about SOURCE graph construction. Target source-fibre compatibility is separate and must already have been arranged to provide the dense S_i.
9. **Raw versus canonical:** apply the true raw clique bounds of B; canonical equivalent feasible vectors may be used through the verified canonicalizer but NUMERICAL mixed raw values need not be unchanged.
10. **Density after finite commitments:** rank-zero density is preserved on any chronological descendant, but only once each new one-point old-neighbour pool is certified safe by this lemma.
11. **No invented literal coding node:** the next point is chosen via the verified density of ACTUAL coding nodes, not by assuming all hypothetical finite Henson types are realized by vertices.
12. **No global BRD claim:** arbitrary-rank multi-sort richness and persistence of each diary remain unproved by this one-step bridge alone.

## Lean acceptance

Prove (a) local feasibility for any actual clique D⊆Q from global B sorted raw clique feasibility, using finite image/preimage, and (b) its composition with the exact #345 old-neighbour safety theorem. Use source-level induced edge agreement and actual old columns as hypotheses, with no new axioms. Exact-head Lean build and transitive standard-only axiom gate. Keep manuscript black text untouched and global pending marks unchanged.