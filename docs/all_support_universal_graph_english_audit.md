# All-support universal finite clique gadget — proof and adversarial audit

**13 November 2026. English FIRST.** This is the exact finite ordinary-L graph-age realization combining every support constraint simultaneously. The proof depends on the single-reserved-block construction in draft PR #93 and on the verified universal finite future W_B. It is NOT a proof that the completed gadget already sits in the specified full Henson H+ parameter-closed source.

## Statement

Fix ell>0, finite labelled sorts Fin d and **arbitrary raw** bounds B on all admissible nonempty supports T. Let V_B be the feasible normalized integer clique vectors respecting **every** bound; W_B is the one finite future which realizes exactly V_B, by verified PRs #86/#88.

Construct an actual finite Boolean ordinary-L graph with a reserved base:

\[
R_B=\coprod_{T\in \operatorname{IntegerGraphSupport}(d,\ell)}
 \operatorname{Fin}(\ell-1-B(T)),\qquad
V=R_B\amalg W_B.
\]

Every individual reserved block R_T is a complete irreflexive clique. All edges between different reserved blocks are **absent in both directions**. Future-future edges are exactly the universal graph edge of W_B, so a future clique stays within one feasible component C_w. For reserved q∈R_T and future v of sort j, define **both** directed L bits to be 1 exactly when j∈T. No additional vertices or edges are present in the finite carrier (the ambient dependent-sum type may include infeasible coordinates, but the designated finite set does not).

**Theorem 1 — exact K_ell-freeness.** Every directed clique in this actual finite graph has cardinality strictly below ell.

**Theorem 2 — exact L-only future profile.** The cliques contained **in the future part W_B** have normalized sort-count vectors exactly V_B, not merely a subset. The reserved blocks do not affect those internal future edges. Consequently their maximum T-support sizes are the actual canonical values G_B(T), for every T.

**Theorem 3 — sharp blocked vectors.** Suppose a normalized vector w violates B(T) for some support T. If a new full clique component with exactly w_j sort-j vertices is attached with all the same support columns, then its T-sorted vertices together with R_T contain a clique of size at least ell. Thus the reserved blocks *exactly* encode the raw constraints against complete normalized future clique components.

## Proof of K_ell-freeness

Let s be any clique of the entire constructed finite carrier.

- If s contains no reserved vertex, s is a clique in W_B and has size <ell by PR #86.
- Otherwise choose reserved q∈R_T. **Every other reserved vertex in s belongs to the same T-block**, because different reserved blocks have no L edge. Every future vertex in s has sort in T, because it must be adjacent to q. Thus its future part s_W is a clique in W_B with |s_W|<ell and |(s_W)_T|=|s_W|≤B(T). The reserved part has ≤r_T:=ell−1−B(T) vertices. The verified sharp arithmetic lemma from merged PR #89 gives r_T+|s_W|<ell, including the saturated subtraction case. Hence |s|<ell.

This proof is independent of the number of supports and even works with duplicate raw ages; supports are tagged and different tagged blocks have no edges.

For sharp blocked vectors w, violation w(T)>B(T) together with w(T)≤ell−1 implies B(T)<ell−1. Hence r_T>0, and (ell−1−B(T))+w(T)≥ell. Since the complete w-component has all sorts in T adjacent to R_T and those T-vertices mutually adjacent, there is a directed K_ell inside their union. It is essential that the violating w-component is *hypothetically added*; it cannot already lie in the feasible W_B.

## Adversarial audit

1. **Arbitrary B and truncated subtraction:** if B(T)≥ell−1, the T-reserved block has size zero. No false cancellation identity is used.
2. **ell=1:** no admissible supports exist, so the reserved base is empty and the future is empty; the K_1-free statement is vacuously correct. ell=0 must be excluded.
3. **Two different blocks:** reserved-reserved atoms between T≠U must be **false**, otherwise their union may create a forbidden clique despite every individual T-budget being safe.
4. **Repeated sorts:** distinct future clique vertices of the same sort are counted individually via the Sigma slot coordinates.
5. **No full W_B cardinality shortcut:** W_B may be huge and contain many nonadjacent components; only actual clique subsets matter.
6. **Selected support of a clique with reserved vertices:** if s meets R_T, every future vertex in s must have sort in T; that is an exact Boolean implication from the mixed L edge, not from age monotonicity.
7. **All support constraints simultaneously:** a component C_w is included in W_B iff w obeys **all** B(U). The construction does not only satisfy the T-maximizer bounds separately.
8. **Two-stage canonicalization:** the future profile determines G_B, not the raw B pointwise if B is noncanonical.
9. **All normalized vectors vs full relative Kpt types:** the result quantifies over labelled finite complete ordinary-L clique patterns, not dependent auxiliary E/parameter assignments for full corrected (B3).
10. **Past graph P:** no arbitrary fixed old prefix is attached. The graph is a standalone finite K_ell-free pattern. Embedding it as ordinary-L into the fixed Henson graph may use the finite chronological induction in draft PR #92, but that does not automatically preserve the diary's required old-front positions and auxiliary H+ data.
11. **No common source orbit:** even identical finite L-age profiles of two selected occurrences do not force a common labelled inverse source in the successor-tree monoid.
12. **No circular use of the desired characterization:** K-freeness is proved directly by finite clique classification and the raw bound, and future-vector exactness is checked by the already proved explicit graph; nothing assumes the big Ramsey degree theorem.

## Lean implementation order

First finish draft PR #93's single-support graph and K-freeness proof. Next define the all-support tagged reserved sum and its complete ordinary-L table. Prove exact clique classification by selecting one reserved support T and showing all reserved members share that tag, and all future members have T-sort. To bound reserved cardinality, inject the reserved portion into the finite block Fin(ell−1−B(T)); to bound the future portion, apply the verified PR #86 all-clique support theorem. The existing sharp raw-block lemma handles the final arithmetic. Then reuse the exact future-profile iff and canonical maxima from merged PR #88. Lastly formalize the violating-vector sharpness by exhibiting an ell-subclique in a **separate augmented graph** containing the forbidden component.

After complete hosted Lean checks, one may conclude the **finite ordinary-L gadget** is correct. One may NOT mark the full H+ resolved-copy B3/profile fidelity, common labelled source orbit or unconditional upper Ramsey bound green without separate geometric proofs.
