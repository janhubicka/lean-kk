# Finite exact clique capacity transports through an injective induced L-copy

**12 November 2026. English proof and hostile audit BEFORE Lean.**

## Target and motivation

A crucial missing step in converting abstract labelled witness components into **actual Henson** originals is proving that a finite partial embedding preserves the *complete old-neighbourhood clique test*. The one-point left-density theorem (merged PR #87) works with an actual old-neighbour set \(S\subseteq\mathbb N\), but the intended certificate comes from a finite abstract pattern with its own index set. One must transport clique-freeness through a genuine **injective induced** embedding, not assume it.

Fix two arbitrary **directed** Boolean ordinary-L tables \(A,E:\mathbb N^2\to\mathrm{Bool}\), a finite set \(P\subseteq\mathbb N\), and an arbitrary function \(f:\mathbb N\to\mathbb N\). Assume:

1. **Injectivity on P:** \(x,y\in P,\ f(x)=f(y)\Rightarrow x=y\).
2. **Complete atom agreement on P:** for all distinct x,y∈P,
\[
A(x,y)=E(f(x),f(y)).
\]
Here the Boolean equality includes **present and absent** atoms, in **both ordered orientations** by quantifying over all x,y.

Then the actual finite exact directed-clique capacities agree:
\[
\boxed{\operatorname{cap}_A(P)=\operatorname{cap}_E(f[P]).}
\]
Consequently, for **every** q≥0,
\[
\boxed{
\operatorname{finitePoolCliqueCheck}(A,q,P)=\mathbf{false}
\iff
\operatorname{finitePoolCliqueCheck}(E,q,f[P])=\mathbf{false}.
}
\]
The q=0 boundary is included. No symmetry, loops, graph universality or age assumption is needed.

### Proof of the capacity equality

For any clique s⊆P, injectivity on P implies |f[s]|=|s|, and the complete atom agreement implies f[s] is a directed clique of E. Hence cap_A(P)≤cap_E(f[P]).

Conversely, let t⊆f[P] be any directed clique of E. Define the **explicit finite preimage set**
\[
s=\{x\in P:f(x)\in t\}.
\]
It satisfies f[s]=t. Injectivity on P gives |s|=|t|. For distinct x,y∈s, their images are distinct, so the positive E atom between them transports through the stipulated Boolean equality to a positive A atom; thus s is a directed clique. Hence cap_E(f[P])≤cap_A(P).

This is the already-validated method of \`Kk.reservedPrefixCapacity_image_transport\` (PR #74), generalized from the numerical-H real-copy pair carrier and its special gate to arbitrary finite labelled L-structures.

### Exact clique-checker transfer

Use the already kernel-checked
\`finitePoolCliqueCheck_false_iff_capacity_lt\` on both P and f[P], at the same threshold q. Substitute the capacity equality. The result is exact and requires no per-q induction.

## Adversarial audit

1. **Injectivity is essential.** Two mutually adjacent original vertices could map to one image vertex. That collapses a 2-clique and invalidates capacity equality.
2. **Inducedness is essential for an iff.** A one-way graph homomorphism preserving positive A edges gives only one capacity inequality; an extra E edge between two originally nonadjacent vertices can create a new image clique.
3. **Both orientations are required for a directed graph.** It is not enough to match A(x,y) for x<y and ignore A(y,x).
4. **Diagonal equality is unnecessary.** Directed cliques test only distinct vertices. We neither assume nor use looplessness; the theorem is stronger than a graph-only special case.
5. **Image restriction matters.** The target pool is exactly f[P]. Arbitrary extra vertices in the ambient E prefix may create cliques and cannot be ignored.
6. **Nonempty and q=0 boundaries.** For q=0, a 0-clique (the empty set) is detected by the exact checker, and both checker values agree; do not use a false “every graph is K_0-free” premise.
7. **Finite pullback is explicit.** The inverse of f need not exist globally. Use \`P.filter (fun x=>f x∈t)\` and injectivity on P, not global surjectivity.
8. **No need to specialize to ordered embeddings prematurely.** Strict monotonicity implies injectivity, but the capacity transfer works with any injective finite representation; chronological order is a *separate* constraint in the Henson enumeration.
9. **Pullback preserves the entire clique**, not just its cardinality; this prevents a false proof of image capacity based only on cardinalities.
10. **No physical extension theorem yet.** This result says an *already given finite induced map* transports exact safety certificates. It does not construct a later vertex realizing a new column in the fixed Henson E graph.
11. **Auxiliary Kpt E is different.** The two ordinary-L tables here are graph edges, not the H+ auxiliary parameter/closure E relation.
12. **Interaction with left-density:** if the desired abstract neighbour pool S is K_(ell−1)-free and its existing selected originals are represented by an injected induced map f into E, then the physical pool f[S] is K_(ell−1)-free by this theorem. That supplies the *exact* safe input for PR #87's one-point existence result, provided the pool lies below the chosen front. Extending f chronologically to include the selected later vertex is the next proof.
13. **No common labelled orbit:** even an embedding of every finite L pattern does not imply the full parameter-closed corrected B3 source or a common inverse-source monoid orbit.

## Formalization

First prove exact capacity equality using the existing \`Kk.finiteDirectedCliqueCapacity\` and \`Kk.IsDirectedCliqueOn\`; the same finite-filter preimage approach used in the verified numerical-H real-copy image-capacity theorem is appropriate. Then deduce the exact checker iff via \`finitePoolCliqueCheck_false_iff_capacity_lt\`. Finally prove the sharp **forward safe-neighbour pool** corollary in the form needed by the chronological extension induction.

The full pinned project \`lake build\` and exact named standard-only transitive-axiom checker are mandatory before merging. This is a new finite-embedding structural lemma, not a reason to mark the global diary characterization green.
