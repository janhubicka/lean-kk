# From the finite all-support L gadget to genuine Henson originals: exact finite enumeration adapter

**13 November 2026. English-first proof and adversarial audit.** This is a proposed composition of the explicitly constructed all-support graph (draft PR #94) with the hosted-verified finite chronological Henson induced-embedding theorem (merged PR #92). It deliberately proves only an *ordinary-L induced copy*, not a full numerical-H/Kpt source.

## Finite reindexing lemma

Let V be ANY finite type, E_V:V×V→Bool a symmetric irreflexive binary edge table, and assume the graph is K_ell-free in the strong directed sense:
\[
\forall s\subseteq V\ \bigl(\forall x\ne y\in s,\ E_V(x,y)=1\bigr)
 \Rightarrow |s|<\ell.
\]
Choose an explicit bijection \(e:\mathrm{Fin}(N)\simeq V\), where \(N=|\!V\!|\). Define a Boolean L table \(A:\mathbb N^2\to Bool\) on the **first N naturals** by
\[
 A(i,j)=
  \begin{cases}
  E_V(e(i),e(j)), & i<N,\ j<N,\\
  0, &\text{otherwise}.
  \end{cases}
\]
This table is symmetric and loop-free (including outside [0,N)). It has **no directed K_ell entirely in its first N vertices**: a putative clique s⊆[0,N) is injected into V by e, preserving all ordered edges, so its image would be an ell-clique in V, contrary to the hypothesis.

Then \`henson_leftDense_embeds_finite_KFree_pattern\` from verified PR #92 applies under the normalized Henson forbidden-family avoidance (ell≥2) and the fixed graph's explicit \`OnePointLeftDense\` predicate. It yields a strictly increasing f on [0,N) with
\[
 E_H(f(i),f(j))=A(i,j) \quad(i\ne j<N).
\]
Composing \(e^{-1}:V\to\mathrm{Fin}(N)\) with f gives an injective *induced ordinary-L embedding* of the actual finite graph V into the fixed Henson original enumeration, with every present AND absent edge preserved in both directions.

## All-support gadget specialization

Take \(V=\{v\in\mathrm{AllSupportFutureVertex}(d,\ell,B):v\in
\mathrm{allSupportFutureCarrier}(d,\ell,B)\}\), the finite subtype of exactly those vertices in the constructed tagged graph, not the entire ambient dependent-sum type which contains infeasible future weights.

The restricted ordinary-L edge table is the literal \`allSupportFutureEdge\` of PR #94. Its symmetric, loop-free and K_ell-free facts are exactly the three proposed endpoints of that PR. Applying the reindexing lemma therefore constructs an **actual finite family of Henson original indices** whose induced ordinary-L graph has:
- one complete reserved support clique of size ell−1−B(T) for **every** admissible T;
- no cross edges between reserved cliques of distinct supports;
- one common collection of jointly feasible future clique components, with exact multiplicities and no cross-component edges;
- in BOTH directions, exactly the selected-support adjacency bit between every reserved support T-block and every future vertex of sort j.

No passage to a hypothetical graph-age equality is used: all these Boolean edges are already in V and are preserved by an induced embedding. The embedding can have gaps in the fixed Henson enumeration; PR #92 guarantees its chosen image vertices are strictly ordered and their *induced* mutual edges agree. Edges involving **unselected gaps and unrelated preexisting Henson originals** are not part of this finite induced-copy statement.

## Adversarial audit

1. **Finite carrier subtype:** the ambient dependent sum contains vertices indexed by infeasible integer vectors. Enumerating the whole type instead of the designated Finset carrier can destroy K_ell-freeness.
2. **Both directions:** use a symmetric source table and induced equality of all *ordered off-diagonal* L atoms. A one-way homomorphism is insufficient to recover nonedges.
3. **No hidden loops:** PR #92's finite target theorem requires explicit A(i,i)=false, so use the actual all-support edge-irreflexivity from PR #94.
4. **ell≥2 in the Henson specialization:** the normalized forbidden-family API has this premise. The standalone gadget only required ell>0.
5. **Fintype cardinality:** use \(N=Fintype.card V\). The empty V case has N=0 and a unique vacuous encoding; never invent a vertex for a zero-support bound.
6. **Image injection:** the finite equivalence e and the strict monotonicity of f on [0,N) jointly give injectivity on V; no global injectivity of f outside the prefix is needed.
7. **Actual clone, not literal named indices:** the Henson embedding produces new natural original labels, often nonconsecutive. It does not identify them with the specific numerical-H original indices presumed by an already fixed diary template.
8. **Old past P:** the theorem constructs a standalone finite induced copy, not a *relative extension over a previously fixed graph P* with required edges to every old coding/parameter vertex.
9. **Gaps:** the staged one-point source theorem makes a newly chosen vertex nonadjacent to intervening unnamed vertices; the final finite embedding theorem records only the induced chosen-vertex graph, not a complete global gap invariant for every pair.
10. **Parameter-closed H+ E:** the ordinary L graph and its Henson induced copy are insufficient to reconstruct auxiliary E/closure, the actual selected/front source assignment, I1/I2/I3 events or full corrected B3.
11. **Same labelled monoid inverse source:** finite induced graph isomorphism is much weaker than the required equality of labelled inverse sources under genuine successor-tree monoid maps.
12. **No circularity:** K-freeness of V is proved by finite support-block clique classification, not by assuming the desired upper Ramsey bound.

## Lean plan

First formalize a generic finite-type encoding lemma using \`Fintype.equivFin\` (or a stable finite enumeration) to transport K_ell-freeness of a symmetric irreflexive graph on V to a Nat-indexed pattern on [0,Fintype.card V). Then compose it with the actual verified \`henson_leftDense_embeds_finite_KFree_pattern\` theorem, yielding an injected induced image inside the fixed normalized Henson graph.

Only after the full all-support gadget PR #94 passes should the specialized source be committed to an integrated Lean branch. This will close the *finite ordinary-L* physical realization step but leaves the entire **relative parameter-closed H+ source** and common labelled inverse orbit open.
