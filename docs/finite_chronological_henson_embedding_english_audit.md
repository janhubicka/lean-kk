# Finite chronological induced embedding of any K_ell-free L graph in a left-dense Henson graph

**12 November 2026. English proof and hostile audit BEFORE Lean.**

## Target and relationship to current code

The true Henson original graph E is an arbitrary fixed enumerated directed Boolean L-table with all finite initial segments K_ell-free and the precisely stipulated \`OnePointLeftDense E ell\` property. Let A be a SECOND symmetric, loop-free directed Boolean L-table; its first N indices constitute any finite K_ell-free graph.

The new claim is a genuinely **chronological induced embedding**
\(f:\{0,\ldots,N-1\}\to\mathbb N\) into the **same fixed E** such that

1. for all \(i<j<N\), \(f(i)<f(j)\);
2. for all distinct \(i,j<N\), \(E(f(i),f(j))=A(i,j)\).

The extension process in fact uses the stronger one-step theorem staged in PR #91, so each newly selected genuine original v is nonadjacent in BOTH directions to all earlier physical original indices not already named by the previously embedded pattern (including every intervening gap). The first theorem need only record the two displayed final embedding properties; the gap statement remains available separately at each construction step. Proving a persistent global gap invariant is useful later but is NOT silently claimed by this result.

A specialized corollary replaces the assumed E-prefix-freeness by the existing **normalized Henson forbidden-family** avoidance, retaining \`OnePointLeftDense\` of its enumeration. This constructs every finite ordinary-L K_ell-free pattern, but NOT yet a finite pattern with arbitrary auxiliary H+ Kpt E/parameter-closed source records.

## Induction proof

Use strong induction on N, or ordinary induction with the K_ell-freeness of the current abstract initial segment as a quantified premise.

**Base N=0.** Any function f works; strict increase and induced atom agreement are vacuous.

**Step N=n+1.** The old abstract prefix [0,n) is K_ell-free by heredity. Apply the inductive hypothesis to obtain a function f embedding it as a strictly increasing sequence of genuine E-indices.

Set \(P=[0,n)\), and let \(S=\{i<n:A(i,n)=1\}\) be the **complete old neighbour set** of abstract vertex n.

- **Safety in the abstract graph.** If S contained a directed clique of size ell−1, adding n would create an ell-clique in A[0,n+1), because A is symmetric and loop-free and n is adjacent in both directions to every member of S. This contradicts the assumed K_ell-freeness. Formally apply the already verified \`hasCliqueBelow_succ_iff_old_or_neighbour\` (requires ell>0 and the displayed A symmetry and false loops), or its equivalent explicit clique-witness argument. Hence the ACTUAL finite Boolean \`finitePoolCliqueCheck A (ell−1) S\` is false.
- **Choose a physical front.** Put \(\mathrm{front}=1+\max\{f(i):i<n\}\), taking the empty finite supremum as zero. Every already represented genuine original lies strictly below this front, including when n=0.
- **Transfer and realize.** The one-step theorem on the previous stacked PR #91 uses injectivity and full induced A/E agreement of f on P, transports the safety check to f[S], and invokes PR #87's true left-density theorem. It produces a genuine original \(v\ge\mathrm{front}\) with EXACT column
  \[
  E(f(i),v)=A(i,n),\qquad E(v,f(i))=A(n,i)
  \quad (i<n),
  \]
  and zero atoms to every other earlier E-index.
- **Extend the map.** Put \(f'(n)=v\) and \(f'(i)=f(i)\) for \(i\ne n\). All earlier images stay below front≤v, hence f' is strictly increasing on [0,n+1). Old-old atoms are unchanged; old-new and new-old atoms are exactly the ones supplied by the one-step theorem. Thus f' is an induced embedding of the n+1 prefix.

This proves the finite result for every N. It does not require a global inverse or homogeneity theorem: the only existence principle is the fixed left-dense enumeration, used one vertex at a time.

## Adversarial audit

1. **One-point safety uses the FULL old neighbour set.** A selected-shadow clique test or a bound on the mere cardinality of S is insufficient. The induction derives exactly the (ell−1)-clique-free condition from the whole finite target A prefix.
2. **Target A must be symmetric at each new column.** The chosen genuine Henson original is connected in both tuple orientations with the same bit; a generic asymmetric directed target cannot be embedded in an undirected graph.
3. **Target false loops.** The standard prefix decomposition uses looplessness. Do not omit its hypothesis even if the target is informally called a graph.
4. **E must have all old prefixes free.** This does NOT follow from the finite A hypothesis. The normalized Henson avoidance supplies it in the specialized corollary.
5. **Left density is a real enumeration hypothesis.** Arbitrary K_ell-free E (e.g. the empty graph) cannot realize every prescribed edge. Retain \`OnePointLeftDense\` explicitly.
6. **Empty prefix / n=0:** the finite supremum over an empty index set is 0, so front=1 works and the new neighbour set is empty. Nothing requires a phantom old vertex.
7. **Choose v≥front, not v=front.** The fixed left-dense enumeration may force arbitrary gaps. The one-step lemma makes all those intervening vertices nonneighbours, ensuring they do not create hidden positive columns to the new selected vertex.
8. **Strict monotonicity is only on the finite domain.** The total function f:Nat→Nat outside [0,N) is irrelevant; do not falsely require a strictly increasing total extension on all Nat.
9. **Preserve BOTH old-new directions.** The induction stores every ordered atom E(f(i),f(j))=A(i,j) when i≠j, not merely forward edges i<j.
10. **No stale-domain conflict:** at the n+1 step, the updated function must preserve f(i) for all i<n and change only f(n). Its proof uses the strict previous frontier bound and the exact new column from PR #91.
11. **No induced graph outside the chosen vertices.** Extra edges among the omitted physical gap vertices are unconstrained; only their edges to the newly selected v are zero. The theorem must not claim that the entire E prefix equals the abstract A prefix.
12. **Finite only.** An embedding of each finite K_ell-free pattern does not automatically yield one coherent embedding of a countable pattern with prescribed diary levels; a nested/recursive choice and control of auxiliary E is separate.
13. **Auxiliary Kpt E and parameter closure:** the result is for ordinary L edges. It does not preserve dependent-parameter tuples, assigned full upper L+ successor types, or the corrected B3 (I1/I2/I3) source.
14. **No optimal BRD conclusion:** full labelled inverse-source orbit and the upper-bound diary characterization are not consequences of finite ordinary-L universality.

## Formalization requirements

Use the actual exact finite prefixes \`HasCliqueBelow A N ell\`, \`IsDirectedCliqueOn\`, and \`finitePoolCliqueCheck\`, the verified target prefix split theorem \`hasCliqueBelow_succ_iff_old_or_neighbour\`, and the staged induced-copy one-point extension lemma from PR #91. Define the target finite embedding as a total f:Nat→Nat satisfying strict monotonicity and complete ordered-atom agreement only below N. Induct on N, taking the old image maximum from \`(Finset.range n).sup f + 1\` and the desired neighbour set from \`Finset.range n\` filtered by A(i,n). The specialized Henson version invokes \`hensonForbiddenFamily_no_prefix_cliques\`.

Register named transitive-axiom reports and require a complete hosted Lean build. Neither this finite theorem nor its specialization validates the unbounded numerical-H+ resolved-copy construction, full corrected-B3, or the common labelled source orbit. Leave manuscript global green markers unchanged.
