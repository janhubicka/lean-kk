# Actual numerical-H top-selected support columns for a reserved block

**10 November 2026: English proof and hostile audit BEFORE Lean.** This note is independent of the full unbounded resolved-copy theorem; no conclusion about final Ramsey degrees is asserted.

## Data

Work with the literal numerical H binary L relation of a symmetric original graph \(E\), at height \(k\) and finite carrier bound \(M\). The reserved clique block occupies consecutive original labels \(N,\ldots,N+r-1\), with \(a<r\). The real-copy reserved prefix is
\[
Q=\{\iota(N+b,t):b<a,\ t\le k\}\;\cup\;
   \{\iota(N+a,t):t\le g,\ t\le k\}.
\]

Take a finite set \(S\) of **genuinely later original labels**, all \(j\ge N+r\), and a supported subset \(T\subseteq S\). Define whole top-original future pool
\[
W=\{\iota(j,k):j\in S\},\qquad U=\{\iota(j,k):j\in T\}.
\]
There is **no** clique condition on S, T, W, or U. In particular the gluing budget must use the *actual directed clique capacity* of U, not \(|U|\).

Assume the *uniform original support column*:
\[
\tag{*}
\forall b<r,\ \forall j\in S:\quad E(N+b,j)=\mathbf1_{j\in T}.
\]
This is a geometrical assumption about the chosen original adjacency table, **not** the conclusion of a Ramsey or age theorem. It can fail in a proposed recursive construction, and mixed-neighbourhood admissibility is still open.

## Physical top-generation lemma

Fix \(q=\iota(N+b,t)\in Q\), \(w=\iota(j,k)\in W\). The definition of Q gives \(b\le a<r\) and \(t\le k\). Laterness gives \(N+b<j\), so the existing checked \`numericH_older_generation_to_top_exact\` proves
\[
L_H(q,w)=E(N+b,j)
\]
**as an exact Boolean equality**, including absent bits, because the generation gate is automatically open to target generation k. The original E symmetry and already checked \`henson_finiteNumericH_binary_symmetric\` give
\[
L_H(w,q)=E(j,N+b)=E(N+b,j).
\]
By (*), both bits equal decide(j∈T).

## Top-image membership and automatic separation

The map \(j\mapsto \iota(j,k)\) is injective by \`hPosition_injective_bounded\` (both generation arguments k≤k). Therefore, for each \(j\in S\),
\[
  \iota(j,k)\in U\quad\iff\quad j\in T.
\]
Hence **both** directed L bits of every reserved q to every future w equal decide(w∈U). This discharges the exact two-direction support hypothesis \`hSupport\` of \`finitePoolCliqueCheck_isolated_block_gluing_iff\` without assuming the resulting age conclusion.

The inclusion \(T\subseteq S\) gives \(U\subseteq W\). The sets Q and W are disjoint: if \(\iota(N+b,t)=\iota(j,k)\), injectivity of \(\iota\) on bounded generations forces \(N+b=j\), contradicting \(b<r\) and \(j\ge N+r\). Thus Q and U are disjoint automatically. These proofs are literal-coordinate results, not abstract labels.

## Exact one-block gluing corollary

Feed the proved Q/U disjointness, U⊆W, and all two-direction support bits into the verified physical gluing theorem of the preceding finite-carrier PR. The remaining input hypotheses are only the explicit complete past K_ell test, old/reserved nonedges, and gap/future zeros. The resulting iff has exactly
\[
\neg K_\ell(P\cup Q\cup G\cup W)
\iff \neg K_\ell(P\cup W)\quad\wedge\quad
 (a+\mathbf 1_{g\ge a})+\operatorname{cap}(U)<\ell.
\]
This does not assert these remaining hypotheses always hold. A recursive construction must verify its full old-to-future and gap-to-future adjacency **simultaneously**, along with parameter E and the integer-age canonicalizer.

## Adversarial checks

1. **Original versus numerical support:** (*) concerns original \(E(N+b,j)\), not the numerical-H auxiliary E relation. Mixing them would invalidate the claim.
2. **Every earlier generation:** the exact forward theorem works for t=k as well as t<k due to the top-tie gate. Restricting to designated generations would not establish the whole Q column.
3. **Both directions:** the reverse bit needs the graph-symmetry hypothesis. The general H constructor is directed; do not infer reverse equality without proof.
4. **Image membership:** proving \(j∈T\Rightarrow w∈U\) alone is insufficient. To obtain an *exact* support equation, injectivity is needed for the converse.
5. **No accidental overlap:** Q∩W=∅ follows from laterness, not from mere disjointness of the **pair-labelled** original index sets.
6. **Fake vertices:** Q and W consist entirely of explicitly real even coordinates. No claim about arbitrary fake or unmarked vertices is made.
7. **T not a clique:** U may contain a nonclique; replace cardinality by exact clique capacity only under a separate clique hypothesis.
8. **Multiple old blocks:** the hypothesis (*) does not imply nonedges between Q and an arbitrary old pool P, or between gap G and W; these remain independent.
9. **No age circularity:** the entire-old-plus-reserve-plus-gap clique check and old-plus-future test must remain explicit.
10. **Height and carrier:** the quantitative prefix formula uses a<r≤k+1 and g≤k, while real-carrier inclusion additionally needs \(\iota(N+a,g)<M\).
11. **Parameter closure:** this concerns ordinary binary L, not the Kpt auxiliary E, and does not establish full parameter-closed B3 or a common labelled source.
12. **Global existence:** uniform adjacency (*) is not automatic from Henson universality when future vertices carry other prescribed neighbours; the complete one-point mixed certificate must still be constructed.

## Implementation order

First prove top-coordinate injectivity, exact image membership and Q∩W=∅. Then deduce the complete two-direction physical H binary column for all q∈Q,w∈W using existing exact top-generation lemmas. Finally specialize the previously checked physical four-pool gluing iff and retain all unproved old/gap/past hypotheses visibly. Before manuscript validation, require full project \`lake build\`, a named transitive-axiom report with standard axioms only, and a separate adversarial check that (*) can be realized in the intended recursive construction.
