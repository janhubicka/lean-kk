# Numerical-H reserved prefix capacity — English proof and adversarial audit

**10 November 2026. English FIRST; Lean follows only after review.**

## Claim and precise carrier

Fix the true H constructor at integer height \(k\). Let \(q_0<\cdots<q_{r-1}\) be **distinct, increasing original labels**, inducing a complete symmetric irreflexive clique in the original graph. Assume \(1\le r\le k+1\). Its real numerical-H copies are \(q_b^t=\iota(q_b,t)\) for \(0\le b<r\), \(0\le t\le k\).

For a pivot \(a<r\), \(g\le k\), form the *single-block real-copy prefix*
\[
P_{a,g}=\{q_b^t:b<a,\ 0\le t\le k\}\cup
 \{q_a^t:0\le t\le g\}.
\]
Define capacity as the maximum **cardinality of a directed clique** in the literal binary L graph on \(P_{a,g}\), including the empty clique. Then
\[
\boxed{\quad \operatorname{cap}(P_{a,g})=
\begin{cases}a,&g<a,\\a+1,&a\le g.\end{cases}\quad}
\]
The formula is independent of whether \(g=k\), **because \(a<r\le k+1\) implies \(a\le k\)**. We are not measuring the neighbour pool of the pivot alone. Its capacity is a different number.

This is a claim about the reserved original clique's real H copies, not the entire ambient prefix with unrelated original vertices, fake singleton coordinates, or all selected/future labels. A global use must establish a separate isolation/partition statement, using the four-endpoint finite gluing theorem already in main.

## Actual binary gate — no alternate model

For \(b<c\), with both labels genuine reserved originals,
\[
  L(q_b^s,q_c^t)=1\iff
   s<t\ \text{or}\ (s=t=k).
\]
This is precisely the standard numerical-H real-real gate, since the corresponding original L atom is 1. The opposite directed bit agrees by original symmetry, and same-original copies have **no** edges (original irreflexivity). Thus a clique contains at most one copy per original label. The map to the original label is injective on any clique; the prefix contains only labels \(0,\ldots,a\). Hence every clique has size at most \(a+1\).

## Lower bounds

1. The \(a\) top copies \(q_0^k,\ldots,q_{a-1}^k\) form a clique by the **top-tie** alternative \(s=t=k\). All lie in \(P_{a,g}\). This works also for \(a=0\), where the empty clique is the witness of size zero.
2. If \(a\le g\), the \(a+1\) copies
   \(q_0^0,q_1^1,\ldots,q_{a-1}^{a-1},q_a^g\)
   form a clique by **strictly increasing** generations. They lie in the prefix because \(a\le g\le k\). Together with the universal \(a+1\) upper bound this proves the second case.

## Sharp upper bound when \(g<a\)

By \(a\le k\), the strict inequality \(g<a\) implies \(g<k\); this rules out the special top-tie edge when the clique contains a copy of the pivot original.

Take any clique \(S\subseteq P_{a,g}\).

- If \(S\) contains no copy of original \(q_a\), its original-label projection lands injectively in \(\{0,\ldots,a-1\}\), so \(|S|\le a\).
- If \(S\) contains \(q_a^h\), then \(h\le g<k\). Every other vertex is a copy \(q_b^t\) with \(b<a\), and its edge to \(q_a^h\) forces \(t<h\). The **generations** of these remaining vertices are pairwise distinct: if two different originals had the same \(t<h<k\), neither strict increase nor the top-tie gate would permit their edge. Therefore the map from \(S\setminus\{q_a^h\}\) to the generations \(0,\ldots,h-1\) is injective. We conclude \(|S|\le h+1\le g+1\le a\).

This closes the first case, with no dependence on Ramsey/age assertions.

## Adversarial audit and regression controls

- **Essential height condition.** Without \(r\le k+1\), take \(a=k+1\) and \(g=k<a\). All \(a+1\) copies \(q_0^k,\ldots,q_a^k\) form a top-generation clique. The naive formula incorrectly gives only \(a\).
- **Top-tie cannot be deleted.** If all equal-generation \(k\)-edges are suppressed, the alleged \(a\)-clique in the first case may disappear.
- **Do not collapse copies by original.** The ambient H carrier contains *many* copies per original. A clique, but not an arbitrary subset, has at most one; this must be proved via the actual L table.
- **Do not count a fake vertex as an original.** The statement is for real copies. Fake coordinates with no binary edges can contribute an isolated singleton; they require an extra argument if included in a larger carrier.
- **Do not replace a directed clique with a graph path.** For machine regressions, a DP exploiting transitivity was checked against an *independent all-pairs brute-force clique oracle* for every \(k\le3\).
- **No unconditional full-front conclusion.** Actual selected-future supports, parameter E columns, overlapping old pools, and the integer-age canonicalizer remain independent obligations.
- **No invalid zero-boundary inference.** When \(a=0\), the first case \(g<a\) is impossible. The second case yields the one pivot copy and capacity 1, while the empty-set clique has size 0.

## Executable regression evidence

An independent Python test evaluated the exact real-real Boolean generation gate on every relevant pair for **1,705** cases with \(0\le k\le9\), \(1\le r\le k+1\), \(0\le a<r\), \(0\le g\le k\), and found **zero** deviations from the formula. The test also found systematic height-condition counterexamples when \(k<a\) and \(g=k\). The all-pairs brute-force oracle agrees with the dynamic programme for all tested \(k\le3\). These finite checks are regression tests **not Lean proofs**.

## Lean implementation contract

Formalize the result first over finite label/generation pairs with the literal gate, giving (a) lower witnesses, (b) injective original-label upper bound, (c) injective-generation sharp upper bound, and finally the exact finite capacity. Only then transfer via the verified injective \(\iota\) and \`hNumericBinary_real_forward_iff\` to the actual H graph and the existing \`finiteDirectedCliqueCapacity\` API.

Require the full local compiler check and the hosted project \`lake build\` with **named transitive-axiom reports**. No manuscript green marker should be added until the exact actual-H bridge, not just the abstract gate lemma, has passed.
