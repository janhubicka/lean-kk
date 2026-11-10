# Exact finite clique-capacity support bounds versus ALL continuation witnesses

**10 November 2026 — English-first proof and adversarial audit.**

## Why this adapter is needed

The finite numerical-H gluing theorem now reduces the absence of new K_ell cliques meeting a reserved pool to
\[
 a+\operatorname{cap}_E(U)<\ell.
\]
A full corrected-B3 age comparison, however, quantifies over arbitrary *L-only continuation witnesses*, not merely the realized selected-top copies. We must translate the capacity bound into a uniform statement about all clique witnesses in an arbitrary finite continuation graph.

## Data

Let \(E:\mathbb N^2\to\mathrm{Bool}\) be ANY directed edge table, \(W\subseteq_{\rm fin}\mathbb N\) a future-vertex pool, \(\sigma:\mathbb N\to\mathrm{Fin}(d)\) a sort map and \(T\subseteq_{\rm fin}\mathrm{Fin}(d)\) a chosen support. Define \(U=\{w\in W:\sigma(w)\in T\}\). Write \(\operatorname{Cliq}_E(s)\) for the repository's *full directed* clique predicate (both ordered arcs required between distinct vertices), and \(\operatorname{cap}_E(U)\) for the repository's exact maximum clique cardinality, attained by a finite clique even when U is empty.

For arbitrary \(a,\ell\in\mathbb N\), the exact statement is
\[
\boxed{\quad
a+\operatorname{cap}_E(U)<\ell
\iff
\forall s\subseteq W\;\bigl(\operatorname{Cliq}_E(s)\Rightarrow
   a+|\{v\in s:\sigma(v)\in T\}|<\ell\bigr).
\quad}
\]
There is **no assumption** that W, U, or any individual sort class is a clique, and no assumption that W is K_ell-free.

## English proof

**Forward.** Take any clique \(s\subseteq W\). Its selected part
\(s_T=s\cap U=\{v\in s:\sigma(v)\in T\}\)
is a directed clique (inheritance to subsets), and \(s_T\subseteq U\). Therefore \(|s_T|\le\operatorname{cap}_E(U)\), giving the desired inequality by addition of a.

**Reverse.** The existing verified theorem \`finiteDirectedCliqueCapacity_attained\` supplies a clique \(s\subseteq U\) with \(|s|=\operatorname{cap}_E(U)\). Since \(U\subseteq W\), the universal witness inequality applies to s; every vertex of s lies in the selected part, so \(s_T=s\). Thus \(a+\operatorname{cap}_E(U)<\ell\).

The empty-U case is included: its maximizing clique is empty. Then the right side applied to the empty clique yields precisely \(a<\ell\), matching the left side.

## Exact raw-bound translation

If in addition **a<ell**, natural-number arithmetic gives
\[
a+c<\ell\iff c\le\ell-1-a
\]
for every \(c\in\mathbb N\). Therefore the same lemma yields:
\[
 \operatorname{cap}_E(U)\le\ell-1-a
\iff
\forall s\subseteq W\;(\operatorname{Cliq}_E(s)\Rightarrow
 |\{v\in s:\sigma(v)\in T\}|\le\ell-1-a).
\]
This is precisely the form of the single-support raw clique-bound used by \`rawCliqueBlockBound\`. The necessary inequality a<ell is available at genuine cover stages since \(\ell=\operatorname{lower}(T)+r+1\) and a≤r; it MUST NOT be silently omitted from a general statement.

## Hostile audit

1. **Natural subtraction boundary.** If a≥ell, the raw inequality with \(\ell-1-a=0\) can hold even when \(a+\operatorname{cap}_E(U)<\ell\) is false. The second theorem therefore assumes a<ell.
2. **W need not be K_ell-free.** This single-support budget does NOT imply absence of a forbidden clique lying wholly in W or old-plus-W. The separate gluing hypothesis on P∪W remains necessary.
3. **U may be empty.** The empty-clique maximizer and s=∅ universal witness are essential: no false implication at ell=0 or a=ell.
4. **U need not be a clique.** Replacing cap(U) by |U| invalidates the reverse equivalence in non-complete future graphs.
5. **Full directed clique** is required, not a one-orientation chain; all ordered pairs in s must satisfy the existing predicate.
6. **Sort map need not be injective.** Multiple clique vertices of one sort contribute multiplicity; do not replace the filtered cardinality by the cardinality of T or its support set.
7. **Arbitrary W vs universal over all W.** The theorem quantifies over every clique *inside one given W*. It does NOT assert that every prescribed continuation W has an admissible realization in the K_ell-free original. That is a separate extension theorem.
8. **No integer-age circularity.** The theorem is pure finite-graph combinatorics. Identifying a clique's counts with the finite integer vector \`IntegerCliqueWeights\`, then taking the canonical graph age, remains another adapter.
9. **Past and gaps.** Neither the old/reserved disjointness nor past-K_ell check is discharged here.
10. **No auxiliary E.** The edge relation E in this note means ordinary Boolean L adjacency; it is unrelated to the auxiliary parameter E of H+.

## Validation contract

First kernel-check this equivalence on the existing \`IsDirectedCliqueOn\`, \`finiteDirectedCliqueCapacity\`, \`finiteDirectedCliqueCapacity_attained\`, and \`directedClique_card_le_capacity\` APIs. Then prove the raw-bound corollary under a<ell using Omega. The entire proof (including empty-pool boundary) was first tested in a pinned local Lean 4.35.0-rc3 / Mathlib model that reproduced the exact existing capacity and clique predicates; it produced no nonstandard axioms.

A full exact-head hosted \`lake build\` and named transitive-axiom audit are REQUIRED before adding any manuscript validation markers. The next mathematical bridge identifies each filtered clique cardinality with its normalized integer witness vector \`IntegerCliqueWeights\`, and must retain the outside-support old-plus-future age test.
