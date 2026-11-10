# Physical numerical-H finite carrier and exact isolated-block gluing

**10 November 2026 — English proof and hostile review before Lean.**

## What has been checked already

PR [#75](https://github.com/janhubicka/lean-kk/pull/75) passed a complete hosted Lean build and **315 named standard-only transitive-axiom reports** at revision \`9de8be2e339e7851a2182cf5672dd42aeeb2cb19\`; merged as \`9e03d4e021cca4e14bcfebf65a11d393d0c9143c\`. It proves the exact real-copy clique capacity inside the literal finite numerical-H binary L-reduct. The capacity theorem is about a finite set of real H-coordinate labels; it deliberately does not presume those labels lie in the finite carrier \([0,M)\).

## Carrier lemma — English proof

Fix height k, block start N, pivot a, generation g and finite cut M. Assume
\[
\iota_k(N+a,g)<M,\qquad \iota_k(i,t)=2(k+1)i+2t.
\]
Recall that \`reservedBlockNumericPrefix k N a g\` is the image of pairs (b,t) with b<a and t≤k, or b=a and t≤g (subject to t≤k).

Take any u in that image, represented by (b,t). If b=a, then t≤g and the explicit formula gives \(\iota_k(N+a,t)\le\iota_k(N+a,g)<M\). If b<a, then t≤k and **the existing** \`hPosition_lt_of_block_lt\` proves
\(\iota_k(N+b,t)<\iota_k(N+a,g)<M\).
These two exhaustive cases show that every member lies in the genuine carrier of \`finiteNumericHL (normalizedGraphModel E) k M\`.

The local model of this proof was compiled with official pinned Lean 4.35.0-rc3 and the pinned Mathlib, including the named axiom report. No new axiom is needed. The dependent project theorem must reuse the actual \`hPosition_lt_of_block_lt\`, not duplicate it.

## Exact physical gluing equivalence — English proof

Put \(\mathcal H(u,v)\) equal to the actual ordinary binary atom
\[
(\mathrm{finiteNumericHL}(\mathrm{normalizedGraphModel}\,E)\ k\ M).binary\ u\ v\ (0:\mathrm{Fin}\ 1).
\]
Let Q be **exactly** the reserved coordinate prefix from the carrier lemma. Let P be a finite old-coordinate pool, G a finite inserted gap pool, W a finite future pool and U⊆W the supported future pool.

Assume precisely the hypotheses required by the already checked \`finitePoolCliqueCheck_isolated_block_gluing_iff\`:
- Q and U are disjoint;
- U⊆W;
- every P-to-Q ordinary L bit vanishes;
- every G-to-W ordinary L bit vanishes;
- for every q∈Q and w∈W, BOTH ordinary L(q,w) and L(w,q) equal decide(w∈U);
- the entire past P∪Q∪G passes the K_ell clique check.

Then the existing exact finite gluing theorem yields:
\[
 \neg K_\ell(P\cup Q\cup G\cup W)
 \iff
 \neg K_\ell(P\cup W)\ \wedge\
 \mathrm{cap}_{\mathcal H}(Q)+\mathrm{cap}_{\mathcal H}(U)<\ell.
\]
The new checked physical prefix-capacity theorem identifies
\(\mathrm{cap}_{\mathcal H}(Q)=a\) when \(g<a\), and \(a+1\) otherwise, provided \(a<r\le k+1\), \(g\le k\), original clique edges \(E(N+b,N+c)=1\) for b<c<r and original symmetry. Substitution produces the exact iff with \((\operatorname{if}\ g<a\ \operatorname{then}\ a\ \operatorname{else}\ a+1)+\operatorname{cap}_{\mathcal H}(U)<\ell\). No additional disjointness, maximality, or age assumptions are required.

This is a conditional **physical** gluing theorem: the entire old, gap and future adjacency hypotheses are stated explicitly. It is not a proof that the desired recursive Henson construction satisfies them. That later proof must use whole-front top-column and old-block isolation lemmas.

## Hostile checks

1. **Carrier bound must be numerical**, not just an original-label cutoff. Earlier blocks with generation k precede the pivot by the H block-order lemma.
2. If pivot generation g is smaller than k, all earlier blocks' top copies still lie below the pivot **because block order dominates generation order**.
3. The finite H L structure has neutral fake coordinates. Our Q contains only explicitly real copies; no unproved claim is made about arbitrary fake coordinates.
4. The E in this theorem is the **ordinary L binary edge table**, not auxiliary H+ E incidence.
5. \`hNoPQ\` and \`hNoGW\` have one ordered direction exactly as in the already verified classification lemma. The selected support \`hSupport\` has two directions; dropping one admits counterexamples for directed cliques.
6. The gluing theorem's past test cannot be omitted, and neither can the old+future test. A forbidden clique may lie entirely in either of those pools.
7. Do not replace actual \(\mathrm{cap}(U)\) by \(|U|\): U need not be a clique. The complete join with Q has capacity \(\mathrm{cap}(Q)+\mathrm{cap}(U)\).
8. Do not implicitly require Q to be a clique. At g<a it has many real copies with a sharp capacity a; for g≥a its capacity is a+1.
9. The earlier height condition r≤k+1 remains necessary for the sharp prefix formula.
10. No claim about full parameter-closed B3 source records or a common labelled orbit follows from the graph-L calculation alone.

## Formalization contract and remaining gap

First kernel-check the numerical carrier lemma and its direct membership in the finite H carrier. Then specialize the exact old/future/reserve/gap gluing iff by substituting the physical capacity theorem. Register named axiom reports and demand a full repository build with only standard axioms.

**Remaining:** derive hNoPQ, hNoGW, hSupport, hPast and old/future admissibility *simultaneously* for each marked-front stage of the actual recursive construction; then transport the continuation test through the integer graph-age canonicalizer. No new manuscript green marker until those adapter hypotheses have been proved in the intended application.
