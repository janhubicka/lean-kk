# Exact finite neighbour-pool criterion for one real Henson extension

**12 November 2026. English proof and adversarial audit, committed before Lean.**

## Problem on the critical path

The universal finite typed-clique construction gives a complete finite ordinary-L model of a desired integer-age witness system. To realize its vertices inside **one fixed** left-dense Henson graph, the actual old-neighbourhoods of newly chosen originals must all be legal. The existing kernel-checked \`OnePointLeftDense\` theorem realizes a later original when its *complete* finite neighbour certificate is negative, with nonedges to every intervening gap original. We need an exact finitary criterion in terms of an explicitly proposed neighbour set S—not the overly strong condition that \(|S|<\ell-1\).

## Exact Boolean certificate equivalence

Let \(E:\mathbb N^2\to\mathrm{Bool}\) be an arbitrary directed Boolean graph, \(\mathrm{front},q\in\mathbb N\), and \(S\subseteq_{\rm fin}\mathbb N\) with \(S\subseteq[0,\mathrm{front})\). Put
\[
n_S(x)=\operatorname{decide}(x\in S).
\]
Then the existing library's executable finite-neighbour checker satisfies
\[
\boxed{
\operatorname{finiteNeighbourCliqueCheck}(E,\mathrm{front},q,n_S)
    =\mathrm{false}
\iff
\operatorname{finitePoolCliqueCheck}(E,q,S)
    =\mathrm{false}.}
\]
No assumption of symmetry, graph-age universality, or q>0 is required.

**Proof.** Both checkers are already verified to be false precisely when there is no directed q-clique witness of the prescribed form. For the left side, any witness has every vertex below front and satisfying n_S(x)=true, hence belongs to S. For the right side, any witness contained in S lies below front by hypothesis and has n_S(x)=true. The same finite set and all its directed E edges witness either condition. This argument works also for q=0: the empty clique makes both checkers nonnegative, so both displayed false equalities fail together.

## Actual left-dense Henson realization

Assume \(\ell>0\), the fixed Boolean edge table E is K_\ell-free on the initial segment \([0,\mathrm{front})\), and E satisfies **the explicitly stipulated** \`OnePointLeftDense E ell\`. If
\[
\operatorname{finitePoolCliqueCheck}(E,\ell-1,S)=\mathrm{false},
\]
then the above equivalence gives the exact complete-neighbour certificate. The verified \`onePointLeftDense_realizes_finite_certificate\` yields a genuine index \(v\ge\mathrm{front}\) such that
\[
\forall x<v:\quad E(x,v)=E(v,x)=\operatorname{decide}(x\in S).
\]
Every vertex in S is a neighbour in BOTH orientations, every older original outside S is a nonneighbour, and every intervening original \(\mathrm{front}\le x<v\) is a nonneighbour, all in the **unchanged fixed graph**.

For the normalized Henson language, the verified \`hensonForbiddenFamily_no_prefix_cliques\` discharges initial-prefix K_\ell-freeness from genuine forbidden-pattern avoidance; \`henson_leftDense_realizes_certified_original\` then gives the same conclusion with exact premises \(\ell\ge2\), avoidance, left density, S⊆front and K_{\ell-1}-freeness of the induced old neighbour pool.

## Why this improves the earlier sufficient condition

The old \`SmallCliqueLeftDense\` route required \(|S|<\ell-1\). That is sufficient but unnecessary. For \(\ell=3\), S may be an arbitrarily large independent set: its graph has no K_2, so a new vertex adjacent to **all** of S remains triangle-free. The sharp criterion uses \(\mathrm{cap}_E(S)<\ell-1\), rather than \(|S|<\ell-1\). This is especially useful when many witness components or old selected types share a passing neighbourhood of low clique capacity.

## Hostile audit

1. **All required old atoms.** S is the *complete* intended neighbour set among the entire old prefix, including coding/split/parameter originals represented in the original graph. Replacing S by only the selected active branches can hide a forbidden clique.
2. **Every intervening gap index.** Left-density returns v≥front, not necessarily v=front. The theorem must explicitly prove decide(x∈S)=false for front≤x<v using S⊆front; gaps are not allowed to acquire positive edges.
3. **One- and two-sided orientation.** The finite checker uses the full directed clique predicate; the left-density conclusion supplies BOTH orientations. We do not assume graph symmetry for the certificate equivalence; the Henson specialization already has symmetric original E from its normalized family.
4. **Necessity of the neighbourhood test.** In the triangle-free case, if S contains adjacent old vertices p,q, any new vertex adjacent to both forms a triangle.
5. **No cardinality shortcut.** A large independent S can be safe; the inequality |S|<ell−1 is unnecessarily strong and cannot replace exact clique capacity.
6. **No arbitrary extension premise.** The one-point theorem constructs one vertex with its prescribed column. A general finite schedule still needs an induction maintaining the induced embedding of **all previously chosen** vertices, and at each step must prove the next S is K_{\ell-1}-free. This is not automatically inherited from abstract integer-age bounds unless the full old graph representation is faithful.
7. **Zero threshold q=0.** Both exact checkers detect the empty clique, so the two false values are equivalent even though both are unattainable. The actual Henson application has ell≥2.
8. **Finite support containment.** S⊆front is essential. If S contains a vertex x≥front, the left checker ignores it while the right checker does not.
9. **No initial prefix conclusion from left density alone.** The proof requires K_\ell-free old-prefix, either explicitly or via the *real* normalized Henson family avoidance theorem.
10. **Auxiliary H+ E still open.** This is a theorem about ordinary graph binary L on true Henson original indices, not about the numerical-H E parameter relation, complete upper L+ source assignment, or corrected B3.
11. **One-copy versus simultaneous front.** Independently realizing each desired new vertex is insufficient to guarantee one coherent macrodiary with the correct chronological E/free levels; a finite-stage induction and common labelled source orbit remain separate.
12. **Bounded J(T) support tests.** The exact criterion can be expressed using already verified \`finiteDirectedCliqueCapacity\` since \`finitePoolCliqueCheck_false_iff_capacity_lt\` proves its equivalence with \(\mathrm{cap}_E(S)<\ell-1\). This can support a future numeric H gadget certificate without reducing capacity to cardinality.

## Planned formal endpoints

- \`finiteNeighbourCliqueCheck_membership_iff_pool\`: exact equivalence between the executable complete-neighbour checker and finite directed clique-pool checker, assuming S⊆front.
- \`onePointLeftDense_realizes_exact_finite_neighbour_set\`: actual later original with precisely that whole neighbour set and zero intervening edges, under old-prefix K_\ell-freeness and OnePointLeftDense.
- \`henson_leftDense_realizes_exact_finite_neighbour_set\`: normalized Henson forbidden-family specialization with no separate old-prefix-freeness axiom.

All statements preserve original E, include the full finite old prefix, and impose no extraneous bound on |S|. Lean must pass full pinned project build and strict named transitive-axiom checks before merging; manuscript global B3/diary green markers remain pending.
