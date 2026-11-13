# One-step relative induced graph embedding in a fixed left-dense Henson graph

**12 November 2026 — English proof and adversarial audit BEFORE Lean.**

## Motivation

The previous two exact finite interfaces now available in \`lean-kk\` are (i) the true Henson one-point realization theorem of PR #87, given a complete safe old-neighbour pool, and (ii) finite induced-copy preservation of exact clique-freeness (stacked PR #90). Their composition provides a genuine **physical one-vertex extension of an existing finite induced copy**, rather than merely an abstract witness certificate.

## Statement in the ordinary Boolean graph language

Fix arbitrary directed Boolean ordinary-L tables A (finite target pattern, encoded on Nat) and E (the fixed actual graph). Fix ell>0, a finite set P of already represented abstract vertices, and a subset S⊆P describing which old abstract vertices the new target vertex n must see. Let f:Nat→Nat represent P as **distinct** genuine originals of E, with:

- f injective on P;
- every f(x), x∈P, lies below a cut front;
- for all distinct x,y∈P, **both orientations** of the existing graph table are exactly preserved: A(x,y)=E(f(x),f(y));
- A(x,n)=1 iff x∈S, and A(n,x)=A(x,n) for every x∈P (the new target vertex has a symmetric prescribed column);
- the abstract S is \(K_{\ell-1}\)-free in A, using the actual directed finite checker;
- the entire actual E-prefix below front is K_ell-free, and the fixed graph E has the explicitly stipulated \`OnePointLeftDense E ell\` property.

Then there exists a *genuine original index* \(v\ge\mathrm{front}\) satisfying:
\[
E(f(x),v)=A(x,n),\qquad
E(v,f(x))=A(n,x)
\quad\text{for all }x\in P.
\]
Moreover **every** old index \(z<v\) not belonging to f[P] is a nonneighbour of v in BOTH directions. Thus all intervening gaps and all old undesignated parameter/coding originals are zero, unless they have deliberately been included in P with their prescribed positive/negative bits.

This is an exact one-step induced extension over the entire *named* old pattern, and physically realizes the proposed new vertex. It does not yet extend a whole arbitrary finite pattern; iterating it requires maintaining the induced embedding and verifying the next target neighbourhood certificate at each step.

## English proof

1. The finite induced-copy transport theorem of stacked PR #90 applies to S⊆P, because f is injective on P and matches every off-diagonal A/E atom there. It transfers \(\neg K_{\ell-1}^A(S)\) to \(\neg K_{\ell-1}^E(f[S])\), exactly rather than by a cardinality shortcut.
2. Every f(x) for x∈S is below front by the named-old-vertex bound. PR #87's \`onePointLeftDense_realizes_exact_finite_neighbour_set\` therefore produces v≥front whose entire backward column equals the characteristic function of f[S] in both directions. It also automatically sets every intervening new gap edge to zero.
3. If x∈P, then
\[
f(x)\in f[S]\quad\Longleftrightarrow\quad x\in S.
\]
The reverse implication uses injectivity of f **on P** and the inclusion S⊆P. Thus E(f(x),v)=decide(x∈S)=A(x,n), and E(v,f(x)) equals the same bit, which is A(n,x) by the target symmetry premise.
4. If z<v and z∉f[P], then z∉f[S]. The exact full backward column from step 2 is false in both directed orientations. This finishes the full old-image/gap separation guarantee.

## Fixed Henson normalized-family specialization

The actual Henson forbidden-family avoidance, as verified in \`Kk.HensonLeftDensityAge\`, implies K_ell-freeness of every initial E-prefix. Therefore the generic result can be specialized without an additional \`hOld\` premise, under \`ell≥2\`, the actual normalized Henson avoidance and the fixed enumeration's \`OnePointLeftDense\` condition. No universality/left-density property is derived from mere K_ell-freeness. Both explicit physical/original indices and their backward complete columns are conclusions.

## Hostile audit

1. **Injectivity:** without injective f, two abstract distinct adjacent vertices might collapse, and the safe-neighbour clique test would not transport correctly.
2. **Induced atom matching:** preserving only positive A edges, but allowing extra E edges in f[S], can make an abstract safe S physically unsafe.
3. **Both ordered orientations:** the abstract target may be directed. We require its new column symmetric on P because the physical one-point realization always produces a symmetric new column.
4. **Safe S does not imply old E-prefix safe.** An old forbidden clique elsewhere in the fixed Henson enumeration is a separate obstruction to invoking one-point left-density. For normalized Henson E, the actual forbidden-family assumption supplies that prefix condition.
5. **S is a subset of P.** Without this inclusion, positive edges to previously unrepresented abstract vertices may be requested and the claimed gap-nonedge property would be false.
6. **P need not be an initial segment.** The theorem permits nonconsecutive old embedded originals. It explicitly turns off edges to all intervening old indices outside f[P], which is the correct chronological gap condition.
7. **No false surjectivity:** f need only be injective on P, not globally invertible or onto an old prefix. The finite reverse membership equivalence uses explicit image witnesses and local injection.
8. **New target index n:** the target A table need not be globally K_ell-free, but the new S must pass its exact (ell−1)-clique checker. If A is globally K_ell-free on P∪{n}, this safety is a further lemma, not assumed for free.
9. **Existing new-index isolation:** v≥front ensures f[P] lies below v. The extension output is the exact \`E(f x,v)\` and \`E(v,f x)\` bits; there is no claim v=front or that gaps are absent.
10. **Old parameter originals:** a parameter vertex requiring a prescribed positive link to v must be included in P; the theorem's conclusion explicitly forbids links to outsiders. Thus this is an ordinary-L extension primitive, not a full automatic Kpt parameter closure.
11. **No auxiliary E confusion:** \`A\` and \`E\` are ordinary directed Boolean L-edge tables, not the H+ Kpt E-incidence records.
12. **No unbounded resolved copy:** a finite one-step extension is not enough to show the entire chronological diary's mixed-neighbourhood certificates pass at every stage, nor that the common labelled inverse source orbit exists.

## Formalization order

(A) Prove the generic physical one-point extension by applying \`finitePoolCliqueCheck_false_iff_induced_image\` from PR #90 to S and then \`onePointLeftDense_realizes_exact_finite_neighbour_set\` from merged PR #87. Use the explicit finite image membership equivalence, not an unchecked simplifier. (B) Specialize to actual normalized Henson forbidden-family avoidance via \`hensonForbiddenFamily_no_prefix_cliques\` with ell≥2.

Register named transitive-axiom reports and require a complete exact-head hosted \`lake build\` with only \`propext\`, \`Classical.choice\`, and \`Quot.sound\` before merge. This theorem is a step toward relative finite pattern realization, not evidence of full numerical-H+ corrected B3 or the unconditional Ramsey characterization.
