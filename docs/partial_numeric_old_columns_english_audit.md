# Track A — partial numerical-H original-block prefix, physical columns and sharp capacity

15 November 2026. Mathematical proof **before** Lean; hostile checks and
independent finite regression of the sharp capacity formula.

## The obstruction to a complete-block shortcut

A completed numerical-H original block has *all* top-generation
copies of previous originals, so its old L age equals the original
graph age. A cut inside the current original block is different.
Let k be the H height, b the current original and 0<=g<=k. We
take the literal numbered old prefix

    Pnum = [0, hPosition(k,b,g)),  hPosition(k,i,q)=2*((k+1)*i+q).

This cut excludes generation g and higher of original b; it does
not omit any numbered odd dummy coordinates. Its exact partition is

    Pnum =
       (all real generations q<=k of every i<b)
        UNION (real generations q<g of original b)
        UNION (all odd numbers in Pnum).

The three pieces are pairwise disjoint. Call the union of the
two real pieces Real(b,g). If g=0 the second real piece is empty,
recovering the complete-block result. The case g=k+1 is not
included: at g=k+1 the current b *top* is present and top-top
L edges allow an additional clique, so the non-top formula
below is not valid without a separate case.

## Exact ACTUAL old-to-future top columns

Fix symmetric original graph E and any finite family j(t) of
future original names with b<j(t) for every future sort t.
For every numeric old z in Pnum, define its pulled-back column
Col(z,t) as E(i,j(t)) if z is real generation copy of a
partially/fully included original i, and zero on all odd dummies.

The actual finite numerical H binary L has for EVERY z in Pnum:

    L(z,hPosition(k,j(t),k)) = Col(z,t)
    L(hPosition(k,j(t),k),z) = Col(z,t).

Proof: any real z is iota(i,q) with i<=b and q<=k.
Because i<=b<j(t), the older-real-to-later-top H gate is
open, including negative original bits; symmetry gives the
reverse orientation. If z is odd, both actual L atoms are
zero by the established odd-to-top lemma. This identifies
the true actual old future column, not a chosen abstract one.

For any nonempty support U, odd dummy z cannot satisfy all
future column tests. Consequently the complete real pool
Real(b,g) contains EXACTLY the whole old common-neighbourhood,
and the raw old age can be computed using that real pool
(with genuine finiteNumericHL old edges) without omitting
a physical common-neighbour witness.

## Sharp mixed-generation clique capacity

For any nonempty support U let
  A_U = { i<b : E(i,j(t))=1 for all t in U },
  eligible(U) = for all t in U, E(b,j(t))=1,
  S_U = { i in A_U : E(i,b)=1 }.

Write cap_E(X) for the maximum size of a directed E clique
contained in X. The maximum size of an actual binary-L clique
in the full old common-neighbourhood at the partial cut is

  cap_num(U)
    = max(cap_E(A_U),
          (if eligible(U) and g>0
           then min(g, 1+cap_E(S_U))
           else 0)).

This is valid for 0<=g<=k. It does NOT assert a canonical
single-support cover or a boring auxiliary level.

Upper bound: A numerical clique contains at most one real copy
of b, because L requires distinct originals. If it contains
none, the known real-generation clique projection is injective
and its original image is an E clique in A_U, of size <=cap_E(A_U).
If it contains b at generation m<g<=k, all earlier real
members in the clique must have generation STRICTLY below m:
their pair with b cannot use the top-top exception.
The earlier clique's generations are themselves strictly
increasing in original-name order, so with a earlier members
we have a<=m<g. Their original names form an E clique in
S_U, so a<=cap_E(S_U). Thus the total is
<=min(g,1+cap_E(S_U)). Odd dummies cannot belong to a
nonempty-support old common-neighbourhood.

Lower bound: top-generation copies of an original E clique
attaining cap_E(A_U) realize the first term. If b is eligible
and g>0, choose a clique in S_U of size
a=min(cap_E(S_U),g-1). Ordered increasingly by original index,
give its a members successive generations 0,...,a-1 and
give original b generation a<g. Every pair meets the genuine
strictly-increasing H gate and an original E edge, so this
is an actual L clique of size a+1. This realizes the
second term.

In particular the complete-block equality at g=0 is recovered;
for g>0 this new term is the *partial witness capacity*.
For g=k+1 the b top generation is present, enabling the
top-top gate; a different formula applies and should be
recovered from the completed-block theorem for b+1.

## Concrete counterexample to the false full-block extrapolation

Take original graph on vertices 0,1,2 with all three original
edges, k=2, b=1, g=1 and a single selected future top j=2.
Both earlier original 0 and partially present original 1
are common neighbours of the selected type. Their ORIGINAL
capacity is 2; however old real copies of 1 appear only in
generation 0, and cannot be adjacent to any earlier real copy
of 0. Thus the actual old numeric capacity is 1, not 2.
With ell=4 the raw old bound is 2, whereas applying the
false completed-block shortcut would give 1. At g=2 one
can take 0 at generation 0 and 1 at generation 1, and the
actual capacity rises to 2.

## Adversarial checklist

1. Do not identify a partial prefix with the complete original prefix b+1.
2. g=0: no current-original real copy is present.
3. 0<g<=k: only non-TOP generations of b are present.
4. g=k+1: excluded from the sharp partial formula; top-top exception.
5. Height k=0: only g=0 is admissible; use the completed-block theorem.
6. Same-original copies never form positive L pairs.
7. Only one current-original copy enters a positive clique.
8. Every earlier copy adjacent to non-top current b has q<m.
9. Among earlier copies in a clique q's strictly increase, not merely differ.
10. Top copies of all earlier originals are still available and
    give the full cap_E(A_U) independent of the current partial block.
11. The earlier clique with the current b must lie in S_U,
    not just A_U; do not replace its cap by its cardinality.
12. If the current b is not common to every sort of U,
    none of its partial real copies contributes.
13. U must be nonempty, otherwise odd dummy coordinates survive.
14. E symmetry is needed for graph interpretations and reverse
    top crossing bits; original graph loop-freeness is customary.
15. Future original names must be strictly later than b.
16. The Boolean L relation is total on Nat; carrier membership
    needs hPosition(k,b,g)<=M and future top positions <M.
17. The formula is an ordinary-L relative old age, not an
    actual proof of admissibility of the next selected original.
18. Auxiliary Kpt E/parameter closure and full corrected (B3)
    may distinguish levels with identical ordinary-L ages.
19. The finite graph-age state need not be a genuine positive age
    for arbitrary prescribed future columns; raw equality is
    valid and can be canonicalized separately.
20. No global resolved diary, labelled orbit or BRD is deduced.

## Independent verification and implementation

An independent brute-force interpreter of the literal H generator
checked the partial real common-neighbour set and the sharp
capacity formula over all 64 simple graphs on four originals,
k=0,1,2,3, every valid b=0,1,2, all partial cuts
0<=g<=k, both future names chosen strictly later and all
three nonempty two-sort supports: **26,880 cases passed**.
It did not import graph-age/diary definitions from the manuscript.

Lean implementation should proceed in two stages:

A. Full literal partial-prefix partition; actual both-direction
old-to-later-top physical columns; equality of complete numbered
and real-pool old common-neighbourhoods at every nonempty support.
This module is a meaningful intermediate proof and should pass
direct build/strict axiom gate before any manuscript green mark.

B. Sharp capacity formula above, with the non-top generation
counting argument and a constructed staircase witness. Verify
its exact mathematical statement and new independent finite
regression before integrating. This theorem is *not* inferred
from A or the existing reserved-complete-clique formula alone.
