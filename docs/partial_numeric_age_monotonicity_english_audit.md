# Track A — monotonicity of the ACTUAL old age along partial block cuts

15 November 2026. English mathematics and adversarial check **before Lean**.

## Precise statement

Fix numerical-H height k, original b, finite carrier M and a family
j(t) of given later original top names. For a given admissible NONEMPTY
support U, define the true actual old common-neighbour pool at the
cut before generation g of original b by

  N_g(U) = { z < hPosition(k,b,g):
             L_H(z,hPosition(k,j(t),k))=true for every t∈U }.

For any g<=h (and in particular 0<=g<=h<=k),
  N_g(U) subset N_h(U).

Thus every directed clique in N_g(U) is also one in N_h(U),
and for the true numerical-H old graph L,
  cap_L(N_g(U)) <= cap_L(N_h(U)).

Consequently the genuine *raw* graph-age bounds computed
from these **actual** complete old binary crossing columns satisfy
  Raw_h(U) <= Raw_g(U).
This is an inequality of natural truncated subtractions, not
a claim that either arbitrary column family is a genuine
positive graph age.

## Proof

The numerical position of original b's q-th generation is
  hPosition(k,b,q) = 2*((k+1)*b+q).
For fixed k,b this increases with q; therefore
  [0,hPosition(k,b,g)) subset [0,hPosition(k,b,h))
whenever g<=h.

For every physical coordinate z in the smaller prefix, the
tested complete typed future column
  L_H(z,hPosition(k,j(t),k))
is a function of z,t and the given E,k,M,j only: it does **not**
depend on the prefix cutoff. Consequently membership of z in
the intersection of all positive U-neighbour conditions is
preserved after enlarging the old prefix. This proves
N_g(U) subset N_h(U).

Every directed clique in the smaller pool remains a directed
clique in the larger pool under the SAME actual L table.
The checked generic finiteDirectedCliqueCapacity_mono
proves the capacity inequality. Finally the raw graph-age
value is ell-1-cap_L(N_g(U)) in natural truncated subtraction,
so the inequality reverses. The g=0 endpoint is exactly the
completed-block actual old-age theorem already proved in
FullBlockActualAge: for later j(t)>=b, the full earlier
original-block old age equals the original old age. Hence
for 0<=g<=k, the partial-prefix actual raw bound is
pointwise <= the original old age, without assuming
all partial capacities equal the original one.

## Adversarial checks

1. The same numerical-H L table and same given future originals
   are used at both cutoffs. The statement is not a comparison
   between different Henson graphs or changed future label families.
2. The proof quantifies over entire physical old prefixes,
   including odd dummies; no selected shadow approximation.
3. Raw age bounds use **maximum cliques**, not numbers of
   common-neighbour vertices.
4. No nonedge preservation across different structures is
   needed because both pools are subsets of one fixed L table.
5. Natural truncated subtraction reverses weak inequalities.
6. Equal raw ages are permitted; monotonically advancing the
   cutoff need not force a strict age change at every generation.
7. g=0 is the completed earlier-original block, for which the
   existing exact original-age equality applies.
8. g<=h<=k is the physically intended partial-block regime.
   The pool inclusion itself holds even for arbitrary g<=h.
9. The result is independent of original graph symmetry,
   unless invoking the earlier completed-block baseline,
   which assumes original symmetry.
10. The support U must be nonempty only to use the
    IntegerGraphSupport age API and the prior complete-block
    theorem; simple pool inclusion works for arbitrary U.
11. The original-to-top column is the TRUE finiteNumericHL
    binary relation, not a chosen pullback c.
12. Nothing guarantees an arbitrary prescribed full recursive
    stage will realize the given future top names.
13. The age bound may be a raw nonpositive/degenerate object;
    do not silently treat it as a graph-age lattice element
    without the relevant consistency/positivity checks.
14. The conclusion does not classify exactly WHEN the
    capacity increases: that still requires the sharp
    non-top staircase formula, under independent formalization.
15. A monotone selected-front age is not a proof that the full
    parameter-closed (I1)/(I2)/(I3)/(B3) event is boring;
    auxiliary E source data may change even at raw equality.
16. No global infinite resolved diary or common labelled orbit
    is inferred.

## Lean acceptance

Implement Kk/PartialNumericAgeMonotonicity.lean with:
- all-support literal common old-pool inclusion;
- maximum directed clique capacity inequality under this inclusion;
- raw actual old age antitonicity;
- comparison of every partial age (g<=k) with the
  original completed previous-block raw age.

Report fully qualified axioms for each declaration, require
direct Lean module build, strict standard-only named audit,
and full repository build. Stack on the previous common-pool
PR and keep DRAFT until all dependency heads pass. No green
global manuscript claim is justified.
