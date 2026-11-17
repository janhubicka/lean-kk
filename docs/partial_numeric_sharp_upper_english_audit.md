# Track A — sharp universal upper bound at a physical partial numerical-H cut

15 November 2026. English proof and adversarial audit BEFORE Lean.

## Statement

Fix a symmetric original graph E, numerical height k, current
original b, partial cut g<=k, finite numerical carrier M and
any finite family of given later original top names j(t)>b.
For any nonempty admissible support U put

    P_U = {i<b : every E(i,j(t)) is positive for t∈U},
    S_U = {i∈P_U : E(i,b)=true},
    N_U = {z<hPosition(k,b,g) :
             every actual L_H(z,iota(j(t),k)) is positive for t∈U}.

Then the physical finite directed clique capacity obeys the
**sharp universal upper bound**

  cap_L(N_U)
     <= max(cap_E(P_U), min(g,1+cap_E(S_U))).

There is NO assumption that b is U-eligible. In the ineligible
case the already formalized stronger theorem says
cap_L(N_U)=cap_E(P_U). The formula above bounds eligible and
ineligible cases uniformly.

The matching LOWER inequality, which requires a constructed
literal generation staircase witness, is NOT asserted here.

## Proof

Let s be an actual largest directed L-clique inside N_U;
its existence and cardinality equality to cap_L(N_U) follow
from the checked finite capacity attainment theorem.

The exact physical common-neighbour pool theorem (#224) says
  N_U = Copies_k(P_U)
    union (if b has all U bits then {iota(b,q):q<g} else empty).
In particular every member of N_U lies in the *larger*
literal real pool
  Copies_k(P_U) union {iota(b,q):q<g}
and N_U is a subset of the true EVEN partial old prefix.

Case 1: s contains NO copy of current original b at
a generation m<g. Then every member of s lies in
Copies_k(P_U), by the exact pool decomposition. Thus
  |s|<=cap_L(Copies_k(P_U))=cap_E(P_U),
using the previously verified complete real-pool capacity.

Case 2: s contains a current-b copy v=iota(b,m) at
m<g. The physical generation-height lemma (#234) proves
  |s| <= g
by erasing v and injecting all other clique vertices
into distinct generations below m<g. Independently
the linked-original-image lemma (#235) proves
  |s| <= 1+cap_E(S_U)
because the remaining original-index image is a
genuine directed clique inside the neighbours of b.
Therefore
  |s|<=min(g,1+cap_E(S_U)).

In either case |s| is bounded by the displayed max,
hence the genuine physical capacity is too.

This is not a cardinality shortcut or a selected-shadow
age comparison: every positive edge is the literal
finite numerical-H binary L, with original indices and
generation gates treated precisely.

## Adversarial controls

1. U is nonempty; the exact physical common-pool theorem
   removes odd dummies only using this.
2. The current original b is a genuine original name, and
   the cut includes only q<g<=k, never its top q=k copy.
3. Any non-top current-b clique contains at most one copy
   of b, by true same-original L nonadjacency.
4. The maximal physical clique s exists for every finite
   N_U, including N_U empty; capacity then is zero.
5. s may entirely avoid current b, even if b is eligible.
   This is why cap_E(P_U) remains the FIRST max term.
6. If b is not U-eligible, no current copy enters N_U:
   exact equality cap_L(N_U)=cap_E(P_U) is already
   formalized in an independent predecessor.
7. g=0 forces the first case, giving the completed-block
   age equality. No fictitious b neighbour is introduced.
8. The original pool P_U need not be a clique, and
   original indices need not be consecutive.
9. The linked original capacity uses E(i,b)=true, not
   cardinality of P_U.
10. Strictly increasing non-top generations give the
    g-bound, not an arbitrary estimate from |P_U|.
11. The two upper estimates may be unequal; the
    correct combination is min, not max or sum.
12. Positive physical real-real edges project to
    original E edges in the matching ordered orientation.
13. The finite H binary L is total on Nat, so actual
    finite-carrier vertex membership still requires
    hPosition(k,b,g)<=M and selected top positions<M.
14. The theorem does not construct a staircase clique:
    equality of capacity requires a separately verified
    lower bound.
15. Nor does it ensure a chosen later original has the
    desired recursive prescribed E column; it quantifies
    over already given later original names.
16. No auxiliary Kpt E/(I1)--(I3)/(B3), labelled inverse
    source orbit or global BRD statement is proved.

## Lean acceptance

Add independent Kk/PartialNumericSharpUpper.lean importing
the exact physical pool and both independently formalized
physical upper lemmas. Use finiteDirectedCliqueCapacity_attained
to split on existence of a current-b generation in the
maximizing clique. In the no-current case apply capacity
monotonicity and the complete real-pool theorem; in the
current case apply both card <= g and
card <= 1+cap_E(S_U), then combine by Nat.le_min.

Require exact-head full Lake build, direct module compile
and strict qualified named standard-only axiom report.
This is a sharp universal UPPER only; do not mark the
equality/BRD upper bound green without the lower witness
and independent parameter-closed source proof.
