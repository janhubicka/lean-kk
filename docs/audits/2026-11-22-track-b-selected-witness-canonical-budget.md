# Track B — Exact canonical-age preservation after inserting finite selected witnesses
22 November 2026. English proof and 16 hostile checks BEFORE Lean.

## Theorem

Fix the original graph E, forbidden clique parameter ell, future sort
number d, complete future passing columns c(p,t), and finite original
vertex sets P⊆Q. Let B_P and B_Q be the TRUE full original old-neighbour
raw integer graph-age bounds. Put F=G(B_P) and assume F is a genuine
positive normalized integer graph age: IsIntegerGraphAge d ell F and
F(U)>=1 for every admissible nonempty support U.

Then

  G(B_Q)=F    iff    for every admissible nonempty U,
  cap_E({q∈Q: c(q,t)=1 for all t∈U}) + F(U) ≤ ell−1.

This includes Q=P∪W for ANY finite set W of newly protected actual
selected/top/coding originals with arbitrary positive future columns.
Nothing requires W to be isolated or independent from P or internally.

## English proof

Because P⊆Q, for each U its common old-neighbour pool grows
N_P(U)⊆N_Q(U), so its clique capacity does not decrease. The literal
raw bound B_R(U)=ell−1−cap_E(N_R(U)) uses truncated Nat subtraction,
therefore B_Q≤B_P. Monotonicity of normalized integer-witness
canonicalization gives G(B_Q)≤G(B_P)=F.

Conversely, since F is a genuine age, greatest-age-below-raw
establishes F≤G(B_Q) precisely when F≤B_Q. Under positivity F(U)≥1,
the latter inequality at U is *equivalent* to
cap_E(N_Q(U))+F(U)≤ell−1. Indeed, if truncated subtraction were
zero then F(U)≥1 would make F(U)≤B_Q(U) impossible; otherwise Nat
arithmetic gives the stated sum bound. The reverse direction holds
for arbitrary nonnegative capacities. Thus the all-support budgets
give F≤G(B_Q), and the already proved opposite bound gives equality.

For necessity, equality G(B_Q)=F and canonicalization-below-raw
give F≤B_Q. Positivity eliminates the Nat-subtraction pitfall,
yielding the same sum inequalities.

Notice this is a TRUE canonical-age criterion. It does NOT claim
B_Q=B_P: redundant raw bounds may decrease without affecting
the allowed normalized clique vectors. Nor does it assume separate
singleton budgets suffice; ALL supports are necessary.

## Hostile audit

1. F must be a genuine integer-witness normalized graph age; mere
   pointwise nonnegative raw data cannot invoke greatest-age.
2. F must be positive on every tested support. Without this, Nat
   truncated subtraction makes necessity false when capacity≥ell.
3. The underlying graph E is exactly the SAME at both cutoffs.
4. P⊆Q is essential to the monotonicity G(B_Q)≤G(B_P).
5. Q may contain former *top future* coding witnesses; their real
   mutual E-edges are included in cap_E(N_Q(U)).
6. Their passing c(q,t) columns may be nonzero, so a blanket
   zero-tail/boringness argument is invalid.
7. No raw equality B_P=B_Q is inferred: we compare canonical ages.
8. Every admissible support U is checked, including mixed supports
   of size 2 or 3. Singleton-only checks are insufficient.
9. No assumption of original graph symmetry or looplessness is
   required for this finite algebraic identity; literal directed
   clique capacity is used.
10. Adding Q vertices that were previously tagged top witnesses is
    not automatically age-neutral, even if they were individually
    legal future vertices in the earlier finite universal stage.
11. Concrete K4 counterexample: one future sort, old P={p},
    positive c(p)=1, so cap(N_P)=1 and F({t})=2. Add a former future
    witness q with E(p,q)=E(q,p)=1 and positive c(q)=1. The enlarged
    old neighbour pool is an edge of capacity 2, so G(B_Q)({t})=1.
    The witness was individually legal but age neutrality fails.
12. The theorem is conditional on actual complete columns and
    graph-age positivity. It does not CONSTRUCT those columns.
13. The all-support budget is a finite exact condition and suitable
    induction invariant for a coherent protected-witness construction,
    but it has not been proved for the proposed resolved Q diary.
14. Even canonical age equality does not imply equality of the
    dependent Kpt full old/upper L+/E source or corrected B3
    parameter-closed microevent tests.
15. There is no common labelled inverse-source orbit, total I/F
    transport or unbounded resolved copy conclusion.
16. This specializes existing canonicalization monotonicity and
    greatest-age theorems; no new combinatorial axiom is introduced.

## Required next proof

For the prescribed finite diary macro-step, construct one complete
protected passing column c on old+earlier selected witnesses such
that the displayed full-support budgets hold for all required
neutral intervals, and check the full Kpt source profiles there.
This closes an actual existence obligation, rather than just
rewriting it as numerical inequalities.
