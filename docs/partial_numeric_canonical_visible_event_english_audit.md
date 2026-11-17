# Track A — exact *canonical-visible* raw support events, 17 November 2026

English-first mathematical proof and adversarial audit BEFORE Lean.

## The two independently checked inputs

1. The normalized integer-witness canonicalizer is the finite supremum
   of all bounded clique-weight vectors w satisfying the given full
   support-bound system B. The kernel theorem
   `integerGraphAgeCanonical_preserves_clique_vectors` says exactly
   that w respects B iff w respects G_B; it does *not* demand that
   B is already an admissible positive graph age.
2. The verified and merged Track A raw physical event theorem
   [PR #284](https://github.com/janhubicka/lean-kk/pull/284),
   exact-head CI 44040233653, says Raw_h(U)<Raw_g(U)
   precisely when b is U-eligible, c_U=p_U,
   g<=p_U<h, and p_U<ell-1; every such raw decrease is one unit.
   Physical raw age antitonicity is separately verified and merged.

## General finite-witness equivalence

For ANY two raw bound functions B_new<=B_old on every
`IntegerGraphSupport d ell` (no positivity or genuine-age
hypothesis), the canonical graph ages differ if and only if

  there exists w : IntegerCliqueWeights d ell
  such that w respects B_old on ALL supports,
  but w does NOT respect B_new on some support.

Proof (⇒): If no such w exists, the two raw bound systems admit
the same normalized clique weight vectors: feasibility for B_new
implies feasibility for B_old by B_new<=B_old, and absence of a
lost witness implies the converse. The two finite sets over
which `integerGraphAgeCanonical` takes the pointwise supremum
are literally equal. Hence their canonical functions equal.

Proof (⇐): If w is feasible for B_old but not B_new, the
canonicalization preservation theorem implies w is feasible
for G_{B_old}, but infeasible for G_{B_new}. If the two
canonical functions were equal, this is impossible.

This directly separates a raw-bound change from a *visible*
canonical change: the latter must remove at least one
actual normalized integer clique vector.

## Exact physical iff: one saturating vector

Fix symmetric original E, numerical height k, original b,
g<=h<=k, the SAME M and GIVEN later top original family j(t)>b.
Write Raw_g, Raw_h for actual numbered-prefix ordinary-L raw
age against j(t), and C_g=G_{Raw_g}, C_h=G_{Raw_h}.
For each nonempty admissible support U set

  P_U={i<b : all E(i,j(t)) positive for t in U},
  S_U={i in P_U : E(i,b) positive},
  p_U=cap_E(P_U),   c_U=cap_E(S_U),
  eligible_U : all E(b,j(t)) positive for t in U.

Then **C_h≠C_g if and only if** there are
w : IntegerCliqueWeights d ell and
U : IntegerGraphSupport d ell such that:

  (a) w satisfies *every* earlier raw support bound Raw_g;
  (b) integerCliqueOnSupport(w,U) = Raw_g(U);
  (c) b is U-eligible;
  (d) c_U=p_U and g<=p_U<h;
  (e) p_U<ell-1.

The correct object witnessing a visible age change is thus
an OLD-feasible **complete** normalized multiplicity vector
that SATURATES the exact raw U-bound which subsequently falls
by one.

Proof (⇒): Use the general finite-witness equivalence to find
old-feasible w that is no longer feasible. Failure of feasibility
produces some U with value(w,U)>Raw_h(U).
Old feasibility implies value(w,U)<=Raw_g(U), so
Raw_h(U)<Raw_g(U). Apply the kernel-checked physical raw
event iff to obtain (c)--(e), and its one-unit theorem to see
Raw_g(U)=Raw_h(U)+1. These two inequalities force
value(w,U)=Raw_g(U), proving (b).

Proof (⇐): From (c)--(e) use the physical raw event iff and
one-unit result to obtain Raw_g(U)=Raw_h(U)+1. The saturation
(b) makes w violate Raw_h(U); (a) says it remains feasible
at the previous cut. Apply the general finite-witness
equivalence to deduce C_h≠C_g.

This is an exact criterion for **ordinary-L canonical AGE
DISTINCTION**, not merely a necessary condition; it does not
assert that C_h covers C_g in the age poset, nor that there
is any full parameter-closed (I1)--(I3)/(B3) event.

## Adversarial checks

1. Raw_new<=Raw_old on every admissible nonempty support is
   essential for orienting the lost-witness iff; without it
   the feasible-set difference can go the opposite way.
2. The canonicalizer is a finite witness supremum, so equal
   feasible sets imply equal canonical functions even when
   raw B is nonpositive or degenerate.
3. Canonicalization preserves the entire normalized feasibility
   system, not merely one selected support.
4. The witness w must satisfy the OLD bounds on *all* supports.
   A single coordinate saturating Raw_g(U) with no global
   feasibility certificate cannot force a canonical change.
5. No assumption that raw ages themselves are genuine graph
   ages is introduced.
6. A failed new inequality supplies a support U only because
   WitnessRespects is a universal condition over supports.
7. A physical raw event is exactly one unit (the PR #284
   theorem), so the lost witness saturates the old bound;
   for a multiple-unit raw decrease the saturation conclusion
   would be false.
8. Eligibility is essential; an ineligible current b cannot
   introduce the requisite physical U-capacity increase.
9. c_U and p_U are CLIQUE capacities, not |S_U| or |P_U|.
10. The threshold g<=p_U<h includes g=h as impossible,
    so equal cuts cannot produce a false canonical event.
11. p_U<ell-1 excludes age bounds already saturated at zero.
12. The same actual numerical-H binary table and same j(t)
    are used at both cuts; no independently reselected
    future original family is being compared.
13. Odd fake coordinates remain in the physical old prefix,
    but their ordinary-L U-crossings are zero; no full
    auxiliary Kpt source conclusion is inferred.
14. The supports U must be nonempty and size-bounded by ell-1;
    using the empty support would change the literal pool.
15. The normalized weight domain includes all bounded total
    clique vectors, not just counts realized in one chosen
    future set W.
16. Even an ordinary canonical age difference need not be
    a COVER: several support constraints may change at once.
17. The actual recursively prescribed Henson schedule, full
    dependent Kpt E/(B3) and labelled source orbit still
    require independent Lean/English proofs.

## Validation acceptance

Implement `Kk/PartialNumericCanonicalVisibleEvent.lean`
English-first, export (i) general canonical mismatch iff
an old-feasible lost vector, and (ii) the exact
physical saturating-vector criterion. Require standalone
exact-head Lean compile, fully qualified named standard-only
axioms, full Lake build and the existing independent
197,120-case actual raw transition regression.

Do NOT add a green canonical-visible marker until these gates
pass; do NOT promote global BRD or auxiliary (B3) statements.
