# Track A — actual full-block old numerical-H columns to later selected tops

**15 November 2026. English proof and adversarial audit before Lean.**

## Exact statement

Fix numerical height k, old completed original-block prefix [0,b), symmetric
original E and a finite family j(t) of future original names with b<=j(t).
Define prescribed old-original columns c(i,t)=E(i,j(t)).
For every actual numbered H old coordinate z<hPosition(k,b,0), the
genuine finite numerical H ordinary binary L crossings in BOTH
ordered orientations are exactly the complete old column
Col(z,t)=numericHFullBlockOldColumn(k,b,c)(z,t):

  L_H(z,iota(j(t),k)) = Col(z,t)
  L_H(iota(j(t),k),z) = Col(z,t).

This is for the true finiteNumericHL binary table, not an abstract
invented graph. To interpret addresses inside a physical finite
carrier additionally require hPosition(k,b,0)<=M and
hPosition(k,j(t),k)<M; Boolean table identity is independent of M.

## English proof

Use the proved numericH_full_block_prefix_exact to partition the old
numeric prefix into all real coordinates iota(i,q) with i<b, q<=k
and all odd fake coordinates 2*a+1.

In the real case, i<b<=j(t). The genuine numerical-H generator gate
from an older real generation q to a strictly later top generation k
is open (q<k or q=k). By
numericH_older_generation_to_top_exact, the true forward L bit
is E(i,j(t)), including negative bits. By
henson_finiteNumericH_binary_symmetric, symmetry of E gives the
same true reverse L bit. By numericH_full_block_real_column
the pulled-back column is E(i,j(t)). Compose.

In the odd case, z=2*(z/2)+1 by Nat.mod_add_div and the parity
hypothesis. finiteNumericH_odd_dummy_to_top_zero says that the
two true L bits to the top are false. By
numericH_full_block_odd_column the proposed complete old column
is false. Compose.

The proof uses only a finite completed original-block cut, and does
not assert existence of the j(t), satisfaction of an entire prescribed
stage schedule, or any full auxiliary Kpt E/(B3) property.

## Fourteen adversarial controls

1. Intermediate reserved-generation cuts are excluded.
2. Original indices are not assumed consecutive.
3. Height k=0 and arbitrary k are covered.
4. b=0 has empty numbered old prefix.
5. Both positive and negative old bits are transported.
6. Reverse crossings explicitly use original symmetry.
7. Odd fake vertices can still carry auxiliary Kpt E incidences.
8. No imaginary old numeric coordinate is omitted.
9. The gate is checked for any q<=k to top k, not q-to-q.
10. Physical carrier needs extra old/top cutoff bounds.
11. The future original names are GIVEN, not constructed by left density.
12. Distinct future sorts need not choose distinct top originals.
13. The raw/canonical age equality needs a full column match, not
    only matching selected-front shadows.
14. No claim about unbounded recursive realization, mixed old
    neighbourhood safety, full source, labelled orbit or BRDs.

## Lean acceptance

Add independent Kk/FullBlockActualTopColumn.lean importing the
verified numeric prefix and binary crossing lemmas. Print its named
axioms; demand direct module build, exact-head fully qualified
standard-only axiom audit and full repository build. Source-exact
manuscript markers only after this acceptance gate; no new global
resolved-copy status.
