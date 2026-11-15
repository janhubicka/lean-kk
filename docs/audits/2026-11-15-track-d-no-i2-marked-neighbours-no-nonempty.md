# Track D — nonempty-free closure-marked cut-neighbour transfer
15 November 2026. Additional English-first proof before the Lean endpoint.

## Problem
The existing verified
`henson_fullB3_of_no_i2_marked_closure_cut_neighbours` in
`Kk/B3ClosureFibreCoherence.lean` assumes an *independent*
`∃ v : Fin M, Marked v`, along with marked closure representation,
no-(I2), all cut-visible full names Marked, and marked corrected B3.
The marked-source nonemptiness condition is unnecessary if one uses
uniform cut-visible target coverage in the correct failure-first order.

## Precise statement
Fix a symmetric, loop-free, K_ell-free numerical-H base and a true
finite original list; fix cut<N and one set Z of actual Kpt closure
nodes. Let Full, Marked be arbitrary predicates on original names.

Assume:
(1) Every Marked original represents some genuine node in Z crossing
    the cut (the actual `closureSelectedOriginal` predicate).
(2) There are NO two same-component Z nodes whose meet has level cut
    (full no-(I2)).
(3) EVERY Full name that is cut-eligible and L-adjacent to the cut
    is Marked (including all auxiliary full parameter originals).
(4) The chosen Marked source passes corrected (B3).

Then the Full chosen source passes corrected (B3), even with no
independently supplied Marked source name.

## Proof
Let A be the actual numerical H, C=A.L, G the selected-stage Marked
prescribed data, and v any Full cut-eligible positive cut neighbour.
By (3), Marked v. The checked Lean theorem
`selected_named_nextL_permitted_of_no_I2`, under (1)--(2),
ensures that the COMPLETE next-cut ordinary-L reduct of v lies in
`G.PrescribedUpperLType`. This is a statement about G's *ACTUALLY
CHOSEN* upper output in its complete old-`L^+` source fibre; it is
not just membership of Marked v, and it controls all directed
old-to-upper L atoms.
The checked `partialTypeAt_lReduct_eq_ofAgeModel` identifies
this reduct with the physical L-type in the arbitrary age-test model,
thereby supplying uniform cut-visible coverage of the new lemma
`henson_fullB3_of_cut_visible_complete_outputs_no_nonempty`.
Apply that lemma and (4). No standalone source existence premise.

If Marked is empty, condition (3) implies no eligible Full name is
cut-adjacent. The separate actual finite no-neighbour lemma proves
Full (B3); there is no contradiction with the vacuity of marked B3.

## Hostile checks
- Requires actual marked Z-representation, not merely Marked subset of
  an arbitrary finite pool.
- No-(I2) prevents source deduplication choosing divergent next targets.
- Requires inclusion of ALL genuine full cut-neighbours, even q2
  auxiliary names. It is NOT known for general resolved diaries.
- The marked B3 test is the complete corrected one on real chosen
  outputs; it is not a selected age equality.
- No assertion of no-(I1) is needed for this B3 consequence, but
  full boringness needs separate structural I1 and I2 tests.
- No change to upper--upper edges or auxiliary E of an arbitrary
  ordinary-L forbidden witness.
- This theorem works whether Marked is empty or nonempty.
- Do not replace the 3-part proof by a selected shadow projection;
  K4 cut-10 explicitly invalidates that shortcut.
- No common labelled orbit is constructed.
- Must compile the actual successor-tree prerequisite and list
  the exact theorem in the strict report.

## Impact
This repairs an artificial nonemptiness obligation in the *finite*
closed-source transfer, and gives a clean proof order for the small
independent case: classify the physical cut-visible names; exclude
the structural (I2) competing meet; obtain genuine chosen upper-type
coverage from represented Marked originals; then transfer marked B3
to full B3; and finally verify no (I1). None of the application-specific
classification or structural verifications is asserted here.
