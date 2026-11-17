# Track A — a canonical ordinary-L age change has a physical raw support certificate

17 November 2026. English mathematics and hostile audit BEFORE Lean.

## Statement

Fix the SAME symmetric original Boolean graph E, numerical-H height k,
current original b, finite Boolean carrier bound M, given original top
names j(t)>b, and two partial generation cuts 0<=g<=h<=k.

Let Raw_x be the ACTUAL ordinary-L old raw graph-age function
at cut hPosition(k,b,x) against these given top originals, defined
on all nonempty admissible IntegerGraphSupport d ell.
Let C_x=integerGraphAgeCanonical d ell Raw_x.

The new theorem is strictly ONE WAY:

  C_h != C_g  =>
  there exists a nonempty admissible support U with
    (i)   b U-eligible (all E(b,j(t)) bits positive);
    (ii)  cap_E(S_U) = cap_E(P_U) = p_U;
    (iii) g <= p_U < h;
    (iv)  p_U < ell-1 (no natural subtraction saturation).

P_U is the earlier ORIGINAL U-common-neighbour pool,
S_U={i in P_U : E(i,b) true}. The criterion is precisely
the genuine RAW change theorem being independently checked in
Kk/PartialNumericRawSupportEvents.lean (stacked parent PR #284).

## English proof

The old raw support bounds are pointwise antitone with respect to
the actual numbered old prefix (verified PR #228). Thus

     Raw_h(U) <= Raw_g(U)

for every admissible nonempty support U.

Suppose NO U satisfies the displayed four conditions.
The independent physical raw change iff then implies that no
support satisfies Raw_h(U)<Raw_g(U).
By antitonicity, Raw_h(U)=Raw_g(U) for all U.

Therefore Raw_h=Raw_g by function extensionality. Applying the
deterministic integer-witness canonicalization gives
C_h=integerGraphAgeCanonical(Raw_h)
   =integerGraphAgeCanonical(Raw_g)=C_g,
contradiction.

Equivalently, any distinct canonical values require at least one
strict raw support decrease, which has the exact physical
eligibility, linked-capacity and height threshold certificate.

No handwavy assertion about a full auxiliary B3 or the minimal
envelope is needed.

## Adversarial checks

1. E,k,b,M,j and U are FIXED across the two cuts. Comparing
   independently chosen original top names is outside the theorem.
2. The actual numeric old-prefix pools include all intervening
   odd fake coordinates; their ordinary-L crossing zeros are
   included in the kernel result. No selected-shadow substitution.
3. The statement holds for all admissible nonempty U, not just
   singleton supports; this is what makes the extensionality
   argument valid for full graph-age canonicalization.
4. C_x is the existing deterministic integer-witness canonicalizer;
   no assumption that an arbitrary raw reference table is already
   a genuine positive age.
5. If g=h, the canonical ages are definitionally equal, and the
   conclusion is vacuous because g<=p<h is impossible.
6. If there are no nonempty admissible supports (e.g. some
   degenerate d/ell), the antecedent is false: the total raw
   functions are equal on their empty domain.
7. A U-eligible b can cause at most one raw support decrease
   within the block and only when c_U=p_U and the cuts straddle
   p_U+1. This threshold may lie outside h<=k.
8. Capacity jumps at a saturated raw zero do not produce
   strict raw age changes; p_U<ell-1 is essential.
9. The statement does NOT say that any qualifying raw event
   forces a canonical-age change: the raw U-constraint may
   be redundant under other support inequalities.
10. It does NOT say that any canonical-age change is a cover
    in the graph-age lattice; multiple supports can change
    at the same generation and changes can be coupled.
11. Even a genuine selected-front canonical-age cover is
    not yet the full parameter-closed (I1)--(I3)/(B3)
    event, because auxiliary Kpt E records can change
    independently.
12. The result does not construct the given later original
    top names with arbitrarily prescribed E columns in
    the left-dense Henson enumeration.
13. The Boolean relation age is M-independent, while actual
    finite carrier membership still needs numeric cutoff
    hypotheses; neither is silently inferred.
14. No cross-occurrence labelled source or global BRD count
    follows from an existing finite raw-event witness.

## Lean acceptance

Implement a standalone `Kk/PartialNumericCanonicalEventWitness.lean`
stacked on the raw physical event iff:
- a total abbreviation for the ACTUAL raw physical old age;
- the one-way canonical-age-inequality implies existence of
  U satisfying the verified raw change criterion;
- use only PR #228 physical raw age antitonicity,
  parent PR #284 physical raw event iff, function extensionality
  and canonicalization congruence.

Exact-head direct module build, qualified standard-only axiom
gate, and full Lake build are required. No new manuscript
green mark or canonical cover claim until checked.
