# Track A — exact physical critical-cut spectrum of one H block

22 November 2026. English-first proof and adversarial audit BEFORE Lean.
This composes exact-head Lean-verified and merged modules:
- Track A #460: sharp finite original Henson critical-generation set C_gen,
  `trackA_henson_raw_change_iff_critical_generation`;
- Track A/G #468: mapped physical critical cuts
  `trackAPhysicalCriticalCuts ell k E b j`, cardinal <=ell-2;
- Track A #479: complete literal numbered-H raw event iff at each
  non-top real cut `hPosition(k,b,g)`, and ordinary L odd neutrality.

## The exact physical spectrum theorem

Fix a genuine original normalized Henson K_ell-free graph E, ell>=2,
height k, current original b, arbitrary total finite carrier parameter
M, and given future top-original family j(t)>b.

Write C_gen(E,b,j) for the previous critical generation set; put

  C_phys = { hPosition(k,b,g) : g in C_gen, g<k }.

Let B_c denote the complete ordinary binary-L raw continuation age
over ALL numbered coordinates z<c, relative to the actual generated
H table and GIVEN later top-original positions.

**Theorem.** For any natural numerical coordinate c,

  c in C_phys
    iff exists g<k, c=hPosition(k,b,g)
         and B_(c+1) != B_c.

**Proof.** If c belongs to C_phys, its finite-image membership
gives g in C_gen, g<k and c=hPosition(k,b,g). Since g+1<=k,
the independently kernel-verified PR #479 exact
`trackA_henson_numeric_real_cut_change_iff_critical` gives
B_(c+1)!=B_c. Conversely, any such g and actual raw event
imply g in C_gen by the same iff; the finite filter/image definition
then places c in C_phys. This is literal generated finite H graph-L,
not a shadow age or selected-skeleton calculation.

The bound |C_phys|<=ell-2 was kernel-verified in PR #468, and the
present theorem proves that the exceptional set is EXACTLY the set
of ordinary-L raw-age event coordinates *among current b non-top
real-copy cuts*, not merely a set of possible numeric locations.

## All odd coordinates, not merely adjacent dummy cuts

**Theorem.** For arbitrary original directed E, without symmetry,
Henson freeness or positivity, any a>=0 and any given top original
family j, the complete raw support bound satisfies

    B_(2*a+2) = B_(2*a+1).

At the new old coordinate z=2*a+1 all actual numerical-H binary-L
crossing columns are identically false, by the fully verified
`finiteNumericH_odd_dummy_to_top_zero` (or its literal generator).
For every NONEMPTY support U, this z cannot belong to the
all-coordinate common old-neighbour pool. Hence adding z does not
change any actual common pool or its clique capacity. The verified
zero-column support lemma in #479 gives RAW equality, and
canonical and feasible normalized integer witness ages are also
unchanged by equality. This works at odd positions in every original
block, including those not represented by a specific non-top
generation g<k.

## Why this does not finish Kpt

The full Algorithm 5.4 uses auxiliary-dependent Kpt terminal I1,
same-component meet I2 and I3 monoid skip data. They are NOT
determined by equality of the ordinary binary-L raw or canonical
age at an odd cut. Even if the full ordinary event spectrum is
exactly C_phys on the non-top b-phase, the dependent defect set
D from merged #468 may contain genuine odd or other off-spectrum
cuts. The verified Track G zero-column bad-cut trichotomy and
pending odd specialization explicitly preserve terminal/meet/
missing-OLD-complete-socle obstructions.

No lower bound from BRD definition, common labelled inverse-source
orbit or uniform degree claim follows merely from the finite
ordinary-L spectrum.

## Hostile audit

1. The theorem compares true NUMERICAL cut c with the GEN index g
   only via hPosition(k,b,g) = 2*((k+1)b+g); no direct g=c assumption.
2. The generation boundary theorem compares prefixes at c and c+2,
   but the independently verified odd-neutrality lemma localizes
   its raw change to c->c+1.
3. Domain is g<k, so the current original TOP generation g=k and
   any later original blocks are OUTSIDE the asserted exact spectrum.
4. The theorem does NOT say there are no ordinary-L changes at
   non-top real cuts belonging to other original blocks.
5. The new universal odd-neutrality theorem is independent of
   Henson K_ell-freeness and of hPosition integer decomposition;
   its hypothesis is only the actual generator's zero odd L column.
6. Nonempty support U is indispensable: otherwise a zero column
   would not exclude the inserted coordinate from the empty
   intersection of old-neighbour sets.
7. The finite carrier M indexes the total generated Boolean table;
   to interpret a numerical coordinate as a genuine vertex
   in `EnumeratedPartialStructure` require a separate physical
   membership bound. Do not imply such membership from algebraic
   identities alone.
8. The marked top original family j may contain duplicates; the
   event iff and zero column hold for every named support.
9. Equality of raw functions implies equality of canonical ages
   and feasible weights but a nonsingleton raw change may be
   canonically redundant.
10. The exactness theorem does not assert graph-age COVER relation
    or adjacency in the canonical age order.
11. Full Kpt profile equality on a cut cannot be inferred from
    zero ordinary-L data, even for odd coordinates with corrected
    B3 safe: auxiliary E-free ends and missing old socle remain.
12. The bound ell-2 counts different genuine ordinary-L event
    numeric levels within a single b non-top phase, not all
    algorithmic interesting levels, not total selected levels.
13. The proof is a literal composition of prior kernel-verified
    lemmas, not an appeal to manuscript diary definitions.
14. Do not promote green manuscript marks or merge before the
    new source passes direct/full Lean and strict standard-only
    named axiom reports.

## Lean acceptance

New module `Kk/TrackAPhysicalCriticalSpectrum.lean`:
- `trackA_numeric_all_odd_raw_neutral`;
- `trackA_henson_physical_critical_cut_iff_actual_raw_event`.

Both under an isolated exact-head named axiom audit, direct build
and full Lake. Include the independent physical regression from
#479 or a lightweight new all-odd numerical check.
