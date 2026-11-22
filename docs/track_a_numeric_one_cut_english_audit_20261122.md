# Track A — actual one-NUMERICAL-cut ordinary-L event, not merely generation-boundary age

22 November 2026. English FIRST and adversarial audit before Lean.
This repairs a genuine coordinate issue in applying the already
verified generation-index critical set of Track A #460 to individual
numerical-H Algorithm 5.4 cut coordinates.

## Coordinate data

The numerical H construction of height k places the q-th copy
of original b at the actual even coordinate

  c = hPosition(k,b,q) = 2*((k+1)*b+q).

Consequently

  hPosition(k,b,q+1) = c+2.

The intervening coordinate c+1 is an ODD fake H coordinate.
The verified lemma `finiteNumericH_odd_dummy_to_top_zero`
states that its actual binary L crossing bits to every named later
top original are zero in BOTH directions, irrespective of H+ E.

For a fixed given family of later original top names j(t)>b, define
the full literal raw continuation support function at an ARBITRARY
numeric cutoff a by

  B_a(U) = ell-1 -
           cap_L({z<a: for every t in U, L(z,top(j(t)))=true}),

for nonempty admissible support U. This uses ALL literal numbered
old coordinates, not only the real-copy shadow. The old generation
bound `Raw_g` of #460 is exactly `B_(hPosition(k,b,g))`.

## Lemma 1: zero-column extension

Let P be any finite old coordinate pool and z a new coordinate whose
old-to-future column is zero on EVERY named sort t. On a nonempty
support U, choose t0 in U. Since the column at z is false at t0,
z cannot belong to the U-common-neighbour pool. Therefore

  common(P union {z}, U) = common(P,U),

even if z was already in P. Consequently the actual raw support
bound and canonicalized integer graph age do not change.
No symmetry, graph freeness or positivity hypothesis is required
for this elementary zero-column lemma.

## Lemma 2: odd dummy is raw/canonically neutral

Take c=hPosition(k,b,g), with no need to assume g<k for the
algebraic total generated L table. The actual crossing column from
z=c+1 to all given later top originals is zero. Applying Lemma 1
to P=[0,c+1) shows

  B_(c+2) = B_(c+1).

The entire raw support functions agree, hence their canonical ages
and feasible normalized clique multiplicity vectors agree. The
proof uses literal `Finset.range_succ` and the actual odd-H
zero-column theorem, not an axiomatized source shadow.

## Theorem 3: exact one-numerical-cut event

Assume genuine original Henson K_ell-freeness, ell>=2, symmetry
derived from the forbidden family, given later originals j(t)>b,
and g+1<=k. Put c=hPosition(k,b,g).

By the exact identity c+2=hPosition(k,b,g+1), the old verified
critical-generation iff of Track A #460 and Lemma 2 give

  B_(c+1) != B_c
      iff B_(c+2) != B_c
      iff Raw_(g+1) != Raw_g
      iff g in C_gen(E,b,j).

More precisely, for EVERY nonempty admissible U,

  B_(c+1)(U) < B_c(U)
      iff b is U-eligible, c_U=p_U=g.

This is an exact **individual numerical-cut** result:
ordinary binary-L support raw ages can change at the even real
coordinate c, not the odd dummy c+1. In the current original block
(through g<k), all eligible ordinary-L critical physical cuts
are exactly the image under hPosition of the verified C_gen set,
restricted to g<k. There is no appeal to full Kpt I1/I2/I3/B3.

## Adversarial checks

1. Generation index g and numbered H cut c are NOT the same:
   c=2*((k+1)*b+g). The first provisional Track A/G ledger mixed
   these coordinates; it was corrected in PR #468 before merge.
2. This theorem compares the actual generated ordinary-L **raw**
   bound over complete numbered prefixes, not the full dependent
   Kpt source. It cannot alone certify Algorithm 5.4 boringness.
3. The older exact generation event lemma is about the prefix
   difference from [0,c) to [0,c+2). The new odd neutrality proof
   is ESSENTIAL to localize the change to the single cut c.
4. The no-edge dummy L property holds in BOTH directions; it
   does not say that H+ auxiliary E at the odd cut is absent.
5. Nonemptiness of U is essential: otherwise a zero column
   would not exclude z from a common-neighbour pool.
6. No uniqueness of full Kpt interesting levels or canonical
   graph-age COVERS is inferred. Raw events can be canonically
   redundant on nonsingleton supports.
7. For singleton U, verified Track A canonical singleton exactness
   allows the same numeric-cut event iff for canonical age.
8. At ell=2, no critical support exists in a genuine K2-free
   original graph. The step theorem then asserts no ordinary
   raw event, consistently with the K2-free age.
9. The formula needs g+1<=k, NOT g+1<=k+1: top generation is
   a distinct finite H crossing phase. No top cut is hidden.
10. The numeric physical carrier cutoff M is a separate issue.
    The generated Boolean-L table is total on Nat, but to
    interpret every mentioned coordinate as a VERTEX of a
    finite `EnumeratedPartialStructure`, require
    hPosition(k,b,g+1)<=M and each named top position < M.
    The base numeric identity is valid algebraically without
    such carrier bounds. Do not silently promote physical
    membership without these hypotheses.
11. Later top originals j(t) need not be pairwise distinct;
    nonempty supports still supply one later original.
12. The canonical age remains constant when the raw function
    remains constant, but converse can fail for nonsingleton
    raw support events.
13. Since odd fake cuts are L-neutral, any genuinely selected
    odd dummy level must arise from terminal, crossing or
    auxiliary B3 information, not from the ordinary old
    clique-capacity event at that coordinate.
14. The raw critical set for one b-block says nothing about
    auxiliary cuts in OTHER original blocks, e.g. the
    separately verified K4 gadget cuts 10 and 22.
15. The finite case examples and independent regressions of
    #460 do not substitute for an exact-head Lean theorem
    about each individual numeric cutoff.

## Lean plan and acceptance

New module `Kk/TrackANumericSingleCutRawEvent.lean`, importing
verified `Kk.PartialNumericCriticalGenerations`,
`Kk.NumericPrefixGapZero`, and
`Kk.FiniteOldColumnAge`.
Endpoints:
- `oldSupportCommonNeighbourPool_insert_zero_column`;
- `finiteOldColumnRawBound_insert_zero_column`;
- `trackA_numeric_odd_dummy_raw_neutral`;
- `trackA_henson_numeric_single_real_cut_change_iff_critical`;
- optionally singleton canonical event iff.

Implement and run standalone named standard-only axiom audit,
`lake build Kk.TrackANumericSingleCutRawEvent`, full `lake build`,
and the existing independent small graph raw-event regression.
No frozen black manuscript edits or premature green marks.


## Independent literal numbered-cut regression and Lean proof-script audit

The new script `scripts/check_track_a_numeric_real_cut.py` reconstructs
the actual generated numerical-H binary L table independently of
Lean. It tests all simple 4-original graphs, heights k=1..3,
all admissible b and ordered later top pairs (allowing repeated
names), every nonempty support of width <=2, and ell=2..5.
It compares the REAL numerical prefix cut c, c+1 and c+2 for
every generation g<k, including full odd coordinates.

**Independent local check:** 59,136 literal numerical cut/support/ell
comparisons passed; 11,652 real-cut raw decreases and exactly
ZERO odd-dummy raw decreases. On genuine original K_ell-free
inputs it also checks that the raw saturation clause is automatic.
The standalone CI runs this same independent test.

First exact-head Lean CI found two LOCAL proof-engineering issues:
a nonlinear-looking multiplication normalization needed `ring`,
and `Finset.range_succ` is not available under that symbol name
in the pinned Lean/Mathlib environment. The latter was replaced
with direct extensional `Finset.mem_range`/`Finset.mem_insert`
plus `omega`; neither issue changes the mathematics.

These are submitted repairs, not a claim of passing exact-head Lean
validation. All five named kernel and standard-axiom gates remain
pending until a complete successful run.
