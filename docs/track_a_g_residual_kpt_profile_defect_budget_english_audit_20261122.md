# Track A/G — residual full-Kpt profile defect budget above the sharp ordinary-L event schedule

22 November 2026. **English-first proof and adversarial scope audit.**
This note follows two separately exact-head Lean-verified, merged results:
- Track A #460: genuine original K_ell-free ordinary-L critical generations C(E,b,j) satisfy |C|<=ell-2;
- Track A/G #427: two genuine same-top Kpt AlgorithmRuns have selected-level differences only in a supplied finite exceptional cut set on whose complement the actual full terminal and old/upper L+/E crossing profiles agree.

## Exact residual dependent-profile defect set

Fix ell>=2, original Boolean graph E genuinely avoiding the normalized
Henson forbidden family, original b, and GIVEN later originals j(t)>b.
Let C_gen=C(E,b,j) be the finite set of ordinary-L *generation indices*.
Fix the numerical-H height k and define the distinct PHYSICAL candidate cuts

  C = { hPosition(k,b,g) : g in C_gen and g<k },

where hPosition(k,b,g)=2*((k+1)*b+g) is a true numerical-H
vertex coordinate. This mapping is essential: using g itself as an
Algorithm 5.4 cut would identify the WRONG source levels. Restrict
to g<k since the Track A partial-block formula does not cover the
top generation or subsequent original blocks. Separately
fix TWO genuine AlgorithmRuns R_X,R_Y of the normalized Kpt successor tree
for the same forbidden family, with possibly different seed sets X,Y,
but the SAME scan top N and cut coordinates.

For each cut q<N define the ACTUAL pre-cut parameter closures

  Z_q = closure (R_X.I(q+1)) X,
  W_q = closure (R_Y.I(q+1)) Y.

Let T_q mean that genuine I1 terminal flags agree at q:
  KptI1AtCut family Z_q q <-> KptI1AtCut family W_q q.

Let P_q mean that the COMPLETE physical old/upper dependent L+/E
crossing relations agree at q:
  FullPhysicalClosureCrossing family Z_q q =
  FullPhysicalClosureCrossing family W_q q.

Define the finite residual profile-defect set

  D = { q<N : q notin C and NOT (T_q and P_q) }.

This is a genuine *finite logical profile comparison* over actual
pre-cut closures, not a claim of computability from ordinary-L data.
The two source sets need NOT have equal size, inject into one another,
or share literal Kpt nodes. It includes real I2 forks and full
parameter-closure records. I3 skip-law invariance follows from the
existing full-crossing transfer theorem, not from an L-only projection.

## New unconditional bookkeeping theorem

For every such pair of actual same-top runs,

  (R_X.I(0) symmetric_difference R_Y.I(0))
      subset (C union D),

and consequently

  |R_X.I(0) symmetric_difference R_Y.I(0)|
      <= |C| + |D|
      <= ell-2 + |D|.

Here cardinality is Set.ncard of the finite disagreement set. Every
selected stage agrees outside C union D, not merely the final one.

### English proof

Fix q<N outside C union D. The definition of D and q<N imply that
both the I1 terminal flag and the complete dependent crossing relation
agree at q. The verified Track G physical profile criterion converts
this into equivalence of the TRUE I1/I2/I3 interestingness decisions
of the actual pre-cut closures of the two runs. Thus the verified
Track A/G exception-localization theorem applies with exception
C union D, and gives the selected-stage agreement and final
symmetric-difference inclusion.

The verified finite cardinality corollary bounds the disagreement by
|C union D| <= |C|+|D|. Finally the verified Track A Henson
two-original-clique capacity argument gives |C_gen|<=ell-2,
and taking a filter and an image cannot increase cardinality:
|C|<=|C_gen|<=ell-2.

Nothing in this proof uses a hypothetical common selected shadow,
a forbidden raw-to-canonical shortcut, or the unproved diary-to-profile
matching implication.

## Exact zero-defect interface

D is empty **iff** the actual terminal flags and full L+/E crossing
relations agree at every aligned cut q<N outside C.

Therefore the conditional bound of ell-2 is just the D=empty
specialization, now formulated as a sharply identified residual
mathematical task. The deficit |D| is not claimed to equal the
number of extra interesting cuts: distinct profiles may still induce
equal genuine interestingness decisions, and some mismatches may occur
at levels neither run eventually selects.

## Crucial adversarial checks

1. **Coordinate safeguard:** the ordinary set C_gen contains
   generation indices, NOT Kpt scan cuts. The numerical exceptional
   set C is an hPosition(k,b,-) image restricted to g<k.
   There is NO Lean theorem here asserting that every actual
   per-coordinate ordinary raw event happens only at these cuts;
   the mapped set serves as the intended candidate exceptions.
   The previously verified Track A event iff is a comparison
   of complete partial prefix boundaries, not automatically an
   all-intermediate-numeric-cut localization.
2. The original graph E and the two genuine Kpt runs are parameters
   of the same theorem, but **no theorem here constructs those runs
   from the finite original E**. This is a modular ledger, not a
   proven physical diary/source coupling. Any eventual application
   must separately identify E,b,j and the two actual run sources.
3. C_gen counts raw binary-L support-capacity changes, not all canonical
   covers and not any auxiliary I1/I2/I3 event. D explicitly retains
   all full-source discrepancies outside C.
4. D is defined on the FULL actual pre-cut closures, with
   R_X.I(q+1),R_Y.I(q+1) separately; substituting the initial
   seed sets or one common fictional selected tail is invalid.
5. The terminal flag is required independently. Equal crossing
   relations alone miss genuine terminal I1 differences.
6. The full crossing relation includes auxiliary E records, I2 forks
   and the I3 skip-law transport. An ordinary-L-only restriction is
   insufficient to derive T_q/P_q.
7. Two different seeds may have different actual Kpt index sizes;
   this theorem does not demand a bijection or reverse source map.
8. q<N is essential. Defects outside the actual scan interval are
   deliberately not counted; the ordinal cut N itself is not scanned.
9. D is disjoint from C by its definition. The upper bound
   |C|+|D| remains correct without exploiting that disjointness;
   it should not be described as a bound on either selected set's
   total cardinality.
10. At ell=2, the genuine K_2-free graph has empty critical C.
   Disagreement can still be carried by D; no false free
   Kpt-boringness is claimed.
11. If the two actual profile relations differ but the interesting
    decision is the same, q may belong to D needlessly; the
    bound is intentionally a sufficient (possibly nonminimal)
    source-profile discrepancy budget.
12. The finite `Finset` D uses classical decidability of source-set
    equalities. It does NOT claim a uniform algorithm without
    complete finite Kpt source indices. The verified Track E/G
    indexed profile constructions provide the appropriate later
    executable comparison interface.
13. The model-specific diary construction is still missing the
    implication `diary -> D=empty` (or a uniform bound on |D|).
    This is the real remaining source-comparison task.
14. No global BRD theorem, common labelled inverse-source orbit,
    cross-top reindexing or arbitrary-dimensional finite microdiary
    degree is asserted.
15. Black manuscript text and existing green verification marks
    remain untouched until this source and all qualified axiom
    reports pass an exact-head Lean gate.

## Lean plan

Implement in `Kk/TrackAKptResidualDefectBudget.lean`:
- `kptOffExceptionFullProfileDefects` (finite set of genuine full
  profile mismatches outside any specified ordinary exception set);
- `kpt_full_profiles_eq_of_not_mem_off_exception_defects`;
- `trackAPhysicalCriticalCuts` (actual hPosition image with
  g<k) and `trackA_henson_physical_critical_cuts_card_le`;
- `kpt_actual_runs_selected_disagreement_le_exception_plus_defects`;
- `trackA_henson_kpt_selected_disagreement_le_sharp_plus_defects` with the PHYSICAL numerical-H exceptional set (not C_gen);
- optionally `kpt_off_exception_defects_empty_iff_profile_match`.

Import only already merged `Kk.PartialNumericCriticalGenerations`
and `Kk.TrackAGExceptionSelected`; avoid any dependency on stale
PR #351/#431. Run direct module build, full Lake and exact qualified
strictly standard-only `#print axioms` parser.

The provisional first source draft mistakenly used the generation set
C_gen directly as the numerical cut set. This was identified in the
adversarial source audit BEFORE any merge, and the Lean theorem and
this English note were corrected to use C. The correction changes
the theorem interface but does not prove the still-open
parameter-closed diary-to-profile matching statement. Keep in DRAFT until
the precise head passes.


## Application-facing conditional special case

Suppose at every **numerical** scan cut `q<N` outside the mapped
physical candidate set `C`, the TRUE pre-cut I1 terminal flags
and complete L+/E old/upper crossing relations of the two actual
runs agree. Then the already verified five-theorem Track A/G
exception comparison applies directly with
`Exceptional = trackAPhysicalCriticalCuts ell k E b j`, giving

  ncard(I_X(0) symmetric_difference I_Y(0))
      <= |C| <= ell-2.

This is precisely the `D=empty` case of the more general defect
budget, but is useful as a separate theorem with explicit,
testable full-source hypotheses. It does **not** assert that the
diary construction supplies them.

Lean target:
`trackA_henson_kpt_selected_disagreement_le_sharp_of_full_profiles`.
Its proof is one composition of
`kpt_actual_runs_selected_disagreement_card_le_of_full_profiles`
and `trackA_henson_physical_critical_cuts_card_le`.
