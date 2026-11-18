# Track G — transfer the WHOLE actual successor-tree run across distinct Kpt seed sets

18 November 2026. English proof and adversarial audit before Lean.
Follow-up to verified/merged PR #347 (local full I1/I2/I3
interestingness and precise skip-law equivalence).

## Stronger result

Fix one normalized Kpt monoid H, two potentially DISJOINT
seed sets X,Y, a finite scan top t, and ONE genuine actual
run R : AlgorithmRun H X t. There is no input run on Y.
Define for each cut c<t:

  ZX(c)=closure(S,R.I(c+1),X),
  ZY(c)=closure(S,R.I(c+1),Y).

Suppose for EVERY c<t:

  (T) KptI1AtCut(family,ZX(c),c) iff
      KptI1AtCut(family,ZY(c),c);

  (C) FullPhysicalClosureCrossing(family,ZX(c),c)
      = FullPhysicalClosureCrossing(family,ZY(c),c).

Then the EXACT SAME functions R.I and R.F define a genuine
`AlgorithmRun H Y t`. In particular there exists RY on Y
with RY.I=R.I and RY.F=R.F as TOTAL MMap-valued functions.

This proves CHOICE-EXISTENCE of a synchronized run, not
equality of the monoid maps in all arbitrary Y-runs.
No equal source enumeration, source inclusion, physical
node overlap, source cardinality constraint, I2-free
assumption, or OneLevelPullback E1 is required.

## Full proof (not an assumption of synchronization)

Construct a record RY using exactly the fields
`I:=R.I`, `F:=R.F`, `topI:=R.topI`, `topF:=R.topF`.
At a cut c<t, the verified G347 local theorem, using
(T) and (C), gives equivalence of the TRUE
`IsInterestingAt(H,ZX(c),c)` and
`IsInterestingAt(H,ZY(c),c)` predicates.

* Interesting Y case: G347 makes X interesting. The
  original genuine `R.interesting_step` yields
  R.I(c)=insert c (R.I(c+1)) and R.F(c)=R.F(c+1),
  exactly the required Y step equations.

* Boring Y case: G347 makes X boring. The original
  genuine `R.noninteresting_step` supplies ONE
  actual skip-only D_c:MMap H with
  R.F(c)=R.F(c+1) o D_c, R.I(c)=R.I(c+1),
  and its ancestor crossing equation for EVERY
  z∈ZX(c) with lev(z)>c.
  The separate verified G347
  `kpt_actual_skipLaw_iff_of_full_crossing_eq`
  transfers that SAME D_c equation to EVERY
  z∈ZY(c), because full paired raw ancestor
  relations agree by (C). The skip-only property
  belongs to D_c itself, so remains unchanged.
  Reuse the original I/F equations verbatim.

These formulas define a genuine `AlgorithmRun` on Y
with identical I and F. Importantly, the record
construction works for the whole scan simultaneously:
it does not merely choose matching maps independently
at each cut without satisfying their recursion.

## Existing arbitrary-run consequence

If ANY other actual R' : AlgorithmRun H Y t is given,
the verified successor-tree same-seed run theorem
`AlgorithmRun.I_eq` applies to RY and R'. It yields
R'.I(i)=R.I(i) for all i≤t, although R'.F(i)
may be different. Thus these (T,C) hypotheses,
checked only along the ORIGINAL R-selected tails,
already suffice to synchronize the selected levels
of EVERY Y-run; no prior RY selected-set agreement
is assumed.

## Independent finite-index input

Given independent EXHAUSTIVE finite indices for
ZX(c) and ZY(c) for all c<t, equality of their
indexed terminal-existence flags and complete paired
raw L+/E crossing relations supplies (T,C) by the
verified finite-index G347 interface. Hence the
whole run can be transported with unchanged I/F.
Neither index-size equality nor any bijection is needed.

## Adversarial checks

1. The new Y profiles are tested against R.I(c+1),
   not the unknown selected sets of a future Y-run.
2. R is an ACTUAL AlgorithmRun, with its full original
   noninteresting-step crossing law; a selected macrodiary
   alone is not an acceptable R.
3. The SAME numeric Kpt tree/family and scan top t are used.
   This does not construct chronological cut reindexing.
4. Terminal flags are essential: a level-c Kpt terminal
   can be invisible to full crossing-pair data.
5. Full dependent old/upper raw L+/E PAIRS must match;
   ordinary graph age or separate marginal spectra fail.
6. The I3 step reuses the same total skipping map D_c,
   not just existence of some unrelated map for Y.
7. Transfer is valid at competing I2 forks because
   the full crossing relation is set-valued, not a
   single-valued arbitrary selected target function.
8. No E1 pullback or source-set inclusion appears.
9. `topF` is literally R.topF, and all step equations
   use the SAME R.F function; no extra coherence axiom.
10. This does not assert two arbitrary Y-runs have equal F;
    only a synchronized Y-run EXISTS.
11. The I choice-independence consequence is from genuine
    `AlgorithmRun.I_eq`, not from equality of source sets X,Y.
12. The two different seeds may have different actual
    terminal and dependent Kpt nodes outside the crossing
    carriers; equality of local profiles ignores those.
13. Equal chosen total monoid maps F on X and Y do NOT
    imply equality of inverse images F^{-1}X and F^{-1}Y.
14. No common labelled inverse-source orbit, finite uniform
    event budget or ordered cut-transport is supplied.
15. K4 real auxiliary q1=10 and q2=22 must still appear
    in both TRUE local profiles if the transport is used.
16. The (B3) relative-continuation comparison is not
    replaced by this conditional abstract run theorem.
17. No unbounded resolved numerical-H+ source copy is built.
18. No lower-colouring or exact Kk-free BRD is obtained.

## Acceptance

Import the exact already verified G347 module and actual
successor-tree AlgorithmRun interface. Formalize the same-I/F
run record construction and its any-Y-run I consequence.
Optionally add an independent exact finite-index entrypoint.
Dedicated standalone direct build and strict named standard-only
axiom gate, plus independent full Lean CI. English first.
Only scoped BLUE manuscript annotations, never a global mark.
