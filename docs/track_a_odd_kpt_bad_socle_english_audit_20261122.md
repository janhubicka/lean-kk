# Track A/G — physical odd-cut complete Kpt Bad-factor obstructions

22 November 2026. English-first proof and independent adversarial audit
BEFORE Lean. This uses only already merged source:
`Kk.TrackGZeroStageExactBadTrichotomy` and the ACTUAL numerical-H
odd-coordinate zero-L theorem, and is independent of pending
numeric-real-cut PR #479.

## Precise physical statement

Fix a true numerical-H+ model A=finiteNumericH(K,k,N) in the graph
signature (one binary L; no unary; one diagonal). Fix an arbitrary
normalized forbidden family `family`, genuine family avoidance
`hAvoid`, and genuine L symmetry `hSym`. Fix selected original
index set U, old Kpt seed X and candidate seed Y, with X subset Y
and the candidate seeds in the actual ambientPrefixPool. Let R be a
genuine OLD AlgorithmRun on X at top. Let a finite exact index
`node : Fin Q -> AdmissibleKptNode family` with live masks enumerate
all and only the actual pre-cut parameter closure on Y. Choose an
ODD numerical level c=2*a+1.

If the actual exact old-factor Bad cut test holds at c, then at
the TRUE candidate pre-cut closure on Y, at least one of the following
physical obstructions occurs:

1. A genuine terminal Kpt source node z has lev(z)=c (I1).
2. Two genuine candidate Kpt source nodes in one component have
   their meet at level c (I2).
3. A genuine candidate crossing node z has **no OLD live**
   crossing w with the SAME complete OLD Kpt ancestor at cut c,
   retaining all dependent E atoms and the negative L data.

**Proof.** The numeric-H binary generator is identically zero on
odd left coordinates:
`hNumericBinary_odd_left_false K.binary k a v (0:Fin 1)`
for every natural vertex v. Thus the entire true stage-original
zero-L condition used in the already kernel-verified theorem
`finiteNumericH_zero_stage_exact_factor_bad_has_three_physical_witnesses`
is automatic at c, independently of U, R.I, or free-level. Apply
that theorem to the actual candidate exact index. Its three outputs
are precisely the three cases displayed.

There is **no** assertion that the third alternative vanishes.
At an odd cut the auxiliary E-free-end may cause terminal I1,
and a newly appearing dependent Kpt prefix may lack an old-socle
representative. Ordinary-L zero alone is never used as a substitute
for full E or corrected B3 matching.

## Direct contrapositive certificate

In the same setting, if no candidate terminal exists at c, no true
same-component meet at c exists, and **every** candidate crossing
node z has some OLD live matching complete OLD Kpt ancestor at c,
then c is NOT a member of the exact old-factor Bad-cut set.

This is the logical negation of the preceding trichotomy and is
an exact sufficient physical certificate for a good OLD-factor cut.
It is NOT by itself existence of a target AlgorithmRun; that
requires a separate genuine whole-run transfer theorem and may
include other levels.

## Relation to other already verified facts

- `henson_numericH_odd_cut_correctedB3` proves the L-only
  corrected-B3 component is safe at odd cuts, but expressly does
  NOT exclude structural Kpt I1/I2. Our theorem retains those.
- The general zero-column socle transport E72 forces equal complete
  UPPER Kpt ancestor from matching complete OLD ancestor under the
  true stage zero assumption. At odd cuts this assumption is automatic.
- Track G's exact factor Bad trichotomy combines this with true I3
  factor obstruction; our specialization identifies the missing-old
  socle alternative at genuine odd coordinates.
- This is independent of the new Track A ordinary even-cut event
  theorem: it is a source-exact dependent-Kpt statement about ODD
  physical levels, not about cardinalities of raw graph ages.

## Adversarial checks

1. The odd level is **numeric coordinate** c=2*a+1, not a
   generation index g. The proof never confuses these.
2. The candidate live finite index is required EXHAUSTIVE at the
   actual pre-cut closure on Y, including parameter-generated nodes
   and auxiliary E. An index of selected original graph nodes
   would be unsound.
3. The old R.I(c+1) is used in both candidate and old closures;
   this theorem does not assume any target R_Y.
4. `hSym` for the full true numerical-H graph L remains an
   explicit hypothesis, not inferred from arbitrary K.
5. Both seed inclusion X subset Y and ambient candidate-pool
   hypothesis are needed to use the verified zero-stage trichotomy.
6. The stage zero-L premise is for ALL eligible actual originals
   in the TRUE stage pool. Oddness supplies the stronger universal
   zero L bit, not merely zero to given later TOP columns.
7. Odd H+ E incidence may remain nontrivial, so do NOT infer
   absence of terminal I1 from ordinary-L zero.
8. Full Kpt old ancestry includes all dependent E and negative
   ordinary L coordinates; an L-only old-type match is insufficient.
9. The I2 alternative is a genuine same-component meet; mere
   old-type coincidence does not automatically create it.
10. The third alternative refers to absence of an OLD match for
    a candidate crossing; it is not an assertion of source
    injectivity or a reverse coherent source map.
11. This is **only a necessary trichotomy** for Bad cuts and
    a conditional sufficient no-Bad criterion. It does not count
    the number of Bad cuts uniformly, construct an infinite
    resolved diary, or settle global BRDs.
12. This is a direct corollary of existing verified results,
    which must still be compiled on the exact current Lean head
    and checked with standard-only transitive axioms.
13. No black manuscript changes or premature validation marks.

## Lean target

New independent `Kk/TrackAOddBadSocleTrichotomy.lean` with
- `finiteNumericH_odd_exact_bad_terminal_meet_or_missing_old_socle`
- `finiteNumericH_odd_exact_good_of_no_three_obstructions`

The first directly instantiates the merged zero-stage theorem using
`hNumericBinary_odd_left_false`. The second is a straight
contradiction via three explicit negations. Dedicated exact-head
direct module/full Lake and named standard-only axiom report,
leaving the PR draft until it passes.
