# Track G — full local event profiles synchronize the selected scan of DISTINCT Kpt seed sets

18 November 2026. English proof before Lean. This continues verified
Track G PR #347, merged at b6d42df78516cf85c8c936a423cf2324db915195.

## Abstract successor-tree stagewise-decision lemma

Fix any genuine successor-tree monoid H, TWO seed sets X,Y,
one common finite scan height t, and two genuine AlgorithmRuns
RX:AlgorithmRun H X t and RY:AlgorithmRun H Y t.
Suppose for EVERY i<t their TRUE pre-cut interestingness
predicates agree:

  IsInterestingAt(H,closure(S,RX.I(i+1),X),i)
     iff IsInterestingAt(H,closure(S,RY.I(i+1),Y),i).

Then for every i≤t, RX.I(i)=RY.I(i). In particular the
two final selected-level sets are identical.

Proof: downward induction from t. Base: both actual runs
have I(t)={t} by their topI fields. At i<t assume the
equality of selected I(i+1). If the shared decision is
interesting, both actual interesting_step laws give
I(i)=insert i (I(i+1)); if boring, both genuine
noninteresting_step laws give I(i)=I(i+1). The induction
closes in either case. The proof does NOT use E1, source
set inclusion, equal monoid F values or a source orbit.

## Kpt full-profile finite scan theorem

Take one fixed normalized forbidden family, actual Kpt seed
sets X,Y (possibly physically disjoint), same scan top t,
and their actual AlgorithmRuns RX,RY. For each i<t let
Z_i=closure(S,RX.I(i+1),X), W_i=closure(S,RY.I(i+1),Y).

Assume at EVERY aligned numeric cut i:

  (1) KptI1AtCut(family,Z_i,i) iff KptI1AtCut(family,W_i,i);
  (2) FullPhysicalClosureCrossing(family,Z_i,i)
          = FullPhysicalClosureCrossing(family,W_i,i).

By G347's verified
`kpt_IsInterestingAt_iff_of_terminal_and_full_crossing_eq`,
the true I1/I2/I3 algorithm decisions agree at each i.
Apply the abstract stagewise-decision lemma. Hence
RX.I(i)=RY.I(i) for EVERY i≤t, not only at the end.

This statement does not require any literal Kpt node
overlap, finite index bijection, or a no-I2 assumption.
It compares ACTUAL complete source profiles and
does not infer them from selected ordinary-L ages.

## Independent exact finite-index criterion

Give each run an independent FINITE index of its complete
pre-cut parameter-closed sources, with exact Boolean live
masks at EVERY i<t. Sizes P,Q may differ. Suppose for
every i<t the two source-index terminal-existence flags
agree, and their full indexed dependent old/upper
`IndexedPhysicalCrossing` relations agree. G347's
verified independent-index theorem converts these
conditions to agreement of the actual I1/I2/I3
decisions; apply the abstract scan lemma.

The conclusion is equality of the entire selected I
scan, WITHOUT any index matching or source-node bijection.
At a single cut, terminal equality is independent of
crossing equality (terminal-prefix blindness). The
full pair must retain complete E and negative L atoms
and the paired old/upper relation, not just its marginals.

## Adversarial audit

1. Both AlgorithmRuns have exactly the SAME scan height t;
   the statement does not reindex different top heights.
2. Source sets X,Y can differ; generic AlgorithmRun.I_eq
   for one fixed X cannot be applied to this situation.
3. Profile equality is of the TRUE pre-cut full closures,
   not of a selected-front ordinary graph-age shadow.
4. I1 terminal presence must be checked separately: a
   level-i terminal contributes no crossing pair above i.
5. Full same-node dependent raw L+/E pair equality is used;
   unpaired upper spectra do not characterize I3 constraints.
6. No no-I2 premise; competing fork pairs all survive.
7. The source at step i is closure(S,I(i+1),X), not
   closure(S,I(i),X) or the final source at zero.
8. The abstract downward induction needs only actual
   interesting_step/noninteresting_step equations for I.
9. A boring step can change its total MMap F nontrivially;
   I equality does not imply F equality or common factor.
10. Two different sources can have different number of
    actual Kpt nodes while producing the same full profile.
11. Independent per-cut indexed profiles do not supply a
    coherent index correspondence across adjacent cuts.
12. There is NO occurrence-independent labelled inverse
    Kpt source monoid orbit or uniform bounded carrier here.
13. K4 genuine auxiliary cuts 10 and 22 remain interesting
    in any actual runs with matching complete profiles there.
14. The source-profile equality must still be constructed
    from the proposed refined diary resolution schedule;
    it is NOT a consequence of the current macrodiary.
15. No assumption about OneLevelPullback E1 is used.
16. Corrected full-(B3)-loss versus relative continuation
    remains a separate bridge, not inferred from I equality.
17. Infinite resolved numerical-H+ copy existence remains open.
18. Independent lower colouring/unavoidable BRD numbers remain open.

## Acceptance

Implement an abstract one-run-pair stagewise decision lemma,
an actual Kpt profile-scan corollary, and the finite-index
same-scan corollary. Use source-exact prior G347 results.
Run dedicated direct compilation, strict parser self-test and
three exact qualified standard-only #print axioms endpoints,
plus independent full-project CI. No manuscript BLACK edits
and no global validation claims. If passed, a narrowly scoped
BLUE olive annotation may be appropriate.
