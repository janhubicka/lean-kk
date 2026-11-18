# Track G — boring-factor action is independent of choices for one seed set

18 November 2026. English proof BEFORE Lean. This is a source-level
choice-independence theorem, not identification across distinct diaries.

## Theorem

Let R,R' be any two ACTUAL AlgorithmRuns for the same SMTree H,
same finite scan top t and same selected seed set X. Fix
low≤high≤t. Suppose I_R(low)=I_R(high), where I_R is the
genuine selected-level set, NOT the selected ordinary graph age.
Then both runs have UNIQUE total accumulated monoid factors D,E
over the interval, and for every c in the common actual
complete high-end closure and lev(c)≥high,

  D(ancestor(c,low))=E(ancestor(c,low))=ancestor(c,high).

This requires no OneLevelPullback E1, bounded Henson
realization, full numerical-H cut schedule, or assumption
that the total maps F_R(i) and F_R'(i) coincide.

## Proof

By the already verified `AlgorithmRun.I_eq` in
`lean-successors/SuccessorTree/EnvelopeRun.lean`, both runs
select exactly the SAME I(i) at every i≤t. Hence
I_R'(low)=I_R'(high). The verified G318 exact equivalence
`I(low)=I(high) iff all actual complete pre-cut stages
are boring` now shows that both runs are genuinely
boring at every cut of [low,high), using their own full
source data. The verified G331 two-run actual physical
overlap theorem provides D,E and their equality on the
ancestors of each node belonging to BOTH high-end
closures. Since I_R(high)=I_R'(high) and the seed set X
is identical, these closures are literally equal. Thus
every c from either complete high-end closure is covered.
G331 separately identifies each action with the
actual upper ancestor. Unique total D,E follow from G309/G318
left cancellation by the respective high-endpoint embeddings.

## Hostile checks

1. The SAME X and scan top are essential for I_eq;
   this does not compare different diary occurrences.
2. The equality is I_R(low)=I_R(high), not equality
   of any ordinary-L selected-front graph-age projection.
3. Every run must satisfy the actual AlgorithmRun recursion;
   not an arbitrary proposed family of I,F maps.
4. G318 converts endpoint I equality to full-source boringness.
5. Different noninteresting-step map choices are allowed;
   the total factors can differ outside the common carrier.
6. No E1 is required for I choice independence or G331 action.
7. This is a theorem about the entire actual full closure
   at high, not just originally marked terminal vertices.
8. The old K4 10/22 microevents remain selected and
   cannot appear in an asserted all-boring interval.
9. No cut-coordinate map between distinct occurrences follows.
10. No inverse source orbit, prescribed resolved H+ copy,
    corrected B3 relative-continuation or BRD count follows.

## Acceptance

Import the verified G318 and G331 and the actual
successor-tree `AlgorithmRun.I_eq` theorem. One independent
standalone Lean theorem, direct build, one exact qualified
standard-only axiom gate and independent full CI. This
should not add a global manuscript validation mark.
