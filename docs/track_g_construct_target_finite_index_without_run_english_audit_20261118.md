# Track G — construct the TARGET finite full Kpt source index without a target run

18 November 2026. English proof BEFORE Lean. This closes a gap
in the hypothesis accounting of the G371 finite canonical-Bad test.

## Target

Fix one actual finite numerical-H+ structure A=finiteNumericH K k N
avoiding a normalized forbidden Kpt family; fix U⊆Fin N.
Let Y be ANY set of admissible Kpt seed nodes represented by the
actual ambientPrefixPool of A over U. Let I:Nat→Set Nat be
ANY externally supplied family of selected level sets, with
one fixed finite top t and the simple tail condition:

  for each cut c<t, I(c+1) ⊆ I(0).

There is NO AlgorithmRun on Y and no interestingness
decision hypothesis for I.

## Theorem A — finite exhaustive target index for arbitrary I tails

One fixed finite Kpt node set `params` and Boolean
`live(c,j)` enumerate EXACTLY the entire complete
meet/parameter closure at every given tail:

  z∈closure(S,I(c+1),Y)
    iff ∃j∈Fin params.card, node(j)=z ∧ live(c,j)=true.

The finite source-name universe is precisely
`closure(S,I(0),Y)`, enumerated by its canonical Finset
and equivFin; it is NOT the selected ordinary graph.

**Proof.** Each y∈Y is below some genuine original Kpt
source node of the finite H+ prefix. The verified free-level
bound gives lev(y)≤freeLevel(v)≤v<N. Thus Y lies below
the uniform Kpt level bound N even if Y is not itself finite.
The generic verified successor-tree closure-finiteness
theorem `SMTree.Envelope.closure_finite_of_bounded` applies
to ANY selected level set I(0), not only one obtained
from Algorithm 5.4. Therefore

  Z = closure(S,I(0),Y)

is a finite set of actual Kpt nodes. Enumerate it by
`params=Z.toFinset`, and define the stage live mask by
literal closure membership at each cut. The assumed
I-tail inclusion and closure monotonicity imply every
true pre-cut source sits inside Z. Finset.equivFin
exhaustiveness then yields the exact iff at every cut.

The proof is based on the physical finite H+ level bound,
not on any assumed full source enumeration on Y.

## Theorem B — physical finite H+ application to canonical Bad

Now let X⊆Y, and assume ONE genuine AlgorithmRun RX on X
with top t. Y and X are represented by the same finite
numerical H+ prefix and forbidden family. The already
verified Track C theorem constructs one exact old index
for ALL actual RX pre-cut closures on X.

The genuine final-tail invariant
  RX.I(c+1)⊆RX.I(0)   for all c<t
supplies Theorem A's sole I-tail premise, thus a separate
exact new source index for closures on Y *along RX.I*.
No actual run on Y is assumed or used to construct the index.

The resulting two indices have (possibly different) finite
name counts. Form the verified E54 minimal canonical
physical old-boring Bad Finset from their exact live masks.
If this concrete canonical Bad Finset is EMPTY, verified
G371 constructs a genuine AlgorithmRun RY on Y with

  RY.I = RX.I,
  RY.F = RX.F (as TOTAL monoid-valued functions).

Thus the only remaining unproved input for this finite
physical stage is the actual no-novelty/Bad=empty property.
Neither existence of a finite new source index nor a
target run needs to be assumed.

## Important limits and hostile checks

1. The physical target Y must be represented by ONE ACTUAL
   finite numerical-H+ original-prefix pool. Arbitrary
   unbounded abstract Kpt seed sets need not admit finite indices.
2. A finite source index here is a CLASSICAL existence result;
   do not claim an implemented executable classifier of all
   dependent type nodes, no bound uniform in the diary.
3. The generic finite Kpt closure theorem is used for
   an arbitrary I(0); NO Y AlgorithmRun is input.
4. The prescribed tails must satisfy I(c+1)⊆I(0);
   otherwise a pre-cut node may not be in the shared
   final enumeration.
5. At an actual RX run, tail inclusion follows from the
   verified I_eq_final_tail_of_run theorem, not from
   selected graph-age invariance.
6. The stage live mask is literal complete closure membership,
   including all generated parameter and meet nodes.
7. Source indices are injective via Finset.equivFin,
   but no index equivalence old↔new is required.
8. Different index cardinalities do not obstruct terminal
   and paired old/upper full L+/E comparisons.
9. No-(I2) is NOT assumed, since true physical crossing
   relations retain all competing fork outputs.
10. A real K4 auxiliary microcut can make the canonical
    Bad set nonempty, which blocks the stated transfer.
11. Emptiness is a sufficient but not a necessary condition
    for existence of some same-I/F target run.
12. The resulting Y run is a synchronized CHOICE, not proof
    that every possible Y run uses the same F.
13. No claim that RX and RY have the same labelled inverse
    images of different seed sets under their equal F.
14. No chronological cut-coordinate reindexing, common
    occurrence-independent source history, or finite bound
    independent of the finite H+ carrier size N.
15. Unbounded resolved copy, corrected B3 relative-continuation
    and independently unavoidable lower colouring remain open.

## Lean acceptance

Import `NumericHExhaustiveRunIndex`, G371 and verified
generic closure_finite_of_bounded. Prove an arbitrary-I
finite source index and one combined physical-stage
canonical Bad zero ⇒ constructed same-I/F target run.
Dedicated exact-head Lake module and two exact qualified
standard-only axiom reports with parser negative self-test;
independent full Lean CI. Manuscript BLACK untouched.
