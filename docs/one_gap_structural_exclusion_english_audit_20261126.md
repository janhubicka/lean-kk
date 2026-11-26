# One-gap full closure structural exclusion

26 November 2026. English proof and adversarial review before implementation.

## Obligation

`OneGapFullClosure` proves the complete next-type fibre equality but its
closure-endpoint theorem still assumes that no two pool originals have a
same-component meet at the omitted cut. This note discharges that assumption.
The result concerns the complete dependent Kpt closure, including auxiliary
parameters and iterated meets, for any prescribed retained set. It does not
construct the countable ordinary resolution or prove a Big Ramsey degree.

## Proof

Fix one finite enumerated partial structure A, an admissible forbidden family,
and a pool V of actual original addresses. Suppose that no original in V has
its free endpoint at c. Assume also that whenever two originals in V have free
levels strictly above c and equal complete types at c, their complete types at
c+1 agree.

If two originals in V had a same-component meet of level c, both originals
would have free levels at least c. Endpoint exclusion makes both levels
strictly larger than c. The meet is the level-c ancestor of each original, so
the complete old types agree. Fibre equality then makes the level-(c+1)
ancestors equal. This common next ancestor is below the meet, contradicting
that its level c+1 exceeds the meet level c. The argument includes duplicate
originals: the endpoint hypothesis is precisely what excludes a self-meet.

For the actual meet-and-parameter closure, assume the initial seeds are
represented by a pool U contained in V, every retained successor parameter
belongs to V, and no seed ends at c. The previously proved exact closure
normal form says that every closure node is a seed, a retained parameter
original, or a same-component meet of two pool originals. All three cases
have just been excluded at c. This gives complete (I1) absence.

The actual closure is componentwise meet-closed. Consequently, any pair of
closure nodes in the same component whose meet had level c would give a
closure node at level c. This contradicts (I1) absence, so the complete (I2)
test also fails. This last implication uses the actual closure; it need not
hold for an arbitrary selected set which has not been closed under meets.

For the graph signature, the existing
`oneGap_full_nextType_eq_of_no_column_fork` supplies full type coherence from
ordinary column coherence on V. Symmetry, zero loops and zero diagonals are
retained as explicit ordinary-structure hypotheses. Eligibility by the exact
free level forces both E directions, so no auxiliary atom is omitted.

Finally, `oneGap_full_pool_column_fibre` derives ordinary coherence from
selected-terminal no-fork, positive-source classification, the existence of
an old neighbour for every positive pool source, and zero old columns on
nonselected future pool sources. The old-neighbour premise is itself
discharged from complete selected canonical-age neutrality: canonicalization
is exact on singleton old-column supports. If a positive selected terminal
had no neighbour below c, its old singleton bound would be ell-1. Restoring c
puts the one-vertex clique {c} in its common-neighbour pool, making its new
bound at most ell-2. Equality of canonical singleton bounds contradicts
this. This works for every ell at least two, with no symmetry, freeness or
positive-raw-bound assumption needed for the singleton calculation.

Thus the assembled structural theorem needs selected no-split, positive
pool-source classification, nonselected future old-column zero, and exact
selected age neutrality; it does not assume a separate old-neighbour,
full-pool no-fork, no-meet, no-I1 or no-I2 certificate. The resolved-graph
construction still has to establish the stated ordinary data.

## Adversarial checks

1. A self-meet at c is possible without free-endpoint exclusion; keep it.
2. A seed at c need not be a proper meet; keep seed-endpoint exclusion.
3. Pool originals may end below c; only a hypothetical meet at c forces the
   two relevant originals to reach c.
4. Equal old ordinary columns alone do not force equal auxiliary next atoms
   without free-level eligibility; use the full existing next-type theorem.
5. Root components must match before using meet lower-bound properties.
6. Duplicate addresses and duplicate old types are allowed; no injectivity of
   original-type representation is assumed.
7. V covers every selected parameter, not merely selected graph terminals.
8. The normal form covers arbitrarily iterated meet/parameter closure.
9. I2 is excluded for all actual closure pairs, including pairs with equality.
10. Retained levels can be a nonminimal prescribed set; no AlgorithmRun
    interestingness condition is used.
11. No selected-only age criterion is asserted without the positive-source
    and full-pool structural hypotheses.
12. No new axioms, `sorry`, infinite constructor, common source orbit or
    unconditional sharp BRD theorem is introduced.
13. Singleton raw bounds can be zero; the old-neighbour argument only uses
    the contradiction between old bound ell-1 and new bound at most ell-2.
14. The selected list may repeat vertices and d can be zero. A positive pool
    source then forces a selected index; no artificial nonempty default is
    introduced by the structural theorem.
15. Selected no-split is required only for selected vertices above the cut;
    previously coded selected vertices are not silently included in that
    hypothesis.

The proof was independently reviewed before Lean implementation. Compilation
and exact transitive-axiom checks must succeed before certification.

## Convexity on the literal padded carrier

A further independent application review found that the original
`OneGapBlockConvex` demanded that every natural coordinate strictly between
two retained members of one block also be an auxiliary member of that block.
That contract works on unpadded Q but fails on literal one-gap coordinates:
each internal odd coordinate is an isolated dummy.

We therefore weaken the convexity contract to allow an intermediate dummy
or another retained auxiliary of the same block. The old-column theorem
still follows. If an older and a later retained auxiliary belonged to the
same block around the tested cut, the cut would have one of these two roles;
both satisfy `ResolvedQRetainedBase`, contradicting its explicit omission
hypothesis. Different-block, coded and dummy source cases are unchanged.

This is a weaker ordinary construction premise, with exactly the same
conclusion. It retains the essential restriction that an omitted meaningful
coordinate cannot interrupt a kept block. It does not assert that every
dummy cut is retained by a particular envelope: `ResolvedQRetainedBase` is
the role-level pool predicate, and the old-column theorem's omission
hypothesis still excludes dummy roles. Actual treatment of omitted dummy
cuts remains a separate application case.
