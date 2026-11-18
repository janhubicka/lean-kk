# Track D: a complete zero ordinary cut-column cannot create a new full Kpt fork
18 November 2026. English first; adversarial audit before Lean.

## Claim 1: one-step full dependent type uniqueness

Fix one real finite enumerated partial L+/E structure A in the graph
signature (one directed binary atom; zero unary atoms; one diagonal),
whose ORDINARY binary L is symmetric. Let cut be a numerical position
and v,w two genuine physical original addresses such that
 cut+1 <= freeLevel_A(v), cut+1 <= freeLevel_A(w),
 L_A(cut,v) = L_A(cut,w) = false.
Assume their COMPLETE old dependent types coincide:
 partialTypeAt_A(cut,v) = partialTypeAt_A(cut,w).

Conclusion: their COMPLETE next dependent types also coincide:
 partialTypeAt_A(cut+1,v) = partialTypeAt_A(cut+1,w).

Proof in English. By literal restriction, the two next records have
the same complete predecessor. The verified CompleteNextColumn
reconstruction theorem says it suffices to match every atom involving
the new old ordinary coordinate cut.

For ordinary L:
* old/new coordinate interactions among old ordinary vertices are
  fixed by the same actual ambient A, independent of v/w;
* cut->type vertex is zero on both, and type->cut is zero by
  ordinary binary symmetry;
* unary/diagonal symbols of the new old coordinate are fixed by A.

For auxiliary E:
* old/old, including new coordinate cut with any earlier old
  coordinate, is fixed by the SAME ambient A;
* cut->type vertex is TRUE for both, by cut < freeLevel of both
  actual eligible originals;
* type->cut is FALSE for both, by the verified no-reverse-E
  consequence of SpacedE and cut < the later original;
* E loops at the new old coordinate, and E type-type, are covered
  by old-column independence and the common predecessor, respectively.

The complete last columns therefore agree. No unconstrained
additional tuples remain; apply completeNextColumn_determines_type.

This is stronger than selected shadow equality and retains all FALSE
L bits, reverse orientations, auxiliary E and (trivial) unary/diagonal
information. It does not assume no-I2 or give an E structure to an
L-only forbidden-clique witness.

## Claim 2: full Kpt strict-fork exclusion (proposed)

Let Z be a genuine actual meet/parameter closure in the SAME A,
represented exhaustively by a finite original-name list. At cut c,
assume EVERY full closure-selected original v with its E-free level
strictly beyond c has ordinary L(c,v)=false.

Suppose a,b in Z cross c and share the SAME complete old Kpt type.
Choose actual source representatives v,w of a and b (possible by
full pool exhaustion); because their Kpt nodes cross c, these
originals are eligible. Their physical old full types equal the two
Kpt old ancestors, hence coincide. Claim 1 then gives equality of
their physical next types. Identifying these with the actual next
Kpt ancestors of the SAME a and b contradicts any upper-distinct
KptFullCutFork.

Conclusion: the complete nonfunctional full L+/E crossing fork
predicate is false. Under an ADDITIONAL no-I1 hypothesis, the
already verified kpt_no_I1_I2_iff_complete_full_fork also excludes
the genuine competing I2 meet. No-I1 is not inferred.

## Attack on a tempting but INVALID stronger result

The no-positive-cut-star property does not by itself forbid an
initial seed which ENDS at the tested cut (a genuine I1 terminal).
Such a seed can have no crossing name at all. Similarly, generated
meets of genuine original types may end at cut even if their full
originals are not themselves active source nodes. It is incorrect
to infer no-I1 solely from the absence of full crossing forks.
This audit explicitly keeps the I1 test.

## Adversarial audit (18 checks)

1. Both future sources live in the SAME physical A; no cross-run
   old socle equality is silently assumed.
2. L symmetry is essential to control type->cut when only cut->type
   zero has been supplied.
3. Both actual original free E-levels reach cut+1.
4. E(cut,v) and E(cut,w) are true; do not replace them with zero
   just because ordinary L cut bits vanish.
5. E(v,cut) and E(w,cut) are false by genuine spacing.
6. Equality of old dependent types already includes each E old bit.
7. Ordinary old-old and E old-old atoms at the NEW coordinate cut
   are independent of which future type vertex is used.
8. Unary/diagonal source atoms at the newly added OLD coordinate
   depend on A alone, so neither can create a fork.
9. The initial type vertex's unary/diagonal and loop atoms are
   already included in the equal old records.
10. Both L orientations involving the type vertex are checked,
    not just undirected adjacency.
11. The CompleteNextColumn theorem covers all Option(Fin) indices.
12. Full source representation uses ACTUAL Kpt node <= named original.
13. A prefix/meet recipe is not substituted for a Kpt node in Z.
14. The no-positive condition covers EVERY closure-selected physical
    representative, not only selected coding TOP names.
15. If one physical source has two original representatives, the
    earlier verified name transport equates both full old and next.
16. KptFullCutFork is only strict crossing upper nonfunctionality;
    trivial meets at I1 levels are not included.
17. No-I2 follows from no-fork only under no-I1, by the checked exact
    structural classifier.
18. The result does NOT prove global full-pool boringness, no-I1,
    uniform diary correspondence, labelled orbit, or BRD values.

## Integration target

If Claims 1 and 2 pass strict Lean, combine with the new
Track D isolated-dummy/selected-coding LOWER cut-star elimination.
For those cuts, no-I2 is then redundant GIVEN no-I1. The hard
structural induction reduces to eliminating actual full I1 endpoints,
whose seed/parameter/meet normal forms must be checked separately.
