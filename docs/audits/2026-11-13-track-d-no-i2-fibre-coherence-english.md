# Track D: no-(I2) forces complete next-type fibre coherence
13 November 2026 — English-first proof and hostile review

## Existing checked ingredient

In pinned SuccessorTree.V10.I3ClosureSelectedCrossing, the proof of
closureSelectedBoringData_covers uses the theorem
SMTree.Envelope.nextPrefix_eq_of_no_meet: two closure nodes whose
level-cut ancestors agree must have the same level-(cut+1) ancestor
unless their meet is exactly at cut.

## New general theorem

Fix an enumerated L+ partial structure A avoiding a normalized family,
a set Z of genuine Kpt nodes, an original-name map from Fin M into A,
and a tested cut. Suppose each MARKED original represents some node of
Z strictly above cut which is a prefix of that ambient original.
Suppose no pair of nodes in Z in a common component has meet at cut.

If two marked original names have identical COMPLETE old L+ records
A.partialTypeAt cut, then their COMPLETE next L+ records
A.partialTypeAt (cut+1) agree. Consequently their next ordinary
L-reducts agree, including all directed negative atoms.

### English proof

Choose genuine representing nodes z_v,z_w in Z. Their ancestors at cut
have raw dependent type nodes (cut,A.partialTypeAt cut v) and
(cut,A.partialTypeAt cut w), by checked
kptBelowOriginal_ancestor_raw. The two raw records are equal by
the hypothesis on old complete source types; hence the ancestors
are equal and the two closure nodes share a component. The no-(I2)
condition forbids their meet from having level cut. The checked
nextPrefix_eq_of_no_meet theorem now identifies their ancestors
at cut+1. Apply kptBelowOriginal_ancestor_raw at cut+1 to turn
this equality into equality of raw pairs with the same level,
and cancel that level using dependent Sigma equality.
This establishes equality of complete next L+ records.

This statement does NOT assign E to an arbitrary L-only B3 witness.

## New Henson corollary

For actual finite numerical H, suppose Marked is nonempty and every
marked original represents a closure node above cut; no-(I2) holds
in the SAME closure; every genuinely cut-eligible FULL original with
a positive actual L-edge to cut is marked; and the marked
selectedStagePoolPrescribedData passes corrected B3.

The representation makes the marked nonempty witness eligible:
the representing node's level is above cut and at most the genuine
original's E-free level. The new no-(I2) theorem supplies the
fibre-coherence premise required by the previously verified
henson_fullB3_of_marked_cut_neighbours_and_fibre_coherence.
Thus full corrected B3 follows.

## Hostile audit / nonclaims

1. Marked v must represent a node IN Z, not just an ambient original.
2. Identical old ordinary L-reducts are insufficient to identify Kpt
   ancestors: the source records must agree as full L+ types.
3. The two represented nodes need not be comparable; equality of
   their cut ancestors gives a common component.
4. The relevant structural exclusion is no-(I2), i.e. no meet at
   cut, rather than an unrelated no-(I1) assumption.
5. The equality is of full genuine next L+ records, stronger than
   B3's needed ordinary L-reduct equality.
6. No-(I2) must hold in the SAME Z at the SAME cut.
7. This does NOT prove the global diary's active MARKED names cover
   full auxiliary cut-neighbours. The K4 q2/x microevent warns
   against this unqualified step.
8. It does not establish full relative-profile fidelity,
   B3-loss equivalence or a common labelled inverse-source orbit.
9. No global manuscript validation marker may be upgraded.

This English proof and hostile audit precede the Lean module. Compile
it on Track D with an exact-head standard-only transitive-axiom gate.
