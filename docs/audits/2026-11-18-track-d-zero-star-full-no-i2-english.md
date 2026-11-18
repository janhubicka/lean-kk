# Track D — actual full zero ordinary cut-star excludes strict dependent Kpt forks
18 November 2026. English proof and adversarial audit BEFORE Lean.

## Theorem 1: no full strict I2 fork

Let A be one finite EnumeratedPartialStructure in the graph signature
(binary L, zero unary symbols, one diagonal) with symmetric ordinary
L, and let family be a normalized forbidden family avoided by A.L.
Let Z be any set of genuine admissible Kpt nodes; in applications
it is the full closure at one true AlgorithmRun cut.

Let original : Fin M -> Fin A.size be a finite actual-original-name
enumeration EXHAUSTIVE for Z: each z in Z is a prefix of
A.kptOriginal(original i) for some i. Fix cut c.
Assume that for every original name i representing an actual z in Z
which strictly crosses c, the ordinary L bit L_A(c,original i) is
FALSE. In particular this quantifies over all generated parameter
and meet sources, not a selected-front shadow.

Conclusion: NOT KptFullCutFork family Z c.

Proof. Suppose a,b in Z strictly cross c with equal COMPLETE old
dependent raw Kpt records and different COMPLETE next raw records.
By exhaustive true original source coverage choose i,j such that
a <= A.kptOriginal(original i) and
b <= A.kptOriginal(original j).
Because a,b strictly cross c, the full original free E levels
reach c+1 by verified kptBelowOriginal_level_le_free.
Thus i,j are actual closureSelectedOriginal names and the zero
L-cut hypothesis applies to both.

Verified kptBelowOriginal_ancestor_raw identifies each actual Kpt
ancestor at c and c+1 with the literal A.partialTypeAt records
of its physical representative. Independently, verified
kpt_full_old_upper_types_of_crossing identifies the two optional
raw Kpt records with those same ancestors. Compose the old
equalities to obtain equality of complete old physical dependent
types A.partialTypeAt c (original i) and A.partialTypeAt c (original j).

Apply the just verified zero-column primitive,
full_zero_ordinary_cut_column_determines_next_type. Its premises
hold because both physical representatives reach c+1, the old
dependent types coincide, and both ordinary L cut bits vanish.
The complete NEXT physical dependent L+/E partial types are equal.
Compose with Kpt upper ancestor equalities: the two Kpt upper
raw records coincide, contradicting their supposed inequality.
Thus no strict full Kpt fork exists, without any no-I1 assumption.

## Corollary 2: no I2 once no I1

Assume separately that Z has no node whose level is c.
By verified kpt_no_I1_I2_iff_complete_full_fork, a competing
same-component cut-level Kpt meet (I2) is EQUIVALENT to a strict
full old-equal, next-different L+/E fork, given no-I1.
The previous theorem excludes such forks. Hence no I2 at c.

No-I1 is indispensable: an actual node ending at c gives the
trivial self-meet I1 but does not strictly cross c. A zero ordinary
cut-star alone does not exclude such a terminal node.

## Application and strongest supported claim

The already verified Track D empty physical cut-star theorem
for isolated dummy bases, and the separate one for lower generations
of selected coding vertices under a descending Plan stage hypothesis,
supply the source zero-column input on their entire actual stage pool.
Track D source representation supplies the exhaustive actual
finite stage names. Therefore, once the new no-fork theorem is
formally composed with those existing results, these two cut
families will have no-I2 AUTOMATICALLY under no-I1.
The global full-pool boringness lemma is NOT proved: no-I1 itself,
the chronological descending Plan induction, and the other omitted
auxiliary/nonselected-coded marked B3 cases remain open.

## Adversarial checks (18)

1. Both future sources live in the SAME A.
2. Every z in Z including meets and E parameters has an ORIGINAL name.
3. The stage source is closure(Run.I(c+1),X), not selected ages.
4. The zero condition checks ALL closure-selected original names.
5. The two physical representatives can have the same type; no
   injective type-enumeration or unique recipe is assumed.
6. Strict crossing gives c+1 <= each physical free E level.
7. E(c,original) is TRUE, never set to zero by ordinary-L emptiness.
8. Reverse E(original,c) is FALSE by SpacedE.
9. L symmetry is essential to control the reverse ordinary cut bit.
10. Every false atom of the complete old L+/E type is retained.
11. Both old and next ancestors come from the SAME physical original.
12. The full fork refers to exact Option(RawPartialTypeNode) records.
13. No comparison is made across different physical sources or cuts.
14. No E is attached to a separate L-only B3 continuation witness.
15. Strict forks do not include trivial I1 self-meets.
16. No-I1 is used only in the fork-to-I2 reverse classification.
17. Genuine K4 auxiliary microcuts 10 and 22 remain regression cases.
18. No all-cuts Plan theorem, common labelled inverse orbit or BRD
    count is promoted.

Formalization: new independent module imports the verified zero-column
primitive and the exact Kpt full-fork classifier; its first theorem
is no FULL strict fork, second theorem no full competing meet if no-I1.
Only standard axioms allowed; dedicated and full CI required.
