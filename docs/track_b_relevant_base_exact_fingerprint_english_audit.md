# KK-free Track B — EXACT finite old-base fingerprint for physical Henson sources
**14 November 2026. English mathematical proof and hostile audit committed BEFORE Lean. Stacked on PR #202.**

## Why this is stronger than the existing finite-support theorem

The pending Track B 717-report integration [PR #202](https://github.com/janhubicka/lean-kk/pull/202) proves that, for two numerical Henson L-reducts with the SAME generation parameter k and literal common source cut c, equality of both directed base graph bits on the FINITE relation `HensonRelevantBasePair k c i j` suffices for equality of complete old ordinary-L socles through c. The relevant relation holds precisely when real-copy positions `hPosition k i q` and `hPosition k j m` both lie ≤c for allowed generations q<m or q=m=k.

For physically symmetric loop-free Henson base graphs, this finite condition is actually **equivalent** to the complete old ordinary-L socle comparison. The converse is useful: it confirms the finite base-pair table neither loses information nor introduces extraneous checks, and turns a difficult structural `SameInitialL` predicate into a concrete finite fingerprint. No auxiliary E source is involved.

## Proof of the converse

Let `P,Q : HensonCutOccurrence ell c hell` be true finite physical Henson occurrences, with generation equality `P.k=Q.k`. Let
`hOld : SameInitialL P.ambient.L Q.ambient.L c`.

Fix any `HensonRelevantBasePair P.k c i j`; take its actual witness `q,m`, `i<j`, `q,m≤k`, correct exact numerical-H gate and both real positions ≤c. The old socle comparison gives equality of the **physical directed numerical-H binary atoms** at the actual real-copy coordinates:
```
hNumericBinary (normalizedGraphModel P.E).binary
  P.k (hPosition P.k i q) (hPosition P.k j m) 0 =
hNumericBinary (normalizedGraphModel Q.E).binary
  P.k (hPosition P.k i q) (hPosition P.k j m) 0.
```

The pinned successor-tree theorem
`hNumericBinary_real_forward_iff` identifies the Boolean value of each side with its corresponding base original directed edge E(i,j) whenever the exact gate holds.

Thus `P.E i j=true ↔ Q.E i j=true`; since these are Booleans, `P.E i j=Q.E i j`. Explicitly split P.E i j into `false/true`: the false branch excludes a Q=true value by the reverse implication, and the true branch uses the forward implication.

Because each physical Henson base is symmetric, also:
```
P.E j i = P.E i j = Q.E i j = Q.E j i.
```
No separate reverse-orientation successor lemma is needed, but the symmetry certificates are essential for this simplification. The result preserves BOTH directed atomic values, including FALSE bits, and works regardless of different base E outside the relevant pairs.

The forward direction of the equivalence is **already checked by parent PR #202**: relevant pairs agree ⇒ old complete L socles agree, with diagonal bits handled by genuine loop-freeness. Combining the two implications yields:
```
SameInitialL P.ambient.L Q.ambient.L c
  ↔ (∀ i j, HensonRelevantBasePair P.k c i j →
        P.E i j = Q.E i j ∧ P.E j i = Q.E j i).
```

## Actual-run specialization

For P,Q genuine `HensonPhysicalRunCutData ell hell c`, their physical occurrences satisfy HensonCutOccurrence including symmetry and loop-freeness automatically. If P.k=Q.k, the same IFF holds for their old finite numerical-H prefixes, regardless of different seed sets, Kpt closures, maintained source-index cardinalities, chosen monoid maps or auxiliary E records.

Combining the exact finite old-base fingerprint with the verified two-run live cut-star comparison gives an exact *source-old* physical certificate, but NOT a characterization of full B3 by old atoms alone: the projected COMPLETE upper ordinary-L cut-star spectrum must additionally match, independently.

## Adversarial checks (13)

1. The relevant pair must have ACTUAL allowed numerical-H generations q,m and both REAL positions ≤c; an arbitrary base edge with indices i,j≤c may be irrelevant.
2. The generated H binary bit equals the base directed edge only with the correct gate; the checked `hNumericBinary_real_forward_iff` supplies both directions.
3. Symmetry of P.E and Q.E is used to infer reversed directed base atom equality. Generic directed signature structures without symmetry require a separate reverse-orientation check.
4. Loop-freeness enters the *sufficient* direction to identify base diagonal singleton bits; the converse checks off-diagonal relevant base pairs.
5. P.k=Q.k is an explicit hypothesis; different generation parameters change physical positions and gates.
6. The source-coordinate c is LITERAL, not an arbitrary index in the selected diary or a target embedding.
7. Both finite physical carriers contain c by `P.hCut` and `Q.hCut`.
8. All FALSE bits are preserved: equality of Booleans is proved by true-bit equivalence, not by inclusion of positive edge sets alone.
9. The relevant base-pair table is finite because i<j≤c, but may grow with the physical cut; no diary-uniform finite bound follows.
10. Equality of old L socles does not imply equality of auxiliary E, Kpt meet/parameter closure, structural I1/I2 or selected level sets.
11. The K4 q2 auxiliary cut-neighbour remains an independent UPPER cut-star datum even when all old relevant base edges agree.
12. The refined diary has not yet been proved to encode/transport this exact finite table across different physical source cuts.
13. No relative-continuation B3-loss bridge, labelled common inverse-source orbit, exact BRD upper bound or independently unavoidable lower bound follows.

## Verification gate

English FIRST; two named endpoints in `Kk/B3RelevantBaseExactFingerprint.lean`: exact IFF for two physical `HensonCutOccurrence` sources, and actual-run specialization for `HensonPhysicalRunCutData`. Stacked after PR #202, whose expected 717-report full source gate is still pending at writing. This adds **2** endpoints for expected **719** standard-only named reports on that frozen source, subject to later Track G/A/C/D/E/F merges. Require exact-head `lake build`, parser self-test, only `propext`, `Classical.choice`, `Quot.sound`, no sorryAx. Keep the paper's global markers pending and black text frozen.
