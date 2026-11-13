# Track B — complete upper-L-reduct profile is sufficient for finite corrected (B3)
**13 November 2026. English proof committed BEFORE Lean code.**

## The actual problem being reduced

The verified corrected-(B3) predicate `PrescribedBoringData.CorrectedB3` tests arbitrary finite **ordinary-L** continuations over an old ordinary-L socle, with each future vertex assigned one of the prescribed COMPLETE upper ordinary-L reducts. Auxiliary E-records determine which Kpt source nodes and original names are present, but B3's finite continuation does not itself have E.

The prior merged Track B PRs #95 and #100 establish that two **nonempty, genuinely cut-eligible selected original-name pools in one and the same ambient enumerated partial structure A** automatically have mutually matching old ordinary-L socles, and that a full I3 failure hidden from a passing marked profile forces an extra concrete upper L-reduct. The present proof supplies the positive/sufficient direction and a useful exact equivalence.

## A. One-sided actual selected-stage sufficient criterion

Let `A : EnumeratedPartialStructure db du dd` with `p<A.size`, `original : Fin M → Fin A.size`, and two selected-name predicates `Full, Marked : Fin M → Prop`. Let
`F := selectedStagePoolPrescribedData A p original Full`,
`G := selectedStagePoolPrescribedData A p original Marked`.

Assume a **real eligible marked representative** `w`, i.e. `Marked w` and `p+1≤A.freeLevel(original w)`. Suppose for every complete upper L-reduct R
```
F.PrescribedUpperLType R → G.PrescribedUpperLType R.
```
Then the previous verified `selectedStagePool_full_to_marked_Lsocle_coverage` supplies precisely the F→G old-L-socle premise of `correctedB3_of_Lprofile_dominance`. Therefore
```
G.CorrectedB3 family → F.CorrectedB3 family.
```

This is a sufficient **full-source** B3 test; it is not merely selected-shadow graph-age equality. The complete upper type inclusion is a substantive test, false for the x-only marked profile of the actual K4 q2/x cut-10 gadget.

## B. Exact equivalence for identical upper-L profiles

If BOTH selected-name predicates have an eligible representative, apply the previous old-socle coverage theorem twice (F→G, G→F). If their complete upper-L-reduct predicates agree pointwise:
```
∀ R, F.PrescribedUpperLType R ↔ G.PrescribedUpperLType R,
```
then `correctedB3_iff_of_equal_Lprofiles` gives
```
F.CorrectedB3 family ↔ G.CorrectedB3 family.
```
No equality of individual L+ type vertices, E columns, or source-name sets is required. The result is about corrected B3 alone, not equivalence of full envelopes or their labelled inverse-source orbits.

## C. Genuine closure-selected source, not arbitrary all-eligible pool

Fix a genuine Kpt admissible finite ambient source A and a closure set Z. The verified successor-tree construction defines
`closureSelectedBoringData family A hAvoid original Z p` **definitionally** as the selected-stage pool for
`closureSelectedOriginal family A hAvoid original Z p`. Apply Theorem A directly to this true full crossing. If a nonempty eligible marked pool's B3 test passes and all complete upper L-reducts of the true closure crossing are permitted by the marked pool, the full closure's corrected B3 passes. This is the exact conditional positive direction needed to exclude an auxiliary I3 obstruction.

It does **not** assert the full chosen source graph is uniquely determined by the selected macrodiary. That is the genuinely unproved global task.

## D. Physical name-based upper-cover interface

A practical sufficient hypothesis for `F.PrescribedUpperLType⊆G.PrescribedUpperLType` is:
for **every full selected source type S∈F.source**, choose a REAL marked eligible name v such that the COMPLETE next-level upper L-reduct of **the actual chosen** F.target(S) equals the complete upper L-reduct of G.target(A.partialTypeAt p (original v)). Then each R permitted by F has a witness S; choose v by the hypothesis, put T=A.partialTypeAt p (original v), show T∈G.source by *both* Marked v and its free-cut eligibility, and rewrite the upper reduct equality. Feed the resulting inclusion into Theorem A.

**Crucial:** one cannot replace `G.target T` by `A.partialTypeAt (p+1) (original v)` for an arbitrary marked v if multiple names share an old type: the selected-stage constructor chooses a representative, and another name can have a different next type without (I2) control. The theorem explicitly compares the CHOSEN targets.

## Adversarial checklist

1. The old L socle is common only because F and G are extracted from ONE A at ONE cut and there is an eligible marked witness.
2. `p<A.size` is needed to make the induced old L-socle an actual ambient prefix.
3. `Marked w` alone is insufficient: require `p+1≤freeLevel(original w)`.
4. If either pool is empty, two-way age-test equivalence cannot be inferred from a bare L-profile equality via this nonempty proof; the empty case must be handled independently.
5. One-sided dominance must go **full source → marked source** and **full upper types → marked upper types** to conclude marked B3 implies full B3; reverse would be false.
6. `PrescribedUpperLType` ranges over complete upper L-reduct types at p+1, not selected graph-age support vectors or just positive adjacency bits.
7. Ordinary-L age witnesses have arbitrary upper–upper edges. No attempt is made to make their upper part an induced subgraph of the ambient A.
8. The result does not discard E from the Kpt *source/selection* data. It merely observes that once the source profiles have been determined, corrected B3 tests L-only continuations.
9. For two occurrences in DIFFERENT ambient models, the common-socle argument is unavailable without an independent L-socle isomorphism.
10. The real K4 gadget's q2 auxiliary upper type proves that the full→x-only inclusion may FAIL; do not mark an unconditional macrodiary B3 projection green.
11. The physical name-based cover must use the chosen `target T` of G; duplicate old types with different next types are a real danger and require no-I2 in later geometrical applications.
12. Equality of corrected B3 tests does not imply equality of full L+ envelope records or a common labelled inverse-source monoid orbit.
13. The unbounded resolved diary and exact K_k-free Ramsey upper/lower bounds remain open.
14. New markers must be scoped as **interfaces** until the upper-type cover is actually discharged for all canonical resolved-copy events.

## Verification requirements

Four exact theorem endpoints are proposed in `Kk/B3UpperProfileSufficiency.lean`, backed by the existing verified `Kk.B3ReductProfile` and merged Track B selected-source theorem. Baseline at merged PR #100 is **413** exact standard-only axiom reports; new gate is **417**, full hosted `lake build`, parser self-test, standard-only axiom reports. Do not edit protected manuscript black prose.
