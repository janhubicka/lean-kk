# Track C — I2 versus a full dependent L+ fork (English proof and adversarial audit)
**14 November 2026. Proof and hostile review BEFORE the Lean module.**
Baseline: merged Track C #99/#109/#114 and integrated `lean-kk/main` `498b83ec77871b5efd9c38c7a75491cbc261f6c9` (successful full main build). Work exclusively in the new Track-C branch; no manuscript/protected text changes.

## Issue addressed

The existing `FullPhysicalClosureCrossing` relation is meaningful even at a competing (I2) cut, and Track E proves that a *fork* (the same old full L+ type with two distinct next types) forces a cut-level meet. However, the reverse implication is false in general because an (I1) node **at the cut** also gives a trivial meet witness if the meet test allows `a=b`.

The correct exact statement is: **in the absence of (I1), a competing cut-level meet exists IF AND ONLY IF the entire actual Kpt crossing relation is nonfunctional.** We can express the fork directly using Track C's two already verified optional *complete raw old/upper L+ records*, then turn it into a finite active-index witness using the actual AlgorithmRun `presentAt` mask.

## C17: the correct intrinsic full-source fork

Let `family` be any normalized forbidden family, `Z : Set (AdmissibleKptNode family)` any genuine set of admissible Kpt nodes, and `p : Nat` any cut. Define

`KptCompleteCutFork family Z p` iff there are `a,b∈Z` satisfying
`p<lev a`, `p<lev b`,
`kptFullOldAtCut a p = kptFullOldAtCut b p` but
`kptFullUpperAtCut a p ≠ kptFullUpperAtCut b p`.

These are WHOLE `RawPartialTypeNode db du dd` values, not only ordinary L-reducts. In particular, their auxiliary E-incidences, negative L bits, unary/diagonal data and fake E-predecessor bits are retained.

Let `I1(Z,p)` mean `∃z∈Z, lev z=p`, and let the **literal no-(I2) competing-meet obstruction** be
`I2Meet(Z,p) := ∃a,b∈Z, SameComponent(a,b) ∧ lev(meet(a,b))=p`.

### Theorem (mathematical)

1. **Any full fork forces I2Meet**, without any no-(I1) premise.
2. **I2Meet and no I1 implies a full fork.** Consequently under `¬I1(Z,p)`, `I2Meet(Z,p) ↔ KptCompleteCutFork family Z p`.
3. Equivalently, for arbitrary Z without no-I1:
   `I2Meet(Z,p) → I1(Z,p) ∨ KptCompleteCutFork family Z p`.
   The converse from I1 alone is not needed here, since the genuine Algorithm 5.4 trichotomy prioritizes I1.

### Proof

**Fork ⇒ meet.** Unpack `kptFullOldAtCut` and `kptFullUpperAtCut` using the proven exact-ancestor lemmas. Equality of old option records yields equality of the actual Kpt ancestors at p (equality of subtype raw data). Unequal upper options yields different ancestors at p+1. Apply `SMTree.Envelope.meet_level_eq_of_nextPrefix_ne` from the genuine successor-tree library, so `lev(meet(a,b))=p`. The common ancestor at p is a witness to `SameComponent(a,b)`.

**Meet + no I1 ⇒ fork.** Let m=meet(a,b) be the actual meet at level p. Because m≤a,b, both nodes have level ≥p. Since no node of Z has level p, both are strictly above p. Unique-ancestor-at-level (`LevelTree.eq_ancestor_of_le`) shows
`ancestor(a,p)=m=ancestor(b,p)`; hence the old options coincide. The next ancestors must differ: if `ancestor(a,p+1)=ancestor(b,p+1)=u`, then u≤a,b so u≤m by `LevelTree.le_meet`; but lev u=p+1>lev m=p, contradiction. Therefore their complete upper options differ.

**I2 without no I1.** If either original witness itself has level p, we have I1. Otherwise the previous argument constructs the full fork. This exhausts the cases and correctly treats trivial meets.

## C18: finite indexed fork = actual full Kpt fork

Fix a genuine `Finset params` of *actual Kpt nodes*, injectively named by `(params.equivFin.symm j).val`; an actual subset Z covered by params; and a Boolean `present : Fin params.card → Bool` satisfying
`present j=true ↔ (params.equivFin.symm j).val∈Z`.

Then `KptCompleteCutFork family Z p` iff there exist two indices i,j whose `present` values are true, both named nodes cross p, their complete old options agree, and their complete upper options differ.

**Proof.** For a fork a,b, the assumed exact params coverage gives `a,b∈params`. Use the canonical finite equivalence `params.equivFin` to choose their indices, and the definition of the mask gives active flags. Conversely, active named nodes provide a,b in Z, satisfying the same fork equations. Multiple meet *recipes* naming the same actual node do not produce spurious duplicates: the index names Kpt nodes themselves.

## C19: actual numerical H+ AlgorithmRun specialization

Let A=finiteNumericH K k N, let its forbidden family be avoided, let X be the genuine Kpt initial seeds represented by an original prefix pool U, and let R be a true AlgorithmRun of height H. Let params and `presentAt` be the exact *single* final-closure index/mask from merged Track C PR #109, so for all cut<H:
`presentAt cut j=true ↔ node(j)∈Z_cut`,
where `Z_cut=closure (admissibleKptSTree family) (R.I(cut+1)) X`.

Then under the **explicit** no-(I1) hypothesis for that *same* Z_cut,
`I2Meet(Z_cut,cut)` is equivalent to a fork among two *active* indices with the complete old and upper L+ records of merged PR #114. This is a finite, exact, physical microevent certificate with no selected-shadow projection.

No event is asserted to occur: this is a decision/equivalence interface, not a proof that every cut is I2, nor that all auxiliary levels are boring.

## Adversarial checks

1. **I1 exception is essential.** A single node z at level p has a trivial meet at p with itself; it does NOT give two different upper records and does not cross p. Never assert I2Meet↔fork unconditionally.
2. `SameComponent` is required before using `meet_le_left/right`; the total meet on unrelated forest components falls back to an argument.
3. Both fork witnesses must satisfy strict `p<lev`; mere final-closure membership does not certify an upper ancestor.
4. Old equalities and upper inequalities concern WHOLE raw dependent L+ types, not only plain graph-age signatures.
5. The fork's two upper records must differ; two distinct names with identical upper records are NOT an I2 witness.
6. Indexing nodes, not original names or meet recipes, prevents double counting nonunique meet decompositions.
7. The mask uses the actual pre-cut `R.I(p+1)`, not `R.I 0` membership alone.
8. `params` includes all seed, positive parameter and meet nodes; it must *cover* the entire pre-cut Z, not merely selected originals.
9. No equality between indices from different AlgorithmRuns or different H+ structures follows.
10. The statement is at a common *source* cut; numerical target gaps can be different in distinct occurrences.
11. A complete physical fork test does not itself determine corrected B3 or the interesting-event order; I3 remains a distinct classification.
12. The existing K4 physical cuts 10 and 22 remain hostile regressions: the new test must never deem them boring from a selected-shadow age.
13. Finite-source certificates do not prove a uniform bound on the number of event levels or higher-generation original names.
14. No arbitrary L-only B3 witness gains an auxiliary E expansion in these proofs.
15. Multi-root physical stage preservation still depends on proving the actual next-seed premise and complete old/new L+ columns in the recursive diary.
16. No global labelled source orbit, Ramsey bound or BRD characterization is inferred by the local fork classification.

## Acceptance

Prove in `Kk/NumericHI2FullFork.lean`, with exact named standard-only axiom reports and isolated `lake build Kk.NumericHI2FullFork`, then record the true scoped conditional theorem for Track D/E integration. Do not edit shared `Kk.lean`, central 535-report registry, or protected manuscript prose.
