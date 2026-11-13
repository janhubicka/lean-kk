# KK-free Track B — cut-star compression of the FULL corrected-(B3) test
**13 November 2026. English proof written before any Lean source.**

## Main insight: a small exact B3 profile, not selected graph-age projection

At a finite Henson K_ell-free source and an actual Kpt parameter-closed cut c with **no (I2) competing meet**, the corrected-(B3) test over *every* genuine closure-selected original is equivalent to the same test over **only those closure-selected original names physically adjacent to c, plus one genuine anchor name**. The anchor makes the marked source nonempty and carries the common old ordinary-L socle. It is NOT an arbitrary source: the anchor is required to represent an actual closure node strictly above c.

This is stronger than the previous conditional one-sided marked⇒full transfer, yet avoids the false general claim that the selected macrodiary's graph-age F alone determines the full B3 profile. We do not need to assume structural no-(I1), that c is selected/interesting, or any global resolved diary.

## Exact finite theorem

Fix ell≥2, k with ell≤k+1, a symmetric loop-free K_ell-free source graph E and finite numerical Henson structure
`A=finiteNumericH(normalizedGraphModel E,k,N)`, with a true family-avoidance certificate. Choose a full Kpt closure `Z`, an actual name map `original : Fin M→Fin N`, a tested c<N, and exclude full-closure (I2) at c.

Define the **genuine full source selection**
`Full(v) := closureSelectedOriginal family A hAvoid original Z c v`.

Choose an **actual full selected anchor** a∈Fin M with `Full(a)`. Define
```
Star(v) := Full(v) ∧
  (A.L.binary c (original v) = true  ∨  v = a).
```
This is a cut-star plus ONE anchor, not all Kpt parameter-positive originals and not an arbitrary full upper-type saturation.

**Theorem:** 
```
(selectedStagePoolPrescribedData A c original Full).CorrectedB3 family
  ↔
(selectedStagePoolPrescribedData A c original Star).CorrectedB3 family.
```

### Proof, forward direction (FULL passing ⇒ Star passing)

The verification does not silently assume that the `selectedStagePoolPrescribedData` constructor uses the same next type for every original sharing its old type. Instead apply the verified Track D no-(I2) cut-visible transfer with its `Full` argument set to **Star** and its `Marked` argument set to **Full**.

The marked Full pool is nonempty (a∈Full) and every one of its names genuinely represents a closure crossing, tautologically. No-(I2) makes all chosen next-type source fibres agree in complete L+. Every cut-neighbour in Star is in Full by definition, so Track D's cut-neighbour coverage hypothesis is immediate. Hence passing full B3 implies passing Star B3.

### Proof, reverse direction (Star passing ⇒ FULL passing)

Apply the SAME Track D theorem in the other direction. The marked Star pool is nonempty because a∈Star by its right-hand disjunct v=a, and every Star name lies in genuine Full closure by its left-hand conjunction. If any Full name is cut-eligible and has a positive physical L-edge to c, its name lies in Star by the left-hand disjunct. No-(I2) again forces full next-type fibre coherence. Thus a passing Star B3 test implies passing Full B3.

This is an **iff with no unproved upper-L-spectrum equality** and no freely chosen future-to-future L-edge assumption. Upper-type equivalence is only **as it affects B3**, not equality of the full raw spectra or of event-indexed labelled L+ source records. Off-cut auxiliary originals may still be required by I1/I2, meet parameters or labelled source orbits.

## Actual AlgorithmRun corollary

Let Z be *exactly* `Envelope.closure (admissibleKptSTree family) (Run.I(c+1)) X`. Supply the genuine selected anchor and no-(I2) on this Z. Instantiating the finite theorem gives an actual-run cut-star reduction. It does not require c∈Run.I 0 or I1 exclusion, because it is a statement about B3 alone at this full source.

## Final maintained-pool numerical-H corollary

Assume an actual finite Henson AlgorithmRun seeded from the genuine U originals. Let `V=hStageOriginals(normalizedGraphModel E) k N U (Run.I 0)` with `original=hOriginalName V`. The already checked Track C
`finiteNumericH_run_final_pool_crossing_and_upper_types` (same Z, no-I2) proves the canonical closureSelectedBoringData genuinely **CoversClosureCrossing** and **IsCrossingGraphOf** its whole source, rather than merely listing arbitrary ambient names. Combine with cut-star equivalence to obtain a *source-correct* B3 compression in the exact finite maintained name universe.

The anchor is still an explicit hypothesis. If the source is empty, the full B3 test is vacuous, and the nonempty marked transfer does not apply; the empty case should be handled separately rather than assuming an anchor.

## Adversarial audit: failure modes ruled out

1. **Not the selected diary:** Star includes ALL physically cut-adjacent, full closure-selected auxiliary originals, even if none are canonical active branches.
2. **No-(I2) is essential:** duplicate old full L+ source types may have different next L+ targets. Track D's selected-fibre theorem discharges this only when no competing meet occurs at c.
3. **Anchor is genuine:** a must satisfy Full(a), not merely belong to Fin M or have a positive free level.
4. **Nonempty source:** a supplies nonemptiness on BOTH sides. Do not invoke the no-(I2) transfer with a vacuous empty marked source.
5. **No-(I1) unnecessary:** the B3 predicate exists even at an I1-level, but this equivalence does NOT authorize skipping an I1 event.
6. **No selection necessary:** the statement is stage-local at the actual closure, not “c was an I3 event.”
7. **B3 asymmetry/loop patterns:** the Henson forbidden family includes loops/asymmetry; Track D's small-clique-core argument reduces actual failed B3 to cliques using the genuine graph-language assumptions.
8. **Real L not E:** cut adjacency is the positive actual ordinary L bit, never inferred from an incoming E value. Odd fake coordinates are not included just because their E columns are positive.
9. **Upper–upper continuations free:** future-to-future edges in B3 continuation W are arbitrary; only the cut–future adjacency is forced by the complete prescribed upper L-type.
10. **Deduplicated chosen next target:** neither proof assumes marked prescribed target equals the next type of an arbitrary chosen name. No-(I2) handles exactly this issue.
11. **Source index:** actual-run pre-cut closure uses Run.I(c+1); maintained pool uses Run.I 0. Do not exchange.
12. **Full closure representation:** the numerical-H corollary uses the actual run seed-prefix invariant and final maintained pool to verify CoversClosureCrossing and IsCrossingGraphOf.
13. **No global orbit:** equality of B3 *truth values* is far weaker than equality of complete L+ event frames, source-parameter incidences and common labelled inverse images.
14. **No monotonic-age shortcut:** neither proof uses the selected graph-age F or assumes abstract feasible labelled clique vectors realize arbitrary old-prefix extensions.
15. **Physical assumptions explicit:** loop-free symmetry, K_ell avoidance, ell≥2, ell≤k+1, c<N, and no-I2 are retained.
16. **No upper-spectrum equality asserted:** Star may remove complete upper types nonadjacent to c; the theorem states only the corrected-(B3) equivalence.
17. **Cut-star potentially not canonical:** which original labels are physically cut-neighbours still depends on the actual resolved H+ copy. Further work is needed to show that their profile is determined by a finite intrinsic diary.
18. **K4 regression:** the actual cut10 q2 auxiliary cut-neighbour must be included if selected x-only B3 passes and full B3 fails. The compression does NOT discard q2.
19. **Black manuscript protected:** any eventual textual marker belongs only in olive text and must explicitly retain the full diary/open-orbit caveats.
20. **Validation discipline:** exact Lean kernel proof + full CI and standard-only axiom check required; the global B3 projection and exact big Ramsey degrees remain pending.

## Proposed Lean endpoints

1. `henson_closureB3_iff_cutStarB3`: exact finite full closure source ↔ its cut-star anchored restriction under no-I2.
2. `henson_algorithmRun_B3_iff_cutStarB3`: exact actual pre-cut AlgorithmRun source.
3. `henson_numericH_run_finalPool_cutStar_B3_equivalence`: the exact canonical full crossing of the final maintained finite numeric-H original pool, with both crossing/graph correctness and B3 equivalence.

After the independent previous Track B PR #106, the expected strict full-project audit gate is **478** named standard-only reports (475 +3). Pending actual CI; no assumption that this is an unconditional diary theorem.
