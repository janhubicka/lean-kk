# Track B — TWO actual Henson AlgorithmRuns over DIFFERENT base graphs
**14 November 2026. English proof and adversarial audit committed BEFORE Lean.**

## New mathematical interface

The kernel-checked Track B [PR #180](https://github.com/janhubicka/lean-kk/pull/180) constructs two actual finite Henson AlgorithmRuns, with independent seeds, final original-name pools, Kpt closures and finite active-node indexes, and transfers their complete corrected-(B3) tests via bilateral live physical positive-cut upper-L matching. However its `HensonRunCutData` type assumes the SAME physical base graph E and generation k. Consequently a shared old ordinary-L prefix is automatic, but this precludes directly comparing two different graph presentations.

[PR #186](https://github.com/janhubicka/lean-kk/pull/186), verified by 652-report full run [43620701899](https://github.com/janhubicka/lean-kk/actions/runs/43620701899), produces an actual live unmatched physical Kpt node from a full corrected B3 discrepancy, still assuming the same base E and k.

Here we remove the same-base assumption **without fabricating an old-L isomorphism or source-rank transport**. We allow two actual finite Henson sources with independent E and k and require, as a separate geometric hypothesis, the EXACT common old ordinary-L socle at ONE common literal source cut. This is strictly more general than the same-base two-run theorem and is directly compatible with the earlier physically verified cross-ambient cut-star comparison.

## Data

Fix only a forbidden-clique parameter `ell≥2`, a proof hell and one actual source-coordinate cut c. Define `HensonPhysicalRunCutData ell hell c` with:
* an independent numerical generation parameter k, bound `ell ≤ k+1`;
* an independent ordinary graph E and physical no-loops, symmetry and K_ell-freeness proofs;
* its own finite carrier size N with c<N, physical Henson forbidden-family avoidance;
* an actual finite original seed pool U, Kpt seed set X and **real original-prefix seed representation** `hX : X ⊆ ambientPrefixPool family (finiteNumericH ... N) ... U`;
* a REAL `AlgorithmRun (normalizedKptSMTree family) X top`, with c<top;
* genuine no competing (I2) on the exact pre-cut meet/parameter closure `closure ... (run.I(c+1)) X`.

This type is not a surrogate `PrescribedBoringData`, nor does it permit a fabricated subset of its closure or arbitrary E on a future age-test witness.

Its `occurrence : HensonCutOccurrence ell c hell` is constructed using the already verified `actualHensonRunCutOccurrence`. Its `Full` selector is **definitionally** the entire `closureSelectedOriginal` predicate over final maintained originals; every actual pre-cut Kpt node has a representing original by the true AlgorithmRun invariant.

## Theorem 1 — exhaustive genuine physical sources for both distinct base graphs

For any P, extract `∀v, P.occurrence.Full v ↔ closureSelectedOriginal ... v` from verified `actualHensonRunCutOccurrence_fullExact`. Separately extract `∀z∈P.occurrence.Z, ∃ v, z≤P.occurrence.ambient.kptOriginal(...v)` from `actualHensonRunCutOccurrence_poolExhaustive` with P.hX and P.hBelow.

This discharges BOTH source coverage requirements of `HensonCutOccurrence.full_B3_crossAmbient_iff_of_intrinsic_physical_cutStar`, even with different E,k,N,X,U and run choices. Do not substitute the old one-sided hRepresented field for both certificates.

## Theorem 2 — corrected B3 comparison with only an explicit old-L prefix alignment

For TWO arbitrary genuine P,Q of this type, suppose
`hOld : SameInitialL P.occurrence.ambient.L Q.occurrence.ambient.L c`
and
`hCutStar : ∀R, PhysicalCutStarUpperL family P.occurrence.Z c R ↔ PhysicalCutStarUpperL family Q.occurrence.Z c R`.

Then the verified cross-ambient theorem `HensonCutOccurrence.full_B3_crossAmbient_iff_of_intrinsic_physical_cutStar`, supplied with the DERIVED exact source/exhaustive pool certificates for each run, gives:
```
P.occurrence.fullProfile.CorrectedB3 family ↔
Q.occurrence.fullProfile.CorrectedB3 family.
```

Different **physical E, k, truncation sizes, seed sets, full closures and real finite Kpt-node index cardinalities** are allowed. Old-L prefix matching remains a genuine premise, not guessed from selected macrodiary F or graph isomorphism, and the shared source coordinate c is fixed by the type.

## Theorem 3 — finite bilateral real live Kpt-node matching suffices, different E and k

Use the verified `numericH_actual_run_all_cuts_indexed_cutStar` for each P, Q separately, taking K=normalizedGraphModel P.E resp. Q.E and their own k,N,U,X,hX,top,run. It constructs `paramsP,liveP,paramsQ,liveQ`, each exactly enumerating all actual final Kpt closure nodes, and gives equality between each projected live-index cut-star spectrum and that occurrence's intrinsic `PhysicalCutStarUpperL` predicate at c.

If `IndexedCutStarLiveCover Pidx Qidx c ∧ IndexedCutStarLiveCover Qidx Pidx c`, the already verified `indexed_cutStar_iff_of_bilateral_live_cover` gives equality of projected complete next ordinary-L positive-cut types. Transport via the two physical projection equalities and invoke Theorem 2. This is a TRUE finite two-run transfer that does **not** require same E,k, name sets or full OLD+UPPER L+ crossing relations.

The live cover is a many-to-one relation matching only the actual upper ordinary-L type of genuinely live Kpt cut-crossing nodes with a positive ORDINARY-L edge at c. Do not require equality of old E values, source node multiplicity, or complete Kpt source relations, and do not count fake E-positive coordinates as L-neighbours.

## Theorem 4 — a real unmatched live physical node from disagreement between different bases

Suppose P full corrected B3 fails and Q passes, with the same old-L alignment hOld. Apply the *already verified generic cross-ambient* `HensonCutOccurrence.failing_full_B3_has_unmatched_cutStar_original` to their TRUE occurrences: obtain a real cut-eligible positive-L-adjacent full closure original v in P whose complete next upper L-reduct R is not in Q's permitted cut-star type spectrum.

By `star_name_complete_upperL_permitted`, R is in P's actual cut-star source. By the verified exhaustive-source projection equivalences and each true finite Kpt-index exactness, R is realized by a true live j of P with both complete old/upper dependent L+ raw Kpt ancestor records and a positive ORDINARY-L cut edge, but it is not realized by ANY true live cut-crossing Kpt node of Q. Thus
```
∃ true finite Kpt indexes Pidx,Qidx,
  UnmatchedLiveCutStarNode family Pidx Qidx c.
```
This strengthens the prior two-run mismatch theorem by removing the common physical base E/k, but still explicitly requires common OLD ordinary-L socles and literal source coordinate c.

## Hostile audit (18 points)

1. P,Q may use DIFFERENT graphs E; old-L prefix alignment is an independent hypothesis, not implied by selected F or the fact that both are K_ell-free.
2. P,Q may use DIFFERENT numerical generation parameters k; do not rewrite one physical E/cut type into the other without an explicit map.
3. The cut c is ONE identical source coordinate, not arbitrary target gap positions; differing source ranks need a separate type-correct reindexing theorem.
4. Genuine `hX` original-prefix representation is required for EVERY seed of each run; do not postulate source exhaustiveness from an arbitrary run.
5. The pre-cut closure is `Run.I(c+1)`, while final maintained ORIGINAL names use `Run.I 0`.
6. Full no-(I2) is assumed separately on each actual pre-cut closure, not inferred from the absence of selected-front meet events; it makes the prescribed B3 source-to-target function valid.
7. Exact Full name membership and exhaustive full original-prefix coverage are DIFFERENT certificates, both derived here.
8. The two finite Kpt node `params` indexes include generated parameter and meet nodes and may have different cardinality from each other and from the selected original-name index.
9. A live bit alone is not a crossing: both old and upper `some` Kpt ancestor records must come from the SAME indexed physical Kpt node.
10. The cut-neighbour test is an ordinary-L positive edge, NOT an auxiliary E or fake coordinate.
11. Matching preserves complete NEXT ordinary-L reduct, including every positive and negative directed atomic bit, unary/diagonal parts, not merely the cut-edge itself.
12. Off-cut upper types and old E-dependent Kpt type pairs are not required to match for this local B3 test; full envelope/orbit comparison remains strictly stronger.
13. An ordinary-L corrected-B3 future witness has arbitrary upper-upper edges; do not transplant physical ambient future-future edges.
14. Empty cut-stars and duplicate upper L types are allowed, with no dummy anchor or bijection.
15. This is a local corrected-B3 truth-value comparison; structural I1/I2 and full dependent L+ source event trace remain open.
16. Refined diary occurrence-to-occurrence cut transport, physical old prefix alignment and live cut-star matching are NOT proved by these conditional theorems.
17. K4 genuine auxiliary q2-type cut neighbour remains visible and cannot be omitted because the selected macrodiary F is unchanged.
18. No common labelled inverse-source monoid orbit, fixed-source relative-continuation/B3-loss equivalence or independently unavoidable exact BRD formula follows.

## Verification gate

Commit this English proof BEFORE Lean. Formalize four named theorem endpoints in `Kk/B3DifferentBaseActualRuns.lean`, register them in the exact shared `Kk.lean` and `scripts/check_axioms.lean`. Latest merged main `007a635fb35a16be0c584693ea3a591deb45bdea` passed 652 named standard-only reports at [hosted full run 43620701899](https://github.com/janhubicka/lean-kk/actions/runs/43620701899) on an identical tested Git tree. Four new public endpoints target **656 exact** named standard-only transitive-axiom reports, full `lake build` and parser self-test, no `sorryAx` or custom axioms. If concurrent A/C/D/E/F/G merges change main, re-integrate without overwriting their checks. Do not mark the manuscript's global characterization or exact BRD green.
