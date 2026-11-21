# Track C — one maximal complete OLD Kpt prefix per physical original suffices for all positive-real zero stages

21 November 2026. English-first proof and adversarial audit, BEFORE Lean. This is the next application after merged Track C #405/#418 and merged Track E E79 #419.

## Exact mathematical claim

Assume all of the ACTUAL finite numerical-H+ base-extension hypotheses of `finiteNumericH_constructed_bare_root_real_zero_stage_quiet`: two finite graph-signature age models K and L, complete old original binary/unary/diagonal column fidelity, finite-family avoidance on both numerical H+ structures, positive generation and root chronology bounds, a physically exhaustive old normalized Kpt AlgorithmRun on possibly dependent seeds X, and ambient ordinary-L symmetry in L. The verified constructor supplies a true old run Rold and a SINGLE finite original-coordinate support W ⊆ Fin M which represents the true corrected bare new-root source Y = X ∪ {O_new}.

Define the set Z(Rold,W) of all **positive even-real physical cuts** c=hPosition k idx g at which the **complete** current original stage `hStageOriginals L k M W (Rold.I(c+1))` has zero ordinary-L cut column on every eligible original crossing c. This set is a literal set of source coordinates; it need not be an interval and need not contain every old-boring cut.

For each physical original coordinate v∈Fin M define S_v as the set of old-boring, candidate-new-live physical ORIGINAL crossing cuts c∈Z(Rold,W) where O_v represents a candidate new crossing Kpt node, as formalized by E79's `kpt_actual_original_socle_allowed_cuts`. If S_v is nonempty, let m_v=max S_v. Assume **one** complete OLD Kpt prefix witness at m_v:
`KptActualOldSocleCoveredAt family X oldTop Rold (O_v) m_v`.

Then at EVERY positive even-real c<oldTop omitted by the actual old AlgorithmRun whose actual complete W-stage ordinary-L cut column is zero, the bare candidate closure `closure_(Rold.I(c+1))(Y)` has:
- NO new full I1 terminal, even when generated meets/parameters are included;
- NO new complete same-node old/upper dependent L+/E crossing pair absent from `closure_(Rold.I(c+1))(X)`.

Equivalently `NewRootNoNoveltyAtCut family oldCandidate newCandidate c` holds.

This is a real finite-stage theorem with **at most M maximal OLD-prefix checks**, not the previous one-per-original-per-cut condition. The stage-zero obligations are still per-cut and not proven. M is the finite numerical carrier size, not a uniform diary bound.

## Proof (English)

1. Use the existing verified Track C #418 physical constructor to choose Rold, W, Y and the one-cut implication from complete stage zero + per-original OLD-prefix coverage to full candidate `NewRootNoNoveltyAtCut`.
2. Fix c=hPosition k idx g with positive c<oldTop, c∉Rold.I c and stage zero. The proof of the old run's `interesting_step` shows its complete pre-cut closure is genuinely BORING: if interesting, the run would select c, contradicting its nonselection.
3. By its very definition, the positive real and complete stage-zero facts yield c∈Z(Rold,W).
4. Fix an actual stage original v representing some new candidate crossing node z≤O_v. Thus v satisfies the exact E71/E79 active physical original conditions at cut c. Apply checked E79 `kpt_actual_original_socle_covered_of_all_allowed_max` with Allowed=Z(Rold,W), the per-original m_v certificate and the genuine old-boring fact. Its proof uses genuine old pre-cut closure monotonicity and literal Kpt ancestor restriction to derive a complete OLD-prefix witness at c.
5. This supplies PRECISELY the per-original-prefix premise required by the verified one-cut implication of Track C #418. Invoke that implication with the already assumed complete stage zero. Conclude full candidate no-novelty, including the auxiliary E/I2 forks.

## Adversarial checks

1. The original-name list is W from the physical base extension, not a guessed diary-only marked list. It may include reserved/coding/gap originals.
2. M is finite but can grow; "at most M" is not a diary-uniform BRD bound or source-event-count bound.
3. The maximal eligible cut is chosen from **positive even-real cuts WITH a complete zero original stage** AND genuine old-boring/candidate representation. It is NOT the highest numerical source cut or highest graph-shadow selected level.
4. The eligible cut family S_v may be disconnected. E79's monotone old-prefix result does not require it to be an interval.
5. The maximal prefix witness w may depend on v, but no fresh witness need be supplied for every lower eligible c; the SAME w persists by actual old-source closure monotonicity.
6. The full old prefix includes negative L, unary/diagonal and directed E; no assumption of E symmetry.
7. Stage zero is needed for the E72 upper-ancestor comparison. Old-prefix matching alone cannot be promoted to full old/upper matching at a nonzero source cut.
8. The bare new seed set Y adds ONE literal actual original; do not preinsert old final closure/ancestor prefixes.
9. Source quietness is proved for the candidate closure computed with **old** Rold.I(c+1), not automatically the separately constructed taller new AlgorithmRun.
10. The theorem says nothing about odd/fake cuts or positive real cuts where complete original-stage zero fails. K4 q2 auxiliary cuts 10 and 22 must be handled by their actual source roles and conditions.
11. The old AlgorithmRun is real and its old-unselected cut is genuinely boring; an arbitrary mask would be insufficient to invoke E79.
12. The per-original maximum hypothesis is not automatically true for the resolved diary. It is the remaining finite geometric matching problem and may fail in a proposed construction.
13. Full new/old original-column agreement, forbidden avoidance and chronological bounds are NOT weakened by this transformation.
14. No new original-support existence premise is inserted: W is obtained by #418, which had its own verified physical construction.
15. No assumption of any reverse coherent index map; fresh dependent Kpt nodes can exist while their complete old/upper pair is covered.
16. No common labelled inverse monoid orbit, total newTop run stabilization or BRD equality follows from this theorem.
17. The statement is a one-way implication from maximal prefix witnesses to candidate quietness, not a proof the resolved diary supplies witnesses.
18. Do NOT mark global BRD/diary claims GREEN after an exact-headed Lean check of this finite theorem alone.

## Formalization plan

One module `Kk/TrackCMaxOriginalZeroCertificate.lean` importing the two merged source modules #418 and E79. Reuse the exact actual base-extension hypotheses; preserve W chosen existentially once. Define the literal stage-zero Allowed set using Rold, W, finite graph H+. Use E79's one-max-per-original theorem to discharge the per-cut OLD-prefix premise of #418; use the old AlgorithmRun's `interesting_step` to derive old-boring. Add a fully qualified `#print axioms` report to the strict central script; full exact-head Lake CI is mandatory. No black manuscript edits.