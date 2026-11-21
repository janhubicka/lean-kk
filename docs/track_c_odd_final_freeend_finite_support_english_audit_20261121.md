# Track C — one finite physical original free-end set controls every old-range odd source cut

21 November 2026. English-first theorem and adversarial proof audit, before Lean.

## New geometric conclusion (not just an iff)

Let A=finiteNumericH(L,k,M) be a genuine finite numerical H+ graph-signature physical source and W⊆Fin M a finite set of true physical original coordinates covering the seeds. Fix one GENUINE normalized-Kpt AlgorithmRun Rold on X, of old scan height oldTop.

Define the full FINAL original stage pool
  P_final = hStageOriginals(L,k,M,W,Rold.I(0)).
Every actual pre-cut stage original pool
  P_c = hStageOriginals(L,k,M,W,Rold.I(c+1))
for c<oldTop is contained in P_final. This uses the actual AlgorithmRun tail identity, NOT an arbitrary selected-level mask:
  Rold.I(c+1) = {q∈Rold.I(0) : c+1≤q} ⊆ Rold.I(0).

Define a single physical exceptional-source-cut set
  F = { freeLevel_A(v) : v∈P_final } ⊆ Nat.
It is a literal FINITE set with |F|≤|P_final|≤M.

For EVERY cut c<oldTop outside F, no original of the FULL actual c-stage (W roots plus all genuine selected positive-free-level originals) has its canonical AUXILIARY E-free endpoint at c.

Proof: if a current stage original v ended at c, its final-pool membership gives freeLevel(v)∈F and equals c, contradiction. Distinct original names can share a free level, hence the image cardinal may be smaller.

## Physical chronological consequence

Use the already-verified Track C #441 theorem
  finiteNumericH_constructed_bare_odd_quiet_of_stage_free_and_socle
with its exact two-model K/L original-column fidelity, forbidden
avoidance, positive new root chronology, represented old source and
physically exhaustive true old run. It CONSTRUCTS ONE old Rold, ONE
finite original pool W representing bare Y=X∪{O_new}, and at each
old-unselected odd cut c=2a+1<oldTop derives candidate complete
NewRootNoNoveltyAtCut from (i) no ACTUAL stage original E-free end
at c and (ii) complete OLD Kpt prefix coverage of each active
representing original.

Choose F from THIS Rold,W exactly as above. The first theorem
DISCHARGES (i) at every c<oldTop outside F. Therefore, under just
the complete OLD Kpt prefix condition at c, every old-unselected
ODD c outside the FINITE physical exceptional set F has full
candidate no-novelty (no generated I1 terminal, no missing
SAME-NODE paired old/upper L+/E crossing, all I2/E forks retained).

The true newly inserted root's own endpoint was already proved to
be ABOVE oldTop in #441 by physical chronology; it is not assumed
to lie in W and does not need to be separately removed from F.

**Gain:** the previous arbitrary per-cut no-stage-end test is now
replaced by ONE physically CONSTRUCTED finite F with |F|≤M, without
assuming anything about the resolved-diary Plan.

## Adversarial tests

1. The final original pool uses the GENUINE final Rold.I(0), not an
   unverified proposed diary retained set; therefore stage-tail
   inclusion is a proven AlgorithmRun property.
2. Rold must be an actual run. For an arbitrary family of sets I(c),
   P_c need not lie in P_final and the claimed F fails.
3. F includes the free levels of ALL true W original roots and ALL
   actually selected positive-free-level original addresses,
   including coding, reserved and gap names, not just Q originals.
4. The set F is a finite image of Fin M source names, so |F|≤M.
   This is *not* a bound independent of M, and M grows in a Ramsey
   construction; do NOT infer uniform diary BRDs from it.
5. The source need not have distinct free levels; the image is a
   Finset, not a multiset, so cardinality is ≤, not =.
6. This result is valid at ANY numerical source cut c<oldTop;
   oddness is used only in the subsequent #441 no-novelty theorem.
7. It does NOT prove the complete old-Kpt-prefix condition (P) at
   nonexceptional cuts; P remains a genuine geometric hypothesis.
8. A cut c∈F may still be quiet; F is an overapproximation of
   potentially ending stages, not the exact physical bad-cut set.
9. The newly inserted root need not belong to W; its free end is
   excluded separately by chronological newTop>oldTop.
10. Directed auxiliary E is not an ordinary graph L edge; no
    claim is made that F exactly identifies selected I1/I2 events.
11. The condition c∉F does not imply quietness at EVEN nonzero
    ordinary-L source columns; use #441 only for ODD c.
12. K4 q2/E microcuts (including the physical example's 10 and
    22) are not arbitrarily excluded; they may belong to F or
    remain nonzero even cuts requiring independent treatment.
13. The old K/L complete binary/unary/diagonal prefix fidelity and
    both whole finite forbidden avoidances are preserved in the
    physical specialization; nothing is inferred from shadows.
14. The conclusion uses candidate closure with the OLD Rold.I(c+1)
    selected-level tail, not the physically taller new-root run.
15. The final stage original pool can contain original nodes which
    do not occur as live source parameters at any tested cut;
    including their ends only enlarges F, safely.
16. A same-height synchronized total I/F run would additionally
    require quietness at cuts IN F and at nonzero even/other cuts,
    plus the maximal old-prefix witnesses from C423/E79.
17. No cross-occurrence inverse monoid orbit, diary-uniform carrier
    or sharp BRD follows.
18. Register the new theorem only after exact-head kernel build and
    named standard-only axiom audit; no frozen black edits.

## Lean implementation

A: Define `KptPhysicalFinalStageFreeEnds` as the Finset.image of
`(finiteNumericH L k M).freeLevel` over genuine
`hStageOriginals L k M W (Rold.I 0)`. Prove
`finalStageFreeEnds_card_le_carrier` (≤M).

B: Prove `no_current_stage_free_end_outside_final` from actual
`Rold.I_eq_final_tail_of_run` and full `ambientStagePool`
membership, for every c<oldTop.

C: Apply the already kernel-verified #441 physical odd-constructor
to obtain true Rold,W, define F once, prove |F|≤M, and infer
candidate no-novelty at every old-unselected ODD c<oldTop
with c∉F and full original old-prefix witness at c.

No unmerged Track E dependency. Test with complete Lake and strict
central named #print axioms; no global manuscript validation mark.
