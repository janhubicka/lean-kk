# Track E E71 — actual stage-original maximal crossing certificate (English FIRST)

**19 November 2026. Independent mathematical proof and adversarial audit, committed before any E71 Lean implementation.**

## Problem and improvement

Merged E69 gives an actual new Kpt AlgorithmRun preserving the complete old I/F once every new auxiliary source node is checked at its maximal old-boring residual crossing cut, together with the separate terminal-I1 check. Merged E70 constructs a finite exhaustive candidate source index without needing a new run, but its cardinality is not uniformly controlled by the diary.

The numerical-H+ geometry supports a **different, strictly coarser crossing test family**: every genuine candidate source node is an initial segment of a PHYSICAL numerical-H+ original in the actual old-run stage pool (checked Track D theorem `finiteNumericH_stage_closure_represented_by_stage_originals`). Several different auxiliary meets and parameters may share one original upper ancestor at a cut, so we can check **at most one maximal old-boring cut per actual original coordinate v∈Fin N**, rather than one test per Kpt closure node. This avoids any finite enumeration of auxiliary nodes in the final construction theorem and does not assume a target run.

### Actual data

Fix one normalized forbidden family, a finite numerical-H+ structure A=finiteNumericH(K,k,N) avoiding that family, a finite original root pool U⊆Fin N, two Kpt seed sets X⊆Y, and a genuine OLD AlgorithmRun R on X of height h. Assume Y⊆ambientPrefixPool(family,A,hAvoid,U) (so X also lies there). Define the candidate source, with the **OLD** selected level tail, by

    Znew(c) = closure_(R.I(c+1))(Y)                 (c<h)

and the old source by the same expression with X. At c<h the old full source is genuinely boring precisely when `¬ IsInterestingAt(normalizedKptSMTree family,Zold(c),c)`. There is **no** AlgorithmRun on Y in any of these data.

For a physical original address v∈Fin N, let O_v=A.kptOriginal(family,hAvoid,v). Define the finite **original-eligible** set

    C_v = {c<h : oldBoring(c)
         and v∈hStageOriginals(K,k,N,U,R.I(c+1))
         and there exists z∈Znew(c) with c<lev(z) and z≤O_v }.

The last clause is crucial: one does NOT assert that every original in the stage pool is itself a live Kpt closure node. The set C_v is finite because it is contained in [0,h), independently of the size of the auxiliary parameter closure.

Let `Covered(O_v,c)` be the checked G294 exact **old physical upper-ancestor cover** predicate: some w∈Zold(c), both v,w above c, and ancestor_(c+1)(O_v)=ancestor_(c+1)(w). It is a SAME-PAIR witness for the complete dependent old/upper L+/E record, not marginal old/upper spectra.

## E71.1 — same complete crossing under an original representative

For arbitrary Kpt nodes z≤O_v and c<lev(z), one has c<lev(O_v). By uniqueness of Kpt level ancestors,

    ancestor_(c+1)(z) = ancestor_(c+1)(O_v),

and similarly at c. If Covered(O_v,c), the SAME old physical witness w also covers z, including ALL dependent L+/E and negative ordinary L coordinates. The old witness w need not equal the original O_v and O_v need not belong to Zold or Znew. Proof uses the checked LevelTree ancestor characterization, not a reconstruction of types from their positive L-bits.

## E71.2 — one maximal crossing test per physical original

Assume for each original v with C_v nonempty that Covered(O_v,max C_v).

Fix any old-boring c<h and z∈Znew(c) with c<lev(z). The checked actual stage-original representation theorem gives a **genuine** v∈hStageOriginals(K,k,N,U,R.I(c+1)) such that z≤O_v. Thus c∈C_v. Its maximum m=max C_v exists, c≤m<h. By the hypothesis Covered(O_v,m), verified G294 downward monotonicity transports the same old physical ancestor witness from m to c. E71.1 transfers coverage from O_v to z at c. Consequently every new physical source crossing pair is already present in the old full source:

    FullPhysicalClosureCrossing(family,Znew(c),c)
      ⊆ FullPhysicalClosureCrossing(family,Zold(c),c).

There is NO need to enumerate or classify each new meet/parameter Kpt node. No no-I2 assumption is needed; forks remain separate physical crossing pairs. The original-source crossing test does not depend on the arbitrary indexing of auxiliary closure nodes.

The reduction is **sufficient**, not necessary: one original may represent multiple z, and a particular crossing may have a different old representative, so the proposed finite set of maximal original tests need not be minimal.

## E71.3 — construct the synchronized new run without finite-index hypotheses

Assume in addition, for each c<h genuinely old-boring, there is no cut-level terminal in Znew(c), i.e.

    not KptI1AtCut(family,Znew(c),c).

This is a separate geometric I1 test. It cannot be deduced from crossing coverage, because a terminal at c has no (c+1)-ancestor. In particular real K4 auxiliary cuts 10 and 22 must NOT be discarded or called boring without checking the full source.

At every old-boring cut E71.2 gives full NEW→OLD crossing inclusion, and terminal absence gives the first half of `NewRootNoNoveltyAtCut`. Apply the verified G365 theorem `kpt_transport_actualRun_of_boring_only_noNovelty`: there exists a GENUINE new AlgorithmRun on Y of the SAME top h with

    Rnew.I = R.I    and    Rnew.F = R.F

including the entire total monoid-valued F function. No Y-run and no Y source index appear in the hypothesis. E70 remains useful to obtain an independent finite record or to check physical premises computationally.

This improves the application target: a **per-stage original-coordinate** crossing check, potentially simpler to verify directly from the numerical-H+ ordinary L and auxiliary E columns, instead of an unbounded family of per-parameter closure-node crossing tests. It does **not** yield a bound uniform in the diary, because N may grow with the physical realization.

## Adversarial audit (22 checks)

1. The only input AlgorithmRun is R on X; the new run is constructed in the conclusion.
2. X⊆Y is essential for G365's run-transport theorem.
3. Y has true ambient original-prefix pool representation; replacing it by a selected graph-age shadow is invalid.
4. The selected level set in both candidate closures is exactly R.I(c+1).
5. The stage pool uses R.I(c+1), not the potentially larger R.I(0).
6. v is an actual `Fin N` numerical-H+ original, not a partial type generated by a diary.
7. v's free level may be zero; C_v's nonempty condition forces lev(z)>c and therefore lev(O_v)>c.
8. `v∈stagePool` by itself does NOT imply `O_v∈Znew(c)`; the existence of a source z≤O_v remains explicit.
9. A source z can be represented by more than one v; no choice of canonical name or injection is used.
10. One v can represent multiple auxiliary Kpt meets and parameters, but their c+1 ancestors agree when they cross c.
11. Complete upper Kpt ancestor equality implies complete old and upper dependent L+/E, not only positive ordinary-L bits.
12. The witness of Covered(O_v,c) is an ACTUAL old pre-cut source node w.
13. No matching of old and new finite name lists is assumed.
14. The same old witness is transported downward by verified G294 monotonicity.
15. C_v can have gaps because old-interesting cuts are excluded; the maximal-check proof does not require convexity.
16. C_v may be empty; never take its max without Nonempty.
17. The maximal source cut is below h because C_v ⊆ Finset.range h.
18. No functional crossing assumption is used; an I2 fork can produce multiple different complete pairs.
19. Terminal I1 is tested separately and cannot be absorbed into old/upper crossing.
20. The construction does not assume candidate new-run interesting levels or auxiliary microcut classifications.
21. K4 q2 and E cuts 10 and 22 remain possible genuine I1/I2/I3 events; no implicit Allowed mask.
22. The size of the physical H+ carrier N, complete resulting diary source orbit, actual geometric discharge of the maximal tests, and uniform upper BRD remain open.

## Next geometric tasks

For the ACTUAL resolved-Q/Henson stage, give original-column criteria ensuring that each O_v at its maximal eligible old-boring cut has one old live Kpt node with the same c+1 ancestor; and rule out new terminal I1 nodes at those cuts. Because O_v is a REAL original, compare full dependent numerical-H+ L and E prefix columns, not only the original Henson graph adjacency. The selected TOP coding, whole auxiliary block and dummy roles of Track D's original-Q stage classification give a natural case split, but that classification currently has conditional planned-level hypotheses and should NOT be silently substituted into E71.

## Validation protocol

Implement independently in a new Lean module: (a) original-representative upper cover transfer; (b) exact finite eligible-cut membership; (c) maximal-original coverage for all physical candidate crossings; (d) transport to a newly constructed AlgorithmRun via G365. Run standalone Lake build, explicit named standard-only `#print axioms` checks with parser self-test, and separate full build. Keep all new source theorems BLUE conditional pending exact-head checks. Freeze black manuscript; olive note only if supported by verified Lean.
