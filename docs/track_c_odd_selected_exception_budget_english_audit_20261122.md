# Track C: finite odd E-free source exceptions cost roots plus ACTUAL selected old levels

22 November 2026. English proof and adversarial audit committed before Lean.

## Sharper result

Let A=finiteNumericH(L,k,M), W⊆Fin M a finite full ORIGINAL root pool, X a genuine old dependent Kpt seed set, and Rold a TRUE normalized Kpt AlgorithmRun on X of height oldTop. Denote by
  S = hStageOriginals L k M W (Rold.I 0)
the COMPLETE final physical original stage and by
  F = { A.freeLevel(v) : v∈S }
the genuine **physical E-free-end exception set** at old source cuts. Let
  T = {q≤oldTop : q∈Rold.I 0}
be the exact finite set of selected old levels.

Then

    |F| ≤ min(M, |W|+|T|).

In particular the bound is **independent of arbitrary padded physical carrier M and of long gaps between selected old levels**, except insofar as these affect the actual root W and selected-level set. Every actual earlier stage original lies in S, hence for c<oldTop outside F no genuine current-stage original ends at c, preserving the previously verified all-odd cut no-free-end criterion.

## English proof

An image of a finite set has no larger cardinality than the original, so |F|≤|S|. The verified Track E E86 original-budget theorem gives |S|≤|W|+|T|, using the exact selected Rold.I0 level names: the final original stage consists of W plus at most one address per selected actual level (the injection is the physical coordinate v.val). Independently S⊆Fin M, so |S|≤M. Combine the two inequalities using Nat.le_min. The result requires neither a resolved-Q diary, graph adjacency, zero L columns, nor any comparison of old Kpt prefixes.

For the *genuinely constructed* one-bare-new-root chronological K/L extension, invoke the existing verified Track C constructor supplying a real Rold, finite W, and a conditional no-novelty implication at any odd unselected cut where (i) the entire stage has no E-free endpoint, and (ii) the complete OLD Kpt prefix condition holds. Take F to be the actual final stage free-end image defined above. For c outside F, existing stage-tail monotonicity supplies (i), so odd no-novelty follows from (ii). The NEW theorem has exactly the same physical assumptions and geometric hypothesis as the earlier finite-carrier version but the sharper |F|≤|W|+|T| conclusion.

## Adversarial audit (English first)

1. This counts only distinct original E-free endpoints, not all Kpt I1/I2 or arbitrary source event cuts.
2. The starting S contains **all** genuine stage originals W plus all actually selected positive-parameter originals, not just selected coding vertices.
3. T is the **actual final Rold.I0**, not a proposed diary plan or a subset.
4. The inclusive oldTop event is retained in T; it is wrong to use q<oldTop.
5. Selected level names are physical numerical coordinates, so v↦v.val injects among selected originals.
6. W may overlap with selected originals; use subadditivity, not equality |S|=|W|+|T|.
7. The final stage may have several originals with the SAME free level: F is an image, so counting originals is conservative.
8. The physical carrier M can be arbitrarily large, so |F|≤M alone is not uniform.
9. The improved bound is M-free as an expression but still not a **diary-uniform** bound: W and |T| need independent control by an abstract diary.
10. The old run must be genuine to invoke selected-tail identity and prove every intermediate stage is in the final S.
11. The constructed extension must use the actual bare root original, not every prefix or the full old-closure-as-seeds physically taller run.
12. The finite F must be built from the SAME Rold and W as the conditional physical odd no-novelty theorem; cannot replace an arbitrary existential F by another one post hoc.
13. The new odd root's own free end is excluded by exact numerical chronology, not by counting F.
14. The odd conclusion remains conditional on complete OLD Kpt prefix coverage of all active stage originals; the bound does NOT produce such witnesses.
15. The new bound does not exclude a nonzero even-real cut, an odd cut in F, a K4 q2/E event, or a genuine I2 fork.
16. Directed auxiliary E and negative ordinary L atoms are NOT projected to a graph shadow by this finite counting statement.
17. The old and new height runs are not identified; no global inverse-source orbit or BRD follows.
18. No special cardinal argument needs proof of freeLevel injectivity (false in general).
19. The min statement should use both independently verified |F|≤M and |F|≤|W|+|T| rather than silently assuming W⊆Fin M cardinal small.
20. Exact Lean validation requires a full source build, strict qualified axiom print audit, and comparison against existing #446 theorem; this note precedes Lean and itself is not verification.

## Lean plan

Add `Kk/TrackCOddSelectedLevelExceptionBudget.lean` importing `TrackCOddFinalFreeEndSupport`, `TrackESelectedLevelOriginalBudget`. First prove a generic bound for the concrete same-run F, then re-prove the constructed odd no-novelty theorem with the stronger bound via the *same* true physical constructor used in #446. Central imports and qualified axiom checks; no frozen black manuscript edits.

Next genuine tasks: control |W| and |T| by a **fixed abstract diary**, derive complete old dependent socle witnesses from resolved Q geometry, address F and other non-safe cuts, and compare physically taller new runs.
