# Track G — original-coordinate order-convex socle-novelty carriers

22 November 2026. English proof and adversarial audit **before Lean**.

## Position in the existing proof

G469 establishes order-convex *individual Kpt-node* novelty intervals, but the number Q of candidate node names may grow with the physical numerical-H+ carrier. G474 charges a genuine nonstructural zero-column exact factor-Bad cut to an original coordinate v in the E85/E86 test support of size at most |U| + |actual old selected levels|. It does not state interval structure of the corresponding *active original*. We must not infer a bound on the number of Bad cuts or their connected components.

## Definition — actual active original old-socle novelty

Fix a normalized forbidden family, a genuine finite numerical-H+ physical source, genuine old AlgorithmRun R on X, candidate seeds Y and original coordinate v:Fin N. At cut c define *OriginalNovel(v,c)* by:

1. v belongs to the genuine stage-original pool hStageOriginals(K,k,N,U,R.I(c+1)).
2. Some actual candidate Kpt node z belongs to closure(S,R.I(c+1),Y), crosses c (c < lev z), and is below the real original O_v.
3. The complete old Kpt ancestor of O_v at c has NO witness in the true old closure(S,R.I(c+1),X), i.e., not KptActualOldSocleCoveredAt(family,X,top,R,O_v,c).

This retains ALL dependent lower L+/E data; it does not project to an ordinary graph age. It requires an *active candidate representative at the same cut*, unlike a mere "original v somewhere in support" assertion.

## Theorem A — interval convexity of one original

For 0 ≤ a ≤ b ≤ c < top, OriginalNovel(v,a) and OriginalNovel(v,c) imply OriginalNovel(v,b).

**Proof.** From OriginalNovel(v,c), pick actual candidate z crossing c with z≤O_v. The genuine selected-tail identity for R gives R.I(c+1)⊆R.I(b+1); both the stage-original pool and complete candidate source closure are monotone in selected levels. Hence v remains a stage original at b, z remains in the actual candidate pre-cut closure at b, and b<lev z. Suppose v acquired an OLD complete-socle witness at b. Verified E79 kpt_actual_old_socle_covered_mono_down sends that literal witness to every lower cut, in particular a. This contradicts OriginalNovel(v,a). Thus OriginalNovel(v,b).

No old-boring hypothesis is needed for convexity itself: intersecting the original novelty interval with old-boring, zero-column, or prescribed allowed masks may destroy convexity.

## Theorem B — active original carrier for a nonstructural factor-Bad cut

Assume the graph signature db=1,du=0,dd=1, ambient finite numerical-H+ symmetry, genuine nested X⊆Y and original-pool representation of Y, a true old AlgorithmRun, an exact finite index of the complete candidate source at cut c, and genuine ZERO ordinary-L column for every eligible stage original. Suppose c is in the exact old-factor Bad set and the candidate source has neither a true I1 terminal nor a genuine same-component I2 meet at c. Fix arbitrary Allowed containing c.

Then some actual original v satisfies **both**:
- v belongs to E85's finite support kpt_originals_needing_max_old_socle_test(...,Allowed);
- OriginalNovel(v,c).

Moreover that support has cardinal at most |U|+|kpt_old_actual_selected_levels(family,X,top,R)|, independent of new numerical-H+ carrier size N or auxiliary candidate-index size Q.

**Proof.** G469/G449 extracts one genuinely live candidate Kpt crossing z at c with no OLD complete lower Kpt ancestor match. If every genuinely active stage original v had an old complete lower-socle mate, verified E78 finiteNumericH_candidate_old_socle_iff_active_original_prefixes would yield an old match for z, contradiction. Thus some active original v lacks old socle at exactly c; all three clauses of OriginalNovel hold for this v. As the cut is already old-boring (by membership in exact factor-Bad), v's genuinely active crossing gives membership c∈E71's candidate-original boring crossing cuts; together with c∈Allowed this places v in E85's maximal-test support. E86 supplies the cardinality bound.

## Corollary — bounded family of interval carriers

Under the zero-column and no-I1/no-I2 assumptions on every relevant Bad cut in Allowed, all those Bad cuts lie in the union of the raw original novelty intervals OriginalNovel(v,-) for v in E85's fixed finite test support. The number of such original intervals is ≤ |U|+|actual old selected levels|. This is a bound on *interval carriers* ONLY, not cardinality/connected components of the Bad-cut set: selecting zero-column/boring/Allowed cuts from an interval can split it arbitrarily.

## Hostile audit

1. G474's witness v∈support ∧ ¬Covered(v,c) alone does NOT imply v was active at c. Theorem B must actually construct an active v using E78, not simply strengthen G474 by rewriting its conclusion.
2. The stage-original pool is hStageOriginals(K,k,N,U,R.I(c+1)), not the full Fin N pool.
3. Source-closure monotonicity uses R.I_eq_final_tail_of_run; it must not be assumed for arbitrary I sequences.
4. The candidate node z below O_v need not be an original and may be an auxiliary meet/parameter source.
5. OLD-socle equality is equality of full admissible Kpt ancestor nodes, retaining negative L and E.
6. Both old source membership and stage-original membership are needed for the true interval claim.
7. Old complete-socle coverage persists downward, so its **failure propagates upwards**; reversing this direction would falsify the interval proof.
8. The active candidate crossing property persists downward; intersecting an increasing and a decreasing cut predicate is the convex interval.
9. The zero-column and no I1/I2 assumptions are required only for charging Bad cuts, not for interval convexity.
10. K4 genuine selected auxiliary cuts 10 and 22 remain real; no premise labels them boring without the algorithm.
11. The cardinal bound concerns the **number of distinct v carriers**, not the number of Bad cut coordinates.
12. Even if all Bad cuts are covered by one interval, there can be arbitrarily many Bad cuts inside it; no stronger counting conclusion follows.
13. The actual old selected levels may still grow with the diary resolution: |I_old(0)| is not yet bounded by the abstract diary.
14. No target AlgorithmRun on Y is assumed.
15. No cut-coordinate transport between two different diary occurrences or source-name bijection is constructed.
16. Complete inverse-source history and corrected B3/relative continuation remain unproved.
17. Infinite resolved copy, independent lower colouring and exact BRD characterization remain pending.

## Lean acceptance

Implement (A) a genuine original-coordinate novelty predicate; (B) its order-convexity theorem using E85 stageOriginal monotonicity, G469 source monotonicity, E79 old-socle downward persistence; (C) an active-original witness at zero-column exact Bad, using E78 and G469/G449 rather than a spurious reverse implication from G474; (D) the E86 original-carrier cardinal bound. Direct standalone Lake build with strict exact named #print axioms reports, negative parser self-test and independent full Lean CI. Leave black manuscript unchanged, and annotate only as BLUE when verified.
