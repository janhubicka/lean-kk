# Track C — raw OLD seed representatives imply genuine SAME-HEIGHT safe-real/odd run transport

22 November 2026. English-first proof and adversarial audit; this note is committed before the Lean implementation. This is an *application-facing conditional reduction*, **not** a proof that a resolved diary satisfies the hypotheses.

## Claim

Fix a genuine two-model numerical-H+ physical extension in signature (1,0,1), with the same explicit K/L initial-model agreement, forbidden-family avoidance, chronological root, old initial Kpt seeds X, and physically exhaustive old AlgorithmRun as in `finiteNumericH_constructed_safe_real_odd_quiet_of_max_socle`.

Let Y be the true one-root extension, not an abstract set of proposed history names. The existing verified physical constructor produces one genuine old AlgorithmRun Rold and one finite complete original support W such that Y lies in the corresponding ambient prefix pool.

For each physical original v, consider the set S_v of *actual* eligible old-boring, new-crossing source cuts at which either:

(a) the FULL W-stage positive even-real ordinary-L column is zero; or

(b) the cut is odd and **no actual W-stage source original** has its auxiliary E-free endpoint there.

This is exactly the union `kptActualChronologicalSafeCuts` filtered by the real E79 original-crossing predicate. If S_v is nonempty, let m_v=max S_v.

**Finite raw seed representative condition.** For every such v, there are an actual OLD initial Kpt seed x∈X and a physical original u in the SAME new ambient numerical-H+ structure such that:

1. x≤O_u in the complete dependent Kpt tree;
2. m_v < lev(x) and m_v < lev(O_v);
3. the literal complete `A.partialTypeAt m_v u.val` equals `A.partialTypeAt m_v v.val` (including all ordinary negative atoms, unary/diagonal and directed auxiliary E/type-vertex fields).

Then at every old-boring cut c∈S_v, O_v has a genuine OLD Kpt pre-cut socle witness: the seed x (or, formally, one of its old pre-cut representatives). Consequently **all old-boring cuts belonging to the union of the safe real-zero and safe odd classes have full new-root no-novelty**, including I1 and SAME-NODE old/upper L+/E crossing comparison.

If, *separately*, full new-root no-novelty holds at **all other old-boring cuts c<oldTop**, the existing Track G transfer yields an **actual target AlgorithmRun RY on Y with height oldTop and RY.I=Rold.I and RY.F=Rold.F as entire functions**.

Neither the finite raw seed representative condition nor off-safe-cut quietness is automatic from the resolved Q graph; nothing establishes a physically taller new run, a common inverse-source orbit, or a BRD characterization.

## English proof

The real base-extension theorem `finiteNumericH_constructed_safe_real_odd_quiet_of_max_socle` supplies Rold, W, literal Y, and an implication from E79's maximal OLD-socle certificate for every active v to full no-novelty at all old-boring cuts in the safe union. Fix v with nonempty S_v, m_v its maximum, and raw witness u,x. The independently verified `kpt_original_old_socle_covered_of_seed_raw_type_eq` converts the literal old seed, two strict crossings and exact full raw equality into `KptActualOldSocleCoveredAt ... O_v m_v`. This discharges the E79 maximal certificate, for **each** eligible original v. E79 itself propagates complete socle matching to all its earlier possibly disconnected allowed cuts. Therefore the physical safe-cut theorem gives no-novelty at every boring safe cut.

The bare one-root definition gives X⊆Y. Apply the separately verified `kpt_transport_actualRun_of_boring_only_noNovelty` to the actual Rold. For any c<oldTop at which the OLD pre-cut source is not interesting, split on membership of c in the safe union. In the safe branch apply the preceding no-novelty theorem, in the complementary branch apply the explicitly supplied off-safe-cut hypothesis. This constructs a genuine RY and equality of the TOTAL I and F values, not merely selected-level equality.

## Hostile audit (before Lean)

1. A candidate ordinary-graph-neighbourhood equivalence is NOT the complete dependent raw type equality in the finite witness premise.
2. `u` and `v` must refer to the SAME *new* physical ambient L, whereas the old seeds X originated in K; the literal X⊆new ambient support is derived from the physical constructor, not assumed via an illicit identification.
3. `x∈X` must hold literally, not merely for a node in a hypothetical final new source.
4. `x≤O_u` must be full dependent Kpt comparability, not a selected G+ chain.
5. Both strict inequalities m_v<lev(x) and m_v<lev(O_v) are indispensable to the crossing witness; an equality level would give an I1 terminal.
6. The target v can be distinct from the old-seed representative u. No spurious assertion x≤O_v is used.
7. The raw equality must include FULL directed auxiliary E and negative L atoms; zero ordinary-L column at the **same** safe cut does not imply this.
8. The W-stage column-zero test quantifies over *all* genuine active original coordinates, not just retained selected vertices or a proposed Q-stage subfamily.
9. Odd cut safety requires absence of **all** actual physical stage free ends, not merely absence of the new root endpoint. The finite exceptional set controls one aspect of this but does not magically remove exceptions.
10. New full I1 terminals can reflect to old terminals outside finite free ends, but reflection alone does not establish no I2/B3/crossing novelty; the safe theorem already includes the remaining necessary premises.
11. Only old-boring cuts require no-novelty for same-height transport. Interesting old levels are deliberately preserved by the verified transfer theorem.
12. No conjectured equivalence between an old-boring schedule and the proposed diary schedule is used.
13. The off-safe hypothesis remains explicit and covers nonzero-real and genuinely exceptional E-parameter cuts, including any relevant K4 auxiliary cuts 10 and 22.
14. The maximal eligible original source-cut sets S_v can be disconnected; the verified E79 downward lemma does not require an interval.
15. The raw seed x and representative u may depend on v and its maximum; their existence is not inferred from cardinality budgets.
16. Originals with no eligible safe cuts require no witness. The `Nonempty` binder is essential.
17. The old run is an actual normalized-Kpt `AlgorithmRun`; no freestanding Boolean mask can replace its closure-tail monotonicity.
18. Same-height means height precisely oldTop and equality of TOTAL `I` and `F`; it does not identify RY with the independently constructed newTop physical run.
19. The number M of physical originals can vary; the theorem alone gives neither a uniform diary bound nor a direct BRD.
20. No textbook or manuscript frozen black text is changed; mark the result Lean-verified only after exact-commit full Lake build and explicit standard-axiom gate.
21. The overall global orbit remains open: safe-source comparison by itself cannot identify the event-labelled inverse-source monoid across two occurrences.

## Implementation contract

Add `KptRawOldSeedMatchAt` as an explicit predicate, a one-line bridge to the existing verified raw-socle lemma, and a theorem combining the physical safe-union constructor with the genuine same-height boring-only transfer. Import from `Kk.lean` and register exact named axiom print checks. An unrun or failing CI result is unverified; it must not receive a positive validation marker.

Remaining geometric tasks: derive the raw seed condition from the actual resolved-Q diary (complete *dependent* old-prefix records, not bare Q adjacency), verify other old-boring cuts including exceptional E events, and synchronize the physically taller run with the common labelled inverse-source orbit.
