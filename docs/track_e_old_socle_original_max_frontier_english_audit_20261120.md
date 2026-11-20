# Track E E79 — one maximal COMPLETE OLD Kpt prefix test per physical original across selected source cuts

**20 November 2026. English proof and 20 adversarial checks committed BEFORE Lean implementation.**

## Motivation

E71 reduced old-to-new COMPLETE UPPER dependent L+/E crossing tests at old-boring cuts to the maximal eligible cut per actual physical original. The later verified E72–E78 line is sharper at genuine ZERO ordinary-L stages: full upper crossing coverage is implied by matching just the COMPLETE OLD Kpt ancestor (the **socle**) to one old-live source node. At zero-column cuts the resulting old-prefix test is strictly less data than a full old/upper crossing match.

We should not need to repeat this old-prefix matching test at every old-boring zero-column cut. Its physical old witness persists DOWNWARD in the actual AlgorithmRun. The exact statement below packages that persistence and the maximal-cut certificate, **without** claiming that the maximal witness exists for the canonical resolved-Q diary.

## Source-exact definition

Fix one normalized Kpt family, true OLD AlgorithmRun R on seeds X of height h, physical source Kpt node z, and source cut c. Define

    OldSocleCovered(z,c) :

    there exists w∈closure_(R.I(c+1))(X),
      c<lev(z), c<lev(w),
      ancestor_c(z)=ancestor_c(w).

All ancestors are ACTUAL complete dependent Kpt nodes, retaining directed E, negative ordinary L and all other coordinates. No upper L+/E successor character is chosen; z need not lie in any closure.

## Lemma E79.1 — downward monotonicity of OLD prefix coverage

For low≤high<h, if OldSocleCovered(z,high) then OldSocleCovered(z,low).

Proof. Let w be the OLD-LIVE physical witness at high. The checked genuine old run pre-cut source monotonicity `kpt_actual_run_preCut_source_mono_down` transports w from closure_(R.I(high+1))(X) into closure_(R.I(low+1))(X). The level inequalities low<lev(z), low<lev(w) follow from high crossing. The checked LevelTree lower-ancestor restriction theorem `kpt_LevelTree_lower_ancestors_eq_of_higher_eq` transports equality of the two ACTUAL high ancestors to equality of the low ancestors. The same w witnesses OldSocleCovered(z,low).

This uses ONE genuine OLD AlgorithmRun and its actual selected-level tails. It is false for arbitrary unrelated per-cut membership masks.

## Lemma E79.2 — an arbitrary finite eligible set has ONE maximal test

Let S⊆{0,...,h−1} be any nonempty finite set of source cuts. It may have arbitrary gaps (e.g., because old interesting levels, nonzero ordinary-L cuts, odd/auxiliary stages or allowed microcuts were omitted). Let m=max S. Then

    (∀ c∈S, OldSocleCovered(z,c))
        ⇔ OldSocleCovered(z,m).

Necessity takes m∈S. Sufficiency uses c≤m and E79.1, with m<h from the defining bounded support. No interval or convexity of S is required.

**Important direction:** coverage at HIGHER cuts implies coverage at LOWER cuts, not conversely. Thus if ANY lower eligible cut fails, the maximum also fails, by contraposition. A source node may be covered at many low cuts but fail at some high cut.

## Actual numerical-H+ original specialization

For one genuine finite numerical-H+ original coordinate v∈Fin N, let O_v denote its actual Kpt original node. Existing E71 defines the complete finite candidate original crossing cut set

    C_v={ c<h : c genuinely old-boring,
         v in the true stage original pool of R.I(c+1),
         there exists new-live crossing z≤O_v at c }.

Fix any independent set Allowed of source cuts to which a test should apply, such as just the positive even-real zero-column stages. Define

    S_v = C_v ∩ Allowed.

There is at most ONE maximal OLD-SOCLE test per original v with S_v nonempty:

    (∀ c∈S_v, OldSocleCovered(O_v,c))
       ⇔ OldSocleCovered(O_v,max S_v).

This is an exact iff for the same complete old-prefix test used in E74/E78. It is **not** the E67/E71 upper-type frontier: requiring only equality of old Kpt ancestors is weaker than matching upper successors, except where the verified E72 zero-column theorem restores the latter.

## Application-facing consequence

If every real stage original v with S_v nonempty has its OLD complete prefix represented by one old-live source at max S_v, then for every c∈Allowed∩old-boring and every active original v representing a genuinely new-live crossing, the original-prefix match holds at c by downward monotonicity. E74/E78 identifies this with FULL OLD Kpt socle coverage of every candidate new crossing. At zero ordinary-L cuts, E72 upgrades it to full old/upper L+/E crossing inclusion; for one bare-root positive even-real cut E77 additionally excludes all terminals under the actual physical seed conditions.

This is a cleaner FINITE-stage test: at most N maximal OLD-Kpt-prefix obligations, rather than one per source-cut/per-auxiliary-node. It does not bound N in terms of a finite diary, identify different physical occurrences or prove that the maximal witness exists.

## Hostile adversarial audit (20)

1. One genuinely defined old AlgorithmRun is essential for downward source closure monotonicity.
2. S is finite and ALL its cuts satisfy c<h; never take a max of an empty set.
3. The old witness must be an ACTUAL old-live closure node at the HIGH cut.
4. Its old-live membership persists when scanning DOWN, not UP.
5. Lower ancestor equality follows from a high Kpt ancestor equality by genuine LevelTree uniqueness.
6. The source node z may be an original O_v not itself active in the old/new closures.
7. All old Kpt ancestors include dependent E and negative L bits; selected adjacency shadows are insufficient.
8. This is OLD-socle coverage, not an upper L+/E matching certificate at arbitrary cuts.
9. At zero ordinary-L stages E72 bridges old-socle to full crossing pairs; no unqualified upper-type claim.
10. The tested cut values are literal common normalized-Kpt source coordinates, not physical target gaps reindexed between diary occurrences.
11. Old-boringness is the actual full source interesting predicate in E71, not an assumed selected-F value.
12. The stage original pool depends on the true old selected tail R.I(c+1), not the final tail R.I 0.
13. Active original v must represent some real NEW-LIVE crossing source z≤O_v; mere membership in stage pool is insufficient.
14. The set Allowed is externally chosen and may have gaps; no order-convexity of S_v is used.
15. For each v, the maximum is computed over C_v∩Allowed, not over unfiltered stage levels when only zero-column cuts are relevant.
16. One maximal test per original still permits an arbitrarily large number of eligible cuts to be covered by that test.
17. N can grow with the finite H+ realization, so no diary-uniform carrier bound follows.
18. The theorem does NOT prove any given maximal old prefix actually has an old-live witness in the canonical resolved-Q construction.
19. K4 auxiliary E/q2 cuts 10 and 22 remain relevant whenever they belong to Allowed and actual C_v; no blanket removal.
20. No common labelled inverse-source orbit, full relative B3 diary proof, or sharp upper/lower BRD follows.

## Lean acceptance

Prove the full old-Kpt-prefix coverage predicate and its genuine old-run downward monotonicity, finite-set max iff, and one physical original-restricted-filter corollary reusing E71's exact stage original cut set. Use E71 and G294's checked monotonicity and LevelTree restriction, NOT a new invented source-mask axiom. Dedicate exact named standard-only `#print axioms` reports, strict parser negative self-test, standalone source Lake build and independent full build. Freeze manuscript black text and existing TODO policy. After validation, E78 and E77 can consume this certificate; geometry and uniformity must remain pending.
