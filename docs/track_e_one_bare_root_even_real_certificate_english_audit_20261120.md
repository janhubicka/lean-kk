# Track E E77 — one genuine bare-root insertion: original-prefix certificate at an old-boring even-real cut

**20 November 2026. English-first proof and adversarial audit.** This source is committed BEFORE its Lean implementation.

## Target and verified inputs

The ultimate Track E task is to construct the full physical successor-tree AlgorithmRun after enlarging a resolved numerical-H+ seed set, without assuming the new run or replacing its parameter-closed source by selected-graph shadows. The separately verified E69–E76 reductions have exposed a precise **one-stage old-boring even-real** criterion.

This note composes four existing facts without inventing the missing resolved-Q geometry:

1. E76: at an old-boring cut, no OLD initial Kpt seed terminates. A single new complete numerical-H+ original has no positive even-real terminal either. The result allows old X to contain legitimate dependent seeds, unlike a false all-originals shortcut.
2. Track D: at a positive even-real cut, if NO initial seed ends there and every eligible ORIGINAL in the entire stage pool has ordinary-L cut bit zero, then no NEW *generated* parameter/meet terminal occurs.
3. E74: matching the complete OLD Kpt prefix of every genuinely ACTIVE stage original with one old-live physical Kpt node forces complete old-prefix coverage for every NEW crossing closure node. Original representatives need not themselves be live.
4. E72/E73: at a zero ordinary-L stage, full old-prefix coverage forces each complete assigned upper L+/E type to match an actual old witness. With no new terminal, this is exact physical no-novelty.

E73 is an audited English result awaiting its own exact-head dedicated Lean gate at the time of this note; it must **NOT** be cited as verified or used to promote a manuscript marker until its Lean CI succeeds.

## Actual data and reduction

Fix `family : List (NormalizedForbidden 1 0 1)`, an actual finite numerical-H+ graph expansion A=`finiteNumericH (normalizedGraphModel E) k N`, with E symmetric and A avoiding family, one true original root-name pool U : Finset (Fin N), an old seed set X represented by `ambientPrefixPool family A hAvoid U`, a genuine old AlgorithmRun R on X, and ONE true physical new original address `newV : Fin N` with `newV∈U`.

Let `O_new=A.kptOriginal family hAvoid newV` and define the new INITIAL seed family by

    Y := X ∪ {O_new}.

Important: Y is NOT `closure_I(X) ∪ {O_new}` and NOT the all-ancestor prefix pool. The latter would insert artificial initial I1 terminals.

**Automatic representation of Y.** Since X is represented by ambientPrefixPool U and newV∈U, Y⊆ambientPrefixPool U: the new root is represented by itself. Its whole meet/parameter pre-cut closure is still evaluated using the old run's genuine tail `R.I(c+1)`; no candidate new AlgorithmRun is assumed.

Fix a numerical-H+ REAL source cut `c=hPosition k idx g` with c>0 and c<R.top. Assume c is actually OLD-BORING:

    ¬ IsInterestingAt (normalizedKptSMTree family)
        (closure_(R.I(c+1))(X)) c.

For this one cut, the remaining two *geometric* hypotheses are:

**(Z) Entire genuine stage-zero column.** Every physical v∈`hStageOriginals (normalizedGraphModel E) k N U (R.I(c+1))` with `c+1≤A.freeLevel v` has `A.L.binary c v 0 = false`. Not merely selected-front original names; genuinely eligible auxiliary originals are included.

**(P) Active ORIGINAL complete old-prefix match.** Whenever an actual numerical-H+ stage original v represents some NEW-LIVE Kpt source node z above c (i.e., z∈closure_(R.I(c+1))(Y), c<lev(z), and z≤O_v), an ACTUAL old-live source w∈closure_(R.I(c+1))(X) crosses c and has the SAME `ancestor_c` as the original O_v. The old type is the full Kpt type with directed E and all negative ordinary L atoms, NOT a graph adjacency column.

No upper-L+/E matching, new source enumeration, uniqueness of representatives, new run, or extra terminal-I1 hypothesis is assumed.

## E77 — one-stage physical no-novelty theorem

**Claim.** Under the above hypotheses,

    NewRootNoNoveltyAtCut
      family
      (closure_(R.I(c+1))(X))
      (closure_(R.I(c+1))(Y))
      c

holds.

**Proof.**

1. Y is represented in the same physical original pool U: old seeds inherit `hX`; O_new has representative newV∈U and is below itself.
2. E76 applied to the true old-boring cut and the bare new root O_new gives `¬∃ y∈Y, lev(y)=c`, even if old X contains dependent Kpt seeds. **This is the only use of old-boringness before checking no-novelty**; it is not inferred from the desired conclusion.
3. E74 applies to candidate source closure computed with the OLD selected tail `R.I(c+1)`. (P) gives the complete old-Kpt source-socle coverage of EVERY new-live crossing Kpt node. This is a strictly source-exact statement; no selected-L shadow is substituted.
4. Symmetry of the original graph E gives full symmetry of the physical A ordinary L table by verified Track D, including fake numerical coordinates, without forcing symmetry of auxiliary E.
5. Apply E73 to Y, using (Z), the source-socle coverage from step 3, and no-seed-at-c from step 2. The verified Track D generated-meet/parameter terminal exclusion supplies no new I1. Verified E72 turns old complete Kpt ancestor agreement and zero ordinary-L columns into exact complete upper-L+/E crossing inclusion, at I2 forks as well.
6. The conclusion is the full physical terminal/crossing no-novelty predicate. It says the OLD skip-only monoid map is usable at this **one cut**, not that the entire enlarged AlgorithmRun was constructed.

A separate old-unselected version takes `c∉R.I(c)` with c<R.top, and derives genuine old-boringness by the actual `R.interesting_step` equation. This must use the actual full-source interesting predicate, not a selected graph-age approximation.

## Why this is a real improvement

The previous E69/E71 construction criteria included an independent new-terminal test and complete upper-Kpt crossing tests at maximal cuts for many candidate source nodes. For an actual one bare-root extension at an OLD-BORING *positive even-real zero-column* cut, E77 removes the terminal check **automatically** and reduces crossing coverage to one complete OLD `ancestor_c` match per genuinely active PHYSICAL ORIGINAL, rather than matching full assigned upper types or enumerating every dependent meet/parameter node.

This isolates the genuinely missing resolved-diary geometry as `(Z)+(P)`, both expressible in actual numerical-H+ physical original addresses.

## Crucial boundaries

- At cuts not positive even-real, including odd E/fake auxiliary levels, neither the seed-parity theorem nor the Track D even-real terminal argument applies without additional work.
- A truly old-boring cut need not satisfy stage-zero (Z). Distinct coded/auxiliary roles must be checked in the actual original-Q construction, with a genuine descending-stage invariant.
- Original-prefix condition (P) does **not** follow automatically from X⊆Y or old-to-new source-node identity; a new root can have a genuinely new complete old prefix.
- The real K4 auxiliary E/q2 cuts 10 and 22 remain compulsory when in the tested range. The theorem applies to them only if the literal (Z)+(P) hypotheses hold; it must never be used to declare all such cuts harmless.
- This is ONE cut and ONE bare original insertion. To construct a synchronized new AlgorithmRun on Y via G365/E69, it must be checked at every OLD-BORING cut, including all other cut classes; arbitrary selected levels are treated separately by G365.
- N is a finite physical original carrier of the chosen stage, not a bound uniform in the diary. This does not construct the common labelled inverse-source monoid orbit or prove a sharp BRD theorem.

## Adversarial checklist (23)

1. R is an actual OLD AlgorithmRun, not a guessed selected-level function.
2. X may have dependent initial Kpt seeds; all-X-original assumption is absent.
3. Y is precisely X∪{O_new}, not the inherited old closure.
4. newV∈U is explicit, so representing Y by U does not hide an expanded original name pool.
5. `newV:Fin N` ensures the physical coordinate belongs to the actual finite H+ carrier.
6. Both old/new sources use the SAME old `R.I(c+1)` tail.
7. Cut c is a physical REAL H+ position and c>0.
8. Require c<R.top when using nonselection to derive old-boringness.
9. Old-boringness is the full actual Kpt interesting predicate, not a graph-age shadow.
10. Old-boringness excludes OLD initial seed terminals by genuine I1, irrespective of source type.
11. Genuine new complete original cannot terminate at positive even-real c because positive E-free levels are odd.
12. Odd/fake E cuts are NOT included by the even-real theorem.
13. The full stage-original pool is computed from `R.I(c+1)`, not `R.I(0)`.
14. Zero-column condition tests EVERY stage original with free E-level extending beyond c, not only selected coding vertices.
15. The old physical prefix match uses equality of complete Kpt ancestors, retaining E and negative ordinary L atoms.
16. The physical stage original representing a live z need not itself be live.
17. Every crossing z is represented by at least one actual stage original; no canonical representative is chosen.
18. The old witness w actually belongs to the OLD full pre-cut source and crosses c.
19. Full upper successor type follows from the checked six-field zero-column theorem, not from equality of ordinary L-only types.
20. I2 forks are handled pairwise; no prescribed functional crossing assumption.
21. The generated meet/parameter terminal is excluded by Track D's full normal-form theorem, not by E76 seed exclusion alone.
22. Genuine K4 source microcuts cannot be discarded based only on graph-age diary.
23. No cross-occurrence source-level normalization, uniform diary carrier, common labelled inverse-source orbit or BRD theorem is asserted.

## Acceptance gate

After E73 exact-head green and merge, formalize a theorem for actual numerical-H+ graph models in a separate source importing E73, E74 and E76; prove true Y prefix-pool representation, OLD-BORING no-seed, active-original old-socle transfer, and the final full `NewRootNoNoveltyAtCut`. Optionally add the c∉R.I(c) formulation. Use exact named strict transitive-axiom gate and independent full Lean build. No frozen black manuscript edits, no global validation marker until this conditional source theorem is verified.

## Verification checkpoint (20 November 2026, before E77 Lean code)

E73's source has now passed the dedicated **two-name strict axiom gate** [run 44777166825](https://github.com/janhubicka/lean-kk/actions/runs/44777166825) and the independent full Lean [run 44777166666](https://github.com/janhubicka/lean-kk/actions/runs/44777166666), at exact source head `cc26b7b92372c74d5145ccfad4451581da042bb2`, and was merged in PR #394. Its only source-level compile repair changed the `Fin A.size` versus `Fin N` stage-pool adapter; it did **not** change any theorem hypotheses. E74 (#396) and E76 (#402) have previously passed independent exact-head Lean and axioms. The present E77 theorem is still conditional on (Z)+(P) and must pass its OWN exact-head gate before any manuscript marker.
