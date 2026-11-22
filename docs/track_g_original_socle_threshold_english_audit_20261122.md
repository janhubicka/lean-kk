# Track G — charge exact zero-column factor-Bad cuts to bounded ORIGINAL-socle tests

22 November 2026. English proof and adversarial audit BEFORE Lean.

## Adversarial correction: reuse existing Track E, do not duplicate it

The first draft proposed to prove monotonicity of complete old Kpt lower-socle coverage and original-to-candidate ancestor transfer again. An independent source audit found that these ingredients were ALREADY verified:

- E78 `finiteNumericH_candidate_old_socle_iff_active_original_prefixes` gives the exact equivalence between OLD-SOCLE coverage for ALL actual candidate complete Kpt source nodes and OLD prefix matches for all genuinely ACTIVE original representatives.
- E79 `kpt_actual_old_socle_covered_mono_down` and `kpt_actual_original_socle_allowed_cuts_iff_max` give the downward persistence and ONE maximal eligible cut per original.
- E85/E86 `kpt_originals_needing_max_old_socle_test_card_le_root_add_selected` bounds the number of active physical ORIGINAL representatives requiring such maximal tests by `U.card + (kpt_old_actual_selected_levels family X top R).card`, independent of the ambient new numerical-H+ carrier size N.

We REMOVE the duplicate lower-socle lemmas from the new Track G source. The genuinely new theorem relates the G449 exact factor-Bad witness to this E86 BOUNDED original-test support.

## Setting

Fix an actual finite numerical-H+ symmetric graph Kpt stage (signature 1,0,1), a genuine old AlgorithmRun R on seeds X, nested candidate seeds X⊆Y inside an actual finite original-prefix pool U, and a finite COMPLETE candidate Kpt source index `(node:Fin Q→Kpt,live)` on the old R.I(c+1) tail. Let Allowed : Set Nat be an arbitrary set of source-cut coordinates, e.g. the true positive even-real zero cuts. At a selected cut c assume:

  c ∈ Allowed;
  c ∈ kptExactOldFactorBadCuts family X top R node live;
  the complete actual stage-original ordinary L(c,v)=0 for every eligible v;
  the complete candidate source has no terminal I1 at c and no genuine same-component meet I2 at c.

## New theorem

Then there EXISTS a genuine source original v:Fin N such that:

(1) v is in the verified E85 support `kpt_originals_needing_max_old_socle_test family K k N hAvoid U X Y top R Allowed`;
(2) the complete original Kpt node O_v has NO OLD LIVE source node sharing its COMPLETE lower Kpt ancestor at c;
(3) the total number of original coordinates in that exact support satisfies

   support.card ≤ U.card + selectedOld.card

where selectedOld is the actual `kpt_old_actual_selected_levels` Finset of R.I 0.

Thus one exact zero-column Bad cut (excluding true I1/I2) can be charged to a MISSING OLD PREFIX test among at most `|U|+|R.I 0|` original-coordinate maximal tests. This is independent of physical N and of the potentially huge auxiliary candidate Kpt source index Q.

## Full proof

G469 (new, stacked predecessor) combines G449's verified exact zero-stage factor-Bad trichotomy with the exact candidate finite index. With I1/I2 excluded it supplies a live actual candidate node z∈closure(S,R.I(c+1),Y), lev(z)>c, and **NO** old live complete lower-socle witness at c.

Suppose every genuinely ACTIVE stage original had an old complete prefix witness at c. The verified E78 equivalence would give such a witness for EVERY candidate crossing z, contradicting the G469 missing-socle conclusion. Classical quantifier negation therefore supplies v∈hStageOriginals(K,k,N,U,R.I(c+1)), actually representing some candidate crossing node at c, whose old original-prefix witness does NOT exist.

Because c is in exact Bad support, the verified `mem_kptExactOldFactorBadCuts` says c<top and the old R test is genuinely boring. The original representation condition and `c∈Allowed` imply membership

  c∈kpt_actual_original_socle_allowed_cuts(...,Allowed,v).

Hence that finite set is nonempty, and E85 `mem_kpt_originals_needing_max_old_socle_test` places v in the exact original-test support. The original missing witness is, by definitional equality, `¬KptActualOldSocleCoveredAt family X top R (O_v) c`. The E86 cardinality bound now yields (3).

No new characterization of the entire source-set inverse orbit is used. The proof depends on FULL dependent old L+/E Kpt ancestors and genuine actual stage-original representation; it never projects to positive ordinary-L graph ages.

## Adversarial checks

1. E78/E79/E85/E86 are reused directly; no duplicate source monotonicity theorem is introduced.
2. G469 is only a new candidate-node order-convex interval witness; it does not bound interval length or the physical source index Q.
3. The arbitrary Allowed set must contain the tested c; otherwise the resulting original-test support need not contain the witness original.
4. The E85 test support is finite and includes originals with ACTUAL new live candidate crossings and OLD-BORING cuts, not all Fin N original names.
5. The cardinality budget uses the ACTUAL selected OLD I(0) Finset, not physical oldTop+1 or an assumed diary count.
6. The cardinality bound does NOT bound the number of exact Bad cuts per original, nor bound selected levels by a fixed diary.
7. The I1 terminal and I2 same-component meet alternatives must be excluded separately. Zero-L columns alone need not exclude them for a candidate extension.
8. The full zero-column condition applies to ALL genuine eligible stage originals and physical ordinary-L symmetry, as required by G449.
9. Old complete Kpt lower ancestors include negative ordinary L and dependent auxiliary E records; selected graph-age reduct equality is insufficient.
10. The candidate full source index must be exhaustive on closure(S,R.I(c+1),Y), not just original vertices; index size Q may vary with N.
11. The representing original may NOT itself be a live candidate or old source node. Only an actual candidate crossing below it is required.
12. One cannot infer a common labelled inverse source from a bounded set of original prefix tests; the verified G366 event-profile blindness regression remains relevant.
13. The support count is independent of N but not necessarily diary-uniform until selected I levels are controlled by the resolved diary construction.
14. Original-coordinate maximal test membership does not assert that a missing prefix occurs only once; per-original missing coverage is upper-closed, but filtered old-boring/Allowed cuts can be disconnected.
15. The K4 genuine auxiliary cuts 10 and 22 must remain in the actual source scan; this theorem neither removes nor bounds them.
16. Full chronological cut-coordinate transport, corrected B3 relative continuation, the unbounded resolved H+ copy and exact BRD numbers remain OPEN.

## Lean acceptance

Import G469, E78 and E86. Formalize ONLY the new bounded original-charging theorem, with one exact qualified standard-only #print axioms report and an independent integrated Lean build. Delete the two duplicate lemmas from the earlier stacked source. Never upgrade global manuscript validation or edit frozen black text.