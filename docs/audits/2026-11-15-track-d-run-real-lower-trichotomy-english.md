# Track D — actual AlgorithmRun selection splits into structural I1/I2 or physical non-top I3

15 November 2026. Mathematical proof and hostile audit COMMITTED BEFORE Lean.

## Dependencies and exact source

This is STACKED on draft PR #227, `Kk/B3FailedCutGeneration.lean`.
It must not be merged independently: its new `henson_failed_selectedB3_forces_lower_real_generation`
theorem is presently a **candidate**, pending exact-head Lean CI. No
paper GREEN mark is allowed until both the upstream and this source
have passed strict transitive-axiom audit.

The other two essential results are ALREADY checked and merged:
- `henson_actualRun_nonstructural_I3_has_exact_physical_core`
  (in `Kk/B3ActualI3PhysicalCore.lean`) at a true selected positive
  nonstructural cut: the **entire** actual pre-cut closure `Z_c`
  produces one physical labelled finite forbidden clique core.
- `henson_actualRun_complete_fullB3_failure_iff_physical_bad_core`
  (in `Kk/B3ActualRunFullBadCoreIff.lean`) uses exact full original
  name predicate and exhaustive Kpt node coverage to equate a physical
  bad core with failed full corrected B3 **on the same run/source**.

The strongest new finite location lemma of #227 derives
`c = hPosition k i g` with `g<k` from failed selected-stage
B3 for an arbitrary original-name list and selected predicate.
It relies on full forbidden-copy relocation, including the
exceptional top-to-top relation case, rather than assuming the cut
already has a real non-top generation.

## Main theorem

Fix ell>=2, ell<=k+1, a symmetric, loop-free K_ell-free base graph E
and the genuine finite numerical H=H(E,k,N), with full Henson
forbidden-family avoidance. Let U be one finite original list, X a
Kpt seed set actually represented by U, and R a genuine AlgorithmRun
with top level t and an actual top seed. Let 0<c<t and c<N.

Assume c is genuinely selected, `c ∈ R.I 0`.

Then ONE of the following holds in the **same actual pre-cut full
parameter closure** `Z_c=closure(admissibleKptSTree, R.I(c+1), X)`:

(A) I1: `Z_c` contains a node of level c;

(B) I2: two same-component nodes of Z_c meet at level c; or

(C) c is an ACTUAL REAL numerical coordinate of strictly
    non-top generation: `c=hPosition k i g`, g<k.

The disjunction is inclusive: I1 may coexist with a trivial meet
that satisfies the literal I2 predicate, and neither of the
structural alternatives says anything about other candidate
cut locations.

A useful contrapositive: if c is not a real coordinate of any
generation g<k, then **every true selected c is structural I1/I2**.
This includes all odd fake coordinates and all real top-generation
coordinates. It is stronger than the separate direct odd-cut
argument (draft PR #239), conditional on this theorem passing Lean.

## Proof (English before Lean)

Suppose c is selected and neither I1 nor I2 occurs in Z_c.
These are the exact full source predicates, not approximations
on selected macrodiary active branches.

1. By genuine selected+positive cut and no I1/I2, apply the already
   merged actual-run physical-core theorem with the true seed/rank
   and actual `R.I(c+1)` closure. Its conclusion is a
   `HensonPhysicalCutStarBadCore` on the **actual entire maintained
   final original name pool** `hStageOriginals(..., R.I 0)`
   and full closure-selected predicate. There is no invented
   auxiliary E on the arbitrary age-test clique witness.
2. Use the actual-run full-B3 physical-core iff at the SAME
   `P=actualHensonRunCutOccurrence`, not at another closure or
   chosen sample of originals. Its exact full name and
   pool-exhaustiveness components show
   `¬ P.fullProfile.CorrectedB3`.
3. By definitional equality, `P.fullProfile` is the selected-stage
   prescribed data on `P.original : Fin P.M -> Fin N` with the
   full genuine closure-selected predicate `P.Full`.
   Apply the new #227 source theorem to this exact failed
   full test and obtain `c=hPosition k i g` with g<k.
4. This contradicts any asserted non-lower-real cut location.
   By classical cases on the two structural predicates, the
   claimed disjunction and the explicit contrapositive follow.

The conclusion does not require original-to-diary active source
projection or source-orbit invariance. It says only which PHYSICAL
numerical-H levels can be genuinely nonstructural selected I3
events in ONE finite run.

## 19 hostile checks

1. Do NOT replace `Z_c=closure(R.I(c+1),X)` with `closure(R.I 0,X)`.
   The latter changes the active algorithm stage.
2. The maintained original-name carrier *does* come from
   `R.I 0`, but must not be confused with the source set Z_c.
3. The valid I2 predicate includes trivial meets at I1 endpoints;
   do not assert `I2 iff fork` without excluding actual I1.
4. The result is conditional on actual top seed; a selected
   positive level need not be nonstructural I3 without it.
5. Physical source avoidance is for the entire normalized Henson
   family, not only the pure clique pattern.
6. Symmetry, false diagonal, base K_ell-freeness and size
   ell<=k+1 are explicit, not hidden by abbreviations.
7. Every full chosen target type may include E and negative L
   source data. The proof uses checked complete source
   certification, not a selected-only capacity.
8. The physical bad core has ordinary-L upper-upper atoms
   chosen freely. Do not transplant them into actual H.
9. The full B3-to-core equivalence uses no-(I2) precisely to
   control chosen next-type source fibres.
10. The selected cut must be strictly positive and strictly
    below the Run top and within the finite H carrier.
11. The conclusion g<k comes from the actual forbidden-copy
    relocation result, not the H generator's bare gate,
    which allows top-to-top links.
12. If k=0, ell>=2 and ell<=k+1 make the input inconsistent;
    do not silently delete these hypotheses.
13. No assumption that the old physical source equals the
    selected diary branches appears anywhere.
14. An absent odd L-edge does not exclude odd I1 or I2
    because auxiliary E/free-level parameters survive.
15. Top-generation coordinates may be structural
    even though a nonstructural I3 B3 obstruction is excluded.
16. The uniform non-lower-real corollary is an implication
    about a SPECIFIED cut; it does not bound the total number
    of structural levels or prove the fixed retained set I.
17. The direct small independent-set proof still has to prove
    all required I1/I2 levels lie in the proposed retained I,
    and to verify B3/marked-source on omitted lower generations.
18. Existing universal Henson copy/BRD and common labelled
    inverse source claims do not follow.
19. This theorem stacks on draft #227; only after exact-head
    green checks may it be integrated into the central
    Lean proof list or manuscript BLUE/GREEN registry.

## Lean implementation plan

New `Kk/ActualRunStructuralOrLowerReal.lean`, imports:
`Kk.B3FailedCutGeneration`,
`Kk.B3ActualI3PhysicalCore`,
`Kk.NumericHStructuralCutClassifier`.

1. Prove explicit
   `henson_actualRun_nonstructural_selected_has_lower_real_cut`
   with literal no-I1/no-I2 raw hypotheses matching the
   merged actual-run I3 physical-core theorem.
   Let P denote the ACTUAL run occurrence at this cut; obtain its
   physical core, turn it into failed full selected B3 through
   the exact full run iff, invoke #227 on the same P.
2. Package the trichotomy
   `henson_actualRun_selected_structural_or_lower_real_cut`
   by cases on `KptI1AtCut` and `KptI2MeetAtCut` in true Z_c;
   otherwise invoke the first theorem.
3. Derive
   `henson_actualRun_selected_non_lower_real_requires_structural`
   under explicit `∀ g idx, g<k -> c != hPosition k idx g`
   by contradicing the third disjunct.

Register all three fully qualified #check/#print-axioms pairs in a
dedicated source-exact CI gate, no custom axioms or sorry.
