# Track F — central code-stage validation closure and strict axiom registry

22 November 2026, late evening. Audit of already exact-head, independently verified Lean modules BEFORE integration.

## Scope

The individual components were proved with complete English-first adversarial audits, then compiled and strict named standard-only axiom-checked in their OWN GitHub Actions workflows, and merged into lean-kk main. Their public theorem names are not yet imported/reported through the aggregate Kk.lean and scripts/check_axioms.lean workflow, leaving a regression-coverage gap. This source-only integration closes it.

## Nine modules to import, and 18 exact endpoints to register

- TrackFCompleteNatWitnessNumericAge — exact complete finite Nat witness and numeric canonical age extraction (#478).
- TrackFPhysicalNumericAgeFromClasses — genuine source/target and after-code survivor full numerical canonical age comparison (#482).
- TrackFPhysicalSurvivorDeletion — literal physical raw/canonical survivor reindexing and zero-code post-age (#475).
- TrackFActualCodeAgeWithoutDummy — non-circular full pre-code age from REAL surviving chronological front, without dummy future coded branch (#488).
- TrackFPrecodeFromRealSurvivors — genuine actual image pre-code target front from only real surviving types (#492).
- TrackFRealTargetSurvivorNumericEndpoint — true old-target/later-target survivor numeric endpoint from one full source-target checkpoint (#494).
- TrackFTargetLexOrderPersistence — binary target lex ordering preserved by actual type extensions and deletion (#498).
- TrackFFullActualZeroCodeAgeStep — complete ACTUAL ordinary-L zero-code age stage (#500, strengthened with literal pre→post bit chronology in #501).
- TrackFActualZeroCodeTargetLex — true target lex ordering of pre/post/later fronts under the actual zero-code stage (#501).

The 18 public declarations are exact qualified names, each separately tested on the relevant prior PR. Retain ALL earlier reports; do not rename, reduce or omit them.

## Adversarial audit

1. Registry equality must be checked against the EXACT current main commit; old integration PR #442 was closed without merging, though earlier components were subsequently integrated elsewhere.
2. Imports belong in Kk.lean, not just the source-local individual module, so the central full Lake build rebuilds every new theorem.
3. Every registered declaration must have both #check and #print axioms; parser's negative self-test must pass.
4. Allowed transitive axioms are exactly the standard Lean logical propext, Classical.choice and Quot.sound (or subsets), with no sorryAx or new project axioms.
5. Only modules already merged to main are included here. The separate true-pivot split lex PR #505 is still under review and is NOT added before merge.
6. The full ordinary-L independent-code theorem does not certify all diary events. The central comments must never suggest global cover/split/meet, Kpt L+/E/parameters, 24-orbit count or exact big Ramsey lower bound are checked.
7. Avoid the earlier #442 formatting failure where literal backslash-n tokens were inserted into scripts/check_axioms.lean. Append actual newline characters and inspect around the insertion.
8. Do not clobber concurrent Track A/B/C/D/E/G main registry additions. A subsequent mergeability conflict must be refreshed and reconciled.
9. The public k4_full_actual_zero_code_ordinary_age_step was strengthened in #501 to expose genuine chronological pre-code survivor extension to post-code survivors. Verify the checked exact declaration signature is the LATEST, not the older #500 one.
10. Once CI passes this aggregate, still leave frozen black manuscript and global history/BRD validation markers pending; all theorems are physical ordinary-L components.

## Acceptance gates

Source coverage audit and full repository Lean build at exact PR head; strict full scripts/check_axioms.lean standard-only parser, self-test and all 18 named reports. Merge only after all pass. No mathematics is weakened or re-proved in the registry.
