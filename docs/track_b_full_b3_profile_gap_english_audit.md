# Track B — full corrected-(B3) profile-gap audit (13 November 2026)

## Scope and source checkpoint

Independent Track B is the **full parameter-closed corrected-(B3) comparison** for the K_k-free manuscript. It is *not* Track A's finite physical Henson realisation and *not* the separate common-labelled-orbit theorem. Baseline: `janhubicka/lean-kk` main `173fc879dcaa1e99616121ae8c1afe1d56767a15` (PR #94, 403 exact standard-only axiom reports); manuscript draft PR #22 remains unmerged. The finite all-support graph of PR #94 is an ordinary-L witness gadget and does not supply an L+ source or a corrected-(B3) comparison.

Source interfaces reviewed: `Kk/B3ReductProfile.lean`, `Kk/K4FullVsMarkedB3.lean`, `Kk/K4UpperProfileNonInclusion.lean`, `Kk/B3CutStarLocality.lean`, `Kk/FaithfulRelativeB3Profile.lean`, and the olive statement/proof of `Lem:Kk_Boring_Level` in manuscript draft `adversarial-kk-20261031`.

## Exact mathematical reduction

Let F and M be two arbitrary finite `PrescribedBoringData cut db du dd` profiles, interpreted as a *full* parameter-closed profile and a *marked* profile. Fix the same normalized forbidden family `family`. Define:

* **Socle coverage** `S(F,M)`: for every `s∈F.source`, some `t∈M.source` has the same prescribed ordinary-L initial socle through `cut`.
* **Upper-reduct inclusion** `U(F,M)`: every complete ordinary-L upper reduct permitted by F is also permitted by M.

The already verified `correctedB3_of_Lprofile_dominance` proves

```
S(F,M) ∧ U(F,M) ∧ CorrectedB3(M)  ⇒  CorrectedB3(F).
```

Consequently, whenever the actual full test fails and the marked test passes, at least ONE of these two *specific, falsifiable* profile requirements fails:

**(I)** there exists `s∈F.source` with no socle-equivalent member of `M.source`; or

**(II)** there exists a complete allowed upper L-reduct in F which is *not* allowed in M.

If (I) has already been ruled out by a separate source-closure argument, then (II) is **necessary**; if (II) is ruled out, (I) is necessary. The proof is a direct classical contrapositive of the verified transfer theorem. It does **not** assume an exhaustive source classifier or a concrete numerical-H gadget.

These three contrapositive forms are the proposed new Lean endpoints:
`fullB3_failure_good_marked_profile_gap`,
`fullB3_failure_good_marked_missing_upper`,
`fullB3_failure_good_marked_missing_socle`.

## Concrete adversarial regression

The actual K4 finite numerical-H gadget at cut 10 has a **passing selected x=38-only** B3 profile but a **failing full {q2=22,x=38}** profile on the same old L-socle (`Kk/K4FullVsMarkedB3.lean`). The existing `Kk/K4UpperProfileNonInclusion.lean` proves the complete upper L reduct for auxiliary q2 is *different* from the selected x reduct, and the full upper-type family is NOT included in the x-only family. Thus obstruction **(II)** is genuine, not a speculative deficiency.

The actual AlgorithmRun also selects cuts 22 and 10 when seeded by x=38 (`Kk/K4ActualAlgorithmRunCut10.lean`). This refutes the blanket inference “selected-front age unchanged ⇒ all auxiliary microlevels boring”. It does **not** decide whether some different, correctly resolved canonical construction can make every occurrence of the same diary have the same *full* profile.

## Critical missing theorem for the manuscript

For every candidate nonstructural level and EVERY source node in the actual `SMTree.Envelope.closure` of the selected seed family, build the genuine complete old L+ target/parameter records and prove a suitable comparison with the canonical marked profile. One possible sufficient goal is `S(F,M)∧U(F,M)`. If this fails, retain the extra auxiliary microevent in a refined canonical record and prove its profile is **determined** by the selected diary. Neither disjunct follows from the PR #94 finite graph-age construction.

The current conditional boring-level lemma also *assumes* both-stage relative-profile fidelity, no new relative continuations, and the full corrected-(B3)-loss equivalence. Those are stronger than abstract graph-age identities and have not been established for the actual resolved Henson L+ source. The separately stated witness-projection hypothesis is not used after these stronger full relative-fidelity/B3-loss assumptions; it may be moved to the proof strategy for obtaining the bridge, rather than presented as an independent requirement of the conditional equivalence. This is a presentation simplification only, not a discharge of the bridge.

## Hostile audit of the reduction

1. **Source and target direction:** to transfer *passing marked* to *passing full*, coverage must run full-source → marked-source and inclusion full-upper → marked-upper. Reversing either direction invalidates the contrapositive.
2. **Same lower socle:** membership of two types in the same ambient numerical-H carrier alone does not ensure equal prescribed ordinary-L socles through the tested cut.
3. **Complete, not selected-only upper types:** the actual K4 q2 type is precisely the missing upper reduct.
4. **Arbitrary age-test continuations:** their upper–upper edges are freely chosen; ambient H cross-block nonedges cannot be substituted for those edges. `B3CutStarLocality` only transports cut–upper incidence.
5. **Normalized forbidden family:** loop and asymmetric-pair obstructions remain part of corrected B3; the logical profile-gap lemma works for all normalized families, and does not incorrectly claim every gap is a clique witness.
6. **Parameter source closure:** an E-positive original belongs to the current closure only with the actual selected-level membership and seed hypotheses; do not infer it from E alone.
7. **Finite graph ≠ physical L+ Henson source:** an ordinary-L all-support graph is not a Kpt parameter-compatible copy without additional representation and embedding data.
8. **One-step vs countable:** finite chronological induced graph embedding does not prove the unbounded diary realisation.
9. **Age profile vs relative profile:** abstract feasible vectors need not extend a fixed old Henson prefix; the K3 triangle obstruction remains.
10. **Separate labels/orbits:** even a match of full corrected-B3 profiles does not prove a common labelled inverse-source orbit.
11. **No false green:** register the generic contrapositive results only after an exact-head full Lean build and standard-only axiom audit. Do not upgrade the global pending manuscript marker.
12. **Non-vacuity:** the new dichotomy merely identifies a missing datum when one profile passes and the other fails. It cannot be read as an existence theorem for a good marked comparison.

## Planned gate

Add the three Lean theorems with no `sorry` or new axioms, import the module in `Kk.lean`, add the three named reports to `scripts/check_axioms.lean`. Require full GitHub Actions `lake build`, parser self-test, and exactly **406** standard-only named axiom reports against the 403-report merged baseline. Until it passes, keep these results **pending CI** and the full numerical-H corrected-(B3) theorem **open**.
