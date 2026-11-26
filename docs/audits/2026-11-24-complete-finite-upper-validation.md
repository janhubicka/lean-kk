# Complete finite upper-validation checkpoint

24 November 2026. This checkpoint extends the audited upper-continuation
branch with **63 public theorems in twelve new modules**. Every mathematical
proposal was committed in English, with an independent review, before its
Lean implementation. The corresponding source reviews are in this directory.

## Verified result and its precise scope

`k4_numericRetainedPlan_run_exact` proves, for the genuine envelope run on
all planned ancestors of one actual cap,

```
Run.I 0 = Plan
Run.I i = {q | q in Plan and i <= q}   (i <= top)
IsEnvelope (Run.F 0).map X
(Run.F 0).map.levelRange = {q | q in Plan or top < q}.
```

`k4_numericRetainedPlan_exists_exact_envelope` supplies the canonical run
and derives finite-H admissibility and the normalized Kpt E1 requirement.
The plan is the explicit finite set `numericRetainedPlan`, not an unknown
final set renamed as a hypothesis. Neither off-plan noninterestingness,
no-I1/no-I2, a B3 verdict, nor final-level equality is an input.

Its ordinary hypotheses are explicit in `ResolvedQK4FinitePlanHypotheses`:
a loopless symmetric K4-free base graph, chronological roles, auxiliary
blocks consecutive modulo dummies, independent selected codes, a bounded
dummy cap, and actual full-reference-age neutrality plus selected no-split
at unretained meaningful bases. The exhaustive finite target list covers
all future selected coding bases. Singleton neutrality is derived from the
full age identity by canonical sort pullback.

This is a complete finite descending-algorithm theorem under ordinary
construction data. It is not yet a Lean implementation of the infinite
resolved-Q constructor, its record parser, or the complete characterisation
and big Ramsey degree theorem. The manuscript application must connect its
explicit events and records to those ordinary data and tagged coordinates.
The special four-clique argument must not be read as an arbitrary-K-ell
singleton argument.

## What the audit repaired or completed

| Issue | Verified resolution |
| --- | --- |
| Omitted TOP cuts still need structural exclusion even when their B3 test passes | Their entire eligible column equals the strictly older generation-zero column; actual no-I1/no-I2 and TOP skipping follow |
| Generation-zero names can include the dummy cap and retained auxiliary originals | Actual singleton neutrality supplies an old positive witness, and block intervals plus no-split give complete whole-stage coherence |
| Singleton neutralities do not determine mixed-support B3 | The full canonical reference age gives a physical-prefix sandwich and transfers every finite future clique constraint |
| The full stage need not consist only of selected TOP names | The exact failed cut-star core requires coverage only of eligible cut-adjacent names; zero-bit cap/auxiliary names remain permitted |
| Enlarging the seed family changes the actual run | Planned cap ancestors preserve the singleton physical root pool; concrete free-level closure and all cut cases are proved for this same enlarged family |
| A proposed retained Plan does not establish actual final-level equality | The genuine descending induction proves both containments and every stage tail, followed by E1 whole-node coverage |
| Matching local profiles does not identify a common full source | Literal retained chunk tables, exact level-map enumeration, and complete ordinary-code recovery retain every ordinary and directed E atom |

The mixed-support counterexample in the B3 English note, the bounded-address
alias regressions inherited from the previous checkpoint, the zero-cap
boundary, repeated labels, and empty target lists remain explicit. None of
the global manuscript pending markers is promoted by this checkpoint.

## Module inventory

| Module | Public theorems |
| --- | ---: |
| `GenerationZeroStageCoherence` | 3 |
| `GenerationZeroStructural` | 2 |
| `NumericRetainedPlan` | 15 |
| `NumericRetainedPlanExact` | 6 |
| `NumericTopNeutralPrefixAge` | 3 |
| `PlannedPrefixSeeds` | 7 |
| `ResolvedQNeutralAgeB3` | 1 |
| `RetainedChunkTables` | 11 |
| `RetainedLevelEnumeration` | 4 |
| `RetainedPrefixSource` | 3 |
| `SelectedTopAgeNeutralB3` | 2 |
| `TopGenerationStageCoherence` | 6 |

At height four the positive free offsets are **1, 3, 5, 9** in the preceding
dummy block. A retained auxiliary member contributes nine ordinary slots,
a selected coding member contributes two, and the anchor contributes one.
The cap endpoint is excluded from these ordinary coordinates. The matrix
theorem permits any common tag sequence; actual order and injectivity are
proved separately. The range theorem derives the source length and literal
coordinates instead of assuming them.

## Local verification

- Full root `lake build Kk`: **PASS, 9951 jobs**.
- Focused upper-continuation audit: **88 exact named reports**, comprising
  the existing 25 and all 63 new public endpoints.
- Central audit: **1195 exact named reports**, comprising the existing
  1132 and the new 63.
- Every report has only an allowed subset of `propext`, `Classical.choice`,
  and `Quot.sound`. No `sorryAx`, unknown constant, or custom axiom is accepted.
- The strict report parser's missing/extra/renamed/custom-axiom rejection
  self-tests pass. All new modules are imported by `Kk.lean`; the focused
  workflow builds them and runs the same strict named gate.
- `git diff --check` passes.

Runtime: Lean 4.35.0-rc3, commit
`470d5ce1400764999581fd26d5d72b00d990b0f4`.
Pinned dependencies: successor-tree
`a74c10761303a18649053f2af3a1a1697f032e13`, Ramsey library
`bb29d1f3f36ff37a35857247ca9fae581fa1fa43`, and Mathlib
`5bd58ac291422a21f412ae354c91e7d172255a2c`.

`2026-11-24-proof-source-manifest.json` records the exact source and local
verification-log hashes for this checkpoint. Hosted CI is a separate check
on the published commit; no hosted result is asserted by this local report.
