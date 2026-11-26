# One-gap local completion and countable construction — 26 November 2026

## Outcome and validation status

This batch supplies an actual countable **K4-free construction and its
one-gap G+ source**, a constructor for the complete planned Kpt envelope
from explicit ordinary conditions, and exact compression of finite retained
codes. The sharp big Ramsey characterization remains open at the five
application obligations listed below.

The inventory comprises **eight new modules with 83 registered endpoints**
and **seven recovered modules with 69 registered endpoints**. All 1,131
previous central report names are retained; the central script now requests
**1,283 distinct transitive-axiom reports**. These counts describe registered
declaration names and source coverage, not a percentage of the mathematical
characterization.

| Final gate | Status |
|---|---|
| Default whole-project `lake build` | **PASS** — exit 0, 4,113 jobs |
| Central `scripts/check_axioms.lean` and strict named-report parser | **PASS** — 1,283 unique, exact reports; 14 axiom-free |
| Axiom-report parser self-test | **PASS** |

The completed default build is recorded in `kk-full-local-build.log`;
the central Lean output is `proof-audit/central-local-axioms.log`.
The strict parser accepts every requested name exactly once. The only
reported axioms are `propext`, `Classical.choice` and `Quot.sound`;
14 endpoints use none. The parser self-test also passes its rejection
cases for missing, extra and unapproved-axiom reports. Exact validation
provenance is recorded in the
[machine-readable completion audit](audits/2026-11-26-local-one-gap-completion.json).

| Validated component | Version or pin |
|---|---|
| Lean | `4.35.0-rc3` |
| Successor tree | `a74c10761303a18649053f2af3a1a1697f032e13` |
| Ramsey space | `f471b640f11e6b35fbbc3ad74dfa93df5ec3eadc` |
| Mathlib | `5bd58ac291422a21f412ae354c91e7d172255a2c` |

The focused scripts are
[`check_axioms_one_gap_local_completion.lean`](../scripts/check_axioms_one_gap_local_completion.lean)
and
[`check_axioms_resolved_countable_local.lean`](../scripts/check_axioms_resolved_countable_local.lean).
They overlap on the integrated source closure; the totals above count each
new central endpoint once. Component build evidence is recorded under
`proof-audit/serial-build/`.

## Import and build efficiency

The Ramsey-space dependency replaces two whole-Mathlib imports with
`Mathlib.Tactic` and gives `TopologyBridge` its explicit Baire-measurable
set import. Every non-import line in those three source files is unchanged.
The upstream change was merged in
[PR #21](https://github.com/janhubicka/lean-ramsey-space-todorcevic/pull/21)
at `f4bdd0bfd9228817e15fe0b92d29b336bdd9160a`; its
[hosted PR check](https://github.com/janhubicka/lean-ramsey-space-todorcevic/actions/runs/45888670277)
passed. The pinned source and merge have the identical tree
`298b9be8a2dc6f1d0e8521566a06c01f35ed419b`.

Five existing Kk files also have import-only changes: unnecessary
generation/capacity and neighbour-certificate dependencies are removed,
and the actual envelope APIs used by two files are imported directly.
Their theorem statements and proof bodies are unchanged. Kk explicitly
pins the validated Ramsey-space source above. The resulting tested
whole-project dependency closure builds successfully with 4,113 jobs.

## Eight new modules

| Module in `Kk/` | Endpoints | Exact contribution |
|---|---:|---|
| `OneGapCompression.lean` | 10 | Constructs the paired-coordinate lift and preserves the complete ordinary, diagonal and auxiliary tables. Equal finite ordinary tables give equal compressed full codes. |
| `OneGapCountableSchedule.lean` | 19 | Constructs the bijection between positive finite batches and natural positions, with exact batch intervals, convexity, range and prefix results. Actual vertex enumeration is injective when its lists are disjoint and have no repetitions. |
| `OneGapFiniteSelection.lean` | 8 | Extends a finite increasing selection by an explicit maximum-and-tail construction. Finite compression is independent of the extension, including the empty selection. |
| `OneGapStructuralExclusion.lean` | 7 | Derives full next-type coherence, excludes every actual closure endpoint and meet at an omitted cut, and obtains the required old neighbour from singleton canonical-age neutrality. |
| `OneGapPrescribedPool.lean` | 11 | Constructs the full retained-pool prescription, admissible targets, coverage of every closure crossing, full corrected B3 and an actual one-gap map. The selected front may be empty even when the full source is nonempty. |
| `OneGapLocalToEnvelope.lean` | 1 | Constructs the full planned envelope and its exact retained-level range from the stated ordinary source, age, split and endpoint conditions. |
| `ResolvedFairChronological.lean` | 18 | Extracts disjoint nonempty **round** batches from the actual fair stages, orders the code last, proves exact old-prefix sets, and constructs a chronological K4-free graph inducing the prescribed original graph. |
| `ResolvedFairOneGap.lean` | 9 | Constructs the actual one-gap partial structure and its canonical G+ embedding, with exact original binary and diagonal atoms, injectivity, increasing code sizes and the original auxiliary-order table. |

The first six modules contain generic finite-order or finite-pool results;
their Henson-family local envelope conclusions allow arbitrary
`ell >= 2`. The final two modules use the recovered **K4-specific** fair
construction. The generic forbidden-avoidance helper in
`ResolvedFairOneGap` does not by itself generalize that construction.

## Seven recovered construction modules

The construction was recovered from PR #512, source
`4ba24e5bff3686b4ff102c9aa9f1920fca8a6d3d`, rather than recreated as a
hypothesis that a resolved graph already exists. Its reachable source
closure contains 126 Kk modules: these seven were missing, while the other
119 matched baseline `47307be2d4b4e3ac365409a9c063094f51823f79` at extraction,
before the five Kk import-only changes described above. See the
[recovery audit](resolved_countable_recovery_audit_20261126.md) for the
source comparison and mathematical review.

| Recovered module in `Kk/` | Endpoints | Exact contribution |
|---|---:|---|
| `ResolvedLiveFutureAge.lean` | 12 | Defines future ages from actual finite live cliques, proves attained supported witnesses, and establishes normalization and survivor-age properties. |
| `ResolvedLiveCoverNormalization.lean` | 9 | Inserts actual fresh support blocks, preserves the complete old/live graph, and constructs a finite saturated cover normalization to actual future age. |
| `ResolvedLiveCoding.lean` | 5 | Preserves complete-column classes and proves exact coding of normalized survivors. |
| `ResolvedLiveSelectedProjection.lean` | 5 | Proves selected-support pullback, neutrality through every member of an omitted cover block, and absence of a new split. |
| `ResolvedLiveRefinement.lean` | 12 | Constructs occupied labels and fresh private-marker batches; proves their safety and exact refinement, including the singleton and neighbour tests used for K4. |
| `ResolvedLiveRound.lean` | 5 | Constructs the complete K4 refinement/normalization/coding round and proves coding neutrality and no new split on surviving terminals. |
| `ResolvedFairLimit.lean` | 21 | Iterates actual rounds, constructs their coherent countable K4-free limit, preserves the prescribed graph, and transfers complete old/live columns and coding neutrality to the limit. |

The recovered private `capacity_congr_on` proof was repaired using the
existing induced-image clique-capacity theorem with the identity map.
Its statement, hypotheses and construction are unchanged. Historical
English notes retain their then-pending CI descriptions; those descriptions
are not new verification evidence.

## Strongest assembled conclusions

**An actual infinite graph is constructed.**
`Kk.resolvedFair_exists_graph` starts with an arbitrary symmetric, loop-free
graph `E` on the naturals whose finite cliques have size below four. It
constructs a coherent graph `Q`, proves its K4-freeness, proves
`Q (2*i) (2*j) = E i j`, and supplies an actual finite resolved-round trace
for each coded original. The construction of the countable graph is
therefore no longer an outstanding existence assumption.

**The round schedule and the G+ source are also constructed.**
For the constructed empty-old initial state,
`Kk.resolvedFairChronological_prefix` identifies exact old-prefix sets,
and `Kk.resolvedFairCodePosition_last` locates each original at the end of
its round. `Kk.resolvedInitialOneGapOriginal_binary`, together with
`Kk.resolvedFairOneGapOriginal_diagonal` and
`Kk.resolvedFairOneGapOriginal_E`, identifies the concrete source's complete
original graph atoms and auxiliary order. Sorting extras within a round
does not yet certify the internal order of its individual marker and
cover events.

**The complete local Kpt obligations are derived from ordinary data.**
`Kk.oneGap_planned_envelope_of_selected_neutrality` constructs a full
envelope `F` with

```text
F.map.levelRange = {q | q ∈ I ∨ top < q}.
```

Its inputs include actual retained-pool coverage, retained seed and free
endpoints, selected no-split, positive-source classification, zero old
columns for eligible nonselected sources, and complete canonical selected
age neutrality. Full-type fibre agreement, old neighbours, no-I1/no-I2,
the prescribed crossing, admissible targets, corrected B3 and the skipping
maps are derived. The theorem still requires those ordinary hypotheses to
be verified for the projected events of the constructed graph.

The full B3 endpoint
`Kk.oneGapRetainedPoolData_correctedB3_all` covers `d = 0` directly.
It does not replace an empty selected front by an empty full Kpt source.
All retained auxiliary originals and the cap remain eligible source names
when their actual free levels permit them.

**Finite code compression is exact.**
`Kk.oneGapFiniteRetainedCode_eq_of_graph` identifies the full compressed
codes of two finite selections from equality of their finite ordinary
tables. `Kk.oneGapFiniteRetainedCode_extension_independent` removes any
dependence on the chosen infinite extension. The preceding retained gap
is essential to preservation of the auxiliary table. These results do
not yet establish that a macrodiary determines the table or identify it
with an actual envelope's inverse source.

## Existing convexity contract repaired

`Kk.OneGapBlockConvex`, in `OneGapFullClosure.lean`, previously required every coordinate
between two kept members of an auxiliary block to be another member of
that block. Literal one-gap padding inserts isolated dummy coordinates
between them. The contract now allows either an intermediate dummy or a
kept member of the same block. The old-column conclusion is unchanged;
the proof handles both alternatives explicitly.

This weakens an ordinary construction premise while preserving the
essential exclusion of an omitted meaningful vertex inside a kept block.
It adds no endpoint to the 152-name inventory. The omission hypothesis of
`oneGap_later_retained_aux_old_zero` still excludes dummy roles under
`ResolvedQRetainedBase`; omitted dummy cuts require their own application
case. See the [structural audit](one_gap_structural_exclusion_english_audit_20261126.md).

## Five remaining mathematical obligations

1. **Extract individual event chronology inside the constructed rounds.**
   The countable graph, disjoint round batches, exact round prefixes and
   coding-last positions already exist. Extract the separate marker
   events and ordered saturated-cover blocks from each finite round trace;
   prove their exact intermediate prefixes and whole-block convexity after
   inserting the paired dummies. Numerical sorting of the round's extras
   is not that theorem.

2. **Construct the projected diary record and discharge its ordinary local
   hypotheses.** For each selected finite occurrence, define the retained
   set, complete retained original pool, selected terminal lists and cap.
   Prove the concrete diary event rules and finite record bounds, then
   verify the endpoint, positive-source, old-column-zero, no-split and full
   selected-age conditions at every omitted meaningful or dummy cut. Then
   instantiate `oneGap_planned_envelope_of_selected_neutrality` on this
   actual event sequence. Existing per-block and coding-neutrality results
   supply components, not the complete parser and induction.

3. **Identify one full labelled inverse source for every record and apply
   the upper-bound transfer.** Show that equal macrodiaries determine the
   same retained ordinary table and marked positions; use the established
   compression and actual G+ code-recovery theorems to identify the entire
   inverse source, including auxiliary atoms and the cap. Obtain a common
   labelled source under genuine Kpt monoid maps and instantiate the
   countable-source orbit transfer. Equality of selected shadows or of
   unlabelled source sets is insufficient.

4. **Prove direct history occurrence and the matching lower bound.** Carry
   the legal finite history induction into every relevant Henson subcopy,
   prove unavoidability of distinct records, and combine the resulting
   lower bound with the upper bound and finite count. The K4 targets remain
   copy degrees 24 for the nonedge and 120,487 for the independent triple.
   Finite enumeration alone does not establish this infinite assertion;
   the intended proof remains independent of the JEMS characterization.

5. **Extend the actual construction from K4 to general K_ell.** The local
   full-B3, structural, envelope and compression interfaces already have
   general scope. The private-marker safety argument, fair-round constructor
   and countable limit used here are instantiated at four. Supply the
   corresponding construction and event hypotheses for general forbidden
   clique size before claiming the general sharp characterization.

These obligations concern the mathematical application. The successful
whole-project build and central axiom gate certify the stated theorem
interfaces; the five remaining arguments are still outstanding.
