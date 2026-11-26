# One-gap ordinary resolution: successor-tree route (26 November 2026)

## Decision and scope

The independent successor-tree characterization is the primary route. The JEMS derivation remains a cross-check, not a theorem to import as an axiom or a new project to formalize in full. The ordinary resolved graph can itself be used as a partial-structure source. There is no requirement in the structural theorem to choose the particular numerical H+ scaffold.

New English proof: `kk.tex`, Appendix C, subsection `SubSec:OneGapResolution`, theorem `Thm:OneGapUpper`. It proposes the sharp upper bound for arbitrary finite graphs and ell >= 3 without the JEMS characterization. It does NOT establish a new Lean theorem, nor the direct lower bound. The older numerical approach remains conditional. No main-body text changed.

## Critical mathematical change

1. Resolve V into an ordinary Q by isolated split markers, saturated ordinary-age cover blocks, and controlled codes. Normalize before coding r to actual maximum clique sizes on the classes of remaining V (not the possibly smaller full realized age). The survivor restriction is exact because its maximizing actual cliques remain. Every block anticomplete to the entire older prefix, and different blocks anticomplete. Restriction of a cover to selected subfront is a cover or equality, with essential support contained in subfront if visible.
2. Place Q vertex i at 2i+2; all odd positions and 0 are ordinary isolated dummies. For meaningful targets v put E+(u,v) iff u<v-1; dummy columns empty. This obeys spacing, downward and linked_E. Use verified CountableEnumeratedPartialStructure.toGPlus (no generation premise). Cap over prefix through last selected terminal: cap level tau=m+1, dummy tau, cap original tau+1, neutral ordinary column.
3. Retain all meaningful vertices in a visible block, selected codes, their preceding gaps, anchor and cap end. Retain **no portion** of any omitted block. Work with nonminimal forced-retained envelopes, not actual AlgorithmRun that must retain only interesting levels. For a fixed planned I, generic admissibleKpt_stage_closure_normalForm applies to cl(I intersect (c,tau],Y); pool cap + retained meaningful originals. Every seed or parameter ends on a retained level. Every proper meet at omitted cut would be a full-prefix fork. Any crossing positive to omitted meaningful cut is a selected terminal, since all later auxiliary blocks have zero old edges and omitted block has no retained member. For two selected opposite bits, neutrality excludes first split. For positive selected versus negative auxiliary/cap, neutrality forces an old neighbour of positive terminal, which distinguishes it from future auxiliary (and cap).
4. Corrected B3: use exact chosen full next types of ALL actual closure crossings. A newly forbidden witness after restoring c must contain c in a K_ell (loops/asymmetry impossible); has at least one upper vertex. EVERY upper vertex of this forbidden clique is positive to c, hence represented by a selected terminal. Its labelled clique multiplicity vector feasible on old prefix but infeasible on restored prefix, contradicting selected age equality. This is a proof of the special full-to-selected obstruction projection, NOT the previously false unconditional shadow implication. It works for any subset of actual represented crossing sources and repeated labels.
5. Use fullInvariant retaining and skipping steps directly (retaining has no interestingness premise), E1, and the genuine prescribed one-gap map. Force exact retained set, recover cap inverse table via actual shapeMap_recovers_ordinaryCode. Retained ordinary edges and marks determined by macrodiary; retained E columns have exactly one preceding retained gap, no generation indices. This yields one common source orbit per record, not necessarily equal minimal envelopes. Pad finite source with isolated neutral tail, apply countable_source_orbits_colour_factors.

## Adversarial finite check (not Lean)

Independently implemented finite ordinary resolution, exact capacity canonicalization by enumerating bounded-total integer vectors, maximal one-bound decrements for covers, every nonempty selected subset, and all later retained originals plus cap (stronger pool than actual closure). Explicit padding, free cuts, omitted full-prefix forks, positive-source roles, exact positive-subfront age equality, complete compressed ordinary/auxiliary tables and marked positions compared across equal macrodiaries. All enumerated ordered K_ell-free graphs on 1..4 vertices and deterministic samples of masks on 5 vertices (32/64/24 masks for ell=3/4/5, discarding forbidden graphs).

| ell | graphs | subsets | omitted cuts | full-pool fork pairs | positive age equalities | equal-record source comparisons |
|---|---:|---:|---:|---:|---:|---:|
| 3 | 61 | 981 | 8214 | 41266 | 1633 | 840 |
| 4 | 132 | 2806 | 65060 | 1179638 | 14096 | 2247 |
| 5 | 99 | 1767 | 68008 | 2561544 | 15572 | 1383 |

No counterexamples found. Finite test does not implement the generic Kpt kernel, actual closure or arbitrary finite B3 witnesses; the English argument explicitly addresses them. It does not prove existence for infinite V by computation.

## Lean plan — pinned dependency verified present

lean-kk main 0fcac8624ef0328ff4b885b8945e682d480d8669; pinned lean-successors a74c10761303a18649053f2af3a1a1697f032e13. At that exact pin, inspect `HCountablePartialTower.lean` (countable record), `CountableGPlusEmbedding.lean` (toGPlus_induced), `ConcreteOriginalPool.lean` (ambientStagePool, admissibleKpt_stage_closure_subset_pool), `KptStageClosureNormalForm.lean` (admissibleKpt_stage_closure_normalForm), `PrescribedCorrectedB3.lean` (CorrectedB3 definition), `PrescribedBoringCompletion.lean` (prescribedKpt_boring_extension_exists), `EnvelopeInvariantLevels.lean` (stageFullInvariant_interesting, stageFullInvariant_noninteresting, stageFullInvariant_levelRange), `GPlusRetainedCodeRecovery.lean` (shapeMap_recovers_ordinaryCode), `GPlusNeutralCapType.lean`, and lean-kk `CountableOrbitTransfer.lean` (countable_source_orbits_colour_factors).

Priorities:
- A/B: finite ordinary resolution and coherent countable prefix tower. Reuse ordinary canonical cover, split, controlled pre-age and restriction algebra, but do NOT build numerical-H copies or preserve old hypothetical top witnesses. Q is constructed externally over prescribed V, not inside a fixed left-dense enumeration.
- C/D: prove one-gap partial-structure record, exact free levels and full stage pool/structural exclusion for planned I. No positive-generation case analysis.
- E/G: prove full B3 via selected positive-neighbour clique obstruction, then planned retaining/skipping induction and exact compressed full inverse-code equality. No bounds on auxiliary generations or minimal-envelope synchronization. The old counterexample is not contradicted; the new positive-source property fails in that old scaffold.
- F: continue direct lower-bound finite history induction independently. Do not replace it by JEMS unavoidability. The target remains independent 24 nonedge, then 120487 independent triple, then general lower bound.

New English argument should receive hostile review and kernel validation before the sharp theorem is called formally verified. Keep old numerical modules and their exact historical axiom reports intact until the new route has passed full CI. No lean-successors change appears necessary.


Manuscript proof commit: 469557f836ce00afcdae362436156ef06365d0ef.
